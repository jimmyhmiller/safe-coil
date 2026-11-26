#!/usr/bin/env python3
"""Check the Coil checker against the Redex model.

    python3 tests/diff.py [N [SEED]]

`model/diff.rkt` writes the model's hand-written cases and N random programs as
Coil, with the model's verdict on each. Every one is then compiled with
`--use safe.check`. A program the compiler itself refuses (a type error, a use
of a moved value) is set aside: the checker never saw it. For the rest, the
checker must accept exactly what the model accepts. build/diff/results.txt lists
every program with both verdicts.

Exit status 1 if the checker accepts a program the model refuses. COIL names the
compiler to use when it is not the `coil` on PATH.
"""
import concurrent.futures, os, subprocess, sys

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
out = os.environ.get("SAFE_DIFF_OUT", os.path.join(root, "build", "diff"))
n = sys.argv[1] if len(sys.argv) > 1 else "300"
seed = sys.argv[2] if len(sys.argv) > 2 else "1"

subprocess.run(["rm", "-rf", out], check=True)
subprocess.run(["racket", "model/diff.rkt", out, n, seed], cwd=root, check=True)

def coil(name):
    r = subprocess.run([os.environ.get("COIL", "coil"), "check", os.path.join(out, name + ".coil"), "--use", "safe.check"],
                       cwd=root, capture_output=True, text=True)
    text = r.stdout + r.stderr
    errors = [l for l in text.splitlines() if l.startswith("error:")]
    if r.returncode == 0:
        return name, "accept", ""
    if any(l.startswith("error: safe:") for l in errors):
        return name, "reject", next(l for l in errors if l.startswith("error: safe:"))
    return name, "compiler", errors[0] if errors else text[:200]

model, skipped = {}, {}
for line in open(os.path.join(out, "verdicts.txt")):
    name, verdict, *why = line.split()
    if verdict == "skipped":
        skipped[" ".join(why)] = skipped.get(" ".join(why), 0) + 1
    else:
        model[name] = verdict

table, reasons, unsound, strict, refused, details, reborrow = {}, {}, [], [], {}, [], {}
closure_kind = {}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
    for name, verdict, why in pool.map(coil, sorted(model)):
        details.append(f"{name} model={model[name]} checker={verdict} {why}")
        if model[name] == "reborrow":
            reborrow[verdict] = reborrow.get(verdict, 0) + 1
            continue
        if model[name] == "closure-kind":
            closure_kind[verdict] = closure_kind.get(verdict, 0) + 1
            continue
        key = (model[name], verdict)
        table[key] = table.get(key, 0) + 1
        if key == ("accept", "compiler"):
            refused[why + "  [" + name + "]"] = refused.get(why, 0) + 1
        if key == ("reject", "accept"):
            unsound.append(name)
        if key == ("accept", "reject"):
            strict.append((name, why))
            reasons[why] = reasons.get(why, 0) + 1

print(f"programs written as Coil: {len(model)}; not expressible: {sum(skipped.values())}")
for why, count in sorted(skipped.items(), key=lambda kv: -kv[1]):
    print(f"    {count:6}  {why}")
print("model    checker   programs")
for key in [("accept", "accept"), ("reject", "reject"), ("accept", "reject"), ("reject", "accept"),
            ("accept", "compiler"), ("reject", "compiler")]:
    print(f"{key[0]:8} {key[1]:9} {table.get(key, 0)}")
if reborrow:
    print("refused by the model only for using an exclusive reference after moving it, which Coil")
    print(f"never does (it lends again): {sum(reborrow.values())}, of which the checker accepts {reborrow.get('accept', 0)}")
if closure_kind:
    print("refused by the model only for giving a closure that captured exclusively where one that")
    print(f"captured shared is asked for, which Coil allows (it has one kind): {sum(closure_kind.values())}, of which the checker accepts {closure_kind.get('accept', 0)}")
open(os.path.join(out, "results.txt"), "w").write("\n".join(details) + "\n")
if refused:
    print("the compiler refuses what the model accepts:")
    for why, count in sorted(refused.items())[:40]:
        print(f"    {why[:210]}")
if strict:
    print("the checker refuses what the model accepts:")
    for why, count in sorted(reasons.items(), key=lambda kv: -kv[1]):
        print(f"    {count:6}  {why}")
    print("    e.g. " + " ".join(name for name, _ in strict[:12]))
if unsound:
    print("THE CHECKER ACCEPTS WHAT THE MODEL REFUSES: " + " ".join(unsound[:40]))
sys.exit(1 if unsound else 0)
