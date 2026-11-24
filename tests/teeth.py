#!/usr/bin/env python3
"""Check that tests/diff.py can tell a broken checker from a working one.

    python3 tests/teeth.py [N [NAME…]]

Each weakening below removes one rule from src/check.coil. With it applied,
either a hand-written case (tests/run.py) must be wrongly accepted, or diff.py
over N random programs (default 600) must find a program the checker accepts
and the model refuses. The checker's source is restored afterwards.
"""
import os, subprocess, sys

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
checker = os.path.join(root, "src", "check.coil")

# (name, what is lost, text in the checker, its replacement)
WEAKENINGS = [
    ("no-exclusive", "nothing is checked against the loans alive",
     "(when (and (or any (.excl l)) (overlap? (.place l) q))",
     "(when (and false (or any (.excl l)) (overlap? (.place l) q))"),
    ("no-escape", "a reference may leave the scope of what it refers to",
     '(fail! node (text3 "safe: a reference to `" (meta/source (.binder l)) "` would outlive it"))',
     "0"),
    ("no-call-loans", "a returned reference carries no loans from the call's arguments",
     "(_ (carrying all))",
     "(_ (carrying (no-loans)))"),
    ("no-arg-loans", "an argument's loans are not alive while later arguments are evaluated",
     "(hold! (mut cx) -1 carried)",
     "0"),
    ("no-let-loans", "a let-bound reference holds no loans",
     "(hold! (mut cx) serial (.loans r))",
     "0"),
    ("no-subplace", "a loan on part of a place does not protect the whole",
     "(or (prefix? a b) (prefix? b a)))",
     "(prefix? a b))"),
    ("move-while-lent", "an owner is moved while it is lent shared",
     '(check-write! cx node q "moved")',
     "(check-read! cx node q)"),
    ("match-no-loans", "a match arm's reference holds no loan on the matched place",
     "(hold! (mut cx) serial lent)",
     "0"),
    ("raw-anywhere", "raw memory is followed outside unsafe",
     "(if (raw-ok? cx node)",
     "(if true"),
]

n = sys.argv[1] if len(sys.argv) > 1 else "600"
only = sys.argv[2:]
original = open(checker).read()
missed = []
try:
    for name, lost, text, replacement in WEAKENINGS:
        if only and name not in only:
            continue
        if original.count(text) != 1:
            sys.exit(f"{name}: the text to replace occurs {original.count(text)} times in src/check.coil")
        open(checker, "w").write(original.replace(text, replacement))
        cases = subprocess.run([sys.executable, os.path.join(root, "tests", "run.py")],
                               cwd=root, capture_output=True, text=True)
        accepted = [l.split(":")[0] for l in cases.stdout.splitlines() if l.endswith(": ACCEPTED")]
        if accepted:
            print(f"if {lost}: found by a hand-written case ({' '.join(accepted)[:60]})", flush=True)
            continue
        env = dict(os.environ, SAFE_DIFF_OUT=os.path.join(root, "build", "teeth"))
        r = subprocess.run([sys.executable, os.path.join(root, "tests", "diff.py"), n, "1"],
                           cwd=root, capture_output=True, text=True, env=env)
        found = [l for l in r.stdout.splitlines() if l.startswith("THE CHECKER ACCEPTS")]
        if r.returncode == 1 and found:
            print(f"if {lost}: found ({found[0].split(': ')[1][:60]})", flush=True)
        else:
            missed.append(name)
            print(f"if {lost}: NOTHING FOUND\n{r.stdout[-600:]}{r.stderr[-600:]}", flush=True)
finally:
    open(checker, "w").write(original)
sys.exit(1 if missed else 0)
