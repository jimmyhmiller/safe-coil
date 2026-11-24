#!/usr/bin/env python3
"""Run the checker over tests/cases. A file `ok_*.coil` must pass. A file `bad_*.coil`
must compile without the checker and be refused by it, with a `safe:` error."""
import subprocess, sys, os, glob
here = os.path.dirname(os.path.abspath(__file__))
root = os.path.dirname(here)
def check(path, use):
    cmd = ["coil", "check", path] + (["--use", "safe.check"] if use else [])
    r = subprocess.run(cmd, cwd=root, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr
failed = 0
names = sys.argv[1:] or sorted(glob.glob(os.path.join(here, "cases", "*.coil")))
for path in names:
    name = os.path.basename(path)
    plain, plain_out = check(path, False)
    code, out = check(path, True)
    if plain != 0:
        verdict = "DOES NOT COMPILE"
    elif name.startswith("ok_"):
        verdict = "ok" if code == 0 else "REFUSED"
    else:
        verdict = "ok" if code != 0 and "safe:" in out else "ACCEPTED"
    if verdict != "ok":
        failed += 1
        print(f"{name}: {verdict}\n{plain_out if plain else out}")
print(f"{len(names) - failed} of {len(names)} cases behave as intended")
sys.exit(1 if failed else 0)
