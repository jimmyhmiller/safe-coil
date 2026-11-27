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
     "(when (and (or any (.excl l))\n                   (overlap? (.place l) q)",
     "(when (and false\n                   (overlap? (.place l) q)"),
    ("no-escape", "a reference may leave the scope of what it refers to",
     '(fail! node (text3 "safe: a reference to `" (meta/source (.binder l)) "` would outlive it"))',
     "0"),
    ("no-call-loans", "a returned reference carries no loans from the call's arguments",
     "(_ (carrying all))",
     "(_ (carrying (no-loans)))"),
    ("no-arg-loans", "an argument's loans are not alive while later arguments are evaluated",
     "(hold! (mut cx) -1 (reserve-loans carried))",
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
    ("temporary-kept", "a reference into a temporary is kept past its statement",
     '(fail! node "safe: this keeps a reference into a temporary past the statement it was made in; bind the temporary to a name")',
     "0"),
    ("view-no-loans", "a view a call returns carries no loans from the call's arguments",
     "(view-type? cx (type-of e)) (Res :loans all :fresh true)",
     "(view-type? cx (type-of e)) (Res :loans (no-loans) :fresh true)"),
    ("view-moved", "a view moved out of a local leaves its loans behind",
     "(Res :loans (if (head-is? q `loc) (loans-of cx (primitive/code-int (get q 1))) (shared-loan q))",
     "(Res :loans (no-loans)"),
    ("view-passed", "a view passed by value lends the result nothing",
     "(set! all (union all (view-argument-loans (mut cx) arg param r))))",
     "0)"),
    ("view-generic", "a view is passed for a type parameter, which can store it",
     '(fail! arg "safe: a view is passed where it could be stored; it can only be a local, an argument that names its type, or a result")',
     "0"),
    ("view-copied", "a view over an exclusive reference can be copied",
     '(fail! e "safe: a view that can be copied is made from an exclusive reference; a view over one is moved, so its type needs a Drop")',
     "0"),
    ("dead-source", "a reference borrowed through one that is no longer named forgets what that one borrowed",
     "(holder-counts? cx (.holder l) (+ depth 1)))",
     "false)"),
    ("loop-once", "a name used in a loop is not counted as used by the loop's next turn",
     '(or (= text "loop")',
     "(or false"),
    ("guard-unpinned", "a view that is dropped gives up its loans when it is last named",
     "(push! (mut (.pinned cx)) serial))",
     "0)"),
    ("view-stored", "a view is stored in a struct",
     '(fail! value "safe: a view is stored; it can only be a local, an argument or a result")',
     "0"),
    ("quiet-drop-anywhere", "any module may say a view's drop is quiet, letting a lock's loans end before it unlocks",
     "(check-quiet-drop! module form)",
     "0"),
    ("dyn-copied", "a trait object is lent shared, so one call can be given it twice",
     "(if (and (dyn-local? (mut cx) node) (match want (WDiscard [] false) (WExcl [] false) (_ true)))",
     "(if (and false (match want (WDiscard [] false) (WExcl [] false) (_ true)))"),
    ("dyn-from-raw", "a trait object is made from a raw pointer outside unsafe",
     '(do (need-unsafe! cx arg "a trait object made from anything but (mut PLACE) or another trait object")',
     "(do 0"),
    ("trait-self-raw", "a raw pointer is given to a trait's method as what it works on outside unsafe",
     '(need-unsafe! cx arg "a raw pointer given to a trait\'s method as what it works on")',
     "0"),
    ("dyn-stored", "a trait object is stored in a struct",
     '(fail! value "safe: a trait object is stored; it is an exclusive reference: a local, an argument or a result")',
     "0"),
    ("literal-unchecked", "the body of a function literal whose parameter types were inferred is not checked",
     "(check-function! (.user cx) typed 2 (.tparams cx) `() (.closures cx))",
     "0"),
    ("borrows-unchecked", "a function may return what a parameter its :safe/borrows leaves out was lent",
     '(fail! form "safe: this returns a reference to what a parameter its :safe/borrows leaves out was lent")',
     "0"),
    ("two-phase-unchecked", "an argument lent exclusively may still be held by another argument when the call begins",
     '(fail! e "safe: one argument of this call lends a place exclusively and another still holds a loan on it")',
     "0"),
    ("gives-up-any", "a scope gives up to its statement whatever loan on its own local its value holds",
     "(primitive/code-sym? (value-form node))\n                      (primitive/bound-identifier=? (.binder l) (value-form node)))]",
     "true)]"),
    ("dyn-result-fresh", "a trait object a generic call gives back keeps nothing lent",
     "(dyn-type? (type-of e)) (carrying all)",
     "(dyn-type? (type-of e)) (fresh)"),
    ("par-any-view", "par's expansion may hand another thread any view, a held lock's too",
     "(cross-thread? (pointee (type-of arg))))))",
     "true)))"),
    ("any-trait-checked", "a method of any trait is taken to be checked code",
     "(checked-type? cx (get signature 3))))",
     "true))"),
    ("arena-crosses", "par may hand its other thread a shared reference to an arena",
     "(reaches-one-thread? cx t `()))\n        (fail! arg",
     "false)\n        (fail! arg"),
    ("arena-fields-unseen", "a struct holding an arena is not seen to reach it",
     "(when (reaches-one-thread? cx (primitive/code-field-type t i) more)",
     "(when false"),
    ("view-literal-fresh", "a view built from its fields holds none of their loans",
     "(if view (Res :loans all :fresh true) (fresh))",
     "(fresh)"),
    ("keeps-unvouched", "a function may say :safe/keeps without vouching for its body",
     '(fail! form "safe: a function that says :safe/keeps vouches for where the view goes: its whole body is one (unsafe …)")',
     "0"),
    ("arena-owner", "an owner may be put in an arena, which drops nothing it holds",
     "(if (and (in-arena? t) (> (len t) 1) (not (arena-safe? cx (get t 1) `())))",
     "(if false"),
    ("closure-param-stored", "a type parameter bounded by a closure trait is not used as a view",
     "(and (primitive/code-sym? t) (primitive/code-sym? (closure-bound-of (.closures cx) t)))",
     "false"),
    ("closure-any-generic", "a view is lent to any generic function's reference parameter",
     "(and (primitive/code-sym? trait)\n              (or (match (primitive/code-type-traits t)",
     "(or true\n              (or (match (primitive/code-type-traits t)"),
    ("alloc-unsealed", "any module may implement Alloc",
     '(fail! form "safe: only safe.alloc implements Alloc; give a collection another allocator through a Lease")',
     "0"),
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
