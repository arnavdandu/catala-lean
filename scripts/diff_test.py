#!/usr/bin/env python3
"""Differential testing harness — Python side (L4-04).

Generates random s-expression terms, evaluates them with a Python mirror of
the Lean small-step semantics, then compares against the Lean oracle:

    lake exe catala-eval '<sexpr>' [fuel]

Modes:
  default        fuzz N terms, compare Python mirror vs Lean oracle
  --seed S       deterministic corpus
  --mutate       deliberately corrupt the Python mirror (+ -> *) to verify
                 the harness catches divergences (harness self-test)
  -n N           number of terms (default 50)

Exit code 0 = all agree, 1 = divergence found.
"""

import argparse
import json
import random
import subprocess
import sys

# ---------------------------------------------------------------- generation


def gen_leaf(rnd):
    r = rnd.random()
    if r < 0.25:
        return f"(int {rnd.randint(-9, 9)})"
    if r < 0.40:
        return "(bool true)" if rnd.random() < 0.5 else "(bool false)"
    if r < 0.50:
        return "(none)"          # bare atoms need parens (documented quirk)
    if r < 0.60:
        return "(empty)"
    if r < 0.68:
        return "(conflict)"
    return "(unit)"


def gen_term(rnd, depth):
    """Well-typed-ish generator: only integer-typed terms at the top level,
    so both evaluators stay in the defined (non-stuck) fragment."""
    return gen_intish(rnd, depth)


def gen_bool(rnd):
    return "(bool true)" if rnd.random() < 0.5 else "(bool false)"


def gen_boolish(rnd, d):
    """Boolean-producing term."""
    if d <= 0 or rnd.random() < 0.4:
        return gen_bool(rnd)
    k = rnd.random()
    if k < 0.45:
        return f"(ge {gen_intish(rnd, d - 1)} {gen_intish(rnd, d - 1)})"
    if k < 0.75:
        return f"({rnd.choice(['and', 'or'])} {gen_boolish(rnd, d - 1)} {gen_boolish(rnd, d - 1)})"
    return f"(if {gen_boolish(rnd, d - 1)} {gen_bool(rnd)} {gen_bool(rnd)})"


def gen_intish(rnd, d):
    """Integer-producing term (traps: zero divisor)."""
    if d <= 0 or rnd.random() < 0.35:
        return f"(int {rnd.choice([0, 1, -1, rnd.randint(-20, 20)])})"
    k = rnd.random()
    if k < 0.55:
        op = "+" if rnd.random() < 0.6 else "*"
        return f"({op} {gen_intish(rnd, d - 1)} {gen_intish(rnd, d - 1)})"
    if k < 0.80:
        return f"(if {gen_boolish(rnd, d - 1)} {gen_intish(rnd, d - 1)} {gen_intish(rnd, d - 1)})"
    return f"(int {rnd.randint(-5, 5)})"


def gen_opt(rnd, d):
    """Option-typed: none / some v / errorOnEmpty chains."""
    r = rnd.random()
    if r < 0.35:
        return "(none)"
    if r < 0.70:
        return f"(some {gen_intish(rnd, d)})"
    return f"(errorOnEmpty {'(none)' if rnd.random() < 0.5 else f'(some {gen_intish(rnd, max(0, d - 1))})'})"


def gen_exc(rnd, d):
    """Exception-list entry for default: empty or conflict."""
    return "(empty)" if rnd.random() < 0.6 else "(conflict)"


def gen_pure_target(rnd, d):
    """Argument of defaultPure: value (becomes vpure) or already-pure."""
    r = rnd.random()
    if r < 0.5:
        return f"(pure {gen_intish(rnd, max(0, d - 1))})" if False else gen_intish(rnd, max(0, d - 1))
    if r < 0.75:
        return f"(pure {gen_intish(rnd, max(0, d - 1))})"
    return f"(defaultPure {gen_intish(rnd, max(0, d - 1))})"


# ------------------------------------------------------------------- sexpr

def tokenize(s):
    return [t for t in s.replace("(", " ( ").replace(")", " ) ").split() if t]


def parse(tokens):
    """Returns (ast, rest). ast = ['atom'|'list' nodes]."""
    if not tokens:
        raise ValueError("eof")
    t, rest = tokens[0], tokens[1:]
    if t == "(":
        items = []
        while True:
            node, rest = parse(rest)
            items.append(node)
            if rest and rest[0] == ")":
                return items, rest[1:]
            if not rest:
                raise ValueError("unbalanced")
    if t == ")":
        raise ValueError("unexpected )")
    return t, rest


ATOM_MAP = {"unit": "tunit", "none": "tvnone", "empty": "tempty", "conflict": "tconflict"}


def to_term(ast):
    """Parsed s-expr AST -> internal evaluator term."""
    if isinstance(ast, str):
        if ast in ATOM_MAP:
            return ATOM_MAP[ast]
        raise ValueError(f"bare atom {ast}")
    if isinstance(ast, list) and len(ast) == 1 and ast[0] in ATOM_MAP:
        return ATOM_MAP[ast[0]]  # over-parenthesized atom, e.g. ['empty']
    h = ast[0]
    if h == "int":
        return ("tint", int(ast[1]))
    if h == "bool":
        return ("tbool", ast[1] == "true")
    if h == "some":
        return ("tvsome", to_term(ast[1]))
    if h == "pair":
        return ("tpair", to_term(ast[1]), to_term(ast[2]))
    if h == "pure":
        return ("tvpure", to_term(ast[1]))
    if h in ("+", "*", "ge", "and", "or"):
        return ("tbinop", h, to_term(ast[1]), to_term(ast[2]))
    if h == "if":
        return ("tif",) + tuple(to_term(x) for x in ast[1:])
    if h == "match":
        return ("tmatch", to_term(ast[1]), to_term(ast[2]), to_term(ast[3]))
    if h == "errorOnEmpty":
        return ("terrorOnEmpty", to_term(ast[1]))
    if h == "defaultPure":
        return ("tdefaultPure", to_term(ast[1]))
    if h == "default":
        # (default (T ...) T T): exc list may be over-parenthesized; flatten
        def flat(xs):
            out = []
            for x in xs:
                if isinstance(x, list) and len(x) == 1 and isinstance(x[0], list):
                    out.extend(flat(x))
                else:
                    out.append(x)
            return out
        excs = [to_term(x) for x in flat(ast[1])]
        return ("tdefault", excs, to_term(ast[2]), to_term(ast[3]))
    raise ValueError(f"unknown head {h}")


# ------------------------------------------------------- evaluator (mirror)

class Stuck(Exception):
    pass


def is_val(t):
    if isinstance(t, str):
        return t in ("tunit", "tvnone", "tconflict")
    h = t[0]
    if h in ("tbool", "tint", "tclosure"):
        return True
    if h == "tpair":
        return is_val(t[1]) and is_val(t[2])
    if h in ("tvsome", "tvpure"):
        return is_val(t[1])
    return False


def val_of(t):
    """termOf inverse bridge: value-headed term -> value tag tuple."""
    return t


BINOP = {
    "+": lambda a, b: ("tint", a[1] + b[1]),
    "*": lambda a, b: ("tint", a[1] * b[1]),
    "ge": lambda a, b: ("tbool", a[1] >= b[1]),
    "and": lambda a, b: ("tbool", a[1] and b[1]),
    "or": lambda a, b: ("tbool", a[1] or b[1]),
}


def step(t, mutate=False):
    """One small-step. Returns None on normal form. Raises Stuck when red has no reduct."""
    if isinstance(t, str):
        return None
    h = t[0]
    if h == "tempty":
        return "tvnone"
    if h == "tbinop":
        op, a, b = t[1], t[2], t[3]
        if mutate and op == "+":
            op = "*"   # deliberate mutation for harness self-test
        if is_val(a) and is_val(b):
            va, vb = val_of(a), val_of(b)
            f = BINOP.get(op)
            if f is None:
                raise Stuck(f"unknown binop: {op}")
            try:
                return f(va, vb)
            except TypeError:
                raise Stuck(f"binop type mismatch: {op}")
        if not is_val(a):
            sa = step(a, mutate)
            return None if sa is None else ("tbinop", op, sa, b)
        sb = step(b, mutate)
        return None if sb is None else ("tbinop", op, a, sb)
    if h == "tif":
        c = t[1]
        if isinstance(c, tuple) and len(c) == 2 and c[0] == "tbool":
            return t[2] if c[1] else t[3]
        sc = step(c, mutate)
        return None if sc is None else ("tif", sc, t[2], t[3])
    if h == "tmatch":
        s, tb_none, tb_some = t[1], t[2], t[3]
        if s == "tvnone":
            return tb_none
        if isinstance(s, tuple) and s[0] == "tvsome":
            inner = s[1]
            if is_val(inner):
                # substitute var 0 by inner in tb_some — our generated some-bodies are closed
                return tb_some
            si = step(inner, mutate)
            return None if si is None else ("tmatch", ("tvsome", si), tb_none, tb_some)
        ss = step(s, mutate)
        return None if ss is None else ("tmatch", ss, tb_none, tb_some)
    if h == "terrorOnEmpty":
        x = t[1]
        if x == "tvnone":
            return "tconflict"
        if isinstance(x, tuple) and x[0] == "tvsome":
            return x[1]
        sx = step(x, mutate)
        return None if sx is None else ("terrorOnEmpty", sx)
    if h == "tdefaultPure":
        x = t[1]
        if isinstance(x, tuple) and x[0] == "tvpure":
            return None
        if is_val(x):
            return ("tvpure", x)
        sx = step(x, mutate)
        return None if sx is None else ("tdefaultPure", sx)
    if h == "tdefault":
        excs, tj, tc = t[1], t[2], t[3]
        if not excs:
            if isinstance(tj, tuple) and tj[0] == "tbool":
                return tc if tj[1] else None
            return None
        head, rest = excs[0], excs[1:]
        if head == "tempty":
            return ("tdefault", rest, tj, tc)
        # non-empty exception: wrap in match/if like the Lean rule
        body = ("tmatch", head, ("tif", tj, tc, "tempty"), ("tvsome", ["tvar", ["zero"]]))
        return body
    return None  # values, pairs, tvsome/tvpure heads, closures: normal forms


def evaluate(t, fuel=200, mutate=False):
    for _ in range(fuel):
        try:
            t2 = step(t, mutate)
        except Stuck:
            return "STUCK"
        if t2 is None:
            return render(t)
        t = t2
    return "FUEL"


# ---------------------------------------------------------------- rendering

def render(t):
    if isinstance(t, str):
        return {"tunit": "tunit", "tvnone": "tvnone", "tconflict": "tconflict",
                "tempty": "tempty"}[t]
    if isinstance(t, tuple):
        h = t[0]
        if h == "tint":
            return f"tint {t[1]}"
        if h == "tbool":
            return f"tbool {'true' if t[1] else 'false'}"
        if h in ("tpair", "tvsome", "tvpure"):
            return f"{h} {render(t[1])}" + (f" {render(t[2])}" if h == "tpair" else "")
    raise ValueError(f"unexpected normal form: {t!r}")


# ------------------------------------------------------------------ runner

LEAN_OUTPUT_MAP = {
    "CatalaLean.CataTerm.tunit": "(unit)",
    "CatalaLean.CataTerm.tvnone": "(none)",
    "CatalaLean.CataTerm.tconflict": "(conflict)",
}


def normalize_lean(out):
    return out.strip().replace("\n", " ").replace("CatalaLean.CataTerm.", "")


def run_lean(sexpr, fuel=200):
    p = subprocess.run(
        ["lake", "exe", "catala-eval", sexpr, str(fuel)],
        cwd=REPO, capture_output=True, text=True, timeout=120,
    )
    return normalize_lean(p.stdout), p.returncode


REPO = "."


def canon(s):
    """Canonicalize both sides: token stream minus parens (Lean repr wraps
    compound args in parens; Python doesn't)."""
    return " ".join(t for t in tokenize(s) if t not in ("(", ")"))


def main():
    global REPO
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=50)
    ap.add_argument("--seed", type=int, default=None)
    ap.add_argument("--fuel", type=int, default=200)
    ap.add_argument("--mutate", action="store_true",
                    help="corrupt the Python mirror to self-test the harness")
    ap.add_argument("--repo", default=".")
    args = ap.parse_args()
    REPO = args.repo

    rnd = random.Random(args.seed)
    divergences = 0
    stuck = 0
    for i in range(args.n):
        expr = gen_term(rnd, rnd.randint(1, 4))
        py = evaluate(to_term(parse(tokenize(expr))[0]), args.fuel, mutate=args.mutate)
        lean, rc = run_lean(expr, args.fuel)
        if lean.strip().startswith('{"error"'):
            print(f"[{i}] LEAN ERROR ({lean.strip()}): {expr}")
            divergences += 1
            continue
        if py == "STUCK":
            stuck += 1
            continue  # generated term outside executable fragment
        if canon(py) != canon(lean):
            print(f"[{i}] DIVERGENCE:\n  term : {expr}\n  py   : {py}\n  lean : {lean}")
            divergences += 1
            with open(f"divergence_{args.seed or 'adhoc'}.txt", "a") as f:
                f.write(f"term : {expr}\npy   : {py}\nlean : {lean}\n\n")
    print(f"\n{args.n} terms | divergences={divergences} | stuck(skipped)={stuck}"
          f" | mode={'MUTATED' if args.mutate else 'clean'}")
    sys.exit(1 if divergences else 0)


if __name__ == "__main__":
    main()
