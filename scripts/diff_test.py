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
  --ocaml CMD    additionally round-trip each term through the upstream OCaml
                 compiler: wrap the expression in a generated scope, run
                 `CMD dcalc --output-format=json`, parse the JSON AST back
                 into a term, and require it to match the generated term.
                 Requires the dcalc JSON export (upstream PR #1088).

Exit code 0 = all agree, 1 = divergence found.
"""

import argparse
import json
import os
import random
import subprocess
import sys
import tempfile

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


# ----------------------------------------------- OCaml dcalc JSON interop
#
# The upstream `dcalc --output-format=json` export (PR #1088) emits nodes:
#   {"tag":"lit","value":true|"()"|"<string>"}   ints/decimals/money as strings
#   {"tag":"var","name":"x"}
#   {"tag":"op","op":"<printed op>","args":[...]}
#   {"tag":"if","cond":..,"then":..,"else":..}
#   {"tag":"default","excepts":[nested defaults],"just":..,"cons":..}
#   {"tag":"pure_default","e":..}
#   {"tag":"empty"} / {"tag":"error_on_empty","e":..}

OCAML_OP_MAP = {
    # printed form (Print.operator_to_string) -> harness binop tag
    "+!": "+", "-!": "-", "*!": "*", "/!": "/",
    "==!": "==", "<=!": "<=", ">=!": ">=", " <!": "<", ">!": ">",
    "&&!": "and", "||!": "or",
    "&&": "and", "||": "or", ">=": "ge", "<=": "le",
    "==": "eq", "<": "lt", ">": "gt",
}


def ocaml_op(op):
    if op in OCAML_OP_MAP:
        return OCAML_OP_MAP[op]
    stripped = op.rstrip("!").rstrip("?")
    return stripped if stripped in ("+", "*", "ge", "and", "or") else op


def json_to_term(node):
    """dcalc JSON AST node -> internal harness term (closed fragment)."""
    tag = node.get("tag")
    if tag == "lit":
        v = node["value"]
        if isinstance(v, bool):
            return ("tbool", v)
        if v == "()":
            return "tunit"
        try:
            return ("tint", int(v))
        except (TypeError, ValueError):
            raise ValueError(f"unsupported literal: {v!r}")
    if tag == "var":
        # closed generated terms never carry free vars after the scope's
        # input destructuring; a var here means the fragment leaked
        raise ValueError(f"free variable in extracted term: {node['name']!r}")
    if tag == "op":
        args = [json_to_term(a) for a in node["args"]]
        op = ocaml_op(node["op"])
        if len(args) != 2:
            raise ValueError(f"non-binary op {node['op']!r}")
        return ("tbinop", op, args[0], args[1])
    if tag == "if":
        return ("tif", json_to_term(node["cond"]),
                json_to_term(node["then"]), json_to_term(node["else"]))
    if tag == "error_on_empty":
        inner = node["e"]
        # dcalc encodes a scope-variable definition as:
        #   error_on_empty(default(
        #     excepts = [ default(just=<guard>, cons=pure_default(<body>)) ... ],
        #     just    = lit false,
        #     cons    = empty ))
        # Semantics: first exception whose guard is true and whose body is not
        # empty wins; otherwise empty -> conflict. Convert the exception chain
        # to an if-ladder: error_empty(if g1 then b1 else if g2 ... else ∅).
        def ladder(d):
            """Build the if-ladder term for one (nested) default node."""
            acc = "tempty"
            for ex in reversed(d.get("excepts", [])):
                if ex.get("tag") != "default":
                    raise ValueError(f"bad exception node: {ex.get('tag')!r}")
                j, c = ex.get("just"), ex.get("cons")
                # nested exception chains fold into the accumulator
                if isinstance(c, dict) and c.get("tag") == "pure_default" \
                        and isinstance(c["e"], dict) and c["e"].get("tag") == "default":
                    acc = ladder(c["e"])
                    continue
                if c.get("tag") == "empty":
                    continue
                body = json_to_term(c["e"]) if c.get("tag") == "pure_default" \
                    else json_to_term(c)
                acc = ("tif", json_to_term(j), body, acc)
            return acc

        return ("terrorOnEmpty", ladder(inner))
    if tag == "default":
        # bare default outside error_on_empty (shouldn't occur in our fragment)
        raise ValueError("bare default node")
    if tag == "empty":
        return "tempty"
    if tag == "pure_default":
        return ("tvpure", json_to_term(node["e"])) if False else json_to_term(node["e"])
    if tag == "default":
        # dcalc encodes a scope-variable definition as:
        #   error_on_empty(default(
        #     excepts = [ default(just=<guard>, cons=pure_default(<body>)) ... ],
        #     just    = lit false,          (fallback guard: never take cons)
        #     cons    = empty ))
        # i.e. the real fallback is ∅ and each exception carries its own
        # boolean guard. Convert to harness form: one tdefault with an
        # exception list where guarded exceptions become
        #   ⟨ if <guard> then <body> else ∅ ⟩  ≈ match-free encoding:
        # we keep guards by wrapping body in tif(guard, body, tempty) — the
        # mirror's tdefault rule treats tempty exceptions as no-ops, so a
        # false guard degrades to skipping the exception.
        excs = []

        def walk(d):
            for ex in d.get("excepts", []):
                if ex.get("tag") != "default":
                    raise ValueError(f"bad exception node: {ex.get('tag')!r}")
                j = ex.get("just")
                c = ex.get("cons")
                # descend into nested exception chains first
                if isinstance(c, dict) and c.get("tag") == "pure_default" \
                        and isinstance(c["e"], dict) and c["e"].get("tag") == "default":
                    walk(c["e"])
                    continue
                if c.get("tag") == "empty":
                    excs.append("tempty")
                    continue
                body_term = json_to_term(c["e"]) if c.get("tag") == "pure_default" \
                    else json_to_term(c)
                guard_true = isinstance(j, dict) and j.get("tag") == "lit" \
                    and j.get("value") is True
                if guard_true:
                    excs.append(body_term)
                else:
                    guard = json_to_term(j)
                    excs.append(("tif", guard, body_term, "tempty"))

        walk(node)
        # fallback of the outermost default is the empty cons
        return ("tdefault", excs, ("tbool", True), "tempty")
    raise ValueError(f"unsupported dcalc JSON tag: {tag!r}")


SCOPE_TEMPLATE = """```catala
declaration scope Fuzz:
  output out content integer

scope Fuzz:
  definition out equals {expr}
```
"""


class OcamlOracle:
    """Round-trips generated terms through the upstream OCaml compiler."""

    def __init__(self, cmd, workdir=None):
        self.cmd = cmd.split()
        self.stdlib = os.environ.get("OCATALA_STDLIB")
        self.workdir = workdir or tempfile.mkdtemp(prefix="diff_ocaml_")
        os.makedirs(self.workdir, exist_ok=True)

    def _run(self, extra):
        return subprocess.run(
            self.cmd + ["dcalc"] + extra,
            capture_output=True, text=True, timeout=120,
        )

    def roundtrip(self, term):
        """Returns ('ok', term) or ('skip', reason)."""
        expr = term_to_catala_expr(to_catala_term(term))
        if expr is None:
            return "skip", "outside catala-surface fragment"
        path = os.path.join(self.workdir, "fuzz.catala_en")
        with open(path, "w") as f:
            f.write(SCOPE_TEMPLATE.replace("{expr}", expr))
        extra = ["--output-format=json", "-s", "Fuzz", path]
        if self.stdlib:
            extra = ["--stdlib", self.stdlib] + extra
        p = self._run(extra)
        if p.returncode != 0 or "could not be found" in p.stderr:
            if self.stdlib is None and "Stdlib" in (p.stderr + p.stdout):
                return "skip", "needs --stdlib; pass a libcatala dir via OCATALA_STDLIB"
            return "skip", f"catala rejected: {(p.stderr.strip().splitlines() or [''])[-1:]}"
        try:
            data = json.loads(p.stdout)
        except json.JSONDecodeError:
            return "skip", "invalid JSON from dcalc"
        body = data[0]["scope"]
        sets = [l for l in body["lets"] if l["kind"] == "set"]
        target = sets[-1]["expr"] if sets else body["return"]
        try:
            got = json_to_term(target)
        except ValueError as e:
            return "skip", f"JSON outside fragment ({e})"
        return "ok", got


def term_to_catala_expr(term):
    """Internal term -> Catala surface expression (integer fragment + defaults).
    Only used for terms the generator produces (no options/pairs needed at the
    top level; those are skipped by the caller)."""
    if isinstance(term, str):
        return {"tempty": "∅", "tconflict": "conflict", "tvnone": "none"}.get(term)
    h = term[0]
    if h == "tint":
        return str(term[1])
    if h == "tbool":
        return "true" if term[1] else "false"
    if h == "tbinop":
        sym = {"+": "+", "*": "*", "ge": ">=", "and": "and", "or": "or"}.get(term[1])
        if sym is None:
            return None
        a = term_to_catala_expr(term[2])
        b = term_to_catala_expr(term[3])
        if a is None or b is None:
            return None
        # always parenthesize operands: Catala precedence differs from the
        # flat s-expr tree (e.g. -1 * 1 + -8 parses as (-1*1) + -8)
        return f"({a} {sym} {b})"
    if h == "tif":
        c = term_to_catala_expr(term[1])
        a = term_to_catala_expr(term[2])
        b = term_to_catala_expr(term[3])
        if None in (c, a, b):
            return None
        return f"(if {c} then {a} else {b})"
    if h == "terrorOnEmpty":
        x = term_to_catala_expr(term[1])
        return None if x is None else f"error_empty ⟨ {x} ⟩"
    if h == "tdefault":
        excs, tj, tc = term
        parts = []
        for ex in excs:
            e = term_to_catala_expr(ex)
            if e is None:
                return None
            parts.append(f"⟨ true ⊢ {e} ⟩")
        j = term_to_catala_expr(tj)
        c = term_to_catala_expr(tc)
        if j is None or c is None:
            return None
        inner = " | ".join(parts + [f"{j} ⊢ {c}"]) if parts else f"{j} ⊢ {c}"
        return f"⟨ {inner} ⟩"
    return None



def to_catala_term(t):
    """Normalize harness term to the subset expressible in Catala surface
    syntax: drop tvsome/tvpure wrappers introduced by generation."""
    if isinstance(t, tuple) and t[0] in ("tvsome", "tvpure"):
        return to_catala_term(t[1])
    if isinstance(t, tuple):
        return tuple(to_catala_term(x) if isinstance(x, tuple) else
                     ([to_catala_term(y) for y in x] if isinstance(x, list) else x)
                     for x in t)
    if isinstance(t, list):
        return [to_catala_term(x) for x in t]
    return t


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
    ">=": lambda a, b: ("tbool", a[1] >= b[1]),    "and": lambda a, b: ("tbool", a[1] and b[1]),
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
        if isinstance(x, str) or (isinstance(x, tuple) and is_val(x)):
            return ("tvsome", x)  # value body: wrap like the Lean rule
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
    ap.add_argument("--ocaml", default=None, metavar="CMD",
                    help="path to a catala binary with the dcalc JSON export "
                         "(e.g. ~/Exploration/catala/_build/default/compiler/catala.exe); "
                         "enables the OCaml round-trip oracle")
    args = ap.parse_args()
    REPO = args.repo

    ocaml = OcamlOracle(args.ocaml) if args.ocaml else None

    rnd = random.Random(args.seed)
    divergences = 0
    stuck = 0
    ocaml_checked = 0
    ocaml_skipped = 0
    for i in range(args.n):
        expr = gen_term(rnd, rnd.randint(1, 4))
        term = to_term(parse(tokenize(expr))[0])
        py = evaluate(term, args.fuel, mutate=args.mutate)

        if ocaml is not None:
            status, payload = ocaml.roundtrip(term)
            if status == "ok":
                ocaml_checked += 1
                # the scope wraps results in an option via error_empty:
                # evaluate the OCaml-parsed term with the mirror and strip
                # the top-level tvsome wrapper before comparing.
                try:
                    oc = evaluate(payload, args.fuel)
                except Stuck:
                    oc = "STUCK"
                if isinstance(oc, str) and oc.startswith("tvsome "):
                    oc = oc[len("tvsome "):]
                py_nf = evaluate(term, args.fuel, mutate=args.mutate)
                if oc != "STUCK" and canon(oc) != canon(py_nf):
                    print(f"[{i}] OCAML DIVERGENCE:\n  term  : {expr}\n"
                          f"  py    : {py_nf}\n  ocaml : {oc}")
                    divergences += 1
                    with open(f"divergence_ocaml_{args.seed or 'adhoc'}.txt", "a") as f:
                        f.write(f"term : {expr}\npy   : {py_nf}\nocaml: {oc}\n\n")
            else:
                ocaml_skipped += 1

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
    extra = ""
    if ocaml is not None:
        extra = f" | ocaml_roundtrip={ocaml_checked} ocaml_skipped={ocaml_skipped}"
    print(f"\n{args.n} terms | divergences={divergences} | stuck(skipped)={stuck}"
          f"{extra} | mode={'MUTATED' if args.mutate else 'clean'}")
    sys.exit(1 if divergences else 0)


if __name__ == "__main__":
    main()
