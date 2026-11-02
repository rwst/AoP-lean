#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# Released under CC0 1.0 Universal (public-domain dedication).
# See https://creativecommons.org/publicdomain/zero/1.0/
"""Generate a brief's comparator challenge from the development.

Adapted from `scripts/make-challenge.py` of Subspace-Theorems (paper lanes only). For the brief
`B` it reads the certified theorems from `briefs/B/comparator/theorems.txt` and writes, in the
same directory,

* `ChallengeB.lean`, the certified statements in one module that imports only Mathlib, physlib and
  TauCeti, and
* `comparator.json`, the configuration `lake comparator` checks against the hand-written
  re-export `SolutionB.lean`.

Nothing here is written by hand, and nothing is paraphrased: every definition in the compared
closure that belongs to this project (`ForMathlib`, `ForPhyslib` or a brief library), and every
theorem such a definition mentions, is copied from its source file character for character,
docstrings and comments dropped; every certified theorem is copied up to its `:=` and given a
`sorry` proof. Each copied part keeps the source file's `namespace`, `section`, `open` and
`variable` commands that some copied declaration follows, and nothing else. Why the challenge
looks as it does is in `COMPARATOR.md`.

Usage, from the repository root, after `lake build`:

    python3 scripts/make-challenge.py --brief BornRuleEntropy

The data pass runs `lake env lean` on a generated metaprogram that imports the modules
`SolutionB.lean` imports; it honours `LEAN_NUM_THREADS` (default 3).
"""
import collections
import json
import os
import re
import subprocess
import sys
import textwrap

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if "--brief" not in sys.argv:
    raise SystemExit("usage: make-challenge.py --brief <BriefLibrary> [--no-data]")
BRIEF = sys.argv[sys.argv.index("--brief") + 1]
LANE = os.path.join(ROOT, "briefs", BRIEF, "comparator")
DATA = os.path.join(ROOT, ".lake", f"challenge-data-{BRIEF}")
THEOREMS = os.path.join(LANE, "theorems.txt")
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]


def brief_libraries():
    """Library name → source directory, for every brief library of `lakefile.toml`."""
    out, name = {}, None
    for line in open(os.path.join(ROOT, "lakefile.toml")):
        m = re.match(r'^name = "(\w+)"', line)
        if m:
            name = m.group(1)
        m = re.match(r'^srcDir = "(briefs/[^"]+)"', line)
        if m and name:
            out[name] = m.group(1)
    return out


# The development: the libraries whose declarations a challenge copies rather than imports. Every
# brief library counts, so that a brief building on another one is handled like one building on
# `ForPhyslib`.
BRIEF_SRC = brief_libraries()
DEV_ROOTS = ("ForMathlib", "ForPhyslib") + tuple(sorted(BRIEF_SRC))
if BRIEF not in BRIEF_SRC:
    raise SystemExit(f"make-challenge: {BRIEF} is not a brief library of lakefile.toml")

HEADER = """/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
"""

# The metaprogram of the data pass. For the certified theorems it writes the compared closure —
# every declaration of the development reached from a theorem's *type*, following the types and
# values of definitions and the proofs of theorems, which is exactly what comparator walks — and
# for the whole development every declaration's line range and the import graph.
METAPROGRAM = r'''
open Lean Elab Command

def challengeOwner (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  let m := env.header.moduleNames[idx.toNat]!
  if [DEV_ROOTS].any (·.isPrefixOf m) then some m else none

def challengeClosure (env : Environment) (root : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  let mut stack : Array Name := (env.find? root).get!.type.getUsedConstants
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if (challengeOwner env n).isNone then continue
    out := out.push n
    -- `Y._proof_n` is minted by `Y` and cached for the rest of the module, where a later
    -- declaration can reuse it; the copy reproduces the name only if `Y` is copied too.
    if let .str p s := n then
      if s.startsWith "_proof_" then stack := stack.push p
    stack := stack ++ ci.type.getUsedConstants ++
      ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
    match ci with
    | .inductInfo i => stack := stack ++ i.ctors.toArray
    | .ctorInfo c => stack := stack.push c.induct
    | _ => pure ()
  return out

elab "#challengeData " dir:str : command => do
  let env ← getEnv
  let dir := dir.getString
  let names := (← IO.FS.lines (dir ++ "/theorems.txt")).filter (· ≠ "")
  let mut rows : Array String := #[]
  let mut done : NameSet := {}
  for s in names do
    let root := s.toName
    unless env.contains root do throwError "not a declaration: {root}"
    for c in (challengeClosure env root).push root do
      if done.contains c then continue
      done := done.insert c
      let some m := challengeOwner env c | continue
      if isPrivateName c then
        throwError "{root} reaches the private constant {c}; comparator cannot compare it"
      let kind := if (env.find? c).get!.isThm then "thm" else "def"
      let tgt := if c == root then "TARGET" else "dep"
      let range := match ← findDeclarationRanges? c with
        | some r => s!"{r.range.pos.line}\t{r.range.endPos.line}"
        | none => "-\t-"
      rows := rows.push s!"{m}\t{range}\t{kind}\t{tgt}\t{c}"
  IO.FS.writeFile (dir ++ "/closure.tsv") (String.intercalate "\n" rows.toList)
  let mut decls : Array String := #[]
  for (c, _) in env.constants.map₁.toList do
    let some m := challengeOwner env c | continue
    if let some r ← findDeclarationRanges? c then
      decls := decls.push s!"{m}\t{r.range.pos.line}\t{r.range.endPos.line}"
  IO.FS.writeFile (dir ++ "/decls.tsv") (String.intercalate "\n" decls.toList)
  let mut outside : NameSet := {}
  for (c, _) in env.constants.map₁.toList do
    if (challengeOwner env c).isNone then
      let mut p := c.getPrefix
      while !p.isAnonymous && !outside.contains p do
        outside := outside.insert p
        p := p.getPrefix
  let mut names : Array String := #[]
  let mut nsSeen : NameSet := {}
  for (c, _) in env.constants.map₁.toList do
    if (challengeOwner env c).isNone || isPrivateName c then continue
    names := names.push s!"decl\t{c}"
    let mut p := c.getPrefix
    while !p.isAnonymous && !nsSeen.contains p do
      nsSeen := nsSeen.insert p
      unless outside.contains p do names := names.push s!"ns\t{p}"
      p := p.getPrefix
  IO.FS.writeFile (dir ++ "/names.tsv") (String.intercalate "\n" names.toList)
  let mut graph : Array String := #[]
  for i in [0:env.header.moduleNames.size] do
    for imp in env.header.moduleData[i]!.imports do
      graph := graph.push s!"{env.header.moduleNames[i]!}\t{imp.module}\t{imp.isExported}"
  IO.FS.writeFile (dir ++ "/graph.tsv") (String.intercalate "\n" graph.toList)
'''


def is_dev(mod):
    return mod.split(".")[0] in DEV_ROOTS


def path_of(mod):
    parts = mod.split(".")
    base = os.path.join(ROOT, BRIEF_SRC[parts[0]]) if parts[0] in BRIEF_SRC else ROOT
    return os.path.join(base, *parts) + ".lean"


def read_theorems():
    """The certified theorems, in file order; `#` starts a comment."""
    out = []
    for line in open(THEOREMS):
        line = line.split("#", 1)[0].strip()
        if line:
            out.append(line)
    return out


def solution_roots():
    """The modules `SolutionB.lean` imports: the ones owning the certified statements."""
    sol = os.path.join(LANE, f"Solution{BRIEF}.lean")
    return [mm.group(1) for mm in (re.match(r"^(?:public )?import (\S+)", l)
            for l in open(sol)) if mm]


def run_data_pass(theorems):
    os.makedirs(DATA, exist_ok=True)
    with open(os.path.join(DATA, "theorems.txt"), "w") as f:
        f.write("\n".join(theorems) + "\n")
    roots = ", ".join(f"`{r}" for r in DEV_ROOTS)
    src = "".join(f"import {m}\n" for m in solution_roots()) + \
        METAPROGRAM.replace("[DEV_ROOTS]", f"[{roots}]") + \
        f'#challengeData "{DATA}"\n'
    prog = os.path.join(DATA, "ChallengeData.lean")
    with open(prog, "w") as f:
        f.write(src)
    threads = os.environ.get("LEAN_NUM_THREADS", "3")
    subprocess.run(["lake", "env", "lean", f"-j{threads}", prog], cwd=ROOT, check=True)


# ---------------------------------------------------------------------------------------------
# imports

IMPORT_RE = re.compile(r"^(public )?(meta )?import (\S+)\s*$")


def read_imports(mod):
    out = []
    for line in open(path_of(mod)):
        m = IMPORT_RE.match(line)
        if m:
            out.append((m.group(3), bool(m.group(1))))
    return out


def resolve(mod, chal_set):
    """The imports of the challenge copy of `mod`, in the source's load order, each `True` when
    public. An import of a development module that has a challenge copy becomes an import of the
    copy; one that has none is replaced by its own imports, recursively, at the same place, so
    that the external modules load in the same order. An import is public only along a path of
    public imports."""
    res = {}

    def walk(m, pub, stack):
        for imp, ipub in read_imports(m):
            p = pub and ipub
            if not is_dev(imp):
                res[imp] = res.get(imp, False) or p
            elif imp in chal_set:
                key = "Challenge." + imp
                res[key] = res.get(key, False) or p
            elif imp not in stack:
                walk(imp, p, stack | {imp})

    walk(mod, True, {mod})
    return res


def load_order(roots):
    """The external modules the development imports directly, in the order Lean loads the
    development from `roots`: a depth-first walk over each file's imports in file order."""
    order, seen = [], set()

    def walk(m):
        for imp, _ in read_imports(m):
            if imp in seen:
                continue
            seen.add(imp)
            if is_dev(imp):
                walk(imp)
            else:
                order.append(imp)

    for r in roots:
        if r not in seen:
            seen.add(r)
            walk(r)
    return order


def reduce_imports(mods, roots):
    """`mods` maps each external module to `True` (public) or `False`. Keep the development's
    load order; drop a module only when an import earlier in that order already loads it, which
    does not move it, and makes it visible (publicly, when it is a public import)."""
    edges, pedges = collections.defaultdict(set), collections.defaultdict(set)
    for row in open(os.path.join(DATA, "graph.tsv")):
        x, y, pub = row.rstrip("\n").split("\t")
        edges[x].add(y)
        if pub == "true":
            pedges[x].add(y)
    cache = {}

    def closure(m, g):
        if (m, id(g)) not in cache:
            seen, todo = set(), [m]
            while todo:
                for y in g[todo.pop()]:
                    if y not in seen:
                        seen.add(y)
                        todo.append(y)
            cache[(m, id(g))] = seen
        return cache[(m, id(g))]

    kept, loaded = [], set()
    for m in load_order(roots):
        if m not in mods:
            continue
        pub = mods[m]
        visible = any(m in closure(o, pedges) for o, opub in kept if opub or not pub)
        if not (m in loaded and visible):
            kept.append((m, pub))
        loaded |= {m} | closure(m, edges)
    missing = set(mods) - {m for m, _ in kept} - loaded
    if missing:
        raise SystemExit(f"make-challenge: lost imports {sorted(missing)}")
    return kept


# ---------------------------------------------------------------------------------------------
# bodies

SECTION = (r"@\[expose\] public noncomputable section|@\[expose\] public section|"
           r"public noncomputable section|public section|noncomputable section")
CONTEXT_RE = re.compile(
    r"^(namespace|section|end|open|variable|universe|" + SECTION + r"|local notation|notation|"
    r"scoped|local infix|attribute \[local)")
OPEN_RE = re.compile(r"^(namespace|section|" + SECTION + r")\b\s*(\S*)")
# Notation commands: they declare constants of their own, but are copied as context.
NOTATION_RE = re.compile(r"^(local notation|notation|scoped|local infix)\b")
# The `:=` of a `letI x := …;` (or `haveI`, `let`, `have`) inside a statement.
LET_RE = re.compile(r"\b(letI|haveI|let|have)\b[^;]*$")
OPENERS = "([{⟨⦃"
CLOSERS = ")]}⟩⦄"


def strip_doc(text):
    """Drop a leading doc comment and full-line `--` comments."""
    text = text.lstrip("\n")
    if text.startswith("/--"):
        depth, i = 0, 0
        while i < len(text):
            if text.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif text.startswith("-/", i):
                depth, i = depth - 1, i + 2
                if depth == 0:
                    break
            else:
                i += 1
        text = text[i:].lstrip("\n")
    return "\n".join(l for l in text.split("\n") if not l.strip().startswith("--"))


def statement(text):
    """Cut a theorem at its top-level `:=` or `where` and give it a `sorry` proof."""
    depth = 0
    for i, c in enumerate(text):
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth == 0 and text.startswith(":=", i) and not LET_RE.search(text[:i]):
            return text[:i].rstrip() + " := by\n  sorry"
        elif depth == 0 and i > 0 and text[i - 1].isspace() and re.match(r"where\s", text[i:]):
            return text[:i].rstrip() + " := by\n  sorry"
    raise SystemExit("make-challenge: no top-level := in\n" + text)


def body(mod, needed, decls):
    """The module's copied declarations and context commands, as ("decl"|"ctx", text) items."""
    lines = open(path_of(mod)).read().split("\n")
    n = len(lines)
    covered = [False] * (n + 2)
    for s, e in decls[mod]:
        for l in range(s, e + 1):
            covered[l] = True
    keep = {s: (e, tgt) for s, e, tgt in needed[mod]}
    out, pending, l = [], [], 1          # `pending`: `… in` prefixes awaiting their declaration
    while l <= n:
        line = lines[l - 1]
        if l in keep:
            e, tgt = keep[l]
            text = strip_doc("\n".join(lines[l - 1:e]))
            out.append(("decl", "\n".join(pending + [statement(text) if tgt else text])))
            pending, l = [], e + 1
        elif NOTATION_RE.match(line):
            block = [line]
            l += 1
            while l <= n and lines[l - 1].startswith((" ", "\t")):
                block.append(lines[l - 1])
                l += 1
            out.append(("ctx", "\n".join(pending + block)))
            pending = []
        elif covered[l]:
            start = l
            while l <= n and covered[l] and l not in keep:
                l += 1
            run = "\n".join(lines[start - 1:l - 1])
            if any(NOTATION_RE.match(x) for x in run.split("\n")):
                # a notation command, with its `… in` prefixes: context, without its doc comment
                out.append(("ctx", "\n".join(pending + [re.sub(r"/--.*?-/\n?", "", run,
                                                               flags=re.DOTALL)])))
            pending = []
        elif CONTEXT_RE.match(line):
            block = [line]
            l += 1
            while l <= n and lines[l - 1].startswith((" ", "\t")) and not covered[l]:
                block.append(lines[l - 1])
                l += 1
            text = "\n".join(block)
            if re.search(r"\bin\s*$", text):
                pending.append(text)
            else:
                pending = []
                out.append(("ctx", text))
        elif re.match(r"^(omit|include|set_option|open)\b.*\bin\s*$", line):
            pending.append(line)
            l += 1
        elif line.startswith("/-"):
            depth = 0
            while l <= n:
                depth += lines[l - 1].count("/-") - lines[l - 1].count("-/")
                l += 1
                if depth <= 0:
                    break
        else:
            l += 1
    return out


def tree(items):
    """Nest the items into blocks `["block", header, children, closed]`."""
    root, stack, headers = [], [], []
    stack.append(root)
    for kind, text in items:
        if kind == "ctx" and OPEN_RE.match(text):
            node = ["block", text, [], False]
            stack[-1].append(node)
            stack.append(node[2])
            headers.append(node)
        elif kind == "ctx" and re.match(r"^end\b", text):
            headers.pop()[3] = True
            stack.pop()
        else:
            stack[-1].append((kind, text))
    return root


# What the copy may name: `NAMES` is filled by `main` from the data pass. A context command that
# names a development declaration left out of the copy, or opens a namespace that only such
# declarations populate, does not elaborate in the copy. No copied declaration can use what it
# introduces, or that declaration would be in the closure, so it is dropped.
NAMES = {"uncopied": set(), "copied": set(), "dev_ns": set(), "copied_ns": set()}
IDENT_RE = re.compile(r"[^\W\d][\w.'!?₀-₉ₐ-ₜ]*")


def scopes(ns):
    """The names `X` may stand for inside the namespace `ns`, innermost first."""
    return [".".join(ns[:k] + [""]) for k in range(len(ns), -1, -1)]


def uncopied(ident, ns):
    full = [p + ident for p in scopes(ns)]
    return (any(f in NAMES["uncopied"] for f in full)
            and not any(f in NAMES["copied"] for f in full))


def dead_ns(ident, ns):
    full = [p + ident for p in scopes(ns)]
    return (any(f in NAMES["dev_ns"] for f in full)
            and not any(f in NAMES["copied_ns"] for f in full))


def top_groups(text):
    """Split the binders of a `variable` command into its top-level bracket groups."""
    groups, depth, start = [], 0, None
    for i, ch in enumerate(text):
        if ch in OPENERS:
            if depth == 0:
                start = i
            depth += 1
        elif ch in CLOSERS:
            depth -= 1
            if depth == 0:
                groups.append(text[start:i + 1])
    return groups


def clean_ctx(text, ns):
    """`text` without what names left-out declarations; `None` when nothing is left."""
    m = re.match(r"^open( scoped)?((?: +[^\s()]+)+)\s*$", text)
    if m:
        keep = [x for x in m.group(2).split() if not dead_ns(x, ns)]
        return f"open{m.group(1) or ''} {' '.join(keep)}" if keep else None
    m = re.match(r"^open ([^\s()]+) \(([^()]*)\)\s*$", text, re.DOTALL)
    if m:
        # `open X (a b …)` names declarations of `X`: keep the ones the copy has
        keep = [x for x in m.group(2).split() if not uncopied(f"{m.group(1)}.{x}", ns)]
        return f"open {m.group(1)} ({' '.join(keep)})" if keep else None
    if text.startswith("variable"):
        groups = top_groups(text[len("variable"):])
        keep = [g for g in groups
                if not any(uncopied(x, ns) for x in IDENT_RE.findall(g))]
        if len(keep) == len(groups):
            return text
        return "variable " + " ".join(keep) if keep else None
    return text


def render(nodes, close, ns=()):
    """Drop the context commands no declaration follows and the blocks holding no declaration;
    with `close`, also end the blocks the source leaves open at the end of the file."""
    out, has_decl = [], False
    for idx, node in enumerate(nodes):
        if node[0] == "block":
            m = OPEN_RE.match(node[1])
            inner_ns = list(ns) + (m.group(2).split(".") if m.group(1) == "namespace" else [])
            inner, d = render(node[2], close, inner_ns)
            if d:
                has_decl = True
                out.append(node[1])
                out.extend(inner)
                if node[3] or close:
                    name = m.group(2) if m.group(1) in ("namespace", "section") else ""
                    out.append(("end " + name).rstrip())
        elif node[0] == "decl":
            has_decl = True
            out.append(node[1])
        elif any(n[0] == "decl" or (n[0] == "block" and render(n[2], close, ns)[1])
                 for n in nodes[idx + 1:]):
            text = clean_ctx(node[1], list(ns))
            if text is not None:
                out.append(text)
    return out, has_decl


def render_text(items, close):
    return "\n".join(render(tree(items), close)[0])


# Groups of instances of equal priority that the development does not choose between uniformly.
# Lean tries such instances in load order, the later-loaded first, and modules load their imports
# in different orders, so the same goal can elaborate with one instance in some modules and with
# another in the rest. Where the flat file ranks a group differently from a module's own, that
# module's part restores the module's ranking locally: its first choice keeps the common priority
# and the others go below it, one step each, in the module's order. Only a group comparator has
# rejected belongs here, listing every candidate seen chosen, with its module and the common
# priority. See `COMPARATOR.md`.
TIES = []

# Instances that some modules of the development never load, but the flat file does, and that
# outrank what those modules choose. In the part copied from a module that does not load the
# instance, it goes to priority 0. Each entry lists one that comparator has rejected, with its
# module. See `COMPARATOR.md`.
ABSENT = []


def post_order(roots, edges):
    """Module → position in the order Lean loads `roots` and everything they import."""
    seen, out = set(), []
    stack = [(r, False) for r in reversed(roots)]
    while stack:
        m, expanded = stack.pop()
        if expanded:
            out.append(m)
        elif m not in seen:
            seen.add(m)
            stack.append((m, True))
            stack.extend((c, False) for c in reversed(edges[m]) if c not in seen)
    return {m: i for i, m in enumerate(out)}


def pins(mod, flat_imports, edges):
    """The `attribute [local instance …]` lines the flat file needs for `mod`'s part."""
    dev = post_order(edges[mod], edges)
    flat = post_order(["Init"] + flat_imports, edges)
    out = []
    for group, prio in TIES:
        group = [(x, mx) for x, mx in group if mx in dev and mx in flat]
        want = sorted(group, key=lambda c: -dev[c[1]])       # the module's order, first tried first
        have = sorted(group, key=lambda c: -flat[c[1]])
        if want != have:
            for k, (x, _) in enumerate(want[1:], 1):
                out.append(f"attribute [local instance {prio - k}] {x}")
    for x, mx in ABSENT:
        if mx in flat and mx not in dev:
            out.append(f"attribute [local instance 0] {x}")
    return out


# The auxiliary-lemma cache (`Lean.Meta.auxLemmasExt`, "a mere cache, keep local") lives for one
# module. Clearing it between the former modules of the flat file makes each of them mint its own
# `_proof_` constants, as the development's modules do. See `COMPARATOR.md`.
RESET = "run_cmd Lean.modifyEnv (Lean.Meta.auxLemmasExt.setState · {})"

DOC_TEXT = ("Generated by `scripts/make-challenge.py --brief {brief}` from the brief library "
            "`{brief}` and the libraries it builds on; do not edit. Each `-- <module>` part "
            "repeats, verbatim, the definitions of that module the certified theorems mention, "
            "and states the theorems with `sorry`. Each part opens by clearing Lean's "
            "auxiliary-proof cache, as a module boundary does. See `COMPARATOR.md`.")


def doc(brief):
    """The challenge's module docstring, wrapped at 100 columns."""
    text = textwrap.fill(DOC_TEXT.format(brief=brief), width=100, break_long_words=False,
                         break_on_hyphens=False)
    return f"/-!\n# {brief}: the statements of record\n\n{text}\n-/\n\n"


def main():
    theorems = read_theorems()
    if "--no-data" not in sys.argv:
        run_data_pass(theorems)
    needed = collections.defaultdict(list)
    for row in open(os.path.join(DATA, "closure.tsv")):
        mod, s, e, _kind, tgt, name = row.rstrip("\n").split("\t")
        if s != "-":
            needed[mod].append((int(s), int(e), tgt == "TARGET"))
        NAMES["copied"].add(name)
        parts = name.split(".")
        NAMES["copied_ns"].update(".".join(parts[:k]) for k in range(1, len(parts)))
    for row in open(os.path.join(DATA, "names.tsv")):
        kind, name = row.rstrip("\n").split("\t")
        if kind == "ns":
            NAMES["dev_ns"].add(name)
        elif name not in NAMES["copied"]:
            NAMES["uncopied"].add(name)
    decls = collections.defaultdict(list)
    for row in open(os.path.join(DATA, "decls.tsv")):
        mod, s, e = row.rstrip("\n").split("\t")
        decls[mod].append((int(s), int(e)))
    chal_set = set(needed)
    deps = {m: [i[len("Challenge."):] for i in resolve(m, chal_set) if i.startswith("Challenge.")]
            for m in chal_set}
    order, done = [], set()

    def visit(m):
        if m not in done:
            done.add(m)
            for d in deps[m]:
                visit(d)
            order.append(m)

    for m in sorted(chal_set):
        visit(m)
    items = {m: body(m, needed, decls) for m in order}

    flat_name = f"Challenge{BRIEF}"
    flat_imps = {}
    for m in order:
        for i, p in resolve(m, chal_set).items():
            if not i.startswith("Challenge."):
                flat_imps[i] = flat_imps.get(i, False) or p
    flat_list = reduce_imports(flat_imps, solution_roots())
    edges = collections.defaultdict(list)
    for row in open(os.path.join(DATA, "graph.tsv")):
        x, y, _ = row.rstrip("\n").split("\t")
        if y not in edges[x]:
            edges[x].append(y)
    parts = []
    for m in order:
        text = render_text(items[m], True)
        pinned = pins(m, [i for i, _ in flat_list], edges)
        if pinned:
            text = "\n".join(pinned) + "\n" + text
        loose = pinned or any(n[0] == "ctx" for n in tree(items[m]))
        parts.append(f"-- {m}\n{RESET}\n" + (f"section\n{text}\nend" if loose else text))
    flat_path = os.path.join(LANE, flat_name + ".lean")
    with open(flat_path, "w") as f:
        f.write(HEADER + "module\n\n" + "".join(
            f"{'public ' if p else ''}import {i}\n" for i, p in flat_list)
            + "\n" + doc(BRIEF) + "\n".join(parts) + "\n")

    cfg = {"challenge_module": flat_name, "solution_module": f"Solution{BRIEF}",
           "theorem_names": theorems, "permitted_axioms": AXIOMS}
    with open(os.path.join(LANE, "comparator.json"), "w") as f:
        f.write(json.dumps(cfg, indent=2, ensure_ascii=False) + "\n")

    flat = open(flat_path, encoding="utf-8").read()
    print(f"make-challenge: {len(theorems)} theorems, {len(order)} copied modules; "
          f"{os.path.relpath(flat_path, ROOT)} is {flat.count(chr(10))} lines, "
          f"{len(flat.encode())} bytes")


main()
