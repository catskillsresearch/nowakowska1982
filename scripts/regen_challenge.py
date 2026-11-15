#!/usr/bin/env python3
"""Regenerate Mathlib-only Challenge.lean from Actions/ + comparator.json."""
from __future__ import annotations

from pathlib import Path
import json
import re
from collections import defaultdict, deque

ROOT = Path(__file__).resolve().parents[1]
cfg = json.load(open(ROOT / "comparator.json"))
thm_names = set(cfg["theorem_names"])
def_names = set(cfg.get("definition_names", []))

# Skip Bar-Hillel internals; Language.inter_regular is appended by hand.
SKIP_FILES = {
    "Promise/CFInterRegular.lean",
}

files = {
    str(p.relative_to(ROOT / "Actions")): p
    for p in (ROOT / "Actions").rglob("*.lean")
    if str(p.relative_to(ROOT / "Actions")) not in SKIP_FILES
}


def mod_of(rel: str) -> str:
    return "Actions." + Path(rel).with_suffix("").as_posix().replace("/", ".")


deps: dict[str, set[str]] = defaultdict(set)
all_mods: set[str] = set()
for rel, p in files.items():
    mod = mod_of(rel)
    all_mods.add(mod)
    for m in re.finditer(r"^(?:public )?import\s+(Actions\.\S+)", p.read_text(), re.M):
        deps[mod].add(m.group(1))

indeg = {m: sum(1 for d in deps[m] if d in all_mods) for m in all_mods}
q = deque([m for m, c in indeg.items() if c == 0])
order: list[str] = []
while q:
    m = q.popleft()
    order.append(m)
    for n in all_mods:
        if m in deps[n]:
            indeg[n] -= 1
            if indeg[n] == 0:
                q.append(n)
for m in all_mods:
    if m not in order:
        order.append(m)


def path_for(mod: str) -> Path | None:
    rel = mod[len("Actions.") :].replace(".", "/") + ".lean"
    p = ROOT / "Actions" / rel
    if p.exists():
        return p
    hits = list((ROOT / "Actions").rglob(Path(rel).name))
    return hits[0] if hits else None


def is_thm_start(line: str) -> bool:
    return bool(
        re.match(
            r"^(?:noncomputable\s+|protected\s+|private\s+)*"
            r"(theorem|lemma|corollary)\b",
            line,
        )
    )


def is_def_start(line: str) -> bool:
    return bool(
        re.match(
            r"^(?:noncomputable\s+|protected\s+|private\s+|abbrev\s+)*"
            r"(def|abbrev|structure|class|inductive|instance|opaque)\b",
            line,
        )
    )


def is_any_decl(line: str) -> bool:
    return is_thm_start(line) or is_def_start(line)


def fqn_of(ns_stack: list[str], name: str) -> str:
    short = name.split(".")[-1]
    parts = name.split(".") if "." in name else [short]
    if ns_stack and ns_stack[0] in ("Actions", "Language"):
        return ".".join(ns_stack + parts)
    return "Actions." + ".".join(ns_stack + parts)


def skip_doc_or_attr(lines: list[str], i: int) -> int:
    while i < len(lines):
        line = lines[i]
        if line.startswith("/-!") or line.startswith("/--") or (
            line.startswith("/-") and not line.startswith("/--")
        ):
            if "-/" in line:
                i += 1
                continue
            i += 1
            while i < len(lines) and "-/" not in lines[i]:
                i += 1
            if i < len(lines):
                i += 1
            continue
        if line.strip().startswith("--"):
            i += 1
            continue
        if line.startswith("@[expose]") or line.strip() == "public section":
            i += 1
            continue
        if line.startswith("open ") or line.startswith("set_option ") or line.startswith(
            "universe "
        ):
            i += 1
            continue
        break
    return i


def collect_attrs(lines: list[str], i: int) -> tuple[list[str], int]:
    attrs: list[str] = []
    while i < len(lines) and lines[i].startswith("@["):
        # skip @[simp] etc on theorems we may drop; keep attrs for defs/structures
        attrs.append(lines[i])
        i += 1
        i = skip_doc_or_attr(lines, i)
    return attrs, i


def decl_end(lines: list[str], i: int) -> int:
    j = i + 1
    while j < len(lines):
        L = lines[j]
        if L.startswith("@[") or is_any_decl(L) or re.match(r"^namespace\s|^end\b", L):
            break
        # Doc comments bind to the *next* decl; do not swallow them into this one.
        if L.startswith("/--") or L.startswith("/-!") or (
            L.startswith("/-") and not L.startswith("/--")
        ):
            break
        j += 1
    return j


mathlib_imps: set[str] = {
    "Mathlib.Tactic",
    "Mathlib.Computability.ContextFreeGrammar",
    "Mathlib.Computability.DFA",
    "Mathlib.Data.Finset.Card",
    "Mathlib.Data.Fintype.Basic",
}
chunks: list[str] = []
kept: list[str] = []

for mod in order:
    f = path_for(mod)
    if not f:
        continue
    text = f.read_text()
    for m in re.finditer(r"^(?:public )?import\s+(Mathlib\.\S+)", text, re.M):
        mathlib_imps.add(m.group(1))
    lines = text.splitlines()
    start = 0
    for i, L in enumerate(lines):
        if L.startswith("namespace "):
            start = i
            break
    lines = lines[start:]
    ns_stack: list[str] = []
    out: list[str] = []
    i = 0
    while i < len(lines):
        i = skip_doc_or_attr(lines, i)
        if i >= len(lines):
            break
        line = lines[i]
        mns = re.match(r"^namespace\s+([A-Za-z0-9_\.]+)", line)
        if mns:
            for p in mns.group(1).split("."):
                ns_stack.append(p)
            out.append(line)
            i += 1
            continue
        if re.match(r"^end\b", line):
            if ns_stack:
                ns_stack.pop()
            out.append(line)
            i += 1
            continue

        # Attributes may precede theorem or def
        if line.startswith("@["):
            attrs, i2 = collect_attrs(lines, i)
            if i2 >= len(lines):
                break
            if is_thm_start(lines[i2]):
                m = re.match(
                    r"^(?:noncomputable\s+|protected\s+|private\s+)*"
                    r"(theorem|lemma|corollary)\s+(\S+)",
                    lines[i2],
                )
                if not m:
                    raise SystemExit(f"thm parse fail at {f}:{i2+1}: {lines[i2]!r}")
                fqn = fqn_of(ns_stack, m.group(2))
                j = decl_end(lines, i2)
                if fqn in thm_names:
                    # drop simp attrs on challenge holes
                    hdr: list[str] = []
                    for k in range(i2, j):
                        L = lines[k]
                        if L.rstrip().endswith(" where"):
                            hdr.append(L.rstrip()[:-6])
                            break
                        if ":=" in L:
                            hdr.append(L.split(":=")[0].rstrip())
                            break
                        hdr.append(L)
                    out.append("\n".join(hdr).rstrip() + " := by")
                    out.append("  sorry")
                    kept.append(fqn)
                i = j
                continue
            if is_def_start(lines[i2]):
                j = decl_end(lines, i2)
                # keep attrs for structures/instances
                out.extend(attrs)
                out.extend(lines[i2:j])
                i = j
                continue
            # unknown after attr: skip attrs
            i = i2
            continue

        if is_thm_start(line):
            m = re.match(
                r"^(?:noncomputable\s+|protected\s+|private\s+)*"
                r"(theorem|lemma|corollary)\s+(\S+)",
                line,
            )
            if not m:
                raise SystemExit(f"thm parse fail at {f}:{i+1}: {line!r}")
            fqn = fqn_of(ns_stack, m.group(2))
            j = decl_end(lines, i)
            if fqn in thm_names:
                hdr = []
                for k in range(i, j):
                    L = lines[k]
                    if L.rstrip().endswith(" where"):
                        hdr.append(L.rstrip()[:-6])
                        break
                    if ":=" in L:
                        hdr.append(L.split(":=")[0].rstrip())
                        break
                    hdr.append(L)
                out.append("\n".join(hdr).rstrip() + " := by")
                out.append("  sorry")
                kept.append(fqn)
            i = j
            continue

        if is_def_start(line):
            m = re.match(
                r"^(?:noncomputable\s+|protected\s+|private\s+|abbrev\s+)*"
                r"(def|abbrev)\s+([A-Za-z0-9_\'\.]+)",
                line,
            )
            j = decl_end(lines, i)
            if m:
                fqn = fqn_of(ns_stack, m.group(2))
                if fqn in def_names:
                    # Compared definitions are statement-of-record formulas:
                    # keep the body (do not hole out with `sorry`).
                    out.extend(lines[i:j])
                    kept.append(fqn)
                    i = j
                    continue
            out.extend(lines[i:j])
            i = j
            continue

        if line.strip() == "":
            if out and out[-1] != "":
                out.append("")
            i += 1
            continue
        # Keep section scaffolding only; never emit orphaned proof tactics.
        if re.match(r"^variable\b", line) or re.match(r"^attribute\b", line):
            out.append(line)
            i += 1
            continue
        # Skip unrecognized lines (typically bodies of dropped @[simp] lemmas).
        i += 1
        continue

    chunk = "\n".join(out).strip()
    if chunk:
        chunks.append(chunk)

# Hand-written Language.inter_regular (Mathlib-only statement)
if "Language.IsContextFree.inter_regular" in thm_names:
    chunks.append(
        """namespace Language
variable {T : Type*}
theorem IsContextFree.inter_regular {L R : Language T}
    (hL : L.IsContextFree) (hR : R.IsRegular) : (L ⊓ R).IsContextFree := by
  sorry
end Language"""
    )
    kept.append("Language.IsContextFree.inter_regular")

print("kept", len(kept))
print("missing", sorted(thm_names - set(kept)))

body = "\n".join(chunks)
body = re.sub(r"\n{3,}", "\n\n", body)
prev = None
while prev != body:
    prev = body
    body = re.sub(r"\nnamespace (\S+)\nend \1(?=\n|$)", "\n", body)
    body = re.sub(r"\nnamespace (\S+)\n\nend \1(?=\n|$)", "\n", body)
body = re.sub(r"\n{2,}", "\n", body)

header = """/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

"""
imps = "\n".join(f"public import {m}" for m in sorted(mathlib_imps))
doc = """
/-!
# Palomar Challenge (statement of record)

Single-file Mathlib-only Challenge. Compared declarations match `Solution.lean`
via the sorry-free `Actions/` library. Framing: reconstruction/verification of
Nowakowska 1982/1973, plus Lean discharge of classical CF ∩ Regular.
-/
@[expose] public section

"""
text = header + imps + "\n" + doc + body.strip() + "\n"
(ROOT / "Challenge.lean").write_text(text)
print(f"lines={text.count(chr(10))+1} bytes={len(text.encode())}")
