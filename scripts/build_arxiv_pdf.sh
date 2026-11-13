#!/usr/bin/env bash
# Flatten Actions.md → arxiv.md → arxiv.tex → Actions.pdf (Lean-highlighted).
set -euo pipefail
cd "$(dirname "$0")/.."

TEX="arxiv.tex"
PDF="arxiv.pdf"
OUT="Actions.pdf"

echo "==> Flattening Actions.md note tree (inline Lean)"
python3 scripts/compile_md_tree.py --md-only --lean=inline

echo "==> Preparing arxiv_with_code.md"
cp -f arxiv.md arxiv_with_code.md

echo "==> Building arxiv.tex + lean-listings/ + figures/"
python3 scripts/build_arxiv_tex.py

echo "==> Compiling PDF (pdfLaTeX via latexmk)"
latexmk -C "$TEX" >/dev/null 2>&1 || true
rm -f arxiv.aux arxiv.out arxiv.toc
latexmk -pdf \
  -pdflatex="pdflatex -interaction=nonstopmode -halt-on-error" \
  -interaction=nonstopmode \
  -halt-on-error \
  "$TEX" || {
  echo "latexmk reported errors; tail of log:" >&2
  tail -n 60 arxiv.log >&2 || true
  exit 1
}

echo "wrote $PDF ($(du -h "$PDF" | cut -f1))"
cp -f "$PDF" "$OUT"
cp -f "$PDF" view.pdf
echo "wrote $OUT and view.pdf"
