# Source materials

`nowakowska1982.pdf` is included for citation and transcription checking only.

## Vision OCR (triple pass + merge)

From the repo root (needs `pdftoppm`, and `CURSOR_API_KEY` in
`../tokens_ssto.yaml`):

```bash
bash scripts/ocr_pdf_pipeline.sh                          # full PDF
bash scripts/ocr_pdf_pipeline.sh --pages 1-3              # smoke test
bash scripts/ocr_pdf_pipeline.sh --png-only               # render pages only
bash scripts/ocr_pdf_pipeline.sh --status                 # resume state
bash scripts/ocr_pdf_pipeline.sh --merge-only             # restitch merged.md
```

Outputs:

| Path | Role |
|------|------|
| `sources/pages/nowakowska1982/` | Per-page PNGs + `pass{1,2,3}.md` + `merged.md` |
| `sources/nowakowska1982.md` | Stitched draft transcription |
| `sources/ocr_nowakowska1982_run.log` | Run log |

Model: `composer-2.5` (same as scott1964 OCR runs).
