# md_to_docx.py -- usage

Current flags: `python3 bin/md_to_docx.py --help`. That is the only source that
cannot drift, and it is why this file is a pointer.
Pipeline mechanics (document unit, index, styles, generate script):
**`bin/DOC_GENERATION.md`**.
Decisions and traps (`--style` picks the engine, PNG never SVG, captions drive
LoF/LoT/LoW): **`vault/handbook/authoring/doc-pipeline.md`**.

What was here documented `-t/--template`, `-o/--output` and `--verbose`, none of
which the tool has, and `md_to_docx.py input.md` with one positional when it
takes two (`input output`). Following it produced an argparse error, so this was
worse than redundant.
