# md_to_docx.py -- installation

Toolchain setup, and the gotchas that actually bite here:
**`vault/handbook/authoring/doc-pipeline.md`**.
Pipeline mechanics: **`bin/DOC_GENERATION.md`**.
Current flags: `python3 bin/md_to_docx.py --help`.

This file carried a generic walkthrough -- install Python, make a venv, install
Pandoc, optionally install LaTeX -- none of it repo-specific, and it ended with
an invocation the tool rejects (`-t`, `-o` and `--verbose` do not exist). A
second copy next to the code is how documentation rots; the copy nobody edits
is the one the next session reads.
