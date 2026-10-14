# STREAM MAS Mermaid Diagrams

This directory holds the Mermaid sources (`.mmd`) for the STREAM MAS figures
together with the PNGs rendered from them. Each source and its PNG sit side by
side. Chapters reference the `.png`. Why it is PNG and not SVG, and the rest of
the pipeline, are covered in `vault/handbook/authoring/doc-pipeline.md` and
`bin/DOC_GENERATION.md`.

## Files

Each diagram has:
- **Source:** `{diagram_id}.mmd`, the file you edit
- **Generated:** `{diagram_id}.png`, rendered from the source and referenced by the chapter

For example, the scheduler FSM figure in `ch02_blocks/04_scheduler.md`:

```
02_scheduler_fsm.mmd   <- edit this
02_scheduler_fsm.png   <- regenerated from the .mmd
```

Run `ls *.mmd` to see the current set. A list kept here would drift.

## Regenerating

Use the committed batch script, not an ad hoc `mmdc` call:

```bash
./regenerate_all_diagrams.sh          # every .mmd -> .png (SCALE=2 by default)
SCALE=3 ./regenerate_all_diagrams.sh  # higher-resolution render
```

The script writes the puppeteer `--no-sandbox` config that headless Chromium
needs on Ubuntu 23.10+ and later releases ("No usable sandbox!"). It also
reports any diagram that fails to render. Rebuild the book PDF afterwards with
`../../../generate_mas_pdf.sh`.

## Referencing a diagram from a chapter

```markdown
### Figure 2.4.2: Scheduler FSM

![Scheduler FSM](../assets/mermaid/02_scheduler_fsm.png)

**Source:** [02_scheduler_fsm.mmd](../assets/mermaid/02_scheduler_fsm.mmd)
```

## Troubleshooting

- **Parse errors:** quote labels that contain special characters, for example
  `"label (a, b)"` rather than `{a, b}`.
- **Render fails or times out:** check the `.mmd` syntax first. The script
  prints the first lines of the `mmdc` error for each failed diagram.
- **Requirement:** Mermaid CLI (`npm install -g @mermaid-js/mermaid-cli`).
