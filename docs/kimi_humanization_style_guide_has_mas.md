# Kimi Humanization Style Guide — HAS/MAS Documents

This guide adapts the base
[kimi_humanization_style_guide.md](kimi_humanization_style_guide.md) for
Hardware Architecture Specifications (HAS) and Micro-Architecture
Specifications (MAS). Voice, personality, and every language rule from the
base guide apply unchanged. What's different here is the **container**:
these are chaptered, versioned, table-heavy engineering specifications
that build into DOCX/PDF through a pandoc pipeline — their structure is
load-bearing and must survive humanization byte-exact.

## The One-Sentence Rule

Humanize the **prose between the structure**. Never the structure itself.

## Structure You Must NOT Touch

The build pipeline (`md_to_docx.py` via each doc's `generate_*_pdf.sh`)
and the cross-reference web depend on these being byte-identical:

1. **Heading lines** — text, level (`#`/`##`/`###`), and order. Chapter
   and section titles are referenced from index files and other chapters.
   If a title is clumsy, flag it in your notes; don't rename it.
2. **File and directory names** — `chNN_*/NN_*.md` numbering is the
   stitch order. Never rename, split, or merge files.
3. **Index files** (`*_index.md`) — the link lists ARE the document
   assembly manifest. Prose paragraphs inside them may be humanized;
   every link line stays verbatim.
4. **Tables** — column structure, header rows, and cell CONTENT for
   signal names, widths, encodings, parameter values, file paths.
   You may rephrase a descriptive-text cell if it contains full prose
   sentences, but never a name/value/encoding cell.
5. **Pandoc caption lines** — `: Table 2.1: ...` / `: Figure 3.2: ...`
   syntax and numbering exactly as written.
6. **Code blocks** — everything fenced (```toml, ```systemverilog,
   ```text diagrams) is untouchable, comments included. RTL comments
   were written against the code; "humanizing" them detaches them
   from it.
7. **Signal/module/file identifiers in prose** — `axi5_atomic_filter`,
   `fub_axi_*`, `AWATOP[5]`, `bin/bridge_pkg/sideband.py`. Backticked
   or not, identifiers are data.
8. **Front matter and metadata lines** — revision tables, `**Module:**`
   / `**Status:**` blocks, copyright, the styles YAML.
9. **Cross-reference links** — path and anchor. Link TEXT may be
   smoothed only if the target title is quoted verbatim elsewhere in it.
10. **Admonition markers** — lines beginning `> **HISTORICAL`,
    `> **Note`, etc. keep their marker word; the sentence after it is
    fair game.

## What You SHOULD Humanize

- **Overview and rationale paragraphs** — this is where LLM-flavored
  filler accumulates and where the base guide's voice pays off most.
  Lead with the decision, then the why. Kill "provides comprehensive
  support for", "is responsible for", "in order to".
- **Trade-off discussions** — make them honest and specific per the base
  guide's Architecture/Design rules: what it costs, what it buys, when
  to reconsider.
- **Transitions between sections** — a chaptered spec reads as a
  sequence of disconnected blocks when every section opens cold. One
  connecting sentence ("Now that the request path is routed, responses
  have to find their way back") earns its keep. Don't force one
  everywhere; these documents are reference material, and engineers
  jump straight to sections.
- **Failure-mode explanations** — walk through the failure like the
  base guide's bug-report voice: "So what happens when ready drops
  mid-burst?" is exactly right for a MAS.
- **Table intro sentences** — the sentence before a table should say
  what question the table answers, not announce that a table follows.

## Spec-Specific Calibration

HAS/MAS voice sits slightly more formal than a code review — these
documents outlive conversations and get read by people who never met
the author. Concretely:

- First person is fine in rationale ("I picked the union-of-features
  layout because...") but keep it OUT of normative statements. "The
  filter returns DECERR" — not "I return DECERR". Normative text states
  behavior; rationale text owns decisions.
- Wry asides go in parentheticals in rationale sections, at most one
  or two per chapter. A spec that's constantly winking is worse than
  one that never does.
- Keep RFC-ish force words (**must**, **never**, **only**) exactly
  where the original put them. They're contract language, not filler.
- Warnings about traps ("Here's the part that bites people:") are
  encouraged in MAS design-notes sections — that's institutional
  knowledge, the most valuable prose in the document.
- No summaries at chapter ends. The chapter structure IS the summary.

## Length Discipline

Humanization is not expansion. The right result is usually the same
length or shorter — LLM prose compresses well once the filler goes.
If a section grew more than ~10% after your pass, you added padding;
cut it. If it shrank 30%, check you didn't delete normative content.

## Workflow

1. Work one chapter file at a time; deliver each file complete
   (structure verbatim + humanized prose), not as a diff or commentary.
2. After each file, run the final-check questions from the base guide,
   plus one more: **would this file still build?** If you touched a
   heading, a caption, a fence, or a link — put it back.
3. Do not re-version documents. The `--rev` bump happens at build time,
   after the humanization pass is reviewed.
