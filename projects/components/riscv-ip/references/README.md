# Reference Shelf

Common reference material for every rung of the falcon suite. Per-rung
doc books (`docs/simplified_*` in each core's directory) cite sections of
these primary sources; they do not restate them.

| File | What it is | Provenance |
|---|---|---|
| [`riscv-spec.pdf`](riscv-spec.pdf) | *The RISC-V Instruction Set Manual* — the combined Unprivileged (Volume I) + Privileged (Volume II) specification, 909 pages | `riscv/riscv-isa-manual` GitHub release `riscv-isa-release-d641d8e-2026-10-06` (fetched 2026-10-06) |

The combined volume is the working reference for all four cores. When a
book or RTL comment cites the spec, cite the chapter (e.g. "unpriv ch.
2.5, JALR") rather than a page number — page numbers drift between spec
releases.

Research literature behind the design decisions is curated in
[`microarchitecture-papers.md`](microarchitecture-papers.md) — twenty
papers organized by the decision each guides (pipeline partition, branch
prediction, precise interrupts, write policies, checkpoint-restore OOO,
and the interleaved multithreading behind gatling's barrel), with honest
availability notes. The same file ends with the textbook chapters the
rung books cite and the short keys (H&P6, P&H, H&H, ...) they cite them
by; the books themselves are the owner's library, machine-local, see
`vault/handbook/book-library.md`.

Where a legitimate open PDF exists, a local copy lives in
[`papers/`](papers/README.md) (RISC I, the Waterman dissertation, and
the BOOM report as of 2026-10-07); the other twelve are paywalled with
full citations in the list — fetch them through an institutional
subscription.

Future additions as rungs demand them: the RISC-V psABI (toolchain run),
the debug specification, profile docs. Add them here with the same
provenance table row.
