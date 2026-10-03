# TASK-002: Author the BCH HAS v0.1

**Status:** open 2026-10-03
**Priority:** P3 — the component has no consumer yet; the HAS is the next
planning artifact after the PRD, the same posture reed-solomon TASK-002 had
**Owner:** TBD

The BCH PRD fixes only D7 (share the reed-solomon GF layer), D9 direction
(valid/ready core plus wrapper adapters), D10 direction (consumer deferred to
the memory-controller project), and D12 (scrambler out of scope). Everything
else is open with candidates. The HAS must describe the target architecture
honestly: no RTL, no measured numbers, every TBD tied to a PRD decision ID,
and the structural facts that separate binary BCH from the sibling RS codec
(no Forney stage, bit-level Chien/flip, only t odd syndromes).

## Scope

- `projects/components/ecc-ip/bch/docs/bch_has/` mirroring
  `projects/components/ecc-ip/reed-solomon/docs/reed_solomon_has/`:
  index, styles, front matter, six chapters, assets/mermaid sources, and a
  PDF generator if the reed-solomon script is one-line adaptable.
- The document must cite the PRD decision table (D1-D12), the candidate
  profiles, and the references in `projects/components/ecc-ip/bch/References/`.
- Every open item is marked **TBD** and tied to a PRD decision ID; no
  placeholder prose; no emoji.

## Definition of done

- The v0.1 PDF builds from `docs/generate_has_pdf.sh`.
- Every TBD in the HAS names the PRD decision that resolves it.
- `bin/check_task_ids.py --area projects/components/ecc-ip/bch/task` passes.

## Log

**2026-10-03 -- v0.1 skeleton authored.** `docs/bch_has/` tree landed with
index, styles, front matter, six chapters, mermaid sources, and the PDF
generator; every open item is tied to a PRD decision ID.
