# TASK-008: reconcile the scoria HAS to a 1.0

HAS v0.8 matches what implementation and the first board work have settled,
but three things separate it from a 1.0 — named in its own Chapter 6, filed
here so the ledger carries them:

1. **A value chosen for `tWLMRD`'s controller-defined maximum.** Q4 reduced
   this to a one-line policy decision: no PHY supplies one (LiteDRAM's
   `s7ddrphy` has no timeout of any kind), JESD79-3F declares it
   controller-dependent, and at CK = 2.5 ns on the named target a generous
   bound is easy to pick. The requirement is that the CSR timeout exists and
   reports distinctly, not that it be tight.
2. **Block-by-block reconciliation of every INHERITED / MODIFIED / NEW
   marking against the landed RTL.** Each marking confirmed or corrected in
   the document. A marking that turns out wrong is a defect in the document;
   the correction goes in the revision history rather than being dropped
   silently. v0.8 reconciled what had settled; this is the systematic pass.
3. **The exact CSR map, finalized from the RDL that now exists**
   (`rtl/macro/scoria_csr.rdl`, with generated documentation and Python
   regmap in `regs/generated/`). The HAS specifies CSR groups (Ch 5) but not
   offsets; the generated docs and the HAS must be brought to agree.

**Priority:** P2 — nothing is blocked. The RTL is verified (221 tests, 9
formal blocks), the PRD cites the HAS as binding, and the board work is gated
by BUG-003, not by this.
**Status:** OPEN, filed 2026-10-03 as the close-out of TASK-002, which
delivered the HAS and the PRD.
**Depends on:** nothing. Supersedes nothing — TASK-002 closed the "author
the HAS / replace the PRD stub" scope; this is the remaining road to 1.0.

## Done when

- `tWLMRD`'s maximum has a chosen value, present in the CSR with its own
  status bit.
- Every block marking in the HAS is confirmed against the RTL or corrected,
  and the revision history records each correction.
- The CSR group descriptions in the HAS agree with the generated RDL
  documentation.
- The document is re-issued as 1.0 (sources and the published book).
