# TASK-009: Verification reference models for andesite (DRAMsim3 cross-check, BFM CA encoder tests)
> Source: `/mnt/data/github/dfi-specs/ddr4/index.md` and `lpddr4/index.md`
> verification sections

**Priority:** P3
**Status:** open 2026-10-04
**Owner:** TBD

The HAS ch06 verification strategy names the DFI 4.0 BFM as the sole
counterparty. The research set names two more: **DRAMsim3** (cycle-accurate
DDR4/LPDDR4 timing models; the standard free cross-check for a controller's
command stream) and **round-trip encode/decode tests** for the LPDDR4 6-bit
CA encoder (the in-house BFM has `lpddr_ca.py` for LPDDR2/3 and an
`lpddr4_ca.py` is explicitly noted as missing — building it is BFM work that
gates the MAS CA submodule's verification). Record both in HAS ch06's
verification strategy at its next edit pass, and fold the `lpddr4_ca.py` gap
into andesite TASK-005's BFM study. Closes when the ch06 strategy names all
three counterparties and the TASK-005 scope note includes the CA-encoder gap.
