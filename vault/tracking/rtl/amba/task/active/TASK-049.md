# TASK-049: CHI link-layer family (IHI 0050 Issue H): RTL, filelists, tests, docs

**Priority:** P2
**Status:** active 2026-10-30
**Owner:** sean galloway

Owner 2026-10-30: "create rtl collateral, similar to cxs, for chi" after the
RDS-DV CHI BFM family (RDS-DV #98) landed. The link layer of a CHI port
(chapters B13 and B14): credited channels, FLITPEND, one LINKACTIVE pair per
direction, LCrdReturn, SACTIVE. The Protocol layer (B2 to B12) stays on the
FUB side; this is the CHI counterpart of cxs_master / cxs_slave.

## Scope

- rtl/amba/includes/chi_pkg.sv: flit widths (Tables B13.6-B13.9), the Opcode
  and TxnID offsets the link layer reads, config_error with the rule numbers
  of the RDS-DV CHIConfig.
- rtl/amba/chi/chi_tx_channel.sv, chi_rx_channel.sv: one credited channel
  each way (skid buffer / receive FIFO as the credit pool).
- rtl/amba/chi/chi_link_tx.sv, chi_link_rx.sv: the LINKACTIVE controllers,
  cross-coupled for B14.6 and B14.6.3.4.
- rtl/amba/chi/chi_rnf_port.sv (TX REQ/RSP/DAT, RX RSP/DAT/SNP, prefix
  m_chi_) and chi_hnf_port.sv (TX RSP/DAT/SNP, RX REQ/RSP/DAT, prefix
  s_chi_).
- Filelists for all seven; val/amba/test_chi_{rnf,hnf}_port.py over
  bin/TBClasses/chi/ with the RDS-DV CHI BFMs as link partners and monitors;
  docs/markdown/rtl-amba/chi/ with block diagrams, _book_chi_index.md,
  rtl/amba/CLAUDE.md section.

## Not in scope (follow-ups)

- _cg clock-gated wrappers. (The _monlite wrappers and the ocelus CHI
  monitor-lite became TASK-050, built the same day.)
- Resource Planes and shared credits, replicated channels, interface parity
  (Check_Type), RN-I / RN-D / SN-F port tops.
- A Protocol-layer block (an RN-F requester or an HN-F home agent in RTL).

## Done

(filled in at close)
