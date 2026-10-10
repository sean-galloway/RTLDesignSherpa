# TASK-006: CA parity / ALERT_n recovery sub-FSM (DDR4)
> Source: `/mnt/data/github/dfi-specs/ddr4/index.md` "Key Design Ideas" #4
> (research index, operator cold storage)

**Priority:** P3
**Status:** closed 2026-10-04 — completed and owner-directed (pre-RTL creation pass)
**Owner:** TBD

The HAS/MAS specify CA parity generation and name the `alert_n` return path,
but no recovery mechanism: andesite MAS ch02 01_cmd_formatter says the
sequencer "owns the recovery policy" without specifying it. The research
index's recommendation: keep the recovery state machine out of the main bank
machine — a 3-state error sub-FSM (idle -> alert_seen -> resending) suffices,
plus dropping the suspect command and retransmitting. Specify it in the MAS
(add to `01_cmd_formatter.md` or the sequencer page) at the next MAS edit
pass, reconciled against the DFI 4.0 alert/parity clauses once andesite
TASK-005's confirmation pass lands. Closes when the MAS carries the recovery
FSM states, the drop/retransmit policy, and its interaction with the
scheduler's grant stream.
