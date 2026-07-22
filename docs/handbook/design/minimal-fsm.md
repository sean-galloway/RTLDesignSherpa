---
title: Minimal FSMs
summary: When a state machine is justified, keep it minimal and idiomatic.
---

# Minimal FSMs

Datapaths get pipelines, not FSMs ([[streaming-no-fsm]]). Where an FSM IS
right - descriptor lifecycle, schedulers, init sequencers - keep it minimal:

- Fewest states that carry the real distinctions. A state that only waits
  one fixed cycle, or that differs from a sibling only by a datapath value,
  is a register, not a state. Merge states whose outputs and successors are
  identical.
- Idiom: `typedef enum logic [N-1:0] {...} state_t;` + two-process form -
  registered `r_state`, combinational `w_next_state` with a default-hold
  first line (`w_next_state = r_state;`) and a default arm. One FSM per
  module; nested/communicating FSMs are a smell that the block wants
  splitting.
- Outputs: prefer registered (Moore) at module boundaries; combinational
  decode of r_state internally is fine but belongs in the K-maps
  ([[signal-contracts-and-kmaps]]).
- Every FSM's exit conditions are decision logic - map them. The stream
  scheduler's XFER/COMPLETE exits and the descriptor engine's chain
  decisions are the worked examples in stream_signal_contracts.xlsx.
- De-FSM precedent: pumice retired whole FSMs (bank timer, CAM control)
  into counters + qualifiers and got simpler, faster logic - ask whether
  the machine is needed before minimizing it.
