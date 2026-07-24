---
title: Streaming datapaths - no FSM
summary: Skid-buffered pipelines with backpressure, not state machines.
---

# Streaming, not FSMs

Datapath blocks (engines, movers) are valid/ready pipelines:
`s_ready = !r_valid || m_ready`, register the beat, propagate backpressure.
FSMs are for control paths (descriptor lifecycle, schedulers) - never in the
per-beat data path, where they cost throughput and breed corner cases.
Skid buffers (`gaxi_skid_buffer`) decouple timing at block boundaries; when
a block gates a handshake (e.g. a monitor's block_ready), the observation
point and the gate must be on the SAME side of the skid or the loop doesn't
close ([[sizing-invariants]] tells the rest of that story).
Reference implementations: stream axi_read_engine / axi_write_engine.
