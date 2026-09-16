<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# cdc — Open (accepted, ready to start)

## CDC-002: cdc_4_phase_handshake FAST_PATH acknowledges a transfer the receiver never took

**Priority:** P2 — a real data-loss defect in a shared CDC primitive. Latent in
the only in-tree user, which ties `dst_ready` high, so nothing shipped is
currently wrong.
**Status:** open 2026-09-16. Found by formal the first time the fast path was
ever exercised, under [[CDC-FORMAL-STALE]].

**The defect.** With `FAST_PATH=1`, `D_IDLE` samples `dst_ready` and, on the
synchronized request, sets `dst_valid <= 1` **and** `r_ack_dst <= 1` together,
jumping to `D_WAIT_REQ_CLR`:

```systemverilog
if (FAST_PATH && dst_ready) begin
    dst_valid   <= 1'b1;
    r_ack_dst   <= 1'b1;      // acked before the handshake is observed
    r_dst_state <= D_WAIT_REQ_CLR;
end
```

`dst_ready` was sampled in the PREVIOUS cycle. If it falls before `dst_valid`
rises, `dst_valid && dst_ready` never holds -- the receiver never takes the
beat -- but the ack has already gone back, the source completes, and the data
is silently dropped. `D_WAIT_REQ_CLR` then drives `dst_valid` low, so the beat
is never re-offered.

**Counterexample** (`prove_fast`, step 22): the destination sits in
`D_WAIT_REQ_CLR` with `r_ack_dst=1` while the harness ghost `f_dst_completes`
is still 0, then the source returns ready and accepts a SECOND transfer with
the first never delivered -- `ap_no_lost_transfer` fires.

**It is a defect, not a missing assumption.** `docs/markdown/rtl-cdc/cdc.md`
states a data-stability guarantee for the crossing but places no stability
requirement on `dst_ready`, and ordinary valid/ready lets a receiver drop
ready. The slow path is correct: `D_WAIT_READY` acks only on observing
`dst_ready`.

**Blast radius: nothing shipped is broken.** The only in-tree instantiations
with `FAST_PATH=1` are the two in
`projects/fpga-systems/NexysA7/cdc_counter_display/build-demo/rtl/cdc_counter_domain.sv`
(lines ~482 and ~511), and both drive `.dst_ready (1'b1)`. A constant-high
ready cannot fall, so the window never opens there.

**Two fix shapes, and they are not equivalent:**
1. Make `dst_valid` combinational on the fast branch so the handshake
   completes in the same cycle `dst_ready` is observed. Keeps the one-cycle
   saving, which is the whole point of the parameter, but adds a
   combinational path out of the synchronizer in the destination domain.
2. Ack only on an observed `dst_valid && dst_ready` (i.e. fall back to the
   `D_WAIT_READY` behaviour). Trivially correct, but then `FAST_PATH` saves
   nothing and the parameter should be deleted rather than left as a knob
   that does nothing.

Choosing between them is a design call, which is why this is filed rather
than fixed.

**`formal/cdc/cdc_4_phase_handshake` task `prove_fast` is left RED on
purpose**, so the finding cannot quietly disappear. `prove`, `cover`,
`prove_timeout`, `cover_timeout` and `cover_fast` all pass.

**Test gap worth noting:** `val/cdc/test_cdc_4_phase_handshake.py` sweeps only
clock-period combinations. It sets neither `FAST_PATH` nor `TIMEOUT_CYCLES`,
so no directed test covers either path. That belongs to [[CDC-001]].

---

## CDC-003: fifo_async wavedrom scenarios hand-drive dut.read against a live BFM

**Priority:** P3. A TB defect, not an RTL one. Found by the CDC-001 testqc
round (part_03), raised SUSPECTED and confirmed by reading the framework.
**Status:** open 2026-09-16.

`FifoAsyncWaveDromTB` (in `val/cdc/test_fifo_async_wavedrom.py`) writes through
the BFM -- `await self.write_master.send(packet)` -- but reads by poking the
pin directly, at three sites:

```python
self.dut.read.value = 1
await RisingEdge(self.rd_clk)
self.dut.read.value = 0
```

Its base `FifoBufferTB` constructs `self.read_slave = FIFOSlave(...)`, and
`FIFOSlave` extends `FIFOMonitorBase(FIFOComponentBase, BusMonitor)` -- cocotb's
`BusMonitor.__init__` auto-starts `_monitor_recv`. `FIFOSlave` drives the same
pin through `_set_rd_ready()` at five sites (line 191 drives it HIGH during the
receive phase). So two drivers contend for `dut.read`.

This also breaks the repo's standing rule: drive through the BFMs, never
hand-poke a valid/ready interface.

**Why it is filed rather than fixed:** the scenarios exist to emit specific
wavedrom diagrams, and the committed JSON is a deliverable. Moving reads onto
the BFM changes capture timing and therefore the diagrams, which needs a look
at the rendered output rather than a green test.

