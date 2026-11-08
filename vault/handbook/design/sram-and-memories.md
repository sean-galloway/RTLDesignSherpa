---
title: SRAMs and memories
summary: No reset ports on SRAMs; ram_style attributes; [DEPTH] syntax.
---

# SRAMs and memories

- SRAM modules have NO reset port. Controllers own pointers and reset;
  memory contents are init-by-write. Shared primitives:
  `rtl/amba/gaxi/gaxi_fifo_sync.sv`, `rtl/amba/shared/sdpram_core.sv`
  (+ the sdpram_slave_* protocol wrappers). The old simple_sram.sv is gone.
- FPGA inference attributes on every memory array:
  `(* ram_style = "auto"|"distributed"|"block" *)` (Xilinx) with the
  comment variant beside it. Small FIFOs: distributed.
- Array syntax `[DEPTH]`, never `[0:DEPTH-1]`.
- FIFO depths: power of 2 ([[cdc]] for why async cares even more).
- A datapath buffer sized too shallow for concurrent read+write at wide data
  widths corrupts data *silently* - it is not a stall, it is a mismatch. STREAM
  case: a uniform 4 KB buffer meant `fifo_depth=64` at 512-bit, which produced
  data-mismatch errors (the read fill and write drain collided); the fix was to
  scale depth with width and hold a minimum safe depth (128 entries at 512-bit).
  Size buffers by `depth = target_bytes / (data_width/8)` but floor the depth,
  don't floor the byte size.

Authority: /GLOBAL_REQUIREMENTS.md sections 1.2-1.4.

## An accounting counter must never gate its own count (2026-09-27)

`sram_controller_unit` tracks "beats written minus beats reserved" with
`stream_drain_ctrl`, a virtual FIFO of depth `SD`. Being a FIFO, it has a
`wr_ready`, and its write count is gated on it. But the bound on the REAL
FIFO is set elsewhere -- `stream_alloc_ctrl` allows written minus DRAINED
to reach `SD`, and the latency bridge parks up to five beats outside the
FIFO -- so written minus RESERVED legitimately sits at `SD` while the FIFO
still accepts. The counter then drops a real write: the beat is in the
channel, never reservable, and the source path on rapids ended 4 beats
short of every long transfer (rapids BUG-003, stream BUG-011).

Two rules fall out of it. A counter that exists to OBSERVE a datapath
takes its headroom from the datapath's real bound (here `SD` plus the
bridge), never from its own nominal size; if it is modelled as a FIFO,
size that FIFO past every reachable occupancy and never let its full flag
touch the count. And "isolation passing is not integration passing"
applies at the boundary too: the unit suites (`test_sram_controller*`,
38/38 before and after) cannot reach the trigger, because it needs the
alloc/bridge interplay at exactly `SD` occupancy -- a consumer draining
slower than the fill. The rapids char harness, driving a 512-deep channel
with a 1024-beat transfer at a 50% drain, is what found it; the 84-beat
conservation cells that gated the SRAM swap could not.

## An unreset array inside a reset block still synthesizes as flops (2026-10-29)

`axi_perf_latency_hist` kept its timestamp FIFO as an array that was never
reset or cleared, but wrote it from inside the `ALWAYS_FF_RST` block whose
reset-or-clear branch initializes the pointers. Vivado does not infer
distributed or block RAM for an array written in a process that has an
asynchronous reset branch, whatever that branch does to the array: the
array became 32 x depth flops with a read mux. At depth 32 nobody noticed
(2k FFs); sizing it to the generators' admission domain (depth 128, pumice
ISSUE-025) cost +6.2k registers and +1.9k LUTs on the Nexys A7
characterization build before the write was moved into its own reset-free
`always_ff`, gated only by the push condition. The pumice BRAM CAM failed
the same way (the whole design used 0 BRAM until the async reset came off
the array). The rule: a memory array gets its own `always_ff @(posedge clk)`
with no reset and no clear term, the controller owns the pointers and their
reset, and an entry under a reset pointer is overwritten before it can be
read. Check the post-implementation "LUT as Memory" and register counts
when a FIFO depth changes; a register count that grows by width x depth is
this.

The mechanical check is the synth log, not the utilization table: Vivado
names every array it refused as RAM with `[Synth 8-4767] ... implemented in
registers` and the reason `RAM is sensitive to asynchronous reset signal`.
`grep -c 'Synth 8-4767' vivado.log` after `make synth` is the count; it was
35 on pumice and 30 on granite on the 10-27 builds (memory-controllers
ISSUE-001) and every one of those arrays was a tag written ONCE under a
dynamic slot index and never reset -- the reset branch beside it was for other
state. Moving the write statements into their own clock-only `always_ff`
(same condition, same index) is behaviour-identical in simulation, which is
why nothing but the synth log can tell you it was needed (memory-controllers
MC-005, 2026-11-06). A census helps: for every `[N]` array, list its write
sites and whether any is a reset-loop write; the single-site, no-reset ones
are the candidates.

## Several write addresses in one process also dissolve the array (2026-11-07)

The cache-ip shared tag array (`l1_tag_array`) had no reset anywhere near
it and still synthesized as 11,264 flops plus ~23k LUT of 128:1 read muxes
per core on the Genesys2 pair rigs -- 43 percent of the whole design, and
the LUTs landed in the *controller's* hierarchy, so the utilization table
blamed the wrong block. The cause was the write loop: one `always_ff`
walked `for (w...) if (wr_way_onehot[w]) mem[w*SETS + wr_set] <= ...`, so
Vivado saw WAYS distinct write addresses in one process and gave up on RAM
inference (no `Synth 8-4767` line this time; the array simply never appears
as a RAM). The per-way generate -- one `mem [SETS]` per way, written by
`if (wr_en && wr_way_onehot[w]) mem[wr_set] <= ...` -- synthesizes the same
contents to 184 LUT + 608 LUTRAM primitives and zero flops, with the same
ports and cycle behaviour. `l1_data_array` already used that idiom, which is
why it was LUTRAM and the tag array was not. The rule: one write address per
process per array; a way or bank select belongs on the generate index, never
in the address arithmetic. Out-of-context `synth_design` of the one module
(`-mode out_of_context`, count `REF_NAME =~ RAM*` vs `FD*`) is a two-minute
check and was the thing that found it.

The TB side: hierarchical peeks into a flat array (`u_tag.mem[way*SETS+set]`)
break when the array becomes per-way; cocotb reaches the generate scope as
`u_tag.g_way[way].mem[set]`. Three pair-rig TBs carried that peek.

## Policy state that must be deterministic after reset: init bitmap, not reset flops (2026-11-07)

`l1_repl`'s true-LRU rank array needs a known permutation after reset, which
is why it sat under the reset macro as 1,024 flops + ~400 LUT per core.
Reset-free RAM plus a per-set valid bit gives the same contract: the rank
word for a set is read from a SETS-deep distributed RAM when `rank_vld[set]`
is set and from the constant reset permutation when it is not; the first
access to a set writes the RAM and sets the bit. 128 flops + 24 LUTRAM
primitives, cycle-identical to the flop array (the unit TB and the pair-rig
victim-way parity scored both). The pattern generalizes to any per-entry
state with a reset value that is a function of the index: the RAM holds the
live state, the bitmap says which entries have been written, the reset value
is a constant the read mux substitutes.

## A cache data array belongs in block RAM: the read address leads by a cycle (2026-11-07)

Block RAM reads are synchronous, so a combinational-read array can never
map to it. The cache-ip `l1_data_array` (128 sets x 4 ways x 8 beats x
64 bits) was 16k LUTRAM + 8.7k F7/F8 muxes per core as a combinational
read; the same array with a registered read is 16 RAMB36 + ~140 LUT
(`ram_style = "auto"` picks block RAM once the read is registered; two
copies, one per read port). Behind a `SYNC_READ` parameter the module
keeps both contracts; the controller takes a matching `DATA_SYNC_READ`
and presents each address one cycle before the consumer needs the word:
the hit beat during the lookup cycle, gather beat k+1 during gather beat
k (beat 0 during the lookup cycle of a miss), the snoop line's beat 0 at
the grant and beat k+1 at the beat-k handshake. The way select stays
after the register, so the way may arrive with the data. Latency was
unchanged on every path; the pair-rig TB and the board agree cycle for
cycle with the combinational-read RTL.

The one hazard is read-before-write: a registered read of the address
written at the same edge returns the old word in RTL, and on the RAMB
only READ_FIRST on the write port guarantees even that. Do not rely on
`rw_addr_collision`; design so the colliding word is never consumed. Here
the only consumer was the pending-fill snoop bypass, which streams a beat
the cycle it lands: it now gates on a one-cycle-delayed beat-valid, so the
beat is re-read clean before it streams. Amber Genesys2 pair rig after
items 1, 2, 4, 6: 98,033 -> 17,615 LUT, 47,455 -> 20,721 FF, 128 -> 160
RAMB36 (the 128 are the harness memory), WNS +0.014 -> +0.407 ns.

### The shared-port variant: fire only when the address last cycle was yours (jet, 2026-11-07)

Amber's data ports each had one consumer per state, so the address lead
was a per-state rewrite. Jet shares each port between two independent
engines (port A: hit-serve read vs. the commit's read-slot capture; port
B: the snoop CD stream vs. the dirty-victim capture), and either can take
the port in any cycle. The registered word on a port is "whatever address
was presented last cycle", so each consumer carries a one-flop qualifier
saying that address was its own, and fires only on it:

- the serve read fires on `r_pa_srv_d1` (port A carried the serve record's
  address last cycle AND the record did not reload); one extra cycle of
  read-hit latency (class pulse to deposit 1 -> 2 cycles), nothing else
  moves because `jet_rsp_seq` deposits are tag-indexed;
- the commit's read slot lands through `r_cmt_rd_d1`/`r_cmt_rd_k_d1`, one
  cycle after its address, while the cursor has already advanced -- the
  last slot lands during C_INSTALL, before C_DEPOSIT reads it;
- the snoop takes port B's address in its GRANT cycle for beat 0 and
  presents beat+1 on each `cdready`; a stalled beat re-presents itself;
- the capture presents a beat and strobes the WB buffer one cycle later
  (`r_cap_d1`); `w_cap_active = busy | word in flight` replaces every
  reader of the busy flag (WB-full stall, drain race, snoop-safe, fill
  accept) so the in-flight word is never raced.

The way select is applied in the DATA cycle (per-way registers, mux after),
so the way mux must follow the owner of the word, not the owner of the
address: `dat_a_way_o` holds the commit way while `r_cmt_rd_d1`,
`dat_b_way_o` holds the capture way while `r_cap_d1`. Jet func was 60/60
on the first run; see [[decision-stage-reads-the-snapshot]] for the
tag-side rule that made the same pipeline honest.

## A line-wide read interface forces a flop array: read payload by beat (2026-11-07)

Two payload stores survived the first FPGA pass as flops because their READ
interfaces were drawn as whole lines: jet's WB buffer (`drain_data_o` and
`sn_data_o`, 512 bits each, on 2 x 512 bits of beat-written storage) and
amber's gathered victim line in l1_control (`victim_line_q`, 512 bits, read
whole by l1_drain and by the snoop CD bypass). Written one beat at a time and
read as a line in one cycle, neither can be a RAM, so Vivado builds the
storage as flops plus a line-wide read mux -- about 1,500 flops of line
payload across the jet buffer and its snoop snapshot. The async clear on
those flops was then the reset synchronizer's worst recovery path.

Every consumer was already beat-serial: l1_drain emits one W beat per cycle,
the snoop CD stream emits one beat per cycle. The whole-line reads existed
only because the interface was a line. The owner's question that caught it:
"why isn't the WB buffer a RAM?"

**Rule:** a payload store's read port has the width of the consumer's beat,
and the consumer presents the beat address. `l1_drain` now exports
`victim_beat_idx` and takes `victim_beat_data`; l1_control's victim line is
`victim_line_mem[FILL_BEATS]` (one distributed RAM, read by the drain and by
the bypass at `sn_beat_q`); `jet_wb_buffer.r_data` is
`[VICTIM_DEPTH*FILL_BEATS]` words with a drain beat port and a snarf stream
port. `l1_victim` keeps address and valid only.

**The corner a snapshot was hiding.** jet_control copied the snarfed WB line
into a 512-bit register at the snoop grant because the WB entry may retire on
its BRESP mid-stream. Streaming from the store instead needs the slot's words
to survive that retire: `wb_sn_lock_o` (the stream is in SN_DATA from the WB
source) with the latched slot makes a retired-but-locked tail slot not free,
so no capture reuses it until the last beat has been read. The lock costs a
dirty alloc at most one stream of wait; the snapshot cost 512 flops always.

Harness consequence: nothing exports a whole line any more. A TB that wants
the line either sweeps the beat index on a combinational read port it owns
(set index, settle 1 ps, sample; `jet_wb_buffer_tb._drain_line`) or peeks the
store's words directly (`l1_control_tb._victim_line` reads
`u_control.victim_line_mem[b]`) -- the latter is the only option in a harness
whose drain owns the beat-index port (amber_eviction_macro_test: a TB sweep
there fought the drain and read the drain's beat, not the line).
