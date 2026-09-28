# TASK-033: monitor side done (measured 2026-08-30); board-code residue noted

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **OBS-PORTS** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Status:** CLOSED 2026-09-15 — the telemetry ports are GONE and the regblock owns them. Landed
in f1847268, "feat(observers): both roles in the harness, telemetry behind the
regblock". Was: open 2026-08-16.

**Measured against the tree, because the description below is now false:**

* `axi4_intf_slave_observer` declares 33 outputs -- EXACTLY the "real
  interface" count this task asked to be left (APB slave response, AXIL slave
  read, dump master, irq). Zero outputs match meter/hist/perf/fifo/compress.
  (106 total ports, but 73 of those are inputs; do not read the total as the
  problem -- an earlier summary did and it made the task look untouched.)
* `obs_regs.rdl` carries the status fields: HIST_DATA, HIST_METRIC,
  HIST_SAMPLE_LOST, COMPRESS_EN, compression/Compressor and FIFO fields.
* `projects/fpga-systems/Genesys2/stream/bin/obs_addrs.py` exists, so the host
  reads them by name ([[feedback_registers_by_name]]).

**The one bullet still open is NOT monitor code.** "Repoint the readers" is
partly undone: `Genesys2/stream/rtl/harness_csr.sv` still carries its "RFC
Stage E external axi4_intf_master_observer perf readback" mirror (around lines
279-284 and 688), so the host can still read perf from the harness CSR space
rather than the observer's own APB window. That is board/harness code, tracked
here only so the trail is not lost -- it does not belong to the monitors.

`axi4_intf_{master,slave}_observer` each declare 60 outputs, and only 33 are a
real interface (APB slave response, AXIL slave read, the dump master, irq).
The rest -- bus meters, latency histograms, perf counters, FIFO counts,
compressor stats -- are TELEMETRY fanned out as top-level ports. Wiring the
slave observer into `stream_harness` required tying off **70 pins** on that one
instance, and every one of them is a Verilator PINMISSING error if forgotten.

**This contradicts the block's own design note.** Its header argues it "owns
its configuration rather than taking 29 cfg_* ports that the harness tied off",
and that owning the APB window is "what lets ONE harness source serve both
builds". Config was internalized; STATUS never was, so the harness still has to
know the block's internals to read anything out of it.

**Wanted:** telemetry readable through the observer's OWN regblock (`obs_regs`,
already instantiated behind `s_apb_*`), not through ports.

- Add status fields to `obs_regs.rdl` for the meter buckets, histogram
  bins/totals, perf counters, FIFO counts and compressor stats.
- Regenerate via `bin/peakrdl_generate.py` ONLY -- the wrapper emits RTL, docs
  and regmap in lockstep; raw `peakrdl regblock` desyncs the regmap
  ([[feedback_peakrdl_generate_bin]]).
- Wire the internal nets to the regblock and DELETE the telemetry ports.
- Repoint the readers: `harness_csr.sv` currently mirrors the observer's perf
  outputs into its own CSR space (the "RFC Stage E external observer perf
  readback" path), and the host reads them there. With the regblock owning
  them, the host reads the observer's APB window directly, by name via
  `obs_addrs.py` ([[feedback_registers_by_name]]).

**Why it matters beyond tidiness:** 70 tie-offs per instance is 70 chances to
forget one, and a forgotten OUTPUT is silent -- it reads as PINMISSING only
because Verilator escalates it. The `_cg` wrappers shipped for months with an
unconnected `debug_block_ready` for exactly this reason, hidden behind
`-Wno-PINMISSING`.

**Do this BEFORE the 8-channel build.** Two observers x 70 ports is also
routing and area on a 325T that is already the reason build-mon is 4 channels.

<!-- Moved back from closed.md 2026-09-14: each of these says 'open' or 'NOT fixed' in its own body. They were filed to closed.md by mistake; see AUDIT-002 for why auto-flipping the status line instead would have been the wrong fix. -->


**CLOSED 2026-09-15 — the monitor-side goal is met; the one residue is board
code and does not belong to amba.** Verified rather than taken on trust:

* `obs_regs.rdl` carries the telemetry (14 HIST_/PERF/METER/FIFO/COMPRESS
  fields), and the generated regblock plus `obs_regs_top_regmap.py` exist, so
  the host reads telemetry BY NAME through the observer's own APB window --
  which is exactly what this task asked for.
* both observers declare 33 outputs, the "real interface" count this entry
  set as the target (APB slave response, AXIL slave read, dump master, irq).
* both are instantiated in `Genesys2/stream/rtl/stream_harness.sv`.

**Correction on scope, recorded because the claim is easy to repeat:** the
observer is functional in STREAM only. In pumice it is NOT instantiated --
`NexysA7/pumice/build-perf/rtl/ddr2_char_harness.sv:263` reserves APB slave 4
at 0x00090000 for `obs_regs` and marks the slot "EXPANSION SLOT, currently
UNUSED", terminated so the bridge answers zero instead of wedging the board on
an access. That is groundwork so adoption is "an instantiation, not a bridge
regen on the DDR2 critical path". Adoption was [[PUMICE-016]], DROPPED
2026-09-23: the slot stays reserved and usable, but pumice measured the
observer at +4223 LUTs (+208%) over the two shared primitives it already
instantiates directly, for no additional measurement. The groundwork is not
wasted -- it makes adoption a decision rather than a project -- it simply was
not taken up.

**What is left, and why it is not an amba task:**
`Genesys2/stream/rtl/harness_csr.sv` still mirrors the observer's perf outputs
into its own CSR space (the "RFC Stage E" readback path). That is board/harness
code -- this entry says so itself -- and with the regblock owning the telemetry
it is now a legacy convenience rather than the design gap the task described.
Recorded here so the trail survives; it needs a Genesys2 harness cleanup, not a
monitor change.

---
