<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# stream-g Verification

**Status:** Implemented (stream TASK-020)
**Last Updated:** 2026-10-24

---

## Suites

| Suite | Directory | What it proves |
|---|---|---|
| Edge table | `dv/tests/fub_g/test_scheduler_g_edges.py` | every command in every state, the flags, the firmware packets, on STREAM's `scheduler_g` (the rapids-g bench with STREAM's port set) |
| Equivalence | `dv/tests/fub_g/test_stream_g_equiv.py`, bench `dv/tb/stream_g_equiv_tb_top.sv` | NUM_CHANNELS state-machine schedulers beside NUM_CHANNELS `scheduler_g` on one `rapids_seq_g`, the same descriptors, each side's own engine models: every read and write command, every MonBus packet and the final state must match, and an independent golden model checks the EXT run bases (rapids-g's bench, with beats, aligned addresses, no packet records) |
| macro_g | `dv/tests/macro_g/` | the product `stream_core` suites re-hosted on `stream_core_g` by the directory's conftest (the mailbox answered by a guard that fails the test if the firmware ever uses it) |
| top_g | `dv/tests/top_g/` | the product `stream_top` suites re-hosted on `stream_g_top_ch8` / `_ch16` |

: Table 7.4.1: stream-g suites

The equivalence cases are rapids-g's less the packet-record ones, plus two with STREAM's read-ahead
prefetch on: `linear_pf` and `reset_any_pf`. With the prefetch on, whether a chained head advances in
place or walks COMPLETE / NEXT_DESC depends on when the firmware staged it, so those cases compare the
commands and the completion packets but not DESC_START packets or the state sequence. Configurations:
4, 8 and 16 channels at one slot per hart, 8 channels on 4 harts and 16 on 8 and 4.

Two things the bench taught:

- The bench's write-engine model must not outrun its read model. In hardware the write engine cannot
  issue beats the reads have not landed in the SRAM; with independent models the write side could finish
  descriptor N while N's reads were still out, and the prefetch's in-place advance then reloaded the read
  flops -- a model artifact, now coupled as the SRAM couples them.
- STREAM's scheduler sent a last descriptor's DESC_COMPLETE / IRQ packet once per cycle of its commit
  wait (stream BUG-022, rapids BUG-016's twin): the two sides dwell in COMPLETE for different numbers of
  cycles and their packet streams diverged on channels whose commands matched exactly. Packets go once
  per state visit now.
- With the prefetch on, one full-level `linear_pf` seed stalled a gatling channel: its reads finished
  on the cycle the write side advanced in place onto a staged head, `scheduler_g`'s armed
  auto-completion took COMPLETE, and the new head sat loaded with nothing issuing it. The advance
  wins now, as it does in the state machine (Chapter 7.2).

## Results (2026-10-24)

From `make clean-all`, no reruns: the split scheduler is bit-exact with the one-module one (same seed,
identical simulation logs on all 141 scheduler and stream_core cells); fub_g 64 cells at gate and 192 at
full, all passing; macro_g 159 passed, 12 skipped (1- and 2-channel and
per-channel-engine cells, which stream-g does not build); top_g 67 passed, 2 skipped (1-channel); the
product fub 510, macro 684 (+5 by design) and top suites unchanged.

## The Genesys 2 (2026-10-24)

Both bitstreams come from the same tree and the same flow (`build-perf`, 8 channels, 100 MHz, Kintex-7
325T); the STREAM one is the control for the stream-g one, built minutes apart.

| | STREAM (`stream_top_ch8`) | stream-g (`stream_g_top_ch8`, ROM firmware) |
|---|---|---|
| Slice LUTs | 66,221 | 65,472 |
| Slice registers | 59,652 | 58,265 |
| LUT as memory | 6,390 | 6,742 |
| Block RAM tiles | 26 | 29 |
| DSP48 | 64 | 0 |
| Setup WNS / hold WHS (ns) | +0.790 / +0.032 | +0.668 / +0.050 |

: Table 7.4.2: the two Genesys 2 builds

The 64 DSPs were the FSM scheduler's EXT run-base generators (a multiplier pair per channel per direction,
`stream_run_addr_gen`); stream-g computes the bases in firmware and the gatling's own datapath is LUTs. The
three extra block RAMs are the firmware ROM and the harts' scratch. The gatling costs less area than the
eight state machines and generators it replaces, in this configuration.

The first stream-g bitstream answered nothing on the UART, not even the harness's own registers, while the
control answered on the same port; the Vivado log named the cause (`Net host_cmd_valid ... does not have
driver`): the generated top connected the APB slave to the `host_*` nets before the include that declares
them, and Vivado made implicit undriven nets where Verilator had resolved the names (Chapter 7.3). The
generator anchors the include before the instances now, and every bitstream build scans its log for that
line.

### Throughput

`host_characterize.py`'s 40-config matrix (1, 2, 4, 8 and 16 descriptors per channel, 1 to 8 channels), run at
three descriptor sizes on each bitstream, 240 runs, all passing; cycles are the harness timer from kick to the
last channel's done. The STREAM bitstream's 1 MB matrix is cycle-identical to the 2026-10-03 measurement
(`results/perf_sweep_2026-10-03.csv`), so the harness bridge regenerated for these builds changed nothing.

| descriptor size | 1 desc, 1 ch | 1 desc, 8 ch | 16 desc, 1 ch | 16 desc, 8 ch | mean over 40 |
|---|---|---|---|---|---|
| 1 MB | 65,583 / 65,730 (+0.22 %) | 524,335 / 524,476 (+0.03 %) | 1,048,623 / 1,048,771 (+0.01 %) | 8,388,655 / 8,388,688 (+0.00 %) | +0.02 % |
| 64 KB | 4,143 / 4,299 (+3.8 %) | 32,815 / 32,963 (+0.45 %) | 65,583 / 65,723 (+0.21 %) | 524,335 / 524,371 (+0.01 %) | +0.41 % |
| 4 KB | 303 / 444 (+46.5 %) | 2,095 / 2,231 (+6.5 %) | 4,143 / 4,170 (+0.65 %) | 32,815 / 32,844 (+0.09 %) | +4.96 % |

: Table 7.4.3: cycles, STREAM / stream-g (stream-g relative to STREAM), Genesys 2, 100 MHz, 128-bit data

The difference is a fixed latency, not a rate: about 140 to 150 cycles once per channel, between the kick and
the first read (the firmware's poll, STAGE_ARM and the state walk, against the state machine's four cycles),
and a cycle or two per chained descriptor after that. At 1 MB both move 1,525 MB/s against the 1,600 MB/s
peak; at 4 KB the state machine's 303 cycles become 444. A channel is within 10 % of STREAM once its first
descriptor carries about 24 KB (1,500 beats), within 5 % at about 47 KB, within 1 % at about 235 KB; a chain
amortizes the same latency over all its descriptors, so the 16-descriptor columns reach those bounds at a
sixteenth of the size. The figures are the rapids-g simulation sweep's shape (rapids HAS Table 6.4.9) measured
on silicon. Artifacts: `build-perf/results/perf_sweep_2026-10-24_{fsm,g}_{1MB,64KB,4KB}.{csv,json}`.
