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

# Trackers

Passive monitors for the ddr2-lpddr2 controller's internal FUBs.

Every tracker:
- Attaches as a `cocotb.start_soon(tracker.run())` background task.
- Snoops the FUB's external outputs every clock cycle.
- Emits typed `TrackerEvent` records into a single `.events` deque.
- Renders each event as **one row of a fixed markdown table** via
  `to_md_row()`. Concatenating events from many trackers yields one
  unified table that's grep-able across the whole simulation.

## Unified output format

```
| time(ns)  | cycle  | tracker  | event          | rank | bank | slot  | data |
| ---       | ---    | ---      | ---            | ---  | ---  | ---   | ---- |
|    1234.5 |     42 | sched    | CMD_ACT        | r0   | b3   | -     | row=0x100 col=0x40 len=8 |
|    1245.5 |     43 | xbank    | STATE_ACTIVATING| r0  | b3   | -     | prev=IDLE |
|    1255.5 |     44 | dficmd   | WIRE_ACT       | -    | -    | -     | bank=3 addr=0x100 cs_n=0 |
|    1290.0 |     47 | wrbeat   | DRIVE_CYC      | -    | -    | -     |  |
|    1300.0 |     48 | refr     | REQ_EDGE       | -    | -    | -     | pending=1 |
```

Dump all events from all trackers into one file:

```python
from tbclasses.trackers import (
    SchedulerTracker, RefreshTracker, XBankTimersTracker,
    PagePredictorTracker, DfiCmdFormatterTracker,
    WrBeatSequencerTracker, RdClAlignerTracker,
    dump_md_unified,
)
sched = SchedulerTracker(dut); cocotb.start_soon(sched.run())
xb    = XBankTimersTracker(dut, num_ranks=1, num_banks=8); cocotb.start_soon(xb.run())
# ... attach as many as you want
dump_md_unified([sched, xb, ...], 'trace.md')
```

## Trackers

| Tracker | FUB | Snoops | Key events | Key stats |
|---|---|---|---|---|
| `SchedulerTracker` | `scheduler.sv` | `cmd_*`, `evt_*`, grants, `*_issued_*` | `CMD_<op>`, `EVT_ACT/RD/WR/RDA/WRA/PRE`, `GRANT_REF/PDN/MR`, `ISSUED_WR/RD` | `op_counts`, `per_bank_act_counts`, `col_ops_with_ap` vs `_open_page` |
| `RefreshTracker` | `refresh_ctrl.sv` | `refresh_req_o`, `pending_refreshes_o`, `refresh_grant_o`, `t_refi_i` | `REQ_EDGE`, `GRANT`, `PENDING_<n>` | `jedec_postpone_violation`, `avg_refresh_interval`, `request_to_grant_latency` |
| `XBankTimersTracker` | `xbank_timers.sv` | `bank_state_o`, `bank_open_row_o`, `bank_row_active_o` | `STATE_<NEW>`, `ROW_OPEN`, `ROW_ACTIVE_SET/CLR` | `per_bank_state_cycle_counts`, `auto_pre_inferred` |
| `PagePredictorTracker` | `page_predictor.sv` | `evt_act_i`, `predict_open_o` | `ACT_SEEN`, `PREDICT_OPEN`, `PREDICT_CLOSE` | `act_count_per_bank`, `time_in_predict_open` |
| `DfiCmdFormatterTracker` | `dfi_cmd_formatter.sv` | `dfi_cs_n_o`, `dfi_ras/cas/we_n_o`, `dfi_address_o`, `dfi_bank_o`, `dfi_cke_o`, `dfi_odt_o` | `WIRE_<op>` (with A10 RDA/WRA/PREA), `CKE_<val>`, `ODT_<val>` | `wire_cmd_counts`, `unknown_encodings` (compliance check) |
| `PowerdownTracker` | `powerdown_ctrl.sv` | `pdn_req_o`, `dfi_cke_o` | `PDN_REQ_<n>`, `CKE_DROP`, `CKE_RISE` | `pdn_req_count`, per-rank `cke_residency` |
| `InitSequencerTracker` | `init_sequencer.sv` | `init_busy_o`, `dfi_init_start_o`, `mr_seq_*`, `zqcl_req_o` | `INIT_DONE`, `DFI_INIT_START`, `MR_WRITE`, `ZQCL_REQ` | `init_duration_cycles`, `mr_write_log` |
| `WrBeatSequencerTracker` | `wr_beat_sequencer.sv` | `op_valid/ready`, `beat_pull_strb`, `dfi_wrdata_en`, `b_complete_strb` | `OP_ACCEPT`, `PULL_BEAT`, `DRIVE_CYC`, `B_COMPLETE` | `pull_drive_overlap_ratio` (proves multi-outstanding) |
| `RdClAlignerTracker` | `rd_cl_aligner.sv` | `op_valid/ready`, `dfi_rddata_en`, `dfi_rddata_valid`, `rd_inject_*`, `rd_beat_we_o` | `OP_ACCEPT`, `EN_CYC`, `CAPTURE_CYC`, `EMIT_BEAT`, `EMIT_LAST`, `BEAT_WE` | `en_capture_overlap_ratio`, `capture_emit_overlap_ratio` |

## Grep examples

```bash
# All events from one tracker
grep '| sched    |' trace.md

# All commands of one type, from any tracker
grep '| CMD_ACT  '  trace.md   # scheduler-issued
grep '| WIRE_ACT '  trace.md   # decoded from DFI wires
grep '| EVT_ACT  '  trace.md   # event sent to xbank_timers

# Everything touching rank 0 bank 3
grep '| r0   | b3 ' trace.md

# All page-predictor open transitions
grep '| pgpred   | PREDICT_OPEN'  trace.md

# All multi-outstanding overlap proof
grep '| wrbeat   ' trace.md | grep -E 'PULL_BEAT|DRIVE_CYC'
```

## Usage

### Quick: attach all 9 trackers at once

```python
from tbclasses.trackers import wire_trackers

# In your TB setup, after start_clock + reset:
trackers = wire_trackers(dut, num_ranks=1, num_banks=8)
# That's it — all 9 trackers are running. Each will auto-write its file
# at end of sim:
#   <sim_build_dir>/sched.out
#   <sim_build_dir>/refr.out
#   <sim_build_dir>/xbank.out
#   <sim_build_dir>/pgpred.out
#   <sim_build_dir>/dficmd.out
#   <sim_build_dir>/pdn.out
#   <sim_build_dir>/init.out
#   <sim_build_dir>/wrbeat.out
#   <sim_build_dir>/rdalign.out

# Mid-test, query in-memory stats:
print(trackers['sched'].stats())
assert not trackers['refr'].jedec_postpone_violation()
```

### Manual: one tracker, custom path

```python
from tbclasses.trackers import SchedulerTracker
import cocotb

# output_dir defaults to cwd (= sim_build dir under cocotb_test)
sched = SchedulerTracker(dut)               # → sched.out in cwd
sched = SchedulerTracker(dut, output_dir='/tmp')  # → /tmp/sched.out
sched = SchedulerTracker(dut, filename='/tmp/custom.out')  # explicit path

cocotb.start_soon(sched.run())
```

### Unified file (all trackers' events merged + sorted by cycle)

```python
from tbclasses.trackers import dump_md_unified

# Sometime during or after the test:
dump_md_unified(list(trackers.values()), 'trace_unified.out')
```

## Output files

Every tracker auto-registers an `atexit` handler that writes its events
to `<output_dir>/<short>.out` at the end of the simulation subprocess.

| Default filename | Tracker |
|---|---|
| `sched.out`   | `SchedulerTracker` |
| `refr.out`    | `RefreshTracker` |
| `xbank.out`   | `XBankTimersTracker` |
| `pgpred.out`  | `PagePredictorTracker` |
| `dficmd.out`  | `DfiCmdFormatterTracker` |
| `pdn.out`     | `PowerdownTracker` |
| `init.out`    | `InitSequencerTracker` |
| `wrbeat.out`  | `WrBeatSequencerTracker` |
| `rdalign.out` | `RdClAlignerTracker` |

The default `output_dir` is `os.getcwd()`. Under cocotb_test, the
simulation runs from the per-test `sim_build/<test_name>/` directory,
so the files land there alongside the other simulation artifacts.

## Design conventions

- Sample on `RisingEdge(dut.mc_clk)` + `Timer(1, 'ps')` NBA settle.
- Tolerate missing signals via `is_high` / `safe_int` helpers (so a
  tracker doesn't crash a TB that exposes only a subset of ports).
- Events are dataclasses with `sim_time_ns` and `cycle` for waveform
  cross-reference.
- Statistics computed lazily on `.stats()` — keeps the hot path cheap.
- Tracker short names (`sched`, `refr`, `xbank`, `pgpred`, `dficmd`,
  `pdn`, `init`, `wrbeat`, `rdalign`) are fixed and grep-friendly.
