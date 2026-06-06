# Monbus Compression — Handoff to FPGA Characterization Work

**Status:** Pre-RTL modeling complete; FPGA-side capture work pending.
**Last updated:** 2026-06-06
**Audience:** Engineer/agent driving the stream_char FPGA captures + parameter tuning.

---

## Context

We are designing a hardware compressor for the monbus bulk-trace path
(`m_axil_mon` in `monbus_axil_group`) to reduce AXI traffic when many
monitor agents fire simultaneously. The compressor sits between the
group's `err_fifo` output and the AXIL master writer; it leaves the
err-fifo IRQ path (`s_mon_axil`) untouched so real-time alerts stay
zero-latency.

The plan is **trace-driven**: build a Python encoder model first, validate
on real packet streams, tune parameters, then commit to RTL. This file
hands off the FPGA-side capture work (steps 2 and 3 below) to the
characterization expert.

---

## What's already built (on `origin/main`)

### Commit `4e00aafb` — Format scaffolding

`rtl/amba/shared/monbus_axil_group.sv` now emits records in a new
3-beat order, with the timestamp beat first and the top 4 bits of that
beat reserved as an encoding tag:

```
beat 0 = {tag[3:0], source_ts[59:0]}
         tag = 4'h0  → raw, no compression  (only value emitted today)
         tag = 4'h1..3 → reserved for future Tier-1 compression formats
         tag = 4'h4..F → reserved
beat 1 = packet[127:64]
beat 2 = packet[63:0]
```

The `m_axil_mon` master writer hardwires `tag = 4'h0` today, so on the
wire today is "the same data, in slightly different beat order, with
zero on top of the timestamp." Software/decoder needs to read the new
order; the Python parser already does.

The `s_axil` slice-counter drain mirrors this layout so the IRQ-driven
CPU read path sees the same record format.

### Commit `61878021` — Python encoder + decoder + reporter

`bin/TBClasses/monbus/monbus_compressor.py` implements the proposed
compression format: 16-entry LRU CAM keyed on
`(packet_type, protocol, event_code, channel_id, agent_id, unit_id)`,
with three Tier-1 sub-formats (formats A/B/C trading off `delta_ts`
width vs. `event_data` width vs. signed-delta encoding) plus a Tier-0
raw escape. Encoder and decoder are bit-exact mirrors of each other —
the decoder reconstructs CAM state from the slot stream alone, no
out-of-band info.

`format_report(encoder)` produces a human-readable summary:

```
Records:           2000
Tier 1 hits:       1700 (85.0%)
  - format A:      1421 (71.1%)
  - format B:       205 (10.3%)
  - format C:        74 ( 3.7%)
Tier 0 (raw):       300 (15.0%)
Escape reasons (Tier 0):
  cam_miss                  280 (93%)
  event_data_overflow        20 ( 7%)
CAM final state (16/16 entries used):
  [ 0]  pkt_type=0x1 protocol=0x0 event=0x01 agent=0x0010 chan=0 unit=0x01  hits=412
  ...
Compression ratio: 2.6x
```

24 unit tests in `bin/TBClasses/monbus/tests/test_monbus_compressor.py`.

### Commit `b6a42455` — Sim-side sniffer + capture hook

`bin/TBClasses/monbus/sniffer.py` provides a passive `MonbusSniffer`
class that taps a cocotb DUT's monbus interface signals
(`valid`, `ready`, `packet`, `timestamp`, `clk`) and dumps every
accepted record to JSON or CSV. The file format is autodetected by
extension. A `load_capture()` helper round-trips the file back into
the list of `(packet_int, timestamp_int)` tuples the encoder expects.

The sniffer is wired into `MonbusAxilGroupTB` behind a `MONBUS_CAPTURE`
env var — default behavior unchanged when the var is unset, but with
it set the test dumps a capture file at end-of-test:

```bash
cd projects/components/stream/dv/tests/macro
MONBUS_CAPTURE=/tmp/sim_capture.json pytest test_monbus_axil_group.py -v
```

That's the **only** sim source wired so far. Adding the same hook to
other monbus-using tests (the rapids equivalents, the bridge monitor
tests) is a 3-line addition per TB; the brief is in
`bin/TBClasses/monbus/sniffer.py`'s module docstring.

---

## What's needed from the FPGA characterization work

### Step 2: Per-source-isolation captures on Nexys A7

Goal: produce capture files from real silicon that the Python encoder
model can analyse, with per-source tagging so we can compute working-set
size per monitor instance.

**Hardware setup:** stream_char as-is on the Nexys A7 (the bitstream
already captures `m_axil_mon` writes into `debug_sram`; the host script
already dumps it). The compressor RTL is **not** in the build — the
captures are uncompressed records exactly as they hit the AXIL bus.

**Per-source isolation methodology:** for each capture run, enable only
**one** of the per-port monitor wrappers and disable the rest. This gives
clean per-source statistics about template tuple cardinality and
distribution. Then a final "all-enabled" run gives the aggregate.

The per-wrapper enable plumbing exists today via the bridge-generator-emitted
`USE_MONITOR` SV parameter on each wrapper instance — but it's a build-time
parameter, not runtime. So per-source isolation likely requires rebuilding
the bitstream with different parameter settings per run, **or** adding a
runtime enable in the harness CSRs (which would be a small TODO item
before captures start).

**Suggested run matrix:**

| Run | Monitors enabled | Workload | Purpose |
|-----|------------------|----------|---------|
| 1 | descriptor-fetch only | Standard DMA exerciser | Per-source CAM cardinality, fetch path |
| 2 | read-engine only     | Standard DMA exerciser | Read path, address patterns |
| 3 | write-engine only    | Standard DMA exerciser | Write path |
| 4 | all monitors enabled | Standard DMA exerciser | Aggregate working set |
| 5 | all monitors enabled | Idle/stall heavy workload | Long-delta-ts validation |
| 6 | all monitors enabled | Error injection workload | Error packet distribution |

For each run: capture as many records as `debug_sram` holds, then
dump via the existing host path. **Multiple iterations of the same
config are valuable** — let the system run for N minutes per run if
the SRAM is small, so the aggregate working set converges.

**Capture file contract:** the Python model accepts `.json` or `.csv`
files in the format produced by `MonbusSniffer.dump_*`. The simplest
path is to extend the host script
(`projects/NexysA7/stream_characterization/flows-stream-bridge/host/dump_monbus_sram.py`)
to write captures in that same format. The schema is:

```json
{
  "meta": {
    "label": "string identifier for this run",
    "schema_version": 1,
    "record_count": <int>,
    "...": "any other metadata you want (run config, workload, etc.)"
  },
  "records": [
    {"packet": "0x<32 hex digits = 128 bits>", "timestamp": "0x<16 hex digits = 64 bits>"},
    ...
  ]
}
```

CSV variant: 2 columns `packet_hex,timestamp_hex`, no metadata.

Either format loads cleanly via:
```python
from TBClasses.monbus.sniffer import load_capture
records = load_capture("/tmp/fpga_run4.json")
```

### Step 3: Parameter tuning

Once captures from steps 1–2 (sim + FPGA) are in hand, run them through
the model and inspect the report:

```python
from TBClasses.monbus.sniffer import load_capture
from TBClasses.monbus.monbus_compressor import Encoder, format_report

for run in ["/tmp/fpga_run1.json", "/tmp/fpga_run2.json", ...]:
    enc = Encoder(cam_size=16)
    list(enc.encode(load_capture(run)))
    print(f"=== {run} ===")
    print(format_report(enc))
```

Tunables (at the top of `bin/TBClasses/monbus/monbus_compressor.py`):

| Constant | Default | What it controls |
|----------|--------:|------------------|
| `DEFAULT_CAM_SIZE` | 16 | Number of templates the CAM holds |
| `DELTA_TS_A` | 16 | Format A delta-ts width (bits) |
| `DELTA_TS_B` | 24 | Format B delta-ts width |
| `DELTA_TS_C` | 16 | Format C delta-ts width |
| `EVENT_DATA_A` | 40 | Format A event_data width |
| `EVENT_DATA_B` | 32 | Format B event_data width |
| `EVENT_DATA_C_DELTA` | 40 | Format C signed delta width |

**Decision criteria** for accepting the current values vs. growing them:

- **Tier 1 hit rate < 85%** on aggregate-run data → grow CAM (try 32),
  or add a format targeting the dominant escape reason.
- **`cam_miss` is the dominant escape reason** → grow CAM.
- **`delta_ts_overflow` is dominant** → widen `DELTA_TS_B` (currently 24
  bits ≈ 167 ms at 100 MHz; might need to grow if real workloads have
  longer quiet gaps).
- **`event_data_overflow` is dominant on perf packets** → consider a
  4th sub-format targeting perf-counter widths specifically.
- **Some templates get evicted and re-installed often** → LRU isn't
  helping; consider explicit pinning of "always-hot" templates via SW
  pre-programming (would need a new CSR interface in RTL).

Once parameters are tuned, **lock the format** in
`docs/markdown/RTLAmba/includes/monitor_package_spec.md` with explicit
bit-allocation tables. That document becomes the contract the RTL
compressor implements.

### Step 4 (for the main author, not this handoff)

Implement the actual RTL compressor in
`rtl/amba/shared/monbus_axil_group.sv` (or a sibling
`rtl/amba/shared/monbus_compressor.sv`), tested with a bit-exact
regression harness that:

1. Feeds N captured records through the Python encoder.
2. Feeds the same records through an RTL cosim of the compressor.
3. Asserts the AXIL slot streams are identical byte-for-byte.

Plus the Python decoder consuming the RTL output and reconstructing
the original records.

---

## Open questions / decisions for the FPGA work

1. **Runtime per-wrapper enable.** Today `USE_MONITOR` is a build-time
   SV parameter. Adding a runtime enable (e.g. via a new harness CSR
   that masks each wrapper's `monbus_valid` output before it reaches
   the arbiter tree) avoids needing N bitstream rebuilds. Is this worth
   adding? Probably yes if more than a couple of isolated runs are
   planned.

2. **Capture rate budget.** stream_char's `debug_sram` is 64 KB (correct
   me if it's been resized). At 24 bytes per uncompressed record, that's
   ~2700 records per snapshot. For statistical confidence on the CAM
   working set we want at least 10K records per run — so multiple SRAM
   dump cycles per run are needed, with the host reading the SRAM,
   resetting the write pointer, and starting a new burst.

3. **Workload variation.** The Python model needs traces with realistic
   diversity. Pure repeating-burst workloads will show artificially high
   compression. Recommend at least one run with the existing
   characterization workload variants (different burst lengths, mixed
   read/write, error injection) so the captures aren't degenerate.

4. **Per-source labeling in the capture file metadata.** Even if all
   monitors are enabled during a run, knowing which wrapper produced
   each packet (from its `(unit_id, agent_id)`) lets the model report
   per-source statistics after the fact. The Python side already
   extracts these fields per-packet, so no extra work in the capture —
   just make sure the runs are tagged in the JSON metadata so we know
   which workload produced which file.

---

## File map

| Path | What it is |
|------|-----------|
| `bin/TBClasses/monbus/monbus_compressor.py` | Python encoder + decoder + reporter |
| `bin/TBClasses/monbus/sniffer.py` | Live cocotb sniffer + `load_capture` helper |
| `bin/TBClasses/monbus/tests/test_monbus_compressor.py` | 24 model tests |
| `bin/TBClasses/monbus/tests/test_sniffer.py` | 6 sniffer file-I/O tests |
| `bin/TBClasses/monbus/tests/test_monbus_parser.py` | 21 parser tests (pre-existing) |
| `rtl/amba/shared/monbus_axil_group.sv` | New beat order + tag scaffolding |
| `docs/markdown/RTLAmba/includes/monitor_package_spec.md` | Spec doc — needs update after format lock |
| `docs/markdown/RTLAmba/monitor_system_whitepaper.md` | §3 timestamp policy mentions the new beat order |
| `projects/components/stream/dv/tbclasses/monbus_axil_group_tb.py` | Sniffer wired in behind `MONBUS_CAPTURE` env var |
| `projects/components/stream/dv/tests/macro/test_monbus_axil_group.py` | Calls `finalize_monbus_capture` at end-of-test |
| `projects/NexysA7/stream_characterization/flows-stream-bridge/host/dump_monbus_sram.py` | Existing FPGA-side capture path — extend to write the JSON/CSV format above |

---

## How to validate the model end-to-end before any captures

Smoke test of the round trip on the sim path, no FPGA needed:

```bash
source env_python
cd bin/TBClasses/monbus/tests
pytest -v
# Expect: 51 passed
```

Then a live sim capture:

```bash
cd projects/components/stream/dv/tests/macro
MONBUS_CAPTURE=/tmp/smoke.json pytest test_monbus_axil_group.py -v
ls -la /tmp/smoke.json
python3 - <<'PY'
import sys; sys.path.insert(0, 'bin')
from TBClasses.monbus.sniffer import load_capture
from TBClasses.monbus.monbus_compressor import Encoder, format_report
enc = Encoder(cam_size=16)
list(enc.encode(load_capture("/tmp/smoke.json")))
print(format_report(enc))
PY
```

If that pipeline works end-to-end, the FPGA-side just needs to produce
captures in the same JSON format and the rest of the toolchain is
already in place.
