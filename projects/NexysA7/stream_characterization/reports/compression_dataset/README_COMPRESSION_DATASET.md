# Monbus compression dataset — handoff to the RTL compressor author

**Date locked:** 2026-06-06
**Format-lock commit:** `65c6ef8b feat(monbus): lock compressor format at cam=32, idx=5b + drop pollution at parse`
**Capture-path-fix commit:** `65b243b3 feat(stream_char): WR_PTR-bounded captures + drop too-strict validity default`
**Source:** Nexys A7, stream_char bitstream + harness, descriptor-bus monitor
**Audience:** Engineer/agent implementing the RTL compressor described in `MONBUS_COMPRESSION_HANDOFF.md` Step 4.

This is the single page that should let you size, lay out, and verify
the compressor without re-deriving anything. Every other doc this
references is reachable through its absolute repo path.

---

## 1. The dataset

```
projects/NexysA7/stream_characterization/reports/compression_dataset/
  desc_axi_16desc_8ch_1MB.json       ← THIS dataset
  README_COMPRESSION_DATASET.md      ← THIS file
```

**Workload:** `python3 run_characterization.py --configs 16desc_8ch_1MB`
- 8 channels × 16 descriptors × 1 MB transfer = 128 MB total DMA
- 18.5 s wall-clock (workload + UART overhead)
- All 8 channels pass CRC; bitstream timing clean (built on `893d43e0`)

**Source monitor:** `axi4_master_rd_mon` inside
`projects/components/stream/rtl/macro/scheduler_group_array.sv`, the
descriptor-fetch read-bus monitor between `scheduler_group` and
`desc_ram`. Cones enabled via `DAXMON_ENABLE = 0x1F` (`mon` +
`error` + `compl` + `timeout` + `perf`; debug stays off until
[task #114](https://example.invalid/#114) lands the cfg port).

**File schema:** matches `bin/TBClasses/monbus/sniffer.MonbusSniffer.dump_json`
exactly so `sniffer.load_capture(path)` round-trips into the encoder.

```json
{
  "meta": {
    "label": "desc_axi",
    "schema_version": 1,
    "record_count": 682,
    "source_format": "monbus_axil_group_24B_ts_mode_1",
    "dump_base": "0x00040000",
    "dump_bytes_max": "0x40000",
    "live_bytes": "0x4000",
    "workload_cmd": "python3 run_characterization.py --configs 16desc_8ch_1MB --port /dev/ttyUSB2",
    "captured": "20260606_222112",
    "description": "axi4_master_rd_mon inside scheduler_group_array..."
  },
  "records": [
    {"packet": "0x10000000000008010000000000020020", "timestamp": "0x00000000036eb3b4"},
    {"packet": "0x10000000000010140000000000020020", "timestamp": "0x00000000036eb3e8"},
    ...
  ]
}
```

Each record is one 128-bit `MonitorPacket` + 64-bit local timestamp.
`packet` hex is bit-exact what the RTL emitted on the monbus master
side; `timestamp` is the 60-bit `source_ts` field captured by
`monbus_axil_group` (top 4 bits zero today — that's the encoding tag
reserved for the future Tier-1 compressor; see Step 4 of the
[main handoff doc](../../MONBUS_COMPRESSION_HANDOFF.md)).

---

## 2. The format being locked

Single source of truth — every constant the RTL needs:
```
bin/TBClasses/monbus/monbus_compressor.py   (lines 1-90)
```

### 2.1 Beat layouts (the wire format)

```
Tag 0x0 — RAW / Tier-0 escape (3 beats, 192 bits total):
  beat 0:  [63:60] tag=0x0  | [59:0] source_ts[59:0]
  beat 1:  packet[127:64]
  beat 2:  packet[63:0]

Tag 0x1 — Tier-1 format A (template hit, small payload, 1 beat):
  beat 0:  [63:60] tag=0x1  | [59:55] tmpl_idx[4:0]  | [54:40] delta_ts[14:0]  | [39:0] event_data[39:0]
  Covers:  Δts ≤ 32K cycles (~328 µs @ 100 MHz), event_data ≤ 40 bits

Tag 0x2 — Tier-1 format B (template hit, big delta_ts, 1 beat):
  beat 0:  [63:60] tag=0x2  | [59:55] tmpl_idx[4:0]  | [54:32] delta_ts[22:0]  | [31:0] event_data[31:0]
  Covers:  Δts ≤ 8M cycles (~84 ms @ 100 MHz), event_data ≤ 32 bits

Tag 0x3 — Tier-1 format C (template hit, event_data delta, 1 beat):
  beat 0:  [63:60] tag=0x3  | [59:55] tmpl_idx[4:0]  | [54:40] delta_ts[14:0]  | [39:0] ed_delta[39:0] signed
  Covers:  Δts ≤ 32K cycles, monotonic counters / sequential addresses

Tags 0x4-0xF — Reserved for future use (decoder rejects with an error)
```

### 2.2 Constants (mirror these in SV)

```python
TAG_RAW       = 0x0
TAG_FORMAT_A  = 0x1
TAG_FORMAT_B  = 0x2
TAG_FORMAT_C  = 0x3

TS_BITS       = 60     # source_ts width in beat 0 of Tier-0
DELTA_TS_A    = 15     # bits
DELTA_TS_B    = 23
DELTA_TS_C    = 15
EVENT_DATA_A  = 40
EVENT_DATA_B  = 32
EVENT_DATA_C_DELTA = 40       # signed
TMPL_IDX_BITS = 5             # 5b idx → 32-entry CAM
TMPL_IDX_MASK  = 0x1F
TMPL_IDX_SHIFT = 55           # idx sits at [59:55]

DEFAULT_CAM_SIZE = 32
```

### 2.3 CAM specification

- **Size:** 32 entries (locked)
- **Key:** `(packet_type, protocol, event_code, channel_id, agent_id, unit_id)`
  = 4 + 4 + 8 + 9 + 16 + 8 = **49 bits**
- **Value:** `last_event_data[63:0]` (used by Format C only)
- **Eviction:** LRU (least-recently-used → evicted on Tier-0 install)
- **Touch policy:** on Tier-1 hit, move that entry to MRU position;
  on Tier-0 install (CAM miss), insert at MRU, evict LRU
- **Per-entry size:** 49b key + 64b last_event_data + ~5b LRU rank = 118b
- **Total CAM storage:** ~3.8 Kb ≈ **480 bytes**

### 2.4 Encoder decision tree (per record)

```
1. Compute key = _key_from_packet(packet)
   Compute event_data = packet[63:0] >> EVENT_DATA_SHIFT
   Compute delta_ts = (timestamp - last_ts) & ((1<<60)-1)

2. CAM lookup by key:
   - MISS  → Tier-0 escape: install (key, event_data), emit 3-beat raw
   - HIT(idx) → continue to step 3

3. Try Tier-1 formats in order:
   A. if delta_ts < 2^15 and event_data < 2^40:
        emit format A, _touch(idx, event_data), done
   B. else if delta_ts < 2^23 and event_data < 2^32:
        emit format B, _touch(idx, event_data), done
   C. else if delta_ts < 2^15:
        let ed_delta = event_data - CAM[idx].last_event_data
        if signed-fits-in-40b(ed_delta):
            emit format C, _touch(idx, event_data), done
   else:
        Tier-0 escape (don't reinstall — key already in CAM)
```

The CAM-hit-but-still-escape case bumps the appropriate escape reason
(`delta_ts_overflow` / `event_data_overflow` / `ed_delta_overflow`).
See `Encoder.encode_one` in the spec file.

### 2.5 Decoder mirror

The Python decoder reconstructs the exact CAM state from the slot
stream alone (no out-of-band info). The RTL decoder, if implemented,
must do the same — Tier-0 escapes install templates, Tier-1 hits
reconstruct (key, event_data) from CAM[idx] + slot fields and touch
the CAM the same way the encoder did.

---

## 3. Numbers from this dataset (your bring-up target)

```
records:           682
distinct tmpls:     32  (4.7% unique — fits exactly in CAM)
Tier-1 hit rate: 93.5%  [A=628, B=10, C=0]
Tier-0 escapes:   6.5%  [cam_miss=32, delta_ts_overflow=12]
compression ratio: 2.66x
round-trip:         OK (Python encoder → Python decoder → original records, bit-exact)
```

Frequency histogram (templates by occurrence count):

| Hits per template | Templates | Records | Class |
|---:|---:|---:|---|
| 127 | 2 | 254 | hot |
| 126 | 2 | 252 | hot |
| 9 | 16 | 144 | warm |
| 6 | 4 | 24 | warm |
| 1 | 8 | 8 | cold (the only Tier-0 escapes) |
| **total** | **32** | **682** | |

The 32 distinct templates fit exactly in CAM=32. Going to CAM=64 or
larger gives **zero** incremental hit rate on this workload (verified
in the parameter sweep — see commit `65c6ef8b` log).

Reference numbers from the handoff doc that this dataset confirms:
- target Tier-1 hit ≥ 85%  → **achieved 93.5%**
- target compression ratio ≥ 2.6x → **achieved 2.66x**

---

## 4. Verification harness (RTL acceptance criterion)

The RTL compressor passes when its slot stream is **byte-identical** to
what the Python encoder produces for the same input record sequence.

```python
import sys
sys.path.insert(0, "bin")
from TBClasses.monbus.sniffer import load_capture
from TBClasses.monbus.monbus_compressor import Encoder, Decoder

records = load_capture(
    "projects/NexysA7/stream_characterization/reports/"
    "compression_dataset/desc_axi_16desc_8ch_1MB.json"
)

# 1. Generate the golden 64-bit slot stream
enc = Encoder()                       # uses DEFAULT_CAM_SIZE=32
golden_slots = list(enc.encode(records))

# 2. (Round-trip sanity) decode the golden slots and verify
dec = Decoder()
roundtrip = list(dec.decode(golden_slots))
assert roundtrip == records, "Python encoder/decoder mismatch"

# 3. Feed `records` into the RTL compressor cosim, collect its
#    emitted 64-bit slot stream `rtl_slots`. Compare:
assert rtl_slots == golden_slots, (
    f"RTL diverges at slot {next(i for i, (a, b) in enumerate(zip(rtl_slots, golden_slots)) if a != b)}: "
    f"rtl=0x{rtl_slots[i]:016x} golden=0x{golden_slots[i]:016x}"
)
```

For an end-to-end test:
```bash
source $REPO_ROOT/env_python
cd $REPO_ROOT
pytest bin/TBClasses/monbus/tests/test_monbus_compressor.py -v
# Expect 24 passed — these are the model-side regression tests that
# the RTL bit-exact harness must extend.
```

---

## 5. Open follow-ups (not blocking the RTL compressor — for awareness)

| Item | Where | Why it matters to compression |
|---|---|---|
| `PROTOCOL_CORE` event-code enum in Python | `bin/TBClasses/monbus/monbus_types.py` `_EVENT_CODE_ENUM_LOOKUP` | The scheduler-side packets in this dataset have `proto=PROTOCOL_CORE` (=4); `is_valid_event_code()` returns False for them today. `parse_records(validate=False)` (default) sidesteps it, but the model-side `MonitorPacket.is_valid()` is incorrect for CORE. Pure Python fix. |
| Runtime per-wrapper enable | task #114 (`cfg_debug_enable` + `cfg_threshold_enable` + `cfg_compl_enable` as wrapper ports) | Required before we can capture from the **other** sources (`host_bridge_*`, the bridge mon adapters in `bridge_stream_char_axil_mon`). Today only `desc_axi` is runtime-isolatable, which is why this dataset is single-source. |
| Heavier-workload captures | n/a — same script, different `--configs` arg | The `1desc_1ch_1MB` workload produces only 1 record (1 descriptor = 1 monitor packet). For statistical breadth across more (channel, agent) combinations, sweep `2desc_*` through `16desc_*` and concatenate. |
| Cold-tail compression | model + RTL | The 8 single-hit templates (1% of records) escape to Tier-0. Per the handoff doc, addressing these requires SW pre-pinning of "always-hot" templates — a new CSR interface. Not in scope for the initial RTL compressor; mentioned for context. |

---

## 6. Quick rebuild / re-capture

```bash
# 1. Rebuild bitstream (if needed)
cd projects/NexysA7/stream_characterization/flows-stream-bridge
make bitstream            # ~15-30 min, includes verify-sim per task #92

# 2. Program FPGA (Nexys A7)
make program

# 3. Find UART port (renumerates after programming)
ls /dev/ttyUSB*

# 4. Sanity check
cd host
source $REPO_ROOT/env_python
python3 dump_status.py --port /dev/ttyUSB2   # adjust port
# Expect BUILD_ID = 0x53545243 ("STRC")

# 5. Capture (full handoff Run 1-6 mapping in PER_SOURCE_CAPTURE.md)
python3 per_source_capture.py \
  --port /dev/ttyUSB2 \
  --output-dir /tmp/compression_dataset_run_$(date +%Y%m%d) \
  --workload-cmd "python3 run_characterization.py --configs 16desc_8ch_1MB --port /dev/ttyUSB2"
```

---

## 7. Related files in this repo

| Path | Purpose |
|---|---|
| `MONBUS_COMPRESSION_HANDOFF.md` (project root) | Original handoff doc — context for steps 2, 3, 4 |
| `bin/TBClasses/monbus/monbus_compressor.py` | The locked format spec + Python encoder/decoder/reporter |
| `bin/TBClasses/monbus/sniffer.py` | Live cocotb sniffer + `load_capture()` for these JSON files |
| `bin/TBClasses/monbus/tests/test_monbus_compressor.py` | 24 model tests — extend for RTL bit-exact harness |
| `rtl/amba/shared/monbus_axil_group.sv` | The tag/ts scaffolding (commit `4e00aafb`) — wire-side beat-order swap, compressor will replace `tag=0x0` hardwire |
| `projects/NexysA7/stream_characterization/flows-stream-bridge/host/per_source_capture.py` | The orchestrator that produced this dataset |
| `projects/NexysA7/stream_characterization/flows-stream-bridge/host/dump_monbus_sram.py` | UART-side SRAM drain + JSON serializer |
| `projects/NexysA7/stream_characterization/flows-stream-bridge/host/PER_SOURCE_CAPTURE.md` | Local capture procedure quickstart |

---

**Bottom line for the RTL author:**
- Implement the format in §2 exactly. CAM at 32. idx at 5b. delta_ts widths
  15/23/15.
- Test bit-exact against §4's golden slot stream on §1's dataset.
- Pass when 24 model tests + a new "this RTL matches the Python golden"
  test all pass.
- Numbers in §3 are what you should see on the same dataset; they're
  not the acceptance criterion (that's bit-exact slot match), they're
  the sanity check that you haven't accidentally broken the encoder.
