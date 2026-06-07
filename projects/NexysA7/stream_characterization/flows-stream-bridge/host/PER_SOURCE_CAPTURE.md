# Per-source capture quickstart

Sister doc to `MONBUS_COMPRESSION_HANDOFF.md`. Tells you the concrete
local commands to produce JSON capture files that feed the Python
compression encoder.

## Prereqs

- Bitstream built and programmed (see `make bitstream && make program`
  from `flows-stream-bridge/`). The trace-SRAM capture path needs the
  beat-order swap committed in `4e00aafb` — bitstreams older than
  that emit records in the legacy order and will be mis-parsed.
- FPGA powered, UART connected. Default port `/dev/ttyUSB1`.
- `env_python` sourced (`source $REPO_ROOT/env_python`).

## Sources today

| Source     | Where it lives                                           | Cones runtime-controllable today |
|------------|----------------------------------------------------------|----------------------------------|
| `desc_axi` | `axi4_master_rd_mon` inside `scheduler_group_array.sv`. Covers the descriptor-fetch read path between scheduler and `desc_ram`. | error, compl, timeout, perf (via `DAXMON_ENABLE` bits 1..4). Debug stays off at runtime until task #114 lands. |

Sources **not yet wired** (would need #114 cfg_*_enable as wrapper
ports, and the harness to consume `bridge_stream_char_axil_mon`):

- `host_bridge_<port>` — per-adapter `axil4_*_mon` on the bridge.
- `stream_core_*` — read/write engine monitors per channel.

## Single capture

```bash
cd $REPO_ROOT
source env_python
cd projects/NexysA7/stream_characterization/flows-stream-bridge/host

# Tab A: terminal that will program the FPGA + run captures.
python3 per_source_capture.py \
  --port /dev/ttyUSB1 \
  --output-dir /tmp/compression_dataset \
  --workload-cmd "python3 run_characterization.py --configs 4desc_8ch --port /dev/ttyUSB1"
```

That:
1. Zeros every monitor enable.
2. Programs DAXMON for the `desc_axi` source (all 4 runtime cones on).
3. Runs `run_characterization.py --configs 4desc_8ch` as a subprocess.
4. After the workload returns, drains 256 KB of `debug_sram` (start
   addr `0x0004_0000`) into a JSON file:
   `/tmp/compression_dataset/per_source_desc_axi_<TIMESTAMP>.json`

## Handoff doc's Run 1-6 matrix (today's possible mapping)

The handoff suggests six runs (descriptor-fetch only / read-engine only
/ write-engine only / all / idle-heavy / error-injection). With only
`desc_axi` runtime-isolatable today, the practical mapping is:

| Handoff run | Local command                                                                          |
|-------------|----------------------------------------------------------------------------------------|
| 1: fetch only | `per_source_capture.py … --workload-cmd "run_characterization.py --configs 1desc_1ch"` |
| 2: read only  | (defer — no runtime knob; would need #114) |
| 3: write only | (defer — no runtime knob; would need #114) |
| 4: aggregate  | `per_source_capture.py … --workload-cmd "run_characterization.py --configs 4desc_8ch"` |
| 5: idle-heavy | `per_source_capture.py … --workload-cmd "run_characterization.py --configs 1desc_1ch"` with long settle |
| 6: error-injection | (defer — need an error-injection workload variant) |

For Step 3 (parameter tuning) we only need a non-degenerate workload
mix from desc_axi to start. Runs 4+5 give that. Drop the dataset off
to the compression agent for an initial round-trip; we'll expand to
the other sources once #114 lands.

## Feed captures to the encoder

```bash
cd $REPO_ROOT
source env_python
python3 - <<'PY'
import sys
sys.path.insert(0, "bin")
from TBClasses.monbus.sniffer import load_capture
from TBClasses.monbus.monbus_compressor import Encoder, format_report

import glob
for path in sorted(glob.glob("/tmp/compression_dataset/per_source_*.json")):
    enc = Encoder(cam_size=16)
    list(enc.encode(load_capture(path)))
    print(f"=== {path} ===")
    print(format_report(enc))
    print()
PY
```

## Dry-run (no FPGA)

```bash
python3 per_source_capture.py \
  --port /dev/null --output-dir /tmp/psc_test \
  --workload-cmd "echo workload" --dry-run
```

Walks the orchestration path without touching the UART or kicking the
workload. Useful sanity check after edits to the runner.

## When the FPGA doesn't respond

1. Power-cycle the board (the user has done this for us already).
2. Re-program: `cd flows-stream-bridge && make program`.
3. Confirm with `python3 dump_status.py --port /dev/ttyUSB1` —
   should print non-zero BUILD_ID (`STRC` = `0x5354_5243`).
4. If still no response, the bitstream may have synth-time issues
   with the post-#114 perfmon ports. Tighten `DESC_MON_ENABLE_*_LOGIC`
   defaults on `stream_top_ch8` for the next pass.
