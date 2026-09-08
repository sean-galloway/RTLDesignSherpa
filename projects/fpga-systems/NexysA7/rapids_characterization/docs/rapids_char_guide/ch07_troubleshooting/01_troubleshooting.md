# Troubleshooting

## Current state

Silicon-validated. `make smoke` passes both paths; `make suite` passes 48/48
(3 channels × 4 beats × 2 backpressure × 2 seeds). Timing closes at 100 MHz
(setup WNS +0.007 ns, 0 failing endpoints; hold WHS +0.011 ns). Post-route
utilization (4-channel, `xc7a100t-1`): 37,555 LUTs (59.2%), 28,683 FF (22.6%),
22 BRAM (16.3%), 0 DSP. There is no separate `KNOWN_ISSUES` file — the
known-state material lives in `docs/rapids_characterization_findings.md`.

## Known gotchas

| Symptom | Cause / workaround |
|---------|--------------------|
| SINK over-produces / desyncs | The generator `start` must be a one-cycle pulse, not a held level (a UART-held level runs the generator repeatedly). Fixed in RTL; residual: SINK is fully trustworthy only on the **first arm after a board reset** — a full SINK sweep needs a per-config reset. SOURCE re-arms cleanly. |
| Stale scheduler/descriptor state | `reset_channels()` pulses `CHANNEL_RESET` on both halves before each run — the sink does not self-clean after a transfer. |
| Meter reads 0 / frozen | The bus meters have no per-run auto-reset. Arm each run via `OBS_CTRL.arm` or the `CSR_GO` write; use `CSR_OBS_TARGET = channels × beats` for a deterministic freeze window. |
| `gen_expected_crc_valid` intermittently 0 | Non-fatal — PASS anchors on the data-path CRC (`WR_CRC` vs golden); the generator self-CRC is corroboration only. |
| Spurious read failure | `csr_read()` retries up to 3× on malformed/short UART frames. |

: Known issues and workarounds

## Cannot find the board

The USB-UART re-enumerates across reboots/replugs. `--port auto` (default) probes
each `/dev/ttyUSB*` and picks the board whose region-2 `CTRL`/`ID` reads
`0x52415031` ("RAP1"). `make program` and the UART campaign are pinned to the
same board by JTAG serial (override `RAPIDS_CHAR_JTAG_SERIAL`) so the flash and
the run land together.

## Board-fit vs sim geometry

The harness sim defaults (`SRAM_DEPTH = 4096`, `DESC_RAM_ENTRIES = 2048`) inflate
to ~148 BRAM tiles — over the 100T's 135 — so the board build trims both to 256
(~22 tiles). This is a build-time generic only; the RTL is unchanged. Set
`CHANNELS` once (it drives both the build generic and the host `--channels`) so
the two never drift.

## Three different "0x1000"s

Do not conflate them: the **SNK APB half** is at APB `0x1000`; the host default
**`MON_BASE`** is `0x1000`; and the in-core DUT monitors (which would live in a
`0x1000` monitor window) are compiled **out** (`GEN_MON = 0`) for this build.

## Vivado-only package collisions

`rapids_pkg` vs `stream_pkg` enum-label/type clashes (`RD_*`, `CH_*`,
`channel_state_t`, `descriptor_t`, …) surface only under Vivado's flattened
`$unit` scope — Verilator does not catch them. They are resolved by
`rapids_pkg::` qualification; if a Vivado elaboration errors on a duplicate enum
label, look here first.
