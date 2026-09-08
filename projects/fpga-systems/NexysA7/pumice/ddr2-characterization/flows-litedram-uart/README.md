# flows-litedram-uart — LiteDRAM DDR2 comparison flavor

A drop-in flavor of the ddr2-characterization harness where **LiteDRAM's DDR2
controller** replaces pumice, so the same pattern generator + the same external
perf taps measure both — an apples-to-apples benchmark. Purpose: once the pumice
perf data is in, run this to find the gaps (if any) and know what to fix.

## What's here

- `litedram_hp.yml` — LiteDRAM core config tuned to mirror a **high-perf pumice**
  (`reorder`/`happy_hybrid` preset). Nexys A7 = Nexys4 DDR, MT47H64M16 x16 DDR2,
  A7DDRPHY.
- `regen.sh` — regenerate the core(s) from the YAML (litex-venv310).
- `build_board/gateware/litedram_core.v` — real A7DDRPHY core (for silicon).
- `build_sim/gateware/litedram_core_sim.v` — SDRAMPHYModel core (verilatable).

## High-perf config ↔ pumice mapping

| pumice high-perf | litedram_hp.yml / ControllerSettings default | 
|---|---|
| `scheme = ROW_MAJOR` | `address_mapping = "ROW_BANK_COL"` (default) |
| `page_policy = OPEN`/`HAPPY_HYBRID` | `with_auto_precharge = True` (lookahead adaptive, default) |
| `lookahead = max` (reorder window) | `cmd_buffer_depth = 16` |
| `force_inorder = False` | multiplexer per-bank arbitration (structural) |
| `refresh_defer` | `refresh_postponing` (default 1; bump if exposed) |
| — (OOO read returns) | **not matched** — LiteDRAM reorders commands, not per-port responses; reflects in latency spread only |

Operating point: stock nexys4ddr (100 MHz sys, 1:4). Proven-safe fallback if
silicon leveling is marginal: 75 MHz / 1:2 (the point that passed memtest this
session) — edit `sys_clk_freq`/`input_clk_freq` and regenerate.

## Generated top interface (`litedram_core`) — the harness boundary

```
input  clk, rst                       # 100 MHz ref + reset (core has its own PLL)
output init_done, init_error          # BIOS self-levels DDR2, asserts init_done
output pll_locked, user_clk, user_rst # user_clk = AXI-port clock domain
input  uart_rx / output uart_tx       # LiteDRAM BIOS console (self-init; not the harness UART)
output ddram_* (a/ba/cas_n/cke/clk/cs_n/dm/dq/dqs/odt/ras_n/reset_n/we_n)  # board pins (board core only)
user_port_axi_0_*                     # AXI4: 64-bit data, 8-bit id, 27-bit addr (128 MiB)
```

The AXI port is **already 64-bit / id-8** — matches `axi4_master_wr_pattern_gen`
with **no width/id adapter**. The sim core has no `ddram_*` pads (PHY model is
internal).

## Harness wiring (all on `user_clk`)

```
                 ┌─ axi4_master_wr_pattern_gen ─┐        ┌───────────────┐
harness_csr ───▶ │  (+ axi4_master_rd_crc_check) │──AXI──▶│ litedram_core │──▶ ddram pads / model
(timer/perf/     └──────────────┬───────────────┘        │  (self-init)  │
 engine cfg)                    │ (snoop)                 └──────┬────────┘
UART bridge ───▶ harness_csr    ▼                                │ init_done
                 axi_bus_meter + axi_perf_latency_hist  ◀── wait ─┘
```

**Reused unchanged** from `build-perf`: the pattern gen + CRC check, the
perf collateral (`axi_bus_meter`, `axi_perf_latency_hist`), `harness_csr`
(timer/perf/engine-cfg), the UART bridge, and the host `pumice_char` metrics/
report layer (it measures from the AXI side, controller-agnostic). **Dropped vs
pumice:** DFI, external a7ddrphy, leveling, `pumice_csr` — LiteDRAM self-inits.

## Status / prerequisites to make it functional

1. **RTL generated** ✅ (both cores, correct interface + high-perf config).
2. **BIOS toolchain** ⚠️ — cores were generated with `--no-compile-software`, so
   the init ROM is empty (won't self-init yet). Install a riscv-gcc (LiteX
   toolchain) and regenerate WITHOUT `--no-compile-software` so the BIOS is baked
   in → `init_done` works in sim and on board. See `regen.sh`.
3. **SV harness top** — `ddr2_char_litedram_top.sv`: instantiate `litedram_core`,
   wire `user_port_axi_0` to the pattern gen, tap the perf monitors, run
   `harness_csr` + UART bridge on `user_clk`, gate the run on `init_done`. (TODO)
4. **Sim**: verilate `litedram_core_sim` + the harness; the vexriscv BIOS boot
   over SDRAMPHYModel is slow but functional once the ROM is populated.
5. **Board**: synth `litedram_core` (real A7DDRPHY) into the harness bitstream;
   `ddram_*` to the existing DDR2 XDC pins (no pin changes).

The comparison itself is gated on the pumice perf data (in progress) + board
availability — this flavor is staged so it's ready to run the moment both land.
