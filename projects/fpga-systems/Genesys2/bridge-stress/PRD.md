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

# Genesys 2 (Kintex-7) Bridge Stress Model -- PRD

**Version:** 0.2 (draft) · **Date:** 2026-10-19 · **Status:** AXI4 and AXI3 builds passing on the Genesys 2: 27/27 board runs each (9 profiles x 3 seeds x 4000 bursts per master direction) and a 15-minute chaos soak each

## 1. Purpose

Validate the bridge generator's fabrics in silicon, independent of any other
IP. Every port of the device under test (a generated bridge) is driven or
answered by a purpose-built stress block, so the only design on the board
whose behaviour is in question is the bridge.

The existing harnesses were reviewed first. Their blocks are kept where they
fit and not used where they cannot check a fabric:

| Block | From | Why not as-is |
|---|---|---|
| `axi4_master_wr_injector` / `axi4_master_rd_crc_check` | pumice / DDR2 characterization | the read checker regenerates each beat's address in AR issue order and never checks RID/BID: a fabric that reorders across IDs or interleaves R (this one does both) fails it falsely, and a misrouted response goes unseen |
| `axi4_slave_rd_injector` / `axi4_slave_wr_crc_check` | STREAM characterization | one burst at a time, in order, with a running CRC per channel: they cannot reorder, interleave, or answer per-ID, which is what exercises the bridge's response paths |

What carries over: the address-generation discipline, the protocol channel
modules (`axi4_{master,slave}_{rd,wr}`), the UART host link and
configuration-bridge pattern, the stage-then-GO launch, PeakRDL register
access by name, and the sim harness that runs the board's own host code.

## 2. The data contract

Every byte is a function of its fabric address, the owning slave's tag and
the direction (`rtl/amba/includes/axi_stress_pkg.sv`, `f_word`). Nothing is
stored, so any master may read or write any slave, responses may come back in
any order, and a byte that lands on the wrong lane, beat, address or slave
fails the check at the far end. The function is xorshift32-based: a bijection,
so an address error is always a data error, and XOR-only, so it costs two
LUT levels at bus rate.

## 3. Architecture

| Layer | Where | What |
|---|---|---|
| stress cores | `rtl/amba/shared/axi_stress_*.sv` | protocol-neutral master (generator + per-ID ordered scoreboard, rd and wr) and slave (hash responder with reorder / interleave / latency / throttle / SLVERR window); `cfg` / `sts` structs, no CSRs |
| protocol shells | `rtl/amba/shared/<proto>_{master,slave}_stress.sv` | the cores on the protocol's channel modules: AXI4, AXI3 (bursts cut to 16 beats in the generator, WID carried with each W beat, 2-bit lock) |
| register blocks | `rtl/regs/*.rdl`, `rtl/bstress_{mst,slv}_csr.sv` | one regblock per block, in that block's clock (`apb4_to_peakrdl` carries the access across) |
| harness | `rtl/generated/bs_harness_<dut>/` from `bin/gen_bs_harness.py` | generated from the DUT TOML: one shell per DUT port, the configuration bridge, control regs, GO/STOP into every clock |
| board top | `rtl/bs_genesys2_top.sv` | MMCM (aclk 100 MHz, cclk 75 MHz), resets, UART, LEDs |
| host | `bin/bstress.py`, `bin/run_stress.py` | window plan from the TOML, profiles, verdict; the same code in sim and on the board |

### Checks

| Code | Side | Fires on |
|---|---|---|
| RD_STRAY / WR_STRAY | master | a response on an ID with nothing outstanding |
| RD_LAST | master | RLAST on the wrong beat of the burst its RID names |
| RD_RESP / WR_RESP | master | a response code other than the window's (OKAY / SLVERR / DECERR) |
| RD_DATA | master | an active byte lane differs from `f_word` |
| WR_EARLY | master | a B before the burst's last W left the master |
| HANG | master | work outstanding and no response for 2^n cycles |
| S_ADDR | slave | a request outside the slave's window (misroute) |
| S_PROTO | slave | an illegal burst: size, WRAP shape, FIXED/WRAP length, 4 KB crossing |
| S_WDATA / S_WSTRB / S_WLAST | slave | a strobed byte wrong, a strobe outside the beat, WLAST misplaced |
| S_WID | AXI3 slave | a W beat whose WID is not the AWID of the burst it belongs to (interleaved or mis-stamped write data) |

Every check is shown to fire by the pair test's fault injector
(`val/amba/test_axi_stress_pair.py`), and an independent Python monitor
checks the blocks themselves against the model.

## 4. Builds

| Build | DUT | Status |
|---|---|---|
| `build-axi4` | `bridge_bs_axi4`: 4 AXI4 masters (64/128/32/64, IDs 8/4/6/8, one cdc) x 4 AXI4 slaves (64/128/32/64, one cdc), a 256 MB hole | WNS +0.081 ns at 100 / 75 MHz, 94.8k LUTs (47%), no BRAM/DSP; sim and board: every profile passes under the path limits |
| `build-axi3` | `bridge_bs_axi3`: the same shape with AXI3 on every port that does not cross a clock (cpu, dma, io; mem0, mem1, mem2). The two CDC ports (acc, mem3) stay AXI4: the generator has no AXI3 CDC (`validate_axi3`, rule 3). Paths: AXI3 -> AXI3, AXI3 -> AXI4, and AXI4 -> AXI3 with bursts longer than 16 beats chopped | WNS +0.001 ns, WHS +0.013 ns at 100 / 75 MHz, 106.7k LUTs (52%); sim and board: every profile passes under the path limits |

## 5. Phases

| Phase | Adds | Shells |
|---|---|---|
| 1 | the cores, AXI4, the Genesys 2 build | `axi4_{master,slave}_stress` |
| 2a (done) | AXI3 ports, `build-axi3` | `axi3_{master,slave}_stress` (WID, 16-beat, 2-bit lock) |
| 2b | AXI5 ports in a mixed DUT | `axi5_*` (the bridge's AXI5 feature groups) |
| 3 | AXI4-Lite / AXI5-Lite, APB4 / APB5, WB4 | single-beat shells; slaves in offset mode where the bridge hands them a window offset |

## 6. Findings

| ID | Where | Finding |
|---|---|---|
| bridge BUG-018 | DUT | width-converted paths emit illegal AXI for FIXED, WRAP, narrow and unaligned bursts -- in sim and on the board; the host limits those paths to aligned full-width INCR (`bstress.path_caps`) until it is fixed |
| converters BUG-010 | shared CSR path | `peakrdl_to_cmdrsp` hands the regblock every access twice: a singlepulse is two cycles. Through a toggle synchronizer that lost the cclk domain's GO; the harness edge-detects GO / STOP |
| (fixed here) | stress master | `32'(now - stamp)` on 16-bit stamps saturated LAT_SUM in Vivado, not in Verilator; the latency is a 16-bit wire now |
| converters BUG-011 (fixed) | DUT, AXI3 slave adapters | `axi4_to_axi3` chopped an unaligned INCR longer than 16 beats into chunks that all stayed unaligned (AXI: every beat after the first is aligned), so the AXI3 slave took the first beat of each later chunk for a partial one. `S_WSTRB` in sim and on the board (0/4 runs on the pre-fix bitstream); the chunk address is aligned now, with regressions in the converter suite |
| (fixed here) | build flow | `make lint` never passed `BS_HARNESS`, so every build linted the AXI4 harness; the build Makefiles set `LINT_DEFINES` |
| (limit) | bridge generator | no AXI3 port may be a CDC port (v1); `build-axi3` keeps its CDC ports AXI4 |

## 7. Board results

| Run | Result | Data |
|---|---|---|
| every profile x seeds 1-3, 4000 bursts per master direction | 27/27 PASS; 0.34-19.2 ms per run | `reports/board/bridge_bs_axi4_20261019_102024.csv` |
| `bursts`, `narrow` with `--full-axi` | FAIL as BUG-018 predicts; no hang | `reports/board/bridge_bs_axi4_20261019_102327.csv` |
| latency-fix bitstream: every profile x seeds 11-12, 4000 bursts | 18/18 PASS; chaos latency mean 2338 / max 19689 cycles | `reports/board/bridge_bs_axi4_20261019_103727.csv` |
| soak: chaos, a fresh seed per run, 8000 bursts per master direction, 15 min | 166/166 PASS (~10.6 M bursts) | `reports/board/bridge_bs_axi4_20261019_103942.csv` |
| AXI3, pre-fix bitstream (BUG-011): `clean`, `bursts`, seeds 1-2 | 0/4 PASS: `S_WSTRB` on the AXI3 slaves, every error from the AXI4 master's chopped writes | `reports/board/bridge_bs_axi3_20261019_135031.csv` |
| AXI3: every profile x seeds 1-3, 4000 bursts | 27/27 PASS | `reports/board/bridge_bs_axi3_20261019_140649.csv` |
| AXI3 soak: chaos, a fresh seed per run, 8000 bursts per master direction, 15 min | 168/168 PASS (~10.7 M bursts) | `reports/board/bridge_bs_axi3_20261019_140943.csv` |

## 8. Running

```
bin/regen.sh                                   # bridges, regblocks, harness
cd dv/tests && make run-all-gate-parallel      # sim: the board's host code over the sim UART
cd build-axi4 && make bitstream && make program   # or build-axi3
python3 bin/run_stress.py                      # every profile, 3 seeds (--build axi3 for build-axi3)
python3 bin/run_stress.py --soak 3600          # chaos, a fresh seed per run, one hour
```
