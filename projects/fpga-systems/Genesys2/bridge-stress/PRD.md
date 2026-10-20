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

**Version:** 0.3 (draft) · **Date:** 2026-10-19 · **Status:** AXI4, AXI3 and AXI5 builds passing on the Genesys 2: 27/27 board runs each (9 profiles x 3 seeds x 4000 bursts per master direction) and a 15-minute chaos soak each

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
| protocol shells | `rtl/amba/shared/<proto>_{master,slave}_stress.sv` | the cores on the protocol's channel modules: AXI4, AXI3 (bursts cut to 16 beats in the generator, WID carried with each W beat, 2-bit lock), AXI5 (`axi5_*` channel modules; NSAID / TRACE / MPAM / MECID / POISON per port, from the DUT TOML's `axi5_features`) |
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
| S_SB | AXI5 slave | a request's NSAID / TRACE / MPAM / MECID is not `f_sb(address)` (from a master whose path carries sideband natively) or not 0 (from any other: the slave tells them apart by the master index in the fabric ID), a W beat's WPOISON is not `f_poison(beat address)`, or a request breaks the IDUNQ rule on the IDs the slave sees (unique with another burst of its ID held, or any request on an ID whose held burst is unique) |
| M_SB | AXI5 master | BTRACE / RTRACE is not the request's TRACE (a trace-capable bridge port echoes it whatever the slave, bridge BUG-010), an R beat's RPOISON is not `f_poison(beat address)`, or BIDUNQ / RIDUNQ is not the bit the burst was issued with |
| S_PROTO (atomics) | AXI5 slave | an AWATOP the master would never issue: not one aligned INCR beat inside the bus, a size its class does not allow, a reserved encoding |
| RD_* in a write block | AXI5 master | a read-return atomic's R beat: no atomic owed on its RID (RD_STRAY), RLAST low (RD_LAST), RRESP not the window's (RD_RESP), a lane not `f_word(address, tag, RD)` (RD_DATA) |

AXI5 sideband and poison follow the data contract: every field is a hash of
the address (`f_sb`, `f_poison` in `axi_stress_pkg`), so both ends compute it
and nothing is stored. Poison is drawn 1 beat in 2^POISON_LG2 by address
hash, on paths where both ends enable it.

AXI5 IDUNQ: a master marks a burst unique (by address hash) only when its ID
has nothing outstanding, and issues nothing more on that ID until it
completes. The bridge's master port regenerates BIDUNQ / RIDUNQ; every IDUNQ
slave checks that the fabric still keeps the rule on the IDs it sees.

AXI5 atomics: 1 write burst in 2^WR_ATOM.LG2 on an atomic path becomes one
legal beat -- AtomicStore / Load / Swap / Compare by address hash, 1..8
bytes (2..32 for Compare), aligned INCR -- on an ID with the MSB set, issued
only when that ID has nothing outstanding (the AXI5 atomic ID rule). The
operand is ordinary write data. The slave is stateless, so a read-return
atomic's "original value" is the read hash `f_word(address, tag, RD)` on the
beat's lanes; it is sent after the W beat and merged onto R between read
bursts.

### Limits

| Limit | Value | Why / effect |
|---|---|---|
| bridge: read-return atomics in flight per slave port | 8 | the slave adapter's `axi5_atomic_rr_tracker` is built `DEPTH(8)`; the ninth atomic AW stalls until a slot frees (bridge TASK-020 makes it a TOML key). Slows a run, never fails it |
| bridge: atomic masters per fabric | none | every fabric ID carries its master's index, so atomics from different masters never alias at a slave |
| model: atomic IDs | the upper half of each atomic master's ID space | atomics use ID MSB = 1; the host keeps that master's read and write IDs below it. An atomic master needs `id_width >= 2` |
| model: atomics and IDUNQ bursts in flight | one per ID | the AXI5 rules; the master waits rather than violate them |
| model: read-return atomics owed per master | 16 (`DEPTH`) | a full table holds the next atomic |
| model: read-return atomics queued per slave | 16 (`DEPTH`) | a full queue holds the atomic's W beat |
| model: atomic shapes | one beat, aligned INCR, 1..8 bytes (Compare 2..32), within the bus | a slave flags any other atomic as S_PROTO, so a fabric that changes an atomic is caught |

Every check is shown to fire by the pair test's fault injector
(`val/amba/test_axi_stress_pair.py`), and an independent Python monitor
checks the blocks themselves against the model.

## 4. Builds

| Build | DUT | Status |
|---|---|---|
| `build-axi4` | `bridge_bs_axi4`: 4 AXI4 masters (64/128/32/64, IDs 8/4/6/8, one cdc) x 4 AXI4 slaves (64/128/32/64, one cdc), a 256 MB hole | WNS +0.081 ns at 100 / 75 MHz, 94.8k LUTs (47%), no BRAM/DSP; sim and board: every profile passes under the path limits |
| `build-axi3` | `bridge_bs_axi3`: the same shape with AXI3 on every port that does not cross a clock (cpu, dma, io; mem0, mem1, mem2). The two CDC ports (acc, mem3) stay AXI4: the generator has no AXI3 CDC (`validate_axi3`, rule 3). Paths: AXI3 -> AXI3, AXI3 -> AXI4, and AXI4 -> AXI3 with bursts longer than 16 beats chopped | WNS +0.001 ns, WHS +0.013 ns at 100 / 75 MHz, 106.7k LUTs (52%); sim and board: every profile passes under the path limits |

| `build-axi5` | `bridge_bs_axi5`: AXI5 on every port that does not cross a clock (cpu 64b, dma 128b, io 32b; mem0 64b, mem1 128b, mem2 64b), all with NSAID / TRACE / MPAM / MECID; the CDC ports (acc, mem3) stay AXI4. Poison on a 64-bit clique (cpu -> mem0, mem2): the validator allows it only where every connected path is AXI5 at both ends and one width. mem1 takes native (dma), width-converted (io: sideband dropped) and AXI4 (acc) requests at once and tells them apart by the fabric's master index | with IDUNQ on every AXI5 port and atomics on the cpu clique (cpu IDs 4): WNS +0.298 ns, WHS +0.009 ns at 100 / 75 MHz, 92.1k LUTs (45%); sim 9/9 (with a pin-level count that atomics, IDUNQ and poison really ran), board 27/27, soak 172/172 |

## 5. Phases

| Phase | Adds | Shells |
|---|---|---|
| 1 | the cores, AXI4, the Genesys 2 build | `axi4_{master,slave}_stress` |
| 2a (done) | AXI3 ports, `build-axi3` | `axi3_{master,slave}_stress` (WID, 16-beat, 2-bit lock) |
| 2b (sideband + poison) | AXI5 ports in a mixed DUT, `build-axi5` | `axi5_{master,slave}_stress`: NSAID, TRACE, MPAM, MECID, POISON |
| 2c | IDUNQ, atomics (done in sim); MTE | the same shells; see bridge TASK-019 |
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
| (limit) | bridge generator | no AXI5 port may be a CDC port (the crossing carries the AXI4 set); `build-axi5` keeps its CDC ports AXI4 |
| (by design) | DUT, AXI5 master ports | a trace-capable master port echoes AxTRACE on BTRACE / RTRACE itself, whatever the slave (bridge BUG-010), and asserts in sim that a trace-capable slave echoes it too. The stress model's first slave returned an address hash and hit that assertion; it echoes now |
| bridge BUG-019 | DUT, several converters | unaligned INCR bursts keep their start misalignment past the first beat in the dwidth downsize, `axi4_to_axil4` (and AXI5-Lite / WB4) and `axi_gen_addr` (APB) paths; `axi4_to_axi3` was fixed as converters BUG-011 |

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
| AXI5: every profile x seeds 1-3, 4000 bursts | 27/27 PASS | `reports/board/bridge_bs_axi5_20261019_181755.csv` |
| AXI5 soak: chaos, a fresh seed per run, 8000 bursts per master direction, 15 min | 174/174 PASS (~11.1 M bursts) | `reports/board/bridge_bs_axi5_20261019_182057.csv` |
| AXI5 + IDUNQ + atomics: every profile x seeds 1-3, 4000 bursts | 27/27 PASS | `reports/board/bridge_bs_axi5_20261019_214752.csv` |
| AXI5 + IDUNQ + atomics soak: chaos, fresh seeds, 8000 bursts, 15 min | 172/172 PASS (~11.0 M bursts) | `reports/board/bridge_bs_axi5_20261019_215052.csv` |

## 8. Running

```
bin/regen.sh                                   # bridges, regblocks, harness
cd dv/tests && make run-all-gate-parallel      # sim: the board's host code over the sim UART
cd build-axi4 && make bitstream && make program   # or build-axi3
python3 bin/run_stress.py                      # every profile, 3 seeds (--build axi3 for build-axi3)
python3 bin/run_stress.py --soak 3600          # chaos, a fresh seed per run, one hour
```
