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

# Genesys 2 (Kintex-7) Fabric Benchmark — PRD

**Version:** 0.3 (draft) · **Date:** 2026-10-15 · **Status:** K0 done in sim (legs A, B1); K1/K2 W2 on the board, all three legs

## 1. Purpose

Run the DE10-Standard fabric benchmark on the Genesys 2 first, for two
reasons:

- **Prove the benchmark on a board we know.** The Genesys 2 already runs
  `stream` at 8 channels with the same host stack, harness CSR, observers,
  LFSR source and CRC sink. Doing the benchmark here first proves the
  harness, the host programs, the sequence files and the sim harness while
  the Quartus tools are being brought up, so the DE10 port is a fabric and
  a board swap, not a first bring-up.
- **Compare against Xilinx's own fabric IP.** The same runs on Kintex-7
  give a second vendor comparison next to the Intel one.

**The benchmark itself is the DE10 PRD's**:
[DE10-Standard fabric benchmark PRD](../../DE10-Standard/fabric-benchmark/PRD.md)
§4 (runs, fabric-only mode, metrics, methodology) and §5 (system address
map, control path, data path, measurement points). This document carries
only what differs on the Genesys 2. Where the two disagree, the DE10 PRD
owns the method and this one owns the board facts.

## 2. Legs

| Leg | Data fabric under test | Source |
| --- | --- | --- |
| **A — bridge** | the bridge generator's AXI4 crossbar | `projects/components/fabric-gen-ip/bridge/bin/bridge_generator.py`, TOML in this area |
| **B1 — Xilinx AXI Crossbar** | `axi_crossbar_v2_1` (the crossbar inside AXI Interconnect), full crossbar, shared-address multiple-data | Vivado 2025.1 IP catalog; HDL ships unencrypted, so it runs in the Verilator sim harness. The wrapper's parameters equal the IP-catalog customization's (`bin/check_xbar_params.py`) |
| **B2 — Xilinx SmartConnect** | `smartconnect_v1_0` | Vivado 2025.1 IP integrator block design `fb_sc`, built by `fpga/tcl/vendor_ip.tcl` from the same TOML. Encrypted: board-only, no Verilator sim (§5) |

The matching rule is the DE10 PRD's §3 rule applied per pair: Leg A's TOML
mirrors the vendor fabric's configuration (port count, data width, ID
width, address map, outstanding depth), and Leg A is never configured
wider or deeper than the vendor fabric it is compared with. Where the two
Xilinx IPs expose different knobs, Leg A carries one TOML per comparison
rather than one compromise.

### Figure 2.1: Legs on the Genesys 2 (planned)

![Legs on the Genesys 2 (planned)](docs/assets/graphviz/k7_legs.png)

**Source:** [k7_legs.dot](docs/assets/graphviz/k7_legs.dot)

## 3. What differs from the DE10

| Item | DE10-Standard | Genesys 2 | Why it is still the same benchmark |
| --- | --- | --- | --- |
| Device / tools | Cyclone V 5CSX, Quartus 24.1 std | xc7k325tffg900-2, Vivado 2025.1 | per-board facts; legs are compared within one board, never across |
| Host control path | JTAG to Avalon Master Bridge → `avmm_to_axil4` | UART → `uart_axil_bridge` (the Genesys 2 STREAM front end) | both present the same AXI4-Lite master to the same generated configuration bridge; the host reaches registers by name either way |
| Memory controller | HPS hard DDR3 controller through f2sdram (AXI-3) | LiteDRAM DDR3 (`fb_litedram`: K7DDRPHY, DDR3-800), AXI4 slave port | held constant across legs on each board; LiteDRAM's port is AXI4, so the Genesys 2 has **no** AXI3 edge and no `axi4_to_axi3` |
| DDR3 | 1 GB, 32-bit | 1 GB, 2 × MT41J256M16, 32-bit; DDR3-800 proven by the LiteDRAM memtest (`Genesys2/mem-ctrl-ip/scoria/build-litedram/results/`) | same address window (Table 5.1, `0x0000_0000`, 1 GB) |
| Fabric data width | mixed (descriptor master 256-bit) | **128-bit on every port** | the Xilinx AXI Crossbar has one data width for all ports, so the descriptor master's 256→128 conversion sits **outside** every fabric (`axi4_dwidth_converter_rd`), same RTL all legs — the same rule that keeps `axi4_to_axi3` outside the fabric on the DE10 |
| Board clocks | 50 MHz | 200 MHz differential; fabric clock from the MMCM as in the STREAM build | one fabric clock, same frequency all legs |

Everything else is the DE10 PRD's held-constant list unchanged: `stream`
(`stream_top_ch8`, the Genesys 2 configuration from `stream_cfg_pkg`),
`desc_ram`, the LFSR source and CRC sink behind their CDC crossings, the
W3 injector (`char_engine_block`), the observers at the same probe points,
the same sequence files and the same seeds in every leg.

## 4. The fabric port set (all legs)

Every leg presents exactly this port set to the harness; the harness does
not know which fabric it holds.

| Port | Role | Direction | Width | Behind it |
| --- | --- | --- | ---: | --- |
| M0 | `stream` descriptor fetch | rd | 128 | `stream` m_axi_desc (256) → `axi4_dwidth_converter_rd` (outside the fabric) |
| M1 | `stream` data read | rd | 128 | `stream` m_axi_rd |
| M2 | `stream` data write | wr | 128 | `stream` m_axi_wr |
| M3 | W3 injector | wr | 128 | `char_engine_block` (contention run only) |
| S0 | DDR3 `0x0000_0000`, 1 GB | rd/wr | 128 | `fb_litedram` AXI4 user port, 128-bit, ID 10 (its own width conversion to the 256-bit native port is the controller's and identical all legs) |
| S1 | `desc_ram` read port `0x8000_0000` | rd | 128 | `sdpram_slave_axi4_axi4` |
| S2 | LFSR source `0x9000_0000` | rd | 128 | `axi4_cdc_rd` → LFSR source |
| S3 | CRC sink `0xA000_0000` | wr | 128 | `axi4_cdc_wr` → CRC sink |

AXI4, ID width 8 at every master. The port set carries no USER and no
REGION. The LFSR source and CRC sink bin channels on the **address**:
channel N owns the 32 MB window at its endpoint's base + N x 32 MB
(`fb_harness` sets `fb_endpoints` `CH_SEL_ADDR`=1, `CH_ADDR_LSB`=25; 32 MB
holds the largest chain the host builds, 16 descriptors x 1 MB), and the
host places each channel's buffers in its own window
(`DescriptorBuilder(channel_stride=32 MB)`). Nothing downstream of the fabric
depends on the slave-side ID, because SmartConnect delivers none (§5.1).
Leg B1 presents `{master slot, master ID}` (10 bits) at its slaves. Leg A
presents `{master slot, remap slot}` (2 + 4 bits, zero-extended to 10): the
bridge remaps a master ID wider than `$clog2(max_outstanding)` to a slot
(bridge TASK-018), and the leg A wrapper sizes the ports explicitly from
`bridge_fb_data_pkg::XBAR_ID_WIDTH`. The fabric test checks the layout of
its leg at every slave handshake; B2 presents 0.

Descriptors at 128 bits: the scheduler's descriptor is 256 bits and
`m_axi_desc` stays 256-bit, so the converter splits each one-beat fetch into
two 128-bit beats and reassembles the 256-bit beat for `stream`. The
converter splits on ARSIZE, which the descriptor engine drove as 64 bytes
on a 32-byte bus until `e236d102e` (2026-09-26); with that fixed, the K0
sim checks descriptor contents end to end through the converter and the
fabric. The configuration region (`0xF000_0000`) is the DE10 PRD's
Table 5.1 unchanged; it is decoded by the generated configuration bridge,
which is not the fabric under test.

## 5. Simulation before silicon

The house rule holds per leg: the sim harness runs the same harness RTL,
the same generated regmaps and the same host programs (over
`UARTAxiBridge(channel=...)`) as the board, at the board's configuration.

- Leg A: generated RTL, Verilator.
- Leg B1: `axi_crossbar_v2_1` plus its `axi_infrastructure`,
  `axi_register_slice` and `axi_data_fifo` dependencies from the Vivado
  install, Verilator. Configured from the same parameter set the Vivado IP
  customization produces (one source: the IP's `.xci` parameters are
  generated from the leg's config file, and the sim reads the same file).
- Leg B2: **board-only.** SmartConnect's HDL is encrypted (`pragma protect`
  in every `sc_*` sub-IP), and so is the post-synthesis functional netlist
  `write_verilog -mode funcsim` produces, so there is nothing Verilator can
  read. B2 runs the same host programs on the board; the fabric test's
  checks (data, DECERR, IDs at the slaves) are made there through the
  harness. Vivado's own simulator could run it, but not the cocotb harness.
- DDR3: the controller is not simulated (LiteDRAM's core is Xilinx-primitive Verilog with a CPU and BIOS). The sim harness models S0 with
  an AXI4 memory slave of the same width and ID width; DDR3 timing is
  measured on the board, and fabric-only mode (W2) needs no DDR3 at all.

### 5.1 SmartConnect at the slave ports

SmartConnect presents **no ID** to its slaves: the ID width of every MI port
is 0 and read-only. It expects in-order slaves and returns each response to
the master's own ID itself. So the per-channel CRC cannot key on the ID in
this leg, and the endpoints take the channel from the address in **every**
leg (§4) -- the endpoints stay identical across the legs, and SmartConnect
is configured with no AxUSER, so it carries nothing the other legs do not.

(A first version carried `{slot, id}` on AxUSER and rebuilt the slave-side
ID from it. It worked, but it added 10 bits per request that only B2
carried; dropping it took B2 from 8,438 to 8,333 LUTs, 4,064 to 3,959
LUTRAM and 11,938 to 11,616 flops.)

The in-order requirement holds: with ID 0 on every request, the controller at S0 must
answer in order by the AXI rules for a single ID, and S1-S3 are in order.

## 6. Milestones

**Status (2026-10-16):** K0-K4 done. K0 in sim on legs A and B1; K1/K2 on the board -- W2, all three legs; K3 on the board on all three legs -- the DDR3 chain (W1-F2, W1-F1, W4) 144/144 steps on the LiteDRAM controller, W3 contention 24/24 points; K4 -- the v1 sweep x5 (45/45 sweeps pass) and the analysis, §8.

- K0: `rtl/fb_harness.sv` (`dv/tests/test_fb_harness.py`) is the harness of
  §4. The Genesys 2 STREAM characterization runner drives it unchanged over
  the sim UART -- the configuration bridge keeps the STREAM harness's
  offsets -- given only a `DescriptorBuilder` for the fabric's map
  (descriptors preloaded at 0x0002_0000, fetched at 0x8000_0000; per-channel
  32 MB windows). func on both legs: 1ch x 1 x 4 KB, 4ch x 2 x 8 KB,
  8ch x 2 x 8 KB all pass with the on-chip PASS and every active channel
  in the CRC valid and match masks; datapath utilization from the
  master-side observer 79.5 / 98.4 / 99.2 % (A) and 80.0 / 98.5 / 99.2 % (B1).
  The slave-side observer (`u_slv_observer`, S2 reads / S3 writes, bus
  meter only, sharing the master observer's window) reads the same
  utilization as the master side in sim on both legs, which the TB asserts;
  the W3 injector on M3 is idle until K3.

- All three data fabrics exist, every one from
  `rtl/bridges/configs/bridge_fb_data.toml` and its connectivity CSV
  (`bin/regen.sh`): Leg A (bridge generator), Leg B1 (AXI Crossbar HDL
  wrapper), Leg B2 (SmartConnect block design, `make vendor-ip`). A and B1
  pass the same fabric test (`dv/tests/test_fb_fabric.py`); B2 is board-only
  (§5).
- `make check-xbar` proves B1's wrapper passes exactly the 29 parameters the
  IP-catalog customization of the same TOML produces.
- First size and timing comparison, every leg alone out of context on the
  board's part: [reports/ooc/README.md](reports/ooc/README.md) (`make ooc-all`).
  At the 100 MHz board clock all three close; at a 4 ns target B1 and B2
  close (est. Fmax ~256 and ~268 MHz) and Leg A misses by 1 ps (-0.001 ns,
  ~250 MHz on 2026-10-22, a 7-level path through a master's ID remap into a
  slave's AW stage; ~179 MHz on 2026-10-16, ~148 MHz / 15 levels before the
  registered CAM insert and free, ~186 MHz / 12 levels before GitHub #119 L1
  -- §8). Leg A is ~3.9x B1's LUTs; B2 is ~3.1x B1's LUTs plus
  3,959 LUTRAM and ~5.3x its flops.
- S0's DDR3 controller is LiteDRAM, generated (`fb_litedram`,
  `rtl/litedram/fb_litedram.yml`, `bin/gen_litedram.sh`; the core is
  toolchain output and gitignored, its port blackbox is tracked): the
  board-proven LiteDRAM memtest configuration (K7DDRPHY, DDR3-800 at 1:4,
  its VexRiscv BIOS calibrating the PHY at boot) with a 128-bit, ID-10 AXI4
  port. Its `user_clk` is the 100 MHz fabric clock, so S0 needs no clock
  crossing. It replaced MIG 7-series on 2026-10-16 (owner decision): MIG
  calibrated on this board but its read path returned no data (K3 below).

- K1/K2 board: `rtl/fb_genesys2_top.sv` -- the DDR3 controller at S0 (its
  100 MHz user clock is `aclk`), `ep_clk` 125 MHz from a second MMCM on
  `aclk`, LEDs from
  `led_status_driver` -- built per leg by `build-{a,b1,b2}/` (`make
  bitstream`, `make program`). Post-route, every leg meets timing:

  | Leg | WNS (ns) | WHS (ns) | LUTs | FFs | BRAM | DSP |
  | --- | ---: | ---: | ---: | ---: | ---: | ---: |
  | A (bridge) | +0.138 | +0.052 | 101,429 | 71,094 | 43.5 | 68 |
  | B1 (AXI Crossbar) | +0.360 | +0.052 | 97,482 | 68,072 | 43.5 | 68 |
  | B2 (SmartConnect) | +0.083 | +0.050 | 102,409 | 75,139 | 43.5 | 68 |

  (The LiteDRAM builds of 2026-10-16, which also carry `fb_ctl`. The
  2026-10-15 MIG builds, without `fb_ctl`, closed at +0.273 / +0.006 /
  +0.201 ns; W2 measured within 0.5% on both.)

  The harness around the fabric is the same in every leg, so these totals
  differ by the fabric alone (the OOC figures above isolate it).

  W2 headline sweep (`bin/fb_char.py --leg X`, 4 descriptors per channel,
  bus throughput from the on-chip timer; peak = 128 bit x 100 MHz one
  direction = 1525.9 MiB/s, which W2 can reach because reads and writes go
  to separate endpoints). Per-leg CSVs: `reports/board/w2_<leg>_*.csv`.

  | Bytes/desc | Ch | A MiB/s (% peak) | B1 MiB/s (% peak) | B2 MiB/s (% peak) |
  | --- | ---: | ---: | ---: | ---: |
  | 4 KB | 1 | 1421.7 (93.2) | 1419.2 (93.0) | 1363.4 (89.4) |
  | 4 KB | 8 | 1511.3 (99.0) | 1512.2 (99.1) | 1502.2 (98.4) |
  | 64 KB | 1 | 1518.7 (99.5) | 1518.7 (99.5) | 1514.5 (99.3) |
  | 64 KB | 8 | 1525.0 (99.9) | 1525.0 (99.9) | 1524.4 (99.9) |
  | 1 MB | 1 | 1525.4 (100.0) | 1525.4 (100.0) | 1525.1 (100.0) |
  | 1 MB | 8 | 1525.8 (100.0) | 1525.8 (100.0) | 1525.8 (100.0) |

  Every run passes with the on-chip verdict and every active channel in the
  CRC valid and match masks, and on every run with a valid window the
  slave-side utilization equals the master-side to the fourth place: with
  one STREAM master and ID 0 the fabric adds no bubbles in steady state, and
  what separates the legs is the fixed per-descriptor latency, visible only
  at 4 KB (B2 takes 47-50 more cycles per run than A, e.g. 1146 vs 1099
  at 1 channel).

  On B2, 1-channel runs report no utilization. STREAM's perf window
  measures data movement only, by design -- a descriptor fetch is not
  activity. It opens on the scheduler's first non-idle cycle (the kick) and
  closes after 16 quiet cycles; on B2 at 1 channel the descriptor fetch
  through SmartConnect is longer than that, so the window closes at cycle
  ~31, before the first data beat, and the run's data is not in it.
  `fb_char` flags those rows; throughput (on-chip timer) and CRC are
  unaffected. Left as is (owner decision 2026-10-16); opening the window on
  the first data beat would fit the data-only rule, but it is a
  `stream_core` change and moves STREAM's own board measurements.

- K3 (done): the DDR3 workloads run as one
  CRC-checked chain (`bin/fb_workloads.py`, the same code in sim and on the
  board): W1-F2 fills DDR3 region A from the LFSR source; W1-F1 drains A
  into the CRC sink, whose per-channel CRC must equal the fill's LFSR CRC;
  W4 copies A to region B; a second drain checks B the same way. `fb_ctl`
  (`rtl/regs/fb_ctl_regs.rdl`, config window 0x0020_0000) points the run
  timer at the endpoints a step uses (WORKLOAD), counts S0 handshakes and
  beats, and reports the DDR3 controller's calibration and the S0
  handshake levels live (STATUS). The chain passes in sim on legs A and B1
  (func), and on the board on LiteDRAM, 144/144 steps on all three legs
  (`fb_char.py --leg X --chain`, 1/2/4/8 channels x 4 KB/64 KB/1 MB):
  every drain reproduces the fill's per-channel LFSR CRC, including after
  the copy, and every S0 count is exact.

  **W1 and W4 are integrity checks, not bandwidth measurements** (owner
  decision 2026-10-16). With DDR3 in the path the three legs measured
  identically, all at 7-26% of the path peak that W2 reaches through the
  same fabrics: S0's controller (LiteDRAM's AXI port), not the fabric,
  sets the rate, so a W1/W4 bandwidth figure would describe LiteDRAM and
  nothing about the legs. The fabric comparison is W2's; W3 measures how
  each fabric shares one slow slave between two masters, which does not
  need S0 to be fast. `fb_char --chain` reports pass/fail and the S0 counts
  only.

  MIG 7-series was the first S0 controller. It calibrated and completed
  writes, but its read path usually returned no data: an ILA
  (`make bitstream-ila`, `make tcl-capture_ila`) showed read commands
  reaching its app interface and `app_rd_data_valid` never asserting, on
  legs A and B1 alike. Replaced by LiteDRAM 2026-10-16 (owner decision).

- W3 (contention, `bin/fb_w3.py`, `bin/fb_w3_char.py`): STREAM and the
  injector (`char_engine_block` on M3, config window 0x0021_0000) share S0.
  f3 = STREAM drains DDR3 while the injector writes another region; the
  mirror = STREAM fills DDR3 while the injector writes. Every point also
  ends in a CRC data check (f3 drains an uncontended fill; the mirror's
  contended fill is drained afterwards). The share is productive beats in
  one window -- STREAM's observer and the injector's own meter -- and
  `fb_ctl` WORKLOAD.INJ_SYNC lets the injector start bursts only while
  STREAM's window is open (the host's GO precedes the kick by tens of UART
  transactions, long enough for the injector to finish alone).

  The mix is set by the injector's gap (owner decision 2026-10-16). Two
  injector fixes came out of it (`2a0e1a465`): the 4-bit gap could not
  throttle the writer below what S0 absorbs (the split stayed 50/50 at
  every value), so the gap is now `gap << gap_shift` (up to 1920 idle
  cycles); and a gapped injector pipelined AWs ahead of its W data, which
  then waited out the gap at S0 and -- AXI4 W following AW order -- paced
  STREAM's writes to the injector's gap. Calibrated on leg A and held for
  every leg: 50/50 = idle 0; 90/10 = idle 1280 (f3) and 480 (mirror).

  Board, 24/24 points pass (CSVs `reports/board/w3_<leg>_*.csv`), injector
  share of S0 in STREAM's window (8 ch x 4 x 128 KB):

  | Flavor, offered mix, outstanding | A (bridge) | B1 (AXI Crossbar) | B2 (SmartConnect) |
  | --- | ---: | ---: | ---: |
  | f3, 50/50, 2 or 4 | 50.0% | 50.0% | 50.0% |
  | f3, 90/10, 2 or 4 | 10.1% | 10.1% | 10.1% |
  | mirror, 50/50, 2 | 50.0% (40.0% on 2026-10-16) | 50.0% | 11.1% |
  | mirror, 50/50, 4 | 50.0% | 50.0% | 20.0% |
  | mirror, 90/10, 2 | 12.5% (10.6% on 2026-10-16) | 11.9% | 11.1% |
  | mirror, 90/10, 4 | 12.5% (10.6% on 2026-10-16) | 11.9% | 13.4% |

  **f3 does not measure the fabric**: STREAM's reads and the injector's
  writes travel on different AXI channels, so no fabric arbitrates between
  them; the identical split on every leg is S0's controller alternating
  reads and writes. **The mirror is the fabric's arbitration** (two writers
  into one slave): B1 and A split evenly (A gave a 2-outstanding injector
  40% until the 2026-10-21 re-measurement, section 8.3); SmartConnect favours
  STREAM heavily when both offer full load (injector 11-20% where B1 gives
  50%). S0's total write rate is about the same on every leg (~365-375
  MiB/s), so the difference is who gets the slave, not how much it moves.

K4: §8 (owner decision 2026-10-16: a PRD section plus CSVs).

| K | Content | Gate |
| --- | --- | --- |
| K0 | Fabric-only mode (W2) in sim, Leg A: the harness with the port set of §4, S0 tied to a memory model, `CharacterizationRunner` driving it over the UART channel | sim green, CRC verdicts on every run |
| K1 | Leg B1 (AXI Crossbar) in the same sim; then both legs on the board, W2 headline sweep | same host program both legs, sim then board |
| K2 | Leg B2 (SmartConnect): IP integrator generation, sim decision, board W2 | as K1 |
| K3 | DDR3 at S0; W1-F1, W1-F2, W4, W3 on all legs | sim with the memory model, then board |
| K4 | Size and timing parses (Vivado utilization / timing reports), v1 sweep × 5, analysis section for the Kintex-7 legs | done: §8 |

The DE10 milestones resume after K1: the harness, host programs and
sequence files are then proven, and the DE10 work is the Quartus flow, the
JTAG front end and the Platform Designer leg.

## 7. Open questions

- *Closed 2026-10-16:* memory controller -- LiteDRAM (`fb_litedram`),
  owner decision after MIG's read path returned no data on this board
  (an ILA showed read commands reaching MIG's app interface and
  `app_rd_data_valid` never asserting). One controller, held constant
  across the legs.
- *Closed 2026-10-15:* board-clock plan -- the harness and fabric run on
  the DDR3 controller's 100 MHz user clock (MIG's `ui_clk`, LiteDRAM's
  `user_clk` since 2026-10-16); `ep_clk` (125 MHz) comes from a separate MMCM
  cascaded from it (`rtl/fb_genesys2_top.sv`). The two cross only
  through synchronizers, bounded by `set_max_delay -datapath_only` rather
  than clock groups so the Gray-pointer skew stays timed.
- *Closed 2026-10-15:* SmartConnect simulation -- board-only (§5).
- *Closed 2026-10-15:* per-channel CRC through a fabric -- A and B1 forward
  `{slot, id}` (checked at every slave handshake by the fabric test); B2
  delivers no ID, so the endpoints select channels by address in every leg
  (`CH_SEL_ADDR`, §4, §5.1).

## 8. Analysis -- the Kintex-7 legs (K4)

All figures are from the Genesys 2 at the 100 MHz fabric clock, the
2026-10-16 bitstreams of every leg, the same harness and the same host
programs; only the fabric instance differs. CSVs: `reports/k4/`
(`python3 bin/fb_k4.py size` / `aggregate --since 20261016_100000`), the
per-run files they summarize in `reports/board/`, and the fabric alone in
`reports/ooc/README.md` (`make ooc-all`).

### 8.1 Size and timing

The fabric alone, placed and routed out of context (`make ooc-all`; legs B1
and B2 2026-10-16, leg A re-run 2026-10-22):

| Leg | LUT | LUTRAM | FF | WNS at 10 ns | WNS at 4 ns | Fmax est. |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| A (bridge) | 8,449 | 0 | 6,722 | +3.889 | -0.001 | ~250 MHz |
| B1 (AXI Crossbar) | 2,688 | 10 | 2,190 | +4.658 | +0.088 | ~256 MHz |
| B2 (SmartConnect) | 8,333 | 3,959 | 11,616 | +4.286 | +0.268 | ~268 MHz |

The whole board design, post-route (B1 and B2 on 2026-10-16; leg A on 2026-10-16 and again on
2026-10-22, after the CAM removal (bridge W12) and the `bridge_id_remap` timing fix; harness, STREAM,
the injector and LiteDRAM are the same in every leg; the differences are the fabric's). The
2026-10-22 leg A passed W2 12/12 (`reports/board/w2_a_20261022_221321.csv`, every point within
0.3% of the 2026-10-16 run, 1,419-1,526 MB/s of 1,526 peak) and the DDR3 chain 48/48
(`k3_a_20261022_221403.csv`):

| Leg | WNS (ns) | WHS (ns) | LUTs | LUTRAM | FFs | BRAM | DSP |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| A (bridge), 2026-10-16 | +0.021 | +0.027 | 111,567 | 10,120 | 78,938 | 43.5 | 71 |
| A (bridge), rebuilt 2026-10-22 | +0.519 | +0.020 | 87,904 | 7,070 | 72,157 | 43.5 | 71 |
| B1 (AXI Crossbar) | +0.285 | +0.047 | 107,283 | 10,166 | 75,356 | 43.5 | 71 |
| B2 (SmartConnect) | +0.378 | +0.023 | 112,491 | 12,009 | 83,133 | 43.5 | 71 |

Leg A is the largest fabric in logic (3.1x B1's LUTs) and misses 4 ns by
1 ps; B2 spends about as many LUTs as A but adds 3,959 LUTRAM and the most
flops. Leg A's history at 4 ns: ~161 -> ~148 MHz (2026-10-15 to 10-16, the
port latency modes and outstanding limits, #119 L5/L7/L1b, put a 15-level
path into the DDR slave's write CAM count); ~165 -> ~179 MHz (registered CAM
insert and free); then bridge W12 removed the slave-side CAMs altogether
(responses route by the ID's master-index bits) and TASK-018 added the
per-master ID remap, which re-measured on 2026-10-22 at -0.189 ns, ~239 MHz,
8,253 LUTs, worst path 6 levels from a master's AR skid into its remap
table. Two edits to `bridge_id_remap` that day -- the table writes its
lowest free entry every cycle instead of decoding the request's slot, and
`req_ok` is one flat reduction over (hit and disagrees) -- took it to
-0.001 ns (~250 MHz). The worst path is now 7 levels: a master's AW skid,
the remap ID compare, `req_ok` into AW valid, and the slave's AW stage
enable.

Leg A on UltraScale+ (2026-10-23; `make ooc PART=xczu7ev-ffvc1156-2-e`,
the same script and RTL, reports under `reports/ooc/xczu7ev-ffvc1156-2-e/`):
it meets 2.7 ns at +0.060 ns and misses 2.5 ns by 0.190 ns, ~375 MHz, at
8,328 LUT cells (7,986 CLB LUTs) and 6,721 FFs. The worst path is again 7
levels, about 72% route: a master's AW skid into a crossbar AW slot enable
at 2.5 ns, the subtractive slave's W owner pointer into the injector's W
skid at 2.7 ns. Legs B1 and B2 were not run there -- their IP is generated
for the Genesys 2 part -- so this is leg A's ceiling on a faster family,
not a leg comparison.

### 8.2 W2 -- the fabric alone (5 runs per point)

MiB/s, mean (min-max) over 5 runs; peak 1525.9 MiB/s (128 bit x 100 MHz,
one direction). Every run passed its on-chip verdict and per-channel CRC.

| Point | A (bridge) | B1 (AXI Crossbar) | B2 (SmartConnect) |
| --- | ---: | ---: | ---: |
| 1 ch x 4 x 4 KB | 1416.6 (1415.3-1417.9) | 1420.7 (1416.6-1424.3) | 1358.5 (1355.2-1362.2) |
| 8 ch x 4 x 4 KB | 1512.1 (1511.7-1512.4) | 1511.6 (1511.1-1512.4) | 1503.2 (1502.8-1503.5) |
| 1 ch x 4 x 64 KB | 1518.8 (1518.6-1519.0) | 1518.9 (1518.6-1519.2) | 1514.3 (1514.0-1514.6) |
| 8 ch x 4 x 64 KB | 1525.0 (1524.9-1525.0) | 1525.0 (1525.0-1525.0) | 1524.4 (1524.4-1524.5) |
| 1 ch x 4 x 1 MB | 1525.4 (1525.4-1525.4) | 1525.4 (1525.4-1525.5) | 1525.2 (1525.1-1525.2) |
| 8 ch x 4 x 1 MB | 1525.8 (1525.8-1525.8) | 1525.8 (1525.8-1525.8) | 1525.8 (1525.8-1525.8) |

In steady state no fabric costs bandwidth: all three reach 100.0% of peak
at 1 MB, and slave-side utilization equals master-side on every run with
a measurement window. What separates them is the fixed cost per
descriptor, visible only at small transfers: A and B1 are within noise of
each other, and B2 is 4.1% slower at 1 channel x 4 KB (~50 cycles per
4-descriptor run, measured with the on-chip timer), which disappears once
several channels overlap or transfers grow -- consistent with a longer
per-request latency through SmartConnect. (Not instrumented further: B2
does not simulate, and its internals are encrypted.)

### 8.3 W3 -- two masters into one slave (5 runs per point)

Injector share of S0 in STREAM's window; identical to 0.1% across the 5
runs (min-max shown only where they differ). 50/50 = injector unthrottled;
90/10 = idle 1280 cycles (f3) / 480 (mirror) between its 16-beat bursts.

| Flavor, offered mix, outstanding | A (bridge) | B1 (AXI Crossbar) | B2 (SmartConnect) |
| --- | ---: | ---: | ---: |
| f3, 50/50, 2 or 4 | 50.0% | 50.0% | 50.0% |
| f3, 90/10, 2 or 4 | 10.1% | 10.1% | 10.1% |
| mirror, 50/50, 2 | 50.0% (40.0% on 2026-10-16) | 50.0% | 11.1% |
| mirror, 50/50, 4 | 50.0% | 50.0% | 20.0% |
| mirror, 90/10, 2 | 12.5% (10.6% on 2026-10-16) | 11.8% (11.8-11.9) | 11.1% |
| mirror, 90/10, 4 | 12.5% (10.6% on 2026-10-16) | 11.8% (11.8-11.9) | 13.4% |

f3 is the controller's split, not the fabric's: STREAM's reads and the
injector's writes travel on different AXI channels, so no fabric
arbitrates between them. The mirror -- two writers into one slave -- is
the fabric's arbitration, and the outcome is deterministic per leg:

- B1 splits a contended slave evenly regardless of outstanding.
- A splits evenly at either limit. On 2026-10-16 it gave a 2-outstanding
  injector 40%. Root cause, bisected on the board (leg A rebuilt from each
  commit's own tree, same LiteDRAM, `mirror` at 2 outstanding: 4fc23c275
  40.0%, c98ed071e 40.0%, 73467609f 50.0%, 77ae05054 50.0%, ecebdada5
  50.0%, HEAD 50.0%): the bridge's shared-slave arbiter picked from the raw
  master requests into a 2-deep AW stage (the DDR adapter's AW skid) ahead of
  the slave. LiteDRAM holds AWREADY until that burst's W is buffered, so
  the stage sat full of AWs that had already won. Arbitration therefore
  happened when a stage slot freed, and STREAM, whose 8 channels always
  have an AW waiting, took every slot that freed while the injector was
  between bursts waiting for a B. The injector's share followed its
  outstanding count, not the round-robin. Bridge commit 73467609f
  (2026-10-17) moved the pick to the slave pins from per-master request
  slots with nothing queued past it (the DDR adapter's AW stage is depth
  0), which is also how the AXI Crossbar is built here (no register
  slices). It was measured in the bridge's own perf suite at the time
  (share 0.34 -> 0.50) but this benchmark was not re-run until 2026-10-21
  (`reports/board/w3_a_20261021_175411.csv`: 50.0%, five identical runs, and
  again after bridge BUG-023). Simulation cannot show the effect with the
  BFM S0, which accepts AW without waiting for W.
- B2 favours STREAM heavily under full load: the injector gets 11-20%
  where B1 gives it 50%. Total S0 write throughput is about the same on
  every leg (~365-375 MiB/s), so this is who gets the slave, not how much
  it moves.

### 8.4 W1 and W4

Integrity checks only (§6, K3): 144/144 chain steps pass on every leg, but
their rates are LiteDRAM's (7-26% of peak, identical across legs) and say
nothing about the fabrics.

### 8.5 Summary

| | A (bridge) | B1 (AXI Crossbar) | B2 (SmartConnect) |
| --- | --- | --- | --- |
| Steady-state bandwidth | 100% of peak | 100% of peak | 100% of peak |
| Small-transfer cost | baseline | = A | 4.1% slower at 1 ch x 4 KB |
| Contended-slave fairness | even (40/60 at 2 outstanding before 2026-10-21) | even | biased to STREAM (11-20%) |
| Size (fabric, OOC) | 8.4k LUT, 6.7k FF | 2.7k LUT, 2.2k FF | 8.3k LUT, 4.0k LUTRAM, 11.6k FF |
| Fmax est. (fabric, OOC) | ~250 MHz | ~256 MHz | ~268 MHz |
| Simulatable | yes | yes | no (encrypted) |

On this port set and clock, the generated bridge matches the Xilinx
crossbar on bandwidth and per-transfer latency, is fairer than
SmartConnect under contention, and costs about 3.1x B1's logic at nearly
the same Fmax (~250 vs ~256 MHz). The paths found here went back to the
bridge: the registered CAM insert and free, then the ID remap edits (~179
-> ~250 MHz). The logic gap is mostly the bridge's default of registering
every channel at both ends of every port, which B1 here does not do (no
register slices), plus the remap tables.
