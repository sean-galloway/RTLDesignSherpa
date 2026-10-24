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
| **A2 — bridge, `preset = "xbar"`** | the same generator and TOML with the one-key plain-crossbar preset: no registered stage at any port, no rate buffer, no ID remap (added 2026-10-23) | `bin/regen.sh` derives `rtl/bridges/generated/derived/bridge_fb_data_plain.toml` from leg A's TOML by adding that one key; nothing else differs |
| **B1 — Xilinx AXI Crossbar** | `axi_crossbar_v2_1` (the crossbar inside AXI Interconnect), full crossbar, shared-address multiple-data | Vivado 2025.1 IP catalog; HDL ships unencrypted, so it runs in the Verilator sim harness. The wrapper's parameters equal the IP-catalog customization's (`bin/check_xbar_params.py`) |
| **B2 — Xilinx SmartConnect** | `smartconnect_v1_0` | Vivado 2025.1 IP integrator block design `fb_sc`, built by `fpga/tcl/vendor_ip.tcl` from the same TOML. Encrypted: board-only, no Verilator sim (§5) |
| **C1 — Forencich `axi_crossbar`** | `verilog-axi` `axi_crossbar` (MIT), the most widely used open-source AXI4 crossbar (added 2026-10-23) | vendored at `vendor/verilog-axi` (commit `516bd5d`, upstream's last; its successor `taxi` is CERN-OHL-S, which cannot be vendored into this MIT repo). Wrapper generated from the same TOML |
| **C2 — PULP `axi_xbar`** | pulp-platform `axi` v0.39.11 `axi_xbar` (Solderpad 0.51) | vendored at `vendor/pulp-axi` + `vendor/pulp-common_cells` (1.39.0, the version its `Bender.yml` pins). Wrapper generated from the same TOML |
| **C3 — LiteX AXI crossbar** | LiteX 2026.8 `AXIDecoder` + `AXIArbiter`, built as `AXICrossbar` builds them, with the connectivity applied | `bin/gen_litex_xbar.py` converts it to Verilog from the same TOML (`rtl/generated/fb_litex_xbar/`, tracked so the sim needs no LiteX) |

The matching rule is the DE10 PRD's §3 rule applied per pair: Leg A's TOML
mirrors the vendor fabric's configuration (port count, data width, ID
width, address map, outstanding depth), and Leg A is never configured
wider or deeper than the vendor fabric it is compared with. Where the two
Xilinx IPs expose different knobs, Leg A carries one TOML per comparison
rather than one compromise.

The open-source legs are configured by the same rule, to the limits the
bridge and B1 use: 16 outstanding per master and per slave, no register
slices or spill registers (Forencich's upstream defaults register B and R at
the ports facing the masters and AW, W and AR at the ports facing the
slaves; PULP's examples use `CUT_ALL_AX`), round-robin,
AXI4 without atomics. Where a fabric tracks IDs it is sized for the eight
IDs STREAM issues (ID = channel): Forencich `S_THREADS = 8`, PULP
`AxiIdUsedSlvPorts = 3`. LiteX has no such knob. Two of LiteX's behaviours
differ from every other leg and are design, not configuration: its slaves
see the master's own ID with no slot bits, and an unmapped or unconnected
command is never accepted (there is no error slave). The fabric test checks
both as such (`dv/tests/test_fb_fabric.py`, `LEG_BEHAVIOUR`).

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
`bridge_fb_data_pkg::XBAR_ID_WIDTH`. Leg A2 presents `{master slot, master
ID}` (10 bits), as B1 does: with `id_remap` off the bridge forwards the whole
ID. The fabric test checks the layout of its leg at every slave handshake;
B2 presents 0.

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

- Legs A and A2: generated RTL, Verilator.
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
carried; dropping it took B2 from 8,438 to 8,333 LUTs and 11,938 to 11,616
flops.)

The in-order requirement holds: with ID 0 on every request, the controller at S0 must
answer in order by the AXI rules for a single ID, and S1-S3 are in order.

## 6. Milestones

**Status (2026-10-23):** seven legs (A, A2, B1, B2, C1, C2, C3) measured on the board from one tree, with latency; §8. **Status (2026-10-16):** K0-K4 done. K0 in sim on legs A and B1; K1/K2 on the board -- W2, all three legs; K3 on the board on all three legs -- the DDR3 chain (W1-F2, W1-F1, W4) 144/144 steps on the LiteDRAM controller, W3 contention 24/24 points; K4 -- the v1 sweep x5 (45/45 sweeps pass) and the analysis, §8.

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
  1,428 LUTs of distributed RAM and 755 of shift register, and ~5.3x its
  flops.
- Leg A2 (2026-10-23): leg A with `preset = "xbar"`, to test whether that
  size gap is the bridge or its defaults. Sim (fabric and harness tests) and
  the board (W2 x5 60/60, the DDR3 chain 48/48, W3 x5 40/40) pass; out of
  context it is 1.07x B1's LUTs and 0.51x its flops at ~254 MHz, and the
  whole board design is the smallest of the four legs (§8).
- Legs C1-C3 (2026-10-23): the Forencich, PULP and LiteX crossbars (§2),
  each from the same TOML. Sim: the fabric and harness tests pass on all
  three (16/16 in the suite, `make sim`); C3's gap-0 mirror point is an
  expected starvation, checked as such (§8.3). Board: W2 x3 36/36 and W3
  f3 x3 12/12 on each; the DDR3 chain 48/48 on each (on the bitstreams
  before the two injector fixes below, which do not touch the chain's
  path). W3 mirror x3 12/12 on C1 and C2; 6/12 on C3, the six gap-0 points
  by design (§8.3).
- Two harness bugs found by C1 and C3, both in the injector's
  window gating (`rtl/fb_harness.sv`), fixed 2026-10-23 and every leg
  rebuilt and re-measured: W was released for bursts whose AW was held at
  the window's close, which a fabric that forwards W ahead of AW (C3)
  delivered to S0 as orphan data; and the AW hold dropped AWVALID without a
  handshake, which a fabric that decodes on AWVALID (C1) turned into an AW
  at S0 with no W. Neither moved any earlier figure of legs A-B2 (§8.3).
- Latency (2026-10-23): the board figures now carry the master-side
  observer's latency histograms (`bin/fb_latency.py`), and the sim harness
  measures exact per-transaction latency on the same port (`FB_LAT=1`,
  `dv/tbclasses/fb_latency_mon.py`); §8.2.
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

All figures are from the Genesys 2 at the 100 MHz fabric clock, the same
harness and the same host programs; only the fabric instance differs. The
board figures of 8.1-8.3 are the 2026-10-23 bitstreams of all seven legs,
built from one tree (13:41, after the two injector fixes of §6) and run
2026-10-23 13:46-15:10: W2 and W3 three times per leg (A2's W2 six times,
its mirror once -- below). CSVs: `reports/k4/`
(`python3 bin/fb_k4.py size` / `aggregate --since 20261023_134600 --tag
20261023_lat`), the per-run files they summarize in `reports/board/`, and
the fabric alone in `reports/ooc/README.md` (`make ooc-all`). The
2026-10-16 K4 sweep (legs A, B1, B2, 5 runs) is in `reports/k4/w2_summary.csv`
and `w3_summary.csv`; every leg's 10-23 figure reproduces its 10-16 one to
0.4% or better.

A board run that lost the UART partway is not a measurement: another
session reprogrammed the board twice during the 10-23 runs (programming
takes the board lock; these host programs do not hold it between steps).
Both times it landed in leg A2: the first cut A2's second mirror run short
(that run is left out), the second took the board before A2's second W3
pass started (no data). A2's W2 is the six runs before either; its W3 is
f3 x3 and mirror x1.

### 8.1 Size and timing

The fabric alone, placed and routed out of context (`make ooc-all`; legs B1
and B2 2026-10-16, leg A re-run 2026-10-22, A2 and C1-C3 2026-10-23; A, B1,
B2 rebuilt 2026-10-23 for the LUTRAM count, timing and every other count
unchanged):

| Leg | LUT | LUTRAM | SRL | FF | WNS at 10 ns | WNS at 4 ns | Fmax est. |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| A (bridge) | 8,449 | 0 | 0 | 6,722 | +3.889 | -0.001 | ~250 MHz |
| A2 (bridge, `preset = "xbar"`) | 2,861 | 0 | 0 | 1,117 | +4.781 | +0.068 | ~254 MHz |
| B1 (AXI Crossbar) | 2,688 | 0 | 10 | 2,190 | +4.658 | +0.088 | ~256 MHz |
| B2 (SmartConnect) | 8,333 | 1,428 | 755 | 11,616 | +4.286 | +0.268 | ~268 MHz |
| C1 (Forencich `axi_crossbar`) | 2,336 | 0 | 0 | 1,606 | +4.444 | -0.250 | ~235 MHz |
| C2 (PULP `axi_xbar`) | 3,090 | 0 | 0 | 1,072 | +4.313 | -0.038 | ~248 MHz |
| C3 (LiteX AXI crossbar) | 731 | 0 | 0 | 59 | +6.509 | +0.926 | ~402 MHz (2.5 ns: +0.012) |

LUT and FF are primitive cells; LUTRAM (distributed RAM) and SRL (shift
register) are LUTs, from Vivado's utilization report. Before 2026-10-23
this table's LUTRAM column was a primitive-cell count of both together
(B1 10, B2 3,959) -- one RAM32M is four LUTs but eight cells -- which
overstated B2's memory LUTs ~1.8x and called B1's 10 shift registers
LUTRAM. Fmax est. is 1000 / (period - WNS) at the tightest period run.

The open-source legs: C1's worst path (9 levels) is its read address
decoder's per-thread ID compare into a thread count enable -- the
`S_THREADS = 8` per-ID thread tracking. C2's (10 levels)
is the AW demux's per-ID in-flight counter into its open-W counter. C3 is
a different kind of fabric: 731 LUTs and 59 flops, because it keeps almost
no state -- one arbiter per slave that holds its grant while the granted
master has anything outstanding, request counters, and no ID tracking,
no ID slot bits and no error slave (§2); its worst path is a request
counter's own increment.

The whole board design, post-route: all seven legs built 2026-10-23 13:41
from one tree (`reports/k4/board_size_timing.csv`; harness, STREAM, the
injector and LiteDRAM are the same in every leg, so the differences are the
fabric's):

| Leg | WNS (ns) | WHS (ns) | LUTs | LUT as memory | FFs | BRAM | DSP |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| A (bridge) | +0.591 | +0.042 | 87,964 | 7,070 | 72,163 | 43.5 | 71 |
| A2 (bridge, `preset = "xbar"`) | +0.381 | +0.044 | 84,498 | 7,080 | 67,689 | 43.5 | 71 |
| B1 (AXI Crossbar) | +0.326 | +0.029 | 84,629 | 7,092 | 68,757 | 43.5 | 71 |
| B2 (SmartConnect) | +0.575 | +0.050 | 89,823 | 8,935 | 76,535 | 43.5 | 71 |
| C1 (Forencich) | +0.298 | +0.033 | 84,099 | 7,082 | 67,996 | 43.5 | 71 |
| C2 (PULP) | +0.473 | +0.040 | 84,921 | 7,084 | 67,738 | 43.5 | 71 |
| C3 (LiteX) | +0.672 | +0.023 | 82,985 | 7,062 | 66,763 | 43.5 | 71 |

Board totals from different days are not comparable: B1 and B2 were 107,283
and 112,491 LUTs on 2026-10-16 (leg A 111,567), and B1 and B2 each dropped
~22,700 LUTs since with no change to their fabrics -- harness and STREAM
changes outside the fabric. The 10-23 13:41 builds differ from that
morning's by the two injector fixes (+19 to +60 LUTs per leg).

Leg A is the largest fabric in logic (3.1x B1's LUTs) and misses 4 ns by
1 ps; B2 spends about as many LUTs as A but adds 2,183 memory LUTs (1,428
distributed RAM, 755 shift register) and the most
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

Leg A2 is that bridge without its defaults' cost: 2,861 LUT cells (2,406
Slice LUTs against B1's 2,267) and 1,117 FFs, 1.07x B1's LUTs and 0.51x its
flops, +0.068 ns at 4 ns (~254 MHz). Its worst path is 9 levels, 81% route,
from a write master's W-tracking pointer into another write master's per-ID
count. Its only buffers are the internal unmapped-address slave's, off the
data path. Against the two general-purpose open-source crossbars it is
0.93x C2's LUTs at 1.04x its flops, and 1.22x C1's LUTs at 0.70x its flops,
and it closes 4 ns where both miss it.

UltraScale+ (2026-10-23; `make ooc PART=xczu7ev-ffvc1156-2-e`, the same
script and RTL, reports under `reports/ooc/xczu7ev-ffvc1156-2-e/`). Legs B1
and B2 were not run there -- their IP is generated for the Genesys 2 part --
so this compares the RTL legs only:

| Leg | Tightest met (WNS) | Tightest run (WNS) | Fmax est. | LUT cells | FF |
| --- | ---: | ---: | ---: | ---: | ---: |
| A (bridge) | 2.7 ns (+0.060) | 2.5 ns (-0.190) | ~372 MHz | 8,331 | 6,722 |
| A2 (`preset = "xbar"`) | 2.35 ns (+0.129) | 2.0 ns (-0.410) | ~415 MHz | 2,616 | 1,117 |
| C1 (Forencich) | 2.5 ns (+0.027) | 2.2 ns (-0.197) | ~418 MHz | 2,319 | 1,604 |
| C2 (PULP) | 2.5 ns (+0.168) | 2.0 ns (-0.194) | ~456 MHz | 2,998 | 1,075 |
| C3 (LiteX) | 1.4 ns (+0.099) | 1.4 ns (+0.099) | >= ~769 MHz | 731 | 58 |

Leg A's worst path there is again 7 levels, about 72% route: a master's AW
skid into a crossbar AW slot enable at 2.5 ns, the subtractive slave's W
owner pointer into the injector's W skid at 2.7 ns. (A2 was reported as
~425-450 MHz before this table: that bracketed its met and missed periods;
the column here is the one formula on the tightest run for every leg.) C3
was not pushed past 1.4 ns, so its figure is a floor.

These estimates move by 6-8% with the target period, because Vivado's
slack depends on the target it is given. A2 and C2 show it:
- From the tightest run, C2 looks faster: ~456 vs ~415 MHz, both at 2.0 ns.
- From the tightest period each one met, A2 is faster. It met 2.35 ns
  (+0.129, ~450 MHz), a tighter period than C2's 2.5 ns (+0.168, ~429 MHz).
Neither ordering holds, so read the two as level. The same caution applies
on Kintex-7, where every leg but C3 lands within 235-268 MHz at 4.0 ns.

### 8.2 W2 -- the fabric alone

MiB/s, mean over 3 runs (A2 6); peak 1525.9 MiB/s (128 bit x 100 MHz, one
direction). Every run passed its on-chip verdict and per-channel CRC. The
runs agree to 0.3% or better except at 1 ch x 4 KB (ranges in
`reports/k4/w2_summary_20261023_lat.csv`).

| Point | A | A2 | B1 | B2 | C1 | C2 | C3 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 ch x 4 x 4 KB | 1421.3 | 1435.9 | 1421.7 | 1361.1 | 1347.0 | 1437.0 | 1437.9 |
| 8 ch x 4 x 4 KB | 1512.7 | 1513.8 | 1512.9 | 1503.5 | 1424.4 | 1514.3 | 1514.5 |
| 1 ch x 4 x 64 KB | 1519.1 | 1520.0 | 1519.1 | 1514.5 | 1430.1 | 1520.0 | 1520.1 |
| 8 ch x 4 x 64 KB | 1525.0 | 1525.1 | 1525.0 | 1524.5 | 1435.4 | 1525.1 | 1525.1 |
| 1 ch x 4 x 1 MB | 1525.4 | 1525.5 | 1525.4 | 1525.2 | 1435.7 | 1525.5 | 1525.5 |
| 8 ch x 4 x 1 MB | 1525.8 | 1525.8 | 1525.8 | 1525.8 | 1436.1 | 1525.8 | 1525.8 |

In steady state every leg but C1 reaches 100.0% of peak. C1 is capped at
94.1%, which is 16/17: one idle cycle per 16-beat burst. The sim harness
shows the same ratio (8 ch x 2 x 8 KB in 8,774 cycles against 8,254 for
A2, C2 and C3, 0.941). What separates the rest is the fixed cost per
descriptor, visible only at 1 ch x 4 KB: A2, C2 and C3 are level
(1,436-1,438), A and B1 are 1.0% behind them, and B2 is 5.3% behind --
consistent with the zero-load latencies below. A2's lead over B1 at that
point is the one measured on 10-23 morning (1.0%, ranges not overlapping)
and holds.

#### 8.2.1 Latency

Two instruments, on the same port (STREAM's, so each figure is the fabric
plus the endpoint plus any queueing behind other traffic):

- **Sim, exact.** `FB_LAT=1` adds framework monitors on `stream_rd_*` /
  `stream_wr_*` in the harness sim and matches every completion to the
  oldest open command of its ID; cycles, handshake to handshake. S0 there
  is the AXI4 slave BFM, not LiteDRAM, so absolute values are the BFM's;
  the differences between legs are the fabrics'.
- **Board, log2.** The master-side observer's latency histograms
  (`bin/fb_latency.py`): 16 bins, bin b = [2^b, 2^(b+1)) cycles, no sum, min
  or max. A percentile is reported as its bin's lower edge, and the mean
  estimate uses bin midpoints. It resolves 2x, not a few cycles: two legs
  a few cycles apart either side of a power of two land a bin apart.

Zero-load and loaded latency in sim (W2, AR -> first R and AW -> B):

| Leg | Read, zero-load min | Write, zero-load min | Read, 8 ch p50 | 8 ch x 2 x 8 KB, cycles |
| --- | ---: | ---: | ---: | ---: |
| A (bridge) | 13 | 30 | 271 | 8,262 |
| A2 (`preset = "xbar"`) | 8 | 26 | 240 | 8,254 |
| B1 (AXI Crossbar) | 11 | 26 | 238 | 8,262 |
| C1 (Forencich) | 10 | 25 | 254 | 8,774 |
| C2 (PULP) | 8 | 26 | 301 | 8,254 |
| C3 (LiteX) | 8 | 26 | 301 | 8,254 |

The zero-load minimum is the fabric's pipeline: A2, C2 and C3 add nothing
over the endpoint (8 read, 26 write), B1 adds 3 cycles to a read, C1 2 (and
takes one off a write), leg A 5 and 4 -- its registered stage at each end of
each port. (B2 does not simulate.) Under 8-channel load the p50 is mostly
queueing, and at equal throughput (Little's law) it says where the queue
sits rather than how fast the fabric is: the pass-through fabrics C2 and C3
accept STREAM's ARs as fast as it issues them and the reads wait at the
slave, so the clock starts earlier; A2 and B1 hold them back at the port.

On the board (2026-10-23, 3 runs; identical to the bin across runs):

| Leg | W2 1 ch read p50 | W2 8 ch read, mean est. | W2 write p50 | W3 f3 gap 0: STREAM read, mean est. | W3 mirror gap 0: write p50 |
| --- | ---: | ---: | ---: | ---: | ---: |
| A | 64 | 360 | 16 | 787 | 512 |
| A2 | 64 | 180 | 16 | 109 | 64 |
| B1 | 64 | 192 | 16 | 384 | 64 |
| B2 | 64 | 360 | 32 | 2,895 | 1,024 |
| C1 | 64 | 192 | 16 | 384 | 64 |
| C2 | 64 | 360 | 16 | 109 | 64 |
| C3 | 64 | 360 | 16 | 109 | starves (8.3) |

Read the W2 columns with the bin edges in mind: the sim's exact 8-channel
p50s (238-301) straddle 256, so the board shows 2x where the difference is
up to 26%. The two W3 columns are not edge effects -- they are 3.5-26x apart:

- **f3** (STREAM reading S0 while the injector writes it): every leg moves
  exactly the same 115.1 MiB/s for STREAM, so the latency is how many of
  STREAM's reads the path takes in and holds behind the writes. A2, C2 and
  C3 hold the fewest (~109 cycles); B1 and C1 ~384; leg A, with a
  registered stage at every port, ~787; B2 ~2,900. For a latency-sensitive
  master sharing a slave this is the figure that matters, and A2 is at the
  minimum.
- **mirror** (two writers into S0): write-to-B p50 is 64-127 cycles on A2,
  B1, C1 and C2, 512 on A and 1,024 on B2.

Write latency at zero load is one bin on every leg but B2 (16-31 cycles;
B2 32-63).

### 8.3 W3 -- two masters into one slave

Injector share of S0 in STREAM's window, 3 runs per point (A2's mirror 1,
§8), identical to 0.1% across runs. 50/50 = injector unthrottled; 90/10 =
idle 1280 cycles (f3) / 480 (mirror) between its 16-beat bursts.

| Flavor, offered mix, outstanding | A | A2 | B1 | B2 | C1 | C2 | C3 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| f3, 50/50, 2 or 4 | 50.0% | 50.0% | 50.0% | 50.0% | 50.0% | 50.0% | 50.0% |
| f3, 90/10, 2 or 4 | 10.1% | 10.1% | 10.1% | 10.1% | 10.1% | 10.1% | 10.1% |
| mirror, 50/50, 2 | 50.0% | 50.0% | 50.0% | 11.1% | 50.0% | 50.0% | 80% (STREAM waits, below) |
| mirror, 50/50, 4 | 50.0% | 50.0% | 50.0% | 20.0% | 50.0% | 50.0% | 80% (STREAM waits, below) |
| mirror, 90/10, 2 | 12.5% | 10.9% | 11.8% | 11.1% | 11.8% | 9.8% | 0.01% |
| mirror, 90/10, 4 | 12.5% | 10.9% | 11.8% | 13.4% | 11.8% | 9.8% | 0.01% |

f3 is the controller's split, not the fabric's: STREAM's reads and the
injector's writes travel on different AXI channels, so no fabric
arbitrates between them. The mirror -- two writers into one slave -- is
the fabric's arbitration, and the outcome is deterministic per leg:

- A, A2, B1, C1 and C2 split a contended slave evenly regardless of
  outstanding. At 90/10 the injector gets 10-12.5%, the differences being
  how each fabric's grant meets its 16-beat bursts.
- B2 favours STREAM heavily under full load: the injector gets 11-20%
  where the others give it 50%. Total S0 write throughput is about the same
  on every leg but C3 (~365-375 MiB/s), so this is who gets the slave, not
  how much it moves.
- C3 does not arbitrate between masters that keep writes outstanding.
  LiteX's `AXIArbiter` moves its write grant only when the granted master
  has nothing in flight (`ce = ~(aw.valid | w.valid | b.valid) &
  wr_lock.empty`). At gap 0 the injector always has one in flight, so it
  holds S0 until its whole program (1,048,556 beats) is done; STREAM gets
  nothing until then and finishes at 78.0 MiB/s against the injector's
  312.0 (S0 total 390). The point fails its check -- the injector finished
  inside STREAM's window, so the share is truncated -- with every CRC
  correct. At 90/10 it is the other way round: STREAM's eight channels
  always have a write in flight and the injector moves 28 beats in the
  window. In sim, where the injector's program outlasts the run, STREAM
  never moves at gap 0, and the harness test expects exactly that
  (`STARVES` in `dv/tests/test_fb_harness.py`, mutation-checked). This is
  LiteX's design, not a configuration: there is no fairness knob.

The 10-16 history of leg A's mirror (40% to a 2-outstanding injector until
2026-10-21) is unchanged:
bisected on the board (leg A rebuilt from each
commit's own tree, same LiteDRAM, `mirror` at 2 outstanding: 4fc23c275
40.0%, c98ed071e 40.0%, 73467609f 50.0%, 77ae05054 50.0%, ecebdada5
50.0%, HEAD 50.0%), the bridge's shared-slave arbiter picked from the raw
master requests into a 2-deep AW stage (the DDR adapter's AW skid) ahead of
the slave. LiteDRAM holds AWREADY until that burst's W is buffered, so
the stage sat full of AWs that had already won. Arbitration therefore
happened when a stage slot freed, and STREAM, whose 8 channels always
have an AW waiting, took every slot that freed while the injector was
between bursts waiting for a B. Bridge commit 73467609f (2026-10-17) moved
the pick to the slave pins from per-master request slots with nothing
queued past it, which is also how the AXI Crossbar is built here. Simulation
cannot show the effect with the BFM S0, which accepts AW without waiting
for W.

The two injector fixes (§6) changed none of legs A-B2's figures: every W3
share above equals that leg's figure before them (A2 and B1 10-23 morning,
A and B2 10-16/10-21). What they changed is that C1 and C3 run at all:
before them C1 deadlocked S0 at the window's close (an AW with no W) and C3
corrupted the next step's data (orphan W).

### 8.4 W1 and W4

Integrity checks only (§6, K3): the DDR3 chain passes on every leg (144/144
steps on A, B1, B2; 48/48 on A2, C1, C2, C3), but its rates are LiteDRAM's
(7-26% of peak, identical across legs) and say nothing about the fabrics.

### 8.5 Summary

| | A (bridge) | A2 (bridge, `preset = "xbar"`) | B1 (AXI Crossbar) | B2 (SmartConnect) | C1 (Forencich) | C2 (PULP) | C3 (LiteX) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Steady-state bandwidth | 100% | 100% | 100% | 100% | 94.1% (1 bubble / burst) | 100% | 100% |
| 1 ch x 4 KB | 1421 MiB/s | 1436 | 1422 | 1361 | 1347 | 1437 | 1438 |
| Zero-load read / write (sim, cycles) | 13 / 30 | 8 / 26 | 11 / 26 | not simulatable | 10 / 25 | 8 / 26 | 8 / 26 |
| STREAM read under f3 (board, mean est.) | ~787 | ~109 | ~384 | ~2,895 | ~384 | ~109 | ~109 |
| Contended-slave fairness | even | even | even | biased to STREAM (11-20%) | even | even | none: the master with writes in flight keeps S0 |
| Fabric LUT / FF (OOC, K7) | 8.4k / 6.7k | 2.9k / 1.1k | 2.7k / 2.2k | 8.3k + 2.2k mem / 11.6k | 2.3k / 1.6k | 3.1k / 1.1k | 0.7k / 0.06k |
| Fmax est. K7 / US+ (OOC) | ~250 / ~372 | ~254 / ~415 | ~256 / - | ~268 / - | ~235 / ~418 | ~248 / ~456 | ~402 / >= ~769 |
| Board design LUTs (10-23) | 87,964 | 84,498 | 84,629 | 89,823 | 84,099 | 84,921 | 82,985 |
| Simulatable | yes | yes | yes | no (encrypted) | yes | yes | yes |

On this port set and clock, the bridge as a plain crossbar (A2) is at
parity with the best of the open-source fabric generators on every axis
measured, and level with the Xilinx crossbar:

- Against PULP's `axi_xbar` (C2), the strongest general-purpose open-source
  crossbar here: the same bandwidth at every point, the same zero-load
  latency (8 / 26 cycles, nothing over the endpoint), the same f3 read
  latency, the same even split; 0.93x its LUTs at 1.04x its flops. Fmax is
  level. On Kintex-7, A2 meets a 4.0 ns (250 MHz) target with +0.068 ns
  (~254 MHz) and C2 misses it by 0.038 ns (~248 MHz), a 2.4% gap. On
  UltraScale+, the ordering depends on which run is used (above).
- Against Forencich's `axi_crossbar` (C1): 6% more bandwidth in steady
  state (C1's one-cycle gap per burst), 2 fewer cycles per read, ~3.5x lower
  f3 read latency, the same fairness; 1.22x its LUTs at 0.70x its flops,
  ~254 vs ~235 MHz.
- LiteX (C3) is a quarter of the logic and runs fastest, at the same
  bandwidth and zero-load latency, but it is not the same kind of fabric: a
  master that keeps one write in flight owns a slave indefinitely, slaves
  see the master's raw ID, and an unmapped command is never answered.
- Against the AXI Crossbar (B1): 1% more bandwidth at 1 ch x 4 KB, 3 fewer
  cycles per read, ~3.5x lower f3 read latency, the same fairness, 1.07x its
  LUTs at 0.51x its flops, ~254 vs ~256 MHz.

Leg A, the bridge's defaults, is the outlier in cost, not in throughput:
the registered stage at both ends of every port and the per-master ID remap
cost ~3x the logic, 5 cycles on a read and 4 on a write, and the deepest
queueing of the RTL legs under f3 (~787 cycles), for 100% of peak and an
even split. What A2 gives up to reach parity is exactly those: its slaves
see the full 10-bit ID, as B1's, C1's and C2's do, so the slave ID width
grows with the masters' ID width.
