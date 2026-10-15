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

**Version:** 0.1 (draft) · **Date:** 2026-10-14 · **Status:** planned; K0 in progress

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
| **B1 — Xilinx AXI Crossbar** | `axi_crossbar_v2_1` (the crossbar inside AXI Interconnect), full crossbar, shared-address multiple-data | Vivado 2025.1 IP catalog; HDL ships unencrypted, so it runs in the Verilator sim harness |
| **B2 — Xilinx SmartConnect** | `smartconnect_v1_0` | Vivado 2025.1 IP integrator; generated through a block design. Whether its generated HDL simulates outside Vivado is a K2 question |

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
| Memory controller | HPS hard DDR3 controller through f2sdram (AXI-3) | MIG 7-series DDR3, AXI4 slave interface | held constant across legs on each board; MIG's port is AXI4, so the Genesys 2 has **no** AXI3 edge and no `axi4_to_axi3` |
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
| S0 | DDR3 `0x0000_0000`, 1 GB | rd/wr | 128 | MIG AXI4 slave (its own width conversion, if any, is the controller's and identical all legs) |
| S1 | `desc_ram` read port `0x8000_0000` | rd | 128 | `sdpram_slave_axi4_axi4` |
| S2 | LFSR source `0x9000_0000` | rd | 128 | `axi4_cdc_rd` → LFSR source |
| S3 | CRC sink `0xA000_0000` | wr | 128 | `axi4_cdc_wr` → CRC sink |

AXI4, ID width 8 at every master, `stream`'s 3-bit channel USER carried
end to end. The configuration region (`0xF000_0000`) is the DE10 PRD's
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
- Leg B2: decided at K2 from what IP integrator generates.
- DDR3: MIG does not simulate in Verilator. The sim harness models S0 with
  an AXI4 memory slave of the same width and ID width; DDR3 timing is
  measured on the board, and fabric-only mode (W2) needs no DDR3 at all.

## 6. Milestones

| K | Content | Gate |
| --- | --- | --- |
| K0 | Fabric-only mode (W2) in sim, Leg A: the harness with the port set of §4, S0 tied to a memory model, `CharacterizationRunner` driving it over the UART channel | sim green, CRC verdicts on every run |
| K1 | Leg B1 (AXI Crossbar) in the same sim; then both legs on the board, W2 headline sweep | same host program both legs, sim then board |
| K2 | Leg B2 (SmartConnect): IP integrator generation, sim decision, board W2 | as K1 |
| K3 | MIG DDR3 at S0; W1-F1, W1-F2, W4, W3 on all legs | sim with the memory model, then board |
| K4 | Size and timing parses (Vivado utilization / timing reports), v1 sweep × 5, analysis section for the Kintex-7 legs | — |

The DE10 milestones resume after K1: the harness, host programs and
sequence files are then proven, and the DE10 work is the Quartus flow, the
JTAG front end and the Platform Designer leg.

## 7. Open questions

- **Memory controller:** MIG 7-series (the vendor controller, the analog
  of the HPS hard controller) is the plan. LiteDRAM is proven on this
  board and is the fallback if MIG bring-up stalls K3; either way it is
  one controller held constant across the legs.
- **SmartConnect simulation:** whether IP integrator's generated HDL is
  readable by Verilator. If not, B2 is board-only and the analysis says so.
- **Per-channel CRC through a fabric:** the CRC sink bins by channel. The
  vendor crossbars prefix the master index onto the ID at the slave; the
  sink must key on the channel field (USER, or the low ID bits), not on
  the full slave-side ID. K0 confirms it on Leg A, K1 on B1.
