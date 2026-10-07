# stream_characterization Port / Width Map

Lists every AXI/AXIL/APB port prefix that crosses a module boundary in the
stream_characterization harness, with the address and data widths and what
it currently wires to. Used to verify rule compliance (e.g., the
monbus-on-AXI rule: every monbus path on AXI = 64-bit data).

Conventions:
- **Channels** column says which AXI sub-channels the row covers (`wr`
  = AW/W/B, `rd` = AR/R, `rw` = both).
- **Addr** = address-channel width in bits (`awaddr`/`araddr`).
- **Data** = data-channel width in bits (`wdata`/`rdata`).
- Rows under one **Prefix** with the same width across `wr` and `rd`
  are collapsed into a single `rw` row.

---

## 1. Bridge external ports — `bridge_stream_char_axil_mon`

The bridge module exposes these ports at its top level. The harness
wires them to the rest of the system. All bridge slaves go through
the bridge's internal AXI4 fabric; widths are at the bridge's external
boundary (post-conversion for slaves with `data_width != 32`).

### 1.1 Master side (host)

| Prefix          | Channels | Protocol | Addr | Data | Currently connects to                   |
| --------------- | -------- | -------- | ---- | ---- | --------------------------------------- |
| `host_axi_`     | rw       | AXI4*    | 32   | 32   | UART AXIL bridge (`uart_axi_bridge.sv`) |

*The bridge expects full AXI4 on the master side but the host is AXIL —
the harness ties the AXI4-only fields (`awid=0`, `awlen=0`, `awsize=2`,
`awburst=01`, etc.) to constants matching single-beat AXIL semantics.

### 1.2 Slave side (fan-out)

| Prefix                  | Channels | Protocol | Addr | Data | Currently connects to                                    |
| ----------------------- | -------- | -------- | ---- | ---- | -------------------------------------------------------- |
| `stream_apb_`           | rw       | APB      | 12†  | 32   | STREAM's APB config slave (`s_apb_*`)                    |
| `harness_csr_axi_`      | rw       | AXIL     | 32   | 32   | `harness_csr` module (`s1_*`)                            |
| `desc_ram_axi_`         | rw       | AXIL     | 32   | 32   | `desc_ram.s_axil_*` (host descriptor writes, `s2_*`)     |
| `stream_err_axi_`       | rw       | AXIL     | 32   | **64** | STREAM's `s_axil_err_*` — monbus IRQ-status FIFO drain (`s3_*`) |
| `debug_sram_axi_`       | rw       | AXIL     | 32   | **64** | `debug_sram.rd_*` — host reads STREAM's monbus trace (`s4_*`) |
| `dma_axil_`             | rw       | AXIL     | 32   | 32   | **TIED OFF** — reserved for Xilinx MCDMA `s_axi_lite`    |
| `bridge_trace_sram_`    | rw       | AXIL     | 32   | **64** | `u_bridge_trace_sram.rd_*` — host reads bridge's monbus trace (`btr_*`) |

†Bridge emits 32-bit `PADDR`; harness slices low 12 bits into `apb_paddr`.

**Bold data widths** are 64-bit per the monbus-on-AXI rule. The bridge
generator inserts a single 32→64 width converter at the host adapter so
the 32-bit master can reach these slaves; the 32-bit slaves stay on the
direct path with no converter.

### 1.3 Monitor side-band (mon variant only)

| Prefix          | Channels | Protocol | Addr | Data | Currently connects to                                                   |
| --------------- | -------- | -------- | ---- | ---- | ----------------------------------------------------------------------- |
| `s_mon_axil_`   | rd*      | AXIL     | 32   | **64** | **TIED OFF** — bridge's monbus_axil_group IRQ-status FIFO (host has no 64-bit AXIL path today; bulk trace + `mon_irq_out` is sufficient) |
| `m_mon_axil_`   | wr       | AXIL     | 32   | **64** | `u_bridge_trace_sram.wr_*` — direct wire, bypasses bridge fabric        |

*`s_mon_axil_` only carries the read channels (`ar`/`r`) — the monbus
group exposes it as a read-only slave for IRQ-status drain.

Per-wrapper monitor cfg: **16 wrappers × 15 cfg signals = 240 inputs**
(1 master × 2 channels + 7 slaves × 2 channels = 16 wrappers). All
driven to defaults at the bridge instance via the
`BRIDGE_MON_CFG_DEFAULTS(P)` macro:
- `monitor/error/timeout_enable = 1`, `perf_enable = 0` (avoid packet
  congestion — never enable compl+perf together).
- `axi_err_select = 0` (every packet → write FIFO / bulk trace, none to
  err FIFO / IRQ).
- All `axi_*_mask = 0` (no filtering).

`mon_irq_out` is observed in the harness as `bridge_mon_irq` (currently
visible as a status LED — not yet OR'd into the harness IRQ tree).

---

## 2. Non-bridge interfaces (direct module-to-module)

These wires don't go through the bridge fabric; they're harness-level
direct connections between modules.

### 2.1 Descriptor read path (256-bit)

| Edge                            | Channels | Protocol | Addr | Data | Connects                                              |
| ------------------------------- | -------- | -------- | ---- | ---- | ----------------------------------------------------- |
| `desc_*` wires (`desc_arid`, `desc_araddr`, `desc_rdata`, …) | rd | AXI4 | 32 | **256** | STREAM's `m_axi_desc_*` ↔ `desc_ram.s_axi_*` (descriptor fetch) |

Note: descriptor reads bypass the bridge entirely. STREAM's scheduler
pulls full 256-bit descriptors in one beat from `desc_ram`. The host
writes those same descriptors as 8 × 32-bit AXIL stores via the bridge
(`desc_ram_axi_wr` path above).

### 2.2 STREAM monbus master (trace writes)

| Edge                            | Channels | Protocol | Addr | Data | Connects                                              |
| ------------------------------- | -------- | -------- | ---- | ---- | ----------------------------------------------------- |
| `mon_*` wires (`mon_awvalid`, `mon_wdata`, `mon_bvalid`, …) | wr | AXIL | 32 | **64** | STREAM's `m_axil_mon_*` ↔ `debug_sram.wr_*` (bulk monbus trace) |

### 2.3 STREAM data masters (DMA payload)

| Edge                            | Channels | Protocol | Addr | Data | Connects                                              |
| ------------------------------- | -------- | -------- | ---- | ---- | ----------------------------------------------------- |
| `rd_*` wires (`rd_arid`, `rd_araddr`, `rd_rdata`, …) | rd | AXI4 | 32 | **128** | STREAM's `m_axi_rd_*` ↔ `axi4_slave_rd_pattern_gen` (DMA source) |
| `wr_*` wires (`wr_awid`, `wr_awaddr`, `wr_wdata`, …) | wr | AXI4 | 32 | **128** | STREAM's `m_axi_wr_*` ↔ `axi4_slave_wr_crc_check`     (DMA sink) |

`DATA_WIDTH = 128` is a harness top-level parameter (default 128 bits).

---

## 3. Rule-compliance check

**Monbus-on-AXI rule: every AXI port that carries monbus packets is 64-bit.**

| Port                          | Carries monbus? | Width | Compliant? |
| ----------------------------- | --------------- | ----- | ---------- |
| STREAM `m_axil_mon_*`         | yes (writes)    | 64    | ✓          |
| STREAM `s_axil_err_*`         | yes (reads)     | 64    | ✓          |
| `debug_sram.wr_*`             | yes (writes)    | 64    | ✓          |
| `debug_sram.rd_*`             | yes (reads)     | 64    | ✓ (after task #82 refactor) |
| `bridge.m_mon_axil_*`         | yes (writes)    | 64    | ✓          |
| `bridge.s_mon_axil_*`         | yes (reads)     | 64    | ✓          |
| `bridge_trace_sram.wr_*`      | yes (writes)    | 64    | ✓          |
| `bridge_trace_sram.rd_*`      | yes (reads)     | 64    | ✓          |
| Bridge slave `stream_err_axi_`     | yes (fanout to STREAM s_axil_err) | 64 | ✓ |
| Bridge slave `debug_sram_axi_`     | yes (fanout to debug_sram rd)    | 64 | ✓ |
| Bridge slave `bridge_trace_sram_`  | yes (fanout to bridge_trace_sram rd) | 64 | ✓ |

All monbus paths are 64-bit. Non-monbus paths (host control, descriptor
writes, DMA payload) keep their native widths.

---

## 4. Address map (host's view)

| Address range            | Slave                  | Window  | Notes                              |
| ------------------------ | ---------------------- | ------- | ---------------------------------- |
| `0x0000_0000`–`0x0000_0FFF` | `stream_apb`        | 4 KB    | APB config (auto-converted)        |
| `0x0001_0000`–`0x0001_0FFF` | `harness_csr`       | 4 KB    | Timer / kick / status              |
| `0x0002_0000`–`0x0002_FFFF` | `desc_ram`          | 64 KB   | Descriptor preload (host writes)   |
| `0x0003_0000`–`0x0003_0FFF` | `stream_err`        | 4 KB    | STREAM monbus IRQ-FIFO drain (64b) |
| `0x0004_0000`–`0x0007_FFFF` | `debug_sram`        | 256 KB  | STREAM monbus bulk trace (64b)     |
| `0x0008_0000`–`0x0008_0FFF` | `dma_axil`          | 4 KB    | Reserved (MCDMA `s_axi_lite`)      |
| `0x000c_0000`–`0x000c_FFFF` | `bridge_trace_sram` | 64 KB   | Bridge monbus bulk trace (64b)     |

`cfg_mon_group_base_addr` for the bridge's internal monbus_axil_group is
set to `0x000c_0000` in the harness, so the bridge writes records to
the same address window the host reads back through.

---

## 5. Quick host-side decoder commands

Both trace regions share the same 24-byte record layout (3 × 64-bit
beats), so `dump_monbus_sram.py` works on either with `--base`:

```bash
# STREAM monbus trace (per-channel monitors inside stream_core)
python3 flows-stream-bridge/host/dump_monbus_sram.py \
    --port /dev/ttyUSB1 --base 0x00040000 --bytes 0x40000

# Bridge monbus trace (per-port axi4_master_*_mon wrappers)
python3 flows-stream-bridge/host/dump_monbus_sram.py \
    --port /dev/ttyUSB1 --base 0x000c0000 --bytes 0x10000
```
