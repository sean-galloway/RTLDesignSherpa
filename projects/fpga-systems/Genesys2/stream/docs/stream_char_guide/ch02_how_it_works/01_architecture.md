# How It Works

## The spine (primary flow)

The host drives one UART link into a generated 1→N AXI4-Lite/APB fabric that
fans out to the DUT config, the harness CSR, and the trace/error memories:

### Figure 2.1: STREAM Characterization Harness Spine

![STREAM characterization harness spine](../assets/mermaid/01_harness_spine.png)

**Source:** [01_harness_spine.mmd](../assets/mermaid/01_harness_spine.mmd)

## Bridge slaves and base addresses

From `flows-stream-bridge/host/ADDRESS_MAP.md` and `PORT_MAP.md` (the current design; the older
`flows-stream-bridge/README.md` describes a superseded 5-slave decoder — trust
the address-map docs):

The two builds ride different bridges. The perf build (`build-perf`,
`USE_AXI_MONITORS=0`) carries the DMA plus a capture memory; the monitor build
(`build-mon`) adds the two observers, their tallies and the compression capture
memory. Both tables are generated from the bridge configs the RTL is generated
from -- `bin/bridge_windows.py` prints them, and host tools resolve every window
by NAME rather than by a pasted constant.

Perf build (`bridge_stream_char_axil`):

| Base | Size | Slave |
|------|------|-------|
| 0x00000000 | 8 KB | `stream_apb` (STREAM config) |
| 0x00010000 | 4 KB | `harness_csr` (harness control/status) |
| 0x00020000 | 64 KB | `desc_ram` (descriptor preload, 32 B/desc) |
| 0x00030000 | 4 KB | `stream_err` (MonBus IRQ-FIFO drain) |
| 0x00040000 | 256 KB | `debug_sram` -- STREAM MonBus capture memory |
| 0x00080000 | 4 KB | `dma_axil` (tied off, reserved MCDMA) |

Monitor build (`bridge_stream_mon_axil`):

| Base | Size | Slave |
|------|------|-------|
| 0x00000000 | 8 KB | `stream_apb` (STREAM config) |
| 0x00010000 | 4 KB | `harness_csr` (harness control/status) |
| 0x00020000 | 64 KB | `desc_ram` (descriptor preload, 32 B/desc) |
| 0x00030000 | 4 KB | `stream_err` (MonBus IRQ-FIFO drain) |
| 0x00040000 | 256 KB | `stream_tally` (master-observer MonBus records, counted) |
| 0x00080000 | 4 KB | `dma_axil` (tied off, reserved MCDMA) |
| 0x00090000 | 4 KB | `slave_err` (slave-monitor err/IRQ drain) |
| 0x000C0000 | 256 KB | `slave_tally` (slave-observer MonBus records, counted) |
| 0x00100000 | 256 KB | `stream_tally_cfg` (stream tally CAM config/readback) |
| 0x00140000 | 256 KB | `slave_tally_cfg` (slave tally CAM config/readback) |
| 0x00180000 | 4 KB | `slvmon_apb` (slave-monitor config regblock) |
| 0x00190000 | 4 KB | `obs_apb` (observer config regblock) |
| 0x001A0000 | 64 KB | `comp_sram` -- STREAM MonBus capture memory (host download) |

: Bridge slave address map

Every MonBus-carrying AXI path is 64-bit. The descriptor read path is a direct
256-bit AXI4 (`m_axi_desc` ↔ `desc_ram`, bypassing the bridge); the DMA payload
masters `m_axi_rd` / `m_axi_wr` are 128-bit into the pattern-gen / CRC-check
slaves.

## Key RTL blocks

| File | Role |
|------|------|
| `flows-stream-bridge/rtl/stream_char_top.sv` | FPGA pin-level top: instantiates the harness, `led_status_driver`, `seven_seg_4digit`. |
| `flows-stream-bridge/rtl/stream_char_harness.sv` | The integration hub: `uart_axil_bridge` + generated `bridge_stream_char_axil` + `harness_csr` + `desc_ram` + `debug_sram` + `axi_response_delay` ×2 + `axi4_dma_slaves` + `axi4_dma_observer` + the DUT `stream_top_ch8`. |
| `stream_char_framework/rtl/` | Shared framework RTL: `harness_csr.sv` (authoritative CSR), `desc_ram.sv`, `debug_sram.sv`, `axi_response_delay.sv`, `led_status_driver.sv`, `seven_seg_4digit.sv`, `sram_chan_tracker.sv`. |

: Key RTL blocks

## The instrumentation harness

Around the DUT, the harness supplies stimulus, a memory-latency model, and
non-perturbing observability:

- **`axi4_dma_slaves`** — an LFSR read-source pattern generator (feeds `m_axi_rd`)
  and a write-sink CRC checker (verifies `m_axi_wr`).
- **`axi_response_delay` ×2** — a programmable memory-latency model on the read
  and write paths (the `RESP_DELAY` CSR, Chapter 5).
- **`axi4_dma_observer`** — non-perturbing valid/ready bus meters plus a burst
  histogram and the MonBus-compression observer, all read back through the
  harness CSR.

STREAM's own in-core MonBus monitors feed the capture MEMORY -- `debug_sram` in
the perf build, `comp_sram` in the monitor build -- which the host downloads and
diffs against the bit-exact Python golden
(`bin/TBClasses/monbus/monbus_compressor.py`), so the wire format is verified on
silicon with no RTL decoder in the loop. The monbus compressor / half-beat packer
(`USE_MON_COMPRESSION`) drives the compression characterization.

The tallies are NOT on that path. Each observer's monbus group drives its tally's
record port directly, with no bridge in between: the observer is the monitor
under test, and the tally counts its packets. Through the bridge the tally
windows are the host's count-read path only.
