# STREAM Characterization on Nexys A7-100T

**Purpose:** On-chip functional and performance characterization of the
STREAM DMA using a self-contained test harness on the Digilent Nexys A7-100T
development board. All I/O to the host is through a single USB-UART link.

**Status:** Phase 1 -- RTL bring-up (harness and top level)

---

## Architecture

```
                     Nexys A7-100T (100 MHz)
┌──────────────────────────────────────────────────────────┐
│                                                          │
│ [USB-UART] ──→ uart_axil_bridge ──→ AXIL                 │
│                                     │                    │
│                                     ↓                    │
│                              axil_decode_5s              │
│                                     │                    │
│   ┌─────────┬──────────┬────────────┼────────┬─────────┐ │
│   ↓         ↓          ↓            ↓        ↓         ↓ │
│ axil2apb  harness_csr  desc_ram  err_rd   debug_sram rsvd│
│   │        │           │ ↑        │         ↑           │
│   ↓        ↓           │ │        │         │           │
│ stream   CSR regs    (ram)│    (stream     (dbg ram     │
│ .apb                      │      .s_axil   read port)   │
│                           │      _err)          ↑       │
│                           │                     │       │
│     stream_top_ch8        │                     │       │
│       s_apb         ←─────┘                     │       │
│       m_axi_desc    →  desc_ram (AXI4 read)     │       │
│       m_axi_rd      →  axi4_slave_rd_pattern_gen│       │
│       m_axi_wr      →  axi4_slave_wr_crc_check  │       │
│       s_axil_err    ←  host reads via decode            │
│       m_axil_mon    →  debug_sram (write port) ─────────┘
│       stream_irq    →  LED[0]                            │
│                                                          │
└──────────────────────────────────────────────────────────┘
```

### STREAM parameters (shrunk to fit Artix-7 100T)

| Parameter           | ASIC default | FPGA value |
|---------------------|--------------|------------|
| `NUM_CHANNELS`      | 8            | 8 (fixed)  |
| `DATA_WIDTH`        | 512          | 128        |
| `ADDR_WIDTH`        | 64           | 32         |
| `SRAM_DEPTH`        | 4096         | 256        |
| `CDC_ENABLE`        | 1            | 0          |
| `USE_AXI_MONITORS`  | 0            | 1          |

### Host memory map (via UART AXIL bridge)

| Range                         | Size   | Slave                   | Direction     |
|-------------------------------|--------|-------------------------|---------------|
| `0x0000_0000 - 0x0000_0FFF`   | 4 KB   | STREAM APB config       | R/W           |
| `0x0001_0000 - 0x0001_00FF`   | 256 B  | `harness_csr`           | R/W           |
| `0x0002_0000 - 0x0002_FFFF`   | 64 KB  | `desc_ram`              | W (preload)   |
| `0x0003_0000 - 0x0003_003F`   | 64 B   | STREAM err FIFO         | R             |
| `0x0004_0000 - 0x0007_FFFF`   | 256 KB | `debug_sram` trace      | R             |

### Harness CSR map (offsets from `0x0001_0000`)

| Offset | Name             | Access | Description                               |
|--------|------------------|--------|-------------------------------------------|
| `0x00` | `CTRL`           | RW     | `[0]` start, `[1]` clear_stats, `[2]` freeze_trace, `[3]` soft_reset |
| `0x04` | `STATUS`         | R      | `[0]` stream_irq, `[1]` any_error, `[2]` trace_overflow |
| `0x08` | `DBG_WR_PTR`     | R      | Words written to `debug_sram` since clear |
| `0x0C` | `DBG_OVERFLOW`   | R      | Sticky overflow flag                      |
| `0x10` | `CRC_RD_EXPECTED`| R      | Source-side CRC (from pattern gen)        |
| `0x14` | `CRC_WR_EXPECTED`| R      | Expected sink-side CRC                    |
| `0x18` | `CRC_WR_COMPUTED`| R      | Actual sink-side CRC                      |
| `0x1C` | `CRC_MATCH`      | R      | `[0]` match, `[1]` valid                  |
| `0x20` | `SCRATCH`        | RW     | Bring-up ping register                    |
| `0x24` | `BUILD_ID`       | R      | `0x5354_5243` ("STRC")                    |

---

## UART protocol

Uses `uart_axil_bridge` ASCII commands at **115200 baud, 8N1**:

```
Host → FPGA:  W 00010020 DEADBEEF\n     (write scratch)
FPGA → Host:  OK\n

Host → FPGA:  R 00010024\n               (read build ID)
FPGA → Host:  0x53545243\n
```

---

## File layout

```
projects/NexysA7/stream_characterization/
├── rtl/
│   ├── stream_char_top.sv         FPGA pin-level top (clk, uart, LEDs)
│   ├── stream_char_harness.sv     Internal integration
│   ├── axil_decode_5s.sv          1-master -> 5-slave AXIL decoder
│   ├── axil2apb.sv                AXIL slave -> APB master bridge
│   ├── harness_csr.sv             Control/status registers
│   ├── desc_ram.sv                Descriptor storage (AXIL wr / AXI4 rd)
│   └── debug_sram.sv              Debug trace buffer (dual AXIL)
├── tcl/                           Vivado build scripts (phase 2)
├── constraints/                   XDC files (phase 2)
├── host/                          Python UART driver (phase 2)
├── docs/                          Design notes
└── README.md                      This file
```

---

## Build and run (phase 2 -- not yet implemented)

```bash
cd projects/NexysA7/stream_characterization
make synth        # Vivado synthesis
make program      # Program FPGA via USB
python3 host/run_test.py --port /dev/ttyUSB1
```

---

## Dependencies

- `projects/components/converters/rtl/uart_to_axil4/` -- UART AXIL bridge
- `projects/components/stream/rtl/top/stream_top_ch8.sv` -- STREAM DMA core
- `projects/components/misc/rtl/axi4_slave_rd_pattern_gen.sv` -- source
- `projects/components/misc/rtl/axi4_slave_wr_crc_check.sv` -- sink
- `rtl/amba/includes/reset_defs.svh` -- reset macros

---

**Author:** sean galloway
**Last updated:** 2026-04-09
