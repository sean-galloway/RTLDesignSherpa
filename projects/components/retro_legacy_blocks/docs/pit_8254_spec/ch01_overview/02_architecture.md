### APB PIT 8254 - Architecture

#### High-Level Block Diagram

```
                                  apb_pit_8254 (Top Level)
┌────────────────────────────────────────────────────────────────────────┐
│                                                                        │
│  ┌──────────────┐     ┌──────────────────┐     ┌──────────────────┐  │
│  │              │     │                  │     │                  │  │
│  │  apb_slave   │────▶│  pit_config_regs │────▶│    pit_core      │  │
│  │   or         │     │                  │     │                  │  │
│  │ apb_slave_cdc│     │  (PeakRDL Wrap)  │     │  (3 Counters)    │  │
│  │              │     │                  │     │                  │  │
│  └──────────────┘     └──────────────────┘     └──────────────────┘  │
│                                                                        │
│  APB Domain         │  Register Interface   │  Counter Domain         │
│  (pclk)             │                       │  (pit_clk or pclk)      │
└────────────────────────────────────────────────────────────────────────┘
         ▲                                              │
         │                                              ▼
    APB Interface                            GATE[2:0], OUT[2:0]
```

#### Module Hierarchy

```
apb_pit_8254
├── apb_slave (CDC_ENABLE=0) or apb_slave_cdc (CDC_ENABLE=1)
│   └── Converts APB protocol to cmd/rsp interface
├── pit_config_regs
│   ├── peakrdl_to_cmdrsp (protocol adapter)
│   └── pit_regs (PeakRDL generated)
│       └── Register file with hwif interface
└── pit_core
    ├── pit_counter (Counter 0)
    ├── pit_counter (Counter 1)
    └── pit_counter (Counter 2)
```

#### Three-Layer Architecture

Following the HPET design pattern, the PIT uses a clean three-layer architecture:

**Layer 1: APB Interface (apb_pit_8254)**
- Protocol conversion (APB → cmd/rsp)
- Optional clock domain crossing
- Top-level integration
- Parameter configuration

**Layer 2: Configuration Registers (pit_config_regs)**
- Register file integration
- Edge detection for write strobes
- Counter readback connection
- Status feedback aggregation

**Layer 3: Core Logic (pit_core + pit_counter)**
- Counter control and data routing
- Three independent pit_counter instances
- Mode 0 counting logic
- GATE/OUT signal management

#### Data Flow

**Write Path:**
```
APB Write → APB Slave → CMD Interface → PeakRDL Adapter →
→ PeakRDL Registers → hwif_out → Config Regs Wrapper →
→ PIT Core → Counter Instance → Counter Logic
```

**Read Path:**
```
Counter Value → count_reg_out → PIT Core → Config Regs →
→ hwif_in → PeakRDL Registers → Read Data → RSP Interface →
→ APB Slave → APB Read Data
```

#### Counter State Machine

Each `pit_counter` module implements a simple state machine for Mode 0:

```
                    ┌──────────┐
                    │          │
                    │  RESET   │
                    │          │
                    └────┬─────┘
                         │ rst_n
                         ▼
                    ┌──────────┐
        ┌───────────│          │
        │           │   IDLE   │◀──────────────┐
        │  ┌────────│          │               │
        │  │        └────┬─────┘               │
        │  │             │ reload_pending      │
        │  │ NULL_COUNT  ▼                     │
        │  │        ┌──────────┐               │
        │  │        │          │               │
        │  └───────▶│  LOADED  │               │
        │           │          │               │
        │           └────┬─────┘               │
        │                │ GATE && CLK_EN      │
        │                ▼                     │
        │           ┌──────────┐               │
        │           │          │               │
        └──────────▶│ COUNTING │               │
                    │          │               │
                    └────┬─────┘               │
                         │ count==0            │
                         ▼                     │
                    ┌──────────┐               │
                    │          │               │
                    │ TERMINAL │───────────────┘
                    │          │  (OUT=1)
                    └──────────┘
```

**States:**
- **RESET**: All registers cleared
- **IDLE**: Waiting for count value load (NULL_COUNT=1)
- **LOADED**: Count loaded but not counting yet
- **COUNTING**: Actively decrementing counter
- **TERMINAL**: Count reached zero, OUT signal high

#### Clock Domains

**Single Clock Mode (CDC_ENABLE=0):**
```
pclk ──┬──▶ APB Slave
       └──▶ Registers ──▶ Counters
```

**Dual Clock Mode (CDC_ENABLE=1):**
```
pclk ────▶ APB Slave ──▶ CDC ──┐
                                ├──▶ Registers
pit_clk ────────────────────────┴──▶ Counters
```

#### Control Flow

**Counter Programming Sequence:**
1. Write `PIT_CONTROL` with control word (counter select, mode, RW mode)
2. Control word decoded and routed to selected counter
3. Write `COUNTERx_DATA` with 16-bit count value
4. Counter loads value and starts counting (if GATE high and PIT enabled)
5. Counter decrements on each clock cycle
6. When count reaches 0, OUT goes high

**Status Readback:**
1. Read `PIT_STATUS` register
2. Returns 3 bytes (one per counter) with packed status fields
3. Status includes: OUT state, NULL_COUNT, RW mode, counter mode, BCD flag

#### Reset Behavior

**Power-On Reset:**
- All counters: NULL_COUNT=1, counting=0, OUT=0
- PIT disabled (PIT_CONFIG=0)
- All count values cleared

**Soft Reset (PIT disable):**
- Counters stop counting (counting=0)
- Count values preserved
- OUT signals remain in current state
- NULL_COUNT flags unchanged

---

**Version:** 1.0
**Last Updated:** 2025-11-08
