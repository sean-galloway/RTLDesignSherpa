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

# STREAM - Scatter-gather Transfer Rapid Engine for AXI Memory

**Status:** 🟢 Nearly Complete - 95% Done
**Version:** 1.0

---

## Quick Start

STREAM is a tutorial-focused descriptor-based DMA engine for memory-to-memory transfers with scatter-gather support.

### Key Features

- ✅ **8 independent channels** with priority-based arbitration
- ✅ **Descriptor-based** scatter-gather with chaining
- ✅ **Simple APB config** - single write kicks off transfer
- ✅ **Aligned addresses only** (tutorial constraint)
- ✅ **Length in beats** (simplified from chunks/bytes)
- ✅ **MonBus monitoring** (standard 64-bit format)

### Intentional Simplifications (Tutorial Focus)

STREAM is deliberately simplified compared to RAPIDS:
- ❌ No network interfaces (pure memory-to-memory)
- ❌ No address alignment fixup (aligned addresses required)
- ❌ No credit management (simple transaction limits)
- ❌ No circular buffers (explicit chain termination)

**Learning Path:** STREAM → STREAM Extended → RAPIDS

---

## Architecture Overview

```
STREAM Components:
├── APB Config          - Channel registers, kick-off via write
├── Descriptor Engine   - Fetch and parse descriptors (from RAPIDS)
├── Scheduler           - Coordinate transfers (simplified from RAPIDS)
├── AXI Read Engine     - Source data fetch (multiple versions)
├── AXI Write Engine    - Destination data write (multiple versions)
├── Simple SRAM         - Buffer between read/write (from RAPIDS)
└── MonBus Reporter     - Monitoring packets
```

**Interfaces:**
- APB Slave - Configuration
- AXI Master (Descriptor) - Fetch descriptors (256-bit)
- AXI Master (Data Read) - Read source data (parameterizable)
- AXI Master (Data Write) - Write destination data (parameterizable)
- MonBus Master - Monitoring packets (64-bit)

---

## Descriptor Format

**256-bit Descriptor (4 × 64-bit words):**

| Bits | Field | Description |
|------|-------|-------------|
| [63:0] | `src_addr` | Source address (aligned to data width) |
| [127:64] | `dst_addr` | Destination address (aligned to data width) |
| [159:128] | `length` | Transfer length in **BEATS** (not bytes!) |
| [191:160] | `next_descriptor_ptr` | Next descriptor address (0 = last) |
| [192] | `valid` | Descriptor valid flag |
| [193] | `interrupt` | Generate interrupt on completion |
| [194] | `last` | Last descriptor in chain |
| [199:196] | `channel_id` | Channel ID (informational - for MonBus/debug) |
| [207:200] | `priority` | Transfer priority |

**Example Descriptor Chain:**
```c
descriptor_t desc[2];

// Descriptor 0 (first)
desc[0].src_addr = 0x80000000;  // Aligned
desc[0].dst_addr = 0x90000000;
desc[0].length = 64;  // 64 beats × 64 bytes = 4KB
desc[0].next_descriptor_ptr = &desc[1];  // Chain to next
desc[0].valid = 1;

// Descriptor 1 (last)
desc[1].src_addr = 0x80001000;
desc[1].dst_addr = 0x90001000;
desc[1].length = 32;  // 32 beats × 64 bytes = 2KB
desc[1].next_descriptor_ptr = 0;  // Last (no next)
desc[1].last = 1;  // Explicit last flag
desc[1].valid = 1;
desc[1].interrupt = 1;  // Generate interrupt when done

// Kick off transfer (single APB write)
write_apb(CH0_CTRL, &desc[0]);
```

---

## Usage Example

### 1. Kick Off Channel

```systemverilog
// Write descriptor address to channel 0 control register
// APB address 0x10 (ADDR_CH0_CTRL) selects channel 0
write_apb(ADDR_CH0_CTRL, descriptor_address);

// STREAM automatically:
// - APB decodes address → selects channel 0 (NOT from descriptor)
// - Channel 0 descriptor engine fetches descriptor
// - Channel 0 scheduler parses fields
// - Performs transfer
// - Follows chain (if next_descriptor_ptr != 0)
// - Generates MonBus completion packet
```

**Note:** Channel is selected by which APB register you write to (`CH0_CTRL` = channel 0, `CH1_CTRL` = channel 1, etc.), NOT by the `channel_id` field in the descriptor packet.

### 2. Monitor Status

```systemverilog
// Read channel status
status = read_apb(ADDR_CH0_STATUS);

// Check completion
bytes_transferred = read_apb(ADDR_CH0_BYTES_XFER);
```

### 3. Multi-Channel Operation

```systemverilog
// Kick off multiple channels via separate APB register writes
write_apb(ADDR_CH0_CTRL, desc0_address);  // Channel 0 (APB addr selects)
write_apb(ADDR_CH1_CTRL, desc1_address);  // Channel 1 (APB addr selects)
write_apb(ADDR_CH2_CTRL, desc2_address);  // Channel 2 (APB addr selects)

// Each APB address selects its channel:
//   0x10 → Channel 0
//   0x20 → Channel 1
//   0x30 → Channel 2
//   etc.

// Channels operate independently
// Arbiter manages shared AXI masters using descriptor priority field
```

---

## Directory Structure

```
projects/components/dma-ip/stream/
├── rtl/
│   ├── fub/                # Functional unit blocks
│   ├── macro/              # Integration blocks (+ stream_regs.rdl)
│   ├── top/                # 8-channel top-level wrapper
│   ├── filelists/          # Compile filelists
│   └── includes/           # Packages and imports
├── regs/                   # PeakRDL register collateral
│   ├── README.md           # Register generation guide
│   └── generated/          # PeakRDL-generated outputs
├── dv/
│   ├── tbclasses/          # STREAM testbench classes
│   └── tests/
│       ├── fub/            # Individual block tests
│       ├── macro/          # Multi-block tests
│       └── top/            # Top-level tests
├── bin/                    # coverage/report + regmap tooling
├── docs/
│   ├── stream_has/         # HAS spec tree (+ built PDFs)
│   └── stream_mas/         # MAS spec tree (+ built PDFs)
├── known_issues/           # Bug tracking
├── PRD.md                  # Product requirements (main spec)
├── CLAUDE.md               # AI assistance guide
└── README.md               # This file
```

---

## Documentation

- **[PRD.md](PRD.md)** - Complete product requirements and architecture
- **[CLAUDE.md](CLAUDE.md)** - AI assistance guide for development
- **Package:** `rtl/includes/stream_pkg.sv` - Descriptor format, types, enums

---

## Testing

```bash
# Run FUB tests (individual blocks)
pytest projects/components/dma-ip/stream/dv/tests/fub/ -v

# Run macro / top tests (multi-block)
pytest projects/components/dma-ip/stream/dv/tests/macro/ -v
pytest projects/components/dma-ip/stream/dv/tests/top/ -v

# Run with waveforms
WAVES=1 pytest projects/components/dma-ip/stream/dv/tests/fub/test_scheduler.py -v
```

---

## Development Status

### Phase 1: Foundation (Current)
- ✅ Directory structure
- ✅ Package definitions (`stream_pkg.sv`, `stream_imports.svh`)
- ✅ Documentation (PRD, CLAUDE, README)
- ⏳ Descriptor engine adaptation
- ⏳ Simplified scheduler design

### Phase 2: Core Blocks (Pending)
- APB config interface
- Scheduler FSM
- Channel arbiter

### Phase 3: Data Path (Pending)
- AXI read engine (v1 - basic)
- AXI write engine (v1 - basic)
- SRAM integration

### Phase 4: Integration (Pending)
- Top-level module
- MonBus reporter
- Single-channel validation

### Phase 5: Multi-Channel (Pending)
- 8-channel support
- Priority arbitration
- Multi-channel tests

---

## Comparison to RAPIDS

| Feature | RAPIDS | STREAM |
|---------|--------|--------|
| **Purpose** | Production DMA + Network | Tutorial DMA |
| **Complexity** | High | Low |
| **Interfaces** | APB + AXI + Network | APB + AXI |
| **Address Alignment** | Complex fixup | Aligned only |
| **Descriptor Length** | Chunks (4-byte) | Beats (data width) |
| **Channels** | 32 max | 8 max |
| **Credit Management** | Exponential encoding | Simple limits |
| **Tutorial Focus** | No | Yes |

**Use STREAM when:**
- Learning descriptor-based DMA design
- Need simple memory-to-memory transfers
- Want clear, understandable code

**Use RAPIDS when:**
- Need network integration
- Require complex alignment handling
- Production system with high performance needs

---

## Contributing

When contributing to STREAM, remember:
1. **Maintain tutorial focus** - Don't add unnecessary complexity
2. **Aligned addresses only** - This is intentional!
3. **Reuse from RAPIDS** where appropriate
4. **Follow repository conventions** (see `/CLAUDE.md`)
5. **Update documentation** with all changes

---

## License

This project is licensed under the MIT License - see the [LICENSE](../../../../LICENSE) file for details.

Copyright (c) 2024-2025 sean galloway

---

## Questions?

- **Architecture:** See `PRD.md` for complete specification
- **Development:** See `CLAUDE.md` for AI assistance guide
- **Repository:** See `/CLAUDE.md` for overall project guide
- **Parent Project:** See `projects/components/dma-ip/rapids/` for comparison

**Status:** Initial design - awaiting review and feedback

---

## References

Books and papers the stream design and its neighboring IP lines are built
against. Print chapter/section numbers are the citation currency; converted
markdown sources live in the local calibre library (`calibre/books/<book-slug>/`)
for maintainers auditing a claim.

### Books

- **Patterson & Hennessy**, *Computer Organization and Design: The
  Hardware/Software Interface, RISC-V Edition*, Morgan Kaufmann, 2018.
  Datapath and pipeline canon for the falcon suite (kestrel's single-cycle
  machine is COD §4.3/§4.4 realized; §4.6–4.9 is merlin's pipeline).
- **Hennessy & Patterson**, *Computer Architecture: A Quantitative Approach*,
  6th ed., Morgan Kaufmann, 2017. Quantitative backing: ILP and speculation
  (ch3, the gyrfalcon anchor), dynamic branch prediction (§3.4), memory
  technology and SRAM realities (ch2 §2.2 — the "no-latency SRAM is
  fantasy" anchor, see notes below).
- **Handy**, *The Cache Memory Book*, 2nd ed., Morgan Kaufmann, 1998.
  Cache-policy depth COD deliberately omits: write policies, replacement
  (true-LRU cost vs pseudo-LRU), write/line buffers, coherence protocols.
- **Przybylski**, *Cache and Memory Hierarchy Design: A Performance-Directed
  Approach*, Morgan Kaufmann, 1990. The analytical performance model and
  speed/size/set-size tradeoffs behind the cache IP line's geometry choices.

### Papers

- **Kroft**, "Lockup-Free Instruction Fetch/Prefetch Cache Organization,"
  ISCA 1981 — the MSHR; origin of jet-mesi-l1's nonblocking-cache
  decisions.
- **Jouppi**, "Architectural and Organizational Tradeoffs in the Design of
  the MultiTitan CPU," ISCA 1989 — tag-compare-before-data-gating hit-time
  argument (as documented in Przybylski §4.2).
- **Binkert et al.**, "The gem5 Simulator," ACM SIGARCH Computer
  Architecture News 39(2), 2011 — gem5 Ruby/SLICC oracles used as the
  executable coherence reference in the cache IP line.
- Miss-ratio rules of thumb (direct→2-way ~20%, Hill; associativity limits,
  Agarwal) are cited secondhand via Handy §2.2.2 and Przybylski §4.2.

### Specifications

- **RISC-V unprivileged and privileged ISA manuals** — ISA contract for
  the falcon suite (cited by chapter).
- **ARM IHI0022** (AMBA AXI4 / ACE) — the house fabric's transport
  authority; ACE shapes the cache line's snoop channels.
- **IEEE 754-2008** — the `math_ieee754_2008_fp32_*` units' contract.

### Design-reality notes

1. **SRAMs with no read latency are fantasy.** A zero-latency
   combinational memory is a *modeling choice*, not hardware: COD §4.3
   adopts it silently ("no read control signal is needed"), and kestrel
   adopts it *explicitly* as a documented contract (kestrel HAS ch4) so the
   single-cycle machine stays analyzable — with the fantasy labeled as
   such. Real SRAM macros have a 1-cycle read latency; H&P 6e ch2 §2.2
   (*Memory Technology and Optimizations*) is the quantitative treatment.
2. **stream's answer is `rtl/fub/stream_latency_bridge.sv`.** It bridges a
   registered (1-cycle-latency) FIFO/SRAM output to the consumer: cycle 0
   issues the read, cycle 1 the data arrives and pushes into a 4-deep
   `gaxi_fifo_sync` skid buffer, which absorbs backpressure — so `valid`
   stays aligned with `data` at full throughput without ready-leg
   gymnastics. Formally proven at `formal/stream/stream_latency_bridge/`.
