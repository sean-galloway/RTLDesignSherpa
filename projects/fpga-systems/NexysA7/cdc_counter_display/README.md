# CDC Counter Display - Nexys A7 FPGA Project

**Educational demonstration of Clock Domain Crossing (CDC) — both done right and broken on purpose**

---

## Two builds in one project

| Build | Top | Build | Program | Demo |
|---|---|---|---|---|
| **build-phase1 (original)** — button-only, one counter, pulse-based handshake CDC | `cdc_counter_display_top` | `make bitstream BUILD=phase1` | `make program BUILD=phase1` | Press BTNC → counter +1 → 7-seg updates. Standalone, no host required. |
| **build-demo (UART harness, default)** — four counters, four buttons, host-controlled clock divisors, switchable proper-vs-broken CDC, watch-it-fail demo | `cdc_demo_top` | `make bitstream` | `make program` | `make host-cdc_demo ARGS="watch-fail --counter 2"` runs the headline demo: take one counter to NO-CDC mode, sweep its clock from slow → fast, watch the 7-seg flicker garbage at high speeds while the other counters stay clean. |

**Demo-build docs:** [`docs/HARNESS.md`](docs/HARNESS.md) (CSR map + scripted demo procedure).
**Demo-build background:** [`docs/CDC_DEMO_TODO.md`](docs/CDC_DEMO_TODO.md) (taxonomy of CDC failure modes + "why it sometimes works anyway" pitfalls).

Each build is its own `build-*` directory (`build-phase1/` and `build-demo/`) with its own RTL top, filelist, XDC and Vivado project tree. The component Makefile is a dispatcher: targets go to `build-demo` by default, `BUILD=phase1` selects the other. All flow logic lives in the global `make/fpga_flow.mk` — the build Makefiles are variables only.

---

## Overview (phase 1)

This project demonstrates safe clock domain crossing (CDC) techniques using a practical example: a debounced button counter that transfers count values between independent clock domains to drive a 7-segment hex display.

### Key Features

- **Dual Independent Clock Domains**
  - Button domain: 10 Hz (100ms period)
  - Display domain: 1 kHz (1ms period)

- **CDC Components**
  - Button debouncing with configurable debounce time
  - 8-bit binary up counter (0x00-0xFF)
  - Pulse-based CDC handshake (sync_pulse)
  - Dual 7-segment hex display

- **Visual Indicators**
  - LED0: Button clock heartbeat (5 Hz toggle)
  - LED1: Display clock heartbeat (500 Hz toggle)

- **rtldesignsherpa Integration**
  - Uses common library modules (debounce, clock_divider, sync_pulse, hex_to_7seg)
  - Demonstrates proper module reuse
  - Production-quality CDC techniques

---

## Hardware Requirements

- **FPGA Board:** Digilent Nexys A7-100T (XC7A100T-1CSG324C)
- **Development Tools:** Xilinx Vivado 2020.2 or newer
- **Programming:** USB cable (included with board)

### Physical Connections

| Component | Connection | Purpose |
|-----------|-----------|---------|
| **CLK100MHZ** | On-board oscillator | 100 MHz system clock |
| **BTNC** | Center button | Increment counter |
| **BTNU** | Up button | Reset system |
| **AN[1:0]** | 7-segment anodes | Display digit select |
| **SEG[6:0]** | 7-segment segments | Display segments |
| **LED[0]** | LED 0 | Button domain heartbeat |
| **LED[1]** | LED 1 | Display domain heartbeat |

---

## Quick Start

### 1. Clone Repository

```bash
cd /path/to/rtldesignsherpa
```

### 2. Build Project

```bash
cd projects/fpga-systems/NexysA7/cdc_counter_display
make bitstream BUILD=phase1
```

This will:
- Create Vivado project
- Run synthesis
- Run implementation
- Generate bitstream
- Create reports

Build time: ~5-10 minutes (depending on your system)

### 3. Program FPGA

```bash
# Connect Nexys A7 board via USB and power it on
make program BUILD=phase1   # shared board layer: registry-pinned JTAG serial
```

Or use Vivado GUI:
```bash
vivado build-phase1/fpga/build/vivado_project/cdc_counter_display.xpr
# Hardware Manager → Open Target → Auto Connect → Program Device
```

### 4. Test Design

1. **Power on board** - Both heartbeat LEDs should blink (LED0 slowly, LED1 faster)
2. **Press center button (BTNC)** - Counter increments, display updates
3. **Watch display** - Shows hex value (00-FF)
4. **Press up button (BTNU)** - Resets counter to 00

---

## Usage

### Button Operation

- **BTNC (Center):** Increment counter
  - Each press increments count by 1
  - Rolls over from FF → 00
  - Debounced for clean operation

- **BTNU (Up):** Reset
  - Resets counter to 00
  - Resets all clock domains

### Display Format

The 7-segment display shows the counter value in hexadecimal:

```
 AN1  AN0
┌───┬───┐
│ 3 │ A │  ← Counter value = 0x3A (58 decimal)
└───┴───┘
```

Rightmost two digits display current count (00-FF hex).

### Heartbeat Indicators

- **LED0 (Button Domain):** Blinks at 5 Hz (200ms period)
  - Confirms button clock is running
  - Slow, visible blink

- **LED1 (Display Domain):** Blinks at 500 Hz (2ms period)
  - Confirms display clock is running
  - Fast flicker

---

## Architecture

### Block Diagram

```
System Clock (100 MHz)
         │
         ├──→ Clock Divider ──→ Button Clock (10 Hz)
         │                          │
         │                          ├──→ Debounce ──→ Edge Detect ──→ Counter
         │                          │                                    │
         │                          │                                    │ r_count_value[7:0]
         │                          │                                    │
         │                          └──→ Heartbeat LED0                  │
         │                                                                │
         └──→ Clock Divider ──→ Display Clock (1 kHz)               ┌────┘
                                    │                                │
                                    │              (CDC CROSSING)    │
                                    │                                │
                                    │         sync_pulse ←───────────┘ increment_pulse
                                    │                │
                                    │                ▼
                                    ├──→ Capture ──→ r_display_count[7:0]
                                    │                │
                                    │                ├──→ Hex Decode ──→ 7-Seg Display
                                    │                │
                                    └──→ Heartbeat LED1
```

### Clock Domains

| Domain | Frequency | Period | Purpose |
|--------|-----------|--------|---------|
| **sys_clk** | 100 MHz | 10 ns | System clock (from oscillator) |
| **btn_clk** | 10 Hz | 100 ms | Button sampling and counting |
| **disp_clk** | 1 kHz | 1 ms | Display refresh and update |

### CDC Crossings

**Crossing #1: Increment Pulse (btn_clk → disp_clk)**
- **Method:** sync_pulse module (pulse synchronizer)
- **Safety:** Dual-FF synchronizer + edge detection
- **Latency:** 2-3 disp_clk cycles (~2-3ms)
- **Guarantee:** Exactly one pulse per button press

**Crossing #2: Counter Value (btn_clk → disp_clk, quasi-static)**
- **Method:** Direct connection, sampled on pulse edge
- **Safety:** Counter value stable during pulse
- **Constraints:** False path (synchronized by pulse)

---

## Educational Value

### CDC Concepts Demonstrated

1. **Clock Domain Isolation**
   - Independent clock domains with no direct signal crossing
   - Proper synchronization at all boundaries

2. **Pulse-Based Handshake**
   - Single-cycle pulse generation in source domain
   - Safe pulse transfer to destination domain
   - Explicit transfer event (not just data synchronization)

3. **Quasi-Static Data Transfer**
   - Multi-bit data held stable during pulse
   - Sampled only on synchronized pulse edge
   - Avoids metastability on bus crossing

4. **Timing Constraints**
   - Asynchronous clock groups
   - False path declarations
   - ASYNC_REG attributes

### Why This Approach?

**Alternative: Multi-Bit Synchronizer**
```verilog
// Could use sync_2ff for slow-changing counter
sync_2ff #(.WIDTH(8)) u_sync (
    .i_data(r_count_value),
    .o_data(r_display_count)
);
```

**Why Pulse Handshake Instead:**
- ✅ Explicit transfer event (know when data updated)
- ✅ Better for learning CDC protocols
- ✅ Demonstrates common industry pattern
- ✅ Scales to more complex handshakes (req/ack)

---

## File Structure

```
projects/fpga-systems/NexysA7/cdc_counter_display/
├── Makefile                          # Area dispatcher (BUILD=demo|phase1)
├── docs/                             # Guides, analysis, transcripts
├── stable/                           # Last kept build's reports (make keep)
├── build-demo/                       # UART harness build (default)
│   ├── Makefile                      # Variables only + make/fpga_flow.mk
│   ├── rtl/                          # cdc_demo_top, harness, counter domain, RDL
│   │   └── filelists/cdc_demo_top.f  # The build's compile closure
│   ├── dv/                           # UART-equivalence cocotb sim (tb, tests, tbclasses)
│   ├── host/                         # host_cdc_demo.py + driver + programs
│   └── fpga/
│       ├── tcl/                      # create_project / build_all / synth_only
│       ├── constraints/cdc_demo.xdc
│       ├── bitstream/                # build output
│       └── reports/
└── build-phase1/                     # Button-only build
    ├── Makefile
    ├── rtl/cdc_counter_display_top.sv
    │   └── filelists/cdc_counter_display_top.f
    ├── dv/tests/test_cdc_counter_display.py   # CocoTB testbench
    └── fpga/
        ├── tcl/
        ├── constraints/nexys_a7_100t.xdc
        ├── bitstream/
        └── reports/
```

---

## Module Reuse from rtldesignsherpa

This project demonstrates proper reuse of the rtldesignsherpa common library:

| Module | Location | Purpose |
|--------|----------|---------|
| `clock_divider.sv` | `rtl/common/` | Generate btn_clk and disp_clk |
| `debounce.sv` | `rtl/common/` | Button debouncing |
| `sync_pulse.sv` | `rtl/common/` | CDC pulse synchronizer |
| `hex_to_7seg.sv` | `rtl/common/` | Hex to 7-segment decoder |

**Reuse Benefits:**
- Proven, tested modules
- Consistent coding style
- Well-documented components
- Production-quality CDC

---

## Simulation

**build-phase1** (`cdc_counter_display_top`) — CocoTB testbench for
pre-implementation verification:

```bash
make sim BUILD=phase1   # pytest build-phase1/dv/tests
```

Verifies clock generation, button debouncing, counter increment, CDC pulse
transfer, and display update.

**build-demo** (`cdc_demo_top`) — UART-characterization **equivalence** sim: wraps the
real `uart_axil_bridge` + `cdc_demo_harness` and runs the **same host programs**
that drive the FPGA (`build-demo/host/cdc_programs.py`) over a cocotb UART master,
so sim and silicon are byte-for-byte identical at the wire. See
[`docs/HARNESS.md`](docs/HARNESS.md).

```bash
make regmap       # regenerate the by-name regmap from build-demo/rtl/cdc_demo_csr.rdl
make consistency  # guard: regmap vs hand-written harness SV
make sim          # smoke / press / cfg_load / cdc_mode over the real bridge RTL
```

---

## Build Reports

After `make bitstream`, reports are generated in the build's `fpga/reports/`
(`make utilization` and `make timing` print the summaries):

| Report | File | Contents |
|--------|------|----------|
| **Timing Summary** | `timing_summary.txt` | Setup/hold timing, WNS/WHS |
| **Utilization** | `utilization_synth.txt` / `utilization_impl.txt` | LUT/FF/BRAM usage |
| **Clock Interaction** | `clock_interaction.txt` | Clock domain analysis |
| **CDC Report** | `cdc.txt` | CDC crossing analysis |
| **DRC** | `drc.txt` | Design rule checks |

### Expected Resource Usage

| Resource | Used | Available | Utilization |
|----------|------|-----------|-------------|
| **LUTs** | ~150 | 63,400 | < 1% |
| **FFs** | ~80 | 126,800 | < 1% |
| **BRAMs** | 0 | 135 | 0% |
| **DSPs** | 0 | 240 | 0% |

This design is very lightweight!

---

## Troubleshooting

### Issue: Heartbeat LEDs not blinking

**Cause:** Clock dividers not working
**Solution:**
- Check CLK100MHZ connection
- Verify clock divider parameters
- Check reset (BTNU) not stuck

### Issue: Display shows garbage

**Cause:** Display timing or decode issue
**Solution:**
- Check 7-segment connections in .xdc
- Verify hex_to_7seg module
- Check display clock frequency

### Issue: Counter doesn't increment

**Cause:** Button debounce or CDC issue
**Solution:**
- Verify button connection
- Check debounce timing
- Inspect sync_pulse operation
- Review CDC timing constraints

### Issue: Build fails

**Cause:** Missing dependencies
**Solution:**
- Ensure rtldesignsherpa common library accessible
- Check the build's `rtl/filelists/*.f` closure (`make lint` flattens the same list)
- Verify Vivado version (2020.2+)

---

## Advanced Experimentation

### Modify Clock Frequencies

Edit parameters in `cdc_counter_display_top.sv`:

```systemverilog
module cdc_counter_display_top #(
    parameter int BTN_CLK_FREQ_HZ = 10,    // Try 1, 5, 20
    parameter int DISP_CLK_FREQ_HZ = 1000, // Try 500, 2000
    // ...
```

**Experiment Ideas:**
- Slower button clock (1 Hz) for easier observation
- Faster display clock (10 kHz) for smoother refresh
- Match clock frequencies (edge case testing)

### Add Features

**1. Up/Down Counter**
- Add BTND for decrement
- Modify counter logic
- Add direction indicator LED

**2. Multi-Digit Display**
- Use all 8 digits
- Show binary counter patterns
- Add scrolling display

**3. Variable Count Rate**
- Add switches to control increment rate
- Auto-increment mode
- Programmable step size

**4. Pattern Generator**
- Cycle through test patterns
- Display animation
- Walking 1s/0s patterns

---

## References

### Documentation

- [Vivado Constraints Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2020_2/ug903-vivado-using-constraints.pdf)
- [CDC Methodology White Paper](https://www.xilinx.com/support/documentation/white_papers/wp272.pdf)
- [Nexys A7 Reference Manual](https://reference.digilentinc.com/reference/programmable-logic/nexys-a7/reference-manual)
- [rtldesignsherpa Documentation](../../README.md)

### Related rtldesignsherpa Examples

- `rtl/common/CLAUDE.md` - Common library guide
- `docs/pdfs/RTL_CDC.pdf` - CDC library reference book (rendered from `docs/markdown/`)
- `rtl/cdc/sync_pulse.sv` + `formal/cdc/sync_pulse/` - pulse synchronizer and its formal proofs

---

## License

Part of the RTL Design Sherpa project.
See root repository LICENSE file for details.

---

## Support

For issues or questions:

1. Check rtldesignsherpa documentation
2. Review Nexys A7 reference manual
3. Open issue in rtldesignsherpa repository

---

**Project Status:** Complete and tested
**Last Updated:** 2025-10-15
**Maintainer:** RTL Design Sherpa Project
