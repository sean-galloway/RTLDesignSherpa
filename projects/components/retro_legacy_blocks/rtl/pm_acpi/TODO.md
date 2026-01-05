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

# PM_ACPI TODO List

## Status: MVP Complete - Ready for Verification

### Completed ✅
- [x] PeakRDL register specification (pm_acpi_regs.rdl)
- [x] PeakRDL register generation (pm_acpi_regs.sv, pm_acpi_regs_pkg.sv)
- [x] Core PM logic (pm_acpi_core.sv)
  - PM Timer with configurable divider
  - Power state FSM (S0/S1/S3)
  - GPE event handling (32 sources)
  - Clock gating control (32 bits)
  - Power domain sequencing (8 domains)
  - Wake event logic
  - Interrupt aggregation
- [x] Configuration register wrapper (pm_acpi_config_regs.sv)
  - PeakRDL hwif mapping
  - W1C edge detection
  - Auto-clear fields
- [x] APB top-level wrapper (apb_pm_acpi.sv)
  - CDC_ENABLE parameter
  - Dual clock domain support
- [x] Filelist (filelists/apb_pm_acpi.f)
- [x] PeakRDL README (peakrdl/README.md)

### High Priority 🔴

#### Verification and Testing
- [ ] **Python Helper Script** (pm_acpi_helper.py)
  - Register access methods
  - Power state control functions
  - PM timer utilities
  - GPE management
  - Clock gate control
  - Power domain control
  - Based on smbus_helper.py pattern

- [ ] **Cocotb Test Infrastructure**
  - Basic register R/W tests
  - PM timer increment and overflow tests
  - Power state transition tests (S0↔S1, S0↔S3, wake)
  - GPE event tests (set, clear, enable, interrupt)
  - Clock gating control tests
  - Power domain sequencing tests
  - Wake event tests (power button, GPE, RTC, external)
  - Full ACPI sequence tests

- [ ] **Test Benches**
  - Create dv/tbclasses/pm_acpi/ directory
  - pm_acpi_tb.py - Base testbench class
  - pm_acpi_tests_basic.py - Basic functionality tests
  - Create dv/tests/pm_acpi/ directory
  - test_apb_pm_acpi.py - Cocotb test runner

#### Documentation
- [ ] **Update Main README.md**
  - Full feature description
  - Register map summary
  - Usage examples
  - Integration guidelines
  - Power state descriptions
  - Clock domain configuration

- [ ] **IMPLEMENTATION_STATUS.md**
  - Current status tracking
  - Feature checklist
  - Known issues/limitations
  - Testing status

### Medium Priority 🟡

#### Feature Enhancements
- [ ] **Enhanced Power Sequencing**
  - Gradual clock gate transitions (not instant)
  - Power domain ramp-up delays
  - Sequencing state machine

- [ ] **Reset Handling**
  - Wire up reset request outputs
  - Track reset sources properly
  - External reset pin input
  - Watchdog reset input
  - Software reset mechanism

- [ ] **Button Debouncing**
  - Enhanced debounce logic for power/sleep buttons
  - Configurable debounce threshold
  - Long-press detection

- [ ] **PM Timer Enhancements**
  - Optional 64-bit timer support
  - Timer prescaler options
  - Multiple timer comparison values

### Low Priority 🟢

#### Advanced Features
- [ ] **S5 State Support**
  - Add S5 (soft off) state to FSM
  - S5 wake sources
  - S5 sequencing

- [ ] **GPE Enhancements**
  - Additional GPE banks (GPE1)
  - Level vs edge configuration per event
  - GPE run/wake split

- [ ] **Legacy Support**
  - IRQ0 timer routing
  - IRQ8 RTC routing
  - Legacy replacement mode implementation

- [ ] **C-States**
  - Processor C-state hints
  - P-state coordination
  - Thermal management

#### Optimization
- [ ] **Timing Optimization**
  - Pipeline register insertions if needed
  - Critical path analysis
  - CDC optimization

- [ ] **Area Optimization**
  - Configurable feature enables
  - Resource sharing opportunities

### Integration Notes

**System Integration Requirements:**
- Connect `gpe_events[31:0]` to system event sources
- Connect `power_button_n` to physical button (debounced externally if needed)
- Connect `sleep_button_n` to physical button
- Connect `rtc_alarm` to RTC alarm output
- Connect `ext_wake_n` to external wake signal
- Connect `clock_gate_en[31:0]` to system clock gates
- Connect `power_domain_en[7:0]` to power switches
- Connect `pm_interrupt` to interrupt controller

**Clock Domain Configuration:**
- **CDC_ENABLE=0**: Single clock domain (pclk == pm_clk)
  - Typical for synchronous systems
  - Lower latency
  - Simpler timing analysis
  
- **CDC_ENABLE=1**: Dual clock domains (pclk != pm_clk)
  - Always-on PM timer even when APB clock gated
  - pm_clk can be battery-backed
  - Higher latency due to CDC
  - More complex timing

### Known Limitations (MVP)

1. **Clock Gating**: Instant transitions (no ramp)
2. **Power Domains**: Instant on/off (no sequencing delays)
3. **Reset Tracking**: Simplified implementation
4. **Button Debounce**: Simple 3-stage synchronizer only
5. **GPE**: Edge-triggered only (no level mode)
6. **Timer**: 32-bit only (no 64-bit mode)

### Testing Checklist

- [ ] APB register read/write to all registers
- [ ] PM timer increments at correct rate
- [ ] PM timer overflow generates interrupt
- [ ] Power state S0→S1 transition
- [ ] Power state S1→S0 wake
- [ ] Power state S0→S3 transition
- [ ] Power state S3→S0 wake
- [ ] GPE events set status bits
- [ ] GPE status cleared by W1C
- [ ] GPE interrupt generation
- [ ] Clock gates controlled by registers
- [ ] Clock gates auto-gated in S1/S3
- [ ] Power domains controlled by registers
- [ ] Power domains auto-off in S3
- [ ] Power button generates PM1 event
- [ ] Sleep button generates PM1 event
- [ ] RTC alarm generates PM1 event
- [ ] Wake from S1 on enabled events
- [ ] Wake from S3 on enabled events
- [ ] Interrupt aggregation correct
- [ ] CDC mode (CDC_ENABLE=1) functional

### Questions / Decisions Needed

- [ ] Specific GPE event source assignments?
- [ ] Clock gate to peripheral mapping?
- [ ] Power domain to subsystem mapping?
- [ ] PM timer frequency for target system?
- [ ] CDC required for target application?

---

**Last Updated:** 2025-11-16  
**Status:** MVP Complete, Ready for Verification Phase
