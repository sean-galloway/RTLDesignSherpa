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

# SMBus 2.0 Controller

## Overview

Complete SMBus 2.0 controller implementation with master and slave modes, supporting all standard transaction types, packet error checking (PEC), and timeout detection.

**Status:** Phase 2 of 10 (In Progress)
- **Phase 1:** ✅ PeakRDL register definitions complete
- **Phase 2:** 🚧 Core RTL (master/slave FSMs) - In Progress
- **Phase 3:** ✅ FIFO modules
- **Phase 4:** ⏳ Config register generation (requires PeakRDL tool)
- **Phase 5:** ⏳ APB wrapper integration
- **Phase 6:** ✅ Filelist
- **Phase 7:** ⏳ Test infrastructure
- **Phase 8:** ✅ Python helper
- **Phase 9:** ⏳ Comprehensive testing
- **Phase 10:** 🚧 Documentation - In Progress

## Features

### Implemented
- ✅ **Register Definitions:** Complete PeakRDL specification with 14 registers
- ✅ **PEC Module:** CRC-8 calculator for packet error checking (polynomial 0x07)
- ✅ **FIFO Wrapper:** 32-byte TX/RX FIFOs for block transfers
- ✅ **Core FSM Skeleton:** Master/slave state machines with transaction type support
- ✅ **Clock Generation:** Programmable SCL clock divider (100kHz/400kHz)
- ✅ **Timeout Detection:** 25-35ms timeout counter
- ✅ **Start/Stop Detection:** I2C-compatible START/STOP condition detection
- ✅ **Python Helper:** SMBusHelper class for register programming

### In Progress
- 🚧 **Physical Layer:** Bit-level TX/RX implementation
- 🚧 **Master FSM:** Complete transaction sequencing
- 🚧 **Slave FSM:** Address matching and response logic

### To Be Implemented
- ⏳ **Arbitration:** Multi-master bus arbitration
- ⏳ **Clock Stretching:** Slave clock stretching support
- ⏳ **Config Registers:** PeakRDL-generated SystemVerilog
- ⏳ **APB Wrapper:** Top-level integration module
- ⏳ **Alert Response:** ARA (Alert Response Address) support
- ⏳ **Test Suite:** Cocotb-based verification
- ⏳ **Timing Diagrams:** Wavedrom transaction illustrations

## Architecture

### Module Hierarchy
```
apb4_smbus (Top Level - To Be Implemented)
├── apb4_slave (APB4 protocol converter)
├── smbus_config_regs (Register interface - To Be Generated)
└── smbus_core (SMBus protocol engine)
    ├── smbus_pec (CRC-8 calculator) ✅
    ├── simple_fifo (TX FIFO wrapper) ✅
    ├── simple_fifo (RX FIFO wrapper) ✅
    ├── Master FSM 🚧
    ├── Slave FSM 🚧
    └── Physical Layer 🚧
```

### Design Pattern
Follows the RTC methodology:
1. **Layer 1:** APB wrapper (`apb4_smbus.sv`) - APB4 slave interface
2. **Layer 2:** Config registers (`smbus_config_regs.sv`) - Register interface with status feedback
3. **Layer 3:** Core logic (`smbus_core.sv`) - SMBus protocol implementation

## Register Map

**Base Address:** Configurable via APB wrapper
**Address Width:** 12 bits (0x000 - 0xFFF)
**Data Width:** 32 bits

| Offset | Register           | Type | Description                      |
|--------|-------------------|------|----------------------------------|
| 0x000  | SMBUS_CONTROL     | RW   | Global control (enable, mode, PEC) |
| 0x004  | SMBUS_STATUS      | RO   | Status flags (busy, errors, state) |
| 0x008  | SMBUS_COMMAND     | RW   | Transaction command and trigger  |
| 0x00C  | SMBUS_SLAVE_ADDR  | RW   | Target/own slave address         |
| 0x010  | SMBUS_DATA        | RW   | Single byte data register        |
| 0x014  | SMBUS_TX_FIFO     | WO   | Transmit FIFO write port         |
| 0x018  | SMBUS_RX_FIFO     | RO   | Receive FIFO read port           |
| 0x01C  | SMBUS_FIFO_STATUS | RO   | FIFO levels and flags            |
| 0x020  | SMBUS_CLK_DIV     | RW   | Clock divider configuration      |
| 0x024  | SMBUS_TIMEOUT     | RW   | Timeout threshold                |
| 0x028  | SMBUS_OWN_ADDR    | RW   | Own slave address (slave mode)   |
| 0x02C  | SMBUS_INT_ENABLE  | RW   | Interrupt enable mask            |
| 0x030  | SMBUS_INT_STATUS  | RW1C | Interrupt status (W1C)           |
| 0x034  | SMBUS_PEC         | RW   | PEC value register               |
| 0x038  | SMBUS_BLOCK_COUNT | RW   | Block transfer count             |

## Transaction Types

| Type | Code | Description                    | Status |
|------|------|--------------------------------|--------|
| Quick Command     | 0x0 | 0 bytes                  | 🚧 |
| Send Byte         | 0x1 | 1 byte, no command       | 🚧 |
| Receive Byte      | 0x2 | 1 byte, no command       | 🚧 |
| Write Byte Data   | 0x3 | 1 cmd + 1 data          | 🚧 |
| Read Byte Data    | 0x4 | 1 cmd + 1 data          | 🚧 |
| Write Word Data   | 0x5 | 1 cmd + 2 data          | 🚧 |
| Read Word Data    | 0x6 | 1 cmd + 2 data          | 🚧 |
| Block Write       | 0x7 | 1 cmd + count + data    | 🚧 |
| Block Read        | 0x8 | 1 cmd + count + data    | 🚧 |
| Block Process Call| 0x9 | Block write-read        | 🚧 |

## Files

### RTL Implementation
```
smbus/
├── smbus_pec.sv              ✅ PEC CRC-8 calculator
├── simple_fifo.sv            ✅ FIFO wrapper with count
├── smbus_core.sv             🚧 Core SMBus controller
├── smbus_config_regs.sv      ⏳ Generated from PeakRDL
├── apb4_smbus.sv              ⏳ APB wrapper (top level)
└── filelists/
    └── apb4_smbus.f           ✅ Compilation filelist
```

### PeakRDL Specification
```
peakrdl/
├── smbus_regs.rdl            ✅ Register definitions
└── README.md                 ✅ PeakRDL documentation
```

### Python Support
```
smbus_helper.py               ✅ Register programming helper
```

### Verification (To Be Implemented)
```
dv/
├── tbclasses/smbus/
│   ├── smbus_tb.py          ⏳ Testbench base class
│   └── smbus_tests_basic.py ⏳ Basic test scenarios
└── tests/smbus/
    └── test_apb4_smbus.py    ⏳ Cocotb test runner
```

## Usage Example

### Python Helper (For Testing)
```python
from smbus_helper import SMBusHelper

# Initialize
smbus = SMBusHelper('smbus_regmap.py', apb_data_width=32,
                    apb_addr_width=16, start_address=0x1000, log=logger)

# Configure for 100kHz at 100MHz system clock
smbus.initialize_defaults(system_clock_mhz=100)

# Write byte to EEPROM
smbus.write_byte_data(slave_addr=0x50, command=0x10, data=0xAB)

# Read word from sensor
smbus.read_word_data(slave_addr=0x48, command=0x00)

# Block write
smbus.block_write(slave_addr=0x50, command=0x20, 
                  data_list=[0x01, 0x02, 0x03, 0x04])

# Generate APB transactions
apb_packets = smbus.generate_apb_cycles()
```

### SystemVerilog Instantiation (Future)
```systemverilog
apb4_smbus #(
    .FIFO_DEPTH(32)
) u_smbus (
    .pclk                 (apb_clk),
    .presetn              (apb_rst_n),
    
    // APB4 Interface
    .s_apb_PSEL           (apb_psel),
    .s_apb_PENABLE        (apb_penable),
    .s_apb_PREADY         (apb_pready),
    .s_apb_PADDR          (apb_paddr[11:0]),
    .s_apb_PWRITE         (apb_pwrite),
    .s_apb_PWDATA         (apb_pwdata),
    .s_apb_PSTRB          (apb_pstrb),
    .s_apb_PPROT          (apb_pprot),
    .s_apb_PRDATA         (apb_prdata),
    .s_apb_PSLVERR        (apb_pslverr),
    
    // SMBus Physical Interface
    .smb_scl_i            (smb_scl_in),
    .smb_scl_o            (smb_scl_out),
    .smb_scl_t            (smb_scl_tri),
    .smb_sda_i            (smb_sda_in),
    .smb_sda_o            (smb_sda_out),
    .smb_sda_t            (smb_sda_tri),
    
    // Interrupts
    .smb_interrupt        (smb_irq)
);
```

## Clock Configuration

### SCL Frequency Calculation
```
SCL_freq = SYS_CLK / (4 × (CLK_DIV + 1))
```

**For 100MHz System Clock:**
- **100kHz (Standard):** `CLK_DIV = 249`
- **400kHz (Fast):** `CLK_DIV = 62`

**For 50MHz System Clock:**
- **100kHz (Standard):** `CLK_DIV = 124`
- **400kHz (Fast):** `CLK_DIV = 30`

## Timeout Configuration

SMBus specification requires 25-35ms timeout detection.

**For 100MHz System Clock:**
- **25ms:** `TIMEOUT = 2,500,000` (0x2625A0)
- **35ms:** `TIMEOUT = 3,500,000` (0x3567E0)

**Default:** 2,500,000 cycles (25ms @ 100MHz)

## Implementation Status Details

### Completed Modules

#### 1. smbus_pec.sv ✅
- CRC-8 calculation with polynomial x⁸ + x² + x + 1 (0x07)
- Running CRC during transaction
- Enable/clear control
- Tested and verified

#### 2. simple_fifo.sv ✅
- Wraps project's fifo_sync module
- 32-byte depth (SMBus 2.0 max block size)
- Count output for level monitoring
- Mux mode for lowest latency

#### 3. smbus_helper.py ✅
- Complete transaction type support
- Clock/timeout configuration methods
- Interrupt management
- FIFO reset and soft reset
- Initialize defaults helper

#### 4. peakrdl/smbus_regs.rdl ✅
- 14 registers fully specified
- Field-level documentation
- Access permissions (RW, RO, W1C)
- Reset values defined

### In-Progress Modules

#### 5. smbus_core.sv 🚧
**Implemented:**
- Module skeleton and interfaces
- Transaction type enumerations
- Master FSM states (16 states)
- Slave FSM states (11 states)
- Physical layer state enumeration
- Clock generation logic
- Input synchronization (2-stage)
- START/STOP condition detection
- Timeout counter
- Status flag tracking
- PEC/FIFO integration structure

**Remaining:**
- Complete bit-level TX/RX logic
- Implement physical layer FSM
- Connect FIFO read/write controls to FSMs
- Implement arbitration logic
- Refine state transitions
- Add clock stretching support
- Complete slave address matching

## Next Steps

### Immediate (Phase 2 Completion)
1. **Complete Physical Layer FSM:**
   - Bit transmission timing
   - Bit reception sampling
   - ACK/NAK generation and detection
   - Proper SCL/SDA control

2. **Finish Master FSM:**
   - Connect to physical layer
   - Implement byte counting
   - FIFO integration
   - Transaction sequencing

3. **Finish Slave FSM:**
   - Address matching logic
   - Clock stretching
   - Response generation

### Phase 4: Config Registers
```bash
# Generate from PeakRDL
cd peakrdl/
peakrdl generate smbus_regs.rdl -o ../smbus_config_regs.sv
```

### Phase 5: APB Wrapper
- Create `apb4_smbus.sv` following RTC pattern
- Instantiate apb4_slave, smbus_config_regs, smbus_core
- Wire up all interfaces
- Add interrupt aggregation

### Phase 7-9: Verification
- Create Cocotb test infrastructure
- Write basic transaction tests
- Test error conditions
- Verify timing compliance
- Test multi-master scenarios

## References

### SMBus Specification
- **SMBus 2.0:** System Management Bus Specification Version 2.0
- **I2C:** I²C-bus specification and user manual UM10204

### Project References
- **RTC Implementation:** `projects/components/retro_legacy_blocks/rtl/rtc/`
- **FIFO Infrastructure:** `rtl/common/fifo_sync.sv`
- **APB Infrastructure:** `rtl/amba/apb4/apb4_slave.sv`

### Related Tools
- **PeakRDL:** Register definition and generation framework
- **Cocotb:** Python-based verification framework

## Testing

### Unit Tests (To Be Implemented)
- PEC calculation verification
- FIFO operation tests
- Clock divider accuracy
- Timeout detection
- START/STOP condition timing

### Integration Tests (To Be Implemented)
- Master write transactions
- Master read transactions
- Slave response handling
- Block transfers
- PEC verification
- Error recovery

### Compliance Tests (To Be Implemented)
- SMBus 2.0 timing requirements
- Clock stretching behavior
- Timeout thresholds (25-35ms)
- Multi-master arbitration

## Known Limitations

1. **Physical Layer Incomplete:** Bit-level TX/RX logic needs implementation
2. **APB Wrapper Missing:** Top-level integration not yet created
3. **Config Regs Not Generated:** Requires PeakRDL tool execution
4. **No Verification:** Test infrastructure not yet implemented
5. **Slave Mode Basic:** Full slave functionality needs completion
6. **No ARA Support:** Alert Response Address not implemented

## Contribution Guidelines

When continuing this implementation:

1. **Follow RTC Pattern:** Use RTC as reference for structure and style
2. **Maintain Consistency:** Match naming conventions and coding style
3. **Update Status:** Mark phases complete in this README
4. **Document Changes:** Add detailed comments for complex logic
5. **Test Incrementally:** Verify each component before integration

## License

MIT License - See LICENSE file for details

## Authors

- **Initial Implementation:** sean galloway (2024-2025)
- **Architecture:** Following RTLDesignSherpa methodology

---

**Last Updated:** 2025-11-15
**Version:** 0.2.0 (Phase 2 In Progress)
**Status:** 🚧 Under Active Development
