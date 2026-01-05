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

# AXI Splitter Testbench Framework Overview

The AXI Splitter testbench framework provides comprehensive verification for AXI transaction splitting functionality. This framework is designed to test AXI master components that need to split large transactions crossing memory boundaries into smaller, boundary-aligned transactions.

## Framework Architecture

### Core Components

The framework consists of six main Python files organized into read and write splitter components:

**Read Splitter Components:**
- `axi_read_splitter_packets.py` - Packet definitions and field configurations
- `axi_read_splitter_scoreboard.py` - Transaction tracking and verification
- `axi_read_splitter_tb.py` - Main testbench implementation

**Write Splitter Components:**
- `axi_write_splitter_packets.py` - Write packet definitions and field configurations  
- `axi_write_splitter_scoreboard.py` - Write transaction tracking and verification
- `axi_write_splitter_tb.py` - Main write testbench implementation

### Design Philosophy

**Realistic Testing Approach:**
- **No Address Wraparound**: All testing focuses on legitimate boundary crossing scenarios without impossible edge cases
- **Safe Address Regions**: Tests use addresses in safe regions (< MAX_ADDR/2) to avoid wraparound complications
- **Data Width Awareness**: Dynamic test generation based on actual data width configurations
- **Boundary Alignment**: Proper address alignment to data width boundaries

## AXI Read Splitter Framework

### Key Features

**Transaction Flow:**
1. **Address Request (AR)**: Original large transaction submitted
2. **Boundary Detection**: Automatic detection of boundary crossings
3. **Transaction Splitting**: Large transaction split into boundary-aligned smaller transactions
4. **Data Response (R)**: Multiple split responses received and consolidated
5. **Verification**: End-to-end data integrity and timing verification

**Verification Capabilities:**
- Split transaction correlation using transaction IDs
- Data integrity verification across split boundaries
- Response consolidation validation
- Timing relationship verification
- Comprehensive error detection and reporting

### Packet Structure

**AXIAddressPacket**: Represents AXI AR (Address Read) channel packets
- Transaction ID, address, length, size, burst type
- Cache, protection, QoS attributes
- User-defined signals
- Boundary crossing detection methods

**AXIDataPacket**: Represents AXI R (Read Data) channel packets  
- Transaction ID, read data, response status
- Last transfer indication
- User-defined signals
- Response status decoding

**SplitInfoPacket**: Tracking information for split transactions
- Original address and transaction ID
- Split count and boundary information
- Timing and correlation data

## AXI Write Splitter Framework

### Key Features

**Three-Channel Write Flow:**
1. **Write Address (AW)**: Address phase with potential splitting
2. **Write Data (W)**: Data phase with proper distribution across splits
3. **Write Response (B)**: Response consolidation from multiple splits

**Write-Specific Verification:**
- Write data generation and transmission coordination
- WLAST verification for split boundaries
- Single response per original transaction (regardless of splits)
- Write strobe pattern generation and verification
- Data integrity verification across split transactions

### Write Packet Structure

**AXIWriteAddressPacket**: Represents AXI AW (Address Write) channel packets
- Similar to read address packets but for write transactions
- Write-specific burst and cache attributes
- Protection and QoS for write operations

**AXIWriteDataPacket**: Represents AXI W (Write Data) channel packets
- Write data and byte enable strobes
- Last transfer indication (WLAST)
- User-defined write attributes

**AXIWriteResponsePacket**: Represents AXI B (Write Response) channel packets
- Transaction ID and response status
- Write completion indication
- User-defined response attributes

**WriteSplitInfoPacket**: Write-specific split tracking information
- Write transaction correlation data
- Data distribution tracking
- Response consolidation information

## Scoreboard Architecture

### Read Splitter Scoreboard

**Transaction Tracking:**
- Upstream transaction monitoring (original requests)
- Downstream transaction monitoring (split requests)
- Response correlation and consolidation verification
- Split information tracking and validation

**Verification Features:**
- Data integrity checking across splits
- Response timing validation
- Transaction ID correlation
- Boundary crossing verification
- Comprehensive error reporting with context

### Write Splitter Scoreboard

**Enhanced Write Tracking:**
- Three-channel coordination (AW → W → B)
- Write data distribution verification
- Response consolidation validation
- WLAST signal verification at boundaries

**Write-Specific Checks:**
- Data integrity across write splits
- Proper write strobe patterns
- Response timing and consolidation
- Error detection and context reporting

## Testbench Implementation

### Read Splitter Testbench

**Test Generation:**
- Dynamic boundary crossing test cases
- Multiple data width support (32, 64, 128, 256, 512 bits)
- Realistic address generation with safety checks
- Randomized transaction parameters within safe bounds

**Verification Flow:**
- Transaction submission with boundary detection
- Split monitoring and correlation
- Data response collection and verification
- End-to-end integrity checking

### Write Splitter Testbench  

**Write Test Generation:**
- Write-specific boundary crossing scenarios
- Data pattern generation for write verification
- Write strobe pattern testing
- Response consolidation verification

**Write Verification Flow:**
- Write address submission and splitting
- Write data distribution across splits
- Write response collection and consolidation
- Complete write transaction verification

## Usage Patterns

### Extending the Framework

**Custom Test Scenarios:**
```python
class CustomAxiSplitterTest(AxiReadSplitterTB):
    def __init__(self, dut):
        super().__init__(dut)
        # Add custom configuration
        
    async def run_custom_scenario(self):
        # Implement custom test logic
        await self.custom_boundary_test()
```

**Configuration Customization:**
```python
# Custom boundary sizes
tb.configure_boundary_size(0x1000)  # 4KB boundaries

# Custom data widths  
tb.configure_data_width(512)  # 512-bit data width

# Custom address ranges
tb.configure_safe_address_range(0x1000, 0x7FFFFFFF)
```

## Error Handling and Debugging

### Comprehensive Error Reporting

**Context-Rich Error Messages:**
- Transaction context with timing information
- Boundary crossing analysis
- Data integrity violation details
- Correlation failure analysis

**Debug Features:**
- Transaction state tracking
- Timing analysis and reporting
- Split correlation visualization
- Data pattern verification

### Error Categories

**Read Splitter Errors:**
- Split count mismatches
- Data integrity violations
- Response correlation failures
- Timing constraint violations

**Write Splitter Errors:**
- Write data distribution errors
- WLAST signal violations
- Response consolidation failures
- Three-channel coordination errors

## Performance and Statistics

### Metrics Tracking

**Transaction Statistics:**
- Total transactions processed
- Split transactions generated
- Boundary crossings detected
- Verification checks performed
- Error counts and categories

**Performance Metrics:**
- Transaction throughput
- Split overhead analysis
- Verification timing
- Resource utilization

### Reporting

**Comprehensive Reports:**
- Test execution summary
- Transaction statistics
- Error analysis and categorization
- Performance metrics
- Boundary crossing analysis

This framework provides a robust foundation for verifying AXI splitter functionality with comprehensive coverage, realistic testing scenarios, and detailed error analysis capabilities.