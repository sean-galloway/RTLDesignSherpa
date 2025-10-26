### Channel-Specific Masters (Phase 2 Feature)

#### Overview

**Phase 2 Key Feature:** Support for channel-specific AXI4 masters that only implement needed channels (write-only, read-only, or full).

**Why This Matters:**
- Real hardware often has dedicated read or write masters
- Full 5-channel interfaces waste resources for dedicated masters
- Matches actual accelerator architectures (RAPIDS, STREAM)
- Reduces port count, logic, and synthesis time

#### The Problem

**Traditional AXI4 Crossbar Generation:**

All masters get all 5 AXI4 channels, even if they only perform reads or writes:

```systemverilog
// ❌ WASTEFUL: Write-only master gets unused read channels
input  logic [63:0]  rapids_descr_m_axi_awaddr,  // ✅ USED (write address)
input  logic [511:0] rapids_descr_m_axi_wdata,   // ✅ USED (write data)
output logic [7:0]   rapids_descr_m_axi_bid,     // ✅ USED (write response)
input  logic [63:0]  rapids_descr_m_axi_araddr,  // ❌ UNUSED (read address)
output logic [511:0] rapids_descr_m_axi_rdata,   // ❌ UNUSED (read data)
```

**Resource Waste:**
- 50% of ports unused for dedicated masters
- Width converters instantiated for unused directions
- Internal crossbar wiring for unused channels
- Verification coverage for unused paths

#### The Solution: channels Field

**CSV Configuration Enhancement:**

Add `channels` field to `ports.csv`:

```csv
port_name,direction,protocol,channels,prefix,data_width,addr_width,id_width,base_addr,addr_range
rapids_descr_wr,master,axi4,wr,rapids_descr_m_axi_,512,64,8,N/A,N/A
rapids_sink_wr,master,axi4,wr,rapids_sink_m_axi_,512,64,8,N/A,N/A
rapids_src_rd,master,axi4,rd,rapids_src_m_axi_,512,64,8,N/A,N/A
stream_master,master,axi4,rw,stream_m_axi_,512,64,8,N/A,N/A
cpu_master,master,axi4,rw,cpu_m_axi_,64,32,4,N/A,N/A
```

**Channel Values:**
- **`rw`** - Full read/write master (all 5 channels: AW, W, B, AR, R)
- **`wr`** - Write-only master (3 channels: AW, W, B)
- **`rd`** - Read-only master (2 channels: AR, R)

**Backward Compatibility:**
- `channels` field is optional
- Defaults to `rw` if not specified
- Existing CSV files work unchanged

#### Generated RTL Differences

**Write-Only Master (`channels=wr`):**

```systemverilog
// Master port: rapids_descr_wr (512b AXI4 [WR], prefix: rapids_descr_m_axi_)
// Write Address Channel
input  logic [63:0]   rapids_descr_m_axi_awaddr,
input  logic [7:0]    rapids_descr_m_axi_awid,
input  logic [7:0]    rapids_descr_m_axi_awlen,
input  logic [2:0]    rapids_descr_m_axi_awsize,
input  logic [1:0]    rapids_descr_m_axi_awburst,
input  logic          rapids_descr_m_axi_awlock,
input  logic [3:0]    rapids_descr_m_axi_awcache,
input  logic [2:0]    rapids_descr_m_axi_awprot,
input  logic          rapids_descr_m_axi_awvalid,
output logic          rapids_descr_m_axi_awready,
// Write Data Channel
input  logic [511:0]  rapids_descr_m_axi_wdata,
input  logic [63:0]   rapids_descr_m_axi_wstrb,
input  logic          rapids_descr_m_axi_wlast,
input  logic          rapids_descr_m_axi_wvalid,
output logic          rapids_descr_m_axi_wready,
// Write Response Channel
output logic [7:0]    rapids_descr_m_axi_bid,
output logic [1:0]    rapids_descr_m_axi_bresp,
output logic          rapids_descr_m_axi_bvalid,
input  logic          rapids_descr_m_axi_bready

// ✅ NO READ CHANNELS (araddr, arid, rdata, etc.)
```

**Read-Only Master (`channels=rd`):**

```systemverilog
// Master port: rapids_src_rd (512b AXI4 [RD], prefix: rapids_src_m_axi_)
// Read Address Channel
input  logic [63:0]   rapids_src_m_axi_araddr,
input  logic [7:0]    rapids_src_m_axi_arid,
input  logic [7:0]    rapids_src_m_axi_arlen,
input  logic [2:0]    rapids_src_m_axi_arsize,
input  logic [1:0]    rapids_src_m_axi_arburst,
input  logic          rapids_src_m_axi_arlock,
input  logic [3:0]    rapids_src_m_axi_arcache,
input  logic [2:0]    rapids_src_m_axi_arprot,
input  logic          rapids_src_m_axi_arvalid,
output logic          rapids_src_m_axi_arready,
// Read Data Channel
output logic [511:0]  rapids_src_m_axi_rdata,
output logic [7:0]    rapids_src_m_axi_rid,
output logic [1:0]    rapids_src_m_axi_rresp,
output logic          rapids_src_m_axi_rlast,
output logic          rapids_src_m_axi_rvalid,
input  logic          rapids_src_m_axi_rready

// ✅ NO WRITE CHANNELS (awaddr, awid, wdata, bid, etc.)
```

**Full Master (`channels=rw`):**

```systemverilog
// Master port: stream_master (512b AXI4, prefix: stream_m_axi_)
// Write Address Channel
input  logic [63:0]   stream_m_axi_awaddr,
// ... (all write channel signals)
// Read Address Channel
input  logic [63:0]   stream_m_axi_araddr,
// ... (all read channel signals)

// ✅ ALL 5 CHANNELS PRESENT
```

#### Width Converter Optimization

**Separate Write and Read Converters:**

For channel-specific masters, width converters are only instantiated for needed directions:

**Write-Only Master (512b → 512b crossbar):**

```systemverilog
// Width Converter (WRITE) - Master 0: rapids_descr_wr [WR]
// No converter needed - direct connection (same width)
assign xbar_m_awaddr[0]  = rapids_descr_m_axi_awaddr;
assign xbar_m_awid[0]    = rapids_descr_m_axi_awid;
// ... (write channel direct assignments)

// ✅ NO READ CONVERTER INSTANCE (master doesn't have read channels)
```

**Read-Only Master (512b → 512b crossbar):**

```systemverilog
// Width Converter (READ) - Master 2: rapids_src_rd [RD]
// No converter needed - direct connection (same width)
assign xbar_m_araddr[2]  = rapids_src_m_axi_araddr;
assign xbar_m_arid[2]    = rapids_src_m_axi_arid;
// ... (read channel direct assignments)

// ✅ NO WRITE CONVERTER INSTANCE (master doesn't have write channels)
```

**Full Master with Width Mismatch (64b → 512b crossbar):**

```systemverilog
// Width Converter (WRITE) - Master 4: cpu_master
axi4_dwidth_converter_wr #(
    .S_AXI_DATA_WIDTH(64),
    .M_AXI_DATA_WIDTH(512),
    // ...
) u_wconv_m4_wr (
    .aclk         (aclk),
    .aresetn      (aresetn),
    // Slave interface (64b external)
    .s_axi_awaddr (cpu_m_axi_awaddr),
    // Master interface (512b crossbar)
    .m_axi_awaddr (xbar_m_awaddr[4]),
    // ...
);

// Width Converter (READ) - Master 4: cpu_master
axi4_dwidth_converter_rd #(
    .S_AXI_DATA_WIDTH(64),
    .M_AXI_DATA_WIDTH(512),
    // ...
) u_wconv_m4_rd (
    .aclk         (aclk),
    .aresetn      (aresetn),
    // Slave interface (64b external)
    .s_axi_araddr (cpu_m_axi_araddr),
    // Master interface (512b crossbar)
    .m_axi_araddr (xbar_m_araddr[4]),
    // ...
);

// ✅ BOTH CONVERTERS (full master with width mismatch)
```

#### Direct Connection Optimization

**Channel-Aware Wiring:**

When no width conversion is needed, only existing channels are wired:

**Write-Only Master Direct Connection:**

```systemverilog
// Master 0: rapids_descr_wr [WR] (direct connection)

// Write channels only
assign xbar_m_awaddr[0]  = rapids_descr_m_axi_awaddr;
assign xbar_m_awid[0]    = rapids_descr_m_axi_awid;
assign xbar_m_awlen[0]   = rapids_descr_m_axi_awlen;
// ... (all write channel signals)

assign rapids_descr_m_axi_bid    = xbar_m_bid[0];
assign rapids_descr_m_axi_bresp  = xbar_m_bresp[0];
assign rapids_descr_m_axi_bvalid = xbar_m_bvalid[0];
assign xbar_m_bready[0] = rapids_descr_m_axi_bready;

// ✅ NO READ CHANNEL ASSIGNMENTS (signals don't exist)
```

**Read-Only Master Direct Connection:**

```systemverilog
// Master 2: rapids_src_rd [RD] (direct connection)

// Read channels only
assign xbar_m_araddr[2]  = rapids_src_m_axi_araddr;
assign xbar_m_arid[2]    = rapids_src_m_axi_arid;
assign xbar_m_arlen[2]   = rapids_src_m_axi_arlen;
// ... (all read channel signals)

assign rapids_src_m_axi_rdata  = xbar_m_rdata[2];
assign rapids_src_m_axi_rid    = xbar_m_rid[2];
assign rapids_src_m_axi_rresp  = xbar_m_rresp[2];
assign rapids_src_m_axi_rvalid = xbar_m_rvalid[2];
assign xbar_m_rready[2] = rapids_src_m_axi_rready;

// ✅ NO WRITE CHANNEL ASSIGNMENTS (signals don't exist)
```

#### Resource Savings

**Example: 3 Masters, 2 Slaves, All Channel-Specific**

**Configuration:**
```csv
rapids_descr_wr,master,axi4,wr,rapids_descr_m_axi_,512,64,8,N/A,N/A
rapids_sink_wr,master,axi4,wr,rapids_sink_m_axi_,512,64,8,N/A,N/A
rapids_src_rd,master,axi4,rd,rapids_src_m_axi_,512,64,8,N/A,N/A
```

**Port Count Comparison:**

| Master | Traditional (rw) | Channel-Specific | Reduction |
|--------|------------------|------------------|-----------|
| rapids_descr_wr | 61 signals | 37 signals | -39% |
| rapids_sink_wr | 61 signals | 37 signals | -39% |
| rapids_src_rd | 61 signals | 24 signals | -61% |
| **Total** | **183 signals** | **98 signals** | **-46%** |

**Logic Savings:**
- No unused width converter instances
- No unused crossbar channel wiring
- Reduced multiplexer/demultiplexer logic
- Faster synthesis and place & route

#### Implementation Details

**PortSpec Class Enhancement:**

```python
@dataclass
class PortSpec:
    port_name: str
    direction: str
    protocol: str
    channels: str = 'rw'  # NEW: Default to full read/write
    prefix: str = ''
    data_width: int = 0
    # ... other fields

    def has_write_channels(self) -> bool:
        """True if this port has write channels (AW, W, B)"""
        return self.channels in ['rw', 'wr']

    def has_read_channels(self) -> bool:
        """True if this port has read channels (AR, R)"""
        return self.channels in ['rw', 'rd']
```

**CSV Validation:**

```python
# Validate channels value
if channels not in ['rw', 'rd', 'wr']:
    print(f"  WARNING: Invalid channels '{channels}' for {port_name}, defaulting to 'rw'")
    channels = 'rw'
```

**Conditional Generation:**

```python
# Generate port signals based on channel type
if port.has_write_channels():
    port_str += generate_write_channels(port)

if port.has_read_channels():
    port_str += generate_read_channels(port)
```

#### Usage Example

**RAPIDS-Style Configuration:**

```csv
# example_ports_channels.csv
port_name,direction,protocol,channels,prefix,data_width,addr_width,id_width,base_addr,addr_range
rapids_descr_wr,master,axi4,wr,rapids_descr_m_axi_,512,64,8,N/A,N/A
rapids_sink_wr,master,axi4,wr,rapids_sink_m_axi_,512,64,8,N/A,N/A
rapids_src_rd,master,axi4,rd,rapids_src_m_axi_,512,64,8,N/A,N/A
stream_master,master,axi4,rw,stream_m_axi_,512,64,8,N/A,N/A
cpu_master,master,axi4,rw,cpu_m_axi_,64,32,4,N/A,N/A
apb_periph0,slave,apb,rw,apb0_,32,32,N/A,0x00000000,0x00010000
ddr_controller,slave,axi4,rw,ddr_s_axi_,512,64,8,0x80000000,0x80000000
sram_buffer,slave,axi4,rw,sram_s_axi_,512,48,8,0x40000000,0x10000000
```

**Generate:**

```bash
python3 bridge_csv_generator.py \
    --ports example_ports_channels.csv \
    --connectivity example_connectivity_channels.csv \
    --name bridge_channels_demo \
    --output /tmp/bridge_test/
```

**Verification:**

```bash
# Verify write-only master has NO read channels
grep -c "rapids_descr_m_axi_ar\|rapids_descr_m_axi_r[^e]" bridge_channels_demo.sv
# Output: 0 ✅

# Verify read-only master has NO write channels
grep -c "rapids_src_m_axi_aw\|rapids_src_m_axi_w[^a]\|rapids_src_m_axi_b" bridge_channels_demo.sv
# Output: 0 ✅
```

#### Benefits Summary

**Resource Efficiency:**
- 40-60% fewer ports for dedicated masters
- Only necessary width converters instantiated
- Reduced internal crossbar wiring
- Faster synthesis and smaller netlists

**Design Clarity:**
- CSV clearly shows master capabilities
- Generated RTL matches actual hardware
- Easier verification (no unused paths)
- Self-documenting configuration

**Real-World Applicability:**
- Matches RAPIDS accelerator architecture
- Matches STREAM datapath architecture
- Common pattern in custom SoCs
- FPGA resource optimization

---

**Next:** [2.5 - Converter Insertion](05_converter_insertion.md)
