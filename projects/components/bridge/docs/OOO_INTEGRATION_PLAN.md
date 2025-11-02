# Out-of-Order (OOO) Integration Plan for Bridge Generator

**Version:** 1.0
**Date:** 2025-10-26
**Status:** Implementation Plan

---

## Overview

This document describes the plan to integrate bridge_cam into the bridge generator to support out-of-order slave responses.

---

## Changes Required

### 1. Update PortSpec Dataclass

**File:** `projects/components/bridge/bin/bridge_csv_generator.py`

**Location:** Line 48-73

**Change:**
```python
@dataclass
class PortSpec:
    """Specification for a single port (master or slave)"""
    port_name: str          # Unique identifier
    direction: str          # 'master' or 'slave'
    protocol: str           # 'axi4' or 'apb'
    channels: str = 'rw'    # 'rw' (read+write), 'rd' (read-only), 'wr' (write-only)
    prefix: str = ''        # Signal prefix (e.g., 'rapids_m_axi_')
    data_width: int = 0     # Data width in bits
    addr_width: int = 0     # Address width in bits
    id_width: int = 0       # ID width (0 for APB)
    base_addr: int = 0      # Base address for slave (N/A for master)
    addr_range: int = 0     # Address range for slave (N/A for master)
    ooo: bool = False       # NEW: Out-of-order support (slaves only)

    # Internal fields (filled during generation)
    needs_axi2apb: bool = False      # True if APB slave (needs AXI2APB converter)
    needs_width_conv: bool = False   # True if width doesn't match crossbar
    converter_name: str = ''         # Name of converter instance
    needs_bridge_cam: bool = False   # NEW: True if ooo=1 (needs bridge_cam)
    cam_instance_name: str = ''      # NEW: Name of bridge_cam instance

    def has_write_channels(self) -> bool:
        """True if this port has write channels (AW, W, B)"""
        return self.channels in ['rw', 'wr']

    def has_read_channels(self) -> bool:
        """True if this port has read channels (AR, R)"""
        return self.channels in ['rw', 'rd']

    def requires_cam(self) -> bool:
        """True if this slave requires bridge_cam for OOO support"""
        return self.direction == 'slave' and self.ooo
```

### 2. Update parse_ports_csv Function

**File:** `projects/components/bridge/bin/bridge_csv_generator.py`

**Location:** Line 114-200

**Change:**
```python
def parse_ports_csv(csv_path: str) -> Tuple[List[PortSpec], List[PortSpec]]:
    """
    Parse ports.csv file to extract master and slave port specifications

    Returns:
        (masters, slaves) - Lists of PortSpec objects
    """
    masters = []
    slaves = []

    print(f"Parsing ports configuration: {csv_path}")

    with open(csv_path, 'r') as f:
        # ... existing header parsing code ...

        reader = csv.DictReader(lines)
        for row in reader:
            # Skip empty rows
            if not row.get('port_name') or row['port_name'].strip() == '':
                continue

            # Parse CSV fields
            port_name = row['port_name'].strip()
            direction = row['direction'].strip().lower()
            protocol = row['protocol'].strip().lower()
            # channels column is optional, default to 'rw' for backward compatibility
            channels = row.get('channels', 'rw').strip().lower() if row.get('channels') else 'rw'
            prefix = row['prefix'].strip()
            data_width = int(row['data_width'])
            addr_width = int(row['addr_width'])
            id_width_val = parse_csv_value(row['id_width'], 'id_width')
            base_addr_val = parse_csv_value(row['base_addr'], 'base_addr')
            addr_range_val = parse_csv_value(row['addr_range'], 'addr_range')

            # NEW: Parse ooo column (backward compatible)
            ooo_val = False
            if 'ooo' in row and row['ooo']:
                ooo_str = row['ooo'].strip().lower()
                if ooo_str not in ['n/a', 'na', '']:
                    ooo_val = int(ooo_str) == 1

            # Validate channels value
            if channels not in ['rw', 'rd', 'wr']:
                print(f"  WARNING: Invalid channels '{channels}' for {port_name}, defaulting to 'rw'")
                channels = 'rw'

            # Create PortSpec
            port = PortSpec(
                port_name=port_name,
                direction=direction,
                protocol=protocol,
                channels=channels,
                prefix=prefix,
                data_width=data_width,
                addr_width=addr_width,
                id_width=id_width_val if id_width_val is not None else 0,
                base_addr=base_addr_val if base_addr_val is not None else 0,
                addr_range=addr_range_val if addr_range_val is not None else 0,
                ooo=ooo_val  # NEW
            )

            # Add to appropriate list
            if direction == 'master':
                masters.append(port)
                channels_str = f"[{channels.upper()}]" if channels != 'rw' else ""
                print(f"  Master: {port_name} ({protocol.upper()}, {data_width}b data, {channels.upper()}, prefix: {prefix})")
            elif direction == 'slave':
                slaves.append(port)
                ooo_str = " [OOO]" if port.ooo else ""  # NEW
                print(f"  Slave: {port_name} ({protocol.upper()}, {data_width}b data, base=0x{base_addr_val:X}, range=0x{addr_range_val:X}, prefix: {prefix}){ooo_str}")

    return masters, slaves
```

### 3. Add bridge_cam Generation Logic

**New Function to Add:**

```python
def generate_bridge_cam_instance(slave: PortSpec, config: BridgeCSVConfig, module: Module) -> str:
    """
    Generate bridge_cam instance for an out-of-order slave

    Args:
        slave: Slave port specification with ooo=1
        config: Bridge configuration
        module: Module to add instance to

    Returns:
        Instance name of the generated CAM
    """
    if not slave.requires_cam():
        return ""

    cam_name = f"u_{slave.port_name}_cam"
    slave.cam_instance_name = cam_name
    slave.needs_bridge_cam = True

    # Calculate CAM parameters
    tag_width = config.crossbar_id_width
    data_width = max(1, (len(config.masters) - 1).bit_length())  # $clog2(NUM_MASTERS)
    depth = 16  # TODO: Make configurable via CSV
    allow_duplicates = 1  # Mode 2: FIFO ordering for OOO slaves
    pipeline_evict = 0  # Start with combinational

    # Add comment
    module.add_comment(f"")
    module.add_comment(f"Bridge CAM for out-of-order slave: {slave.port_name}")
    module.add_comment(f"Tracks transaction IDs and routes responses back to correct master")

    # Generate instance
    instance = f"""bridge_cam #(
    .TAG_WIDTH({tag_width}),
    .DATA_WIDTH({data_width}),
    .DEPTH({depth}),
    .ALLOW_DUPLICATES({allow_duplicates}),
    .PIPELINE_EVICT({pipeline_evict})
) {cam_name} (
    .clk(aclk),
    .rst_n(aresetn),

    // Entry port (allocation on AW/AR)
    .allocate(/* Connect to AW/AR allocation logic */),
    .allocate_tag(/* Connect to transaction ID */),
    .allocate_data(/* Connect to master index */),

    // Eviction port (deallocation on B/R)
    .deallocate(/* Connect to B/R deallocation logic */),
    .deallocate_tag(/* Connect to response ID */),
    .deallocate_valid(/* Connect to routing logic */),
    .deallocate_data(/* Connect to master select */),
    .deallocate_count(/* Optional: count field */),

    // Status
    .cam_hit(/* Connect to arbiter for duplicate detection */),
    .tags_empty(),
    .tags_full(/* Connect to backpressure logic */),
    .tags_count()
);"""

    module.add_raw(instance)
    return cam_name
```

### 4. Update Bridge Generator Flow

**Integration Points:**

The bridge_cam must be connected at several points in the generated bridge:

#### A. Write Path Allocation (AW Channel)

```systemverilog
// When master issues AW and arbiter grants
logic cam_allocate_aw;
logic [ID_WIDTH-1:0] cam_allocate_tag_aw;
logic [$clog2(NUM_MASTERS)-1:0] cam_allocate_data_aw;

assign cam_allocate_aw = aw_grant_valid & aw_grant_ready;
assign cam_allocate_tag_aw = aw_grant_id;  // From granted master
assign cam_allocate_data_aw = aw_master_index;  // Which master was granted

// Connect to CAM
assign u_slave_cam.allocate = cam_allocate_aw;
assign u_slave_cam.allocate_tag = cam_allocate_tag_aw;
assign u_slave_cam.allocate_data = cam_allocate_data_aw;
```

#### B. Write Path Deallocation (B Channel)

```systemverilog
// When slave returns B response
logic cam_deallocate_b;
logic [ID_WIDTH-1:0] cam_deallocate_tag_b;
logic cam_deallocate_valid_b;
logic [$clog2(NUM_MASTERS)-1:0] cam_deallocate_data_b;

assign cam_deallocate_b = slave_b_valid & slave_b_ready;
assign cam_deallocate_tag_b = slave_b_id;

// Connect to CAM
assign u_slave_cam.deallocate = cam_deallocate_b;
assign u_slave_cam.deallocate_tag = cam_deallocate_tag_b;

// CAM returns master index
assign master_select_b = cam_deallocate_data_b;  // Route to this master
assign master_b_valid[master_select_b] = cam_deallocate_valid_b & slave_b_valid;
```

#### C. Read Path Allocation (AR Channel)

```systemverilog
// When master issues AR and arbiter grants
logic cam_allocate_ar;
logic [ID_WIDTH-1:0] cam_allocate_tag_ar;
logic [$clog2(NUM_MASTERS)-1:0] cam_allocate_data_ar;

assign cam_allocate_ar = ar_grant_valid & ar_grant_ready;
assign cam_allocate_tag_ar = ar_grant_id;  // From granted master
assign cam_allocate_data_ar = ar_master_index;  // Which master was granted

// Connect to CAM (same CAM for both write and read)
assign u_slave_cam.allocate = cam_allocate_aw | cam_allocate_ar;
assign u_slave_cam.allocate_tag = cam_allocate_aw ? cam_allocate_tag_aw : cam_allocate_tag_ar;
assign u_slave_cam.allocate_data = cam_allocate_aw ? cam_allocate_data_aw : cam_allocate_data_ar;
```

#### D. Read Path Deallocation (R Channel, on RLAST)

```systemverilog
// When slave returns R response (deallocate on RLAST)
logic cam_deallocate_r;
logic [ID_WIDTH-1:0] cam_deallocate_tag_r;
logic cam_deallocate_valid_r;
logic [$clog2(NUM_MASTERS)-1:0] cam_deallocate_data_r;

assign cam_deallocate_r = slave_r_valid & slave_r_ready & slave_r_last;
assign cam_deallocate_tag_r = slave_r_id;

// Connect to CAM (same CAM for both write and read)
assign u_slave_cam.deallocate = cam_deallocate_b | cam_deallocate_r;
assign u_slave_cam.deallocate_tag = cam_deallocate_b ? cam_deallocate_tag_b : cam_deallocate_tag_r;

// CAM returns master index
assign master_select_r = cam_deallocate_data_r;  // Route to this master
assign master_r_valid[master_select_r] = cam_deallocate_valid_r & slave_r_valid;
```

---

## Testing Plan

### 1. CSV Configuration Test

Create test CSV with OOO slave:
```csv
port_name,direction,protocol,channels,prefix,data_width,addr_width,id_width,base_addr,addr_range,ooo
master0,master,axi4,rw,m0_,64,32,4,N/A,N/A,N/A
master1,master,axi4,rw,m1_,64,32,4,N/A,N/A,N/A
ddr_slave,slave,axi4,rw,ddr_,64,32,4,0x80000000,0x80000000,1
sram_slave,slave,axi4,rw,sram_,64,32,4,0x40000000,0x10000000,0
```

### 2. Generator Test

Run generator:
```bash
cd projects/components/bridge/bin
python3 bridge_csv_generator.py \
    --ports example_ports_ooo.csv \
    --connectivity example_connectivity.csv \
    --name bridge_ooo_test \
    --output ../rtl/
```

Verify:
- [ ] bridge_cam instantiated for ddr_slave (ooo=1)
- [ ] No bridge_cam for sram_slave (ooo=0)
- [ ] CAM connected to AW/AR allocation paths
- [ ] CAM connected to B/R deallocation paths
- [ ] Proper routing of responses via cam_deallocate_data

### 3. Functional Test

Create testbench:
- Send transactions to OOO slave
- Return responses out-of-order
- Verify correct master receives each response
- Test with duplicate transaction IDs (Mode 2 FIFO ordering)

---

## Implementation Status

- [x] Created BRIDGE_CAM_SPEC.md documentation
- [x] Created example_ports_ooo.csv with ooo column
- [x] Created OOO_INTEGRATION_PLAN.md (this document)
- [ ] Update PortSpec dataclass with ooo field
- [ ] Update parse_ports_csv to read ooo column
- [ ] Add generate_bridge_cam_instance function
- [ ] Integrate CAM into write path (AW→B)
- [ ] Integrate CAM into read path (AR→R)
- [ ] Test with example configuration
- [ ] Document in PRD.md

---

## Notes

### Why Mode 2 (ALLOW_DUPLICATES=1)?

Out-of-order slaves may return responses for the same transaction ID in different order than requested. Mode 2 FIFO ordering ensures:
1. Multiple masters can use the same transaction ID
2. Responses are routed correctly even when out-of-order
3. Count field tracks ordering for correct FIFO behavior

### Why Single CAM for Both Write and Read?

A single CAM can track both write and read transactions because:
1. Transaction IDs are independent between write and read
2. B and R responses have different channels
3. Allocation logic differentiates AW vs AR
4. Deallocation logic differentiates B vs R

Alternative: Use separate CAMs for write and read paths if transaction ID spaces overlap.

---

## Future Enhancements

1. **Configurable DEPTH**: Add `cam_depth` column to CSV
2. **Per-slave PIPELINE_EVICT**: Add `cam_pipeline` column to CSV
3. **CAM Status Monitoring**: Export tags_full, tags_count for debugging
4. **Multiple CAMs**: Support separate write/read CAMs if needed
5. **Dynamic Sizing**: Calculate DEPTH based on expected outstanding transactions

---

**End of Plan**
