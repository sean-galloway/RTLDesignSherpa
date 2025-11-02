# cam_tag_perf.sv Analysis - Extract Before Deletion

**Date:** 2025-10-26
**Purpose:** Document key features of cam_tag_perf.sv before removal from repository
**Source:** `projects/components/bridge/rtl/cam_tag_perf.sv`

---

## Module Overview

`cam_tag_perf` is a specialized CAM designed for transaction ID tracking with automatic ID generation and data payload storage.

### Key Innovation vs. cam_tag.sv

**cam_tag.sv (current repository baseline):**
- Tracks tag presence/absence only
- No associated data storage
- Tag provided by user

**cam_tag_perf.sv (legacy, to be removed):**
- **Auto-generates IDs** using internal counter
- **Stores associated data** (master_index, metadata) with each tag
- **Retrieves data** on lookup/deallocation

---

## Critical Features to Preserve

### 1. Dual Array Architecture

**Concept:** Parallel storage of tags and associated data

```systemverilog
logic [N-1:0]     r_tag_array [0:DEPTH-1];  // Auto-generated IDs
logic [N-1:0]     r_id_array  [0:DEPTH-1];  // User data (master_index)
logic [DEPTH-1:0] r_valid;                   // Valid bit per entry
```

**Why Important:**
- Tag array: Stores auto-generated transaction IDs
- ID array: Stores associated payload (e.g., which master initiated transaction)
- On lookup: Returns r_id_array[match_loc], not just "tag exists"

**Bridge Use Case:**
```
Allocation:
  r_tag_array[slot] <= auto_generated_id  // Bridge assigns unique ID
  r_id_array[slot]  <= master_index       // Remember which master

Lookup (on response):
  match = search r_tag_array for response_id
  master = r_id_array[match]  // ← KEY: Retrieve which master to route to
```

### 2. Auto-ID Generation with Counter

**Concept:** CAM generates unique IDs automatically

```systemverilog
logic [N-2:0] r_ptr;  // Running counter for ID generation

// On allocation
if (i_mark_valid && !ow_tags_full && ENABLE) begin
    r_tag_array[w_next_valid_loc] <= {HI_BIT, r_ptr};  // Auto ID
    r_id_array[w_next_valid_loc]  <= i_tag_in_valid;  // User data
    r_valid[w_next_valid_loc]     <= 1'b1;
    r_ptr <= r_ptr + 1'b1;  // Increment for next ID
end

// Current ID output
assign o_cur_id = {HI_BIT, r_ptr};
```

**Why Important:**
- Automatic ID management prevents ID collisions
- Bridge doesn't need to track next available ID
- HI_BIT parameter allows ID namespace partitioning

**Bridge Application:**
- Each slave could have its own CAM with different HI_BIT
- Example: Slave 0 IDs = 0x00-0x7F, Slave 1 IDs = 0x80-0xFF

### 3. Data Retrieval on Deallocation

**Concept:** Return associated data when transaction completes

```systemverilog
// Find matching entry for deallocation
always_comb begin
    w_match_invalid_loc = -1;
    for (j = 0; j < DEPTH; j++)
        if (r_valid[j] == 1'b1 && i_tag_in_invalid == r_tag_array[j])
            w_match_invalid_loc = j;
end

// Output: Retrieved data from matched entry
assign ow_ret_id = r_id_array[w_match_invalid_loc];  // ← KEY OUTPUT
```

**Why Important:**
- Single operation: deallocate + retrieve data
- Bridge use: On B/R response, get master_index in same cycle as freeing entry
- More efficient than separate lookup + deallocate

**Usage Pattern:**
```systemverilog
// When B response arrives
.i_mark_invalid(b_response_valid && b_response_ready),
.i_tag_in_invalid(b_response_id),
.ow_ret_id(master_index_for_routing)  // ← Use immediately for demux
```

### 4. Full/Empty Status Signals

```systemverilog
assign ow_tags_empty = ~|r_valid;  // No active transactions
assign ow_tags_full  =  &r_valid;  // All slots occupied
```

**Why Important:**
- `ow_tags_full`: Apply backpressure (stop accepting new transactions)
- `ow_tags_empty`: Idle detection, power gating opportunity
- Simple, efficient: Single reduction operation

---

## Interface Comparison

### cam_tag_perf Interface

```systemverilog
module cam_tag_perf #(
    parameter int ENABLE = 1,
    parameter int HI_BIT = 0,      // ← ID namespace partitioning
    parameter int N = 8,
    parameter int DEPTH = 16
)(
    input  logic               i_clk,
    input  logic               i_rst_n,

    // ALLOCATE: Store new transaction
    input  logic               i_mark_valid,
    input  logic [N-1:0]       i_tag_in_valid,    // User data (master_index)

    // DEALLOCATE: Free transaction, return data
    input  logic               i_mark_invalid,
    input  logic [N-1:0]       i_tag_in_invalid,  // Which ID to free

    // STATUS
    output logic               ow_tags_empty,
    output logic               ow_tags_full,
    output logic [N-1:0]       o_cur_id,          // ← Next auto ID
    output logic [N-1:0]       ow_ret_id          // ← Retrieved data
);
```

### Needed for Bridge: cam_tag_bridge Interface

```systemverilog
module cam_tag_bridge #(
    parameter int TAG_WIDTH = 8,   // Transaction ID width
    parameter int DATA_WIDTH = 8,  // Payload width (master_index)
    parameter int DEPTH = 16,
    parameter int ENABLE = 1
)(
    input  logic                     clk,
    input  logic                     rst_n,

    // ALLOCATE
    input  logic                     allocate,
    input  logic [TAG_WIDTH-1:0]     allocate_tag,   // ← User provides ID
    input  logic [DATA_WIDTH-1:0]    allocate_data,  // Payload (master_index)

    // LOOKUP (separate from deallocation)
    input  logic [TAG_WIDTH-1:0]     lookup_tag,
    output logic                     lookup_valid,
    output logic [DATA_WIDTH-1:0]    lookup_data,    // ← Retrieved payload

    // DEALLOCATE
    input  logic                     deallocate,
    input  logic [TAG_WIDTH-1:0]     deallocate_tag,

    // STATUS
    output logic                     tags_empty,
    output logic                     tags_full,
    output logic [$clog2(DEPTH):0]   tags_count      // ← New: occupancy
);
```

**Key Differences:**
1. **ID Source:**
   - cam_tag_perf: Auto-generates IDs (o_cur_id output)
   - cam_tag_bridge: User provides IDs (allocate_tag input)

2. **Lookup vs. Deallocation:**
   - cam_tag_perf: Combined (retrieve data on deallocation only)
   - cam_tag_bridge: Separate (can lookup without deallocating)

3. **Occupancy Counter:**
   - cam_tag_perf: No counter (only full/empty flags)
   - cam_tag_bridge: Explicit tags_count for monitoring

---

## Design Patterns to Adopt

### Pattern 1: Priority Encoder for Next Free Slot

```systemverilog
// Scan from high to low, last match wins (lowest free index)
always_comb begin
    w_next_valid_loc = -1;
    for (i = DEPTH-1; i >= 0; i--)
        if (r_valid[i] == 1'b0)
            w_next_valid_loc = i;
end
```

**Why This Direction:**
- Scanning high→low with assignment on each match
- Final w_next_valid_loc contains lowest free index
- Synthesizes to priority encoder

**Alternative (same result):**
```systemverilog
// Scan low to high, break on first match
always_comb begin
    w_next_valid_loc = -1;
    for (i = 0; i < DEPTH; i++)
        if (r_valid[i] == 1'b0 && w_next_valid_loc == -1)
            w_next_valid_loc = i;
end
```

**Adopt:** Either pattern works, high→low is more concise.

### Pattern 2: Match Location Search

```systemverilog
// Find matching tag (last match wins if duplicates exist)
always_comb begin
    w_match_invalid_loc = -1;
    for (j = 0; j < DEPTH; j++)
        if (r_valid[j] == 1'b1 && i_tag_in_invalid == r_tag_array[j])
            w_match_invalid_loc = j;
end
```

**Why Low→High:**
- If duplicate IDs exist (should never happen), higher index wins
- Doesn't matter in correct usage (unique IDs)

**Adopt:** This pattern works well, matches cam_tag.sv approach.

### Pattern 3: Single-Cycle Allocation/Deallocation

```systemverilog
always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        // Reset
    end else begin
        if (i_mark_valid && !ow_tags_full && ENABLE) begin
            // Allocate
        end
        if (i_mark_invalid) begin  // ← NOT else-if
            // Deallocate
        end
    end
end
```

**Why Independent:**
- Allow allocate and deallocate in same cycle
- Useful when one transaction completes as another starts
- Correctly handles count (alloc+dealloc = no change)

**Adopt:** Use separate if blocks, not else-if.

---

## What NOT to Adopt

### 1. Auto-ID Generation

**Don't Adopt:**
```systemverilog
logic [N-2:0] r_ptr;
r_tag_array[slot] <= {HI_BIT, r_ptr};  // Auto-generated
r_ptr <= r_ptr + 1'b1;
```

**Why:**
- Bridge masters provide their own transaction IDs
- CAM must store master's ID, not generate new one
- Auto-ID would break AXI4 protocol compliance

**Bridge Needs:**
- Store awid/arid from master
- Return same ID on bid/rid to master
- CAM is lookup table, not ID generator

### 2. HI_BIT Parameter

**Don't Adopt:**
```systemverilog
parameter int HI_BIT = 0,
o_cur_id = {HI_BIT, r_ptr};
```

**Why:**
- Intended for ID namespace partitioning across multiple CAMs
- Adds complexity without clear benefit for bridge
- Bridge CAMs are already partitioned by slave index

**Alternative:**
- Separate CAM per slave already provides isolation
- No need for additional namespace bits

### 3. Combined Deallocation + Retrieval Only

**Don't Adopt:**
- cam_tag_perf only returns data on deallocation (ow_ret_id)
- No separate lookup operation

**Bridge Needs:**
- Lookup without deallocating (for monitoring, debug)
- Deallocation separate from retrieval
- More flexible interface

---

## Implementation Recommendations

### Adopt from cam_tag_perf:

1. **Dual array architecture:**
   ```systemverilog
   logic [TAG_WIDTH-1:0]  r_tag_array [DEPTH];
   logic [DATA_WIDTH-1:0] r_data_array [DEPTH];  // ← Store master_index
   logic [DEPTH-1:0]      r_valid;
   ```

2. **Priority encoder for free slot:**
   ```systemverilog
   always_comb begin
       w_next_free = -1;
       for (int i = DEPTH-1; i >= 0; i--)
           if (r_valid[i] == 1'b0)
               w_next_free = i;
   end
   ```

3. **Match location search:**
   ```systemverilog
   always_comb begin
       w_match = -1;
       for (int i = 0; i < DEPTH; i++)
           if (r_valid[i] && lookup_tag == r_tag_array[i])
               w_match = i;
   end
   ```

4. **Independent alloc/dealloc:**
   ```systemverilog
   if (allocate && !tags_full) begin /* alloc */ end
   if (deallocate) begin /* dealloc */ end  // NOT else-if
   ```

5. **Full/empty status:**
   ```systemverilog
   assign tags_empty = ~|r_valid;
   assign tags_full  =  &r_valid;
   ```

### Don't Adopt from cam_tag_perf:

1. Auto-ID generation (r_ptr, o_cur_id)
2. HI_BIT parameter
3. Combined deallocation+retrieval only

### Add to Bridge CAM:

1. **Separate lookup interface** (query without deallocating)
2. **Occupancy counter** (tags_count for monitoring)
3. **Separate TAG_WIDTH and DATA_WIDTH** parameters
4. **Reset macro usage** (repo standard)
5. **FPGA synthesis attributes** (for data arrays)

---

## Usage Example (How It Would Be Used in Bridge)

### Hypothetical Integration (cam_tag_perf style):

```systemverilog
// PER SLAVE: Track write transactions
cam_tag_perf #(
    .N(ID_WIDTH + $clog2(NUM_MASTERS)),  // Store both
    .DEPTH(16),
    .HI_BIT(slave_id[7])  // Namespace by slave
) u_write_cam [NUM_SLAVES-1:0] (
    .i_clk(aclk),
    .i_rst_n(aresetn),

    // Allocate when AW handshake completes
    .i_mark_valid(awvalid[s] && awready[s]),
    .i_tag_in_valid({master_idx, awid[s]}),  // Store master + ID
    .o_cur_id(next_available_id[s]),  // ← Not used in bridge!

    // Deallocate when B response completes
    .i_mark_invalid(bvalid[s] && bready[s]),
    .i_tag_in_invalid({don't_care, bid[s]}),  // Search by ID only
    .ow_ret_id(b_master_route[s]),  // ← Route B to this master

    // Status
    .ow_tags_full(write_cam_full[s]),
    .ow_tags_empty(write_cam_empty[s])
);
```

**Problems with This Approach:**
1. o_cur_id unused (waste)
2. HI_BIT complexity for no benefit
3. Can't lookup without deallocating (debugging difficult)
4. No occupancy counter (monitoring blind)

---

## Checklist: Information Captured

Before deleting cam_tag_perf.sv, confirm these concepts are documented:

- [x] Dual array architecture (tag + data)
- [x] Data storage alongside tags (r_id_array)
- [x] Data retrieval on match (ow_ret_id output)
- [x] Priority encoder for next free slot
- [x] Match location search pattern
- [x] Independent allocate/deallocate (not else-if)
- [x] Full/empty status generation
- [x] Auto-ID generation (document but don't adopt)
- [x] HI_BIT namespace (document but don't adopt)
- [x] Why bridge needs different interface

---

## Recommended Next Steps

1. **Review this document** - Confirm all critical features captured
2. **Delete cam_tag_perf.sv** - No longer needed, concepts documented
3. **Create cam_tag_bridge.sv** - New module using adopted patterns
4. **Reference this doc** - During cam_tag_bridge implementation

---

## Summary

**Keep These Concepts:**
- Dual array architecture for tag + associated data
- Priority encoder for free slot allocation
- Parallel search for tag matching
- Independent allocate/deallocate operations
- Simple full/empty status flags

**Discard These Features:**
- Auto-ID generation (bridge provides IDs)
- HI_BIT parameter (unnecessary complexity)
- Combined deallocation+retrieval only (too restrictive)

**Add for Bridge:**
- Separate lookup interface
- Occupancy counter
- User-provided tag storage
- Repository coding standards (reset macros, FPGA attributes)

---

## Actual Usage Example: hbm2e_shim_perf.v

**Purpose:** Document how cam_tag_perf was actually used in production for ID replacement

**File:** `projects/components/bridge/rtl/hbm2e_shim_perf.v` (to be deleted with cam_tag_perf.sv)

### Architecture Overview

The HBM2E shim sits between an AXI master and HBM2E memory controller to solve ID space limitations:

```
AXI Master                    hbm2e_shim_perf                    HBM2E Controller
(Uses IDs: 0-255)            (ID replacement layer)              (Supports IDs: 0-127)
     |                              |                                      |
     | AWID = 42                    |                                      |
     |----------------------------->|                                      |
     |                              | Store original ID (42)               |
     |                              | Generate new ID (o_cur_id = 17)      |
     |                              |------------------------------------->|
     |                              |                    AWID = 17         |
     |                              |                                      |
     |                              |<-------------------------------------|
     |                              |                    BID = 17          |
     |                              | Lookup: BID=17 → Original ID=42      |
     |<-----------------------------|                                      |
     | BID = 42                     |                                      |
```

### Dual CAM Architecture

**Two separate CAM instances:**

1. **Write Path CAM (AW → B):**
```systemverilog
cam_tag_perf #(
    .ENABLE(1),
    .HI_BIT(0),          // Namespace: IDs 0x00-0x7F
    .N(8),
    .DEPTH(64)
) u_aw_cam_tag (
    .i_clk(clk),
    .i_rst_n(aresetn_safe),

    // Allocate: When AW handshake completes
    .i_mark_valid(i_axi_shim_slv_awvalid & o_axi_shim_slv_awready),
    .i_tag_in_valid(axi_shim_slv_awid_pre),  // Store original master ID

    // Deallocate: When B response completes
    .i_mark_invalid(o_axi_shim_slv_bvalid & i_axi_shim_slv_bready),
    .i_tag_in_invalid(o_axi_shim_slv_bid),   // Search by shim-assigned ID

    // Auto-ID output
    .o_cur_id(aw_id_cur),           // Next available ID for HBM2E
    .ow_ret_id(aw_id_ret),          // Retrieved original master ID

    // Status
    .ow_tags_full(ow_aw_tags_full),
    .ow_tags_empty(ow_aw_tags_empty)
);
```

2. **Read Path CAM (AR → R):**
```systemverilog
cam_tag_perf #(
    .ENABLE(1),
    .HI_BIT(1),          // Namespace: IDs 0x80-0xFF (different from AW!)
    .N(8),
    .DEPTH(64)
) u_ar_cam_tag (
    .i_clk(clk),
    .i_rst_n(aresetn_safe),

    // Allocate: When AR handshake completes
    .i_mark_valid(i_axi_shim_slv_arvalid & o_axi_shim_slv_arready),
    .i_tag_in_valid(axi_shim_slv_arid_pre),  // Store original master ID

    // Deallocate: When R response completes (with RLAST)
    .i_mark_invalid(o_axi_shim_slv_rvalid & i_axi_shim_slv_rready & o_axi_shim_slv_rlast),
    .i_tag_in_invalid(o_axi_shim_slv_rid),   // Search by shim-assigned ID

    // Auto-ID output
    .o_cur_id(ar_id_cur),           // Next available ID for HBM2E
    .ow_ret_id(ar_id_ret),          // Retrieved original master ID

    // Status
    .ow_tags_full(ow_ar_tags_full),
    .ow_tags_empty(ow_ar_tags_empty)
);
```

### ID Replacement Flow

**Write Path (AW → W → B):**

```systemverilog
// Step 1: AW channel - Replace master's AWID with auto-generated ID
assign i_aw_mark_valid = i_axi_shim_slv_awvalid & o_axi_shim_slv_awready;
assign i_aw_tag_in_valid = axi_shim_slv_awid_pre;  // Store original AWID
assign i_axi_shim_slv_awid = aw_id_cur;             // Send auto-generated ID to HBM2E

// Step 2: CAM stores mapping: aw_id_cur → axi_shim_slv_awid_pre

// Step 3: B channel - Restore original master's AWID
assign i_aw_mark_invalid = o_axi_shim_slv_bvalid & i_axi_shim_slv_bready;
assign i_aw_tag_in_invalid = o_axi_shim_slv_bid;  // HBM2E's BID (was aw_id_cur)
assign aw_id_fin = o_axi_shim_slv_bvalid ? aw_id_ret : 'b0;  // Retrieved original ID
assign o_axi_slv_bid = aw_id_fin;  // Return original master's AWID
```

**Read Path (AR → R):**

```systemverilog
// Step 1: AR channel - Replace master's ARID with auto-generated ID
assign i_ar_mark_valid = i_axi_shim_slv_arvalid & o_axi_shim_slv_arready;
assign i_ar_tag_in_valid = axi_shim_slv_arid_pre;  // Store original ARID
assign i_axi_shim_slv_arid = ar_id_cur;             // Send auto-generated ID to HBM2E

// Step 2: CAM stores mapping: ar_id_cur → axi_shim_slv_arid_pre

// Step 3: R channel - Restore original master's ARID
assign i_ar_mark_invalid = o_axi_shim_slv_rvalid & i_axi_shim_slv_rready & o_axi_shim_slv_rlast;
assign i_ar_tag_in_invalid = o_axi_shim_slv_rid;  // HBM2E's RID (was ar_id_cur)
assign ar_id_fin = o_axi_shim_slv_rvalid ? ar_id_ret : 'b0;  // Retrieved original ID
assign o_axi_slv_rid = ar_id_fin;  // Return original master's ARID
```

### HI_BIT Usage for Namespace Partitioning

**Critical Feature:** Prevents ID collisions between write and read paths

```systemverilog
// Write CAM: HI_BIT=0 → Generates IDs 0x00-0x7F (bit 7 = 0)
.HI_BIT(0)  // o_cur_id = {1'b0, r_ptr[6:0]}

// Read CAM: HI_BIT=1 → Generates IDs 0x80-0xFF (bit 7 = 1)
.HI_BIT(1)  // o_cur_id = {1'b1, r_ptr[6:0]}
```

**Why This Matters:**
- Master can issue AWID=5 and ARID=5 simultaneously
- Shim assigns AWID_new=0x05 (from AW CAM) and ARID_new=0x85 (from AR CAM)
- HBM2E sees two different IDs (0x05 vs 0x85) → no collision
- Responses BID=0x05 and RID=0x85 correctly map back to original AWID=5 and ARID=5

### Pipeline Integration

**Regslice on Both Sides:**

```systemverilog
// AW channel pipeline (before CAM)
gen_regslice #(.T(logic [aw_channel_width-1:0])) aw_regslice (
    .data_in_dat(aw_in),                  // Original AW packet
    .data_in_val(i_axi_slv_awvalid),
    .data_in_rdy(o_axi_slv_awready),
    .data_out_dat(aw_out),                // To CAM for ID replacement
    .data_out_val(i_axi_shim_slv_awvalid),
    .data_out_rdy(o_axi_shim_slv_awready),
    .clk, .arstn
);

// B channel pipeline (after CAM)
gen_regslice #(.T(logic [b_channel_width-1:0])) b_regslice (
    .data_in_dat(b_in),                   // B packet with restored ID
    .data_in_val(o_axi_shim_slv_bvalid),
    .data_in_rdy(i_axi_shim_slv_bready),
    .data_out_dat(b_out),                 // Back to master
    .data_out_val(o_axi_slv_bvalid),
    .data_out_rdy(i_axi_slv_bready),
    .clk, .arstn
);
```

**Benefits:**
- Timing closure (breaks long combinational paths)
- Buffering for throughput
- Clean separation of concerns

### What This Example Teaches Us

**For Bridge CAM Design:**

1. **DON'T Adopt Auto-ID Generation:**
   - Shim's use case: ID replacement (master's ID → shim's ID → back to master's ID)
   - Bridge's use case: Transaction tracking (master_index lookup, no ID replacement)
   - Bridge masters provide their own IDs; CAM should **store** them, not **generate** them

2. **DON'T Adopt HI_BIT Namespace Partitioning:**
   - Shim needs it to prevent AW/AR ID collisions (single CAM namespace)
   - Bridge has separate CAMs per slave (already partitioned by destination)
   - Additional complexity without benefit

3. **DO Adopt Dual CAM Pattern:**
   - Shim: One CAM for write path, one for read path
   - Bridge: One CAM per slave for writes, one CAM per slave for reads
   - Correct pattern: Separate CAMs for independent paths

4. **DO Adopt Combined Deallocation + Retrieval:**
   - Shim: `i_mark_invalid` triggers `ow_ret_id` output in same cycle
   - Bridge: When B/R response arrives, lookup master_index and deallocate in one operation
   - Efficient: Single action for both operations

5. **DO Adopt Regslice Integration:**
   - Shim: Pipeline stages on both sides of CAM for timing closure
   - Bridge: Can use skid buffers or regslices around CAM if needed
   - Performance: Helps with high-frequency designs

### Key Differences: Shim vs. Bridge

| Feature | hbm2e_shim_perf (This Example) | cam_tag_bridge (Needed for Bridge) |
|---------|--------------------------------|-------------------------------------|
| **ID Source** | Auto-generate (o_cur_id) | User-provided (store master's ID) |
| **ID Usage** | Replace master's ID for HBM2E | Store for response routing lookup |
| **Data Stored** | Original master ID (8 bits) | Master index + metadata (3-8 bits) |
| **HI_BIT** | Required (AW vs AR namespace) | Not needed (separate CAMs per slave) |
| **Lookup** | Only on deallocation (combined) | Separate lookup + deallocation |
| **Purpose** | ID space translation | Transaction tracking and routing |

### Shim Instantiation Pattern

```systemverilog
// Per HBM2E pseudo-channel (PC0-PC15)
hbm2e_shim_perf #(
    .ENABLE(1),
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WD(48),
    .AXI_DATA_WD(256)
) u_hbm2e_shim_pc0 (
    .clk, .arstn,

    // Master-side interface (original IDs: 0-255)
    .i_axi_slv_awid(master_awid),
    .i_axi_slv_awvalid(master_awvalid),
    .o_axi_slv_awready(master_awready),
    // ... other AW signals ...

    // HBM2E-side interface (shim-assigned IDs: 0-127)
    .i_axi_shim_slv_awid(hbm_awid),         // Auto-generated
    .i_axi_shim_slv_awvalid(hbm_awvalid),
    .o_axi_shim_slv_awready(hbm_awready),
    // ... other AW signals ...

    // Response path (restored IDs)
    .o_axi_shim_slv_bid(hbm_bid),           // From HBM2E
    .o_axi_slv_bid(master_bid),             // Restored original
    // ... other B signals ...
);
```

### Files to Delete Together

When removing cam_tag_perf.sv, also remove:
- `projects/components/bridge/rtl/cam_tag_perf.sv` (CAM module)
- `projects/components/bridge/rtl/hbm2e_shim_perf.v` (Shim using CAM)

Both are legacy code not following repository standards (no reset macros, no FPGA attributes).

---

**Version:** 1.0
**Purpose:** Documentation before deletion
**Next:** Create cam_tag_bridge.sv incorporating these lessons
**Documented Files:** cam_tag_perf.sv + hbm2e_shim_perf.v
