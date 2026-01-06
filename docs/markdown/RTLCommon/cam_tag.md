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

# CAM Tag Module

## Purpose
The `cam_tag` module implements a Content Addressable Memory (CAM) for tag storage and lookup. It provides fast associative lookup capabilities where data can be found based on content rather than address, commonly used in cache implementations, translation lookaside buffers (TLBs), and routing tables.

## Parameters
- `ENABLE`: Enable/disable CAM functionality (default: 1)
- `N`: Width of each tag in bits (default: 8)
- `DEPTH`: Number of tag entries in the CAM (default: 16)

## Ports

### Inputs
- `clk`: System clock
- `rst_n`: Active-low asynchronous reset
- `tag_in_status[N-1:0]`: Tag to search for (lookup operation)
- `mark_valid`: Signal to add a new valid tag
- `tag_in_valid[N-1:0]`: Tag value to mark as valid
- `mark_invalid`: Signal to invalidate an existing tag
- `tag_in_invalid[N-1:0]`: Tag value to mark as invalid

### Outputs
- `tags_empty`: Indicates when CAM contains no valid entries
- `tags_full`: Indicates when CAM is completely full
- `tag_status`: Result of lookup operation (1 if tag found, 0 if not found)

## Key Internal Structures

### Storage Arrays
```systemverilog
logic [N-1:0]     r_tag_array [0:DEPTH-1];  // Tag storage array
logic [DEPTH-1:0] r_valid;                  // Valid bit for each entry
```

### Search Logic
Three parallel search operations are implemented:

#### 1. Next Available Location Search
```systemverilog
always_comb begin
    w_next_valid_loc = -1;
    for (int i=DEPTH-1; i >= 0; i--)
        if (r_valid[i] == 1'b0)
            w_next_valid_loc = i;
end
```
- Searches from highest to lowest index
- Returns the highest-indexed free location
- Returns -1 if no free locations available

#### 2. Valid Tag Match Search
```systemverilog
always_comb begin
    w_match_loc = -1;
    for (int i = 0; i < DEPTH; i++)
        if (r_valid[i] == 1'b1 && tag_in_status == r_tag_array[i])
            w_match_loc = i;
end
```
- Searches for exact tag match among valid entries
- Returns index of matching entry or -1 if no match

#### 3. Invalid Tag Match Search
```systemverilog
always_comb begin
    w_match_invalid_loc = -1;
    for (int i = 0; i < DEPTH; i++)
        if (r_valid[i] == 1'b1 && tag_in_invalid == r_tag_array[i])
            w_match_invalid_loc = i;
end
```
- Used for invalidation operations
- Finds valid entries that match the invalidation tag

## Operations

### Tag Insertion
When `mark_valid` is asserted and CAM is not full:
1. Store `tag_in_valid` at `w_next_valid_loc`
2. Set corresponding valid bit
3. Only occurs when `ENABLE != 0`

### Tag Invalidation
When `mark_invalid` is asserted and matching tag found:
1. Clear the tag value at matching location
2. Clear corresponding valid bit

### Tag Lookup
Continuously compares `tag_in_status` against all valid entries:
- Returns 1 if tag found among valid entries
- Returns 0 if tag not found or entry is invalid

## State Management

### Update Logic
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_valid <= 'b0;
        for (int i = 0; i < DEPTH; i++) begin
            r_tag_array[i] <= 'b0;
        end
    end else begin
        if (mark_valid && !tags_full && (ENABLE != 0)) begin
            r_tag_array[w_next_valid_loc] <= tag_in_valid;
            r_valid[w_next_valid_loc] <= 1'b1;
        end else if (mark_invalid && w_match_invalid_loc >= 0) begin
            r_tag_array[w_match_invalid_loc] <= 'b0;
            r_valid[w_match_invalid_loc] <= 1'b0;
        end
    end
end
```

### Status Signals
- `tags_empty = ~|r_valid`: NOR of all valid bits
- `tags_full = &r_valid`: AND of all valid bits
- `tag_status`: Result of tag lookup operation

## Special Features

### Enable Control
When `ENABLE = 0`:
- Tag insertion is disabled
- Tag lookup and invalidation still function
- Useful for disabling CAM without losing existing data

### Allocation Strategy
- **First Available**: Uses highest-indexed free location
- **Replacement**: No automatic replacement policy (must manually invalidate)
- **Overflow Protection**: Prevents insertion when full

### Debug Support
The module includes simulation-only logic for waveform viewing:
```systemverilog
// synopsys translate_off
logic [(N*DEPTH)-1:0] flat_r_tag_array;
generate
    for (j = 0; j < DEPTH; j++) begin : gen_flatten_memory
        assign flat_r_tag_array[j*N+:N] = r_tag_array[j];
    end
endgenerate
// synopsys translate_on
```

## Usage Considerations
- **Timing**: All lookups are combinational (single cycle)
- **Capacity**: Monitor `tags_full` before insertions
- **Conflicts**: No protection against duplicate tag insertion
- **Performance**: Search time is constant regardless of occupancy
- **Power**: All entries are searched simultaneously (high power for large depths)

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
