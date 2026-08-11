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

**[← Back to Main Index](../index.md)** | **[rtl-common Index](index.md)**

# CAM Tag

Associative tag storage: you find entries by content, not by address.

## Overview

The `cam_tag` module implements a Content Addressable Memory (CAM) for tag storage and lookup. Lookups are associative — you find data by content, not by address — which is exactly what cache implementations, translation lookaside buffers (TLBs), and routing tables need.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| ENABLE | int | 1 | Enable/disable CAM functionality |
| N | int | 8 | Width of each tag in bits |
| DEPTH | int | 16 | Number of tag entries in the CAM |

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| clk | 1 | System clock |
| rst_n | 1 | Active-low asynchronous reset |
| tag_in_status | N | Tag to search for (lookup operation) |
| mark_valid | 1 | Signal to add a new valid tag |
| tag_in_valid | N | Tag value to mark as valid |
| mark_invalid | 1 | Signal to invalidate an existing tag |
| tag_in_invalid | N | Tag value to mark as invalid |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| tags_empty | 1 | Indicates when CAM contains no valid entries |
| tags_full | 1 | Indicates when CAM is completely full |
| tag_status | 1 | Result of lookup operation (1 if tag found, 0 if not found) |

## Functional Description

### Tag Lookup

Continuously compares `tag_in_status` against all valid entries:
- Returns 1 if tag found among valid entries
- Returns 0 if tag not found or entry is invalid

### Tag Insertion

When `mark_valid` is asserted and CAM is not full:
1. Store `tag_in_valid` at `w_next_valid_loc`
2. Set corresponding valid bit
3. Only occurs when `ENABLE != 0`

### Tag Invalidation

When `mark_invalid` is asserted and matching tag found:
1. Clear the tag value at matching location
2. Clear corresponding valid bit

### Enable Control

When `ENABLE = 0`:
- Tag insertion is disabled
- Tag lookup and invalidation still function
- Useful for disabling CAM without losing existing data

### Allocation Strategy

- **First Available**: Uses the **lowest-indexed** free location (see the search
  below). Functional behavior is correct either way; only the index order matters
  when matching allocations to waveforms.
- **Replacement**: No automatic replacement policy (must manually invalidate)
- **Overflow Protection**: Prevents insertion when full

### Storage Arrays

```systemverilog
logic [N-1:0]     r_tag_array [0:DEPTH-1];  // Tag storage array
logic [DEPTH-1:0] r_valid;                  // Valid bit for each entry
```

### Search Logic

Three parallel search operations run side by side:

#### 1. Next Available Location Search

```systemverilog
always_comb begin
    w_next_valid_loc = -1;
    for (int i=DEPTH-1; i >= 0; i--)
        if (r_valid[i] == 1'b0)
            w_next_valid_loc = i;
end
```
- Iterates from the highest index down to 0, overwriting `w_next_valid_loc` on
  every free slot — so the **last** assignment (index 0, if free) wins
- Returns the **lowest-indexed** free location (e.g., all slots free → slot 0)
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

### State Management

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

## Design Notes

### Usage Considerations

- **Timing**: All lookups are combinational (single cycle)
- **Capacity**: Monitor `tags_full` before insertions
- **Conflicts**: No protection against duplicate tag insertion
- **Performance**: Search time is constant regardless of occupancy
- **Power**: All entries are searched simultaneously (high power for large depths)

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
