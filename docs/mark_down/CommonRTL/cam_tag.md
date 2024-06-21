# cam_tag

## Overview

The `cam_tag` module is a Content-Addressable Memory (CAM) system implemented in SystemVerilog. CAM is useful for high-speed searches of tags, commonly used in networking and cache systems. This is simplified to focus on the core features.

## Parameters

- **ENABLE (default=1)**: Enables or disables the CAM module.
- **N (default=8)**: Width of each TAG entry in bits.
- **DEPTH (default=16)**: Number of TAG entries in the CAM.

## I/O Ports

### Input Ports

- **i_clk**: Clock signal.
- **i_rst_n**: Active-low reset signal.
- **i_tag_in_status [N-1:0]**: Tag input for status checking.
- **i_mark_valid**: Signal to mark a tag as valid.
- **i_tag_in_valid [N-1:0]**: Tag input to be marked as valid.
- **i_mark_invalid**: Signal to mark a tag as invalid.
- **i_tag_in_invalid [N-1:0]**: Tag input to be marked as invalid.

### Output Ports

- **ow_tags_empty**: Indicates if all tags are empty.
- **ow_tags_full**: Indicates if all tag slots are full.
- **ow_tag_status**: Status output indicating if the current tag is valid or not.

## Internal Variables

- **r_tag_array [DEPTH][N]**: Array storing the tags.
- **r_valid [DEPTH]**: Array storing the validity of each tag.
- **w_next_valid_loc**: Identifies the next available slot for a new tag.
- **w_match_loc**: Identifies the index of a matching valid tag.
- **w_match_invalid_loc**: Identifies the index of a matching invalid tag.

## Functionality

1. **Finding Next Open Slot**:
   - Scans through `r_valid` to identify the first empty/invalid slot (`w_next_valid_loc`).

2. **Matching Valid Tag**:
   - Searches for a tag in `r_tag_array` that matches `i_tag_in_status` and is valid (`w_match_loc`).

3. **Matching Invalid Tag**:
   - Searches for a tag in `r_tag_array` that matches `i_tag_in_invalid` and is valid (`w_match_invalid_loc`).

### Output Assignments

- **ow_tag_status**: Reflects the validity of the tag at `w_match_loc`.
- **ow_tags_empty**: Indicates if all tags are invalid.
- **ow_tags_full**: Indicates if all tag slots are in use.

## Error Checking and Debug

- A flattened version of `r_tag_array` is created for waveform visualization during simulation.

## Usage

To use this module, instantiate it with appropriate parameter values and connect the input/output ports. Control the validation and invalidation of tags using `i_mark_valid`, `i_mark_invalid`, and provide tags as `i_tag_in_valid`, `i_tag_in_invalid`. Monitor flags like `ow_tags_empty`, `ow_tags_full`, and `ow_tag_status` for real-time status feedback.

This module is ideal for applications requiring efficient tag management and quick look-up capabilities, such as cache designs and associative memory implementations.

---

[Return to Index](index.md)

---
