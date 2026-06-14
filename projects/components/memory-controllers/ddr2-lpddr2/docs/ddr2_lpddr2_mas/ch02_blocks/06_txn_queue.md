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

# Transaction Queue (`txn_queue_fub`)

**Module:** `txn_queue_fub.sv`
**Location:** `rtl/fub/`
**Status:** Skeleton

> See HAS §3.2 `txn_queue` for the architectural view. This MAS block is the implementation-level detail.

## Relationship to the CAMs

The `txn_queue` is the **unified scheduling view**. Each pending CAM slot (read or write) is reflected as one queue entry, but the queue's entry only carries fields the scheduler needs:

`{is_write, rank, bank, row, row_hit_cached, age, state, cam_slot_idx}`

The reverse pointer `cam_slot_idx` links back to the corresponding `rd_cmd_cam` or `wr_cmd_cam` entry. The queue's job is purely scheduling-policy storage; the CAMs carry the AXI-side and beat-tracking detail.

## TODO

- Entry-format width breakdown
- Age-saturation specifics
- `row_hit_cached` update path (per HAS §3.2 — cached at insert; updated on row-state change)
