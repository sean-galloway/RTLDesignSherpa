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

# Identity space allocation

Three fields in every packet are designer-owned and fixed at build time:

| Field | Bits | Set by | Meaning |
|---|---:|---|---|
| `unit_id` | 8 | wrapper parameter `UNIT_ID` | which subsystem |
| `agent_id` | 16 | wrapper parameter `AGENT_ID` | which block inside it |
| `channel_id` | 9 | the monitor, from the transaction | which channel or AXI ID |

The tools decode nothing from these fields; a host-side table maps the
`(unit_id, agent_id)` tuple to a name. That makes the allocation yours.
STREAM uses `unit_id = 0x01` for the whole DMA and spends `agent_id` on
blocks: `0x10` descriptor engine, `0x30` scheduler, `0x40` the widened
scheduler set (`projects/components/dma-ip/stream/rtl/macro/scheduler_group.sv`).

**Worked example, one level down.** A subsystem with several internal
buses can split `unit_id` into a subsystem nibble and a sub-bus nibble:
`unit_id = {sub_system[3:0], sub_bus[3:0]}` gives sixteen subsystems each
with up to sixteen tracked internal buses, and `agent_id` is still free to
name the block on each bus. A host filter on `unit_id[7:4]` then isolates a
subsystem, and on the full byte a single bus, with no change to the RTL.
The cost is nothing: the fields exist in every packet regardless.

![Identity allocation: one unit per subsystem, or a subsystem nibble and a sub-bus nibble](../../assets/rtl-amba/monitor_wp_identity.png)
