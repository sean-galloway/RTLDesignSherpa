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

# monbus_wb4_axil4_group / monbus_wb4_axi4_group

## Overview

The monitor-bus groups with their read-only CSR port presented as a
**Wishbone B4 slave** instead of an AXI4-Lite one, so a Wishbone host can
own a monitor group without an AXI bridge in front of it.

| Module | Host read port | Record-write master |
|---|---|---|
| `monbus_wb4_axil4_group` | Wishbone B4 | AXI4-Lite |
| `monbus_wb4_axi4_group` | Wishbone B4 | AXI4 (burst) |

Both are **thin wrappers**. The drain path, compressor, FIFOs, interrupt and
statistics are the existing
[`monbus_axil4_axil4_group`](monbus_axil4_axil4_group.md) and
[`monbus_axil4_axi4_group`](monbus_axil4_axi4_group.md) bodies, untouched;
only the host read port changes, through `monbus_wb4_rd_shim`. Duplicating
the group body would have created a second copy to keep in step, and the
copy nobody edits is the one that rots.

## monbus_wb4_rd_shim

Wishbone B4 slave in, AXI4-Lite **read** master out.

| Parameter | Default | Description |
|---|---|---|
| ADDR_WIDTH | 32 | Address width |
| DATA_WIDTH | 64 | The group's read beat; 32 for a 32-bit host |
| CMD_DEPTH / RSP_DEPTH | 2 | The internal `wb4_slave`'s queues |
| CLASSIC | 0 | 0 = B4 pipelined, 1 = B4 standard |
| AXIL_PROT | 3'b000 | `ARPROT` driven on every read |

**Writes are refused, not ignored.** The CSR port is read-only. A Wishbone
write terminates `ERR` in the shim and never reaches the group, so a host
that writes here learns it was wrong instead of believing it worked.

**One transfer at a time.** This port is a host reading a drain register;
pipelining it would add a reorder buffer to save nothing. The internal
slave is built `MAX_OUTSTANDING = 1`.

This is deliberately not
[`wb4_to_axil4`](../../../../projects/components/converters/docs/converter_mas/ch03_protocol_blocks/11_wb4_to_axil4.md),
which carries write channels and an outstanding queue that a read-only CSR
port has no use for.

## Reading a record

Identical to the AXI4-Lite groups: each read pops one beat of the error
FIFO, and a record is three 64-bit slices. With `S_AXIL_DATA_WIDTH = 32`
the group's 2:1 serializer presents each slice as a low then a high read,
so a record is six beats. The Wishbone side sees ordinary single reads
either way.

The drain register is **address-insensitive**: any read in the region pops
the next beat. That is the group's existing behaviour, not something the
shim adds, and it means a test cannot detect a corrupted read address on
this port. The data path is checked instead.

## Notes

- Under `ifdef FORMAL` the shim asserts that a write never reaches the
  group, that only one read is outstanding, that `R` is consumed only while
  a read is open, and that a write is always refused rather than acknowledged.
- The wrappers forward every other group port straight through, so the
  configuration, statistics and interrupt interfaces are unchanged.

## Related

- [monbus_axil4_axil4_group](monbus_axil4_axil4_group.md), [monbus_axil4_axi4_group](monbus_axil4_axi4_group.md) - the bodies these wrap
- [wb4_slave](../wb4/wb4_slave.md) - the Wishbone end of the shim

## Test

`val/amba/test_monbus_wb4_axil4_group.py` is the AXI4-Lite group's test with
its drain switched to Wishbone through the shared `MonbusGroupHarness`,
which gained a `drain_proto="wb4"` path for it. Records decode correctly at
both the 64-bit and 32-bit drain widths. A mutation rotating the shim's read
data fails the test.
