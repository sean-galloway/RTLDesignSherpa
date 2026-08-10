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


# rtl-integ-common Modules Index

The catalogue for `rtl/integ_common/`. For orientation -- what an integration
example is for here, and when to reach for one -- start at
[overview.md](overview.md).

**2 modules** in `rtl/integ_common/`. Count is from `ls rtl/integ_common/*.sv`;
regenerate rather than hand-editing.

## Multi-field FIFO wrappers

Both pack a structured payload into a single [fifo_sync](../rtl-common/fifo_sync.md)
so one FIFO and one set of flags carry several fields.

- **[fifo_sync_multi](fifo_sync_multi.md)** - packs addr / ctrl / data by name
- **[fifo_sync_multi_sigmap](fifo_sync_multi_sigmap.md)** - the same wrapper with
  generic positional ports, for callers that own the field names

## Technique index

Looking for how a design technique is used in real code — streaming
datapaths, minimal FSMs, CDC, arbitration, timeout/recovery, in-line data
integrity? **[technique-index.md](technique-index.md)** maps each one to its
best worked examples in the tree. It replaces the once-planned set of toy
demonstration designs: the real, tested implementations teach better and
cannot rot.

## Related

The blocks these are built from stay in their own areas and are reached by `-f`
include, never copied:

- [fifo_sync](../rtl-common/fifo_sync.md), [fifo_control](../rtl-common/fifo_control.md),
  [counter_bin](../rtl-common/counter_bin.md) - [rtl-common](../rtl-common/index.md)

For a FIFO that crosses clock domains, see [fifo_async](../rtl-cdc/fifo_async.md)
in [rtl-cdc](../rtl-cdc/index.md).

## Navigation

- **[Overview](overview.md)**
- **[Back to Main Documentation Index](../index.md)**
