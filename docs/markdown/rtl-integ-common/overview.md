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


# rtl-integ-common Overview

**RTL:** `rtl/integ_common/` (2 modules)
**Filelists:** `rtl/integ_common/filelists/` -- lint the area with `integ_common_all.f`
**Tests:** `val/integ_common/`

Integration examples built from `rtl-common` blocks. Nothing here is a library
primitive: each module wires existing blocks together to demonstrate a pattern
you would otherwise have to reconstruct from the per-module pages.

**Full catalogue:** [index.md](index.md)

## What "integration example" means here

A library module earns its place by doing one thing that several designs need.
An integration example earns its place by showing how several of those fit
together -- so it is allowed to be opinionated in ways a library module is not.

These two demonstrate the same pattern: a multi-field payload packed into a
single `fifo_sync`, so one FIFO carries an address, a control word and data
without three separate instances and three sets of flags.

- **[fifo_sync_multi](fifo_sync_multi.md)** packs the fields by name.
- **[fifo_sync_multi_sigmap](fifo_sync_multi_sigmap.md)** does the same with
  generic positional ports, for when the field names belong to the caller rather
  than the wrapper.

They lived in `rtl/common/testcode/` until 2026-07-26 -- inside the library they
consume, which is why neither had a filelist and both were marked exempt from
coverage with the untrue reason "no consumer yet". They have three tests.

## When to reach for these

Take one when you need a single synchronous FIFO to carry a structured payload
and you would otherwise instantiate several. Read
[fifo_sync](../rtl-common/fifo_sync.md) first -- these are wrappers around it,
and its depth, almost-full/empty margins and `REGISTERED` behavior are what
actually govern yours.

If the payload crosses a clock boundary, you want `rtl-cdc` instead: see
[fifo_async](../rtl-cdc/fifo_async.md) and the
[CDC decision guide](../rtl-cdc/overview.md).

## Navigation

- [Catalogue of every module in this area](index.md)
- [Back to the documentation index](../index.md)
- [rtl-common](../rtl-common/index.md) -- the blocks these are built from
- [rtl-integ-amba](../rtl-integ-amba/index.md) -- the AMBA-side examples
