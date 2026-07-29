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

# STREAM Extended - Chained Strided (Transpose) Descriptor Corruption

## A strided extended descriptor reached via `next_ptr` reads the wrong source, writes with holes, and corrupts the preceding descriptor

**Severity**: High (silent data corruption)
**Impact**: Wrong data movement, no error flag raised. Affects only builds with
`USE_ROW_COL_MAJOR_ADDRESSING=1` (TASK-101 extended addressing) when a
per-beat/strided extended descriptor is chained after another descriptor.
**Status**: ACTIVE
**Discovery Date**: 2026-07-29 (found by the first STREAM top-level extended
integration test, `cocotb_test_stream_top_extended_chained_transpose`)

### Description

With the extended (row/col) addressing path enabled, an extended descriptor
whose address generator runs in **per-beat/strided mode** (`stride_0 != beat_size`,
e.g. a transpose) is corrupted **when it is reached through the descriptor chain
via `next_ptr`**. The exact same descriptor **kicked directly works correctly**,
and a chained extended-**contiguous** descriptor (single-dimension burst walk,
`stride_1 = 0`, `inner = beats`) also works. The bug is the intersection:
**chained + strided**.

Two symptoms occur together:

1. **The chained transpose reads the wrong source and drops beats.** For a 4x4
   (16-beat) transpose whose source region was filled with the byte pattern
   `0x30..0x3f`, the destination came out as:

   ```
   [0x30, 0x12, 0x12, 0x00, 0x13, 0x13, 0x13, 0x00,
    0x10, 0x10, 0x00, 0x00, 0x11, 0x11, 0x00, 0x00]
   ```

   The non-zero values (`0x10..0x13`) are the **preceding** descriptor's source
   data, not this descriptor's own `0x30..0x3f`, and several beats are `0x00`
   (never written). The write address sequence is neither the correct transpose
   permutation nor contiguous.

2. **The preceding descriptor is corrupted.** The descriptor that chains into the
   transpose has its **last-touched beat** overwritten (its beat 0 read back
   `0x12` instead of `0x10` in the repro).

No error/abort is asserted on the monitor bus - the transfer completes and the
channel returns to idle, so this is **silent** corruption.

### Reproduction

`projects/components/dmas/stream/dv/tests/top/test_stream_top.py`

- `test_stream_top_extended` (PASSES) - the known-good coverage:
  legacy -> extended-contiguous chain on ch0 (both formats, one chain) plus a
  directly-kicked transpose on ch1.
- `test_stream_top_extended_chained_transpose` (`xfail(strict=True)`) - the
  minimal repro: a 2-deep chain `legacy -> transpose`. Asserts the correct
  behaviour, so it will **xpass** (and fail the suite, prompting removal of the
  xfail) once the RTL is fixed.

Isolation matrix (each a separate build with `USE_ROW_COL_MAJOR_ADDRESSING=1`):

| Scenario                                   | Result |
|--------------------------------------------|--------|
| legacy descriptor alone                    | pass   |
| directly-kicked transpose alone            | pass   |
| legacy -> extended-contiguous (chained)    | pass   |
| legacy -> transpose (chained)              | **fail** |
| legacy -> ext-contig -> transpose (3-deep) | **fail** |

### Suspected Root Cause (not yet confirmed in RTL)

The two symptoms together - a wrong **read base** on the chained descriptor and
corruption of the **previous** descriptor - point at the extended **chunk-1
(stride config) fetch/apply on the chained path** aliasing with the descriptor
engine's **prefetch** of the next descriptor while the current transfer is still
in flight. The contiguous extended case survives because its address generator
collapses to a single-dimension burst walk that does not depend on the strided
per-beat sequencing that the shared config registers drive.

Prime suspects: `descriptor_engine.sv` (extended chunk-1 fetch + prefetch
sequencing, the `g_ext_fifo` / `w_want_ext` logic) and `scheduler.sv`
(`w_is_ext_in` handling), plus `stream_run_addr_gen.sv` config latching. This
is a strong candidate for the signal-contract / K-map "correct by construction"
work tracked in `vault/Tasks/projects/components/dmas/stream/` - the interaction
that fails is exactly the kind of cross-descriptor pipeline hazard a per-signal
contract on the engines would forbid.

### Workaround

Until fixed, do **not** chain a strided/per-beat extended (transpose)
descriptor after another descriptor. Either kick each strided extended
descriptor directly (single-descriptor kick), or keep chained extended
descriptors in **contiguous** (single-dimension) mode.
