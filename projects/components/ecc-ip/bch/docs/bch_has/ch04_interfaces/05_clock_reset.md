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

# Clock and Reset

## Single clock

The core and its adapters run on one clock, `aclk`. A consumer whose data
path runs on another clock crosses at the consumer's boundary with the
repository's CDC blocks (`rtl/cdc`); the core does not contain a crossing.
For a standalone top whose AXI4 memory side runs on a different clock than
the stream side, the adapter's timing wrapper is the place to insert the
`axi4_cdc_{rd,wr}` pair, as the bridge does for its CDC slave ports; that is
a build option for the adapter, not a property of the core.

## Reset

`aresetn` is active-low and synchronous, per the component target convention.
It is applied through the `ALWAYS_FF_RST` macros with `RST_ASSERTED` so the
polarity follows the repository build (`vault/handbook/design/reset-and-clocking.md`).
Reset clears control state, the parity and syndrome registers, position and
iteration counters and the status. The block buffer's storage is not reset;
its pointers are, so stale contents are never read.

## Clock gating

None inside the core. The `_cg` variants of the AXIS and AXI4 wrappers may
be selected at the adapters for a standalone top that wants boundary clock
gating, following the rest of the repository.

## Frequency

The decoder's clock is set by the key-equation solver's per-iteration
critical path, then by the syndrome and Chien cells (one constant multiply
plus an XOR). The exact paths are not yet characterised; chapter 5.3 gives
the characterisation plan that turns this into a number per part.
