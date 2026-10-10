# TASK-004: plumb RD_EN_CYC, or delete it

`scoria_dfi_layer.RD_EN_CYC` is the read-enable window width, and its own
comment says what it is for: "set separately when the DRAM beat != device
word". **No instantiation anywhere sets it.** It defaults to `BL_WORDS` in
every build, while `scoria_top` computes the true DQ occupancy
`ceil(DRAM_BL / DFI_RATE)` as a localparam (`RD_EN_CYC_TOP`) and uses it only
for the tRTW floor.

**Priority:** P2 — the two values AGREE for the Genesys 2 design point, so
nothing is wrong on the board today. They diverge exactly when the knob was
added for: a device word narrower than the DRAM beat.
**Status:** CLOSED 2026-10-01. PLUMBED, not deleted. `scoria_core` now passes
`RD_EN_CYC_CORE = ceil(DRAM_BL / DFI_RATE)` explicitly to the DFI layer -- the
same expression `scoria_top` uses for its tRTW floor, so the two cannot
disagree. Found 2026-09-30 writing the `scoria_dfi_rd_aligner` unit test, which
needed the two parameters separated to drive the aligner.

The fix went in `scoria_core` rather than threading a parameter down from
`scoria_top`, because the core already has `DRAM_BL` and `DFI_RATE` and the bug
WAS a parameter nobody set -- adding another top-level one to be forgotten
would repeat it. The layer keeps the `BL_WORDS` default only so a bare
instantiation elaborates, and its comment now says the default is wrong for any
narrow build.

No behaviour change at the shipping point: both expressions give 2 for BL8 over
a 1:4 gear, which is why the board was never affected. Suite and lint green
after.

NOT TESTED in the narrow configuration, and this is the honest limit: no narrow
build exists to run. What IS gated is the property the fix relies on -- that
the aligner honours EN_CYC independently of BL_WORDS -- by
`test_scoria_dfi_rd_aligner.py`, which already runs EN_CYC=4 against
BL_WORDS=2, plus `en_cyc_below_bl_words_is_unsupported` for the other
direction.

## The divergence

`BL_WORDS = BURST_WORDS = (BL_PUMICE >= DFI_RATE) ? BL_PUMICE/DFI_RATE : 1`,
and `BL_PUMICE = DRAM_BL >> BL_SHIFT` where `BL_SHIFT` is nonzero only when
`DRAM_BEAT_WIDTH > DRAM_DEVICE_WIDTH`.

| Build | DRAM_BL | DFI_RATE | BL_SHIFT | BL_WORDS | true occupancy | agree? |
|---|---|---|---|---|---|---|
| Genesys 2 (beat == device word) | 8 | 4 | 0 | 2 | 2 | yes |
| narrow device (beat 2x device word) | 8 | 4 | 1 | 1 | 2 | **no** |

In the narrow case the PHY is told to sample DQ for one DFI cycle of a
two-cycle burst. The window is the only thing that tells the PHY when the data
is on the wire, so the second half of every read is never sampled.

## Related constraint, now recorded in the RTL

The aligner's enable-window credit mints one credit per enable cycle and spends
one per captured word, so **EN_CYC must be >= BL_WORDS**; below that it drops
words silently. That direction is NOT the narrow case above (which needs EN_CYC
*larger* than BL_WORDS), but a fix that computes one from the other must not
land on the wrong side of it. Measured and gated in
`dv/tests/fub/test_scoria_dfi_rd_aligner.py::en_cyc_below_bl_words_is_unsupported`.

## Done when

Either `scoria_core`/`scoria_top` pass the occupancy they already compute down
to `scoria_dfi_layer` (and a narrow-device config is in the unit test's
parameter table), or `RD_EN_CYC` is removed and `BL_WORDS` is documented as the
window width -- which also means admitting the narrow-device case is
unsupported, and saying so where someone configuring a build will read it.

## Not in scope

Whether scoria should support a device word narrower than the DRAM beat at all.
`BL_SHIFT` and `SUB_COL_STRIDE` exist for it elsewhere in `scoria_core`, so the
answer today appears to be yes.
