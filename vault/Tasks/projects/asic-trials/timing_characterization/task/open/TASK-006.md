# TASK-006: Compressor-cell A/B stamp experiment — CSA SRT divider inline vs structural

**Status:** Planned
**Priority:** P3 (Low)
**Effort:** ~1 day

**Description:**

`rtl/math/` now has a carry-save SRT radix-2 divider in two behaviorally
identical forms: `math_divider_srt_radix2_csa` (inline XOR/majority 3:2
equations) and `math_divider_srt_radix2_csa_structural` (both 3:2 stages
instantiate `math_adder_carry_save_nbit`). The open question is whether
primitive-cell structure changes FPGA mapping (LUT packing, carry-chain
inference) versus inline equations. Both are `parameter int DATA_WIDTH`
modules; the hybrid ripple-prefix adder family is also parameterized if the
experiment expands.

**Work items:**

- [ ] Stamp fixed-width variants of both CSA dividers at 16/32/64 bits
      following the repo per-width idiom: `math_divider_srt_radix2_csa_{016,032,064}`
      and `math_divider_srt_radix2_csa_structural_{016,032,064}` (wrapper
      modules + generated filelists + per-width DV at gate/func/full, same
      shape as the hybrid adder wrappers).
- [ ] Run the OOC synthesis flow (`rtl/amba/fpga/tcl/monitor_synth.tcl` with
      `BRIDGE_TOP` / `FPGA_FILELIST` per stamped module, Kintex-7 part as in
      the scoria flow) — **sixteen runs per configuration** so a single
      lucky/unlucky placement cannot masquerade as a structural difference
      (owner: "the reason for sixteen is in case there is a one-off high/low
      synth result"). Record LUTs, FFs, logic levels, and
      `timing_worst_reg2reg.txt` per run.
- [ ] Alternative variance probe if runs are too slow: one stamp top per
      width instantiating 16 copies of the divider with independent
      input registers, single synthesis — intra-design spread instead of
      inter-run spread.
- [ ] Compare distributions (median + spread) inline vs structural per
      width; conclude whether cell structure matters on the target part.

**Done when:**

A short report under `projects/asic-trials/` (or the handbook asic area, at
the doer's discretion) holds the per-run table, the distribution comparison,
and a keep/refactor/revert recommendation for the structural style.

**Notes:**

- RTL, filelists, and full DV for both A/B modules already land via commit
  `17fafaa42` (2026-10-11); this task only stamps widths and runs the flow.
- If the experiment shows a real gap, the same structural treatment can be
  applied to the radix-4 divider datapath or revisited for the multiplier
  trees — file follow-ups from the results, not in advance.
