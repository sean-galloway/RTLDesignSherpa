<!--
  Thanks for the contribution. Please read CONTRIBUTING.md and CLAUDE.md
  if you haven't already — they describe the conventions this repo
  enforces.
-->

## Summary

<!-- One or two sentences describing what this PR changes and why. -->

## Type of change

- [ ] Bug fix (non-breaking change that fixes an issue)
- [ ] New feature (non-breaking change that adds functionality)
- [ ] Breaking change (fix or feature that changes existing behavior in
      a way that could affect downstream consumers)
- [ ] Documentation only
- [ ] Refactor / cleanup (no functional change)
- [ ] Tooling / CI / build

## Subsystems touched

<!-- e.g., rtl/amba/shared, projects/components/stream, val/common, docs -->

## Related issue

<!-- Closes #N / Refs #N. Open an issue first for non-trivial changes. -->

## Test plan

<!--
  Be specific. What commands did you run? Did you regenerate any
  generated code (see CRITICAL RULE #0 in CLAUDE.md)? Did you lint the
  touched RTL?
-->

- [ ] `pytest <touched test paths> -v` — passes
- [ ] `verilator --lint-only <touched RTL>` — clean
- [ ] Generated files (if any) were fully regenerated, not partially
      updated
- [ ] Added / updated tests covering the change
- [ ] Updated `PRD.md` / `TASKS.md` / `KNOWN_ISSUES/` as appropriate
- [ ] Updated docs under `docs/markdown/` if user-facing behavior changed

## Conventions checklist

- [ ] Module names follow `{category}_{function}.sv`
- [ ] Active-low reset uses `ALWAYS_FF_RST` from `reset_defs.svh` (no
      hand-rolled `always_ff @(posedge clk or negedge rst_n)`)
- [ ] Memory arrays carry FPGA synthesis attributes
- [ ] Array syntax uses `[DEPTH]`, not `[0:DEPTH-1]`
- [ ] SRAM modules have no reset port
- [ ] Three mandatory TB methods present
      (`setup_clocks_and_reset` / `assert_reset` / `deassert_reset`)
- [ ] No emojis in technical documentation
- [ ] Commit messages follow `type(scope): description`

## Notes for reviewers

<!--
  Anything reviewers should pay attention to: design tradeoffs you made,
  alternative approaches you rejected, parts you're unsure about.
-->
