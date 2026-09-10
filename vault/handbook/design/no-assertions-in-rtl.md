---
title: No assertions in RTL
summary: SVA lives in formal/ bindings, never inside a module; the RLB arc reintroduced it in seven blocks under `ifndef SYNTHESIS`.
---

# No assertions in RTL

**Rule (owner's standing decision, 2026-09-03): a synthesizable module carries
no `assert`, `assume`, `cover` or `property` statement, guarded or not.**
Properties belong in the external `formal/<area>/<block>/formal_<block>.sv`
binding. If formal cannot express a contract, state it in the module header as
`CHECK BY INSPECTION: <prose>` and stop; an unchecked documented contract is
the accepted state here.

**Why:** embedded SVA trips lint, synthesis and equivalence flows in this
toolchain, and the cost lands on every downstream user of the module. The
`` `ifndef SYNTHESIS `` / `` `ifndef VERILATOR `` guard does not change that:
the Verilator cocotb flow never executes the block, so it checks nothing here
and still has to be parsed by everything else.

**The failure that wrote this note:** during the RLB RTL-bug arc (issues
#44-#60, 2026-09-08/09) every fix agent added "mirrored-decode" and
bookkeeping assertions under the guard, in all seven blocks it touched
(gpio, hpet, ioapic, pic_8259, pit_8254, pm_acpi, rtc). Six of them were
committed before a review flagged it as a standing-rule breach. The guard
made the blocks look inert, and the reviews across six rounds read them as
house idiom. They were removed in a cleanup commit; the contracts they
encoded became header prose.

**The one sanctioned form:** an elaboration-time parameter guard, an
`initial begin : param_check ... $fatal/$error end` block under
`` `ifndef SYNTHESIS ``, is not an assertion in this sense. It is what
[[sizing-invariants]] asks for ("assert the invariant at elaboration"),
eleven shared `rtl/common` and `rtl/amba` files carry one, and it checks
nothing at runtime. The RLB cleanup first removed those too; they were
restored. What stays out is SVA: `assert property`, `assume`, `cover`,
`property`, `sequence`, and any runtime `assert` in an `always` block.

**How to check:** `grep -rn "assert property\|\bassume\b\|\bcover\b\|^\s*property\|^\s*sequence"`
over the block's `rtl/` before committing. A hit is a finding; an
`initial ... param_check` block is not.

Related: [[generated-rtl-discipline]] (regen-and-diff catches the same
class in generated files), [[signal-contracts-and-kmaps]] (`CHECK BY
INSPECTION` prose form).
