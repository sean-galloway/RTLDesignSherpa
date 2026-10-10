# ISSUE-016: three CSR resets encode a build geometry this board is not

**Status:** CLOSED 2026-09-28 (resolution below)  **Priority:** P2 -- a host script that forgets the
compensation measures nothing and reports it as clean, which has already happened.
**Owner:** TBD
**Found by:** [[TASK-015]] layer 0, auditing every `ships` claim against what the
board host actually writes.
**Related:** [[ISSUE-015]] (two host paths, one read-path tuple)

## The divergence

| field | RTL reset | this board build writes | written by |
|---|---:|---:|---|
| `DFI_PHASE.gear_ratio` | `0x2` (log2 1:4) | `0x1` (1:2) | `DDR2CharDriver.BOARD_GEAR_RATIO` |
| `DFI_PHASE.bl` | `8` | `4` | `DDR2CharDriver.BOARD_DRAM_BL` |
| `MR0.VAL` | `0x0433` | `0x0432` (BL4/CL3/tWR3) | `DDR2CharDriver.BOARD_MR0` |

`CTRL.soft_reset` reverts every pumice CSR to its RTL reset, so **every soft
reset silently puts the controller back to 1:4 / BL8 on a 1:2 / BL4 bitstream**
until something re-programs it. `DDR2CharDriver.program_geometry()` does exactly
that, and the driver comment records why it had to become the driver's job:

> Nine host scripts each re-programmed it (or forgot to); `wide_rd_sweep.py`
> forgot, ran the whole sweep at 1:4/BL8 on a 1:2/BL4 build, and reported the
> resulting never-completed reads as `beats_mismatched=0` -- a clean sweep that
> measured nothing.

So the compensation works and is centralised. The issue is that it is a
compensation for a reset that does not describe the design it ships in.

## Why this is not simply "change the reset"

pumice is parameterised for several geometries and one RDL constant serves all
of them, so moving the reset to 1:2 / BL4 makes it right for this board and wrong
for the next. The real options, and this needs a decision rather than a sweep:

1. **Track the build.** Generate these three resets from the same build
   parameters the RTL is elaborated with, so the reset is always this build's
   geometry. Removes the class permanently; costs a generation step in the RDL
   flow.
2. **Make the reset a safe no-op.** Reset to a geometry that cannot silently
   mis-measure -- e.g. leave the controller held until geometry is programmed,
   so a forgetting script fails loudly instead of measuring nothing.
3. **Accept and gate.** Keep the resets, and keep the written waivers in
   `dv/csr_reset_parity.py` so the divergence stays visible. This is the state
   today.

Option 2 is the one that matches the handbook's usual answer -- a missing
configuration should fail loudly, not read as a clean zero -- but it changes
bring-up behaviour and is therefore Sean's call.

## Note on how this was found

The layer-0 gate did NOT catch these. I populated the manifest by reading the
reset values and declaring them as the shipping values, which is precisely the
vacuous declaration the checker's own docstring warns about; the gate then
passed because the claim and the reset agreed with each other. They surfaced
only when the `ships` claims were audited against the board host's literal
writes. **A manifest gate is only as good as the evidence behind each entry**,
and "I read the reset" is not evidence about what ships. The audit is worth
re-running whenever entries are added -- it is a dozen lines and it found two
wrong claims out of 55.

---

## Closed 2026-09-28 -- by reading the hardware, which needed no decision

The issue offered three options and called for a judgement. It turned out not to
need one: the board already reports its own geometry, and the driver was simply
not asking.

`DDR2CharDriver.build_info()` reads `BUILD_CONFIG.{gear_ratio,dram_bl}` --
elaboration-time constants driven from the harness's own parameters, so, as its
docstring says, they "cannot drift from the hardware". `program_geometry()` now
takes the geometry from there instead of from the `BOARD_*` environment
constants, and derives MR0's burst-length field from the same source so MR0 and
`DFI_PHASE.bl` cannot disagree. The `BOARD_*` values remain as a fallback for a
harness too old to carry the build registers, and a divergence between the two is
printed rather than silently resolved.

That closes the actual failure mode. `CTRL.soft_reset` still reverts the pumice
CSRs to RTL resets describing a 1:4/BL8 geometry -- **the resets are unchanged,
option 3 stands** -- but the restore that follows now uses what the silicon says
it is, so a wrong environment variable can no longer put a sweep on the wrong
geometry. The failure this issue was filed for ("a script forgot, ran a whole
sweep at 1:4/BL8 on a 1:2/BL4 build, and reported beats_mismatched=0 -- a clean
sweep that measured nothing") is not reachable through this path any more.

Verified on the board at 75 MHz: `init` reports
`dfi_rate=2 gear=1 bl=4 row=13 bank=6 axi=64b beat=32b dev=16b clk=75.00MHz`,
with `write_read` clean (`mismatched=0`) and the telemetry sequence passing all
five invariants across three families.

What is NOT closed by this, and is now [[ISSUE-017]]: the same class one level
up. The RESETS are only one way to end up measuring a build you did not mean to
-- building the wrong frequency profile is another, and that one bit on the same
day.
