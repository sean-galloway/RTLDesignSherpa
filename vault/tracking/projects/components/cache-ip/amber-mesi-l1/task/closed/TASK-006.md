# TASK-006: install a read fill as E when the response says the line is not shared

**Priority:** P3
**Status:** closed 2026-11-26 (behind a parameter, `READ_FILL_E`; filed 2026-11-25, owner: "File an amber task")
**Owner:** TBD (filed from riscv-ip/peregrine-rv32im TASK-001 stage 4)

## Why

amber installs every read-miss fill as **S** unless `PassDirty` is set (MAS
ch03/03 `fabric_ace`: "the default install state still comes from the
request class: `ReadShared` installs S"). The read issues
`ReadNotSharedDirty`, whose response carries `RRESP[3]` IsShared; amber
does not look at it. So a line no other master holds still installs S, and
the first store to it pays a CLEAN_UNIQUE upgrade round trip (measured on
the pair rig in peregrine TASK-001 stage 6: 16-18 cycles, against 1 for a
write hit on E or M).

peregrine is a single-core system: its D$ is the only coherent master, the
fabric is plain AXI4, and the memory returns `RRESP[3:2] = 0`. Every
load-then-store line pays the upgrade, which is pure cost there. With a
real ACE interconnect, IsShared = 0 means the same thing: installing E is
what the protocol allows (IHI 0022H, ReadNotSharedDirty response rules).

## What

On a read-miss fill, install **E** when the response has IsShared = 0 and
PassDirty = 0, S when IsShared = 1, M when PassDirty = 1 (unchanged).
Write-allocate (ReadUnique) is unchanged.

- Check what the pair rig's fabric (`amber_pair_fabric`) and onyx return in
  `RRESP[3]` today. If they always answer 0, the rig installs E too and the
  coherence suites change shape: the second reader's snoop must now find E
  and downgrade it. That is the correct MESI behaviour, but every directed
  test that assumes "a fill is S" needs checking. If either fabric does not
  compute IsShared, it must be fixed, or the change must sit behind a
  parameter that peregrine sets.
- jet and jet-prime share `l1_fill`: keep their behaviour unless the same
  question is answered for them.

## Done when

- The install rule is in the MAS (ch03 fabric_ace) and the tag-model
  formal property for fills.
- amber FULL, common-ip FULL, jet / jet-prime / onyx gates are green.
- peregrine's `test_peregrine_amber_latency` reports the load-then-store
  case as a write hit (latency 1) where the line is unshared, and the
  peregrine CPI effect is measured.

## Not decided here

Unconditional (protocol-correct whenever the fabric computes IsShared) or
behind a parameter: decide after checking the two fabrics above.

## Resolution (2026-11-26)

**The fabric check.** Neither fabric computes IsShared. `amber_pair_fabric`
and `onyx_ccu` return a 2-bit `rresp` to the caches, and on the AXI4 plane
(`amber_top`) `l1_axi4_plane` pads `RRESP[3:2]` to 0. If the rule were
"IsShared = 0 installs E", the pair rig would install E beside the other
cache's S copy. So per "Not decided here", the change sits behind a
parameter instead of being unconditional.

**What was built:**
- `READ_FILL_E` (default 0) on `l1_control`, `l1_coh_core` and `amber_top`.
  1 means the cache is the system's only coherent master, so a
  ReadNotSharedDirty fill without PassDirty installs E. PassDirty still
  installs M. ReadUnique and upgrades are unchanged.
- Only `peregrine_top` sets it to 1 (one D$, snoop port tied idle). With 0
  the install logic is identical to before: the regenerated formal flat
  differs only in the constant.
- E was already handled everywhere else. A write hit on E takes the
  HIT_WR fast path, and the snoop CRRESP and next state for E are in
  Table 3.0.
- `amber_ace_top` (the 4-bit ACE `RRESP`) still ignores IsShared. Honouring
  it there needs a fabric that computes it; no such fabric exists yet.

**Formal.** New property `ap_fill_install_rule`, stated independently of
the DUT's `install_state`: with no armed snoop effect, a ReadNotSharedDirty
fill without PassDirty installs S at the flat's `READ_FILL_E = 0`, and every
other fill installs M. The mutant (flat constant flipped to E) fails it at
step 24. The existing `ap_fill_install` passes that mutant, because it
compares against the DUT's own `install_state_eff`. The flat pins
`READ_FILL_E=0` and was regenerated against the canonical root. amber
control prove (depth 48, 42 min), cover and live PASS; peregrine top_props
prove and cover PASS.

**peregrine.** CPI harness, HEAD against HEAD plus this change (the
baseline reproduces `var_real` exactly):
- 7 of 58 programs get faster and none get slower;
- kernels 105,055 -> 104,975 cycles (-0.08%), rv32ui -0.04%, rv32um 0.

The saving is small because most lines a kernel stores to are first
brought in by a store, which already installs M.

**Deviation from "Done when".** `test_peregrine_amber_latency` runs on
amber's two-cache pair rig, which must keep `READ_FILL_E = 0`. Its
load-then-store case therefore still measures the upgrade. The
peregrine-side effect is measured by the CPI harness instead.

Regressions (clean-all first, no reruns): peregrine FULL 88/88, amber FULL
121/121, common-ip FULL 255/255. OOC `peregrine_top` at 13.333 ns, 0.2 ns
uncertainty in: +0.375 (`MUL_DSP=0`), +0.329 (`MUL_DSP=1`). jet, jet-prime and onyx include
none of the edited files (onyx's rig is built on `jet_prime_top`).

Docs: amber HAS ch05 parameters; amber MAS ch03/03 fabric_ace and ch02/02
pending-fill bypass; peregrine PRD history, HAS ch05 performance, MAS
ch04/06 D-side, the simplified book ch05; books rebuilt at v0.1.
