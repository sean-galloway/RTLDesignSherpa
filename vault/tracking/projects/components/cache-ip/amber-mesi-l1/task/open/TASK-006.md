# TASK-006: install a read fill as E when the response says the line is not shared

**Priority:** P3
**Status:** open (filed 2026-11-25; owner: "File an amber task")
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
