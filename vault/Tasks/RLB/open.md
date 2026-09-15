# RLB — Open (accepted, not started)

---

## RLB-016: an unmapped APB address hangs the RLB bus

**Priority:** P2. Not a defect in any block -- it is the subsystem's response
to an address nobody implements, and today that response is "never answer".
**Status:** open, found 2026-09-14 while building the rlb_top smoke tests.

`apbx_xbar_rlb_1to10` drives `m_cmd_ready` only inside
`if (m_cmd_valid && addr_in_range)`, where

    addr_in_range = (paddr >= BASE_ADDR) && (paddr < BASE_ADDR + 32'h0000A000)

so an access outside the 40KB window is never accepted. `apb4_slave` leaves
IDLE only `if (... && r_cmd_ready)` and asserts `s_apb_PREADY` only in BUSY on
`r_rsp_valid`, so PREADY never asserts and the transfer never completes. There
is no timeout anywhere in that path.

The response-mux default DOES have `m_rsp_pslverr = 1'b1` for an invalid
select, but it cannot fire: `r_slave_sel` only updates on an ACCEPTED command,
and an out-of-range command is never accepted. The error path is unreachable
for the case it was written for.

Contrast the RESERVED window (slave 9), which is correct: rlb_top ties it to
`PRDATA=0xDEADBEEF, PSLVERR=1, PREADY=1`, so a reserved access is reported
rather than hanging. That is the behaviour an out-of-range access should have.

NOT COVERED BY A TEST, deliberately. The APB master BFM's completion loop is
unbounded, so probing an unmapped address would hang until the cocotb timeout
killed the whole test, and hand-driving the bus to dodge that would break the
"always use the BFMs" rule. `rlb_top_tests.py` documents the omission.

**CORRECTED 2026-09-14 after Sean asked whether the apbx-xbar had a
subtractive agent. It does, and this entry had the finding backwards.**

This is not a novel defect and the fix is not new logic. The apbx-xbar family
already fixed exactly this, and the fix lives in the GENERATOR
(`projects/components/apbx-xbar/bin/apbx_xbar_generator.py`, guarded `if
N > 1`), whose own comment reads: "Emitting the decode without this is what
shipped that bug in every decoding variant." The family's regression covers it
as `test_apbx_xbar_2to4.py` Scenario APB-2TO4-21, "decode-miss returns PSLVERR
(qc round_7)". The bridge carries the same concept at AXI level -- a
subtractive catch-all answering DECERR + 0xDEADBEEF (BRIDGE-009).

`apbx_xbar_rlb_1to10.sv` is a HAND-WRITTEN sibling that sits outside the
generator flow -- no `1to10` or `rlb` variant appears anywhere in
`apbx-xbar/bin/*.py` -- so it never received a fix the rest of the family got.
That, not the missing responder, is the finding.

(1to1 and 2to1 lack the decode-miss logic legitimately: with a single slave
there is no decode to miss, which is what the `N > 1` guard expresses.)

**A SECOND divergence, currently latent.** The family derives the slave index
from the OFFSET -- `m0_cmd_offset = m0_cmd_paddr - BASE_ADDR; m0_slave_sel =
m0_cmd_offset[15:12]` -- because raw PADDR bits "silently rotated the whole
slave map relative to the documented address map" when BASE_ADDR's select bits
are nonzero. The RLB copy uses raw `m_cmd_paddr[15:12]`. At the default
BASE_ADDR of 0xFEC00000 those bits are zero so it behaves correctly today, but
it breaks the moment anyone re-bases the subsystem.

**REMEDY: regenerate, do not hand-patch.** Generating 1x10 with 4KB windows
(`--masters 1 --slaves 10 --base-addr 0xFEC00000 --slave-size 0x1000`) yields
772 lines carrying both fixes -- 17 decerr_pending references and the
offset-based decode. Verified by generating one.

NOT DROP-IN, and this is the whole cost: the generator emits `s0_apb_*` ..
`s9_apb_*` while the RLB crossbar exposes named per-peripheral ports
(`hpet_apb_*` .. `rsvd_apb_*`). Adopting it means remapping roughly 100
connection lines in rlb_top, or adding a thin naming wrapper. The reserved
slave-9 tie-off (0xDEADBEEF/PSLVERR/PREADY) stays in rlb_top either way -- the
generator has no reserved-slave concept, and does not need one.

Worth deciding at the same time: whether the RLB variant should JOIN the
generator flow (added to generate_xbars.py so it regenerates with the family)
rather than being regenerated once and drifting again. Drifting once is what
produced this entry.

Still not covered by a test in the family for the 1xN shape:
`test_apbx_xbar_1to4.py` has no decode-miss scenario -- only 2to4 does. The
rlb_top smoke suite would be the first place the 1xN decode miss is exercised.
