# RLB — Active (in progress)

---

Nothing active. RLB-004 closed 2026-09-14 (see `closed.md`) once all nine
`bug` issues were confirmed closed on GitHub and the whole area was verified
green: 63 passed, 0 failed at REG_LEVEL=FULL on a clean build.

The remaining RLB items live in `open.md` and none of them is a defect.
RLB-010 closed 2026-09-14: its formal area was created, and its last bullet --
the combinational clock mux -- was resolved by `rtc_clk_mux` in `ae03c6b43`,
which supplies the device-specific cell the entry named as the real answer.
