# TASK-004: single-bit synchronizer demonstration (`cdc_synchronizer`)

**Priority:** P3
**Status:** open (filed 2026-11-07; was `demo_1_synchronizer` in CDC_DEMO_TODO)
**Owner:** TBD

The demo's modes all move a multi-bit counter value. The fifth primitive in the
selection guide, `cdc_synchronizer` for a single quasi-static bit, has no demo
of its own. The plan: synchronize a 1-bit "counter overflowed" flag from the
counter domain to the display domain and flash the 7-seg on it.

Worth deciding before building: whether a single-bit case teaches anything the
board does not already show (mode 0 is the counter-example: per-bit
synchronization of a bus is exactly what fails). If not, drop this with that
reason.
