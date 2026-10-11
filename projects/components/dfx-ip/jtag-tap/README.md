# jtag-tap

**Status:** Scaffold (2026-10-11) — spec pending (HAS ch03/ch04)
**Plane:** transport for both config and override planes (shared)

IEEE 1149.1 JTAG TAP: state FSM (TCK/TMS/TDI/TDO), instruction register,
data-register scan chains. Everything here lives in the TCK domain; the
planes it feeds own their own CDC crossings.

Planned structure (house layout: `rtl/`, `docs/`, `dv/`):

- `jtag_tap` — the FSM, IR, DR mux/demux.
- `jtag_tap_bscan` — 7-series `BSCANE2` wrapper so boards (NexysA7,
  Genesys2) share the FPGA's own JTAG port instead of spending four pins.
- USER-DR chain exports for the config plane (command register file)
  and the override plane (DMI).

Education notes: the TAP state machine is the classic teaching FSM —
drills can animate TAP states against live board transactions.
