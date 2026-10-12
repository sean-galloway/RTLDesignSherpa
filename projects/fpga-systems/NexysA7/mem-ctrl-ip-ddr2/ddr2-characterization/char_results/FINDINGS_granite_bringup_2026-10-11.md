# Granite A7 first bring-up — 2026-10-11

## Verdict

**Partial PASS, one open defect.** The product SKU comes up far enough to
initialize the DRAM; the read-data return path hangs.

## Evidence (Nexys A7-100T, serial 210292BFA3EE, granite bitstream @ 75 MHz)

- Bitstream: built 2026-10-11 (`targets/granite`), WNS +9.272 ns, TNS 0,
  30,453 LUTs (48.0% vs pumice's 35,316 / 55.7% — the shed CAMs/knobs).
- `make program` clean (after staging the bit at the flow's expected path —
  see commit history; HOLD-dir fallback initially flashed the pumice keep).
- Host handshake: BUILD_ID = 0x44445232 (harness is controller-independent,
  identical map — as designed).
- `init`: soft reset, controller config, and geometry all completed —
  the board banner printed `DDR2 v1 dfi_rate=2 gear=1 bl=4 row=13 bank=6
  axi=64b beat=32b dev=16b clk=75.00MHz`.
- **STATUS = 0x1 → `init_done` = 1**: the DRAM initialized through granite's
  `mc_xddr2_init_sequencer` and the training plane's maintenance path.
  The init/training/maintenance request-grant machinery works on silicon.
- **Defect:** the read-path leveling sweep then hangs silently — no bitslip
  output at all (pumice prints `bitslip 0: eye taps …` within seconds;
  granite printed nothing for >150 s; the full run was killed at 1 h).
  Reads are issued but no read data ever returns to the host.

## Working hypothesis (check first)

The ring-ticket contract. In pumice, `mc_storage_plane`'s `mc_rd_cmd_cam`
issues the rd_return_ring ticket at insert ("ticket at insert"). Granite
has **no storage plane** — `mc_xddr2_entry_store` closes the seam. If the
entry store does not issue the ticket / does not service
`mc_rd_return_ring`'s insert-side contract for reads, the scheduler can
issue the RD and the PHY can return data, but the return never routes home
— exactly a silent leveling hang with init_done=1.

Compare: `mc_xddr2_entry_store.sv` read-side ticket/return wiring vs what
`mc_axi4_plane`'s `mc_rd_return_ring` expects (and vs how
`mc_storage_plane`/`mc_rd_cmd_cam` did it pre-extraction). The cocotb fub
tests for the entry store (if any) exercise the sch vectors but likely not
the return contract — that gap is why lint+sim were green.

## Environment notes for the next session

- Board restored to the pumice bitstream (known-good) after the session.
- Run bring-up from `targets/granite` (`make run SEQUENCES="init …"`),
  UART = ttyUSB3 (Digilent if01). Note: stdout is block-buffered when
  redirected — use `python3 -u` or expect silent hangs.
- Pumice post-rename reference data: `char_post_rename_2026-10-11.csv`
  (matrix ALL PASS; anchor open_page/incremental 561.2 MB/s vs the
  2026-09-27 in-book 561.1 — rename-neutral).
