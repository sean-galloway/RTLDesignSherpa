# TASK-003: delete, or keep dormant, the two FUBs nothing instantiates

`scoria_powerdown_ctrl` and `scoria_dfi_signal_pack` are complete, lint-clean
modules that **no design in the tree instantiates**. Either wire them or delete
them; leaving them is the one option that costs something, because the next
session reads the file list and assumes the function is present.

**Priority:** P3 — downgraded. The FEATURE question is settled (below), so
what remains is only whether two uninstantiated files are deleted or left
dormant.
**Status:** OPEN, but the decision that was blocking it is MADE.

**DECIDED 2026-09-30 (Sean): they stay unconnected.** The test applied was
parity with the reference design that passes memtest on this board, and
LiteDRAM's generated DDR3 core for the Genesys 2 has neither capability:

| Checked in `litedram_genesys2_ddr3.v` (23,542 lines) | Result |
|---|---|
| power-down / self-refresh engine | **none** — the only `power_down` hits are the MMCM's `PWRDWN` pin |
| DFI low-power channel (`dfi_lp`, `lp_req`, `lp_ack`) | **zero hits** |
| CKE management | a CSR bit: `main_litedramcore_sdram_cke = main_litedramcore_sdram_storage[1]`, fanned identically to all four phases — software raises it during init and it stays |
| `SRE` / `SRX` issue path | none |
| phase-packing block | none needed; `dfi_p0..p3_*` are per-phase by construction, as scoria's `× DFI_RATE` buses are |

So scoria holding CKE high for ever, and having no CKE port, is PARITY with the
controller that works on this hardware -- not a shortfall. Revisit only if a
power-managed target appears.

**Found while sweeping every FUB for a unit test:** the two with no
instantiation are also the two with no test, and a test for a module no build
contains proves nothing about the controller. `scoria_top` has no CKE port at
all, so `powerdown_ctrl` is an ABSENT FEATURE rather than an unconnected block
-- which is why "how does anything work with unconnected FUBs" has the answer
"nothing references them; the design is 24 of the 26 files in rtl/fub/".

## The measurement

Across `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/`, every other
FUB resolves to at least one instantiation site. These two appear only in
comments and in their own filelists:

| Module | Instantiated | CSR fields | Unit test |
|---|---|---|---|
| `scoria_powerdown_ctrl` | nowhere | none in `scoria_csr.rdl` | none |
| `scoria_dfi_signal_pack` | nowhere | n/a | none |

It is inherited, not introduced: pumice's `powerdown_ctrl` and
`dfi_signal_pack` are referenced only from comments there too. `scoria_dfi_layer`
instantiates `scoria_dfi_cdc`, `scoria_dfi_cmd_path`, `scoria_dfi_wr_serializer`
and `scoria_dfi_rd_aligner`, and does the phase/CKE/ODT work inline -- which is
`dfi_signal_pack`'s stated job.

## What is left to choose

Only housekeeping, and the two options are close in value:

- **Leave both dormant.** Zero risk, and `powerdown_ctrl` is a working starting
  point if a power-managed target ever appears. Cost: both stay in the lint
  closure (deliberately -- a module outside it is one nothing checks) and the
  next reader has to re-learn that they are not in the design.
- **Delete both.** Recoverable from git. Removes the "26 FUBs, 24 in the
  design" footnote permanently.

If `powerdown_ctrl` is ever wired, its header names two asymmetries to resolve
first: a grant arriving in the same cycle as new activity is dropped while the
scheduler may consider it taken, and clearing `enable_sref_i` while already
asleep does NOT wake the part.

## Done when

Either both files are deleted along with their filelists and the comments that
point at them, or a one-line note in each header says it is retained dormant
and why -- so the next sweep does not re-open this.

The HAS rows are already corrected: Ch 3.1 and Ch 4.1 said `powerdown_ctrl` was
INHERITED with its mechanism intact, which read as "present in the design", and
Ch 4.1 implied LiteDRAM powers down by DRAM command. Both now state the
measured position.
