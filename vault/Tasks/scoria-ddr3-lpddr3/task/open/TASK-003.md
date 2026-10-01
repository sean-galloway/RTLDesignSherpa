# TASK-003: decide the fate of the two FUBs nothing instantiates

`scoria_powerdown_ctrl` and `scoria_dfi_signal_pack` are complete, lint-clean
modules that **no design in the tree instantiates**. Either wire them or delete
them; leaving them is the one option that costs something, because the next
session reads the file list and assumes the function is present.

**Priority:** P2 — nothing is broken today, but one of the two is a missing
FEATURE (there is no power-down support in the wired controller at all) and the
other is dead weight that still has to be lint-clean and documented.
**Status:** OPEN. Found 2026-09-30 while sweeping every FUB for a unit test:
the two with no instantiation are also the two with no test, and a test for a
module no build contains proves nothing about the controller.

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

## What each decision costs

- **powerdown_ctrl — wire it.** Needs a CSR block (`idle_threshold`,
  `enable_pde`, `enable_sref`), a `pdn_req`/`pdn_grant` handshake in
  `scoria_cmd_arbiter`, and the exit-timing enforcement its own header delegates
  to the scheduler (tXP / tXPDLL for PDE, tXSDLL for self-refresh). Its header
  also notes two asymmetries worth resolving first: a grant arriving in the same
  cycle as new activity is dropped while the scheduler may consider it taken,
  and clearing `enable_sref_i` while already asleep does NOT wake the part.
- **powerdown_ctrl — delete it.** Honest: scoria has never powered down, no
  measurement asks for it, and self-refresh on an FPGA bring-up board buys
  nothing. The module is recoverable from git.
- **dfi_signal_pack — delete it.** The function exists in `scoria_dfi_layer`,
  so this is a second implementation of the phase split with no consumer. Two
  copies of the packing rule is exactly the drift the handbook warns about.

## Done when

Each module is either instantiated with a test that exercises it in place, or
removed along with its filelist and the comments that point at it.

## Not in scope

The power-down *feature* decision (does scoria need PDE / self-refresh at all).
That is Sean's call and belongs in the HAS; this item only requires that the
tree stop implying the answer is yes.
