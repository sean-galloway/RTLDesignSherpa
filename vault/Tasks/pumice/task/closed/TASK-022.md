# TASK-022: Full LPDDR2 mode-register init

> **Migrated from `PUMICE-011`** on 2026-09-27, when this area's flat
> `closed.md` was split into one file per item to match the rest of the vault.
> The legacy ID is cited throughout the repo -- RTL comments, DV code, handbook
> notes, commit messages and session memory -- so it is NOT rewritten at those
> call sites; `vault/Tasks/MIGRATION_MAP.md` and this line are how an old
> `PUMICE-011` reference resolves. Body below is verbatim from the flat page.
>
> Lane chosen by reading this item's own Status line and opening, not its title:
> a keyword pass over the 35 items misclassified 14 of them.


**Status:** closed — resolved

Implemented the JEDEC JESD209-2F LPDDR2 init sequence in `init_sequencer.sv`
(memtype-gated): MRW Reset(MR63) -> ZQ Init(MR10=0xFF) -> MR1(BL8/nWR3=0x23) ->
MR2(RL3/WL1=0x01) -> MR3(DS 40ohm=0x02). The wide MR index (MA up to MR63)
reaches the CA formatter via the ROW request field packed as {MA[5:0], OP[7:0]}
(`dfi_cmd_formatter` unpacks row[13:8]=MA, row[7:0]=OP) — no 3-bit bank-port
limit. Only MR1/2/3 update the CL/CWL/BL shadow; MR63/MR10 are issued but not
shadowed. `mode_register.sv` LPDDR2 CL/CWL decode made JEDEC-faithful (MR2[3:0]
RL&WL enum).

Verified: DFISlavePHY now records decoded MRW ({index:data}); `smoke_lpddr2`
asserts init programmed {63:0x00, 10:0xFF, 1:0x23, 2:0x01, 3:0x02}. Formatter
conformance + init_sequencer FUB updated.

**NOTE (silicon):** the sim gates PHY-init-complete on config-ready (TB) so the
sequencer latches the correct memtype ("config before init"). Real LPDDR2
silicon needs memtype stable before init — a strap, or gating the sequencer's
start on `CTRL.init_start`. DDR2 (the board target) is unaffected: its reset
default IS DDR2.
