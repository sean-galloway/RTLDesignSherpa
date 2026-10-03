# Timing Tables - Pack Authoring Worksheet

Per-tech timing parameters as encoded in `packs/<tech>.js`, with the JEDEC
references they were transcribed from. The condensed study-note books
(`cold_storage/MemorySpecs/docs/<tech>/ch06_*`) are the intermediate source;
this file is the cross-check against the spec.

Scope values used in `appliesTo` rules: `same_bank`, `same_group`,
`diff_group`, `diff_bank`, `diff_sid` (HBM4 SID crossings), `any`.
Command patterns support `|` alternation and `*` wildcard. Rules whose
`from` is `REF` are reference-panel-only: the drill engine never emits REF
commands, so they document the parameter without generating questions.

Cross-book symbol rule: tRTW appears in every pack even where the spec
leaves the read-to-write rule unnamed (DDR2, LPDDR2) - see
`../notes/design.md` and the books' Chapter 6.

## HBM4 (packs/hbm4.js, JESD270-4A)

Topology: 2 BG x 4 banks, sids: 2 (drill model). Real: up to 32 channels
x 2 PCs, 16-64 banks/PC, 1 KB page, 256-bit prefetch (book ch01).

| Symbol | Scope pattern | Value basis | Reference |
| --- | --- | --- | --- |
| tRCDRD | ACT -> RD/RDA same_bank | vendor | Table 108 |
| tRCDWR | ACT -> WR/WRA same_bank | vendor | Table 108 |
| tRAS | ACT -> PRE same_bank | vendor; max 9 x tREFI | Table 108 |
| tRP | PRE -> ACT same_bank | vendor | Table 108 |
| tRC | ACT -> ACT same_bank | = tRAS + tRP | Table 108 |
| tRRDL | ACT -> ACT same_group | vendor; > tRRDS in practice | Table 6 |
| tRRDS | ACT -> ACT diff_group | vendor | Table 6 |
| tFAW | ACT -> ACT any (rolling window of 4) | vendor | Table 108 |
| tRTP | RD/RDA -> PRE same_bank | MR5 nCK twin | Table 108 |
| tWR | WR/WRA -> PRE same_bank | MR3 nCK twin; feeds tDAL | Table 108 |
| tPPD | PRE -> PRE any | 2 nCK | Table 108 |
| tCCDL | col -> col same_group / same_bank | Max(4, 2.5 ns/tCK) nCK | Table 6, sec 6.3.3 |
| tCCDS | col -> col diff_group | 2 nCK | Table 6 |
| tCCDR | RD -> RD diff_sid | vendor; tCCDS+1..+2 nCK; reads only, 8H+ | Table 108 note 17 |
| tWTRL | WR -> RD same_group / same_bank | vendor; cmd form WL + 2 + tWTRL | Table 6, sec 6.3.3 |
| tWTRS | WR -> RD diff_group | vendor; cmd form WL + 2 + tWTRS | Table 6 |
| tRTW | RD -> WR any | controller formula: (RL + BL/4 - WL + 0.5) x tCK + strobe offsets | sec 6.3.3 |
| tREFI | REF -> REF (panel only) | 3.9 us; 0.5x/0.25x at trip points | Table 38 |
| tRFCab | REF -> * (panel only) | 360-530 ns by density/height | Table 41 |
| tRFCpb | REF -> * same_bank (panel only) | 240/280 ns | Table 41 |
| tRREFD | REF -> REF/ACT diff_bank (panel only) | MAX(3 tCK, 8 ns) | Table 42 |

Notes:
- All ACT-related timings reference the second rising CK edge of the
  1.5-cycle ACT command (sec 10).
- tCCDL covers same_bank too (same bank is same group); the pack lists
  both scopes explicitly rather than relying on matcher subsumption.
- PRE on a falling edge adds 0.5 tCK to internal WR/RTP accounting
  (Table 108 note 32) - below drill-model resolution, not encoded.

## DDR2 (pending - plan commit 10)

## LPDDR2 (pending - plan commit 10)
