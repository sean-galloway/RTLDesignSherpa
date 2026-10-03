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

## DDR2 (packs/ddr2.js, JESD79-2F)

Topology: flat 8 banks, sids: 0 (drill model). Real: 4 banks (512 Mb and
below) / 8 banks (1 Gb+), 1-2 KB pages, x4/x8/x16, NO bank groups.
Scopes used: same_bank / diff_bank / any.

| Symbol | Scope pattern | Value basis | Reference |
| --- | --- | --- | --- |
| tRCD | ACT -> RD/WR same_bank | 10-15 ns by bin | sec 3.5, Tables 41-43 |
| tRAS | ACT -> PRE same_bank | 45 ns min, 70 us max | sec 3.5 |
| tRP | PRE -> ACT same_bank | bin-matched to tRCD | sec 3.5 |
| tRC | ACT -> ACT same_bank | = tRAS + tRP (55-60 ns @800) | sec 3.5 |
| tRRD | ACT -> ACT diff_bank | 7.5 ns (1KB) / 10 ns (2KB page) | sec 3.7 |
| tFAW | ACT -> ACT any (rolling window of 4) | 35-50 ns by page/speed | sec 3.7 |
| tRTP | RD/RDA -> PRE same_bank | 7.5 ns; cmd form AL+BL/2+max(RU(tRTP),2)-2 | sec 3.8 |
| tWR | WR/WRA -> PRE same_bank | 15 ns; MR programs WR=RU(tWR/tCK) | sec 3.8 |
| tDAL | WRA -> ACT same_bank | = WR + tRP clocks; also >= tRC | sec 3.8 |
| tCCD | RD->RD / WR->WR any (same direction only) | 2 clocks = BL/2 at BL4 | sec 3.6.1 |
| tRTW | RD -> WR any (book symbol) | BL/2 + 2 clocks (4@BL4, 6@BL8) | sec 3.6.3 (unnamed) |
| tWTR | WR -> RD any | 7.5 ns (10 ns @400); CL-1+BL/2+RU(tWTR) | sec 3.6.2 |
| tREFI | REF -> REF (panel only) | 7.8 us (3.9 us 85-95 C); 8 postponable | sec 3.9 |
| tRFC | REF -> REF/ACT (panel only) | 75-327.5 ns by density | Table 40 |
| tXSRD | SRX -> RD (panel only) | 200 clocks (DLL relock) | sec 3.10 |

Notes:
- tCCD is same-direction only in the pack, matching the book's gap sheet;
  direction changes are governed by tRTW/tWTR, which dominate tCCD there.
- Latency context (not engine params): RL = AL + CL, WL = RL - 1; AL from
  EMR1 A5-A3 (posted CAS), CL 2-6 from MR.

## LPDDR2 (packs/lpddr2.js, JESD209-2F)

Topology: flat 8 banks, sids: 0 (drill model). Real: 4 banks (512 Mb and
below) / 8 banks (1 Gb+ S4), x8/x16/x32, no DLL, no ODT, no bank groups.
Scopes used: same_bank / diff_bank / any.

| Symbol | Scope pattern | Value basis | Reference |
| --- | --- | --- | --- |
| tRCD | ACT -> RD/WR same_bank | 15/18/24 ns, min 3 tCK | Table 103 |
| tRAS | ACT -> PRE same_bank | 42 ns, min 3 tCK; max 70 us | Table 103 |
| tRPpb | PRE -> ACT same_bank | 15/18/24 ns, min 3 tCK | Table 103 |
| tRPab | PREA -> ACT (panel only) | = tRPpb on 4-bank; longer on 8-bank | Table 103 |
| tRC | ACT -> ACT same_bank | = tRAS + tRPpb | Table 103 |
| tRRD | ACT -> ACT diff_bank | 10 ns, min 2 tCK; REFpb counts for tFAW | Table 103 |
| tFAW | ACT -> ACT any (8-bank only) | 50 ns, min 8 tCK | Table 103 |
| tRTP | RD/RDA -> PRE same_bank | 7.5 ns, min 2 tCK; count from BL/2-2 (S4) | sec 5.9 |
| tWR | WR/WRA -> PRE same_bank | 15 ns, min 3 tCK; MR1 nWR field | Table 103 |
| tCCD | RD->RD / WR->WR any (same direction only) | S4: 2 tCK; S2: 1 tCK | sec 5.6 |
| tWTR | WR -> RD any | 7.5/10 ns, min 2 tCK; WL+1+BL/2+RU(tWTR/tCK) | sec 5.9.1 |
| tRTW | RD -> WR any (book symbol) | RL+RU(tDQSCKmax/tCK)+BL/2+1-WL | sec 5.9.2 (unnamed) |
| tREFI | REF -> REF (panel only; reference avg) | 15.6/7.8/3.9 us by density | sec 5.10 |
| tRFCab | REF -> REF/ACT (panel only) | 90/130/210 ns by density | Table 101 |
| tRFCpb | REF -> ACT same_bank (panel only) | 60 ns (<=4 Gb); 8 REFpb = 1 REFab | Table 102 |

Notes:
- Panel-only convention extension: tRPab uses from 'PREA' (all-bank
  precharge), a command the engine never emits - same trick as the REF
  rules, keeping it visible in the reference panel without ever matching.
- The real refresh contract is R refreshes per rolling tREFW (32 ms);
  tREFI is a reference average only. Burst/pause patterns are legal.
- Latency context (not engine params): RL/WL from MR2 by speed grade
  (8/4 at 1066 down to 3/1 at 466-); tDQSCK is analog (no DLL) and may
  span multiple clocks.

## DDR3 (packs/ddr3.js, JESD79-3F)

Topology: flat 8 banks, sids: 0 (drill model). Real: 512 Mb-8 Gb, all
with 8 banks (BA0-BA2), 1-2 KB pages, x4/x8/x16, NO bank groups.
Scopes used: same_bank / diff_bank / any.

| Symbol | Scope pattern | Value basis | Reference |
| --- | --- | --- | --- |
| tRCD | ACT -> RD/WR/RDA/WRA same_bank | 10-15 ns by bin | sec 4.11, Tables 62-67 |
| tRAS | ACT -> PRE same_bank | 36-37.5 ns min; max 9 x tREFI | sec 4.11 |
| tRP | PRE -> ACT same_bank | bin-matched to tRCD | sec 4.11, Tables 62-67 |
| tRC | ACT -> ACT same_bank | = tRAS + tRP (46.5-52.5 ns by bin) | sec 4.11 |
| tRRD | ACT -> ACT diff_bank | max(4 nCK, 6-10 ns by speed); 1KB/2KB page variants | sec 4.12 |
| tFAW | ACT -> ACT any (rolling window of 4) | 25-50 ns by speed/page | sec 4.12 |
| tRTP | RD/RDA -> PRE same_bank | max(4 nCK, 7.5 ns); cmd form AL + BL/2 + RU(tRTP) | sec 4.13 |
| tWR | WR/WRA -> PRE same_bank | 15 ns; MR0 WR codes 5-16 | sec 4.13 |
| tDAL | WRA -> ACT same_bank | = WL + BL/2 + WR + tRP clocks; also >= tRC | sec 4.13 |
| tCCD | RD->RD / WR->WR any (same direction only) | 4 nCK = BL/2 at BL8 | sec 4.13 |
| tRTW | RD -> WR any (book symbol) | RL + tCCD + 2 - WL at BL8 (spec gives relation unnamed) | sec 4.14 |
| tWTR | WR -> RD any | max(4 nCK, 7.5 ns); cmd form WL + BL/2 + RU(tWTR) | sec 4.14 |
| tMRD | MRS -> MRS (panel only) | 4 nCK | sec 3.4 |
| tMOD | MRS -> * (panel only) | max(12 nCK, 15 ns) | sec 3.4 |
| tDLLK | MRS -> RD/RDA (panel only) | 512 nCK after DLL reset | sec 3.4.1, 4.13 |
| tREFI | REF -> REF (panel only) | 7.8 us (3.9 us 85-95 C); 8 postponable / 8 pulled-in | sec 4.15 |
| tRFC | REF -> REF/ACT (panel only) | 90/110/160/260/350 ns by density | sec 4.15, Table 68 |
| tXS | SRX -> ACT/PRE/MRS/REF (panel only) | max(5 nCK, tRFC + 10 ns); DLL commands add tDLLK | sec 4.16 |
| tXP | SRX -> * (panel only) | max(3 nCK, 6-7.5 ns by speed) | sec 4.17 |

Notes:
- tCCD is same-direction only in the pack, matching the book's gap sheet;
  direction changes are governed by tRTW/tWTR, which dominate tCCD there.
- Latency context (not engine params): RL = AL + CL (MR0 CL, MR1 AL);
  WL = AL + CWL (MR2 CWL). DDR3 changed WL from RL-1 to an independently
  programmed CWL.
- PREA uses the same tRP as PRE in DDR3 (no extra clock as in DDR2).

## LPDDR3 (packs/lpddr3.js, JESD209-3C)

Topology: flat 8 banks, sids: 0 (drill model). Real: x16/x32 organizations,
densities 1 Gb-32 Gb, no bank groups, no DLL.
Scopes used: same_bank / diff_bank / any.

| Symbol | Scope pattern | Value basis | Reference |
| --- | --- | --- | --- |
| tRCD | ACT -> RD/WR/RDA/WRA same_bank | 15/18/24 ns, min 3 tCK | Table 64 |
| tRAS | ACT -> PRE same_bank | min max(42 ns, 3 tCK); max min(70.2 us, 9 x RM x tREFI) | Table 64 |
| tRPpb | PRE -> ACT same_bank | 15/18/24 ns, min 3 tCK | Table 64 |
| tRPpab | PREA -> ACT (panel only) | 18/21/27 ns, min 3 tCK | Table 64 |
| tRC | ACT -> ACT same_bank | = tRAS + tRPpb (or + tRPpab after PREA) | Table 64 |
| tRRD | ACT -> ACT diff_bank | 10 ns, min 2 tCK; REFpb counts for tFAW | Table 64 |
| tFAW | ACT -> ACT any (rolling window of 4) | 50 ns, min 8 tCK | Table 64 |
| tRTP | RD/RDA -> PRE same_bank | 7.5 ns, min 4 tCK; BL/2 + max(4, RU(tRTP/tCK)) - 4 | sec 4.7 |
| tWR | WR/WRA -> PRE same_bank | 15 ns, min 4 tCK; MR1 nWR field | Table 64 |
| tCCD | RD->RD / WR->WR any (same direction only) | 4 tCK = BL/2 | sec 4.5 |
| tRTW | RD -> WR any (book symbol) | RL + RU(tDQSCKmax/tCK) + BL/2 + 1 - WL | sec 4.5 (unnamed) |
| tWTR | WR -> RD any | 7.5 ns, min 4 tCK; WL + 1 + BL/2 + RU(tWTR/tCK) | sec 4.5 |
| tMRW | MRW -> MRW (panel only) | 10 tCK | sec 4.10 |
| tMRR | MRR -> MRR (panel only) | 4 tCK | sec 4.10 |
| tMRD | MRW -> * (panel only) | max(14 ns, 10 nCK) | sec 4.10 |
| tREFI | REF -> REF (panel only; reference avg) | 7.8 us at <=85 C | sec 4.8 |
| tRFCab | REF -> REF/ACT (panel only) | 130 ns (1-4 Gb), 210 ns (6-8 Gb) | sec 4.8 |
| tRFCpb | REFpb -> ACT/REFpb same_bank (panel only) | 60 ns (1-4 Gb), 90 ns (6-8 Gb) | sec 4.8 |
| tXSR | SRX -> * (panel only) | max(tRFCab + 10 ns, 2 nCK) | sec 4.13 |
| tXP | SRX -> * (panel only) | max(7.5 ns, 3 nCK) | sec 4.14 |
| tCKE | SRX -> * (panel only; CKE pulse width) | max(7.5 ns, 3 nCK) | sec 4.14 |

Notes:
- tCCD is same-direction only in the pack, matching the book's gap sheet;
  direction changes are governed by tRTW/tWTR, which dominate tCCD there.
- tRTW is the cross-book symbol; JESD209-3C gives the read-to-write relation
  unnamed. The tDQSCK term is the LPDDR3 signature because there is no DLL.
- tRPpab uses from 'PREA', tRFCpb uses from 'REFpb', and the init/refresh
  panel-only params use from 'MRW' / 'MRR' / 'SRX': all are commands the
  drill engine never emits, so they render in the reference panel only.
- Latency context (not engine params): RL/WL programmed in MR2; tDQSCK is an
  analog window (2.5-5.5 ns, 5.62 ns derated) that may span multiple clocks.
