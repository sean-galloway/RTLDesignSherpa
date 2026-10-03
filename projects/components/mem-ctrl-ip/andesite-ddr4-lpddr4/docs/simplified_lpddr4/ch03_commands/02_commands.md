# Commands: Rules and Constraints

LPDDR4 uses two-cycle commands on a 6-bit CA bus. Each die contains two independent channels; the examples here use one channel with banks B0-B7. The device has no DLL and no bank groups. Burst length is BL16 or BL32 on-the-fly; masked writes are BL16 only. Read latency (RL) and write latency (WL) are programmed through mode registers.

## ACT - Activate

Opens row R in bank B. The command is issued as ACT-1 followed immediately by ACT-2; the row address is split across both cycles and the bank address is carried in ACT-1.

- RD or WR to the same bank may follow after tRCD.
- ACT to a different bank needs tRRD; ACT to the same bank again needs a PRE first and must satisfy tRAS (ACT-to-PRE) and tRC (ACT-to-ACT).
- On 8-bank devices, no more than four ACT or REFpb operations may fall inside a rolling tFAW window.

Core timing (x16 mode):

| Symbol | Rule |
| --- | --- |
| tRCD | max(18 ns, 4 nCK) |
| tRRD | max(10 ns, 4 nCK), relaxed to max(7.5 ns, 4 nCK) at 4267 Mbps |
| tFAW | 40 ns at most data rates, 30 ns at 4267 Mbps |
| tRAS | min = max(42 ns, 3 nCK); max = min(9 x RefreshRate x tREFI, 70.2 us) |
| tRC | tRAS + tRPab (with PREab) or tRAS + tRPpb (with PREpb) |

## RD - Burst read

Starts a BL16 or BL32 read burst from the open row. RD-1 is immediately followed by CAS-2; the starting column is a multiple of four because C1-C0 are implied zero.

- RL is programmed in the mode registers. Valid data begins RL x tCK + tDQSCK + tDQSQ after the second rising edge of the read command.
- Back-to-back reads are spaced by tCCD = 8 clocks for BL16 and 16 clocks for BL32.
- A PRE to the same bank may follow after BL/2 + max(8, RU(tRTP/tCK)) - 8 clocks, and tRAS must also be satisfied.
- The earliest WR or MWR after a RD is governed by tRTW (the spec names this symbol). With DQ ODT disabled: tRTW = RL + RU(tDQSCKmax/tCK) + BL/2 - WL + tWPRE + RD(tRPST). With DQ ODT enabled the formula includes ODT turn-on latency.

## WR - Burst write

Starts a BL16 or BL32 write burst. WR-1 is immediately followed by CAS-2. The DQS strobe must arrive before DQ by tDQS2DQ and be center-aligned with the data.

- WL is programmed in the mode registers. The first latching DQS edge occurs WL x tCK + tDQSS after the command completes.
- Back-to-back writes are spaced by tCCD = 8 clocks (BL16) or 16 clocks (BL32).
- A PRE to the same bank may follow after WL + 1 + BL/2 + RU(tWR/tCK) clocks.
- The earliest RD after a WR is WL + 1 + BL/2 + RU(tWTR/tCK) clocks after the WR command.

Core timing:

| Symbol | Rule (x16 mode) |
| --- | --- |
| tWR | max(18 ns, 6 nCK) |
| tWTR | max(10 ns, 8 nCK) |

## Masked Write

Any write that masks one or more bytes within the burst must use the Masked Write command (MWR-1 + CAS-2). Masked writes are BL16 only.

- One DMI pin per byte lane carries the mask; DMI high masks the corresponding beat across the byte, DMI low writes normally. DMI timing matches DQ timing.
- DM is enabled by MR13 OP[5]. Write DBIdc and read DBIdc are controlled separately by MR3 OP[7] and OP[6].
- Two masked writes to the same bank must be separated by tCCDMW = 32 clocks (four tCCD periods at BL16).

## PRE - Precharge

Closes the open row of one bank or all banks. PRE uses AB = 1 for all-bank precharge; AB = 0 closes the bank selected by BA[2:0].

- After a per-bank PRE wait tRPpb = max(18 ns, 4 nCK); after PREab wait tRPab = max(21 ns, 4 nCK).
- PRE must not violate tRAS after ACT, tRTP after RD, or tWR after WR.

## Auto-Precharge

Setting AP = 1 in RD-1, WR-1, or MWR-1 schedules an internal precharge at the earliest possible moment. The controller must still satisfy tRC before the next ACT to the same bank. RAS lockout ensures tRAS is not violated.

## REFab / REFpb

Refresh all banks (REFab) or one bank (REFpb). REFpb uses the bank address supplied by the controller.

- REFab requires all banks idle and refreshes every bank; wait tRFCab before ACT or another refresh.
- REFpb refreshes the addressed bank; the bank must be idle. Wait tRFCpb before ACT or another REFpb to that bank; only tRRD is needed before ACT to a different bank. REFpb commands to different banks must satisfy tpbR2pbR.
- The controller tracks an internal bank counter synchronized by RESET_n, self-refresh exit, or any REFab. Repeating a REFpb to the same bank before all eight banks have been refreshed is illegal.
- Up to eight REFab commands may be postponed or pulled in (legacy mode); modified refresh limits apply at slower refresh rates. Per-bank refresh allows up to 8 x 8 per-bank commands to be postponed or pulled in, with a maximum of 2 x 8 x 8 within 2 x tREFI.

## RFM - Refresh Management

RFM is required on some devices when the rolling accumulated ACT (RAA) counter reaches vendor thresholds.

- MR24 OP[0] = 1 indicates RFM is required. RAA increments per ACT per bank. When RAA reaches RAAIMT (MR24 OP[5:1]) additional refresh management is needed; it must never reach RAAMMT = RAAIMT x RAAMULT (MR24 OP[7:6]).
- RFMab decrements all banks' RAA by RAAIMT x RAADEC (MR36 OP[1:0]); RFMpb decrements only the selected bank by the same amount.
- RFM uses the REF encoding with CA3 = 1 when MR24 OP[0] = 1. RFM scheduling obeys the same minimum separations as REF.
- No RFM is required when the effective refresh interval tREFIe is at or below RFMTH = RAAIMT x tRC absolute min.

## Self Refresh

- Entry: SRE with all banks idle and read data complete. CKE falls; only MRR-1, CAS-2, DES, SRX, MPC, MRW-1, and MRW-2 are allowed inside self refresh (except PASR and SR abort settings).
- Minimum stay is tSR = max(15 ns, 3 nCK). Exit to valid commands waits tXSR = max(tRFCab + 7.5 ns, 2 nCK).
- After any self-refresh exit, at least one extra refresh (one REFab or eight REFpb) must be issued before re-entering self refresh.
- Abort: if MR4 OP[3] is enabled, the DRAM aborts any ongoing refresh at SR exit and does not increment the refresh counter. The controller may issue a valid command after tXSR_abort = tRFCpb + 17.5 ns. The extra-refresh requirement still applies.

## MRR / MRW / MPC

- MRR-1 + CAS-2 reads one of 64 mode registers. Valid OP code data appears on DQ[7:0] during the first 4 UI; DQS toggles for the full BL16 burst. Only DES is allowed during tMRR = 8 clocks.
- MRW is a two-cycle command (MRW-1 + MRW-2) carrying register address and data. tMRW = max(10 ns, 10 nCK); only DES is allowed during tMRW and tMRD = max(14 ns, 10 nCK). MRW is allowed from idle or active states.
- MPC provides NOP (OP6 = 0) and training functions. Write FIFO, Read FIFO, and Read DQ Calibration require CAS-2 immediately after MPC. Start/Stop DQS Oscillator and ZQCal Start/Latch do not require CAS-2 but need two additional DES/NOP cycles before the next command.

## Power-down

- Entry: CKE falls. Illegal during RD, WR, MWR, MRR, MRW, VREF range/value MRW, command bus training MRW, VRCG high-current MRW, or Start DQS Oscillator. Allowed during ACT, PRE, auto-precharge, or REF.
- Idle power-down has no rows open; active power-down has at least one row open; self-refresh power-down continues internal refresh.
- Exit: CKE rises; first valid command after tXP = max(7.5 ns, 5 nCK). At least two clock transitions must occur during tXP.

## Clock stop and frequency change

Clock stop or frequency change is allowed while CKE is low or while CKE is high with CS held low. When CKE is low, only REFab or REFpb may be executing and any ACT or PRE must have completed. When CKE is high, all commands and data bursts must have finished, RDA/WRA need four extra clocks, and normal operation resumes only after the clock is stable for at least 2 x tCK + tXP.

## NOP / Deselect

DES (CS high) holds the bus idle for one cycle and never aborts an in-flight operation. MPC with OP6 = 0 is a two-cycle NOP.

**Source:** JESD209-4E sections 4.1, 4.2, 4.3, 4.4, 4.6, 4.10, 4.12, 4.13, 4.15, 4.16, 4.17, 4.18, 4.19, 4.20, 4.21, 4.22, 4.23, 4.24, 4.35, 4.44, 4.45, 4.47
