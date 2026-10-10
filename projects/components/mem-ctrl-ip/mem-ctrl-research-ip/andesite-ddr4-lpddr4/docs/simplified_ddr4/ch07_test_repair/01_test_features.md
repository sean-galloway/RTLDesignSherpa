# Test and Calibration Features

DDR4 keeps DDR3's write leveling, MPR, and ZQ calibration and adds DQ Vref training, per-DRAM addressability, CAL mode, and CA parity with an ALERT_n feedback pin.

## Write leveling

Fly-by routing makes CK arrive at each DRAM at a different time, so the controller aligns DQS to CK per device.

Enablement and rules:

- Enter by loading MR1 A7 = 1; exit by loading MR1 A7 = 0. All banks must be idle for entry.
- Only DESELECT and MRS commands are legal in leveling mode. The allowed MRS changes are Qoff (MR1 A12) and the exit bit.
- Dynamic ODT is unavailable; set MR2 A[11:9] = 000 before entry. ODT controls only DQS_t/DQS_c termination; DQ termination stays off.
- Other ranks are usually quieted via MR1 A12 = 1.

Flow: assert ODT after tMOD; wait tWLDQSEN, then drive DQS_t low / DQS_c high; after tDQSL and tWLMRD send one DQS edge; the DRAM returns the sampled CK value on all DQs. Adjust DQS delay until the 0 -> 1 transition is found, then exit and wait tMOD.

| Symbol | Meaning | Value |
| --- | --- | --- |
| tWLMRD | Entry MRS to first leveling DQS edge | 40 nCK |
| tWLDQSEN | ODT assertion to DQS termination ready | 25 nCK |
| tDQSL / tDQSH | Minimum leveling strobe pulse width | - |
| tWLO | DQS edge to valid DQ feedback | 0 to 9.5 ns |
| tWLOE | Earliest-to-latest DQ feedback spread | 0 to 2 ns |
| tMOD | Exit MRS to next valid command | max(24 nCK, 15 ns) |

## Multi-Purpose Register (MPR)

DDR4 has four MPR locations in each of four pages. Page 0 is read/write; pages 1-3 are read-only.

| Page | Purpose |
| --- | --- |
| 0 | Training pattern (MPR0=01010101, MPR1=00110011, MPR2=00001111, MPR3=00000000) |
| 1 | CA parity error log |
| 2 | MRS readout, including current MR6 VrefDQ range/value |
| 3 | Vendor use only |

Enablement and rules:

- Enter MPR mode with MR3 A2 = 1. All banks idle and tRP satisfied first.
- MR3 A[1:0] selects the page; MR3 A[12:11] selects readout format. Page 0 supports serial, parallel, and staggered; pages 1-3 support only serial.
- Valid commands in MPR mode are MRS, reads, writes, deselect, refresh, and reset. Reads and writes with auto-precharge behave as plain reads/writes. Power-down entry and self-refresh are prohibited.
- The DLL must be locked before issuing MPR reads.

Flow: PREA -> wait tRP -> MRS MR3 A2=1 -> wait tMRD/tMOD -> RD with A[1:0]=00 and BA1:BA0 selecting the location -> data returns after RL = AL + CL (+ PL). Repeat reads for training, wait tMPRR (1 nCK) after the last burst, then MRS MR3 A2=0 and wait tMRD/tMOD. Page 0 reads may use tCCD_S or tCCD_L; pages 1-3 must use tCCD_L.

## ZQ calibration

ZQ calibration trims Ron and ODT against an external 240 ohm resistor.

| Symbol | Definition | Value |
| --- | --- | --- |
| tZQinit | First ZQCL after reset | 1024 nCK |
| tZQoper | Later full ZQCL | 512 nCK |
| tZQCS | Short periodic calibration | 128 nCK |

Issue ZQCL or ZQCS only when all banks are precharged and tRP is met. Keep CKE high and ODT low during the calibration window. ZQCL is required at initialization; ZQCS is used periodically. After leaving self-refresh, wait at least tXS (or the fast/abort equivalent) before issuing a ZQ command. If several DRAMs share one ZQ resistor, their calibration windows must not overlap.

## DQ Vref training

The internal DQ reference voltage is tuned through MR6.

| MR6 bit(s) | Function |
| --- | --- |
| A7 | 1 = enable training mode; 0 = disable |
| A6 | Range select (0 = range 1, 1 = range 2) |
| A5:A0 | VrefDQ value |

Range 1 spans 60-92% of VDDQ; range 2 spans 45-77%. Step size is 0.5-0.8% of VDDQ (typical 0.65%). After each MR6 value change, wait Vref_time (max 150 ns). Entry delay tVREFDQE and exit delay tVREFDQX are each 150 ns.

Training loop: enter a range, set a value, wait Vref_time, issue dummy writes/reads, and record pass/fail. The current range and value can be read back through MPR page 2. If PDA mode is active, only MRS commands are legal.

## Per-DRAM addressability (PDA)

PDA lets the controller target one DRAM in a rank for an MRS command, useful for different ODT or Vref settings per device.

- Enable with MR3 A4 = 1; exit with MR3 A4 = 0.
- Write leveling must be completed first, and both RTT_PARK and RTT_NOM need to be turned on.
- An MRS is executed only when DQ0 (x4/x8) or DQL0 (x16) is low; when that data bit is high the DRAM ignores the MRS.
- Dynamic ODT is not supported, so only MRS commands may be issued.
- Leave at least AL + CWL + BL/2 - 0.5 nCK + tMRD_PDA + PL between PDA MRS commands.

## CAL mode

CAL delays the command/address bus relative to CS_n so the DRAM can keep CA receivers off between commands.

| MR4 A[8:6] | CAL delay |
| --- | --- |
| 000 | Disabled |
| 001 | 3 nCK |
| 010 | 4 nCK |
| 011 | 5 nCK |
| 100 | 6 nCK |
| 101 | 8 nCK |
| 110-111 | Reserved |

tCAL(min) = max(3 nCK, 3.748 ns). In gear-down 2N mode, odd CAL values round up. When CAL is on, tMOD_CAL = tMOD + tCAL and tMRD_CAL = tMOD + tCAL.

## CA parity

CA parity adds an even-parity bit over ACT_n, RAS/A16, CAS/A15, WE/A14, the address bus, bank addresses, bank-group bits, and C0-C2 on 3DS devices. CKE, ODT, and CS_n are not covered.

| MR5 A[2:0] | PL | Typical speed bins |
| --- | --- | --- |
| 000 | Disabled | - |
| 001 | 4 clocks | DDR4-1600/1866/2133 |
| 010 | 5 clocks | DDR4-2400 |
| 011 | 6 clocks | RFU |
| 100 | 8 clocks | RFU |

- MR5 A4 is the parity error status bit; the controller clears it by writing 0.
- MR5 A9 enables persistent parity error mode. In that mode the DRAM resumes parity checking after ALERT_n returns high, even if the status bit has not yet been cleared.
- Parity latency adds to command latency: WL = AL + CWL + PL and RL = AL + CL + PL.
- CA parity is allowed only with DLL on. With parity enabled, only DESELECT may appear between valid commands.

On error, the DRAM ignores the command, logs the frame in MPR page 1, sets the status bit, asserts ALERT_n within tPAR_ALERT_ON, completes in-flight commands, precharges all banks after tRAS_min, holds ALERT_n for at least tPAR_ALERT_PW, then resumes with checking off until the status bit is cleared. Entry/exit delays are tMOD_PAR = tMOD + PL and tMRD_PAR = tMOD + PL.

Write/read CRC is covered in Chapter 5.

## What is not here

- No OCD command set; ZQ calibration replaces it.
- No boundary-scan or JTAG test port inside the DRAM.
- No standard user test mode beyond MPR and vendor-specific MR bits.
- MPR writes are allowed only to page 0; pages 1-3 ignore them.
- No on-die ECC or post-package repair interface exposed to the user.

**Source:** JESD79-4D sections 4.7, 4.10, 4.10.5, 4.12-4.15, 4.17, 4.17.1
