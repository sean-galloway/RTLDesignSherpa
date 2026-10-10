# Test and Calibration Features

DDR3 adds several calibration and diagnostic aids that DDR2 lacked: write leveling, the Multi-Purpose Register (MPR), ZQ calibration, and self-refresh temperature selection.

## Write leveling

Because command/address/clock routing on DDR3 modules uses fly-by topology, CK arrives at each DRAM at a different time relative to its DQS. Write leveling lets the controller align DQS to CK per rank.

Enablement and rules:

- Enter by loading MR1 with A7 = 1. All banks must be idle first.
- Exit by loading MR1 with A7 = 0. After the exit MRS, observe tMOD (and tMRD for further MRS commands) before normal traffic.
- Only NOP, DESELECT, and MRS commands are legal in leveling mode; the allowed MRS changes are the Qoff bit (A12) and the exit bit (A7).
- Other ranks are typically quieted by setting their MR1 A12 = 1, disabling their output buffers so only the target rank feeds back.
- While leveling is active, asserting ODT turns on termination for DQS/DQS# only; DQ termination remains off.

Procedure outline:

```
MRS MR1 A7=1                    # enter write leveling
wait tMOD, then assert ODT
wait tWLDQSEN, then drive DQS low / DQS# high
after both tDQSL and tWLMRD are satisfied, send one DQS/DQS# edge
DRAM samples CK with the rising DQS edge and returns the CK value on DQ
repeat while adjusting DQS delay until a 0 -> 1 transition is found
stop driving DQS, deassert ODT, MRS MR1 A7=0  # exit
wait tMOD before the next valid command
```

Key timing symbols:

| Symbol | Meaning |
| --- | --- |
| tWLDQSEN | Wait from ODT assertion until the DRAM has turned on DQS termination |
| tWLMRD | Wait from the entry MRS until the first DQS/DQS# leveling edge |
| tDQSL / tDQSH | Minimum low/high pulse width for the leveling strobe edge |
| tWLO | Delay from the leveling DQS edge to valid DQ feedback |
| tWLOE | Allowed spread between the earliest and latest DQ transitions during feedback |
| tMOD | Mode-register command update delay after the exit MRS |

The controller adjusts the DQS delay so the DQS rising edge lines up with the CK rising edge at each DRAM, satisfying tDQSS, tDSS, and tDSH.

## Multi-Purpose Register (MPR)

The MPR is a read-only register that sources a fixed calibration pattern. It is used for read-timing training and debug, not for normal data access.

Enablement and rules:

- Load MR3 with A2 = 1 to enter MPR mode. Before that MRS, all banks must be idle and tRP must be satisfied.
- MR3 A[1:0] selects the location; only `00b` (predefined calibration pattern) is valid; the other encodings are RFU.
- In MPR mode the command set shrinks to RD and RDA only. RDA is treated as a plain read; its auto-precharge request is ignored. Writes, power-down entry, and self-refresh entry are not allowed.
- Issue MPR reads only after the DLL has locked.

Predefined pattern readout:

| Burst setting | A2 | Burst order | Data pattern |
| --- | --- | --- | --- |
| BL8 | 0 | 0,1,2,3,4,5,6,7 | 0,1,0,1,0,1,0,1 |
| BC4 lower nibble | 0 | 0,1,2,3 | 0,1,0,1 |
| BC4 upper nibble | 1 | 4,5,6,7 | 0,1,0,1 |

Address rules during MPR reads: drive A[1:0] = `00b`; A2 chooses the nibble for BC4; A12/BC selects burst-chop on-the-fly; all other address and bank bits are don't-care. DQ[0] carries the pattern, and the remaining DQ pins either repeat DQ[0] or drive 0.

Relevant timings: tRP before entry, tMRD/tMOD around the enabling and disabling MRS commands, normal read latency (RL = AL + CL), and tMPRR = 1 nCK after the last MPR burst before exiting MPR mode.

## ZQ calibration

ZQ calibration trims the output driver impedance (Ron) and on-die termination (ODT) against an external reference.

| Symbol | Definition | Typical value |
| --- | --- | --- |
| tZQinit | First ZQCL after reset/initialization | max(512 nCK, 640 ns) |
| tZQoper | Subsequent ZQCL during normal operation | max(256 nCK, 320 ns) |
| tZQCS | Short ZQCS for periodic calibration | max(64 nCK, 80 ns) |

- A precision 240 ohm resistor (RZQ) connects the ZQ ball to ground; it may be shared between two DRAMs only if their calibration windows do not overlap.
- ZQCL performs the full calibration; ZQCS performs a shorter correction for voltage and temperature drift.
- Both require all banks precharged and tRP satisfied. The channel must be quiet during the calibration window.
- A ZQCL is required during initialization. Periodic ZQCS commands are recommended afterwards; the interval depends on system temperature and voltage drift rates.
- After self-refresh exit, an explicit ZQ command is required if calibration is needed; the earliest issue time is tXS.
- If multiple DRAMs share one ZQ resistor, their calibration windows must not overlap.

## Self-refresh temperature (SRT / ASR)

Self-refresh timing is configured in MR2:

| MR2 A6 | MR2 A7 | Meaning |
| --- | --- | --- |
| 0 | 0 | Manual SRT, normal temperature range |
| 0 | 1 | Manual SRT, extended temperature range (only if the part supports it) |
| 1 | 0 | Auto Self-Refresh (ASR) enabled; DRAM manages its own refresh rate |
| 1 | 1 | Illegal |

- A6 selects ASR when the device supports it; A7 selects extended-range manual mode when ASR is off.
- If the part does not support extended temperature range, A7 must stay 0.
- Refer to the data sheet or SPD to discover which options are actually implemented.

## Test mode

MR0 A7 selects a vendor-specific test mode. The only user requirement is to keep it 0. No standard user-visible test mode exists at that bit.

## What is not here

- No OCD (off-chip driver calibration) command set: DDR3 replaces it with ZQ calibration.
- No boundary-scan / JTAG test port inside the DRAM device.
- No writes to the MPR; the pattern is fixed and read-only.
- No per-pin loopback test mode.
- No on-die repair readback or post-package repair interface exposed to the user.

**Source:** JESD79-3F sections 3.4.2.3, 4.8, 4.9, 4.10, 5.5
