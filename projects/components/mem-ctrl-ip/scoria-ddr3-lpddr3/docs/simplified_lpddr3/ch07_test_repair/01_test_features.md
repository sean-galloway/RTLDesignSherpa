# Test Features

LPDDR3 has no JTAG boundary scan, no DDR3-style MPR, no OCD calibration engine, and no standard write-CRC or gear-down mode. Instead it exposes a small set of calibration and observation mechanisms, all reached through MRW or MRR.

## MRR as the observation port

A Mode Register Read returns the contents of any mode register. The command is recognized when CS_n is low with CA0-CA2 low and CA3 high; the register address is built from the remaining CA fields. Valid data appears on DQ[7:0] on the first beat after the programmed read latency, and the burst is always eight clocks long. Only NOP is legal during the tMRR interval. MRR is the normal way to read MR0 at boot to confirm device-auto-initialization status, ZQ pin self-test results, and supported write-latency/read-latency options.

## DQ calibration (MR32 / MR40)

Because LPDDR3 has no DLL, the controller must train its read capture against a known pattern. MRR to MR32 returns Pattern A and MRR to MR40 returns Pattern B. For x16 parts the expected bits are driven on DQ0 and DQ8; for x32 parts they are driven on DQ0, DQ8, DQ16, and DQ24. The remaining data pins may either repeat DQ0 or drive zero. Pattern A toggles every bit time (1-0-1-0...), while Pattern B produces pairs of identical values (0-0-1-1-0-0-1-1). Unlike ordinary MRR bursts, the DQ calibration bursts define valid content on every beat so the host can tune capture timing on multiple edges.

## ZQ calibration (MR10)

Output-driver and ODT calibration is initiated by MRW to MR10 with one of four opcodes:

| Opcode | Command | Typical use |
| --- | --- | --- |
| 0xFF | ZQINIT | Required once after reset; ~1 us |
| 0xAB | ZQCL | Long maintenance calibration; ~360 ns |
| 0x56 | ZQCS | Short maintenance calibration; ~90 ns |
| 0xC3 | ZQRESET | Return to default calibration; max(50 ns, 3 tCK) |

A 240 ohm, +/-1% resistor must be connected between the ZQ ball and ground. ZQ commands are only legal when all banks are precharged, ODT is disabled, and the DQ bus is quiet; only NOP may be issued during the calibration window. If several devices share one ZQ resistor, their initialization, long, and short calibrations must not overlap, although ZQRESET overlap is allowed.

## CA training (MR41 / MR48 / MR42)

Commands travel across the narrow CA bus over two cycles, so the controller must align each CA bit to the clock before normal operation. Training is entered by MRW to MR41, performed in two passes, and exited by MRW to MR42.

- First pass (MR41): calibrate CA0, CA1, CA2, CA3, CA5, CA6, CA7, and CA8. The DRAM echoes each CA value on specific DQ pins according to the MR41 CA-to-DQ map.
- Mapping change (MR48): switch the mapping so the remaining pins can be observed.
- Second pass (MR48): calibrate CA4 and CA9.
- Exit (MR42): return to normal operation.

MR41, MR48, and MR42 use special encodings that are intentionally identical on the rising and falling clock edges so the DRAM can recognize them even before CA timing is adjusted. During training the clock phase may be intentionally varied while CS_n is high and CKE is low.

Key CA-training timings:

| Symbol | Definition | Value |
| --- | --- | --- |
| tCAMRD | First CA calibration command after mode entry | 20 tCK |
| tCAENT | First CA calibration command after CKE goes LOW | 10 tCK |
| tCACKEL | CKE LOW after CA-training mode is programmed | 10 tCK |
| tCACKEH | CKE HIGH after the last CA-training result is driven | 10 tCK |
| tCAEXT | CA-training exit command after CKE is HIGH | 10 tCK |
| tCACD | Delay from one CA calibration command to the next | RU(tADR + 2 x tCK) |
| tADR | Data-out delay after a calibration command | 20 ns max |
| tMRZ | MRW CA-training exit command to DQ tri-state | 3 ns min |

## Write leveling (MR2[7])

Write leveling lets the controller align each DQS rising edge to the clock at the DRAM pin. The device enters write-leveling mode when MR2[7] is set HIGH and leaves when MR2[7] is cleared. Only NOP or the exit MRW is legal while in this mode.

The controller first holds DQS_t LOW and DQS_c HIGH for at least tWLDQSEN, then issues the first DQS edge no sooner than tWLMRD. The DRAM samples CK with that DQS rising edge and asynchronously drives the sampled value onto every DQ bit in the byte after tWLO. The controller iterates its DQS delay until it sees a 0-to-1 transition, which locks the DQS-to-CK relationship needed for tDQSS.

| Symbol | Definition | Value |
| --- | --- | --- |
| tWLDQSEN | DQS_t/DQS_c delay after entering write-leveling mode | 25 ns min |
| tWLMRD | First DQS edge after entering write-leveling mode | 40 ns min |
| tWLO | Write-leveling output delay | 0 to 20 ns |
| tWLS | DQS rising-edge setup to CK | 135-205 ps |
| tWLH | DQS rising-edge hold from CK | 135-205 ps |

## Temperature sensor (MR4)

The on-die temperature sensor is read through MR4. The lower three bits report a refresh-rate multiplier that ranges from 4x down to 0.25x and also indicate whether the die is below the low-temperature limit or above the high-temperature limit. Bit 7 is the Temperature Update Flag (TUF), which is set whenever the 3-bit value has changed since the last MR4 read; reading MR4 clears TUF. The device updates the sensor at least every tTSI = 32 ms, and the value is never older than tTSI after exiting self-refresh or power-down.

## What is not here

- No DDR3 MPR; LPDDR3 uses MRR and the DQ calibration registers instead.
- No standard boundary scan on the device.
- No OCD engine; ZQ calibration replaces it.
- No write CRC, no gear-down mode, and no per-pin loopback.
- Vendor test modes exist only as a reserved write-only register (MR9) with vendor-defined behavior.

**Source:** JESD209-3C sections 4.10, 4.10.1, 4.10.2, 4.11.2, 4.11.3, 4.11.4, 3.4.1
