# On-Die Termination

LPDDR4 provides two independent termination domains. The CA-bus domain
terminates the command/address signals and is controlled by a bond pad plus
mode registers. The DQ domain terminates the data bus and is switched on and
off by write commands. Both use a 240 ohm RZQ reference calibrated through the
ZQ pin.

## CA-bus ODT

CA ODT applies to CK_t, CK_c, CS, and CA[5:0]. It is enabled and its value is
selected by MR11 OP[6:4]; the default is off. MR22 provides override bits:
ODTE-CK (OP[3]) and ODTE-CS (OP[4]) can force termination on the clock or
chip-select even when the ODT_CA bond pad is low, while ODTD-CA (OP[5]) can
disable CA termination regardless of the pad.

| ODT_CA pad | MR11 OP[6:4] | ODTD-CA | CA term | CK term | CS term |
| --- | --- | --- | --- | --- | --- |
| Low | Valid (not 000B) | 0 | Off | Off unless ODTE-CK=1 | Off unless ODTE-CS=1 |
| High | Valid | 0 | On | On | On |
| Any | Disabled or RFU | 1 | Off | On unless separately disabled | On unless separately disabled |

A multi-rank system normally trains the terminating rank first, then the
non-terminating rank. Unlike DQ ODT, CA ODT stays active through power-down and
self-refresh. After writing a new CA ODT value, allow tODTUP before relying on
the new setting; the spec leaves this update time as TBD.

## DQ/DQS/DMI ODT

DQ ODT is selected by MR11 OP[2:0]; 000B disables it. Valid codes select
RZQ/1 through RZQ/6. The DRAM leaves termination at high-Z until a Write-1 or
Masked Write-1 command is sampled. It then turns on after a programmed ODTLon
latency and turns off after ODTLoff once the write burst ends.

| WL Set A | ODTLon (Set A) | ODTLoff (BL16, Set A) | Clock freq range |
| --- | --- | --- | --- |
| N/A | N/A | N/A | <= 266 / <= 533 MHz |
| 8 | 4 | 20 | 533-800 MHz |
| 12 | 4 | 22 | 800-1066 MHz |
| 14 | 6 | 24 | 1066-1333 MHz |
| 16 | 6 | 26 | 1333-1600 MHz |
| 18 | 8 | 28 | 1600-1866 MHz |
| 20 | 8 | 30 | 1866-2133 MHz |

Set B uses larger ODTLon/off values; add 8 tCK to ODTLoff for BL32. The analog
turn-on and turn-off windows are each 1.5 ns min to 3.5 ns max.

## ODT during special operations

| Situation | DQ/DQS/DMI ODT | CA ODT |
| --- | --- | --- |
| Reads | Off / high-Z | As programmed |
| Write / Masked Write | On around burst per ODTLon/off | As programmed |
| Power-down / self-refresh | Feature off | Stays on if enabled |
| CA bus training | Follows MR11/MR22/ODT_CA pad | Follows MR11/MR22/ODT_CA pad |
| Write leveling | DQS on if enabled, DQ off | As programmed |

During write leveling, DQS_t/DQS_c termination is on whenever DQ ODT is
enabled, but the DQ lines remain unterminated.

## ZQ calibration

The 240 ohm RZQ resistor calibrates both output driver strength and
termination. Calibration is started with an MPC ZQCal Start command and the
result is captured with an MPC ZQCal Latch command after tZQCAL (min 1 us).
During tZQLAT (max(30 ns, 8 tCK)) the CA bus must be deselected so the new CA
ODT value can settle. If the long calibration flow is not used, writing
MR10 OP[0]=1 performs a ZQCal Reset that restores roughly +/- 30% accuracy.

## What LPDDR4 does not have

- No dedicated ODT control pin for the DQ bus; termination turns on and off
  automatically around write commands.
- No VTT termination rail.
- No write CRC.
- No on-die ECC.

**Source:** JESD209-4E sections 3.4.1 (MR10, MR11, MR22), 4.38, 4.40, 4.41,
4.42, Table 159, Table 167, Table 168
