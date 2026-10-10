# Package and Electrical Notes

Light notes on the physical side; the spec's package section is
primarily ballout drawings, which are not reproduced here.

## Supplies

| Rail | Typ | Feeds |
| --- | --- | --- |
| VDD1 | 1.8 V | Core (low-current domain) |
| VDD2 | 1.2 V (S4B; 1.35 V S4A; absent on S2A) | Core (main current) |
| VDDCA | 1.2 V | CA/CKE/CS_n/CK input receivers |
| VDDQ | 1.2 V | DQ/DQS/DM IO buffers |
| VREFCA / VREFDQ | rail / 2 | Input reference for CA and DQ receivers |
| ZQ | - | External 240 ohm +/-1% calibration reference |

Ramp-order rules (Chapter 2) keep VDD1 within 200 mV above VDD2, and
both within 200 mV above VDDCA/VDDQ, at all times. VDDQ may be switched
off in power-down and self-refresh (VREFDQ must follow it), which is a
real system-level power lever.

## Interface: HSUL_12

LPDDR2's IO is high-speed unterminated logic at 1.2 V: point-to-point
or short multi-drop, no termination resistors, no ODT. Drive strength
is programmed in MR3 (34-120 ohm typical options, default 40 ohm) and
held over voltage/temperature by ZQ calibration (tZQINIT at boot,
tZQCL/tZQCS maintenance commands thereafter). Clock and strobes are
differential (CK_t/CK_c, DQS_t/DQS_c); everything else is single-ended.

## Packages

The spec defines BGA ballouts for both PoP (package-on-package, stacked
under the SoC) and discrete/MCP use, including:

- 168-ball 12x12 mm PoP, 2-channel 2x32 (two independent x32 channels
  plus shared power in one package)
- 134-ball and 162/180-ball x16/x32 discrete/MCP options
- 79-ball x16 small-pitch discrete
- MCP ballouts pairing LPDDR2 with SDR NAND or e-MMC on one package

Multi-channel packages give each channel its own CA bus, CK, CKE and
CS_n - they are independent memories sharing a package and nothing
else.

## Power-state current hierarchy (why the states exist)

Roughly, from most to least expensive: active operation > active
power-down > idle power-down > self-refresh (with PASR reducing it
further) > deep power-down (contents lost) > powered off. The CKE table
in Chapter 3 is the map between them.

**Source:** JESD209-2F sections 2 (package ballouts), 6-7 (Tables
69-73), 9, 11
