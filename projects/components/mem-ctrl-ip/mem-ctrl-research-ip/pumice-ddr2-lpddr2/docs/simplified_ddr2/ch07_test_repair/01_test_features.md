# Test and Calibration Features

DDR2 has almost no test logic compared to later generations. What it has
is OCD calibration, a test-mode bit you must never set, and no boundary
scan at all.

## OCD - Off-Chip Driver impedance adjustment

The output driver strength is trimmable so the DQ/DQS drive impedance can
be matched to the channel instead of relying on process-lot luck. Control
lives in EMR1 A9-A7:

| A9 A8 A7 | Operation |
| --- | --- |
| 0 0 0 | Exit OCD calibration mode; keep current setting |
| 0 0 1 | Drive(1): DQ/DQS driven high, DQS# low (measure pull-up) |
| 0 1 0 | Drive(0): DQ/DQS driven low, DQS# high (measure pull-down) |
| 1 0 0 | Adjust mode: shift the driver code (BL4 op-code on all DQs: increment, decrement, or hold) |
| 1 1 1 | OCD calibration default (nominal 18 ohm full-strength drive) |

Flow:

```
for pull-up and pull-down sides:
    EMRS Drive(1) or Drive(0)      # drive a static level
    measure at the controller/PHY
    EMRS OCD exit                  # mandatory after every calibration command
    if adjustment needed:
        EMRS Adjust mode           # then a BL4 write of the adjust op-code
        EMRS OCD exit
EMRS OCD default (if not calibrating) then EMRS OCD exit
```

Rules:

- Every OCD calibration command must be followed by an OCD-exit EMRS
  before any other command.
- All mode registers must be programmed before OCD calibration, and ODT
  must be managed so it does not corrupt the measurement.
- OCD applies only to the full-strength drive setting; with reduced
  strength (EMR1 A1) the OCD characteristics do not apply, and the
  default values are likewise not applicable when Adjust mode is used.
- If OCD is not used at all, the init sequence still requires the
  default-then-exit pair (see Chapter 2).
- tOIT (0-12 ns) covers the output delay after entering a drive mode.

## Test mode (MR A7)

MR A7 selects a vendor test mode. The spec's only directive for users is:
keep it 0. There is no standardized user-visible test mode.

## What is not here

- No boundary scan / JTAG on the DRAM itself (that lives on registers and
  buffers in module form factors, not in the JESD79-2 device spec).
- No connectivity test mode, no per-pin loopback, no MPR (multi-purpose
  register) reads - those arrive with DDR3.
- No post-package repair interface exposed to the user.
- The DLL is observable only indirectly, through read-data timing
  (tAC/tDQSCK); there is no lock-status readback.

**Source:** JESD79-2F sections 3.4.1, 3.4.3
