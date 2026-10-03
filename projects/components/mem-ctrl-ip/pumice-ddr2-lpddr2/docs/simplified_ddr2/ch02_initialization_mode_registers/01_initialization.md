# Power-Up and Initialization

DDR2 must be initialized by a fixed sequence; anything else is undefined
behavior. The sequence below paraphrases the required steps.

## Cold start sequence

1. Ramp supplies with CKE held below 0.2 x VDDQ and the ODT pin LOW.
   VDD/VDDL and VDDQ ramp together (or VDD first), VTT last; each ramp
   must complete within spec windows (200 ms VDD, 500 ms VDDQ-then-VTT).
   VREF tracks VDDQ/2 and must never exceed VDDQ.
2. Start the clock (CK/CK#) and keep it stable.
3. Wait at least 200 us with stable power and clock, issuing NOP or
   Deselect, then raise CKE.
4. Wait at least 400 ns more (NOP/Deselect), then issue Precharge-All.
5. EMRS to EMR(2) - BA1=1, BA0=0 selects it.
6. EMRS to EMR(3) - BA1=1, BA0=1.
7. EMRS to EMR(1) with A0=0: enable the DLL.
8. MRS with A8=1: DLL reset (this also programs the other MR fields).
9. Precharge-All.
10. Two or more Refresh commands.
11. MRS with A8=0: program operating parameters without resetting the DLL.
12. At least 200 clocks after step 8, run OCD calibration. If OCD is not
    used, instead write EMR(1) twice: once with the OCD-default code
    (A9=A8=A7=1), once with the OCD-exit code (A9=A8=A7=0), carrying the
    desired EMR(1) operating fields.
13. Ready for normal operation.

The required gaps between these commands (tRP, tMRD, tRFC) look like this:

```
... CKE high ... 400 ns ... PREA ... EMRS(2) ... EMRS(3) ... EMRS(1) ...
     MRS(DLL reset) ... PREA ... REF ... REF ... MRS(operating) ...
     >= 200 clk ... OCD flow ... ready
        |tRP|tMRD|tMRD|tMRD|   |tRP|tRFC|tRFC|tMRD|
```

## Notes that bite

- All four mode registers must be written; the spec allows them in any
  order but the canonical sequence above programs EMR2/EMR3 first because
  their fields are inert defaults.
- The register contents are undefined at power-up - there is no hardware
  default. Skip a register and its fields are garbage.
- MRS/EMRS require all banks precharged and idle, CKE high, and tMRD (2
  clocks) before the next command.
- Reprogramming MR/EMR later is legal any time all banks are idle, and
  does not disturb array contents - but any field not rewritten takes its
  newly written value, so every field must always be written, even
  unchanged ones.
- The DLL needs 200 clocks after enable+reset before a Read may be issued,
  or tAC/tDQSCK are not guaranteed. This same 200-clock rule reappears at
  self-refresh exit (tXSRD).
- DLL is automatically disabled in self-refresh and re-enabled on exit.

## Why the order matters

DLL enable (step 7) must precede DLL reset (step 8); the reset pulse is
only meaningful on an enabled DLL. The precharge-all before refresh
guarantees a clean idle state; the two refreshes seed the internal refresh
counter so the first tREFI window is well-defined. OCD calibration must
follow all mode-register programming because its results depend on the
configured drive strength and ODT settings.

**Source:** JESD79-2F sections 3.3, 3.3.1
