<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# RTC PeakRDL Register Specification

This directory contains the SystemRDL specification for the Real-Time Clock (RTC) configuration registers.

## Files

- `rtc_regs.rdl` - SystemRDL register specification, and the single source of
  truth for the RTC register map. The field detail is NOT restated here: a
  second copy is what rots.

## Generated files

Generation writes three artefacts that must move together:

- `../rtc_regs.sv/rtc_regs.sv` - the register block
- `../rtc_regs.sv/rtc_regs_pkg.sv` - the hwif package
- `../rtc_regmap.py` - the by-name register map used by DV

Note the parent directory is literally named `rtc_regs.sv`; the filelist
`../filelists/apb4_rtc.f` reads from it, so that is where the output has to
land.

## Generation command

Use the shared wrapper, never `peakrdl regblock` directly - the wrapper emits
RTL, docs and the regmap in lockstep, and a raw invocation desynchronizes the
regmap:

```bash
python3 bin/peakrdl_generate.py \
    projects/components/retro_legacy_blocks/rtl/rtc/peakrdl/rtc_regs.rdl \
    -o <scratch-dir> --no-html --no-markdown \
    --regmap-output <scratch-dir>/rtc_regmap.py
```

Then copy `<scratch-dir>/rtl/rtc_regs.sv`, `<scratch-dir>/rtl/rtc_regs_pkg.sv`
and `<scratch-dir>/rtc_regmap.py` into the paths listed above and delete the
scratch directory. Do not leave a second copy of generated output anywhere.

## What the RDL carries beyond plain fields

- The six time registers are `hw=rw` **with `we`**. The counter-domain shadow
  only writes them when `rtc_config_regs` allows it, which is what gives the
  time-set protocol somewhere to stage six writes (GitHub #56 H7).
- `RTC_STATUS.alarm_flag` / `second_tick` / `commit_timeout` carry
  `precedence = sw`, so a W1C write wins over the hardware mirror in its own
  cycle. They do **not** carry `swmod`: the wrapper hand-decodes the W1C
  strobe it forwards to `rtc_core`, nothing ever consumed `swmod`, and the
  guard against a regenerated decode drifting away from that hand-decode is
  the DV suite's W1C tests, not a port.
- `RTC_HOURS` bit 7 is the PM flag in 12-hour mode for BOTH binary and BCD
  counting.

## Integration

```
Layer 1: apb4_rtc.sv         APB4 interface, both clocks and both resets
         v
Layer 2: rtc_config_regs.sv  decode + PSLVERR, time-set staging, read window
         v
Layer 3: rtc_core.sv         counters, calendar, alarm, clock crossings
```

The generated files are instantiated in `rtc_config_regs.sv`. Behaviour is
described once, in `../README.md`.
