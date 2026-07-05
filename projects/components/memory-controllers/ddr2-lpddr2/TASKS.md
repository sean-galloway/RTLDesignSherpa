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

# ddr2-lpddr2 — Open Tasks

## TASK-GEAR: Generic AXI ↔ DRAM-beat width gearing

Decouple `AXI_DATA_WIDTH` from `DRAM_BEAT_WIDTH` (today `axi_intake.sv` hard-assumes
they're equal). Make AXI width a free parameter (32/64/128/256/512) via an internal
gearbox localized to `axi_intake` — everything below the AXI↔beat seam is already
beat-parameterized. Primarily for **future DDR\* IP** (each device/PHY pins its own
beat/rate; hosts want a fixed AXI width); the Nexys A7 a7ddrphy x16 bring-up
(beat=32, rate=4) is the first consumer.

**Full design + effort + risks + resource note:** `docs/AXI_DRAM_GEARING_SCOPE.md`
