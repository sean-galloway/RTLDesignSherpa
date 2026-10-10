# Parameter Families and Ratio Phasing

## Parameter families

DFI 2.1 timing parameters are named `dfi_t*` in public shorthand, but the
specification itself uses names like `tctrl_delay`, `tphy_wrlat`, and
`trddata_en`. Each parameter is defined by the MC, the PHY, or the system as a
whole, and must remain constant while traffic is in flight. They may be changed
only when the DFI bus is idle.

### Who defines what

| Family | Examples | Defined by | Observable by |
| --- | --- | --- | --- |
| Control | tctrl_delay | PHY | MC sees command-to-DRAM delay |
| Write data | tphy_wrlat, tphy_wrdata, tphy_wrdelay | PHY | MC schedules enable and data |
| Read data | trddata_en, tphy_rdlat | System / PHY | MC schedules enable, PHY bounds valid |
| Update | tctrlupd_*, tphyupd_* | MC / PHY | Both sides handshake idle windows |
| Status | tdram_clk_disable, tdram_clk_enable, tinit_complete, tinit_start, tphy_paritylat | PHY / MC | Both sides |
| Training | trdlvl_*, twrlvl_* | PHY / MC | Both sides during leveling |
| Low power | tlp_resp, tlp_wakeup | MC | PHY responds within bounds |
: Timing parameter families and ownership

### What the families constrain

Control timing only has `tctrl_delay`: the uniform delay through the PHY to the
DRAM pins. Write data timing constrains the gap from command to enable and from
enable to data. Read data timing constrains the gap from command to enable and
from enable to the latest valid data. Update timing bounds how long each side
may keep the bus idle. Status timing bounds clock disable, init handshake, and
parity latency. Training timing bounds command-to-response and delay-load
delays. Low power timing bounds how quickly the PHY must acknowledge and exit.

### Constants, maxima, and fixed values

A parameter may be a fixed constant, a maximum value, or a value derived from
other system settings. For example, `tphy_wrlat` is usually a fixed PHY
property, while `tphy_rdlat` is often a system-level maximum. The DFI does not
mandate absolute numeric ranges; compatibility depends on the MC and PHY
supporting overlapping ranges.

## Ratio and phasing

DFI 2.1 supports matched frequency (1:1) and frequency ratio (1:2 and 1:4)
systems. The ratio changes how command, write, and read information is packed
into a single DFI clock.

### 1:1 matched frequency

In a 1:1 system the MC clock and the PHY clock are the same. There is one set
of control signals, one write data bus, one read data bus, and one read data
enable. All timing parameters are expressed in DFI clock cycles, which are also
PHY clock cycles.

### 1:2 frequency ratio

In a 1:2 system the PHY clock runs at twice the DFI clock. Each DFI clock
contains two PHY phases. The MC can therefore place commands on both phases:

- Control signals become `dfi_*_p0` and `dfi_*_p1`.
- Write data and mask become `dfi_wrdata_p0` / `_p1` and
  `dfi_wrdata_mask_p0` / `_p1`.
- Write data enable becomes `dfi_wrdata_en_p0` / `_p1`.
- Read data enable becomes `dfi_rddata_en_p0` / `_p1`.
- Read data, valid, and DNV become `dfi_rddata_w0` / `_w1`,
  `dfi_rddata_valid_w0` / `_w1`, and `dfi_rddata_dnv_w0` / `_w1`.

The MC may issue a command on any phase. The PHY must accept commands on all
phases.

### 1:4 frequency ratio

In a 1:4 system there are four PHY phases per DFI clock. The same suffixing
applies with `_p0` through `_p3` and `_w0` through `_w3`. This allows the MC to
issue up to four commands per DFI clock and to receive up to four read data
words per DFI clock.

### Impact on scheduling

A higher ratio lets the MC run slower than the DRAM pins while still supplying
full pin bandwidth. The trade-off is scheduling complexity: the controller must
place each command on the correct phase, align write data to `tphy_wrlat` and
`tphy_wrdata` in PHY-clock terms, and align the read data enable to
`trddata_en` in PHY-clock terms. The `tphy_wrdelay` parameter exists so the MC
can keep write data aligned to phase 0 in its own view while the PHY shifts it
to the correct phase internally.

### Ratio selection

The ratio is static for normal operation. It is communicated at initialization
via `dfi_freq_ratio` and confirmed by the `dfi_init_start` handshake. A later
frequency change can select a new ratio, but that requires the optional
frequency change protocol.

**Source:** DFI Specification v2.1.1 sections 2.0, 3.1, 3.2, 3.3, 4.7, 5.0
