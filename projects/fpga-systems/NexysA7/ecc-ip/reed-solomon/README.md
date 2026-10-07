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

# Reed-Solomon on the Nexys A7

The Reed-Solomon codec (`projects/components/ecc-ip/reed-solomon`) on the
A7-100T, in the same UART loop harness as the Genesys 2 — generator,
encoder, error injector, dual solvers (riBM + Euclidean) checked against
each other, pattern checkers — scaled down to fit the Artix-7.

**This directory is an entry point, not a second harness.** The harness
lives in one place, [`projects/fpga-systems/Genesys2/ecc-ip/reed-solomon/`
](../../../Genesys2/ecc-ip/reed-solomon/), and builds both boards' images from the
same RTL, DV, host programs, and campaign sequences. Targets here forward
there with the small profile preset.

## The small profile (BUILD_ID "RSLS")

| | full (Genesys 2) | small (this board) |
|---|---|---|
| code | RS(252,236) t=8, GF(2^8) | RS(64,56) t=4, shortened from 255 over GF(2^8) |
| clock | 100 MHz | 50 MHz (fabric divide-by-2; the -1 speed grade misses 100 MHz) |
| BUILD_ID | RSLP | RSLS |
| post-route | WNS positive | WNS +5.137 ns, ~26% LUT |

`init` reads the geometry back from the PROFILE CSR, so the identical
campaign sequences drive both boards; the host never trusts the build tree
over the board.

## Quickstart

```bash
make bitstream        # -> Genesys2/ecc-ip/reed-solomon/build-loop/fpga/bitstream/rs_loop_small.bit
make program          # JTAG onto the A7 (board_lock.sh serial-keyed lock)
make run SEQUENCES="init smoke sweep"
```

Board gotcha (from the registry): Digilent Adept steals the UART ttyUSB —
**do not power-cycle after programming** or the port binding is lost.

## Evidence and docs

- Scale-down tracking: issue #83; A7 board campaign: issue #85.
- Campaign results (functional battery + soak): `stable/results/` in the
  harness tree, rendered by `projects/fpga-systems/bin/report_battery.py`.
- Harness guide: [`../../../Genesys2/ecc-ip/reed-solomon/docs/UART_HARNESS.md`](../../../Genesys2/ecc-ip/reed-solomon/docs/UART_HARNESS.md)
  (PDF: `docs/Reed_Solomon_UART_Harness_v0.1.pdf`), board validation report
  in the same `docs/` directory.
- Component docs (the math): `projects/components/ecc-ip/reed-solomon/docs/`.
