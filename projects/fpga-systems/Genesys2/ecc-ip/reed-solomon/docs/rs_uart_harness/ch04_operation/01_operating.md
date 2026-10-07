# Operating It

To run on the Genesys 2:

```bash
cd projects/fpga-systems/Genesys2/ecc-ip/reed-solomon
bin/run_smoke.py --board genesys2 --port /dev/ttyUSB0 --sequences init smoke sweep
```

For the Nexys A7 small profile, build the bitstream with
`make -C build-loop bitstream RS_TARGET=nexys_a7_100t RS_PROFILE=small`
and drive the same sequences over the A7's UART; `init` proves the "RSLS"
BUILD_ID and the PROFILE CSR reports n=64, t=4, so the host programs pick up
the geometry from the board.

See `README.md` and `Makefile` for the full target list (bitstream, lint,
sim, regmap) and `build-loop/host/host_rs_loop.py` for the lower-level CLI.
Build evidence and the board-validation record live in `stable/MANIFEST.md`
and the four `stable/reports/genesys2_*` directories. Campaign transcripts
turn into reports with `projects/fpga-systems/bin/report_battery.py` (JSON
artifacts, correction-boundary / decode-cost / soak-timeline figures, and a
generated `FINDINGS.md`); published runs live under `stable/results/`. The
run evidence — the 2026-10-05 four-image battery and the one-million-block
soak — is rolled up in the companion *Reed-Solomon Board Validation Report*
(`docs/Reed_Solomon_Board_Validation_v0.1.pdf`). The math behind the codec is
in the component HAS chapter 7 at
`projects/components/ecc-ip/reed-solomon/docs/reed_solomon_has/ch07_understanding_the_math/`.
The sister BCH harness has the matching guide at
`../../bch/docs/Binary_BCH_UART_Harness_v0.1.pdf`.
