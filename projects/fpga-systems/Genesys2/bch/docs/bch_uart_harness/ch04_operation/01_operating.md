# Operating It

Start with `make help` in `projects/fpga-systems/Genesys2/bch/` and the
per-build help under `build-loop/`. A typical board run looks like:

```bash
bin/run_smoke.py --board genesys2 --port /dev/ttyUSB0 --sequences init smoke sweep
```

Board timing, utilisation, and the matrix summary are recorded in
`stable/MANIFEST.md` and `stable/reports/{genesys2_axis,genesys2_axi4}/`.
Campaign transcripts turn into reports with
`projects/fpga-systems/bin/report_battery.py` (JSON artifacts,
correction-boundary / decode-cost / soak-timeline figures, and a generated
`FINDINGS.md`); published runs live under `stable/results/`. The run evidence
— the 2026-10-05 battery and the one-million-block soak — is rolled up in the
companion *Binary BCH Board Validation Report* (`docs/Binary_BCH_Board_Validation_v0.1.pdf`).
For the Galois-field math behind the profile, see the component HAS chapter 7
under `projects/components/ecc-ip/bch/docs/`. The sister harness has the
matching guide at `../../reed-solomon/docs/Reed_Solomon_UART_Harness_v0.1.pdf`.
