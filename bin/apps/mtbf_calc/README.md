# Metastability MTBF Calculator

A standalone drill app that teaches why a two-flop synchronizer is not
always enough at high clock frequencies.

Open `index.html` directly in a browser (`file://` is supported).  There
is no build step, no CDN, and no external dependency.

## File layout

```
bin/apps/mtbf_calc/
├── index.html
├── style.css
├── js/
│   ├── model.js   # pure calculation logic, node-testable
│   └── app.js     # DOM glue
├── test/
│   └── run_tests.js
└── README.md
```

## Model

The app implements the classic synchronizer MTBF formula:

```
MTBF = exp(C2 * tMET_total) / (C1 * f_clk * f_data)
```

with

```
tMET_total = t0 + (N - 1) * r
r          = (1 / f_clk) - tCO - tSU
```

- `C1` is in seconds.
- `C2` is in s^-1 so that `C2 * tMET_total` is dimensionless.
- `t0` is the input aperture / metastability window of the first flop.
- `r` is the per-stage resolution time available after clock-to-output
  and setup overhead.
- `N` is the number of synchronizer stages.

This convention follows the teaching in Clifford E. Cummings' SNUG
synchronizer papers (e.g. "Synthesis and Scripting Techniques for
Designing Multi-Asynchronous Clock Designs", SNUG 2001).  The presets
are illustrative literature ballparks, not foundry data.

## Tests

```
node bin/apps/mtbf_calc/test/run_tests.js
```

The runner is a zero-dependency TAP-ish script that exits 0 on pass.
