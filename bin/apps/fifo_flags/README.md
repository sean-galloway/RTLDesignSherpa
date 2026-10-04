# FIFO Flags Calculator

A standalone drill app that teaches how to set almost-full and almost-empty
thresholds in an asynchronous FIFO, and why the thresholds depend on clock
ratio and synchronizer depth.

Open `index.html` directly in a browser (`file://` is supported). There is no
build step, no CDN, and no external dependency.

## File layout

```
bin/apps/fifo_flags/
├── index.html
├── style.css
├── js/
│   ├── model.js   # pure threshold logic, node-testable
│   └── app.js     # DOM glue
├── test/
│   └── run_tests.js
└── README.md
```

## Model

The app computes conservative worst-case margins for an async FIFO with
N-stage pointer synchronizers:

```
margin_AF = ceil(f_wr / f_rd) * (N + 1)
margin_AE = ceil(f_rd / f_wr) * (N + 1)
```

- `margin_AF` is the occupancy uncertainty seen from the write (producer)
  side: at most `(N + 1)` read clocks, converted to write-side items.
- `margin_AE` is the occupancy uncertainty seen from the read (consumer)
  side: at most `(N + 1)` write clocks, converted to read-side items.

The user also supplies a bubble tolerance `B%` of the FIFO depth:

```
bubble_items = round(depth * B / 100)
AF_threshold = depth - margin_AF - bubble_items
AE_threshold = margin_AE + bubble_items
```

The result is a PASS when `AF_threshold > AE_threshold`; otherwise the depth
is too small for the chosen margins and bubble.

## Model API

- `FIFOFLAGS.validate(p)` -- validate inputs and return `{ok, errors}`.
- `FIFOFLAGS.compute(p)` -- compute thresholds and return `{marginAF,
  marginAE, bubbleItems, afThreshold, aeThreshold, pass, message, ...}`.
- `FIFOFLAGS.EXAMPLES` -- array of three click-to-load example cases.

## Tests

```
node bin/apps/fifo_flags/test/run_tests.js
```

The runner is a zero-dependency TAP-ish script that exits 0 on pass.
