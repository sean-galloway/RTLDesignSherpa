# CRC Calculator

A standalone drill app that teaches how a parameterized CRC engine works
and why the same polynomial can produce very different intermediate
states depending on the bit-order convention.

Open `index.html` directly in a browser (`file://` is supported).  There
is no build step, no CDN, and no external dependency.

## File layout

```
bin/apps/crc_calc/
├── index.html
├── style.css
├── js/
│   ├── model.js   # pure CRC engine, node-testable
│   └── app.js     # DOM glue
├── test/
│   └── run_tests.js
└── README.md
```

## Model

The app implements the standard generalized CRC algorithm with the same
five semantic parameters as `rtl/common/dataint_crc.sv`:

- `CRC_POLY` / `POLY` — non-reflected polynomial
- `CRC_INIT` / `POLY_INIT` — seed loaded into the shift register
- `CRC_REFIN` / `REFIN` — reflect each input byte before shifting
- `CRC_REFOUT` / `REFOUT` — reflect the final register before `XOROUT`
- `CRC_XOROUT` / `XOROUT` — final XOR mask
- `width` / `CRC_WIDTH` — polynomial width (8, 16, or 32)

For each byte the engine XORs it into the top of the register, shifts
left eight times, and applies the polynomial taps whenever the bit that
shifts out is a 1.  When `CRC_REFIN` is set the byte is bit-reversed
first, matching a hardware LSB-first serial CRC.  When `CRC_REFOUT` is
set the final register is bit-reversed before the XOR-out stage.

Presets are provided for CRC-8, CRC-16/CCITT-FALSE, CRC-16/ARC, and
CRC-32, each verified against the standard "123456789" check string.  A
"Custom" mode lets you edit any parameter and watch the shift-register
steps in real time.

## Tests

```
node bin/apps/crc_calc/test/run_tests.js
```

The runner is a zero-dependency TAP-ish script that exits 0 on pass.
