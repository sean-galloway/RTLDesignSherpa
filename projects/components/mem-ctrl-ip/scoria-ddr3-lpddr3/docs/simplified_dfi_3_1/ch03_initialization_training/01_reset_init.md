# Reset and Initialization

DFI 3.1 does not dictate a power-up sequence for either the MC or the PHY,
but it does define the handshake that marks the boundary between
initialization and normal operation.

## Default values before `dfi_init_complete`

Until `dfi_init_complete` asserts, every command and status signal must be
held at its default value. The defaults come from the interface tables:

- High-active signals default to `0` (for example `dfi_odt`,
  `dfi_wrdata_en`).
- Low-active signals default to `1` (for example `dfi_cs_n`, `dfi_we_n`).
- Buses have no specified default.
- State-specific signals such as `dfi_dram_clk_disable` and
  `dfi_parity_in` take their system-defined values.

For LPDDR3 and LPDDR2 systems, `dfi_address` must drive a NOP command
until `dfi_init_complete` asserts.

## The `dfi_init_start` / `dfi_init_complete` handshake

`dfi_init_start` has two functions:

1. At initialization it tells the PHY that `dfi_data_byte_disable` and
   `dfi_freq_ratio` are valid. The PHY may wait for this assertion before
   asserting `dfi_init_complete` if it needs those values.
2. During normal operation it requests a frequency change.

Initialization completes when both `dfi_init_start` and `dfi_init_complete`
are asserted for at least one DFI clock cycle. After that, the MC may hold
or de-assert `dfi_init_start`.

| Phase | `dfi_init_start` | `dfi_init_complete` | Meaning |
| --- | --- | --- | --- |
| Power-up | driven by MC | `0` | PHY not ready. |
| Config valid | `1` | `0` | MC has defined ratio and byte disable. |
| Complete | `1` | `1` for >=1 cycle | PHY ready; normal operation may begin. |

: Initialization handshake states

## Frequency-change reuse of the init signals

During normal operation the MC may assert `dfi_init_start` again to request
a frequency change. The PHY must de-assert `dfi_init_complete` within
`tinit_start` cycles to acknowledge the request. If it does not, the MC
must abort and release `dfi_init_start`.

Once acknowledged, the MC holds `dfi_init_start` asserted while the clock
frequency changes. When the change is done, the MC de-asserts
`dfi_init_start`; the PHY then re-initializes and re-asserts
`dfi_init_complete` within `tinit_complete` cycles.

The DFI bus must be kept at valid and stable levels throughout the
frequency change. Both sides reset their DFI read data word pointers to
zero when `dfi_init_start` asserts.

## Initialization timing parameters

| Parameter | Defined by | Meaning |
| --- | --- | --- |
| `tinit_start` | MC | Max cycles for the PHY to acknowledge a frequency-change request. |
| `tinit_complete` | PHY | Max cycles for the PHY to re-assert `dfi_init_complete` after `dfi_init_start` de-asserts. |

: Initialization timing parameters

**Source:** DFI Specification v3.1 sections 3.5.1, 4.1, 4.9, Figure 3, Figure 4, Figure 5
