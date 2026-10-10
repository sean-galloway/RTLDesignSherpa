# Low Power Control Interface

The low power control interface lets the MC inform the PHY of an
opportunity to enter a low-power state. DFI 3.1 splits the single v2.1
`dfi_lp_req` into two requests: one for the control path and one for the
data path. This lets the MC and PHY sleep the paths independently.

## Low power signals

| Signal | From | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| `dfi_lp_ctrl_req` | MC | 1 bit | 0x0 | MC indicates no more commands will be sent on the control interface. |
| `dfi_lp_data_req` | MC | 1 bit | 0x0 | MC indicates no more commands will be sent on the data interface. |
| `dfi_lp_ack` | PHY | 1 bit | 0x0 | Optional PHY acknowledge. |
| `dfi_lp_wakeup` | MC | 4 bits | none | Encoded wakeup time. Valid only while a request is asserted. |

: Low power control interface signals

Only one low-power request may be outstanding until it is acknowledged or
aborted. When exiting, if both requests are asserted they must de-assert
simultaneously.

## `dfi_lp_wakeup` encoding

| `dfi_lp_wakeup` | Wakeup time (DFI clock cycles) |
| --- | --- |
| 0000 | 16 |
| 0001 | 32 |
| 0010 | 64 |
| 0011 | 128 |
| 0100 | 256 |
| 0101 | 512 |
| 0110 | 1024 |
| 0111 | 2048 |
| 1000 | 4096 |
| 1001 | 8192 |
| 1010 | 16384 |
| 1011 | 32768 |
| 1100 | 65536 |
| 1101 | 131072 |
| 1110 | 262144 |
| 1111 | unlimited |

: Low power wakeup encoding

The MC must hold `dfi_lp_wakeup` constant until `dfi_lp_ack` asserts. After
acknowledge it may increase the value but never decrease it. The value at
the moment the request de-asserts defines the `tlp_wakeup` time.

## Low power handshake

1. The MC asserts `dfi_lp_ctrl_req` or `dfi_lp_data_req` with a static
   `dfi_lp_wakeup` value.
2. The PHY may assert `dfi_lp_ack` within `tlp_resp` cycles.
3. While request and acknowledge are both asserted, the PHY may remain in a
   low-power state.
4. When the request de-asserts, the PHY must return to normal operation and
   de-assert `dfi_lp_ack` within `tlp_wakeup` cycles.

If the PHY does not acknowledge within `tlp_resp` cycles, the MC may de-
assert the request and treat the opportunity as declined.

## Low power timing parameters

| Parameter | Defined by | Meaning |
| --- | --- | --- |
| `tlp_resp` | MC | Max cycles from request assertion to `dfi_lp_ack` assertion. |
| `tlp_wakeup` | MC | Max cycles from request de-assertion to `dfi_lp_ack` de-assertion. |

: Low power control interface timing parameters

In the scoria DDR3/LPDDR3 controller this interface is exposed for spec
compliance but is not consumed by the target PHY family.

**Source:** DFI Specification v3.1 sections 3.7, 4.12, Table 19, Table 20
