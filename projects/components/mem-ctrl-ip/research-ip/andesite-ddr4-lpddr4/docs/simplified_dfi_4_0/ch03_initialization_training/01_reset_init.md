# Reset and Initialization

DFI initialization is a handshake between MC and PHY mediated by `dfi_init_start` and
`dfi_init_complete`. The same two signals are reused for frequency change during normal
operation.

## Power-up and the init handshake

At power-up the PHY may optionally wait for `dfi_init_start` before asserting `dfi_init_complete`.
The MC drives `dfi_freq_ratio` and `dfi_frequency` to their initial values and then asserts
`dfi_init_start`. This tells the PHY that the frequency ratio and frequency indicator are valid.

Initialization completes when both `dfi_init_start` and `dfi_init_complete` are asserted
simultaneously for at least one DFI clock. After that point the PHY accepts normal DFI transactions
and all command/status signals may leave their defaults.

| Phase | MC behavior | PHY behavior |
| --- | --- | --- |
| Power-up | Drive `dfi_freq_ratio` and `dfi_frequency` to initial values. | May wait for `dfi_init_start`. |
| Init request | Assert `dfi_init_start`. | Accept ratio/frequency; prepare DRAM interface. |
| Init complete | May hold or de-assert `dfi_init_start` after both signals are high. | Assert `dfi_init_complete`. |
| Normal operation | Issue commands, data, refresh. | Respond to DFI transactions. |

: Initialization handshake phases

## Frequency change

During normal operation the MC requests a frequency change by asserting `dfi_init_start` again.
The PHY accepts by de-asserting `dfi_init_complete` within `tinit_start` cycles. If the PHY does not
de-assert `dfi_init_complete` within `tinit_start`, the MC must abort the request and release
`dfi_init_start`.

While `dfi_init_start` is asserted for a frequency change, `dfi_frequency` must be set to the new
legal value and remain unchanged. Once `dfi_init_complete` de-asserts, the MC holds
`dfi_init_start` until the frequency change is complete. The PHY re-asserts `dfi_init_complete`
within `tinit_complete` cycles after `dfi_init_start` de-asserts.

## Clock disabling during init

When `dfi_init_start` is asserted during initialization, `dfi_dram_clk_disable` must reflect the
clocks that are being used. In normal operation this signal can change dynamically to gate the
DRAM clocks for power savings.

## Init timing parameters

| Parameter | Description |
| --- | --- |
| `tinit_start` | Max DFI clocks from `dfi_init_start` assertion until PHY must de-assert `dfi_init_complete` to accept frequency change. |
| `tinit_start_min` | Min DFI clocks before `dfi_init_start` can be driven after a previous command or training event. |
| `tinit_complete` | Max DFI clocks from `dfi_init_start` de-assertion to `dfi_init_complete` re-assertion during frequency change. |
| `tinit_complete_min` | Min DFI clocks before `dfi_init_complete` can be driven after a previous command or training event. |

: Initialization timing parameters

## Update before self-refresh exit

DFI 4.0 requires a `dfi_ctrlupd_req`/`dfi_ctrlupd_ack` handshake immediately before a self-
refresh exit command. This update window guarantees that the PHY has a clean point to apply any
pending delay updates before the command stream resumes at full speed.

**Source:** DFI Specification v4.0 sections 3.5.1, 3.5.5, 4.1, 4.10
