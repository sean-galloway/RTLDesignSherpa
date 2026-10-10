# Refresh Interaction and Frequency Change

## Refresh interaction

DFI does not define refresh commands specially. A refresh is just another command on the control
interface: `dfi_ras_n` and `dfi_cas_n` low, `dfi_we_n` high, with `dfi_address` and `dfi_bank` set
according to the memory type. The MC is responsible for scheduling refresh at the required rate
and for precharging all banks before issuing an all-bank refresh.

The PHY may request control of the bus for its own refresh-related purposes through the PHY
master interface. While the PHY is master, the MC may still forward refresh commands, which the
PHY relays to the DRAM within `tphymstr_rfsh` cycles.

### Refresh during training

DFI 4.0 allows refreshes to be issued during some training sequences, provided the DRAM timing
requirements are met. The MC must not issue normal read or write traffic to slices that are actively
being trained.

## Frequency change

DFI 4.0 reuses the init handshake (`dfi_init_start`/`dfi_init_complete`) for frequency change. The
MC also uses `dfi_frequency` to tell the PHY the target frequency encoding.

### Acknowledged frequency change

1. MC drives new `dfi_frequency` and asserts `dfi_init_start`.
2. PHY accepts by de-asserting `dfi_init_complete` within `tinit_start` cycles.
3. MC holds `dfi_init_start` until the frequency switch is complete.
4. PHY re-asserts `dfi_init_complete` within `tinit_complete` cycles after `dfi_init_start` de-asserts.

### Not-acknowledged frequency change

If the PHY does not de-assert `dfi_init_complete` within `tinit_start` cycles, the MC must abort the
request and release `dfi_init_start`. The PHY must not de-assert `dfi_init_complete` after
`tinit_start` expires.

### Frequency indicator

`dfi_frequency` is a 5-bit value supporting up to 32 encodings. The mapping from encoding to
clock frequency is PHY/system-defined. The `phyfreq_range` parameter tells the MC how many
encodings the PHY supports. The MC must never drive an unsupported value.

`dfi_frequency` can change when `dfi_init_start` is low and should be ignored at that time. Once
`dfi_init_start` asserts, `dfi_frequency` must be legal and stable.

**Source:** DFI Specification v4.0 sections 3.5.5, 3.5.6, 4.10
