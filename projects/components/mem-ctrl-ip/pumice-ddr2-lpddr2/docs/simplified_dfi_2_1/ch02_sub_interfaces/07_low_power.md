# Low Power Control Interface

The low power control interface lets the MC tell the PHY when the memory
subsystem is expected to remain idle, giving the PHY an opportunity to enter a
lower power state. The interface is optional for both sides.

## Low power signals

| Signal | Direction | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| dfi_lp_req | MC -> PHY | 1 bit | 0x0 | Informs the PHY of a low-power opportunity. |
| dfi_lp_wakeup | MC -> PHY | 4 bits | no default | Encodes how quickly the MC needs normal operation to resume. |
| dfi_lp_ack | PHY -> MC | 1 bit | 0x0 | PHY acknowledges the low-power opportunity. |
: DFI 2.1 low power control interface signals

## Wakeup encoding

`dfi_lp_wakeup` is valid only while `dfi_lp_req` is asserted. The encoding
doubles the wakeup time on each step:

| dfi_lp_wakeup | tlp_wakeup cycles |
| --- | --- |
| 4'b0000 | 16 |
| 4'b0001 | 32 |
| 4'b0010 | 64 |
| 4'b0011 | 128 |
| 4'b0100 | 256 |
| 4'b0101 | 512 |
| 4'b0110 | 1024 |
| 4'b0111 | 2048 |
| 4'b1000 | 4096 |
| 4'b1001 | 8192 |
| 4'b1010 | 16384 |
| 4'b1011 | 32768 |
| 4'b1100 | 65536 |
| 4'b1101 | 131072 |
| 4'b1110 | 262144 |
| 4'b1111 | unlimited |
: Low power wakeup encoding

The value must remain constant until `dfi_lp_ack` asserts. After that the MC
may increase the value, allowing the PHY to enter a deeper low power state, but
it may not decrease it. The value at the moment `dfi_lp_req` de-asserts sets
the `tlp_wakeup` exit budget.

## Handshake

When the MC detects an idle window it asserts `dfi_lp_req` with a chosen
`dfi_lp_wakeup`. The PHY may acknowledge within `tlp_resp` cycles or ignore the
request. If it acknowledges, both signals remain asserted while the PHY is in
the low power state. After `dfi_lp_req` de-asserts, the PHY has `tlp_wakeup`
cycles to resume normal operation and de-assert `dfi_lp_ack`.

The DFI clock must remain valid and constant during the entire low power
handshake.

**Source:** DFI Specification v2.1.1 sections 3.7, 4.11
