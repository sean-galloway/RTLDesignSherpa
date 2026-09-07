<!-- markdownlint-disable -->

# Unmapped-Address Handling

## Why the bridge answers an address no slave owns

A positively-decoded fabric answers only addresses that fall inside some
slave's range. An address in none of them selects nothing: the one-hot select
is all-zero, no slave sees `AWVALID`/`ARVALID`, `READY` never rises, and the
master waits forever.

A hang is the worst failure available here, because it destroys the evidence.
There is no response to inspect, no error bit to read, and the offending
address is whatever the master still has latched. A stray pointer in software
becomes a wedged interconnect with nothing to point at the cause.

The bridge therefore ends its decode chain in an `else` -- subtractive decode
-- and that `else` selects an internal slave that always answers.

## Behaviour

| | |
|---|---|
| Write | every `W` beat is accepted; one `B` per `AW` |
| Read | `AxLEN+1` beats, `RLAST` on the last |
| Response | **`DECERR`** on both, always |
| Read data | `0xDEADBEEF`, replicated to the bus width |

`DECERR` rather than `SLVERR` is the AXI4 code for "no slave at this address":
nothing failed to service the request, there was nothing there to service it.
There is no `OKAY` mode and no parameter to select one -- a mode switch here is
where lint, simulation and synthesis end up disagreeing about what the fabric
does.

The read data is a recognisable pattern rather than zeros because zeros are
indistinguishable from real memory. `0xDEADBEEF` in a dump is a fault; `0` is a
plausible value.

Write data is discarded. There is nowhere for it to go, and inventing a
destination would be worse than saying so.

## Status, interrupt and clearing

The catch-all latches its status. Every bridge exposes:

| Port | Dir | Meaning |
|---|---|---|
| `unmapped_irq` | out | **sticky**: set by the first unmapped access, held until cleared |
| `unmapped_addr[31:0]` | out | address of that **first** access |
| `unmapped_count[7:0]` | out | number of unmapped accesses, saturating at 255 |
| `unmapped_clear` | in | pulse to clear the flag and the count |

Three choices worth knowing about:

* **Sticky, not a pulse.** A one-cycle pulse is gone before software can look,
  and this is precisely the access nobody expected.
* **The first address wins.** A later fault does not overwrite it; the first
  one is usually what explains the rest.
* **The address survives the clear**, so a late reader still learns where the
  fault was after the flag is acknowledged. The count saturates rather than
  wrapping -- "255+" is honest, a wrapped 3 is not.

## Register access (cfg regblock builds)

Bridges built with the cfg register block also expose the status over the
cfg AXI4-Lite/APB window:

| Register | Field | Access | Meaning |
|---|---|---|---|
| `SUBTRACTIVE_STATUS` | `HIT[0]` | RO | mirrors `unmapped_irq` |
| | `CLEAR[1]` | W | write 1 to clear the flag and count |
| | `COUNT[15:8]` | RO | mirrors `unmapped_count` |
| `SUBTRACTIVE_ADDR` | `ADDR[31:0]` | RO | mirrors `unmapped_addr` |

: Unmapped-address status registers

The sticky state lives in the RTL, not in the register block: one owner for
one piece of state, so the two cannot disagree about whether a fault happened.
These registers are a window onto it plus a clear. Clearing works from either
the `unmapped_clear` pin or a `CLEAR` write; neither disables the other.

These registers are appended **after** every pre-existing register, so adding
them did not move any existing offset. That is deliberate: a register map is an
ABI. An earlier attempt inserted per-slave configuration for the catch-all
midway through the map, which renumbered everything after it, silently moved
the monitor-enable bits, and left the monitors switched off while every
functional test still passed.

## What this does not do

The catch-all does not make an unmapped access *correct*. It makes it
**visible and survivable**: the master gets an error instead of stalling, and
software gets an address instead of a puzzle. An address that reaches it is
still a configuration or software fault.

**Previous:** [AXI5 and APB5 Interfaces](04_axi5_apb5_interfaces.md)
