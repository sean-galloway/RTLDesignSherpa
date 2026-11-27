<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Snoop AC / CR / CD Timing

The snoop port is per cache: onyx drives AC, the cache answers on CR and,
when it supplies, on CD. The contract is the in-repo
[AMBA ACE Interface Definition](../../../../References/AMBA_ACE_Interface_Definition.md)
with the family's CD-before-CR convention (invariant 6).

## Timing class per signal

| Signal | Class | Source |
|---|---|---|
| `s_acvalid[p]` | from flops | `r_snq_cnt[p] != 0 && r_sni_cnt[p] < SNOOP_INFLIGHT` |
| `s_acaddr[p]`, `s_acsnoop[p]` | from flops | the queue head's slot line and class; `s_acprot = 0` |
| `s_crready[p]` | from flops | `r_sni_cnt[p] != 0` |
| `s_cdready[p]` | **comb on `s_cdvalid`** | the per-buffer CD pick over the peers' `s_cdvalid` (ch02/03) |

: Table 3.2: Snoop-side timing classes

`CDREADY` depending on `CDVALID` is legal AXI (READY may wait for VALID)
and is the one place onyx uses it: a buffer's single write port is shared
by the peers that may supply that requester's slots. At `N_PORTS = 2` no
two peers ever share a buffer and `s_cdready[p]` reduces to "`s_cdvalid`
and a snoop outstanding".

## Ordering onyx relies on

- **In order per peer.** CRs come back in AC order; CD beats come back in
  AC order. onyx pairs both with the in-flight queue head, so a cache that
  answered out of order would corrupt the pairing. ACE requires it.
- **CD before CR.** A slot's CD beats all arrive before its CR; the CR
  resets the peer's CD beat counter. The beat index is counted, not
  carried.
- **No snoop to the requester.** The fanout never pushes the requester's
  own queue (ch02/03); the cache's own MSHR entry is therefore never asked
  about the line it is filling.
- **At most `SNOOP_INFLIGHT` outstanding per cache.** The rigs build 2;
  the default is 1.

## Cycle shape of one snoop

For one peer with an empty in-flight queue and a slot granted in cycle
*t*: the push lands in *t*, so `s_acvalid` is high from *t+1*. The AC
handshake moves the slot to the in-flight queue; `s_crready` is high from
the next cycle. CD beats (if any) are accepted as they come, one per cycle
when the buffer pick grants them; the CR handshake closes the snoop and
steps the slot's counter. With `DEFER_AR = 0` the memory AR is a candidate
from the cycle after the last peer's AC handshake.
