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

# Fabric ACE Master Timing

The `amber_ace` onyx-rig top uses the house `axi4ace_master_rd` and `axi4ace_master_wr` wrappers. The timing is identical to the AXI4 case except for the `ARSNOOP`/`AWSNOOP` fields, the constant `AxDOMAIN`/`AxBAR` fields, the 4-bit `RRESP`, and the auto-pulsed `RACK`/`WACK` outputs (deprecated per ruling 2026-10-11 (Sean); removal tracked as amber A5).

## Domain, Barrier and Read-Response Fields

Every amber transaction is coherent and the onyx rig has one shareability domain, so `amber_ace_top` drives `ARDOMAIN` and `AWDOMAIN` to `0b10` (Outer Shareable), an encoding IHI 0022H Tables D3-7 and D3-8 permit for every Table 4.2 transaction type. Inner Shareable would also be legal on ACE, but ACE5 deprecates it. amber issues no barrier transactions (onyx D8), so `ARBAR` and `AWBAR` are `0b00`, a normal access that respects barriers.

`RRESP` is 4 bits on an ACE read (IHI 0022H §D2.1.3, Table D3-14). `RRESP[1:0]` reaches the fill engine as before. `RRESP[3:2]` (IsShared, PassDirty) travels through the read transport and its monitor, but the core does not use it. The install state comes from the request class: `ReadShared` installs S and `ReadUnique` installs M. S is legal for either IsShared value, and M already owns the dirty data, so neither class depends on IsShared. The one response amber cannot honour is `PassDirty = 1` on a `ReadShared`, because it would install a clean S and lose the write-back. amber therefore relies on its manager keeping PassDirty low on `ReadShared`. IHI 0022H gives a MESI cache `ReadNotSharedDirty` for this case. The item is open: no port contract states the rule yet.

## Read Transactions

| Cache event | ACE transaction | `fub_axi_arsnoop` |
|---|---|---|
| read miss, shared intent | `ReadShared` | `ReadShared` encoding |
| read miss, exclusive intent | `ReadUnique` | `ReadUnique` encoding |

`RACK` is auto-pulsed one cycle after `RLAST` is accepted (deprecated per ruling 2026-10-11 (Sean); removal tracked as amber A5). `amber_ace_issue` supplies `fub_axi_arsnoop`; `amber_fill` supplies address, length, size, and burst.

## Write Transactions

| Cache event | ACE transaction | `fub_axi_awsnoop` |
|---|---|---|
| write to Shared line | `CleanUnique` | `CleanUnique` encoding |
| write to Invalid line (whole line) | `MakeUnique` | `MakeUnique` encoding |
| dirty eviction | `WriteBack` | `WriteBack` encoding |
| clean eviction | `Evict` | `Evict` encoding |

`WACK` is auto-pulsed one cycle after the B handshake (deprecated per ruling 2026-10-11 (Sean); removal tracked as amber A5). `CleanUnique`, `MakeUnique`, and `Evict` are AW-only transactions with no W data. `WriteBack` is an AW+W burst with the dirty victim data.

## Timing Example: ReadShared Fill

```
Cycle :  0   1   2   3   4   5   6
AR_v  :  1   0   0   0   0   0   0
AR_r  :  1   0   0   0   0   0   0   <- AR handshake, ARSNOOP=ReadShared
R_v   :  0   0   0   1   1   1   0
R_r   :  0   0   0   1   1   1   0
last  :  0   0   0   0   0   1   0
rack  :  0   0   0   0   0   0   1   <- auto-pulsed
```

## Timing Example: WriteBack Drain

```
Cycle :  0   1   2   3   4   5   6
AW_v  :  1   0   0   0   0   0   0
AW_r  :  1   0   0   0   0   0   0   <- AW handshake, AWSNOOP=WriteBack
W_v   :  0   1   1   1   0   0   0
W_r   :  0   1   1   1   0   0   0
last  :  0   0   0   1   0   0   0
B_v   :  0   0   0   0   0   1   0
B_r   :  0   0   0   0   0   1   0
wack  :  0   0   0   0   0   0   1   <- auto-pulsed
```

---

**Last Updated:** 2026-10-11
