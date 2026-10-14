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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Mixed APB4/APB5 and Parity

The generator supports mixed-version ports: any master or slave can be declared APB4 or APB5 independently. The feature is controlled entirely by the `master_versions` and `slave_versions` lists.

## Version list rules

- Each list has length `num_masters` or `num_slaves`.
- Valid values are `'apb4'` or `'apb5'`.
- APB4 ports expose the classic PSEL/PENABLE/PADDR/PWRITE/PWDATA/PSTRB/PPROT/PRDATA/PSLVERR/PREADY set.
- APB5 ports add `PAUSER`, `PWUSER`, `PWAKEUP`, `PRUSER`, and `PBUSER`.

## PWAKEUP direction and forwarding

`PWAKEUP` is a **Requester** output (AMBA APB IHI 0024E section 3.7.2,
Table 3-7). The crossbar sits between two kinds of APB5 interface, so the pin
points a different way on each:

| Port | Direction at the crossbar | Behaviour |
|------|---------------------------|-----------|
| `m<i>_apb_PWAKEUP` (APB5 requester port) | Input | Driven by the external requester. Parity-checked by the `apb5_slave` boundary IP when parity is on. |
| `s<j>_apb_PWAKEUP` (APB5 completer port) | Output | Driven by the crossbar, which is the Requester on this interface. |

: PWAKEUP Direction at the Crossbar

Each APB5 completer port drives

```
s<j>_apb_PWAKEUP = <boundary apb5_master's own PWAKEUP>
                 | m<i>_apb_PWAKEUP   for every APB5 requester i
```

- **The boundary term** is the `apb5_master` IP's registered wake. It is high
  while a command for that completer is pending or a transfer is in flight, so
  it leads PSEL by a cycle and holds through PREADY. It covers every
  transfer, including one from an APB4 requester that has no `PWAKEUP` at
  all. 3.7.2 permits a Completer to wait for `PWAKEUP` before asserting
  PREADY, so a PSEL without it could deadlock.
- **The requester terms** forward each APB5 requester's wake. Every requester
  can address every completer here, because there is one address map for all
  masters. "Any requester that can address this completer" is therefore all
  of them. The wake is not routed by decode: the address is unknown until
  PSEL, and 3.7.2 recommends `PWAKEUP` lead PSEL. The cost is that a
  requester's wake also raises `PWAKEUP` on completers it will not access.
  3.7.2 permits a wake with no transfer, though it does not recommend one.
- **Glitch-free.** 3.7.2 requires `PWAKEUP` to be glitch-free and names a
  glitch-free OR tree as a valid construction. The tree ORs a flop output with
  requester `PWAKEUP` inputs, and those inputs are themselves required to be
  glitch-free. Nothing is registered, so a requester's wake reaches the
  completer in the same cycle and keeps its lead over PSEL.

The completer's `PWAKEUP` is not forwarded back to any requester, because it
has no completer-to-requester meaning. The old crossbar treated `PWAKEUP` as
completer-driven and dropped it (the `rsp_pwakeup` and `wakeup_request` boundary
pins). Both pins are gone from `apb5_master` and `apb5_slave` (issue #102 item 7).

## Mixed-port sideband behavior

The cmd/rsp fabric between boundary modules is where the protocol conversion happens. Sideband signals are carried only when **both** the source master and the target slave are APB5:

- If the source master is APB5 but the selected slave is APB4, `cmd_pauser` and `cmd_pwuser` are dropped at the slave-side APB4 master.
- If the source master is APB4 but the selected slave is APB5, the APB5 master ties `cmd_pauser` and `cmd_pwuser` to zero.
- Response sideband (`pruser`, `pbuser`) follows the same rule in reverse.

This keeps the fabric simple: there is one cmd/rsp width per direction, and the boundary modules handle expansion or zero-padding.

## Parity (`enable_parity=True`)

APB5 parity is optional and independent of the version lists. The generator
emits parity pins only on APB5 interfaces. The pins are the IHI 0024E
chapter 5 check signals. Parity is **odd**: each check bit plus the bits it
covers hold an odd number of ones. Wide signals get one check bit per 8 bits
(Table 5-1). For a one-bit signal, the check bit is the inversion of the
signal.

| Check signal | Width at the crossbar | Covers | Requester port (`m<i>_`) | Completer port (`s<j>_`) |
|--------------|-----------------------|--------|--------------------------|--------------------------|
| `PADDRCHK` | `(ADDR_WIDTH+7)/8` | `PADDR` | input, checked | output, regenerated |
| `PCTRLCHK` | 1 | `PPROT`, `PWRITE` (no `PNSE` is carried) | input, checked | output, regenerated |
| `PSELCHK` | 1 | `PSEL` (`PSELxCHK`) | input, checked | output, regenerated |
| `PENABLECHK` | 1 | `PENABLE` | input, checked | output, regenerated |
| `PWDATACHK` | `STRB_WIDTH` | `PWDATA` | input, checked | output, regenerated |
| `PSTRBCHK` | 1 | `PSTRB` | input, checked | output, regenerated |
| `PAUSERCHK` | 1 | `PAUSER` | input, checked | output, regenerated |
| `PWUSERCHK` | 1 | `PWUSER` | input, checked | output, regenerated |
| `PWAKEUPCHK` | 1 | `PWAKEUP` | input, checked | output, `~s<j>_apb_PWAKEUP` |
| `PRDATACHK` | `STRB_WIDTH` | `PRDATA` | output, regenerated | input, checked |
| `PREADYCHK` | 1 | `PREADY` | output, regenerated | input, checked |
| `PSLVERRCHK` | 1 | `PSLVERR` | output, regenerated | input, checked |
| `PRUSERCHK` | 1 | `PRUSER` | output, regenerated | input, checked |
| `PBUSERCHK` | 1 | `PBUSER` | output, regenerated | input, checked |

: APB5 Parity Check Signals

The user signals are 1 bit on the crossbar surface, so each user check signal
is 1 bit. A completer port's `PWAKEUPCHK` is computed by the crossbar over the
OR above. It is not taken from the `apb5_master` IP, whose own check bit
covers only the IP's term, so that output is left unconnected.

Parity does **not** cross the cmd/rsp fabric. The boundary IP deconstructs the
APB transfer, checks parity at entry under each signal's Table 5-1 Check
Enable term, and regenerates it at exit. Each APB5 requester port exposes
`m<i>_parity_error_wdata` and `m<i>_parity_error_ctrl`. Each APB5 completer
port exposes `s<j>_parity_error_rdata` and `s<j>_parity_error_ctrl`. A fabric
fault is therefore distinguishable from a slave's own `PSLVERR` response. When
parity is off, the boundary IP's check inputs are tied LOW and its check
outputs are left unconnected. The crossbar module then has no check pins at
all.

`test_apbx_xbar_parity.py` generates an all-APB5 2x2 variant with
`enable_parity=True` into its build directory. It checks every check output
for odd parity, injects bad `PWDATACHK` and `PRDATACHK` and expects the
matching error flag, and checks `PWAKEUP` forwarding from either requester to
both completers.

The shipped `apbx_xbar_2to2_mixed` variant uses APB5 without parity. Parity is reserved for custom subsystems that explicitly request it.
