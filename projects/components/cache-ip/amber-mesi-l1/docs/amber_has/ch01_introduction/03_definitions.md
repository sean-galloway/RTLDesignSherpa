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

# Definitions and Acronyms

| Term | Definition |
|---|---|
| **ACE** | AXI Coherency Extensions (Arm IHI 0022); the protocol shape used for the snoop port and, in the onyx rig, for coherent fabric transactions. |
| **AC / CR / CD** | ACE snoop channels: Address, Response, Data. |
| **ARSNOOP / AWSNOOP** | ACE transaction-type fields on read and write address channels. |
| **CRRESP** | Five-bit snoop response: `DataTransfer`, `Error`, `PassDirty`, `IsShared`, `WasUnique`. |
| **MESI** | Cache-coherence states: Modified, Exclusive, Shared, Invalid. |
| **MOESI** | MESI plus Owned state; amber reserves encoding headroom but does not implement O in v1.0. |
| **Line** | The cache allocation unit, parameterized but defaulting to 64 bytes. |
| **Set** | The group of ways indexed by the set portion of the address. |
| **Way** | One associative entry within a set. |
| **Blocking** | The cache accepts no new CPU request while a miss is outstanding. |
| **MSHR** | Miss Status Holding Register; amber deliberately has none. |
| **Fill** | The memory/peer response that writes a missing line into the data array. |
| **Drain** | The write-back of a dirty victim line to memory or the CCU. |
| **Pending-fill bypass** | The single register that lets a snoop probe observe the post-fill state while the fill is still in flight (F9). |
| **Victim buffer** | A small staging buffer for a dirty line waiting to drain; amber uses depth 1. |
| **GAXI** | The house generic AXI-like valid/ready streaming bus used for the CPU-side port. |
| **MonBus** | The 128-bit observation packet bus emitted by `*_monlite` wrappers. |
| **Pair rig** | Two `amber` instances plus shared memory, the gated deliverable (D10). |
| **Onyx rig** | An `amber_ace` instance attached to the `onyx` coherency manager. |
| **Pattern-B** | The repo's cocotb GATE/FUNC/FULL verification grid naming. |

: Table 1.0: Definitions and acronyms
