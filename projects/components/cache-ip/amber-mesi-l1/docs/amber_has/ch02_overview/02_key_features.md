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

# Key Features

| Feature | What amber does | PRD / F anchor |
|---|---|---|
| Blocking single-outstanding pipeline | One miss at a time; the front end freezes until fill + replay complete. | F1 |
| Parameterized geometry | 4–32 KiB capacity, 32–64 B lines, 2–8 ways; default 32 KiB / 64 B / 4-way (128 sets); tiny 16-set / 2-way config reserved for proofs. | D1 |
| GAXI CPU-side slave | House valid/ready streaming port with skid/FIFO plumbing; STREAM attaches without an adapter. | D2 |
| Write-back + write-allocate | Default policy; write-through/no-allocate retained as a bring-up mode only. | D5 |
| Plain MESI on a 3-bit state field | Stable M/E/S/I; headroom for MOESI O-state as a later elaboration upgrade. | D6 |
| Pluggable replacement | LRU (default), tree-PLRU, FIFO, RANDOM; LRU/FIFO/RANDOM have cache_sim golden parity; tree-PLRU is the timing-tight fallback without a sim golden model. | D7 |
| ACE-shaped snoop responder | AC/CR/CD adapter facing peer or onyx; bus-agnostic inside. | D4 |
| Pending-fill bypass register | Probe-during-fill answered from the register, bounded and state-accurate. | F9 |
| Two tops on one core | `amber` for the pair rig, `amber_ace` for the onyx rig; no mode parameter. | F12 |
| MonBus observation | `amber_monlite` emits 128-bit packets; drop-and-count, never stalls the observed path. | D8 |

: Table 2.0: Key features and their decisions

The feature set is intentionally narrow. Every item that is not listed is a non-goal: no MSHRs, no prefetch, no ECC, no multi-port issue, no directory filter, no barrier/DVM support. That narrowness is the design.
