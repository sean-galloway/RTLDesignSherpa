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

# Inherited amber Contracts

jet inherits the following interface contracts unchanged from the [amber HAS](../../../../amber-mesi-l1/docs/amber_has/amber_has_index.md):

- **CPU-side GAXI slave.** The request/response pin names, valid/ready handshake, and ordering rules are the same as amber ch04 `01_cpu_gaxi.md`. The lockup-free delta appears as additional latency tolerance on the response path, not as a pin change.
- **Fabric-side AXI4 masters.** The pair-rig read/write master pins, ID usage, and ordering obligations are the same as amber ch04 `02_fabric_axi4.md`. jet will issue multiple outstanding read/write transactions through these masters; the in-order-per-ID rules still apply.
- **Fabric-side ACE masters.** The onyx-rig coherent transaction issuer is the same as amber ch04 `03_fabric_ace.md`. `ReadShared`, `ReadUnique`, `CleanUnique`, `MakeUnique`, `WriteBack`, and `Evict` still issue from the same pin contract.
- **ACE-shaped snoop port (AC/CD/CR).** The snoop responder contract is the same as amber ch04 `04_snoop_accdcr.md` and is defined by onyx D7. The data/response channels use the same no-ID in-order CR/CD obligations.

## Owner rulings inherited from amber/onyx

Ruling 2026-10-11 (Sean): the inherited ACE contract omits RACK/WACK
(the D7 port guarantees ordered data-return and snoop paths to the
coherency point, which is the condition Chinnakonda §7.20/§14.39 gives
for omitting them). The CD-before-CR snoop-response ordering remains the
binding family convention; the ACE spec only requires per-channel ordering.

## Jet-specific stress

The contracts themselves do not change, but the internal concurrency does. With multiple outstanding misses:

- The snoop port and the fabric masters must honor the same no-ID in-order CR/CD obligations under MSHR concurrency.
- A snoop may now match a pending fill in the MSHR file or a dirty victim in the write-back path. The contract still requires a response; per the J4/J5 rulings that response comes from the per-entry pending-fill bypass (post-fill state) or from the writeback buffer (snarf, SINK_WB_ACK semantics).
- The CPU-side GAXI slave presents responses in issue order (J4: no ID field exists, so out-of-order internal completion is re-sequenced before the response port).

The binding record for these obligations is the jet PRD J4 row.
