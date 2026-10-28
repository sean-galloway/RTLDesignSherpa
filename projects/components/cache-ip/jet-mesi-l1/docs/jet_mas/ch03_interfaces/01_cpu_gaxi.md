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

# CPU GAXI Request/Response Timing

**Status:** planned contract. The base handshake is amber's (amber MAS
ch03/01): single-beat request, valid/ready both directions. This chapter
records only what MSHR concurrency changes.

## Accept timing

`req_ready` is high unless the lookup stage is occupied this cycle or the
classify would produce STALL for a resource reason that cannot resolve
combinationally (MSHR full, WB full with a dirty victim, set
oversubscribed, cross-class wait). A stalled request simply holds
`req_ready` low; the GAXI master retries unchanged.

## Response timing

- Hit: response data at the hit-service latency (amber's, unchanged), held
  at the sequencer until all earlier tags have released.
- Miss: response at fill commit + release-pointer wait.
- Merged requester: same commit, same release rule — a merged read's data
  comes from the just-installed line at commit.

## Ordering guarantee (J4)

Responses release strictly in accept order. The guarantee the CPU sees is
identical to amber's; only the latency distribution changes (which is the
J7 measurement).

## What the contract does NOT promise

No bound on miss latency (memory-dependent), no interleaving guarantees
between the request and response channels beyond valid/ready, and no
response reordering — ever.
