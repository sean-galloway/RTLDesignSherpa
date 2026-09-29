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

# Error-Correction IP

The family directory for error-correction codecs, created 2026-09-29 when the
Reed-Solomon component moved here from the `projects/components/` root (Sean).
One IP per subdirectory, each with its own `README.md`, `PRD.md`, `CLAUDE.md`,
`References/`, and -- when work starts -- `rtl/`, `dv/`, `docs/`. The task
lanes mirror the path: `vault/Tasks/projects/components/ecc-ip/<ip>/`.

| Directory | Code | Status |
|---|---|---|
| [`reed-solomon/`](reed-solomon/README.md) | RS(n, k) over GF(2^m); riBM key-equation solver decided, symbol width a parameter, scrambler behind `ENABLE_SCRAMBLER` | stood up 2026-09-29: references, draft PRD, architecture sketch; no RTL yet ([PRD](reed-solomon/PRD.md), [sketch](reed-solomon/docs/rs_architecture_sketch.md), [References](reed-solomon/References/README.md)) |

What belongs here and what does not: block codecs with their own field
arithmetic and decoder machinery (RS; BCH if PRD D7 brings it in; LDPC or polar
if a consumer ever asks). The Hamming SECDED primitives stay in
`rtl/common/dataint_ecc_*` -- a single-file library primitive is not an IP.
