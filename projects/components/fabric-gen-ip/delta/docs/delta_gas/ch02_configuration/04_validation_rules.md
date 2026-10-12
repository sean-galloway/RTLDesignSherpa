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

# Validation Rules

The generator validates CLI arguments through `argparse` and additional checks inside `main()`.

## CLI-level checks

| Rule | Behavior |
|------|----------|
| `--topology` must be `flat`, `tree`, or `both`. | Enforced by `choices`. |
| `--masters` and `--slaves` are required integers. | Enforced by `required=True`. |
| `--strb-width` must be >= 0. | Custom check; negative values raise an error. |
| `--amba5` requires `--data-width % 8 == 0`. | Custom check; `TDATACHK` is one bit per `TDATA` byte (IHI 0051B Table 5-1). |

## Internal checks

| Rule | Rationale |
|------|-----------|
| `num_masters >= 1` and `num_slaves >= 1` | A crossbar needs at least one master and one slave. |
| `data_width > 0` | Required for meaningful `TDATA`. |
| `user_width >= 1` | `TUSER` is always at least one bit. |
| `dest_width = ceil(log2(num_slaves))` | `TDEST` must encode all slave indices. |
| `id_width = ceil(log2(num_masters))` | `TID` must encode all master indices. |

The generator does **not** currently validate that `strb_width` matches `data_width/8`; callers must ensure the width is consistent with their byte-qualifier policy.
