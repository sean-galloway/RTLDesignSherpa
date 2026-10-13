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

The generator validates inputs early and raises `ValueError` before emitting any RTL.

## Structural checks

| Rule | Error message shape |
|------|---------------------|
| `1 <= num_masters <= 16` | "Number of masters must be 1-16, got N" |
| `1 <= num_slaves <= 16` | "Number of slaves must be 1-16, got N" |
| `len(master_versions) == num_masters` | "version list length mismatch" |
| `len(slave_versions) == num_slaves` | "version list length mismatch" |
| Each version is `'apb4'` or `'apb5'` | "unknown port version '...'" |

## Address-map checks

| Rule | Rationale |
|------|-----------|
| `slave_size` must be a power of two. | Slave selection uses bit slicing after subtracting `BASE_ADDR`. |
| `slave_size >= 256` (0x100). | Keeps the stride above the smallest practical APB register region. |

The generator does **not** check whether the full span (`num_slaves * slave_size`) overflows the address width; that is the caller's responsibility.

## Parity checks

There is no explicit parity validation beyond the version lists. If `enable_parity=True` and a port is APB4, the generator simply omits parity pins for that port. This is intentional: mixed parity-on/off systems are allowed, and the absence of pins is the safe default.
