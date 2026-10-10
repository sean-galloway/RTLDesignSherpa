# Error Interface

The error interface lets the PHY report error conditions to the MC. It is
optional for both MC and PHY, and is not phased for frequency-ratio
systems.

## Error signals

| Signal | From | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| `dfi_error` | PHY | DFI Error Width | 0 | Indicates the PHY has detected an error. Typically one bit per data slice plus one bit for control. |
| `dfi_error_info` | PHY | DFI Error Width x 4 | 0 | Additional information about the error source. Valid only while `dfi_error` is asserted. |

: Error interface signals

The PHY may implement `dfi_error` as a single bit or as one bit per data
slice plus one control bit. `dfi_error_info` provides four bits per error
instance. The specification defines only a few general encodings; the rest
are design-specific. Undriven bits must be tied low at the MC.

## Error timing

| Parameter | Defined by | Meaning |
| --- | --- | --- |
| `terror_resp` | PHY | Max cycles from the affected transaction to `dfi_error` assertion. |

: Error interface timing parameter

For data errors the reference point is `dfi_wrdata_en` or `dfi_rddata_en`.
For command errors the reference point is the command itself. Because
`terror_resp` is a maximum, the MC may not be able to correlate the error
with a single transaction.

## Spec-defined error codes

| `dfi_error_info` | Name | Meaning |
| --- | --- | --- |
| 0000 | General purpose | PHY general-purpose error. |
| 0001 | Internal PHY | PHY-specific internal error. |
| 0010-0111 | Reserved | Reserved for future definition. |
| 1000-1111 | User-defined | Available for design-specific codes. |

: DFI 3.1 error codes

The scoria controller uses the error indication but ignores the DDR4-
specific encodings, treating `dfi_error` as a generic PHY fault flag.

**Source:** DFI Specification v3.1 sections 3.8, 4.13, Table 21, Table 22, Table 27
