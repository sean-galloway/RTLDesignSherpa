# axi_gen_addr

This SystemVerilog module generates the next address for AXI transactions based on the current address, transfer size, burst type, and length.

## Module Parameters

- `AW`: Address width in bits (default: 32)
- `DW`: Input data width in bits (default: 32)
- `ODW`: Output data width in bits (default: 32)
- `LEN`: Maximum burst length support (default: 8)

## Ports

### Inputs:

- `i_curr_addr`: Current address (width: AW)
- `i_size`: Transfer size encoding (width: 3)
- `i_burst`: Burst type (width: 2)
- `i_len`: Burst length (width: LEN)

### Outputs:

- `ow_next_addr`: Next address based on burst type and size (width: AW)
- `ow_next_addr_align`: Aligned address for proper data bus boundaries (width: AW)

## Functionality

1. **Local Parameters**:
   - `ODWBYTES`: Number of bytes in the output data width (ODW/8)

2. **Address Increment Calculation**:
   - Calculates the increment based on transfer size (`i_size`)
   - Adjusts increment if input and output data widths differ
   - Enforces limits on increment size based on output data width

3. **Wrap Address Calculation**:
   - Computes the wrap mask based on size and burst length
   - Calculates the aligned address for wrap operations
   - Applies wrap mask to handle proper address wrapping

4. **Burst Type Handling**:
   - FIXED (2'b00): Returns the same address (no increment)
   - INCR (2'b01): Returns the current address plus increment
   - WRAP (2'b10): Returns the wrapped address based on calculated mask
   - Default: Behaves like INCR burst

5. **Alignment**:
   - Produces both the exact next address and an aligned version
   - Alignment ensures proper data bus boundary alignment

This module is used in AXI master and slave implementations to correctly calculate address sequences for burst transfers, adhering to the AXI protocol specification for different burst types (FIXED, INCR, and WRAP).

---

[Return to Index](index.md)

---