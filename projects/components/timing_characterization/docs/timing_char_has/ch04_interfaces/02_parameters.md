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

# 4.2 Parameters

## Feature Enable Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `EN_NAND_TREE` | 1 | Enable NAND binary tree FUB |
| `EN_INVERTER_CHAIN` | 1 | Enable inverter chain FUB |
| `EN_XOR_TREE` | 1 | Enable XOR binary tree FUB |
| `EN_CARRY_CHAIN` | 1 | Enable ripple-carry adder FUB |
| `EN_MULTIPLIER` | 1 | Enable multiplier FUB |
| `EN_MUX_TREE` | 1 | Enable mux binary tree FUB |
| `EN_QUEUE_DEPTH` | 1 | Enable FIFO queue FUB |
| `EN_CLK_DIVIDER` | 1 | Enable clock divider cascade FUB |
| `EN_GRAY_COUNTER` | 1 | Enable Gray counter FUB |

## FUB-Specific Parameters

| Parameter | Default | Valid Range | Description |
|-----------|---------|-------------|-------------|
| `NAND_LEVELS` | 4 | 1-12 | NAND tree depth (levels of NAND gates) |
| `NAND_NUM_FLOPS` | 8 | 2-2^LEVELS | Number of input flops for NAND tree |
| `INVERTER_COUNT` | 16 | 1-256 | Number of inverters in chain |
| `XOR_LEVELS` | 4 | 1-12 | XOR tree depth |
| `XOR_NUM_FLOPS` | 8 | 2-2^LEVELS | Number of input flops for XOR tree |
| `CARRY_WIDTH` | 8 | 4-512 | Adder operand bit width |
| `MULT_WIDTH` | 8 | 4-32 | Multiplier operand bit width |
| `MULT_TYPE` | 0 | 0-4 | Multiplier implementation type |
| `MUX_LEVELS` | 4 | 1-12 | Mux tree depth |
| `MUX_NUM_FLOPS` | 8 | 2-2^LEVELS | Number of data input flops for mux tree |
| `FIFO_DATA_WIDTH` | 8 | 1-64 | FIFO data width |
| `FIFO_DEPTH` | 16 | 4-4096 | FIFO depth (must be power of 2) |
| `CLK_DIV_STAGES` | 3 | 1-8 | Number of cascaded clock dividers |
| `CLK_DIV_CW` | 4 | 2-16 | Counter width per divider stage |
| `CLK_DIV_PICKOFF` | 2 | 0-CW-1 | Counter bit used for divided clock output |
| `GRAY_WIDTH` | 8 | 4-128 | Gray counter bit width |

## MULT_TYPE Values

| Value | Implementation | Requires |
|-------|---------------|----------|
| 0 | Inferred (`*` operator) | Any width |
| 1 | Dadda tree (structural) | Width 8, 16, or 32 |
| 2 | Wallace tree (structural) | Width 8, 16, or 32 |
| 3 | Wallace tree CSA (structural) | Width 8, 16, or 32 |
| 4 | Dadda 4:2 compressor (structural) | Width 8, 11, or 24 |

Unsupported width/type combinations fall back to inferred.
