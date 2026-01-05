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

# APB GPIO - Programming Model Overview

## Register Summary

| Offset | Name | Access | Description |
|--------|------|--------|-------------|
| 0x000 | GPIO_CONTROL | RW | Global control |
| 0x004 | GPIO_DIRECTION | RW | I/O direction |
| 0x008 | GPIO_OUTPUT | RW | Output data |
| 0x00C | GPIO_INPUT | RO | Input data |
| 0x010 | GPIO_INT_ENABLE | RW | Interrupt enable |
| 0x014 | GPIO_INT_TYPE | RW | Edge/level select |
| 0x018 | GPIO_INT_POLARITY | RW | Interrupt polarity |
| 0x01C | GPIO_INT_BOTH | RW | Both edges |
| 0x020 | GPIO_INT_STATUS | W1C | Interrupt status |

## Chapter Contents

### Basic Operations
Fundamental GPIO read/write operations.

**See:** [01_basic_operations.md](01_basic_operations.md)

### Interrupt Configuration
Setting up and handling GPIO interrupts.

**See:** [02_interrupt_config.md](02_interrupt_config.md)

### Programming Examples
Common use cases with code samples.

**See:** [03_examples.md](03_examples.md)

### Software Considerations
Performance tips and best practices.

**See:** [04_software_notes.md](04_software_notes.md)

---

**Next:** [01_basic_operations.md](01_basic_operations.md) - Basic Operations
