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

## Overview

Thirteen registers do all the work. Everything in this chapter is a recipe built on these:

| Offset | Name | Access | Reset | Description |
|--------|------|--------|-------|-------------|
| 0x000 | GPIO_CONTROL | RW | 0x00000001 | Global control |
| 0x004 | GPIO_DIRECTION | RW | 0x00000000 | I/O direction |
| 0x008 | GPIO_OUTPUT | RW | 0x00000000 | Output data |
| 0x00C | GPIO_INPUT | RO | - | Input data |
| 0x010 | GPIO_INT_ENABLE | RW | 0x00000000 | Interrupt enable |
| 0x014 | GPIO_INT_TYPE | RW | 0x00000000 | Edge/level select |
| 0x018 | GPIO_INT_POLARITY | RW | 0xFFFFFFFF | Interrupt polarity |
| 0x01C | GPIO_INT_BOTH | RW | 0x00000000 | Both edges |
| 0x020 | GPIO_INT_STATUS | W1C | 0x00000000 | Interrupt status |
| 0x024 | GPIO_RAW_INT | RO | 0 (live) | Raw (unlatched) event status |
| 0x028 | GPIO_OUTPUT_SET | WO | 0x00000000 | Atomic output set (reads return 0) |
| 0x02C | GPIO_OUTPUT_CLR | WO | 0x00000000 | Atomic output clear (reads return 0) |
| 0x030 | GPIO_OUTPUT_TGL | WO | 0x00000000 | Atomic output toggle (reads return 0) |

### In This Chapter

#### Basic Operations
Fundamental GPIO read/write operations.

**See:** [01_basic_operations.md](01_basic_operations.md)

#### Interrupt Configuration
Setting up and handling GPIO interrupts.

**See:** [02_interrupt_config.md](02_interrupt_config.md)

#### Programming Examples
Common use cases with code samples.

**See:** [03_examples.md](03_examples.md)

#### Software Considerations
Performance tips and best practices.

**See:** [04_software_notes.md](04_software_notes.md)

---

## Navigation

**Next:** [01_basic_operations.md](01_basic_operations.md) - Basic Operations
