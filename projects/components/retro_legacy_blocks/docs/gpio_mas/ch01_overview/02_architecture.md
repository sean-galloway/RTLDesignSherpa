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

# APB GPIO - Architecture

## High-Level Block Diagram

### Figure 1.2: APB GPIO Top-Level Architecture

![APB GPIO Architecture](../assets/mermaid/gpio_block_diagram.png)

## Module Hierarchy

### Figure 1.3: APB GPIO Module Hierarchy

![APB GPIO Module Hierarchy](../assets/mermaid/gpio_module_hierarchy.png)

## Data Flow

### Write Transaction Flow

### Figure 1.4: Write Transaction Flow

![Write Transaction Flow](../assets/mermaid/gpio_write_flow.png)

### Read Transaction Flow

### Figure 1.5: Read Transaction Flow

![Read Transaction Flow](../assets/mermaid/gpio_read_flow.png)

### Interrupt Flow

### Figure 1.6: Interrupt Flow

![Interrupt Flow](../assets/mermaid/gpio_interrupt_flow.png)

## Clock Domains

### Synchronous Mode (CDC_ENABLE = 0)

### Figure 1.7: Synchronous Mode Clock Domains

![Synchronous Mode](../assets/mermaid/gpio_sync_mode.png)

In synchronous mode, all modules operate on the APB clock (pclk). Input synchronization remains active for external GPIO pins to prevent metastability.

### Asynchronous Mode (CDC_ENABLE = 1)

### Figure 1.8: Asynchronous Mode Clock Domains

![Asynchronous Mode](../assets/mermaid/gpio_async_mode.png)

In asynchronous mode, the APB clock domain handles protocol conversion while the GPIO clock domain handles all register and I/O operations. Skid buffers provide safe clock domain crossing.

## Parameterization

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `GPIO_WIDTH` | int | 32 | Number of GPIO pins |
| `SYNC_STAGES` | int | 2 | Input synchronizer stages |
| `CDC_ENABLE` | int | 0 | Enable clock domain crossing |
| `SKID_DEPTH` | int | 2 | CDC skid buffer depth |

: Table 1.1: GPIO Parameters

## Resource Estimates

| Component | Flip-Flops | LUTs |
|-----------|-----------|------|
| gpio_core | ~200 | ~300 |
| gpio_regs | ~400 | ~200 |
| gpio_config_regs | ~50 | ~100 |
| apb_slave (no CDC) | ~20 | ~50 |
| apb_slave_cdc | ~100 | ~150 |
| **Total (no CDC)** | ~670 | ~650 |
| **Total (with CDC)** | ~750 | ~750 |

: Table 1.2: Resource Estimates

---

**Next:** [03_clocks_and_reset.md](03_clocks_and_reset.md) - Clock and reset behavior
