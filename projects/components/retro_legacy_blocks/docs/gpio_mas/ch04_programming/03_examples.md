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

# APB GPIO - Programming Examples

## LED Control

### Simple LED Blink

```c
#define LED_PIN  (1 << 0)

void led_init(void) {
    GPIO_CONTROL = 1;            // Enable GPIO
    GPIO_DIRECTION |= LED_PIN;   // Set as output
}

void led_on(void) {
    GPIO_OUTPUT |= LED_PIN;
}

void led_off(void) {
    GPIO_OUTPUT &= ~LED_PIN;
}

void led_toggle(void) {
    GPIO_OUTPUT ^= LED_PIN;
}
```

### Multiple LED Control

```c
#define LED_MASK  0x000000FF  // LEDs on pins 7:0

void leds_write(uint8_t pattern) {
    uint32_t output = GPIO_OUTPUT;
    output = (output & ~LED_MASK) | pattern;
    GPIO_OUTPUT = output;
}
```

## Button Input

### Simple Button Read

```c
#define BUTTON_PIN  (1 << 8)

void button_init(void) {
    GPIO_CONTROL = 1;              // Enable GPIO
    GPIO_DIRECTION &= ~BUTTON_PIN; // Set as input
}

bool button_pressed(void) {
    return (GPIO_INPUT & BUTTON_PIN) != 0;
}
```

### Button with Interrupt

```c
#define BUTTON_PIN  (1 << 8)

volatile bool button_event = false;

void button_init_irq(void) {
    GPIO_CONTROL = 1;
    GPIO_DIRECTION &= ~BUTTON_PIN;

    // Configure falling edge interrupt (button press)
    GPIO_INT_TYPE &= ~BUTTON_PIN;      // Edge mode
    GPIO_INT_POLARITY &= ~BUTTON_PIN;  // Falling edge
    GPIO_INT_BOTH &= ~BUTTON_PIN;      // Single edge
    GPIO_INT_ENABLE |= BUTTON_PIN;     // Enable
}

void button_isr(void) {
    if (GPIO_INT_STATUS & BUTTON_PIN) {
        button_event = true;
        GPIO_INT_STATUS = BUTTON_PIN;  // Clear
    }
}
```

## DIP Switch Reading

### 8-Bit Switch Input

```c
#define SWITCH_MASK  0x00FF0000  // Switches on pins 23:16
#define SWITCH_SHIFT 16

void switch_init(void) {
    GPIO_CONTROL = 1;
    GPIO_DIRECTION &= ~SWITCH_MASK;  // All inputs
}

uint8_t switch_read(void) {
    return (GPIO_INPUT & SWITCH_MASK) >> SWITCH_SHIFT;
}
```

## Parallel Data Interface

### 8-Bit Output Port

```c
#define DATA_MASK   0x000000FF  // Data on pins 7:0
#define STROBE_PIN  (1 << 8)    // Strobe on pin 8

void data_port_init(void) {
    GPIO_CONTROL = 1;
    GPIO_DIRECTION |= (DATA_MASK | STROBE_PIN);
    GPIO_OUTPUT &= ~STROBE_PIN;  // Strobe low
}

void data_write(uint8_t data) {
    uint32_t output = GPIO_OUTPUT;
    output = (output & ~DATA_MASK) | data;
    GPIO_OUTPUT = output;

    // Generate strobe pulse
    GPIO_OUTPUT |= STROBE_PIN;
    // Small delay if needed
    GPIO_OUTPUT &= ~STROBE_PIN;
}
```

### 8-Bit Input Port with Ready

```c
#define DATA_MASK   0x000000FF  // Data on pins 7:0
#define READY_PIN   (1 << 8)    // Ready on pin 8

void data_input_init(void) {
    GPIO_CONTROL = 1;
    GPIO_DIRECTION &= ~(DATA_MASK | READY_PIN);

    // Interrupt on ready rising edge
    GPIO_INT_TYPE &= ~READY_PIN;
    GPIO_INT_POLARITY |= READY_PIN;
    GPIO_INT_ENABLE |= READY_PIN;
}

uint8_t data_read(void) {
    return GPIO_INPUT & DATA_MASK;
}
```

## PWM-Style Output

### Bit-Banged PWM (Low Frequency)

```c
#define PWM_PIN  (1 << 0)

void pwm_init(void) {
    GPIO_CONTROL = 1;
    GPIO_DIRECTION |= PWM_PIN;
}

// Call from timer interrupt
void pwm_update(uint8_t duty, uint8_t *counter) {
    (*counter)++;
    if (*counter >= 100) *counter = 0;

    if (*counter < duty) {
        GPIO_OUTPUT |= PWM_PIN;
    } else {
        GPIO_OUTPUT &= ~PWM_PIN;
    }
}
```

## Wake-On-Change

### Power Management Integration

```c
#define WAKE_PINS  0x0000000F  // Wake sources on pins 3:0

void wake_setup(void) {
    // Configure both-edge interrupts for wake pins
    GPIO_INT_TYPE &= ~WAKE_PINS;   // Edge mode
    GPIO_INT_BOTH |= WAKE_PINS;    // Both edges
    GPIO_INT_ENABLE |= WAKE_PINS;  // Enable

    // Clear any pending before sleep
    GPIO_INT_STATUS = WAKE_PINS;
}

void enter_sleep(void) {
    wake_setup();
    // Platform-specific sleep entry
    __WFI();  // Wait for interrupt
}
```

---

**Next:** [04_software_notes.md](04_software_notes.md) - Software Considerations
