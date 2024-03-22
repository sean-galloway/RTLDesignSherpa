---
title: PWM
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The PWM (Pulse Width Modulation) module generates a PWM signal for multiple channels. Each channel has independent control and configuration. The module is practical for applications requiring multiple PWM signals with different duty cycles, periods, and repeat counts.

## Parameters

- `WIDTH`: Bit width of the duty cycle, period, and repeat count. The default is 8.
- `CHANNELS`: Number of PWM channels. The default is 4.

## Inputs

- `i_clk`: Clock signal. Synchronizes the operation of the PWM logic.
- `i_rst_n`: Active low reset signal. Resets the module's internal states when low.
- `i_start [CHANNELS-1:0]`: Start signals for each PWM channel. Starts the PWM operation for each corresponding channel.
- `i_duty [CHANNELS*WIDTH-1:0]`: Duty cycle values for each channel. Determines the duration for which the PWM signal stays high in each cycle.
- `i_period [CHANNELS*WIDTH-1:0]`: Period values for each channel. Sets the total duration of each PWM cycle.
- `i_repeat_count [CHANNELS*WIDTH-1:0]`: Repeat count values for each channel. Specifies how many times the PWM cycle should repeat.

## Outputs

- `ow_done [CHANNELS-1:0]`: Signals indicating the completion of the repeat count for each channel.
- `o_pwm [CHANNELS-1:0]`: PWM output signals for each channel.

## Functionality

- Each channel of the PWM operates independently based on its configuration.
- The `r_count` register in each channel counts up to the specified period and then resets to 0.
- The PWM signal for a channel remains high as long as the `r_count` is less than the duty cycle value and the channel is active (not done).
- If the duty cycle is greater than or equal to the period, the PWM signal stays high continuously, representing a 100% duty cycle.
- The repeat count mechanism allows the PWM cycle to repeat several times before signaling completion through the `ow_done` output.
- The module supports the simultaneous operation of multiple channels with different configurations.

## Implementation Details

- The module uses a `generate` block to create separate logic for each channel.
- The module provides independent control for each channel's start, duty cycle, period, and repeat count.
- The module is suitable for applications requiring multiple, independently controlled PWM signals.

---

[Return to Index](/docs/mark_down/rtl/)

---
