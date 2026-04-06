# SPDX-License-Identifier: MIT
# Formal verification Makefile for uart_rx
# No sv2v needed: uart_rx uses no packages, read directly as -sv

.PHONY: prove cover all clean

all: prove cover

prove:
	sby -f uart_rx.sby prove

cover:
	sby -f uart_rx.sby cover

clean:
	rm -rf uart_rx_prove uart_rx_cover
