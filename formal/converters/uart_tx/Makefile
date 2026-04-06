# SPDX-License-Identifier: MIT
# Formal verification Makefile for uart_tx
# No sv2v needed: uart_tx uses no packages, read directly as -sv

.PHONY: prove cover all clean

all: prove cover

prove:
	sby -f uart_tx.sby prove

cover:
	sby -f uart_tx.sby cover

clean:
	rm -rf uart_tx_prove uart_tx_cover
