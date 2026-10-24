# TASK-003 — split the X stage to clock gatling above 100 MHz

**Status:** deferred -- 2026-10-21; owner: "permanently defer we can look at this later 100mhz is good enough". Un-defers when a consumer needs gatling above 100 MHz. · **Priority:** low · **Filed:** 2026-10-21 · **Area:** projects/components/riscv-ip/gatling-rv32i

## Why

On the Nexys A7-100T, gatling closes 100 MHz with +0.152 ns of slack (MAS ch07; board README, "Board result"). The worst path is 9.4 ns over 10 levels: regfile BRAM -> branch compare / halt logic -> `pc_q` clock enable. That is the X stage; F, D and W have slack.

## What

Move part of X (the branch/halt resolution, or the PC enable) into a deeper rotation or a split stage, so the clock is bound by something other than X.

## Done when

The clock target moves above 100 MHz on the A7 with positive WNS, and DV (full), formal and the board battery are all green.
