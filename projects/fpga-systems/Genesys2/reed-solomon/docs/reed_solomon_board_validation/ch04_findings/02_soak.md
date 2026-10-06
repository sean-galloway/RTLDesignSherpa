# Soak Run Scheduled

## Status at publication time

The million-block soak for Reed-Solomon was scheduled at publication time and
had not yet completed. This chapter records the target and the reporting plan;
it contains no fabricated numbers.

## Target

- Code: RS(252,236) t=8, S=4.
- Board: Digilent Genesys 2 serial `200300B818A0`.
- Target image: `genesys2_axis_ribm` or `genesys2_axis_euclid`; the AXIS
  flavour is used because the AXI4 job-memory cap makes long soaks impractical.
- Target volume: 1,000,000 blocks, matching the BCH soak depth.
- Host interface: UART 115200-8N1, so the effective block rate will be
  host-bound rather than datapath-bound.

## What will be reported

When the soak completes, the following will be added to this chapter and the
battery JSON artifact:

- Final block count, wall time, and blocks per second.
- Clean, corrected, and uncorrectable block counts.
- Total symbols corrected.
- Number of blocks with more than t errors and whether every one was flagged.
- Mis-decode count (must be 0 for a pass).
- The soak-timeline figure.

Until those numbers exist, the honest statement is that the run is scheduled.
