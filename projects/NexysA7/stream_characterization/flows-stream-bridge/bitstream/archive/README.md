# Bitstream archive

Each `.bit` file is named `<commit_sha>.bit` — a known-good build snapshot.
The latest working build is the one with the most recent commit-sha file.

To reuse a known-good bitstream instead of rebuilding (saves ~25 min):
```
cp bitstream/archive/<sha>.bit bitstream/stream_char.bit
cd ../flows-stream-bridge && make program
```

Convention: archive the bit ONLY AFTER UART ping confirms the design is alive.

## Notable archived bitstreams

| SHA | Notable for |
|---|---|
| `893d43e0` | First build with the 0.9-monitor refactor (debug cone, ENABLE_*_LOGIC across 24 wrappers, DESC_MON_ENABLE_*_LOGIC cluster propagation) + the monbus beat-order swap. Confirmed alive via BUILD_ID = `STRC`; ran the 16desc_8ch_1MB workload that produced the compression handoff dataset (93.5% T1 hit, 2.66x ratio — see `reports/compression_dataset/`). |
| `a5da0fe1` | RFC Stage E option 1: descriptor-fetch monitor perf window surfaced to CSR (DAXMON_PERF_* @ 0x2D0-0x2F8). Timing closed at WNS +0.055 ns via the new `pblock_compressor` (compressor pinned to one clock region). Board-verified: a 1ch x 4desc x 4KB DMA produced productive=4 / beats=4 / bursts=4 / bytes=256 on the desc-fetch bus, matching cosim bit-for-bit (read via `host/read_desc_perf.py`). |
