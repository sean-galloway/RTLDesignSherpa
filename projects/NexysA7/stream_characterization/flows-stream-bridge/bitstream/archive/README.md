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
