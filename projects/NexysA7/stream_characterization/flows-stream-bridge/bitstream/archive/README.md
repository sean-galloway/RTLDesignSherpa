# Bitstream archive

Each `.bit` file is named `<commit_sha>.bit` — a known-good build snapshot.
The latest working build is the one with the most recent commit-sha file.

To reuse a known-good bitstream instead of rebuilding (saves ~25 min):
```
cp bitstream/archive/<sha>.bit bitstream/stream_char.bit
cd ../flows-stream-bridge && make program
```

Convention: archive the bit ONLY AFTER UART ping confirms the design is alive.
