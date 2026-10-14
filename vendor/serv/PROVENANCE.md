# PROVENANCE — vendor/serv

Vendored copy of the SERV RISC-V core, used by the HIVE subsystem
(`projects/components/compute-eng-ip/hive-serv`) as the per-tile monitor core.

- **Upstream:** https://github.com/olofk/serv
- **Version:** 1.4.0 (git tag `1.4.0`, commit `7d9cde4e6ca4f4c84d7512a752a4c187537dd373`)
- **Vendored:** 2026-10-13
- **License:** ISC (see `LICENSE`; compatible with the repo MIT license)
- **Kept:** `rtl/` (the core, Verilog-2005), `serv.core` (FuseSoC core
  description, useful metadata), upstream `README.md`/`NEWS`
- **Dropped:** FuseSoC/Zephyr/wrapper/bench trees (`.git`, `bench/`,
  `servant/`, `servile/`, `serving/`, `sw/`, `zephyr/`, `verif/`, `doc/`,
  `data/`, `west.yml`) — HIVE wraps the core directly.

## Update procedure

```bash
cd vendor/serv
rm -rf /tmp/serv-up && git clone --depth 1 --branch <new-tag> https://github.com/olofk/serv /tmp/serv-up
rsync -a --delete /tmp/serv-up/ ./ && rm -rf .git bench data doc servant servant.core servile servile.core serving serving.core sw west.yml zephyr verif
# bump the version/commit lines above, then re-run the hive serv_monitor tests
```

Interface reference for the wrapper: see `rtl/serv_top.v` (i_ibus/dbus
cmd/rsp pairs, `i_timer_irq`, RISC-V external debug port optional).
