# TASK-011: 15 rapids .sv files carry a `// Module:` header that contradicts their own filename

**Priority:** P2. This is the ROOT CAUSE of the doc naming drift, so it recurs
until fixed.
**Status:** open 2026-09-26. The rapids session verified the count independently
and is tracking it their side; filed here so it survives that session ending.

**Measured** across `projects/components/dmas/rapids/rtl`: 28 files carry a
`// Module:` header, **17 disagreed** with their filename; 15 remain after
`bdf4e0dff` deleted two.

```
alloc_ctrl_beats.sv              header says  beats_alloc_ctrl
drain_ctrl_beats.sv                           beats_drain_ctrl
latency_bridge_beats.sv                       beats_latency_bridge
scheduler_beats.sv                            scheduler
scheduler_group_beats.sv                      beats_scheduler_group
scheduler_group_array_beats.sv                beats_scheduler_group_array
axi_read_engine_beats.sv                      axi_read_engine
axi_write_engine_beats.sv                     axi_write_engine
descriptor_engine_beats.sv                    descriptor_engine
snk_data_path_beats.sv                        sink_data_path
src_data_path_beats.sv                        source_data_path
snk_data_path_axis_beats.sv                   sink_data_path_axis
src_data_path_axis_beats.sv                   source_data_path_axis
snk_data_path_axis_test_beats.sv              sink_data_path_axis_test
src_data_path_axis_test_beats.sv              source_data_path_axis_test
```

**Why it matters beyond tidiness.** The MAS book's 17 wrong `**Module:**`
declarations (fixed in `fcd940777`) were not invented -- they were COPIED from
these headers. Every future doc pass re-derives the wrong name from the same
source. It also defeated four rounds of automated attribution: pages resolved to
STREAM's identically-named modules or to nothing, producing 32 then 53 confident
false findings, all withdrawn.

**Repro, one command:**

```bash
python3 - <<'EOF'
import os,re
for d,_,fs in os.walk('projects/components/dmas/rapids/rtl'):
    for fn in sorted(f for f in fs if f.endswith('.sv')):
        m=re.search(r'^//\s*Module:\s*(\S+)', open(os.path.join(d,fn)).read(), re.M)
        if m and m.group(1).removesuffix('.sv') != fn.removesuffix('.sv'):
            print(fn, '->', m.group(1))
EOF
```

**Note on counting:** an earlier report said 22. That was a bug in the measuring
script -- `rstrip('.sv')` strips a CHARACTER SET, so the trailing `s` of every
`_beats` name was eaten and 5 correctly-named files compared unequal. Use
`removesuffix`. 17 (now 15) is right.

**Scope:** `.sv` headers only. No port, logic or filename changes.

**Related:** [[TASK-007]]
