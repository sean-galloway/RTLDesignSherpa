"""rapids-g live firmware load (rapids TASK-038), over the DUT's FW_* registers.

A FW_WRITABLE build's gatling instruction memory powers up holding the image
the bitstream was built with; this replaces it in both halves without a
rebuild:

    FW_CTRL  HOLD=1, ALG_MAX=<the image's>   harts held in reset
    FW_ADDR  0; FW_DATA x N                  the words (FW_ADDR advances)
    FW_ADDR  0; FW_RDATA x N                 read back, compared word for word
    FW_CTRL  HOLD=0, ALG_MAX kept            harts restart on the new image

Every channel must be idle (load before the first kick). The image is built
from a .S by the same generator the ROM include comes from
(projects/components/dma-ip/rapids/bin/gen_rapids_g_fw.py), so a source that
loads here is the source that later becomes the ROM. Its SHA-256 goes into the
results: once the memory is writable the bitstream no longer names the firmware.
"""

import hashlib
import os
import sys
from pathlib import Path

_REPO = Path(__file__).resolve().parents[7]
_FW_GEN_DIR = _REPO / 'projects' / 'components' / 'dma-ip' / 'rapids' / 'bin'
HALVES = ('src', 'snk')


def image_from_source(src: str) -> dict:
    """Assemble a firmware .S into {words, alg_max, sha256, source}."""
    sys.path.insert(0, str(_FW_GEN_DIR))
    try:
        import gen_rapids_g_fw as gen
    finally:
        sys.path.pop(0)
    tools = Path(os.environ.get('RISCV_TOOLCHAIN', gen.TOOLCHAIN_DEFAULT))
    if not (tools / 'riscv-none-elf-as').exists():
        raise RuntimeError(f"no riscv-none-elf-as in {tools} (set RISCV_TOOLCHAIN)")
    path = Path(src).resolve()
    words = gen.build_words(path, tools, need_ptab=True)
    blob = b''.join(w.to_bytes(4, 'little') for w in words)
    return {'source': str(path), 'words': words, 'alg_max': gen.alg_max(path),
            'sha256': hashlib.sha256(blob).hexdigest()}


def load(campaign, image: dict, halves=HALVES, out=print) -> dict:
    """Load image into each half's instruction memory; raise on any mismatch.
    Returns the record the results carry."""
    words, algs = image['words'], image['alg_max']
    for half in halves:
        if not campaign.read_field(half, 'FW_CTRL', 'WRITABLE'):
            raise RuntimeError(f"{half.upper()}: FW_CTRL.WRITABLE = 0 -- this bitstream's "
                               f"instruction memory is a ROM (build with FW_WRITABLE=1)")
    for half in halves:
        campaign.write_fields(half, 'FW_CTRL', HOLD=1, ALG_MAX=algs)
        campaign.write_reg(half, 'FW_ADDR', 0)
        for w in words:
            campaign.write_reg(half, 'FW_DATA', w)
        campaign.write_reg(half, 'FW_ADDR', 0)
        bad = [(i, w, r) for i, w in enumerate(words)
               for r in (campaign.read_reg(half, 'FW_RDATA'),) if r != w]
        if bad:
            i, w, r = bad[0]
            alias = [j for j, ww in enumerate(words) if ww == r][:4]
            raise RuntimeError(f"{half.upper()}: {len(bad)} of {len(words)} words read back wrong "
                               f"(first: word {i} wrote 0x{w:08X}, read 0x{r:08X}, which is word(s) {alias}; "
                               f"last bad {bad[-1][0]}); harts left held")
        campaign.write_fields(half, 'FW_CTRL', HOLD=0, ALG_MAX=algs)
        out(f"FW {half.upper()}: loaded {len(words)} words, read back, released "
            f"(ALG_MAX {algs}, sha256 {image['sha256'][:16]})")
    return {'loaded': True, 'source': image['source'], 'sha256': image['sha256'],
            'words': len(words), 'alg_max': algs, 'halves': list(halves)}


CH_ERROR = 0x20          # rapids_pkg::CH_ERROR, one-hot [5] of CH_STATEn.STATE
CH_IDLE = 0x01


def _states(campaign, half):
    return [campaign.read_field(half, f'CH_STATE{c}_STATE', 'STATE') for c in range(campaign.num_channels)]


def selftest(campaign, image: dict, out=print) -> list:
    """Prove the load path end to end, then leave `image` loaded and every
    channel idle. Returns [{check, ok, detail}]; the caller fails on any
    not-ok. Every channel must be idle (run it before the first kick).

      refused  a FW_DATA write with HOLD = 0 leaves the memory unchanged
      takes    a one-word image of 0x00000000 (an illegal instruction) halts
               every hart, so every channel goes to CH_ERROR -- the harts run
               what was loaded, not the build's image
      restores loading `image` and pulsing CHANNEL_RESET brings every channel
               back to CH_IDLE
    On a ROM build (FW_CTRL.WRITABLE = 0) it checks the opposite instead: a
    held zero write changes nothing and every channel stays idle."""
    checks = []

    def check(name, ok, detail):
        checks.append({'check': name, 'ok': bool(ok), 'detail': detail})
        out(f"FW SELFTEST {name}: {'ok' if ok else 'FAIL'} ({detail})")

    writable = [campaign.read_field(h, 'FW_CTRL', 'WRITABLE') for h in HALVES]
    if not any(writable):
        # A ROM build: the same writes, held, must change nothing -- no hart is
        # held or halted, so every channel stays idle, and FW_RDATA reads 0
        for half in HALVES:
            campaign.write_fields(half, 'FW_CTRL', HOLD=1, ALG_MAX=image['alg_max'])
            campaign.write_reg(half, 'FW_ADDR', 0)
            campaign.write_reg(half, 'FW_DATA', 0x00000000)
            campaign.write_reg(half, 'FW_ADDR', 0)
            rd = campaign.read_reg(half, 'FW_RDATA')
            campaign.write_fields(half, 'FW_CTRL', HOLD=0, ALG_MAX=0)
            st = _states(campaign, half)
            check(f'{half}_rom_ignores', rd == 0 and all(x == CH_IDLE for x in st),
                  f"FW_RDATA 0x{rd:08X}, CH_STATE {[hex(x) for x in st]} after a held zero write")
        campaign.fw_record = {'loaded': False, 'rom': True, 'selftest': checks}
        return checks
    if not all(writable):
        check('writable', False, f"FW_CTRL.WRITABLE src/snk = {writable}")
        return checks

    for half in HALVES:
        campaign.write_reg(half, 'FW_ADDR', 0)
        w0 = campaign.read_reg(half, 'FW_RDATA')
        campaign.write_reg(half, 'FW_ADDR', 0)
        campaign.write_reg(half, 'FW_DATA', w0 ^ 0xFFFFFFFF)
        campaign.write_reg(half, 'FW_ADDR', 0)
        r0 = campaign.read_reg(half, 'FW_RDATA')
        check(f'{half}_refused', r0 == w0, f"word 0 0x{w0:08X} -> 0x{r0:08X} after an unheld write")
    load(campaign, {'source': 'selftest-halt', 'words': [0x00000000], 'alg_max': image['alg_max'],
                    'sha256': 'selftest-halt'}, out=out)
    for half in HALVES:
        st = _states(campaign, half)
        check(f'{half}_takes', all(x == CH_ERROR for x in st), f"CH_STATE {[hex(x) for x in st]}")
    try:
        rec = load(campaign, image, out=out)
    except RuntimeError as exc:          # keep going: the probes below say where
        check('load', False, str(exc))
        rec = {'loaded': False, 'source': image['source'], 'sha256': image['sha256']}
    # Direct addressing across the memory, not only the run from 0: each probe
    # sets FW_ADDR, reads FW_RDATA and reads FW_ADDR back (it advanced by one)
    n = len(image['words'])
    for half in HALVES:
        probes = []
        for a in sorted({0, min(511, n - 1), min(512, n - 1), min(513, n - 1), n - 1}):
            campaign.write_reg(half, 'FW_ADDR', a)
            r = campaign.read_reg(half, 'FW_RDATA')
            probes.append((a, r, campaign.read_field(half, 'FW_ADDR', 'ADDR'), r == image['words'][a]))
        check(f'{half}_addressing', all(p[3] for p in probes),
              '; '.join(f"[{a}] 0x{r:08X} addr->{nx}{'' if ok else ' WRONG'}" for a, r, nx, ok in probes))
    campaign.reset_channels()
    for half in HALVES:
        st = _states(campaign, half)
        check(f'{half}_restores', all(x == CH_IDLE for x in st), f"CH_STATE {[hex(x) for x in st]}")
    campaign.fw_record = dict(rec, selftest=checks)
    return checks


def expect(campaign, image: dict, sample: int = 8, out=print) -> dict:
    """A simulation built with this image compiled in (the DV runner's
    TEST_FW_IMAGE), where a full load does not fit a chunk: read back the
    first and last `sample` words of each half and compare, and record the
    image as preloaded. Needs a FW_WRITABLE build (a ROM build reads 0)."""
    words = image['words']
    runs = [(0, min(sample, len(words))), (max(0, len(words) - sample), len(words))]
    for half in HALVES:
        if not campaign.read_field(half, 'FW_CTRL', 'WRITABLE'):
            raise RuntimeError(f"{half.upper()}: FW_CTRL.WRITABLE = 0 -- --fw-expect needs a FW_WRITABLE build")
        for lo, hi in runs:
            campaign.write_reg(half, 'FW_ADDR', lo)
            for i in range(lo, hi):
                r = campaign.read_reg(half, 'FW_RDATA')
                if r != words[i]:
                    raise RuntimeError(f"{half.upper()}: the compiled-in image is not {image['source']} "
                                       f"(word {i}: 0x{r:08X} != 0x{words[i]:08X})")
        out(f"FW {half.upper()}: compiled-in image matches words {runs} "
            f"(sha256 {image['sha256'][:16]})")
    return {'loaded': False, 'preloaded': True, 'source': image['source'], 'sha256': image['sha256'],
            'words': len(words), 'alg_max': image['alg_max'], 'sampled': runs}
