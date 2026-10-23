# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Read the master-side observer's latency histograms (STREAM's own port).

fb_harness builds u_dma_observer with ENABLE_LATENCY_HIST=1 in every leg: per
transaction, AR->first R, AR->RLAST and AW->B, measured at STREAM's port, so
the figure is the fabric plus the endpoint plus any queueing behind other
masters. The histograms share the meters' measurement window, so a run's
latency and its bandwidth cover the same cycles.

Resolution: the hardware keeps 16 log2 bins and nothing else -- bin b counts
latencies in [2^b, 2^(b+1)) cycles (0 and 1 both land in bin 0, and the last bin
holds everything from 2^15 up). There is no sum, min or max, so a percentile is
reported as the bin's lower edge, and the mean is estimated from bin midpoints
and can be off by up to a factor of 1.5. It separates fabrics whose latency
differs by 2x, not by a few cycles; the exact zero-load cycle counts come from
sim.

sample_lost is the observer's HIST_SAMPLE_LOST sticky, reported but not
trusted: it is meant to say a timestamp FIFO was full when a command arrived,
but it sets on axi_perf_latency_hist's o_cmd_block, which is "the FIFO for
the channel on cmd_id is full" with no command qualifier. A one-channel STREAM
run fills channel 0's FIFO to exactly its outstanding limit and sets it with
nothing lost (bins and totals exact on the board, 2026-10-23). The columns are
left empty only when a histogram's bins do not sum to its total.
"""
import fb_map

NUM_BINS = 16
METRIC_BIN, METRIC_TOTAL = 9, 10      # OBS_STAT_SEL.METRIC ids for the histograms
# name -> (IS_WRITE, HIST_METRIC)
HISTS = {'rd_first': (0, 0), 'rd_last': (0, 1), 'wr_b': (1, 0)}


def _read(bridge, metric: int, is_write: int, bin_idx: int = 0, hist_metric: int = 0) -> int:
    fb_map.stream_host_path()
    from bus_meters import read_obs_stat
    return read_obs_stat(bridge, metric, is_write, bin_idx=bin_idx, hist_metric=hist_metric)


def read_hist(bridge, is_write: int, hist_metric: int) -> dict:
    bins = [_read(bridge, METRIC_BIN, is_write, b, hist_metric) for b in range(NUM_BINS)]
    return {'bins': bins, 'total': _read(bridge, METRIC_TOTAL, is_write, 0, hist_metric)}


def percentile_edge(bins: list, q: float):
    """Lower edge, in cycles, of the bin holding the q-quantile (0 for bin 0)."""
    n = sum(bins)
    if not n:
        return None
    seen = 0
    for b, c in enumerate(bins):
        seen += c
        if seen >= q * n:
            return 0 if b == 0 else 1 << b
    return 1 << (NUM_BINS - 1)


def mean_estimate(bins: list):
    """Mean from bin midpoints: bin 0 counts as 0.5, bin b as 1.5 * 2^b."""
    n = sum(bins)
    if not n:
        return None
    return sum(c * (0.5 if b == 0 else 1.5 * (1 << b)) for b, c in enumerate(bins)) / n


def read_latency(bridge) -> dict:
    """{'sample_lost': bool, <hist>: {'bins', 'total'}} for every HISTS entry."""
    fb_map.stream_host_path()
    from obs_addrs import O
    out = {name: read_hist(bridge, w, m) for name, (w, m) in HISTS.items()}
    out['sample_lost'] = bool((bridge.read(O("OBS_STICKY")) or 0) & 0x1)
    return out


def from_bins_text(text: str) -> list:
    """The *_bins CSV column back into counts."""
    return [int(x) for x in text.split()] if text else []


def columns(lat: dict) -> dict:
    """Flat CSV columns: per histogram n, p50, p90, p99 (bin lower edges) and
    the midpoint mean estimate, all in cycles; empty when a histogram's bins
    do not sum to its total."""
    cols = {'lat_sample_lost': lat['sample_lost']}
    for name in HISTS:
        h = lat[name]
        good = sum(h['bins']) == h['total']
        cols[f'{name}_n'] = h['total']
        for q, tag in ((0.5, 'p50'), (0.9, 'p90'), (0.99, 'p99')):
            cols[f'{name}_{tag}'] = percentile_edge(h['bins'], q) if good else None
        m = mean_estimate(h['bins']) if good else None
        cols[f'{name}_mean_est'] = round(m, 1) if m is not None else None
        cols[f'{name}_bins'] = ' '.join(map(str, h['bins']))
    return cols


COLUMNS = tuple(['lat_sample_lost'] + [f'{n}_{t}' for n in HISTS
                                       for t in ('n', 'p50', 'p90', 'p99', 'mean_est', 'bins')])
