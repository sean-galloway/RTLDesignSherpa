// apps.js -- launcher tile data + renderer for the root app picker.
// Adding a new app = one entry in APPS plus a workflow staging line.
var LAUNCHER_APPS = [
  {
    id: 'ddr_drills',
    name: 'DDR and HBM Drills',
    href: 'ddr_drills/',
    blurb: 'Memory-controller training: quizzes, timing parameters, and AXI walkthroughs for 11 memory technologies'
  },
  {
    id: 'fifo_depth',
    name: 'FIFO Depth Calculator',
    href: 'fifo/',
    blurb: 'Worst-case async FIFO sizing with synchronizer margin and Gray/Johnson depth output'
  },
  {
    id: 'mtbf_calc',
    name: 'MTBF Calculator',
    href: 'mtbf_calc/',
    blurb: 'Metastability MTBF vs synchronizer stages, clock/data rates, and resolution time -- why two flops fail at 1 GHz'
  },
  {
    id: 'fifo_flags',
    name: 'FIFO Flag Generator',
    href: 'fifo_flags/',
    blurb: 'Async FIFO almost-full/almost-empty thresholds from depth, clock ratio, and bubble tolerance'
  },
  {
    id: 'slack_explorer',
    name: 'Slack & Pipelining Explorer',
    href: 'slack_explorer/',
    blurb: 'Setup/hold slack vs clock skew, plus the latency-vs-throughput tradeoff when pipelining a path'
  },
  {
    id: 'qformat_explorer',
    name: 'Q-Format Explorer',
    href: 'qformat_explorer/',
    blurb: 'Fixed-point Qm.n bit patterns, signed/unsigned modes, quantization error, and wrap vs saturate'
  },
  {
    id: 'cdc_drill',
    name: 'CDC Drill',
    href: 'cdc_drill/',
    blurb: 'Clock-domain-crossing drill: spot the illegal crossing, then pick the right synchronizer'
  },
  {
    id: 'crc_calc',
    name: 'CRC Calculator',
    href: 'crc_calc/',
    blurb: 'CRC-8/16/32 with preset and custom polynomials, standard check strings, and a shift-register step view'
  },
  {
    id: 'cache_sim',
    name: 'Cache Simulator',
    href: 'cache_sim/',
    blurb: 'Trace-driven cache simulator: sets/ways/block size, LRU/FIFO/RANDOM replacement, and the compulsory/capacity/conflict miss split'
  }
];

(function () {
  'use strict';

  if (typeof document === 'undefined') { return; }

  document.addEventListener('DOMContentLoaded', function () {
    var host = document.getElementById('tiles');
    if (!host) { return; }
    var html = '';
    LAUNCHER_APPS.forEach(function (a) {
      html += '<a class="tile" href="' + a.href + '">' +
              '<span class="tile-name">' + a.name + '</span>' +
              '<span class="tile-blurb">' + a.blurb + '</span></a>';
    });
    host.innerHTML = html;
  });
})();

if (typeof module !== 'undefined' && module.exports) {
  module.exports = LAUNCHER_APPS;
}
