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
