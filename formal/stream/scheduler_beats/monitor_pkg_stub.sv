// SPDX-License-Identifier: MIT
// Empty stub for monitor_pkg - satisfies `import monitor_pkg::*` in rapids_imports.svh
// without re-exporting create_monitor_packet (which causes sv2v ambiguity with
// monitor_common_pkg). All needed symbols come from the individual protocol packages.
package monitor_pkg;
endpackage
