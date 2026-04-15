// Formal-friendly version of monitor_pkg
// sv2v cannot handle typedef re-exports that duplicate identifiers from sub-packages.
// This minimal wrapper just makes `import monitor_pkg::*` resolve without error,
// delegating everything to the sub-packages.

package monitor_pkg;
    // Just bring everything into scope - no re-definitions
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
    import monitor_amba5_pkg::*;
    import monitor_arbiter_pkg::*;
endpackage : monitor_pkg
