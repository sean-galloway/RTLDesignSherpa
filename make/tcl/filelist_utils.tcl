#==============================================================================
# filelist_utils.tcl — expand a repo-style `.f` filelist for Vivado / Quartus
#==============================================================================
# THE ONE Tcl expander (tooling TASK-019, 2026-09-29). It used to exist as
# eight per-flow copies, seven of which did not treat `//` as a comment while
# the filelists and the Python expander (bin/TBClasses/shared/filelist_utils.py
# via bin/FileFolderFunctions/file_list_processor.py) did -- so a `// heading`
# line came back as a source path. Every flow now sources this file:
#
#   set rds_root [expr {[info exists ::env(REPO_ROOT)] ? $::env(REPO_ROOT)
#                       : [string trim [exec git -C $script_dir rev-parse --show-toplevel]]}]
#   source "$rds_root/make/tcl/filelist_utils.tcl"
#
# bin/tests/test_filelist_utils_tcl.py pins that this and the Python expander
# agree on the same filelist. Understands:
#   - Environment-variable substitution ($REPO_ROOT, $STREAM_ROOT, ...)
#   - `+incdir+` prefixes for include paths
#   - `-f <other.f>` nested filelist includes
#   - `#` and `//` line comments (and trailing inline comments)
#==============================================================================

namespace eval filelist {
    variable seen_files

    proc _expand_env {line} {
        # Expand ${NAME} first (so e.g. "${STREAM_CHAR_ROOT}foo" works),
        # then plain $NAME. Each match is replaced with the env value directly.
        while {[regexp {\$\{([A-Za-z_][A-Za-z0-9_]*)\}} $line _ name]} {
            if {![info exists ::env($name)]} {
                error "filelist: environment variable '$name' is not set"
            }
            regsub "\\\$\\{$name\\}" $line $::env($name) line
        }
        while {[regexp {\$([A-Za-z_][A-Za-z0-9_]*)} $line _ name]} {
            if {![info exists ::env($name)]} {
                error "filelist: environment variable '$name' is not set"
            }
            regsub "\\\$$name\\y" $line $::env($name) line
        }
        return $line
    }

    # Resolve a (possibly relative) path against `base_dir`.
    # Absolute paths and $REPO_ROOT-anchored paths come back unchanged.
    proc _resolve_relative {raw base_dir} {
        if {[file pathtype $raw] eq "absolute"} {
            return [file normalize $raw]
        }
        return [file normalize [file join $base_dir $raw]]
    }

    # Parse one filelist, return {sources include_dirs defines}.
    proc read_filelist {path} {
        variable seen_files
        set path [file normalize $path]
        if {[info exists seen_files($path)]} {
            return {{} {} {}}
        }
        set seen_files($path) 1

        # Anchor for any bare relative path inside this filelist. Match the
        # cocotb-side filelist_utils.py, which uses `dirname(dirname(path))`
        # — i.e. `<rtl>/filelists/foo.f` → relative paths root at `<rtl>/`.
        # Without this, Tcl's `[file normalize]` resolves bare paths against
        # the launching CWD (e.g. flows-stream-bridge/) and fails to find
        # generated bridge files that actually live under
        # stream_char_framework/rtl/bridges/generated/.
        set filelist_dir   [file dirname $path]
        set rel_path_base  [file dirname $filelist_dir]

        set sources {}
        set incdirs {}
        set defines {}

        set fh [open $path r]
        set raw [read $fh]
        close $fh

        foreach line [split $raw "\n"] {
            set line [string trim $line]
            if {$line eq "" || [string index $line 0] eq "#"} { continue }
            # `//` is a comment too -- the repo's filelists use it (char_top.f
            # is written that way), and the cocotb-side expander treats it so.
            # Until 2026-09-29 this parser did not, and every `// heading`
            # line came back as a source path beginning with "/ ".
            if {[string range $line 0 1] eq "//"} { continue }

            # Strip trailing inline comments (`#` or `//`)
            set hash_idx [string first "#" $line]
            if {$hash_idx >= 0} {
                set line [string trim [string range $line 0 [expr {$hash_idx - 1}]]]
            }
            set slash_idx [string first "//" $line]
            if {$slash_idx >= 0} {
                set line [string trim [string range $line 0 [expr {$slash_idx - 1}]]]
            }
            if {$line eq ""} { continue }

            set expanded [_expand_env $line]

            if {[string match "+incdir+*" $expanded]} {
                set inc [string range $expanded 8 end]
                lappend incdirs [_resolve_relative $inc $rel_path_base]
                continue
            }
            if {[string match "+define+*" $expanded]} {
                lappend defines [string range $expanded 8 end]
                continue
            }
            if {[string match "-f*" $expanded] || [string match "-F*" $expanded]} {
                set nested [string trim [string range $expanded 2 end]]
                set nested [_resolve_relative $nested $rel_path_base]
                lassign [read_filelist $nested] ns ni nd
                set sources [concat $sources $ns]
                set incdirs [concat $incdirs $ni]
                set defines [concat $defines $nd]
                continue
            }
            # Otherwise, treat as a source file path.
            lappend sources [_resolve_relative $expanded $rel_path_base]
        }

        return [list $sources $incdirs $defines]
    }

    proc flatten {path} {
        variable seen_files
        array unset seen_files
        lassign [read_filelist $path] sources incdirs defines
        return [list [lsort -unique $sources] [lsort -unique $incdirs] [lsort -unique $defines]]
    }
}
