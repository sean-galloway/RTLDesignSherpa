#==============================================================================
# filelist_utils.tcl — expand a repo-style `.f` filelist for Vivado
#==============================================================================
# Used by create_project.tcl. Understands:
#   - Environment-variable substitution ($REPO_ROOT, $STREAM_ROOT, ...)
#   - `+incdir+` prefixes for include paths
#   - `-f <other.f>` nested filelist includes
#   - `#` line comments
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

    # Parse one filelist, return {sources include_dirs defines}.
    proc read_filelist {path} {
        variable seen_files
        set path [file normalize $path]
        if {[info exists seen_files($path)]} {
            return {{} {} {}}
        }
        set seen_files($path) 1

        set sources {}
        set incdirs {}
        set defines {}

        set fh [open $path r]
        set raw [read $fh]
        close $fh

        foreach line [split $raw "\n"] {
            set line [string trim $line]
            if {$line eq "" || [string index $line 0] eq "#"} { continue }

            # Strip trailing inline comments
            set hash_idx [string first "#" $line]
            if {$hash_idx >= 0} {
                set line [string trim [string range $line 0 [expr {$hash_idx - 1}]]]
            }
            if {$line eq ""} { continue }

            set expanded [_expand_env $line]

            if {[string match "+incdir+*" $expanded]} {
                lappend incdirs [file normalize [string range $expanded 8 end]]
                continue
            }
            if {[string match "+define+*" $expanded]} {
                lappend defines [string range $expanded 8 end]
                continue
            }
            if {[string match "-f*" $expanded] || [string match "-F*" $expanded]} {
                set nested [string trim [string range $expanded 2 end]]
                set nested [file normalize $nested]
                lassign [read_filelist $nested] ns ni nd
                set sources [concat $sources $ns]
                set incdirs [concat $incdirs $ni]
                set defines [concat $defines $nd]
                continue
            }
            # Otherwise, treat as a source file path.
            lappend sources [file normalize $expanded]
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
