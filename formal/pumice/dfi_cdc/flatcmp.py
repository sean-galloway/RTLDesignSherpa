#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# flatcmp.py -- byte-compare two generated flats, ignoring the repo-root
# prefix baked into sv2v's elaboration-$display strings. Uses exactly the
# normalization bin/formal_status.py --check-flats uses, so this block's
# house check-flat target agrees with the repo-wide sweep (which regenerates
# with REPO_ROOT pointed at a canonical symlink, /tmp/rds-canonical-repo-root).

import re
import sys

ROOT_PREFIX = re.compile(
    r"(?:/[^\s'\"]*)+/(?=(?:rtl|projects|formal|bin|docs|vault|\.github)(?:/|\b))"
)


def norm(path):
    with open(path) as f:
        return ROOT_PREFIX.sub("$REPO_ROOT/", f.read())


sys.exit(0 if norm(sys.argv[1]) == norm(sys.argv[2]) else 1)
