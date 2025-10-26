# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: REMatcher
# Purpose: Rematcher implementation
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

import re

class REMatcher(object):
    ''' This is a utility function to help out with matching regex's and
        grabbing the matches out in a way that is similar to how perl
        does it.
    '''
    def __init__(self, matchstring: str) -> None:
        self.matchstring = matchstring

    def match(self, regexp: str) -> bool:
        self.rematch = re.match(regexp, self.matchstring,
                                re.IGNORECASE |
                                re.MULTILINE |
                                re.DOTALL
                                )
        return bool(self.rematch)

    def group(self, i: int) -> str:
        return "Error 999" if self.rematch is None else self.rematch.group(i)
