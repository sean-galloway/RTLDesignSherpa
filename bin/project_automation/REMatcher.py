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
