# REMatcher

This code defines a `REMatcher` class in Python for simplifying the use of regular expressions by providing an easy-to-use interface for matching strings and retrieving parts of the match. It is useful as it abstracts the complexity of Python's `re` module and makes regex operations more akin to how Perl handles them.
![REMatcher UML](../../images_scripts_uml/ProjAuto_REMatcherClass.svg)

The class has two main methods:

- `match()`, which guards against running match operations without having a valid regex pattern by returning a boolean indicator.
- `group()`, which allows safe retrieval of matching groups with error handling in case of no matches.

**Note**: The `REMatcher` class is dependent on the `re` module from Python's standard library.

**File Location**: `project_automation/REMatcher.py`.

**Command Line Options**: This class is not designed to be executed directly from the command line but utilized as part of a larger Python project.

**Example Usage**:

```python
m = REMatcher(line)
if m.match(r'.*TESTS=(\d+) PASS=(\d+) FAIL=(\d+) SKIP=(\d+).*'):
    tests_tot = int(m.group(1))
    tests_pass = int(m.group(2))
    tests_fail = int(m.group(3))
    tests_skip = int(m.group(4))
```

---

[Back to Scripts Index](index.md)
