pie 's/\s+$/\n/' *.py
pie 's/^(\s+)(tb|self)\.(log|logger)\.(info|debug|warning|error)\((f.*)\)/$1msg = $5\n$1$2.$3.$4(msg)/' *.py
pie 's/cocotb.test\(\)/cocotb.test(timeout_time=1, timeout_unit="ms")/' *.py
pie 's/cocotb.test\(\)/cocotb.test(timeout_time=1, timeout_unit="ms")/' *.py

pie 's/async def assert_reset/def assert_reset/' *.py
pie 's/await tb.assert_reset\(\)/tb.assert_reset()/' *.py

pie 's/async def clear_interface/def clear_interface/' *.py
pie 's/await tb.clear_interface\(\)/tb.clear_interface()/' *.py

pie 's/async def deassert_reset/def deassert_reset/' *.py
pie 's/await tb.deassert_reset\(\)/tb.deassert_reset()/' *.py

