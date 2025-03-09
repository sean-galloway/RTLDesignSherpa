import cocotb
from cocotb_coverage.crv import Randomized
import random

class DelayRandomizer(Randomized):
    def __init__(self, constraints):
        super().__init__()
        self.constraints = constraints

        # Initialize attributes for each delay
        for delay_name in self.constraints.keys():
            setattr(self, delay_name, 0)
            self.add_rand(delay_name, self._get_full_range(self.constraints[delay_name][0]))


    def _get_full_range(self, bins):
        full_range = []
        for bin_range in bins:
            full_range.extend(range(bin_range[0], bin_range[1] + 1))
        return full_range


    def apply_constraints(self):
        for delay_name, (bins, weights) in self.constraints.items():
            choice = random.choices(bins, weights)[0]
            value = random.randint(choice[0], choice[1])
            setattr(self, delay_name, value)


    def set_constrained_random(self):
        self.randomize()
        self.apply_constraints()
        return {delay_name: getattr(self, delay_name) for delay_name in self.constraints.keys()}
