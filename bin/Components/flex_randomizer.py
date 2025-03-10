from cocotb_coverage.crv import Randomized
import random

class FlexRandomizer(Randomized):
    """Randomizes delays based on specified constraints.

    This class allows for constrained randomization of delays, ensuring
    that generated values fall within specified ranges and distributions.
    """
    def __init__(self, constraints):
        """Initialize the DelayRandomizer with delay constraints.

        Args:
            constraints (dict): A dictionary defining the constraints for each delay.
                The keys are the names of the delays, and the values are tuples containing
                a list of bins (ranges) and a list of weights for each bin.
        """
        super().__init__()
        self.constraints = constraints

        # Initialize attributes for each delay
        for delay_name in self.constraints.keys():
            setattr(self, delay_name, 0)
            self.add_rand(delay_name, self._get_full_range(self.constraints[delay_name][0]))

    def _get_full_range(self, bins):
        """Generate a full range of values from a list of bins.

        Args:
            bins (list): A list of bins, where each bin is a tuple specifying a range.

        Returns:
            list: A list containing all the values within the specified bins.
        """
        full_range = []
        for bin_range in bins:
            full_range.extend(range(bin_range[0], bin_range[1] + 1))
        return full_range

    def _apply_constraints(self):
        """next gets the next batch of randomized numbers"""
        for delay_name, (bins, weights) in self.constraints.items():
            choice = random.choices(bins, weights)[0]
            value = random.randint(choice[0], choice[1])
            setattr(self, delay_name, value)

    def next(self):
        """Generate and set constrained random values for the delays.

        Returns:
            dict: A dictionary containing the generated random values for each delay.
        """
        self.randomize()
        self._apply_constraints()
        return {delay_name: getattr(self, delay_name) for delay_name in self.constraints.keys()}
