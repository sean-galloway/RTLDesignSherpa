import time
import random
# import logging

# logging.basicConfig(level=logging.NOTSET)
# logger = logging.getLogger()
# logger.setLevel(logging.DEBUG)

class ConstrainedRandom():
    def __init__(self, constraints, weights, is_integer=True):
        if len(constraints) != len(weights):
            raise ValueError("Constraints and weights must have the same length")

        self.constraints = constraints
        self.weights = weights
        self.random_generator = random.Random()
        self.is_integer = is_integer


    def next(self):
        # Normalize weights to create a probability distribution
        total_weight = sum(self.weights)
        probabilities = [weight / total_weight for weight in self.weights]

        # Generate a random value based on weights
        selected_index = self.random_generator.choices(range(len(self.constraints)), probabilities)[0]

        # Generate a random number within the selected constraint
        min_value, max_value = self.constraints[selected_index]
        if self.is_integer:
            return self.random_generator.randint(min_value, max_value)
        else:
            return self.random_generator.uniform(min_value, max_value)


