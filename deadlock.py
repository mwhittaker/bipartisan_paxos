from itertools import combinations, combinations_with_replacement, permutations, product
import math

class Ordering(object):
    def __init__(self, n, commands=None):
        self.n = n
        self.commands = commands or tuple(range(n))
        self.commands = tuple(self.commands)

    def __str__(self):
        return str(self.commands)

    def __repr__(self):
        return str(self)

    def deps(self, command):
        conflicts = {self.next_conflict(command), self.prev_conflict(command)}
        prefix = self.commands[:self.commands.index(command)]
        return frozenset([c for c in prefix if c in conflicts])

    def next_conflict(self, cmd):
        return (cmd + 1) % self.n

    def prev_conflict(self, cmd):
        return (cmd - 1) % self.n

    @staticmethod
    def permutations(n):
        for permutation in permutations(range(n)):
            yield Ordering(n, permutation)

def majority_size(n):
    return int(math.floor(float(n) / 2) + 1)

def exists_majority_dep(global_ordering, command):
    majority_orderings = combinations(
        global_ordering, majority_size(len(global_ordering)))
    for majority_ordering in majority_orderings:
        all_deps = {ordering.deps(command) for ordering in majority_ordering}
        if len(all_deps) == 1:
            deps = list(all_deps)[0]
            if global_ordering[0].next_conflict(command) not in deps:
                return True
    return False

def is_global_ordering_deadlocked(global_ordering):
    return all(exists_majority_dep(global_ordering, command)
               for command in global_ordering[0].commands)

def deadlock_possible(num_replicas, num_commands):
    global_orderings = combinations_with_replacement(
        Ordering.permutations(num_commands), num_replicas)
    for global_ordering in global_orderings:
        if is_global_ordering_deadlocked(global_ordering):
            return global_ordering
    return None

def main():
    for num_commands in range(2, 6):
        for num_replicas in range(3, 6):
            print("Checking {} commands and {} replicas."
                  .format(num_commands, num_replicas))
            global_ordering = deadlock_possible(num_replicas, num_commands)
            if global_ordering:
                print("num_replicas = " + str(num_replicas))
                print("num_commands = " + str(num_commands))
                print(global_ordering)
                print("")

if __name__ == '__main__':
    main()
