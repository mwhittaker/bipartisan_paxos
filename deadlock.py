from itertools import combinations, combinations_with_replacement, permutations, product
from multiprocessing import cpu_count, Pool, Process, Queue
import math
import os

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
        majority_deps = {ordering.deps(command) for ordering in majority_ordering}
        all_deps = {ordering.deps(command) for ordering in global_ordering}
        if len(majority_deps) == 1:
            deps = list(majority_deps)[0]
            if (global_ordering[0].next_conflict(command) not in deps and
                any(global_ordering[0].next_conflict(command) in deps
                    for deps in all_deps)):
                return True
    return False

def is_global_ordering_deadlocked(global_ordering):
    return all(exists_majority_dep(global_ordering, command)
               for command in global_ordering[0].commands)

def deadlock_possible(queue, num_replicas, num_commands):
    print("num_replicas={} num_commands={}".format(num_replicas, num_commands))
    global_orderings = combinations_with_replacement(
        Ordering.permutations(num_commands), num_replicas)
    for global_ordering in global_orderings:
        queue.put(global_ordering)

class Worker(Process):
    def __init__(self, queue):
        self.queue = queue
        super(Worker, self).__init__()

    def run(self):
        global_ordering = self.queue.get()
        while global_ordering:
            if is_global_ordering_deadlocked(global_ordering):
                print(global_ordering)
            global_ordering = self.queue.get()

def main():
    # Start the workers.
    queue = Queue(maxsize=cpu_count())
    workers = [Worker(queue) for _ in range(cpu_count())]
    for worker in workers:
        worker.start()

    # Dish out work to the workers.
    for num_commands in range(3, 7):
        for num_replicas in range(3, 7):
            deadlock_possible(queue, num_replicas, num_commands)

    # Wait for the workers.
    for _ in cpu_count():
        queue.put(None)
    for worker in workers:
        worker.join()

if __name__ == '__main__':
    main()
