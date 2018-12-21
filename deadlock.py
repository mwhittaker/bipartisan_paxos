from collections import defaultdict
from itertools import islice, chain, combinations, combinations_with_replacement, permutations, product
from multiprocessing import cpu_count, Pool, Process, Queue
import math
import operator as op
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
    next_conflict = global_ordering[0].next_conflict(command)
    deps_count = defaultdict(int)
    for ordering in global_ordering:
        deps_count[ordering.deps(command)] += 1
    for (deps, count) in deps_count.items():
        if (count >= majority_size(len(global_ordering)) and
            next_conflict not in deps and
            any(next_conflict in d for (d, c) in deps_count.items())):
            return True
    return False

def is_global_ordering_deadlocked(global_ordering):
    return all(exists_majority_dep(global_ordering, command)
               for command in global_ordering[0].commands)

def ncr(n, r):
    """https://stackoverflow.com/a/4941932/3187068"""
    r = min(r, n-r)
    numer = reduce(op.mul, range(n, n-r, -1), 1)
    denom = reduce(op.mul, range(1, r+1), 1)
    return numer / denom

def deadlock_possible(queue, num_replicas, num_commands):
    print("num_replicas={} num_commands={}".format(num_replicas, num_commands))
    global_orderings = combinations_with_replacement(
        Ordering.permutations(num_commands), num_replicas)

    i = 0
    total = ncr(num_replicas + math.factorial(num_commands) - 1, num_replicas)
    batch_size = 10000
    for global_ordering_batch in batch(global_orderings, batch_size):
        queue.put(global_ordering_batch)
        i += batch_size
        if (i % 100000) == 0:
            print("{}/{}".format(i, total))

def batch(iterable, size):
    sourceiter = iter(iterable)
    while True:
        batchiter = islice(sourceiter, size)
        yield chain([batchiter.next()], batchiter)

class Worker(Process):
    def __init__(self, queue):
        self.queue = queue
        super(Worker, self).__init__()

    def run(self):
        global_ordering_batch = self.queue.get()
        while global_ordering_batch:
            for global_ordering in global_ordering_batch:
                if is_global_ordering_deadlocked(global_ordering):
                    print(global_ordering)
            global_ordering_batch = self.queue.get()

def main():
    # Start the workers.
    queue = Queue(maxsize=cpu_count())
    workers = [Worker(queue) for _ in range(cpu_count())]
    for worker in workers:
        worker.start()

    # Dish out work to the workers.
    for num_commands in range(5, 6):
        for num_replicas in range(6, 7):
            deadlock_possible(queue, num_replicas, num_commands)

    # Wait for the workers.
    for _ in range(cpu_count()):
        queue.put(None)
    for worker in workers:
        worker.join()

if __name__ == '__main__':
    main()
