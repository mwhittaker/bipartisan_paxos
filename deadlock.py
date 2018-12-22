from collections import defaultdict
from multiprocessing import cpu_count, Pool, Process, Queue
from typing import DefaultDict, FrozenSet, Iterable, Iterator, Tuple, TypeVar
import itertools
import math
import operator as op
import os

Command = int
Ordering = Tuple[Command, ...]
GlobalOrdering = Tuple[Ordering, ...]


T = TypeVar('T')
def batched(iterable: Iterable[T], size: int) -> Iterator[Tuple[T, ...]]:
    """https://docs.python.org/3/library/itertools.html#recipes"""
    args = [iter(iterable)] * size
    return itertools.zip_longest(*args, fillvalue=None)


def prod(xs: Iterable[int]) -> int:
    p = 1
    for x in xs:
        p *= x
    return p


def choose(n: int, r: int) -> int:
    """https://stackoverflow.com/a/4941932/3187068"""
    r = min(r, n-r)
    numer = prod(range(n, n-r, -1))
    denom = prod(range(1, r+1))
    return int(numer / denom)


def majority_size(n: int) -> int:
    return int(math.floor(n / 2) + 1)


class Ord(object):
    @staticmethod
    def all(n: int) -> Iterator[Ordering]:
        for permutation in itertools.permutations(range(n)):
            yield permutation

    @staticmethod
    def num(num_commands: int) -> int:
        return math.factorial(num_commands)

    @staticmethod
    def next_conflict(n: int, cmd: Command):
        return (cmd + 1) % n

    @staticmethod
    def prev_conflict(n: int, cmd: Command):
        return (cmd - 1) % n

    @staticmethod
    def deps(ordering: Ordering, cmd: Command) -> FrozenSet[Command]:
        n = len(ordering)
        conflicts = {
            Ord.next_conflict(n, cmd),
            Ord.prev_conflict(n, cmd),
        }
        prefix = ordering[:ordering.index(cmd)]
        return frozenset([c for c in prefix if c in conflicts])

class GlobalOrd(object):
    @staticmethod
    def all(num_replicas: int, num_commands: int) -> Iterable[GlobalOrdering]:
        combos = itertools.combinations_with_replacement
        return combos(Ord.all(num_commands), num_replicas)

    @staticmethod
    def num(num_replicas: int, num_commands: int) -> int:
        n = Ord.num(num_commands)
        r = num_replicas
        return choose(n - 1 + r, r)

    @staticmethod
    def exists_deferred_majority(
        global_ordering: GlobalOrdering,
        cmd: Command
    ) -> bool:
        """Returns whether there is an equal majority with dissenting dep.

        Given a global ordering and command, `exists_deferred_majority` returns
        whether there exists a majority of nodes that agree on the deps of
        `cmd` and exclude `cmd + 1` from these deps and exists some node with
        deps that does include `cmd + 1`. This is the sitaution in which BPaxos
        defers recovery of `cmd`.
        """
        num_replicas = len(global_ordering)
        num_commands = len(global_ordering[0])

        # Compute a histogram of the nodes' deps.
        deps_count: DefaultDict[FrozenSet[Command], int] = defaultdict(int)
        for ordering in global_ordering:
            deps_count[Ord.deps(ordering, cmd)] += 1

        # Check the conditions listed in the docstring.
        next_conflict = Ord.next_conflict(num_commands, cmd)
        return (any(next_conflict in deps for deps in deps_count) and
                any(count >= majority_size(num_replicas) and
                    next_conflict not in deps
                    for (deps, count) in deps_count.items()))

    @staticmethod
    def is_deadlocked(global_ordering: GlobalOrdering) -> bool:
        return all(GlobalOrd.exists_deferred_majority(global_ordering, cmd)
                   for cmd in global_ordering[0])

def is_deadlock_possible(
    queue: Queue,
    num_replicas: int,
    num_commands: int
) -> None:
    global_orderings = GlobalOrd.all(num_replicas, num_commands)
    num = GlobalOrd.num(num_replicas, num_commands)
    batch_size = int(100 * 1000)

    if queue:
        i = 0
        for batch in batched(global_orderings, batch_size):
            queue.put(batch)
            i += batch_size
            print("{}/{}".format(i, num))
    else:
        i = 0
        for global_ordering in global_orderings:
            if GlobalOrd.is_deadlocked(global_ordering):
                print(global_ordering)

            i += 1
            if (i % batch_size) == 0:
                print("{}/{}".format(i, num))


class Worker(Process):
    def __init__(self, queue):
        self.queue = queue
        super(Worker, self).__init__()

    def run(self):
        batch = self.queue.get()
        while batch:
            for global_ordering in batch:
                if global_ordering and GlobalOrd.is_deadlocked(global_ordering):
                    print(global_ordering)
            batch = self.queue.get()


def main():
    # Start the workers.
    num_workers = cpu_count()
    queue = Queue(maxsize=num_workers)
    workers = [Worker(queue) for _ in range(num_workers)]
    for worker in workers:
        worker.start()

    # Dish out work to the workers.
    for num_commands in range(5, 6):
        for num_replicas in range(5, 6):
            # is_deadlock_possible(queue, num_replicas, num_commands)
            is_deadlock_possible(None, num_replicas, num_commands)

    # Wait for the workers.
    for _ in range(num_workers):
        queue.put(None)
    for worker in workers:
        worker.join()

if __name__ == '__main__':
    main()
