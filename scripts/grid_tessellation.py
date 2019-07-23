from typing import Any, Iterator, List, NamedTuple, Optional, Set, Tuple
import itertools
import random


class Config(NamedTuple):
    f: int # Number of tolerable failures
    n: int # Number of machines
    m: int # Number of threads per machine


def batch(nodes: List[Any], n: int) -> List[List[Any]]:
    return [nodes[x:x+n] for x in range(0, len(nodes), n)]


def transpose(grid: List[List[Any]]) -> List[List[Any]]:
    assert len(grid) > 0
    return [[row[i] for row in grid] for i in range(len(grid[0]))]


class Tessellation:
    def __init__(self, config: Config, grid: List[List[int]]) -> None:
        self.config = config
        self.grid = grid

    @staticmethod
    def all(config: Config) -> Iterator['Tessellation']:
        ids = [i for i in range(config.n) for _ in range(config.m)]
        for shuffled in itertools.permutations(ids):
            yield Tessellation(config, batch(list(shuffled), config.m))

    @staticmethod
    def random(config: Config) -> 'Tessellation':
        grid = [i for i in range(config.n) for _ in range(config.m)]
        random.shuffle(grid)
        return Tessellation(config, batch(grid, config.m))

    def __str__(self) -> str:
        return '\n'.join(str(row) for row in self.grid)

    def _quorum_exists(self, excluding: Set[int]) -> bool:
        return (any(len(set(row).intersection(excluding)) == 0
                    for row in self.grid) and
                any(len(set(col).intersection(excluding)) == 0
                    for col in transpose(self.grid)))

    def is_safe(self) -> bool:
        n = self.config.n
        f = self.config.f
        return all(self._quorum_exists(set(excluding))
                   for excluding in itertools.combinations(range(n), f))


def main() -> None:
    config = Config(f=2, n=4, m=4)
    for (i, tessellation) in enumerate(Tessellation.all(config)):
        if tessellation.is_safe():
            print(2*i)
            print(tessellation)
            return

        tessellation = Tessellation.random(config)
        if tessellation.is_safe():
            print(2*i + 1)
            print(tessellation)
            return


if __name__ == '__main__':
    main()
