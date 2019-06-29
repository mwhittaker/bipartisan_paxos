from typing import NamedTuple
import datetime


class Parameters(NamedTuple):
    recv: datetime.timedelta
    send: datetime.timedelta
    thrifty: bool
    f: int


def multipaxos(params: Parameters) -> float:
    n = 2 * params.f + 1
    send_size = params.f + 1 if params.thrifty else n

    leader = (
        params.recv +
        send_size * params.send +
        (params.f + 1) * params.recv +
        params.send
    )

    return datetime.timedelta(seconds=1) / leader


def basic_epaxos(params: Parameters) -> float:
    n = 2 * params.f + 1
    fast_quorum = n - 1

    leader = (
        params.recv +
        (n - 2) * params.send +
        (n - 2) * params.recv +
        params.send
    )

    return n * (datetime.timedelta(seconds=1) / leader)


def simple_bpaxos(params: Parameters, num_leaders: int) -> float:
    n = 2 * params.f + 1
    send_size = params.f + 1 if params.thrifty else n

    leader = (
        params.recv +
        send_size * params.send +
        (params.f + 1) * params.recv +
        send_size * params.send +
        (params.f + 1) * params.recv +
        params.send
    )

    return num_leaders * (datetime.timedelta(seconds=1) / leader)


def main() -> None:
    for f in [1, 2, 3]:
        params = Parameters(
            recv = datetime.timedelta(microseconds=50),
            send = datetime.timedelta(microseconds=50),
            thrifty = True,
            f = f
        )

        print(f'f = {f}:')
        print(f'multipaxos:         {multipaxos(params)}')
        print(f'basic bpaxos:       {basic_epaxos(params)}')
        for n in range(1, 20):
            print(f'simple bpaxos ({n:02}): {simple_bpaxos(params, n)}')
        print()


if __name__ == '__main__':
    main()
