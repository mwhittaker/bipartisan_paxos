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
        # Receive from client.
        params.recv +
        # Send phase2a.
        send_size * params.send +
        # Receive phase2b.
        (params.f + 1) * params.recv +
        # Send to client.
        params.send +
        # Send to other leaders.
        params.f * params.send
    )

    return datetime.timedelta(seconds=1) / leader


def basic_epaxos(params: Parameters) -> float:
    n = 2 * params.f + 1
    fast_quorum = n - 1

    leader = (
        # Receive from client.
        params.recv +
        # Send pre-accepts.
        (n - 2) * params.send +
        # Receive pre-accept oks.
        (n - 2) * params.recv +
        # Send to client.
        params.send +
        # Send to other replicas.
        (n - 1) * params.send
    )

    return n * (datetime.timedelta(seconds=1) / leader)


def simple_bpaxos(params: Parameters, num_leaders: int) -> float:
    n = 2 * params.f + 1
    send_size = params.f + 1 if params.thrifty else n

    leader = (
        # Receive from client.
        params.recv +
        # Send to dep service.
        send_size * params.send +
        # Hear from dep service.
        (params.f + 1) * params.recv +
        # Send to acceptors.
        send_size * params.send +
        # Hear from acceptors.
        (params.f + 1) * params.recv +
        # Send to client.
        params.send +
        # Send to other replicas.
        (num_leaders - 1) * params.send
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
        print(f'basic epaxos:       {basic_epaxos(params)}')
        for n in range(1, 20):
            print(f'simple bpaxos ({n:02}): {simple_bpaxos(params, n)}')
        print()


if __name__ == '__main__':
    main()
