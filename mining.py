#!/usr/bin/env python3

import argparse
import datetime
import math
import sys
from random import random
from collections import namedtuple
from operator import attrgetter

def bits_to_target(bits):
    size = bits >> 24
    assert size <= 0x1d

    word = bits & 0x00ffffff
    assert 0x8000 <= word <= 0x7fffff

    if size <= 3:
        return word >> (8 * (3 - size))
    else:
        return word << (8 * (size - 3))

def target_to_bits(target):
    size = (target.bit_length() + 7) // 8
    mask64 = 0xffffffffffffffff
    if size <= 3:
        compact = (target & mask64) << (8 * (3 - size))
    else:
        compact = (target >> (8 * (size - 3))) & mask64

    if compact & 0x00800000:
        compact >>= 8
        size += 1
    assert compact == (compact & 0x007fffff)
    assert size < 256
    return compact | size << 24

def bits_to_work(bits):
    return (2 << 255) // (bits_to_target(bits) + 1)

def target_to_hex(target):
    h = hex(target)[2:]
    return '0' * (64 - len(h)) + h

TARGET_1 = bits_to_target(486604799)

INITIAL_BCC_BITS = 403458999
INITIAL_SWC_BITS = 402734313
INITIAL_FX = 0.18
INITIAL_TIMESTAMP = 1503430225
INITIAL_HASHRATE = 500
INITIAL_HEIGHT = 481824
INITIAL_SINGLE_WORK = bits_to_work(INITIAL_BCC_BITS)

# Steady hashrate mines the BCC chain all the time
STEADY_HASHRATE = 300

# Variable hash is split across both chains according to relative
# revenue.  If the revenue ratio for either chain is at least 15%
# higher, everything switches.  Otherwise the proportion mining the
# chain is linear between +- 15%.
VARIABLE_HASHRATE = 2000
VARIABLE_PCT = 15   # 85% to 115%
VARIABLE_WINDOW = 6  # No of blocks averaged to determine revenue ratio

# Greedy hashrate switches chain if that chain is more profitable for
# GREEDY_WINDOW BCC blocks.  It will only bother to switch if it has
# consistently been GREEDY_PCT more profitable.
GREEDY_HASHRATE = 2000
GREEDY_PCT = 10
GREEDY_WINDOW = 6

State = namedtuple('State', 'height timestamp bits chainwork fx hashrate '
                   'rev_ratio greedy_frac msg')

states = []

def print_headers():
    print(', '.join(['Height', 'Block Time', 'Unix', 'Timestamp',
                     'Difficulty (bn)', 'Hashrate (PH/s)', 'Rev Ratio',
                     'Greedy?', 'Comments']))

def print_state():
    state = states[-1]
    block_time = state.timestamp - states[-2].timestamp
    t = datetime.datetime.fromtimestamp(state.timestamp)
    difficulty = TARGET_1 / bits_to_target(state.bits)
    print(', '.join(['{:d}'.format(state.height),
                     '{:d}'.format(block_time),
                     '{:d}'.format(state.timestamp),
                     '{:%Y-%m-%d %H:%M:%S}'.format(t),
                     '{:.2f}'.format(difficulty / 1e9),
                     '{:.0f}'.format(state.hashrate),
                     '{:.3f}'.format(state.rev_ratio),
                     'Yes' if state.greedy_frac == 1.0 else 'No',
                     state.msg]))

def revenue_ratio(fx, BCC_target):
    '''Returns the instantaneous SWC revenue rate divided by the
    instantaneous BCC revenue rate.  A value less than 1.0 makes it
    attractive to mine BCC.  Greater than 1.0, SWC.'''
    SWC_fees = 0.25 + 2.0 * random()
    SWC_revenue = 12.5 + SWC_fees
    SWC_target = bits_to_target(INITIAL_SWC_BITS)

    BCC_fees = 0.2 * random()
    BCC_revenue = (12.5 + BCC_fees) * fx

    SWC_difficulty_ratio = BCC_target / SWC_target
    return SWC_revenue / SWC_difficulty_ratio / BCC_revenue

def median_time_past(states):
    times = [state.timestamp for state in states]
    return sorted(times)[len(times) // 2]

def next_bits_k(msg, mtp_window, high_barrier, target_raise_frac,
                low_barrier, target_drop_frac, fast_blocks_pct):
    # Calculate N-block MTP diff
    MTP_0 = median_time_past(states[-11:])
    MTP_N = median_time_past(states[-11-mtp_window:-mtp_window])
    MTP_diff = MTP_0 - MTP_N
    bits = states[-1].bits
    target = bits_to_target(bits)

    # Long term block production time stabiliser
    t = states[-1].timestamp - states[-2017].timestamp
    if t < 600 * 2016 * fast_blocks_pct // 100:
        msg.append("2016 block time difficulty raise")
        target -= target // target_drop_frac

    if MTP_diff > high_barrier:
        target += target // target_raise_frac
        msg.append("Difficulty drop {}".format(MTP_diff))
    elif MTP_diff < low_barrier:
        target -= target // target_drop_frac
        msg.append("Difficulty raise {}".format(MTP_diff))
    else:
        msg.append("Difficulty held {}".format(MTP_diff))

    return target_to_bits(target)

def suitable_block_index(index):
    assert index >= 3
    indices = [index - 2, index - 1, index]

    if states[indices[0]].timestamp > states[indices[2]].timestamp:
        indices[0], indices[2] = indices[2], indices[0]

    if states[indices[0]].timestamp > states[indices[1]].timestamp:
        indices[0], indices[1] = indices[1], indices[0]

    if states[indices[1]].timestamp > states[indices[2]].timestamp:
        indices[1], indices[2] = indices[2], indices[1]

    return indices[1]

def compute_index_fast(index_last):
    for candidate in range(index_last - 3, 0, -1):
        index_fast = suitable_block_index(candidate)
        if index_last - index_fast < 5:
            continue
        if (states[index_last].timestamp - states[index_fast].timestamp
            >= 13 * 600):
            return index_fast
    raise AssertionError('should not happen')

def compute_target(first_index, last_index):
    work = states[last_index].chainwork - states[first_index].chainwork
    work *= 600
    work //= states[last_index].timestamp - states[first_index].timestamp
    return (2 << 255) // work - 1

def next_bits_d(msg):
    N = len(states) - 1
    index_last = suitable_block_index(N)
    index_first = suitable_block_index(N - 2016)
    interval_target = compute_target(index_first, index_last)
    index_fast = compute_index_fast(index_last)
    fast_target = compute_target(index_fast, index_last)

    next_target = interval_target
    if (fast_target < interval_target - (interval_target >> 2) or
        fast_target > interval_target + (interval_target >> 2)):
        msg.append("fast target")
        next_target = fast_target
    else:
        msg.append("interval target")

    prev_target = bits_to_target(states[-1].bits)
    min_target = prev_target - (prev_target >> 3)
    if next_target < min_target:
        msg.append("min target")
        return target_to_bits(min_target)

    max_target = prev_target + (prev_target >> 3)
    if next_target > max_target:
        msg.append("max target")
        return target_to_bits(max_target)

    return target_to_bits(next_target)

def block_time(mean_time):
    # Sample the exponential distn
    sample = random()
    lmbda = 1 / mean_time
    return math.log(1 - sample) / -lmbda

def next_step(algo):
    # First figure out our hashrate
    msg = []
    high = 1.0 + VARIABLE_PCT / 100
    scale_fac = 50 / VARIABLE_PCT
    N = VARIABLE_WINDOW
    mean_rev_ratio = sum(state.rev_ratio for state in states[-N:]) / N
    var_fraction = max(0, min(1, (high - mean_rev_ratio) * scale_fac))

    N = GREEDY_WINDOW
    gready_rev_ratio = sum(state.rev_ratio for state in states[-N:]) / N
    greedy_frac = states[-1].greedy_frac
    if mean_rev_ratio >= 1 + GREEDY_PCT / 100:
        if greedy_frac != 0.0:
            msg.append("Greedy miners left")
        greedy_frac = 0.0
    elif mean_rev_ratio <= 1 - GREEDY_PCT / 100:
        if greedy_frac != 1.0:
            msg.append("Greedy miners joined")
        greedy_frac = 1.0

    hashrate = (STEADY_HASHRATE
                + VARIABLE_HASHRATE * var_fraction
                + GREEDY_HASHRATE * greedy_frac)
    # Calculate our dynamic difficulty
    bits = algo.next_bits(msg, **algo.params)
    target = bits_to_target(bits)
    # See how long we take to mine a block
    mean_hashes = pow(2, 256) // target
    mean_time = mean_hashes / (hashrate * 1e15)
    time = int(block_time(mean_time) + 0.5)
    timestamp = states[-1].timestamp + time
    # Get a new FX rate
    fx = states[-1].fx * (1.0 + (random() - 0.5) / 200)
    rev_ratio = revenue_ratio(fx, target)

    chainwork = states[-1].chainwork + bits_to_work(bits)

    # add a state
    states.append(State(states[-1].height + 1, timestamp, bits, chainwork,
                        fx, hashrate, rev_ratio, greedy_frac, ' / '.join(msg)))

Algo = namedtuple('Algo', 'next_bits params')

Algos = {
    'k-1' : Algo(next_bits_k, {
        'mtp_window': 6,
        'high_barrier': 60 * 128,
        'target_raise_frac': 64,   # Reduce difficulty ~ 1.6%
        'low_barrier': 60 * 30,
        'target_drop_frac': 256,   # Raise difficulty ~ 0.4%
        'fast_blocks_pct': 95,
    }),
    'k-2' : Algo(next_bits_k, {
        'mtp_window': 4,
        'high_barrier': 60 * 55,
        'target_raise_frac': 100,   # Reduce difficulty ~ 1.0%
        'low_barrier': 60 * 36,
        'target_drop_frac': 256,   # Raise difficulty ~ 0.4%
        'fast_blocks_pct': 95,
    }),
    'k-3' : Algo(next_bits_k, {
        'mtp_window': 2,
        'high_barrier': 60 * 21,
        'target_raise_frac': 70,   # Reduce difficulty ~ 3.0%
        'low_barrier': 60 * 19,
        'target_drop_frac': 140,   # Raise difficulty ~ 1.0%
        'fast_blocks_pct': 95,
    }),
    'd-1' : Algo(next_bits_d, {}),
}


def main():
    '''Outputs CSV data to stdout.   Final stats to stderr.'''

    parser = argparse.ArgumentParser('Run a mining simulation')
    parser.add_argument('-a', '--algo', metavar='algo', type=str,
                        choices = list(Algos.keys()),
                        default = 'k-1', help='algorithm choice')
    args = parser.parse_args()

    algo = Algos.get(args.algo)

    # Initial state is afer 2020 steady prefix blocks
    N = 2020
    for n in range(-N, 0):
        state = State(INITIAL_HEIGHT + n, INITIAL_TIMESTAMP + n * 600,
                      INITIAL_BCC_BITS, INITIAL_SINGLE_WORK * (n + N + 1),
                      INITIAL_FX, INITIAL_HASHRATE, 1.0, False, '')
        states.append(state)

    # Run the simulation
    print_headers()
    for n in range(10000):
        next_step(algo)
        print_state()

    # Drop the prefix blocks to be left with the simulation blocks
    simul = states[N:]

    mean = (simul[-1].timestamp - simul[0].timestamp) / (len(simul) - 1)
    block_times = [simul[n + 1].timestamp - simul[n].timestamp
                   for n in range(len(simul) - 1)]
    median = sorted(block_times)[len(block_times) // 2]

    print("Mean block time: {}s".format(mean), file=sys.stderr)
    print("Median block time: {}s".format(median), file=sys.stderr)
    print("Max block time: {}s".format(max(block_times)), file=sys.stderr)

if __name__ == '__main__':
    main()
