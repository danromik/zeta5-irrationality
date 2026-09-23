import random
from core import *
from collections import Counter
from test_largeE import inst, check
rng = random.Random(5)
for p, kmin, kmax in [(11, 7, 10), (13, 9, 12), (17, 12, 16)]:
    Es = Counter(); fails = 0; tight = 0; n = 0; fails1 = 0
    for _ in range(25):
        S, rho, W = inst(p, rng, kmin, kmax)
        E, v, u, tt = check(p, S, rho, W)
        Es[E] += 1; n += 1
        if v < E: fails += 1
        if v == E: tight += 1
        if v < E + 1: fails1 += 1
    print(f"p={p}: E distribution {sorted(Es.items())}; failures {fails}/{n}; tight {tight}; claim-E+1 failures {fails1}")
