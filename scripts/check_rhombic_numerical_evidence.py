"""Interval evaluation of the theta formulas for DLMF's rhombic lattice roots.

No Lean proof is claimed. mpmath interval arithmetic encloses a finite series,
and explicit geometric upper bounds enclose both omitted tails.
"""

import mpmath as mp

iv = mp.iv
iv.dps = 60
N = 24


def root_intervals(b):
    r = iv.exp(-iv.pi * b)
    A = 1 + 2 * sum(r ** (n * n) for n in range(1, N + 1) if n % 2 == 0)
    B = 2 * sum(r ** (n * n) for n in range(1, N + 1) if n % 2 == 1)
    # n^2 has consecutive differences at least 2N+3 for n >= N+1.
    tail = 2 * r ** ((N + 1) ** 2) / (1 - r ** (2 * N + 3))
    A += iv.mpf([-1, 1]) * tail
    B += iv.mpf([-1, 1]) * tail
    C = sum((-1) ** (n * (n + 1) // 2) * r ** (n * (n + 1)) for n in range(N + 1))
    ctail = r ** ((N + 1) * (N + 2)) / (1 - r ** (2 * N + 4))
    C += iv.mpf([-1, 1]) * ctail
    # theta_3 = A+iB, theta_4=A-iB, theta_2^4=16 i r C^4.
    e1re = iv.pi**2 / 6 * (A**4 - 6 * A**2 * B**2 + B**4)
    e3im = -iv.pi**2 / 12 * (4 * A * B * (A**2 - B**2) + 16 * r * C**4)
    return e1re, e3im


b1, b2 = iv.mpf(1) / 5, iv.mpf(1) / 10
u1, v1 = root_intervals(b1)
u2, v2 = root_intervals(b2)
print("a = 1; b1 = 1/5; b2 = 1/10; N =", N)
print("Re e1(b1):", u1)
print("Re e1(b2):", u2)
print("Im e3(b1):", v1)
print("Im e3(b2):", v2)
print("Hypothesis Im e3(b1) < Im e3(b2):", bool(v1 < v2))
print("Opposite conclusion Re e1(b2) < Re e1(b1):", bool(u2 < u1))
