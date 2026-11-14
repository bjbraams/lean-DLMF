"""Numerical principal-branch witnesses; no Lean certificate is claimed."""

import mpmath as m

m.mp.dps = 60
x, y, z, p = m.mpc(1) / 5 - 12 * m.j / 5, m.mpc(1) / 2 + 7 * m.j, 2 + 2 * m.j, m.mpc(3) / 2 - m.j
a = (x + y) / 2
P = lambda v, s: (m.sqrt((v + x) * (v + y)) + s * m.sqrt((v - x) * (v - y))) / 2
u, v = P(z, 1), P(z, -1)
print("x,y,z,p:", x, y, z, p)
print("a,z+,z-:", a, u, v)
print("RF lhs,rhs:", m.elliprf(x * x, y * y, z * z), m.elliprf(a * a, v * v, u * u))
print(
    "RG lhs,rhs:",
    2 * m.elliprg(x * x, y * y, z * z),
    4 * m.elliprg(a * a, u * u, v * v) - x * y * m.elliprf(x * x, y * y, z * z) - z,
)
for s in (1, -1):
    u, v = P(z, s), P(z, -s)
    print(
        "RD sign, lhs,rhs:",
        s,
        (u * u - v * v) * m.elliprd(x * x, y * y, z * z),
        2 * (u * u - a * a) * m.elliprd(a * a, v * v, u * u)
        - 3 * m.elliprf(x * x, y * y, z * z)
        + 3 / z,
    )
    print(
        "RJ0 p=z sign,lhs,rhs:",
        s,
        (u * u - v * v) * m.elliprj(0, x * x, y * y, z * z),
        2 * (u * u - a * a) * m.elliprj(0, x * y, a * a, u * u)
        - 3 * m.elliprf(0, x * y, a * a)
        + 3 * m.pi / (2 * z),
    )
    u, v = P(p, s), P(p, -s)
    print(
        "RJ sign,lhs,rhs:",
        s,
        (u * u - v * v) * m.elliprj(x * x, y * y, z * z, p * p),
        2 * (u * u - a * a) * m.elliprj(a * a, P(z, 1) ** 2, P(z, -1) ** 2, u * u)
        - 3 * m.elliprf(x * x, y * y, z * z)
        + 3 * m.elliprc(z * z, p * p),
    )
