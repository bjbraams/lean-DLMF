/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Mathieu.Properties.BasicSolutions
public import DLMF.Mathieu.Properties.Floquet
public import DLMF.Mathieu.Properties.Spectra
public import DLMF.Mathieu.Properties.Eigenfunctions

/-!
# Basic properties of Mathieu's equation and its solutions (DLMF §28.2)

The algebraic forms of Mathieu's equation (28.2.2, 28.2.3), the symmetries 28.2.4, the parity,
Wronskian and half-period relations of the basic solutions (28.2.5–28.2.13), Floquet theory
(28.2.14–28.2.20), the eigenvalues (28.2.21–28.2.28, Table 28.2.1) and the eigenfunctions
(Table 28.2.2, 28.2.29–28.2.39).

Proved here from the definitions of `DLMF.Mathieu.Basic` (hence relative to the admitted
existence theorem `exists_isMathieuSolution`, and for eigenvalue statements to the admitted
`mathieuSpecA_exists`, `mathieuSpecB_exists`): the algebraic forms, the symmetries, parity,
the Wronskian, 28.2.7–28.2.13, the connection formula 28.2.17 and the Floquet dichotomy of
§28.2(iv), the boundary conditions 28.2.21–28.2.22, the periodicity and parity of Table 28.2.2
and 28.2.38–28.2.39, Floquet's theorem 28.2.14–28.2.16, the half-period relations between
`q` and `-q` (28.2.16, 28.2.26–28.2.28), the ordering within each spectrum, the values at
`q = 0` (28.2.23, 28.2.24, 28.2.29), the normalization and orthogonality 28.2.30–28.2.32, and
(from the admitted analytic dependence on `a`) the characterizations of Table 28.2.1.
Also proved (2026-10-26, round 2): the singularities of the algebraic form (§28.2(i)), the joint
analyticity of `w_I`, `w_II` in `(z, a, q)` (§28.2(ii), by holomorphic parameter dependence and
Hartogs's theorem from lean-codes), `cos πν` as an entire function of `(a, q²)` (§28.2(iii)), the
Fourier series of Floquet solutions and its converse (28.2.18–28.2.20), and Ince's theorem
(§28.2(iv)) by the Casoratian of the Fourier coefficient recurrences (no coexistence for
`q ≠ 0`). Interlacing (Sturm–Liouville theory), the signs in 28.2.34–28.2.37 and the infinitude
of the characteristic set (§28.2(v)) remain admitted.
28.2.33 carries the hypothesis `n ≠ 0` (added 2026-10-26): for the junk value `n = 0` it
fails (`p1a1_integral_mathieuCe_mul_mathieuSe_zero_ne`).

The principal characteristic exponent `ν̂ = π⁻¹ arccos w_I(π; a, q)` uses the project's
principal arccosine `DLMF.Elementary.arccosPrincipal` (DLMF 4.23.16); no new definition is
made.
-/
