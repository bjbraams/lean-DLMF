/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Confluent.IntegralRepresentations.EulerAndBessel
public import DLMF.Confluent.IntegralRepresentations.BarnesAndConnections

/-!
# Integral representations (DLMF §§13.4, 13.16)

Gauss kernels use cut-plane continuation, since their arguments range over the
negative ray. Argument bounds explicitly exclude zero where needed.

Euler, Laplace, Bessel, and vertical Barnes integrals are acquired on real
intervals or vertical lines. Hankel-loop and Pochhammer-double-loop formulas
13.4.9–13.4.15 are deferred pending a contour API, matching Chapter 15.
The `M` form of 13.4.1 is already `kummerM_eq_euler_integral` in `Basic`.
Tricomi's Laplace representation is proved in its full stated region. The Gauss
connection formula tends to the defining Tricomi connection, while its Euler
integral tends to the Laplace integral. The Tau Ceti contributors' second Beta
integrability theorem supplies the fixed majorant; Mathlib's real Bernoulli
inequality and dominated convergence justify the limit. Holomorphic continuation
in the argument and continuity in the second parameter cover every parameter.
The Whittaker W Laplace representation follows by an affine substitution.
The Gauss and Stieltjes representations 13.4.5, 13.4.6, 13.4.8, 13.16.6 and 13.16.9 use the
Kummer and Tricomi Laplace transforms, so they are proved in `DLMF.Confluent.Integrals`.
The exponential Barnes integrals 13.4.18 and 13.16.12 insert the Cahen–Mellin integral for
`e^{-x(1+τ)}` into Tricomi's Laplace integral and evaluate Euler's second Beta integral
in `τ`. Tricomi's contiguous relation in `a`, matched by the reciprocal Gamma recurrence,
then removes the restriction `Re a > 0`.
-/
