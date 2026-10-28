/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Struve.Asymptotics.Watson
public import DLMF.Struve.Asymptotics.IntegratedKernels
public import DLMF.Struve.Asymptotics.IntegratedExpansions
public import DLMF.Struve.Asymptotics.LargeOrder
public import DLMF.Struve.Asymptotics.BinomialAndAnger
public import DLMF.Struve.Asymptotics.AngerWeberExpansions
public import DLMF.Struve.Asymptotics.TurningPointEstimates
public import DLMF.Struve.Asymptotics.InnerExpansions
public import DLMF.Struve.Asymptotics.ScaledExpansions

/-!
# Struve and Anger–Weber asymptotics

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.

The large-argument expansions 11.6.1 and 11.6.2 are proved by Watson's lemma
(`hasAsymptoticExpansion_integral_cexp_smul_sector`). For `𝐊_ν` the Laplace integral
11.5.2 (`DLMF.Bessel.struveK_eq_integral`) is rotated to the ray `arg t = α`, `|α| < π/2`
(`struveK_eq_struveKRotated`, by `Complex.integral_Ioi_eq_exp_mul_integral_Ioi_rotate`
and analytic continuation, following `DLMF.Confluent.kummerU_eq_tricomiRotated`); two
rotated sectors cover `|arg z| ≤ π - δ`. For `𝐌_ν` the integral 11.5.4 gives the case
`re ν > 1/2`, and the recurrence 11.4.25 with 10.29.1 extends it to all orders.

The large-order expansions 11.6.6–11.6.7 follow from 11.5.2 and 11.5.4 by a binomial expansion
of `(1 ± t²)^{ν-1/2}` with the uniform remainder bounds of `DLMF.Struve.LargeOrderTools`; the
binomial terms are regrouped into powers of `1/ν` through the reflected polynomials
`struveLO_Q` (`struveLO_poly_bound`). The removable singularity 11.11(iii) of the coefficient
recurrence follows from the Lagrange-inversion form `A_k(λ) = (2πi)⁻¹ ∮ (t + λ sinh t)^{-2k-1} dt`
(`struveLO_angerScaledA_eq`).
-/
