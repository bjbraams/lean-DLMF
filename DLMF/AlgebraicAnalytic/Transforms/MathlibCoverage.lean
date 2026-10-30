/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import DLMF.AlgebraicAnalytic.Transforms.Basic
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# DLMF §1.14 results already in Mathlib and TauCeti

Checked pointers (`dlmf_upstream`) for DLMF §1.14, deliberately not duplicate local theorems.

**Normalizations.** Mathlib's Fourier transform is `𝓕 f w = ∫ e^{-2πi⟨v,w⟩} f(v) dv`; DLMF's
(1.14.1) is `𝓕(f)(x) = (2π)^{-1/2} ∫ f(t) e^{ixt} dt = (2π)^{-1/2} 𝓕_Mathlib f (-x/(2π))`
(`DLMF.AlgebraicAnalytic.fourierTransform_eq_fourier`). Mathlib's statements are for functions on
a finite-dimensional inner product space; the DLMF forms on `ℝ` are proved in
`Transforms/Fourier.lean` through the bridge. Mathlib's `MeasureTheory.convolution` has no factor
`(2π)^{-1/2}` (DLMF 1.14.5). Mathlib's Plancherel theorem is for the `L²` extension of the
transform, not for the pointwise integral of an `L¹ ∩ L²` function. Mathlib's `mellin` is DLMF's
Mellin transform 1.14.32 exactly, and `mellinInv σ F x = (1/2π) ∫ x^{-(σ+iy)} F(σ + iy) dy` is
DLMF's inversion integral 1.14.35. TauCeti's `TauCeti.laplaceTransform` is the Laplace transform
of a measure on `ℝ≥0` at real arguments, a different (measure) setting from DLMF's 1.14.17; its
uniqueness theorem `TauCeti.Measure.ext_of_forall_integral_exp_neg_mul_eq` and convolution
theorem `TauCeti.laplaceTransform_conv` are related to §1.14(iii) and 1.14.31 but are not
recorded as pointers here (those TauCeti modules are not built in this project).
-/

/- §1.14(i): Fourier transform. -/
dlmf_upstream 1.14.E1 Real.fourier_real_eq_integral_exp_smul
  "different convention: 𝓕 f w = ∫ e^{-2πivw} f(v) dv; DLMF's 𝓕(f)(x) = (2π)^{-1/2} 𝓕 f (-x/2π)"
dlmf_upstream 1.14.i Real.zero_at_infty_fourier
  "different convention: Riemann–Lebesgue lemma, 𝓕 f → 0 at infinity"
dlmf_upstream 1.14.i VectorFourier.fourierIntegral_continuous
  "different convention: the Fourier integral of an integrable function is continuous"
dlmf_upstream 1.14.E2 Real.norm_fourier_le_integral_norm
  "different convention: ‖𝓕 f w‖ ≤ ∫ ‖f‖ (no factor (2π)^{-1/2})"
dlmf_upstream 1.14.E4 Continuous.fourierInv_fourier_eq
  "different convention: 𝓕⁻(𝓕 f) = f for continuous integrable f with 𝓕 f integrable"
dlmf_upstream 1.14.E4 MeasureTheory.Integrable.fourierInv_fourier_eq
  "different convention: pointwise inversion at points of continuity, 𝓕 f integrable"
dlmf_upstream 1.14.i Real.fourier_mul_convolution_eq
  "different convention: 𝓕(f ⋆ g) = 𝓕 f · 𝓕 g for integrable f, g"
dlmf_upstream 1.14.E8 MeasureTheory.Lp.norm_fourier_eq
  "partial: Plancherel ‖𝓕 f‖₂ = ‖f‖₂ for the L² extension of the transform"
dlmf_upstream 1.14.E7_5 MeasureTheory.Lp.inner_fourier_eq
  "partial: Parseval ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫ for the L² extension of the transform"

/- §1.14(iv): Mellin transform. -/
dlmf_upstream 1.14.E32 mellin
  "exact: 𝓜(f)(s) = ∫₀^∞ x^{s-1} f(x) dx"
dlmf_upstream 1.14.iv mellin_differentiableAt_of_isBigO_rpow
  "partial: analyticity in the strip under O-bounds at 0 and ∞"
dlmf_upstream 1.14.iv mellinConvergent_of_isBigO_rpow
  "exact: x^{σ-1} f integrable for σ between the O-exponents (the note of §1.14(iv))"
dlmf_upstream 1.14.E33 mellin_eq_fourier
  "partial: the Mellin transform on a vertical line is a Fourier transform (gives 1.14.33)"
dlmf_upstream 1.14.E35 mellinInv_mellin_eq
  "exact: f(x) = (1/2πi) ∫ x^{-s} 𝓜(f)(s) ds, with convergence on ℜs = σ and continuity at x"

/- §1.14(vii): table entries. -/
dlmf_upstream 1.14.T1 fourierIntegral_gaussian
  "different convention: ∫ e^{itx} e^{-bx²} dx = (π/b)^{1/2} e^{-t²/(4b)}, ℜb > 0 (row 9)"
dlmf_upstream 1.14.T4 integral_exp_mul_complex_Ioi
  "special case: ∫_c^∞ e^{ax} dx = -e^{ac}/a, ℜa < 0 (rows 2 and 5)"
