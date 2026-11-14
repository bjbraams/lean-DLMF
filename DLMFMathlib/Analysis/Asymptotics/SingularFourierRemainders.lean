/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Singular Fourier remainders and weak endpoint expansions

Olver, *Asymptotics and Special Functions*, Chapter 3, Lemmas 12.2–12.3
and Theorem 13.2, pp. 99–102, synopses O-3.12–O-3.13 and O-3.15.
Conditional integrals are ordinary cutoff limits, with uniform convergence away
from zero frequency. Finite exceptional sets do not permit interior jumps in the
weak endpoint theorem, whose amplitude is continuous.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory Complex Asymptotics
open scoped Topology

namespace Asymptotics

/-- The oscillatory power tail has a uniform inverse-frequency bound even for negative alpha.
Olver, Chapter 3, Lemma 12.2, synopsis O-3.12. -/
theorem exists_power_fourier_tail_bound {α K : ℝ} (hα : α < 1) (hK : 0 < K) :
    ∃ F : ℝ → ℂ,
      (∀ x : ℝ, 0 < x → Tendsto (fun T : ℝ =>
        ∫ t in K..T, exp (I * x * t) * (t ^ (α - 1) : ℝ)) atTop (𝓝 (F x))) ∧
      (∀ X : ℝ, 0 < X → TendstoUniformlyOn (fun T x : ℝ =>
        ∫ t in K..T, exp (I * x * t) * (t ^ (α - 1) : ℝ)) F atTop (Ici X)) ∧
      ∀ x : ℝ, 0 < x → ‖F x‖ ≤ 2 * K ^ (α - 1) / x := by
  sorry

/-- A differentiated little-oh singular amplitude gives a little-oh Fourier remainder.
Olver, Chapter 3, Lemma 12.3, synopsis O-3.13. -/
theorem exists_fourier_remainder_isLittleO {φ : ℝ → ℂ} {α : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (singular : Finset ℝ)
    (hφ : ContDiffOn ℝ 1 φ (Ioi 0 \ (singular : Set ℝ)))
    (hzero : φ =o[𝓝[>] 0] fun t : ℝ => t ^ (α - 1))
    (hderiv : deriv φ =o[𝓝[>] 0] fun t : ℝ => t ^ (α - 2))
    (hvar : ∀ K : ℝ, 0 < K → BoundedVariationOn φ (Ici K))
    (hinfty : Tendsto φ atTop (𝓝 0)) :
    ∃ F : ℝ → ℂ,
      (∀ X : ℝ, 0 < X → TendstoUniformlyOn (fun T x : ℝ =>
        ∫ t in (0 : ℝ)..T, exp (I * x * t) * φ t) F atTop (Ici X)) ∧
      F =o[atTop] (fun x : ℝ => x ^ (-α)) := by
  sorry

/-- The Big-O version of the singular Fourier remainder lemma.
Olver, Chapter 3, Lemma 12.3, synopsis O-3.13. -/
theorem exists_fourier_remainder_isBigO {φ : ℝ → ℂ} {α : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (singular : Finset ℝ)
    (hφ : ContDiffOn ℝ 1 φ (Ioi 0 \ (singular : Set ℝ)))
    (hzero : φ =O[𝓝[>] 0] fun t : ℝ => t ^ (α - 1))
    (hderiv : deriv φ =O[𝓝[>] 0] fun t : ℝ => t ^ (α - 2))
    (hvar : ∀ K : ℝ, 0 < K → BoundedVariationOn φ (Ici K))
    (hinfty : Tendsto φ atTop (𝓝 0)) :
    ∃ F : ℝ → ℂ,
      (∀ X : ℝ, 0 < X → TendstoUniformlyOn (fun T x : ℝ =>
        ∫ t in (0 : ℝ)..T, exp (I * x * t) * φ t) F atTop (Ici X)) ∧
      F =O[atTop] (fun x : ℝ => x ^ (-α)) := by
  sorry

/-- A continuous bounded-variation amplitude, piecewise smooth away from finitely many points,
has the two endpoint terms and a little-oh inverse-frequency remainder.
Olver, Chapter 3, Theorem 13.2 after phase substitution, synopsis O-3.15. -/
theorem isLittleO_fourier_sub_endpoint_terms {φ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn φ (Icc a b)) (hvar : BoundedVariationOn φ (Icc a b))
    (singular : Finset ℝ) (hsmooth : ContDiffOn ℝ 1 φ (Ioo a b \ (singular : Set ℝ))) :
    (fun x : ℝ => (∫ t in a..b, exp (I * x * t) * φ t) -
      (exp (I * x * b) * φ b - exp (I * x * a) * φ a) / (I * x))
        =o[atTop] (fun x : ℝ => x⁻¹) := by
  sorry

/-- The weak endpoint formula on a half-line retains its ordinary improper limit.
Olver, Chapter 3, Theorem 13.2 after phase substitution, synopsis O-3.15. -/
theorem exists_fourier_halfLine_sub_endpoint_isLittleO {φ : ℝ → ℂ} {a : ℝ}
    (hcont : ContinuousOn φ (Ici a)) (hvar : BoundedVariationOn φ (Ici a))
    (singular : Finset ℝ) (hsmooth : ContDiffOn ℝ 1 φ (Ioi a \ (singular : Set ℝ)))
    (hinfty : Tendsto φ atTop (𝓝 0)) :
    ∃ F : ℝ → ℂ,
      (∀ X : ℝ, 0 < X → TendstoUniformlyOn (fun T x : ℝ =>
        ∫ t in a..T, exp (I * x * t) * φ t) F atTop (Ici X)) ∧
      (fun x : ℝ => F x + exp (I * x * a) * φ a / (I * x))
        =o[atTop] (fun x : ℝ => x⁻¹) := by
  sorry

/-- The oscillatory Gamma moment, as an ordinary cutoff limit rather than a totalized
Lebesgue integral. Olver, Chapter 3, Lemma 12.1, p. 98, synopsis O-3.11. -/
theorem tendsto_integral_rpow_mul_exp_I {α x : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (hx : 0 < x) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T,
      exp (I * x * t) * (t ^ (α - 1) : ℝ)) atTop
        (𝓝 (exp (I * Real.pi * α / 2) * Real.Gamma α *
          ((x ^ (-α) : ℝ) : ℂ))) := by
  sorry

end Asymptotics
