/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Summability.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Fractional integration under absolute Fubini hypotheses

Andrews, Askey and Roy, *Special Functions*, Appendix B, §B.3, pp. 604–605.
The semigroup law is stated with its actual integrable triangular kernel rather
than requiring continuity. Abel's half-integral inversion holds almost everywhere
for locally integrable data.
-/

@[expose] public section

open MeasureTheory Filter

namespace DLMF.AlgebraicAnalytic

/-- The fractional-integral semigroup law under the absolute Fubini hypothesis.
Andrews–Askey–Roy, *Special Functions*, Appendix B, §B.3, pp. 604–605
(synopsis AAR-B.2–B.3). All powers use the principal complex power of a
positive real base on the integration triangle. -/
theorem fractionalIntegral_fractionalIntegral_of_integrable
    {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) {x : ℝ} (hx : 0 ≤ x)
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioo 0 x)))
    (hFubini : Integrable (fun p : ℝ × ℝ =>
      if 0 < p.2 ∧ p.2 < p.1 ∧ p.1 < x then
        ((x - p.1 : ℝ) : ℂ) ^ (α - 1) *
          ((p.1 - p.2 : ℝ) : ℂ) ^ (β - 1) * f p.2 else 0)) :
    fractionalIntegral α (fractionalIntegral β f) x = fractionalIntegral (α + β) f x := by
  sorry

/-- Abel's inversion of a half-integral for locally integrable data.
Andrews–Askey–Roy, *Special Functions*, Appendix B, §B.3, pp. 604–605
(synopsis AAR-B.2–B.3). The derivative equality is necessarily almost everywhere. -/
theorem ae_hasDerivAt_fractionalIntegral_half_twice {f : ℝ → ℂ}
    (hf : ∀ b : ℝ, 0 < b → IntegrableOn f (Set.Icc 0 b)) :
    ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioi 0),
      HasDerivAt (fun y : ℝ => fractionalIntegral (1 / 2) (fractionalIntegral (1 / 2) f) y)
        (f x) x := by
  sorry


/-- The fractional semigroup law for arbitrary `L¹` data holds almost everywhere on a
finite interval. Andrews–Askey–Roy, *Special Functions*, §2.9, pp. 111–114
(synopsis AAR-2.9.1). Absolute Fubini integrability at almost every outer point
follows from the positive real parts and is not an extra hypothesis. -/
theorem ae_riemannLiouvilleIntegralFrom_riemannLiouvilleIntegralFrom
    {a b : ℝ} (hab : a < b) {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re)
    {f : ℝ → ℂ} (hf : IntegrableOn f (Set.Icc a b)) :
    (fun x => riemannLiouvilleIntegralFrom a α (riemannLiouvilleIntegralFrom a β f) x)
      =ᵐ[volume.restrict (Set.Icc a b)] riemannLiouvilleIntegralFrom a (α + β) f := by
  sorry

/-- Left and right fractional integrals are dual under the actual triangular Fubini
hypothesis. Andrews–Askey–Roy, *Special Functions*, §2.9, pp. 111–114
(synopsis AAR-2.9.1). Both products are integrable; no positivity or conjugation
of the complex data is imposed. -/
theorem integral_riemannLiouvilleIntegralFrom_mul_eq
    {a b : ℝ} (hab : a < b) {α : ℂ} (hα : 0 < α.re) {f g : ℝ → ℂ}
    (hf : IntegrableOn f (Set.Icc a b)) (hg : IntegrableOn g (Set.Icc a b))
    (hFubini : IntegrableOn (fun p : ℝ × ℝ =>
      ((p.2 - p.1 : ℝ) : ℂ) ^ (α - 1) * f p.1 * g p.2)
      {p | a < p.1 ∧ p.1 < p.2 ∧ p.2 < b}) :
    IntegrableOn (fun x => riemannLiouvilleIntegralFrom a α f x * g x) (Set.Icc a b) ∧
      IntegrableOn (fun x => f x * riemannLiouvilleIntegralUpper b α g x) (Set.Icc a b) ∧
      (∫ x : ℝ in a..b, riemannLiouvilleIntegralFrom a α f x * g x) =
        ∫ x : ℝ in a..b, f x * riemannLiouvilleIntegralUpper b α g x := by
  sorry

end DLMF.AlgebraicAnalytic
