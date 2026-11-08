/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Order.Filter.Cofinite

/-!
# Differentiating Laurent moments on a circle

Integrating the derivative of `f(z)z⁻ⁿ` around a circle relates the Laurent moments of
`f` and its derivative. Only differentiability on the circle and continuity of the
first derivative are required; the enclosed center may be singular.
-/

@[expose] public noncomputable section

open Complex Set Metric
open scoped Real Topology

namespace circleIntegral

/-- Integration of a derivative on a circle gives the Laurent moment recurrence. -/
theorem integral_deriv_mul_zpow {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ∀ z ∈ sphere (0 : ℂ) R, DifferentiableAt ℂ f z)
    (hd : ContinuousOn (deriv f) (sphere (0 : ℂ) R)) (n : ℤ) :
    (∮ z in C(0, R), deriv f z * z ^ (-n)) =
      (n : ℂ) * ∮ z in C(0, R), f z * z ^ (-(n + 1)) := by
  have hz0 {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) : z ≠ 0 := by
    have H : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
    intro h
    simp [h] at H
    linarith
  have hF : ContinuousOn f (sphere (0 : ℂ) R) :=
    fun z hz => (hf z hz).continuousAt.continuousWithinAt
  have hci (k : ℤ) : ContinuousOn (fun z : ℂ => z ^ k) (sphere (0 : ℂ) R) :=
    fun z hz => (continuousAt_id.zpow₀ k (Or.inl (hz0 hz))).continuousWithinAt
  have hD : CircleIntegrable (fun z => deriv f z * z ^ (-n)) 0 R :=
    (hd.mul (hci _)).circleIntegrable hR.le
  have hH : CircleIntegrable (fun z => (n : ℂ) * (f z * z ^ (-(n + 1)))) 0 R :=
    ((hF.mul (hci _)).const_mul _).circleIntegrable hR.le
  have H := integral_eq_zero_of_hasDerivWithinAt hR.le
    (f := fun z => f z * z ^ (-n))
    (f' := fun z => deriv f z * z ^ (-n) - (n : ℂ) * (f z * z ^ (-(n + 1))))
    (fun z hz => by
      have HH := ((hf z hz).hasDerivAt.mul
        (hasDerivAt_zpow (-n) z (Or.inl (hz0 hz)))).hasDerivWithinAt
          (s := sphere (0 : ℂ) R)
      convert HH using 1
      push_cast
      rw [show -n - 1 = -(n + 1) by omega]
      ring)
  rw [integral_sub hD hH, integral_const_mul] at H
  exact sub_eq_zero.mp H

end circleIntegral

namespace Complex

open Filter

/-- Away from finitely many integer indices, a falling factorial controls the corresponding
power of the index uniformly. -/
theorem eventually_norm_int_pow_le_prod_sub (m : ℕ) :
    ∀ᶠ n : ℤ in cofinite, ‖(n : ℂ)‖ ^ m ≤
      (2 : ℝ) ^ m * ‖∏ j ∈ Finset.range m, ((n : ℂ) - (j : ℂ))‖ := by
  have hlarge : ∀ᶠ n : ℤ in cofinite, (2 * m : ℤ) ≤ |n| := by
    apply eventually_cofinite.mpr
    apply (Set.finite_Icc (-(2 * m : ℤ)) (2 * m)).subset
    intro n hn
    have H := abs_lt.mp (lt_of_not_ge hn)
    exact ⟨H.1.le, H.2.le⟩
  filter_upwards [hlarge] with n hn
  have hnR : 2 * (m : ℝ) ≤ ‖(n : ℂ)‖ := by
    rw [norm_intCast, ← Int.cast_abs]
    exact_mod_cast hn
  have H : (∏ _j ∈ Finset.range m, ‖(n : ℂ)‖) ≤
      ∏ j ∈ Finset.range m, 2 * ‖(n : ℂ) - (j : ℂ)‖ := by
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro j hj
    have hjR : (j : ℝ) ≤ m := by exact_mod_cast (Finset.mem_range.mp hj).le
    have H := norm_sub_norm_le (n : ℂ) (j : ℂ)
    rw [norm_natCast] at H
    linarith
  simpa only [Finset.prod_const, Finset.card_range, Finset.prod_mul_distrib,
    ← norm_prod] using H

end Complex
