/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Polygamma

/-!
# Polygamma and the Hurwitz zeta function (Duverney §§2.1.5, 2.5.2)

This file connects the project's polygamma series with Mathlib's Hurwitz zeta function.
* `polygamma_eq_hurwitzZeta`: `ψ⁽ⁿ⁾(a) = (-1)ⁿ⁺¹ n! ζ(n+1, a)` for `0 < a ≤ 1`, `n ≥ 1`
  (DLMF 25.11.12). Mathlib's Dirichlet series for `hurwitzZeta` covers only `a ∈ [0, 1]`.
* `hurwitzZeta_one_half_nat`: `ζ(n+1, ½) = (2ⁿ⁺¹ - 1) ζ(n+1)` (DLMF 25.11.11).
* `integral_cpow_mul_exp_div_one_sub_exp`: `∫₀^∞ t^{s-1} e^{-xt}/(1-e^{-t}) dt = Γ(s) ∑ₖ (k+x)^{-s}`
  for `x > 0`, `Re s > 1`, by termwise integration of the geometric series. It gives the
  Hurwitz integral 25.11.25 (Duverney (2.89)) and the polygamma integral (Duverney (2.29)).
-/

@[expose] public section

open Complex Filter HurwitzZeta MeasureTheory Set
open scoped Nat Real Topology

noncomputable section

namespace DLMF.Gamma

/-- **Polygamma and Hurwitz zeta** (Duverney (2.81), DLMF 25.11.12): for `0 < a ≤ 1` and
`n ≥ 1`, `ψ⁽ⁿ⁾(a) = (-1)ⁿ⁺¹ n! ζ(n+1, a)`. -/
@[dlmf 25.11.E12]
theorem polygamma_eq_hurwitzZeta {n : ℕ} (hn : 0 < n) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    polygamma n a = (-1 : ℂ) ^ (n + 1) * n ! * hurwitzZeta a (n + 1) := by
  have hmem : (a : ℂ) ∈ notNegNat := ofReal_mem_notNegNat ha0
  have hH := hasSum_hurwitzZeta_of_one_lt_re (s := ((n + 1 : ℕ) : ℂ)) ⟨ha0.le, ha1⟩
    (by simp; omega)
  rw [polygamma_eq_tsum hn hmem, show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring,
    ← hH.tsum_eq]
  congr 2
  funext k
  rw [zpow_neg_one_sub_nat_eq, cpow_natCast, add_comm]

/-- `ζ(n+1, ½) = (2ⁿ⁺¹ - 1) ζ(n+1)` for `n ≥ 1` (Duverney (2.82), DLMF 25.11.11). -/
@[dlmf 25.11.E11]
theorem hurwitzZeta_one_half_nat {n : ℕ} (hn : 0 < n) :
    hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) (n + 1) =
      ((2 : ℂ) ^ (n + 1) - 1) * riemannZeta (n + 1) := by
  have h := polygamma_eq_hurwitzZeta hn (a := 1 / 2) (by norm_num) (by norm_num)
  rw [show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by push_cast; ring, polygamma_one_div_two n hn] at h
  have hc : (-1 : ℂ) ^ (n + 1) * (n ! : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  apply mul_left_cancel₀ hc
  linear_combination -h

/-- `ζ(n+1, 1) = ζ(n+1)`, read off from `ψ⁽ⁿ⁾(1)` through the Hurwitz zeta function. -/
theorem hurwitzZeta_one_nat {n : ℕ} (hn : 0 < n) :
    hurwitzZeta ((1 : ℝ) : UnitAddCircle) (n + 1) = riemannZeta (n + 1) := by
  have h := polygamma_eq_hurwitzZeta hn (a := 1) one_pos le_rfl
  rw [ofReal_one, polygamma_one n hn] at h
  have hc : (-1 : ℂ) ^ (n + 1) * (n ! : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  apply mul_left_cancel₀ hc
  linear_combination -h

/-- `t ↦ t^{s-1} e^{-rt}` is integrable on `(0, ∞)` for `Re s > 0`, `r > 0`. -/
theorem integrableOn_cpow_mul_exp_neg_mul {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * exp (-((r : ℂ) * t))) (Ioi 0) := by
  have hg := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s.re - 1) (p := 1) (b := r)
    (by linarith) one_pos hr
  refine hg.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht' : (0 : ℝ) < t := ht
    exact (((continuous_ofReal.continuousAt (x := t)).cpow continuousAt_const
      (Or.inl (by simpa using ht'))).mul
      (by fun_prop : Continuous fun t : ℝ => exp (-((r : ℂ) * t))).continuousAt).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht', show -((r : ℂ) * t) = ((-(r * t) : ℝ) : ℂ) by
      push_cast; ring, norm_exp_ofReal, Real.rpow_one, sub_re, one_re]
    ring_nf; rfl

/-- `∫₀^∞ t^{s-1} e^{-xt}/(1-e^{-t}) dt = Γ(s) ∑ₖ (k+x)^{-s}` for `x > 0`, `Re s > 1`
(Duverney (2.29), (2.89)). -/
theorem integral_cpow_mul_exp_div_one_sub_exp {s : ℂ} (hs : 1 < s.re) {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-((x : ℂ) * t)) / (1 - exp (-(t : ℂ))) =
      Gamma s * ∑' k : ℕ, 1 / ((k : ℂ) + x) ^ s := by
  have hs0 : 0 < s.re := by linarith
  set F : ℕ → ℝ → ℂ := fun k t => (t : ℂ) ^ (s - 1) * exp (-(((k + x : ℝ) : ℂ) * t)) with hF
  have hr (k : ℕ) : (0 : ℝ) < k + x := by positivity
  have hFint (k : ℕ) : Integrable (F k) (volume.restrict (Ioi 0)) :=
    integrableOn_cpow_mul_exp_neg_mul hs0 (hr k)
  have hinv (k : ℕ) : (1 / ((k + x : ℝ) : ℂ)) ^ s = 1 / ((k : ℂ) + x) ^ s := by
    rw [one_div, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg (hr k).le]; exact Real.pi_ne_zero.symm),
      one_div]
    push_cast; rfl
  have hFval (k : ℕ) : ∫ t in Ioi (0 : ℝ), F k t = Gamma s * (1 / ((k : ℂ) + x) ^ s) := by
    rw [integral_cpow_mul_exp_neg_mul_Ioi hs0 (hr k), cpow_neg, one_div]
    push_cast; ring
  have hnorm (k : ℕ) : ∫ t in Ioi (0 : ℝ), ‖F k t‖ = (1 / (k + x)) ^ s.re * Real.Gamma s.re := by
    rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hs0 (hr k)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht', show -(((k + x : ℝ) : ℂ) * t) =
      ((-((k + x) * t) : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal, sub_re, one_re]
  have hsum : Summable fun k => ∫ t in Ioi (0 : ℝ), ‖F k t‖ := by
    simp_rw [hnorm]
    refine Summable.mul_right _ ?_
    have h := (Real.summable_one_div_nat_add_rpow x s.re).mpr hs
    refine h.congr fun k => ?_
    rw [abs_of_pos (hr k), Real.div_rpow zero_le_one (hr k).le, Real.one_rpow]
  have key := integral_tsum_of_summable_integral_norm hFint hsum
  simp_rw [hFval] at key
  rw [← tsum_mul_left, key]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  have hq : ‖exp (-(t : ℂ))‖ < 1 := by
    rw [show -(t : ℂ) = ((-t : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom := (hasSum_geometric_of_norm_lt_one hq).mul_left
    ((t : ℂ) ^ (s - 1) * exp (-((x : ℂ) * t)))
  rw [div_eq_mul_inv, ← hgeom.tsum_eq]
  congr 1
  funext k
  simp only [hF]
  rw [← exp_nat_mul, mul_assoc, ← exp_add]
  congr 2
  push_cast; ring

/-- Hurwitz zeta as a Laplace integral, `Γ(s) ζ(s,a) = ∫₀^∞ t^{s-1} e^{-at}/(1-e^{-t}) dt`
for `0 < a ≤ 1`, `Re s > 1` (Duverney (2.89), DLMF 25.11.25). -/
@[dlmf 25.11.E25]
theorem Gamma_mul_hurwitzZeta_eq_integral {s : ℂ} (hs : 1 < s.re) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a ≤ 1) :
    Gamma s * hurwitzZeta a s =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-((a : ℂ) * t)) / (1 - exp (-(t : ℂ))) := by
  rw [integral_cpow_mul_exp_div_one_sub_exp hs ha0,
    (hasSum_hurwitzZeta_of_one_lt_re ⟨ha0.le, ha1⟩ hs).tsum_eq]

/-- Polygamma as a Laplace integral, `ψ⁽ⁿ⁾(x) = (-1)ⁿ⁺¹ ∫₀^∞ tⁿ e^{-xt}/(1-e^{-t}) dt` for
`x > 0`, `n ≥ 1` (Duverney (2.29), DLMF 5.15.1). -/
theorem polygamma_eq_integral {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    polygamma n x = (-1 : ℂ) ^ (n + 1) *
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * exp (-((x : ℂ) * t)) / (1 - exp (-(t : ℂ))) := by
  have h := integral_cpow_mul_exp_div_one_sub_exp (s := ((n + 1 : ℕ) : ℂ)) (by simp; omega) hx
  rw [show ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial] at h
  simp_rw [show (n : ℂ) + 1 - 1 = (n : ℂ) by ring, show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by
    push_cast; ring, cpow_natCast] at h
  rw [h, polygamma_eq_tsum hn (ofReal_mem_notNegNat hx)]
  have hs : ∑' k : ℕ, ((x : ℂ) + k) ^ (-1 - n : ℤ) = ∑' k : ℕ, 1 / ((k : ℂ) + x) ^ (n + 1) := by
    congr 1; funext k; rw [zpow_neg_one_sub_nat_eq, add_comm]
  rw [hs]
  ring

end DLMF.Gamma

end
