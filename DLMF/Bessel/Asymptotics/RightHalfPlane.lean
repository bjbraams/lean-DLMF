/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Asymptotics.RightHalfPlane
public import DLMF.Bessel.Asymptotics

/-!
# Modified Bessel asymptotics in the right half-plane

Kummer's relation and the uniform Euler-integral expansion give the leading term
of `I_ν(z)` as `z` tends to infinity with `δ |z| ≤ re z`, for `δ > 0` and `re ν > -1/2`.
The normalization agrees with DLMF 10.40.1.
-/

@[expose] public noncomputable section
open Complex Filter Set Asymptotics
open scoped Real Topology Nat
open DLMF.Hypergeometric DLMF.Confluent

namespace DLMF.Bessel

/-- Kummer's relation expresses `I_ν` through the regularized confluent function off the cut. -/
theorem besselI_eq_mul_regularizedConfluent_of_mem_slitPlane {ν z : ℂ}
    (hν : ∀ k : ℕ, 1 + 2 * ν ≠ -k) (hz : z ∈ slitPlane) :
    (z / 2) ^ ν * exp (-z) * Gamma (2 * ν + 1) / Gamma (ν + 1) *
      regularizedHGFun {ν + 1 / 2} {2 * ν + 1} (2 * z) = besselI ν z := by
  have hb : ∀ k : ℕ, 2 * ν + 1 ≠ -k := fun k h => hν k (by linear_combination h)
  have hK := DLMF.Confluent.kummerM_besselI ν z hz hν
  rw [DLMF.Confluent.kummerM_eq_mul_regularizedHGFun hb] at hK
  have hG1 : Gamma (ν + 1) ≠ 0 := Gamma_ne_zero fun k h => hν (2 * k + 1) (by
    push_cast; linear_combination 2 * h)
  have hz0 : z / 2 ≠ 0 := div_ne_zero (slitPlane_ne_zero hz) two_ne_zero
  have hp : (z / 2) ^ ν * (z / 2) ^ (-ν) = 1 := by
    rw [cpow_neg, mul_inv_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl hz0))]
  have he : exp (-z) * exp z = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  rw [add_comm (1 : ℂ) ν] at hK
  calc _ = (z / 2) ^ ν * exp (-z) / Gamma (ν + 1) *
        (Gamma (2 * ν + 1) * regularizedHGFun {ν + 1 / 2} {2 * ν + 1} (2 * z)) := by ring
    _ = ((z / 2) ^ ν * (z / 2) ^ (-ν)) * (exp (-z) * exp z) *
        (Gamma (ν + 1) / Gamma (ν + 1)) * besselI ν z := by rw [hK]; ring
    _ = _ := by rw [hp, he, div_self hG1]; ring

/-- Gamma duplication makes the dominant Kummer term independent of the Bessel order. -/
theorem besselI_main_term_of_ne_zero {ν z : ℂ} (hν : ∀ k : ℕ, 1 + 2 * ν ≠ -k)
    (hz : z ≠ 0) :
    (z / 2) ^ ν * exp (-z) * Gamma (2 * ν + 1) / Gamma (ν + 1) *
      (exp (2 * z) * (2 * z) ^ (ν + 1 / 2 - (2 * ν + 1)) / Gamma (ν + 1 / 2)) =
      exp z * (2 * z) ^ (-1 / 2 : ℂ) / (Real.sqrt π : ℂ) := by
  have hdup := Complex.Gamma_mul_Gamma_add_half (ν + 1 / 2)
  have h2 : (2 : ℂ) ^ (1 - 2 * (ν + 1 / 2)) = exp ((Real.log 2 : ℂ) * (-2 * ν)) := by
    rw [← Complex.ofReal_cpow_eq_exp two_pos, ofReal_ofNat]
    congr 1
    ring
  rw [h2, show ν + 1 / 2 + 1 / 2 = ν + 1 by ring,
    show 2 * (ν + 1 / 2) = 2 * ν + 1 by ring] at hdup
  have ha : Gamma (ν + 1 / 2) ≠ 0 := Gamma_ne_zero fun k h => hν (2 * k) (by
    push_cast; linear_combination 2 * h)
  have hb : Gamma (ν + 1) ≠ 0 := Gamma_ne_zero fun k h => hν (2 * k + 1) (by
    push_cast; linear_combination 2 * h)
  have hs : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hE := exp_ne_zero ((Real.log 2 : ℂ) * (-2 * ν))
  have key : Gamma (2 * ν + 1) / Gamma (ν + 1) / Gamma (ν + 1 / 2) =
      1 / (exp ((Real.log 2 : ℂ) * (-2 * ν)) * (Real.sqrt π : ℂ)) := by
    rw [div_div, div_eq_div_iff (mul_ne_zero hb ha) (mul_ne_zero hE hs)]
    linear_combination -hdup
  have hlog : log (z / 2) = log z - (Real.log 2 : ℂ) := by
    rw [show z / 2 = ((1 / 2 : ℝ) : ℂ) * z by push_cast; ring,
      log_ofReal_mul (by norm_num : (0 : ℝ) < 1 / 2) hz]
    simp [sub_eq_add_neg, add_comm]
  rw [cpow_def_of_ne_zero (div_ne_zero hz two_ne_zero), hlog,
    cpow_def_of_ne_zero (mul_ne_zero two_ne_zero hz),
    cpow_def_of_ne_zero (mul_ne_zero two_ne_zero hz),
    show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl, log_ofReal_mul two_pos hz]
  norm_num only [ofReal_ofNat]
  calc _ = exp ((log z - Real.log 2) * ν) * exp (-z) * exp (2 * z) *
        exp ((Real.log 2 + log z) * (ν + 1 / 2 - (2 * ν + 1))) *
        (Gamma (2 * ν + 1) / Gamma (ν + 1) / Gamma (ν + 1 / 2)) := by ring
    _ = _ := by
      rw [key]
      field_simp
      simp only [← exp_add]
      congr 1
      ring

/-- `I_ν(z) ~ e^z (2z)^(-1/2)/√π` uniformly in closed right-half-plane sectors
for `re ν > -1/2`. -/
theorem besselI_isEquivalent_sector {ν : ℂ} (hνre : -1 / 2 < ν.re)
    {δ : ℝ} (hδ : 0 < δ) :
    IsEquivalent (sectorAtTop δ) (fun z : ℂ => besselI ν z)
      (fun z : ℂ => exp z * (2 * z) ^ (-1 / 2 : ℂ) / (Real.sqrt π : ℂ)) := by
  have ha : 0 < (ν + 1 / 2).re := by simp; linarith
  have hba : 0 < (2 * ν + 1 - (ν + 1 / 2)).re := by simp; linarith
  have hν : ∀ k : ℕ, 1 + 2 * ν ≠ -k := by
    intro k hk
    have h := congrArg Complex.re hk
    simp at h
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hb : Gamma (2 * ν + 1) ≠ 0 := Gamma_ne_zero fun k hk => hν k (by
    linear_combination hk)
  have h1 : Gamma (ν + 1) ≠ 0 := Gamma_ne_zero fun k hk => hν (2 * k + 1) (by
    push_cast; linear_combination 2 * hk)
  have hM := (DLMF.Confluent.tendsto_regularizedHGFun_mul_exp_neg_sector ha hba hδ).comp
    (tendsto_two_mul_sectorAtTop δ)
  apply isEquivalent_of_tendsto_one
  refine hM.congr' ?_
  refine eventually_sectorAtTop (R := 1) fun z hz hsector => ?_
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
  have hzre : 0 < z.re := lt_of_lt_of_le (mul_pos hδ (by positivity : 0 < ‖z‖)) hsector
  have hP : (z / 2) ^ ν * exp (-z) * Gamma (2 * ν + 1) / Gamma (ν + 1) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (cpow_ne_zero_iff.mpr
      (Or.inl (div_ne_zero hz0 two_ne_zero))) (exp_ne_zero _)) hb) h1
  dsimp only [Function.comp_apply, Pi.div_apply]
  rw [← besselI_eq_mul_regularizedConfluent_of_mem_slitPlane hν (Or.inl hzre),
    ← besselI_main_term_of_ne_zero hν hz0]
  rw [mul_div_mul_left _ _ hP]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- The leading modified-Bessel approximation has relative error `O(1/z)` uniformly in
closed right-half-plane sectors, for `re ν > -1/2`. -/
theorem besselI_sub_main_isBigO_sector {ν : ℂ} (hνre : -1 / 2 < ν.re)
    {δ : ℝ} (hδ : 0 < δ) :
    (fun z : ℂ => besselI ν z - exp z * (2 * z) ^ (-1 / 2 : ℂ) / (Real.sqrt π : ℂ))
      =O[sectorAtTop δ]
      (fun z : ℂ => exp z * (2 * z) ^ (-1 / 2 : ℂ) / (Real.sqrt π : ℂ) / z) := by
  have ha : 0 < (ν + 1 / 2).re := by simp; linarith
  have hba : 0 < (2 * ν + 1 - (ν + 1 / 2)).re := by simp; linarith
  have hν : ∀ k : ℕ, 1 + 2 * ν ≠ -k := by
    intro k hk
    have h := congrArg Complex.re hk
    simp at h
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hGa : Gamma (ν + 1 / 2) ≠ 0 := Gamma_ne_zero fun k hk => by
    have h := congrArg Complex.re hk
    simp at h
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hM := (hasAsymptoticExpansion_regularizedConfluent_sector_of_re_pos ha hba hδ 1).comp_tendsto
    (tendsto_two_mul_sectorAtTop δ)
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, sub_zero,
    kummerCoeff_zero, smul_eq_mul, Nat.cast_one] at hM
  set P : ℂ → ℂ := fun z => (z / 2) ^ ν * exp (-z) * Gamma (2 * ν + 1) / Gamma (ν + 1)
  have h := (isBigO_refl P (sectorAtTop δ)).mul hM
  refine (h.congr' ?_ EventuallyEq.rfl).trans ?_
  · refine eventually_sectorAtTop (R := 1) fun z hz hs => ?_
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have hzre : 0 < z.re := lt_of_lt_of_le (mul_pos hδ (by positivity : 0 < ‖z‖)) hs
    dsimp only [P, Function.comp_apply]
    rw [mul_sub, besselI_eq_mul_regularizedConfluent_of_mem_slitPlane hν (Or.inl hzre)]
    congr 1
    convert besselI_main_term_of_ne_zero hν hz0 using 1; ring
  · have hb := isBigO_const_mul_self (Gamma (ν + 1 / 2) / 2)
      (fun z : ℂ => exp z * (2 * z) ^ (-1 / 2 : ℂ) / (Real.sqrt π : ℂ) / z)
      (sectorAtTop δ)
    refine hb.congr' ?_ EventuallyEq.rfl
    refine eventually_sectorAtTop (R := 1) fun z hz _ => ?_
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    dsimp only [P, Function.comp_apply]
    rw [← besselI_main_term_of_ne_zero hν hz0]
    have hpow : (2 * z) ^ (ν + 1 / 2 - (2 * ν + 1) - 1) =
        (2 * z) ^ (ν + 1 / 2 - (2 * ν + 1)) / (2 * z) := by
      rw [cpow_sub _ _ (mul_ne_zero two_ne_zero hz0), cpow_one]
    rw [hpow]
    generalize Gamma (ν + 1 / 2) = G at hGa ⊢
    field_simp [hGa]


end DLMF.Bessel
