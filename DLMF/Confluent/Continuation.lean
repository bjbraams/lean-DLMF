/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Recurrence

/-!
# Analytic continuation of Kummer's function in its parameters (DLMF §13.2(i))

Mathlib's regularized function `𝐌(a,b,z) = regularizedHGFun {a} {b} z = M(a,b,z)/Γ(b)` is
entire in `a`, in `b` and in `z`. We prove that it is entire along any entire curve in the
parameter plane, and use the identity principle to remove every parameter hypothesis from the
contiguous relations of §13.3, from the derivative formula 13.3.15 and from Kummer's
transformation 13.2.39. The classical statements with hypotheses remain in
`DLMF.Confluent.Recurrence` and `DLMF.Confluent.Basic`.
-/

@[expose] public section

open Complex Filter Set FormalMultilinearSeries DLMF.Hypergeometric
open scoped Real Nat Topology ENNReal

noncomputable section

set_option autoImplicit false

namespace DLMF.Confluent

/-- At a denominator pole, the normalized ordinary Kummer function converges
along the punctured parameter neighborhood to the entire regularized function.
The puncture is essential: the totalized quotient has value zero at the pole. -/
@[dlmf 13.2.E5]
theorem tendsto_kummerM_div_Gamma_at_neg_nat (a : ℂ) (n : ℕ) (z : ℂ) :
    Tendsto (fun b : ℂ => kummerM a b z / Gamma b) (𝓝[≠] (-(n : ℂ)))
      (𝓝 (regularizedHGFun {a} {(-(n : ℂ))} z)) := by
  have ht : Tendsto (fun b => regularizedHGFun {a} {b} z) (𝓝[≠] (-(n : ℂ)))
      (𝓝 (regularizedHGFun {a} {(-(n : ℂ))} z)) :=
    ((analyticOnNhd_regularizedConfluent_b a z) (-(n : ℂ))
      (Set.mem_univ _)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [eventually_nhdsWithin_ne_neg_nat n] with b hb
  exact regularizedConfluent_eq_div_Gamma hb z

/-- 13.3.15 iterated, for the regularized function and all parameters:
`𝐌⁽ⁿ⁾(a,b,z) = (a)ₙ 𝐌(a+n,b+n,z)`. -/
theorem iteratedDeriv_regularizedConfluent (a b : ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (regularizedHGFun {a} {b}) z =
      poch a n * regularizedHGFun {a + n} {b + n} z := by
  induction n generalizing z with
  | zero => simp [iteratedDeriv_zero, poch_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih, deriv_const_mul _ (differentiableAt_regularizedConfluent _ _ _),
      deriv_regularizedConfluent, poch_succ,
      show a + ((n + 1 : ℕ) : ℂ) = a + n + 1 by push_cast; ring,
      show b + ((n + 1 : ℕ) : ℂ) = b + n + 1 by push_cast; ring]
    ring

/-! ### Regularized contiguous relations (all parameters) -/

/-- 13.3.1 (`kummerM_contiguous_a`) for the regularized function, valid for all parameters. -/
theorem regularizedConfluent_contiguous_a (a b z : ℂ) :
    (b - a) * regularizedHGFun {a - 1} {b} z + (2 * a - b + z) * regularizedHGFun {a} {b} z - a * regularizedHGFun {a + 1} {b} z = 0 := by
  have key := eq_of_eqOn_not_neg_nat (f := fun b => (b - a) * regularizedHGFun {a - 1} {b} z + (2 * a - b + z) * regularizedHGFun {a} {b} z - a * regularizedHGFun {a + 1} {b} z)
    (g := fun b => 0) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hb
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have h := kummerM_contiguous_a (a := a) (z := z) hb
  simp only [regularizedConfluent_eq_div_Gamma hb]
  field_simp
  linear_combination h

/-- 13.3.2 (`kummerM_contiguous_b`) for the regularized function, valid for all parameters. -/
theorem regularizedConfluent_contiguous_b (a b z : ℂ) :
    regularizedHGFun {a} {b - 1} z + (1 - b - z) * regularizedHGFun {a} {b} z + z * (b - a) * regularizedHGFun {a} {b + 1} z = 0 := by
  have key := eq_of_eqOn_not_neg_nat_sub_one (f := fun b => regularizedHGFun {a} {b - 1} z + (1 - b - z) * regularizedHGFun {a} {b} z + z * (b - a) * regularizedHGFun {a} {b + 1} z)
    (g := fun b => 0) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hbm
  have hb : ∀ k : ℕ, b ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hbm 1
  have hbm0 : b - 1 ≠ 0 := by simpa using hbm 0
  have hΓm : Gamma b = (b - 1) * Gamma (b - 1) := by
    have := Gamma_add_one (b - 1) hbm0
    rwa [sub_add_cancel] at this
  have hΓm0 : Gamma (b - 1) ≠ 0 := Gamma_ne_zero hbm
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have h := kummerM_contiguous_b (a := a) (z := z) hbm
  simp only [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hbm, regularizedConfluent_eq_div_Gamma hb1, hΓ1, hΓm]
  field_simp
  linear_combination h

/-- 13.3.3 (`kummerM_contiguous_a_b`) for the regularized function, valid for all parameters. -/
theorem regularizedConfluent_contiguous_a_b (a b z : ℂ) :
    (a - b + 1) * regularizedHGFun {a} {b} z - a * regularizedHGFun {a + 1} {b} z + regularizedHGFun {a} {b - 1} z = 0 := by
  have key := eq_of_eqOn_not_neg_nat_sub_one (f := fun b => (a - b + 1) * regularizedHGFun {a} {b} z - a * regularizedHGFun {a + 1} {b} z + regularizedHGFun {a} {b - 1} z)
    (g := fun b => 0) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hbm
  have hb : ∀ k : ℕ, b ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hbm 1
  have hbm0 : b - 1 ≠ 0 := by simpa using hbm 0
  have hΓm : Gamma b = (b - 1) * Gamma (b - 1) := by
    have := Gamma_add_one (b - 1) hbm0
    rwa [sub_add_cancel] at this
  have hΓm0 : Gamma (b - 1) ≠ 0 := Gamma_ne_zero hbm
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have h := kummerM_contiguous_a_b (a := a) (z := z) hbm
  simp only [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hbm, hΓm]
  field_simp
  linear_combination h

/-- 13.3.4 (`kummerM_contiguous_shift_a`) for the regularized function, valid for all parameters. -/
theorem regularizedConfluent_contiguous_shift_a (a b z : ℂ) :
    regularizedHGFun {a} {b} z - regularizedHGFun {a - 1} {b} z - z * regularizedHGFun {a} {b + 1} z = 0 := by
  have key := eq_of_eqOn_not_neg_nat (f := fun b => regularizedHGFun {a} {b} z - regularizedHGFun {a - 1} {b} z - z * regularizedHGFun {a} {b + 1} z)
    (g := fun b => 0) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hb
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have h := kummerM_contiguous_shift_a (a := a) (z := z) hb
  simp only [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hb1, hΓ1]
  field_simp
  linear_combination h

/-- 13.3.5 (`kummerM_contiguous_mixed`) for the regularized function, valid for all parameters. -/
theorem regularizedConfluent_contiguous_mixed (a b z : ℂ) :
    (a + z) * regularizedHGFun {a} {b} z + z * (a - b) * regularizedHGFun {a} {b + 1} z - a * regularizedHGFun {a + 1} {b} z = 0 := by
  have key := eq_of_eqOn_not_neg_nat (f := fun b => (a + z) * regularizedHGFun {a} {b} z + z * (a - b) * regularizedHGFun {a} {b + 1} z - a * regularizedHGFun {a + 1} {b} z)
    (g := fun b => 0) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hb
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have h := kummerM_contiguous_mixed (a := a) (z := z) hb
  simp only [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hb1, hΓ1]
  field_simp
  linear_combination h

/-- 13.3.6 (`kummerM_contiguous_down`) for the regularized function, valid for all parameters. -/
theorem regularizedConfluent_contiguous_down (a b z : ℂ) :
    (a - 1 + z) * regularizedHGFun {a} {b} z + (b - a) * regularizedHGFun {a - 1} {b} z - regularizedHGFun {a} {b - 1} z = 0 := by
  have key := eq_of_eqOn_not_neg_nat_sub_one (f := fun b => (a - 1 + z) * regularizedHGFun {a} {b} z + (b - a) * regularizedHGFun {a - 1} {b} z - regularizedHGFun {a} {b - 1} z)
    (g := fun b => 0) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hbm
  have hb : ∀ k : ℕ, b ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hbm 1
  have hbm0 : b - 1 ≠ 0 := by simpa using hbm 0
  have hΓm : Gamma b = (b - 1) * Gamma (b - 1) := by
    have := Gamma_add_one (b - 1) hbm0
    rwa [sub_add_cancel] at this
  have hΓm0 : Gamma (b - 1) ≠ 0 := Gamma_ne_zero hbm
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have h := kummerM_contiguous_down (a := a) (z := z) hbm
  simp only [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hbm, hΓm]
  field_simp
  linear_combination h

/-- `kummerM_contiguous_shift_b_succ` for the regularized function, valid for all parameters. -/
theorem regularizedConfluent_contiguous_shift_b_succ (a b z : ℂ) :
    a * regularizedHGFun {a + 1} {b + 1} z = (a - b) * regularizedHGFun {a} {b + 1} z + regularizedHGFun {a} {b} z := by
  have key := eq_of_eqOn_not_neg_nat (f := fun b => a * regularizedHGFun {a + 1} {b + 1} z)
    (g := fun b => (a - b) * regularizedHGFun {a} {b + 1} z + regularizedHGFun {a} {b} z) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hb
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have h := kummerM_contiguous_shift_b_succ (a := a) (z := z) hb
  simp only [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hb1, hΓ1]
  field_simp
  linear_combination h

/-- `kummerM_contiguous_mixed_b_pred` for the regularized function, valid for all parameters. -/
theorem regularizedConfluent_contiguous_mixed_b_pred (a b z : ℂ) :
    (b - 1) * regularizedHGFun {a} {b} z - regularizedHGFun {a} {b - 1} z + a * z * regularizedHGFun {a + 1} {b + 1} z = 0 := by
  have key := eq_of_eqOn_not_neg_nat_sub_one (f := fun b => (b - 1) * regularizedHGFun {a} {b} z - regularizedHGFun {a} {b - 1} z + a * z * regularizedHGFun {a + 1} {b + 1} z)
    (g := fun b => 0) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hbm
  have hb : ∀ k : ℕ, b ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hbm 1
  have hbm0 : b - 1 ≠ 0 := by simpa using hbm 0
  have hΓm : Gamma b = (b - 1) * Gamma (b - 1) := by
    have := Gamma_add_one (b - 1) hbm0
    rwa [sub_add_cancel] at this
  have hΓm0 : Gamma (b - 1) ≠ 0 := Gamma_ne_zero hbm
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have h := kummerM_contiguous_mixed_b_pred (a := a) (z := z) hbm
  simp only [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hbm, regularizedConfluent_eq_div_Gamma hb1, hΓ1, hΓm]
  field_simp
  linear_combination h

/-- 13.3.13 (`kummerM_ode_contiguous`) for the regularized function, valid for all
parameters. -/
theorem regularizedConfluent_ode_contiguous (a b z : ℂ) :
    (a + 1) * z * regularizedHGFun {a + 2} {b + 2} z + (b - z) * regularizedHGFun {a + 1} {b + 1} z -
      regularizedHGFun {a} {b} z = 0 := by
  have key := eq_of_eqOn_not_neg_nat (f := fun b => (a + 1) * z * regularizedHGFun {a + 2} {b + 2} z +
      (b - z) * regularizedHGFun {a + 1} {b + 1} z - regularizedHGFun {a} {b} z)
    (g := fun b => 0) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hb
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb2 : ∀ k : ℕ, b + 2 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 2
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hb10 : b + 1 ≠ 0 := by simpa using hb1 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have hΓ2 : Gamma (b + 2) = (b + 1) * Gamma (b + 1) := by
    have := Gamma_add_one (b + 1) hb10
    rwa [show b + 1 + 1 = b + 2 by ring] at this
  have h := kummerM_ode_contiguous (a := a) (z := z) hb
  simp only [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hb1, regularizedConfluent_eq_div_Gamma hb2, hΓ2, hΓ1]
  field_simp
  linear_combination h

/-- Kummer's transformation 13.2.39 for the regularized function, valid for all parameters:
`𝐌(a,b,z) = e^z 𝐌(b-a,b,-z)`. -/
theorem regularizedConfluent_kummer_transform (a b z : ℂ) :
    regularizedHGFun {a} {b} z = exp z * regularizedHGFun {b - a} {b} (-z) := by
  have key := eq_of_eqOn_not_neg_nat (f := fun b => regularizedHGFun {a} {b} z)
    (g := fun b => exp z * regularizedHGFun {b - a} {b} (-z)) (by intro b _; fun_prop)
    (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hb
  rw [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hb, kummerM_kummer_transform hb]
  ring

end DLMF.Confluent
