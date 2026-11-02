/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Derivatives
public import DLMF.Hypergeometric.Basic.ParameterAnalyticity
public import DLMF.Hypergeometric.Transformations
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.AbelLimit

/-!
# Regularized contiguous relations and transformations (DLMF §§15.2(ii), 15.5, 15.8)

The analyticity of `regularizedGaussHGFun a b c z` in its parameters, the identity principles
in the parameters and the regularized derivative formulas are in
`DLMF.Hypergeometric.Basic.ParameterAnalyticity`; they extend identities proved under
restrictive parameter hypotheses to all parameters.

## Main results

* `regularizedGaussHGFun_contiguous_a` and the other `regularizedGaussHGFun_contiguous_*`
  lemmas: contiguous relations for all parameters (the generators `contiguous_c` and
  `contiguous_shift_b` are in `DLMF.Hypergeometric.Basic.ParameterAnalyticity`).
* `regularizedGaussHGFun_euler`, `regularizedGaussHGFun_pfaff`,
  `euler_transformation_of_ne_neg_nat`, `pfaff_transformation_of_ne_neg_nat`: Euler's and
  Pfaff's transformations.
* `tendsto_ordinaryHypergeometric_nhdsWithin_one`: Gauss's asymptotic as `x → 1⁻`, DLMF 15.4.23
  (AAR Theorem 2.1.3).

## Implementation notes

The joint statement `entire_regularized_parameters` is in `DLMF.Hypergeometric.AnalyticProperties`
and is not derived here.
-/

@[expose] public section

open Complex Filter Set FormalMultilinearSeries
open scoped Topology

noncomputable section

namespace DLMF.Hypergeometric

/-! ### Regularized contiguous relations (all parameters)

Each identity is the ordinary disk relation, rewritten in `𝐅 = ₂F₁/Γ(c)` and extended
to all `c` by the identity principle. The generators `contiguous_c`, `contiguous_a`,
`contiguous_shift_b`, and `deriv_contiguous_c_succ` are lifted that way; the remaining
neighbours are linear combinations of those regularized identities, matching
`Derivatives.lean`.
-/

/-- 15.5.11 (`contiguous_a`) for the regularized function, valid for all parameters. -/
theorem regularizedGaussHGFun_contiguous_a (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (c - a) * regularizedGaussHGFun (a - 1) b c z +
        (2 * a - c + (b - a) * z) * regularizedGaussHGFun a b c z +
        a * (z - 1) * regularizedGaussHGFun (a + 1) b c z = 0 :=
  eqFun_of_eqOn_not_neg_nat
    (fun c => (c - a) * regularizedGaussHGFun (a - 1) b c z +
      (2 * a - c + (b - a) * z) * regularizedGaussHGFun a b c z +
      a * (z - 1) * regularizedGaussHGFun (a + 1) b c z)
    (fun _ => 0)
    (by intro c _; fun_prop (disch := assumption))
    (by intro c _; fun_prop (disch := assumption))
    (fun c hc => by
      have hΓ0 : Gamma c ≠ 0 := Gamma_ne_zero hc
      have h := contiguous_a (a := a) (b := b) hc hz
      simp only [regularizedGaussHGFun_eq_div_Gamma hc]
      field_simp
      linear_combination h) c

/-- 15.5.12 (`contiguous_ab`): `contiguous_shift_b` minus its `a ↔ b` swap. -/
theorem regularizedGaussHGFun_contiguous_ab (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (b - a) * regularizedGaussHGFun a b c z + a * regularizedGaussHGFun (a + 1) b c z -
      b * regularizedGaussHGFun a (b + 1) c z = 0 := by
  have ha := regularizedGaussHGFun_contiguous_shift_b a b c hz
  have hb := regularizedGaussHGFun_contiguous_shift_b b a c hz
  simp only [regularizedGaussHGFun_symm b a c, regularizedGaussHGFun_symm b (a + 1) c,
    regularizedGaussHGFun_symm (b + 1) (a + 1) (c + 1)] at hb
  linear_combination b * ha - a * hb

/-- 15.5.13 (`contiguous_a_b_pred`): swapped `contiguous_a` plus `(z-1)` times
`contiguous_ab`. -/
theorem regularizedGaussHGFun_contiguous_a_b_pred (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (c - a - b) * regularizedGaussHGFun a b c z +
        a * (1 - z) * regularizedGaussHGFun (a + 1) b c z -
        (c - b) * regularizedGaussHGFun a (b - 1) c z = 0 := by
  have hab := regularizedGaussHGFun_contiguous_ab a b c hz
  have ha := regularizedGaussHGFun_contiguous_a b a c hz
  simp only [regularizedGaussHGFun_symm b a c, regularizedGaussHGFun_symm (b - 1) a c,
    regularizedGaussHGFun_symm (b + 1) a c] at ha
  linear_combination -(ha + (z - 1) * hab)

/-- 15.5.21 (`deriv_contiguous_c_succ`) for the regularized function, valid for all parameters. -/
theorem regularizedGaussHGFun_contiguous_c_succ_deriv (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - z) * (a * b) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z =
      (c - a) * (c - b) * regularizedGaussHGFun a b (c + 1) z +
        (a + b - c) * regularizedGaussHGFun a b c z :=
  eqFun_of_eqOn_not_neg_nat
    (fun c => (1 - z) * (a * b) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z)
    (fun c => (c - a) * (c - b) * regularizedGaussHGFun a b (c + 1) z +
      (a + b - c) * regularizedGaussHGFun a b c z)
    (by intro c _; fun_prop (disch := assumption))
    (by intro c _; fun_prop (disch := assumption))
    (fun c hc => by
      have hc1 := not_neg_nat_add_one hc
      have hΓ0 : Gamma c ≠ 0 := Gamma_ne_zero hc
      have hΓ1 := Gamma_succ_of_not_neg_nat hc
      have hc0 := ne_zero_of_not_neg_nat hc
      have hd : c * deriv (₂F₁ a b c) z = a * b * ₂F₁ (a + 1) (b + 1) (c + 1) z := by
        rw [deriv_ordinaryHypergeometric hc hz]
        field_simp
      have h := deriv_contiguous_c_succ (a := a) (b := b) hc hz
      simp only [regularizedGaussHGFun_eq_div_Gamma hc,
        regularizedGaussHGFun_eq_div_Gamma hc1, hΓ1]
      field_simp [hΓ0, ne_zero_of_not_neg_nat hc]
      linear_combination h - (1 - z) * hd) c

/-- 15.5.14 (`contiguous_a_c_succ`): `-z` times `contiguous_c_succ_deriv` plus
`a(1-z)` times swapped `contiguous_shift_b`. -/
theorem regularizedGaussHGFun_contiguous_a_c_succ (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (a + (b - c) * z) * regularizedGaussHGFun a b c z -
        a * (1 - z) * regularizedGaussHGFun (a + 1) b c z +
        (c - a) * (c - b) * z * regularizedGaussHGFun a b (c + 1) z = 0 := by
  have hd := regularizedGaussHGFun_contiguous_c_succ_deriv a b c hz
  have hs := regularizedGaussHGFun_contiguous_shift_b b a c hz
  simp only [regularizedGaussHGFun_symm b a c, regularizedGaussHGFun_symm b (a + 1) c,
    regularizedGaussHGFun_symm (b + 1) (a + 1) (c + 1)] at hs
  linear_combination -z * hd + a * (1 - z) * hs

/-- 15.5.15 (`contiguous_a_succ_c_pred`): `contiguous_c` at `c-1`. -/
theorem regularizedGaussHGFun_contiguous_a_succ_c_pred (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (c - a - 1) * regularizedGaussHGFun a b c z +
        a * regularizedGaussHGFun (a + 1) b c z -
        regularizedGaussHGFun a b (c - 1) z = 0 := by
  have h := regularizedGaussHGFun_contiguous_c a b (c - 1) hz
  simp only [sub_add_cancel] at h
  have h' :
      regularizedGaussHGFun a b (c - 1) z =
        (c - a - 1) * regularizedGaussHGFun a b c z +
          a * regularizedGaussHGFun (a + 1) b c z := by
    convert h using 2
    ring
  linear_combination -h'

/-- 15.5.16 (`contiguous_a_pred_c_succ`): swapped `contiguous_shift_b` and
`contiguous_c`. -/
theorem regularizedGaussHGFun_contiguous_a_pred_c_succ (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - z) * regularizedGaussHGFun a b c z - regularizedGaussHGFun (a - 1) b c z +
      (c - b) * z * regularizedGaussHGFun a b (c + 1) z = 0 := by
  have hs := regularizedGaussHGFun_contiguous_shift_b b (a - 1) c hz
  have hc' := regularizedGaussHGFun_contiguous_c b a c hz
  simp only [sub_add_cancel, regularizedGaussHGFun_symm b (a - 1) c,
    regularizedGaussHGFun_symm b a c, regularizedGaussHGFun_symm (b + 1) a (c + 1)] at hs
  simp only [regularizedGaussHGFun_symm b a c, regularizedGaussHGFun_symm b a (c + 1),
    regularizedGaussHGFun_symm (b + 1) a (c + 1)] at hc'
  linear_combination -hs - z * hc'

/-- 15.5.17 (`contiguous_a_pred_c_pred`): `contiguous_a` plus `(1-z)` times
`contiguous_a_succ_c_pred`. -/
theorem regularizedGaussHGFun_contiguous_a_pred_c_pred (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (a - 1 + (b + 1 - c) * z) * regularizedGaussHGFun a b c z +
        (c - a) * regularizedGaussHGFun (a - 1) b c z -
        (1 - z) * regularizedGaussHGFun a b (c - 1) z = 0 := by
  have h₁ := regularizedGaussHGFun_contiguous_a a b c hz
  have h₂ := regularizedGaussHGFun_contiguous_a_succ_c_pred a b c hz
  linear_combination h₁ + (1 - z) * h₂

/-- 15.5.18 (`contiguous_c_three`): `contiguous_a_c_succ - contiguous_a + contiguous_a_pred_c_pred`.
-/
theorem regularizedGaussHGFun_contiguous_c_three (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (z - 1) * regularizedGaussHGFun a b (c - 1) z +
        (c - 1 - (2 * c - a - b - 1) * z) * regularizedGaussHGFun a b c z +
        (c - a) * (c - b) * z * regularizedGaussHGFun a b (c + 1) z = 0 := by
  have h₁ := regularizedGaussHGFun_contiguous_a_c_succ a b c hz
  have h₂ := regularizedGaussHGFun_contiguous_a a b c hz
  have h₃ := regularizedGaussHGFun_contiguous_a_pred_c_pred a b c hz
  linear_combination h₁ - h₂ + h₃

/-- 15.5.19 (`contiguous_diagonal`) for the regularized function, valid for all parameters. -/
theorem regularizedGaussHGFun_contiguous_diagonal (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * (1 - z) * (a + 1) * (b + 1) * regularizedGaussHGFun (a + 2) (b + 2) (c + 2) z +
        (c - (a + b + 1) * z) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z -
        regularizedGaussHGFun a b c z = 0 :=
  eqFun_of_eqOn_not_neg_nat
    (fun c => z * (1 - z) * (a + 1) * (b + 1) *
        regularizedGaussHGFun (a + 2) (b + 2) (c + 2) z +
      (c - (a + b + 1) * z) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z -
      regularizedGaussHGFun a b c z)
    (fun _ => 0)
    (by intro c _; fun_prop (disch := assumption))
    (by intro c _; fun_prop (disch := assumption))
    (fun c hc => by
      have hc1 := not_neg_nat_add_one hc
      have hc2 : ∀ k : ℕ, c + 2 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hc 2
      have hΓ0 : Gamma c ≠ 0 := Gamma_ne_zero hc
      have hΓ1 := Gamma_succ_of_not_neg_nat hc
      have hΓ2 : Gamma (c + 2) = (c + 1) * Gamma (c + 1) := by
        simpa [show c + 1 + 1 = c + 2 by ring] using Gamma_succ_of_not_neg_nat hc1
      have h := contiguous_diagonal (a := a) (b := b) hc hz
      simp only [regularizedGaussHGFun_eq_div_Gamma hc,
        regularizedGaussHGFun_eq_div_Gamma hc1, regularizedGaussHGFun_eq_div_Gamma hc2,
        hΓ2, hΓ1]
      field_simp [hΓ0, ne_zero_of_not_neg_nat hc, ne_zero_of_not_neg_nat hc1]
      linear_combination h) c

/-! ### Regularized Euler and Pfaff transformations (all parameters) -/

/-- Euler's transformation 15.8.1 for the regularized function, valid for all parameters:
`𝐅(a,b;c;z) = (1-z)^(c-a-b) 𝐅(c-a,c-b;c;z)`. -/
theorem regularizedGaussHGFun_euler (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      (1 - z) ^ (c - a - b) * regularizedGaussHGFun (c - a) (c - b) c z := by
  have h1z : (1 : ℂ) - z ≠ 0 := by
    intro h
    have : z = 1 := by linear_combination -h
    rw [this, norm_one] at hz
    exact lt_irrefl _ hz
  -- step 1: continuation in `b`, for `0 < Re c`
  have step1 : ∀ c : ℂ, 0 < c.re → ∀ b : ℂ, regularizedGaussHGFun a b c z =
      (1 - z) ^ (c - a - b) * regularizedGaussHGFun (c - a) (c - b) c z := by
    intro c hc b
    have hcpole : ∀ k : ℕ, c ≠ -(k : ℂ) := not_neg_nat_of_re_pos hc
    have hf : AnalyticOnNhd ℂ (fun b => regularizedGaussHGFun a b c z) univ :=
      analyticOnNhd_regularizedGaussHGFun_b a c hz
    have hg : AnalyticOnNhd ℂ (fun b => (1 - z) ^ (c - a - b) *
        regularizedGaussHGFun (c - a) (c - b) c z) univ := by
      intro b _
      have hd : Differentiable ℂ (fun b => (1 - z) ^ (c - a - b) *
          regularizedGaussHGFun (c - a) (c - b) c z) :=
        ((differentiable_const _).sub differentiable_id |>.const_cpow (Or.inl h1z)).mul
          (differentiable_regularizedGaussHGFun_comp (differentiable_const _)
            ((differentiable_const _).sub differentiable_id) (differentiable_const _) hz)
      exact hd.analyticAt b
    have hopen : IsOpen {b : ℂ | 0 < b.re ∧ b.re < c.re} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hne : ({b : ℂ | 0 < b.re ∧ b.re < c.re} : Set ℂ).Nonempty := ⟨c / 2, by
      simp only [Set.mem_ofPred_eq, Complex.div_ofNat_re]
      constructor <;> linarith⟩
    have key := eq_of_analyticOnNhd_univ_of_eqOn hf hg hopen hne fun b hb => by
      obtain ⟨hb0, hbc⟩ := hb
      have hcb : 0 < (c - b).re := by simp only [Complex.sub_re]; linarith
      rw [regularizedGaussHGFun_eq_div_Gamma hcpole, regularizedGaussHGFun_eq_div_Gamma hcpole,
        euler_transformation hb0 hcb hz]
      ring
    exact congrFun key b
  -- step 2: continuation in `c`
  have hf : AnalyticOnNhd ℂ (fun c => regularizedGaussHGFun a b c z) univ :=
    analyticOnNhd_regularizedGaussHGFun_c a b hz
  have hg : AnalyticOnNhd ℂ (fun c => (1 - z) ^ (c - a - b) *
      regularizedGaussHGFun (c - a) (c - b) c z) univ := by
    intro c _
    have hd : Differentiable ℂ (fun c => (1 - z) ^ (c - a - b) *
        regularizedGaussHGFun (c - a) (c - b) c z) :=
      ((differentiable_id.sub (differentiable_const _)).sub (differentiable_const _)
        |>.const_cpow (Or.inl h1z)).mul
        (differentiable_regularizedGaussHGFun_comp (differentiable_id.sub (differentiable_const _))
          (differentiable_id.sub (differentiable_const _)) differentiable_id hz)
    exact hd.analyticAt c
  exact congrFun (eq_of_eqOn_re_pos hf hg fun c hc => step1 c hc b) c

/-- Pfaff's transformation 15.8.1 for the regularized function, valid for all parameters:
`𝐅(a,b;c;z) = (1-z)^(-a) 𝐅(a,c-b;c;z/(z-1))`. -/
theorem regularizedGaussHGFun_pfaff (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    (hzt : ‖z / (z - 1)‖ < 1) :
    regularizedGaussHGFun a b c z =
      (1 - z) ^ (-a) * regularizedGaussHGFun a (c - b) c (z / (z - 1)) := by
  have step1 : ∀ c : ℂ, 0 < c.re → ∀ b : ℂ, regularizedGaussHGFun a b c z =
      (1 - z) ^ (-a) * regularizedGaussHGFun a (c - b) c (z / (z - 1)) := by
    intro c hc b
    have hcpole : ∀ k : ℕ, c ≠ -(k : ℂ) := not_neg_nat_of_re_pos hc
    have hf : AnalyticOnNhd ℂ (fun b => regularizedGaussHGFun a b c z) univ :=
      analyticOnNhd_regularizedGaussHGFun_b a c hz
    have hg : AnalyticOnNhd ℂ (fun b => (1 - z) ^ (-a) *
        regularizedGaussHGFun a (c - b) c (z / (z - 1))) univ := by
      intro b _
      have hd : Differentiable ℂ (fun b => (1 - z) ^ (-a) *
          regularizedGaussHGFun a (c - b) c (z / (z - 1))) :=
        (differentiable_const _).mul
          (differentiable_regularizedGaussHGFun_comp (differentiable_const _)
            ((differentiable_const _).sub differentiable_id) (differentiable_const _) hzt)
      exact hd.analyticAt b
    have hopen : IsOpen {b : ℂ | 0 < b.re ∧ b.re < c.re} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hne : ({b : ℂ | 0 < b.re ∧ b.re < c.re} : Set ℂ).Nonempty := ⟨c / 2, by
      simp only [Set.mem_ofPred_eq, Complex.div_ofNat_re]
      constructor <;> linarith⟩
    have key := eq_of_analyticOnNhd_univ_of_eqOn hf hg hopen hne fun b hb => by
      obtain ⟨hb0, hbc⟩ := hb
      have hcb : 0 < (c - b).re := by simp only [Complex.sub_re]; linarith
      rw [regularizedGaussHGFun_eq_div_Gamma hcpole, regularizedGaussHGFun_eq_div_Gamma hcpole,
        pfaff_transformation hb0 hcb hz hzt]
      ring
    exact congrFun key b
  have hf : AnalyticOnNhd ℂ (fun c => regularizedGaussHGFun a b c z) univ :=
    analyticOnNhd_regularizedGaussHGFun_c a b hz
  have hg : AnalyticOnNhd ℂ (fun c => (1 - z) ^ (-a) *
      regularizedGaussHGFun a (c - b) c (z / (z - 1))) univ := by
    intro c _
    have hd : Differentiable ℂ (fun c => (1 - z) ^ (-a) *
        regularizedGaussHGFun a (c - b) c (z / (z - 1))) :=
      (differentiable_const _).mul
        (differentiable_regularizedGaussHGFun_comp (differentiable_const _)
          (differentiable_id.sub (differentiable_const _)) differentiable_id hzt)
    exact hd.analyticAt c
  exact congrFun (eq_of_eqOn_re_pos hf hg fun c hc => step1 c hc b) c

/-- Euler's transformation 15.8.1 for `₂F₁`, with no hypothesis on `a`, `b`. -/
theorem euler_transformation_of_ne_neg_nat {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) {z : ℂ}
    (hz : ‖z‖ < 1) : ₂F₁ a b c z = (1 - z) ^ (c - a - b) * ₂F₁ (c - a) (c - b) c z := by
  have hΓ : Gamma c ≠ 0 := Gamma_ne_zero hc
  have h := regularizedGaussHGFun_euler a b c hz
  simp only [regularizedGaussHGFun_eq_div_Gamma hc] at h
  rw [div_eq_iff hΓ] at h
  rw [h]
  field_simp

/-- AAR Theorem 2.1.3: Gauss's asymptotic as `x → 1⁻`. By Euler's transformation,
`(1-x)^(a+b-c) F(a,b;c;x) = F(c-a,c-b;c;x)`, which tends to `F(c-a,c-b;c;1)` by Abel's
theorem; Gauss's summation theorem evaluates the limit. -/
@[dlmf 15.4.E23]
theorem tendsto_ordinaryHypergeometric_nhdsWithin_one {a b c : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (h : (c - a - b).re < 0) :
    Tendsto (fun x : ℝ => (1 - x : ℂ) ^ (a + b - c) * ₂F₁ a b c (x : ℂ))
      (𝓝[<] (1 : ℝ)) (𝓝 (Gamma (a + b - c) * Gamma c / (Gamma a * Gamma b))) := by
  have h' : 0 < (c - (c - a) - (c - b)).re := by
    simp only [sub_re] at h ⊢
    linarith
  have hG := gauss_summation (a := c - a) (b := c - b) hc h'
  rw [show c - (c - a) - (c - b) = a + b - c by ring, sub_sub_cancel, sub_sub_cancel,
    ordinaryHypergeometric_one_eq_tsum] at hG
  have hs : Summable (gaussHGCoeff (c - a) (c - b) c) := by
    simpa using ordinaryHypergeometric_summable_of_mem_sphere (z := 1) (by simp) h'
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hs.hasSum.tendsto_sum_nat
  rw [tendsto_map'_iff, hG] at habel
  rw [show Gamma (a + b - c) * Gamma c = Gamma c * Gamma (a + b - c) by ring]
  apply habel.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with x hx
  have hx1 : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact ⟨hx.1, hx.2⟩
  have hx0 : (1 : ℂ) - x ≠ 0 := by
    rw [← ofReal_one, ← ofReal_sub, ofReal_ne_zero]
    linarith [hx.2]
  rw [euler_transformation_of_ne_neg_nat hc hx1, ← mul_assoc, ← cpow_add _ _ hx0,
    show a + b - c + (c - a - b) = 0 by ring, cpow_zero, one_mul, ordinaryHypergeometric_eq_tsum]
  simp only [Function.comp_apply, smul_eq_mul]
  congr 1
  funext n
  simp [gaussHGCoeff, poch, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Pfaff's transformation 15.8.1 for `₂F₁`, with no hypothesis on `a`, `b`. -/
theorem pfaff_transformation_of_ne_neg_nat {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) {z : ℂ}
    (hz : ‖z‖ < 1) (hzt : ‖z / (z - 1)‖ < 1) :
    ₂F₁ a b c z = (1 - z) ^ (-a) * ₂F₁ a (c - b) c (z / (z - 1)) := by
  have hΓ : Gamma c ≠ 0 := Gamma_ne_zero hc
  have h := regularizedGaussHGFun_pfaff a b c hz hzt
  simp only [regularizedGaussHGFun_eq_div_Gamma hc] at h
  rw [div_eq_iff hΓ] at h
  rw [h]
  field_simp

/-! ### Terminating series as functions of the denominator parameter -/

/-- `(c)_k ≠ 0` when `c` avoids `0, -1, …, -(k-1)`. -/
theorem poch_ne_zero_of_lt (c : ℂ) (k : ℕ) (hc : ∀ j : ℕ, j < k → c ≠ -(j : ℂ)) : poch c k ≠ 0 := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    rw [poch_succ]
    refine mul_ne_zero (ih fun j hj => hc j (by omega)) fun h => ?_
    exact hc k (by omega) (by linear_combination h)

/-- The terminating `₂F₁(-n, b; c; z)` is analytic in `c` off `{0, -1, …, -(n-1)}`. -/
theorem analyticOnNhd_gauss_neg_nat_param (n : ℕ) (b z : ℂ) :
    AnalyticOnNhd ℂ (fun c : ℂ => ₂F₁ (-(n : ℂ)) b c z)
        {c : ℂ | ∀ j : ℕ, j < n → c ≠ -(j : ℂ)} := by
  intro c hc
  have heq : (fun c : ℂ => ₂F₁ (-(n : ℂ)) b c z) = fun c => ∑ k ∈ Finset.range (n + 1),
      poch (-(n : ℂ)) k * poch b k / (poch c k * k.factorial) * z ^ k := by
    funext c
    rw [ordinaryHypergeometric_eq_sum_neg_nat]
    rfl
  rw [heq]
  refine Finset.analyticAt_fun_sum (Finset.range (n + 1)) fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hden : poch c k * k.factorial ≠ 0 := mul_ne_zero
    (poch_ne_zero_of_lt c k fun j hj => hc j (lt_of_lt_of_le hj hk'))
    (Nat.cast_ne_zero.mpr k.factorial_ne_zero)
  have hpoch : AnalyticAt ℂ (fun c : ℂ => poch c k * k.factorial) c :=
    ((Polynomial.differentiable (ascPochhammer ℂ k)).analyticAt c).mul analyticAt_const
  exact (AnalyticAt.fun_div (f := fun _ : ℂ => poch (-(n : ℂ)) k * poch b k)
    (g := fun c : ℂ => poch c k * k.factorial) (x := c) analyticAt_const hpoch hden).mul
    analyticAt_const

/-- Gauss's contiguous relation in `a` for a terminating series, valid for every argument. -/
theorem contiguous_a_neg_nat {b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) (z : ℂ) :
    (c + (n + 1)) * ₂F₁ (-((n + 2 : ℕ) : ℂ)) b c z +
      (-(2 * (n + 1)) - c + (b + (n + 1)) * z) * ₂F₁ (-((n + 1 : ℕ) : ℂ)) b c z -
      (n + 1) * (z - 1) * ₂F₁ (-(n : ℂ)) b c z = 0 := by
  set F : ℂ → ℂ := fun z : ℂ => (c + (n + 1)) * ₂F₁ (-((n + 2 : ℕ) : ℂ)) b c z +
      (-(2 * (n + 1)) - c + (b + (n + 1)) * z) * ₂F₁ (-((n + 1 : ℕ) : ℂ)) b c z -
      (n + 1) * (z - 1) * ₂F₁ (-(n : ℂ)) b c z with hF
  have hpoly : ∀ m : ℕ, Differentiable ℂ (fun z : ℂ => ₂F₁ (-(m : ℂ)) b c z) := by
    intro m
    have : (fun z : ℂ => ₂F₁ (-(m : ℂ)) b c z) =
        fun z : ℂ => ∑ k ∈ Finset.range (m + 1), gaussHGCoeff (-(m : ℂ)) b c k * z ^ k := by
      funext z; exact ordinaryHypergeometric_eq_sum_neg_nat m b c z
    rw [this]
    fun_prop
  have hdiff : Differentiable ℂ F := by
    have h2 := hpoly (n + 2); have h1 := hpoly (n + 1); have h0 := hpoly n
    fun_prop
  have hball : ∀ z ∈ Metric.ball (0 : ℂ) 1, F z = 0 := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    have h := contiguous_a (a := -((n + 1 : ℕ) : ℂ)) (b := b) hc hz
    rw [show -((n + 1 : ℕ) : ℂ) - 1 = -((n + 2 : ℕ) : ℂ) by push_cast; ring,
      show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring] at h
    simp only [hF]
    push_cast at h ⊢
    linear_combination h
  have han : AnalyticOnNhd ℂ F Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff
  have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ 0)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds 0 one_pos) hball)
  simpa [hF] using hzero (Set.mem_univ z)

end DLMF.Hypergeometric
