/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Products
public import DLMF.Theta.Identities

/-!
# Theta functions: values at `z = 0` (DLMF §20.4)

Values of `θⱼ` and their `z`-derivatives at `z = 0`, in the lattice form with `q = e^{iπτ}`,
`q^{1/4} = e^{iπτ/4}` and `Im τ > 0`. Infinite products are stated with `HasProd` over
`k : ℕ` with `n = k + 1`; the `q`-Pochhammer form uses the project's `qPochhammerInf`.
The vanishing statements 20.4.1 and 20.4.7 follow from the parity of the theta functions.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic DLMF.QSeries

/-- Odd-order derivatives of an even function vanish at `0`. -/
lemma th20_iteratedDeriv_even_zero {f : ℂ → ℂ} (hf : ∀ z, f (-z) = f z) {n : ℕ}
    (hn : Odd n) : iteratedDeriv n f 0 = 0 := by
  have h := iteratedDeriv_comp_neg n f 0
  simp only [hf, neg_zero, hn.neg_one_pow, smul_eq_mul, neg_one_mul] at h
  have : (fun x => f x) = f := rfl
  rw [this] at h
  exact CharZero.eq_neg_self_iff.mp h

/-- Even-order derivatives of an odd function vanish at `0`. -/
lemma th20_iteratedDeriv_odd_zero {f : ℂ → ℂ} (hf : ∀ z, f (-z) = -f z) {n : ℕ}
    (hn : Even n) : iteratedDeriv n f 0 = 0 := by
  have h := iteratedDeriv_comp_neg n f 0
  simp only [hf, neg_zero, hn.neg_one_pow, one_smul] at h
  rw [show (fun x => -f x) = -f from rfl, iteratedDeriv_neg] at h
  exact CharZero.eq_neg_self_iff.mp h.symm

/-- DLMF 20.4.1: `θ₁(0,q) = θ₂'(0,q) = θ₃'(0,q) = θ₄'(0,q) = 0` (for every `τ`). -/
@[dlmf 20.4.E1]
theorem jacobiTheta_zero_values (τ : ℂ) :
    jacobiThetaOneTau 0 τ = 0 ∧ deriv (fun z => jacobiThetaTwoTau z τ) 0 = 0 ∧
      deriv (fun z => jacobiThetaThreeTau z τ) 0 = 0 ∧
      deriv (fun z => jacobiThetaFourTau z τ) 0 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using jacobiThetaOneTau_lattice_eq_zero τ 0 0
  · simpa using th20_iteratedDeriv_even_zero (f := fun z => jacobiThetaTwoTau z τ)
      (fun z => jacobiThetaTwoTau_neg z τ) (n := 1) odd_one
  · simpa using th20_iteratedDeriv_even_zero (f := fun z => jacobiThetaThreeTau z τ)
      (fun z => jacobiThetaThreeTau_neg z τ) (n := 1) odd_one
  · simpa using th20_iteratedDeriv_even_zero (f := fun z => jacobiThetaFourTau z τ)
      (fun z => jacobiThetaFourTau_neg z τ) (n := 1) odd_one

/-- DLMF 20.4.7: `θ₁''(0,q) = θ₂'''(0,q) = θ₃'''(0,q) = θ₄'''(0,q) = 0` (for every `τ`). -/
@[dlmf 20.4.E7]
theorem jacobiTheta_iteratedDeriv_zero_values (τ : ℂ) :
    iteratedDeriv 2 (fun z => jacobiThetaOneTau z τ) 0 = 0 ∧
      iteratedDeriv 3 (fun z => jacobiThetaTwoTau z τ) 0 = 0 ∧
      iteratedDeriv 3 (fun z => jacobiThetaThreeTau z τ) 0 = 0 ∧
      iteratedDeriv 3 (fun z => jacobiThetaFourTau z τ) 0 = 0 := by
  have h3 : Odd 3 := by decide
  exact ⟨th20_iteratedDeriv_odd_zero (fun z => jacobiThetaOneTau_neg z τ) even_two,
    th20_iteratedDeriv_even_zero (fun z => jacobiThetaTwoTau_neg z τ) h3,
    th20_iteratedDeriv_even_zero (fun z => jacobiThetaThreeTau_neg z τ) h3,
    th20_iteratedDeriv_even_zero (fun z => jacobiThetaFourTau_neg z τ) h3⟩

/-- `‖cos 2w‖ ≤ e^{2|Im w|}` (helper). -/
lemma p20R1_norm_cos_two_le (w : ℂ) : ‖cos (2 * w)‖ ≤ Real.exp (2 * |w.im|) := by
  obtain ⟨e1, e2⟩ := p20R1_norm_exp_two_I w
  have h := th20_exp_add_inv w
  have : cos (2 * w) = (cexp (2 * I * w) + (cexp (2 * I * w))⁻¹) / 2 := by rw [h]; ring
  rw [this, norm_div]
  have : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [this]
  linarith [norm_add_le (cexp (2 * I * w)) (cexp (2 * I * w))⁻¹]

/-- `p20R1_F` is even (helper). -/
lemma p20R1_F_even (b Q w : ℂ) : p20R1_F b Q (-w) = p20R1_F b Q w := by
  simp only [p20R1_F, mul_neg, cos_neg]

/-- `p20R1_F` is entire (helper). -/
lemma p20R1_F_differentiable {b Q : ℂ} (hQ : ‖Q‖ < 1) : Differentiable ℂ (p20R1_F b Q) := by
  intro w₀
  set R := |w₀.im| + 1
  set U : Set ℂ := {w | |w.im| < R}
  have hU : IsOpen U := isOpen_lt (continuous_abs.comp continuous_im) continuous_const
  have hw₀ : w₀ ∈ U := by show |w₀.im| < R; linarith
  set g : ℕ → ℂ → ℂ := fun k w => -2 * (b * Q ^ k) * cos (2 * w) + (b * Q ^ k) ^ 2 with hg
  have hQ0 : 0 ≤ ‖Q‖ := norm_nonneg _
  have hgb : ∀ k : ℕ, ∀ w ∈ U, ‖g k w‖ ≤ (2 * ‖b‖ * Real.exp (2 * R) + ‖b‖ ^ 2) * ‖Q‖ ^ k := by
    intro k w hw
    have hc : ‖cos (2 * w)‖ ≤ Real.exp (2 * R) := (p20R1_norm_cos_two_le w).trans
      (Real.exp_le_exp.mpr (by have : |w.im| < R := hw; linarith))
    have hq : ‖Q‖ ^ k ≤ 1 := pow_le_one₀ hQ0 hQ.le
    have hq2 : (‖Q‖ ^ k) ^ 2 ≤ ‖Q‖ ^ k := by
      rw [sq]; exact mul_le_of_le_one_left (by positivity) hq
    calc ‖g k w‖ ≤ ‖-2 * (b * Q ^ k) * cos (2 * w)‖ + ‖(b * Q ^ k) ^ 2‖ := norm_add_le _ _
      _ = 2 * ‖b‖ * ‖Q‖ ^ k * ‖cos (2 * w)‖ + ‖b‖ ^ 2 * (‖Q‖ ^ k) ^ 2 := by
          simp only [norm_mul, norm_pow, norm_neg]; norm_num; ring
      _ ≤ 2 * ‖b‖ * ‖Q‖ ^ k * Real.exp (2 * R) + ‖b‖ ^ 2 * ‖Q‖ ^ k := by gcongr
      _ = (2 * ‖b‖ * Real.exp (2 * R) + ‖b‖ ^ 2) * ‖Q‖ ^ k := by ring
  have hsumu := (summable_geometric_of_lt_one hQ0 hQ).mul_left (2 * ‖b‖ * Real.exp (2 * R) + ‖b‖ ^ 2)
  have hloc : HasProdLocallyUniformlyOn (fun k w => 1 + g k w) (fun w => ∏' k, (1 + g k w)) U :=
    hsumu.hasProdLocallyUniformlyOn_nat_one_add hU (.of_forall fun k w hw => hgb k w hw)
      (fun k => by simp only [hg]; fun_prop)
  have hdiff : DifferentiableOn ℂ (fun w => ∏' k, (1 + g k w)) U :=
    hloc.differentiableOn (.of_forall fun s => by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun _ _ => by
        simp only [hg]; fun_prop)) hU
  have hFdef : p20R1_F b Q = fun w => ∏' k : ℕ, (1 + g k w) := by
    funext w; simp only [p20R1_F, hg]; congr 1; funext k; ring
  rw [hFdef]; exact (hdiff w₀ hw₀).differentiableAt (hU.mem_nhds hw₀)

/-- `F''(0)/F(0) = 8 ∑ bQ^k/(1 - bQ^k)²` for `F = p20R1_F b Q` (helper for 20.4.8–20.4.11). -/
lemma p20R1_F_second {b Q : ℂ} (hQ : ‖Q‖ < 1) (hb : ‖b‖ < 1) :
    p20R1_F b Q 0 ≠ 0 ∧
    HasSum (fun k : ℕ => 8 * (b * Q ^ k) / (1 - b * Q ^ k) ^ 2)
      (iteratedDeriv 2 (p20R1_F b Q) 0 / p20R1_F b Q 0) := by
  have hFd := p20R1_F_differentiable (b := b) hQ
  set s := ‖b‖ with hsdef
  have hs0 : 0 ≤ s := norm_nonneg _
  set c := Real.log (2 / (1 + s)) / 2 with hc
  have hlog : 0 < Real.log (2 / (1 + s)) :=
    Real.log_pos (by rw [lt_div_iff₀ (by linarith)]; linarith)
  have hc0 : 0 < c := by positivity
  have hbc : s * Real.exp (2 * c) < 1 := by
    rw [hc, show 2 * (Real.log (2 / (1 + s)) / 2) = Real.log (2 / (1 + s)) by ring,
      Real.exp_log (by positivity), mul_div_assoc', div_lt_one (by linarith)]; linarith
  set U : Set ℂ := {w | |w.im| < c} with hUdef
  have hU : IsOpen U := isOpen_lt (continuous_abs.comp continuous_im) continuous_const
  have h0U : (0 : ℂ) ∈ U := by show |(0 : ℂ).im| < c; simpa using hc0
  have hexp : ∀ w ∈ U, Real.exp (2 * |w.im|) ≤ Real.exp (2 * c) := fun w hw =>
    Real.exp_le_exp.mpr (by have : |w.im| < c := hw; linarith)
  have hbw : ∀ w ∈ U, ‖b‖ * Real.exp (2 * |w.im|) < 1 := fun w hw =>
    (mul_le_mul_of_nonneg_left (hexp w hw) hs0).trans_lt hbc
  have hQ0 : 0 ≤ ‖Q‖ := norm_nonneg _
  have hak : ∀ k : ℕ, ‖b * Q ^ k‖ ≤ s := fun k => by
    rw [norm_mul, norm_pow]; exact mul_le_of_le_one_right hs0 (pow_le_one₀ hQ0 hQ.le)
  have hak' : ∀ k : ℕ, ‖b * Q ^ k‖ = s * ‖Q‖ ^ k := fun k => by rw [norm_mul, norm_pow]
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℂ → ℂ, T = fun k w => 4 * (b * Q ^ k) * sin (2 * w) /
      (1 - 2 * (b * Q ^ k) * cos (2 * w) + (b * Q ^ k) ^ 2) := ⟨_, rfl⟩
  have hfne : ∀ k : ℕ, ∀ w ∈ U, 1 - 2 * (b * Q ^ k) * cos (2 * w) + (b * Q ^ k) ^ 2 ≠ 0 := by
    intro k w hw
    rw [p20R1_factor]
    obtain ⟨e1, e2⟩ := p20R1_norm_exp_two_I w
    have h := hbw w hw
    refine mul_ne_zero (one_sub_ne_zero_of_norm_lt_one ?_) (one_sub_ne_zero_of_norm_lt_one ?_)
    · rw [norm_mul]; exact (mul_le_mul (hak k) e1 (norm_nonneg _) hs0).trans_lt h
    · rw [norm_mul]; exact (mul_le_mul (hak k) e2 (norm_nonneg _) hs0).trans_lt h
  have hTb : ∀ k : ℕ, ∀ w ∈ U, ‖T k w‖ ≤
      4 * Real.exp (2 * c) * (s * ‖Q‖ ^ k) / (1 - s * Real.exp (2 * c)) ^ 2 := by
    intro k w hw
    have hq := (p20R1_bound_quot (x := b * Q ^ k) (z := w) (R := s) (ρ := s * Real.exp (2 * c))
      (hak k) (mul_le_mul_of_nonneg_left (hexp w hw) hs0) hbc).1
    have hsin : ‖sin (2 * w)‖ ≤ Real.exp (2 * c) := by
      refine (p20R1_norm_sin_le _).trans (Real.exp_le_exp.mpr ?_)
      have : |w.im| < c := hw
      have him : (2 * w).im = 2 * w.im := by simp
      rw [him, abs_mul]; norm_num; linarith
    have hrw : T k w = 4 * sin (2 * w) * (b * Q ^ k /
        (1 - 2 * (b * Q ^ k) * cos (2 * w) + (b * Q ^ k) ^ 2)) := by rw [hT]; ring
    rw [hrw, norm_mul, norm_mul, ← hak' k]
    have : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [this]
    calc 4 * ‖sin (2 * w)‖ * ‖b * Q ^ k / (1 - 2 * (b * Q ^ k) * cos (2 * w) + (b * Q ^ k) ^ 2)‖
        ≤ 4 * Real.exp (2 * c) * (‖b * Q ^ k‖ / (1 - s * Real.exp (2 * c)) ^ 2) := by gcongr
      _ = _ := by ring
  have hTs : Summable (fun k : ℕ =>
      4 * Real.exp (2 * c) * (s * ‖Q‖ ^ k) / (1 - s * Real.exp (2 * c)) ^ 2) :=
    (((summable_geometric_of_lt_one hQ0 hQ).mul_left s).mul_left _).div_const _
  have hTd : ∀ k : ℕ, DifferentiableOn ℂ (T k) U := fun k w hw => by
    rw [hT]
    exact ((by fun_prop : DifferentiableAt ℂ (fun w => 4 * (b * Q ^ k) * sin (2 * w)) w).div
      (by fun_prop) (hfne k w hw)).differentiableWithinAt
  have hSd := hasSum_deriv_of_summable_norm hTs hTd hU hTb h0U
  have hSdiff : DifferentiableAt ℂ (fun w => ∑' k, T k w) 0 :=
    (differentiableOn_tsum_of_summable_norm hTs hTd hU hTb 0 h0U).differentiableAt
      (hU.mem_nhds h0U)
  have hev : deriv (p20R1_F b Q) =ᶠ[𝓝 0] fun w => p20R1_F b Q w * ∑' k, T k w := by
    filter_upwards [hU.mem_nhds h0U] with w hw
    obtain ⟨hFw, -, hS1, -⟩ := p20R1_logDeriv_core hQ (hbw w hw)
    have : ∑' k, T k w = logDeriv (p20R1_F b Q) w := by rw [hT]; exact hS1.tsum_eq
    rw [this, logDeriv_apply]
    field_simp
  have hF'0 : deriv (p20R1_F b Q) 0 = 0 := by
    have := th20_iteratedDeriv_even_zero (f := p20R1_F b Q) (fun w => p20R1_F_even b Q w)
      (n := 1) odd_one
    simpa using this
  have hS0 : ∑' k, T k 0 = 0 := by simp [hT]
  have h2 : iteratedDeriv 2 (p20R1_F b Q) 0 = p20R1_F b Q 0 * deriv (fun w => ∑' k, T k w) 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq, deriv_fun_mul (hFd 0) hSdiff, hF'0,
      hS0]
    ring
  have hF0 : p20R1_F b Q 0 ≠ 0 := (p20R1_logDeriv_core hQ (hbw 0 h0U)).1
  refine ⟨hF0, ?_⟩
  rw [h2, mul_div_cancel_left₀ _ hF0]
  convert hSd using 1
  funext k
  have hD0 : 1 - 2 * (b * Q ^ k) * cos (2 * (0 : ℂ)) + (b * Q ^ k) ^ 2 ≠ 0 := hfne k 0 h0U
  have h0 : HasDerivAt (fun w : ℂ => 2 * w) 2 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul (2 : ℂ)
  have hN := (h0.csin).const_mul (4 * (b * Q ^ k))
  have hD := ((h0.ccos).const_mul (2 * (b * Q ^ k))).const_sub 1 |>.add_const ((b * Q ^ k) ^ 2)
  have hq := hN.div hD (by simpa using hD0)
  rw [hT]
  refine (HasDerivAt.deriv ?_).symm
  convert hq using 1
  simp only [mul_zero, sin_zero, cos_zero]
  have : (1 : ℂ) - 2 * (b * Q ^ k) * 1 + (b * Q ^ k) ^ 2 = (1 - b * Q ^ k) ^ 2 := by ring
  have hD0' : (1 - b * Q ^ k) ^ 2 ≠ 0 := by
    rw [← this]; simpa using hD0
  rw [this, zero_mul, sub_zero]
  field_simp
  ring

/-- `p20R1_F` has differentiable first and second derivatives (helper). -/
lemma p20R1_F_deriv_diff {b Q : ℂ} (hQ : ‖Q‖ < 1) :
    Differentiable ℂ (deriv (p20R1_F b Q)) ∧ Differentiable ℂ (deriv (deriv (p20R1_F b Q))) := by
  have h0 : ContDiff ℂ (⊤ : ℕ∞) (p20R1_F b Q) := (p20R1_F_differentiable hQ).contDiff
  have h1 := (contDiff_infty_iff_deriv.mp h0).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  exact ⟨h1.differentiable (by simp), h2.differentiable (by simp)⟩

/-- Product representation of the four theta functions through `p20R1_F` (helper). -/
lemma p20R1_theta_eq_F {τ : ℂ} (hτ : 0 < τ.im) :
    (fun w => jacobiThetaOneTau w τ) = (fun w => (2 * cexp (π * I * τ / 4) *
      ∏' k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) * sin w *
        p20R1_F (cexp (π * I * τ) ^ 2) (cexp (π * I * τ) ^ 2) w) ∧
    (fun w => jacobiThetaTwoTau w τ) = (fun w => (2 * cexp (π * I * τ / 4) *
      ∏' k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) * cos w *
        p20R1_F (-cexp (π * I * τ) ^ 2) (cexp (π * I * τ) ^ 2) w) ∧
    (fun w => jacobiThetaThreeTau w τ) = (fun w => (∏' k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) *
        p20R1_F (-cexp (π * I * τ)) (cexp (π * I * τ) ^ 2) w) ∧
    (fun w => jacobiThetaFourTau w τ) = (fun w => (∏' k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) *
        p20R1_F (cexp (π * I * τ)) (cexp (π * I * τ) ^ 2) w) := by
  set E := cexp (π * I * τ) with hE
  have hQ : ‖E ^ 2‖ < 1 := th20_norm_nome_sq_lt_one hτ
  obtain ⟨hPm, -⟩ := p20R1_P_mult_ne hτ
  have hpow : ∀ k : ℕ, E ^ 2 * (E ^ 2) ^ k = E ^ (2 * (k + 1)) := fun k => by
    rw [← pow_mul, ← pow_add]; ring_nf
  have hpow4 : ∀ k : ℕ, E ^ (4 * (k + 1)) = (E ^ (2 * (k + 1))) ^ 2 := fun k => by
    rw [← pow_mul]; ring_nf
  have hpo : ∀ k : ℕ, E * (E ^ 2) ^ k = E ^ (2 * k + 1) := fun k => by
    rw [← pow_mul, ← pow_succ']
  have hpo4 : ∀ k : ℕ, E ^ (4 * k + 2) = (E ^ (2 * k + 1)) ^ 2 := fun k => by
    rw [← pow_mul]; ring_nf
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext w
  · rw [(jacobiThetaOneTau_hasProd w hτ).2]
    have hc : ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
        (1 - 2 * E ^ (2 * (k + 1)) * cos (2 * w) + E ^ (4 * (k + 1)))) =
        ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
          (1 - 2 * (E ^ 2 * (E ^ 2) ^ k) * cos (2 * w) + (E ^ 2 * (E ^ 2) ^ k) ^ 2)) :=
      tprod_congr fun k => by rw [hpow, hpow4]
    rw [hc, hPm.tprod_mul (p20R1_F_mult _ _ w hQ), p20R1_F]
    ring
  · rw [(jacobiThetaTwoTau_hasProd w hτ).2]
    have hc : ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
        (1 + 2 * E ^ (2 * (k + 1)) * cos (2 * w) + E ^ (4 * (k + 1)))) =
        ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
          (1 - 2 * (-E ^ 2 * (E ^ 2) ^ k) * cos (2 * w) + (-E ^ 2 * (E ^ 2) ^ k) ^ 2)) :=
      tprod_congr fun k => by rw [neg_mul, hpow, hpow4]; ring
    rw [hc, hPm.tprod_mul (p20R1_F_mult _ _ w hQ), p20R1_F]
    ring
  · rw [(jacobiThetaThreeTau_hasProd w hτ).2]
    have hc : ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
        (1 + 2 * E ^ (2 * k + 1) * cos (2 * w) + E ^ (4 * k + 2))) =
        ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
          (1 - 2 * (-E * (E ^ 2) ^ k) * cos (2 * w) + (-E * (E ^ 2) ^ k) ^ 2)) :=
      tprod_congr fun k => by rw [neg_mul, hpo, hpo4]; ring
    rw [hc, hPm.tprod_mul (p20R1_F_mult _ _ w hQ), p20R1_F]
  · rw [(jacobiThetaFourTau_hasProd w hτ).2]
    have hc : ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
        (1 - 2 * E ^ (2 * k + 1) * cos (2 * w) + E ^ (4 * k + 2))) =
        ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
          (1 - 2 * (E * (E ^ 2) ^ k) * cos (2 * w) + (E * (E ^ 2) ^ k) ^ 2)) :=
      tprod_congr fun k => by rw [hpo, hpo4]
    rw [hc, hPm.tprod_mul (p20R1_F_mult _ _ w hQ), p20R1_F]

/-- `θ₁⁽³⁾(0)/θ₁'(0) = -1 + 3 F''(0)/F(0)` (helper). -/
lemma p20R1_ratio1 {τ : ℂ} (hτ : 0 < τ.im) :
    iteratedDeriv 3 (fun z => jacobiThetaOneTau z τ) 0 / jacobiThetaOneDerivNullTau τ =
      -1 + 3 * (iteratedDeriv 2 (p20R1_F (cexp (π * I * τ) ^ 2) (cexp (π * I * τ) ^ 2)) 0 /
        p20R1_F (cexp (π * I * τ) ^ 2) (cexp (π * I * τ) ^ 2) 0) := by
  set E := cexp (π * I * τ) with hE
  have hQ : ‖E ^ 2‖ < 1 := th20_norm_nome_sq_lt_one hτ
  obtain ⟨hF0, hS⟩ := p20R1_F_second (b := E ^ 2) hQ hQ
  obtain ⟨hd1, hd2⟩ := p20R1_F_deriv_diff (b := E ^ 2) hQ
  have hFd := p20R1_F_differentiable (b := E ^ 2) hQ
  obtain ⟨-, hPne⟩ := p20R1_P_mult_ne hτ
  set F := p20R1_F (E ^ 2) (E ^ 2) with hF
  set C := 2 * cexp (π * I * τ / 4) * ∏' k : ℕ, (1 - E ^ (2 * (k + 1))) with hC
  have hC0 : C ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (exp_ne_zero _)) hPne
  have hfun := (p20R1_theta_eq_F hτ).1
  have hF'0 : deriv F 0 = 0 := by
    have := th20_iteratedDeriv_even_zero (f := F) (fun w => p20R1_F_even _ _ w) (n := 1) odd_one
    simpa using this
  have e1 : deriv (fun w => C * sin w * F w) =
      fun w => C * cos w * F w + C * sin w * deriv F w := by
    funext w
    exact (((hasDerivAt_sin w).const_mul C).mul (hFd w).hasDerivAt).deriv
  have e2 : deriv (fun w => C * cos w * F w + C * sin w * deriv F w) =
      fun w => (C * -sin w * F w + C * cos w * deriv F w) +
        (C * cos w * deriv F w + C * sin w * deriv (deriv F) w) := by
    funext w
    exact ((((hasDerivAt_cos w).const_mul C).mul (hFd w).hasDerivAt).add
      (((hasDerivAt_sin w).const_mul C).mul (hd1 w).hasDerivAt)).deriv
  have e3 : deriv (fun w => (C * -sin w * F w + C * cos w * deriv F w) +
        (C * cos w * deriv F w + C * sin w * deriv (deriv F) w)) 0 =
      -C * F 0 + 3 * C * deriv (deriv F) 0 := by
    refine (HasDerivAt.deriv (((((hasDerivAt_sin 0).neg.const_mul C).mul (hFd 0).hasDerivAt).add
      (((hasDerivAt_cos 0).const_mul C).mul (hd1 0).hasDerivAt)).add
      ((((hasDerivAt_cos 0).const_mul C).mul (hd1 0).hasDerivAt).add
      (((hasDerivAt_sin 0).const_mul C).mul (hd2 0).hasDerivAt)))).trans ?_
    simp [hF'0]; ring
  have h3 : iteratedDeriv 3 (fun z => jacobiThetaOneTau z τ) 0 =
      -C * F 0 + 3 * C * iteratedDeriv 2 F 0 := by
    rw [hfun, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, e1, e2, e3,
      iteratedDeriv_succ, iteratedDeriv_one]
  have h1 : jacobiThetaOneDerivNullTau τ = C * F 0 := by
    rw [jacobiThetaOneDerivNullTau, hfun, e1]; simp
  rw [h3, h1]
  field_simp

/-- `θ₂''(0)/θ₂(0) = -1 + F''(0)/F(0)` (helper). -/
lemma p20R1_ratio2 {τ : ℂ} (hτ : 0 < τ.im) :
    iteratedDeriv 2 (fun z => jacobiThetaTwoTau z τ) 0 / jacobiThetaTwoNullTau τ =
      -1 + iteratedDeriv 2 (p20R1_F (-cexp (π * I * τ) ^ 2) (cexp (π * I * τ) ^ 2)) 0 /
        p20R1_F (-cexp (π * I * τ) ^ 2) (cexp (π * I * τ) ^ 2) 0 := by
  set E := cexp (π * I * τ) with hE
  have hQ : ‖E ^ 2‖ < 1 := th20_norm_nome_sq_lt_one hτ
  have hb : ‖-E ^ 2‖ < 1 := by rwa [norm_neg]
  obtain ⟨hF0, hS⟩ := p20R1_F_second (b := -E ^ 2) hQ hb
  obtain ⟨hd1, -⟩ := p20R1_F_deriv_diff (b := -E ^ 2) hQ
  have hFd := p20R1_F_differentiable (b := -E ^ 2) hQ
  obtain ⟨-, hPne⟩ := p20R1_P_mult_ne hτ
  set F := p20R1_F (-E ^ 2) (E ^ 2) with hF
  set C := 2 * cexp (π * I * τ / 4) * ∏' k : ℕ, (1 - E ^ (2 * (k + 1))) with hC
  have hC0 : C ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (exp_ne_zero _)) hPne
  have hfun := (p20R1_theta_eq_F hτ).2.1
  have hF'0 : deriv F 0 = 0 := by
    have := th20_iteratedDeriv_even_zero (f := F) (fun w => p20R1_F_even _ _ w) (n := 1) odd_one
    simpa using this
  have e1 : deriv (fun w => C * cos w * F w) =
      fun w => C * -sin w * F w + C * cos w * deriv F w := by
    funext w
    exact (((hasDerivAt_cos w).const_mul C).mul (hFd w).hasDerivAt).deriv
  have e2 : deriv (fun w => C * -sin w * F w + C * cos w * deriv F w) 0 =
      -C * F 0 + C * deriv (deriv F) 0 := by
    refine (HasDerivAt.deriv ((((hasDerivAt_sin 0).neg.const_mul C).mul (hFd 0).hasDerivAt).add
      (((hasDerivAt_cos 0).const_mul C).mul (hd1 0).hasDerivAt))).trans ?_
    simp [hF'0]
  have h2 : iteratedDeriv 2 (fun z => jacobiThetaTwoTau z τ) 0 =
      -C * F 0 + C * iteratedDeriv 2 F 0 := by
    rw [hfun, iteratedDeriv_succ, iteratedDeriv_one, e1, e2, iteratedDeriv_succ, iteratedDeriv_one]
  have h0 : jacobiThetaTwoNullTau τ = C * F 0 := by
    rw [jacobiThetaTwoNullTau, show jacobiThetaTwoTau 0 τ = C * cos 0 * F 0 from congrFun hfun 0]
    simp
  rw [h2, h0]
  field_simp

/-- `θ''(0)/θ(0) = F''(0)/F(0)` for `θ₃`, `θ₄` (helper). -/
lemma p20R1_ratio3 {τ : ℂ} (hτ : 0 < τ.im) :
    iteratedDeriv 2 (fun z => jacobiThetaThreeTau z τ) 0 / jacobiThetaThreeNullTau τ =
      iteratedDeriv 2 (p20R1_F (-cexp (π * I * τ)) (cexp (π * I * τ) ^ 2)) 0 /
        p20R1_F (-cexp (π * I * τ)) (cexp (π * I * τ) ^ 2) 0 := by
  obtain ⟨-, hPne⟩ := p20R1_P_mult_ne hτ
  have hfun := (p20R1_theta_eq_F hτ).2.2.1
  rw [jacobiThetaThreeNullTau, show jacobiThetaThreeTau 0 τ = (∏' k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) *
    p20R1_F (-cexp (π * I * τ)) (cexp (π * I * τ) ^ 2) 0 from congrFun hfun 0, hfun,
    iteratedDeriv_const_mul_field, mul_div_mul_left _ _ hPne]

/-- `θ''(0)/θ(0) = F''(0)/F(0)` for `θ₃`, `θ₄` (helper). -/
lemma p20R1_ratio4 {τ : ℂ} (hτ : 0 < τ.im) :
    iteratedDeriv 2 (fun z => jacobiThetaFourTau z τ) 0 / jacobiThetaFourNullTau τ =
      iteratedDeriv 2 (p20R1_F (cexp (π * I * τ)) (cexp (π * I * τ) ^ 2)) 0 /
        p20R1_F (cexp (π * I * τ)) (cexp (π * I * τ) ^ 2) 0 := by
  obtain ⟨-, hPne⟩ := p20R1_P_mult_ne hτ
  have hfun := (p20R1_theta_eq_F hτ).2.2.2
  rw [jacobiThetaFourNullTau, show jacobiThetaFourTau 0 τ = (∏' k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) *
    p20R1_F (cexp (π * I * τ)) (cexp (π * I * τ) ^ 2) 0 from congrFun hfun 0, hfun,
    iteratedDeriv_const_mul_field, mul_div_mul_left _ _ hPne]

/-- Second derivative at `0` of a product of two functions with vanishing first derivatives
there (helper). -/
lemma p20R1_even_mul {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hf' : Differentiable ℂ (deriv f)) (hg' : Differentiable ℂ (deriv g))
    (hf0 : deriv f 0 = 0) (hg0 : deriv g 0 = 0) :
    Differentiable ℂ (fun z => f z * g z) ∧ Differentiable ℂ (deriv (fun z => f z * g z)) ∧
      deriv (fun z => f z * g z) 0 = 0 ∧
      iteratedDeriv 2 (fun z => f z * g z) 0 = iteratedDeriv 2 f 0 * g 0 + f 0 * iteratedDeriv 2 g 0 := by
  have hd : deriv (fun z => f z * g z) = fun z => deriv f z * g z + f z * deriv g z := by
    funext z; exact ((hf z).hasDerivAt.mul (hg z).hasDerivAt).deriv
  have hdd : Differentiable ℂ (fun z => deriv f z * g z + f z * deriv g z) :=
    (hf'.mul hg).add (hf.mul hg')
  refine ⟨hf.mul hg, hd ▸ hdd, by
    rw [hd]; show deriv f 0 * g 0 + f 0 * deriv g 0 = 0; rw [hf0, hg0]; ring, ?_⟩
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd, iteratedDeriv_succ, iteratedDeriv_one,
    iteratedDeriv_succ, iteratedDeriv_one]
  refine (HasDerivAt.deriv ((((hf' 0).hasDerivAt.mul (hg 0).hasDerivAt)).add
    ((hf 0).hasDerivAt.mul (hg' 0).hasDerivAt))).trans ?_
  rw [hf0, hg0]; ring

/-- Data of `p20R1_F` used for 20.4.12 (helper). -/
lemma p20R1_F_data {b Q : ℂ} (hQ : ‖Q‖ < 1) :
    Differentiable ℂ (p20R1_F b Q) ∧ Differentiable ℂ (deriv (p20R1_F b Q)) ∧
      deriv (p20R1_F b Q) 0 = 0 :=
  ⟨p20R1_F_differentiable hQ, (p20R1_F_deriv_diff hQ).1, by
    have := th20_iteratedDeriv_even_zero (f := p20R1_F b Q) (fun w => p20R1_F_even _ _ w)
      (n := 1) odd_one
    simpa using this⟩

/-- `sin z cos z ≠ 0` for `0 < ‖z‖ < 1` (helper). -/
lemma p20R1_sin_cos_ne {z : ℂ} (h0 : z ≠ 0) (h1 : ‖z‖ < 1 / 2) : sin z * cos z ≠ 0 := by
  have hpi := Real.two_le_pi
  refine mul_ne_zero (fun hs => ?_) (fun hc => ?_)
  · obtain ⟨k, hk⟩ := sin_eq_zero_iff.mp hs
    have hz : z = k * π := hk
    have hk0 : k ≠ 0 := by rintro rfl; apply h0; rw [hz]; simp
    have : ‖z‖ = |(k : ℝ)| * π := by
      rw [hz, norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
    nlinarith
  · obtain ⟨k, hk⟩ := cos_eq_zero_iff.mp hc
    have : ‖z‖ = |(2 * (k : ℝ) + 1)| * π / 2 := by
      rw [hk, show (2 * (k : ℂ) + 1) * π / 2 = (((2 * (k : ℝ) + 1) * π / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos Real.pi_pos]
      norm_num
    have hk1 : (1 : ℝ) ≤ |(2 * (k : ℝ) + 1)| := by
      rw [show (2 * (k : ℝ) + 1) = ((2 * k + 1 : ℤ) : ℝ) by push_cast; ring, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by omega)
    nlinarith

/-- DLMF 20.4.8: `θ₁'''(0,q)/θ₁'(0,q) = -1 + 24 ∑_{n≥1} q^{2n}/(1 - q^{2n})²`, `Im τ > 0`. -/
@[dlmf 20.4.E8]
theorem jacobiThetaOne_third_deriv_ratio {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun k : ℕ => 24 * cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 - cexp (π * I * τ) ^ (2 * (k + 1))) ^ 2)
      (iteratedDeriv 3 (fun z => jacobiThetaOneTau z τ) 0 / jacobiThetaOneDerivNullTau τ + 1) := by
  rw [p20R1_ratio1 hτ]
  set E := cexp (π * I * τ) with hE
  have hQ : ‖E ^ 2‖ < 1 := th20_norm_nome_sq_lt_one hτ
  obtain ⟨-, hS⟩ := p20R1_F_second (b := E ^ 2) hQ hQ
  rw [show ∀ x : ℂ, -1 + 3 * x + 1 = 3 * x from fun x => by ring]
  convert hS.mul_left 3 using 1
  funext k
  rw [show E ^ 2 * (E ^ 2) ^ k = E ^ (2 * (k + 1)) by rw [← pow_mul, ← pow_add]; ring_nf]
  ring

/-- DLMF 20.4.9: `θ₂''(0,q)/θ₂(0,q) = -1 - 8 ∑_{n≥1} q^{2n}/(1 + q^{2n})²`, `Im τ > 0`. -/
@[dlmf 20.4.E9]
theorem jacobiThetaTwo_second_deriv_ratio {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun k : ℕ => 8 * cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 + cexp (π * I * τ) ^ (2 * (k + 1))) ^ 2)
      (-1 - iteratedDeriv 2 (fun z => jacobiThetaTwoTau z τ) 0 / jacobiThetaTwoNullTau τ) := by
  rw [p20R1_ratio2 hτ]
  set E := cexp (π * I * τ) with hE
  have hQ : ‖E ^ 2‖ < 1 := th20_norm_nome_sq_lt_one hτ
  have hb : ‖-E ^ 2‖ < 1 := by rwa [norm_neg]
  obtain ⟨-, hS⟩ := p20R1_F_second (b := -E ^ 2) hQ hb
  rw [show ∀ x : ℂ, -1 - (-1 + x) = -x from fun x => by ring]
  convert hS.neg using 1
  funext k
  rw [show -E ^ 2 * (E ^ 2) ^ k = -E ^ (2 * (k + 1)) by rw [neg_mul, ← pow_mul, ← pow_add]; ring_nf]
  ring

/-- DLMF 20.4.10: `θ₃''(0,q)/θ₃(0,q) = -8 ∑_{n≥1} q^{2n-1}/(1 + q^{2n-1})²`, `Im τ > 0`. -/
@[dlmf 20.4.E10]
theorem jacobiThetaThree_second_deriv_ratio {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun k : ℕ => -8 * cexp (π * I * τ) ^ (2 * k + 1) /
        (1 + cexp (π * I * τ) ^ (2 * k + 1)) ^ 2)
      (iteratedDeriv 2 (fun z => jacobiThetaThreeTau z τ) 0 / jacobiThetaThreeNullTau τ) := by
  set E := cexp (π * I * τ) with hE
  have hQ : ‖E ^ 2‖ < 1 := th20_norm_nome_sq_lt_one hτ
  have hb : ‖-E‖ < 1 := by rw [norm_neg]; exact th20_norm_nome_lt_one hτ
  obtain ⟨hF0, hS⟩ := p20R1_F_second (b := -E) hQ hb
  obtain ⟨-, hPne⟩ := p20R1_P_mult_ne hτ
  have hfun := (p20R1_theta_eq_F hτ).2.2.1
  rw [jacobiThetaThreeNullTau, show jacobiThetaThreeTau 0 τ = (∏' k : ℕ, (1 - E ^ (2 * (k + 1)))) * p20R1_F (-E) (E ^ 2) 0 from
    congrFun hfun 0, hfun, iteratedDeriv_const_mul_field, mul_div_mul_left _ _ hPne]
  convert hS using 1
  funext k
  rw [show -E * (E ^ 2) ^ k = -E ^ (2 * k + 1) by rw [neg_mul, ← pow_mul, ← pow_succ']]
  ring

/-- DLMF 20.4.11: `θ₄''(0,q)/θ₄(0,q) = 8 ∑_{n≥1} q^{2n-1}/(1 - q^{2n-1})²`, `Im τ > 0`. -/
@[dlmf 20.4.E11]
theorem jacobiThetaFour_second_deriv_ratio {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun k : ℕ => 8 * cexp (π * I * τ) ^ (2 * k + 1) /
        (1 - cexp (π * I * τ) ^ (2 * k + 1)) ^ 2)
      (iteratedDeriv 2 (fun z => jacobiThetaFourTau z τ) 0 / jacobiThetaFourNullTau τ) := by
  set E := cexp (π * I * τ) with hE
  have hQ : ‖E ^ 2‖ < 1 := th20_norm_nome_sq_lt_one hτ
  have hb : ‖E‖ < 1 := th20_norm_nome_lt_one hτ
  obtain ⟨hF0, hS⟩ := p20R1_F_second (b := E) hQ hb
  obtain ⟨-, hPne⟩ := p20R1_P_mult_ne hτ
  have hfun := (p20R1_theta_eq_F hτ).2.2.2
  rw [jacobiThetaFourNullTau, show jacobiThetaFourTau 0 τ = (∏' k : ℕ, (1 - E ^ (2 * (k + 1)))) * p20R1_F E (E ^ 2) 0 from
    congrFun hfun 0, hfun, iteratedDeriv_const_mul_field, mul_div_mul_left _ _ hPne]
  convert hS using 1
  funext k
  rw [show E * (E ^ 2) ^ k = E ^ (2 * k + 1) by rw [← pow_mul, ← pow_succ']]

/-- DLMF 20.4.12: `θ₁'''(0)/θ₁'(0) = θ₂''(0)/θ₂(0) + θ₃''(0)/θ₃(0) + θ₄''(0)/θ₄(0)`, `Im τ > 0`. -/
@[dlmf 20.4.E12]
theorem jacobiTheta_deriv_ratio_sum {τ : ℂ} (hτ : 0 < τ.im) :
    iteratedDeriv 3 (fun z => jacobiThetaOneTau z τ) 0 / jacobiThetaOneDerivNullTau τ =
      iteratedDeriv 2 (fun z => jacobiThetaTwoTau z τ) 0 / jacobiThetaTwoNullTau τ +
      iteratedDeriv 2 (fun z => jacobiThetaThreeTau z τ) 0 / jacobiThetaThreeNullTau τ +
      iteratedDeriv 2 (fun z => jacobiThetaFourTau z τ) 0 / jacobiThetaFourNullTau τ := by
  set E := cexp (π * I * τ) with hE
  have hQ : ‖E ^ 2‖ < 1 := th20_norm_nome_sq_lt_one hτ
  have hE1 : ‖E‖ < 1 := th20_norm_nome_lt_one hτ
  have hb2 : ‖-E ^ 2‖ < 1 := by rwa [norm_neg]
  have hb3 : ‖-E‖ < 1 := by rwa [norm_neg]
  obtain ⟨n1, -⟩ := p20R1_F_second (b := E ^ 2) hQ hQ
  obtain ⟨n2, -⟩ := p20R1_F_second (b := -E ^ 2) hQ hb2
  obtain ⟨n3, -⟩ := p20R1_F_second (b := -E) hQ hb3
  obtain ⟨n4, -⟩ := p20R1_F_second (b := E) hQ hE1
  obtain ⟨d1, d1', z1⟩ := p20R1_F_data (b := E ^ 2) hQ
  obtain ⟨d2, d2', z2⟩ := p20R1_F_data (b := -E ^ 2) hQ
  obtain ⟨d3, d3', z3⟩ := p20R1_F_data (b := -E) hQ
  obtain ⟨d4, d4', z4⟩ := p20R1_F_data (b := E) hQ
  set F1 := p20R1_F (E ^ 2) (E ^ 2) with hF1
  set F2 := p20R1_F (-E ^ 2) (E ^ 2) with hF2
  set F3 := p20R1_F (-E) (E ^ 2) with hF3
  set F4 := p20R1_F E (E ^ 2) with hF4
  obtain ⟨-, hPne⟩ := p20R1_P_mult_ne hτ
  set P := ∏' k : ℕ, (1 - E ^ (2 * (k + 1))) with hP
  set C := 2 * cexp (π * I * τ / 4) * P with hC
  have hC0 : C ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (exp_ne_zero _)) hPne
  obtain ⟨f1, f2, f3, f4⟩ := p20R1_theta_eq_F hτ
  obtain ⟨m2, m3, m4⟩ := jacobiThetaNullTau_ne_zero hτ
  set N := jacobiThetaTwoNullTau τ * jacobiThetaThreeNullTau τ * jacobiThetaFourNullTau τ with hN
  have hN0 : N ≠ 0 := mul_ne_zero (mul_ne_zero m2 m3) m4
  set κ := C * P ^ 2 / N with hκ
  -- the product identity `F₁(2z) = κ F₁F₂F₃F₄(z)`
  set G : ℂ → ℂ := fun z => F1 z * F2 z * F3 z * F4 z with hG
  have hrel : ∀ z : ℂ, sin z * cos z ≠ 0 → F1 (2 * z) = κ * G z := by
    intro z hz
    have h := jacobiThetaOneTau_two_mul z τ hτ
    rw [show jacobiThetaOneTau (2 * z) τ = C * sin (2 * z) * F1 (2 * z) from congrFun f1 (2 * z),
      show jacobiThetaOneTau z τ = C * sin z * F1 z from congrFun f1 z,
      show jacobiThetaTwoTau z τ = C * cos z * F2 z from congrFun f2 z,
      show jacobiThetaThreeTau z τ = P * F3 z from congrFun f3 z,
      show jacobiThetaFourTau z τ = P * F4 z from congrFun f4 z, sin_two_mul, ← hN] at h
    rw [eq_div_iff hN0] at h
    rw [hκ, hG, div_mul_eq_mul_div, eq_div_iff hN0]
    have hz2 : 2 * C * (sin z * cos z) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hC0) hz
    apply mul_left_cancel₀ hz2
    linear_combination h
  have hcont : Continuous (fun z => F1 (2 * z) - κ * G z) := by
    have := d1.continuous; have := d2.continuous; have := d3.continuous; have := d4.continuous
    rw [hG]; fun_prop
  have hev : (fun z => F1 (2 * z)) =ᶠ[𝓝 0] fun z => κ * G z := by
    have hball : ∀ᶠ z in 𝓝 (0 : ℂ), ‖z‖ < 1 / 2 := by
      have : Metric.ball (0 : ℂ) (1 / 2) ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ (by norm_num)
      filter_upwards [this] with z hz; simpa using hz
    filter_upwards [hball] with z hz
    by_cases h0 : z = 0
    · subst h0
      have hpunct : ∀ᶠ w in 𝓝[≠] (0 : ℂ), F1 (2 * w) - κ * G w = 0 := by
        filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with w hw hw0
        rw [hrel w (p20R1_sin_cos_ne hw0 hw)]; ring
      have t1 : Tendsto (fun w => F1 (2 * w) - κ * G w) (𝓝[≠] (0 : ℂ))
          (𝓝 (F1 (2 * 0) - κ * G 0)) := (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      have t2 : Tendsto (fun w => F1 (2 * w) - κ * G w) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
        tendsto_const_nhds.congr' (EventuallyEq.symm hpunct)
      exact sub_eq_zero.mp (tendsto_nhds_unique t1 t2)
    · exact hrel z (p20R1_sin_cos_ne h0 hz)
  -- second derivatives
  obtain ⟨g12, g12', g12z, g12d⟩ := p20R1_even_mul d1 d2 d1' d2' z1 z2
  obtain ⟨g123, g123', g123z, g123d⟩ := p20R1_even_mul g12 d3 g12' d3' g12z z3
  obtain ⟨-, -, -, g1234d⟩ := p20R1_even_mul g123 d4 g123' d4' g123z z4
  have hGd : iteratedDeriv 2 G 0 = ((iteratedDeriv 2 F1 0 * F2 0 + F1 0 * iteratedDeriv 2 F2 0) *
      F3 0 + F1 0 * F2 0 * iteratedDeriv 2 F3 0) * F4 0 +
      F1 0 * F2 0 * F3 0 * iteratedDeriv 2 F4 0 := by
    rw [hG, g1234d, g123d, g12d]
  have h20 : HasDerivAt (fun z : ℂ => 2 * z) 2 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul (2 : ℂ)
  have hD1 : deriv (fun z => F1 (2 * z)) = fun z => deriv F1 (2 * z) * 2 := by
    funext z
    have h2z : HasDerivAt (fun z : ℂ => 2 * z) 2 z := by
      simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
    exact ((d1 (2 * z)).hasDerivAt.comp z h2z).deriv
  have hD2 : iteratedDeriv 2 (fun z => F1 (2 * z)) 0 = 4 * iteratedDeriv 2 F1 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hD1, iteratedDeriv_succ, iteratedDeriv_one]
    refine (HasDerivAt.deriv (((d1' (2 * 0)).hasDerivAt.comp 0 h20).mul_const (2 : ℂ))).trans ?_
    simp; ring
  have hE2 : iteratedDeriv 2 (fun z => F1 (2 * z)) 0 = κ * iteratedDeriv 2 G 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv.deriv_eq]
    have := iteratedDeriv_const_mul_field (n := 2) (x := 0) κ G
    rw [iteratedDeriv_succ, iteratedDeriv_one] at this
    exact this
  have hval : F1 0 = κ * G 0 := by simpa using hev.eq_of_nhds
  rw [hD2, hGd] at hE2
  rw [hG] at hval
  have hk1 : κ * (F2 0 * F3 0 * F4 0) = 1 := by
    have : F1 0 * (κ * (F2 0 * F3 0 * F4 0) - 1) = 0 := by linear_combination -hval
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left n1)
  rw [p20R1_ratio1 hτ, p20R1_ratio2 hτ, p20R1_ratio3 hτ, p20R1_ratio4 hτ]
  rw [← hF1, ← hF2, ← hF3, ← hF4]
  set r1 := iteratedDeriv 2 F1 0 / F1 0 with hr1
  set r2 := iteratedDeriv 2 F2 0 / F2 0 with hr2
  set r3 := iteratedDeriv 2 F3 0 / F3 0 with hr3
  set r4 := iteratedDeriv 2 F4 0 / F4 0 with hr4
  have a1 : iteratedDeriv 2 F1 0 = r1 * F1 0 := (div_mul_cancel₀ _ n1).symm
  have a2 : iteratedDeriv 2 F2 0 = r2 * F2 0 := (div_mul_cancel₀ _ n2).symm
  have a3 : iteratedDeriv 2 F3 0 = r3 * F3 0 := (div_mul_cancel₀ _ n3).symm
  have a4 : iteratedDeriv 2 F4 0 = r4 * F4 0 := (div_mul_cancel₀ _ n4).symm
  rw [a1, a2, a3, a4] at hE2
  have key : F1 0 * (3 * r1 - r2 - r3 - r4) = 0 := by
    linear_combination hE2 + F1 0 * (r1 + r2 + r3 + r4) * hk1
  have := (mul_eq_zero.mp key).resolve_left n1
  linear_combination this

end DLMF.Theta

end
