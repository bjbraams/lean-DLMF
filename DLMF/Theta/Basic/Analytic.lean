/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Basic.Periodicity
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Theta functions: analyticity (DLMF §20.2(i)–(ii))

Analyticity of the theta functions in `z` and in `τ`, the entire quotients `θ₁(z|τ)/sin z` and
`θ₂(z|τ)/cos z`, and the termwise differentiated Fourier series.

## Main definitions

* `thetaDirichletKernel`: the Dirichlet kernel `Uₙ(z) = ∑_{k=0}^{2n} e^{2i(k-n)z}`.
* `jacobiThetaOneDivSinTerm`: the terms of the series for `θ₁(z|τ)/sin z`.

## Main results

* `differentiable_jacobiThetaTau`, `differentiableAt_jacobiThetaThreeTau_tau`, …: the theta
  functions are entire in `z` and analytic in `τ` on the upper half-plane (DLMF §20.2(ii)).
* `jacobiThetaOneTau_div_sin_analytic`: `θ₁(z|τ)/sin z` and `θ₂(z|τ)/cos z` are entire in `z`
  and analytic in `τ`.
* `jacobiThetaTau_deriv_hasSum`: termwise differentiated series (DLMF §20.2(i)).
-/

@[expose] public section

open Complex
open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic Filter Topology

/-- DLMF §20.2(ii): `θ₃(·|τ)` is entire in `z` for `Im τ > 0`. -/
theorem differentiable_jacobiThetaThreeTau {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ (fun z => jacobiThetaThreeTau z τ) := fun z => by
  have := (differentiableAt_jacobiTheta₂_fst (z / π) hτ).comp z
    (differentiableAt_id.div_const (π : ℂ))
  exact this

/-- DLMF §20.2(ii): each `θⱼ(·|τ)` is an entire function of `z` for `Im τ > 0`. -/
@[dlmf 20.2.ii]
theorem differentiable_jacobiThetaTau (j : ℕ) {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ (fun z => jacobiThetaTau j z τ) := by
  have h3 := differentiable_jacobiThetaThreeTau hτ
  have h2 : Differentiable ℂ (fun z => jacobiThetaTwoTau z τ) := by
    unfold jacobiThetaTwoTau
    exact ((differentiable_const _).add (differentiable_const _ |>.mul differentiable_id)).cexp.mul
      (h3.comp (differentiable_id.add_const _))
  rcases j with _ | _ | _ | _ | _ | j
  · exact differentiable_const _
  · show Differentiable ℂ (fun z => jacobiThetaOneTau z τ)
    unfold jacobiThetaOneTau
    exact (h2.comp (differentiable_id.add_const _)).neg
  · exact h2
  · exact h3
  · show Differentiable ℂ (fun z => jacobiThetaFourTau z τ)
    unfold jacobiThetaFourTau
    exact h3.comp (differentiable_id.add_const _)
  · exact differentiable_const _

/-- DLMF §20.2(ii): for fixed `z`, `θ₃(z|τ)` and `θ₄(z|τ)` are analytic in `τ` on `Im τ > 0`. -/
@[dlmf 20.2.ii]
theorem differentiableAt_jacobiThetaThreeTau_tau (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (jacobiThetaThreeTau z) τ :=
  differentiableAt_jacobiTheta₂_snd (z / π) hτ

/-- DLMF §20.2(ii): `θ₄(z|·)` is analytic on the upper half-plane. -/
@[dlmf 20.2.ii]
theorem differentiableAt_jacobiThetaFourTau_tau (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (jacobiThetaFourTau z) τ :=
  differentiableAt_jacobiThetaThreeTau_tau (z + π / 2) hτ

/-- `θ₂(z|·)` is analytic on the upper half-plane (used for DLMF §20.2(ii)). -/
theorem differentiableAt_jacobiThetaTwoTau_tau (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (jacobiThetaTwoTau z) τ := by
  have hθ : DifferentiableAt ℂ (fun σ : ℂ => jacobiThetaThreeTau (z + π * σ / 2) σ) τ := by
    have h := (hasFDerivAt_jacobiTheta₂ ((z + π * τ / 2) / π) hτ).differentiableAt
    have hp : DifferentiableAt ℂ (fun σ : ℂ => ((z + π * σ / 2) / π, σ)) τ :=
      (((differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id
        |>.div_const _)).div_const _).prodMk differentiableAt_id
    exact DifferentiableAt.comp (𝕜 := ℂ) τ (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2)
      (f := fun σ : ℂ => ((z + π * σ / 2) / π, σ)) h hp
  exact ((((differentiableAt_const _).mul differentiableAt_id).div_const _).add
    (differentiableAt_const _)).cexp.mul hθ

/-- `θ₁(z|·)` is analytic on the upper half-plane (used for DLMF §20.2(ii)). -/
theorem differentiableAt_jacobiThetaOneTau_tau (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (jacobiThetaOneTau z) τ :=
  (differentiableAt_jacobiThetaTwoTau_tau (z + π / 2) hτ).neg

/-! ### Helpers for the quotients `θ₁(z|τ)/sin z`, `θ₂(z|τ)/cos z` -/

/-- Dirichlet kernel `Uₙ(z) = ∑_{k=0}^{2n} e^{2i(k-n)z}`. -/
def thetaDirichletKernel (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (2 * n + 1), cexp (2 * I * ((k : ℂ) - n) * z)

/-- `sin z · Uₙ(z) = sin((2n+1)z)`. -/
private lemma sin_mul_thetaDirichletKernel (n : ℕ) (z : ℂ) :
    sin z * thetaDirichletKernel n z = sin ((2 * n + 1) * z) := by
  set f : ℕ → ℂ := fun k => cexp (I * (2 * k - 2 * n - 1) * z) with hf
  have hterm : ∀ k : ℕ, sin z * cexp (2 * I * ((k : ℂ) - n) * z) = (f (k + 1) - f k) / (2 * I) := by
    intro k
    rw [Complex.sin, hf]
    simp only
    field_simp
    simp only [I_sq, neg_mul, one_mul]
    push_cast
    ring_nf
    simp only [exp_add, exp_sub]
    ring
  rw [thetaDirichletKernel, Finset.mul_sum]
  simp_rw [hterm]
  rw [← Finset.sum_div, Finset.sum_range_sub, Complex.sin, hf]
  simp only
  field_simp
  simp only [I_sq, neg_mul, one_mul]
  push_cast
  ring_nf

/-- `‖Uₙ(z)‖ ≤ (2n+1) e^{2n|Im z|}`. -/
private lemma norm_thetaDirichletKernel_le (n : ℕ) (z : ℂ) :
    ‖thetaDirichletKernel n z‖ ≤ (2 * n + 1) * Real.exp (2 * n * |z.im|) := by
  refine (norm_sum_le _ _).trans ?_
  have : ∀ k ∈ Finset.range (2 * n + 1), ‖cexp (2 * I * ((k : ℂ) - n) * z)‖ ≤
      Real.exp (2 * n * |z.im|) := by
    intro k hk
    rw [Complex.norm_exp, Real.exp_le_exp]
    have hk' : (k : ℝ) ≤ 2 * n := by
      have := Finset.mem_range.mp hk; exact_mod_cast Nat.lt_succ_iff.mp this
    have hre : (2 * I * ((k : ℂ) - n) * z).re = -(2 * ((k : ℝ) - n) * z.im) := by
      simp [mul_re, mul_im]
    rw [hre]
    have h1 : |(k : ℝ) - n| ≤ n := by rw [abs_le]; constructor <;>
      linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    have h2 : -(2 * ((k : ℝ) - n) * z.im) ≤ 2 * |(k : ℝ) - n| * |z.im| := by
      have := neg_abs_le (((k : ℝ) - n) * z.im)
      rw [abs_mul] at this; nlinarith
    nlinarith [abs_nonneg z.im]
  refine (Finset.sum_le_sum this).trans ?_
  simp

/-- Differentiability of `Uₙ`. -/
private lemma differentiable_thetaDirichletKernel (n : ℕ) :
    Differentiable ℂ (thetaDirichletKernel n) := by
  unfold thetaDirichletKernel
  fun_prop

/-- The terms of the series for `θ₁(z|τ)/sin z`. -/
def jacobiThetaOneDivSinTerm (n : ℕ) (z τ : ℂ) : ℂ :=
  2 * (-1 : ℂ) ^ n * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) * thetaDirichletKernel n z

/-- Termwise bound. -/
private lemma norm_jacobiThetaOneDivSinTerm_le (n : ℕ) {z τ : ℂ} {R T : ℝ} (hT : 0 ≤ T)
    (hz : |z.im| ≤ R)
    (hτ : T ≤ τ.im) :
    ‖jacobiThetaOneDivSinTerm n z τ‖ ≤ 2 *
        ((2 * n + 1) * Real.exp (-π * T * n ^ 2 + 2 * R * n)) := by
  have he : ‖cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2)‖ =
      Real.exp (-π * τ.im * (n + 1 / 2) ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    have : ((n : ℂ) + 1 / 2) = (((n : ℝ) + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← ofReal_pow, Complex.re_mul_ofReal]
    simp [mul_re, mul_im]
  rw [jacobiThetaOneDivSinTerm, norm_mul, norm_mul, norm_mul, he]
  simp only [norm_pow, norm_neg, norm_one, one_pow, mul_one, Complex.norm_ofNat]
  have hU := norm_thetaDirichletKernel_le n z
  have hexp : Real.exp (-π * τ.im * (n + 1 / 2) ^ 2) * Real.exp (2 * n * |z.im|) ≤
      Real.exp (-π * T * n ^ 2 + 2 * R * n) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have h1 : π * T * n ^ 2 ≤ π * τ.im * (n + 1 / 2) ^ 2 := by
      have : (n : ℝ) ^ 2 ≤ (n + 1 / 2) ^ 2 := by nlinarith
      have := mul_le_mul hτ this (sq_nonneg _) (hT.trans hτ)
      nlinarith [Real.pi_pos]
    nlinarith
  calc 2 * Real.exp (-π * τ.im * (n + 1 / 2) ^ 2) * ‖thetaDirichletKernel n z‖
      ≤ 2 * Real.exp (-π * τ.im * (n + 1 / 2) ^ 2) *
        ((2 * n + 1) * Real.exp (2 * n * |z.im|)) := by gcongr
    _ = 2 * ((2 * n + 1) * (Real.exp (-π * τ.im * (n + 1 / 2) ^ 2) *
        Real.exp (2 * n * |z.im|))) := by ring
    _ ≤ _ := by gcongr

/-- Summability of the majorant. -/
private lemma summable_jacobiThetaOneDivSin_majorant (R : ℝ) {T : ℝ} (hT : 0 < T) :
    Summable (fun n : ℕ => 2 * ((2 * n + 1) * Real.exp (-π * T * n ^ 2 + 2 * R * n))) := by
  have h1 := (summable_pow_mul_jacobiTheta₂_term_bound (R / π) hT 1).comp_injective
    Nat.cast_injective
  have h0 := (summable_pow_mul_jacobiTheta₂_term_bound (R / π) hT 0).comp_injective
    Nat.cast_injective
  refine ((h1.mul_left 2).add h0).mul_left 2 |>.congr fun n => ?_
  simp only [Function.comp_apply, Int.cast_natCast, Nat.abs_cast, pow_one, pow_zero, one_mul]
  have : -π * (T * (n : ℝ) ^ 2 - 2 * (R / π) * n) = -π * T * n ^ 2 + 2 * R * n := by
    field_simp; ring
  rw [this]; ring

/-- Summability of the series for `θ₁(z|τ)/sin z`. -/
private lemma summable_jacobiThetaOneDivSinTerm (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℕ => jacobiThetaOneDivSinTerm n z τ) :=
  (summable_jacobiThetaOneDivSin_majorant |z.im| hτ).of_norm_bounded fun n =>
      norm_jacobiThetaOneDivSinTerm_le n hτ.le le_rfl le_rfl

/-- `sin z · ∑ₙ (2(-1)ⁿ q^{(n+1/2)²} Uₙ(z)) = θ₁(z|τ)`. -/
private lemma sin_mul_tsum_jacobiThetaOneDivSinTerm (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    sin z * ∑' n : ℕ, jacobiThetaOneDivSinTerm n z τ = jacobiThetaOneTau z τ := by
  refine ((summable_jacobiThetaOneDivSinTerm z hτ).hasSum.mul_left (sin z)).unique ?_
  convert jacobiThetaOneTau_hasSum_sin z hτ using 2 with n
  rw [jacobiThetaOneDivSinTerm, ← sin_mul_thetaDirichletKernel]
  ring

/-- For `Im τ > 0`, `z ↦ ∑ₙ 2(-1)ⁿ q^{(n+1/2)²} Uₙ(z)` is entire. -/
private lemma differentiable_tsum_jacobiThetaOneDivSinTerm {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ (fun z => ∑' n : ℕ, jacobiThetaOneDivSinTerm n z τ) := by
  intro z₀
  have hU : IsOpen {z : ℂ | |z.im| < |z₀.im| + 1} :=
    isOpen_lt (continuous_abs.comp continuous_im) continuous_const
  have h := Complex.differentiableOn_tsum_of_summable_norm
      (summable_jacobiThetaOneDivSin_majorant (|z₀.im| + 1) hτ)
    (fun n => by
      simp only [jacobiThetaOneDivSinTerm]
      exact ((differentiable_thetaDirichletKernel n).const_mul _).differentiableOn) hU
    (fun n w hw => norm_jacobiThetaOneDivSinTerm_le n hτ.le (le_of_lt hw) le_rfl)
  exact h.differentiableAt (hU.mem_nhds (by simp))

/-- For fixed `z`, `τ ↦ ∑ₙ 2(-1)ⁿ q^{(n+1/2)²} Uₙ(z)` is analytic on the upper half-plane. -/
private lemma differentiableOn_tsum_jacobiThetaOneDivSinTerm_tau (z : ℂ) :
    DifferentiableOn ℂ (fun τ => ∑' n : ℕ, jacobiThetaOneDivSinTerm n z τ) {τ | 0 < τ.im} := by
  intro τ₀ hτ₀
  have hT : 0 < τ₀.im / 2 := half_pos hτ₀
  have hU : IsOpen {τ : ℂ | τ₀.im / 2 < τ.im} := isOpen_lt continuous_const continuous_im
  have h := Complex.differentiableOn_tsum_of_summable_norm
      (summable_jacobiThetaOneDivSin_majorant |z.im| hT)
    (fun n => by
      simp only [jacobiThetaOneDivSinTerm]
      exact Differentiable.differentiableOn (by fun_prop)) hU
    (fun n w hw => norm_jacobiThetaOneDivSinTerm_le n hT.le le_rfl (le_of_lt hw))
  exact (h.differentiableAt (hU.mem_nhds (by simp only [Set.mem_ofPred_eq]; linarith))
    ).differentiableWithinAt

/-- `θ₁(π/2 - z|τ) = θ₂(z|τ)`. -/
private lemma jacobiThetaOneTau_pi_div_two_sub (z τ : ℂ) :
    jacobiThetaOneTau (π / 2 - z) τ = jacobiThetaTwoTau z τ := by
  rw [jacobiThetaOneTau, show (π : ℂ) / 2 - z + π / 2 = -z + π by ring, jacobiThetaTwoTau_add_pi,
    neg_neg, jacobiThetaTwoTau_neg]

/-- DLMF §20.2(ii): `θ₁(z|τ)/sin z` and `θ₂(z|τ)/cos z` are analytic functions of `τ` in the
upper half-plane for every fixed `z`, including the zeros of `sin z`, `cos z`, where the quotients
are understood as their limits. Formally: there is a function `F(z, τ)` that is entire in `z` for
each `τ` with `Im τ > 0`, analytic in `τ` on the upper half-plane for each `z`, and equal to
`θ₁(z|τ)/sin z` wherever `sin z ≠ 0`; continuity in `z` makes `F` unique, so at the zeros of
`sin z` it is the removable-singularity value. Likewise `G` for `θ₂(z|τ)/cos z`.
Restated 2026-10-25 (user decision): the earlier form only asked for some analytic function of
`τ` agreeing with the quotient where `sin z ≠ 0`, which is trivially true at the zeros. -/
@[dlmf 20.2.ii]
theorem jacobiThetaOneTau_div_sin_analytic :
    (∃ F : ℂ → ℂ → ℂ, (∀ τ : ℂ, 0 < τ.im → Differentiable ℂ (fun z => F z τ)) ∧
      (∀ z : ℂ, DifferentiableOn ℂ (F z) {τ | 0 < τ.im}) ∧
      ∀ z τ : ℂ, 0 < τ.im → sin z ≠ 0 → F z τ = jacobiThetaOneTau z τ / sin z) ∧
    (∃ G : ℂ → ℂ → ℂ, (∀ τ : ℂ, 0 < τ.im → Differentiable ℂ (fun z => G z τ)) ∧
      (∀ z : ℂ, DifferentiableOn ℂ (G z) {τ | 0 < τ.im}) ∧
      ∀ z τ : ℂ, 0 < τ.im → cos z ≠ 0 → G z τ = jacobiThetaTwoTau z τ / cos z) := by
  refine ⟨⟨fun z τ => ∑' n : ℕ, jacobiThetaOneDivSinTerm n z τ,
      fun τ hτ => differentiable_tsum_jacobiThetaOneDivSinTerm hτ,
    differentiableOn_tsum_jacobiThetaOneDivSinTerm_tau, fun z τ hτ hz => ?_⟩,
    ⟨fun z τ => ∑' n : ℕ, jacobiThetaOneDivSinTerm n (π / 2 - z) τ, fun τ hτ => ?_,
    fun z => differentiableOn_tsum_jacobiThetaOneDivSinTerm_tau (π / 2 - z), fun z τ hτ hz => ?_⟩⟩
  · rw [eq_div_iff hz, mul_comm, sin_mul_tsum_jacobiThetaOneDivSinTerm z hτ]
  · exact (differentiable_tsum_jacobiThetaOneDivSinTerm hτ).comp
      ((differentiable_const _).sub differentiable_id)
  · rw [← sin_pi_div_two_sub] at hz
    rw [eq_div_iff (by rwa [← sin_pi_div_two_sub]), ← sin_pi_div_two_sub, mul_comm,
      sin_mul_tsum_jacobiThetaOneDivSinTerm _ hτ, jacobiThetaOneTau_pi_div_two_sub]

/-- `sin(x + nπ) = (-1)ⁿ sin x` (helper). -/
private lemma complex_sin_add_nat_mul_pi (x : ℂ) (n : ℕ) : sin (x + n * π) = (-1) ^ n * sin x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show x + ((n + 1 : ℕ) : ℂ) * π = (x + n * π) + π by push_cast; ring, sin_add_pi, ih]
    ring

/-- The derivative of `θ₃(·|τ)` and its sine series (helper). -/
private lemma hasDerivAt_jacobiThetaThreeTau_and_hasSum (u : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (fun w => jacobiThetaThreeTau w τ) ((1 / π) * jacobiTheta₂' (u / π) τ) u ∧
    HasSum (fun k : ℕ => -(2 * cexp (π * I * τ * ((k : ℂ) + 1) ^ 2) *
        (2 * ((k : ℂ) + 1) * sin (2 * ((k : ℂ) + 1) * u))))
            ((1 / π) * jacobiTheta₂' (u / π) τ) := by
  refine ⟨?_, ?_⟩
  · have h := (hasDerivAt_jacobiTheta₂_fst (u / π) hτ).comp u ((hasDerivAt_id u).div_const (π : ℂ))
    exact h.congr_deriv (by ring)
  · have h := ((hasSum_jacobiTheta₂'_term (u / π) hτ).mul_left (1 / (π : ℂ))).nat_add_neg
    have h0 : (1 / (π : ℂ)) * jacobiTheta₂'_term 0 (u / π) τ = 0 := by
      simp [jacobiTheta₂'_term]
    rw [h0, add_zero] at h
    have h' := (hasSum_nat_add_iff' 1).mpr h
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, neg_zero, h0, add_zero,
      sub_zero] at h'
    convert h' using 1
    funext k
    simp only [jacobiTheta₂'_term, jacobiTheta₂_term, sin]
    push_cast
    have e1 : cexp (2 * π * I * ((k : ℂ) + 1) * (u / π) + π * I * ((k : ℂ) + 1) ^ 2 * τ) =
        cexp (π * I * τ * ((k : ℂ) + 1) ^ 2) * cexp (2 * ((k : ℂ) + 1) * u * I) := by
      rw [← exp_add]; congr 1; field_simp [pi_ne_zero']; ring
    have e2 : cexp (2 * π * I * -((k : ℂ) + 1) * (u / π) + π * I * (-((k : ℂ) + 1)) ^ 2 * τ) =
        cexp (π * I * τ * ((k : ℂ) + 1) ^ 2) * cexp (-(2 * ((k : ℂ) + 1) * u) * I) := by
      rw [← exp_add]; congr 1; field_simp [pi_ne_zero']; ring
    rw [e1, e2]
    field_simp [pi_ne_zero']
    ring

/-- The derivative of `θ₂(·|τ)` and its sine series (helper). -/
private lemma exists_hasDerivAt_jacobiThetaTwoTau_and_hasSum (u : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ D : ℂ, HasDerivAt (fun w => jacobiThetaTwoTau w τ) D u ∧
    HasSum (fun n : ℕ => -(2 * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) *
        ((2 * n + 1) * sin ((2 * n + 1) * u)))) D := by
  set c := cexp (π * I * τ / 4 + I * u) with hc
  set v := (u + π * τ / 2) / π with hv
  have hE : HasDerivAt (fun w : ℂ => cexp (π * I * τ / 4 + I * w)) (I * c) u := by
    have := (((hasDerivAt_id u).const_mul I).const_add (π * I * τ / 4)).cexp
    simpa [hc, mul_comm] using this
  have hJ : HasDerivAt (fun w : ℂ => jacobiTheta₂ ((w + π * τ / 2) / π) τ)
      (jacobiTheta₂' v τ * (1 / π)) u := by
    have := (hasDerivAt_jacobiTheta₂_fst v hτ).comp u
      (((hasDerivAt_id u).add_const (π * τ / 2)).div_const (π : ℂ))
    simpa [hv, Function.comp_def] using this
  refine ⟨I * c * jacobiTheta₂ v τ + c * (jacobiTheta₂' v τ * (1 / π)), hE.mul hJ, ?_⟩
  have hS := (((hasSum_jacobiTheta₂_term v hτ).mul_left (I * c)).add
    ((hasSum_jacobiTheta₂'_term v hτ).mul_left (c * (1 / (π : ℂ))))).nat_add_neg_add_one
  convert hS using 1
  · funext n
    have hm : ∀ m : ℤ, I * c * jacobiTheta₂_term m v τ + c * (1 / π) * jacobiTheta₂'_term m v τ =
        I * (2 * m + 1) * (c * jacobiTheta₂_term m v τ) := fun m => by
      simp only [jacobiTheta₂'_term]; field_simp [pi_ne_zero']; ring
    rw [hm, hm]
    simp only [jacobiTheta₂_term, sin, hc, hv]
    push_cast
    set A := cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2)
    have e1 : cexp (π * I * τ / 4 + I * u) *
        cexp (2 * π * I * n * ((u + π * τ / 2) / π) + π * I * n ^ 2 * τ) =
        A * cexp ((2 * n + 1) * u * I) := by
      simp only [A, ← exp_add]; congr 1; field_simp [pi_ne_zero']; ring
    have e2 : cexp (π * I * τ / 4 + I * u) *
        cexp (2 * π * I * -((n : ℂ) + 1) * ((u + π * τ / 2) / π) +
          π * I * (-((n : ℂ) + 1)) ^ 2 * τ) =
        A * cexp (-((2 * n + 1) * u) * I) := by
      simp only [A, ← exp_add]; congr 1; field_simp [pi_ne_zero']; ring
    linear_combination (-(I * (2 * n + 1))) * e1 + (I * (2 * n + 1)) * e2
  · ring

/-- DLMF §20.2(i): the expansions of `θⱼ'(z|τ)` obtained by termwise differentiation of
20.2.1–20.2.4 (`Im τ > 0`). -/
@[dlmf 20.2.i]
theorem jacobiThetaTau_deriv_hasSum (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => 2 * (-1 : ℂ) ^ n * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) *
        ((2 * n + 1) * cos ((2 * n + 1) * z))) (deriv (fun w => jacobiThetaOneTau w τ) z) ∧
    HasSum (fun n : ℕ => -(2 * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) *
        ((2 * n + 1) * sin ((2 * n + 1) * z)))) (deriv (fun w => jacobiThetaTwoTau w τ) z) ∧
    HasSum (fun n : ℕ => -(2 * cexp (π * I * τ * ((n : ℂ) + 1) ^ 2) *
        (2 * ((n : ℂ) + 1) * sin (2 * ((n : ℂ) + 1) * z))))
      (deriv (fun w => jacobiThetaThreeTau w τ) z) ∧
    HasSum (fun n : ℕ => -(2 * (-1 : ℂ) ^ (n + 1) * cexp (π * I * τ * ((n : ℂ) + 1) ^ 2) *
        (2 * ((n : ℂ) + 1) * sin (2 * ((n : ℂ) + 1) * z))))
      (deriv (fun w => jacobiThetaFourTau w τ) z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨D, hD, hS⟩ := exists_hasDerivAt_jacobiThetaTwoTau_and_hasSum (z + π / 2) hτ
    have hD1 : HasDerivAt (fun w => jacobiThetaOneTau w τ) (-D) z :=
      (hD.comp_add_const z (π / 2)).neg
    rw [hD1.deriv]
    convert hS.neg using 1
    funext n
    rw [neg_neg, show (2 * (n : ℂ) + 1) * (z + π / 2) = ((2 * n + 1) * z + π / 2) + n * π by ring,
      complex_sin_add_nat_mul_pi, sin_add_pi_div_two]
    ring
  · obtain ⟨D, hD, hS⟩ := exists_hasDerivAt_jacobiThetaTwoTau_and_hasSum z hτ
    rw [hD.deriv]; exact hS
  · obtain ⟨hD, hS⟩ := hasDerivAt_jacobiThetaThreeTau_and_hasSum z hτ
    rw [hD.deriv]; exact hS
  · obtain ⟨hD, hS⟩ := hasDerivAt_jacobiThetaThreeTau_and_hasSum (z + π / 2) hτ
    have hD4 : HasDerivAt (fun w => jacobiThetaFourTau w τ)
        ((1 / π) * jacobiTheta₂' ((z + π / 2) / π) τ) z :=
      hD.comp_add_const z (π / 2)
    rw [hD4.deriv]
    convert hS using 1
    funext n
    rw [show 2 * ((n : ℂ) + 1) * (z + π / 2) = 2 * ((n : ℂ) + 1) * z + ((n + 1 : ℕ) : ℂ) * π by
      push_cast; ring, complex_sin_add_nat_mul_pi]
    ring

end DLMF.Theta

end
