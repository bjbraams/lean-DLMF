/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.EllipticFunctionsAndInvariants
public import DLMF.Weierstrass.Series

/-!
# Asymptotic approximations as `q → 0` (DLMF §23.12)

Asymptotic forms of `℘`, `ζ`, `σ` and `η₁` as the nome tends to zero.

## Main results

* `weierstrassP_isBigO_nome`: DLMF 23.12.1.
* `weierstrassZeta_isBigO_nome`: DLMF 23.12.2.
* `weierstrassSigma_isBigO_nome`: DLMF 23.12.3.
* `eta_one_isBigO_nome`: DLMF 23.12.4.

## Implementation notes

DLMF lets `q = e^{πiω₃/ω₁} → 0` with `ω₁` and `z` fixed. Here `ω₃ = ω₁τ` and `τ` tends to
`i∞` in the upper half-plane (`UpperHalfPlane.atImInfty`), which is the same as `q → 0`.
The condition `z ∉ 𝕃` of DLMF is, eventually as `ℑτ → ∞`, the condition `z ∉ 2ω₁ℤ`.
§23.13 (zeros of `℘`) only refers to Eichler and Zagier (1982) and contains no formula.
-/

@[expose] public section

open Complex PeriodPair Asymptotics UpperHalfPlane Filter
open scoped Real

noncomputable section

namespace DLMF.Weierstrass

namespace HalfPeriods

/-- A series whose terms are bounded by `C (n + 2) ρ^{n+2}` with `0 ≤ ρ ≤ 1/2` has sum at most
`6Cρ²`. -/

private lemma norm_le_of_hasSum_le_mul_pow {f : ℕ → ℂ} {S : ℂ} (hS : HasSum f S) {ρ C : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2) (hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C * ((n : ℝ) + 2) * ρ ^ (n + 2)) : ‖S‖ ≤ 6 * C * ρ ^ 2 := by
  have hρ1 : ρ < 1 := by linarith
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := ρ)
    (by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ1)
  have h2 := hasSum_geometric_of_lt_one hρ0 hρ1
  have hg : HasSum (fun n : ℕ => C * ((n : ℝ) + 2) * ρ ^ (n + 2))
      (C * ρ ^ 2 * (ρ / (1 - ρ) ^ 2 + 2 * (1 - ρ)⁻¹)) := by
    convert ((h1.add (h2.mul_left 2)).mul_left (C * ρ ^ 2)) using 1
    funext n; ring
  refine (hS.norm_le_of_bounded hg hf).trans ?_
  have hd : 0 < 1 - ρ := by linarith
  have e1 : ρ / (1 - ρ) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have e2 : (1 - ρ)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hd (by norm_num)]; linarith
  have : 0 ≤ C * ρ ^ 2 := by positivity
  nlinarith

/-- Eventually as `ℑτ → ∞` the nome is small. -/

private lemma eventually_norm_nome_le (ω : ℂ) (hω : ω ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ τ in atImInfty, ‖(ofTau ω hω τ).nome‖ ≤ ε := by
  rw [Filter.Eventually, atImInfty_mem]
  refine ⟨-Real.log ε / π, fun τ hτ => ?_⟩
  have ht : (ofTau ω hω τ).tau = τ := by
    simp only [HalfPeriods.tau, ofTau_ω₁, ofTau_ω₃]; field_simp
  simp only [Set.mem_ofPred_eq, HalfPeriods.nome, ht, Complex.norm_exp]
  have : (π * Complex.I * (τ : ℂ)).re = -(π * τ.im) := by simp
  rw [this]
  have hπ := Real.pi_pos
  calc Real.exp (-(π * τ.im)) ≤ Real.exp (Real.log ε) := by
        apply Real.exp_le_exp.mpr
        have := (div_le_iff₀ hπ).mp hτ; linarith
    _ = ε := Real.exp_log hε

/-- `η₁ = (π²/(12ω₁)) - (2π²/ω₁) ∑_{k≥1} q^{2k}/(1 - q^{2k})²`, as a sum. -/

private lemma hasSum_eta_one (H : HalfPeriods) :
    HasSum (fun k : ℕ => 24 * H.nome ^ (2 * (k + 1)) / (1 - H.nome ^ (2 * (k + 1))) ^ 2)
      (1 - 12 * H.ω₁ / π ^ 2 * H.eta 1) := by
  have h := DLMF.Theta.jacobiThetaOne_third_deriv_ratio H.tau_im_pos
  have he := H.eta_one_eq_theta
  have hω := H.ω₁_ne_zero
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hD := H.jacobiThetaOneDerivNullTau_tau_ne_zero
  have h' : HasSum (fun k : ℕ => 24 * H.nome ^ (2 * (k + 1)) / (1 - H.nome ^ (2 * (k + 1))) ^ 2)
      _ := h
  convert h' using 1
  rw [he, thetaOneTripleDerivNull]
  field_simp
  ring

/-- Explicit form of DLMF 23.12.4: for `‖q‖ ≤ 1/2`,
`‖η₁ - (π²/(4ω₁))(1/3 - 8q²)‖ ≤ 352 ‖π²/(12ω₁)‖ ‖q‖⁴`. -/

private lemma norm_eta_one_sub_le (H : HalfPeriods) (hq : ‖H.nome‖ ≤ 1 / 2) :
    ‖H.eta 1 - π ^ 2 / (4 * H.ω₁) * (1 / 3 - 8 * H.nome ^ 2)‖ ≤
      ‖π ^ 2 / (12 * H.ω₁)‖ * 352 * ‖H.nome ^ 4‖ := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hω := H.ω₁_ne_zero
  set q := H.nome
  have hS := hasSum_eta_one H
  have hS' := (hasSum_nat_add_iff' 1).mpr hS
  simp only [Finset.range_one, Finset.sum_singleton] at hS'
  have hR : HasSum (fun k : ℕ => 24 * q ^ (2 * (k + 1 + 1)) / (1 - q ^ (2 * (k + 1 + 1))) ^ 2)
      (1 - 12 * H.ω₁ / π ^ 2 * H.eta 1 - 24 * q ^ (2 * (0 + 1)) / (1 - q ^ (2 * (0 + 1))) ^ 2) :=
    hS'
  have hn1 : (3 / 4 : ℝ) ≤ ‖1 - q ^ 2‖ := by
    have := norm_sub_norm_le (1 : ℂ) (q ^ 2)
    rw [norm_one, norm_pow] at this; nlinarith [norm_nonneg q]
  have h1q : 1 - q ^ 2 ≠ 0 := fun h0 => by rw [h0, norm_zero] at hn1; norm_num at hn1
  -- the first term
  have hf0 : ‖24 * q ^ (2 * (0 + 1)) / (1 - q ^ (2 * (0 + 1))) ^ 2 - 24 * q ^ 2‖ ≤
      96 * ‖q‖ ^ 4 := by
    rw [show 24 * q ^ (2 * (0 + 1)) / (1 - q ^ (2 * (0 + 1))) ^ 2 - 24 * q ^ 2 =
      24 * q ^ 4 * (2 - q ^ 2) / (1 - q ^ 2) ^ 2 by field_simp; ring]
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
    have h2 : ‖2 - q ^ 2‖ ≤ 9 / 4 := by
      refine (norm_sub_le _ _).trans ?_; rw [norm_pow]; norm_num; nlinarith [norm_nonneg q]
    rw [div_le_iff₀ (by positivity)]
    have : (9 / 16 : ℝ) ≤ ‖1 - q ^ 2‖ ^ 2 := by nlinarith
    simp only [Complex.norm_ofNat]
    have := norm_nonneg q
    nlinarith [pow_nonneg (norm_nonneg q) 4]
  -- the tail
  have hRb := norm_le_of_hasSum_le_mul_pow hR (ρ := ‖q‖ ^ 2) (C := 128 / 3) (by positivity)
    (by nlinarith [norm_nonneg q]) (by norm_num) (fun n => by
      have hx : ‖q ^ (2 * (n + 1 + 1))‖ = (‖q‖ ^ 2) ^ (n + 2) := by
        rw [norm_pow, ← pow_mul, show 2 * (n + 1 + 1) = 2 * (n + 2) by ring]
      have hxl : (‖q‖ ^ 2) ^ (n + 2) ≤ 1 / 4 := by
        calc (‖q‖ ^ 2) ^ (n + 2) ≤ (‖q‖ ^ 2) ^ 1 :=
              pow_le_pow_of_le_one (by positivity) (by nlinarith [norm_nonneg q]) (by omega)
          _ ≤ 1 / 4 := by nlinarith [norm_nonneg q]
      have hd : (3 / 4 : ℝ) ≤ ‖1 - q ^ (2 * (n + 1 + 1))‖ := by
        have := norm_sub_norm_le (1 : ℂ) (q ^ (2 * (n + 1 + 1)))
        rw [norm_one, hx] at this; linarith
      have : (9 / 16 : ℝ) ≤ ‖1 - q ^ (2 * (n + 1 + 1))‖ ^ 2 := by nlinarith
      have e : ‖24 * q ^ (2 * (n + 1 + 1)) / (1 - q ^ (2 * (n + 1 + 1))) ^ 2‖ =
          24 * (‖q‖ ^ 2) ^ (n + 2) / ‖1 - q ^ (2 * (n + 1 + 1))‖ ^ 2 := by
        rw [norm_div, norm_mul, hx, norm_pow, Complex.norm_ofNat]
      rw [e, div_le_iff₀ (by positivity)]
      have hp : 0 ≤ (‖q‖ ^ 2) ^ (n + 2) := by positivity
      have hn : (1 : ℝ) ≤ (n : ℝ) + 2 := by have := n.cast_nonneg (α := ℝ); linarith
      nlinarith [mul_le_mul_of_nonneg_left this hp])
  have key : H.eta 1 - π ^ 2 / (4 * H.ω₁) * (1 / 3 - 8 * q ^ 2) = -(π ^ 2 / (12 * H.ω₁)) *
      ((24 * q ^ (2 * (0 + 1)) / (1 - q ^ (2 * (0 + 1))) ^ 2 - 24 * q ^ 2) +
        ∑' k : ℕ, 24 * q ^ (2 * (k + 1 + 1)) / (1 - q ^ (2 * (k + 1 + 1))) ^ 2) := by
    rw [hR.tsum_eq]; field_simp; ring
  rw [key, norm_mul, norm_neg, norm_pow]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_add_le _ _).trans ?_
  rw [hR.tsum_eq] at *
  nlinarith [hRb, hf0]

/-- `‖cos w‖ ≤ e^{|ℑw|}`. -/
private lemma norm_cos_le_exp_abs_im (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  refine (DLMF.Elementary.sinh_im_le_norm_cos_le_cosh_im w).2.trans ?_
  rw [← Real.cosh_abs, Real.cosh_eq]
  have := Real.exp_le_exp.mpr (show -|w.im| ≤ |w.im| by linarith [abs_nonneg w.im])
  linarith

/-- `‖sin w‖ ≤ e^{|ℑw|}`. -/
private lemma norm_sin_le_exp_abs_im (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  refine (DLMF.Elementary.sinh_im_le_norm_sin_le_cosh_im w).2.trans ?_
  rw [← Real.cosh_abs, Real.cosh_eq]
  have := Real.exp_le_exp.mpr (show -|w.im| ≤ |w.im| by linarith [abs_nonneg w.im])
  linarith

/-- Eventually as `ℑτ → ∞`, a point `z ∉ 2ω₁ℤ` is off the lattice, lies in the strip of the
Fourier series, and the nome is at most `e^{-π|ℑ(z/ω₁)|}/2`. -/

private lemma eventually_fourier_conditions (ω : ℂ) (hω : ω ≠ 0) {z : ℂ}
    (hz : ∀ m : ℤ, z ≠ 2 * m * ω) :
    ∀ᶠ τ in atImInfty, z ∉ (ofTau ω hω τ).lattice ∧
      |(z / ω).im| < 2 * (ofTau ω hω τ).tau.im ∧
      ‖(ofTau ω hω τ).nome‖ ≤ Real.exp (-(π * |(z / ω).im|)) / 2 := by
  have hA : ∀ᶠ τ : ℍ in atImInfty, |(z / ω).im| < 2 * τ.im := by
    rw [Filter.Eventually, atImInfty_mem]
    exact ⟨|(z / ω).im| / 2 + 1, fun τ hτ => by simp only [Set.mem_ofPred_eq]; linarith⟩
  filter_upwards [hA, eventually_norm_nome_le ω hω (ε := Real.exp (-(π * |(z / ω).im|)) / 2)
    (by positivity)] with τ h1 h2
  have ht : (ofTau ω hω τ).tau = τ := by
    simp only [HalfPeriods.tau, ofTau_ω₁, ofTau_ω₃]; field_simp
  rw [ht]
  refine ⟨fun hmem => ?_, h1, h2⟩
  obtain ⟨m, n, hmn⟩ := (ofTau ω hω τ).mem_lattice_iff.mp hmem
  simp only [ofTau_ω₁, ofTau_ω₃] at hmn
  have hzω : z / ω = 2 * m + 2 * n * (τ : ℂ) := by rw [hmn]; field_simp
  rw [hzω] at h1
  have him : (2 * (m : ℂ) + 2 * n * (τ : ℂ)).im = 2 * n * τ.im := by simp
  rw [him] at h1
  rcases eq_or_ne n 0 with rfl | hn
  · exact hz m (by rw [hmn]; simp)
  · have : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
    rw [abs_mul, abs_mul, abs_of_pos (show (0:ℝ) < 2 by norm_num), abs_of_pos τ.im_pos] at h1
    have := τ.im_pos
    nlinarith

/-- Bound for a term `m q^{2m}/(1 - q^{2m}) g` with `‖g‖ ≤ E^m` and `ρ = ‖q‖²E ≤ 1/4`,
`‖q‖ ≤ 1/2`. -/

private lemma norm_lambert_term_le {q g : ℂ} {E : ℝ} (hE : 1 ≤ E) (hq : ‖q‖ ≤ 1 / 2) {m : ℕ}
    (hm : 1 ≤ m) (hg : ‖g‖ ≤ E ^ m) :
    ‖(m : ℂ) * q ^ (2 * m) / (1 - q ^ (2 * m)) * g‖ ≤ 4 / 3 * m * (‖q‖ ^ 2 * E) ^ m := by
  have hx : ‖q ^ (2 * m)‖ = (‖q‖ ^ 2) ^ m := by rw [norm_pow, pow_mul]
  have hxl : (‖q‖ ^ 2) ^ m ≤ 1 / 4 := by
    calc (‖q‖ ^ 2) ^ m ≤ (‖q‖ ^ 2) ^ 1 :=
          pow_le_pow_of_le_one (by positivity) (by nlinarith [norm_nonneg q]) hm
      _ ≤ 1 / 4 := by nlinarith [norm_nonneg q]
  have hd : (3 / 4 : ℝ) ≤ ‖1 - q ^ (2 * m)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (q ^ (2 * m))
    rw [norm_one, hx] at this; linarith
  rw [norm_mul, norm_div, norm_mul, hx, Complex.norm_natCast, mul_pow]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  have h1 : 0 ≤ (m : ℝ) * (‖q‖ ^ 2) ^ m := by positivity
  have h2 : (m : ℝ) * (‖q‖ ^ 2) ^ m * ‖g‖ ≤ (m : ℝ) * (‖q‖ ^ 2) ^ m * E ^ m :=
    mul_le_mul_of_nonneg_left hg h1
  have h3 : 0 ≤ (m : ℝ) * (‖q‖ ^ 2) ^ m * E ^ m := by
    have : 0 ≤ E ^ m := pow_nonneg (by linarith) m
    positivity
  nlinarith

/-- Explicit form of DLMF 23.12.1 under the conditions of `eventually_fourier_conditions`. -/

private lemma norm_weierstrassP_sub_le (H : HalfPeriods) {z : ℂ} (hz : z ∉ H.lattice)
    (hzi : |(z / H.ω₁).im| < 2 * H.tau.im)
    (hq : ‖H.nome‖ ≤ Real.exp (-(π * |(z / H.ω₁).im|)) / 2) :
    ‖H.weierstrassP z - π ^ 2 / (4 * H.ω₁ ^ 2) *
        (-1 / 3 + 1 / Complex.sin (π * z / (2 * H.ω₁)) ^ 2 +
          8 * (1 - Complex.cos (π * z / H.ω₁)) * H.nome ^ 2)‖ ≤
      (‖2 * π ^ 2 / H.ω₁ ^ 2‖ * (4 / 3 * ‖Complex.cos (π * z / H.ω₁)‖ +
        8 * Real.exp (π * |(z / H.ω₁).im|) ^ 2) +
        ‖1 / H.ω₁‖ * (‖π ^ 2 / (12 * H.ω₁)‖ * 352)) * ‖H.nome ^ 4‖ := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hω := H.ω₁_ne_zero
  set q := H.nome with hqdef
  set Y := π * |(z / H.ω₁).im| with hY
  have hY0 : 0 ≤ Y := by positivity
  set E := Real.exp Y with hE
  have hE1 : 1 ≤ E := Real.one_le_exp hY0
  have hq2 : ‖q‖ ≤ 1 / 2 := by
    refine hq.trans ?_
    have : Real.exp (-Y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hρ : ‖q‖ ^ 2 * E ≤ 1 / 4 := by
    have h0 := norm_nonneg q
    have hEm : Real.exp (-Y) * E = 1 := by rw [hE, ← Real.exp_add]; simp
    have hsq : ‖q‖ ^ 2 ≤ (Real.exp (-Y) / 2) ^ 2 := pow_le_pow_left₀ h0 hq 2
    have hEp : 0 < E := Real.exp_pos _
    have hem : Real.exp (-Y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hep : 0 < Real.exp (-Y) := Real.exp_pos _
    calc ‖q‖ ^ 2 * E ≤ (Real.exp (-Y) / 2) ^ 2 * E := mul_le_mul_of_nonneg_right hsq hEp.le
      _ = Real.exp (-Y) * (Real.exp (-Y) * E) / 4 := by ring
      _ ≤ 1 / 4 := by rw [hEm]; linarith
  set c := Complex.cos (π * z / H.ω₁)
  have hcos : ∀ m : ℕ, ‖Complex.cos ((m : ℂ) * π * z / H.ω₁)‖ ≤ E ^ m := by
    intro m
    refine (norm_cos_le_exp_abs_im _).trans ?_
    rw [hE, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have : ((m : ℂ) * π * z / H.ω₁).im = m * π * (z / H.ω₁).im := by
      rw [show (m : ℂ) * π * z / H.ω₁ = ((m * π : ℝ) : ℂ) * (z / H.ω₁) by push_cast; ring,
        Complex.im_ofReal_mul]
    rw [this, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg m), abs_of_pos Real.pi_pos, hY]
    ring_nf; rfl
  -- the Fourier series
  have hF := H.weierstrassP_fourier hz hzi
  set a : ℕ → ℂ := fun n => ((n + 1 : ℕ) : ℂ) * q ^ (2 * (n + 1)) / (1 - q ^ (2 * (n + 1))) *
    Complex.cos (((n + 1 : ℕ) : ℂ) * π * z / H.ω₁) with ha
  have hk : (2 * π ^ 2 / H.ω₁ ^ 2 : ℂ) ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 hπ)) (pow_ne_zero 2 hω)
  have hA : HasSum a (-(H.weierstrassP z + H.eta 1 / H.ω₁ -
      π ^ 2 / (4 * H.ω₁ ^ 2) * (1 / Complex.sin (π * z / (2 * H.ω₁)) ^ 2)) /
        (2 * π ^ 2 / H.ω₁ ^ 2)) := by
    convert (hF.neg.div_const (2 * π ^ 2 / H.ω₁ ^ 2)) using 1
    funext n; simp only [ha]; push_cast; field_simp; rw [← hqdef]; ring
  set Aval := -(H.weierstrassP z + H.eta 1 / H.ω₁ -
      π ^ 2 / (4 * H.ω₁ ^ 2) * (1 / Complex.sin (π * z / (2 * H.ω₁)) ^ 2)) /
        (2 * π ^ 2 / H.ω₁ ^ 2) with hAval
  have hR := (hasSum_nat_add_iff' 1).mpr hA
  simp only [Finset.range_one, Finset.sum_singleton] at hR
  have hn1 : (3 / 4 : ℝ) ≤ ‖1 - q ^ 2‖ := by
    have := norm_sub_norm_le (1 : ℂ) (q ^ 2)
    rw [norm_one, norm_pow] at this; nlinarith [norm_nonneg q]
  have h1q : 1 - q ^ 2 ≠ 0 := fun h0 => by rw [h0, norm_zero] at hn1; norm_num at hn1
  have ha0 : a 0 - c * q ^ 2 = c * q ^ 4 / (1 - q ^ 2) := by
    simp only [ha, c]; push_cast; field_simp; ring
  have hb0 : ‖a 0 - c * q ^ 2‖ ≤ 4 / 3 * ‖c‖ * ‖q ^ 4‖ := by
    rw [ha0, norm_div, norm_mul, div_le_iff₀ (by linarith)]
    have := mul_nonneg (norm_nonneg c) (norm_nonneg (q ^ 4))
    nlinarith
  have hRb := norm_le_of_hasSum_le_mul_pow hR (ρ := ‖q‖ ^ 2 * E) (C := 4 / 3)
    (by positivity) (by linarith) (by norm_num) (fun n => by
      have := norm_lambert_term_le (g := Complex.cos (((n + 1 + 1 : ℕ) : ℂ) * π * z / H.ω₁))
        hE1 hq2 (m := n + 1 + 1) (by omega) (hcos _)
      convert this using 1
      push_cast; ring)
  have key : H.weierstrassP z - π ^ 2 / (4 * H.ω₁ ^ 2) *
        (-1 / 3 + 1 / Complex.sin (π * z / (2 * H.ω₁)) ^ 2 + 8 * (1 - c) * q ^ 2) =
      -(2 * π ^ 2 / H.ω₁ ^ 2) * ((a 0 - c * q ^ 2) + (Aval - a 0)) -
        1 / H.ω₁ * (H.eta 1 - π ^ 2 / (4 * H.ω₁) * (1 / 3 - 8 * q ^ 2)) := by
    rw [hAval]; field_simp; ring
  rw [key]
  have hη := norm_eta_one_sub_le H hq2
  have hq4 : ‖q ^ 4‖ = (‖q‖ ^ 2) ^ 2 := by rw [norm_pow]; ring
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_neg]
  have h1 : ‖(a 0 - c * q ^ 2) + (Aval - a 0)‖ ≤
      4 / 3 * ‖c‖ * ‖q ^ 4‖ + 8 * E ^ 2 * ‖q ^ 4‖ := by
    refine (norm_add_le _ _).trans (add_le_add hb0 ?_)
    rw [hq4]; nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 (norm_nonneg (2 * π ^ 2 / H.ω₁ ^ 2 : ℂ))
  have h3 := mul_le_mul_of_nonneg_left hη (norm_nonneg (1 / H.ω₁))
  nlinarith

/-- Explicit form of DLMF 23.12.2 under the conditions of `eventually_fourier_conditions`. -/

private lemma norm_weierstrassZeta_sub_le (H : HalfPeriods) {z : ℂ} (hz : z ∉ H.lattice)
    (hzi : |(z / H.ω₁).im| < 2 * H.tau.im)
    (hq : ‖H.nome‖ ≤ Real.exp (-(π * |(z / H.ω₁).im|)) / 2) :
    ‖H.weierstrassZeta z - π ^ 2 / (4 * H.ω₁ ^ 2) *
        (z / 3 + 2 * H.ω₁ / π * Complex.cot (π * z / (2 * H.ω₁)) -
          8 * (z - H.ω₁ / π * Complex.sin (π * z / H.ω₁)) * H.nome ^ 2)‖ ≤
      (‖2 * π / H.ω₁‖ * (4 / 3 * ‖Complex.sin (π * z / H.ω₁)‖ +
        8 * Real.exp (π * |(z / H.ω₁).im|) ^ 2) +
        ‖z / H.ω₁‖ * (‖π ^ 2 / (12 * H.ω₁)‖ * 352)) * ‖H.nome ^ 4‖ := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hω := H.ω₁_ne_zero
  set q := H.nome with hqdef
  set Y := π * |(z / H.ω₁).im| with hY
  have hY0 : 0 ≤ Y := by positivity
  set E := Real.exp Y with hE
  have hE1 : 1 ≤ E := Real.one_le_exp hY0
  have hq2 : ‖q‖ ≤ 1 / 2 := by
    refine hq.trans ?_
    have : Real.exp (-Y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hρ : ‖q‖ ^ 2 * E ≤ 1 / 4 := by
    have h0 := norm_nonneg q
    have hEm : Real.exp (-Y) * E = 1 := by rw [hE, ← Real.exp_add]; simp
    have hsq : ‖q‖ ^ 2 ≤ (Real.exp (-Y) / 2) ^ 2 := pow_le_pow_left₀ h0 hq 2
    have hEp : 0 < E := Real.exp_pos _
    have hem : Real.exp (-Y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hep : 0 < Real.exp (-Y) := Real.exp_pos _
    calc ‖q‖ ^ 2 * E ≤ (Real.exp (-Y) / 2) ^ 2 * E := mul_le_mul_of_nonneg_right hsq hEp.le
      _ = Real.exp (-Y) * (Real.exp (-Y) * E) / 4 := by ring
      _ ≤ 1 / 4 := by rw [hEm]; linarith
  set c := Complex.sin (π * z / H.ω₁)
  have hcos : ∀ m : ℕ, ‖Complex.sin ((m : ℂ) * π * z / H.ω₁)‖ ≤ E ^ m := by
    intro m
    refine (norm_sin_le_exp_abs_im _).trans ?_
    rw [hE, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have : ((m : ℂ) * π * z / H.ω₁).im = m * π * (z / H.ω₁).im := by
      rw [show (m : ℂ) * π * z / H.ω₁ = ((m * π : ℝ) : ℂ) * (z / H.ω₁) by push_cast; ring,
        Complex.im_ofReal_mul]
    rw [this, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg m), abs_of_pos Real.pi_pos, hY]
    ring_nf; rfl
  -- the Fourier series
  have hF := H.weierstrassZeta_fourier hz hzi
  set a : ℕ → ℂ := fun n => q ^ (2 * (n + 1)) / (1 - q ^ (2 * (n + 1))) *
    Complex.sin (((n + 1 : ℕ) : ℂ) * π * z / H.ω₁) with ha
  have hk : (2 * π / H.ω₁ : ℂ) ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero hπ) hω
  have hA : HasSum a ((H.weierstrassZeta z - H.eta 1 * z / H.ω₁ -
      π / (2 * H.ω₁) * Complex.cot (π * z / (2 * H.ω₁))) / (2 * π / H.ω₁)) := by
    convert (hF.div_const (2 * π / H.ω₁)) using 1
    funext n; simp only [ha]; push_cast; field_simp; rw [← hqdef]; ring
  set Aval := (H.weierstrassZeta z - H.eta 1 * z / H.ω₁ -
      π / (2 * H.ω₁) * Complex.cot (π * z / (2 * H.ω₁))) / (2 * π / H.ω₁) with hAval
  have hR := (hasSum_nat_add_iff' 1).mpr hA
  simp only [Finset.range_one, Finset.sum_singleton] at hR
  have hn1 : (3 / 4 : ℝ) ≤ ‖1 - q ^ 2‖ := by
    have := norm_sub_norm_le (1 : ℂ) (q ^ 2)
    rw [norm_one, norm_pow] at this; nlinarith [norm_nonneg q]
  have h1q : 1 - q ^ 2 ≠ 0 := fun h0 => by rw [h0, norm_zero] at hn1; norm_num at hn1
  have ha0 : a 0 - c * q ^ 2 = c * q ^ 4 / (1 - q ^ 2) := by
    simp only [ha, c]; push_cast; field_simp; ring
  have hb0 : ‖a 0 - c * q ^ 2‖ ≤ 4 / 3 * ‖c‖ * ‖q ^ 4‖ := by
    rw [ha0, norm_div, norm_mul, div_le_iff₀ (by linarith)]
    have := mul_nonneg (norm_nonneg c) (norm_nonneg (q ^ 4))
    nlinarith
  have hRb := norm_le_of_hasSum_le_mul_pow hR (ρ := ‖q‖ ^ 2 * E) (C := 4 / 3)
    (by positivity) (by linarith) (by norm_num) (fun n => by
      have := norm_lambert_term_le (g := Complex.sin (((n + 1 + 1 : ℕ) : ℂ) * π * z / H.ω₁))
        hE1 hq2 (m := n + 1 + 1) (by omega) (hcos _)
      refine le_trans ?_ (this.trans_eq (by push_cast; ring))
      have e : ((n + 1 + 1 : ℕ) : ℂ) * q ^ (2 * (n + 1 + 1)) / (1 - q ^ (2 * (n + 1 + 1))) *
          Complex.sin (((n + 1 + 1 : ℕ) : ℂ) * π * z / H.ω₁) =
          ((n + 1 + 1 : ℕ) : ℂ) * a (n + 1) := by simp only [ha]; ring
      rw [e, norm_mul ((n + 1 + 1 : ℕ) : ℂ), Complex.norm_natCast]
      have h0 := norm_nonneg (a (n + 1))
      have : (1 : ℝ) ≤ ((n + 1 + 1 : ℕ) : ℝ) := by push_cast; linarith [n.cast_nonneg (α := ℝ)]
      nlinarith)
  have key : H.weierstrassZeta z - π ^ 2 / (4 * H.ω₁ ^ 2) *
        (z / 3 + 2 * H.ω₁ / π * Complex.cot (π * z / (2 * H.ω₁)) -
          8 * (z - H.ω₁ / π * c) * q ^ 2) =
      (2 * π / H.ω₁) * ((a 0 - c * q ^ 2) + (Aval - a 0)) +
        z / H.ω₁ * (H.eta 1 - π ^ 2 / (4 * H.ω₁) * (1 / 3 - 8 * q ^ 2)) := by
    rw [hAval]; field_simp; ring
  rw [key]
  have hη := norm_eta_one_sub_le H hq2
  have hq4 : ‖q ^ 4‖ = (‖q‖ ^ 2) ^ 2 := by rw [norm_pow]; ring
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h1 : ‖(a 0 - c * q ^ 2) + (Aval - a 0)‖ ≤
      4 / 3 * ‖c‖ * ‖q ^ 4‖ + 8 * E ^ 2 * ‖q ^ 4‖ := by
    refine (norm_add_le _ _).trans (add_le_add hb0 ?_)
    rw [hq4]; nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 (norm_nonneg (2 * π / H.ω₁ : ℂ))
  have h3 := mul_le_mul_of_nonneg_left hη (norm_nonneg (z / H.ω₁))
  nlinarith

/-- The coefficient `4 sin²(πz/(2ω)) - π²z²/ω²` of `q²` in DLMF 23.12.3. -/
private def sigmaEps (ω z : ℂ) : ℂ := 4 * Complex.sin (π * z / (2 * ω)) ^ 2 - π ^ 2 * z ^ 2 / ω ^ 2

/-- A constant for the `O(q⁴)` remainder of the exponent in DLMF 23.12.3. -/
private def sigmaM (ω z : ℂ) : ℝ :=
  ‖z ^ 2 / (2 * ω)‖ * (‖π ^ 2 / (12 * ω)‖ * 352) +
    (16 * ‖Complex.sin (π * z / (2 * ω)) ^ 2‖ + (64 / 9 * ‖Complex.sin (π * z / (2 * ω)) ^ 2‖) ^ 2 +
      64 * ‖Complex.sin (π * z / (2 * ω)) ^ 2‖)

/-- Explicit form of DLMF 23.12.3 for small nome. -/
private lemma norm_weierstrassSigma_sub_le (H : HalfPeriods) (z : ℂ)
    (hq : ‖H.nome‖ ≤ 1 / 2)
    (hu : 64 / 9 * ‖Complex.sin (π * z / (2 * H.ω₁)) ^ 2‖ * ‖H.nome‖ ^ 2 ≤ 1 / 2)
    (hv : (‖sigmaEps H.ω₁ z‖ + sigmaM H.ω₁ z) * ‖H.nome‖ ^ 2 ≤ 1) :
    ‖H.weierstrassSigma z - 2 * H.ω₁ / π * cexp (π ^ 2 * z ^ 2 / (24 * H.ω₁ ^ 2)) *
        Complex.sin (π * z / (2 * H.ω₁)) *
        (1 - (π ^ 2 * z ^ 2 / H.ω₁ ^ 2 - 4 * Complex.sin (π * z / (2 * H.ω₁)) ^ 2) *
          H.nome ^ 2)‖ ≤
      ‖2 * H.ω₁ / π * cexp (π ^ 2 * z ^ 2 / (24 * H.ω₁ ^ 2)) * Complex.sin (π * z / (2 * H.ω₁))‖ *
        ((‖sigmaEps H.ω₁ z‖ + sigmaM H.ω₁ z) ^ 2 + sigmaM H.ω₁ z) * ‖H.nome ^ 4‖ := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hω := H.ω₁_ne_zero
  set q := H.nome with hqdef
  set w := π * z / (2 * H.ω₁) with hw
  set s2 := Complex.sin w ^ 2 with hs2
  set K := ‖s2‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  have hq0 := norm_nonneg q
  set ρ := ‖q‖ ^ 2 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ4 : ρ ≤ 1 / 4 := by
    have := pow_le_pow_left₀ hq0 hq 2
    rw [hρ]; linarith [show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num]
  set u : ℕ → ℂ := fun n => 4 * s2 * q ^ (2 * (n + 1)) / (1 - q ^ (2 * (n + 1))) ^ 2 with hudef
  have hx : ∀ n : ℕ, ‖q ^ (2 * (n + 1))‖ = ρ ^ (n + 1) := by
    intro n; rw [norm_pow, pow_mul]
  have hxl : ∀ n : ℕ, ρ ^ (n + 1) ≤ ρ := fun n =>
    pow_le_of_le_one hρ0 (by linarith) (by omega)
  have hd : ∀ n : ℕ, (3 / 4 : ℝ) ≤ ‖1 - q ^ (2 * (n + 1))‖ := by
    intro n
    have := norm_sub_norm_le (1 : ℂ) (q ^ (2 * (n + 1)))
    rw [norm_one, hx] at this; linarith [hxl n]
  have hd0 : ∀ n : ℕ, 1 - q ^ (2 * (n + 1)) ≠ 0 := fun n h0 => by
    have := hd n; rw [h0, norm_zero] at this; norm_num at this
  have hub : ∀ n : ℕ, ‖u n‖ ≤ 64 / 9 * K * ρ ^ (n + 1) := by
    intro n
    have h9 : (9 / 16 : ℝ) ≤ ‖1 - q ^ (2 * (n + 1))‖ ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) (hd n) 2
      linarith [show ((3 : ℝ) / 4) ^ 2 = 9 / 16 by norm_num]
    have e : ‖u n‖ = 4 * K * ρ ^ (n + 1) / ‖1 - q ^ (2 * (n + 1))‖ ^ 2 := by
      simp only [hudef]
      rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat, hx, norm_pow (1 - _)]
    rw [e, div_le_iff₀ (by have := hd n; positivity)]
    have : 0 ≤ K * ρ ^ (n + 1) := by positivity
    have := mul_le_mul_of_nonneg_left h9 this
    linarith
  have hu2 : ∀ n : ℕ, ‖u n‖ ≤ 1 / 2 := by
    intro n
    refine (hub n).trans ?_
    have := mul_le_mul_of_nonneg_left (hxl n) (show 0 ≤ 64 / 9 * K by positivity)
    linarith
  -- the product
  obtain ⟨-, hσ⟩ := H.weierstrassSigma_prod z
  have hc : Complex.cos (π * z / H.ω₁) = 1 - 2 * s2 := by
    rw [show π * z / H.ω₁ = 2 * w by rw [hw]; field_simp, Complex.cos_two_mul]
    have := Complex.sin_sq_add_cos_sq w
    rw [hs2]; linear_combination 2 * this
  have hP : ∀ n : ℕ, (1 - 2 * q ^ (2 * (n + 1)) * Complex.cos (π * z / H.ω₁) +
      q ^ (4 * (n + 1))) / (1 - q ^ (2 * (n + 1))) ^ 2 = 1 + u n := by
    intro n
    have h4 : q ^ (4 * (n + 1)) = (q ^ (2 * (n + 1))) ^ 2 := by
      rw [← pow_mul, show 2 * (n + 1) * 2 = 4 * (n + 1) by ring]
    rw [hc, h4]
    simp only [hudef]
    rw [eq_comm, one_add_div (pow_ne_zero 2 (hd0 n))]
    congr 1; ring
  have hsum_u : Summable u := by
    refine Summable.of_norm_bounded (g := fun n => 64 / 9 * K * ρ ^ (n + 1)) ?_ hub
    exact ((summable_geometric_of_lt_one hρ0 (by linarith)).mul_left (64 / 9 * K * ρ)).congr
      fun n => by ring
  have hlog := Complex.summable_log_one_add_of_summable hsum_u
  have hne : ∀ n, 1 + u n ≠ 0 := by
    intro n h0
    have : ‖u n‖ = 1 := by rw [show u n = -1 by linear_combination h0]; simp
    linarith [hu2 n]
  set L := ∑' n, Complex.log (1 + u n) with hL
  have hprod : ∏' n : ℕ, (1 - 2 * q ^ (2 * (n + 1)) * Complex.cos (π * z / H.ω₁) +
      q ^ (4 * (n + 1))) / (1 - q ^ (2 * (n + 1))) ^ 2 = cexp L := by
    rw [tprod_congr hP, hL, Complex.cexp_tsum_eq_tprod hne hlog]
  -- bounds on `L`
  have hL1 := (hasSum_nat_add_iff' 1).mpr hlog.hasSum
  simp only [Finset.range_one, Finset.sum_singleton] at hL1
  have hLt := norm_le_of_hasSum_le_mul_pow hL1 (ρ := ρ) (C := 32 / 3 * K) hρ0 (by linarith)
    (by positivity) (fun n => by
      refine (Complex.norm_log_one_add_half_le_self (hu2 (n + 1))).trans ?_
      have h1 := hub (n + 1)
      have h2 : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith [n.cast_nonneg (α := ℝ)]
      have h3 : 0 ≤ K * ρ ^ (n + 2) := by positivity
      rw [show n + 1 + 1 = n + 2 by ring] at h1
      have := mul_le_mul_of_nonneg_left h2 h3
      linarith)
  have hl0 : ‖Complex.log (1 + u 0) - u 0‖ ≤ (64 / 9 * K) ^ 2 * ρ ^ 2 := by
    refine (Complex.norm_log_one_add_sub_self_le (by linarith [hu2 0])).trans ?_
    have h1 : (1 - ‖u 0‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith [hu2 0]) (by norm_num)]; linarith [hu2 0]
    have h2 : ‖u 0‖ ≤ 64 / 9 * K * ρ := by simpa using hub 0
    have h3 : ‖u 0‖ ^ 2 ≤ (64 / 9 * K * ρ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h4 : 0 ≤ ‖u 0‖ ^ 2 := by positivity
    have h5 : ‖u 0‖ ^ 2 * (1 - ‖u 0‖)⁻¹ ≤ ‖u 0‖ ^ 2 * 2 := mul_le_mul_of_nonneg_left h1 h4
    have : (64 / 9 * K * ρ) ^ 2 = (64 / 9 * K) ^ 2 * ρ ^ 2 := by ring
    linarith
  have hu0 : ‖u 0 - 4 * s2 * q ^ 2‖ ≤ 16 * K * ρ ^ 2 := by
    have h1q := hd0 0
    simp only [zero_add, mul_one] at h1q
    have e : u 0 - 4 * s2 * q ^ 2 = 4 * s2 * (q ^ 4 * (2 - q ^ 2)) / (1 - q ^ 2) ^ 2 := by
      simp only [hudef]; field_simp; ring
    rw [e, norm_div, norm_mul, norm_mul, norm_mul, norm_pow q 4, norm_pow (1 - q ^ 2) 2,
      Complex.norm_ofNat]
    have hn1 : (3 / 4 : ℝ) ≤ ‖1 - q ^ 2‖ := by simpa using hd 0
    have h2 : ‖2 - q ^ 2‖ ≤ 9 / 4 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow, ← hρ, Complex.norm_ofNat]; linarith
    rw [div_le_iff₀ (pow_pos (by linarith) 2)]
    have h9 : (9 / 16 : ℝ) ≤ ‖1 - q ^ 2‖ ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) hn1 2
      linarith [show ((3 : ℝ) / 4) ^ 2 = 9 / 16 by norm_num]
    have : ‖q‖ ^ 4 = ρ ^ 2 := by rw [hρ]; ring
    rw [this]
    have h0 : 0 ≤ K * ρ ^ 2 := by positivity
    have A := mul_le_mul_of_nonneg_left h2 h0
    have B := mul_le_mul_of_nonneg_left h9 h0
    linarith
  have hLb : ‖L - 4 * s2 * q ^ 2‖ ≤ (16 * K + (64 / 9 * K) ^ 2 + 64 * K) * ρ ^ 2 := by
    have e : L - 4 * s2 * q ^ 2 = (L - Complex.log (1 + u 0)) +
        (Complex.log (1 + u 0) - u 0) + (u 0 - 4 * s2 * q ^ 2) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le (L - Complex.log (1 + u 0)) (Complex.log (1 + u 0) - u 0)
    linarith
  -- the exponent
  have hη := norm_eta_one_sub_le H hq
  set δ := H.eta 1 * z ^ 2 / (2 * H.ω₁) - π ^ 2 * z ^ 2 / (24 * H.ω₁ ^ 2) with hδ
  have hδe : δ + π ^ 2 * z ^ 2 / H.ω₁ ^ 2 * q ^ 2 =
      z ^ 2 / (2 * H.ω₁) * (H.eta 1 - π ^ 2 / (4 * H.ω₁) * (1 / 3 - 8 * q ^ 2)) := by
    rw [hδ]; field_simp; ring
  have hq4 : ‖q ^ 4‖ = ρ ^ 2 := by rw [norm_pow, hρ]; ring
  set M := sigmaM H.ω₁ z with hM
  set ε := sigmaEps H.ω₁ z with hε
  set v := δ + L with hv'
  have hvε : ‖v - ε * q ^ 2‖ ≤ M * ρ ^ 2 := by
    have e : v - ε * q ^ 2 = (δ + π ^ 2 * z ^ 2 / H.ω₁ ^ 2 * q ^ 2) + (L - 4 * s2 * q ^ 2) := by
      rw [hv', hε, sigmaEps]; ring
    rw [e, hδe]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have h1 := mul_le_mul_of_nonneg_left hη (norm_nonneg (z ^ 2 / (2 * H.ω₁)))
    rw [hq4] at h1
    rw [hM, sigmaM]
    linarith
  have hM0 : 0 ≤ M := by rw [hM, sigmaM]; positivity
  have hvb : ‖v‖ ≤ (‖ε‖ + M) * ρ := by
    have h1 : ‖v‖ ≤ ‖ε * q ^ 2‖ + M * ρ ^ 2 := by
      have := norm_le_insert' v (ε * q ^ 2)
      linarith [norm_sub_rev v (ε * q ^ 2)]
    rw [norm_mul, norm_pow] at h1
    have : M * ρ ^ 2 ≤ M * ρ :=
      mul_le_mul_of_nonneg_left (pow_le_of_le_one hρ0 (by linarith) two_ne_zero) hM0
    rw [← hρ] at h1
    linarith
  have hv1 : ‖v‖ ≤ 1 := hvb.trans hv
  have hexp := Complex.norm_exp_sub_one_sub_id_le hv1
  have hσ' : H.weierstrassSigma z = 2 * H.ω₁ / π * cexp (π ^ 2 * z ^ 2 / (24 * H.ω₁ ^ 2)) *
      Complex.sin w * cexp v := by
    have he : cexp (H.eta 1 * z ^ 2 / (2 * H.ω₁)) =
        cexp (π ^ 2 * z ^ 2 / (24 * H.ω₁ ^ 2)) * cexp δ := by
      rw [← Complex.exp_add, hδ]; ring_nf
    rw [hσ, hprod, hv', Complex.exp_add, he]
    ring
  rw [hσ', show (1 - (π ^ 2 * z ^ 2 / H.ω₁ ^ 2 - 4 * s2) * q ^ 2) = 1 + ε * q ^ 2 by
    rw [hε, sigmaEps]; ring]
  have key : ‖cexp v - (1 + ε * q ^ 2)‖ ≤ ((‖ε‖ + M) ^ 2 + M) * ρ ^ 2 := by
    have e : cexp v - (1 + ε * q ^ 2) = (cexp v - 1 - v) + (v - ε * q ^ 2) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have : ‖v‖ ^ 2 ≤ ((‖ε‖ + M) * ρ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvb 2
    linarith
  set Cst := 2 * H.ω₁ / π * cexp (π ^ 2 * z ^ 2 / (24 * H.ω₁ ^ 2)) * Complex.sin w with hCst
  rw [← mul_sub, norm_mul, hq4]
  calc ‖Cst‖ * ‖cexp v - (1 + ε * q ^ 2)‖ ≤ ‖Cst‖ * (((‖ε‖ + M) ^ 2 + M) * ρ ^ 2) :=
        mul_le_mul_of_nonneg_left key (norm_nonneg _)
    _ = ‖Cst‖ * ((‖ε‖ + M) ^ 2 + M) * ρ ^ 2 := by ring

/-- DLMF 23.12.1: as `q → 0` with `ω₁` and `z ∉ 2ω₁ℤ` fixed,
`℘(z) = (π²/(4ω₁²))(-1/3 + csc²(πz/(2ω₁)) + 8(1 - cos(πz/ω₁))q² + O(q⁴))`. -/
@[dlmf 23.12.E1]
theorem weierstrassP_isBigO_nome (ω : ℂ) (hω : ω ≠ 0) {z : ℂ} (hz : ∀ m : ℤ, z ≠ 2 * m * ω) :
    (fun τ : ℍ ↦ (ofTau ω hω τ).weierstrassP z - π ^ 2 / (4 * ω ^ 2) *
        (-1 / 3 + 1 / Complex.sin (π * z / (2 * ω)) ^ 2 +
          8 * (1 - Complex.cos (π * z / ω)) * (ofTau ω hω τ).nome ^ 2)) =O[atImInfty]
      fun τ ↦ (ofTau ω hω τ).nome ^ 4 := by
  refine IsBigO.of_bound ((‖2 * π ^ 2 / ω ^ 2‖ * (4 / 3 * ‖Complex.cos (π * z / ω)‖ +
        8 * Real.exp (π * |(z / ω).im|) ^ 2) +
        ‖1 / ω‖ * (‖π ^ 2 / (12 * ω)‖ * 352))) ?_
  filter_upwards [eventually_fourier_conditions ω hω hz] with τ h
  exact norm_weierstrassP_sub_le (ofTau ω hω τ) h.1 h.2.1 h.2.2

/-- DLMF 23.12.2: as `q → 0` with `ω₁` and `z ∉ 2ω₁ℤ` fixed,
`ζ(z) = (π²/(4ω₁²))(z/3 + (2ω₁/π)cot(πz/(2ω₁)) - 8(z - (ω₁/π)sin(πz/ω₁))q² + O(q⁴))`. -/
@[dlmf 23.12.E2]
theorem weierstrassZeta_isBigO_nome (ω : ℂ) (hω : ω ≠ 0) {z : ℂ} (hz : ∀ m : ℤ, z ≠ 2 * m * ω) :
    (fun τ : ℍ ↦ (ofTau ω hω τ).weierstrassZeta z - π ^ 2 / (4 * ω ^ 2) *
        (z / 3 + 2 * ω / π * Complex.cot (π * z / (2 * ω)) -
          8 * (z - ω / π * Complex.sin (π * z / ω)) * (ofTau ω hω τ).nome ^ 2)) =O[atImInfty]
      fun τ ↦ (ofTau ω hω τ).nome ^ 4 := by
  refine IsBigO.of_bound ((‖2 * π / ω‖ * (4 / 3 * ‖Complex.sin (π * z / ω)‖ +
        8 * Real.exp (π * |(z / ω).im|) ^ 2) +
        ‖z / ω‖ * (‖π ^ 2 / (12 * ω)‖ * 352))) ?_
  filter_upwards [eventually_fourier_conditions ω hω hz] with τ h
  exact norm_weierstrassZeta_sub_le (ofTau ω hω τ) h.1 h.2.1 h.2.2

/-- DLMF 23.12.3: as `q → 0` with `ω₁` and `z` fixed,
`σ(z) = (2ω₁/π)exp(π²z²/(24ω₁²))sin(πz/(2ω₁))(1 - (π²z²/ω₁² - 4sin²(πz/(2ω₁)))q² + O(q⁴))`. -/
@[dlmf 23.12.E3]
theorem weierstrassSigma_isBigO_nome (ω : ℂ) (hω : ω ≠ 0) (z : ℂ) :
    (fun τ : ℍ ↦ (ofTau ω hω τ).weierstrassSigma z - 2 * ω / π *
        cexp (π ^ 2 * z ^ 2 / (24 * ω ^ 2)) * Complex.sin (π * z / (2 * ω)) *
        (1 - (π ^ 2 * z ^ 2 / ω ^ 2 - 4 * Complex.sin (π * z / (2 * ω)) ^ 2) *
          (ofTau ω hω τ).nome ^ 2)) =O[atImInfty]
      fun τ ↦ (ofTau ω hω τ).nome ^ 4 := by
  set K := ‖Complex.sin (π * z / (2 * ω)) ^ 2‖ with hK
  have hM0 : 0 ≤ sigmaM ω z := by rw [sigmaM]; positivity
  set X := 2 + 64 / 9 * K + ‖sigmaEps ω z‖ + sigmaM ω z with hX
  have hX2 : 2 ≤ X := by
    have := norm_nonneg (sigmaEps ω z); have : 0 ≤ K := norm_nonneg _; linarith
  have hX0 : 0 < X := by linarith
  refine IsBigO.of_bound (‖2 * ω / π * cexp (π ^ 2 * z ^ 2 / (24 * ω ^ 2)) *
    Complex.sin (π * z / (2 * ω))‖ * ((‖sigmaEps ω z‖ + sigmaM ω z) ^ 2 + sigmaM ω z)) ?_
  filter_upwards [eventually_norm_nome_le ω hω (ε := 1 / X) (by positivity)] with τ hq
  have hq0 := norm_nonneg (ofTau ω hω τ).nome
  have hXi : 1 / X ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hX2
  have hq2 : ‖(ofTau ω hω τ).nome‖ ≤ 1 / 2 := hq.trans hXi
  have hsq : ‖(ofTau ω hω τ).nome‖ ^ 2 ≤ 1 / X * (1 / 2) := by
    rw [sq]; exact mul_le_mul hq hq2 hq0 (by positivity)
  have hK0 : 0 ≤ K := norm_nonneg _
  refine norm_weierstrassSigma_sub_le (ofTau ω hω τ) z hq2 ?_ ?_
  · have h1 : 64 / 9 * K / X ≤ 1 := by
      rw [div_le_one hX0]; have := norm_nonneg (sigmaEps ω z); linarith
    calc 64 / 9 * K * ‖(ofTau ω hω τ).nome‖ ^ 2 ≤ 64 / 9 * K * (1 / X * (1 / 2)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 64 / 9 * K / X / 2 := by ring
      _ ≤ 1 / 2 := by linarith
  · have h0 : 0 ≤ ‖sigmaEps ω z‖ + sigmaM ω z := by positivity
    have h1 : (‖sigmaEps ω z‖ + sigmaM ω z) / X ≤ 1 := by
      rw [div_le_one hX0]; linarith
    calc (‖sigmaEps (ofTau ω hω τ).ω₁ z‖ + sigmaM (ofTau ω hω τ).ω₁ z) *
          ‖(ofTau ω hω τ).nome‖ ^ 2 ≤ (‖sigmaEps ω z‖ + sigmaM ω z) * (1 / X * (1 / 2)) :=
          mul_le_mul_of_nonneg_left hsq h0
      _ = (‖sigmaEps ω z‖ + sigmaM ω z) / X / 2 := by ring
      _ ≤ 1 := by linarith

/-- DLMF 23.12.4: as `q → 0` with `ω₁` fixed, `η₁ = (π²/(4ω₁))(1/3 - 8q² + O(q⁴))`. -/
@[dlmf 23.12.E4]
theorem eta_one_isBigO_nome (ω : ℂ) (hω : ω ≠ 0) :
    (fun τ : ℍ ↦ (ofTau ω hω τ).eta 1 - π ^ 2 / (4 * ω) * (1 / 3 - 8 * (ofTau ω hω τ).nome ^ 2))
      =O[atImInfty] fun τ ↦ (ofTau ω hω τ).nome ^ 4 := by
  refine IsBigO.of_bound (‖π ^ 2 / (12 * ω)‖ * 352) ?_
  filter_upwards [eventually_norm_nome_le ω hω (show (0 : ℝ) < 1 / 2 by norm_num)] with τ hq
  exact norm_eta_one_sub_le _ hq

end HalfPeriods

end DLMF.Weierstrass
