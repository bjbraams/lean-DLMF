/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.UniformLG2.PositiveParameterEstimates

/-!
# Algebra of reciprocal-power expansions for parabolic cylinder functions

This file develops asymptotic expansions in reciprocal powers (Cauchy products, reciprocals,
uniqueness and Borel's lemma) and uses them to identify the normalizer of the uniform
expansion DLMF 12.10.3 of `U(a,z)` for negative parameter.

## Main definitions

* `HasInversePowerExpansion`: the expansion `f(u) ∼ ∑ a_s u^{-s}` as `u → ∞`.
* `CylinderUniformExpansion.truncPoly`, `CylinderUniformExpansion.cauchyProduct`,
  `CylinderUniformExpansion.signTwist`, `CylinderUniformExpansion.unitSeq`: truncation polynomials,
  the Cauchy product, the sign twist `a_n ↦ (-1)^n a_n` and the unit sequence.
* `CylinderUniformExpansion.gammaRatio`: the normalized Gamma ratio
  `Γ(1/2 + u/2)/(√(2π) e^{-u/2} (u/2)^{u/2})`.

## Main results

* `HasInversePowerExpansion.unique`, `HasInversePowerExpansion.mul`,
  `HasInversePowerExpansion.recip`: uniqueness, products and reciprocals of expansions.
* `CylinderUniformExpansion.exists_hasInversePowerExpansion`: Borel's lemma for real coefficients.
* `CylinderUniformExpansion.gamma_identity`: the normalizer identity in formal form.
* `pcf_negative_parameter_uniform_U_normalizer`: DLMF 12.10.3 with a normalizer satisfying
  DLMF 12.10.14.

## Implementation notes

Comparing the limits of `U` at `+∞` (DLMF 12.9.1) and at `-∞` (DLMF 12.2.15 with
DLMF 12.9.1–12.9.2) gives the formal identity `(∑ γ_j (u/2)^{-j})(∑ c_s u^{-s}) =
∑ (-1)^s c_s u^{-s}`, where `c_s` is the coefficient of `t^{3s}` in `u_s`. Since the even
`c_s`, `s ≥ 2`, vanish, this yields DLMF 12.10.14 for the normalizer of DLMF 12.10.3.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Confluent

open Polynomial

/-! ### Asymptotic expansions in reciprocal powers: algebra -/

/-- `f(u) ∼ ∑ a_s u^{-s}` as `u → ∞`. -/
def HasInversePowerExpansion (f : ℝ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ N : ℕ, (fun u : ℝ => f u - ∑ s ∈ Finset.range N, a s / (u:ℂ)^s) =O[atTop]
    (fun u : ℝ => (u:ℂ)^(-(N:ℤ)))

/-- The truncation polynomial `∑_{s<N} a_s X^s`. -/
noncomputable def CylinderUniformExpansion.truncPoly (N : ℕ) (a : ℕ → ℂ) : ℂ[X] :=
  ∑ s ∈ Finset.range N, C (a s) * X^s

/-- The Cauchy product of coefficient sequences. -/
def CylinderUniformExpansion.cauchyProduct (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ x ∈ Finset.antidiagonal n, a x.1 * b x.2

/-- The sign twist `a_n ↦ (-1)^n a_n` (the substitution `u ↦ -u`). -/
def CylinderUniformExpansion.signTwist (a : ℕ → ℂ) (n : ℕ) : ℂ := (-1)^n * a n

/-- The unit sequence. -/
def CylinderUniformExpansion.unitSeq (n : ℕ) : ℂ := if n = 0 then 1 else 0

/-- Formula under the stated hypotheses:
`(CylinderUniformExpansion.truncPoly N a).eval ((u:ℂ)⁻¹) = ∑ s ∈ Finset.range N, a s / (u:ℂ)^s`. -/
lemma CylinderUniformExpansion.truncPoly_eval (N : ℕ) (a : ℕ → ℂ) {u : ℝ} :
    (CylinderUniformExpansion.truncPoly N a).eval ((u:ℂ)⁻¹) = ∑ s ∈ Finset.range N,
        a s / (u:ℂ)^s := by
  rw [CylinderUniformExpansion.truncPoly, eval_finsetSum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [div_eq_mul_inv, inv_pow]

/-- Estimate under the stated parameter and domain assumptions:
`(CylinderUniformExpansion.truncPoly N a).coeff n = if n < N then a n else 0`. -/
lemma CylinderUniformExpansion.truncPoly_coeff (N : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    (CylinderUniformExpansion.truncPoly N a).coeff n = if n < N then a n else 0 := by
  rw [CylinderUniformExpansion.truncPoly, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hn; exact absurd (Finset.mem_range.2 h) hn
  · refine Finset.sum_eq_zero fun s hs => ?_
    have : s ≠ n := by rintro rfl; exact h (Finset.mem_range.1 hs)
    simp [Ne.symm this]

/-- A polynomial with vanishing coefficients below `N`, evaluated at `1/u`, is `O(u^{-N})`. -/
lemma CylinderUniformExpansion.isBigO_eval_recip {Q : ℂ[X]} {N : ℕ} (hQ : ∀ n < N, Q.coeff n = 0) :
    (fun u : ℝ => Q.eval ((u:ℂ)⁻¹)) =O[atTop] (fun u : ℝ => (u:ℂ)^(-(N:ℤ))) := by
  obtain ⟨Q', hQ'⟩ := (X_pow_dvd_iff).2 hQ
  have hb : (fun u : ℝ => Q'.eval ((u:ℂ)⁻¹)) =O[atTop] (fun _ => (1:ℂ)) := by
    have h1 : Tendsto (fun u : ℝ => ((u:ℂ)⁻¹)) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).ofReal
      simpa using this
    exact ((Q'.continuous.tendsto 0).comp h1).isBigO_one ℂ
  refine (hb.mul (isBigO_refl (fun u : ℝ => (u:ℂ)^(-(N:ℤ))) atTop)).congr' ?_ ?_
  · filter_upwards with u
    rw [hQ', eval_mul, eval_pow, eval_X, zpow_neg, zpow_natCast, inv_pow]; ring
  · filter_upwards with u; ring

/-- A truncation is eventually bounded. -/
lemma CylinderUniformExpansion.truncPoly_isBigO_one (N : ℕ) (a : ℕ → ℂ) :
    (fun u : ℝ => ∑ s ∈ Finset.range N, a s / (u:ℂ)^s) =O[atTop] (fun _ => (1:ℂ)) := by
  have h1 : Tendsto (fun u : ℝ => ((u:ℂ)⁻¹)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).ofReal
    simpa using this
  refine (((CylinderUniformExpansion.truncPoly N a).continuous.tendsto 0).comp
      h1).isBigO_one ℂ |>.congr' ?_
    EventuallyEq.rfl
  filter_upwards [eventually_ne_atTop 0] with u hu
  exact CylinderUniformExpansion.truncPoly_eval N a

/-- An expansion gives boundedness. -/
theorem HasInversePowerExpansion.isBigO_one {f : ℝ → ℂ} {a : ℕ → ℂ}
    (h : HasInversePowerExpansion f a) :
    f =O[atTop] (fun _ => (1:ℂ)) := by
  have := h 0
  simpa using this

/-- Uniqueness of asymptotic expansions. -/
theorem HasInversePowerExpansion.unique {f : ℝ → ℂ} {a b : ℕ → ℂ}
    (ha : HasInversePowerExpansion f a)
    (hb : HasInversePowerExpansion f b) : a = b := by
  funext n
  rw [← CylinderLiouvilleGreen.asymptoticCoeff_eq ha n,
      CylinderLiouvilleGreen.asymptoticCoeff_eq hb n]

/-- Products of expansions. -/
theorem HasInversePowerExpansion.mul {f g : ℝ → ℂ} {a b : ℕ → ℂ} (ha : HasInversePowerExpansion f a)
    (hb : HasInversePowerExpansion g b) : HasInversePowerExpansion (fun u => f u * g u)
        (CylinderUniformExpansion.cauchyProduct a b) := by
  intro N
  have hQ : ∀ n < N, (CylinderUniformExpansion.truncPoly N a *
      CylinderUniformExpansion.truncPoly N b -
      CylinderUniformExpansion.truncPoly N
          (CylinderUniformExpansion.cauchyProduct a b)).coeff n = 0 := by
    intro n hn
    rw [coeff_sub, coeff_mul, CylinderUniformExpansion.truncPoly_coeff]
    simp only [hn, ↓reduceIte]
    rw [CylinderUniformExpansion.cauchyProduct, sub_eq_zero]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := Finset.mem_antidiagonal.1 hx
    rw [CylinderUniformExpansion.truncPoly_coeff, CylinderUniformExpansion.truncPoly_coeff]
    simp [show x.1 < N by omega, show x.2 < N by omega]
  have h3 := CylinderUniformExpansion.isBigO_eval_recip hQ
  have h1 : (fun u : ℝ => (f u - ∑ s ∈ Finset.range N, a s / (u:ℂ)^s) * g u) =O[atTop]
      (fun u : ℝ => (u:ℂ)^(-(N:ℤ))) := by
    simpa only [mul_one] using (ha N).mul hb.isBigO_one
  have h2 : (fun u : ℝ => (∑ s ∈ Finset.range N, a s / (u:ℂ)^s) *
      (g u - ∑ s ∈ Finset.range N, b s / (u:ℂ)^s)) =O[atTop] (fun u : ℝ => (u:ℂ)^(-(N:ℤ))) := by
    simpa only [one_mul] using (CylinderUniformExpansion.truncPoly_isBigO_one N a).mul (hb N)
  refine ((h1.add h2).add h3).congr' ?_ ?_
  · filter_upwards [eventually_ne_atTop 0] with u hu
    simp only [eval_sub, eval_mul, CylinderUniformExpansion.truncPoly_eval _ _]
    ring
  · filter_upwards with u; ring

/-- Sums of expansions. -/
theorem HasInversePowerExpansion.sub {f g : ℝ → ℂ} {a b : ℕ → ℂ} (ha : HasInversePowerExpansion f a)
    (hb : HasInversePowerExpansion g b) : HasInversePowerExpansion (fun u => f u - g u)
        (fun n => a n - b n) := by
  intro N
  refine ((ha N).sub (hb N)).congr' (Eventually.of_forall fun u => ?_) EventuallyEq.rfl
  simp only [sub_div, Finset.sum_sub_distrib]; ring

/-- Expansion of a function that is `O(u^{-N})` for every `N`. -/
theorem HasInversePowerExpansion.of_isBigO {f : ℝ → ℂ}
    (h : ∀ N : ℕ, f =O[atTop] (fun u : ℝ => (u:ℂ)^(-(N:ℤ)))) : HasInversePowerExpansion f 0 := by
  intro N; simpa using h N

/-- **Reciprocals of expansions.** -/
theorem HasInversePowerExpansion.recip {f : ℝ → ℂ} {a d : ℕ → ℂ} (ha : HasInversePowerExpansion f a)
    (had : CylinderUniformExpansion.cauchyProduct a d = CylinderUniformExpansion.unitSeq)
        (hf : (fun u => (f u)⁻¹) =O[atTop] (fun _ => (1:ℂ)))
    (hf0 : ∀ᶠ u in atTop, f u ≠ 0) :
    HasInversePowerExpansion (fun u => (f u)⁻¹) d := by
  intro N
  have hQ : ∀ n < N, (CylinderUniformExpansion.truncPoly N a *
      CylinderUniformExpansion.truncPoly N d - 1).coeff n = 0 := by
    intro n hn
    rw [coeff_sub, coeff_mul, coeff_one, sub_eq_zero]
    have h := congrFun had n
    rw [CylinderUniformExpansion.cauchyProduct, CylinderUniformExpansion.unitSeq] at h
    rw [← h]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := Finset.mem_antidiagonal.1 hx
    rw [CylinderUniformExpansion.truncPoly_coeff, CylinderUniformExpansion.truncPoly_coeff]
    simp [show x.1 < N by omega, show x.2 < N by omega]
  have h3 := CylinderUniformExpansion.isBigO_eval_recip hQ
  have h1 : (fun u : ℝ => (f u - ∑ s ∈ Finset.range N, a s / (u:ℂ)^s) *
      ∑ s ∈ Finset.range N, d s / (u:ℂ)^s) =O[atTop] (fun u : ℝ => (u:ℂ)^(-(N:ℤ))) := by
    simpa only [mul_one] using (ha N).mul (CylinderUniformExpansion.truncPoly_isBigO_one N d)
  -- `1 - f T_N d = -(f - T_N a) T_N d - (T_N a T_N d - 1)`
  have hk : (fun u : ℝ => -((f u)⁻¹ * ((f u - ∑ s ∈ Finset.range N, a s / (u:ℂ)^s) *
      ∑ s ∈ Finset.range N, d s / (u:ℂ)^s +
          (CylinderUniformExpansion.truncPoly N a * CylinderUniformExpansion.truncPoly N d - 1).eval
        ((u:ℂ)⁻¹)))) =O[atTop] (fun u : ℝ => (u:ℂ)^(-(N:ℤ))) := by
    simpa only [one_mul] using (hf.mul (h1.add h3)).neg_left
  refine (hk.congr' ?_ ?_)
  · filter_upwards [eventually_ne_atTop 0, hf0] with u hu hfu
    simp only [eval_sub, eval_mul, eval_one, CylinderUniformExpansion.truncPoly_eval _ _]
    field_simp
    ring
  · filter_upwards with u; ring

/-- The sign twist is multiplicative. -/
lemma CylinderUniformExpansion.cauchyProduct_signTwist (a b : ℕ → ℂ) :
    CylinderUniformExpansion.cauchyProduct (CylinderUniformExpansion.signTwist a)
        (CylinderUniformExpansion.signTwist b) =
        CylinderUniformExpansion.signTwist (CylinderUniformExpansion.cauchyProduct a b) := by
  funext n
  simp only [CylinderUniformExpansion.cauchyProduct, CylinderUniformExpansion.signTwist,
      Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finset.mem_antidiagonal.1 hx, pow_add]; ring

/-- The twist is an involution. -/
lemma CylinderUniformExpansion.signTwist_signTwist (a : ℕ → ℂ) : CylinderUniformExpansion.signTwist
    (CylinderUniformExpansion.signTwist a) = a := by
  funext n; simp only [CylinderUniformExpansion.signTwist]; rw [← mul_assoc, ← mul_pow]; norm_num

/-- Cauchy product is commutative. -/
lemma CylinderUniformExpansion.cauchyProduct_comm (a b : ℕ → ℂ) :
    CylinderUniformExpansion.cauchyProduct a b = CylinderUniformExpansion.cauchyProduct b a := by
  funext n
  simp only [CylinderUniformExpansion.cauchyProduct]
  rw [← Finset.Nat.sum_antidiagonal_swap]
  simp [mul_comm]

/-- Cauchy product is additive. -/
lemma CylinderUniformExpansion.cauchyProduct_add (a b c : ℕ → ℂ) :
    CylinderUniformExpansion.cauchyProduct a (fun n => b n + c n) = fun n =>
        CylinderUniformExpansion.cauchyProduct a b n +
        CylinderUniformExpansion.cauchyProduct a c n := by
  funext n; simp only [CylinderUniformExpansion.cauchyProduct, mul_add, Finset.sum_add_distrib]

/-- Cauchy product with the unit. -/
lemma CylinderUniformExpansion.cauchyProduct_unitSeq (a : ℕ → ℂ) :
    CylinderUniformExpansion.cauchyProduct a CylinderUniformExpansion.unitSeq = a := by
  funext n
  simp only [CylinderUniformExpansion.cauchyProduct, CylinderUniformExpansion.unitSeq]
  rw [Finset.sum_eq_single (n, 0)]
  · simp
  · intro x hx hne
    have h := Finset.mem_antidiagonal.1 hx
    have : x.2 ≠ 0 := by
      intro h2; apply hne; ext <;> simp_all
    simp [this]
  · intro h; exact absurd (Finset.mem_antidiagonal.2 (by simp)) h

/-- Cauchy product with a scalar multiple. -/
lemma CylinderUniformExpansion.cauchyProduct_smul (a b : ℕ → ℂ) (k : ℂ) :
    CylinderUniformExpansion.cauchyProduct a (fun n => k * b n) = fun n => k *
        CylinderUniformExpansion.cauchyProduct a b n := by
  funext n; simp only [CylinderUniformExpansion.cauchyProduct, Finset.mul_sum];
      congr 1; funext x; ring

/-- **The expansion of `Γ(1/2+z)/(√(2π)e^{-z}z^z)` at `z = u/2`** (DLMF 12.10.16). -/
lemma CylinderUniformExpansion.hasInversePowerExpansion_gamma : HasInversePowerExpansion
    (fun u : ℝ => Gamma (1/2+((u/2:ℝ):ℂ))/((Real.sqrt (2*π):ℂ)*exp (-((u/2:ℝ):ℂ))*
      (((u/2:ℝ):ℂ))^(((u/2:ℝ):ℂ))))
    (fun j => pcfGammaCoeff j * 2^j) := by
  intro N
  have h2 : Tendsto (fun u : ℝ => u/2) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  have h := (pcfGammaCoeff_expansion N).comp_tendsto h2
  have hb : (fun u : ℝ => ((u/2:ℝ):ℂ)^(-(N:ℤ))) =O[atTop] (fun u : ℝ => (u:ℂ)^(-(N:ℤ))) := by
    refine IsBigO.of_bound (2^N) (Eventually.of_forall fun u => ?_)
    rw [norm_zpow, norm_zpow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_div, abs_two, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast,
      div_pow, inv_div]
    rw [div_eq_mul_inv]
  refine (h.trans hb).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with u hu
  have hu' : (u:ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  simp only [Function.comp]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  rw [div_pow]
  field_simp

/-- **Borel's lemma** in the form of `HasInversePowerExpansion`, for real coefficients. -/
lemma CylinderUniformExpansion.exists_hasInversePowerExpansion (c : ℕ → ℝ) :
    ∃ Φ : ℝ → ℝ, HasInversePowerExpansion (fun u => (Φ u : ℂ)) (fun s => (c s : ℂ)) := by
  obtain ⟨Φ, hΦ⟩ := CylinderLiouvilleGreen.exists_asymptotic c
  refine ⟨Φ, fun N => ?_⟩
  obtain ⟨B, hB⟩ := (hΦ N).bound
  refine IsBigO.of_bound B ?_
  filter_upwards [hB, eventually_gt_atTop 0] with u hu hu0
  have e : (Φ u : ℂ) - ∑ s ∈ Finset.range N, (c s : ℂ) / (u:ℂ)^s =
      ((Φ u - ∑ s ∈ Finset.range N, c s / u^s : ℝ) : ℂ) := by push_cast; rfl
  rw [e, Complex.norm_real, norm_zpow, Complex.norm_real, zpow_neg, zpow_natCast]
  rwa [norm_inv, norm_pow] at hu

/-- An expansion in `u` gives one in `μ²`. -/
theorem HasInversePowerExpansion.comp_sq {f : ℝ → ℂ} {a : ℕ → ℂ}
    (h : HasInversePowerExpansion f a) (N : ℕ) :
    (fun μ : ℝ => f (μ^2) - ∑ s ∈ Finset.range N, a s / (μ^2:ℂ)^s) =O[atTop]
      (fun μ : ℝ => (μ:ℂ)^(-(2*N:ℤ))) := by
  have h2 : Tendsto (fun μ : ℝ => μ^2) atTop atTop := tendsto_pow_atTop two_ne_zero
  refine ((h N).comp_tendsto h2).congr' (Eventually.of_forall fun μ => ?_)
    (Eventually.of_forall fun μ => ?_)
  · simp only [Function.comp]; push_cast; rfl
  · simp only [Function.comp]; push_cast
    rw [show (2*N:ℤ) = ((2*N:ℕ):ℤ) by push_cast; ring, zpow_neg, zpow_neg, zpow_natCast,
      zpow_natCast, pow_mul]

/-- `μ√2 h(μ)² = e^{-z} z^z` with `z = μ²/2`. -/
lemma CylinderUniformExpansion.normalizer_sq {μ : ℝ} (hμ : 0 < μ) :
    μ * Real.sqrt 2 * CylinderLiouvilleGreen.normalizer μ ^ 2 = Real.exp (-(μ^2/2)) *
        (μ^2/2) ^ (μ^2/2) := by
  have hz : 0 < μ^2/2 := by positivity
  have hh := CylinderLiouvilleGreen.normalizer_pos hμ
  refine Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity)) ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_exp,
    Real.log_rpow hz, Real.log_div (by positivity) (by norm_num), Real.log_pow,
    Real.log_sqrt (by norm_num), CylinderLiouvilleGreen.normalizer,
        Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
    Real.log_rpow hμ, Real.log_exp]
  push_cast; ring

/-- `H₋/H₊ = 1/R̃(μ²/2)`, with `R̃(z) = Γ(1/2+z)/(√(2π)e^{-z}z^z)`. -/
lemma CylinderUniformExpansion.ratio_eq {μ : ℝ} (hμ : 0 < μ) :
    ((Real.sqrt (2*π) * CylinderLiouvilleGreen.normalizer μ : ℝ) : ℂ) / Gamma (1/2 + (μ:ℂ)^2/2) /
      (((μ * Real.sqrt 2 * CylinderLiouvilleGreen.normalizer μ)⁻¹ : ℝ) : ℂ) =
    (Gamma (1/2+((μ^2/2:ℝ):ℂ))/((Real.sqrt (2*π):ℂ)*exp (-((μ^2/2:ℝ):ℂ))*
      (((μ^2/2:ℝ):ℂ))^(((μ^2/2:ℝ):ℂ))))⁻¹ := by
  have hz : 0 < μ^2/2 := by positivity
  have hh := CylinderLiouvilleGreen.normalizer_pos hμ
  have hG : Gamma (1/2 + ((μ^2/2:ℝ):ℂ)) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    rw [add_re, ofReal_re]; norm_num; positivity)
  have hcp : (((μ^2/2:ℝ):ℂ))^(((μ^2/2:ℝ):ℂ)) = (((μ^2/2) ^ (μ^2/2) : ℝ) : ℂ) :=
    (Complex.ofReal_cpow hz.le _).symm
  have he : exp (-((μ^2/2:ℝ):ℂ)) = ((Real.exp (-(μ^2/2)) : ℝ) : ℂ) := by push_cast; rfl
  have hsq := CylinderUniformExpansion.normalizer_sq hμ
  have h1 : (((μ^2/2:ℝ):ℂ)) = (μ:ℂ)^2/2 := by push_cast; ring
  rw [hcp, he, ← h1, inv_div]
  have hs : (Real.sqrt (2*π) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  have hsq' : ((μ * Real.sqrt 2 * CylinderLiouvilleGreen.normalizer μ ^ 2 : ℝ) : ℂ) =
      ((Real.exp (-(μ^2/2)) * (μ^2/2) ^ (μ^2/2) : ℝ) : ℂ) := by rw [hsq]
  push_cast at hsq' ⊢
  rw [mul_assoc (Real.sqrt (2*π) : ℂ), ← hsq']
  have : (CylinderLiouvilleGreen.normalizer μ : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)).ne'
  field_simp

/-- **The connection relation between `+∞` and `-∞`**: comparing the whole-line expansion with
the behaviour of `U` at `-∞` gives `|L₊ H₋/H₊ - L₋| ≤ C μ^{-2N}`. -/
lemma CylinderUniformExpansion.connection_relation {N : ℕ} (hN : 1 ≤ N) : ∃ C μ₀ : ℝ, 1 ≤
    μ₀ ∧ ∀ μ, μ₀ ≤ μ →
    ‖(CylinderUniformExpansion.truncSeries (fun s _ => CylinderUniformExpansion.barLimitCoeff s)
        N (μ^2) 0 : ℂ) *
      (((Real.sqrt (2*π) * CylinderLiouvilleGreen.normalizer μ : ℝ) : ℂ) / Gamma (1/2 + (μ:ℂ)^2/2) /
        (((μ * Real.sqrt 2 * CylinderLiouvilleGreen.normalizer μ)⁻¹ : ℝ) : ℂ)) -
      (CylinderUniformExpansion.truncSeries
          (fun s _ => (-1)^s * CylinderUniformExpansion.barLimitCoeff s) N (μ^2) 0 : ℂ)‖ ≤
          C / (μ^2)^N := by
  obtain ⟨C, μ₀, hC, hμ₀, hcore⟩ := CylinderUniformExpansion.pos_core hN
  refine ⟨C, μ₀, hμ₀, fun μ hμ => ?_⟩
  have hμ0 : 0 < μ := by linarith
  obtain ⟨hL, hct⟩ := hcore μ hμ
  set L := CylinderUniformExpansion.truncSeries
      (fun s _ => CylinderUniformExpansion.barLimitCoeff s) N (μ^2) 0 with hLdef
  set Hp : ℂ := (((μ * Real.sqrt 2 * CylinderLiouvilleGreen.normalizer μ)⁻¹ : ℝ) : ℂ) with hHpdef
  have hL0 : (L:ℂ) ≠ 0 := by exact_mod_cast (by linarith [(abs_le.1 hL).1] : (0:ℝ) < L).ne'
  have hHp : Hp ≠ 0 := by
    have := CylinderLiouvilleGreen.normalizer_pos hμ0
    simp only [Hp]; exact_mod_cast
        (by positivity : (0:ℝ) < (μ * Real.sqrt 2 * CylinderLiouvilleGreen.normalizer μ)⁻¹).ne'
  set F : ℝ → ℂ := fun t => parabolicCylinderU (μ^2/2) (μ*t*Real.sqrt 2) /
    ((CylinderUniformExpansion.posAmplitude t * Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ) * L / Hp -
      (CylinderUniformExpansion.truncSeries CylinderUniformExpansion.posCoeff N (μ^2)
          t : ℂ) with hFdef
  have hF : ∀ t, ‖F t‖ ≤ C/(μ^2)^N := by
    intro t
    obtain ⟨-, e, e', he, -, hU, -⟩ := hct t
    have hA : ((CylinderUniformExpansion.posAmplitude t *
        Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos (CylinderUniformExpansion.posAmplitude_pos t) (Real.exp_pos _)).ne'
    have : F t = (e : ℂ) := by
      simp only [F]; rw [hU]
      rw [show (((CylinderUniformExpansion.posAmplitude t * Real.exp (-(μ^2 * pcfXiBar t)) *
        (CylinderUniformExpansion.truncSeries CylinderUniformExpansion.posCoeff N (μ^2) t +
            e) : ℝ)) : ℂ) =
        ((CylinderUniformExpansion.posAmplitude t * Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ) *
        ((CylinderUniformExpansion.truncSeries CylinderUniformExpansion.posCoeff N (μ^2) t : ℂ) +
            e) by push_cast; ring]
      field_simp
      ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]; exact he
  have hser : Tendsto (fun t =>
      (CylinderUniformExpansion.truncSeries CylinderUniformExpansion.posCoeff N (μ^2) t : ℂ)) atBot
      (𝓝 (CylinderUniformExpansion.truncSeries
          (fun s _ => (-1)^s * CylinderUniformExpansion.barLimitCoeff s) N (μ^2) 0 : ℂ)) := by
    refine (Complex.continuous_ofReal.tendsto _).comp ?_
    exact tendsto_finsetSum _ fun s _ =>
        (CylinderUniformExpansion.tendsto_posCoeff_atBot s).div_const _
  have hFl := ((((CylinderUniformExpansion.tendsto_posU_div_atBot hμ0).mul_const
      (L:ℂ)).div_const Hp).sub hser)
  have := le_of_tendsto hFl.norm (Eventually.of_forall hF)
  convert this using 2
  ring

/-- The function `R̃(u/2) = Γ(1/2+u/2)/(√(2π)e^{-u/2}(u/2)^{u/2})`. -/
noncomputable def CylinderUniformExpansion.gammaRatio (u : ℝ) : ℂ :=
  Gamma (1/2+((u/2:ℝ):ℂ))/((Real.sqrt (2*π):ℂ)*exp (-((u/2:ℝ):ℂ))*(((u/2:ℝ):ℂ))^(((u/2:ℝ):ℂ)))

/-- `u^{-(N+1)} = O(u^{-N})`. -/
lemma CylinderUniformExpansion.isBigO_zpow_succ (N : ℕ) :
    (fun u : ℝ => (u:ℂ)^(-((N+1:ℕ):ℤ))) =O[atTop] (fun u : ℝ => (u:ℂ)^(-(N:ℤ))) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with u hu
  rw [one_mul, norm_zpow, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  exact zpow_le_zpow_right₀ hu (by push_cast; omega)

/-- **The normalizer identity, formal form**: with `c_s` the coefficient of `t^{3s}` in `u_s`
and `γ_s` the coefficients of DLMF 12.10.16,
`(∑ γ_j (u/2)^{-j}) (∑ c_s u^{-s}) = ∑ (-1)^s c_s u^{-s}` as formal series. -/
lemma CylinderUniformExpansion.gamma_identity :
    CylinderUniformExpansion.cauchyProduct (fun j => pcfGammaCoeff j * 2^j)
        (fun s => (CylinderLiouvilleGreen.limitCoeff s : ℂ)) =
      CylinderUniformExpansion.signTwist (fun s => (CylinderLiouvilleGreen.limitCoeff s : ℂ)) := by
  obtain ⟨Φ, hΦ⟩ := CylinderUniformExpansion.exists_hasInversePowerExpansion
      CylinderLiouvilleGreen.limitCoeff
  obtain ⟨Ψ, hΨ⟩ := CylinderUniformExpansion.exists_hasInversePowerExpansion
      CylinderUniformExpansion.barLimitCoeff
  have hR : HasInversePowerExpansion CylinderUniformExpansion.gammaRatio
      (fun j => pcfGammaCoeff j * 2^j) :=
      CylinderUniformExpansion.hasInversePowerExpansion_gamma
  have hcb : (fun s => (CylinderUniformExpansion.barLimitCoeff s : ℂ)) =
      CylinderUniformExpansion.signTwist (fun s => (CylinderLiouvilleGreen.limitCoeff s : ℂ)) := by
    funext s; simp [CylinderUniformExpansion.barLimitCoeff, CylinderUniformExpansion.Q_coeff,
        CylinderUniformExpansion.signTwist]
  have hdiff : HasInversePowerExpansion
      (fun u => (Ψ u : ℂ) - CylinderUniformExpansion.gammaRatio u * Φ u) 0 := by
    refine HasInversePowerExpansion.of_isBigO fun N => ?_
    obtain ⟨C, μ₀, hμ₀, hF⟩ := CylinderUniformExpansion.connection_relation (N := N+1) (by omega)
    obtain ⟨B, hB⟩ := hR.isBigO_one.bound
    have h3 : (fun u : ℝ =>
        (∑ s ∈ Finset.range (N+1), (CylinderUniformExpansion.barLimitCoeff s : ℂ) / (u:ℂ)^s) -
        CylinderUniformExpansion.gammaRatio u * ∑ s ∈ Finset.range (N+1),
            (CylinderLiouvilleGreen.limitCoeff s : ℂ) / (u:ℂ)^s) =O[atTop]
        (fun u : ℝ => (u:ℂ)^(-((N+1:ℕ):ℤ))) := by
      refine IsBigO.of_bound (B*C) ?_
      filter_upwards [hB, eventually_ge_atTop (μ₀^2)] with u hBu hu
      have hu1 : 1 ≤ u := le_trans (by nlinarith) hu
      have hu0 : 0 < u := by linarith
      set μ := Real.sqrt u
      have hμu : μ^2 = u := Real.sq_sqrt hu0.le
      have hμ : μ₀ ≤ μ := by
        rw [← Real.sqrt_sq (by linarith : (0:ℝ) ≤ μ₀)]; exact Real.sqrt_le_sqrt hu
      have hμ0 : 0 < μ := Real.sqrt_pos.2 hu0
      have h := hF μ hμ
      rw [CylinderUniformExpansion.ratio_eq hμ0, hμu] at h
      have hRf : CylinderUniformExpansion.gammaRatio u ≠ 0 := by
        unfold CylinderUniformExpansion.gammaRatio
        refine div_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by
          rw [add_re, ofReal_re]; norm_num; positivity)) ?_
        refine mul_ne_zero (mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne')
          (Complex.exp_ne_zero _)) ?_
        rw [Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by
          exact_mod_cast (by positivity : (0:ℝ) < u/2).ne')]
        exact_mod_cast (by positivity : (0:ℝ) < u/2).ne'
      have e1 : ((CylinderUniformExpansion.truncSeries
          (fun s _ => CylinderUniformExpansion.barLimitCoeff s) (N+1) u 0 : ℝ) : ℂ) =
          ∑ s ∈ Finset.range (N+1), (CylinderUniformExpansion.barLimitCoeff s : ℂ) / (u:ℂ)^s := by
        rw [CylinderUniformExpansion.truncSeries]; push_cast; rfl
      have e2 : ((CylinderUniformExpansion.truncSeries
          (fun s _ => (-1)^s * CylinderUniformExpansion.barLimitCoeff s) (N+1) u 0 : ℝ) : ℂ) =
          ∑ s ∈ Finset.range (N+1), (CylinderLiouvilleGreen.limitCoeff s : ℂ) / (u:ℂ)^s := by
        rw [CylinderUniformExpansion.truncSeries]; push_cast
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [CylinderUniformExpansion.barLimitCoeff, CylinderUniformExpansion.Q_coeff]; push_cast
        rw [← mul_assoc, ← mul_pow]; norm_num
      have e3 : CylinderUniformExpansion.gammaRatio u =
          Gamma (1/2+((u/2:ℝ):ℂ))/((Real.sqrt (2*π):ℂ)*exp (-((u/2:ℝ):ℂ))*
          (((u/2:ℝ):ℂ))^(((u/2:ℝ):ℂ))) := rfl
      rw [e1, e2, ← e3] at h
      have heq : (∑ s ∈ Finset.range (N+1),
          (CylinderUniformExpansion.barLimitCoeff s : ℂ) / (u:ℂ)^s) -
          CylinderUniformExpansion.gammaRatio u * ∑ s ∈ Finset.range (N+1),
              (CylinderLiouvilleGreen.limitCoeff s : ℂ) / (u:ℂ)^s =
          CylinderUniformExpansion.gammaRatio u *
              ((∑ s ∈ Finset.range (N+1),
              (CylinderUniformExpansion.barLimitCoeff s : ℂ) / (u:ℂ)^s) *
            (CylinderUniformExpansion.gammaRatio u)⁻¹ - ∑ s ∈ Finset.range (N+1),
                (CylinderLiouvilleGreen.limitCoeff s : ℂ) / (u:ℂ)^s) := by
        field_simp
      rw [heq, norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0,
        zpow_neg, zpow_natCast]
      have hBu' : ‖CylinderUniformExpansion.gammaRatio u‖ ≤ B := by simpa using hBu
      have hB0 : 0 ≤ B := (norm_nonneg _).trans hBu'
      calc ‖CylinderUniformExpansion.gammaRatio u‖ * ‖_‖ ≤ B * (C / u^(N+1)) :=
             mul_le_mul hBu' h (norm_nonneg _) hB0
        _ = B * C * (u^(N+1))⁻¹ := by ring
    have h1 := hΨ (N+1)
    have h2 := hR.isBigO_one.mul (hΦ (N+1))
    simp only [one_mul] at h2
    refine (((h1.sub h2).add h3).trans (CylinderUniformExpansion.isBigO_zpow_succ N)).congr'
      (Eventually.of_forall fun u => ?_) EventuallyEq.rfl
    simp only; ring
  have h := (hΨ.sub (hR.mul hΦ)).unique hdiff
  funext n
  have := congrFun h n
  simp only [Pi.zero_apply, sub_eq_zero] at this
  rw [← this]
  exact congrFun hcb n

/-- The even coefficients `c_s`, `s ≥ 2`, vanish (degree bound DLMF 12.10.11), so
`c + tw c = 2δ`. -/
lemma CylinderUniformExpansion.limitCoeff_add_signTwist :
    (fun n => (CylinderLiouvilleGreen.limitCoeff n : ℂ) +
    CylinderUniformExpansion.signTwist (fun s => (CylinderLiouvilleGreen.limitCoeff s : ℂ)) n) =
    fun n => 2 * CylinderUniformExpansion.unitSeq n := by
  funext n
  rcases n with _ | m
  · simp [CylinderUniformExpansion.signTwist, CylinderUniformExpansion.unitSeq,
        CylinderLiouvilleGreen.limitCoeff_zero]; norm_num
  · simp only [CylinderUniformExpansion.signTwist, CylinderUniformExpansion.unitSeq,
        Nat.succ_ne_zero, ite_false, mul_zero]
    rcases Nat.even_or_odd (m+1) with he | ho
    · have hd := (pcfOlverU_spec m).2
      simp only [he, ↓reduceIte] at hd
      have : CylinderLiouvilleGreen.limitCoeff (m+1) = 0 := by
        rw [CylinderLiouvilleGreen.limitCoeff]; exact coeff_eq_zero_of_natDegree_lt (by omega)
      simp [this]
    · rw [ho.neg_one_pow]; ring

/-- `c · (δ + γ̃)/2 = δ`. -/
lemma CylinderUniformExpansion.limitCoeff_mul_halfGammaSum : CylinderUniformExpansion.cauchyProduct
    (fun s => (CylinderLiouvilleGreen.limitCoeff s : ℂ))
    (fun n => 1/2 * (CylinderUniformExpansion.unitSeq n + pcfGammaCoeff n * 2^n)) =
        CylinderUniformExpansion.unitSeq := by
  rw [CylinderUniformExpansion.cauchyProduct_smul, CylinderUniformExpansion.cauchyProduct_add,
      CylinderUniformExpansion.cauchyProduct_unitSeq, CylinderUniformExpansion.cauchyProduct_comm _
    (fun j => pcfGammaCoeff j * 2^j), CylinderUniformExpansion.gamma_identity]
  funext n
  have := congrFun CylinderUniformExpansion.limitCoeff_add_signTwist n
  beta_reduce
  rw [this]; ring

/-- `tw c · (δ + tw γ̃)/2 = δ`. -/
lemma CylinderUniformExpansion.signTwistLimitCoeff_mul_halfGammaSum :
    CylinderUniformExpansion.cauchyProduct
    (CylinderUniformExpansion.signTwist (fun s => (CylinderLiouvilleGreen.limitCoeff s : ℂ)))
    (fun n => 1/2 * (CylinderUniformExpansion.unitSeq n + (-1)^n * (pcfGammaCoeff n * 2^n))) =
        CylinderUniformExpansion.unitSeq := by
  have h := congrArg CylinderUniformExpansion.signTwist CylinderUniformExpansion.gamma_identity
  rw [← CylinderUniformExpansion.cauchyProduct_signTwist,
      CylinderUniformExpansion.signTwist_signTwist] at h
  rw [CylinderUniformExpansion.cauchyProduct_smul, CylinderUniformExpansion.cauchyProduct_add,
      CylinderUniformExpansion.cauchyProduct_unitSeq]
  have h2 : CylinderUniformExpansion.cauchyProduct
      (CylinderUniformExpansion.signTwist fun s => (CylinderLiouvilleGreen.limitCoeff s : ℂ))
      (fun n => (-1)^n * (pcfGammaCoeff n * 2^n)) = fun s =>
          (CylinderLiouvilleGreen.limitCoeff s : ℂ) := by
    rw [CylinderUniformExpansion.cauchyProduct_comm]; exact h
  rw [h2]
  funext n
  have := congrFun CylinderUniformExpansion.limitCoeff_add_signTwist n
  beta_reduce
  rw [add_comm (CylinderUniformExpansion.signTwist _ n), this]; ring

/-- **Reciprocal expansions in `μ²`**: if `G(μ) T_M(a)(μ²) - 1 = O(μ^{-2M})` for all `M` and
`a · d = δ`, then `G(μ) - T_M(d)(μ²) = O(μ^{-2M})` for all `M`. -/
lemma CylinderUniformExpansion.recip_sq {G : ℝ → ℂ} {a d : ℕ → ℂ}
    (had : CylinderUniformExpansion.cauchyProduct a d = CylinderUniformExpansion.unitSeq)
    (hG : ∀ M : ℕ, (fun μ : ℝ => G μ * (∑ s ∈ Finset.range M, a s / (μ:ℂ)^(2*s)) - 1) =O[atTop]
      (fun μ : ℝ => (μ:ℂ)^(-(2*M:ℤ)))) (M : ℕ) :
    (fun μ : ℝ => G μ - ∑ s ∈ Finset.range M, d s / (μ:ℂ)^(2*s)) =O[atTop]
      (fun μ : ℝ => (μ:ℂ)^(-(2*M:ℤ))) := by
  have h2 : Tendsto (fun μ : ℝ => μ^2) atTop atTop := tendsto_pow_atTop two_ne_zero
  -- conversions from `u` to `μ²`
  have hT : ∀ (b : ℕ → ℂ) (K : ℕ) (μ : ℝ), μ ≠ 0 →
      (CylinderUniformExpansion.truncPoly K b).eval (((μ^2:ℝ):ℂ)⁻¹) = ∑ s ∈ Finset.range K, b s /
          (μ:ℂ)^(2*s) := by
    intro b K μ hμ
    rw [CylinderUniformExpansion.truncPoly_eval K b]
    refine Finset.sum_congr rfl fun s _ => ?_
    push_cast; rw [pow_mul]
  have hz : ∀ K : ℕ, ((fun u : ℝ => (u:ℂ)^(-(K:ℤ))) ∘ fun μ : ℝ => μ^2) =ᶠ[atTop]
      fun μ : ℝ => (μ:ℂ)^(-(2*K:ℤ)) := fun K => Eventually.of_forall fun μ => by
    simp only [Function.comp]; push_cast
    rw [show (2*K:ℤ) = ((2*K:ℕ):ℤ) by push_cast; ring, zpow_neg, zpow_neg, zpow_natCast,
      zpow_natCast, pow_mul]
  have hQ : ∀ n < M, (CylinderUniformExpansion.truncPoly M a *
      CylinderUniformExpansion.truncPoly M d - 1).coeff n = 0 := by
    intro n hn
    rw [coeff_sub, coeff_mul, coeff_one, sub_eq_zero]
    have h := congrFun had n
    rw [CylinderUniformExpansion.cauchyProduct, CylinderUniformExpansion.unitSeq] at h
    rw [← h]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := Finset.mem_antidiagonal.1 hx
    rw [CylinderUniformExpansion.truncPoly_coeff, CylinderUniformExpansion.truncPoly_coeff]
    simp [show x.1 < M by omega, show x.2 < M by omega]
  have h3 := ((CylinderUniformExpansion.isBigO_eval_recip hQ).comp_tendsto
      h2).trans_eventuallyEq (hz M)
  have hb : ∀ (b : ℕ → ℂ) (K : ℕ), (fun μ : ℝ => ∑ s ∈ Finset.range K, b s / (μ:ℂ)^(2*s)) =O[atTop]
      (fun _ => (1:ℂ)) := by
    intro b K
    refine ((CylinderUniformExpansion.truncPoly_isBigO_one K b).comp_tendsto h2).congr' ?_
        EventuallyEq.rfl
    filter_upwards [eventually_ne_atTop 0] with μ hμ
    simp only [Function.comp]
    refine Finset.sum_congr rfl fun s _ => ?_
    push_cast; rw [pow_mul]
  -- `G` is bounded
  have ha0 : a 0 * d 0 = 1 := by
    have := congrFun had 0
    simpa [CylinderUniformExpansion.cauchyProduct, CylinderUniformExpansion.unitSeq] using this
  have ha0' : a 0 ≠ 0 := left_ne_zero_of_mul_eq_one ha0
  have hc : (fun μ : ℝ => (μ:ℂ)^(-(2*(1:ℕ):ℤ))) =O[atTop] (fun _ => (1:ℂ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with μ hμ
    rw [one_mul, norm_one, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact zpow_le_one_of_nonpos₀ hμ (by norm_num)
  have hG1 : G =O[atTop] (fun _ => (1:ℂ)) := by
    have := ((((hG 1).trans hc).add (isBigO_refl (fun _ => (1:ℂ)) atTop)).const_mul_left (a 0)⁻¹)
    refine this.congr' (Eventually.of_forall fun μ => ?_) EventuallyEq.rfl
    simp only [Finset.sum_range_one, pow_zero, mul_zero, div_one]
    field_simp
    ring
  have h4 : (fun μ : ℝ =>
      -(G μ * (CylinderUniformExpansion.truncPoly M a *
      CylinderUniformExpansion.truncPoly M d - 1).eval
      (((μ^2:ℝ):ℂ)⁻¹)) + (∑ s ∈ Finset.range M, d s / (μ:ℂ)^(2*s)) *
      (G μ * (∑ s ∈ Finset.range M, a s / (μ:ℂ)^(2*s)) - 1)) =O[atTop]
      (fun μ : ℝ => (μ:ℂ)^(-(2*M:ℤ))) := by
    have e1 : (fun μ : ℝ => G μ *
        (CylinderUniformExpansion.truncPoly M a * CylinderUniformExpansion.truncPoly M d - 1).eval
        (((μ^2:ℝ):ℂ)⁻¹)) =O[atTop] (fun μ : ℝ => (μ:ℂ)^(-(2*M:ℤ))) := by
      simpa only [one_mul, Function.comp_def] using hG1.mul h3
    have e2 : (fun μ : ℝ => (∑ s ∈ Finset.range M, d s / (μ:ℂ)^(2*s)) *
        (G μ * (∑ s ∈ Finset.range M, a s / (μ:ℂ)^(2*s)) - 1)) =O[atTop]
        (fun μ : ℝ => (μ:ℂ)^(-(2*M:ℤ))) := by
      simpa only [one_mul] using (hb d M).mul (hG M)
    exact e1.neg_left.add e2
  refine h4.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ne_atTop 0] with μ hμ
  simp only [eval_sub, eval_mul, eval_one, hT a M μ hμ, hT d M μ hμ]
  ring

/-- **DLMF 12.10.3 with the normalizer of DLMF 12.10.14**: the normalizer `g` of Olver's
expansion of `U(-½μ², μt√2)` for `t ≥ 1+δ` satisfies
`g(μ)/h(μ) ∼ 1 + ½ ∑ γ_s (½μ²)^{-s}` (`IsCylinderGNormalizer`). The proof combines
`pcf_negative_parameter_uniform_U` (`g/h · ∑ c_s μ^{-2s} ∼ 1`) with the formal identity
`(∑ c_s u^{-s})(1 + ∑ γ_s (u/2)^{-s}) = 2` (`CylinderUniformExpansion.limitCoeff_mul_halfGammaSum`),
obtained from the whole-line expansion for positive parameter. This is the `U`-part of
`pcf_negative_parameter_uniform`. -/
@[dlmf 12.10.E3, dlmf 12.10.E14]
theorem pcf_negative_parameter_uniform_U_normalizer :
    ∃ g : ℝ → ℂ, IsCylinderGNormalizer g ∧ ∀ δ : ℝ, 0 < δ → HasCylinderUniformExpansion
      (fun μ t => parabolicCylinderU (-μ^2/2)
          (μ*t*Real.sqrt 2)/(g μ*exp (-μ^2*pcfXi t)/(t^2-1:ℂ)^(1/4:ℂ)))
      (fun s t => pcfOlverA s t) (Ici (1+δ)) := by
  obtain ⟨g, hg, hexp⟩ := pcf_negative_parameter_uniform_U
  refine ⟨g, fun N => ?_, hexp⟩
  have h := CylinderUniformExpansion.recip_sq (G := fun μ => g μ / pcfH μ)
      (a := fun s => (CylinderLiouvilleGreen.limitCoeff s : ℂ))
    CylinderUniformExpansion.limitCoeff_mul_halfGammaSum (fun M => hg M) (N+1)
  have hγ0 : pcfGammaCoeff 0 = 1 := pcfGammaCoeff_initial.1
  refine h.congr' ?_ (Eventually.of_forall fun μ => by push_cast; ring_nf)
  filter_upwards [eventually_ne_atTop 0] with μ hμ
  have hμ' : (μ:ℂ) ≠ 0 := by exact_mod_cast hμ
  rw [Finset.sum_range_succ']
  simp only [CylinderUniformExpansion.unitSeq, hγ0, ite_true, Nat.succ_ne_zero, ite_false,
      pow_zero, mul_zero,
    zero_add, div_one, Finset.mul_sum]
  have : ∀ j : ℕ, 1/2 * (pcfGammaCoeff (j+1) * 2^(j+1)) / (μ:ℂ)^(2*(j+1)) =
      1/2 * (pcfGammaCoeff (j+1) / ((μ:ℂ)^2/2)^(j+1)) := fun j => by
    rw [div_pow, pow_mul]; field_simp
  simp only [this]
  ring

end DLMF.Confluent
end
