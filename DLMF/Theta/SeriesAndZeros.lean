/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Basic.Analytic
public import DLMF.Elliptic.Theta
public import DLMF.QSeries.Identities
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Theta functions: natural boundary and zeros (DLMF §20.2(ii), §20.2(iv))

The natural boundary `Im τ = 0`, the `z`-zeros of the four theta functions, from Jacobi's
triple product, and the nonvanishing of the theta constants. The nome forms, Fourier series,
quasi-periodicity, half-period translations and analyticity of DLMF §20.2(i)–(iii) are in
`DLMF.Theta.Basic.Series`, `DLMF.Theta.Basic.Periodicity` and `DLMF.Theta.Basic.Analytic`.

## Main results

* `jacobiThetaThreeTau_natural_boundary`: the natural boundary `Im τ = 0` (DLMF §20.2(ii)).
* `jacobiThetaThreeTau_eq_qPochhammerInf`: Jacobi's triple product in theta form.
* `jacobiThetaOneTau_lattice_eq_zero`: `θ₁` vanishes at the lattice points.
* `jacobiThetaTau_eq_zero_iff`: the `z`-zeros of the theta functions (DLMF §20.2(iv)).
* `jacobiThetaNullTau_ne_zero`: `θ₂(0|τ), θ₃(0|τ), θ₄(0|τ) ≠ 0` for `Im τ > 0`.
-/

@[expose] public section

open Complex
open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic DLMF.QSeries Filter Topology

/-! ### §20.2(ii) The natural boundary -/

/-- DLMF §20.2(ii): `Im τ = 0` is a natural boundary of `θ₃(z|·)`: no real point has a
neighbourhood on which an analytic function agrees with `θ₃(z|τ)` for `Im τ > 0`. -/
@[dlmf 20.2.ii]
theorem jacobiThetaThreeTau_natural_boundary (z : ℂ) (x : ℝ) :
    ¬ ∃ U : Set ℂ, IsOpen U ∧ (x : ℂ) ∈ U ∧ ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧
      ∀ τ ∈ U, 0 < τ.im → f τ = jacobiThetaThreeTau z τ := by
  sorry

/-! ### Helpers: the triple product in theta form -/

/-- Jacobi's triple product for `θ₃`: with `E = e^{iπτ}`, `Q = E²`, `w = e^{2iz}`,
`θ₃(z|τ) = (Q;Q)_∞ (-Ew;Q)_∞ (-E/w;Q)_∞`. -/
theorem jacobiThetaThreeTau_eq_qPochhammerInf (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiThetaThreeTau z τ =
      qPochhammerInf (cexp (π * I * τ) ^ 2) (cexp (π * I * τ) ^ 2) *
        qPochhammerInf (-(cexp (π * I * τ) * cexp (2 * I * z))) (cexp (π * I * τ) ^ 2) *
        qPochhammerInf (-(cexp (π * I * τ) * (cexp (2 * I * z))⁻¹)) (cexp (π * I * τ) ^ 2) := by
  set E := cexp (π * I * τ) with hE
  set w := cexp (2 * I * z) with hw
  have hEne : E ≠ 0 := exp_ne_zero _
  have hwne : w ≠ 0 := exp_ne_zero _
  have hQn : ‖E ^ 2‖ < 1 := by
    rw [norm_pow]
    have h := norm_nome_lt_one hτ
    nlinarith [norm_nonneg E]
  have hZ : -(E * w) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hEne hwne)
  have hdiv : E ^ 2 / -(E * w) = -(E * w⁻¹) := by field_simp
  have h := DLMF.QSeries.jacobi_triple_product hQn hZ
  rw [hdiv] at h
  rw [h, jacobiThetaThreeTau_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [TripleProduct.cpow_tri, neg_eq_neg_one_mul (E * w), mul_zpow, mul_zpow,
    show (-1 : ℂ) ^ n * (E ^ 2) ^ TripleProduct.tri n * ((-1) ^ n * (E ^ n * w ^ n)) =
      ((-1) * (-1) : ℂ) ^ n * ((E ^ 2) ^ TripleProduct.tri n * E ^ n * w ^ n) by
        rw [mul_zpow]; ring,
    show ((-1 : ℂ) * -1) = 1 by norm_num, one_zpow, one_mul]
  have ht : ((TripleProduct.tri n : ℤ) : ℂ) * 2 = n * (n - 1) := by
    exact_mod_cast TripleProduct.tri_mul_two n
  have hsq : cexp (π * I * τ) ^ 2 = cexp (2 * (π * I * τ)) := by
    rw [← exp_nat_mul]; norm_num
  rw [hE, hw, hsq, exp_zpow_eq_exp_intCast_mul, exp_zpow_eq_exp_intCast_mul,
      exp_zpow_eq_exp_intCast_mul, ← exp_add, ← exp_add]
  congr 1
  linear_combination (-(π * I * τ)) * ht

/-- A `q`-Pochhammer product with a vanishing factor vanishes. -/
private lemma qPochhammerInf_eq_zero_of_factor {a q : ℂ} (hq : ‖q‖ < 1) {k : ℕ}
    (hk : 1 - a * q ^ k = 0) :
    qPochhammerInf a q = 0 := by
  have ht := tendsto_qPochhammer (w := a) hq
  have hev : ∀ᶠ n in atTop, qPochhammer a q n = 0 := by
    filter_upwards [eventually_gt_atTop k] with n hn
    rw [qPochhammer_eq_prod]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hn) hk
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))

/-- The `q`-Pochhammer product vanishes exactly when one of its factors does (`|q| < 1`). -/
private lemma qPochhammerInf_eq_zero_iff {a q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInf a q = 0 ↔ ∃ k : ℕ, 1 - a * q ^ k = 0 := by
  constructor
  · intro h
    by_contra hne
    exact qPochhammerInf_ne_zero hq (fun n hn => hne ⟨n, hn⟩) h
  · rintro ⟨k, hk⟩
    exact qPochhammerInf_eq_zero_of_factor hq hk

/-- Transport of `HasProd` along a pointwise equality of factors. -/
theorem hasProd_congr_of_eq {f g : ℕ → ℂ} {a : ℂ} (h : HasProd f a) (hfg : ∀ k, f k = g k) :
    HasProd g a := by
  have : f = g := funext hfg
  exact this ▸ h

/-- `e^{2iz} + e^{-2iz} = 2 cos 2z`. -/
theorem exp_two_I_mul_add_inv (z : ℂ) : cexp (2 * I * z) + (cexp (2 * I * z))⁻¹ = 2 *
    cos (2 * z) := by
  rw [← exp_neg, cos, show 2 * z * I = 2 * I * z by ring, show -(2 * z) * I = -(2 * I * z) by ring]
  ring

/-! ### §20.2(iv) `z`-zeros -/

/-- DLMF §20.2(iv): the lattice points `(m + nτ)π` are zeros of `θ₁(z|τ)` (for every `τ`). -/
theorem jacobiThetaOneTau_lattice_eq_zero (τ : ℂ) (m n : ℤ) :
    jacobiThetaOneTau ((m + n * τ) * π) τ = 0 := by
  have h0 : jacobiThetaOneTau 0 τ = 0 := by
    have := jacobiThetaOneTau_neg 0 τ
    rw [neg_zero] at this
    exact CharZero.eq_neg_self_iff.mp this
  have := jacobiThetaOneTau_add_lattice 0 τ m n
  rw [zero_add, h0, mul_zero] at this
  exact this

/-- `1 + e^x = 0` iff `x = iπ + 2πim` for some integer `m`. -/
private lemma one_add_exp_eq_zero_iff (x : ℂ) :
    1 + cexp x = 0 ↔ ∃ m : ℤ, x = π * I + m * (2 * π * I) := by
  rw [add_eq_zero_iff_eq_neg', ← exp_pi_mul_I, exp_eq_exp_iff_exists_int]

/-- `2i ≠ 0`. -/
private lemma two_I_ne_zero : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero

/-- The zeros of `θ₃(z|τ)` (DLMF §20.2(iv)), from the triple product. -/
private lemma jacobiThetaThreeTau_eq_zero_iff {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiThetaThreeTau z τ = 0 ↔ ∃ m n : ℤ, z = (m + 1 / 2 + (n + 1 / 2) * τ) * π := by
  have hQn := norm_nome_sq_lt_one hτ
  have hA : qPochhammerInf (cexp (π * I * τ) ^ 2) (cexp (π * I * τ) ^ 2) ≠ 0 :=
    qPochhammerInf_ne_zero_of_norm_lt_one hQn hQn
  have hQk : ∀ k : ℕ, (cexp (π * I * τ) ^ 2) ^ k = cexp (k * (2 * (π * I * τ))) := fun k => by
    rw [← exp_nat_mul, ← exp_nat_mul]; push_cast; ring_nf
  rw [jacobiThetaThreeTau_eq_qPochhammerInf z hτ]
  simp only [mul_eq_zero, hA, false_or]
  rw [qPochhammerInf_eq_zero_iff hQn, qPochhammerInf_eq_zero_iff hQn]
  constructor
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · rw [hQk, sub_eq_add_neg, neg_mul, neg_neg, ← exp_add, ← exp_add,
        one_add_exp_eq_zero_iff] at hk
      obtain ⟨m, hm⟩ := hk
      refine ⟨m, -((k : ℤ) + 1), ?_⟩
      apply mul_left_cancel₀ two_I_ne_zero
      push_cast
      linear_combination hm
    · rw [hQk, sub_eq_add_neg, neg_mul, neg_neg, ← exp_neg, ← exp_add, ← exp_add,
        one_add_exp_eq_zero_iff] at hk
      obtain ⟨m, hm⟩ := hk
      refine ⟨-m - 1, k, ?_⟩
      apply mul_left_cancel₀ two_I_ne_zero
      push_cast
      linear_combination -hm
  · rintro ⟨m, n, rfl⟩
    rcases le_or_gt 0 n with hn | hn
    · right
      lift n to ℕ using hn
      refine ⟨n, ?_⟩
      rw [hQk, sub_eq_add_neg, neg_mul, neg_neg, ← exp_neg, ← exp_add, ← exp_add,
        one_add_exp_eq_zero_iff]
      refine ⟨-m - 1, ?_⟩
      push_cast
      ring
    · left
      obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -((k : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
      subst hk
      refine ⟨k, ?_⟩
      rw [hQk, sub_eq_add_neg, neg_mul, neg_neg, ← exp_add, ← exp_add,
        one_add_exp_eq_zero_iff]
      refine ⟨m, ?_⟩
      push_cast
      ring

/-- DLMF §20.2(iv): for `Im τ > 0` the `z`-zeros of `θ₁, θ₂, θ₃, θ₄` are exactly
`(m + nτ)π`, `(m + 1/2 + nτ)π`, `(m + 1/2 + (n + 1/2)τ)π`, `(m + (n + 1/2)τ)π`. -/
@[dlmf 20.2.iv]
theorem jacobiThetaTau_eq_zero_iff {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    (jacobiThetaOneTau z τ = 0 ↔ ∃ m n : ℤ, z = (m + n * τ) * π) ∧
    (jacobiThetaTwoTau z τ = 0 ↔ ∃ m n : ℤ, z = (m + 1 / 2 + n * τ) * π) ∧
    (jacobiThetaThreeTau z τ = 0 ↔ ∃ m n : ℤ, z = (m + 1 / 2 + (n + 1 / 2) * τ) * π) ∧
    (jacobiThetaFourTau z τ = 0 ↔ ∃ m n : ℤ, z = (m + (n + 1 / 2) * τ) * π) := by
  have h3 : ∀ z : ℂ, jacobiThetaThreeTau z τ = 0 ↔
      ∃ m n : ℤ, z = (m + 1 / 2 + (n + 1 / 2) * τ) * π := fun z =>
          jacobiThetaThreeTau_eq_zero_iff hτ z
  refine ⟨?_, ?_, h3 z, ?_⟩
  · rw [jacobiThetaOneTau, neg_eq_zero, jacobiThetaTwoTau, mul_eq_zero, h3]
    simp only [exp_ne_zero, false_or]
    refine exists₂_congr fun m n => ?_
    constructor <;> intro h <;> linear_combination h
  · rw [jacobiThetaTwoTau, mul_eq_zero, h3]
    simp only [exp_ne_zero, false_or]
    refine exists₂_congr fun m n => ?_
    constructor <;> intro h <;> linear_combination h
  · rw [jacobiThetaFourTau, h3]
    refine exists₂_congr fun m n => ?_
    constructor <;> intro h <;> linear_combination h

/-- A lattice-type point `(a + bτ)π` with real `a, b` vanishes only if `a = b = 0` (`Im τ > 0`). -/
theorem eq_zero_of_lattice_point_eq_zero {τ : ℂ} (hτ : 0 < τ.im) {a b : ℝ}
    (h : 0 = ((a : ℂ) + b * τ) * π) :
    a = 0 ∧ b = 0 := by
  have h' : (a : ℂ) + b * τ = 0 := by
    rcases mul_eq_zero.mp h.symm with h | h
    · exact h
    · exact absurd h pi_ne_zero'
  have him := congrArg Complex.im h'
  have hre := congrArg Complex.re h'
  simp only [add_im, ofReal_im, mul_im, ofReal_re, zero_add, zero_im, add_re, mul_re,
    zero_mul, sub_zero, zero_re] at him hre
  have hb : b = 0 := by
    rw [add_zero] at him
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h hτ.ne'
  subst hb
  simp at hre
  exact ⟨hre, rfl⟩

/-- `θ₂(0|τ), θ₃(0|τ), θ₄(0|τ) ≠ 0` for `Im τ > 0` (from the zeros of §20.2(iv)). -/
theorem jacobiThetaNullTau_ne_zero {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiThetaTwoNullTau τ ≠ 0 ∧ jacobiThetaThreeNullTau τ ≠ 0 ∧ jacobiThetaFourNullTau τ ≠ 0 := by
  have hz := jacobiThetaTau_eq_zero_iff hτ 0
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨m, n, hmn⟩ := hz.2.1.mp h
    have := eq_zero_of_lattice_point_eq_zero hτ (a := m + 1 / 2) (b := n) (by push_cast; exact hmn)
    have h2 : (2 * m + 1 : ℝ) = 0 := by linarith [this.1]
    exact absurd (by exact_mod_cast h2 : (2 * m + 1 : ℤ) = 0) (by omega)
  · obtain ⟨m, n, hmn⟩ := hz.2.2.1.mp h
    have := eq_zero_of_lattice_point_eq_zero hτ (a := m + 1 / 2) (b := n + 1 / 2)
        (by push_cast; exact hmn)
    have h2 : (2 * m + 1 : ℝ) = 0 := by linarith [this.1]
    exact absurd (by exact_mod_cast h2 : (2 * m + 1 : ℤ) = 0) (by omega)
  · obtain ⟨m, n, hmn⟩ := hz.2.2.2.mp h
    have := eq_zero_of_lattice_point_eq_zero hτ (a := m) (b := n + 1 / 2) (by push_cast; exact hmn)
    have h2 : (2 * n + 1 : ℝ) = 0 := by linarith [this.2]
    exact absurd (by exact_mod_cast h2 : (2 * n + 1 : ℤ) = 0) (by omega)

end DLMF.Theta

end
