/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Products
public import DLMF.QSeries.Pochhammer
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Theta functions: values at `z = 0` (DLMF §20.4)

Values of `θⱼ` and their `z`-derivatives at `z = 0`, in the lattice form with `q = e^{iπτ}`,
`q^{1/4} = e^{iπτ/4}` and `Im τ > 0`. Infinite products are stated with `HasProd` over
`k : ℕ` with `n = k + 1`; the `q`-Pochhammer form uses the project's `qPochhammerInf`.
The vanishing statements 20.4.1 and 20.4.7 follow from the parity of the theta functions.
-/

@[expose] public section

open Complex
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

/-- DLMF 20.4.2: `θ₁'(0,q) = 2q^{1/4} ∏_{n≥1} (1 - q^{2n})³ = 2q^{1/4} (q²;q²)_∞³`, `Im τ > 0`. -/
@[dlmf 20.4.E2]
theorem jacobiThetaOneDerivNullTau_prod {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) ^ 3) ∧
      jacobiThetaOneDerivNullTau τ = 2 * cexp (π * I * τ / 4) *
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) ^ 3) ∧
      jacobiThetaOneDerivNullTau τ = 2 * cexp (π * I * τ / 4) *
        qPochhammerInf (cexp (π * I * τ) ^ 2) (cexp (π * I * τ) ^ 2) ^ 3 := by
  sorry

/-- DLMF 20.4.3: `θ₂(0,q) = 2q^{1/4} ∏_{n≥1} (1 - q^{2n})(1 + q^{2n})²`, `Im τ > 0`. -/
@[dlmf 20.4.E3]
theorem jacobiThetaTwoNullTau_prod {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + cexp (π * I * τ) ^ (2 * (k + 1))) ^ 2) ∧
      jacobiThetaTwoNullTau τ = 2 * cexp (π * I * τ / 4) *
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + cexp (π * I * τ) ^ (2 * (k + 1))) ^ 2) := by
  obtain ⟨hm, he⟩ := jacobiThetaTwoTau_hasProd 0 hτ
  have key : ∀ k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
      (1 + 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * 0) +
        cexp (π * I * τ) ^ (4 * (k + 1))) =
      (1 - cexp (π * I * τ) ^ (2 * (k + 1))) * (1 + cexp (π * I * τ) ^ (2 * (k + 1))) ^ 2 :=
    fun k => by rw [mul_zero, cos_zero]; ring
  refine ⟨hm.congr key, ?_⟩
  rw [jacobiThetaTwoNullTau, he, cos_zero, tprod_congr key, mul_one]

/-- DLMF 20.4.4: `θ₃(0,q) = ∏_{n≥1} (1 - q^{2n})(1 + q^{2n-1})²`, `Im τ > 0`. -/
@[dlmf 20.4.E4]
theorem jacobiThetaThreeNullTau_prod {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + cexp (π * I * τ) ^ (2 * k + 1)) ^ 2) ∧
      jacobiThetaThreeNullTau τ =
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + cexp (π * I * τ) ^ (2 * k + 1)) ^ 2) := by
  obtain ⟨hm, he⟩ := jacobiThetaThreeTau_hasProd 0 hτ
  have key : ∀ k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
      (1 + 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * 0) +
        cexp (π * I * τ) ^ (4 * k + 2)) =
      (1 - cexp (π * I * τ) ^ (2 * (k + 1))) * (1 + cexp (π * I * τ) ^ (2 * k + 1)) ^ 2 :=
    fun k => by rw [mul_zero, cos_zero]; ring
  exact ⟨hm.congr key, by rw [jacobiThetaThreeNullTau, he]; exact tprod_congr key⟩

/-- DLMF 20.4.5: `θ₄(0,q) = ∏_{n≥1} (1 - q^{2n})(1 - q^{2n-1})²`, `Im τ > 0`. -/
@[dlmf 20.4.E5]
theorem jacobiThetaFourNullTau_prod {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 - cexp (π * I * τ) ^ (2 * k + 1)) ^ 2) ∧
      jacobiThetaFourNullTau τ =
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 - cexp (π * I * τ) ^ (2 * k + 1)) ^ 2) := by
  obtain ⟨hm, he⟩ := jacobiThetaFourTau_hasProd 0 hτ
  have key : ∀ k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
      (1 - 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * 0) +
        cexp (π * I * τ) ^ (4 * k + 2)) =
      (1 - cexp (π * I * τ) ^ (2 * (k + 1))) * (1 - cexp (π * I * τ) ^ (2 * k + 1)) ^ 2 :=
    fun k => by rw [mul_zero, cos_zero]; ring
  exact ⟨hm.congr key, by rw [jacobiThetaFourNullTau, he]; exact tprod_congr key⟩

/-- DLMF 20.4.6: Jacobi's derivative formula `θ₁'(0,q) = θ₂(0,q) θ₃(0,q) θ₄(0,q)`, `Im τ > 0`. -/
@[dlmf 20.4.E6]
theorem jacobiThetaOneDerivNullTau_eq_mul {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiThetaOneDerivNullTau τ =
      jacobiThetaTwoNullTau τ * jacobiThetaThreeNullTau τ * jacobiThetaFourNullTau τ := by
  sorry

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

/-- DLMF 20.4.8: `θ₁'''(0,q)/θ₁'(0,q) = -1 + 24 ∑_{n≥1} q^{2n}/(1 - q^{2n})²`, `Im τ > 0`. -/
@[dlmf 20.4.E8]
theorem jacobiThetaOne_third_deriv_ratio {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun k : ℕ => 24 * cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 - cexp (π * I * τ) ^ (2 * (k + 1))) ^ 2)
      (iteratedDeriv 3 (fun z => jacobiThetaOneTau z τ) 0 / jacobiThetaOneDerivNullTau τ + 1) := by
  sorry

/-- DLMF 20.4.9: `θ₂''(0,q)/θ₂(0,q) = -1 - 8 ∑_{n≥1} q^{2n}/(1 + q^{2n})²`, `Im τ > 0`. -/
@[dlmf 20.4.E9]
theorem jacobiThetaTwo_second_deriv_ratio {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun k : ℕ => 8 * cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 + cexp (π * I * τ) ^ (2 * (k + 1))) ^ 2)
      (-1 - iteratedDeriv 2 (fun z => jacobiThetaTwoTau z τ) 0 / jacobiThetaTwoNullTau τ) := by
  sorry

/-- DLMF 20.4.10: `θ₃''(0,q)/θ₃(0,q) = -8 ∑_{n≥1} q^{2n-1}/(1 + q^{2n-1})²`, `Im τ > 0`. -/
@[dlmf 20.4.E10]
theorem jacobiThetaThree_second_deriv_ratio {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun k : ℕ => -8 * cexp (π * I * τ) ^ (2 * k + 1) /
        (1 + cexp (π * I * τ) ^ (2 * k + 1)) ^ 2)
      (iteratedDeriv 2 (fun z => jacobiThetaThreeTau z τ) 0 / jacobiThetaThreeNullTau τ) := by
  sorry

/-- DLMF 20.4.11: `θ₄''(0,q)/θ₄(0,q) = 8 ∑_{n≥1} q^{2n-1}/(1 - q^{2n-1})²`, `Im τ > 0`. -/
@[dlmf 20.4.E11]
theorem jacobiThetaFour_second_deriv_ratio {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun k : ℕ => 8 * cexp (π * I * τ) ^ (2 * k + 1) /
        (1 - cexp (π * I * τ) ^ (2 * k + 1)) ^ 2)
      (iteratedDeriv 2 (fun z => jacobiThetaFourTau z τ) 0 / jacobiThetaFourNullTau τ) := by
  sorry

/-- DLMF 20.4.12: `θ₁'''(0)/θ₁'(0) = θ₂''(0)/θ₂(0) + θ₃''(0)/θ₃(0) + θ₄''(0)/θ₄(0)`, `Im τ > 0`. -/
@[dlmf 20.4.E12]
theorem jacobiTheta_deriv_ratio_sum {τ : ℂ} (hτ : 0 < τ.im) :
    iteratedDeriv 3 (fun z => jacobiThetaOneTau z τ) 0 / jacobiThetaOneDerivNullTau τ =
      iteratedDeriv 2 (fun z => jacobiThetaTwoTau z τ) 0 / jacobiThetaTwoNullTau τ +
      iteratedDeriv 2 (fun z => jacobiThetaThreeTau z τ) 0 / jacobiThetaThreeNullTau τ +
      iteratedDeriv 2 (fun z => jacobiThetaFourTau z τ) 0 / jacobiThetaFourNullTau τ := by
  sorry

end DLMF.Theta

end
