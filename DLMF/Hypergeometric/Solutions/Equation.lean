/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.Pochhammer
public import DLMF.Hypergeometric.Basic.GaussEquation

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import DLMF.Hypergeometric.Continuation
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Logarithmic solutions and uniqueness for the Gauss equation (DLMF §15.10)

The Gauss operator, the standard local solutions, their differential equations and their
Wronskians are in `DLMF.Hypergeometric.Basic.GaussEquation`.

## Main definitions

* `logarithmicSecond`, `logarithmicSecondTerminating`, `logarithmicSecondBothTerminating`:
  logarithmic second solutions at a positive integral denominator, DLMF 15.10.8–15.10.10.

## Main results

* `cpow_eq_exp_of_exp_eq`: a principal power computed from a logarithm in the principal strip.
* `gaussOperator_iteratedDeriv`: the differentiated Gauss equation.
* `gaussOperator_eq_zero_of_deriv_eq_zero`: uniqueness of solutions on connected open sets.
-/

@[expose] public section

open Complex Filter

open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric

/-- A principal power computed from any logarithm in the principal strip. -/
theorem cpow_eq_exp_of_exp_eq {x L : ℂ} (hx : exp L = x) (h1 : -Real.pi < L.im)
    (h2 : L.im ≤ Real.pi) (y : ℂ) : x ^ y = exp (L * y) := by
  have hx0 : x ≠ 0 := by rw [← hx]; exact exp_ne_zero L
  rw [cpow_def_of_ne_zero hx0, ← hx, log_exp h1 h2]

/-- The logarithmic second solution for a positive integral denominator (generic numerators). -/
@[dlmf 15.10.E8]
def logarithmicSecond (a b : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ₂F₁ a b (n : ℂ) z * log z -
    (∑ j ∈ Finset.range (n - 1),
      ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
        (((n - j - 2).factorial : ℂ) * poch (1 - a) (j + 1) * poch (1 - b) (j + 1)) *
            ((-z)⁻¹) ^ (j + 1)) +
    ∑' k : ℕ, gaussHGCoeff a b n k * z ^ k *
      (digamma (a + k) + digamma (b + k) - digamma (1 + k) - digamma (n + k))

/-- The logarithmic second solution with one terminating numerator. -/
@[dlmf 15.10.E9]
def logarithmicSecondTerminating (b : ℂ) (m n : ℕ) (z : ℂ) : ℂ :=
  ₂F₁ (-m : ℂ) b (n : ℂ) z * log z -
    (∑ j ∈ Finset.range (n - 1),
      ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
        (((n - j - 2).factorial : ℂ) * poch (m + 1) (j + 1) * poch (1 - b) (j + 1)) *
            ((-z)⁻¹) ^ (j + 1)) +
    (∑ k ∈ Finset.range (m + 1), gaussHGCoeff (-m) b n k * z ^ k *
      (digamma (1 + m - k) + digamma (b + k) - digamma (1 + k) - digamma (n + k))) +
    (-1 : ℂ) ^ m * (m.factorial : ℂ) * ∑' j : ℕ,
      (j.factorial : ℂ) * poch b (m + 1 + j) /
        (poch n (m + 1 + j) * ((m + 1 + j).factorial : ℂ)) * z ^ (m + 1 + j)

/-- The logarithmic second solution with two terminating numerators. -/
@[dlmf 15.10.E10]
def logarithmicSecondBothTerminating (m l n : ℕ) (z : ℂ) : ℂ :=
  ₂F₁ (-m : ℂ) (-l) (n : ℂ) z * log z -
    (∑ j ∈ Finset.range (n - 1),
      ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
        (((n - j - 2).factorial : ℂ) * poch (m + 1) (j + 1) * poch (l + 1) (j + 1)) *
            ((-z)⁻¹) ^ (j + 1)) +
    (∑ k ∈ Finset.range (l + 1), gaussHGCoeff (-m) (-l) n k * z ^ k *
      (digamma (1 + m - k) + digamma (1 + l - k) - digamma (1 + k) - digamma (n + k))) +
    (-1 : ℂ) ^ l * (l.factorial : ℂ) * ∑ j ∈ Finset.range (m - l),
      (j.factorial : ℂ) * poch (-m) (l + 1 + j) /
        (poch n (l + 1 + j) * ((l + 1 + j).factorial : ℂ)) * z ^ (l + 1 + j)

/-! ### Uniqueness for the Gauss equation on an open set -/

/-- Differentiating the Gauss equation `n` times on an open set. -/
theorem gaussOperator_iteratedDeriv {a b c : ℂ} {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (hode : ∀ w ∈ U, gaussOperator a b c f w = 0) (n : ℕ) :
    ∀ w ∈ U, w * (1 - w) * iteratedDeriv (n + 2) f w +
      ((n : ℂ) * (1 - 2 * w) + (c - (a + b + 1) * w)) * iteratedDeriv (n + 1) f w +
      (-((n : ℂ) * (n - 1)) - n * (a + b + 1) - a * b) * iteratedDeriv n f w = 0 := by
  have ha (k : ℕ) : AnalyticOnNhd ℂ (iteratedDeriv k f) U := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hf
    | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hd (k : ℕ) (w : ℂ) (hw : w ∈ U) :
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f w) w := by
    simpa only [iteratedDeriv_succ] using (ha k w hw).differentiableAt.hasDerivAt
  induction n with
  | zero =>
    intro w hw
    have h := hode w hw
    simp only [gaussOperator] at h
    simp only [Nat.cast_zero, zero_mul, zero_add, zero_sub, neg_zero, iteratedDeriv_one,
      iteratedDeriv_zero]
    linear_combination h
  | succ n ih =>
    intro w hw
    set E : ℂ → ℂ := fun w' => w' * (1 - w') * iteratedDeriv (n + 2) f w' +
      ((n : ℂ) * (1 - 2 * w') + (c - (a + b + 1) * w')) * iteratedDeriv (n + 1) f w' +
      (-((n : ℂ) * (n - 1)) - n * (a + b + 1) - a * b) * iteratedDeriv n f w' with hE
    have h1 := ((hasDerivAt_id w).mul ((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w))).mul
      (hd (n + 2) w hw)
    have h2 := (((hasDerivAt_const w (n : ℂ)).mul ((hasDerivAt_const w (1 : ℂ)).sub
      ((hasDerivAt_id w).const_mul 2))).add ((hasDerivAt_const w c).sub
      ((hasDerivAt_id w).const_mul (a + b + 1)))).mul (hd (n + 1) w hw)
    have h3 := (hd n w hw).const_mul (-((n : ℂ) * (n - 1)) - n * (a + b + 1) - a * b)
    have ht : HasDerivAt E _ w := (h1.add h2).add h3
    have he : E =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [hU.mem_nhds hw] with w' hw'
      exact ih w' hw'
    have hD := ht.deriv
    rw [he.deriv_eq, deriv_const] at hD
    simp only [id, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, mul_one, zero_sub, zero_add,
      one_mul, zero_mul] at hD
    simp only [show n + 2 + 1 = n + 3 by ring, show n + 1 + 1 = n + 2 by ring] at hD ⊢
    push_cast
    linear_combination -hD

/-- A solution of the Gauss equation on a connected open set vanishing to second order at a
regular point vanishes identically. -/
theorem gaussOperator_eq_zero_of_deriv_eq_zero {a b c : ℂ} {g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hg : AnalyticOnNhd ℂ g U)
    (hode : ∀ w ∈ U, gaussOperator a b c g w = 0) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (h0 : z₀ ≠ 0)
    (h1 : z₀ ≠ 1) (hv : g z₀ = 0) (hdv : deriv g z₀ = 0) : ∀ w ∈ U, g w = 0 := by
  have hP : z₀ * (1 - z₀) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr (Ne.symm h1))
  have hall (n : ℕ) : iteratedDeriv n g z₀ = 0 ∧ iteratedDeriv (n + 1) g z₀ = 0 := by
    induction n with
    | zero => exact ⟨by simpa using hv, by simpa using hdv⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h := gaussOperator_iteratedDeriv hU hg hode n z₀ hz₀
      rw [ih.1, ih.2] at h
      have h' : z₀ * (1 - z₀) * iteratedDeriv (n + 2) g z₀ = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_left hP
  have hp := (hg z₀ hz₀).hasFPowerSeriesAt
  simp_rw [fun n => (hall n).1, zero_div] at hp
  have hev : g =ᶠ[𝓝 z₀] fun _ => (0 : ℂ) := by
    filter_upwards [hp.eventually_hasSum_sub] with w hw
    have h0' : HasSum (fun n => FormalMultilinearSeries.ofScalars ℂ (fun _ : ℕ => (0 : ℂ)) n
        (fun _ => w - z₀)) 0 := by
      simp
    exact hw.unique h0'
  intro w hw
  exact hg.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUc hz₀ hev hw

end DLMF.Hypergeometric
end
end
