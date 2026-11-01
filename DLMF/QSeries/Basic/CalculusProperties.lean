/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic.Calculus
public import DLMF.QSeries.Basic.PochhammerProperties

/-!
# Basic properties of Gaussian coefficients and of the `q`-derivative

This file proves the basic properties of the Gaussian `q`-binomial coefficients and of Jackson's
`q`-derivative (DLMF §17.2(ii), §17.2(iv), Duverney §10.1).

## Main results

* `qBinom_zero_right`, `qBinom_zero_succ`, `qBinom_self`, `qBinom_eq_zero_of_lt`: special
  values.
* `qBinom_succ_succ`: the `q`-Pascal rule (DLMF 17.2.31).
* `qBinom_one`: `[n k]_1 = C(n, k)`.
* `continuous_qBinom`, `tendsto_qBinom`: continuity in `q`, and `[n k]_q → C(n, k)` as
  `q → 1` (Duverney (10.5), DLMF 17.2.28).
* `qPochhammer_succ'`: `(x;q)_{n+1} = (1 - x) (xq;q)_n`.
* `qDeriv_pow`: `δ_q xⁿ = [n]_q x^{n-1}` (Duverney (10.11)).
* `qDeriv_add`, `qDeriv_const_mul`, `qDeriv_mul`: linearity and the `q`-product rule
  (Duverney (10.14)).
* `tendsto_qDeriv`: `δ_q f(x) → f'(x)` as `q → 1` (DLMF §17.2(iv)).

## Implementation notes

Cauchy's finite `q`-binomial theorem is in `DLMF.QSeries.QBinomial`; the `q`-fundamental theorem
of calculus for the Jackson integral is in `DLMF.QSeries.QCalculus`.
-/

@[expose] public section

open Complex Finset Filter
open scoped Topology

noncomputable section

namespace DLMF.QSeries

/-- `[n 0]_q = 1`. -/
@[simp] theorem qBinom_zero_right (q : ℂ) (n : ℕ) : qBinom q n 0 = 1 := by
  cases n <;> rfl

/-- `[0, k+1]_q = 0`. -/
@[simp] theorem qBinom_zero_succ (q : ℂ) (k : ℕ) : qBinom q 0 (k + 1) = 0 := rfl

/-- The `q`-Pascal rule `[n+1, k+1]_q = [n, k]_q + q^{k+1} [n, k+1]_q` (Duverney (10.7)). -/
@[dlmf 17.2.E31 "exact: first polynomial q-Pascal rule after successor reindexing"]
theorem qBinom_succ_succ (q : ℂ) (n k : ℕ) :
    qBinom q (n + 1) (k + 1) = qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1) := rfl

/-- `[n k]_q = 0` for `k > n`. -/
theorem qBinom_eq_zero_of_lt (q : ℂ) {n k : ℕ} (h : n < k) : qBinom q n k = 0 := by
  induction n generalizing k with
  | zero => obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0); rfl
  | succ n ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [qBinom_succ_succ, ih (by omega), ih (by omega)]; ring

/-- `[n n]_q = 1` (Duverney (10.6)). -/
@[simp] theorem qBinom_self (q : ℂ) (n : ℕ) : qBinom q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [qBinom_succ_succ, ih, qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)]; ring

/-- At `q = 1` the Gaussian coefficients are the binomial coefficients. -/
theorem qBinom_one (n k : ℕ) : qBinom 1 n k = n.choose k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => rw [qBinom_succ_succ, ih, ih, Nat.choose_succ_succ]; push_cast; ring

/-- Splitting the first factor: `(x;q)_{n+1} = (1-x)(xq;q)_n`. -/
theorem qPochhammer_succ' (x q : ℂ) (n : ℕ) :
    qPochhammer x q (n + 1) = (1 - x) * qPochhammer (x * q) q n := by
  induction n with
  | zero => simp [qPochhammer_succ]
  | succ n ih =>
    rw [qPochhammer_succ, ih, qPochhammer_succ]; ring

/-- `q ↦ [n k]_q` is continuous (it is a polynomial in `q`). -/
theorem continuous_qBinom (n k : ℕ) : Continuous fun q : ℂ => qBinom q n k := by
  induction n generalizing k with
  | zero => cases k <;> simp only [qBinom_zero_right, qBinom_zero_succ] <;> fun_prop
  | succ n ih =>
    cases k with
    | zero => simp only [qBinom_zero_right]; fun_prop
    | succ k => simp only [qBinom_succ_succ]; exact (ih k).add ((continuous_pow _).mul (ih (k + 1)))

/-- `[n k]_q → C(n, k)` as `q → 1` (Duverney (10.5)). -/
@[dlmf 17.2.E28 "exact: complex q tends to1, using polynomial Gaussian binomials"]
theorem tendsto_qBinom (n k : ℕ) :
    Filter.Tendsto (fun q : ℂ => qBinom q n k) (nhds 1) (nhds (n.choose k : ℂ)) := by
  rw [← qBinom_one]
  exact (continuous_qBinom n k).tendsto 1

/-- `δ_q xⁿ = [n]_q x^{n-1}` (Duverney (10.11)). -/
theorem qDeriv_pow {q x : ℂ} (hq : q ≠ 1) (hx : x ≠ 0) (n : ℕ) :
    qDeriv q (fun t => t ^ n) x = qNum q n * x ^ (n - 1) := by
  have hq' : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  rcases n with _ | n
  · simp [qDeriv, qNum]
  simp only [qDeriv, qNum, mul_pow, Nat.add_sub_cancel, pow_succ]
  field_simp

/-- The `q`-product rule `δ_q(uv)(x) = δ_q u(x) v(x) + u(qx) δ_q v(x)` (Duverney (10.14)). -/
theorem qDeriv_mul (q : ℂ) (u v : ℂ → ℂ) (x : ℂ) :
    qDeriv q (fun t => u t * v t) x = qDeriv q u x * v x + u (q * x) * qDeriv q v x := by
  simp only [qDeriv]
  rw [div_mul_eq_mul_div, mul_div_assoc', ← add_div]
  congr 1; ring

/-- Linearity of `δ_q`. -/
theorem qDeriv_add (q : ℂ) (u v : ℂ → ℂ) (x : ℂ) :
    qDeriv q (fun t => u t + v t) x = qDeriv q u x + qDeriv q v x := by
  simp only [qDeriv]; rw [← add_div]; congr 1; ring

/-- Homogeneity of `δ_q`. -/
theorem qDeriv_const_mul (q c : ℂ) (u : ℂ → ℂ) (x : ℂ) :
    qDeriv q (fun t => c * u t) x = c * qDeriv q u x := by
  simp only [qDeriv]; rw [mul_div_assoc']; congr 1; ring

/-- `δ_q f(x) → f'(x)` as `q → 1` (Duverney (10.12)). -/
@[dlmf 17.2.iv
  "partial: q-derivative limit away from zero; extended origin convention handled by the \
    proved local adapter"]
theorem tendsto_qDeriv {f : ℂ → ℂ} {f' x : ℂ} (hf : HasDerivAt f f' x) (hx : x ≠ 0) :
    Tendsto (fun q => qDeriv q f x) (𝓝[≠] 1) (𝓝 f') := by
  have hs := hasDerivAt_iff_tendsto_slope.mp hf
  have hmap : Tendsto (fun q : ℂ => q * x) (𝓝[≠] 1) (𝓝[≠] x) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Tendsto (fun q : ℂ => q * x) (𝓝 1) (𝓝 x) := by
        have hcont : Continuous fun q : ℂ => q * x := by fun_prop
        simpa using hcont.tendsto (1 : ℂ)
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hq ⊢
      intro h
      exact hq (by simpa [hx] using congrArg (· / x) h)
  refine (hs.comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  simp only [Function.comp, slope_def_field, qDeriv]
  have hq' : (1 : ℂ) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  rw [show q * x - x = -((1 - q) * x) by ring, show f (q * x) - f x = -(f x - f (q * x)) by ring,
    neg_div_neg_eq]

end DLMF.QSeries
