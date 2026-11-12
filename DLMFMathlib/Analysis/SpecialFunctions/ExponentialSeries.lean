/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Bounds for weighted exponential series

The exponential-series tail with coefficients `1/(n!(n+1))` has two useful majorants:
`r^N exp r` near zero and `exp r/r` for positive arguments. These estimates allow a
Gaussian factor to cancel before checking integrability of a parameterized series.
Polynomially weighted exponential series are summable by comparison with a larger argument.
-/

@[expose] public noncomputable section
open Filter Set
open scoped Topology Nat
namespace Real
/-- The exponential series with an extra reciprocal successor remains summable after any shift. -/
theorem summable_pow_div_factorial_mul_succ (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    Summable (fun n : ℕ => r^(n+N)/((n+N).factorial:ℝ)/(n+N+1)) := by
  have hs := (NormedSpace.expSeries_div_hasSum_exp r).summable.comp_injective
    (show Function.Injective (fun n : ℕ => n+N) from by intro n m h; change n+N=m+N at h; omega)
  exact hs.of_nonneg_of_le (fun n => by positivity) fun n => by
    exact div_le_self (by positivity) (by
      have hn := Nat.cast_nonneg (α := ℝ) n
      have hN := Nat.cast_nonneg (α := ℝ) N
      linarith)

/-- An exponential majorant for the tail with an extra reciprocal successor. -/
theorem tsum_pow_div_factorial_mul_succ_le (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (∑' n : ℕ, r^(n+N)/((n+N).factorial:ℝ)/(n+N+1)) ≤ r^N*exp r := by
  have hs := summable_pow_div_factorial_mul_succ N hr
  have hg := (NormedSpace.expSeries_div_hasSum_exp r).summable.mul_left (r^N)
  rw [Real.exp_eq_exp_ℝ, ← (NormedSpace.expSeries_div_hasSum_exp r).tsum_eq, ← tsum_mul_left]
  apply hs.tsum_le_tsum _ hg
  intro n
  calc r^(n+N)/((n+N).factorial:ℝ)/(n+N+1) ≤ r^(n+N)/((n+N).factorial:ℝ) :=
        div_le_self (by positivity) (by
          have hn := Nat.cast_nonneg (α := ℝ) n
          have hN := Nat.cast_nonneg (α := ℝ) N
          linarith)
    _ ≤ r^(n+N)/(n.factorial:ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact_mod_cast Nat.factorial_le (Nat.le_add_right n N)
    _ = _ := by rw [pow_add]; ring

/-- Multiplication by the argument bounds the weighted tail by the exponential. -/
theorem mul_tsum_pow_div_factorial_mul_succ_le (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    r*(∑' n : ℕ, r^(n+N)/((n+N).factorial:ℝ)/(n+N+1)) ≤ exp r := by
  rw [← tsum_mul_left]
  have he (n : ℕ) : r*(r^(n+N)/((n+N).factorial:ℝ)/(n+N+1)) =
      r^(n+N+1)/((n+N+1).factorial:ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    push_cast
    field_simp
  simp_rw [he]
  have hs := (NormedSpace.expSeries_div_hasSum_exp r).summable
  rw [Real.exp_eq_exp_ℝ, ← (NormedSpace.expSeries_div_hasSum_exp r).tsum_eq]
  simpa only [Function.comp_def] using! tsum_comp_le_tsum_of_inj hs
    (fun n => div_nonneg (pow_nonneg hr n) (Nat.cast_nonneg _))
    (show Function.Injective (fun n : ℕ => n+N+1) from by
      intro n m h
      change n+N+1=m+N+1 at h
      omega)

/-- Polynomially weighted exponential series are absolutely summable. -/
theorem summable_nat_pow_mul_pow_div_factorial (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * r ^ n / n.factorial) := by
  have hb := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k (by norm_num : (1 : ℝ) < 2)).isBigO
  apply summable_of_isBigO_nat (Real.summable_pow_div_factorial (2 * r))
  obtain ⟨C, hC⟩ := hb.bound
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC] with n hn
  have hn' : (n : ℝ) ^ k ≤ C * 2 ^ n := by simpa using hn
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow]
  calc _ ≤ C * 2 ^ n * r ^ n / n.factorial :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hn' (by positivity))
          (Nat.cast_nonneg _)
    _ = _ := by ring

end Real
