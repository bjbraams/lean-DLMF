/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.SpecificLimits.Basic
public import DLMFMathlib.Analysis.ODE.PowerSeriesUniqueness

/-!
# Entire solutions of linear second-order ODEs with entire coefficients

For entire coefficients `p q : ℂ → ℂ`, the equation `w'' = p w' + q w` has, for every point
`z₀` and all initial data `w₀`, `w₁`, an entire solution with `w(z₀) = w₀`, `w'(z₀) = w₁`
(`ODE.exists_entire_solution_linear_ode`). Together with `ODE.eqOn_of_ode` this solution is
unique.

The proof is by majorants: the Taylor coefficients `d n = w⁽ⁿ⁾(z₀)` are defined by the
recurrence of `ODE.eventually_ode_of_iteratedDeriv`; the Cauchy estimates
`‖p⁽ⁱ⁾(z₀)‖ ≤ A i! (s/2)ⁱ` (valid for every `s > 0`, the coefficients being entire) give
`‖d n‖ ≤ K n! sⁿ` by strong induction, so the power series `∑ d n / n! (z - z₀)ⁿ` is entire;
it solves the equation near `z₀` by `ODE.eventually_ode_of_iteratedDeriv`, hence everywhere
by the identity theorem.
-/

@[expose] public section

open Set Filter Topology Nat
open scoped NNReal ENNReal

namespace ODE

/-- The Taylor coefficients `w⁽ⁿ⁾(z₀)` of the solution of `w'' = p w' + q w` with
`w(z₀) = a`, `w'(z₀) = b`, given the derivatives `P i = p⁽ⁱ⁾(z₀)`, `Q i = q⁽ⁱ⁾(z₀)`. -/
def p1oTaylorSeq (P Q : ℕ → ℂ) (a b : ℂ) : ℕ → ℂ
  | 0 => a
  | 1 => b
  | n + 2 => ∑ i : Fin (n + 1), (n.choose i : ℂ) *
      (P i * p1oTaylorSeq P Q a b (n - i + 1) + Q i * p1oTaylorSeq P Q a b (n - i))

theorem p1oTaylorSeq_add_two (P Q : ℕ → ℂ) (a b : ℂ) (n : ℕ) :
    p1oTaylorSeq P Q a b (n + 2) = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) *
      (P i * p1oTaylorSeq P Q a b (n - i + 1) + Q i * p1oTaylorSeq P Q a b (n - i)) := by
  rw [p1oTaylorSeq]
  exact Fin.sum_univ_eq_sum_range (fun i => (n.choose i : ℂ) *
      (P i * p1oTaylorSeq P Q a b (n - i + 1) + Q i * p1oTaylorSeq P Q a b (n - i))) (n + 1)

/-- The majorant estimate: if `‖P i‖, ‖Q i‖ ≤ A i! (s/2)ⁱ`, then `‖d n‖ ≤ K n! sⁿ`. -/
theorem p1oTaylorSeq_bound {P Q : ℕ → ℂ} (a b : ℂ) {s A : ℝ} (hs : 0 < s) (hA : 0 ≤ A)
    (hP : ∀ i, ‖P i‖ ≤ A * i ! * (s / 2) ^ i) (hQ : ∀ i, ‖Q i‖ ≤ A * i ! * (s / 2) ^ i) :
    ∃ K, ∀ n, ‖p1oTaylorSeq P Q a b n‖ ≤ K * n ! * s ^ n := by
  set d := p1oTaylorSeq P Q a b
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * A * (s + 1) / s ^ 2)
  have hN' : 2 * A * (s + 1) ≤ N * s ^ 2 := by
    rwa [div_le_iff₀ (by positivity)] at hN
  set K := ∑ m ∈ Finset.range (N + 2), ‖d m‖ / (m ! * s ^ m)
  have hK : 0 ≤ K := Finset.sum_nonneg fun m _ => by positivity
  refine ⟨K, fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hn : n < N + 2
  · have hpos : (0 : ℝ) < n ! * s ^ n := by positivity
    have h1 : ‖d n‖ / (n ! * s ^ n) ≤ K :=
      Finset.single_le_sum (f := fun m => ‖d m‖ / (m ! * s ^ m))
        (fun m _ => by positivity) (Finset.mem_range.mpr hn)
    rw [div_le_iff₀ hpos] at h1
    linarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : N ≤ m := by omega
  have hterm : ∀ i ∈ Finset.range (m + 1),
      ‖(m.choose i : ℂ) * (P i * d (m - i + 1) + Q i * d (m - i))‖ ≤
        A * K * m ! * ((m + 1) * s ^ (m + 1) + s ^ m) * (1 / 2) ^ i := by
    intro i hi
    have hi : i ≤ m := by simpa [Nat.lt_succ_iff] using hi
    have e1 := ih (m - i + 1) (by omega)
    have e2 := ih (m - i) (by omega)
    have hc : (m.choose i : ℝ) * i ! * (m - i)! = m ! := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
    have hf : ((m - i + 1)! : ℝ) = (m - i + 1 : ℕ) * (m - i)! := by
      exact_mod_cast Nat.factorial_succ (m - i)
    have hmi : ((m - i + 1 : ℕ) : ℝ) ≤ m + 1 := by exact_mod_cast (by omega : m - i + 1 ≤ m + 1)
    have hp1 : (s / 2) ^ i * s ^ (m - i) = s ^ m * (1 / 2) ^ i := by
      rw [div_pow, ← mul_div_right_comm, ← pow_add, Nat.add_sub_cancel' hi, one_div, inv_pow,
        div_eq_mul_inv]
    have hp2 : (s / 2) ^ i * s ^ (m - i + 1) = s ^ (m + 1) * (1 / 2) ^ i := by
      rw [pow_succ, ← mul_assoc, hp1, pow_succ]; ring
    calc ‖(m.choose i : ℂ) * (P i * d (m - i + 1) + Q i * d (m - i))‖
        ≤ (m.choose i : ℝ) * (‖P i‖ * ‖d (m - i + 1)‖ + ‖Q i‖ * ‖d (m - i)‖) := by
          rw [norm_mul, Complex.norm_natCast]
          gcongr
          exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ (m.choose i : ℝ) * (A * i ! * (s / 2) ^ i * (K * (m - i + 1)! * s ^ (m - i + 1)) +
            A * i ! * (s / 2) ^ i * (K * (m - i)! * s ^ (m - i))) := by
          gcongr
          · exact hP i
          · exact hQ i
      _ = A * K * ((m.choose i : ℝ) * i ! * (m - i)!) *
            (((m - i + 1 : ℕ) : ℝ) * ((s / 2) ^ i * s ^ (m - i + 1)) +
              (s / 2) ^ i * s ^ (m - i)) := by
          rw [hf]; ring
      _ ≤ A * K * m ! * ((m + 1) * s ^ (m + 1) + s ^ m) * (1 / 2) ^ i := by
          rw [hc, hp1, hp2]
          calc A * K * m ! * (((m - i + 1 : ℕ) : ℝ) * (s ^ (m + 1) * (1 / 2) ^ i) +
                s ^ m * (1 / 2) ^ i)
              ≤ A * K * m ! * ((m + 1) * (s ^ (m + 1) * (1 / 2) ^ i) + s ^ m * (1 / 2) ^ i) := by
                gcongr
            _ = _ := by ring
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  rw [← Finset.mul_sum] at hsum
  have hgeo := sum_geometric_two_le (m + 1)
  have hB : 0 ≤ A * K * m ! * ((m + 1) * s ^ (m + 1) + s ^ m) := by positivity
  have h3 : ‖d (m + 2)‖ ≤ A * K * m ! * ((m + 1) * s ^ (m + 1) + s ^ m) * 2 := by
    rw [show d (m + 2) = _ from p1oTaylorSeq_add_two P Q a b m]
    exact hsum.trans (mul_le_mul_of_nonneg_left hgeo hB)
  refine h3.trans ?_
  have hfac : ((m + 2)! : ℝ) = (m + 2) * (m + 1) * m ! := by
    push_cast [Nat.factorial_succ]; ring
  rw [hfac]
  have hKm : 0 ≤ K * m ! * s ^ m := by positivity
  have hmN : (N : ℝ) ≤ m := by exact_mod_cast hm
  have key : 2 * A * ((m + 1) * s + 1) ≤ (m + 2) * (m + 1) * s ^ 2 := by
    have : 2 * A * (s + 1) ≤ (m + 2) * s ^ 2 := by nlinarith
    nlinarith
  calc A * K * m ! * ((m + 1) * s ^ (m + 1) + s ^ m) * 2
      = (2 * A * ((m + 1) * s + 1)) * (K * m ! * s ^ m) := by ring
    _ ≤ ((m + 2) * (m + 1) * s ^ 2) * (K * m ! * s ^ m) := by gcongr
    _ = K * ((m + 2) * (m + 1) * m !) * s ^ (m + 2) := by ring

/-- Cauchy estimates for an entire function: for every `s > 0` there is `A ≥ 0` with
`‖f⁽ⁱ⁾(z₀)‖ ≤ A i! (s/2)ⁱ` for all `i`. -/
theorem p1o_norm_iteratedDeriv_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z₀ : ℂ) {s : ℝ}
    (hs : 0 < s) : ∃ A, 0 ≤ A ∧ ∀ i, ‖iteratedDeriv i f z₀‖ ≤ A * i ! * (s / 2) ^ i := by
  have h1 := (hf.analyticAt z₀).hasFPowerSeriesAt
  have h2 := hf.hasFPowerSeriesOnBall z₀ one_pos
  have heq := h2.hasFPowerSeriesAt.eq_formalMultilinearSeries h1
  have hrad : (FormalMultilinearSeries.ofScalars ℂ
      (fun n => iteratedDeriv n f z₀ / n !)).radius = ⊤ := by
    rw [← heq]; exact top_le_iff.mp h2.r_le
  set r : ℝ≥0 := ⟨2 / s, by positivity⟩
  obtain ⟨C, hC, hCb⟩ := FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius _
    (r := r) (by rw [hrad]; exact ENNReal.coe_lt_top)
  refine ⟨C, hC.le, fun i => ?_⟩
  have hb := hCb i
  rw [FormalMultilinearSeries.ofScalars_norm, norm_div, Complex.norm_natCast] at hb
  have hr : ((r : ℝ)) = 2 / s := rfl
  rw [hr] at hb
  have hfac : (0 : ℝ) < i ! := by positivity
  have hpow : (0 : ℝ) < (2 / s) ^ i := by positivity
  have h22 : 2 / s * (s / 2) = 1 := by field_simp
  have : (2 / s) ^ i * (s / 2) ^ i = 1 := by rw [← mul_pow, h22, one_pow]
  calc ‖iteratedDeriv i f z₀‖
      = ‖iteratedDeriv i f z₀‖ / i ! * (2 / s) ^ i * (i ! * (s / 2) ^ i) := by
        field_simp; rw [mul_assoc, this, mul_one]
    _ ≤ C * (i ! * (s / 2) ^ i) := by gcongr
    _ = C * i ! * (s / 2) ^ i := by ring

/-- **Existence of entire solutions** of a linear second-order ODE with entire coefficients:
for entire `p`, `q` and any `z₀`, `w₀`, `w₁` there is an entire `w` with
`w'' = p w' + q w` on `ℂ`, `w(z₀) = w₀` and `w'(z₀) = w₁`. (Uniqueness: `ODE.eqOn_of_ode`.) -/
theorem exists_entire_solution_linear_ode {p q : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hq : Differentiable ℂ q) (z₀ w₀ w₁ : ℂ) :
    ∃ w : ℂ → ℂ, Differentiable ℂ w ∧
      (∀ z, deriv (deriv w) z = p z * deriv w z + q z * w z) ∧ w z₀ = w₀ ∧ deriv w z₀ = w₁ := by
  set P : ℕ → ℂ := fun i => iteratedDeriv i p z₀
  set Q : ℕ → ℂ := fun i => iteratedDeriv i q z₀
  set d := p1oTaylorSeq P Q w₀ w₁
  set c : ℕ → ℂ := fun n => d n / (n !)
  set S := FormalMultilinearSeries.ofScalars ℂ c
  have hrad : S.radius = ⊤ := by
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    have hs : (0 : ℝ) < 1 / ((r : ℝ) + 1) := by positivity
    obtain ⟨A₁, hA₁, hP⟩ := p1o_norm_iteratedDeriv_le hp z₀ hs
    obtain ⟨A₂, hA₂, hQ⟩ := p1o_norm_iteratedDeriv_le hq z₀ hs
    obtain ⟨K, hK⟩ := p1oTaylorSeq_bound (P := P) (Q := Q) w₀ w₁ hs (le_max_left 0 (max A₁ A₂))
      (fun i => (hP i).trans (by gcongr; exact (le_max_left _ _).trans (le_max_right _ _)))
      (fun i => (hQ i).trans (by gcongr; exact (le_max_right _ _).trans (le_max_right _ _)))
    refine S.le_radius_of_bound K fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm]
    have hfac : (0 : ℝ) < n ! := by positivity
    have hn : ‖c n‖ ≤ K * (1 / ((r : ℝ) + 1)) ^ n := by
      simp only [c, norm_div, Complex.norm_natCast]
      rw [div_le_iff₀ hfac]
      linarith [hK n]
    have hK0 : 0 ≤ K := by
      have := (norm_nonneg _).trans (hK 0); simpa using this
    calc ‖c n‖ * (r : ℝ) ^ n ≤ K * (1 / ((r : ℝ) + 1)) ^ n * ((r : ℝ) + 1) ^ n := by
          gcongr; linarith
      _ = K := by
          rw [mul_assoc, ← mul_pow, one_div, inv_mul_cancel₀ (by positivity), one_pow, mul_one]
  have hS := S.hasFPowerSeriesOnBall (by rw [hrad]; exact ENNReal.zero_lt_top)
  rw [hrad] at hS
  have hw := hS.comp_sub z₀
  rw [zero_add] at hw
  set w : ℂ → ℂ := fun z => S.sum (z - z₀)
  have han : ∀ z, AnalyticAt ℂ w z := fun z => hw.analyticAt_of_mem (by simp)
  have hD : ∀ n, iteratedDeriv n w z₀ = d n := by
    intro n
    have h := hw.factorial_smul 1 n
    rw [iteratedDeriv_eq_iteratedFDeriv, ← h, FormalMultilinearSeries.ofScalars_apply_eq]
    simp only [c, one_pow, smul_eq_mul, mul_one, nsmul_eq_mul]
    have : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    field_simp
  have hloc := eventually_ode_of_iteratedDeriv (han z₀) (hp.analyticAt z₀) (hq.analyticAt z₀)
    (fun n => by
      simp only [hD]
      exact p1oTaylorSeq_add_two P Q w₀ w₁ n)
  have hg : AnalyticOnNhd ℂ (fun z => deriv (deriv w) z - (p z * deriv w z + q z * w z))
      univ := fun z _ =>
    ((han z).deriv.deriv).sub (((hp.analyticAt z).mul (han z).deriv).add
      ((hq.analyticAt z).mul (han z)))
  have hzero := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ z₀) (by filter_upwards [hloc] with z hz; simp [hz])
  refine ⟨w, fun z => (han z).differentiableAt, fun z => ?_, ?_, ?_⟩
  · have := hzero (mem_univ z); simpa [sub_eq_zero] using this
  · have := hD 0; simpa [d, p1oTaylorSeq] using this
  · have := hD 1; simpa [d, p1oTaylorSeq] using this

/-- **Existence of entire solutions** (`HasDerivAt` form): for entire `p`, `q` there is an entire
`w` whose derivative is entire with `(w')' = p w' + q w` everywhere, `w(z₀) = w₀`,
`w'(z₀) = w₁`. -/
theorem exists_entire_solution_linear_ode' {p q : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hq : Differentiable ℂ q) (z₀ w₀ w₁ : ℂ) :
    ∃ w : ℂ → ℂ, Differentiable ℂ w ∧
      (∀ z, HasDerivAt (deriv w) (p z * deriv w z + q z * w z) z) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ := by
  obtain ⟨w, hw, hode, h0, h1⟩ := exists_entire_solution_linear_ode hp hq z₀ w₀ w₁
  have hd : Differentiable ℂ (deriv w) := by
    intro z
    exact ((hw.analyticAt z).deriv).differentiableAt
  exact ⟨w, hw, fun z => by rw [← hode z]; exact (hd z).hasDerivAt, h0, h1⟩

end ODE
