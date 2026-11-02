/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.EntireLinear
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Solutions of linear second-order ODEs on a disc

For coefficients `p q : ℂ → ℂ` holomorphic on the open disc `ball z₀ R`, the equation
`w'' = p w' + q w` has, for all initial data `w₀`, `w₁`, a solution holomorphic on the whole disc
with `w(z₀) = w₀`, `w'(z₀) = w₁`. This is the disc analogue of
`ODE.exists_entire_solution_linear_ode`.

## Main results

* `ODE.exists_ball_solution_linear_ode`: existence of a solution on `ball z₀ R` with data at the
  centre.

## Implementation notes

The proof is the majorant argument of `DLMFMathlib.Analysis.ODE.EntireLinear`, with the ratio
`1/2` of the Cauchy estimates replaced by an arbitrary ratio `ρ < 1`, so that the radius of
convergence of the Taylor series of the solution is not halved: Cauchy estimates
`‖p⁽ⁱ⁾(z₀)‖ ≤ A i! t⁻ⁱ` for every `t < R` give `‖w⁽ⁿ⁾(z₀)‖ ≤ K n! sⁿ` for every `s > 1/t`, so the
radius is at least `R`.
-/

@[expose] public section

open Set Filter Topology Nat Metric
open scoped NNReal ENNReal

namespace ODE

/-- The recurrence of `linearOdeTaylorCoeff` as a sum over `Finset.range`. -/
private lemma linearOdeTaylorCoeff_add_two (P Q : ℕ → ℂ) (a b : ℂ) (n : ℕ) :
    linearOdeTaylorCoeff P Q a b (n + 2) = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) *
      (P i * linearOdeTaylorCoeff P Q a b (n - i + 1) +
        Q i * linearOdeTaylorCoeff P Q a b (n - i)) := by
  rw [linearOdeTaylorCoeff]
  exact Fin.sum_univ_eq_sum_range (fun i => (n.choose i : ℂ) *
      (P i * linearOdeTaylorCoeff P Q a b (n - i + 1) +
        Q i * linearOdeTaylorCoeff P Q a b (n - i))) (n + 1)

/-- The majorant estimate with ratio `ρ < 1`: if `‖P i‖, ‖Q i‖ ≤ A i! (ρ s)ⁱ`, then
`‖d n‖ ≤ K n! sⁿ` for the Taylor coefficients `d = linearOdeTaylorCoeff P Q a b`. -/
private lemma exists_norm_linearOdeTaylorCoeff_le_of_ratio {P Q : ℕ → ℂ} (a b : ℂ)
    {s ρ A : ℝ} (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hA : 0 ≤ A)
    (hP : ∀ i, ‖P i‖ ≤ A * i ! * (ρ * s) ^ i) (hQ : ∀ i, ‖Q i‖ ≤ A * i ! * (ρ * s) ^ i) :
    ∃ K, ∀ n, ‖linearOdeTaylorCoeff P Q a b n‖ ≤ K * n ! * s ^ n := by
  set d := linearOdeTaylorCoeff P Q a b
  have h1ρ : 0 < 1 - ρ := by linarith
  have hB : 0 ≤ A * (1 - ρ)⁻¹ := by positivity
  obtain ⟨N, hN⟩ := exists_nat_ge (A * (1 - ρ)⁻¹ * (s + 1) / s ^ 2)
  have hN' : A * (1 - ρ)⁻¹ * (s + 1) ≤ N * s ^ 2 := by
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
        A * K * m ! * ((m + 1) * s ^ (m + 1) + s ^ m) * ρ ^ i := by
    intro i hi
    have hi : i ≤ m := by simpa [Nat.lt_succ_iff] using hi
    have e1 := ih (m - i + 1) (by omega)
    have e2 := ih (m - i) (by omega)
    have hc : (m.choose i : ℝ) * i ! * (m - i)! = m ! := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
    have hf : ((m - i + 1)! : ℝ) = (m - i + 1 : ℕ) * (m - i)! := by
      exact_mod_cast Nat.factorial_succ (m - i)
    have hmi : ((m - i + 1 : ℕ) : ℝ) ≤ m + 1 := by
      exact_mod_cast (by omega : m - i + 1 ≤ m + 1)
    have hp1 : (ρ * s) ^ i * s ^ (m - i) = s ^ m * ρ ^ i := by
      rw [mul_pow, show s ^ m = s ^ i * s ^ (m - i) by
        rw [← pow_add, Nat.add_sub_cancel' hi]]
      ring
    have hp2 : (ρ * s) ^ i * s ^ (m - i + 1) = s ^ (m + 1) * ρ ^ i := by
      rw [pow_succ, ← mul_assoc, hp1, pow_succ]; ring
    calc ‖(m.choose i : ℂ) * (P i * d (m - i + 1) + Q i * d (m - i))‖
        ≤ (m.choose i : ℝ) * (‖P i‖ * ‖d (m - i + 1)‖ + ‖Q i‖ * ‖d (m - i)‖) := by
          rw [norm_mul, Complex.norm_natCast]
          gcongr
          exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ (m.choose i : ℝ) * (A * i ! * (ρ * s) ^ i * (K * (m - i + 1)! * s ^ (m - i + 1)) +
            A * i ! * (ρ * s) ^ i * (K * (m - i)! * s ^ (m - i))) := by
          gcongr
          · exact hP i
          · exact hQ i
      _ = A * K * ((m.choose i : ℝ) * i ! * (m - i)!) *
            (((m - i + 1 : ℕ) : ℝ) * ((ρ * s) ^ i * s ^ (m - i + 1)) +
              (ρ * s) ^ i * s ^ (m - i)) := by
          rw [hf]; ring
      _ ≤ A * K * m ! * ((m + 1) * s ^ (m + 1) + s ^ m) * ρ ^ i := by
          rw [hc, hp1, hp2]
          calc A * K * m ! * (((m - i + 1 : ℕ) : ℝ) * (s ^ (m + 1) * ρ ^ i) +
                s ^ m * ρ ^ i)
              ≤ A * K * m ! * ((m + 1) * (s ^ (m + 1) * ρ ^ i) + s ^ m * ρ ^ i) := by
                gcongr
            _ = _ := by ring
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  rw [← Finset.mul_sum] at hsum
  have hgeo : ∑ i ∈ Finset.range (m + 1), ρ ^ i ≤ (1 - ρ)⁻¹ := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := m + 1) hρ0 hρ1
    rw [← Finset.range_eq_Ico, pow_zero, one_div] at this
    exact this
  have hBm : 0 ≤ A * K * m ! * ((m + 1) * s ^ (m + 1) + s ^ m) := by positivity
  have h3 : ‖d (m + 2)‖ ≤ A * K * m ! * ((m + 1) * s ^ (m + 1) + s ^ m) * (1 - ρ)⁻¹ := by
    rw [show d (m + 2) = _ from linearOdeTaylorCoeff_add_two P Q a b m]
    exact hsum.trans (mul_le_mul_of_nonneg_left hgeo hBm)
  refine h3.trans ?_
  have hfac : ((m + 2)! : ℝ) = (m + 2) * (m + 1) * m ! := by
    push_cast [Nat.factorial_succ]; ring
  rw [hfac]
  have hKm : 0 ≤ K * m ! * s ^ m := by positivity
  have hmN : (N : ℝ) ≤ m := by exact_mod_cast hm
  have key : A * (1 - ρ)⁻¹ * ((m + 1) * s + 1) ≤ (m + 2) * (m + 1) * s ^ 2 := by
    have : A * (1 - ρ)⁻¹ * (s + 1) ≤ (m + 2) * s ^ 2 := by nlinarith
    nlinarith
  calc A * K * m ! * ((m + 1) * s ^ (m + 1) + s ^ m) * (1 - ρ)⁻¹
      = (A * (1 - ρ)⁻¹ * ((m + 1) * s + 1)) * (K * m ! * s ^ m) := by ring
    _ ≤ ((m + 2) * (m + 1) * s ^ 2) * (K * m ! * s ^ m) := by gcongr
    _ = K * ((m + 2) * (m + 1) * m !) * s ^ (m + 2) := by ring

/-- Cauchy estimates on a disc: if `f` is holomorphic on `ball z₀ R` and `0 < t < R`, then
`‖f⁽ⁱ⁾(z₀)‖ ≤ C i! t⁻ⁱ` for some `C ≥ 0` and all `i`. -/
private lemma exists_norm_iteratedDeriv_le_of_ball {f : ℂ → ℂ} {z₀ : ℂ} {R t : ℝ}
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (ht : 0 < t) (htR : t < R) :
    ∃ C, 0 ≤ C ∧ ∀ i, ‖iteratedDeriv i f z₀‖ ≤ C * i ! * t⁻¹ ^ i := by
  set t' : ℝ≥0 := ⟨(t + R) / 2, by linarith⟩
  have ht' : (t' : ℝ) = (t + R) / 2 := rfl
  have hsub : closedBall z₀ (t' : ℝ) ⊆ ball z₀ R := closedBall_subset_ball (by rw [ht']; linarith)
  have h2 := (hf.mono hsub).hasFPowerSeriesOnBall (by
    rw [← NNReal.coe_pos, ht']; linarith)
  have hz : ball z₀ R ∈ 𝓝 z₀ := ball_mem_nhds z₀ (ht.trans htR)
  have h1 := (hf.analyticAt hz).hasFPowerSeriesAt
  have heq := h2.hasFPowerSeriesAt.eq_formalMultilinearSeries h1
  set r : ℝ≥0 := ⟨t, ht.le⟩
  have hlt : (r : ℝ≥0∞) < (FormalMultilinearSeries.ofScalars ℂ
      (fun n => iteratedDeriv n f z₀ / n !)).radius := by
    rw [← heq]
    refine lt_of_lt_of_le ?_ h2.r_le
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
    change t < (t + R) / 2
    linarith
  obtain ⟨C, hC, hCb⟩ := FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius _ hlt
  refine ⟨C, hC.le, fun i => ?_⟩
  have hb := hCb i
  rw [FormalMultilinearSeries.ofScalars_norm, norm_div, Complex.norm_natCast] at hb
  have hr : ((r : ℝ)) = t := rfl
  rw [hr] at hb
  have hfac : (0 : ℝ) < i ! := by positivity
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  rw [div_mul_eq_mul_div, div_le_iff₀ hfac] at hb
  linarith

/-- **Existence of solutions on a disc** of a linear second-order ODE with holomorphic
coefficients: for `p`, `q` holomorphic on `ball z₀ R` and any `w₀`, `w₁` there is a `w`
holomorphic on `ball z₀ R` with `(w')' = p w' + q w` there, `w(z₀) = w₀` and `w'(z₀) = w₁`.
(Uniqueness: `ODE.eqOn_of_ode`.) -/
theorem exists_ball_solution_linear_ode {p q : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hp : DifferentiableOn ℂ p (ball z₀ R)) (hq : DifferentiableOn ℂ q (ball z₀ R))
    (w₀ w₁ : ℂ) :
    ∃ w : ℂ → ℂ, DifferentiableOn ℂ w (ball z₀ R) ∧
      (∀ z ∈ ball z₀ R, HasDerivAt (deriv w) (p z * deriv w z + q z * w z) z) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ := by
  rcases le_or_gt R 0 with hR | hR
  · refine ⟨fun z => w₀ + w₁ * (z - z₀), ?_, ?_, by simp, ?_⟩
    · rw [ball_eq_empty.mpr hR]; exact differentiableOn_empty
    · rw [ball_eq_empty.mpr hR]; simp
    · have : HasDerivAt (fun z => w₀ + w₁ * (z - z₀)) w₁ z₀ := by
        simpa using (((hasDerivAt_id z₀).sub_const z₀).const_mul w₁).const_add w₀
      exact this.deriv
  have hz₀ : ball z₀ R ∈ 𝓝 z₀ := ball_mem_nhds z₀ hR
  set P : ℕ → ℂ := fun i => iteratedDeriv i p z₀
  set Q : ℕ → ℂ := fun i => iteratedDeriv i q z₀
  set d := linearOdeTaylorCoeff P Q w₀ w₁
  set c : ℕ → ℂ := fun n => d n / (n !)
  set S := FormalMultilinearSeries.ofScalars ℂ c
  have hrad : ENNReal.ofReal R ≤ S.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    have hrR : (r : ℝ) < R := by
      rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hR] at hr
    have hr0 : (0 : ℝ) ≤ r := r.2
    set r₂ : ℝ := (2 * r + R) / 3
    set t : ℝ := (r + 2 * R) / 3
    have hr₂ : 0 < r₂ := by positivity
    have ht : 0 < t := by positivity
    have hr₂t : r₂ < t := by simp only [r₂, t]; linarith
    have htR : t < R := by simp only [t]; linarith
    obtain ⟨A₁, hA₁, hP⟩ := exists_norm_iteratedDeriv_le_of_ball hp ht htR
    obtain ⟨A₂, hA₂, hQ⟩ := exists_norm_iteratedDeriv_le_of_ball hq ht htR
    have hρs : r₂ / t * r₂⁻¹ = t⁻¹ := by field_simp
    obtain ⟨K, hK⟩ := exists_norm_linearOdeTaylorCoeff_le_of_ratio (P := P) (Q := Q) w₀ w₁
      (s := r₂⁻¹) (ρ := r₂ / t) (by positivity) (by positivity)
      ((div_lt_one ht).mpr hr₂t) (le_max_left 0 (max A₁ A₂))
      (fun i => by
        rw [hρs]
        exact (hP i).trans (by gcongr; exact (le_max_left _ _).trans (le_max_right _ _)))
      (fun i => by
        rw [hρs]
        exact (hQ i).trans (by gcongr; exact (le_max_right _ _).trans (le_max_right _ _)))
    refine S.le_radius_of_bound K fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm]
    have hfac : (0 : ℝ) < n ! := by positivity
    have hn : ‖c n‖ ≤ K * r₂⁻¹ ^ n := by
      simp only [c, norm_div, Complex.norm_natCast]
      rw [div_le_iff₀ hfac]
      linarith [hK n]
    have hK0 : 0 ≤ K := by
      have := (norm_nonneg _).trans (hK 0); simpa using this
    have hrr : (r : ℝ) ≤ r₂ := by simp only [r₂]; linarith
    calc ‖c n‖ * (r : ℝ) ^ n ≤ K * r₂⁻¹ ^ n * r₂ ^ n := by gcongr
      _ = K := by
          rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hr₂.ne', one_pow, mul_one]
  have hpos : 0 < S.radius := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hR) hrad
  have hS := S.hasFPowerSeriesOnBall hpos
  have hw := hS.comp_sub z₀
  rw [zero_add] at hw
  set w : ℂ → ℂ := fun z => S.sum (z - z₀)
  have han : ∀ z ∈ ball z₀ R, AnalyticAt ℂ w z := fun z hz => hw.analyticAt_of_mem (by
    rw [Metric.mem_eball, edist_dist]
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hz) hrad)
  have hD : ∀ n, iteratedDeriv n w z₀ = d n := by
    intro n
    have h := hw.factorial_smul 1 n
    rw [iteratedDeriv_eq_iteratedFDeriv, ← h, FormalMultilinearSeries.ofScalars_apply_eq]
    simp only [c, one_pow, smul_eq_mul, mul_one, nsmul_eq_mul]
    have : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    field_simp
  have hpa : ∀ z ∈ ball z₀ R, AnalyticAt ℂ p z := fun z hz =>
    hp.analyticAt (isOpen_ball.mem_nhds hz)
  have hqa : ∀ z ∈ ball z₀ R, AnalyticAt ℂ q z := fun z hz =>
    hq.analyticAt (isOpen_ball.mem_nhds hz)
  have hz₀m : z₀ ∈ ball z₀ R := mem_ball_self hR
  have hloc := eventually_ode_of_iteratedDeriv (han z₀ hz₀m) (hpa z₀ hz₀m) (hqa z₀ hz₀m)
    (fun n => by
      simp only [hD]
      exact linearOdeTaylorCoeff_add_two P Q w₀ w₁ n)
  have hg : AnalyticOnNhd ℂ (fun z => deriv (deriv w) z - (p z * deriv w z + q z * w z))
      (ball z₀ R) := fun z hz =>
    ((han z hz).deriv.deriv).sub (((hpa z hz).mul (han z hz).deriv).add
      ((hqa z hz).mul (han z hz)))
  have hzero := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball z₀ R).isPreconnected hz₀m (by filter_upwards [hloc] with z hz; simp [hz])
  refine ⟨w, fun z hz => (han z hz).differentiableAt.differentiableWithinAt, fun z hz => ?_,
    ?_, ?_⟩
  · have h := hzero hz
    simp only [Pi.zero_apply, sub_eq_zero] at h
    rw [← h]
    exact (han z hz).deriv.differentiableAt.hasDerivAt
  · have := hD 0; simpa [d, linearOdeTaylorCoeff] using this
  · have := hD 1; simpa [d, linearOdeTaylorCoeff] using this

end ODE
