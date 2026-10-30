/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Basic.Integrals
public import DLMF.Hypergeometric.Identities

/-!
# Complete elliptic integrals (Temme §12.1, DLMF §§19.2–19.7)

With the parameter `m = k²`,
`K(m) = ∫₀^{π/2} (1 - m sin²θ)^{-1/2} dθ` and `E(m) = ∫₀^{π/2} (1 - m sin²θ)^{1/2} dθ`.
The integrals are differentiated under the integral sign; one integration by parts,
`(1-m) ∫₀^{π/2} (1 - m sin²θ)^{-3/2} dθ = E(m)`, gives the derivatives (DLMF 19.4.1–19.4.2).
Legendre's relation (19.7.1) follows because its left side has zero derivative on `(0, 1)` and
tends to `π/2` as `m → 0⁺`: `E(m) - K(m) = O(m)` while `K(1-m) = O(m^{-1/2})`. Euler's integral
gives the hypergeometric forms (19.5.1–19.5.2).

## Main results

* `Real.hasDerivAt_compEllIntKm`, `Real.hasDerivAt_compEllIntEm`: DLMF 19.4.1–19.4.2 in the
  parameter `m`.
* `legendre_relation`: `E(m)K(1-m) + E(1-m)K(m) - K(m)K(1-m) = π/2`.
* `Real.compEllIntKm_eq_ordinaryHypergeometric`, `Real.compEllIntEm_eq_ordinaryHypergeometric`.
-/

@[expose] public section

open Real Set Filter
open scoped Topology
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Elliptic

/-- Differentiation in the parameter of `∫₀^{π/2} (1 - m sin²θ)^p dθ`. -/
theorem hasDerivAt_integral_one_sub_mul_sin_sq_rpow (p : ℝ) {m₀ : ℝ} (hm : m₀ < 1) :
    HasDerivAt (fun m => ∫ θ in (0 : ℝ)..(π / 2), (1 - m * sin θ ^ 2) ^ p)
      (∫ θ in (0 : ℝ)..(π / 2), -p * sin θ ^ 2 * (1 - m₀ * sin θ ^ 2) ^ (p - 1)) m₀ := by
  set ε := (1 - m₀) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set δ := min 1 (1 - (m₀ + ε)) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by rw [hε]; linarith)
  set R := 1 + (|m₀| + ε) with hR
  have hbase : ∀ m ∈ Metric.ball m₀ ε, ∀ θ : ℝ,
      δ ≤ 1 - m * sin θ ^ 2 ∧ 1 - m * sin θ ^ 2 ≤ R := by
    intro m hm θ
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hm
    have hs := sin_sq_le_one θ
    have hs0 := sq_nonneg (sin θ)
    constructor
    · rcases le_or_gt m 0 with h | h
      · exact le_trans (min_le_left _ _) (by nlinarith)
      · exact le_trans (min_le_right _ _) (by nlinarith)
    · have := one_sub_mul_sin_sq_le (m := m) θ
      have : |m| ≤ |m₀| + ε := by
        rw [abs_le]; constructor <;> linarith [neg_abs_le m₀, le_abs_self m₀]
      linarith
  have hmem : ∀ m ∈ Metric.ball m₀ ε, m < 1 := by
    intro m hm; rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hm; rw [hε] at hm; linarith
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := 0) (b := π / 2)
    (F := fun (m θ : ℝ) => (1 - m * sin θ ^ 2) ^ p)
    (F' := fun (m θ : ℝ) => -p * sin θ ^ 2 * (1 - m * sin θ ^ 2) ^ (p - 1))
    (bound := fun _ => |p| * (δ ^ (p - 1) + R ^ (p - 1)))
    (Metric.ball_mem_nhds m₀ hεpos)
    (by
      filter_upwards [Metric.ball_mem_nhds m₀ hεpos] with m hm
      exact (continuous_one_sub_mul_sin_sq_rpow (hmem m hm) p).aestronglyMeasurable)
    ((continuous_one_sub_mul_sin_sq_rpow hm p).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ : ℝ => -p * sin θ ^ 2).mul
      (continuous_one_sub_mul_sin_sq_rpow hm (p - 1))).aestronglyMeasurable
    (Eventually.of_forall fun θ _ m hm => by
      obtain ⟨h1, h2⟩ := hbase m hm θ
      have hpos : 0 < 1 - m * sin θ ^ 2 := lt_of_lt_of_le hδpos h1
      have hpow : (1 - m * sin θ ^ 2) ^ (p - 1) ≤ δ ^ (p - 1) + R ^ (p - 1) := by
        rcases le_or_gt (p - 1) 0 with hq | hq
        · have := rpow_le_rpow_of_nonpos hδpos h1 hq
          linarith [rpow_nonneg (le_trans hδpos.le (h1.trans h2)) (p - 1)]
        · have := rpow_le_rpow hpos.le h2 hq.le
          linarith [rpow_nonneg hδpos.le (p - 1)]
      simp only [norm_mul, norm_neg, Real.norm_eq_abs]
      rw [abs_of_nonneg (sq_nonneg (sin θ)), abs_of_pos (rpow_pos_of_pos hpos _)]
      have hs := sin_sq_le_one θ
      have hp := abs_nonneg p
      have hr := rpow_nonneg hpos.le (p - 1)
      calc |p| * sin θ ^ 2 * (1 - m * sin θ ^ 2) ^ (p - 1)
          ≤ |p| * 1 * (δ ^ (p - 1) + R ^ (p - 1)) := by gcongr
        _ = |p| * (δ ^ (p - 1) + R ^ (p - 1)) := by ring)
    intervalIntegrable_const
    (Eventually.of_forall fun θ _ m hm => by
      have hpos := one_sub_mul_sin_sq_pos (hmem m hm) θ
      have h := ((hasDerivAt_id m).mul_const (sin θ ^ 2)).const_sub 1
      have h2 := h.rpow_const (p := p) (Or.inl hpos.ne')
      exact h2.congr_deriv (by simp only [id]; ring))
  exact key.2

/-- `x^{1/2} = x · x^{-1/2}` for `x > 0`. -/
theorem rpow_half_eq_mul {x : ℝ} (hx : 0 < x) : x ^ (1 / 2 : ℝ) = x * x ^ (-(1 / 2) : ℝ) := by
  rw [← rpow_one_add' hx.le (by norm_num)]; norm_num

/-- `x^{-3/2} = (x^{-1/2})³` for `x > 0`. -/
theorem rpow_neg_three_halves_eq {x : ℝ} (hx : 0 < x) :
    x ^ (-(3 / 2) : ℝ) = (x ^ (-(1 / 2) : ℝ)) ^ 3 := by
  rw [← rpow_natCast, ← rpow_mul hx.le]; norm_num

/-- `(x^{-1/2})² x = 1` for `x > 0`. -/
theorem rpow_neg_half_sq_mul {x : ℝ} (hx : 0 < x) : (x ^ (-(1 / 2) : ℝ)) ^ 2 * x = 1 := by
  rw [← rpow_natCast, ← rpow_mul hx.le]; norm_num; rw [rpow_neg_one]; field_simp

/-- Integration by parts: `(1 - m) ∫₀^{π/2} (1 - m sin²θ)^{-3/2} dθ = E(m)`. -/
theorem one_sub_mul_integral_rpow_neg_three_halves {m : ℝ} (hm : m < 1) :
    (1 - m) * ∫ θ in (0 : ℝ)..(π / 2), (1 - m * sin θ ^ 2) ^ (-(3 / 2) : ℝ) =
      Real.compEllIntEm m := by
  set G : ℝ → ℝ := fun θ => sin θ * cos θ * (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)
  set G' : ℝ → ℝ := fun θ => (cos θ * cos θ + sin θ * (-sin θ)) *
      (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ) +
    sin θ * cos θ * (-(m * (2 * sin θ * cos θ)) * (-(1 / 2)) *
      (1 - m * sin θ ^ 2) ^ (-(1 / 2) - 1 : ℝ))
  have hG : ∀ θ, HasDerivAt G (G' θ) θ := by
    intro θ
    have hpos := one_sub_mul_sin_sq_pos hm θ
    have h1 := (hasDerivAt_sin θ).mul (hasDerivAt_cos θ)
    have h2 : HasDerivAt (fun θ => 1 - m * sin θ ^ 2) (-(m * (2 * sin θ * cos θ))) θ := by
      have := ((hasDerivAt_sin θ).pow 2).const_mul m |>.const_sub 1
      exact this.congr_deriv (by simp)
    exact h1.mul (h2.rpow_const (Or.inl hpos.ne'))
  have hcont : Continuous G' := by
    have := continuous_one_sub_mul_sin_sq_rpow hm (-(1 / 2))
    have := continuous_one_sub_mul_sin_sq_rpow hm (-(1 / 2) - 1)
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hG θ)
    (hcont.intervalIntegrable 0 (π / 2))
  simp only [G, sin_pi_div_two, cos_pi_div_two, sin_zero, mul_zero, zero_mul, sub_zero]
    at hftc
  have hpt : ∀ θ, m * G' θ = (1 - m * sin θ ^ 2) ^ (1 / 2 : ℝ) -
      (1 - m) * (1 - m * sin θ ^ 2) ^ (-(3 / 2) : ℝ) := by
    intro θ
    have hpos := one_sub_mul_sin_sq_pos hm θ
    have hr := rpow_neg_half_sq_mul hpos
    have hc : cos θ ^ 2 = 1 - sin θ ^ 2 := by rw [cos_sq']
    simp only [G']
    rw [rpow_half_eq_mul hpos, rpow_neg_three_halves_eq hpos,
      show (-(1 / 2) - 1 : ℝ) = -(3 / 2) by norm_num, rpow_neg_three_halves_eq hpos]
    generalize (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ) = r at *
    linear_combination (1 - m + m * sin θ ^ 2) * r * hr + (m * r + m ^ 2 * sin θ ^ 2 * r ^ 3) * hc
  have hint : ∫ θ in (0 : ℝ)..(π / 2), m * G' θ = 0 := by
    rw [intervalIntegral.integral_const_mul, hftc, mul_zero]
  simp_rw [hpt] at hint
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul] at hint
  · rw [Real.compEllIntEm]; linarith
  · exact (continuous_one_sub_mul_sin_sq_rpow hm _).intervalIntegrable _ _
  · exact ((continuous_one_sub_mul_sin_sq_rpow hm _).const_mul _).intervalIntegrable _ _

/-- `dE/dm = (E - K)/(2m)` (DLMF 19.4.2 in the parameter `m = k²`). -/
@[dlmf 19.4.E2]
theorem Real.hasDerivAt_compEllIntEm {m : ℝ} (hm : m < 1) (hm0 : m ≠ 0) :
    HasDerivAt Real.compEllIntEm ((Real.compEllIntEm m - Real.compEllIntKm m) / (2 * m)) m := by
  have h := hasDerivAt_integral_one_sub_mul_sin_sq_rpow (1 / 2) hm
  refine h.congr_deriv ?_
  have hpt : ∀ θ, m * (-(1 / 2) * sin θ ^ 2 * (1 - m * sin θ ^ 2) ^ (1 / 2 - 1 : ℝ)) =
      ((1 - m * sin θ ^ 2) ^ (1 / 2 : ℝ) - (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)) / 2 := by
    intro θ
    have hpos := one_sub_mul_sin_sq_pos hm θ
    rw [show (1 / 2 - 1 : ℝ) = -(1 / 2) by norm_num, rpow_half_eq_mul hpos]
    ring
  have hint : m * ∫ θ in (0 : ℝ)..(π / 2),
      -(1 / 2) * sin θ ^ 2 * (1 - m * sin θ ^ 2) ^ (1 / 2 - 1 : ℝ) =
      (Real.compEllIntEm m - Real.compEllIntKm m) / 2 := by
    rw [← intervalIntegral.integral_const_mul]
    simp_rw [hpt]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      ((continuous_one_sub_mul_sin_sq_rpow hm _).intervalIntegrable _ _)
      ((continuous_one_sub_mul_sin_sq_rpow hm _).intervalIntegrable _ _)]
    rfl
  set I := ∫ θ in (0 : ℝ)..(π / 2), -(1 / 2) * sin θ ^ 2 * (1 - m * sin θ ^ 2) ^ (1 / 2 - 1 : ℝ)
  rw [eq_div_iff (mul_ne_zero two_ne_zero hm0)]
  linarith

/-- `dK/dm = (E - (1-m)K)/(2m(1-m))` (DLMF 19.4.1 in the parameter `m = k²`). -/
@[dlmf 19.4.E1]
theorem Real.hasDerivAt_compEllIntKm {m : ℝ} (hm : m < 1) (hm0 : m ≠ 0) :
    HasDerivAt Real.compEllIntKm
      ((Real.compEllIntEm m - (1 - m) * Real.compEllIntKm m) / (2 * m * (1 - m))) m := by
  have h := hasDerivAt_integral_one_sub_mul_sin_sq_rpow (-(1 / 2)) hm
  refine h.congr_deriv ?_
  have hpt : ∀ θ, m * (-(-(1 / 2)) * sin θ ^ 2 * (1 - m * sin θ ^ 2) ^ (-(1 / 2) - 1 : ℝ)) =
      ((1 - m * sin θ ^ 2) ^ (-(3 / 2) : ℝ) - (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)) / 2 := by
    intro θ
    have hpos := one_sub_mul_sin_sq_pos hm θ
    have hr := rpow_neg_half_sq_mul hpos
    rw [show (-(1 / 2) - 1 : ℝ) = -(3 / 2) by norm_num, rpow_neg_three_halves_eq hpos]
    generalize (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ) = r at *
    linear_combination (-(r / 2)) * hr
  have hint : m * ∫ θ in (0 : ℝ)..(π / 2),
      -(-(1 / 2)) * sin θ ^ 2 * (1 - m * sin θ ^ 2) ^ (-(1 / 2) - 1 : ℝ) =
      (Real.compEllIntEm m / (1 - m) - Real.compEllIntKm m) / 2 := by
    rw [← intervalIntegral.integral_const_mul]
    simp_rw [hpt]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      ((continuous_one_sub_mul_sin_sq_rpow hm _).intervalIntegrable _ _)
      ((continuous_one_sub_mul_sin_sq_rpow hm _).intervalIntegrable _ _),
      ← one_sub_mul_integral_rpow_neg_three_halves hm]
    have : (1 - m) ≠ 0 := by linarith
    field_simp
    rfl
  have h1m : (1 - m) ≠ 0 := by linarith
  set I := ∫ θ in (0 : ℝ)..(π / 2),
    -(-(1 / 2)) * sin θ ^ 2 * (1 - m * sin θ ^ 2) ^ (-(1 / 2) - 1 : ℝ)
  have h2 : m * I * (2 * (1 - m)) = Real.compEllIntEm m - (1 - m) * Real.compEllIntKm m := by
    rw [hint]; field_simp
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hm0) h1m)]
  linarith

/-- `K(0) = π/2`. -/
theorem Real.compEllIntKm_zero : Real.compEllIntKm 0 = π / 2 := by simp [Real.compEllIntKm]

/-- `E(0) = π/2`. -/
theorem Real.compEllIntEm_zero : Real.compEllIntEm 0 = π / 2 := by simp [Real.compEllIntEm]

/-- `E(1) = 1` (DLMF 19.6.1). -/
@[dlmf 19.6.E1]
theorem Real.compEllIntEm_one : Real.compEllIntEm 1 = 1 := by
  rw [Real.compEllIntEm]
  have h : ∀ θ ∈ uIcc (0 : ℝ) (π / 2), (1 - 1 * sin θ ^ 2) ^ (1 / 2 : ℝ) = cos θ := by
    intro θ hθ
    rw [uIcc_of_le (by positivity)] at hθ
    rw [one_mul, ← cos_sq', ← sqrt_eq_rpow, sqrt_sq (cos_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, pi_pos], hθ.2⟩)]
  rw [intervalIntegral.integral_congr h, integral_cos]
  simp

/-- `K` is continuous on `(-∞, 1)`. -/
theorem Real.continuousAt_compEllIntKm {m : ℝ} (hm : m < 1) : ContinuousAt Real.compEllIntKm m :=
  (hasDerivAt_integral_one_sub_mul_sin_sq_rpow (-(1 / 2)) hm).continuousAt

/-- `E` is continuous. -/
theorem Real.continuous_compEllIntEm : Continuous Real.compEllIntEm := by
  unfold Real.compEllIntEm
  have h : Continuous fun p : ℝ × ℝ => (1 - p.1 * sin p.2 ^ 2) ^ (1 / 2 : ℝ) :=
    (continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).comp (by fun_prop)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h _ _

/-- `K(1-m) ≤ (π/2) m^{-1/2}` for `0 < m ≤ 1`. -/
theorem Real.compEllIntKm_one_sub_le {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) :
    Real.compEllIntKm (1 - m) ≤ π / 2 * m ^ (-(1 / 2) : ℝ) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π / 2)
    (C := m ^ (-(1 / 2) : ℝ))
    (f := fun θ => (1 - (1 - m) * sin θ ^ 2) ^ (-(1 / 2) : ℝ)) (fun θ _ => by
      have hb : m ≤ 1 - (1 - m) * sin θ ^ 2 := by
        nlinarith [sin_sq_le_one θ, sq_nonneg (sin θ)]
      rw [Real.norm_of_nonneg (rpow_nonneg (by linarith) _)]
      exact rpow_le_rpow_of_nonpos hm hb (by norm_num))
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos (by positivity : (0 : ℝ) < π / 2)] at h
  rw [Real.compEllIntKm]
  linarith [le_abs_self (∫ θ in (0 : ℝ)..(π / 2), (1 - (1 - m) * sin θ ^ 2) ^ (-(1 / 2) : ℝ))]

/-- `|E(m) - K(m)| ≤ π m` for `0 ≤ m ≤ 1/2`. -/
theorem Real.abs_compEllIntEm_sub_compEllIntKm_le {m : ℝ} (hm : 0 ≤ m) (hm2 : m ≤ 1 / 2) :
    |Real.compEllIntEm m - Real.compEllIntKm m| ≤ π * m := by
  have hm1 : m < 1 := by linarith
  rw [Real.compEllIntEm, Real.compEllIntKm, ← intervalIntegral.integral_sub
    ((continuous_one_sub_mul_sin_sq_rpow hm1 _).intervalIntegrable _ _)
    ((continuous_one_sub_mul_sin_sq_rpow hm1 _).intervalIntegrable _ _)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π / 2)
    (C := 2 * m) (f := fun θ => (1 - m * sin θ ^ 2) ^ (1 / 2 : ℝ) -
      (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)) (fun θ _ => by
      have hpos := one_sub_mul_sin_sq_pos hm1 θ
      have hs := sin_sq_le_one θ
      have hs0 := sq_nonneg (sin θ)
      have hb : 1 / 2 ≤ 1 - m * sin θ ^ 2 := by nlinarith
      have hr : (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ) ≤ 2 := by
        have := rpow_le_rpow_of_nonpos (by norm_num) hb (by norm_num : (-(1 / 2) : ℝ) ≤ 0)
        have h2 : (1 / 2 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 2 := by
          rw [rpow_neg (by norm_num), ← sqrt_eq_rpow, inv_le_comm₀ (by positivity) two_pos,
            le_sqrt (by norm_num) (by norm_num)]
          norm_num
        linarith
      have hr0 := rpow_nonneg hpos.le (-(1 / 2) : ℝ)
      rw [rpow_half_eq_mul hpos, Real.norm_eq_abs,
        show (1 - m * sin θ ^ 2) * (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ) -
          (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ) =
          -(m * sin θ ^ 2 * (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)) by ring, abs_neg,
        abs_of_nonneg (by positivity)]
      calc m * sin θ ^ 2 * (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ) ≤ m * 1 * 2 := by gcongr
        _ = 2 * m := by ring)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos (by positivity : (0 : ℝ) < π / 2)] at h
  linarith

/-- **Legendre's relation** in the parameter `m = k²`:
`E(m) K(1-m) + E(1-m) K(m) - K(m) K(1-m) = π/2` for `0 < m < 1` (DLMF 19.7.1). -/
@[dlmf 19.7.E1]
theorem legendre_relation {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) :
    Real.compEllIntEm m * Real.compEllIntKm (1 - m) +
      Real.compEllIntEm (1 - m) * Real.compEllIntKm m -
      Real.compEllIntKm m * Real.compEllIntKm (1 - m) = π / 2 := by
  set L : ℝ → ℝ := fun m => Real.compEllIntEm m * Real.compEllIntKm (1 - m) +
      Real.compEllIntEm (1 - m) * Real.compEllIntKm m -
      Real.compEllIntKm m * Real.compEllIntKm (1 - m) with hL
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt L 0 x := by
    intro x hx
    have ha := hx.1; have hb := hx.2
    have hb0 : 1 - x ≠ 0 := by linarith
    have hEa := Real.hasDerivAt_compEllIntEm hb ha.ne'
    have hKa := Real.hasDerivAt_compEllIntKm hb ha.ne'
    have hEb := (Real.hasDerivAt_compEllIntEm (by linarith : 1 - x < 1) hb0).comp x
      ((hasDerivAt_id x).const_sub 1)
    have hKb := (Real.hasDerivAt_compEllIntKm (by linarith : 1 - x < 1) hb0).comp x
      ((hasDerivAt_id x).const_sub 1)
    have h := ((hEa.mul hKb).add (hEb.mul hKa)).sub (hKa.mul hKb)
    refine h.congr_deriv ?_
    simp only [Function.comp_apply, sub_sub_cancel]
    field_simp
    ring
  have hconst : ∀ x ∈ Ioo (0 : ℝ) 1, L x = L m := fun x hx =>
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun y hy => (hderiv y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hderiv y hy).deriv) hx ⟨hm0, hm1⟩
  -- the limit as `x → 0⁺`
  have hlim : Tendsto L (𝓝[>] 0) (𝓝 (π / 2)) := by
    have hE0 : Tendsto Real.compEllIntEm (𝓝[>] 0) (𝓝 (π / 2)) := by
      rw [← Real.compEllIntEm_zero]
      exact Real.continuous_compEllIntEm.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    have hK0 : Tendsto Real.compEllIntKm (𝓝[>] 0) (𝓝 (π / 2)) := by
      rw [← Real.compEllIntKm_zero]
      exact (Real.continuousAt_compEllIntKm (by norm_num)).tendsto.mono_left
        nhdsWithin_le_nhds
    have hE1 : Tendsto (fun x => Real.compEllIntEm (1 - x)) (𝓝[>] 0) (𝓝 1) := by
      have : Tendsto (fun x : ℝ => 1 - x) (𝓝 0) (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id (x := 𝓝 (0 : ℝ)))
      have h := (Real.continuous_compEllIntEm.continuousAt.tendsto.comp this).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      rwa [Real.compEllIntEm_one] at h
    -- `(E(x) - K(x)) K(1-x) → 0`
    have hsmall : Tendsto
        (fun x => (Real.compEllIntEm x - Real.compEllIntKm x) * Real.compEllIntKm (1 - x))
        (𝓝[>] 0) (𝓝 0) := by
      have hb : Tendsto (fun x : ℝ => π * x * (π / 2 * x ^ (-(1 / 2) : ℝ))) (𝓝[>] 0) (𝓝 0) := by
        have h1 : Tendsto (fun x : ℝ => x ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
          have := (continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).tendsto 0
          rw [zero_rpow (by norm_num)] at this
          exact this.mono_left nhdsWithin_le_nhds
        have h2 := h1.const_mul (π * (π / 2))
        rw [mul_zero] at h2
        refine h2.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        have hx : (0 : ℝ) < x := hx
        rw [show x ^ (1 / 2 : ℝ) = x * x ^ (-(1 / 2) : ℝ) from rpow_half_eq_mul hx]
        ring
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)]
        with x hx hx2
      have hx : (0 : ℝ) < x := hx
      have h1 := Real.abs_compEllIntEm_sub_compEllIntKm_le hx.le hx2.2.le
      have h2 := Real.compEllIntKm_one_sub_le hx (by linarith [hx2.2])
      have h3 : 0 ≤ Real.compEllIntKm (1 - x) := by
        rw [Real.compEllIntKm]
        exact intervalIntegral.integral_nonneg (by positivity) fun θ _ =>
          rpow_nonneg (one_sub_mul_sin_sq_pos (by linarith) θ).le _
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h3]
      exact mul_le_mul h1 h2 h3 (by positivity)
    have := ((hsmall.add (hE1.mul hK0)))
    refine (this.congr' (Eventually.of_forall fun x => ?_)).trans ?_
    · simp only [hL]; ring
    · simp
  have hev : L =ᶠ[𝓝[>] 0] fun _ => L m := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact hconst x hx
  have := tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
  exact this.symm

open Complex in
/-- `∫₀^{π/2} (1 - m sin²θ)^{-a} dθ = (π/2) ₂F₁(a, 1/2; 1; m)` for `|m| < 1`. -/
theorem ofReal_integral_eq_ordinaryHypergeometric (a : ℝ) {m : ℝ} (hm : |m| < 1) :
    ((∫ θ in (0 : ℝ)..(π / 2), (1 - m * Real.sin θ ^ 2) ^ (-a) : ℝ) : ℂ) =
      (π / 2) * ₂F₁ (a : ℂ) (1 / 2) 1 (m : ℂ) := by
  have hm1 : m < 1 := lt_of_le_of_lt (le_abs_self m) hm
  have hhalf : (0 : ℝ) < (1 / 2 : ℂ).re := by norm_num
  have hsub : (1 : ℂ) - 1 / 2 = 1 / 2 := by ring
  have hz : ‖(m : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hgamma : Complex.Gamma (1 / 2 : ℂ) * Complex.Gamma (1 / 2) = (π : ℂ) := by
    have h := Complex.Gamma_mul_Gamma_one_sub (1 / 2)
    rw [hsub, show (π : ℂ) * (1 / 2) = π / 2 by ring, Complex.sin_pi_div_two, div_one] at h
    exact h
  rw [ordinaryHypergeometric_eq_integral hhalf (by rwa [hsub]) hz, hsub, Complex.Gamma_one, hgamma]
  have hexp : (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) := by ring
  simp only [hexp]
  rw [DLMF.Hypergeometric.integral_beta_half_weight
    (fun t : ℝ => (1 - (m : ℂ) * (t : ℂ)) ^ (-(a : ℂ))), intervalIntegral.integral_ofReal.symm]
  have hpt : ∀ θ : ℝ, (((1 - m * Real.sin θ ^ 2) ^ (-a) : ℝ) : ℂ) =
      (1 - (m : ℂ) * ((Real.sin θ ^ 2 : ℝ) : ℂ)) ^ (-(a : ℂ)) := by
    intro θ
    rw [ofReal_cpow (one_sub_mul_sin_sq_pos hm1 θ).le]
    push_cast; ring_nf
  simp_rw [hpt]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- `K(m) = (π/2) ₂F₁(1/2, 1/2; 1; m)` for `|m| < 1` (DLMF 19.5.1). -/
@[dlmf 19.5.E1]
theorem Real.compEllIntKm_eq_ordinaryHypergeometric {m : ℝ} (hm : |m| < 1) :
    (Real.compEllIntKm m : ℂ) = (π / 2) * ₂F₁ (1 / 2 : ℂ) (1 / 2) 1 (m : ℂ) := by
  have h := ofReal_integral_eq_ordinaryHypergeometric (1 / 2) hm
  push_cast at h
  rw [Real.compEllIntKm]
  exact_mod_cast h

/-- `E(m) = (π/2) ₂F₁(-1/2, 1/2; 1; m)` for `|m| < 1` (DLMF 19.5.2). -/
@[dlmf 19.5.E2]
theorem Real.compEllIntEm_eq_ordinaryHypergeometric {m : ℝ} (hm : |m| < 1) :
    (Real.compEllIntEm m : ℂ) = (π / 2) * ₂F₁ (-(1 / 2) : ℂ) (1 / 2) 1 (m : ℂ) := by
  have h := ofReal_integral_eq_ordinaryHypergeometric (-(1 / 2)) hm
  rw [neg_neg] at h
  push_cast at h
  rw [Real.compEllIntEm]
  exact_mod_cast h

/-- The elliptic integral `K` agrees with the hypergeometric `compEllIntKkSeries` of
the hypergeometric chapter: `K(k²) = compEllIntKkSeries k` for `|k| < 1`. -/
theorem Real.compEllIntKm_sq_eq_compEllIntKkSeries {k : ℝ} (hk : |k| < 1) :
    (Real.compEllIntKm (k ^ 2) : ℂ) = DLMF.Hypergeometric.compEllIntKkSeries k := by
  have hk2 : |k ^ 2| < 1 := by
    rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg k) hk (by decide)
  rw [Real.compEllIntKm_eq_ordinaryHypergeometric hk2, DLMF.Hypergeometric.compEllIntKkSeries]
  push_cast; rfl

/-- `dK/dk = (E - k'² K)/(k k'²)` in the modulus `k` (DLMF 19.4.1). -/
@[dlmf 19.4.E1]
theorem Real.hasDerivAt_compEllIntKm_sq {k : ℝ} (hk0 : k ≠ 0) (hk1 : k ^ 2 < 1) :
    HasDerivAt (fun k => Real.compEllIntKm (k ^ 2))
      ((Real.compEllIntEm (k ^ 2) - (1 - k ^ 2) * Real.compEllIntKm (k ^ 2)) /
        (k * (1 - k ^ 2))) k := by
  have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * k) k := by simpa using hasDerivAt_pow 2 k
  have h := HasDerivAt.comp (h₂ := Real.compEllIntKm) (h := fun x : ℝ => x ^ 2) k
    (Real.hasDerivAt_compEllIntKm hk1 (pow_ne_zero 2 hk0)) hp
  refine h.congr_deriv ?_
  have : (1 : ℝ) - k ^ 2 ≠ 0 := by linarith
  field_simp

/-- `dE/dk = (E - K)/k` in the modulus `k` (DLMF 19.4.2). -/
@[dlmf 19.4.E2]
theorem Real.hasDerivAt_compEllIntEm_sq {k : ℝ} (hk0 : k ≠ 0) (hk1 : k ^ 2 < 1) :
    HasDerivAt (fun k => Real.compEllIntEm (k ^ 2))
      ((Real.compEllIntEm (k ^ 2) - Real.compEllIntKm (k ^ 2)) / k) k := by
  have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * k) k := by simpa using hasDerivAt_pow 2 k
  have h := HasDerivAt.comp (h₂ := Real.compEllIntEm) (h := fun x : ℝ => x ^ 2) k
    (Real.hasDerivAt_compEllIntEm hk1 (pow_ne_zero 2 hk0)) hp
  refine h.congr_deriv ?_
  field_simp

end DLMF.Elliptic

end
