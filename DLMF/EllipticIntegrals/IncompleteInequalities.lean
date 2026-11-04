/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Inequalities

/-!
# Inequalities for incomplete Legendre integrals (DLMF §19.9(ii))

The amplitude is real with `0 ≤ φ ≤ π/2` and `Δ = √(1 - k² sin²φ) > 0`; the inequalities are
stated for the real parts of the complex DLMF integrals at real arguments. The domain
qualifications are listed in `DLMF.EllipticIntegrals.Inequalities`.

## Main results

* `one_le_completeEllipticE_le`, `one_le_completeEllipticPi_le`: the second and third lines of
  DLMF 19.9.1.
* `incompleteEllipticF_bounds`, `incompleteEllipticE_bounds`, `incompleteEllipticPi_bounds`: DLMF
  19.9.11–19.9.13.
* `incompleteEllipticF_div_sin_bounds`, `incompleteEllipticF_div_sin_mul_log_bounds`,
  `incompleteEllipticF_eq_log_sub_bounds`: DLMF 19.9.14–19.9.16.
* `incompleteEllipticF_arctanh_bounds`: Carlson's bounds by inverse hyperbolic tangents
  (DLMF 19.9.17, 19.9.18).

## Implementation notes

The strict bounds (19.9.14) use the normalized first-kind integral from
`Carlson.Elliptic.Standard`, the strict capacity lower bound from
`Carlson.Elliptic.CapacityBound`, and the geometric upper bound from `Carlson.Mean.Bounds`
(all in lean-codes).
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology NNReal

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic
open DLMF.Hypergeometric (pochhammer_ofReal hasSum_pochhammer_div_factorial)

/-! ### §19.9(ii) Incomplete integrals -/

/-- DLMF 19.9.11: `φ ≤ F(φ, k) ≤ min(φ/Δ, gd⁻¹(φ))` for `0 < k < 1`, `0 ≤ φ ≤ π/2`,
`Δ = √(1 - k² sin²φ)`; the bound `gd⁻¹(φ)` (DLMF 4.23.41,
`DLMF.Elementary.inverseGudermannian`) is stated for `φ < π/2`. -/
@[dlmf 19.9.E11]
theorem incompleteEllipticF_bounds {φ k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ π / 2) :
    φ ≤ (incompleteEllipticF φ k).re ∧
      (incompleteEllipticF φ k).re ≤ φ / Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) ∧
      (φ < π / 2 → (incompleteEllipticF φ k).re ≤ DLMF.Elementary.inverseGudermannian φ) := by
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hm0 : 0 ≤ k ^ 2 := sq_nonneg k
  rw [re_incompleteEllipticF_ofReal hk2.le, DLMF.Elliptic.Real.incompleteEllipticFOfParameter]
  have hc := DLMF.Elliptic.continuous_one_sub_mul_sin_sq_rpow hk2 (-(1 / 2))
  have hΔ : 0 < 1 - k ^ 2 * Real.sin φ ^ 2 := DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 φ
  refine ⟨?_, ?_, ?_⟩
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hφ0
      (continuous_const.intervalIntegrable 0 φ)
      (hc.intervalIntegrable 0 φ) (f := fun _ => (1 : ℝ)) (fun θ hθ => by
        rw [rpow_neg_half_eq_inv_sqrt (DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ).le]
        have h1 := one_sub_mul_sin_sq_le_one hm0 θ
        have h2 := DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ
        rw [one_le_inv₀ (Real.sqrt_pos.mpr h2)]
        exact Real.sqrt_le_one.mpr h1)
    simpa using h
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hφ0
      (hc.intervalIntegrable 0 φ)
      (continuous_const.intervalIntegrable 0 φ)
      (g := fun _ => (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2))⁻¹)
      (fun θ hθ => by
        rw [rpow_neg_half_eq_inv_sqrt (DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ).le]
        exact inv_anti₀ (Real.sqrt_pos.mpr hΔ)
          (Real.sqrt_le_sqrt (one_sub_mul_sin_sq_le_of_le hm0 hθ.1 hθ.2 hφ1)))
    simpa [div_eq_mul_inv] using h
  · intro hφ2
    unfold DLMF.Elementary.inverseGudermannian
    have hcos : ∀ θ ∈ Icc (0 : ℝ) φ, 0 < Real.cos θ := fun θ hθ =>
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
    refine intervalIntegral.integral_mono_on hφ0 (hc.intervalIntegrable 0 φ) ?_ ?_
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hφ0]
      exact (Real.continuous_cos.continuousOn).inv₀ fun θ hθ => (hcos θ hθ).ne'
    · intro θ hθ
      rw [rpow_neg_half_eq_inv_sqrt (DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ).le]
      refine inv_anti₀ (hcos θ hθ) ?_
      rw [← Real.sqrt_sq (hcos θ hθ).le]
      exact Real.sqrt_le_sqrt (cos_sq_le_one_sub_mul_sin_sq hk2.le θ)

/-- DLMF 19.9.12: `max(sin φ, φΔ) ≤ E(φ, k) ≤ φ` for `0 < k < 1`, `0 ≤ φ ≤ π/2`. -/
@[dlmf 19.9.E12]
theorem incompleteEllipticE_bounds {φ k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ π / 2) :
    max (Real.sin φ) (φ * Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2)) ≤ (incompleteEllipticE φ k).re ∧
      (incompleteEllipticE φ k).re ≤ φ := by
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hm0 : 0 ≤ k ^ 2 := sq_nonneg k
  rw [re_incompleteEllipticE_ofReal hk2.le, DLMF.Elliptic.Real.incompleteEllipticEOfParameter]
  have hc := DLMF.Elliptic.continuous_one_sub_mul_sin_sq_rpow hk2 (1 / 2)
  refine ⟨max_le ?_ ?_, ?_⟩
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hφ0
      (Real.continuous_cos.intervalIntegrable 0 φ)
      (hc.intervalIntegrable 0 φ) (fun θ hθ => by
        rw [rpow_half_eq_sqrt]
        have hcos : 0 ≤ Real.cos θ :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
        rw [← Real.sqrt_sq hcos]
        exact Real.sqrt_le_sqrt (cos_sq_le_one_sub_mul_sin_sq hk2.le θ))
    simpa using h
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hφ0
      (continuous_const.intervalIntegrable 0 φ)
      (hc.intervalIntegrable 0 φ) (f := fun _ => Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2))
      (fun θ hθ => by
        rw [rpow_half_eq_sqrt]
        exact Real.sqrt_le_sqrt (one_sub_mul_sin_sq_le_of_le hm0 hθ.1 hθ.2 hφ1))
    simpa using h
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hφ0
      (hc.intervalIntegrable 0 φ)
      (continuous_const.intervalIntegrable 0 φ) (g := fun _ => (1 : ℝ)) (fun θ _ => by
        rw [rpow_half_eq_sqrt]
        exact Real.sqrt_le_one.mpr (one_sub_mul_sin_sq_le_one hm0 θ))
    simpa using h

/-- Pointwise comparison of the third-kind integrands in the modulus. -/
private lemma piIntegrand_le_piIntegrand_of_le {n m m' θ : ℝ} (hn : n < 1) (hm : m ≤ m')
    (hm' : m' * Real.sin θ ^ 2 < 1)
    (hm0 : m * Real.sin θ ^ 2 < 1) :
    DLMF.Elliptic.piIntegrand n m θ ≤ DLMF.Elliptic.piIntegrand n m' θ := by
  unfold DLMF.Elliptic.piIntegrand
  refine mul_le_mul_of_nonneg_left ?_ (inv_one_sub_mul_sin_sq_pos hn θ).le
  rw [rpow_neg_half_eq_inv_sqrt (by linarith), rpow_neg_half_eq_inv_sqrt (by linarith)]
  refine inv_anti₀ (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt ?_)
  nlinarith [sq_nonneg (Real.sin θ)]

/-- DLMF 19.9.13: `Π(φ, α², 0) ≤ Π(φ, α², k) ≤ min(Π(φ, α², 0)/Δ, Π(φ, α², 1))` for
`0 < k < 1`, `0 ≤ φ ≤ π/2` and real `α² < 1`; the bound by `Π(φ, α², 1)` is stated for
`φ < π/2` (it is infinite at `φ = π/2`). -/
@[dlmf 19.9.E13]
theorem incompleteEllipticPi_bounds {φ α2 k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ π / 2) (hα : α2 < 1) :
    (incompleteEllipticPi φ α2 0).re ≤ (incompleteEllipticPi φ α2 k).re ∧
      (incompleteEllipticPi φ α2 k).re ≤
        (incompleteEllipticPi φ α2 0).re / Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) ∧
      (φ < π / 2 → (incompleteEllipticPi φ α2 k).re ≤ (incompleteEllipticPi φ α2 1).re) := by
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hm0 : 0 ≤ k ^ 2 := sq_nonneg k
  have e0 : incompleteEllipticPi φ α2 0 = incompleteEllipticPi φ α2 ((0 : ℝ) : ℂ) := by simp
  have e1 : incompleteEllipticPi φ α2 1 = incompleteEllipticPi φ α2 ((1 : ℝ) : ℂ) := by simp
  rw [e0, e1, re_incompleteEllipticPi_ofReal hα hk2.le,
      re_incompleteEllipticPi_ofReal (k := 0) hα (by norm_num),
    re_incompleteEllipticPi_ofReal (k := 1) hα (by norm_num)]
  simp only [DLMF.Elliptic.Real.incompleteEllipticPiOfParameter]
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, one_pow]
  have hcont : ∀ m : ℝ, m < 1 → Continuous (DLMF.Elliptic.piIntegrand α2 m) :=
    fun m hm => DLMF.Elliptic.continuous_piIntegrand hα hm
  have hΔ : 0 < 1 - k ^ 2 * Real.sin φ ^ 2 := DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 φ
  refine ⟨?_, ?_, ?_⟩
  · refine intervalIntegral.integral_mono_on hφ0 ((hcont 0 (by norm_num)).intervalIntegrable _ _)
      ((hcont _ hk2).intervalIntegrable _ _) fun θ _ => ?_
    have h := piIntegrand_le_piIntegrand_of_le (θ := θ) hα hm0 (by nlinarith [Real.sin_sq_le_one θ])
      (by simp)
    simpa using h
  · rw [div_eq_mul_inv, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_mono_on hφ0 ((hcont _ hk2).intervalIntegrable _ _)
      (((hcont 0 (by norm_num)).mul continuous_const).intervalIntegrable _ _) fun θ hθ => ?_
    unfold DLMF.Elliptic.piIntegrand
    simp only [zero_mul, sub_zero, Real.one_rpow, mul_one]
    refine mul_le_mul_of_nonneg_left ?_ (inv_one_sub_mul_sin_sq_pos hα θ).le
    rw [rpow_neg_half_eq_inv_sqrt (DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ).le]
    exact inv_anti₀ (Real.sqrt_pos.mpr hΔ)
      (Real.sqrt_le_sqrt (one_sub_mul_sin_sq_le_of_le hm0 hθ.1 hθ.2 hφ1))
  · intro hφ2
    have hcos : ∀ θ ∈ Icc (0 : ℝ) φ, 0 < Real.cos θ := fun θ hθ =>
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
    have hbase : ∀ θ ∈ Icc (0 : ℝ) φ, 0 < 1 - 1 * Real.sin θ ^ 2 := fun θ hθ => by
      have := Real.sin_sq_add_cos_sq θ
      have := hcos θ hθ
      nlinarith
    refine intervalIntegral.integral_mono_on hφ0 ((hcont _ hk2).intervalIntegrable _ _) ?_
      fun θ hθ => ?_
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hφ0]
      unfold DLMF.Elliptic.piIntegrand
      refine ContinuousOn.mul ((Continuous.inv₀ (by fun_prop)
        fun θ => (DLMF.Elliptic.one_sub_mul_sin_sq_pos hα θ).ne').continuousOn) ?_
      · exact ContinuousOn.rpow_const (by fun_prop) fun θ hθ => Or.inl (hbase θ hθ).ne'
    · have hb := hbase θ hθ
      exact piIntegrand_le_piIntegrand_of_le hα hk2.le (by linarith)
        (by nlinarith [Real.sin_sq_le_one θ])

/-- DLMF 19.9.1, second line: `1 ≤ E(k) ≤ π/2` for `0 < k < 1`. -/
@[dlmf 19.9.E1]
theorem one_le_completeEllipticE_le {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    1 ≤ (completeEllipticE k).re ∧ (completeEllipticE k).re ≤ π / 2 := by
  rw [completeEllipticE_eq_incompleteEllipticE]
  have h := incompleteEllipticE_bounds (φ := π / 2) hk0 hk1 (by positivity) le_rfl
  rw [Real.sin_pi_div_two] at h
  exact ⟨le_trans (le_max_left _ _) h.1, h.2⟩

/-- DLMF 19.9.1, third line: `1 ≤ (2/π)√(1 - α²) Π(α², k) ≤ 1/k'` for `0 < k < 1` and real
`α² < 1`. -/
@[dlmf 19.9.E1]
theorem one_le_completeEllipticPi_le {α2 k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hα : α2 < 1) :
    1 ≤ 2 / π * Real.sqrt (1 - α2) * (completeEllipticPi α2 k).re ∧
      2 / π * Real.sqrt (1 - α2) * (completeEllipticPi α2 k).re ≤ 1 / Real.sqrt (1 - k ^ 2) := by
  rw [completeEllipticPi_eq_incompleteEllipticPi]
  have h := incompleteEllipticPi_bounds (φ := π / 2) hk0 hk1 (by positivity) le_rfl hα
  rw [Real.sin_pi_div_two, one_pow, mul_one] at h
  have e0 : incompleteEllipticPi ((π / 2 : ℝ) : ℂ) α2 0 =
      incompleteEllipticPi ((π / 2 : ℝ) : ℂ) α2 ((0 : ℝ) : ℂ) :=
    by simp
  rw [e0, re_incompleteEllipticPi_ofReal (k := 0) hα (by norm_num)] at h
  have hz : DLMF.Elliptic.Real.incompleteEllipticPiOfParameter (π / 2) α2 (0 ^ 2) = π /
      (2 * Real.sqrt (1 - α2)) := by
    rw [zero_pow two_ne_zero]
    exact DLMF.Elliptic.Real.completeEllipticPiOfParameter_param_zero hα
  rw [hz] at h
  have hs : 0 < Real.sqrt (1 - α2) := Real.sqrt_pos.mpr (by linarith)
  have hk' : 0 < Real.sqrt (1 - k ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hc : 0 < 2 / π * Real.sqrt (1 - α2) := by positivity
  obtain ⟨h1, h2, -⟩ := h
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hc.le
    calc (1 : ℝ) = 2 / π * Real.sqrt (1 - α2) * (π / (2 * Real.sqrt (1 - α2))) := by
          field_simp
      _ ≤ _ := this
  · have := mul_le_mul_of_nonneg_left h2 hc.le
    calc _ ≤ 2 / π * Real.sqrt (1 - α2) * (π / (2 * Real.sqrt (1 - α2)) / Real.sqrt (1 - k ^ 2)) :=
          this
      _ = 1 / Real.sqrt (1 - k ^ 2) := by field_simp

/-- DLMF 19.9.14: `3/(1 + Δ + cos φ) < F(φ, k)/sin φ < (Δ cos φ)^{-1/3}` for `0 < k < 1`,
`0 < φ < π/2`. -/
@[dlmf 19.9.E14]
theorem incompleteEllipticF_div_sin_bounds {φ k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) :
    3 / (1 + Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) + Real.cos φ) <
        (incompleteEllipticF φ k).re / Real.sin φ ∧
      (incompleteEllipticF φ k).re / Real.sin φ <
        (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) * Real.cos φ) ^ (-(1 / 3) : ℝ) := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφ1⟩
  have hx : 0 < Real.cos φ ^ 2 := sq_pos_of_pos hc
  have hy : 0 < 1 - k ^ 2 * Real.sin φ ^ 2 := DLMF.Elliptic.one_sub_mul_sin_sq_pos hk φ
  have hxy : ¬(Real.cos φ ^ 2 = 1 - k ^ 2 * Real.sin φ ^ 2 ∧ 1 - k ^ 2 * Real.sin φ ^ 2 = 1) := by
    intro he
    nlinarith [Real.sin_sq_add_cos_sq φ, sq_pos_of_pos hs]
  have hF : (incompleteEllipticF φ k).re / Real.sin φ =
      (Carlson.carlsonRF ((Real.cos φ ^ 2 : ℝ) : ℂ)
          ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) 1).re := by
    have h := congrArg Complex.re (Carlson.Real.incEllIntFk_eq hφ0 hφ1 hk)
    have he := incompleteEllipticF_eq_ofReal (m:=k ^ 2) (k:=(k : ℂ)) (by push_cast; rfl) hk.le φ
    rw [he, ofReal_re]
    change DLMF.Elliptic.Real.incompleteEllipticFOfParameter φ (k ^ 2) / Real.sin φ = _
    simp only [ofReal_re] at h
    have hreal : Carlson.Real.incEllIntFk φ k =
        DLMF.Elliptic.Real.incompleteEllipticFOfParameter φ (k ^ 2) := by
      simp only [Carlson.Real.incEllIntFk,
          DLMF.Elliptic.Real.incompleteEllipticFOfParameter, neg_div]
    rw [hreal] at h
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at h
    rw [h]
    field_simp
  rw [hF]
  constructor
  · have h := Carlson.carlsonRF_capacity_lower_bound hx hy (by norm_num : (0 : ℝ) < 1) hxy
    simpa only [Real.sqrt_sq hc.le, Real.sqrt_one, ofReal_one, add_comm, add_left_comm] using h
  · let b : Fin 3 → ℝ := fun _ => 1 / 2
    let v : Fin 3 → ℝ := ![Real.cos φ ^ 2, 1 - k ^ 2 * Real.sin φ ^ 2, 1]
    have hb : b ∈ ProbabilityTheory.mvRealBetaDomain := by intro i; norm_num [b]
    have hv : ∀ i, 0 < v i := by intro i; fin_cases i <;> first | exact hx | exact hy | norm_num [v]
    have hn : ∃ i j, v i ≠ v j := by
      refine ⟨0, 2, ?_⟩
      dsimp [v]
      nlinarith [Real.sin_sq_add_cos_sq φ, sq_pos_of_pos hs]
    have hh := (Carlson.carlsonRReal_bounds_between_neg_sum_zero hb hv hn
      (by norm_num : (-1 / 2 : ℝ) < 0) (by norm_num [b, Fin.sum_univ_succ])).2
    have he := Carlson.ofReal_carlsonRReal (-1 / 2) hb hv
    have he' : (Carlson.carlsonRF ((Real.cos φ ^ 2 : ℝ) : ℂ)
        ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) 1).re =
        Carlson.carlsonRReal (-1 / 2) b v := by
      unfold Carlson.carlsonRF
      have ev : (fun i => (v i : ℂ)) =
          ![((Real.cos φ ^ 2 : ℝ) : ℂ), ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ), 1] := by
        ext i; fin_cases i <;> simp [v]
      norm_num only [b, ofReal_neg, ofReal_div, ofReal_one, ofReal_ofNat, ev] at he
      rw [neg_div, ←he, ofReal_re]
      simp only [neg_div, b]
    rw [he']
    refine hh.trans_eq ?_
    rw [←Real.exp_mul, Real.rpow_def_of_pos (mul_pos (Real.sqrt_pos.mpr hy) hc)]
    congr 1
    simp only [b, v, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Real.log_one, mul_zero,
          Real.log_mul (Real.sqrt_pos.mpr hy).ne' hc.ne',
      Real.log_sqrt hy.le, Real.log_pow]
    ring

/-- DLMF 19.9.15: `1 < F(φ, k)/((sin φ) ln(4/(Δ + cos φ))) < 4/(2 + (1 + k²) sin²φ)` for
`0 < k < 1`, `0 < φ ≤ π/2`. -/
@[dlmf 19.9.E15]
theorem incompleteEllipticF_div_sin_mul_log_bounds {φ k : ℝ} (hk0 : 0 < k)
    (hk1 : k < 1) (hφ0 : 0 < φ)
    (hφ1 : φ ≤ π / 2) :
    1 < (incompleteEllipticF φ k).re /
        (Real.sin φ * Real.log (4 / (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) + Real.cos φ))) ∧
      (incompleteEllipticF φ k).re /
          (Real.sin φ * Real.log (4 / (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) + Real.cos φ))) <
        4 / (2 + (1 + k ^ 2) * Real.sin φ ^ 2) := by
  sorry

/-- DLMF 19.9.16: `F(φ, k) = (2/π) K(k') ln(4/(Δ + cos φ)) - θΔ²` with
`(sin φ)/8 < θ < (ln 2)/(k² sin φ)`, for `0 < k < 1`, `0 < φ ≤ π/2`; here `θ` is defined by the
equation. -/
@[dlmf 19.9.E16]
theorem incompleteEllipticF_eq_log_sub_bounds {φ k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 < φ)
    (hφ1 : φ ≤ π / 2) :
    Real.sin φ / 8 <
        (2 / π * (completeEllipticK (Real.sqrt (1 - k ^ 2))).re *
            Real.log (4 / (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) + Real.cos φ)) -
          (incompleteEllipticF φ k).re) / (1 - k ^ 2 * Real.sin φ ^ 2) ∧
      (2 / π * (completeEllipticK (Real.sqrt (1 - k ^ 2))).re *
            Real.log (4 / (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) + Real.cos φ)) -
          (incompleteEllipticF φ k).re) / (1 - k ^ 2 * Real.sin φ ^ 2) <
        Real.log 2 / (k ^ 2 * Real.sin φ) := by
  sorry

/-! ### Helpers for 19.9.17–19.9.18 -/

/-- At `x`, the function `Real.artanh` has derivative `(1 / (1 - x ^ 2))`. -/
private lemma hasDerivAt_artanh_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  have h1 : 0 < 1 + x := by linarith [hx.1]
  have h2 : 0 < 1 - x := by linarith [hx.2]
  have heq : (fun y => 1 / 2 * (Real.log (1 + y) - Real.log (1 - y))) =ᶠ[𝓝 x] Real.artanh := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    have h1' : 0 < 1 + y := by linarith [hy.1]
    have h2' : 0 < 1 - y := by linarith [hy.2]
    rw [Real.artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩, Real.log_div h1'.ne' h2'.ne']
  have hd := (((hasDerivAt_id x).const_add 1).log h1.ne').sub
    (((hasDerivAt_id x).const_sub 1).log h2.ne') |>.const_mul (1 / 2 : ℝ)
  refine (hd.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  have h3 : (1 - x ^ 2) ≠ 0 := by nlinarith
  simp only [id]
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `∫ θ in (0 : ℝ)..φ, Real.cos θ /
(1 - q ^ 2 * Real.sin θ ^ 2) = q⁻¹ * Real.artanh (q * Real.sin φ)`. -/
private lemma integral_cos_div_one_sub_sq_mul_sin_sq {q φ : ℝ} (hq : 0 < q) (hφ0 : 0 ≤ φ)
    (hφ1 : φ < π / 2)
    (hqs : q * Real.sin φ < 1) :
    ∫ θ in (0 : ℝ)..φ, Real.cos θ / (1 - q ^ 2 * Real.sin θ ^ 2) =
      q⁻¹ * Real.artanh (q * Real.sin φ) := by
  have hmem : ∀ θ ∈ uIcc 0 φ, q * Real.sin θ ∈ Ioo (-1 : ℝ) 1 := by
    intro θ hθ
    rw [uIcc_of_le hφ0] at hθ
    have h0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2])
    have h1 : Real.sin θ ≤ Real.sin φ :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hθ.1, Real.pi_pos]) hφ1.le hθ.2
    exact ⟨by nlinarith, by nlinarith⟩
  have hden : ∀ θ ∈ uIcc 0 φ, 0 < 1 - q ^ 2 * Real.sin θ ^ 2 := by
    intro θ hθ
    have := hmem θ hθ
    nlinarith [this.1, this.2]
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun θ => q⁻¹ * Real.artanh (q * Real.sin θ))
    (f' := fun θ => Real.cos θ / (1 - q ^ 2 * Real.sin θ ^ 2)) (a := 0) (b := φ)
    (fun θ hθ => by
      have h := ((hasDerivAt_artanh_of_mem_Ioo (hmem θ hθ)).comp θ
        ((Real.hasDerivAt_sin θ).const_mul q)).const_mul q⁻¹
      refine h.congr_deriv ?_
      have := (hden θ hθ).ne'
      rw [mul_pow]
      field_simp)
    (ContinuousOn.intervalIntegrable (by
      refine ContinuousOn.div (by fun_prop) (by fun_prop) fun θ hθ => (hden θ hθ).ne'))
  rw [this]
  simp

/-- Cauchy–Schwarz for interval integrals of continuous nonnegative functions. -/
private lemma sq_integral_sqrt_mul_sqrt_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : Continuous f)
    (hg : Continuous g) (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x) (hg0 : ∀ x ∈ Icc a b, 0 ≤ g x) :
    (∫ x in a..b, Real.sqrt (f x) * Real.sqrt (g x)) ^ 2 ≤
      (∫ x in a..b, f x) * ∫ x in a..b, g x := by
  set A := ∫ x in a..b, f x
  set B := ∫ x in a..b, g x
  set C := ∫ x in a..b, Real.sqrt (f x) * Real.sqrt (g x)
  have hsf : Continuous fun x => Real.sqrt (f x) := hf.sqrt
  have hsg : Continuous fun x => Real.sqrt (g x) := hg.sqrt
  have hq : ∀ t : ℝ, 0 ≤ A * (t * t) + (-2 * C) * t + B := by
    intro t
    have h0 : 0 ≤ ∫ x in a..b, (t * Real.sqrt (f x) - Real.sqrt (g x)) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
    have hexp : ∫ x in a..b, (t * Real.sqrt (f x) - Real.sqrt (g x)) ^ 2 =
        ∫ x in a..b, (t ^ 2 * f x - 2 * t * (Real.sqrt (f x) * Real.sqrt (g x)) + g x) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le hab] at hx
      have h1 := Real.sq_sqrt (hf0 x hx)
      have h2 := Real.sq_sqrt (hg0 x hx)
      linear_combination t ^ 2 * h1 + h2
    rw [hexp, intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h0
    · linarith
    all_goals first
      | exact (hf.intervalIntegrable _ _).const_mul _
      | exact ((hsf.mul hsg).intervalIntegrable _ _).const_mul _
      | exact hg.intervalIntegrable _ _
      | exact (((hf.intervalIntegrable _ _).const_mul _).sub
          (((hsf.mul hsg).intervalIntegrable _ _).const_mul _))
  have := discrim_le_zero hq
  rw [discrim] at this
  nlinarith

/-- Estimate under the stated parameter and domain assumptions: `c / ((a + b) / 2) ≤ c * (a⁻¹ +
b⁻¹) / 2`. -/
private lemma div_avg_le_mul_avg_inv {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) :
    c / ((a + b) / 2) ≤ c * (a⁻¹ + b⁻¹) / 2 := by
  rw [div_le_iff₀ (by positivity)]
  have : c * (a⁻¹ + b⁻¹) / 2 * ((a + b) / 2) = c * ((a + b) ^ 2 / (4 * a * b)) := by
    field_simp; ring
  rw [this]
  have h1 : 1 ≤ (a + b) ^ 2 / (4 * a * b) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg (a - b)]
  nlinarith

/-- Estimate under the stated parameter and domain assumptions: `c / ((c ^ 2 + b) / 2) ≤
(Real.sqrt b)⁻¹`. -/
private lemma div_avg_sq_add_le_inv_sqrt {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    c / ((c ^ 2 + b) / 2) ≤ (Real.sqrt b)⁻¹ := by
  have hsb := Real.sq_sqrt hb.le
  have hsb0 := Real.sqrt_pos.2 hb
  rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hsb0]
  nlinarith [sq_nonneg (c - Real.sqrt b)]

/-- Identity under the stated parameter and domain assumptions: `Real.sqrt (c * ((c ^ 2)⁻¹ + b⁻¹)
/ 2) * Real.sqrt (c / ((c ^ 2 + b) / 2)) = (Real.sqrt b)⁻¹`. -/
private lemma sqrt_mul_sqrt_avg_eq_inv_sqrt {b c : ℝ} (hc : 0 < c) (hb : 0 < b) :
    Real.sqrt (c * ((c ^ 2)⁻¹ + b⁻¹) / 2) * Real.sqrt (c / ((c ^ 2 + b) / 2)) =
      (Real.sqrt b)⁻¹ := by
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_inv]
  congr 1
  field_simp
  ring

/-- DLMF 19.9.17–19.9.18 (Carlson 1961b): `L ≤ F(φ, k) ≤ √(UL) ≤ (U + L)/2 ≤ U` with
`L = σ⁻¹ arctanh(σ sin φ)`, `σ = √((1 + k²)/2)`, and
`U = ½ arctanh(sin φ) + ½ k⁻¹ arctanh(k sin φ)`, for `0 < k < 1`, `0 ≤ φ < π/2`. In the variable
`θ` the three integrands are `cos θ/√(ab)`, `cos θ (1/a + 1/b)/2` and `2 cos θ/(a + b)` with
`a = cos²θ`, `b = 1 - k² sin²θ`; the bounds follow from AM–GM and Cauchy–Schwarz. -/
@[dlmf 19.9.E17, dlmf 19.9.E18]
theorem incompleteEllipticF_arctanh_bounds {φ k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 ≤ φ)
    (hφ1 : φ < π / 2) :
    let σ := Real.sqrt ((1 + k ^ 2) / 2)
    let L := σ⁻¹ * Real.artanh (σ * Real.sin φ)
    let U := Real.artanh (Real.sin φ) / 2 + k⁻¹ * Real.artanh (k * Real.sin φ) / 2
    L ≤ (incompleteEllipticF φ k).re ∧ (incompleteEllipticF φ k).re ≤ Real.sqrt (U * L) ∧
      Real.sqrt (U * L) ≤ (U + L) / 2 ∧ (U + L) / 2 ≤ U := by
  intro σ L U
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hσ2 : σ ^ 2 = (1 + k ^ 2) / 2 := Real.sq_sqrt (by positivity)
  have hσ0 : 0 < σ := Real.sqrt_pos.2 (by positivity)
  have hσ1 : σ < 1 := by nlinarith
  have hs0 : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith [Real.pi_pos])
  have hs1 : Real.sin φ < 1 := by
    rw [← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) le_rfl hφ1
  -- pointwise data on `[0, φ]`
  have hc : ∀ θ ∈ Icc (0 : ℝ) φ, 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hb : ∀ θ : ℝ, 0 < 1 - k ^ 2 * Real.sin θ ^ 2 := fun θ =>
    DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ
  have hsq : ∀ θ : ℝ, 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := fun θ => by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  set A : ℝ → ℝ := fun θ => Real.cos θ * ((1 - Real.sin θ ^ 2)⁻¹ +
    (1 - k ^ 2 * Real.sin θ ^ 2)⁻¹) / 2 with hA
  set G : ℝ → ℝ := fun θ => Real.cos θ / (1 - σ ^ 2 * Real.sin θ ^ 2) with hG
  set Φ : ℝ → ℝ := fun θ => (Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹ with hΦ
  have hF : (incompleteEllipticF φ k).re = ∫ θ in (0 : ℝ)..φ, Φ θ := by
    rw [re_incompleteEllipticF_ofReal hk2.le, DLMF.Elliptic.Real.incompleteEllipticFOfParameter]
    exact intervalIntegral.integral_congr fun θ _ => rpow_neg_half_eq_inv_sqrt (hb θ).le
  have hU : U = ∫ θ in (0 : ℝ)..φ, A θ := by
    have h1 := integral_cos_div_one_sub_sq_mul_sin_sq one_pos hφ0 hφ1 (by linarith)
    have h2 := integral_cos_div_one_sub_sq_mul_sin_sq hk0 hφ0 hφ1 (by nlinarith)
    simp only [one_pow, one_mul, inv_one] at h1
    have hi1 : IntervalIntegrable (fun θ => Real.cos θ / (1 - Real.sin θ ^ 2)) volume 0 φ := by
      refine ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
      intro θ hθ; rw [uIcc_of_le hφ0] at hθ; rw [hsq]; exact pow_ne_zero _ (hc θ hθ).ne'
    have hi2 : IntervalIntegrable (fun θ => Real.cos θ / (1 - k ^ 2 * Real.sin θ ^ 2)) volume 0 φ :=
      (Continuous.div (by fun_prop) (by fun_prop) fun θ => (hb θ).ne').intervalIntegrable _ _
    have : (∫ θ in (0 : ℝ)..φ, A θ) = ((∫ θ in (0 : ℝ)..φ, Real.cos θ / (1 - Real.sin θ ^ 2)) +
        ∫ θ in (0 : ℝ)..φ, Real.cos θ / (1 - k ^ 2 * Real.sin θ ^ 2)) / 2 := by
      rw [← intervalIntegral.integral_add hi1 hi2, ← intervalIntegral.integral_div]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [hA]; ring
    rw [this, h1, h2]
    show Real.artanh (Real.sin φ) / 2 + k⁻¹ * Real.artanh (k * Real.sin φ) / 2 = _
    ring
  have hL : L = ∫ θ in (0 : ℝ)..φ, G θ :=
    (integral_cos_div_one_sub_sq_mul_sin_sq hσ0 hφ0 hφ1 (by nlinarith)).symm
  have hab : ∀ θ ∈ Icc (0 : ℝ) φ, 1 - σ ^ 2 * Real.sin θ ^ 2 =
      ((1 - Real.sin θ ^ 2) + (1 - k ^ 2 * Real.sin θ ^ 2)) / 2 := fun θ _ => by
    rw [hσ2]; ring
  -- pointwise inequalities
  have hGΦ : ∀ θ ∈ Icc (0 : ℝ) φ, G θ ≤ Φ θ := by
    intro θ hθ
    simp only [hG, hΦ]
    rw [hab θ hθ, hsq]
    exact div_avg_sq_add_le_inv_sqrt (hb θ) (hc θ hθ)
  have hGA : ∀ θ ∈ Icc (0 : ℝ) φ, G θ ≤ A θ := by
    intro θ hθ
    simp only [hG, hA]
    rw [hab θ hθ, hsq]
    exact div_avg_le_mul_avg_inv (pow_pos (hc θ hθ) 2) (hb θ) (hc θ hθ).le
  have hAG : ∀ θ ∈ Icc (0 : ℝ) φ, Real.sqrt (A θ) * Real.sqrt (G θ) = Φ θ := by
    intro θ hθ
    simp only [hG, hA, hΦ]
    rw [hab θ hθ, hsq]
    exact sqrt_mul_sqrt_avg_eq_inv_sqrt (hc θ hθ) (hb θ)
  have hG0 : ∀ θ ∈ Icc (0 : ℝ) φ, 0 ≤ G θ := fun θ hθ => by
    simp only [hG]; rw [hab θ hθ]
    exact div_nonneg (hc θ hθ).le (by linarith [hb θ, sq_nonneg (Real.sin θ), Real.sin_sq_le_one θ])
  have hA0 : ∀ θ ∈ Icc (0 : ℝ) φ, 0 ≤ A θ := fun θ hθ => (hG0 θ hθ).trans (hGA θ hθ)
  -- continuity
  have hdenσ : ∀ θ : ℝ, 0 < 1 - σ ^ 2 * Real.sin θ ^ 2 := fun θ => by
    nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.sin θ)]
  have hGc : Continuous G := Continuous.div (by fun_prop) (by fun_prop) fun θ => (hdenσ θ).ne'
  have hΦc : Continuous Φ :=
    (Continuous.sqrt (by fun_prop)).inv₀ fun θ => (Real.sqrt_pos.2 (hb θ)).ne'
  -- `A` is continuous on `[0, φ]`; use a continuous extension for Cauchy–Schwarz
  have hAc : ContinuousOn A (Icc 0 φ) := by
    refine ContinuousOn.div_const (ContinuousOn.mul (by fun_prop) (ContinuousOn.add ?_ ?_)) _
    · refine ContinuousOn.inv₀ (by fun_prop) fun θ hθ => ?_
      rw [hsq]; exact pow_ne_zero _ (hc θ hθ).ne'
    · exact (Continuous.inv₀ (by fun_prop) fun θ => (hb θ).ne').continuousOn
  obtain ⟨A', hA'c, hA'eq⟩ : ∃ A' : ℝ → ℝ, Continuous A' ∧ EqOn A' A (Icc 0 φ) := by
    refine ⟨IccExtend hφ0 (domRestrict (Icc 0 φ) A), ?_, fun θ hθ => ?_⟩
    · exact continuous_IccExtend_iff.2 (hAc.domRestrict)
    · rw [IccExtend_of_mem hφ0 _ hθ]; rfl
  have hint_eq : ∀ {f g : ℝ → ℝ}, EqOn f g (Icc 0 φ) → ∫ θ in (0 : ℝ)..φ, f θ =
      ∫ θ in (0 : ℝ)..φ, g θ :=
    fun h => intervalIntegral.integral_congr (by rw [uIcc_of_le hφ0]; exact h)
  have hUA' : U = ∫ θ in (0 : ℝ)..φ, A' θ := by rw [hU]; exact (hint_eq hA'eq).symm
  have hcs := sq_integral_sqrt_mul_sqrt_le hφ0 hA'c hGc (fun θ hθ => (hA'eq hθ).symm ▸ hA0 θ hθ) hG0
  have hFeq : (∫ θ in (0 : ℝ)..φ, Real.sqrt (A' θ) * Real.sqrt (G θ)) =
      (incompleteEllipticF φ k).re := by
    rw [hF]; exact hint_eq fun θ hθ => by rw [hA'eq hθ]; exact hAG θ hθ
  rw [hFeq, ← hUA', ← hL] at hcs
  have hLF : L ≤ (incompleteEllipticF φ k).re := by
    rw [hL, hF]
    exact intervalIntegral.integral_mono_on hφ0 (hGc.intervalIntegrable _ _)
      (hΦc.intervalIntegrable _ _) hGΦ
  have hLU : L ≤ U := by
    rw [hL, hUA']
    exact intervalIntegral.integral_mono_on hφ0 (hGc.intervalIntegrable _ _)
      (hA'c.intervalIntegrable _ _) fun θ hθ => (hA'eq hθ).symm ▸ hGA θ hθ
  have hL0 : 0 ≤ L := by rw [hL]; exact intervalIntegral.integral_nonneg hφ0 hG0
  have hF0 : 0 ≤ (incompleteEllipticF φ k).re := hL0.trans hLF
  have hU0 : 0 ≤ U := hL0.trans hLU
  refine ⟨hLF, ?_, ?_, by linarith⟩
  · rw [← Real.sqrt_sq hF0]; exact Real.sqrt_le_sqrt hcs
  · rw [← Real.sqrt_sq (by linarith : 0 ≤ (U + L) / 2)]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (U - L)])

end DLMF.EllipticIntegrals
