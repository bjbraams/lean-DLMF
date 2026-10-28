/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.Asymptotics.PartialSums

/-!
# The central incomplete Gamma expansion

Uniform estimates for the central incomplete-Gamma regime and its coefficient expansion.

Source references and common attribution are retained in
`DLMF.IncompleteGamma.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Confluent

open DLMF.Statistical

/-! ### The central expansion 8.11.10 (helper prefix `igCen_`)

The statements 8.11.10–8.11.11 were moved verbatim to the end of the file, after the saddle
substitution `igAsy_saddle` that their proofs use. -/

/-- `d/dt (-t²) = -2t`. -/
theorem igCen_hasDerivAt_neg_sq (x : ℝ) : HasDerivAt (fun t : ℝ => -t^2) (-(2*x)) x := by
  convert (hasDerivAt_pow 2 x).const_mul (-1:ℝ) using 1
  · funext t; ring
  · push_cast; ring

/-- `|e^{-s²} - e^{-y²}| ≤ |s - y|`. -/
theorem igCen_exp_neg_sq_lip (s y : ℝ) : |Real.exp (-s^2) - Real.exp (-y^2)| ≤ |s - y| := by
  have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => Real.exp (-t^2)) (-(2*x) * Real.exp (-x^2)) x :=
    fun x => by
      have h := igCen_hasDerivAt_neg_sq x
      convert h.exp using 1; ring
  have hb : ∀ x : ℝ, ‖-(2*x) * Real.exp (-x^2)‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _), abs_mul,
      abs_two]
    have h1 : 1 + x^2 ≤ Real.exp (x^2) := by linarith [Real.add_one_le_exp (x^2)]
    have h2 : 2*|x| ≤ 1 + x^2 := by nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
    have h3 : Real.exp (-x^2) * Real.exp (x^2) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-x^2)]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun t : ℝ => Real.exp (-t^2))
    (fun x _ => (hd x).hasDerivWithinAt) (fun x _ => hb x) convex_univ (mem_univ y) (mem_univ s)
  simpa [Real.norm_eq_abs] using this

/-- Linearisation of `erf`: `|erf T - erf y - (2/√π)(T-y)e^{-y²}| ≤ (2/√π)(T-y)²`. -/
theorem igCen_erf_sub (T y : ℝ) :
    |TauCeti.Real.erf T - TauCeti.Real.erf y - 2/Real.sqrt π * (T - y) * Real.exp (-y^2)| ≤
      2/Real.sqrt π * (T - y)^2 := by
  have hc : Continuous fun t : ℝ => Real.exp (-t^2) := by fun_prop
  have h1 : TauCeti.Real.erf T - TauCeti.Real.erf y =
      2/Real.sqrt π * ∫ t in y..T, Real.exp (-t^2) := by
    rw [TauCeti.Real.erf_def, TauCeti.Real.erf_def, ← mul_sub,
      intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
  have h2 : (∫ t in y..T, Real.exp (-t^2)) - (T - y) * Real.exp (-y^2) =
      ∫ t in y..T, (Real.exp (-t^2) - Real.exp (-y^2)) := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
  have h3 : ‖∫ t in y..T, (Real.exp (-t^2) - Real.exp (-y^2))‖ ≤ |T - y| * |T - y| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [Real.norm_eq_abs]
    refine (igCen_exp_neg_sq_lip t y).trans ?_
    rcases le_total y T with h | h
    · rw [uIoc_of_le h] at ht
      rw [abs_of_nonneg (by linarith [ht.1]), abs_of_nonneg (by linarith)]; linarith [ht.2]
    · rw [uIoc_of_ge h] at ht
      rw [abs_of_nonpos (by linarith [ht.2]), abs_of_nonpos (by linarith)]; linarith [ht.1]
  have hp : 0 < 2/Real.sqrt π := by positivity
  rw [show TauCeti.Real.erf T - TauCeti.Real.erf y - 2/Real.sqrt π * (T - y) * Real.exp (-y^2) =
    2/Real.sqrt π * ((∫ t in y..T, Real.exp (-t^2)) - (T - y) * Real.exp (-y^2)) by rw [h1]; ring,
    h2, abs_mul, abs_of_pos hp]
  rw [Real.norm_eq_abs, abs_mul_abs_self] at h3
  gcongr
  nlinarith [h3]

/-- Gaussian tail: `1 - erf M ≤ e^{-M²}/M` for `M > 0`. -/
theorem igCen_one_sub_erf_le {M : ℝ} (hM : 0 < M) :
    1 - TauCeti.Real.erf M ≤ Real.exp (-M^2) / M := by
  have hc : Continuous fun t : ℝ => Real.exp (-t^2) := by fun_prop
  have hsp : 1 ≤ Real.sqrt π := by
    rw [Real.one_le_sqrt]; linarith [Real.pi_gt_three]
  have hX : ∀ X, M ≤ X → TauCeti.Real.erf X ≤ TauCeti.Real.erf M + Real.exp (-M^2) / M := by
    intro X hX
    have h1 : TauCeti.Real.erf X - TauCeti.Real.erf M =
        2/Real.sqrt π * ∫ t in M..X, Real.exp (-t^2) := by
      rw [TauCeti.Real.erf_def, TauCeti.Real.erf_def, ← mul_sub,
        intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
          (hc.intervalIntegrable _ _)]
    have h2 : ∫ t in M..X, Real.exp (-t^2) ≤ ∫ t in M..X, t / M * Real.exp (-t^2) :=
      intervalIntegral.integral_mono_on hX (hc.intervalIntegrable _ _)
        ((by fun_prop : Continuous fun t : ℝ => t / M * Real.exp (-t^2)).intervalIntegrable _ _)
        fun t ht => by
          have : 1 ≤ t / M := by rw [le_div_iff₀ hM]; linarith [ht.1]
          nlinarith [Real.exp_pos (-t^2)]
    have h3 : ∫ t in M..X, t / M * Real.exp (-t^2) =
        (Real.exp (-M^2) - Real.exp (-X^2)) / (2*M) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -Real.exp (-t^2) / (2*M))
        (fun t _ => by
          have h := igCen_hasDerivAt_neg_sq t
          convert (h.exp.neg).div_const (2*M) using 1; field_simp)
        ((by fun_prop : Continuous fun t : ℝ => t / M * Real.exp (-t^2)).intervalIntegrable _ _)]
      ring
    have h4 : (Real.exp (-M^2) - Real.exp (-X^2)) / (2*M) ≤ Real.exp (-M^2) / (2*M) := by
      gcongr; linarith [Real.exp_pos (-X^2)]
    have h5 : 2/Real.sqrt π * (Real.exp (-M^2) / (2*M)) ≤ Real.exp (-M^2) / M := by
      rw [show 2/Real.sqrt π * (Real.exp (-M^2) / (2*M)) = Real.exp (-M^2) / M / Real.sqrt π by
        field_simp]
      exact div_le_self (by positivity) hsp
    have hp : 0 ≤ 2/Real.sqrt π := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (h2.trans (h3 ▸ h4)) hp]
  have := le_of_tendsto TauCeti.Real.tendsto_erf_atTop (eventually_atTop.2 ⟨M, hX⟩)
  linarith

/-- `e^{-x} ≤ 2/x²` for `x > 0`. -/
theorem igCen_exp_neg_le {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 2 / x^2 := by
  have h := Real.pow_div_factorial_le_exp x hx.le 2
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos x) (by positivity)]
  norm_num [Nat.factorial] at h
  linarith

/-- Cubic Taylor bound for `φ(u) = u - log(1+u)`. -/
theorem igCen_phi_cubic {u : ℝ} (hu : |u| ≤ 1/2) :
    |igAsy_phi u - u^2/2 + u^3/3| ≤ 2*|u|^4 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -u) (by rw [abs_neg]; linarith) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at h
  have hu1 : 0 < 1 - |u| := by linarith
  have h2 : |u|^(3+1) / (1 - |u|) ≤ 2*|u|^4 := by
    rw [div_le_iff₀ hu1, show 3+1 = 4 from rfl]; nlinarith [pow_nonneg (abs_nonneg u) 4]
  have h3 : igAsy_phi u - u^2/2 + u^3/3 = -(0 + (-u)^(0+1)/((0:ℕ)+1) + (-u)^(1+1)/((1:ℕ)+1) +
      (-u)^(2+1)/((2:ℕ)+1) + Real.log (1 + u)) := by
    unfold igAsy_phi; push_cast; ring
  rw [h3, abs_neg]
  exact h.trans h2

/-- If `v² = 2φ(u)` and `uv ≥ 0`, then `v = u - u²/3 + O(u³)`. -/
theorem igCen_v_approx {u v : ℝ} (hu : |u| ≤ 1/2) (hv : v^2 = 2*igAsy_phi u) (huv : 0 ≤ u*v) :
    |v - (u - u^2/3)| ≤ 6*|u|^3 := by
  set w := u - u^2/3 with hw
  have hφ := igCen_phi_cubic hu
  have hu4 : |u|^4 ≤ |u|^3 / 2 := by
    rw [pow_succ]; nlinarith [pow_nonneg (abs_nonneg u) 3]
  have hd : |v^2 - w^2| ≤ 5*|u|^4 := by
    rw [hv, hw]
    have : 2*igAsy_phi u - (u - u^2/3)^2 = 2*(igAsy_phi u - u^2/2 + u^3/3) - u^4/9 := by ring
    rw [this]
    have : |u^4/9| = |u|^4/9 := by rw [abs_div, abs_pow]; norm_num
    calc _ ≤ |2*(igAsy_phi u - u^2/2 + u^3/3)| + |u^4/9| := abs_sub _ _
      _ ≤ 2*(2*|u|^4) + |u|^4/9 := by rw [abs_mul, abs_two, this]; gcongr
      _ ≤ 5*|u|^4 := by nlinarith [pow_nonneg (abs_nonneg u) 4]
  rcases eq_or_ne u 0 with h0 | h0
  · subst h0
    have : v = 0 := by
      have : v^2 = 0 := by rw [hv]; simp [igAsy_phi]
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    simp [this, hw]
  have hpos : 0 < |u| := abs_pos.2 h0
  have hwu : (5/6)*|u| ≤ |w| := by
    rw [hw, show u - u^2/3 = u*(1 - u/3) by ring, abs_mul]
    have : 5/6 ≤ |1 - u/3| := by
      rw [abs_of_pos (by linarith [neg_abs_le u, le_abs_self u])]
      linarith [le_abs_self u]
    nlinarith
  have hvw : 0 ≤ v*w := by
    rw [hw, show v*(u - u^2/3) = (u*v)*(1 - u/3) by ring]
    exact mul_nonneg huv (by linarith [le_abs_self u])
  have hsum : |w| ≤ |v + w| := by
    rcases le_total 0 w with h | h
    · have : 0 ≤ v ∨ w = 0 := by
        rcases h.lt_or_eq with h' | h'
        · left; by_contra hc; push Not at hc; nlinarith
        · right; exact h'.symm
      rcases this with hv0 | hw0
      · rw [abs_of_nonneg h, abs_of_nonneg (by linarith)]; linarith
      · rw [hw0]; simp
    · have : v ≤ 0 ∨ w = 0 := by
        rcases h.lt_or_eq with h' | h'
        · left; by_contra hc; push Not at hc; nlinarith
        · right; exact h'
      rcases this with hv0 | hw0
      · rw [abs_of_nonpos h, abs_of_nonpos (by linarith)]; linarith
      · rw [hw0]; simp
  have hm : |v - w| * |v + w| ≤ 5*|u|^4 := by
    rw [← abs_mul, show (v - w)*(v + w) = v^2 - w^2 by ring]; exact hd
  have hvw' : (5/6)*|u| ≤ |v + w| := hwu.trans hsum
  have : |v - w| * ((5/6)*|u|) ≤ 5*|u|^4 :=
    (mul_le_mul_of_nonneg_left hvw' (abs_nonneg _)).trans hm
  have h6 : 5*|u|^4 = (6*|u|^3) * ((5/6)*|u|) := by ring
  rw [h6] at this
  exact le_of_mul_le_mul_right this (by positivity)

/-- `φ'(u) = 1 - 1/(1+u)` for `u > -1`. -/
theorem igCen_hasDerivAt_phi {u : ℝ} (hu : -1 < u) :
    HasDerivAt igAsy_phi (1 - 1/(1+u)) u := by
  have h1 : HasDerivAt (fun w : ℝ => 1 + w) 1 u := (hasDerivAt_id u).const_add 1
  have h2 := (Real.hasDerivAt_log (by linarith : (1+u) ≠ 0)).comp u h1
  have := (hasDerivAt_id u).sub h2
  convert this using 1
  · funext w; simp [igAsy_phi]
  · simp [one_div]

/-- The saddle substitution `U` of `igAsy_saddle` restricted to a small interval `[-w₀, w₀]`,
with `U'(v) = 1 + 2v/3 + O(v²)` and `vU(v) ≥ 0`. -/
theorem igCen_U : ∃ (U : ℝ → ℝ) (w₀ C₂ : ℝ), 0 < w₀ ∧ w₀ ≤ 1/2 ∧ 0 ≤ C₂ ∧
    (∀ v ∈ Icc (-w₀) w₀, HasDerivAt U (deriv U v) v ∧ ContinuousAt (deriv U) v ∧
      -1/2 < U v ∧ igAsy_phi (U v) = v^2/2 ∧ 0 ≤ v * U v ∧
      |deriv U v - 1 - 2/3*v| ≤ C₂ * v^2) ∧ U (-w₀) < 0 ∧ 0 < U w₀ := by
  obtain ⟨U, p, v₀, hv₀, hp, hc, hd, -, -⟩ := igAsy_saddle
  have hc0 : p.coeff 0 = 0 := (hc 0 (by norm_num)).trans (by simp [igAsy_Pc])
  have hU0 : U 0 = 0 := by rw [← hp.coeff_zero 1]; exact hc0
  have hc1 : p.coeff 1 = 1 := (hc 1 (by norm_num)).trans (by simp [igAsy_Pc])
  have hc2 : p.coeff 2 = 1/3 := (hc 2 (by norm_num)).trans (by simp [igAsy_Pc])
  have hO := hp.isBigO_sub_partialSum_pow 3
  simp only [zero_add, FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul] at hO
  obtain ⟨c, hcpos, hcb⟩ := hO.exists_pos
  rw [isBigOWith_iff] at hcb
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hcb
  have hr : ∀ v : ℝ, |v| < ε → |U v - v - v^2/3| ≤ c * |v|^3 := by
    intro v hv
    have := hball (by simpa [Real.dist_eq] using hv)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc0, hc1, hc2, Real.norm_eq_abs] at this
    rw [abs_of_nonneg (pow_nonneg (abs_nonneg v) 3)] at this
    convert this using 2
    ring
  set w₀ := min (v₀/2) (min (ε/2) (1/(3*(1+c)))) with hw₀
  have hw0 : 0 < w₀ := by positivity
  have hw1 : w₀ ≤ v₀/2 := min_le_left _ _
  have hw2 : w₀ ≤ ε/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hw3 : w₀ ≤ 1/(3*(1+c)) := (min_le_right _ _).trans (min_le_right _ _)
  have hw3' : w₀ * (3*(1+c)) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hw3
  have hw4 : w₀ ≤ 1/3 := by nlinarith
  have hsmall : ∀ v ∈ Icc (-w₀) w₀, |v| ≤ w₀ := fun v hv => abs_le.2 ⟨hv.1, hv.2⟩
  have hrv : ∀ v ∈ Icc (-w₀) w₀, |U v - v - v^2/3| ≤ c * |v|^3 := fun v hv =>
    hr v (by linarith [hsmall v hv])
  have hUv : ∀ v ∈ Icc (-w₀) w₀, |U v - v| ≤ |v|/2 := by
    intro v hv
    have h1 := hrv v hv
    have h2 := hsmall v hv
    have h3 : c * |v| ≤ 1/3 := by nlinarith [abs_nonneg v]
    have h4 : |U v - v| ≤ |v^2/3| + |U v - v - v^2/3| := by
      have := abs_add_le (v^2/3) (U v - v - v^2/3)
      rwa [show v^2/3 + (U v - v - v^2/3) = U v - v by ring] at this
    have h5 : |v^2/3| = |v| *|v|/3 := by rw [abs_div, abs_pow, sq]; norm_num
    have h6 : c * |v|^3 = (c*|v|)*|v| *|v| := by ring
    rw [h5] at h4
    rw [h6] at h1
    have h7 : (c*|v|)*|v| *|v| ≤ (1/3)*|v| *|v| := by
      have := abs_nonneg v
      gcongr
    nlinarith [abs_nonneg v]
  have hIcc : ∀ v ∈ Icc (-w₀) w₀, v ∈ Icc (-v₀) v₀ := fun v hv =>
    ⟨by linarith [hv.1], by linarith [hv.2]⟩
  refine ⟨U, w₀, 2*(2*c+1), hw0, by linarith, by positivity, fun v hv => ?_, ?_, ?_⟩
  · obtain ⟨hUd, hUc, hU1, hUφ⟩ := hd v (hIcc v hv)
    refine ⟨hUd, hUc, hU1, hUφ, ?_, ?_⟩
    · have := hUv v hv
      have h2 : v * U v = v^2 + v * (U v - v) := by ring
      have h3 : |v * (U v - v)| ≤ |v| * (|v|/2) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left this (abs_nonneg v)
      have h4 := neg_abs_le (v * (U v - v))
      nlinarith [sq_abs v]
    · -- the derivative identity `U v · U' v = v (1 + U v)`
      have hnhds : Icc (-v₀) v₀ ∈ 𝓝 v := by
        apply Icc_mem_nhds <;> linarith [hv.1, hv.2]
      have hφU := (igCen_hasDerivAt_phi (by linarith : -1 < U v)).comp v hUd
      have hsq : HasDerivAt (fun w => igAsy_phi (U w)) v v := by
        have := (hasDerivAt_pow 2 v).div_const 2
        refine (this.congr_of_eventuallyEq ?_).congr_deriv (by push_cast; ring)
        filter_upwards [hnhds] with w hw
        exact (hd w hw).2.2.2
      have hid := hφU.unique hsq
      have hU1' : 0 < 1 + U v := by linarith
      have hkey : U v * deriv U v = v * (1 + U v) := by
        field_simp at hid
        linarith
      rcases eq_or_ne v 0 with h0 | h0
      · subst h0
        have : deriv U 0 = 1 := by rw [hp.deriv]; exact hc1
        simp [this]
      · have hvpos : 0 < |v| := abs_pos.2 h0
        have hUlow : |v|/2 ≤ |U v| := by
          have := hUv v hv
          have := abs_sub_abs_le_abs_sub v (U v)
          rw [abs_sub_comm] at this
          linarith
        set r := U v - v - v^2/3 with hrdef
        have hrb := hrv v hv
        have hid2 : (deriv U v - 1 - 2/3*v) * U v = -r + v^3/9 + v*r/3 := by
          rw [hrdef]; linear_combination hkey
        have hv1 : |v| ≤ 1 := by linarith [hsmall v hv]
        have hb : |-r + v^3/9 + v*r/3| ≤ (2*c+1) * |v|^3 := by
          have e1 : |-r + v^3/9 + v*r/3| ≤ |r| + |v|^3/9 + |v| *|r|/3 := by
            have := abs_add_le (-r + v^3/9) (v*r/3)
            have := abs_add_le (-r) (v^3/9)
            rw [abs_neg] at this
            have : |v^3/9| = |v|^3/9 := by rw [abs_div, abs_pow]; norm_num
            have : |v*r/3| = |v| *|r|/3 := by rw [abs_div, abs_mul]; norm_num
            linarith
          have e2 : |v| *|r| ≤ |r| := mul_le_of_le_one_left (abs_nonneg r) hv1
          have e3 : 0 ≤ |v|^3 := by positivity
          nlinarith
        have hm : |deriv U v - 1 - 2/3*v| * (|v|/2) ≤ (2*c+1) * |v|^3 := by
          calc |deriv U v - 1 - 2/3*v| * (|v|/2) ≤ |deriv U v - 1 - 2/3*v| * |U v| :=
                mul_le_mul_of_nonneg_left hUlow (abs_nonneg _)
            _ = |-r + v^3/9 + v*r/3| := by rw [← abs_mul, hid2]
            _ ≤ _ := hb
        have : (2*c+1) * |v|^3 = (2*(2*c+1) * v^2) * (|v|/2) := by
          rw [← sq_abs v]; ring
        rw [this] at hm
        exact le_of_mul_le_mul_right hm (by positivity)
  · have := hUv (-w₀) ⟨le_rfl, by linarith⟩
    rw [abs_neg, abs_of_pos hw0] at this
    linarith [le_abs_self (U (-w₀) - -w₀)]
  · have := hUv w₀ ⟨by linarith, le_rfl⟩
    rw [abs_of_pos hw0] at this
    linarith [neg_abs_le (U w₀ - w₀)]

/-- `(1+u)^a e^{-au} = e^{-aφ(u)}` for `u > -1`. -/
theorem igCen_kernel (a : ℝ) {u : ℝ} (hu : -1 < u) :
    (1+u)^a * Real.exp (-a*u) = Real.exp (-a * igAsy_phi u) := by
  rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_add]
  unfold igAsy_phi
  congr 1; ring

/-- The substitution `t = a(1+u)` in `∫₀ˣ t^a e^{-t} dt`. -/
theorem igCen_integral_subst {a u₁ : ℝ} (ha : 0 < a) (hu : -1 ≤ u₁) :
    ∫ t in (0:ℝ)..a*(1+u₁), t^a * Real.exp (-t) =
      a^(a+1) * Real.exp (-a) * ∫ u in (-1:ℝ)..u₁, (1+u)^a * Real.exp (-a*u) := by
  have h := intervalIntegral.integral_comp_mul_add (a := -1) (b := u₁)
    (fun t : ℝ => t^a * Real.exp (-t)) ha.ne' a
  rw [show a * -1 + a = 0 by ring, show a*u₁ + a = a*(1+u₁) by ring] at h
  rw [← smul_eq_mul (a := a^(a+1) * Real.exp (-a)), ← intervalIntegral.integral_smul]
  have h2 : ∫ u in (-1:ℝ)..u₁, (fun t : ℝ => t^a * Real.exp (-t)) (a*u + a) =
      ∫ u in (-1:ℝ)..u₁, a^a * Real.exp (-a) * ((1+u)^a * Real.exp (-a*u)) := by
    refine intervalIntegral.integral_congr fun u hu' => ?_
    rw [uIcc_of_le hu] at hu'
    have h1u : 0 ≤ 1 + u := by linarith [hu'.1]
    simp only
    rw [show a*u + a = a*(1+u) by ring, Real.mul_rpow ha.le h1u,
      show -(a*(1+u)) = -a + -a*u by ring, Real.exp_add]
    ring
  rw [h2, intervalIntegral.integral_const_mul, smul_eq_mul] at h
  have h3 : ∫ t in (0:ℝ)..a*(1+u₁), t^a * Real.exp (-t) =
      a * (a^a * Real.exp (-a) * ∫ u in (-1:ℝ)..u₁, (1+u)^a * Real.exp (-a*u)) := by
    rw [h]; field_simp
  rw [h3, intervalIntegral.integral_smul]
  simp only [smul_eq_mul]
  rw [Real.rpow_add_one ha.ne']
  ring

/-- Stirling's formula with Binet's remainder: `a^{a+1} e^{-a}/Γ(a+1) = √a/√(2π) e^{-Φ(a)}`. -/
theorem igCen_stirling {a : ℝ} (ha : 0 < a) :
    a^(a+1) * Real.exp (-a) / Real.Gamma (a+1) =
      Real.sqrt a / Real.sqrt (2*π) * Real.exp (-DLMF.Gamma.binetIntegral a) := by
  have hG : Real.Gamma (a+1) = Real.exp (Real.log a + ((a - 1/2) * Real.log a - a +
      1/2 * Real.log (2*π) + DLMF.Gamma.binetIntegral a)) := by
    rw [Real.Gamma_add_one ha.ne', Real.exp_add, Real.exp_log ha,
      ← DLMF.Gamma.log_Gamma_eq_add_binetIntegral ha, Real.exp_log (Real.Gamma_pos_of_pos ha)]
  have h1 : a^(a+1) = Real.exp ((a+1) * Real.log a) := by
    rw [Real.rpow_def_of_pos ha]; ring_nf
  have h2 : Real.sqrt a = Real.exp (1/2 * Real.log a) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ha]; ring_nf
  have h3 : Real.sqrt (2*π) = Real.exp (1/2 * Real.log (2*π)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]; ring_nf
  rw [hG, h1, h2, h3]
  simp only [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
  congr 1; ring

/-- For real `a, x > 0`, the continued `P(a+1, x)` is the real integral
`(1/Γ(a+1)) ∫₀ˣ t^a e^{-t} dt`. -/
theorem igCen_normIncGammaP_eq {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    normIncGammaPContinued ((a:ℂ)+1) (x:ℂ) =
      (((∫ t in (0:ℝ)..x, t^a * Real.exp (-t)) / Real.Gamma (a+1) : ℝ) : ℂ) := by
  have hre : 0 < ((a:ℂ)+1).re := by simp; linarith
  have hnp : ∀ n : ℕ, (a:ℂ)+1 ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  rw [normIncGammaPContinued_eq hnp, DLMF.Statistical.normIncGammaP,
    lowerIncGamma_eq_integral hre hx, show (a:ℂ)+1 = ((a+1:ℝ):ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, show ((a+1:ℝ):ℂ) - 1 = (a:ℂ) by push_cast; ring]
  push_cast
  congr 1
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun t ht => ?_
  have ht0 : (0:ℝ) ≤ t := by rw [uIcc_of_le hx.le] at ht; exact ht.1
  push_cast
  rw [ofReal_cpow ht0]

/-- Continuity of `u ↦ (1+u)^a e^{-au}` for `a ≥ 0`. -/
theorem igCen_continuous_g {a : ℝ} (ha : 0 ≤ a) :
    Continuous fun u : ℝ => (1+u)^a * Real.exp (-a*u) :=
  ((Real.continuous_rpow_const ha).comp (continuous_const.add continuous_id)).mul (by fun_prop)

/-- `∫_α^β e^{-t²} dt = (√π/2)(erf β - erf α)`. -/
theorem igCen_integral_exp_neg_sq (α β : ℝ) :
    ∫ t in α..β, Real.exp (-t^2) =
      Real.sqrt π / 2 * (TauCeti.Real.erf β - TauCeti.Real.erf α) := by
  have hc : Continuous fun t : ℝ => Real.exp (-t^2) := by fun_prop
  rw [TauCeti.Real.erf_def, TauCeti.Real.erf_def, ← mul_sub,
    intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  have : Real.sqrt π ≠ 0 := by positivity
  field_simp

/-- Gaussian integral over an interval through `erf`. -/
theorem igCen_integral_gauss {s : ℝ} (hs : 0 < s) (α β : ℝ) :
    ∫ v in α..β, Real.exp (-v^2/s^2) =
      s * (Real.sqrt π / 2) * (TauCeti.Real.erf (β/s) - TauCeti.Real.erf (α/s)) := by
  have h := intervalIntegral.integral_comp_mul_left (a := α) (b := β)
    (fun t : ℝ => Real.exp (-t^2)) (inv_ne_zero hs.ne')
  calc ∫ v in α..β, Real.exp (-v^2/s^2) = ∫ v in α..β, Real.exp (-(s⁻¹ * v)^2) := by
        congr 1; funext v; congr 1; field_simp
    _ = _ := by
        rw [h, igCen_integral_exp_neg_sq, inv_inv, smul_eq_mul, mul_comm s⁻¹ α, mul_comm s⁻¹ β,
          ← div_eq_mul_inv, ← div_eq_mul_inv]
        ring

/-- `∫_α^β v e^{-v²/s²} dv = (s²/2)(e^{-α²/s²} - e^{-β²/s²})`. -/
theorem igCen_integral_mul_gauss {s : ℝ} (hs : 0 < s) (α β : ℝ) :
    ∫ v in α..β, v * Real.exp (-v^2/s^2) =
      s^2/2 * (Real.exp (-α^2/s^2) - Real.exp (-β^2/s^2)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v => -(s^2/2) * Real.exp (-v^2/s^2))
    (fun v _ => by
      have h : HasDerivAt (fun t : ℝ => -t^2/s^2) (-(2*v)/s^2) v :=
        (igCen_hasDerivAt_neg_sq v).div_const _
      convert h.exp.const_mul (-(s^2/2)) using 1
      field_simp)
    ((by fun_prop : Continuous fun v : ℝ => v * Real.exp (-v^2/s^2)).intervalIntegrable _ _)]
  ring

/-- `v² e^{-v²/s²} ≤ 2s² e^{-v²/(2s²)}`. -/
theorem igCen_sq_mul_gauss_le {s : ℝ} (hs : 0 < s) (v : ℝ) :
    v^2 * Real.exp (-v^2/s^2) ≤ 2*s^2 * Real.exp (-(1/(2*s^2)) * v^2) := by
  set z := v^2/(2*s^2) with hz
  have h1 : v^2 = 2*s^2*z := by rw [hz]; field_simp
  have h2 : -v^2/s^2 = -z + -z := by rw [hz]; field_simp; ring
  have h3 : -(1/(2*s^2)) * v^2 = -z := by rw [hz]; field_simp
  rw [h2, h3, Real.exp_add, h1]
  have h4 : z * Real.exp (-z) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos z)]
    linarith [Real.add_one_le_exp z]
  have h5 : 0 ≤ 2*s^2*Real.exp (-z) := by positivity
  calc 2*s^2*z * (Real.exp (-z) * Real.exp (-z)) = (2*s^2*Real.exp (-z)) * (z * Real.exp (-z)) := by
        ring
    _ ≤ (2*s^2*Real.exp (-z)) * 1 := mul_le_mul_of_nonneg_left h4 h5
    _ = _ := by ring

/-- The remainder integral: if `|h(v)| ≤ C v²` on `[α, β]`, then
`|∫_α^β e^{-v²/s²} h(v) dv| ≤ 6 C s³`. -/
theorem igCen_err_bound {s C α β : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hαβ : α ≤ β) {h : ℝ → ℝ}
    (hb : ∀ v ∈ Icc α β, |h v| ≤ C * v^2) :
    |∫ v in α..β, Real.exp (-v^2/s^2) * h v| ≤ 6 * C * s^3 := by
  have hb2 : 0 < 1/(2*s^2) := by positivity
  have hint : Integrable fun v : ℝ => Real.exp (-(1/(2*s^2)) * v^2) :=
    integrable_exp_neg_mul_sq hb2
  have hG := integral_gaussian (1/(2*s^2))
  have hsq : Real.sqrt (π / (1/(2*s^2))) ≤ 3 * s := by
    have h1 : π / (1/(2*s^2)) ≤ (3*s)^2 := by
      rw [div_le_iff₀ hb2]; field_simp; nlinarith [Real.pi_lt_four, sq_nonneg s]
    calc Real.sqrt (π / (1/(2*s^2))) ≤ Real.sqrt ((3*s)^2) := Real.sqrt_le_sqrt h1
      _ = 3*s := Real.sqrt_sq (by positivity)
  have hcI : Continuous fun v : ℝ => C * (2*s^2 * Real.exp (-(1/(2*s^2)) * v^2)) := by fun_prop
  calc |∫ v in α..β, Real.exp (-v^2/s^2) * h v|
      ≤ ∫ v in α..β, C * (2*s^2 * Real.exp (-(1/(2*s^2)) * v^2)) := by
        rw [← Real.norm_eq_abs]
        refine intervalIntegral.norm_integral_le_of_norm_le hαβ
          (Eventually.of_forall fun v hv => ?_) (hcI.intervalIntegrable _ _)
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have := hb v ⟨hv.1.le, hv.2⟩
        calc Real.exp (-v^2/s^2) * |h v| ≤ Real.exp (-v^2/s^2) * (C * v^2) :=
              mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
          _ = C * (v^2 * Real.exp (-v^2/s^2)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (igCen_sq_mul_gauss_le hs v) hC
    _ = C * (2*s^2) * ∫ v in α..β, Real.exp (-(1/(2*s^2)) * v^2) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]; ring
    _ ≤ C * (2*s^2) * ∫ v, Real.exp (-(1/(2*s^2)) * v^2) := by
        gcongr
        rw [intervalIntegral.integral_of_le hαβ]
        exact setIntegral_le_integral hint (Eventually.of_forall fun _ => (Real.exp_pos _).le)
    _ ≤ C * (2*s^2) * (3*s) := by rw [hG]; gcongr
    _ = 6 * C * s^3 := by ring

/-- The left piece `∫_{-1}^b (1+u)^a e^{-au} du ∈ [0, e^{-aφ(b)}]` for `-1 < b ≤ 0`. -/
theorem igCen_J1 {a b : ℝ} (ha : 0 < a) (hb1 : -1 < b) (hb0 : b ≤ 0) :
    0 ≤ ∫ u in (-1:ℝ)..b, (1+u)^a * Real.exp (-a*u) ∧
      ∫ u in (-1:ℝ)..b, (1+u)^a * Real.exp (-a*u) ≤ Real.exp (-a * igAsy_phi b) := by
  have hc := igCen_continuous_g ha.le
  have hle : (-1:ℝ) ≤ b := hb1.le
  constructor
  · exact intervalIntegral.integral_nonneg hle fun u hu =>
      mul_nonneg (Real.rpow_nonneg (by linarith [hu.1]) _) (Real.exp_pos _).le
  · have := intervalIntegral.integral_mono_on hle (hc.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable (μ := volume) _ _)
      (g := fun _ => Real.exp (-a * igAsy_phi b)) fun u hu => by
        rcases hu.1.eq_or_lt with h | h
        · subst h; simp [Real.zero_rpow ha.ne']; positivity
        · rw [igCen_kernel a h, Real.exp_le_exp]
          have := igAsy_phi_anti (s := 1+u) (t := 1+b) (by linarith) (by linarith [hu.2])
            (by linarith)
          simp only [add_sub_cancel_left] at this
          nlinarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have := Real.exp_pos (-a * igAsy_phi b)
    nlinarith

/-- The comparison of the Gaussian main term with the DLMF form (algebraic part of 8.11.10). -/
theorem igCen_stepB {s y B π' rT ry eT ey v₁ : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hB : 0 < B)
    (hy : |y| ≤ B) (hπ'1 : 1 ≤ π') (hey0 : 0 ≤ ey) (hey1 : ey ≤ 1)
    (herf : |rT - ry - 2/π' * (v₁/s - y) * ey| ≤ 2/π' * (v₁/s - y)^2)
    (hlip : |ey - eT| ≤ |v₁/s - y|)
    (hρ : |v₁ - (s*y - (s*y)^2/3)| ≤ 6*|s*y|^3) :
    |((1 + rT)/2 - s/(3*π') * eT) - ((1 + ry)/2 - s/(3*π')*(1+y^2)*ey)| ≤
      ((B^2/3 + 6*B^3)^2 + (B^2/3 + 6*B^3) + 6*B^3) * s^2 := by
  set c₁ := B^2/3 + 6*B^3 with hc₁
  have hπ'0 : 0 < π' := by linarith
  have hs3π : s/(3*π') ≤ s := div_le_self hs.le (by linarith)
  have hyB3 : |y|^3 ≤ B^3 := pow_le_pow_left₀ (abs_nonneg y) hy 3
  have hyB2 : |y|^2 ≤ B^2 := pow_le_pow_left₀ (abs_nonneg y) hy 2
  set ρ := v₁ - (s*y - (s*y)^2/3) with hρdef
  have hρb : |ρ| ≤ 6 * s^3 * B^3 := by
    calc |ρ| ≤ 6*|s*y|^3 := hρ
      _ = 6 * s^3 * |y|^3 := by rw [abs_mul, abs_of_pos hs]; ring
      _ ≤ 6 * s^3 * B^3 := by gcongr
  set d := v₁/s - y with hd
  have hdρ : d = ρ/s - s*y^2/3 := by
    rw [hd, hρdef]; field_simp; ring
  have hρs : |ρ/s| ≤ 6 * B^3 * s^2 := by
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    calc |ρ| ≤ 6 * s^3 * B^3 := hρb
      _ = 6 * B^3 * s^2 * s := by ring
  have hsy : |s*y^2/3| ≤ s * B^2/3 := by
    rw [abs_div, abs_mul, abs_of_pos hs, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 3)]
    gcongr
  have hdb : |d| ≤ s * c₁ := by
    rw [hdρ]
    have h1 : 6 * B^3 * s^2 ≤ 6 * B^3 * s := by
      have : s^2 ≤ s := by nlinarith
      have : 0 ≤ 6 * B^3 := by positivity
      exact mul_le_mul_of_nonneg_left (by assumption) this
    calc |ρ/s - s*y^2/3| ≤ |ρ/s| + |s*y^2/3| := abs_sub _ _
      _ ≤ 6 * B^3 * s + s * B^2/3 := by linarith
      _ = s * c₁ := by rw [hc₁]; ring
  have hid : ((1 + rT)/2 - s/(3*π') * eT) - ((1 + ry)/2 - s/(3*π')*(1+y^2)*ey) =
      ((rT - ry)/2 - 1/π' * d * ey) + 1/π' * (ρ/s) * ey + s/(3*π') * (ey - eT) := by
    rw [hdρ]; field_simp; ring
  have q1 : |(rT - ry)/2 - 1/π' * d * ey| ≤ d^2 := by
    have e : (rT - ry)/2 - 1/π' * d * ey = (rT - ry - 2/π' * d * ey)/2 := by ring
    rw [e, abs_div, abs_two, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    have h2 : 2/π' ≤ 2 := div_le_self (by norm_num) hπ'1
    calc |rT - ry - 2/π' * d * ey| ≤ 2/π' * d^2 := herf
      _ ≤ 2 * d^2 := by gcongr
      _ = d^2 * 2 := by ring
  have q2 : |1/π' * (ρ/s) * ey| ≤ 6 * B^3 * s^2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hey0, abs_of_pos (by positivity)]
    have h1 : 1/π' ≤ 1 := div_le_self zero_le_one hπ'1
    calc 1/π' * |ρ/s| * ey ≤ 1 * (6 * B^3 * s^2) * 1 := by gcongr
      _ = _ := by ring
  have q3 : |s/(3*π') * (ey - eT)| ≤ c₁ * s^2 := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc s/(3*π') * |ey - eT| ≤ s * (s * c₁) := by gcongr; exact hlip.trans hdb
      _ = c₁ * s^2 := by ring
  have hd2 : d^2 ≤ c₁^2 * s^2 := by
    rw [← sq_abs d, show c₁^2 * s^2 = (s*c₁)^2 by ring]
    exact pow_le_pow_left₀ (abs_nonneg d) hdb 2
  rw [hid]
  calc _ ≤ |(rT - ry)/2 - 1/π' * d * ey + 1/π' * (ρ/s) * ey| +
        |s/(3*π') * (ey - eT)| := abs_add_le _ _
    _ ≤ |(rT - ry)/2 - 1/π' * d * ey| + |1/π' * (ρ/s) * ey| +
        |s/(3*π') * (ey - eT)| := by gcongr; exact abs_add_le _ _
    _ ≤ d^2 + 6 * B^3 * s^2 + c₁ * s^2 := by linarith
    _ ≤ c₁^2 * s^2 + 6 * B^3 * s^2 + c₁ * s^2 := by linarith
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
/-- The central estimate behind 8.11.10, in the variable `s = √(2/a)`:
`P(a+1, a(1+sy)) = (1 + erf y)/2 - s/(3√π) (1+y²) e^{-y²} + O(s²)` uniformly for `|y| ≤ B`. -/
theorem igCen_core {B : ℝ} (hB : 0 < B) : ∃ C s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
    ∀ s y : ℝ, 0 < s → s ≤ s₀ → |y| ≤ B →
    |(∫ t in (0:ℝ)..(2/s^2)*(1+s*y), t^(2/s^2) * Real.exp (-t)) / Real.Gamma (2/s^2+1) -
      ((1 + TauCeti.Real.erf y)/2 - s/(3*Real.sqrt π)*(1+y^2)*Real.exp (-y^2))| ≤ C * s^2 := by
  obtain ⟨U, w₀, C₂, hw0, hw1, hC₂, hU, hUm, hUp⟩ := igCen_U
  set δ₁ := min (1/2) (min (-U (-w₀)) (U w₀)) with hδ₁
  have hδ₁0 : 0 < δ₁ := by
    simp only [hδ₁, lt_min_iff]; exact ⟨by norm_num, by linarith, hUp⟩
  set c₁ := B^2/3 + 6*B^3 with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set D := (5/w₀^5 + 6*C₂) + (c₁^2 + c₁ + 6*B^3) with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨D + (2 + B^2 + D)/24, min 1 (δ₁/B), by positivity, min_le_left _ _,
    fun s y hs hs0 hy => ?_⟩
  have hs1 : s ≤ 1 := hs0.trans (min_le_left _ _)
  have hsB : s * B ≤ δ₁ := by
    have := hs0.trans (min_le_right _ _); rwa [le_div_iff₀ hB] at this
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = 2/s^2 := ⟨_, rfl⟩
  rw [← ha_def]
  have ha : 0 < a := by rw [ha_def]; positivity
  have has : a * s^2 = 2 := by rw [ha_def]; field_simp
  set u₁ := s*y with hu₁
  have hu₁B : |u₁| ≤ δ₁ := by
    rw [hu₁, abs_mul, abs_of_pos hs]; nlinarith [abs_nonneg y]
  have hδa : δ₁ ≤ 1/2 := min_le_left _ _
  have hδb : δ₁ ≤ -U (-w₀) := (min_le_right _ _).trans (min_le_left _ _)
  have hδc : δ₁ ≤ U w₀ := (min_le_right _ _).trans (min_le_right _ _)
  have hu₁h : |u₁| ≤ 1/2 := hu₁B.trans hδa
  -- the upper limit in the `v` variable
  have hUc : ContinuousOn U (Icc (-w₀) w₀) := fun v hv =>
    (hU v hv).1.continuousAt.continuousWithinAt
  obtain ⟨v₁, hv₁, hUv₁⟩ : ∃ v₁ ∈ Icc (-w₀) w₀, U v₁ = u₁ :=
    intermediate_value_Icc (by linarith) hUc
      ⟨by linarith [neg_abs_le u₁], by linarith [le_abs_self u₁]⟩
  obtain ⟨-, -, -, hφv1, hsign, -⟩ := hU v₁ hv₁
  have hv1sq : v₁^2 = 2 * igAsy_phi u₁ := by rw [← hUv₁, hφv1]; ring
  have hρ := igCen_v_approx hu₁h hv1sq (by rw [← hUv₁, mul_comm]; exact hsign)
  -- the integral as `J₁ + G₀ + (2/3) G₁ + E`
  set g : ℝ → ℝ := fun u => (1+u)^a * Real.exp (-a*u) with hg
  have hgc : Continuous g := igCen_continuous_g ha.le
  have hsub : ∫ t in (0:ℝ)..a*(1+u₁), t^a * Real.exp (-t) =
      a^(a+1) * Real.exp (-a) * ∫ u in (-1:ℝ)..u₁, g u :=
    igCen_integral_subst ha (by linarith [neg_abs_le u₁])
  have hsplit : ∫ u in (-1:ℝ)..u₁, g u =
      (∫ u in (-1:ℝ)..U (-w₀), g u) + ∫ u in U (-w₀)..u₁, g u :=
    (intervalIntegral.integral_add_adjacent_intervals (hgc.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _)).symm
  have hIcc1 : uIcc (-w₀) v₁ ⊆ Icc (-w₀) w₀ := by
    rw [uIcc_of_le hv₁.1]; exact Icc_subset_Icc le_rfl hv₁.2
  have hchange : ∫ u in U (-w₀)..u₁, g u =
      ∫ v in (-w₀)..v₁, Real.exp (-v^2/s^2) * deriv U v := by
    rw [← hUv₁, ← intervalIntegral.integral_comp_mul_deriv (fun x hx => (hU x (hIcc1 hx)).1)
      (fun x hx => (hU x (hIcc1 hx)).2.1.continuousWithinAt) hgc]
    refine intervalIntegral.integral_congr fun v hv => ?_
    obtain ⟨-, -, h1, h2, -, -⟩ := hU v (hIcc1 hv)
    simp only [Function.comp_apply, hg]
    rw [igCen_kernel a (by linarith), h2]
    congr 2
    rw [ha_def]; field_simp
  set h : ℝ → ℝ := fun v => deriv U v - 1 - 2/3*v with hh
  have hcU' : ContinuousOn (deriv U) (uIcc (-w₀) v₁) := fun x hx =>
    (hU x (hIcc1 hx)).2.1.continuousWithinAt
  have hdec : ∫ v in (-w₀)..v₁, Real.exp (-v^2/s^2) * deriv U v =
      (∫ v in (-w₀)..v₁, Real.exp (-v^2/s^2)) +
      2/3 * (∫ v in (-w₀)..v₁, v * Real.exp (-v^2/s^2)) +
      ∫ v in (-w₀)..v₁, Real.exp (-v^2/s^2) * h v := by
    have i1 : IntervalIntegrable (fun v => Real.exp (-v^2/s^2)) volume (-w₀) v₁ :=
      (by fun_prop : Continuous fun v : ℝ => Real.exp (-v^2/s^2)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun v => v * Real.exp (-v^2/s^2)) volume (-w₀) v₁ :=
      (by fun_prop : Continuous fun v : ℝ => v * Real.exp (-v^2/s^2)).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun v => Real.exp (-v^2/s^2) * h v) volume (-w₀) v₁ :=
      ContinuousOn.intervalIntegrable ((by fun_prop : Continuous fun v : ℝ =>
        Real.exp (-v^2/s^2)).continuousOn.mul ((hcU'.sub continuousOn_const).sub
          (by fun_prop)))
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add i1 (i2.const_mul _),
      ← intervalIntegral.integral_add (i1.add (i2.const_mul _)) i3]
    refine intervalIntegral.integral_congr fun v _ => ?_
    simp only [hh]; ring
  -- the pieces
  set J₁ := ∫ u in (-1:ℝ)..U (-w₀), g u with hJ₁
  set E := ∫ v in (-w₀)..v₁, Real.exp (-v^2/s^2) * h v with hE
  set π' := Real.sqrt π with hπ'
  have hπ'1 : 1 ≤ π' := by rw [hπ', Real.one_le_sqrt]; linarith [Real.pi_gt_three]
  have hπ'0 : 0 < π' := by linarith
  have hsπ1 : s ≤ s*π' := le_mul_of_one_le_right hs.le hπ'1
  have hsπ : s^2 ≤ s*π' := by rw [sq]; exact mul_le_mul_of_nonneg_left (hs1.trans hπ'1) hs.le
  have hs3π : s/(3*π') ≤ s := div_le_self hs.le (by linarith)
  set eM := Real.exp (-w₀^2/s^2) with heM
  set eT := Real.exp (-v₁^2/s^2) with heT
  set ey := Real.exp (-y^2) with hey
  set rT := TauCeti.Real.erf (v₁/s) with hrT
  set rM := TauCeti.Real.erf (w₀/s) with hrM
  set ry := TauCeti.Real.erf y with hry
  have hG₀ : ∫ v in (-w₀)..v₁, Real.exp (-v^2/s^2) = s * (π'/2) * (rT + rM) := by
    rw [igCen_integral_gauss hs, neg_div, TauCeti.Real.erf_neg]; ring
  have hG₁ : ∫ v in (-w₀)..v₁, v * Real.exp (-v^2/s^2) = s^2/2 * (eM - eT) := by
    rw [igCen_integral_mul_gauss hs, neg_sq]
  have hJ : ∫ u in (-1:ℝ)..u₁, g u = J₁ + s * (π'/2) * (rT + rM) + 2/3 * (s^2/2 * (eM - eT)) + E := by
    rw [hsplit, hchange, hdec, hG₀, hG₁]; ring
  -- bounds on the pieces
  have hUw : -1 < U (-w₀) := by linarith [(hU (-w₀) ⟨le_rfl, by linarith⟩).2.2.1]
  obtain ⟨hJ₁0, hJ₁1⟩ := igCen_J1 ha hUw hUm.le
  have hφw : igAsy_phi (U (-w₀)) = w₀^2/2 := by
    rw [(hU (-w₀) ⟨le_rfl, by linarith⟩).2.2.2.1, neg_sq]
  have haw : -a * (w₀^2/2) = -w₀^2/s^2 := by
    rw [ha_def]; field_simp
  rw [hφw, haw] at hJ₁1
  have hEb : |E| ≤ 6 * C₂ * s^3 :=
    igCen_err_bound hs hC₂ hv₁.1 fun v hv => (hU v (hIcc1 (by rw [uIcc_of_le hv₁.1]; exact hv))).2.2.2.2.2
  have hM : 0 < w₀/s := by positivity
  have hrM1 : 1 - rM ≤ eM / (w₀/s) := by
    have := igCen_one_sub_erf_le hM
    rwa [div_pow, ← neg_div] at this
  have hrM0 : 0 ≤ 1 - rM := by linarith [TauCeti.Real.erf_le_one (w₀/s)]
  have heM : eM ≤ 2 * s^4 / w₀^4 := by
    have := igCen_exp_neg_le (x := w₀^2/s^2) (by positivity)
    rw [heM, neg_div]; refine this.trans (le_of_eq ?_); field_simp
  have heM0 : 0 ≤ eM := (Real.exp_pos _).le
  -- Stirling
  have hst := igCen_stirling ha
  have hsa : Real.sqrt a / Real.sqrt (2*π) = 1/(s*π') := by
    rw [ha_def, Real.sqrt_div' _ (by positivity : (0:ℝ) ≤ s^2), Real.sqrt_sq hs.le,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), hπ']
    have : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
  rw [hsa] at hst
  set Φ := DLMF.Gamma.binetIntegral a with hΦ
  obtain ⟨hΦ0, hΦ1⟩ := DLMF.Gamma.binetIntegral_pos_lt ha
  have hΦs : 1/(12*a) = s^2/24 := by
    rw [ha_def]; field_simp; ring
  rw [hΦs] at hΦ1
  have hP : (∫ t in (0:ℝ)..a*(1+s*y), t^a * Real.exp (-t)) / Real.Gamma (a+1) =
      Real.exp (-Φ) * ((∫ u in (-1:ℝ)..u₁, g u) / (s*π')) := by
    rw [← hu₁, hsub, mul_div_right_comm, hst]; ring
  rw [hP]
  -- step A: the Gaussian main part `X`
  set K := (∫ u in (-1:ℝ)..u₁, g u) / (s*π') with hK
  set X := (1 + rT)/2 - s/(3*π') * eT with hX
  have hA : |K - X| ≤ (5/w₀^5 + 6*C₂) * s^2 := by
    have hid : K - X = J₁/(s*π') - (1 - rM)/2 + s/(3*π') * eM + E/(s*π') := by
      rw [hK, hJ, hX]; field_simp; ring
    rw [hid]
    have hw1' : w₀ ≤ 1 := by linarith
    have hs4 : s^4 ≤ s^2 := pow_le_pow_of_le_one hs.le hs1 (by norm_num)
    have hs3 : s^3 ≤ s^2 := pow_le_pow_of_le_one hs.le hs1 (by norm_num)
    have hs5 : s^5 ≤ s^2 := pow_le_pow_of_le_one hs.le hs1 (by norm_num)
    have hw45 : 1/w₀^4 ≤ 1/w₀^5 := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_of_le_one hw0.le hw1' (by norm_num)
    have t1 : |J₁/(s*π')| ≤ 2 * s^2 / w₀^4 := by
      rw [abs_div, abs_of_nonneg hJ₁0, abs_of_pos (by positivity)]
      rw [div_le_iff₀ (by positivity)]
      have : J₁ ≤ 2*s^4/w₀^4 := hJ₁1.trans heM
      calc J₁ ≤ 2*s^4/w₀^4 := this
        _ = 2*s^2/w₀^4 * (s^2) := by ring
        _ ≤ 2*s^2/w₀^4 * (s*π') := by gcongr
    have t2 : |(1 - rM)/2| ≤ s^2 / w₀^5 := by
      rw [abs_of_nonneg (by linarith)]
      have : eM / (w₀/s) ≤ 2*s^5/w₀^5 := by
        rw [div_div_eq_mul_div]
        calc eM * s / w₀ ≤ 2*s^4/w₀^4 * s / w₀ := by gcongr
          _ = 2*s^5/w₀^5 := by field_simp
      have h5 : 2*s^5/w₀^5 ≤ 2*s^2/w₀^5 := by gcongr
      have h6 := hrM1.trans (this.trans h5)
      calc (1 - rM)/2 ≤ (2*s^2/w₀^5)/2 := by gcongr
        _ = s^2/w₀^5 := by ring
    have t3 : |s/(3*π') * eM| ≤ 2 * s^2 / w₀^4 := by
      rw [abs_of_nonneg (by positivity)]
      calc s/(3*π') * eM ≤ s * (2 * s^4 / w₀^4) := by gcongr
        _ = 2 * s^5 / w₀^4 := by ring
        _ ≤ 2 * s^2 / w₀^4 := by gcongr
    have t4 : |E/(s*π')| ≤ 6 * C₂ * s^2 := by
      rw [abs_div, abs_of_pos (show 0 < s*π' by positivity), div_le_iff₀ (by positivity)]
      calc |E| ≤ 6 * C₂ * s^3 := hEb
        _ = 6 * C₂ * s^2 * s := by ring
        _ ≤ 6 * C₂ * s^2 * (s * π') := by gcongr
    have e1 : 2 * s^2 / w₀^4 = 2 * s^2 * (1/w₀^4) := by ring
    have e2 : s^2 / w₀^5 = s^2 * (1/w₀^5) := by ring
    have : 2 * s^2 * (1/w₀^4) ≤ 2 * s^2 * (1/w₀^5) := by gcongr
    calc _ ≤ |J₁/(s*π') - (1 - rM)/2 + s/(3*π') * eM| + |E/(s*π')| := abs_add_le _ _
      _ ≤ |J₁/(s*π') - (1 - rM)/2| + |s/(3*π') * eM| + |E/(s*π')| := by
          gcongr; exact abs_add_le _ _
      _ ≤ |J₁/(s*π')| + |(1 - rM)/2| + |s/(3*π') * eM| + |E/(s*π')| := by
          gcongr; exact abs_sub _ _
      _ ≤ 2*s^2*(1/w₀^5) + s^2*(1/w₀^5) + 2*s^2*(1/w₀^5) + 6*C₂*s^2 := by
          rw [e1] at t1 t3; rw [e2] at t2; linarith
      _ = _ := by ring
  -- step B: comparison of `X` with the target
  set tgt := (1 + ry)/2 - s/(3*π')*(1+y^2)*ey with htgt
  have hyB2 : |y|^2 ≤ B^2 := pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hey1 : ey ≤ 1 := by rw [hey]; exact Real.exp_le_one_iff.2 (neg_nonpos.2 (sq_nonneg y))
  have hey0 : 0 ≤ ey := (Real.exp_pos _).le
  have hB' : |X - tgt| ≤ (c₁^2 + c₁ + 6*B^3) * s^2 := by
    have herf := igCen_erf_sub (v₁/s) y
    rw [← hrT, ← hry, ← hey] at herf
    have hT : eT = Real.exp (-(v₁/s)^2) := by rw [heT, div_pow, neg_div]
    have hl := igCen_exp_neg_sq_lip y (v₁/s)
    rw [← hey, ← hT, abs_sub_comm y] at hl
    exact igCen_stepB hs hs1 hB hy hπ'1 hey0 hey1 herf hl (by rw [← hu₁]; exact hρ)
  -- step C: the Binet factor
  have hKt : |K - tgt| ≤ D * s^2 := by
    have := abs_sub_le K X tgt
    rw [hD]; linarith
  have htgtb : |tgt| ≤ 1 + (1 + B^2) := by
    rw [htgt]
    have h1 : |(1 + ry)/2| ≤ 1 := by
      rw [abs_le]; constructor <;>
        linarith [TauCeti.Real.erf_le_one y, TauCeti.Real.neg_one_lt_erf y]
    have h2 : |s/(3*π')*(1+y^2)*ey| ≤ 1 + B^2 := by
      rw [abs_of_nonneg (by positivity)]
      have h3 : s/(3*π') ≤ 1 := hs3π.trans hs1
      have h4 : y^2 ≤ B^2 := by rw [← sq_abs]; exact hyB2
      calc s/(3*π')*(1+y^2)*ey ≤ 1 * (1 + B^2) * 1 := by gcongr
        _ = 1 + B^2 := by ring
    exact (abs_sub _ _).trans (by linarith)
  have hKb : |K| ≤ 2 + B^2 + D := by
    have := abs_sub_abs_le_abs_sub K tgt
    have : D * s^2 ≤ D := by
      have : s^2 ≤ 1 := by nlinarith
      exact mul_le_of_le_one_right hD0 this
    linarith
  have hexp : |Real.exp (-Φ) - 1| ≤ s^2/24 := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [Real.exp_le_one_iff.2 (by linarith : -Φ ≤ 0)])]
    linarith [Real.add_one_le_exp (-Φ)]
  have hid : Real.exp (-Φ) * K - tgt = (Real.exp (-Φ) - 1) * K + (K - tgt) := by ring
  rw [hid]
  calc _ ≤ |(Real.exp (-Φ) - 1) * K| + |K - tgt| := abs_add_le _ _
    _ ≤ s^2/24 * (2 + B^2 + D) + D * s^2 := by
        rw [abs_mul]; gcongr
    _ = _ := by ring
/-- Uniform large positive parameter with bounded real central variable. -/
def gammaCentralFilter (B : ℝ) : Filter (ℝ × ℝ) :=
  comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.1 ∧ |p.2| ≤ B}

/-- normIncGammaP central expansion. Proof: Stirling with Binet's remainder, the saddle substitution
`φ(U(v)) = v²/2` with `U'(v) = 1 + 2v/3 + O(v²)`, and the Gaussian integral through `erf`
(`igCen_core`). -/
@[dlmf 8.11.E10]
theorem normIncGammaP_central_expansion {B : ℝ} (hB : 0 < B) :
    IsBigO (gammaCentralFilter B) (fun p : ℝ × ℝ => normIncGammaPContinued (p.1+1) (p.1+Real.sqrt (2*p.1)*p.2)-erfc (-p.2)/2+((Real.sqrt (2/(π*p.1))/3*(1+p.2^2)*Real.exp (-p.2^2) : ℝ) : ℂ)) (fun p => p.1⁻¹) := by
  obtain ⟨C, s₀, hs₀, -, hcore⟩ := igCen_core hB
  set s₁ := min s₀ (1/(2*B)) with hs₁
  have hs₁0 : 0 < s₁ := by positivity
  refine IsBigO.of_bound (2*C) ?_
  have hev : ∀ᶠ p : ℝ × ℝ in gammaCentralFilter B, 2/s₁^2 ≤ p.1 ∧ 0 < p.1 ∧ |p.2| ≤ B := by
    have h1 : ∀ᶠ p : ℝ × ℝ in gammaCentralFilter B, 2/s₁^2 ≤ p.1 :=
      (tendsto_comap.eventually (eventually_ge_atTop _)).filter_mono inf_le_left
    have h2 : ∀ᶠ p : ℝ × ℝ in gammaCentralFilter B, 0 < p.1 ∧ |p.2| ≤ B :=
      mem_inf_of_right (mem_principal_self _)
    exact h1.and h2
  filter_upwards [hev] with p ⟨hA, ha, hy⟩
  obtain ⟨a, y⟩ := p
  simp only at hA ha hy ⊢
  set s := Real.sqrt (2/a) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hss : s^2 = 2/a := Real.sq_sqrt (by positivity)
  have hsle : s ≤ s₁ := by
    rw [← Real.sqrt_sq hs₁0.le, hs]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ ha]; rw [div_le_iff₀ (by positivity)] at hA; linarith
  have hsy : s * |y| ≤ 1/2 := by
    have h1 : s ≤ 1/(2*B) := hsle.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [abs_nonneg y]
  have h2s : 2/s^2 = a := by rw [hss]; field_simp
  have hc := hcore s y hs0 (hsle.trans (min_le_left _ _)) hy
  rw [h2s] at hc
  have hx : (a:ℂ) + (Real.sqrt (2*a) : ℂ) * (y:ℂ) = ((a*(1+s*y) : ℝ) : ℂ) := by
    have : Real.sqrt (2*a) = a * s := by
      rw [hs, ← Real.sqrt_sq ha.le, ← Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
      congr 1; field_simp
    rw [this]; push_cast; ring
  have hxpos : 0 < a*(1+s*y) := by
    have : -(s*|y|) ≤ s*y := by rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_abs_le y) hs0.le
    have : 0 < 1 + s*y := by linarith
    positivity
  rw [hx, igCen_normIncGammaP_eq ha hxpos, show -(y:ℂ) = ((-y:ℝ):ℂ) by push_cast; ring,
    erfc_ofReal]
  have hsq : Real.sqrt (2/(π*a)) = s/Real.sqrt π := by
    rw [hs, ← Real.sqrt_div' _ Real.pi_pos.le]; congr 1; field_simp
  rw [hsq, TauCeti.Real.erfc_def, TauCeti.Real.erf_neg]
  have e : ((((∫ t in (0:ℝ)..a*(1+s*y), t^a * Real.exp (-t)) / Real.Gamma (a+1) : ℝ) : ℂ) -
      ((1 - -TauCeti.Real.erf y : ℝ) : ℂ)/2 +
      ((s/Real.sqrt π/3*(1+y^2)*Real.exp (-y^2) : ℝ) : ℂ)) =
      (((∫ t in (0:ℝ)..a*(1+s*y), t^a * Real.exp (-t)) / Real.Gamma (a+1) -
        ((1 + TauCeti.Real.erf y)/2 - s/(3*Real.sqrt π)*(1+y^2)*Real.exp (-y^2)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, norm_inv, Real.norm_eq_abs, abs_of_pos ha]
  calc _ ≤ C * s^2 := hc
    _ = 2*C*a⁻¹ := by rw [hss]; ring

/-- Identity under the stated parameter and domain assumptions: `IsBigO (gammaCentralFilter B)
(fun p : ℝ × ℝ => let x := p.1+Real.sqrt (2*p.1)*p.2; (x : ℂ)^(1-(p.1 : ℂ))*scIncGamma (1-p.1)
(-x)+Real.cos (π*p.1)-Real.sin (π*p.1)/π*(2*Real.sqrt π*dawsonF p.2+(2/3*Real.sqrt
(2*π/p.1)*(1-p.2^2) : ℝ))*Real.exp (p.2^2)) (fun p => p.1⁻¹)`. -/
@[dlmf 8.11.E11]
theorem scIncGamma_central_expansion {B : ℝ} (hB : 0 < B) :
    IsBigO (gammaCentralFilter B) (fun p : ℝ × ℝ => let x := p.1+Real.sqrt (2*p.1)*p.2; (x : ℂ)^(1-(p.1 : ℂ))*scIncGamma (1-p.1) (-x)+Real.cos (π*p.1)-Real.sin (π*p.1)/π*(2*Real.sqrt π*dawsonF p.2+(2/3*Real.sqrt (2*π/p.1)*(1-p.2^2) : ℝ))*Real.exp (p.2^2)) (fun p => p.1⁻¹) := by
  sorry

end DLMF.Confluent

end
