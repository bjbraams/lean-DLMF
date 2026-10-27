/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.Basic

/-!
# Real-variable tools for the incomplete Gamma inequalities, DLMF §8.10

* `igBd_pos_of_leftProp`: a function vanishing at `0` and at `∞` whose derivative has the sign
  pattern `+ … + − … −` (positivity of `H'` propagates to the left) is positive on `(0,∞)`;
  `igBd_rightProp`, `igBd_neg_of_deriv_pos` are companion sign lemmas.
* `igBd_Gamma_lt_two_lower_self`: `Γ(a) < 2γ(a,a)` for real `a > 0` (median below the mean of
  the Gamma law), by the reflection `t ↦ a²/t`.
* `igBd_two_lower_mode_lt_Gamma`: `2γ(a,a-1) < Γ(a)` for `a > 1` (median above the mode), by
  the reflection `t ↦ 2(a-1)-t`.
* `igBd_regGamma_lt_pow`, `igBd_pow_lt_regGamma` with `igBd_prop_*`: Alzer's bounds
  `(1-e^{-αx})^a < P(a,x) < (1-e^{-βx})^a` (DLMF 8.10.11), via the sign of the logarithmic
  derivative ratio `igBd_k` and the strict convexity of `ℓ(u) = log((1-e^{-u})/u)`.
* `igBd_upper_gt`, `igBd_upper_lt`: the bounds of DLMF 8.10.10 in the form
  `e^{-x}((x+2)^a-x^a)/(2a) < Γ(a,x) < e^{-x}((x+c)^a-x^a)/(ac)`, `c = Γ(1+a)^{1/(a-1)}`;
  the derivative of the difference is `e^{-x} x^a λ^{-2} Q(λ/x)` with an explicit `igBd_Q`
  whose second derivative changes sign once.
* `igBd_normIncGammaQ_re`, `igBd_normIncGammaP_re`: the continued `P`, `Q` at real `a > 0`,
  `x ≥ 0` in terms of TauCeti's `lowerIncompleteGamma`.

Lower incomplete Gamma API from TauCeti (`TauCeti.lowerIncompleteGamma`).
-/

@[expose] public noncomputable section
open Complex Filter Set DLMF.Hypergeometric DLMF
open scoped Topology
namespace DLMF.Confluent

open DLMF.Statistical


/-- A function vanishing at `0` and at `∞`, whose derivative's positivity propagates to the
left, is positive on `(0,∞)`. -/
theorem igBd_pos_of_leftProp {H H' : ℝ → ℝ} (hc : ContinuousOn H (Ici 0)) (h0 : H 0 = 0)
    (hlim : Tendsto H atTop (𝓝 0)) (hd : ∀ x, 0 < x → HasDerivAt H (H' x) x)
    (hprop : ∀ x y, 0 < x → x < y → 0 ≤ H' y → 0 < H' x) {x : ℝ} (hx : 0 < x) : 0 < H x := by
  by_cases hA : ∃ y, x < y ∧ 0 ≤ H' y
  · obtain ⟨y, hxy, hy⟩ := hA
    have hm : StrictMonoOn H (Icc 0 y) := strictMonoOn_of_deriv_pos (convex_Icc 0 y)
      (hc.mono Icc_subset_Ici_self) (fun t ht => by
        rw [interior_Icc] at ht
        rw [(hd t ht.1).deriv]; exact hprop t y ht.1 ht.2 hy)
    have := hm ⟨le_rfl, (hx.trans hxy).le⟩ ⟨hx.le, hxy.le⟩ hx
    rwa [h0] at this
  · push Not at hA
    have ha : StrictAntiOn H (Ici x) := strictAntiOn_of_deriv_neg (convex_Ici x)
      (hc.mono (Ici_subset_Ici.mpr hx.le)) (fun t ht => by
        rw [interior_Ici] at ht
        rw [(hd t (hx.trans ht)).deriv]; exact hA t ht)
    have h1 : 0 ≤ H (x+1) := by
      refine le_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop (x+1)] with t ht
      exact ha.antitoneOn (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith)) ht
    exact h1.trans_lt (ha (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by linarith)) (by linarith))

/-- If `F(0) = 0` and nonnegativity of `F'` propagates strictly to the right, so does that of `F`. -/
theorem igBd_rightProp {F F' : ℝ → ℝ} (hc : ContinuousOn F (Ici 0)) (h0 : F 0 = 0)
    (hd : ∀ w, 0 < w → HasDerivAt F (F' w) w)
    (hprop : ∀ v w, 0 < v → v < w → 0 ≤ F' v → 0 < F' w) :
    ∀ v w, 0 < v → v < w → 0 ≤ F v → 0 < F w := by
  intro v w hv hvw hFv
  have hex : ∃ u, 0 < u ∧ u < v ∧ 0 ≤ F' u := by
    by_contra hne; push Not at hne
    have ha : StrictAntiOn F (Icc 0 v) := strictAntiOn_of_deriv_neg (convex_Icc 0 v)
      (hc.mono Icc_subset_Ici_self)
      (fun t ht => by rw [interior_Icc] at ht; rw [(hd t ht.1).deriv]; exact hne t ht.1 ht.2)
    have := ha ⟨le_rfl, hv.le⟩ ⟨hv.le, le_rfl⟩ hv
    rw [h0] at this; linarith
  obtain ⟨u, hu, huv, hFu⟩ := hex
  have hm : StrictMonoOn F (Icc v w) := strictMonoOn_of_deriv_pos (convex_Icc v w)
    (hc.mono (fun t ht => mem_Ici.mpr (hv.le.trans ht.1)))
    (fun t ht => by
      rw [interior_Icc] at ht
      rw [(hd t (hv.trans ht.1)).deriv]; exact hprop u t hu (huv.trans ht.1) hFu)
  have := hm ⟨le_rfl, hvw.le⟩ ⟨hvw.le, le_rfl⟩ hvw
  linarith

/-- A strictly increasing function on `(0,∞)` tending to `0` at `∞` is negative. -/
theorem igBd_neg_of_deriv_pos {H H' : ℝ → ℝ} (hlim : Tendsto H atTop (𝓝 0))
    (hd : ∀ x, 0 < x → HasDerivAt H (H' x) x) (hpos : ∀ x, 0 < x → 0 < H' x)
    {x : ℝ} (hx : 0 < x) : H x < 0 := by
  have hm : StrictMonoOn H (Ici x) := strictMonoOn_of_deriv_pos (convex_Ici x)
    (fun t ht => (hd t (hx.trans_le ht)).continuousAt.continuousWithinAt) (fun t ht => by
      rw [interior_Ici] at ht
      rw [(hd t (hx.trans ht)).deriv]; exact hpos t (hx.trans ht))
  have h1 : H (x+1) ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (x+1)] with t ht
    exact hm.monotoneOn (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith)) ht
  exact (hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by linarith)) (by linarith)).trans_le h1

/-- `2 log s < s - 1/s` for `s > 1`. -/
theorem igBd_two_log_lt {s : ℝ} (hs : 1 < s) : 2 * Real.log s < s - s⁻¹ := by
  have := Real.self_lt_sinh_iff.mpr (Real.log_pos hs)
  rw [Real.sinh_log (by linarith)] at this
  linarith

/-- Pointwise comparison of the Gamma integrand under `t ↦ a²/t`. -/
theorem igBd_integrand_reflect {a s : ℝ} (ha : 0 < a) (hs : 1 < s) :
    (a*s)^(a-1)*Real.exp (-(a*s))*a < (a/s)^(a-1)*Real.exp (-(a/s))*(a/s^2) := by
  have hs0 : 0 < s := by linarith
  have hl := igBd_two_log_lt hs
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity),
    Real.log_mul ha.ne' hs0.ne', Real.log_div ha.ne' hs0.ne', ← Real.exp_add, ← Real.exp_add,
    div_eq_mul_inv a (s^2), show (s^2)⁻¹ = Real.exp (-(2*Real.log s)) by
      rw [Real.exp_neg, ← Real.log_rpow hs0, Real.exp_log (by positivity)]; norm_num]
  rw [show ∀ u v : ℝ, Real.exp u * (a * Real.exp v) = Real.exp (u+v) * a from
    fun u v => by rw [Real.exp_add]; ring]
  refine mul_lt_mul_of_pos_right (Real.exp_lt_exp.mpr ?_) ha
  have : a * (s - s⁻¹) > a * (2 * Real.log s) := mul_lt_mul_of_pos_left hl ha
  rw [div_eq_mul_inv]
  nlinarith


/-- `Γ(a) < 2γ(a,a)` for `a > 0`: the median of the Gamma(a) law is below its mean. -/
theorem igBd_Gamma_lt_two_lower_self {a : ℝ} (ha : 0 < a) :
    Real.Gamma a < 2 * TauCeti.lowerIncompleteGamma a a := by
  set L := TauCeti.lowerIncompleteGamma a with hLdef
  have hLc : Continuous L := TauCeti.continuous_lowerIncompleteGamma a
  set Φ : ℝ → ℝ := fun s => 2 * L a - L (a * s⁻¹) - L (a * s) with hΦ
  have hd : ∀ s, 1 < s → HasDerivAt Φ ((a/s)^(a-1)*Real.exp (-(a/s))*(a/s^2) -
      (a*s)^(a-1)*Real.exp (-(a*s))*a) s := by
    intro s hs
    have hs0 : 0 < s := by linarith
    have h1 := (TauCeti.hasDerivAt_lowerIncompleteGamma ha (show 0 < a * s⁻¹ by positivity)).comp s
      ((hasDerivAt_inv hs0.ne').const_mul a)
    have h2 := (TauCeti.hasDerivAt_lowerIncompleteGamma ha (show 0 < a * s by positivity)).comp s
      ((hasDerivAt_id s).const_mul a)
    convert ((hasDerivAt_const s (2 * L a)).sub h1).sub h2 using 1
    · rfl
    · rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  have hpos : ∀ s, 1 < s → 0 < (a/s)^(a-1)*Real.exp (-(a/s))*(a/s^2) -
      (a*s)^(a-1)*Real.exp (-(a*s))*a := fun s hs => sub_pos.mpr (igBd_integrand_reflect ha hs)
  have hcont : ContinuousOn Φ (Ici 1) := by
    refine ContinuousOn.sub (ContinuousOn.sub continuousOn_const ?_)
      (hLc.comp (continuous_const.mul continuous_id)).continuousOn
    exact hLc.comp_continuousOn (continuousOn_const.mul (continuousOn_inv₀.mono fun t ht =>
      (show (0:ℝ) < t from lt_of_lt_of_le one_pos ht).ne'))
  have hm : StrictMonoOn Φ (Ici 1) := strictMonoOn_of_deriv_pos (convex_Ici 1) hcont
    (fun t ht => by rw [interior_Ici] at ht; rw [(hd t ht).deriv]; exact hpos t ht)
  have h1 : Φ 1 = 0 := by simp [Φ]; ring
  have h2 : 0 < Φ 2 := h1 ▸ hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr one_le_two) one_lt_two
  have hlim : Tendsto Φ atTop (𝓝 (2 * L a - L (a * 0) - Real.Gamma a)) := by
    refine (tendsto_const_nhds.sub ((hLc.tendsto _).comp
      (tendsto_inv_atTop_zero.const_mul a))).sub ?_
    exact (TauCeti.tendsto_lowerIncompleteGamma_atTop ha).comp
      (tendsto_id.const_mul_atTop ha)
  have hle : Φ 2 ≤ 2 * L a - L (a * 0) - Real.Gamma a := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop 2] with s hs
    exact hm.monotoneOn (mem_Ici.mpr one_le_two) (mem_Ici.mpr (by linarith)) hs
  rw [mul_zero, hLdef, TauCeti.lowerIncompleteGamma_eq_zero_of_nonpos_right a le_rfl] at hle
  linarith

/-- For `0 < s < m`, `m log((m+s)/(m-s)) > 2s`. -/
theorem igBd_log_ratio_gt {m s : ℝ} (hs : 0 < s) (hsm : s < m) :
    2 * s < m * Real.log (m + s) - m * Real.log (m - s) := by
  have hm : 0 < m := hs.trans hsm
  set g : ℝ → ℝ := fun s => m * Real.log (m + s) - m * Real.log (m - s) - 2 * s
  have hd : ∀ t ∈ Ioo 0 m, HasDerivAt g (m * (1 / (m + t)) - m * (-1 / (m - t)) - 2) t := by
    intro t ht
    have h1 := (((hasDerivAt_id t).const_add m).log (by simp; linarith [ht.1])).const_mul m
    have h2 := (((hasDerivAt_id t).const_sub m).log (by simp; linarith [ht.2])).const_mul m
    exact (h1.sub h2).sub ((hasDerivAt_id t).const_mul 2) |>.congr_deriv (by simp)
  have hmono : StrictMonoOn g (Ico 0 m) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico 0 m) ?_ ?_
    · intro t ht
      have h1 : m + t ≠ 0 := by linarith [ht.1]
      have h2 : m - t ≠ 0 := by linarith [ht.2]
      exact ((continuousAt_const.mul ((continuousAt_const.add continuousAt_id).log h1)).sub
        (continuousAt_const.mul ((continuousAt_const.sub continuousAt_id).log h2))).sub
        (continuousAt_const.mul continuousAt_id) |>.continuousWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      rw [(hd t ht).deriv]
      have hp : 0 < m + t := by linarith [ht.1]
      have hq : 0 < m - t := by linarith [ht.2]
      have : 2 < m / (m + t) + m / (m - t) := by
        rw [div_add_div _ _ hp.ne' hq.ne', lt_div_iff₀ (mul_pos hp hq)]; nlinarith [ht.1]
      have e : m * (1 / (m + t)) - m * (-1 / (m - t)) - 2 = m / (m + t) + m / (m - t) - 2 := by
        ring
      linarith
  have := hmono (mem_Ico.mpr ⟨le_rfl, hm⟩) (mem_Ico.mpr ⟨hs.le, hsm⟩) hs
  simp only [g, add_zero, sub_zero, mul_zero] at this
  linarith

/-- `2γ(a,a-1) < Γ(a)` for `a > 1`: the median of the Gamma(a) law exceeds its mode. -/
theorem igBd_two_lower_mode_lt_Gamma {a : ℝ} (ha : 1 < a) :
    2 * TauCeti.lowerIncompleteGamma a (a-1) < Real.Gamma a := by
  have ha0 : 0 < a := by linarith
  set m := a - 1 with hmdef
  have hm : 0 < m := by linarith
  set L := TauCeti.lowerIncompleteGamma a with hLdef
  have hLc : Continuous L := TauCeti.continuous_lowerIncompleteGamma a
  have hpt : ∀ s, 0 < s → s < m →
      (m-s)^(a-1)*Real.exp (-(m-s)) < (m+s)^(a-1)*Real.exp (-(m+s)) := by
    intro s hs hsm
    have hl := igBd_log_ratio_gt hs hsm
    rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos (by linarith), ← Real.exp_add,
      ← Real.exp_add, Real.exp_lt_exp, ← hmdef]
    linarith
  set Φ : ℝ → ℝ := fun s => L (m + s) - 2 * L m + L (m - s) with hΦ
  have hd : ∀ s ∈ Ioo 0 m, HasDerivAt Φ ((m+s)^(a-1)*Real.exp (-(m+s)) -
      (m-s)^(a-1)*Real.exp (-(m-s))) s := by
    intro s hs
    have h1 := (TauCeti.hasDerivAt_lowerIncompleteGamma ha0 (show 0 < m + s by linarith [hs.1])).comp s
      ((hasDerivAt_id s).const_add m)
    have h2 := (TauCeti.hasDerivAt_lowerIncompleteGamma ha0 (show 0 < m - s by linarith [hs.2])).comp s
      ((hasDerivAt_id s).const_sub m)
    convert (h1.sub_const (2 * L m)).add h2 using 1
    · rfl
    · ring
  have hmono : StrictMonoOn Φ (Icc 0 m) := strictMonoOn_of_deriv_pos (convex_Icc 0 m)
    ((hLc.comp (continuous_const.add continuous_id)).sub continuous_const |>.add
      (hLc.comp (continuous_const.sub continuous_id))).continuousOn
    (fun t ht => by
      rw [interior_Icc] at ht
      rw [(hd t ht).deriv]; exact sub_pos.mpr (hpt t ht.1 ht.2))
  have := hmono (mem_Icc.mpr ⟨le_rfl, hm.le⟩) (mem_Icc.mpr ⟨hm.le, le_rfl⟩) hm
  simp only [Φ, add_zero, sub_zero, sub_self] at this
  rw [hLdef, TauCeti.lowerIncompleteGamma_eq_zero_of_nonpos_right a le_rfl] at this
  have hG := TauCeti.lowerIncompleteGamma_le_Gamma ha0 (m + m)
  linarith

/-! ### DLMF 8.10.10: Gautschi-type bounds for `Γ(a,x)`, `0 < a < 1` -/

/-- `Q(w) = w(1+w)^{a-1} + (λ-1)w - (λ/a)((1+w)^a-1)`, the sign function for DLMF 8.10.10. -/
def igBd_Q (a l w : ℝ) : ℝ := w*(1+w)^(a-1) + (l-1)*w - (l/a)*((1+w)^a - 1)

/-- The derivative of `igBd_Q`. -/
def igBd_dQ (a l w : ℝ) : ℝ := (1-l)*(1+w)^(a-1) + (l-1) + (a-1)*w*(1+w)^(a-2)

/-- The second derivative of `igBd_Q`. -/
def igBd_ddQ (a l w : ℝ) : ℝ := (1-a)*(1+w)^(a-3)*((l-2) + (l-a)*w)

/-- Derivative of `igBd_Q`. -/
theorem igBd_Q_hasDerivAt {a l w : ℝ} (ha : 0 < a) (hw : 0 < w) :
    HasDerivAt (igBd_Q a l) (igBd_dQ a l w) w := by
  have h1 : (1:ℝ) + w ≠ 0 := by linarith
  have hp : HasDerivAt (fun w : ℝ => 1 + w) 1 w := (hasDerivAt_id w).const_add 1
  have e1 := hp.rpow_const (p := a-1) (Or.inl h1)
  have e2 := hp.rpow_const (p := a) (Or.inl h1)
  have := (((hasDerivAt_id w).mul e1).add ((hasDerivAt_id w).const_mul (l-1))).sub
    ((e2.sub_const 1).const_mul (l/a))
  convert this using 1
  · funext y; simp [igBd_Q]
  have h2 : (1+w)^(a-1) = (1+w)^(a-2)*(1+w) := by
    rw [← Real.rpow_add_one h1]; ring_nf
  simp only [igBd_dQ, id, one_mul, mul_one]
  rw [show a - 1 - 1 = a - 2 by ring]
  field_simp
  ring

/-- Derivative of `igBd_dQ`. -/
theorem igBd_dQ_hasDerivAt {a l w : ℝ} (hw : 0 < w) :
    HasDerivAt (igBd_dQ a l) (igBd_ddQ a l w) w := by
  have h1 : (1:ℝ) + w ≠ 0 := by linarith
  have hp : HasDerivAt (fun w : ℝ => 1 + w) 1 w := (hasDerivAt_id w).const_add 1
  have e1 := hp.rpow_const (p := a-1) (Or.inl h1)
  have e2 := hp.rpow_const (p := a-2) (Or.inl h1)
  have := ((e1.const_mul (1-l)).add_const (l-1)).add (((hasDerivAt_id w).const_mul (a-1)).mul e2)
  convert this using 1
  · funext y; simp [igBd_dQ]
  have h2 : (1+w)^(a-2) = (1+w)^(a-3)*(1+w) := by
    rw [← Real.rpow_add_one h1]; ring_nf
  simp only [igBd_ddQ, id, one_mul, mul_one]
  rw [show a - 1 - 1 = a - 2 by ring, show a - 2 - 1 = a - 3 by ring, h2]
  ring

/-- Continuity of `igBd_Q` on `[0,∞)`. -/
theorem igBd_Q_continuousOn {a l : ℝ} : ContinuousOn (igBd_Q a l) (Ici 0) := by
  intro w hw
  have h1 : (1:ℝ) + w ≠ 0 := by have := mem_Ici.mp hw; linarith
  refine ContinuousAt.continuousWithinAt ?_
  unfold igBd_Q
  have hc : ContinuousAt (fun w : ℝ => 1 + w) w := continuousAt_const.add continuousAt_id
  exact ((continuousAt_id.mul (hc.rpow_const (Or.inl h1))).add (continuousAt_const.mul
    continuousAt_id)).sub (continuousAt_const.mul ((hc.rpow_const (Or.inl h1)).sub
    continuousAt_const))

/-- Continuity of `igBd_dQ` on `[0,∞)`. -/
theorem igBd_dQ_continuousOn {a l : ℝ} : ContinuousOn (igBd_dQ a l) (Ici 0) := by
  intro w hw
  have h1 : (1:ℝ) + w ≠ 0 := by have := mem_Ici.mp hw; linarith
  refine ContinuousAt.continuousWithinAt ?_
  unfold igBd_dQ
  have hc : ContinuousAt (fun w : ℝ => 1 + w) w := continuousAt_const.add continuousAt_id
  exact ((continuousAt_const.mul (hc.rpow_const (Or.inl h1))).add continuousAt_const).add
    ((continuousAt_const.mul continuousAt_id).mul (hc.rpow_const (Or.inl h1)))

/-- `Q(0) = 0`. -/
theorem igBd_Q_zero {a l : ℝ} : igBd_Q a l 0 = 0 := by simp [igBd_Q]

/-- `Q'(0) = 0`. -/
theorem igBd_dQ_zero {a l : ℝ} : igBd_dQ a l 0 = 0 := by simp [igBd_dQ]

/-- For `0 < a < 1` and `a < λ`, nonnegativity of `Q` propagates to the right. -/
theorem igBd_Q_rightProp {a l : ℝ} (ha : 0 < a) (ha1 : a < 1) (hl : a < l) :
    ∀ v w, 0 < v → v < w → 0 ≤ igBd_Q a l v → 0 < igBd_Q a l w := by
  have hdd : ∀ v w, 0 < v → v < w → 0 ≤ igBd_ddQ a l v → 0 < igBd_ddQ a l w := by
    intro v w hv hvw h
    have hfv : 0 < (1-a)*(1+v)^(a-3) := mul_pos (by linarith) (Real.rpow_pos_of_pos (by linarith) _)
    have hfw : 0 < (1-a)*(1+w)^(a-3) := mul_pos (by linarith) (Real.rpow_pos_of_pos (by linarith) _)
    unfold igBd_ddQ at h ⊢
    have := nonneg_of_mul_nonneg_right (by linarith : 0 ≤ (1-a)*(1+v)^(a-3) * ((l-2) + (l-a)*v))
      hfv
    exact mul_pos hfw (by nlinarith)
  have hd := igBd_rightProp igBd_dQ_continuousOn igBd_dQ_zero (fun w hw => igBd_dQ_hasDerivAt hw) hdd
  exact igBd_rightProp igBd_Q_continuousOn igBd_Q_zero (fun w hw => igBd_Q_hasDerivAt ha hw) hd

/-- A function vanishing at `0` with positive derivative on `(0,∞)` is positive there. -/
theorem igBd_pos_of_deriv_pos {F F' : ℝ → ℝ} (hc : ContinuousOn F (Ici 0)) (h0 : F 0 = 0)
    (hd : ∀ w, 0 < w → HasDerivAt F (F' w) w) (hp : ∀ w, 0 < w → 0 < F' w) {w : ℝ}
    (hw : 0 < w) : 0 < F w := by
  have hm : StrictMonoOn F (Ici 0) := strictMonoOn_of_deriv_pos (convex_Ici 0) hc
    (fun t ht => by rw [interior_Ici] at ht; rw [(hd t ht).deriv]; exact hp t ht)
  have := hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr hw.le) hw
  rwa [h0] at this

/-- For `λ = 2` and `0 < a < 1`, `Q > 0` on `(0,∞)` (the trapezoidal rule for `t^{a-1}`). -/
theorem igBd_Q_two_pos {a w : ℝ} (ha : 0 < a) (ha1 : a < 1) (hw : 0 < w) : 0 < igBd_Q a 2 w := by
  have hdd : ∀ w, 0 < w → 0 < igBd_ddQ a 2 w := fun w hw => by
    unfold igBd_ddQ
    have : 0 < (1-a)*(1+w)^(a-3) := mul_pos (by linarith) (Real.rpow_pos_of_pos (by linarith) _)
    exact mul_pos this (by nlinarith)
  have hd : ∀ w, 0 < w → 0 < igBd_dQ a 2 w := fun w hw =>
    igBd_pos_of_deriv_pos igBd_dQ_continuousOn igBd_dQ_zero (fun w hw => igBd_dQ_hasDerivAt hw)
      hdd hw
  exact igBd_pos_of_deriv_pos igBd_Q_continuousOn igBd_Q_zero
    (fun w hw => igBd_Q_hasDerivAt ha hw) hd hw

/-- `e^{-x}((x+λ)^a-x^a)/(aλ) - Γ(a,x)`, the comparison function for DLMF 8.10.10. -/
def igBd_G (a l x : ℝ) : ℝ :=
  Real.exp (-x) * (((x+l)^a - x^a)/(a*l)) - (Real.Gamma a - TauCeti.lowerIncompleteGamma a x)

/-- `G' = e^{-x} x^a λ^{-2} Q(λ/x)`. -/
theorem igBd_G_hasDerivAt {a l x : ℝ} (ha : 0 < a) (hl : 0 < l) (hx : 0 < x) :
    HasDerivAt (igBd_G a l) (Real.exp (-x) * x^a / l^2 * igBd_Q a l (l/x)) x := by
  have hxl : 0 < x + l := by linarith
  have e1 := ((hasDerivAt_id x).add_const l).rpow_const (p := a) (Or.inl hxl.ne')
  have e2 := Real.hasDerivAt_rpow_const (x := x) (p := a) (Or.inl hx.ne')
  have e3 := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have := (e3.mul ((e1.sub e2).div_const (a*l))).sub
    ((TauCeti.hasDerivAt_lowerIncompleteGamma ha hx).const_sub (Real.Gamma a))
  refine this.congr_deriv ?_
  simp only [id, one_mul, Function.comp_apply, mul_neg, mul_one, sub_neg_eq_add, Pi.sub_apply]
  have hX : x^a = x^(a-1)*x := by rw [← Real.rpow_add_one hx.ne']; ring_nf
  have hY : (x+l)^a = (x+l)^(a-1)*(x+l) := by rw [← Real.rpow_add_one hxl.ne']; ring_nf
  have h1 : 1 + l/x = (x+l)/x := by field_simp
  rw [igBd_Q, h1, Real.div_rpow hxl.le hx.le, Real.div_rpow hxl.le hx.le, hX, hY]
  have : 0 < x^(a-1) := Real.rpow_pos_of_pos hx _
  have : 0 < (x+l)^(a-1) := Real.rpow_pos_of_pos hxl _
  field_simp
  ring

/-- Continuity of `igBd_G`. -/
theorem igBd_G_continuous {a l : ℝ} (ha : 0 < a) : Continuous (igBd_G a l) := by
  unfold igBd_G
  exact (Real.continuous_exp.comp continuous_neg).mul
    ((((continuous_id.add continuous_const).rpow_const (fun _ => Or.inr ha.le)).sub
      (Real.continuous_rpow_const ha.le)).div_const _) |>.sub
    (continuous_const.sub (TauCeti.continuous_lowerIncompleteGamma a))

/-- Value of `igBd_G` at `0`. -/
theorem igBd_G_zero {a l : ℝ} (ha : 0 < a) : igBd_G a l 0 = l^a/(a*l) - Real.Gamma a := by
  simp [igBd_G, Real.zero_rpow ha.ne', TauCeti.lowerIncompleteGamma_eq_zero_of_nonpos_right]

/-- `igBd_G a λ x → 0` as `x → ∞` (`a ≤ 1`). -/
theorem igBd_G_tendsto {a l : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hl : 0 < l) :
    Tendsto (igBd_G a l) atTop (𝓝 0) := by
  have hf : Tendsto (fun x : ℝ => Real.exp (-x) * (((x+l)^a - x^a)/(a*l))) atTop (𝓝 0) := by
    have hup : Tendsto (fun x : ℝ => (x^1 * Real.exp (-x) + l * Real.exp (-x)) / (a*l)) atTop
        (𝓝 0) := by
      have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).add
        (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul l)).div_const (a*l)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with x hx
      have : x^a ≤ (x+l)^a := Real.rpow_le_rpow hx (by linarith) ha.le
      have : 0 ≤ ((x+l)^a - x^a)/(a*l) := div_nonneg (by linarith) (by positivity)
      positivity
    · filter_upwards [eventually_ge_atTop 1] with x hx
      have h1 : (x+l)^a ≤ x + l := by
        calc (x+l)^a ≤ (x+l)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) ha1
          _ = x + l := Real.rpow_one _
      have h2 : 0 ≤ x^a := Real.rpow_nonneg (by linarith) _
      rw [pow_one, mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
      have : 0 < Real.exp (-x) := Real.exp_pos _
      nlinarith
  have := hf.sub ((tendsto_const_nhds (x := Real.Gamma a)).sub
    (TauCeti.tendsto_lowerIncompleteGamma_atTop ha))
  rw [sub_self, sub_zero] at this
  exact this

/-- DLMF 8.10.10, lower bound in real form: `e^{-x}((x+2)^a-x^a)/(2a) < Γ(a,x)` for
`0 < a < 1`, `x > 0`. -/
theorem igBd_upper_gt {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : 0 < x) :
    Real.exp (-x) * (((x+2)^a - x^a)/(a*2)) < Real.Gamma a - TauCeti.lowerIncompleteGamma a x := by
  have := igBd_neg_of_deriv_pos (igBd_G_tendsto ha ha1.le two_pos)
    (fun x hx => igBd_G_hasDerivAt ha two_pos hx)
    (fun x hx => mul_pos (by positivity) (igBd_Q_two_pos ha ha1 (by positivity))) hx
  unfold igBd_G at this
  linarith

/-- `Γ(1+a) ≤ 1` for `0 ≤ a ≤ 1`, by convexity of `Γ`. -/
theorem igBd_Gamma_one_add_le_one {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) : Real.Gamma (1+a) ≤ 1 := by
  have := Real.convexOn_Gamma.2 (show (1:ℝ) ∈ Ioi 0 by norm_num) (show (2:ℝ) ∈ Ioi 0 by norm_num)
    (show 0 ≤ 1 - a by linarith) ha (by ring)
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at this
  convert this using 2 <;> ring

/-- DLMF 8.10.10, upper bound in real form: `Γ(a,x) < e^{-x}((x+c)^a-x^a)/(ac)` for
`0 < a < 1`, `x > 0`, `c = Γ(1+a)^{1/(a-1)}`. -/
theorem igBd_upper_lt {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : 0 < x) :
    Real.Gamma a - TauCeti.lowerIncompleteGamma a x <
      Real.exp (-x) * (((x+Real.Gamma (1+a)^(1/(a-1)))^a - x^a)/(a*Real.Gamma (1+a)^(1/(a-1)))) := by
  set c := Real.Gamma (1+a)^(1/(a-1)) with hc
  have hG := Real.Gamma_pos_of_pos (show 0 < 1 + a by linarith)
  have hc1 : 1 ≤ c := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hG
    (igBd_Gamma_one_add_le_one ha.le ha1.le) (by
      rw [one_div]; exact inv_nonpos.mpr (by linarith))
  have hc0 : 0 < c := by linarith
  have hcpow : c^(a-1) = Real.Gamma (1+a) := by
    rw [hc, ← Real.rpow_mul hG.le, one_div, inv_mul_cancel₀ (by linarith : a - 1 ≠ 0),
      Real.rpow_one]
  have h0 : igBd_G a c 0 = 0 := by
    rw [igBd_G_zero ha, show c^a = c^(a-1)*c by rw [← Real.rpow_add_one hc0.ne']; ring_nf, hcpow,
      add_comm 1 a, Real.Gamma_add_one ha.ne']
    field_simp
    ring
  have := igBd_pos_of_leftProp (igBd_G_continuous ha).continuousOn h0
    (igBd_G_tendsto ha ha1.le hc0) (fun x hx => igBd_G_hasDerivAt ha hc0 hx)
    (fun x y hx hxy hy => by
      have hy0 := hx.trans hxy
      have hpos : ∀ t : ℝ, 0 < t → 0 < Real.exp (-t) * t^a / c^2 := fun t ht => by positivity
      have hQy : 0 ≤ igBd_Q a c (c/y) := nonneg_of_mul_nonneg_right hy (hpos y hy0)
      exact mul_pos (hpos x hx) (igBd_Q_rightProp ha ha1 (by linarith) (c/y) (c/x)
        (by positivity) (div_lt_div_of_pos_left hc0 hx hxy) hQy)) hx
  unfold igBd_G at this
  linarith

/-- The continued `P(a,x)` at real `a > 0`, `x ≥ 0` is TauCeti's regularized lower Gamma. -/
theorem igBd_normIncGammaP_ofReal {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) :
    normIncGammaPContinued a x = ((TauCeti.lowerIncompleteGamma a x / Real.Gamma a : ℝ) : ℂ) := by
  rcases hx.eq_or_lt with h0 | h0
  · subst h0
    rw [TauCeti.lowerIncompleteGamma_eq_zero_of_nonpos_right a le_rfl, normIncGammaPContinued,
      ofReal_zero, zero_cpow (ofReal_ne_zero.mpr ha.ne')]
    simp
  · have ha' : ∀ n : ℕ, (a:ℂ) ≠ -n := fun n h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    rw [normIncGammaPContinued_eq ha', normIncGammaP, lowerIncGamma_ofReal ha h0,
      Complex.Gamma_ofReal]
    push_cast; rfl

/-- Real part of the continued `P(a,x)` at real `a > 0`, `x ≥ 0`. -/
theorem igBd_normIncGammaP_re {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) :
    (normIncGammaPContinued a x).re = TauCeti.regularizedGamma a x := by
  rw [igBd_normIncGammaP_ofReal ha hx, ofReal_re, TauCeti.regularizedGamma_eq_div]

/-- Real part of the continued `Q(a,x)` at real `a > 0`, `x ≥ 0`. -/
theorem igBd_normIncGammaQ_re {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) :
    (normIncGammaQContinued a x).re = 1 - TauCeti.lowerIncompleteGamma a x / Real.Gamma a := by
  rw [normIncGammaQContinued, sub_re, one_re, igBd_normIncGammaP_ofReal ha hx, ofReal_re]

/-! ### DLMF 8.10.11: comparison with `(1-e^{-γx})^a` -/

/-- `ℓ(u) = log((1-e^{-u})/u)`; Lean's conventions give `ℓ(0) = 0`, its limit at `0`. -/
def igBd_ell (u : ℝ) : ℝ := Real.log ((1 - Real.exp (-u)) / u)

/-- `ℓ(0) = 0` (Lean's junk values `x/0 = 0`, `log 0 = 0`). -/
theorem igBd_ell_zero : igBd_ell 0 = 0 := by simp [igBd_ell]

/-- `(1-e^{-u})/u > 0` for `u > 0`. -/
theorem igBd_E_pos {u : ℝ} (hu : 0 < u) : 0 < (1 - Real.exp (-u)) / u := by
  have : Real.exp (-u) < 1 := (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith))
  exact div_pos (by linarith) hu

/-- `(1-e^{-u})/u` is strictly decreasing on `(0,∞)`. -/
theorem igBd_E_strictAnti : StrictAntiOn (fun u : ℝ => (1 - Real.exp (-u)) / u) (Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
  · intro u hu
    exact ((continuousAt_const.sub (Real.continuous_exp.comp continuous_neg).continuousAt).div
      continuousAt_id (ne_of_gt hu)).continuousWithinAt
  · intro u hu
    rw [interior_Ioi] at hu
    have hu0 : u ≠ 0 := ne_of_gt hu
    have h := ((((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).const_sub 1).div
      (hasDerivAt_id u) hu0)
    rw [show deriv (fun u : ℝ => (1 - Real.exp (-u)) / u) u = _ from h.deriv]
    simp only [id, mul_one, Function.comp_apply]
    have h1 := Real.add_one_lt_exp hu0
    have h2 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have h3 : 0 < Real.exp (-u) := Real.exp_pos _
    apply div_neg_of_neg_of_pos _ (by positivity)
    nlinarith

/-- `ℓ` is strictly decreasing on `(0,∞)`. -/
theorem igBd_ell_strictAnti : StrictAntiOn igBd_ell (Ioi 0) := fun _ hu _ hv huv =>
  Real.log_lt_log (igBd_E_pos hv) (igBd_E_strictAnti hu hv huv)

/-- `ℓ'(u) = 1/(e^u-1) - 1/u`. -/
theorem igBd_ell_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt igBd_ell ((Real.exp u - 1)⁻¹ - u⁻¹) u := by
  have he : Real.exp (-u) < 1 := (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith))
  have hne : 1 - Real.exp (-u) ≠ 0 := by linarith
  have h := ((((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).const_sub 1).log hne).sub
    (Real.hasDerivAt_log (ne_of_gt hu))
  have heq : (fun v => Real.log (1 - Real.exp (-v)) - Real.log v) =ᶠ[𝓝 u] igBd_ell := by
    filter_upwards [eventually_gt_nhds hu] with v hv
    have : Real.exp (-v) < 1 := (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith))
    rw [igBd_ell, Real.log_div (by linarith) (ne_of_gt hv)]
  refine (h.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  have h2 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  have h3 : Real.exp u - 1 ≠ 0 := by have := Real.add_one_lt_exp (ne_of_gt (mem_Ioi.mp hu)); linarith
  simp only [Function.comp_apply, mul_neg, mul_one, neg_neg]
  congr 1
  rw [Real.exp_neg]
  have h4 : Real.exp u ≠ 0 := (Real.exp_pos u).ne'
  field_simp

/-- `1/(e^u-1) - 1/u` is strictly increasing on `(0,∞)`, from `u < 2 sinh(u/2)`. -/
theorem igBd_D_strictMono : StrictMonoOn (fun u : ℝ => (Real.exp u - 1)⁻¹ - u⁻¹) (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro u hu
    replace hu : 0 < u := hu
    have h3 : Real.exp u - 1 ≠ 0 := by have := Real.add_one_lt_exp (ne_of_gt (mem_Ioi.mp hu)); linarith
    exact (((Real.continuous_exp.continuousAt.sub continuousAt_const).inv₀ h3).sub
      (continuousAt_id.inv₀ (ne_of_gt hu))).continuousWithinAt
  · intro u hu
    rw [interior_Ioi] at hu
    replace hu : 0 < u := hu
    have h3 : 0 < Real.exp u - 1 := by have := Real.add_one_lt_exp (ne_of_gt (mem_Ioi.mp hu)); linarith
    have h := (((Real.hasDerivAt_exp u).sub_const 1).inv h3.ne').sub (hasDerivAt_inv (ne_of_gt hu))
    rw [show deriv (fun u : ℝ => (Real.exp u - 1)⁻¹ - u⁻¹) u = _ from h.deriv]
    -- u e^{u/2} < e^u - 1
    have hs := Real.self_lt_sinh_iff.mpr (show 0 < u/2 by linarith)
    rw [Real.sinh_eq] at hs
    have hh : Real.exp (u/2) * Real.exp (u/2) = Real.exp u := by rw [← Real.exp_add]; ring_nf
    have hh2 : Real.exp (u/2) * Real.exp (-(u/2)) = 1 := by rw [← Real.exp_add]; simp
    have hp : 0 < Real.exp (u/2) := Real.exp_pos _
    have key : u * Real.exp (u/2) < Real.exp u - 1 := by nlinarith
    have key2 : u^2 * Real.exp u < (Real.exp u - 1)^2 := by
      rw [← hh]; nlinarith [mul_pos hu hp]
    rw [sub_pos, neg_div, neg_lt_neg_iff, div_lt_iff₀ (by positivity)]
    rw [show (u ^ 2)⁻¹ * (Real.exp u - 1) ^ 2 = (Real.exp u - 1) ^ 2 / u^2 by ring,
      lt_div_iff₀ (by positivity)]
    linarith

/-- `ℓ` is continuous on `[0,∞)`. -/
theorem igBd_ell_continuousOn : ContinuousOn igBd_ell (Ici 0) := by
  intro u hu
  rcases (mem_Ici.mp hu).eq_or_lt with h0 | h0
  · subst h0
    refine continuousWithinAt_Ioi_iff_Ici.mp ?_
    have hd : HasDerivAt (fun u : ℝ => 1 - Real.exp (-u)) 1 0 := by
      simpa using ((Real.hasDerivAt_exp (-0)).comp 0 (hasDerivAt_neg 0)).const_sub 1
    have hE : Tendsto (fun t : ℝ => (1 - Real.exp (-t)) / t) (𝓝[>] 0) (𝓝 1) := by
      refine hd.tendsto_slope_zero_right.congr fun t => ?_
      simp [smul_eq_mul, div_eq_inv_mul]
    have := ((Real.continuousAt_log one_ne_zero).tendsto.comp hE)
    rw [Real.log_one] at this
    rw [ContinuousWithinAt, igBd_ell_zero]
    exact this
  · exact (igBd_ell_hasDerivAt h0).continuousAt.continuousWithinAt

/-- `ℓ` is strictly convex on `[0,∞)`. -/
theorem igBd_ell_strictConvexOn : StrictConvexOn ℝ (Ici 0) igBd_ell := by
  refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 0) igBd_ell_continuousOn ?_
  rw [interior_Ici]
  intro u hu v hv huv
  rw [(igBd_ell_hasDerivAt hu).deriv, (igBd_ell_hasDerivAt hv).deriv]
  exact igBd_D_strictMono hu hv huv

/-- `ℓ(u)/u` is strictly increasing on `(0,∞)`. -/
theorem igBd_ell_div_lt {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    igBd_ell u / u < igBd_ell v / v := by
  have := igBd_ell_strictConvexOn.secant_strict_mono_aux2 (x := 0) (y := u) (z := v)
    (mem_Ici.mpr le_rfl) (mem_Ici.mpr (hu.trans huv).le) hu huv
  simpa [igBd_ell_zero] using this

/-- The logarithm of the ratio of the derivatives of `(1-e^{-γx})^a` and `P(a,x)`. -/
def igBd_k (a γ x : ℝ) : ℝ :=
  Real.log (Real.Gamma (a+1)) + a * Real.log γ + (1-γ)*x + (a-1) * igBd_ell (γ*x)

/-- `1 - e^{-u} > 0` for `u > 0`. -/
theorem igBd_one_sub_exp_pos {u : ℝ} (hu : 0 < u) : 0 < 1 - Real.exp (-u) := by
  have : Real.exp (-u) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- The derivative of `(1-e^{-γx})^a` is that of `P(a,x)` times `exp (igBd_k a γ x)`. -/
theorem igBd_deriv_eq {a γ x : ℝ} (ha : 0 < a) (hγ : 0 < γ) (hx : 0 < x) :
    γ*Real.exp (-(γ*x))*a*(1-Real.exp (-(γ*x)))^(a-1) =
      x^(a-1)*Real.exp (-x)/Real.Gamma a * Real.exp (igBd_k a γ x) := by
  have hu : 0 < γ*x := mul_pos hγ hx
  have hE := igBd_E_pos hu
  have h1 := igBd_one_sub_exp_pos hu
  have hG := Real.Gamma_pos_of_pos ha
  rw [igBd_k, Real.exp_add, Real.exp_add, Real.exp_add,
    Real.exp_log (Real.Gamma_pos_of_pos (by linarith)),
    Real.Gamma_add_one ha.ne', mul_comm a (Real.log γ), ← Real.rpow_def_of_pos hγ, mul_comm (a-1),
    igBd_ell, ← Real.rpow_def_of_pos hE, Real.div_rpow h1.le hu.le, Real.mul_rpow hγ.le hx.le]
  have hγa : γ^a = γ^(a-1)*γ := by rw [← Real.rpow_add_one hγ.ne']; ring_nf
  have hexp : Real.exp (-x) * Real.exp ((1-γ)*x) = Real.exp (-(γ*x)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hγa, ← hexp]
  have : 0 < γ^(a-1) := Real.rpow_pos_of_pos hγ _
  have : 0 < x^(a-1) := Real.rpow_pos_of_pos hx _
  field_simp

/-- Sign of `B e^k - B` for `B > 0`. -/
theorem igBd_sign_le {B k : ℝ} (hB : 0 < B) : 0 ≤ B * Real.exp k - B ↔ 0 ≤ k := by
  rw [show B * Real.exp k - B = B * (Real.exp k - 1) by ring, mul_nonneg_iff_of_pos_left hB,
    sub_nonneg, ← Real.exp_zero, Real.exp_le_exp]

/-- Strict sign of `B e^k - B` for `B > 0`. -/
theorem igBd_sign_lt {B k : ℝ} (hB : 0 < B) : 0 < B * Real.exp k - B ↔ 0 < k := by
  rw [show B * Real.exp k - B = B * (Real.exp k - 1) by ring, mul_pos_iff_of_pos_left hB,
    sub_pos, ← Real.exp_zero, Real.exp_lt_exp]

/-- Sign of `B - B e^k` for `B > 0`. -/
theorem igBd_sign_neg_le {B k : ℝ} (hB : 0 < B) : 0 ≤ -(B * Real.exp k - B) ↔ k ≤ 0 := by
  rw [show -(B * Real.exp k - B) = B * (1 - Real.exp k) by ring, mul_nonneg_iff_of_pos_left hB,
    sub_nonneg, ← Real.exp_zero, Real.exp_le_exp]

/-- Strict sign of `B - B e^k` for `B > 0`. -/
theorem igBd_sign_neg_lt {B k : ℝ} (hB : 0 < B) : 0 < -(B * Real.exp k - B) ↔ k < 0 := by
  rw [show -(B * Real.exp k - B) = B * (1 - Real.exp k) by ring, mul_pos_iff_of_pos_left hB,
    sub_pos, ← Real.exp_zero, Real.exp_lt_exp]

/-- Derivative of `(1-e^{-γx})^a - P(a,x)`. -/
theorem igBd_H_hasDerivAt {a γ x : ℝ} (ha : 0 < a) (hγ : 0 < γ) (hx : 0 < x) :
    HasDerivAt (fun x => (1 - Real.exp (-(γ*x)))^a - TauCeti.regularizedGamma a x)
      (γ*Real.exp (-(γ*x))*a*(1-Real.exp (-(γ*x)))^(a-1) - x^(a-1)*Real.exp (-x)/Real.Gamma a) x := by
  have hf : HasDerivAt (fun x => 1 - Real.exp (-(γ*x))) (γ*Real.exp (-(γ*x))) x := by
    have := ((Real.hasDerivAt_exp (-(γ*x))).comp x ((hasDerivAt_id x).const_mul γ).neg).const_sub 1
    convert this using 1; simp; ring
  exact (hf.rpow_const (Or.inl (igBd_one_sub_exp_pos (mul_pos hγ hx)).ne')).sub
    (TauCeti.hasDerivAt_regularizedGamma ha hx)

/-- Continuity of `(1-e^{-γx})^a - P(a,x)`. -/
theorem igBd_H_continuous {a γ : ℝ} (ha : 0 < a) :
    Continuous (fun x => (1 - Real.exp (-(γ*x)))^a - TauCeti.regularizedGamma a x) :=
  ((continuous_const.sub (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)).rpow_const
    (fun _ => Or.inr ha.le)).sub (TauCeti.continuous_regularizedGamma a)

/-- `(1-e^{-γx})^a - P(a,x)` vanishes at `x = 0`. -/
theorem igBd_H_zero {a γ : ℝ} (ha : 0 < a) :
    (1 - Real.exp (-(γ*0)))^a - TauCeti.regularizedGamma a 0 = 0 := by
  simp [Real.zero_rpow ha.ne']

/-- `(1-e^{-γx})^a - P(a,x) → 0` as `x → ∞`. -/
theorem igBd_H_tendsto {a γ : ℝ} (ha : 0 < a) (hγ : 0 < γ) :
    Tendsto (fun x => (1 - Real.exp (-(γ*x)))^a - TauCeti.regularizedGamma a x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x => Real.exp (-(γ*x))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hγ)
  have h2 := ((tendsto_const_nhds (x := (1:ℝ))).sub h1).rpow_const (p := a) (Or.inr ha.le)
  have := h2.sub (TauCeti.tendsto_regularizedGamma_atTop ha)
  simpa using this

/-- If positivity of `igBd_k a γ` propagates to the left, then `P(a,x) < (1-e^{-γx})^a`. -/
theorem igBd_regGamma_lt_pow {a γ : ℝ} (ha : 0 < a) (hγ : 0 < γ)
    (hprop : ∀ x y, 0 < x → x < y → 0 ≤ igBd_k a γ y → 0 < igBd_k a γ x) {x : ℝ} (hx : 0 < x) :
    TauCeti.regularizedGamma a x < (1 - Real.exp (-(γ*x)))^a := by
  have hB : ∀ x : ℝ, 0 < x → 0 < x^(a-1)*Real.exp (-x)/Real.Gamma a := fun x hx =>
    div_pos (mul_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _)) (Real.Gamma_pos_of_pos ha)
  have := igBd_pos_of_leftProp (igBd_H_continuous (γ := γ) ha).continuousOn (igBd_H_zero ha)
    (igBd_H_tendsto ha hγ) (fun x hx => igBd_H_hasDerivAt ha hγ hx) (fun x y hx hxy hy => by
      rw [igBd_deriv_eq ha hγ (hx.trans hxy), igBd_sign_le (hB y (hx.trans hxy))] at hy
      rw [igBd_deriv_eq ha hγ hx, igBd_sign_lt (hB x hx)]
      exact hprop x y hx hxy hy) hx
  linarith

/-- If negativity of `igBd_k a γ` propagates to the left, then `(1-e^{-γx})^a < P(a,x)`. -/
theorem igBd_pow_lt_regGamma {a γ : ℝ} (ha : 0 < a) (hγ : 0 < γ)
    (hprop : ∀ x y, 0 < x → x < y → igBd_k a γ y ≤ 0 → igBd_k a γ x < 0) {x : ℝ} (hx : 0 < x) :
    (1 - Real.exp (-(γ*x)))^a < TauCeti.regularizedGamma a x := by
  have hB : ∀ x : ℝ, 0 < x → 0 < x^(a-1)*Real.exp (-x)/Real.Gamma a := fun x hx =>
    div_pos (mul_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _)) (Real.Gamma_pos_of_pos ha)
  have := igBd_pos_of_leftProp (igBd_H_continuous (γ := γ) ha).neg.continuousOn
    (by simp only [Pi.neg_apply]; rw [igBd_H_zero ha, neg_zero])
    (by have := (igBd_H_tendsto ha hγ).neg; rw [neg_zero] at this; exact this) (fun x hx => (igBd_H_hasDerivAt ha hγ hx).neg)
    (fun x y hx hxy hy => by
      rw [igBd_deriv_eq ha hγ (hx.trans hxy), igBd_sign_neg_le (hB y (hx.trans hxy))] at hy
      rw [igBd_deriv_eq ha hγ hx, igBd_sign_neg_lt (hB x hx)]
      exact hprop x y hx hxy hy) hx
  simp only [Pi.neg_apply] at this
  linarith

/-- The constant `log Γ(1+a) + a log d_a` vanishes for `d_a = Γ(1+a)^{-1/a}`. -/
theorem igBd_k_da {a x : ℝ} (ha : 0 < a) :
    igBd_k a (Real.Gamma (1+a)^(-1/a)) x =
      (1 - Real.Gamma (1+a)^(-1/a))*x + (a-1) * igBd_ell (Real.Gamma (1+a)^(-1/a)*x) := by
  have hG := Real.Gamma_pos_of_pos (show 0 < 1 + a by linarith)
  rw [igBd_k, Real.log_rpow hG, add_comm a 1]
  field_simp
  ring

/-- `k(x)/x` for `γ = d_a`, written through `ℓ(u)/u`. -/
theorem igBd_k_da_eq {a γ x : ℝ} (hγ : 0 < γ) (hx : 0 < x) :
    (1 - γ)*x + (a-1) * igBd_ell (γ*x) = x * ((1-γ) + (a-1)*γ*(igBd_ell (γ*x)/(γ*x))) := by
  field_simp

/-- Left propagation for `γ = d_a`, `a < 1` (upper bound of 8.10.11). -/
theorem igBd_prop_da_lt_one {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ x y, 0 < x → x < y → 0 ≤ igBd_k a (Real.Gamma (1+a)^(-1/a)) y →
      0 < igBd_k a (Real.Gamma (1+a)^(-1/a)) x := by
  intro x y hx hxy hy
  set γ := Real.Gamma (1+a)^(-1/a)
  have hγ : 0 < γ := Real.rpow_pos_of_pos (Real.Gamma_pos_of_pos (by linarith)) _
  have hy0 := hx.trans hxy
  rw [igBd_k_da ha, igBd_k_da_eq hγ hy0] at hy
  rw [igBd_k_da ha, igBd_k_da_eq hγ hx]
  have hb : 0 ≤ (1-γ) + (a-1)*γ*(igBd_ell (γ*y)/(γ*y)) := by
    by_contra h; push Not at h; linarith [mul_neg_of_pos_of_neg hy0 h]
  have hr := igBd_ell_div_lt (mul_pos hγ hx) (mul_lt_mul_of_pos_left hxy hγ)
  have hc : (a-1)*γ < 0 := mul_neg_of_neg_of_pos (by linarith) hγ
  refine mul_pos hx ?_
  nlinarith

/-- Left propagation of negativity for `γ = d_a`, `a > 1` (lower bound of 8.10.11). -/
theorem igBd_prop_da_gt_one {a : ℝ} (ha1 : 1 < a) :
    ∀ x y, 0 < x → x < y → igBd_k a (Real.Gamma (1+a)^(-1/a)) y ≤ 0 →
      igBd_k a (Real.Gamma (1+a)^(-1/a)) x < 0 := by
  intro x y hx hxy hy
  have ha : 0 < a := by linarith
  set γ := Real.Gamma (1+a)^(-1/a)
  have hγ : 0 < γ := Real.rpow_pos_of_pos (Real.Gamma_pos_of_pos (by linarith)) _
  have hy0 := hx.trans hxy
  rw [igBd_k_da ha, igBd_k_da_eq hγ hy0] at hy
  rw [igBd_k_da ha, igBd_k_da_eq hγ hx]
  have hb : (1-γ) + (a-1)*γ*(igBd_ell (γ*y)/(γ*y)) ≤ 0 := by
    by_contra h; push Not at h; linarith [mul_pos hy0 h]
  have hr := igBd_ell_div_lt (mul_pos hγ hx) (mul_lt_mul_of_pos_left hxy hγ)
  have hc : 0 < (a-1)*γ := mul_pos (by linarith) hγ
  refine mul_neg_of_pos_of_neg hx ?_
  nlinarith

/-- Left propagation for `γ = 1`, `a > 1` (upper bound of 8.10.11). -/
theorem igBd_prop_one_gt_one {a : ℝ} (ha1 : 1 < a) :
    ∀ x y, 0 < x → x < y → 0 ≤ igBd_k a 1 y → 0 < igBd_k a 1 x := by
  intro x y hx hxy hy
  simp only [igBd_k, Real.log_one, mul_zero, add_zero, sub_self, zero_mul, one_mul] at hy ⊢
  have := igBd_ell_strictAnti hx (hx.trans hxy) hxy
  nlinarith

/-- Left propagation of negativity for `γ = 1`, `a < 1` (lower bound of 8.10.11). -/
theorem igBd_prop_one_lt_one {a : ℝ} (ha1 : a < 1) :
    ∀ x y, 0 < x → x < y → igBd_k a 1 y ≤ 0 → igBd_k a 1 x < 0 := by
  intro x y hx hxy hy
  simp only [igBd_k, Real.log_one, mul_zero, add_zero, sub_self, zero_mul, one_mul] at hy ⊢
  have := igBd_ell_strictAnti hx (hx.trans hxy) hxy
  nlinarith

end DLMF.Confluent
