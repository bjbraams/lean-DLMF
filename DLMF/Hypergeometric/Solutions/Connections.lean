/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Solutions.Logarithmic

/-!
# Connection formulas on intersecting Gauss disks

The connected lens of the origin and unit-point disks supports the fundamental connection
identities.

Source references and common attribution are retained in
`DLMF.Hypergeometric.Solutions`.
-/

@[expose] public section

open Complex Filter

open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric

/-! ### The lens `‖z‖ < 1`, `‖1 - z‖ < 1` and the connection at `z = 1` -/

/-- The overlap of the series disks at `0` and at `1`. -/
def connLens : Set ℂ := {z | ‖z‖ < 1 ∧ ‖1 - z‖ < 1}

/-- The lens is the intersection of the unit disks about `0` and `1`. -/
theorem connLens_eq : connLens = Metric.ball 0 1 ∩ Metric.ball 1 1 := by
  ext z
  simp only [connLens, Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_ball, dist_eq_norm,
    sub_zero, norm_sub_rev z 1]

/-- The lens is open. -/
theorem isOpen_connLens : IsOpen connLens := by
  rw [connLens_eq]
  exact Metric.isOpen_ball.inter Metric.isOpen_ball

/-- The lens is preconnected (it is convex). -/
theorem isPreconnected_connLens : IsPreconnected connLens := by
  rw [connLens_eq]
  exact ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected

/-- On the lens, `1 - z` lies in the slit plane. -/
theorem one_sub_mem_slitPlane_of_mem_connLens {z : ℂ} (hz : z ∈ connLens) : 1 - z ∈ slitPlane := by
  refine mem_slitPlane_iff.mpr (Or.inl ?_)
  have := (re_le_norm z).trans_lt hz.1
  simp only [sub_re, one_re]
  linarith

/-- The lens does not contain `0`. -/
theorem ne_zero_of_mem_connLens {z : ℂ} (hz : z ∈ connLens) : z ≠ 0 := by
  rintro rfl
  simp [connLens] at hz

/-- The lens does not contain `1`. -/
theorem ne_one_of_mem_connLens {z : ℂ} (hz : z ∈ connLens) : z ≠ 1 := by
  rintro rfl
  simp [connLens] at hz

/-- `₂F₁(a, b; c; ·)` is analytic on the open unit disk. -/
theorem analyticAt_ordinaryHypergeometric {a b c z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (₂F₁ a b c) z :=
  (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).analyticAt_of_mem
    (mem_eball_one_of_norm_lt_one hz)

/-- The first local solution at `1` is analytic on the disk `‖1 - z‖ < 1`. -/
theorem analyticAt_oneFirst {a b c z : ℂ} (hz : ‖1 - z‖ < 1) : AnalyticAt ℂ (oneFirst a b c) z :=
  (analyticAt_ordinaryHypergeometric hz).comp (analyticAt_const.sub analyticAt_id)

/-- The second local solution at `1` is analytic on the disk `‖1 - z‖ < 1` inside the slit-plane
  condition. -/
theorem analyticAt_oneSecond {a b c z : ℂ} (hz : ‖1 - z‖ < 1) (hs : 1 - z ∈ slitPlane) :
    AnalyticAt ℂ (oneSecond a b c) z :=
  ((analyticAt_const.sub analyticAt_id).cpow analyticAt_const hs).mul
    ((analyticAt_ordinaryHypergeometric hz).comp (analyticAt_const.sub analyticAt_id))

/-- On the lens, `₂F₁(a,b;c;z)` is a combination of the two local solutions at `z = 1`. -/
theorem exists_connection_one {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hC : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ)) (hS : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ))
    (hs0 : c - a - b ≠ 0) :
    ∃ α β : ℂ, ∀ z ∈ connLens,
      ₂F₁ a b c z = α * oneFirst a b c z + β * oneSecond a b c z := by
  set s := c - a - b with hsdef
  set H : ℂ → ℂ := ₂F₁ a b (a + b - c + 1) with hH
  set G : ℂ → ℂ := ₂F₁ (c - a) (c - b) (c - a - b + 1) with hG
  set B : ℂ → ℂ := fun w => -s * H w * G w - w * H w * deriv G w + w * deriv H w * G w with hB
  have hH0 : AnalyticAt ℂ H 0 := analyticAt_ordinaryHypergeometric (by simp)
  have hG0 : AnalyticAt ℂ G 0 := analyticAt_ordinaryHypergeometric (by simp)
  have hBc : ContinuousAt B 0 := by
    simp only [hB]
    exact (((continuousAt_const.mul hH0.continuousAt).mul hG0.continuousAt).sub
      ((continuousAt_id.mul hH0.continuousAt).mul hG0.deriv.continuousAt)).add
      ((continuousAt_id.mul hH0.deriv.continuousAt).mul hG0.continuousAt)
  have hB0 : B 0 ≠ 0 := by
    simp only [hB, hH, hG, ordinaryHypergeometric_zero]
    simpa using hs0
  have hev : ∀ᶠ w in 𝓝 (0 : ℂ), B w ≠ 0 := hBc.eventually_ne hB0
  have hreal : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := (continuous_ofReal.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    rwa [ofReal_zero] at this
  obtain ⟨t, hBt, ht⟩ := ((hreal.eventually hev).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num))).exists
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
  set z₀ : ℂ := 1 - t with hz₀
  have h1z₀ : 1 - z₀ = t := by rw [hz₀]; ring
  have hz₀L : z₀ ∈ connLens := by
    refine ⟨?_, ?_⟩
    · rw [hz₀, ← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith [ht.2])]
      linarith [ht.1]
    · rw [h1z₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      linarith [ht.2]
  have htn : ‖(t : ℂ)‖ < 1 := by rw [← h1z₀]; exact hz₀L.2
  have htslit : (t : ℂ) ∈ slitPlane := by rw [← h1z₀]; exact one_sub_mem_slitPlane_of_mem_connLens hz₀L
  -- Derivatives at `z₀`.
  have hHt : AnalyticAt ℂ H t := analyticAt_ordinaryHypergeometric htn
  have hGt : AnalyticAt ℂ G t := analyticAt_ordinaryHypergeometric htn
  have hsub : HasDerivAt (fun w : ℂ => 1 - w) (-1) z₀ := by
    simpa using (hasDerivAt_id z₀).const_sub 1
  have hHt' : HasDerivAt H (deriv H (1 - z₀)) (1 - z₀) := by
    rw [h1z₀]; exact hHt.differentiableAt.hasDerivAt
  have hGt' : HasDerivAt G (deriv G (1 - z₀)) (1 - z₀) := by
    rw [h1z₀]; exact hGt.differentiableAt.hasDerivAt
  have dF1 : HasDerivAt (oneFirst a b c) (-deriv H t) z₀ := by
    show HasDerivAt (fun w => H (1 - w)) _ z₀
    exact (hHt'.comp z₀ hsub).congr_deriv (by rw [h1z₀]; ring)
  have dF2 : HasDerivAt (oneSecond a b c)
      (s * (t : ℂ) ^ (s - 1) * (-1) * G t + (t : ℂ) ^ s * (-deriv G t)) z₀ := by
    have hp := hsub.cpow_const (c := s) (by rw [h1z₀]; exact htslit)
    show HasDerivAt (fun w => (1 - w) ^ s * G (1 - w)) _ z₀
    exact (hp.mul (hGt'.comp z₀ hsub)).congr_deriv
      (by simp only [Function.comp_apply, h1z₀]; ring)
  have hf₀ : AnalyticAt ℂ (₂F₁ a b c) z₀ := analyticAt_ordinaryHypergeometric hz₀L.1
  have hF1v : oneFirst a b c z₀ = H t := by simp [oneFirst, hH, h1z₀]
  have hF2v : oneSecond a b c z₀ = (t : ℂ) ^ s * G t := by simp [oneSecond, hG, hsdef, h1z₀]
  set W : ℂ := oneFirst a b c z₀ * (s * (t : ℂ) ^ (s - 1) * (-1) * G t + (t : ℂ) ^ s *
    (-deriv G t)) - (-deriv H t) * oneSecond a b c z₀ with hW
  have hpow : (t : ℂ) ^ s = (t : ℂ) ^ (s - 1) * t := by
    conv_lhs => rw [show s = s - 1 + 1 by ring, cpow_add _ _ ht0, cpow_one]
  have hWt : (t : ℂ) * W = (t : ℂ) ^ s * B t := by
    rw [hW, hF1v, hF2v, hpow]
    simp only [hB]
    ring
  have hW0 : W ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hWt
    exact (mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl ht0)) hBt) hWt.symm
  -- The combination with vanishing value and derivative at `z₀`.
  set f₀ := ₂F₁ a b c z₀
  set f₁ := deriv (₂F₁ a b c) z₀
  set p₀ := oneFirst a b c z₀
  set p₁ := -deriv H t
  set q₀ := oneSecond a b c z₀
  set q₁ := s * (t : ℂ) ^ (s - 1) * (-1) * G t + (t : ℂ) ^ s * (-deriv G t)
  refine ⟨(f₀ * q₁ - f₁ * q₀) / W, (p₀ * f₁ - p₁ * f₀) / W, fun z hz => ?_⟩
  set α := (f₀ * q₁ - f₁ * q₀) / W
  set β := (p₀ * f₁ - p₁ * f₀) / W
  let g : ℂ → ℂ := fun w => ₂F₁ a b c w - α * oneFirst a b c w - β * oneSecond a b c w
  have hgan : AnalyticOnNhd ℂ g connLens := fun w hw =>
    ((analyticAt_ordinaryHypergeometric hw.1).sub
      (analyticAt_const.mul (analyticAt_oneFirst hw.2))).sub
      (analyticAt_const.mul (analyticAt_oneSecond hw.2
        (one_sub_mem_slitPlane_of_mem_connLens hw)))
  have hgode : ∀ w ∈ connLens, gaussOperator a b c g w = 0 := by
    intro w hw
    rw [gaussOperator_sub_smul (analyticAt_ordinaryHypergeometric hw.1)
      (analyticAt_oneFirst hw.2)
      (analyticAt_oneSecond hw.2 (one_sub_mem_slitPlane_of_mem_connLens hw))]
    have h1 : gaussOperator a b c (₂F₁ a b c) w = 0 := by
      have := ordinaryHypergeometric_ode (a := a) (b := b) hc hw.1
        (ne_zero_of_mem_connLens hw) (ne_one_of_mem_connLens hw)
      simpa [gaussOperator] using this
    rw [h1, one_first_ode hC hw.2,
      one_second_ode hS hw.2 (one_sub_mem_slitPlane_of_mem_connLens hw)]
    ring
  have hgv : g z₀ = 0 := by
    change f₀ - α * p₀ - β * q₀ = 0
    simp only [α, β]
    field_simp
    simp only [hW]
    ring
  have hgd : deriv g z₀ = 0 := by
    have h : HasDerivAt g (f₁ - α * p₁ - β * q₁) z₀ :=
      ((hf₀.differentiableAt.hasDerivAt.sub (dF1.const_mul α)).sub (dF2.const_mul β))
    rw [h.deriv]
    change f₁ - α * p₁ - β * q₁ = 0
    simp only [α, β]
    field_simp
    simp only [hW]
    ring
  have hg0 := gaussOperator_eq_zero_of_deriv_eq_zero isOpen_connLens isPreconnected_connLens
    hgan hgode hz₀L (ne_zero_of_mem_connLens hz₀L) (ne_one_of_mem_connLens hz₀L) hgv hgd z hz
  simp only [g] at hg0
  linear_combination hg0

/-- Abel's theorem for `₂F₁` at `z = 1` when `Re(c-a-b) > 0`. -/
theorem tendsto_ordinaryHypergeometric_left_one {a b c : ℂ} (h : 0 < (c - a - b).re) :
    Tendsto (fun x : ℝ => ₂F₁ a b c (x : ℂ)) (𝓝[<] 1) (𝓝 (₂F₁ a b c 1)) := by
  have hs : Summable (gaussHGCoeff a b c) := by
    simpa using ordinaryHypergeometric_summable_of_mem_sphere (z := 1) (by simp) h
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hs.hasSum.tendsto_sum_nat
  rw [tendsto_map'_iff, ← ordinaryHypergeometric_one_eq_tsum] at habel
  refine habel.congr fun x => ?_
  simp only [Function.comp_apply]
  rw [ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  congr 1
  funext n
  simp [gaussHGCoeff, poch, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- `sin(πx) ≠ 0` when `x` is not an integer. -/
theorem sin_pi_mul_ne_zero_of_not_int {x : ℂ} (hx : ∀ k : ℤ, x ≠ (k : ℂ)) :
    Complex.sin (π * x) ≠ 0 := by
  rw [Ne, Complex.sin_eq_zero_iff]
  rintro ⟨k, hk⟩
  apply hx k
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have := hk
  field_simp at this
  linear_combination this

/-- The connection formula 15.10.21 in a parameter region where every limit is available. -/
theorem zero_first_connection_one_base {a b c : ℂ} (ha : ∀ k : ℤ, a ≠ (k : ℂ))
    (hb : ∀ k : ℤ, b ≠ (k : ℂ)) (hc : ∀ k : ℤ, c ≠ (k : ℂ)) (hca : ∀ k : ℤ, c - a ≠ (k : ℂ))
    (hcb : ∀ k : ℤ, c - b ≠ (k : ℂ)) (hs : ∀ k : ℤ, c - a - b ≠ (k : ℂ))
    (hre : 0 < (c - a - b).re) (hre1 : c.re < 1) {z : ℂ} (hz : z ∈ connLens) :
    ₂F₁ a b c z =
      Gamma c * Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)) * oneFirst a b c z +
        Gamma c * Gamma (a + b - c) / (Gamma a * Gamma b) * oneSecond a b c z := by
  have hc' := not_neg_nat_of_not_int hc
  have hC : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ) := by
    refine not_neg_nat_of_not_int fun k h => hs (1 - k) ?_
    push_cast
    linear_combination -h
  have hS : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ) := by
    refine not_neg_nat_of_not_int fun k h => hs (k - 1) ?_
    push_cast
    linear_combination h
  have hs0 : c - a - b ≠ 0 := by simpa using hs 0
  obtain ⟨α, β, hαβ⟩ := exists_connection_one hc' hC hS hs0
  set H : ℂ → ℂ := ₂F₁ a b (a + b - c + 1) with hH
  set G : ℂ → ℂ := ₂F₁ (c - a) (c - b) (c - a - b + 1) with hG
  have hH0 : AnalyticAt ℂ H 0 := analyticAt_ordinaryHypergeometric (by simp)
  have hG0 : AnalyticAt ℂ G 0 := analyticAt_ordinaryHypergeometric (by simp)
  have hf0 : AnalyticAt ℂ (₂F₁ a b c : ℂ → ℂ) (0 : ℂ) :=
    analyticAt_ordinaryHypergeometric (by simp)
  have hmem : ∀ x : ℝ, 0 < x → x < 1 → (x : ℂ) ∈ connLens := by
    intro x hx0 hx1
    refine ⟨?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact hx1
    · rw [← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
  have hid : ∀ x : ℝ, 0 < x → x < 1 → ₂F₁ a b c (x : ℂ) =
      α * H (1 - x) + β * ((1 - (x : ℂ)) ^ (c - a - b) * G (1 - x)) := by
    intro x hx0 hx1
    exact hαβ _ (hmem x hx0 hx1)
  have hsub1 : Tendsto (fun x : ℝ => (1 : ℂ) - x) (𝓝[<] 1) (𝓝 0) := by
    have := ((show Continuous (fun x : ℝ => (1 : ℂ) - (x : ℂ)) by fun_prop).tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    simpa using this
  have hsub0 : Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := ((show Continuous (fun x : ℝ => (1 : ℝ) - x) by fun_prop).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_Iio]
      linarith [Set.mem_Ioi.mp hx]
  -- The limit `x → 1⁻`.
  have hα : α = ₂F₁ a b c 1 := by
    have hF := tendsto_ordinaryHypergeometric_left_one hre
    have hF1 : Tendsto (fun x : ℝ => H (1 - x)) (𝓝[<] 1) (𝓝 1) := by
      have := hH0.continuousAt.tendsto.comp hsub1
      simpa [hH, Function.comp_def] using this
    have hpow : Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (c - a - b)) (𝓝[<] 1) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hr : Tendsto (fun x : ℝ => (1 - x) ^ (c - a - b).re) (𝓝[<] 1) (𝓝 0) := by
        have hc0 := (Real.continuousAt_rpow_const 0 (c - a - b).re (Or.inr hre.le)).tendsto
        rw [Real.zero_rpow hre.ne'] at hc0
        refine hc0.comp ?_
        have := ((show Continuous (fun x : ℝ => (1 : ℝ) - x) by fun_prop).tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
        simpa using this
      refine hr.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [← ofReal_one, ← ofReal_sub, norm_cpow_eq_rpow_re_of_pos (by linarith [Set.mem_Iio.mp hx])]
    have hF2 : Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (c - a - b) * G (1 - x)) (𝓝[<] 1)
        (𝓝 (0 * 1)) := by
      refine hpow.mul ?_
      have := hG0.continuousAt.tendsto.comp hsub1
      simpa [hG, Function.comp_def] using this
    have hR := (hF1.const_mul α).add (hF2.const_mul β)
    rw [mul_one, zero_mul, mul_zero, add_zero] at hR
    refine tendsto_nhds_unique (hR.congr' ?_) hF
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact (hid x hx.1 hx.2).symm
  -- The limit `x → 0⁺`.
  have hre' : 0 < ((a + b - c + 1) - a - b).re := by
    simp only [sub_re, add_re, one_re] at hre1 ⊢
    linarith
  have hre'' : 0 < ((c - a - b + 1) - (c - a) - (c - b)).re := by
    simp only [sub_re, add_re, one_re] at hre1 ⊢
    linarith
  have h0 : 1 = α * H 1 + β * G 1 := by
    have hF : Tendsto (fun x : ℝ => ₂F₁ a b c (x : ℂ)) (𝓝[>] 0) (𝓝 1) := by
      have := hf0.continuousAt.tendsto.comp ((continuous_ofReal.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ))))
      simpa [Function.comp_def] using this
    have hF1 : Tendsto (fun x : ℝ => H (1 - x)) (𝓝[>] 0) (𝓝 (H 1)) := by
      have := (tendsto_ordinaryHypergeometric_left_one hre').comp hsub0
      simpa [hH, Function.comp_def] using this
    have hF2 : Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (c - a - b) * G (1 - x)) (𝓝[>] 0)
        (𝓝 (1 * G 1)) := by
      refine Tendsto.mul ?_ ?_
      · have h1 := (continuousAt_cpow_const (b := c - a - b) one_mem_slitPlane).tendsto
        rw [one_cpow] at h1
        refine h1.comp ?_
        have := ((show Continuous (fun x : ℝ => (1 : ℂ) - (x : ℂ)) by fun_prop).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
        simpa using this
      · have := (tendsto_ordinaryHypergeometric_left_one hre'').comp hsub0
        simpa [hG, Function.comp_def] using this
    have hR := (hF1.const_mul α).add (hF2.const_mul β)
    rw [one_mul] at hR
    refine tendsto_nhds_unique hF (hR.congr' ?_)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact (hid x hx.1 hx.2).symm
  -- Gauss's sums and the reflection formula.
  have hg1 := gauss_summation (a := a) (b := b) hc' hre
  have hH1 : H 1 = Gamma (a + b - c + 1) * Gamma (1 - c) /
      (Gamma (b - c + 1) * Gamma (a - c + 1)) := by
    have := gauss_summation (a := a) (b := b) hC hre'
    rw [show a + b - c + 1 - a - b = 1 - c by ring, show a + b - c + 1 - a = b - c + 1 by ring,
      show a + b - c + 1 - b = a - c + 1 by ring] at this
    exact this
  have hG1 : G 1 = Gamma (c - a - b + 1) * Gamma (1 - c) / (Gamma (1 - b) * Gamma (1 - a)) := by
    have := gauss_summation (a := c - a) (b := c - b) hS hre''
    rw [show c - a - b + 1 - (c - a) - (c - b) = 1 - c by ring,
      show c - a - b + 1 - (c - a) = 1 - b by ring,
      show c - a - b + 1 - (c - b) = 1 - a by ring] at this
    exact this
  have refl (x y : ℂ) (hxy : 1 - x = y) : Gamma x * Gamma y = π / Complex.sin (π * x) := by
    rw [← hxy]
    exact Complex.Gamma_mul_Gamma_one_sub x
  have hnz (x : ℂ) (hx : ∀ k : ℤ, x ≠ (k : ℂ)) : Gamma x ≠ 0 :=
    Complex.Gamma_ne_zero (not_neg_nat_of_not_int hx)
  have hshift (x : ℂ) (hx : ∀ k : ℤ, x ≠ (k : ℂ)) (m : ℤ) : ∀ k : ℤ, x + m ≠ (k : ℂ) := by
    intro k h
    exact hx (k - m) (by push_cast; linear_combination h)
  have hneg (x : ℂ) (hx : ∀ k : ℤ, x ≠ (k : ℂ)) : ∀ k : ℤ, -x ≠ (k : ℂ) := by
    intro k h
    exact hx (-k) (by push_cast; linear_combination -h)
  have hab : ∀ k : ℤ, a + b - c ≠ (k : ℂ) := by
    simpa [show -(c - a - b) = a + b - c by ring] using hneg _ hs
  have hsa := sin_pi_mul_ne_zero_of_not_int ha
  have hsb := sin_pi_mul_ne_zero_of_not_int hb
  have hsc := sin_pi_mul_ne_zero_of_not_int hc
  have hsca := sin_pi_mul_ne_zero_of_not_int hca
  have hscb := sin_pi_mul_ne_zero_of_not_int hcb
  have hss := sin_pi_mul_ne_zero_of_not_int hs
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have r1 := refl c (1 - c) rfl
  have r2 := refl (c - a - b) (a + b - c + 1) (by ring)
  have r3 := refl (c - a) (a - c + 1) (by ring)
  have r4 := refl (c - b) (b - c + 1) (by ring)
  have r5 := refl (a + b - c) (c - a - b + 1) (by ring)
  have r6 := refl a (1 - a) rfl
  have r7 := refl b (1 - b) rfl
  have hsin5 : Complex.sin (π * (a + b - c)) = -Complex.sin (π * (c - a - b)) := by
    rw [← Complex.sin_neg]
    ring_nf
  set β₀ := Gamma c * Gamma (a + b - c) / (Gamma a * Gamma b) with hβ₀
  have hG1ne : G 1 ≠ 0 := by
    rw [hG1]
    have h1 : ∀ k : ℤ, c - a - b + 1 ≠ (k : ℂ) := by simpa using hshift _ hs 1
    have h2 : ∀ k : ℤ, 1 - c ≠ (k : ℂ) := by
      simpa [show -c + 1 = 1 - c by ring] using hshift _ (hneg _ hc) 1
    have h3 : ∀ k : ℤ, 1 - b ≠ (k : ℂ) := by
      simpa [show -b + 1 = 1 - b by ring] using hshift _ (hneg _ hb) 1
    have h4 : ∀ k : ℤ, 1 - a ≠ (k : ℂ) := by
      simpa [show -a + 1 = 1 - a by ring] using hshift _ (hneg _ ha) 1
    exact div_ne_zero (mul_ne_zero (hnz _ h1) (hnz _ h2)) (mul_ne_zero (hnz _ h3) (hnz _ h4))
  have k1 : α * H 1 = (π / Complex.sin (π * c)) * (π / Complex.sin (π * (c - a - b))) /
      ((π / Complex.sin (π * (c - a))) * (π / Complex.sin (π * (c - b)))) := by
    rw [hα, hg1, hH1, ← r1, ← r2, ← r3, ← r4]
    ring
  have k2 : β₀ * G 1 = (π / Complex.sin (π * c)) * (π / Complex.sin (π * (a + b - c))) /
      ((π / Complex.sin (π * a)) * (π / Complex.sin (π * b))) := by
    rw [hβ₀, hG1, ← r1, ← r5, ← r6, ← r7]
    ring
  have htrig : 1 = α * H 1 + β₀ * G 1 := by
    rw [k1, k2, hsin5]
    field_simp
    simp only [mul_sub, Complex.sin_sub, Complex.cos_sub]
    linear_combination (-(Complex.sin (π * a) * Complex.sin (π * b))) *
      Complex.sin_sq_add_cos_sq (π * c)
  have hβ : β = β₀ := by
    have : (β - β₀) * G 1 = 0 := by linear_combination htrig - h0
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hG1ne)
  rw [hαβ z hz, hα, hg1, hβ]

/-- Left side of the regularized form of 15.10.21, entire in each parameter. -/
def connLhs (a b c z : ℂ) : ℂ :=
  Complex.sin (π * (c - a - b)) * regularizedGaussHGFun a b c z

/-- Right side of the regularized form of 15.10.21, entire in each parameter. -/
def connRhs (a b c z : ℂ) : ℂ :=
  π * (regularizedGaussHGFun a b (a + b - c + 1) (1 - z) * (Gamma (c - a))⁻¹ * (Gamma (c - b))⁻¹ -
    (1 - z) ^ (c - a - b) * regularizedGaussHGFun (c - a) (c - b) (c - a - b + 1) (1 - z) *
      (Gamma a)⁻¹ * (Gamma b)⁻¹)

/-- For parameters depending holomorphically on `w`, both sides of the connection formula are entire
  in `w` at each point of the lens. -/
theorem differentiable_connLhs_connRhs {A B C : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (hC : Differentiable ℂ C) {z : ℂ} (hz : z ∈ connLens) :
    Differentiable ℂ (fun w => connLhs (A w) (B w) (C w) z) ∧
      Differentiable ℂ (fun w => connRhs (A w) (B w) (C w) z) := by
  have hz1 : ‖1 - z‖ < 1 := hz.2
  have hz0 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_one_of_mem_connLens hz))
  have hR (A' B' C' : ℂ → ℂ) (hA' : Differentiable ℂ A') (hB' : Differentiable ℂ B')
      (hC' : Differentiable ℂ C') {x : ℂ} (hx : ‖x‖ < 1) :
      Differentiable ℂ (fun w => regularizedGaussHGFun (A' w) (B' w) (C' w) x) := fun w =>
    (analyticOnNhd_regularizedGaussHGFun_comp hA' hB' hC' hx w trivial).differentiableAt
  have hiG (U : ℂ → ℂ) (hU : Differentiable ℂ U) : Differentiable ℂ (fun w => (Gamma (U w))⁻¹) :=
    differentiable_one_div_Gamma.comp hU
  have hs : Differentiable ℂ (fun w => C w - A w - B w) := (hC.sub hA).sub hB
  refine ⟨?_, ?_⟩
  · exact (differentiable_sin.comp ((differentiable_const _).mul hs)).mul
      (hR A B C hA hB hC hz.1)
  · have h1 := hR A B (fun w => A w + B w - C w + 1) hA hB (((hA.add hB).sub hC).add_const 1) hz1
    have h2 := hR (fun w => C w - A w) (fun w => C w - B w) (fun w => C w - A w - B w + 1)
      (hC.sub hA) (hC.sub hB) (hs.add_const 1) hz1
    have hp : Differentiable ℂ (fun w => (1 - z) ^ (C w - A w - B w)) := fun w =>
      (hs w).const_cpow (Or.inl hz0)
    exact (differentiable_const _).mul
      (((h1.mul (hiG _ (hC.sub hA))).mul (hiG _ (hC.sub hB))).sub
        (((hp.mul h2).mul (hiG _ hA)).mul (hiG _ hB)))

/-- The regularized form of 15.10.21 in the base parameter region. -/
theorem connLhs_eq_connRhs_base {a b c : ℂ} (ha : ∀ k : ℤ, a ≠ (k : ℂ))
    (hb : ∀ k : ℤ, b ≠ (k : ℂ)) (hc : ∀ k : ℤ, c ≠ (k : ℂ)) (hca : ∀ k : ℤ, c - a ≠ (k : ℂ))
    (hcb : ∀ k : ℤ, c - b ≠ (k : ℂ)) (hs : ∀ k : ℤ, c - a - b ≠ (k : ℂ))
    (hre : 0 < (c - a - b).re) (hre1 : c.re < 1) {z : ℂ} (hz : z ∈ connLens) :
    connLhs a b c z = connRhs a b c z := by
  have h := zero_first_connection_one_base ha hb hc hca hcb hs hre hre1 hz
  have hc' := not_neg_nat_of_not_int hc
  have hC : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ) := by
    refine not_neg_nat_of_not_int fun k h => hs (1 - k) ?_
    push_cast
    linear_combination -h
  have hS : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ) := by
    refine not_neg_nat_of_not_int fun k h => hs (k - 1) ?_
    push_cast
    linear_combination h
  have hΓc := Complex.Gamma_ne_zero hc'
  have hΓC := Complex.Gamma_ne_zero hC
  have hΓS := Complex.Gamma_ne_zero hS
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hss := sin_pi_mul_ne_zero_of_not_int hs
  have e1 : Gamma (c - a - b) * Gamma (a + b - c + 1) = π / Complex.sin (π * (c - a - b)) := by
    rw [show a + b - c + 1 = 1 - (c - a - b) by ring]
    exact Complex.Gamma_mul_Gamma_one_sub _
  have e2 : Gamma (a + b - c) * Gamma (c - a - b + 1) = -(π / Complex.sin (π * (c - a - b))) := by
    rw [show c - a - b + 1 = 1 - (a + b - c) by ring, Complex.Gamma_mul_Gamma_one_sub,
      show (π : ℂ) * (a + b - c) = -(π * (c - a - b)) by ring, Complex.sin_neg, div_neg]
  have hG1 : Gamma (c - a - b) = π / Complex.sin (π * (c - a - b)) / Gamma (a + b - c + 1) := by
    rw [eq_div_iff hΓC, e1]
  have hG2 : Gamma (a + b - c) =
      -(π / Complex.sin (π * (c - a - b))) / Gamma (c - a - b + 1) := by
    rw [eq_div_iff hΓS, e2]
  rw [hG1, hG2] at h
  simp only [oneFirst, oneSecond] at h
  simp only [connLhs, connRhs, regularizedGaussHGFun_eq_div_Gamma hc',
    regularizedGaussHGFun_eq_div_Gamma hC, regularizedGaussHGFun_eq_div_Gamma hS]
  rw [h]
  field_simp
  ring

/-- A complex number with positive imaginary part is not an integer. -/
theorem not_int_of_im_pos {x : ℂ} (h : 0 < x.im) : ∀ k : ℤ, x ≠ (k : ℂ) := by
  intro k hk
  rw [hk] at h
  simp at h

/-- The regularized form of 15.10.21 for all parameters, by analytic continuation in `c`,
then `a`, then `b`. -/
theorem connLhs_eq_connRhs (a b c : ℂ) {z : ℂ} (hz : z ∈ connLens) :
    connLhs a b c z = connRhs a b c z := by
  have hVo : IsOpen ({w : ℂ | w.re < 0} ∩ {w : ℂ | 0 < w.im}) :=
    (isOpen_lt continuous_re continuous_const).inter (isOpen_lt continuous_const continuous_im)
  have hVne : ({w : ℂ | w.re < 0} ∩ {w : ℂ | 0 < w.im}).Nonempty :=
    ⟨⟨-1, 1⟩, by simp, by simp⟩
  have st1 : ∀ a b : ℂ, a.re < 0 → b.re < 0 → 0 < a.im → 0 < b.im →
      ∀ c, connLhs a b c z = connRhs a b c z := by
    intro a b ha hb ha' hb'
    have hd := differentiable_connLhs_connRhs (A := fun _ => a) (B := fun _ => b)
      (C := fun w => w) (differentiable_const _) (differentiable_const _) differentiable_id hz
    set V : Set ℂ := {w : ℂ | (a + b).re < w.re} ∩ {w : ℂ | w.re < 1} ∩
      {w : ℂ | a.im + b.im < w.im} with hV
    have hVo' : IsOpen V := ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_re continuous_const)).inter (isOpen_lt continuous_const continuous_im)
    have hVne' : V.Nonempty := by
      refine ⟨⟨(a + b).re / 2, a.im + b.im + 1⟩, ⟨?_, ?_⟩, ?_⟩ <;>
        simp only [Set.mem_ofPred_eq, add_re] at * <;> linarith
    have hEq : Set.EqOn (fun w => connLhs a b w z) (fun w => connRhs a b w z) V := by
      intro w hw
      obtain ⟨⟨h1, h2⟩, h3⟩ := hw
      simp only [Set.mem_ofPred_eq, add_re] at h1 h2 h3
      exact connLhs_eq_connRhs_base (not_int_of_im_pos ha') (not_int_of_im_pos hb')
        (not_int_of_im_pos (by linarith)) (not_int_of_im_pos (by simp; linarith))
        (not_int_of_im_pos (by simp; linarith)) (not_int_of_im_pos (by simp; linarith))
        (by simp; linarith) h2 hz
    have := eq_of_analyticOnNhd_univ_of_eqOn (fun w _ => hd.1.analyticAt w)
      (fun w _ => hd.2.analyticAt w) hVo' hVne' hEq
    exact fun c => congrFun this c
  have st2 : ∀ b : ℂ, b.re < 0 → 0 < b.im → ∀ a c, connLhs a b c z = connRhs a b c z := by
    intro b hb hb' a c
    have hd := differentiable_connLhs_connRhs (A := fun w => w) (B := fun _ => b)
      (C := fun _ => c) differentiable_id (differentiable_const _) (differentiable_const _) hz
    have := eq_of_analyticOnNhd_univ_of_eqOn (fun w _ => hd.1.analyticAt w)
      (fun w _ => hd.2.analyticAt w) hVo hVne (fun w hw => st1 w b hw.1 hb hw.2 hb' c)
    exact congrFun this a
  have hd := differentiable_connLhs_connRhs (A := fun _ => a) (B := fun w => w)
    (C := fun _ => c) (differentiable_const _) differentiable_id (differentiable_const _) hz
  have := eq_of_analyticOnNhd_univ_of_eqOn (fun w _ => hd.1.analyticAt w)
    (fun w _ => hd.2.analyticAt w) hVo hVne (fun w hw => st2 w hw.1 hw.2 a c)
  exact congrFun this b

/-- 15.10.21 with `c` only required to avoid the nonpositive integers. -/
theorem zero_first_connection_one_of_not_neg_nat {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    ₂F₁ a b c z =
      Gamma c * Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)) * oneFirst a b c z + Gamma c * Gamma (a
        + b - c) / (Gamma a * Gamma b) * oneSecond a b c z := by
  have hP := connLhs_eq_connRhs a b c (z := z) ⟨hz, hw⟩
  have hc' := hc
  have hC : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ) := by
    refine not_neg_nat_of_not_int fun k h => he (1 - k) ?_
    push_cast
    linear_combination -h
  have hS : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ) := by
    refine not_neg_nat_of_not_int fun k h => he (k - 1) ?_
    push_cast
    linear_combination h
  have hΓc := Complex.Gamma_ne_zero hc'
  have hΓC := Complex.Gamma_ne_zero hC
  have hΓS := Complex.Gamma_ne_zero hS
  have hss := sin_pi_mul_ne_zero_of_not_int he
  have e1 : Gamma (c - a - b) * Gamma (a + b - c + 1) = π / Complex.sin (π * (c - a - b)) := by
    rw [show a + b - c + 1 = 1 - (c - a - b) by ring]
    exact Complex.Gamma_mul_Gamma_one_sub _
  have e2 : Gamma (a + b - c) * Gamma (c - a - b + 1) = -(π / Complex.sin (π * (c - a - b))) := by
    rw [show c - a - b + 1 = 1 - (a + b - c) by ring, Complex.Gamma_mul_Gamma_one_sub,
      show (π : ℂ) * (a + b - c) = -(π * (c - a - b)) by ring, Complex.sin_neg, div_neg]
  have hG1 : Gamma (c - a - b) = π / Complex.sin (π * (c - a - b)) / Gamma (a + b - c + 1) := by
    rw [eq_div_iff hΓC, e1]
  have hG2 : Gamma (a + b - c) =
      -(π / Complex.sin (π * (c - a - b))) / Gamma (c - a - b + 1) := by
    rw [eq_div_iff hΓS, e2]
  simp only [connLhs, connRhs, regularizedGaussHGFun_eq_div_Gamma hc',
    regularizedGaussHGFun_eq_div_Gamma hC, regularizedGaussHGFun_eq_div_Gamma hS] at hP
  have hF : ₂F₁ a b c z = Gamma c * (π * (₂F₁ a b (a + b - c + 1) (1 - z) /
      Gamma (a + b - c + 1) * (Gamma (c - a))⁻¹ * (Gamma (c - b))⁻¹ -
      (1 - z) ^ (c - a - b) * (₂F₁ (c - a) (c - b) (c - a - b + 1) (1 - z) /
        Gamma (c - a - b + 1)) * (Gamma a)⁻¹ * (Gamma b)⁻¹)) /
      Complex.sin (π * (c - a - b)) := by
    rw [eq_div_iff hss, ← hP]
    field_simp
  rw [hF, hG1, hG2, oneFirst, oneSecond]
  ring

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a b c z = Gamma c * Gamma (c
- a - b) / (Gamma (c - a) * Gamma (c - b)) * oneFirst a b c z + Gamma c * Gamma (a + b - c) /
(Gamma a * Gamma b) * oneSecond a b c z`. -/
@[dlmf 15.10.E21]
theorem zero_first_connection_one {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    ₂F₁ a b c z =
      Gamma c * Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)) * oneFirst a b c z + Gamma c * Gamma (a
        + b - c) / (Gamma a * Gamma b) * oneSecond a b c z := by
  exact zero_first_connection_one_of_not_neg_nat (not_neg_nat_of_not_int hc) he hz hw

/-- Identity under the stated parameter and domain assumptions: `zeroSecond a b c z = Gamma (2 -
c) * Gamma (c - a - b) / (Gamma (1 - a) * Gamma (1 - b)) * oneFirst a b c z + Gamma (2 - c) *
Gamma (a + b - c) / (Gamma (a - c + 1) * Gamma (b - c + 1)) * oneSecond a b c z`. -/
@[dlmf 15.10.E22]
theorem zero_second_connection_one {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    zeroSecond a b c z =
      Gamma (2 - c) * Gamma (c - a - b) / (Gamma (1 - a) * Gamma (1 - b)) * oneFirst a b c z + Gamma (2 - c)
        * Gamma (a + b - c) / (Gamma (a - c + 1) * Gamma (b - c + 1)) * oneSecond a b c z := by
  have hz0 : z ≠ 0 := ne_zero_of_mem_connLens ⟨hz, hw⟩
  have hc' : ∀ k : ℤ, 2 - c ≠ (k : ℂ) := fun k h => hc (2 - k) (by
    push_cast; linear_combination -h)
  have he' : ∀ k : ℤ, 2 - c - (a - c + 1) - (b - c + 1) ≠ (k : ℂ) := fun k h => he k (by
    linear_combination h)
  have hC : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ) := by
    refine not_neg_nat_of_not_int fun k h => he (1 - k) ?_
    push_cast
    linear_combination -h
  have hS : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ) := by
    refine not_neg_nat_of_not_int fun k h => he (k - 1) ?_
    push_cast
    linear_combination h
  have key := zero_first_connection_one (a := a - c + 1) (b := b - c + 1) hc' he' hz hw
  rw [show 2 - c - (a - c + 1) - (b - c + 1) = c - a - b by ring,
    show 2 - c - (a - c + 1) = 1 - a by ring, show 2 - c - (b - c + 1) = 1 - b by ring,
    show a - c + 1 + (b - c + 1) - (2 - c) = a + b - c by ring] at key
  have hcancel (X : ℂ) : z ^ (1 - c) * (z ^ (c - 1) * X) = X := by
    rw [← mul_assoc, ← cpow_add _ _ hz0, show 1 - c + (c - 1) = 0 by ring, cpow_zero, one_mul]
  have h1 : z ^ (1 - c) * oneFirst (a - c + 1) (b - c + 1) (2 - c) z = oneFirst a b c z := by
    rw [oneFirst, oneFirst, show a - c + 1 + (b - c + 1) - (2 - c) + 1 = a + b - c + 1 by ring,
      euler_transformation_of_ne_neg_nat hC hw, sub_sub_cancel,
      show a + b - c + 1 - (a - c + 1) - (b - c + 1) = c - 1 by ring,
      show a + b - c + 1 - (a - c + 1) = b by ring, show a + b - c + 1 - (b - c + 1) = a by ring,
      ordinaryHypergeometric_symm b a, hcancel]
  have h2 : z ^ (1 - c) * oneSecond (a - c + 1) (b - c + 1) (2 - c) z = oneSecond a b c z := by
    rw [oneSecond, oneSecond, show 2 - c - (a - c + 1) - (b - c + 1) = c - a - b by ring,
      show 2 - c - (a - c + 1) = 1 - a by ring, show 2 - c - (b - c + 1) = 1 - b by ring,
      euler_transformation_of_ne_neg_nat hS hw, sub_sub_cancel,
      show c - a - b + 1 - (1 - a) - (1 - b) = c - 1 by ring,
      show c - a - b + 1 - (1 - a) = c - b by ring, show c - a - b + 1 - (1 - b) = c - a by ring,
      ordinaryHypergeometric_symm (c - b) (c - a), mul_left_comm, hcancel]
  rw [zeroSecond, key, ← h1, ← h2]
  ring

/-- Identity under the stated parameter and domain assumptions: `oneFirst a b c z = Gamma (1 - c)
* Gamma (a + b - c + 1) / (Gamma (a - c + 1) * Gamma (b - c + 1)) * ₂F₁ a b c z + Gamma (c -
1) * Gamma (a + b - c + 1) / (Gamma a * Gamma b) * zeroSecond a b c z`. -/
@[dlmf 15.10.E17]
theorem one_first_connection_zero {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    oneFirst a b c z =
      Gamma (1 - c) * Gamma (a + b - c + 1) / (Gamma (a - c + 1) * Gamma (b - c + 1)) * ₂F₁ a b c z + Gamma
        (c - 1) * Gamma (a + b - c + 1) / (Gamma a * Gamma b) * zeroSecond a b c z := by
  have hc' : ∀ k : ℤ, a + b - c + 1 ≠ (k : ℂ) := fun k h => he (1 - k) (by
    push_cast; linear_combination -h)
  have he' : ∀ k : ℤ, a + b - c + 1 - a - b ≠ (k : ℂ) := fun k h => hc (1 - k) (by
    push_cast; linear_combination -h)
  have key := zero_first_connection_one (a := a) (b := b) hc' he' hw (by simpa using hz)
  rw [show a + b - c + 1 - a - b = 1 - c by ring, show a + b - c + 1 - a = b - c + 1 by ring,
    show a + b - c + 1 - b = a - c + 1 by ring, show a + b - (a + b - c + 1) = c - 1 by ring]
    at key
  have h1 : oneFirst a b (a + b - c + 1) (1 - z) = ₂F₁ a b c z := by
    rw [oneFirst, show a + b - (a + b - c + 1) + 1 = c by ring, sub_sub_cancel]
  have h2 : oneSecond a b (a + b - c + 1) (1 - z) = zeroSecond a b c z := by
    rw [oneSecond, zeroSecond, sub_sub_cancel, show a + b - c + 1 - a - b = 1 - c by ring,
      show a + b - c + 1 - a = b - c + 1 by ring, show a + b - c + 1 - b = a - c + 1 by ring,
      show 1 - c + 1 = 2 - c by ring, ordinaryHypergeometric_symm]
  rw [oneFirst, key, h1, h2]
  ring

/-- Identity under the stated parameter and domain assumptions: `oneSecond a b c z = Gamma (1 - c)
* Gamma (c - a - b + 1) / (Gamma (1 - a) * Gamma (1 - b)) * ₂F₁ a b c z + Gamma (c - 1) *
Gamma (c - a - b + 1) / (Gamma (c - a) * Gamma (c - b)) * zeroSecond a b c z`. -/
@[dlmf 15.10.E18]
theorem one_second_connection_zero {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    oneSecond a b c z =
      Gamma (1 - c) * Gamma (c - a - b + 1) / (Gamma (1 - a) * Gamma (1 - b)) * ₂F₁ a b c z + Gamma (c - 1)
        * Gamma (c - a - b + 1) / (Gamma (c - a) * Gamma (c - b)) * zeroSecond a b c z := by
  have hc' : ∀ k : ℤ, a + b - c + 1 ≠ (k : ℂ) := fun k h => he (1 - k) (by
    push_cast; linear_combination -h)
  have he' : ∀ k : ℤ, a + b - c + 1 - a - b ≠ (k : ℂ) := fun k h => hc (1 - k) (by
    push_cast; linear_combination -h)
  have key := zero_second_connection_one (a := a) (b := b) hc' he' hw (by simpa using hz)
  rw [show a + b - c + 1 - a - b = 1 - c by ring, show 2 - (a + b - c + 1) = c - a - b + 1 by ring,
    show a + b - (a + b - c + 1) = c - 1 by ring, show a - (a + b - c + 1) + 1 = c - b by ring,
    show b - (a + b - c + 1) + 1 = c - a by ring] at key
  have h1 : oneFirst a b (a + b - c + 1) (1 - z) = ₂F₁ a b c z := by
    rw [oneFirst, show a + b - (a + b - c + 1) + 1 = c by ring, sub_sub_cancel]
  have h2 : oneSecond a b (a + b - c + 1) (1 - z) = zeroSecond a b c z := by
    rw [oneSecond, zeroSecond, sub_sub_cancel, show a + b - c + 1 - a - b = 1 - c by ring,
      show a + b - c + 1 - a = b - c + 1 by ring, show a + b - c + 1 - b = a - c + 1 by ring,
      show 1 - c + 1 = 2 - c by ring, ordinaryHypergeometric_symm]
  have h3 : zeroSecond a b (a + b - c + 1) (1 - z) = oneSecond a b c z := by
    rw [zeroSecond, oneSecond, show 1 - (a + b - c + 1) = c - a - b by ring,
      show a - (a + b - c + 1) + 1 = c - b by ring, show b - (a + b - c + 1) + 1 = c - a by ring,
      show 2 - (a + b - c + 1) = c - a - b + 1 by ring, ordinaryHypergeometric_symm]
  rw [← h3, key, h1, h2]
  ring

end DLMF.Hypergeometric

end
end
