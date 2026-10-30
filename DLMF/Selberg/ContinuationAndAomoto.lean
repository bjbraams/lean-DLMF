/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Selberg.Basic.Integrands
public import DLMF.Selberg.DimensionAndParameters

/-!
# Selberg continuation and the Aomoto integral

Landau-type continuation, real integrand forms and the Aomoto integral extend the Selberg
evaluation.

Source references and common attribution are retained in
`DLMF.Selberg.Basic`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter

open scoped Real Topology

noncomputable section

namespace DLMF.Selberg

/-! ### A Landau-type continuation theorem -/

/-- Uniqueness of real power-series coefficients from one-sided vanishing. -/
theorem eq_zero_of_hasSum_pow_eq_zero {e : ℕ → ℝ} {ε r : ℝ} (hr : 0 < r) (hrε : r < ε)
    (hs : Summable fun k => |e k| * r ^ k)
    (h : ∀ w : ℝ, 0 < w → w < ε → HasSum (fun k => e k * w ^ k) 0) : ∀ k, e k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  -- the shifted series vanishes
  have hshift : ∀ w : ℝ, 0 < w → w < ε → HasSum (fun j => e (j + k) * w ^ j) 0 := by
    intro w hw hwε
    have h1 := h w hw hwε
    have h2 : ∑ i ∈ Finset.range k, e i * w ^ i = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [ih i (Finset.mem_range.mp hi), zero_mul]
    rw [← hasSum_nat_add_iff' k, h2, sub_zero] at h1
    have h3 := h1.mul_left (w ^ k)⁻¹
    rw [mul_zero] at h3
    refine h3.congr_fun fun j => ?_
    rw [pow_add]
    field_simp
  have hsum' : Summable fun j => |e (j + k)| * r ^ j := by
    have := (summable_nat_add_iff k).mpr hs
    refine (this.mul_left (r ^ k)⁻¹).congr fun j => ?_
    rw [pow_add]
    field_simp
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun w j => e (j + k) * w ^ j) (g := fun j => if j = 0 then e k else 0) hsum'
    (fun j => by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp
      · simp only [Nat.pos_iff_ne_zero.mp hj, ↓reduceIte]
        have : Tendsto (fun w : ℝ => w ^ j) (𝓝[>] 0) (𝓝 0) := by
          have := ((continuous_pow j).tendsto (0 : ℝ)).mono_left
            (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
          simpa [zero_pow (Nat.pos_iff_ne_zero.mp hj)] using this
        simpa using this.const_mul (e (j + k)))
    (by
      filter_upwards [Ioo_mem_nhdsGT hr] with w hw j
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hw.1]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw.1.le hw.2.le j) (abs_nonneg _))
  rw [tsum_ite_eq] at hlim
  have hzero : (∑' j, (fun w j => e (j + k) * w ^ j) · j) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhdsGT (hr.trans hrε)] with w hw
    exact (hshift w hw.1 hw.2).tsum_eq
  exact tendsto_nhds_unique (hlim.congr' hzero) tendsto_const_nhds

/-- Absolute convergence of a Taylor series strictly inside the disc of holomorphy. -/
theorem summable_norm_taylor {R : ℂ → ℂ} {z₀ : ℂ} {ρ : ℝ}
    (hR : DifferentiableOn ℂ R (Metric.ball z₀ ρ)) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < ρ) :
    Summable fun k : ℕ => ‖(k.factorial : ℂ)⁻¹ * iteratedDeriv k R z₀‖ * r ^ k := by
  set r' := (r + ρ) / 2 with hr'
  have hr'0 : 0 < r' := by rw [hr']; linarith
  have hrr' : r < r' := by rw [hr']; linarith
  have hmem : z₀ + (r' : ℂ) ∈ Metric.ball z₀ ρ := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr'0, hr']
    linarith
  have hT := Complex.hasSum_taylorSeries_on_ball hR hmem
  have hT0 := hT.summable.tendsto_atTop_zero
  obtain ⟨B, hB⟩ := (hT0.norm).bddAbove_range
  have hterm : ∀ k : ℕ, ‖(k.factorial : ℂ)⁻¹ * iteratedDeriv k R z₀‖ * r' ^ k ≤ B := by
    intro k
    have := hB ⟨k, rfl⟩
    simp only [add_sub_cancel_left, smul_eq_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr'0] at this
    calc ‖(k.factorial : ℂ)⁻¹ * iteratedDeriv k R z₀‖ * r' ^ k
        = ‖(k.factorial : ℂ)⁻¹‖ * (r' ^ k * ‖iteratedDeriv k R z₀‖) := by rw [norm_mul]; ring
      _ ≤ B := this
  have hq : 0 ≤ r / r' := div_nonneg hr0 hr'0.le
  have hq1 : r / r' < 1 := (div_lt_one hr'0).mpr hrr'
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_geometric_of_lt_one hq hq1).mul_left B)
  calc ‖(k.factorial : ℂ)⁻¹ * iteratedDeriv k R z₀‖ * r ^ k
      = ‖(k.factorial : ℂ)⁻¹ * iteratedDeriv k R z₀‖ * r' ^ k * (r / r') ^ k := by
        rw [mul_assoc, ← mul_pow]
        congr 2
        field_simp
    _ ≤ B * (r / r') ^ k := by gcongr; exact hterm k

/-- The exponential series `∑ₖ vᵏ/k! · W (-log y)ᵏ y^{σ₁} = W y^{σ₁ - v}`. -/
theorem hasSum_mul_rpow_sub {y : ℝ} (hy : 0 < y) (W σ₁ v : ℝ) :
    HasSum (fun k : ℕ => v ^ k / k.factorial * (W * (-Real.log y) ^ k * y ^ σ₁))
      (W * y ^ (σ₁ - v)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (v * -Real.log y)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (W * y ^ σ₁)
  have hval : W * y ^ σ₁ * Real.exp (v * -Real.log y) = W * y ^ (σ₁ - v) := by
    rw [Real.rpow_sub hy, Real.rpow_def_of_pos hy v, div_eq_mul_inv, ← Real.exp_neg]
    ring_nf
  rw [hval] at h2
  refine h2.congr_fun fun k => ?_
  rw [mul_pow]
  ring

/-- Termwise expansion of `∫⁻ W Y^{σ₁ - v}` in the moments `∫⁻ W (-log Y)ᵏ Y^{σ₁}`, for
`0 < Y ≤ 1`, `W ≥ 0` and `v ≥ 0`. -/
private lemma lintegral_mul_rpow_sub_eq_tsum {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W Y : α → ℝ} (hWm : AEMeasurable W μ) (hW0 : ∀ᵐ x ∂μ, 0 ≤ W x) (hYm : AEMeasurable Y μ)
    (hY : ∀ᵐ x ∂μ, 0 < Y x ∧ Y x ≤ 1) (σ₁ : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    ∫⁻ x, ENNReal.ofReal (W x * Y x ^ (σ₁ - v)) ∂μ =
      ∑' k : ℕ, ENNReal.ofReal (v ^ k / k.factorial) *
        ∫⁻ x, ENNReal.ofReal (W x * (-Real.log (Y x)) ^ k * Y x ^ σ₁) ∂μ := by
  have hXm : AEMeasurable (fun x => -Real.log (Y x)) μ :=
    (Real.measurable_log.comp_aemeasurable hYm).neg
  have hfin_meas : ∀ k : ℕ, AEMeasurable
      (fun x => ENNReal.ofReal (W x * (-Real.log (Y x)) ^ k * Y x ^ σ₁)) μ :=
    fun k => ENNReal.measurable_ofReal.comp_aemeasurable
      ((hWm.mul (hXm.pow_const k)).mul (hYm.pow_const σ₁))
  have hterm_nn : ∀ k : ℕ, ∀ᵐ x ∂μ, 0 ≤ W x * (-Real.log (Y x)) ^ k * Y x ^ σ₁ := fun k => by
    filter_upwards [hW0, hY] with x hw hy
    exact mul_nonneg (mul_nonneg hw (pow_nonneg (neg_nonneg.mpr (Real.log_nonpos hy.1.le hy.2))
      k)) (Real.rpow_nonneg hy.1.le _)
  have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (W x * Y x ^ (σ₁ - v)) =
      ∑' k, ENNReal.ofReal (v ^ k / k.factorial) *
        ENNReal.ofReal (W x * (-Real.log (Y x)) ^ k * Y x ^ σ₁) := by
    filter_upwards [hY, ae_all_iff.2 hterm_nn] with x hy hk
    have h := hasSum_mul_rpow_sub hy.1 (W x) σ₁ v
    rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (by positivity) (hk k))
      h.summable]
    exact tsum_congr fun k => ENNReal.ofReal_mul (by positivity)
  rw [lintegral_congr_ae hpt, lintegral_tsum fun k => (hfin_meas k).const_mul _]
  exact tsum_congr fun k => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The Taylor series of `R` about the real point `σ₁`, evaluated at `σ₁ - v` with `|v| < ρ`. -/
private lemma hasSum_taylor_ofReal_sub {R : ℂ → ℂ} {σ₁ ρ : ℝ}
    (hR : DifferentiableOn ℂ R (Metric.ball (σ₁ : ℂ) ρ)) {v : ℝ} (hv : |v| < ρ) :
    HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ * iteratedDeriv k R σ₁ * ((-v) ^ k : ℝ))
      (R ((σ₁ - v : ℝ) : ℂ)) := by
  have hmem : ((σ₁ - v : ℝ) : ℂ) ∈ Metric.ball (σ₁ : ℂ) ρ := by
    rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, show σ₁ - v - σ₁ = -v by ring, abs_neg]
    exact hv
  refine (Complex.hasSum_taylorSeries_on_ball hR hmem).congr_fun fun k => ?_
  simp only [smul_eq_mul, ← Complex.ofReal_sub, show σ₁ - v - σ₁ = -v by ring]
  push_cast
  try ring

/-- **Landau's theorem** in the form needed here: if `σ ↦ ∫ W Y^σ` (with `0 < Y ≤ 1`) agrees
for `0 < σ ≤ σ₁` with a function holomorphic on the disc of radius `ρ > σ₁` about `σ₁`, then
`W Y^σ` is integrable for all `σ > σ₁ - ρ`. -/
theorem integrable_mul_rpow_of_analytic {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W Y : α → ℝ} (hW : Integrable W μ) (hW0 : ∀ᵐ x ∂μ, 0 ≤ W x) (hYm : AEMeasurable Y μ)
    (hY : ∀ᵐ x ∂μ, 0 < Y x ∧ Y x ≤ 1) {R : ℂ → ℂ} {σ₁ ρ : ℝ} (hσ₁ : 0 < σ₁)
    (hR : DifferentiableOn ℂ R (Metric.ball (σ₁ : ℂ) ρ))
    (heq : ∀ σ : ℝ, 0 < σ → σ ≤ σ₁ → ((∫ x, W x * Y x ^ σ ∂μ : ℝ) : ℂ) = R σ)
    {σ : ℝ} (hσ : σ₁ - ρ < σ) : Integrable (fun x => W x * Y x ^ σ) μ := by
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable (fun x => W x * Y x ^ s) μ := fun s =>
    hW.aestronglyMeasurable.mul (hYm.pow_const s).aestronglyMeasurable
  have hnn : ∀ s : ℝ, ∀ᵐ x ∂μ, 0 ≤ W x * Y x ^ s := fun s => by
    filter_upwards [hW0, hY] with x hx hy
    exact mul_nonneg hx (Real.rpow_nonneg hy.1.le s)
  -- nonnegative exponents
  have hpos : ∀ s : ℝ, 0 ≤ s → Integrable (fun x => W x * Y x ^ s) μ := by
    intro s hs
    refine hW.mono' (hmeas s) ?_
    filter_upwards [hW0, hY] with x hx hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx (Real.rpow_nonneg hy.1.le s))]
    exact mul_le_of_le_one_right hx (Real.rpow_le_one hy.1.le hy.2 hs)
  rcases le_or_gt 0 σ with hσ0 | hσ0
  · exact hpos σ hσ0
  -- the moments
  set X : α → ℝ := fun x => -Real.log (Y x) with hX
  set M : ℕ → ENNReal := fun k => ∫⁻ x, ENNReal.ofReal (W x * X x ^ k * Y x ^ σ₁) ∂μ with hM
  -- the lintegral identity
  have hlin : ∀ v : ℝ, 0 ≤ v → ∫⁻ x, ENNReal.ofReal (W x * Y x ^ (σ₁ - v)) ∂μ =
      ∑' k, ENNReal.ofReal (v ^ k / k.factorial) * M k := fun v hv =>
    lintegral_mul_rpow_sub_eq_tsum hW.aemeasurable hW0 hYm hY σ₁ hv
  -- finiteness of the moments
  have hlt : ∀ v : ℝ, 0 ≤ v → v < σ₁ →
      ∫⁻ x, ENNReal.ofReal (W x * Y x ^ (σ₁ - v)) ∂μ ≠ ⊤ := by
    intro v _ hv
    have hI := hpos (σ₁ - v) (by linarith)
    rw [← ofReal_integral_eq_lintegral_ofReal hI (hnn _)]
    exact ENNReal.ofReal_ne_top
  have hMfin : ∀ k, M k ≠ ⊤ := by
    intro k
    have h1 := hlt (σ₁ / 2) (by positivity) (by linarith)
    rw [hlin _ (by positivity)] at h1
    have h2 := ENNReal.le_tsum (f := fun k => ENNReal.ofReal ((σ₁ / 2) ^ k / k.factorial) * M k) k
    have h3 : ENNReal.ofReal ((σ₁ / 2) ^ k / k.factorial) * M k ≠ ⊤ :=
      ne_top_of_le_ne_top h1 h2
    have hpos' : ENNReal.ofReal ((σ₁ / 2) ^ k / k.factorial) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; positivity
    intro hk
    exact h3 (ENNReal.mul_eq_top.mpr (Or.inl ⟨hpos', hk⟩))
  set m : ℕ → ℝ := fun k => (M k).toReal with hm
  have hMm : ∀ k, M k = ENNReal.ofReal (m k) := fun k => (ENNReal.ofReal_toReal (hMfin k)).symm
  have hm0 : ∀ k, 0 ≤ m k := fun k => ENNReal.toReal_nonneg
  have hterm : ∀ v : ℝ, 0 ≤ v → ∀ k : ℕ, ENNReal.ofReal (v ^ k / k.factorial) * M k =
      ENNReal.ofReal (v ^ k / k.factorial * m k) := fun v hv k => by
    rw [hMm, ← ENNReal.ofReal_mul (by positivity)]
  -- the real expansion for `0 ≤ v < σ₁`
  have hreal : ∀ v : ℝ, 0 ≤ v → v < σ₁ →
      HasSum (fun k => v ^ k / k.factorial * m k) (∫ x, W x * Y x ^ (σ₁ - v) ∂μ) := by
    intro v hv hvσ
    have h1 := hlin v hv
    have h2 := hlt v hv hvσ
    simp_rw [hterm v hv] at h1
    rw [h1] at h2
    have hnn' : ∀ k : ℕ, 0 ≤ v ^ k / k.factorial * m k := fun k =>
      mul_nonneg (by positivity) (hm0 k)
    have hs : Summable fun k => v ^ k / k.factorial * m k :=
      (ENNReal.summable_toReal h2).congr fun k => ENNReal.toReal_ofReal (hnn' k)
    rw [integral_eq_lintegral_of_nonneg_ae (hnn _) (hmeas _), h1,
      ENNReal.tsum_toReal_eq (fun k => ENNReal.ofReal_ne_top),
      tsum_congr fun k => ENNReal.toReal_ofReal (hnn' k)]
    exact hs.hasSum
  -- the Taylor expansion of `R`
  set d : ℕ → ℂ := fun k => (k.factorial : ℂ)⁻¹ * iteratedDeriv k R σ₁ with hd
  have htaylor : ∀ v : ℝ, |v| < ρ →
      HasSum (fun k => d k * ((-v) ^ k : ℝ)) (R ((σ₁ - v : ℝ) : ℂ)) := fun v hv =>
    hasSum_taylor_ofReal_sub hR hv
  -- the coefficient identity
  set e : ℕ → ℝ := fun k => m k / k.factorial - (d k).re * (-1) ^ k with he_def
  have he : ∀ v : ℝ, 0 < v → v < σ₁ → HasSum (fun k => e k * v ^ k) 0 := by
    intro v hv hvσ
    have h1 := hreal v hv.le hvσ
    have h2 := htaylor v (by rw [abs_of_pos hv]; linarith)
    rw [← heq (σ₁ - v) (by linarith) (by linarith)] at h2
    have h4 := Complex.hasSum_re h2
    simp only [Complex.ofReal_re] at h4
    have := h1.sub h4
    rw [sub_self] at this
    refine this.congr_fun fun k => ?_
    simp only [he_def, Complex.re_mul_ofReal, neg_pow v k]
    field_simp
  have hsum_e : Summable fun k => |e k| * (σ₁ / 2) ^ k := by
    have h1 := (hreal (σ₁ / 2) (by positivity) (by linarith)).summable
    have h2 := summable_norm_taylor hR (r := σ₁ / 2) (by positivity) (by linarith)
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (h1.add h2)
    simp only [he_def]
    calc |m k / k.factorial - (d k).re * (-1) ^ k| * (σ₁ / 2) ^ k
        ≤ (|m k / k.factorial| + |(d k).re * (-1) ^ k|) * (σ₁ / 2) ^ k := by
          gcongr; exact abs_sub _ _
      _ ≤ (σ₁ / 2) ^ k / k.factorial * m k + ‖d k‖ * (σ₁ / 2) ^ k := by
          rw [abs_of_nonneg (div_nonneg (hm0 k) (by positivity)), abs_mul, abs_pow, abs_neg,
            abs_one, one_pow, mul_one, add_mul,
            show m k / k.factorial * (σ₁ / 2) ^ k = (σ₁ / 2) ^ k / k.factorial * m k by ring]
          gcongr
          exact Complex.abs_re_le_norm _
  have he0 := eq_zero_of_hasSum_pow_eq_zero (ε := σ₁) (r := σ₁ / 2) (by positivity)
    (by linarith) hsum_e he
  have hmle : ∀ k : ℕ, m k / k.factorial ≤ ‖d k‖ := by
    intro k
    have h := he0 k
    simp only [he_def, sub_eq_zero] at h
    rw [h]
    calc (d k).re * (-1) ^ k ≤ |(d k).re * (-1) ^ k| := le_abs_self _
      _ = |(d k).re| := by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
      _ ≤ ‖d k‖ := Complex.abs_re_le_norm _
  -- the conclusion
  set w := σ₁ - σ with hw
  have hw0 : 0 ≤ w := by rw [hw]; linarith
  have hwρ : w < ρ := by rw [hw]; linarith
  have hsd := summable_norm_taylor hR hw0 hwρ
  have hfinal : ∫⁻ x, ENNReal.ofReal (W x * Y x ^ σ) ∂μ < ⊤ := by
    have h := hlin w hw0
    rw [show σ₁ - w = σ by rw [hw]; ring] at h
    rw [h]
    calc ∑' k, ENNReal.ofReal (w ^ k / k.factorial) * M k
        = ∑' k, ENNReal.ofReal (w ^ k / k.factorial * m k) := tsum_congr (hterm w hw0)
      _ ≤ ∑' k, ENNReal.ofReal (‖d k‖ * w ^ k) := by
          refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
          calc w ^ k / k.factorial * m k = m k / k.factorial * w ^ k := by ring
            _ ≤ ‖d k‖ * w ^ k := by gcongr; exact hmle k
      _ = ENNReal.ofReal (∑' k, ‖d k‖ * w ^ k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsd).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  exact ⟨hmeas σ, (hasFiniteIntegral_iff_ofReal (hnn σ)).2 hfinal⟩

/-! ### Real forms of the integrand -/

/-- The squared Vandermonde product is measurable. -/
theorem measurable_vdmSq (N : ℕ) : Measurable (vdmSq N) := by
  unfold vdmSq; fun_prop

/-- The real Selberg weight is measurable. -/
theorem measurable_weightR (N : ℕ) (α β : ℝ) : Measurable (weightR N α β) := by
  unfold weightR; fun_prop

/-- The squared Vandermonde product is positive at points with distinct coordinates. -/
theorem vdmSq_pos {N : ℕ} {t : Fin N → ℝ} (ht : ∀ i j, i ≠ j → t i ≠ t j) : 0 < vdmSq N t := by
  unfold vdmSq
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => ?_
  split_ifs with hij
  · have := sub_ne_zero.mpr (ht i j (Fin.ne_of_lt hij)); positivity
  · exact one_pos

/-- On the cube, the squared Vandermonde product is at most `1`. -/
theorem vdmSq_le_one {N : ℕ} {t : Fin N → ℝ} (ht : t ∈ cube N) : vdmSq N t ≤ 1 := by
  unfold vdmSq
  refine Finset.prod_le_one₀ (fun i _ => Finset.prod_nonneg fun j _ => by split_ifs <;> positivity)
    fun i _ => Finset.prod_le_one₀ (fun j _ => by split_ifs <;> positivity) fun j _ => ?_
  split_ifs
  · have hi := ht i (Set.mem_univ _)
    have hj := ht j (Set.mem_univ _)
    have : |t i - t j| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hi.1, hi.2, hj.1, hj.2]
    calc (t i - t j) ^ 2 = |t i - t j| ^ 2 := (sq_abs _).symm
      _ ≤ 1 := pow_le_one₀ (abs_nonneg _) this
  · exact le_rfl

/-- At points with distinct coordinates, `‖Δ(t)^{2c}‖ = (Δ(t)²)^{Re c}`. -/
theorem norm_vdm_eq {N : ℕ} (c : ℂ) {t : Fin N → ℝ} (ht : ∀ i j, i ≠ j → t i ≠ t j) :
    ‖vdm N c t‖ = vdmSq N t ^ c.re := by
  unfold vdm vdmSq
  rw [norm_prod, ← Real.finsetProd_rpow _ _ fun i _ => Finset.prod_nonneg fun j _ => by
    split_ifs <;> positivity]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_prod, ← Real.finsetProd_rpow _ _ fun j _ => by split_ifs <;> positivity]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs with hij
  · have hne : t i - t j ≠ 0 := sub_ne_zero.mpr (ht i j (Fin.ne_of_lt hij))
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hne), ← sq_abs, ← Real.rpow_natCast,
      ← Real.rpow_mul (abs_nonneg _)]
    simp
  · simp

/-- On `(0,1)ᴺ`, the norm of the complex weight is the real weight at `Re a`, `Re b`. -/
theorem norm_prod_weight_eq {N : ℕ} (a b : ℂ) {t : Fin N → ℝ} (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1) :
    ‖∏ i, weight a b (t i)‖ = weightR N a.re b.re t := by
  unfold weightR
  rw [norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : 0 < 1 - t i := by linarith [(ht i).2]
  unfold weight
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ht i).1, one_sub_ofReal,
    Complex.norm_cpow_eq_rpow_re_of_pos h1]
  simp

/-- On `(0,1)ᴺ` with distinct coordinates, the norm of the Selberg integrand is the
real integrand at `Re a`, `Re b`, `Re c`. -/
theorem norm_selbergIntegrand_eq {N : ℕ} (a b c : ℂ) {t : Fin N → ℝ}
    (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1) (ht' : ∀ i j, i ≠ j → t i ≠ t j) :
    ‖selbergIntegrand N a b c t‖ = weightR N a.re b.re t * vdmSq N t ^ c.re := by
  rw [selbergIntegrand_eq, norm_mul, norm_prod_weight_eq a b ht, norm_vdm_eq c ht']

/-- The real weight is nonnegative on `(0,1)ᴺ`. -/
theorem weightR_nonneg {N : ℕ} (α β : ℝ) {t : Fin N → ℝ} (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1) :
    0 ≤ weightR N α β t :=
  Finset.prod_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (ht i).1.le _)
    (Real.rpow_nonneg (by linarith [(ht i).2]) _)

/-- For real parameters the integrand is the real nonnegative integrand. -/
theorem selbergIntegrand_ofReal {N : ℕ} (α β σ : ℝ) {t : Fin N → ℝ}
    (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1) (ht' : ∀ i j, i ≠ j → t i ≠ t j) :
    selbergIntegrand N α β σ t = ((weightR N α β t * vdmSq N t ^ σ : ℝ) : ℂ) := by
  have h := norm_selbergIntegrand_eq (α : ℂ) β σ ht ht'
  simp only [Complex.ofReal_re] at h
  rw [← h]
  -- the integrand is a nonnegative real number
  have hreal : selbergIntegrand N α β σ t =
      ((∏ i, t i ^ (α - 1) * (1 - t i) ^ (β - 1)) *
        ∏ i : Fin N, ∏ j : Fin N, if i.val < j.val then |t i - t j| ^ (2 * σ) else 1 : ℝ) := by
    unfold selbergIntegrand
    push_cast
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      have h1 : 0 ≤ 1 - t i := by linarith [(ht i).2]
      rw [Complex.ofReal_cpow (ht i).1.le, Complex.ofReal_cpow h1]
      push_cast; ring_nf
    · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
      split_ifs
      · rw [Complex.ofReal_cpow (abs_nonneg _)]; push_cast; ring_nf
      · rfl
  rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  refine mul_nonneg (Finset.prod_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (ht i).1.le _)
    (Real.rpow_nonneg (by linarith [(ht i).2]) _)) (Finset.prod_nonneg fun i _ =>
    Finset.prod_nonneg fun j _ => by split_ifs <;> positivity)

/-- For `α, β > 0`, the real weight is integrable on the cube. -/
theorem integrableOn_weightR {N : ℕ} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IntegrableOn (weightR N α β) (cube N) := by
  have h := (integrableOn_prod_cube (n := N) (integrableOn_weight (a := (α : ℂ)) (b := (β : ℂ))
    (by simpa using hα) (by simpa using hβ))).norm
  refine Integrable.congr h ?_
  filter_upwards [(ae_restrict_iff' (measurableSet_cube N)).2 (ae_cube_coords_Ioo N)] with t ht
  rw [norm_prod_weight_eq _ _ ht]
  simp

/-- Almost every point of the cube has coordinates in `(0,1)` that are pairwise distinct. -/
theorem ae_cube_good (N : ℕ) : ∀ᵐ t ∂(volume.restrict (cube N)),
    (∀ i, t i ∈ Ioo (0 : ℝ) 1) ∧ (∀ i j, i ≠ j → t i ≠ t j) ∧ t ∈ cube N := by
  filter_upwards [(ae_restrict_iff' (measurableSet_cube N)).2 (ae_cube_coords_Ioo N),
    ae_restrict_of_ae (ae_coords_ne N), ae_restrict_mem (measurableSet_cube N)] with t h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- For real parameters, the Selberg integral is the cast of the real integral. -/
theorem selbergInt_ofReal {N : ℕ} (α β σ : ℝ) :
    selbergInt N α β σ = ((∫ t in cube N, weightR N α β t * vdmSq N t ^ σ : ℝ) : ℂ) := by
  rw [selbergInt, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [ae_cube_good N] with t ht
  exact selbergIntegrand_ofReal α β σ ht.1 ht.2.1

/-- **Integrability of the Selberg integrand** on its full domain of convergence, by Landau's
theorem. -/
theorem integrableOn_weightR_mul_vdmSq_rpow {N : ℕ} {α β σ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hσ : (σ : ℂ) ∈ cDomain N α β) :
    IntegrableOn (fun t => weightR N α β t * vdmSq N t ^ σ) (cube N) := by
  have hW := integrableOn_weightR (N := N) hα hβ
  have hmeas : AEStronglyMeasurable (fun t => weightR N α β t * vdmSq N t ^ σ)
      (volume.restrict (cube N)) :=
    ((measurable_weightR N α β).mul ((measurable_vdmSq N).pow_const σ)).aestronglyMeasurable
  rcases le_or_gt 0 σ with h0 | h0
  · refine hW.mono' hmeas ?_
    filter_upwards [ae_cube_good N] with t ht
    have hW0 := weightR_nonneg α β ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hW0 (Real.rpow_nonneg
      (vdmSq_pos ht.2.1).le _))]
    exact mul_le_of_le_one_right hW0 (Real.rpow_le_one (vdmSq_pos ht.2.1).le
      (vdmSq_le_one ht.2.2) h0)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine hW.mono' hmeas (Eventually.of_forall fun t => ?_)
    simp [vdmSq, weightR]
  obtain ⟨h1, h2, h3⟩ := hσ
  simp only [Complex.ofReal_re] at h1 h2 h3
  set m := min (1 + N * σ) (min (α + ((N - 1 : ℕ) : ℝ) * σ) (β + ((N - 1 : ℕ) : ℝ) * σ))
    with hm
  have hm0 : 0 < m := lt_min h1 (lt_min h2 h3)
  have hmN : m / 2 ≥ N * (m / (2 * (N + 1))) := by
    rw [ge_iff_le, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  set s := σ - m / (2 * (N + 1)) with hs
  have hN1 : (((N - 1 : ℕ) : ℝ)) ≤ N := by exact_mod_cast Nat.sub_le N 1
  have hsdom : ∀ z : ℂ, s < z.re → z ∈ cDomain N α β := by
    intro z hz
    have hd : 0 ≤ m / (2 * (N + 1)) := by positivity
    refine ⟨?_, ?_, ?_⟩
    · have : 1 + N * σ - N * (m / (2 * (N + 1))) > 0 := by
        have h4 : m ≤ 1 + N * σ := by rw [hm]; exact min_le_left _ _
        linarith
      nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    · have : α + ((N - 1 : ℕ) : ℝ) * σ - ((N - 1 : ℕ) : ℝ) * (m / (2 * (N + 1))) > 0 := by
        have h4 : m ≤ α + ((N - 1 : ℕ) : ℝ) * σ := by
          rw [hm]; exact (min_le_right _ _).trans (min_le_left _ _)
        have : ((N - 1 : ℕ) : ℝ) * (m / (2 * (N + 1))) ≤ N * (m / (2 * (N + 1))) :=
          mul_le_mul_of_nonneg_right hN1 hd
        linarith
      simp only [Complex.ofReal_re]
      nlinarith [(Nat.cast_nonneg (N - 1) : (0 : ℝ) ≤ ((N - 1 : ℕ) : ℝ))]
    · have : β + ((N - 1 : ℕ) : ℝ) * σ - ((N - 1 : ℕ) : ℝ) * (m / (2 * (N + 1))) > 0 := by
        have h4 : m ≤ β + ((N - 1 : ℕ) : ℝ) * σ := by
          rw [hm]; exact (min_le_right _ _).trans (min_le_right _ _)
        have : ((N - 1 : ℕ) : ℝ) * (m / (2 * (N + 1))) ≤ N * (m / (2 * (N + 1))) :=
          mul_le_mul_of_nonneg_right hN1 hd
        linarith
      simp only [Complex.ofReal_re]
      nlinarith [(Nat.cast_nonneg (N - 1) : (0 : ℝ) ≤ ((N - 1 : ℕ) : ℝ))]
  have hs0 : s < 0 := by
    have : 0 < m / (2 * (N + 1)) := by positivity
    linarith
  have hball : Metric.ball ((1 : ℝ) : ℂ) (1 - s) ⊆ cDomain N α β := by
    intro z hz
    refine hsdom z ?_
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have := Complex.abs_re_le_norm (z - ((1 : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re, abs_le] at this
    linarith
  have hR := (differentiableOn_selbergRHS_c (a := α) (b := β) (by simpa using hα)
    (by simpa using hβ) hN).mono hball
  have hYm : AEMeasurable (vdmSq N) (volume.restrict (cube N)) :=
    (measurable_vdmSq N).aemeasurable
  have hsσ : s < σ := by
    have : 0 < m / (2 * (N + 1)) := by positivity
    linarith
  refine integrable_mul_rpow_of_analytic hW ?_ hYm ?_ one_pos hR ?_ (by linarith)
  · filter_upwards [ae_cube_good N] with t ht
    exact weightR_nonneg α β ht.1
  · filter_upwards [ae_cube_good N] with t ht
    exact ⟨vdmSq_pos ht.2.1, vdmSq_le_one ht.2.2⟩
  · intro σ' hσ' _
    rw [← selbergInt_ofReal, selbergInt_eq_of_re_pos (by simpa using hα) (by simpa using hβ)
      (by simpa using hσ')]

/-- The domain of convergence depends only on real parts. -/
theorem mem_cDomain_re {N : ℕ} {a b c : ℂ} (hc : c ∈ cDomain N a b) :
    (c.re : ℂ) ∈ cDomain N (a.re : ℂ) (b.re : ℂ) := by
  obtain ⟨h1, h2, h3⟩ := hc
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩

/-- For `Re a, Re b > 0`, the Selberg integral is holomorphic in `c` on the full
domain of convergence. -/
theorem differentiableOn_selbergInt_cDomain (N : ℕ) {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    DifferentiableOn ℂ (fun c => selbergInt N a b c) (cDomain N a b) := by
  unfold selbergInt
  refine DLMF.Gamma.vb_differentiableOn_integral (isOpen_cDomain N a b)
    (fun c _ => (measurable_selbergIntegrand N a b c).aestronglyMeasurable) ?_ ?_
  · filter_upwards [ae_restrict_of_ae (ae_coords_ne N)] with t ht
    exact fun c _ => (differentiableAt_selbergIntegrand_c a b ht c).differentiableWithinAt
  · intro c₀ hc₀
    obtain ⟨ε', hε', hball⟩ := Metric.isOpen_iff.mp (isOpen_cDomain N a b) c₀ hc₀
    set ε := ε' / 2 with hε
    have hε0 : 0 < ε := by positivity
    have hcl : Metric.closedBall c₀ ε ⊆ cDomain N a b :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    set σm := c₀.re - ε with hσm
    have hmem : (σm : ℂ) ∈ cDomain N (a.re : ℂ) (b.re : ℂ) := by
      have h := mem_cDomain_re (hcl (show c₀ - (ε : ℂ) ∈ Metric.closedBall c₀ ε by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]))
      simpa [hσm] using h
    refine ⟨ε, hε0, hcl, fun t => weightR N a.re b.re t * vdmSq N t ^ σm,
      integrableOn_weightR_mul_vdmSq_rpow ha hb hmem, ?_⟩
    filter_upwards [ae_cube_good N] with t ht z hz
    rw [norm_selbergIntegrand_eq a b z ht.1 ht.2.1]
    refine mul_le_mul_of_nonneg_left ?_ (weightR_nonneg _ _ ht.1)
    refine Real.rpow_le_rpow_of_exponent_ge (vdmSq_pos ht.2.1) (vdmSq_le_one ht.2.2) ?_
    have := Complex.abs_re_le_norm (z - c₀)
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have h2 : |(z - c₀).re| ≤ ε := this.trans hz
    rw [Complex.sub_re, abs_le] at h2
    linarith

/-- **Selberg's integral** on its full domain of convergence. -/
theorem selbergInt_eq {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : c ∈ cDomain N a b) : selbergInt N a b c = selbergRHS N a b c := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [selbergInt_zero, selbergRHS_zero]
  have hU := isOpen_cDomain N a b
  have hf := (differentiableOn_selbergInt_cDomain N ha hb).analyticOnNhd hU
  have hg := (differentiableOn_selbergRHS_c ha hb hN).analyticOnNhd hU
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_cDomain N a b).isPreconnected
    (z₀ := 1) (pos_mem_cDomain N ha hb (by simp)) ?_ hc
  have hV : IsOpen {c : ℂ | 0 < c.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hV.mem_nhds (by simp : (0 : ℝ) < (1 : ℂ).re)] with c hc'
  exact selbergInt_eq_of_re_pos ha hb hc'

/-! ### Aomoto's integral -/

/-- For bounded measurable `h`, `c ↦ ∫ h · Φ` is holomorphic on `Re c > 0`. -/
theorem differentiableOn_integral_mul_selbergIntegrand_c (N : ℕ) {a b : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) {h : (Fin N → ℝ) → ℂ} (hh : Measurable h)
    (hh1 : ∀ t ∈ cube N, ‖h t‖ ≤ 1) :
    DifferentiableOn ℂ (fun c => ∫ t in cube N, h t * selbergIntegrand N a b c t)
      {c | 0 < c.re} := by
  refine DLMF.Gamma.vb_differentiableOn_integral (isOpen_lt continuous_const Complex.continuous_re)
    (fun c _ => (hh.mul (measurable_selbergIntegrand N a b c)).aestronglyMeasurable) ?_ ?_
  · filter_upwards [ae_restrict_of_ae (ae_coords_ne N)] with t ht
    exact fun c _ => ((differentiableAt_selbergIntegrand_c a b ht c).const_mul (h t))
      |>.differentiableWithinAt
  · intro c₀ hc₀
    have hc₀' : 0 < c₀.re := hc₀
    refine ⟨c₀.re / 2, by positivity, fun z hz => ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      have := Complex.abs_re_le_norm (z - c₀)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have h2 : |(z - c₀).re| ≤ c₀.re / 2 := this.trans hz
      rw [Complex.sub_re, abs_le] at h2
      linarith
    refine ⟨fun t => ‖∏ i, weight a b (t i)‖,
      (integrableOn_prod_cube (n := N) (integrableOn_weight ha hb)).norm, ?_⟩
    filter_upwards [ae_restrict_mem (measurableSet_cube N)] with t ht z hz
    rw [norm_mul]
    have hz' : 0 ≤ z.re := by
      have := Complex.abs_re_le_norm (z - c₀)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have h2 : |(z - c₀).re| ≤ c₀.re / 2 := this.trans hz
      rw [Complex.sub_re, abs_le] at h2
      linarith
    calc ‖h t‖ * ‖selbergIntegrand N a b z t‖ ≤ 1 * ‖∏ i, weight a b (t i)‖ :=
          mul_le_mul (hh1 t ht) (norm_selbergIntegrand_le hz' ht) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

/-- The factors in Aomoto's formula are holomorphic in `c` on `Re c ≥ 0`. -/
theorem differentiableAt_aomotoFactor {N : ℕ} {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (j : ℕ)
    {c : ℂ} (hc : 0 ≤ c.re) : DifferentiableAt ℂ (fun c => aomotoFactor N a b c j) c := by
  unfold aomotoFactor
  have hab : 0 < (a + b).re := by simp; linarith
  refine DifferentiableAt.div (by fun_prop) (by fun_prop) fun h => ?_
  have := re_pos_add_nat_mul hab hc (2 * N - 2 - j)
  rw [h] at this; simp at this

/-- Aomoto's formula for `Re c > 0`. -/
theorem aomotoInt_eq {N m : ℕ} {a b c : ℂ} (hm : m ≤ N) (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) :
    aomotoInt N a b c (iseg N m) =
      (∏ j ∈ Finset.range m, aomotoFactor N a b c j) * selbergInt N a b c := by
  have hV : IsOpen {c : ℂ | 0 < c.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (fun c => aomotoInt N a b c (iseg N m)) {c | 0 < c.re} :=
    (differentiableOn_integral_mul_selbergIntegrand_c N ha hb (measurable_mono _)
      (fun t ht => norm_mono_le _ ht)).analyticOnNhd hV
  have hg : AnalyticOnNhd ℂ (fun c => (∏ j ∈ Finset.range m, aomotoFactor N a b c j) *
      selbergInt N a b c) {c | 0 < c.re} := by
    refine DifferentiableOn.analyticOnNhd ?_ hV
    refine DifferentiableOn.mul ?_ (differentiableOn_selbergInt_c N ha hb)
    intro c hc'
    exact (DifferentiableAt.fun_finsetProd fun j _ =>
      differentiableAt_aomotoFactor ha hb j (le_of_lt hc')).differentiableWithinAt
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt 0).isPreconnected
    (z₀ := 1) (by simp) ?_ hc
  have hW : IsOpen {c : ℂ | 1 / 2 < c.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hW.mem_nhds (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re)] with c hc'
  exact aomoto_prod ha hb (le_of_lt hc') hm

/-- Selberg's integral, AAR Theorem 8.1.1. Indexed so that `j : Fin n` corresponds to
the factor with shift `j · c`. -/
@[dlmf 5.14.E4]
theorem selberg_integral {n : ℕ} {a b c : ℂ} (hn : 0 < n)
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < 1 + n * c.re)
    (hca : 0 < a.re + (n - 1 : ℕ) * c.re)
    (hcb : 0 < b.re + (n - 1 : ℕ) * c.re) :
    ∫ t : Fin n → ℝ in Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1,
        selbergIntegrand n a b c t =
      ∏ j : Fin n,
        Gamma (a + (j : ℕ) * c) * Gamma (b + (j : ℕ) * c) * Gamma (1 + ((j : ℕ) + 1) * c) /
          (Gamma (a + b + (n + j - 1 : ℕ) * c) * Gamma (1 + c)) :=
  selbergInt_eq ha hb ⟨hc, hca, hcb⟩

/-- The `n = 1` case is the Beta integral (independent of `c`). -/
@[dlmf 5.12.E1]
theorem selberg_integral_one {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) =
      Gamma a * Gamma b / Gamma (a + b) := by
  have hG : Gamma (a + b) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp [add_re]; linarith)
  change betaIntegral a b = _
  rw [eq_div_iff_mul_eq hG, mul_comm, Gamma_mul_Gamma_eq_betaIntegral ha hb]

/-- Aomoto's extension (AAR §8.1, §8.3): inserting `∏_{i=1}^m t_i`. -/
@[dlmf 5.14.E4]
theorem aomoto_integral {n m : ℕ} {a b c : ℂ} (hm : m ≤ n)
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) :
    ∫ t : Fin n → ℝ in Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1,
        selbergIntegrand n a b c t * ∏ i : Fin m, (t (Fin.castLE hm i) : ℂ) =
      (∏ j : Fin m, (a + (n - 1 - j : ℕ) * c) / (a + b + (2 * n - 2 - j : ℕ) * c)) *
        ∏ j : Fin n,
          Gamma (a + (j : ℕ) * c) * Gamma (b + (j : ℕ) * c) * Gamma (1 + ((j : ℕ) + 1) * c) /
            (Gamma (a + b + (n + j - 1 : ℕ) * c) * Gamma (1 + c)) := by
  have h := aomotoInt_eq hm ha hb hc
  rw [selbergInt_eq ha hb (pos_mem_cDomain n ha hb hc)] at h
  have hP : ∏ j : Fin m, (a + ((n - 1 - j : ℕ) : ℂ) * c) / (a + b + ((2 * n - 2 - j : ℕ) : ℂ) * c) =
      ∏ j ∈ Finset.range m, aomotoFactor n a b c j :=
    Fin.prod_univ_eq_prod_range (fun j => aomotoFactor n a b c j) m
  rw [hP]
  change _ = _ * selbergRHS n a b c
  rw [← h]
  refine setIntegral_congr_fun (measurableSet_cube n) fun t _ => ?_
  rw [mul_comm]
  congr 1
  unfold mono iseg
  have hset : (Finset.univ.filter fun i : Fin n => i.val < m) =
      Finset.univ.map (Fin.castLEEmb hm) := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, Fin.castLEEmb_apply]
    constructor
    · intro hi; exact ⟨⟨i, hi⟩, Fin.ext rfl⟩
    · rintro ⟨j, rfl⟩; simp
  rw [hset, Finset.prod_map]
  rfl

end DLMF.Selberg

end
end
