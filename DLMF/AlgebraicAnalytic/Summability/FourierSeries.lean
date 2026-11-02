/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Summability.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.Complex.Harmonic.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Summability of Fourier series (DLMF §1.15(iii))

The Poisson kernel `P(r, θ)` (1.15.12), the Fejér kernel `K_n(θ)` (1.15.15), the Abel means
`A(r, θ)` (1.15.18) and the Cesàro means `σ_n(θ)` (1.15.21) of the Fourier series of a function
on `[0, 2π]` with coefficients `F(n) = fourierCoeffOn Real.two_pi_pos f n` (1.15.19).
Throughout, `0 < δ < π` as in DLMF.

## Main results

* `hasSum_abelPoissonKernel`, `integral_abelPoissonKernel`,
  `tendstoUniformlyOn_abelPoissonKernel`: the Poisson kernel (DLMF 1.15.12–1.15.14).
* `integral_fejerKernel`, `tendstoUniformlyOn_fejerKernel`: the Fejér kernel
  (DLMF 1.15.16–1.15.17).
* `abelMean_eq_integral`, `harmonicOnNhd_abelMean`, `fourierCesaroMean_eq_integral`: integral
  representations of the means (DLMF 1.15.20, 1.15.23).
* `tendsto_abelMean`, `tendsto_fourierCesaroMean`, `tendstoUniformly_abelMean`,
  `tendstoUniformly_fourierCesaroMean`: convergence of the means, including Fejér's theorem
  (DLMF 1.15.24).
* `differentiableOn_fourierAnalyticExtension`, `re_fourierAnalyticExtension`,
  `im_fourierAnalyticExtension`: the analytic extension (DLMF 1.15.25–1.15.28).
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology Finset ComplexConjugate

namespace DLMF.AlgebraicAnalytic

/-- DLMF 1.15.12: `P(r, θ) = ∑_{n ∈ ℤ} r^{|n|} e^{inθ}` for `0 ≤ r < 1`. -/
@[dlmf 1.15.E12]
theorem hasSum_abelPoissonKernel {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    HasSum (fun n : ℤ => ((r ^ n.natAbs : ℝ) : ℂ) * cexp (n * θ * I))
      (abelPoissonKernel r θ : ℂ) := by
  obtain ⟨q, hqd⟩ : ∃ q : ℂ, q = r * cexp (θ * I) := ⟨_, rfl⟩
  have hq : ‖q‖ = r := by
    rw [hqd, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr0]
  have hqc : ‖conj q‖ = r := by rw [Complex.norm_conj, hq]
  have h1 : HasSum (fun n : ℕ => q ^ n) (1 - q)⁻¹ :=
    hasSum_geometric_of_norm_lt_one (by rw [hq]; exact hr1)
  have h2' : HasSum (fun n : ℕ => conj q ^ n) (1 - conj q)⁻¹ :=
    hasSum_geometric_of_norm_lt_one (by rw [hqc]; exact hr1)
  have h2 : HasSum (fun n : ℕ => conj q * conj q ^ n) (conj q * (1 - conj q)⁻¹) :=
    h2'.mul_left (conj q)
  have hconj : conj q = r * cexp (-(θ * I)) := by
    rw [hqd, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
      Complex.conj_I, Complex.conj_ofReal]
    ring_nf
  have hA : HasSum (fun n : ℕ => ((r ^ ((n : ℤ)).natAbs : ℝ) : ℂ) *
      cexp (((n : ℤ) : ℂ) * θ * I)) (1 - q)⁻¹ := by
    refine h1.congr_fun fun n => ?_
    rw [hqd, mul_pow, ← Complex.exp_nat_mul, Int.natAbs_natCast]
    push_cast
    ring_nf
  have hB : HasSum (fun n : ℕ => ((r ^ (-((n : ℤ) + 1)).natAbs : ℝ) : ℂ) *
      cexp (((-((n : ℤ) + 1) : ℤ) : ℂ) * θ * I)) (conj q * (1 - conj q)⁻¹) := by
    refine h2.congr_fun fun n => ?_
    have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    rw [this, hconj, ← pow_succ', mul_pow, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have key := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ =>
      ((r ^ n.natAbs : ℝ) : ℂ) * cexp (n * θ * I)) hA hB
  convert key using 1
  have hq1 : (1 : ℂ) - q ≠ 0 := fun h => by
    have : ‖q‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
    linarith
  have hq2 : (1 : ℂ) - conj q ≠ 0 := fun h => by
    have : ‖conj q‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
    linarith
  have hsum : (1 - q)⁻¹ + conj q * (1 - conj q)⁻¹ =
      (1 - q * conj q) / (1 - (q + conj q) + q * conj q) := by
    rw [show 1 - (q + conj q) + q * conj q = (1 - q) * (1 - conj q) by ring]
    field_simp
    ring
  have hre : q.re = r * Real.cos θ := by
    rw [hqd, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [hsum, Complex.add_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, hq, hre,
    abelPoissonKernel]
  push_cast
  ring

/-- DLMF 1.15.13: `(1/2π) ∫₀^{2π} P(r, θ) dθ = 1` for `0 ≤ r < 1`. -/
@[dlmf 1.15.E13]
theorem integral_abelPoissonKernel {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..2 * Real.pi, abelPoissonKernel r θ = 1 := by
  set F : ℂ → ℂ := fun z => (1 + z) / (1 - z)
  have hFa : ∀ z ∈ Metric.closedBall (0 : ℂ) |r|, AnalyticAt ℂ F z := by
    intro z hz
    have hz1 : (1 : ℂ) - z ≠ 0 := by
      intro h
      rw [Metric.mem_closedBall, dist_zero_right, abs_of_nonneg hr0,
        ← sub_eq_zero.mp h, norm_one] at hz
      linarith
    exact (analyticAt_const.add analyticAt_id).div (analyticAt_const.sub analyticAt_id) hz1
  have hH : InnerProductSpace.HarmonicOnNhd (fun z => (F z).re) (Metric.closedBall 0 |r|) :=
    fun z hz => (hFa z hz).harmonicAt_re
  have hav := hH.circleAverage_eq
  rw [Real.circleAverage_def] at hav
  have hpt : ∀ θ, (F (circleMap 0 r θ)).re = abelPoissonKernel r θ := by
    intro θ
    simp only [F, circleMap, zero_add, abelPoissonKernel]
    rw [Complex.div_re]
    have hc : (r * cexp (θ * I)).re = r * Real.cos θ := by
      rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    have hs : (r * cexp (θ * I)).im = r * Real.sin θ := by
      rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.add_im,
      Complex.sub_im, Complex.one_im, Complex.normSq_apply, hc, hs]
    have h1 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    have hden : (1 - r * Real.cos θ) * (1 - r * Real.cos θ) +
        (0 - r * Real.sin θ) * (0 - r * Real.sin θ) = 1 - 2 * r * Real.cos θ + r ^ 2 := by
      linear_combination r ^ 2 * h1
    rw [hden, ← add_div]
    congr 1
    linear_combination (-r ^ 2) * h1
  have hF0 : (F 0).re = 1 := by simp [F]
  simp only [hpt, smul_eq_mul, hF0] at hav
  rw [one_div]
  simpa using hav

/-- The denominator of the Poisson kernel is bounded below away from `θ ∈ 2πℤ`. -/
private lemma poissonKernel_denom_ge {r θ δ : ℝ} (hr : 0 ≤ r) (hθ : θ ∈ Icc δ (2 * Real.pi - δ))
    (hδ0 : 0 < δ) :
    2 * r * (1 - Real.cos δ) ≤ 1 - 2 * r * Real.cos θ + r ^ 2 := by
  have hcos : Real.cos θ ≤ Real.cos δ := by
    rcases le_total θ Real.pi with h | h
    · exact Real.cos_le_cos_of_nonneg_of_le_pi hδ0.le h hθ.1
    · have h1 : Real.cos θ = Real.cos (2 * Real.pi - θ) := by
        rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]; ring
      rw [h1]
      exact Real.cos_le_cos_of_nonneg_of_le_pi hδ0.le (by linarith) (by linarith [hθ.2])
  nlinarith [sq_nonneg (1 - r), mul_le_mul_of_nonneg_left hcos (by linarith : 0 ≤ 2 * r)]

/-- DLMF 1.15.14: `P(r, θ) → 0` as `r → 1-`, uniformly for `θ ∈ [δ, 2π - δ]`, `0 < δ < π`. -/
@[dlmf 1.15.E14]
theorem tendstoUniformlyOn_abelPoissonKernel {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < Real.pi) :
    TendstoUniformlyOn (fun r θ => abelPoissonKernel r θ) (fun _ => 0) (𝓝[<] 1)
      (Icc δ (2 * Real.pi - δ)) := by
  have hc : 0 < 1 - Real.cos δ := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hδ.le hδ0
    rw [Real.cos_zero] at this; linarith
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- for `1/2 ≤ r < 1`: `|P| ≤ (1 - r²)/(1 - cos δ) ≤ 2(1 - r)/(1 - cos δ)`
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), 1 / 2 ≤ r ∧ 2 * (1 - r) / (1 - Real.cos δ) < ε := by
    have h1 : ∀ᶠ r in 𝓝[<] (1 : ℝ), 1 / 2 < r :=
      nhdsWithin_le_nhds (lt_mem_nhds (by norm_num))
    have h2 : Tendsto (fun r : ℝ => 2 * (1 - r) / (1 - Real.cos δ)) (𝓝[<] 1)
        (𝓝 (2 * (1 - 1) / (1 - Real.cos δ))) :=
      (((continuous_const.sub continuous_id).const_mul 2).div_const _).tendsto 1
        |>.mono_left nhdsWithin_le_nhds
    rw [sub_self, mul_zero, zero_div] at h2
    filter_upwards [h1, h2 (gt_mem_nhds hε)] with r hr1 hr2
    exact ⟨hr1.le, hr2⟩
  filter_upwards [hev, self_mem_nhdsWithin] with r ⟨hr, hrε⟩ hr1 θ hθ
  have hr1 : r < 1 := hr1
  have hden := poissonKernel_denom_ge (by linarith : (0 : ℝ) ≤ r) hθ hδ0
  have hpos : 0 < 2 * r * (1 - Real.cos δ) := by positivity
  have hnum : 0 ≤ 1 - r ^ 2 := by nlinarith
  rw [dist_zero_left, Real.norm_eq_abs, abelPoissonKernel,
    abs_of_nonneg (div_nonneg hnum (by linarith))]
  calc (1 - r ^ 2) / (1 - 2 * r * Real.cos θ + r ^ 2)
      ≤ (1 - r ^ 2) / (2 * r * (1 - Real.cos δ)) := div_le_div_of_nonneg_left hnum hpos hden
    _ ≤ 2 * (1 - r) / (1 - Real.cos δ) := by
        rw [div_le_div_iff₀ hpos hc]
        nlinarith [mul_pos hc (by linarith : (0 : ℝ) < 1 - r)]
    _ < ε := hrε

/-- The Dirichlet kernel identity `sin(θ/2) (1 + 2 ∑_{k=1}^{m} cos kθ) = sin((2m+1)θ/2)`. -/
private lemma sin_half_mul_dirichlet (θ : ℝ) (m : ℕ) :
    Real.sin (θ / 2) * (1 + 2 * ∑ k ∈ range m, Real.cos ((k + 1) * θ)) =
      Real.sin ((2 * m + 1) * θ / 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have h := Real.sin_sub_sin ((2 * (m + 1 : ℕ) + 1) * θ / 2) ((2 * m + 1) * θ / 2)
    push_cast at h ⊢
    have e1 : ((2 * (m + 1) + 1) * θ / 2 - (2 * m + 1) * θ / 2) / 2 = θ / 2 := by ring
    have e2 : ((2 * (m + 1) + 1) * θ / 2 + (2 * m + 1) * θ / 2) / 2 = (m + 1) * θ := by ring
    rw [e1, e2] at h
    linear_combination ih - h

/-- `sin² a - sin² b = sin(a + b) sin(a - b)`. -/
private lemma sin_sq_sub_sin_sq (a b : ℝ) :
    Real.sin a ^ 2 - Real.sin b ^ 2 = Real.sin (a + b) * Real.sin (a - b) := by
  rw [Real.sin_add, Real.sin_sub]
  linear_combination (-(Real.sin a ^ 2)) * Real.sin_sq_add_cos_sq b +
    (Real.sin b ^ 2) * Real.sin_sq_add_cos_sq a

/-- The Fejér kernel identity `sin²(θ/2) ((n+1) + 2 ∑_{k=1}^{n} (n+1-k) cos kθ) =
sin²((n+1)θ/2)`. -/
private lemma sin_half_sq_mul_fejer (θ : ℝ) (n : ℕ) :
    Real.sin (θ / 2) ^ 2 * ((n + 1) + 2 * ∑ k ∈ range n, ((n : ℝ) - k) * Real.cos ((k + 1) * θ)) =
      Real.sin ((n + 1) * θ / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hA : ((n + 1 : ℕ) : ℝ) + 1 + 2 * ∑ k ∈ range (n + 1),
        (((n + 1 : ℕ) : ℝ) - k) * Real.cos ((k + 1) * θ) =
        ((n + 1) + 2 * ∑ k ∈ range n, ((n : ℝ) - k) * Real.cos ((k + 1) * θ)) +
          (1 + 2 * ∑ k ∈ range (n + 1), Real.cos ((k + 1) * θ)) := by
      rw [sum_range_succ, sum_range_succ (fun k : ℕ => Real.cos ((k + 1) * θ))]
      have : ∑ k ∈ range n, (((n + 1 : ℕ) : ℝ) - k) * Real.cos ((k + 1) * θ) =
          ∑ k ∈ range n, ((n : ℝ) - k) * Real.cos ((k + 1) * θ) +
            ∑ k ∈ range n, Real.cos ((k + 1) * θ) := by
        rw [← sum_add_distrib]; refine sum_congr rfl fun k _ => ?_; push_cast; ring
      rw [this]; push_cast; ring
    rw [hA, mul_add, ih, pow_two (Real.sin (θ / 2)), mul_assoc, sin_half_mul_dirichlet]
    have := sin_sq_sub_sin_sq (((n + 1 : ℕ) + 1) * θ / 2) ((n + 1) * θ / 2)
    have e1 : ((n + 1 : ℕ) + 1) * θ / 2 + (n + 1) * θ / 2 = (2 * (n + 1 : ℕ) + 1) * θ / 2 := by
      push_cast; ring
    have e2 : ((n + 1 : ℕ) + 1) * θ / 2 - (n + 1) * θ / 2 = θ / 2 := by push_cast; ring
    rw [e1, e2] at this
    push_cast at this ⊢
    linear_combination -this

/-- DLMF 1.15.16: `(1/2π) ∫₀^{2π} K_n(θ) dθ = 1`. -/
@[dlmf 1.15.E16]
theorem integral_fejerKernel (n : ℕ) :
    (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..2 * Real.pi, fejerKernel n θ = 1 := by
  set A : ℝ → ℝ := fun θ =>
    (1 / (n + 1 : ℝ)) * ((n + 1) + 2 * ∑ k ∈ range n, ((n : ℝ) - k) * Real.cos ((k + 1) * θ))
  have hEq : ∀ θ ∈ Ioo 0 (2 * Real.pi), fejerKernel n θ = A θ := by
    intro θ hθ
    have hs : Real.sin (θ / 2) ≠ 0 := by
      apply (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])).ne'
    simp only [fejerKernel, A]
    rw [div_pow, ← sin_half_sq_mul_fejer θ n]
    field_simp
  have hint : ∫ θ in (0 : ℝ)..2 * Real.pi, fejerKernel n θ =
      ∫ θ in (0 : ℝ)..2 * Real.pi, A θ := by
    refine intervalIntegral.integral_congr_ae ?_
    have hfin : ∀ᵐ θ ∂volume, θ ∉ ({0, 2 * Real.pi} : Set ℝ) :=
      (Set.toFinite _).measure_zero volume |> measure_eq_zero_iff_ae_notMem.mp
    filter_upwards [hfin] with θ hθ hθI
    rw [uIoc_of_le (by positivity)] at hθI
    refine hEq θ ⟨hθI.1, lt_of_le_of_ne hθI.2 fun h => hθ (by simp [h])⟩
  have hcos : ∀ k : ℕ, ∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos ((k + 1) * θ) = 0 := by
    intro k
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hk, integral_cos,
      mul_zero, Real.sin_zero]
    have : ((k : ℝ) + 1) * (2 * Real.pi) = ((2 * (k + 1) : ℕ) : ℝ) * Real.pi := by
      push_cast; ring
    rw [this, Real.sin_nat_mul_pi]; simp
  have hcont : ∀ k : ℕ, IntervalIntegrable (fun θ => ((n : ℝ) - k) * Real.cos ((k + 1) * θ))
      volume 0 (2 * Real.pi) := fun k => (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [hint]
  simp only [A]
  have hsI : IntervalIntegrable (fun θ : ℝ => 2 * ∑ k ∈ range n,
      ((n : ℝ) - k) * Real.cos ((k + 1) * θ)) volume 0 (2 * Real.pi) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const
    hsI,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
      fun k _ => hcont k]
  simp only [intervalIntegral.integral_const_mul, hcos, mul_zero, Finset.sum_const_zero,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, add_zero]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- DLMF 1.15.17: `K_n(θ) → 0` as `n → ∞`, uniformly for `θ ∈ [δ, 2π - δ]`, `0 < δ < π`. -/
@[dlmf 1.15.E17]
theorem tendstoUniformlyOn_fejerKernel {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < Real.pi) :
    TendstoUniformlyOn (fun n θ => fejerKernel n θ) (fun _ => 0) atTop
      (Icc δ (2 * Real.pi - δ)) := by
  have hs : 0 < Real.sin (δ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℝ) * Real.sin (δ / 2) ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.sin (δ / 2) ^ 2) atTop atTop :=
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).atTop_mul_const
        (by positivity)
    refine h1.inv_tendsto_atTop.congr fun n => ?_
    simp [one_div]
  filter_upwards [hlim (gt_mem_nhds hε)] with n hn θ hθ
  have hsθ : Real.sin (δ / 2) ≤ Real.sin (θ / 2) := by
    rcases le_total (θ / 2) (Real.pi / 2) with h | h
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h (by linarith [hθ.1])
    · rw [← Real.sin_pi_sub (θ / 2)]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith)
        (by linarith) (by linarith [hθ.2])
  have hsθ0 : 0 < Real.sin (θ / 2) := lt_of_lt_of_le hs hsθ
  have hK0 : 0 ≤ fejerKernel n θ := by unfold fejerKernel; positivity
  rw [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg hK0]
  refine lt_of_le_of_lt ?_ hn
  have hK : fejerKernel n θ =
      Real.sin ((n + 1) * θ / 2) ^ 2 / (((n : ℝ) + 1) * Real.sin (θ / 2) ^ 2) := by
    unfold fejerKernel
    field_simp
  have hnum : Real.sin ((n + 1) * θ / 2) ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]; exact Real.abs_sin_le_one _
  rw [hK]
  calc Real.sin ((n + 1) * θ / 2) ^ 2 / (((n : ℝ) + 1) * Real.sin (θ / 2) ^ 2)
      ≤ 1 / (((n : ℝ) + 1) * Real.sin (θ / 2) ^ 2) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ 1 / (((n : ℝ) + 1) * Real.sin (δ / 2) ^ 2) := by
        apply one_div_le_one_div_of_le (by positivity)
        gcongr

/-- DLMF 1.15.20: for `f` integrable on `[0, 2π]` and `0 ≤ r < 1`,
`A(r, θ) = (1/2π) ∫₀^{2π} P(r, θ - t) f(t) dt`. -/
@[dlmf 1.15.E20]
theorem abelMean_eq_integral {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 (2 * Real.pi))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    abelMean f r θ = ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
      ∫ t in (0 : ℝ)..2 * Real.pi, (abelPoissonKernel r (θ - t) : ℂ) * f t := by
  sorry

/-- DLMF §1.15(iii): `A(r, θ)` is a harmonic function in polar coordinates: `z ↦ A(|z|, arg z)` is
harmonic in the open unit disc. -/
@[dlmf 1.15.iii]
theorem harmonicOnNhd_abelMean {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) :
    InnerProductSpace.HarmonicOnNhd (fun z : ℂ => abelMean f ‖z‖ (arg z)) (Metric.ball 0 1) := by
  sorry

/-- DLMF 1.15.23: `σ_n(θ) = (1/2π) ∫₀^{2π} K_n(θ - t) f(t) dt` for `f` integrable on
`[0, 2π]`. -/
@[dlmf 1.15.E23]
theorem fourierCesaroMean_eq_integral {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) (n : ℕ) (θ : ℝ) :
    fourierCesaroMean f n θ = ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
      ∫ t in (0 : ℝ)..2 * Real.pi, (fejerKernel n (θ - t) : ℂ) * f t := by
  sorry

/-- DLMF 1.15.24 (Abel means): if `f` is `2π`-periodic and integrable on `[0, 2π]`, then
`A(r, θ) → ½(f(θ+) + f(θ-))` as `r → 1-` at every `θ` where both one-sided limits exist. -/
@[dlmf 1.15.E24]
theorem tendsto_abelMean {f : ℝ → ℂ} (hper : Function.Periodic f (2 * Real.pi))
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) {θ : ℝ} {fp fm : ℂ}
    (hp : Tendsto f (𝓝[>] θ) (𝓝 fp)) (hm : Tendsto f (𝓝[<] θ) (𝓝 fm)) :
    Tendsto (fun r => abelMean f r θ) (𝓝[<] 1) (𝓝 ((fp + fm) / 2)) := by
  sorry

/-- DLMF 1.15.24 (Cesàro means, Fejér's theorem): if `f` is `2π`-periodic and integrable on
`[0, 2π]`, then `σ_n(θ) → ½(f(θ+) + f(θ-))` at every `θ` where both one-sided limits exist. -/
@[dlmf 1.15.E24]
theorem tendsto_fourierCesaroMean {f : ℝ → ℂ} (hper : Function.Periodic f (2 * Real.pi))
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) {θ : ℝ} {fp fm : ℂ}
    (hp : Tendsto f (𝓝[>] θ) (𝓝 fp)) (hm : Tendsto f (𝓝[<] θ) (𝓝 fm)) :
    Tendsto (fun n => fourierCesaroMean f n θ) atTop (𝓝 ((fp + fm) / 2)) := by
  sorry

/-- DLMF §1.15(iii), after 1.15.24: for continuous `2π`-periodic `f` the Abel means converge to
`f` uniformly as `r → 1-`. -/
@[dlmf 1.15.E24]
theorem tendstoUniformly_abelMean {f : ℝ → ℂ} (hper : Function.Periodic f (2 * Real.pi))
    (hf : Continuous f) :
    TendstoUniformly (fun r θ => abelMean f r θ) f (𝓝[<] 1) := by
  sorry

/-- DLMF §1.15(iii), after 1.15.24 (Fejér): for continuous `2π`-periodic `f` the Cesàro means
converge to `f` uniformly. -/
@[dlmf 1.15.E24]
theorem tendstoUniformly_fourierCesaroMean {f : ℝ → ℂ} (hper : Function.Periodic f (2 * Real.pi))
    (hf : Continuous f) :
    TendstoUniformly (fun n θ => fourierCesaroMean f n θ) f atTop := by
  sorry

/-- DLMF 1.15.25–1.15.27: for real `f` integrable on `[0, 2π]` with Fourier series 1.15.25, the
series `F(0) + 2 ∑_{n≥1} F(n) zⁿ` converges in the unit disc to an analytic function `G`
extending 1.15.26. -/
@[dlmf 1.15.E25, dlmf 1.15.E26, dlmf 1.15.E27]
theorem differentiableOn_fourierAnalyticExtension {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) :
    (∀ z ∈ Metric.ball (0 : ℂ) 1, Summable fun n : ℕ =>
      fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) (n + 1 : ℕ) * z ^ (n + 1)) ∧
    DifferentiableOn ℂ (fourierAnalyticExtension fun t => (f t : ℂ)) (Metric.ball 0 1) := by
  sorry

/-- DLMF §1.15(iii), 1.15.27: for real `f`, the real part `u` of `G(re^{iθ})` is the Abel (Poisson)
sum `A(r, θ)` (which is real). -/
@[dlmf 1.15.E27]
theorem re_fourierAnalyticExtension {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (θ : ℝ) :
    ((fourierAnalyticExtension (fun t => (f t : ℂ)) (r * cexp (θ * I))).re : ℂ) =
      abelMean (fun t => (f t : ℂ)) r θ := by
  sorry

/-- DLMF 1.15.28: for real `f`, the imaginary part `v` of `G(re^{iθ})` is
`-∑_{n ∈ ℤ} i (sign n) F(n) r^{|n|} e^{inθ}`. -/
@[dlmf 1.15.E28]
theorem im_fourierAnalyticExtension {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (θ : ℝ) :
    ((fourierAnalyticExtension (fun t => (f t : ℂ)) (r * cexp (θ * I))).im : ℂ) =
      -∑' n : ℤ, I * (Int.sign n : ℂ) * fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) n *
        ((r ^ n.natAbs : ℝ) : ℂ) * cexp (n * θ * I) := by
  sorry

end DLMF.AlgebraicAnalytic
