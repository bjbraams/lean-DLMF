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
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.MeasureTheory.Integral.PeakFunction

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
  set F : ℤ → ℝ → ℂ := fun n t => ((r ^ n.natAbs : ℝ) : ℂ) * cexp (n * (θ - t) * I) * f t
    with hFdef
  have hgeo : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one hr0 hr1
  have hsum : Summable fun n : ℤ => r ^ n.natAbs :=
    Summable.of_nat_of_neg (by simpa using hgeo) (by simpa using hgeo)
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (uIoc 0 (2 * Real.pi))) := by
    intro n
    have : IntervalIntegrable (fun t => ((r ^ n.natAbs : ℝ) : ℂ) * cexp (n * (θ - t) * I) * f t)
        volume 0 (2 * Real.pi) := by
      have h := hf.continuousOn_mul (g := fun t : ℝ =>
        ((r ^ n.natAbs : ℝ) : ℂ) * cexp (n * (θ - t) * I)) (by fun_prop)
      simpa only using h
    exact (intervalIntegrable_iff.1 this).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ t ∂volume, t ∈ uIoc 0 (2 * Real.pi) →
      ‖F n t‖ ≤ r ^ n.natAbs * ‖f t‖ := by
    intro n
    refine Eventually.of_forall fun t _ => ?_
    simp only [hFdef, norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hr0 _)]
    rw [show (n : ℂ) * ((θ : ℂ) - t) * I = ((n * (θ - t) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hlim : ∀ᵐ t ∂volume, t ∈ uIoc 0 (2 * Real.pi) →
      HasSum (fun n => F n t) ((abelPoissonKernel r (θ - t) : ℂ) * f t) := by
    refine Eventually.of_forall fun t _ => ?_
    have h := (hasSum_abelPoissonKernel hr0 hr1 (θ - t)).mul_right (f t)
    refine h.congr_fun fun n => ?_
    simp only [hFdef]
    push_cast
    ring_nf
  have hint : IntervalIntegrable (fun t => ∑' n : ℤ, r ^ n.natAbs * ‖f t‖) volume 0
      (2 * Real.pi) := by
    simp_rw [tsum_mul_right]
    exact hf.norm.const_mul _
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n t => r ^ n.natAbs * ‖f t‖) hmeas hbound
    (Eventually.of_forall fun t _ => hsum.mul_right _) hint hlim
  unfold abelMean
  rw [← key.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [fourierCoeffOn_two_pi_eq]
  simp only [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [hFdef]
  have he : cexp (-(n * t * I)) * cexp (n * θ * I) = cexp (n * (θ - t) * I) := by
    rw [← Complex.exp_add]; ring_nf
  linear_combination (((r ^ n.natAbs : ℝ) : ℂ) * ((2 * Real.pi : ℝ)⁻¹ : ℂ) * f t) * he

/-- The Fourier coefficients are bounded by `(2π)⁻¹ ∫₀^{2π} |f|`. -/
private lemma norm_fourierCoeffOn_le (f : ℝ → ℂ) (n : ℤ) :
    ‖fourierCoeffOn Real.two_pi_pos f n‖ ≤
      (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi, ‖f t‖ := by
  rw [fourierCoeffOn_two_pi_eq, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans_eq ?_
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [norm_mul]
  rw [show -((n : ℂ) * t * I) = ((-(n * t) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- A power series `∑ cₙ w^{n+1}` with bounded coefficients is holomorphic in the unit disc. -/
private lemma differentiableOn_tsum_mul_pow_succ {c : ℕ → ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hc : ∀ n, ‖c n‖ ≤ C) :
    DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, c n * w ^ (n + 1)) (Metric.ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz
  set ρ := (‖z‖ + 1) / 2
  have hρ1 : ρ < 1 := by simp only [ρ]; linarith
  have hzρ : ‖z‖ < ρ := by simp only [ρ]; linarith
  have hρ0 : 0 ≤ ρ := (norm_nonneg z).trans hzρ.le
  have hd : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, c n * w ^ (n + 1))
      (Metric.ball 0 ρ) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (u := fun n : ℕ => C * ρ ^ (n + 1)) ?_
      (fun n => (differentiable_const _ |>.mul (differentiable_id.pow _)).differentiableOn)
      Metric.isOpen_ball fun n w hw => ?_
    · exact ((summable_geometric_of_lt_one hρ0 hρ1).mul_left (C * ρ)).congr fun n => by ring
    · rw [mem_ball_zero_iff] at hw
      rw [norm_mul, norm_pow]
      exact mul_le_mul (hc n) (pow_le_pow_left₀ (norm_nonneg _) hw.le _) (by positivity) hC0
  exact (hd.differentiableAt (Metric.isOpen_ball.mem_nhds (by simpa using hzρ)))
    |>.differentiableWithinAt

/-- DLMF §1.15(iii): `A(r, θ)` is a harmonic function in polar coordinates: `z ↦ A(|z|, arg z)` is
harmonic in the open unit disc. Stronger than DLMF, which assumes `f` integrable on `[0, 2π]`. -/
@[dlmf 1.15.iii]
theorem harmonicOnNhd_abelMean' (f : ℝ → ℂ) :
    InnerProductSpace.HarmonicOnNhd (fun z : ℂ => abelMean f ‖z‖ (arg z)) (Metric.ball 0 1) := by
  set F : ℤ → ℂ := fourierCoeffOn Real.two_pi_pos f with hFdef
  set C := (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi, ‖f t‖
  have hC0 : 0 ≤ C := mul_nonneg (by positivity)
    (intervalIntegral.integral_nonneg Real.two_pi_pos.le fun _ _ => norm_nonneg _)
  have hFC : ∀ n, ‖F n‖ ≤ C := norm_fourierCoeffOn_le f
  set G1 : ℂ → ℂ := fun w => ∑' n : ℕ, F (n + 1 : ℕ) * w ^ (n + 1)
  set G2 : ℂ → ℂ := fun w => ∑' n : ℕ, conj (F (-(n + 1 : ℕ))) * w ^ (n + 1)
  have hG1 := differentiableOn_tsum_mul_pow_succ hC0 (c := fun n => F (n + 1 : ℕ)) fun n => hFC _
  have hG2 := differentiableOn_tsum_mul_pow_succ hC0 (c := fun n => conj (F (-(n + 1 : ℕ))))
    fun n => by rw [Complex.norm_conj]; exact hFC _
  have hsum : ∀ c : ℕ → ℂ, (∀ n, ‖c n‖ ≤ C) → ∀ w : ℂ, ‖w‖ < 1 →
      Summable fun n : ℕ => c n * w ^ (n + 1) := by
    intro c hc w hw
    refine Summable.of_norm_bounded (g := fun n : ℕ => C * ‖w‖ ^ (n + 1)) ?_ fun n => ?_
    · exact ((summable_geometric_of_lt_one (norm_nonneg _) hw).mul_left (C * ‖w‖)).congr
        fun n => by ring
    · rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right (hc n) (by positivity)
  have heq : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      abelMean f ‖z‖ (arg z) = G1 z + F 0 + conj (G2 z) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    set a : ℤ → ℂ := fun n => ((‖z‖ ^ n.natAbs : ℝ) : ℂ) * F n * cexp (n * arg z * I) with ha
    have hz' : ((‖z‖ : ℝ) : ℂ) * cexp ((arg z : ℝ) * I) = z := Complex.norm_mul_exp_arg_mul_I z
    have hpow : ∀ m : ℕ, ((‖z‖ ^ m : ℝ) : ℂ) * cexp ((m : ℤ) * arg z * I) = z ^ m := by
      intro m
      conv_rhs => rw [← hz']
      rw [mul_pow, ← Complex.exp_nat_mul]
      push_cast
      ring_nf
    have hpowc : ∀ m : ℕ, ((‖z‖ ^ m : ℝ) : ℂ) * cexp (-((m : ℤ) * arg z * I)) = conj z ^ m := by
      intro m
      have := congrArg conj (hpow m)
      rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_pow] at this
      rw [← this]
      simp [map_mul, Complex.conj_I]
    have h1 : HasSum (fun n : ℕ => a (n + 1)) (G1 z) := by
      refine (hsum _ (fun n => hFC _) z hz).hasSum.congr_fun fun n => ?_
      simp only [ha]
      have : ((n : ℤ) + 1).natAbs = n + 1 := by omega
      rw [this, ← hpow (n + 1)]
      push_cast
      ring
    have h2 : HasSum (fun n : ℕ => a (-(n + 1))) (conj (G2 z)) := by
      refine (Complex.hasSum_conj'.mpr (hsum _ (fun n => by rw [Complex.norm_conj]; exact hFC _)
        z hz).hasSum).congr_fun fun n => ?_
      simp only [ha, map_mul, map_pow, Complex.conj_conj]
      have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
      rw [this, ← hpowc (n + 1)]
      push_cast
      ring_nf
    have h := (h1.of_add_one_of_neg_add_one h2).tsum_eq
    change ∑' n : ℤ, a n = _
    rw [h]
    simp [ha]
  intro z hz
  have hopen : Metric.ball (0 : ℂ) 1 ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds hz
  have hh : InnerProductSpace.HarmonicAt (fun w => G1 w + F 0 + conj (G2 w)) z :=
    (((hG1.analyticAt hopen).harmonicAt).add (InnerProductSpace.harmonicAt_const _)).add
      (hG2.analyticAt hopen).harmonicAt_conj
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).2 hh
  filter_upwards [hopen] with w hw using heq w hw

/-- DLMF §1.15(iii): `A(r, θ)` is a harmonic function in polar coordinates: `z ↦ A(|z|, arg z)` is
harmonic in the open unit disc. -/
@[dlmf 1.15.iii]
theorem harmonicOnNhd_abelMean {f : ℝ → ℂ} (_hf : IntervalIntegrable f volume 0 (2 * Real.pi)) :
    InnerProductSpace.HarmonicOnNhd (fun z : ℂ => abelMean f ‖z‖ (arg z)) (Metric.ball 0 1) :=
  harmonicOnNhd_abelMean' f

/-- The Dirichlet kernel as a finite exponential sum. -/
private lemma sum_cexp_Icc (m : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.Icc (-(m : ℤ)) m, cexp (k * x * I) =
      ((1 + 2 * ∑ j ∈ range m, Real.cos ((j + 1) * x) : ℝ) : ℂ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hset : Finset.Icc (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ) =
        insert (-((m + 1 : ℕ) : ℤ)) (insert ((m + 1 : ℕ) : ℤ) (Finset.Icc (-(m : ℤ)) m)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    have h1 : ((m + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(m : ℤ)) m := by simp
    have h2 : -((m + 1 : ℕ) : ℤ) ∉ insert ((m + 1 : ℕ) : ℤ) (Finset.Icc (-(m : ℤ)) m) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega
    rw [hset, sum_insert h2, sum_insert h1, ih, sum_range_succ]
    have hc : (Real.cos ((m + 1 : ℝ) * x) : ℂ) =
        (cexp ((m + 1 : ℝ) * x * I) + cexp (-((m + 1 : ℝ) * x * I))) / 2 := by
      rw [Complex.ofReal_cos, Complex.cos]; push_cast; ring_nf
    push_cast at hc ⊢
    rw [hc]
    ring_nf

/-- The sum of the first `n + 1` Dirichlet kernels. -/
private lemma sum_range_dirichlet (n : ℕ) (x : ℝ) :
    ∑ m ∈ range (n + 1), (1 + 2 * ∑ j ∈ range m, Real.cos ((j + 1) * x)) =
      (n + 1) + 2 * ∑ k ∈ range n, ((n : ℝ) - k) * Real.cos ((k + 1) * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun k : ℕ => ((n + 1 : ℕ) - (k : ℝ)) * _)]
    have : ∑ k ∈ range n, (((n + 1 : ℕ) : ℝ) - k) * Real.cos ((k + 1) * x) =
        ∑ k ∈ range n, ((n : ℝ) - k) * Real.cos ((k + 1) * x) +
          ∑ k ∈ range n, Real.cos ((k + 1) * x) := by
      rw [← sum_add_distrib]; refine sum_congr rfl fun k _ => ?_; push_cast; ring
    rw [this, sum_range_succ (fun j : ℕ => Real.cos ((j + 1) * x))]
    push_cast
    ring

/-- The partial sum `s_m(θ)` as an integral against the Dirichlet kernel. -/
private lemma fourierPartialSum_eq_integral {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) (m : ℕ) (θ : ℝ) :
    fourierPartialSum f m θ = ((2 * Real.pi : ℝ)⁻¹ : ℂ) * ∫ t in (0 : ℝ)..2 * Real.pi,
      f t * ((1 + 2 * ∑ j ∈ range m, Real.cos ((j + 1) * (θ - t)) : ℝ) : ℂ) := by
  unfold fourierPartialSum
  simp_rw [fourierCoeffOn_two_pi_eq]
  conv_lhs => arg 2; ext k; rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  have hint : ∀ k ∈ Finset.Icc (-(m : ℤ)) m, IntervalIntegrable
      (fun t => f t * cexp (-(k * t * I)) * cexp (k * θ * I)) volume 0 (2 * Real.pi) :=
    fun k _ => (hf.mul_continuousOn (by fun_prop)).mul_const _
  simp_rw [← intervalIntegral.integral_mul_const]
  rw [← intervalIntegral.integral_finsetSum hint]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [← sum_cexp_Icc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- DLMF 1.15.23: `σ_n(θ) = (1/2π) ∫₀^{2π} K_n(θ - t) f(t) dt` for `f` integrable on
`[0, 2π]`. -/
@[dlmf 1.15.E23]
theorem fourierCesaroMean_eq_integral {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) (n : ℕ) (θ : ℝ) :
    fourierCesaroMean f n θ = ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
      ∫ t in (0 : ℝ)..2 * Real.pi, (fejerKernel n (θ - t) : ℂ) * f t := by
  unfold fourierCesaroMean
  simp_rw [fourierPartialSum_eq_integral hf]
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum (fun m _ =>
    hf.mul_continuousOn (by fun_prop)), mul_div_assoc, ← intervalIntegral.integral_div]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  have hnull : ∀ᵐ t ∂volume, Real.sin ((θ - t) / 2) ≠ 0 := by
    have hc : {t : ℝ | Real.sin ((θ - t) / 2) = 0} ⊆
        Set.range (fun k : ℤ => θ - 2 * (k * Real.pi)) := by
      intro t ht
      obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 ht
      exact ⟨k, by linarith⟩
    have := ((Set.countable_range _).mono hc).measure_zero volume
    exact measure_eq_zero_iff_ae_notMem.1 this
  filter_upwards [hnull] with t ht _
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, sum_range_dirichlet]
  have hK : fejerKernel n (θ - t) = (1 / (n + 1 : ℝ)) *
      ((n + 1) + 2 * ∑ k ∈ range n, ((n : ℝ) - k) * Real.cos ((k + 1) * (θ - t))) := by
    simp only [fejerKernel]
    rw [div_pow, ← sin_half_sq_mul_fejer (θ - t) n]
    field_simp
  rw [hK]
  generalize ((n : ℝ) + 1 + 2 * ∑ k ∈ range n, ((n : ℝ) - k) * Real.cos ((k + 1) * (θ - t))) = E
  push_cast
  field_simp

/-- A bounded measurable real kernel times an interval integrable function. -/
private lemma intervalIntegrable_kernel_mul {k : ℝ → ℝ} (hkm : Measurable k) {C : ℝ}
    (hkC : ∀ s, |k s| ≤ C) {g : ℝ → ℂ} {a b : ℝ} (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun s => (k s : ℂ) * g s) volume a b := by
  have hm : AEStronglyMeasurable (fun s => (k s : ℂ)) volume :=
    (Complex.measurable_ofReal.comp hkm).aestronglyMeasurable
  have hb : ∀ s, ‖(k s : ℂ)‖ ≤ C := fun s => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hkC s
  exact ⟨hg.1.bdd_mul hm.restrict (Eventually.of_forall hb),
    hg.2.bdd_mul hm.restrict (Eventually.of_forall hb)⟩

/-- The mean of `f` against an even `2π`-periodic kernel, folded onto `(0, π]`. -/
private lemma integral_kernel_mul_eq {k : ℝ → ℝ} (hkp : Function.Periodic k (2 * Real.pi))
    (hke : ∀ s, k (-s) = k s) (hkm : Measurable k) {C : ℝ} (hkC : ∀ s, |k s| ≤ C)
    {f : ℝ → ℂ} (hper : Function.Periodic f (2 * Real.pi))
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) (θ : ℝ) :
    ((2 * Real.pi : ℝ)⁻¹ : ℂ) * ∫ t in (0 : ℝ)..2 * Real.pi, (k (θ - t) : ℂ) * f t =
      ∫ s in Ioc 0 Real.pi, (k s / Real.pi) • ((f (θ + s) + f (θ - s)) / 2) := by
  have hpi := Real.pi_pos
  have hfi : ∀ a b, IntervalIntegrable f volume a b :=
    hper.intervalIntegrable₀ (by positivity) hf
  set h : ℝ → ℂ := fun s => (k s : ℂ) * f (θ - s) with hh
  have hhp : Function.Periodic h (2 * Real.pi) := by
    intro s
    simp only [hh, hkp s, show θ - (s + 2 * Real.pi) = θ - s - 2 * Real.pi by ring,
      hper.sub_eq]
  have hhi : ∀ a b, IntervalIntegrable h volume a b := fun a b =>
    intervalIntegrable_kernel_mul hkm hkC
      (by simpa using ((hfi (θ - b) (θ - a)).comp_sub_left θ).symm)
  have h1 : ∫ t in (0 : ℝ)..2 * Real.pi, (k (θ - t) : ℂ) * f t =
      ∫ s in θ - 2 * Real.pi..θ, h s := by
    have := intervalIntegral.integral_comp_sub_left h θ (a := 0) (b := 2 * Real.pi)
    rw [sub_zero] at this
    rw [← this]
    simp [hh]
  have h2 : ∫ s in θ - 2 * Real.pi..θ, h s = ∫ s in -Real.pi..Real.pi, h s := by
    have := hhp.intervalIntegral_add_eq (θ - 2 * Real.pi) (-Real.pi)
    rwa [sub_add_cancel, show -Real.pi + 2 * Real.pi = Real.pi by ring] at this
  have h3 : ∫ s in -Real.pi..Real.pi, h s =
      ∫ s in (0 : ℝ)..Real.pi, (k s : ℂ) * (f (θ + s) + f (θ - s)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hhi _ _) (hhi _ _) (b := 0)]
    have hneg := intervalIntegral.integral_comp_neg (a := 0) (b := Real.pi) h
    rw [neg_zero] at hneg
    have hneg' : ∫ s in -Real.pi..0, h s =
        ∫ s in (0 : ℝ)..Real.pi, (k s : ℂ) * f (θ + s) := by
      rw [← hneg]
      simp only [hh, hke, sub_neg_eq_add]
    have hpl : IntervalIntegrable (fun s => (k s : ℂ) * f (θ + s)) volume 0 Real.pi :=
      intervalIntegrable_kernel_mul hkm hkC
        (by simpa using (hfi (θ + 0) (θ + Real.pi)).comp_add_left θ)
    rw [hneg', ← intervalIntegral.integral_add hpl (hhi _ _)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hh]
    ring
  rw [h1, h2, h3, intervalIntegral.integral_of_le hpi.le, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [Complex.real_smul]
  push_cast
  field_simp

/-- An even `2π`-periodic kernel with `(1/2π) ∫₀^{2π} k = 1` has `∫_{(0, π]} k/π = 1`. -/
private lemma integral_Ioc_kernel_div {k : ℝ → ℝ} (hkp : Function.Periodic k (2 * Real.pi))
    (hke : ∀ s, k (-s) = k s) (hkm : Measurable k) {C : ℝ} (hkC : ∀ s, |k s| ≤ C)
    (hk1 : 1 / (2 * Real.pi) * ∫ θ in (0 : ℝ)..2 * Real.pi, k θ = 1) :
    ∫ s in Ioc 0 Real.pi, k s / Real.pi = 1 := by
  have h := integral_kernel_mul_eq hkp hke hkm hkC (f := fun _ => (1 : ℂ))
    (fun _ => rfl) intervalIntegrable_const 0
  simp only [zero_sub, hke, mul_one, Complex.real_smul] at h
  rw [show ((1 : ℂ) + 1) / 2 = 1 by norm_num] at h
  simp only [mul_one] at h
  rw [intervalIntegral.integral_ofReal, integral_complex_ofReal, ← ofReal_inv, ← ofReal_mul] at h
  have h' := Complex.ofReal_injective h
  rw [← h', ← hk1, one_div]

/-- **Approximate identity on the circle.** For even `2π`-periodic nonnegative kernels with mean
`1` that tend to `0` uniformly away from `2πℤ`, the means of a periodic integrable `f` tend to
`(f(θ+) + f(θ-))/2` at every `θ` where both one-sided limits exist. -/
private lemma tendsto_kernel_mean {ι : Type*} {l : Filter ι} {k : ι → ℝ → ℝ}
    (hkp : ∀ i, Function.Periodic (k i) (2 * Real.pi)) (hke : ∀ i s, k i (-s) = k i s)
    (hkb : ∀ᶠ i in l, Measurable (k i) ∧ (∃ C, ∀ s, |k i s| ≤ C) ∧ ∀ s, 0 ≤ k i s)
    (hk1 : ∀ᶠ i in l, 1 / (2 * Real.pi) * ∫ θ in (0 : ℝ)..2 * Real.pi, k i θ = 1)
    (hku : ∀ δ, 0 < δ → δ < Real.pi →
      TendstoUniformlyOn k (fun _ => 0) l (Icc δ (2 * Real.pi - δ)))
    {f : ℝ → ℂ} (hper : Function.Periodic f (2 * Real.pi))
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) {θ : ℝ} {fp fm : ℂ}
    (hp : Tendsto f (𝓝[>] θ) (𝓝 fp)) (hm : Tendsto f (𝓝[<] θ) (𝓝 fm)) :
    Tendsto (fun i => ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
      ∫ t in (0 : ℝ)..2 * Real.pi, (k i (θ - t) : ℂ) * f t) l (𝓝 ((fp + fm) / 2)) := by
  have hpi := Real.pi_pos
  have hfi : ∀ a b, IntervalIntegrable f volume a b :=
    hper.intervalIntegrable₀ (by positivity) hf
  set g : ℝ → ℂ := fun s => (f (θ + s) + f (θ - s)) / 2 with hg
  have hmg : IntegrableOn g (Ioc 0 Real.pi) := by
    have h1 : IntervalIntegrable (fun s => f (θ + s)) volume 0 Real.pi := by
      simpa using (hfi (θ + 0) (θ + Real.pi)).comp_add_left θ
    have h2 : IntervalIntegrable (fun s => f (θ - s)) volume 0 Real.pi := by
      simpa using ((hfi (θ - Real.pi) (θ - 0)).comp_sub_left θ).symm
    have := (h1.add h2).div_const 2
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).1 this
  have hcg : Tendsto g (𝓝[Ioc 0 Real.pi] 0) (𝓝 ((fp + fm) / 2)) := by
    have hplus : Tendsto (fun s : ℝ => θ + s) (𝓝[Ioc 0 Real.pi] 0) (𝓝[>] θ) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun s : ℝ => θ + s) (𝓝 0) (𝓝 (θ + 0)) :=
          (continuous_const.add continuous_id).tendsto 0
        rw [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact lt_add_of_pos_right θ hs.1
    have hminus : Tendsto (fun s : ℝ => θ - s) (𝓝[Ioc 0 Real.pi] 0) (𝓝[<] θ) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun s : ℝ => θ - s) (𝓝 0) (𝓝 (θ - 0)) :=
          (continuous_const.sub continuous_id).tendsto 0
        rw [sub_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact sub_lt_self θ hs.1
    exact ((hp.comp hplus).add (hm.comp hminus)).div_const 2
  have hlφ : ∀ u : Set ℝ, IsOpen u → (0 : ℝ) ∈ u →
      TendstoUniformlyOn (fun i s => k i s / Real.pi) 0 l (Ioc 0 Real.pi \ u) := by
    intro u hu h0u
    obtain ⟨ε, hε, hεu⟩ := Metric.isOpen_iff.1 hu 0 h0u
    set δ := min (ε / 2) (Real.pi / 2) with hδ
    have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
    have hδπ : δ < Real.pi := (min_le_right _ _).trans_lt (by linarith)
    have hsub : Ioc 0 Real.pi \ u ⊆ Icc δ (2 * Real.pi - δ) := by
      intro s ⟨hs, hsu⟩
      have hsε : ε ≤ s := by
        by_contra hlt
        exact hsu (hεu (by rw [Metric.mem_ball, Real.dist_eq, sub_zero,
          abs_of_pos hs.1]; linarith))
      exact ⟨(min_le_left _ _).trans (by linarith), by linarith [hs.2]⟩
    have hu' := (hku δ hδ0 hδπ).mono hsub
    rw [Metric.tendstoUniformlyOn_iff] at hu' ⊢
    intro ε' hε'
    filter_upwards [hu' (ε' * Real.pi) (by positivity)] with i hi s hs
    have := hi s hs
    rw [Real.dist_eq] at this ⊢
    simp only [Pi.zero_apply, zero_sub, abs_neg, abs_div, abs_of_pos hpi] at this ⊢
    rwa [div_lt_iff₀ hpi]
  have hpeak := tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto (μ := volume)
    (φ := fun i s => k i s / Real.pi) (x₀ := 0) measurableSet_Ioc measurableSet_Ioc
    subset_rfl self_mem_nhdsWithin measure_Ioc_lt_top.ne
    (hkb.mono fun i hi s _ => div_nonneg (hi.2.2 s) hpi.le) hlφ
    (tendsto_const_nhds.congr' (by
      filter_upwards [hkb, hk1] with i hi hi1
      obtain ⟨C, hC⟩ := hi.2.1
      exact (integral_Ioc_kernel_div (hkp i) (hke i) hi.1 hC hi1).symm))
    (hkb.mono fun i hi => (hi.1.div_const _).aestronglyMeasurable) hmg hcg
  refine hpeak.congr' ?_
  filter_upwards [hkb] with i hi
  obtain ⟨C, hC⟩ := hi.2.1
  exact (integral_kernel_mul_eq (hkp i) (hke i) hi.1 hC hper hf θ).symm

/-- A continuous `2π`-periodic function is uniformly continuous at scales below `π`. -/
private lemma exists_uniform_periodic {f : ℝ → ℂ} (hper : Function.Periodic f (2 * Real.pi))
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ δ < Real.pi ∧ ∀ θ s, |s| ≤ δ → ‖f (θ + s) - f θ‖ < ε := by
  have hpi := Real.pi_pos
  have hK : IsCompact (Icc (-Real.pi) (3 * Real.pi)) := isCompact_Icc
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hf.continuousOn) ε hε
  refine ⟨min (δ / 2) (Real.pi / 2), lt_min (by positivity) (by positivity),
    (min_le_right _ _).trans_lt (by linarith), fun θ s hs => ?_⟩
  obtain ⟨n, hn, -⟩ := existsUnique_zsmul_near_of_pos' (by positivity : 0 < 2 * Real.pi) θ
  set θ' := θ - n • (2 * Real.pi) with hθ'
  have h1 : f θ = f θ' := (hper.sub_zsmul_eq n).symm
  have h2 : f (θ + s) = f (θ' + s) := by
    rw [hθ', sub_add_eq_add_sub]; exact (hper.sub_zsmul_eq n).symm
  have hsπ : |s| ≤ Real.pi / 2 := hs.trans (min_le_right _ _)
  have hsδ : |s| < δ := hs.trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have habs := abs_le.1 hsπ
  rw [h1, h2, ← dist_eq_norm]
  refine hu _ ⟨by linarith [hn.1], by linarith [hn.2]⟩ _ ⟨by linarith [hn.1], by linarith [hn.2]⟩
    ?_
  rw [Real.dist_eq, add_sub_cancel_left]
  exact hsδ

/-- **Uniform approximate identity on the circle.** For the kernels of `tendsto_kernel_mean` and a
continuous `2π`-periodic `f`, the means converge to `f` uniformly. -/
private lemma tendstoUniformly_kernel_mean {ι : Type*} {l : Filter ι} {k : ι → ℝ → ℝ}
    (hkp : ∀ i, Function.Periodic (k i) (2 * Real.pi)) (hke : ∀ i s, k i (-s) = k i s)
    (hkb : ∀ᶠ i in l, Measurable (k i) ∧ (∃ C, ∀ s, |k i s| ≤ C) ∧ ∀ s, 0 ≤ k i s)
    (hk1 : ∀ᶠ i in l, 1 / (2 * Real.pi) * ∫ θ in (0 : ℝ)..2 * Real.pi, k i θ = 1)
    (hku : ∀ δ, 0 < δ → δ < Real.pi →
      TendstoUniformlyOn k (fun _ => 0) l (Icc δ (2 * Real.pi - δ)))
    {f : ℝ → ℂ} (hper : Function.Periodic f (2 * Real.pi)) (hf : Continuous f) :
    TendstoUniformly (fun i θ => ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
      ∫ t in (0 : ℝ)..2 * Real.pi, (k i (θ - t) : ℂ) * f t) f l := by
  have hpi := Real.pi_pos
  have hfi : IntervalIntegrable f volume 0 (2 * Real.pi) := hf.intervalIntegrable _ _
  obtain ⟨B, hB⟩ : ∃ B, ∀ x, ‖f x‖ ≤ B := by
    obtain ⟨B, hB⟩ := (hper.isBounded_of_continuous (by positivity) hf).exists_norm_le
    exact ⟨B, fun x => hB _ (mem_range_self x)⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ0, hδπ, hδ⟩ := exists_uniform_periodic hper hf (ε := ε / 4) (by positivity)
  set η := ε / (8 * (B + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hku' := Metric.tendstoUniformlyOn_iff.1 (hku δ hδ0 hδπ) η hη0
  filter_upwards [hkb, hk1, hku'] with i hi hi1 hiu θ
  obtain ⟨C, hC⟩ := hi.2.1
  have hφ1 := integral_Ioc_kernel_div (hkp i) (hke i) hi.1 hC hi1
  rw [integral_kernel_mul_eq (hkp i) (hke i) hi.1 hC hper hfi θ, dist_eq_norm']
  set φ : ℝ → ℝ := fun s => k i s / Real.pi with hφ
  set g : ℝ → ℂ := fun s => (f (θ + s) + f (θ - s)) / 2 with hg
  have hφi : IntegrableOn φ (Ioc 0 Real.pi) := by
    refine Measure.integrableOn_of_bounded (M := C / Real.pi) measure_Ioc_lt_top.ne
      (hi.1.div_const _).aestronglyMeasurable (Eventually.of_forall fun s => ?_)
    rw [hφ, Real.norm_eq_abs, abs_div, abs_of_pos hpi]
    exact div_le_div_of_nonneg_right (hC s) hpi.le
  have hgm : AEStronglyMeasurable g (volume.restrict (Ioc 0 Real.pi)) :=
    (by fun_prop : Continuous g).aestronglyMeasurable
  have hφg : IntegrableOn (fun s => φ s • g s) (Ioc 0 Real.pi) :=
    hφi.smul_of_top_left (memLp_top_of_bound hgm B (Eventually.of_forall fun s => by
      simp only [hg, norm_div, Complex.norm_ofNat]
      calc ‖f (θ + s) + f (θ - s)‖ / 2 ≤ (B + B) / 2 := by
            gcongr; exact (norm_add_le _ _).trans (add_le_add (hB _) (hB _))
        _ = B := by ring))
  have hdiff : (∫ s in Ioc 0 Real.pi, φ s • g s) - f θ =
      ∫ s in Ioc 0 Real.pi, φ s • (g s - f θ) := by
    rw [show (∫ s in Ioc 0 Real.pi, φ s • (g s - f θ)) =
        ∫ s in Ioc 0 Real.pi, (φ s • g s - φ s • f θ) by simp_rw [smul_sub],
      integral_sub hφg (hφi.smul_const _), integral_smul_const, hφ1, one_smul]
  rw [hdiff]
  have hbound : ∀ s ∈ Ioc 0 Real.pi,
      ‖φ s • (g s - f θ)‖ ≤ φ s * (ε / 4) + η / Real.pi * (2 * B) := by
    intro s hs
    have hφ0 : 0 ≤ φ s := div_nonneg (hi.2.2 s) hpi.le
    rw [norm_smul, Real.norm_of_nonneg hφ0]
    have hgs : ‖g s - f θ‖ ≤ 2 * B := by
      simp only [hg]
      calc ‖(f (θ + s) + f (θ - s)) / 2 - f θ‖ ≤ ‖(f (θ + s) + f (θ - s)) / 2‖ + ‖f θ‖ :=
            norm_sub_le _ _
        _ ≤ B + B := by
            gcongr
            · rw [norm_div, Complex.norm_ofNat]
              calc ‖f (θ + s) + f (θ - s)‖ / 2 ≤ (B + B) / 2 := by
                    gcongr; exact (norm_add_le _ _).trans (add_le_add (hB _) (hB _))
                _ = B := by ring
            · exact hB _
        _ = 2 * B := by ring
    rcases le_or_gt s δ with hsδ | hsδ
    · have h1 := hδ θ s (by rw [abs_of_pos hs.1]; exact hsδ)
      have h2 := hδ θ (-s) (by rw [abs_neg, abs_of_pos hs.1]; exact hsδ)
      rw [← sub_eq_add_neg] at h2
      have hgs' : ‖g s - f θ‖ ≤ ε / 4 := by
        simp only [hg]
        rw [show (f (θ + s) + f (θ - s)) / 2 - f θ =
          ((f (θ + s) - f θ) + (f (θ - s) - f θ)) / 2 by ring, norm_div, Complex.norm_ofNat]
        calc ‖(f (θ + s) - f θ) + (f (θ - s) - f θ)‖ / 2 ≤ (ε / 4 + ε / 4) / 2 := by
              gcongr; exact (norm_add_le _ _).trans (add_le_add h1.le h2.le)
          _ = ε / 4 := by ring
      calc φ s * ‖g s - f θ‖ ≤ φ s * (ε / 4) := mul_le_mul_of_nonneg_left hgs' hφ0
        _ ≤ φ s * (ε / 4) + η / Real.pi * (2 * B) := le_add_of_nonneg_right (by positivity)
    · have hks := hiu s ⟨hsδ.le, by linarith [hs.2]⟩
      rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hi.2.2 s)] at hks
      have hφs : φ s ≤ η / Real.pi := div_le_div_of_nonneg_right hks.le hpi.le
      calc φ s * ‖g s - f θ‖ ≤ η / Real.pi * (2 * B) :=
            mul_le_mul hφs hgs (norm_nonneg _) (by positivity)
        _ ≤ φ s * (ε / 4) + η / Real.pi * (2 * B) :=
            le_add_of_nonneg_left (by positivity)
  have hint : IntegrableOn (fun s => φ s * (ε / 4) + η / Real.pi * (2 * B)) (Ioc 0 Real.pi) :=
    (hφi.mul_const _).add (integrableOn_const measure_Ioc_lt_top.ne)
  refine (norm_integral_le_of_norm_le hint ((ae_restrict_mem measurableSet_Ioc).mono
    fun s hs => hbound s hs)).trans_lt ?_
  rw [integral_add (hφi.mul_const _) (integrableOn_const measure_Ioc_lt_top.ne),
    integral_mul_const, hφ1, setIntegral_const, Real.volume_real_Ioc_of_le hpi.le, sub_zero,
    smul_eq_mul]
  have : Real.pi * (η / Real.pi * (2 * B)) = ε * B / (4 * (B + 1)) := by
    rw [hη]; field_simp; ring
  rw [this]
  have : ε * B / (4 * (B + 1)) < ε / 4 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- The Poisson kernel is `2π`-periodic. -/
private lemma abelPoissonKernel_periodic (r : ℝ) :
    Function.Periodic (abelPoissonKernel r) (2 * Real.pi) := fun θ => by
  simp only [abelPoissonKernel, Real.cos_add_two_pi]

/-- The Poisson kernel is even. -/
private lemma abelPoissonKernel_neg (r θ : ℝ) :
    abelPoissonKernel r (-θ) = abelPoissonKernel r θ := by
  simp only [abelPoissonKernel, Real.cos_neg]

/-- For `0 ≤ r < 1`, the Poisson kernel is measurable, bounded and nonnegative. -/
private lemma abelPoissonKernel_bounds {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Measurable (abelPoissonKernel r) ∧ (∃ C, ∀ s, |abelPoissonKernel r s| ≤ C) ∧
      ∀ s, 0 ≤ abelPoissonKernel r s := by
  have hD : ∀ s, (1 - r) ^ 2 ≤ 1 - 2 * r * Real.cos s + r ^ 2 := fun s => by
    nlinarith [Real.cos_le_one s]
  have hD0 : 0 < (1 - r) ^ 2 := by nlinarith
  have hnum : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hnn : ∀ s, 0 ≤ abelPoissonKernel r s := fun s =>
    div_nonneg hnum (hD0.le.trans (hD s))
  refine ⟨by unfold abelPoissonKernel; fun_prop, ⟨(1 - r ^ 2) / (1 - r) ^ 2, fun s => ?_⟩, hnn⟩
  rw [abs_of_nonneg (hnn s), abelPoissonKernel]
  exact div_le_div_of_nonneg_left hnum hD0 (hD s)


/-- `|sin((n+1)x)| ≤ (n+1)|sin x|`. -/
private lemma abs_sin_nat_succ_mul_le (n : ℕ) (x : ℝ) :
    |Real.sin ((n + 1) * x)| ≤ (n + 1) * |Real.sin x| := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    rw [show ((n : ℝ) + 1 + 1) * x = (n + 1) * x + x by ring, Real.sin_add]
    calc |Real.sin ((n + 1) * x) * Real.cos x + Real.cos ((n + 1) * x) * Real.sin x|
        ≤ |Real.sin ((n + 1) * x)| * |Real.cos x| + |Real.cos ((n + 1) * x)| * |Real.sin x| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |Real.sin ((n + 1) * x)| * 1 + 1 * |Real.sin x| := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
      _ ≤ (n + 1 + 1) * |Real.sin x| := by linarith

/-- The Fejér kernel is `2π`-periodic. -/
private lemma fejerKernel_periodic (n : ℕ) :
    Function.Periodic (fejerKernel n) (2 * Real.pi) := fun θ => by
  simp only [fejerKernel]
  rw [show ((n : ℝ) + 1) * (θ + 2 * Real.pi) / 2 = (n + 1) * θ / 2 + ((n + 1 : ℕ) : ℝ) * Real.pi by
      push_cast; ring,
    show (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi by ring, Real.sin_add_nat_mul_pi,
    Real.sin_add_pi, div_pow, div_pow, mul_pow, neg_sq, ← pow_mul, mul_comm (n + 1) 2, pow_mul]
  norm_num

/-- The Fejér kernel is even. -/
private lemma fejerKernel_neg (n : ℕ) (θ : ℝ) : fejerKernel n (-θ) = fejerKernel n θ := by
  simp only [fejerKernel]
  rw [show ((n : ℝ) + 1) * -θ / 2 = -((n + 1) * θ / 2) by ring, show -θ / 2 = -(θ / 2) by ring,
    Real.sin_neg, Real.sin_neg, neg_div_neg_eq]

/-- The Fejér kernel is measurable, bounded by `n + 1` and nonnegative. -/
private lemma fejerKernel_bounds (n : ℕ) :
    Measurable (fejerKernel n) ∧ (∃ C, ∀ s, |fejerKernel n s| ≤ C) ∧
      ∀ s, 0 ≤ fejerKernel n s := by
  have hnn : ∀ s, 0 ≤ fejerKernel n s := fun s => by unfold fejerKernel; positivity
  refine ⟨by unfold fejerKernel; fun_prop, ⟨n + 1, fun s => ?_⟩, hnn⟩
  rw [abs_of_nonneg (hnn s), fejerKernel]
  rcases eq_or_ne (Real.sin (s / 2)) 0 with h | h
  · rw [h, div_zero]; simp; positivity
  have hb := abs_sin_nat_succ_mul_le n (s / 2)
  rw [show ((n : ℝ) + 1) * (s / 2) = (n + 1) * s / 2 by ring] at hb
  have hq : (Real.sin ((n + 1) * s / 2) / Real.sin (s / 2)) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    calc Real.sin ((n + 1) * s / 2) ^ 2 = |Real.sin ((n + 1) * s / 2)| ^ 2 := (sq_abs _).symm
      _ ≤ (((n : ℝ) + 1) * |Real.sin (s / 2)|) ^ 2 := by gcongr
      _ = ((n : ℝ) + 1) ^ 2 * Real.sin (s / 2) ^ 2 := by rw [mul_pow, sq_abs]
  calc 1 / ((n : ℝ) + 1) * (Real.sin ((n + 1) * s / 2) / Real.sin (s / 2)) ^ 2
      ≤ 1 / ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ 2 := mul_le_mul_of_nonneg_left hq (by positivity)
    _ = (n : ℝ) + 1 := by field_simp

/-- DLMF 1.15.24 (Abel means): if `f` is `2π`-periodic and integrable on `[0, 2π]`, then
`A(r, θ) → ½(f(θ+) + f(θ-))` as `r → 1-` at every `θ` where both one-sided limits exist. -/
@[dlmf 1.15.E24]
theorem tendsto_abelMean {f : ℝ → ℂ} (hper : Function.Periodic f (2 * Real.pi))
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) {θ : ℝ} {fp fm : ℂ}
    (hp : Tendsto f (𝓝[>] θ) (𝓝 fp)) (hm : Tendsto f (𝓝[<] θ) (𝓝 fm)) :
    Tendsto (fun r => abelMean f r θ) (𝓝[<] 1) (𝓝 ((fp + fm) / 2)) := by
  have hr : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 ≤ r ∧ r < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with r h1 h0
    exact ⟨h0.le, h1⟩
  refine (tendsto_kernel_mean abelPoissonKernel_periodic abelPoissonKernel_neg
    (hr.mono fun r h => abelPoissonKernel_bounds h.1 h.2)
    (hr.mono fun r h => integral_abelPoissonKernel h.1 h.2)
    (fun δ hδ0 hδ => tendstoUniformlyOn_abelPoissonKernel hδ0 hδ) hper hf hp hm).congr' ?_
  filter_upwards [hr] with r h
  exact (abelMean_eq_integral hf h.1 h.2 θ).symm

/-- DLMF 1.15.24 (Cesàro means, Fejér's theorem): if `f` is `2π`-periodic and integrable on
`[0, 2π]`, then `σ_n(θ) → ½(f(θ+) + f(θ-))` at every `θ` where both one-sided limits exist. -/
@[dlmf 1.15.E24]
theorem tendsto_fourierCesaroMean {f : ℝ → ℂ} (hper : Function.Periodic f (2 * Real.pi))
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) {θ : ℝ} {fp fm : ℂ}
    (hp : Tendsto f (𝓝[>] θ) (𝓝 fp)) (hm : Tendsto f (𝓝[<] θ) (𝓝 fm)) :
    Tendsto (fun n => fourierCesaroMean f n θ) atTop (𝓝 ((fp + fm) / 2)) := by
  refine (tendsto_kernel_mean fejerKernel_periodic fejerKernel_neg
    (Eventually.of_forall fejerKernel_bounds) (Eventually.of_forall integral_fejerKernel)
    (fun δ hδ0 hδ => tendstoUniformlyOn_fejerKernel hδ0 hδ) hper hf hp hm).congr' ?_
  exact Eventually.of_forall fun n => (fourierCesaroMean_eq_integral hf n θ).symm

/-- DLMF §1.15(iii), after 1.15.24: for continuous `2π`-periodic `f` the Abel means converge to
`f` uniformly as `r → 1-`. -/
@[dlmf 1.15.E24]
theorem tendstoUniformly_abelMean {f : ℝ → ℂ} (hper : Function.Periodic f (2 * Real.pi))
    (hf : Continuous f) :
    TendstoUniformly (fun r θ => abelMean f r θ) f (𝓝[<] 1) := by
  have hr : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 ≤ r ∧ r < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with r h1 h0
    exact ⟨h0.le, h1⟩
  refine (tendstoUniformly_congr ?_).1 (tendstoUniformly_kernel_mean abelPoissonKernel_periodic
    abelPoissonKernel_neg (hr.mono fun r h => abelPoissonKernel_bounds h.1 h.2)
    (hr.mono fun r h => integral_abelPoissonKernel h.1 h.2)
    (fun δ hδ0 hδ => tendstoUniformlyOn_abelPoissonKernel hδ0 hδ) hper hf)
  filter_upwards [hr] with r h
  funext θ
  exact (abelMean_eq_integral (hf.intervalIntegrable _ _) h.1 h.2 θ).symm

/-- DLMF §1.15(iii), after 1.15.24 (Fejér): for continuous `2π`-periodic `f` the Cesàro means
converge to `f` uniformly. -/
@[dlmf 1.15.E24]
theorem tendstoUniformly_fourierCesaroMean {f : ℝ → ℂ} (hper : Function.Periodic f (2 * Real.pi))
    (hf : Continuous f) :
    TendstoUniformly (fun n θ => fourierCesaroMean f n θ) f atTop := by
  refine (tendstoUniformly_congr ?_).1 (tendstoUniformly_kernel_mean fejerKernel_periodic
    fejerKernel_neg (Eventually.of_forall fejerKernel_bounds)
    (Eventually.of_forall integral_fejerKernel)
    (fun δ hδ0 hδ => tendstoUniformlyOn_fejerKernel hδ0 hδ) hper hf)
  exact Eventually.of_forall fun n => funext fun θ =>
    (fourierCesaroMean_eq_integral (hf.intervalIntegrable _ _) n θ).symm

/-- For real `f`, `F(-n) = conj F(n)`. -/
private lemma fourierCoeffOn_neg_ofReal (f : ℝ → ℝ) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) (-n) =
      conj (fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) n) := by
  rw [fourierCoeffOn_two_pi_eq, fourierCoeffOn_two_pi_eq, map_mul, map_inv₀, Complex.conj_ofReal,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le, ← integral_conj]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I,
    map_intCast]
  push_cast
  ring_nf

/-- `(r e^{iθ})^m = r^m e^{imθ}`. -/
private lemma ofReal_mul_cexp_pow (r θ : ℝ) (m : ℕ) :
    ((r : ℂ) * cexp (θ * I)) ^ m = ((r ^ m : ℝ) : ℂ) * cexp ((m : ℤ) * θ * I) := by
  rw [mul_pow, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

private lemma summable_fourierAnalytic {f : ℝ → ℂ} {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => fourierCoeffOn Real.two_pi_pos f (n + 1 : ℕ) * z ^ (n + 1) := by
  set C := (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi, ‖f t‖
  refine Summable.of_norm_bounded (g := fun n : ℕ => C * ‖z‖ ^ (n + 1)) ?_ fun n => ?_
  · exact ((summable_geometric_of_lt_one (norm_nonneg _) hz).mul_left (C * ‖z‖)).congr
      fun n => by ring
  · rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (norm_fourierCoeffOn_le f _) (by positivity)

/-- DLMF 1.15.25–1.15.27: for real `f`, the series `F(0) + 2 ∑_{n≥1} F(n) zⁿ` converges in the
unit disc to an analytic function `G` extending 1.15.26. Stronger than DLMF, which assumes `f`
integrable on `[0, 2π]`. -/
@[dlmf 1.15.E25, dlmf 1.15.E26, dlmf 1.15.E27]
theorem differentiableOn_fourierAnalyticExtension' (f : ℝ → ℝ) :
    (∀ z ∈ Metric.ball (0 : ℂ) 1, Summable fun n : ℕ =>
      fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) (n + 1 : ℕ) * z ^ (n + 1)) ∧
    DifferentiableOn ℂ (fourierAnalyticExtension fun t => (f t : ℂ)) (Metric.ball 0 1) := by
  refine ⟨fun z hz => summable_fourierAnalytic (by simpa using hz), ?_⟩
  set C := (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi, ‖(f t : ℂ)‖
  have hC0 : 0 ≤ C := mul_nonneg (by positivity)
    (intervalIntegral.integral_nonneg Real.two_pi_pos.le fun _ _ => norm_nonneg _)
  intro z hz
  rw [mem_ball_zero_iff] at hz
  set ρ := (‖z‖ + 1) / 2
  have hρ1 : ρ < 1 := by simp only [ρ]; linarith
  have hzρ : ‖z‖ < ρ := by simp only [ρ]; linarith
  have hρ0 : 0 ≤ ρ := (norm_nonneg z).trans hzρ.le
  have hd : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ,
      fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) (n + 1 : ℕ) * w ^ (n + 1))
      (Metric.ball 0 ρ) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (u := fun n : ℕ => C * ρ ^ (n + 1)) ?_
      (fun n => (differentiable_const _ |>.mul (differentiable_id.pow _)).differentiableOn)
      Metric.isOpen_ball fun n w hw => ?_
    · exact ((summable_geometric_of_lt_one hρ0 hρ1).mul_left (C * ρ)).congr fun n => by ring
    · rw [mem_ball_zero_iff] at hw
      rw [norm_mul, norm_pow]
      exact mul_le_mul (norm_fourierCoeffOn_le _ _) (pow_le_pow_left₀ (norm_nonneg _) hw.le _)
        (by positivity) hC0
  have hda := (hd.const_mul 2).const_add
    (fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) 0)
  exact (hda.differentiableAt (Metric.isOpen_ball.mem_nhds (by simpa using hzρ)))
    |>.differentiableWithinAt

/-- DLMF 1.15.25–1.15.27: for real `f` integrable on `[0, 2π]` with Fourier series 1.15.25, the
series `F(0) + 2 ∑_{n≥1} F(n) zⁿ` converges in the unit disc to an analytic function `G`
extending 1.15.26. -/
@[dlmf 1.15.E25, dlmf 1.15.E26, dlmf 1.15.E27]
theorem differentiableOn_fourierAnalyticExtension {f : ℝ → ℝ}
    (_hf : IntervalIntegrable f volume 0 (2 * Real.pi)) :
    (∀ z ∈ Metric.ball (0 : ℂ) 1, Summable fun n : ℕ =>
      fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) (n + 1 : ℕ) * z ^ (n + 1)) ∧
    DifferentiableOn ℂ (fourierAnalyticExtension fun t => (f t : ℂ)) (Metric.ball 0 1) :=
  differentiableOn_fourierAnalyticExtension' f

/-- The two halves of the Abel series of a coefficient sequence with `F(-n) = conj F(n)`. -/
private lemma hasSum_abel_halves {F : ℤ → ℂ} (hF : ∀ n, F (-n) = conj (F n)) {r θ : ℝ}
    {S : ℂ} (hS : HasSum (fun n : ℕ => F (n + 1 : ℕ) * ((r : ℂ) * cexp (θ * I)) ^ (n + 1)) S)
    {a : ℤ → ℂ} (ha : ∀ m, a m = ((r ^ m.natAbs : ℝ) : ℂ) * F m * cexp (m * θ * I)) :
    HasSum (fun n : ℕ => a (n + 1)) S ∧ HasSum (fun n : ℕ => a (-(n + 1))) (conj S) := by
  have hpos : ∀ n : ℕ, a (n + 1) = F (n + 1 : ℕ) * ((r : ℂ) * cexp (θ * I)) ^ (n + 1) := by
    intro n
    rw [ha, ofReal_mul_cexp_pow]
    have : ((n : ℤ) + 1).natAbs = n + 1 := by omega
    rw [this]
    push_cast
    ring
  have hneg : ∀ n : ℕ, a (-(n + 1)) =
      conj (F (n + 1 : ℕ) * ((r : ℂ) * cexp (θ * I)) ^ (n + 1)) := by
    intro n
    rw [ha, ofReal_mul_cexp_pow, map_mul, map_mul, ← hF, Complex.conj_ofReal,
      ← Complex.exp_conj]
    have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    rw [this]
    simp only [map_mul, map_intCast, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring_nf
  exact ⟨hS.congr_fun hpos, (Complex.hasSum_conj'.mpr hS).congr_fun hneg⟩

/-- `‖re^{iθ}‖ < 1` for `0 ≤ r < 1`. -/
private lemma norm_ofReal_mul_cexp_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    ‖(r : ℂ) * cexp (θ * I)‖ < 1 := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hr0]
  exact hr1


/-- DLMF §1.15(iii), 1.15.27: for real `f`, the real part `u` of `G(re^{iθ})` is the Abel (Poisson)
sum `A(r, θ)` (which is real). Stronger than DLMF, which assumes `f` integrable on `[0, 2π]`. -/
@[dlmf 1.15.E27]
theorem re_fourierAnalyticExtension' (f : ℝ → ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (θ : ℝ) :
    ((fourierAnalyticExtension (fun t => (f t : ℂ)) (r * cexp (θ * I))).re : ℂ) =
      abelMean (fun t => (f t : ℂ)) r θ := by
  set a : ℤ → ℂ := fun m => ((r ^ m.natAbs : ℝ) : ℂ) *
    fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) m * cexp (m * θ * I) with ha
  obtain ⟨h1, h2⟩ := hasSum_abel_halves (fourierCoeffOn_neg_ofReal f)
    (summable_fourierAnalytic (norm_ofReal_mul_cexp_lt_one hr0 hr1 θ)).hasSum
    (a := a) fun _ => rfl
  have h0 := fourierCoeffOn_neg_ofReal f 0
  rw [neg_zero] at h0
  have h := (h1.of_add_one_of_neg_add_one h2).tsum_eq
  change _ = ∑' n : ℤ, a n
  rw [h, Complex.re_eq_add_conj, fourierAnalyticExtension]
  set S := ∑' n : ℕ, fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) (n + 1 : ℕ) *
    ((r : ℂ) * cexp (θ * I)) ^ (n + 1)
  simp only [ha, map_add, map_mul, ← h0, Int.natAbs_zero, pow_zero, Complex.ofReal_one, one_mul,
    Int.cast_zero, zero_mul, Complex.exp_zero, mul_one, map_ofNat]
  ring

/-- DLMF §1.15(iii), 1.15.27: for real `f`, the real part `u` of `G(re^{iθ})` is the Abel (Poisson)
sum `A(r, θ)` (which is real). -/
@[dlmf 1.15.E27]
theorem re_fourierAnalyticExtension {f : ℝ → ℝ}
    (_hf : IntervalIntegrable f volume 0 (2 * Real.pi)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (θ : ℝ) :
    ((fourierAnalyticExtension (fun t => (f t : ℂ)) (r * cexp (θ * I))).re : ℂ) =
      abelMean (fun t => (f t : ℂ)) r θ :=
  re_fourierAnalyticExtension' f hr0 hr1 θ

/-- DLMF 1.15.28: for real `f`, the imaginary part `v` of `G(re^{iθ})` is
`-∑_{n ∈ ℤ} i (sign n) F(n) r^{|n|} e^{inθ}`. Stronger than DLMF, which assumes `f` integrable on
`[0, 2π]`. -/
@[dlmf 1.15.E28]
theorem im_fourierAnalyticExtension' (f : ℝ → ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (θ : ℝ) :
    ((fourierAnalyticExtension (fun t => (f t : ℂ)) (r * cexp (θ * I))).im : ℂ) =
      -∑' n : ℤ, I * (Int.sign n : ℂ) * fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) n *
        ((r ^ n.natAbs : ℝ) : ℂ) * cexp (n * θ * I) := by
  obtain ⟨h1, h2⟩ := hasSum_abel_halves (fourierCoeffOn_neg_ofReal f)
    (summable_fourierAnalytic (norm_ofReal_mul_cexp_lt_one hr0 hr1 θ)).hasSum
    (a := fun m : ℤ => ((r ^ m.natAbs : ℝ) : ℂ) *
      fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) m * cexp (m * θ * I)) fun _ => rfl
  set b : ℤ → ℂ := fun n => I * (Int.sign n : ℂ) *
    fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) n * ((r ^ n.natAbs : ℝ) : ℂ) *
      cexp (n * θ * I) with hb
  have hb1 : HasSum (fun n : ℕ => b (n + 1)) (I * ∑' n : ℕ,
      fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) (n + 1 : ℕ) *
        ((r : ℂ) * cexp (θ * I)) ^ (n + 1)) := by
    refine (h1.mul_left I).congr_fun fun n => ?_
    simp only [hb]
    have : Int.sign ((n : ℤ) + 1) = 1 := Int.sign_eq_one_of_pos (by omega)
    rw [this]
    push_cast
    ring
  have hb2 : HasSum (fun n : ℕ => b (-(n + 1))) (-I * conj (∑' n : ℕ,
      fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) (n + 1 : ℕ) *
        ((r : ℂ) * cexp (θ * I)) ^ (n + 1))) := by
    refine (h2.mul_left (-I)).congr_fun fun n => ?_
    simp only [hb]
    have : Int.sign (-((n : ℤ) + 1)) = -1 := Int.sign_eq_neg_one_of_neg (by omega)
    rw [this]
    push_cast
    ring
  have h := (hb1.of_add_one_of_neg_add_one hb2).tsum_eq
  rw [h, Complex.im_eq_sub_conj, fourierAnalyticExtension]
  set S := ∑' n : ℕ, fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) (n + 1 : ℕ) *
    ((r : ℂ) * cexp (θ * I)) ^ (n + 1)
  have h0 := fourierCoeffOn_neg_ofReal f 0
  rw [neg_zero] at h0
  simp only [map_add, map_mul, ← h0, map_ofNat, hb, Int.sign_zero, Int.cast_zero, mul_zero,
    zero_mul, add_zero]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- DLMF 1.15.28: for real `f`, the imaginary part `v` of `G(re^{iθ})` is
`-∑_{n ∈ ℤ} i (sign n) F(n) r^{|n|} e^{inθ}`. -/
@[dlmf 1.15.E28]
theorem im_fourierAnalyticExtension {f : ℝ → ℝ}
    (_hf : IntervalIntegrable f volume 0 (2 * Real.pi)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (θ : ℝ) :
    ((fourierAnalyticExtension (fun t => (f t : ℂ)) (r * cexp (θ * I))).im : ℂ) =
      -∑' n : ℤ, I * (Int.sign n : ℂ) * fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) n *
        ((r ^ n.natAbs : ℝ) : ℂ) * cexp (n * θ * I) :=
  im_fourierAnalyticExtension' f hr0 hr1 θ

/-- Every continuous periodic function has a uniformly close trigonometric Cesàro polynomial.
Andrews, Askey and Roy, *Special Functions*, Theorem B.1.6, p. 602,
synopsis AAR-B.1.1–B.1.6. The approximant is the canonical finite Fourier Cesàro mean. -/
theorem exists_uniform_fourierCesaroMean_sub_lt {f : ℝ → ℂ}
    (hper : Function.Periodic f (2 * Real.pi)) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ θ : ℝ, ‖fourierCesaroMean f N θ - f θ‖ < ε := by
  have h := Metric.tendstoUniformly_iff.mp (tendstoUniformly_fourierCesaroMean hper hf) ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨N, fun θ => ?_⟩
  rw [norm_sub_rev]
  simpa only [dist_eq_norm] using hN N le_rfl θ

end DLMF.AlgebraicAnalytic
