/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Appell.Basic.EulerBranches

public import DLMF.GeneralizedHypergeometric.Appell.SeriesAndDifferentialEquations

/-!
# Euler integrals for Appell functions

Branch domains and locally dominated Euler-integral representations of the Appell functions.
The F3-to-F1 reduction and F1/F2 Pfaff transformations use Gauss-series fiber sums
and the proved `pfaff_transformation_of_ne_neg_nat`, retaining all regular lower parameters.

Source references and common attribution are retained in
`DLMF.GeneralizedHypergeometric.Appell`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Polynomial

open scoped Real Topology Nat Interval

namespace DLMF.Hypergeometric

/-! ## Euler integral branches with actual integrability -/

/-- The segment from `1` to `1 - w` stays in the slit plane. -/
lemma ghaR4_slit_segment {w : ℂ} (hw : 1 - w ∈ slitPlane) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    1 - (u:ℂ) * w ∈ slitPlane := by
  have := starConvex_one_slitPlane.add_smul_mem (y := -w) (by simpa [sub_eq_add_neg] using hw)
    hu.1 hu.2
  convert this using 1
  simp [Complex.real_smul]
  ring

/-- A reciprocal principal power of a slit-valued continuous function is bounded on a compact set. -/
lemma ghaR4_inv_cpow_bound {α : Type*} [TopologicalSpace α] {f : α → ℂ} {s : Set α}
    (hs : IsCompact s) (hf : ContinuousOn f s)
    (hslit : ∀ u ∈ s, f u ∈ slitPlane) (b : ℂ) :
    ∃ M : ℝ, ∀ u ∈ s, ‖(f u ^ b)⁻¹‖ ≤ M := by
  have hc : ContinuousOn (fun u => (f u ^ b)⁻¹) s := by
    refine ContinuousOn.inv₀ (hf.cpow_const hslit) fun u hu => ?_
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => slitPlane_ne_zero (hslit u hu) h.1
  exact hs.exists_bound_of_continuousOn hc

/-- The Euler beta kernel is integrable on `[0,1]`. -/
lemma ghaR4_beta_integrableOn {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^(u-1) * (1 - (t:ℂ))^(v-1)) (Icc 0 1) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc,
    ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact Complex.betaIntegral_convergent hu hv

/-- The product of two beta kernels is integrable on the unit square. -/
lemma ghaR4_beta_prod_integrableOn {u v u' v' : ℂ} (hu : 0 < u.re) (hv : 0 < v.re)
    (hu' : 0 < u'.re) (hv' : 0 < v'.re) :
    IntegrableOn (fun p : ℝ × ℝ => ‖(p.1:ℂ)^(u-1) * (1 - (p.1:ℂ))^(v-1)‖ *
      ‖(p.2:ℂ)^(u'-1) * (1 - (p.2:ℂ))^(v'-1)‖) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact (ghaR4_beta_integrableOn hu hv).norm.mul_prod (ghaR4_beta_integrableOn hu' hv').norm

/-- The set where `1 - x` lies in the slit plane is open. -/
lemma ghaR4_isOpen_slitPre : IsOpen {x : ℂ | 1 - x ∈ slitPlane} :=
  isOpen_slitPlane.preimage (by fun_prop)

/-- A closed ball on which `1 - x` stays in the slit plane. -/
lemma ghaR4_exists_closedBall_slit {x₀ : ℂ} (hx : 1 - x₀ ∈ slitPlane) :
    ∃ r > 0, Metric.closedBall x₀ r ⊆ {x : ℂ | 1 - x ∈ slitPlane} := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp ghaR4_isOpen_slitPre x₀ hx
  exact ⟨r / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hsub⟩

/-- Uniform bound for `(1 - u x)^(-b)` over `u ∈ [0,1]` and `x` in a slit-admissible closed ball. -/
lemma ghaR4_inv_cpow_bound_param {x₀ : ℂ} {r : ℝ}
    (hr : Metric.closedBall x₀ r ⊆ {x : ℂ | 1 - x ∈ slitPlane}) (b : ℂ) :
    ∃ M : ℝ, ∀ u ∈ Icc (0:ℝ) 1, ∀ x ∈ Metric.closedBall x₀ r, ‖((1 - (u:ℂ) * x) ^ b)⁻¹‖ ≤ M := by
  obtain ⟨M, hM⟩ := ghaR4_inv_cpow_bound (f := fun q : ℝ × ℂ => 1 - (q.1:ℂ) * q.2)
    (isCompact_Icc.prod (isCompact_closedBall x₀ r)) (by fun_prop)
    (fun q hq => ghaR4_slit_segment (hr hq.2) hq.1) b
  exact ⟨M, fun u hu x hx => hM (u, x) ⟨hu, hx⟩⟩

/-- Differentiability of `x ↦ (1 - u x)^(-b)` on the Euler domain. -/
lemma ghaR4_differentiableAt_inv_cpow {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) {x : ℂ}
    (hx : 1 - x ∈ slitPlane) (b : ℂ) :
    DifferentiableAt ℂ (fun x : ℂ => ((1 - (u:ℂ) * x) ^ b)⁻¹) x := by
  have hs := ghaR4_slit_segment hx hu
  refine (((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)).cpow
    (differentiableAt_const b) hs).inv ?_
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => slitPlane_ne_zero hs h.1

/-- The square-slit condition is open. -/
lemma ghaR4_square_eventually {p₀ : ℂ × ℂ} (h : AppellSquareSlit p₀) :
    ∀ᶠ p in 𝓝 p₀, AppellSquareSlit p := by
  have hK : IsCompact (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have := hK.eventually_forall_of_forall_eventually (x₀ := p₀)
    (P := fun p q => 1 - (q.1:ℂ) * p.1 - (q.2:ℂ) * p.2 ∈ slitPlane) (fun q hq => by
      have hc : Continuous fun z : (ℂ × ℂ) × (ℝ × ℝ) => 1 - (z.2.1:ℂ) * z.1.1 - (z.2.2:ℂ) * z.1.2 := by
        fun_prop
      exact hc.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds (h q.1 hq.1 q.2 hq.2)))
  filter_upwards [this] with p hp u hu v hv
  exact hp (u, v) ⟨hu, hv⟩

/-- The F2/F4 Euler domain is open. -/
lemma ghaR4_isOpen_square : IsOpen {p : ℂ × ℂ | AppellSquareSlit p} :=
  isOpen_iff_mem_nhds.mpr fun _ hp => ghaR4_square_eventually hp

/-- A closed ball inside the F2/F4 Euler domain. -/
lemma ghaR4_exists_closedBall_square {p₀ : ℂ × ℂ} (h : AppellSquareSlit p₀) :
    ∃ r > 0, ∀ p ∈ Metric.closedBall p₀ r, AppellSquareSlit p := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp ghaR4_isOpen_square p₀ h
  exact ⟨r / 2, by positivity, fun p hp => hsub (Metric.closedBall_subset_ball (by linarith) hp)⟩

/-- A uniform bound for a reciprocal power along the square, for parameters near a point. -/
lemma ghaR4_square_inv_cpow_bound {p₀ : ℂ × ℂ} {r : ℝ}
    {f : (ℂ × ℂ) × (ℝ × ℝ) → ℂ} (hf : Continuous f)
    (hs : ∀ p ∈ Metric.closedBall p₀ r, ∀ q ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, f (p, q) ∈ slitPlane)
    (b : ℂ) :
    ∃ M : ℝ, ∀ p ∈ Metric.closedBall p₀ r, ∀ q ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1,
      ‖(f (p, q) ^ b)⁻¹‖ ≤ M := by
  obtain ⟨M, hM⟩ := ghaR4_inv_cpow_bound (f := f)
    ((isCompact_closedBall p₀ r).prod (isCompact_Icc.prod isCompact_Icc)) hf.continuousOn
    (fun z hz => hs z.1 hz.1 z.2 hz.2) b
  exact ⟨M, fun p hp q hq => hM (p, q) ⟨hp, hq⟩⟩

/-- Differentiability of the square-integral denominator power. -/
lemma ghaR4_differentiableAt_inv_cpow_square {p : ℂ × ℂ} {u v : ℝ}
    (hs : 1 - (u:ℂ) * p.1 - (v:ℂ) * p.2 ∈ slitPlane) (b : ℂ) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => ((1 - (u:ℂ) * p.1 - (v:ℂ) * p.2) ^ b)⁻¹) p := by
  have hf : DifferentiableAt ℂ (fun p : ℂ × ℂ => 1 - (u:ℂ) * p.1 - (v:ℂ) * p.2) p := by fun_prop
  refine (hf.cpow (differentiableAt_const b) hs).inv ?_
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => slitPlane_ne_zero hs h.1

/-- Termwise integration of a series with a bounded integrable weight. -/
lemma ghaR4_hasSum_integral {α ι : Type*} [MeasurableSpace α] [Countable ι] {μ : Measure α}
    {w : α → ℂ} (hw : Integrable w μ) {d : ι → ℂ} (hd : Summable fun i => ‖d i‖)
    {e : ι → α → ℂ} (he : ∀ i, AEStronglyMeasurable (e i) μ) (hbd : ∀ i, ∀ᵐ t ∂μ, ‖e i t‖ ≤ 1)
    {g : α → ℂ} (hg : ∀ᵐ t ∂μ, HasSum (fun i => d i * e i t) (g t)) :
    HasSum (fun i => d i * ∫ t, w t * e i t ∂μ) (∫ t, w t * g t ∂μ) := by
  have h := hasSum_integral_of_dominated_convergence (μ := μ)
    (F := fun i t => w t * (d i * e i t)) (f := fun t => w t * g t)
    (fun i t => ‖d i‖ * ‖w t‖)
    (fun i => hw.aestronglyMeasurable.mul (aestronglyMeasurable_const.mul (he i)))
    (fun i => by
      filter_upwards [hbd i] with t ht
      rw [norm_mul, norm_mul]
      calc ‖w t‖ * (‖d i‖ * ‖e i t‖) ≤ ‖w t‖ * (‖d i‖ * 1) := by gcongr
        _ = _ := by ring)
    (Eventually.of_forall fun t => hd.mul_right _)
    (by simp_rw [tsum_mul_right]; exact hw.norm.const_mul _)
    (by filter_upwards [hg] with t ht using ht.mul_left (w t))
  refine h.congr_fun fun i => ?_
  rw [← integral_const_mul]
  congr 1; funext t; ring

/-- Absolute convergence of the binomial series `∑ (b)ₘ xᵐ/m!` in the unit disk. -/
lemma ghaR4_summable_norm_binom (b : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun m : ℕ => ‖poch b m / m ! * x ^ m‖ := by
  set σ := 2 / (1 + ‖x‖) with hσ
  have hx0 := norm_nonneg x
  have hσ1 : 1 < σ := by rw [hσ, lt_div_iff₀ (by linarith)]; linarith
  have hσx : σ * ‖x‖ < 1 := by
    rw [hσ, div_mul_eq_mul_div, div_lt_one (by linarith)]; linarith
  obtain ⟨C, hC0, hC⟩ := ghaR4_norm_poch_le_factorial b hσ1
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    ((summable_geometric_of_lt_one (by positivity) hσx).mul_left C)
  have hf : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
  rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow, div_mul_eq_mul_div,
    div_le_iff₀ hf, mul_pow]
  calc ‖poch b m‖ * ‖x‖ ^ m ≤ (C * σ ^ m * m !) * ‖x‖ ^ m := by gcongr; exact hC m
    _ = _ := by ring

/-- Binomially weighted bound for the two-variable binomial coefficients. -/
lemma ghaR4_binom2_coeff_bound (a : ℂ) {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, ∀ q : ℕ × ℕ, ‖poch a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ)‖ ≤
      C * σ ^ (q.1 + q.2) * ((q.1 + q.2).choose q.1 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := ghaR4_norm_poch_le_factorial a hσ
  refine ⟨C, fun ⟨m, n⟩ => ?_⟩
  have hm : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
  have hn : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have hfac : ((m + n) ! : ℝ) = ((m + n).choose m : ℝ) * m ! * n ! := by
    have := Nat.add_choose_mul_factorial_mul_factorial m n
    rw [← Nat.choose_symm_add] at this
    exact_mod_cast this.symm
  simp only
  rw [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast, div_le_iff₀ (by positivity)]
  calc ‖poch a (m + n)‖ ≤ C * σ ^ (m + n) * (m + n) ! := hC _
    _ = _ := by rw [hfac]; ring

/-- The two-variable binomial series `(1-s-t)^(-a) = ∑ (a)ₘ₊ₙ sᵐ tⁿ/(m! n!)`. -/
lemma ghaR4_hasSum_binom2 (a : ℂ) {s t : ℂ} (hst : ‖s‖ + ‖t‖ < 1) :
    HasSum (fun q : ℕ × ℕ => poch a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ) * s ^ q.1 * t ^ q.2)
      ((1 - s - t) ^ (-a)) ∧
    Summable (fun q : ℕ × ℕ => ‖poch a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ) * s ^ q.1 * t ^ q.2‖) := by
  set f := fun q : ℕ × ℕ => poch a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ) * s ^ q.1 * t ^ q.2 with hf
  have hnorm : Summable fun q => ‖f q‖ := by
    obtain ⟨A, B, hA, hB, hS⟩ := ghaR4_dom_diamond
      (fun q : ℕ × ℕ => poch a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ))
      (fun _ hσ => ghaR4_binom2_coeff_bound a hσ) hst
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_) hS
    simp only [hf, norm_mul, norm_pow]
    have := norm_nonneg (poch a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ))
    have hA0 : 0 ≤ A := (norm_nonneg _).trans hA.le
    gcongr
  refine ⟨?_, hnorm⟩
  have hT := (Summable.of_norm hnorm).hasSum
  have hT' : HasSum (f ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) (∑' q, f q) :=
    (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff).mpr hT
  have hfib : ∀ N : ℕ, HasSum (fun c : Finset.antidiagonal N =>
      (f ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) ⟨N, c⟩) (poch a N / N ! * (s + t) ^ N) := by
    intro N
    convert hasSum_fintype (fun c : Finset.antidiagonal N =>
      (f ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) ⟨N, c⟩) using 1
    rw [(Commute.all s t).add_pow', Finset.mul_sum, ← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun c _ => ?_
    obtain ⟨⟨m, n⟩, hc⟩ := c
    have hmn : m + n = N := Finset.mem_antidiagonal.mp hc
    subst hmn
    simp only [Function.comp, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply, hf, nsmul_eq_mul]
    have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hfac : (((m + n) ! : ℕ) : ℂ) = ((m + n).choose m : ℂ) * m ! * n ! := by
      have := Nat.add_choose_mul_factorial_mul_factorial m n
      rw [← Nat.choose_symm_add] at this
      exact_mod_cast this.symm
    have hC : ((m + n).choose m : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    rw [hfac]
    field_simp
  have hG := hT'.sigma hfib
  have hst' : ‖s + t‖ < 1 := (norm_add_le s t).trans_lt hst
  have h1 := hasSum_poch_div_factorial (β := a) hst'
  rw [show 1 - s - t = 1 - (s + t) by ring, h1.unique hG]
  exact hT

/-- Beta-integral moments on `[0,1]`. -/
lemma ghaR4_beta_moment {b γ : ℂ} (m : ℕ) :
    (∫ u in Icc (0:ℝ) 1, (u:ℂ) ^ (b - 1) * ((1 - u : ℝ) : ℂ) ^ (γ - 1) * (u:ℂ) ^ m) =
      betaIntegral (b + m) γ := by
  rw [integral_Icc_eq_integral_Ioc, betaIntegral, intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  have hu0 : (u:ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.1.ne'
  rw [show b + (m : ℂ) - 1 = (b - 1) + (m : ℂ) by ring, cpow_add _ _ hu0, cpow_natCast]
  push_cast
  ring

/-- The normalized beta moment `Γ(c)B(b+m,c-b)/(Γ(b)Γ(c-b)) = (b)ₘ/(c)ₘ`. -/
lemma ghaR4_gamma_beta {b c : ℂ} (hb : 0 < b.re) (hcb : 0 < (c - b).re) (m : ℕ) :
    Gamma c / (Gamma b * Gamma (c - b)) * betaIntegral (b + m) (c - b) = poch b m / poch c m := by
  have hE := euler_term_eq_gaussHGCoeff (a := 1) (b := b) (c := c) m hb hcb
  have hf : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hc : ∀ k : ℕ, c ≠ -k := not_neg_nat_of_re_pos (re_c_pos_of hb hcb)
  rw [poch_nat_one, div_self hf, one_mul] at hE
  rw [hE, gaussHGCoeff, poch_nat_one]
  have hpc := poch_ne_zero_of_not_neg_nat hc m
  field_simp

/-- 16.15.E1: appF1 euler integrable. -/
@[dlmf 16.15.E1]
theorem appF1_euler_integrable (a b b' c : ℂ) (ha : 0<a.re) (hca : 0<(c-a).re) {x y : ℂ} (hxy : (x,y)∈appellEulerDomain) :
    IntegrableOn (appF1EulerKernel a b b' c x y) (Icc (0:ℝ) 1) := by
  obtain ⟨M1, hM1⟩ := ghaR4_inv_cpow_bound (f := fun u : ℝ => 1 - (u:ℂ) * x) isCompact_Icc
    (by fun_prop) (fun u hu => ghaR4_slit_segment hxy.1 hu) b
  obtain ⟨M2, hM2⟩ := ghaR4_inv_cpow_bound (f := fun u : ℝ => 1 - (u:ℂ) * y) isCompact_Icc
    (by fun_prop) (fun u hu => ghaR4_slit_segment hxy.2 hu) b'
  have hβ : IntegrableOn (fun u : ℝ => (u:ℂ)^(a-1) * (1 - (u:ℂ))^(c-a-1)) (Icc 0 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc,
      ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    simpa using Complex.betaIntegral_convergent ha hca
  refine (hβ.norm.mul_const (M1 * M2)).mono' ?_ ?_
  · exact (by unfold appF1EulerKernel; fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have h1 := hM1 u hu
    have h2 := hM2 u hu
    have hM1' := (norm_nonneg _).trans h1
    simp only [appF1EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub, Complex.ofReal_one]
    calc ‖(u:ℂ) ^ (a - 1)‖ * ‖(1 - (u:ℂ)) ^ (c - a - 1)‖ * ‖((1 - (u:ℂ) * x) ^ b)⁻¹‖ *
          ‖((1 - (u:ℂ) * y) ^ b')⁻¹‖
        ≤ ‖(u:ℂ) ^ (a - 1)‖ * ‖(1 - (u:ℂ)) ^ (c - a - 1)‖ * M1 * M2 := by gcongr
      _ = _ := by ring

/-- 16.15.E1: appF1 euler analytic. -/
@[dlmf 16.15.E1]
theorem appF1_euler_analytic (a b b' c : ℂ) (ha : 0<a.re) (hca : 0<(c-a).re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF1Euler a b b' c p.1 p.2) appellEulerDomain := by
  have hU : IsOpen appellEulerDomain :=
    (ghaR4_isOpen_slitPre.preimage continuous_fst).inter
      (ghaR4_isOpen_slitPre.preimage continuous_snd)
  have hβ : IntegrableOn (fun u : ℝ => (u:ℂ)^(a-1) * (1 - (u:ℂ))^(c-a-1)) (Icc 0 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc,
      ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    simpa using Complex.betaIntegral_convergent ha hca
  have hΙ : Ι (0:ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  have hd : DifferentiableOn ℂ
      (fun p : ℂ × ℂ => ∫ u in (0:ℝ)..1, appF1EulerKernel a b b' c p.1 p.2 u) appellEulerDomain := by
    refine differentiableOn_intervalIntegral_of_locally_dominated hU 0 1
      (fun p _ => (by unfold appF1EulerKernel; fun_prop : Measurable _).aestronglyMeasurable)
      ?_ ?_
    · rw [hΙ]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hu' : u ∈ Icc (0:ℝ) 1 := Ioc_subset_Icc_self hu
      intro p hp
      have h1 := ghaR4_differentiableAt_inv_cpow hu' hp.1 b
      have h2 := ghaR4_differentiableAt_inv_cpow hu' hp.2 b'
      have e : (fun q : ℂ × ℂ => appF1EulerKernel a b b' c q.1 q.2 u) = fun q =>
          (u:ℂ) ^ (a - 1) * ((1 - u:ℝ):ℂ) ^ (c - a - 1) * ((1 - (u:ℂ) * q.1) ^ b)⁻¹ *
            ((1 - (u:ℂ) * q.2) ^ b')⁻¹ := by
        funext q; simp only [appF1EulerKernel, div_eq_mul_inv]
      rw [e]
      exact (((differentiableAt_const _).mul (h1.comp p differentiableAt_fst)).mul
        (h2.comp p differentiableAt_snd)).differentiableWithinAt
    · intro p hp
      obtain ⟨r1, hr1, hs1⟩ := ghaR4_exists_closedBall_slit hp.1
      obtain ⟨r2, hr2, hs2⟩ := ghaR4_exists_closedBall_slit hp.2
      obtain ⟨M1, hM1⟩ := ghaR4_inv_cpow_bound_param hs1 b
      obtain ⟨M2, hM2⟩ := ghaR4_inv_cpow_bound_param hs2 b'
      refine ⟨Metric.ball p.1 r1 ×ˢ Metric.ball p.2 r2,
        prod_mem_nhds (Metric.ball_mem_nhds _ hr1) (Metric.ball_mem_nhds _ hr2),
        fun u => ‖(u:ℂ)^(a-1) * (1 - (u:ℂ))^(c-a-1)‖ * (M1 * M2), ?_, ?_⟩
      · rw [hΙ]
        exact (hβ.mono_set Ioc_subset_Icc_self).norm.mul_const _
      · rw [hΙ]
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        have hu' : u ∈ Icc (0:ℝ) 1 := Ioc_subset_Icc_self hu
        intro q hq
        have h1 := hM1 u hu' q.1 (Metric.ball_subset_closedBall hq.1)
        have h2 := hM2 u hu' q.2 (Metric.ball_subset_closedBall hq.2)
        have hM1' := (norm_nonneg _).trans h1
        simp only [appF1EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub,
          Complex.ofReal_one]
        calc ‖(u:ℂ) ^ (a - 1)‖ * ‖(1 - (u:ℂ)) ^ (c - a - 1)‖ * ‖((1 - (u:ℂ) * q.1) ^ b)⁻¹‖ *
              ‖((1 - (u:ℂ) * q.2) ^ b')⁻¹‖
            ≤ ‖(u:ℂ) ^ (a - 1)‖ * ‖(1 - (u:ℂ)) ^ (c - a - 1)‖ * M1 * M2 := by gcongr
          _ = _ := by ring
  have : DifferentiableOn ℂ (fun p : ℂ × ℂ => appF1Euler a b b' c p.1 p.2) appellEulerDomain :=
    (differentiableOn_const _).mul hd
  exact this.analyticOnNhd_of_finiteDimensional hU

/-- For `u ∈ (0, 1]` and `‖x‖, ‖y‖ < 1`, the product of the binomial series of
`(1 - u x)^{-b}` and `(1 - u y)^{-b'}`, as a double series in `u^{m+n}`. -/
private lemma appF1_hasSum_binom_prod (b b' : ℂ) {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) :
    HasSum (fun q : ℕ × ℕ => poch b q.1 / q.1 ! * x ^ q.1 * (poch b' q.2 / q.2 ! * y ^ q.2) *
      (u:ℂ) ^ (q.1 + q.2)) (((1 - (u:ℂ) * x) ^ b)⁻¹ * ((1 - (u:ℂ) * y) ^ b')⁻¹) := by
  have hu' : u ∈ Icc (0:ℝ) 1 := Ioc_subset_Icc_self hu
  have h1 := hasSum_one_sub_mul_cpow (a := b) hu' hx
  have h2 := hasSum_one_sub_mul_cpow (a := b') hu' hy
  have hs : Summable fun q : ℕ × ℕ => (poch b q.1 / q.1 ! * (x * u) ^ q.1) *
      (poch b' q.2 / q.2 ! * (y * u) ^ q.2) := by
    refine Summable.of_norm ?_
    have hux : ‖x * u‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
      nlinarith [norm_nonneg x, hu.2]
    have huy : ‖y * u‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
      nlinarith [norm_nonneg y, hu.2]
    have := (ghaR4_summable_norm_binom b hux).mul_of_nonneg (ghaR4_summable_norm_binom b' huy)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    exact this.congr fun q => by simp only [norm_mul]
  have := h1.mul h2 hs
  rw [cpow_neg, cpow_neg, mul_comm x, mul_comm y] at this
  refine this.congr_fun fun q => ?_
  rw [pow_add, mul_pow, mul_pow]
  ring

/-- 16.15.E1: appF1 euler germ. -/
@[dlmf 16.15.E1]
theorem appF1_euler_germ (a b b' c : ℂ) (ha : 0<a.re) (hca : 0<(c-a).re) :
    (fun p : ℂ × ℂ => appF1 a b b' c p.1 p.2)=ᶠ[𝓝 (0,0)] (fun p => appF1Euler a b b' c p.1 p.2) := by
  have hcre := re_c_pos_of ha hca
  have hc : AppellRegular c := not_neg_nat_of_re_pos hcre
  have hU : {p : ℂ × ℂ | ‖p.1‖ < 1 ∧ ‖p.2‖ < 1} ∈ 𝓝 ((0:ℂ), (0:ℂ)) :=
    ((isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)).mem_nhds (by simp)
  filter_upwards [hU] with p hp
  obtain ⟨x, y⟩ := p
  obtain ⟨hx, hy⟩ := hp
  simp only at hx hy ⊢
  set w : ℝ → ℂ := fun u => (u:ℂ) ^ (a - 1) * ((1 - u : ℝ) : ℂ) ^ (c - a - 1) with hwdef
  set d : ℕ × ℕ → ℂ := fun q => poch b q.1 / q.1 ! * x ^ q.1 * (poch b' q.2 / q.2 ! * y ^ q.2)
    with hddef
  have hw : Integrable w (volume.restrict (Ioc (0:ℝ) 1)) := by
    have := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (Complex.betaIntegral_convergent ha hca)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp [hwdef]
  have hd : Summable fun q => ‖d q‖ := by
    have := (ghaR4_summable_norm_binom b hx).mul_of_nonneg (ghaR4_summable_norm_binom b' hy)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    refine this.congr fun q => ?_
    simp only [hddef, norm_mul]
  have key := ghaR4_hasSum_integral (μ := volume.restrict (Ioc (0:ℝ) 1)) hw hd
    (e := fun q u => (u:ℂ) ^ (q.1 + q.2)) (fun q => by fun_prop)
    (fun q => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
      exact pow_le_one₀ hu.1.le hu.2)
    (g := fun u => ((1 - (u:ℂ) * x) ^ b)⁻¹ * ((1 - (u:ℂ) * y) ^ b')⁻¹)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact appF1_hasSum_binom_prod b b' hx hy hu)
  have hsum := hasSum_appF1 a b b' c hc (x := x) (y := y) ⟨hx, hy⟩
  refine hsum.unique ?_
  unfold appF1Euler
  rw [intervalIntegral.integral_of_le zero_le_one]
  have e1 : (∫ u in Ioc (0:ℝ) 1, appF1EulerKernel a b b' c x y u) =
      ∫ u in Ioc (0:ℝ) 1, w u * (((1 - (u:ℂ) * x) ^ b)⁻¹ * ((1 - (u:ℂ) * y) ^ b')⁻¹) := by
    congr 1; funext u; simp only [appF1EulerKernel, hwdef, div_eq_mul_inv]; ring
  rw [e1]
  refine (key.mul_left (Gamma c / (Gamma a * Gamma (c - a)))).congr_fun fun q => ?_
  obtain ⟨m, n⟩ := q
  simp only
  have hbeta : (∫ u in Ioc (0:ℝ) 1, w u * (u:ℂ) ^ (m + n)) = betaIntegral (a + (m + n : ℕ)) (c - a) := by
    rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    have hu0 : (u:ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.1.ne'
    simp only [hwdef]
    rw [show a + ((m + n : ℕ) : ℂ) - 1 = (a - 1) + ((m + n : ℕ) : ℂ) by ring, cpow_add _ _ hu0,
      cpow_natCast, show c - a - 1 = c - a - 1 by ring]
    push_cast
    ring
  rw [hbeta]
  have hB := ghaR4_gamma_beta ha hca (m + n)
  calc appF1Coeff a b b' c m n * x ^ m * y ^ n
      = (Gamma c / (Gamma a * Gamma (c - a)) * betaIntegral (a + (m + n : ℕ)) (c - a)) *
          (poch b m / m ! * x ^ m * (poch b' n / n ! * y ^ n)) := by
        rw [hB, appF1Coeff]
        have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
        have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
        have hpc := poch_ne_zero_of_not_neg_nat hc (m + n)
        field_simp
    _ = _ := by simp only [hddef]; ring

/-- 16.15.E2: appF2 euler integrable. -/
@[dlmf 16.15.E2]
theorem appF2_euler_integrable (a b b' c c' : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hcb : b.re<c.re) (hcb' : b'.re<c'.re) {x y : ℂ} (hxy : (x,y)∈{p | AppellSquareSlit p}) :
    IntegrableOn (appF2EulerKernel a b b' c c' x y) (Icc (0:ℝ) 1×ˢIcc (0:ℝ) 1) := by
  obtain ⟨M, hM⟩ := ghaR4_inv_cpow_bound (f := fun p : ℝ × ℝ => 1 - (p.1:ℂ) * x - (p.2:ℂ) * y)
    (isCompact_Icc.prod isCompact_Icc) (by fun_prop) (fun p hp => hxy p.1 hp.1 p.2 hp.2) a
  have hcb1 : 0 < (c - b).re := by simp; linarith
  have hcb2 : 0 < (c' - b').re := by simp; linarith
  refine ((ghaR4_beta_prod_integrableOn hb hcb1 hb' hcb2).mul_const M).mono' ?_ ?_
  · exact (by unfold appF2EulerKernel; fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    have h1 := hM p hp
    have hM0 := (norm_nonneg _).trans h1
    simp only [appF2EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub, Complex.ofReal_one]
    calc ‖(p.1:ℂ) ^ (b - 1)‖ * ‖(p.2:ℂ) ^ (b' - 1)‖ * ‖(1 - (p.1:ℂ)) ^ (c - b - 1)‖ *
          ‖(1 - (p.2:ℂ)) ^ (c' - b' - 1)‖ * ‖((1 - (p.1:ℂ) * x - (p.2:ℂ) * y) ^ a)⁻¹‖
        ≤ ‖(p.1:ℂ) ^ (b - 1)‖ * ‖(p.2:ℂ) ^ (b' - 1)‖ * ‖(1 - (p.1:ℂ)) ^ (c - b - 1)‖ *
          ‖(1 - (p.2:ℂ)) ^ (c' - b' - 1)‖ * M := by gcongr
      _ = _ := by ring

/-- 16.15.E2: appF2 euler analytic. -/
@[dlmf 16.15.E2]
theorem appF2_euler_analytic (a b b' c c' : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hcb : b.re<c.re) (hcb' : b'.re<c'.re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF2Euler a b b' c c' p.1 p.2) {p | AppellSquareSlit p} := by
  have hU := ghaR4_isOpen_square
  have hcb1 : 0 < (c - b).re := by simp; linarith
  have hcb2 : 0 < (c' - b').re := by simp; linarith
  have hsq : MeasurableSet (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  have hd : DifferentiableOn ℂ (fun p : ℂ × ℂ =>
      ∫ q in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, appF2EulerKernel a b b' c c' p.1 p.2 q)
      {p | AppellSquareSlit p} := by
    refine differentiableOn_integral_of_locally_dominated hU
      (fun p _ => (by unfold appF2EulerKernel; fun_prop : Measurable _).aestronglyMeasurable)
      ?_ ?_
    · filter_upwards [ae_restrict_mem hsq] with q hq
      intro p hp
      have h1 := ghaR4_differentiableAt_inv_cpow_square (p := p) (hp q.1 hq.1 q.2 hq.2) a
      have e : (fun p : ℂ × ℂ => appF2EulerKernel a b b' c c' p.1 p.2 q) = fun p =>
          (q.1:ℂ) ^ (b - 1) * (q.2:ℂ) ^ (b' - 1) * ((1 - q.1:ℝ):ℂ) ^ (c - b - 1) *
            ((1 - q.2:ℝ):ℂ) ^ (c' - b' - 1) * ((1 - (q.1:ℂ) * p.1 - (q.2:ℂ) * p.2) ^ a)⁻¹ := by
        funext p; simp only [appF2EulerKernel, div_eq_mul_inv]
      rw [e]
      exact ((differentiableAt_const _).mul h1).differentiableWithinAt
    · intro p hp
      obtain ⟨r, hr, hs⟩ := ghaR4_exists_closedBall_square hp
      obtain ⟨M, hM⟩ := ghaR4_square_inv_cpow_bound
        (f := fun z : (ℂ × ℂ) × (ℝ × ℝ) => 1 - (z.2.1:ℂ) * z.1.1 - (z.2.2:ℂ) * z.1.2)
        (by fun_prop) (fun p hp q hq => hs p hp q.1 hq.1 q.2 hq.2) a
      refine ⟨Metric.ball p r, Metric.ball_mem_nhds _ hr,
        fun q => ‖(q.1:ℂ)^(b-1) * (1 - (q.1:ℂ))^(c-b-1)‖ *
          ‖(q.2:ℂ)^(b'-1) * (1 - (q.2:ℂ))^(c'-b'-1)‖ * M, ?_, ?_⟩
      · exact (ghaR4_beta_prod_integrableOn hb hcb1 hb' hcb2).mul_const M
      · filter_upwards [ae_restrict_mem hsq] with q hq
        intro z hz
        have h1 := hM z (Metric.ball_subset_closedBall hz) q hq
        have hM0 := (norm_nonneg _).trans h1
        simp only [appF2EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub,
          Complex.ofReal_one]
        calc ‖(q.1:ℂ) ^ (b - 1)‖ * ‖(q.2:ℂ) ^ (b' - 1)‖ * ‖(1 - (q.1:ℂ)) ^ (c - b - 1)‖ *
              ‖(1 - (q.2:ℂ)) ^ (c' - b' - 1)‖ * ‖((1 - (q.1:ℂ) * z.1 - (q.2:ℂ) * z.2) ^ a)⁻¹‖
            ≤ ‖(q.1:ℂ) ^ (b - 1)‖ * ‖(q.2:ℂ) ^ (b' - 1)‖ * ‖(1 - (q.1:ℂ)) ^ (c - b - 1)‖ *
              ‖(1 - (q.2:ℂ)) ^ (c' - b' - 1)‖ * M := by gcongr
          _ = _ := by ring
  have : DifferentiableOn ℂ (fun p : ℂ × ℂ => appF2Euler a b b' c c' p.1 p.2)
      {p | AppellSquareSlit p} := (differentiableOn_const _).mul hd
  exact this.analyticOnNhd_of_finiteDimensional hU

/-- For `z ∈ [0, 1]²` and `‖x‖ + ‖y‖ < 1`, the double binomial series of
`(1 - z₁ x - z₂ y)^{-a}` in the monomials `z₁^m z₂^n`. -/
private lemma appF2_hasSum_binom2_mul (a : ℂ) {x y : ℂ} (hp : ‖x‖ + ‖y‖ < 1) {z : ℝ × ℝ}
    (hz : z ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) :
    HasSum (fun q : ℕ × ℕ => poch a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ) * x ^ q.1 * y ^ q.2 *
      ((z.1:ℂ) ^ q.1 * (z.2:ℂ) ^ q.2)) (((1 - (z.1:ℂ) * x - (z.2:ℂ) * y) ^ a)⁻¹) := by
  have hz1 : ‖x * z.1‖ ≤ ‖x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz.1.1]
    nlinarith [norm_nonneg x, hz.1.2]
  have hz2 : ‖y * z.2‖ ≤ ‖y‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz.2.1]
    nlinarith [norm_nonneg y, hz.2.2]
  have h := (ghaR4_hasSum_binom2 a (s := x * z.1) (t := y * z.2) (by linarith)).1
  rw [cpow_neg, mul_comm x, mul_comm y] at h
  refine h.congr_fun fun q => ?_
  rw [mul_pow, mul_pow]
  ring

/-- 16.15.E2: appF2 euler germ. -/
@[dlmf 16.15.E2]
theorem appF2_euler_germ (a b b' c c' : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hcb : b.re<c.re) (hcb' : b'.re<c'.re) :
    (fun p : ℂ × ℂ => appF2 a b b' c c' p.1 p.2)=ᶠ[𝓝 (0,0)] (fun p => appF2Euler a b b' c c' p.1 p.2) := by
  have hcb1 : 0 < (c - b).re := by simp; linarith
  have hcb2 : 0 < (c' - b').re := by simp; linarith
  have hc : AppellRegular c := not_neg_nat_of_re_pos (re_c_pos_of hb hcb1)
  have hc' : AppellRegular c' := not_neg_nat_of_re_pos (re_c_pos_of hb' hcb2)
  have hU : {p : ℂ × ℂ | ‖p.1‖ + ‖p.2‖ < 1} ∈ 𝓝 ((0:ℂ), (0:ℂ)) :=
    (isOpen_lt ((continuous_norm.comp continuous_fst).add (continuous_norm.comp continuous_snd))
      continuous_const).mem_nhds (by simp)
  filter_upwards [hU] with p hp
  obtain ⟨x, y⟩ := p
  simp only at hp ⊢
  set f1 : ℕ → ℝ → ℂ := fun m u => (u:ℂ) ^ (b - 1) * ((1 - u : ℝ) : ℂ) ^ (c - b - 1) * (u:ℂ) ^ m
    with hf1
  set f2 : ℕ → ℝ → ℂ := fun n u => (u:ℂ) ^ (b' - 1) * ((1 - u : ℝ) : ℂ) ^ (c' - b' - 1) * (u:ℂ) ^ n
    with hf2
  set w : ℝ × ℝ → ℂ := fun q => f1 0 q.1 * f2 0 q.2 with hwdef
  set d : ℕ × ℕ → ℂ := fun q => poch a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ) * x ^ q.1 * y ^ q.2
    with hddef
  have hsq : MeasurableSet (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  have hint0 : ∀ {β γ : ℂ}, 0 < β.re → 0 < γ.re →
      IntegrableOn (fun u : ℝ => (u:ℂ) ^ (β - 1) * ((1 - u : ℝ) : ℂ) ^ (γ - 1)) (Icc 0 1) := by
    intro β γ hβ hγ
    refine (ghaR4_beta_integrableOn hβ hγ).congr_fun (fun u _ => ?_) measurableSet_Icc
    push_cast; ring
  have hw : Integrable w (volume.restrict (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    refine ((hint0 hb hcb1).mul_prod (hint0 hb' hcb2)).congr (Eventually.of_forall fun q => ?_)
    simp [hwdef, hf1, hf2]
  have hd : Summable fun q => ‖d q‖ := (ghaR4_hasSum_binom2 a hp).2
  have key := ghaR4_hasSum_integral (μ := volume.restrict (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) hw hd
    (e := fun q z => (z.1:ℂ) ^ q.1 * (z.2:ℂ) ^ q.2) (fun q => by fun_prop)
    (fun q => by
      filter_upwards [ae_restrict_mem hsq] with z hz
      rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hz.1.1, abs_of_nonneg hz.2.1]
      calc z.1 ^ q.1 * z.2 ^ q.2 ≤ 1 * 1 :=
            mul_le_mul (pow_le_one₀ hz.1.1 hz.1.2) (pow_le_one₀ hz.2.1 hz.2.2)
              (pow_nonneg hz.2.1 _) zero_le_one
        _ = 1 := one_mul 1)
    (g := fun z => ((1 - (z.1:ℂ) * x - (z.2:ℂ) * y) ^ a)⁻¹)
    (by
      filter_upwards [ae_restrict_mem hsq] with z hz
      exact appF2_hasSum_binom2_mul a hp hz)
  have hsum := hasSum_appF2 a b b' c c' hc hc' (x := x) (y := y) hp
  refine hsum.unique ?_
  unfold appF2Euler
  have e1 : (∫ z in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, appF2EulerKernel a b b' c c' x y z) =
      ∫ z in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, w z * ((1 - (z.1:ℂ) * x - (z.2:ℂ) * y) ^ a)⁻¹ := by
    congr 1; funext z; simp only [appF2EulerKernel, hwdef, hf1, hf2, div_eq_mul_inv]; ring
  rw [e1]
  refine (key.mul_left (Gamma c * Gamma c' / (Gamma b * Gamma b' * Gamma (c - b) *
    Gamma (c' - b')))).congr_fun fun q => ?_
  obtain ⟨m, n⟩ := q
  simp only
  have hI : (∫ z in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, w z * ((z.1:ℂ) ^ m * (z.2:ℂ) ^ n)) =
      betaIntegral (b + m) (c - b) * betaIntegral (b' + n) (c' - b') := by
    have e2 : (fun z : ℝ × ℝ => w z * ((z.1:ℂ) ^ m * (z.2:ℂ) ^ n)) =
        fun z => f1 m z.1 * f2 n z.2 := by
      funext z; simp only [hwdef, hf1, hf2, pow_zero, mul_one]; ring
    rw [e2, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_mul]
    rw [show c - b - 1 = (c - b) - 1 by ring] at hf1
    simp only [hf1, hf2]
    rw [ghaR4_beta_moment m, ghaR4_beta_moment n]
  rw [hI]
  have hB1 := ghaR4_gamma_beta hb hcb1 m
  have hB2 := ghaR4_gamma_beta hb' hcb2 n
  have hG : Gamma c * Gamma c' / (Gamma b * Gamma b' * Gamma (c - b) * Gamma (c' - b')) *
      (betaIntegral (b + m) (c - b) * betaIntegral (b' + n) (c' - b')) =
      poch b m / poch c m * (poch b' n / poch c' n) := by
    rw [← hB1, ← hB2]; ring
  have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hpc := poch_ne_zero_of_not_neg_nat hc m
  have hpc' := poch_ne_zero_of_not_neg_nat hc' n
  calc appF2Coeff a b b' c c' m n * x ^ m * y ^ n
      = (poch b m / poch c m * (poch b' n / poch c' n)) *
          (poch a (m + n) / (m ! * n ! : ℂ) * x ^ m * y ^ n) := by
        rw [appF2Coeff]; field_simp
    _ = _ := by rw [← hG]; simp only [hddef]; ring

/-- 16.15.E3: appF3 euler integrable. -/
@[dlmf 16.15.E3]
theorem appF3_euler_integrable (a a' b b' c : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hrest : 0<(c-b-b').re) {x y : ℂ} (hxy : (x,y)∈appellEulerDomain) :
    IntegrableOn (appF3EulerKernel a a' b b' c x y) appellTriangle := by
  sorry

/-- 16.15.E3: appF3 euler analytic. -/
@[dlmf 16.15.E3]
theorem appF3_euler_analytic (a a' b b' c : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hrest : 0<(c-b-b').re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF3Euler a a' b b' c p.1 p.2) appellEulerDomain := by
  sorry

/-- 16.15.E3: appF3 euler germ. -/
@[dlmf 16.15.E3]
theorem appF3_euler_germ (a a' b b' c : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hrest : 0<(c-b-b').re) :
    (fun p : ℂ × ℂ => appF3 a a' b b' c p.1 p.2)=ᶠ[𝓝 (0,0)] (fun p => appF3Euler a a' b b' c p.1 p.2) := by
  sorry

/-- 16.15.E4: appF4 euler integrable. -/
@[dlmf 16.15.E4]
theorem appF4_euler_integrable (a b c c' : ℂ) (ha : 0<a.re) (hb : 0<b.re) (hca : a.re<c.re) (hcb : b.re<c'.re) {x y : ℂ} (hxy : (x,y)∈{p | AppellSquareSlit p}) :
    IntegrableOn (appF4EulerKernel a b c c' x y) (Icc (0:ℝ) 1×ˢIcc (0:ℝ) 1) := by
  have hK : IsCompact (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := left_mem_Icc.mpr zero_le_one
  obtain ⟨M1, hM1⟩ := ghaR4_inv_cpow_bound (f := fun p : ℝ × ℝ => 1 - (p.1:ℂ) * x)
    hK (by fun_prop) (fun p hp => by simpa using hxy p.1 hp.1 0 h0) (c + c' - a - 1)
  obtain ⟨M2, hM2⟩ := ghaR4_inv_cpow_bound (f := fun p : ℝ × ℝ => 1 - (p.2:ℂ) * y)
    hK (by fun_prop) (fun p hp => by simpa using hxy 0 h0 p.2 hp.2) (c + c' - b - 1)
  obtain ⟨M3, hM3⟩ := ghaR4_inv_cpow_bound (f := fun p : ℝ × ℝ => 1 - (p.1:ℂ) * x - (p.2:ℂ) * y)
    hK (by fun_prop) (fun p hp => hxy p.1 hp.1 p.2 hp.2) (a + b - c - c' + 1)
  have hca1 : 0 < (c - a).re := by simp; linarith
  have hcb1 : 0 < (c' - b).re := by simp; linarith
  refine ((ghaR4_beta_prod_integrableOn ha hca1 hb hcb1).mul_const (M1 * M2 * M3)).mono' ?_ ?_
  · exact (by unfold appF4EulerKernel; fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    have h1 := hM1 p hp
    have h2 := hM2 p hp
    have h3 := hM3 p hp
    have hM10 := (norm_nonneg _).trans h1
    have hM20 := (norm_nonneg _).trans h2
    have hM30 := (norm_nonneg _).trans h3
    simp only [appF4EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub, Complex.ofReal_one]
    calc ‖(p.1:ℂ) ^ (a - 1)‖ * ‖(p.2:ℂ) ^ (b - 1)‖ * ‖(1 - (p.1:ℂ)) ^ (c - a - 1)‖ *
          ‖(1 - (p.2:ℂ)) ^ (c' - b - 1)‖ * ‖((1 - (p.1:ℂ) * x) ^ (c + c' - a - 1))⁻¹‖ *
          ‖((1 - (p.2:ℂ) * y) ^ (c + c' - b - 1))⁻¹‖ *
          ‖((1 - (p.1:ℂ) * x - (p.2:ℂ) * y) ^ (a + b - c - c' + 1))⁻¹‖
        ≤ ‖(p.1:ℂ) ^ (a - 1)‖ * ‖(p.2:ℂ) ^ (b - 1)‖ * ‖(1 - (p.1:ℂ)) ^ (c - a - 1)‖ *
          ‖(1 - (p.2:ℂ)) ^ (c' - b - 1)‖ * M1 * M2 * M3 := by gcongr
      _ = _ := by ring

/-- 16.15.E4: appF4 euler analytic. -/
@[dlmf 16.15.E4]
theorem appF4_euler_analytic (a b c c' : ℂ) (ha : 0<a.re) (hb : 0<b.re) (hca : a.re<c.re) (hcb : b.re<c'.re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF4Euler a b c c' p.1 p.2) {p | AppellSquareSlit p} := by
  have hU := ghaR4_isOpen_square
  have hca1 : 0 < (c - a).re := by simp; linarith
  have hcb1 : 0 < (c' - b).re := by simp; linarith
  have hsq : MeasurableSet (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := left_mem_Icc.mpr zero_le_one
  have hd : DifferentiableOn ℂ (fun p : ℂ × ℂ =>
      ∫ q in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, appF4EulerKernel a b c c' p.1 p.2 q)
      {p | AppellSquareSlit p} := by
    refine differentiableOn_integral_of_locally_dominated hU
      (fun p _ => (by unfold appF4EulerKernel; fun_prop : Measurable _).aestronglyMeasurable)
      ?_ ?_
    · filter_upwards [ae_restrict_mem hsq] with q hq
      intro p hp
      have h1 := ghaR4_differentiableAt_inv_cpow_square (p := p) (u := q.1) (v := 0)
        (by simpa using hp q.1 hq.1 0 h0) (c + c' - a - 1)
      have h2 := ghaR4_differentiableAt_inv_cpow_square (p := p) (u := 0) (v := q.2)
        (by simpa using hp 0 h0 q.2 hq.2) (c + c' - b - 1)
      have h3 := ghaR4_differentiableAt_inv_cpow_square (p := p) (hp q.1 hq.1 q.2 hq.2)
        (a + b - c - c' + 1)
      have e : (fun p : ℂ × ℂ => appF4EulerKernel a b c c' p.1 p.2 q) = fun p =>
          (q.1:ℂ) ^ (a - 1) * (q.2:ℂ) ^ (b - 1) * ((1 - q.1:ℝ):ℂ) ^ (c - a - 1) *
            ((1 - q.2:ℝ):ℂ) ^ (c' - b - 1) *
            ((1 - (q.1:ℂ) * p.1 - ((0:ℝ):ℂ) * p.2) ^ (c + c' - a - 1))⁻¹ *
            ((1 - ((0:ℝ):ℂ) * p.1 - (q.2:ℂ) * p.2) ^ (c + c' - b - 1))⁻¹ *
            ((1 - (q.1:ℂ) * p.1 - (q.2:ℂ) * p.2) ^ (a + b - c - c' + 1))⁻¹ := by
        funext p; simp only [appF4EulerKernel, div_eq_mul_inv]; simp
      rw [e]
      exact ((((differentiableAt_const _).mul h1).mul h2).mul h3).differentiableWithinAt
    · intro p hp
      obtain ⟨r, hr, hs⟩ := ghaR4_exists_closedBall_square hp
      obtain ⟨M1, hM1⟩ := ghaR4_square_inv_cpow_bound
        (f := fun z : (ℂ × ℂ) × (ℝ × ℝ) => 1 - (z.2.1:ℂ) * z.1.1)
        (by fun_prop) (fun p hp q hq => by simpa using hs p hp q.1 hq.1 0 h0) (c + c' - a - 1)
      obtain ⟨M2, hM2⟩ := ghaR4_square_inv_cpow_bound
        (f := fun z : (ℂ × ℂ) × (ℝ × ℝ) => 1 - (z.2.2:ℂ) * z.1.2)
        (by fun_prop) (fun p hp q hq => by simpa using hs p hp 0 h0 q.2 hq.2) (c + c' - b - 1)
      obtain ⟨M3, hM3⟩ := ghaR4_square_inv_cpow_bound
        (f := fun z : (ℂ × ℂ) × (ℝ × ℝ) => 1 - (z.2.1:ℂ) * z.1.1 - (z.2.2:ℂ) * z.1.2)
        (by fun_prop) (fun p hp q hq => hs p hp q.1 hq.1 q.2 hq.2) (a + b - c - c' + 1)
      refine ⟨Metric.ball p r, Metric.ball_mem_nhds _ hr,
        fun q => ‖(q.1:ℂ)^(a-1) * (1 - (q.1:ℂ))^(c-a-1)‖ *
          ‖(q.2:ℂ)^(b-1) * (1 - (q.2:ℂ))^(c'-b-1)‖ * (M1 * M2 * M3), ?_, ?_⟩
      · exact (ghaR4_beta_prod_integrableOn ha hca1 hb hcb1).mul_const _
      · filter_upwards [ae_restrict_mem hsq] with q hq
        intro z hz
        have hz' := Metric.ball_subset_closedBall hz
        have h1 := hM1 z hz' q hq
        have h2 := hM2 z hz' q hq
        have h3 := hM3 z hz' q hq
        have hM10 := (norm_nonneg _).trans h1
        have hM20 := (norm_nonneg _).trans h2
        have hM30 := (norm_nonneg _).trans h3
        simp only [appF4EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub,
          Complex.ofReal_one]
        calc ‖(q.1:ℂ) ^ (a - 1)‖ * ‖(q.2:ℂ) ^ (b - 1)‖ * ‖(1 - (q.1:ℂ)) ^ (c - a - 1)‖ *
              ‖(1 - (q.2:ℂ)) ^ (c' - b - 1)‖ * ‖((1 - (q.1:ℂ) * z.1) ^ (c + c' - a - 1))⁻¹‖ *
              ‖((1 - (q.2:ℂ) * z.2) ^ (c + c' - b - 1))⁻¹‖ *
              ‖((1 - (q.1:ℂ) * z.1 - (q.2:ℂ) * z.2) ^ (a + b - c - c' + 1))⁻¹‖
            ≤ ‖(q.1:ℂ) ^ (a - 1)‖ * ‖(q.2:ℂ) ^ (b - 1)‖ * ‖(1 - (q.1:ℂ)) ^ (c - a - 1)‖ *
              ‖(1 - (q.2:ℂ)) ^ (c' - b - 1)‖ * M1 * M2 * M3 := by gcongr
          _ = _ := by ring
  have : DifferentiableOn ℂ (fun p : ℂ × ℂ => appF4Euler a b c c' p.1 p.2)
      {p | AppellSquareSlit p} := (differentiableOn_const _).mul hd
  exact this.analyticOnNhd_of_finiteDimensional hU

/-- 16.15.E4: appF4 euler germ. -/
@[dlmf 16.15.E4]
theorem appF4_euler_germ (a b c c' : ℂ) (ha : 0<a.re) (hb : 0<b.re) (hca : a.re<c.re) (hcb : b.re<c'.re) :
    (fun p : ℂ × ℂ => appF4 a b c c' (p.1*(1-p.2)) (p.2*(1-p.1)))=ᶠ[𝓝 (0,0)] (fun p => appF4Euler a b c c' p.1 p.2) := by
  sorry

/-- The Gauss series in the unit disk, as a scalar `HasSum`. -/
lemma ghaR4_gauss_hasSum {a b c z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => gaussHGCoeff a b c n * z ^ n) (₂F₁ a b c z) := by
  have := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).hasSum
    (y := z) (by simpa using mem_eball_one_of_norm_lt_one hz)
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using this

/-- 16.16.E2: appF2 reduction gauss. -/
@[dlmf 16.16.E2]
theorem appF2_reduction_gauss (a b b' c : ℂ) (hc : AppellRegular c) (hb' : AppellRegular b') :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF2 a b b' c b' x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-y)^(-a)*₂F₁ a b c (x/(1-y))) := by
  have hU : {p : ℂ × ℂ | ‖p.1‖ + ‖p.2‖ < 1} ∈ 𝓝 ((0:ℂ), (0:ℂ)) :=
    (isOpen_lt ((continuous_norm.comp continuous_fst).add (continuous_norm.comp continuous_snd))
      continuous_const).mem_nhds (by simp)
  filter_upwards [hU] with p hp
  obtain ⟨x, y⟩ := p
  simp only at hp ⊢
  have hy : ‖y‖ < 1 := by linarith [norm_nonneg x]
  have h1y : 1 - y ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h] at hy; simp at hy
  have hny : 1 - ‖y‖ ≤ ‖1 - y‖ := by
    have := norm_sub_norm_le (1 : ℂ) y; simpa using this
  have hz : ‖x / (1 - y)‖ < 1 := by
    rw [norm_div, div_lt_one (by linarith)]; linarith
  have hsum := hasSum_appF2 a b b' c b' hc hb' (x := x) (y := y) hp
  have hfib : ∀ m : ℕ, HasSum (fun n => appF2Coeff a b b' c b' m n * x ^ m * y ^ n)
      (gaussHGCoeff a b c m * x ^ m * (1 - y) ^ (-(a + m))) := by
    intro m
    have h := (hasSum_poch_div_factorial (β := a + m) hy).mul_left (gaussHGCoeff a b c m * x ^ m)
    refine h.congr_fun fun n => ?_
    have hpb := poch_ne_zero_of_not_neg_nat hb' n
    have hpc := poch_ne_zero_of_not_neg_nat hc m
    have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rw [appF2Coeff, gaussHGCoeff, poch_add a m n]
    field_simp
  have hG := hsum.prod_fiberwise hfib
  refine hG.unique ?_
  have h2 := (ghaR4_gauss_hasSum (a := a) (b := b) (c := c) hz).mul_left ((1 - y) ^ (-a))
  refine h2.congr_fun fun m => ?_
  rw [show -(a + (m : ℂ)) = -a + -(m : ℂ) by ring, cpow_add _ _ h1y, cpow_neg (1 - y) (m : ℂ),
    cpow_natCast, div_pow]
  field_simp

/-- Summing each row of the F3 double series gives a Gauss hypergeometric series. -/
lemma hasSum_appF3_gauss_fibers (a a' b b' c : ℂ) (hc : AppellRegular c)
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum (fun m : ℕ => poch a m * poch b m / (poch c m * m !) * x ^ m *
      ₂F₁ a' b' (c + m) y) (appF3 a a' b b' c x y) := by
  have hs := hasSum_appF3 a a' b b' c hc (x := x) (y := y) ⟨hx, hy⟩
  apply hs.prod_fiberwise
  intro m
  have h := (ghaR4_gauss_hasSum (a := a') (b := b') (c := c + m) hy).mul_left
    (poch a m * poch b m / (poch c m * m !) * x ^ m)
  refine h.congr_fun fun n => ?_
  rw [appF3Coeff, gaussHGCoeff, poch_add]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Summing each row of the F1 double series gives a Gauss hypergeometric series. -/
lemma hasSum_appF1_gauss_fibers (a b b' c : ℂ) (hc : AppellRegular c)
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum (fun m : ℕ => poch a m * poch b m / (poch c m * m !) * x ^ m *
      ₂F₁ (a + m) b' (c + m) y) (appF1 a b b' c x y) := by
  have hs := hasSum_appF1 a b b' c hc (x := x) (y := y) ⟨hx, hy⟩
  apply hs.prod_fiberwise
  intro m
  have h := (ghaR4_gauss_hasSum (a := a + m) (b := b') (c := c + m) hy).mul_left
    (poch a m * poch b m / (poch c m * m !) * x ^ m)
  refine h.congr_fun fun n => ?_
  rw [appF1Coeff, gaussHGCoeff, poch_add a, poch_add c]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Complementary first upper parameters reduce Appell F3 to F1 after a fractional
linear change of its second variable, as germs at the origin (DLMF 16.16.E4). -/
@[dlmf 16.16.E4]
theorem appF3_reduction_appF1 (a b b' c : ℂ) (hc : AppellRegular c) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF3 a (c-a) b b' c x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-y)^(-b')*appF1 a b b' c x (y/(y-1))) := by
  have hU : {p : ℂ × ℂ | ‖p.1‖ < 1 ∧ ‖p.2‖ < 1 / 3} ∈ 𝓝 ((0 : ℂ),(0 : ℂ)) :=
    ((isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)).mem_nhds (by norm_num)
  filter_upwards [hU] with p hp
  obtain ⟨x, y⟩ := p
  simp only at hp ⊢
  have hy : ‖y‖ < 1 := by linarith [hp.2]
  have hd : 0 < ‖1 - y‖ := by
    have := norm_sub_norm_le (1 : ℂ) y
    simp only [norm_one] at this
    linarith
  have hyt : ‖y / (y - 1)‖ < 1 := by
    rw [norm_div, norm_sub_rev y 1, div_lt_one hd]
    have := norm_sub_norm_le (1 : ℂ) y
    simp only [norm_one] at this
    linarith [hp.2]
  have hs := hasSum_appF3_gauss_fibers a (c - a) b b' c hc hp.1 hy
  have hs' := (hasSum_appF1_gauss_fibers a b b' c hc hp.1 hyt).mul_left ((1 - y)^ (-b'))
  apply hs.unique
  refine hs'.congr_fun fun m => ?_
  have hcm : ∀ j : ℕ, c + m ≠ -(j:ℂ) := by
    intro j he
    apply hc (m + j)
    push_cast
    linear_combination he
  rw [ordinaryHypergeometric_symm (c - a) b', pfaff_transformation_of_ne_neg_nat hcm hy hyt,
    show c+(m : ℂ)-(c - a) = a + m by ring, ordinaryHypergeometric_symm b' (a + m)]
  ring

/-- 16.16.E5_5: appF4 reduction appF1. -/
@[dlmf 16.16.E5_5]
theorem appF4_reduction_appF1 (a b c : ℂ) (hc : AppellRegular c) (hb : AppellRegular b) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF4 a b c b (x*(1-y)) (y*(1-x)))=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-x)^(-a)*(1-y)^(-a)*appF1 a (c-b) (a-c+1) c (x/(x-1)) (x*y/((1-x)*(1-y)))) := by
  sorry

/-- A geometric bound for the F4 coefficients at regular lower parameters. -/
lemma ghaR4_appF4Coeff_geom (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m n : ℕ, ‖appF4Coeff a b c c' m n‖ ≤ C * (8 ^ m * 8 ^ n) := by
  obtain ⟨C, hC⟩ := ghaR4_appF4Coeff_bound a b c c' hc hc' (σ := 2) (by norm_num)
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC (0, 0))
    simpa using this
  refine ⟨C, hC0, fun m n => (hC (m, n)).trans ?_⟩
  have h1 : (((m + n).choose m : ℕ) : ℝ) ≤ 2 ^ (m + n) := by exact_mod_cast Nat.choose_le_two_pow _ _
  calc C * 2 ^ (m + n) * (((m + n).choose m : ℕ) : ℝ) ^ 2 ≤ C * 2 ^ (m + n) * (2 ^ (m + n)) ^ 2 := by
        gcongr
    _ = C * (8 ^ m * 8 ^ n) := by
        have : (8:ℝ) ^ m * 8 ^ n = (2 ^ (m + n)) ^ 3 := by
          rw [← pow_add, show (8:ℝ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
        rw [this]; ring

/-- Summing the four-index family `appF4Fam` over its last two indices gives the `(m, n)`
term `c_{mn} (X(1-Y))ᵐ (Y(1-X))ⁿ` of the `F₄` double series. -/
private lemma ghaR4_appF4Fam_hasSum_fst (a b c c' X Y : ℂ) (p : ℕ × ℕ) :
    HasSum (fun q => appF4Fam a b c c' X Y (p, q))
      (appF4Coeff a b c c' p.1 p.2 * (X * (1 - Y)) ^ p.1 * (Y * (1 - X)) ^ p.2) := by
  obtain ⟨m, n⟩ := p
  have hfin := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _)
    (s := Finset.range (m + n + 1) ×ˢ Finset.range (m + n + 1))
    (f := fun q => appF4Fam a b c c' X Y ((m, n), q)) (fun q hq => by
      obtain ⟨M, N⟩ := q
      simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hq
      unfold appF4Fam
      simp only
      rcases hq with h | h
      · rw [appF4E_eq_zero_of_lt (by omega)]; simp
      · rw [appF4E_eq_zero_of_lt (m := n) (n := m) (by omega)]; simp)
  convert hfin using 1
  rw [Finset.sum_product]
  simp only [appF4Fam]
  have h1 := appF4E_sum m n X
  have h2 := appF4E_sum n m Y
  rw [show n + m + 1 = m + n + 1 by ring] at h2
  have : ∑ x ∈ Finset.range (m + n + 1), ∑ y ∈ Finset.range (m + n + 1),
      appF4Coeff a b c c' m n * (appF4E m n x * X ^ x) * (appF4E n m y * Y ^ y) =
      appF4Coeff a b c c' m n * ((∑ x ∈ Finset.range (m + n + 1), appF4E m n x * X ^ x) *
        (∑ y ∈ Finset.range (m + n + 1), appF4E n m y * Y ^ y)) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [this, h1, h2]
  simp only [mul_pow]
  ring

/-- Under `c + c' = a + b + 1`, summing `appF4Fam` over its first two indices gives the
product of the `(M, N)` terms of `₂F₁(a,b;c;X)` and `₂F₁(a,b;c';Y)`. -/
private lemma ghaR4_appF4Fam_hasSum_snd {a b c c' : ℂ} (hcc : c + c' = a + b + 1)
    (hpc : ∀ k, poch c k ≠ 0) (hpc' : ∀ k, poch c' k ≠ 0) (X Y : ℂ) (q : ℕ × ℕ) :
    HasSum (fun p => appF4Fam a b c c' X Y (p, q))
      (gaussHGCoeff a b c q.1 * X ^ q.1 * (gaussHGCoeff a b c' q.2 * Y ^ q.2)) := by
  obtain ⟨M, N⟩ := q
  have hfin := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _)
    (s := Finset.range (M + 1) ×ˢ Finset.range (N + 1))
    (f := fun p => appF4Fam a b c c' X Y (p, (M, N))) (fun p hp => by
      obtain ⟨m, n⟩ := p
      simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hp
      unfold appF4Fam appF4E
      simp only
      rcases hp with h | h
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; simp
      · rw [ite_eq_right_of_eq_false (c := n ≤ N) _ _ (eq_false (by omega))]; simp)
  convert hfin using 1
  rw [Finset.sum_product]
  simp only
  rw [show gaussHGCoeff a b c M * X ^ M * (gaussHGCoeff a b c' N * Y ^ N) =
    (gaussHGCoeff a b c M * gaussHGCoeff a b c' N) * (X ^ M * Y ^ N) by ring,
    ← appF4_coeff hcc hpc hpc' M N, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hmM : m ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  unfold appF4Fam appF4Term appF4E
  simp only
  rw [ite_eq_left_of_eq_true _ _ (eq_true hmM), ite_eq_left_of_eq_true _ _ (eq_true hnN)]
  ring

/-- Bailey's product formula at all regular lower parameters (stronger than `appF4_bailey`,
which assumes positive real parts). The proof is that of `appF4_bailey` in
`DLMF.Hypergeometric.AppellF4`, with its coefficient bound replaced by `ghaR4_appF4Coeff_geom`. -/
lemma ghaR4_appF4_bailey {a b c c' : ℂ} (hcc : c + c' = a + b + 1) (hc : AppellRegular c)
    (hc' : AppellRegular c') : ∃ δ > 0, ∀ X Y : ℂ, ‖X‖ < δ → ‖Y‖ < δ →
      HasSum (fun p : ℕ × ℕ => appF4Coeff a b c c' p.1 p.2 * (X * (1 - Y)) ^ p.1 *
        (Y * (1 - X)) ^ p.2) (₂F₁ a b c X * ₂F₁ a b c' Y) := by
  obtain ⟨C, hC0, hCb⟩ := ghaR4_appF4Coeff_geom a b c c' hc hc'
  refine ⟨1 / 1024, by norm_num, fun X Y hX hY => ?_⟩
  have hpc : ∀ k, poch c k ≠ 0 := poch_ne_zero_of_not_neg_nat hc
  have hpc' : ∀ k, poch c' k ≠ 0 := poch_ne_zero_of_not_neg_nat hc'
  have hsq : ∀ W : ℂ, ‖W‖ < 1 / 1024 → Real.sqrt ‖W‖ < 1 / 32 := by
    intro W hW
    rw [show (1 / 32 : ℝ) = Real.sqrt (1 / 1024) by
      rw [show (1 / 1024 : ℝ) = (1 / 32) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] ]
    exact Real.sqrt_lt_sqrt (norm_nonneg _) hW
  have hX1 : ‖X‖ ≤ 1 := by linarith
  have hY1 : ‖Y‖ ≤ 1 := by linarith
  set sX := Real.sqrt ‖X‖ with hsX
  set sY := Real.sqrt ‖Y‖ with hsY
  have hsX0 : 0 ≤ sX := Real.sqrt_nonneg _
  have hsY0 : 0 ≤ sY := Real.sqrt_nonneg _
  have hsXQ : sX < 1 / 32 := hsq X hX
  have hsYQ : sY < 1 / 32 := hsq Y hY
  have hsX1 : sX < 1 := by linarith
  have hsY1 : sY < 1 := by linarith
  set rX := 2 * 8 * sX with hrX
  set rY := 2 * 8 * sY with hrY
  have hrX0 : 0 ≤ rX := by positivity
  have hrY0 : 0 ≤ rY := by positivity
  have hrX1 : rX < 1 := by rw [hrX]; linarith
  have hrY1 : rY < 1 := by rw [hrY]; linarith
  have hgeo : ∀ u v : ℝ, 0 ≤ u → u < 1 → 0 ≤ v → v < 1 →
      Summable fun p : ℕ × ℕ => u ^ p.1 * v ^ p.2 := fun u v hu0 hu1 hv0 hv1 =>
    (summable_geometric_of_lt_one hu0 hu1).mul_of_nonneg (summable_geometric_of_lt_one hv0 hv1)
      (fun _ => by positivity) (fun _ => by positivity)
  have hD : Summable fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
      C * ((rX ^ p.1.1 * rY ^ p.1.2) * (sX ^ p.2.1 * sY ^ p.2.2)) :=
    ((hgeo rX rY hrX0 hrX1 hrY0 hrY1).mul_of_nonneg (hgeo sX sY hsX0 hsX1 hsY0 hsY1)
      (fun _ => by positivity) (fun _ => by positivity)).mul_left C
  have hsum : Summable (appF4Fam a b c c' X Y) := by
    refine Summable.of_norm_bounded hD fun p => ?_
    obtain ⟨⟨m, n⟩, ⟨M, N⟩⟩ := p
    unfold appF4Fam
    simp only
    rw [norm_mul, norm_mul]
    have h1 := hCb m n
    have h2 := appF4E_norm_le m n M hX1
    have h3 := appF4E_norm_le n m N hY1
    calc ‖appF4Coeff a b c c' m n‖ * ‖appF4E m n M * X ^ M‖ * ‖appF4E n m N * Y ^ N‖
        ≤ (C * (8 ^ m * 8 ^ n)) * (2 ^ n * sX ^ m * sX ^ M) * (2 ^ m * sY ^ n * sY ^ N) := by
          gcongr
      _ = _ := by rw [hrX, hrY]; simp only [mul_pow]; ring
  have hS := hsum.hasSum
  have hfib1 := ghaR4_appF4Fam_hasSum_fst a b c c' X Y
  have hF4 := hS.prod_fiberwise hfib1
  have hfib2 := ghaR4_appF4Fam_hasSum_snd hcc hpc hpc' X Y
  have hS' : HasSum (fun x : (ℕ × ℕ) × (ℕ × ℕ) => appF4Fam a b c c' X Y (x.2, x.1))
      (∑' p, appF4Fam a b c c' X Y p) :=
    ((Equiv.prodComm (ℕ × ℕ) (ℕ × ℕ)).hasSum_iff (f := appF4Fam a b c c' X Y)).mpr hS
  have hG := hS'.prod_fiberwise hfib2
  have hXs := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one (show ‖X‖ < 1 by linarith))
  have hYs := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c').hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one (show ‖Y‖ < 1 by linarith))
  have hprod := hXs.mul hYs hG.summable
  rw [hG.unique hprod] at hF4
  exact hF4

/-- 16.16.E6: appF4 product germ. -/
@[dlmf 16.16.E6]
theorem appF4_product_germ (a b c : ℂ) (hc : AppellRegular c) (hc' : AppellRegular (a+b-c+1)) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF4 a b c (a+b-c+1) (x*(1-y)) (y*(1-x)))=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; ₂F₁ a b c x*₂F₁ a b (a+b-c+1) y) := by
  obtain ⟨δ, hδ, h⟩ := ghaR4_appF4_bailey (a := a) (b := b) (c := c) (c' := a + b - c + 1)
    (by ring) hc hc'
  have hU : {p : ℂ × ℂ | ‖p.1‖ < δ ∧ ‖p.2‖ < δ} ∈ 𝓝 ((0:ℂ), (0:ℂ)) :=
    ((isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)).mem_nhds
      (by simp [hδ])
  filter_upwards [hU] with p hp
  exact (h p.1 p.2 hp.1 hp.2).tsum_eq

/-- Exchanging the two pairs of upper parameters exchanges the F3 variables. -/
lemma appF3_swap (a a' b b' c x y : ℂ) :
    appF3 a a' b b' c x y = appF3 a' a b' b c y x := by
  rw [appF3, appF3, ← (Equiv.prodComm ℕ ℕ).tsum_eq]
  apply tsum_congr
  rintro ⟨m, n⟩
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  rw [appF3Coeff_swap a a' b b' c n m]
  ring

/-- Exchanging the two separate upper parameters exchanges the F1 variables. -/
lemma appF1_swap (a b b' c x y : ℂ) :
    appF1 a b b' c x y = appF1 a b' b c y x := by
  rw [appF1, appF1, ← (Equiv.prodComm ℕ ℕ).tsum_eq]
  apply tsum_congr
  rintro ⟨m, n⟩
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  rw [appF1Coeff_swap a b b' c n m]
  ring

/-- Pfaff's simultaneous fractional linear change of both Appell F1 variables,
as analytic germs at the origin (DLMF 16.16.E8). -/
@[dlmf 16.16.E8]
theorem appF1_pfaff_first (a b b' c : ℂ) (hc : AppellRegular c) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF1 a b b' c x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-x)^(-b)*(1-y)^(-b')*appF1 (c-a) b b' c (x/(x-1)) (y/(y-1))) := by
  let T : ℂ → ℂ := fun z => z / (z-1)
  have hT : ContinuousAt T 0 := by
    dsimp [T]
    exact continuousAt_id.div (continuousAt_id.sub continuousAt_const) (by norm_num)
  have h0 : T 0 = 0 := by simp [T]
  have hC1 : Tendsto (fun p : ℂ × ℂ => (p.1, T p.2)) (𝓝 (0, 0)) (𝓝 (0, 0)) := by
    simpa only [Function.comp_apply, h0] using continuous_fst.continuousAt.prodMk
      (hT.comp_of_eq (continuous_snd.continuousAt (x := ((0 : ℂ),(0 : ℂ)))) rfl) |>.tendsto
  have hC2 : Tendsto (fun p : ℂ × ℂ => (T p.2, p.1)) (𝓝 (0, 0)) (𝓝 (0, 0)) := by
    simpa only [Function.comp_apply, h0] using
      (hT.comp_of_eq (continuous_snd.continuousAt (x := ((0 : ℂ), (0 : ℂ)))) rfl).prodMk
      continuous_fst.continuousAt |>.tendsto
  have h1 := (appF3_reduction_appF1 a b b' c hc).comp_tendsto hC1
  have h2 := (appF3_reduction_appF1 (c - a) b' b c hc).comp_tendsto hC2
  have hU : {p : ℂ × ℂ | ‖p.1‖ < 1 ∧ ‖p.2‖ < 1} ∈ 𝓝 ((0 : ℂ),(0 : ℂ)) :=
    ((isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)).mem_nhds (by norm_num)
  filter_upwards [h1, h2, hU] with p h1 h2 hp
  obtain ⟨x, y⟩ := p
  simp only [Function.comp_apply] at h1 h2 ⊢
  have hy : y - 1 ≠ 0 := by
    intro he
    rw [sub_eq_zero.mp he] at hp
    simp at hp
  have hy1 : 1 - y ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hy))
  have hinv : 1 - T y = (1 - y)⁻¹ := by dsimp [T]; field_simp [hy1, hy]; ring
  have hTT : T (T y) = y := by dsimp [T]; field_simp [hy1, hy]; ring
  have harg : (1 - y).arg ≠ Real.pi := by
    have hslit : 1 - y ∈ slitPlane := by
      left
      have := re_le_norm y
      simp only [sub_re, one_re]
      linarith [hp.2]
    exact (arg_lt_pi_iff.mpr (hslit.imp_left le_of_lt)).ne
  change appF3 a (c - a) b b' c x (T y) = (1 - T y)^ (-b') * appF1 a b b' c x (T (T y)) at h1
  rw [hinv, hTT, inv_cpow _ _ harg] at h1
  rw [show c - (c - a) = a by ring, ← appF3_swap a (c - a) b b' c x (T y),
    appF1_swap (c - a) b' b c (T y) (T x)] at h2
  rw [h2] at h1
  have hne : (1 - y)^ (-b') ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hy1)
  have hh := congrArg (fun v : ℂ => (1 - y)^ (-b') * v) h1
  rw [mul_inv_cancel_left₀ hne] at hh
  calc appF1 a b b' c x y = _ := hh.symm
       _ = _ := by dsimp only [T]; ring

/-- Summing each column of the F2 double series gives a Gauss hypergeometric series. -/
lemma hasSum_appF2_gauss_fibers (a b b' c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c')
    {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    HasSum (fun n : ℕ => poch a n * poch b' n / (poch c' n * n !) * y ^ n *
      ₂F₁ (a + n) b c x) (appF2 a b b' c c' x y) := by
  have hs := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr (hasSum_appF2 a b b' c c' hc hc' hxy)
  apply hs.prod_fiberwise
  intro n
  have hx : ‖x‖ < 1 := by linarith [norm_nonneg y]
  have h := (ghaR4_gauss_hasSum (a := a + n) (b := b) (c := c) hx).mul_left
    (poch a n * poch b' n / (poch c' n * n !) * y ^ n)
  refine h.congr_fun fun m => ?_
  change appF2Coeff a b b' c c' m n * x ^ m * y ^ n = _
  rw [appF2Coeff, gaussHGCoeff, show m + n = n + m by omega, poch_add]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Pfaff's transformation in the first F2 variable rescales the second variable,
as analytic germs at the origin (DLMF 16.16.E9). -/
@[dlmf 16.16.E9]
theorem appF2_pfaff (a b b' c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF2 a b b' c c' x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-x)^(-a)*appF2 a (c-b) b' c c' (x/(x-1)) (y/(1-x))) := by
  have hU : {p : ℂ × ℂ | ‖p.1‖ + ‖p.2‖ < 1 / 3} ∈ 𝓝 ((0 : ℂ),(0 : ℂ)) :=
    (isOpen_lt ((continuous_norm.comp continuous_fst).add (continuous_norm.comp continuous_snd))
      continuous_const).mem_nhds (by norm_num)
  filter_upwards [hU] with p hp
  obtain ⟨x, y⟩ := p
  simp only at hp ⊢
  have hx : ‖x‖ < 1 := by linarith [norm_nonneg y]
  have h1x : 1 - x ≠ 0 := by
    intro he
    have : x = 1 := by linear_combination -he
    simp [this] at hx
  have hden : 1 - ‖x‖ ≤ ‖1 - x‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) x
  have hd : 0 < ‖1 - x‖ := norm_pos_iff.mpr h1x
  have ht : ‖x / (x - 1)‖ + ‖y / (1 - x)‖ < 1 := by
    rw [norm_div, norm_div, norm_sub_rev x 1, ← add_div, div_lt_one hd]
    linarith [norm_nonneg x, norm_nonneg y]
  have hxt : ‖x / (x - 1)‖ < 1 := by linarith [norm_nonneg (y / (1 - x))]
  have hs := hasSum_appF2_gauss_fibers a b b' c c' hc hc' (x := x) (y := y) (by linarith)
  have hs' := (hasSum_appF2_gauss_fibers a (c - b) b' c c' hc hc' ht).mul_left ((1 - x)^ (-a))
  apply hs.unique
  refine hs'.congr_fun fun n => ?_
  rw [pfaff_transformation_of_ne_neg_nat hc hx hxt]
  rw [show -(a+(n : ℂ)) = -a + -(n : ℂ) by ring, cpow_add _ _ h1x,
    cpow_neg (1 - x) (n : ℂ), cpow_natCast, div_pow]
  ring

/-- 16.16.E7: appF4 burchnall chaundy. -/
@[dlmf 16.16.E7]
theorem appF4_burchnall_chaundy (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') :
    ∃ δ>0,∀ x y : ℂ,‖x‖<δ→‖y‖<δ→
      HasSum (fun k : ℕ => poch a k*poch b k*poch (a+b-c-c'+1) k/
        (poch c k*poch c' k*k !)*x^k*y^k*₂F₁ (a+k) (b+k) (c+k) x*
          ₂F₁ (a+k) (b+k) (c'+k) y) (appF4 a b c c' (x*(1-y)) (y*(1-x))) := by
  sorry

/-- The large-variable formula is a branch reached by analytic continuation, not a divergent-series identity. -/
@[dlmf 16.16.E10]
theorem appF4_infinity_connection (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c')
    (hab : ∀ k : ℤ,a-b≠k) {x y : ℂ}
    (hconv : (x/y,1/y)∈appellF4Domain) (hy : -y∈slitPlane) :
    IsAppellBranchAt (fun p : ℂ × ℂ => appF4 a b c c' p.1 p.2) (x,y)
      (fun p => Gamma c'*Gamma (b-a)/(Gamma (c'-a)*Gamma b)*(-p.2)^(-a)*
        appF4 a (a-c'+1) c (a-b+1) (p.1/p.2) (1/p.2)+
        Gamma c'*Gamma (a-b)/(Gamma (c'-b)*Gamma a)*(-p.2)^(-b)*
        appF4 b (b-c'+1) c (b-a+1) (p.1/p.2) (1/p.2)) := by
  sorry

/-- Coalescing exponent parameters require the combined connection expression limit. -/
@[dlmf 16.16.E10]
theorem appF4_infinity_resonance_limits {a b c c' : ℂ} (hc : AppellRegular c) (hc' : AppellRegular c')
    (k : ℤ) (hab : a-b=k) {x y : ℂ} (hconv : (x/y,1/y)∈appellF4Domain) (hy : -y∈slitPlane) :
    ∃ L : ℂ,Tendsto (fun a' : ℂ =>
      Gamma c'*Gamma (b-a')/(Gamma (c'-a')*Gamma b)*(-y)^(-a')*
        appF4 a' (a'-c'+1) c (a'-b+1) (x/y) (1/y)+
      Gamma c'*Gamma (a'-b)/(Gamma (c'-b)*Gamma a')*(-y)^(-b)*
        appF4 b (b-c'+1) c (b-a'+1) (x/y) (1/y)) (𝓝[≠] a) (𝓝 L) := by
  sorry

end DLMF.Hypergeometric

end
