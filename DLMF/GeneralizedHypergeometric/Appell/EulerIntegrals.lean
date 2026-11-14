/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Appell.Basic.EulerBranches

public import DLMF.GeneralizedHypergeometric.Appell.SeriesAndDifferentialEquations
import DLMF.GeneralizedHypergeometric.Appell.ComposedF4
import DLMF.GeneralizedHypergeometric.Appell.BurchnallChaundy
import DLMF.GeneralizedHypergeometric.Appell.EulerF4
import DLMFMathlib.Analysis.Integral.WeightedSeries
public import DLMF.GeneralizedHypergeometric.Appell.TriangleDirichlet

/-!
# Euler integrals for Appell functions (DLMF §§16.15–16.16)

Integrability and analyticity of the Euler integrals of the Appell functions, their agreement
with the double series as germs at the origin, and the reductions and transformations that
follow.

## Main results

* `appellF1_euler_integrable`, `appellF1_euler_analytic`, `appellF1_euler_germ`: the Euler integral
  of `F₁`, DLMF 16.15.1; likewise for `F₂`, `F₃`, `F₄` (16.15.2–16.15.4).
* `appellF2_reduction_gauss`, `appellF3_reduction_appellF1`, `appellF4_reduction_appellF1`:
  reductions, DLMF 16.16.2, 16.16.4, 16.16.5_5.
* `appellF4_product_germ`, `appellF4_burchnall_chaundy`: DLMF 16.16.6–16.16.7.
* `appellF1_pfaff_first`, `appellF2_pfaff`: Pfaff transformations, DLMF 16.16.8–16.16.9.
* `appellF4_infinity_connection`, `appellF4_infinity_resonance_limits`: the connection formula at
  infinity, DLMF 16.16.10, as a continued branch.

## Implementation notes

The simplex integral of `F₃` uses Dirichlet's integral on the triangle
(`DLMF.GeneralizedHypergeometric.Appell.TriangleDirichlet`). The `F₃`-to-`F₁` reduction and the
`F₁`/`F₂` Pfaff transformations use Gauss-series fiber sums and
`pfaff_transformation_of_ne_neg_nat`, retaining all regular lower parameters.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Polynomial

open scoped Real Topology Nat Interval

namespace DLMF.Hypergeometric

/-! ## Euler integral branches with actual integrability -/

/-- The segment from `1` to `1 - w` stays in the slit plane. -/
private lemma one_sub_mul_mem_slitPlane_of_one_sub_mem {w : ℂ} (hw : 1 - w ∈ slitPlane) {u : ℝ}
    (hu : u ∈ Icc (0:ℝ) 1) :
    1 - (u:ℂ) * w ∈ slitPlane := by
  have := starConvex_one_slitPlane.add_smul_mem (y := -w) (by simpa [sub_eq_add_neg] using hw)
    hu.1 hu.2
  convert this using 1
  simp [Complex.real_smul]
  ring

/-- A reciprocal principal power of a slit-valued continuous function is bounded on a compact set.
-/
private lemma exists_norm_inv_cpow_le_of_isCompact {α : Type*} [TopologicalSpace α]
    {f : α → ℂ} {s : Set α}
    (hs : IsCompact s) (hf : ContinuousOn f s)
    (hslit : ∀ u ∈ s, f u ∈ slitPlane) (b : ℂ) :
    ∃ M : ℝ, ∀ u ∈ s, ‖(f u ^ b)⁻¹‖ ≤ M := by
  have hc : ContinuousOn (fun u => (f u ^ b)⁻¹) s := by
    refine ContinuousOn.inv₀ (hf.cpow_const hslit) fun u hu => ?_
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => slitPlane_ne_zero (hslit u hu) h.1
  exact hs.exists_bound_of_continuousOn hc

/-- The Euler beta kernel is integrable on `[0,1]`. -/
private lemma integrableOn_betaKernel {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^(u-1) * (1 - (t:ℂ))^(v-1)) (Icc 0 1) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc,
    ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact Complex.betaIntegral_convergent hu hv

/-- The product of two beta kernels is integrable on the unit square. -/
private lemma integrableOn_norm_betaKernel_mul_norm_betaKernel {u v u' v' : ℂ} (hu : 0 < u.re)
    (hv : 0 < v.re)
    (hu' : 0 < u'.re) (hv' : 0 < v'.re) :
    IntegrableOn (fun p : ℝ × ℝ => ‖(p.1:ℂ)^(u-1) * (1 - (p.1:ℂ))^(v-1)‖ *
      ‖(p.2:ℂ)^(u'-1) * (1 - (p.2:ℂ))^(v'-1)‖) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact (integrableOn_betaKernel hu hv).norm.mul_prod (integrableOn_betaKernel hu' hv').norm

/-- The set where `1 - x` lies in the slit plane is open. -/
private lemma isOpen_one_sub_mem_slitPlane : IsOpen {x : ℂ | 1 - x ∈ slitPlane} :=
  isOpen_slitPlane.preimage (by fun_prop)

/-- A closed ball on which `1 - x` stays in the slit plane. -/
private lemma exists_closedBall_one_sub_mem_slitPlane {x₀ : ℂ} (hx : 1 - x₀ ∈ slitPlane) :
    ∃ r > 0, Metric.closedBall x₀ r ⊆ {x : ℂ | 1 - x ∈ slitPlane} := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp isOpen_one_sub_mem_slitPlane x₀ hx
  exact ⟨r / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hsub⟩

/-- Uniform bound for `(1 - u x)^(-b)` over `u ∈ [0,1]` and `x` in a slit-admissible closed ball. -/
private lemma exists_norm_inv_one_sub_mul_cpow_le {x₀ : ℂ} {r : ℝ}
    (hr : Metric.closedBall x₀ r ⊆ {x : ℂ | 1 - x ∈ slitPlane}) (b : ℂ) :
    ∃ M : ℝ, ∀ u ∈ Icc (0:ℝ) 1, ∀ x ∈ Metric.closedBall x₀ r, ‖((1 - (u:ℂ) * x) ^ b)⁻¹‖ ≤ M := by
  obtain ⟨M, hM⟩ := exists_norm_inv_cpow_le_of_isCompact (f := fun q : ℝ × ℂ => 1 - (q.1:ℂ) * q.2)
    (isCompact_Icc.prod (isCompact_closedBall x₀ r)) (by fun_prop)
    (fun q hq => one_sub_mul_mem_slitPlane_of_one_sub_mem (hr hq.2) hq.1) b
  exact ⟨M, fun u hu x hx => hM (u, x) ⟨hu, hx⟩⟩

/-- Differentiability of `x ↦ (1 - u x)^(-b)` on the Euler domain. -/
private lemma differentiableAt_inv_one_sub_mul_cpow {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) {x : ℂ}
    (hx : 1 - x ∈ slitPlane) (b : ℂ) :
    DifferentiableAt ℂ (fun x : ℂ => ((1 - (u:ℂ) * x) ^ b)⁻¹) x := by
  have hs := one_sub_mul_mem_slitPlane_of_one_sub_mem hx hu
  refine (((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)).cpow
    (differentiableAt_const b) hs).inv ?_
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => slitPlane_ne_zero hs h.1

/-- The square-slit condition is open. -/
private lemma eventually_appellSquareSlit {p₀ : ℂ × ℂ} (h : AppellSquareSlit p₀) :
    ∀ᶠ p in 𝓝 p₀, AppellSquareSlit p := by
  have hK : IsCompact (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have := hK.eventually_forall_of_forall_eventually (x₀ := p₀)
    (P := fun p q => 1 - (q.1:ℂ) * p.1 - (q.2:ℂ) * p.2 ∈ slitPlane) (fun q hq => by
      have hc : Continuous fun z : (ℂ × ℂ) × (ℝ × ℝ) => 1 - (z.2.1:ℂ) * z.1.1 -
          (z.2.2:ℂ) * z.1.2 := by
        fun_prop
      exact hc.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds (h q.1 hq.1 q.2 hq.2)))
  filter_upwards [this] with p hp u hu v hv
  exact hp (u, v) ⟨hu, hv⟩

/-- The F2/F4 Euler domain is open. -/
private lemma isOpen_appellSquareSlit : IsOpen {p : ℂ × ℂ | AppellSquareSlit p} :=
  isOpen_iff_mem_nhds.mpr fun _ hp => eventually_appellSquareSlit hp

/-- A closed ball inside the F2/F4 Euler domain. -/
private lemma exists_closedBall_appellSquareSlit {p₀ : ℂ × ℂ} (h : AppellSquareSlit p₀) :
    ∃ r > 0, ∀ p ∈ Metric.closedBall p₀ r, AppellSquareSlit p := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp isOpen_appellSquareSlit p₀ h
  exact ⟨r / 2, by positivity, fun p hp => hsub (Metric.closedBall_subset_ball (by linarith) hp)⟩

/-- A uniform bound for a reciprocal power along the square, for parameters near a point. -/
private lemma exists_norm_inv_cpow_le_square {p₀ : ℂ × ℂ} {r : ℝ}
    {f : (ℂ × ℂ) × (ℝ × ℝ) → ℂ} (hf : Continuous f)
    (hs : ∀ p ∈ Metric.closedBall p₀ r, ∀ q ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, f (p, q) ∈ slitPlane)
    (b : ℂ) :
    ∃ M : ℝ, ∀ p ∈ Metric.closedBall p₀ r, ∀ q ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1,
      ‖(f (p, q) ^ b)⁻¹‖ ≤ M := by
  obtain ⟨M, hM⟩ := exists_norm_inv_cpow_le_of_isCompact (f := f)
    ((isCompact_closedBall p₀ r).prod (isCompact_Icc.prod isCompact_Icc)) hf.continuousOn
    (fun z hz => hs z.1 hz.1 z.2 hz.2) b
  exact ⟨M, fun p hp q hq => hM (p, q) ⟨hp, hq⟩⟩

/-- Differentiability of the square-integral denominator power. -/
private lemma differentiableAt_inv_one_sub_mul_sub_mul_cpow {p : ℂ × ℂ} {u v : ℝ}
    (hs : 1 - (u:ℂ) * p.1 - (v:ℂ) * p.2 ∈ slitPlane) (b : ℂ) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => ((1 - (u:ℂ) * p.1 - (v:ℂ) * p.2) ^ b)⁻¹) p := by
  have hf : DifferentiableAt ℂ (fun p : ℂ × ℂ => 1 - (u:ℂ) * p.1 - (v:ℂ) * p.2) p := by fun_prop
  refine (hf.cpow (differentiableAt_const b) hs).inv ?_
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => slitPlane_ne_zero hs h.1

/-- Absolute convergence of the binomial series `∑ (b)ₘ xᵐ/m!` in the unit disk. -/
private lemma summable_norm_pochhammer_div_factorial_mul_pow_of_norm_lt_one (b : ℂ) {x : ℂ}
    (hx : ‖x‖ < 1) :
    Summable fun m : ℕ => ‖pochhammer b m / m ! * x ^ m‖ := by
  set σ := 2 / (1 + ‖x‖) with hσ
  have hx0 := norm_nonneg x
  have hσ1 : 1 < σ := by rw [hσ, lt_div_iff₀ (by linarith)]; linarith
  have hσx : σ * ‖x‖ < 1 := by
    rw [hσ, div_mul_eq_mul_div, div_lt_one (by linarith)]; linarith
  obtain ⟨C, hC0, hC⟩ := norm_pochhammer_le_mul_factorial b hσ1
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    ((summable_geometric_of_lt_one (by positivity) hσx).mul_left C)
  have hf : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
  rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow, div_mul_eq_mul_div,
    div_le_iff₀ hf, mul_pow]
  calc ‖pochhammer b m‖ * ‖x‖ ^ m ≤ (C * σ ^ m * m !) * ‖x‖ ^ m := by gcongr; exact hC m
    _ = _ := by ring

/-- Binomially weighted bound for the two-variable binomial coefficients. -/
private lemma exists_norm_pochhammer_add_div_factorial_mul_le (a : ℂ) {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, ∀ q : ℕ × ℕ, ‖pochhammer a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ)‖ ≤
      C * σ ^ (q.1 + q.2) * ((q.1 + q.2).choose q.1 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := norm_pochhammer_le_mul_factorial a hσ
  refine ⟨C, fun ⟨m, n⟩ => ?_⟩
  have hm : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
  have hn : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have hfac : ((m + n) ! : ℝ) = ((m + n).choose m : ℝ) * m ! * n ! := by
    have := Nat.add_choose_mul_factorial_mul_factorial m n
    rw [← Nat.choose_symm_add] at this
    exact_mod_cast this.symm
  simp only
  rw [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast, div_le_iff₀ (by positivity)]
  calc ‖pochhammer a (m + n)‖ ≤ C * σ ^ (m + n) * (m + n) ! := hC _
    _ = _ := by rw [hfac]; ring

/-- The two-variable binomial series `(1-s-t)^(-a) = ∑ (a)ₘ₊ₙ sᵐ tⁿ/(m! n!)`. -/
private lemma hasSum_two_var_binomial (a : ℂ) {s t : ℂ} (hst : ‖s‖ + ‖t‖ < 1) :
    HasSum (fun q : ℕ × ℕ => pochhammer a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ) * s ^ q.1 * t ^ q.2)
      ((1 - s - t) ^ (-a)) ∧
    Summable (fun q : ℕ × ℕ => ‖pochhammer a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ) * s ^ q.1 *
        t ^ q.2‖) := by
  set f := fun q : ℕ × ℕ => pochhammer a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ) * s ^ q.1 *
      t ^ q.2 with hf
  have hnorm : Summable fun q => ‖f q‖ := by
    obtain ⟨A, B, hA, hB, hS⟩ := exists_summable_doubleSeries_of_diamond
      (fun q : ℕ × ℕ => pochhammer a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ))
      (fun _ hσ => exists_norm_pochhammer_add_div_factorial_mul_le a hσ) hst
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_) hS
    simp only [hf, norm_mul, norm_pow]
    have := norm_nonneg (pochhammer a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ))
    have hA0 : 0 ≤ A := (norm_nonneg _).trans hA.le
    gcongr
  refine ⟨?_, hnorm⟩
  have hT := (Summable.of_norm hnorm).hasSum
  have hT' : HasSum (f ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) (∑' q, f q) :=
    (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff).mpr hT
  have hfib : ∀ N : ℕ, HasSum (fun c : Finset.antidiagonal N =>
      (f ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) ⟨N, c⟩)
          (pochhammer a N / N ! * (s + t) ^ N) := by
    intro N
    convert hasSum_fintype (fun c : Finset.antidiagonal N =>
      (f ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) ⟨N, c⟩) using 1
    rw [(Commute.all s t).add_pow', Finset.mul_sum, ← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun c _ => ?_
    obtain ⟨⟨m, n⟩, hc⟩ := c
    have hmn : m + n = N := Finset.mem_antidiagonal.mp hc
    subst hmn
    simp only [Function.comp, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply,
        hf, nsmul_eq_mul]
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
  have h1 := hasSum_pochhammer_div_factorial (β := a) hst'
  rw [show 1 - s - t = 1 - (s + t) by ring, h1.unique hG]
  exact hT

/-- Beta-integral moments on `[0,1]`. -/
private lemma setIntegral_betaKernel_mul_pow {b γ : ℂ} (m : ℕ) :
    (∫ u in Icc (0:ℝ) 1, (u:ℂ) ^ (b - 1) * ((1 - u : ℝ) : ℂ) ^ (γ - 1) * (u:ℂ) ^ m) =
      betaIntegral (b + m) γ := by
  rw [integral_Icc_eq_integral_Ioc, betaIntegral, intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  have hu0 : (u:ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.1.ne'
  rw [show b + (m : ℂ) - 1 = (b - 1) + (m : ℂ) by ring, cpow_add _ _ hu0, cpow_natCast]
  push_cast
  ring

/-- The normalized beta moment `Γ(c)B(b+m,c-b)/(Γ(b)Γ(c-b)) = (b)ₘ/(c)ₘ`. -/
private lemma Gamma_div_mul_betaIntegral_eq_pochhammer_div_pochhammer {b c : ℂ} (hb : 0 < b.re)
    (hcb : 0 < (c - b).re) (m : ℕ) :
    Gamma c / (Gamma b * Gamma (c - b)) * betaIntegral (b + m) (c - b) = pochhammer b m /
        pochhammer c m := by
  have hE := euler_term_eq_gaussHypergeometricCoeff (a := 1) (b := b) (c := c) m hb hcb
  have hf : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hc : ∀ k : ℕ, c ≠ -k := not_neg_nat_of_re_pos (re_c_pos_of hb hcb)
  rw [pochhammer_nat_one, div_self hf, one_mul] at hE
  rw [hE, gaussHypergeometricCoeff, pochhammer_nat_one]
  have hpc := pochhammer_ne_zero_of_not_neg_nat hc m
  field_simp

/-- 16.15.E1: appellF1 euler integrable. -/
@[dlmf 16.15.E1]
theorem appellF1_euler_integrable (a b b' c : ℂ) (ha : 0<a.re) (hca : 0<(c-a).re) {x y : ℂ}
    (hxy : (x, y)∈appellEulerDomain) :
    IntegrableOn (appellF1EulerKernel a b b' c x y) (Icc (0:ℝ) 1) := by
  obtain ⟨M1, hM1⟩ := exists_norm_inv_cpow_le_of_isCompact
      (f := fun u : ℝ => 1 - (u:ℂ) * x) isCompact_Icc
    (by fun_prop) (fun u hu => one_sub_mul_mem_slitPlane_of_one_sub_mem hxy.1 hu) b
  obtain ⟨M2, hM2⟩ := exists_norm_inv_cpow_le_of_isCompact
      (f := fun u : ℝ => 1 - (u:ℂ) * y) isCompact_Icc
    (by fun_prop) (fun u hu => one_sub_mul_mem_slitPlane_of_one_sub_mem hxy.2 hu) b'
  have hβ : IntegrableOn (fun u : ℝ => (u:ℂ)^(a-1) * (1 - (u:ℂ))^(c-a-1)) (Icc 0 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc,
      ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    simpa using Complex.betaIntegral_convergent ha hca
  refine (hβ.norm.mul_const (M1 * M2)).mono' ?_ ?_
  · exact (by unfold appellF1EulerKernel; fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have h1 := hM1 u hu
    have h2 := hM2 u hu
    have hM1' := (norm_nonneg _).trans h1
    simp only [appellF1EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub,
        Complex.ofReal_one]
    calc ‖(u:ℂ) ^ (a - 1)‖ * ‖(1 - (u:ℂ)) ^ (c - a - 1)‖ * ‖((1 - (u:ℂ) * x) ^ b)⁻¹‖ *
          ‖((1 - (u:ℂ) * y) ^ b')⁻¹‖
        ≤ ‖(u:ℂ) ^ (a - 1)‖ * ‖(1 - (u:ℂ)) ^ (c - a - 1)‖ * M1 * M2 := by gcongr
      _ = _ := by ring

/-- 16.15.E1: appellF1 euler analytic. -/
@[dlmf 16.15.E1]
theorem appellF1_euler_analytic (a b b' c : ℂ) (ha : 0<a.re) (hca : 0<(c-a).re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appellF1Euler a b b' c p.1 p.2) appellEulerDomain := by
  have hU : IsOpen appellEulerDomain :=
    (isOpen_one_sub_mem_slitPlane.preimage continuous_fst).inter
      (isOpen_one_sub_mem_slitPlane.preimage continuous_snd)
  have hβ : IntegrableOn (fun u : ℝ => (u:ℂ)^(a-1) * (1 - (u:ℂ))^(c-a-1)) (Icc 0 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc,
      ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    simpa using Complex.betaIntegral_convergent ha hca
  have hΙ : Ι (0:ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  have hd : DifferentiableOn ℂ
      (fun p : ℂ × ℂ => ∫ u in (0:ℝ)..1, appellF1EulerKernel a b b' c p.1 p.2 u)
          appellEulerDomain := by
    refine differentiableOn_intervalIntegral_of_locally_dominated hU 0 1
      (fun p _ => (by unfold appellF1EulerKernel; fun_prop : Measurable _).aestronglyMeasurable)
      ?_ ?_
    · rw [hΙ]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hu' : u ∈ Icc (0:ℝ) 1 := Ioc_subset_Icc_self hu
      intro p hp
      have h1 := differentiableAt_inv_one_sub_mul_cpow hu' hp.1 b
      have h2 := differentiableAt_inv_one_sub_mul_cpow hu' hp.2 b'
      have e : (fun q : ℂ × ℂ => appellF1EulerKernel a b b' c q.1 q.2 u) = fun q =>
          (u:ℂ) ^ (a - 1) * ((1 - u:ℝ):ℂ) ^ (c - a - 1) * ((1 - (u:ℂ) * q.1) ^ b)⁻¹ *
            ((1 - (u:ℂ) * q.2) ^ b')⁻¹ := by
        funext q; simp only [appellF1EulerKernel, div_eq_mul_inv]
      rw [e]
      exact (((differentiableAt_const _).mul (h1.comp p differentiableAt_fst)).mul
        (h2.comp p differentiableAt_snd)).differentiableWithinAt
    · intro p hp
      obtain ⟨r1, hr1, hs1⟩ := exists_closedBall_one_sub_mem_slitPlane hp.1
      obtain ⟨r2, hr2, hs2⟩ := exists_closedBall_one_sub_mem_slitPlane hp.2
      obtain ⟨M1, hM1⟩ := exists_norm_inv_one_sub_mul_cpow_le hs1 b
      obtain ⟨M2, hM2⟩ := exists_norm_inv_one_sub_mul_cpow_le hs2 b'
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
        simp only [appellF1EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub,
          Complex.ofReal_one]
        calc ‖(u:ℂ) ^ (a - 1)‖ * ‖(1 - (u:ℂ)) ^ (c - a - 1)‖ * ‖((1 - (u:ℂ) * q.1) ^ b)⁻¹‖ *
              ‖((1 - (u:ℂ) * q.2) ^ b')⁻¹‖
            ≤ ‖(u:ℂ) ^ (a - 1)‖ * ‖(1 - (u:ℂ)) ^ (c - a - 1)‖ * M1 * M2 := by gcongr
          _ = _ := by ring
  have : DifferentiableOn ℂ (fun p : ℂ × ℂ => appellF1Euler a b b' c p.1 p.2) appellEulerDomain :=
    (differentiableOn_const _).mul hd
  exact this.analyticOnNhd_of_finiteDimensional hU

/-- For `u ∈ (0, 1]` and `‖x‖, ‖y‖ < 1`, the product of the binomial series of
`(1 - u x)^{-b}` and `(1 - u y)^{-b'}`, as a double series in `u^{m+n}`. -/
private lemma appellF1_hasSum_binom_prod (b b' : ℂ) {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) :
    HasSum (fun q : ℕ × ℕ => pochhammer b q.1 / q.1 ! * x ^ q.1 *
        (pochhammer b' q.2 / q.2 ! * y ^ q.2) *
      (u:ℂ) ^ (q.1 + q.2)) (((1 - (u:ℂ) * x) ^ b)⁻¹ * ((1 - (u:ℂ) * y) ^ b')⁻¹) := by
  have hu' : u ∈ Icc (0:ℝ) 1 := Ioc_subset_Icc_self hu
  have h1 := hasSum_one_sub_mul_cpow (a := b) hu' hx
  have h2 := hasSum_one_sub_mul_cpow (a := b') hu' hy
  have hs : Summable fun q : ℕ × ℕ => (pochhammer b q.1 / q.1 ! * (x * u) ^ q.1) *
      (pochhammer b' q.2 / q.2 ! * (y * u) ^ q.2) := by
    refine Summable.of_norm ?_
    have hux : ‖x * u‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
      nlinarith [norm_nonneg x, hu.2]
    have huy : ‖y * u‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
      nlinarith [norm_nonneg y, hu.2]
    have := (summable_norm_pochhammer_div_factorial_mul_pow_of_norm_lt_one b hux).mul_of_nonneg
        (summable_norm_pochhammer_div_factorial_mul_pow_of_norm_lt_one b' huy)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    exact this.congr fun q => by simp only [norm_mul]
  have := h1.mul h2 hs
  rw [cpow_neg, cpow_neg, mul_comm x, mul_comm y] at this
  refine this.congr_fun fun q => ?_
  rw [pow_add, mul_pow, mul_pow]
  ring

/-- 16.15.E1: appellF1 euler germ. -/
@[dlmf 16.15.E1]
theorem appellF1_euler_germ (a b b' c : ℂ) (ha : 0<a.re) (hca : 0<(c-a).re) :
    (fun p : ℂ × ℂ => appellF1 a b b' c p.1 p.2)=ᶠ[𝓝 (0, 0)]
        (fun p => appellF1Euler a b b' c p.1 p.2) := by
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
  set d : ℕ × ℕ → ℂ := fun q => pochhammer b q.1 / q.1 ! * x ^ q.1 *
      (pochhammer b' q.2 / q.2 ! * y ^ q.2)
    with hddef
  have hw : Integrable w (volume.restrict (Ioc (0:ℝ) 1)) := by
    have := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (Complex.betaIntegral_convergent ha hca)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp [hwdef]
  have hd : Summable fun q => ‖d q‖ := by
    have := (summable_norm_pochhammer_div_factorial_mul_pow_of_norm_lt_one b hx).mul_of_nonneg
        (summable_norm_pochhammer_div_factorial_mul_pow_of_norm_lt_one b' hy)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    refine this.congr fun q => ?_
    simp only [hddef, norm_mul]
  have key := hasSum_integral_mul_of_norm_le_one (μ := volume.restrict (Ioc (0:ℝ) 1)) hw hd
    (e := fun q u => (u:ℂ) ^ (q.1 + q.2)) (fun q => by fun_prop)
    (fun q => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
      exact pow_le_one₀ hu.1.le hu.2)
    (g := fun u => ((1 - (u:ℂ) * x) ^ b)⁻¹ * ((1 - (u:ℂ) * y) ^ b')⁻¹)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact appellF1_hasSum_binom_prod b b' hx hy hu)
  have hsum := hasSum_appellF1 a b b' c hc (x := x) (y := y) ⟨hx, hy⟩
  refine hsum.unique ?_
  unfold appellF1Euler
  rw [intervalIntegral.integral_of_le zero_le_one]
  have e1 : (∫ u in Ioc (0:ℝ) 1, appellF1EulerKernel a b b' c x y u) =
      ∫ u in Ioc (0:ℝ) 1, w u * (((1 - (u:ℂ) * x) ^ b)⁻¹ * ((1 - (u:ℂ) * y) ^ b')⁻¹) := by
    congr 1; funext u; simp only [appellF1EulerKernel, hwdef, div_eq_mul_inv]; ring
  rw [e1]
  refine (key.mul_left (Gamma c / (Gamma a * Gamma (c - a)))).congr_fun fun q => ?_
  obtain ⟨m, n⟩ := q
  simp only
  have hbeta : (∫ u in Ioc (0:ℝ) 1, w u * (u:ℂ) ^ (m + n)) =
      betaIntegral (a + (m + n : ℕ)) (c - a) := by
    rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    have hu0 : (u:ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.1.ne'
    simp only [hwdef]
    rw [show a + ((m + n : ℕ) : ℂ) - 1 = (a - 1) + ((m + n : ℕ) : ℂ) by ring, cpow_add _ _ hu0,
      cpow_natCast, show c - a - 1 = c - a - 1 by ring]
    push_cast
    ring
  rw [hbeta]
  have hB := Gamma_div_mul_betaIntegral_eq_pochhammer_div_pochhammer ha hca (m + n)
  calc appellF1Coeff a b b' c m n * x ^ m * y ^ n
      = (Gamma c / (Gamma a * Gamma (c - a)) * betaIntegral (a + (m + n : ℕ)) (c - a)) *
          (pochhammer b m / m ! * x ^ m * (pochhammer b' n / n ! * y ^ n)) := by
        rw [hB, appellF1Coeff]
        have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
        have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
        have hpc := pochhammer_ne_zero_of_not_neg_nat hc (m + n)
        field_simp
    _ = _ := by simp only [hddef]; ring

/-- 16.15.E2: appellF2 euler integrable. -/
@[dlmf 16.15.E2]
theorem appellF2_euler_integrable (a b b' c c' : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hcb : b.re<c.re)
    (hcb' : b'.re<c'.re) {x y : ℂ} (hxy : (x, y)∈{p | AppellSquareSlit p}) :
    IntegrableOn (appellF2EulerKernel a b b' c c' x y) (Icc (0:ℝ) 1×ˢIcc (0:ℝ) 1) := by
  obtain ⟨M, hM⟩ := exists_norm_inv_cpow_le_of_isCompact
      (f := fun p : ℝ × ℝ => 1 - (p.1:ℂ) * x - (p.2:ℂ) * y)
    (isCompact_Icc.prod isCompact_Icc) (by fun_prop) (fun p hp => hxy p.1 hp.1 p.2 hp.2) a
  have hcb1 : 0 < (c - b).re := by simp; linarith
  have hcb2 : 0 < (c' - b').re := by simp; linarith
  refine ((integrableOn_norm_betaKernel_mul_norm_betaKernel hb hcb1 hb'
      hcb2).mul_const M).mono' ?_ ?_
  · exact (by unfold appellF2EulerKernel; fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    have h1 := hM p hp
    have hM0 := (norm_nonneg _).trans h1
    simp only [appellF2EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub,
        Complex.ofReal_one]
    calc ‖(p.1:ℂ) ^ (b - 1)‖ * ‖(p.2:ℂ) ^ (b' - 1)‖ * ‖(1 - (p.1:ℂ)) ^ (c - b - 1)‖ *
          ‖(1 - (p.2:ℂ)) ^ (c' - b' - 1)‖ * ‖((1 - (p.1:ℂ) * x - (p.2:ℂ) * y) ^ a)⁻¹‖
        ≤ ‖(p.1:ℂ) ^ (b - 1)‖ * ‖(p.2:ℂ) ^ (b' - 1)‖ * ‖(1 - (p.1:ℂ)) ^ (c - b - 1)‖ *
          ‖(1 - (p.2:ℂ)) ^ (c' - b' - 1)‖ * M := by gcongr
      _ = _ := by ring

/-- 16.15.E2: appellF2 euler analytic. -/
@[dlmf 16.15.E2]
theorem appellF2_euler_analytic (a b b' c c' : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hcb : b.re<c.re)
    (hcb' : b'.re<c'.re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appellF2Euler a b b' c c' p.1 p.2)
        {p | AppellSquareSlit p} := by
  have hU := isOpen_appellSquareSlit
  have hcb1 : 0 < (c - b).re := by simp; linarith
  have hcb2 : 0 < (c' - b').re := by simp; linarith
  have hsq : MeasurableSet (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  have hd : DifferentiableOn ℂ (fun p : ℂ × ℂ =>
      ∫ q in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, appellF2EulerKernel a b b' c c' p.1 p.2 q)
      {p | AppellSquareSlit p} := by
    refine differentiableOn_integral_of_locally_dominated hU
      (fun p _ => (by unfold appellF2EulerKernel; fun_prop : Measurable _).aestronglyMeasurable)
      ?_ ?_
    · filter_upwards [ae_restrict_mem hsq] with q hq
      intro p hp
      have h1 := differentiableAt_inv_one_sub_mul_sub_mul_cpow (p := p) (hp q.1 hq.1 q.2 hq.2) a
      have e : (fun p : ℂ × ℂ => appellF2EulerKernel a b b' c c' p.1 p.2 q) = fun p =>
          (q.1:ℂ) ^ (b - 1) * (q.2:ℂ) ^ (b' - 1) * ((1 - q.1:ℝ):ℂ) ^ (c - b - 1) *
            ((1 - q.2:ℝ):ℂ) ^ (c' - b' - 1) * ((1 - (q.1:ℂ) * p.1 - (q.2:ℂ) * p.2) ^ a)⁻¹ := by
        funext p; simp only [appellF2EulerKernel, div_eq_mul_inv]
      rw [e]
      exact ((differentiableAt_const _).mul h1).differentiableWithinAt
    · intro p hp
      obtain ⟨r, hr, hs⟩ := exists_closedBall_appellSquareSlit hp
      obtain ⟨M, hM⟩ := exists_norm_inv_cpow_le_square
        (f := fun z : (ℂ × ℂ) × (ℝ × ℝ) => 1 - (z.2.1:ℂ) * z.1.1 - (z.2.2:ℂ) * z.1.2)
        (by fun_prop) (fun p hp q hq => hs p hp q.1 hq.1 q.2 hq.2) a
      refine ⟨Metric.ball p r, Metric.ball_mem_nhds _ hr,
        fun q => ‖(q.1:ℂ)^(b-1) * (1 - (q.1:ℂ))^(c-b-1)‖ *
          ‖(q.2:ℂ)^(b'-1) * (1 - (q.2:ℂ))^(c'-b'-1)‖ * M, ?_, ?_⟩
      · exact (integrableOn_norm_betaKernel_mul_norm_betaKernel hb hcb1 hb' hcb2).mul_const M
      · filter_upwards [ae_restrict_mem hsq] with q hq
        intro z hz
        have h1 := hM z (Metric.ball_subset_closedBall hz) q hq
        have hM0 := (norm_nonneg _).trans h1
        simp only [appellF2EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub,
          Complex.ofReal_one]
        calc ‖(q.1:ℂ) ^ (b - 1)‖ * ‖(q.2:ℂ) ^ (b' - 1)‖ * ‖(1 - (q.1:ℂ)) ^ (c - b - 1)‖ *
              ‖(1 - (q.2:ℂ)) ^ (c' - b' - 1)‖ * ‖((1 - (q.1:ℂ) * z.1 - (q.2:ℂ) * z.2) ^ a)⁻¹‖
            ≤ ‖(q.1:ℂ) ^ (b - 1)‖ * ‖(q.2:ℂ) ^ (b' - 1)‖ * ‖(1 - (q.1:ℂ)) ^ (c - b - 1)‖ *
              ‖(1 - (q.2:ℂ)) ^ (c' - b' - 1)‖ * M := by gcongr
          _ = _ := by ring
  have : DifferentiableOn ℂ (fun p : ℂ × ℂ => appellF2Euler a b b' c c' p.1 p.2)
      {p | AppellSquareSlit p} := (differentiableOn_const _).mul hd
  exact this.analyticOnNhd_of_finiteDimensional hU

/-- For `z ∈ [0, 1]²` and `‖x‖ + ‖y‖ < 1`, the double binomial series of
`(1 - z₁ x - z₂ y)^{-a}` in the monomials `z₁^m z₂^n`. -/
private lemma appellF2_hasSum_binom2_mul (a : ℂ) {x y : ℂ} (hp : ‖x‖ + ‖y‖ < 1) {z : ℝ × ℝ}
    (hz : z ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) :
    HasSum (fun q : ℕ × ℕ => pochhammer a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ) * x ^ q.1 * y ^ q.2 *
      ((z.1:ℂ) ^ q.1 * (z.2:ℂ) ^ q.2)) (((1 - (z.1:ℂ) * x - (z.2:ℂ) * y) ^ a)⁻¹) := by
  have hz1 : ‖x * z.1‖ ≤ ‖x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz.1.1]
    nlinarith [norm_nonneg x, hz.1.2]
  have hz2 : ‖y * z.2‖ ≤ ‖y‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz.2.1]
    nlinarith [norm_nonneg y, hz.2.2]
  have h := (hasSum_two_var_binomial a (s := x * z.1) (t := y * z.2) (by linarith)).1
  rw [cpow_neg, mul_comm x, mul_comm y] at h
  refine h.congr_fun fun q => ?_
  rw [mul_pow, mul_pow]
  ring

/-- 16.15.E2: appellF2 euler germ. -/
@[dlmf 16.15.E2]
theorem appellF2_euler_germ (a b b' c c' : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hcb : b.re<c.re)
    (hcb' : b'.re<c'.re) :
    (fun p : ℂ × ℂ => appellF2 a b b' c c' p.1 p.2)=ᶠ[𝓝 (0, 0)]
        (fun p => appellF2Euler a b b' c c' p.1 p.2) := by
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
  set d : ℕ × ℕ → ℂ := fun q => pochhammer a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ) * x ^ q.1 * y ^ q.2
    with hddef
  have hsq : MeasurableSet (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  have hint0 : ∀ {β γ : ℂ}, 0 < β.re → 0 < γ.re →
      IntegrableOn (fun u : ℝ => (u:ℂ) ^ (β - 1) * ((1 - u : ℝ) : ℂ) ^ (γ - 1)) (Icc 0 1) := by
    intro β γ hβ hγ
    refine (integrableOn_betaKernel hβ hγ).congr_fun (fun u _ => ?_) measurableSet_Icc
    push_cast; ring
  have hw : Integrable w (volume.restrict (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    refine ((hint0 hb hcb1).mul_prod (hint0 hb' hcb2)).congr (Eventually.of_forall fun q => ?_)
    simp [hwdef, hf1, hf2]
  have hd : Summable fun q => ‖d q‖ := (hasSum_two_var_binomial a hp).2
  have key := hasSum_integral_mul_of_norm_le_one
      (μ := volume.restrict (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) hw hd
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
      exact appellF2_hasSum_binom2_mul a hp hz)
  have hsum := hasSum_appellF2 a b b' c c' hc hc' (x := x) (y := y) hp
  refine hsum.unique ?_
  unfold appellF2Euler
  have e1 : (∫ z in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, appellF2EulerKernel a b b' c c' x y z) =
      ∫ z in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, w z * ((1 - (z.1:ℂ) * x - (z.2:ℂ) * y) ^ a)⁻¹ := by
    congr 1; funext z; simp only [appellF2EulerKernel, hwdef, hf1, hf2, div_eq_mul_inv]; ring
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
    rw [setIntegral_betaKernel_mul_pow m, setIntegral_betaKernel_mul_pow n]
  rw [hI]
  have hB1 := Gamma_div_mul_betaIntegral_eq_pochhammer_div_pochhammer hb hcb1 m
  have hB2 := Gamma_div_mul_betaIntegral_eq_pochhammer_div_pochhammer hb' hcb2 n
  have hG : Gamma c * Gamma c' / (Gamma b * Gamma b' * Gamma (c - b) * Gamma (c' - b')) *
      (betaIntegral (b + m) (c - b) * betaIntegral (b' + n) (c' - b')) =
      pochhammer b m / pochhammer c m * (pochhammer b' n / pochhammer c' n) := by
    rw [← hB1, ← hB2]; ring
  have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hpc := pochhammer_ne_zero_of_not_neg_nat hc m
  have hpc' := pochhammer_ne_zero_of_not_neg_nat hc' n
  calc appellF2Coeff a b b' c c' m n * x ^ m * y ^ n
      = (pochhammer b m / pochhammer c m * (pochhammer b' n / pochhammer c' n)) *
          (pochhammer a (m + n) / (m ! * n ! : ℂ) * x ^ m * y ^ n) := by
        rw [appellF2Coeff]; field_simp
    _ = _ := by rw [← hG]; simp only [hddef]; ring

/-- `appellTriangle` is measurable. -/
private lemma measurableSet_appellTriangle : MeasurableSet appellTriangle := by
  refine IsClosed.measurableSet ?_
  simp only [appellTriangle, ofPred_and]
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (continuous_fst.add continuous_snd) continuous_const))

/-- Both coordinates of a point of the triangle lie in `[0,1]`. -/
private lemma mem_Icc_of_mem_appellTriangle {p : ℝ × ℝ} (hp : p ∈ appellTriangle) :
    p.1 ∈ Icc (0:ℝ) 1 ∧ p.2 ∈ Icc (0:ℝ) 1 :=
  ⟨⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩, ⟨hp.2.1, by linarith [hp.1, hp.2.2]⟩⟩

/-- 16.15.E3: appellF3 euler integrable. -/
@[dlmf 16.15.E3]
theorem appellF3_euler_integrable (a a' b b' c : ℂ) (hb : 0<b.re) (hb' : 0<b'.re)
    (hrest : 0<(c-b-b').re) {x y : ℂ} (hxy : (x, y)∈appellEulerDomain) :
    IntegrableOn (appellF3EulerKernel a a' b b' c x y) appellTriangle := by
  obtain ⟨M1, hM1⟩ := exists_norm_inv_cpow_le_of_isCompact
      (f := fun u : ℝ => 1 - (u:ℂ) * x) isCompact_Icc
    (by fun_prop) (fun u hu => one_sub_mul_mem_slitPlane_of_one_sub_mem hxy.1 hu) a
  obtain ⟨M2, hM2⟩ := exists_norm_inv_cpow_le_of_isCompact
      (f := fun u : ℝ => 1 - (u:ℂ) * y) isCompact_Icc
    (by fun_prop) (fun u hu => one_sub_mul_mem_slitPlane_of_one_sub_mem hxy.2 hu) a'
  refine ((integrableOn_appellTriangleKernel hb hb' hrest).norm.mul_const (M1 * M2)).mono' ?_ ?_
  · exact (by unfold appellF3EulerKernel; fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_appellTriangle] with p hp
    obtain ⟨hu, hv⟩ := mem_Icc_of_mem_appellTriangle hp
    have h1 := hM1 p.1 hu
    have h2 := hM2 p.2 hv
    have h10 := (norm_nonneg _).trans h1
    have e : appellF3EulerKernel a a' b b' c x y p =
        appellTriangleKernel b b' (c - b - b') p * ((1 - (p.1:ℂ) * x) ^ a)⁻¹ *
          ((1 - (p.2:ℂ) * y) ^ a')⁻¹ := by
      simp only [appellF3EulerKernel, appellTriangleKernel, div_eq_mul_inv]
    rw [e, norm_mul, norm_mul, mul_assoc]
    gcongr

/-- The F3 Euler domain is open. -/
private lemma isOpen_appellEulerDomain : IsOpen appellEulerDomain :=
  (isOpen_slitPlane.preimage (by fun_prop)).inter (isOpen_slitPlane.preimage (by fun_prop))

/-- 16.15.E3: appellF3 euler analytic. -/
@[dlmf 16.15.E3]
theorem appellF3_euler_analytic (a a' b b' c : ℂ) (hb : 0<b.re) (hb' : 0<b'.re)
    (hrest : 0<(c-b-b').re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appellF3Euler a a' b b' c p.1 p.2) appellEulerDomain := by
  have hU := isOpen_appellEulerDomain
  have hT := measurableSet_appellTriangle
  have hd : DifferentiableOn ℂ (fun p : ℂ × ℂ =>
      ∫ q in appellTriangle, appellF3EulerKernel a a' b b' c p.1 p.2 q) appellEulerDomain := by
    refine differentiableOn_integral_of_locally_dominated hU
      (fun p _ => (by unfold appellF3EulerKernel; fun_prop : Measurable _).aestronglyMeasurable)
      ?_ ?_
    · filter_upwards [ae_restrict_mem hT] with q hq
      intro p hp
      obtain ⟨hu, hv⟩ := mem_Icc_of_mem_appellTriangle hq
      have h1 := (differentiableAt_inv_one_sub_mul_cpow hu hp.1 a).comp p differentiableAt_fst
      have h2 := (differentiableAt_inv_one_sub_mul_cpow hv hp.2 a').comp p differentiableAt_snd
      have e : (fun p : ℂ × ℂ => appellF3EulerKernel a a' b b' c p.1 p.2 q) = fun p =>
          appellTriangleKernel b b' (c - b - b') q * ((1 - (q.1:ℂ) * p.1) ^ a)⁻¹ *
            ((1 - (q.2:ℂ) * p.2) ^ a')⁻¹ := by
        funext p
        simp only [appellF3EulerKernel, appellTriangleKernel, div_eq_mul_inv]
      rw [e]
      exact (((differentiableAt_const _).mul h1).mul h2).differentiableWithinAt
    · intro p hp
      obtain ⟨r1, hr1, hs1⟩ := exists_closedBall_one_sub_mem_slitPlane hp.1
      obtain ⟨r2, hr2, hs2⟩ := exists_closedBall_one_sub_mem_slitPlane hp.2
      obtain ⟨M1, hM1⟩ := exists_norm_inv_one_sub_mul_cpow_le hs1 a
      obtain ⟨M2, hM2⟩ := exists_norm_inv_one_sub_mul_cpow_le hs2 a'
      refine ⟨Metric.ball p.1 r1 ×ˢ Metric.ball p.2 r2,
        prod_mem_nhds (Metric.ball_mem_nhds _ hr1) (Metric.ball_mem_nhds _ hr2),
        fun q => ‖appellTriangleKernel b b' (c - b - b') q‖ * (M1 * M2), ?_, ?_⟩
      · exact (integrableOn_appellTriangleKernel hb hb' hrest).norm.mul_const _
      · filter_upwards [ae_restrict_mem hT] with q hq
        intro z hz
        obtain ⟨hu, hv⟩ := mem_Icc_of_mem_appellTriangle hq
        have h1 := hM1 q.1 hu z.1 (Metric.ball_subset_closedBall hz.1)
        have h2 := hM2 q.2 hv z.2 (Metric.ball_subset_closedBall hz.2)
        have h10 := (norm_nonneg _).trans h1
        have e : appellF3EulerKernel a a' b b' c z.1 z.2 q =
            appellTriangleKernel b b' (c - b - b') q * ((1 - (q.1:ℂ) * z.1) ^ a)⁻¹ *
              ((1 - (q.2:ℂ) * z.2) ^ a')⁻¹ := by
          simp only [appellF3EulerKernel, appellTriangleKernel, div_eq_mul_inv]
        rw [e, norm_mul, norm_mul, mul_assoc]
        gcongr
  have : DifferentiableOn ℂ (fun p : ℂ × ℂ => appellF3Euler a a' b b' c p.1 p.2)
      appellEulerDomain := (differentiableOn_const _).mul hd
  exact this.analyticOnNhd_of_finiteDimensional hU

/-- `u^(β-1) uᵐ = u^(β+m-1)` for `u ≥ 0` and `Re β > 0`. -/
private lemma ofReal_cpow_sub_one_mul_pow {u : ℝ} (hu : 0 ≤ u) {β : ℂ} (hβ : 0 < β.re) (m : ℕ) :
    (u:ℂ) ^ (β - 1) * (u:ℂ) ^ m = (u:ℂ) ^ (β + m - 1) := by
  rcases hu.lt_or_eq with hu | rfl
  · have hu0 : (u:ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
    rw [show β + (m:ℂ) - 1 = (β - 1) + (m:ℂ) by ring, cpow_add _ _ hu0, cpow_natCast]
  · rcases m with _ | m
    · simp
    · have hne : β + ((m + 1 : ℕ) : ℂ) - 1 ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      rw [ofReal_zero, zero_pow (Nat.succ_ne_zero m), mul_zero, zero_cpow hne]

/-- 16.15.E3: appellF3 euler germ. -/
@[dlmf 16.15.E3]
theorem appellF3_euler_germ (a a' b b' c : ℂ) (hb : 0<b.re) (hb' : 0<b'.re)
    (hrest : 0<(c-b-b').re) :
    (fun p : ℂ × ℂ => appellF3 a a' b b' c p.1 p.2)=ᶠ[𝓝 (0, 0)]
        (fun p => appellF3Euler a a' b b' c p.1 p.2) := by
  set γ := c - b - b' with hγdef
  have hcre : 0 < c.re := by
    have : c = b + b' + γ := by rw [hγdef]; ring
    rw [this]; simp only [add_re]; linarith
  have hc : AppellRegular c := not_neg_nat_of_re_pos hcre
  have hT := measurableSet_appellTriangle
  have hU : {p : ℂ × ℂ | ‖p.1‖ < 1 ∧ ‖p.2‖ < 1} ∈ 𝓝 ((0:ℂ), (0:ℂ)) :=
    ((isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)).mem_nhds (by simp)
  filter_upwards [hU] with p hp
  obtain ⟨x, y⟩ := p
  obtain ⟨hx, hy⟩ := hp
  simp only at hx hy ⊢
  set w : ℝ × ℝ → ℂ := appellTriangleKernel b b' γ with hwdef
  set d : ℕ × ℕ → ℂ := fun q => pochhammer a q.1 / q.1 ! * x ^ q.1 *
      (pochhammer a' q.2 / q.2 ! * y ^ q.2)
    with hddef
  have hw : Integrable w (volume.restrict appellTriangle) :=
    integrableOn_appellTriangleKernel hb hb' hrest
  have hs1 := summable_norm_pochhammer_div_factorial_mul_pow_of_norm_lt_one a hx
  have hs2 := summable_norm_pochhammer_div_factorial_mul_pow_of_norm_lt_one a' hy
  have hd : Summable fun q => ‖d q‖ := by
    refine (hs1.mul_of_nonneg hs2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
      fun q => ?_
    simp only [hddef, norm_mul]
  have hbd : ∀ q : ℕ × ℕ, ∀ᵐ z ∂(volume.restrict appellTriangle),
      ‖(z.1:ℂ) ^ q.1 * (z.2:ℂ) ^ q.2‖ ≤ 1 := fun q => by
    filter_upwards [ae_restrict_mem hT] with z hz
    obtain ⟨hu, hv⟩ := mem_Icc_of_mem_appellTriangle hz
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hu.1, abs_of_nonneg hv.1]
    calc z.1 ^ q.1 * z.2 ^ q.2 ≤ 1 * 1 :=
          mul_le_mul (pow_le_one₀ hu.1 hu.2) (pow_le_one₀ hv.1 hv.2)
            (pow_nonneg hv.1 _) zero_le_one
      _ = 1 := one_mul 1
  have hg : ∀ᵐ z ∂(volume.restrict appellTriangle), HasSum
      (fun q : ℕ × ℕ => d q * ((z.1:ℂ) ^ q.1 * (z.2:ℂ) ^ q.2))
      (((1 - (z.1:ℂ) * x) ^ a)⁻¹ * ((1 - (z.2:ℂ) * y) ^ a')⁻¹) := by
    filter_upwards [ae_restrict_mem hT] with z hz
    obtain ⟨hu, hv⟩ := mem_Icc_of_mem_appellTriangle hz
    have hn1 : ‖x * z.1‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
      nlinarith [norm_nonneg x, hu.2]
    have hn2 : ‖y * z.2‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv.1]
      nlinarith [norm_nonneg y, hv.2]
    have h1 := hasSum_pochhammer_div_factorial (β := a) hn1
    have h2 := hasSum_pochhammer_div_factorial (β := a') hn2
    have hm := h1.mul h2 (summable_mul_of_summable_norm
      (summable_norm_pochhammer_div_factorial_mul_pow_of_norm_lt_one a hn1)
      (summable_norm_pochhammer_div_factorial_mul_pow_of_norm_lt_one a' hn2))
    rw [cpow_neg, cpow_neg, mul_comm x, mul_comm y] at hm
    refine hm.congr_fun fun q => ?_
    simp only [hddef, mul_pow]
    ring
  have key := hasSum_integral_mul_of_norm_le_one (μ := volume.restrict appellTriangle) hw hd
    (e := fun q z => (z.1:ℂ) ^ q.1 * (z.2:ℂ) ^ q.2) (fun q => by fun_prop) hbd hg
  have hsum := hasSum_appellF3 a a' b b' c hc (x := x) (y := y) ⟨hx, hy⟩
  refine hsum.unique ?_
  unfold appellF3Euler
  have e1 : (∫ z in appellTriangle, appellF3EulerKernel a a' b b' c x y z) =
      ∫ z in appellTriangle, w z * (((1 - (z.1:ℂ) * x) ^ a)⁻¹ * ((1 - (z.2:ℂ) * y) ^ a')⁻¹) := by
    congr 1; funext z; simp only [appellF3EulerKernel, hwdef, appellTriangleKernel, div_eq_mul_inv]
    ring
  rw [e1]
  refine (key.mul_left (Gamma c / (Gamma b * Gamma b' * Gamma γ))).congr_fun fun q => ?_
  obtain ⟨m, n⟩ := q
  simp only
  have hI : (∫ z in appellTriangle, w z * ((z.1:ℂ) ^ m * (z.2:ℂ) ^ n)) =
      Gamma (b + m) * Gamma (b' + n) * Gamma γ / Gamma (b + m + (b' + n) + γ) := by
    rw [← setIntegral_appellTriangleKernel (by simp; linarith) (by simp; linarith) hrest]
    refine setIntegral_congr_fun hT fun z hz => ?_
    obtain ⟨hu, hv⟩ := mem_Icc_of_mem_appellTriangle hz
    simp only [hwdef, appellTriangleKernel]
    rw [← ofReal_cpow_sub_one_mul_pow hu.1 hb m, ← ofReal_cpow_sub_one_mul_pow hv.1 hb' n]
    ring
  rw [hI, show b + m + (b' + n) + γ = c + ((m + n : ℕ) : ℂ) by rw [hγdef]; push_cast; ring,
    Gamma_add_nat_eq_pochhammer_mul_Gamma hb, Gamma_add_nat_eq_pochhammer_mul_Gamma hb',
    Gamma_add_nat_eq_pochhammer_mul_Gamma hcre]
  have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hpc := pochhammer_ne_zero_of_not_neg_nat hc (m + n)
  have hGb := Gamma_ne_zero_of_re_pos hb
  have hGb' := Gamma_ne_zero_of_re_pos hb'
  have hGγ := Gamma_ne_zero_of_re_pos hrest
  have hGc := Gamma_ne_zero_of_re_pos hcre
  simp only [appellF3Coeff, hddef]
  field_simp

/-- 16.15.E4: appellF4 euler integrable. -/
@[dlmf 16.15.E4]
theorem appellF4_euler_integrable (a b c c' : ℂ) (ha : 0<a.re) (hb : 0<b.re) (hca : a.re<c.re)
    (hcb : b.re<c'.re) {x y : ℂ} (hxy : (x, y)∈{p | AppellSquareSlit p}) :
    IntegrableOn (appellF4EulerKernel a b c c' x y) (Icc (0:ℝ) 1×ˢIcc (0:ℝ) 1) := by
  have hK : IsCompact (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := left_mem_Icc.mpr zero_le_one
  obtain ⟨M1, hM1⟩ := exists_norm_inv_cpow_le_of_isCompact (f := fun p : ℝ × ℝ => 1 - (p.1:ℂ) * x)
    hK (by fun_prop) (fun p hp => by simpa using hxy p.1 hp.1 0 h0) (c + c' - a - 1)
  obtain ⟨M2, hM2⟩ := exists_norm_inv_cpow_le_of_isCompact (f := fun p : ℝ × ℝ => 1 - (p.2:ℂ) * y)
    hK (by fun_prop) (fun p hp => by simpa using hxy 0 h0 p.2 hp.2) (c + c' - b - 1)
  obtain ⟨M3, hM3⟩ := exists_norm_inv_cpow_le_of_isCompact
      (f := fun p : ℝ × ℝ => 1 - (p.1:ℂ) * x - (p.2:ℂ) * y)
    hK (by fun_prop) (fun p hp => hxy p.1 hp.1 p.2 hp.2) (a + b - c - c' + 1)
  have hca1 : 0 < (c - a).re := by simp; linarith
  have hcb1 : 0 < (c' - b).re := by simp; linarith
  refine ((integrableOn_norm_betaKernel_mul_norm_betaKernel ha hca1 hb hcb1).mul_const
      (M1 * M2 * M3)).mono' ?_ ?_
  · exact (by unfold appellF4EulerKernel; fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    have h1 := hM1 p hp
    have h2 := hM2 p hp
    have h3 := hM3 p hp
    have hM10 := (norm_nonneg _).trans h1
    have hM20 := (norm_nonneg _).trans h2
    have hM30 := (norm_nonneg _).trans h3
    simp only [appellF4EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub,
        Complex.ofReal_one]
    calc ‖(p.1:ℂ) ^ (a - 1)‖ * ‖(p.2:ℂ) ^ (b - 1)‖ * ‖(1 - (p.1:ℂ)) ^ (c - a - 1)‖ *
          ‖(1 - (p.2:ℂ)) ^ (c' - b - 1)‖ * ‖((1 - (p.1:ℂ) * x) ^ (c + c' - a - 1))⁻¹‖ *
          ‖((1 - (p.2:ℂ) * y) ^ (c + c' - b - 1))⁻¹‖ *
          ‖((1 - (p.1:ℂ) * x - (p.2:ℂ) * y) ^ (a + b - c - c' + 1))⁻¹‖
        ≤ ‖(p.1:ℂ) ^ (a - 1)‖ * ‖(p.2:ℂ) ^ (b - 1)‖ * ‖(1 - (p.1:ℂ)) ^ (c - a - 1)‖ *
          ‖(1 - (p.2:ℂ)) ^ (c' - b - 1)‖ * M1 * M2 * M3 := by gcongr
      _ = _ := by ring

/-- 16.15.E4: appellF4 euler analytic. -/
@[dlmf 16.15.E4]
theorem appellF4_euler_analytic (a b c c' : ℂ) (ha : 0<a.re) (hb : 0<b.re) (hca : a.re<c.re)
    (hcb : b.re<c'.re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appellF4Euler a b c c' p.1 p.2) {p | AppellSquareSlit p} := by
  have hU := isOpen_appellSquareSlit
  have hca1 : 0 < (c - a).re := by simp; linarith
  have hcb1 : 0 < (c' - b).re := by simp; linarith
  have hsq : MeasurableSet (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := left_mem_Icc.mpr zero_le_one
  have hd : DifferentiableOn ℂ (fun p : ℂ × ℂ =>
      ∫ q in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, appellF4EulerKernel a b c c' p.1 p.2 q)
      {p | AppellSquareSlit p} := by
    refine differentiableOn_integral_of_locally_dominated hU
      (fun p _ => (by unfold appellF4EulerKernel; fun_prop : Measurable _).aestronglyMeasurable)
      ?_ ?_
    · filter_upwards [ae_restrict_mem hsq] with q hq
      intro p hp
      have h1 := differentiableAt_inv_one_sub_mul_sub_mul_cpow (p := p) (u := q.1) (v := 0)
        (by simpa using hp q.1 hq.1 0 h0) (c + c' - a - 1)
      have h2 := differentiableAt_inv_one_sub_mul_sub_mul_cpow (p := p) (u := 0) (v := q.2)
        (by simpa using hp 0 h0 q.2 hq.2) (c + c' - b - 1)
      have h3 := differentiableAt_inv_one_sub_mul_sub_mul_cpow (p := p) (hp q.1 hq.1 q.2 hq.2)
        (a + b - c - c' + 1)
      have e : (fun p : ℂ × ℂ => appellF4EulerKernel a b c c' p.1 p.2 q) = fun p =>
          (q.1:ℂ) ^ (a - 1) * (q.2:ℂ) ^ (b - 1) * ((1 - q.1:ℝ):ℂ) ^ (c - a - 1) *
            ((1 - q.2:ℝ):ℂ) ^ (c' - b - 1) *
            ((1 - (q.1:ℂ) * p.1 - ((0:ℝ):ℂ) * p.2) ^ (c + c' - a - 1))⁻¹ *
            ((1 - ((0:ℝ):ℂ) * p.1 - (q.2:ℂ) * p.2) ^ (c + c' - b - 1))⁻¹ *
            ((1 - (q.1:ℂ) * p.1 - (q.2:ℂ) * p.2) ^ (a + b - c - c' + 1))⁻¹ := by
        funext p; simp only [appellF4EulerKernel, div_eq_mul_inv]; simp
      rw [e]
      exact ((((differentiableAt_const _).mul h1).mul h2).mul h3).differentiableWithinAt
    · intro p hp
      obtain ⟨r, hr, hs⟩ := exists_closedBall_appellSquareSlit hp
      obtain ⟨M1, hM1⟩ := exists_norm_inv_cpow_le_square
        (f := fun z : (ℂ × ℂ) × (ℝ × ℝ) => 1 - (z.2.1:ℂ) * z.1.1)
        (by fun_prop) (fun p hp q hq => by simpa using hs p hp q.1 hq.1 0 h0) (c + c' - a - 1)
      obtain ⟨M2, hM2⟩ := exists_norm_inv_cpow_le_square
        (f := fun z : (ℂ × ℂ) × (ℝ × ℝ) => 1 - (z.2.2:ℂ) * z.1.2)
        (by fun_prop) (fun p hp q hq => by simpa using hs p hp 0 h0 q.2 hq.2) (c + c' - b - 1)
      obtain ⟨M3, hM3⟩ := exists_norm_inv_cpow_le_square
        (f := fun z : (ℂ × ℂ) × (ℝ × ℝ) => 1 - (z.2.1:ℂ) * z.1.1 - (z.2.2:ℂ) * z.1.2)
        (by fun_prop) (fun p hp q hq => hs p hp q.1 hq.1 q.2 hq.2) (a + b - c - c' + 1)
      refine ⟨Metric.ball p r, Metric.ball_mem_nhds _ hr,
        fun q => ‖(q.1:ℂ)^(a-1) * (1 - (q.1:ℂ))^(c-a-1)‖ *
          ‖(q.2:ℂ)^(b-1) * (1 - (q.2:ℂ))^(c'-b-1)‖ * (M1 * M2 * M3), ?_, ?_⟩
      · exact (integrableOn_norm_betaKernel_mul_norm_betaKernel ha hca1 hb hcb1).mul_const _
      · filter_upwards [ae_restrict_mem hsq] with q hq
        intro z hz
        have hz' := Metric.ball_subset_closedBall hz
        have h1 := hM1 z hz' q hq
        have h2 := hM2 z hz' q hq
        have h3 := hM3 z hz' q hq
        have hM10 := (norm_nonneg _).trans h1
        have hM20 := (norm_nonneg _).trans h2
        have hM30 := (norm_nonneg _).trans h3
        simp only [appellF4EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub,
          Complex.ofReal_one]
        calc ‖(q.1:ℂ) ^ (a - 1)‖ * ‖(q.2:ℂ) ^ (b - 1)‖ * ‖(1 - (q.1:ℂ)) ^ (c - a - 1)‖ *
              ‖(1 - (q.2:ℂ)) ^ (c' - b - 1)‖ * ‖((1 - (q.1:ℂ) * z.1) ^ (c + c' - a - 1))⁻¹‖ *
              ‖((1 - (q.2:ℂ) * z.2) ^ (c + c' - b - 1))⁻¹‖ *
              ‖((1 - (q.1:ℂ) * z.1 - (q.2:ℂ) * z.2) ^ (a + b - c - c' + 1))⁻¹‖
            ≤ ‖(q.1:ℂ) ^ (a - 1)‖ * ‖(q.2:ℂ) ^ (b - 1)‖ * ‖(1 - (q.1:ℂ)) ^ (c - a - 1)‖ *
              ‖(1 - (q.2:ℂ)) ^ (c' - b - 1)‖ * M1 * M2 * M3 := by gcongr
          _ = _ := by ring
  have : DifferentiableOn ℂ (fun p : ℂ × ℂ => appellF4Euler a b c c' p.1 p.2)
      {p | AppellSquareSlit p} := (differentiableOn_const _).mul hd
  exact this.analyticOnNhd_of_finiteDimensional hU

/-- 16.15.E4: appellF4 euler germ. -/
@[dlmf 16.15.E4]
theorem appellF4_euler_germ (a b c c' : ℂ) (ha : 0<a.re) (hb : 0<b.re) (hca : a.re<c.re)
    (hcb : b.re<c'.re) :
    (fun p : ℂ × ℂ => appellF4 a b c c' (p.1*(1-p.2)) (p.2*(1-p.1)))=ᶠ[𝓝 (0, 0)]
        (fun p => appellF4Euler a b c c' p.1 p.2) := by
  exact F4EulerSeries.euler_germ a b c c' ha hb hca hcb

/-- The Gauss series in the unit disk, as a scalar `HasSum`. -/
private lemma hasSum_gaussHypergeometricCoeff_mul_pow {a b c z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => gaussHypergeometricCoeff a b c n * z ^ n) (₂F₁ a b c z) := by
  have := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).hasSum
    (y := z) (by simpa using mem_eball_one_of_norm_lt_one hz)
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using this

/-- 16.16.E2: appellF2 reduction gauss. -/
@[dlmf 16.16.E2]
theorem appellF2_reduction_gauss (a b b' c : ℂ) (hc : AppellRegular c) (hb' : AppellRegular b') :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appellF2 a b b' c b' x y)=ᶠ[𝓝 (0,0)]
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
  have hsum := hasSum_appellF2 a b b' c b' hc hb' (x := x) (y := y) hp
  have hfib : ∀ m : ℕ, HasSum (fun n => appellF2Coeff a b b' c b' m n * x ^ m * y ^ n)
      (gaussHypergeometricCoeff a b c m * x ^ m * (1 - y) ^ (-(a + m))) := by
    intro m
    have h := (hasSum_pochhammer_div_factorial (β := a + m) hy).mul_left
        (gaussHypergeometricCoeff a b c m * x ^ m)
    refine h.congr_fun fun n => ?_
    have hpb := pochhammer_ne_zero_of_not_neg_nat hb' n
    have hpc := pochhammer_ne_zero_of_not_neg_nat hc m
    have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rw [appellF2Coeff, gaussHypergeometricCoeff, pochhammer_add a m n]
    field_simp
  have hG := hsum.prod_fiberwise hfib
  refine hG.unique ?_
  have h2 := (hasSum_gaussHypergeometricCoeff_mul_pow (a := a) (b := b) (c := c) hz).mul_left
      ((1 - y) ^ (-a))
  refine h2.congr_fun fun m => ?_
  rw [show -(a + (m : ℂ)) = -a + -(m : ℂ) by ring, cpow_add _ _ h1y, cpow_neg (1 - y) (m : ℂ),
    cpow_natCast, div_pow]
  field_simp

/-- Summing each row of the F3 double series gives a Gauss hypergeometric series. -/
lemma hasSum_appellF3_gauss_fibers (a a' b b' c : ℂ) (hc : AppellRegular c)
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum (fun m : ℕ => pochhammer a m * pochhammer b m / (pochhammer c m * m !) * x ^ m *
      ₂F₁ a' b' (c + m) y) (appellF3 a a' b b' c x y) := by
  have hs := hasSum_appellF3 a a' b b' c hc (x := x) (y := y) ⟨hx, hy⟩
  apply hs.prod_fiberwise
  intro m
  have h := (hasSum_gaussHypergeometricCoeff_mul_pow (a := a') (b := b') (c := c + m) hy).mul_left
    (pochhammer a m * pochhammer b m / (pochhammer c m * m !) * x ^ m)
  refine h.congr_fun fun n => ?_
  rw [appellF3Coeff, gaussHypergeometricCoeff, pochhammer_add]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Summing each row of the F1 double series gives a Gauss hypergeometric series. -/
lemma hasSum_appellF1_gauss_fibers (a b b' c : ℂ) (hc : AppellRegular c)
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum (fun m : ℕ => pochhammer a m * pochhammer b m / (pochhammer c m * m !) * x ^ m *
      ₂F₁ (a + m) b' (c + m) y) (appellF1 a b b' c x y) := by
  have hs := hasSum_appellF1 a b b' c hc (x := x) (y := y) ⟨hx, hy⟩
  apply hs.prod_fiberwise
  intro m
  have h := (hasSum_gaussHypergeometricCoeff_mul_pow (a := a + m) (b := b')
      (c := c + m) hy).mul_left
    (pochhammer a m * pochhammer b m / (pochhammer c m * m !) * x ^ m)
  refine h.congr_fun fun n => ?_
  rw [appellF1Coeff, gaussHypergeometricCoeff, pochhammer_add a, pochhammer_add c]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Complementary first upper parameters reduce Appell F3 to F1 after a fractional
linear change of its second variable, as germs at the origin (DLMF 16.16.E4). -/
@[dlmf 16.16.E4]
theorem appellF3_reduction_appellF1 (a b b' c : ℂ) (hc : AppellRegular c) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appellF3 a (c-a) b b' c x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-y)^(-b')*appellF1 a b b' c x (y/(y-1))) := by
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
  have hs := hasSum_appellF3_gauss_fibers a (c - a) b b' c hc hp.1 hy
  have hs' := (hasSum_appellF1_gauss_fibers a b b' c hc hp.1 hyt).mul_left ((1 - y)^ (-b'))
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

/-- Exchanging the two separate upper parameters exchanges the F1 variables. -/
lemma appellF1_swap (a b b' c x y : ℂ) :
    appellF1 a b b' c x y = appellF1 a b' b c y x := by
  rw [appellF1, appellF1, ← (Equiv.prodComm ℕ ℕ).tsum_eq]
  apply tsum_congr
  rintro ⟨m, n⟩
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  rw [appellF1Coeff_swap a b b' c n m]
  ring


/-- 16.16.E5_5: appellF4 reduction appellF1. -/
@[dlmf 16.16.E5_5]
theorem appellF4_reduction_appellF1 (a b c : ℂ) (hc : AppellRegular c) (hb : AppellRegular b) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appellF4 a b c b (x*(1-y)) (y*(1-x)))=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2;
          (1-x)^(-a)*(1-y)^(-a)*appellF1 a (c-b) (a-c+1) c (x/(x-1)) (x*y/((1-x)*(1-y)))) := by
  obtain ⟨δ, hδ, hBC⟩ := BurchnallChaundy.hasSum_expansion a b c b hc hb
  have hδ' : 0 < min δ (1 / 8) := lt_min hδ (by norm_num)
  have hU : {p : ℂ × ℂ | ‖p.1‖ < min δ (1 / 8) ∧ ‖p.2‖ < min δ (1 / 8)} ∈
      𝓝 ((0 : ℂ),(0 : ℂ)) :=
    ((isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)).mem_nhds
      (by simpa using And.intro hδ' hδ')
  filter_upwards [hU] with p hp
  obtain ⟨x, y⟩ := p
  simp only at hp ⊢
  have hx : ‖x‖ < 1 / 8 := hp.1.trans_le (min_le_right _ _)
  have hy : ‖y‖ < 1 / 8 := hp.2.trans_le (min_le_right _ _)
  have hx1 : 1 - x ≠ 0 := by
    intro h
    have he : x = 1 := by linear_combination -h
    rw [he, norm_one] at hx
    norm_num at hx
  have hy1 : 1 - y ≠ 0 := by
    intro h
    have he : y = 1 := by linear_combination -h
    rw [he, norm_one] at hy
    norm_num at hy
  have hxden : 1 - ‖x‖ ≤ ‖1 - x‖ := by simpa using norm_sub_norm_le (1 : ℂ) x
  have hyden : 1 - ‖y‖ ≤ ‖1 - y‖ := by simpa using norm_sub_norm_le (1 : ℂ) y
  have hxden0 : 0 < ‖1 - x‖ := norm_pos_iff.mpr hx1
  have hyden0 : 0 < ‖1 - y‖ := norm_pos_iff.mpr hy1
  have htx : ‖x / (x - 1)‖ < 1 := by
    rw [norm_div, norm_sub_rev x 1, div_lt_one hxden0]
    linarith
  have huxy : ‖x * y / ((1 - x) * (1 - y))‖ < 1 := by
    rw [norm_div, norm_mul, norm_mul, div_lt_one (mul_pos hxden0 hyden0)]
    have hprod : (1 - ‖x‖) * (1 - ‖y‖) ≤ ‖1 - x‖ * ‖1 - y‖ :=
      mul_le_mul hxden hyden (by linarith) (by positivity)
    nlinarith [norm_nonneg x, norm_nonneg y]
  have hF1 := (hasSum_appellF1_gauss_fibers a (a - c + 1) (c - b) c hc huxy htx).mul_left
    ((1 - x) ^ (-a) * (1 - y) ^ (-a))
  rw [appellF1_swap a (a - c + 1) (c - b) c] at hF1
  apply (hBC x y (hp.1.trans_le (min_le_left _ _))
    (hp.2.trans_le (min_le_left _ _))).unique
  refine hF1.congr_fun fun k => ?_
  have hck : ∀ j : ℕ, c + k ≠ -(j : ℂ) := by
    intro j h
    apply hc (k + j)
    push_cast
    linear_combination h
  have hbk : ∀ j : ℕ, (j : ℂ) ≠ -(b + k) := by
    intro j h
    apply hb (k + j)
    push_cast
    linear_combination h
  rw [ordinaryHypergeometric_eq_one_sub_neg_cpow hbk (by linarith),
    pfaff_transformation_of_ne_neg_nat hck (by linarith) htx,
    show c + k - (b + k) = c - b by ring]
  rw [show -(a + (k : ℂ)) = -a + -(k : ℂ) by ring,
    cpow_add _ _ hx1, cpow_add _ _ hy1,
    cpow_neg (1 - x) (k : ℂ), cpow_neg (1 - y) (k : ℂ), cpow_natCast, cpow_natCast,
    div_pow, mul_pow, mul_pow]
  have hbp := pochhammer_ne_zero_of_not_neg_nat hb k
  have hcp := pochhammer_ne_zero_of_not_neg_nat hc k
  have hfac : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  rw [show a + b - c - b + 1 = a - c + 1 by ring]
  field_simp [hbp, hcp, hfac, hx1, hy1]

/-- Under `c + c' = a + b + 1`, summing `appellF4Family` over its first two indices gives the
product of the `(M, N)` terms of `₂F₁(a,b;c;X)` and `₂F₁(a,b;c';Y)`. -/
private lemma hasSum_appellF4Family_snd {a b c c' : ℂ} (hcc : c + c' = a + b + 1)
    (hpc : ∀ k, pochhammer c k ≠ 0) (hpc' : ∀ k, pochhammer c' k ≠ 0) (X Y : ℂ) (q : ℕ × ℕ) :
    HasSum (fun p => appellF4Family a b c c' X Y (p, q))
      (gaussHypergeometricCoeff a b c q.1 * X ^ q.1 *
          (gaussHypergeometricCoeff a b c' q.2 * Y ^ q.2)) := by
  obtain ⟨M, N⟩ := q
  have hfin := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _)
    (s := Finset.range (M + 1) ×ˢ Finset.range (N + 1))
    (f := fun p => appellF4Family a b c c' X Y (p, (M, N))) (fun p hp => by
      obtain ⟨m, n⟩ := p
      simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hp
      unfold appellF4Family appellF4BinomialCoeff
      simp only
      rcases hp with h | h
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; simp
      · rw [ite_eq_right_of_eq_false (c := n ≤ N) _ _ (eq_false (by omega))]; simp)
  convert hfin using 1
  rw [Finset.sum_product]
  simp only
  rw [show gaussHypergeometricCoeff a b c M * X ^ M * (gaussHypergeometricCoeff a b c' N * Y ^ N) =
    (gaussHypergeometricCoeff a b c M * gaussHypergeometricCoeff a b c' N) *
        (X ^ M * Y ^ N) by ring,
    ← appellF4_coeff hcc hpc hpc' M N, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hmM : m ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  unfold appellF4Family appellF4Term appellF4BinomialCoeff
  simp only
  rw [ite_eq_left_of_eq_true _ _ (eq_true hmM), ite_eq_left_of_eq_true _ _ (eq_true hnN)]
  ring

/-- Bailey's product formula at all regular lower parameters (stronger than `appellF4_bailey`,
which assumes positive real parts). The proof is that of `appellF4_bailey` in
`DLMF.Hypergeometric.AppellF4`, with its coefficient bound replaced by
`exists_norm_appellF4Coeff_le_geom`. -/
private lemma appellF4_bailey_of_appellRegular {a b c c' : ℂ} (hcc : c + c' = a + b + 1)
    (hc : AppellRegular c)
    (hc' : AppellRegular c') : ∃ δ > 0, ∀ X Y : ℂ, ‖X‖ < δ → ‖Y‖ < δ →
      HasSum (fun p : ℕ × ℕ => appellF4Coeff a b c c' p.1 p.2 * (X * (1 - Y)) ^ p.1 *
        (Y * (1 - X)) ^ p.2) (₂F₁ a b c X * ₂F₁ a b c' Y) := by
  refine ⟨1 / 1024, by norm_num, fun X Y hX hY => ?_⟩
  have hpc : ∀ k, pochhammer c k ≠ 0 := pochhammer_ne_zero_of_not_neg_nat hc
  have hpc' : ∀ k, pochhammer c' k ≠ 0 := pochhammer_ne_zero_of_not_neg_nat hc'
  have hS := (summable_appellF4Family a b c c' hc hc' hX hY).hasSum
  have hfib1 := hasSum_appellF4Family_fst a b c c' X Y
  have hF4 := hS.prod_fiberwise hfib1
  have hfib2 := hasSum_appellF4Family_snd hcc hpc hpc' X Y
  have hS' : HasSum (fun x : (ℕ × ℕ) × (ℕ × ℕ) => appellF4Family a b c c' X Y (x.2, x.1))
      (∑' p, appellF4Family a b c c' X Y p) :=
    ((Equiv.prodComm (ℕ × ℕ) (ℕ × ℕ)).hasSum_iff (f := appellF4Family a b c c' X Y)).mpr hS
  have hG := hS'.prod_fiberwise hfib2
  have hXs := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one (show ‖X‖ < 1 by linarith))
  have hYs := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c').hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one (show ‖Y‖ < 1 by linarith))
  have hprod := hXs.mul hYs hG.summable
  rw [hG.unique hprod] at hF4
  exact hF4

/-- 16.16.E6: appellF4 product germ. -/
@[dlmf 16.16.E6]
theorem appellF4_product_germ (a b c : ℂ) (hc : AppellRegular c) (hc' : AppellRegular (a+b-c+1)) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2;
        appellF4 a b c (a+b-c+1) (x*(1-y)) (y*(1-x)))=ᶠ[𝓝 (0, 0)]
      (fun p => let x:=p.1; let y:=p.2; ₂F₁ a b c x*₂F₁ a b (a+b-c+1) y) := by
  obtain ⟨δ, hδ, h⟩ :=
      appellF4_bailey_of_appellRegular (a := a) (b := b) (c := c) (c' := a + b - c + 1)
    (by ring) hc hc'
  have hU : {p : ℂ × ℂ | ‖p.1‖ < δ ∧ ‖p.2‖ < δ} ∈ 𝓝 ((0:ℂ), (0:ℂ)) :=
    ((isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)).mem_nhds
      (by simp [hδ])
  filter_upwards [hU] with p hp
  exact (h p.1 p.2 hp.1 hp.2).tsum_eq

/-- Exchanging the two pairs of upper parameters exchanges the F3 variables. -/
lemma appellF3_swap (a a' b b' c x y : ℂ) :
    appellF3 a a' b b' c x y = appellF3 a' a b' b c y x := by
  rw [appellF3, appellF3, ← (Equiv.prodComm ℕ ℕ).tsum_eq]
  apply tsum_congr
  rintro ⟨m, n⟩
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  rw [appellF3Coeff_swap a a' b b' c n m]
  ring


/-- Pfaff's simultaneous fractional linear change of both Appell F1 variables,
as analytic germs at the origin (DLMF 16.16.E8). -/
@[dlmf 16.16.E8]
theorem appellF1_pfaff_first (a b b' c : ℂ) (hc : AppellRegular c) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appellF1 a b b' c x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2;
          (1-x)^(-b)*(1-y)^(-b')*appellF1 (c-a) b b' c (x/(x-1)) (y/(y-1))) := by
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
  have h1 := (appellF3_reduction_appellF1 a b b' c hc).comp_tendsto hC1
  have h2 := (appellF3_reduction_appellF1 (c - a) b' b c hc).comp_tendsto hC2
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
  change appellF3 a (c - a) b b' c x (T y) = (1 - T y)^ (-b') * appellF1 a b b' c x (T (T y)) at h1
  rw [hinv, hTT, inv_cpow _ _ harg] at h1
  rw [show c - (c - a) = a by ring, ← appellF3_swap a (c - a) b b' c x (T y),
    appellF1_swap (c - a) b' b c (T y) (T x)] at h2
  rw [h2] at h1
  have hne : (1 - y)^ (-b') ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hy1)
  have hh := congrArg (fun v : ℂ => (1 - y)^ (-b') * v) h1
  rw [mul_inv_cancel_left₀ hne] at hh
  calc appellF1 a b b' c x y = _ := hh.symm
       _ = _ := by dsimp only [T]; ring

/-- Summing each column of the F2 double series gives a Gauss hypergeometric series. -/
lemma hasSum_appellF2_gauss_fibers (a b b' c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c')
    {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    HasSum (fun n : ℕ => pochhammer a n * pochhammer b' n / (pochhammer c' n * n !) * y ^ n *
      ₂F₁ (a + n) b c x) (appellF2 a b b' c c' x y) := by
  have hs := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr (hasSum_appellF2 a b b' c c' hc hc' hxy)
  apply hs.prod_fiberwise
  intro n
  have hx : ‖x‖ < 1 := by linarith [norm_nonneg y]
  have h := (hasSum_gaussHypergeometricCoeff_mul_pow (a := a + n) (b := b) (c := c) hx).mul_left
    (pochhammer a n * pochhammer b' n / (pochhammer c' n * n !) * y ^ n)
  refine h.congr_fun fun m => ?_
  change appellF2Coeff a b b' c c' m n * x ^ m * y ^ n = _
  rw [appellF2Coeff, gaussHypergeometricCoeff, show m + n = n + m by omega, pochhammer_add]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Pfaff's transformation in the first F2 variable rescales the second variable,
as analytic germs at the origin (DLMF 16.16.E9). -/
@[dlmf 16.16.E9]
theorem appellF2_pfaff (a b b' c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appellF2 a b b' c c' x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2;
          (1-x)^(-a)*appellF2 a (c-b) b' c c' (x/(x-1)) (y/(1-x))) := by
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
  have hs := hasSum_appellF2_gauss_fibers a b b' c c' hc hc' (x := x) (y := y) (by linarith)
  have hs' := (hasSum_appellF2_gauss_fibers a (c - b) b' c c' hc hc' ht).mul_left ((1 - x)^ (-a))
  apply hs.unique
  refine hs'.congr_fun fun n => ?_
  rw [pfaff_transformation_of_ne_neg_nat hc hx hxt]
  rw [show -(a+(n : ℂ)) = -a + -(n : ℂ) by ring, cpow_add _ _ h1x,
    cpow_neg (1 - x) (n : ℂ), cpow_natCast, div_pow]
  ring

/-- 16.16.E7: appellF4 burchnall chaundy. -/
@[dlmf 16.16.E7]
theorem appellF4_burchnall_chaundy (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') :
    ∃ δ>0,∀ x y : ℂ,‖x‖<δ→‖y‖<δ→
      HasSum (fun k : ℕ => pochhammer a k*pochhammer b k*pochhammer (a+b-c-c'+1) k/
        (pochhammer c k*pochhammer c' k*k !)*x^k*y^k*₂F₁ (a+k) (b+k) (c+k) x*
          ₂F₁ (a+k) (b+k) (c'+k) y) (appellF4 a b c c' (x*(1-y)) (y*(1-x))) := by
  exact BurchnallChaundy.hasSum_expansion a b c c' hc hc'

/-- The large-variable formula is a branch reached by analytic continuation, not a divergent-series
identity. -/
@[dlmf 16.16.E10]
theorem appellF4_infinity_connection (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c')
    (hab : ∀ k : ℤ,a-b≠k) {x y : ℂ}
    (hconv : (x/y,1/y)∈appellF4Domain) (hy : -y∈slitPlane) :
    IsAppellBranchAt (fun p : ℂ × ℂ => appellF4 a b c c' p.1 p.2) (x,y)
      (fun p => Gamma c'*Gamma (b-a)/(Gamma (c'-a)*Gamma b)*(-p.2)^(-a)*
        appellF4 a (a-c'+1) c (a-b+1) (p.1/p.2) (1/p.2)+
        Gamma c'*Gamma (a-b)/(Gamma (c'-b)*Gamma a)*(-p.2)^(-b)*
        appellF4 b (b-c'+1) c (b-a+1) (p.1/p.2) (1/p.2)) := by
  sorry

/-- Coalescing exponent parameters require the combined connection expression limit. -/
@[dlmf 16.16.E10]
theorem appellF4_infinity_resonance_limits {a b c c' : ℂ} (hc : AppellRegular c)
    (hc' : AppellRegular c')
    (k : ℤ) (hab : a-b=k) {x y : ℂ} (hconv : (x/y,1/y)∈appellF4Domain) (hy : -y∈slitPlane) :
    ∃ L : ℂ,Tendsto (fun a' : ℂ =>
      Gamma c'*Gamma (b-a')/(Gamma (c'-a')*Gamma b)*(-y)^(-a')*
        appellF4 a' (a'-c'+1) c (a'-b+1) (x/y) (1/y)+
      Gamma c'*Gamma (a'-b)/(Gamma (c'-b)*Gamma a')*(-y)^(-b)*
        appellF4 b (b-c'+1) c (b-a'+1) (x/y) (1/y)) (𝓝[≠] a) (𝓝 L) := by
  sorry

end DLMF.Hypergeometric

end
