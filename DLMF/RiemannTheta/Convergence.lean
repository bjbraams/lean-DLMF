/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.RiemannTheta.Basic.Definitions
public import DLMF.Elliptic.Basic.Theta
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Complex.Liouville

/-!
# Convergence and analytic properties of the Riemann theta series
-/

@[expose] public noncomputable section

open Complex Matrix Finset Filter Topology
open scoped Real

variable {ι : Type*} [Fintype ι]

namespace DLMF.RiemannTheta

/-! ## Riemann matrices and the theta series -/

/-! ## The modulus of a term -/

/-- Identity under the stated parameter and domain assumptions: `((fun i => (x i : ℂ)) ⬝ᵥ z).im =
x ⬝ᵥ fun i => (z i).im`. -/
lemma rth21_im_dotProduct_ofReal (x : ι → ℝ) (z : ι → ℂ) :
    ((fun i => (x i : ℂ)) ⬝ᵥ z).im = x ⬝ᵥ fun i => (z i).im := by
  simp [dotProduct, Complex.im_sum]

/-- Identity under the stated parameter and domain assumptions: `((fun i => (x i : ℂ)) ⬝ᵥ (Ω *ᵥ
fun i => (x i : ℂ))).im = x ⬝ᵥ (Ω.map Complex.im *ᵥ x)`. -/
theorem rth21_im_quad_ofReal (x : ι → ℝ) (Ω : Matrix ι ι ℂ) :
    ((fun i => (x i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (x i : ℂ))).im =
      x ⬝ᵥ (Ω.map Complex.im *ᵥ x) := by
  simp [dotProduct, mulVec, Complex.im_sum, Finset.mul_sum]

omit [Fintype ι] in
/-- Identity under the stated parameter and domain assumptions: `(fun i => (n i : ℂ)) = fun i =>
(((n i : ℝ)) : ℂ)`. -/
lemma rth21_intVec (n : ι → ℤ) : (fun i => (n i : ℂ)) = fun i => (((n i : ℝ)) : ℂ) := by
  simp

/-- `‖exp(2πi(½ n·Ω·n + n·z))‖ = exp(-π n·(Im Ω)·n - 2π n·Im z)`. -/
theorem norm_riemannThetaTerm (z : ι → ℂ) (Ω : Matrix ι ι ℂ) (n : ι → ℤ) :
    ‖riemannThetaTerm z Ω n‖ = Real.exp (-π * ((fun i => (n i : ℝ)) ⬝ᵥ
      (Ω.map Complex.im *ᵥ fun i => (n i : ℝ))) -
        2 * π * ((fun i => (n i : ℝ)) ⬝ᵥ fun i => (z i).im)) := by
  rw [riemannThetaTerm, Complex.norm_exp, rth21_intVec]
  rw [← rth21_im_quad_ofReal, ← rth21_im_dotProduct_ofReal]
  generalize ((fun i => ((n i : ℝ) : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => ((n i : ℝ) : ℂ))) = q
  generalize ((fun i => ((n i : ℝ) : ℂ)) ⬝ᵥ z) = d
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-! ## Convergence (DLMF §21.2(i)) -/

/-- Membership in Siegel upper half-space implies the positive-definiteness condition used to
control the theta summands. -/
theorem rth21_posIm_of_mem {Ω : Matrix ι ι ℂ} (h : Ω ∈ siegelUpperHalfSpace ι) :
    rth21_PosIm Ω := fun x hx => by
  simpa using h.2.dotProduct_mulVec_pos hx

/-- Estimate under the stated parameter and domain assumptions: `∃ c > 0, ∀ x : ι → ℝ, c * ∑ i, x
i ^ 2 ≤ x ⬝ᵥ (Y *ᵥ x)`. -/
lemma rth21_exists_lower {Y : Matrix ι ι ℝ} (hY : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (Y *ᵥ x)) :
    ∃ c > 0, ∀ x : ι → ℝ, c * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (Y *ᵥ x) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun x => by simp [dotProduct, Finset.univ_eq_empty]⟩
  have hK : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty :=
    ⟨fun _ => 1, by simp [mem_sphere_iff_norm, pi_norm_const]⟩
  have hcont : Continuous fun x : ι → ℝ => x ⬝ᵥ (Y *ᵥ x) := by
    simp only [dotProduct, mulVec]
    fun_prop
  obtain ⟨u, hu, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hm : 0 < u ⬝ᵥ (Y *ᵥ u) := hY u hu0
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine ⟨u ⬝ᵥ (Y *ᵥ u) / Fintype.card ι, by positivity, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hv : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    simp [norm_smul, hxn.ne']
  have h1 : u ⬝ᵥ (Y *ᵥ u) ≤ (‖x‖⁻¹ • x) ⬝ᵥ (Y *ᵥ (‖x‖⁻¹ • x)) := hmin hv
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h1
  have h4 : u ⬝ᵥ (Y *ᵥ u) * ‖x‖ ^ 2 ≤ x ⬝ᵥ (Y *ᵥ x) := by
    calc u ⬝ᵥ (Y *ᵥ u) * ‖x‖ ^ 2 ≤ (‖x‖⁻¹ * (‖x‖⁻¹ * x ⬝ᵥ (Y *ᵥ x))) * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = x ⬝ᵥ (Y *ᵥ x) := by field_simp
  have h3 : ∑ i, x i ^ 2 ≤ Fintype.card ι * ‖x‖ ^ 2 := by
    calc ∑ i, x i ^ 2 ≤ ∑ _i : ι, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
          have h := norm_le_pi_norm x i
          rw [Real.norm_eq_abs] at h
          nlinarith [abs_nonneg (x i), sq_abs (x i)]
      _ = _ := by simp
  calc u ⬝ᵥ (Y *ᵥ u) / Fintype.card ι * ∑ i, x i ^ 2
      ≤ u ⬝ᵥ (Y *ᵥ u) / Fintype.card ι * (Fintype.card ι * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = u ⬝ᵥ (Y *ᵥ u) * ‖x‖ ^ 2 := by field_simp
    _ ≤ _ := h4

/-- Estimate under the stated parameter and domain assumptions: `x ⬝ᵥ (Y *ᵥ x) - δ * Fintype.card
ι * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (Y' *ᵥ x)`. -/
lemma rth21_quad_perturb {Y Y' : Matrix ι ι ℝ} {δ : ℝ} (hδ : ∀ i j, |Y' i j - Y i j| ≤ δ)
    (x : ι → ℝ) :
    x ⬝ᵥ (Y *ᵥ x) - δ * Fintype.card ι * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (Y' *ᵥ x) := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i0⟩⟩
  · simp [dotProduct, Finset.univ_eq_empty]
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ i0 i0)
  have hsplit : x ⬝ᵥ (Y' *ᵥ x) = x ⬝ᵥ (Y *ᵥ x) + x ⬝ᵥ ((Y' - Y) *ᵥ x) := by
    rw [sub_mulVec, dotProduct_sub]
    ring
  have habs : |x ⬝ᵥ ((Y' - Y) *ᵥ x)| ≤ δ * (∑ i, |x i|) ^ 2 := by
    simp only [dotProduct, mulVec, Matrix.sub_apply]
    calc |∑ i, x i * ∑ j, (Y' i j - Y i j) * x j|
        ≤ ∑ i, |x i * ∑ j, (Y' i j - Y i j) * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |x i| * ∑ j, δ * |x j| := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hδ i j) (abs_nonneg _)
      _ = δ * (∑ i, |x i|) ^ 2 := by
          simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
          ring
  have hcs : (∑ i, |x i|) ^ 2 ≤ Fintype.card ι * ∑ i, x i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |x i|)
    simpa [sq_abs] using this
  have := neg_abs_le (x ⬝ᵥ ((Y' - Y) *ᵥ x))
  nlinarith [mul_le_mul_of_nonneg_left hcs hδ0]

/-- The term bound `‖θ-term‖ ≤ ∏ᵢ exp(-π(T nᵢ² - 2S|nᵢ|))`. -/
lemma rth21_norm_term_le {z : ι → ℂ} {Ω : Matrix ι ι ℂ} {T S : ℝ}
    (hY : ∀ x : ι → ℝ, T * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (Ω.map Complex.im *ᵥ x))
    (hS : ∀ i, |(z i).im| ≤ S) (n : ι → ℤ) :
    ‖riemannThetaTerm z Ω n‖ ≤ ∏ i, Real.exp (-π * (T * (n i : ℝ) ^ 2 - 2 * S * |(n i : ℝ)|)) := by
  rw [norm_riemannThetaTerm, ← Real.exp_sum, Real.exp_le_exp]
  have h1 := hY (fun i => (n i : ℝ))
  have h2 : -((fun i => (n i : ℝ)) ⬝ᵥ fun i => (z i).im) ≤ S * ∑ i, |(n i : ℝ)| := by
    rw [dotProduct, ← Finset.sum_neg_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc -((n i : ℝ) * (z i).im) ≤ |(n i : ℝ)| * |(z i).im| := by
          rw [← abs_mul]; exact neg_le_abs _
      _ ≤ |(n i : ℝ)| * S := mul_le_mul_of_nonneg_left (hS i) (abs_nonneg _)
      _ = _ := mul_comm _ _
  have h3 : ∑ i, -π * (T * (n i : ℝ) ^ 2 - 2 * S * |(n i : ℝ)|) =
      -π * (T * ∑ i, (n i : ℝ) ^ 2) + 2 * π * (S * ∑ i, |(n i : ℝ)|) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h3]
  nlinarith [mul_le_mul_of_nonneg_left h1 Real.pi_pos.le,
    mul_le_mul_of_nonneg_left h2 Real.pi_pos.le]

/-- Summability of the indicated series: `Summable fun n : ι → ℤ => ∏ i, f (n i)`. -/
lemma rth21_summable_prod {f : ℤ → ℝ} (hf0 : ∀ k, 0 ≤ f k) (hf : Summable f) :
    Summable fun n : ι → ℤ => ∏ i, f (n i) := by
  classical
  refine summable_of_sum_le (c := ∏ _i : ι, ∑' k, f k)
    (fun n => Finset.prod_nonneg fun i _ => hf0 _) fun s => ?_
  calc ∑ n ∈ s, ∏ i, f (n i)
      ≤ ∑ n ∈ Fintype.piFinset (fun i => s.image (fun n : ι → ℤ => n i)), ∏ i, f (n i) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn => Fintype.mem_piFinset.mpr fun i => Finset.mem_image_of_mem _ hn)
          (fun n _ _ => Finset.prod_nonneg fun i _ => hf0 _)
    _ = ∏ i, ∑ k ∈ s.image (fun n : ι → ℤ => n i), f k := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ _i : ι, ∑' k, f k :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun k _ => hf0 k)
          (fun i _ => hf.sum_le_tsum _ (fun k _ => hf0 k))

/-- Estimate under the stated parameter and domain assumptions: `∀ᶠ x in 𝓝 x0, |f x - f x0| < ε`. -/
lemma rth21_eventually_abs_lt {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f)
    (x0 : X) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ x in 𝓝 x0, |f x - f x0| < ε := by
  have := (hf.tendsto x0).eventually (Metric.ball_mem_nhds (f x0) hε)
  filter_upwards [this] with x hx
  simpa [Metric.mem_ball, Real.dist_eq] using hx

/-- Local summable majorant: near a point `(z₀, Ω₀)` with `Im Ω₀` positive definite there is a
summable bound for the theta terms, uniform on a neighbourhood. -/
lemma rth21_local_majorant {z0 : ι → ℂ} {Ω0 : Matrix ι ι ℂ} (h0 : rth21_PosIm Ω0) :
    ∃ t ∈ 𝓝 (z0, Ω0), ∃ u : (ι → ℤ) → ℝ, Summable u ∧
      ∀ p ∈ t, ∀ n, ‖riemannThetaTerm p.1 p.2 n‖ ≤ u n := by
  obtain ⟨c, hc, hlow⟩ := rth21_exists_lower h0
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = c / (2 * (Fintype.card ι + 1)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδc : δ * Fintype.card ι ≤ c / 2 := by
    rw [hδdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hc]
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = 1 + ∑ i, |(z0 i).im| := ⟨_, rfl⟩
  have ht : {p : (ι → ℂ) × Matrix ι ι ℂ | (∀ i, |(p.1 i).im - (z0 i).im| < 1) ∧
      ∀ i j, |(p.2 i j).im - (Ω0 i j).im| < δ} ∈ 𝓝 (z0, Ω0) := by
    have hA : ∀ᶠ p in 𝓝 (z0, Ω0), ∀ i, |(p.1 i).im - (z0 i).im| < 1 :=
      eventually_all.mpr fun i =>
        rth21_eventually_abs_lt (f := fun p : (ι → ℂ) × Matrix ι ι ℂ => (p.1 i).im)
          (by fun_prop) (z0, Ω0) one_pos
    have hB : ∀ᶠ p in 𝓝 (z0, Ω0), ∀ i j, |(p.2 i j).im - (Ω0 i j).im| < δ :=
      eventually_all.mpr fun i => eventually_all.mpr fun j =>
        rth21_eventually_abs_lt (f := fun p : (ι → ℂ) × Matrix ι ι ℂ => (p.2 i j).im)
          (by fun_prop) (z0, Ω0) hδ
    filter_upwards [hA, hB] with p hpA hpB
    exact ⟨hpA, hpB⟩
  refine ⟨_, ht, fun n => ∏ i, Real.exp (-π * (c / 2 * (n i : ℝ) ^ 2 - 2 * S * |(n i : ℝ)|)),
    ?_, fun p hp n => ?_⟩
  · refine rth21_summable_prod
      (f := fun k : ℤ => Real.exp (-π * (c / 2 * (k : ℝ) ^ 2 - 2 * S * |(k : ℝ)|)))
      (fun k => (Real.exp_pos _).le) ?_
    have hsum := summable_pow_mul_jacobiTheta₂_term_bound S (half_pos hc) 0
    simp only [pow_zero, one_mul, Int.cast_abs] at hsum
    exact hsum
  · refine rth21_norm_term_le (fun x => ?_) (fun i => ?_) n
    · have hp' := rth21_quad_perturb (Y := Ω0.map Complex.im) (Y' := p.2.map Complex.im)
        (δ := δ) (fun i j => by simpa using (hp.2 i j).le) x
      have := hlow x
      have hsq : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right hδc hsq]
    · have h1 := hp.1 i
      have h2 : |(z0 i).im| ≤ ∑ i, |(z0 i).im| :=
        Finset.single_le_sum (f := fun i => |(z0 i).im|) (fun i _ => abs_nonneg _)
          (Finset.mem_univ i)
      have h3 := abs_sub_abs_le_abs_sub (p.1 i).im (z0 i).im
      rw [hSdef]
      linarith

/-- Absolute convergence of the Riemann theta series (DLMF §21.2(i)). -/
@[dlmf 21.2.i "absolute convergence of the g-tuple Fourier series"]
theorem summable_norm_riemannThetaTerm (z : ι → ℂ) {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) : Summable fun n => ‖riemannThetaTerm z Ω n‖ := by
  obtain ⟨t, ht, u, hu, hb⟩ := rth21_local_majorant (z0 := z) (rth21_posIm_of_mem hΩ)
  exact hu.of_nonneg_of_le (fun n => norm_nonneg _) (hb (z, Ω) (mem_of_mem_nhds ht))

/-- The theta series sums to `θ(z|Ω)` (DLMF 21.2.1). -/
@[dlmf 21.2.E1]
theorem hasSum_riemannTheta (z : ι → ℂ) {Ω : Matrix ι ι ℂ} (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    HasSum (riemannThetaTerm z Ω) (riemannTheta z Ω) :=
  (summable_norm_riemannThetaTerm z hΩ).of_norm.hasSum

/-- Locally uniform convergence of the theta series on the open set where the quadratic form
of `Im Ω` is positive definite (stronger than DLMF: `Ω` need not be symmetric). -/
@[dlmf 21.2.i "stronger than DLMF: locally uniform where the imaginary quadratic form is positive"]
theorem tendstoLocallyUniformlyOn_riemannTheta :
    TendstoLocallyUniformlyOn (fun (s : Finset (ι → ℤ)) (p : (ι → ℂ) × Matrix ι ι ℂ) =>
        ∑ n ∈ s, riemannThetaTerm p.1 p.2 n) (fun p => riemannTheta p.1 p.2) atTop
      {p | rth21_PosIm p.2} := by
  intro u hu p hp
  obtain ⟨t, ht, v, hv, hb⟩ := rth21_local_majorant (z0 := p.1) (Ω0 := p.2) hp
  exact ⟨t, mem_nhdsWithin_of_mem_nhds ht,
    tendstoUniformlyOn_tsum hv (fun n x hx => hb x hx n) u hu⟩

/-- Uniform convergence of the theta series on compact subsets of `ℂ^g × 𝔖_g`
(DLMF §21.2(i)). -/
@[dlmf 21.2.i "uniform convergence on compact sets of the z and Ω spaces"]
theorem tendstoUniformlyOn_riemannTheta {K : Set ((ι → ℂ) × Matrix ι ι ℂ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, p.2 ∈ siegelUpperHalfSpace ι) :
    TendstoUniformlyOn (fun (s : Finset (ι → ℤ)) (p : (ι → ℂ) × Matrix ι ι ℂ) =>
        ∑ n ∈ s, riemannThetaTerm p.1 p.2 n) (fun p => riemannTheta p.1 p.2) atTop K := by
  rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK]
  exact tendstoLocallyUniformlyOn_riemannTheta.mono fun p hp => rth21_posIm_of_mem (hKS p hp)

/-- Continuity of the indicated function: `Continuous fun p : (ι → ℂ) × Matrix ι ι ℂ =>
riemannThetaTerm p.1 p.2 n`. -/
lemma rth21_continuous_term (n : ι → ℤ) :
    Continuous fun p : (ι → ℂ) × Matrix ι ι ℂ => riemannThetaTerm p.1 p.2 n := by
  simp only [riemannThetaTerm, dotProduct, mulVec]
  fun_prop

/-- `θ(z|Ω)` is jointly continuous on `ℂ^g × 𝔖_g`. -/
@[dlmf 21.2.i "continuity of the locally uniform limit"]
theorem continuousOn_riemannTheta :
    ContinuousOn (fun p : (ι → ℂ) × Matrix ι ι ℂ => riemannTheta p.1 p.2)
      {p | p.2 ∈ siegelUpperHalfSpace ι} := by
  refine (tendstoLocallyUniformlyOn_riemannTheta.mono fun p hp =>
    rth21_posIm_of_mem hp).continuousOn
    (Frequently.of_forall fun s =>
      (continuous_finsetSum _ fun n _ => rth21_continuous_term n).continuousOn)

/-- Differentiability at the specified argument: `DifferentiableAt ℂ (fun w => riemannTheta (L
w).1 (L w).2) w0`. -/
lemma rth21_differentiableAt_comp {L : ℂ → (ι → ℂ) × Matrix ι ι ℂ} {w0 : ℂ}
    (hL : Continuous L) (h0 : rth21_PosIm (L w0).2)
    (hd : ∀ n, Differentiable ℂ fun w => riemannThetaTerm (L w).1 (L w).2 n) :
    DifferentiableAt ℂ (fun w => riemannTheta (L w).1 (L w).2) w0 := by
  obtain ⟨t, ht, u, hu, hb⟩ := rth21_local_majorant (z0 := (L w0).1) (Ω0 := (L w0).2) h0
  have hpre : L ⁻¹' t ∈ 𝓝 w0 := hL.continuousAt.preimage_mem_nhds ht
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hD := differentiableOn_tsum_of_summable_norm hu (fun n => (hd n).differentiableOn)
    Metric.isOpen_ball (fun n w hw => hb (L w) (hball hw) n)
  exact hD.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))

/-- `θ(z|Ω)` is an analytic function of each component `z_j` (DLMF §21.2(i)). -/
@[dlmf 21.2.i "analytic in each element of z"]
theorem differentiableAt_riemannTheta_update [DecidableEq ι] (z : ι → ℂ) {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) (j : ι) :
    DifferentiableAt ℂ (fun w => riemannTheta (Function.update z j w) Ω) (z j) := by
  have hupd : ∀ w, Function.update z j w = z + (w - z j) • Pi.single j 1 := by
    intro w
    funext i
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  refine rth21_differentiableAt_comp (L := fun w => (Function.update z j w, Ω))
    (by fun_prop) (by simpa using rth21_posIm_of_mem hΩ) fun n => ?_
  simp only [hupd, riemannThetaTerm, dotProduct_add, dotProduct_smul, dotProduct_single,
    smul_eq_mul]
  fun_prop

/-- `θ(z|Ω)` is an analytic function of each entry `Ω_jk`: here the entry `(j,k)` of
`Ω + (w - Ω_jk) E_jk` is `w` (DLMF §21.2(i)). For a symmetric perturbation see the joint
continuity and the parametrization of the entries; the open domain makes the one-entry
perturbation admissible. -/
@[dlmf 21.2.i "analytic in each element of Ω"]
theorem differentiableAt_riemannTheta_entry [DecidableEq ι] (z : ι → ℂ) {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) (j k : ι) :
    DifferentiableAt ℂ (fun w => riemannTheta z (Ω + (w - Ω j k) • Matrix.single j k 1))
      (Ω j k) := by
  refine rth21_differentiableAt_comp
    (L := fun w => (z, Ω + (w - Ω j k) • Matrix.single j k 1))
    (by fun_prop) (by simpa using rth21_posIm_of_mem hΩ) fun n => ?_
  simp only [riemannThetaTerm, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  fun_prop

end DLMF.RiemannTheta
