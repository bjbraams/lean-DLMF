/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.RiemannTheta.Convergence

/-!
# Boundedness and nonholomorphy of the scaled Riemann theta function
-/

@[expose] public noncomputable section

open Complex Matrix Finset Filter Topology
open scoped Real

variable {ι : Type*} [Fintype ι]
open MeasureTheory

namespace DLMF.RiemannTheta

/-! ## The scaled theta function (DLMF 21.2.2) -/

/-- Summability of the indicated series: `Summable (fun n : ι → ℤ => ∏ i, f i (n i)) ∧ ∑' n : ι →
ℤ, ∏ i, f i (n i) ≤ M ^ Fintype.card ι`. -/
lemma rth21_prod_sum_le {f : ι → ℤ → ℝ} {M : ℝ} (hf0 : ∀ i k, 0 ≤ f i k)
    (hf : ∀ i, Summable (f i)) (hM : ∀ i, ∑' k, f i k ≤ M) :
    Summable (fun n : ι → ℤ => ∏ i, f i (n i)) ∧
      ∑' n : ι → ℤ, ∏ i, f i (n i) ≤ M ^ Fintype.card ι := by
  classical
  have hbound : ∀ s : Finset (ι → ℤ), ∑ n ∈ s, ∏ i, f i (n i) ≤ M ^ Fintype.card ι := by
    intro s
    calc ∑ n ∈ s, ∏ i, f i (n i)
        ≤ ∑ n ∈ Fintype.piFinset (fun i => s.image (fun n : ι → ℤ => n i)), ∏ i, f i (n i) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun n hn => Fintype.mem_piFinset.mpr fun i => Finset.mem_image_of_mem _ hn)
            (fun n _ _ => Finset.prod_nonneg fun i _ => hf0 _ _)
      _ = ∏ i, ∑ k ∈ s.image (fun n : ι → ℤ => n i), f i k := (Finset.prod_univ_sum _ _).symm
      _ ≤ ∏ _i : ι, M :=
          Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun k _ => hf0 i k)
            (fun i _ => ((hf i).sum_le_tsum _ (fun k _ => hf0 i k)).trans (hM i))
      _ = M ^ Fintype.card ι := by simp
  have h0 : ∀ n : ι → ℤ, 0 ≤ ∏ i, f i (n i) := fun n => Finset.prod_nonneg fun i _ => hf0 _ _
  exact ⟨summable_of_sum_le h0 hbound, Real.tsum_le_of_sum_le h0 hbound⟩

/-- Estimate under the stated parameter and domain assumptions: `∃ M : ℝ, ∀ t : ℝ, Summable (fun k
: ℤ => Real.exp (-π * c * ((k : ℝ) + t) ^ 2)) ∧ ∑' k : ℤ, Real.exp (-π * c * ((k : ℝ) + t) ^
2) ≤ M`. -/
lemma rth21_gauss_shift_bound {c : ℝ} (hc : 0 < c) :
    ∃ M : ℝ, ∀ t : ℝ, Summable (fun k : ℤ => Real.exp (-π * c * ((k : ℝ) + t) ^ 2)) ∧
      ∑' k : ℤ, Real.exp (-π * c * ((k : ℝ) + t) ^ 2) ≤ M := by
  have hg : Summable fun k : ℤ => Real.exp (-π * c * (k : ℝ) ^ 2) := by
    have := summable_pow_mul_jacobiTheta₂_term_bound 0 hc 0
    simp only [pow_zero, one_mul, mul_zero, zero_mul, sub_zero] at this
    exact this.congr fun k => by ring_nf
  have hg1 : Summable fun k : ℤ => Real.exp (-π * c * ((k : ℝ) + 1) ^ 2) := by
    have := (Equiv.addRight (1 : ℤ)).summable_iff.mpr hg
    exact this.congr fun k => by simp
  refine ⟨∑' k : ℤ, Real.exp (-π * c * (k : ℝ) ^ 2) +
    ∑' k : ℤ, Real.exp (-π * c * ((k : ℝ) + 1) ^ 2), fun t => ?_⟩
  set t' := t - ⌊t⌋ with ht'
  have ht0 : 0 ≤ t' := by simp [ht']
  have ht1 : t' < 1 := by simp only [ht']; linarith [Int.lt_floor_add_one t]
  have hle : ∀ k : ℤ, Real.exp (-π * c * ((k : ℝ) + t') ^ 2) ≤
      Real.exp (-π * c * (k : ℝ) ^ 2) + Real.exp (-π * c * ((k : ℝ) + 1) ^ 2) := by
    intro k
    have hpc : 0 < π * c := mul_pos Real.pi_pos hc
    rcases le_or_gt 0 k with hk | hk
    · have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
      have : (k : ℝ) ^ 2 ≤ ((k : ℝ) + t') ^ 2 := by nlinarith
      have h1 : Real.exp (-π * c * ((k : ℝ) + t') ^ 2) ≤ Real.exp (-π * c * (k : ℝ) ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith [Real.exp_pos (-π * c * ((k : ℝ) + 1) ^ 2)]
    · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      have : ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + t') ^ 2 := by nlinarith
      have h1 : Real.exp (-π * c * ((k : ℝ) + t') ^ 2) ≤
          Real.exp (-π * c * ((k : ℝ) + 1) ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
      linarith [Real.exp_pos (-π * c * (k : ℝ) ^ 2)]
  have hs' : Summable fun k : ℤ => Real.exp (-π * c * ((k : ℝ) + t') ^ 2) :=
    (hg.add hg1).of_nonneg_of_le (fun k => (Real.exp_pos _).le) hle
  have hshift : ∀ k : ℤ, Real.exp (-π * c * (((k + ⌊t⌋ : ℤ) : ℝ) + t') ^ 2) =
      Real.exp (-π * c * ((k : ℝ) + t) ^ 2) := by
    intro k; simp only [ht']; push_cast; ring_nf
  have hsum : Summable fun k : ℤ => Real.exp (-π * c * ((k : ℝ) + t) ^ 2) := by
    have := (Equiv.addRight ⌊t⌋).summable_iff.mpr hs'
    exact this.congr fun k => by simpa using hshift k
  refine ⟨hsum, ?_⟩
  have heq : ∑' k : ℤ, Real.exp (-π * c * ((k : ℝ) + t) ^ 2) =
      ∑' k : ℤ, Real.exp (-π * c * ((k : ℝ) + t') ^ 2) := by
    calc ∑' k : ℤ, Real.exp (-π * c * ((k : ℝ) + t) ^ 2)
        = ∑' k : ℤ, Real.exp (-π * c * ((((Equiv.addRight ⌊t⌋) k : ℤ) : ℝ) + t') ^ 2) :=
          tsum_congr fun k => by rw [Equiv.coe_addRight, hshift]
      _ = _ := (Equiv.addRight ⌊t⌋).tsum_eq
          (fun k : ℤ => Real.exp (-π * c * ((k : ℝ) + t') ^ 2))
  rw [heq, ← (hg.tsum_add hg1)]
  exact hs'.tsum_le_tsum hle (hg.add hg1)

/-- `θ̂(z|Ω)` is a bounded function of `z` (DLMF §21.2(i), after 21.2.2). -/
@[dlmf 21.2.i "the scaled theta function is bounded in z"]
theorem riemannThetaScaled_bounded [DecidableEq ι] {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) : ∃ C : ℝ, ∀ z : ι → ℂ, ‖riemannThetaScaled z Ω‖ ≤ C := by
  set Y := Ω.map Complex.im with hYdef
  obtain ⟨c, hc, hlow⟩ := rth21_exists_lower (rth21_posIm_of_mem hΩ)
  obtain ⟨M, hM⟩ := rth21_gauss_shift_bound hc
  refine ⟨M ^ Fintype.card ι, fun z => ?_⟩
  set y : ι → ℝ := fun i => (z i).im
  set a : ι → ℝ := Y⁻¹ *ᵥ y
  have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp hΩ.2.isUnit
  have hYsym : Yᵀ = Y := hΩ.2.isHermitian
  have hYa : Y *ᵥ a = y := by
    simp only [a, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hterm : ∀ n : ι → ℤ, Real.exp (-π * (y ⬝ᵥ (Y⁻¹ *ᵥ y))) * ‖riemannThetaTerm z Ω n‖ ≤
      ∏ i, Real.exp (-π * c * ((n i : ℝ) + a i) ^ 2) := by
    intro n
    rw [norm_riemannThetaTerm, ← Real.exp_add, ← Real.exp_sum, Real.exp_le_exp]
    set N : ι → ℝ := fun i => (n i : ℝ)
    have hq := hlow (N + a)
    have hexp : (N + a) ⬝ᵥ (Y *ᵥ (N + a)) =
        N ⬝ᵥ (Y *ᵥ N) + 2 * (N ⬝ᵥ y) + y ⬝ᵥ (Y⁻¹ *ᵥ y) := by
      have h1 : a ⬝ᵥ (Y *ᵥ N) = N ⬝ᵥ y := by
        rw [dotProduct_mulVec, ← mulVec_transpose, hYsym, hYa, dotProduct_comm]
      rw [mulVec_add, hYa, dotProduct_add, add_dotProduct, add_dotProduct, h1]
      simp only [a]
      rw [dotProduct_comm (Y⁻¹ *ᵥ y) y]
      ring
    have hsum : ∑ i, -π * c * ((n i : ℝ) + a i) ^ 2 = -π * (c * ∑ i, (N + a) i ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [N]; ring
    rw [hsum]
    have : N ⬝ᵥ (Y *ᵥ N) + 2 * (N ⬝ᵥ y) + y ⬝ᵥ (Y⁻¹ *ᵥ y) ≥ c * ∑ i, (N + a) i ^ 2 := by
      rw [← hexp]; exact hq
    nlinarith [Real.pi_pos]
  obtain ⟨hprodS, hprodle⟩ := rth21_prod_sum_le
    (f := fun i k => Real.exp (-π * c * ((k : ℝ) + a i) ^ 2))
    (fun i k => (Real.exp_pos _).le) (fun i => (hM (a i)).1) (fun i => (hM (a i)).2)
  have hS := summable_norm_riemannThetaTerm z hΩ
  rw [riemannThetaScaled, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), riemannTheta]
  calc Real.exp (-π * (y ⬝ᵥ (Y⁻¹ *ᵥ y))) * ‖∑' n, riemannThetaTerm z Ω n‖
      ≤ Real.exp (-π * (y ⬝ᵥ (Y⁻¹ *ᵥ y))) * ∑' n, ‖riemannThetaTerm z Ω n‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hS) (Real.exp_pos _).le
    _ = ∑' n, Real.exp (-π * (y ⬝ᵥ (Y⁻¹ *ᵥ y))) * ‖riemannThetaTerm z Ω n‖ :=
        (tsum_mul_left).symm
    _ ≤ ∑' n : ι → ℤ, ∏ i, Real.exp (-π * c * ((n i : ℝ) + a i) ^ 2) :=
        (hS.mul_left _).tsum_le_tsum hterm hprodS
    _ ≤ M ^ Fintype.card ι := hprodle

section p3t

open MeasureTheory

/-- `∫₀¹ e^{2πikt} dt = δ_{k0}`. -/
lemma p3t_integral_exp_int (k : ℤ) :
    ∫ t in Set.Icc (0 : ℝ) 1, cexp (2 * π * I * k * t) = if k = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hk
  · subst hk; simp
  · have hc : (2 * π * I * k : ℂ) ≠ 0 := by
      have := Real.pi_ne_zero
      simp [hk, I_ne_zero, this]
    rw [integral_exp_mul_complex hc]
    have : cexp (2 * π * I * k * ((1 : ℝ) : ℂ)) = 1 := by
      rw [ofReal_one, mul_one, show (2 * π * I * k : ℂ) = k * (2 * π * I) by ring]
      exact exp_int_mul_two_pi_mul_I k
    rw [this]; simp

/-- The cube measure on `[0,1]^ι`. -/
noncomputable abbrev p3t_cube (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => volume.restrict (Set.Icc (0 : ℝ) 1)

/-- A theta term at a real vector as a constant times a product. -/
lemma p3t_term_real (Ω : Matrix ι ι ℂ) (n : ι → ℤ) (x : ι → ℝ) :
    riemannThetaTerm (fun i => (x i : ℂ)) Ω n =
      cexp (2 * π * I * ((1 / 2 : ℂ) * ((fun i => (n i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (n i : ℂ))))) *
        ∏ i, cexp (2 * π * I * (n i) * x i) := by
  rw [riemannThetaTerm, mul_add, Complex.exp_add, ← Complex.exp_sum]
  congr 2
  simp only [dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `∫_{[0,1]^g}` of a theta term is `δ_{n0}`. -/
lemma p3t_integral_term (Ω : Matrix ι ι ℂ) (n : ι → ℤ) :
    ∫ x, riemannThetaTerm (fun i => (x i : ℂ)) Ω n ∂(p3t_cube ι) = if n = 0 then 1 else 0 := by
  simp_rw [p3t_term_real]
  rw [integral_const_mul]
  rw [integral_fintype_prod_eq_prod (f := fun i (t : ℝ) => cexp (2 * π * I * (n i) * t))]
  simp_rw [p3t_integral_exp_int]
  rw [Finset.prod_boole]
  by_cases hn : n = 0
  · subst hn; simp
  · have : ∃ i, n i ≠ 0 := by
      by_contra h; exact hn (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
    simp [hn, this]

/-- The modulus of a theta term at a real vector. -/
lemma p3t_norm_term_real (Ω : Matrix ι ι ℂ) (n : ι → ℤ) (x : ι → ℝ) :
    ‖riemannThetaTerm (fun i => (x i : ℂ)) Ω n‖ = ‖riemannThetaTerm 0 Ω n‖ := by
  rw [norm_riemannThetaTerm, norm_riemannThetaTerm]
  simp

/-- The cube has measure one. -/
lemma p3t_cube_univ : (p3t_cube ι) Set.univ = 1 := by
  rw [p3t_cube, Measure.pi_univ]
  simp

/-- `∫_{[0,1]^g} θ(x|Ω) dx = 1`, so `θ(·|Ω)` is not identically zero. -/
lemma p3t_integral_riemannTheta {Ω : Matrix ι ι ℂ} (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    ∫ x, riemannTheta (fun i => (x i : ℂ)) Ω ∂(p3t_cube ι) = 1 := by
  have hfin : IsFiniteMeasure (p3t_cube ι) := ⟨by rw [p3t_cube_univ]; simp⟩
  have hint : ∀ n, Integrable (fun x : ι → ℝ => riemannThetaTerm (fun i => (x i : ℂ)) Ω n)
      (p3t_cube ι) := by
    intro n
    refine Integrable.of_bound ?_ ‖riemannThetaTerm 0 Ω n‖
      (Eventually.of_forall fun x => (p3t_norm_term_real Ω n x).le)
    refine Continuous.aestronglyMeasurable ?_
    simp only [riemannThetaTerm, dotProduct]
    fun_prop
  have hsum : Summable fun n => ∫ x, ‖riemannThetaTerm (fun i => (x i : ℂ)) Ω n‖ ∂(p3t_cube ι) := by
    simp_rw [p3t_norm_term_real, integral_const, smul_eq_mul]
    exact (summable_norm_riemannThetaTerm 0 hΩ).mul_left _
  simp only [riemannTheta]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [p3t_integral_term]
  exact tsum_ite_eq 0 1

end p3t

/-- `θ̂(z|Ω)` is not an analytic function of `z` (DLMF §21.2(i), after 21.2.2); genus
`g ≥ 1`. -/
@[dlmf 21.2.i "the scaled theta function is nonanalytic in z"]
theorem not_differentiable_riemannThetaScaled [DecidableEq ι] [Nonempty ι] {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    ¬ Differentiable ℂ fun z : ι → ℂ => riemannThetaScaled z Ω := by
  intro hd
  obtain ⟨C, hC⟩ := riemannThetaScaled_bounded hΩ
  have hb : Bornology.IsBounded (Set.range fun z => riemannThetaScaled z Ω) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨C, by rintro _ ⟨z, rfl⟩; exact hC z⟩
  have hconst : ∀ z, riemannThetaScaled z Ω = riemannThetaScaled 0 Ω := fun z =>
    hd.apply_eq_apply_of_bounded hb z 0
  have hreal : ∀ x : ι → ℝ, riemannThetaScaled (fun i => (x i : ℂ)) Ω =
      riemannTheta (fun i => (x i : ℂ)) Ω := by
    intro x
    have h0 : (fun i => ((x i : ℂ)).im) = 0 := by funext i; simp
    rw [riemannThetaScaled, h0]; simp
  have hc1 : riemannThetaScaled 0 Ω = 1 := by
    have h := p3t_integral_riemannTheta hΩ
    have e : (fun x : ι → ℝ => riemannTheta (fun i => (x i : ℂ)) Ω) =
        fun _ => riemannThetaScaled 0 Ω := by
      funext x; rw [← hreal, hconst]
    rw [e, MeasureTheory.integral_const, MeasureTheory.measureReal_def, p3t_cube_univ] at h
    simpa using h
  set Y := Ω.map Complex.im with hY
  have hθ : ∀ z : ι → ℂ, riemannTheta z Ω =
      (Real.exp (π * ((fun i => (z i).im) ⬝ᵥ (Y⁻¹ *ᵥ fun i => (z i).im))) : ℂ) := by
    intro z
    have h := hconst z
    rw [hc1, riemannThetaScaled] at h
    rw [← hY] at h
    have he : (Real.exp (-π * ((fun i => (z i).im) ⬝ᵥ (Y⁻¹ *ᵥ fun i => (z i).im))) : ℂ) *
        (Real.exp (π * ((fun i => (z i).im) ⬝ᵥ (Y⁻¹ *ᵥ fun i => (z i).im))) : ℂ) = 1 := by
      rw [← ofReal_mul, ← Real.exp_add]; simp
    calc riemannTheta z Ω = ((Real.exp (-π * ((fun i => (z i).im) ⬝ᵥ
          (Y⁻¹ *ᵥ fun i => (z i).im))) : ℂ) * riemannTheta z Ω) *
          (Real.exp (π * ((fun i => (z i).im) ⬝ᵥ (Y⁻¹ *ᵥ fun i => (z i).im))) : ℂ) := by
          rw [mul_comm _ (riemannTheta z Ω), mul_assoc, he, mul_one]
      _ = _ := by rw [h, one_mul]
  obtain ⟨j⟩ := ‹Nonempty ι›
  set v : ι → ℂ := Pi.single j 1 with hv
  set g : ℂ → ℂ := fun w => riemannTheta (w • v) Ω with hgdef
  have hg : Differentiable ℂ g := fun w0 =>
    rth21_differentiableAt_comp (L := fun w => (w • v, Ω)) (by fun_prop)
      (rth21_posIm_of_mem hΩ) fun n => by
        simp only [riemannThetaTerm, dotProduct_smul, smul_eq_mul]
        fun_prop
  have him : ∀ w : ℂ, (fun i => ((w • v) i).im) = w.im • (Pi.single j 1 : ι → ℝ) := by
    intro w; funext i
    by_cases h : i = j
    · subst h; simp [hv]
    · simp [hv, h]
  have hgr : ∀ w : ℂ, ∀ t : ℝ, g (w + t) = g w := by
    intro w t
    simp only [hgdef, hθ, him, add_im, ofReal_im, add_zero]
  have hg' : ∀ w, deriv g w = 0 := by
    intro w
    have h1 : HasDerivAt (fun u => g (w + u)) (deriv g w) ((0 : ℝ) : ℂ) := by
      rw [ofReal_zero]
      exact HasDerivAt.comp_const_add w 0 (by rw [add_zero]; exact (hg w).hasDerivAt)
    have h2 := h1.comp_ofReal
    have h3 : (fun t : ℝ => g (w + t)) = fun _ => g w := funext fun t => hgr w t
    rw [h3] at h2
    exact h2.unique (hasDerivAt_const _ _)
  have h4 := is_const_of_deriv_eq_zero hg hg' I 0
  simp only [hgdef, hθ, him, I_im, zero_im, one_smul, zero_smul] at h4
  have h5 : π * ((Pi.single j 1 : ι → ℝ) ⬝ᵥ (Y⁻¹ *ᵥ Pi.single j 1)) = 0 := by
    have := congrArg Complex.re h4
    simp only [ofReal_re, Matrix.mulVec_zero, zero_dotProduct, mul_zero, Real.exp_zero] at this
    exact Real.exp_eq_one_iff _ |>.mp this
  have h6 := hΩ.2.inv.dotProduct_mulVec_pos (x := (Pi.single j 1 : ι → ℝ))
    (by simp)
  rw [star_trivial] at h6
  have := Real.pi_pos
  nlinarith

/-- The series form `Θ(φ|B) = ∑ₙ exp(½ n·B·n + n·φ)` of the alternative normalization
(DLMF §21.1). -/
@[dlmf 21.1 "series form of Θ(φ|B)"]
theorem riemannThetaBig_eq_tsum (φ : ι → ℂ) (B : Matrix ι ι ℂ) :
    riemannThetaBig φ B = ∑' n : ι → ℤ, cexp ((1 / 2 : ℂ) *
      ((fun i => (n i : ℂ)) ⬝ᵥ (B *ᵥ fun i => (n i : ℂ))) + (fun i => (n i : ℂ)) ⬝ᵥ φ) := by
  rw [riemannThetaBig, riemannTheta]
  refine tsum_congr fun n => ?_
  rw [riemannThetaTerm]
  congr 1
  have h : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have h2 : (fun i => φ i / (2 * π * I)) = (2 * π * I)⁻¹ • φ := by
    funext i
    simp [div_eq_inv_mul]
  rw [h2, smul_mulVec, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  field_simp

end DLMF.RiemannTheta
