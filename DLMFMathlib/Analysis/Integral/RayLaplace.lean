/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.WatsonRotated

/-!
# Laplace transforms on rotated rays in logarithmic coordinates

The logarithmic parameter keeps distinct continuations around the origin separate.
The integral on the ray of angle `θ` is holomorphic where its exponential kernel decays
faster than the growth of the original function on that ray.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology Real

namespace Complex

/-- A Laplace transform on the ray of angle `θ`, as a function of the logarithm `ζ` of the
Laplace parameter. The ray is parameterized outward from the origin. -/
def rayLaplace (q : ℂ → ℂ) (θ : ℝ) (ζ : ℂ) : ℂ :=
  exp (θ * I) * ∫ r in Ioi (0 : ℝ),
    exp (-(exp (ζ + θ * I) * r)) * q (r * exp (θ * I))

/-- The strip on the logarithmic plane where the ray has the chosen branch and its
Laplace kernel dominates growth of exponential rate `σ`. -/
def rayLaplaceDomain (σ θ : ℝ) : Set ℂ :=
  {ζ | |ζ.im + θ| < Real.pi / 2 ∧ σ < (exp (ζ + θ * I)).re}

/-- Uniform power bounds at zero and exponential bounds at infinity on a closed interval
of ray angles. The same constant bounds both endpoints of the radial split at one. -/
def HasRayLaplaceBounds (q : ℂ → ℂ) (σ ρ : ℝ) (angles : Set ℝ) : Prop :=
  ∀ θ ∈ angles, ∀ θ' ∈ angles, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ uIcc θ θ',
    (∀ r : ℝ, 0 < r → r ≤ 1 → ‖q (r * exp (y * I))‖ ≤ C * r ^ (ρ - 1)) ∧
    (∀ r : ℝ, 1 ≤ r → ‖q (r * exp (y * I))‖ ≤ C * Real.exp (σ * r))

/-- On a compact annular sector a continuous function is bounded by a positive continuous
radial weight. -/
theorem exists_bound_on_ray_rectangle {q : ℂ → ℂ} {a b θ θ' : ℝ} {w : ℝ → ℝ}
    (ha : 0 < a)
    (hq : ∀ r ∈ Icc a b, ∀ y ∈ uIcc θ θ', ContinuousAt q (r * exp (y * I)))
    (hw : ContinuousOn w (Icc a b)) (hwpos : ∀ r ∈ Icc a b, 0 < w r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc a b, ∀ y ∈ uIcc θ θ',
      ‖q (r * exp (y * I))‖ ≤ C * w r := by
  let K : Set (ℝ × ℝ) := Icc a b ×ˢ uIcc θ θ'
  have hqc : ContinuousOn (fun p : ℝ × ℝ => q (p.1 * exp (p.2 * I))) K := by
    intro p hp
    exact (ContinuousAt.comp (g := q)
      (f := fun p : ℝ × ℝ => (p.1 : ℂ) * exp (p.2 * I))
      (hq p.1 hp.1 p.2 hp.2) (by fun_prop)).continuousWithinAt
  have hwc : ContinuousOn (fun p : ℝ × ℝ => w p.1) K :=
    hw.comp continuous_fst.continuousOn fun p hp => hp.1
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn
    (hqc.norm.div hwc fun p hp => (hwpos p.1 hp.1).ne')
  refine ⟨max M 0, le_max_right _ _, fun r hr y hy => ?_⟩
  have h := hM (r, y) ⟨hr, hy⟩
  dsimp only [Pi.div_apply] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (hwpos r hr).le)] at h
  exact (div_le_iff₀ (hwpos r hr)).mp (h.trans (le_max_left _ _))

/-- Uniform endpoint bounds on a closed angular interval extend across its compact radial
middle. This turns local bounds at zero and infinity into the bounds with split radius one. -/
theorem hasRayLaplaceBounds_of_local_bounds {q : ℂ → ℂ} {σ ρ : ℝ} {angles : Set ℝ}
    (hqc : ∀ θ ∈ angles, ∀ θ' ∈ angles, ∀ r : ℝ, 0 < r → ∀ y ∈ uIcc θ θ',
      ContinuousAt q (r * exp (y * I)))
    (hzero : ∀ θ ∈ angles, ∀ θ' ∈ angles, ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ r : ℝ, 0 < r → r ≤ ε → ∀ y ∈ uIcc θ θ',
        ‖q (r * exp (y * I))‖ ≤ C * r ^ (ρ - 1))
    (htop : ∀ θ ∈ angles, ∀ θ' ∈ angles, ∃ R C : ℝ, 0 ≤ C ∧
      ∀ r : ℝ, R ≤ r → ∀ y ∈ uIcc θ θ',
        ‖q (r * exp (y * I))‖ ≤ C * Real.exp (σ * r)) :
    HasRayLaplaceBounds q σ ρ angles := by
  intro θ hθ θ' hθ'
  obtain ⟨ε, C₀, hε, hC₀, hb₀⟩ := hzero θ hθ θ' hθ'
  obtain ⟨R, Cinf, hCinf, hbinf⟩ := htop θ hθ θ' hθ'
  let d := min ε 1
  have hd : 0 < d := lt_min hε zero_lt_one
  obtain ⟨M₀, hM₀, hbM₀⟩ := exists_bound_on_ray_rectangle (q := q) hd
    (fun r hr y hy => hqc θ hθ θ' hθ' r (hd.trans_le hr.1) y hy)
    (w := fun r : ℝ => r ^ (ρ - 1))
    (fun r hr => (Real.continuousAt_rpow_const _ _ (Or.inl
      (hd.trans_le hr.1).ne')).continuousWithinAt)
    (fun r hr => Real.rpow_pos_of_pos (hd.trans_le hr.1) _)
  obtain ⟨Minf, hMinf, hbMinf⟩ := exists_bound_on_ray_rectangle (q := q) zero_lt_one
    (a := 1) (b := max R 1)
    (fun r hr y hy => hqc θ hθ θ' hθ' r (zero_lt_one.trans_le hr.1) y hy)
    (w := fun r : ℝ => Real.exp (σ * r)) (by fun_prop)
    (fun r _ => Real.exp_pos _)
  let C := max (max C₀ Cinf) (max M₀ Minf)
  have hC₀C : C₀ ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCinfC : Cinf ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hM₀C : M₀ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hMinfC : Minf ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC₀.trans hC₀C, fun y hy => ⟨?_, ?_⟩⟩
  · intro r hr hr1
    rcases le_total r d with hrd | hdr
    · exact (hb₀ r hr (hrd.trans (min_le_left _ _)) y hy).trans
        (mul_le_mul_of_nonneg_right hC₀C (Real.rpow_nonneg hr.le _))
    · exact (hbM₀ r ⟨hdr, hr1⟩ y hy).trans
        (mul_le_mul_of_nonneg_right hM₀C (Real.rpow_nonneg hr.le _))
  · intro r hr
    rcases le_total R r with hRr | hrR
    · exact (hbinf r hRr y hy).trans
        (mul_le_mul_of_nonneg_right hCinfC (Real.exp_pos _).le)
    · exact (hbMinf r ⟨hr, hrR.trans (le_max_left _ _)⟩ y hy).trans
        (mul_le_mul_of_nonneg_right hMinfC (Real.exp_pos _).le)

/-- The ray transform with angle zero is the original Laplace integral at `exp ζ`. -/
theorem rayLaplace_zero (q : ℂ → ℂ) (ζ : ℂ) :
    rayLaplace q 0 ζ = ∫ r in Ioi (0 : ℝ), exp (-(exp ζ * r)) * q r := by
  simp [rayLaplace]

/-- The convergence strip of a ray transform is open. -/
theorem isOpen_rayLaplaceDomain (σ θ : ℝ) : IsOpen (rayLaplaceDomain σ θ) := by
  change IsOpen ({ζ : ℂ | |ζ.im + θ| < Real.pi / 2} ∩
    {ζ : ℂ | σ < (exp (ζ + θ * I)).re})
  exact (isOpen_lt (by fun_prop) continuous_const).inter
    (isOpen_lt continuous_const (by fun_prop))

/-- Bounds at the two radial endpoints imply absolute convergence on a rotated ray. -/
theorem integrableOn_rayLaplace_kernel {q : ℂ → ℂ} {σ ρ C θ : ℝ} {z : ℂ}
    (hσ : 0 ≤ σ) (hρ : 0 < ρ) (hz : σ < z.re)
    (hqc : ContinuousOn (fun r : ℝ => q (r * exp (θ * I))) (Ioi 0))
    (hzero : ∀ r : ℝ, 0 < r → r ≤ 1 → ‖q (r * exp (θ * I))‖ ≤ C * r ^ (ρ - 1))
    (htop : ∀ r : ℝ, 1 ≤ r → ‖q (r * exp (θ * I))‖ ≤ C * Real.exp (σ * r)) :
    IntegrableOn (fun r : ℝ => exp (-(z * r)) * q (r * exp (θ * I))) (Ioi 0) := by
  suffices h : IntegrableOn (fun r : ℝ => exp (-(z * (r * exp ((0 : ℝ) * I)))) *
      q ((r * exp ((0 : ℝ) * I)) * exp (θ * I))) (Ioi 0) by simpa using h
  apply integrableOn_ray_of_bounds (f := fun w => exp (-(z * w)) * q (w * exp (θ * I)))
    (y := 0) hρ (sub_pos.mpr hz)
  · intro r hr
    simpa only [Pi.mul_def, ofReal_zero, zero_mul, exp_zero, mul_one] using
      ((by fun_prop : ContinuousAt (fun r : ℝ => exp (-(z * r))) r).mul
      (hqc.continuousAt (Ioi_mem_nhds hr)))
  · intro r hr hr1
    simp only [ofReal_zero, zero_mul, exp_zero, mul_one]
    rw [norm_mul, norm_exp]
    have hnorm : (-(z * (r : ℂ))).re = -z.re * r := by simp
    rw [hnorm]
    calc Real.exp (-z.re * r) * ‖q (r * exp (θ * I))‖ ≤
        1 * (C * r ^ (ρ - 1)) := mul_le_mul
          (Real.exp_le_one_iff.mpr (by nlinarith)) (hzero r hr hr1) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · intro r hr
    simp only [ofReal_zero, zero_mul, exp_zero, mul_one]
    rw [norm_mul, norm_exp]
    simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    calc Real.exp (-(z.re * r)) * ‖q (r * exp (θ * I))‖ ≤
        Real.exp (-(z.re * r)) * (C * Real.exp (σ * r)) :=
          mul_le_mul_of_nonneg_left (htop r hr) (Real.exp_pos _).le
      _ = C * Real.exp (-(z.re - σ) * r) := by
        rw [← mul_assoc, mul_comm _ C, mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- The rotated Laplace transform is holomorphic on its strip in logarithmic coordinates. -/
theorem differentiableOn_rayLaplace {q : ℂ → ℂ} {σ ρ θ : ℝ} {angles : Set ℝ}
    (hσ : 0 ≤ σ) (hρ : 0 < ρ) (hθ : θ ∈ angles)
    (hqc : ContinuousOn (fun r : ℝ => q (r * exp (θ * I))) (Ioi 0))
    (hb : HasRayLaplaceBounds q σ ρ angles) :
    DifferentiableOn ℂ (rayLaplace q θ) (rayLaplaceDomain σ θ) := by
  obtain ⟨C, hC, hbound⟩ := hb θ hθ θ hθ
  have hzero := (hbound θ (by simp)).1
  have htop := (hbound θ (by simp)).2
  intro ζ hζ
  let c := (σ + (exp (ζ + θ * I)).re) / 2
  have hσc : σ < c := by dsimp [c]; linarith [hζ.2]
  have hcζ : c < (exp (ζ + θ * I)).re := by dsimp [c]; linarith [hζ.2]
  have hint : IntegrableOn (fun r : ℝ => Real.exp (-c * r) •
      q (r * exp (θ * I))) (Ioi 0) := by
    convert integrableOn_rayLaplace_kernel hσ hρ (z := (c : ℂ))
      (by simpa using hσc) hqc hzero htop using 1
    funext r
    simp only [real_smul, ofReal_exp, ofReal_mul, ofReal_neg, neg_mul]
  have hd := (differentiableOn_integral_cexp_neg_mul_smul hint).differentiableAt
    ((isOpen_lt continuous_const continuous_re).mem_nhds hcζ)
  have he : DifferentiableAt ℂ (fun z : ℂ => exp (z + θ * I)) ζ := by fun_prop
  exact ((hd.comp ζ he).const_mul (exp (θ * I))).differentiableWithinAt

/-- On an interval of angles lying in the right half-plane, the real part of the exponential
is bounded below by the smaller of its endpoint real parts. -/
theorem min_re_exp_add_mul_I_le {ζ : ℂ} {θ θ' y : ℝ}
    (hθ : |ζ.im + θ| < Real.pi / 2) (hθ' : |ζ.im + θ'| < Real.pi / 2)
    (hy : y ∈ uIcc θ θ') :
    min (exp (ζ + θ * I)).re (exp (ζ + θ' * I)).re ≤ (exp (ζ + y * I)).re := by
  have hyabs : |ζ.im + y| ≤ max |ζ.im + θ| |ζ.im + θ'| := by
    rcases le_total θ θ' with hle | hle
    · rw [uIcc_of_le hle] at hy
      apply abs_le.mpr
      constructor
      · linarith [neg_abs_le (ζ.im + θ), le_max_left |ζ.im + θ| |ζ.im + θ'|, hy.1]
      · linarith [le_abs_self (ζ.im + θ'), le_max_right |ζ.im + θ| |ζ.im + θ'|, hy.2]
    · rw [uIcc_of_ge hle] at hy
      apply abs_le.mpr
      constructor
      · linarith [neg_abs_le (ζ.im + θ'), le_max_right |ζ.im + θ| |ζ.im + θ'|, hy.1]
      · linarith [le_abs_self (ζ.im + θ), le_max_left |ζ.im + θ| |ζ.im + θ'|, hy.2]
  have hre (u : ℝ) : (exp (ζ + u * I)).re = Real.exp ζ.re * Real.cos (ζ.im + u) := by
    simp [exp_re]
  rcases le_total |ζ.im + θ| |ζ.im + θ'| with hle | hle
  · rw [max_eq_right hle] at hyabs
    have hcos : Real.cos (ζ.im + θ') ≤ Real.cos (ζ.im + y) := by
      simpa only [Real.cos_abs] using Real.cos_le_cos_of_nonneg_of_le_pi
        (abs_nonneg (ζ.im + y)) (by linarith [Real.pi_pos]) hyabs
    exact (min_le_right _ _).trans (by rw [hre, hre]; gcongr)
  · rw [max_eq_left hle] at hyabs
    have hcos : Real.cos (ζ.im + θ) ≤ Real.cos (ζ.im + y) := by
      simpa only [Real.cos_abs] using Real.cos_le_cos_of_nonneg_of_le_pi
        (abs_nonneg (ζ.im + y)) (by linarith [Real.pi_pos]) hyabs
    exact (min_le_left _ _).trans (by rw [hre, hre]; gcongr)

/-- Laplace integrals along two rays agree on the overlap of their logarithmic convergence
strips, under uniform endpoint bounds and holomorphy between the rays. -/
theorem rayLaplace_eq_of_bounds {q : ℂ → ℂ} {σ ρ θ θ' C : ℝ} {ζ : ℂ}
    (hσ : 0 ≤ σ) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hζ : ζ ∈ rayLaplaceDomain σ θ) (hζ' : ζ ∈ rayLaplaceDomain σ θ')
    (hqd : ∀ r : ℝ, 0 < r → ∀ y ∈ uIcc θ θ',
      DifferentiableAt ℂ q (r * exp (y * I)))
    (hzero : ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ y ∈ uIcc θ θ',
      ‖q (r * exp (y * I))‖ ≤ C * r ^ (ρ - 1))
    (htop : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ uIcc θ θ',
      ‖q (r * exp (y * I))‖ ≤ C * Real.exp (σ * r)) :
    rayLaplace q θ ζ = rayLaplace q θ' ζ := by
  let κ := min (exp (ζ + θ * I)).re (exp (ζ + θ' * I)).re - σ
  have hκ : 0 < κ := sub_pos.mpr (lt_min hζ.2 hζ'.2)
  have hre (y : ℝ) (hy : y ∈ uIcc θ θ') :
      σ + κ ≤ (exp (ζ + y * I)).re := by
    simpa [κ] using min_re_exp_add_mul_I_le hζ.1 hζ'.1 hy
  let f : ℂ → ℂ := fun w => exp (-(exp (ζ + θ * I) * w)) * q (w * exp (θ * I))
  have hyangle (y : ℝ) (hy : y ∈ uIcc 0 (θ' - θ)) : θ + y ∈ uIcc θ θ' := by
    rcases le_total θ θ' with hle | hle
    · rw [uIcc_of_le (sub_nonneg.mpr hle)] at hy
      rw [uIcc_of_le hle]
      constructor <;> linarith [hy.1, hy.2]
    · rw [uIcc_of_ge (sub_nonpos.mpr hle)] at hy
      rw [uIcc_of_ge hle]
      constructor <;> linarith [hy.1, hy.2]
  have heq (r y : ℝ) : f (r * exp (y * I)) =
      exp (-(exp (ζ + ((θ + y : ℝ) : ℂ) * I) * r)) * q (r * exp (((θ + y : ℝ) : ℂ) * I)) := by
    dsimp [f]
    have hphase : exp (y * I) * exp (θ * I) = exp (((θ + y : ℝ) : ℂ) * I) := by
      rw [← exp_add]
      congr 1
      push_cast
      ring
    have hphase' : exp (ζ + θ * I) * exp (y * I) = exp (ζ + ((θ + y : ℝ) : ℂ) * I) := by
      rw [← exp_add]
      congr 1
      push_cast
      ring
    rw [mul_assoc _ _ (exp (θ * I)), hphase]
    congr 2
    rw [← mul_assoc, mul_comm (exp (ζ + θ * I)) (r : ℂ), mul_assoc, hphase']
    ring
  have hd (r : ℝ) (hr : 0 < r) (y : ℝ) (hy : y ∈ uIcc 0 (θ' - θ)) :
      DifferentiableAt ℂ f (r * exp (y * I)) := by
    have hq := hqd r hr (θ + y) (hyangle y hy)
    have hphase : (r : ℂ) * exp (y * I) * exp (θ * I) = r * exp (((θ + y : ℝ) : ℂ) * I) := by
      rw [mul_assoc, ← exp_add]
      congr 2
      push_cast
      ring
    rw [← hphase] at hq
    have hinner : DifferentiableAt ℂ (fun w : ℂ => w * exp (θ * I))
        (r * exp (y * I)) := by fun_prop
    exact (by fun_prop : DifferentiableAt ℂ (fun w => exp (-(exp (ζ + θ * I) * w)))
      (r * exp (y * I))).mul (hq.comp (r * exp (y * I)) hinner)
  have h0 (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (y : ℝ)
      (hy : y ∈ uIcc 0 (θ' - θ)) : ‖f (r * exp (y * I))‖ ≤ C * r ^ (ρ - 1) := by
    rw [heq, norm_mul, norm_exp]
    have hy' := hyangle y hy
    have hpos : 0 ≤ (exp (ζ + ((θ + y : ℝ) : ℂ) * I)).re := by linarith [hre _ hy']
    simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact (mul_le_mul (Real.exp_le_one_iff.mpr (by nlinarith))
      (hzero r hr hr1 _ hy') (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hinf (r : ℝ) (hr : 1 ≤ r) (y : ℝ)
      (hy : y ∈ uIcc 0 (θ' - θ)) : ‖f (r * exp (y * I))‖ ≤ C * Real.exp (-κ * r) := by
    rw [heq, norm_mul, norm_exp]
    have hy' := hyangle y hy
    simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    calc Real.exp (-((exp (ζ + ((θ + y : ℝ) : ℂ) * I)).re * r)) *
        ‖q (r * exp (((θ + y : ℝ) : ℂ) * I))‖ ≤
        Real.exp (-((σ + κ) * r)) * (C * Real.exp (σ * r)) :=
          mul_le_mul (Real.exp_le_exp.mpr (by nlinarith [hre _ hy'])) (htop r hr _ hy')
            (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by
        rw [← mul_assoc, mul_comm _ C, mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hrot := integral_Ioi_eq_exp_mul_integral_Ioi_rotate hρ hκ hd h0 hinf
  have he0 : (fun r : ℝ => f r) =
      (fun r : ℝ => exp (-(exp (ζ + θ * I) * r)) * q (r * exp (θ * I))) := rfl
  have he1 : (fun r : ℝ => f (r * exp (((θ' - θ : ℝ) : ℂ) * I))) =
      (fun r : ℝ => exp (-(exp (ζ + θ' * I) * r)) * q (r * exp (θ' * I))) := by
    funext r
    rw [heq]
    rw [add_sub_cancel]
  rw [he0, he1] at hrot
  unfold rayLaplace
  rw [hrot, ← mul_assoc, ← exp_add]
  congr 1
  push_cast
  ring

/-- Uniform bounds in closed angular intervals give holomorphic ray transforms that agree
on every overlap in the logarithmic plane. -/
theorem rayLaplace_differentiableOn_and_eqOn {q : ℂ → ℂ} {σ ρ a b : ℝ}
    (hσ : 0 ≤ σ) (hρ : 0 < ρ)
    (hqd : ∀ r : ℝ, 0 < r → ∀ θ ∈ Ioo a b,
      DifferentiableAt ℂ q (r * exp (θ * I)))
    (hb : HasRayLaplaceBounds q σ ρ (Ioo a b)) :
    (∀ θ ∈ Ioo a b, DifferentiableOn ℂ (rayLaplace q θ) (rayLaplaceDomain σ θ)) ∧
      ∀ θ ∈ Ioo a b, ∀ θ' ∈ Ioo a b,
        EqOn (rayLaplace q θ) (rayLaplace q θ')
          (rayLaplaceDomain σ θ ∩ rayLaplaceDomain σ θ') := by
  constructor
  · intro θ hθ
    apply differentiableOn_rayLaplace hσ hρ hθ _ hb
    intro r hr
    have hi : Continuous (fun r : ℝ => (r : ℂ) * exp (θ * I)) := by fun_prop
    exact (ContinuousAt.comp (g := q) (f := fun r : ℝ => (r : ℂ) * exp (θ * I))
      (x := r) (hqd r hr θ hθ).continuousAt hi.continuousAt).continuousWithinAt
  · intro θ hθ θ' hθ' ζ hζ
    obtain ⟨C, hC, hbound⟩ := hb θ hθ θ' hθ'
    have hsub : uIcc θ θ' ⊆ Ioo a b := by
      intro y hy
      exact ⟨(lt_min hθ.1 hθ'.1).trans_le hy.1,
        hy.2.trans_lt (max_lt hθ.2 hθ'.2)⟩
    exact rayLaplace_eq_of_bounds hσ hρ hC hζ.1 hζ.2
      (fun r hr y hy => hqd r hr y (hsub hy))
      (fun r hr hr1 y hy => (hbound y hy).1 r hr hr1)
      (fun r hr y hy => (hbound y hy).2 r hr)

/-- The ray transforms define a single holomorphic function on the union of their
logarithmic convergence strips. -/
theorem exists_differentiableOn_rayLaplace {q : ℂ → ℂ} {σ ρ a b : ℝ}
    (hσ : 0 ≤ σ) (hρ : 0 < ρ)
    (hqd : ∀ r : ℝ, 0 < r → ∀ θ ∈ Ioo a b,
      DifferentiableAt ℂ q (r * exp (θ * I)))
    (hb : HasRayLaplaceBounds q σ ρ (Ioo a b)) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (⋃ θ ∈ Ioo a b, rayLaplaceDomain σ θ) ∧
      ∀ θ ∈ Ioo a b, EqOn H (rayLaplace q θ) (rayLaplaceDomain σ θ) := by
  classical
  have h := rayLaplace_differentiableOn_and_eqOn hσ hρ hqd hb
  let admissible : ℂ → Prop := fun ζ => ∃ θ ∈ Ioo a b, ζ ∈ rayLaplaceDomain σ θ
  let H : ℂ → ℂ := fun ζ => if hζ : admissible ζ then
    rayLaplace q (Classical.choose hζ) ζ else 0
  have key (θ : ℝ) (hθ : θ ∈ Ioo a b) : EqOn H (rayLaplace q θ) (rayLaplaceDomain σ θ) := by
    intro ζ hζ
    have hadm : admissible ζ := ⟨θ, hθ, hζ⟩
    have hc := Classical.choose_spec hadm
    change (if hζ' : admissible ζ then rayLaplace q (Classical.choose hζ') ζ else 0) = _
    rw [dite_eq_left hadm]
    exact h.2 _ hc.1 θ hθ ⟨hc.2, hζ⟩
  refine ⟨H, fun ζ hζ => ?_, key⟩
  obtain ⟨θ, hθ, hζθ⟩ := Set.mem_iUnion₂.mp hζ
  have hd := (h.1 θ hθ).differentiableAt ((isOpen_rayLaplaceDomain σ θ).mem_nhds hζθ)
  refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
  exact (isOpen_rayLaplaceDomain σ θ).eventually_mem hζθ |>.mono fun z hz => key θ hθ hz

/-- Every closed substrip of the full continued angular domain is covered by the ray
domains when its real coordinate is sufficiently large. -/
theorem exists_re_ge_mem_iUnion_rayLaplaceDomain {σ a b L U : ℝ} (hab : a < b)
    (hL : -b - Real.pi / 2 < L) (hU : U < -a + Real.pi / 2) :
    ∃ R : ℝ, ∀ ζ : ℂ, R ≤ ζ.re → ζ.im ∈ Icc L U →
      ζ ∈ ⋃ θ ∈ Ioo a b, rayLaplaceDomain σ θ := by
  let δ := min ((b - a) / 4) (min ((L + b + Real.pi / 2) / 4)
    (min ((-a + Real.pi / 2 - U) / 4) (Real.pi / 8)))
  have hδ : 0 < δ := by
    dsimp [δ]
    apply lt_min (by linarith)
    apply lt_min (by linarith)
    apply lt_min (by linarith)
    positivity
  have hδab : δ ≤ (b - a) / 4 := min_le_left _ _
  have hδL : δ ≤ (L + b + Real.pi / 2) / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδU : δ ≤ (-a + Real.pi / 2 - U) / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδπ : δ ≤ Real.pi / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let γ := Real.cos (Real.pi / 2 - δ)
  have hγ : 0 < γ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (Real.tendsto_exp_atTop.eventually_gt_atTop (σ / γ))
  refine ⟨R, fun ζ hζ hη => ?_⟩
  let θ := max (a + δ) (min (b - δ) (-ζ.im))
  have hθa : a < θ := (by linarith : a < a + δ).trans_le (le_max_left _ _)
  have hθb : θ < b := by
    dsimp [θ]
    apply max_lt (by linarith)
    exact (min_le_left _ _).trans_lt (by linarith)
  have hphase : |ζ.im + θ| ≤ Real.pi / 2 - δ := by
    apply abs_le.mpr
    constructor
    · have hm : -(Real.pi / 2 - δ) ≤ ζ.im + min (b - δ) (-ζ.im) := by
        rw [add_min]
        apply le_min <;> linarith [hη.1, Real.pi_pos]
      have ht : min (b - δ) (-ζ.im) ≤ θ := le_max_right _ _
      linarith
    · change ζ.im + max (a + δ) (min (b - δ) (-ζ.im)) ≤ _
      rw [add_max]
      apply max_le
      · linarith [hη.2]
      · have hm : min (b - δ) (-ζ.im) ≤ -ζ.im := min_le_right _ _
        linarith [Real.pi_pos]
  have hcos : γ ≤ Real.cos (ζ.im + θ) := by
    simpa only [Real.cos_abs] using Real.cos_le_cos_of_nonneg_of_le_pi
      (abs_nonneg (ζ.im + θ)) (by linarith [Real.pi_pos]) hphase
  apply Set.mem_iUnion₂.mpr
  refine ⟨θ, ⟨hθa, hθb⟩, ?_⟩
  refine ⟨hphase.trans_lt (by linarith), ?_⟩
  have hexp : σ < Real.exp ζ.re * γ := (div_lt_iff₀ hγ).mp (hR ζ.re hζ)
  calc σ < Real.exp ζ.re * γ := hexp
    _ ≤ Real.exp ζ.re * Real.cos (ζ.im + θ) :=
      mul_le_mul_of_nonneg_left hcos (Real.exp_pos _).le
    _ = (exp (ζ + θ * I)).re := by simp [exp_re]

/-- For a principal power and a ray inside its slit plane, the logarithmic ray transform
is exactly `Γ(α) exp(-αζ)`. This includes continuations across `Im ζ = ±π`. -/
theorem rayLaplace_cpow {α ζ : ℂ} {θ : ℝ} (hα : 0 < α.re)
    (hθ : θ ∈ Ioo (-Real.pi) Real.pi) (hζ : ζ ∈ rayLaplaceDomain 0 θ) :
    rayLaplace (fun w => w ^ (α - 1)) θ ζ = Gamma α * exp (-α * ζ) := by
  have hi : (∫ r in Ioi (0 : ℝ), exp (-(exp (ζ + θ * I) * r)) *
      ((r : ℂ) * exp (θ * I)) ^ (α - 1)) =
      (Gamma α * (exp (ζ + θ * I)) ^ (-α)) * exp (θ * I * (α - 1)) := by
    rw [← integral_cpow_mul_cexp_neg_mul_Ioi hα hζ.2, ← integral_mul_const]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [ofReal_mul_exp_cpow hr hθ.1 hθ.2.le]
    ring
  have hlog : log (exp (ζ + θ * I)) = ζ + θ * I := by
    apply log_exp <;> simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one,
      I_re, mul_zero, sub_zero] <;> linarith [(abs_lt.mp hζ.1).1, (abs_lt.mp hζ.1).2,
        Real.pi_pos]
  unfold rayLaplace
  rw [hi, cpow_def_of_ne_zero (exp_ne_zero _), hlog]
  calc exp (θ * I) * (Gamma α * exp ((ζ + θ * I) * -α) * exp (θ * I * (α - 1))) =
      Gamma α * (exp (θ * I) * exp ((ζ + θ * I) * -α) * exp (θ * I * (α - 1))) := by ring
    _ = Gamma α * exp (θ * I + (ζ + θ * I) * -α + θ * I * (α - 1)) := by
      rw [← exp_add, ← exp_add]
    _ = _ := by congr 2; ring

end Complex
