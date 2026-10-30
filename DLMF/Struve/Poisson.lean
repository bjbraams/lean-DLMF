/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.SeriesAndEquations
public import DLMF.Bessel.Elementary

/-!
# Poisson integrals for the Struve functions

Termwise Beta integration of the Struve series against the Poisson weight
`(1-t²)^(ν-1/2)` on `[0,1]` (DLMF 11.5.1, 11.5.4, 11.5.6):

* `integral_poissonWeight_mul_pow`: the Beta moments `∫₀¹ (1-t²)^(ν-1/2) t^m dt`;
* `hasSum_integral_poissonWeight`: termwise integration of a power series on `[0,1]`;
* `integral_poissonWeight_eq_trig`: the substitution `t = cos θ`;
* `struveH_eq_poisson`, `struveL_eq_poisson`, `struveM_eq_poisson`.

The `I_ν` case reuses `DLMF.Bessel.besselI_eq_poisson_integral`.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory DLMF
open scoped Real Topology Nat Interval

namespace DLMF.Struve


/-- The substitution `x = t²` on `(0,1)`. -/
theorem integral_unit_eq_integral_sq (g : ℝ → ℂ) :
    (∫ x : ℝ in 0..1, g x) = ∫ t : ℝ in 0..1, (2*t:ℂ) * g (t^2) := by
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have himg : (fun t : ℝ => t^2) '' Ioo 0 1 = Ioo 0 1 := by
    ext x; constructor
    · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
      exact ⟨by positivity, by nlinarith⟩
    · rintro ⟨h0, h1⟩
      refine ⟨Real.sqrt x, ⟨Real.sqrt_pos.2 h0, ?_⟩, Real.sq_sqrt h0.le⟩
      rw [Real.sqrt_lt' one_pos]; simpa using h1
  have h := integral_image_eq_integral_abs_deriv_smul (f := fun t : ℝ => t^2)
    (f' := fun t => 2*t) (s := Ioo (0:ℝ) 1) measurableSet_Ioo
    (fun t _ => by simpa using (hasDerivAt_pow 2 t).hasDerivWithinAt)
    (fun a ha b hb hab => by
      simp only at hab
      nlinarith [ha.1, hb.1, sq_nonneg (a-b), sq_nonneg (a+b)]) g
  rw [himg] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  simp only [abs_of_pos (by linarith [ht.1] : (0:ℝ) < 2*t), Complex.real_smul]
  push_cast; ring

/-- The substitution `t = cos θ` on `(0,1)`. -/
theorem integral_unit_eq_integral_cos (g : ℝ → ℂ) :
    (∫ t : ℝ in 0..1, g t) = ∫ θ : ℝ in 0..π/2, (Real.sin θ:ℂ) * g (Real.cos θ) := by
  rw [intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le (by positivity),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have himg : Real.cos '' Ioo 0 (π/2) = Ioo 0 1 := by
    ext x; constructor
    · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
      refine ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩, ?_⟩
      rw [← Real.cos_zero]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two le_rfl h1.le h0
    · rintro ⟨h0, h1⟩
      refine ⟨Real.arccos x, ⟨Real.arccos_pos.2 h1, Real.arccos_lt_pi_div_two.2 h0⟩,
        Real.cos_arccos (by linarith) h1.le⟩
  have h := integral_image_eq_integral_abs_deriv_smul (f := Real.cos)
    (f' := fun t => -Real.sin t) (s := Ioo (0:ℝ) (π/2)) measurableSet_Ioo
    (fun t _ => (Real.hasDerivAt_cos t).hasDerivWithinAt)
    (Real.injOn_cos.mono (fun t (ht : t ∈ Ioo (0:ℝ) (π/2)) =>
      (⟨ht.1.le, by linarith [ht.2, Real.pi_pos]⟩ : t ∈ Icc 0 π))) g
  rw [himg] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  simp only [abs_neg, abs_of_pos hs, Complex.real_smul]


/-- The Poisson weight `(1-t²)^(ν-1/2)` is integrable on `[0,1]` for `Re ν > -1/2`. -/
theorem intervalIntegrable_poissonWeight {ν : ℂ} (hν : -1/2 < ν.re) :
    IntervalIntegrable (fun t : ℝ => (1-(t:ℂ)^2)^(ν-1/2)) volume 0 1 := by
  have h1 : IntervalIntegrable (fun t : ℝ => ((1-t:ℝ):ℂ)^(ν-1/2)) volume 0 1 := by
    have := (intervalIntegral.intervalIntegrable_cpow' (a := 1) (b := 0) (r := ν-1/2)
      (by simp; linarith)).comp_sub_left 1
    simpa using this
  have h2 : ContinuousOn (fun t : ℝ => ((1+t:ℝ):ℂ)^(ν-1/2)) (uIcc 0 1) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    apply ContinuousAt.continuousWithinAt
    have hs : ((1+t:ℝ):ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 (by linarith [ht.1])
    exact (continuous_ofReal.comp (continuous_const.add continuous_id)).continuousAt.cpow
      continuousAt_const hs
  refine (h1.mul_continuousOn h2).congr_uIoo fun t ht => ?_
  rw [uIoo_of_le zero_le_one] at ht
  simp only
  rw [← mul_cpow_ofReal_nonneg (by linarith [ht.2]) (by linarith [ht.1])]
  push_cast; ring_nf

/-- `t · (t²)^((m+1)/2-1) = t^m` for `t > 0`. -/
theorem ofReal_mul_sq_cpow {t : ℝ} (ht : 0 < t) (m : ℕ) :
    (t:ℂ) * ((t^2:ℝ):ℂ)^(((m:ℂ)+1)/2-1) = (t:ℂ)^m := by
  have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
  rw [show t^2 = t*t by ring, ofReal_mul, mul_cpow_ofReal_nonneg ht.le ht.le]
  conv_lhs => arg 1; rw [← cpow_one (t:ℂ)]
  rw [← cpow_add _ _ ht0, ← cpow_add _ _ ht0, ← cpow_natCast]
  congr 1; ring

/-- Beta moments of the Poisson weight. -/
theorem integral_poissonWeight_mul_pow {ν : ℂ} (hν : -1/2 < ν.re) (m : ℕ) :
    (∫ t : ℝ in 0..1, (1-(t:ℂ)^2)^(ν-1/2) * (t:ℂ)^m) =
      Gamma (((m:ℂ)+1)/2) * Gamma (ν+1/2) / (2*Gamma (((m:ℂ)+1)/2+(ν+1/2))) := by
  have hu : 0 < (((m:ℂ)+1)/2).re := by simp; positivity
  have hv : 0 < (ν+1/2).re := by simp; linarith
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral hu hv
  have hG : Gamma (((m:ℂ)+1)/2+(ν+1/2)) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp at hu hv ⊢; linarith)
  rw [hB, mul_comm (2:ℂ), ← div_div, mul_div_cancel_left₀ _ hG, Complex.betaIntegral,
    integral_unit_eq_integral_sq (fun x : ℝ => (x:ℂ)^(((m:ℂ)+1)/2-1) * (1-(x:ℂ))^(ν+1/2-1)),
    ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro t ht
  simp only
  rw [show (2*(t:ℂ)) * ((((t^2:ℝ)):ℂ)^(((m:ℂ)+1)/2-1) * (1-((t^2:ℝ):ℂ))^(ν+1/2-1)) / 2 =
    ((t:ℂ) * ((t^2:ℝ):ℂ)^(((m:ℂ)+1)/2-1)) * (1-((t^2:ℝ):ℂ))^(ν+1/2-1) by ring,
    ofReal_mul_sq_cpow ht.1]
  push_cast; ring_nf


/-- Termwise integration of a power series on `[0,1]` against the Poisson weight. -/
theorem hasSum_integral_poissonWeight {ν : ℂ} (hν : -1/2 < ν.re) (c : ℕ → ℂ)
    (hc : Summable fun k => ‖c k‖) (p : ℕ → ℕ) (f : ℝ → ℂ)
    (hf : ∀ t ∈ Icc (0:ℝ) 1, HasSum (fun k => c k * (t:ℂ)^(p k)) (f t)) :
    HasSum (fun k => c k * ∫ t : ℝ in 0..1, (1-(t:ℂ)^2)^(ν-1/2) * (t:ℂ)^(p k))
      (∫ t : ℝ in 0..1, (1-(t:ℂ)^2)^(ν-1/2) * f t) := by
  have hw := intervalIntegrable_poissonWeight hν
  have hmem : ∀ t ∈ uIoc (0:ℝ) 1, t ∈ Icc (0:ℝ) 1 := fun t ht => by
    rw [uIoc_of_le zero_le_one] at ht; exact ⟨ht.1.le, ht.2⟩
  simp_rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun k t => ‖(1-(t:ℂ)^2)^(ν-1/2)‖ * ‖c k‖) (fun k => ?_) (fun k => ?_) ?_ ?_ ?_
  · have : IntervalIntegrable (fun t : ℝ => c k * ((1-(t:ℂ)^2)^(ν-1/2) * (t:ℂ)^(p k)))
        volume 0 1 :=
      (hw.mul_continuousOn (by fun_prop : Continuous fun t : ℝ => (t:ℂ)^(p k)).continuousOn
        ).const_mul _
    exact this.def'.aestronglyMeasurable
  · refine Eventually.of_forall fun t ht => ?_
    have ht' := hmem t ht
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht'.1]
    have : t^(p k) ≤ 1 := pow_le_one₀ ht'.1 ht'.2
    have h0 := norm_nonneg ((1-(t:ℂ)^2)^(ν-1/2))
    have h1 := norm_nonneg (c k)
    nlinarith [mul_nonneg h0 h1]
  · exact Eventually.of_forall fun t _ => hc.mul_left _
  · simp_rw [tsum_mul_left]
    exact hw.norm.mul_const _
  · refine Eventually.of_forall fun t ht => ?_
    refine ((hf t (hmem t ht)).mul_left ((1-(t:ℂ)^2)^(ν-1/2))).congr_fun fun k => ?_
    ring


/-- `(2k+1)! = (2k+1)!! 2^k k!`. -/
theorem factorial_odd_eq_oddProduct (k : ℕ) :
    (((2*k+1)! : ℕ) : ℂ) = oddProduct k * 2^k * (k ! : ℂ) := by
  induction k with
  | zero => simp [oddProduct]
  | succ k ih =>
    rw [show 2*(k+1)+1 = (2*k+1)+1+1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ k]
    push_cast
    rw [ih]
    simp only [oddProduct, Finset.prod_range_succ]
    push_cast; ring

/-- Odd Beta moments of the Poisson weight. -/
theorem integral_poissonWeight_mul_odd_pow {ν : ℂ} (hν : -1/2 < ν.re) (k : ℕ) :
    (∫ t : ℝ in 0..1, (1-(t:ℂ)^2)^(ν-1/2) * (t:ℂ)^(2*k+1)) =
      k ! * Gamma (ν+1/2) / (2*Gamma (k+ν+3/2)) := by
  rw [integral_poissonWeight_mul_pow hν]
  rw [show (((2*k+1 : ℕ):ℂ)+1)/2 = (k:ℂ)+1 by push_cast; ring, Complex.Gamma_nat_eq_factorial,
    show (k:ℂ)+1+(ν+1/2) = k+ν+3/2 by ring]

/-- Summability of odd exponential coefficients. -/
theorem summable_norm_odd_div_factorial (z : ℂ) :
    Summable fun k : ℕ => ‖z‖^(2*k+1) / ((2*k+1)! : ℝ) := by
  have h := Real.summable_pow_div_factorial ‖z‖
  exact h.comp_injective (i := fun k : ℕ => 2*k+1) (fun a b h => by simp only at h; omega)

/-- **Poisson's integral for `H_ν`** (core computation). -/
theorem struveH_eq_poisson {ν : ℂ} (hν : -1/2 < ν.re) {z : ℂ} (hz : z ≠ 0) :
    struveH ν z = 2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) *
      ∫ t : ℝ in 0..1, (1-(t:ℂ)^2)^(ν-1/2)*sin (z*t) := by
  set c : ℕ → ℂ := fun k => (-1)^k * z^(2*k+1) / ((2*k+1)! : ℂ)
  have hc : Summable fun k => ‖c k‖ := by
    refine (summable_norm_odd_div_factorial z).congr fun k => ?_
    simp [c, norm_pow]
  have hS := hasSum_integral_poissonWeight hν c hc (fun k => 2*k+1) (fun t => sin (z*t))
    (fun t _ => by
      refine (Complex.hasSum_sin (z*t)).congr_fun fun k => ?_
      simp only [c]; ring)
  simp_rw [integral_poissonWeight_mul_odd_pow hν] at hS
  have hv : 0 < (ν+1/2).re := by simp; linarith
  have hΓ : Gamma (ν+1/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hv
  have hP : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hz2 : z/2 ≠ 0 := div_ne_zero hz two_ne_zero
  have hH : HasSum (fun k : ℕ => 2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) *
      (c k * (k ! * Gamma (ν+1/2) / (2*Gamma (k+ν+3/2))))) (struveH ν z) := by
    rw [struveH]
    refine ((hasSum_struveHCore ν z).mul_left ((z/2)^(ν+1))).congr_fun fun k => ?_
    have ho : oddProduct k ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      have : (0:ℝ) < 2*j+1 := by positivity
      exact_mod_cast this.ne'
    have hf : ((k ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
    simp only [c, struveCoeff, Gamma_oddProduct]
    rw [factorial_odd_eq_oddProduct, cpow_add _ _ hz2, cpow_one,
      div_pow z 2 (2*k)]
    have hk : Gamma ((k:ℂ)+ν+3/2) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])
    generalize Gamma (ν+1/2) = G at hΓ ⊢
    generalize Gamma ((k:ℂ)+ν+3/2) = G2 at hk ⊢
    generalize (z/2)^ν = P
    field_simp
    ring
  exact (hH.unique (hS.mul_left _)).trans rfl


/-- **Poisson's integral for `L_ν`** (core computation). -/
theorem struveL_eq_poisson {ν : ℂ} (hν : -1/2 < ν.re) {z : ℂ} (hz : z ≠ 0) :
    struveL ν z = 2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) *
      ∫ t : ℝ in 0..1, (1-(t:ℂ)^2)^(ν-1/2)*sinh (z*t) := by
  set c : ℕ → ℂ := fun k => z^(2*k+1) / ((2*k+1)! : ℂ)
  have hc : Summable fun k => ‖c k‖ := by
    refine (summable_norm_odd_div_factorial z).congr fun k => ?_
    simp [c, norm_pow]
  have hS := hasSum_integral_poissonWeight hν c hc (fun k => 2*k+1) (fun t => sinh (z*t))
    (fun t _ => by
      refine (Complex.hasSum_sinh (z*t)).congr_fun fun k => ?_
      simp only [c]; ring)
  simp_rw [integral_poissonWeight_mul_odd_pow hν] at hS
  have hv : 0 < (ν+1/2).re := by simp; linarith
  have hΓ : Gamma (ν+1/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hv
  have hP : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hz2 : z/2 ≠ 0 := div_ne_zero hz two_ne_zero
  have hH : HasSum (fun k : ℕ => 2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) *
      (c k * (k ! * Gamma (ν+1/2) / (2*Gamma (k+ν+3/2))))) (struveL ν z) := by
    rw [struveL]
    refine ((hasSum_struveLCore ν z).mul_left ((z/2)^(ν+1))).congr_fun fun k => ?_
    have ho : oddProduct k ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      have : (0:ℝ) < 2*j+1 := by positivity
      exact_mod_cast this.ne'
    have hf : ((k ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
    simp only [c, struveCoeff, Gamma_oddProduct]
    rw [factorial_odd_eq_oddProduct, cpow_add _ _ hz2, cpow_one,
      div_pow z 2 (2*k)]
    have hk : Gamma ((k:ℂ)+ν+3/2) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])
    generalize Gamma (ν+1/2) = G at hΓ ⊢
    generalize Gamma ((k:ℂ)+ν+3/2) = G2 at hk ⊢
    generalize (z/2)^ν = P
    field_simp
    ring
  exact (hH.unique (hS.mul_left _)).trans rfl

/-- `t · (t²)^w = t^(2w+1)` for `t > 0`. -/
theorem ofReal_mul_sq_cpow' {t : ℝ} (ht : 0 < t) (w : ℂ) :
    (t:ℂ) * ((t^2:ℝ):ℂ)^w = (t:ℂ)^(2*w+1) := by
  have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
  rw [show t^2 = t*t by ring, ofReal_mul, mul_cpow_ofReal_nonneg ht.le ht.le]
  conv_lhs => arg 1; rw [← cpow_one (t:ℂ)]
  rw [← cpow_add _ _ ht0, ← cpow_add _ _ ht0]
  congr 1; ring

/-- The Poisson weight in trigonometric form: `t = cos θ`. -/
theorem integral_poissonWeight_eq_trig (ν : ℂ) (f : ℝ → ℂ) :
    (∫ t : ℝ in 0..1, (1-(t:ℂ)^2)^(ν-1/2) * f t) =
      ∫ θ : ℝ in 0..π/2, f (Real.cos θ) * (Real.sin θ : ℂ)^(2*ν) := by
  rw [integral_unit_eq_integral_cos]
  apply intervalIntegral.integral_congr_Ioo_of_le (by positivity)
  intro θ hθ
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h1 : 1 - ((Real.cos θ:ℝ):ℂ)^2 = ((Real.sin θ^2:ℝ):ℂ) := by
    have := Real.sin_sq_add_cos_sq θ
    rw [show Real.sin θ^2 = 1 - Real.cos θ^2 by linarith]; push_cast; ring
  simp only
  rw [h1, show ∀ (a b c : ℂ), a * (b * c) = c * (a * b) from fun a b c => by ring,
    ofReal_mul_sq_cpow' hs]
  congr 2; ring


/-- Poisson-type integral for `M_ν`, from Poisson's integrals for `L_ν` and `I_ν`. -/
theorem struveM_eq_poisson {ν : ℂ} (hν : -1/2 < ν.re) {z : ℂ} (hz : z ∈ slitPlane) :
    struveM ν z = -2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) * ∫ t : ℝ in 0..1, exp (-z*t)*(1-t^2:ℂ)^(ν-1/2) := by
  have hz0 := slitPlane_ne_zero hz
  have hw := intervalIntegrable_poissonWeight hν
  have hI := DLMF.Bessel.besselI_eq_poisson_integral hν hz
  have hL := struveL_eq_poisson hν hz0
  set w : ℝ → ℂ := fun t => (1-(t:ℂ)^2)^(ν-1/2)
  have hp : IntervalIntegrable (fun t : ℝ => w t * exp (z*t)) volume 0 1 :=
    hw.mul_continuousOn (by fun_prop : Continuous fun t : ℝ => exp (z*t)).continuousOn
  have hm : IntervalIntegrable (fun t : ℝ => w t * exp (-z*t)) volume 0 1 :=
    hw.mul_continuousOn (by fun_prop : Continuous fun t : ℝ => exp (-z*t)).continuousOn
  have hneg : (∫ t : ℝ in (-1:ℝ)..0, w t * exp (z*t)) = ∫ t : ℝ in 0..1, w t * exp (-z*t) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := 1)
      (fun t : ℝ => w t * exp (z*t))
    simp only [neg_zero] at this
    rw [← this]
    apply intervalIntegral.integral_congr fun t _ => ?_
    simp only [w]; push_cast; ring_nf
  have hneg_int : IntervalIntegrable (fun t : ℝ => w t * exp (z*t)) volume (-1) 0 := by
    have := (IntervalIntegrable.iff_comp_neg (by simp)).mp hm
    simp only [neg_zero] at this
    refine (this.symm).congr fun t _ => ?_
    simp only [w]; push_cast; ring_nf
  have hsplit : (∫ t : ℝ in (-1:ℝ)..1, (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) * exp (z * t)) =
      (∫ t : ℝ in 0..1, w t * exp (-z*t)) + ∫ t : ℝ in 0..1, w t * exp (z*t) := by
    rw [← hneg]
    exact (intervalIntegral.integral_add_adjacent_intervals hneg_int hp).symm
  have hsinh : (∫ t : ℝ in 0..1, w t * sinh (z*t)) =
      ((∫ t : ℝ in 0..1, w t * exp (z*t)) - ∫ t : ℝ in 0..1, w t * exp (-z*t)) / 2 := by
    rw [← intervalIntegral.integral_sub hp hm, ← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr fun t _ => ?_
    simp only [Complex.sinh, neg_mul]; ring
  rw [struveM, hL, hI, hsplit]
  change 2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) * (∫ t : ℝ in 0..1, w t * sinh (z*t)) - _ = _
  rw [hsinh]
  have : (∫ t : ℝ in 0..1, exp (-z*t)*(1-t^2:ℂ)^(ν-1/2)) = ∫ t : ℝ in 0..1, w t * exp (-z*t) :=
    intervalIntegral.integral_congr fun t _ => by simp only [w]; ring
  rw [this]
  ring

end DLMF.Struve
