/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.Integrals

/-!
# Voigt functions and their properties, DLMF §7.19

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- Voigt U for t>0. -/
@[dlmf 7.19.E1]
def Real.voigtU (x t : ℝ) : ℝ :=
  1/Real.sqrt (4*π*t)*(∫ y : ℝ, Real.exp (-(x-y)^2/(4*t))/(1+y^2))

/-- Voigt V for t>0. -/
@[dlmf 7.19.E2]
def Real.voigtV (x t : ℝ) : ℝ :=
  1/Real.sqrt (4*π*t)*(∫ y : ℝ, y*Real.exp (-(x-y)^2/(4*t))/(1+y^2))

/-- Voigt line-broadening profile for a>0. -/
@[dlmf 7.19.E4]
def Real.voigtH (a u : ℝ) : ℝ :=
  a/π*(∫ t : ℝ, Real.exp (-t^2)/((u-t)^2+a^2))

/-- The shifted Gaussian kernel of the Voigt functions is integrable. -/
theorem integrable_voigt_kernel (x : ℝ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun y : ℝ => Real.exp (-(x-y)^2/(4*t))) := by
  have h := (integrable_exp_neg_mul_sq (b := 1/(4*t)) (by positivity)).comp_sub_left x
  refine h.congr (ae_of_all _ fun y => ?_)
  simp only
  congr 1; ring

/-- The total mass of the shifted Voigt Gaussian kernel. -/
theorem integral_voigt_kernel (x t : ℝ) :
    (∫ y : ℝ, Real.exp (-(x-y)^2/(4*t))) = Real.sqrt (4*π*t) := by
  have h := integral_sub_left_eq_self (fun y : ℝ => Real.exp (-(1/(4*t))*y^2)) (μ := volume) x
  have hg := integral_gaussian (1/(4*t))
  rw [show π/(1/(4*t)) = 4*π*t by field_simp] at hg
  rw [← hg, ← h]
  congr 1; funext y; congr 1; ring

/-- The Gaussian Fourier transform used for the Voigt functions. -/
theorem integral_voigt_kernel_fourier (x : ℝ) {t : ℝ} (ht : 0 < t) (s : ℝ) :
    (∫ y : ℝ, (Real.exp (-(x-y)^2/(4*t)) : ℂ) * exp (-(s:ℂ)*(1-I*y))) =
      Real.sqrt (4*π*t) * exp (-(s:ℂ)*(1-I*x) - t*(s:ℂ)^2) := by
  have hb : ((-1/(4*t):ℝ):ℂ).re < 0 := by
    rw [ofReal_re]; have : 0 < 1/(4*t) := by positivity
    linarith [show -1/(4*t) = -(1/(4*t)) by ring]
  have h := integral_cexp_quadratic hb ((x/(2*t):ℝ) + I*s) ((-x^2/(4*t) - s:ℝ))
  have hpt : (fun y : ℝ => (Real.exp (-(x-y)^2/(4*t)) : ℂ) * exp (-(s:ℂ)*(1-I*y))) =
      fun y : ℝ => cexp (((-1/(4*t):ℝ):ℂ) * y^2 + (((x/(2*t):ℝ):ℂ) + I*s) * y + ((-x^2/(4*t) - s:ℝ):ℂ)) := by
    funext y
    rw [ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [hpt, h]
  have hπ : (π:ℂ)/(-((-1/(4*t):ℝ):ℂ)) = ((4*π*t:ℝ):ℂ) := by
    push_cast; field_simp
  rw [hπ, show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
    ← Real.sqrt_eq_rpow]
  have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  congr 1
  congr 1
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring
/-- Laplace representation of the Voigt functions,
`U + iV = ∫₀^∞ exp (-s(1 - ix) - t s²) ds`, by Fubini. -/
theorem voigt_laplace (x : ℝ) {t : ℝ} (ht : 0 < t) :
    (Real.voigtU x t : ℂ) + I*Real.voigtV x t =
      ∫ s : ℝ in Ioi 0, exp (-(s:ℂ)*(1-I*x) - t*(s:ℂ)^2) := by
  set k : ℝ → ℝ := fun y => Real.exp (-(x-y)^2/(4*t)) with hk
  have hkint : Integrable k := integrable_voigt_kernel x ht
  have hs : 0 < Real.sqrt (4*π*t) := Real.sqrt_pos.mpr (by positivity)
  have hy1 (y : ℝ) : 0 < 1+y^2 := by positivity
  have hU : Integrable (fun y : ℝ => k y/(1+y^2)) := by
    refine hkint.mono' ((Continuous.div (by fun_prop) (by fun_prop)
      (fun y => (hy1 y).ne')).aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) (hy1 y))]
    exact div_le_self (Real.exp_pos _).le (by nlinarith [sq_nonneg y])
  have hV : Integrable (fun y : ℝ => y*k y/(1+y^2)) := by
    refine hkint.mono' ((Continuous.div (by fun_prop) (by fun_prop)
      (fun y => (hy1 y).ne')).aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (hy1 y),
      div_le_iff₀ (hy1 y)]
    have : |y| ≤ 1+y^2 := by nlinarith [abs_nonneg y, sq_abs y, sq_nonneg (|y|-1)]
    nlinarith [Real.exp_pos (-(x-y)^2/(4*t))]
  -- step 1
  have h1 : (Real.voigtU x t : ℂ) + I*Real.voigtV x t =
      (1/Real.sqrt (4*π*t):ℝ) * ∫ y : ℝ, (k y : ℂ) * (1-I*y)⁻¹ := by
    have eU : (Real.voigtU x t : ℂ) = ((1/Real.sqrt (4*π*t):ℝ):ℂ) *
        ∫ y : ℝ, ((k y/(1+y^2) : ℝ) : ℂ) := by
      rw [Real.voigtU, ofReal_mul, integral_complex_ofReal]
    have eV : (Real.voigtV x t : ℂ) = ((1/Real.sqrt (4*π*t):ℝ):ℂ) *
        ∫ y : ℝ, ((y*k y/(1+y^2) : ℝ) : ℂ) := by
      rw [Real.voigtV, ofReal_mul, integral_complex_ofReal]
    rw [eU, eV, show ∀ c A B : ℂ, c*A + I*(c*B) = c*(A + I*B) by intros; ring,
      ← integral_const_mul, ← integral_add (f := fun y : ℝ => ((k y/(1+y^2) : ℝ) : ℂ)) ?_ ?_]
    rotate_left
    · exact hU.ofReal
    · exact hV.ofReal.const_mul I
    congr 1
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    have h1 : (1 - I*(y:ℂ)) ≠ 0 := by
      intro h; have := congrArg re h; simp at this
    have h2 : (1+(y:ℂ)^2) ≠ 0 := by exact_mod_cast (hy1 y).ne'
    have hf : (1+(y:ℂ)^2) = (1-I*y)*(1+I*y) := by ring_nf; rw [I_sq]; ring
    have hinv : (1-I*(y:ℂ))⁻¹ = (1+I*y)/(1+(y:ℂ)^2) := by
      rw [eq_div_iff h2, hf, ← mul_assoc, inv_mul_cancel₀ h1, one_mul]
    simp only; rw [hinv]
    push_cast
    field_simp
  -- step 2
  have h2 (y : ℝ) : (1-I*(y:ℂ))⁻¹ = ∫ s : ℝ in Ioi 0, exp (-(s:ℂ)*(1-I*y)) := by
    have := integral_exp_mul_complex_Ioi (a := -(1-I*y)) (by simp) 0
    simp only [ofReal_zero, mul_zero, Complex.exp_zero] at this
    rw [show (fun s : ℝ => exp (-(s:ℂ)*(1-I*y))) = fun s : ℝ => exp (-(1-I*y)*s) by
      funext s; ring_nf]
    rw [this]; field_simp
  -- step 3: Fubini
  have hprod : Integrable (Function.uncurry fun (y : ℝ) (s : ℝ) =>
      (k y : ℂ) * exp (-(s:ℂ)*(1-I*y))) (volume.prod (volume.restrict (Ioi 0))) := by
    have hg := hkint.mul_prod (exp_neg_integrableOn_Ioi 0 one_pos)
    refine hg.mono' ?_ (ae_of_all _ fun p => ?_)
    · exact (Continuous.aestronglyMeasurable (by fun_prop))
    · change ‖(k p.1 : ℂ) * exp (-(p.2:ℂ)*(1-I*p.1))‖ ≤ k p.1 * Real.exp (-1*p.2)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_exp]
      apply le_of_eq; congr 2; simp
  have h3 : (∫ y : ℝ, (k y : ℂ) * (1-I*y)⁻¹) =
      ∫ s : ℝ in Ioi 0, ∫ y : ℝ, (k y : ℂ) * exp (-(s:ℂ)*(1-I*y)) := by
    simp_rw [h2, ← integral_const_mul]
    exact integral_integral_swap hprod
  rw [h1, h3]
  simp_rw [hk, integral_voigt_kernel_fourier x ht]
  rw [integral_const_mul, ← mul_assoc]
  have : ((1/Real.sqrt (4*π*t):ℝ):ℂ) * Real.sqrt (4*π*t) = 1 := by
    rw [← ofReal_mul]; field_simp; simp
  rw [this, one_mul]
/-- The Voigt functions at `(u/a, 1/(4a²))` as one complex Laplace–Fourier integral. -/
theorem voigt_fourier_laplace_complex {a : ℝ} (ha : 0 < a) (u : ℝ) :
    (Real.voigtU (u/a) (1/(4*a^2)) : ℂ) + I*Real.voigtV (u/a) (1/(4*a^2)) =
      a * ∫ τ : ℝ in Ioi 0, exp ((-a*τ-τ^2/4 : ℝ) + (u*τ:ℝ)*I) := by
  rw [voigt_laplace (u/a) (t := 1/(4*a^2)) (by positivity)]
  set G : ℝ → ℂ := fun s => exp (-(s:ℂ)*(1-I*((u/a:ℝ):ℂ)) - ((1/(4*a^2):ℝ):ℂ)*(s:ℂ)^2)
  have hsub := integral_comp_mul_left_Ioi' G 0 ha
  rw [mul_zero] at hsub
  have hG (τ : ℝ) : G (a*τ) = exp ((-a*τ-τ^2/4 : ℝ) + (u*τ:ℝ)*I) := by
    have ha0 : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    simp only [G]; congr 1; push_cast; field_simp; ring
  simp_rw [hG] at hsub
  rw [← hsub, real_smul]

/-- Integrability of the Voigt Laplace–Fourier integrand. -/
theorem integrableOn_voigt_fourier_laplace {a : ℝ} (ha : 0 < a) (u : ℝ) :
    IntegrableOn (fun τ : ℝ => exp ((-a*τ-τ^2/4 : ℝ) + (u*τ:ℝ)*I)) (Ioi 0) := by
  refine Integrable.mono' (exp_neg_integrableOn_Ioi 0 ha) (Continuous.aestronglyMeasurable
    (by fun_prop)) ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ => ?_))
  rw [Complex.norm_exp]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, add_zero, sub_self]
  rw [Real.exp_le_exp]
  nlinarith [sq_nonneg τ]

/-- `∫₀^∞ exp (-s (1 - i y)) ds = (1 - i y)⁻¹`. -/
theorem integral_exp_neg_mul_one_sub_I_mul (y : ℝ) :
    (∫ s : ℝ in Ioi 0, exp (-(s:ℂ)*(1-I*y))) = (1-I*(y:ℂ))⁻¹ := by
  have := integral_exp_mul_complex_Ioi (a := -(1-I*y)) (by simp) 0
  simp only [ofReal_zero, mul_zero, Complex.exp_zero] at this
  rw [show (fun s : ℝ => exp (-(s:ℂ)*(1-I*y))) = fun s : ℝ => exp (-(1-I*y)*s) by
    funext s; ring_nf]
  rw [this]; field_simp

/-- Differentiation and integration by parts for the Voigt Laplace integral
`W(x) = ∫₀^∞ exp (-s(1 - ix) - t s²) ds`: `W' = i J` and `(1 - ix) W + 2t J = 1`,
where `J = ∫₀^∞ s exp (-s(1 - ix) - t s²) ds`. -/
theorem voigt_laplace_deriv (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => ∫ s : ℝ in Ioi 0, exp (-(s:ℂ)*(1-I*x) - t*(s:ℂ)^2))
      (I * ∫ s : ℝ in Ioi 0, (s:ℂ) * exp (-(s:ℂ)*(1-I*x) - t*(s:ℂ)^2)) x ∧
    (1-I*x) * (∫ s : ℝ in Ioi 0, exp (-(s:ℂ)*(1-I*x) - t*(s:ℂ)^2)) +
      2*t*(∫ s : ℝ in Ioi 0, (s:ℂ) * exp (-(s:ℂ)*(1-I*x) - t*(s:ℂ)^2)) = 1 := by
  set e : ℝ → ℝ → ℂ := fun x s => exp (-(s:ℂ)*(1-I*x) - t*(s:ℂ)^2) with he
  have hne (x s : ℝ) (hs : 0 ≤ s) : ‖e x s‖ ≤ Real.exp (-1*s) := by
    rw [he, Complex.norm_exp, Real.exp_le_exp]
    have : (-(s:ℂ)*(1-I*x) - t*(s:ℂ)^2).re = -s - t*s^2 := by simp [← ofReal_pow]
    rw [this]; nlinarith [sq_nonneg s]
  have hb1 : IntegrableOn (fun s : ℝ => s * Real.exp (-1*s)) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := 1) (by norm_num)
      one_pos one_pos
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp [Real.rpow_one]
  have hb0 : IntegrableOn (fun s : ℝ => Real.exp (-1*s)) (Ioi 0) := exp_neg_integrableOn_Ioi 0 one_pos
  have hint0 (x : ℝ) : IntegrableOn (e x) (Ioi 0) :=
    hb0.mono' (Continuous.aestronglyMeasurable (by fun_prop))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => hne x s (le_of_lt hs)))
  have hint1 (x : ℝ) : IntegrableOn (fun s : ℝ => (s:ℂ) * e x s) (Ioi 0) := by
    refine hb1.mono' (Continuous.aestronglyMeasurable (by fun_prop))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_))
    have hs : (0:ℝ) < s := hs
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
    exact mul_le_mul_of_nonneg_left (hne x s hs.le) hs.le
  constructor
  · have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
      (F := e) (F' := fun x s => I*(s:ℂ)*e x s) (x₀ := x) (bound := fun s => s * Real.exp (-1*s))
      Filter.univ_mem (Eventually.of_forall fun x => (hint0 x).aestronglyMeasurable) (hint0 x)
      (Continuous.aestronglyMeasurable (by fun_prop)) ?_ hb1 ?_
    · simp only [he] at hd ⊢
      rw [← integral_const_mul]
      convert hd.2 using 2
      funext s; ring
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs y _ => ?_)
      have hs : (0:ℝ) < s := hs
      rw [norm_mul, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
      exact mul_le_mul_of_nonneg_left (hne y s hs.le) hs.le
    · refine Eventually.of_forall fun s y _ => ?_
      have hin : HasDerivAt (fun y : ℝ => -(s:ℂ)*(1-I*(y:ℂ)) - t*(s:ℂ)^2) (I*s) y := by
        have := (((hasDerivAt_id (y:ℂ)).const_mul (I*s)).comp_ofReal).add_const (-(s:ℂ) - t*(s:ℂ)^2)
        convert this using 1
        · funext y; simp only [id]; ring
        · simp
      exact hin.cexp.congr_deriv (by ring)
  · -- integration by parts
    have hG (s : ℝ) : HasDerivAt (fun s : ℝ => -e x s) ((1-I*(x:ℂ) + 2*t*s) * e x s) s := by
      have hin : HasDerivAt (fun s : ℝ => -(s:ℂ)*(1-I*(x:ℂ)) - t*(s:ℂ)^2)
          (-(1-I*(x:ℂ)) - 2*t*s) s := by
        have := (((hasDerivAt_id (s:ℂ)).const_mul (-(1-I*(x:ℂ)))).sub
          (((hasDerivAt_id (s:ℂ)).pow 2).const_mul (t:ℂ))).comp_ofReal
        convert this using 1
        · funext r; simp only [id, Pi.sub_apply, Pi.pow_apply]; ring
        · simp; ring
      exact hin.cexp.neg.congr_deriv (by simp only [he]; ring)
    have hGlim : Tendsto (fun s : ℝ => -e x s) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_
        (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-1:ℝ) < 0)))
      filter_upwards [eventually_ge_atTop 0] with s hs
      rw [norm_neg]; exact hne x s hs
    have hint2 : IntegrableOn (fun s : ℝ => (1-I*(x:ℂ) + 2*t*s) * e x s) (Ioi 0) := by
      have := ((hint0 x).const_mul (1-I*(x:ℂ))).add ((hint1 x).const_mul (2*t:ℂ))
      refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
      simp only [Pi.add_apply]; ring
    have h := integral_Ioi_of_hasDerivAt_of_tendsto (hG 0).continuousAt.continuousWithinAt
      (fun s _ => hG s) hint2 hGlim
    have he0 : e x 0 = 1 := by simp [he]
    rw [he0] at h
    have hsplit : (∫ s : ℝ in Ioi 0, (1-I*(x:ℂ) + 2*t*s) * e x s) =
        (1-I*(x:ℂ)) * (∫ s : ℝ in Ioi 0, e x s) + 2*t*(∫ s : ℝ in Ioi 0, (s:ℂ) * e x s) := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hint0 x).const_mul (1-I*(x:ℂ)))
        ((hint1 x).const_mul (2*t:ℂ))]
      congr 1; funext s; ring
    rw [hsplit, zero_sub, neg_neg] at h
    exact h
/-- Derivatives of the Voigt functions in `x` from the Laplace representation. -/
theorem hasDerivAt_voigt (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => Real.voigtU u t)
      (-(∫ s : ℝ in Ioi 0, (s:ℂ) * exp (-(s:ℂ)*(1-I*x) - t*(s:ℂ)^2)).im) x ∧
    HasDerivAt (fun u => Real.voigtV u t)
      ((∫ s : ℝ in Ioi 0, (s:ℂ) * exp (-(s:ℂ)*(1-I*x) - t*(s:ℂ)^2)).re) x := by
  have hd := (voigt_laplace_deriv x ht).1
  have hU : (fun u => Real.voigtU u t) = fun u : ℝ => Complex.reCLM
      (∫ s : ℝ in Ioi 0, exp (-(s:ℂ)*(1-I*(u:ℂ)) - t*(s:ℂ)^2)) := by
    funext u; rw [Complex.reCLM_apply, ← voigt_laplace u ht]; simp
  have hV : (fun u => Real.voigtV u t) = fun u : ℝ => Complex.imCLM
      (∫ s : ℝ in Ioi 0, exp (-(s:ℂ)*(1-I*(u:ℂ)) - t*(s:ℂ)^2)) := by
    funext u; rw [Complex.imCLM_apply, ← voigt_laplace u ht]; simp
  set J := ∫ s : ℝ in Ioi 0, (s:ℂ) * exp (-(s:ℂ)*(1-I*x) - t*(s:ℂ)^2)
  constructor
  · rw [hU]
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd).congr_deriv (by simp)
  · rw [hV]
    exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd).congr_deriv (by simp)

/-- voigt erfc. -/
@[dlmf 7.19.E3]
theorem voigt_erfc (x : ℝ) {t : ℝ} (ht : 0 < t) :
    (Real.voigtU x t : ℂ)+I*Real.voigtV x t=(π/(4*t : ℂ))^(1/2 : ℂ)*exp (((1-I*x)/(2*Real.sqrt t))^2)*erfc ((1-I*x)/(2*Real.sqrt t)) := by
  rw [voigt_laplace x ht]
  have h := gaussian_quadratic_tail (a := (t:ℂ)) (by simpa using ht) ((1-I*x)/2) 0 0
  have hi : (fun s : ℝ => exp (-(s:ℂ)*(1-I*x) - t*(s:ℂ)^2)) =
      fun s : ℝ => exp (-((t:ℂ)*(s:ℂ)^2+2*((1-I*x)/2)*s+0)) := by
    funext s; congr 1; ring
  have hst : (t:ℂ)^(1/2:ℂ) = Real.sqrt t := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring, ← ofReal_cpow ht.le, Real.sqrt_eq_rpow]
  have hs0 : (Real.sqrt t:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
  have hss : (Real.sqrt t:ℂ)^2 = t := by exact_mod_cast Real.sq_sqrt ht.le
  have hr : Real.sqrt (π/(4*t)) = Real.sqrt (π/t)/2 := by
    rw [show π/(4*t) = (π/t)/2^2 by ring, Real.sqrt_div' (π/t) (by norm_num : (0:ℝ) ≤ 2^2),
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have hpi : (π/(t:ℂ))^(1/2:ℂ)/2 = (π/(4*t : ℂ))^(1/2 : ℂ) := by
    rw [show (π/(t:ℂ)) = ((π/t:ℝ):ℂ) by push_cast; ring, show (π/(4*t:ℂ)) = ((π/(4*t):ℝ):ℂ) by
      push_cast; ring, show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring,
      ← ofReal_cpow (div_pos Real.pi_pos ht).le, ← ofReal_cpow (div_pos Real.pi_pos (by linarith)).le,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hr]
    push_cast; ring
  rw [hi, h, hst, hpi]
  congr 2
  · congr 1; simp only [mul_zero, sub_zero]; rw [div_pow (1-I*(x:ℂ)) (2*_), mul_pow, hss]; field_simp
  · rw [ofReal_zero, mul_zero, zero_add, div_div]

/-- Real.voigtH eq voigtU. -/
@[dlmf 7.19.E4]
theorem Real.voigtH_eq_voigtU {a : ℝ} (ha : 0 < a) (u : ℝ) :
    Real.voigtH a u=Real.voigtU (u/a) (1/(4*a^2))/(a*Real.sqrt π) := by
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  let F : ℝ → ℝ := fun t => Real.exp (-t^2)/((u-t)^2+a^2)
  have h1 : (∫ y : ℝ, F (u - a*y)) = a⁻¹ * ∫ t : ℝ, F t := by
    have := Measure.integral_comp_mul_left (fun s => F (u - s)) a
    rw [this, integral_sub_left_eq_self (fun s => F s), abs_inv, abs_of_pos ha, smul_eq_mul]
  have hU : Real.voigtU (u/a) (1/(4*a^2)) = a^3/Real.sqrt π * ∫ y : ℝ, F (u - a*y) := by
    rw [Real.voigtU, ← integral_const_mul, ← integral_const_mul]
    have hs : Real.sqrt (4*π*(1/(4*a^2))) = Real.sqrt π/a := by
      rw [show 4*π*(1/(4*a^2)) = π/a^2 by field_simp, Real.sqrt_div' _ (sq_nonneg a),
        Real.sqrt_sq ha.le]
    rw [hs]
    congr 1; funext y
    simp only [F]
    have hd : (u - (u - a*y))^2+a^2 = a^2*(1+y^2) := by ring
    have he : -(u/a-y)^2/(4*(1/(4*a^2))) = -(u-a*y)^2 := by field_simp
    rw [hd, he]
    field_simp
  rw [Real.voigtH, hU, h1]
  simp only [F]
  field_simp
  rw [Real.sq_sqrt Real.pi_pos.le]
  ring

/-- Real.voigt limits. -/
@[dlmf 7.19.E5]
theorem Real.voigt_limits (x : ℝ) :
    Tendsto (Real.voigtU x) (𝓝[>] 0) (𝓝 (1/(1+x^2))) ∧ Tendsto (Real.voigtV x) (𝓝[>] 0) (𝓝 (x/(1+x^2))) := by
  have hW : Tendsto (fun t : ℝ => ∫ s : ℝ in Ioi 0, exp (-(s:ℂ)*(1-I*x) - t*(s:ℂ)^2))
      (𝓝[>] 0) (𝓝 (1-I*(x:ℂ))⁻¹) := by
    rw [← integral_exp_neg_mul_one_sub_I_mul]
    refine tendsto_integral_filter_of_dominated_convergence (fun s => Real.exp (-1*s)) ?_ ?_
      (exp_neg_integrableOn_Ioi 0 one_pos) ?_
    · exact Eventually.of_forall fun t => (Continuous.aestronglyMeasurable (by fun_prop))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
      have ht : (0:ℝ) < t := ht
      rw [Complex.norm_exp, Real.exp_le_exp]
      have : (-(s:ℂ)*(1-I*x) - t*(s:ℂ)^2).re = -s - t*s^2 := by simp [← ofReal_pow]
      rw [this]; nlinarith [sq_nonneg s]
    · refine Eventually.of_forall fun s => ?_
      have : Continuous fun t : ℝ => exp (-(s:ℂ)*(1-I*x) - t*(s:ℂ)^2) := by fun_prop
      have h := this.tendsto 0
      simp only [ofReal_zero, zero_mul, sub_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
  have h1 : (1-I*(x:ℂ)) ≠ 0 := by intro h; have := congrArg re h; simp at this
  have h2 : (1+(x:ℂ)^2) ≠ 0 := by exact_mod_cast (show (0:ℝ) < 1+x^2 by positivity).ne'
  have hinv : (1-I*(x:ℂ))⁻¹ = ((1/(1+x^2):ℝ):ℂ) + I*((x/(1+x^2):ℝ):ℂ) := by
    have hf : (1+(x:ℂ)^2) = (1-I*x)*(1+I*x) := by ring_nf; rw [I_sq]; ring
    have : (1-I*(x:ℂ))⁻¹ = (1+I*x)/(1+(x:ℂ)^2) := by
      rw [eq_div_iff h2, hf, ← mul_assoc, inv_mul_cancel₀ h1, one_mul]
    rw [this]; push_cast; field_simp
  have hev : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), (∫ s : ℝ in Ioi 0, exp (-(s:ℂ)*(1-I*x) - (t:ℂ)*(s:ℂ)^2)) =
      (Real.voigtU x t : ℂ) + I*Real.voigtV x t := by
    filter_upwards [self_mem_nhdsWithin] with t ht using (voigt_laplace x ht).symm
  have hW' := hW.congr' hev
  rw [hinv] at hW'
  constructor
  · have := (Complex.continuous_re.tendsto _).comp hW'
    simp only [Function.comp_def, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul,
      mul_zero, sub_zero, add_zero] at this
    exact this
  · have := (Complex.continuous_im.tendsto _).comp hW'
    simp only [Function.comp_def, add_im, ofReal_re, mul_im, I_re, I_im, ofReal_im,
      one_mul, mul_zero, zero_add] at this
    exact this

/-- Real.voigt symmetry. -/
@[dlmf 7.19.E6]
theorem Real.voigt_symmetry (x : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.voigtU (-x) t=Real.voigtU x t ∧ Real.voigtV (-x) t = -Real.voigtV x t := by
  constructor
  · rw [Real.voigtU, Real.voigtU, ← integral_neg_eq_self]
    congr 1; congr 1; funext y
    rw [show -x - -y = -(x-y) by ring, neg_sq, neg_sq]
  · rw [Real.voigtV, Real.voigtV, ← integral_neg_eq_self, ← mul_neg, ← integral_neg]
    congr 1; congr 1; funext y
    rw [show -(-x - -y)^2 = -(x-y)^2 by ring, neg_sq]
    ring

/-- Real.voigt bounds. -/
@[dlmf 7.19.E7]
theorem Real.voigt_bounds (x : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < Real.voigtU x t ∧ Real.voigtU x t ≤ 1 ∧ -1 ≤ Real.voigtV x t ∧ Real.voigtV x t ≤ 1 := by
  have hk := integrable_voigt_kernel x ht
  have hK := integral_voigt_kernel x t
  have hs : 0 < Real.sqrt (4*π*t) := Real.sqrt_pos.mpr (by positivity)
  have hy1 (y : ℝ) : 0 < 1+y^2 := by positivity
  have hU : Integrable (fun y : ℝ => Real.exp (-(x-y)^2/(4*t))/(1+y^2)) := by
    refine hk.mono' ((Continuous.div (by fun_prop) (by fun_prop)
      (fun y => (hy1 y).ne')).aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) (hy1 y))]
    exact div_le_self (Real.exp_pos _).le (by nlinarith [sq_nonneg y])
  have hV : Integrable (fun y : ℝ => y*Real.exp (-(x-y)^2/(4*t))/(1+y^2)) := by
    refine hk.mono' ((Continuous.div (by fun_prop) (by fun_prop)
      (fun y => (hy1 y).ne')).aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (hy1 y),
      div_le_iff₀ (hy1 y)]
    have : |y| ≤ 1+y^2 := by nlinarith [abs_nonneg y, sq_abs y, sq_nonneg (|y|-1)]
    nlinarith [Real.exp_pos (-(x-y)^2/(4*t))]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Real.voigtU]
    refine mul_pos (by positivity) ?_
    rw [integral_pos_iff_support_of_nonneg (fun y => (div_pos (Real.exp_pos _) (hy1 y)).le) hU]
    have : Function.support (fun y : ℝ => Real.exp (-(x-y)^2/(4*t))/(1+y^2)) = univ :=
      Set.eq_univ_of_forall fun y => Function.mem_support.mpr (div_pos (Real.exp_pos _) (hy1 y)).ne'
    rw [this]; simp
  · rw [Real.voigtU, one_div, inv_mul_le_iff₀ hs, mul_one, ← hK]
    refine integral_mono hU hk fun y => ?_
    exact div_le_self (Real.exp_pos _).le (by nlinarith [sq_nonneg y])
  · rw [Real.voigtV, one_div, le_inv_mul_iff₀ hs, ← hK, mul_neg_one, ← integral_neg]
    refine integral_mono hk.neg hV fun y => ?_
    simp only
    rw [le_div_iff₀ (hy1 y)]
    nlinarith [Real.exp_pos (-(x-y)^2/(4*t)), sq_nonneg (y+1)]
  · rw [Real.voigtV, one_div, inv_mul_le_iff₀ hs, mul_one, ← hK]
    refine integral_mono hV hk fun y => ?_
    simp only
    rw [div_le_iff₀ (hy1 y)]
    nlinarith [Real.exp_pos (-(x-y)^2/(4*t)), sq_nonneg (y-1)]

/-- Real.voigtV derivative relation. -/
@[dlmf 7.19.E8]
theorem Real.voigtV_derivative_relation (x : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.voigtV x t=x*Real.voigtU x t+2*t*deriv (fun u => Real.voigtU u t) x := by
  rw [(hasDerivAt_voigt x ht).1.deriv]
  have h := congrArg im (voigt_laplace_deriv x ht).2
  rw [← voigt_laplace x ht] at h
  set J := ∫ s : ℝ in Ioi 0, (s:ℂ) * exp (-(s:ℂ)*(1-I*x) - t*(s:ℂ)^2)
  simp at h
  linarith

/-- Real.voigtU derivative relation. -/
@[dlmf 7.19.E9]
theorem Real.voigtU_derivative_relation (x : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.voigtU x t=1-x*Real.voigtV x t-2*t*deriv (fun u => Real.voigtV u t) x := by
  rw [(hasDerivAt_voigt x ht).2.deriv]
  have h := congrArg re (voigt_laplace_deriv x ht).2
  rw [← voigt_laplace x ht] at h
  set J := ∫ s : ℝ in Ioi 0, (s:ℂ) * exp (-(s:ℂ)*(1-I*x) - t*(s:ℂ)^2)
  simp at h
  linarith

/-- Real.voigtU fourier laplace. -/
@[dlmf 7.19.E10]
theorem Real.voigtU_fourier_laplace {a : ℝ} (ha : 0 < a) (u : ℝ) :
    Real.voigtU (u/a) (1/(4*a^2))=a*(∫ t : ℝ in Ioi 0, Real.exp (-a*t-t^2/4)*Real.cos (u*t)) := by
  have h := congrArg re (voigt_fourier_laplace_complex ha u)
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero,
    add_zero] at h
  rw [h, ← RCLike.re_to_complex, ← integral_re (integrableOn_voigt_fourier_laplace ha u)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
  rw [RCLike.re_to_complex, Complex.exp_re]
  simp [-ofReal_pow]

/-- Real.voigtV fourier laplace. -/
@[dlmf 7.19.E11]
theorem Real.voigtV_fourier_laplace {a : ℝ} (ha : 0 < a) (u : ℝ) :
    Real.voigtV (u/a) (1/(4*a^2))=a*(∫ t : ℝ in Ioi 0, Real.exp (-a*t-t^2/4)*Real.sin (u*t)) := by
  have h := congrArg im (voigt_fourier_laplace_complex ha u)
  simp only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_mul, one_mul, zero_add,
    mul_zero, add_zero] at h
  rw [h, ← RCLike.im_to_complex, ← integral_im (integrableOn_voigt_fourier_laplace ha u)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
  rw [RCLike.im_to_complex, Complex.exp_im]
  simp [-ofReal_pow]

end DLMF.Confluent
