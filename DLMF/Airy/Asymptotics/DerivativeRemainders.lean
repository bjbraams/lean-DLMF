/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Asymptotics.OscillatoryRemainders

/-!
# Stieltjes representations for Airy derivative remainders

Exact chi constants and a positive Stieltjes representation control the derivative error kernel.

Source references and common attribution are retained in
`DLMF.Airy.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent

open scoped Real Topology Interval

namespace DLMF.Airy

/-! ### Exact values of χ at integers -/

/-- The two-step recurrence `χ(x+2) = χ(x) (x+2)/(x+1)` for `x ≥ 0`. -/
theorem airyChi_add_two {x : ℝ} (hx : 0 ≤ x) :
    airyChi (x + 2) = airyChi x * ((x + 2) / (x + 1)) := by
  have h1 : (x + 2) / 2 + 1 = (x / 2 + 1) + 1 := by ring
  have h2 : (x + 2) / 2 + 1 / 2 = (x / 2 + 1 / 2) + 1 := by ring
  have hp1 : 0 < x / 2 + 1 := by positivity
  have hp2 : 0 < x / 2 + 1 / 2 := by positivity
  have hG := (Real.Gamma_pos_of_pos hp2).ne'
  rw [airyChi, airyChi, h1, h2, Real.Gamma_add_one hp1.ne', Real.Gamma_add_one hp2.ne']
  have : x + 1 ≠ 0 := by positivity
  field_simp

/-- `χ(0) = 1`. -/
theorem airyChi_zero : airyChi 0 = 1 := by
  rw [airyChi]; norm_num [Real.Gamma_one_half_eq]
  exact (Real.sqrt_pos.mpr Real.pi_pos).ne'

/-- `χ(1) = π/2`. -/
theorem airyChi_one : airyChi 1 = π / 2 := by
  rw [airyChi, show (1 : ℝ) / 2 + 1 = 1 / 2 + 1 by ring, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq, show (1 : ℝ) / 2 + 1 / 2 = 1 by ring, Real.Gamma_one]
  rw [show Real.sqrt π * (1 / 2 * Real.sqrt π) = (Real.sqrt π) ^ 2 / 2 by ring,
    Real.sq_sqrt Real.pi_pos.le]
  ring

/-- `χ(2m) = ∏_{j<m} (2j+2)/(2j+1)`. -/
theorem airyChi_two_mul (m : ℕ) :
    airyChi (2 * m) = ∏ j ∈ Finset.range m, ((2 * j + 2 : ℝ) / (2 * j + 1)) := by
  induction m with
  | zero => simpa using airyChi_zero
  | succ m ih =>
    rw [Finset.prod_range_succ, ← ih, show (2 * ((m + 1 : ℕ) : ℝ)) = 2 * m + 2 by push_cast; ring,
      airyChi_add_two (by positivity)]

/-- `χ(2m+1) = (π/2) ∏_{j<m} (2j+3)/(2j+2)`. -/
theorem airyChi_two_mul_add_one (m : ℕ) :
    airyChi (2 * m + 1) = π / 2 * ∏ j ∈ Finset.range m, ((2 * j + 3 : ℝ) / (2 * j + 2)) := by
  induction m with
  | zero => simpa using airyChi_one
  | succ m ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih,
      show (2 * ((m + 1 : ℕ) : ℝ)) + 1 = (2 * m + 1) + 2 by push_cast; ring,
      airyChi_add_two (by positivity)]
    congr 1; ring_nf

/-! ### A positive Stieltjes representation for the derivative error kernel

The two positive-parameter instances of DLMF 13.4.5 below combine by contiguous
relations to give the sharp-parameter density for the sigma-zero Airy derivative bounds.
The final error estimates still require the Laplace-mixture and branch-continuation steps.
-/

/-- The normalized Kummer form of the Airy derivative. -/
def airyDer_normalizedU (z : ℂ) : ℂ := z^(-(1/6):ℂ)*kummerU (-(1/6)) (-(1/3)) z

/-- Integrable Cauchy transforms of the kernels used below. -/
theorem airyDer_integrable_cauchy {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) {z : ℂ}
    (hz : z ∈ slitPlane) : IntegrableOn (fun t : ℝ => f t/((t:ℂ)+z)) (Ioi 0) := by
  obtain ⟨δ, hδ, hδb⟩ := exists_forall_le_norm_add_of_mem_slitPlane hz
  have hm : AEStronglyMeasurable (fun t : ℝ => f t/((t:ℂ)+z)) (volume.restrict (Ioi 0)) :=
    hf.aestronglyMeasurable.mul (by fun_prop : Measurable fun t : ℝ => ((t:ℂ)+z)⁻¹).aestronglyMeasurable
  refine (hf.norm.const_mul δ⁻¹).mono' hm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hb := hδb t (le_of_lt ht) z (Metric.mem_ball_self hδ)
  rw [norm_div]
  calc ‖f t‖/‖(t:ℂ)+z‖ ≤ ‖f t‖/δ := div_le_div_of_nonneg_left (norm_nonneg _) hδ hb
    _ = _ := by ring

/-- A contiguous relation lowering the first parameter from its positive domain. -/
theorem airyDer_U_lower {z : ℂ} (hz : z ≠ 0) :
    kummerU (-(1/6)) (-(1/3)) z = z*kummerU (5/6) (2/3) z+(7/6:ℂ)*kummerU (5/6) (-(1/3)) z := by
  have h1 := kummerU_contiguous_mixed (-(1/6)) (-(1/3)) z hz
  have h2 := kummerU_contiguous_a_b (-(1/6)) (2/3) z hz
  norm_num at h1 h2
  linear_combination -6*h1-6*z*h2

/-- The kernel relation used to combine the two positive-parameter transforms. -/
theorem airyDer_U_kernel {t : ℂ} (ht : t ≠ 0) :
    kummerU (-(7/6)) (-(1/3)) t = t*kummerU (-(1/6)) (2/3) t+(1/6:ℂ)*kummerU (-(1/6)) (-(1/3)) t := by
  have h := kummerU_contiguous_shift_a (-(1/6)) (-(1/3)) t ht
  norm_num at h
  linear_combination h

/-- The exactly evaluated constant term in the continued Stieltjes formula. -/
theorem airyDer_constant_moment :
    (∫ t : ℝ in Ioi 0, exp (-(t:ℂ))*(t:ℂ)^(-(1/6):ℂ)*kummerU (-(1/6)) (2/3) t) =
      Gamma (5/6)*Gamma (7/6) := by
  have h := laplace_kummerU (a := (-(1/6):ℂ)) (b := 5/6) (c := 2/3) (z := 1)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by norm_num),
    regularizedGaussHGFun_eq_div_Gamma (fun k => by
      have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
      intro he
      have := congrArg Complex.re he
      norm_num at this
      linarith), ordinaryHypergeometric_zero, Gamma_one] at h
  simpa using h

/-- `6 Γ(5/6) Γ(7/6) = 2π`, from the reflection formula at `1/6`. -/
private lemma airyDer_six_gamma_mul : 6 * Gamma (5 / 6 : ℂ) * Gamma (7 / 6) = 2 * π := by
  have h := Gamma_mul_Gamma_one_sub (1 / 6 : ℂ)
  have hg := Gamma_add_one (1 / 6 : ℂ) (by norm_num)
  rw [show π * (1 / 6 : ℂ) = ((Real.pi / 6 : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin,
    Real.sin_pi_div_six] at h
  norm_num at h hg
  linear_combination h + (6 * Gamma (5 / 6 : ℂ)) * hg

/-- The Airy derivative's normalized Kummer function has a positive Stieltjes remainder. -/
theorem airyDer_stieltjes {z : ℂ} (hz : z ∈ slitPlane) :
    airyDer_normalizedU z = 1 + 1/(2*π:ℂ)*
      ∫ t : ℝ in Ioi 0, exp (-(t:ℂ))*airyDer_normalizedU t/((t:ℂ)+z) := by
  have hz0 := slitPlane_ne_zero hz
  have h1 := kummerU_stieltjes (a := (5/6:ℂ)) (b := 2/3) hz (by norm_num) (by norm_num)
  have h2 := kummerU_stieltjes (a := (5/6:ℂ)) (b := -(1/3)) hz (by norm_num) (by norm_num)
  norm_num at h1 h2
  have hG : Gamma (13/6:ℂ) = (7/6:ℂ)*Gamma (7/6) := by
    rw [show (13/6:ℂ)=(7/6)+1 by norm_num, Gamma_add_one (7/6) (by norm_num)]
  have hG1 : Gamma (5/6:ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hG2 : Gamma (7/6:ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  let f : ℝ → ℂ := fun t => exp (-(t:ℂ))*(t:ℂ)^(-(1/6):ℂ)*kummerU (-(1/6)) (2/3) t
  let g : ℝ → ℂ := fun t => exp (-(t:ℂ))*(t:ℂ)^(-(1/6):ℂ)*kummerU (-(7/6)) (-(1/3)) t
  let p : ℝ → ℂ := fun t => exp (-(t:ℂ))*airyDer_normalizedU t
  have hf : IntegrableOn f (Ioi 0) := by
    have h := (laplace_kummerU_gauss (a := (-(1/6):ℂ)) (b := 5/6) (c := 2/3) (z := 1)
      (by norm_num) (by norm_num) (by norm_num)).1
    convert h using 1
    funext t
    simp only [tricomiLaplaceKernel, f]
    norm_num
  have hg : IntegrableOn g (Ioi 0) := by
    have h := (laplace_kummerU_gauss (a := (-(7/6):ℂ)) (b := 5/6) (c := -(1/3)) (z := 1)
      (by norm_num) (by norm_num) (by norm_num)).1
    convert h using 1
    funext t
    simp only [tricomiLaplaceKernel, g]
    norm_num
  have hp : IntegrableOn p (Ioi 0) := by
    have h := (laplace_kummerU_gauss (a := (-(1/6):ℂ)) (b := 5/6) (c := -(1/3)) (z := 1)
      (by norm_num) (by norm_num) (by norm_num)).1
    convert h using 1
    funext t
    simp only [tricomiLaplaceKernel, p, airyDer_normalizedU]
    norm_num
    ring
  have hpt : ∀ t ∈ Ioi (0:ℝ),
      z*(f t/((t:ℂ)+z))+g t/((t:ℂ)+z) = f t+(1/6:ℂ)*(p t/((t:ℂ)+z)) := by
    intro t ht
    have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have hd : (t:ℂ)+z ≠ 0 := by
      obtain ⟨δ,hδ,hδb⟩ := exists_forall_le_norm_add_of_mem_slitPlane hz
      exact norm_pos_iff.mp (hδ.trans_le (hδb t (le_of_lt ht) z (Metric.mem_ball_self hδ)))
    dsimp only [f,g,p,airyDer_normalizedU]
    rw [airyDer_U_kernel ht0]
    field_simp
    ring
  have hint : z*(∫ t in Ioi (0:ℝ), f t/((t:ℂ)+z))+
      (∫ t in Ioi (0:ℝ), g t/((t:ℂ)+z)) =
      Gamma (5/6)*Gamma (7/6)+(1/6:ℂ)*(∫ t in Ioi (0:ℝ), p t/((t:ℂ)+z)) := by
    rw [← integral_const_mul, ← integral_add ((airyDer_integrable_cauchy hf hz).const_mul _) (airyDer_integrable_cauchy hg hz),
      setIntegral_congr_fun measurableSet_Ioi hpt, integral_add hf ((airyDer_integrable_cauchy hp hz).const_mul _), integral_const_mul]
    rw [show (∫ t in Ioi (0:ℝ), f t)=Gamma (5/6)*Gamma (7/6) from airyDer_constant_moment]
  have hu := airyDer_U_lower hz0
  rw [h1,h2,hG] at hu
  have hI1 : (∫ t in Ioi (0:ℝ), kummerU (-(1/6)) (2/3) t*exp (-(t:ℂ))*(t:ℂ)^(-(1/6):ℂ)/((t:ℂ)+z)) =
      ∫ t in Ioi (0:ℝ), f t/((t:ℂ)+z) := by
    apply setIntegral_congr_fun measurableSet_Ioi; intro t ht; dsimp only [f]; ring
  have hI2 : (∫ t in Ioi (0:ℝ), kummerU (-(7/6)) (-(1/3)) t*exp (-(t:ℂ))*(t:ℂ)^(-(1/6):ℂ)/((t:ℂ)+z)) =
      ∫ t in Ioi (0:ℝ), g t/((t:ℂ)+z) := by
    apply setIntegral_congr_fun measurableSet_Ioi; intro t ht; dsimp only [g]; ring
  rw [hI1,hI2] at hu
  have hpow : z^(-(1/6):ℂ)*z^(1/6:ℂ)=1 := by rw [← cpow_add _ _ hz0]; norm_num
  have hgamma := airyDer_six_gamma_mul
  have hu' : kummerU (-(1/6)) (-(1/3)) z =
      z^(1/6:ℂ)/(Gamma (5/6)*Gamma (7/6)) *
        (z*(∫ t in Ioi (0:ℝ), f t/((t:ℂ)+z))+
          (∫ t in Ioi (0:ℝ), g t/((t:ℂ)+z))) := by
    rw [hu]
    field_simp
  change z^(-(1/6):ℂ)*kummerU (-(1/6)) (-(1/3)) z =
    1+1/(2*π:ℂ)*(∫ t in Ioi (0:ℝ), p t/((t:ℂ)+z))
  rw [hu', hint]
  calc
    _ = 1+1/(6*Gamma (5/6:ℂ)*Gamma (7/6))*
        (∫ t in Ioi (0:ℝ), p t/((t:ℂ)+z)) := by
      field_simp
      linear_combination (6*Gamma (5/6:ℂ)*Gamma (7/6)+
        (∫ t in Ioi (0:ℝ), p t/((t:ℂ)+z)))*hpow
    _ = _ := by rw [hgamma]

/-- Positive real Laplace representation of the normalized derivative kernel. -/
theorem airyDer_normalizedU_real {t : ℝ} (ht : 0 < t) :
    airyDer_normalizedU t = ((t^(7/6:ℝ)/Real.Gamma (7/6) *
      ∫ u : ℝ in Ioi 0, Real.exp (-t*u)*u^(1/6:ℝ)*(1+u)^(1/6:ℝ) : ℝ):ℂ) := by
  have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have h := kummerU_kummer_transform_all (-(1/6):ℂ) (-(1/3)) ht0
  norm_num at h
  have hp : (t:ℂ)^(-(1/6):ℂ)*(t:ℂ)^(4/3:ℂ)=(t:ℂ)^(7/6:ℂ) := by
    rw [← cpow_add _ _ ht0]
    norm_num
  rw [airyDer_normalizedU, h, ← mul_assoc, hp, kummerU_laplace (by norm_num) (by simpa using ht)]
  rw [show (7/6:ℂ)-1=1/6 by norm_num, show (7/3:ℂ)-7/6-1=1/6 by norm_num]
  have hI : (∫ u : ℝ in Ioi 0, exp (-(t:ℂ)*u)*(u:ℂ)^(1/6:ℂ)*(1+(u:ℂ))^(1/6:ℂ)) =
      ((∫ u : ℝ in Ioi 0, Real.exp (-t*u)*u^(1/6:ℝ)*(1+u)^(1/6:ℝ) : ℝ):ℂ) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    have hu0 : 0 < u := hu
    push_cast
    rw [ofReal_cpow hu0.le, ofReal_cpow (by linarith : 0 ≤ 1+u)]
    push_cast
    ring
  rw [hI]
  push_cast
  rw [ofReal_cpow ht.le]
  have hGamma : Gamma (7/6:ℂ)=(Real.Gamma (7/6:ℝ):ℂ) := by
    convert Gamma_ofReal (7/6) using 1; norm_num
  rw [hGamma]
  push_cast
  ring

/-- The derivative Stieltjes kernel is real and nonnegative on the positive axis. -/
theorem airyDer_normalizedU_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ (airyDer_normalizedU t).re ∧ (airyDer_normalizedU t).im=0 := by
  rw [airyDer_normalizedU_real ht]
  simp only [ofReal_re, ofReal_im, and_true]
  have hi : 0 ≤ ∫ u : ℝ in Ioi 0, Real.exp (-t*u)*u^(1/6:ℝ)*(1+u)^(1/6:ℝ) := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro u hu
    have hu0 : 0 < u := hu
    have : 0 ≤ 1+u := by linarith
    positivity
  exact mul_nonneg (div_nonneg (Real.rpow_nonneg ht.le _) (Real.Gamma_pos_of_pos (by norm_num)).le) hi

/-- The real density of the Airy derivative Stieltjes transform. -/
def airyDer_density (t : ℝ) : ℝ := Real.exp (-t)*(airyDer_normalizedU t).re

/-- Complex and real forms of the derivative Stieltjes density agree. -/
theorem airyDer_density_coe {t : ℝ} (ht : 0 < t) :
    (airyDer_density t:ℂ)=exp (-(t:ℂ))*airyDer_normalizedU t := by
  rw [airyDer_density, ofReal_mul, ofReal_exp]
  push_cast
  congr 1
  apply Complex.ext <;> simp [(airyDer_normalizedU_nonneg ht).2]

/-- The Airy derivative Stieltjes density is nonnegative. -/
theorem airyDer_density_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ airyDer_density t :=
  mul_nonneg (Real.exp_pos _).le (airyDer_normalizedU_nonneg ht).1

/-- The regularized Gauss function at zero, on its positive parameter half-plane. -/
theorem airyDer_regularizedGaussHG_zero (a b c : ℂ) (hc : 0 < c.re) :
    regularizedGaussHG a b c 0 = 1/Gamma c := by
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by norm_num),
    regularizedGaussHGFun_eq_div_Gamma (fun k => by
      intro he
      have := congrArg Complex.re he
      simp only [neg_re, natCast_re] at this
      linarith [Nat.cast_nonneg (α := ℝ) k]), ordinaryHypergeometric_zero]

/-- The moments of the complex derivative Stieltjes density. -/
theorem airyDer_density_moment_complex (k : ℕ) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^k*exp (-(t:ℂ))*airyDer_normalizedU t) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, (t:ℂ)^k*exp (-(t:ℂ))*airyDer_normalizedU t) =
      Gamma ((k:ℂ)+5/6)*Gamma ((k:ℂ)+13/6)/Gamma ((k:ℂ)+2) := by
  have h := laplace_kummerU_gauss (a := (-(1/6):ℂ)) (b := (k:ℂ)+5/6) (c := -(1/3)) (z := 1)
    (by norm_num; linarith [Nat.cast_nonneg (α := ℝ) k])
    (by norm_num; linarith [Nat.cast_nonneg (α := ℝ) k]) (by norm_num)
  have hpt (t : ℝ) (ht : t ∈ Ioi (0:ℝ)) :
      (t:ℂ)^k*exp (-(t:ℂ))*airyDer_normalizedU t =
        tricomiLaplaceKernel (-(1/6)) ((k:ℂ)+5/6) (-(1/3)) 1 t := by
    dsimp only [airyDer_normalizedU, tricomiLaplaceKernel]
    have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    rw [show (k:ℂ)+5/6-1=(k:ℂ)+(-(1/6)) by ring, cpow_add _ _ ht0, cpow_natCast]
    ring
  constructor
  · exact h.1.congr_fun (fun t ht => (hpt t ht).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi hpt, h.2]
    norm_num
    rw [show (k:ℂ)+5/6+1/3+1=(k:ℂ)+13/6 by ring,
      show -(1/6:ℂ)+((k:ℂ)+5/6)+1/3+1=(k:ℂ)+2 by ring,
      airyDer_regularizedGaussHG_zero _ _ _ (by simp; positivity)]
    ring

/-- The real moments of the positive derivative Stieltjes density. -/
theorem airyDer_density_moment (k : ℕ) :
    IntegrableOn (fun t : ℝ => t^k*airyDer_density t) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, t^k*airyDer_density t) =
      Real.Gamma ((k:ℝ)+5/6)*Real.Gamma ((k:ℝ)+13/6)/Real.Gamma ((k:ℝ)+2) := by
  have heq (t : ℝ) (ht : t ∈ Ioi (0:ℝ)) :
      ((t^k*airyDer_density t:ℝ):ℂ)=(t:ℂ)^k*exp (-(t:ℂ))*airyDer_normalizedU t := by
    push_cast
    rw [airyDer_density_coe ht]
    ring
  have h := airyDer_density_moment_complex k
  have hc : IntegrableOn (fun t : ℝ => ((t^k*airyDer_density t:ℝ):ℂ)) (Ioi 0) :=
    h.1.congr_fun (fun t ht => (heq t ht).symm) measurableSet_Ioi
  constructor
  · simpa only [RCLike.re_to_complex, ofReal_re] using hc.re
  · apply ofReal_injective
    rw [← integral_complex_ofReal, setIntegral_congr_fun measurableSet_Ioi heq, h.2]
    have hGamma (a : ℝ) : (Real.Gamma a:ℂ)=Gamma (a:ℂ) := (Gamma_ofReal a).symm
    push_cast
    simp only [hGamma]
    push_cast
    rfl

/-- Kummer's positive-parameter form of the normalized derivative. -/
theorem airyDer_normalizedU_positive {z : ℂ} (hz : z ≠ 0) :
    airyDer_normalizedU z=z^(7/6:ℂ)*kummerU (7/6) (7/3) z := by
  have h := kummerU_kummer_transform_all (-(1/6):ℂ) (-(1/3)) hz
  norm_num at h
  rw [airyDer_normalizedU,h,← mul_assoc,← cpow_add _ _ hz]
  norm_num

/-- The normalized Airy derivative is the positive Stieltjes function on its principal sector. -/
theorem airyDer_normalizedU_eq {z : ℂ} (hz : z ≠ 0) (harg : |arg z|<2*π/3) :
    airyAiDeriv z/airyPrefactor .aiDeriv z = airyDer_normalizedU (2*airyZetaComplex z) := by
  have hW : 2*airyZetaComplex z ≠ 0 := mul_ne_zero two_ne_zero (airySt_zeta_ne_zero hz)
  rw [airyDer_normalizedU_positive hW, airySt_two_zeta_cpow hz harg,
    airyAiDeriv_eq_kummerU hz harg, airyPrefactor]
  have hπ : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z^(1/4:ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
  rw [exp_sub]
  have hN := airyDer_norm_const hz
  have hE : exp (-airyZetaComplex z) ≠ 0 := exp_ne_zero _
  field_simp
  have hEE : exp (airyZetaComplex z)*exp (-airyZetaComplex z)=1 := by
    rw [← exp_add]; simp
  ring_nf at hN ⊢
  linear_combination kummerU (7/6) (7/3) (airyZetaComplex z*2)*hN -
    kummerU (7/6) (7/3) (airyZetaComplex z*2)*z^(1/4:ℂ)*
      exp (airyLogZeta z*(7/6)+log 2*(7/6))*hEE
end DLMF.Airy

end
