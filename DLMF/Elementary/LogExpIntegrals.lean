/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Polylog.Dilog
public import DLMF.Core.Framework
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Continued fractions and integrals: DLMF §§4.9–4.11

Continued fractions use continuants from `DLMF.Core.Framework`, so an intermediate
zero denominator is not prematurely interpreted as a terminating nested quotient.
Convergence means convergence of the finite convergents. Indefinite integrals are
stated as derivative identities on their full branch domains. Section 4.11 only
contains bibliographic references and has no mathematical statement to acquire.
-/

@[expose] public section
open Complex Filter Set Finset MeasureTheory
open scoped Topology Real
noncomputable section
namespace DLMF.Elementary

/-- Logarithm continued fraction on its full principal slit domain. -/
@[dlmf 4.9.E1]
theorem log_one_add_continuedFraction {z : ℂ} (hz : 1 + z ∈ Complex.slitPlane) :
    DLMF.HasContinuedFraction
      (fun k => if k = 0 then z else (((k + 1) / 2 : ℕ) : ℂ) ^ 2 * z)
      (fun k => (k + 1 : ℂ)) (Complex.log (1 + z)) := by
  sorry

/-- Odd logarithm fraction outside the two real exterior rays. -/
@[dlmf 4.9.E2]
theorem log_ratio_continuedFraction {z : ℂ} (hz : z.im ≠ 0 ∨ |z.re| < 1) :
    DLMF.HasContinuedFraction
      (fun k => if k = 0 then 2 * z else -(k : ℂ) ^ 2 * z ^ 2)
      (fun k => (2 * k + 1 : ℂ)) (Complex.log ((1 + z) / (1 - z))) := by
  sorry

/-- First exponential continued fraction, valid for every complex argument. -/
@[dlmf 4.9.E3]
theorem exp_continuedFraction_one (z : ℂ) :
    DLMF.HasContinuedFraction
      (fun k => if k = 0 then 1 else (-1 : ℂ) ^ k * z)
      (fun k => if k = 0 then 1 else if k % 2 = 0 then 2 else (k : ℂ))
      (Complex.exp z) := by
  sorry

/-- Second exponential continued fraction, valid for every complex argument. -/
@[dlmf 4.9.E3]
theorem exp_continuedFraction_two (z : ℂ) :
    Tendsto (fun N => 1 + DLMF.cfTail
      (fun k => if k = 0 then z else (-1 : ℂ) ^ k * z)
      (fun k => if k = 0 then 1 else if k % 2 = 1 then 2 else (k + 1 : ℂ)) 0 N)
      atTop (𝓝 (Complex.exp z)) := by
  sorry

/-- Third exponential continued fraction, valid for every complex argument. -/
@[dlmf 4.9.E3]
theorem exp_continuedFraction_three (z : ℂ) :
    Tendsto (fun N => 1 + DLMF.cfTail
      (fun k => if k = 0 then z else z ^ 2 / (4 * (4 * (k : ℂ) ^ 2 - 1)))
      (fun k => if k = 0 then 1 - z / 2 else 1) 0 N) atTop (𝓝 (Complex.exp z)) := by
  sorry

/-- The exponential polynomial of degree n. -/
@[dlmf 4.9.E5]
def expPartialSum (n : ℕ) (z : ℂ) : ℂ := ∑ k ∈ range (n + 1), z ^ k / k.factorial

/-- The full n-parameter remainder fraction for every complex argument. -/
@[dlmf 4.9.E4]
theorem exp_remainder_continuedFraction (n : ℕ) (hn : 1 ≤ n) (z : ℂ) :
    DLMF.HasContinuedFraction
      (fun k => if k = 0 then z ^ n else if k = 1 then -(n.factorial : ℂ) * z
        else if k % 2 = 0 then (k / 2 : ℕ) * z
        else -((n + (k - 1) / 2 : ℕ) : ℂ) * z)
      (fun k => if k = 0 then (n.factorial : ℂ) else (n + k : ℂ))
      (Complex.exp z - expPartialSum (n - 1) z) := by
  sorry

/-- The inverse function is the derivative of the principal logarithm on its slit domain. -/
@[dlmf 4.10.E1]
theorem log_primitive {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt Complex.log (1 / z) z := by
  simpa [one_div] using Complex.hasDerivAt_log hz

/-- The logarithm antiderivative on its full principal branch. -/
@[dlmf 4.10.E2]
theorem log_mul_primitive {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (fun z : ℂ => z * Complex.log z - z) (Complex.log z) z := by
  have hz0 := Complex.slitPlane_ne_zero hz
  convert ((hasDerivAt_id z).mul (Complex.hasDerivAt_log hz)).sub (hasDerivAt_id z) using 1
  · ext w
    simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
  · simp only [id_eq, mul_one]
    field_simp <;> ring

/-- The power-logarithm antiderivative with all complex exponents except minus one. -/
@[dlmf 4.10.E3]
theorem cpow_log_primitive (a : ℂ) (ha : a ≠ -1) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (fun z : ℂ => z ^ (a + 1) / (a + 1) * Complex.log z -
      z ^ (a + 1) / (a + 1) ^ 2) (z ^ a * Complex.log z) z := by
  have hz0 := Complex.slitPlane_ne_zero hz
  have ha1 : a+1≠0 := by intro h; apply ha; linear_combination h
  have hp := (Complex.hasStrictDerivAt_cpow_const (c := a+1) hz).hasDerivAt
  convert ((hp.div_const (a+1)).mul (Complex.hasDerivAt_log hz)).sub
    (hp.div_const ((a+1)^2)) using 1
  rw [show a+1-1=a by ring, Complex.cpow_add _ _ hz0, Complex.cpow_one]
  field_simp
  ring

/-- The iterated-logarithm antiderivative retains both logarithm branch conditions. -/
@[dlmf 4.10.E4]
theorem log_log_primitive {z : ℂ} (hz : z ∈ Complex.slitPlane) (hl : Complex.log z ∈ Complex.slitPlane) :
    HasDerivAt (fun z : ℂ => Complex.log (Complex.log z)) (1 / (z * Complex.log z)) z := by
  simpa only [Function.comp_def, one_div, mul_inv_rev] using
    (Complex.hasDerivAt_log hl).comp z (Complex.hasDerivAt_log hz)

/-- The dilogarithm kernel is interval integrable on `[0,1]`, up to its logarithmic endpoint. -/
lemma logR4_dilogKernel_intervalIntegrable :
    IntervalIntegrable DLMF.Polylog.dilogKernel volume 0 1 := by
  have hcont := DLMF.Polylog.continuousOn_re_polylogSeries_two.mono
    (Icc_subset_Icc (by norm_num : (-1:ℝ) ≤ 0) le_rfl)
  refine intervalIntegral.intervalIntegrable_deriv_of_nonneg
    (g := fun t : ℝ => (DLMF.Polylog.polylogSeries 2 t).re)
    (by rwa [Set.uIcc_of_le zero_le_one]) ?_ ?_
  · intro t ht
    rw [min_eq_left zero_le_one, max_eq_right zero_le_one] at ht
    exact DLMF.Polylog.hasDerivAt_re_polylogSeries_two (abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩)
  · intro t ht
    rw [min_eq_left zero_le_one, max_eq_right zero_le_one] at ht
    exact DLMF.Polylog.dilogKernel_nonneg (abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩)

/-- Reflection of the logarithmic integrand into the dilogarithm kernel. -/
lemma logR4_log_div_one_sub_eq (x : ℝ) (hx : x ≠ 0) :
    Real.log (1-x)/(1-(1-x)) = -DLMF.Polylog.dilogKernel x := by
  rw [DLMF.Polylog.dilogKernel_of_ne hx]; ring

/-- Convergent improper logarithm integral with its exact value. -/
@[dlmf 4.10.E5]
theorem integral_log_div_one_sub  :
    IntervalIntegrable (fun t : ℝ => Real.log t / (1 - t)) volume 0 1 ∧
    (∫ t in (0 : ℝ)..1, Real.log t / (1 - t)) = -Real.pi ^ 2 / 6 := by
  have hae : ∀ᵐ x ∂volume, x ∈ Set.uIoc (0:ℝ) 1 →
      (fun x => Real.log (1-x)/(1-(1-x))) x = (fun x => -DLMF.Polylog.dilogKernel x) x := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with x hx _
    exact logR4_log_div_one_sub_eq x (by simpa using hx)
  have hint : IntervalIntegrable (fun x => Real.log (1-x)/(1-(1-x))) volume 0 1 :=
    (logR4_dilogKernel_intervalIntegrable.neg).congr_ae (by
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with x hx
      exact (logR4_log_div_one_sub_eq x (by simpa using hx)).symm)
  have e := intervalIntegral.integral_comp_sub_left (fun t : ℝ => Real.log t / (1 - t)) (1:ℝ)
    (a := 0) (b := 1)
  simp only [sub_zero, sub_self] at e
  constructor
  · have := hint.comp_sub_left 1
    simpa using this.symm
  · rw [← e, intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_neg]
    change -DLMF.Polylog.Real.dilog 1 = _
    rw [DLMF.Polylog.Real.dilog_one]; ring

/-- Convergent improper alternating logarithm integral with its exact value. -/
@[dlmf 4.10.E6]
theorem integral_log_div_one_add  :
    IntervalIntegrable (fun t : ℝ => Real.log t / (1 + t)) volume 0 1 ∧
    (∫ t in (0 : ℝ)..1, Real.log t / (1 + t)) = -Real.pi ^ 2 / 12 := by
  obtain ⟨hA, hAv⟩ := integral_log_div_one_sub
  have hf : ContinuousOn (fun t : ℝ => t^2) (Set.uIcc 0 1) := by fun_prop
  have hff' : ∀ x ∈ Ioo (min (0:ℝ) 1) (max 0 1), HasDerivAt (fun t : ℝ => t^2) (2*x) x := by
    intro x _; simpa using hasDerivAt_pow 2 x
  have hpos : ∀ x ∈ Ioo (min (0:ℝ) 1) (max 0 1), 0 ≤ 2*x := by
    intro x hx; simp at hx; linarith [hx.1]
  have hC : IntervalIntegrable (fun x => ((fun t : ℝ => Real.log t / (1 - t)) ∘ (fun t => t^2)) x * (2*x))
      volume 0 1 := by
    rw [intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg hf hff' hpos]
    simpa using hA
  have hCv : (∫ x in (0:ℝ)..1, ((fun t : ℝ => Real.log t / (1 - t)) ∘ (fun t => t^2)) x * (2*x)) =
      -Real.pi ^ 2 / 6 := by
    rw [intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg hf hff' hpos]
    simpa using hAv
  have heq : ∀ x ∈ Set.uIcc (0:ℝ) 1, Real.log x / (1 + x) =
      Real.log x / (1 - x) - (1/2) * (((fun t : ℝ => Real.log t / (1 - t)) ∘ (fun t => t^2)) x * (2*x)) := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    simp only [Function.comp, Real.log_pow]
    rcases eq_or_lt_of_le hx.2 with h | h
    · subst h; simp
    · have h1 : 1 - x ≠ 0 := by linarith
      have h2 : 1 + x ≠ 0 := by linarith [hx.1]
      have h3 : 1 - x^2 ≠ 0 := by nlinarith [hx.1]
      field_simp
      push_cast
      ring
  have hint : IntervalIntegrable (fun x : ℝ => Real.log x / (1 - x) -
      (1/2) * (((fun t : ℝ => Real.log t / (1 - t)) ∘ (fun t => t^2)) x * (2*x))) volume 0 1 :=
    hA.sub (hC.const_mul _)
  constructor
  · exact hint.congr (fun x hx => (heq x (Set.uIoc_subset_uIcc hx)).symm) |>.mono_set le_rfl
  · rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_sub hA (hC.const_mul _),
      intervalIntegral.integral_const_mul, hAv, hCv]
    ring

/-- Exponential antiderivative for every nonzero complex slope. -/
@[dlmf 4.10.E8]
theorem exp_primitive (a : ℂ) (ha : a ≠ 0) (z : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (a * z) / a) (Complex.exp (a * z)) z := by
  convert (((hasDerivAt_id z).const_mul a).cexp).div_const a using 1
  · ext w
    simp only [id_eq]
  · simp only [id_eq, mul_one]
    field_simp

/-- Reciprocal exponential antiderivative, with the logarithm branch condition explicit. -/
@[dlmf 4.10.E9]
theorem inv_exp_add_primitive (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) {z : ℂ}
    (hz : Complex.exp (a * z) + b ∈ Complex.slitPlane) :
    HasDerivAt (fun z : ℂ => (a * z - Complex.log (Complex.exp (a * z) + b)) / (a * b))
      (1 / (Complex.exp (a * z) + b)) z := by
  have hz0 := Complex.slitPlane_ne_zero hz
  have he := ((hasDerivAt_id z).const_mul a).cexp
  have hl := (Complex.hasDerivAt_log hz).comp z (he.add_const b)
  convert (((hasDerivAt_id z).const_mul a).sub hl).div_const (a*b) using 1
  · ext w
    simp only [Pi.sub_apply, Function.comp_def, id_eq]
  · simp only [id_eq, mul_one]
    field_simp
    ring

/-- Hyperbolic exponential ratio antiderivative with its selected logarithm branch. -/
@[dlmf 4.10.E10]
theorem exp_ratio_primitive (a : ℂ) (ha : a ≠ 0) {z : ℂ}
    (hz : Complex.exp (a * z / 2) + Complex.exp (-a * z / 2) ∈ Complex.slitPlane) :
    HasDerivAt (fun z : ℂ => 2 / a *
      Complex.log (Complex.exp (a * z / 2) + Complex.exp (-a * z / 2)))
      ((Complex.exp (a * z) - 1) / (Complex.exp (a * z) + 1)) z := by
  let u := Complex.exp (a*z/2)
  let v := Complex.exp (-a*z/2)
  have huv : u*v=1 := by dsimp [u,v]; rw [← Complex.exp_add]; convert Complex.exp_zero using 1; congr 1; ring
  have hu2 : u^2=Complex.exp (a*z) := by
    dsimp [u]; rw [pow_two,← Complex.exp_add]; congr 1; ring
  have hne : u+v≠0 := Complex.slitPlane_ne_zero hz
  have hden : Complex.exp (a*z)+1≠0 := by
    intro hh
    have he : (u+v)*u=0 := by rw [add_mul,← pow_two,mul_comm v u,huv,hu2]; exact hh
    exact (mul_ne_zero hne (Complex.exp_ne_zero _)) he
  have hp := (((hasDerivAt_id z).const_mul a).div_const (2:ℂ)).cexp
  have hm := (((hasDerivAt_id z).const_mul (-a)).div_const (2:ℂ)).cexp
  have hd := ((Complex.hasDerivAt_log hz).comp z (hp.add hm)).const_mul (2/a)
  convert hd using 1
  · ext w
    simp only [Function.comp_def,id_eq,neg_mul,Pi.add_apply]
  · simp only [id_eq,mul_one]
    change (Complex.exp (a*z)-1)/(Complex.exp (a*z)+1)=2/a*((u+v)⁻¹*(u*(a/2)+v*(-a/2)))
    rw [← hu2]
    have hd2 : u^2+1≠0 := by rw [hu2]; exact hden
    field_simp [ha,hne,hd2]
    linear_combination 2*u*huv

/-- The finite Bose-type integral, including integrability at its removable endpoint. -/
@[dlmf 4.10.E12]
theorem integral_x_exp_div_exp_sub_one  :
    IntervalIntegrable (fun x : ℝ => x * Real.exp x / (Real.exp x - 1)) volume 0 (Real.log 2) ∧
    (∫ x in (0 : ℝ)..Real.log 2, x * Real.exp x / (Real.exp x - 1)) = Real.pi ^ 2 / 12 := by
  set g : ℝ → ℝ := fun u => DLMF.Polylog.dilogKernel (-u)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgc : Continuous fun x : ℝ => (g ∘ fun x => Real.exp x - 1) x * Real.exp x := by
    apply Continuous.mul _ Real.continuous_exp
    rw [continuous_iff_continuousAt]
    intro x
    apply ContinuousAt.comp (g := DLMF.Polylog.dilogKernel) _ (by fun_prop)
    apply DLMF.Polylog.continuousAt_dilogKernel
    simp only [neg_sub]; linarith [Real.exp_pos x]
  have hae : ∀ x ∈ Set.uIcc (0:ℝ) (Real.log 2), x ≠ 0 →
      x * Real.exp x / (Real.exp x - 1) = (g ∘ fun x => Real.exp x - 1) x * Real.exp x := by
    intro x _ hx
    have he : Real.exp x - 1 ≠ 0 := by
      intro h; apply hx; have := Real.exp_eq_one_iff x |>.mp (by linarith); exact this
    simp only [Function.comp, g]
    rw [DLMF.Polylog.dilogKernel_of_ne (by intro h; apply he; linarith)]
    rw [show 1 - -(Real.exp x - 1) = Real.exp x by ring, Real.log_exp]
    field_simp
  have hae' : ∀ᵐ x ∂volume, x ∈ Set.uIoc (0:ℝ) (Real.log 2) →
      x * Real.exp x / (Real.exp x - 1) = (g ∘ fun x => Real.exp x - 1) x * Real.exp x := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with x hx hx'
    exact hae x (Set.uIoc_subset_uIcc hx') (by simpa using hx)
  constructor
  · refine (hgc.intervalIntegrable _ _).congr_uIoo (fun x hx => ?_)
    have hx' : 0 < x ∧ x < Real.log 2 := by simpa [Set.uIoo, hl2.le] using hx
    refine (hae x ?_ hx'.1.ne').symm
    rw [Set.uIcc_of_le hl2.le]; exact ⟨hx'.1.le, hx'.2.le⟩
  · rw [intervalIntegral.integral_congr_ae hae']
    rw [intervalIntegral.integral_comp_mul_deriv' (fun x _ => (Real.hasDerivAt_exp x).sub_const 1)
      Real.continuous_exp.continuousOn]
    · simp only [Real.exp_zero, sub_self, Real.exp_log (by norm_num : (0:ℝ) < 2)]
      rw [show (2:ℝ) - 1 = 1 by norm_num]
      simp only [g]
      rw [intervalIntegral.integral_comp_neg (fun u => DLMF.Polylog.dilogKernel u),
        intervalIntegral.integral_symm, neg_zero]
      change -DLMF.Polylog.Real.dilog (-1) = _
      rw [DLMF.Polylog.Real.dilog_neg_one]; ring
    · rintro _ ⟨x, hx, rfl⟩
      rw [Set.uIcc_of_le hl2.le] at hx
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.comp (g := DLMF.Polylog.dilogKernel) _ (by fun_prop)
      apply DLMF.Polylog.continuousAt_dilogKernel
      have := Real.add_one_le_exp x
      linarith [hx.1]

/-- The convergent Fermi-type improper integral. -/
@[dlmf 4.10.E13]
theorem integral_inv_exp_add_one  :
    IntegrableOn (fun x : ℝ => 1 / (Real.exp x + 1)) (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), 1 / (Real.exp x + 1)) = Real.log 2 := by
  let F : ℝ → ℝ := fun x => -Real.log (1+Real.exp (-x))
  have hd (x : ℝ) : HasDerivAt F (1/(Real.exp x+1)) x := by
    have hx : 1+Real.exp (-x)≠0 := ne_of_gt (by positivity)
    have h := (((hasDerivAt_id x).neg.exp.const_add 1).log hx).neg
    convert h using 1
    · rfl
    · dsimp
      rw [Real.exp_neg]
      field_simp
  have ht : Tendsto F atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    have hs : Tendsto (fun x : ℝ => 1+Real.exp (-x)) atTop (𝓝 1) := by simpa using he.const_add 1
    have hl := (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp hs
    simpa [F] using hl.neg
  have hi := integrableOn_Ioi_deriv_of_nonneg' (a := 0) (fun x _ => hd x)
    (fun x _ => by positivity) ht
  refine ⟨hi,?_⟩
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0) (fun x _ => hd x)
    (fun x _ => by positivity) ht
  simpa [F,show (1:ℝ)+1=2 by norm_num] using he

end DLMF.Elementary
