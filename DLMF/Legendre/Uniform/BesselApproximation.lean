/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Uniform.HyperbolicEquation
public import DLMF.Legendre.IntegralRepresentations.Ferrers
public import DLMF.Bessel.ModifiedComparison.Asymptotics

/-!
# A uniform modified-Bessel approximation for associated Legendre P

The hyperbolic equation for `P^{-μ}_ν(coth u)` is an integrable perturbation of the
modified-Bessel equation of order `ν+1/2`. Its perturbation has total norm `|ν(ν+1)|`.
The recessive comparison bound gives a relative error at most `2|ν(ν+1)|/μ`, uniformly
for positive `u`, whenever `μ > max 1 (4|ν(ν+1)|)`. The inverse coordinate yields
DLMF 14.15.2 uniformly for every real `x > 1`.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Real Topology
@[expose] public noncomputable section

namespace DLMF.Legendre.HyperbolicAssociatedP
/-- The integrable difference between the hyperbolic Legendre and modified-Bessel potentials. -/
noncomputable def perturbation (ν u : ℝ) : ℂ :=
  -((ν*(ν+1)*(u⁻¹^2-(Real.sinh u)⁻¹^2) : ℝ) : ℂ)
/-- The Legendre comparison perturbation is absolutely integrable on the positive axis. -/
lemma integrableOn_perturbation (ν : ℝ) : IntegrableOn (perturbation ν) (Ioi 0) := by
  exact (Real.integrableOn_inv_sq_sub_inv_sinh_sq.const_mul (ν*(ν+1))).ofReal.neg
/-- The Legendre comparison perturbation is continuous on the positive axis. -/
lemma continuousOn_perturbation (ν : ℝ) : ContinuousOn (perturbation ν) (Ioi 0) := by
  intro u hu
  unfold perturbation
  have hs : Real.sinh u ≠ 0 := (Real.sinh_pos_iff.mpr hu).ne'
  have hr : ContinuousAt (fun u : ℝ => ν*(ν+1)*(u⁻¹^2-(Real.sinh u)⁻¹^2)) u :=
    (((continuousAt_id.inv₀ hu.ne').pow 2).sub
      ((Real.continuous_sinh.continuousAt.inv₀ hs).pow 2)).const_mul _
  exact (continuous_ofReal.continuousAt.comp hr).neg.continuousWithinAt
/-- The norm of the perturbation is a constant times the nonnegative hyperbolic remainder. -/
lemma norm_perturbation (ν : ℝ) {u : ℝ} (hu : 0 < u) :
    ‖perturbation ν u‖ = |ν*(ν+1)| *(u⁻¹^2-(Real.sinh u)⁻¹^2) := by
  simp only [perturbation, norm_neg, norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.inv_sq_sub_inv_sinh_sq_nonneg hu)]
/-- The total variation of the Legendre perturbation is `|ν(ν+1)|`. -/
lemma integral_norm_perturbation (ν : ℝ) :
    (∫ u in Ioi 0, ‖perturbation ν u‖) = |ν*(ν+1)| := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => norm_perturbation ν hu),
    integral_const_mul, Real.integral_Ioi_inv_sq_sub_inv_sinh_sq, mul_one]
/-- The Bessel potential plus its perturbation equals the hyperbolic Legendre potential. -/
lemma potential_eq (ν μ : ℝ) {u : ℝ} (hu : 0 < u) :
    ((μ^2+((ν+1/2)^2-1/4)/u^2 : ℝ) : ℂ) + perturbation ν u =
      (μ : ℂ)^2+(ν : ℂ)*(ν+1)/(Real.sinh u : ℂ)^2 := by
  have hs : (Real.sinh u : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr hu).ne'
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  simp only [perturbation, ofReal_add, ofReal_sub, ofReal_pow, ofReal_mul, ofReal_div,
    ofReal_neg, ofReal_inv, ofReal_one, ofReal_ofNat]
  field_simp
  ring
/-- The real coordinate `u = arcoth x` is positive for `x > 1`. -/
lemma coordinate_pos {x : ℝ} (hx : 1 < x) : 0 < legendreUCoordinate x := by
  unfold legendreUCoordinate
  have hd : 0 < x-1 := by linarith
  have hr : 1 < (x+1)/(x-1) := (lt_div_iff₀ hd).mpr (by linarith)
  exact mul_pos (by norm_num) (Real.log_pos hr)
/-- The hyperbolic cotangent inverts the Legendre coordinate for `x > 1`. -/
lemma coth_coordinate {x : ℝ} (hx : 1 < x) :
    Real.cosh (legendreUCoordinate x) / Real.sinh (legendreUCoordinate x) = x := by
  have h := LaplaceIntegrals.sqrt_mul_cosh_sinh_arcothEndpoint hx
  change Real.sqrt (x^2-1)*Real.cosh (legendreUCoordinate x)=x ∧
    Real.sqrt (x^2-1)*Real.sinh (legendreUCoordinate x)=1 at h
  have hs : Real.sinh (legendreUCoordinate x) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (coordinate_pos hx)).ne'
  apply (div_eq_iff hs).mpr
  linear_combination Real.sinh (legendreUCoordinate x)*h.1 -
    Real.cosh (legendreUCoordinate x)*h.2
/-- The scaling that matches the Legendre solution to the recessive Bessel solution. -/
noncomputable def normalization (μ : ℝ) : ℂ :=
  Gamma (1+μ) * (Real.sqrt π / Real.sqrt 2 / Real.sqrt μ : ℝ)
/-- The comparison normalization is nonzero for positive order magnitude. -/
lemma normalization_ne_zero {μ : ℝ} (hμ : 0 < μ) : normalization μ ≠ 0 := by
  have hr : ∀ k : ℕ, (1+(μ : ℂ)) ≠ -(k : ℂ) := by
    intro k hk
    have he := congrArg re hk
    simp only [add_re, one_re, ofReal_re, neg_re, natCast_re] at he
    linarith [Nat.cast_nonneg (α := ℝ) k]
  exact mul_ne_zero (Gamma_ne_zero hr) (ofReal_ne_zero.mpr
    (div_ne_zero (div_ne_zero (Real.sqrt_pos.mpr Real.pi_pos).ne'
      (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne')
      (Real.sqrt_pos.mpr hμ).ne'))
/-- Scaling the DLMF leading term gives the recessive modified-Bessel solution. -/
lemma normalization_mul_leading {μ u : ℝ} (hμ : 0 < μ) (hu : 0 < u) (ν : ℝ) :
    normalization μ * (1/Gamma (μ+1) * (2*μ*u/π : ℂ)^(1/2 : ℂ) *
      DLMF.Bessel.besselK (ν+1/2) (μ*u)) =
        DLMF.Bessel.ModifiedComparison.recessive (ν+1/2) μ u := by
  have hr : ∀ k : ℕ, (1+(μ : ℂ)) ≠ -(k : ℂ) := by
    intro k hk
    have he := congrArg re hk
    simp only [add_re, one_re, ofReal_re, neg_re, natCast_re] at he
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hΓ := Gamma_ne_zero hr
  have he : (Real.sqrt π / Real.sqrt 2 / Real.sqrt μ : ℂ) *
      (2*μ*u/π : ℂ)^(1/2 : ℂ) = (Real.sqrt u : ℂ) := by

    have hp := (Complex.ofReal_cpow (x := 2*μ*u/π) (by positivity) (1/2)).symm
    simp only [ofReal_mul, ofReal_div, ofReal_ofNat, ofReal_one] at hp
    rw [hp, ← Real.sqrt_eq_rpow, ← ofReal_div, ← ofReal_div, ← ofReal_mul]
    apply congrArg ofReal
    rw [Real.sqrt_div, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    · field_simp
    · positivity
  simp only [normalization, DLMF.Bessel.ModifiedComparison.recessive, ofReal_div]
  rw [show (μ:ℂ)+1=1+μ by ring]
  calc _ = ((Real.sqrt π / Real.sqrt 2 / Real.sqrt μ : ℂ) *
      (2*μ*u/π : ℂ)^(1/2 : ℂ)) * DLMF.Bessel.besselK (ν+1/2) (μ*u) := by
        field_simp
    _ = _ := by rw [he]; congr 2 <;> push_cast <;> ring
/-- A uniform relative-error bound for positive order exceeding `max 1 (4|ν(ν+1)|)`. -/
lemma norm_ratio_le {ν μ u : ℝ} (hν : -1/2 ≤ ν)
    (hμ : max 1 (4*|ν*(ν+1)|) < μ) (hu : 0 < u) :
    ‖value ν μ u / (1/Gamma (μ+1) * (2*μ*u/π : ℂ)^(1/2 : ℂ) *
      DLMF.Bessel.besselK (ν+1/2) (μ*u)) - 1‖ ≤ 2*|ν*(ν+1)|/μ := by
  have hμ0 : 0 < μ := lt_trans (by positivity) (lt_of_le_of_lt (le_max_left _ _) hμ)
  have hμA : 4*|ν*(ν+1)| < μ := lt_of_le_of_lt (le_max_right _ _) hμ
  have ht0 : 0 ≤ |ν*(ν+1)|/μ := div_nonneg (abs_nonneg _) hμ0.le
  have ht1 : abs (abs (ν*(ν+1))/μ) ≤ 1 := by
    rw [abs_of_nonneg ht0, div_le_iff₀ hμ0]
    nlinarith [abs_nonneg (ν*(ν+1))]
  have hE : Real.exp (|ν*(ν+1)|/μ)-1 ≤ 2*|ν*(ν+1)|/μ := by
    have he := Real.abs_exp_sub_one_le ht1
    rw [abs_of_nonneg ht0] at he
    exact (le_abs_self _).trans (by simpa only [mul_div_assoc] using he)
  have hsmall : Real.exp ((∫ t in Ioi 0, ‖perturbation ν t‖)/μ)-1 < 1 := by
    rw [integral_norm_perturbation]
    refine lt_of_le_of_lt hE ?_
    rw [div_lt_one hμ0]
    nlinarith [abs_nonneg (ν*(ν+1))]
  let f : ℝ → ℂ := fun u => normalization μ * value ν μ u
  let f' : ℝ → ℂ := fun u => normalization μ * firstDerivative ν μ u
  have hf : ∀ u, 0 < u → HasDerivAt f (f' u) u := by
    intro u hu
    exact (hasDerivAt_value ν μ hu).const_mul (normalization μ)
  have hf' : ∀ u, 0 < u → HasDerivAt f'
      ((((μ^2+((ν+1/2)^2-1/4)/u^2 : ℝ) : ℂ) + perturbation ν u) * f u) u := by
    intro u hu
    rw [potential_eq ν μ hu]
    convert (hasDerivAt_firstDerivative ν μ hu).const_mul (normalization μ) using 1
    dsimp only [f]
    ring
  have hfn : Tendsto (fun u : ℝ => exp ((μ:ℂ)*u) * f u) atTop
      (𝓝 ((Real.sqrt π / Real.sqrt 2 / Real.sqrt μ : ℝ) : ℂ)) := by
    have ht := (tendsto_exp_mul_value ν hμ0).const_mul (normalization μ)
    have hΓ : Gamma (1+(μ:ℂ)) ≠ 0 := by
      intro he
      have hc := normalization_ne_zero hμ0
      apply hc
      simp [normalization, he]
    have hv : normalization μ * (1/Gamma (1+μ)) =
        ((Real.sqrt π / Real.sqrt 2 / Real.sqrt μ : ℝ) : ℂ) := by
      simp only [normalization]
      field_simp
    rw [hv] at ht
    convert ht using 1
    funext u
    simp only [f]
    ring
  have hb := DLMF.Bessel.ModifiedComparison.norm_div_recessive_sub_one_le
    (by linarith : 0 ≤ ν+1/2) hμ0 (continuousOn_perturbation ν)
    (integrableOn_perturbation ν) hsmall hf hf'
    (by simpa [f] using (tendsto_value_zero ν hμ0).const_mul (normalization μ))
    (by simpa [f'] using (tendsto_firstDerivative_zero ν hμ0).const_mul (normalization μ)) hfn hu
  rw [← normalization_mul_leading hμ0 hu ν] at hb
  simp only [f, mul_div_mul_left _ _ (normalization_ne_zero hμ0)] at hb
  refine hb.trans (le_trans ?_ hE)
  apply sub_le_sub_right (Real.exp_le_exp.mpr ?_) 1
  apply div_le_div_of_nonneg_right ?_ hμ0.le
  rw [← integral_norm_perturbation ν]
  exact setIntegral_mono_set (integrableOn_perturbation ν).norm
    (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun _ h => hu.trans h)
/-- The uniform modified-Bessel approximation for fixed real degree, DLMF 14.15.2. -/
lemma isBigO_associatedP_large_order {ν : ℝ} (hν : -1/2 ≤ ν) :
    (fun p : ℝ × ℝ => associatedP ν (-p.1)
        p.2/(1/Gamma (p.1+1)*(2*p.1*legendreUCoordinate p.2/π:ℂ)^(1/2:ℂ)*
        DLMF.Bessel.besselK (ν+1/2) (p.1*legendreUCoordinate p.2))-1)
      =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 1 < p.2}]
        (fun p : ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  refine IsBigO.of_bound (2*|ν*(ν+1)|) ?_
  have ht : ∀ᶠ p : ℝ × ℝ in comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 1 < p.2},
      max 1 (4*|ν*(ν+1)|) < p.1 ∧ 1 < p.2 :=
    ((tendsto_comap.eventually (eventually_gt_atTop _)).filter_mono inf_le_left).and
      (mem_inf_of_right (mem_principal_self _))
  filter_upwards [ht] with p hp
  have hb := norm_ratio_le hν hp.1 (coordinate_pos hp.2)
  have hμ : 0 < p.1 := lt_trans (by norm_num) (lt_of_le_of_lt (le_max_left _ _) hp.1)
  simp only [value, ← ofReal_div, coth_coordinate hp.2] at hb
  simpa only [norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos hμ,
    div_eq_mul_inv] using hb
end DLMF.Legendre.HyperbolicAssociatedP
