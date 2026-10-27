/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.ArgumentContinuation

/-!
# Euler's Gauss integral on the positive half-line

The substitution `v = 1 / (1 + u)` transfers the continued Euler integral
and its absolute integrability to the positive half-line. Mathlib's Jacobian
change-of-variables theorem handles the decreasing substitution and its endpoints.
-/

@[expose] public section
open Complex MeasureTheory Set
open scoped Real
noncomputable section
namespace DLMF.Hypergeometric

/-- The half-line form of Euler's Gauss kernel. -/
def eulerHalfLineKernel (p a d z : ℂ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (p - a - d) * (z + u) ^ (-p)

/-- The Euler half-line kernel is absolutely integrable and evaluates to the continued
Gauss function for every exponent `p`, with positive endpoint exponents `a,d`. -/
theorem eulerHalfLine_integrable_integral {p a d z : ℂ}
    (ha : 0 < a.re) (hd : 0 < d.re) (hz : 0 < z.re) :
    IntegrableOn (eulerHalfLineKernel p a d z) (Ioi 0) ∧
      (∫ u : ℝ in Ioi 0, eulerHalfLineKernel p a d z u) =
        Gamma a * Gamma d * regularizedGaussHG p d (a + d) (1 - z) := by
  let f : ℝ → ℝ := fun u => 1 / (1 + u)
  let f' : ℝ → ℝ := fun u => -1 / (1 + u) ^ 2
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt f (f' u) (Ioi 0) u := by
    intro u hu
    have hd0 : 1 + u ≠ 0 := ne_of_gt (by linarith [mem_Ioi.mp hu])
    have h := (hasDerivAt_const u (1 : ℝ)).div ((hasDerivAt_id u).const_add 1) hd0
    change HasDerivAt f _ u at h
    convert h.hasDerivWithinAt using 1
    simp [f']
  have hinj : InjOn f (Ioi 0) := by
    intro u hu v hv he
    dsimp [f] at he
    have h := inv_injective (by simpa only [one_div] using he)
    linarith
  have himage : f '' Ioi 0 = Ioo 0 1 := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu0 : 0 < u := hu
      refine ⟨by dsimp [f]; positivity, ?_⟩
      dsimp [f]
      rw [div_lt_one (by linarith)]; linarith
    · rintro ⟨hv0, hv1⟩
      refine ⟨v⁻¹ - 1, ?_, ?_⟩
      · change 0 < v⁻¹ - 1
        have := (one_lt_inv₀ hv0).mpr hv1
        linarith
      · dsimp [f]; field_simp; ring
  have hw : 1 - z ∈ cutPlane := by
    change 1 - (1 - z) ∈ slitPlane
    rw [sub_sub_cancel]
    exact Or.inl hz
  let K : ℝ → ℂ := eulerKernel p d (a + d) (1 - z)
  have hi : IntegrableOn K (Ioo 0 1) := by
    have h := intervalIntegrable_eulerKernel (a := p) (b := d) (c := a + d) hd
      (by simpa using ha) hw
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
      integrableOn_Ioc_iff_integrableOn_Ioo] at h
    exact h
  have hker (u : ℝ) (hu : u ∈ Ioi 0) :
      |f' u| • K (f u) = eulerHalfLineKernel p a d z u := by
    have hu0 : 0 < u := hu
    have hu1 : 0 < 1 + u := by linarith
    have hzu : z + (u : ℂ) ≠ 0 := by
      apply slitPlane_ne_zero; left; simp; linarith
    have hcpow (t : ℝ) (ht : 0 < t) (s : ℂ) :
        (t : ℂ) ^ s = exp (Real.log t * s) := by
      rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht.ne'), ofReal_log ht.le]
    have hf0 : 0 < f u := by dsimp [f]; positivity
    have h1f : 1 - f u = u / (1 + u) := by dsimp [f]; field_simp; ring
    have hlogf : Real.log (f u) = -Real.log (1 + u) := by simp [f, Real.log_inv]
    have hlog1f : Real.log (1 - f u) = Real.log u - Real.log (1 + u) := by
      rw [h1f, Real.log_div hu0.ne' hu1.ne']
    have hlogz : log (1 - (1 - z) * (f u : ℂ)) = log (z + u) - Real.log (1 + u) := by
      rw [show 1 - (1 - z) * (f u : ℂ) = (z + u) * ((1 + u : ℝ)⁻¹ : ℂ) by
        dsimp [f]; push_cast; field_simp [show 1 + (u : ℂ) ≠ 0 by exact_mod_cast hu1.ne']; ring,
        ← ofReal_inv, log_mul_ofReal _ (inv_pos.mpr hu1) _ hzu, Real.log_inv, ofReal_neg]
      ring
    have hw0 : 1 - (1 - z) * (f u : ℂ) ≠ 0 :=
      slitPlane_ne_zero (one_sub_mul_mem_slitPlane hw ⟨hf0.le, le_of_lt (by
        dsimp [f]; rw [div_lt_one hu1]; linarith)⟩)
    have habs : |f' u| = Real.exp (-2 * Real.log (1 + u)) := by
      dsimp only [f']
      rw [neg_div, abs_neg, abs_of_pos (by positivity : 0 < 1 / (1 + u) ^ 2),
        show -2 * Real.log (1 + u) = -(Real.log (1 + u) + Real.log (1 + u)) by ring,
        Real.exp_neg, Real.exp_add, Real.exp_log hu1]
      ring
    dsimp only [K, eulerKernel, eulerHalfLineKernel]
    rw [show 1 - (f u : ℂ) = ((1 - f u : ℝ) : ℂ) by push_cast; rfl,
      hcpow _ hf0, hcpow _ (by rw [h1f]; positivity),
      show 1 + (u : ℂ) = ((1 + u : ℝ) : ℂ) by push_cast; rfl,
      hcpow _ hu1, hcpow _ hu0, cpow_def_of_ne_zero hw0, cpow_def_of_ne_zero hzu,
      hlogz, habs, Complex.real_smul, ofReal_exp, hlogf, hlog1f]
    simp only [← exp_add]
    congr 1
    push_cast
    ring
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj K
  have hcovI := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj K
  rw [himage] at hcov hcovI
  refine ⟨(hcovI.mp hi).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu; exact hker u hu), ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hker, ← hcov]
  have hg := regularizedGaussHG_eq_regularizedGaussHGIntegral (a := p) hd
    (show 0 < (a + d - d).re by simpa using ha) hw
  rw [regularizedGaussHGIntegral, show a + d - d = a by ring,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hg
  rw [hg]
  have hG := mul_ne_zero (Gamma_ne_zero_of_re_pos ha) (Gamma_ne_zero_of_re_pos hd)
  dsimp only [K]
  field_simp [Gamma_ne_zero_of_re_pos ha, Gamma_ne_zero_of_re_pos hd]

end DLMF.Hypergeometric
