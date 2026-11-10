/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Asymptotics.RealRemainders
public import DLMF.Confluent.Integrals.Stieltjes

/-!
# Tricomi kernels for the Airy Stieltjes representation

Kummer's transformation expresses `Ai` through `U(1/6,1/3,2ζ)` throughout the sector
`|arg z| < 2π/3`. The self-Stieltjes representation of this Tricomi function and the
substitution `u = (4/3)t^(3/2)` give the kernel and prefactors of DLMF 9.10.18.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory DLMF.Confluent
open scoped Real Topology

namespace DLMF.Airy
namespace StieltjesRepresentation

/-- Constant in the `U(1/6,1/3,2ζ)` representation of the Airy function. -/
def normalization : ℂ :=
  (3 : ℂ) ^ (-1 / 6 : ℂ) * exp (-(2 / 3) * log 2) / Real.sqrt π

/-- The Airy function in terms of the self-Stieltjes Tricomi kernel, on `|arg z| < 2π/3`. -/
theorem airyAi_eq_tricomi {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyAi z = normalization * exp (-airyZetaComplex z) *
      kummerU (1 / 6) (1 / 3) (2 * airyZetaComplex z) := by
  have hs0 : 2 * airyZetaComplex z ≠ 0 := by
    rw [← exp_log_two_add_airyLogZeta hz0]; exact exp_ne_zero _
  rw [airyAi_eq_kummerU hz0 hz, kummerU_kummer_transform_all _ _ hs0,
    StieltjesBounds.two_zeta_cpow hz0 hz]
  have ha : (5 / 6 - 5 / 3 + 1 : ℂ) = 1 / 6 := by ring
  have hb : (2 - 5 / 3 : ℂ) = 1 / 3 := by ring
  rw [ha, hb]
  have hE : exp (2 / 3 * airyLogZeta z - airyZetaComplex z) *
      exp ((1 - 5 / 3) * (log 2 + airyLogZeta z)) =
      exp (-(2 / 3) * log 2) * exp (-airyZetaComplex z) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  unfold normalization
  linear_combination ((3 : ℂ) ^ (-1 / 6 : ℂ) / Real.sqrt π *
    kummerU (1 / 6) (1 / 3) (2 * airyZetaComplex z)) * hE

/-- The doubled Airy variable lies in the principal slit plane on `|arg z| < 2π/3`. -/
theorem two_zeta_mem_slitPlane {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    2 * airyZetaComplex z ∈ slitPlane := by
  rw [← exp_log_two_add_airyLogZeta hz0]
  apply expOpenPartialHomeomorph.map_source'
  change -π < (log 2 + airyLogZeta z).im ∧ (log 2 + airyLogZeta z).im < π
  rw [im_log_two_add_airyLogZeta]
  constructor <;> linarith [abs_lt.mp hz]

/-- The positive-axis Tricomi factor normalized to `exp(ζ) Ai`. -/
theorem normalization_mul_tricomi {t : ℝ} (ht : 0 < t) :
    normalization * kummerU (1 / 6) (1 / 3) (2 * airyZetaComplex t) =
      exp (airyZeta t) * airyAi t := by
  have ha := airyAi_eq_tricomi (ofReal_ne_zero.mpr ht.ne') (by
    rw [arg_ofReal_of_nonneg ht.le, abs_zero]; positivity)
  rw [ha, RealRemainders.zeta_ofReal ht]
  symm
  calc _ = normalization * (exp (airyZeta t) * exp (-(airyZeta t : ℂ))) *
      kummerU (1 / 6) (1 / 3) (2 * (airyZeta t : ℂ)) := by ring
    _ = _ := by rw [← exp_add]; simp

/-- The substitution `u = (4/3)t^(3/2)` converts the Tricomi Stieltjes kernel to Airy form. -/
theorem transformed_kernel {z : ℂ} {t : ℝ} (ht : 0 < t) :
    normalization * (2 * (t : ℂ) ^ (1 / 2 : ℂ)) *
      (kummerU (1 / 6) (1 / 3) ((4 / 3 : ℂ) * (t : ℂ) ^ (3 / 2 : ℂ)) *
        exp (-((4 / 3 : ℂ) * (t : ℂ) ^ (3 / 2 : ℂ))) *
        ((4 / 3 : ℂ) * (t : ℂ) ^ (3 / 2 : ℂ)) ^ (-5 / 6 : ℂ) /
          ((4 / 3 : ℂ) * (t : ℂ) ^ (3 / 2 : ℂ) + 2 * airyZetaComplex z)) =
    (3 / 2 : ℂ) * (4 / 3 : ℂ) ^ (-5 / 6 : ℂ) *
      ((t : ℂ) ^ (-3 / 4 : ℂ) * exp (-(airyZeta t : ℂ)) *
        airyAi t / (z ^ (3 / 2 : ℂ) + (t : ℂ) ^ (3 / 2 : ℂ))) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have htpow : ((t : ℂ) ^ (3 / 2 : ℂ)) ^ (-5 / 6 : ℂ) =
      (t : ℂ) ^ (-5 / 4 : ℂ) := by
    rw [← cpow_mul]
    · congr 1; ring
    · simp [mul_im, log_im, arg_ofReal_of_nonneg ht.le, Real.pi_pos]
    · simp [mul_im, log_im, arg_ofReal_of_nonneg ht.le, Real.pi_pos.le]
  have hp : ((4 / 3 : ℂ) * (t : ℂ) ^ (3 / 2 : ℂ)) ^ (-5 / 6 : ℂ) =
      (4 / 3 : ℂ) ^ (-5 / 6 : ℂ) * (t : ℂ) ^ (-5 / 4 : ℂ) := by
    have hmul := mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3)
      (Real.rpow_nonneg ht.le (3 / 2)) (-5 / 6 : ℂ)
    have hcast : ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) = (t : ℂ) ^ (3 / 2 : ℂ) := by
      convert ofReal_cpow ht.le (3 / 2) using 1
      push_cast
      ring
    norm_num only [ofReal_div, ofReal_ofNat] at hmul
    simp only [← neg_div] at hmul
    rw [hcast, htpow] at hmul
    exact hmul
  have hu : (4 / 3 : ℂ) * (t : ℂ) ^ (3 / 2 : ℂ) = 2 * airyZetaComplex t := by
    unfold airyZetaComplex; ring
  have he : normalization *
      kummerU (1 / 6) (1 / 3) ((4 / 3 : ℂ) * (t : ℂ) ^ (3 / 2 : ℂ)) *
        exp (-((4 / 3 : ℂ) * (t : ℂ) ^ (3 / 2 : ℂ))) =
        exp (-(airyZeta t : ℂ)) * airyAi t := by
    rw [hu, normalization_mul_tricomi ht, RealRemainders.zeta_ofReal ht]
    calc _ = (exp (airyZeta t) * exp (-(2 * (airyZeta t : ℂ)))) * airyAi t := by ring
      _ = _ := by rw [← exp_add]; congr 2; ring
  rw [hp]
  have hm : (t : ℂ) ^ (1 / 2 : ℂ) * (t : ℂ) ^ (-5 / 4 : ℂ) =
      (t : ℂ) ^ (-3 / 4 : ℂ) := by
    rw [← cpow_add _ _ ht0]; congr 1; ring
  have hd : (4 / 3 : ℂ) * (t : ℂ) ^ (3 / 2 : ℂ) + 2 * airyZetaComplex z =
      (4 / 3 : ℂ) * (z ^ (3 / 2 : ℂ) + (t : ℂ) ^ (3 / 2 : ℂ)) := by
    unfold airyZetaComplex; ring
  rw [hd]
  calc _ = (3 / 2 : ℂ) * (4 / 3 : ℂ) ^ (-5 / 6 : ℂ) *
      (((t : ℂ) ^ (1 / 2 : ℂ) * (t : ℂ) ^ (-5 / 4 : ℂ)) *
        (normalization * kummerU (1 / 6) (1 / 3)
          ((4 / 3 : ℂ) * (t : ℂ) ^ (3 / 2 : ℂ)) *
            exp (-((4 / 3 : ℂ) * (t : ℂ) ^ (3 / 2 : ℂ)))) /
          (z ^ (3 / 2 : ℂ) + (t : ℂ) ^ (3 / 2 : ℂ))) := by simp only [div_mul_eq_div_div]; ring
    _ = _ := by rw [hm, he]; ring

/-- The self-Stieltjes kernel for `U(1/6,1/3,w)` on the positive half-line. -/
def tricomiKernel (w : ℂ) (t : ℝ) : ℂ :=
  kummerU (1 / 6) (1 / 3) t * exp (-(t : ℂ)) * (t : ℂ) ^ (-5 / 6 : ℂ) /
    ((t : ℂ) + w)

/-- The Airy Stieltjes kernel in DLMF 9.10.18, with principal complex powers. -/
def airyKernel (z : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (-3 / 4 : ℂ) * exp (-(airyZeta t : ℂ)) * airyAi t /
    (z ^ (3 / 2 : ℂ) + (t : ℂ) ^ (3 / 2 : ℂ))

/-- Change of variables from the self-Stieltjes Tricomi integral to the Airy integral. -/
theorem integral_kernel_transform (z : ℂ) :
    normalization * (∫ t : ℝ in Ioi 0, tricomiKernel (2 * airyZetaComplex z) t) =
      (3 / 2 : ℂ) * (4 / 3 : ℂ) ^ (-5 / 6 : ℂ) *
        ∫ t : ℝ in Ioi 0, airyKernel z t := by
  have hs := integral_comp_mul_left_Ioi (tricomiKernel (2 * airyZetaComplex z)) 0
    (b := (4 / 3 : ℝ)) (by norm_num)
  rw [mul_zero, Complex.real_smul] at hs
  have hp := integral_comp_rpow_Ioi_of_pos
    (g := fun s : ℝ => tricomiKernel (2 * airyZetaComplex z) ((4 / 3 : ℝ) * s))
    (p := (3 / 2 : ℝ)) (by norm_num)
  have hpoint : ∀ t ∈ Ioi (0 : ℝ), normalization * (4 / 3 : ℂ) *
      (((3 / 2 : ℝ) * t ^ ((3 / 2 : ℝ) - 1)) •
        tricomiKernel (2 * airyZetaComplex z) ((4 / 3 : ℝ) * t ^ (3 / 2 : ℝ))) =
      (3 / 2 : ℂ) * (4 / 3 : ℂ) ^ (-5 / 6 : ℂ) * airyKernel z t := by
    intro t ht
    have hc : ∀ q : ℝ, ((t ^ q : ℝ) : ℂ) = (t : ℂ) ^ (q : ℂ) := ofReal_cpow ht.le
    simp only [tricomiKernel, airyKernel, Complex.real_smul, ofReal_mul, ofReal_div,
      ofReal_ofNat, hc, ofReal_sub, ofReal_one]
    rw [show (3 / 2 - 1 : ℂ) = 1 / 2 by ring]
    convert transformed_kernel (z := z) ht using 1
    ring
  calc _ = normalization * (4 / 3 : ℂ) *
        ∫ s : ℝ in Ioi 0, tricomiKernel (2 * airyZetaComplex z) ((4 / 3 : ℝ) * s) := by
          rw [hs]; push_cast; ring
    _ = normalization * (4 / 3 : ℂ) *
        ∫ t : ℝ in Ioi 0, ((3 / 2 : ℝ) * t ^ ((3 / 2 : ℝ) - 1)) •
          tricomiKernel (2 * airyZetaComplex z) ((4 / 3 : ℝ) * t ^ (3 / 2 : ℝ)) := by rw [hp]
    _ = _ := by
      rw [← integral_const_mul, setIntegral_congr_fun measurableSet_Ioi hpoint,
        integral_const_mul]

/-- Euler reflection at `1/6`: `Γ(1/6) Γ(5/6) = 2π`. -/
theorem gamma_sixth_mul_five_sixths :
    Gamma (1 / 6 : ℂ) * Gamma (5 / 6 : ℂ) = 2 * π := by
  have hg := Gamma_mul_Gamma_one_sub (1 / 6 : ℂ)
  rw [show (1 - 1 / 6 : ℂ) = 5 / 6 by ring,
    show (π : ℂ) * (1 / 6) = ((π / 6 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_sin, Real.sin_pi_div_six] at hg
  rw [hg]; push_cast; ring

/-- The Tricomi self-Stieltjes representation evaluated at the doubled Airy variable. -/
theorem kummerU_eq_stieltjes {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    kummerU (1 / 6) (1 / 3) (2 * airyZetaComplex z) =
      (2 * airyZetaComplex z) ^ (5 / 6 : ℂ) / (2 * π) *
        ∫ t : ℝ in Ioi 0, tricomiKernel (2 * airyZetaComplex z) t := by
  have hs := kummerU_stieltjes (a := 1 / 6) (b := 1 / 3)
    (two_zeta_mem_slitPlane hz0 hz) (by norm_num) (by norm_num)
  rw [show (1 - 1 / 6 : ℂ) = 5 / 6 by ring,
    show (1 + 1 / 6 - 1 / 3 : ℂ) = 5 / 6 by ring,
    gamma_sixth_mul_five_sixths,
    show (1 / 3 - 1 / 6 : ℂ) = 1 / 6 by ring,
    show (1 / 6 - 1 : ℂ) = -5 / 6 by ring] at hs
  exact hs

/-- The principal-power prefactors in the Tricomi change of variables reduce to `z^(5/4)`. -/
theorem cpow_normalization {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    (2 * airyZetaComplex z) ^ (5 / 6 : ℂ) * (4 / 3 : ℂ) ^ (-5 / 6 : ℂ) =
      z ^ (5 / 4 : ℂ) := by
  have hlog : log (4 / 3 : ℂ) = log 2 + log (2 / 3 : ℂ) := by
    rw [show (4 / 3 : ℂ) = (2 : ℝ) * (2 / 3 : ℂ) by push_cast; ring,
      log_ofReal_mul (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 / 3 : ℂ) ≠ 0)]
    norm_cast
  rw [StieltjesBounds.two_zeta_cpow hz0 hz,
    cpow_def_of_ne_zero (by norm_num : (4 / 3 : ℂ) ≠ 0),
    cpow_def_of_ne_zero hz0, ← exp_add, hlog, airyLogZeta]
  congr 1; ring

end StieltjesRepresentation
end DLMF.Airy
