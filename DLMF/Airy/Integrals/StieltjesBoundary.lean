/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Integrals.StieltjesRepresentation
public import DLMFMathlib.Analysis.Integral.CauchyBoundary
import DLMF.Airy.Integrals.HalfLineLaplace

/-!
# Boundary reduction of the Airy Stieltjes transform

The self-Stieltjes kernel of `U(1/6,1/3,z)`, after positive dilation and the substitution
`t ↦ t^(3/2)`, gives the Airy principal-value kernel of DLMF 9.10.19. The finite part
is unchanged because the transformed excision widths have ratio tending to one.

The proof reuses the project's Tricomi integral, Airy normalization and convergent Airy
principal value. Signed Cauchy boundary limits and the Airy connection formula cancel
the imaginary residue terms. The changes of variables use Mathlib's real-power substitutions.

## Main results

* `BiStieltjes.density_change_variable`: the exact density normalization.
* `BiStieltjes.finitePart_relation`: the finite part equals the Airy principal value.
* `airyBi_stieltjes_principalValue`: the evaluated representation (DLMF 9.10.19).
-/

public noncomputable section

open Complex Filter Set MeasureTheory DLMF.Confluent
open scoped Real Topology

set_option maxHeartbeats 800000
namespace DLMF.Airy.BiStieltjes
local notation "density" => tricomiLaplaceKernel (1 / 6) (1 / 6) (1 / 3) 1

/-- The self-Stieltjes Tricomi density is absolutely integrable on the positive axis. -/
lemma integrableOn_density : IntegrableOn density (Ioi 0) :=
  (laplace_kummerU_gauss (by norm_num) (by norm_num) (by norm_num)).1

/-- The self-Stieltjes Tricomi density is differentiable at each positive real point. -/
lemma differentiableAt_density {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ density t := by
  have hslit : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht
  have hU := (hasDerivAt_kummerU (1 / 6) (1 / 3) hslit).comp_ofReal
  unfold tricomiLaplaceKernel
  have hE : DifferentiableAt ℝ (fun u : ℝ => exp (-(1 : ℂ) * u)) t := by fun_prop
  have hP : DifferentiableAt ℝ (fun u : ℝ => (u : ℂ) ^ (1 / 6 - 1 : ℂ)) t :=
    by
      have h := (Complex.hasStrictDerivAt_cpow_const (c := (1 / 6 - 1 : ℂ)) hslit).hasDerivAt
      exact h.comp_ofReal.differentiableAt
  exact (hE.mul hP).mul hU.differentiableAt


local notation "scaledDensity" => (fun t : ℝ => density ((4 / 3 : ℝ) * t))
local notation "normalization" => StieltjesRepresentation.normalization
local notation "conversion" => ((3 / 2 : ℂ) * (4 / 3 : ℂ) ^ (-5 / 6 : ℂ))
local notation "principalKernel" => (fun x t : ℝ =>
  (t : ℂ) ^ (-3 / 4 : ℂ) * exp (-(airyZeta t : ℂ)) * airyAi t /
    ((x : ℂ) ^ (3 / 2 : ℂ) - (t : ℂ) ^ (3 / 2 : ℂ)))
local notation "jacobianKernel" => (fun x t : ℝ =>
  ((3 / 2 : ℝ) * t ^ ((3 / 2 : ℝ) - 1)) •
    (scaledDensity (t ^ (3 / 2 : ℝ)) /
      (Complex.ofReal (t ^ (3 / 2 : ℝ)) - Complex.ofReal (x ^ (3 / 2 : ℝ)))))
local notation "finitePart" => (fun c : ℝ =>
  (∫ t in 0..2 * c, (scaledDensity t - scaledDensity c) / ((t : ℂ) - c)) +
    ∫ t in Ioi (2 * c), scaledDensity t / ((t : ℂ) - c))


/-- Positive dilation preserves integrability of the self-Stieltjes density. -/
lemma integrableOn_scaledDensity : IntegrableOn scaledDensity (Ioi 0) := by
  apply (integrableOn_Ioi_comp_mul_left_iff density 0 (by norm_num : (0 : ℝ) < 4 / 3)).mpr
  simpa only [mul_zero] using integrableOn_density

/-- The dilated density is differentiable at each positive real point. -/
lemma differentiableAt_scaledDensity {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ scaledDensity t := by
  exact (differentiableAt_density (by positivity : 0 < (4 / 3 : ℝ) * t)).comp t
    (by fun_prop : DifferentiableAt ℝ (fun u : ℝ => (4 / 3 : ℝ) * u) t)

/-- Dilation puts the self-Stieltjes kernel in the Airy normalization. -/
lemma integral_scaledDensity_div_add (w : ℂ) :
    (∫ s in Ioi 0, scaledDensity s / ((s : ℂ) + w)) =
      ∫ u in Ioi 0, density u / ((u : ℂ) + (4 / 3 : ℂ) * w) := by
  have hs := integral_comp_mul_left_Ioi'
    (fun u : ℝ => density u / ((u : ℂ) + (4 / 3 : ℂ) * w)) 0
    (by norm_num : (0 : ℝ) < 4 / 3)
  rw [mul_zero, Complex.real_smul, ← integral_const_mul] at hs
  rw [← hs]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [show (4 / 3 : ℂ) * t + (4 / 3 : ℂ) * w =
      (4 / 3 : ℂ) * (t + w) by ring, ← mul_div_assoc,
    mul_div_mul_left _ _ (by norm_num : (4 / 3 : ℂ) ≠ 0)]

/-- The self-Stieltjes expression of the Tricomi function in the dilated coordinate. -/
lemma kummerU_eq_scaled_stieltjes {w : ℂ} (hw : (4 / 3 : ℂ) * w ∈ slitPlane) :
    kummerU (1 / 6) (1 / 3) ((4 / 3 : ℂ) * w) =
      ((4 / 3 : ℂ) * w) ^ (5 / 6 : ℂ) / (2 * π) *
        ∫ t in Ioi 0, scaledDensity t / ((t : ℂ) + w) := by
  have h := kummerU_stieltjes (a := 1 / 6) (b := 1 / 3) hw
    (by norm_num) (by norm_num)
  rw [show (1 - 1 / 6 : ℂ) = 5 / 6 by ring,
    show (1 + 1 / 6 - 1 / 3 : ℂ) = 5 / 6 by ring,
    StieltjesRepresentation.gamma_sixth_mul_five_sixths,
    show (1 / 3 - 1 / 6 : ℂ) = 1 / 6 by ring,
    show (1 / 6 - 1 : ℂ) = -5 / 6 by ring] at h
  rw [integral_scaledDensity_div_add]
  rw [h]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only [tricomiLaplaceKernel]
  rw [show (1 / 6 - 1 : ℂ) = -5 / 6 by ring]
  simp only [neg_one_mul]
  ring

/-- The principal two-thirds power gives the inverse Airy coordinate on the slit plane. -/
lemma airyArgument_spec {w : ℂ} (hw : w ∈ slitPlane) :
    w ^ (2 / 3 : ℂ) ≠ 0 ∧ |arg (w ^ (2 / 3 : ℂ))| < 2 * π / 3 ∧
      2 * airyZetaComplex (w ^ (2 / 3 : ℂ)) = (4 / 3 : ℂ) * w := by
  have hw0 := slitPlane_ne_zero hw
  let L : ℂ := (2 / 3 : ℂ) * log w
  have hL : L.im = 2 / 3 * arg w := by norm_num [L, mul_im, log_im]
  have hLa : -π < L.im := by rw [hL]; linarith [neg_pi_lt_arg w, Real.pi_pos]
  have hLb : L.im ≤ π := by rw [hL]; linarith [arg_le_pi w, Real.pi_pos]
  have hlog : log (w ^ (2 / 3 : ℂ)) = L := by
    rw [cpow_def_of_ne_zero hw0,
      show log w * (2 / 3 : ℂ) = L by dsimp only [L]; ring]
    exact log_exp hLa hLb
  have harg : arg (w ^ (2 / 3 : ℂ)) = 2 / 3 * arg w := by
    rw [← log_im, hlog, hL]
  have hwarg : |arg w| < π := by
    refine abs_lt.mpr ⟨neg_pi_lt_arg w, ?_⟩
    exact lt_of_le_of_ne (arg_le_pi w) (mem_slitPlane_iff_arg.mp hw).1
  have hp0 : w ^ (2 / 3 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hw0)
  refine ⟨hp0, ?_, ?_⟩
  · rw [harg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
    linarith [hwarg]
  · rw [airyZetaComplex, cpow_def_of_ne_zero hp0, hlog]
    have he : L * (3 / 2 : ℂ) = log w := by dsimp only [L]; ring
    rw [he, exp_log hw0]
    ring

/-- Airy Ai in the coordinate of the dilated self-Stieltjes kernel. -/
lemma airyAi_eq_scaled_stieltjes {w : ℂ} (hw : w ∈ slitPlane) :
    airyAi (w ^ (2 / 3 : ℂ)) =
      StieltjesRepresentation.normalization * exp (-(2 / 3 : ℂ) * w) *
        ((4 / 3 : ℂ) * w) ^ (5 / 6 : ℂ) / (2 * π) *
        ∫ t in Ioi 0, scaledDensity t / ((t : ℂ) + w) := by
  obtain ⟨hz0, hzarg, hzeta⟩ := airyArgument_spec hw
  have hscaled : (4 / 3 : ℂ) * w ∈ slitPlane := by
    rw [← hzeta]
    exact StieltjesRepresentation.two_zeta_mem_slitPlane hz0 hzarg
  rw [StieltjesRepresentation.airyAi_eq_tricomi hz0 hzarg, hzeta,
    kummerU_eq_scaled_stieltjes hscaled]
  have hzeta' : airyZetaComplex (w ^ (2 / 3 : ℂ)) = (2 / 3 : ℂ) * w := by
    linear_combination hzeta / 2
  rw [hzeta', show -((2 / 3 : ℂ) * w) = -(2 / 3 : ℂ) * w by ring]
  ring

/-- The positive-power Jacobian converts the Tricomi density to the Airy density. -/
lemma density_change_variable {t : ℝ} (ht : 0 < t) :
    StieltjesRepresentation.normalization *
      (((3 / 2 : ℝ) * t ^ ((3 / 2 : ℝ) - 1)) • scaledDensity (t ^ (3 / 2 : ℝ))) =
      ((3 / 2 : ℂ) * (4 / 3 : ℂ) ^ (-5 / 6 : ℂ)) *
        ((t : ℂ) ^ (-3 / 4 : ℂ) * exp (-(airyZeta t : ℂ)) * airyAi t) := by
  have h := StieltjesRepresentation.transformed_kernel (z := 0) ht
  rw [Complex.zero_cpow (by norm_num : (3 / 2 : ℂ) ≠ 0)] at h
  simp only [airyZetaComplex, Complex.zero_cpow (by norm_num : (3 / 2 : ℂ) ≠ 0),
    mul_zero, add_zero, zero_add] at h
  have hp : ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) = (t : ℂ) ^ (3 / 2 : ℂ) := by
    simpa only [ofReal_div, ofReal_ofNat, ofReal_one] using (ofReal_cpow ht.le (3 / 2 : ℝ))
  have hs : ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) = (t : ℂ) ^ (1 / 2 : ℂ) := by
    simpa only [ofReal_div, ofReal_ofNat, ofReal_one] using (ofReal_cpow ht.le (1 / 2 : ℝ))
  have hr : (t : ℂ) ^ (3 / 2 : ℂ) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr ht.ne'))
  rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by ring, Complex.real_smul]
  dsimp only [tricomiLaplaceKernel]
  simp only [ofReal_mul, ofReal_div, ofReal_ofNat, hp, hs]
  rw [show (1 / 6 - 1 : ℂ) = -5 / 6 by ring]
  simp only [neg_one_mul]
  simp only [← mul_div_assoc] at h
  have hcross := (div_eq_div_iff
    (mul_ne_zero (by norm_num : (4 / 3 : ℂ) ≠ 0) hr) hr).mp h
  have hcancellation :
      StieltjesRepresentation.normalization * (2 * (t : ℂ) ^ (1 / 2 : ℂ)) *
        (kummerU (1 / 6) (1 / 3) ((4 / 3 : ℂ) * (t : ℂ) ^ (3 / 2 : ℂ)) *
          exp (-((4 / 3 : ℂ) * (t : ℂ) ^ (3 / 2 : ℂ)))) *
        ((4 / 3 : ℂ) * (t : ℂ) ^ (3 / 2 : ℂ)) ^ (-5 / 6 : ℂ) =
      (((3 / 2 : ℂ) * (4 / 3 : ℂ) ^ (-5 / 6 : ℂ)) *
        ((t : ℂ) ^ (-3 / 4 : ℂ) * exp (-(airyZeta t : ℂ)) * airyAi t)) * (4 / 3) := by
    apply mul_right_cancel₀ hr
    linear_combination hcross
  linear_combination (3 / 4 : ℂ) * hcancellation

/-- The Cauchy pullback is the negative Airy principal-value kernel, with its exact constant. -/
lemma jacobianKernel_eq {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    normalization * jacobianKernel x t = -conversion * principalKernel x t := by
  have h := density_change_variable ht
  simp only [Complex.real_smul, ← mul_assoc] at h
  have hp (u : ℝ) (hu : 0 < u) :
      ((u ^ (3 / 2 : ℝ) : ℝ) : ℂ) = (u : ℂ) ^ (3 / 2 : ℂ) := by
    simpa only [ofReal_div, ofReal_ofNat, ofReal_one] using (ofReal_cpow hu.le (3 / 2 : ℝ))
  simp only [Complex.real_smul, ← mul_div_assoc, ← mul_assoc]
  rw [h, hp x hx, hp t ht,
    show (t : ℂ) ^ (3 / 2 : ℂ) - (x : ℂ) ^ (3 / 2 : ℂ) =
      -((x : ℂ) ^ (3 / 2 : ℂ) - (t : ℂ) ^ (3 / 2 : ℂ)) by ring, div_neg]
  ring

/-- The finite part of the self-Stieltjes kernel equals the Airy symmetric principal value. -/
lemma finitePart_relation {x : ℝ} (hx : 0 < x) :
    normalization * finitePart (x ^ (3 / 2 : ℝ)) =
      -conversion * principalValueIoi (principalKernel x) x := by
  have hgen := (pv_tendsto_rpow_div_sub (p := 3 / 2) (by norm_num) hx
    integrableOn_scaledDensity
    (differentiableAt_scaledDensity (Real.rpow_pos_of_pos hx _))).const_mul normalization
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      normalization * ((∫ t in 0..x - ε, jacobianKernel x t) +
        ∫ t in Ioi (x + ε), jacobianKernel x t) =
      -conversion * ((∫ t in 0..x - ε, principalKernel x t) +
        DLMF.Core.improperAtTop (principalKernel x) (x + ε)) := by
    filter_upwards [Ioo_mem_nhdsGT hx] with ε hε
    have hε0 : 0 < ε := hε.1
    have hεx : ε < x := hε.2
    have htail := PrincipalValue.tail_integrableOn hx (d := x + ε) (by linarith)
    have htailValue : DLMF.Core.improperAtTop (principalKernel x) (x + ε) =
        ∫ t in Ioi (x + ε), principalKernel x t :=
      (intervalIntegral_tendsto_integral_Ioi (x + ε) htail tendsto_id).limUnder_eq
    rw [htailValue]
    simp only [mul_add]
    congr 1
    · rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with t ht
      rw [uIoc_of_le (show (0 : ℝ) ≤ x - ε by linarith)] at ht
      exact jacobianKernel_eq hx ht.1
    · rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact jacobianKernel_eq hx (lt_trans (by linarith : 0 < x + ε) ht)
  have horig := (airyBi_stieltjes_principalValue_converges hx).2.const_mul (-conversion)
  exact tendsto_nhds_unique (hgen.congr' heq) horig

/-- The two signed boundary values of the dilated Tricomi Stieltjes transform. -/
lemma tendsto_scaled_stieltjes {c ε : ℝ} (hc : 0 < c) (hε : ε = 1 ∨ ε = -1) :
    Tendsto (fun η : ℝ => ∫ t : ℝ in Ioi 0,
      scaledDensity t / ((t : ℂ) + negativeAxisApproach c ε η)) (𝓝[>] 0)
      (𝓝 ((finitePart c : ℂ) - (ε : ℂ) * (Real.pi : ℂ) * Complex.I * scaledDensity c)) := by
  have h := tendsto_integral_Ioi_div_sub_add_sign_mul_I hc hε
    integrableOn_scaledDensity (differentiableAt_scaledDensity hc)
  have hi : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hscale : Tendsto (fun η : ℝ => c * η) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [mul_zero] using hi.const_mul c
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact mul_pos hc hη
  convert h.comp hscale using 1
  funext η
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  have hd : (t : ℂ) + negativeAxisApproach c ε η =
      (t : ℂ) - c + (ε * (c * η) : ℝ) * I := by
    simp only [negativeAxisApproach]
    push_cast
    ring
  exact congrArg (fun d : ℂ => scaledDensity t / d) hd

/-- The two-thirds power approaches the corresponding Airy rotation. -/
lemma tendsto_airyArgument {x ε : ℝ} (hx : 0 < x) (hε : ε = 1 ∨ ε = -1) :
    Tendsto (fun η : ℝ => negativeAxisApproach (x ^ (3 / 2 : ℝ)) ε η ^ (2 / 3 : ℂ))
      (𝓝[>] 0) (𝓝 ((x : ℂ) * exp ((ε : ℂ) * 2 * π * I / 3))) := by
  have hc : 0 < x ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hx (3 / 2 : ℝ)
  have h := tendsto_cpow_negativeAxisApproach hc hε (2 / 3 : ℂ)
  have hp : ((x ^ (3 / 2 : ℝ) : ℝ) : ℂ) ^ (2 / 3 : ℂ) = x := by
    have hr : (x ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) = x := by
      rw [← Real.rpow_mul hx.le]
      norm_num
    calc _ = (((x ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
          simpa only [ofReal_div, ofReal_ofNat, ofReal_one] using
            (ofReal_cpow hc.le (2 / 3 : ℝ)).symm
      _ = _ := congrArg Complex.ofReal hr
  rw [hp, show (ε : ℂ) * π * I * (2 / 3 : ℂ) = (ε : ℂ) * 2 * π * I / 3 by ring] at h
  exact h

/-- Boundary values of the explicit prefactor in the Airy Stieltjes representation. -/
lemma tendsto_stieltjesPrefactor {x ε : ℝ} (hx : 0 < x) (hε : ε = 1 ∨ ε = -1) :
    Tendsto (fun η : ℝ => normalization *
      exp (-(2 / 3 : ℂ) * negativeAxisApproach (x ^ (3 / 2 : ℝ)) ε η) *
      ((4 / 3 : ℂ) * negativeAxisApproach (x ^ (3 / 2 : ℝ)) ε η) ^ (5 / 6 : ℂ) /
        (2 * π)) (𝓝[>] 0)
      (𝓝 (normalization * exp (airyZeta x) *
        ((4 / 3 : ℂ) * (x ^ (3 / 2 : ℝ) : ℝ)) ^ (5 / 6 : ℂ) / (2 * π) *
        exp ((ε : ℂ) * 5 * π * I / 6))) := by
  let c : ℝ := x ^ (3 / 2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hx (3 / 2 : ℝ)
  have hscaled (η : ℝ) : (4 / 3 : ℂ) * negativeAxisApproach c ε η =
      negativeAxisApproach ((4 / 3 : ℝ) * c) ε η := by
    simp only [negativeAxisApproach]
    push_cast
    ring
  have hp := tendsto_cpow_negativeAxisApproach
    (mul_pos (by norm_num : (0 : ℝ) < 4 / 3) hc) hε (5 / 6 : ℂ)
  have hp' : Tendsto (fun η : ℝ =>
      ((4 / 3 : ℂ) * negativeAxisApproach c ε η) ^ (5 / 6 : ℂ)) (𝓝[>] 0)
      (𝓝 (((4 / 3 : ℂ) * c) ^ (5 / 6 : ℂ) * exp ((ε : ℂ) * 5 * π * I / 6))) := by
    convert hp using 1
    · funext η
      rw [hscaled]
    · push_cast
      congr 3
      ring
  have he := ((tendsto_negativeAxisApproach c ε).const_mul (-(2 / 3 : ℂ))).cexp
  have hzeta : -(2 / 3 : ℂ) * (-(c : ℂ)) = (airyZeta x : ℂ) := by
    dsimp only [c, airyZeta]
    push_cast
    ring
  rw [hzeta] at he
  dsimp only [c] at he hp'
  convert (((he.const_mul normalization).mul hp').div_const (2 * π)) using 1
  ring_nf

/-- The two rotated Airy values are the signed boundary values of the Tricomi transform. -/
lemma airyAi_rotated_eq_finitePart {x ε : ℝ} (hx : 0 < x) (hε : ε = 1 ∨ ε = -1) :
    airyAi ((x : ℂ) * exp ((ε : ℂ) * 2 * π * I / 3)) =
      normalization * exp (airyZeta x) *
        ((4 / 3 : ℂ) * (x ^ (3 / 2 : ℝ) : ℝ)) ^ (5 / 6 : ℂ) / (2 * π) *
        exp ((ε : ℂ) * 5 * π * I / 6) *
        (finitePart (x ^ (3 / 2 : ℝ)) -
          (ε : ℂ) * π * I * scaledDensity (x ^ (3 / 2 : ℝ))) := by
  have hleft := differentiable_airyAi.continuous.tendsto
    ((x : ℂ) * exp ((ε : ℂ) * 2 * π * I / 3)) |>.comp
      (tendsto_airyArgument hx hε)
  have hright := (tendsto_stieltjesPrefactor hx hε).mul
    (tendsto_scaled_stieltjes (Real.rpow_pos_of_pos hx (3 / 2 : ℝ)) hε)
  have heq : ∀ᶠ η : ℝ in 𝓝[>] 0,
      normalization * exp (-(2 / 3 : ℂ) *
          negativeAxisApproach (x ^ (3 / 2 : ℝ)) ε η) *
        ((4 / 3 : ℂ) * negativeAxisApproach (x ^ (3 / 2 : ℝ)) ε η) ^ (5 / 6 : ℂ) /
          (2 * π) *
        (∫ t : ℝ in Ioi 0, scaledDensity t /
          ((t : ℂ) + negativeAxisApproach (x ^ (3 / 2 : ℝ)) ε η)) =
        airyAi (negativeAxisApproach (x ^ (3 / 2 : ℝ)) ε η ^ (2 / 3 : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact (airyAi_eq_scaled_stieltjes
      (negativeAxisApproach_mem_slitPlane (Real.rpow_pos_of_pos hx (3 / 2 : ℝ)) hε hη)).symm
  exact tendsto_nhds_unique hleft (hright.congr' heq)

/-- The Airy connection formula cancels the two imaginary residue terms. -/
lemma airyBi_eq_finitePart {x : ℝ} (hx : 0 < x) :
    airyBi x = -(normalization * exp (airyZeta x) *
      ((4 / 3 : ℂ) * (x ^ (3 / 2 : ℝ) : ℝ)) ^ (5 / 6 : ℂ)) / π *
        finitePart (x ^ (3 / 2 : ℝ)) := by
  let c : ℝ := x ^ (3 / 2 : ℝ)
  let R : ℂ := normalization * exp (airyZeta x) *
    ((4 / 3 : ℂ) * c) ^ (5 / 6 : ℂ) / (2 * π)
  have hp := airyAi_rotated_eq_finitePart (ε := 1) hx (Or.inl rfl)
  have hm := airyAi_rotated_eq_finitePart (ε := -1) hx (Or.inr rfl)
  simp only [ofReal_one, one_mul] at hp
  simp only [ofReal_neg, ofReal_one, neg_mul, neg_div, one_mul, sub_neg_eq_add] at hm
  have hep : exp (π * I / 6) * exp (5 * π * I / 6) = -1 := by
    rw [← exp_add, show π * I / 6 + 5 * π * I / 6 = π * I by ring, exp_pi_mul_I]
  have hem : exp (-(π * I / 6)) * exp (-(5 * π * I / 6)) = -1 := by
    rw [← exp_add, show -(π * I / 6) + -(5 * π * I / 6) = -(π * I) by ring,
      exp_neg, exp_pi_mul_I, inv_neg, inv_one]
  rw [airyBi_eq_airyAi_omega, hm, hp]
  have he : exp (-(π * I / 6)) *
      (R * exp (-(5 * π * I / 6)) *
        (finitePart c + π * I * scaledDensity c)) +
      exp (π * I / 6) * (R * exp (5 * π * I / 6) *
        (finitePart c - π * I * scaledDensity c)) = -2 * R * finitePart c := by
    linear_combination R * (finitePart c + π * I * scaledDensity c) * hem +
      R * (finitePart c - π * I * scaledDensity c) * hep
  dsimp only [R, c] at he
  rw [he]
  ring

/-- Positive-axis powers give the exact normalization of the Airy principal value. -/
lemma stieltjesPrefactor_normalization {x : ℝ} (hx : 0 < x) :
    ((4 / 3 : ℂ) * (x ^ (3 / 2 : ℝ) : ℝ)) ^ (5 / 6 : ℂ) *
      (4 / 3 : ℂ) ^ (-5 / 6 : ℂ) = (x : ℂ) ^ (5 / 4 : ℂ) := by
  have hc : 0 ≤ x ^ (3 / 2 : ℝ) := Real.rpow_nonneg hx.le _
  have hm := mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3) hc (5 / 6 : ℂ)
  norm_num only [ofReal_div, ofReal_ofNat, ofReal_mul] at hm
  have hxpow : ((x ^ (3 / 2 : ℝ) : ℝ) : ℂ) ^ (5 / 6 : ℂ) =
      (x : ℂ) ^ (5 / 4 : ℂ) := by
    have hr : (x ^ (3 / 2 : ℝ)) ^ (5 / 6 : ℝ) = x ^ (5 / 4 : ℝ) := by
      rw [← Real.rpow_mul hx.le]
      norm_num
    rw [show (5 / 6 : ℂ) = ((5 / 6 : ℝ) : ℂ) by norm_num,
      ← ofReal_cpow hc, hr, ofReal_cpow hx.le]
    norm_num
  rw [hm, hxpow]
  calc _ = ((4 / 3 : ℂ) ^ (5 / 6 : ℂ) * (4 / 3 : ℂ) ^ (-5 / 6 : ℂ)) *
      (x : ℂ) ^ (5 / 4 : ℂ) := by ring
    _ = _ := by
      rw [← cpow_add _ _ (by norm_num : (4 / 3 : ℂ) ≠ 0)]
      norm_num

/-- The Airy Bi function equals its symmetry-line principal-value Stieltjes integral. -/
lemma airyBi_eq_principalValue {x : ℝ} (hx : 0 < x) :
    airyBi x = 3 * (x : ℂ) ^ (5 / 4 : ℂ) * exp (airyZeta x) / (2 * π) *
      principalValueIoi (principalKernel x) x := by
  rw [airyBi_eq_finitePart hx]
  calc _ = -(exp (airyZeta x) *
        ((4 / 3 : ℂ) * (x ^ (3 / 2 : ℝ) : ℝ)) ^ (5 / 6 : ℂ) / π) *
        (normalization * finitePart (x ^ (3 / 2 : ℝ))) := by ring
    _ = exp (airyZeta x) *
        ((4 / 3 : ℂ) * (x ^ (3 / 2 : ℝ) : ℝ)) ^ (5 / 6 : ℂ) / π *
        conversion * principalValueIoi (principalKernel x) x := by
      rw [finitePart_relation hx]
      ring
    _ = _ := by
      have h := stieltjesPrefactor_normalization hx
      linear_combination (3 / (2 * π) * exp (airyZeta x) *
        principalValueIoi (principalKernel x) x) * h

end DLMF.Airy.BiStieltjes

namespace DLMF.Airy

/-- For `x > 0`:
`Bi(x) = (3 x^{5/4} e^{ζ}/(2π)) ⨍₀^∞ t^{-3/4} e^{-(2/3)t^{3/2}} Ai(t)/(x^{3/2} - t^{3/2}) dt`, a
Cauchy principal value at `t = x` (DLMF 9.10.19). -/
@[dlmf 9.10.E19]
theorem airyBi_stieltjes_principalValue {x : ℝ} (hx : 0 < x) :
    airyBi x = 3 * (x : ℂ) ^ (5 / 4 : ℂ) * exp (airyZeta x) / (2 * π) *
      principalValueIoi (fun t : ℝ => (t : ℂ) ^ (-3 / 4 : ℂ) * exp (-(airyZeta t : ℂ)) *
        airyAi t / ((x : ℂ) ^ (3 / 2 : ℂ) - (t : ℂ) ^ (3 / 2 : ℂ))) x := by
  exact BiStieltjes.airyBi_eq_principalValue hx

end DLMF.Airy
