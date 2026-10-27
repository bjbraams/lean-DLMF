/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.IntegralRepresentations
public import DLMF.Hypergeometric.EulerHalfLine

/-!
# Tricomi's Laplace transform with unrestricted first parameter

Fubini and the half-line Euler integral evaluate the transform for `Re a > 0`.
Tricomi's contiguous relation then lowers `a` by natural steps, preserving both
endpoint convergence inequalities. The regularized Gauss contiguous relation
satisfies the same recursion even when its denominator parameter is singular.
-/

@[expose] public section
open Complex Filter MeasureTheory Set
open scoped Real Topology
open DLMF.Hypergeometric
noncomputable section
namespace DLMF.Confluent

/-- The kernel of the weighted Tricomi Laplace transform. -/
def tricomiLaplaceKernel (a b c z : ℂ) (t : ℝ) : ℂ :=
  exp (-z * t) * (t : ℂ) ^ (b - 1) * kummerU a c t

/-- Absolute integrability of the double Laplace kernel in its initial parameter region. -/
theorem integrable_tricomi_double_kernel {a b c z : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hbc : (c - 1).re < b.re) (hz : 0 < z.re) :
    Integrable (fun q : ℝ × ℝ => exp (-(z + q.2) * q.1) * (q.1 : ℂ) ^ (b - 1) *
      (q.2 : ℂ) ^ (a - 1) * (1 + (q.2 : ℂ)) ^ (c - a - 1))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  let F (t u : ℝ) : ℂ := exp (-(z + u) * t) * (t : ℂ) ^ (b - 1) *
    (u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (c - a - 1)
  let C (u : ℝ) := u ^ (a.re - 1) * (1 + u) ^ (c.re - a.re - 1)
  have hnorm (t u : ℝ) (ht : 0 < t) (hu : 0 < u) :
      ‖F t u‖ = C u * (t ^ (b.re - 1) * Real.exp (-((z.re + u) * t))) := by
    dsimp only [F, C]
    rw [norm_mul, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht,
      norm_cpow_eq_rpow_re_of_pos hu,
      show 1 + (u : ℂ) = ((1 + u : ℝ) : ℂ) by push_cast; rfl,
      norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.norm_exp]
    simp only [sub_re, one_re, neg_re, mul_re, add_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    ring
  have hbase (u : ℝ) (hu : 0 < u) :
      IntegrableOn (fun t : ℝ => t ^ (b.re - 1) * Real.exp (-((z.re + u) * t))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := b.re - 1) (b := z.re + u)
        (by linarith) one_pos (by positivity)
  have hnormIntegral (u : ℝ) (hu : 0 < u) :
      (∫ t : ℝ in Ioi 0, ‖F t u‖) = Real.Gamma b.re *
        ‖eulerHalfLineKernel (b.re : ℂ) (a.re : ℂ) (b.re - c.re + 1) (z.re : ℂ) u‖ := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hnorm t u ht hu),
      integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hb (by positivity),
      one_div, Real.inv_rpow (by positivity : 0 ≤ z.re + u),
      ← Real.rpow_neg (by positivity : 0 ≤ z.re + u)]
    dsimp only [eulerHalfLineKernel, C]
    rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hu,
      show 1 + (u : ℂ) = ((1 + u : ℝ) : ℂ) by push_cast; rfl,
      show (z.re : ℂ) + u = ((z.re + u : ℝ) : ℂ) by push_cast; rfl,
      norm_cpow_eq_rpow_re_of_pos (by positivity), norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [sub_re, add_re, ofReal_re, one_re, neg_re]
    ring
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) :=
    Measurable.aestronglyMeasurable (by dsimp [F, Function.uncurry]; fun_prop)
  apply (integrable_prod_iff' hmeas).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    apply Integrable.mono' ((hbase u hu).const_mul (C u))
      (Measurable.aestronglyMeasurable (by dsimp [F]; fun_prop))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hnorm t u ht hu).le
  · have hi := (eulerHalfLine_integrable_integral (p := (b.re : ℂ))
      (a := (a.re : ℂ)) (d := (b.re - c.re + 1 : ℂ)) (z := (z.re : ℂ))
        (by simpa using ha) (by simp only [add_re, sub_re, ofReal_re, one_re] at hbc ⊢; linarith)
        (by simpa using hz)).1
    refine (hi.norm.const_mul (Real.Gamma b.re)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (hnormIntegral u hu).symm

/-- Tricomi's transform and its absolute integrability when the Laplace representation applies. -/
theorem laplace_kummerU_gauss_of_re_pos {a b c z : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hbc : (c - 1).re < b.re) (hz : 0 < z.re) :
    IntegrableOn (tricomiLaplaceKernel a b c z) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, tricomiLaplaceKernel a b c z t) =
        Gamma b * Gamma (b - c + 1) *
          regularizedGaussHG b (b - c + 1) (a + b - c + 1) (1 - z) := by
  let F (t u : ℝ) : ℂ := exp (-(z + u) * t) * (t : ℂ) ^ (b - 1) *
    (u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (c - a - 1)
  have hi : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) :=
    integrable_tricomi_double_kernel ha hb hbc hz
  have hpoint (t : ℝ) (ht : t ∈ Ioi 0) : tricomiLaplaceKernel a b c z t =
      1 / Gamma a * ∫ u : ℝ in Ioi 0, F t u := by
    rw [tricomiLaplaceKernel, kummerU_laplace ha (by simpa using ht)]
    simp_rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only [F]
    rw [show -(z + (u : ℂ)) * t = -z * t + -(t : ℂ) * u by ring, exp_add]
    ring
  have hint := (hi.integral_prod_left.const_mul (1 / Gamma a)).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact (hpoint t ht).symm)
  refine ⟨hint, ?_⟩
  have hinner (u : ℝ) (hu : u ∈ Ioi 0) : (∫ t : ℝ in Ioi 0, F t u) =
      Gamma b * eulerHalfLineKernel b a (b - c + 1) z u := by
    rw [show F = fun (t u : ℝ) => ((t : ℂ) ^ (b - 1) * exp (-((z + u) * t))) *
      ((u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (c - a - 1)) by funext t u; dsimp [F]; ring,
      integral_mul_const, DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi hb
        (show 0 < (z + u).re by simp; linarith [mem_Ioi.mp hu])]
    dsimp only [eulerHalfLineKernel]
    rw [show b - a - (b - c + 1) = c - a - 1 by ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul,
    integral_integral_swap hi, setIntegral_congr_fun measurableSet_Ioi hinner, integral_const_mul,
    (eulerHalfLine_integrable_integral (p := b) ha
      (show 0 < (b - c + 1).re by simp only [sub_re, add_re, one_re] at hbc ⊢; linarith) hz).2,
    show a + (b - c + 1) = a + b - c + 1 by ring]
  field_simp [Gamma_ne_zero_of_re_pos ha]

/-- The Tricomi Laplace transform on its full parameter region, with absolute integrability. -/
theorem laplace_kummerU_gauss {a b c z : ℂ}
    (hb : 0 < b.re) (hbc : (c - 1).re < b.re) (hz : 0 < z.re) :
    IntegrableOn (tricomiLaplaceKernel a b c z) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, tricomiLaplaceKernel a b c z t) =
        Gamma b * Gamma (b - c + 1) *
          regularizedGaussHG b (b - c + 1) (a + b - c + 1) (1 - z) := by
  have hshift : ∀ N : ℕ, ∀ a b c z : ℂ,
      0 < a.re + N → 0 < b.re → (c - 1).re < b.re → 0 < z.re →
      IntegrableOn (tricomiLaplaceKernel a b c z) (Ioi 0) ∧
        (∫ t : ℝ in Ioi 0, tricomiLaplaceKernel a b c z t) =
          Gamma b * Gamma (b - c + 1) *
            regularizedGaussHG b (b - c + 1) (a + b - c + 1) (1 - z) := by
    intro N
    induction N with
    | zero => intro a b c z ha hb hbc hz; exact laplace_kummerU_gauss_of_re_pos (by simpa using ha) hb hbc hz
    | succ N ih =>
      intro a b c z ha hb hbc hz
      have hi1 := ih (a + 1) (b + 1) (c + 1) z (by simp at ha ⊢; linarith)
        (by simp; linarith) (by simp at hbc ⊢; linarith) hz
      have hi2 := ih (a + 1) b c z (by simp at ha ⊢; linarith) hb hbc hz
      have hpoint (t : ℝ) (ht : t ∈ Ioi 0) : tricomiLaplaceKernel a b c z t =
          tricomiLaplaceKernel (a + 1) (b + 1) (c + 1) z t +
            (a + 1 - c) * tricomiLaplaceKernel (a + 1) b c z t := by
        have ht0 := ofReal_ne_zero.mpr (ne_of_gt (mem_Ioi.mp ht))
        have hU := kummerU_contiguous_shift_a (a + 1) c t ht0
        rw [add_sub_cancel_right] at hU
        dsimp only [tricomiLaplaceKernel]
        rw [show b + 1 - 1 = (b - 1) + 1 by ring, cpow_add _ _ ht0, cpow_one]
        linear_combination (exp (-z * t) * (t : ℂ) ^ (b - 1)) * hU
      refine ⟨(hi1.1.add (hi2.1.const_mul (a + 1 - c))).congr (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact (hpoint t ht).symm), ?_⟩
      rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_add hi1.1
        (hi2.1.const_mul (a + 1 - c)), integral_const_mul, hi1.2, hi2.2,
        show (b + 1) - (c + 1) + 1 = b - c + 1 by ring,
        show (a + 1) + (b + 1) - (c + 1) + 1 = (a + b - c + 1) + 1 by ring,
        show (a + 1) + b - c + 1 = (a + b - c + 1) + 1 by ring,
        Gamma_add_one _ (ne_zero_of_re_pos hb)]
      have hw : 1 - z ∈ cutPlane := by
        change 1 - (1 - z) ∈ slitPlane; rw [sub_sub_cancel]; exact Or.inl hz
      have hg := regularizedGaussHG_contiguous_a_succ_c_pred b (b - c + 1) ((a + b - c + 1) + 1) hw
      rw [add_sub_cancel_right] at hg
      linear_combination (Gamma b * Gamma (b - c + 1)) * hg
  obtain ⟨N, hN⟩ := exists_nat_gt (-a.re)
  exact hshift N a b c z (by linarith) hb hbc hz

end DLMF.Confluent
