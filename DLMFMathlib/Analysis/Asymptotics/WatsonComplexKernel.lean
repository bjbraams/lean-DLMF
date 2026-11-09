/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.WatsonKernel
public import DLMFMathlib.Analysis.MellinConvolution

/-!
# Watson's lemma for general kernels and complex exponent sequences

A kernel bounded by a decreasing stretched exponential transfers an expansion in complex
powers at zero to an expansion with Mellin-moment coefficients at infinity. This extends
the real-exponent kernel theorem to the complex powers in DLMF 2.3.10–2.3.12.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics Finset
open scoped Topology

namespace Asymptotics

/-- The norm of a complex power on the positive axis is the corresponding real power. -/
theorem isBigO_cpow_rpow_atTop (s : ℂ) :
    (fun t : ℝ => (t : ℂ) ^ s) =O[atTop] fun t => t ^ s.re := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [one_mul, norm_cpow_eq_rpow_re_of_pos ht,
    Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]

/-- Positive dilation of a complex power moment gives the corresponding Mellin transform. -/
theorem integral_kernel_mul_cpow (f : ℝ → ℂ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), f (x * t) * (t : ℂ) ^ (s - 1)) =
      (x : ℂ) ^ (-s) * mellin f s := by
  have hm : (∫ t in Ioi (0 : ℝ), f (x * t) * (t : ℂ) ^ (s - 1)) =
      mellin (fun t => f (x * t)) s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [smul_eq_mul]
    ring
  rw [hm, mellin_comp_mul_left f _ hx, smul_eq_mul]

/-- Complex moments of a rapidly decreasing measurable kernel converge absolutely after dilation. -/
theorem integrableOn_kernel_mul_cpow {f : ℝ → ℂ} {A a κ x : ℝ} {s : ℂ}
    (ha : 0 < a) (hκ : 0 < κ) (hs : 0 < s.re) (hx : 0 < x)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ t, 0 ≤ t → ‖f t‖ ≤ A * Real.exp (-a * t ^ κ)) :
    IntegrableOn (fun t : ℝ => f (x * t) * (t : ℂ) ^ (s - 1)) (Ioi 0) := by
  have hi : MellinConvergent f s :=
    (mellinConvergent_of_norm_le_exp_rpow ha hκ hs hfm hf).of_re_eq (by simp)
  refine IntegrableOn.congr_fun ((MellinConvergent.comp_mul_left hx).mpr hi)
    (fun t _ => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  ring

/-- The general-kernel Watson lemma for complex exponents with positive real parts.
Strict increase is needed only to regard the comparison functions as an asymptotic scale. -/
private theorem kernel_expansion_of_bound_on_nonnegative_axis
    {f q : ℝ → ℂ} {d e : ℕ → ℂ}
    {A a b κ : ℝ} (he : ∀ n, 0 < (e n).re)
    (hA : 0 ≤ A) (ha : 0 < a) (hb : 0 < b) (hκ : 0 < κ)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ t, 0 ≤ t → ‖f t‖ ≤ A * Real.exp (-a * t ^ κ))
    (hqi : LocallyIntegrableOn q (Ioi 0))
    (hqb : q =O[atTop] (fun t => Real.exp (b * t ^ κ)))
    (hq : ∀ N : ℕ, (fun t => q t - ∑ n ∈ range N, (t : ℂ) ^ (e n - 1) * d n)
      =O[𝓝[>] 0] fun t => t ^ ((e N).re - 1)) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => (x : ℂ) ^ (-e n))
      (fun n => mellin f (e n) * d n) (fun x => ∫ t in Ioi (0 : ℝ), f (x * t) * q t) := by
  intro N
  let P : ℝ → ℂ := fun t => ∑ n ∈ range N, (t : ℂ) ^ (e n - 1) * d n
  let R : ℝ → ℂ := fun t => q t - P t
  have hPc : ContinuousOn P (Ioi 0) := by
    refine continuousOn_finsetSum _ fun n _ t ht => ?_
    exact ((continuousAt_ofReal_cpow_const _ _ (Or.inr ht.ne')).mul
      continuousAt_const).continuousWithinAt
  have hPb : P =O[atTop] fun t => Real.exp (b * t ^ κ) := by
    refine IsBigO.fun_sum fun n _ => ?_
    have hn := (isBigO_cpow_rpow_atTop (e n - 1)).trans
      (isLittleO_rpow_exp_mul_rpow_atTop hκ hb _).isBigO
    simpa only [mul_comm] using hn.const_mul_left (d n)
  have hRi : LocallyIntegrableOn R (Ioi 0) :=
    hqi.sub (hPc.locallyIntegrableOn measurableSet_Ioi)
  have hRb : R =O[atTop] fun t => Real.exp (b * t ^ κ) := hqb.sub hPb
  have hzero : q =O[𝓝[>] 0] fun t => t ^ ((e 0).re - 1) := by simpa using hq 0
  have hiq := integrableOn_exp_neg_mul_rpow_mul_of_isBigO (c := b + 1)
    hκ (by linarith) (he 0) hqi.norm hzero.norm_left hqb.norm_left
  have hnorm : (fun x : ℝ => x ^ (-(e N).re)) =O[atTop] fun x => (x : ℂ) ^ (-e N) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [one_mul, norm_cpow_eq_rpow_re_of_pos hx, neg_re,
      Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
  refine ((isBigO_integral_kernel_mul hA ha hκ (he N) hf hRi (hq N) hRb).trans hnorm).congr'
    ?_ .rfl
  have hz : ∀ᶠ x : ℝ in atTop, b + 1 ≤ a * x ^ κ :=
    ((tendsto_rpow_atTop hκ).const_mul_atTop ha).eventually (eventually_ge_atTop (b + 1))
  filter_upwards [hz, eventually_gt_atTop 0] with x hxz hx
  have hi := integrableOn_kernel_mul_of_exp_rpow ha hκ hx hxz hfm
    hqi.aestronglyMeasurable hf hiq
  have ht (n : ℕ) : IntegrableOn (fun t : ℝ =>
      f (x * t) * ((t : ℂ) ^ (e n - 1) * d n)) (Ioi 0) := by
    refine IntegrableOn.congr_fun
      ((integrableOn_kernel_mul_cpow ha hκ (he n) hx hfm hf).mul_const (d n))
      (fun t _ => ?_) measurableSet_Ioi
    ring
  have hiP : IntegrableOn (fun t => f (x * t) * P t) (Ioi 0) := by
    simp_rw [P, mul_sum]
    exact integrable_finsetSum (range N) (fun n _ => ht n)
  simp only [R, mul_sub]
  rw [integral_sub hi hiP]
  congr 1
  simp only [P, mul_sum, smul_eq_mul]
  rw [integral_finsetSum _ (fun n _ => ht n)]
  refine sum_congr rfl fun n _ => ?_
  simp_rw [← mul_assoc]
  rw [integral_mul_const, integral_kernel_mul_cpow f (e n) hx]

/-- The general-kernel Watson lemma on the positive half-line. No condition is imposed
on the value of the kernel at zero. The exponents may have arbitrary imaginary parts. -/
theorem hasAsymptoticExpansion_integral_kernel_mul_cpow_seq {f q : ℝ → ℂ} {d e : ℕ → ℂ}
    {A a b κ : ℝ} (he : ∀ n, 0 < (e n).re)
    (hA : 0 ≤ A) (ha : 0 < a) (hb : 0 < b) (hκ : 0 < κ)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ t, 0 < t → ‖f t‖ ≤ A * Real.exp (-a * t ^ κ))
    (hqi : LocallyIntegrableOn q (Ioi 0))
    (hqb : q =O[atTop] (fun t => Real.exp (b * t ^ κ)))
    (hq : ∀ N : ℕ, (fun t => q t - ∑ n ∈ range N, (t : ℂ) ^ (e n - 1) * d n)
      =O[𝓝[>] 0] fun t => t ^ ((e N).re - 1)) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => (x : ℂ) ^ (-e n))
      (fun n => mellin f (e n) * d n) (fun x => ∫ t in Ioi (0 : ℝ), f (x * t) * q t) := by
  let g : ℝ → ℂ := fun t => if t = 0 then 0 else f t
  have hgf : ∀ t ∈ Ioi (0 : ℝ), g t = f t := fun t ht => ite_eq_right ht.ne'
  have hgm : AEStronglyMeasurable g (volume.restrict (Ioi 0)) :=
    hfm.congr ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => (hgf t ht).symm)
  have hgb : ∀ t, 0 ≤ t → ‖g t‖ ≤ A * Real.exp (-a * t ^ κ) := by
    intro t ht
    rcases eq_or_lt_of_le ht with rfl | ht
    · simp only [g, ite_true, norm_zero]
      positivity
    · rw [hgf t ht]
      exact hf t ht
  have hm : ∀ s : ℂ, mellin g s = mellin f s := by
    intro s
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [hgf t ht]
  have h := kernel_expansion_of_bound_on_nonnegative_axis he hA ha hb hκ hgm hgb hqi hqb hq
  have h' := h.congr_coeff (funext fun n => by rw [hm])
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [hgf (x * t) (mul_pos hx ht)]

end Asymptotics
