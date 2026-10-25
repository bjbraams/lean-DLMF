/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Topology.Order.Compact

/-!
# Natural convergence of the complex logarithm series on its closed disk

The integral-remainder argument adapts Michael Stoll's proof of
`Complex.norm_log_sub_logTaylor_le` in Mathlib. A compact-path bound replaces
its open-disk geometric bound, retaining all convergent points of the unit circle.
-/

@[expose] public section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace Complex

/-- The logarithm remainder has a uniform path bound, independent of its order. -/
lemma exists_norm_log_sub_logTaylor_le {z : ℂ} (hz : 1+z∈slitPlane) :
    ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ,
      ‖log (1+z)-logTaylor (n+1) z‖≤‖z‖^(n+1)*C/(n+1) := by
  have hi := continuousOn_one_add_mul_inv hz
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hi
  have hC0 : 0≤C := (norm_nonneg _).trans (hC 0 (by constructor <;> norm_num))
  refine ⟨C,hC0,fun n => ?_⟩
  let f : ℂ → ℂ := fun w => log (1+w)-logTaylor (n+1) w
  let f' : ℂ → ℂ := fun w => (-w)^n*(1+w)⁻¹
  have hd : ∀ t∈Icc (0:ℝ) 1, HasDerivAt f (f' (0+t*z)) (0+t*z) := by
    intro t ht
    rw [zero_add]
    exact hasDerivAt_log_sub_logTaylor n
      (StarConvex.add_smul_mem starConvex_one_slitPlane hz ht.1 ht.2)
  have hc : ContinuousOn (fun t : ℝ => f' (0+t*z)) (Icc 0 1) := by
    simp only [zero_add]
    exact (Continuous.continuousOn (by fun_prop)).mul hi
  have he : f z=z*∫ t in (0:ℝ)..1, (-(t*z))^n*(1+t*z)⁻¹ := by
    convert (integral_unitInterval_deriv_eq_sub hc hd).symm using 1
    · simp only [f,zero_add,add_zero,log_one,logTaylor_at_zero,sub_self,sub_zero]
    · simp only [f',real_smul,zero_add,smul_eq_mul]
  unfold f at he
  rw [he,norm_mul]
  simp_rw [neg_pow (_*z) n,mul_assoc,intervalIntegral.integral_const_mul,mul_pow,
    mul_comm _ (z^n),mul_assoc,intervalIntegral.integral_const_mul,norm_mul,norm_pow,
    norm_neg,norm_one,one_pow,one_mul,← mul_assoc,← pow_succ',mul_div_assoc]
  gcongr _ * ?_
  calc
    ‖∫ t in (0:ℝ)..1, (t:ℂ)^n*(1+t*z)⁻¹‖ ≤ ∫ t in (0:ℝ)..1,t^n*C := by
      apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      · filter_upwards with t ht
        rw [norm_mul,norm_pow,Complex.norm_of_nonneg ht.1.le]
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht.1.le n)
        simpa only [Complex.real_smul] using hC t ⟨ht.1.le,ht.2⟩
      · exact (Continuous.intervalIntegrable (by fun_prop) 0 1).mul_const C
    _=C/(n+1) := by
      rw [intervalIntegral.integral_mul_const,mul_comm,integral_pow]
      simp [field]

/-- Adding one to a closed-unit-disk point other than minus one gives a slit-plane point. -/
lemma one_add_mem_slitPlane_of_norm_le_one {z : ℂ} (hz : ‖z‖≤1) (hne : z≠ -1) :
    1+z∈slitPlane := by
  have hs : z.re^2+z.im^2≤1 := by
    have h:=Complex.sq_norm z
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg z]
  have hr : -1<z.re := by
    have hb := (abs_le.mp (Complex.abs_re_le_norm z)).1
    by_contra hh
    have he : z.re = -1 := by linarith
    have him : z.im=0 := by nlinarith [sq_nonneg z.im]
    apply hne
    exact Complex.ext (by simpa using he) (by simpa using him)
  change 0<(1+z).re ∨ (1+z).im≠0
  left
  simpa using (show 0<1+z.re by linarith)

/-- The complex log Taylor polynomials converge in natural order at every valid closed-disk point. -/
lemma tendsto_logTaylor_closed {z : ℂ} (hz : ‖z‖≤1) (hne : z≠ -1) :
    Tendsto (fun n : ℕ => logTaylor (n+1) z) atTop (𝓝 (log (1+z))) := by
  obtain ⟨C,hC,hbound⟩ := exists_norm_log_sub_logTaylor_le
    (one_add_mem_slitPlane_of_norm_le_one hz hne)
  rw [← tendsto_sub_nhds_zero_iff,tendsto_zero_iff_norm_tendsto_zero]
  have hb (n : ℕ) : ‖logTaylor (n+1) z-log (1+z)‖≤C/(n+1) := by
    rw [norm_sub_rev]
    apply (hbound n).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hz (n := n+1)) hC
  apply squeeze_zero (fun _ => norm_nonneg _) hb
  have ht := (tendsto_const_div_atTop_nhds_zero_nat C).comp (tendsto_add_atTop_nat 1)
  convert ht using 1
  funext n
  simp only [Function.comp_apply,Nat.cast_add,Nat.cast_one]
end Complex
