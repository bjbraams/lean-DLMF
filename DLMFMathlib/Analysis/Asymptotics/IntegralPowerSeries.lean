/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import DLMFMathlib.Analysis.Asymptotics.IntegralComparison

/-!
# Termwise integration of asymptotic inverse power series

An integrable power bound at infinity passes to the tail integral. Consequently a Poincaré
expansion whose constant and inverse-linear coefficients vanish can be integrated termwise
from `x` to infinity. This is the convergent-tail case of DLMF §2.1(ii).
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory Asymptotics Finset
open scoped Topology

namespace Asymptotics

/-- Integrating a power bound of order strictly below `-1` gives the corresponding tail bound. -/
theorem IsBigO.integral_Ioi_rpow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {r : ℝ} (hf : f =O[atTop] fun t : ℝ => t ^ r) (hr : r < -1) :
    (fun x : ℝ => ∫ t in Ioi x, f t) =O[atTop] fun x : ℝ => x ^ (r + 1) := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨A, hA⟩ := eventually_atTop.mp hC
  refine IsBigO.of_bound (C / (-(r + 1))) ?_
  filter_upwards [eventually_ge_atTop A, eventually_gt_atTop 0] with x hxA hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
  calc ‖∫ t in Ioi x, f t‖ ≤ ∫ t in Ioi x, C * t ^ r := by
        refine norm_integral_le_of_norm_le
          ((integrableOn_Ioi_rpow_of_lt hr hx).const_mul C) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have h := hA t (hxA.trans ht.le)
        simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (hx.trans ht).le _)] using h
    _ = C / (-(r + 1)) * x ^ (r + 1) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt hr hx]
        rw [div_neg]
        ring

/-- Positive inverse powers have the usual elementary tail integral. -/
theorem integral_Ioi_inv_pow {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (∫ t in Ioi x, t⁻¹ ^ (n + 2)) = x⁻¹ ^ (n + 1) / (n + 1 : ℝ) := by
  have hr : -((n : ℝ) + 2) < -1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hpow : ∀ t ∈ Ioi x, t⁻¹ ^ (n + 2) = t ^ (-((n : ℝ) + 2)) := by
    intro t ht
    rw [Real.rpow_neg (hx.trans ht).le]
    norm_cast
    rw [inv_pow]
  rw [setIntegral_congr_fun measurableSet_Ioi hpow, integral_Ioi_rpow_of_lt hr hx]
  rw [show -((n : ℝ) + 2) + 1 = -((n : ℝ) + 1) by ring, neg_div_neg_eq,
    Real.rpow_neg hx.le]
  rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast, inv_pow]

/-- Termwise tail integration of a complex-valued Poincaré expansion with vanishing
constant and inverse-linear terms. Continuity is only needed on the positive half-line. -/
theorem HasAsymptoticExpansion.integral_Ioi_inv_pow {f : ℝ → ℂ} {a : ℕ → ℂ} {x₀ : ℝ}
    (hf : HasAsymptoticExpansion atTop (fun n (x : ℝ) => x⁻¹ ^ n) a f)
    (ha0 : a 0 = 0) (ha1 : a 1 = 0) (hx₀ : 0 < x₀) (hfc : ContinuousOn f (Ici x₀)) :
    HasAsymptoticExpansion atTop (fun n (x : ℝ) => x⁻¹ ^ (n + 1))
      (fun n => ((n + 1 : ℂ)⁻¹) * a (n + 2)) (fun x => ∫ t in Ioi x, f t) := by
  have hscale (n : ℕ) : (fun x : ℝ => x⁻¹ ^ n) =ᶠ[atTop]
      (fun x : ℝ => x ^ (-(n : ℝ))) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.rpow_neg hx.le, Real.rpow_natCast, inv_pow]
  have hsum (N : ℕ) (t : ℝ) :
      ∑ n ∈ range (N + 2), t⁻¹ ^ n • a n =
        ∑ n ∈ range N, t⁻¹ ^ (n + 2) • a (n + 2) := by
    rw [show N + 2 = 2 + N by omega, sum_range_add]
    simp [sum_range_succ, ha0, ha1, Nat.add_comm]
  have hzero : f =O[atTop] fun x : ℝ => x ^ (-2 : ℝ) := by
    have h := hf 2
    simpa only [sum_range_succ, range_zero, sum_empty, ha0, ha1, smul_zero, add_zero,
      sub_zero, Nat.cast_ofNat] using h.congr' .rfl (hscale 2)
  have hfi : IntegrableOn f (Ici x₀) := by
    have hbig : f =O[atTop] fun x : ℝ => (x : ℂ) ^ (-2 : ℂ) := by
      refine hzero.trans (IsBigO.of_bound 1 ?_)
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp
    exact hfc.integrableOn_Ici_of_isBigO_cpow hx₀ (by norm_num) hbig
  intro N
  let R : ℝ → ℂ := fun t => f t - ∑ n ∈ range N, t⁻¹ ^ (n + 2) • a (n + 2)
  have hR : R =O[atTop] fun x : ℝ => x ^ (-((N : ℝ) + 2)) := by
    simpa only [hsum, Nat.cast_add, Nat.cast_ofNat] using
      (hf (N + 2)).congr' .rfl (hscale (N + 2))
  have hb := hR.integral_Ioi_rpow
    (by linarith [Nat.cast_nonneg (α := ℝ) N] : -((N : ℝ) + 2) < -1)
  have he : (fun x : ℝ => x ^ (-((N : ℝ) + 2) + 1)) =ᶠ[atTop]
      fun x : ℝ => x⁻¹ ^ (N + 1) := by
    convert (hscale (N + 1)).symm using 1
    congr 1
    push_cast
    ring
  refine hb.congr' ?_ he
  filter_upwards [eventually_ge_atTop x₀] with x hx
  have hx0 : 0 < x := hx₀.trans_le hx
  have ht (n : ℕ) : IntegrableOn (fun t : ℝ => t⁻¹ ^ (n + 2) • a (n + 2)) (Ioi x) := by
    have hr : -((n : ℝ) + 2) < -1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hi := (integrableOn_Ioi_rpow_of_lt hr hx0).smul_const (a (n + 2))
    refine IntegrableOn.congr_fun hi (fun t ht => ?_) measurableSet_Ioi
    rw [Real.rpow_neg (hx0.trans ht).le]
    norm_cast
    rw [inv_pow]
  simp only [R]
  rw [integral_sub (hfi.mono_set (fun t ht => hx.trans (show x < t from ht).le))
      (integrable_finsetSum (range N) (fun n _ => ht n)),
    integral_finsetSum _ (fun n _ => ht n)]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  rw [integral_smul_const, Asymptotics.integral_Ioi_inv_pow hx0 n, Complex.real_smul,
    Complex.real_smul]
  push_cast
  ring

end Asymptotics
