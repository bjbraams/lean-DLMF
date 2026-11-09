/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Moment expansions of Laplace integrals at zero

The exponential Taylor remainder on the negative real axis has a polynomial bound
uniformly on the entire half-line. This permits integration against functions with finitely
many absolutely integrable moments, without an exponential moment hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Asymptotics Finset
open scoped Topology

namespace Real

/-- On the negative real axis, the exponential Taylor remainder is bounded by its first
omitted power times a constant depending only on the truncation order. -/
theorem norm_exp_neg_sub_sum_le {x : ℝ} (hx : 0 ≤ x) (M : ℕ) :
    ‖exp (-x) - ∑ m ∈ range M, (-x) ^ m / (m.factorial : ℝ)‖ ≤
      x ^ M / ((M - 1).factorial : ℝ) := by
  rcases M with _ | n
  · simp [exp_le_one_iff.mpr (neg_nonpos.mpr hx), Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  rcases eq_or_lt_of_le hx with rfl | hx0
  · simp [Finset.sum_range_succ']
  let f : ℝ → ℝ := fun y => exp (-y)
  have hd (k : ℕ) (y : ℝ) (hy : y ∈ Icc 0 x) :
      iteratedDerivWithin k f (Icc 0 x) y = (-1 : ℝ) ^ k * exp (-y) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx0)
      (by dsimp [f]; fun_prop) hy]
    simpa only [f, neg_one_mul] using congrFun (iteratedDeriv_exp_const_mul k (-1)) y
  have ht : taylorWithinEval f n (Icc 0 x) 0 x =
      ∑ m ∈ range (n + 1), (-x) ^ m / (m.factorial : ℝ) := by
    rw [taylor_within_apply]
    apply sum_congr rfl
    intro m _
    rw [hd m 0 ⟨le_rfl, hx⟩]
    simp only [sub_zero, neg_zero, exp_zero, mul_one, smul_eq_mul,
      div_eq_mul_inv]
    rw [neg_pow]
    ring
  have hb (y : ℝ) (hy : y ∈ Icc 0 x) :
      ‖iteratedDerivWithin (n + 1) f (Icc 0 x) y‖ ≤ 1 := by
    rw [hd _ _ hy, norm_mul, norm_pow]
    simpa using exp_le_one_iff.mpr (neg_nonpos.mpr hy.1)
  simpa only [f, ht, one_mul, sub_zero, Nat.add_sub_cancel] using
    taylor_mean_remainder_bound hx (by dsimp [f]; fun_prop) ⟨hx, le_rfl⟩ hb

end Real

namespace Complex

/-- The same negative-axis exponential remainder estimate, in the complex norm. -/
theorem norm_exp_neg_ofReal_sub_sum_le {x : ℝ} (hx : 0 ≤ x) (M : ℕ) :
    ‖exp (-(x : ℂ)) - ∑ m ∈ range M, (-(x : ℂ)) ^ m / (m.factorial : ℂ)‖ ≤
      x ^ M / ((M - 1).factorial : ℝ) := by
  have he : exp (-(x : ℂ)) - ∑ m ∈ range M, (-(x : ℂ)) ^ m / (m.factorial : ℂ) =
      ((Real.exp (-x) - ∑ m ∈ range M, (-x) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he, norm_real]
  exact Real.norm_exp_neg_sub_sum_le hx M

end Complex

namespace MeasureTheory

/-- Multiplication by a decaying real exponential preserves integrability on the positive
half-line. The conclusion is written with the complex exponential. -/
theorem IntegrableOn.cexp_neg_mul_of_nonneg {f : ℝ → ℂ}
    (hf : IntegrableOn f (Ioi 0)) {ζ : ℝ} (hζ : 0 ≤ ζ) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(ζ : ℂ) * t) * f t) (Ioi 0) := by
  refine hf.norm.mono' ((by fun_prop : Continuous fun t : ℝ =>
    Complex.exp (-(ζ : ℂ) * t)).aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hζ) ht.le))

end MeasureTheory

namespace Asymptotics

/-- Absolutely integrable moments through order `M` give the Taylor expansion of a Laplace
integral through degree `M-1`, with a remainder `O(ζ^M)` at `ζ = 0+`. -/
theorem isBigO_integral_exp_neg_mul_sub_sum {f : ℝ → ℂ} (M : ℕ)
    (hm : ∀ m ≤ M, IntegrableOn (fun t : ℝ => (t : ℂ) ^ m * f t) (Ioi 0)) :
    (fun ζ : ℝ => (∫ t in Ioi (0 : ℝ), Complex.exp (-(ζ : ℂ) * t) * f t) -
      ∑ m ∈ range M, (-(ζ : ℂ)) ^ m / (m.factorial : ℂ) *
        ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ m * f t) =O[𝓝[>] 0] (fun ζ : ℝ => ζ ^ M) := by
  have hf : IntegrableOn f (Ioi 0) := by simpa using hm 0 (Nat.zero_le M)
  let B := ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ M * f t‖
  refine IsBigO.of_bound (B / ((M - 1).factorial : ℝ)) ?_
  filter_upwards [self_mem_nhdsWithin] with ζ hζ
  let P : ℝ → ℂ := fun t => ∑ m ∈ range M,
    ((-(ζ : ℂ)) ^ m / (m.factorial : ℂ)) * ((t : ℂ) ^ m * f t)
  have hiL := hf.cexp_neg_mul_of_nonneg hζ.le
  have hiP : IntegrableOn P (Ioi 0) := integrable_finsetSum _ (fun m hm' =>
    (hm m (Nat.le_of_lt (mem_range.mp hm'))).const_mul _)
  have hpoly : (∫ t in Ioi (0 : ℝ), P t) =
      ∑ m ∈ range M, (-(ζ : ℂ)) ^ m / (m.factorial : ℂ) *
        ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ m * f t := by
    rw [integral_finsetSum _ (fun m hm' =>
      (hm m (Nat.le_of_lt (mem_range.mp hm'))).const_mul _)]
    simp only [integral_const_mul]
  have hrem (t : ℝ) : Complex.exp (-(ζ : ℂ) * t) * f t - P t =
      (Complex.exp (-(ζ : ℂ) * t) -
        ∑ m ∈ range M, (-(ζ * t : ℝ) : ℂ) ^ m / (m.factorial : ℂ)) * f t := by
    simp only [P, sub_mul, Finset.sum_mul]
    congr 1
    apply sum_congr rfl
    intro m _
    push_cast
    rw [← neg_mul, mul_pow]
    ring
  have hbound (t : ℝ) (ht : 0 < t) :
      ‖Complex.exp (-(ζ : ℂ) * t) * f t - P t‖ ≤
        (ζ ^ M / ((M - 1).factorial : ℝ)) * ‖(t : ℂ) ^ M * f t‖ := by
    rw [hrem, norm_mul]
    have hb := Complex.norm_exp_neg_ofReal_sub_sum_le (mul_nonneg hζ.le ht.le) M
    have he : -(ζ : ℂ) * (t : ℂ) = -((ζ * t : ℝ) : ℂ) := by push_cast; ring
    rw [he]
    have h := mul_le_mul_of_nonneg_right hb (norm_nonneg (f t))
    convert h using 1
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le, mul_pow]
    ring
  have hmajor : IntegrableOn (fun t : ℝ =>
      (ζ ^ M / ((M - 1).factorial : ℝ)) * ‖(t : ℂ) ^ M * f t‖) (Ioi 0) :=
    (hm M le_rfl).norm.const_mul _
  rw [← hpoly, ← integral_sub hiL hiP]
  have hb := norm_integral_le_of_norm_le hmajor (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hbound t ht)
  rw [integral_const_mul] at hb
  have hζnorm : ‖ζ ^ M‖ = ζ ^ M := Real.norm_of_nonneg (pow_nonneg hζ.le M)
  rw [hζnorm]
  exact hb.trans_eq (by dsimp [B]; ring)

end Asymptotics
