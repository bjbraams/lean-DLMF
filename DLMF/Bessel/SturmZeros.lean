/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt

public import DLMF.Bessel.Elementary
public import DLMF.Bessel.Theorems
public import DLMF.Confluent.Asymptotics
public import DLMFMathlib.Analysis.ODE.SturmComparison

/-!
# Zeros of Bessel functions and the large-argument behaviour of `I_ν`

* `besselJ_im_eq_zero_of_eq_zero`: for real `ν > -1` every zero of `J_ν` is real (DLMF 10.21(i)).
  With `g = ₀F̃₁(ν+1; ·)` and `A = -α²/4`, the function `t ↦ t^{2ν+2}(B g(At²) g'(Bt²) -
  A g'(At²) g(Bt²))` has derivative `2(B-A) t^{2ν+1} g(At²) g(Bt²)` (a Lommel identity), so for
  `B = Ā` and `g(A) = 0` the positive integral `∫₀¹ t^{2ν+1} |g(At²)|² dt` forces `A = Ā`. The
  case `A > 0` is excluded since `I_ν` is positive.
* `besselI_sub_exp_isBigO`, `besselI_isEquivalent`: `I_ν(x) = eˣ/√(2πx) + O(eˣ x^{-3/2})`
  (DLMF 10.40.1, leading term), from `I_ν(x) = c(x) 𝐌(ν+½, 2ν+1, 2x)` and DLMF 13.7.1.
* `IsRealBesselSolution`: real solutions of Bessel's equation (real cylinder functions). Through
  the Liouville normal form `u = √x y`, `u'' + (1 - (ν²-¼)/x²) u = 0`, Sturm comparison
  (`DLMFMathlib.Analysis.ODE.SturmComparison`) gives Beals–Wong Thm 9.2.1: infinitely many positive
  zeros (`infinite_zeros`), a zero in every `(a, a+π)` for `|ν| < ½` (`exists_zero_Ioo`), and
  gaps larger than `π` for `|ν| > ½` (`pi_lt_sub`); with the corollaries for `J_ν`.
* `besselJ_succ_ne_zero_of_eq_zero`, `existsUnique_besselJ_succ_zero_between`,
  `existsUnique_besselJ_zero_between`: the positive zeros of `J_ν` and `J_{ν+1}` interlace
  strictly (DLMF 10.21.3).
-/
@[expose] public section

open Complex Filter Set Asymptotics
open scoped Real Topology Nat ComplexConjugate

noncomputable section

namespace DLMF.Bessel

/-! ### Reality of the zeros of `J_ν` -/

section RealZeros

/-- `₀F̃₁(c; ·)` with real parameter commutes with complex conjugation. -/
lemma regularized0F1_conj (c : ℝ) (w : ℂ) :
    regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} (conj w) =
      conj (regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} w) := by
  rw [regularized0F1_eq_tsum, regularized0F1_eq_tsum, Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  simp only [map_mul, map_div₀, map_pow, map_inv₀, map_natCast, ← Complex.Gamma_conj, map_add,
    conj_ofReal]

/-- The Lommel identity for `g = ₀F̃₁(c; ·)` along the rays `A t²`, `B t²`. -/
lemma hasDerivAt_lommel_regularized0F1 (c : ℝ) (A B : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ((s ^ (2 * c) : ℝ) : ℂ) *
        (B * regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} (A * (s : ℂ) ^ 2) *
            regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ) + 1} (B * (s : ℂ) ^ 2) -
          A * regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ) + 1} (A * (s : ℂ) ^ 2) *
            regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} (B * (s : ℂ) ^ 2)))
      (2 * (B - A) * ((t ^ (2 * c - 1) : ℝ) : ℂ) *
        regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} (A * (t : ℂ) ^ 2) *
          regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} (B * (t : ℂ) ^ 2)) t := by
  set g := regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)}
  set g₁ := regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ) + 1}
  have hray (C : ℂ) : HasDerivAt (fun s : ℝ => C * (s : ℂ) ^ 2) (C * (2 * t)) t := by
    have h := ((hasDerivAt_pow 2 (t : ℂ)).const_mul C).comp_ofReal
    simpa using h
  have hg (C : ℂ) := (hasDerivAt_regularized0F1 (c : ℂ) (C * (t : ℂ) ^ 2)).comp t (hray C)
  have hg₁ (C : ℂ) := (hasDerivAt_regularized0F1 ((c : ℂ) + 1) (C * (t : ℂ) ^ 2)).comp t (hray C)
  have hp := (Real.hasDerivAt_rpow_const (p := 2 * c) (Or.inl ht.ne')).ofReal_comp
  have h := hp.mul ((((hg A).const_mul B).mul (hg₁ B)).sub (((hg₁ A).const_mul A).mul (hg B)))
  convert h using 1
  · funext s
    simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, g, g₁]
  have hga := regularized0F1_contiguous (c : ℂ) (A * (t : ℂ) ^ 2)
  have hgb := regularized0F1_contiguous (c : ℂ) (B * (t : ℂ) ^ 2)
  have hr : ((t ^ (2 * c) : ℝ) : ℂ) = ((t ^ (2 * c - 1) : ℝ) : ℂ) * t := by
    rw [← ofReal_mul, Real.rpow_sub_one ht.ne', div_mul_cancel₀ _ ht.ne']
  simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, ofReal_mul, ofReal_ofNat, g]
  rw [hr]
  linear_combination (2 * ((t ^ (2 * c - 1) : ℝ) : ℂ)) *
    (B * regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} (A * (t : ℂ) ^ 2) * hgb -
      A * regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} (B * (t : ℂ) ^ 2) * hga)

/-- If `g(A) = 0` for `g = ₀F̃₁(c; ·)` with real `c > 0`, then `A` is real. -/
lemma conj_eq_of_regularized0F1_eq_zero {c : ℝ} (hc : 0 < c) {A : ℂ}
    (hA : regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} A = 0) : conj A = A := by
  set g := regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} with hgdef
  set g₁ := regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ) + 1} with hg₁def
  set B := conj A with hB
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun w =>
    (analyticAt_regularized0F1 _ w).continuousAt
  have hg₁c : Continuous g₁ := continuous_iff_continuousAt.mpr fun w =>
    (analyticAt_regularized0F1 _ w).continuousAt
  have hconj (s : ℝ) : g (B * (s : ℂ) ^ 2) = conj (g (A * (s : ℂ) ^ 2)) := by
    rw [hgdef, ← regularized0F1_conj]
    congr 1
    simp [hB, map_mul, map_pow, conj_ofReal]
  set Φ : ℝ → ℂ := fun s => ((s ^ (2 * c) : ℝ) : ℂ) *
    (B * g (A * (s : ℂ) ^ 2) * g₁ (B * (s : ℂ) ^ 2) -
      A * g₁ (A * (s : ℂ) ^ 2) * g (B * (s : ℂ) ^ 2)) with hΦ
  set w : ℝ → ℝ := fun s => s ^ (2 * c - 1) * ‖g (A * (s : ℂ) ^ 2)‖ ^ 2 with hw
  have hcont : Continuous fun s : ℝ => g (A * (s : ℂ) ^ 2) := hgc.comp (by fun_prop)
  have hwi : IntervalIntegrable w MeasureTheory.volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < 2 * c - 1)).mul_continuousOn
      ((continuous_norm.comp hcont).pow 2).continuousOn
  have hderiv (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt Φ (2 * (B - A) * (w s : ℂ)) s := by
    have h := hasDerivAt_lommel_regularized0F1 c A B hs.1
    convert h using 1
    change _ = 2 * (B - A) * ((s ^ (2 * c - 1) : ℝ) : ℂ) * g (A * (s : ℂ) ^ 2) *
      g (B * (s : ℂ) ^ 2)
    rw [hconj s, hw]
    simp only [ofReal_mul, ofReal_pow]
    linear_combination (-(2 * (B - A) * ((s ^ (2 * c - 1) : ℝ) : ℂ))) *
      mul_conj' (g (A * (s : ℂ) ^ 2))
  have hpc : Continuous fun s : ℝ => s ^ (2 * c) := Real.continuous_rpow_const (by linarith)
  have hΦc : Continuous Φ := by
    simp only [hΦ]
    fun_prop
  have hint : IntervalIntegrable (fun s => 2 * (B - A) * (w s : ℂ)) MeasureTheory.volume 0 1 :=
    (IntervalIntegrable.const_mul ⟨hwi.1.ofReal, hwi.2.ofReal⟩ _)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    hΦc.continuousOn hderiv hint
  have hgB : g B = 0 := by simpa [hA] using hconj 1
  have hΦ1 : Φ 1 = 0 := by
    simp [hΦ, hA, hgB]
  have hΦ0 : Φ 0 = 0 := by
    simp only [hΦ, Real.zero_rpow (by linarith : 2 * c ≠ 0), ofReal_zero, zero_mul]
  rw [hΦ1, hΦ0, sub_zero, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    at hFTC
  -- positivity of the weighted integral
  have hg0 : g 0 ≠ 0 := by
    rw [hgdef, DLMF.Confluent.regularizedHGFun_zero, regularizedHGFunCoeff_empty]
    simp only [Nat.factorial_zero, Nat.cast_one, CharP.cast_eq_zero, add_zero, one_mul,
      one_div, ne_eq, inv_eq_zero]
    exact Complex.Gamma_ne_zero_of_re_pos (by simpa using hc)
  have hg0' : g (A * ((0 : ℝ) : ℂ) ^ 2) ≠ 0 := by simpa using hg0
  have hev : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), g (A * ((s : ℝ) : ℂ) ^ 2) ≠ 0 :=
    hcont.continuousAt.eventually_ne hg0'
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff.mp hev
  set δ := min (ε / 2) 1 with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hmem0 : (0 : ℝ) ∈ uIcc (0 : ℝ) 1 := left_mem_uIcc
  have hmem1 : (1 : ℝ) ∈ uIcc (0 : ℝ) 1 := right_mem_uIcc
  have hmemδ : δ ∈ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le zero_le_one]; exact ⟨hδ0.le, hδ1⟩
  have hw1 := hwi.mono_set (uIcc_subset_uIcc hmem0 hmemδ)
  have hw2 := hwi.mono_set (uIcc_subset_uIcc hmemδ hmem1)
  have hpos1 : 0 < ∫ s in (0 : ℝ)..δ, w s := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hw1 (fun s hs => ?_) hδ0
    have hne : g (A * (s : ℂ) ^ 2) ≠ 0 := hεs (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]
      exact lt_of_lt_of_le hs.2 ((min_le_left _ _).trans (by linarith)))
    exact mul_pos (Real.rpow_pos_of_pos hs.1 _) (pow_pos (norm_pos_iff.mpr hne) 2)
  have hpos2 : 0 ≤ ∫ s in δ..1, w s :=
    intervalIntegral.integral_nonneg hδ1 fun s hs =>
      mul_nonneg (Real.rpow_nonneg (hδ0.le.trans hs.1) _) (sq_nonneg _)
  have hR : 0 < ∫ s in (0 : ℝ)..1, w s := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hw1 hw2]
    linarith
  have hR' : ((∫ s in (0 : ℝ)..1, w s : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  have h2 : (2 : ℂ) * (B - A) = 0 := (mul_eq_zero.mp hFTC).resolve_right hR'
  have := (mul_eq_zero.mp h2).resolve_left two_ne_zero
  exact sub_eq_zero.mp this

/-- **The zeros of `J_ν` are real** for real `ν > -1` (DLMF 10.21(i)). -/
theorem besselJ_im_eq_zero_of_eq_zero {ν : ℝ} (hν : -1 < ν) {z : ℂ}
    (hz : besselJ ν z = 0) : z.im = 0 := by
  by_contra him
  have hz0 : z ≠ 0 := fun h => him (by simp [h])
  rw [besselJ_eq_regularized] at hz
  have hp : (z / 2) ^ (ν : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero hz0 two_ne_zero))
  have hg := (mul_eq_zero.mp hz).resolve_left hp
  have hc : ((ν + 1 : ℝ) : ℂ) = (ν : ℂ) + 1 := by push_cast; ring
  rw [← hc] at hg
  have hA := conj_eq_of_regularized0F1_eq_zero (by linarith : 0 < ν + 1) hg
  have him2 : z.re * z.im = 0 := by
    have h := congrArg Complex.im hA
    simp only [conj_im, neg_im, div_im, pow_two, mul_im] at h
    norm_num at h
    nlinarith [h]
  have hre : z.re = 0 := (mul_eq_zero.mp him2).resolve_right him
  have hy : 0 < |z.im| := abs_pos.mpr him
  obtain ⟨r, hr, hI⟩ := besselI_ofReal_pos hν hy
  rw [besselI] at hI
  have hgI : regularizedHGFun (∅ : Multiset ℂ) {(ν : ℂ) + 1} (((|z.im| : ℝ) : ℂ) ^ 2 / 4) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hI
    exact hr.ne' (ofReal_eq_zero.mp hI.symm)
  apply hgI
  have hzsq : ((|z.im| : ℝ) : ℂ) ^ 2 / 4 = -(z ^ 2 / 4) := by
    set y := z.im
    have hzI : z = (y : ℂ) * I := Complex.ext (by simp [hre]) (by simp [y])
    rw [hzI, show ((|y| : ℝ) : ℂ) ^ 2 = (y : ℂ) ^ 2 by rw [← ofReal_pow, sq_abs, ofReal_pow],
      mul_pow, I_sq]
    ring
  rw [hzsq, ← hc]
  exact hg

end RealZeros

/-! ### Large-argument behaviour of `I_ν` -/

section LargeI

/-- A complex power of a positive real as an exponential. -/
lemma ofReal_cpow_eq_exp_log {r : ℝ} (hr : 0 < r) (s : ℂ) :
    (r : ℂ) ^ s = exp ((Real.log r : ℂ) * s) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), ofReal_log hr.le]

/-- The leading term of `I_ν` from the leading term of `𝐌(ν+½, 2ν+1, 2x)`. -/
lemma besselI_main_term {ν : ℂ} (hν : ∀ k : ℕ, 1 + 2 * ν ≠ -k) {x : ℝ} (hx : 0 < x) :
    ((x : ℂ) / 2) ^ ν * exp (-(x : ℂ)) * Gamma (2 * ν + 1) / Gamma (ν + 1) *
      (exp ((2 * x : ℝ) : ℂ) * ((2 * x : ℝ) : ℂ) ^ (ν + 1 / 2 - (2 * ν + 1)) /
        Gamma (ν + 1 / 2)) =
      ((Real.exp x / Real.sqrt (2 * π * x) : ℝ) : ℂ) := by
  have hdup := Complex.Gamma_mul_Gamma_add_half (ν + 1 / 2)
  have h2 : (2 : ℂ) ^ (1 - 2 * (ν + 1 / 2)) = exp ((Real.log 2 : ℂ) * (-2 * ν)) := by
    rw [← ofReal_cpow_eq_exp_log two_pos, ofReal_ofNat]
    congr 1
    ring
  rw [h2, show ν + 1 / 2 + 1 / 2 = ν + 1 by ring,
    show 2 * (ν + 1 / 2) = 2 * ν + 1 by ring] at hdup
  have ha : Gamma (ν + 1 / 2) ≠ 0 := Gamma_ne_zero fun k h => hν (2 * k) (by
    push_cast; linear_combination 2 * h)
  have hb : Gamma (ν + 1) ≠ 0 := Gamma_ne_zero fun k h => hν (2 * k + 1) (by
    push_cast; linear_combination 2 * h)
  have hs : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hE := exp_ne_zero ((Real.log 2 : ℂ) * (-2 * ν))
  have key : Gamma (2 * ν + 1) / Gamma (ν + 1) / Gamma (ν + 1 / 2) =
      1 / (exp ((Real.log 2 : ℂ) * (-2 * ν)) * (Real.sqrt π : ℂ)) := by
    rw [div_div, div_eq_div_iff (mul_ne_zero hb ha) (mul_ne_zero hE hs)]
    linear_combination -hdup
  have hx2 : (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) := by push_cast; ring
  have hsq : Real.sqrt (2 * π * x) = Real.sqrt π * Real.exp (Real.log (2 * x) / 2) := by
    rw [show 2 * π * x = π * (2 * x) by ring, Real.sqrt_mul Real.pi_pos.le,
      Real.sqrt_eq_rpow (2 * x), Real.rpow_def_of_pos (by positivity), mul_one_div]
  rw [hx2, ofReal_cpow_eq_exp_log (by positivity), ofReal_cpow_eq_exp_log (by positivity),
    Real.log_div hx.ne' two_ne_zero, Real.log_mul two_ne_zero hx.ne', hsq,
    Real.log_mul two_ne_zero hx.ne']
  set L2 := Real.log 2
  set Lx := Real.log x
  calc _ = exp (((Lx - L2 : ℝ) : ℂ) * ν) * exp (-(x : ℂ)) * exp ((2 * x : ℝ) : ℂ) *
        exp (((L2 + Lx : ℝ) : ℂ) * (ν + 1 / 2 - (2 * ν + 1))) *
        (Gamma (2 * ν + 1) / Gamma (ν + 1) / Gamma (ν + 1 / 2)) := by ring
    _ = exp ((x : ℂ) - ((L2 + Lx) / 2 : ℝ)) / (Real.sqrt π : ℂ) := by
      rw [key, ← exp_add, ← exp_add, ← exp_add]
      field_simp
      rw [← exp_add]
      congr 1
      push_cast
      ring
    _ = _ := by
      push_cast
      rw [exp_sub]
      field_simp

/-- `I_ν(x) = c(x) 𝐌(ν+½, 2ν+1, 2x)` with `c(x) = (x/2)^ν e^{-x} Γ(2ν+1)/Γ(ν+1)`. -/
lemma besselI_eq_mul_regularizedConfluent {ν : ℂ} (hν : ∀ k : ℕ, 1 + 2 * ν ≠ -k) {x : ℝ}
    (hx : 0 < x) :
    ((x : ℂ) / 2) ^ ν * exp (-(x : ℂ)) * Gamma (2 * ν + 1) / Gamma (ν + 1) *
      regularizedHGFun {ν + 1 / 2} {2 * ν + 1} ((2 * x : ℝ) : ℂ) = besselI ν x := by
  have hb : ∀ k : ℕ, 2 * ν + 1 ≠ -k := fun k h => hν k (by linear_combination h)
  have hs : (x : ℂ) ∈ slitPlane := Or.inl (by simpa using hx)
  have hK := DLMF.Confluent.kummerM_besselI ν x hs hν
  rw [DLMF.Confluent.kummerM_eq_mul_regularizedHGFun hb] at hK
  have hG : Gamma (2 * ν + 1) ≠ 0 := Gamma_ne_zero hb
  have hG1 : Gamma (ν + 1) ≠ 0 := Gamma_ne_zero fun k h => hν (2 * k + 1) (by
    push_cast; linear_combination 2 * h)
  have hx0 : (x : ℂ) / 2 ≠ 0 := div_ne_zero (ofReal_ne_zero.mpr hx.ne') two_ne_zero
  have hp : ((x : ℂ) / 2) ^ ν * ((x : ℂ) / 2) ^ (-ν) = 1 := by
    rw [cpow_neg, mul_inv_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl hx0))]
  have he : exp (-(x : ℂ)) * exp (x : ℂ) = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  have h2x : ((2 * x : ℝ) : ℂ) = 2 * (x : ℂ) := by push_cast; ring
  rw [h2x, add_comm (1 : ℂ) ν] at *
  calc _ = ((x : ℂ) / 2) ^ ν * exp (-(x : ℂ)) / Gamma (ν + 1) *
        (Gamma (2 * ν + 1) * regularizedHGFun {ν + 1 / 2} {2 * ν + 1} (2 * (x : ℂ))) := by ring
    _ = (((x : ℂ) / 2) ^ ν * ((x : ℂ) / 2) ^ (-ν)) * (exp (-(x : ℂ)) * exp (x : ℂ)) *
        (Gamma (ν + 1) / Gamma (ν + 1)) * besselI ν x := by rw [hK]; ring
    _ = _ := by rw [hp, he, div_self hG1]; ring

/-- **Large-argument behaviour of `I_ν`** (DLMF 10.40.1, leading term):
`I_ν(x) = eˣ/√(2πx) + O(eˣ x^{-3/2})` as `x → +∞`, for every `ν` with `1 + 2ν ∉ -ℕ`. -/
@[dlmf 10.40.E1]
theorem besselI_sub_exp_isBigO {ν : ℂ} (hν : ∀ k : ℕ, 1 + 2 * ν ≠ -k) :
    (fun x : ℝ => besselI ν x - ((Real.exp x / Real.sqrt (2 * π * x) : ℝ) : ℂ)) =O[atTop]
      fun x : ℝ => Real.exp x * x ^ (-(3 / 2) : ℝ) := by
  have ha : ∀ k : ℕ, ν + 1 / 2 ≠ -k := fun k h => hν (2 * k) (by
    push_cast; linear_combination 2 * h)
  have hP := (DLMF.Confluent.regularizedHGFun_poincare_real (ν + 1 / 2) (2 * ν + 1) 1
    ha).comp_tendsto (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  set c : ℝ → ℂ := fun x =>
    ((x : ℂ) / 2) ^ ν * exp (-(x : ℂ)) * Gamma (2 * ν + 1) / Gamma (ν + 1) with hc
  have hM := (isBigO_refl c atTop).mul hP
  refine (hM.congr' ?_ EventuallyEq.rfl).trans ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Function.comp_apply, id, Finset.sum_range_one, DLMF.Hypergeometric.poch_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, CharP.cast_eq_zero, neg_zero, cpow_zero,
      mul_one, hc]
    rw [mul_sub, besselI_eq_mul_regularizedConfluent hν hx, ← besselI_main_term hν hx]
  · refine isBigO_iff.mpr ⟨‖Gamma (2 * ν + 1) / Gamma (ν + 1)‖ *
      Real.exp ((-2 * ν.re - 3 / 2) * Real.log 2), ?_⟩
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    apply le_of_eq
    have hx2 : (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) := by push_cast; ring
    simp only [Function.comp_apply, id, hc, hx2, norm_mul, norm_div, Complex.norm_exp,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < x / 2),
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < 2 * x)]
    have hre : (ν + 1 / 2 - (2 * ν + 1) - ((1 : ℕ) : ℂ)).re = -ν.re - 3 / 2 := by
      simp; ring
    rw [hre, neg_re, ofReal_re, ofReal_re, Real.rpow_def_of_pos (by positivity : 0 < x / 2),
      Real.rpow_def_of_pos (by positivity : 0 < 2 * x), Real.rpow_def_of_pos hx,
      Real.log_div hx.ne' two_ne_zero, Real.log_mul two_ne_zero hx.ne']
    set K := ‖Gamma (2 * ν + 1)‖ / ‖Gamma (ν + 1)‖
    calc _ = K * Real.exp ((Real.log x - Real.log 2) * ν.re + -x + 2 * x +
          (Real.log 2 + Real.log x) * (-ν.re - 3 / 2)) := by
          simp only [Real.exp_add, K]; ring
      _ = K * Real.exp ((-2 * ν.re - 3 / 2) * Real.log 2 + x + Real.log x * (-(3 / 2))) := by
          congr 2; ring
      _ = _ := by simp only [Real.exp_add]; ring

/-- `I_ν(x) ~ eˣ/√(2πx)` as `x → +∞` (DLMF 10.40.1), for every `ν` with `1 + 2ν ∉ -ℕ`. -/
@[dlmf 10.40.E1]
theorem besselI_isEquivalent {ν : ℂ} (hν : ∀ k : ℕ, 1 + 2 * ν ≠ -k) :
    IsEquivalent atTop (fun x : ℝ => besselI ν x)
      fun x : ℝ => ((Real.exp x / Real.sqrt (2 * π * x) : ℝ) : ℂ) := by
  refine (besselI_sub_exp_isBigO hν).trans_isLittleO (IsLittleO.of_norm_right ?_)
  have h0 : Tendsto (fun x : ℝ => Real.sqrt (2 * π) / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h := (isLittleO_one_iff (F := ℝ)).mpr h0 |>.mul_isBigO
    (isBigO_refl (fun x : ℝ => ‖((Real.exp x / Real.sqrt (2 * π * x) : ℝ) : ℂ)‖) atTop)
  refine (h.congr' ?_ ?_)
  · filter_upwards [eventually_gt_atTop 0] with x hx
    rw [norm_real, Real.norm_of_nonneg (by positivity), Real.rpow_neg hx.le,
      show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one,
      ← Real.sqrt_eq_rpow, show 2 * π * x = (2 * π) * x by ring,
      Real.sqrt_mul (by positivity)]
    have h1 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
    have h2 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    field_simp
    rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by positivity)]
    ring_nf
  · exact Eventually.of_forall fun x => one_mul _

end LargeI

/-! ### Sturm comparison for real cylinder functions -/

section Sturm

/-- `y` (with derivatives `y'`, `y''`) is a real solution of Bessel's equation
`x² y'' + x y' + (x² - ν²) y = 0` on `(0, ∞)`; for example a real cylinder function. -/
def IsRealBesselSolution (ν : ℝ) (y y' y'' : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → HasDerivAt y (y' x) x ∧ HasDerivAt y' (y'' x) x ∧
    x ^ 2 * y'' x + x * y' x + (x ^ 2 - ν ^ 2) * y x = 0

variable {ν : ℝ} {y y' y'' : ℝ → ℝ}

/-- The derivative of the Liouville normal form `u = √x y`. -/
def besselNormalDeriv (y y' : ℝ → ℝ) (x : ℝ) : ℝ := y x / (2 * Real.sqrt x) + Real.sqrt x * y' x

/-- The coefficient `1 - (ν² - 1/4)/x²` of the normal form `u'' + q u = 0`. -/
def besselNormalCoeff (ν x : ℝ) : ℝ := 1 - (ν ^ 2 - 1 / 4) / x ^ 2

lemma IsRealBesselSolution.hasDerivAt_normal (hy : IsRealBesselSolution ν y y' y'') {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt (fun t => Real.sqrt t * y t) (besselNormalDeriv y y' x) x := by
  have h := (Real.hasDerivAt_sqrt hx.ne').mul (hy x hx).1
  convert h using 1
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  simp only [besselNormalDeriv]
  field_simp

/-- The Liouville normal form: `u = √x y` solves `u'' + (1 - (ν² - 1/4)/x²) u = 0`. -/
lemma IsRealBesselSolution.hasDerivAt_normalDeriv (hy : IsRealBesselSolution ν y y' y'')
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => 1 * besselNormalDeriv y y' t)
      (-(besselNormalCoeff ν x * (Real.sqrt x * y x))) x := by
  obtain ⟨hy1, hy2, hode⟩ := hy x hx
  have hsq := Real.hasDerivAt_sqrt hx.ne'
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := ((hy1.div (hsq.const_mul 2) (by positivity)).add (hsq.mul hy2)).const_mul 1
  convert h using 1
  · rfl
  have hy'' : y'' x = (-x * y' x - (x ^ 2 - ν ^ 2) * y x) / x ^ 2 := by
    field_simp
    linear_combination hode
  simp only [besselNormalCoeff]
  rw [hy'']
  have hs2 : x = Real.sqrt x ^ 2 := (Real.sq_sqrt hx.le).symm
  generalize Real.sqrt x = s at hs hs2 ⊢
  subst hs2
  field_simp
  ring

lemma eq_zero_of_sqrt_mul_eq_zero {x : ℝ} (hx : 0 < x) (h : Real.sqrt x * y x = 0) : y x = 0 :=
  (mul_eq_zero.mp h).resolve_left (Real.sqrt_pos.mpr hx).ne'

/-- For `|ν| < 1/2` every interval `(a, a + π)` with `a > 0` contains a zero of every real
solution of Bessel's equation, so consecutive zeros are less than `π` apart (Beals–Wong
Thm 9.2.1). -/
theorem IsRealBesselSolution.exists_zero_Ioo (hy : IsRealBesselSolution ν y y' y'')
    (hν : ν ^ 2 < 1 / 4) {a : ℝ} (ha : 0 < a) : ∃ x ∈ Ioo a (a + π), y x = 0 := by
  have hpi := Real.pi_pos
  have hpos (x : ℝ) (hx : x ∈ Icc a (a + π)) : 0 < x := by linarith [hx.1]
  obtain ⟨x, hx, hx0⟩ := ODE.sturm_comparison_strict (p := fun _ => 1) (q₁ := fun _ => 1)
    (q₂ := besselNormalCoeff ν) (u := fun t => Real.sin (t - a))
    (u' := fun t => Real.cos (t - a)) (v := fun t => Real.sqrt t * y t)
    (v' := besselNormalDeriv y y') (by linarith)
    (fun x _ => by simpa using ((hasDerivAt_id x).sub_const a).sin)
    (fun x _ => by simpa using ((hasDerivAt_id x).sub_const a).cos)
    (fun x hx => hy.hasDerivAt_normal (hpos x hx))
    (fun x hx => hy.hasDerivAt_normalDeriv (hpos x hx)) zero_le_one zero_le_one
    (fun x hx => by
      have hx0 : 0 < x := by linarith [hx.1]
      simp only [besselNormalCoeff]
      have : (ν ^ 2 - 1 / 4) / x ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
      linarith)
    (by simp) (by simp [Real.sin_pi])
    (fun x hx => (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])).ne')
  exact ⟨x, hx, eq_zero_of_sqrt_mul_eq_zero (by linarith [hx.1]) hx0⟩

/-- For `|ν| > 1/2` consecutive positive zeros of a real solution of Bessel's equation are more
than `π` apart (Beals–Wong Thm 9.2.1). -/
theorem IsRealBesselSolution.pi_lt_sub (hy : IsRealBesselSolution ν y y' y'')
    (hν : 1 / 4 < ν ^ 2) {c d : ℝ} (hc : 0 < c) (hcd : c < d) (hyc : y c = 0) (hyd : y d = 0)
    (hne : ∀ x ∈ Ioo c d, y x ≠ 0) : π < d - c := by
  by_contra hle
  push Not at hle
  have hpos (x : ℝ) (hx : x ∈ Icc c d) : 0 < x := by linarith [hx.1]
  obtain ⟨x, hx, hx0⟩ := ODE.sturm_comparison_strict (p := fun _ => 1)
    (q₁ := besselNormalCoeff ν) (q₂ := fun _ => 1) (u := fun t => Real.sqrt t * y t)
    (u' := besselNormalDeriv y y') (v := fun t => Real.sin (t - c))
    (v' := fun t => Real.cos (t - c)) hcd
    (fun x hx => hy.hasDerivAt_normal (hpos x hx))
    (fun x hx => hy.hasDerivAt_normalDeriv (hpos x hx))
    (fun x _ => by simpa using ((hasDerivAt_id x).sub_const c).sin)
    (fun x _ => by simpa using ((hasDerivAt_id x).sub_const c).cos)
    zero_le_one zero_le_one
    (fun x hx => by
      have hx0 : 0 < x := by linarith [hx.1]
      simp only [besselNormalCoeff]
      have : 0 < (ν ^ 2 - 1 / 4) / x ^ 2 := div_pos (by linarith) (by positivity)
      linarith)
    (by simp [hyc]) (by simp [hyd])
    (fun x hx => mul_ne_zero (Real.sqrt_pos.mpr (by linarith [hx.1])).ne' (hne x hx))
  have := Real.sin_pos_of_pos_of_lt_pi (x := x - c) (by linarith [hx.1]) (by linarith [hx.2])
  linarith

/-- Every real solution of Bessel's equation has zeros beyond any bound (Beals–Wong
Thm 9.2.1): beyond `x = 2|ν| + 1` the normal form has `q > 1/4`. -/
theorem IsRealBesselSolution.exists_zero_gt (hy : IsRealBesselSolution ν y y' y'') (M : ℝ) :
    ∃ x, M < x ∧ y x = 0 := by
  have hpi := Real.pi_pos
  set a := max M 0 + 2 * |ν| + 1 with ha
  have ha0 : 0 < a := by positivity
  have haM : M < a := by
    have := le_max_left M 0; have := abs_nonneg ν; linarith
  have hpos (x : ℝ) (hx : x ∈ Icc a (a + 2 * π)) : 0 < x := by linarith [hx.1]
  obtain ⟨x, hx, hx0⟩ := ODE.sturm_comparison_strict (p := fun _ => 1)
    (q₁ := fun _ => 1 / 4) (q₂ := besselNormalCoeff ν) (u := fun t => Real.sin ((t - a) / 2))
    (u' := fun t => Real.cos ((t - a) / 2) / 2) (v := fun t => Real.sqrt t * y t)
    (v' := besselNormalDeriv y y') (by linarith)
    (fun x _ => by
      have h := (((hasDerivAt_id' x).sub_const a).div_const 2).sin
      convert h using 1; ring)
    (fun x _ => by
      have h := ((((hasDerivAt_id' x).sub_const a).div_const 2).cos).div_const 2
      convert h using 1
      · funext t; simp only [one_mul]
      · ring)
    (fun x hx => hy.hasDerivAt_normal (hpos x hx))
    (fun x hx => hy.hasDerivAt_normalDeriv (hpos x hx)) zero_le_one zero_le_one
    (fun x hx => by
      have hx0 : 0 < x := by linarith [hx.1]
      have hxa : 2 * |ν| + 1 ≤ x := by have := le_max_right M 0; linarith [hx.1]
      have hν2 : ν ^ 2 ≤ x ^ 2 / 4 := by
        have h1 : 0 ≤ 2 * |ν| := by positivity
        have h2 : (2 * |ν|) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ h1 (by linarith) 2
        have h3 : (2 * |ν|) ^ 2 = 4 * ν ^ 2 := by rw [mul_pow, sq_abs]; ring
        linarith
      simp only [besselNormalCoeff]
      have hlt : (ν ^ 2 - 1 / 4) / x ^ 2 < 3 / 4 := by
        rw [div_lt_iff₀ (by positivity)]; nlinarith
      linarith)
    (by simp) (by simp [Real.sin_pi])
    (fun x hx => (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
      (by linarith [hx.2])).ne')
  exact ⟨x, by linarith [hx.1], eq_zero_of_sqrt_mul_eq_zero (by linarith [hx.1]) hx0⟩

/-- Every real solution of Bessel's equation has infinitely many positive zeros. -/
theorem IsRealBesselSolution.infinite_zeros (hy : IsRealBesselSolution ν y y' y'') :
    Set.Infinite {x : ℝ | 0 < x ∧ y x = 0} := by
  refine Set.infinite_of_forall_exists_gt fun M => ?_
  obtain ⟨x, hx, hx0⟩ := hy.exists_zero_gt (max M 0)
  exact ⟨x, ⟨lt_of_le_of_lt (le_max_right M 0) hx, hx0⟩, lt_of_le_of_lt (le_max_left M 0) hx⟩

/-- `x ↦ J_ν(x)` (real part) is a real solution of Bessel's equation for real `ν`. -/
theorem isRealBesselSolution_besselJ (ν : ℝ) :
    IsRealBesselSolution ν (fun x => (besselJ ν x).re) (fun x => (deriv (besselJ ν) x).re)
      (fun x => (deriv (deriv (besselJ ν)) x).re) := by
  intro x hx
  have hs : (x : ℂ) ∈ slitPlane := Or.inl (by simpa using hx)
  have ha := analyticAt_besselJ (ν : ℂ) hs
  refine ⟨ha.differentiableAt.hasDerivAt.real_of_complex,
    ha.deriv.differentiableAt.hasDerivAt.real_of_complex, ?_⟩
  have h := congrArg Complex.re (besselJ_ode (ν := (ν : ℂ)) hs)
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h
  rw [show (x : ℂ) ^ 2 = ((x ^ 2 : ℝ) : ℂ) by push_cast; ring,
    show ((x ^ 2 : ℝ) : ℂ) - (ν : ℂ) ^ 2 = ((x ^ 2 - ν ^ 2 : ℝ) : ℂ) by push_cast; ring] at h
  simpa only [add_re, re_ofReal_mul, zero_re] using h

lemma besselJ_eq_zero_iff_re {ν x : ℝ} (hx : 0 < x) :
    besselJ ν x = 0 ↔ (besselJ ν x).re = 0 := by
  constructor
  · intro h; rw [h, zero_re]
  · intro h; rw [besselJ_ofReal_eq_re ν x hx, h, ofReal_zero]

/-- For `|ν| < 1/2` every interval `(a, a + π)`, `a > 0`, contains a zero of `J_ν`. -/
theorem besselJ_exists_zero_Ioo {ν : ℝ} (hν : ν ^ 2 < 1 / 4) {a : ℝ} (ha : 0 < a) :
    ∃ x ∈ Ioo a (a + π), besselJ ν x = 0 := by
  obtain ⟨x, hx, hx0⟩ := (isRealBesselSolution_besselJ ν).exists_zero_Ioo hν ha
  exact ⟨x, hx, (besselJ_eq_zero_iff_re (ha.trans hx.1)).mpr hx0⟩

/-- For `|ν| > 1/2` consecutive positive zeros of `J_ν` are more than `π` apart. -/
theorem besselJ_pi_lt_sub {ν : ℝ} (hν : 1 / 4 < ν ^ 2) {c d : ℝ} (hc : 0 < c) (hcd : c < d)
    (hJc : besselJ ν c = 0) (hJd : besselJ ν d = 0) (hne : ∀ x ∈ Ioo c d, besselJ ν x ≠ 0) :
    π < d - c :=
  (isRealBesselSolution_besselJ ν).pi_lt_sub hν hc hcd
    ((besselJ_eq_zero_iff_re hc).mp hJc) ((besselJ_eq_zero_iff_re (hc.trans hcd)).mp hJd)
    fun x hx h => hne x hx ((besselJ_eq_zero_iff_re (hc.trans hx.1)).mpr h)

end Sturm

/-! ### Interlacing of the zeros of `J_ν` and `J_{ν+1}` -/

section Interlacing

/-- `J_ν` and `J_{ν+1}` have no common positive zero for real `ν > -1` (DLMF 10.21(i)). -/
theorem besselJ_succ_ne_zero_of_eq_zero {ν x : ℝ} (hν : -1 < ν) (hx : 0 < x)
    (h : besselJ ν x = 0) : besselJ ((ν : ℂ) + 1) x ≠ 0 := by
  have hs : (x : ℂ) ∈ slitPlane := Or.inl (by simpa using hx)
  have hd := besselJ_zeros_simple hν hx h
  rw [(hasDerivAt_besselJ hs).deriv, h, mul_zero, zero_sub, neg_ne_zero] at hd
  exact hd

/-- Between consecutive positive zeros of `J_ν` there is exactly one zero of `J_{ν+1}`
(DLMF 10.21.3). -/
theorem existsUnique_besselJ_succ_zero_between {ν a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hJa : besselJ ν a = 0) (hJb : besselJ ν b = 0) (hne : ∀ x ∈ Ioo a b, besselJ ν x ≠ 0) :
    ∃! c, c ∈ Ioo a b ∧ besselJ ((ν : ℂ) + 1) c = 0 := by
  obtain ⟨c, hc, hc0⟩ := exists_besselJ_succ_zero_between ha hab hJa hJb
  refine ⟨c, ⟨hc, hc0⟩, fun d ⟨hd, hd0⟩ => ?_⟩
  by_contra hdc
  rcases lt_or_gt_of_ne hdc with h | h
  · obtain ⟨e, he, he0⟩ := exists_besselJ_zero_between (ha.trans hd.1) h hd0 hc0
    exact hne e ⟨hd.1.trans he.1, he.2.trans hc.2⟩ he0
  · obtain ⟨e, he, he0⟩ := exists_besselJ_zero_between (ha.trans hc.1) h hc0 hd0
    exact hne e ⟨hc.1.trans he.1, he.2.trans hd.2⟩ he0

/-- Between consecutive positive zeros of `J_{ν+1}` there is exactly one zero of `J_ν`
(DLMF 10.21.3). -/
theorem existsUnique_besselJ_zero_between {ν a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hJa : besselJ ((ν : ℂ) + 1) a = 0) (hJb : besselJ ((ν : ℂ) + 1) b = 0)
    (hne : ∀ x ∈ Ioo a b, besselJ ((ν : ℂ) + 1) x ≠ 0) :
    ∃! c, c ∈ Ioo a b ∧ besselJ ν c = 0 := by
  obtain ⟨c, hc, hc0⟩ := exists_besselJ_zero_between ha hab hJa hJb
  refine ⟨c, ⟨hc, hc0⟩, fun d ⟨hd, hd0⟩ => ?_⟩
  by_contra hdc
  rcases lt_or_gt_of_ne hdc with h | h
  · obtain ⟨e, he, he0⟩ := exists_besselJ_succ_zero_between (ha.trans hd.1) h hd0 hc0
    exact hne e ⟨hd.1.trans he.1, he.2.trans hc.2⟩ he0
  · obtain ⟨e, he, he0⟩ := exists_besselJ_succ_zero_between (ha.trans hc.1) h hc0 hd0
    exact hne e ⟨hc.1.trans he.1, he.2.trans hd.2⟩ he0

end Interlacing

end DLMF.Bessel
