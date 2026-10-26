/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Euler–Maclaurin continuation of the Hurwitz zeta function: the core (DLMF §25.11(i))

This module holds the part of `DLMF.Zeta.R25bHurwitzContinuation` that does not depend on
`DLMF.IncompleteGamma.ZerosIntegrals`, so that the latter can import it. It holds the
definition of `DLMF.Confluent.hurwitzZetaComplex s z` (moved here from
`DLMF.IncompleteGamma.ZerosIntegrals` on 2026-10-26), the limit of the Euler–Maclaurin sequence
`E_N(s, z) = ∑_{n<N} (z+n)^{-s} + (z+N)^{1-s}/(s-1) + (z+N)^{-s}/2
  + ∑_{k<M} B_{2k+2}/(2k+2)! (s)_{2k+1} (z+N)^{-s-2k-1}`,
and proves that the limit exists for every `s ≠ 1` and every `z`, that it is the same for every
admissible number `M` of correction terms (`Re s > -2M`), that it is holomorphic in `s ≠ 1` for
`z ≠ 0, -1, -2, …`, and that it agrees with Mathlib's `hurwitzZeta` for real `0 < x ≤ 1`
(`s25b_hzc_mathlib`).
-/

@[expose] public section

open Complex Filter Set MeasureTheory intervalIntegral
open scoped Nat Real Topology

noncomputable section

namespace DLMF.Zeta

open DLMF.Hypergeometric (poch poch_succ poch_zero)

/-- One step of integration by parts against Bernoulli polynomials on `[0,1]`. -/
lemma r25b_integral_bernoulli_mul_step {u u' : ℝ → ℂ} (p : ℕ)
    (hu : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt u (u' x) x) (hu' : ContinuousOn u' (Icc 0 1)) :
    ∫ x in (0 : ℝ)..1, u x * (bernoulliFun p x : ℂ) =
      ((p : ℂ) + 1)⁻¹ * (u 1 * bernoulliFun (p + 1) 1 - u 0 * bernoulliFun (p + 1) 0 -
        ∫ x in (0 : ℝ)..1, u' x * (bernoulliFun (p + 1) x : ℂ)) := by
  have hp : ((p : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
  have hv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ((bernoulliFun (p + 1) y : ℝ) : ℂ) / ((p : ℂ) + 1))
      (bernoulliFun p x : ℂ) x := by
    intro x
    have h := ((hasDerivAt_bernoulliFun (p + 1) x).ofReal_comp).div_const ((p : ℂ) + 1)
    convert h using 1
    push_cast
    field_simp
  have hcu : ContinuousOn u (Icc 0 1) := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have huI : ∀ x ∈ Ioo (min (0:ℝ) 1) (max 0 1), HasDerivAt u (u' x) x := fun x hx =>
    hu x (by simp at hx; exact ⟨hx.1.le, hx.2.le⟩)
  have h := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (a := 0) (b := 1)
    (u := u) (v := fun y : ℝ => ((bernoulliFun (p + 1) y : ℝ) : ℂ) / ((p : ℂ) + 1))
    (by simpa [uIcc_of_le zero_le_one] using hcu)
    (Continuous.continuousOn (by fun_prop [continuous_bernoulliFun]))
    huI (fun x _ => hv x)
    (by apply ContinuousOn.intervalIntegrable; simpa [uIcc_of_le zero_le_one] using hu')
    (Continuous.intervalIntegrable (by
      have := continuous_bernoulliFun p
      fun_prop) _ _)
  rw [h]
  have : ∫ x in (0 : ℝ)..1, u' x * (((bernoulliFun (p + 1) x : ℝ) : ℂ) / ((p : ℂ) + 1)) =
      ((p : ℂ) + 1)⁻¹ * ∫ x in (0 : ℝ)..1, u' x * (bernoulliFun (p + 1) x : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext x; field_simp
  rw [this]
  field_simp

/-- The one-interval Euler–Maclaurin identity on `[0, 1]` for a family `f j` with
`f j' = f (j+1)` on `[0, 1]`. -/
lemma r25b_integral_eq_sum_bernoulliFun (f : ℕ → ℝ → ℂ)
    (hf : ∀ j, ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt (f j) (f (j + 1) x) x) (p : ℕ) :
    ∫ x in (0 : ℝ)..1, f 0 x =
      ∑ j ∈ Finset.range p, ((-1 : ℂ) ^ j / (j + 1)!) *
        (f j 1 * bernoulliFun (j + 1) 1 - f j 0 * bernoulliFun (j + 1) 0) +
      ((-1 : ℂ) ^ p / p !) * ∫ x in (0 : ℝ)..1, f p x * (bernoulliFun p x : ℂ) := by
  induction p with
  | zero => simp [bernoulliFun_zero]
  | succ p ih =>
    have hc : ContinuousOn (f (p + 1)) (Icc 0 1) := fun x hx =>
      (hf (p + 1) x hx).continuousAt.continuousWithinAt
    rw [ih, r25b_integral_bernoulli_mul_step p (hf p) hc, Finset.sum_range_succ, add_assoc]
    congr 1
    have hp : ((p : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
    have hfac : ((p + 1)! : ℂ) = ((p : ℂ) + 1) * p ! := by push_cast [Nat.factorial_succ]; ring
    have hpf : (p ! : ℂ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
    rw [hfac, pow_succ]
    field_simp
    ring


lemma r25b_hasDerivAt_cpow_shift {w c : ℂ} {t : ℝ} (h : w + t ∈ slitPlane) :
    HasDerivAt (fun y : ℝ => (w + y) ^ c) (c * (w + t) ^ (c - 1)) t := by
  have := ((hasDerivAt_id (t : ℂ)).const_add w).cpow_const (c := c) h
  simpa using this.comp_ofReal

lemma r25b_mem_slitPlane {w : ℂ} (hw : 0 < w.re) {t : ℝ} (ht : 0 ≤ t) : w + t ∈ slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))

/-- The derivative family of `t ↦ (w+t)^{-s}`. -/
def r25b_fam (s w : ℂ) (j : ℕ) (t : ℝ) : ℂ := (-1) ^ j * poch s j * (w + t) ^ (-s - j)

lemma r25b_hasDerivAt_fam {s w : ℂ} (hw : 0 < w.re) (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (r25b_fam s w j) (r25b_fam s w (j + 1) t) t := by
  have h := (r25b_hasDerivAt_cpow_shift (c := -s - j) (r25b_mem_slitPlane hw ht)).const_mul
    ((-1) ^ j * poch s j)
  unfold r25b_fam
  convert h using 1
  rw [show -s - ((j + 1 : ℕ) : ℂ) = -s - j - 1 by push_cast; ring, poch_succ, pow_succ]
  ring

/-- The coefficient `B_{2k+2}/(2k+2)! · (s)_{2k+1}` of the Euler–Maclaurin correction terms. -/
def r25b_emC (s : ℂ) (k : ℕ) : ℂ :=
  (bernoulli (2 * k + 2) : ℂ) / (2 * k + 2).factorial * poch s (2 * k + 1)

/-- The Euler–Maclaurin tail `w^{1-s}/(s-1) + w^{-s}/2 + ∑_{k<M} c_k w^{-s-2k-1}`. -/
def r25b_emF (M : ℕ) (s w : ℂ) : ℂ :=
  w ^ (1 - s) / (s - 1) + w ^ (-s) / 2 +
    ∑ k ∈ Finset.range M, r25b_emC s k * w ^ (-s - (2 * k + 1))

lemma r25b_sum_range_two_mul (T : ℕ → ℂ) (M : ℕ) :
    ∑ j ∈ Finset.range (2 * M), T j = ∑ k ∈ Finset.range M, (T (2 * k) + T (2 * k + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

/-- **The one-step Euler–Maclaurin identity**: for `Re w > 0` and `s ≠ 1`,
`w^{-s} + F(w+1) - F(w) = -((s)_{2M+1}/(2M+1)!) ∫_0^1 (w+t)^{-s-2M-1} B_{2M+1}(t) dt`. -/
lemma r25b_emF_diff {s w : ℂ} (hs : s ≠ 1) (hw : 0 < w.re) (M : ℕ) :
    w ^ (-s) + r25b_emF M s (w + 1) - r25b_emF M s w =
      -(poch s (2 * M + 1) / (2 * M + 1 : ℕ)!) *
        ∫ t in (0 : ℝ)..1, (w + t) ^ (-s - (2 * M + 1 : ℕ)) * (bernoulliFun (2 * M + 1) t : ℂ) := by
  have EM := r25b_integral_eq_sum_bernoulliFun (r25b_fam s w)
    (fun j x hx => r25b_hasDerivAt_fam hw j hx.1) (2 * M + 1)
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hs2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hint :
      ∫ t in (0 : ℝ)..1, r25b_fam s w 0 t = ((w + 1) ^ (1 - s) - w ^ (1 - s)) / (1 - s) := by
    have hF : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => (w + y) ^ (1 - s) / (1 - s))
        (r25b_fam s w 0 x) x := by
      intro x hx
      rw [uIcc_of_le zero_le_one] at hx
      have := (r25b_hasDerivAt_cpow_shift (c := 1 - s) (r25b_mem_slitPlane hw hx.1)).div_const
        (1 - s)
      convert this using 1
      simp only [r25b_fam, pow_zero, poch_zero, Nat.cast_zero, sub_zero, one_mul]
      field_simp
      ring_nf
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF]
    · simp; ring
    · apply ContinuousOn.intervalIntegrable
      intro x hx
      exact (r25b_hasDerivAt_fam hw 0 (by rw [uIcc_of_le zero_le_one] at hx; exact hx.1)
        ).continuousAt.continuousWithinAt
  rw [hint, Finset.sum_range_succ', r25b_sum_range_two_mul] at EM
  have hodd : ∀ k : ℕ, (-1 : ℂ) ^ (2 * k + 1) / (((2 * k + 1 + 1)! : ℕ) : ℂ) *
      (r25b_fam s w (2 * k + 1) 1 * (bernoulliFun (2 * k + 1 + 1) 1 : ℂ) -
        r25b_fam s w (2 * k + 1) 0 * (bernoulliFun (2 * k + 1 + 1) 0 : ℂ)) =
      r25b_emC s k * ((w + 1) ^ (-s - (2 * k + 1)) - w ^ (-s - (2 * k + 1))) := by
    intro k
    have hb : bernoulliFun (2 * k + 1 + 1) 1 = bernoulli (2 * k + 2) := by
      rw [bernoulliFun_endpoints_eq_of_ne_one (by omega), bernoulliFun_eval_zero]
    have hb0 : bernoulliFun (2 * k + 1 + 1) 0 = bernoulli (2 * k + 2) := bernoulliFun_eval_zero _
    have hm : ((-1 : ℂ)) ^ (2 * k + 1) * (-1) ^ (2 * k + 1) = 1 := by rw [← mul_pow]; simp
    simp only [r25b_fam, hb, hb0, r25b_emC, ofReal_one, ofReal_zero, add_zero]
    rw [show 2 * k + 1 + 1 = 2 * k + 2 from rfl]
    push_cast
    linear_combination ((bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℕ) * poch s (2 * k + 1) *
      ((w + 1) ^ (-s - (2 * k + 1)) - w ^ (-s - (2 * k + 1)))) * hm
  have heven : ∀ k : ℕ, (-1 : ℂ) ^ (2 * k + 1 + 1) / (((2 * k + 1 + 1 + 1)! : ℕ) : ℂ) *
      (r25b_fam s w (2 * k + 1 + 1) 1 * (bernoulliFun (2 * k + 1 + 1 + 1) 1 : ℂ) -
        r25b_fam s w (2 * k + 1 + 1) 0 * (bernoulliFun (2 * k + 1 + 1 + 1) 0 : ℂ)) = 0 := by
    intro k
    have hb0 : bernoulliFun (2 * k + 1 + 1 + 1) 0 = 0 := by
      rw [bernoulliFun_eval_zero, bernoulli_eq_zero_of_odd ⟨k + 1, by ring⟩ (by omega)]; simp
    have hb : bernoulliFun (2 * k + 1 + 1 + 1) 1 = 0 := by
      rw [bernoulliFun_endpoints_eq_of_ne_one (by omega), hb0]
    simp [hb, hb0]
  simp only [hodd, heven, add_zero] at EM
  have hR : ∫ x in (0 : ℝ)..1, r25b_fam s w (2 * M + 1) x * (bernoulliFun (2 * M + 1) x : ℂ) =
      (-1) ^ (2 * M + 1) * poch s (2 * M + 1) * ∫ t in (0 : ℝ)..1,
        (w + t) ^ (-s - (2 * M + 1 : ℕ)) * (bernoulliFun (2 * M + 1) t : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext t; simp only [r25b_fam]; ring
  have h0 : r25b_fam s w 0 1 = (w + 1) ^ (-s) := by simp [r25b_fam, poch_zero]
  have h0' : r25b_fam s w 0 0 = w ^ (-s) := by simp [r25b_fam, poch_zero]
  have hm : ((-1 : ℂ)) ^ (2 * M + 1) * (-1) ^ (2 * M + 1) = 1 := by rw [← mul_pow]; simp
  rw [hR, h0, h0'] at EM
  simp only [mul_sub, Finset.sum_sub_distrib, bernoulliFun_one, zero_add, pow_zero,
    Nat.factorial_one, Nat.cast_one, div_one, one_mul] at EM
  rw [show ((w + 1) ^ (1 - s) - w ^ (1 - s)) / (1 - s) =
    -(((w + 1) ^ (1 - s) - w ^ (1 - s)) / (s - 1)) by rw [← div_neg, neg_sub]] at EM
  unfold r25b_emF
  set I := ∫ t in (0 : ℝ)..1, (w + t) ^ (-s - (2 * M + 1 : ℕ)) * (bernoulliFun (2 * M + 1) t : ℂ)
  push_cast at EM
  linear_combination (-1 : ℂ) * EM - (poch s (2 * M + 1) / ((2 * M + 1)! : ℕ) * I) * hm

/-- Bound for a principal power on a right half-plane with nonpositive real exponent. -/
lemma r25b_norm_cpow_le {x u : ℂ} {c : ℝ} (hc : 0 < c) (hx : c ≤ x.re) (hu : u.re ≤ 0) :
    ‖x ^ u‖ ≤ c ^ u.re * Real.exp (π * |u.im|) := by
  refine (norm_cpow_le _ _).trans ?_
  rw [div_eq_mul_inv, ← Real.exp_neg]
  have h1 : ‖x‖ ^ u.re ≤ c ^ u.re := Real.rpow_le_rpow_of_nonpos hc (hx.trans (re_le_norm x)) hu
  have h2 : Real.exp (-(arg x * u.im)) ≤ Real.exp (π * |u.im|) := by
    rw [Real.exp_le_exp]
    have harg := abs_arg_le_pi x
    calc -(arg x * u.im) ≤ |arg x| * |u.im| := by rw [← abs_mul]; exact neg_le_abs _
      _ ≤ π * |u.im| := by gcongr
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

/-- **Bound for the Euler–Maclaurin step**: there is `C` with
`‖w^{-s} + F(w+1) - F(w)‖ ≤ C ‖(s)_{2M+1}‖ (Re w)^{-(Re s + 2M + 1)} e^{π |Im s|}`
for `Re w > 0`, `Re s + 2M + 1 ≥ 0`, `s ≠ 1`. -/
lemma r25b_norm_emF_diff_le (M : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s w : ℂ, s ≠ 1 → 0 < w.re →
    0 ≤ s.re + (2 * M + 1) →
    ‖w ^ (-s) + r25b_emF M s (w + 1) - r25b_emF M s w‖ ≤
      C * ‖poch s (2 * M + 1)‖ * w.re ^ (-(s.re + (2 * M + 1))) * Real.exp (π * |s.im|) := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ y ∈ Icc (0 : ℝ) 1, ‖bernoulliFun (2 * M + 1) y‖ ≤ B :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc
      (continuous_bernoulliFun (2 * M + 1)).continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨B / ((2 * M + 1 : ℕ)! : ℝ), by positivity, fun s w hs hw hsM => ?_⟩
  rw [r25b_emF_diff hs hw M, norm_mul, norm_neg, norm_div, Complex.norm_natCast]
  have hI : ‖∫ t in (0 : ℝ)..1, (w + t) ^ (-s - (2 * M + 1 : ℕ)) *
      (bernoulliFun (2 * M + 1) t : ℂ)‖ ≤
      (w.re ^ (-(s.re + (2 * M + 1))) * Real.exp (π * |s.im|)) * B := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := (w.re ^ (-(s.re + (2 * M + 1))) * Real.exp (π * |s.im|)) * B)
      (f := fun t : ℝ => (w + t) ^ (-s - (2 * M + 1 : ℕ)) * (bernoulliFun (2 * M + 1) t : ℂ))
      (by
        intro t ht
        rw [uIoc_of_le zero_le_one] at ht
        rw [norm_mul, Complex.norm_real]
        gcongr
        · have h := r25b_norm_cpow_le (x := w + t) (u := -s - (2 * M + 1 : ℕ)) hw
            (by simp; linarith [ht.1]) (by simp; linarith)
          convert h using 3 <;> simp; ring
        · exact hB t ⟨ht.1.le, ht.2⟩)
    simpa using this
  calc ‖poch s (2 * M + 1)‖ / ((2 * M + 1 : ℕ)! : ℝ) * ‖∫ t in (0 : ℝ)..1,
        (w + t) ^ (-s - (2 * M + 1 : ℕ)) * (bernoulliFun (2 * M + 1) t : ℂ)‖
      ≤ ‖poch s (2 * M + 1)‖ / ((2 * M + 1 : ℕ)! : ℝ) *
        ((w.re ^ (-(s.re + (2 * M + 1))) * Real.exp (π * |s.im|)) * B) := by gcongr
    _ = _ := by ring

/-- The Euler–Maclaurin sequence with `M` correction terms:
`∑_{n<N} (z+n)^{-s} + F_M(s, z+N)`. -/
def r25b_emSeq (M : ℕ) (s z : ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, (z + n) ^ (-s)) + r25b_emF M s (z + N)

/-- The increment of the Euler–Maclaurin sequence. -/
def r25b_emD (M : ℕ) (s w : ℂ) : ℂ :=
  w ^ (-s) + r25b_emF M s (w + 1) - r25b_emF M s w

lemma r25b_emSeq_add (M : ℕ) (s z : ℂ) (N₀ N : ℕ) :
    r25b_emSeq M s z (N₀ + N) =
      r25b_emSeq M s z N₀ + ∑ n ∈ Finset.range N, r25b_emD M s (z + (N₀ + n : ℕ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [← add_assoc, Finset.sum_range_succ, ← add_assoc, ← ih]
    simp only [r25b_emSeq, r25b_emD, Finset.sum_range_succ]
    push_cast
    ring_nf

lemma r25b_norm_poch_le {s : ℂ} {R : ℝ} (hR : 0 ≤ R) (hs : ‖s‖ ≤ R) (n : ℕ) :
    ‖poch s n‖ ≤ (R + n) ^ n := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [poch_succ, norm_mul, pow_succ]
    have h1 : ‖s + n‖ ≤ R + n := (norm_add_le _ _).trans (by simp [hs])
    have h2 : (R + n) ^ n ≤ (R + (n + 1 : ℕ)) ^ n := by gcongr; linarith
    have h3 : R + n ≤ R + (n + 1 : ℕ) := by push_cast; linarith
    exact mul_le_mul (ih.trans h2) (h1.trans h3) (norm_nonneg _) (by positivity)

/-- A summable majorant for the Euler–Maclaurin increments on a bounded set of `(s, z)` with
`Re s ≥ σ > -2M` and `s ≠ 1`. -/
lemma r25b_exists_summable_bound_emD {M : ℕ} {K : Set (ℂ × ℂ)} {R σ : ℝ} (hR : 0 ≤ R)
    (hσ : 0 < σ + 2 * M) (hK : ∀ q ∈ K, ‖q.1‖ ≤ R ∧ ‖q.2‖ ≤ R ∧ σ ≤ q.1.re ∧ q.1 ≠ 1) :
    ∃ u : ℕ → ℝ, Summable u ∧ (∀ n, 0 ≤ u n) ∧
      ∀ n : ℕ, ∀ q ∈ K, ‖r25b_emD M q.1 (q.2 + (⌈R⌉₊ + 1 + n : ℕ))‖ ≤ u n := by
  obtain ⟨C, hC0, hC⟩ := r25b_norm_emF_diff_le M
  set N₀ := ⌈R⌉₊ + 1
  set τ : ℝ := σ + (2 * M + 1)
  have hτ : 1 < τ := by simp only [τ]; linarith
  set u : ℕ → ℝ := fun n => C * (R + (2 * M + 1 : ℕ)) ^ (2 * M + 1) * Real.exp (π * R) *
    ((n : ℝ) + 1) ^ (-τ)
  have hu : Summable u := by
    refine Summable.mul_left _ ?_
    have := (Real.summable_nat_rpow.mpr (show -τ < -1 by linarith))
    exact_mod_cast (summable_nat_add_iff 1).mpr this
  have hbound : ∀ n : ℕ, ∀ q ∈ K, ‖r25b_emD M q.1 (q.2 + (N₀ + n : ℕ))‖ ≤ u n := by
    intro n q hq
    obtain ⟨hs, hz, hσq, hs1⟩ := hK q hq
    set w := q.2 + ((N₀ + n : ℕ) : ℂ)
    have hN₀ : R + 1 ≤ (N₀ : ℝ) := by
      simp only [N₀]; push_cast; linarith [Nat.le_ceil R]
    have hw : (n : ℝ) + 1 ≤ w.re := by
      simp only [w, add_re, natCast_re]
      push_cast
      linarith [neg_abs_le q.2.re, abs_re_le_norm q.2]
    have hw0 : 0 < w.re := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have hsM : 0 ≤ q.1.re + (2 * M + 1) := by linarith
    refine (hC q.1 w hs1 hw0 hsM).trans ?_
    have h1 : w.re ^ (-(q.1.re + (2 * M + 1))) ≤ ((n : ℝ) + 1) ^ (-τ) := by
      calc w.re ^ (-(q.1.re + (2 * M + 1))) ≤ ((n : ℝ) + 1) ^ (-(q.1.re + (2 * M + 1))) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hw (by linarith)
        _ ≤ ((n : ℝ) + 1) ^ (-τ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
              (by simp only [τ]; linarith)
    have h2 : Real.exp (π * |q.1.im|) ≤ Real.exp (π * R) := by
      rw [Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left ((abs_im_le_norm _).trans hs) Real.pi_pos.le
    have h3 := r25b_norm_poch_le hR hs (2 * M + 1)
    simp only [u]
    have := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h3 hC0) h1 (by positivity)
      (by positivity)) h2 (by positivity) (by positivity)
    convert this using 1; ring
  exact ⟨u, hu, fun n => by positivity, hbound⟩

/-- **Uniform convergence of the Euler–Maclaurin sequence** on a bounded set of `(s, z)` with
`Re s ≥ σ > -2M` and `s ≠ 1`: the shifted sequence `emSeq M s z (N₀ + N)` converges uniformly. -/
lemma r25b_tendstoUniformlyOn_emSeq {M : ℕ} {K : Set (ℂ × ℂ)} {R σ : ℝ} (hR : 0 ≤ R)
    (hσ : 0 < σ + 2 * M) (hK : ∀ q ∈ K, ‖q.1‖ ≤ R ∧ ‖q.2‖ ≤ R ∧ σ ≤ q.1.re ∧ q.1 ≠ 1) :
    TendstoUniformlyOn (fun N (q : ℂ × ℂ) => r25b_emSeq M q.1 q.2 (⌈R⌉₊ + 1 + N))
      (fun q => r25b_emSeq M q.1 q.2 (⌈R⌉₊ + 1) +
        ∑' n : ℕ, r25b_emD M q.1 (q.2 + (⌈R⌉₊ + 1 + n : ℕ))) atTop K := by
  obtain ⟨u, hu, -, hbound⟩ := r25b_exists_summable_bound_emD hR hσ hK
  set N₀ := ⌈R⌉₊ + 1
  have hT := tendstoUniformlyOn_tsum_nat hu hbound
  rw [Metric.tendstoUniformlyOn_iff] at hT ⊢
  intro ε hε
  filter_upwards [hT ε hε] with N hN q hq
  rw [r25b_emSeq_add M q.1 q.2 N₀ N, dist_add_left]
  exact hN q hq

/-- Pointwise form of `r25b_tendstoUniformlyOn_emSeq`. -/
lemma r25b_tendsto_emSeq_shift {M : ℕ} {s z : ℂ} (hs : s ≠ 1) (hM : 0 < s.re + 2 * M) :
    Tendsto (fun N => r25b_emSeq M s z (⌈max ‖s‖ ‖z‖⌉₊ + 1 + N)) atTop
      (𝓝 (r25b_emSeq M s z (⌈max ‖s‖ ‖z‖⌉₊ + 1) +
        ∑' n : ℕ, r25b_emD M s (z + (⌈max ‖s‖ ‖z‖⌉₊ + 1 + n : ℕ)))) := by
  have hK : ∀ q ∈ ({(s, z)} : Set (ℂ × ℂ)), ‖q.1‖ ≤ max ‖s‖ ‖z‖ ∧ ‖q.2‖ ≤ max ‖s‖ ‖z‖ ∧
      s.re ≤ q.1.re ∧ q.1 ≠ 1 := by
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨le_max_left _ _, le_max_right _ _, le_rfl, hs⟩
  have h := r25b_tendstoUniformlyOn_emSeq (le_max_of_le_left (norm_nonneg _)) hM hK
  have h2 := h.tendsto_at (Set.mem_singleton _)
  exact h2

/-- **Existence of the Euler–Maclaurin limit** with any admissible number `M` of corrections. -/
lemma r25b_tendsto_emSeq {M : ℕ} {s z : ℂ} (hs : s ≠ 1) (hM : 0 < s.re + 2 * M) :
    Tendsto (r25b_emSeq M s z) atTop (𝓝 (limUnder atTop (r25b_emSeq M s z))) := by
  have h := r25b_tendsto_emSeq_shift (z := z) hs hM
  simp_rw [add_comm (⌈max ‖s‖ ‖z‖⌉₊ + 1)] at h
  have h' := (tendsto_add_atTop_iff_nat _).mp h
  exact h'.congr' (Eventually.of_forall fun _ => rfl) |>.trans (le_of_eq (by
    rw [h'.limUnder_eq]))

/-- `(z + N)^w → 0` as `N → ∞`, for `Re w < 0`. -/
lemma r25b_tendsto_cpow_nat (z : ℂ) {w : ℂ} (hw : w.re < 0) :
    Tendsto (fun N : ℕ => (z + N) ^ w) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => ‖z + N‖) atTop atTop := by
    refine tendsto_atTop_mono (fun N => ?_)
      (tendsto_atTop_add_const_right _ (-‖z‖) tendsto_natCast_atTop_atTop)
    have := norm_sub_norm_le (N : ℂ) (-z)
    simp only [Complex.norm_natCast, norm_neg, sub_neg_eq_add] at this
    rw [add_comm z]; linarith
  have h2 : Tendsto (fun N : ℕ => ‖z + N‖ ^ w.re) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := -w.re) (by linarith)).comp h1
    simpa [Function.comp_def] using this
  refine squeeze_zero_norm (fun N => ?_) (by simpa using h2.mul_const (Real.exp (π * |w.im|)))
  refine (norm_cpow_le _ _).trans ?_
  rw [div_eq_mul_inv, ← Real.exp_neg]
  gcongr
  have harg := abs_arg_le_pi (z + N)
  calc -(arg (z + N) * w.im) ≤ |arg (z + N)| * |w.im| := by
        rw [← abs_mul]; exact neg_le_abs _
    _ ≤ π * |w.im| := by gcongr

lemma r25b_emSeq_succ_M (M : ℕ) (s z : ℂ) (N : ℕ) :
    r25b_emSeq (M + 1) s z N =
      r25b_emSeq M s z N + r25b_emC s M * (z + N) ^ (-s - (2 * M + 1)) := by
  simp only [r25b_emSeq, r25b_emF, Finset.sum_range_succ]
  ring

/-- The Euler–Maclaurin limit does not depend on the admissible `M`. -/
lemma r25b_limUnder_emSeq_eq {M₁ M₂ : ℕ} {s z : ℂ} (hs : s ≠ 1) (h₁ : 0 < s.re + 2 * M₁)
    (h₂ : 0 < s.re + 2 * M₂) :
    limUnder atTop (r25b_emSeq M₁ s z) = limUnder atTop (r25b_emSeq M₂ s z) := by
  wlog h : M₁ ≤ M₂ generalizing M₁ M₂
  · exact (this h₂ h₁ (by omega)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => rfl
  | succ d ih =>
    have hd : 0 < s.re + 2 * ((M₁ + d : ℕ) : ℝ) := by
      push_cast; linarith [(d.cast_nonneg : (0 : ℝ) ≤ d)]
    rw [ih hd (by omega)]
    have hT := r25b_tendsto_emSeq (z := z) hs hd
    have hT2 := hT.add ((r25b_tendsto_cpow_nat z (w := -s - (2 * ((M₁ + d : ℕ) : ℂ) + 1))
      (by simp; linarith)).const_mul (r25b_emC s (M₁ + d)))
    rw [mul_zero, add_zero] at hT2
    simp_rw [← r25b_emSeq_succ_M] at hT2
    rw [← add_assoc, hT2.limUnder_eq]

end DLMF.Zeta

namespace DLMF.Confluent

open DLMF.Hypergeometric in
/-- Complex-argument Hurwitz zeta by Euler–Maclaurin continuation; used for 8.15.2 and in
Chapter 25. (Moved here from `DLMF.IncompleteGamma.ZerosIntegrals` on 2026-10-26 so that the
continuation results of this module can refer to it directly.) -/
def hurwitzZetaComplex (s z : ℂ) : ℂ :=
  let M := ⌈(1-s.re)/2⌉₊+1; limUnder atTop (fun N : ℕ => (∑ n ∈ Finset.range N, (z+n)^(-s)) +
    (z+N)^(1-s)/(s-1)+(z+N)^(-s)/2+∑ k ∈ Finset.range M,
      (bernoulli (2*k+2) : ℂ)/(2*k+2).factorial*poch s (2*k+1)*(z+N)^(-s-(2*k+1)))

end DLMF.Confluent

namespace DLMF.Zeta

open DLMF.Hypergeometric (poch poch_succ poch_zero)

/-- The project's `hurwitzZetaComplex` is the Euler–Maclaurin limit for any admissible `M`. -/
lemma s25b_hzc_eq_limUnder {M : ℕ} {s z : ℂ} (hs : s ≠ 1)
    (hM : 0 < s.re + 2 * M) :
    DLMF.Confluent.hurwitzZetaComplex s z = limUnder atTop (r25b_emSeq M s z) := by
  have hdef : DLMF.Confluent.hurwitzZetaComplex s z =
      limUnder atTop (r25b_emSeq (⌈(1 - s.re) / 2⌉₊ + 1) s z) := by
    unfold DLMF.Confluent.hurwitzZetaComplex r25b_emSeq r25b_emF r25b_emC
    simp only []
    congr 1; funext N; ring
  rw [hdef]
  refine r25b_limUnder_emSeq_eq hs ?_ hM
  have := Nat.le_ceil ((1 - s.re) / 2)
  push_cast; linarith

/-- **Existence of the defining limit of `hurwitzZetaComplex`** for `s ≠ 1`, any `z`. -/
lemma s25b_tendsto_hzc {M : ℕ} {s z : ℂ} (hs : s ≠ 1) (hM : 0 < s.re + 2 * M) :
    Tendsto (r25b_emSeq M s z) atTop (𝓝 (DLMF.Confluent.hurwitzZetaComplex s z)) := by
  rw [s25b_hzc_eq_limUnder hs hM]
  exact r25b_tendsto_emSeq hs hM

/-- **Uniform convergence to `hurwitzZetaComplex`** on bounded sets with `Re s ≥ σ > -2M`,
`s ≠ 1`. -/
lemma s25b_tendstoUniformlyOn_hzc {M : ℕ} {K : Set (ℂ × ℂ)} {R σ : ℝ} (hR : 0 ≤ R)
    (hσ : 0 < σ + 2 * M) (hK : ∀ q ∈ K, ‖q.1‖ ≤ R ∧ ‖q.2‖ ≤ R ∧ σ ≤ q.1.re ∧ q.1 ≠ 1) :
    TendstoUniformlyOn (fun N (q : ℂ × ℂ) => r25b_emSeq M q.1 q.2 (⌈R⌉₊ + 1 + N))
      (fun q => DLMF.Confluent.hurwitzZetaComplex q.1 q.2) atTop K := by
  have hU := r25b_tendstoUniformlyOn_emSeq hR hσ hK
  refine hU.congr_right fun q hq => ?_
  obtain ⟨-, -, hσq, hq1⟩ := hK q hq
  have hM : 0 < q.1.re + 2 * M := by linarith
  have h1 := hU.tendsto_at hq
  have hT : Tendsto (fun N : ℕ => ⌈R⌉₊ + 1 + N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_add_left N _) tendsto_id
  have h2 := (s25b_tendsto_hzc (z := q.2) hq1 hM).comp hT
  exact tendsto_nhds_unique h1 h2

lemma r25b_differentiableAt_poch (k : ℕ) (s : ℂ) :
    DifferentiableAt ℂ (fun t => poch t k) s :=
  (ascPochhammer ℂ k).differentiableAt

/-- Each term of the Euler–Maclaurin sequence is holomorphic in `s ≠ 1` when `z + n ≠ 0`. -/
lemma r25b_differentiableAt_emSeq_s (M : ℕ) {s z : ℂ} (hs : s ≠ 1) (N : ℕ)
    (hz : ∀ n : ℕ, z + n ≠ 0) :
    DifferentiableAt ℂ (fun t => r25b_emSeq M t z N) s := by
  unfold r25b_emSeq r25b_emF r25b_emC
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  refine DifferentiableAt.add (DifferentiableAt.fun_sum fun n _ =>
    (differentiableAt_id.neg).const_cpow (Or.inl (hz n))) ?_
  refine DifferentiableAt.add (DifferentiableAt.add ?_ ?_) (DifferentiableAt.fun_sum fun k _ => ?_)
  · exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl (hz N)) |>.div
      (differentiableAt_id.sub (differentiableAt_const _)) hs1
  · exact (differentiableAt_id.neg.const_cpow (Or.inl (hz N))).div_const _
  · exact ((r25b_differentiableAt_poch _ s).const_mul _).mul
      ((differentiableAt_id.neg.sub (differentiableAt_const _)).const_cpow (Or.inl (hz N)))

/-- **Holomorphy of `ζ(s, z)` in `s ≠ 1`** for `z ≠ 0, -1, -2, …`. -/
theorem s25b_differentiableAt_hzc {s₀ z : ℂ} (hs₀ : s₀ ≠ 1)
    (hz : ∀ n : ℕ, z + n ≠ 0) :
    DifferentiableAt ℂ (fun s => DLMF.Confluent.hurwitzZetaComplex s z) s₀ := by
  have hd : 0 < ‖s₀ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs₀)
  set r : ℝ := min (1 / 2) (‖s₀ - 1‖ / 2)
  have hr : 0 < r := lt_min (by norm_num) (by linarith)
  set M : ℕ := ⌈|s₀.re|⌉₊ + 1
  set R : ℝ := max (‖s₀‖ + 1) ‖z‖
  have hR : 0 ≤ R := le_max_of_le_right (norm_nonneg _)
  have hσ : 0 < (s₀.re - 1 / 2) + 2 * M := by
    have := Nat.le_ceil |s₀.re|
    have := neg_abs_le s₀.re
    simp only [M]; push_cast; linarith
  have hK : ∀ q ∈ (Metric.closedBall s₀ r ×ˢ ({z} : Set ℂ)), ‖q.1‖ ≤ R ∧ ‖q.2‖ ≤ R ∧
      s₀.re - 1 / 2 ≤ q.1.re ∧ q.1 ≠ 1 := by
    rintro ⟨s, w⟩ ⟨hs, hw⟩
    simp only [Set.mem_singleton_iff] at hw
    subst hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hs
    have hr1 : r ≤ 1 / 2 := min_le_left _ _
    have hr2 : r ≤ ‖s₀ - 1‖ / 2 := min_le_right _ _
    refine ⟨?_, le_max_right _ _, ?_, ?_⟩
    · calc ‖s‖ = ‖(s - s₀) + s₀‖ := by ring_nf
        _ ≤ ‖s - s₀‖ + ‖s₀‖ := norm_add_le _ _
        _ ≤ R := by simp only [R]; linarith [le_max_left (‖s₀‖ + 1) ‖w‖]
    · have := abs_re_le_norm (s - s₀)
      simp only [sub_re] at this
      linarith [neg_abs_le (s.re - s₀.re)]
    · rintro rfl
      have : ‖s₀ - 1‖ = ‖1 - s₀‖ := norm_sub_rev _ _
      linarith
  have hU := (s25b_tendstoUniformlyOn_hzc hR hσ hK).comp (fun s : ℂ => (s, z))
  have hpre : (fun s : ℂ => (s, z)) ⁻¹' (Metric.closedBall s₀ r ×ˢ ({z} : Set ℂ)) =
      Metric.closedBall s₀ r := by
    ext s; simp
  rw [hpre] at hU
  have hU' := (hU.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn
  have hdiff := hU'.differentiableOn (Eventually.of_forall fun N s hs => ?_) Metric.isOpen_ball
  · exact hdiff.differentiableAt (Metric.ball_mem_nhds _ hr)
  · refine (r25b_differentiableAt_emSeq_s M ?_ _ hz).differentiableWithinAt
    rintro rfl
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hs
    have hr2 : r ≤ ‖s₀ - 1‖ / 2 := min_le_right _ _
    linarith

/-- For `Re s > 1` the Euler–Maclaurin sequence converges to the sum of the series. -/
lemma r25b_tendsto_emSeq_of_hasSum (M : ℕ) {s z L : ℂ} (hs : 1 < s.re)
    (h : HasSum (fun n : ℕ => (z + n) ^ (-s)) L) :
    Tendsto (r25b_emSeq M s z) atTop (𝓝 L) := by
  have h1 : Tendsto (fun N : ℕ => (z + N) ^ (1 - s) / (s - 1)) atTop (𝓝 0) := by
    simpa using (r25b_tendsto_cpow_nat z (w := 1 - s) (by simp; linarith)).div_const (s - 1)
  have h2 : Tendsto (fun N : ℕ => (z + N) ^ (-s) / 2) atTop (𝓝 0) := by
    simpa using (r25b_tendsto_cpow_nat z (w := -s) (by simp; linarith)).div_const 2
  have h3 : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range M,
      r25b_emC s k * (z + N) ^ (-s - (2 * k + 1))) atTop (𝓝 0) := by
    rw [show (0 : ℂ) = ∑ k ∈ Finset.range M, 0 by simp]
    refine tendsto_finsetSum _ fun k _ => ?_
    simpa using (r25b_tendsto_cpow_nat z (w := -s - (2 * k + 1))
      (by simp; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])).const_mul _
  have := h.tendsto_sum_nat.add ((h1.add h2).add h3)
  simp only [add_zero] at this
  exact this

/-- **Bridge to Mathlib's Hurwitz zeta function** for real `0 < x ≤ 1` and `s ≠ 1`
(a proved form of `s25b_hzc_mathlib`). -/
theorem s25b_hzc_mathlib {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) {s : ℂ} (hs : s ≠ 1) :
    DLMF.Confluent.hurwitzZetaComplex s x = HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hx' : ∀ n : ℕ, (x : ℂ) + n ≠ 0 := fun n h => by
    have := congrArg Complex.re h
    simp at this; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hf' : DifferentiableOn ℂ (fun t => DLMF.Confluent.hurwitzZetaComplex t x) {1}ᶜ :=
    fun t ht => (s25b_differentiableAt_hzc ht hx').differentiableWithinAt
  have hg' : DifferentiableOn ℂ (HurwitzZeta.hurwitzZeta (x : UnitAddCircle)) {1}ᶜ :=
    fun t ht => (HurwitzZeta.differentiableAt_hurwitzZeta _ ht).differentiableWithinAt
  have hf := hf'.analyticOnNhd hU
  have hg := hg'.analyticOnNhd hU
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (rank_real_complex ▸ Nat.one_lt_ofNat) _).isPreconnected
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg hpc h2 ?_ hs
  have hopen : IsOpen {t : ℂ | 1 < t.re} := isOpen_lt continuous_const continuous_re
  filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with t ht
  have ht1 : t ≠ 1 := by rintro rfl; simp at ht
  have hsum := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ⟨hx.le, hx1⟩ ht
  have hsum' : HasSum (fun n : ℕ => ((x : ℂ) + n) ^ (-t)) (HurwitzZeta.hurwitzZeta x t) := by
    convert hsum using 2 with n
    rw [cpow_neg, one_div, add_comm]
  have hM : 0 < t.re + 2 * ((0 : ℕ) : ℝ) := by simp; linarith
  exact tendsto_nhds_unique (s25b_tendsto_hzc ht1 hM)
    (r25b_tendsto_emSeq_of_hasSum 0 ht hsum')
end DLMF.Zeta

end
