/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import DLMFMathlib.Analysis.InnerProductSpace.CauchySchwarz
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import ToMathlib.Analysis.Convex.NegativePower
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Inequalities (DLMF §1.7)

The inequalities of Cauchy–Schwarz, Hölder and Minkowski for finite sums (1.7.1–1.7.3) and
for integrals (1.7.4–1.7.6), the inequalities between means (1.7.7) and Jensen's inequality
(1.7.10) are in Mathlib (pointers in `DLMF.AlgebraicAnalytic.Calculus.MathlibCoverage`). This
file states the remaining parts: the equality cases, the converse statements, the reversed
Minkowski inequality for `0 < p < 1`, the power-mean inequalities 1.7.8–1.7.9 and DLMF's form
of Jensen's inequality on an open interval, together with 1.7.11.
The finite Hölder converse uses the normalized dual vector and Mathlib’s conjugate-exponent
and real-power identities, including the zero-vector case. The finite Hölder equality case
uses Mathlib’s equality characterization in Young’s inequality after normalizing each vector.
The integral analogue uses the same normalization and Mathlib’s almost-everywhere equality
criterion for ordered integrable functions.
The finite Minkowski equality case uses strict convexity or strict concavity of real powers
according to the exponent, with zero vectors handled separately. The integral equality proof
applies the corresponding almost-everywhere Jensen criterion; measurability follows from
integrability of the positive powers.
Power-mean order and equality
use strict Jensen and lean-codes' negative-power convexity theorem from
`ToMathlib.Analysis.Convex.NegativePower`.

**Equality cases.** For sums DLMF writes "equality iff `aⱼ = c bⱼ`" (1.7.1, 1.7.3) and
"`aⱼᵖ = c bⱼ^q`" (1.7.2); this misses `b = 0`, `a ≠ 0`, where equality holds. We use the
symmetric form of DLMF's integral statements: `A aⱼ = B bⱼ` with `A`, `B` not both zero.

**1.7.11.** DLMF prints the strict inequality `exp(∫₀¹ ln f) < ∫₀¹ f`, which fails for constant
`f`. We prove `≤` (`exp_integral_log_le_integral`) and state the strict inequality for `f` not
almost everywhere constant.

The means of §1.2(iv) are written out explicitly: `A = (∑ aⱼ)/n`, `G = (∏ aⱼ)^{1/n}`,
`1/H = (∑ 1/aⱼ)/n`, and `M(r) = (∑ pⱼ aⱼ^r)^{1/r}` (weights `pⱼ > 0`, `∑ pⱼ = 1`).
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Finset
open scoped Topology

namespace DLMF.AlgebraicAnalytic

/-! ### §1.7(i) Finite sums -/

/-- DLMF 1.7.1, equality case (corrected): `(∑ aⱼbⱼ)² = (∑ aⱼ²)(∑ bⱼ²)` iff `A aⱼ = B bⱼ` for
all `j`, with constants `A`, `B` not both zero. -/
@[dlmf 1.7.E1]
theorem sq_sum_mul_eq_iff {n : ℕ} (a b : Fin n → ℝ) :
    (∑ j, a j * b j) ^ 2 = (∑ j, a j ^ 2) * (∑ j, b j ^ 2) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ j, A * a j = B * b j := by
  have h := real_inner_sq_eq_iff_smul_eq (WithLp.toLp 2 a) (WithLp.toLp 2 b)
  simp only [PiLp.inner_apply, Real.inner_apply, ← sq] at h
  rw [h]
  refine exists_congr fun A => exists_congr fun B => and_congr_right fun _ => ?_
  rw [WithLp.ext_iff]
  exact funext_iff

/-- DLMF §1.7(i), converse of the Cauchy–Schwarz inequality: if `A, B > 0` and
`(∑ aⱼbⱼ)² ≤ AB` for all `b` with `∑ bⱼ² ≤ B`, then `∑ aⱼ² ≤ A`. -/
@[dlmf 1.7.i]
theorem sum_sq_le_of_forall_sq_sum_mul_le {n : ℕ} (a : Fin n → ℝ) {A B : ℝ} (hA : 0 < A)
    (hB : 0 < B)
    (h : ∀ b : Fin n → ℝ, ∑ j, b j ^ 2 ≤ B → (∑ j, a j * b j) ^ 2 ≤ A * B) :
    ∑ j, a j ^ 2 ≤ A := by
  set S := ∑ j, a j ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg (a j)
  rcases eq_or_lt_of_le hS0 with h0 | hpos
  · rw [← h0]
    exact hA.le
  set t := Real.sqrt (B / S)
  have ht2 : t ^ 2 = B / S := Real.sq_sqrt (div_nonneg hB.le hS0)
  have hb : ∑ j, (t * a j) ^ 2 ≤ B := by
    have : ∑ j, (t * a j) ^ 2 = t ^ 2 * S := by
      rw [hS, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, ht2, div_mul_cancel₀ _ hpos.ne']
  have := h (fun j => t * a j) hb
  have e : (∑ j, a j * (t * a j)) ^ 2 = t ^ 2 * S * S := by
    have : ∑ j, a j * (t * a j) = t * S := by
      rw [hS, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    ring
  rw [e, ht2, div_mul_cancel₀ _ hpos.ne'] at this
  nlinarith

/-- A finite sum of positive real powers of nonnegative terms vanishes exactly when every term
vanishes. -/
private lemma sum_rpow_eq_zero_iff {n : ℕ} {p : ℝ} (hp : 0 < p) (a : Fin n → ℝ)
    (ha : ∀ j, 0 ≤ a j) : (∑ j, a j ^ p) = 0 ↔ ∀ j, a j = 0 := by
  constructor
  · intro h j
    have hj : a j ^ p = 0 := le_antisymm
      (by calc a j ^ p ≤ ∑ i, a i ^ p :=
                 single_le_sum (fun i _ => Real.rpow_nonneg (ha i) _) (mem_univ j)
               _ = 0 := h)
      (Real.rpow_nonneg (ha j) _)
    exact (Real.rpow_eq_zero (ha j) hp.ne').mp hj
  · intro h
    simp [h, Real.zero_rpow hp.ne']

/-- Equality in the normalized finite Young inequality holds exactly when the conjugate powers
agree term by term. -/
private lemma sum_mul_eq_one_iff_of_sum_rpow_eq_one {n : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (u v : Fin n → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (hsu : ∑ j, u j ^ p = 1) (hsv : ∑ j, v j ^ q = 1) :
    ∑ j, u j * v j = 1 ↔ ∀ j, u j ^ p = v j ^ q := by
  have hsum : (∑ j, (u j ^ p / p + v j ^ q / q)) = 1 := by
    rw [sum_add_distrib, ← sum_div, ← sum_div, hsu, hsv]
    simpa only [one_div] using hpq.inv_add_inv_eq_one
  rw [← hsum, sum_eq_sum_iff_of_le (fun j _ =>
    Real.young_inequality_of_nonneg (hu j) (hv j) hpq)]
  simp only [Finset.mem_univ, forall_const]
  exact forall_congr' fun j => Real.young_inequality_eq_iff_of_nonneg (hu j) (hv j) hpq

/-- Dividing a nonzero nonnegative vector by its power-sum norm gives total power mass one. -/
private lemma sum_normalized_rpow {n : ℕ} {p : ℝ} (hp : 0 < p) (a : Fin n → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hS : 0 < ∑ j, a j ^ p) :
    ∑ j, (a j / (∑ i, a i ^ p) ^ (1 / p)) ^ p = 1 := by
  have hpow : ((∑ i, a i ^ p) ^ (1 / p)) ^ p = ∑ i, a i ^ p := by
    simpa only [one_div] using Real.rpow_inv_rpow hS.le hp.ne'
  simp_rw [Real.div_rpow (ha _) (Real.rpow_nonneg hS.le _)]
  rw [← sum_div, hpow, div_self hS.ne']

/-- Two finite vectors of nonzero total mass have equal normalized entries exactly when they
are proportional, allowing arbitrary real proportionality constants. -/
private lemma div_sum_eq_iff_proportional {n : ℕ} (a b : Fin n → ℝ) {S T : ℝ}
    (hS : S ≠ 0) (hT : T ≠ 0) (ha : ∑ j, a j = S) (hb : ∑ j, b j = T) :
    (∀ j, a j / S = b j / T) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ j, A * a j = B * b j := by
  constructor
  · intro h
    exact ⟨T, S, Or.inl hT, fun j => by
      have := (div_eq_div_iff hS hT).mp (h j)
      nlinarith⟩
  · rintro ⟨A, B, hAB, h⟩
    have hs : A * S = B * T := by
      rw [← ha, ← hb, mul_sum, mul_sum]
      exact sum_congr rfl fun j _ => h j
    have hA : A ≠ 0 := by
      intro hz
      have hB : B = 0 := (mul_eq_zero.mp (by simpa [hz] using hs.symm)).resolve_right hT
      exact hAB.elim (fun h => h hz) (fun h => h hB)
    intro j
    apply (div_eq_div_iff hS hT).mpr
    apply (mul_left_cancel₀ hA)
    linear_combination T * h j - b j * hs

/-- DLMF 1.7.2, equality case (corrected): for `p > 1`, `1/p + 1/q = 1` and `aⱼ, bⱼ ≥ 0`,
equality holds in Hölder's inequality iff `A aⱼᵖ = B bⱼ^q` for all `j`, with `A`, `B` not both
zero. -/
@[dlmf 1.7.E2]
theorem inner_eq_Lp_mul_Lq_iff {n : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    ∑ j, a j * b j = (∑ j, a j ^ p) ^ (1 / p) * (∑ j, b j ^ q) ^ (1 / q) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ j, A * a j ^ p = B * b j ^ q := by
  let S := ∑ j, a j ^ p
  let T := ∑ j, b j ^ q
  have hS : 0 ≤ S := sum_nonneg fun j _ => Real.rpow_nonneg (ha j) _
  have hT : 0 ≤ T := sum_nonneg fun j _ => Real.rpow_nonneg (hb j) _
  by_cases hSz : S = 0
  · have haz : ∀ j, a j = 0 := (sum_rpow_eq_zero_iff hpq.pos a ha).mp hSz
    have he : ∑ j, a j * b j = S ^ (1 / p) * T ^ (1 / q) := by
      simp [haz, hSz, Real.zero_rpow (inv_ne_zero hpq.ne_zero)]
    exact iff_of_true he ⟨1, 0, Or.inl one_ne_zero, by simp [haz, Real.zero_rpow hpq.ne_zero]⟩
  by_cases hTz : T = 0
  · have hbz : ∀ j, b j = 0 := (sum_rpow_eq_zero_iff hpq.symm.pos b hb).mp hTz
    have he : ∑ j, a j * b j = S ^ (1 / p) * T ^ (1 / q) := by
      simp [hbz, hTz, Real.zero_rpow (inv_ne_zero hpq.symm.ne_zero)]
    exact iff_of_true he ⟨0, 1, Or.inr one_ne_zero, by simp [hbz, Real.zero_rpow hpq.symm.ne_zero]⟩
  have hSp : 0 < S := hS.lt_of_ne' hSz
  have hTp : 0 < T := hT.lt_of_ne' hTz
  let A := S ^ (1 / p)
  let B := T ^ (1 / q)
  have hA : 0 < A := Real.rpow_pos_of_pos hSp _
  have hB : 0 < B := Real.rpow_pos_of_pos hTp _
  have hAp : A ^ p = S := by
    simpa only [A, one_div] using Real.rpow_inv_rpow hS hpq.ne_zero
  have hBq : B ^ q = T := by
    simpa only [B, one_div] using Real.rpow_inv_rpow hT hpq.symm.ne_zero
  have he : (∑ j, a j / A * (b j / B)) = (∑ j, a j * b j) / (A * B) := by
    rw [sum_div]
    exact sum_congr rfl fun j _ => by ring
  change _ = A * B ↔ _
  rw [← div_eq_one_iff_eq (mul_pos hA hB).ne', ← he,
    sum_mul_eq_one_iff_of_sum_rpow_eq_one hpq _ _ (fun j => div_nonneg (ha j) hA.le)
      (fun j => div_nonneg (hb j) hB.le)
      (sum_normalized_rpow hpq.pos a ha hSp) (sum_normalized_rpow hpq.symm.pos b hb hTp)]
  simp_rw [Real.div_rpow (ha _) hA.le, Real.div_rpow (hb _) hB.le, hAp, hBq]
  exact div_sum_eq_iff_proportional _ _ hSz hTz rfl rfl

/-- DLMF §1.7(i), converse of Hölder's inequality: for `p > 1`, `1/p + 1/q = 1`, `aⱼ ≥ 0` and
`A, B > 0`, if `∑ aⱼbⱼ ≤ A^{1/p} B^{1/q}` for all `bⱼ ≥ 0` with `∑ bⱼ^q ≤ B`, then
`∑ aⱼᵖ ≤ A`. -/
@[dlmf 1.7.i]
theorem sum_rpow_le_of_forall_inner_le {n : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (a : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h : ∀ b : Fin n → ℝ, (∀ j, 0 ≤ b j) → ∑ j, b j ^ q ≤ B →
      ∑ j, a j * b j ≤ A ^ (1 / p) * B ^ (1 / q)) :
    ∑ j, a j ^ p ≤ A := by
  let S := ∑ j, a j ^ p
  have hS : 0 ≤ S := sum_nonneg (fun j _ => Real.rpow_nonneg (ha j) _)
  change S ≤ A
  rcases eq_or_lt_of_le hS with hSz | hSpos
  · simpa [← hSz] using hA.le
  let t := (B / S) ^ (1 / q)
  let b : Fin n → ℝ := fun j => t * a j ^ (p - 1)
  have ht : 0 < t := Real.rpow_pos_of_pos (div_pos hB hSpos) _
  have hb (j) : 0 ≤ b j := mul_nonneg ht.le (Real.rpow_nonneg (ha j) _)
  have htq : t ^ q = B / S := by
    simpa [t, one_div] using Real.rpow_inv_rpow (div_nonneg hB.le hS) hpq.symm.pos.ne'
  have hbq : ∑ j, b j ^ q = B := by
    have he (j : Fin n) : b j ^ q = t ^ q * a j ^ p := by
      dsimp only [b]
      rw [Real.mul_rpow ht.le (Real.rpow_nonneg (ha j) _),
        ← Real.rpow_mul (ha j), hpq.sub_one_mul_conj]
    simp_rw [he]
    rw [← mul_sum, htq]
    change B / S * S = B
    exact div_mul_cancel₀ _ hSpos.ne'
  have hab : ∑ j, a j * b j = t * S := by
    rw [show (∑ j, a j * b j) = ∑ j, t * a j ^ p from sum_congr rfl (fun j _ => by
      dsimp [b]
      have he := Real.rpow_add_one' (ha j) (show p - 1 + 1 ≠ 0 by simpa using hpq.pos.ne')
      rw [show p - 1 + 1 = p by ring] at he
      rw [he]
      ring), ← mul_sum]
  have hbound := h b hb hbq.le
  rw [hab] at hbound
  have hSS : S = S ^ (1 / p) * S ^ (1 / q) := by
    rw [← Real.rpow_add hSpos, show 1 / p + 1 / q = 1 by
      simpa only [one_div] using hpq.inv_add_inv_eq_one, Real.rpow_one]
  have htS : t * S = B ^ (1 / q) * S ^ (1 / p) := by
    change (B / S) ^ (1 / q) * S = _
    rw [Real.div_rpow hB.le hS]
    calc
      _ = (B ^ (1 / q) / S ^ (1 / q)) * (S ^ (1 / p) * S ^ (1 / q)) :=
        congrArg (fun v => (B ^ (1 / q) / S ^ (1 / q)) * v) hSS
      _ = _ := by field_simp
  rw [htS] at hbound
  have hnorm : S ^ (1 / p) ≤ A ^ (1 / p) :=
    (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hB (1 / q))).mp (by simpa [mul_comm] using hbound)
  exact (Real.rpow_le_rpow_iff hS hA.le (one_div_pos.mpr hpq.pos)).mp hnorm

/-- DLMF 1.7.3, reversed Minkowski inequality: for `0 < p < 1` and `aⱼ, bⱼ ≥ 0`,
`(∑ (aⱼ + bⱼ)ᵖ)^{1/p} ≥ (∑ aⱼᵖ)^{1/p} + (∑ bⱼᵖ)^{1/p}`. -/
@[dlmf 1.7.E3]
theorem Lp_add_ge_of_lt_one {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (a b : Fin n → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    (∑ j, a j ^ p) ^ (1 / p) + (∑ j, b j ^ p) ^ (1 / p) ≤
      (∑ j, (a j + b j) ^ p) ^ (1 / p) := by
  let S : ℝ := ∑ j, a j ^ p
  let T : ℝ := ∑ j, b j ^ p
  have hS : 0 ≤ S := sum_nonneg fun j _ => Real.rpow_nonneg (ha j) _
  have hT : 0 ≤ T := sum_nonneg fun j _ => Real.rpow_nonneg (hb j) _
  let A := S ^ (1 / p)
  let B := T ^ (1 / p)
  have hA : 0 ≤ A := Real.rpow_nonneg hS _
  have hB : 0 ≤ B := Real.rpow_nonneg hT _
  have hAp : A ^ p = S := by simp [A, one_div, Real.rpow_inv_rpow hS hp0.ne']
  have hBp : B ^ p = T := by simp [B, one_div, Real.rpow_inv_rpow hT hp0.ne']
  by_cases hAz : A = 0
  · have hS0 : S = 0 := by rw [← hAp, hAz, Real.zero_rpow hp0.ne']
    have ha0 : ∀ j, a j = 0 := (sum_rpow_eq_zero_iff hp0 a ha).mp hS0
    simp [ha0, Real.zero_rpow hp0.ne', Real.zero_rpow (inv_ne_zero hp0.ne')]
  by_cases hBz : B = 0
  · have hT0 : T = 0 := by rw [← hBp, hBz, Real.zero_rpow hp0.ne']
    have hb0 : ∀ j, b j = 0 := (sum_rpow_eq_zero_iff hp0 b hb).mp hT0
    simp [hb0, Real.zero_rpow hp0.ne', Real.zero_rpow (inv_ne_zero hp0.ne')]
  have hAp0 : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  have hBp0 : 0 < B := lt_of_le_of_ne hB (Ne.symm hBz)
  have hsum : 0 < A + B := add_pos hAp0 hBp0
  have hpoint (j : Fin n) :
      A / (A + B) * (a j / A) ^ p + B / (A + B) * (b j / B) ^ p ≤
        ((a j + b j) / (A + B)) ^ p := by
    have h := (Real.concaveOn_rpow hp0.le hp1.le).2
      (show a j / A ∈ Set.Ici 0 from div_nonneg (ha j) hA)
      (show b j / B ∈ Set.Ici 0 from div_nonneg (hb j) hB)
      (show 0 ≤ A / (A + B) from div_nonneg hA hsum.le)
      (show 0 ≤ B / (A + B) from div_nonneg hB hsum.le)
      (show A / (A + B) + B / (A + B) = 1 from by field_simp)
    simp only [smul_eq_mul] at h
    convert h using 1
    congr 1
    field_simp
  have hs := sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin n))) => hpoint j
  have hleft : (∑ j, (A / (A + B) * (a j / A) ^ p + B / (A + B) * (b j / B) ^ p)) = 1 := by
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have hsa : (∑ j, (a j / A) ^ p) = 1 := by
      have he : (∑ j, (a j / A) ^ p) = S / A ^ p := by
        dsimp only [S]
        rw [sum_div]
        exact sum_congr rfl fun j _ => Real.div_rpow (ha j) hA p
      rw [he]
      have hpS : S ≠ 0 := by rw [← hAp]; exact (Real.rpow_pos_of_pos hAp0 _).ne'
      rw [hAp, div_self hpS]
    have hsb : (∑ j, (b j / B) ^ p) = 1 := by
      have he : (∑ j, (b j / B) ^ p) = T / B ^ p := by
        dsimp only [T]
        rw [sum_div]
        exact sum_congr rfl fun j _ => Real.div_rpow (hb j) hB p
      rw [he]
      have hpT : T ≠ 0 := by rw [← hBp]; exact (Real.rpow_pos_of_pos hBp0 _).ne'
      rw [hBp, div_self hpT]
    rw [hsa, hsb]
    field_simp
  rw [hleft] at hs
  have hright : (∑ j, ((a j + b j) / (A + B)) ^ p) =
      (∑ j, (a j + b j) ^ p) / (A + B) ^ p := by
    simp_rw [Real.div_rpow (add_nonneg (ha _) (hb _)) hsum.le, sum_div]
  rw [hright, one_le_div (Real.rpow_pos_of_pos hsum _)] at hs
  have := Real.rpow_le_rpow (Real.rpow_nonneg hsum.le _) hs (inv_nonneg.mpr hp0.le)
  rw [Real.rpow_rpow_inv hsum.le hp0.ne'] at this
  simpa [A, B, S, T, one_div] using this

/-- For a strictly convex or strictly concave function, equality in a fixed positive
weighted finite Jensen sum forces the two vectors to agree at every index. -/
private lemma sum_strict_jensen_eq_iff {n : ℕ} {F : ℝ → ℝ}
    (hF : StrictConvexOn ℝ (Ici 0) F ∨ StrictConcaveOn ℝ (Ici 0) F)
    (u v : Fin n → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hts : t + s = 1) :
    (∑ j, F (t * u j + s * v j)) = t * (∑ j, F (u j)) + s * (∑ j, F (v j)) ↔
      ∀ j, u j = v j := by
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  rcases hF with hF | hF
  · have hle (j) : F (t * u j + s * v j) ≤ t * F (u j) + s * F (v j) := by
      simpa only [smul_eq_mul] using hF.convexOn.2 (hu j) (hv j) ht.le hs.le hts
    rw [sum_eq_sum_iff_of_le (fun j _ => hle j)]
    simp only [Finset.mem_univ, forall_const]
    refine forall_congr' fun j => ⟨fun he => ?_, fun he => ?_⟩
    · by_contra hne
      have hlt := hF.2 (hu j) (hv j) hne ht hs hts
      simp only [smul_eq_mul] at hlt
      exact (ne_of_lt hlt) he
    · rw [he, ← add_mul, hts, one_mul, ← add_mul, hts, one_mul]
  · have hle (j) : t * F (u j) + s * F (v j) ≤ F (t * u j + s * v j) := by
      simpa only [smul_eq_mul] using hF.concaveOn.2 (hu j) (hv j) ht.le hs.le hts
    rw [eq_comm, sum_eq_sum_iff_of_le (fun j _ => hle j)]
    simp only [Finset.mem_univ, forall_const]
    refine forall_congr' fun j => ⟨fun he => ?_, fun he => ?_⟩
    · by_contra hne
      have hlt := hF.2 (hu j) (hv j) hne ht hs hts
      simp only [smul_eq_mul] at hlt
      exact (ne_of_lt hlt) he
    · rw [he, ← add_mul, hts, one_mul, ← add_mul, hts, one_mul]

/-- Equality between the power-sum norm of a sum and the sum of two positive normalizing
factors is equivalent to equality of the normalized vectors. -/
private lemma sum_rpow_add_eq_iff_normalized_eq {n : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p ≠ 1)
    (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hsa : ∑ j, (a j / A) ^ p = 1) (hsb : ∑ j, (b j / B) ^ p = 1) :
    (∑ j, (a j + b j) ^ p) ^ (1 / p) = A + B ↔ ∀ j, a j / A = b j / B := by
  have hC : 0 < A + B := add_pos hA hB
  have hweights : A / (A + B) + B / (A + B) = 1 := by field_simp
  have hF : StrictConvexOn ℝ (Ici 0) (fun x : ℝ => x ^ p) ∨
      StrictConcaveOn ℝ (Ici 0) (fun x : ℝ => x ^ p) := by
    rcases lt_or_gt_of_ne hp1 with hlt | hgt
    · exact Or.inr (Real.strictConcaveOn_rpow hp hlt)
    · exact Or.inl (strictConvexOn_rpow hgt)
  have hj := sum_strict_jensen_eq_iff hF (fun j => a j / A) (fun j => b j / B)
    (fun j => div_nonneg (ha j) hA.le) (fun j => div_nonneg (hb j) hB.le)
    (div_pos hA hC) (div_pos hB hC) hweights
  have hpoint (j) : A / (A + B) * (a j / A) + B / (A + B) * (b j / B) =
      (a j + b j) / (A + B) := by field_simp
  simp_rw [hpoint] at hj
  rw [hsa, hsb, mul_one, mul_one, hweights] at hj
  rw [← hj]
  simp_rw [Real.div_rpow (add_nonneg (ha _) (hb _)) hC.le]
  rw [← sum_div, div_eq_one_iff_eq (Real.rpow_pos_of_pos hC _).ne']
  simpa only [one_div] using Real.rpow_inv_eq
    (sum_nonneg fun j _ => Real.rpow_nonneg (add_nonneg (ha j) (hb j)) _) hC.le hp.ne'

/-- Two nonzero nonnegative vectors have the same power-norm normalization exactly when
they are proportional by real constants. -/
private lemma normalized_rpow_sum_eq_iff_proportional {n : ℕ} {p : ℝ} (hp : 0 < p)
    (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hAp : A ^ p = ∑ j, a j ^ p) (hBp : B ^ p = ∑ j, b j ^ p) :
    (∀ j, a j / A = b j / B) ↔
      ∃ C D : ℝ, (C ≠ 0 ∨ D ≠ 0) ∧ ∀ j, C * a j = D * b j := by
  constructor
  · intro h
    refine ⟨B, A, Or.inl hB.ne', fun j => ?_⟩
    have := (div_eq_div_iff hA.ne' hB.ne').mp (h j)
    nlinarith
  · rintro ⟨C, D, hCD, h⟩
    have hpow : ∀ j, |C| ^ p * a j ^ p = |D| ^ p * b j ^ p := by
      intro j
      rw [← Real.mul_rpow (abs_nonneg _) (ha j), ← Real.mul_rpow (abs_nonneg _) (hb j)]
      have he := congrArg abs (h j)
      simp only [abs_mul, abs_of_nonneg (ha j), abs_of_nonneg (hb j)] at he
      rw [he]
    have hCDp : |C| ^ p ≠ 0 ∨ |D| ^ p ≠ 0 := hCD.imp
      (fun h => (Real.rpow_pos_of_pos (abs_pos.mpr h) _).ne')
      (fun h => (Real.rpow_pos_of_pos (abs_pos.mpr h) _).ne')
    have hs : (∑ j, a j ^ p) ≠ 0 := hAp ▸ (Real.rpow_pos_of_pos hA _).ne'
    have ht : (∑ j, b j ^ p) ≠ 0 := hBp ▸ (Real.rpow_pos_of_pos hB _).ne'
    have hr := (div_sum_eq_iff_proportional (fun j => a j ^ p) (fun j => b j ^ p)
      hs ht rfl rfl).mpr ⟨|C| ^ p, |D| ^ p, hCDp, hpow⟩
    intro j
    apply (Real.rpow_left_inj (div_nonneg (ha j) hA.le) (div_nonneg (hb j) hB.le) hp.ne').mp
    simpa only [Real.div_rpow (ha j) hA.le, Real.div_rpow (hb j) hB.le, hAp, hBp] using hr j

/-- DLMF 1.7.3, equality case (corrected): for `p > 0`, `p ≠ 1` and `aⱼ, bⱼ ≥ 0`, equality holds
in Minkowski's inequality iff `A aⱼ = B bⱼ` for all `j`, with `A`, `B` not both zero. -/
@[dlmf 1.7.E3]
theorem Lp_add_eq_iff {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≠ 1) (a b : Fin n → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    (∑ j, (a j + b j) ^ p) ^ (1 / p) = (∑ j, a j ^ p) ^ (1 / p) + (∑ j, b j ^ p) ^ (1 / p) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ j, A * a j = B * b j := by
  let S := ∑ j, a j ^ p
  let T := ∑ j, b j ^ p
  have hS : 0 ≤ S := sum_nonneg fun j _ => Real.rpow_nonneg (ha j) _
  have hT : 0 ≤ T := sum_nonneg fun j _ => Real.rpow_nonneg (hb j) _
  by_cases hSz : S = 0
  · have haz : ∀ j, a j = 0 := (sum_rpow_eq_zero_iff hp0 a ha).mp hSz
    have he : (∑ j, (a j + b j) ^ p) ^ (1 / p) = S ^ (1 / p) + T ^ (1 / p) := by
      simp [haz, hSz, T, Real.zero_rpow (inv_ne_zero hp0.ne')]
    exact iff_of_true he ⟨1, 0, Or.inl one_ne_zero, by simp [haz]⟩
  by_cases hTz : T = 0
  · have hbz : ∀ j, b j = 0 := (sum_rpow_eq_zero_iff hp0 b hb).mp hTz
    have he : (∑ j, (a j + b j) ^ p) ^ (1 / p) = S ^ (1 / p) + T ^ (1 / p) := by
      simp [hbz, hTz, S, Real.zero_rpow (inv_ne_zero hp0.ne')]
    exact iff_of_true he ⟨0, 1, Or.inr one_ne_zero, by simp [hbz]⟩
  have hSp : 0 < S := hS.lt_of_ne' hSz
  have hTp : 0 < T := hT.lt_of_ne' hTz
  let A := S ^ (1 / p)
  let B := T ^ (1 / p)
  have hA : 0 < A := Real.rpow_pos_of_pos hSp _
  have hB : 0 < B := Real.rpow_pos_of_pos hTp _
  have hAp : A ^ p = S := by
    simpa only [A, one_div] using Real.rpow_inv_rpow hS hp0.ne'
  have hBp : B ^ p = T := by
    simpa only [B, one_div] using Real.rpow_inv_rpow hT hp0.ne'
  exact (sum_rpow_add_eq_iff_normalized_eq hp0 hp1 a b ha hb hA hB (sum_normalized_rpow hp0 a ha hSp)
    (sum_normalized_rpow hp0 b hb hTp)).trans (normalized_rpow_sum_eq_iff_proportional hp0 a b ha hb hA hB hAp hBp)

/-! ### §1.7(ii) Integrals -/

/-- DLMF 1.7.4 (Cauchy–Schwarz inequality for integrals): for `f`, `g` square integrable on
`(a, b)` (possibly infinite), `(∫ fg)² ≤ ∫ f² ∫ g²`. -/
@[dlmf 1.7.E4]
theorem sq_integral_mul_le {f g : ℝ → ℝ} {s : Set ℝ} (hf : MemLp f 2 (volume.restrict s))
    (hg : MemLp g 2 (volume.restrict s)) :
    (∫ x in s, f x * g x) ^ 2 ≤ (∫ x in s, f x ^ 2) * ∫ x in s, g x ^ 2 := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hf' : MemLp (fun x => |f x|) (ENNReal.ofReal 2) (volume.restrict s) := by
    rw [ENNReal.ofReal_ofNat]; exact hf.abs
  have hg' : MemLp (fun x => |g x|) (ENNReal.ofReal 2) (volume.restrict s) := by
    rw [ENNReal.ofReal_ofNat]; exact hg.abs
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall fun x => abs_nonneg (f x))
    (Eventually.of_forall fun x => abs_nonneg (g x)) hf' hg'
  simp only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] at h
  have hA : 0 ≤ ∫ x in s, f x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ ∫ x in s, g x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have habs : |∫ x in s, f x * g x| ≤ ∫ x in s, |f x| * |g x| := by
    simpa [abs_mul] using abs_integral_le_integral_abs (f := fun x => f x * g x)
      (μ := volume.restrict s)
  have h2 := habs.trans h
  calc (∫ x in s, f x * g x) ^ 2 = |∫ x in s, f x * g x| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt (∫ x in s, f x ^ 2) * Real.sqrt (∫ x in s, g x ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h2 2
    _ = (∫ x in s, f x ^ 2) * ∫ x in s, g x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]

/-- DLMF 1.7.4, equality case: equality holds iff `A f = B g` almost everywhere, with `A`, `B`
not both zero (DLMF: "for all `x`"). -/
@[dlmf 1.7.E4]
theorem sq_integral_mul_eq_iff {f g : ℝ → ℝ} {s : Set ℝ} (hf : MemLp f 2 (volume.restrict s))
    (hg : MemLp g 2 (volume.restrict s)) :
    (∫ x in s, f x * g x) ^ 2 = (∫ x in s, f x ^ 2) * (∫ x in s, g x ^ 2) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ᵐ x ∂(volume.restrict s), A * f x = B * g x := by
  have h := real_inner_sq_eq_iff_smul_eq (hf.toLp f) (hg.toLp g)
  rw [hf.real_inner_toLp hg, hf.real_inner_toLp hf, hg.real_inner_toLp hg] at h
  simp only [← sq] at h
  rw [h]
  refine exists_congr fun A => exists_congr fun B => and_congr_right fun _ => ?_
  rw [Lp.ext_iff]
  have he := (Lp.coeFn_smul A (hf.toLp f)).trans (hf.coeFn_toLp.const_smul A)
  have he' := (Lp.coeFn_smul B (hg.toLp g)).trans (hg.coeFn_toLp.const_smul B)
  exact eventually_congr ((he.and he').mono fun x hx => by
    simp only [hx.1, hx.2, Pi.smul_apply, smul_eq_mul])

/-- Equality in the normalized integral Young inequality is equivalent to equality of the
conjugate powers almost everywhere. -/
private lemma integral_mul_eq_one_iff_of_integral_rpow_eq_one {f g : ℝ → ℝ} {μ : Measure ℝ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : Integrable (fun x => f x ^ p) μ) (hg : Integrable (fun x => g x ^ q) μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hsf : ∫ x, f x ^ p ∂μ = 1) (hsg : ∫ x, g x ^ q ∂μ = 1) :
    (∫ x, f x * g x ∂μ) = 1 ↔ ∀ᵐ x ∂μ, f x ^ p = g x ^ q := by
  have hsum : (∫ x, f x ^ p / p + g x ^ q / q ∂μ) = 1 := by
    rw [integral_add (hf.div_const _) (hg.div_const _), integral_div, integral_div, hsf, hsg]
    simpa only [one_div] using hpq.inv_add_inv_eq_one
  rw [← hsum, integral_eq_iff_of_ae_le (g := fun x => f x ^ p / p + g x ^ q / q) hfg ((hf.div_const _).add (hg.div_const _))
    (Eventually.of_forall fun x => Real.young_inequality_of_nonneg (hf0 x) (hg0 x) hpq)]
  exact eventually_congr (Eventually.of_forall fun x =>
    Real.young_inequality_eq_iff_of_nonneg (hf0 x) (hg0 x) hpq)

/-- Two integrands with nonzero integrals have equal normalized values almost everywhere
exactly when they are proportional by real constants. -/
private lemma div_integral_eq_iff_proportional {f g : ℝ → ℝ} {μ : Measure ℝ} {S T : ℝ}
    (hS : S ≠ 0) (hT : T ≠ 0)
    (hsf : ∫ x, f x ∂μ = S) (hsg : ∫ x, g x ∂μ = T) :
    (∀ᵐ x ∂μ, f x / S = g x / T) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ᵐ x ∂μ, A * f x = B * g x := by
  constructor
  · intro h
    exact ⟨T, S, Or.inl hT, h.mono fun x hx => by
      have := (div_eq_div_iff hS hT).mp hx
      nlinarith⟩
  · rintro ⟨A, B, hAB, h⟩
    have hs : A * S = B * T := by
      rw [← hsf, ← hsg, ← integral_const_mul, ← integral_const_mul]
      exact integral_congr_ae h
    have hA : A ≠ 0 := by
      intro hz
      have hB : B = 0 := (mul_eq_zero.mp (by simpa [hz] using hs.symm)).resolve_right hT
      exact hAB.elim (fun h => h hz) (fun h => h hB)
    filter_upwards [h] with x hx
    apply (div_eq_div_iff hS hT).mpr
    apply mul_left_cancel₀ hA
    linear_combination T * hx - g x * hs

/-- Normalizing a nonnegative function by its nonzero power-integral norm gives power
integral one. -/
private lemma integral_normalized_rpow {f : ℝ → ℝ} {μ : Measure ℝ} {p : ℝ} (hp : 0 < p)
    (hf0 : ∀ x, 0 ≤ f x) (hS : 0 < ∫ x, f x ^ p ∂μ) :
    ∫ x, (f x / (∫ y, f y ^ p ∂μ) ^ (1 / p)) ^ p ∂μ = 1 := by
  simp_rw [Real.div_rpow (hf0 _) (Real.rpow_nonneg hS.le _)]
  rw [integral_div, show ((∫ y, f y ^ p ∂μ) ^ (1 / p)) ^ p = (∫ y, f y ^ p ∂μ) from by
    simpa only [one_div] using Real.rpow_inv_rpow hS.le hp.ne', div_self hS.ne']

/-- The positive real power of a nonnegative function in the corresponding Lebesgue space
is integrable. -/
private lemma integrable_rpow_of_nonneg_memLp {f : ℝ → ℝ} {μ : Measure ℝ} {p : ℝ} (hp : 0 < p)
    (hf0 : ∀ x, 0 ≤ f x) (hf : MemLp f (ENNReal.ofReal p) μ) :
    Integrable (fun x => f x ^ p) μ := by
  simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_of_nonneg (hf0 _)] using
    hf.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top

/-- A nonnegative function with zero integral of a positive power vanishes almost everywhere. -/
private lemma ae_eq_zero_of_integral_rpow_eq_zero {f : ℝ → ℝ} {μ : Measure ℝ} {p : ℝ} (hp : 0 < p)
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable (fun x => f x ^ p) μ)
    (h : ∫ x, f x ^ p ∂μ = 0) : f =ᵐ[μ] 0 := by
  have hz := (integral_eq_zero_iff_of_nonneg (fun x => Real.rpow_nonneg (hf0 x) _) hf).mp h
  exact hz.mono fun x hx => (Real.rpow_eq_zero (hf0 x) hp.ne').mp hx

/-- DLMF 1.7.5, equality case: for `p > 1`, `1/p + 1/q = 1` and `f, g ≥ 0` with `fᵖ`, `g^q`
integrable, equality holds in Hölder's inequality iff `A fᵖ = B g^q` almost everywhere, with
`A`, `B` not both zero. -/
@[dlmf 1.7.E5]
theorem integral_mul_eq_Lp_mul_Lq_iff {f g : ℝ → ℝ} {s : Set ℝ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict s))
    (hg : MemLp g (ENNReal.ofReal q) (volume.restrict s)) :
    ∫ x in s, f x * g x =
        (∫ x in s, f x ^ p) ^ (1 / p) * (∫ x in s, g x ^ q) ^ (1 / q) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ᵐ x ∂(volume.restrict s), A * f x ^ p = B * g x ^ q := by
  let μ := volume.restrict s
  have hfp := integrable_rpow_of_nonneg_memLp hpq.pos hf0 hf
  have hgq := integrable_rpow_of_nonneg_memLp hpq.symm.pos hg0 hg
  let : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q) := hpq.ennrealOfReal
  have hfg : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  let S := ∫ x, f x ^ p ∂μ
  let T := ∫ x, g x ^ q ∂μ
  have hS : 0 ≤ S := integral_nonneg fun x => Real.rpow_nonneg (hf0 x) _
  have hT : 0 ≤ T := integral_nonneg fun x => Real.rpow_nonneg (hg0 x) _
  by_cases hSz : S = 0
  · have hfz := ae_eq_zero_of_integral_rpow_eq_zero hpq.pos hf0 hfp hSz
    have he : (∫ x, f x * g x ∂μ) = S ^ (1 / p) * T ^ (1 / q) := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (hfz.mono fun x hx => by simp [hx])]
      simp [hSz, Real.zero_rpow (inv_ne_zero hpq.ne_zero)]
    exact iff_of_true he ⟨1, 0, Or.inl one_ne_zero,
      hfz.mono fun x hx => by simp [hx, Real.zero_rpow hpq.ne_zero]⟩
  by_cases hTz : T = 0
  · have hgz := ae_eq_zero_of_integral_rpow_eq_zero hpq.symm.pos hg0 hgq hTz
    have he : (∫ x, f x * g x ∂μ) = S ^ (1 / p) * T ^ (1 / q) := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (hgz.mono fun x hx => by simp [hx])]
      simp [hTz, Real.zero_rpow (inv_ne_zero hpq.symm.ne_zero)]
    exact iff_of_true he ⟨0, 1, Or.inr one_ne_zero,
      hgz.mono fun x hx => by simp [hx, Real.zero_rpow hpq.symm.ne_zero]⟩
  have hSp : 0 < S := hS.lt_of_ne' hSz
  have hTp : 0 < T := hT.lt_of_ne' hTz
  let A := S ^ (1 / p)
  let B := T ^ (1 / q)
  have hA : 0 < A := Real.rpow_pos_of_pos hSp _
  have hB : 0 < B := Real.rpow_pos_of_pos hTp _
  have hAp : A ^ p = S := by
    simpa only [A, one_div] using Real.rpow_inv_rpow hS hpq.ne_zero
  have hBq : B ^ q = T := by
    simpa only [B, one_div] using Real.rpow_inv_rpow hT hpq.symm.ne_zero
  have hfn : Integrable (fun x => (f x / A) ^ p) μ := by
    simpa only [Real.div_rpow (hf0 _) hA.le] using hfp.div_const (A ^ p)
  have hgn : Integrable (fun x => (g x / B) ^ q) μ := by
    simpa only [Real.div_rpow (hg0 _) hB.le] using hgq.div_const (B ^ q)
  have he : (fun x => f x / A * (g x / B)) = fun x => f x * g x / (A * B) := by
    funext x; ring
  have hnorm := integral_mul_eq_one_iff_of_integral_rpow_eq_one hpq (fun x => div_nonneg (hf0 x) hA.le)
    (fun x => div_nonneg (hg0 x) hB.le) hfn hgn
    (by rw [he]; exact hfg.div_const _)
    (integral_normalized_rpow hpq.pos hf0 hSp) (integral_normalized_rpow hpq.symm.pos hg0 hTp)
  rw [he, integral_div, div_eq_one_iff_eq (mul_pos hA hB).ne'] at hnorm
  change _ = A * B ↔ _
  rw [hnorm]
  simp_rw [Real.div_rpow (hf0 _) hA.le, Real.div_rpow (hg0 _) hB.le, hAp, hBq]
  exact div_integral_eq_iff_proportional hSz hTz rfl rfl

/-- DLMF 1.7.6 (Minkowski's inequality for integrals, real form): for `p > 1` and `f, g ≥ 0`
in `Lᵖ(a, b)`, `(∫ (f + g)ᵖ)^{1/p} ≤ (∫ fᵖ)^{1/p} + (∫ gᵖ)^{1/p}`. -/
@[dlmf 1.7.E6]
theorem integral_add_rpow_le {f g : ℝ → ℝ} {s : Set ℝ} {p : ℝ} (hp : 1 < p)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict s))
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict s)) :
    (∫ x in s, (f x + g x) ^ p) ^ (1 / p) ≤
      (∫ x in s, f x ^ p) ^ (1 / p) + (∫ x in s, g x ^ p) ^ (1 / p) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  have h := eLpNorm_add_le (f := f) (g := g) (μ := volume.restrict s) hp1
  rw [(hf.add hg).eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top,
    hf.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top,
    hg.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top,
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at h
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  simp only [ENNReal.toReal_ofReal (by linarith : 0 ≤ p), Pi.add_apply] at hr
  simp_rw [Real.norm_of_nonneg (hf0 _), Real.norm_of_nonneg (hg0 _),
    Real.norm_of_nonneg (add_nonneg (hf0 _) (hg0 _))] at hr
  simpa only [one_div] using hr

/-- Nonnegative functions with integrable `p`th powers have an integrable sum to the `p`th
power for `0 < p ≤ 1`. -/
private lemma integrable_add_rpow_of_integrable_rpow {f g : ℝ → ℝ} {μ : Measure ℝ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : Integrable (fun x => f x ^ p) μ) (hg : Integrable (fun x => g x ^ p) μ) :
    Integrable (fun x => (f x + g x) ^ p) μ := by
  have hfm : AEStronglyMeasurable f μ := by
    have h := (Real.continuous_rpow_const (inv_nonneg.mpr hp0.le)).comp_aestronglyMeasurable
      hf.aestronglyMeasurable
    apply h.congr
    exact Eventually.of_forall fun x => Real.rpow_rpow_inv (hf0 x) hp0.ne'
  have hgm : AEStronglyMeasurable g μ := by
    have h := (Real.continuous_rpow_const (inv_nonneg.mpr hp0.le)).comp_aestronglyMeasurable
      hg.aestronglyMeasurable
    apply h.congr
    exact Eventually.of_forall fun x => Real.rpow_rpow_inv (hg0 x) hp0.ne'
  apply (hf.add hg).mono'
  · exact (Real.continuous_rpow_const hp0.le).comp_aestronglyMeasurable (hfm.add hgm)
  · exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (add_nonneg (hf0 x) (hg0 x)) _)]
      exact Real.rpow_add_le_add_rpow (hf0 x) (hg0 x) hp0.le hp1

/-- DLMF 1.7.6, reversed for `0 < p < 1`: for `f, g ≥ 0` with `fᵖ`, `gᵖ` integrable,
`(∫ (f + g)ᵖ)^{1/p} ≥ (∫ fᵖ)^{1/p} + (∫ gᵖ)^{1/p}`. -/
@[dlmf 1.7.E6]
theorem integral_add_rpow_ge_of_lt_one {f g : ℝ → ℝ} {s : Set ℝ} {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : IntegrableOn (fun x => f x ^ p) s) (hg : IntegrableOn (fun x => g x ^ p) s) :
    (∫ x in s, f x ^ p) ^ (1 / p) + (∫ x in s, g x ^ p) ^ (1 / p) ≤
      (∫ x in s, (f x + g x) ^ p) ^ (1 / p) := by
  let μ := volume.restrict s
  have hsum := integrable_add_rpow_of_integrable_rpow hp0 hp1.le hf0 hg0 hf hg
  let S := ∫ x, f x ^ p ∂μ
  let T := ∫ x, g x ^ p ∂μ
  have hS : 0 ≤ S := integral_nonneg fun x => Real.rpow_nonneg (hf0 x) _
  have hT : 0 ≤ T := integral_nonneg fun x => Real.rpow_nonneg (hg0 x) _
  let A := S ^ (1 / p)
  let B := T ^ (1 / p)
  have hA : 0 ≤ A := Real.rpow_nonneg hS _
  have hB : 0 ≤ B := Real.rpow_nonneg hT _
  have hAp : A ^ p = S := by simp [A, one_div, Real.rpow_inv_rpow hS hp0.ne']
  have hBp : B ^ p = T := by simp [B, one_div, Real.rpow_inv_rpow hT hp0.ne']
  by_cases hAz : A = 0
  · have hS0 : S = 0 := by rw [← hAp, hAz, Real.zero_rpow hp0.ne']
    have ha0 : ∀ᵐ x ∂μ, f x = 0 := by
      have h := (integral_eq_zero_iff_of_nonneg (fun x => Real.rpow_nonneg (hf0 x) _) hf).mp hS0
      filter_upwards [h] with x hx
      exact (Real.rpow_eq_zero (hf0 x) hp0.ne').mp hx
    have he : (∫ x, (f x + g x) ^ p ∂μ) = ∫ x, g x ^ p ∂μ := by
      apply integral_congr_ae
      filter_upwards [ha0] with x hx
      simp [hx]
    change A + B ≤ (∫ x, (f x + g x) ^ p ∂μ) ^ (1 / p)
    simp [hAz, B, T, he]
  by_cases hBz : B = 0
  · have hT0 : T = 0 := by rw [← hBp, hBz, Real.zero_rpow hp0.ne']
    have hb0 : ∀ᵐ x ∂μ, g x = 0 := by
      have h := (integral_eq_zero_iff_of_nonneg (fun x => Real.rpow_nonneg (hg0 x) _) hg).mp hT0
      filter_upwards [h] with x hx
      exact (Real.rpow_eq_zero (hg0 x) hp0.ne').mp hx
    have he : (∫ x, (f x + g x) ^ p ∂μ) = ∫ x, f x ^ p ∂μ := by
      apply integral_congr_ae
      filter_upwards [hb0] with x hx
      simp [hx]
    change A + B ≤ (∫ x, (f x + g x) ^ p ∂μ) ^ (1 / p)
    simp [hBz, A, S, he]
  have hAp0 : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  have hBp0 : 0 < B := lt_of_le_of_ne hB (Ne.symm hBz)
  have hAB : 0 < A + B := add_pos hAp0 hBp0
  have hpoint (x : ℝ) :
      A / (A + B) * (f x / A) ^ p + B / (A + B) * (g x / B) ^ p ≤
        ((f x + g x) / (A + B)) ^ p := by
    have h := (Real.concaveOn_rpow hp0.le hp1.le).2
      (show f x / A ∈ Set.Ici 0 from div_nonneg (hf0 x) hA)
      (show g x / B ∈ Set.Ici 0 from div_nonneg (hg0 x) hB)
      (show 0 ≤ A / (A + B) from div_nonneg hA hAB.le)
      (show 0 ≤ B / (A + B) from div_nonneg hB hAB.le)
      (show A / (A + B) + B / (A + B) = 1 from by field_simp)
    simp only [smul_eq_mul] at h
    convert h using 1
    congr 1
    field_simp
  have hfdiv : Integrable (fun x => (f x / A) ^ p) μ := by
    have h := hf.div_const (A ^ p)
    convert h using 1
    ext x
    exact Real.div_rpow (hf0 x) hA p
  have hgdiv : Integrable (fun x => (g x / B) ^ p) μ := by
    have h := hg.div_const (B ^ p)
    convert h using 1
    ext x
    exact Real.div_rpow (hg0 x) hB p
  have hsumdiv : Integrable (fun x => ((f x + g x) / (A + B)) ^ p) μ := by
    have h := hsum.div_const ((A + B) ^ p)
    convert h using 1
    ext x
    exact Real.div_rpow (add_nonneg (hf0 x) (hg0 x)) hAB.le p
  have hi := integral_mono_ae ((hfdiv.const_mul (A / (A + B))).add (hgdiv.const_mul (B / (A + B))))
    hsumdiv (Eventually.of_forall hpoint)
  have hfa : (∫ x, (f x / A) ^ p ∂μ) = 1 := by
    have he : (∫ x, (f x / A) ^ p ∂μ) = S / (A ^ p) := by
      simp_rw [Real.div_rpow (hf0 _) hA, integral_div]
      rfl
    rw [he, hAp, div_self (by rw [← hAp]; exact (Real.rpow_pos_of_pos hAp0 _).ne')]
  have hgb : (∫ x, (g x / B) ^ p ∂μ) = 1 := by
    have he : (∫ x, (g x / B) ^ p ∂μ) = T / (B ^ p) := by
      simp_rw [Real.div_rpow (hg0 _) hB, integral_div]
      rfl
    rw [he, hBp, div_self (by rw [← hBp]; exact (Real.rpow_pos_of_pos hBp0 _).ne')]
  simp only [Pi.add_apply] at hi
  rw [integral_add (hfdiv.const_mul _) (hgdiv.const_mul _), integral_const_mul,
    integral_const_mul, hfa, hgb] at hi
  have hone : A / (A + B) * 1 + B / (A + B) * 1 = 1 := by field_simp
  rw [hone] at hi
  have he : (∫ x, ((f x + g x) / (A + B)) ^ p ∂μ) =
      (∫ x, (f x + g x) ^ p ∂μ) / (A + B) ^ p := by
    simp_rw [Real.div_rpow (add_nonneg (hf0 _) (hg0 _)) hAB.le, integral_div]
  rw [he, one_le_div (Real.rpow_pos_of_pos hAB _)] at hi
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hAB.le _) hi (inv_nonneg.mpr hp0.le)
  rw [Real.rpow_rpow_inv hAB.le hp0.ne'] at h
  simpa [μ, A, B, S, T, one_div] using h

/-- Integrability of a positive power of a nonnegative function gives membership in the
corresponding Lebesgue space; measurability is recovered by taking the inverse power. -/
private lemma memLp_of_nonneg_integrable_rpow {f : ℝ → ℝ} {μ : Measure ℝ} {p : ℝ} (hp : 0 < p)
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable (fun x => f x ^ p) μ) :
    MemLp f (ENNReal.ofReal p) μ := by
  have hm : AEStronglyMeasurable f μ := by
    have h := (Real.continuous_rpow_const (inv_nonneg.mpr hp.le)).comp_aestronglyMeasurable
      hf.aestronglyMeasurable
    exact h.congr (Eventually.of_forall fun x => Real.rpow_rpow_inv (hf0 x) hp.ne')
  apply (integrable_norm_rpow_iff hm (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_of_nonneg (hf0 _)] using hf

/-- For a strictly convex or strictly concave function, equality in the integral of a
fixed positive weighted Jensen combination forces the two inputs to agree almost everywhere. -/
private lemma integral_strict_jensen_eq_iff {f g : ℝ → ℝ} {μ : Measure ℝ} {F : ℝ → ℝ}
    (hF : StrictConvexOn ℝ (Ici 0) F ∨ StrictConcaveOn ℝ (Ici 0) F)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hts : t + s = 1)
    (hf : Integrable (fun x => F (f x)) μ) (hg : Integrable (fun x => F (g x)) μ)
    (hfg : Integrable (fun x => F (t * f x + s * g x)) μ) :
    (∫ x, F (t * f x + s * g x) ∂μ) = t * (∫ x, F (f x) ∂μ) + s * (∫ x, F (g x) ∂μ) ↔
      f =ᵐ[μ] g := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hf.const_mul _) (hg.const_mul _)]
  rcases hF with hF | hF
  · have hle (x) : F (t * f x + s * g x) ≤ t * F (f x) + s * F (g x) := by
      simpa only [smul_eq_mul] using hF.convexOn.2 (hf0 x) (hg0 x) ht.le hs.le hts
    rw [integral_eq_iff_of_ae_le (g := fun x => t * F (f x) + s * F (g x))
      hfg ((hf.const_mul _).add (hg.const_mul _)) (Eventually.of_forall hle)]
    apply eventually_congr (Eventually.of_forall fun x => ?_)
    dsimp only
    constructor
    · intro he
      by_contra hne
      have hlt := hF.2 (hf0 x) (hg0 x) hne ht hs hts
      simp only [smul_eq_mul] at hlt
      exact (ne_of_lt hlt) he
    · intro he
      rw [he, ← add_mul, hts, one_mul, ← add_mul, hts, one_mul]
  · have hle (x) : t * F (f x) + s * F (g x) ≤ F (t * f x + s * g x) := by
      simpa only [smul_eq_mul] using hF.concaveOn.2 (hf0 x) (hg0 x) ht.le hs.le hts
    rw [eq_comm, integral_eq_iff_of_ae_le (f := fun x => t * F (f x) + s * F (g x))
      ((hf.const_mul _).add (hg.const_mul _)) hfg (Eventually.of_forall hle)]
    apply eventually_congr (Eventually.of_forall fun x => ?_)
    dsimp only
    constructor
    · intro he
      by_contra hne
      have hlt := hF.2 (hf0 x) (hg0 x) hne ht hs hts
      simp only [smul_eq_mul] at hlt
      exact (ne_of_lt hlt) he
    · intro he
      rw [he, ← add_mul, hts, one_mul, ← add_mul, hts, one_mul]

/-- Equality between the power-integral norm of a sum and the sum of two positive
normalizing factors is equivalent to equality of the normalized functions almost everywhere. -/
private lemma integral_rpow_add_eq_iff_normalized_eq {f g : ℝ → ℝ} {μ : Measure ℝ} {p : ℝ}
    (hp : 0 < p) (hp1 : p ≠ 1) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : Integrable (fun x => f x ^ p) μ) (hg : Integrable (fun x => g x ^ p) μ)
    (hfg : Integrable (fun x => (f x + g x) ^ p) μ)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hsa : ∫ x, (f x / A) ^ p ∂μ = 1) (hsb : ∫ x, (g x / B) ^ p ∂μ = 1) :
    (∫ x, (f x + g x) ^ p ∂μ) ^ (1 / p) = A + B ↔ ∀ᵐ x ∂μ, f x / A = g x / B := by
  have hC : 0 < A + B := add_pos hA hB
  have hweights : A / (A + B) + B / (A + B) = 1 := by field_simp
  have hF : StrictConvexOn ℝ (Ici 0) (fun x : ℝ => x ^ p) ∨
      StrictConcaveOn ℝ (Ici 0) (fun x : ℝ => x ^ p) := by
    rcases lt_or_gt_of_ne hp1 with hlt | hgt
    · exact Or.inr (Real.strictConcaveOn_rpow hp hlt)
    · exact Or.inl (strictConvexOn_rpow hgt)
  have hpoint (x) : A / (A + B) * (f x / A) + B / (A + B) * (g x / B) =
      (f x + g x) / (A + B) := by field_simp
  have hfn : Integrable (fun x => (f x / A) ^ p) μ := by
    simpa only [Real.div_rpow (hf0 _) hA.le] using hf.div_const (A ^ p)
  have hgn : Integrable (fun x => (g x / B) ^ p) μ := by
    simpa only [Real.div_rpow (hg0 _) hB.le] using hg.div_const (B ^ p)
  have hfgN : Integrable (fun x => ((f x + g x) / (A + B)) ^ p) μ := by
    simpa only [Real.div_rpow (add_nonneg (hf0 _) (hg0 _)) hC.le] using hfg.div_const ((A + B) ^ p)
  have hj := integral_strict_jensen_eq_iff hF
    (fun x => div_nonneg (hf0 x) hA.le) (fun x => div_nonneg (hg0 x) hB.le)
    (div_pos hA hC) (div_pos hB hC) hweights hfn hgn (by simp_rw [hpoint]; exact hfgN)
  simp_rw [hpoint] at hj
  rw [hsa, hsb, mul_one, mul_one, hweights] at hj
  change (∫ x, ((f x + g x) / (A + B)) ^ p ∂μ) = 1 ↔
    ∀ᵐ x ∂μ, f x / A = g x / B at hj
  rw [← hj]
  simp_rw [Real.div_rpow (add_nonneg (hf0 _) (hg0 _)) hC.le]
  rw [integral_div, div_eq_one_iff_eq (Real.rpow_pos_of_pos hC _).ne']
  simpa only [one_div] using Real.rpow_inv_eq
    (integral_nonneg fun x => Real.rpow_nonneg (add_nonneg (hf0 x) (hg0 x)) _) hC.le hp.ne'

/-- Two nonnegative functions with nonzero power-integral norms have the same normalization
almost everywhere exactly when they are proportional by real constants. -/
private lemma normalized_rpow_integral_eq_iff_proportional {f g : ℝ → ℝ} {μ : Measure ℝ} {p : ℝ}
    (hp : 0 < p) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hAp : A ^ p = ∫ x, f x ^ p ∂μ) (hBp : B ^ p = ∫ x, g x ^ p ∂μ) :
    (∀ᵐ x ∂μ, f x / A = g x / B) ↔
      ∃ C D : ℝ, (C ≠ 0 ∨ D ≠ 0) ∧ ∀ᵐ x ∂μ, C * f x = D * g x := by
  constructor
  · intro h
    refine ⟨B, A, Or.inl hB.ne', h.mono fun x hx => ?_⟩
    have := (div_eq_div_iff hA.ne' hB.ne').mp hx
    nlinarith
  · rintro ⟨C, D, hCD, h⟩
    have hpow : ∀ᵐ x ∂μ, |C| ^ p * f x ^ p = |D| ^ p * g x ^ p := by
      filter_upwards [h] with x hx
      rw [← Real.mul_rpow (abs_nonneg _) (hf0 x), ← Real.mul_rpow (abs_nonneg _) (hg0 x)]
      have he := congrArg abs hx
      simp only [abs_mul, abs_of_nonneg (hf0 x), abs_of_nonneg (hg0 x)] at he
      rw [he]
    have hCDp : |C| ^ p ≠ 0 ∨ |D| ^ p ≠ 0 := hCD.imp
      (fun h => (Real.rpow_pos_of_pos (abs_pos.mpr h) _).ne')
      (fun h => (Real.rpow_pos_of_pos (abs_pos.mpr h) _).ne')
    have hs : (∫ x, f x ^ p ∂μ) ≠ 0 := hAp ▸ (Real.rpow_pos_of_pos hA _).ne'
    have ht : (∫ x, g x ^ p ∂μ) ≠ 0 := hBp ▸ (Real.rpow_pos_of_pos hB _).ne'
    have hr := (div_integral_eq_iff_proportional (f := fun x => f x ^ p) (g := fun x => g x ^ p)
      hs ht rfl rfl).mpr ⟨|C| ^ p, |D| ^ p, hCDp, hpow⟩
    filter_upwards [hr] with x hx
    apply (Real.rpow_left_inj (div_nonneg (hf0 x) hA.le) (div_nonneg (hg0 x) hB.le) hp.ne').mp
    simpa only [Real.div_rpow (hf0 x) hA.le, Real.div_rpow (hg0 x) hB.le, hAp, hBp] using hx

/-- DLMF 1.7.6, equality case: for `p > 0`, `p ≠ 1`, equality holds in Minkowski's inequality
iff `A f = B g` almost everywhere, with `A`, `B` not both zero. -/
@[dlmf 1.7.E6]
theorem integral_add_rpow_eq_iff {f g : ℝ → ℝ} {s : Set ℝ} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≠ 1)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : IntegrableOn (fun x => f x ^ p) s) (hg : IntegrableOn (fun x => g x ^ p) s) :
    (∫ x in s, (f x + g x) ^ p) ^ (1 / p) =
        (∫ x in s, f x ^ p) ^ (1 / p) + (∫ x in s, g x ^ p) ^ (1 / p) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ᵐ x ∂(volume.restrict s), A * f x = B * g x := by
  let μ := volume.restrict s
  let S := ∫ x, f x ^ p ∂μ
  let T := ∫ x, g x ^ p ∂μ
  have hS : 0 ≤ S := integral_nonneg fun x => Real.rpow_nonneg (hf0 x) _
  have hT : 0 ≤ T := integral_nonneg fun x => Real.rpow_nonneg (hg0 x) _
  by_cases hSz : S = 0
  · have hfz := ae_eq_zero_of_integral_rpow_eq_zero hp0 hf0 hf hSz
    have he : (∫ x, (f x + g x) ^ p ∂μ) = T :=
      integral_congr_ae (hfz.mono fun x hx => by simp [hx])
    have heq : (∫ x, (f x + g x) ^ p ∂μ) ^ (1 / p) = S ^ (1 / p) + T ^ (1 / p) := by
      simp [he, hSz, Real.zero_rpow (inv_ne_zero hp0.ne')]
    exact iff_of_true heq ⟨1, 0, Or.inl one_ne_zero, hfz.mono fun x hx => by simp [hx]⟩
  by_cases hTz : T = 0
  · have hgz := ae_eq_zero_of_integral_rpow_eq_zero hp0 hg0 hg hTz
    have he : (∫ x, (f x + g x) ^ p ∂μ) = S :=
      integral_congr_ae (hgz.mono fun x hx => by simp [hx])
    have heq : (∫ x, (f x + g x) ^ p ∂μ) ^ (1 / p) = S ^ (1 / p) + T ^ (1 / p) := by
      simp [he, hTz, Real.zero_rpow (inv_ne_zero hp0.ne')]
    exact iff_of_true heq ⟨0, 1, Or.inr one_ne_zero, hgz.mono fun x hx => by simp [hx]⟩
  have hSp : 0 < S := hS.lt_of_ne' hSz
  have hTp : 0 < T := hT.lt_of_ne' hTz
  let A := S ^ (1 / p)
  let B := T ^ (1 / p)
  have hA : 0 < A := Real.rpow_pos_of_pos hSp _
  have hB : 0 < B := Real.rpow_pos_of_pos hTp _
  have hAp : A ^ p = S := by
    simpa only [A, one_div] using Real.rpow_inv_rpow hS hp0.ne'
  have hBp : B ^ p = T := by
    simpa only [B, one_div] using Real.rpow_inv_rpow hT hp0.ne'
  have hsum : Integrable (fun x => (f x + g x) ^ p) μ :=
    integrable_rpow_of_nonneg_memLp hp0 (fun x => add_nonneg (hf0 x) (hg0 x))
      ((memLp_of_nonneg_integrable_rpow hp0 hf0 hf).add (memLp_of_nonneg_integrable_rpow hp0 hg0 hg))
  exact (integral_rpow_add_eq_iff_normalized_eq hp0 hp1 hf0 hg0 hf hg hsum hA hB
    (integral_normalized_rpow hp0 hf0 hSp) (integral_normalized_rpow hp0 hg0 hTp)).trans
    (normalized_rpow_integral_eq_iff_proportional hp0 hf0 hg0 hA hB hAp hBp)

/-! ### §1.7(iii) Means -/

/-- DLMF 1.7.7: for positive `a₁, …, aₙ`, `H ≤ G ≤ A`. -/
@[dlmf 1.7.E7]
theorem harmMean_le_geomMean_le_arithMean {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ j, 0 < a j) :
    (n : ℝ) / ∑ j, 1 / a j ≤ (∏ j, a j) ^ (1 / (n : ℝ)) ∧
      (∏ j, a j) ^ (1 / (n : ℝ)) ≤ (∑ j, a j) / n := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have h1 := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 : ℝ)) a (by simp)
    (by simp [hn]) (fun j _ => (ha j).le)
  have h2 := Real.harm_mean_le_geom_mean Finset.univ hne (fun _ => (1 : ℝ)) a (by simp)
    (by simp [hn]) (fun j _ => ha j)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, one_mul] at h1 h2
  exact ⟨by simpa [one_div] using h2, by simpa [one_div] using h1⟩

/-- Helper: `G = A` iff all entries agree. -/
lemma g1b_GA {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) :
    (∏ j, a j) ^ (1 / (n : ℝ)) = (∑ j, a j) / n ↔ ∀ i j, a i = a j := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.geom_mean_eq_arith_mean_weighted_iff_of_pos (s := Finset.univ)
    (fun _ => 1 / (n : ℝ)) a (fun _ _ => by positivity) (by simp; field_simp) (fun j _ => (ha j).le)
  rw [Real.finsetProd_rpow _ _ (fun j _ => (ha j).le), ← Finset.mul_sum] at h
  rw [show (∑ j, a j) / n = 1 / n * ∑ j, a j by ring, h]
  simp

/-- Helper: `H = G` iff all entries agree. -/
lemma g1b_HG {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) :
    (n : ℝ) / ∑ j, 1 / a j = (∏ j, a j) ^ (1 / (n : ℝ)) ↔ ∀ i j, a i = a j := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := g1b_GA hn (fun j => 1 / a j) (fun j => by have := ha j; positivity)
  have hP : 0 < ∏ j, a j := Finset.prod_pos fun j _ => ha j
  have hS : 0 < ∑ j, 1 / a j :=
    Finset.sum_pos (fun j _ => by have := ha j; positivity) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hG : 0 < (∏ j, a j) ^ (1 / (n : ℝ)) := Real.rpow_pos_of_pos hP _
  have e : (∏ j, 1 / a j) ^ (1 / (n : ℝ)) = 1 / (∏ j, a j) ^ (1 / (n : ℝ)) := by
    rw [Finset.prod_div_distrib, Finset.prod_const_one, Real.div_rpow zero_le_one hP.le,
      Real.one_rpow]
  rw [e] at h
  have : (∀ i j, 1 / a i = 1 / a j) ↔ ∀ i j, a i = a j := by
    constructor
    · intro H i j; have := H i j; simpa [one_div, inv_inj] using this
    · intro H i j; rw [H i j]
  rw [← this, ← h]
  constructor
  · intro H; rw [← H]; field_simp
  · intro H; field_simp at H ⊢; linarith

/-- DLMF 1.7.7, equality case: `G = A`, and likewise `H = G`, iff `a₁ = ⋯ = aₙ`. -/
@[dlmf 1.7.E7]
theorem geomMean_eq_arithMean_iff {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) :
    ((∏ j, a j) ^ (1 / (n : ℝ)) = (∑ j, a j) / n ↔ ∀ i j, a i = a j) ∧
      ((n : ℝ) / ∑ j, 1 / a j = (∏ j, a j) ^ (1 / (n : ℝ)) ↔ ∀ i j, a i = a j) :=
  ⟨g1b_GA hn a ha, g1b_HG hn a ha⟩

/-- A positive weighted sum attains a common bound only when every term equals that bound. -/
private lemma weighted_sum_bounds_and_eq_of_pos {n : ℕ} (w b : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (hw1 : ∑ j, w j = 1) {L U : ℝ} (hL : ∀ j, L ≤ b j) (hU : ∀ j, b j ≤ U) :
    L ≤ ∑ j, w j * b j ∧ (∑ j, w j * b j) ≤ U ∧
      ((∑ j, w j * b j) = L → ∀ j, b j = L) ∧
      ((∑ j, w j * b j) = U → ∀ j, b j = U) := by
  have hLo : (∑ j, w j * L) = L := by rw [← sum_mul, hw1, one_mul]
  have hHi : (∑ j, w j * U) = U := by rw [← sum_mul, hw1, one_mul]
  have hlo (j : Fin n) (_ : j ∈ (univ : Finset (Fin n))) : w j * L ≤ w j * b j :=
    mul_le_mul_of_nonneg_left (hL j) (hw j).le
  have hhi (j : Fin n) (_ : j ∈ (univ : Finset (Fin n))) : w j * b j ≤ w j * U :=
    mul_le_mul_of_nonneg_left (hU j) (hw j).le
  refine ⟨by simpa [hLo] using sum_le_sum hlo, by simpa [hHi] using sum_le_sum hhi, ?_, ?_⟩
  · intro he j
    have hh := (sum_eq_sum_iff_of_le hlo).mp (by rw [hLo, he]) j (mem_univ j)
    exact (mul_left_cancel₀ (hw j).ne' hh).symm
  · intro he j
    have hh := (sum_eq_sum_iff_of_le hhi).mp (by rw [hHi, he]) j (mem_univ j)
    exact mul_left_cancel₀ (hw j).ne' hh

/-- A power mean stays in any positive interval containing the entries, with rigid endpoints. -/
private lemma powerMean_bounds_and_eq_of_bounds {n : ℕ} (hn : (univ : Finset (Fin n)).Nonempty)
    (w a : Fin n → ℝ) (hw : ∀ j, 0 < w j) (hw1 : ∑ j, w j = 1) (ha : ∀ j, 0 < a j)
    {L U r : ℝ} (hL : 0 < L) (hU : 0 < U) (hr : r ≠ 0)
    (hLa : ∀ j, L ≤ a j) (haU : ∀ j, a j ≤ U) :
    L ≤ (∑ j, w j * a j ^ r) ^ (1 / r) ∧
      (∑ j, w j * a j ^ r) ^ (1 / r) ≤ U ∧
      ((∑ j, w j * a j ^ r) ^ (1 / r) = L → ∀ j, a j = L) ∧
      ((∑ j, w j * a j ^ r) ^ (1 / r) = U → ∀ j, a j = U) := by
  let S := ∑ j, w j * a j ^ r
  let P := S ^ (1 / r)
  have hS : 0 < S := sum_pos (fun j _ => mul_pos (hw j) (Real.rpow_pos_of_pos (ha j) _)) hn
  have hP : 0 < P := Real.rpow_pos_of_pos hS _
  have hPr : P ^ r = S := by simpa [P, one_div] using Real.rpow_inv_rpow hS.le hr
  have hcancel {v : ℝ} (hv : 0 ≤ v) (h : ∀ j, a j ^ r = v ^ r) : ∀ j, a j = v :=
    fun j => (Real.rpow_left_inj (ha j).le hv hr).mp (h j)
  change L ≤ P ∧ P ≤ U ∧ (P = L → ∀ j, a j = L) ∧ (P = U → ∀ j, a j = U)
  rcases lt_or_gt_of_ne hr with hr | hr
  · have h := weighted_sum_bounds_and_eq_of_pos w (fun j => a j ^ r) hw hw1
      (fun j => Real.rpow_le_rpow_of_nonpos (ha j) (haU j) hr.le)
      (fun j => Real.rpow_le_rpow_of_nonpos hL (hLa j) hr.le)
    refine ⟨(Real.rpow_le_rpow_iff_of_neg hP hL hr).mp (hPr.trans_le h.2.1),
      (Real.rpow_le_rpow_iff_of_neg hU hP hr).mp (h.1.trans_eq hPr.symm), ?_, ?_⟩
    · intro he
      exact hcancel hL.le (h.2.2.2 (by change S = _; rw [← hPr, he]))
    · intro he
      exact hcancel hU.le (h.2.2.1 (by change S = _; rw [← hPr, he]))
  · have h := weighted_sum_bounds_and_eq_of_pos w (fun j => a j ^ r) hw hw1
      (fun j => Real.rpow_le_rpow hL.le (hLa j) hr.le)
      (fun j => Real.rpow_le_rpow (ha j).le (haU j) hr.le)
    refine ⟨(Real.rpow_le_rpow_iff hL.le hP.le hr).mp (h.1.trans_eq hPr.symm),
      (Real.rpow_le_rpow_iff hP.le hU.le hr).mp (hPr.trans_le h.2.1), ?_, ?_⟩
    · intro he
      exact hcancel hL.le (h.2.2.1 (by change S = _; rw [← hPr, he]))
    · intro he
      exact hcancel hU.le (h.2.2.2 (by change S = _; rw [← hPr, he]))

/-- DLMF 1.7.8: for `r ≠ 0`, positive `aⱼ` and weights `pⱼ > 0` with `∑ pⱼ = 1`, the
weighted mean `M(r) = (∑ pⱼ aⱼ^r)^{1/r}` lies between `min aⱼ` and `max aⱼ`, with equality
(on either side) iff `a₁ = ⋯ = aₙ`. (DLMF's further case `r < 0` with some `aⱼ = 0` is the
convention `M(r) = 0 = min aⱼ` of 1.2.22.) -/
@[dlmf 1.7.E8]
theorem min_le_powerMean_le_max {n : ℕ} (hn : (Finset.univ : Finset (Fin n)).Nonempty)
    (w a : Fin n → ℝ) (hw : ∀ j, 0 < w j) (hw1 : ∑ j, w j = 1) (ha : ∀ j, 0 < a j) {r : ℝ}
    (hr : r ≠ 0) :
    Finset.univ.inf' hn a ≤ (∑ j, w j * a j ^ r) ^ (1 / r) ∧
      (∑ j, w j * a j ^ r) ^ (1 / r) ≤ Finset.univ.sup' hn a ∧
      ((Finset.univ.inf' hn a = (∑ j, w j * a j ^ r) ^ (1 / r) ∨
          (∑ j, w j * a j ^ r) ^ (1 / r) = Finset.univ.sup' hn a) ↔ ∀ i j, a i = a j) := by
  obtain ⟨i, hi, hmin⟩ := exists_mem_eq_inf' hn a
  obtain ⟨j, hj, hmax⟩ := exists_mem_eq_sup' hn a
  have hL : 0 < univ.inf' hn a := by rw [hmin]; exact ha i
  have hU : 0 < univ.sup' hn a := by rw [hmax]; exact ha j
  have h := powerMean_bounds_and_eq_of_bounds hn w a hw hw1 ha hL hU hr
    (fun k => inf'_le a (mem_univ k)) (fun k => le_sup' a (mem_univ k))
  refine ⟨h.1, h.2.1, ?_⟩
  constructor
  · rintro (hlo | hhi)
    · have he := h.2.2.1 hlo.symm
      intro k l
      rw [he k, he l]
    · have he := h.2.2.2 hhi
      intro k l
      rw [he k, he l]
  · intro he
    left
    have hc : ∀ k, a k = univ.inf' hn a := fun k => (he k i).trans hmin.symm
    have hs : (∑ k, w k * a k ^ r) = (univ.inf' hn a) ^ r := by
      calc
        _ = ∑ k, w k * (univ.inf' hn a) ^ r :=
          sum_congr rfl (fun k _ => by rw [hc k])
        _ = _ := by rw [← sum_mul, hw1, one_mul]
    rw [hs]
    simpa only [one_div] using (Real.rpow_rpow_inv hL.le hr).symm

/-- Strict Jensen for powers detects equality of the original positive entries. -/
private lemma strictConvex_rpow_sum_le_and_eq_iff {n : ℕ} (w a : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (hw1 : ∑ j, w j = 1) (ha : ∀ j, 0 < a j) {r : ℝ} (hr : r ≠ 0)
    {φ : ℝ → ℝ} (hφ : StrictConvexOn ℝ (Ioi 0) φ) :
    φ (∑ j, w j * a j ^ r) ≤ ∑ j, w j * φ (a j ^ r) ∧
      (φ (∑ j, w j * a j ^ r) = ∑ j, w j * φ (a j ^ r) ↔ ∀ i j, a i = a j) := by
  have hm (j : Fin n) (_ : j ∈ (univ : Finset (Fin n))) : a j ^ r ∈ Ioi (0 : ℝ) :=
    Real.rpow_pos_of_pos (ha j) _
  have hle := hφ.convexOn.map_sum_le (fun j _ => (hw j).le) hw1 hm
  have heq := hφ.map_sum_eq_iff_of_pos (fun j _ => hw j) hw1 hm
  simp only [smul_eq_mul] at hle heq
  refine ⟨hle, ?_⟩
  constructor
  · intro h i j
    exact (Real.rpow_left_inj (ha i).le (ha j).le hr).mp (heq.mp h (mem_univ i) (mem_univ j))
  · intro h
    apply heq.mpr
    intro i hi j hj
    rw [h i j]

/-- Jensen's comparison for two orders reverses direction when the larger order is negative. -/
private lemma powerMean_jensen_comparison {n : ℕ} (w a : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (hw1 : ∑ j, w j = 1) (ha : ∀ j, 0 < a j) {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0)
    (hrs : r < s) :
    (if 0 < s then (∑ j, w j * a j ^ r) ^ (s / r) ≤ ∑ j, w j * a j ^ s
      else (∑ j, w j * a j ^ s) ≤ (∑ j, w j * a j ^ r) ^ (s / r)) ∧
    ((∑ j, w j * a j ^ r) ^ (s / r) = ∑ j, w j * a j ^ s ↔ ∀ i j, a i = a j) := by
  have hpoint (j : Fin n) : (a j ^ r) ^ (s / r) = a j ^ s := by
    rw [← Real.rpow_mul (ha j).le]
    congr 1
    field_simp
  by_cases hrpos : 0 < r
  · have hspos : 0 < s := hrpos.trans hrs
    have ht : 1 < s / r := (one_lt_div hrpos).mpr hrs
    have hconv := (strictConvexOn_rpow ht).subset Ioi_subset_Ici_self (convex_Ioi 0)
    have h := strictConvex_rpow_sum_le_and_eq_iff w a hw hw1 ha hr hconv
    simpa only [hpoint, ite_eq_left hspos] using h
  · have hrneg : r < 0 := lt_of_le_of_ne (le_of_not_gt hrpos) hr
    by_cases hspos : 0 < s
    · have ht : s / r < 0 := div_neg_of_pos_of_neg hspos hrneg
      have h := strictConvex_rpow_sum_le_and_eq_iff w a hw hw1 ha hr
        (Real.strictConvexOn_rpow_of_neg ht)
      simpa only [hpoint, ite_eq_left hspos] using h
    · have hsneg : s < 0 := lt_of_le_of_ne (le_of_not_gt hspos) hs
      have ht0 : 0 < s / r := div_pos_of_neg_of_neg hsneg hrneg
      have ht1 : s / r < 1 := (div_lt_one_of_neg hrneg).mpr hrs
      have hconc := (Real.strictConcaveOn_rpow ht0 ht1).subset
        Ioi_subset_Ici_self (convex_Ioi 0)
      have h := strictConvex_rpow_sum_le_and_eq_iff w a hw hw1 ha hr hconc.neg
      simpa only [Pi.neg_apply, mul_neg, hpoint, sum_neg_distrib, neg_le_neg_iff,
        neg_inj, ite_eq_right hspos] using h

/-- DLMF 1.7.9: for positive `aⱼ`, weights `pⱼ > 0` with `∑ pⱼ = 1`, and nonzero `r < s`,
`M(r) ≤ M(s)`, with equality iff all `aⱼ` are equal. -/
@[dlmf 1.7.E9]
theorem powerMean_le_powerMean {n : ℕ} (w a : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (hw1 : ∑ j, w j = 1) (ha : ∀ j, 0 < a j) {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0)
    (hrs : r < s) :
    (∑ j, w j * a j ^ r) ^ (1 / r) ≤ (∑ j, w j * a j ^ s) ^ (1 / s) ∧
      ((∑ j, w j * a j ^ r) ^ (1 / r) = (∑ j, w j * a j ^ s) ^ (1 / s) ↔
        ∀ i j, a i = a j) := by
  have hn : (univ : Finset (Fin n)).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hh := hw1
    rw [he, sum_empty] at hh
    norm_num at hh
  let S := ∑ j, w j * a j ^ r
  let T := ∑ j, w j * a j ^ s
  let P := S ^ (1 / r)
  let Q := T ^ (1 / s)
  have hS : 0 < S := sum_pos (fun j _ => mul_pos (hw j) (Real.rpow_pos_of_pos (ha j) _)) hn
  have hT : 0 < T := sum_pos (fun j _ => mul_pos (hw j) (Real.rpow_pos_of_pos (ha j) _)) hn
  have hP : 0 < P := Real.rpow_pos_of_pos hS _
  have hQ : 0 < Q := Real.rpow_pos_of_pos hT _
  have hPs : P ^ s = S ^ (s / r) := by
    dsimp only [P]
    rw [← Real.rpow_mul hS.le]
    congr 1
    ring
  have hQs : Q ^ s = T := by simpa [Q, one_div] using Real.rpow_inv_rpow hT.le hs
  have hJ := powerMean_jensen_comparison w a hw hw1 ha hr hs hrs
  change (if 0 < s then S ^ (s / r) ≤ T else T ≤ S ^ (s / r)) ∧
    (S ^ (s / r) = T ↔ ∀ i j, a i = a j) at hJ
  change P ≤ Q ∧ (P = Q ↔ ∀ i j, a i = a j)
  have heq : P = Q ↔ S ^ (s / r) = T := by
    rw [← Real.rpow_left_inj hP.le hQ.le hs, hPs, hQs]
  refine ⟨?_, heq.trans hJ.2⟩
  by_cases hspos : 0 < s
  · have hle : S ^ (s / r) ≤ T := by simpa only [ite_eq_left hspos] using hJ.1
    exact (Real.rpow_le_rpow_iff hP.le hQ.le hspos).mp (hPs.trans_le (hle.trans_eq hQs.symm))
  · have hsneg : s < 0 := lt_of_le_of_ne (le_of_not_gt hspos) hs
    have hle : T ≤ S ^ (s / r) := by simpa only [ite_eq_right hspos] using hJ.1
    exact (Real.rpow_le_rpow_iff_of_neg hQ hP hsneg).mp (hQs.trans_le (hle.trans_eq hPs.symm))

/-! ### §1.7(iv) Jensen's inequality -/

/-- DLMF 1.7.10 (Jensen's inequality): for `f` integrable on `[0, 1]` with `a < f(x) < b` and
`φ` convex on `(a, b)`, `φ(∫₀¹ f) ≤ ∫₀¹ φ(f)`; `φ ∘ f` is assumed integrable. -/
@[dlmf 1.7.E10]
theorem convexOn_Ioo_map_integral_le {f φ : ℝ → ℝ} {a b : ℝ} (hφ : ConvexOn ℝ (Ioo a b) φ)
    (hf : IntegrableOn f (Icc 0 1)) (hfab : ∀ x ∈ Icc (0 : ℝ) 1, f x ∈ Ioo a b)
    (hφf : IntegrableOn (fun x => φ (f x)) (Icc 0 1)) :
    φ (∫ x in (0 : ℝ)..1, f x) ≤ ∫ x in (0 : ℝ)..1, φ (f x) := by
  have hfi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (hf.mono_set Ioc_subset_Icc_self)
  have hφi : IntervalIntegrable (fun x => φ (f x)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (hφf.mono_set Ioc_subset_Icc_self)
  set m := ∫ x in (0 : ℝ)..1, f x with hmdef
  have hma : a < m := by
    have := intervalIntegral.intervalIntegral_pos_of_pos_on (hfi.sub intervalIntegrable_const)
      (fun x hx => sub_pos.mpr (hfab x (Ioo_subset_Icc_self hx)).1) (zero_lt_one' ℝ)
    rw [intervalIntegral.integral_sub hfi intervalIntegrable_const] at this
    simpa using this
  have hmb : m < b := by
    have := intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_const.sub hfi)
      (fun x hx => sub_pos.mpr (hfab x (Ioo_subset_Icc_self hx)).2) (zero_lt_one' ℝ)
    rw [intervalIntegral.integral_sub intervalIntegrable_const hfi] at this
    simpa using this
  have hmi : m ∈ interior (Ioo a b) := by rw [interior_Ioo]; exact ⟨hma, hmb⟩
  set sl := derivWithin φ (Ioi m) m
  have hsupp : ∀ y ∈ Ioo a b, φ m + sl * (y - m) ≤ φ y := by
    intro y hy
    rcases lt_trichotomy y m with hym | rfl | hym
    · have h1 := hφ.slope_le_leftDeriv_of_mem_interior hy hmi hym
      have h2 := hφ.leftDeriv_le_rightDeriv_of_mem_interior hmi
      have h3 : slope φ y m ≤ sl := h1.trans h2
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hym)] at h3
      nlinarith
    · simp
    · have h3 : sl ≤ slope φ m y := hφ.rightDeriv_le_slope_of_mem_interior hmi hy hym
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hym)] at h3
      linarith
  have hgi : IntervalIntegrable (fun x => φ m + sl * (f x - m)) volume 0 1 :=
    intervalIntegrable_const.add ((hfi.sub intervalIntegrable_const).const_mul sl)
  have hle := intervalIntegral.integral_mono_on zero_le_one hgi hφi
    (fun x hx => hsupp (f x) (hfab x hx))
  rw [intervalIntegral.integral_add intervalIntegrable_const
      ((hfi.sub intervalIntegrable_const).const_mul sl), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hfi intervalIntegrable_const, ← hmdef] at hle
  simpa using hle

/-- DLMF 1.7.11 (corrected to `≤`): for `f > 0` on `[0, 1]` with `f` and `ln f` integrable,
`exp(∫₀¹ ln f) ≤ ∫₀¹ f`. DLMF prints `<`, which fails for constant `f`; see
`exp_integral_log_lt_integral` for the strict form. -/
@[dlmf 1.7.E11]
theorem exp_integral_log_le_integral {f : ℝ → ℝ} (hf0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 < f x)
    (hf : IntegrableOn f (Icc 0 1)) (hlog : IntegrableOn (fun x => Real.log (f x)) (Icc 0 1)) :
    Real.exp (∫ x in (0 : ℝ)..1, Real.log (f x)) ≤ ∫ x in (0 : ℝ)..1, f x := by
  have hfi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (hf.mono_set Ioc_subset_Icc_self)
  have hli : IntervalIntegrable (fun x => Real.log (f x)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (hlog.mono_set Ioc_subset_Icc_self)
  set m := ∫ x in (0 : ℝ)..1, f x
  have hm : 0 < m := intervalIntegral.intervalIntegral_pos_of_pos_on hfi
    (fun x hx => hf0 x (Ioo_subset_Icc_self hx)) zero_lt_one
  have hpt : ∀ x ∈ Icc (0 : ℝ) 1, Real.log (f x) ≤ Real.log m + (f x / m - 1) := by
    intro x hx
    have h := Real.log_le_sub_one_of_pos (div_pos (hf0 x hx) hm)
    rw [Real.log_div (hf0 x hx).ne' hm.ne'] at h
    linarith
  have hgi : IntervalIntegrable (fun x => Real.log m + (f x / m - 1)) volume 0 1 :=
    intervalIntegrable_const.add ((hfi.div_const m).sub intervalIntegrable_const)
  have hle := intervalIntegral.integral_mono_on zero_le_one hli hgi hpt
  rw [intervalIntegral.integral_add intervalIntegrable_const
      ((hfi.div_const m).sub intervalIntegrable_const),
    intervalIntegral.integral_sub (hfi.div_const m) intervalIntegrable_const,
    intervalIntegral.integral_div, div_self hm.ne'] at hle
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul, sub_self,
    add_zero] at hle
  calc Real.exp (∫ x in (0 : ℝ)..1, Real.log (f x)) ≤ Real.exp (Real.log m) :=
        Real.exp_le_exp.mpr hle
    _ = m := Real.exp_log hm

/-- DLMF 1.7.11 (strict form): if moreover `f` is not almost everywhere constant on `[0, 1]`,
then `exp(∫₀¹ ln f) < ∫₀¹ f`. -/
@[dlmf 1.7.E11]
theorem exp_integral_log_lt_integral {f : ℝ → ℝ} (hf0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 < f x)
    (hf : IntegrableOn f (Icc 0 1)) (hlog : IntegrableOn (fun x => Real.log (f x)) (Icc 0 1))
    (hnc : ¬ ∃ c, ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), f x = c) :
    Real.exp (∫ x in (0 : ℝ)..1, Real.log (f x)) < ∫ x in (0 : ℝ)..1, f x := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  have : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  have he : (fun x => Real.exp (Real.log (f x))) =ᵐ[μ] f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact Real.exp_log (hf0 x hx)
  have hei : Integrable (Real.exp ∘ fun x => Real.log (f x)) μ := hf.congr he.symm
  rcases strictConvexOn_exp.ae_eq_const_or_map_average_lt
      Real.continuous_exp.continuousOn isClosed_univ
      (Eventually.of_forall fun _ => Set.mem_univ _) hlog hei with hc | hlt
  · exfalso
    apply hnc
    refine ⟨Real.exp (⨍ x, Real.log (f x) ∂μ), ?_⟩
    filter_upwards [hc, he] with x hx hex
    exact hex.symm.trans (congrArg Real.exp hx)
  · simp only [average_eq_integral] at hlt
    change Real.exp (∫ x, Real.log (f x) ∂μ) < ∫ x, Real.exp (Real.log (f x)) ∂μ at hlt
    rw [integral_congr_ae he] at hlt
    simpa only [μ, intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc] using hlt

end DLMF.AlgebraicAnalytic
