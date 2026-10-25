/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic
public import DLMF.Hypergeometric.Continuation
public import Mathlib.Algebra.ContinuedFractions.Basic
public import DLMFMathlib.Analysis.ContinuedFraction.Convergence

/-!
# Continued fractions (DLMF §15.7)

All three coefficient sequences use Mathlib's `GenContFract` and `convs`;
the general continued-fraction machinery is not duplicated.
Convergence is acquired on the common real domain `0 < a,b < c`, `0 < x < 1/2`.
This avoids poles and exceptional terminating fractions. The larger complex
domains in DLMF need a meromorphic/projective formulation at denominator zeros.

The three limits are proved by Pincherle's theorem in the real forms
`GenContFract.cfConv_tendsto_of_ratio_real` (15.7.1, 15.7.3: negative partial numerators) and
`GenContFract.cfConv_tendsto_of_ratio_pos` (15.7.5: positive partial numerators). The backward
solutions are regularized Gauss functions on the lines `(a+⌊j/2⌋, b+⌊(j+1)/2⌋, c+j)`,
`(a, b+j, c+j)` and `(a+j, b+j, c+j)`; their three-term recurrences are combinations of the
regularized contiguous relations of `Continuation.lean`. The ratio bounds come from termwise
comparison of the positive real series (`gaussCF_R_shift_le`, `gaussCF_R_shift_c_le`) and, for
15.7.5, from Euler's transformation.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric

/-- Gauss's continued fraction, with DLMF's subtraction absorbed into the
partial numerators. Mathlib's stream index `k` corresponds to DLMF's `k+1`. -/
@[dlmf 15.7.E2]
def gaussContinuedFraction (a b c z : ℂ) : GenContFract ℂ where
  h := c
  s := Stream'.Seq.ofStream fun k =>
    let n : ℂ := ((k + 1) / 2 : ℕ)
    ⟨-(if (k + 1)%2 = 1 then (a + n) * (c - b + n) else (b + n) * (c - a + n)) * z,
      c + (k + 1 : ℕ)⟩

/-- The second expansion of the same quotient. -/
@[dlmf 15.7.E4]
def contiguousContinuedFraction (a b c z : ℂ) : GenContFract ℂ where
  h := c + (b - a + 1) * z
  s := Stream'.Seq.ofStream fun k =>
    let n : ℂ := (k + 1 : ℕ)
    ⟨-(b + n) * (c - a + n) * z, c + n + (b - a + n + 1) * z⟩

/-- The continued fraction associated with the derivative quotient. -/
@[dlmf 15.7.E6]
def derivativeContinuedFraction (a b c z : ℂ) : GenContFract ℂ where
  h := c - (a + b + 1) * z
  s := Stream'.Seq.ofStream fun k =>
    let n : ℂ := (k + 1 : ℕ)
    ⟨(a + n) * (b + n) * z * (1 - z), c + n - (a + b + 2 * n + 1) * z⟩

/-! ### Convergence via Pincherle's theorem -/

/-- The `n`-th term of the real regularized Gauss series. -/
def gaussCF_term (α β γ x : ℝ) (n : ℕ) : ℝ :=
  (ascPochhammer ℝ n).eval α * (ascPochhammer ℝ n).eval β * x ^ n / n.factorial *
    (Real.Gamma (γ + n))⁻¹

/-- The real regularized Gauss function `∑ (α)ₙ (β)ₙ xⁿ / (n! Γ(γ+n))`. -/
def gaussCF_R (α β γ x : ℝ) : ℝ := ∑' n, gaussCF_term α β γ x n

/-- The real terms are the complex terms of `regularizedGaussHGFun` at real arguments. -/
lemma gaussCF_term_ofReal (α β γ x : ℝ) (n : ℕ) :
    ((gaussCF_term α β γ x n : ℝ) : ℂ) = (ascPochhammer ℂ n).eval (α : ℂ) *
      (ascPochhammer ℂ n).eval (β : ℂ) * (x : ℂ) ^ n / n.factorial *
        (Gamma ((γ : ℂ) + n))⁻¹ := by
  have h1 := poch_ofReal α n
  have h2 := poch_ofReal β n
  simp only [poch] at h1 h2
  rw [h1, h2, show (γ : ℂ) + n = ((γ + n : ℝ) : ℂ) by push_cast; ring, Gamma_ofReal]
  simp [gaussCF_term]

/-- Summability of the real regularized series for `|x| < 1`. -/
lemma gaussCF_summable (α β γ : ℝ) {x : ℝ} (hx : |x| < 1) :
    Summable (gaussCF_term α β γ x) := by
  have h := summable_regularizedGaussHGFun_term (α : ℂ) β γ (z := x)
    (by rwa [Complex.norm_real, Real.norm_eq_abs])
  simp_rw [← gaussCF_term_ofReal] at h
  exact Complex.summable_ofReal.mp h

/-- At real arguments `regularizedGaussHGFun` is the real function `gaussCF_R`. -/
lemma gaussCF_ofReal (α β γ x : ℝ) :
    regularizedGaussHGFun (α : ℂ) β γ x = ((gaussCF_R α β γ x : ℝ) : ℂ) := by
  rw [regularizedGaussHGFun_eq_tsum, gaussCF_R, Complex.ofReal_tsum]
  simp_rw [gaussCF_term_ofReal]

/-- The terms are nonnegative for nonnegative parameters and argument. -/
lemma gaussCF_term_nonneg {α β γ x : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hx : 0 ≤ x) (n : ℕ) : 0 ≤ gaussCF_term α β γ x n := by
  have := poch_eval_nonneg hα n
  have := poch_eval_nonneg hβ n
  have : 0 < Real.Gamma (γ + n) := Real.Gamma_pos_of_pos (by positivity)
  unfold gaussCF_term
  positivity

/-- Positivity of the real regularized function for `α, β ≥ 0`, `γ > 0`, `0 ≤ x < 1`. -/
lemma gaussCF_R_pos {α β γ x : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hx : 0 ≤ x) (hx1 : x < 1) : 0 < gaussCF_R α β γ x := by
  refine (gaussCF_summable α β γ (by rwa [abs_of_nonneg hx])).tsum_pos
    (gaussCF_term_nonneg hα hβ hγ hx) 0 ?_
  simp [gaussCF_term, Real.Gamma_pos_of_pos hγ]

/-- Symmetry in the two numerator parameters. -/
lemma gaussCF_R_symm (α β γ x : ℝ) : gaussCF_R α β γ x = gaussCF_R β α γ x := by
  simp only [gaussCF_R, gaussCF_term, mul_comm ((ascPochhammer ℝ _).eval α)]

/-- Termwise comparison of two real regularized Gauss series. -/
lemma gaussCF_R_le_of_term {α β γ α' β' γ' x K : ℝ} (hx : |x| < 1)
    (h : ∀ n, gaussCF_term α' β' γ' x n ≤ K * gaussCF_term α β γ x n) :
    gaussCF_R α' β' γ' x ≤ K * gaussCF_R α β γ x := by
  rw [gaussCF_R, gaussCF_R, ← tsum_mul_left]
  exact (gaussCF_summable α' β' γ' hx).tsum_le_tsum h
    ((gaussCF_summable α β γ hx).mul_left K)

/-- `β (β+1)_n = (β)_n (β+n)`. -/
lemma gaussCF_ascP_succ (β : ℝ) (n : ℕ) :
    β * (ascPochhammer ℝ n).eval (β + 1) = (ascPochhammer ℝ n).eval β * (β + n) := by
  rw [← ascPochhammer_succ_eval, ascPochhammer_succ_left]
  simp [Polynomial.eval_comp]

/-- Shifting `β, γ` by one: `𝐅(α, β+1; γ+1; x) ≤ 𝐅(α, β; γ; x) / β` for `0 < β ≤ γ`. -/
lemma gaussCF_R_shift_le {α β γ x : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hx : 0 ≤ x) (hx1 : x < 1) :
    gaussCF_R α (β + 1) (γ + 1) x ≤ β⁻¹ * gaussCF_R α β γ x := by
  refine gaussCF_R_le_of_term (by rwa [abs_of_nonneg hx]) fun n => ?_
  have hγ : 0 < γ := by linarith
  have hγn : 0 < γ + n := by positivity
  have hΓ : Real.Gamma (γ + 1 + n) = (γ + n) * Real.Gamma (γ + n) := by
    rw [show γ + 1 + n = (γ + n) + 1 by ring, Real.Gamma_add_one hγn.ne']
  have hP : (ascPochhammer ℝ n).eval (β + 1) = (ascPochhammer ℝ n).eval β * (β + n) / β := by
    rw [← gaussCF_ascP_succ]; field_simp
  have hG : 0 < Real.Gamma (γ + n) := Real.Gamma_pos_of_pos hγn
  have h0 := gaussCF_term_nonneg (α := α) (β := β) (γ := γ) hα hβ.le hγ hx n
  unfold gaussCF_term at h0 ⊢
  rw [hΓ, hP]
  set T := (ascPochhammer ℝ n).eval α * (ascPochhammer ℝ n).eval β * x ^ n / n.factorial *
    (Real.Gamma (γ + n))⁻¹ with hT
  have hrw : (ascPochhammer ℝ n).eval α * ((ascPochhammer ℝ n).eval β * (β + n) / β) * x ^ n /
      n.factorial * ((γ + n) * Real.Gamma (γ + n))⁻¹ = T * ((β + n) / (β * (γ + n))) := by
    rw [hT]; field_simp
  rw [hrw, mul_comm β⁻¹]
  refine mul_le_mul_of_nonneg_left ?_ h0
  rw [div_le_iff₀ (by positivity), ← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul]
  linarith

/-- Shifting `γ` by one: `𝐅(α, β; γ+1; x) ≤ 𝐅(α, β; γ; x) / γ` for `γ > 0`. -/
lemma gaussCF_R_shift_c_le {α β γ x : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hx : 0 ≤ x) (hx1 : x < 1) :
    gaussCF_R α β (γ + 1) x ≤ γ⁻¹ * gaussCF_R α β γ x := by
  refine gaussCF_R_le_of_term (by rwa [abs_of_nonneg hx]) fun n => ?_
  have hγn : 0 < γ + n := by positivity
  have hΓ : Real.Gamma (γ + 1 + n) = (γ + n) * Real.Gamma (γ + n) := by
    rw [show γ + 1 + n = (γ + n) + 1 by ring, Real.Gamma_add_one hγn.ne']
  have hG : 0 < Real.Gamma (γ + n) := Real.Gamma_pos_of_pos hγn
  have h0 := gaussCF_term_nonneg hα hβ hγ hx n
  unfold gaussCF_term at h0 ⊢
  rw [hΓ]
  set T := (ascPochhammer ℝ n).eval α * (ascPochhammer ℝ n).eval β * x ^ n / n.factorial *
    (Real.Gamma (γ + n))⁻¹ with hT
  have hrw : (ascPochhammer ℝ n).eval α * (ascPochhammer ℝ n).eval β * x ^ n /
      n.factorial * ((γ + n) * Real.Gamma (γ + n))⁻¹ = T * (γ + n)⁻¹ := by
    rw [hT]; field_simp
  rw [hrw, mul_comm γ⁻¹]
  refine mul_le_mul_of_nonneg_left ?_ h0
  exact inv_anti₀ hγ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])

/-- `𝐅(a,b;c) = c 𝐅(a,b+1;c+1) - a(c-b) z 𝐅(a+1,b+1;c+2)`. -/
lemma gaussCF_rel_I (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z = c * regularizedGaussHGFun a (b + 1) (c + 1) z -
      a * (c - b) * z * regularizedGaussHGFun (a + 1) (b + 1) (c + 2) z := by
  have h1 := regularizedGaussHGFun_contiguous_c b a c hz
  have h2 := regularizedGaussHGFun_contiguous_shift_b a b (c + 1) hz
  have s1 := congrFun (regularizedGaussHGFun_symm b a c) z
  have s2 := congrFun (regularizedGaussHGFun_symm b a (c + 1)) z
  have s3 := congrFun (regularizedGaussHGFun_symm (b + 1) a (c + 1)) z
  rw [s1, s2, s3] at h1
  rw [show c + 1 + 1 = c + 2 by ring] at h2
  linear_combination h1 + (c - b) * h2

/-- `𝐅(a,b+1;c+1) = (c+1) 𝐅(a+1,b+1;c+2) - (b+1)(c-a+1) z 𝐅(a+1,b+2;c+3)`. -/
lemma gaussCF_rel_II (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a (b + 1) (c + 1) z =
      (c + 1) * regularizedGaussHGFun (a + 1) (b + 1) (c + 2) z -
        (b + 1) * (c - a + 1) * z * regularizedGaussHGFun (a + 1) (b + 2) (c + 3) z := by
  have h := gaussCF_rel_I (b + 1) a (c + 1) hz
  rw [congrFun (regularizedGaussHGFun_symm (b + 1) a (c + 1)) z,
    congrFun (regularizedGaussHGFun_symm (b + 1) (a + 1) (c + 1 + 1)) z,
    congrFun (regularizedGaussHGFun_symm (b + 1 + 1) (a + 1) (c + 1 + 2)) z,
    show b + 1 + 1 = b + 2 by ring, show c + 1 + 1 = c + 2 by ring,
    show c + 1 + 2 = c + 3 by ring] at h
  linear_combination h

/-- The backward solution of Gauss's fraction:
`w_{2m} = 𝐅(a+m, b+m; c+2m)`, `w_{2m+1} = 𝐅(a+m, b+m+1; c+2m+1)`. -/
def gaussCF_w (a b c z : ℂ) (j : ℕ) : ℂ :=
  regularizedGaussHGFun (a + ((j / 2 : ℕ) : ℂ)) (b + (((j + 1) / 2 : ℕ) : ℂ)) (c + j) z

/-- The partial numerators of `gaussContinuedFraction`. -/
def gaussCF_num (a b c z : ℂ) (k : ℕ) : ℂ :=
  -(if (k + 1) % 2 = 1 then (a + ((k + 1) / 2 : ℕ)) * (c - b + ((k + 1) / 2 : ℕ))
    else (b + ((k + 1) / 2 : ℕ)) * (c - a + ((k + 1) / 2 : ℕ))) * z

/-- Gauss's fraction in the form `GenContFract.cfConv_ofFun`. -/
lemma gaussContinuedFraction_eq (a b c z : ℂ) :
    gaussContinuedFraction a b c z =
      GenContFract.cfConv_ofFun c (gaussCF_num a b c z) (fun k => c + ((k + 1 : ℕ) : ℂ)) := rfl

/-- The three-term recurrence of the backward solution. -/
lemma gaussCF_w_rec (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (j : ℕ) :
    gaussCF_w a b c z j = (c + j) * gaussCF_w a b c z (j + 1) +
      gaussCF_num a b c z j * gaussCF_w a b c z (j + 2) := by
  rcases Nat.even_or_odd' j with ⟨m, rfl | rfl⟩
  · have e := gaussCF_rel_I (a + m) (b + m) (c + 2 * m) hz
    simp only [gaussCF_w, gaussCF_num, show 2 * m / 2 = m by omega,
      show (2 * m + 1) / 2 = m by omega, show (2 * m + 1 + 1) / 2 = m + 1 by omega,
      show (2 * m + 2 + 1) / 2 = m + 1 by omega,
      show (2 * m + 1) % 2 = 1 by omega, ↓reduceIte]
    push_cast at e ⊢
    ring_nf at e ⊢
    linear_combination e
  · have e := gaussCF_rel_II (a + m) (b + m) (c + 2 * m) hz
    have h2 : ¬ ((2 * m + 1 + 1) % 2 = 1) := by omega
    simp only [gaussCF_w, gaussCF_num, show (2 * m + 1) / 2 = m by omega,
      show (2 * m + 1 + 1) / 2 = m + 1 by omega, show (2 * m + 1 + 1 + 1) / 2 = m + 1 by omega,
      show (2 * m + 1 + 2 + 1) / 2 = m + 2 by omega,
      h2, ↓reduceIte]
    push_cast at e ⊢
    ring_nf at e ⊢
    linear_combination e

/-- The real backward solution. -/
def gaussCF_wR (a b c x : ℝ) (j : ℕ) : ℝ :=
  gaussCF_R (a + (j / 2 : ℕ)) (b + ((j + 1) / 2 : ℕ)) (c + j) x

/-- The real partial numerators. -/
def gaussCF_numR (a b c x : ℝ) (k : ℕ) : ℝ :=
  -(if (k + 1) % 2 = 1 then (a + ((k + 1) / 2 : ℕ)) * (c - b + ((k + 1) / 2 : ℕ))
    else (b + ((k + 1) / 2 : ℕ)) * (c - a + ((k + 1) / 2 : ℕ))) * x

/-- The backward solution at real arguments. -/
lemma gaussCF_w_ofReal (a b c x : ℝ) (j : ℕ) :
    gaussCF_w a b c x j = (gaussCF_wR a b c x j : ℂ) := by
  rw [gaussCF_w, gaussCF_wR, ← gaussCF_ofReal]; push_cast; rfl

/-- The partial numerators at real arguments. -/
lemma gaussCF_num_ofReal (a b c x : ℝ) (k : ℕ) :
    gaussCF_num a b c x k = (gaussCF_numR a b c x k : ℂ) := by
  simp only [gaussCF_num, gaussCF_numR]; split_ifs <;> push_cast <;> ring

/-- The real three-term recurrence of the backward solution. -/
lemma gaussCF_wR_rec (a b c : ℝ) {x : ℝ} (hx : |x| < 1) (j : ℕ) :
    gaussCF_wR a b c x j = (c + j) * gaussCF_wR a b c x (j + 1) +
      gaussCF_numR a b c x j * gaussCF_wR a b c x (j + 2) := by
  have := gaussCF_w_rec (a : ℂ) b c (z := x) (by rwa [Complex.norm_real, Real.norm_eq_abs]) j
  rw [gaussCF_w_ofReal, gaussCF_w_ofReal, gaussCF_w_ofReal, gaussCF_num_ofReal] at this
  exact_mod_cast this

section Real

variable {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b) (hca : a < c) (hcb : b < c) (hx : 0 < x)
  (hx1 : x < 1)
include ha hb hca hcb hx hx1

omit hca in
/-- Positivity of the real backward solution. -/
lemma gaussCF_wR_pos (j : ℕ) : 0 < gaussCF_wR a b c x j := by
  have hc : 0 < c := by linarith
  exact gaussCF_R_pos (by positivity) (by positivity) (by positivity) hx.le hx1

omit hx1 in
/-- The partial numerators are negative. -/
lemma gaussCF_numR_neg (j : ℕ) : gaussCF_numR a b c x j < 0 := by
  unfold gaussCF_numR
  have h1 : 0 < c - b := by linarith
  have h2 : 0 < c - a := by linarith
  split_ifs <;> nlinarith [mul_pos (mul_pos (show 0 < a + ((j + 1) / 2 : ℕ) by positivity)
    (show 0 < c - b + ((j + 1) / 2 : ℕ) by positivity)) hx,
    mul_pos (mul_pos (show 0 < b + ((j + 1) / 2 : ℕ) by positivity)
    (show 0 < c - a + ((j + 1) / 2 : ℕ) by positivity)) hx]

omit hx in
/-- The ratio bound `2 |u_j| w_{j+2} ≤ (c+j) w_{j+1}` for `0 < x < 1/2`. -/
lemma gaussCF_key (hx0 : 0 < x) (hx2 : x < 1 / 2) (j : ℕ) :
    2 * (-gaussCF_numR a b c x j) * gaussCF_wR a b c x (j + 2) ≤
      (c + j) * gaussCF_wR a b c x (j + 1) := by
  have hx := hx0
  have hm0 : ∀ m : ℕ, (0 : ℝ) ≤ m := fun m => Nat.cast_nonneg m
  rcases Nat.even_or_odd' j with ⟨m, rfl | rfl⟩
  · -- `w_{2m+2} ≤ w_{2m+1} / (a+m)`
    have hs : gaussCF_wR a b c x (2 * m + 2) ≤ (a + m)⁻¹ * gaussCF_wR a b c x (2 * m + 1) := by
      have := gaussCF_R_shift_le (α := b + m + 1) (β := a + m) (γ := c + 2 * m + 1) (x := x)
        (by positivity) (by positivity) (by linarith [hm0 m]) hx.le hx1
      simp only [gaussCF_wR]
      simp only [show (2 * m + 2) / 2 = m + 1 by omega, show (2 * m + 2 + 1) / 2 = m + 1 by omega,
        show (2 * m + 1) / 2 = m by omega]
      push_cast
      rw [gaussCF_R_symm (a + _), gaussCF_R_symm (a + _)]
      convert this using 2 <;> ring_nf
    have hpos := gaussCF_wR_pos ha hb hcb hx hx1 (2 * m + 1)
    have hnum : -gaussCF_numR a b c x (2 * m) = (a + m) * (c - b + m) * x := by
      simp [gaussCF_numR, show (2 * m + 1) % 2 = 1 by omega, show (2 * m + 1) / 2 = m by omega]
    rw [hnum]
    have ham : 0 < a + m := by positivity
    have hcbm : 0 < c - b + m := by linarith [hm0 m]
    calc 2 * ((a + m) * (c - b + m) * x) * gaussCF_wR a b c x (2 * m + 2)
        ≤ 2 * ((a + m) * (c - b + m) * x) * ((a + m)⁻¹ * gaussCF_wR a b c x (2 * m + 1)) := by
          gcongr
      _ = (2 * x) * (c - b + m) * gaussCF_wR a b c x (2 * m + 1) := by field_simp
      _ ≤ 1 * (c + (2 * m : ℕ)) * gaussCF_wR a b c x (2 * m + 1) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul (by linarith) ?_ hcbm.le (by norm_num))
            hpos.le
          push_cast; linarith [hm0 m]
      _ = _ := by rw [one_mul]
  · have hs : gaussCF_wR a b c x (2 * m + 1 + 2) ≤
        (b + m + 1)⁻¹ * gaussCF_wR a b c x (2 * m + 1 + 1) := by
      have := gaussCF_R_shift_le (α := a + m + 1) (β := b + m + 1) (γ := c + 2 * m + 2) (x := x)
        (by positivity) (by positivity) (by linarith [hm0 m]) hx.le hx1
      simp only [gaussCF_wR]
      simp only [show (2 * m + 1 + 2) / 2 = m + 1 by omega,
        show (2 * m + 1 + 2 + 1) / 2 = m + 2 by omega,
        show (2 * m + 1 + 1) / 2 = m + 1 by omega]
      push_cast
      convert this using 2 <;> ring_nf
    have hnum : -gaussCF_numR a b c x (2 * m + 1) = (b + (m + 1)) * (c - a + (m + 1)) * x := by
      have h2 : ¬ ((2 * m + 1 + 1) % 2 = 1) := by omega
      simp only [gaussCF_numR, h2, ↓reduceIte, show (2 * m + 1 + 1) / 2 = m + 1 by omega]
      push_cast; ring
    rw [hnum]
    have hbm : 0 < b + m + 1 := by positivity
    have hcam : 0 < c - a + (m + 1) := by linarith [hm0 m]
    calc 2 * ((b + (m + 1)) * (c - a + (m + 1)) * x) * gaussCF_wR a b c x (2 * m + 1 + 2)
        ≤ 2 * ((b + (m + 1)) * (c - a + (m + 1)) * x) *
            ((b + m + 1)⁻¹ * gaussCF_wR a b c x (2 * m + 1 + 1)) := by
          gcongr
      _ = (2 * x) * (c - a + (m + 1)) * gaussCF_wR a b c x (2 * m + 1 + 1) := by
          field_simp; ring
      _ ≤ 1 * (c + (2 * m + 1 : ℕ)) * gaussCF_wR a b c x (2 * m + 1 + 1) := by
          have := gaussCF_wR_pos ha hb hcb hx hx1 (2 * m + 1 + 1)
          refine mul_le_mul_of_nonneg_right (mul_le_mul (by linarith) ?_ hcam.le (by norm_num))
            this.le
          push_cast; linarith [hm0 m]
      _ = _ := by rw [one_mul]

end Real

/-- `𝐅(a,β;γ) = (γ + (β-a+1) z) 𝐅(a,β+1;γ+1) - (β+1)(γ-a+1) z 𝐅(a,β+2;γ+2)`. -/
lemma gaussCF_rel_III (a β γ : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a β γ z =
      (γ + (β - a + 1) * z) * regularizedGaussHGFun a (β + 1) (γ + 1) z -
        (β + 1) * (γ - a + 1) * z * regularizedGaussHGFun a (β + 2) (γ + 2) z := by
  have h1 := regularizedGaussHGFun_contiguous_c β a γ hz
  rw [congrFun (regularizedGaussHGFun_symm β a γ) z,
    congrFun (regularizedGaussHGFun_symm β a (γ + 1)) z,
    congrFun (regularizedGaussHGFun_symm (β + 1) a (γ + 1)) z] at h1
  have h2 := regularizedGaussHGFun_contiguous_shift_b a β (γ + 1) hz
  have h3 := regularizedGaussHGFun_contiguous_c a (β + 1) (γ + 1) hz
  have h4 := regularizedGaussHGFun_contiguous_c (β + 1) a (γ + 1) hz
  rw [congrFun (regularizedGaussHGFun_symm (β + 1) a (γ + 1)) z,
    congrFun (regularizedGaussHGFun_symm (β + 1) a (γ + 1 + 1)) z,
    congrFun (regularizedGaussHGFun_symm (β + 1 + 1) a (γ + 1 + 1)) z] at h4
  rw [show γ + 1 + 1 = γ + 2 by ring] at h2 h3 h4
  rw [show β + 1 + 1 = β + 2 by ring] at h4
  linear_combination h1 + (γ - β) * h2 + (γ - β) * z * h3 - (γ + 1 - a) * z * h4

/-- The real backward solution `𝐅(a, b+j; c+j; x)` of the fraction 15.7.3. -/
def gaussCF_vR (a b c x : ℝ) (j : ℕ) : ℝ := gaussCF_R a (b + j) (c + j) x

/-- The three-term recurrence of `𝐅(a, b+j; c+j; x)`. -/
lemma gaussCF_vR_rec (a b c : ℝ) {x : ℝ} (hx : |x| < 1) (j : ℕ) :
    gaussCF_vR a b c x j = (c + j + (b + j - a + 1) * x) * gaussCF_vR a b c x (j + 1) -
      (b + j + 1) * (c + j - a + 1) * x * gaussCF_vR a b c x (j + 2) := by
  have e := gaussCF_rel_III (a : ℂ) ((b + j : ℝ) : ℂ) ((c + j : ℝ) : ℂ) (z := x)
    (by rwa [Complex.norm_real, Real.norm_eq_abs])
  rw [show ((b + j : ℝ) : ℂ) + 1 = ((b + (j + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
    show ((c + j : ℝ) : ℂ) + 1 = ((c + (j + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
    show ((b + j : ℝ) : ℂ) + 2 = ((b + (j + 2 : ℕ) : ℝ) : ℂ) by push_cast; ring,
    show ((c + j : ℝ) : ℂ) + 2 = ((c + (j + 2 : ℕ) : ℝ) : ℂ) by push_cast; ring,
    gaussCF_ofReal, gaussCF_ofReal, gaussCF_ofReal] at e
  simp only [gaussCF_vR]
  have e' : gaussCF_R a (b + j) (c + j) x =
      (c + j + (b + j - a + 1) * x) * gaussCF_R a (b + (j + 1 : ℕ)) (c + (j + 1 : ℕ)) x -
      (b + (j + 1 : ℕ)) * (c + j - a + 1) * x *
        gaussCF_R a (b + (j + 2 : ℕ)) (c + (j + 2 : ℕ)) x := by
    exact_mod_cast e
  rw [e']; push_cast; ring

section Real3

variable {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b) (hcb : b < c) (hx : 0 < x) (hx1 : x < 1)
include ha hb hcb hx hx1

/-- Positivity of `𝐅(a, b+j; c+j; x)`. -/
lemma gaussCF_vR_pos (j : ℕ) : 0 < gaussCF_vR a b c x j := by
  have hc : 0 < c := by linarith
  exact gaussCF_R_pos ha.le (by positivity) (by positivity) hx.le hx1

/-- `𝐅(a, b+j+2; c+j+2) ≤ 𝐅(a, b+j; c+j) / ((b+j)(b+j+1))`. -/
lemma gaussCF_vR_le (j : ℕ) :
    gaussCF_vR a b c x (j + 2) ≤ (b + j + 1)⁻¹ * ((b + j)⁻¹ * gaussCF_vR a b c x j) := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h1 := gaussCF_R_shift_le (α := a) (β := b + j + 1) (γ := c + j + 1) (x := x) ha.le
    (by positivity) (by linarith) hx.le hx1
  have h2 := gaussCF_R_shift_le (α := a) (β := b + j) (γ := c + j) (x := x) ha.le
    (by positivity) (by linarith) hx.le hx1
  simp only [gaussCF_vR]
  push_cast
  have e1 : b + (j + 2) = b + j + 1 + 1 := by ring
  have e2 : c + (j + 2) = c + j + 1 + 1 := by ring
  rw [e1, e2]
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  convert h2 using 2

end Real3

/-- The real backward solution `𝐅(a+j, b+j; c+j; x)` of the fraction 15.7.5. -/
def gaussCF_uR (a b c x : ℝ) (j : ℕ) : ℝ := gaussCF_R (a + j) (b + j) (c + j) x

/-- The three-term recurrence of `𝐅(a+j, b+j; c+j; x)` (the diagonal contiguous relation). -/
lemma gaussCF_uR_rec (a b c : ℝ) {x : ℝ} (hx : |x| < 1) (j : ℕ) :
    gaussCF_uR a b c x j = (c + j - (a + b + 2 * j + 1) * x) * gaussCF_uR a b c x (j + 1) +
      (a + j + 1) * (b + j + 1) * (x * (1 - x)) * gaussCF_uR a b c x (j + 2) := by
  have e := regularizedGaussHGFun_contiguous_diagonal ((a + j : ℝ) : ℂ) ((b + j : ℝ) : ℂ)
    ((c + j : ℝ) : ℂ) (z := x) (by rwa [Complex.norm_real, Real.norm_eq_abs])
  have r1 : ∀ y : ℝ, (y : ℂ) + 1 = ((y + 1 : ℝ) : ℂ) := fun y => by push_cast; ring
  have r2 : ∀ y : ℝ, (y : ℂ) + 2 = ((y + 2 : ℝ) : ℂ) := fun y => by push_cast; ring
  rw [r1, r1, r1, r2, r2, r2, gaussCF_ofReal, gaussCF_ofReal, gaussCF_ofReal] at e
  have e' : x * (1 - x) * (a + j + 1) * (b + j + 1) *
        gaussCF_R (a + j + 2) (b + j + 2) (c + j + 2) x
      + (c + j - (a + j + (b + j) + 1) * x) * gaussCF_R (a + j + 1) (b + j + 1) (c + j + 1) x
      - gaussCF_R (a + j) (b + j) (c + j) x = 0 := by
    exact_mod_cast e
  simp only [gaussCF_uR]
  push_cast
  rw [show a + (j + 1) = a + j + 1 by ring, show b + (j + 1) = b + j + 1 by ring,
    show c + (j + 1) = c + j + 1 by ring, show a + (j + 2) = a + j + 2 by ring,
    show b + (j + 2) = b + j + 2 by ring, show c + (j + 2) = c + j + 2 by ring]
  linear_combination -e'

/-- Euler's transformation for the real regularized function. -/
lemma gaussCF_R_euler (α β γ : ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    gaussCF_R α β γ x = (1 - x) ^ (γ - α - β) * gaussCF_R (γ - α) (γ - β) γ x := by
  have e := regularizedGaussHGFun_euler (α : ℂ) β γ (z := x)
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1)
  rw [show (γ : ℂ) - α - β = ((γ - α - β : ℝ) : ℂ) by push_cast; ring,
    show (γ : ℂ) - α = ((γ - α : ℝ) : ℂ) by push_cast; ring,
    show (γ : ℂ) - β = ((γ - β : ℝ) : ℂ) by push_cast; ring,
    show (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) by push_cast; ring,
    gaussCF_ofReal, gaussCF_ofReal, ← ofReal_cpow (by linarith)] at e
  exact_mod_cast e

/-- `𝐅(a+j+2, b+j+2; c+j+2) ≤ 𝐅(a+j, b+j; c+j) / ((1-x)² (c+j)(c+j+1))`, by Euler's
transformation. -/
lemma gaussCF_uR_le {a b c x : ℝ} (ha : 0 < a) (hca : a < c) (hcb : b < c)
    (hx : 0 < x) (hx1 : x < 1) (j : ℕ) :
    gaussCF_uR a b c x (j + 2) ≤
      ((1 - x) ^ 2 * ((c + j) * (c + j + 1)))⁻¹ * gaussCF_uR a b c x j := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hc : 0 < c := by linarith
  have h1x : 0 < 1 - x := by linarith
  have E2 : gaussCF_uR a b c x (j + 2) = (1 - x) ^ (c - a - b - j) / (1 - x) ^ (2 : ℝ) *
      gaussCF_R (c - a) (c - b) (c + (j + 2)) x := by
    simp only [gaussCF_uR]
    rw [gaussCF_R_euler _ _ _ hx.le hx1, ← Real.rpow_sub h1x]
    push_cast
    congr 2 <;> ring
  have E0 : gaussCF_uR a b c x j = (1 - x) ^ (c - a - b - j) *
      gaussCF_R (c - a) (c - b) (c + j) x := by
    simp only [gaussCF_uR]
    rw [gaussCF_R_euler _ _ _ hx.le hx1]
    congr 2 <;> ring
  rw [E2, E0, Real.rpow_two]
  set P := (1 - x) ^ (c - a - b - j)
  have hP : 0 < P := Real.rpow_pos_of_pos h1x _
  have hs1 := gaussCF_R_shift_c_le (α := c - a) (β := c - b) (γ := c + j + 1) (x := x)
    (by linarith) (by linarith) (by positivity) hx.le hx1
  have hs2 := gaussCF_R_shift_c_le (α := c - a) (β := c - b) (γ := c + j) (x := x)
    (by linarith) (by linarith) (by positivity) hx.le hx1
  have hE : gaussCF_R (c - a) (c - b) (c + (j + 2)) x ≤
      ((c + j) * (c + j + 1))⁻¹ * gaussCF_R (c - a) (c - b) (c + j) x := by
    rw [show c + (j + 2) = c + j + 1 + 1 by ring]
    refine hs1.trans ?_
    rw [mul_inv, mul_comm ((c + j)⁻¹), mul_assoc]
    exact mul_le_mul_of_nonneg_left hs2 (by positivity)
  have hcj : 0 < (c + j) * (c + j + 1) := by positivity
  calc P / (1 - x) ^ 2 * gaussCF_R (c - a) (c - b) (c + (j + 2)) x
      ≤ P / (1 - x) ^ 2 *
          (((c + j) * (c + j + 1))⁻¹ * gaussCF_R (c - a) (c - b) (c + j) x) := by
        gcongr
    _ = _ := by field_simp

@[dlmf 15.7.E1]
theorem gauss_continued_fraction_limit {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hca : a < c) (hcb : b < c) (hx : 0 < x) (hx1 : x < 1 / 2) :
    Tendsto (gaussContinuedFraction a b c x).convs atTop
      (𝓝 (regularizedGaussHGFun a b c (x : ℂ) / regularizedGaussHGFun a (b + 1) (c + 1) (x : ℂ))) := by
  have hx1' : x < 1 := by linarith
  have hxa : |x| < 1 := by rw [abs_of_pos hx]; exact hx1'
  set w := gaussCF_wR a b c x with hwdef
  set A := gaussCF_numR a b c x with hAdef
  set B : ℕ → ℝ := fun k => c + ((k + 1 : ℕ) : ℝ) with hBdef
  have hw : ∀ k, w (k + 1) = B k * w (k + 1 + 1) + A (k + 1) * w (k + 1 + 2) := by
    intro k
    have := gaussCF_wR_rec a b c hxa (k + 1)
    simpa [w, A, B, add_assoc] using this
  have hpos := gaussCF_wR_pos ha hb hcb hx hx1'
  have hneg := gaussCF_numR_neg ha hb hca hcb hx (x := x)
  have key := GenContFract.cfConv_tendsto_of_ratio_real (h := c) (a := A) (b := B)
    (w := fun k => w (k + 1)) hw (hpos 1).ne' (fun k => (hneg k).ne) (N := 0)
    (fun k _ => (hpos _).ne')
    (fun k _ => mul_neg_of_pos_of_neg (hpos _) (mul_neg_of_neg_of_pos (hneg _) (hpos _)))
    (fun k _ => by
      have hk := gaussCF_key ha hb hca hcb hx1' hx hx1 (k + 1)
      have hr := gaussCF_wR_rec a b c hxa (k + 1)
      rw [abs_of_neg (mul_neg_of_neg_of_pos (hneg _) (hpos _)), abs_of_pos (hpos _)]
      simp only [show k + 2 + 1 = k + 1 + 2 by ring]
      push_cast at hk hr ⊢
      nlinarith)
  have hconv : (gaussContinuedFraction a b c x).convs =
      fun n => (((GenContFract.cfConv_ofFun c A B).convs n : ℝ) : ℂ) := by
    funext n
    have hm := GenContFract.cfConv_convs_map (h := c) (a := A) (b := B) Complex.ofRealHom n
    simp only [Complex.ofRealHom_eq_coe] at hm
    rw [gaussContinuedFraction_eq, ← hm,
      show gaussCF_num (a : ℂ) b c x = fun k => ((A k : ℝ) : ℂ) from
        funext fun k => gaussCF_num_ofReal a b c x k,
      show (fun k : ℕ => (c : ℂ) + ((k + 1 : ℕ) : ℂ)) = fun k => ((B k : ℝ) : ℂ) from
        funext fun k => by simp [B]]
  rw [hconv]
  have hval : regularizedGaussHGFun a b c (x : ℂ) /
      regularizedGaussHGFun a (b + 1) (c + 1) (x : ℂ) =
      ((c + A 0 * w (1 + 1) / w (0 + 1) : ℝ) : ℂ) := by
    have e0 := gaussCF_w_ofReal a b c x 0
    have e1 := gaussCF_w_ofReal a b c x 1
    simp only [gaussCF_w] at e0 e1
    norm_num at e0 e1
    rw [e0, e1, ← ofReal_div]
    congr 1
    have h0 := gaussCF_wR_rec a b c hxa 0
    have h1 := (hpos 1).ne'
    simp only [zero_add] at h0 ⊢
    rw [h0]
    simp only [hwdef, hAdef]
    field_simp
    push_cast; ring
  rw [hval]
  exact (Complex.continuous_ofReal.tendsto _).comp key

@[dlmf 15.7.E3]
theorem contiguous_continued_fraction_limit {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hca : a < c) (hcb : b < c) (hx : 0 < x) (hx1 : x < 1 / 2) :
    Tendsto (contiguousContinuedFraction a b c x).convs atTop
      (𝓝 (regularizedGaussHGFun a b c (x : ℂ) / regularizedGaussHGFun a (b + 1) (c + 1) (x : ℂ))) := by
  have hx1' : x < 1 := by linarith
  have hxa : |x| < 1 := by rw [abs_of_pos hx]; exact hx1'
  set v := gaussCF_vR a b c x with hvdef
  set A : ℕ → ℝ := fun k => -(b + ((k + 1 : ℕ) : ℝ)) * (c - a + ((k + 1 : ℕ) : ℝ)) * x with hAdef
  set B : ℕ → ℝ := fun k => c + ((k + 1 : ℕ) : ℝ) + (b - a + ((k + 1 : ℕ) : ℝ) + 1) * x
    with hBdef
  have hw : ∀ k, v (k + 1) = B k * v (k + 1 + 1) + A (k + 1) * v (k + 1 + 2) := by
    intro k
    have := gaussCF_vR_rec a b c hxa (k + 1)
    simp only [v, A, B]
    rw [this]; push_cast; ring
  have hpos := gaussCF_vR_pos ha hb hcb hx hx1' (c := c)
  have hneg : ∀ k, A k < 0 := by
    intro k
    simp only [A]
    have : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : 0 < b + ((k + 1 : ℕ) : ℝ) := by linarith
    have h2 : 0 < c - a + ((k + 1 : ℕ) : ℝ) := by linarith
    have := mul_pos (mul_pos h1 h2) hx
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt c
  have key := GenContFract.cfConv_tendsto_of_ratio_real (h := c + (b - a + 1) * x) (a := A)
    (b := B) (w := fun k => v (k + 1)) hw (hpos 1).ne' (fun k => (hneg k).ne) (N := N)
    (fun k _ => (hpos _).ne')
    (fun k _ => mul_neg_of_pos_of_neg (hpos _) (mul_neg_of_neg_of_pos (hneg _) (hpos _)))
    (fun k hk => by
      rw [abs_of_neg (mul_neg_of_neg_of_pos (hneg _) (hpos _)), abs_of_pos (hpos _)]
      have hle := gaussCF_vR_le ha hb hcb hx hx1' (k + 1)
      have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
      have hj0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hp1 := hpos (k + 1)
      have hp3 := hpos (k + 1 + 2)
      simp only [A, show k + 2 + 1 = k + 1 + 2 by ring]
      push_cast at hle ⊢
      have hb1 : 0 < b + (k + 1) := by linarith
      have hb2 : 0 < b + (k + 1) + 1 := by linarith
      have hc1 : 0 < c - a + (k + 1 + 1) := by linarith
      calc -(-(b + (k + 1 + 1)) * (c - a + (k + 1 + 1)) * x * v (k + 1 + 2))
          = (b + (k + 1) + 1) * (c - a + (k + 1 + 1)) * x * v (k + 1 + 2) := by ring
        _ ≤ (b + (k + 1) + 1) * (c - a + (k + 1 + 1)) * x *
            ((b + (k + 1) + 1)⁻¹ * ((b + (k + 1))⁻¹ * v (k + 1))) := by gcongr
        _ = (c - a + (k + 1 + 1)) * x / (b + (k + 1)) * v (k + 1) := by field_simp
        _ ≤ 1 * v (k + 1) := by
            gcongr
            rw [div_le_one hb1]
            nlinarith
        _ = v (k + 1) := one_mul _)
  have hconv : (contiguousContinuedFraction a b c x).convs =
      fun n => (((GenContFract.cfConv_ofFun (c + (b - a + 1) * x) A B).convs n : ℝ) : ℂ) := by
    funext n
    have hm := GenContFract.cfConv_convs_map (h := c + (b - a + 1) * x) (a := A) (b := B)
      Complex.ofRealHom n
    simp only [Complex.ofRealHom_eq_coe] at hm
    rw [← hm]
    congr 1
    simp only [contiguousContinuedFraction, GenContFract.cfConv_ofFun, A, B]
    push_cast
    rfl
  rw [hconv]
  have hval : regularizedGaussHGFun a b c (x : ℂ) /
      regularizedGaussHGFun a (b + 1) (c + 1) (x : ℂ) =
      ((c + (b - a + 1) * x + A 0 * v (1 + 1) / v (0 + 1) : ℝ) : ℂ) := by
    have e0 := gaussCF_ofReal a b c x
    have e1 := gaussCF_ofReal a (b + 1) (c + 1) x
    push_cast at e1
    rw [e0, e1, ← ofReal_div]
    congr 1
    have h0 := gaussCF_vR_rec a b c hxa 0
    have h1 := (hpos 1).ne'
    rw [show gaussCF_R a b c x = gaussCF_vR a b c x 0 by simp [gaussCF_vR],
      show gaussCF_R a (b + 1) (c + 1) x = gaussCF_vR a b c x 1 by simp [gaussCF_vR], hvdef]
    simp only [zero_add] at h0 ⊢
    rw [h0]
    simp only [A]
    field_simp
    push_cast; ring
  rw [hval]
  exact (Complex.continuous_ofReal.tendsto _).comp key

@[dlmf 15.7.E5]
theorem derivative_continued_fraction_limit {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hca : a < c) (hcb : b < c) (hx : 0 < x) (hx1 : x < 1 / 2) :
    Tendsto (derivativeContinuedFraction a b c x).convs atTop
      (𝓝 (regularizedGaussHGFun a b c (x : ℂ) / regularizedGaussHGFun (a + 1) (b + 1) (c + 1) (x : ℂ))) := by
  have hx1' : x < 1 := by linarith
  have hxa : |x| < 1 := by rw [abs_of_pos hx]; exact hx1'
  have hc : 0 < c := by linarith
  have h1x : 0 < 1 - x := by linarith
  set u := gaussCF_uR a b c x with hudef
  set A : ℕ → ℝ := fun k => (a + ((k + 1 : ℕ) : ℝ)) * (b + ((k + 1 : ℕ) : ℝ)) * x * (1 - x)
    with hAdef
  set B : ℕ → ℝ := fun k => c + ((k + 1 : ℕ) : ℝ) - (a + b + 2 * ((k + 1 : ℕ) : ℝ) + 1) * x
    with hBdef
  have hw : ∀ k, u (k + 1) = B k * u (k + 1 + 1) + A (k + 1) * u (k + 1 + 2) := by
    intro k
    have := gaussCF_uR_rec a b c hxa (k + 1)
    simp only [u, A, B]
    rw [this]; push_cast; ring
  have hpos : ∀ j, 0 < u j := fun j =>
    gaussCF_R_pos (by positivity) (by positivity) (by positivity) hx.le hx1'
  have hApos : ∀ k, 0 < A k := fun k => by
    simp only [A]; positivity
  set θ := x / (1 - x) with hθ
  have hθ0 : 0 < θ := div_pos hx h1x
  have hθ1 : θ < 1 := by rw [div_lt_one h1x]; linarith
  set μ := (1 + θ) / 2 with hμ
  have hμ1 : μ < 1 := by linarith
  set r := μ / θ with hr
  have hr1 : 1 < r := by rw [hr, lt_div_iff₀ hθ0]; linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (μ / (1 - μ))
  have key := GenContFract.cfConv_tendsto_of_ratio_pos (h := c - (a + b + 1) * x) (a := A)
    (b := B) (w := fun k => u (k + 1)) hw (hpos 1).ne' (fun k => (hApos k).ne') (N := N)
    (fun k _ => (hpos _).ne') (fun k _ => mul_pos (hpos _) (mul_pos (hApos _) (hpos _))) hr1
    (fun k hk => by
      rw [abs_of_pos (mul_pos (hApos _) (hpos _)), abs_of_pos (hpos _)]
      have hle := gaussCF_uR_le ha hca hcb hx hx1' (k + 1)
      have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
      have hj0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hp1 := hpos (k + 1)
      simp only [A, show k + 2 + 1 = k + 1 + 2 by ring]
      push_cast at hle ⊢
      set j : ℝ := (k : ℝ) + 1 with hj
      have hj1 : (N : ℝ) + 1 ≤ j := by linarith
      have hcj : 0 < (c + j) * (c + j + 1) := by positivity
      -- the coefficient bound `r (a+j+1)(b+j+1) x(1-x) ≤ (1-x)² (c+j)(c+j+1)`
      have hcoef : r * ((a + (j + 1)) * (b + (j + 1)) * x * (1 - x)) ≤
          (1 - x) ^ 2 * ((c + j) * (c + j + 1)) := by
        have hrx : r * x = μ * (1 - x) := by
          rw [hr, hθ]; field_simp
        have hab : (a + (j + 1)) * (b + (j + 1)) ≤ (c + j + 1) * (c + j + 1) := by
          have : 0 < a + (j + 1) := by positivity
          have : 0 < b + (j + 1) := by positivity
          exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
        have hμc : μ * (c + j + 1) ≤ c + j := by
          have h1 : μ / (1 - μ) < c + j := by linarith
          rw [div_lt_iff₀ (by linarith)] at h1
          nlinarith
        have hμ0 : 0 < μ := by positivity
        calc r * ((a + (j + 1)) * (b + (j + 1)) * x * (1 - x))
            = (r * x) * (1 - x) * ((a + (j + 1)) * (b + (j + 1))) := by ring
          _ = μ * (1 - x) ^ 2 * ((a + (j + 1)) * (b + (j + 1))) := by rw [hrx]; ring
          _ ≤ μ * (1 - x) ^ 2 * ((c + j + 1) * (c + j + 1)) := by gcongr
          _ = (1 - x) ^ 2 * (c + j + 1) * (μ * (c + j + 1)) := by ring
          _ ≤ (1 - x) ^ 2 * (c + j + 1) * (c + j) := by gcongr
          _ = _ := by ring
      have hp3 : 0 < u (k + 1 + 2) := hpos _
      calc r * ((a + (j + 1)) * (b + (j + 1)) * x * (1 - x) * u (k + 1 + 2))
          = (r * ((a + (j + 1)) * (b + (j + 1)) * x * (1 - x))) * u (k + 1 + 2) := by ring
        _ ≤ ((1 - x) ^ 2 * ((c + j) * (c + j + 1))) *
            (((1 - x) ^ 2 * ((c + j) * (c + j + 1)))⁻¹ * u (k + 1)) := by
          gcongr
        _ = u (k + 1) := by rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul])
  have hconv : (derivativeContinuedFraction a b c x).convs =
      fun n => (((GenContFract.cfConv_ofFun (c - (a + b + 1) * x) A B).convs n : ℝ) : ℂ) := by
    funext n
    have hm := GenContFract.cfConv_convs_map (h := c - (a + b + 1) * x) (a := A) (b := B)
      Complex.ofRealHom n
    simp only [Complex.ofRealHom_eq_coe] at hm
    rw [← hm]
    congr 1
    simp only [derivativeContinuedFraction, GenContFract.cfConv_ofFun, A, B]
    push_cast
    rfl
  rw [hconv]
  have hval : regularizedGaussHGFun a b c (x : ℂ) /
      regularizedGaussHGFun (a + 1) (b + 1) (c + 1) (x : ℂ) =
      ((c - (a + b + 1) * x + A 0 * u (1 + 1) / u (0 + 1) : ℝ) : ℂ) := by
    have e0 := gaussCF_ofReal a b c x
    have e1 := gaussCF_ofReal (a + 1) (b + 1) (c + 1) x
    push_cast at e1
    rw [e0, e1, ← ofReal_div]
    congr 1
    have h0 := gaussCF_uR_rec a b c hxa 0
    have h1 : gaussCF_uR a b c x 1 ≠ 0 := (hpos 1).ne'
    rw [show gaussCF_R a b c x = gaussCF_uR a b c x 0 by simp [gaussCF_uR],
      show gaussCF_R (a + 1) (b + 1) (c + 1) x = gaussCF_uR a b c x 1 by simp [gaussCF_uR],
      hudef]
    simp only [zero_add] at h0 ⊢
    rw [h0]
    simp only [A]
    field_simp
    push_cast; ring
  rw [hval]
  exact (Complex.continuous_ofReal.tendsto _).comp key

end DLMF.Hypergeometric
