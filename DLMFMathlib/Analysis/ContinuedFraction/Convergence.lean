/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.PSeries

/-!
# Convergence of generalized continued fractions with field elements

Mathlib's `GenContFract` theory proves convergence mainly for simple continued fractions of
real numbers. This file supplies a Pincherle-type convergence theory for the continued fraction

  `h + a₀/(b₀ + a₁/(b₁ + a₂/(b₂ + ⋯)))`

with arbitrary partial numerators and denominators in a (normed) field, given by sequences
(`GenContFract.cfConv_ofFun`).

* `cfConv_det`: the determinant formula `A_{m+1}B_m - B_{m+1}A_m = (-1)^m ∏_{k ≤ m} a_k`.
* `cfConv_invariant`: a *backward solution* `w_k = b_k w_{k+1} + a_{k+1} w_{k+2}` pairs with the
  continuants: `A_{m+1} w_{m+1} + a_{m+1} A_m w_{m+2} = a₀ w₁ + h w₀` and similarly for `B`.
* `cfConv_error`: the exact error `h + a₀w₁/w₀ - A_{m+1}/B_{m+1}`.
* `cfConv_tendsto_of_minimal` (**Pincherle's theorem**, sufficiency): if the forward solution
  `G_m = (∏_{k ≤ m} a_k) w_{m+1}` attached to `w` is small compared with the denominators, the
  convergents tend to `h + a₀w₁/w₀`.
* `cfConv_tendsto_of_ratio`: a checkable criterion: if eventually `q ‖a_{k+1} w_{k+2}‖ ≤ ‖w_k‖`
  with `q > 2` (that is, the true tails `τ_{k+1} = a_{k+1}w_{k+2}/w_{k+1}` satisfy
  `‖b_k + τ_{k+1}‖ ≥ q ‖τ_{k+1}‖`), then the convergents tend to `h + a₀w₁/w₀`.
* `cfConv_tendsto_of_ratio_real`: the real analogue when `w_k` and `a_{k+1}w_{k+2}` have
  opposite signs and `|a_{k+1} w_{k+2}| ≤ |w_k|` (negative elements, Worpitzky-type).
* `cfConv_tendsto_of_ratio_pos`: the real analogue when `w_k` and `a_{k+1}w_{k+2}` have the
  same sign and `r |a_{k+1} w_{k+2}| ≤ |w_k|` with `r > 1` (positive elements).
* `cfConv_continuants_of_back`, `cfConv_equiv_convs`, `cfConv_convs_smul_a0`: finite backward
  solutions, equivalence transformations, and linearity in `a₀`.
* `cfConv_sfrac_bound`: the value region of an S-fraction `b_k = 1`, `a_k = c_k s²` (`c_k > 0`,
  `Re s > 0`): nonzero denominators and `‖A_n/B_n - h‖ ≤ ‖a₀‖‖s‖/Re s`; with
  `cfConv_convs_differentiableOn` this gives the local boundedness and holomorphy needed for the
  Stieltjes–Vitali convergence argument.
* `cfConv_convs_lt_of_pos`, `cfConv_lt_convs_of_pos`: for positive elements and a positive
  backward solution, even convergents lie below and odd convergents above `h + a₀w₁/w₀`.
-/

@[expose] public noncomputable section

open Filter Finset
open scoped Topology

namespace GenContFract

variable {K : Type*}

/-- The continued fraction `h + a₀/(b₀ + a₁/(b₁ + ⋯))` built from two sequences. -/
def cfConv_ofFun [DivisionRing K] (h : K) (a b : ℕ → K) : GenContFract K where
  h := h
  s := Stream'.Seq.ofStream fun k => ⟨a k, b k⟩

section Algebra

variable [Field K] (h : K) (a b : ℕ → K)

/-- `A₀ = h`. -/
theorem cfConv_nums_zero : (cfConv_ofFun h a b).nums 0 = h := rfl

/-- `B₀ = 1`. -/
theorem cfConv_dens_zero : (cfConv_ofFun h a b).dens 0 = 1 := zeroth_den_eq_one

/-- `A₁ = b₀ h + a₀`. -/
theorem cfConv_nums_one : (cfConv_ofFun h a b).nums 1 = b 0 * h + a 0 :=
  first_num_eq (g := cfConv_ofFun h a b) (gp := ⟨a 0, b 0⟩) rfl

/-- `B₁ = b₀`. -/
theorem cfConv_dens_one : (cfConv_ofFun h a b).dens 1 = b 0 :=
  first_den_eq (g := cfConv_ofFun h a b) (gp := ⟨a 0, b 0⟩) rfl

/-- The numerator recurrence. -/
theorem cfConv_nums_step (n : ℕ) :
    (cfConv_ofFun h a b).nums (n + 2) =
      b (n + 1) * (cfConv_ofFun h a b).nums (n + 1) + a (n + 1) * (cfConv_ofFun h a b).nums n :=
  nums_recurrence (g := cfConv_ofFun h a b) (n := n) (gp := ⟨a (n + 1), b (n + 1)⟩) rfl rfl rfl

/-- The denominator recurrence. -/
theorem cfConv_dens_step (n : ℕ) :
    (cfConv_ofFun h a b).dens (n + 2) =
      b (n + 1) * (cfConv_ofFun h a b).dens (n + 1) + a (n + 1) * (cfConv_ofFun h a b).dens n :=
  dens_recurrence (g := cfConv_ofFun h a b) (n := n) (gp := ⟨a (n + 1), b (n + 1)⟩) rfl rfl rfl

/-- The denominators do not depend on the integer part. -/
theorem cfConv_dens_eq (h' : K) (n : ℕ) :
    (cfConv_ofFun h a b).dens n = (cfConv_ofFun h' a b).dens n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · exact (cfConv_dens_zero h a b).trans (cfConv_dens_zero h' a b).symm
    · exact (cfConv_dens_one h a b).trans (cfConv_dens_one h' a b).symm
    · rw [cfConv_dens_step, cfConv_dens_step, ih (n + 1) (by omega), ih n (by omega)]

/-- The numerators are affine in the integer part: `A_n(h) = A_n(0) + h B_n`. -/
theorem cfConv_nums_eq (n : ℕ) :
    (cfConv_ofFun h a b).nums n =
      (cfConv_ofFun 0 a b).nums n + h * (cfConv_ofFun 0 a b).dens n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · rw [cfConv_nums_zero, cfConv_nums_zero, cfConv_dens_zero]; ring
    · rw [cfConv_nums_one, cfConv_nums_one, cfConv_dens_one]; ring
    · rw [cfConv_nums_step, cfConv_nums_step, cfConv_dens_step, ih (n + 1) (by omega),
        ih n (by omega)]
      ring

/-- The convergents with integer part `h` are `h` plus those with integer part `0`. -/
theorem cfConv_convs_eq (n : ℕ) (hD : (cfConv_ofFun 0 a b).dens n ≠ 0) :
    (cfConv_ofFun h a b).convs n = h + (cfConv_ofFun 0 a b).convs n := by
  change (cfConv_ofFun h a b).nums n / (cfConv_ofFun h a b).dens n =
    h + (cfConv_ofFun 0 a b).nums n / (cfConv_ofFun 0 a b).dens n
  rw [cfConv_nums_eq, cfConv_dens_eq h a b 0]
  field_simp
  ring

/-- The determinant formula `A_{m+1} B_m - B_{m+1} A_m = (-1)^m ∏_{k ≤ m} a_k`. -/
theorem cfConv_det (m : ℕ) :
    (cfConv_ofFun h a b).nums (m + 1) * (cfConv_ofFun h a b).dens m -
        (cfConv_ofFun h a b).dens (m + 1) * (cfConv_ofFun h a b).nums m =
      (-1) ^ m * ∏ k ∈ range (m + 1), a k := by
  induction m with
  | zero =>
    rw [cfConv_nums_one, cfConv_nums_zero, cfConv_dens_one, cfConv_dens_zero]
    simp
  | succ m ih =>
    rw [cfConv_nums_step, cfConv_dens_step, prod_range_succ]
    linear_combination (-a (m + 1)) * ih

/-- The continuants commute with field homomorphisms (numerators). -/
theorem cfConv_nums_map {L : Type*} [Field L] (f : K →+* L) (n : ℕ) :
    (cfConv_ofFun (f h) (fun k => f (a k)) (fun k => f (b k))).nums n =
      f ((cfConv_ofFun h a b).nums n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · rw [cfConv_nums_zero, cfConv_nums_zero]
    · rw [cfConv_nums_one, cfConv_nums_one, map_add, map_mul]
    · rw [cfConv_nums_step, cfConv_nums_step, ih (n + 1) (by omega), ih n (by omega)]
      simp only [map_add, map_mul]

/-- The continuants commute with field homomorphisms (denominators). -/
theorem cfConv_dens_map {L : Type*} [Field L] (f : K →+* L) (n : ℕ) :
    (cfConv_ofFun (f h) (fun k => f (a k)) (fun k => f (b k))).dens n =
      f ((cfConv_ofFun h a b).dens n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · rw [cfConv_dens_zero, cfConv_dens_zero, map_one]
    · rw [cfConv_dens_one, cfConv_dens_one]
    · rw [cfConv_dens_step, cfConv_dens_step, ih (n + 1) (by omega), ih n (by omega)]
      simp only [map_add, map_mul]

/-- The convergents commute with field homomorphisms. -/
theorem cfConv_convs_map {L : Type*} [Field L] (f : K →+* L) (n : ℕ) :
    (cfConv_ofFun (f h) (fun k => f (a k)) (fun k => f (b k))).convs n =
      f ((cfConv_ofFun h a b).convs n) := by
  change _ / _ = f (_ / _)
  rw [cfConv_nums_map, cfConv_dens_map, map_div₀]

variable {h a b}

/-- **Pincherle invariants**: a backward solution `w` pairs with the continuants. -/
theorem cfConv_invariant {w : ℕ → K} (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2))
    (m : ℕ) :
    (cfConv_ofFun h a b).nums (m + 1) * w (m + 1) +
        a (m + 1) * (cfConv_ofFun h a b).nums m * w (m + 2) = a 0 * w 1 + h * w 0 ∧
      (cfConv_ofFun h a b).dens (m + 1) * w (m + 1) +
        a (m + 1) * (cfConv_ofFun h a b).dens m * w (m + 2) = w 0 := by
  induction m with
  | zero =>
    rw [cfConv_nums_one, cfConv_nums_zero, cfConv_dens_one, cfConv_dens_zero, hw 0]
    constructor <;> ring
  | succ m ih =>
    rw [cfConv_nums_step, cfConv_dens_step]
    constructor
    · rw [← ih.1, hw (m + 1)]; ring
    · rw [← ih.2, hw (m + 1)]; ring

/-- The exact error of the `(m+1)`-st convergent:
`h + a₀w₁/w₀ - A_{m+1}/B_{m+1} = (-1)^{m+1} (∏_{k ≤ m+1} a_k) w_{m+2} / (w₀ B_{m+1})`. -/
theorem cfConv_error {w : ℕ → K} (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2))
    (hw0 : w 0 ≠ 0) (m : ℕ) (hD : (cfConv_ofFun h a b).dens (m + 1) ≠ 0) :
    h + a 0 * w 1 / w 0 - (cfConv_ofFun h a b).convs (m + 1) =
      (-1) ^ (m + 1) * (∏ k ∈ range (m + 2), a k) * w (m + 2) /
        (w 0 * (cfConv_ofFun h a b).dens (m + 1)) := by
  obtain ⟨h1, h2⟩ := cfConv_invariant (h := h) hw m
  have hdet := cfConv_det h a b m
  change h + a 0 * w 1 / w 0 - (cfConv_ofFun h a b).nums (m + 1) /
    (cfConv_ofFun h a b).dens (m + 1) = _
  rw [prod_range_succ, pow_succ]
  field_simp
  linear_combination (-(cfConv_ofFun h a b).dens (m + 1)) * h1 +
    (cfConv_ofFun h a b).nums (m + 1) * h2 - (a (m + 1) * w (m + 2)) * hdet

/-- The forward solution `G_n = (-1)^n (∏_{k ≤ n} a_k) w_{n+1}` attached to a backward
solution `w`. -/
def cfConv_G (a w : ℕ → K) (n : ℕ) : K := (-1) ^ n * (∏ k ∈ range (n + 1), a k) * w (n + 1)

/-- The Casoratian of the denominators with `G`: `B_{n+1} G_n - B_n G_{n+1}` equals
`(-1)^n (∏_{k ≤ n} a_k) w₀`. -/
theorem cfConv_casoratian {w : ℕ → K} (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2))
    (n : ℕ) :
    (cfConv_ofFun h a b).dens (n + 1) * cfConv_G a w n -
        (cfConv_ofFun h a b).dens n * cfConv_G a w (n + 1) =
      (-1) ^ n * (∏ k ∈ range (n + 1), a k) * w 0 := by
  have h2 := (cfConv_invariant (h := h) hw n).2
  simp only [cfConv_G]
  rw [prod_range_succ _ (n + 1), pow_succ]
  linear_combination ((-1) ^ n * ∏ k ∈ range (n + 1), a k) * h2

/-- The quotients `T_i = (-1)^{N+i} (∏_{k ≤ N+i} a_k) w₀ / (G_{N+i} G_{N+i+1})` of the
telescoped expansion of `B_n / G_n` (see `cfConv_dens_div_eq`). -/
def cfConv_T (a w : ℕ → K) (N i : ℕ) : K :=
  (-1) ^ (N + i) * (∏ k ∈ range (N + i + 1), a k) * w 0 /
    (cfConv_G a w (N + i) * cfConv_G a w (N + i + 1))

/-- Nonvanishing under the stated hypotheses: `cfConv_G a w n ≠ 0`. -/
theorem cfConv_G_ne_zero {w : ℕ → K} (ha : ∀ k, a k ≠ 0) {n : ℕ} (hw : w (n + 1) ≠ 0) :
    cfConv_G a w n ≠ 0 :=
  mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (prod_ne_zero_iff.mpr fun k _ => ha k)) hw

/-- Telescoping: `B_{N+j}/G_{N+j} = B_N/G_N + ∑_{i<j} T_i`. -/
theorem cfConv_dens_div_eq {w : ℕ → K}
    (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2)) (ha : ∀ k, a k ≠ 0)
    {N : ℕ} (hwN : ∀ k ≥ N, w k ≠ 0) (j : ℕ) :
    (cfConv_ofFun h a b).dens (N + j) / cfConv_G a w (N + j) =
      (cfConv_ofFun h a b).dens N / cfConv_G a w N + ∑ i ∈ range j, cfConv_T a w N i := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hc := cfConv_casoratian (h := h) hw (N + j)
    have g1 := cfConv_G_ne_zero (w := w) ha (n := N + j) (hwN _ (by omega))
    have g2 := cfConv_G_ne_zero (w := w) ha (n := N + j + 1) (hwN _ (by omega))
    have key : (cfConv_ofFun h a b).dens (N + j + 1) / cfConv_G a w (N + j + 1) -
        (cfConv_ofFun h a b).dens (N + j) / cfConv_G a w (N + j) = cfConv_T a w N j := by
      rw [cfConv_T, ← hc]
      field_simp
    rw [sum_range_succ, show N + (j + 1) = N + j + 1 by ring]
    linear_combination ih + key

/-- Consecutive quotients: `T_{i+1} = T_i · (-w_k/(a_{k+1} w_{k+2}))` with `k = N+i+1`. -/
theorem cfConv_T_succ {w : ℕ → K} (ha : ∀ k, a k ≠ 0) {N : ℕ} (hwN : ∀ k ≥ N, w k ≠ 0)
    (i : ℕ) :
    cfConv_T a w N (i + 1) =
      cfConv_T a w N i * (-(w (N + i + 1) / (a (N + i + 2) * w (N + i + 3)))) := by
  have hP : ∀ n, ∏ k ∈ range n, a k ≠ 0 := fun n => prod_ne_zero_iff.mpr fun k _ => ha k
  simp only [cfConv_T, cfConv_G]
  rw [show N + (i + 1) = N + i + 1 by ring, show N + i + 1 + 1 = N + i + 2 by ring,
    show N + i + 2 + 1 = N + i + 3 by ring]
  rw [prod_range_succ _ (N + i + 2), prod_range_succ _ (N + i + 1)]
  have := ha (N + i + 1); have := ha (N + i + 2)
  have := hP (N + i + 1)
  have := hwN (N + i + 1) (by omega); have := hwN (N + i + 2) (by omega)
  have := hwN (N + i + 3) (by omega)
  have s1 : ((-1 : K) ^ (N + i)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  rw [pow_succ, pow_succ, pow_succ]
  field_simp

/-- Nonvanishing under the stated hypotheses: `cfConv_T a w N i ≠ 0`. -/
theorem cfConv_T_ne_zero {w : ℕ → K} (hw0 : w 0 ≠ 0) (ha : ∀ k, a k ≠ 0) {N : ℕ}
    (hwN : ∀ k ≥ N, w k ≠ 0) (i : ℕ) : cfConv_T a w N i ≠ 0 :=
  div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (prod_ne_zero_iff.mpr fun k _ => ha k)) hw0)
    (mul_ne_zero (cfConv_G_ne_zero ha (hwN _ (by omega)))
      (cfConv_G_ne_zero ha (hwN _ (by omega))))

end Algebra

section Normed

variable [NormedField K] {h : K} {a b w : ℕ → K}

/-- **Pincherle's theorem** (sufficiency): if `w` is a backward solution with `w₀ ≠ 0` whose
forward companion `(∏_{k ≤ m} a_k) w_{m+1}` is negligible against the denominators `B_m`, the
convergents tend to `h + a₀ w₁ / w₀`. -/
theorem cfConv_tendsto_of_minimal (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2))
    (hw0 : w 0 ≠ 0) (hD : ∀ᶠ m in atTop, (cfConv_ofFun h a b).dens m ≠ 0)
    (hmin : Tendsto (fun m => (∏ k ∈ range (m + 1), a k) * w (m + 1) /
      (cfConv_ofFun h a b).dens m) atTop (𝓝 0)) :
    Tendsto (cfConv_ofFun h a b).convs atTop (𝓝 (h + a 0 * w 1 / w 0)) := by
  show Tendsto (fun n => (cfConv_ofFun h a b).convs n) atTop _
  rw [← tendsto_add_atTop_iff_nat 1, tendsto_iff_norm_sub_tendsto_zero]
  have hmin' := (hmin.comp (tendsto_add_atTop_nat 1)).norm.div_const ‖w 0‖
  rw [norm_zero, zero_div] at hmin'
  refine hmin'.congr' ?_
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hD] with m hm
  rw [norm_sub_rev, cfConv_error hw hw0 m hm]
  simp only [Function.comp_apply, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul]
  ring

/-- Partial sums of a sequence whose terms eventually grow by a factor `q > 2` tend to infinity
in norm. -/
theorem cfConv_norm_sum_tendsto {T : ℕ → K} {q : ℝ} (hq : 2 < q) {N : ℕ} (hTN : T N ≠ 0)
    (hT : ∀ n ≥ N, q * ‖T n‖ ≤ ‖T (n + 1)‖) :
    Tendsto (fun n => ‖∑ k ∈ range n, T k‖) atTop atTop := by
  set C := ∑ k ∈ range N, ‖T k‖
  have hq1 : 0 < q - 1 := by linarith
  -- the tail sums are dominated by the last term
  have hR : ∀ n, N ≤ n → ∑ k ∈ Ico N n, ‖T k‖ ≤ ‖T n‖ / (q - 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp; positivity
    | succ n hn ih =>
      rw [sum_Ico_succ_top hn]
      have := hT n hn
      rw [le_div_iff₀ hq1] at ih ⊢
      nlinarith [norm_nonneg (T n)]
  -- geometric growth of the terms
  have hgrow : ∀ j, q ^ j * ‖T N‖ ≤ ‖T (N + j)‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := hT (N + j) (by omega)
      rw [pow_succ, ← add_assoc]
      nlinarith [norm_nonneg (T N), pow_pos (by linarith : (0 : ℝ) < q) j]
  have hlow : ∀ j, (1 - 1 / (q - 1)) * ‖T (N + j)‖ - C ≤ ‖∑ k ∈ range (N + j + 1), T k‖ := by
    intro j
    have hsplit : ∑ k ∈ range (N + j + 1), T k =
        T (N + j) + (∑ k ∈ range N, T k + ∑ k ∈ Ico N (N + j), T k) := by
      rw [sum_range_succ, sum_range_add_sum_Ico _ (by omega)]; ring
    have h1 : ‖∑ k ∈ range N, T k + ∑ k ∈ Ico N (N + j), T k‖ ≤
        C + ‖T (N + j)‖ / (q - 1) :=
      (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _)
        ((norm_sum_le _ _).trans (hR (N + j) (by omega))))
    have h2 := norm_sub_norm_le (T (N + j))
      (-(∑ k ∈ range N, T k + ∑ k ∈ Ico N (N + j), T k))
    rw [sub_neg_eq_add, norm_neg] at h2
    rw [hsplit]
    have : ‖T (N + j)‖ / (q - 1) = 1 / (q - 1) * ‖T (N + j)‖ := by ring
    linarith
  have hc : 0 < 1 - 1 / (q - 1) := by
    rw [sub_pos, div_lt_one hq1]; linarith
  have hgeom : Tendsto (fun j : ℕ => q ^ j * ‖T N‖) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by linarith)).atTop_mul_const (norm_pos_iff.mpr hTN)
  have hj : Tendsto (fun j : ℕ => ‖∑ k ∈ range (N + j + 1), T k‖) atTop atTop := by
    refine tendsto_atTop_mono hlow ?_
    refine tendsto_atTop_add_const_right _ _ ?_
    exact (tendsto_atTop_mono hgrow hgeom).const_mul_atTop hc
  rw [← tendsto_add_atTop_iff_nat (N + 1)]
  refine hj.congr fun j => ?_
  congr 2
  ring_nf

/-- **Dominance criterion.** If the partial sums of the `T_i` tend to infinity in norm, the
denominators dominate the forward companion of `w` and the convergents tend to
`h + a₀ w₁ / w₀`. -/
theorem cfConv_tendsto_of_sum (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2))
    (hw0 : w 0 ≠ 0) (ha : ∀ k, a k ≠ 0) {N : ℕ} (hwN : ∀ k ≥ N, w k ≠ 0)
    (hsum : Tendsto (fun j => ‖∑ i ∈ range j, cfConv_T a w N i‖) atTop atTop) :
    Tendsto (cfConv_ofFun h a b).convs atTop (𝓝 (h + a 0 * w 1 / w 0)) := by
  have hdiv : Tendsto (fun j => ‖(cfConv_ofFun h a b).dens (N + j) / cfConv_G a w (N + j)‖)
      atTop atTop := by
    have hc := tendsto_atTop_add_const_left atTop
      (-‖(cfConv_ofFun h a b).dens N / cfConv_G a w N‖) hsum
    refine tendsto_atTop_mono (fun j => ?_) hc
    rw [cfConv_dens_div_eq (h := h) hw ha hwN j]
    have := norm_sub_norm_le
      ((cfConv_ofFun h a b).dens N / cfConv_G a w N + ∑ i ∈ range j, cfConv_T a w N i)
      ((cfConv_ofFun h a b).dens N / cfConv_G a w N)
    rw [add_sub_cancel_left] at this
    have := norm_sub_norm_le (∑ i ∈ range j, cfConv_T a w N i)
      (-((cfConv_ofFun h a b).dens N / cfConv_G a w N +
        ∑ i ∈ range j, cfConv_T a w N i))
    rw [sub_neg_eq_add, norm_neg, add_comm (_ / _), ← add_assoc] at this
    have := norm_add_le ((cfConv_ofFun h a b).dens N / cfConv_G a w N)
      (∑ i ∈ range j, cfConv_T a w N i)
    have := norm_sub_norm_le (∑ i ∈ range j, cfConv_T a w N i)
      (-((cfConv_ofFun h a b).dens N / cfConv_G a w N))
    rw [sub_neg_eq_add, norm_neg, add_comm] at this
    linarith
  have hdiv' : Tendsto (fun m => ‖(cfConv_ofFun h a b).dens m / cfConv_G a w m‖) atTop atTop := by
    rw [← tendsto_add_atTop_iff_nat N]
    exact hdiv.congr fun j => by rw [add_comm]
  have hDev : ∀ᶠ m in atTop, (cfConv_ofFun h a b).dens m ≠ 0 := by
    filter_upwards [hdiv'.eventually_gt_atTop 0] with m hm hD
    rw [hD, zero_div, norm_zero] at hm
    exact lt_irrefl _ hm
  refine cfConv_tendsto_of_minimal hw hw0 hDev ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (hdiv'.inv_tendsto_atTop).congr' ?_
  filter_upwards [eventually_ge_atTop N] with m hm
  simp only [cfConv_G, Pi.inv_apply, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul]
  rw [inv_div]

/-- **Ratio criterion.** Let `w` be a backward solution with `w₀ ≠ 0`, all `a_k ≠ 0`, and
`w_k ≠ 0` for `k ≥ N`. If `q ‖a_{k+1} w_{k+2}‖ ≤ ‖w_k‖` for `k ≥ N` with `q > 2`, then the
convergents of `h + a₀/(b₀ + a₁/(b₁ + ⋯))` tend to `h + a₀ w₁ / w₀`. -/
theorem cfConv_tendsto_of_ratio (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2))
    (hw0 : w 0 ≠ 0) (ha : ∀ k, a k ≠ 0) {N : ℕ} (hwN : ∀ k ≥ N, w k ≠ 0) {q : ℝ} (hq : 2 < q)
    (hrat : ∀ k ≥ N, q * ‖a (k + 1) * w (k + 2)‖ ≤ ‖w k‖) :
    Tendsto (cfConv_ofFun h a b).convs atTop (𝓝 (h + a 0 * w 1 / w 0)) := by
  refine cfConv_tendsto_of_sum hw hw0 ha hwN (cfConv_norm_sum_tendsto hq
    (cfConv_T_ne_zero hw0 ha hwN 0) fun i _ => ?_)
  rw [cfConv_T_succ ha hwN i, norm_mul, norm_neg, norm_div, mul_comm q]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hpos : 0 < ‖a (N + i + 2) * w (N + i + 3)‖ :=
    norm_pos_iff.mpr (mul_ne_zero (ha _) (hwN _ (by omega)))
  rw [le_div_iff₀ hpos]
  simpa [show N + i + 1 + 1 = N + i + 2 by ring, show N + i + 1 + 2 = N + i + 3 by ring]
    using hrat (N + i + 1) (by omega)

/-- Under the hypotheses of the ratio criterion `cfConv_tendsto_of_ratio`, the denominators
`B_m` are eventually nonzero. -/
theorem cfConv_dens_eventually_ne_of_ratio
    (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2))
    (hw0 : w 0 ≠ 0) (ha : ∀ k, a k ≠ 0) {N : ℕ} (hwN : ∀ k ≥ N, w k ≠ 0) {q : ℝ} (hq : 2 < q)
    (hrat : ∀ k ≥ N, q * ‖a (k + 1) * w (k + 2)‖ ≤ ‖w k‖) :
    ∀ᶠ m in atTop, (cfConv_ofFun h a b).dens m ≠ 0 := by
  have hsum : Tendsto (fun j => ‖∑ i ∈ range j, cfConv_T a w N i‖) atTop atTop := by
    refine cfConv_norm_sum_tendsto hq (cfConv_T_ne_zero hw0 ha hwN 0) fun i _ => ?_
    rw [cfConv_T_succ ha hwN i, norm_mul, norm_neg, norm_div, mul_comm q]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hpos : 0 < ‖a (N + i + 2) * w (N + i + 3)‖ :=
      norm_pos_iff.mpr (mul_ne_zero (ha _) (hwN _ (by omega)))
    rw [le_div_iff₀ hpos]
    simpa [show N + i + 1 + 1 = N + i + 2 by ring, show N + i + 1 + 2 = N + i + 3 by ring]
      using hrat (N + i + 1) (by omega)
  have hdiv : Tendsto (fun j => ‖(cfConv_ofFun h a b).dens (N + j) / cfConv_G a w (N + j)‖)
      atTop atTop := by
    have hc := tendsto_atTop_add_const_left atTop
      (-‖(cfConv_ofFun h a b).dens N / cfConv_G a w N‖) hsum
    refine tendsto_atTop_mono (fun j => ?_) hc
    rw [cfConv_dens_div_eq (h := h) hw ha hwN j]
    have := norm_sub_norm_le
      ((cfConv_ofFun h a b).dens N / cfConv_G a w N + ∑ i ∈ range j, cfConv_T a w N i)
      ((cfConv_ofFun h a b).dens N / cfConv_G a w N)
    rw [add_sub_cancel_left] at this
    have := norm_add_le ((cfConv_ofFun h a b).dens N / cfConv_G a w N)
      (∑ i ∈ range j, cfConv_T a w N i)
    have := norm_sub_norm_le (∑ i ∈ range j, cfConv_T a w N i)
      (-((cfConv_ofFun h a b).dens N / cfConv_G a w N))
    rw [sub_neg_eq_add, norm_neg, add_comm] at this
    linarith
  have hdiv' : Tendsto (fun m => ‖(cfConv_ofFun h a b).dens m / cfConv_G a w m‖) atTop atTop := by
    rw [← tendsto_add_atTop_iff_nat N]
    exact hdiv.congr fun j => by rw [add_comm]
  filter_upwards [hdiv'.eventually_gt_atTop 0] with m hm hD
  rw [hD, zero_div, norm_zero] at hm
  exact lt_irrefl _ hm

end Normed

section Real

variable {h : ℝ} {a b w : ℕ → ℝ}

/-- Partial sums of real terms with `T_{n+1}/T_n ≥ 1` (hence of one sign and non-decreasing
modulus) tend to infinity in absolute value. -/
theorem cfConv_abs_sum_tendsto_real {T : ℕ → ℝ} (hT0 : T 0 ≠ 0)
    (hT : ∀ n, 1 ≤ T (n + 1) / T n) :
    Tendsto (fun n => |∑ k ∈ range n, T k|) atTop atTop := by
  have hsq : 0 < T 0 ^ 2 := by positivity
  have hmono : ∀ n, T 0 ^ 2 ≤ T 0 * T n := by
    intro n
    induction n with
    | zero => rw [sq]
    | succ n ih =>
      have hn : T n ≠ 0 := by intro h0; rw [h0, mul_zero] at ih; linarith
      have hr := hT n
      have e : T (n + 1) = T (n + 1) / T n * T n := by field_simp
      rw [e]
      have : 0 < T 0 * T n := by linarith
      nlinarith
  have hlow : ∀ n, n * |T 0| ≤ |∑ k ∈ range n, T k| := by
    intro n
    have h1 : (n : ℝ) * T 0 ^ 2 ≤ T 0 * ∑ k ∈ range n, T k := by
      rw [mul_sum]
      have := sum_le_sum (s := range n) fun k _ => hmono k
      simpa [mul_comm] using this
    have h2 : T 0 * ∑ k ∈ range n, T k ≤ |T 0| * |∑ k ∈ range n, T k| := by
      rw [← abs_mul]; exact le_abs_self _
    have h3 : (n : ℝ) * T 0 ^ 2 = |T 0| * (n * |T 0|) := by rw [← sq_abs]; ring
    have hpos : 0 < |T 0| := abs_pos.mpr hT0
    nlinarith
  refine tendsto_atTop_mono hlow ?_
  exact tendsto_natCast_atTop_atTop.atTop_mul_const (abs_pos.mpr hT0)

/-- **Real ratio criterion** (negative elements, Worpitzky type). Let `w` be a real backward
solution with `w₀ ≠ 0`, all `a_k ≠ 0` and `w_k ≠ 0` for `k ≥ N`. If for `k ≥ N` the numbers
`w_k` and `a_{k+1} w_{k+2}` have opposite signs and `|a_{k+1} w_{k+2}| ≤ |w_k|`, then the
convergents tend to `h + a₀ w₁ / w₀`. -/
theorem cfConv_tendsto_of_ratio_real (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2))
    (hw0 : w 0 ≠ 0) (ha : ∀ k, a k ≠ 0) {N : ℕ} (hwN : ∀ k ≥ N, w k ≠ 0)
    (hsign : ∀ k ≥ N, w k * (a (k + 1) * w (k + 2)) < 0)
    (hrat : ∀ k ≥ N, |a (k + 1) * w (k + 2)| ≤ |w k|) :
    Tendsto (cfConv_ofFun h a b).convs atTop (𝓝 (h + a 0 * w 1 / w 0)) := by
  refine cfConv_tendsto_of_sum hw hw0 ha hwN ?_
  simp only [Real.norm_eq_abs]
  refine cfConv_abs_sum_tendsto_real (cfConv_T_ne_zero hw0 ha hwN 0) fun i => ?_
  have hTi := cfConv_T_ne_zero hw0 ha hwN i
  rw [cfConv_T_succ ha hwN i, mul_div_cancel_left₀ _ hTi]
  have hs := hsign (N + i + 1) (by omega)
  have hr := hrat (N + i + 1) (by omega)
  simp only [show N + i + 1 + 1 = N + i + 2 by ring, show N + i + 1 + 2 = N + i + 3 by ring]
    at hs hr
  set u := w (N + i + 1)
  set v := a (N + i + 2) * w (N + i + 3)
  have hv : v ≠ 0 := by intro h0; rw [h0, mul_zero] at hs; exact lt_irrefl _ hs
  have hlt : u / v < 0 := by
    have : u / v = u * v / v ^ 2 := by field_simp
    rw [this]; exact div_neg_of_neg_of_pos hs (by positivity)
  rw [show -(u / v) = |u| / |v| by rw [← abs_div, abs_of_neg hlt],
    le_div_iff₀ (abs_pos.mpr hv), one_mul]
  exact hr

/-- Partial sums of real terms with `T_{n+1}/T_n ≤ -r`, `r > 1` (alternating signs and
geometrically growing moduli) tend to infinity in absolute value. -/
theorem cfConv_abs_sum_tendsto_alt {T : ℕ → ℝ} {r : ℝ} (hr : 1 < r) (hT0 : T 0 ≠ 0)
    (hT : ∀ n, T (n + 1) / T n ≤ -r) :
    Tendsto (fun n => |∑ k ∈ range n, T k|) atTop atTop := by
  have hr0 : 0 < r := by linarith
  have hne : ∀ n, T n ≠ 0 := by
    intro n
    induction n with
    | zero => exact hT0
    | succ n ih =>
      intro h0
      have := hT n
      rw [h0, zero_div] at this
      linarith
  have hgrow : ∀ n, r * |T n| ≤ |T (n + 1)| := by
    intro n
    have hq := hT n
    have e : T (n + 1) = T (n + 1) / T n * T n := by field_simp [hne n]
    rw [e, abs_mul, abs_of_neg (by linarith : T (n + 1) / T n < 0)]
    exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  have hpow : ∀ n, r ^ n * |T 0| ≤ |T n| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_comm (r ^ n) r, mul_assoc]
      exact (mul_le_mul_of_nonneg_left ih hr0.le).trans (hgrow n)
  -- `u_n = S_{n+1} / T_n` stays in `[1 - 1/r, 1]`
  set u : ℕ → ℝ := fun n => (∑ k ∈ range (n + 1), T k) / T n with hu
  have hrec : ∀ n, u (n + 1) = 1 + T n / T (n + 1) * u n := by
    intro n
    simp only [u]
    rw [sum_range_succ _ (n + 1)]
    field_simp [hne n, hne (n + 1)]
    ring
  have hρ : ∀ n, -(1 / r) ≤ T n / T (n + 1) ∧ T n / T (n + 1) < 0 := by
    intro n
    have hq := hT n
    have hqn : T (n + 1) / T n < 0 := by linarith
    have e : T n / T (n + 1) = (T (n + 1) / T n)⁻¹ := by
      rw [inv_div]
    rw [e]
    refine ⟨?_, inv_lt_zero.mpr hqn⟩
    rw [neg_le, ← inv_neg, one_div]
    have : r ≤ -(T (n + 1) / T n) := by linarith
    exact inv_anti₀ hr0 this
  have hub : ∀ n, 1 - 1 / r ≤ u n ∧ u n ≤ 1 := by
    intro n
    induction n with
    | zero =>
      simp only [u, zero_add, range_one, sum_singleton, div_self (hne 0)]
      constructor
      · have : 0 < 1 / r := by positivity
        linarith
      · exact le_rfl
    | succ n ih =>
      rw [hrec n]
      obtain ⟨h1, h2⟩ := hρ n
      have hu0 : 0 ≤ u n := le_trans (by
        have : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr
        linarith) ih.1
      constructor
      · nlinarith [ih.2]
      · nlinarith
  have hc : 0 < 1 - 1 / r := by
    have : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr
    linarith
  have hlow : ∀ n, (1 - 1 / r) * |T 0| * r ^ n ≤ |∑ k ∈ range (n + 1), T k| := by
    intro n
    have e : ∑ k ∈ range (n + 1), T k = u n * T n := by
      simp only [u]; field_simp [hne n]
    rw [e, abs_mul, abs_of_nonneg (le_trans hc.le (hub n).1)]
    calc (1 - 1 / r) * |T 0| * r ^ n = (1 - 1 / r) * (r ^ n * |T 0|) := by ring
      _ ≤ u n * |T n| := mul_le_mul (hub n).1 (hpow n) (by positivity)
          (le_trans hc.le (hub n).1)
  rw [← tendsto_add_atTop_iff_nat 1]
  refine tendsto_atTop_mono hlow ?_
  exact (tendsto_pow_atTop_atTop_of_one_lt hr).const_mul_atTop (by positivity)

/-- **Real ratio criterion, positive elements.** Let `w` be a real backward solution with
`w₀ ≠ 0`, all `a_k ≠ 0` and `w_k ≠ 0` for `k ≥ N`. If for `k ≥ N` the numbers `w_k` and
`a_{k+1} w_{k+2}` have the same sign and `r |a_{k+1} w_{k+2}| ≤ |w_k|` with `r > 1`, then the
convergents tend to `h + a₀ w₁ / w₀`. -/
theorem cfConv_tendsto_of_ratio_pos (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2))
    (hw0 : w 0 ≠ 0) (ha : ∀ k, a k ≠ 0) {N : ℕ} (hwN : ∀ k ≥ N, w k ≠ 0)
    (hsign : ∀ k ≥ N, 0 < w k * (a (k + 1) * w (k + 2))) {r : ℝ} (hr : 1 < r)
    (hrat : ∀ k ≥ N, r * |a (k + 1) * w (k + 2)| ≤ |w k|) :
    Tendsto (cfConv_ofFun h a b).convs atTop (𝓝 (h + a 0 * w 1 / w 0)) := by
  refine cfConv_tendsto_of_sum hw hw0 ha hwN ?_
  simp only [Real.norm_eq_abs]
  refine cfConv_abs_sum_tendsto_alt hr (cfConv_T_ne_zero hw0 ha hwN 0) fun i => ?_
  have hTi := cfConv_T_ne_zero hw0 ha hwN i
  rw [cfConv_T_succ ha hwN i, mul_div_cancel_left₀ _ hTi]
  have hs := hsign (N + i + 1) (by omega)
  have hr' := hrat (N + i + 1) (by omega)
  simp only [show N + i + 1 + 1 = N + i + 2 by ring, show N + i + 1 + 2 = N + i + 3 by ring]
    at hs hr'
  set u := w (N + i + 1)
  set v := a (N + i + 2) * w (N + i + 3)
  have hv : v ≠ 0 := by intro h0; rw [h0, mul_zero] at hs; exact lt_irrefl _ hs
  have hgt : 0 < u / v := by
    have : u / v = u * v / v ^ 2 := by field_simp
    rw [this]; exact div_pos hs (by positivity)
  rw [show u / v = |u| / |v| by rw [← abs_div, abs_of_pos hgt], neg_le_neg_iff,
    le_div_iff₀ (abs_pos.mpr hv)]
  exact hr'

/-- The denominators are positive when all elements are positive. -/
theorem cfConv_dens_pos (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k) (m : ℕ) :
    0 < (cfConv_ofFun h a b).dens m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · rw [cfConv_dens_zero]; norm_num
    · rw [cfConv_dens_one]; exact hb 0
    · rw [cfConv_dens_step]
      have := ih (m + 1) (by omega)
      have := ih m (by omega)
      have := ha (m + 1)
      have := hb (m + 1)
      positivity

/-- **Bracketing.** With positive elements and a positive backward solution, the convergents
`A_{2n}/B_{2n}` (`n ≥ 1`) lie strictly below `h + a₀w₁/w₀`. -/
theorem cfConv_convs_lt_of_pos (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k) (hwpos : ∀ k, 0 < w k)
    (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2)) {n : ℕ} (hn : 1 ≤ n) :
    (cfConv_ofFun h a b).convs (2 * n) < h + a 0 * w 1 / w 0 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
  rw [hm]
  have he := cfConv_error (h := h) hw (hwpos 0).ne' m (cfConv_dens_pos ha hb (m + 1)).ne'
  have hodd : Odd m := by
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | hk
    · omega
    · exact hk
  have hsgn : ((-1 : ℝ) ^ (m + 1)) = 1 := (hodd.add_one).neg_one_pow
  have hP : 0 < ∏ k ∈ range (m + 2), a k := prod_pos fun k _ => ha k
  have hpos : 0 < (-1) ^ (m + 1) * (∏ k ∈ range (m + 2), a k) * w (m + 2) /
      (w 0 * (cfConv_ofFun h a b).dens (m + 1)) := by
    rw [hsgn, one_mul]
    exact div_pos (mul_pos hP (hwpos _)) (mul_pos (hwpos 0) (cfConv_dens_pos ha hb _))
  linarith

/-- **Bracketing.** With positive elements and a positive backward solution, the convergents
`A_{2n+1}/B_{2n+1}` lie strictly above `h + a₀w₁/w₀`. -/
theorem cfConv_lt_convs_of_pos (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k) (hwpos : ∀ k, 0 < w k)
    (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2)) (n : ℕ) :
    h + a 0 * w 1 / w 0 < (cfConv_ofFun h a b).convs (2 * n + 1) := by
  have he := cfConv_error (h := h) hw (hwpos 0).ne' (2 * n) (cfConv_dens_pos ha hb _).ne'
  have hsgn : ((-1 : ℝ) ^ (2 * n + 1)) = -1 := by rw [pow_succ, pow_mul]; norm_num
  have hP : 0 < ∏ k ∈ range (2 * n + 2), a k := prod_pos fun k _ => ha k
  have hpos : 0 < (∏ k ∈ range (2 * n + 2), a k) * w (2 * n + 2) /
      (w 0 * (cfConv_ofFun h a b).dens (2 * n + 1)) :=
    div_pos (mul_pos hP (hwpos _)) (mul_pos (hwpos 0) (cfConv_dens_pos ha hb _))
  rw [hsgn, neg_one_mul, neg_mul, neg_div] at he
  linarith

/-- **Convergence of a positive S-fraction with linearly bounded elements.** Let `b_k = 1`,
`a_k > 0` with `a_k ≤ C (k + 1)`, and let `w` be a positive backward solution. Then the
convergents of `h + a₀/(1 + a₁/(1 + ⋯))` tend to `h + a₀ w₁ / w₀`. (The differences of
consecutive convergents decay like `1/(1 + ∑ 1/a_k)`, and the value is bracketed by them.) -/
theorem cfConv_tendsto_of_pos_linear (ha : ∀ k, 0 < a k) (hwpos : ∀ k, 0 < w k)
    (hw : ∀ k, w k = 1 * w (k + 1) + a (k + 1) * w (k + 2)) {C : ℝ}
    (hC : ∀ k, a k ≤ C * (k + 1)) :
    Tendsto (cfConv_ofFun h a (fun _ => 1)).convs atTop (𝓝 (h + a 0 * w 1 / w 0)) := by
  set g := cfConv_ofFun h a (fun _ => (1 : ℝ)) with hg
  have hb : ∀ k, (0 : ℝ) < (fun _ : ℕ => (1 : ℝ)) k := fun _ => one_pos
  have hB : ∀ m, 0 < g.dens m := cfConv_dens_pos ha hb
  have hstepB : ∀ m, g.dens (m + 1 + 1) = g.dens (m + 1) + a (m + 1) * g.dens m := by
    intro m
    have := cfConv_dens_step h a (fun _ => (1 : ℝ)) m
    simpa using this
  have hBmono : ∀ m, g.dens m ≤ g.dens (m + 1) := by
    intro m
    rcases m with _ | m
    · rw [cfConv_dens_one, cfConv_dens_zero]
    · rw [hstepB m]
      have := ha (m + 1)
      have := hB m
      nlinarith
  set D : ℕ → ℝ := fun m => (∏ k ∈ range (m + 1), a k) / (g.dens m * g.dens (m + 1)) with hD
  have hDpos : ∀ m, 0 < D m := fun m =>
    div_pos (prod_pos fun k _ => ha k) (mul_pos (hB m) (hB (m + 1)))
  have hdiff : ∀ m, |g.convs (m + 1) - g.convs m| = D m := by
    intro m
    have hdet := cfConv_det h a (fun _ => (1 : ℝ)) m
    change |g.nums (m + 1) / g.dens (m + 1) - g.nums m / g.dens m| = _
    have hb0 := (hB m).ne'
    have hb1 := (hB (m + 1)).ne'
    have e : g.nums (m + 1) / g.dens (m + 1) - g.nums m / g.dens m = (-1) ^ m * D m := by
      simp only [D]
      field_simp
      linear_combination hdet
    rw [e, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos (hDpos m)]
  have hstep : ∀ m, D (m + 1) * (1 + 1 / a (m + 1)) ≤ D m := by
    intro m
    simp only [D]
    rw [prod_range_succ, hstepB m]
    have hP : 0 < ∏ k ∈ range (m + 1), a k := prod_pos fun k _ => ha k
    have hak := ha (m + 1)
    have hb0 := hB m
    have hb1 := hB (m + 1)
    have key : (∏ k ∈ range (m + 1), a k) * a (m + 1) /
        (g.dens (m + 1) * (g.dens (m + 1) + a (m + 1) * g.dens m)) * (1 + 1 / a (m + 1)) =
        (∏ k ∈ range (m + 1), a k) * (a (m + 1) + 1) /
        (g.dens (m + 1) * (g.dens (m + 1) + a (m + 1) * g.dens m)) := by
      field_simp
    rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left (hBmono m) (mul_pos hP hb1).le
    nlinarith
  have hprod : ∀ m, D m * ∏ k ∈ range m, (1 + 1 / a (k + 1)) ≤ D 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [prod_range_succ]
      have hp : 0 ≤ ∏ k ∈ range m, (1 + 1 / a (k + 1)) :=
        prod_nonneg fun k _ => by have := ha (k + 1); positivity
      calc D (m + 1) * ((∏ k ∈ range m, (1 + 1 / a (k + 1))) * (1 + 1 / a (m + 1)))
          = (D (m + 1) * (1 + 1 / a (m + 1))) * ∏ k ∈ range m, (1 + 1 / a (k + 1)) := by ring
        _ ≤ D m * ∏ k ∈ range m, (1 + 1 / a (k + 1)) := mul_le_mul_of_nonneg_right (hstep m) hp
        _ ≤ D 0 := ih
  have hprod_ge : ∀ m, 1 + ∑ k ∈ range m, 1 / a (k + 1) ≤ ∏ k ∈ range m, (1 + 1 / a (k + 1)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [prod_range_succ, sum_range_succ]
      have he : 0 ≤ 1 / a (m + 1) := by have := ha (m + 1); positivity
      have hs : 0 ≤ ∑ k ∈ range m, 1 / a (k + 1) :=
        sum_nonneg fun k _ => by have := ha (k + 1); positivity
      nlinarith
  have hC0 : 0 < C := by
    have h0 := hC 0
    have := ha 0
    simp only [Nat.cast_zero, zero_add, mul_one] at h0
    linarith
  have hsum : Tendsto (fun m => ∑ k ∈ range m, 1 / a (k + 1)) atTop atTop := by
    have hh := Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop
      (show (0 : ℝ) < 1 / (2 * C) by positivity)
    refine tendsto_atTop_mono (fun m => ?_) hh
    rw [mul_sum]
    refine sum_le_sum fun k _ => ?_
    have hk := hC (k + 1)
    have hk' : a (k + 1) ≤ 2 * C * (k + 1) := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      push_cast at hk
      nlinarith
    rw [div_mul_div_comm, one_mul]
    exact one_div_le_one_div_of_le (ha _) hk'
  have hD0 : Tendsto D atTop (𝓝 0) := by
    have hden : Tendsto (fun m => 1 + ∑ k ∈ range m, 1 / a (k + 1)) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 hsum
    have hlim : Tendsto (fun m => D 0 / (1 + ∑ k ∈ range m, 1 / a (k + 1))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    refine squeeze_zero (fun m => (hDpos m).le) (fun m => ?_) hlim
    have hs : 0 < 1 + ∑ k ∈ range m, 1 / a (k + 1) := by
      have : 0 ≤ ∑ k ∈ range m, 1 / a (k + 1) :=
        sum_nonneg fun k _ => by have := ha (k + 1); positivity
      linarith
    rw [le_div_iff₀ hs]
    exact (mul_le_mul_of_nonneg_left (hprod_ge m) (hDpos m).le).trans (hprod m)
  show Tendsto (fun n => g.convs n) atTop _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hD0
  filter_upwards [eventually_ge_atTop 2] with m hm
  rw [Real.norm_eq_abs]
  rcases Nat.even_or_odd' m with ⟨n, rfl | rfl⟩
  · have h1 := cfConv_convs_lt_of_pos (h := h) ha hb hwpos hw (n := n) (by omega)
    have h2 := cfConv_lt_convs_of_pos (h := h) ha hb hwpos hw n
    rw [← hdiff (2 * n), abs_of_neg (by linarith)]
    exact le_trans (by linarith) (le_abs_self _)
  · have h1 := cfConv_lt_convs_of_pos (h := h) ha hb hwpos hw n
    have h2 := cfConv_convs_lt_of_pos (h := h) ha hb hwpos hw (n := n + 1) (by omega)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring] at h2
    rw [← hdiff (2 * n + 1), abs_of_pos (by linarith), abs_sub_comm]
    exact le_trans (by linarith) (le_abs_self _)

end Real

section Finite

variable {K : Type*} [Field K] {h : K} {a b : ℕ → K}

/-- The Pincherle invariants for a solution of the recurrence up to index `m` only. -/
theorem cfConv_invariant_fin {w : ℕ → K} (m : ℕ)
    (hw : ∀ k ≤ m, w k = b k * w (k + 1) + a (k + 1) * w (k + 2)) :
    (cfConv_ofFun h a b).nums (m + 1) * w (m + 1) +
        a (m + 1) * (cfConv_ofFun h a b).nums m * w (m + 2) = a 0 * w 1 + h * w 0 ∧
      (cfConv_ofFun h a b).dens (m + 1) * w (m + 1) +
        a (m + 1) * (cfConv_ofFun h a b).dens m * w (m + 2) = w 0 := by
  induction m with
  | zero =>
    rw [cfConv_nums_one, cfConv_nums_zero, cfConv_dens_one, cfConv_dens_zero, hw 0 le_rfl]
    constructor <;> ring
  | succ m ih =>
    have ih := ih fun k hk => hw k (by omega)
    rw [cfConv_nums_step, cfConv_dens_step]
    have e := hw (m + 1) le_rfl
    constructor
    · rw [← ih.1, e]; ring
    · rw [← ih.2, e]; ring

/-- A finite backward solution with `w_{N+1} = 1`, `w_{N+2} = 0` computes the `(N+1)`-st
continuants: `B_{N+1} = w₀` and `A_{N+1} = a₀ w₁ + h w₀`. -/
theorem cfConv_continuants_of_back {w : ℕ → K} (N : ℕ)
    (hw : ∀ k ≤ N, w k = b k * w (k + 1) + a (k + 1) * w (k + 2))
    (h1 : w (N + 1) = 1) (h2 : w (N + 2) = 0) :
    (cfConv_ofFun h a b).dens (N + 1) = w 0 ∧
      (cfConv_ofFun h a b).nums (N + 1) = a 0 * w 1 + h * w 0 := by
  obtain ⟨e1, e2⟩ := cfConv_invariant_fin (h := h) N hw
  rw [h1, h2] at e1 e2
  constructor
  · linear_combination e2
  · linear_combination e1

/-- The backward recursion for the pairs `(w_{N+1-j}, w_{N+2-j})`. -/
def cfConv_back (a b : ℕ → K) (N : ℕ) : ℕ → K × K
  | 0 => (1, 0)
  | j + 1 => ((b (N - j)) * (cfConv_back a b N j).1 + a (N - j + 1) * (cfConv_back a b N j).2,
      (cfConv_back a b N j).1)

/-- The finite backward solution of the `N`-th truncation. -/
def cfConv_backW (a b : ℕ → K) (N k : ℕ) : K :=
  if k ≤ N + 1 then (cfConv_back a b N (N + 1 - k)).1 else 0

/-- Identity under the stated parameter and domain assumptions: `cfConv_backW a b N (N + 1) = 1`. -/
theorem cfConv_backW_succ (N : ℕ) : cfConv_backW a b N (N + 1) = 1 := by
  simp [cfConv_backW, cfConv_back]

/-- Identity under the stated parameter and domain assumptions: `cfConv_backW a b N (N + 2) = 0`. -/
theorem cfConv_backW_succ_succ (N : ℕ) : cfConv_backW a b N (N + 2) = 0 := by
  simp [cfConv_backW]

/-- Estimate under the stated parameter and domain assumptions: `∀ k ≤ N, cfConv_backW a b N k = b
k * cfConv_backW a b N (k + 1) + a (k + 1) * cfConv_backW a b N (k + 2)`. -/
theorem cfConv_backW_rec (N : ℕ) :
    ∀ k ≤ N, cfConv_backW a b N k =
      b k * cfConv_backW a b N (k + 1) + a (k + 1) * cfConv_backW a b N (k + 2) := by
  intro k hk
  have e : N + 1 - k = (N - k) + 1 := by omega
  have h1 : k ≤ N + 1 := by omega
  have h2 : k + 1 ≤ N + 1 := by omega
  simp only [cfConv_backW, h1, h2, ↓reduceIte,
    e, cfConv_back, show N - (N - k) = k by omega, show N + 1 - (k + 1) = N - k by omega]
  congr 2
  rcases Nat.eq_zero_or_pos (N - k) with h0 | hpos
  · have h3 : ¬ (k + 2 ≤ N + 1) := by omega
    simp only [h0, h3, ↓reduceIte]; rfl
  · obtain ⟨j, hj⟩ : ∃ j, N - k = j + 1 := ⟨N - k - 1, by omega⟩
    have h3 : k + 2 ≤ N + 1 := by omega
    simp only [hj, h3, ↓reduceIte, show N + 1 - (k + 2) = j by omega]
    rfl

/-- Equivalence transformations: scaling `b_k ↦ r_k b_k`, `a_0 ↦ r_0 a_0`,
`a_k ↦ r_{k-1} r_k a_k` multiplies the continuants by `∏_{k<n} r_k`. -/
theorem cfConv_equiv_continuants (r : ℕ → K) (n : ℕ) :
    (cfConv_ofFun h (fun k => (if k = 0 then r 0 else r (k - 1) * r k) * a k)
        (fun k => r k * b k)).dens n = (∏ k ∈ range n, r k) * (cfConv_ofFun h a b).dens n ∧
      (cfConv_ofFun h (fun k => (if k = 0 then r 0 else r (k - 1) * r k) * a k)
        (fun k => r k * b k)).nums n = (∏ k ∈ range n, r k) * (cfConv_ofFun h a b).nums n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · rw [cfConv_dens_zero, cfConv_dens_zero, cfConv_nums_zero, cfConv_nums_zero]; simp
    · simp [cfConv_dens_one, cfConv_nums_one]; ring
    · obtain ⟨d1, n1⟩ := ih (n + 1) (by omega)
      obtain ⟨d0, n0⟩ := ih n (by omega)
      rw [cfConv_dens_step, cfConv_dens_step, cfConv_nums_step, cfConv_nums_step, d1, d0, n1, n0]
      simp only [show n + 1 ≠ 0 by omega, ↓reduceIte, show n + 1 - 1 = n by omega,
        prod_range_succ]
      constructor <;> ring

/-- Equivalence transformations do not change the convergents. -/
theorem cfConv_equiv_convs (r : ℕ → K) (hr : ∀ k, r k ≠ 0) (n : ℕ) :
    (cfConv_ofFun h (fun k => (if k = 0 then r 0 else r (k - 1) * r k) * a k)
        (fun k => r k * b k)).convs n = (cfConv_ofFun h a b).convs n := by
  obtain ⟨d, e⟩ := cfConv_equiv_continuants (h := h) (a := a) (b := b) r n
  change _ / _ = _ / _
  rw [d, e]
  have : ∏ k ∈ range n, r k ≠ 0 := prod_ne_zero_iff.mpr fun k _ => hr k
  rw [mul_div_mul_left _ _ this]

/-- With `h = 0`, the convergents are linear in `a₀`. -/
theorem cfConv_convs_smul_a0 (c : K) (n : ℕ) :
    (cfConv_ofFun 0 (fun k => if k = 0 then c * a 0 else a k) b).convs n =
      c * (cfConv_ofFun 0 a b).convs n := by
  have hd : ∀ n, (cfConv_ofFun 0 (fun k => if k = 0 then c * a 0 else a k) b).dens n =
      (cfConv_ofFun 0 a b).dens n ∧
      (cfConv_ofFun 0 (fun k => if k = 0 then c * a 0 else a k) b).nums n =
      c * (cfConv_ofFun 0 a b).nums n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | _ | n
      · rw [cfConv_dens_zero, cfConv_dens_zero, cfConv_nums_zero, cfConv_nums_zero]; simp
      · simp [cfConv_dens_one, cfConv_nums_one]
      · obtain ⟨d1, n1⟩ := ih (n + 1) (by omega)
        obtain ⟨d0, n0⟩ := ih n (by omega)
        rw [cfConv_dens_step, cfConv_dens_step, cfConv_nums_step, cfConv_nums_step, d1, d0, n1, n0]
        simp only [show n + 1 ≠ 0 by omega, ↓reduceIte]
        exact ⟨trivial, by ring⟩
  change _ / _ = c * (_ / _)
  rw [(hd n).1, (hd n).2, mul_div_assoc]

end Finite

section Stieltjes

variable {h : ℂ} {a b : ℕ → ℂ}

/-- Estimate under the stated parameter and domain assumptions: `0 < (u⁻¹).re`. -/
theorem cfConv_re_recip_pos {u : ℂ} (hu : 0 < u.re) : 0 < (u⁻¹).re := by
  rw [Complex.inv_re]
  have : u ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hu; exact lt_irrefl _ hu
  exact div_pos hu (Complex.normSq_pos.mpr this)

/-- **Value region of an S-fraction.** Let `b_k = 1` and `a_k = c_k s²` for `k ≥ 1`, with
`c_k > 0` and `Re s > 0`. Then every denominator `B_n` is nonzero and every convergent satisfies
`‖A_n/B_n - h‖ ≤ ‖a₀‖ ‖s‖ / Re s`. (The tails `t` stay in the half-plane `Re (t/s) ≥ 0`.) -/
theorem cfConv_sfrac_bound {s : ℂ} (hs : 0 < s.re) (hb : ∀ k, b k = 1) {c : ℕ → ℝ}
    (hc : ∀ k, 1 ≤ k → 0 < c k) (ha : ∀ k, 1 ≤ k → a k = c k * s ^ 2) (n : ℕ) :
    (cfConv_ofFun h a b).dens n ≠ 0 ∧
      ‖(cfConv_ofFun h a b).convs n - h‖ ≤ ‖a 0‖ * ‖s‖ / s.re := by
  have hs0 : s ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hs; exact lt_irrefl _ hs
  have hinv : 0 < (s⁻¹).re := cfConv_re_recip_pos hs
  rcases n with _ | N
  · refine ⟨by rw [cfConv_dens_zero]; exact one_ne_zero, ?_⟩
    change ‖(cfConv_ofFun h a b).nums 0 / (cfConv_ofFun h a b).dens 0 - h‖ ≤ _
    rw [cfConv_nums_zero, cfConv_dens_zero, div_one, sub_self, norm_zero]
    positivity
  set w := cfConv_backW a b N with hw
  have hrec : ∀ k ≤ N, w k = b k * w (k + 1) + a (k + 1) * w (k + 2) :=
    cfConv_backW_rec (a := a) (b := b) N
  -- the tails `ρ_k = w_k / (s w_{k+1})` have `Re ρ_k ≥ Re (1/s)`
  have key : ∀ j ≤ N, w (N - j + 1) ≠ 0 ∧ (s⁻¹).re ≤ (w (N - j) / (s * w (N - j + 1))).re := by
    intro j
    induction j with
    | zero =>
      intro _
      have e1 : w (N + 1) = 1 := cfConv_backW_succ N
      have e0 : w N = 1 := by
        rw [hrec N le_rfl, e1, show w (N + 2) = 0 from cfConv_backW_succ_succ N, hb]; ring
      simp only [Nat.sub_zero, e1, e0, mul_one, one_div]
      exact ⟨one_ne_zero, le_rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2⟩ := ih (by omega)
      set k := N - (j + 1) with hk
      have hk1 : N - j = k + 1 := by omega
      rw [hk1] at h1 h2
      have hρ : 0 < (w (k + 1) / (s * w (k + 1 + 1))).re := lt_of_lt_of_le hinv h2
      have hw1 : w (k + 1) ≠ 0 := by
        intro h0; rw [h0, zero_div, Complex.zero_re] at hρ; exact lt_irrefl _ hρ
      refine ⟨hw1, ?_⟩
      have e := hrec k (by omega)
      rw [hb, ha (k + 1) (by omega), one_mul, show k + 2 = k + 1 + 1 by ring] at e
      have hc1 := hc (k + 1) (by omega)
      have eq : w k / (s * w (k + 1)) =
          s⁻¹ + (c (k + 1) : ℂ) * (w (k + 1) / (s * w (k + 1 + 1)))⁻¹ := by
        rw [e, inv_div]; field_simp
      rw [eq, Complex.add_re, Complex.re_ofReal_mul]
      have := cfConv_re_recip_pos hρ
      nlinarith
  obtain ⟨h1, h2⟩ := key N le_rfl
  simp only [Nat.sub_self, zero_add] at h1 h2
  have hρ0 : 0 < (w 0 / (s * w 1)).re := lt_of_lt_of_le hinv h2
  have hw0 : w 0 ≠ 0 := by
    intro h0; rw [h0, zero_div, Complex.zero_re] at hρ0; exact lt_irrefl _ hρ0
  obtain ⟨hd, hn⟩ := cfConv_continuants_of_back (h := h) N hrec (cfConv_backW_succ N)
    (cfConv_backW_succ_succ N)
  refine ⟨by rw [hd]; exact hw0, ?_⟩
  change ‖(cfConv_ofFun h a b).nums (N + 1) / (cfConv_ofFun h a b).dens (N + 1) - h‖ ≤ _
  rw [hd, hn]
  have e : (a 0 * w 1 + h * w 0) / w 0 - h = a 0 / (s * (w 0 / (s * w 1))) := by
    field_simp
    ring
  rw [e, norm_div, norm_mul]
  have hlow : s.re / ‖s‖ ≤ ‖s‖ * ‖w 0 / (s * w 1)‖ := by
    have hre : (s⁻¹).re = s.re / ‖s‖ ^ 2 := by
      rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
    have hns : 0 < ‖s‖ := norm_pos_iff.mpr hs0
    have := (Complex.re_le_norm (w 0 / (s * w 1))).trans' h2
    rw [hre] at this
    calc s.re / ‖s‖ = ‖s‖ * (s.re / ‖s‖ ^ 2) := by field_simp
      _ ≤ ‖s‖ * ‖w 0 / (s * w 1)‖ := by gcongr
  have hpos : 0 < s.re / ‖s‖ := div_pos hs (norm_pos_iff.mpr hs0)
  rw [div_le_iff₀ (lt_of_lt_of_le hpos hlow)]
  calc ‖a 0‖ = ‖a 0‖ * ‖s‖ / s.re * (s.re / ‖s‖) := by
        field_simp [norm_pos_iff.mpr hs0 |>.ne']
    _ ≤ ‖a 0‖ * ‖s‖ / s.re * (‖s‖ * ‖w 0 / (s * w 1)‖) := by gcongr

end Stieltjes

section Tails

/-- **Shifting off the first level.** With `h = 0`, the continuants of
`a₀/(b₀ + a₁/(b₁ + ⋯))` are expressed through those of the tail `a₁/(b₁ + a₂/(b₂ + ⋯))`:
`A_{N+1} = a₀ B'_N` and `B_{N+1} = b₀ B'_N + A'_N`. -/
theorem cfConv_shift_continuants {K : Type*} [Field K] (a b : ℕ → K) (N : ℕ) :
    (cfConv_ofFun 0 a b).nums (N + 1) =
        a 0 * (cfConv_ofFun 0 (fun k => a (k + 1)) (fun k => b (k + 1))).dens N ∧
      (cfConv_ofFun 0 a b).dens (N + 1) =
        b 0 * (cfConv_ofFun 0 (fun k => a (k + 1)) (fun k => b (k + 1))).dens N +
          (cfConv_ofFun 0 (fun k => a (k + 1)) (fun k => b (k + 1))).nums N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases N with _ | _ | N
    · rw [cfConv_nums_one, cfConv_dens_one, cfConv_dens_zero, cfConv_nums_zero]
      constructor <;> ring
    · rw [cfConv_nums_step, cfConv_dens_step, cfConv_nums_one, cfConv_dens_one, cfConv_nums_zero,
        cfConv_dens_zero, cfConv_dens_one, cfConv_nums_one]
      constructor <;> ring
    · obtain ⟨h1, h1'⟩ := ih (N + 1) (by omega)
      obtain ⟨h0, h0'⟩ := ih N (by omega)
      refine ⟨?_, ?_⟩
      · rw [cfConv_nums_step 0 a b (N + 1), cfConv_dens_step 0 (fun k => a (k + 1))
          (fun k => b (k + 1)) N, h1, h0]
        ring
      · rw [cfConv_dens_step 0 a b (N + 1), cfConv_dens_step 0 (fun k => a (k + 1))
          (fun k => b (k + 1)) N, cfConv_nums_step 0 (fun k => a (k + 1))
          (fun k => b (k + 1)) N, h1', h0']
        ring

/-- **Convergence of the tail.** If the convergents of `a₀/(b₀ + a₁/(b₁ + ⋯))` tend to `v ≠ 0`,
then the convergents of the tail `a₁/(b₁ + a₂/(b₂ + ⋯))` tend to `a₀/v - b₀`. -/
theorem cfConv_tail_tendsto {K : Type*} [NormedField K] {a b : ℕ → K} {v : K} (hv : v ≠ 0)
    (h : Tendsto (cfConv_ofFun 0 a b).convs atTop (𝓝 v)) :
    Tendsto (cfConv_ofFun 0 (fun k => a (k + 1)) (fun k => b (k + 1))).convs atTop
      (𝓝 (a 0 / v - b 0)) := by
  have h1 := h.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun N => a 0 / (cfConv_ofFun 0 a b).convs (N + 1) - b 0) atTop
      (𝓝 (a 0 / v - b 0)) :=
    (tendsto_const_nhds.div h1 hv).sub_const (b 0)
  refine hlim.congr' ?_
  filter_upwards [h1.eventually_ne hv] with N hN
  obtain ⟨e1, e2⟩ := cfConv_shift_continuants a b N
  change (cfConv_ofFun 0 a b).nums (N + 1) / (cfConv_ofFun 0 a b).dens (N + 1) ≠ 0 at hN
  change _ = (cfConv_ofFun 0 _ _).nums N / (cfConv_ofFun 0 _ _).dens N
  change a 0 / ((cfConv_ofFun 0 a b).nums (N + 1) / (cfConv_ofFun 0 a b).dens (N + 1)) - b 0 = _
  rw [e1, e2] at hN ⊢
  have hA : a 0 ≠ 0 := fun h0 => hN (by rw [h0, zero_mul, zero_div])
  have hD : (cfConv_ofFun 0 (fun k => a (k + 1)) (fun k => b (k + 1))).dens N ≠ 0 :=
    fun h0 => hN (by rw [h0, mul_zero, zero_div])
  have hE : b 0 * (cfConv_ofFun 0 (fun k => a (k + 1)) (fun k => b (k + 1))).dens N +
      (cfConv_ofFun 0 (fun k => a (k + 1)) (fun k => b (k + 1))).nums N ≠ 0 :=
    fun h0 => hN (by rw [h0, div_zero])
  field_simp
  ring

/-- **Value region of a constant-denominator S-fraction.** If `b_k = z` with `Re z > 0` and
`a_k = c_k > 0` for `k ≥ 1`, then every denominator `B_n` of `a₀/(z + a₁/(z + ⋯))` is nonzero
and every convergent satisfies `‖A_n/B_n‖ ≤ ‖a₀‖ / Re z`. -/
theorem cfConv_sfrac_const_bound {z : ℂ} (hz : 0 < z.re) {a : ℕ → ℂ} {c : ℕ → ℝ}
    (hc : ∀ k, 1 ≤ k → 0 < c k) (ha : ∀ k, 1 ≤ k → a k = c k) (n : ℕ) :
    (cfConv_ofFun 0 a (fun _ => z)).dens n ≠ 0 ∧
      ‖(cfConv_ofFun 0 a (fun _ => z)).convs n‖ ≤ ‖a 0‖ / z.re := by
  have hz0 : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hz; exact lt_irrefl _ hz
  set r : ℕ → ℂ := fun _ => z⁻¹ with hr
  have hr0 : ∀ k, r k ≠ 0 := fun _ => inv_ne_zero hz0
  have hs : 0 < (z⁻¹).re := cfConv_re_recip_pos hz
  obtain ⟨hB, hval⟩ := cfConv_sfrac_bound (h := 0) (s := z⁻¹) hs
    (a := fun k => (if k = 0 then r 0 else r (k - 1) * r k) * a k)
    (b := fun k => r k * z) (fun k => inv_mul_cancel₀ hz0) (c := c) hc
    (fun k hk => by
      simp only [r, show k ≠ 0 by omega, ↓reduceIte, ha k hk]
      ring) n
  obtain ⟨hd, -⟩ := cfConv_equiv_continuants (h := (0 : ℂ)) (a := a) (b := fun _ => z) r n
  have hconv := cfConv_equiv_convs (h := (0 : ℂ)) (a := a) (b := fun _ => z) r hr0 n
  refine ⟨fun h0 => hB (by rw [hd, h0, mul_zero]), ?_⟩
  rw [← hconv]
  rw [sub_zero] at hval
  refine hval.trans (le_of_eq ?_)
  simp only [r, ↓reduceIte, norm_mul, norm_inv]
  rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  field_simp

/-- **The value of a constant-denominator S-fraction is nonzero.** If `b_k = z` with
`Re z > 0`, `a₀ ≠ 0` and `a_k = c_k > 0` for `k ≥ 1`, any limit of the convergents of
`a₀/(z + a₁/(z + ⋯))` is nonzero: the convergents stay outside the disc of radius
`‖a₀‖ / (‖z‖ + ‖a₁‖ / Re z)`. -/
theorem cfConv_sfrac_const_ne_zero {z : ℂ} (hz : 0 < z.re) {a : ℕ → ℂ} {c : ℕ → ℝ}
    (hc : ∀ k, 1 ≤ k → 0 < c k) (ha : ∀ k, 1 ≤ k → a k = c k) (ha0 : a 0 ≠ 0) {v : ℂ}
    (h : Tendsto (cfConv_ofFun 0 a (fun _ => z)).convs atTop (𝓝 v)) : v ≠ 0 := by
  set m : ℝ := ‖a 0‖ / (‖z‖ + ‖a 1‖ / z.re) with hm
  have hm0 : 0 < m := by
    have : 0 ≤ ‖a 1‖ / z.re := div_nonneg (norm_nonneg _) hz.le
    have hz0 : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hz; exact lt_irrefl _ hz
    exact div_pos (norm_pos_iff.mpr ha0) (by positivity)
  have hlow : ∀ N, m ≤ ‖(cfConv_ofFun 0 a (fun _ => z)).convs (N + 1)‖ := by
    intro N
    obtain ⟨e1, e2⟩ := cfConv_shift_continuants a (fun _ => z) N
    obtain ⟨hD', hT⟩ := cfConv_sfrac_const_bound hz (a := fun k => a (k + 1))
      (c := fun k => c (k + 1)) (fun k _ => hc (k + 1) (by omega))
      (fun k _ => ha (k + 1) (by omega)) N
    obtain ⟨hD, -⟩ := cfConv_sfrac_const_bound hz hc ha (N + 1)
    set A' := (cfConv_ofFun 0 (fun k => a (k + 1)) (fun _ => z)).nums N
    set D' := (cfConv_ofFun 0 (fun k => a (k + 1)) (fun _ => z)).dens N
    replace hT : ‖A' / D'‖ ≤ ‖a 1‖ / z.re := hT
    change m ≤ ‖(cfConv_ofFun 0 a (fun _ => z)).nums (N + 1) /
      (cfConv_ofFun 0 a (fun _ => z)).dens (N + 1)‖
    rw [e2] at hD
    rw [e1, e2]
    have hE : z + A' / D' ≠ 0 := by
      intro h0; apply hD
      have : z * D' + A' = D' * (z + A' / D') := by field_simp
      rw [this, h0, mul_zero]
    have eq : a 0 * D' / (z * D' + A') = a 0 / (z + A' / D') := by
      field_simp
    rw [eq, norm_div, hm]
    have hpos : 0 < ‖z + A' / D'‖ := norm_pos_iff.mpr hE
    have hle : ‖z + A' / D'‖ ≤ ‖z‖ + ‖a 1‖ / z.re := (norm_add_le _ _).trans (by
      simpa using hT)
    exact div_le_div_of_nonneg_left (norm_nonneg _) hpos hle
  intro hv
  have hn := (h.comp (tendsto_add_atTop_nat 1)).norm
  rw [hv, norm_zero] at hn
  have := ge_of_tendsto hn (Eventually.of_forall hlow)
  linarith

/-- **Convergence from the tail.** If the convergents of the tail `a₁/(b₁ + a₂/(b₂ + ⋯))`
tend to `t`, its denominators are eventually nonzero, and `b₀ + t ≠ 0`, then the convergents
of `a₀/(b₀ + a₁/(b₁ + ⋯))` tend to `a₀/(b₀ + t)`, and its denominators are eventually nonzero. -/
theorem cfConv_head_tendsto {K : Type*} [NormedField K] {a b : ℕ → K} {t : K}
    (hD : ∀ᶠ N in atTop, (cfConv_ofFun 0 (fun k => a (k + 1)) (fun k => b (k + 1))).dens N ≠ 0)
    (ht : Tendsto (cfConv_ofFun 0 (fun k => a (k + 1)) (fun k => b (k + 1))).convs atTop (𝓝 t))
    (hbt : b 0 + t ≠ 0) :
    Tendsto (cfConv_ofFun 0 a b).convs atTop (𝓝 (a 0 / (b 0 + t))) ∧
      ∀ᶠ N in atTop, (cfConv_ofFun 0 a b).dens N ≠ 0 := by
  set g' := cfConv_ofFun 0 (fun k => a (k + 1)) (fun k => b (k + 1))
  have hbt' : ∀ᶠ N in atTop, b 0 + g'.convs N ≠ 0 :=
    (ht.const_add (b 0)).eventually_ne hbt
  have hev := hD.and hbt'
  have hdens : ∀ N, g'.dens N ≠ 0 → b 0 + g'.convs N ≠ 0 →
      (cfConv_ofFun 0 a b).dens (N + 1) ≠ 0 ∧
        (cfConv_ofFun 0 a b).convs (N + 1) = a 0 / (b 0 + g'.convs N) := by
    intro N hN hN'
    have e1 : (cfConv_ofFun 0 a b).nums (N + 1) = a 0 * g'.dens N :=
      (cfConv_shift_continuants a b N).1
    have e2 : (cfConv_ofFun 0 a b).dens (N + 1) = b 0 * g'.dens N + g'.nums N :=
      (cfConv_shift_continuants a b N).2
    change b 0 + g'.nums N / g'.dens N ≠ 0 at hN'
    have hE : b 0 * g'.dens N + g'.nums N ≠ 0 := by
      intro h0; apply hN'
      have : b 0 + g'.nums N / g'.dens N = (b 0 * g'.dens N + g'.nums N) / g'.dens N := by
        field_simp
      rw [this, h0, zero_div]
    refine ⟨by rw [e2]; exact hE, ?_⟩
    change (cfConv_ofFun 0 a b).nums (N + 1) / (cfConv_ofFun 0 a b).dens (N + 1) =
      a 0 / (b 0 + g'.nums N / g'.dens N)
    rw [e1, e2]
    field_simp
  refine ⟨?_, ?_⟩
  · show Tendsto (fun n => (cfConv_ofFun 0 a b).convs n) atTop _
    rw [← tendsto_add_atTop_iff_nat 1]
    refine ((tendsto_const_nhds.div (ht.const_add (b 0)) hbt)).congr' ?_
    filter_upwards [hev] with N hN
    exact ((hdens N hN.1 hN.2).2).symm
  · obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
    refine eventually_atTop.mpr ⟨N0 + 1, fun N hN => ?_⟩
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    exact (hdens M (hN0 M (by omega)).1 (hN0 M (by omega)).2).1

/-- **Convergence from a far tail.** Let `w` be a nowhere vanishing backward solution of the
recurrence `w_k = b_k w_{k+1} + a_{k+1} w_{k+2}`. If for some `j` the tail
`a_j/(b_j + a_{j+1}/(b_{j+1} + ⋯))` converges to `a_j w_{j+1}/w_j` with eventually nonzero
denominators, then `a₀/(b₀ + a₁/(b₁ + ⋯))` converges to `a₀ w₁/w₀`, again with eventually
nonzero denominators. -/
theorem cfConv_tendsto_of_tail {K : Type*} [NormedField K] {a b w : ℕ → K}
    (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2)) (hw0 : ∀ k, w k ≠ 0) (j : ℕ)
    (hD : ∀ᶠ N in atTop, (cfConv_ofFun 0 (fun k => a (k + j)) (fun k => b (k + j))).dens N ≠ 0)
    (hj : Tendsto (cfConv_ofFun 0 (fun k => a (k + j)) (fun k => b (k + j))).convs atTop
      (𝓝 (a j * w (j + 1) / w j))) :
    Tendsto (cfConv_ofFun 0 a b).convs atTop (𝓝 (a 0 * w 1 / w 0)) ∧
      ∀ᶠ N in atTop, (cfConv_ofFun 0 a b).dens N ≠ 0 := by
  induction j with
  | zero => exact ⟨by simpa using hj, by simpa using hD⟩
  | succ j ih =>
    have ea : (fun k => (fun k => a (k + j)) (k + 1)) = fun k => a (k + (j + 1)) :=
      funext fun k => congrArg a (by omega)
    have eb : (fun k => (fun k => b (k + j)) (k + 1)) = fun k => b (k + (j + 1)) :=
      funext fun k => congrArg b (by omega)
    have hbt : b j + a (j + 1) * w (j + 1 + 1) / w (j + 1) ≠ 0 := by
      have e : b j + a (j + 1) * w (j + 1 + 1) / w (j + 1) = w j / w (j + 1) := by
        rw [hw j]; field_simp [hw0 (j + 1)]
      rw [e]; exact div_ne_zero (hw0 j) (hw0 (j + 1))
    obtain ⟨h1, h2⟩ := cfConv_head_tendsto (a := fun k => a (k + j)) (b := fun k => b (k + j))
      (by rw [ea, eb]; exact hD) (by rw [ea, eb]; exact hj) (by simpa using hbt)
    refine ih h2 ?_
    convert h1 using 2
    simp only [zero_add]
    have e : b j + a (j + 1) * w (j + 1 + 1) / w (j + 1) = w j / w (j + 1) := by
      rw [hw j]; field_simp [hw0 (j + 1)]
    rw [e]
    field_simp [hw0 j, hw0 (j + 1)]

/-- **Composition with a tail.** The continuants of `h + a₀/(b₀ + ⋯)` at index `J + 1 + n`
are combinations of those at `J + 1` and `J` with the continuants of the tail
`a_{J+1}/(b_{J+1} + a_{J+2}/(b_{J+2} + ⋯))`. -/
theorem cfConv_compose {K : Type*} [Field K] (h : K) (a b : ℕ → K) (J n : ℕ) :
    (cfConv_ofFun h a b).nums (J + 1 + n) =
        (cfConv_ofFun h a b).nums (J + 1) *
            (cfConv_ofFun 0 (fun k => a (k + (J + 1))) (fun k => b (k + (J + 1)))).dens n +
          (cfConv_ofFun h a b).nums J *
            (cfConv_ofFun 0 (fun k => a (k + (J + 1))) (fun k => b (k + (J + 1)))).nums n ∧
      (cfConv_ofFun h a b).dens (J + 1 + n) =
        (cfConv_ofFun h a b).dens (J + 1) *
            (cfConv_ofFun 0 (fun k => a (k + (J + 1))) (fun k => b (k + (J + 1)))).dens n +
          (cfConv_ofFun h a b).dens J *
            (cfConv_ofFun 0 (fun k => a (k + (J + 1))) (fun k => b (k + (J + 1)))).nums n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · rw [cfConv_dens_zero, cfConv_nums_zero]
      constructor <;> simp
    · rw [cfConv_dens_one, cfConv_nums_one, show J + 1 + 1 = J + 2 from rfl, cfConv_nums_step,
        cfConv_dens_step]
      simp only [zero_add, mul_zero]
      constructor <;> ring
    · obtain ⟨h1, h1'⟩ := ih (n + 1) (by omega)
      obtain ⟨h0, h0'⟩ := ih n (by omega)
      rw [show J + 1 + (n + 1 + 1) = J + 1 + n + 2 by ring, show n + 1 + 1 = n + 2 from rfl,
        cfConv_nums_step h a b (J + 1 + n), cfConv_dens_step h a b (J + 1 + n),
        cfConv_dens_step 0 (fun k => a (k + (J + 1))) (fun k => b (k + (J + 1))) n,
        cfConv_nums_step 0 (fun k => a (k + (J + 1))) (fun k => b (k + (J + 1))) n,
        show J + 1 + n + 1 = J + 1 + (n + 1) by ring, h1, h1', h0, h0']
      simp only [show n + 1 + (J + 1) = J + 1 + (n + 1) by ring]
      constructor <;> ring

/-- **Pincherle's theorem from a tail.** Let `w` be a backward solution of
`w_k = b_k w_{k+1} + a_{k+1} w_{k+2}` with `w₀ ≠ 0` and `w_{J+1} ≠ 0`. If the tail
`a_{J+1}/(b_{J+1} + ⋯)` converges to `a_{J+1} w_{J+2}/w_{J+1}` with eventually nonzero
denominators, then the convergents of `h + a₀/(b₀ + a₁/(b₁ + ⋯))` tend to `h + a₀ w₁/w₀`.
No condition is imposed on the elements before the tail: they may vanish, and the
intermediate `w_k` may vanish. -/
theorem cfConv_tendsto_of_tail_invariant {K : Type*} [NormedField K] {h : K} {a b w : ℕ → K}
    (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2)) (hw0 : w 0 ≠ 0) (J : ℕ)
    (hwJ : w (J + 1) ≠ 0)
    (hD : ∀ᶠ n in atTop,
      (cfConv_ofFun 0 (fun k => a (k + (J + 1))) (fun k => b (k + (J + 1)))).dens n ≠ 0)
    (hT : Tendsto (cfConv_ofFun 0 (fun k => a (k + (J + 1))) (fun k => b (k + (J + 1)))).convs
      atTop (𝓝 (a (J + 1) * w (J + 2) / w (J + 1)))) :
    Tendsto (cfConv_ofFun h a b).convs atTop (𝓝 (h + a 0 * w 1 / w 0)) := by
  set g := cfConv_ofFun h a b with hg
  set T := cfConv_ofFun 0 (fun k => a (k + (J + 1))) (fun k => b (k + (J + 1))) with hTdef
  obtain ⟨i1, i2⟩ := cfConv_invariant (h := h) hw J
  set τ := a (J + 1) * w (J + 2) / w (J + 1) with hτ
  have hden : g.dens (J + 1) + g.dens J * τ ≠ 0 := by
    have e : g.dens (J + 1) + g.dens J * τ = w 0 / w (J + 1) := by
      rw [hτ, eq_div_iff hwJ]
      field_simp
      linear_combination i2
    rw [e]; exact div_ne_zero hw0 hwJ
  have hval : (g.nums (J + 1) + g.nums J * τ) / (g.dens (J + 1) + g.dens J * τ) =
      h + a 0 * w 1 / w 0 := by
    have e1 : g.nums (J + 1) + g.nums J * τ = (a 0 * w 1 + h * w 0) / w (J + 1) := by
      rw [hτ, eq_div_iff hwJ]
      field_simp
      linear_combination i1
    have e2 : g.dens (J + 1) + g.dens J * τ = w 0 / w (J + 1) := by
      rw [hτ, eq_div_iff hwJ]
      field_simp
      linear_combination i2
    rw [e1, e2, div_div_div_cancel_right₀ hwJ]
    field_simp
    ring
  have hlim : Tendsto (fun n => (g.nums (J + 1) + g.nums J * T.convs n) /
      (g.dens (J + 1) + g.dens J * T.convs n)) atTop (𝓝 (h + a 0 * w 1 / w 0)) := by
    rw [← hval]
    exact (tendsto_const_nhds.add (tendsto_const_nhds.mul hT)).div
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hT)) hden
  show Tendsto (fun n => g.convs n) atTop _
  rw [← tendsto_add_atTop_iff_nat (J + 1)]
  refine hlim.congr' ?_
  filter_upwards [hD] with n hn
  obtain ⟨c1, c2⟩ := cfConv_compose h a b J n
  change _ = g.nums (n + (J + 1)) / g.dens (n + (J + 1))
  rw [add_comm n (J + 1), c1, c2]
  change (g.nums (J + 1) + g.nums J * (T.nums n / T.dens n)) /
    (g.dens (J + 1) + g.dens J * (T.nums n / T.dens n)) = _
  have e1 : g.nums (J + 1) + g.nums J * (T.nums n / T.dens n) =
      (g.nums (J + 1) * T.dens n + g.nums J * T.nums n) / T.dens n := by
    field_simp
  have e2 : g.dens (J + 1) + g.dens J * (T.nums n / T.dens n) =
      (g.dens (J + 1) * T.dens n + g.dens J * T.nums n) / T.dens n := by
    field_simp
  rw [e1, e2, div_div_div_cancel_right₀ hn]

end Tails

section Holomorphy

variable {Ω : Set ℂ} {h : ℂ → ℂ} {a b : ℕ → ℂ → ℂ}

/-- Continuants of a continued fraction with holomorphic elements are holomorphic. -/
theorem cfConv_continuants_differentiableOn (hh : DifferentiableOn ℂ h Ω)
    (ha : ∀ k, DifferentiableOn ℂ (a k) Ω) (hb : ∀ k, DifferentiableOn ℂ (b k) Ω) (n : ℕ) :
    DifferentiableOn ℂ (fun z => (cfConv_ofFun (h z) (fun k => a k z) (fun k => b k z)).dens n) Ω ∧
      DifferentiableOn ℂ
        (fun z => (cfConv_ofFun (h z) (fun k => a k z) (fun k => b k z)).nums n) Ω := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · exact ⟨(differentiableOn_const (1 : ℂ)).congr fun z _ => cfConv_dens_zero _ _ _,
        hh.congr fun z _ => cfConv_nums_zero _ _ _⟩
    · exact ⟨(hb 0).congr fun z _ => cfConv_dens_one _ _ _,
        (((hb 0).mul hh).add (ha 0)).congr fun z _ => cfConv_nums_one _ _ _⟩
    · obtain ⟨d1, n1⟩ := ih (n + 1) (by omega)
      obtain ⟨d0, n0⟩ := ih n (by omega)
      exact ⟨(((hb _).mul d1).add ((ha _).mul d0)).congr fun z _ => cfConv_dens_step _ _ _ n,
        (((hb _).mul n1).add ((ha _).mul n0)).congr fun z _ => cfConv_nums_step _ _ _ n⟩

/-- Convergents with holomorphic elements are holomorphic where the denominator is nonzero. -/
theorem cfConv_convs_differentiableOn (hh : DifferentiableOn ℂ h Ω)
    (ha : ∀ k, DifferentiableOn ℂ (a k) Ω) (hb : ∀ k, DifferentiableOn ℂ (b k) Ω) (n : ℕ)
    (hd : ∀ z ∈ Ω, (cfConv_ofFun (h z) (fun k => a k z) (fun k => b k z)).dens n ≠ 0) :
    DifferentiableOn ℂ
      (fun z => (cfConv_ofFun (h z) (fun k => a k z) (fun k => b k z)).convs n) Ω := by
  obtain ⟨d, e⟩ := cfConv_continuants_differentiableOn hh ha hb n
  exact (DifferentiableOn.div e d hd).congr fun z _ => rfl

end Holomorphy

end GenContFract
