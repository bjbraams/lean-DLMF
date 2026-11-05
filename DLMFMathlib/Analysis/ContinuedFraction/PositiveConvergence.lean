/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ContinuedFraction.Convergence
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Convergence of bounded positive continued fractions

A continued fraction with unit partial denominators and positive, bounded partial numerators
has summable consecutive differences. Its convergents therefore form a Cauchy sequence.
-/

@[expose] public noncomputable section

open Filter Finset
open scoped Topology

namespace GenContFract

/-- Bounded positive partial numerators give summable consecutive differences. -/
theorem summable_abs_sub_ofFun_convs_of_pos_bounded (h : ℝ) {a : ℕ → ℝ}
    (ha : ∀ k, 0 < a k) {C : ℝ} (hC : ∀ k, a k ≤ C) :
    Summable (fun n => |(ofFun h a (fun _ => 1)).convs (n + 1) -
      (ofFun h a (fun _ => 1)).convs n|) := by
  let g := ofFun h a (fun _ => (1 : ℝ))
  have hb : ∀ k, 0 < (fun _ : ℕ => (1 : ℝ)) k := fun _ => one_pos
  have hB : ∀ k, 0 < g.dens k := ofFun_dens_pos ha hb
  have hstepB (k : ℕ) : g.dens (k + 2) = g.dens (k + 1) + a (k + 1) * g.dens k := by
    simpa only [one_mul] using ofFun_dens_add_two h a (fun _ => (1 : ℝ)) k
  have hmono : ∀ k, g.dens k ≤ g.dens (k + 1) := by
    intro k
    cases k with
    | zero => rw [ofFun_dens_zero, ofFun_dens_one]
    | succ k =>
      rw [show k + 1 + 1 = k + 2 by omega, hstepB]
      have := ha (k + 1)
      have := hB k
      nlinarith
  let D : ℕ → ℝ := fun k => (∏ j ∈ range (k + 1), a j) / (g.dens k * g.dens (k + 1))
  have hDpos (k : ℕ) : 0 < D k :=
    div_pos (prod_pos fun j _ => ha j) (mul_pos (hB k) (hB (k + 1)))
  have hdiff (k : ℕ) : |g.convs (k + 1) - g.convs k| = D k := by
    have hdet := ofFun_determinant h a (fun _ => (1 : ℝ)) k
    have he : g.convs (k + 1) - g.convs k = (-1) ^ k * D k := by
      change g.nums (k + 1) / g.dens (k + 1) - g.nums k / g.dens k = _
      dsimp [D]
      have h0 := (hB k).ne'
      have h1 := (hB (k + 1)).ne'
      field_simp
      linear_combination hdet
    rw [he, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (hDpos k)]
  have hCpos : 0 < C := (ha 0).trans_le (hC 0)
  have hratio (k : ℕ) : D (k + 1) ≤ C / (1 + C) * D k := by
    have hP : 0 < ∏ j ∈ range (k + 1), a j := prod_pos fun j _ => ha j
    have ha1 := ha (k + 1)
    have hC1 := hC (k + 1)
    have hB0 := hB k
    have hB1 := hB (k + 1)
    have hB2 := hB (k + 2)
    have hBm := hmono k
    dsimp [D]
    rw [show k + 1 + 1 = k + 2 by omega, prod_range_succ]
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    rw [hstepB] at *
    have hle : a (k + 1) * g.dens k ≤ C * g.dens (k + 1) :=
      mul_le_mul hC1 hBm hB0.le hCpos.le
    nlinarith only [mul_le_mul_of_nonneg_left hle (mul_pos hP hB1).le]
  have hsum : Summable D := summable_of_ratio_norm_eventually_le
    (show C / (1 + C) < 1 by rw [div_lt_one (by positivity)]; linarith)
    (Eventually.of_forall fun k => by
      simpa only [Real.norm_eq_abs, abs_of_pos (hDpos k), abs_of_pos (hDpos (k + 1))]
        using hratio k)
  exact hsum.congr fun k => (hdiff k).symm

/-- Bounded positive continued fractions converge. -/
theorem exists_tendsto_ofFun_convs_of_pos_bounded (h : ℝ) {a : ℕ → ℝ}
    (ha : ∀ k, 0 < a k) {C : ℝ} (hC : ∀ k, a k ≤ C) :
    ∃ v, Tendsto (ofFun h a (fun _ => 1)).convs atTop (𝓝 v) := by
  apply cauchySeq_tendsto_of_complete
  apply cauchySeq_of_summable_dist
  simpa only [Real.dist_eq, abs_sub_comm] using
    summable_abs_sub_ofFun_convs_of_pos_bounded h ha hC

/-- Positive continued fractions converge when their normalized partial numerators are bounded. -/
theorem exists_tendsto_ofFun_convs_of_pos_normalized_bounded (h : ℝ) {a b : ℕ → ℝ}
    (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k) {C : ℝ}
    (hC : ∀ k, a k / (if k = 0 then b 0 else b (k - 1) * b k) ≤ C) :
    ∃ v, Tendsto (ofFun h a b).convs atTop (𝓝 v) := by
  let r := fun k => (b k)⁻¹
  let A := fun k => a k / (if k = 0 then b 0 else b (k - 1) * b k)
  have hr (k : ℕ) : r k ≠ 0 := inv_ne_zero (hb k).ne'
  have hA (k : ℕ) : 0 < A k := by
    dsimp [A]
    apply div_pos (ha k)
    split_ifs
    · exact hb 0
    · exact mul_pos (hb _) (hb _)
  obtain ⟨v, hv⟩ := exists_tendsto_ofFun_convs_of_pos_bounded h hA hC
  have heA : (fun k => (if k = 0 then r 0 else r (k - 1) * r k) * a k) = A := by
    funext k
    by_cases hk : k = 0 <;> simp [r, A, hk, div_eq_mul_inv, mul_comm]
  have heB : (fun k => r k * b k) = fun _ => 1 := by
    funext k
    exact inv_mul_cancel₀ (hb k).ne'
  have heq (n : ℕ) : (ofFun h a b).convs n = (ofFun h A (fun _ => 1)).convs n := by
    have he := ofFun_convs_equiv (h := h) (a := a) (b := b) r hr n
    rw [heA, heB] at he
    exact he.symm
  refine ⟨v, ?_⟩
  change Tendsto (fun n => _) atTop _
  simpa only [heq] using hv

end GenContFract
