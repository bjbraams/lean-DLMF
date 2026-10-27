/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ContinuedFraction.Convergence

/-!
# Divergent partial sums under a ratio limit, and a Pincherle criterion

* `pinch_norm_sum_tendsto`: if `T n ≠ 0` and `T (n+1) / T n → ρ` with `‖ρ‖ > 1`, then the
  partial sums `∑_{i<n} T i` tend to infinity in norm. (Unlike
  `GenContFract.cfConv_norm_sum_tendsto`, no growth factor `q > 2` is needed: the partial sums
  are compared with `ρ T_n/(ρ-1)`.)
* `pinch_cfConv_tendsto`: **Pincherle's criterion with a ratio limit.** If `w` is a backward
  solution `w_k = b_k w_{k+1} + a_{k+1} w_{k+2}` with `w₀ ≠ 0`, all `a_k ≠ 0`, `w_k`
  eventually nonzero, and `-w_k/(a_{k+1} w_{k+2}) → ρ` with `‖ρ‖ > 1`, then the convergents of
  `h + a₀/(b₀ + a₁/(b₁ + ⋯))` tend to `h + a₀ w₁/w₀`.
-/

@[expose] public noncomputable section

open Filter Finset
open scoped Topology

namespace GenContFract

variable {K : Type*} [NormedField K]

/-- Tail sums of terms growing at least geometrically with ratio `r > 1` are dominated by the
last term. -/
theorem pinch_sum_Ico_le {T : ℕ → K} {r : ℝ} (hr : 1 < r) {M : ℕ}
    (hT : ∀ n ≥ M, r * ‖T n‖ ≤ ‖T (n + 1)‖) (n : ℕ) (hn : M ≤ n) :
    ∑ k ∈ Ico M n, ‖T k‖ ≤ ‖T n‖ / (r - 1) := by
  have hr1 : 0 < r - 1 := by linarith
  induction n, hn using Nat.le_induction with
  | base => simp; positivity
  | succ n hn ih =>
    rw [sum_Ico_succ_top hn]
    have := hT n hn
    rw [le_div_iff₀ hr1] at ih ⊢
    nlinarith [norm_nonneg (T n)]

/-- If `T n ≠ 0` and `T (n+1)/T n → ρ` with `‖ρ‖ > 1`, the partial sums of `T` tend to infinity
in norm. -/
theorem pinch_norm_sum_tendsto {T : ℕ → K} {ρ : K} (hρ : 1 < ‖ρ‖) (hT : ∀ n, T n ≠ 0)
    (hlim : Tendsto (fun n => T (n + 1) / T n) atTop (𝓝 ρ)) :
    Tendsto (fun n => ‖∑ i ∈ range n, T i‖) atTop atTop := by
  obtain ⟨r, hr1, hrρ⟩ := exists_between hρ
  have hρ0 : 0 < ‖ρ‖ := by linarith
  set ε : ℝ := (r - 1) * ‖ρ‖ / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; nlinarith
  -- eventually the ratios are close to `ρ` and of norm at least `r`
  have hev1 : ∀ᶠ n in atTop, ‖T (n + 1) / T n - ρ‖ < ε := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hlim).eventually (gt_mem_nhds hεpos)
    exact this
  have hev2 : ∀ᶠ n in atTop, r < ‖T (n + 1) / T n‖ :=
    (continuous_norm.tendsto ρ |>.comp hlim).eventually (lt_mem_nhds hrρ)
  obtain ⟨M, hM⟩ := (hev1.and hev2).exists_forall_of_atTop
  have hgrow : ∀ n ≥ M, r * ‖T n‖ ≤ ‖T (n + 1)‖ := by
    intro n hn
    have h := (hM n hn).2
    rw [norm_div, lt_div_iff₀ (norm_pos_iff.mpr (hT n))] at h
    exact h.le
  have hclose : ∀ n ≥ M, ‖ρ * T n - T (n + 1)‖ ≤ ε * ‖T n‖ := by
    intro n hn
    have h := (hM n hn).1
    have e : ρ * T n - T (n + 1) = -((T (n + 1) / T n - ρ) * T n) := by
      field_simp [hT n]; ring
    rw [e, norm_neg, norm_mul]
    exact mul_le_mul_of_nonneg_right h.le (norm_nonneg _)
  -- `R n = (ρ - 1) S_{n+1} - ρ T_n` changes by `ρ T_n - T_{n+1}`
  set R : ℕ → K := fun n => (ρ - 1) * ∑ i ∈ range (n + 1), T i - ρ * T n with hR
  have hRstep : ∀ n, R (n + 1) - R n = ρ * T n - T (n + 1) := by
    intro n; simp only [hR, sum_range_succ _ (n + 1)]; ring
  have hRbound : ∀ n ≥ M, ‖R n‖ ≤ ‖R M‖ + ε * ∑ k ∈ Ico M n, ‖T k‖ := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [sum_Ico_succ_top hn]
      have h1 : R (n + 1) = R n + (ρ * T n - T (n + 1)) := by rw [← hRstep n]; ring
      rw [h1]
      calc ‖R n + (ρ * T n - T (n + 1))‖ ≤ ‖R n‖ + ‖ρ * T n - T (n + 1)‖ := norm_add_le _ _
        _ ≤ ‖R M‖ + ε * ∑ k ∈ Ico M n, ‖T k‖ + ε * ‖T n‖ := add_le_add ih (hclose n hn)
        _ = _ := by ring
  have hr1' : 0 < r - 1 := by linarith
  have hlow : ∀ n ≥ M, ‖ρ‖ / 2 * ‖T n‖ - ‖R M‖ ≤ ‖ρ - 1‖ * ‖∑ i ∈ range (n + 1), T i‖ := by
    intro n hn
    have h1 := hRbound n hn
    have h2 := pinch_sum_Ico_le hr1 hgrow n hn
    have h3 : ε * ∑ k ∈ Ico M n, ‖T k‖ ≤ ε * (‖T n‖ / (r - 1)) :=
      mul_le_mul_of_nonneg_left h2 hεpos.le
    have h4 : ε * (‖T n‖ / (r - 1)) = ‖ρ‖ / 2 * ‖T n‖ := by
      rw [hε]; field_simp
    have e : (ρ - 1) * ∑ i ∈ range (n + 1), T i = ρ * T n + R n := by simp only [hR]; ring
    have h5 : ‖ρ * T n‖ ≤ ‖(ρ - 1) * ∑ i ∈ range (n + 1), T i‖ + ‖R n‖ := by
      rw [e]
      calc ‖ρ * T n‖ = ‖(ρ * T n + R n) - R n‖ := by ring_nf
        _ ≤ ‖ρ * T n + R n‖ + ‖R n‖ := norm_sub_le _ _
    rw [norm_mul, norm_mul] at h5
    linarith
  -- the terms grow geometrically
  have hgeo : ∀ j, r ^ j * ‖T M‖ ≤ ‖T (M + j)‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := hgrow (M + j) (by omega)
      rw [pow_succ, ← add_assoc]
      nlinarith [norm_nonneg (T M), pow_pos (by linarith : (0 : ℝ) < r) j]
  have hTinf : Tendsto (fun j : ℕ => ‖T (M + j)‖) atTop atTop :=
    tendsto_atTop_mono hgeo ((tendsto_pow_atTop_atTop_of_one_lt hr1).atTop_mul_const
      (norm_pos_iff.mpr (hT M)))
  have hρ1 : 0 < ‖ρ - 1‖ := by
    rw [norm_pos_iff, sub_ne_zero]; rintro rfl; simp at hρ
  have hj : Tendsto (fun j : ℕ => ‖∑ i ∈ range (M + j + 1), T i‖) atTop atTop := by
    have hA : Tendsto (fun j : ℕ => (‖ρ‖ / 2 * ‖T (M + j)‖ - ‖R M‖) / ‖ρ - 1‖) atTop atTop :=
      ((tendsto_atTop_add_const_right _ _ (hTinf.const_mul_atTop (by positivity))).atTop_div_const
        hρ1)
    refine tendsto_atTop_mono (fun j => ?_) hA
    rw [div_le_iff₀ hρ1]
    linarith [hlow (M + j) (by omega)]
  rw [← tendsto_add_atTop_iff_nat (M + 1)]
  refine hj.congr fun j => ?_
  congr 2
  ring_nf

/-- **Pincherle's criterion with a ratio limit.** For a backward solution `w` with `w₀ ≠ 0`,
nonvanishing partial numerators, `w_k` eventually nonzero, and `-w_k/(a_{k+1} w_{k+2}) → ρ`
with `‖ρ‖ > 1`, the convergents of `h + a₀/(b₀ + a₁/(b₁ + ⋯))` tend to `h + a₀ w₁/w₀`. -/
theorem pinch_cfConv_tendsto {h : K} {a b w : ℕ → K}
    (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2)) (hw0 : w 0 ≠ 0)
    (ha : ∀ k, a k ≠ 0) (hwev : ∀ᶠ k in atTop, w k ≠ 0) {ρ : K} (hρ : 1 < ‖ρ‖)
    (hlim : Tendsto (fun k => -(w k / (a (k + 1) * w (k + 2)))) atTop (𝓝 ρ)) :
    Tendsto (cfConv_ofFun h a b).convs atTop (𝓝 (h + a 0 * w 1 / w 0)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hwev
  refine cfConv_tendsto_of_sum hw hw0 ha hN (pinch_norm_sum_tendsto hρ
    (cfConv_T_ne_zero hw0 ha hN) ?_)
  have hshift : Tendsto (fun i => -(w (N + i + 1) / (a (N + i + 2) * w (N + i + 3)))) atTop
      (𝓝 ρ) := by
    have := hlim.comp (tendsto_add_atTop_nat (N + 1))
    refine this.congr fun i => ?_
    simp only [Function.comp_apply, show i + (N + 1) = N + i + 1 by ring,
      show N + i + 1 + 1 = N + i + 2 by ring, show N + i + 1 + 2 = N + i + 3 by ring]
  refine hshift.congr fun i => ?_
  rw [cfConv_T_succ ha hN i, mul_div_cancel_left₀ _ (cfConv_T_ne_zero hw0 ha hN i)]

end GenContFract
