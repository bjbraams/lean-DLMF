/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.SmallQFourierCoefficients
public import DLMF.Mathieu.SecondSolutions
public import DLMF.Mathieu.SpectralContinuity

/-!
# Distribution of the Mathieu eigenvalues

The ordering of the characteristic values `a_n(q)`, `b_n(q)` for real `q ≠ 0` (DLMF 28.2.25).
The inequalities `a_m(q) < a_{m+1}(q)` and `b_m(q) < b_{m+1}(q)` hold for all real `q` (Sturm
interlacing, `DLMF.Mathieu.SmallQSpectrum`). For `m ≥ 1` and `q ≠ 0`, `a_m(q) ≠ b_m(q)` by Ince's
theorem (no two independent solutions of period `2π`); since `a_m`, `b_m` are continuous and
`b_m(q) < a_m(q)` for small `q > 0`, `b_m(q) < a_m(q)` for every `q > 0`. The small-`q` sign
comes from a Green identity for the Fourier recurrences of `ce_m` and `se_m`, which differ only
in row `0`: `(a_m - b_m) ∑ A_j B_j = 2q A_* B_*` with `A_*`, `B_*` the lowest coefficients, whose
leading behaviour `c (q/4)^s A_m`, `c > 0`, is DLMF 28.4.23. The relations
28.2.26–28.2.28 between `q` and `-q` give the remaining inequalities.

Refining the descent through the exact rows of the recurrences to a relative error `O(q²)`
gives the leading term of `a_m(q) - b_m(q)` (DLMF 28.6.15).

## Main results

* `eventually_mathieuB_lt_mathieuA`: `b_m(q) < a_m(q)` for small `q > 0`.
* `mathieuA_ne_mathieuB`: `a_m(q) ≠ b_m(q)` for `m ≥ 1`, `q ≠ 0`.
* `mathieuB_lt_mathieuA`: `b_m(q) < a_m(q)` for `m ≥ 1`, `q > 0`.
* `mathieu_eigenvalues_interlace_pos`, `mathieu_eigenvalues_interlace_neg`: DLMF 28.2.25.
* `isBigO_mathieuA_sub_mathieuB_sub`, `exists_mathieuA_sub_mathieuB_eq`:
  `a_m(q) - b_m(q) = 2q^m/(2^{m-1}(m-1)!)² (1 + O(q²))` (DLMF 28.6.15).
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

/-! ### The sign of `a_m(q) - b_m(q)` for small `q > 0`

The Fourier coefficients of `ce_m` and `se_m` solve two recurrences that differ only in row `0`.
A Green identity gives `(a_m - b_m) ∑ A_j B_j = 2q A_* B_*`, where `A_*`, `B_*` are the lowest
coefficients; by 28.4.23 these are `c (q/4)^s A_m (1 + O(q))` with `c > 0`, so `a_m(q) > b_m(q)`
for small `q > 0`. -/

namespace SmallQFourier

/-- `recurrenceLower 1 x (N + 1) = x N`. -/
private lemma recurrenceLower_one_succ (x : ℕ → ℂ) (N : ℕ) :
    recurrenceLower 1 x (N + 1) = x N := by
  cases N <;> simp [recurrenceLower]

/-- Finite Green identity for two three-term recurrences with the same diagonal, one with a
source term `g` in row `0`. -/
private lemma green_sum {a b q g : ℂ} {D x y : ℕ → ℂ}
    (hx : ∀ j, (a - D j) * x j = q * (recurrenceLower 1 x j + x (j + 1)) +
      if j = 0 then g else 0)
    (hy : ∀ j, (b - D j) * y j = q * (recurrenceLower 1 y j + y (j + 1))) (N : ℕ) :
    (a - b) * ∑ j ∈ Finset.range (N + 1), x j * y j =
      g * y 0 + q * (x (N + 1) * y N - x N * y (N + 1)) := by
  induction N with
  | zero =>
    have h1 := hx 0
    have h2 := hy 0
    simp only [recurrenceLower, zero_add, ↓reduceIte] at h1 h2
    simp only [zero_add, Finset.sum_range_one]
    linear_combination y 0 * h1 - x 0 * h2
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 := hx (N + 1)
    have h2 := hy (N + 1)
    rw [recurrenceLower_one_succ] at h1 h2
    simp only [Nat.succ_ne_zero, ↓reduceIte, add_zero] at h1
    linear_combination y (N + 1) * h1 - x (N + 1) * h2

/-- Green identity in the limit. -/
private lemma mul_tsum_eq {a b q g : ℂ} {D x y : ℕ → ℂ}
    (hx : ∀ j, (a - D j) * x j = q * (recurrenceLower 1 x j + x (j + 1)) +
      if j = 0 then g else 0)
    (hy : ∀ j, (b - D j) * y j = q * (recurrenceLower 1 y j + y (j + 1)))
    (hxl : Tendsto x atTop (𝓝 0)) (hyl : Tendsto y atTop (𝓝 0))
    (hs : Summable (fun j => x j * y j)) :
    (a - b) * ∑' j, x j * y j = g * y 0 := by
  have h1 : Tendsto (fun N => (a - b) * ∑ j ∈ Finset.range (N + 1), x j * y j) atTop
      (𝓝 ((a - b) * ∑' j, x j * y j)) :=
    ((hs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)).const_mul _
  have h2 : Tendsto (fun N => g * y 0 + q * (x (N + 1) * y N - x N * y (N + 1))) atTop
      (𝓝 (g * y 0)) := by
    have := ((hxl.comp (tendsto_add_atTop_nat 1)).mul hyl).sub
      (hxl.mul (hyl.comp (tendsto_add_atTop_nat 1)))
    simpa using (this.const_mul q).const_add (g * y 0)
  simp_rw [green_sum hx hy] at h1
  exact tendsto_nhds_unique h1 h2

/-- `j ↦ (1/2)^{|j - n|}` is summable. -/
private lemma summable_half_pow_dist (n : ℕ) :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ Nat.dist j n) := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun j => ?_)
    (summable_geometric_two.mul_left (2 ^ n))
  have hj : j ≤ Nat.dist j n + n := by unfold Nat.dist; omega
  calc (1 / 2 : ℝ) ^ Nat.dist j n = 2 ^ n * (1 / 2) ^ (Nat.dist j n + n) := by
        rw [pow_add, ← mul_assoc, mul_comm (2 ^ n : ℝ), mul_assoc, ← mul_pow]; norm_num
    _ ≤ 2 ^ n * (1 / 2) ^ j := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hj) (by positivity)

/-- The sum `∑ x_j y_j` of two sequences decaying geometrically from the index `n` is close to
its `n`-th term. -/
private lemma summable_and_norm_tsum_sub_le {x y : ℕ → ℂ} {n : ℕ} {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ^ 2 ≤ 1 / 2)
    (hxd : ∀ j, ‖x j‖ ≤ r ^ Nat.dist j n * ‖x n‖) (hyd : ∀ j, ‖y j‖ ≤ r ^ Nat.dist j n * ‖y n‖) :
    Summable (fun j => x j * y j) ∧
      ‖∑' j, x j * y j - x n * y n‖ ≤
        2 * r ^ 2 * (∑' j, (1 / 2 : ℝ) ^ Nat.dist j n) * ‖x n * y n‖ := by
  have hb : ∀ j, ‖x j * y j‖ ≤ (r ^ 2) ^ Nat.dist j n * ‖x n * y n‖ := by
    intro j
    rw [norm_mul, norm_mul, ← pow_mul, mul_comm 2, pow_mul, sq]
    calc ‖x j‖ * ‖y j‖ ≤ (r ^ Nat.dist j n * ‖x n‖) * (r ^ Nat.dist j n * ‖y n‖) :=
          mul_le_mul (hxd j) (hyd j) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hb2 : ∀ j, (r ^ 2) ^ Nat.dist j n ≤ (1 / 2 : ℝ) ^ Nat.dist j n := fun j =>
    pow_le_pow_left₀ (by positivity) hr _
  have hs : Summable (fun j => x j * y j) := by
    refine Summable.of_norm_bounded ((summable_half_pow_dist n).mul_right ‖x n * y n‖)
      (fun j => (hb j).trans ?_)
    gcongr
  refine ⟨hs, ?_⟩
  rw [hs.tsum_eq_add_tsum_ite n, add_sub_cancel_left]
  have hg : HasSum (fun j => 2 * r ^ 2 * ‖x n * y n‖ * (1 / 2 : ℝ) ^ Nat.dist j n)
      (2 * r ^ 2 * ‖x n * y n‖ * ∑' j, (1 / 2 : ℝ) ^ Nat.dist j n) :=
    (summable_half_pow_dist n).hasSum.mul_left _
  calc _ ≤ 2 * r ^ 2 * ‖x n * y n‖ * ∑' j, (1 / 2 : ℝ) ^ Nat.dist j n :=
        tsum_of_norm_bounded hg (fun j => ?_)
    _ = _ := by ring
  split_ifs with hj
  · rw [norm_zero]; positivity
  · have hd : 1 ≤ Nat.dist j n := by
      rcases Nat.lt_or_gt_of_ne hj with h | h <;> unfold Nat.dist <;> omega
    refine (hb j).trans ?_
    obtain ⟨k, hk⟩ : ∃ k, Nat.dist j n = k + 1 := ⟨Nat.dist j n - 1, by omega⟩
    rw [hk, pow_succ, pow_succ]
    have := pow_le_pow_left₀ (by positivity) hr k
    have h0 : 0 ≤ ‖x n * y n‖ := norm_nonneg _
    have h1 : 0 ≤ r ^ 2 := by positivity
    calc (r ^ 2) ^ k * r ^ 2 * ‖x n * y n‖ ≤ (1 / 2) ^ k * r ^ 2 * ‖x n * y n‖ := by gcongr
      _ = 2 * r ^ 2 * ‖x n * y n‖ * ((1 / 2) ^ k * (1 / 2)) := by ring

/-- If `r (1 + ρ) = P (1 + η)` with `r`, `P` real, `P > 0` and `‖ρ‖, ‖η‖ < 1`, then `r > 0`. -/
private lemma pos_of_mul_one_add_eq {r P : ℝ} {ρ η : ℂ} (hρ : ‖ρ‖ < 1) (hη : ‖η‖ < 1)
    (hP : 0 < P) (h : (r : ℂ) * (1 + ρ) = P * (1 + η)) : 0 < r := by
  have hre := congrArg Complex.re h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.one_re, Complex.add_im, Complex.one_im, zero_mul, sub_zero] at hre
  have h1 := (abs_le.mp (Complex.abs_re_le_norm ρ)).1
  have h2 := (abs_le.mp (Complex.abs_re_le_norm η)).1
  have hpos : 0 < r * (1 + ρ.re) := by rw [hre]; exact mul_pos hP (by linarith)
  exact (pos_iff_pos_of_mul_pos hpos).2 (by linarith)

/-- The sign argument: from the Green identity `(a - b) ∑ x_j y_j = 2q X₀ Y₀`, with
`∑ x_j y_j ≈ x_n y_n`, `X₀ ≈ α x_n`, `Y₀ ≈ β y_n`, `α, β > 0`, `q > 0`, follows `b < a`. -/
private lemma lt_of_green {a b q α β : ℝ} {x y : ℕ → ℂ} {n : ℕ} {X0 Y0 εA εB : ℂ}
    (hq : 0 < q) (hα : 0 < α) (hβ : 0 < β)
    (hgreen : ((a : ℂ) - b) * ∑' j, x j * y j = 2 * q * X0 * Y0)
    (hS : ‖∑' j, x j * y j - x n * y n‖ ≤ 1 / 2 * ‖x n * y n‖)
    (hX0 : X0 = (α + εA) * x n) (hY0 : Y0 = (β + εB) * y n)
    (hεA : ‖εA‖ ≤ α / 4) (hεB : ‖εB‖ ≤ β / 4) (hxn : x n ≠ 0) (hyn : y n ≠ 0) : b < a := by
  have hP : x n * y n ≠ 0 := mul_ne_zero hxn hyn
  have hPn := norm_pos_iff.2 hP
  set S := ∑' j, x j * y j with hSdef
  have hρ : ‖(S - x n * y n) / (x n * y n)‖ < 1 := by
    rw [norm_div, div_lt_one hPn]; linarith
  have hu : ‖εA / α‖ ≤ 1 / 4 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hα.le, div_le_iff₀ hα]; linarith
  have hv : ‖εB / β‖ ≤ 1 / 4 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hβ.le, div_le_iff₀ hβ]; linarith
  have hη : ‖εA / α + εB / β + εA / α * (εB / β)‖ < 1 := by
    calc _ ≤ ‖εA / α‖ + ‖εB / β‖ + ‖εA / α‖ * ‖εB / β‖ := by
          rw [← norm_mul]; exact norm_add₃_le
      _ < 1 := by nlinarith [norm_nonneg (εA / α), norm_nonneg (εB / β)]
  have hα' : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  refine sub_pos.1 (pos_of_mul_one_add_eq (r := a - b) (P := 2 * q * α * β) hρ hη
    (by positivity) ?_)
  apply mul_right_cancel₀ hP
  rw [hX0, hY0] at hgreen
  have e1 : (1 + (S - x n * y n) / (x n * y n)) * (x n * y n) = S := by field_simp; ring
  have e2 : (α : ℂ) * β * (1 + (εA / α + εB / β + εA / α * (εB / β))) = (α + εA) * (β + εB) := by
    field_simp; ring
  push_cast
  linear_combination ((a : ℂ) - b) * e1 + hgreen - 2 * (q : ℂ) * (x n * y n) * e2


/-- Smallness of `r = 3|q|` for the sum estimate. -/
private lemma eventually_three_mul_abs_small (T : ℝ) (hT : 0 ≤ T) :
    ∀ᶠ q : ℝ in 𝓝 0, (3 * |q|) ^ 2 ≤ 1 / 2 ∧ 2 * (3 * |q|) ^ 2 * T ≤ 1 / 2 := by
  have h : Tendsto (fun q : ℝ => (3 * |q|) ^ 2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun q : ℝ => (3 * |q|) ^ 2) := by fun_prop
    simpa using hc.tendsto (0 : ℝ)
  filter_upwards [h.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    h.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < 1 / (4 * (T + 1))))] with q h1 h2
  refine ⟨h1, ?_⟩
  have h3 : (3 * |q|) ^ 2 * (4 * (T + 1)) ≤ 1 := by
    rwa [le_div_iff₀ (by positivity)] at h2
  nlinarith [sq_nonneg (3 * |q|)]

/-- A coefficient that is `o(q^s)` is eventually at most `α/4` with `α = c (q/4)^s`. -/
private lemma eventually_norm_le_quarter {ε : ℝ → ℂ} {s : ℕ} {c : ℝ} (hc : 0 < c)
    (h : ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1))) :
    ∀ᶠ q : ℝ in 𝓝[>] 0, ‖ε q‖ ≤ c * (q / 4) ^ s / 4 := by
  have ho : ε =o[𝓝 0] (fun q : ℝ => q ^ s) := h.trans_isLittleO (isLittleO_pow_pow (by omega))
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (ho.def (c := c / 4 ^ s / 4) (by positivity))]
    with q hq h1
  rw [norm_pow, Real.norm_of_nonneg (le_of_lt hq)] at h1
  calc ‖ε q‖ ≤ c / 4 ^ s / 4 * q ^ s := h1
    _ = c * (q / 4) ^ s / 4 := by rw [div_pow]; ring

/-- From the decay estimate, the `n`-th coefficient is nonzero. -/
private lemma ne_zero_of_decay {x : ℕ → ℂ} {n : ℕ} {r : ℝ}
    (hd : ∀ j, ‖x j‖ ≤ r ^ Nat.dist j n * ‖x n‖)
    (hne : ∃ j, x j ≠ 0) : x n ≠ 0 := by
  intro h
  obtain ⟨j, hj⟩ := hne
  have := hd j
  rw [h, norm_zero, mul_zero] at this
  exact hj (norm_le_zero_iff.mp this)

/-- **Sign of `a_m - b_m` for small `q > 0`**, odd `m`. -/
private lemma eventually_mathieuB_lt_mathieuA_odd (n : ℕ) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ), mathieuB (2 * n + 1) q < mathieuA (2 * n + 1) q := by
  obtain ⟨εA, hA1, hA2⟩ := mathieuFourierA_down_small_q' (m := 2 * n + 1) (s := n) (by omega)
  obtain ⟨εB, hB1, hB2⟩ := mathieuFourierB_down_small_q' (m := 2 * n + 1) (s := n) (by omega)
  set c : ℝ := ((2 * n + 1 - n - 1).factorial : ℝ) /
    ((n.factorial : ℝ) * ((2 * n + 1 - 1).factorial : ℝ)) with hc
  have hc0 : 0 < c := by positivity
  have hcC : (((2 * n + 1 - n - 1).factorial : ℂ) /
      ((n.factorial : ℂ) * ((2 * n + 1 - 1).factorial : ℂ))) = (c : ℂ) := by
    simp only [hc]; push_cast; rfl
  set T := ∑' j, (1 / 2 : ℝ) ^ Nat.dist j n
  have hT : 0 ≤ T := tsum_nonneg fun _ => by positivity
  have gA := eventually_one_le_norm_sub_diagonal (δ := 1) (n := n) (m := 2 * n + 1)
    (a := fun q => (mathieuA (2 * n + 1) q : ℂ)) rfl norm_odd_sq_add_ite_sub_sq_le
    (eventually_norm_mathieuA_sub_sq_le (2 * n + 1))
  have gB := eventually_one_le_norm_sub_diagonal (δ := 1) (n := n) (m := 2 * n + 1)
    (a := fun q => (mathieuB (2 * n + 1) q : ℂ)) rfl norm_odd_sq_sub_ite_sub_sq_le
    (eventually_norm_mathieuB_sub_sq_le (by omega))
  filter_upwards [self_mem_nhdsWithin, eventually_norm_le_quarter hc0 hA1,
    eventually_norm_le_quarter hc0 hB1,
    eventually_nhdsWithin_of_eventually_nhds (hA2.and (hB2.and (gA.and (gB.and
      (eventually_three_mul_abs_small T hT)))))]
    with q hq eA eB hall
  obtain ⟨hA, hB, ⟨h8, -, gapA⟩, ⟨-, -, gapB⟩, hr1, hr2⟩ := hall
  have hq0 : 0 < q := hq
  set x : ℕ → ℂ := fun j => mathieuFourierA (2 * n + 1) (2 * j + 1) q with hxdef
  set y : ℕ → ℂ := fun j => mathieuFourierB (2 * n + 1) (2 * j + 1) q with hydef
  have hq4 : ‖(q : ℂ)‖ ≤ 1 / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have hqn : ‖(q : ℂ)‖ = |q| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hdx := norm_le_pow_dist_mul_of_solvesRecurrence (by norm_num)
    (solvesRecurrence_mathieuFourierA_odd n q) (tendsto_mathieuFourierA_odd n q) hq4 gapA
  have hdy := norm_le_pow_dist_mul_of_solvesRecurrence (by norm_num)
    (solvesRecurrence_mathieuFourierB_odd n q) (tendsto_mathieuFourierB_odd n q) hq4 gapB
  rw [hqn] at hdx hdy
  obtain ⟨hs, hS⟩ := summable_and_norm_tsum_sub_le (x := x) (y := y) (by positivity) hr1 hdx hdy
  have hS' : ‖∑' j, x j * y j - x n * y n‖ ≤ 1 / 2 * ‖x n * y n‖ :=
    hS.trans (by gcongr)
  have hgreen := mul_tsum_eq (a := (mathieuA (2 * n + 1) q : ℂ))
    (b := (mathieuB (2 * n + 1) q : ℂ)) (q := q) (g := 2 * q * x 0)
    (D := fun j => (2 * (j : ℂ) + 1) ^ 2 - if j = 0 then (q : ℂ) else 0) (x := x) (y := y)
    (fun j => by
      have := solvesRecurrence_mathieuFourierA_odd n q j
      simp only [recurrenceOperator] at this
      rcases j with _ | j
      · simp only [↓reduceIte] at this ⊢; linear_combination -this
      · simp only [Nat.succ_ne_zero, ↓reduceIte, add_zero, sub_zero] at this ⊢
        linear_combination -this)
    (fun j => by
      have := solvesRecurrence_mathieuFourierB_odd n q j
      simp only [recurrenceOperator] at this
      linear_combination -this)
    (tendsto_mathieuFourierA_odd n q) (tendsto_mathieuFourierB_odd n q) hs
  refine lt_of_green (α := c * (q / 4) ^ n) (β := c * (q / 4) ^ n) (εA := εA q) (εB := εB q)
    (X0 := x 0) (Y0 := y 0) (n := n) hq0 (by positivity) (by positivity)
    (hgreen.trans (by ring)) hS' ?_ ?_ eA eB
    (ne_zero_of_decay hdx (exists_mathieuFourierA_odd_ne_zero n q))
    (ne_zero_of_decay hdy (exists_mathieuFourierB_odd_ne_zero n q))
  · show mathieuFourierA (2 * n + 1) (2 * 0 + 1) q = _
    rw [show 2 * 0 + 1 = 2 * n + 1 - 2 * n by omega, hA, hcC]; push_cast; ring
  · show mathieuFourierB (2 * n + 1) (2 * 0 + 1) q = _
    rw [show 2 * 0 + 1 = 2 * n + 1 - 2 * n by omega, hB, hcC]; push_cast; ring


/-- **Sign of `a_m - b_m` for small `q > 0`**, even `m ≥ 2`. -/
private lemma eventually_mathieuB_lt_mathieuA_even (n : ℕ) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ), mathieuB (2 * n + 2) q < mathieuA (2 * n + 2) q := by
  obtain ⟨εA, hA1, hA2⟩ := mathieuFourierA_down_small_q' (m := 2 * n + 2) (s := n + 1) (by omega)
  obtain ⟨εB, hB1, hB2⟩ := mathieuFourierB_down_small_q' (m := 2 * n + 2) (s := n) (by omega)
  set cA : ℝ := ((2 * n + 2 - (n + 1) - 1).factorial : ℝ) /
    (((n + 1).factorial : ℝ) * ((2 * n + 2 - 1).factorial : ℝ)) with hcA
  set cB : ℝ := ((2 * n + 2 - n - 1).factorial : ℝ) /
    ((n.factorial : ℝ) * ((2 * n + 2 - 1).factorial : ℝ)) with hcB
  have hcA0 : 0 < cA := by positivity
  have hcB0 : 0 < cB := by positivity
  have hcAC : (((2 * n + 2 - (n + 1) - 1).factorial : ℂ) /
      (((n + 1).factorial : ℂ) * ((2 * n + 2 - 1).factorial : ℂ))) = (cA : ℂ) := by
    simp only [hcA]; push_cast; rfl
  have hcBC : (((2 * n + 2 - n - 1).factorial : ℂ) /
      ((n.factorial : ℂ) * ((2 * n + 2 - 1).factorial : ℂ))) = (cB : ℂ) := by
    simp only [hcB]; push_cast; rfl
  set T := ∑' j, (1 / 2 : ℝ) ^ Nat.dist j n
  have hT : 0 ≤ T := tsum_nonneg fun _ => by positivity
  have hAs : ∀ q : ℝ, SolvesRecurrence (fun i => 4 * (i : ℂ) ^ 2) 2 q (mathieuA (2 * n + 2) q)
      (fun i => mathieuFourierA (2 * n + 2) (2 * i) q) := fun q => by
    have := solvesRecurrence_mathieuFourierA_even (n + 1) q
    rwa [show 2 * (n + 1) = 2 * n + 2 by ring] at this
  have hAl : ∀ q : ℝ, Tendsto (fun i => mathieuFourierA (2 * n + 2) (2 * i) q) atTop (𝓝 0) :=
    fun q => by
      have := tendsto_mathieuFourierA_even (n + 1) q
      rwa [show 2 * (n + 1) = 2 * n + 2 by ring] at this
  have gA := eventually_one_le_norm_sub_diagonal (δ := 0) (n := n + 1) (m := 2 * n + 2)
    (a := fun q => (mathieuA (2 * n + 2) q : ℂ)) (by ring) norm_four_mul_sq_sub_sq_le
    (eventually_norm_mathieuA_sub_sq_le (2 * n + 2))
  have gB := eventually_one_le_norm_sub_diagonal (δ := 2) (n := n) (m := 2 * n + 2)
    (a := fun q => (mathieuB (2 * n + 2) q : ℂ)) rfl norm_two_mul_add_two_sq_sub_sq_le
    (eventually_norm_mathieuB_sub_sq_le (by omega))
  filter_upwards [self_mem_nhdsWithin, eventually_norm_le_quarter hcA0 hA1,
    eventually_norm_le_quarter hcB0 hB1,
    eventually_nhdsWithin_of_eventually_nhds (hA2.and (hB2.and (gA.and (gB.and
      (eventually_three_mul_abs_small T hT)))))]
    with q hq eA eB hall
  obtain ⟨hA, hB, ⟨h8, -, gapA⟩, ⟨-, -, gapB⟩, hr1, hr2⟩ := hall
  have hq0 : 0 < q := hq
  set z : ℕ → ℂ := fun i => mathieuFourierA (2 * n + 2) (2 * i) q with hzdef
  set x : ℕ → ℂ := fun j => z (j + 1) with hxdef
  set y : ℕ → ℂ := fun j => mathieuFourierB (2 * n + 2) (2 * j + 2) q with hydef
  have hq4 : ‖(q : ℂ)‖ ≤ 1 / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have hqn : ‖(q : ℂ)‖ = |q| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hdz := norm_le_pow_dist_mul_of_solvesRecurrence (by norm_num) (hAs q) (hAl q) hq4 gapA
  have hdy := norm_le_pow_dist_mul_of_solvesRecurrence (by norm_num)
    (solvesRecurrence_mathieuFourierB_even n q) (tendsto_mathieuFourierB_even n q) hq4 gapB
  rw [hqn] at hdz hdy
  have hdx : ∀ j, ‖x j‖ ≤ (3 * |q|) ^ Nat.dist j n * ‖x n‖ := fun j => by
    have := hdz (j + 1)
    rwa [show Nat.dist (j + 1) (n + 1) = Nat.dist j n by unfold Nat.dist; omega] at this
  obtain ⟨hs, hS⟩ := summable_and_norm_tsum_sub_le (x := x) (y := y) (by positivity) hr1 hdx hdy
  have hS' : ‖∑' j, x j * y j - x n * y n‖ ≤ 1 / 2 * ‖x n * y n‖ :=
    hS.trans (by gcongr)
  have hxl : Tendsto x atTop (𝓝 0) := (hAl q).comp (tendsto_add_atTop_nat 1)
  have hgreen := mul_tsum_eq (a := (mathieuA (2 * n + 2) q : ℂ))
    (b := (mathieuB (2 * n + 2) q : ℂ)) (q := q) (g := 2 * q * z 0)
    (D := fun j => (2 * (j : ℂ) + 2) ^ 2) (x := x) (y := y)
    (fun j => by
      have := hAs q (j + 1)
      simp only [recurrenceOperator] at this
      rcases j with _ | j
      · simp only [recurrenceLower, ↓reduceIte] at this ⊢
        push_cast at this ⊢
        linear_combination -this
      · simp only [Nat.succ_ne_zero, ↓reduceIte, add_zero, recurrenceLower_one_succ] at this ⊢
        simp only [recurrenceLower] at this
        push_cast at this ⊢
        linear_combination -this)
    (fun j => by
      have := solvesRecurrence_mathieuFourierB_even n q j
      simp only [recurrenceOperator] at this
      linear_combination -this)
    hxl (tendsto_mathieuFourierB_even n q) hs
  refine lt_of_green (α := cA * (q / 4) ^ (n + 1)) (β := cB * (q / 4) ^ n) (εA := εA q)
    (εB := εB q) (X0 := z 0) (Y0 := y 0) (n := n) hq0 (by positivity) (by positivity)
    (hgreen.trans (by ring)) hS' ?_ ?_ eA eB
    (ne_zero_of_decay hdx ?_) (ne_zero_of_decay hdy (exists_mathieuFourierB_even_ne_zero n q))
  · show mathieuFourierA (2 * n + 2) (2 * 0) q = _
    rw [show 2 * 0 = 2 * n + 2 - 2 * (n + 1) by omega, hA, hcAC]
    show _ = _ * mathieuFourierA (2 * n + 2) (2 * (n + 1)) q
    rw [show 2 * (n + 1) = 2 * n + 2 by ring]; push_cast; ring
  · show mathieuFourierB (2 * n + 2) (2 * 0 + 2) q = _
    rw [show 2 * 0 + 2 = 2 * n + 2 - 2 * n by omega, hB, hcBC]; push_cast; ring
  · obtain ⟨i, hi⟩ := exists_mathieuFourierA_even_ne_zero (n + 1) q
    rw [show 2 * (n + 1) = 2 * n + 2 by ring] at hi
    rcases i with _ | i
    · -- `A_0 ≠ 0` forces `A_{2n+2} ≠ 0` by the decay of `z`
      refine ⟨n, fun h => hi ?_⟩
      have := hdz 0
      have h' : mathieuFourierA (2 * n + 2) (2 * (n + 1)) q = 0 := h
      rw [h', norm_zero, mul_zero] at this
      exact norm_le_zero_iff.mp (by simpa using this)
    · exact ⟨i, hi⟩

end SmallQFourier

open SmallQFourier in
/-- **Sign of `a_m(q) - b_m(q)` for small `q > 0`**: `b_m(q) < a_m(q)`, `m ≥ 1`. -/
theorem eventually_mathieuB_lt_mathieuA {m : ℕ} (hm : m ≠ 0) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ), mathieuB m q < mathieuA m q := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (n + 1) = 2 * n + 2 by ring]
    exact eventually_mathieuB_lt_mathieuA_even n
  · exact eventually_mathieuB_lt_mathieuA_odd k

/-- **No coexistence** (Ince, DLMF §28.2(v)): for `q ≠ 0` and `m ≥ 1`, `a_m(q) ≠ b_m(q)`. -/
theorem mathieuA_ne_mathieuB {m : ℕ} (hm : m ≠ 0) {q : ℝ} (hq : q ≠ 0) :
    mathieuA m q ≠ mathieuB m q := by
  intro h
  have hsq : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
  refine not_mathieuWI_mathieuWII_two_pi_periodic (a := (mathieuA m q : ℂ)) (q := q)
    (by exact_mod_cast hq) (fun z => ?_) (fun z => ?_)
  · rw [show z + 2 * (π : ℂ) = z + π + π by ring, mathieuWI_mathieuA_add_pi,
      mathieuWI_mathieuA_add_pi, ← mul_assoc, hsq, one_mul]
  · rw [h, show z + 2 * (π : ℂ) = z + π + π by ring, mathieuWII_mathieuB_add_pi hm,
      mathieuWII_mathieuB_add_pi hm, ← mul_assoc, hsq, one_mul]

/-- `b_m(q) < a_m(q)` for `q > 0` and `m ≥ 1` (DLMF 28.2.25). -/
theorem mathieuB_lt_mathieuA {m : ℕ} (hm : m ≠ 0) {q : ℝ} (hq : 0 < q) :
    mathieuB m q < mathieuA m q := by
  refine lt_of_not_ge fun hle => ?_
  obtain ⟨q₀, hq₀, hq₀'⟩ :=
    ((eventually_mathieuB_lt_mathieuA hm).and (Ioo_mem_nhdsGT hq)).exists
  have hcont : ContinuousOn (fun p => mathieuA m p - mathieuB m p) (Icc q₀ q) :=
    ((continuous_mathieuA m).sub (continuous_mathieuB m)).continuousOn
  have h0 : (0 : ℝ) ∈ Icc (mathieuA m q - mathieuB m q) (mathieuA m q₀ - mathieuB m q₀) :=
    ⟨by linarith, by linarith [hq₀]⟩
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hq₀'.2.le hcont h0
  exact mathieuA_ne_mathieuB hm (q := c) (by linarith [hc.1, hq₀'.1]) (sub_eq_zero.1 hc0)

/-- **Distribution of the eigenvalues** (DLMF 28.2.25), `q > 0`:
`a_0 < b_1 < a_1 < b_2 < a_2 < b_3 < ⋯`. -/
@[dlmf 28.2.E25]
theorem mathieu_eigenvalues_interlace_pos {q : ℝ} (hq : 0 < q) (n : ℕ) :
    mathieuA n q < mathieuB (n + 1) q ∧ mathieuB (n + 1) q < mathieuA (n + 1) q := by
  refine ⟨?_, mathieuB_lt_mathieuA (by omega) hq⟩
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have := mathieuA_lt_mathieuA_succ (2 * k) (-q)
    rwa [mathieuA_even_neg, mathieuA_odd_neg] at this
  · have := mathieuB_lt_mathieuB_succ (m := 2 * k + 1) (by omega) (-q)
    rwa [← mathieuA_odd_neg k (-q), neg_neg, show 2 * k + 1 + 1 = 2 * k + 2 by ring,
      mathieuB_even_neg] at this

/-- **Distribution of the eigenvalues** (DLMF 28.2.25), `q < 0`:
`a_0 < a_1 < b_1 < b_2 < a_2 < a_3 < b_3 < b_4 < ⋯`. -/
@[dlmf 28.2.E25]
theorem mathieu_eigenvalues_interlace_neg {q : ℝ} (hq : q < 0) (n : ℕ) :
    mathieuA (2 * n) q < mathieuA (2 * n + 1) q ∧
      mathieuA (2 * n + 1) q < mathieuB (2 * n + 1) q ∧
      mathieuB (2 * n + 1) q < mathieuB (2 * n + 2) q ∧
      mathieuB (2 * n + 2) q < mathieuA (2 * n + 2) q := by
  have hq' : 0 < -q := by linarith
  refine ⟨mathieuA_lt_mathieuA_succ _ q, ?_, mathieuB_lt_mathieuB_succ (by omega) q, ?_⟩
  · have := mathieuB_lt_mathieuA (m := 2 * n + 1) (by omega) hq'
    rwa [← mathieuA_odd_neg n (-q), neg_neg, mathieuA_odd_neg] at this
  · have := mathieuB_lt_mathieuA (m := 2 * n + 2) (by omega) hq'
    rwa [mathieuB_even_neg, show 2 * n + 2 = 2 * (n + 1) by ring, mathieuA_even_neg] at this

/-! ### The leading term of `a_m(q) - b_m(q)`

Through the rows of the recurrences whose diagonal is exactly `(2i+δ)²` the descent of 28.4.23
gains a factor `q²` per step once `a - m² = O(q²)` is known; this gives the lowest coefficients
with relative error `O(q²)` and, through the Green identity, 28.6.15. -/

namespace SmallQFourier

/-- One step of the refined induction: with `‖E - D‖ ≤ K q²` the error gains a factor `q²`. -/
private lemma step_bound_sq {q : ℝ} {D E X Y L An c : ℂ} {C K : ℝ} {k : ℕ}
    (hrow : D * X = q * (L + Y)) (hD : 1 ≤ ‖D‖)
    (hY : ‖Y - c * (q : ℂ) ^ k * An‖ ≤ C * (|q| ^ (k + 2) * ‖An‖))
    (hL : ‖L‖ ≤ 2 * ((3 * |q|) ^ (k + 2) * ‖An‖)) (hED : ‖E - D‖ ≤ K * q ^ 2) (hE : E ≠ 0) :
    ‖X - c / E * (q : ℂ) ^ (k + 1) * An‖ ≤
      (C + 2 * 3 ^ (k + 2) + K * ‖c‖ / ‖E‖) * (|q| ^ (k + 3) * ‖An‖) := by
  have hD0 : D ≠ 0 := by rintro rfl; simp at hD; linarith
  have key : X - c / E * (q : ℂ) ^ (k + 1) * An =
      ((q : ℂ) * (Y - c * (q : ℂ) ^ k * An) + q * L +
        c * (q : ℂ) ^ (k + 1) * An * ((E - D) / E)) / D := by
    rw [eq_div_iff hD0]
    have hc : c * E * E⁻¹ = c := by field_simp
    linear_combination hrow - ((q : ℂ) * (q : ℂ) ^ k * An) * hc
  have hqn : ‖(q : ℂ)‖ = |q| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hA := norm_nonneg An
  have hq0 := abs_nonneg q
  have t1 : ‖(q : ℂ) * (Y - c * (q : ℂ) ^ k * An)‖ ≤ C * (|q| ^ (k + 3) * ‖An‖) := by
    rw [norm_mul, hqn]
    calc |q| * ‖Y - c * (q : ℂ) ^ k * An‖ ≤ |q| * (C * (|q| ^ (k + 2) * ‖An‖)) := by gcongr
      _ = _ := by ring
  have t2 : ‖(q : ℂ) * L‖ ≤ 2 * 3 ^ (k + 2) * (|q| ^ (k + 3) * ‖An‖) := by
    rw [norm_mul, hqn]
    calc |q| * ‖L‖ ≤ |q| * (2 * ((3 * |q|) ^ (k + 2) * ‖An‖)) := by gcongr
      _ = _ := by rw [mul_pow]; ring
  have t3 : ‖c * (q : ℂ) ^ (k + 1) * An * ((E - D) / E)‖ ≤
      K * ‖c‖ / ‖E‖ * (|q| ^ (k + 3) * ‖An‖) := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, hqn, norm_div]
    have hE' : 0 < ‖E‖ := norm_pos_iff.2 hE
    calc ‖c‖ * |q| ^ (k + 1) * ‖An‖ * (‖E - D‖ / ‖E‖)
        ≤ ‖c‖ * |q| ^ (k + 1) * ‖An‖ * (K * q ^ 2 / ‖E‖) := by gcongr
      _ = _ := by rw [← sq_abs q]; field_simp; ring
  rw [key, norm_div]
  calc _ ≤ ‖(q : ℂ) * (Y - c * (q : ℂ) ^ k * An) + q * L +
        c * (q : ℂ) ^ (k + 1) * An * ((E - D) / E)‖ :=
        div_le_self (norm_nonneg _) hD
    _ ≤ _ := norm_add₃_le.trans (by linarith)

/-- The eigenvalue is `m² + O(q²)` when row `n` has the exact diagonal entry `m²`. -/
private lemma eventually_norm_sub_sq_le_nine_mul_sq {δ n m : ℕ} {β : ℂ} {d : ℝ → ℕ → ℂ}
    {a : ℝ → ℂ} {A : ℝ → ℕ → ℂ} (hm : m = 2 * n + δ) (hβ : ‖β‖ ≤ 2)
    (hrec : ∀ q : ℝ, SolvesRecurrence (d q) β q (a q) (A q))
    (hlim : ∀ q, Tendsto (A q) atTop (𝓝 0))
    (hd : ∀ q i, ‖d q i - (((2 * i + δ : ℕ) : ℂ)) ^ 2‖ ≤ |q|)
    (ha : ∀ᶠ q in 𝓝 0, ‖a q - (m : ℂ) ^ 2‖ ≤ 4 * |q|) (hdn : ∀ q, d q n = (m : ℂ) ^ 2)
    (hne : ∀ q, ∃ i, A q i ≠ 0) :
    ∀ᶠ q : ℝ in 𝓝 0, ‖a q - (m : ℂ) ^ 2‖ ≤ 9 * q ^ 2 := by
  filter_upwards [eventually_one_le_norm_sub_diagonal hm hd ha] with q hall
  obtain ⟨h8, -, hgap⟩ := hall
  have hq4 : ‖(q : ℂ)‖ ≤ 1 / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have hqn : ‖(q : ℂ)‖ = |q| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hdec := norm_le_pow_dist_mul_of_solvesRecurrence hβ (hrec q) (hlim q) hq4 hgap
  rw [hqn] at hdec
  have hAn : A q n ≠ 0 := ne_zero_of_decay hdec (hne q)
  have hrow : (a q - (m : ℂ) ^ 2) * A q n =
      q * (recurrenceLower β (A q) n + A q (n + 1)) := by
    have := hrec q n
    simp only [recurrenceOperator, hdn] at this
    linear_combination -this
  have hL : ‖recurrenceLower β (A q) n‖ ≤ 2 * (3 * |q| * ‖A q n‖) :=
    norm_recurrenceLower_le hβ (A q) (by positivity) fun j hj => by
      have := hdec j
      rwa [show Nat.dist j n = 1 by simp [Nat.dist]; omega, pow_one] at this
  have hU : ‖A q (n + 1)‖ ≤ 3 * |q| * ‖A q n‖ := by
    have := hdec (n + 1)
    rwa [show Nat.dist (n + 1) n = 1 by simp [Nat.dist], pow_one] at this
  have hpos := norm_pos_iff.2 hAn
  have key : ‖a q - (m : ℂ) ^ 2‖ * ‖A q n‖ ≤ 9 * q ^ 2 * ‖A q n‖ := by
    rw [← norm_mul, hrow, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |q| * ‖recurrenceLower β (A q) n + A q (n + 1)‖
        ≤ |q| * (2 * (3 * |q| * ‖A q n‖) + 3 * |q| * ‖A q n‖) := by
          gcongr; exact (norm_add_le _ _).trans (add_le_add hL hU)
      _ = 9 * q ^ 2 * ‖A q n‖ := by rw [← sq_abs q]; ring
  exact le_of_mul_le_mul_right key hpos

/-- **Refined downward estimate**: if the rows `n - s, …, n - 1` have exact diagonal entries
and `a = m² + O(q²)`, then `A_{n-k} = c_k q^k A_n + O(q^{k+2} A_n)`. -/
private lemma down_isBigO_sq {δ n m s : ℕ} {β : ℂ} {d : ℝ → ℕ → ℂ} {a : ℝ → ℂ}
    {A : ℝ → ℕ → ℂ} (hm : m = 2 * n + δ) (hβ : ‖β‖ ≤ 2)
    (hrec : ∀ q : ℝ, SolvesRecurrence (d q) β q (a q) (A q))
    (hlim : ∀ q, Tendsto (A q) atTop (𝓝 0))
    (hd : ∀ q i, ‖d q i - (((2 * i + δ : ℕ) : ℂ)) ^ 2‖ ≤ |q|)
    (ha : ∀ᶠ q in 𝓝 0, ‖a q - (m : ℂ) ^ 2‖ ≤ 4 * |q|)
    (ha2 : ∀ᶠ q in 𝓝 0, ‖a q - (m : ℂ) ^ 2‖ ≤ 9 * q ^ 2)
    (hdiag : ∀ q i, n - s ≤ i → i < n → d q i = (((2 * i + δ : ℕ) : ℂ)) ^ 2) (hs : s ≤ n) :
    ∀ k ≤ s, (fun q : ℝ => A q (n - k) - descendingCoefficient m k * (q : ℂ) ^ k * A q n)
      =O[𝓝 0] (fun q : ℝ => q ^ (k + 2) * ‖A q n‖) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [Nat.sub_zero, descendingCoefficient_zero, pow_zero, one_mul, sub_self]
    exact isBigO_zero _ _
  | succ k ih =>
    intro hk
    obtain ⟨C, hC⟩ := (ih (by omega)).bound
    set i := n - (k + 1) with hi
    set E : ℂ := (m : ℂ) ^ 2 - (((2 * i + δ : ℕ) : ℂ)) ^ 2 with hEdef
    have hE : E ≠ 0 := (sq_sub_sq_descending hm (by omega)).2
    refine IsBigO.of_bound (C + 2 * 3 ^ (k + 2) + 9 * ‖descendingCoefficient m k‖ / ‖E‖) ?_
    filter_upwards [hC, eventually_one_le_norm_sub_diagonal hm hd ha, ha2]
      with q hq hall ha2q
    obtain ⟨h8, ham, hgap⟩ := hall
    have hpn : ∀ (j : ℕ) (x : ℂ), ‖q ^ j * ‖x‖‖ = |q| ^ j * ‖x‖ := fun j x => by
      rw [norm_mul, norm_pow, Real.norm_eq_abs, norm_norm]
    rw [hpn] at hq ⊢
    have hq4 : ‖(q : ℂ)‖ ≤ 1 / 4 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; linarith
    have hqn : ‖(q : ℂ)‖ = |q| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have hdec := norm_le_pow_dist_mul_of_solvesRecurrence hβ (hrec q) (hlim q) hq4 hgap
    rw [hqn] at hdec
    have hrow : (a q - d q i) * A q i = q * (recurrenceLower β (A q) i + A q (n - k)) := by
      have := hrec q i
      simp only [recurrenceOperator] at this
      rw [show i + 1 = n - k by omega] at this
      linear_combination -this
    have hL : ‖recurrenceLower β (A q) i‖ ≤ 2 * ((3 * |q|) ^ (k + 2) * ‖A q n‖) :=
      norm_recurrenceLower_le hβ (A q) (by positivity) fun j hj => by
        have := hdec j
        rwa [show Nat.dist j n = k + 2 by simp [Nat.dist]; omega] at this
    have hED : ‖E - (a q - d q i)‖ ≤ 9 * q ^ 2 := by
      rw [hdiag q i (by omega) (by omega), show E - (a q - (((2 * i + δ : ℕ) : ℂ)) ^ 2) =
        -(a q - (m : ℂ) ^ 2) by simp only [hEdef]; ring, norm_neg]
      exact ha2q
    have hD : 1 ≤ ‖a q - d q i‖ := hgap i (by omega)
    have := step_bound_sq (k := k) hrow hD hq hL hED hE
    rwa [show descendingCoefficient m k / E = descendingCoefficient m (k + 1) from
      descendingCoefficient_succ hm (by omega)] at this

/-- From `(a - b)(1 + ρ) = K q^m (1 + η)` with `ρ, η = O(q²)` to `a - b - K q^m = O(q^{m+2})`. -/
private lemma isBigO_sub_of_mul_one_add {f : ℝ → ℝ} {K C : ℝ} {m : ℕ} (hm : m ≠ 0)
    (h0 : f 0 = 0)
    (h : ∀ᶠ q in 𝓝 0, q ≠ 0 → ∃ ρ η : ℂ, ‖ρ‖ ≤ C * q ^ 2 ∧ ‖η‖ ≤ C * q ^ 2 ∧
      ((f q : ℝ) : ℂ) * (1 + ρ) = ((K * q ^ m : ℝ) : ℂ) * (1 + η)) :
    (fun q => f q - K * q ^ m) =O[𝓝 0] (fun q : ℝ => q ^ (m + 2)) := by
  have hsmall : ∀ᶠ q : ℝ in 𝓝 0, C * q ^ 2 ≤ 1 / 2 := by
    have : Tendsto (fun q : ℝ => C * q ^ 2) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun q : ℝ => C * q ^ 2) := by fun_prop
      simpa using hc.tendsto (0 : ℝ)
    exact this.eventually (ge_mem_nhds (by norm_num))
  refine IsBigO.of_bound (4 * |K| * |C|) ?_
  filter_upwards [h, hsmall] with q hq hs
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [h0, zero_pow hm]
  obtain ⟨ρ, η, hρ, hη, he⟩ := hq hq0
  have hρ2 : ‖ρ‖ ≤ 1 / 2 := hρ.trans hs
  have h1ρ : 1 / 2 ≤ ‖1 + ρ‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-ρ)
    rw [sub_neg_eq_add, norm_one, norm_neg] at this
    linarith
  have key : ((f q - K * q ^ m : ℝ) : ℂ) * (1 + ρ) = ((K * q ^ m : ℝ) : ℂ) * (η - ρ) := by
    push_cast at he ⊢; linear_combination he
  have hn := congrArg norm key
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs] at hn
  have hηρ : ‖η - ρ‖ ≤ 2 * (|C| * q ^ 2) := by
    have := norm_sub_le η ρ
    have : C * q ^ 2 ≤ |C| * q ^ 2 := by gcongr; exact le_abs_self C
    linarith
  have hK : |K * q ^ m| = |K| * |q| ^ m := by rw [abs_mul, abs_pow]
  have : |f q - K * q ^ m| * (1 / 2) ≤ |K| * |q| ^ m * (2 * (|C| * q ^ 2)) := by
    calc |f q - K * q ^ m| * (1 / 2) ≤ |f q - K * q ^ m| * ‖1 + ρ‖ := by gcongr
      _ = |K * q ^ m| * ‖η - ρ‖ := hn
      _ ≤ |K| * |q| ^ m * (2 * (|C| * q ^ 2)) := by rw [hK]; gcongr
  rw [← sq_abs q] at this
  rw [pow_add, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow, abs_pow]
  linarith



/-- The coefficient `descendingCoefficient` as a real number. -/
private def descendingCoefficientReal (m k : ℕ) : ℝ :=
  ((m - k - 1).factorial : ℝ) / ((k.factorial : ℝ) * ((m - 1).factorial : ℝ)) / 4 ^ k

private lemma descendingCoefficientReal_pos (m k : ℕ) : 0 < descendingCoefficientReal m k := by
  unfold descendingCoefficientReal; positivity

private lemma ofReal_descendingCoefficientReal (m k : ℕ) :
    (descendingCoefficientReal m k : ℂ) = descendingCoefficient m k := by
  simp [descendingCoefficientReal, descendingCoefficient]

/-- Relative form of an estimate `‖X - c q^s Y‖ ≤ C |q|^{s+2} ‖Y‖`. -/
private lemma exists_eq_mul_one_add {X Y : ℂ} {c C q : ℝ} {s : ℕ} (hc : 0 < c) (hq : q ≠ 0)
    (hY : Y ≠ 0) (h : ‖X - (c : ℂ) * (q : ℂ) ^ s * Y‖ ≤ C * (|q| ^ (s + 2) * ‖Y‖)) :
    ∃ u : ℂ, ‖u‖ ≤ |C| / c * q ^ 2 ∧ X = (c : ℂ) * (q : ℂ) ^ s * (1 + u) * Y := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have h0 : (c : ℂ) * (q : ℂ) ^ s * Y ≠ 0 := mul_ne_zero (mul_ne_zero hc' (pow_ne_zero _ hq')) hY
  refine ⟨(X - c * q ^ s * Y) / (c * q ^ s * Y), ?_, by field_simp; ring⟩
  rw [norm_div, div_le_iff₀ (norm_pos_iff.2 h0), norm_mul, norm_mul, norm_pow, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg hc.le, Real.norm_eq_abs]
  calc _ ≤ C * (|q| ^ (s + 2) * ‖Y‖) := h
    _ ≤ |C| * (|q| ^ (s + 2) * ‖Y‖) := by gcongr; exact le_abs_self C
    _ = _ := by rw [pow_add, ← sq_abs q]; field_simp

/-- `‖u + v + uv‖ ≤ (A + B + AB) q²` when `‖u‖ ≤ A q²`, `‖v‖ ≤ B q²`, `|q| ≤ 1`. -/
private lemma norm_add_add_mul_le {u v : ℂ} {A B q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : |q| ≤ 1)
    (hu : ‖u‖ ≤ A * q ^ 2) (hv : ‖v‖ ≤ B * q ^ 2) :
    ‖u + v + u * v‖ ≤ (A + B + A * B) * q ^ 2 := by
  have hq2 : q ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg q]
  have h1 : ‖u * v‖ ≤ A * B * q ^ 2 := by
    rw [norm_mul]
    calc ‖u‖ * ‖v‖ ≤ (A * q ^ 2) * (B * q ^ 2) :=
          mul_le_mul hu hv (norm_nonneg _) (by positivity)
      _ = A * B * q ^ 2 * q ^ 2 := by ring
      _ ≤ A * B * q ^ 2 * 1 := by gcongr
      _ = _ := by ring
  calc _ ≤ ‖u‖ + ‖v‖ + ‖u * v‖ := norm_add₃_le
    _ ≤ _ := by linarith

/-- The Green identity for even `m = 2n+2` in relative form. -/
private lemma eventually_green_even (n : ℕ) : ∃ C : ℝ, ∀ᶠ q in 𝓝 0, q ≠ 0 →
    ∃ ρ η : ℂ, ‖ρ‖ ≤ C * q ^ 2 ∧ ‖η‖ ≤ C * q ^ 2 ∧
      ((mathieuA (2 * n + 2) q - mathieuB (2 * n + 2) q : ℝ) : ℂ) * (1 + ρ) =
        ((2 * descendingCoefficientReal (2 * n + 2) (n + 1) *
          descendingCoefficientReal (2 * n + 2) n * q ^ (2 * n + 2) : ℝ) : ℂ) * (1 + η) := by
  have hAs : ∀ q : ℝ, SolvesRecurrence (fun i => 4 * (i : ℂ) ^ 2) 2 q (mathieuA (2 * n + 2) q)
      (fun i => mathieuFourierA (2 * n + 2) (2 * i) q) := fun q => by
    have := solvesRecurrence_mathieuFourierA_even (n + 1) q
    rwa [show 2 * (n + 1) = 2 * n + 2 by ring] at this
  have hAl : ∀ q : ℝ, Tendsto (fun i => mathieuFourierA (2 * n + 2) (2 * i) q) atTop (𝓝 0) :=
    fun q => by
      have := tendsto_mathieuFourierA_even (n + 1) q
      rwa [show 2 * (n + 1) = 2 * n + 2 by ring] at this
  have hAne : ∀ q : ℝ, ∃ i, mathieuFourierA (2 * n + 2) (2 * i) q ≠ 0 := fun q => by
    have := exists_mathieuFourierA_even_ne_zero (n + 1) q
    rwa [show 2 * (n + 1) = 2 * n + 2 by ring] at this
  have hdA : ∀ (q : ℝ) (i : ℕ), 4 * (i : ℂ) ^ 2 = (((2 * i + 0 : ℕ) : ℂ)) ^ 2 := fun q i => by
    push_cast; ring
  have hdB : ∀ (q : ℝ) (i : ℕ), (2 * (i : ℂ) + 2) ^ 2 = (((2 * i + 2 : ℕ) : ℂ)) ^ 2 :=
    fun q i => by push_cast; ring
  have haA := eventually_norm_mathieuA_sub_sq_le (2 * n + 2)
  have haB := eventually_norm_mathieuB_sub_sq_le (m := 2 * n + 2) (by omega)
  have hA2 := eventually_norm_sub_sq_le_nine_mul_sq (δ := 0) (n := n + 1) (m := 2 * n + 2)
    (by ring) (by norm_num) hAs hAl norm_four_mul_sq_sub_sq_le haA
    (fun q => by push_cast; ring) hAne
  have hB2 := eventually_norm_sub_sq_le_nine_mul_sq (δ := 2) (n := n) (m := 2 * n + 2) rfl
    (by norm_num) (solvesRecurrence_mathieuFourierB_even n) (tendsto_mathieuFourierB_even n)
    norm_two_mul_add_two_sq_sub_sq_le haB (fun q => by push_cast; ring)
    (exists_mathieuFourierB_even_ne_zero n)
  have hzA := down_isBigO_sq (δ := 0) (n := n + 1) (m := 2 * n + 2) (s := n + 1) (by ring)
    (by norm_num) hAs hAl norm_four_mul_sq_sub_sq_le haA hA2 (fun q i _ _ => hdA q i) le_rfl
    (n + 1) le_rfl
  have hyB := down_isBigO_sq (δ := 2) (n := n) (m := 2 * n + 2) (s := n) rfl (by norm_num)
    (solvesRecurrence_mathieuFourierB_even n) (tendsto_mathieuFourierB_even n)
    norm_two_mul_add_two_sq_sub_sq_le haB hB2 (fun q i _ _ => hdB q i) le_rfl n le_rfl
  obtain ⟨CA, hCA⟩ := hzA.bound
  obtain ⟨CB, hCB⟩ := hyB.bound
  set cA := descendingCoefficientReal (2 * n + 2) (n + 1) with hcA
  set cB := descendingCoefficientReal (2 * n + 2) n with hcB
  have hcA0 : 0 < cA := descendingCoefficientReal_pos _ _
  have hcB0 : 0 < cB := descendingCoefficientReal_pos _ _
  set T := ∑' j, (1 / 2 : ℝ) ^ Nat.dist j n
  have hT : 0 ≤ T := tsum_nonneg fun _ => by positivity
  have gA := eventually_one_le_norm_sub_diagonal (δ := 0) (n := n + 1) (m := 2 * n + 2)
    (a := fun q => (mathieuA (2 * n + 2) q : ℂ)) (by ring) norm_four_mul_sq_sub_sq_le haA
  have gB := eventually_one_le_norm_sub_diagonal (δ := 2) (n := n) (m := 2 * n + 2)
    (a := fun q => (mathieuB (2 * n + 2) q : ℂ)) rfl norm_two_mul_add_two_sq_sub_sq_le haB
  refine ⟨18 * T + (|CA| / cA + |CB| / cB + |CA| / cA * (|CB| / cB)), ?_⟩
  filter_upwards [hCA, hCB, gA, gB, eventually_three_mul_abs_small T hT] with q hqA hqB hgA hgB hr
  intro hq0
  obtain ⟨h8, -, gapA⟩ := hgA
  obtain ⟨-, -, gapB⟩ := hgB
  obtain ⟨hr1, hr2⟩ := hr
  set z : ℕ → ℂ := fun i => mathieuFourierA (2 * n + 2) (2 * i) q with hzdef
  set x : ℕ → ℂ := fun j => z (j + 1) with hxdef
  set y : ℕ → ℂ := fun j => mathieuFourierB (2 * n + 2) (2 * j + 2) q with hydef
  have hq4 : ‖(q : ℂ)‖ ≤ 1 / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have hqn : ‖(q : ℂ)‖ = |q| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hdz := norm_le_pow_dist_mul_of_solvesRecurrence (by norm_num) (hAs q) (hAl q) hq4 gapA
  have hdy := norm_le_pow_dist_mul_of_solvesRecurrence (by norm_num)
    (solvesRecurrence_mathieuFourierB_even n q) (tendsto_mathieuFourierB_even n q) hq4 gapB
  rw [hqn] at hdz hdy
  have hdx : ∀ j, ‖x j‖ ≤ (3 * |q|) ^ Nat.dist j n * ‖x n‖ := fun j => by
    have := hdz (j + 1)
    rwa [show Nat.dist (j + 1) (n + 1) = Nat.dist j n by unfold Nat.dist; omega] at this
  have hxn : x n ≠ 0 := ne_zero_of_decay (x := z) hdz (hAne q)
  have hyn : y n ≠ 0 := ne_zero_of_decay hdy (exists_mathieuFourierB_even_ne_zero n q)
  obtain ⟨hs, hS⟩ := summable_and_norm_tsum_sub_le (x := x) (y := y) (by positivity) hr1 hdx hdy
  have hxl : Tendsto x atTop (𝓝 0) := (hAl q).comp (tendsto_add_atTop_nat 1)
  have hgreen := mul_tsum_eq (a := (mathieuA (2 * n + 2) q : ℂ))
    (b := (mathieuB (2 * n + 2) q : ℂ)) (q := q) (g := 2 * q * z 0)
    (D := fun j => (2 * (j : ℂ) + 2) ^ 2) (x := x) (y := y)
    (fun j => by
      have := hAs q (j + 1)
      simp only [recurrenceOperator] at this
      rcases j with _ | j
      · simp only [recurrenceLower, ↓reduceIte] at this ⊢
        push_cast at this ⊢
        linear_combination -this
      · simp only [Nat.succ_ne_zero, ↓reduceIte, add_zero, recurrenceLower_one_succ] at this ⊢
        simp only [recurrenceLower] at this
        push_cast at this ⊢
        linear_combination -this)
    (fun j => by
      have := solvesRecurrence_mathieuFourierB_even n q j
      simp only [recurrenceOperator] at this
      linear_combination -this)
    hxl (tendsto_mathieuFourierB_even n q) hs
  -- relative forms of the lowest coefficients
  have hpn : ∀ (j : ℕ) (w : ℂ), ‖q ^ j * ‖w‖‖ = |q| ^ j * ‖w‖ := fun j w => by
    rw [norm_mul, norm_pow, Real.norm_eq_abs, norm_norm]
  rw [hpn] at hqA hqB
  simp only [Nat.sub_self, ← ofReal_descendingCoefficientReal] at hqA hqB
  obtain ⟨u, hu, hzu⟩ := exists_eq_mul_one_add (X := z 0) (Y := x n) hcA0 hq0 hxn hqA
  obtain ⟨v, hv, hyv⟩ := exists_eq_mul_one_add (X := y 0) (Y := y n) hcB0 hq0 hyn hqB
  set P := x n * y n with hPdef
  have hP : P ≠ 0 := mul_ne_zero hxn hyn
  have hPn := norm_pos_iff.2 hP
  refine ⟨(∑' j, x j * y j - P) / P, u + v + u * v, ?_, ?_, ?_⟩
  · rw [norm_div, div_le_iff₀ hPn]
    calc _ ≤ 2 * (3 * |q|) ^ 2 * T * ‖P‖ := hS
      _ = 18 * T * q ^ 2 * ‖P‖ := by rw [mul_pow, sq_abs]; ring
      _ ≤ _ := by
        have : (0 : ℝ) ≤ |CA| / cA + |CB| / cB + |CA| / cA * (|CB| / cB) := by positivity
        gcongr; linarith
  · refine (norm_add_add_mul_le (by positivity) (by positivity) (by linarith) hu hv).trans ?_
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (sq_nonneg q)
  · apply mul_right_cancel₀ hP
    rw [hzu, hyv] at hgreen
    have e1 : (1 + (∑' j, x j * y j - P) / P) * P = ∑' j, x j * y j := by field_simp; ring
    push_cast
    linear_combination ((mathieuA (2 * n + 2) q : ℂ) - mathieuB (2 * n + 2) q) * e1 + hgreen


/-- `C q² ≤ 1/2` near `0`. -/
private lemma eventually_mul_sq_le_half (C : ℝ) : ∀ᶠ q : ℝ in 𝓝 0, C * q ^ 2 ≤ 1 / 2 := by
  have : Tendsto (fun q : ℝ => C * q ^ 2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun q : ℝ => C * q ^ 2) := by fun_prop
    simpa using hc.tendsto (0 : ℝ)
  exact this.eventually (ge_mem_nhds (by norm_num))

/-- The perturbed row-`0` product `(E + α - q)(E + β + q) = E² (1 + w)` with `w = O(q²)`. -/
private lemma exists_mul_eq_sq_mul_one_add {α β : ℂ} {E q : ℝ} (hE : E ≠ 0) (hq : |q| < 1 / 8)
    (hα : ‖α‖ ≤ 9 * q ^ 2) (hβ : ‖β‖ ≤ 9 * q ^ 2) :
    ∃ w : ℂ, ‖w‖ ≤ (18 * |E| + 9) / E ^ 2 * q ^ 2 ∧
      ((E : ℂ) + α - q) * ((E : ℂ) + β + q) = (E : ℂ) ^ 2 * (1 + w) := by
  have hE' : (E : ℂ) ≠ 0 := by exact_mod_cast hE
  have hE2 : 0 < E ^ 2 := by positivity
  refine ⟨(E * (α + β) + (α - q) * (β + q)) / (E : ℂ) ^ 2, ?_, by field_simp; ring⟩
  have hqn : ‖(q : ℂ)‖ = |q| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hq2 : 9 * q ^ 2 ≤ 2 * |q| := by
    rw [← sq_abs]; nlinarith [abs_nonneg q]
  have h1 : ‖α - q‖ ≤ 3 * |q| := (norm_sub_le _ _).trans (by rw [hqn]; linarith)
  have h2 : ‖β + q‖ ≤ 3 * |q| := (norm_add_le _ _).trans (by rw [hqn]; linarith)
  have hab : ‖α + β‖ ≤ 18 * q ^ 2 := (norm_add_le _ _).trans (by linarith)
  have hp : ‖α - q‖ * ‖β + q‖ ≤ 9 * q ^ 2 :=
    calc ‖α - q‖ * ‖β + q‖ ≤ (3 * |q|) * (3 * |q|) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = 9 * q ^ 2 := by rw [← sq_abs q]; ring
  have h : ‖(E : ℂ) * (α + β) + (α - q) * (β + q)‖ ≤ (18 * |E| + 9) * q ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_left hab (abs_nonneg E)]
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right h hE2.le

/-- `‖(u + v + uv - w)/(1 + w)‖ ≤ 2(‖u + v + uv‖ + ‖w‖)` when `‖w‖ ≤ 1/2`. -/
private lemma norm_div_one_add_le {z w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖(z - w) / (1 + w)‖ ≤ 2 * (‖z‖ + ‖w‖) := by
  have h1 : 1 / 2 ≤ ‖1 + w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-w)
    rw [sub_neg_eq_add, norm_one, norm_neg] at this
    linarith
  rw [norm_div, div_le_iff₀ (by linarith)]
  have := norm_sub_le z w
  nlinarith [norm_nonneg (z - w)]

/-- The Green identity for odd `m = 2k+3` in relative form. -/
private lemma eventually_green_odd (k : ℕ) : ∃ C : ℝ, ∀ᶠ q in 𝓝 0, q ≠ 0 →
    ∃ ρ η : ℂ, ‖ρ‖ ≤ C * q ^ 2 ∧ ‖η‖ ≤ C * q ^ 2 ∧
      ((mathieuA (2 * (k + 1) + 1) q - mathieuB (2 * (k + 1) + 1) q : ℝ) : ℂ) * (1 + ρ) =
        ((2 * (descendingCoefficientReal (2 * (k + 1) + 1) k /
          (((2 * (k + 1) + 1 : ℕ) : ℝ) ^ 2 - 1)) ^ 2 * q ^ (2 * (k + 1) + 1) : ℝ) : ℂ) *
          (1 + η) := by
  set n := k + 1 with hn
  set m := 2 * n + 1 with hm
  have hdA : ∀ (q : ℝ) (i : ℕ), n - k ≤ i → i < n →
      ((2 * (i : ℂ) + 1) ^ 2 + if i = 0 then (q : ℂ) else 0) = (((2 * i + 1 : ℕ) : ℂ)) ^ 2 :=
    fun q i hi _ => by
      rw [ite_eq_right (by omega)]; push_cast; ring
  have hdB : ∀ (q : ℝ) (i : ℕ), n - k ≤ i → i < n →
      ((2 * (i : ℂ) + 1) ^ 2 - if i = 0 then (q : ℂ) else 0) = (((2 * i + 1 : ℕ) : ℂ)) ^ 2 :=
    fun q i hi _ => by
      rw [ite_eq_right (by omega)]; push_cast; ring
  have haA := eventually_norm_mathieuA_sub_sq_le m
  have haB := eventually_norm_mathieuB_sub_sq_le (m := m) (by omega)
  have hA2 := eventually_norm_sub_sq_le_nine_mul_sq (δ := 1) (n := n) (m := m) rfl
    (by norm_num) (solvesRecurrence_mathieuFourierA_odd n) (tendsto_mathieuFourierA_odd n)
    norm_odd_sq_add_ite_sub_sq_le haA
    (fun q => by rw [ite_eq_right (by omega), hm]; push_cast; ring)
    (exists_mathieuFourierA_odd_ne_zero n)
  have hB2 := eventually_norm_sub_sq_le_nine_mul_sq (δ := 1) (n := n) (m := m) rfl
    (by norm_num) (solvesRecurrence_mathieuFourierB_odd n) (tendsto_mathieuFourierB_odd n)
    norm_odd_sq_sub_ite_sub_sq_le haB
    (fun q => by rw [ite_eq_right (by omega), hm]; push_cast; ring)
    (exists_mathieuFourierB_odd_ne_zero n)
  have hxA := down_isBigO_sq (δ := 1) (n := n) (m := m) (s := k) rfl (by norm_num)
    (solvesRecurrence_mathieuFourierA_odd n) (tendsto_mathieuFourierA_odd n)
    norm_odd_sq_add_ite_sub_sq_le haA hA2 hdA (by omega) k le_rfl
  have hyB := down_isBigO_sq (δ := 1) (n := n) (m := m) (s := k) rfl (by norm_num)
    (solvesRecurrence_mathieuFourierB_odd n) (tendsto_mathieuFourierB_odd n)
    norm_odd_sq_sub_ite_sub_sq_le haB hB2 hdB (by omega) k le_rfl
  obtain ⟨CA, hCA⟩ := hxA.bound
  obtain ⟨CB, hCB⟩ := hyB.bound
  set c := descendingCoefficientReal m k with hc
  have hc0 : 0 < c := descendingCoefficientReal_pos _ _
  set E : ℝ := ((m : ℕ) : ℝ) ^ 2 - 1 with hE
  have hE0 : E ≠ 0 := by
    have : (3 : ℝ) ≤ (m : ℝ) := by norm_cast; omega
    simp only [hE]; nlinarith
  set T := ∑' j, (1 / 2 : ℝ) ^ Nat.dist j n
  have hT : 0 ≤ T := tsum_nonneg fun _ => by positivity
  have gA := eventually_one_le_norm_sub_diagonal (δ := 1) (n := n) (m := m)
    (a := fun q => (mathieuA m q : ℂ)) rfl norm_odd_sq_add_ite_sub_sq_le haA
  have gB := eventually_one_le_norm_sub_diagonal (δ := 1) (n := n) (m := m)
    (a := fun q => (mathieuB m q : ℂ)) rfl norm_odd_sq_sub_ite_sub_sq_le haB
  set W := (18 * |E| + 9) / E ^ 2
  set U := |CA| / c + |CB| / c + |CA| / c * (|CB| / c)
  refine ⟨18 * T + 2 * (U + W), ?_⟩
  filter_upwards [hCA, hCB, gA, gB, eventually_three_mul_abs_small T hT, hA2, hB2,
    eventually_mul_sq_le_half W] with q hqA hqB hgA hgB hr hA2q hB2q hWq
  intro hq0
  obtain ⟨h8, -, gapA⟩ := hgA
  obtain ⟨-, -, gapB⟩ := hgB
  obtain ⟨hr1, hr2⟩ := hr
  set x : ℕ → ℂ := fun j => mathieuFourierA m (2 * j + 1) q with hxdef
  set y : ℕ → ℂ := fun j => mathieuFourierB m (2 * j + 1) q with hydef
  have hq4 : ‖(q : ℂ)‖ ≤ 1 / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have hqn : ‖(q : ℂ)‖ = |q| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hdx := norm_le_pow_dist_mul_of_solvesRecurrence (by norm_num)
    (solvesRecurrence_mathieuFourierA_odd n q) (tendsto_mathieuFourierA_odd n q) hq4 gapA
  have hdy := norm_le_pow_dist_mul_of_solvesRecurrence (by norm_num)
    (solvesRecurrence_mathieuFourierB_odd n q) (tendsto_mathieuFourierB_odd n q) hq4 gapB
  rw [hqn] at hdx hdy
  have hxn : x n ≠ 0 := ne_zero_of_decay hdx (exists_mathieuFourierA_odd_ne_zero n q)
  have hyn : y n ≠ 0 := ne_zero_of_decay hdy (exists_mathieuFourierB_odd_ne_zero n q)
  obtain ⟨hs, hS⟩ := summable_and_norm_tsum_sub_le (x := x) (y := y) (by positivity) hr1 hdx hdy
  have hgreen := mul_tsum_eq (a := (mathieuA m q : ℂ))
    (b := (mathieuB m q : ℂ)) (q := q) (g := 2 * q * x 0)
    (D := fun j => (2 * (j : ℂ) + 1) ^ 2 - if j = 0 then (q : ℂ) else 0) (x := x) (y := y)
    (fun j => by
      have := solvesRecurrence_mathieuFourierA_odd n q j
      simp only [recurrenceOperator] at this
      rcases j with _ | j
      · simp only [↓reduceIte] at this ⊢; linear_combination -this
      · simp only [Nat.succ_ne_zero, ↓reduceIte, add_zero, sub_zero] at this ⊢
        linear_combination -this)
    (fun j => by
      have := solvesRecurrence_mathieuFourierB_odd n q j
      simp only [recurrenceOperator] at this
      linear_combination -this)
    (tendsto_mathieuFourierA_odd n q) (tendsto_mathieuFourierB_odd n q) hs
  have hx0 : ((mathieuA m q : ℂ) - 1 - q) * x 0 = q * x 1 := by
    have := solvesRecurrence_mathieuFourierA_odd n q 0
    simp only [recurrenceOperator, recurrenceLower, ↓reduceIte] at this
    push_cast at this ⊢
    linear_combination -this
  have hy0 : ((mathieuB m q : ℂ) - 1 + q) * y 0 = q * y 1 := by
    have := solvesRecurrence_mathieuFourierB_odd n q 0
    simp only [recurrenceOperator, recurrenceLower, ↓reduceIte] at this
    push_cast at this ⊢
    linear_combination -this
  have hpn : ∀ (j : ℕ) (w : ℂ), ‖q ^ j * ‖w‖‖ = |q| ^ j * ‖w‖ := fun j w => by
    rw [norm_mul, norm_pow, Real.norm_eq_abs, norm_norm]
  rw [hpn] at hqA hqB
  simp only [show n - k = 1 by omega, ← ofReal_descendingCoefficientReal] at hqA hqB
  obtain ⟨u, hu, hxu⟩ := exists_eq_mul_one_add (X := x 1) (Y := x n) hc0 hq0 hxn hqA
  obtain ⟨v, hv, hyv⟩ := exists_eq_mul_one_add (X := y 1) (Y := y n) hc0 hq0 hyn hqB
  obtain ⟨w, hw, hQ⟩ := exists_mul_eq_sq_mul_one_add (α := (mathieuA m q : ℂ) - (m : ℂ) ^ 2)
    (β := (mathieuB m q : ℂ) - (m : ℂ) ^ 2) hE0 h8 hA2q hB2q
  have hw2 : ‖w‖ ≤ 1 / 2 := hw.trans hWq
  have h1w : (1 : ℂ) + w ≠ 0 := by
    intro h
    have : ‖w‖ = 1 := by rw [show w = -1 by linear_combination h]; simp
    linarith
  have huv := norm_add_add_mul_le (by positivity) (by positivity) (by linarith) hu hv
  set P := x n * y n with hPdef
  have hP : P ≠ 0 := mul_ne_zero hxn hyn
  have hPn := norm_pos_iff.2 hP
  have hE' : (E : ℂ) ≠ 0 := by exact_mod_cast hE0
  refine ⟨(∑' j, x j * y j - P) / P, (u + v + u * v - w) / (1 + w), ?_, ?_, ?_⟩
  · rw [norm_div, div_le_iff₀ hPn]
    calc _ ≤ 2 * (3 * |q|) ^ 2 * T * ‖P‖ := hS
      _ = 18 * T * q ^ 2 * ‖P‖ := by rw [mul_pow, sq_abs]; ring
      _ ≤ _ := by
        have : (0 : ℝ) ≤ 2 * (U + W) := by positivity
        gcongr; linarith
  · refine (norm_div_one_add_le hw2).trans ?_
    have : (0 : ℝ) ≤ 18 * T * q ^ 2 := by positivity
    nlinarith
  · have hEm : (E : ℂ) = (m : ℂ) ^ 2 - 1 := by simp only [hE]; push_cast; ring
    have hQ' : ((mathieuA m q : ℂ) - 1 - q) * ((mathieuB m q : ℂ) - 1 + q) =
        (E : ℂ) ^ 2 * (1 + w) := by
      rw [← hQ, hEm]; ring
    have e1 : (1 + (∑' j, x j * y j - P) / P) * P = ∑' j, x j * y j := by field_simp; ring
    have hη : (1 + u) * (1 + v) = (1 + w) * (1 + (u + v + u * v - w) / (1 + w)) := by
      field_simp; ring
    apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hP h1w) (pow_ne_zero 2 hE'))
    set S := ∑' j, x j * y j
    calc ((mathieuA m q - mathieuB m q : ℝ) : ℂ) * (1 + (S - P) / P) * (P * (1 + w) * E ^ 2)
        = 2 * q * (x 0 * y 0 * (((mathieuA m q : ℂ) - 1 - q) * ((mathieuB m q : ℂ) - 1 + q)))
          := by
          push_cast
          linear_combination ((mathieuA m q : ℂ) - mathieuB m q) * (1 + w) * (E : ℂ) ^ 2 * e1 +
            (1 + w) * (E : ℂ) ^ 2 * hgreen - 2 * q * x 0 * y 0 * hQ'
      _ = 2 * q ^ 3 * (x 1 * y 1) := by
          linear_combination 2 * q * (((mathieuB m q : ℂ) - 1 + q) * y 0 * hx0 + q * x 1 * hy0)
      _ = 2 * q ^ 3 * (c * q ^ k) ^ 2 * ((1 + u) * (1 + v)) * P := by rw [hxu, hyv]; ring
      _ = _ := by
          rw [hη]; push_cast; field_simp; ring

/-- The Green identity for `m = 1` in relative form. -/
private lemma eventually_green_one : ∃ C : ℝ, ∀ᶠ q in 𝓝 0, q ≠ 0 →
    ∃ ρ η : ℂ, ‖ρ‖ ≤ C * q ^ 2 ∧ ‖η‖ ≤ C * q ^ 2 ∧
      ((mathieuA 1 q - mathieuB 1 q : ℝ) : ℂ) * (1 + ρ) = ((2 * q ^ 1 : ℝ) : ℂ) * (1 + η) := by
  set T := ∑' j, (1 / 2 : ℝ) ^ Nat.dist j 0
  have hT : 0 ≤ T := tsum_nonneg fun _ => by positivity
  have gA := eventually_one_le_norm_sub_diagonal (δ := 1) (n := 0) (m := 2 * 0 + 1)
    (a := fun q => (mathieuA (2 * 0 + 1) q : ℂ)) rfl norm_odd_sq_add_ite_sub_sq_le
    (eventually_norm_mathieuA_sub_sq_le _)
  have gB := eventually_one_le_norm_sub_diagonal (δ := 1) (n := 0) (m := 2 * 0 + 1)
    (a := fun q => (mathieuB (2 * 0 + 1) q : ℂ)) rfl norm_odd_sq_sub_ite_sub_sq_le
    (eventually_norm_mathieuB_sub_sq_le (by omega))
  refine ⟨18 * T, ?_⟩
  filter_upwards [gA, gB, eventually_three_mul_abs_small T hT] with q hgA hgB hr
  intro _
  obtain ⟨h8, -, gapA⟩ := hgA
  obtain ⟨-, -, gapB⟩ := hgB
  obtain ⟨hr1, -⟩ := hr
  set x : ℕ → ℂ := fun j => mathieuFourierA (2 * 0 + 1) (2 * j + 1) q with hxdef
  set y : ℕ → ℂ := fun j => mathieuFourierB (2 * 0 + 1) (2 * j + 1) q with hydef
  have hq4 : ‖(q : ℂ)‖ ≤ 1 / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have hqn : ‖(q : ℂ)‖ = |q| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hdx := norm_le_pow_dist_mul_of_solvesRecurrence (by norm_num)
    (solvesRecurrence_mathieuFourierA_odd 0 q) (tendsto_mathieuFourierA_odd 0 q) hq4 gapA
  have hdy := norm_le_pow_dist_mul_of_solvesRecurrence (by norm_num)
    (solvesRecurrence_mathieuFourierB_odd 0 q) (tendsto_mathieuFourierB_odd 0 q) hq4 gapB
  rw [hqn] at hdx hdy
  have hxn : x 0 ≠ 0 := ne_zero_of_decay hdx (exists_mathieuFourierA_odd_ne_zero 0 q)
  have hyn : y 0 ≠ 0 := ne_zero_of_decay hdy (exists_mathieuFourierB_odd_ne_zero 0 q)
  obtain ⟨hs, hS⟩ := summable_and_norm_tsum_sub_le (x := x) (y := y) (by positivity) hr1 hdx hdy
  have hgreen := mul_tsum_eq (a := (mathieuA (2 * 0 + 1) q : ℂ))
    (b := (mathieuB (2 * 0 + 1) q : ℂ)) (q := q) (g := 2 * q * x 0)
    (D := fun j => (2 * (j : ℂ) + 1) ^ 2 - if j = 0 then (q : ℂ) else 0) (x := x) (y := y)
    (fun j => by
      have := solvesRecurrence_mathieuFourierA_odd 0 q j
      simp only [recurrenceOperator] at this
      rcases j with _ | j
      · simp only [↓reduceIte] at this ⊢; linear_combination -this
      · simp only [Nat.succ_ne_zero, ↓reduceIte, add_zero, sub_zero] at this ⊢
        linear_combination -this)
    (fun j => by
      have := solvesRecurrence_mathieuFourierB_odd 0 q j
      simp only [recurrenceOperator] at this
      linear_combination -this)
    (tendsto_mathieuFourierA_odd 0 q) (tendsto_mathieuFourierB_odd 0 q) hs
  set P := x 0 * y 0 with hPdef
  have hP : P ≠ 0 := mul_ne_zero hxn hyn
  have hPn := norm_pos_iff.2 hP
  refine ⟨(∑' j, x j * y j - P) / P, 0, ?_, by simp; positivity, ?_⟩
  · rw [norm_div, div_le_iff₀ hPn]
    calc _ ≤ 2 * (3 * |q|) ^ 2 * T * ‖P‖ := hS
      _ = _ := by rw [mul_pow, sq_abs]; ring
  · apply mul_right_cancel₀ hP
    have e1 : (1 + (∑' j, x j * y j - P) / P) * P = ∑' j, x j * y j := by field_simp; ring
    push_cast
    linear_combination ((mathieuA (2 * 0 + 1) q : ℂ) - mathieuB (2 * 0 + 1) q) * e1 + hgreen


/-- The constant of 28.6.15 for even `m = 2n+2`. -/
private lemma descendingCoefficientReal_mul_even (n : ℕ) :
    2 * descendingCoefficientReal (2 * n + 2) (n + 1) * descendingCoefficientReal (2 * n + 2) n =
      2 / (2 ^ (2 * n + 2 - 1) * ((2 * n + 2 - 1).factorial : ℝ)) ^ 2 := by
  unfold descendingCoefficientReal
  rw [show 2 * n + 2 - (n + 1) - 1 = n by omega, show 2 * n + 2 - n - 1 = n + 1 by omega,
    show 2 * n + 2 - 1 = 2 * n + 1 by omega]
  have h1 : ((n + 1).factorial : ℝ) = (n + 1) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [h1]
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  have : ((2 * n + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
  simp only [← pow_mul, ← pow_add]
  ring_nf

/-- The constant of 28.6.15 for odd `m = 2k+3`. -/
private lemma descendingCoefficientReal_odd (k : ℕ) :
    2 * (descendingCoefficientReal (2 * (k + 1) + 1) k /
      (((2 * (k + 1) + 1 : ℕ) : ℝ) ^ 2 - 1)) ^ 2 =
      2 / (2 ^ (2 * (k + 1) + 1 - 1) * ((2 * (k + 1) + 1 - 1).factorial : ℝ)) ^ 2 := by
  unfold descendingCoefficientReal
  rw [show 2 * (k + 1) + 1 - k - 1 = k + 2 by omega,
    show 2 * (k + 1) + 1 - 1 = 2 * k + 2 by omega]
  have h1 : ((k + 2).factorial : ℝ) = (k + 2) * ((k + 1) * (k.factorial : ℝ)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  rw [h1]
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  have : ((2 * k + 2).factorial : ℝ) ≠ 0 := by positivity
  have : ((((2 * (k + 1) + 1 : ℕ) : ℝ)) ^ 2 - 1) = 4 * (k + 1) * (k + 2) := by push_cast; ring
  rw [this]
  field_simp
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
  simp only [← pow_mul, ← pow_add]
  ring_nf

end SmallQFourier

open SmallQFourier in
/-- `a_m(q) - b_m(q) - 2 q^m/(2^{m-1}(m-1)!)² = O(q^{m+2})` as `q → 0`, `m ≥ 1`
(DLMF 28.6.15). -/
theorem isBigO_mathieuA_sub_mathieuB_sub {m : ℕ} (hm : m ≠ 0) :
    (fun q : ℝ => mathieuA m q - mathieuB m q -
      2 / (2 ^ (m - 1) * ((m - 1).factorial : ℝ)) ^ 2 * q ^ m) =O[𝓝 0]
      (fun q : ℝ => q ^ (m + 2)) := by
  have h0 : mathieuA m 0 - mathieuB m 0 = 0 := by
    rw [mathieuA_zero, mathieuB_zero hm, sub_self]
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [show 2 * (n + 1) = 2 * n + 2 by ring] at h0 ⊢
    obtain ⟨C, hC⟩ := eventually_green_even n
    rw [← descendingCoefficientReal_mul_even]
    exact isBigO_sub_of_mul_one_add (f := fun q => mathieuA _ q - mathieuB _ q) (C := C)
      (by omega) h0 hC
  · rcases n with _ | k
    · obtain ⟨C, hC⟩ := eventually_green_one
      simp only [mul_zero, zero_add, Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one,
        mul_one, one_pow, div_one] at h0 ⊢
      exact isBigO_sub_of_mul_one_add (f := fun q => mathieuA 1 q - mathieuB 1 q) (C := C)
        one_ne_zero h0 hC
    · obtain ⟨C, hC⟩ := eventually_green_odd k
      rw [← descendingCoefficientReal_odd]
      exact isBigO_sub_of_mul_one_add (f := fun q => mathieuA _ q - mathieuB _ q) (C := C)
        (by omega) h0 hC

/-- DLMF 28.6.15 in the form `a_m - b_m = 2q^m/(2^{m-1}(m-1)!)² (1 + ε(q))`, `ε = O(q²)`. -/
theorem exists_mathieuA_sub_mathieuB_eq {m : ℕ} (hm : m ≠ 0) :
    ∃ ε : ℝ → ℝ, ε =O[𝓝 0] (fun q => q ^ 2) ∧ ∀ q : ℝ,
      mathieuA m q - mathieuB m q =
        2 * q ^ m / (2 ^ (m - 1) * ((m - 1).factorial : ℝ)) ^ 2 * (1 + ε q) := by
  set K : ℝ := 2 / (2 ^ (m - 1) * ((m - 1).factorial : ℝ)) ^ 2 with hK
  have hK0 : 0 < K := by positivity
  set g := fun q : ℝ => mathieuA m q - mathieuB m q - K * q ^ m
  obtain ⟨C, hC⟩ := (isBigO_mathieuA_sub_mathieuB_sub hm).bound
  refine ⟨fun q => if q = 0 then 0 else g q / (K * q ^ m), ?_, fun q => ?_⟩
  · refine IsBigO.of_bound (|C| / K) ?_
    filter_upwards [hC] with q hq
    split_ifs with h0
    · simp only [norm_zero]; positivity
    have hqm : 0 < |q| ^ m := pow_pos (abs_pos.2 h0) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hK0, abs_pow,
      div_le_iff₀ (mul_pos hK0 hqm), abs_pow, sq_abs]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, pow_add] at hq
    calc |g q| ≤ C * (|q| ^ m * |q| ^ 2) := hq
      _ ≤ |C| * (|q| ^ m * |q| ^ 2) := by gcongr; exact le_abs_self C
      _ = _ := by rw [sq_abs]; field_simp
  · dsimp only
    split_ifs with h0
    · subst h0
      rw [mathieuA_zero, mathieuB_zero hm, zero_pow hm]; ring
    · have : K * q ^ m ≠ 0 := mul_ne_zero hK0.ne' (pow_ne_zero _ h0)
      rw [show 2 * q ^ m / (2 ^ (m - 1) * ((m - 1).factorial : ℝ)) ^ 2 = K * q ^ m by
        rw [hK]; ring]
      simp only [g]
      field_simp
      ring

end DLMF.Mathieu
