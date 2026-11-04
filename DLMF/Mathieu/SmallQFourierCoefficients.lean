/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.SmallQSpectrum
public import DLMF.Mathieu.Modified.CrossConnection.AngularKernels
public import DLMFMathlib.Analysis.SpecificLimits.QuarterRecurrence

/-!
# Fourier coefficients of the Mathieu functions for small `q` (DLMF §28.4(vi))

The behaviour of the Fourier coefficients `A^n_m(q)`, `B^n_m(q)` as `q → 0`. For `ce₀` the
recurrence 28.4.5 is diagonally dominant for small `q`: the coefficients satisfy
`‖A^0_{2k+2}‖ ≤ |q| ‖A^0_{2k}‖` (a discrete maximum principle), hence `|a₀(q)| ≤ q²`, and an
induction on `k` along the recurrence gives the leading term of `A^0_{2s}/A^0_0`.

## Main results

* `mathieuFourierA_zero_small_q`: DLMF 28.4.21.
* `mathieuFourierA_up_small_q`, `mathieuFourierB_up_small_q`: DLMF 28.4.22 (with stronger
  primed forms for `s ≥ 0`).
* `mathieuFourierA_down_small_q`, `mathieuFourierB_down_small_q`: DLMF 28.4.23 (with stronger
  primed forms for `s ≥ 0`).
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

namespace SmallQFourier

/-- One step of the small-`q` induction: from `(a - 4k²) X = q (Y + Z)` with `|a| ≤ q²`,
`Y ≈ c q^{k-1} A₀` and `Z = O(q^{k+1})` to `X ≈ -c/(4k²) q^k A₀`. -/
private lemma step {q a : ℝ} {k : ℕ} (hk : 1 ≤ k) {X Y Z A₀ c : ℂ} {C : ℝ}
    (hrec : ((a : ℂ) - 4 * k ^ 2) * X = q * (Y + Z)) (ha : |a| ≤ q ^ 2) (ha1 : |a| ≤ 1)
    (hY : ‖Y - c * (q : ℂ) ^ (k - 1) * A₀‖ ≤ C * |q| ^ (k + 1) * ‖A₀‖)
    (hZ : ‖Z‖ ≤ |q| ^ (k + 1) * ‖A₀‖) :
    ‖X - (-c / (4 * k ^ 2)) * (q : ℂ) ^ k * A₀‖ ≤ (C + ‖c‖ + 1) * |q| ^ (k + 2) * ‖A₀‖ := by
  set D : ℂ := (a : ℂ) - 4 * k ^ 2
  have hk4 : (4 : ℝ) ≤ 4 * (k : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hD : 3 ≤ ‖D‖ := by
    have h1 : ‖(4 * (k : ℂ) ^ 2)‖ = 4 * (k : ℝ) ^ 2 := by
      rw [show (4 * (k : ℂ) ^ 2) = ((4 * (k : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have := norm_sub_norm_le (4 * (k : ℂ) ^ 2) (a : ℂ)
    rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, h1] at this
    simp only [D]; linarith
  have hD0 : D ≠ 0 := by intro h; rw [h, norm_zero] at hD; norm_num at hD
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hX : X = q * (Y + Z) / D := by rw [← hrec]; field_simp
  have hq : (q : ℂ) ^ k = q * (q : ℂ) ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  have key : X - (-c / (4 * k ^ 2)) * (q : ℂ) ^ k * A₀ =
      q * (Y - c * (q : ℂ) ^ (k - 1) * A₀) / D +
        c * (q : ℂ) ^ k * A₀ * (a / (D * (4 * k ^ 2))) + q * Z / D := by
    rw [hX, hq]; field_simp; simp only [D]; ring
  rw [key]
  have hinv : ‖(1 : ℂ) / D‖ ≤ 1 / 3 := by
    rw [norm_div, norm_one]; exact one_div_le_one_div_of_le (by norm_num) hD
  have hfrac : ‖(a : ℂ) / (D * (4 * k ^ 2))‖ ≤ q ^ 2 := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h4 : ‖(4 * (k : ℂ) ^ 2)‖ = 4 * (k : ℝ) ^ 2 := by
      rw [show (4 * (k : ℂ) ^ 2) = ((4 * (k : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have h12 : 12 ≤ ‖D‖ * (4 * (k : ℝ) ^ 2) := by nlinarith
    rw [h4, div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg a, sq_nonneg q]
  have hqn : ‖(q : ℂ)‖ = |q| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have t1 : ‖(q : ℂ) * (Y - c * (q : ℂ) ^ (k - 1) * A₀) / D‖ ≤
      C * |q| ^ (k + 2) * ‖A₀‖ := by
    rw [mul_div_assoc, show (Y - c * (q : ℂ) ^ (k - 1) * A₀) / D =
      (Y - c * (q : ℂ) ^ (k - 1) * A₀) * (1 / D) by ring, norm_mul, norm_mul, hqn]
    have hC : 0 ≤ C * |q| ^ (k + 1) * ‖A₀‖ := (norm_nonneg _).trans hY
    calc |q| * (‖Y - c * (q : ℂ) ^ (k - 1) * A₀‖ * ‖(1 : ℂ) / D‖)
        ≤ |q| * (C * |q| ^ (k + 1) * ‖A₀‖ * 1) := by
          gcongr; exact hinv.trans (by norm_num)
      _ = C * |q| ^ (k + 2) * ‖A₀‖ := by ring
  have t2 : ‖c * (q : ℂ) ^ k * A₀ * ((a : ℂ) / (D * (4 * k ^ 2)))‖ ≤
      ‖c‖ * |q| ^ (k + 2) * ‖A₀‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, hqn]
    calc ‖c‖ * |q| ^ k * ‖A₀‖ * ‖(a : ℂ) / (D * (4 * k ^ 2))‖
        ≤ ‖c‖ * |q| ^ k * ‖A₀‖ * q ^ 2 := by gcongr
      _ = ‖c‖ * |q| ^ (k + 2) * ‖A₀‖ := by rw [pow_add, ← sq_abs q]; ring
  have t3 : ‖(q : ℂ) * Z / D‖ ≤ |q| ^ (k + 2) * ‖A₀‖ := by
    rw [mul_div_assoc, show Z / D = Z * (1 / D) by ring, norm_mul, norm_mul, hqn]
    calc |q| * (‖Z‖ * ‖(1 : ℂ) / D‖) ≤ |q| * (|q| ^ (k + 1) * ‖A₀‖ * 1) := by
          gcongr; exact hinv.trans (by norm_num)
      _ = |q| ^ (k + 2) * ‖A₀‖ := by ring
  calc _ ≤ ‖(q : ℂ) * (Y - c * (q : ℂ) ^ (k - 1) * A₀) / D‖ +
        ‖c * (q : ℂ) ^ k * A₀ * ((a : ℂ) / (D * (4 * k ^ 2)))‖ + ‖(q : ℂ) * Z / D‖ :=
        norm_add₃_le
    _ ≤ _ := by linarith

/-- The recurrence 28.4.5 for `n = 0` in shifted form. -/
private lemma rec_zero (q : ℝ) :
    (mathieuA 0 q : ℂ) * mathieuFourierA 0 0 q = q * mathieuFourierA 0 (2 * 1) q := by
  have h := mathieuFourierA_even_rec_zero 0 q
  simp only [mul_zero] at h
  linear_combination h

private lemma rec_one (q : ℝ) :
    ((mathieuA 0 q : ℂ) - 4 * ((1 : ℕ) : ℂ) ^ 2) * mathieuFourierA 0 (2 * 1) q =
      q * (2 * mathieuFourierA 0 (2 * 0) q + mathieuFourierA 0 (2 * 2) q) := by
  have h := mathieuFourierA_even_rec_one 0 q
  simp only [mul_zero] at h
  push_cast; linear_combination h

private lemma rec_succ_succ (q : ℝ) (j : ℕ) :
    ((mathieuA 0 q : ℂ) - 4 * ((j + 2 : ℕ) : ℂ) ^ 2) * mathieuFourierA 0 (2 * (j + 2)) q =
      q * (mathieuFourierA 0 (2 * (j + 1)) q + mathieuFourierA 0 (2 * (j + 3)) q) := by
  have h := mathieuFourierA_even_rec 0 q (m := j + 2) (by omega)
  simp only [mul_zero] at h
  rw [show 2 * (j + 2) - 2 = 2 * (j + 1) by omega,
    show 2 * (j + 2) + 2 = 2 * (j + 3) by omega] at h
  linear_combination h

/-- `‖a - 4k²‖ ≥ 4k² - 1` when `|a| ≤ 1`. -/
private lemma norm_sub_four_mul_sq_ge {a : ℝ} (ha : |a| ≤ 1) (k : ℕ) :
    4 * (k : ℝ) ^ 2 - 1 ≤ ‖(a : ℂ) - 4 * (k : ℂ) ^ 2‖ := by
  have h1 : ‖(4 * (k : ℂ) ^ 2)‖ = 4 * (k : ℝ) ^ 2 := by
    rw [show (4 * (k : ℂ) ^ 2) = ((4 * (k : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have := norm_sub_norm_le (4 * (k : ℂ) ^ 2) (a : ℂ)
  rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, h1] at this
  linarith

/-- **Small-`q` estimates** for `ce₀`: for small real `q`, `|a₀(q)| ≤ q²`, `|a₀(q)| ≤ 1` and
`‖A^0_{2k}(q)‖ ≤ |q|^k ‖A^0_0(q)‖`. -/
private lemma eventually_estimates : ∀ᶠ q : ℝ in 𝓝 0, |mathieuA 0 q| ≤ q ^ 2 ∧
    |mathieuA 0 q| ≤ 1 ∧
    ∀ k : ℕ, ‖mathieuFourierA 0 (2 * k) q‖ ≤ |q| ^ k * ‖mathieuFourierA 0 0 q‖ := by
  have hsmall : ∀ᶠ q : ℝ in 𝓝 0, |q| < 1 / 4 := by
    have := Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4)
    filter_upwards [this] with q hq
    rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hq
  filter_upwards [eventually_abs_mathieuA_sub_sq_le 0, hsmall] with q ha4 hq
  set a := mathieuA 0 q
  set A : ℕ → ℂ := fun k => mathieuFourierA 0 (2 * k) q with hAdef
  simp only [CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero] at ha4
  have ha1 : |a| ≤ 1 := by linarith [abs_nonneg q]
  have hq0 := abs_nonneg q
  -- the quarter inequality and halving
  have hquarter : ∀ j : ℕ, ‖A (j + 2)‖ ≤ (‖A (j + 1)‖ + ‖A (j + 3)‖) / 4 := by
    intro j
    have h := congrArg norm (rec_succ_succ q j)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
    have hD := norm_sub_four_mul_sq_ge ha1 (j + 2)
    have h16 : (16 : ℝ) ≤ 4 * ((j + 2 : ℕ) : ℝ) ^ 2 := by
      push_cast; nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hS := norm_add_le (A (j + 1)) (A (j + 3))
    have hx := norm_nonneg (A (j + 2))
    have : 15 * ‖A (j + 2)‖ ≤ |q| * (‖A (j + 1)‖ + ‖A (j + 3)‖) := by
      calc 15 * ‖A (j + 2)‖ ≤ ‖(a : ℂ) - 4 * ((j + 2 : ℕ) : ℂ) ^ 2‖ * ‖A (j + 2)‖ := by
            gcongr; linarith
        _ = |q| * ‖A (j + 1) + A (j + 3)‖ := h
        _ ≤ _ := by gcongr
    nlinarith [norm_nonneg (A (j + 1)), norm_nonneg (A (j + 3))]
  obtain ⟨B, hB⟩ : ∃ B, ∀ k, ‖A k‖ ≤ B := by
    obtain ⟨B, hB⟩ := ((tendsto_mathieuFourierA_even 0 q).norm).bddAbove_range
    exact ⟨B, fun k => hB ⟨k, by simp [A]⟩⟩
  have hhalf := succ_le_half_of_le_add_div_four (f := fun j => ‖A (j + 1)‖)
    (fun _ => norm_nonneg _) (B := B) (fun j => hB _) (J := 0) (fun j _ => hquarter j)
  have hhalf' : ∀ j, ‖A (j + 2)‖ ≤ ‖A (j + 1)‖ / 2 := fun j => hhalf j (Nat.zero_le _)
  -- one-step bounds
  have hstep : ∀ j : ℕ, ‖A (j + 2)‖ ≤ |q| * ‖A (j + 1)‖ := by
    intro j
    have h := congrArg norm (rec_succ_succ q j)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
    have hD := norm_sub_four_mul_sq_ge ha1 (j + 2)
    have h16 : (16 : ℝ) ≤ 4 * ((j + 2 : ℕ) : ℝ) ^ 2 := by
      push_cast; nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hS := norm_add_le (A (j + 1)) (A (j + 3))
    have h3 : ‖A (j + 3)‖ ≤ ‖A (j + 1)‖ / 4 := by
      have := hhalf' (j + 1); have := hhalf' j; linarith
    have hx := norm_nonneg (A (j + 2))
    have : 15 * ‖A (j + 2)‖ ≤ |q| * (‖A (j + 1)‖ + ‖A (j + 3)‖) := by
      calc 15 * ‖A (j + 2)‖ ≤ ‖(a : ℂ) - 4 * ((j + 2 : ℕ) : ℂ) ^ 2‖ * ‖A (j + 2)‖ := by
            gcongr; linarith
        _ = |q| * ‖A (j + 1) + A (j + 3)‖ := h
        _ ≤ _ := by gcongr
    have : 15 * ‖A (j + 2)‖ ≤ |q| * (5 / 4 * ‖A (j + 1)‖) := by
      calc _ ≤ _ := this
        _ ≤ |q| * (5 / 4 * ‖A (j + 1)‖) := by gcongr; linarith
    nlinarith [norm_nonneg (A (j + 1))]
  have hstep0 : ‖A 1‖ ≤ |q| * ‖A 0‖ := by
    have h := congrArg norm (rec_one q)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
    have hD := norm_sub_four_mul_sq_ge ha1 1
    have hS : ‖2 * A 0 + A 2‖ ≤ 2 * ‖A 0‖ + ‖A 2‖ := by
      refine (norm_add_le _ _).trans ?_; rw [norm_mul]; norm_num
    have h2 := hhalf' 0
    have hx := norm_nonneg (A 1)
    have : 3 * ‖A 1‖ ≤ |q| * (2 * ‖A 0‖ + ‖A 1‖ / 2) := by
      calc 3 * ‖A 1‖ ≤ ‖(a : ℂ) - 4 * ((1 : ℕ) : ℂ) ^ 2‖ * ‖A 1‖ := by
            gcongr; push_cast at hD ⊢; linarith
        _ = |q| * ‖2 * A 0 + A 2‖ := h
        _ ≤ |q| * (2 * ‖A 0‖ + ‖A 2‖) := by gcongr
        _ ≤ |q| * (2 * ‖A 0‖ + ‖A 1‖ / 2) := by gcongr
    nlinarith [norm_nonneg (A 0)]
  have hchain : ∀ k, ‖A k‖ ≤ |q| ^ k * ‖A 0‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rcases k with _ | k
      · simpa using hstep0
      · calc ‖A (k + 2)‖ ≤ |q| * ‖A (k + 1)‖ := hstep k
          _ ≤ |q| * (|q| ^ (k + 1) * ‖A 0‖) := by gcongr
          _ = _ := by ring
  refine ⟨?_, ha1, fun k => by simpa [A] using hchain k⟩
  rcases eq_or_ne q 0 with rfl | hq'
  · simpa using ha4
  · have hA0 : A 0 ≠ 0 := by simpa [A] using mathieuFourierA_even_zero_ne_zero 0 hq'
    have h := congrArg norm (rec_zero q)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs] at h
    have h1 : ‖A 1‖ ≤ |q| * ‖A 0‖ := hstep0
    have hpos : 0 < ‖A 0‖ := norm_pos_iff.mpr hA0
    have : |a| * ‖A 0‖ ≤ q ^ 2 * ‖A 0‖ := by
      have e : ‖mathieuFourierA 0 (2 * 1) q‖ = ‖A 1‖ := rfl
      have e0 : ‖mathieuFourierA 0 0 q‖ = ‖A 0‖ := by simp [A]
      rw [e, e0] at h
      rw [h, ← sq_abs q]; nlinarith
    exact le_of_mul_le_mul_right this hpos

/-- The leading coefficients `(-1)^k 2/((k!)² 4^k)` of DLMF 28.4.21. -/
private noncomputable def coeff (k : ℕ) : ℂ := (-1) ^ k * 2 / (k.factorial : ℂ) ^ 2 / 4 ^ k

private lemma coeff_succ (k : ℕ) : coeff (k + 1) = -coeff k / (4 * ((k + 1 : ℕ) : ℂ) ^ 2) := by
  simp only [coeff, Nat.factorial_succ]
  have : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  push_cast
  field_simp
  ring

/-- The error constants of the induction. -/
private noncomputable def errConst : ℕ → ℝ
  | 0 => 0
  | k + 1 => errConst k + ‖coeff k‖ + 1

private lemma errConst_nonneg (k : ℕ) : 0 ≤ errConst k := by
  induction k with
  | zero => simp [errConst]
  | succ k ih => simp only [errConst]; positivity

/-- The induction of DLMF 28.4.21: for small `q`,
`‖A^0_{2k} - c_k q^k A^0_0‖ ≤ C_k |q|^{k+2} ‖A^0_0‖` (with `2 A^0_0` in place of `A^0_0` at
`k = 0`). -/
private lemma eventually_norm_sub_le : ∀ᶠ q : ℝ in 𝓝 0, ∀ k : ℕ,
    ‖(if k = 0 then 2 * mathieuFourierA 0 0 q else mathieuFourierA 0 (2 * k) q) -
      coeff k * (q : ℂ) ^ k * mathieuFourierA 0 0 q‖ ≤
      errConst k * |q| ^ (k + 2) * ‖mathieuFourierA 0 0 q‖ := by
  filter_upwards [eventually_estimates] with q ⟨ha, ha1, hchain⟩
  intro k
  induction k with
  | zero => simp [coeff, errConst]
  | succ k ih =>
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    have hrec : ((mathieuA 0 q : ℂ) - 4 * ((k + 1 : ℕ) : ℂ) ^ 2) *
        mathieuFourierA 0 (2 * (k + 1)) q =
        q * ((if k = 0 then 2 * mathieuFourierA 0 0 q else mathieuFourierA 0 (2 * k) q) +
          mathieuFourierA 0 (2 * (k + 2)) q) := by
      rcases k with _ | j
      · simpa using rec_one q
      · simp only [Nat.add_one_ne_zero, ↓reduceIte]
        exact rec_succ_succ q j
    have hY : ‖(if k = 0 then 2 * mathieuFourierA 0 0 q else mathieuFourierA 0 (2 * k) q) -
        coeff k * (q : ℂ) ^ (k + 1 - 1) * mathieuFourierA 0 0 q‖ ≤
        errConst k * |q| ^ (k + 1 + 1) * ‖mathieuFourierA 0 0 q‖ := by
      simpa using ih
    have hZ : ‖mathieuFourierA 0 (2 * (k + 2)) q‖ ≤
        |q| ^ (k + 1 + 1) * ‖mathieuFourierA 0 0 q‖ := hchain (k + 2)
    have := step (k := k + 1) (by omega) hrec ha ha1 hY hZ
    rw [← coeff_succ] at this
    simpa [errConst, add_assoc] using this

/-! ### General `m`: induction along the recurrence from the index of the eigenvalue -/

/-- One step of the induction along a three-term row. -/
private lemma step_bound {q : ℝ} {D E X Y L An c : ℂ} {C : ℝ} {k : ℕ}
    (hrow : D * X = q * (L + Y)) (hD : 1 ≤ ‖D‖) (hq1 : |q| ≤ 1)
    (hY : ‖Y - c * (q : ℂ) ^ k * An‖ ≤ C * (|q| ^ (k + 1) * ‖An‖))
    (hL : ‖L‖ ≤ 2 * ((3 * |q|) ^ (k + 2) * ‖An‖)) (hED : ‖E - D‖ ≤ 5 * |q|) (hE : E ≠ 0) :
    ‖X - c / E * (q : ℂ) ^ (k + 1) * An‖ ≤
      (C + 2 * 3 ^ (k + 2) + 5 * ‖c‖ / ‖E‖) * (|q| ^ (k + 2) * ‖An‖) := by
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
  have t1 : ‖(q : ℂ) * (Y - c * (q : ℂ) ^ k * An)‖ ≤ C * (|q| ^ (k + 2) * ‖An‖) := by
    rw [norm_mul, hqn]
    calc |q| * ‖Y - c * (q : ℂ) ^ k * An‖ ≤ |q| * (C * (|q| ^ (k + 1) * ‖An‖)) := by gcongr
      _ = _ := by ring
  have t2 : ‖(q : ℂ) * L‖ ≤ 2 * 3 ^ (k + 2) * (|q| ^ (k + 2) * ‖An‖) := by
    rw [norm_mul, hqn]
    calc |q| * ‖L‖ ≤ 1 * (2 * ((3 * |q|) ^ (k + 2) * ‖An‖)) := by gcongr
      _ = _ := by rw [mul_pow]; ring
  have t3 : ‖c * (q : ℂ) ^ (k + 1) * An * ((E - D) / E)‖ ≤
      5 * ‖c‖ / ‖E‖ * (|q| ^ (k + 2) * ‖An‖) := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, hqn, norm_div]
    rcases eq_or_ne ‖E‖ 0 with hE | hE
    · simp [hE]
    have hE' : 0 < ‖E‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hE)
    calc ‖c‖ * |q| ^ (k + 1) * ‖An‖ * (‖E - D‖ / ‖E‖)
        ≤ ‖c‖ * |q| ^ (k + 1) * ‖An‖ * (5 * |q| / ‖E‖) := by gcongr
      _ = _ := by field_simp; ring
  rw [key, norm_div]
  calc _ ≤ ‖(q : ℂ) * (Y - c * (q : ℂ) ^ k * An) + q * L +
        c * (q : ℂ) ^ (k + 1) * An * ((E - D) / E)‖ :=
        div_le_self (norm_nonneg _) hD
    _ ≤ _ := norm_add₃_le.trans (by linarith)

/-- From an estimate `F - K q^s G = O(q^{s+1} ‖G‖)` to the form `F = (K q^s + ε) G`. -/
private lemma exists_eps_of_isBigO {F G : ℝ → ℂ} {K : ℂ} {s : ℕ}
    (h : (fun q : ℝ => F q - K * (q : ℂ) ^ s * G q) =O[𝓝 0]
      (fun q : ℝ => q ^ (s + 1) * ‖G q‖)) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧
      ∀ᶠ q in 𝓝 0, F q = (K * (q : ℂ) ^ s + ε q) * G q := by
  obtain ⟨C, hC, hCw⟩ := h.exists_pos
  have hb := hCw.bound
  refine ⟨fun q => if G q = 0 then 0 else (F q - K * (q : ℂ) ^ s * G q) / G q, ?_, ?_⟩
  · refine IsBigO.of_bound C ?_
    filter_upwards [hb] with q hq
    split_ifs with hG
    · simp only [norm_zero]; positivity
    · rw [norm_mul, norm_norm] at hq
      rw [norm_div, div_le_iff₀ (norm_pos_iff.2 hG)]
      linarith
  · filter_upwards [hb] with q hq
    split_ifs with hG
    · simp only [hG, norm_zero, mul_zero, sub_zero] at hq
      rw [hG, mul_zero]
      exact norm_le_zero_iff.mp hq
    · field_simp; ring

/-- **Gap condition**: if `a(q)` is within `4|q|` of `m² = (2n+δ)²` and each diagonal entry
`d_i(q)` within `|q|` of `(2i+δ)²`, then for small `q`, `‖a(q) - d_i(q)‖ ≥ 1` for `i ≠ n`. -/
theorem eventually_one_le_norm_sub_diagonal {δ n m : ℕ} {d : ℝ → ℕ → ℂ} {a : ℝ → ℂ}
    (hm : m = 2 * n + δ)
    (hd : ∀ q i, ‖d q i - (((2 * i + δ : ℕ) : ℂ)) ^ 2‖ ≤ |q|)
    (ha : ∀ᶠ q in 𝓝 0, ‖a q - (m : ℂ) ^ 2‖ ≤ 4 * |q|) :
    ∀ᶠ q : ℝ in 𝓝 0, |q| < 1 / 8 ∧ ‖a q - (m : ℂ) ^ 2‖ ≤ 4 * |q| ∧
      ∀ i ≠ n, 1 ≤ ‖a q - d q i‖ := by
  filter_upwards [ha, eventually_abs_lt_one_div_eight] with q hq h8
  refine ⟨h8, hq, fun i hi => ?_⟩
  have h4 := four_le_abs_sq_sub_sq hi δ
  have e : ‖(((2 * i + δ : ℕ) : ℂ)) ^ 2 - (m : ℂ) ^ 2‖ =
      |(((2 * i + δ : ℕ) : ℝ)) ^ 2 - (((2 * n + δ : ℕ) : ℝ)) ^ 2| := by
    rw [show (((2 * i + δ : ℕ) : ℂ)) ^ 2 - (m : ℂ) ^ 2 =
      (((((2 * i + δ : ℕ) : ℝ)) ^ 2 - (((2 * n + δ : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) by
        subst hm; push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
  have tri : ‖(((2 * i + δ : ℕ) : ℂ)) ^ 2 - (m : ℂ) ^ 2‖ ≤
      ‖a q - d q i‖ + ‖a q - (m : ℂ) ^ 2‖ + ‖d q i - (((2 * i + δ : ℕ) : ℂ)) ^ 2‖ := by
    have := norm_add₃_le (a := -(a q - d q i)) (b := a q - (m : ℂ) ^ 2)
      (c := -(d q i - (((2 * i + δ : ℕ) : ℂ)) ^ 2))
    rw [norm_neg, norm_neg] at this
    convert this using 2; ring
  have := hd q i
  linarith


/-- The coefficient `(m-k-1)!/(k!(m-1)! 4^k)` of 28.4.23. -/
def descendingCoefficient (m k : ℕ) : ℂ :=
  ((m - k - 1).factorial : ℂ) / ((k.factorial : ℂ) * ((m - 1).factorial : ℂ)) / 4 ^ k

/-- The coefficient `(-1)^k m!/(k!(m+k)! 4^k)` of 28.4.22. -/
private def ascendingCoefficient (m k : ℕ) : ℂ :=
  (-1) ^ k * (m.factorial : ℂ) / ((k.factorial : ℂ) * ((m + k).factorial : ℂ)) / 4 ^ k

/-- `descendingCoefficient m 0 = 1`. -/
theorem descendingCoefficient_zero (m : ℕ) : descendingCoefficient m 0 = 1 := by
  simp only [descendingCoefficient, Nat.sub_zero, Nat.factorial_zero, Nat.cast_one, one_mul,
    pow_zero, div_one]
  exact div_self (by exact_mod_cast (Nat.factorial_pos _).ne')

/-- `ascendingCoefficient m 0 = 1`. -/
private lemma ascendingCoefficient_zero (m : ℕ) : ascendingCoefficient m 0 = 1 := by
  simp only [ascendingCoefficient, add_zero, Nat.factorial_zero, Nat.cast_one, one_mul,
    pow_zero, div_one]
  exact div_self (by exact_mod_cast (Nat.factorial_pos _).ne')

/-- `m² - (m - 2(k+1))² = 4(k+1)(m-k-1) ≠ 0` for `m = 2n+δ`, `k < n`. -/
theorem sq_sub_sq_descending {δ n m k : ℕ} (hm : m = 2 * n + δ) (hk : k + 1 ≤ n) :
    (m : ℂ) ^ 2 - (((2 * (n - (k + 1)) + δ : ℕ) : ℂ)) ^ 2 =
      4 * ((k : ℂ) + 1) * (((m - k - 2 : ℕ) : ℂ) + 1) ∧
    (m : ℂ) ^ 2 - (((2 * (n - (k + 1)) + δ : ℕ) : ℂ)) ^ 2 ≠ 0 := by
  obtain ⟨r, hr⟩ : ∃ r, m = k + 2 + r := ⟨m - k - 2, by omega⟩
  have h1 : ((2 * (n - (k + 1)) + δ : ℕ) : ℂ) = (m : ℂ) - 2 * ((k : ℂ) + 1) := by
    have : 2 * (n - (k + 1)) + δ + 2 * (k + 1) = m := by omega
    rw [eq_sub_iff_add_eq]; exact_mod_cast this
  have h2 : m - k - 2 = r := by omega
  rw [h1, h2, hr]; push_cast
  refine ⟨by ring, ?_⟩
  rw [show ((k : ℂ) + 2 + r) ^ 2 - ((k : ℂ) + 2 + r - 2 * ((k : ℂ) + 1)) ^ 2 =
    4 * ((k : ℂ) + 1) * ((r : ℂ) + 1) by ring]
  exact mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (by exact_mod_cast k.succ_ne_zero))
    (by exact_mod_cast r.succ_ne_zero)

/-- Recurrence of the coefficients of 28.4.23 along the rows below `m`. -/
theorem descendingCoefficient_succ {δ n m k : ℕ} (hm : m = 2 * n + δ) (hk : k + 1 ≤ n) :
    descendingCoefficient m k / ((m : ℂ) ^ 2 - (((2 * (n - (k + 1)) + δ : ℕ) : ℂ)) ^ 2) =
      descendingCoefficient m (k + 1) := by
  rw [(sq_sub_sq_descending hm hk).1]
  obtain ⟨r, hr⟩ : ∃ r, m = k + 2 + r := ⟨m - k - 2, by omega⟩
  rw [show m - k - 2 = r by omega]
  simp only [descendingCoefficient]
  rw [show m - k - 1 = r + 1 by omega, show m - (k + 1) - 1 = r by omega,
    Nat.factorial_succ r, Nat.factorial_succ k]
  have := (Nat.factorial_pos r).ne'
  have := (Nat.factorial_pos k).ne'
  have := (Nat.factorial_pos (m - 1)).ne'
  push_cast
  field_simp
  ring

/-- `m² - (m + 2(k+1))² = -4(k+1)(m+k+1) ≠ 0`. -/
private lemma sq_sub_sq_ascending {δ n m k : ℕ} (hm : m = 2 * n + δ) :
    (m : ℂ) ^ 2 - (((2 * (n + (k + 1)) + δ : ℕ) : ℂ)) ^ 2 =
      -(4 * ((k : ℂ) + 1) * ((m : ℂ) + k + 1)) ∧
    (m : ℂ) ^ 2 - (((2 * (n + (k + 1)) + δ : ℕ) : ℂ)) ^ 2 ≠ 0 := by
  have h1 : ((2 * (n + (k + 1)) + δ : ℕ) : ℂ) = (m : ℂ) + 2 * ((k : ℂ) + 1) := by
    rw [hm]; push_cast; ring
  rw [h1]
  refine ⟨by ring, ?_⟩
  rw [show (m : ℂ) ^ 2 - ((m : ℂ) + 2 * ((k : ℂ) + 1)) ^ 2 =
    -(4 * ((k : ℂ) + 1) * (((m + k : ℕ) : ℂ) + 1)) by push_cast; ring]
  exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0)
    (by exact_mod_cast k.succ_ne_zero))
    (by exact_mod_cast (m + k).succ_ne_zero))

/-- Recurrence of the coefficients of 28.4.22 along the rows above `m`. -/
private lemma ascendingCoefficient_succ {δ n m k : ℕ} (hm : m = 2 * n + δ) :
    ascendingCoefficient m k / ((m : ℂ) ^ 2 - (((2 * (n + (k + 1)) + δ : ℕ) : ℂ)) ^ 2) =
      ascendingCoefficient m (k + 1) := by
  rw [(sq_sub_sq_ascending hm).1]
  simp only [ascendingCoefficient]
  rw [show m + (k + 1) = (m + k) + 1 by ring, Nat.factorial_succ (m + k), Nat.factorial_succ k]
  have := (Nat.factorial_pos m).ne'
  have := (Nat.factorial_pos k).ne'
  have := (Nat.factorial_pos (m + k)).ne'
  have h4 : ((m : ℂ) + k + 1) ≠ 0 := by exact_mod_cast (m + k).succ_ne_zero
  push_cast
  field_simp
  ring

/-- The norm of `q^j ‖x‖` as a real function. -/
private lemma norm_pow_mul_norm (q : ℝ) (j : ℕ) (x : ℂ) : ‖q ^ j * ‖x‖‖ = |q| ^ j * ‖x‖ := by
  rw [norm_mul, norm_pow, Real.norm_eq_abs, norm_norm]

/-- **Downward estimate**: for a decaying solution of a Mathieu-type recurrence with eigenvalue
near `m² = (2n+δ)²`, `A_{n-k} = (m-k-1)!/(k!(m-1)!) (q/4)^k A_n + O(q^{k+1} A_n)`. -/
private lemma down_isBigO {δ n m : ℕ} {β : ℂ} {d : ℝ → ℕ → ℂ} {a : ℝ → ℂ} {A : ℝ → ℕ → ℂ}
    (hm : m = 2 * n + δ) (hβ : ‖β‖ ≤ 2)
    (hrec : ∀ q : ℝ, SolvesRecurrence (d q) β q (a q) (A q))
    (hlim : ∀ q, Tendsto (A q) atTop (𝓝 0))
    (hd : ∀ q i, ‖d q i - (((2 * i + δ : ℕ) : ℂ)) ^ 2‖ ≤ |q|)
    (ha : ∀ᶠ q in 𝓝 0, ‖a q - (m : ℂ) ^ 2‖ ≤ 4 * |q|) :
    ∀ k ≤ n, (fun q : ℝ => A q (n - k) - descendingCoefficient m k * (q : ℂ) ^ k * A q n) =O[𝓝 0]
      (fun q : ℝ => q ^ (k + 1) * ‖A q n‖) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [Nat.sub_zero, descendingCoefficient_zero, pow_zero, one_mul, mul_one, sub_self]
    exact isBigO_zero _ _
  | succ k ih =>
    intro hk
    obtain ⟨C, hC⟩ := (ih (by omega)).bound
    set i := n - (k + 1) with hi
    set E : ℂ := (m : ℂ) ^ 2 - (((2 * i + δ : ℕ) : ℂ)) ^ 2 with hEdef
    have hE : E ≠ 0 := (sq_sub_sq_descending hm hk).2
    refine IsBigO.of_bound (C + 2 * 3 ^ (k + 2) + 5 * ‖descendingCoefficient m k‖ / ‖E‖) ?_
    filter_upwards [hC, eventually_one_le_norm_sub_diagonal hm hd ha] with q hq ⟨h8, ham, hgap⟩
    rw [norm_pow_mul_norm] at hq ⊢
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
    have hED : ‖E - (a q - d q i)‖ ≤ 5 * |q| := by
      have := norm_sub_le (d q i - (((2 * i + δ : ℕ) : ℂ)) ^ 2) (a q - (m : ℂ) ^ 2)
      rw [show d q i - (((2 * i + δ : ℕ) : ℂ)) ^ 2 - (a q - (m : ℂ) ^ 2) = E - (a q - d q i) by
        simp only [hEdef]; ring] at this
      linarith [hd q i]
    have hD : 1 ≤ ‖a q - d q i‖ := hgap i (by omega)
    have := step_bound (k := k) hrow hD (by linarith) hq hL hED hE
    rwa [show descendingCoefficient m k / E = descendingCoefficient m (k + 1) from
      descendingCoefficient_succ hm hk] at this

/-- The lower neighbour of the row `n + k + 1` is `A_{n+k}`. -/
private lemma recurrenceLower_add_one {β : ℂ} {n k : ℕ} (hβ : n ≠ 0 ∨ β = 1) (A : ℕ → ℂ) :
    recurrenceLower β A (n + (k + 1)) = A (n + k) := by
  rcases Nat.eq_zero_or_pos (n + k) with h | h
  · obtain ⟨rfl, rfl⟩ : n = 0 ∧ k = 0 := by omega
    rcases hβ with h | rfl
    · exact absurd rfl h
    · simp [recurrenceLower]
  · obtain ⟨j, hj⟩ : ∃ j, n + k = j + 1 := ⟨n + k - 1, by omega⟩
    rw [show n + (k + 1) = j + 2 by omega, hj]
    rfl

/-- **Upward estimate**: `A_{n+k} = (-1)^k m!/(k!(m+k)!) (q/4)^k A_n + O(q^{k+1} A_n)`. -/
private lemma up_isBigO {δ n m : ℕ} {β : ℂ} {d : ℝ → ℕ → ℂ} {a : ℝ → ℂ} {A : ℝ → ℕ → ℂ}
    (hm : m = 2 * n + δ) (hβ : ‖β‖ ≤ 2) (hβ1 : n ≠ 0 ∨ β = 1)
    (hrec : ∀ q : ℝ, SolvesRecurrence (d q) β q (a q) (A q))
    (hlim : ∀ q, Tendsto (A q) atTop (𝓝 0))
    (hd : ∀ q i, ‖d q i - (((2 * i + δ : ℕ) : ℂ)) ^ 2‖ ≤ |q|)
    (ha : ∀ᶠ q in 𝓝 0, ‖a q - (m : ℂ) ^ 2‖ ≤ 4 * |q|) (k : ℕ) :
    (fun q : ℝ => A q (n + k) - ascendingCoefficient m k * (q : ℂ) ^ k * A q n) =O[𝓝 0]
      (fun q : ℝ => q ^ (k + 1) * ‖A q n‖) := by
  induction k with
  | zero =>
    simp only [add_zero, ascendingCoefficient_zero, pow_zero, one_mul, mul_one, sub_self]
    exact isBigO_zero _ _
  | succ k ih =>
    obtain ⟨C, hC⟩ := ih.bound
    set i := n + (k + 1) with hi
    set E : ℂ := (m : ℂ) ^ 2 - (((2 * i + δ : ℕ) : ℂ)) ^ 2 with hEdef
    have hE : E ≠ 0 := (sq_sub_sq_ascending hm).2
    refine IsBigO.of_bound (C + 2 * 3 ^ (k + 2) + 5 * ‖ascendingCoefficient m k‖ / ‖E‖) ?_
    filter_upwards [hC, eventually_one_le_norm_sub_diagonal hm hd ha] with q hq ⟨h8, ham, hgap⟩
    rw [norm_pow_mul_norm] at hq ⊢
    have hq4 : ‖(q : ℂ)‖ ≤ 1 / 4 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; linarith
    have hqn : ‖(q : ℂ)‖ = |q| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have hdec := norm_le_pow_dist_mul_of_solvesRecurrence hβ (hrec q) (hlim q) hq4 hgap
    rw [hqn] at hdec
    have hrow : (a q - d q i) * A q i = q * (A q (i + 1) + A q (n + k)) := by
      have := hrec q i
      simp only [recurrenceOperator] at this
      rw [hi, recurrenceLower_add_one hβ1] at this
      linear_combination -this
    have hL : ‖A q (i + 1)‖ ≤ 2 * ((3 * |q|) ^ (k + 2) * ‖A q n‖) := by
      have := hdec (i + 1)
      rw [show Nat.dist (i + 1) n = k + 2 by simp [Nat.dist]; omega] at this
      have h0 : 0 ≤ (3 * |q|) ^ (k + 2) * ‖A q n‖ := by positivity
      linarith
    have hED : ‖E - (a q - d q i)‖ ≤ 5 * |q| := by
      have := norm_sub_le (d q i - (((2 * i + δ : ℕ) : ℂ)) ^ 2) (a q - (m : ℂ) ^ 2)
      rw [show d q i - (((2 * i + δ : ℕ) : ℂ)) ^ 2 - (a q - (m : ℂ) ^ 2) = E - (a q - d q i) by
        simp only [hEdef]; ring] at this
      linarith [hd q i]
    have hD : 1 ≤ ‖a q - d q i‖ := hgap i (by omega)
    have := step_bound (k := k) hrow hD (by linarith) hq hL hED hE
    rwa [show ascendingCoefficient m k / E = ascendingCoefficient m (k + 1) from
      ascendingCoefficient_succ hm] at this

/-- 28.4.23 for a decaying solution of a Mathieu-type recurrence. -/
private lemma down_final {δ n m s : ℕ} {β : ℂ} {d : ℝ → ℕ → ℂ} {a : ℝ → ℂ} {A : ℝ → ℕ → ℂ}
    (hm : m = 2 * n + δ) (hβ : ‖β‖ ≤ 2)
    (hrec : ∀ q : ℝ, SolvesRecurrence (d q) β q (a q) (A q))
    (hlim : ∀ q, Tendsto (A q) atTop (𝓝 0))
    (hd : ∀ q i, ‖d q i - (((2 * i + δ : ℕ) : ℂ)) ^ 2‖ ≤ |q|)
    (ha : ∀ᶠ q in 𝓝 0, ‖a q - (m : ℂ) ^ 2‖ ≤ 4 * |q|) (hs : s ≤ n) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ᶠ q in 𝓝 0,
      A q (n - s) = (((m - s - 1).factorial : ℂ) /
        ((s.factorial : ℂ) * ((m - 1).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) * A q n := by
  obtain ⟨ε, h1, h2⟩ := exists_eps_of_isBigO (down_isBigO hm hβ hrec hlim hd ha s hs)
  refine ⟨ε, h1, ?_⟩
  filter_upwards [h2] with q hq
  rw [hq, div_pow]; simp only [descendingCoefficient]; ring

/-- 28.4.22 for a decaying solution of a Mathieu-type recurrence. -/
private lemma up_final {δ n m s : ℕ} {β : ℂ} {d : ℝ → ℕ → ℂ} {a : ℝ → ℂ} {A : ℝ → ℕ → ℂ}
    (hm : m = 2 * n + δ) (hβ : ‖β‖ ≤ 2) (hβ1 : n ≠ 0 ∨ β = 1)
    (hrec : ∀ q : ℝ, SolvesRecurrence (d q) β q (a q) (A q))
    (hlim : ∀ q, Tendsto (A q) atTop (𝓝 0))
    (hd : ∀ q i, ‖d q i - (((2 * i + δ : ℕ) : ℂ)) ^ 2‖ ≤ |q|)
    (ha : ∀ᶠ q in 𝓝 0, ‖a q - (m : ℂ) ^ 2‖ ≤ 4 * |q|) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ᶠ q in 𝓝 0,
      A q (n + s) = ((-1) ^ s * (m.factorial : ℂ) /
        ((s.factorial : ℂ) * ((m + s).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) * A q n := by
  obtain ⟨ε, h1, h2⟩ := exists_eps_of_isBigO (up_isBigO hm hβ hβ1 hrec hlim hd ha s)
  refine ⟨ε, h1, ?_⟩
  filter_upwards [h2] with q hq
  rw [hq, div_pow]; simp only [ascendingCoefficient]; ring

/-- `‖a_m(q) - m²‖ ≤ 4|q|` for small `q`, in complex form. -/
theorem eventually_norm_mathieuA_sub_sq_le (m : ℕ) :
    ∀ᶠ q : ℝ in 𝓝 0, ‖(mathieuA m q : ℂ) - (m : ℂ) ^ 2‖ ≤ 4 * |q| := by
  filter_upwards [eventually_abs_mathieuA_sub_sq_le m] with q hq
  rwa [show (mathieuA m q : ℂ) - (m : ℂ) ^ 2 = ((mathieuA m q - (m : ℝ) ^ 2 : ℝ) : ℂ) by
    push_cast; ring, Complex.norm_real, Real.norm_eq_abs]

/-- `‖b_m(q) - m²‖ ≤ 4|q|` for small `q`, in complex form. -/
theorem eventually_norm_mathieuB_sub_sq_le {m : ℕ} (hm : m ≠ 0) :
    ∀ᶠ q : ℝ in 𝓝 0, ‖(mathieuB m q : ℂ) - (m : ℂ) ^ 2‖ ≤ 4 * |q| := by
  filter_upwards [eventually_abs_mathieuB_sub_sq_le hm] with q hq
  rwa [show (mathieuB m q : ℂ) - (m : ℂ) ^ 2 = ((mathieuB m q - (m : ℝ) ^ 2 : ℝ) : ℂ) by
    push_cast; ring, Complex.norm_real, Real.norm_eq_abs]

/-- The diagonal of 28.4.5 is `(2i)²`. -/
theorem norm_four_mul_sq_sub_sq_le (q : ℝ) (i : ℕ) :
    ‖4 * (i : ℂ) ^ 2 - (((2 * i + 0 : ℕ) : ℂ)) ^ 2‖ ≤ |q| := by
  rw [show 4 * (i : ℂ) ^ 2 - (((2 * i + 0 : ℕ) : ℂ)) ^ 2 = 0 by push_cast; ring, norm_zero]
  exact abs_nonneg q

/-- The diagonal of 28.4.8 is `(2i+2)²`. -/
theorem norm_two_mul_add_two_sq_sub_sq_le (q : ℝ) (i : ℕ) :
    ‖(2 * (i : ℂ) + 2) ^ 2 - (((2 * i + 2 : ℕ) : ℂ)) ^ 2‖ ≤ |q| := by
  rw [show (2 * (i : ℂ) + 2) ^ 2 - (((2 * i + 2 : ℕ) : ℂ)) ^ 2 = 0 by push_cast; ring, norm_zero]
  exact abs_nonneg q

/-- The diagonal of 28.4.6 is within `|q|` of `(2i+1)²`. -/
theorem norm_odd_sq_add_ite_sub_sq_le (q : ℝ) (i : ℕ) :
    ‖((2 * (i : ℂ) + 1) ^ 2 + if i = 0 then (q : ℂ) else 0) - (((2 * i + 1 : ℕ) : ℂ)) ^ 2‖ ≤
      |q| := by
  rw [show ((2 * (i : ℂ) + 1) ^ 2 + if i = 0 then (q : ℂ) else 0) - (((2 * i + 1 : ℕ) : ℂ)) ^ 2 =
    if i = 0 then (q : ℂ) else 0 by push_cast; ring]
  split_ifs <;> simp

/-- The diagonal of 28.4.7 is within `|q|` of `(2i+1)²`. -/
theorem norm_odd_sq_sub_ite_sub_sq_le (q : ℝ) (i : ℕ) :
    ‖((2 * (i : ℂ) + 1) ^ 2 - if i = 0 then (q : ℂ) else 0) - (((2 * i + 1 : ℕ) : ℂ)) ^ 2‖ ≤
      |q| := by
  rw [show ((2 * (i : ℂ) + 1) ^ 2 - if i = 0 then (q : ℂ) else 0) - (((2 * i + 1 : ℕ) : ℂ)) ^ 2 =
    -(if i = 0 then (q : ℂ) else 0) by push_cast; ring]
  split_ifs <;> simp

end SmallQFourier

/-! ### Behavior for small `q` (§28.4(vi)) -/

open SmallQFourier in
/-- **DLMF 28.4.21**: for fixed `s ≥ 1`,
`A^0_{2s}(q) = ((-1)^s 2/(s!)² (q/4)^s + O(q^{s+2})) A^0_0(q)` as `q → 0`. -/
@[dlmf 28.4.E21]
theorem mathieuFourierA_zero_small_q {s : ℕ} (hs : 1 ≤ s) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 2)) ∧ ∀ q : ℝ,
      mathieuFourierA 0 (2 * s) q = ((-1) ^ s * 2 / (s.factorial : ℂ) ^ 2 * ((q : ℂ) / 4) ^ s +
        ε q) * mathieuFourierA 0 0 q := by
  have hcs : ∀ q : ℝ, (-1) ^ s * 2 / (s.factorial : ℂ) ^ 2 * ((q : ℂ) / 4) ^ s =
      coeff s * (q : ℂ) ^ s := by
    intro q; simp only [coeff]; rw [div_pow]; ring
  set ε : ℝ → ℂ := fun q => if mathieuFourierA 0 0 q = 0 then 0 else
    mathieuFourierA 0 (2 * s) q / mathieuFourierA 0 0 q - coeff s * (q : ℂ) ^ s
  have hs0 : s ≠ 0 := by omega
  refine ⟨ε, ?_, fun q => ?_⟩
  · refine Asymptotics.IsBigO.of_bound (errConst s) ?_
    filter_upwards [eventually_norm_sub_le] with q hq
    have h := hq s
    simp only [hs0, ↓reduceIte] at h
    simp only [ε, norm_pow, Real.norm_eq_abs]
    split_ifs with h0
    · rw [norm_zero]
      exact mul_nonneg (errConst_nonneg s) (by positivity)
    · have hpos : 0 < ‖mathieuFourierA 0 0 q‖ := norm_pos_iff.mpr h0
      rw [show mathieuFourierA 0 (2 * s) q / mathieuFourierA 0 0 q - coeff s * (q : ℂ) ^ s =
        (mathieuFourierA 0 (2 * s) q - coeff s * (q : ℂ) ^ s * mathieuFourierA 0 0 q) /
          mathieuFourierA 0 0 q by field_simp, norm_div, div_le_iff₀ hpos]
      exact h
  · rw [hcs]
    simp only [ε]
    split_ifs with h0
    · rw [h0, mul_zero]
      rcases eq_or_ne q 0 with rfl | hq
      · have h := (eventually_estimates.self_of_nhds).2.2 s
        rw [h0, norm_zero, mul_zero] at h
        exact norm_le_zero_iff.mp h
      · exact absurd h0 (by simpa using mathieuFourierA_even_zero_ne_zero 0 hq)
    · field_simp; ring

open SmallQFourier in
/-- **DLMF 28.4.22** (`A`): for fixed `m ≥ 1` and `s`,
`A^m_{m+2s}(q) = ((-1)^s m!/(s!(m+s)!) (q/4)^s + O(q^{s+1})) A^m_m(q)` as `q → 0`.
Stronger than DLMF, which assumes `s ≥ 1`. -/
@[dlmf 28.4.E22 "stronger than DLMF: s = 0 allowed"]
theorem mathieuFourierA_up_small_q' {m s : ℕ} (hm : 1 ≤ m) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ᶠ q in 𝓝 0,
      mathieuFourierA m (m + 2 * s) q = ((-1) ^ s * (m.factorial : ℂ) /
        ((s.factorial : ℂ) * ((m + s).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierA m m q := by
  rcases Nat.even_or_odd' m with ⟨n, rfl | rfl⟩
  · obtain ⟨ε, h1, h2⟩ := up_final (s := s) (n := n) (m := 2 * n) (δ := 0) (β := 2)
      (A := fun q i => mathieuFourierA (2 * n) (2 * i) q) rfl (by norm_num) (.inl (by omega))
      (solvesRecurrence_mathieuFourierA_even n) (tendsto_mathieuFourierA_even n)
      norm_four_mul_sq_sub_sq_le
      (eventually_norm_mathieuA_sub_sq_le _)
    refine ⟨ε, h1, ?_⟩
    filter_upwards [h2] with q hq
    rw [show 2 * n + 2 * s = 2 * (n + s) by ring]
    exact hq
  · obtain ⟨ε, h1, h2⟩ := up_final (s := s) (n := n) (δ := 1) (β := 1)
      (A := fun q i => mathieuFourierA (2 * n + 1) (2 * i + 1) q) rfl (by norm_num) (.inr rfl)
      (solvesRecurrence_mathieuFourierA_odd n) (tendsto_mathieuFourierA_odd n)
      norm_odd_sq_add_ite_sub_sq_le
      (eventually_norm_mathieuA_sub_sq_le _)
    refine ⟨ε, h1, ?_⟩
    filter_upwards [h2] with q hq
    rw [show 2 * n + 1 + 2 * s = 2 * (n + s) + 1 by ring]
    exact hq

/-- **DLMF 28.4.22** (`A`): for fixed `s, m ≥ 1`,
`A^m_{m+2s}(q) = ((-1)^s m!/(s!(m+s)!) (q/4)^s + O(q^{s+1})) A^m_m(q)` as `q → 0`. -/
@[dlmf 28.4.E22]
theorem mathieuFourierA_up_small_q {m s : ℕ} (hm : 1 ≤ m) (_hs : 1 ≤ s) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ᶠ q in 𝓝 0,
      mathieuFourierA m (m + 2 * s) q = ((-1) ^ s * (m.factorial : ℂ) /
        ((s.factorial : ℂ) * ((m + s).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierA m m q :=
  mathieuFourierA_up_small_q' hm

open SmallQFourier in
/-- **DLMF 28.4.22** (`B`):
`B^m_{m+2s}(q) = ((-1)^s m!/(s!(m+s)!) (q/4)^s + O(q^{s+1})) B^m_m(q)`.
Stronger than DLMF, which assumes `s ≥ 1`. -/
@[dlmf 28.4.E22 "stronger than DLMF: s = 0 allowed"]
theorem mathieuFourierB_up_small_q' {m s : ℕ} (hm : 1 ≤ m) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ᶠ q in 𝓝 0,
      mathieuFourierB m (m + 2 * s) q = ((-1) ^ s * (m.factorial : ℂ) /
        ((s.factorial : ℂ) * ((m + s).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierB m m q := by
  rcases Nat.even_or_odd' m with ⟨n, rfl | rfl⟩
  · obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    obtain ⟨ε, h1, h2⟩ := up_final (s := s) (n := n) (δ := 2) (β := 1)
      (A := fun q i => mathieuFourierB (2 * n + 2) (2 * i + 2) q) (by ring) (by norm_num)
      (.inr rfl) (solvesRecurrence_mathieuFourierB_even n) (tendsto_mathieuFourierB_even n)
      norm_two_mul_add_two_sq_sub_sq_le (eventually_norm_mathieuB_sub_sq_le (by omega))
    refine ⟨ε, h1, ?_⟩
    filter_upwards [h2] with q hq
    rw [show 2 * (n + 1) + 2 * s = 2 * (n + s) + 2 by ring, show 2 * (n + 1) = 2 * n + 2 by ring]
    exact hq
  · obtain ⟨ε, h1, h2⟩ := up_final (s := s) (n := n) (δ := 1) (β := 1)
      (A := fun q i => mathieuFourierB (2 * n + 1) (2 * i + 1) q) rfl (by norm_num) (.inr rfl)
      (solvesRecurrence_mathieuFourierB_odd n) (tendsto_mathieuFourierB_odd n)
      norm_odd_sq_sub_ite_sub_sq_le
      (eventually_norm_mathieuB_sub_sq_le (by omega))
    refine ⟨ε, h1, ?_⟩
    filter_upwards [h2] with q hq
    rw [show 2 * n + 1 + 2 * s = 2 * (n + s) + 1 by ring]
    exact hq

/-- **DLMF 28.4.22** (`B`):
`B^m_{m+2s}(q) = ((-1)^s m!/(s!(m+s)!) (q/4)^s + O(q^{s+1})) B^m_m(q)`. -/
@[dlmf 28.4.E22]
theorem mathieuFourierB_up_small_q {m s : ℕ} (hm : 1 ≤ m) (_hs : 1 ≤ s) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ᶠ q in 𝓝 0,
      mathieuFourierB m (m + 2 * s) q = ((-1) ^ s * (m.factorial : ℂ) /
        ((s.factorial : ℂ) * ((m + s).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierB m m q :=
  mathieuFourierB_up_small_q' hm

open SmallQFourier in
/-- **DLMF 28.4.23** (`A`): for `2s ≤ m`,
`A^m_{m-2s}(q) = ((m-s-1)!/(s!(m-1)!) (q/4)^s + O(q^{s+1})) A^m_m(q)` as `q → 0`.
Stronger than DLMF, which assumes `s ≥ 1`. -/
@[dlmf 28.4.E23 "stronger than DLMF: s = 0 allowed"]
theorem mathieuFourierA_down_small_q' {m s : ℕ} (hsm : 2 * s ≤ m) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ᶠ q in 𝓝 0,
      mathieuFourierA m (m - 2 * s) q = (((m - s - 1).factorial : ℂ) /
        ((s.factorial : ℂ) * ((m - 1).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierA m m q := by
  rcases Nat.even_or_odd' m with ⟨n, rfl | rfl⟩
  · obtain ⟨ε, h1, h2⟩ := down_final (s := s) (n := n) (m := 2 * n) (δ := 0) (β := 2)
      (A := fun q i => mathieuFourierA (2 * n) (2 * i) q) rfl (by norm_num)
      (solvesRecurrence_mathieuFourierA_even n) (tendsto_mathieuFourierA_even n)
      norm_four_mul_sq_sub_sq_le
      (eventually_norm_mathieuA_sub_sq_le _) (by omega)
    refine ⟨ε, h1, ?_⟩
    filter_upwards [h2] with q hq
    rw [show 2 * n - 2 * s = 2 * (n - s) by omega]
    exact hq
  · obtain ⟨ε, h1, h2⟩ := down_final (s := s) (n := n) (δ := 1) (β := 1)
      (A := fun q i => mathieuFourierA (2 * n + 1) (2 * i + 1) q) rfl (by norm_num)
      (solvesRecurrence_mathieuFourierA_odd n) (tendsto_mathieuFourierA_odd n)
      norm_odd_sq_add_ite_sub_sq_le
      (eventually_norm_mathieuA_sub_sq_le _) (by omega)
    refine ⟨ε, h1, ?_⟩
    filter_upwards [h2] with q hq
    rw [show 2 * n + 1 - 2 * s = 2 * (n - s) + 1 by omega]
    exact hq

/-- **DLMF 28.4.23** (`A`): for `1 ≤ s` and `2s ≤ m`,
`A^m_{m-2s}(q) = ((m-s-1)!/(s!(m-1)!) (q/4)^s + O(q^{s+1})) A^m_m(q)` as `q → 0`. -/
@[dlmf 28.4.E23]
theorem mathieuFourierA_down_small_q {m s : ℕ} (_hs : 1 ≤ s) (hsm : 2 * s ≤ m) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ᶠ q in 𝓝 0,
      mathieuFourierA m (m - 2 * s) q = (((m - s - 1).factorial : ℂ) /
        ((s.factorial : ℂ) * ((m - 1).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierA m m q :=
  mathieuFourierA_down_small_q' hsm

open SmallQFourier in
/-- **DLMF 28.4.23** (`B`): for `2s < m`,
`B^m_{m-2s}(q) = ((m-s-1)!/(s!(m-1)!) (q/4)^s + O(q^{s+1})) B^m_m(q)` as `q → 0`.
Stronger than DLMF, which assumes `s ≥ 1`. -/
@[dlmf 28.4.E23 "stronger than DLMF: s = 0 allowed"]
theorem mathieuFourierB_down_small_q' {m s : ℕ} (hsm : 2 * s < m) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ᶠ q in 𝓝 0,
      mathieuFourierB m (m - 2 * s) q = (((m - s - 1).factorial : ℂ) /
        ((s.factorial : ℂ) * ((m - 1).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierB m m q := by
  rcases Nat.even_or_odd' m with ⟨n, rfl | rfl⟩
  · obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    obtain ⟨ε, h1, h2⟩ := down_final (s := s) (n := n) (δ := 2) (β := 1)
      (A := fun q i => mathieuFourierB (2 * n + 2) (2 * i + 2) q) (by ring) (by norm_num)
      (solvesRecurrence_mathieuFourierB_even n) (tendsto_mathieuFourierB_even n)
      norm_two_mul_add_two_sq_sub_sq_le (eventually_norm_mathieuB_sub_sq_le (by omega)) (by omega)
    refine ⟨ε, h1, ?_⟩
    filter_upwards [h2] with q hq
    rw [show 2 * (n + 1) - 2 * s = 2 * (n - s) + 2 by omega, show 2 * (n + 1) = 2 * n + 2 by ring]
    exact hq
  · obtain ⟨ε, h1, h2⟩ := down_final (s := s) (n := n) (δ := 1) (β := 1)
      (A := fun q i => mathieuFourierB (2 * n + 1) (2 * i + 1) q) rfl (by norm_num)
      (solvesRecurrence_mathieuFourierB_odd n) (tendsto_mathieuFourierB_odd n)
      norm_odd_sq_sub_ite_sub_sq_le
      (eventually_norm_mathieuB_sub_sq_le (by omega)) (by omega)
    refine ⟨ε, h1, ?_⟩
    filter_upwards [h2] with q hq
    rw [show 2 * n + 1 - 2 * s = 2 * (n - s) + 1 by omega]
    exact hq

/-- **DLMF 28.4.23** (`B`): for `1 ≤ s` and `2s < m`,
`B^m_{m-2s}(q) = ((m-s-1)!/(s!(m-1)!) (q/4)^s + O(q^{s+1})) B^m_m(q)` as `q → 0`. -/
@[dlmf 28.4.E23]
theorem mathieuFourierB_down_small_q {m s : ℕ} (_hs : 1 ≤ s) (hsm : 2 * s < m) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ᶠ q in 𝓝 0,
      mathieuFourierB m (m - 2 * s) q = (((m - s - 1).factorial : ℂ) /
        ((s.factorial : ℂ) * ((m - 1).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierB m m q :=
  mathieuFourierB_down_small_q' hsm

end DLMF.Mathieu
