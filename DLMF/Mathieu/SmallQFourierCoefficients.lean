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
* `mathieuFourierA_up_small_q`, `mathieuFourierB_up_small_q`: DLMF 28.4.22.
* `mathieuFourierA_down_small_q`, `mathieuFourierB_down_small_q`: DLMF 28.4.23.
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

/-- **DLMF 28.4.22** (`A`): for fixed `s, m ≥ 1`,
`A^m_{m+2s}(q) = ((-1)^s m!/(s!(m+s)!) (q/4)^s + O(q^{s+1})) A^m_m(q)` as `q → 0`. -/
@[dlmf 28.4.E22]
theorem mathieuFourierA_up_small_q {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ q : ℝ,
      mathieuFourierA m (m + 2 * s) q = ((-1) ^ s * (m.factorial : ℂ) /
        ((s.factorial : ℂ) * ((m + s).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierA m m q := by
  sorry

/-- **DLMF 28.4.22** (`B`):
`B^m_{m+2s}(q) = ((-1)^s m!/(s!(m+s)!) (q/4)^s + O(q^{s+1})) B^m_m(q)`. -/
@[dlmf 28.4.E22]
theorem mathieuFourierB_up_small_q {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ q : ℝ,
      mathieuFourierB m (m + 2 * s) q = ((-1) ^ s * (m.factorial : ℂ) /
        ((s.factorial : ℂ) * ((m + s).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierB m m q := by
  sorry

/-- **DLMF 28.4.23** (`A`): for `1 ≤ s` and `2s ≤ m`,
`A^m_{m-2s}(q) = ((m-s-1)!/(s!(m-1)!) (q/4)^s + O(q^{s+1})) A^m_m(q)` as `q → 0`. -/
@[dlmf 28.4.E23]
theorem mathieuFourierA_down_small_q {m s : ℕ} (hs : 1 ≤ s) (hsm : 2 * s ≤ m) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ q : ℝ,
      mathieuFourierA m (m - 2 * s) q = (((m - s - 1).factorial : ℂ) /
        ((s.factorial : ℂ) * ((m - 1).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierA m m q := by
  sorry

/-- **DLMF 28.4.23** (`B`): for `1 ≤ s` and `2s < m`,
`B^m_{m-2s}(q) = ((m-s-1)!/(s!(m-1)!) (q/4)^s + O(q^{s+1})) B^m_m(q)` as `q → 0`. -/
@[dlmf 28.4.E23]
theorem mathieuFourierB_down_small_q {m s : ℕ} (hs : 1 ≤ s) (hsm : 2 * s < m) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ q : ℝ,
      mathieuFourierB m (m - 2 * s) q = (((m - s - 1).factorial : ℂ) /
        ((s.factorial : ℂ) * ((m - 1).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierB m m q := by
  sorry

end DLMF.Mathieu
