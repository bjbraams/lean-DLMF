/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Basic
public import DLMFMathlib.Analysis.ContinuedFraction.Convergence
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Continued fractions with odd partial denominators

The continued fraction `a₀/(1 + c/(3 + c/(5 + ⋯)))` converges for every `c` to `a₀ w₁(c)/w₀(c)`,
where `w_k(c) = ∑ₘ (c/2)^m / (m! · 1·3···(2k+2m-1))` is the entire backward solution of
`w_k = (2k+1) w_{k+1} + c w_{k+2}` (for `c = -z²` it is `z^{1-k} j_{k-1}(z)`, a spherical Bessel
function). Lambert's continued fractions for `tan` and `tanh` (DLMF 4.25.1, 4.39.1) and the
continued fraction DLMF 4.9.3 for `exp` follow.

## Main definitions

* `oddFactorialProd`: the odd products `1·3···(2k-1)`.
* `oddFractionTail`: the backward solution `w_k(c)`.

## Main results

* `oddFractionTail_recurrence`: the three-term recurrence.
* `hasContinuedFraction_oddFractionTail`: convergence of `a₀/(1 + c/(3 + ⋯))`.
* `hasContinuedFraction_tan`, `hasContinuedFraction_tanh`: Lambert's continued fractions.
* `tendsto_one_add_continuedFractionTail_exp`: the continued fraction DLMF 4.9.3 for `exp`.

## Implementation notes

Convergence follows from the ratio form of Pincherle's theorem,
`GenContFract.tendsto_ofFun_convs_of_ratio`, since `1·3···(2k-1) w_k(c) = 1 + O(1/k)`.
-/

@[expose] public section

open Complex Filter Finset GenContFract
open scoped Topology Nat

noncomputable section

namespace DLMF.Elementary

/-- The odd products `1·3···(2k-1)`, with the empty product `1` at `k = 0`. -/
def oddFactorialProd (k : ℕ) : ℕ := ∏ i ∈ range k, (2 * i + 1)

/-- The odd products are positive. -/
theorem oddFactorialProd_pos (k : ℕ) : 0 < oddFactorialProd k :=
  Finset.prod_pos fun i _ => by omega

/-- The recursion `P(k+1) = P(k)(2k+1)`. -/
theorem oddFactorialProd_succ (k : ℕ) :
    oddFactorialProd (k + 1) = oddFactorialProd k * (2 * k + 1) := by
  simp [oddFactorialProd, Finset.prod_range_succ]

/-- `(2m)! = 2^m m! · 1·3···(2m-1)`. -/
theorem factorial_two_mul_eq (m : ℕ) : (2 * m)! = 2 ^ m * m ! * oddFactorialProd m := by
  induction m with
  | zero => simp [oddFactorialProd]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, ih,
      oddFactorialProd_succ, Nat.factorial_succ, pow_succ]
    ring

/-- `(2m+1)! = 2^m m! · 1·3···(2m+1)`. -/
theorem factorial_two_mul_add_one_eq (m : ℕ) :
    (2 * m + 1)! = 2 ^ m * m ! * oddFactorialProd (m + 1) := by
  rw [Nat.factorial_succ, factorial_two_mul_eq, oddFactorialProd_succ]; ring

/-- The odd products increase. -/
theorem oddFactorialProd_mono : Monotone oddFactorialProd :=
  monotone_nat_of_le_succ fun n => by
    rw [oddFactorialProd_succ]; exact Nat.le_mul_of_pos_right _ (by omega)

/-- `(2k+1) P(k) ≤ P(k+m)` for `m ≥ 1`. -/
private lemma oddFactorialProd_le_add (k m : ℕ) (hm : 1 ≤ m) :
    oddFactorialProd k * (2 * k + 1) ≤ oddFactorialProd (k + m) := by
  rw [← oddFactorialProd_succ]; exact oddFactorialProd_mono (by omega)

/-- The terms of `oddFractionTail`. -/
def oddFractionTerm (c : ℂ) (k m : ℕ) : ℂ := (c / 2) ^ m / (m ! * oddFactorialProd (k + m))

/-- The entire backward solution `w_k(c) = ∑ₘ (c/2)^m / (m! · 1·3···(2k+2m-1))` of the
recurrence `w_k = (2k+1) w_{k+1} + c w_{k+2}`; for `c = -z²` it is `z^{1-k} j_{k-1}(z)`. -/
def oddFractionTail (c : ℂ) (k : ℕ) : ℂ := ∑' m, oddFractionTerm c k m

/-- Termwise bound by the exponential series. -/
private lemma norm_oddFractionTerm_le (c : ℂ) (k m : ℕ) :
    ‖oddFractionTerm c k m‖ ≤ ‖c / 2‖ ^ m / m ! := by
  rw [oddFractionTerm, norm_div, norm_pow, norm_mul]
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  simp only [Complex.norm_natCast]
  have : (1 : ℝ) ≤ oddFactorialProd (k + m) := by exact_mod_cast oddFactorialProd_pos _
  nlinarith [Nat.cast_pos (α := ℝ) |>.mpr (Nat.factorial_pos m)]

/-- The series defining `oddFractionTail` converges absolutely. -/
theorem summable_oddFractionTerm (c : ℂ) (k : ℕ) : Summable (oddFractionTerm c k) :=
  Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖c / 2‖)
    (norm_oddFractionTerm_le c k)

/-- The termwise form of the recurrence. -/
private lemma oddFractionTerm_succ (c : ℂ) (k m : ℕ) :
    oddFractionTerm c k (m + 1) =
      (2 * k + 1) * oddFractionTerm c (k + 1) (m + 1) + c * oddFractionTerm c (k + 2) m := by
  simp only [oddFractionTerm]
  have h1 := oddFactorialProd_succ (k + m + 1)
  rw [show k + 1 + (m + 1) = k + m + 1 + 1 by ring, show k + (m + 1) = k + m + 1 by ring,
    show k + 2 + m = k + m + 1 + 1 by ring, h1]
  have hP : (oddFactorialProd (k + m + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (oddFactorialProd_pos _).ne'
  have hf : ((m ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hQ : (2 * ((k + m + 1 : ℕ) : ℂ) + 1) ≠ 0 := by
    norm_cast
  rw [Nat.factorial_succ]
  push_cast at hQ ⊢
  field_simp
  ring

/-- The three-term recurrence of the backward solution. -/
theorem oddFractionTail_recurrence (c : ℂ) (k : ℕ) :
    oddFractionTail c k =
      (2 * k + 1 : ℂ) * oddFractionTail c (k + 1) + c * oddFractionTail c (k + 2) := by
  have e : ∀ j, oddFractionTail c j = oddFractionTerm c j 0 + ∑' m, oddFractionTerm c j (m + 1) :=
    fun j => (summable_oddFractionTerm c j).tsum_eq_zero_add
  rw [e k, e (k + 1)]
  have hs : ∀ j, Summable fun m => oddFractionTerm c j (m + 1) :=
    fun j => (summable_nat_add_iff 1).mpr (summable_oddFractionTerm c j)
  simp_rw [oddFractionTerm_succ c k]
  rw [Summable.tsum_add ((hs _).mul_left _) ((summable_oddFractionTerm c _).mul_left _),
    tsum_mul_left, tsum_mul_left, oddFractionTail]
  have h0 : oddFractionTerm c k 0 = (2 * k + 1) * oddFractionTerm c (k + 1) 0 := by
    simp only [oddFractionTerm, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, add_zero,
      oddFactorialProd_succ]
    have hP : (oddFactorialProd k : ℂ) ≠ 0 := by exact_mod_cast (oddFactorialProd_pos _).ne'
    have hQ : (2 * (k : ℂ) + 1) ≠ 0 := by norm_cast
    push_cast
    field_simp
  rw [h0]; ring

/-- Termwise bound for the normalized tail. -/
private lemma norm_oddFactorialProd_mul_term_succ_le (c : ℂ) (k m : ℕ) :
    ‖(oddFactorialProd k : ℂ) * oddFractionTerm c k (m + 1)‖ ≤
      ‖c / 2‖ * (‖c / 2‖ ^ m / m !) / (2 * k + 1) := by
  rw [oddFractionTerm, norm_mul, norm_div, norm_pow, norm_mul]
  simp only [Complex.norm_natCast]
  have hP := oddFactorialProd_le_add k (m + 1) (by omega)
  have hP' : (oddFactorialProd k : ℝ) * (2 * k + 1) ≤ oddFactorialProd (k + (m + 1)) := by
    exact_mod_cast hP
  have hPk : (0 : ℝ) < oddFactorialProd k := by exact_mod_cast oddFactorialProd_pos k
  have hf : (m ! : ℝ) ≤ (m + 1)! := by exact_mod_cast Nat.factorial_le (by omega)
  have hf0 : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
  have hx : 0 ≤ ‖c / 2‖ ^ (m + 1) := by positivity
  have e : ‖c / 2‖ * (‖c / 2‖ ^ m / m !) / (2 * k + 1) =
      ‖c / 2‖ ^ (m + 1) / (m ! * (2 * k + 1)) := by
    field_simp; ring
  have hQ : (0 : ℝ) < oddFactorialProd (k + (m + 1)) := by exact_mod_cast oddFactorialProd_pos _
  rw [e, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (oddFactorialProd k : ℝ) * (m ! * (2 * k + 1)) ≤
      (m + 1)! * oddFactorialProd (k + (m + 1)) := by
    nlinarith [mul_le_mul hf hP' (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h1 hx]

/-- The normalized backward solution `1·3···(2k-1) w_k(c)` is `1 + O(1/k)`. -/
theorem norm_oddFactorialProd_mul_oddFractionTail_sub_one_le (c : ℂ) (k : ℕ) :
    ‖(oddFactorialProd k : ℂ) * oddFractionTail c k - 1‖ ≤
      ‖c / 2‖ * (∑' m, ‖c / 2‖ ^ m / m !) / (2 * k + 1) := by
  have hs := summable_oddFractionTerm c k
  rw [oddFractionTail, ← tsum_mul_left, (hs.mul_left _).tsum_eq_zero_add]
  have h0 : (oddFactorialProd k : ℂ) * oddFractionTerm c k 0 = 1 := by
    simp only [oddFractionTerm, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, add_zero]
    have hP : (oddFactorialProd k : ℂ) ≠ 0 := by exact_mod_cast (oddFactorialProd_pos _).ne'
    field_simp
  rw [h0, add_sub_cancel_left]
  refine tsum_of_norm_bounded ?_ (norm_oddFactorialProd_mul_term_succ_le c k)
  have := ((Real.summable_pow_div_factorial ‖c / 2‖).hasSum.mul_left ‖c / 2‖).div_const
    (2 * k + 1 : ℝ)
  simpa [mul_div_assoc] using this

/-- Eventually the normalized backward solution `1·3···(2k-1) w_k(c)` lies in the annulus
`1/2 ≤ ‖·‖ ≤ 3/2`, and `9‖c‖ ≤ (2k+1)(2k+3)`. -/
theorem exists_norm_oddFactorialProd_mul_oddFractionTail_bounds (c : ℂ) :
    ∃ N : ℕ, ∀ k ≥ N, 1 / 2 ≤ ‖(oddFactorialProd k : ℂ) * oddFractionTail c k‖ ∧
      ‖(oddFactorialProd k : ℂ) * oddFractionTail c k‖ ≤ 3 / 2 ∧
      9 * ‖c‖ ≤ (2 * k + 1) * (2 * k + 3) := by
  set A := ‖c / 2‖ * (∑' m, ‖c / 2‖ ^ m / m !)
  have hA : 0 ≤ A := mul_nonneg (norm_nonneg _) (tsum_nonneg fun m => by positivity)
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * A + 9 * ‖c‖)
  refine ⟨N, fun k hk => ?_⟩
  have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
  have hb : ‖(oddFactorialProd k : ℂ) * oddFractionTail c k - 1‖ ≤ 1 / 2 := by
    refine (norm_oddFactorialProd_mul_oddFractionTail_sub_one_le c k).trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg c]
  set u := (oddFactorialProd k : ℂ) * oddFractionTail c k
  refine ⟨?_, ?_, by nlinarith [norm_nonneg c]⟩
  · have := norm_sub_norm_le (1 : ℂ) (1 - u)
    rw [sub_sub_cancel, norm_one, norm_sub_rev] at this
    linarith
  · have := norm_le_norm_add_norm_sub' u 1
    rw [norm_one] at this
    linarith

/-- Eventually the backward solution is nonzero and decays fast enough for the ratio test. -/
theorem eventually_oddFractionTail_ratio (c : ℂ) :
    ∃ N : ℕ, ∀ k ≥ N, oddFractionTail c k ≠ 0 ∧
      3 * ‖c * oddFractionTail c (k + 2)‖ ≤ ‖oddFractionTail c k‖ := by
  obtain ⟨N, hN⟩ := exists_norm_oddFactorialProd_mul_oddFractionTail_bounds c
  refine ⟨N, fun k hk => ?_⟩
  set u := fun j => (oddFactorialProd j : ℂ) * oddFractionTail c j
  have hlo : 1 / 2 ≤ ‖u k‖ := (hN k hk).1
  have hhi : ‖u (k + 2)‖ ≤ 3 / 2 := (hN (k + 2) (by omega)).2.1
  have hkc := (hN k hk).2.2
  have hPk : (0 : ℝ) < oddFactorialProd k := by exact_mod_cast oddFactorialProd_pos k
  have hw : ∀ j, oddFractionTail c j = u j / oddFactorialProd j := by
    intro j
    have hP : (oddFactorialProd j : ℂ) ≠ 0 := by exact_mod_cast (oddFactorialProd_pos _).ne'
    simp only [u]; field_simp
  have hP2 : (oddFactorialProd (k + 2) : ℝ) = oddFactorialProd k * ((2 * k + 1) * (2 * k + 3)) := by
    rw [oddFactorialProd_succ, oddFactorialProd_succ]; push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [hw]
    exact div_ne_zero (norm_pos_iff.mp (by linarith [hlo]))
      (by exact_mod_cast (oddFactorialProd_pos _).ne')
  · rw [hw, hw, norm_mul, norm_div, norm_div, Complex.norm_natCast, Complex.norm_natCast, hP2]
    have h1 := hlo
    have h2 := hhi
    have : 3 * (‖c‖ * ‖u (k + 2)‖) ≤ ‖u k‖ * ((2 * k + 1) * (2 * k + 3)) := by
      nlinarith [norm_nonneg c, norm_nonneg (u (k + 2))]
    have e : 3 * (‖c‖ * (‖u (k + 2)‖ / (oddFactorialProd k * ((2 * k + 1) * (2 * k + 3))))) =
        3 * (‖c‖ * ‖u (k + 2)‖) / ((2 * k + 1) * (2 * k + 3)) / oddFactorialProd k := by
      field_simp
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hPk.le
    rw [div_le_iff₀ (by positivity)]; exact this

/-- Without vanishing partial numerators the project's continuants are Mathlib's. -/
private lemma continuedFractionContinuants_eq_cfConv {a b : ℕ → ℂ}
    (ha : ∀ k, 1 ≤ k → a k ≠ 0) (n : ℕ) :
    DLMF.Core.continuedFractionContinuants a b 0 n =
      ((ofFun 0 a b).nums n, (ofFun 0 a b).dens n, false) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [DLMF.Core.continuedFractionContinuants]; rfl
    · simp [DLMF.Core.continuedFractionContinuants, ofFun_nums_one, ofFun_dens_one]
    · have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      have han : a (n + 1) ≠ 0 := ha (n + 1) (by omega)
      rw [DLMF.Core.continuedFractionContinuants, h1, h0, ofFun_nums_add_two, ofFun_dens_add_two]
      simp [han, GenContFract.nextConts, GenContFract.nextNum, GenContFract.nextDen]

/-- `HasContinuedFraction` in terms of Mathlib convergents, without vanishing numerators. -/
private lemma hasContinuedFraction_iff_convs {a b : ℕ → ℂ} (ha : ∀ k, 1 ≤ k → a k ≠ 0) (v : ℂ) :
    DLMF.Core.HasContinuedFraction a b v ↔ Tendsto (ofFun 0 a b).convs atTop (𝓝 v) := by
  unfold DLMF.Core.HasContinuedFraction
  have : DLMF.Core.continuedFractionTail a b 0 = fun N => (ofFun 0 a b).convs N := by
    funext N
    simp only [DLMF.Core.continuedFractionTail, continuedFractionContinuants_eq_cfConv ha]
    rfl
  rw [this]

/-- A continued fraction all of whose partial numerators vanish has value `0`. -/
theorem hasContinuedFraction_of_forall_eq_zero {a b : ℕ → ℂ} (ha : ∀ k, a k = 0) :
    DLMF.Core.HasContinuedFraction a b 0 := by
  have h : ∀ N, (DLMF.Core.continuedFractionContinuants a b 0 N).1 = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      rcases N with _ | _ | N
      · simp [DLMF.Core.continuedFractionContinuants]
      · simp [DLMF.Core.continuedFractionContinuants, ha]
      · rw [DLMF.Core.continuedFractionContinuants]
        simp only [ha, zero_add, or_true, ↓reduceIte]
        exact ih (N + 1) (by omega)
  unfold DLMF.Core.HasContinuedFraction
  have : DLMF.Core.continuedFractionTail a b 0 = fun _ => 0 := by
    funext N; simp [DLMF.Core.continuedFractionTail, h N]
  rw [this]; exact tendsto_const_nhds

/-- The continued fraction `a₀/(1 + c/(3 + c/(5 + ⋯)))` converges to `a₀ w₁(c)/w₀(c)`. -/
theorem hasContinuedFraction_oddFractionTail {a₀ c : ℂ} (ha₀ : a₀ ≠ 0) (hc : c ≠ 0)
    (hw₀ : oddFractionTail c 0 ≠ 0) :
    DLMF.Core.HasContinuedFraction (fun n => if n = 0 then a₀ else c) (fun n => 2 * n + 1)
      (a₀ * oddFractionTail c 1 / oddFractionTail c 0) := by
  rw [hasContinuedFraction_iff_convs (fun k hk => by simp [show k ≠ 0 by omega, hc])]
  obtain ⟨N, hN⟩ := eventually_oddFractionTail_ratio c
  have key := tendsto_ofFun_convs_of_ratio (h := 0) (a := fun n => if n = 0 then a₀ else c)
    (b := fun n => 2 * n + 1) (w := oddFractionTail c)
    (fun k => by simpa using oddFractionTail_recurrence c k) hw₀
    (fun k => by by_cases hk : k = 0 <;> simp [hk, ha₀, hc]) (N := N)
    (fun k hk => (hN k hk).1) (q := 3) (by norm_num)
    (fun k hk => by simpa using (hN k hk).2)
  simpa [mul_div_assoc] using key

/-- `w₀(-y²) = cos y`. -/
theorem oddFractionTail_neg_sq_zero (y : ℂ) : oddFractionTail (-y ^ 2) 0 = Complex.cos y := by
  rw [← (Complex.hasSum_cos y).tsum_eq, oddFractionTail]
  congr 1; funext m
  rw [oddFractionTerm, zero_add, factorial_two_mul_eq]
  push_cast
  rw [div_pow, neg_pow, pow_mul]
  field_simp

/-- `y w₁(-y²) = sin y`. -/
theorem mul_oddFractionTail_neg_sq_one (y : ℂ) :
    y * oddFractionTail (-y ^ 2) 1 = Complex.sin y := by
  rw [← (Complex.hasSum_sin y).tsum_eq, oddFractionTail, ← tsum_mul_left]
  congr 1; funext m
  rw [oddFractionTerm, add_comm 1 m, factorial_two_mul_add_one_eq]
  push_cast
  rw [div_pow, neg_pow, ← pow_mul, pow_succ]
  field_simp

/-- Lambert's continued fraction `tan y = y/(1 - y²/(3 - y²/(5 - ⋯)))`. -/
theorem hasContinuedFraction_tan {y : ℂ} (hy : Complex.cos y ≠ 0) :
    DLMF.Core.HasContinuedFraction (fun n => if n = 0 then y else -y ^ 2) (fun n => 2 * n + 1)
      (Complex.tan y) := by
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [Complex.tan_zero]
    exact hasContinuedFraction_of_forall_eq_zero fun k => by split_ifs <;> simp
  have h := hasContinuedFraction_oddFractionTail hy0 (neg_ne_zero.mpr (pow_ne_zero 2 hy0))
    (by rwa [oddFractionTail_neg_sq_zero])
  rwa [oddFractionTail_neg_sq_zero, mul_oddFractionTail_neg_sq_one, ← Complex.tan_eq_sin_div_cos]
    at h

/-- `w₀(z²) = cosh z`. -/
theorem oddFractionTail_sq_zero (z : ℂ) : oddFractionTail (z ^ 2) 0 = Complex.cosh z := by
  rw [show z ^ 2 = -(z * I) ^ 2 by rw [mul_pow, I_sq]; ring, oddFractionTail_neg_sq_zero,
    Complex.cos_mul_I]

/-- `z w₁(z²) = sinh z`. -/
theorem mul_oddFractionTail_sq_one (z : ℂ) : z * oddFractionTail (z ^ 2) 1 = Complex.sinh z := by
  have := mul_oddFractionTail_neg_sq_one (z * I)
  rw [show -(z * I) ^ 2 = z ^ 2 by rw [mul_pow, I_sq]; ring, Complex.sin_mul_I, mul_assoc] at this
  exact mul_right_cancel₀ I_ne_zero (by rw [← this]; ring)

/-- Lambert's continued fraction `tanh z = z/(1 + z²/(3 + z²/(5 + ⋯)))`. -/
theorem hasContinuedFraction_tanh {z : ℂ} (hz : Complex.cosh z ≠ 0) :
    DLMF.Core.HasContinuedFraction (fun n => if n = 0 then z else z ^ 2) (fun n => 2 * n + 1)
      (Complex.tanh z) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [Complex.tanh_zero]
    exact hasContinuedFraction_of_forall_eq_zero fun k => by split_ifs <;> simp
  have h0 := oddFractionTail_sq_zero z
  have h1 := mul_oddFractionTail_sq_one z
  have h := hasContinuedFraction_oddFractionTail hz0 (pow_ne_zero 2 hz0) (by rwa [h0])
  rwa [h0, h1, ← Complex.tanh_eq_sinh_div_cosh] at h

/-- The continued fraction `1 + z/((1 - z/2) + (z²/12)/(1 + (z²/60)/(1 + ⋯)))` for `exp z`, whose
partial numerators are `z²/(4(4k²-1))`. -/
theorem tendsto_one_add_continuedFractionTail_exp (z : ℂ) :
    Tendsto (fun N => 1 + DLMF.Core.continuedFractionTail
      (fun k => if k = 0 then z else z ^ 2 / (4 * (4 * (k : ℂ) ^ 2 - 1)))
      (fun k => if k = 0 then 1 - z / 2 else 1) 0 N) atTop (𝓝 (Complex.exp z)) := by
  set a : ℕ → ℂ := fun k => if k = 0 then z else z ^ 2 / (4 * (4 * (k : ℂ) ^ 2 - 1))
  set b : ℕ → ℂ := fun k => if k = 0 then 1 - z / 2 else 1
  rcases eq_or_ne z 0 with rfl | hz0
  · have h := hasContinuedFraction_of_forall_eq_zero (a := a) (b := b)
      (fun k => by simp only [a]; split_ifs <;> simp)
    simpa using h.const_add 1
  have hq : ∀ k : ℕ, (4 * ((k + 1 : ℕ) : ℂ) ^ 2 - 1) = (2 * k + 1) * (2 * k + 3) := by
    intro k; push_cast; ring
  have hq0 : ∀ k : ℕ, (4 * ((k + 1 : ℕ) : ℂ) ^ 2 - 1) ≠ 0 := by
    intro k; rw [hq]; exact mul_ne_zero (by norm_cast) (by norm_cast)
  have ha : ∀ k, a k ≠ 0 := by
    intro k
    rcases k with _ | k
    · simpa [a] using hz0
    · simp only [a, Nat.succ_ne_zero, ↓reduceIte]
      exact div_ne_zero (pow_ne_zero 2 hz0) (mul_ne_zero (by norm_num) (hq0 k))
  set c : ℂ := (z / 2) ^ 2
  set v := oddFractionTail c
  set w : ℕ → ℂ := fun k => if k = 0 then v 0 - z / 2 * v 1 else oddFactorialProd k * v k
  have hP2 : ∀ k, (oddFactorialProd (k + 2) : ℂ) =
      oddFactorialProd k * ((2 * k + 1) * (2 * k + 3)) := by
    intro k; rw [oddFactorialProd_succ, oddFactorialProd_succ]; push_cast; ring
  have hak : ∀ k, a (k + 1) = c / ((2 * k + 1) * (2 * k + 3)) := by
    intro k
    simp only [a, Nat.succ_ne_zero, ↓reduceIte, c]
    have h1 : (2 * (k : ℂ) + 1) ≠ 0 := by norm_cast
    have h2 : (2 * (k : ℂ) + 3) ≠ 0 := by norm_cast
    rw [hq]; field_simp; ring
  have hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2) := by
    intro k
    have hne : ((2 * k + 1) * (2 * k + 3) : ℂ) ≠ 0 := mul_ne_zero (by norm_cast) (by norm_cast)
    have hr : v k = (2 * k + 1) * v (k + 1) + c * v (k + 2) := oddFractionTail_recurrence c k
    rcases k with _ | k
    · simp only [w, b, hak, ↓reduceIte, Nat.succ_ne_zero, hP2]
      simp only [oddFactorialProd, Finset.range_zero, Finset.prod_empty, zero_add,
        Finset.prod_range_one] at hr ⊢
      rw [hr]; norm_num; ring
    · simp only [w, b, hak, Nat.succ_ne_zero, ↓reduceIte, hP2, one_mul]
      rw [oddFactorialProd_succ, hr]
      have h1 : (2 * ((k : ℂ) + 1) + 1) ≠ 0 := by norm_cast
      have h2 : (2 * ((k : ℂ) + 1) + 3) ≠ 0 := by norm_cast
      push_cast
      field_simp
      ring
  have hv0 : v 0 = Complex.cosh (z / 2) := oddFractionTail_sq_zero _
  have hv1 : z / 2 * v 1 = Complex.sinh (z / 2) := mul_oddFractionTail_sq_one _
  have hw0 : w 0 = Complex.exp (-(z / 2)) := by
    simp only [w, ↓reduceIte, hv0, hv1, Complex.cosh_sub_sinh]
  obtain ⟨N, hN⟩ := exists_norm_oddFactorialProd_mul_oddFractionTail_bounds c
  have hwN : ∀ k ≥ N + 1, w k ≠ 0 := by
    intro k hk
    simp only [w, show k ≠ 0 by omega, ↓reduceIte]
    exact norm_pos_iff.mp (by linarith [(hN k (by omega)).1])
  have key := tendsto_ofFun_convs_of_ratio (h := 0) (a := a) (b := b) (w := w) hw
    (by rw [hw0]; exact Complex.exp_ne_zero _) ha (N := N + 1) hwN (q := 3) (by norm_num)
    (fun k hk => by
      simp only [w, show k ≠ 0 by omega, show k + 2 ≠ 0 by omega, ↓reduceIte, hak]
      obtain ⟨h1, -, h3⟩ := hN k (by omega)
      have h1' : 1 / 2 ≤ ‖(oddFactorialProd k : ℂ) * v k‖ := h1
      have h2 : ‖(oddFactorialProd (k + 2) : ℂ) * v (k + 2)‖ ≤ 3 / 2 :=
        (hN (k + 2) (by omega)).2.1
      rw [norm_mul, norm_div]
      have hn : ‖((2 * k + 1) * (2 * k + 3) : ℂ)‖ = (2 * k + 1) * (2 * k + 3) := by
        norm_cast
      rw [hn]
      have hpos : (0 : ℝ) < (2 * k + 1) * (2 * k + 3) := by positivity
      rw [show 3 * (‖c‖ / ((2 * k + 1) * (2 * k + 3)) *
          ‖(oddFactorialProd (k + 2) : ℂ) * v (k + 2)‖) = 3 * ‖c‖ *
          ‖(oddFactorialProd (k + 2) : ℂ) * v (k + 2)‖ / ((2 * k + 1) * (2 * k + 3)) by ring,
        div_le_iff₀ hpos]
      have hc : ‖c‖ = ‖z / 2‖ ^ 2 := norm_pow _ _
      nlinarith [norm_nonneg c, norm_nonneg ((oddFactorialProd (k + 2) : ℂ) * v (k + 2))])
  have hlim : 0 + a 0 * w 1 / w 0 = Complex.exp z - 1 := by
    have hP1 : (oddFactorialProd 1 : ℂ) = 1 := by simp [oddFactorialProd]
    simp only [a, w, ↓reduceIte, one_ne_zero, hP1, one_mul, zero_add]
    have hw0' : v 0 - z / 2 * v 1 = Complex.exp (-(z / 2)) := hw0
    rw [hw0']
    have : z * v 1 = 2 * Complex.sinh (z / 2) := by rw [← hv1]; ring
    rw [this, Complex.sinh]
    have he : Complex.exp z = Complex.exp (z / 2) * Complex.exp (z / 2) := by
      rw [← Complex.exp_add]; ring_nf
    have hm : Complex.exp (-(z / 2)) * Complex.exp (z / 2) = 1 := by
      rw [← Complex.exp_add]; simp
    have hne := Complex.exp_ne_zero (-(z / 2))
    rw [he]
    field_simp
    linear_combination (-Complex.exp (z / 2)) * hm
  rw [hlim] at key
  have h := key.const_add 1
  rw [add_sub_cancel] at h
  refine h.congr fun n => ?_
  congr 1
  simp only [DLMF.Core.continuedFractionTail,
      continuedFractionContinuants_eq_cfConv (fun k _ => ha k)]
  rfl

end DLMF.Elementary
