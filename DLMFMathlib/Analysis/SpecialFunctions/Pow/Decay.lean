/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Bounds and summability for principal powers

A lower bound for the norm of a complex base bounds its principal powers with nonpositive
real exponent. Bounded orders and affine norm bounds give polynomial growth. Real translated
powers admit a product majorant suited to summation, and polynomial times geometric sequences
are summable inside the unit disk.
-/

@[expose] public section

open scoped Real

namespace Complex

/-- A positive norm lower bound controls a principal power with nonpositive real exponent. -/
lemma norm_cpow_le_of_norm_lower_bound {z s : ℂ} {r : ℝ} (hr : 0 < r) (hz : r ≤ ‖z‖)
    (hs : s.re ≤ 0) : ‖z ^ s‖ ≤ r ^ s.re * Real.exp (π * |s.im|) := by
  refine (norm_cpow_le _ _).trans ?_
  rw [div_eq_mul_inv, ← Real.exp_neg]
  have h1 : ‖z‖ ^ s.re ≤ r ^ s.re := Real.rpow_le_rpow_of_nonpos hr hz hs
  have h2 : Real.exp (-(arg z * s.im)) ≤ Real.exp (π * |s.im|) := by
    rw [Real.exp_le_exp]
    calc -(arg z * s.im) ≤ |arg z| * |s.im| := by rw [← abs_mul]; exact neg_le_abs _
      _ ≤ π * |s.im| := mul_le_mul_of_nonneg_right (abs_arg_le_pi z) (abs_nonneg _)
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (Real.rpow_nonneg hr.le _)

/-- The real power of a norm is bounded by the norm of the principal power and a phase factor. -/
lemma rpow_norm_le_norm_cpow_mul_exp {z : ℂ} (hz : z ≠ 0) (s : ℂ) :
    ‖z‖ ^ s.re ≤ ‖z ^ s‖ * Real.exp (π * |s.im|) := by
  rw [norm_cpow_of_ne_zero hz, div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
  apply le_mul_of_one_le_right (Real.rpow_nonneg (norm_nonneg z) _)
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (abs_arg_le_pi z) (abs_nonneg s.im)
  nlinarith [le_abs_self (arg z * s.im), abs_mul (arg z) s.im]

/-- `‖w ^ s‖ ≤ ‖w‖ ^ Re s · e^{π |Im s|}` for `w ≠ 0` (principal branch). -/
theorem norm_cpow_le_rpow_mul_exp {w : ℂ} (hw : w ≠ 0) (s : ℂ) :
    ‖w ^ s‖ ≤ ‖w‖ ^ s.re * Real.exp (π * |s.im|) := by
  rw [norm_cpow_of_ne_zero hw, div_eq_mul_inv, ← Real.exp_neg]
  gcongr
  calc -(arg w * s.im) ≤ |arg w * s.im| := neg_le_abs _
    _ = |arg w| * |s.im| := abs_mul _ _
    _ ≤ π * |s.im| := by gcongr; exact abs_arg_le_pi w

/-- Principal powers of bounded order admit a polynomial bound when the base stays
away from zero and its norm is bounded by an affine function of a nonnegative variable. -/
lemma exists_bound_cpow_of_norm_bounds {r R M : ℝ} (hr0 : 0 < r) (hR : 0 ≤ R)
    (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ s : ℂ, ‖s‖ ≤ M → ∀ z : ℂ, ∀ x : ℝ,
      0 ≤ x → r ≤ ‖z‖ → ‖z‖ ≤ R + x → ‖z ^ s‖ ≤ C * (1 + x) ^ N := by
  obtain ⟨N, hN⟩ := exists_nat_ge M
  let A : ℝ := (R + 1) ^ M
  let B : ℝ := r ^ (-M)
  have hA : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  have hB : 0 < B := Real.rpow_pos_of_pos hr0 _
  refine ⟨Real.exp (Real.pi * M) * (A + B), by positivity, N, ?_⟩
  intro s hs z x hx hrlo hrhi
  have hzn : 0 < ‖z‖ := hr0.trans_le hrlo
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzn
  have hsr : -M ≤ s.re ∧ s.re ≤ M := by
    have := abs_le.mp ((abs_re_le_norm s).trans hs)
    exact this
  have hsi : |s.im| ≤ M := (abs_im_le_norm s).trans hs
  have hpone : 1 ≤ (1 + x) ^ N := one_le_pow₀ (by linarith [hx])
  have hpow : ‖z‖ ^ s.re ≤ (A + B) * (1 + x) ^ N := by
    rcases le_or_gt ‖z‖ 1 with hr1 | hr1
    · have h₁ := Real.rpow_le_rpow_of_exponent_ge hzn hr1 hsr.1
      have h₂ : ‖z‖ ^ (-M) ≤ B :=
        Real.rpow_le_rpow_of_nonpos hr0 hrlo (by linarith)
      have h₃ : B ≤ (A + B) * (1 + x) ^ N := by
        nlinarith
      exact h₁.trans (h₂.trans h₃)
    · have h₁ := Real.rpow_le_rpow_of_exponent_le hr1.le hsr.2
      have hb : ‖z‖ ≤ (R + 1) * (1 + x) := by
        nlinarith [hR, hx]
      have h₂ : ‖z‖ ^ M ≤ A * (1 + x) ^ N := by
        calc
          ‖z‖ ^ M ≤ ((R + 1) * (1 + x)) ^ M :=
            Real.rpow_le_rpow hzn.le hb hM
          _ = A * (1 + x) ^ M := by rw [Real.mul_rpow (by positivity) (by positivity)]
          _ ≤ A * (1 + x) ^ (N : ℝ) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le (by linarith [hx]) hN) hA.le
          _ = A * (1 + x) ^ N := by rw [Real.rpow_natCast]
      have h₃ : A * (1 + x) ^ N ≤ (A + B) * (1 + x) ^ N := by
        nlinarith [pow_nonneg (by linarith [hx] : 0 ≤ 1 + x) N]
      exact h₁.trans (h₂.trans h₃)
  calc
    ‖z ^ s‖ ≤ ‖z‖ ^ s.re * Real.exp (Real.pi * |s.im|) :=
      norm_cpow_le_rpow_mul_exp hz0 s
    _ ≤ ((A + B) * (1 + x) ^ N) * Real.exp (Real.pi * M) := by gcongr
    _ = _ := by ring

end Complex

namespace Real

/-- A fixed natural power of `n+1` times a geometric sequence is summable inside the unit disk. -/
lemma summable_natCast_add_one_pow_mul_geometric (N : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ N * r ^ n) := by
  rcases eq_or_ne r 0 with rfl | hrne
  · convert (hasSum_ite_eq 0 (1 : ℝ)).summable using 1
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn, zero_pow hn]
  · have h := (summable_nat_add_iff 1).mpr
      (summable_pow_mul_geometric_of_norm_lt_one N (r := r) (by
        simpa only [norm_eq_abs, abs_of_nonneg hr0] using hr))
    convert h.mul_left r⁻¹ using 1
    funext n
    push_cast
    rw [pow_succ]
    field_simp



/-- A decaying translated power separates into two powers of half its degree. -/
lemma add_rpow_le_mul_rpow_half {r t p : ℝ} (hr : 1 ≤ r) (ht : 0 ≤ t) (hp : 0 ≤ p) :
    (r + t) ^ (-p) ≤ r ^ (-p / 2) * (t + 1) ^ (-p / 2) := by
  have hr0 : 0 < r := by linarith
  have hrt : 0 < r + t := by positivity
  have hsq : r * (t + 1) ≤ (r + t) ^ 2 := by
    have h1 : r ≤ r + t := by linarith
    have h2 : t + 1 ≤ r + t := by linarith
    nlinarith [mul_le_mul h1 h2 (by positivity : 0 ≤ t + 1) hrt.le]
  rw [← Real.mul_rpow hr0.le (by positivity)]
  calc (r + t) ^ (-p) = ((r + t) ^ 2) ^ (-p / 2) := by
        rw [← Real.rpow_natCast_mul hrt.le]
        congr 1
        norm_num
        ring
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity) hsq (by linarith)

end Real

namespace Asymptotics

/-- Integer powers are ordered by their exponents at infinity in a normed division ring. -/
lemma isBigO_zpow_zpow_cobounded_of_le {𝕜 : Type*} [NormedDivisionRing 𝕜]
    {m n : ℤ} (hmn : m ≤ n) :
    (fun z : 𝕜 => z ^ m) =O[Bornology.cobounded 𝕜] (fun z => z ^ n) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_cobounded_le_norm (E := 𝕜) 1] with z hz
  simpa only [norm_zpow, one_mul, Real.rpow_intCast] using
    (Real.rpow_le_rpow_of_exponent_le hz (Int.cast_le.mpr hmn))

end Asymptotics
