/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Sums.Defs
public import DLMF.Gamma.BarnesG

/-!
# The Euler–Maclaurin formula and summation by parts (DLMF §2.10(i)–(ii))

* `euler_maclaurin`: DLMF 2.10.1, proved from DLMFMathlib's `sum_range_succ_eq_integral_add`
  (Euler–Maclaurin with periodic Bernoulli remainder) by a shift to the integer `a` and the
  vanishing of the odd Bernoulli numbers.
* `abel_plana`: the Abel–Plana formula 2.10.2.
* The example `∑ j ln j` (2.10.3–2.10.6): the constant `C` is `ln A` with the project's
  Glaisher–Kinkelin constant `DLMF.Gamma.glaisherKinkelin` (5.17.6); the two closed forms of
  2.10.6 are proved from `DLMF.Gamma.glaisherKinkelin_eq_zeta_neg_one` (5.17.7), and the
  leading behaviour `S(n) - (½n² ln n - ¼n² + ½n ln n + 1/12 ln n) → C` from
  `DLMF.Gamma.BarnesAsymp.tendsto_hseq`.
* The power sums 2.10.7 and the harmonic numbers 2.10.8, with the remainder bounds of
  §2.10(i).
* Summation by parts 2.10.9–2.10.10 and the oscillatory example 2.10.11–2.10.18.

Bernoulli numbers are Mathlib's `bernoulli` (`B₁ = -1/2`, as in DLMF §24.2); `B̃_n` is
DLMFMathlib's `periodicBernoulli`; `ζ` is Mathlib's `riemannZeta` and `γ` is
`Real.eulerMascheroniConstant`.
-/

@[expose] public noncomputable section

open Finset MeasureTheory Set intervalIntegral Filter Asymptotics
open scoped Nat Topology Real

namespace DLMF.AsymptoticApproximations

/-! ### §2.10(i) Euler–Maclaurin formula -/

/-- The odd-index Bernoulli terms of DLMFMathlib's Euler–Maclaurin sum vanish:
`∑_{j=1}^{2m-1} (-1)^j B_{j+1}/(j+1)! c_j = -∑_{s=1}^{m} B_{2s}/(2s)! c_{2s-1}`. -/
lemma g2b_bernoulli_sum_split (c : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Ico 1 (2 * m), ((-1 : ℝ) ^ j * (bernoulli (j + 1) : ℝ) / (j + 1)!) * c j =
      -∑ s ∈ Ico 1 (m + 1), ((bernoulli (2 * s) : ℝ) / (2 * s)!) * c (2 * s - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
      norm_num
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_Ico_succ_top (by omega),
      Finset.sum_Ico_succ_top (by omega), ih, Finset.sum_Ico_succ_top (by omega : 1 ≤ m + 1)]
    have hodd : bernoulli (2 * m + 1) = 0 :=
      bernoulli_eq_zero_of_odd ⟨m, rfl⟩ (by omega)
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, show 2 * (m + 1) - 1 = 2 * m + 1 by omega, hodd]
    have : (-1 : ℝ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [this]
    push_cast
    ring

/-- DLMF 2.10.1 (Euler–Maclaurin formula): for an integer `a`, `N ≥ 0`, `m ≥ 1` and `f` of class
`C^{2m}` on `ℝ`, with `n = a + N`,
`∑_{j=a}^{n} f(j) = ∫_a^n f + ½f(a) + ½f(n) + ∑_{s=1}^{m-1} B_{2s}/(2s)! (f^{(2s-1)}(n) -
f^{(2s-1)}(a)) + ∫_a^n (B_{2m} - B̃_{2m}(x))/(2m)! f^{(2m)}(x) dx`.
DLMF assumes only that `f^{(2m)}` is absolutely integrable on `[a, n]`; here `f` is `C^{2m}`
(on `ℝ`, which is no loss for the values on `[a, n]` when `f` extends). -/
@[dlmf 2.10.E1]
theorem euler_maclaurin {f : ℝ → ℝ} {m : ℕ} (hm : 1 ≤ m) (hf : ContDiff ℝ (2 * m : ℕ) f) (a : ℤ)
    (N : ℕ) :
    ∑ k ∈ range (N + 1), f (a + k) =
      (∫ x in (a : ℝ)..a + N, f x) + f a / 2 + f (a + N) / 2 +
        ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s)! *
          (iteratedDeriv (2 * s - 1) f (a + N) - iteratedDeriv (2 * s - 1) f a) +
        ∫ x in (a : ℝ)..a + N, ((bernoulli (2 * m) : ℝ) - periodicBernoulli (2 * m) x) /
          (2 * m)! * iteratedDeriv (2 * m) f x := by
  have hg : ContDiff ℝ (2 * m : ℕ) (fun x => f (x + a)) :=
    hf.comp (contDiff_id.add contDiff_const)
  have h := sum_range_succ_eq_integral_add (p := 2 * m) (by omega) hg N
  simp only [iteratedDeriv_comp_add_const, smul_eq_mul, zero_add] at h
  rw [intervalIntegral.integral_comp_add_right (fun x => f x)] at h
  have hper : (∫ x in (0 : ℝ)..N, periodicBernoulli (2 * m) x * iteratedDeriv (2 * m) f (x + a)) =
      ∫ x in (a : ℝ)..a + N, periodicBernoulli (2 * m) x * iteratedDeriv (2 * m) f x := by
    have := intervalIntegral.integral_comp_add_right
      (fun x => periodicBernoulli (2 * m) x * iteratedDeriv (2 * m) f x) (a : ℝ) (a := 0) (b := N)
    simp only [periodicBernoulli_add_intCast, zero_add] at this
    rw [this, add_comm]
  rw [hper, g2b_bernoulli_sum_split (fun j => iteratedDeriv j f (N + a) - iteratedDeriv j f a),
    Finset.sum_Ico_succ_top (by omega : 1 ≤ m)] at h
  have hR : Continuous (iteratedDeriv (2 * m) f) := hf.continuous_iteratedDeriv _ le_rfl
  have hRint : IntervalIntegrable (fun x => periodicBernoulli (2 * m) x *
      iteratedDeriv (2 * m) f x) volume (a : ℝ) (a + N) := by
    obtain ⟨M, hM⟩ : ∃ M, ∀ y ∈ Icc (0 : ℝ) 1, ‖bernoulliFun (2 * m) y‖ ≤ M :=
      IsCompact.exists_bound_of_continuousOn isCompact_Icc
        (continuous_bernoulliFun (2 * m)).continuousOn
    have hb : ∀ s : Set ℝ, IntegrableOn (iteratedDeriv (2 * m) f) s →
        IntegrableOn (fun x => periodicBernoulli (2 * m) x • iteratedDeriv (2 * m) f x) s :=
      fun s hs => hs.bdd_smul M (measurable_periodicBernoulli (2 * m)).aestronglyMeasurable
        (ae_of_all _ fun y => hM _ ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩)
    exact ⟨hb _ (hR.intervalIntegrable _ _).1, hb _ (hR.intervalIntegrable _ _).2⟩
  -- the fundamental theorem of calculus for the derivative of order `2m - 1`
  have hftc : (∫ x in (a : ℝ)..a + N, iteratedDeriv (2 * m) f x) =
      iteratedDeriv (2 * m - 1) f (a + N) - iteratedDeriv (2 * m - 1) f a := by
    have e : 2 * m = 2 * m - 1 + 1 := by omega
    rw [e, iteratedDeriv_succ]
    refine intervalIntegral.integral_deriv_eq_sub (fun x _ => ?_) ?_
    · exact ((hf.differentiable_iteratedDeriv (2 * m - 1)
        (by exact_mod_cast (by omega : 2 * m - 1 < 2 * m))) x)
    · rw [← iteratedDeriv_succ, ← e]; exact hR.intervalIntegrable _ _
  have hsplit : (∫ x in (a : ℝ)..a + N, ((bernoulli (2 * m) : ℝ) - periodicBernoulli (2 * m) x) /
        (2 * m)! * iteratedDeriv (2 * m) f x) =
      (bernoulli (2 * m) : ℝ) / (2 * m)! * (∫ x in (a : ℝ)..a + N, iteratedDeriv (2 * m) f x) -
        1 / (2 * m)! * ∫ x in (a : ℝ)..a + N,
          periodicBernoulli (2 * m) x * iteratedDeriv (2 * m) f x := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((hR.intervalIntegrable _ _).const_mul _)
        (hRint.const_mul _)]
    congr 1; funext x; ring
  have hpow : (-1 : ℝ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
  rw [hsplit, hftc]
  have e1 : ∀ k : ℕ, f (a + k) = f (k + a) := fun k => by rw [add_comm]
  simp only [e1]
  rw [h, hpow, zero_add, add_comm (N : ℝ) (a : ℝ)]
  ring

/-- DLMF 2.10.2 (Abel–Plana formula): let `a < n` be integers and `m ≥ 1`, and let `f` satisfy
(a) `f` is analytic in the open strip `a < ℜz < n`, `f^{(2m)}` is continuous on the closed strip,
and `f(z) = o(e^{2π|ℑz|})` as `ℑz → ±∞` uniformly in `ℜz ∈ [a, n]`;
(b) `f` is real on `[a, n]`; (c) `∫_0^∞ ℑf(a+iy)/(e^{2πy}-1) dy` converges.
Then for some `ϑ ∈ (0, 1)`,
`∑_{j=a}^{n} f(j) = ∫_a^n f + ½f(a) + ½f(n) - 2∫_0^∞ ℑf(a+iy)/(e^{2πy}-1) dy
  + ∑_{s=1}^{m} B_{2s}/(2s)! f^{(2s-1)}(n)
  + 2(-1)^m/(2m)! ∫_0^∞ ℑf^{(2m)}(n+iϑy) y^{2m}/(e^{2πy}-1) dy`. -/
@[dlmf 2.10.E2]
theorem abel_plana {f : ℂ → ℂ} {a n : ℤ} (han : a < n) {m : ℕ} (hm : 1 ≤ m)
    (hana : DifferentiableOn ℂ f {z : ℂ | (a : ℝ) < z.re ∧ z.re < n})
    (hcont : ∀ k ≤ 2 * m, ContinuousOn (iteratedDeriv k f) {z : ℂ | (a : ℝ) ≤ z.re ∧ z.re ≤ n})
    (hgrowth : ∀ ε > 0, ∃ Y : ℝ, ∀ z : ℂ, (a : ℝ) ≤ z.re → z.re ≤ n → Y ≤ |z.im| →
      ‖f z‖ ≤ ε * Real.exp (2 * π * |z.im|))
    (hreal : ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ n → (f x).im = 0)
    (hconv : IntegrableOn (fun y : ℝ => (f (a + Complex.I * y)).im / (Real.exp (2 * π * y) - 1))
      (Ioi 0)) :
    ∃ ϑ ∈ Ioo (0 : ℝ) 1,
      ∑ j ∈ Icc a n, (f j).re =
        (∫ x in (a : ℝ)..n, (f x).re) + (f a).re / 2 + (f n).re / 2 -
          2 * (∫ y in Ioi (0 : ℝ), (f (a + Complex.I * y)).im / (Real.exp (2 * π * y) - 1)) +
          ∑ s ∈ Icc 1 m, (bernoulli (2 * s) : ℝ) / (2 * s)! * (iteratedDeriv (2 * s - 1) f n).re +
          2 * (-1) ^ m / (2 * m)! * ∫ y in Ioi (0 : ℝ),
            (iteratedDeriv (2 * m) f (n + Complex.I * (ϑ * y))).im * y ^ (2 * m) /
              (Real.exp (2 * π * y) - 1) := by
  sorry

/-! ### Example: `∑ j ln j` (2.10.3–2.10.6) -/

/-- DLMF 2.10.4 (with 2.10.3, 2.10.5 and 2.10.6): for `m ≥ 2` and `n ≥ 1`,
`S(n) = ½n² ln n - ¼n² + ½n ln n + 1/12 ln n + C
  + ∑_{s=2}^{m-1} (-B_{2s})/(2s(2s-1)(2s-2)) n^{-(2s-2)} + R_m(n)`
with `C = ln A`, `A` the Glaisher–Kinkelin constant. -/
@[dlmf 2.10.E4, dlmf 2.10.E5]
theorem jLogJSum_eq {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n) :
    jLogJSum n = (n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 + n / 2 * Real.log n +
      Real.log n / 12 + Real.log DLMF.Gamma.glaisherKinkelin +
      ∑ s ∈ Ico 2 m, g2b_jLogJTerm s n + jLogJRemainder m n := by
  sorry

/-- DLMF §2.10(i) (remainder of 2.10.4): since `B̃_{2m}(x) - B_{2m}` has constant sign
`(-1)^m`, `R_m(n)` has the sign of the `s = m` term of 2.10.4 and is bounded in absolute value
by it (`m ≥ 2`, `n ≥ 1`). -/
@[dlmf 2.10.i]
theorem jLogJRemainder_bound {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n) :
    0 ≤ jLogJRemainder m n * g2b_jLogJTerm m n ∧ |jLogJRemainder m n| ≤ |g2b_jLogJTerm m n| := by
  sorry

/-- DLMF 2.10.4 to leading order (the case `m = 2`, with `R_2(n) → 0`):
`S(n) - (½n² ln n - ¼n² + ½n ln n + 1/12 ln n) → C = ln A` as `n → ∞`. Proved from the
project's limit for the Glaisher–Kinkelin constant. -/
@[dlmf 2.10.E4]
theorem tendsto_jLogJSum_sub :
    Tendsto (fun n : ℕ => jLogJSum n - ((n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 +
      n / 2 * Real.log n + Real.log n / 12)) atTop (𝓝 (Real.log DLMF.Gamma.glaisherKinkelin)) := by
  refine DLMF.Gamma.BarnesAsymp.tendsto_hseq.congr fun N => ?_
  have hS : jLogJSum N = ∑ k ∈ range (N + 1), (k : ℝ) * Real.log k := by
    rw [jLogJSum, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp only [Nat.cast_zero, zero_mul, zero_add]
    rfl
  rw [DLMF.Gamma.BarnesAsymp.hseq, hS]
  ring

/-- DLMF 2.10.6: the constant of 2.10.4 is
`C = (γ + ln(2π))/12 - ζ'(2)/(2π²) = 1/12 - ζ'(-1)`; `e^C` is Glaisher's constant. -/
@[dlmf 2.10.E6]
theorem log_glaisherKinkelin_eq :
    Real.log DLMF.Gamma.glaisherKinkelin =
        (Real.eulerMascheroniConstant + Real.log (2 * π)) / 12 -
          (deriv riemannZeta 2).re / (2 * π ^ 2) ∧
      Real.log DLMF.Gamma.glaisherKinkelin = 1 / 12 - (deriv riemannZeta (-1)).re :=
  ⟨by rw [DLMF.Gamma.glaisherKinkelin, Real.log_exp],
    DLMF.Gamma.glaisherKinkelin_eq_zeta_neg_one⟩

/-! ### Power sums and harmonic numbers (2.10.7–2.10.8) -/

/-- DLMF 2.10.7: for real `α ≠ -1`, as `n → ∞`,
`∑_{j=1}^{n-1} j^α ∼ ζ(-α) + n^{α+1}/(α+1) ∑_{s ≥ 0} (α+1 choose s) B_s n^{-s}`. -/
@[dlmf 2.10.E7]
theorem powerSum_asymptotic {α : ℝ} (hα : α ≠ -1) :
    HasAsymptoticExpansion atTop (g2b_powScale α) (g2b_powSumCoeff α)
      (fun n : ℕ => ∑ j ∈ Ico 1 n, (j : ℝ) ^ α - (riemannZeta (-α)).re) := by
  sorry

/-- DLMF §2.10(i) (remainder of 2.10.7): truncating 2.10.7 after `s = 2m - 1`, where
`m ≥ (α+1)/2`, leaves a remainder bounded in absolute value by the first neglected term
(`s = 2m`) and of the same sign, for every `n ≥ 1`. -/
@[dlmf 2.10.i]
theorem powerSum_remainder_bound {α : ℝ} (hα : α ≠ -1) {m : ℕ} (hm : 1 ≤ m)
    (hmα : (α + 1) / 2 ≤ m) {n : ℕ} (hn : 1 ≤ n) :
    let R := ∑ j ∈ Ico 1 n, (j : ℝ) ^ α - (riemannZeta (-α)).re -
      ∑ s ∈ range (2 * m), g2b_powScale α s n * g2b_powSumCoeff α s
    0 ≤ R * (g2b_powScale α (2 * m) n * g2b_powSumCoeff α (2 * m)) ∧
      |R| ≤ |g2b_powScale α (2 * m) n * g2b_powSumCoeff α (2 * m)| := by
  sorry

/-- DLMF 2.10.8: as `n → ∞`,
`∑_{j=1}^{n-1} 1/j ∼ ln n + γ - 1/(2n) - ∑_{s ≥ 1} B_{2s}/(2s) n^{-2s}`. -/
@[dlmf 2.10.E8]
theorem harmonic_asymptotic :
    HasAsymptoticExpansion atTop g2b_invScale g2b_harmonicCoeff
      (fun n : ℕ => (harmonic (n - 1) : ℝ) - Real.log n - Real.eulerMascheroniConstant) := by
  sorry

/-- DLMF §2.10(i) (remainder of 2.10.8): after the terms `s < m` of `∑ B_{2s}/(2s) n^{-2s}`
(`m ≥ 1`), the remainder is bounded in absolute value by the first neglected term
`-B_{2m}/(2m) n^{-2m}` and has the same sign, for every `n ≥ 1`. -/
@[dlmf 2.10.i]
theorem harmonic_remainder_bound {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    let R := (harmonic (n - 1) : ℝ) - (Real.log n + Real.eulerMascheroniConstant - 1 / (2 * n) -
      ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) / (n : ℝ) ^ (2 * s))
    let T := -(bernoulli (2 * m) : ℝ) / (2 * m) / (n : ℝ) ^ (2 * m)
    0 ≤ R * T ∧ |R| ≤ |T| := by
  sorry

/-! ### §2.10(ii) Summation by parts -/

/-- DLMF 2.10.9–2.10.10 (summation by parts): with `U_j = u_1 + ⋯ + u_j`,
`∑_{j=1}^{n-1} u_j v_j = U_{n-1} v_n + ∑_{j=1}^{n-1} U_j (v_j - v_{j+1})` for `n ≥ 1`. -/
@[dlmf 2.10.E9, dlmf 2.10.E10]
theorem sum_by_parts (u v : ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Ico 1 n, u j * v j = partialSumFrom u (n - 1) * v n +
      ∑ j ∈ Ico 1 n, partialSumFrom u j * (v j - v (j + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  clear hn
  induction k with
  | zero => simp [partialSumFrom]
  | succ k ih =>
    simp only [Finset.sum_Ico_succ_top (show 1 ≤ k + 1 by omega)]
    rw [ih]
    have hU : partialSumFrom u (k + 1) = partialSumFrom u k + u (k + 1) := by
      simp only [partialSumFrom]
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top (by omega),
        Finset.Ico_add_one_right_eq_Icc]
    rw [hU]
    ring

/-- DLMF 2.10.12: `|S(α, β, n)| ≤ ∑_{j=1}^{n-1} j^α`. -/
@[dlmf 2.10.E12]
theorem norm_oscillatorySum_le (α β : ℝ) (n : ℕ) :
    ‖oscillatorySum α β n‖ ≤ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α := by
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  rw [show Complex.I * j * β = ((j * β : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]

/-- DLMF 2.10.12 (orders): `∑_{j=1}^{n-1} j^α = O(1)`, `O(ln n)` or `O(n^{α+1})` according as
`α < -1`, `α = -1` or `α > -1`; hence the same bounds for `S(α, β, n)`. -/
@[dlmf 2.10.E12]
theorem oscillatorySum_isBigO_trivial (β : ℝ) :
    (∀ α < -1, (fun n => oscillatorySum α β n) =O[atTop] fun _ => (1 : ℝ)) ∧
      ((fun n => oscillatorySum (-1) β n) =O[atTop] fun n => Real.log n) ∧
      ∀ α > -1, (fun n => oscillatorySum α β n) =O[atTop] fun n => (n : ℝ) ^ (α + 1) := by
  sorry

/-- DLMF 2.10.13: with `u_j = e^{ijβ}` and `e^{iβ} ≠ 1`,
`U_j = e^{iβ}(e^{ijβ} - 1)/(e^{iβ} - 1)`. -/
@[dlmf 2.10.E13]
theorem partialSumFrom_exp {β : ℝ} (hβ : Complex.exp (Complex.I * β) ≠ 1) (j : ℕ) :
    partialSumFrom (fun i => Complex.exp (Complex.I * i * β)) j =
      Complex.exp (Complex.I * β) * (Complex.exp (Complex.I * j * β) - 1) /
        (Complex.exp (Complex.I * β) - 1) := by
  have hz : Complex.exp (Complex.I * β) - 1 ≠ 0 := sub_ne_zero.2 hβ
  have hpow : ∀ i : ℕ, Complex.exp (Complex.I * i * β) = Complex.exp (Complex.I * β) ^ i :=
    fun i => by rw [← Complex.exp_nat_mul]; ring_nf
  rw [eq_div_iff hz]
  induction j with
  | zero => simp [partialSumFrom]
  | succ j ih =>
    simp only [partialSumFrom] at ih ⊢
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top (by omega),
      Finset.Ico_add_one_right_eq_Icc, add_mul, ih]
    simp only [hpow]
    ring

/-- DLMF 2.10.14: for `e^{iβ} ≠ 1` and `n ≥ 1`,
`S(α, β, n) = e^{iβ}/(e^{iβ} - 1) (e^{i(n-1)β} n^α - 1 + ∑_{j=1}^{n-1} e^{ijβ}(j^α - (j+1)^α))`. -/
@[dlmf 2.10.E14]
theorem oscillatorySum_eq {α β : ℝ} (hβ : Complex.exp (Complex.I * β) ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    oscillatorySum α β n = Complex.exp (Complex.I * β) / (Complex.exp (Complex.I * β) - 1) *
      (Complex.exp (Complex.I * (n - 1 : ℕ) * β) * ((n : ℝ) ^ α : ℝ) - 1 +
        ∑ j ∈ Ico 1 n, Complex.exp (Complex.I * j * β) *
          (((j : ℝ) ^ α : ℝ) - (((j + 1 : ℕ) : ℝ) ^ α : ℝ))) := by
  have hz : Complex.exp (Complex.I * β) - 1 ≠ 0 := sub_ne_zero.2 hβ
  set v : ℕ → ℂ := fun j => (((j : ℝ) ^ α : ℝ) : ℂ)
  rw [oscillatorySum, sum_by_parts (fun i => Complex.exp (Complex.I * i * β)) v hn]
  simp only [partialSumFrom_exp hβ]
  have hv1 : v 1 = 1 := by simp [v]
  have htel : ∑ j ∈ Ico 1 n, (v j - v (j + 1)) = v 1 - v n := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_Ico_succ_top (by omega), ih (by omega)]; ring
  have hsplit : ∑ j ∈ Ico 1 n, Complex.exp (Complex.I * β) *
        (Complex.exp (Complex.I * j * β) - 1) / (Complex.exp (Complex.I * β) - 1) *
        (v j - v (j + 1)) =
      Complex.exp (Complex.I * β) / (Complex.exp (Complex.I * β) - 1) *
        (∑ j ∈ Ico 1 n, Complex.exp (Complex.I * j * β) * (v j - v (j + 1)) -
          ∑ j ∈ Ico 1 n, (v j - v (j + 1))) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsplit, htel, hv1]
  simp only [v]
  ring

/-- DLMF 2.10.15: for every real `α` there is `C` with
`|j^α - (j+1)^α + α j^{α-1}| ≤ C |α(α-1)| j^{α-2}` for all integers `j ≥ 1`. -/
@[dlmf 2.10.E15]
theorem rpow_sub_rpow_succ (α : ℝ) :
    ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
      |(j : ℝ) ^ α - ((j : ℝ) + 1) ^ α + α * (j : ℝ) ^ (α - 1)| ≤
        C * |α * (α - 1)| * (j : ℝ) ^ (α - 2) := by
  sorry

/-- DLMF 2.10.16: for `e^{iβ} ≠ 1`, as `n → ∞`,
`S(α, β, n) = e^{iβ}/(e^{iβ} - 1)(e^{i(n-1)β} n^α - α S(α-1, β, n) + O(n^{α-1}) + O(1))`. -/
@[dlmf 2.10.E16]
theorem oscillatorySum_recursive {α β : ℝ} (hβ : Complex.exp (Complex.I * β) ≠ 1) :
    (fun n : ℕ => oscillatorySum α β n -
        Complex.exp (Complex.I * β) / (Complex.exp (Complex.I * β) - 1) *
          (Complex.exp (Complex.I * (n - 1 : ℕ) * β) * ((n : ℝ) ^ α : ℝ) -
            α * oscillatorySum (α - 1) β n)) =O[atTop]
      fun n => (n : ℝ) ^ (α - 1) + 1 := by
  sorry

/-- DLMF 2.10.17: for `e^{iβ} ≠ 1`, `S(α, β, n) = O(n^α) + O(1)` as `n → ∞`. -/
@[dlmf 2.10.E17]
theorem oscillatorySum_isBigO {α β : ℝ} (hβ : Complex.exp (Complex.I * β) ≠ 1) :
    (fun n : ℕ => oscillatorySum α β n) =O[atTop] fun n => (n : ℝ) ^ α + 1 := by
  sorry

/-- DLMF 2.10.18: for `e^{iβ} ≠ 1`, as `n → ∞`,
`S(α, β, n) = e^{inβ}/(e^{iβ} - 1) n^α + O(n^{α-1}) + O(1)`. -/
@[dlmf 2.10.E18]
theorem oscillatorySum_asymptotic {α β : ℝ} (hβ : Complex.exp (Complex.I * β) ≠ 1) :
    (fun n : ℕ => oscillatorySum α β n -
        Complex.exp (Complex.I * n * β) / (Complex.exp (Complex.I * β) - 1) *
          ((n : ℝ) ^ α : ℝ)) =O[atTop] fun n => (n : ℝ) ^ (α - 1) + 1 := by
  sorry

end DLMF.AsymptoticApproximations
