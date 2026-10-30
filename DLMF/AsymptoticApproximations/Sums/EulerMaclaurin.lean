/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Sums.Basic
public import DLMF.AsymptoticApproximations.Sums.PowerSums
public import DLMF.Gamma.BarnesG
public import DLMF.Gamma.Asymptotics.Stirling
public import Mathlib.Analysis.Calculus.MeanValue
public import DLMFMathlib.Analysis.Asymptotics.PowerSums

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
  §2.10(i). The harmonic expansion and its signed first-neglected-term bound reuse
  the digamma Binet remainder from `DLMF.Gamma.Asymptotics.Stirling`.
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

-- Power-sum asymptotics and their remaining signed-remainder statement are in `Sums.PowerSums`.

/-- The harmonic remainder is a Binet integral, using the digamma value at a
positive integer and the same Bernoulli coefficients as in the Gamma expansion. -/
private theorem harmonic_remainder_eq_integral (m n : ℕ) (hn : 1 ≤ n) :
    (harmonic (n - 1) : ℝ) - (Real.log n + Real.eulerMascheroniConstant - 1 / (2 * n) -
      ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) / (n : ℝ) ^ (2 * s)) =
      -∫ t in Ioi (0 : ℝ), Real.exp (-(n : ℝ) * t) *
        (t ^ 1 * (DLMF.Gamma.binetBeta t / t - DLMF.Gamma.binetPoly (m - 1) t)) := by
  have hd := Real.digamma_nat_add_one (n - 1)
  rw [← Nat.cast_add_one, Nat.sub_add_cancel hn] at hd
  have hs : Finset.Ico 1 m = Finset.Icc 1 (m - 1) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have h := DLMF.Gamma.digamma_sub_stirling_eq_integral (m - 1)
    (z := (n : ℝ)) (by exact_mod_cast (by omega : 0 < n))
  rw [hd, ← hs] at h
  simp_rw [div_mul_eq_div_div] at h ⊢
  linarith

/-- Later inverse-power scales are bounded by earlier ones on the positive integers. -/
private theorem invScale_isBigO_of_le {N M : ℕ} (hNM : N ≤ M) :
    g2b_invScale M =O[atTop] g2b_invScale N := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [g2b_invScale, Real.norm_eq_abs, abs_inv, abs_pow,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), one_mul]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hn' hNM)

/-- Pairing consecutive Bernoulli coefficients recovers the customary harmonic
polynomial with only even powers after the first term. -/
private theorem sum_harmonicCoeff_even (m n : ℕ) (hm : 1 ≤ m) :
    ∑ s ∈ range (2 * m), g2b_invScale s n * g2b_harmonicCoeff s =
      -1 / (2 * n) - ∑ k ∈ Ico 1 m, (bernoulli (2 * k) : ℝ) / (2 * k) /
        (n : ℝ) ^ (2 * k) := by
  induction m, hm using Nat.le_induction with
  | base =>
    simp [g2b_invScale, g2b_harmonicCoeff, sum_range_succ]
    ring
  | succ m hm ih =>
    have hodd : (bernoulli (2 * m + 1) : ℝ) = 0 := by
      rw [bernoulli_eq_zero_of_odd ⟨m, by omega⟩ (by omega)]
      simp
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, sum_range_succ,
      sum_range_succ, ih, sum_Ico_succ_top (by omega : 1 ≤ m)]
    simp only [g2b_invScale, g2b_harmonicCoeff, show 2 * m ≠ 0 by omega,
      show 2 * m ≠ 1 by omega, show 2 * m + 1 ≠ 0 by omega,
      show 2 * m + 1 ≠ 1 by omega, ite_false, hodd, neg_zero, zero_div, mul_zero, add_zero]
    push_cast
    ring

/-- DLMF §2.10(i) (remainder of 2.10.8): after the terms `s < m` of `∑ B_{2s}/(2s) n^{-2s}`
(`m ≥ 1`), the remainder is bounded in absolute value by the first neglected term
`-B_{2m}/(2m) n^{-2m}` and has the same sign, for every `n ≥ 1`. -/
@[dlmf 2.10.i]
theorem harmonic_remainder_bound {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    let R := (harmonic (n - 1) : ℝ) - (Real.log n + Real.eulerMascheroniConstant - 1 / (2 * n) -
      ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) / (n : ℝ) ^ (2 * s))
    let T := -(bernoulli (2 * m) : ℝ) / (2 * m) / (n : ℝ) ^ (2 * m)
    0 ≤ R * T ∧ |R| ≤ |T| := by
  dsimp only
  let R := (harmonic (n - 1) : ℝ) - (Real.log n + Real.eulerMascheroniConstant - 1 / (2 * n) -
    ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) / (n : ℝ) ^ (2 * s))
  let A := 2 * DLMF.Gamma.binetRemConst (m - 1) *
    ((2 * m - 1).factorial / (n : ℝ) ^ (2 * m))
  have hA : 0 ≤ A := by
    have hS : 0 ≤ DLMF.Gamma.binetRemConst (m - 1) := tsum_nonneg fun k => by positivity
    dsimp [A]
    positivity
  have hR := harmonic_remainder_eq_integral m n hn
  have hb := DLMF.Gamma.abs_integral_exp_mul_pow_mul_rem_le
    (z := (n : ℝ)) (by exact_mod_cast (by omega : 0 < n)) (m - 1) 1
  rw [← abs_neg, ← hR] at hb
  have hm1 : 2 * (m - 1) + 1 = 2 * m - 1 := by omega
  have hm2 : 2 * (m - 1) + 1 + 1 = 2 * m := by omega
  rw [hm2, hm1] at hb
  have hsign : 0 ≤ (-1 : ℝ) ^ m * R := by
    have hp : (-1 : ℝ) ^ m = -((-1) ^ (m - 1)) := by
      calc (-1 : ℝ) ^ m = (-1) ^ ((m - 1) + 1) := by congr 1; omega
        _ = -((-1) ^ (m - 1)) := by rw [pow_succ]; ring
    dsimp only [R]
    rw [hp, hR, neg_mul_neg, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have h := DLMF.Gamma.binetBeta_div_sub_binetPoly_sign (m - 1) ht
    convert mul_nonneg (mul_nonneg (Real.exp_pos (-(n : ℝ) * t)).le ht.le) h using 1
    simp only [pow_one]
    ring
  have hS := (DLMF.Gamma.hasSum_recip_two_pi_pow (k := m) (by omega)).tsum_eq
  have he : DLMF.Gamma.binetRemConst (m - 1) =
      (-1 : ℝ) ^ (m + 1) * (bernoulli (2 * m) : ℝ) / (2 * (2 * m).factorial) := by
    unfold DLMF.Gamma.binetRemConst
    simpa only [show 2 * (m - 1) + 2 = 2 * m by omega] using hS
  have hT : -(bernoulli (2 * m) : ℝ) / (2 * m) / (n : ℝ) ^ (2 * m) = (-1 : ℝ) ^ m * A := by
    dsimp [A]
    rw [he, (DLMF.Gamma.factorial_two_mul_sub m hm).2, pow_succ]
    have hp : (-1 : ℝ) ^ m * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
    have hf : ((2 * m - 1).factorial : ℝ) ≠ 0 := by positivity
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    field_simp
    simp only [sq, hp, mul_one]
  rw [hT]
  constructor
  · change 0 ≤ R * ((-1 : ℝ) ^ m * A)
    nlinarith [mul_nonneg hsign hA]
  · rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hA]
    exact hb

/-- DLMF 2.10.8: as `n → ∞`,
`∑_{j=1}^{n-1} 1/j ∼ ln n + γ - 1/(2n) - ∑_{s ≥ 1} B_{2s}/(2s) n^{-2s}`. -/
@[dlmf 2.10.E8]
theorem harmonic_asymptotic :
    HasAsymptoticExpansion atTop g2b_invScale g2b_harmonicCoeff
      (fun n : ℕ => (harmonic (n - 1) : ℝ) - Real.log n - Real.eulerMascheroniConstant) := by
  have hR (m : ℕ) (hm : 1 ≤ m) :
      (fun n : ℕ => (harmonic (n - 1) : ℝ) - Real.log n - Real.eulerMascheroniConstant -
        ∑ s ∈ range (2 * m), g2b_invScale s n * g2b_harmonicCoeff s) =O[atTop]
        g2b_invScale (2 * m) := by
    refine IsBigO.of_bound |(bernoulli (2 * m) : ℝ) / (2 * m)| ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hb := (harmonic_remainder_bound hm hn).2
    calc _ = |(harmonic (n - 1) : ℝ) - (Real.log n + Real.eulerMascheroniConstant -
          1 / (2 * n) - ∑ k ∈ Ico 1 m, (bernoulli (2 * k) : ℝ) / (2 * k) /
            (n : ℝ) ^ (2 * k))| := by
          rw [sum_harmonicCoeff_even m n hm, Real.norm_eq_abs]
          congr 1
          ring
      _ ≤ |-(bernoulli (2 * m) : ℝ) / (2 * m) / (n : ℝ) ^ (2 * m)| := hb
      _ = _ := by
          simp only [g2b_invScale, Real.norm_eq_abs, abs_inv, abs_pow,
            abs_div, abs_neg, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
          ring
  intro N
  let M := 2 * (N + 1)
  have hNM : N ≤ M := by dsimp [M]; omega
  have hr := (hR (N + 1) (by omega)).trans (invScale_isBigO_of_le hNM)
  have htail : (fun n => ∑ s ∈ Ico N M, g2b_invScale s n * g2b_harmonicCoeff s) =O[atTop]
      g2b_invScale N := by
    have h := IsBigO.sum (s := Ico N M) (A := fun s n => g2b_invScale s n * g2b_harmonicCoeff s)
      fun s hs => ((invScale_isBigO_of_le (mem_Ico.mp hs).1).const_mul_left
        (g2b_harmonicCoeff s)).congr_left (fun n => mul_comm _ _)
    exact h.congr_left fun n => by simp only [Finset.sum_apply]
  simp only [smul_eq_mul]
  refine (hr.add htail).congr_left fun n => ?_
  have hsum := sum_range_add_sum_Ico (fun s => g2b_invScale s n * g2b_harmonicCoeff s) hNM
  dsimp only [M] at hsum ⊢
  rw [← hsum]
  ring

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
  have hb (α : ℝ) : (fun n => oscillatorySum α β n) =O[atTop]
      fun n => ∑ j ∈ Ico 1 n, (j : ℝ) ^ α := IsBigO.of_norm_le (norm_oscillatorySum_le α β)
  exact ⟨fun α hα => (hb α).trans (Real.sum_Ico_rpow_isBigO_one hα),
    (hb (-1)).trans Real.sum_Ico_rpow_neg_one_isBigO_log,
    fun α hα => (hb α).trans (Real.sum_Ico_rpow_isBigO hα)⟩

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

/-- On a positive unit interval starting at `a ≥ 1`, any real power is bounded
by its value at `a` times a constant depending only on the exponent. -/
private lemma rpow_le_mul_on_unit_interval (p : ℝ) {a u : ℝ} (ha : 1 ≤ a)
    (hu : u ∈ Icc a (a + 1)) : u ^ p ≤ 2 ^ |p| * a ^ p := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have h2 : 1 ≤ (2 : ℝ) ^ |p| := Real.one_le_rpow (by norm_num) (abs_nonneg p)
  rcases le_total p 0 with hp | hp
  · exact (Real.rpow_le_rpow_of_nonpos ha0 hu.1 hp).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg ha0.le _) h2)
  · calc u ^ p ≤ (2 * a) ^ p :=
          Real.rpow_le_rpow (ha0.le.trans hu.1) (by linarith [hu.2]) hp
      _ = 2 ^ |p| * a ^ p := by rw [Real.mul_rpow (by norm_num) ha0.le, abs_of_nonneg hp]

/-- DLMF 2.10.15: for every real `α` there is `C` with
`|j^α - (j+1)^α + α j^{α-1}| ≤ C |α(α-1)| j^{α-2}` for all integers `j ≥ 1`. -/
@[dlmf 2.10.E15]
theorem rpow_sub_rpow_succ (α : ℝ) :
    ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
      |(j : ℝ) ^ α - ((j : ℝ) + 1) ^ α + α * (j : ℝ) ^ (α - 1)| ≤
        C * |α * (α - 1)| * (j : ℝ) ^ (α - 2) := by
  refine ⟨2 ^ |α - 2|, fun j hj => ?_⟩
  let a : ℝ := j
  have ha : 1 ≤ a := by dsimp [a]; exact_mod_cast hj
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  let B := 2 ^ |α - 2| * |α * (α - 1)| * a ^ (α - 2)
  have hB : 0 ≤ B := by positivity
  have hD (t : ℝ) (ht : t ∈ Icc a (a + 1)) :
      HasDerivAt (fun u : ℝ => α * u ^ (α - 1))
        (α * (α - 1) * t ^ (α - 2)) t := by
    apply ((Real.hasDerivAt_rpow_const (p := α - 1)
      (Or.inl (ha0.trans_le ht.1).ne')).const_mul α).congr_deriv
    rw [show α - 1 - 1 = α - 2 by ring]
    ring
  have hDb (t : ℝ) (ht : t ∈ Ico a (a + 1)) :
      ‖α * (α - 1) * t ^ (α - 2)‖ ≤ B := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith [ht.1]) _)]
    simpa [B, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left (rpow_le_mul_on_unit_interval (α - 2) ha
        (Ico_subset_Icc_self ht)) (abs_nonneg (α * (α - 1)))
  have hdiff := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hD t ht).hasDerivWithinAt) hDb
  have hE (t : ℝ) (ht : t ∈ Icc a (a + 1)) :
      HasDerivAt (fun u : ℝ => u ^ α - u * (α * a ^ (α - 1)))
        (α * t ^ (α - 1) - α * a ^ (α - 1)) t := by
    exact (Real.hasDerivAt_rpow_const (Or.inl (ha0.trans_le ht.1).ne')).sub
      (hasDerivAt_mul_const _)
  have hb := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hE t ht).hasDerivWithinAt)
    (fun t ht => (hdiff t (Ico_subset_Icc_self ht)).trans
      (mul_le_of_le_one_right hB (by linarith [ht.2]))) (a + 1) (by constructor <;> linarith)
  have he : a ^ α - (a + 1) ^ α + α * a ^ (α - 1) =
      -(((a + 1) ^ α - (a + 1) * (α * a ^ (α - 1))) -
        (a ^ α - a * (α * a ^ (α - 1)))) := by ring
  rw [show (j : ℝ) = a from rfl, he, abs_neg, ← Real.norm_eq_abs]
  simpa only [add_sub_cancel_left, mul_one] using hb

/-- The sum of the Taylor errors of the power weight has the next-order power bound. -/
private lemma oscillatorySum_remainder_isBigO (α β : ℝ) :
    (fun n : ℕ => ∑ j ∈ Ico 1 n, Complex.exp (Complex.I * j * β) *
      (((j : ℝ) ^ α - ((j : ℝ) + 1) ^ α + α * (j : ℝ) ^ (α - 1) : ℝ) : ℂ))
      =O[atTop] fun n => (n : ℝ) ^ (α - 1) + 1 := by
  by_cases hα : α = 1
  · subst α
    simp only [Real.rpow_one, sub_self, Real.rpow_zero, one_mul]
    have hz (j : ℕ) : (j : ℝ) - ((j : ℝ) + 1) + 1 = 0 := by ring
    simp only [hz, Complex.ofReal_zero, mul_zero, sum_const_zero]
    exact isBigO_zero _ _
  obtain ⟨C, hC⟩ := rpow_sub_rpow_succ α
  have hb : (fun n : ℕ => ∑ j ∈ Ico 1 n, Complex.exp (Complex.I * j * β) *
      (((j : ℝ) ^ α - ((j : ℝ) + 1) ^ α + α * (j : ℝ) ^ (α - 1) : ℝ) : ℂ))
      =O[atTop] fun n => ∑ j ∈ Ico 1 n, (j : ℝ) ^ (α - 2) := by
    refine IsBigO.of_bound (C * |α * (α - 1)|) (Eventually.of_forall fun n => ?_)
    rw [Real.norm_of_nonneg (sum_nonneg fun j _ => Real.rpow_nonneg (Nat.cast_nonneg _) _),
      Finset.mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun j hj => ?_)
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have he : (Complex.I * j * β).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
    rw [he, Real.exp_zero, one_mul]
    exact hC j (mem_Ico.mp hj).1
  have hsum := Real.sum_Ico_rpow_isBigO_add_one (p := α - 2) (by intro h; apply hα; linarith)
  simpa only [show α - 2 + 1 = α - 1 by ring] using hb.trans hsum

/-- DLMF 2.10.16: for `e^{iβ} ≠ 1`, as `n → ∞`,
`S(α, β, n) = e^{iβ}/(e^{iβ} - 1)(e^{i(n-1)β} n^α - α S(α-1, β, n) + O(n^{α-1}) + O(1))`. -/
@[dlmf 2.10.E16]
theorem oscillatorySum_recursive {α β : ℝ} (hβ : Complex.exp (Complex.I * β) ≠ 1) :
    (fun n : ℕ => oscillatorySum α β n -
        Complex.exp (Complex.I * β) / (Complex.exp (Complex.I * β) - 1) *
          (Complex.exp (Complex.I * (n - 1 : ℕ) * β) * ((n : ℝ) ^ α : ℝ) -
            α * oscillatorySum (α - 1) β n)) =O[atTop]
      fun n => (n : ℝ) ^ (α - 1) + 1 := by
  let E := fun n : ℕ => ∑ j ∈ Ico 1 n, Complex.exp (Complex.I * j * β) *
    (((j : ℝ) ^ α - ((j : ℝ) + 1) ^ α + α * (j : ℝ) ^ (α - 1) : ℝ) : ℂ)
  have he (n : ℕ) : E n = (∑ j ∈ Ico 1 n, Complex.exp (Complex.I * j * β) *
      (((j : ℝ) ^ α : ℝ) - (((j + 1 : ℕ) : ℝ) ^ α : ℝ))) +
        α * oscillatorySum (α - 1) β n := by
    simp only [E, oscillatorySum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have h1 : (fun _ : ℕ => (1 : ℂ)) =O[atTop] fun n => (n : ℝ) ^ (α - 1) + 1 :=
    IsBigO.of_norm_le fun n => by
      rw [norm_one]
      linarith [Real.rpow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (α - 1)]
  refine (((oscillatorySum_remainder_isBigO α β).sub h1).const_mul_left
    (Complex.exp (Complex.I * β) / (Complex.exp (Complex.I * β) - 1))).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hEn := he n
  dsimp only [E] at hEn
  rw [oscillatorySum_eq hβ hn, hEn]
  ring

/-- DLMF 2.10.17: for `e^{iβ} ≠ 1`, `S(α, β, n) = O(n^α) + O(1)` as `n → ∞`. -/
@[dlmf 2.10.E17]
theorem oscillatorySum_isBigO {α β : ℝ} (hβ : Complex.exp (Complex.I * β) ≠ 1) :
    (fun n : ℕ => oscillatorySum α β n) =O[atTop] fun n => (n : ℝ) ^ α + 1 := by
  have hvar (n : ℕ) (hn : 1 ≤ n) :
      ∑ j ∈ Ico 1 n, |(j : ℝ) ^ α - ((j + 1 : ℕ) : ℝ) ^ α| ≤ (n : ℝ) ^ α + 1 := by
    have ht := Finset.sum_Ico_sub (fun j : ℕ => (j : ℝ) ^ α) hn
    simp only [Nat.cast_one, Real.one_rpow] at ht
    rcases le_total 0 α with hα | hα
    · have he : ∑ j ∈ Ico 1 n, |(j : ℝ) ^ α - ((j + 1 : ℕ) : ℝ) ^ α| =
          (n : ℝ) ^ α - 1 := by
        rw [← ht]
        refine sum_congr rfl fun j hj => ?_
        rw [abs_sub_comm, abs_of_nonneg]
        exact sub_nonneg.mpr (Real.rpow_le_rpow (Nat.cast_nonneg _) (by norm_cast; omega) hα)
      rw [he]
      linarith
    · have he : ∑ j ∈ Ico 1 n, |(j : ℝ) ^ α - ((j + 1 : ℕ) : ℝ) ^ α| =
          1 - (n : ℝ) ^ α := by
        rw [← neg_sub ((n : ℝ) ^ α) 1, ← ht, ← Finset.sum_neg_distrib]
        refine sum_congr rfl fun j hj => ?_
        rw [abs_of_nonneg, neg_sub]
        exact sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (mem_Ico.mp hj).1)
          (by norm_cast; omega) hα)
      rw [he]
      linarith [Real.rpow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) α]
  let K := ‖Complex.exp (Complex.I * β) / (Complex.exp (Complex.I * β) - 1)‖
  refine IsBigO.of_bound (2 * K) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : 0 ≤ (n : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) α
  have he (j : ℕ) : ‖Complex.exp (Complex.I * j * β)‖ = 1 := by
    rw [show Complex.I * j * β = ((j * β : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  rw [oscillatorySum_eq hβ hn, norm_mul, Real.norm_of_nonneg (by positivity)]
  have hs : ‖∑ j ∈ Ico 1 n, Complex.exp (Complex.I * j * β) *
      (((j : ℝ) ^ α : ℝ) - (((j + 1 : ℕ) : ℝ) ^ α : ℝ))‖ ≤ (n : ℝ) ^ α + 1 := by
    refine (norm_sum_le _ _).trans ((le_of_eq (sum_congr rfl fun j _ => ?_)).trans (hvar n hn))
    rw [norm_mul, he, one_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hfirst : ‖Complex.exp (Complex.I * (n - 1 : ℕ) * β) * ((n : ℝ) ^ α : ℝ) - 1‖ ≤
      (n : ℝ) ^ α + 1 := by
    refine (norm_sub_le _ _).trans_eq ?_
    rw [norm_mul, he, Complex.norm_real, Real.norm_of_nonneg hn0, norm_one, one_mul]
  have hb := (norm_add_le _ _).trans (add_le_add hfirst hs)
  calc _ ≤ K * (((n : ℝ) ^ α + 1) + ((n : ℝ) ^ α + 1)) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = 2 * K * ((n : ℝ) ^ α + 1) := by ring

/-- DLMF 2.10.18: for `e^{iβ} ≠ 1`, as `n → ∞`,
`S(α, β, n) = e^{inβ}/(e^{iβ} - 1) n^α + O(n^{α-1}) + O(1)`. -/
@[dlmf 2.10.E18]
theorem oscillatorySum_asymptotic {α β : ℝ} (hβ : Complex.exp (Complex.I * β) ≠ 1) :
    (fun n : ℕ => oscillatorySum α β n -
        Complex.exp (Complex.I * n * β) / (Complex.exp (Complex.I * β) - 1) *
          ((n : ℝ) ^ α : ℝ)) =O[atTop] fun n => (n : ℝ) ^ (α - 1) + 1 := by
  have hprev := (oscillatorySum_isBigO (α := α - 1) hβ).const_mul_left
    ((Complex.exp (Complex.I * β) / (Complex.exp (Complex.I * β) - 1)) * α)
  have hrec := (oscillatorySum_recursive (α := α) hβ).sub hprev
  refine hrec.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have he : Complex.exp (Complex.I * (n - 1 : ℕ) * β) * Complex.exp (Complex.I * β) =
      Complex.exp (Complex.I * n * β) := by
    rw [← Complex.exp_add]
    congr 1
    rw [Nat.cast_sub hn]
    push_cast
    ring
  rw [← he]
  ring

end DLMF.AsymptoticApproximations
