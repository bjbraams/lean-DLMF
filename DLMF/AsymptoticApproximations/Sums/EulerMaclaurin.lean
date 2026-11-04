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
public import DLMF.BernoulliEuler.Inequalities
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The Euler–Maclaurin formula and summation by parts

This file covers DLMF §2.10(i)–(ii): the Euler–Maclaurin and Abel–Plana formulas, the example
`∑ j ln j`, the harmonic numbers, summation by parts and the oscillatory sums
`S(α, β, n) = ∑_{j=1}^{n-1} e^{ijβ} j^α`.

## Main results

* `euler_maclaurin`: the Euler–Maclaurin formula (DLMF 2.10.1).
* `abel_plana`: the Abel–Plana formula (DLMF 2.10.2).
* `jLogJSum_eq`, `jLogJRemainder_bound`, `tendsto_jLogJSum_sub`: the expansion of
  `∑_{j=1}^{n} j ln j` and its remainder (DLMF 2.10.3–2.10.5, §2.10(i)).
* `log_glaisherKinkelin_eq`: the constant `C = ln A` of DLMF 2.10.4 (DLMF 2.10.6).
* `harmonic_asymptotic`, `harmonic_remainder_bound`: the harmonic numbers (DLMF 2.10.8) with
  the remainder bound of §2.10(i).
* `sum_by_parts`: summation by parts (DLMF 2.10.9–2.10.10).
* `norm_oscillatorySum_le`, `oscillatorySum_isBigO_trivial`, `partialSumFrom_exp`,
  `oscillatorySum_eq`, `rpow_sub_rpow_succ`, `oscillatorySum_recursive`,
  `oscillatorySum_isBigO`, `oscillatorySum_asymptotic`: the oscillatory example
  (DLMF 2.10.12–2.10.18).

## Implementation notes

`euler_maclaurin` is derived from DLMFMathlib's `sum_range_succ_eq_integral_add`
(Euler–Maclaurin with periodic Bernoulli remainder) by a shift to the integer `a` and the
vanishing of the odd Bernoulli numbers. The constant `C` of 2.10.4 is `ln A` with the
Glaisher–Kinkelin constant `DLMF.Gamma.glaisherKinkelin` (DLMF 5.17.6); the two closed forms of
2.10.6 come from `DLMF.Gamma.glaisherKinkelin_eq_zeta_neg_one` (DLMF 5.17.7), and the leading
behaviour of `S(n)` from `DLMF.Gamma.BarnesAsymp.tendsto_hseq`. The harmonic expansion and its
signed first-neglected-term bound use the digamma Binet remainder from
`DLMF.Gamma.Asymptotics.Stirling`. The power sums 2.10.7 are in `Sums/PowerSums`.

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
private lemma sum_bernoulli_odd_eq_neg_sum_even (c : ℕ → ℝ) (m : ℕ) :
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
  rw [hper, sum_bernoulli_odd_eq_neg_sum_even
      (fun j => iteratedDeriv j f (N + a) - iteratedDeriv j f a),
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

/-- Derivatives of `x ln x` of order at least two. -/
private lemma iteratedDeriv_mul_log {x : ℝ} (hx : 0 < x) (k : ℕ) :
    iteratedDeriv (k + 2) (fun x : ℝ => x * Real.log x) x =
      (-1) ^ k * k ! * x ^ (-1 - k : ℤ) := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ']
  have h1 : ∀ y : ℝ, 0 < y → deriv (fun x : ℝ => x * Real.log x) =ᶠ[𝓝 y]
      fun x => Real.log x + 1 := fun y hy => by
    filter_upwards [lt_mem_nhds hy] with z hz using Real.deriv_mul_log hz.ne'
  have h2 : deriv (deriv (fun x : ℝ => x * Real.log x)) =ᶠ[𝓝 x] Inv.inv := by
    filter_upwards [lt_mem_nhds hx] with y hy
    rw [(h1 y hy).deriv_eq]
    simp [Real.deriv_log]
  rw [h2.iteratedDeriv_eq, iteratedDeriv_eq_iterate, iter_deriv_inv]

/-- First derivative of `x ln x`. -/
private lemma iteratedDeriv_one_mul_log {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 1 (fun x : ℝ => x * Real.log x) x = Real.log x + 1 := by
  rw [iteratedDeriv_one, Real.deriv_mul_log hx.ne']

/-- A smooth function on `ℝ` agreeing with `x ln x` for `x ≥ 1/2`. -/
private lemma exists_contDiff_eq_mul_log :
    ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ ∀ x : ℝ, 1 / 2 < x →
      f =ᶠ[𝓝 x] fun x : ℝ => x * Real.log x := by
  set ψ : ℝ → ℝ := fun x => Real.smoothTransition (4 * x - 1) * x +
    (1 - Real.smoothTransition (4 * x - 1)) * (1 / 4)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    have hs : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => Real.smoothTransition (4 * x - 1) :=
      Real.smoothTransition.contDiff.comp (by fun_prop)
    exact (hs.mul contDiff_id).add ((contDiff_const.sub hs).mul contDiff_const)
  have hpos : ∀ x, 0 < ψ x := by
    intro x
    have h0 := Real.smoothTransition.nonneg (4 * x - 1)
    have h1 := Real.smoothTransition.le_one (4 * x - 1)
    by_cases hx : x ≤ 1 / 4
    · rw [show ψ x = 1 / 4 by
        simp only [ψ, Real.smoothTransition.zero_of_nonpos (show 4 * x - 1 ≤ 0 by linarith)]
        ring]
      norm_num
    · simp only [ψ]
      nlinarith
  refine ⟨fun x => ψ x * Real.log (ψ x), hψ.mul (hψ.log fun x => (hpos x).ne'), ?_⟩
  intro x hx
  filter_upwards [lt_mem_nhds hx] with y hy
  have : ψ y = y := by
    simp only [ψ, Real.smoothTransition.one_of_one_le (show 1 ≤ 4 * y - 1 by linarith)]
    ring
  simp only [this]

/-- Pointwise bound for the integrand of `R_m(n)` (DLMF 2.10.5), `m ≥ 2`. -/
private lemma exists_norm_jLogJIntegrand_le {m : ℕ} (hm : 2 ≤ m) :
    ∃ K : ℝ, ∀ x : ℝ, 0 < x → ‖(periodicBernoulli (2 * m) x - bernoulli (2 * m)) /
      (2 * m * (2 * m - 1) * x ^ (2 * m - 1))‖ ≤ K * x ^ (-((2 * m - 1 : ℕ) : ℝ)) := by
  obtain ⟨D, hD⟩ := DLMF.Zeta.exists_abs_periodicBernoulli_le (2 * m)
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : 0 < (2 * m * (2 * m - 1) : ℝ) := by nlinarith
  refine ⟨(D + |(bernoulli (2 * m) : ℝ)|) / (2 * m * (2 * m - 1)), fun x hx0 => ?_⟩
  have hxp : 0 < x ^ (2 * m - 1) := pow_pos hx0 _
  rw [Real.rpow_neg hx0.le, Real.rpow_natCast, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * m * (2 * m - 1) * x ^ (2 * m - 1))]
  have hnum : |periodicBernoulli (2 * m) x - bernoulli (2 * m)| ≤
      D + |(bernoulli (2 * m) : ℝ)| := (abs_sub _ _).trans (by linarith [hD x])
  rw [div_le_iff₀ (by positivity)]
  calc |periodicBernoulli (2 * m) x - bernoulli (2 * m)|
      ≤ D + |(bernoulli (2 * m) : ℝ)| := hnum
    _ = (D + |(bernoulli (2 * m) : ℝ)|) / (2 * m * (2 * m - 1)) * (x ^ (2 * m - 1))⁻¹ *
        (2 * m * (2 * m - 1) * x ^ (2 * m - 1)) := by
        have : (2 * m - 1 : ℝ) ≠ 0 := by linarith
        field_simp

/-- `((2m - 1 : ℕ) : ℝ) = 2m - 1` for `m ≥ 2`. -/
private lemma two_mul_sub_one_cast {m : ℕ} (hm : 2 ≤ m) :
    ((2 * m - 1 : ℕ) : ℝ) = 2 * m - 1 := by
  rw [Nat.cast_sub (by omega)]; push_cast; ring

/-- The integrand of `R_m(n)` (DLMF 2.10.5) is integrable on `(a, ∞)`, `a > 0`, `m ≥ 2`. -/
private lemma integrableOn_jLogJIntegrand {m : ℕ} (hm : 2 ≤ m) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => (periodicBernoulli (2 * m) x - bernoulli (2 * m)) /
      (2 * m * (2 * m - 1) * x ^ (2 * m - 1))) (Ioi a) := by
  obtain ⟨K, hK⟩ := exists_norm_jLogJIntegrand_le hm
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hi := (integrableOn_Ioi_rpow_of_lt (a := -((2 * m - 1 : ℕ) : ℝ))
    (by rw [two_mul_sub_one_cast hm]; linarith) ha).const_mul K
  refine hi.mono' ?_ ?_
  · refine (((measurable_periodicBernoulli _).sub_const _).div ?_).aestronglyMeasurable
    exact measurable_const.mul (measurable_id.pow_const _)
  · exact (ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun x hx => hK x (ha.trans hx))

/-- `R_m(n) → 0` as `n → ∞` (`m ≥ 2`). -/
private lemma tendsto_jLogJRemainder {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun n : ℕ => jLogJRemainder m n) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_norm_jLogJIntegrand_le hm
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set a : ℝ := -((2 * m - 1 : ℕ) : ℝ) with ha
  have ha1 : a < -1 := by rw [ha, two_mul_sub_one_cast hm]; linarith
  have hlim : Tendsto (fun n : ℕ => K * (-((n : ℝ) ^ (a + 1)) / (a + 1))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := -(a + 1)) (by linarith)).comp
      tendsto_natCast_atTop_atTop
    simp only [neg_neg] at h
    have h' := (h.div_const (a + 1)).neg.const_mul K
    simp only [neg_zero, zero_div, mul_zero] at h'
    refine h'.congr fun n => ?_
    simp only [Function.comp_apply]
    ring
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [jLogJRemainder, ← integral_Ioi_rpow_of_lt ha1 hn0, ← MeasureTheory.integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt ha1 hn0).const_mul K) ?_
  exact (ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun x hx => hK x (hn0.trans hx))

/-- The `s`-th Euler–Maclaurin term for `x ln x` (`s = t + 2 ≥ 2`). -/
private lemma jLogJ_em_term (t n : ℕ) (hn : 1 ≤ n) :
    (bernoulli (2 * (t + 2)) : ℝ) / ((2 * (t + 2))! : ℕ) *
      ((-1) ^ (2 * t + 1) * ((2 * t + 1)! : ℕ) * (n : ℝ) ^ (-1 - (2 * t + 1 : ℕ) : ℤ) -
        (-1) ^ (2 * t + 1) * ((2 * t + 1)! : ℕ) * (1 : ℝ) ^ (-1 - (2 * t + 1 : ℕ) : ℤ)) =
      (bernoulli (2 * (t + 2)) : ℝ) /
          (2 * ((t + 2 : ℕ) : ℝ) * (2 * ((t + 2 : ℕ) : ℝ) - 1) * (2 * ((t + 2 : ℕ) : ℝ) - 2)) +
        sumMulLogTerm (t + 2) n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hodd : (-1 : ℝ) ^ (2 * t + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  have hz : (n : ℝ) ^ (-1 - (2 * t + 1 : ℕ) : ℤ) = ((n : ℝ) ^ (2 * t + 2))⁻¹ := by
    rw [show (-1 - (2 * t + 1 : ℕ) : ℤ) = -((2 * t + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast]
  have hfac : ((2 * (t + 2))! : ℝ) =
      (2 * t + 4) * (2 * t + 3) * (2 * t + 2) * ((2 * t + 1)! : ℕ) := by
    rw [show 2 * (t + 2) = (2 * t + 1) + 1 + 1 + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [sumMulLogTerm, hodd, hz, one_zpow, show 2 * (t + 2) - 2 = 2 * t + 2 by omega]
  push_cast
  rw [hfac]
  have hf0 : ((2 * t + 1)! : ℝ) ≠ 0 := by positivity
  have ht : (0 : ℝ) ≤ t := t.cast_nonneg
  have h1 : 2 * ((t : ℝ) + 2) - 1 ≠ 0 := by linarith
  have h2 : 2 * ((t : ℝ) + 2) - 2 ≠ 0 := by linarith
  have h3 : (2 * (t : ℝ) + 4) * (2 * t + 3) * (2 * t + 2) ≠ 0 := by positivity
  have h4 : (1 : ℝ) + t ≠ 0 := by positivity
  generalize (bernoulli (2 * (t + 2)) : ℝ) = B
  generalize ((2 * t + 1)! : ℝ) = F at hf0 ⊢
  have hN : (n : ℝ) ^ (2 * t + 2) ≠ 0 := by positivity
  generalize (n : ℝ) ^ (2 * t + 2) = N at hN ⊢
  rw [show 2 * ((t : ℝ) + 2) * (2 * (t + 2) - 1) * (2 * (t + 2) - 2) =
    (2 * t + 4) * (2 * t + 3) * (2 * t + 2) by ring]
  field_simp
  ring

/-- The constant of the exact form of 2.10.4 before its identification with `ln A`. -/
private noncomputable def jLogJConst (m : ℕ) : ℝ :=
  1 / 4 + ∑ s ∈ Ico 2 m, (bernoulli (2 * s) : ℝ) / (2 * s * (2 * s - 1) * (2 * s - 2)) -
    jLogJRemainder m 1

/-- Euler–Maclaurin for `∑ j ln j`, with an unidentified constant. -/
private lemma jLogJSum_eq_const {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n) :
    jLogJSum n = (n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 + n / 2 * Real.log n +
      Real.log n / 12 + jLogJConst m +
      ∑ s ∈ Ico 2 m, sumMulLogTerm s n + jLogJRemainder m n := by
  obtain ⟨f, hf, hfeq⟩ := exists_contDiff_eq_mul_log
  set g : ℝ → ℝ := fun x => x * Real.log x with hg
  have hfg : ∀ x : ℝ, 1 ≤ x → f x = g x := fun x hx => (hfeq x (by linarith)).eq_of_nhds
  have hfgk : ∀ (k : ℕ) (x : ℝ), 1 ≤ x → iteratedDeriv k f x = iteratedDeriv k g x :=
    fun k x hx => (hfeq x (by linarith)).iteratedDeriv_eq k
  have hf' : ContDiff ℝ (2 * m : ℕ) f := contDiff_infty.1 hf _
  have h := euler_maclaurin (m := m) (by omega) hf' 1 (n - 1)
  have hN : ((1 : ℤ) : ℝ) + ((n - 1 : ℕ) : ℝ) = n := by
    rw [Nat.cast_sub hn]; push_cast; ring
  rw [hN] at h
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- the sum
  have hS : ∑ k ∈ range (n - 1 + 1), f (((1 : ℤ) : ℝ) + k) = jLogJSum n := by
    rw [Nat.sub_add_cancel hn, jLogJSum, ← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hfg _ (by push_cast; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])]
    simp only [hg]; push_cast; ring
  -- the integral
  have hI : ∫ x in ((1 : ℤ) : ℝ)..n, f x = (n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 +
      1 / 4 := by
    push_cast
    rw [intervalIntegral.integral_congr (g := g) fun x hx => hfg x (by
      rw [uIcc_of_le hn1] at hx; exact hx.1)]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => x ^ 2 / 2 * Real.log x - x ^ 2 / 4)]
    · simp
    · intro x hx
      rw [uIcc_of_le hn1] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      have := (((hasDerivAt_pow 2 x).div_const 2).mul (Real.hasDerivAt_log hx0.ne')).sub
        ((hasDerivAt_pow 2 x).div_const 4)
      convert this using 1
      simp only [hg]; field_simp; ring
    · refine ContinuousOn.intervalIntegrable fun x hx => ?_
      rw [uIcc_of_le hn1] at hx
      exact (continuousAt_id.mul (Real.continuousAt_log (by linarith [hx.1]))).continuousWithinAt
  simp only [Int.cast_one] at h hS hI
  -- the Bernoulli terms
  have hB : ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / ((2 * s)! : ℕ) *
      (iteratedDeriv (2 * s - 1) f n - iteratedDeriv (2 * s - 1) f 1) =
      Real.log n / 12 + ∑ s ∈ Ico 2 m, ((bernoulli (2 * s) : ℝ) /
        (2 * s * (2 * s - 1) * (2 * s - 2)) + sumMulLogTerm s n) := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < m)]
    congr 1
    · rw [hfgk _ _ hn1, hfgk _ _ le_rfl, show 2 * 1 - 1 = 1 from rfl,
        iteratedDeriv_one_mul_log (by linarith), iteratedDeriv_one_mul_log one_pos]
      simp [bernoulli_two]
      ring
    · refine Finset.sum_congr rfl fun s hs => ?_
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by simp at hs; omega⟩
      rw [hfgk _ _ hn1, hfgk _ _ le_rfl, show 2 * (t + 2) - 1 = (2 * t + 1) + 2 by omega,
        iteratedDeriv_mul_log (by linarith), iteratedDeriv_mul_log one_pos]
      exact jLogJ_em_term t n hn
  -- the remainder
  have hR : ∫ x in (1 : ℝ)..n, ((bernoulli (2 * m) : ℝ) - periodicBernoulli (2 * m) x) /
      ((2 * m)! : ℕ) * iteratedDeriv (2 * m) f x = jLogJRemainder m n - jLogJRemainder m 1 := by
    rw [intervalIntegral.integral_congr (g := fun x => -((periodicBernoulli (2 * m) x -
      bernoulli (2 * m)) / (2 * m * (2 * m - 1) * x ^ (2 * m - 1))))]
    · rw [intervalIntegral.integral_neg, ← intervalIntegral.integral_Ioi_sub_Ioi
        (integrableOn_jLogJIntegrand hm one_pos) hn1, jLogJRemainder, jLogJRemainder,
        Nat.cast_one]
      ring
    · intro x hx
      rw [uIcc_of_le hn1] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      obtain ⟨t, rfl⟩ : ∃ t, m = t + 2 := ⟨m - 2, by omega⟩
      simp only
      rw [hfgk _ _ hx.1, show 2 * (t + 2) = (2 * t + 2) + 2 by ring,
        iteratedDeriv_mul_log hx0]
      have hz : x ^ (-1 - (2 * t + 2 : ℕ) : ℤ) = (x ^ (2 * t + 2 + 2 - 1))⁻¹ := by
        rw [show (-1 - (2 * t + 2 : ℕ) : ℤ) = -((2 * t + 2 + 2 - 1 : ℕ) : ℤ) by
          push_cast [show 2 * t + 2 + 2 - 1 = 2 * t + 3 by omega]; ring, zpow_neg, zpow_natCast]
      have hev : (-1 : ℝ) ^ (2 * t + 2) = 1 := by
        rw [show 2 * t + 2 = 2 * (t + 1) by ring, pow_mul]; norm_num
      have hfac : (((2 * t + 2 + 2)! : ℕ) : ℝ) =
          (2 * t + 4) * (2 * t + 3) * ((2 * t + 2)! : ℕ) := by
        rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
      rw [hz, hev, hfac]
      have hf0 : (((2 * t + 2)! : ℕ) : ℝ) ≠ 0 := by positivity
      have hxp : x ^ (2 * t + 2 + 2 - 1) ≠ 0 := by positivity
      generalize (((2 * t + 2)! : ℕ) : ℝ) = F at hf0 ⊢
      generalize x ^ (2 * t + 2 + 2 - 1) = X at hxp ⊢
      push_cast
      have ht : (0 : ℝ) ≤ t := t.cast_nonneg
      have h3 : (2 * (t : ℝ) + 4) * (2 * t + 3) ≠ 0 := by positivity
      rw [show 2 * ((t : ℝ) + 2) * (2 * (t + 2) - 1) = (2 * t + 4) * (2 * t + 3) by ring]
      field_simp
      ring
  rw [hS, hI, hB, hR] at h
  rw [h, jLogJConst, hfg 1 le_rfl, hfg n hn1, Finset.sum_add_distrib]
  simp only [hg, Real.log_one, mul_zero]
  ring

/-- The constant of the exact form is `ln A`. -/
private lemma jLogJConst_eq {m : ℕ} (hm : 2 ≤ m) :
    jLogJConst m = Real.log DLMF.Gamma.glaisherKinkelin := by
  refine tendsto_nhds_unique ?_ tendsto_jLogJSum_sub
  have hT : Tendsto (fun n : ℕ => ∑ s ∈ Ico 2 m, sumMulLogTerm s n) atTop (𝓝 0) := by
    rw [← Finset.sum_const_zero (s := Ico 2 m) (M := ℝ)]
    refine tendsto_finsetSum _ fun s hs => ?_
    have hs2 : 2 ≤ s := (Finset.mem_Ico.1 hs).1
    unfold sumMulLogTerm
    exact tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by omega)).comp
      tendsto_natCast_atTop_atTop)
  have h := (tendsto_const_nhds (x := jLogJConst m)).add hT |>.add (tendsto_jLogJRemainder hm)
  rw [add_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [jLogJSum_eq_const hm hn]
  ring

/-- DLMF 2.10.4 (with 2.10.3, 2.10.5 and 2.10.6): for `m ≥ 2` and `n ≥ 1`,
`S(n) = ½n² ln n - ¼n² + ½n ln n + 1/12 ln n + C
  + ∑_{s=2}^{m-1} (-B_{2s})/(2s(2s-1)(2s-2)) n^{-(2s-2)} + R_m(n)`
with `C = ln A`, `A` the Glaisher–Kinkelin constant. -/
@[dlmf 2.10.E4, dlmf 2.10.E5]
theorem jLogJSum_eq {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n) :
    jLogJSum n = (n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 + n / 2 * Real.log n +
      Real.log n / 12 + Real.log DLMF.Gamma.glaisherKinkelin +
      ∑ s ∈ Ico 2 m, sumMulLogTerm s n + jLogJRemainder m n := by
  rw [jLogJSum_eq_const hm hn, jLogJConst_eq hm]

/-- `|B̃_{2m}(x)| ≤ |B_{2m}|` (DLMF 24.9.1). -/
private lemma abs_periodicBernoulli_two_mul_le {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    |periodicBernoulli (2 * m) x| ≤ |(bernoulli (2 * m) : ℝ)| := by
  rw [periodicBernoulli]
  rcases (Int.fract_nonneg x).eq_or_lt with h | h
  · rw [← h, bernoulliFun_eval_zero]
  · exact (DLMF.BernoulliEuler.abs_bernoulliFun_two_mul_lt hm h (Int.fract_lt_one x)).le

/-- `R_m(n)` has the sign of `-B_{2m}`. -/
private lemma jLogJRemainder_mul_neg_bernoulli_nonneg {m : ℕ} (hm : 2 ≤ m) (n : ℕ) :
    0 ≤ jLogJRemainder m n * -(bernoulli (2 * m) : ℝ) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  rw [jLogJRemainder, ← MeasureTheory.integral_mul_const]
  refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := lt_of_le_of_lt (Nat.cast_nonneg n) hx
  have hb := abs_periodicBernoulli_two_mul_le (m := m) (by omega) x
  have hden : 0 < (2 * m * (2 * m - 1) * x ^ (2 * m - 1) : ℝ) := by
    have : 0 < x ^ (2 * m - 1) := pow_pos hx0 _
    have : (0 : ℝ) < 2 * m * (2 * m - 1) := by nlinarith
    positivity
  rw [div_mul_eq_mul_div]
  refine div_nonneg ?_ hden.le
  set B : ℝ := (bernoulli (2 * m) : ℝ)
  set P : ℝ := periodicBernoulli (2 * m) x
  have h1 : P * B ≤ |P| * |B| := by rw [← abs_mul]; exact le_abs_self _
  have h2 : |P| * |B| ≤ |B| * |B| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have h3 : |B| * |B| = B * B := abs_mul_abs_self B
  nlinarith

/-- The `s = m` term of 2.10.4 is `-B_{2m}` times a positive number. -/
private lemma sumMulLogTerm_eq {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n) :
    ∃ p : ℝ, 0 < p ∧ sumMulLogTerm m n = -(bernoulli (2 * m) : ℝ) * p := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨1 / (2 * m * (2 * m - 1) * (2 * m - 2)) / (n : ℝ) ^ (2 * m - 2), ?_, ?_⟩
  · have : (0 : ℝ) < 2 * m * (2 * m - 1) * (2 * m - 2) := by
      have : (0 : ℝ) < 2 * m - 2 := by linarith
      have : (0 : ℝ) < 2 * m * (2 * m - 1) := by nlinarith
      positivity
    positivity
  · rw [sumMulLogTerm]; ring

/-- DLMF §2.10(i) (remainder of 2.10.4): since `B̃_{2m}(x) - B_{2m}` has constant sign
`(-1)^m`, `R_m(n)` has the sign of the `s = m` term of 2.10.4 and is bounded in absolute value
by it (`m ≥ 2`, `n ≥ 1`). -/
@[dlmf 2.10.i]
theorem jLogJRemainder_bound {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n) :
    0 ≤ jLogJRemainder m n * sumMulLogTerm m n ∧ |jLogJRemainder m n| ≤ |sumMulLogTerm m n| := by
  have hdiff : jLogJRemainder m n = sumMulLogTerm m n + jLogJRemainder (m + 1) n := by
    have h1 := jLogJSum_eq hm hn
    have h2 := jLogJSum_eq (m := m + 1) (by omega) hn
    rw [Finset.sum_Ico_succ_top (by omega)] at h2
    linarith
  obtain ⟨p, hp, hT⟩ := sumMulLogTerm_eq hm hn
  have hR := jLogJRemainder_mul_neg_bernoulli_nonneg hm n
  have hR' := jLogJRemainder_mul_neg_bernoulli_nonneg (m := m + 1) (by omega) n
  have hs1 := (DLMF.BernoulliEuler.bernoulli_two_mul_add_one_eq_zero_and_sign
    (n := m) (by omega)).2
  have hs2 := (DLMF.BernoulliEuler.bernoulli_two_mul_add_one_eq_zero_and_sign
    (n := m + 1) (by omega)).2
  have hs1' : (0 : ℝ) < (-1) ^ (m + 1) * (bernoulli (2 * m) : ℝ) := by exact_mod_cast hs1
  have hs2' : (0 : ℝ) < (-1) ^ (m + 1 + 1) * (bernoulli (2 * (m + 1)) : ℝ) := by
    exact_mod_cast hs2
  rw [pow_succ] at hs2'
  set u : ℝ := -(bernoulli (2 * m) : ℝ)
  set v : ℝ := -(bernoulli (2 * (m + 1)) : ℝ)
  set R := jLogJRemainder m n
  set R' := jLogJRemainder (m + 1) n
  rw [hT] at hdiff ⊢
  refine ⟨by nlinarith [mul_nonneg hR hp.le], ?_⟩
  rcases neg_one_pow_eq_or ℝ (m + 1) with h | h <;> rw [h] at hs1' hs2'
  · -- `B_{2m} > 0`, `u < 0`, `v > 0`
    have hu : u < 0 := by simp only [u]; linarith
    have hv : 0 < v := by simp only [v]; linarith
    have hR0 : R ≤ 0 := by nlinarith
    have hR'0 : 0 ≤ R' := by nlinarith
    rw [abs_of_nonpos hR0, abs_of_nonpos (by nlinarith)]
    linarith
  · have hu : 0 < u := by simp only [u]; linarith
    have hv : v < 0 := by simp only [v]; linarith
    have hR0 : 0 ≤ R := by nlinarith
    have hR'0 : R' ≤ 0 := by nlinarith
    rw [abs_of_nonneg hR0, abs_of_nonneg (by nlinarith)]
    linarith

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
  have hd := Gamma.Real.digamma_nat_add_one (n - 1)
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
    DLMF.AsymptoticApproximations.Real.invPowScale M =O[atTop]
        DLMF.AsymptoticApproximations.Real.invPowScale N := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [DLMF.AsymptoticApproximations.Real.invPowScale, Real.norm_eq_abs, abs_inv, abs_pow,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), one_mul]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hn' hNM)

/-- Pairing consecutive Bernoulli coefficients recovers the customary harmonic
polynomial with only even powers after the first term. -/
private theorem sum_harmonicCoeff_even (m n : ℕ) (hm : 1 ≤ m) :
    ∑ s ∈ range (2 * m), DLMF.AsymptoticApproximations.Real.invPowScale s n *
        harmonicAsymptoticCoeff s =
      -1 / (2 * n) - ∑ k ∈ Ico 1 m, (bernoulli (2 * k) : ℝ) / (2 * k) /
        (n : ℝ) ^ (2 * k) := by
  induction m, hm using Nat.le_induction with
  | base =>
    simp [DLMF.AsymptoticApproximations.Real.invPowScale, harmonicAsymptoticCoeff, sum_range_succ]
    ring
  | succ m hm ih =>
    have hodd : (bernoulli (2 * m + 1) : ℝ) = 0 := by
      rw [bernoulli_eq_zero_of_odd ⟨m, by omega⟩ (by omega)]
      simp
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, sum_range_succ,
      sum_range_succ, ih, sum_Ico_succ_top (by omega : 1 ≤ m)]
    simp only [DLMF.AsymptoticApproximations.Real.invPowScale, harmonicAsymptoticCoeff, show 2 *
        m ≠ 0 by omega,
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
    HasAsymptoticExpansion atTop DLMF.AsymptoticApproximations.Real.invPowScale
        harmonicAsymptoticCoeff
      (fun n : ℕ => (harmonic (n - 1) : ℝ) - Real.log n - Real.eulerMascheroniConstant) := by
  have hR (m : ℕ) (hm : 1 ≤ m) :
      (fun n : ℕ => (harmonic (n - 1) : ℝ) - Real.log n - Real.eulerMascheroniConstant -
        ∑ s ∈ range (2 * m), DLMF.AsymptoticApproximations.Real.invPowScale s n *
            harmonicAsymptoticCoeff s) =O[atTop]
        DLMF.AsymptoticApproximations.Real.invPowScale (2 * m) := by
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
          simp only [DLMF.AsymptoticApproximations.Real.invPowScale, Real.norm_eq_abs,
              abs_inv, abs_pow,
            abs_div, abs_neg, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
          ring
  intro N
  let M := 2 * (N + 1)
  have hNM : N ≤ M := by dsimp [M]; omega
  have hr := (hR (N + 1) (by omega)).trans (invScale_isBigO_of_le hNM)
  have htail : (fun n => ∑ s ∈ Ico N M, DLMF.AsymptoticApproximations.Real.invPowScale s n *
      harmonicAsymptoticCoeff s) =O[atTop]
      DLMF.AsymptoticApproximations.Real.invPowScale N := by
    have h := IsBigO.sum (s := Ico N M)
        (A := fun s n => DLMF.AsymptoticApproximations.Real.invPowScale s n *
            harmonicAsymptoticCoeff s)
      fun s hs => ((invScale_isBigO_of_le (mem_Ico.mp hs).1).const_mul_left
        (harmonicAsymptoticCoeff s)).congr_left (fun n => mul_comm _ _)
    exact h.congr_left fun n => by simp only [Finset.sum_apply]
  simp only [smul_eq_mul]
  refine (hr.add htail).congr_left fun n => ?_
  have hsum := sum_range_add_sum_Ico
      (fun s => DLMF.AsymptoticApproximations.Real.invPowScale s n * harmonicAsymptoticCoeff s) hNM
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
