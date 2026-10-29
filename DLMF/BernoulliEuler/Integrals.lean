/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Basic
public import DLMF.BernoulliEuler.GeneratingFunctions
public import DLMF.BernoulliEuler.Properties
public import ToMathlib.Analysis.SpecialFunctions.RamanujanMaster
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp

/-!
# Bernoulli and Euler numbers and polynomials: integral representations (DLMF §24.7)

The integrals over `(0, ∞)` are Lebesgue (Bochner) integrals `∫ t in Set.Ioi 0, …`; all
integrands are integrable on the stated ranges, so Lean's totalization of non-integrable
integrals to `0` plays no role. The polynomial representations 24.7.7–24.7.10 are stated for
complex `x` with `0 < Re x < 1` (DLMF §24.7(ii)); 24.7.7 for `n ≥ 1`, 24.7.8–24.7.10 for `n ≥ 0`.

The Mellin–Barnes representation 24.7.11 is proved by shifting the integration line to
`Re t = -1/2` and expanding against the moments of `sech²(πs)`. It holds for every complex `x`.
With `t = -c + is`, the contour normalization becomes
`(1/(2πi)) ∫ … dt = (1/(2π)) ∫_ℝ … ds`. The proof uses the vertical-line shift theorem from
lean-codes’ `ToMathlib.Analysis.MellinBarnes` and the sine lower bound from its
`ToMathlib.Analysis.SpecialFunctions.RamanujanMaster`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set Filter Topology
open scoped Real Nat

namespace DLMF.BernoulliEuler

/-! ### Helpers for §24.7(i) -/

/-- Mellin transforms of `∑ aᵢ e^{-pᵢ t}` at a positive integer `m + 1`, real form:
`∫₀^∞ tᵐ F(t) dt = ∑ m! aᵢ/pᵢ^{m+1}`. -/
lemma q24a_hasSum_integral_pow_mul {a p : ℕ → ℝ} {F : ℝ → ℝ} (m : ℕ)
    (hp : ∀ i, 0 < p i)
    (hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun i => a i * rexp (-p i * t)) (F t))
    (h_sum : Summable fun i => |a i| / p i ^ (m + 1)) :
    HasSum (fun i => (m ! : ℝ) * a i / p i ^ (m + 1)) (∫ t in Ioi (0 : ℝ), t ^ m * F t) := by
  have hs : 0 < ((m + 1 : ℕ) : ℂ).re := by simp; positivity
  have h := hasSum_mellin (a := fun i => (a i : ℂ)) (p := p) (F := fun t => (F t : ℂ))
    (s := ((m + 1 : ℕ) : ℂ)) (fun i => Or.inr (hp i)) hs
    (fun t ht => by
      have := (hF t ht)
      exact_mod_cast (Complex.hasSum_ofReal.mpr this))
    (by
      refine h_sum.congr fun i => ?_
      simp only [Complex.norm_real, Real.norm_eq_abs, Complex.natCast_re]
      rw [← Real.rpow_natCast])
  have hm : mellin (fun t => (F t : ℂ)) ((m + 1 : ℕ) : ℂ) =
      ((∫ t in Ioi (0 : ℝ), t ^ m * F t : ℝ) : ℂ) := by
    rw [mellin, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [smul_eq_mul]
    rw [show ((m + 1 : ℕ) : ℂ) - 1 = (m : ℂ) by push_cast; ring, Complex.cpow_natCast]
    push_cast; ring
  rw [hm] at h
  rw [← Complex.hasSum_ofReal]
  refine h.congr_fun fun i => ?_
  rw [Complex.cpow_natCast, Nat.cast_add, Nat.cast_one, Complex.Gamma_nat_eq_factorial]
  push_cast; ring

/-- `ζ(2n) = ∑_{k ≥ 0} 1/(k+1)^{2n}` in Bernoulli form. -/
lemma q24a_hasSum_zeta_succ {n : ℕ} (hn : n ≠ 0) :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (2 * n))
      ((-1 : ℝ) ^ (n + 1) * 2 ^ (2 * n - 1) * π ^ (2 * n) * bernoulli (2 * n) / (2 * n)!) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_zeta_nat hn)
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_pow (show 2 * n ≠ 0 by omega), div_zero,
    sub_zero, Nat.cast_add, Nat.cast_one] at h
  exact h

/-- The Dirichlet eta function from zeta: `∑ (-1)ᵏ/(k+1)ˢ = (1 - 2^{1-s}) ∑ 1/(k+1)ˢ`. -/
lemma q24a_hasSum_eta {s : ℕ} {Z : ℝ} (hZ : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) Z) :
    HasSum (fun k : ℕ => (-1) ^ k * (1 / ((k : ℝ) + 1) ^ s)) ((1 - 2 / 2 ^ s) * Z) := by
  set f : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) ^ s
  have ho : HasSum (fun k => f (2 * k + 1)) (Z / 2 ^ s) := by
    have := hZ.div_const (2 ^ s)
    refine this.congr_fun fun k => ?_
    simp only [f]; push_cast
    rw [show (2 * (k : ℝ) + 1 + 1) = 2 * (k + 1) by ring, mul_pow]; field_simp
  have hsum : Summable (fun k => f (2 * k)) :=
    hZ.summable.comp_injective (fun a b h => by simpa using h)
  have he : HasSum (fun k => f (2 * k)) (Z - Z / 2 ^ s) := by
    have h2 := (hsum.hasSum.even_add_odd ho).unique hZ
    convert hsum.hasSum using 1
    linarith
  have he' : HasSum (fun k => (-1 : ℝ) ^ (2 * k) * f (2 * k)) (Z - Z / 2 ^ s) :=
    he.congr_fun fun k => by simp [pow_mul]
  have ho' : HasSum (fun k => (-1 : ℝ) ^ (2 * k + 1) * f (2 * k + 1)) (-(Z / 2 ^ s)) :=
    ho.neg.congr_fun fun k => by rw [pow_succ, pow_mul]; norm_num
  have := HasSum.even_add_odd (f := fun k => (-1 : ℝ) ^ k * f k) he' ho'
  rw [show (1 - 2 / 2 ^ s) * Z = Z - Z / 2 ^ s + -(Z / 2 ^ s) by ring]
  exact this

/-- Summability of the indicated series: `Summable fun i : ℕ => (1 : ℝ) / (c * ((i : ℝ) + 1)) ^ (m
+ 2)`. -/
lemma q24a_summable_pow_succ (m : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable fun i : ℕ => (1 : ℝ) / (c * ((i : ℝ) + 1)) ^ (m + 2) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega : 1 < m + 2))
  refine (h.mul_left (1 / c ^ (m + 2))).congr fun i => ?_
  push_cast; rw [mul_pow]; field_simp

/-- `∫₀^∞ tᵐ/(e^{ct} - 1) dt = ∑_{i ≥ 0} m!/(c(i+1))^{m+1}`, `m ≥ 1`, `c > 0`. -/
lemma q24a_hasSum_integral_exp_sub_one (m : ℕ) {c : ℝ} (hc : 0 < c) :
    HasSum (fun i : ℕ => ((m + 1) ! : ℝ) * 1 / (c * ((i : ℝ) + 1)) ^ (m + 2))
      (∫ t in Ioi (0 : ℝ), t ^ (m + 1) * (1 / (rexp (c * t) - 1))) := by
  refine q24a_hasSum_integral_pow_mul (a := fun _ => 1) (p := fun i => c * ((i : ℝ) + 1)) (m + 1)
    (fun i => by positivity) (fun t ht => ?_) ?_
  · have ht' : 0 < t := ht
    set r := rexp (-(c * t))
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hct : 0 < c * t := mul_pos hc ht'
    have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
    have hval : r * (1 - r)⁻¹ = 1 / (rexp (c * t) - 1) := by
      have he : rexp (c * t) * r = 1 := by rw [← Real.exp_add]; simp
      have h1 : rexp (c * t) - 1 ≠ 0 := by
        have := Real.add_one_lt_exp (by nlinarith : c * t ≠ 0); linarith
      have h2 : 1 - r ≠ 0 := by linarith
      field_simp
      linear_combination he
    rw [hval] at h
    refine h.congr_fun fun i => ?_
    simp only [one_mul]
    rw [← pow_succ', ← Real.exp_nat_mul]; congr 1; push_cast; ring
  · refine (q24a_summable_pow_succ m hc).congr fun i => ?_
    simp

/-- `∫₀^∞ tᵐ/(e^{ct} + 1) dt = ∑_{i ≥ 0} (-1)ⁱ m!/(c(i+1))^{m+1}`, `m ≥ 1`, `c > 0`. -/
lemma q24a_hasSum_integral_exp_add_one (m : ℕ) {c : ℝ} (hc : 0 < c) :
    HasSum (fun i : ℕ => ((m + 1) ! : ℝ) * (-1) ^ i / (c * ((i : ℝ) + 1)) ^ (m + 2))
      (∫ t in Ioi (0 : ℝ), t ^ (m + 1) * (1 / (rexp (c * t) + 1))) := by
  refine q24a_hasSum_integral_pow_mul (a := fun i => (-1) ^ i) (p := fun i => c * ((i : ℝ) + 1))
    (m + 1) (fun i => by positivity) (fun t ht => ?_) ?_
  · have ht' : 0 < t := ht
    set r := rexp (-(c * t))
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hct : 0 < c * t := mul_pos hc ht'
    have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have h := (hasSum_geometric_of_abs_lt_one (r := -r)
      (by rw [abs_neg, abs_of_nonneg hr0]; exact hr1)).mul_left r
    have hval : r * (1 - -r)⁻¹ = 1 / (rexp (c * t) + 1) := by
      have he : rexp (c * t) * r = 1 := by rw [← Real.exp_add]; simp
      have h1 : rexp (c * t) + 1 ≠ 0 := by positivity
      have h2 : 1 - -r ≠ 0 := by linarith
      field_simp
      linear_combination he
    rw [hval] at h
    refine h.congr_fun fun i => ?_
    rw [show r * (-r) ^ i = (-1) ^ i * r ^ (i + 1) by rw [neg_pow]; ring, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  · refine (q24a_summable_pow_succ m hc).congr fun i => ?_
    simp

/-- The Bose integral `∫₀^∞ t^{2m+1}/(e^{2πt} - 1) dt = (-1)^m B_{2m+2}/(4(m+1))`. -/
lemma q24a_integral_exp_sub_one_bernoulli (m : ℕ) :
    ∫ t in Ioi (0 : ℝ), t ^ (2 * m + 1) / (rexp (2 * π * t) - 1) =
      (-1) ^ m * (bernoulli (2 * (m + 1)) : ℝ) / (4 * (m + 1)) := by
  have h := q24a_hasSum_integral_exp_sub_one (2 * m) (c := 2 * π) (by positivity)
  simp only [mul_one_div] at h
  have hz := (q24a_hasSum_zeta_succ (n := m + 1) (by omega)).mul_left
    (((2 * m + 1) ! : ℝ) / (2 * π) ^ (2 * m + 2))
  have heq := h.unique (hz.congr_fun fun i => by
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, mul_pow]; field_simp)
  rw [heq, show 2 * (m + 1) - 1 = 2 * m + 1 by omega, show 2 * (m + 1) = 2 * m + 2 by ring,
    Nat.factorial_succ (2 * m + 1), mul_pow, pow_succ (-1 : ℝ) (m + 1), pow_succ (-1 : ℝ) m]
  push_cast
  rw [show (2 : ℝ) ^ (2 * m + 2) = 2 * 2 ^ (2 * m + 1) by ring]
  have hpi : π ^ (2 * m + 2) ≠ 0 := pow_ne_zero _ pi_pos.ne'
  have h2 : (2 : ℝ) ^ (2 * m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hf : ((2 * m + 1)! : ℝ) ≠ 0 := by positivity
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- `∫₀^∞ t^{2m+1}/(e^{2πt} + 1) dt = (1 - 2^{-(2m+1)}) (-1)^m B_{2m+2}/(4(m+1))`. -/
lemma q24a_integral_exp_add_one_bernoulli (m : ℕ) :
    ∫ t in Ioi (0 : ℝ), t ^ (2 * m + 1) / (rexp (2 * π * t) + 1) =
      (1 - 2 / 2 ^ (2 * m + 2)) * ((-1) ^ m * (bernoulli (2 * (m + 1)) : ℝ) / (4 * (m + 1))) := by
  have h := q24a_hasSum_integral_exp_add_one (2 * m) (c := 2 * π) (by positivity)
  simp only [mul_one_div] at h
  have hz0 := q24a_hasSum_zeta_succ (n := m + 1) (by omega)
  rw [show 2 * (m + 1) = 2 * m + 2 by ring] at hz0
  have hz := (q24a_hasSum_eta hz0).mul_left (((2 * m + 1) ! : ℝ) / (2 * π) ^ (2 * m + 2))
  have heq := h.unique (hz.congr_fun fun i => by rw [mul_pow]; field_simp)
  have hb := q24a_integral_exp_sub_one_bernoulli m
  have h' := q24a_hasSum_integral_exp_sub_one (2 * m) (c := 2 * π) (by positivity)
  simp only [mul_one_div] at h'
  have heq' := h'.unique ((hz0.mul_left (((2 * m + 1) ! : ℝ) / (2 * π) ^ (2 * m + 2))).congr_fun
    fun i => by rw [mul_pow]; field_simp)
  rw [heq, ← hb, heq']
  ring

/-- At `t`, the function `(fun t => 2 / π * arctan (rexp (π * t)))` has derivative `(1 / cosh (π *
t))`. -/
lemma q24a_hasDerivAt_arctan_exp (t : ℝ) :
    HasDerivAt (fun t => 2 / π * arctan (rexp (π * t))) (1 / cosh (π * t)) t := by
  have h1 : HasDerivAt (fun t => rexp (π * t)) (rexp (π * t) * π) t := by
    have := ((hasDerivAt_id t).const_mul π).exp
    simpa using this
  have h2 := (h1.arctan).const_mul (2 / π)
  convert h2 using 1
  rw [Real.cosh_eq, Real.exp_neg]
  have he : rexp (π * t) ≠ 0 := (Real.exp_pos _).ne'
  have hp : π ≠ 0 := pi_ne_zero
  have h3 : 1 + rexp (π * t) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `∫ t in Ioi (0 : ℝ), 1 / cosh (π *
t) = 1 / 2`. -/
lemma q24a_integral_sech : ∫ t in Ioi (0 : ℝ), 1 / cosh (π * t) = 1 / 2 := by
  have hlim : Tendsto (fun t => 2 / π * arctan (rexp (π * t))) atTop (𝓝 (2 / π * (π / 2))) := by
    refine Tendsto.const_mul _ ?_
    exact (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop pi_pos))
  have hint : IntegrableOn (fun t => 1 / cosh (π * t)) (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun t _ => q24a_hasDerivAt_arctan_exp t)
      (fun t _ => by positivity) hlim
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => q24a_hasDerivAt_arctan_exp t) hint hlim]
  simp only [mul_zero, Real.exp_zero, Real.arctan_one]
  field_simp; ring

/-! ### §24.7(i) Bernoulli and Euler numbers -/

/-- **DLMF 24.7.1**: `B₂ₙ = (-1)ⁿ⁺¹ 4n/(1 - 2^{1-2n}) ∫₀^∞ t^{2n-1}/(e^{2πt} + 1) dt
= (-1)ⁿ⁺¹ 2n/(1 - 2^{1-2n}) ∫₀^∞ t^{2n-1} e^{-πt} sech(πt) dt`, `n ≥ 1`. -/
@[dlmf 24.7.E1]
theorem bernoulli_two_mul_eq_integral_exp_add_one {n : ℕ} (hn : 1 ≤ n) :
    (bernoulli (2 * n) : ℝ) = (-1) ^ (n + 1) * (4 * n) / (1 - (2 : ℝ) ^ (1 - 2 * (n : ℤ))) *
        ∫ t in Set.Ioi (0 : ℝ), t ^ (2 * n - 1) / (exp (2 * π * t) + 1) ∧
      (bernoulli (2 * n) : ℝ) = (-1) ^ (n + 1) * (2 * n) / (1 - (2 : ℝ) ^ (1 - 2 * (n : ℤ))) *
        ∫ t in Set.Ioi (0 : ℝ), t ^ (2 * n - 1) * exp (-(π * t)) / cosh (π * t) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hI := q24a_integral_exp_add_one_bernoulli m
  have hI2 : ∫ t in Ioi (0 : ℝ), t ^ (2 * (m + 1) - 1) * exp (-(π * t)) / cosh (π * t) =
      2 * ∫ t in Ioi (0 : ℝ), t ^ (2 * (m + 1) - 1) / (exp (2 * π * t) + 1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [Real.cosh_eq, show 2 * π * t = π * t + π * t by ring, Real.exp_add]
    have h1 : rexp (π * t) * rexp (-(π * t)) = 1 := by rw [← Real.exp_add]; simp
    have h2 : rexp (π * t) + rexp (-(π * t)) ≠ 0 := by positivity
    have h3 : rexp (π * t) * rexp (π * t) + 1 ≠ 0 := by positivity
    rw [Real.exp_neg] at h2 ⊢
    have h4 : rexp (π * t) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
  rw [hI2, show 2 * (m + 1) - 1 = 2 * m + 1 by omega, hI]
  have hz : (2 : ℝ) ^ (1 - 2 * ((m + 1 : ℕ) : ℤ)) = 2 / 2 ^ (2 * m + 2) := by
    rw [zpow_sub₀ (by norm_num), zpow_one]; push_cast
    rw [show (2 : ℤ) * ((m : ℤ) + 1) = ((2 * m + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [hz]
  have hne : (1 - 2 / (2 : ℝ) ^ (2 * m + 2)) ≠ 0 := by
    have : (2 : ℝ) / 2 ^ (2 * m + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ < 2 ^ (2 * m + 2) := pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have hs : ((-1 : ℝ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [pow_succ, pow_succ]
  generalize (-1 : ℝ) ^ m = σ at hs ⊢
  generalize (2 : ℝ) ^ (2 * m + 2) = x at hne ⊢
  generalize (bernoulli (2 * (m + 1)) : ℝ) = B
  push_cast
  constructor
  · field_simp
    ring_nf; rw [hs]; ring
  · field_simp
    ring_nf; rw [hs]; ring

/-- **DLMF 24.7.2**: `B₂ₙ = (-1)ⁿ⁺¹ 4n ∫₀^∞ t^{2n-1}/(e^{2πt} - 1) dt
= (-1)ⁿ⁺¹ 2n ∫₀^∞ t^{2n-1} e^{-πt} csch(πt) dt`, `n ≥ 1`. -/
@[dlmf 24.7.E2]
theorem bernoulli_two_mul_eq_integral_exp_sub_one {n : ℕ} (hn : 1 ≤ n) :
    (bernoulli (2 * n) : ℝ) = (-1) ^ (n + 1) * (4 * n) *
        ∫ t in Set.Ioi (0 : ℝ), t ^ (2 * n - 1) / (exp (2 * π * t) - 1) ∧
      (bernoulli (2 * n) : ℝ) = (-1) ^ (n + 1) * (2 * n) *
        ∫ t in Set.Ioi (0 : ℝ), t ^ (2 * n - 1) * exp (-(π * t)) / sinh (π * t) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hI := q24a_integral_exp_sub_one_bernoulli m
  have hI2 : ∫ t in Ioi (0 : ℝ), t ^ (2 * (m + 1) - 1) * exp (-(π * t)) / sinh (π * t) =
      2 * ∫ t in Ioi (0 : ℝ), t ^ (2 * (m + 1) - 1) / (exp (2 * π * t) - 1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : 0 < π * t := mul_pos pi_pos ht
    rw [Real.sinh_eq, show 2 * π * t = π * t + π * t by ring, Real.exp_add]
    have h1 : rexp (π * t) * rexp (-(π * t)) = 1 := by rw [← Real.exp_add]; simp
    have hlt : rexp (-(π * t)) < rexp (π * t) := Real.exp_lt_exp.mpr (by linarith)
    have h2 : rexp (π * t) - rexp (-(π * t)) ≠ 0 := by linarith
    have h3 : rexp (π * t) * rexp (π * t) - 1 ≠ 0 := by
      have : 1 < rexp (π * t) := Real.one_lt_exp_iff.mpr ht'
      nlinarith
    rw [Real.exp_neg] at h2 ⊢
    have h4 : rexp (π * t) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
  rw [hI2, show 2 * (m + 1) - 1 = 2 * m + 1 by omega, hI]
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have hs : ((-1 : ℝ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [pow_succ, pow_succ]
  generalize (-1 : ℝ) ^ m = σ at hs ⊢
  generalize (bernoulli (2 * (m + 1)) : ℝ) = B
  push_cast
  constructor
  · field_simp
    ring_nf; rw [hs]; ring
  · field_simp
    ring_nf; rw [hs]; ring

/-- `csch²(πt) = ∑_{i≥0} 4(i+1) e^{-2π(i+1)t}` for `t > 0`. -/
lemma r24a_hasSum_csch_sq {t : ℝ} (ht : 0 < t) :
    HasSum (fun i : ℕ => (4 * ((i : ℝ) + 1)) * rexp (-(2 * π * ((i : ℝ) + 1)) * t))
      (1 / sinh (π * t) ^ 2) := by
  set r := rexp (-(2 * π * t))
  have hr0 : 0 < r := exp_pos _
  have hr1 : r < 1 := exp_lt_one_iff.mpr (by nlinarith [pi_pos])
  have h := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := r)
    (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
  have h' := ((hasSum_nat_add_iff' 1).mpr h).mul_left 4
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero] at h'
  have hval : 4 * (r / (1 - r) ^ 2) = 1 / sinh (π * t) ^ 2 := by
    have hs : sinh (π * t) = (rexp (π * t) - rexp (-(π * t))) / 2 := sinh_eq _
    have he : r = rexp (-(π * t)) ^ 2 := by
      show rexp (-(2 * π * t)) = _
      rw [← exp_nat_mul]; congr 1; push_cast; ring
    have he2 : rexp (π * t) * rexp (-(π * t)) = 1 := by rw [← exp_add]; simp
    have hne : rexp (π * t) - rexp (-(π * t)) ≠ 0 := by
      have : rexp (-(π * t)) < rexp (π * t) := exp_lt_exp.mpr (by nlinarith [pi_pos])
      linarith
    have h1r : 1 - r ≠ 0 := by linarith
    rw [hs, he]
    rw [he] at h1r
    field_simp
    have : rexp (π * t) = 1 / rexp (-(π * t)) := by field_simp; linarith
    rw [this]
    have : rexp (-(π * t)) ≠ 0 := (exp_pos _).ne'
    field_simp
    ring
  rw [hval] at h'
  refine h'.congr_fun fun i => ?_
  push_cast
  rw [show -(2 * π * ((i : ℝ) + 1)) * t = ((i + 1 : ℕ) : ℝ) * (-(2 * π * t)) by push_cast; ring,
    exp_nat_mul, mul_assoc]

/-- `sech²(πt) = ∑_{i≥0} 4(-1)ⁱ(i+1) e^{-2π(i+1)t}` for `t > 0`. -/
lemma r24a_hasSum_sech_sq {t : ℝ} (ht : 0 < t) :
    HasSum (fun i : ℕ => (4 * (-1) ^ i * ((i : ℝ) + 1)) * rexp (-(2 * π * ((i : ℝ) + 1)) * t))
      (1 / cosh (π * t) ^ 2) := by
  set r := rexp (-(2 * π * t))
  have hr0 : 0 < r := exp_pos _
  have hr1 : r < 1 := exp_lt_one_iff.mpr (by nlinarith [pi_pos])
  have h := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := -r)
    (by rw [Real.norm_eq_abs, abs_neg, abs_of_pos hr0]; exact hr1)
  have h' := ((hasSum_nat_add_iff' 1).mpr h).mul_left (-4)
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero] at h'
  have hval : -4 * (-r / (1 - -r) ^ 2) = 1 / cosh (π * t) ^ 2 := by
    have hs : cosh (π * t) = (rexp (π * t) + rexp (-(π * t))) / 2 := cosh_eq _
    have he : r = rexp (-(π * t)) ^ 2 := by
      show rexp (-(2 * π * t)) = _
      rw [← exp_nat_mul]; congr 1; push_cast; ring
    have he2 : rexp (π * t) = 1 / rexp (-(π * t)) := by
      rw [eq_div_iff (exp_pos _).ne', ← exp_add]; simp
    have h1r : 1 + r ≠ 0 := by linarith
    rw [sub_neg_eq_add, hs, he, he2]
    rw [he] at h1r
    have : rexp (-(π * t)) ≠ 0 := (exp_pos _).ne'
    field_simp
    ring
  rw [hval] at h'
  refine h'.congr_fun fun i => ?_
  push_cast
  rw [show -(2 * π * ((i : ℝ) + 1)) * t = ((i + 1 : ℕ) : ℝ) * (-(2 * π * t)) by push_cast; ring,
    exp_nat_mul]
  show _ = -4 * (((i : ℝ) + 1) * (-rexp (-(2 * π * t))) ^ (i + 1))
  rw [neg_pow (rexp _), pow_succ (-1 : ℝ) i]
  ring

/-- `log(1 - e^{-2πt}) = ∑_{i≥0} (-1/(i+1)) e^{-2π(i+1)t}` for `t > 0`. -/
lemma r24a_hasSum_log_one_sub_exp {t : ℝ} (ht : 0 < t) :
    HasSum (fun i : ℕ => (-(1 / ((i : ℝ) + 1))) * rexp (-(2 * π * ((i : ℝ) + 1)) * t))
      (log (1 - rexp (-(2 * π * t)))) := by
  set r := rexp (-(2 * π * t))
  have hr0 : 0 < r := exp_pos _
  have hr1 : r < 1 := exp_lt_one_iff.mpr (by nlinarith [pi_pos])
  have h := (hasSum_pow_div_log_of_abs_lt_one (x := r) (by rw [abs_of_pos hr0]; exact hr1)).neg
  rw [neg_neg] at h
  refine h.congr_fun fun i => ?_
  rw [show -(2 * π * ((i : ℝ) + 1)) * t = ((i + 1 : ℕ) : ℝ) * (-(2 * π * t)) by push_cast; ring,
    exp_nat_mul]
  ring

/-- **DLMF 24.7.3**: `B₂ₙ = (-1)ⁿ⁺¹ π/(1 - 2^{1-2n}) ∫₀^∞ t^{2n} sech²(πt) dt`, `n ≥ 1`. -/
@[dlmf 24.7.E3]
theorem bernoulli_two_mul_eq_integral_sech_sq {n : ℕ} (hn : 1 ≤ n) :
    (bernoulli (2 * n) : ℝ) = (-1) ^ (n + 1) * π / (1 - (2 : ℝ) ^ (1 - 2 * (n : ℤ))) *
      ∫ t in Set.Ioi (0 : ℝ), t ^ (2 * n) / cosh (π * t) ^ 2 := by
  have h := q24a_hasSum_integral_pow_mul (a := fun i : ℕ => 4 * (-1) ^ i * ((i : ℝ) + 1))
    (p := fun i : ℕ => 2 * π * ((i : ℝ) + 1)) (F := fun t => 1 / cosh (π * t) ^ 2) (2 * n)
    (fun i => by positivity) (fun t ht => r24a_hasSum_sech_sq ht) ?_
  · have hz0 := q24a_hasSum_zeta_succ (n := n) (by omega)
    have hz := (q24a_hasSum_eta hz0).mul_left (4 * ((2 * n) ! : ℝ) / (2 * π) ^ (2 * n + 1))
    have heq := h.unique (hz.congr_fun fun i => by
      rw [mul_pow, pow_succ ((i : ℝ) + 1)]
      have : (i : ℝ) + 1 ≠ 0 := by positivity
      field_simp)
    simp only [mul_one_div] at heq
    rw [heq]
    have hzp : (2 : ℝ) ^ (1 - 2 * (n : ℤ)) = 2 / 2 ^ (2 * n) := by
      rw [zpow_sub₀ (by norm_num), zpow_one]; norm_cast
    have hq : 2 / (2 : ℝ) ^ (2 * n) < 1 := by
      rw [div_lt_one (by positivity)]
      calc (2 : ℝ) < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [hzp]
    have hq' : 1 - 2 / (2 : ℝ) ^ (2 * n) ≠ 0 := by linarith
    have h1 : (-1 : ℝ) ^ (n * 2) = 1 := by rw [mul_comm, pow_mul]; norm_num
    have e2 : (2 : ℝ) ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [show (2 * π) ^ (2 * n + 1) = 2 * π * (2 * π) ^ (2 * n) by ring, mul_pow, e2]
    have h1' : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hne : (2 : ℝ) ^ (2 * n - 1) - 1 ≠ 0 := by
      have : (2 : ℝ) ^ 1 ≤ 2 ^ (2 * n - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    field_simp
    rw [h1']
    field_simp
    ring
  · refine ((q24a_hasSum_zeta_succ (n := n) (by omega)).summable.mul_left
      (4 / (2 * π) ^ (2 * n + 1))).congr fun i => ?_
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_of_pos (by positivity),
      abs_of_pos (by positivity), mul_pow (2 * π), pow_succ ((i : ℝ) + 1)]
    have : (i : ℝ) + 1 ≠ 0 := by positivity
    field_simp

/-- **DLMF 24.7.4**: `B₂ₙ = (-1)ⁿ⁺¹ π ∫₀^∞ t^{2n} csch²(πt) dt`, `n ≥ 1`. -/
@[dlmf 24.7.E4]
theorem bernoulli_two_mul_eq_integral_csch_sq {n : ℕ} (hn : 1 ≤ n) :
    (bernoulli (2 * n) : ℝ) = (-1) ^ (n + 1) * π *
      ∫ t in Set.Ioi (0 : ℝ), t ^ (2 * n) / sinh (π * t) ^ 2 := by
  have h := q24a_hasSum_integral_pow_mul (a := fun i : ℕ => 4 * ((i : ℝ) + 1))
    (p := fun i : ℕ => 2 * π * ((i : ℝ) + 1)) (F := fun t => 1 / sinh (π * t) ^ 2) (2 * n)
    (fun i => by positivity) (fun t ht => r24a_hasSum_csch_sq ht) ?_
  · have hz := (q24a_hasSum_zeta_succ (n := n) (by omega)).mul_left
      (4 * ((2 * n) ! : ℝ) / (2 * π) ^ (2 * n + 1))
    have heq := h.unique (hz.congr_fun fun i => by
      rw [mul_pow, pow_succ ((i : ℝ) + 1)]
      have : (i : ℝ) + 1 ≠ 0 := by positivity
      field_simp)
    simp only [mul_one_div] at heq
    rw [heq]
    have h1 : (-1 : ℝ) ^ (n * 2) = 1 := by rw [mul_comm, pow_mul]; norm_num
    have e2 : (2 : ℝ) ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [mul_pow, pow_succ, pow_succ, e2]
    field_simp
    linear_combination (-(4 * (bernoulli (2 * n) : ℝ) * π * π ^ (n * 2))) * h1
  · refine ((q24a_hasSum_zeta_succ (n := n) (by omega)).summable.mul_left
      (4 / (2 * π) ^ (2 * n + 1))).congr fun i => ?_
    rw [abs_of_pos (by positivity), mul_pow (2 * π), pow_succ ((i : ℝ) + 1)]
    have : (i : ℝ) + 1 ≠ 0 := by positivity
    field_simp

/-- **DLMF 24.7.5**: `B₂ₙ = (-1)ⁿ 2n(2n-1)/π ∫₀^∞ t^{2n-2} ln(1 - e^{-2πt}) dt`, `n ≥ 1`. -/
@[dlmf 24.7.E5]
theorem bernoulli_two_mul_eq_integral_log {n : ℕ} (hn : 1 ≤ n) :
    (bernoulli (2 * n) : ℝ) = (-1) ^ n * (2 * n * (2 * n - 1)) / π *
      ∫ t in Set.Ioi (0 : ℝ), t ^ (2 * n - 2) * log (1 - exp (-(2 * π * t))) := by
  have h := q24a_hasSum_integral_pow_mul (a := fun i : ℕ => -(1 / ((i : ℝ) + 1)))
    (p := fun i : ℕ => 2 * π * ((i : ℝ) + 1)) (F := fun t => log (1 - exp (-(2 * π * t))))
    (2 * n - 2) (fun i => by positivity) (fun t ht => r24a_hasSum_log_one_sub_exp ht) ?_
  · have hz0 := q24a_hasSum_zeta_succ (n := n) (by omega)
    have hz := (hz0.mul_left (-(((2 * n - 2) ! : ℝ)) / (2 * π) ^ (2 * n - 1)))
    have heq := h.unique (hz.congr_fun fun i => by
      have e : ((i : ℝ) + 1) ^ (2 * n) = ((i : ℝ) + 1) ^ (2 * n - 1) * ((i : ℝ) + 1) := by
        rw [← pow_succ]; congr 1; omega
      rw [show 2 * n - 2 + 1 = 2 * n - 1 by omega, mul_pow, e]
      have : (i : ℝ) + 1 ≠ 0 := by positivity
      field_simp)
    rw [heq]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [show 2 * (k + 1) - 2 = 2 * k by omega, show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
      show 2 * (k + 1) = 2 * k + 2 by ring, Nat.factorial_succ (2 * k + 1),
      Nat.factorial_succ (2 * k)]
    push_cast
    rw [mul_pow, pow_succ π (2 * k + 1), pow_succ (-1 : ℝ) (k + 1)]
    have hk : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have hk' : (2 * (k : ℝ) + 1 + 1) ≠ 0 := by positivity
    rcases neg_one_pow_eq_or ℝ (k + 1) with h | h <;> rw [h] <;> field_simp <;> ring
  · refine ((q24a_hasSum_zeta_succ (n := n) (by omega)).summable.mul_left
      (1 / (2 * π) ^ (2 * n - 1))).congr fun i => ?_
    have e : ((i : ℝ) + 1) ^ (2 * n) = ((i : ℝ) + 1) ^ (2 * n - 1) * ((i : ℝ) + 1) := by
      rw [← pow_succ]; congr 1; omega
    rw [abs_neg, abs_of_pos (by positivity), show 2 * n - 2 + 1 = 2 * n - 1 by omega,
      mul_pow (2 * π), e]
    have : (i : ℝ) + 1 ≠ 0 := by positivity
    field_simp

/-- **DLMF 24.7.6**: `E₂ₙ = (-1)ⁿ 2^{2n+1} ∫₀^∞ t^{2n} sech(πt) dt`, `n ≥ 0`. -/
@[dlmf 24.7.E6]
theorem eulerNumber_two_mul_eq_integral_sech (n : ℕ) :
    (eulerNumber (2 * n) : ℝ) = (-1) ^ n * 2 ^ (2 * n + 1) *
      ∫ t in Set.Ioi (0 : ℝ), t ^ (2 * n) / cosh (π * t) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [mul_zero, pow_zero, one_mul, zero_add, pow_one]
    rw [q24a_integral_sech]; simp
  have hβ := q24a_hasSum_alt_odd_eulerNumber (k := n) hn.ne'
  have h := q24a_hasSum_integral_pow_mul (a := fun i => 2 * (-1) ^ i)
    (p := fun i => (2 * (i : ℝ) + 1) * π) (F := fun t => 1 / cosh (π * t)) (2 * n)
    (fun i => by positivity) (fun t ht => ?_) ?_
  · have h2 := (hβ.mul_left (((2 * n) ! : ℝ) * 2 / π ^ (2 * n + 1)))
    have heq := h.unique (h2.congr_fun fun i => by rw [mul_pow]; field_simp)
    have hI : ∫ t in Ioi (0 : ℝ), t ^ (2 * n) / cosh (π * t) =
        ∫ t in Ioi (0 : ℝ), t ^ (2 * n) * (1 / cosh (π * t)) := by
      congr 1; ext t; ring
    rw [hI, heq]
    have hp : π ≠ 0 := pi_ne_zero
    have hf : ((2 * n) ! : ℝ) ≠ 0 := by positivity
    have hs : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    rw [show (4 : ℝ) ^ (n + 1) = 2 ^ (2 * n + 1) * 2 by
      rw [pow_succ, pow_succ, pow_mul]; norm_num; ring]
    generalize (-1 : ℝ) ^ n = σ at hs ⊢
    field_simp
    ring_nf; rw [hs]; ring
  · have ht' : 0 < t := ht
    set r := rexp (-(π * t))
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hct : 0 < π * t := mul_pos pi_pos ht'
    have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hr2 : r ^ 2 < 1 := by nlinarith
    have hg := (hasSum_geometric_of_abs_lt_one (r := -r ^ 2)
      (by rw [abs_neg, abs_of_nonneg (by positivity)]; exact hr2)).mul_left (2 * r)
    have hval : 2 * r * (1 - -r ^ 2)⁻¹ = 1 / cosh (π * t) := by
      have he : rexp (π * t) * r = 1 := by rw [← Real.exp_add]; simp
      rw [Real.cosh_eq]
      have h1 : rexp (π * t) + rexp (-(π * t)) ≠ 0 := by positivity
      have h2 : 1 - -r ^ 2 ≠ 0 := by nlinarith [sq_nonneg r]
      field_simp
      linear_combination he
    rw [hval] at hg
    refine hg.congr_fun fun i => ?_
    rw [show 2 * r * (-r ^ 2) ^ i = 2 * (-1) ^ i * r ^ (2 * i + 1) by rw [neg_pow, ← pow_mul]; ring,
      ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  · have hs := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2 * n + 1))
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      (hs.mul_left (2 / π ^ (2 * n + 1)))
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_two]
    rw [mul_pow]
    push_cast
    have hp : 0 < π ^ (2 * n + 1) := by positivity
    have h1 : ((i : ℝ) + 1) ^ (2 * n + 1) ≤ (2 * i + 1) ^ (2 * n + 1) := by
      gcongr; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [pow_pos (by positivity : (0:ℝ) < i + 1) (2 * n + 1)]

/-! ### §24.7(ii) Bernoulli and Euler polynomials -/

/-- **DLMF 24.7.7**: for `0 < Re x < 1` and `n ≥ 1`, `B₂ₙ(x) = (-1)ⁿ⁺¹ 2n
∫₀^∞ (cos 2πx - e^{-2πt})/(cosh 2πt - cos 2πx) t^{2n-1} dt`. -/
@[dlmf 24.7.E7]
theorem bernoulliPolyB_two_mul_eq_integral {n : ℕ} (hn : 1 ≤ n) {x : ℂ} (hx0 : 0 < x.re)
    (hx1 : x.re < 1) :
    bernoulliPolyB (2 * n) x = (-1) ^ (n + 1) * (2 * n) *
      ∫ t in Set.Ioi (0 : ℝ), (Complex.cos (2 * π * x) - Complex.exp (-(2 * π * t))) /
        (Complex.cosh (2 * π * t) - Complex.cos (2 * π * x)) * (t : ℂ) ^ (2 * n - 1) := by
  sorry

/-- **DLMF 24.7.8**: for `0 < Re x < 1`, `B₂ₙ₊₁(x) = (-1)ⁿ⁺¹ (2n+1)
∫₀^∞ sin(2πx)/(cosh 2πt - cos 2πx) t^{2n} dt`. -/
@[dlmf 24.7.E8]
theorem bernoulliPolyB_two_mul_add_one_eq_integral (n : ℕ) {x : ℂ} (hx0 : 0 < x.re)
    (hx1 : x.re < 1) :
    bernoulliPolyB (2 * n + 1) x = (-1) ^ (n + 1) * (2 * n + 1) *
      ∫ t in Set.Ioi (0 : ℝ), Complex.sin (2 * π * x) /
        (Complex.cosh (2 * π * t) - Complex.cos (2 * π * x)) * (t : ℂ) ^ (2 * n) := by
  sorry

/-- **DLMF 24.7.9**: for `0 < Re x < 1`, `E₂ₙ(x) = (-1)ⁿ 4
∫₀^∞ sin(πx) cosh(πt)/(cosh 2πt - cos 2πx) t^{2n} dt`. -/
@[dlmf 24.7.E9]
theorem eulerPolyE_two_mul_eq_integral (n : ℕ) {x : ℂ} (hx0 : 0 < x.re) (hx1 : x.re < 1) :
    eulerPolyE (2 * n) x = (-1) ^ n * 4 *
      ∫ t in Set.Ioi (0 : ℝ), Complex.sin (π * x) * Complex.cosh (π * t) /
        (Complex.cosh (2 * π * t) - Complex.cos (2 * π * x)) * (t : ℂ) ^ (2 * n) := by
  sorry

/-- **DLMF 24.7.10**: for `0 < Re x < 1`, `E₂ₙ₊₁(x) = (-1)ⁿ⁺¹ 4
∫₀^∞ cos(πx) sinh(πt)/(cosh 2πt - cos 2πx) t^{2n+1} dt`. -/
@[dlmf 24.7.E10]
theorem eulerPolyE_two_mul_add_one_eq_integral (n : ℕ) {x : ℂ} (hx0 : 0 < x.re)
    (hx1 : x.re < 1) :
    eulerPolyE (2 * n + 1) x = (-1) ^ (n + 1) * 4 *
      ∫ t in Set.Ioi (0 : ℝ), Complex.cos (π * x) * Complex.sinh (π * t) /
        (Complex.cosh (2 * π * t) - Complex.cos (2 * π * x)) * (t : ℂ) ^ (2 * n + 1) := by
  sorry

/-! ### Mellin–Barnes representation -/

/-- The sine denominator of the Bernoulli Mellin–Barnes kernel has no zeros in the strip
`-1 < Re z < 0`. -/
private lemma bernoulli_mellinBarnes_sin_ne_zero {z : ℂ} (hz0 : -1 < z.re) (hz1 : z.re < 0) :
    Complex.sin ((π : ℂ) * z) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have hr := congrArg Complex.re hk
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.intCast_re, Complex.intCast_im, mul_zero] at hr
  have hk0 : k < 0 := by exact_mod_cast (show (k : ℝ) < 0 by nlinarith [pi_pos])
  have hk1 : -1 < k := by exact_mod_cast (show (-1 : ℝ) < k by nlinarith [pi_pos])
  omega

/-- The polynomial Mellin–Barnes kernel is holomorphic between its two neighboring pole lines. -/
private lemma bernoulli_mellinBarnes_differentiable (n : ℕ) (x : ℂ) {z : ℂ}
    (hz0 : -1 < z.re) (hz1 : z.re < 0) :
    DifferentiableAt ℂ (fun z => (x + z) ^ n * ((π : ℂ) / Complex.sin (π * z)) ^ 2) z := by
  have hs := bernoulli_mellinBarnes_sin_ne_zero hz0 hz1
  fun_prop

/-- The real sine factor stays uniformly away from zero on a closed subinterval of `(-1, 0)`. -/
private lemma bernoulli_mellinBarnes_sin_strip_lower {a b : ℝ}
    (ha : -1 < a) (hb : b < 0) (hab : a ≤ b) :
    ∃ m > (0 : ℝ), ∀ σ ∈ Icc a b, m ≤ |sin (π * σ)| := by
  obtain ⟨σ, hσ, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab)
    (by fun_prop : ContinuousOn (fun σ : ℝ => |sin (π * σ)|) (Icc a b))
  refine ⟨|sin (π * σ)|, abs_pos.mpr ?_, fun t ht => hmin ht⟩
  apply ne_of_lt
  exact Real.sin_neg_of_neg_of_neg_pi_lt (mul_neg_of_pos_of_neg pi_pos (lt_of_le_of_lt hσ.2 hb))
    (by nlinarith [pi_pos, hσ.1])

/-- On a closed substrip of `-1 < Re z < 0`, the polynomial Mellin–Barnes kernel has an
integrable bound of order `(1 + |Im z|)⁻²`. Exponential sine growth absorbs any polynomial
degree. -/
private lemma bernoulli_mellinBarnes_tail_bound (n : ℕ) (x : ℂ) {a b : ℝ}
    (ha : -1 < a) (hb : b < 0) (hab : a ≤ b) :
    ∃ C T : ℝ, ∀ σ t : ℝ, a ≤ σ → σ ≤ b → T ≤ |t| →
      ‖(x + (σ + t * Complex.I)) ^ n *
        ((π : ℂ) / Complex.sin (π * (σ + t * Complex.I))) ^ 2‖ ≤
          C * (1 + |t|) ^ (-2 : ℝ) := by
  obtain ⟨m, hm, hml⟩ := bernoulli_mellinBarnes_sin_strip_lower ha hb hab
  have hlim := Polynomial.tendsto_div_exp_atTop
    ((Polynomial.X + 1 : Polynomial ℝ) ^ (n + 2))
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one] at hlim
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  let A : ℝ := ‖x‖ + 1
  let C : ℝ := 4 * π ^ 2 * A ^ n / m ^ 2
  refine ⟨C, max T 0, fun σ t hσa hσb ht => ?_⟩
  have htT : T ≤ |t| := le_trans (le_max_left _ _) ht
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have hA : 1 ≤ A := by dsimp [A]; linarith [norm_nonneg x]
  have he : (1 + |t|) ^ (n + 2) ≤ rexp (2 * π * |t|) := by
    have h := hT _ htT
    rw [div_lt_one (exp_pos _)] at h
    rw [add_comm |t| 1] at h
    refine h.le.trans (Real.exp_le_exp.mpr ?_)
    nlinarith [pi_gt_three]
  have hs : m * (rexp (π * |t|) / 2) ≤
      ‖Complex.sin (π * ((σ : ℂ) + t * Complex.I))‖ := by
    -- The sine and hyperbolic cosine bounds are imported from lean-codes.
    have hec := Real.exp_abs_div_two_le_cosh (π * t)
    rw [abs_mul, abs_of_pos pi_pos] at hec
    exact (mul_le_mul (hml σ ⟨hσa, hσb⟩) hec (by positivity) (by positivity)).trans
      (Complex.abs_sin_mul_cosh_le_norm_sin_pi σ t)
  have hn : ‖x + ((σ : ℂ) + t * Complex.I)‖ ≤ A * (1 + |t|) := by
    have hσ : |σ| ≤ 1 := by rw [abs_of_neg (lt_of_le_of_lt hσb hb)]; linarith
    calc
      _ ≤ ‖x‖ + (‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ ‖x‖ + (1 + |t|) := by simpa using add_le_add_left (add_le_add_right hσ |t|) ‖x‖
      _ ≤ _ := by dsimp [A]; nlinarith [norm_nonneg x]
  calc
    _ = ‖x + ((σ : ℂ) + t * Complex.I)‖ ^ n *
        (π / ‖Complex.sin (π * ((σ : ℂ) + t * Complex.I))‖) ^ 2 := by
      rw [norm_mul, norm_pow, norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos pi_pos]
    _ ≤ (A * (1 + |t|)) ^ n * (π / (m * (rexp (π * |t|) / 2))) ^ 2 := by
      gcongr
    _ = C * ((1 + |t|) ^ n / rexp (2 * π * |t|)) := by
      rw [show 2 * π * |t| = (2 : ℕ) * (π * |t|) by push_cast; ring, exp_nat_mul]
      rw [mul_pow]
      dsimp [C]
      field_simp
      ring
    _ ≤ C * (1 / (1 + |t|) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [C]; positivity)
      rw [div_le_div_iff₀ (exp_pos _) (by positivity), one_mul, ← pow_add]
      exact he
    _ = _ := by rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]

/-- The Bernoulli polynomial Mellin–Barnes integrand is integrable on every line `Re z = -c`
with `0 < c < 1`. -/
theorem integrable_bernoulliPolyB_mellinBarnes (n : ℕ) (x : ℂ) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    Integrable (fun t : ℝ => (x + (-c + t * Complex.I)) ^ n *
      ((π : ℂ) / Complex.sin (π * (-c + t * Complex.I))) ^ 2) := by
  obtain ⟨C, T, hC⟩ := bernoulli_mellinBarnes_tail_bound n x (a := -c) (b := -c)
    (by linarith) (by linarith) le_rfl
  obtain ⟨K, hK⟩ := Complex.exists_bound_of_tail_bound
    (f := fun z => (x + z) ^ n * ((π : ℂ) / Complex.sin (π * z)) ^ 2)
    (fun z hza hzb =>
      (bernoulli_mellinBarnes_differentiable n x (by linarith) (by linarith)).continuousAt) hC
  have hcont : Continuous (fun t : ℝ => (x + (-c + t * Complex.I)) ^ n *
      ((π : ℂ) / Complex.sin (π * (-c + t * Complex.I))) ^ 2) := by
    have hs : ∀ t : ℝ, Complex.sin (π * (-c + t * Complex.I)) ≠ 0 := fun t =>
      bernoulli_mellinBarnes_sin_ne_zero (by simp; linarith) (by simp; linarith)
    exact (by fun_prop : Continuous (fun t : ℝ => (x + (-c + t * Complex.I)) ^ n)).mul
      ((continuous_const.div (by fun_prop) hs).pow 2)
  exact (integrable_one_add_abs_rpow_neg_two.const_mul K).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun t => by
      simpa only [Complex.ofReal_neg] using hK (-c) t le_rfl le_rfl)

/-- Moving the vertical line within `-1 < Re z < 0` preserves the polynomial Mellin–Barnes
integral, by Cauchy’s theorem and uniform decay at infinity. -/
private lemma bernoulli_mellinBarnes_line_eq (n : ℕ) (x : ℂ) {c d : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hd0 : 0 < d) (hd1 : d < 1) :
    (∫ t : ℝ, (x + (-c + t * Complex.I)) ^ n *
      ((π : ℂ) / Complex.sin (π * (-c + t * Complex.I))) ^ 2) =
    ∫ t : ℝ, (x + (-d + t * Complex.I)) ^ n *
      ((π : ℂ) / Complex.sin (π * (-d + t * Complex.I))) ^ 2 := by
  suffices h : ∀ a b : ℝ, -1 < a → a ≤ b → b < 0 →
      (∫ t : ℝ, (x + (a + t * Complex.I)) ^ n *
        ((π : ℂ) / Complex.sin (π * (a + t * Complex.I))) ^ 2) =
      ∫ t : ℝ, (x + (b + t * Complex.I)) ^ n *
        ((π : ℂ) / Complex.sin (π * (b + t * Complex.I))) ^ 2 by
    rcases le_total (-c) (-d) with hcd | hdc
    · simpa only [Complex.ofReal_neg] using h (-c) (-d) (by linarith) hcd (by linarith)
    · simpa only [Complex.ofReal_neg] using (h (-d) (-c) (by linarith) hdc (by linarith)).symm
  intro a b ha hab hb
  obtain ⟨C, T, hC⟩ := bernoulli_mellinBarnes_tail_bound n x ha hb hab
  exact Complex.integral_vertical_eq_of_tail_bound hab
    (fun z hza hzb => bernoulli_mellinBarnes_differentiable n x (by linarith) (by linarith)) hC

/-- On the central line of the strip, the sine denominator becomes the real hyperbolic cosine. -/
private lemma bernoulli_mellinBarnes_central_sin (t : ℝ) :
    Complex.sin ((π : ℂ) * (-(1 / 2) + t * Complex.I)) = -(cosh (π * t) : ℂ) := by
  rw [show (π : ℂ) * (-(1 / 2) + t * Complex.I) = -(π / 2) + (π * t) * Complex.I by ring,
    Complex.sin_add_mul_I, Complex.sin_neg, Complex.sin_pi_div_two, Complex.cos_neg,
    Complex.cos_pi_div_two]
  simp [← Complex.ofReal_mul, ← Complex.ofReal_cosh]

/-- The zeroth half-line moment of `sech²(πt)` follows from the logistic primitive. -/
private lemma bernoulli_mellinBarnes_integral_sech_sq :
    ∫ t in Ioi (0 : ℝ), 1 / cosh (π * t) ^ 2 = 1 / π := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t => 2 / π / (1 + rexp (-(2 * π * t))))
      (1 / cosh (π * t) ^ 2) t := by
    intro t
    have h := ((((hasDerivAt_id t).const_mul (-(2 * π))).exp).const_add 1).inv
      (by positivity : 1 + rexp (-(2 * π) * t) ≠ 0)
    have h := h.const_mul (2 / π)
    simp only [id_eq, mul_one] at h
    convert h using 1
    · ext t; simp only [div_eq_mul_inv]; congr 3; ring
    · rw [Real.cosh_eq, show -(2 * π) * t = -(π * t) + -(π * t) by ring, exp_add,
        exp_neg]
      have he : rexp (π * t) ≠ 0 := (exp_pos _).ne'
      have hp : π ≠ 0 := pi_ne_zero
      field_simp
  have hlim : Tendsto (fun t : ℝ => 2 / π / (1 + rexp (-(2 * π * t)))) atTop (𝓝 (2 / π)) := by
    have he : Tendsto (fun t : ℝ => rexp (-(2 * π * t))) atTop (𝓝 0) := by
      exact Real.tendsto_exp_atBot.comp (by
        convert (tendsto_id.const_mul_atTop_of_neg
          (neg_neg_of_pos (by positivity : 0 < 2 * π))) using 1
        ext t; simp only [id_eq]; ring)
    convert tendsto_const_nhds.div (tendsto_const_nhds.add he)
      (by norm_num : (1 : ℝ) + 0 ≠ 0) using 1
    norm_num
  have hint : IntegrableOn (fun t : ℝ => 1 / cosh (π * t) ^ 2) (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun t _ => hd t) (fun t _ => by positivity) hlim
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hd t) hint hlim]
  simp only [mul_zero, neg_zero, exp_zero]
  field_simp
  ring

/-- Every polynomial moment of the central `sech²` kernel is integrable. -/
private lemma bernoulli_mellinBarnes_integrable_moment (n : ℕ) :
    Integrable (fun t : ℝ => (t * Complex.I) ^ n / (cosh (π * t) : ℂ) ^ 2) := by
  have h := (integrable_bernoulliPolyB_mellinBarnes n (1 / 2) (c := 1 / 2)
    (by norm_num) (by norm_num)).const_mul
    ((π : ℂ) ^ 2)⁻¹
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  convert h using 1
  ext t
  rw [bernoulli_mellinBarnes_central_sin]
  have hp : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  field_simp
  ring

/-- An even moment of the real `sech²` kernel is twice its integral over the positive half-line. -/
private lemma bernoulli_mellinBarnes_even_moment (m : ℕ) :
    (∫ t : ℝ, t ^ (2 * m) / cosh (π * t) ^ 2) =
      2 * ∫ t in Ioi (0 : ℝ), t ^ (2 * m) / cosh (π * t) ^ 2 := by
  rw [← integral_comp_abs]
  congr 1
  ext t
  rw [show π * |t| = |π * t| by rw [abs_mul, abs_of_pos pi_pos], Real.cosh_abs]
  congr 1
  rw [pow_mul, pow_mul, sq_abs]

/-- A moment along the imaginary axis is the corresponding real `sech²` moment multiplied by
the appropriate power of `I`. -/
private lemma bernoulli_mellinBarnes_moment_ofReal (n : ℕ) :
    (∫ t : ℝ, (t * Complex.I) ^ n / (cosh (π * t) : ℂ) ^ 2) =
      Complex.I ^ n * (∫ t : ℝ, t ^ n / cosh (π * t) ^ 2 : ℝ) := by
  rw [← integral_complex_ofReal, ← integral_const_mul]
  congr 1
  ext t
  push_cast
  rw [mul_pow]
  ring

/-- The normalized even moments of the central `sech²` kernel evaluate to the Bernoulli
polynomial values at `1/2`, by the known positive half-line integrals. -/
private lemma bernoulli_mellinBarnes_moment_two_mul (m : ℕ) :
    (π / 2 : ℂ) * (∫ t : ℝ, (t * Complex.I) ^ (2 * m) / (cosh (π * t) : ℂ) ^ 2) =
      bernoulliPolyB (2 * m) (1 / 2) := by
  rw [bernoulli_mellinBarnes_moment_ofReal]
  rcases m with _ | m
  · norm_num only [mul_zero, pow_zero, one_div, one_mul]
    have hr0 := bernoulli_mellinBarnes_even_moment 0
    simp only [mul_zero, pow_zero, one_div] at hr0
    rw [hr0]
    have hi0 : (∫ t in Ioi (0 : ℝ), (cosh (π * t) ^ 2)⁻¹) = 1 / π := by
      simpa only [one_div] using bernoulli_mellinBarnes_integral_sech_sq
    rw [hi0]
    norm_num [bernoulliPolyB]
    field_simp
  · have hb := bernoulli_two_mul_eq_integral_sech_sq (n := m + 1) (by omega)
    let q : ℝ := 1 - (2 : ℝ) ^ (1 - 2 * ((m + 1 : ℕ) : ℤ))
    have hq : q ≠ 0 := by
      dsimp [q]
      rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      norm_cast
      have htwo : (2 : ℝ) < 2 ^ (2 * (m + 1)) := by
        calc
          (2 : ℝ) = 2 ^ 1 := by norm_num
          _ < _ := pow_lt_pow_right₀ (by norm_num) (by omega)
      exact ne_of_gt (sub_pos.mpr ((div_lt_one (by positivity)).mpr (by exact_mod_cast htwo)))
    have hbq : q * (bernoulli (2 * (m + 1)) : ℝ) =
        (-1) ^ (m + 1 + 1) * π * ∫ t in Ioi (0 : ℝ),
          t ^ (2 * (m + 1)) / cosh (π * t) ^ 2 := by
      rw [hb]
      change q * ((-1) ^ (m + 1 + 1) * π / q * _) = _
      field_simp
    rw [bernoulliPolyB_half, bernoulli_mellinBarnes_even_moment,
      pow_mul, Complex.I_sq]
    have hbqc := congrArg (Complex.ofReal) hbq
    push_cast at hbqc
    rw [pow_succ (-1 : ℂ) (m + 1)] at hbqc
    have hqc : (1 - (2 : ℂ) ^ (1 - ((2 * (m + 1) : ℕ) : ℤ))) = (q : ℂ) := by
      dsimp [q]
      push_cast
      congr 2
    rw [hqc]
    push_cast
    linear_combination hbqc

/-- Odd moments of the central `sech²` kernel vanish by reflection of the real integration
variable. -/
private lemma bernoulli_mellinBarnes_moment_two_mul_add_one (m : ℕ) :
    (∫ t : ℝ, (t * Complex.I) ^ (2 * m + 1) / (cosh (π * t) : ℂ) ^ 2) = 0 := by
  rw [bernoulli_mellinBarnes_moment_ofReal]
  have hzero : (∫ t : ℝ, t ^ (2 * m + 1) / cosh (π * t) ^ 2) = 0 := by
    have h := integral_neg_eq_self (fun t : ℝ => t ^ (2 * m + 1) / cosh (π * t) ^ 2) volume
    simp only [neg_pow, (odd_two_mul_add_one m).neg_one_pow,
      show ∀ t : ℝ, π * -t = -(π * t) by intro t; ring, cosh_neg, neg_one_mul,
      neg_div, integral_neg] at h
    linarith
  rw [hzero, Complex.ofReal_zero, mul_zero]

/-- The normalized moments of the central `sech²` kernel are the Bernoulli polynomial values
at `1/2`; odd moments vanish by symmetry. -/
private lemma bernoulli_mellinBarnes_moment (n : ℕ) :
    (π / 2 : ℂ) * (∫ t : ℝ, (t * Complex.I) ^ n / (cosh (π * t) : ℂ) ^ 2) =
      bernoulliPolyB n (1 / 2) := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · simpa only [two_mul] using bernoulli_mellinBarnes_moment_two_mul m
  · rw [bernoulli_mellinBarnes_moment_two_mul_add_one, mul_zero]
    rw [show (1 / 2 : ℂ) = ((2⁻¹ : ℝ) : ℂ) by norm_num,
      bernoulliPolyB_ofReal, bernoulliFun_eval_half_eq_zero, Complex.ofReal_zero]

/-- Expanding a polynomial against the central `sech²` kernel gives the Bernoulli addition
formula centered at `1/2`. -/
private lemma bernoulli_mellinBarnes_central_polynomial (n : ℕ) (z : ℂ) :
    (π / 2 : ℂ) * (∫ t : ℝ, (z + t * Complex.I) ^ n / (cosh (π * t) : ℂ) ^ 2) =
      bernoulliPolyB n (z + 1 / 2) := by
  rw [add_comm z (1 / 2), bernoulliPolyB_add]
  have heq : (fun t : ℝ => (z + t * Complex.I) ^ n / (cosh (π * t) : ℂ) ^ 2) =
      fun t : ℝ => ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * z ^ (n - k) *
        ((t * Complex.I) ^ k / (cosh (π * t) : ℂ) ^ 2) := by
    ext t
    rw [add_comm z _, add_pow, Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    ring
  rw [heq, integral_finsetSum, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [integral_const_mul]
    calc
      _ = (n.choose k : ℂ) * ((π / 2 : ℂ) *
          (∫ t : ℝ, (t * Complex.I) ^ k / (cosh (π * t) : ℂ) ^ 2)) * z ^ (n - k) := by ring
      _ = _ := by rw [bernoulli_mellinBarnes_moment]
  · intro k hk
    exact (bernoulli_mellinBarnes_integrable_moment k).const_mul _

/-- **Mellin–Barnes integral, DLMF 24.7.11**: for `0 < c < 1` and complex `x`,
`Bₙ(x) = (1/(2πi)) ∫_{-c-i∞}^{-c+i∞} (x+t)ⁿ (π/sin(πt))² dt`, written along `t = -c + is`. -/
@[dlmf 24.7.E11]
theorem bernoulliPolyB_eq_mellinBarnes (n : ℕ) (x : ℂ) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    bernoulliPolyB n x = 1 / (2 * π) * ∫ s : ℝ, (x + (-c + s * Complex.I)) ^ n *
      ((π : ℂ) / Complex.sin (π * (-c + s * Complex.I))) ^ 2 := by
  rw [bernoulli_mellinBarnes_line_eq n x hc0 hc1 (d := 1 / 2) (by norm_num) (by norm_num)]
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have heq : (fun t : ℝ => (x + (-(1 / 2) + t * Complex.I)) ^ n *
        ((π : ℂ) / Complex.sin (π * (-(1 / 2) + t * Complex.I))) ^ 2) =
      fun t : ℝ => (π : ℂ) ^ 2 * ((x - 1 / 2 + t * Complex.I) ^ n /
        (cosh (π * t) : ℂ) ^ 2) := by
    ext t
    rw [bernoulli_mellinBarnes_central_sin]
    ring
  rw [heq, integral_const_mul, ← mul_assoc,
    show (1 / (2 * π) : ℂ) * (π : ℂ) ^ 2 = π / 2 by field_simp,
    bernoulli_mellinBarnes_central_polynomial, sub_add_cancel]

end DLMF.BernoulliEuler
