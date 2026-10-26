/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Basic
public import DLMF.Elementary.Hyperbolic

/-!
# Bernoulli and Euler polynomials: generating functions and tables (DLMF §24.2)

* 24.2.1 is the project's `Complex.hasSum_bernoulli_mul_pow_div` (`DLMFMathlib`, tagged there).
* 24.2.2 and 24.2.7: odd numbers vanish; the signs of `B₂ₙ` (from Mathlib's `ζ(2n)`) and of `E₂ₙ`.
* 24.2.3 and 24.2.8: the generating functions of the polynomials, on DLMF's full discs
  `|t| < 2π` and `|t| < π`, by a Cauchy product with `e^{xt}`.
* 24.2.5 and 24.2.10: the explicit sums; 24.2.6 on the full disc `|t| < π/2`; 24.2.9.
* 24.2.11–24.2.12: the periodic functions `periodicBernoulliB`, `periodicEulerE` (Basic).
* Tables 24.2.1 and 24.2.2: the first entries (exact values).

Helper declarations carry the prefix `b24a_`.
-/

@[expose] public section

noncomputable section

open Polynomial (aeval X C aeval_monomial)
open Finset Filter
open scoped Nat Real Topology

namespace DLMF.BernoulliEuler

/-! ### Power-series helpers -/

/-- A power series that converges on the disc `‖z‖ < R` converges absolutely there. -/
theorem b24a_summable_norm_of_summable {a : ℕ → ℂ} {R : ℝ}
    (h : ∀ z : ℂ, ‖z‖ < R → Summable (fun n => a n * z ^ n)) {z : ℂ} (hz : ‖z‖ < R) :
    Summable (fun n => ‖a n * z ^ n‖) := by
  obtain ⟨r, hzr, hrR⟩ := exists_between hz
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg z) hzr
  have hs := h (r : ℂ) (by rwa [Complex.norm_real, Real.norm_of_nonneg hr0.le])
  obtain ⟨C, hC⟩ : BddAbove (Set.range fun n => ‖a n * (r : ℂ) ^ n‖) :=
    (hs.tendsto_atTop_zero.norm.isBoundedUnder_le).bddAbove_range
  have hq : ‖z‖ / r < 1 := (div_lt_one hr0).mpr hzr
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (by positivity) hq).mul_left C)
  have hn := hC ⟨n, rfl⟩
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le] at hn ⊢
  have : ‖a n‖ * ‖z‖ ^ n = ‖a n‖ * r ^ n * (‖z‖ / r) ^ n := by
    rw [div_pow, mul_assoc, mul_div_cancel₀ _ (pow_ne_zero n hr0.ne')]
  rw [this]
  gcongr

/-- Cauchy product of an exponential-type series with `e^{wz}`. -/
theorem b24a_hasSum_mul_exp {a : ℕ → ℂ} {S z w : ℂ}
    (hs : Summable fun n => ‖a n * z ^ n / (n ! : ℂ)‖) (h : HasSum (fun n => a n * z ^ n / n !) S) :
    HasSum (fun n => (∑ k ∈ range (n + 1), (n.choose k : ℂ) * a k * w ^ (n - k)) * z ^ n / n !)
      (S * Complex.exp (w * z)) := by
  have hexp : HasSum (fun n : ℕ => (w * z) ^ n / n !) (Complex.exp (w * z)) := by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (w * z)
  have hg : Summable fun n : ℕ => ‖(w * z) ^ n / (n ! : ℂ)‖ := by
    simpa [norm_div, norm_pow, Complex.norm_natCast] using
      Real.summable_pow_div_factorial ‖w * z‖
  have hprod := hasSum_sum_range_mul_of_summable_norm hs hg
  rw [h.tsum_eq, hexp.tsum_eq] at hprod
  refine hprod.congr_fun fun n => ?_
  simp only [Finset.sum_mul, Finset.sum_div]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hk1 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hk2 : ((n - k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hch : (n.choose k : ℂ) = n ! / (k ! * (n - k)!) := by
    rw [Nat.choose_eq_factorial_div_factorial hkn, Nat.cast_div
      (Nat.factorial_mul_factorial_dvd_factorial hkn) (by push_cast; exact mul_ne_zero hk1 hk2)]
    push_cast; ring
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [hch, show z ^ n = z ^ k * z ^ (n - k) by rw [← pow_add, Nat.add_sub_cancel' hkn], mul_pow]
  field_simp

/-! ### §24.2(i) Bernoulli numbers and polynomials -/

/-- **DLMF 24.2.2**: `B₂ₙ₊₁ = 0` and `(-1)ⁿ⁺¹ B₂ₙ > 0` for `n = 1, 2, …`. The sign comes from
Mathlib's `ζ(2n) = (-1)ⁿ⁺¹ 2²ⁿ⁻¹ π²ⁿ B₂ₙ/(2n)! > 0`. -/
@[dlmf 24.2.E2]
theorem bernoulli_two_mul_add_one_eq_zero_and_sign {n : ℕ} (hn : 1 ≤ n) :
    bernoulli (2 * n + 1) = 0 ∧ 0 < (-1) ^ (n + 1) * bernoulli (2 * n) := by
  refine ⟨bernoulli_eq_zero_of_odd (odd_two_mul_add_one n) (by omega), ?_⟩
  have h := hasSum_zeta_nat (k := n) (by omega)
  have h1 : (1 : ℝ) ≤ (-1 : ℝ) ^ (n + 1) * 2 ^ (2 * n - 1) * π ^ (2 * n) * bernoulli (2 * n) /
      (2 * n)! := by
    have := le_hasSum h 1 (fun j _ => by positivity)
    simpa using this
  have hpos : (0 : ℝ) < 2 ^ (2 * n - 1) * π ^ (2 * n) / (2 * n)! := by positivity
  have : (0 : ℝ) < (-1) ^ (n + 1) * (bernoulli (2 * n) : ℝ) := by
    by_contra hc
    push Not at hc
    have : (-1 : ℝ) ^ (n + 1) * 2 ^ (2 * n - 1) * π ^ (2 * n) * bernoulli (2 * n) / (2 * n)! =
        ((-1) ^ (n + 1) * (bernoulli (2 * n) : ℝ)) *
          (2 ^ (2 * n - 1) * π ^ (2 * n) / (2 * n)!) := by
      ring
    rw [this] at h1
    nlinarith
  exact_mod_cast this

/-- **DLMF 24.2.5**: `Bₙ(x) = ∑ₖ (n choose k) Bₖ x^{n-k}`, complex `x`. -/
@[dlmf 24.2.E5]
theorem bernoulliPolyB_eq_sum (n : ℕ) (x : ℂ) :
    bernoulliPolyB n x = ∑ k ∈ range (n + 1), (n.choose k : ℂ) * bernoulli k * x ^ (n - k) := by
  simp only [bernoulliPolyB, Polynomial.bernoulli, map_sum, aeval_monomial]
  refine sum_congr rfl fun k _ => ?_
  simp only [map_mul, eq_ratCast, map_natCast]
  ring

/-- **DLMF 24.2.3**: the generating function `t e^{xt}/(e^t - 1) = ∑ₙ Bₙ(x) tⁿ/n!` for
`0 < |t| < 2π`, complex `x`. (At `t = 0` the left side is understood as its limit `1`.) -/
@[dlmf 24.2.E3]
theorem hasSum_bernoulliPolyB_mul_pow_div (x : ℂ) {t : ℂ} (ht : ‖t‖ < 2 * π) (ht0 : t ≠ 0) :
    HasSum (fun n : ℕ => bernoulliPolyB n x * t ^ n / n !)
      (t * Complex.exp (x * t) / (Complex.exp t - 1)) := by
  have hsum : ∀ z : ℂ, ‖z‖ < 2 * π →
      Summable (fun n => ((bernoulli n : ℂ) / n !) * z ^ n) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      exact (hasSum_single 0 (fun n hn => by simp [zero_pow hn])).summable
    · exact ((Complex.hasSum_bernoulli_mul_pow_div hz hz0).congr_fun
        fun n => by ring).summable
  have hs : Summable fun n => ‖(bernoulli n : ℂ) * t ^ n / (n ! : ℂ)‖ := by
    refine (b24a_summable_norm_of_summable hsum ht).congr fun n => ?_
    congr 1; ring
  have h := b24a_hasSum_mul_exp (w := x) hs (Complex.hasSum_bernoulli_mul_pow_div ht ht0)
  rw [show t / (Complex.exp t - 1) * Complex.exp (x * t) =
    t * Complex.exp (x * t) / (Complex.exp t - 1) by ring] at h
  refine h.congr_fun fun n => ?_
  rw [bernoulliPolyB_eq_sum]

/-- **DLMF 24.2.4**: `Bₙ = Bₙ(0)`. -/
@[dlmf 24.2.E4]
theorem bernoulli_eq_bernoulliPolyB_zero (n : ℕ) : (bernoulli n : ℂ) = bernoulliPolyB n 0 :=
  (bernoulliPolyB_zero_arg n).symm

/-! ### §24.2(ii) Euler numbers and polynomials -/

/-- **DLMF 24.2.6** on DLMF's full disc: `2eᵗ/(e^{2t} + 1) = sech t = ∑ₙ Eₙ tⁿ/n!` for
`|t| < π/2`. (The project's `hasSum_eulerNumber_mul_pow_div`, also tagged 24.2.E6, has radius
`1/2`.) -/
@[dlmf 24.2.E6]
theorem hasSum_eulerNumber_mul_pow_div' {t : ℂ} (ht : ‖t‖ < π / 2) :
    HasSum (fun n : ℕ => (eulerNumber n : ℂ) * t ^ n / n !)
      (2 * Complex.exp t / (Complex.exp (2 * t) + 1)) := by
  have hval : 2 * Complex.exp t / (Complex.exp (2 * t) + 1) = DLMF.Elementary.sech t := by
    rw [DLMF.Elementary.sech, Complex.cosh, show 2 * t = t + t by ring, Complex.exp_add,
      Complex.exp_neg]
    have he : Complex.exp t ≠ 0 := Complex.exp_ne_zero t
    by_cases hc : Complex.exp t * Complex.exp t + 1 = 0
    · have : Complex.exp t + (Complex.exp t)⁻¹ = 0 := by
        field_simp; linear_combination hc
      rw [hc, this]; simp
    · field_simp
  rw [hval]
  have h := DLMF.Elementary.hasSum_sech ht
  have hodd : ∀ n ∉ Set.range (fun k : ℕ => 2 * k),
      (eulerNumber n : ℂ) * t ^ n / n ! = 0 := by
    intro n hn
    have : Odd n := by
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | h
      · exact absurd ⟨m, by simp only; omega⟩ hn
      · exact h
    simp [eulerNumber_eq_zero_of_odd this]
  refine ((mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0)).hasSum_iff hodd).mp ?_
  refine h.congr_fun fun k => ?_
  simp only [Function.comp]
  ring

/-- Dirichlet's beta at odd integers through Euler numbers, as an alternating series over odd
numbers: `∑_{m≥0} (-1)ᵐ/(2m+1)^{2k+1} = (-1)ᵏ E₂ₖ π^{2k+1}/(4^{k+1}(2k)!)`, `k ≥ 1`. -/
theorem q24a_hasSum_alt_odd_eulerNumber {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun m : ℕ => (-1 : ℝ) ^ m * (1 / (2 * (m : ℝ) + 1) ^ (2 * k + 1)))
      ((-1) ^ k * (eulerNumber (2 * k) : ℝ) * π ^ (2 * k + 1) / (4 ^ (k + 1) * (2 * k)!)) := by
  have h := Polynomial.hasSum_sin_pi_div_two_div_pow_eulerNumber hk
  have hinj : Function.Injective (fun m : ℕ => 2 * m + 1) := fun a b h => by simp at h; omega
  rw [← hinj.hasSum_iff] at h
  · refine h.congr_fun fun m => ?_
    simp only [Function.comp, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [show π * (2 * (m : ℝ) + 1) / 2 = π / 2 + m * π by ring, Real.sin_add_nat_mul_pi,
      Real.sin_pi_div_two]
    ring
  · intro n hn
    obtain ⟨j, rfl⟩ : Even n := by
      rcases Nat.even_or_odd n with h | ⟨j, rfl⟩
      · exact h
      · exact absurd ⟨j, by ring⟩ hn
    simp only [Nat.cast_add]
    rw [show π * ((j : ℝ) + j) / 2 = j * π by ring, Real.sin_nat_mul_pi, mul_zero]

/-- Alternating-series bounds for `β(2k+1)`. -/
theorem q24a_dirichletBeta_bounds {k : ℕ} (hk : k ≠ 0) :
    1 - (1 / 3 : ℝ) ^ (2 * k + 1) + (1 / 5) ^ (2 * k + 1) - (1 / 7) ^ (2 * k + 1) ≤
        (-1) ^ k * (eulerNumber (2 * k) : ℝ) * π ^ (2 * k + 1) / (4 ^ (k + 1) * (2 * k)!) ∧
      (-1) ^ k * (eulerNumber (2 * k) : ℝ) * π ^ (2 * k + 1) / (4 ^ (k + 1) * (2 * k)!) ≤
        1 - (1 / 3 : ℝ) ^ (2 * k + 1) + (1 / 5) ^ (2 * k + 1) := by
  have h := (q24a_hasSum_alt_odd_eulerNumber hk).tendsto_sum_nat
  have hanti : Antitone (fun m : ℕ => 1 / (2 * (m : ℝ) + 1) ^ (2 * k + 1)) := by
    intro a b hab
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    have : (2 * (a : ℝ) + 1) ≤ 2 * b + 1 := by linarith
    simp only
    gcongr
  have h1 := hanti.alternating_series_le_tendsto h 2
  have h2 := hanti.tendsto_le_alternating_series h 1
  simp only [show 2 * 2 = 3 + 1 by rfl, show 2 * 1 + 1 = 2 + 1 by rfl, sum_range_succ,
    sum_range_zero] at h1 h2
  norm_num at h1 h2
  simp only [one_div, inv_pow]
  constructor <;> linarith

/-- **DLMF 24.2.7**: `E₂ₙ₊₁ = 0` and `(-1)ⁿ E₂ₙ > 0`. -/
@[dlmf 24.2.E7]
theorem eulerNumber_two_mul_add_one_eq_zero_and_sign (n : ℕ) :
    eulerNumber (2 * n + 1) = 0 ∧ 0 < (-1) ^ n * eulerNumber (2 * n) := by
  refine ⟨eulerNumber_eq_zero_of_odd (odd_two_mul_add_one n), ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hb := (q24a_dirichletBeta_bounds hn.ne').1
  have h3 : (1 / 7 : ℝ) ^ (2 * n + 1) ≤ (1 / 5) ^ (2 * n + 1) := by gcongr; norm_num
  have h4 : (1 / 3 : ℝ) ^ (2 * n + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hpos : (0 : ℝ) < (-1) ^ n * (eulerNumber (2 * n) : ℝ) * π ^ (2 * n + 1) /
      (4 ^ (n + 1) * (2 * n)!) := by linarith
  have hK : (0 : ℝ) < π ^ (2 * n + 1) / (4 ^ (n + 1) * (2 * n)!) := by positivity
  have : (0 : ℝ) < (-1) ^ n * (eulerNumber (2 * n) : ℝ) := by
    rw [mul_div_assoc] at hpos
    exact pos_of_mul_pos_left hpos hK.le
  exact_mod_cast this

/-- **DLMF 24.2.10**: `Eₙ(x) = ∑ₖ (n choose k) (Eₖ/2ᵏ) (x - 1/2)^{n-k}`, complex `x`. -/
@[dlmf 24.2.E10]
theorem eulerPolyE_eq_sum (n : ℕ) (x : ℂ) :
    eulerPolyE n x =
      ∑ k ∈ range (n + 1), (n.choose k : ℂ) * ((eulerNumber k : ℂ) / 2 ^ k) *
        (x - 1 / 2) ^ (n - k) := by
  have h := eulerPolyE_add n (1 / 2) (x - 1 / 2)
  rw [show (1 / 2 : ℂ) + (x - 1 / 2) = x by ring] at h
  rw [h]
  refine sum_congr rfl fun k _ => ?_
  rw [eulerPolyE_half]

/-- **DLMF 24.2.8**: the generating function `2e^{xt}/(eᵗ + 1) = ∑ₙ Eₙ(x) tⁿ/n!` for `|t| < π`,
complex `x`. -/
@[dlmf 24.2.E8]
theorem hasSum_eulerPolyE_mul_pow_div (x : ℂ) {t : ℂ} (ht : ‖t‖ < π) :
    HasSum (fun n : ℕ => eulerPolyE n x * t ^ n / n !)
      (2 * Complex.exp (x * t) / (Complex.exp t + 1)) := by
  have ht2 : ‖t / 2‖ < π / 2 := by
    rw [norm_div, Complex.norm_two]; linarith
  have hsum : ∀ z : ℂ, ‖z‖ < π →
      Summable (fun n => ((eulerNumber n : ℂ) / 2 ^ n / n !) * z ^ n) := by
    intro z hz
    have hz2 : ‖z / 2‖ < π / 2 := by rw [norm_div, Complex.norm_two]; linarith
    exact ((hasSum_eulerNumber_mul_pow_div' hz2).congr_fun fun n => by
      rw [div_pow]; ring).summable
  have hE := hasSum_eulerNumber_mul_pow_div' ht2
  have hE' : HasSum (fun n : ℕ => ((eulerNumber n : ℂ) / 2 ^ n) * t ^ n / n !)
      (2 * Complex.exp (t / 2) / (Complex.exp (2 * (t / 2)) + 1)) :=
    hE.congr_fun fun n => by rw [div_pow]; ring
  have hs : Summable fun n => ‖((eulerNumber n : ℂ) / 2 ^ n) * t ^ n / (n ! : ℂ)‖ := by
    refine (b24a_summable_norm_of_summable hsum ht).congr fun n => ?_
    congr 1; ring
  have h := b24a_hasSum_mul_exp (w := x - 1 / 2) hs hE'
  have hval : 2 * Complex.exp (t / 2) / (Complex.exp (2 * (t / 2)) + 1) *
      Complex.exp ((x - 1 / 2) * t) = 2 * Complex.exp (x * t) / (Complex.exp t + 1) := by
    rw [show 2 * (t / 2) = t by ring, div_mul_eq_mul_div, mul_assoc, ← Complex.exp_add,
      show t / 2 + (x - 1 / 2) * t = x * t by ring]
  rw [hval] at h
  refine h.congr_fun fun n => ?_
  rw [eulerPolyE_eq_sum]

/-- **DLMF 24.2.9**: `Eₙ = 2ⁿ Eₙ(1/2)` is an integer. -/
@[dlmf 24.2.E9]
theorem eulerNumber_eq_two_pow_mul_and_integer (n : ℕ) :
    eulerNumber n = 2 ^ n * (Polynomial.euler n).eval (1 / 2) ∧ ∃ m : ℤ, eulerNumber n = m := by
  refine ⟨rfl, ?_⟩
  set R : Subring ℚ := (Int.castRingHom ℚ).range
  suffices h : eulerNumber n ∈ R by
    obtain ⟨m, hm⟩ := h
    exact ⟨m, hm.symm⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | n
  · rw [eulerNumber_zero]; exact R.one_mem
  have hs := sum_choose_mul_eulerNumber (n + 1)
  rw [sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, zero_pow (Nat.succ_ne_zero n),
    mul_zero] at hs
  have hE : eulerNumber (n + 1) = -∑ k ∈ range (n + 1), ((n + 1).choose k : ℚ) *
      ((1 + (-1) ^ (n + 1 - k)) / 2) * eulerNumber k := by
    have : ∑ k ∈ range (n + 1), ((n + 1).choose k : ℚ) * ((1 + (-1) ^ (n + 1 - k)) / 2) *
        eulerNumber k = (∑ k ∈ range (n + 1), ((n + 1).choose k : ℚ) * (1 + (-1) ^ (n + 1 - k)) *
        eulerNumber k) / 2 := by
      rw [sum_div]; refine sum_congr rfl fun k _ => by ring
    rw [this]; push_cast at hs; linarith
  rw [hE]
  refine R.neg_mem (R.sum_mem fun k hk => R.mul_mem (R.mul_mem (natCast_mem R _) ?_)
    (ih k (mem_range.mp hk)))
  rcases neg_one_pow_eq_or ℚ (n + 1 - k) with h | h <;> rw [h]
  · exact ⟨1, by norm_num⟩
  · exact ⟨0, by norm_num⟩

/-! ### §24.2(iii) Periodic Bernoulli and Euler functions -/

/-- **DLMF 24.2.11**: `B̃ₙ(x) = Bₙ(x)` and `Ẽₙ(x) = Eₙ(x)` for `0 ≤ x < 1`. -/
@[dlmf 24.2.E11]
theorem periodic_eq_of_mem_Ico (n : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    periodicBernoulliB n x = bernoulliFun n x ∧ periodicEulerE n x = eulerFun n x := by
  have hf : Int.fract x = x := Int.fract_eq_self.mpr ⟨h0, h1⟩
  have hfl : ⌊x⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩
  simp [periodicBernoulliB, periodicEulerE, hf, hfl]

/-- **DLMF 24.2.12**: `B̃ₙ(x+1) = B̃ₙ(x)` and `Ẽₙ(x+1) = -Ẽₙ(x)`, real `x`. -/
@[dlmf 24.2.E12]
theorem periodic_add_one (n : ℕ) (x : ℝ) :
    periodicBernoulliB n (x + 1) = periodicBernoulliB n x ∧
      periodicEulerE n (x + 1) = -periodicEulerE n x := by
  refine ⟨by simp [periodicBernoulliB], ?_⟩
  simp only [periodicEulerE, Int.fract_add_one, Int.floor_add_one]
  rw [zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  ring

/-! ### §24.2(iv) Tables (exact values; a few entries) -/

/-- **Table 24.2.1** (first entries): `B₀ = 1`, `B₁ = -1/2`, `B₂ = 1/6`, `B₄ = -1/30`,
`B₆ = 1/42`, `E₀ = 1`, `E₂ = -1`, `E₄ = 5`, `E₆ = -61`, and `B₃ = B₅ = E₁ = E₃ = E₅ = 0`. -/
@[dlmf 24.2.T1]
theorem table_24_2_1 :
    bernoulli 0 = 1 ∧ bernoulli 1 = -1 / 2 ∧ bernoulli 2 = 1 / 6 ∧ bernoulli 3 = 0 ∧
      bernoulli 4 = -1 / 30 ∧ bernoulli 5 = 0 ∧ bernoulli 6 = 1 / 42 ∧
      eulerNumber 0 = 1 ∧ eulerNumber 1 = 0 ∧ eulerNumber 2 = -1 ∧ eulerNumber 3 = 0 ∧
      eulerNumber 4 = 5 ∧ eulerNumber 5 = 0 ∧ eulerNumber 6 = -61 := by
  have b3 : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
  have b5 : bernoulli 5 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
  have b4 : bernoulli 4 = -1 / 30 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]
  have b6 : bernoulli 6 = 1 / 42 := by
    have h := sum_bernoulli 7
    simp only [sum_range_succ, sum_range_zero, show (7 : ℕ) ≠ 1 by norm_num, ite_false] at h
    rw [b3, b4, b5, bernoulli_zero, bernoulli_one, bernoulli_two] at h
    norm_num [Nat.choose] at h
    linarith
  have e1 : eulerNumber 1 = 0 := eulerNumber_eq_zero_of_odd (by decide)
  have e3 : eulerNumber 3 = 0 := eulerNumber_eq_zero_of_odd (by decide)
  have e5 : eulerNumber 5 = 0 := eulerNumber_eq_zero_of_odd (by decide)
  have e2 : eulerNumber 2 = -1 := by
    have h := sum_choose_mul_eulerNumber 2
    simp only [sum_range_succ, sum_range_zero, eulerNumber_zero, e1] at h
    norm_num [Nat.choose] at h
    linarith
  have e4 : eulerNumber 4 = 5 := by
    have h := sum_choose_mul_eulerNumber 4
    simp only [sum_range_succ, sum_range_zero, eulerNumber_zero, e1, e2, e3] at h
    norm_num [Nat.choose] at h
    linarith
  have e6 : eulerNumber 6 = -61 := by
    have h := sum_choose_mul_eulerNumber 6
    simp only [sum_range_succ, sum_range_zero, eulerNumber_zero, e1, e2, e3, e4, e5] at h
    norm_num [Nat.choose] at h
    linarith
  exact ⟨bernoulli_zero, bernoulli_one, by rw [bernoulli_two]; norm_num, b3, b4, b5, b6,
    eulerNumber_zero, e1, e2, e3, e4, e5, e6⟩

/-- **Table 24.2.2** (first entries): `B₂(x) = x² - x + 1/6`, `B₃(x) = x³ - (3/2)x² + (1/2)x`,
`E₁(x) = x - 1/2`, `E₂(x) = x² - x`, `E₃(x) = x³ - (3/2)x² + 1/4`, as polynomials over `ℚ`.
(`B₀ = E₀ = 1` and `B₁(x) = x - 1/2` are `Polynomial.bernoulli_zero`, `Polynomial.euler_zero`,
`Polynomial.bernoulli_one`.) -/
@[dlmf 24.2.T2]
theorem table_24_2_2 :
    Polynomial.bernoulli 2 = X ^ 2 - X + C (1 / 6) ∧
      Polynomial.bernoulli 3 = X ^ 3 - C (3 / 2) * X ^ 2 + C (1 / 2) * X ∧
      Polynomial.euler 1 = X - C (1 / 2) ∧ Polynomial.euler 2 = X ^ 2 - X ∧
      Polynomial.euler 3 = X ^ 3 - C (3 / 2) * X ^ 2 + C (1 / 4) := by
  have b3 : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
  have e1 := Polynomial.euler_one
  have e2 : Polynomial.euler 2 = X ^ 2 - X := by
    refine Polynomial.funext fun r => ?_
    rw [Polynomial.euler_def]; simp [sum_range_succ, e1, Nat.choose]; ring
  refine ⟨?_, ?_, e1, e2, ?_⟩
  · refine Polynomial.funext fun r => ?_
    simp [Polynomial.bernoulli, sum_range_succ, Nat.choose]; ring
  · refine Polynomial.funext fun r => ?_
    simp [Polynomial.bernoulli, sum_range_succ, Nat.choose, b3]; ring
  · refine Polynomial.funext fun r => ?_
    rw [Polynomial.euler_def]; simp [sum_range_succ, e1, e2, Nat.choose]; ring

end DLMF.BernoulliEuler
