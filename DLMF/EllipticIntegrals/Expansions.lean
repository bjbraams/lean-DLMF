/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Quadratic

/-!
# Maclaurin and related expansions of Legendre's integrals (DLMF §19.5)

Complex-modulus forms of DLMF 19.5.1–19.5.11: Maclaurin series of the complete and incomplete
integrals, expansions of Jacobi's nome, the nome series for `K` and `E`, and the descending
Landen product for `K`.

## Main definitions

* `appellF1Term`: the general term of Appell's double series `F₁` (DLMF 16.13.1).
* `landenModulusSeq`: the descending Landen sequence of moduli (DLMF 19.5.11).

## Main results

* `compEllIntKk_hasSum`, `compEllIntEk_hasSum`, `compEllIntDk_hasSum`: the Maclaurin series of
  `K`, `E` and `D` for `|k| < 1` (DLMF 19.5.1–19.5.3).
* `compEllIntPik_hasSum`: the double series of `Π(α², k)` (DLMF 19.5.4).
* `incEllIntFk_hasSum`, `incEllIntEk_hasSum`, `incEllIntPik_hasSum`: the series of the
  incomplete integrals (DLMF 19.5.4_1–19.5.4_3).
* `jacobiNomek_isBigO`, `jacobiNomek_isBigO_lambda`: expansions of the nome as `k → 0+`
  (DLMF 19.5.5–19.5.7).
* `compEllIntKk_eq_nome_series`, `compEllIntEk_eq_nome_series`: `K` and `E` as series in the
  nome (DLMF 19.5.8, 19.5.9).
* `compEllIntKk_eq_landen_prod`: `K(k) = (π/2) ∏_{m ≥ 1} (1 + k_m)` (DLMF 19.5.10).

## Implementation notes

* Series are stated with `HasSum`, and `₂F₁` is Mathlib's `ordinaryHypergeometric`. The
  Appell function is the project's `DLMF.Hypergeometric.appF1` (DLMF 16.13.1, the totalized
  double series), written out here as the `tsum` over `ℕ × ℕ` of the terms `appellF1Term`,
  because the module `DLMF.GeneralizedHypergeometric.Appell` cannot be imported together with
  `lean-codes` (both import a declaration `DifferentiableOn.analyticOnNhd_of_finiteDimensional`,
  from TauCeti and from `SeveralComplexVariables`).
* The nome is the Chapter 22 definition
  `DLMF.JacobiElliptic.jacobiNomek k = exp(-πK'(k)/K(k))`, with the literal `K'`, which is
  DLMF's `K'` for `Re k > 0`. The expansions 19.5.5–19.5.6 with "`+ ⋯`" are stated as
  `O`-estimates of the remainder as `k → 0+`.
* The real-parameter forms of 19.5.1–19.5.2 are
  `DLMF.Elliptic.Real.compEllIntKm_eq_ordinaryHypergeometric` and
  `Real.compEllIntEm_eq_ordinaryHypergeometric` (tagged there). The complex forms of
  19.5.1–19.5.3 follow from Euler's integral
  `DLMF.Hypergeometric.ordinaryHypergeometric_eq_integral` with the substitution `t = sin²θ`.

## References

* NIST DLMF §19.5.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic DLMF.Hypergeometric

/-- The `(p₁, p₂)` term of Appell's double series
`F₁(a; b, b'; c; x, y) = ∑ (a)_{p₁+p₂} (b)_{p₁} (b')_{p₂}/((c)_{p₁+p₂} p₁! p₂!) x^{p₁} y^{p₂}`
(DLMF 16.13.1), summed with `tsum` over `ℕ × ℕ` below. -/
def appellF1Term (a b b' c x y : ℂ) (p : ℕ × ℕ) : ℂ :=
  poch a (p.1 + p.2) * poch b p.1 * poch b' p.2 /
    (poch c (p.1 + p.2) * (Nat.factorial p.1 * Nat.factorial p.2 : ℂ)) * x ^ p.1 * y ^ p.2

/-- `‖k²‖ < 1` for `‖k‖ < 1`. -/
private lemma norm_sq_lt_one {k : ℂ} (hk : ‖k‖ < 1) : ‖k ^ 2‖ < 1 := by
  rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hk (by decide)

/-- Euler's integral for `₂F₁(a, 1/2; 1; k²)` in the angular form. -/
private lemma pi_div_two_mul_ordinaryHypergeometric_half_one {a k : ℂ} (hk : ‖k‖ < 1) :
    (π / 2 : ℂ) * ₂F₁ a (1 / 2) 1 (k ^ 2) =
      ∫ θ in (0 : ℝ)..(π / 2), (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-a) := by
  rw [ordinaryHypergeometric_eq_integral (by norm_num) (by norm_num) (norm_sq_lt_one hk),
    show (1 : ℂ) - 1 / 2 = 1 / 2 by ring, Gamma_one, Gamma_one_half_mul_self,
    show (1 / 2 : ℂ) - 1 = -(1 / 2) by ring, integral_beta_half_weight]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [ofReal_pow]
  field_simp

/-- The Gauss series of `₂F₁(a, b; c; k²)` in powers of `k`, for `‖k‖ < 1`. -/
private lemma hasSum_gaussHGCoeff_mul_pow (a b c : ℂ) {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => gaussHGCoeff a b c m * k ^ (2 * m)) (₂F₁ a b c (k ^ 2)) := by
  have h := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).hasSum_mul_pow
    (z := k ^ 2) (by
      rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ← ENNReal.coe_one,
        ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
      exact norm_sq_lt_one hk)
  simpa only [← pow_mul] using h

/-- `(1)ₘ = m!`. -/
private lemma poch_one_eq_factorial (m : ℕ) : poch 1 m = (Nat.factorial m : ℂ) := by
  simp [poch, ascPochhammer_eval_one]

/-- `(2)ₘ = (m+1)!`. -/
private lemma poch_two_eq_factorial (m : ℕ) : poch 2 m = (Nat.factorial (m + 1) : ℂ) := by
  induction m with
  | zero => simp [poch]
  | succ n ih =>
    rw [poch, ascPochhammer_succ_eval, ← poch, ih, Nat.factorial_succ (n + 1)]
    push_cast; ring

/-- DLMF 19.5.1: for `|k| < 1`,
`K(k) = (π/2) ∑ₘ (1/2)ₘ (1/2)ₘ/(m! m!) k^{2m} = (π/2) ₂F₁(1/2, 1/2; 1; k²)`. -/
@[dlmf 19.5.E1]
theorem compEllIntKk_hasSum {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => (π / 2 : ℂ) *
        (poch (1 / 2) m * poch (1 / 2) m / (Nat.factorial m * Nat.factorial m : ℂ)) *
        k ^ (2 * m)) (compEllIntKk k) ∧
      compEllIntKk k = (π / 2 : ℂ) * ₂F₁ (1 / 2 : ℂ) (1 / 2) 1 (k ^ 2) := by
  have h2 : compEllIntKk k = (π / 2 : ℂ) * ₂F₁ (1 / 2 : ℂ) (1 / 2) 1 (k ^ 2) := by
    rw [pi_div_two_mul_ordinaryHypergeometric_half_one hk, compEllIntKk]
  refine ⟨?_, h2⟩
  rw [h2]
  have := (hasSum_gaussHGCoeff_mul_pow (1 / 2) (1 / 2) 1 hk).mul_left (π / 2 : ℂ)
  convert this using 2 with m
  rw [gaussHGCoeff, poch_one_eq_factorial]; ring

/-- DLMF 19.5.2: for `|k| < 1`,
`E(k) = (π/2) ∑ₘ (-1/2)ₘ (1/2)ₘ/(m! m!) k^{2m} = (π/2) ₂F₁(-1/2, 1/2; 1; k²)`. -/
@[dlmf 19.5.E2]
theorem compEllIntEk_hasSum {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => (π / 2 : ℂ) *
        (poch (-(1 / 2)) m * poch (1 / 2) m / (Nat.factorial m * Nat.factorial m : ℂ)) *
        k ^ (2 * m)) (compEllIntEk k) ∧
      compEllIntEk k = (π / 2 : ℂ) * ₂F₁ (-(1 / 2) : ℂ) (1 / 2) 1 (k ^ 2) := by
  have h2 : compEllIntEk k = (π / 2 : ℂ) * ₂F₁ (-(1 / 2) : ℂ) (1 / 2) 1 (k ^ 2) := by
    rw [pi_div_two_mul_ordinaryHypergeometric_half_one hk, compEllIntEk_eq_integral, neg_neg]
  refine ⟨?_, h2⟩
  rw [h2]
  have := (hasSum_gaussHGCoeff_mul_pow (-(1 / 2)) (1 / 2) 1 hk).mul_left (π / 2 : ℂ)
  convert this using 2 with m
  rw [gaussHGCoeff, poch_one_eq_factorial]; ring

/-- DLMF 19.5.3: for `|k| < 1`,
`D(k) = (π/4) ∑ₘ (3/2)ₘ (1/2)ₘ/((m+1)! m!) k^{2m} = (π/4) ₂F₁(3/2, 1/2; 2; k²)`. -/
@[dlmf 19.5.E3]
theorem compEllIntDk_hasSum {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => (π / 4 : ℂ) *
        (poch (3 / 2) m * poch (1 / 2) m / (Nat.factorial (m + 1) * Nat.factorial m : ℂ)) *
        k ^ (2 * m)) (compEllIntDk k) ∧
      compEllIntDk k = (π / 4 : ℂ) * ₂F₁ (3 / 2 : ℂ) (1 / 2) 2 (k ^ 2) := by
  have hG2 : Gamma (2 : ℂ) = 1 := by
    rw [show (2 : ℂ) = 1 + 1 by norm_num, Gamma_add_one _ one_ne_zero, Gamma_one]; norm_num
  have hG32 : Gamma (3 / 2 : ℂ) = 1 / 2 * Gamma (1 / 2) := by
    rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num)]
  have h2 : compEllIntDk k = (π / 4 : ℂ) * ₂F₁ (3 / 2 : ℂ) (1 / 2) 2 (k ^ 2) := by
    rw [ordinaryHypergeometric_symm, ordinaryHypergeometric_eq_integral (by norm_num) (by norm_num)
      (norm_sq_lt_one hk), show (2 : ℂ) - 3 / 2 - 1 = -(1 / 2) by ring,
      show (3 / 2 : ℂ) - 1 = 1 / 2 by ring, show (2 : ℂ) - 3 / 2 = 1 / 2 by ring,
      hG32, hG2]
    have hcongr : ∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (1 / 2 : ℂ) * (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ)) *
        (1 - k ^ 2 * t) ^ (-(1 / 2 : ℂ)) = ∫ t : ℝ in (0 : ℝ)..1,
        (t : ℂ) ^ (-(1 / 2 : ℂ)) * (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ)) *
          ((t : ℂ) * (1 - k ^ 2 * t) ^ (-(1 / 2 : ℂ))) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      rcases eq_or_ne (t : ℂ) 0 with h | h
      · simp [h]
      · rw [show (1 / 2 : ℂ) = -(1 / 2) + 1 by ring, cpow_add _ _ h, cpow_one]; ring_nf
    rw [hcongr, integral_beta_half_weight, compEllIntDk_eq_integral]
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hg := Gamma_one_half_mul_self
    simp only [ofReal_pow]
    rw [mul_assoc (1 / 2 : ℂ), hg]
    set X := ∫ θ in (0 : ℝ)..(π / 2), (Real.sin θ : ℂ) ^ 2 *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))
    field_simp
    ring
  refine ⟨?_, h2⟩
  rw [h2]
  have := (hasSum_gaussHGCoeff_mul_pow (3 / 2) (1 / 2) 2 hk).mul_left (π / 4 : ℂ)
  convert this using 2 with m
  rw [gaussHGCoeff, poch_two_eq_factorial]; ring

/-- Wallis's integral `∫₀^{π/2} sin^{2n} θ dθ = (π/2) ∏_{i<n} (2i+1)/(2i+2)`. -/
private lemma integral_sin_pow_two_mul_real (n : ℕ) :
    ∫ θ in (0 : ℝ)..(π / 2), Real.sin θ ^ (2 * n) =
      π / 2 * ∏ i ∈ Finset.range n, ((2 * i + 1 : ℝ) / (2 * i + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, integral_sin_pow, ih, Finset.prod_range_succ]
    simp
    ring

/-- The ratio recurrence of `(1/2)ₙ/n!`. -/
private lemma poch_half_div_factorial_succ (n : ℕ) :
    poch (1 / 2) (n + 1) / ((n + 1).factorial : ℂ) =
      poch (1 / 2) n / (n.factorial : ℂ) * ((2 * n + 1) / (2 * n + 2)) := by
  rw [poch, ascPochhammer_succ_eval, ← poch, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- Wallis's integral `∫₀^{π/2} sin^{2n} θ dθ = (π/2) (1/2)ₙ/n!`. -/
private lemma integral_sin_pow_two_mul (n : ℕ) :
    ∫ θ in (0 : ℝ)..(π / 2), (Real.sin θ : ℂ) ^ (2 * n) =
      (π / 2 : ℂ) * (poch (1 / 2) n / (n.factorial : ℂ)) := by
  have h : ∫ θ in (0 : ℝ)..(π / 2), (Real.sin θ : ℂ) ^ (2 * n) =
      ((∫ θ in (0 : ℝ)..(π / 2), Real.sin θ ^ (2 * n) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]; push_cast; rfl
  rw [h, integral_sin_pow_two_mul_real]
  push_cast
  congr 1
  clear h
  induction n with
  | zero => simp [poch]
  | succ n ih => rw [Finset.prod_range_succ, ih, poch_half_div_factorial_succ]


/-- `|(1/2)ₙ/n!| ≤ 1`. -/
private lemma norm_poch_half_div_factorial_le (n : ℕ) :
    ‖poch (1 / 2) n / (n.factorial : ℂ)‖ ≤ 1 := by
  induction n with
  | zero => simp [poch]
  | succ n ih =>
    rw [poch_half_div_factorial_succ, norm_mul]
    have h : ‖((2 * n + 1) / (2 * n + 2) : ℂ)‖ ≤ 1 := by
      rw [show ((2 * n + 1) / (2 * n + 2) : ℂ) = (((2 * n + 1) / (2 * n + 2) : ℝ) : ℂ) by
        push_cast; rfl, norm_real, Real.norm_eq_abs, abs_le]
      constructor
      · have : (0 : ℝ) ≤ (2 * n + 1) / (2 * n + 2) := by positivity
        linarith
      · rw [div_le_one (by positivity)]; linarith
    calc _ ≤ 1 * 1 := mul_le_mul ih h (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- The Cauchy-product coefficients of `(1 - α² s)⁻¹ (1 - k² s)^{-1/2}`. -/
private noncomputable def piSeriesCoeff (α2 k : ℂ) (n : ℕ) : ℂ :=
  ∑ m ∈ Finset.range (n + 1), poch (1 / 2) m / (m.factorial : ℂ) * (k ^ 2) ^ m * α2 ^ (n - m)

/-- Absolute convergence of the binomial series of `(1 - k² s)^{-1/2}` for `|s| ≤ 1`. -/
private lemma summable_norm_binomial_half {k : ℂ} (hk : ‖k‖ < 1) {s : ℂ} (hs : ‖s‖ ≤ 1) :
    Summable fun m : ℕ => ‖poch (1 / 2) m / (m.factorial : ℂ) * (k ^ 2) ^ m * s ^ m‖ := by
  have hr : ‖k‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) hk (by decide)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (summable_geometric_of_lt_one (by positivity) hr)
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
  calc _ ≤ 1 * (‖k‖ ^ 2) ^ m * 1 ^ m := by
        gcongr
        · exact norm_poch_half_div_factorial_le m
      _ = (‖k‖ ^ 2) ^ m := by ring

/-- Absolute convergence of the geometric series of `(1 - α² s)⁻¹` for `|s| ≤ 1`. -/
private lemma summable_norm_geometric_mul {α2 : ℂ} (hα : ‖α2‖ < 1) {s : ℂ} (hs : ‖s‖ ≤ 1) :
    Summable fun j : ℕ => ‖α2 ^ j * s ^ j‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
    (summable_geometric_of_lt_one (norm_nonneg _) hα)
  rw [norm_mul, norm_pow, norm_pow]
  calc _ ≤ ‖α2‖ ^ j * 1 ^ j := by gcongr
    _ = _ := by ring

/-- The coefficients `piSeriesCoeff` are absolutely summable. -/
private lemma summable_norm_piSeriesCoeff {α2 k : ℂ} (hk : ‖k‖ < 1) (hα : ‖α2‖ < 1) :
    Summable fun n => ‖piSeriesCoeff α2 k n‖ := by
  have h := summable_norm_sum_mul_range_of_summable_norm
    (summable_norm_binomial_half hk (s := 1) (by simp))
    (summable_norm_geometric_mul hα (s := 1) (by simp))
  simpa [piSeriesCoeff] using h

/-- The Cauchy product of the two series of the integrand of `Π`. -/
private lemma hasSum_piSeriesCoeff_mul {α2 k : ℂ} (hk : ‖k‖ < 1) (hα : ‖α2‖ < 1) {s : ℂ}
    (hs : ‖s‖ ≤ 1) :
    HasSum (fun n => piSeriesCoeff α2 k n * s ^ n)
      ((1 - α2 * s)⁻¹ * (1 - k ^ 2 * s) ^ (-(1 / 2 : ℂ))) := by
  have hks : ‖k ^ 2 * s‖ < 1 := by
    rw [norm_mul, norm_pow]
    calc ‖k‖ ^ 2 * ‖s‖ ≤ ‖k‖ ^ 2 * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact pow_lt_one₀ (norm_nonneg _) hk (by decide)
  have has : ‖α2 * s‖ < 1 := by
    rw [norm_mul]
    calc ‖α2‖ * ‖s‖ ≤ ‖α2‖ * 1 := by gcongr
      _ < 1 := by rwa [mul_one]
  have h1 := hasSum_poch_div_factorial (β := 1 / 2) hks
  have h2 := hasSum_geometric_of_norm_lt_one has
  have hf := summable_norm_binomial_half hk hs
  have hg := summable_norm_geometric_mul hα hs
  have hprod := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg
  have hsum := (summable_norm_sum_mul_range_of_summable_norm hf hg).of_norm
  have e1 : ∑' m : ℕ, poch (1 / 2) m / (m.factorial : ℂ) * (k ^ 2) ^ m * s ^ m =
      (1 - k ^ 2 * s) ^ (-(1 / 2 : ℂ)) := by
    rw [← h1.tsum_eq]; congr 1; funext m; rw [mul_pow]; ring
  have e2 : ∑' j : ℕ, α2 ^ j * s ^ j = (1 - α2 * s)⁻¹ := by
    rw [← h2.tsum_eq]; congr 1; funext j; rw [mul_pow]
  rw [e1, e2] at hprod
  rw [mul_comm, hprod]
  convert hsum.hasSum using 1
  funext n
  rw [piSeriesCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [show s ^ n = s ^ m * s ^ (n - m) by rw [← pow_add, Nat.add_sub_cancel' hmn]]
  ring


/-- For `|α²| < 1` no principal value is needed in `Π(α², k)`. -/
private lemma compEllIntPik_eq_integral_of_norm_lt_one {α2 : ℂ} (hα : ‖α2‖ < 1) (k : ℂ) :
    compEllIntPik α2 k = ∫ θ in (0 : ℝ)..(π / 2), (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  rw [compEllIntPik, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
    incEllIntPik_eq_segmentIntegral (δ := 1 - ‖α2‖) (by linarith), segmentIntegral_ofReal]
  · simp only [← Complex.ofReal_sin]
  · intro t _
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sin]
    have hs : ‖((Real.sin (t * (π / 2)) : ℂ)) ^ 2‖ ≤ 1 := by
      rw [norm_pow, norm_real, Real.norm_eq_abs, sq_abs]; exact Real.sin_sq_le_one _
    calc 1 - ‖α2‖ ≤ ‖(1 : ℂ)‖ - ‖α2 * (Real.sin (t * (π / 2)) : ℂ) ^ 2‖ := by
          rw [norm_one, norm_mul]
          nlinarith [norm_nonneg α2, norm_nonneg ((Real.sin (t * (π / 2)) : ℂ) ^ 2)]
      _ ≤ _ := norm_sub_norm_le _ _

/-- Termwise integration of the series of the integrand of `Π(α², k)`. -/
private lemma hasSum_compEllIntPik_piSeriesCoeff {α2 k : ℂ} (hk : ‖k‖ < 1) (hα : ‖α2‖ < 1) :
    HasSum (fun n => piSeriesCoeff α2 k n * ((π / 2 : ℂ) * (poch (1 / 2) n / (n.factorial : ℂ))))
      (compEllIntPik α2 k) := by
  rw [compEllIntPik_eq_integral_of_norm_lt_one hα]
  have hs (θ : ℝ) : ‖(Real.sin θ : ℂ) ^ 2‖ ≤ 1 := by
    rw [norm_pow, norm_real, Real.norm_eq_abs, sq_abs]; exact Real.sin_sq_le_one _
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := fun n θ => piSeriesCoeff α2 k n * (Real.sin θ : ℂ) ^ (2 * n))
    (fun n _ => ‖piSeriesCoeff α2 k n‖) (μ := MeasureTheory.volume) (a := 0) (b := π / 2)
    (f := fun θ => (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)))
    (fun n => (by fun_prop : Continuous fun θ : ℝ =>
      piSeriesCoeff α2 k n * (Real.sin θ : ℂ) ^ (2 * n)).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun θ _ => by
      rw [norm_mul, pow_mul]
      calc _ ≤ ‖piSeriesCoeff α2 k n‖ * 1 := by
            gcongr; rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hs θ)
        _ = _ := mul_one _)
    (Filter.Eventually.of_forall fun θ _ => summable_norm_piSeriesCoeff hk hα)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ => by
      simpa only [pow_mul] using hasSum_piSeriesCoeff_mul hk hα (hs θ))
  simpa only [intervalIntegral.integral_const_mul, integral_sin_pow_two_mul] using h


/-- The terms of `F₁(1/2; 1/2, 1; 1; k², α²)`. -/
private lemma appellF1Term_half_half_one_one (k α2 : ℂ) (p : ℕ × ℕ) :
    appellF1Term (1 / 2) (1 / 2) 1 1 (k ^ 2) α2 p =
      poch (1 / 2) (p.1 + p.2) / ((p.1 + p.2).factorial : ℂ) *
        (poch (1 / 2) p.1 / (p.1.factorial : ℂ) * (k ^ 2) ^ p.1 * α2 ^ p.2) := by
  rw [appellF1Term, poch_one_eq_factorial, poch_one_eq_factorial]
  have h1 : ((p.1 + p.2).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h2 : (p.1.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h3 : (p.2.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp

/-- Summing `F₁(1/2; 1/2, 1; 1; k², α²)` along antidiagonals. -/
private lemma hasSum_appellF1Term_half_half_one_one {α2 k : ℂ} (hk : ‖k‖ < 1) (hα : ‖α2‖ < 1) :
    HasSum (fun n => piSeriesCoeff α2 k n * (poch (1 / 2) n / (n.factorial : ℂ)))
      (∑' p : ℕ × ℕ, appellF1Term (1 / 2) (1 / 2) 1 1 (k ^ 2) α2 p) := by
  set G := fun p : ℕ × ℕ => appellF1Term (1 / 2) (1 / 2) 1 1 (k ^ 2) α2 p with hG
  have hr : ‖k‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) hk (by decide)
  have hsum : Summable G := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (by positivity) hr).mul_of_nonneg
        (summable_geometric_of_lt_one (norm_nonneg _) hα) (fun _ => by positivity)
        (fun _ => by positivity)) (fun p => ?_)
    rw [hG]
    dsimp only
    rw [appellF1Term_half_half_one_one, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow,
      norm_pow]
    calc _ ≤ 1 * (1 * (‖k‖ ^ 2) ^ p.1 * ‖α2‖ ^ p.2) := by
          gcongr
          · exact norm_poch_half_div_factorial_le _
          · exact norm_poch_half_div_factorial_le _
      _ = _ := by ring
  have h1 := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff (f := G)).mpr
    hsum.hasSum
  have h2 := h1.sigma (fun n => Finset.hasSum (Finset.antidiagonal n) G)
  convert h2 using 1
  funext n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, piSeriesCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [hG]
  dsimp only
  rw [appellF1Term_half_half_one_one, Nat.add_sub_cancel' hmn]
  ring

/-- DLMF 19.5.4: for `|k| < 1` and `|α| < 1` (here `|α²| < 1`),
`Π(α², k) = (π/2) ∑ₙ (1/2)ₙ/n! ∑_{m ≤ n} (1/2)ₘ/m! k^{2m} α^{2n-2m}
= (π/2) F₁(1/2; 1/2, 1; 1; k², α²)`. -/
@[dlmf 19.5.E4]
theorem compEllIntPik_hasSum {α2 k : ℂ} (hk : ‖k‖ < 1) (hα : ‖α2‖ < 1) :
    HasSum (fun n : ℕ => (π / 2 : ℂ) * (poch (1 / 2) n / Nat.factorial n *
        ∑ m ∈ Finset.range (n + 1), poch (1 / 2) m / Nat.factorial m * k ^ (2 * m) * α2 ^ (n - m)))
        (compEllIntPik α2 k) ∧
      compEllIntPik α2 k = (π / 2 : ℂ) * ∑' p : ℕ × ℕ,
          appellF1Term (1 / 2) (1 / 2) 1 1 (k ^ 2) α2 p := by
  have h := hasSum_compEllIntPik_piSeriesCoeff hk hα
  refine ⟨?_, ?_⟩
  · convert h using 1
    funext n
    simp only [piSeriesCoeff, pow_mul]
    ring
  · refine h.unique ?_
    convert (hasSum_appellF1Term_half_half_one_one hk hα).mul_left (π / 2 : ℂ) using 1
    funext n
    ring

/-- **Admitted.** DLMF 19.5.4_1: for real `|φ| < π/2` and `|k| < 1`,
`F(φ, k) = ∑ₘ (1/2)ₘ sin^{2m+1}φ/((2m+1) m!) ₂F₁(m + 1/2, 1/2; m + 3/2; sin²φ) k^{2m}
= sin φ F₁(1/2; 1/2, 1/2; 3/2; sin²φ, k² sin²φ)`. -/
@[dlmf 19.5.E4_1]
theorem incEllIntFk_hasSum {φ : ℝ} (hφ : |φ| < π / 2) {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => poch (1 / 2) m * (Real.sin φ : ℂ) ^ (2 * m + 1) /
        ((2 * m + 1) * Nat.factorial m : ℂ) *
        ₂F₁ ((m : ℂ) + 1 / 2) (1 / 2) ((m : ℂ) + 3 / 2) ((Real.sin φ : ℂ) ^ 2) * k ^ (2 * m))
        (incEllIntFk φ k) ∧
      incEllIntFk φ k = Real.sin φ * ∑' p : ℕ × ℕ,
        appellF1Term (1 / 2) (1 / 2) (1 / 2) (3 / 2) ((Real.sin φ : ℂ) ^ 2)
          (k ^ 2 * (Real.sin φ : ℂ) ^ 2) p := by
  sorry

/-- **Admitted.** DLMF 19.5.4_2: for real `|φ| < π/2` and `|k| < 1`,
`E(φ, k) = ∑ₘ (-1/2)ₘ sin^{2m+1}φ/((2m+1) m!) ₂F₁(m + 1/2, 1/2; m + 3/2; sin²φ) k^{2m}
= sin φ F₁(1/2; 1/2, -1/2; 3/2; sin²φ, k² sin²φ)`. -/
@[dlmf 19.5.E4_2]
theorem incEllIntEk_hasSum {φ : ℝ} (hφ : |φ| < π / 2) {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => poch (-(1 / 2)) m * (Real.sin φ : ℂ) ^ (2 * m + 1) /
        ((2 * m + 1) * Nat.factorial m : ℂ) *
        ₂F₁ ((m : ℂ) + 1 / 2) (1 / 2) ((m : ℂ) + 3 / 2) ((Real.sin φ : ℂ) ^ 2) * k ^ (2 * m))
        (incEllIntEk φ k) ∧
      incEllIntEk φ k = Real.sin φ * ∑' p : ℕ × ℕ,
        appellF1Term (1 / 2) (1 / 2) (-(1 / 2)) (3 / 2) ((Real.sin φ : ℂ) ^ 2)
          (k ^ 2 * (Real.sin φ : ℂ) ^ 2) p := by
  sorry

/-- **Admitted.** DLMF 19.5.4_3: for real `|φ| < π/2`, `|k| < 1` and `|α²| < 1`,
`Π(φ, α², k) = ∑ₘ (1/2)ₘ sin^{2m+1}φ/((2m+1) m!) F₁(m + 1/2; 1/2, 1; m + 3/2; sin²φ, α² sin²φ)
k^{2m}`. -/
@[dlmf 19.5.E4_3]
theorem incEllIntPik_hasSum {φ : ℝ} (hφ : |φ| < π / 2) {α2 k : ℂ} (hk : ‖k‖ < 1)
    (hα : ‖α2‖ < 1) :
    HasSum (fun m : ℕ => poch (1 / 2) m * (Real.sin φ : ℂ) ^ (2 * m + 1) /
        ((2 * m + 1) * Nat.factorial m : ℂ) *
        (∑' p : ℕ × ℕ, appellF1Term ((m : ℂ) + 1 / 2) (1 / 2) 1 ((m : ℂ) + 3 / 2)
          ((Real.sin φ : ℂ) ^ 2) (α2 * (Real.sin φ : ℂ) ^ 2) p) * k ^ (2 * m))
        (incEllIntPik φ α2 k) := by
  sorry

/-- **Admitted.** DLMF 19.5.5: Jacobi's nome `q = exp(-πK'(k)/K(k)) = r + 8r² + 84r³ + 992r⁴ + ⋯`
with `r = k²/16`, as `k → 0+` (the remainder is `O(r⁵)`). -/
@[dlmf 19.5.E5]
theorem jacobiNomek_isBigO :
    (fun k : ℝ => jacobiNomek k - ((k ^ 2 / 16 : ℝ) + 8 * (k ^ 2 / 16 : ℝ) ^ 2 +
        84 * (k ^ 2 / 16 : ℝ) ^ 3 + 992 * (k ^ 2 / 16 : ℝ) ^ 4 : ℂ)) =O[𝓝[>] 0]
      fun k : ℝ => (k ^ 2 / 16) ^ 5 := by
  sorry

/-- **Admitted.** DLMF 19.5.6–19.5.7: with `λ = (1 - √k')/(2(1 + √k'))`,
`q = λ + 2λ⁵ + 15λ⁹ + 150λ¹³ + 1707λ¹⁷ + ⋯` as `k → 0+` (the remainder is `O(λ²¹)`). -/
@[dlmf 19.5.E6, dlmf 19.5.E7]
theorem jacobiNomek_isBigO_lambda :
    let lam : ℝ → ℝ := fun k =>
      (1 - Real.sqrt (Real.sqrt (1 - k ^ 2))) / (2 * (1 + Real.sqrt (Real.sqrt (1 - k ^ 2))))
    (fun k : ℝ => jacobiNomek k - ((lam k + 2 * lam k ^ 5 + 15 * lam k ^ 9 + 150 * lam k ^ 13 +
        1707 * lam k ^ 17 : ℝ) : ℂ)) =O[𝓝[>] 0] fun k : ℝ => lam k ^ 21 := by
  sorry

/-- **Admitted.** DLMF 19.5.8: `K(k) = (π/2)(1 + 2∑_{n ≥ 1} q^{n²})²` with `q = jacobiNomek k`, on
`jacobiModulusDomain` (`Re k > 0`, `k ∉ [1, ∞)`, where `|q| < 1`). -/
@[dlmf 19.5.E8]
theorem compEllIntKk_eq_nome_series {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    compEllIntKk k = (π / 2 : ℂ) * (1 + 2 * ∑' n : ℕ, jacobiNomek k ^ ((n + 1) ^ 2)) ^ 2 := by
  sorry

/-- **Admitted.** DLMF 19.5.9:
`E(k) = K(k) + (2π²/K(k)) ∑_{n≥1} (-1)ⁿ n² q^{n²} / (1 + 2∑_{n≥1} (-1)ⁿ q^{n²})` on
`jacobiModulusDomain`. -/
@[dlmf 19.5.E9]
theorem compEllIntEk_eq_nome_series {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    compEllIntEk k = compEllIntKk k + 2 * π ^ 2 / compEllIntKk k *
      ((∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * ((n + 1 : ℕ) : ℂ) ^ 2 * jacobiNomek k ^ ((n + 1) ^ 2)) /
        (1 + 2 * ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * jacobiNomek k ^ ((n + 1) ^ 2))) := by
  sorry

/-- The descending Landen sequence of moduli of DLMF 19.5.11: `k₀ = k`,
`k_{m+1} = (1 - √(1 - k_m²))/(1 + √(1 - k_m²))` (principal square roots). -/
@[dlmf 19.5.E11]
def landenModulusSeq (k : ℂ) : ℕ → ℂ
  | 0 => k
  | m + 1 =>
    (1 - (1 - landenModulusSeq k m ^ 2) ^ (1 / 2 : ℂ)) /
      (1 + (1 - landenModulusSeq k m ^ 2) ^ (1 / 2 : ℂ))

/-- `‖(1 - c)/(1 + c)‖ < 1` for `ℜ c > 0`. -/
private lemma norm_landen_lt_one {c : ℂ} (hc : 0 < c.re) : ‖(1 - c) / (1 + c)‖ < 1 := by
  have h1c : 1 + c ≠ 0 := fun h => by have := congrArg re h; simp at this; linarith
  rw [norm_div, div_lt_one (norm_pos_iff.2 h1c)]
  have h : ‖1 - c‖ ^ 2 < ‖1 + c‖ ^ 2 := by
    rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
    simp; nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h

/-- The descending Landen modulus satisfies `‖k₁‖ ≤ ‖k‖²`. -/
private lemma norm_landen_le_norm_sq {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    ‖(1 - jacobiComodulusk k) / (1 + jacobiComodulusk k)‖ ≤ ‖k‖ ^ 2 := by
  set c := jacobiComodulusk k
  have hc : 0 < c.re := Carlson.re_cpow_half_pos hk
  have h1c : 1 + c ≠ 0 := fun h => by have := congrArg re h; simp at this; linarith
  have hsq : c ^ 2 = 1 - k ^ 2 := jacobiComodulusk_sq_eq_one_sub_sq k
  have he : (1 - c) / (1 + c) = k ^ 2 / (1 + c) ^ 2 := by
    field_simp; linear_combination -hsq
  have hge : 1 ≤ ‖1 + c‖ := by
    calc (1 : ℝ) ≤ |(1 + c).re| := by simp; rw [abs_of_pos (by linarith)]; linarith
      _ ≤ ‖1 + c‖ := abs_re_le_norm _
  rw [he, norm_div, norm_pow, norm_pow]
  exact div_le_self (by positivity) (one_le_pow₀ hge)

/-- DLMF 19.5.10: `K(k) = (π/2) ∏_{m ≥ 1} (1 + k_m)` with the moduli of 19.5.11, in
the principal domain `1 - k² ∈ ℂ \ (-∞, 0]` (natural-order partial products). Proved by iterating
the complex descending Landen transformation 19.8.12 (`compEllInt_landen_descending`);
`‖k_{m+1}‖ ≤ ‖k_m‖²` gives `k_m → 0`. -/
@[dlmf 19.5.E10]
theorem compEllIntKk_eq_landen_prod {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    Tendsto (fun N => (π / 2 : ℂ) * ∏ m ∈ Finset.range N, (1 + landenModulusSeq k (m + 1))) atTop
      (𝓝 (compEllIntKk k)) := by
  set s := landenModulusSeq k with hs
  have hsucc : ∀ m, s (m + 1) = (1 - jacobiComodulusk (s m)) / (1 + jacobiComodulusk (s m)) :=
    fun m => rfl
  have hmem : ∀ m, 1 - s m ^ 2 ∈ slitPlane := by
    intro m; induction m with
    | zero => exact hk
    | succ m ih => rw [hsucc]; exact one_sub_landen_sq_mem_slitPlane (Carlson.re_cpow_half_pos ih)
  -- the product formula
  have hprod : ∀ N, compEllIntKk k =
      (∏ m ∈ Finset.range N, (1 + s (m + 1))) * compEllIntKk (s N) := by
    intro N; induction N with
    | zero => simp [hs, landenModulusSeq]
    | succ N ih =>
      rw [ih, Finset.prod_range_succ, (compEllInt_landen_descending (hmem N)).1]
      simp only [hsucc]; ring
  -- `s N → 0`
  set r := ‖s 1‖ with hr
  have hr1 : r < 1 := by rw [hr, hsucc]; exact norm_landen_lt_one (Carlson.re_cpow_half_pos hk)
  have hbound : ∀ n, ‖s (n + 1)‖ ≤ r ^ (n + 1) := by
    intro n; induction n with
    | zero => simp [hr]
    | succ n ih =>
      have h1 : ‖s (n + 2)‖ ≤ ‖s (n + 1)‖ ^ 2 := by
        rw [hsucc]; exact norm_landen_le_norm_sq (hmem (n + 1))
      have hr0 : 0 ≤ r := norm_nonneg _
      have h2 : r ^ (n + 1) ≤ r := pow_le_of_le_one hr0 hr1.le (by omega)
      calc ‖s (n + 2)‖ ≤ ‖s (n + 1)‖ ^ 2 := h1
        _ = ‖s (n + 1)‖ * ‖s (n + 1)‖ := sq _
        _ ≤ r ^ (n + 1) * r := mul_le_mul ih (ih.trans h2) (norm_nonneg _) (by positivity)
        _ = r ^ (n + 2) := by ring
  have hlim : Tendsto s atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    refine squeeze_zero_norm hbound ?_
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hr1).comp (tendsto_add_atTop_nat 1)
  have hcont : ContinuousAt compEllIntKk 0 :=
    (differentiableOn_compEllIntKk_compEllIntEk.1.differentiableAt
      (isOpen_setOf_one_sub_sq_mem_slitPlane.mem_nhds (by simp))).continuousAt
  have hK0 : compEllIntKk 0 = π / 2 := by simp [compEllIntKk]
  have hKN : Tendsto (fun N => compEllIntKk (s N)) atTop (𝓝 (π / 2)) := by
    rw [← hK0]; exact hcont.tendsto.comp hlim
  have hpi : (π / 2 : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact div_ne_zero (ofReal_ne_zero.2 this.ne') two_ne_zero
  have hev : ∀ᶠ N in atTop, compEllIntKk (s N) ≠ 0 := hKN.eventually_ne hpi
  have hq := ((tendsto_const_nhds (x := compEllIntKk k)).div hKN hpi).mul_const (π / 2 : ℂ)
  rw [div_mul_cancel₀ _ hpi] at hq
  refine hq.congr' ?_
  filter_upwards [hev] with N hN
  simp only [Pi.div_apply]
  rw [hprod N]; field_simp

end DLMF.EllipticIntegrals
