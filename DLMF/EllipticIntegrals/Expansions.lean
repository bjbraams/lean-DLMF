/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Quadratic
public import DLMF.JacobiElliptic.ModulusInversion
public import DLMF.GeneralizedHypergeometric.Appell.GermTransformations

/-!
# Maclaurin and related expansions of Legendre's integrals (DLMF §19.5)

Complex-modulus forms of DLMF 19.5.1–19.5.11: Maclaurin series of the complete and incomplete
integrals, expansions of Jacobi's nome, the nome series for `K` and `E`, and the descending
Landen product for `K`.

## Main definitions

* `appellF1Term`: the general term of Appell's double series `F₁` (DLMF 16.13.1).
* `landenModulusSeq`: the descending Landen sequence of moduli (DLMF 19.5.11).

## Main results

* `completeEllipticK_hasSum`, `completeEllipticE_hasSum`, `completeEllipticD_hasSum`: the Maclaurin
  series of `K`, `E` and `D` for `|k| < 1` (DLMF 19.5.1–19.5.3).
* `completeEllipticPi_hasSum`: the double series of `Π(α², k)` (DLMF 19.5.4).
* `incompleteEllipticF_hasSum`, `incompleteEllipticE_hasSum`, `incompleteEllipticPi_hasSum`: the
  series of the incomplete integrals (DLMF 19.5.4_1–19.5.4_3).
* `jacobiNome_isBigO`, `jacobiNome_isBigO_lambda`: expansions of the nome as `k → 0+`
  (DLMF 19.5.5–19.5.7).
* `completeEllipticK_eq_nome_series`, `completeEllipticE_eq_nome_series`: `K` and `E` as series in
  the nome (DLMF 19.5.8, 19.5.9).
* `completeEllipticK_eq_landen_prod`: `K(k) = (π/2) ∏_{m ≥ 1} (1 + k_m)` (DLMF 19.5.10).

## Implementation notes

* Series are stated with `HasSum`, and `₂F₁` is Mathlib's `ordinaryHypergeometric`. The
  Appell function is `DLMF.Hypergeometric.appellF1` (DLMF 16.13.1), written explicitly as the
  `tsum` over `ℕ × ℕ` of `appellF1Term` in the statements. Its convergent-series identities
  give the incomplete modulus expansions after Carlson's angular integral representation.
* The nome is the Chapter 22 definition
  `DLMF.JacobiElliptic.jacobiNome k = exp(-πK'(k)/K(k))`, with the literal `K'`, which is
  DLMF's `K'` for `Re k > 0`. The expansions 19.5.5–19.5.6 with "`+ ⋯`" are stated as
  `O`-estimates of the remainder as `k → 0+`.
* The real-parameter forms of 19.5.1–19.5.2 are
  `DLMF.Elliptic.Real.completeEllipticKOfParameter_eq_ordinaryHypergeometric` and
  `Real.completeEllipticEOfParameter_eq_ordinaryHypergeometric` (tagged there). The complex forms of
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
  pochhammer a (p.1 + p.2) * pochhammer b p.1 * pochhammer b' p.2 /
    (pochhammer c (p.1 + p.2) * (Nat.factorial p.1 * Nat.factorial p.2 : ℂ)) * x ^ p.1 * y ^ p.2

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
private lemma hasSum_gaussHypergeometricCoeff_mul_pow (a b c : ℂ) {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => gaussHypergeometricCoeff a b c m * k ^ (2 * m)) (₂F₁ a b c (k ^ 2)) := by
  have h := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).hasSum_mul_pow
    (z := k ^ 2) (by
      rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ← ENNReal.coe_one,
        ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
      exact norm_sq_lt_one hk)
  simpa only [← pow_mul] using h

/-- `(1)ₘ = m!`. -/
private lemma pochhammer_one_eq_factorial (m : ℕ) : pochhammer 1 m = (Nat.factorial m : ℂ) := by
  simp [pochhammer, ascPochhammer_eval_one]

/-- `(2)ₘ = (m+1)!`. -/
private lemma pochhammer_two_eq_factorial (m : ℕ) : pochhammer 2 m =
    (Nat.factorial (m + 1) : ℂ) := by
  induction m with
  | zero => simp [pochhammer]
  | succ n ih =>
    rw [pochhammer, ascPochhammer_succ_eval, ← pochhammer, ih, Nat.factorial_succ (n + 1)]
    push_cast; ring

/-- DLMF 19.5.1: for `|k| < 1`,
`K(k) = (π/2) ∑ₘ (1/2)ₘ (1/2)ₘ/(m! m!) k^{2m} = (π/2) ₂F₁(1/2, 1/2; 1; k²)`. -/
@[dlmf 19.5.E1]
theorem completeEllipticK_hasSum {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => (π / 2 : ℂ) *
        (pochhammer (1 / 2) m * pochhammer (1 / 2) m / (Nat.factorial m * Nat.factorial m : ℂ)) *
        k ^ (2 * m)) (completeEllipticK k) ∧
      completeEllipticK k = (π / 2 : ℂ) * ₂F₁ (1 / 2 : ℂ) (1 / 2) 1 (k ^ 2) := by
  have h2 : completeEllipticK k = (π / 2 : ℂ) * ₂F₁ (1 / 2 : ℂ) (1 / 2) 1 (k ^ 2) := by
    rw [pi_div_two_mul_ordinaryHypergeometric_half_one hk, completeEllipticK]
  refine ⟨?_, h2⟩
  rw [h2]
  have := (hasSum_gaussHypergeometricCoeff_mul_pow (1 / 2) (1 / 2) 1 hk).mul_left (π / 2 : ℂ)
  convert this using 2 with m
  rw [gaussHypergeometricCoeff, pochhammer_one_eq_factorial]; ring

/-- DLMF 19.5.2: for `|k| < 1`,
`E(k) = (π/2) ∑ₘ (-1/2)ₘ (1/2)ₘ/(m! m!) k^{2m} = (π/2) ₂F₁(-1/2, 1/2; 1; k²)`. -/
@[dlmf 19.5.E2]
theorem completeEllipticE_hasSum {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => (π / 2 : ℂ) *
        (pochhammer (-(1 / 2)) m * pochhammer (1 / 2) m / (Nat.factorial m * Nat.factorial m : ℂ)) *
        k ^ (2 * m)) (completeEllipticE k) ∧
      completeEllipticE k = (π / 2 : ℂ) * ₂F₁ (-(1 / 2) : ℂ) (1 / 2) 1 (k ^ 2) := by
  have h2 : completeEllipticE k = (π / 2 : ℂ) * ₂F₁ (-(1 / 2) : ℂ) (1 / 2) 1 (k ^ 2) := by
    rw [pi_div_two_mul_ordinaryHypergeometric_half_one hk, completeEllipticE_eq_integral, neg_neg]
  refine ⟨?_, h2⟩
  rw [h2]
  have := (hasSum_gaussHypergeometricCoeff_mul_pow (-(1 / 2)) (1 / 2) 1 hk).mul_left (π / 2 : ℂ)
  convert this using 2 with m
  rw [gaussHypergeometricCoeff, pochhammer_one_eq_factorial]; ring

/-- DLMF 19.5.3: for `|k| < 1`,
`D(k) = (π/4) ∑ₘ (3/2)ₘ (1/2)ₘ/((m+1)! m!) k^{2m} = (π/4) ₂F₁(3/2, 1/2; 2; k²)`. -/
@[dlmf 19.5.E3]
theorem completeEllipticD_hasSum {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => (π / 4 : ℂ) *
        (pochhammer (3 / 2) m * pochhammer (1 / 2) m /
            (Nat.factorial (m + 1) * Nat.factorial m : ℂ)) *
        k ^ (2 * m)) (completeEllipticD k) ∧
      completeEllipticD k = (π / 4 : ℂ) * ₂F₁ (3 / 2 : ℂ) (1 / 2) 2 (k ^ 2) := by
  have hG2 : Gamma (2 : ℂ) = 1 := by
    rw [show (2 : ℂ) = 1 + 1 by norm_num, Gamma_add_one _ one_ne_zero, Gamma_one]; norm_num
  have hG32 : Gamma (3 / 2 : ℂ) = 1 / 2 * Gamma (1 / 2) := by
    rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num)]
  have h2 : completeEllipticD k = (π / 4 : ℂ) * ₂F₁ (3 / 2 : ℂ) (1 / 2) 2 (k ^ 2) := by
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
    rw [hcongr, integral_beta_half_weight, completeEllipticD_eq_integral]
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
  have := (hasSum_gaussHypergeometricCoeff_mul_pow (3 / 2) (1 / 2) 2 hk).mul_left (π / 4 : ℂ)
  convert this using 2 with m
  rw [gaussHypergeometricCoeff, pochhammer_two_eq_factorial]; ring

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
private lemma pochhammer_half_div_factorial_succ (n : ℕ) :
    pochhammer (1 / 2) (n + 1) / ((n + 1).factorial : ℂ) =
      pochhammer (1 / 2) n / (n.factorial : ℂ) * ((2 * n + 1) / (2 * n + 2)) := by
  rw [pochhammer, ascPochhammer_succ_eval, ← pochhammer, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- Wallis's integral `∫₀^{π/2} sin^{2n} θ dθ = (π/2) (1/2)ₙ/n!`. -/
private lemma integral_sin_pow_two_mul (n : ℕ) :
    ∫ θ in (0 : ℝ)..(π / 2), (Real.sin θ : ℂ) ^ (2 * n) =
      (π / 2 : ℂ) * (pochhammer (1 / 2) n / (n.factorial : ℂ)) := by
  have h : ∫ θ in (0 : ℝ)..(π / 2), (Real.sin θ : ℂ) ^ (2 * n) =
      ((∫ θ in (0 : ℝ)..(π / 2), Real.sin θ ^ (2 * n) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]; push_cast; rfl
  rw [h, integral_sin_pow_two_mul_real]
  push_cast
  congr 1
  clear h
  induction n with
  | zero => simp [pochhammer]
  | succ n ih => rw [Finset.prod_range_succ, ih, pochhammer_half_div_factorial_succ]


/-- `|(1/2)ₙ/n!| ≤ 1`. -/
private lemma norm_pochhammer_half_div_factorial_le (n : ℕ) :
    ‖pochhammer (1 / 2) n / (n.factorial : ℂ)‖ ≤ 1 := by
  induction n with
  | zero => simp [pochhammer]
  | succ n ih =>
    rw [pochhammer_half_div_factorial_succ, norm_mul]
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
  ∑ m ∈ Finset.range (n + 1), pochhammer (1 / 2) m / (m.factorial : ℂ) * (k ^ 2) ^ m * α2 ^ (n - m)

/-- Absolute convergence of the binomial series of `(1 - k² s)^{-1/2}` for `|s| ≤ 1`. -/
private lemma summable_norm_binomial_half {k : ℂ} (hk : ‖k‖ < 1) {s : ℂ} (hs : ‖s‖ ≤ 1) :
    Summable fun m : ℕ => ‖pochhammer (1 / 2) m / (m.factorial : ℂ) * (k ^ 2) ^ m * s ^ m‖ := by
  have hr : ‖k‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) hk (by decide)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (summable_geometric_of_lt_one (by positivity) hr)
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
  calc _ ≤ 1 * (‖k‖ ^ 2) ^ m * 1 ^ m := by
        gcongr
        · exact norm_pochhammer_half_div_factorial_le m
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
  have h1 := hasSum_pochhammer_div_factorial (β := 1 / 2) hks
  have h2 := hasSum_geometric_of_norm_lt_one has
  have hf := summable_norm_binomial_half hk hs
  have hg := summable_norm_geometric_mul hα hs
  have hprod := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg
  have hsum := (summable_norm_sum_mul_range_of_summable_norm hf hg).of_norm
  have e1 : ∑' m : ℕ, pochhammer (1 / 2) m / (m.factorial : ℂ) * (k ^ 2) ^ m * s ^ m =
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
private lemma completeEllipticPi_eq_integral_of_norm_lt_one {α2 : ℂ} (hα : ‖α2‖ < 1) (k : ℂ) :
    completeEllipticPi α2 k = ∫ θ in (0 : ℝ)..(π / 2), (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  rw [completeEllipticPi, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
    incompleteEllipticPi_eq_primitive (δ := 1 - ‖α2‖) (by linarith),
        primitive_ofReal]
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
private lemma hasSum_completeEllipticPi_piSeriesCoeff {α2 k : ℂ} (hk : ‖k‖ < 1) (hα : ‖α2‖ < 1) :
    HasSum (fun n => piSeriesCoeff α2 k n *
        ((π / 2 : ℂ) * (pochhammer (1 / 2) n / (n.factorial : ℂ))))
      (completeEllipticPi α2 k) := by
  rw [completeEllipticPi_eq_integral_of_norm_lt_one hα]
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
      pochhammer (1 / 2) (p.1 + p.2) / ((p.1 + p.2).factorial : ℂ) *
        (pochhammer (1 / 2) p.1 / (p.1.factorial : ℂ) * (k ^ 2) ^ p.1 * α2 ^ p.2) := by
  rw [appellF1Term, pochhammer_one_eq_factorial, pochhammer_one_eq_factorial]
  have h1 : ((p.1 + p.2).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h2 : (p.1.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h3 : (p.2.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp

/-- Summing `F₁(1/2; 1/2, 1; 1; k², α²)` along antidiagonals. -/
private lemma hasSum_appellF1Term_half_half_one_one {α2 k : ℂ} (hk : ‖k‖ < 1) (hα : ‖α2‖ < 1) :
    HasSum (fun n => piSeriesCoeff α2 k n * (pochhammer (1 / 2) n / (n.factorial : ℂ)))
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
          · exact norm_pochhammer_half_div_factorial_le _
          · exact norm_pochhammer_half_div_factorial_le _
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
theorem completeEllipticPi_hasSum {α2 k : ℂ} (hk : ‖k‖ < 1) (hα : ‖α2‖ < 1) :
    HasSum (fun n : ℕ => (π / 2 : ℂ) * (pochhammer (1 / 2) n / Nat.factorial n *
        ∑ m ∈ Finset.range (n + 1), pochhammer (1 / 2) m / Nat.factorial m *
            k ^ (2 * m) * α2 ^ (n - m)))
        (completeEllipticPi α2 k) ∧
      completeEllipticPi α2 k = (π / 2 : ℂ) * ∑' p : ℕ × ℕ,
          appellF1Term (1 / 2) (1 / 2) 1 1 (k ^ 2) α2 p := by
  have h := hasSum_completeEllipticPi_piSeriesCoeff hk hα
  refine ⟨?_, ?_⟩
  · convert h using 1
    funext n
    simp only [piSeriesCoeff, pow_mul]
    ring
  · refine h.unique ?_
    convert (hasSum_appellF1Term_half_half_one_one hk hα).mul_left (π / 2 : ℂ) using 1
    funext n
    ring

/-- The first two Appell variables of an incomplete elliptic integral lie in the unit bidisc. -/
private lemma norm_sin_sq_lt_one {φ : ℝ} (hφ : |φ| < π / 2) :
    ‖(Real.sin φ : ℂ) ^ 2‖ < 1 := by
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hφ)
  rw [norm_pow, norm_real, Real.norm_eq_abs, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq φ]

/-- The binomial angular integral is an Appell function on its convergent bidisc. -/
private lemma integral_incomplete_binomial_eq_appellF1_pos (a : ℂ) {φ : ℝ}
    (hφ : 0 < φ) (hφ' : φ < π / 2) {k : ℂ} (hk : ‖k‖ < 1) :
    (∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-a)) =
      Real.sin φ * DLMF.Hypergeometric.appellF1 (1 / 2) (1 / 2) a (3 / 2)
        ((Real.sin φ : ℂ) ^ 2) (k ^ 2 * (Real.sin φ : ℂ) ^ 2) := by
  classical
  set X : ℂ := (Real.sin φ : ℂ) ^ 2
  set Y : ℂ := k ^ 2 * X
  have hX : ‖X‖ < 1 := norm_sin_sq_lt_one (by rw [abs_of_pos hφ]; exact hφ')
  have hY : ‖Y‖ < 1 := by
    dsimp [Y]
    rw [norm_mul]
    calc ‖k ^ 2‖ * ‖X‖ ≤ ‖k ^ 2‖ * 1 := by gcongr
      _ < 1 := by simpa using norm_sq_lt_one hk
  have hslit : ∀ s ∈ Icc (0 : ℝ) (Real.sin φ ^ 2), 1 - k ^ 2 * (s : ℂ) ∈ slitPlane := by
    intro s hs
    have hs1 : s ≤ 1 := hs.2.trans (Real.sin_sq_le_one _)
    exact one_sub_mul_ofReal_mem_slitPlane (by
      left
      have h := (re_le_norm (k ^ 2)).trans_lt (norm_sq_lt_one hk)
      simp only [sub_re, one_re]
      linarith) hs.1 hs1
  have H := Carlson.integral_sin_cos_cpow (a := (1 / 2 : ℂ)) (β := (1 / 2 : ℂ))
    (γ := a) (δ := (0 : ℂ)) (k := k) (α := (0 : ℂ)) hφ hφ' (by norm_num)
    hslit (by intro s hs; simp)
  have hSin : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ (by linarith)
  have hsroot : ((Real.sin φ : ℂ) ^ 2) ^ (1 / 2 : ℂ) = Real.sin φ := by
    rw [← ofReal_pow, Carlson.ofReal_cpow_half (sq_nonneg _), Real.sqrt_sq hSin.le]
  have hcos : (Real.cos φ : ℂ) ^ 2 = 1 - X := by
    dsimp [X]
    exact_mod_cast (show Real.cos φ ^ 2 = 1 - Real.sin φ ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq φ])
  let q : Fin 4 → Fin 2 ⊕ Unit := ![Sum.inl 0, Sum.inl 1, Sum.inr (), Sum.inr ()]
  have hq : Function.Surjective q := by
    intro i
    cases i with
    | inl i => fin_cases i
               · exact ⟨0, rfl⟩
               · exact ⟨1, rfl⟩
    | inr i => exact ⟨2, by cases i; rfl⟩
  have hn : (![1 - X, 1 - Y, 1, 1] : Fin 4 → ℂ) =
      Carlson.appellCarlsonNodes X Y ∘ q := by
    funext i
    fin_cases i <;> rfl
  have hz : Carlson.appellCarlsonNodes X Y ∈ Carlson.carlsonRSlitDomain := by
    intro i
    cases i with
    | inl i =>
      fin_cases i
      · left
        simp [Carlson.appellCarlsonNodes, Carlson.TwoVariable.pair]
        linarith [re_le_norm X]
      · left
        simp [Carlson.appellCarlsonNodes, Carlson.TwoVariable.pair]
        linarith [re_le_norm Y]
    | inr i => simp [Carlson.appellCarlsonNodes]
  have hagg : stdSimplexAggregate q (![1 / 2, a, 1 - a, 0] : Fin 4 → ℂ) =
      Carlson.appellDirichletParameters (1 / 2) a (3 / 2) := by
    funext i
    rw [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
    cases i with
    | inl i =>
      fin_cases i <;>
        simp [q, Fin.sum_univ_four, Carlson.appellDirichletParameters,
          Carlson.TwoVariable.pair]
    | inr i =>
      cases i
      simp [q, Fin.sum_univ_four, Carlson.appellDirichletParameters]
      ring
  norm_num only [show (2 * (1 / 2) - 1 : ℂ) = 0 by norm_num,
    show (1 - 2 * (1 / 2) : ℂ) = 0 by norm_num, cpow_zero, mul_one,
    one_mul, neg_zero, zero_pow two_ne_zero, zero_mul, sub_zero, one_cpow] at H
  rw [hsroot, hcos] at H
  change (∫ θ in Ioo (0 : ℝ) φ, (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-a)) =
    1 / 2 * Gamma (1 / 2) * (Real.sin φ : ℂ) *
      Carlson.regCarlsonR (-(1 / 2)) ![1 / 2, a, 1 - a, 0] ![1 - X, 1 - Y, 1, 1] at H
  rw [hn, Carlson.regCarlsonR_aggregate_of_slit hq _ hz, hagg] at H
  have hA := appellF1_eq_gamma_mul_regCarlsonR (1 / 2) (1 / 2) a (3 / 2)
    (not_neg_nat_of_re_pos (by norm_num)) hX hY
  rw [intervalIntegral.integral_of_le hφ.le, MeasureTheory.integral_Ioc_eq_integral_Ioo, H,
    hA, Carlson.Gamma_three_halves]
  ring

/-- Oddness extends the angular Appell representation to negative real amplitudes. -/
private lemma integral_incomplete_binomial_eq_appellF1 (a : ℂ) {φ : ℝ}
    (hφ : |φ| < π / 2) {k : ℂ} (hk : ‖k‖ < 1) :
    (∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-a)) =
      Real.sin φ * DLMF.Hypergeometric.appellF1 (1 / 2) (1 / 2) a (3 / 2)
        ((Real.sin φ : ℂ) ^ 2) (k ^ 2 * (Real.sin φ : ℂ) ^ 2) := by
  rcases lt_trichotomy φ 0 with hn | rfl | hp
  · have H := integral_incomplete_binomial_eq_appellF1_pos a (neg_pos.mpr hn)
      (by rw [abs_of_neg hn] at hφ; exact hφ) hk
    have hsub := intervalIntegral.integral_comp_neg (a := 0) (b := -φ)
      (fun θ : ℝ => (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-a))
    simp only [Real.sin_neg, ofReal_neg, neg_sq, neg_zero, neg_neg] at hsub H
    rw [hsub, intervalIntegral.integral_symm] at H
    linear_combination -H
  · simp
  · exact integral_incomplete_binomial_eq_appellF1_pos a hp ((abs_lt.mp hφ).2) hk

/-- Summing Appell's first coordinate gives the modulus series of the incomplete integral. -/
private lemma hasSum_integral_incomplete_binomial (a : ℂ) {φ : ℝ}
    (hφ : |φ| < π / 2) {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => pochhammer a m * (Real.sin φ : ℂ) ^ (2 * m + 1) /
      ((2 * m + 1) * Nat.factorial m : ℂ) *
        ₂F₁ ((m : ℂ) + 1 / 2) (1 / 2) ((m : ℂ) + 3 / 2)
          ((Real.sin φ : ℂ) ^ 2) * k ^ (2 * m))
      (∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-a)) := by
  have hX := norm_sin_sq_lt_one hφ
  have hY : ‖k ^ 2 * (Real.sin φ : ℂ) ^ 2‖ < 1 := by
    rw [norm_mul]
    calc ‖k ^ 2‖ * ‖(Real.sin φ : ℂ) ^ 2‖ ≤ ‖k ^ 2‖ * 1 := by gcongr
      _ < 1 := by simpa using norm_sq_lt_one hk
  have H := (hasSum_appellF1_gauss_fibers (1 / 2) a (1 / 2) (3 / 2)
    (not_neg_nat_of_re_pos (by norm_num)) hY hX).mul_left (Real.sin φ : ℂ)
  rw [integral_incomplete_binomial_eq_appellF1 a hφ hk, appellF1_swap]
  refine H.congr_fun fun m => ?_
  rw [pochhammer_three_halves_eq]
  have hP := pochhammer_ne_zero_of_re_pos (z := (1 / 2 : ℂ)) (by norm_num) m
  have hm : (2 * m + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * m + 1 : ℕ) ≠ 0 by omega)
  have hf : (Nat.factorial m : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  rw [mul_pow, ← pow_mul, ← pow_mul,
    show ((1 / 2 : ℂ) + m) = m + 1 / 2 by ring,
    show ((3 / 2 : ℂ) + m) = m + 3 / 2 by ring]
  push_cast
  field_simp
  ring

/-- DLMF 19.5.4_1: for real `|φ| < π/2` and `|k| < 1`,
`F(φ, k) = ∑ₘ (1/2)ₘ sin^{2m+1}φ/((2m+1) m!) ₂F₁(m + 1/2, 1/2; m + 3/2; sin²φ) k^{2m}
= sin φ F₁(1/2; 1/2, 1/2; 3/2; sin²φ, k² sin²φ)`. -/
@[dlmf 19.5.E4_1]
theorem incompleteEllipticF_hasSum {φ : ℝ} (hφ : |φ| < π / 2) {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => pochhammer (1 / 2) m * (Real.sin φ : ℂ) ^ (2 * m + 1) /
        ((2 * m + 1) * Nat.factorial m : ℂ) *
        ₂F₁ ((m : ℂ) + 1 / 2) (1 / 2) ((m : ℂ) + 3 / 2) ((Real.sin φ : ℂ) ^ 2) * k ^ (2 * m))
        (incompleteEllipticF φ k) ∧
      incompleteEllipticF φ k = Real.sin φ * ∑' p : ℕ × ℕ,
        appellF1Term (1 / 2) (1 / 2) (1 / 2) (3 / 2) ((Real.sin φ : ℂ) ^ 2)
          (k ^ 2 * (Real.sin φ : ℂ) ^ 2) p := by
  constructor
  · rw [incompleteEllipticF_ofReal_eq_integral]
    exact hasSum_integral_incomplete_binomial (1 / 2) hφ hk
  · rw [incompleteEllipticF_ofReal_eq_integral,
      integral_incomplete_binomial_eq_appellF1 (1 / 2) hφ hk]
    rfl

/-- DLMF 19.5.4_2: for real `|φ| < π/2` and `|k| < 1`,
`E(φ, k) = ∑ₘ (-1/2)ₘ sin^{2m+1}φ/((2m+1) m!) ₂F₁(m + 1/2, 1/2; m + 3/2; sin²φ) k^{2m}
= sin φ F₁(1/2; 1/2, -1/2; 3/2; sin²φ, k² sin²φ)`. -/
@[dlmf 19.5.E4_2]
theorem incompleteEllipticE_hasSum {φ : ℝ} (hφ : |φ| < π / 2) {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => pochhammer (-(1 / 2)) m * (Real.sin φ : ℂ) ^ (2 * m + 1) /
        ((2 * m + 1) * Nat.factorial m : ℂ) *
        ₂F₁ ((m : ℂ) + 1 / 2) (1 / 2) ((m : ℂ) + 3 / 2) ((Real.sin φ : ℂ) ^ 2) * k ^ (2 * m))
        (incompleteEllipticE φ k) ∧
      incompleteEllipticE φ k = Real.sin φ * ∑' p : ℕ × ℕ,
        appellF1Term (1 / 2) (1 / 2) (-(1 / 2)) (3 / 2) ((Real.sin φ : ℂ) ^ 2)
          (k ^ 2 * (Real.sin φ : ℂ) ^ 2) p := by
  constructor
  · rw [incompleteEllipticE_ofReal_eq_integral]
    simpa only [neg_neg] using hasSum_integral_incomplete_binomial (-(1 / 2)) hφ hk
  · rw [incompleteEllipticE_ofReal_eq_integral]
    have H := integral_incomplete_binomial_eq_appellF1 (-(1 / 2)) hφ hk
    simpa only [neg_neg, DLMF.Hypergeometric.appellF1, appellF1Coeff, appellF1Term,
      Nat.cast_mul] using H

/-- The even sine moments of the third-kind denominator are Appell functions. -/
private lemma integral_sin_pow_div_eq_appellF1_pos (m : ℕ) {φ : ℝ}
    (hφ : 0 < φ) (hφ' : φ < π / 2) {α2 : ℂ} (hα : ‖α2‖ < 1) :
    (∫ θ in (0 : ℝ)..φ, (Real.sin θ : ℂ) ^ (2 * m) *
      (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹) =
      (Real.sin φ : ℂ) ^ (2 * m + 1) / (2 * m + 1) *
        DLMF.Hypergeometric.appellF1 ((m : ℂ) + 1 / 2) (1 / 2) 1 ((m : ℂ) + 3 / 2)
          ((Real.sin φ : ℂ) ^ 2) (α2 * (Real.sin φ : ℂ) ^ 2) := by
  classical
  set X : ℂ := (Real.sin φ : ℂ) ^ 2
  set Y : ℂ := α2 * X
  set A : ℂ := (m : ℂ) + 1 / 2
  have hA : 0 < A.re := by dsimp [A]; simp; positivity
  have hX : ‖X‖ < 1 := norm_sin_sq_lt_one (by rw [abs_of_pos hφ]; exact hφ')
  have hY : ‖Y‖ < 1 := by
    dsimp [Y]
    rw [norm_mul]
    calc ‖α2‖ * ‖X‖ ≤ ‖α2‖ * 1 := by gcongr
      _ < 1 := by simpa using hα
  have hslit : ∀ s ∈ Icc (0 : ℝ) (Real.sin φ ^ 2), 1 - α2 * (s : ℂ) ∈ slitPlane := by
    intro s hs
    exact one_sub_mul_ofReal_mem_slitPlane (by
      left; simp only [sub_re, one_re]; linarith [re_le_norm α2]) hs.1
      (hs.2.trans (Real.sin_sq_le_one _))
  have H := Carlson.integral_sin_cos_cpow (a := A) (β := (1 / 2 : ℂ))
    (γ := (0 : ℂ)) (δ := (1 : ℂ)) (k := (0 : ℂ)) (α := α2 ^ (1 / 2 : ℂ))
    hφ hφ' hA (by intro s hs; simp)
    (by intro s hs; rw [Carlson.cpow_half_sq]; exact hslit s hs)
  have hSin : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ (by linarith)
  have hsroot : ((Real.sin φ : ℂ) ^ 2) ^ A = (Real.sin φ : ℂ) ^ (2 * m + 1) := by
    rw [Carlson.ofReal_sq_cpow hSin,
      show 2 * A = ((2 * m + 1 : ℕ) : ℂ) by dsimp [A]; push_cast; ring, cpow_natCast]
  have hcos : (Real.cos φ : ℂ) ^ 2 = 1 - X := by
    dsimp [X]
    exact_mod_cast (show Real.cos φ ^ 2 = 1 - Real.sin φ ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq φ])
  let q : Fin 4 → Fin 2 ⊕ Unit := ![Sum.inl 0, Sum.inr (), Sum.inr (), Sum.inl 1]
  have hq : Function.Surjective q := by
    intro i
    cases i with
    | inl i => fin_cases i
               · exact ⟨0, rfl⟩
               · exact ⟨3, rfl⟩
    | inr i => exact ⟨1, by cases i; rfl⟩
  have hn : (![1 - X, 1, 1, 1 - Y] : Fin 4 → ℂ) =
      Carlson.appellCarlsonNodes X Y ∘ q := by
    funext i
    fin_cases i <;> rfl
  have hz : Carlson.appellCarlsonNodes X Y ∈ Carlson.carlsonRSlitDomain := by
    intro i
    cases i with
    | inl i =>
      fin_cases i
      · left
        simp [Carlson.appellCarlsonNodes, Carlson.TwoVariable.pair]
        linarith [re_le_norm X]
      · left
        simp [Carlson.appellCarlsonNodes, Carlson.TwoVariable.pair]
        linarith [re_le_norm Y]
    | inr i => simp [Carlson.appellCarlsonNodes]
  have hagg : stdSimplexAggregate q (![1 / 2, 0, A - 1 / 2, 1] : Fin 4 → ℂ) =
      Carlson.appellDirichletParameters (1 / 2) 1 (A + 1) := by
    funext i
    rw [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
    cases i with
    | inl i =>
      fin_cases i <;>
        simp [q, Fin.sum_univ_four, Carlson.appellDirichletParameters,
          Carlson.TwoVariable.pair]
    | inr i =>
      cases i
      simp [q, Fin.sum_univ_four, Carlson.appellDirichletParameters]
      ring
  have hexp : (2 * A - 1) = ((2 * m : ℕ) : ℂ) := by dsimp [A]; push_cast; ring
  norm_num only [hexp, show (1 - 2 * (1 / 2) : ℂ) = 0 by norm_num,
    cpow_natCast, cpow_zero, mul_one, one_mul, neg_zero, zero_pow two_ne_zero,
    zero_mul, sub_zero, cpow_neg_one, Carlson.cpow_half_sq] at H
  rw [hsroot, hcos, show (1 + A - 1 / 2 - 1 : ℂ) = A - 1 / 2 by ring] at H
  change (∫ θ in Ioo (0 : ℝ) φ, (Real.sin θ : ℂ) ^ (2 * m) *
    (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹) =
    1 / 2 * Gamma A * (Real.sin φ : ℂ) ^ (2 * m + 1) *
      Carlson.regCarlsonR (-A) ![1 / 2, 0, A - 1 / 2, 1] ![1 - X, 1, 1, 1 - Y] at H
  rw [hn, Carlson.regCarlsonR_aggregate_of_slit hq _ hz, hagg] at H
  have hF := appellF1_eq_gamma_mul_regCarlsonR A (1 / 2) 1 (A + 1)
    (not_neg_nat_of_re_pos (by simp; linarith)) hX hY
  have hm : (2 * m + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * m + 1 : ℕ) ≠ 0 by omega)
  rw [show (m : ℂ) + 3 / 2 = A + 1 by dsimp [A]; ring]
  change _ = (Real.sin φ : ℂ) ^ (2 * m + 1) / (2 * m + 1) *
    DLMF.Hypergeometric.appellF1 A (1 / 2) 1 (A + 1) X Y
  rw [intervalIntegral.integral_of_le hφ.le, MeasureTheory.integral_Ioc_eq_integral_Ioo, H,
    hF, Gamma_add_one A (ne_zero_of_re_pos hA)]
  dsimp [A]
  field_simp

/-- The Appell moment formula is odd in the amplitude. -/
private lemma integral_sin_pow_div_eq_appellF1 (m : ℕ) {φ : ℝ}
    (hφ : |φ| < π / 2) {α2 : ℂ} (hα : ‖α2‖ < 1) :
    (∫ θ in (0 : ℝ)..φ, (Real.sin θ : ℂ) ^ (2 * m) *
      (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹) =
      (Real.sin φ : ℂ) ^ (2 * m + 1) / (2 * m + 1) *
        DLMF.Hypergeometric.appellF1 ((m : ℂ) + 1 / 2) (1 / 2) 1 ((m : ℂ) + 3 / 2)
          ((Real.sin φ : ℂ) ^ 2) (α2 * (Real.sin φ : ℂ) ^ 2) := by
  have hpow (z : ℂ) : (-z) ^ (2 * m) = z ^ (2 * m) := by simp only [pow_mul, neg_sq]
  have hodd (z : ℂ) : (-z) ^ (2 * m + 1) = -(z ^ (2 * m + 1)) := by
    rw [pow_succ, hpow, pow_succ, mul_neg]
  rcases lt_trichotomy φ 0 with hn | rfl | hp
  · have H := integral_sin_pow_div_eq_appellF1_pos m (neg_pos.mpr hn)
      (by rw [abs_of_neg hn] at hφ; exact hφ) hα
    have hsub := intervalIntegral.integral_comp_neg (a := 0) (b := -φ)
      (fun θ : ℝ => (Real.sin θ : ℂ) ^ (2 * m) *
        (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹)
    simp only [Real.sin_neg, ofReal_neg, hpow, neg_sq, neg_zero, neg_neg] at hsub
    rw [hsub, intervalIntegral.integral_symm] at H
    simp only [Real.sin_neg, ofReal_neg, hodd, neg_sq] at H
    linear_combination -H
  · simp
  · exact integral_sin_pow_div_eq_appellF1_pos m hp ((abs_lt.mp hφ).2) hα

/-- No pole of the third-kind denominator occurs for a characteristic of norm less than one. -/
private lemma incompleteEllipticPi_real_eq_integral_of_norm_lt_one (φ : ℝ) {α2 : ℂ}
    (hα : ‖α2‖ < 1) (k : ℂ) :
    incompleteEllipticPi φ α2 k = ∫ θ in (0 : ℝ)..φ,
      (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  rw [incompleteEllipticPi_eq_primitive (δ := 1 - ‖α2‖) (by linarith),
    DLMF.Core.primitive_ofReal]
  · simp only [← Complex.ofReal_sin]
  · intro t ht
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sin]
    have hs : ‖(Real.sin (t * φ) : ℂ) ^ 2‖ ≤ 1 := by
      rw [norm_pow, norm_real, Real.norm_eq_abs, sq_abs]
      exact Real.sin_sq_le_one _
    calc 1 - ‖α2‖ ≤ ‖(1 : ℂ)‖ - ‖α2 * (Real.sin (t * φ) : ℂ) ^ 2‖ := by
          rw [norm_one, norm_mul]
          nlinarith [norm_nonneg α2]
      _ ≤ _ := norm_sub_norm_le _ _

/-- Termwise integration of the binomial series for an incomplete integral of the third kind. -/
private lemma hasSum_incompleteEllipticPi_moments {φ : ℝ} {α2 k : ℂ}
    (hk : ‖k‖ < 1) (hα : ‖α2‖ < 1) :
    HasSum (fun m : ℕ => (pochhammer (1 / 2) m / (m.factorial : ℂ) * k ^ (2 * m)) *
      ∫ θ in (0 : ℝ)..φ, (Real.sin θ : ℂ) ^ (2 * m) *
        (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹) (incompleteEllipticPi φ α2 k) := by
  let c : ℕ → ℂ := fun m => pochhammer (1 / 2) m / (m.factorial : ℂ) * k ^ (2 * m)
  have hs (θ : ℝ) : ‖(Real.sin θ : ℂ) ^ 2‖ ≤ 1 := by
    rw [norm_pow, norm_real, Real.norm_eq_abs, sq_abs]
    exact Real.sin_sq_le_one _
  have hc : Summable fun m => ‖c m‖ := by
    simpa only [c, pow_mul, one_pow, mul_one] using
      summable_norm_binomial_half hk (s := 1) (by simp)
  have hb (θ : ℝ) : ‖(1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹‖ ≤ (1 - ‖α2‖)⁻¹ := by
    rw [norm_inv]
    have hL : 1 - ‖α2‖ ≤ ‖1 - α2 * (Real.sin θ : ℂ) ^ 2‖ := by
      calc 1 - ‖α2‖ ≤ ‖(1 : ℂ)‖ - ‖α2 * (Real.sin θ : ℂ) ^ 2‖ := by
            rw [norm_one, norm_mul]
            nlinarith [hs θ, norm_nonneg α2]
        _ ≤ _ := norm_sub_norm_le _ _
    exact inv_anti₀ (by linarith) hL
  have hsum (θ : ℝ) : HasSum
      (fun m : ℕ => c m * ((Real.sin θ : ℂ) ^ (2 * m) *
        (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹))
      ((1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) := by
    have hz : ‖k ^ 2 * (Real.sin θ : ℂ) ^ 2‖ < 1 := by
      rw [norm_mul]
      calc ‖k ^ 2‖ * ‖(Real.sin θ : ℂ) ^ 2‖ ≤ ‖k ^ 2‖ * 1 := by
            gcongr; exact hs θ
        _ < 1 := by simpa using norm_sq_lt_one hk
    have H := (hasSum_pochhammer_div_factorial (β := (1 / 2 : ℂ)) hz).mul_left
      (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹
    refine H.congr_fun fun m => ?_
    simp only [c, mul_pow, ← pow_mul]
    ring
  rw [incompleteEllipticPi_real_eq_integral_of_norm_lt_one φ hα]
  have H := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := fun m θ => c m * ((Real.sin θ : ℂ) ^ (2 * m) *
      (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹))
    (fun m _ => ‖c m‖ * (1 - ‖α2‖)⁻¹)
    (μ := MeasureTheory.volume) (a := 0) (b := φ)
    (f := fun θ => (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)))
    (fun m => (by fun_prop : Measurable _).aestronglyMeasurable)
    (fun m => Filter.Eventually.of_forall fun θ hθ => by
      have hp : ‖(Real.sin θ : ℂ) ^ (2 * m)‖ ≤ 1 := by
        rw [pow_mul, norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (hs θ)
      calc
        ‖c m * ((Real.sin θ : ℂ) ^ (2 * m) *
            (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹)‖ =
            ‖c m‖ * (‖(Real.sin θ : ℂ) ^ (2 * m)‖ *
              ‖(1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹‖) := by
                rw [norm_mul]; congr 1; exact norm_mul _ _
        _ ≤ ‖c m‖ * (1 * (1 - ‖α2‖)⁻¹) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hp (hb θ) (norm_nonneg _) zero_le_one) (norm_nonneg _)
        _ = _ := by rw [one_mul])
    (Filter.Eventually.of_forall fun θ _ => hc.mul_right _)
    intervalIntegrable_const (Filter.Eventually.of_forall fun θ _ => hsum θ)
  simpa only [intervalIntegral.integral_const_mul] using H

/-- **Admitted.** DLMF 19.5.4_3: for real `|φ| < π/2`, `|k| < 1` and `|α²| < 1`,
`Π(φ, α², k) = ∑ₘ (1/2)ₘ sin^{2m+1}φ/((2m+1) m!) F₁(m + 1/2; 1/2, 1; m + 3/2; sin²φ, α² sin²φ)
k^{2m}`. -/
@[dlmf 19.5.E4_3]
theorem incompleteEllipticPi_hasSum {φ : ℝ} (hφ : |φ| < π / 2) {α2 k : ℂ} (hk : ‖k‖ < 1)
    (hα : ‖α2‖ < 1) :
    HasSum (fun m : ℕ => pochhammer (1 / 2) m * (Real.sin φ : ℂ) ^ (2 * m + 1) /
        ((2 * m + 1) * Nat.factorial m : ℂ) *
        (∑' p : ℕ × ℕ, appellF1Term ((m : ℂ) + 1 / 2) (1 / 2) 1 ((m : ℂ) + 3 / 2)
          ((Real.sin φ : ℂ) ^ 2) (α2 * (Real.sin φ : ℂ) ^ 2) p) * k ^ (2 * m))
        (incompleteEllipticPi φ α2 k) := by
  have H := hasSum_incompleteEllipticPi_moments (φ := φ) hk hα
  simp_rw [integral_sin_pow_div_eq_appellF1 _ hφ hα] at H
  refine H.congr_fun fun m => ?_
  have hF : DLMF.Hypergeometric.appellF1 ((m : ℂ) + 1 / 2) (1 / 2) 1
      ((m : ℂ) + 3 / 2) ((Real.sin φ : ℂ) ^ 2) (α2 * (Real.sin φ : ℂ) ^ 2) =
      ∑' p : ℕ × ℕ, appellF1Term ((m : ℂ) + 1 / 2) (1 / 2) 1
        ((m : ℂ) + 3 / 2) ((Real.sin φ : ℂ) ^ 2) (α2 * (Real.sin φ : ℂ) ^ 2) p := rfl
  rw [hF]
  field_simp

/-- **Admitted.** DLMF 19.5.5: Jacobi's nome `q = exp(-πK'(k)/K(k)) = r + 8r² + 84r³ + 992r⁴ + ⋯`
with `r = k²/16`, as `k → 0+` (the remainder is `O(r⁵)`). -/
@[dlmf 19.5.E5]
theorem jacobiNome_isBigO :
    (fun k : ℝ => jacobiNome k - ((k ^ 2 / 16 : ℝ) + 8 * (k ^ 2 / 16 : ℝ) ^ 2 +
        84 * (k ^ 2 / 16 : ℝ) ^ 3 + 992 * (k ^ 2 / 16 : ℝ) ^ 4 : ℂ)) =O[𝓝[>] 0]
      fun k : ℝ => (k ^ 2 / 16) ^ 5 := by
  sorry

/-- **Admitted.** DLMF 19.5.6–19.5.7: with `λ = (1 - √k')/(2(1 + √k'))`,
`q = λ + 2λ⁵ + 15λ⁹ + 150λ¹³ + 1707λ¹⁷ + ⋯` as `k → 0+` (the remainder is `O(λ²¹)`). -/
@[dlmf 19.5.E6, dlmf 19.5.E7]
theorem jacobiNome_isBigO_lambda :
    let lam : ℝ → ℝ := fun k =>
      (1 - Real.sqrt (Real.sqrt (1 - k ^ 2))) / (2 * (1 + Real.sqrt (Real.sqrt (1 - k ^ 2))))
    (fun k : ℝ => jacobiNome k - ((lam k + 2 * lam k ^ 5 + 15 * lam k ^ 9 + 150 * lam k ^ 13 +
        1707 * lam k ^ 17 : ℝ) : ℂ)) =O[𝓝[>] 0] fun k : ℝ => lam k ^ 21 := by
  sorry

/-- DLMF 19.5.8: `K(k) = (π/2)(1 + 2∑_{n ≥ 1} q^{n²})²` with `q = jacobiNome k`, on
`jacobiModulusDomain` (`Re k > 0`, `k ∉ [1, ∞)`, where `|q| < 1`). -/
@[dlmf 19.5.E8]
theorem completeEllipticK_eq_nome_series {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    completeEllipticK k = (π / 2 : ℂ) * (1 + 2 * ∑' n : ℕ, jacobiNome k ^ ((n + 1) ^ 2)) ^ 2 := by
  have hK := (jacobi_inversion_k hk).2.2
  have hS := DLMF.Theta.jacobiThetaThreeTau_hasSum_cos 0 (jacobiTau_im_pos hk)
  have hterm : ∀ n : ℕ, 2 * cexp (π * I * jacobiTau k * ((n : ℂ) + 1) ^ 2) *
      cos (2 * ((n : ℂ) + 1) * 0) = 2 * jacobiNome k ^ ((n + 1) ^ 2) := by
    intro n
    simp only [mul_zero, cos_zero, mul_one, jacobiNome, jacobiTau]
    rw [← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring_nf
    simp
    ring
  have hsum := (hS.congr_fun fun n => (hterm n).symm).tsum_eq
  rw [tsum_mul_left] at hsum
  have htheta : DLMF.Elliptic.jacobiThetaThreeTau 0 (jacobiTau k) =
      1 + 2 * ∑' n : ℕ, jacobiNome k ^ ((n + 1) ^ 2) := by
    linear_combination -hsum
  rw [← hK, completeEllipticKOfTau, htheta]

/-- **Admitted.** DLMF 19.5.9:
`E(k) = K(k) + (2π²/K(k)) ∑_{n≥1} (-1)ⁿ n² q^{n²} / (1 + 2∑_{n≥1} (-1)ⁿ q^{n²})` on
`jacobiModulusDomain`. -/
@[dlmf 19.5.E9]
theorem completeEllipticE_eq_nome_series {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    completeEllipticE k = completeEllipticK k + 2 * π ^ 2 / completeEllipticK k *
      ((∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * ((n + 1 : ℕ) : ℂ) ^ 2 * jacobiNome k ^ ((n + 1) ^ 2)) /
        (1 + 2 * ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * jacobiNome k ^ ((n + 1) ^ 2))) := by
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
    ‖(1 - jacobiComodulus k) / (1 + jacobiComodulus k)‖ ≤ ‖k‖ ^ 2 := by
  set c := jacobiComodulus k
  have hc : 0 < c.re := Carlson.re_cpow_half_pos hk
  have h1c : 1 + c ≠ 0 := fun h => by have := congrArg re h; simp at this; linarith
  have hsq : c ^ 2 = 1 - k ^ 2 := jacobiComodulus_sq_eq_one_sub_sq k
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
theorem completeEllipticK_eq_landen_prod {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    Tendsto (fun N => (π / 2 : ℂ) * ∏ m ∈ Finset.range N, (1 + landenModulusSeq k (m + 1))) atTop
      (𝓝 (completeEllipticK k)) := by
  set s := landenModulusSeq k with hs
  have hsucc : ∀ m, s (m + 1) = (1 - jacobiComodulus (s m)) / (1 + jacobiComodulus (s m)) :=
    fun m => rfl
  have hmem : ∀ m, 1 - s m ^ 2 ∈ slitPlane := by
    intro m; induction m with
    | zero => exact hk
    | succ m ih => rw [hsucc]; exact one_sub_landen_sq_mem_slitPlane (Carlson.re_cpow_half_pos ih)
  -- the product formula
  have hprod : ∀ N, completeEllipticK k =
      (∏ m ∈ Finset.range N, (1 + s (m + 1))) * completeEllipticK (s N) := by
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
  have hcont : ContinuousAt completeEllipticK 0 :=
    (differentiableOn_completeEllipticK_completeEllipticE.1.differentiableAt
      (isOpen_setOf_one_sub_sq_mem_slitPlane.mem_nhds (by simp))).continuousAt
  have hK0 : completeEllipticK 0 = π / 2 := by simp [completeEllipticK]
  have hKN : Tendsto (fun N => completeEllipticK (s N)) atTop (𝓝 (π / 2)) := by
    rw [← hK0]; exact hcont.tendsto.comp hlim
  have hpi : (π / 2 : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact div_ne_zero (ofReal_ne_zero.2 this.ne') two_ne_zero
  have hev : ∀ᶠ N in atTop, completeEllipticK (s N) ≠ 0 := hKN.eventually_ne hpi
  have hq := ((tendsto_const_nhds (x := completeEllipticK k)).div hKN hpi).mul_const (π / 2 : ℂ)
  rw [div_mul_cancel₀ _ hpi] at hq
  refine hq.congr' ?_
  filter_upwards [hev] with N hN
  simp only [Pi.div_apply]
  rw [hprod N]; field_simp

end DLMF.EllipticIntegrals
