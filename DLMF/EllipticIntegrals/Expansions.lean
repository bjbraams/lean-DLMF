/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.LegendreIdentities
public import DLMF.Hypergeometric.EulerIntegral
public import DLMF.EllipticIntegrals.Quadratic

/-!
# Maclaurin and related expansions of Legendre's integrals (DLMF §19.5)

Complex-modulus forms of DLMF 19.5.1–19.5.11. Series are stated with `HasSum`; the Appell
function is the project's `DLMF.Hypergeometric.appF1` (DLMF 16.13.1, the totalized double
series) — written out here as the `tsum` over `ℕ × ℕ` of the terms `ei19a_appF1Term`, because the module
`DLMF.GeneralizedHypergeometric.Appell` cannot be imported together with `lean-codes` (both
import a declaration `DifferentiableOn.analyticOnNhd_of_finiteDimensional`, from TauCeti and
from `SeveralComplexVariables`) — and `₂F₁` is Mathlib's `ordinaryHypergeometric`. The nome
is the Chapter 22 definition
`DLMF.JacobiElliptic.jacobiNomek k = exp(-πK'(k)/K(k))` (with the literal `K'`, which is DLMF's
`K'` for `Re k > 0`). The expansions 19.5.5–19.5.6 with "`+ ⋯`" are stated as `O`-estimates of
the remainder as `k → 0+`.

The real-parameter forms of 19.5.1–19.5.2 are the existing
`DLMF.Elliptic.Real.compEllIntKm_eq_ordinaryHypergeometric` and
`Real.compEllIntEm_eq_ordinaryHypergeometric` (tagged there). The complex forms of 19.5.1–19.5.3
follow from Euler's integral `DLMF.Hypergeometric.ordinaryHypergeometric_eq_integral` with the
substitution `t = sin²θ`.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic DLMF.Hypergeometric

/-- The `(p₁, p₂)` term of Appell's double series
`F₁(a; b, b'; c; x, y) = ∑ (a)_{p₁+p₂} (b)_{p₁} (b')_{p₂}/((c)_{p₁+p₂} p₁! p₂!) x^{p₁} y^{p₂}`
(DLMF 16.13.1), summed with `tsum` over `ℕ × ℕ` below. -/
def ei19a_appF1Term (a b b' c x y : ℂ) (p : ℕ × ℕ) : ℂ :=
  poch a (p.1 + p.2) * poch b p.1 * poch b' p.2 /
    (poch c (p.1 + p.2) * (Nat.factorial p.1 * Nat.factorial p.2 : ℂ)) * x ^ p.1 * y ^ p.2

/-- `Γ(1/2)² = π`. -/
theorem p19lR1_Gamma_half_sq : Gamma (1 / 2 : ℂ) * Gamma (1 / 2) = (π : ℂ) := by
  have h := Gamma_mul_Gamma_one_sub (1 / 2)
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by ring, show (π : ℂ) * (1 / 2) = π / 2 by ring,
    sin_pi_div_two, div_one] at h
  exact h

/-- `‖k²‖ < 1` for `‖k‖ < 1`. -/
theorem p19lR1_norm_sq_lt {k : ℂ} (hk : ‖k‖ < 1) : ‖k ^ 2‖ < 1 := by
  rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hk (by decide)

/-- Euler's integral for `₂F₁(a, 1/2; 1; k²)` in the angular form. -/
theorem p19lR1_hyp_half_one {a k : ℂ} (hk : ‖k‖ < 1) :
    (π / 2 : ℂ) * ₂F₁ a (1 / 2) 1 (k ^ 2) =
      ∫ θ in (0 : ℝ)..(π / 2), (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-a) := by
  rw [ordinaryHypergeometric_eq_integral (by norm_num) (by norm_num) (p19lR1_norm_sq_lt hk),
    show (1 : ℂ) - 1 / 2 = 1 / 2 by ring, Gamma_one, p19lR1_Gamma_half_sq,
    show (1 / 2 : ℂ) - 1 = -(1 / 2) by ring, integral_beta_half_weight]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [ofReal_pow]
  field_simp

/-- The Gauss series of `₂F₁(a, b; c; k²)` in powers of `k`, for `‖k‖ < 1`. -/
theorem p19lR1_hasSum_hyp (a b c : ℂ) {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => gaussHGCoeff a b c m * k ^ (2 * m)) (₂F₁ a b c (k ^ 2)) := by
  have h := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).hasSum_mul_pow
    (z := k ^ 2) (by
      rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ← ENNReal.coe_one,
        ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
      exact p19lR1_norm_sq_lt hk)
  simpa only [← pow_mul] using h

/-- `(1)ₘ = m!`. -/
theorem p19lR1_poch_one (m : ℕ) : poch 1 m = (Nat.factorial m : ℂ) := by
  simp [poch, ascPochhammer_eval_one]

/-- `(2)ₘ = (m+1)!`. -/
theorem p19lR1_poch_two (m : ℕ) : poch 2 m = (Nat.factorial (m + 1) : ℂ) := by
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
    rw [p19lR1_hyp_half_one hk, compEllIntKk]
  refine ⟨?_, h2⟩
  rw [h2]
  have := (p19lR1_hasSum_hyp (1 / 2) (1 / 2) 1 hk).mul_left (π / 2 : ℂ)
  convert this using 2 with m
  rw [gaussHGCoeff, p19lR1_poch_one]; ring

/-- DLMF 19.5.2: for `|k| < 1`,
`E(k) = (π/2) ∑ₘ (-1/2)ₘ (1/2)ₘ/(m! m!) k^{2m} = (π/2) ₂F₁(-1/2, 1/2; 1; k²)`. -/
@[dlmf 19.5.E2]
theorem compEllIntEk_hasSum {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => (π / 2 : ℂ) *
        (poch (-(1 / 2)) m * poch (1 / 2) m / (Nat.factorial m * Nat.factorial m : ℂ)) *
        k ^ (2 * m)) (compEllIntEk k) ∧
      compEllIntEk k = (π / 2 : ℂ) * ₂F₁ (-(1 / 2) : ℂ) (1 / 2) 1 (k ^ 2) := by
  have h2 : compEllIntEk k = (π / 2 : ℂ) * ₂F₁ (-(1 / 2) : ℂ) (1 / 2) 1 (k ^ 2) := by
    rw [p19lR1_hyp_half_one hk, compEllIntEk_eq_integral, neg_neg]
  refine ⟨?_, h2⟩
  rw [h2]
  have := (p19lR1_hasSum_hyp (-(1 / 2)) (1 / 2) 1 hk).mul_left (π / 2 : ℂ)
  convert this using 2 with m
  rw [gaussHGCoeff, p19lR1_poch_one]; ring

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
      (p19lR1_norm_sq_lt hk), show (2 : ℂ) - 3 / 2 - 1 = -(1 / 2) by ring,
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
    have hg := p19lR1_Gamma_half_sq
    simp only [ofReal_pow]
    rw [mul_assoc (1 / 2 : ℂ), hg]
    set X := ∫ θ in (0 : ℝ)..(π / 2), (Real.sin θ : ℂ) ^ 2 *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))
    field_simp
    ring
  refine ⟨?_, h2⟩
  rw [h2]
  have := (p19lR1_hasSum_hyp (3 / 2) (1 / 2) 2 hk).mul_left (π / 4 : ℂ)
  convert this using 2 with m
  rw [gaussHGCoeff, p19lR1_poch_two]; ring

/-- **Admitted.** DLMF 19.5.4: for `|k| < 1` and `|α| < 1` (here `|α²| < 1`),
`Π(α², k) = (π/2) ∑ₙ (1/2)ₙ/n! ∑_{m ≤ n} (1/2)ₘ/m! k^{2m} α^{2n-2m}
= (π/2) F₁(1/2; 1/2, 1; 1; k², α²)`. -/
@[dlmf 19.5.E4]
theorem compEllIntPik_hasSum {α2 k : ℂ} (hk : ‖k‖ < 1) (hα : ‖α2‖ < 1) :
    HasSum (fun n : ℕ => (π / 2 : ℂ) * (poch (1 / 2) n / Nat.factorial n *
        ∑ m ∈ Finset.range (n + 1), poch (1 / 2) m / Nat.factorial m * k ^ (2 * m) * α2 ^ (n - m)))
        (compEllIntPik α2 k) ∧
      compEllIntPik α2 k = (π / 2 : ℂ) * ∑' p : ℕ × ℕ, ei19a_appF1Term (1 / 2) (1 / 2) 1 1 (k ^ 2) α2 p := by
  sorry

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
        ei19a_appF1Term (1 / 2) (1 / 2) (1 / 2) (3 / 2) ((Real.sin φ : ℂ) ^ 2)
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
        ei19a_appF1Term (1 / 2) (1 / 2) (-(1 / 2)) (3 / 2) ((Real.sin φ : ℂ) ^ 2)
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
        (∑' p : ℕ × ℕ, ei19a_appF1Term ((m : ℂ) + 1 / 2) (1 / 2) 1 ((m : ℂ) + 3 / 2)
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
theorem p19lR1_landen_norm_lt {c : ℂ} (hc : 0 < c.re) : ‖(1 - c) / (1 + c)‖ < 1 := by
  have h1c : 1 + c ≠ 0 := fun h => by have := congrArg re h; simp at this; linarith
  rw [norm_div, div_lt_one (norm_pos_iff.2 h1c)]
  have h : ‖1 - c‖ ^ 2 < ‖1 + c‖ ^ 2 := by
    rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
    simp; nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h

/-- The descending Landen modulus satisfies `‖k₁‖ ≤ ‖k‖²`. -/
theorem p19lR1_landen_norm_le {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    ‖(1 - jacobiComodulusk k) / (1 + jacobiComodulusk k)‖ ≤ ‖k‖ ^ 2 := by
  set c := jacobiComodulusk k
  have hc : 0 < c.re := p19lR1_cpow_half_re_pos hk
  have h1c : 1 + c ≠ 0 := fun h => by have := congrArg re h; simp at this; linarith
  have hsq : c ^ 2 = 1 - k ^ 2 := ei19a_jacobiComodulusk_sq k
  have he : (1 - c) / (1 + c) = k ^ 2 / (1 + c) ^ 2 := by
    field_simp; linear_combination -hsq
  have hge : 1 ≤ ‖1 + c‖ := by
    calc (1 : ℝ) ≤ |(1 + c).re| := by simp; rw [abs_of_pos (by linarith)]; linarith
      _ ≤ ‖1 + c‖ := abs_re_le_norm _
  rw [he, norm_div, norm_pow, norm_pow]
  exact div_le_self (by positivity) (one_le_pow₀ hge)

/-- DLMF 19.5.10: `K(k) = (π/2) ∏_{m ≥ 1} (1 + k_m)` with the moduli of 19.5.11, in
the principal domain `1 - k² ∈ ℂ \ (-∞, 0]` (natural-order partial products). Proved by iterating the complex descending Landen
transformation 19.8.12 (`compEllInt_landen_descending`); `‖k_{m+1}‖ ≤ ‖k_m‖²` gives `k_m → 0`. -/
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
    | succ m ih => rw [hsucc]; exact p19lR1_landen_mem (p19lR1_cpow_half_re_pos ih)
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
  have hr1 : r < 1 := by rw [hr, hsucc]; exact p19lR1_landen_norm_lt (p19lR1_cpow_half_re_pos hk)
  have hbound : ∀ n, ‖s (n + 1)‖ ≤ r ^ (n + 1) := by
    intro n; induction n with
    | zero => simp [hr]
    | succ n ih =>
      have h1 : ‖s (n + 2)‖ ≤ ‖s (n + 1)‖ ^ 2 := by
        rw [hsucc]; exact p19lR1_landen_norm_le (hmem (n + 1))
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
      (p19lR1_isOpen_U.mem_nhds (by simp))).continuousAt
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
