/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Legendre
public import DLMF.EllipticIntegrals.Symmetric
public import DLMF.EllipticIntegrals.Relations
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Asymptotic approximations (DLMF §19.12)

* (19.12.1), (19.12.2): convergent logarithmic expansions of `K(k)` and `E(k)` about `k = 1`,
  in powers of the complementary modulus `k' = (1 - k²)^{1/2}` (`jacobiComodulusk`, principal
  square root), with the coefficients `d(m) = ψ(1 + m) - ψ(½ + m)` (19.12.3,
  `compEllIntLogCoeff`) and the principal logarithm. Complex `k` are allowed, as in DLMF
  (`0 < |k'| < 1`); we add `1 - k² ∈ ℂ \ (-∞, 0]`, i.e. `k` off DLMF's cuts `(-∞, -1] ∪ [1, ∞)`
  of `K` and `E` (§19.2(ii)), where the integrals are not defined by DLMF. (For `E` the point
  `k' = 0` is allowed.)
* (19.12.4), (19.12.5): `Π(α², k)` as `k² → 1-` for real `α² < 1` and `α² > 1` (a Cauchy
  principal value). DLMF's `f = g (1 + O(k'²)) + h` is stated as `f - h - g = O(k'² g)`
  (equivalently). The limit `k² → 1-` is taken along real `k → 1-`.
* (19.12.6), (19.12.7): `R_C(x, y)` as `x/y → 0` (`x ≥ 0`, `y > 0`) and as `y/x → 0`
  (`x, y > 0`); the two-variable limits are filters on `ℝ × ℝ` (`Filter.comap` of the ratio).

## References

* NIST DLMF §19.12.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-- DLMF 19.12.3: `d(m) = ψ(1 + m) - ψ(½ + m)`, `ψ` the digamma function
(`Complex.digamma`). -/
@[dlmf 19.12.E3]
def compEllIntLogCoeff (m : ℕ) : ℂ := digamma (1 + m) - digamma (1 / 2 + m)

/-- DLMF 19.12.3: `d(0) = 2 ln 2`. -/
@[dlmf 19.12.E3]
theorem compEllIntLogCoeff_zero : compEllIntLogCoeff 0 = 2 * Complex.log 2 := by
  simp only [compEllIntLogCoeff, Nat.cast_zero, add_zero]
  rw [digamma_one, digamma_one_half]
  ring

/-- DLMF 19.12.3: `d(m + 1) = d(m) - 2/((2m + 1)(2m + 2))`. -/
@[dlmf 19.12.E3]
theorem compEllIntLogCoeff_succ (m : ℕ) :
    compEllIntLogCoeff (m + 1) =
      compEllIntLogCoeff m - 2 / ((2 * m + 1) * (2 * m + 2)) := by
  have h1 : ∀ n : ℕ, (1 + (m : ℂ)) ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m), (n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h2 : ∀ n : ℕ, (1 / 2 + (m : ℂ)) ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m), (n.cast_nonneg : (0 : ℝ) ≤ n)]
  simp only [compEllIntLogCoeff]
  push_cast
  rw [show (1 : ℂ) + (m + 1) = 1 + m + 1 by ring,
    show (1 / 2 : ℂ) + (m + 1) = 1 / 2 + m + 1 by ring,
    digamma_apply_add_one _ h1, digamma_apply_add_one _ h2]
  have hm1 : (1 + (m : ℂ)) ≠ 0 := by simpa using h1 0
  have hm2 : (1 / 2 + (m : ℂ)) ≠ 0 := by simpa using h2 0
  rw [show (2 * (m : ℂ) + 1) * (2 * m + 2) = 4 * ((1 / 2 + m) * (1 + m)) by ring]
  have hm3 : (1 + (m : ℂ) * 2) ≠ 0 := by
    rw [show 1 + (m : ℂ) * 2 = 2 * (1 / 2 + m) by ring]; exact mul_ne_zero two_ne_zero hm2
  field_simp
  ring

/-- DLMF 19.12.1: `K(k) = Σ_{m ≥ 0} ((½)_m)²/(m!)² k'^{2m} (ln(1/k') + d(m))`, for complex
`k` with `0 < |k'| < 1`, `k' = (1 - k²)^{1/2}` principal, and `1 - k² ∉ (-∞, 0]`. -/
@[dlmf 19.12.E1]
theorem compEllIntKk_hasSum_log {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane)
    (h1 : ‖jacobiComodulusk k‖ < 1) :
    HasSum (fun m : ℕ => ((ascPochhammer ℂ m).eval (1 / 2 : ℂ)) ^ 2 / (m.factorial : ℂ) ^ 2 *
        jacobiComodulusk k ^ (2 * m) *
          (Complex.log (1 / jacobiComodulusk k) + compEllIntLogCoeff m))
      (compEllIntKk k) := by
  sorry

/-- DLMF 19.12.2:
`E(k) = 1 + ½ Σ_{m ≥ 0} (½)_m (3/2)_m/((2)_m m!) k'^{2m+2} (ln(1/k') + d(m) - 1/((2m+1)(2m+2)))`,
for complex `k` with `|k'| < 1`, `k' = (1 - k²)^{1/2}` principal, and `1 - k² ∉ (-∞, 0)`. -/
@[dlmf 19.12.E2]
theorem compEllIntEk_hasSum_log {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane ∨ k ^ 2 = 1)
    (h1 : ‖jacobiComodulusk k‖ < 1) :
    HasSum (fun m : ℕ => (1 / 2 : ℂ) * ((ascPochhammer ℂ m).eval (1 / 2 : ℂ) *
        (ascPochhammer ℂ m).eval (3 / 2 : ℂ) /
          ((ascPochhammer ℂ m).eval (2 : ℂ) * (m.factorial : ℂ)) *
        jacobiComodulusk k ^ (2 * m + 2) *
          (Complex.log (1 / jacobiComodulusk k) + compEllIntLogCoeff m -
            1 / ((2 * m + 1) * (2 * m + 2)))))
      (compEllIntEk k - 1) := by
  sorry

/-- DLMF 19.12.4: as `k² → 1-` (real `k → 1-`), for real `α² < 1`,
`(1 - α²) Π(α², k) = (ln(4/k'))(1 + O(k'²)) - α² R_C(1, 1 - α²)`, stated as
`(1 - α²) Π(α², k) + α² R_C(1, 1 - α²) - ln(4/k') = O(k'² ln(4/k'))`. -/
@[dlmf 19.12.E4]
theorem compEllIntPik_isBigO_log {α2 : ℝ} (hα : α2 < 1) :
    (fun k : ℝ => (1 - α2) * compEllIntPik α2 k + α2 * symEllIntRC 1 ((1 - α2 : ℝ) : ℂ) -
        (Real.log (4 / Real.sqrt (1 - k ^ 2)) : ℂ)) =O[𝓝[<] 1]
      fun k : ℝ => (1 - k ^ 2) * Real.log (4 / Real.sqrt (1 - k ^ 2)) := by
  sorry

/-- DLMF 19.12.5: as `k² → 1-` (real `k → 1-`), for real `α² > 1` (Cauchy principal value
`Π`), `(1 - α²) Π(α², k) = (ln(4/k') - R_C(1, 1 - α⁻²))(1 + O(k'²))`, stated as
`(1 - α²) Π(α², k) - (ln(4/k') - R_C(1, 1 - α⁻²)) = O(k'² (ln(4/k') - R_C(1, 1 - α⁻²)))`. -/
@[dlmf 19.12.E5]
theorem compEllIntPik_isBigO_log_of_one_lt {α2 : ℝ} (hα : 1 < α2) :
    (fun k : ℝ => (1 - α2) * compEllIntPik α2 k -
        ((Real.log (4 / Real.sqrt (1 - k ^ 2)) : ℂ) -
          symEllIntRC 1 ((1 - α2⁻¹ : ℝ) : ℂ))) =O[𝓝[<] 1]
      fun k : ℝ => ((1 - k ^ 2 : ℝ) : ℂ) *
        ((Real.log (4 / Real.sqrt (1 - k ^ 2)) : ℂ) - symEllIntRC 1 ((1 - α2⁻¹ : ℝ) : ℂ)) := by
  sorry

/-- The filter of DLMF 19.12.6: `x ≥ 0`, `y > 0`, `x/y → 0`. -/
def ei19b_smallRatioFilter : Filter (ℝ × ℝ) :=
  comap (fun p : ℝ × ℝ => p.1 / p.2) (𝓝 0) ⊓ 𝓟 {p | 0 ≤ p.1 ∧ 0 < p.2}

/-- The filter of DLMF 19.12.7: `x > 0`, `y > 0`, `y/x → 0`. -/
def ei19b_largeRatioFilter : Filter (ℝ × ℝ) :=
  comap (fun p : ℝ × ℝ => p.2 / p.1) (𝓝 0) ⊓ 𝓟 {p | 0 < p.1 ∧ 0 < p.2}

/-- `R_C(x, y) = y^{-1/2} arccos(√(x/y))/√(1 - x/y)` for `0 ≤ x < y` (Carlson's (6.9-15) and
homogeneity; `x = 0` from 19.6.15). -/
theorem ei19b_symEllIntRC_eq_arccos {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    symEllIntRC (x : ℂ) (y : ℂ) =
      (((Real.sqrt y)⁻¹ * (Real.arccos (Real.sqrt (x / y)) / Real.sqrt (1 - x / y)) : ℝ) : ℂ) := by
  have hy : 0 < y := lt_of_le_of_lt hx hxy
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hyy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  rcases hx.lt_or_eq with hx0 | rfl
  · have ht0 : 0 < x / y := div_pos hx0 hy
    have ht1 : x / y < 1 := (div_lt_one hy).mpr hxy
    have e1 : x = Real.sqrt y ^ 2 * (x / y) := by rw [hyy]; field_simp
    have e2 : y = Real.sqrt y ^ 2 * 1 := by rw [hyy, mul_one]
    have h := ei19b_symEllIntRC_scale hsy ht0 one_pos
    rw [← e1, ← e2] at h
    rw [h, show ((1 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) from rfl, Carlson.TwoVariable.carlsonRC_of_lt ht0 ht1,
      div_one]
    push_cast
    ring
  · have h := ei19b_symEllIntRC_zero_sq hsy
    rw [hyy] at h
    rw [ofReal_zero, h, zero_div, Real.sqrt_zero, Real.arccos_zero, sub_zero, Real.sqrt_one,
      div_one]
    push_cast
    field_simp

/-- The elementary estimate behind 19.12.6:
`|arccos s/√(1 - s²) - π/2 + s| ≤ 3s²` for `0 ≤ s ≤ 1/2`. -/
theorem ei19b_arccos_estimate {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) :
    |Real.arccos s / Real.sqrt (1 - s ^ 2) - π / 2 + s| ≤ 3 * s ^ 2 := by
  set r := Real.sqrt (1 - s ^ 2) with hr
  have hs2 : s ^ 2 ≤ 1 / 4 := by nlinarith
  have hr2 : r ^ 2 = 1 - s ^ 2 := Real.sq_sqrt (by nlinarith)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by nlinarith)
  have hr1 : r ≤ 1 := by rw [hr]; exact Real.sqrt_le_one.mpr (by nlinarith)
  have hrr : 3 / 4 ≤ r ^ 2 := by rw [hr2]; linarith
  set A := Real.arcsin s with hA
  have hA0 : 0 ≤ A := Real.arcsin_nonneg.mpr h0
  have hA1 : A < π / 2 := Real.arcsin_lt_pi_div_two.mpr (by linarith)
  have hsA : s ≤ A := by
    have := Real.sin_le hA0
    rwa [hA, Real.sin_arcsin (by linarith) (by linarith)] at this
  have hAs : A * r ≤ s := by
    have := Real.le_tan hA0 hA1
    rw [hA, Real.tan_arcsin] at this
    rw [← hr] at this
    calc A * r ≤ s / r * r := mul_le_mul_of_nonneg_right this hr0.le
      _ = s := by field_simp
  rw [Real.arccos_eq_pi_div_two_sub_arcsin, ← hA]
  have hπ : π < 4 := Real.pi_lt_four
  have hπ0 : 0 < π := Real.pi_pos
  -- `1/r - 1 ≤ s²`, i.e. `1 ≤ r (1 + s²)`
  have hinv : 1 ≤ r * (1 + s ^ 2) := by
    have hsq : 1 ≤ (r * (1 + s ^ 2)) ^ 2 := by
      rw [mul_pow, hr2]; nlinarith [sq_nonneg s, sq_nonneg (s ^ 2)]
    nlinarith [sq_nonneg (r * (1 + s ^ 2) - 1)]
  rw [abs_le]
  constructor
  · rw [div_eq_mul_inv]
    have key : -(3 * s ^ 2) * r ≤ (π / 2 - A) - π / 2 * r + s * r := by
      nlinarith [mul_le_mul_of_nonneg_left hinv h0]
    have := div_le_div_of_nonneg_right key hr0.le
    rw [neg_mul, neg_div, mul_div_assoc, div_self hr0.ne', mul_one] at this
    calc -(3 * s ^ 2) ≤ ((π / 2 - A) - π / 2 * r + s * r) / r := this
      _ = (π / 2 - A) * r⁻¹ - π / 2 + s := by field_simp
  · rw [div_eq_mul_inv]
    have key : (π / 2 - A) - π / 2 * r + s * r ≤ 3 * s ^ 2 * r := by
      nlinarith [mul_le_mul_of_nonneg_left hinv hπ0.le, mul_nonneg h0 hr0.le]
    have := div_le_div_of_nonneg_right key hr0.le
    rw [mul_div_assoc, div_self hr0.ne', mul_one] at this
    calc (π / 2 - A) * r⁻¹ - π / 2 + s = ((π / 2 - A) - π / 2 * r + s * r) / r := by
          field_simp
      _ ≤ 3 * s ^ 2 := this

/-- DLMF 19.12.6: `R_C(x, y) = π/(2√y) - (√x/y)(1 + O(√(x/y)))` as `x/y → 0`, `x ≥ 0`,
`y > 0`; stated as `R_C(x, y) - π/(2√y) + √x/y = O((√x/y) √(x/y))`. -/
@[dlmf 19.12.E6]
theorem symEllIntRC_isBigO_small :
    (fun p : ℝ × ℝ => symEllIntRC (p.1 : ℂ) (p.2 : ℂ) -
        ((π / (2 * Real.sqrt p.2) - Real.sqrt p.1 / p.2 : ℝ) : ℂ)) =O[ei19b_smallRatioFilter]
      fun p : ℝ × ℝ => Real.sqrt p.1 / p.2 * Real.sqrt (p.1 / p.2) := by
  have hev : ∀ᶠ p : ℝ × ℝ in ei19b_smallRatioFilter,
      p.1 / p.2 < 1 / 4 ∧ 0 ≤ p.1 ∧ 0 < p.2 := by
    have h1 : ∀ᶠ p : ℝ × ℝ in ei19b_smallRatioFilter, p.1 / p.2 < 1 / 4 :=
      (tendsto_comap.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))).filter_mono
        inf_le_left
    have h2 : ∀ᶠ p : ℝ × ℝ in ei19b_smallRatioFilter, 0 ≤ p.1 ∧ 0 < p.2 :=
      (eventually_principal.mpr fun p hp => hp).filter_mono inf_le_right
    exact h1.and h2
  refine IsBigO.of_bound 3 ?_
  filter_upwards [hev] with p ⟨ht, hx, hy⟩
  obtain ⟨x, y⟩ := p
  simp only at ht hx hy ⊢
  have hxy : x < y := by
    have : x / y < 1 := by linarith
    rwa [div_lt_one hy] at this
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  set s := Real.sqrt (x / y) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = x / y := Real.sq_sqrt (div_nonneg hx hy.le)
  have hs1 : s ≤ 1 / 2 := by nlinarith
  have hsx : Real.sqrt x / y = s / Real.sqrt y := by
    rw [hs, Real.sqrt_div' _ hy.le, div_div, ← Real.sqrt_mul hy.le, Real.sqrt_mul_self hy.le]
  rw [ei19b_symEllIntRC_eq_arccos hx hxy, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, hsx, ← hs]
  rw [show 1 - x / y = 1 - s ^ 2 by rw [hs2]]
  have he := ei19b_arccos_estimate hs0 hs1
  rw [show (Real.sqrt y)⁻¹ * (Real.arccos s / Real.sqrt (1 - s ^ 2)) - (π / (2 * Real.sqrt y) -
      s / Real.sqrt y) = (Real.sqrt y)⁻¹ * (Real.arccos s / Real.sqrt (1 - s ^ 2) - π / 2 + s) by
    field_simp; ring, abs_mul, abs_of_pos (inv_pos.mpr hsy),
    show s / Real.sqrt y * s = (Real.sqrt y)⁻¹ * s ^ 2 by field_simp,
    abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt y)⁻¹ * s ^ 2)]
  calc (Real.sqrt y)⁻¹ * |Real.arccos s / Real.sqrt (1 - s ^ 2) - π / 2 + s|
      ≤ (Real.sqrt y)⁻¹ * (3 * s ^ 2) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = 3 * ((Real.sqrt y)⁻¹ * s ^ 2) := by ring

/-- DLMF 19.12.7:
`R_C(x, y) = (1/(2√x))((1 + y/(2x)) ln(4x/y) - y/(2x))(1 + O(y²/x²))` as `y/x → 0`, `x, y > 0`;
stated as `R_C(x, y) - M = O(M y²/x²)` with `M` the main term. -/
@[dlmf 19.12.E7]
theorem symEllIntRC_isBigO_large :
    (fun p : ℝ × ℝ => symEllIntRC (p.1 : ℂ) (p.2 : ℂ) -
        ((1 / (2 * Real.sqrt p.1) * ((1 + p.2 / (2 * p.1)) * Real.log (4 * p.1 / p.2) -
          p.2 / (2 * p.1)) : ℝ) : ℂ)) =O[ei19b_largeRatioFilter]
      fun p : ℝ × ℝ => 1 / (2 * Real.sqrt p.1) * ((1 + p.2 / (2 * p.1)) *
        Real.log (4 * p.1 / p.2) - p.2 / (2 * p.1)) * (p.2 / p.1) ^ 2 := by
  sorry

end DLMF.EllipticIntegrals
