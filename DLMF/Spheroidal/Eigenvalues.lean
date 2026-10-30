/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.FerrersProperties
public import DLMF.Spheroidal.Angular
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion

/-!
# Eigenvalues of the spheroidal equation (DLMF §30.3, §30.9)

Statement acquisition from NIST DLMF (version 1.2.8), checked 2026-10-26. Admitted statements
are not completed proofs; see `DLMF30Acquisition.md`.

* §30.3(ii): analyticity in `γ²`, the ordering 30.3.1 (proved from the existence theorem),
  the large-`n` behaviour 30.3.2, `λ^m_n(0) = n(n+1)` (30.3.3) and the derivative bounds 30.3.4;
* §30.3(iii): the continued-fraction equation 30.3.5 with the coefficients 30.3.6 or 30.3.7;
* §30.3(iv): the power series 30.3.8 and its coefficients 30.3.9–30.3.12;
* §30.9: the asymptotic expansions 30.9.1–30.9.6 for `γ² → ±∞`.

The continued fraction 30.3.5 is written with the project's continuants (`DLMF.cfTail`,
`DLMF.HasContinuedFraction`, which assert convergence of the finite truncations). The
equivalence "`λ` solves 30.3.5 iff `λ` is an eigenvalue of the right parity" is split into two
directions with explicit nondegeneracy hypotheses (nonvanishing finite continuant, nonvanishing
expansion coefficient), which DLMF leaves implicit.

All printed formulas of §§30.3 and 30.9 were checked numerically (eigenvalues of the
recurrences 30.8.4 and 30.3.5 in high precision, compared with SciPy's `pro_cv`/`obl_cv`).
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Spheroidal

/-- If two elements of a set have `a < b` smaller elements in the set, they are ordered. -/
private lemma s30_lt_of_encard_lt {S : Set ℝ} {x y : ℝ} {a b : ℕ∞}
    (hx : (S ∩ Iio x).encard = a) (hy : (S ∩ Iio y).encard = b) (hab : a < b) : x < y := by
  by_contra h
  have hsub : S ∩ Iio y ⊆ S ∩ Iio x :=
    inter_subset_inter_right _ (Iio_subset_Iio (not_lt.mp h))
  have := Set.encard_le_encard hsub
  rw [hx, hy] at this
  exact absurd hab (not_lt.mpr this)

/-! ### §30.3(ii) Properties -/

/-- **Ordering of the eigenvalues** (DLMF 30.3.1):
`λ^m_m(γ²) < λ^m_{m+1}(γ²) < λ^m_{m+2}(γ²) < ⋯`. Proved from `exists_spheroidalEigenvalue`. -/
@[dlmf 30.3.E1]
theorem spheroidalEigenvalue_lt_succ {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    spheroidalEigenvalue n m γ2 < spheroidalEigenvalue (n + 1) m γ2 := by
  have h1 := (spheroidalEigenvalue_spec hmn γ2).2
  have h2 := (spheroidalEigenvalue_spec (hmn.trans (Nat.le_succ n)) γ2).2
  refine s30_lt_of_encard_lt h1 h2 ?_
  have : n - m < n + 1 - m := by omega
  exact_mod_cast this

/-- **Ordering of the eigenvalues** (DLMF 30.3.1), strict monotonicity on `n ≥ m`. Proved from
`exists_spheroidalEigenvalue`. -/
@[dlmf 30.3.E1]
theorem spheroidalEigenvalue_lt {n n' m : ℕ} (hmn : m ≤ n) (hn : n < n') (γ2 : ℝ) :
    spheroidalEigenvalue n m γ2 < spheroidalEigenvalue n' m γ2 := by
  have h1 := (spheroidalEigenvalue_spec hmn γ2).2
  have h2 := (spheroidalEigenvalue_spec (hmn.trans hn.le) γ2).2
  refine s30_lt_of_encard_lt h1 h2 ?_
  have : n - m < n' - m := by omega
  exact_mod_cast this

/-- **Analyticity** (DLMF §30.3(ii)): `λ^m_n(γ²)` is a real-analytic function of the real
variable `γ²`. -/
@[dlmf 30.3.ii]
theorem analyticAt_spheroidalEigenvalue {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    AnalyticAt ℝ (fun t => spheroidalEigenvalue n m t) γ2 := by
  sorry

/-- **Large degree** (DLMF 30.3.2): `λ^m_n(γ²) = n(n+1) - γ²/2 + O(n⁻²)` as `n → ∞`. -/
@[dlmf 30.3.E2]
theorem spheroidalEigenvalue_isBigO_atTop (m : ℕ) (γ2 : ℝ) :
    (fun n : ℕ => spheroidalEigenvalue n m γ2 - ((n : ℝ) * (n + 1) - γ2 / 2)) =O[atTop]
      (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
  sorry

/-- **The Legendre case** (DLMF 30.3.3): `λ^m_n(0) = n(n+1)`. -/
@[dlmf 30.3.E3]
theorem spheroidalEigenvalue_zero {n m : ℕ} (hmn : m ≤ n) :
    spheroidalEigenvalue n m 0 = (n : ℝ) * (n + 1) :=
  p1s_spheroidalEigenvalue_zero hmn

/-- **Derivative bounds** (DLMF 30.3.4): `-1 < dλ^m_n(γ²)/d(γ²) < 0`. -/
@[dlmf 30.3.E4]
theorem spheroidalEigenvalue_deriv_bounds {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    ∃ d : ℝ, HasDerivAt (fun t => spheroidalEigenvalue n m t) d γ2 ∧ -1 < d ∧ d < 0 := by
  sorry

/-! ### §30.3(iii) Transcendental equation -/

/-- **The continued-fraction equation** (DLMF 30.3.5 with the coefficients 30.3.6 or 30.3.7),
eigenvalues are roots: for `n = m + p mod 2 + 2j`, `λ = λ^m_n(γ²)` satisfies
`β_p - λ - α_{p-2}γ_p/(β_{p-2} - λ - ⋯) = α_pγ_{p+2}/(β_{p+2} - λ - α_{p+2}γ_{p+4}/(⋯))`, the
right side converging. The left side is a finite continued fraction with last denominator
`β_0 - λ` or `β_1 - λ` (it is `0` for `p = 0, 1`). Nondegeneracy hypotheses (added; implicit in
DLMF): the finite continuant on the left is nonzero, and the coefficient of the expansion with
index `p` is nonzero (for 30.3.6 the Taylor coefficient `g_p` of the entire factor, 30.4.4; for
30.3.7 the Ferrers coefficient `a^m_{n,k}` with `n + 2k = m + p`, 30.8.1). -/
@[dlmf 30.3.E5, dlmf 30.3.E6, dlmf 30.3.E7]
theorem spheroidal_cf_of_eigenvalue {m : ℕ} {γ2 : ℝ} (alt : Bool) (p j : ℕ)
    (hcoef : if alt then
        spheroidalCoeff (m + p % 2 + 2 * j) m γ2 (((p : ℤ) + m - (m + p % 2 + 2 * j)) / 2) ≠ 0
      else iteratedDeriv p (spheroidalPsFactor (m + p % 2 + 2 * j) m γ2) 0 ≠ 0)
    (hden :
      let α : ℕ → ℝ := if alt then spheroidalCFAlphaAlt m γ2 else spheroidalCFAlpha m γ2
      let β : ℕ → ℝ := if alt then spheroidalCFBetaAlt m γ2 else spheroidalCFBeta m γ2
      let γ : ℕ → ℝ := if alt then spheroidalCFGammaAlt m γ2 else spheroidalCFGamma m γ2
      let lam : ℝ := spheroidalEigenvalue (m + p % 2 + 2 * j) m γ2
      (DLMF.cfContinuants
        (fun i => ((if i = 0 then 1 else -1) * (α (p - 2 - 2 * i) * γ (p - 2 * i)) : ℂ))
        (fun i => ((β (p - 2 - 2 * i) - lam : ℝ) : ℂ)) 0 (p / 2)).2.1 ≠ 0) :
    let α : ℕ → ℝ := if alt then spheroidalCFAlphaAlt m γ2 else spheroidalCFAlpha m γ2
    let β : ℕ → ℝ := if alt then spheroidalCFBetaAlt m γ2 else spheroidalCFBeta m γ2
    let γ : ℕ → ℝ := if alt then spheroidalCFGammaAlt m γ2 else spheroidalCFGamma m γ2
    let lam : ℝ := spheroidalEigenvalue (m + p % 2 + 2 * j) m γ2
    ∃ v : ℂ, DLMF.HasContinuedFraction
        (fun i => ((if i = 0 then 1 else -1) * (α (p + 2 * i) * γ (p + 2 * i + 2)) : ℂ))
        (fun i => ((β (p + 2 * i + 2) - lam : ℝ) : ℂ)) v ∧
      ((β p - lam : ℝ) : ℂ) - DLMF.cfTail
        (fun i => ((if i = 0 then 1 else -1) * (α (p - 2 - 2 * i) * γ (p - 2 * i)) : ℂ))
        (fun i => ((β (p - 2 - 2 * i) - lam : ℝ) : ℂ)) 0 (p / 2) = v := by
  sorry

/-- **The continued-fraction equation** (DLMF 30.3.5–30.3.7), roots are eigenvalues: a real root
`λ` of 30.3.5 (with the coefficients 30.3.6 or 30.3.7, a nonzero finite continuant on the left
and a convergent right side) is `λ^m_{m+p mod 2+2j}(γ²)` for some `j`. -/
@[dlmf 30.3.E5, dlmf 30.3.E6, dlmf 30.3.E7]
theorem spheroidal_eigenvalue_of_cf {m : ℕ} {γ2 : ℝ} (alt : Bool) (p : ℕ) (lam : ℝ) (v : ℂ) :
    let α : ℕ → ℝ := if alt then spheroidalCFAlphaAlt m γ2 else spheroidalCFAlpha m γ2
    let β : ℕ → ℝ := if alt then spheroidalCFBetaAlt m γ2 else spheroidalCFBeta m γ2
    let γ : ℕ → ℝ := if alt then spheroidalCFGammaAlt m γ2 else spheroidalCFGamma m γ2
    (DLMF.cfContinuants
        (fun i => ((if i = 0 then 1 else -1) * (α (p - 2 - 2 * i) * γ (p - 2 * i)) : ℂ))
        (fun i => ((β (p - 2 - 2 * i) - lam : ℝ) : ℂ)) 0 (p / 2)).2.1 ≠ 0 →
    DLMF.HasContinuedFraction
        (fun i => ((if i = 0 then 1 else -1) * (α (p + 2 * i) * γ (p + 2 * i + 2)) : ℂ))
        (fun i => ((β (p + 2 * i + 2) - lam : ℝ) : ℂ)) v →
    ((β p - lam : ℝ) : ℂ) - DLMF.cfTail
        (fun i => ((if i = 0 then 1 else -1) * (α (p - 2 - 2 * i) * γ (p - 2 * i)) : ℂ))
        (fun i => ((β (p - 2 - 2 * i) - lam : ℝ) : ℂ)) 0 (p / 2) = v →
    ∃ j : ℕ, lam = spheroidalEigenvalue (m + p % 2 + 2 * j) m γ2 := by
  sorry

/-! ### §30.3(iv) Power-series expansion -/

/-- **The power series in `γ²`** (DLMF 30.3.8): `λ^m_n(γ²) = ∑ ℓ_{2k} γ^{2k}` for
`|γ²| < r^m_n`, with some radius `r^m_n > 0`. Proved from the analyticity
(`analyticAt_spheroidalEigenvalue`). -/
@[dlmf 30.3.E8]
theorem hasSum_spheroidalEll {n m : ℕ} (hmn : m ≤ n) :
    ∃ r > 0, ∀ t : ℝ, |t| < r →
      HasSum (fun k => spheroidalEll n m k * t ^ k) (spheroidalEigenvalue n m t) := by
  obtain ⟨r, hr⟩ := (analyticAt_spheroidalEigenvalue hmn 0).hasFPowerSeriesAt
  obtain ⟨ρ, hρ0, hρr⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ENNReal.ofReal ρ < r := by
    obtain ⟨ρ, hρ, hρr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr.r_pos
    exact ⟨ρ, by exact_mod_cast hρ, by simpa using hρr⟩
  refine ⟨ρ, hρ0, fun t ht => ?_⟩
  have hmem : t ∈ Metric.eball (0 : ℝ) r := by
    rw [Metric.mem_eball, edist_zero_right]
    refine lt_of_le_of_lt ?_ hρr
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal ht.le
  have h := hr.hasSum hmem
  simp only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at h
  convert h using 2 with k
  simp only [spheroidalEll]

/-- **`ℓ_0 = n(n+1)`** (DLMF 30.3.9, first equation). Proved from 30.3.3. -/
@[dlmf 30.3.E9]
theorem spheroidalEll_zero {n m : ℕ} (hmn : m ≤ n) : spheroidalEll n m 0 = (n : ℝ) * (n + 1) := by
  simp [spheroidalEll, spheroidalEigenvalue_zero hmn]

/-- **`2ℓ_2 = -1 - (2m-1)(2m+1)/((2n-1)(2n+3))`** (DLMF 30.3.9, second equation). -/
@[dlmf 30.3.E9]
theorem spheroidalEll_one {n m : ℕ} (hmn : m ≤ n) :
    2 * spheroidalEll n m 1 =
      -1 - (2 * (m : ℝ) - 1) * (2 * m + 1) / ((2 * (n : ℝ) - 1) * (2 * n + 3)) := by
  sorry

/-- **`ℓ_4`** (DLMF 30.3.9, third equation):
`2ℓ_4 = (n-m-1)(n-m)(n+m-1)(n+m)/((2n-3)(2n-1)³(2n+1))
  - (n-m+1)(n-m+2)(n+m+1)(n+m+2)/((2n+1)(2n+3)³(2n+5))`. -/
@[dlmf 30.3.E9]
theorem spheroidalEll_two {n m : ℕ} (hmn : m ≤ n) :
    let a : ℝ := n
    let b : ℝ := m
    2 * spheroidalEll n m 2 =
      (a - b - 1) * (a - b) * (a + b - 1) * (a + b) /
          ((2 * a - 3) * (2 * a - 1) ^ 3 * (2 * a + 1)) -
        (a - b + 1) * (a - b + 2) * (a + b + 1) * (a + b + 2) /
          ((2 * a + 1) * (2 * a + 3) ^ 3 * (2 * a + 5)) := by
  sorry

/-- **`ℓ_6`** (DLMF 30.3.10). -/
@[dlmf 30.3.E10]
theorem spheroidalEll_three {n m : ℕ} (hmn : m ≤ n) :
    let a : ℝ := n
    let b : ℝ := m
    spheroidalEll n m 3 = (4 * b ^ 2 - 1) *
      ((a - b + 1) * (a - b + 2) * (a + b + 1) * (a + b + 2) /
          ((2 * a - 1) * (2 * a + 1) * (2 * a + 3) ^ 5 * (2 * a + 5) * (2 * a + 7)) -
        (a - b - 1) * (a - b) * (a + b - 1) * (a + b) /
          ((2 * a - 5) * (2 * a - 3) * (2 * a - 1) ^ 5 * (2 * a + 1) * (2 * a + 3))) := by
  sorry

/-- **`ℓ_8 = 2(4m²-1)²A + B/16 + C/8 + D/2`** (DLMF 30.3.11, with `A, B, C, D` from 30.3.12). -/
@[dlmf 30.3.E11, dlmf 30.3.E12]
theorem spheroidalEll_four {n m : ℕ} (hmn : m ≤ n) :
    spheroidalEll n m 4 = 2 * (4 * (m : ℝ) ^ 2 - 1) ^ 2 * spheroidalEllA n m +
      spheroidalEllB n m / 16 + spheroidalEllC n m / 8 + spheroidalEllD n m / 2 := by
  sorry

/-! ### §30.9 Asymptotic expansions of the eigenvalues -/

/-- **Prolate asymptotics** (DLMF 30.9.1–30.9.3): as `γ → +∞` (`γ² → +∞`), with
`q = 2(n-m)+1`, `λ^m_n(γ²) ∼ -γ² + γq + β_0 + β_1γ⁻¹ + β_2γ⁻² + ⋯`, with `β_0, …, β_5` as in
30.9.2–30.9.3 (`spheroidalProlateBeta`); the further coefficients exist but are not given. -/
@[dlmf 30.9.E1, dlmf 30.9.E2, dlmf 30.9.E3]
theorem spheroidalEigenvalue_prolate_asymptotic {n m : ℕ} (hmn : m ≤ n) :
    ∃ β : ℕ → ℝ, (∀ j ≤ 5, β j = spheroidalProlateBeta n m j) ∧
      HasAsymptoticExpansion atTop (fun (i : ℕ) (γ : ℝ) => γ ^ (-(i : ℝ))) β
        (fun γ => spheroidalEigenvalue n m (γ ^ 2) + γ ^ 2 - γ * (2 * ((n : ℝ) - m) + 1)) := by
  sorry

/-- **Oblate asymptotics** (DLMF 30.9.4–30.9.6): as `γ² → -∞`, writing `γ² = -κ²` with
`κ = |γ| → +∞` and `q = n + 1` (`n - m` even) or `q = n` (`n - m` odd),
`λ^m_n(γ²) ∼ 2qκ + c_0 + c_1κ⁻¹ + c_2κ⁻² + ⋯`, with `c_0, …, c_5` as in 30.9.5–30.9.6
(`spheroidalOblateC`). -/
@[dlmf 30.9.E4, dlmf 30.9.E5, dlmf 30.9.E6]
theorem spheroidalEigenvalue_oblate_asymptotic {n m : ℕ} (hmn : m ≤ n) :
    ∃ c : ℕ → ℝ, (∀ j ≤ 5, c j = spheroidalOblateC n m j) ∧
      HasAsymptoticExpansion atTop (fun (i : ℕ) (κ : ℝ) => κ ^ (-(i : ℝ))) c
        (fun κ => spheroidalEigenvalue n m (-κ ^ 2) - 2 * spheroidalOblateQ n m * κ) := by
  sorry

end DLMF.Spheroidal
