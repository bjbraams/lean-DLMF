/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Modified.Defs
public import DLMF.Bessel.Modified
public import DLMF.Bessel.SecondKind

/-!
# Modified Mathieu functions: expansions in Bessel functions (DLMF §§28.23–28.24)

* 28.23.1: the cylinder functions `𝒞^{(j)}_μ` (`mathieuCyl`, `mathieuCylExp`) and their
  relation to the project's Hankel functions and to the principal branch.
* 28.23.2–28.23.5: the expansions of `M^{(j)}_ν` in `𝒞^{(j)}_{ν+2n}(2h cosh z)` and
  `𝒞^{(j)}_{ν+2n}(2h sinh z)` (noninteger `ν`; **corrected convergence region**, see below).
* 28.23.6–28.23.13: the integer-order expansions of `Mc^{(j)}_n`, `Ms^{(j)}_n`.
* 28.24.1: the cross-product series, which is the definition of `M^{(j)}_ν`; the theorem says
  that it converges for every index `n` with the same sum.
* 28.24.2–28.24.13: the integer-order cross-product series, including those for `Ie_n`,
  `Io_n`, `Ke_n`, `Ko_n` in modified Bessel functions.

## Correction to DLMF 28.23

DLMF states that 28.23.2–28.23.5 are valid "for all `z` when `j = 1`". For noninteger `ν` this
is false: the terms with `n → -∞` behave like `c^ν_{2n} J_{ν+2n}(2h cosh z)`, and since
`c^ν_{2n}/c^ν_{2n+2} ~ -q/(4n²)` (28.14.6) while `J_{μ-2}(w)/J_μ(w) ~ 4μ²/w²` as
`μ → -∞` through nonintegers, the ratio of consecutive terms tends to `1/cosh² z`
(resp. `1/sinh² z`). The series therefore converge only for `|cosh z| > 1`
(resp. `|sinh z| > 1`), for every `j`. Numerically, with `ν = 0.3`, `h = 1.2`, the series 28.23.2
with `j = 1` at `z = 0.2 + 1.2i` (`|cosh z| = 0.41`) has partial sums of size `10⁵` at
`|n| ≤ 10` and `10¹²` at `|n| ≤ 20`, and 28.23.4 diverges at `z = 0.3`. For integer `ν`
(28.23.6–28.23.13) the `j = 1` series do converge for all `z`. The statements below for
noninteger `ν` carry the hypothesis `|cosh z| > 1` (resp. `|sinh z| > 1`) for all `j`.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real

namespace DLMF.Mathieu

/-! ### §28.23 Expansions in series of Bessel functions -/

/-- `𝒞^{(3)}_μ` and `𝒞^{(4)}_μ` are the project's Hankel functions (DLMF 28.23.1, 10.4.3). -/
@[dlmf 28.23.E1]
theorem mathieuCyl_three_four (μ w : ℂ) :
    mathieuCyl 3 μ w = DLMF.Bessel.hankelH1 μ w ∧ mathieuCyl 4 μ w = DLMF.Bessel.hankelH2 μ w :=
  ⟨rfl, rfl⟩

/-- The continued cylinder functions agree with the principal-branch ones at `h e^z` for
`h > 0` and `-π < Im z ≤ π` (DLMF 28.23.1). -/
@[dlmf 28.23.E1]
theorem mathieuCylExp_eq_mathieuCyl (j : ℕ) (μ : ℂ) {h : ℝ} (hh : 0 < h) {z : ℂ}
    (hz₁ : -π < z.im) (hz₂ : z.im ≤ π) :
    mathieuCylExp j μ h z = mathieuCyl j μ (h * Complex.exp z) := by
  sorry

/-- **Expansion in Bessel functions** (DLMF 28.23.2), `ν` real, `ν ∉ ℤ`, `h > 0`,
`j = 1, 2, 3, 4`, `Re z > 0`, `|cosh z| > 1`:
`me_ν(0, h²) M^{(j)}_ν(z, h) = ∑_n (-1)^n c^ν_{2n}(h²) 𝒞^{(j)}_{ν+2n}(2h cosh z)`.
**Corrected**: DLMF claims validity for all `z` when `j = 1`; the condition `|cosh z| > 1` is
needed for every `j` (module docstring). -/
@[dlmf 28.23.E2]
theorem hasSum_modMathieuM_cosh (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) {ν : ℝ}
    (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 < z.re)
    (hcosh : 1 < ‖Complex.cosh z‖) :
    HasSum (fun n : ℤ => (-1 : ℂ) ^ n * mathieuMeCoeff ν ((h : ℂ) ^ 2) n *
        mathieuCylCosh j (ν + 2 * n) h z)
      (mathieuMe ν 0 ((h : ℂ) ^ 2) * modMathieuM j ν z h) := by
  sorry

/-- **Expansion in Bessel functions** (DLMF 28.23.3), hypotheses as for 28.23.2 (corrected):
`me'_ν(0, h²) M^{(j)}_ν(z, h) = i tanh z ∑_n (-1)^n (ν + 2n) c^ν_{2n}(h²) 𝒞^{(j)}_{ν+2n}(2h cosh
z)`. -/
@[dlmf 28.23.E3]
theorem hasSum_modMathieuM_cosh_deriv (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) {ν : ℝ}
    (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 < z.re)
    (hcosh : 1 < ‖Complex.cosh z‖) :
    HasSum (fun n : ℤ => I * Complex.tanh z * ((-1 : ℂ) ^ n * (ν + 2 * n) *
        mathieuMeCoeff ν ((h : ℂ) ^ 2) n * mathieuCylCosh j (ν + 2 * n) h z))
      (deriv (fun x => mathieuMe ν x ((h : ℂ) ^ 2)) 0 * modMathieuM j ν z h) := by
  sorry

/-- **Expansion in Bessel functions** (DLMF 28.23.4), `ν` real, `ν ∉ ℤ`, `h > 0`,
`j = 1, 2, 3, 4`, `Re z > 0`, `|sinh z| > 1` (**corrected**, as for 28.23.2):
`me_ν(π/2, h²) M^{(j)}_ν(z, h) = e^{iνπ/2} ∑_n c^ν_{2n}(h²) 𝒞^{(j)}_{ν+2n}(2h sinh z)`. -/
@[dlmf 28.23.E4]
theorem hasSum_modMathieuM_sinh (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) {ν : ℝ}
    (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 < z.re)
    (hsinh : 1 < ‖Complex.sinh z‖) :
    HasSum (fun n : ℤ => Complex.exp (I * ν * π / 2) *
        (mathieuMeCoeff ν ((h : ℂ) ^ 2) n * mathieuCylSinh j (ν + 2 * n) h z))
      (mathieuMe ν (π / 2) ((h : ℂ) ^ 2) * modMathieuM j ν z h) := by
  sorry

/-- **Expansion in Bessel functions** (DLMF 28.23.5), hypotheses as for 28.23.4:
`me'_ν(π/2, h²) M^{(j)}_ν(z, h) = i e^{iνπ/2} coth z ∑_n (ν + 2n) c^ν_{2n}(h²) 𝒞^{(j)}_{ν+2n}(2h
sinh z)`. -/
@[dlmf 28.23.E5]
theorem hasSum_modMathieuM_sinh_deriv (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) {ν : ℝ}
    (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 < z.re)
    (hsinh : 1 < ‖Complex.sinh z‖) :
    HasSum (fun n : ℤ => I * Complex.exp (I * ν * π / 2) * (Complex.tanh z)⁻¹ *
        ((ν + 2 * n) * mathieuMeCoeff ν ((h : ℂ) ^ 2) n * mathieuCylSinh j (ν + 2 * n) h z))
      (deriv (fun x => mathieuMe ν x ((h : ℂ) ^ 2)) (π / 2) * modMathieuM j ν z h) := by
  sorry

/-- **Integer-order expansion** (DLMF 28.23.6), `h > 0`, `j = 1, 2, 3, 4`, `z` in the region of
convergence (DLMF 28.23 prose: all `z` for `j = 1`):
`Mc^{(j)}_{2m}(z, h) = (-1)^m ce_{2m}(0, h²)⁻¹ ∑_ℓ (-1)^ℓ A^{2m}_{2ℓ}(h²) 𝒞^{(j)}_{2ℓ}(2h cosh
z)`. -/
@[dlmf 28.23.E6, dlmf 28.23]
theorem hasSum_radialMathieuMc_even_cosh (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m : ℕ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : ModMathieuCoshRegion j z) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * (mathieuCe (2 * m) 0 (h ^ 2))⁻¹ *
        ((-1 : ℂ) ^ ℓ * mathieuFourierA (2 * m) (2 * ℓ) (h ^ 2) *
          mathieuCylCosh j (2 * ℓ : ℕ) h z))
      (radialMathieuMc j (2 * m) z h) := by
  sorry

/-- **Integer-order expansion** (DLMF 28.23.7):
`Mc^{(j)}_{2m}(z, h) = (-1)^m ce_{2m}(π/2, h²)⁻¹ ∑_ℓ A^{2m}_{2ℓ}(h²) 𝒞^{(j)}_{2ℓ}(2h sinh z)`. -/
@[dlmf 28.23.E7, dlmf 28.23]
theorem hasSum_radialMathieuMc_even_sinh (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m : ℕ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : ModMathieuSinhRegion j z) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * (mathieuCe (2 * m) (π / 2) (h ^ 2))⁻¹ *
        (mathieuFourierA (2 * m) (2 * ℓ) (h ^ 2) * mathieuCylSinh j (2 * ℓ : ℕ) h z))
      (radialMathieuMc j (2 * m) z h) := by
  sorry

/-- **Integer-order expansion** (DLMF 28.23.8):
`Mc^{(j)}_{2m+1}(z, h) = (-1)^m ce_{2m+1}(0, h²)⁻¹ ∑_ℓ (-1)^ℓ A^{2m+1}_{2ℓ+1}(h²)
𝒞^{(j)}_{2ℓ+1}(2h cosh z)`. -/
@[dlmf 28.23.E8, dlmf 28.23]
theorem hasSum_radialMathieuMc_odd_cosh (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m : ℕ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : ModMathieuCoshRegion j z) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * (mathieuCe (2 * m + 1) 0 (h ^ 2))⁻¹ *
        ((-1 : ℂ) ^ ℓ * mathieuFourierA (2 * m + 1) (2 * ℓ + 1) (h ^ 2) *
          mathieuCylCosh j (2 * ℓ + 1 : ℕ) h z))
      (radialMathieuMc j (2 * m + 1) z h) := by
  sorry

/-- **Integer-order expansion** (DLMF 28.23.9):
`Mc^{(j)}_{2m+1}(z, h) = (-1)^{m+1} ce'_{2m+1}(π/2, h²)⁻¹ coth z ∑_ℓ (2ℓ+1) A^{2m+1}_{2ℓ+1}(h²)
𝒞^{(j)}_{2ℓ+1}(2h sinh z)`. -/
@[dlmf 28.23.E9, dlmf 28.23]
theorem hasSum_radialMathieuMc_odd_sinh (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m : ℕ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : ModMathieuSinhRegion j z) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ (m + 1) *
        (deriv (fun x => mathieuCe (2 * m + 1) x (h ^ 2)) (π / 2))⁻¹ * (Complex.tanh z)⁻¹ *
        ((2 * ℓ + 1 : ℂ) * mathieuFourierA (2 * m + 1) (2 * ℓ + 1) (h ^ 2) *
          mathieuCylSinh j (2 * ℓ + 1 : ℕ) h z))
      (radialMathieuMc j (2 * m + 1) z h) := by
  sorry

/-- **Integer-order expansion** (DLMF 28.23.10):
`Ms^{(j)}_{2m+1}(z, h) = (-1)^m se'_{2m+1}(0, h²)⁻¹ tanh z ∑_ℓ (-1)^ℓ (2ℓ+1) B^{2m+1}_{2ℓ+1}(h²)
𝒞^{(j)}_{2ℓ+1}(2h cosh z)`. -/
@[dlmf 28.23.E10, dlmf 28.23]
theorem hasSum_radialMathieuMs_odd_cosh (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m : ℕ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : ModMathieuCoshRegion j z) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m *
        (deriv (fun x => mathieuSe (2 * m + 1) x (h ^ 2)) 0)⁻¹ * Complex.tanh z *
        ((-1 : ℂ) ^ ℓ * (2 * ℓ + 1 : ℂ) * mathieuFourierB (2 * m + 1) (2 * ℓ + 1) (h ^ 2) *
          mathieuCylCosh j (2 * ℓ + 1 : ℕ) h z))
      (radialMathieuMs j (2 * m + 1) z h) := by
  sorry

/-- **Integer-order expansion** (DLMF 28.23.11):
`Ms^{(j)}_{2m+1}(z, h) = (-1)^m se_{2m+1}(π/2, h²)⁻¹ ∑_ℓ B^{2m+1}_{2ℓ+1}(h²) 𝒞^{(j)}_{2ℓ+1}(2h
sinh z)`. -/
@[dlmf 28.23.E11, dlmf 28.23]
theorem hasSum_radialMathieuMs_odd_sinh (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m : ℕ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : ModMathieuSinhRegion j z) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * (mathieuSe (2 * m + 1) (π / 2) (h ^ 2))⁻¹ *
        (mathieuFourierB (2 * m + 1) (2 * ℓ + 1) (h ^ 2) *
          mathieuCylSinh j (2 * ℓ + 1 : ℕ) h z))
      (radialMathieuMs j (2 * m + 1) z h) := by
  sorry

/-- **Integer-order expansion** (DLMF 28.23.12):
`Ms^{(j)}_{2m+2}(z, h) = (-1)^m se'_{2m+2}(0, h²)⁻¹ tanh z ∑_ℓ (-1)^ℓ (2ℓ+2) B^{2m+2}_{2ℓ+2}(h²)
𝒞^{(j)}_{2ℓ+2}(2h cosh z)`. -/
@[dlmf 28.23.E12, dlmf 28.23]
theorem hasSum_radialMathieuMs_even_cosh (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m : ℕ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : ModMathieuCoshRegion j z) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m *
        (deriv (fun x => mathieuSe (2 * m + 2) x (h ^ 2)) 0)⁻¹ * Complex.tanh z *
        ((-1 : ℂ) ^ ℓ * (2 * ℓ + 2 : ℂ) * mathieuFourierB (2 * m + 2) (2 * ℓ + 2) (h ^ 2) *
          mathieuCylCosh j (2 * ℓ + 2 : ℕ) h z))
      (radialMathieuMs j (2 * m + 2) z h) := by
  sorry

/-- **Integer-order expansion** (DLMF 28.23.13):
`Ms^{(j)}_{2m+2}(z, h) = (-1)^{m+1} se'_{2m+2}(π/2, h²)⁻¹ coth z ∑_ℓ (2ℓ+2) B^{2m+2}_{2ℓ+2}(h²)
𝒞^{(j)}_{2ℓ+2}(2h sinh z)`. -/
@[dlmf 28.23.E13, dlmf 28.23]
theorem hasSum_radialMathieuMs_even_sinh (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m : ℕ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : ModMathieuSinhRegion j z) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ (m + 1) *
        (deriv (fun x => mathieuSe (2 * m + 2) x (h ^ 2)) (π / 2))⁻¹ * (Complex.tanh z)⁻¹ *
        ((2 * ℓ + 2 : ℂ) * mathieuFourierB (2 * m + 2) (2 * ℓ + 2) (h ^ 2) *
          mathieuCylSinh j (2 * ℓ + 2 : ℕ) h z))
      (radialMathieuMs j (2 * m + 2) z h) := by
  sorry

/-! ### §28.24 Expansions in series of cross-products of Bessel functions -/

/-- **Cross-product expansion** (DLMF 28.24.1), `j = 1, 2, 3, 4`, every `n ∈ ℤ`, every complex
`z`, `h ≠ 0`, admissible `(ν, h)`:
`c^ν_{2n}(h²) M^{(j)}_ν(z, h) = ∑_ℓ (-1)^ℓ c^ν_{2ℓ}(h²) J_{ℓ-n}(h e^{-z}) 𝒞^{(j)}_{ν+n+ℓ}(h e^z)`.
(For `n = modMathieuIndex ν h` this is the definition of `M^{(j)}_ν`; the content is the
convergence and the independence of `n`.) -/
@[dlmf 28.24.E1]
theorem hasSum_modMathieuTerm (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) {ν h : ℂ}
    (hν : ModMathieuAdmissible ν h) (hh : h ≠ 0) (n : ℤ) (z : ℂ) :
    HasSum (modMathieuTerm j ν z h n)
      (mathieuMeCoeff ν (h ^ 2) n * modMathieuM j ν z h) := by
  sorry

/-- **Absolute and locally uniform convergence** of the cross-product series (DLMF §28.24,
"the expansions (28.24.1)–(28.24.13) converge absolutely and uniformly on compact sets of the
`z`-plane"), in Weierstrass M-test form. -/
@[dlmf 28.24]
theorem modMathieuTerm_locally_uniform (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) {ν h : ℂ}
    (hν : ModMathieuAdmissible ν h) (hh : h ≠ 0) (n : ℤ) {K : Set ℂ} (hK : IsCompact K) :
    ∃ u : ℤ → ℝ, Summable u ∧ ∀ ℓ, ∀ z ∈ K, ‖modMathieuTerm j ν z h n ℓ‖ ≤ u ℓ := by
  sorry

/-- The summability of the defining series, a consequence of 28.24.1. -/
theorem summable_modMathieuTerm (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) {ν h : ℂ}
    (hν : ModMathieuAdmissible ν h) (hh : h ≠ 0) (n : ℤ) (z : ℂ) :
    Summable (modMathieuTerm j ν z h n) :=
  (hasSum_modMathieuTerm j hj₁ hj₄ hν hh n z).summable

/-- **Cross-product expansion** (DLMF 28.24.2), `j = 1, 2, 3, 4`, `s = 0, 1, …`, `h > 0`, all
`z`, `A^{2m}_{2s}(h²) ≠ 0`:
`ε_s Mc^{(j)}_{2m}(z, h) = (-1)^m ∑_ℓ (-1)^ℓ (A^{2m}_{2ℓ}/A^{2m}_{2s})
(J_{ℓ-s}(h e^{-z}) 𝒞^{(j)}_{ℓ+s}(h e^z) + J_{ℓ+s}(h e^{-z}) 𝒞^{(j)}_{ℓ-s}(h e^z))`. -/
@[dlmf 28.24.E2]
theorem hasSum_radialMathieuMc_even_cross (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m s : ℕ)
    {h : ℝ} (hh : 0 < h) (hA : mathieuFourierA (2 * m) (2 * s) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierA (2 * m) (2 * ℓ) (h ^ 2) / mathieuFourierA (2 * m) (2 * s) (h ^ 2)) *
        (besselJExp ((ℓ : ℤ) - s : ℤ) h (-z) * mathieuCylExp j ((ℓ + s : ℕ) : ℂ) h z +
          besselJExp ((ℓ + s : ℕ) : ℂ) h (-z) * mathieuCylExp j ((ℓ : ℤ) - s : ℤ) h z)))
      (mathieuEpsilon s * radialMathieuMc j (2 * m) z h) := by
  sorry

/-- **Cross-product expansion** (DLMF 28.24.3), as 28.24.2, `A^{2m+1}_{2s+1}(h²) ≠ 0`:
`Mc^{(j)}_{2m+1} = (-1)^m ∑_ℓ (-1)^ℓ (A^{2m+1}_{2ℓ+1}/A^{2m+1}_{2s+1})
(J_{ℓ-s} 𝒞^{(j)}_{ℓ+s+1} + J_{ℓ+s+1} 𝒞^{(j)}_{ℓ-s})`. -/
@[dlmf 28.24.E3]
theorem hasSum_radialMathieuMc_odd_cross (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m s : ℕ)
    {h : ℝ} (hh : 0 < h) (hA : mathieuFourierA (2 * m + 1) (2 * s + 1) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierA (2 * m + 1) (2 * ℓ + 1) (h ^ 2) /
          mathieuFourierA (2 * m + 1) (2 * s + 1) (h ^ 2)) *
        (besselJExp ((ℓ : ℤ) - s : ℤ) h (-z) * mathieuCylExp j ((ℓ + s + 1 : ℕ) : ℂ) h z +
          besselJExp ((ℓ + s + 1 : ℕ) : ℂ) h (-z) * mathieuCylExp j ((ℓ : ℤ) - s : ℤ) h z)))
      (radialMathieuMc j (2 * m + 1) z h) := by
  sorry

/-- **Cross-product expansion** (DLMF 28.24.4), `B^{2m+1}_{2s+1}(h²) ≠ 0`:
`Ms^{(j)}_{2m+1} = (-1)^m ∑_ℓ (-1)^ℓ (B^{2m+1}_{2ℓ+1}/B^{2m+1}_{2s+1})
(J_{ℓ-s} 𝒞^{(j)}_{ℓ+s+1} - J_{ℓ+s+1} 𝒞^{(j)}_{ℓ-s})`. -/
@[dlmf 28.24.E4]
theorem hasSum_radialMathieuMs_odd_cross (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m s : ℕ)
    {h : ℝ} (hh : 0 < h) (hB : mathieuFourierB (2 * m + 1) (2 * s + 1) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierB (2 * m + 1) (2 * ℓ + 1) (h ^ 2) /
          mathieuFourierB (2 * m + 1) (2 * s + 1) (h ^ 2)) *
        (besselJExp ((ℓ : ℤ) - s : ℤ) h (-z) * mathieuCylExp j ((ℓ + s + 1 : ℕ) : ℂ) h z -
          besselJExp ((ℓ + s + 1 : ℕ) : ℂ) h (-z) * mathieuCylExp j ((ℓ : ℤ) - s : ℤ) h z)))
      (radialMathieuMs j (2 * m + 1) z h) := by
  sorry

/-- **Cross-product expansion** (DLMF 28.24.5), `B^{2m+2}_{2s+2}(h²) ≠ 0`:
`Ms^{(j)}_{2m+2} = (-1)^m ∑_ℓ (-1)^ℓ (B^{2m+2}_{2ℓ+2}/B^{2m+2}_{2s+2})
(J_{ℓ-s} 𝒞^{(j)}_{ℓ+s+2} - J_{ℓ+s+2} 𝒞^{(j)}_{ℓ-s})`. -/
@[dlmf 28.24.E5]
theorem hasSum_radialMathieuMs_even_cross (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m s : ℕ)
    {h : ℝ} (hh : 0 < h) (hB : mathieuFourierB (2 * m + 2) (2 * s + 2) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierB (2 * m + 2) (2 * ℓ + 2) (h ^ 2) /
          mathieuFourierB (2 * m + 2) (2 * s + 2) (h ^ 2)) *
        (besselJExp ((ℓ : ℤ) - s : ℤ) h (-z) * mathieuCylExp j ((ℓ + s + 2 : ℕ) : ℂ) h z -
          besselJExp ((ℓ + s + 2 : ℕ) : ℂ) h (-z) * mathieuCylExp j ((ℓ : ℤ) - s : ℤ) h z)))
      (radialMathieuMs j (2 * m + 2) z h) := by
  sorry

open DLMF.Bessel in
/-- **Modified-Bessel cross-product expansion** (DLMF 28.24.6), `h > 0`, `s = 0, 1, …`,
`A^{2m}_{2s}(h²) ≠ 0`, all `z`:
`ε_s Ie_{2m}(z, h) = (-1)^s ∑_ℓ (-1)^ℓ (A^{2m}_{2ℓ}/A^{2m}_{2s})
(I_{ℓ-s}(h e^{-z}) I_{ℓ+s}(h e^z) + I_{ℓ+s}(h e^{-z}) I_{ℓ-s}(h e^z))`. -/
@[dlmf 28.24.E6]
theorem hasSum_modMathieuIe_even (m s : ℕ) {h : ℝ} (hh : 0 < h)
    (hA : mathieuFourierA (2 * m) (2 * s) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ s * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierA (2 * m) (2 * ℓ) (h ^ 2) / mathieuFourierA (2 * m) (2 * s) (h ^ 2)) *
        (besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp (-z)) *
            besselI ((ℓ + s : ℕ) : ℂ) (h * Complex.exp z) +
          besselI ((ℓ + s : ℕ) : ℂ) (h * Complex.exp (-z)) *
            besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp z))))
      (mathieuEpsilon s * modMathieuIe (2 * m) z h) := by
  sorry

open DLMF.Bessel in
/-- **Modified-Bessel cross-product expansion** (DLMF 28.24.7), `B^{2m+2}_{2s+2}(h²) ≠ 0`:
`Io_{2m+2}(z, h) = (-1)^s ∑_ℓ (-1)^ℓ (B^{2m+2}_{2ℓ+2}/B^{2m+2}_{2s+2})
(I_{ℓ-s} I_{ℓ+s+2} - I_{ℓ+s+2} I_{ℓ-s})`. -/
@[dlmf 28.24.E7]
theorem hasSum_modMathieuIo_even (m s : ℕ) {h : ℝ} (hh : 0 < h)
    (hB : mathieuFourierB (2 * m + 2) (2 * s + 2) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ s * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierB (2 * m + 2) (2 * ℓ + 2) (h ^ 2) /
          mathieuFourierB (2 * m + 2) (2 * s + 2) (h ^ 2)) *
        (besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp (-z)) *
            besselI ((ℓ + s + 2 : ℕ) : ℂ) (h * Complex.exp z) -
          besselI ((ℓ + s + 2 : ℕ) : ℂ) (h * Complex.exp (-z)) *
            besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp z))))
      (modMathieuIo (2 * m + 2) z h) := by
  sorry

open DLMF.Bessel in
/-- **Modified-Bessel cross-product expansion** (DLMF 28.24.8), `B^{2m+1}_{2s+1}(h²) ≠ 0` (the
`B` coefficients, since `Ie_{2m+1}` involves `q = -h²`):
`Ie_{2m+1}(z, h) = (-1)^s ∑_ℓ (-1)^ℓ (B^{2m+1}_{2ℓ+1}/B^{2m+1}_{2s+1})
(I_{ℓ-s} I_{ℓ+s+1} + I_{ℓ+s+1} I_{ℓ-s})`. -/
@[dlmf 28.24.E8]
theorem hasSum_modMathieuIe_odd (m s : ℕ) {h : ℝ} (hh : 0 < h)
    (hB : mathieuFourierB (2 * m + 1) (2 * s + 1) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ s * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierB (2 * m + 1) (2 * ℓ + 1) (h ^ 2) /
          mathieuFourierB (2 * m + 1) (2 * s + 1) (h ^ 2)) *
        (besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp (-z)) *
            besselI ((ℓ + s + 1 : ℕ) : ℂ) (h * Complex.exp z) +
          besselI ((ℓ + s + 1 : ℕ) : ℂ) (h * Complex.exp (-z)) *
            besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp z))))
      (modMathieuIe (2 * m + 1) z h) := by
  sorry

open DLMF.Bessel in
/-- **Modified-Bessel cross-product expansion** (DLMF 28.24.9), `A^{2m+1}_{2s+1}(h²) ≠ 0`:
`Io_{2m+1}(z, h) = (-1)^s ∑_ℓ (-1)^ℓ (A^{2m+1}_{2ℓ+1}/A^{2m+1}_{2s+1})
(I_{ℓ-s} I_{ℓ+s+1} - I_{ℓ+s+1} I_{ℓ-s})`. -/
@[dlmf 28.24.E9]
theorem hasSum_modMathieuIo_odd (m s : ℕ) {h : ℝ} (hh : 0 < h)
    (hA : mathieuFourierA (2 * m + 1) (2 * s + 1) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ s * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierA (2 * m + 1) (2 * ℓ + 1) (h ^ 2) /
          mathieuFourierA (2 * m + 1) (2 * s + 1) (h ^ 2)) *
        (besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp (-z)) *
            besselI ((ℓ + s + 1 : ℕ) : ℂ) (h * Complex.exp z) -
          besselI ((ℓ + s + 1 : ℕ) : ℂ) (h * Complex.exp (-z)) *
            besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp z))))
      (modMathieuIo (2 * m + 1) z h) := by
  sorry

open DLMF.Bessel in
/-- **Modified-Bessel cross-product expansion** (DLMF 28.24.10), `h > 0`, `|Im z| < π`
(principal-branch `K`; DLMF: all `z`, with `K` continued), `A^{2m}_{2s}(h²) ≠ 0`:
`ε_s Ke_{2m}(z, h) = ∑_ℓ (A^{2m}_{2ℓ}/A^{2m}_{2s})
(I_{ℓ-s}(h e^{-z}) K_{ℓ+s}(h e^z) + I_{ℓ+s}(h e^{-z}) K_{ℓ-s}(h e^z))`. -/
@[dlmf 28.24.E10]
theorem hasSum_modMathieuKe_even (m s : ℕ) {h : ℝ} (hh : 0 < h)
    (hA : mathieuFourierA (2 * m) (2 * s) (h ^ 2) ≠ 0) {z : ℂ} (hz : |z.im| < π) :
    HasSum (fun ℓ : ℕ =>
        (mathieuFourierA (2 * m) (2 * ℓ) (h ^ 2) / mathieuFourierA (2 * m) (2 * s) (h ^ 2)) *
        (besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp (-z)) *
            besselK ((ℓ + s : ℕ) : ℂ) (h * Complex.exp z) +
          besselI ((ℓ + s : ℕ) : ℂ) (h * Complex.exp (-z)) *
            besselK ((ℓ : ℤ) - s : ℤ) (h * Complex.exp z)))
      (mathieuEpsilon s * modMathieuKe (2 * m) z h) := by
  sorry

open DLMF.Bessel in
/-- **Modified-Bessel cross-product expansion** (DLMF 28.24.11), as 28.24.10,
`B^{2m+2}_{2s+2}(h²) ≠ 0`:
`Ko_{2m+2}(z, h) = ∑_ℓ (B^{2m+2}_{2ℓ+2}/B^{2m+2}_{2s+2}) (I_{ℓ-s} K_{ℓ+s+2} - I_{ℓ+s+2} K_{ℓ-s})`.
-/
@[dlmf 28.24.E11]
theorem hasSum_modMathieuKo_even (m s : ℕ) {h : ℝ} (hh : 0 < h)
    (hB : mathieuFourierB (2 * m + 2) (2 * s + 2) (h ^ 2) ≠ 0) {z : ℂ} (hz : |z.im| < π) :
    HasSum (fun ℓ : ℕ =>
        (mathieuFourierB (2 * m + 2) (2 * ℓ + 2) (h ^ 2) /
          mathieuFourierB (2 * m + 2) (2 * s + 2) (h ^ 2)) *
        (besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp (-z)) *
            besselK ((ℓ + s + 2 : ℕ) : ℂ) (h * Complex.exp z) -
          besselI ((ℓ + s + 2 : ℕ) : ℂ) (h * Complex.exp (-z)) *
            besselK ((ℓ : ℤ) - s : ℤ) (h * Complex.exp z)))
      (modMathieuKo (2 * m + 2) z h) := by
  sorry

open DLMF.Bessel in
/-- **Modified-Bessel cross-product expansion** (DLMF 28.24.12), as 28.24.10,
`B^{2m+1}_{2s+1}(h²) ≠ 0`:
`Ke_{2m+1}(z, h) = ∑_ℓ (B^{2m+1}_{2ℓ+1}/B^{2m+1}_{2s+1}) (I_{ℓ-s} K_{ℓ+s+1} - I_{ℓ+s+1} K_{ℓ-s})`.
-/
@[dlmf 28.24.E12]
theorem hasSum_modMathieuKe_odd (m s : ℕ) {h : ℝ} (hh : 0 < h)
    (hB : mathieuFourierB (2 * m + 1) (2 * s + 1) (h ^ 2) ≠ 0) {z : ℂ} (hz : |z.im| < π) :
    HasSum (fun ℓ : ℕ =>
        (mathieuFourierB (2 * m + 1) (2 * ℓ + 1) (h ^ 2) /
          mathieuFourierB (2 * m + 1) (2 * s + 1) (h ^ 2)) *
        (besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp (-z)) *
            besselK ((ℓ + s + 1 : ℕ) : ℂ) (h * Complex.exp z) -
          besselI ((ℓ + s + 1 : ℕ) : ℂ) (h * Complex.exp (-z)) *
            besselK ((ℓ : ℤ) - s : ℤ) (h * Complex.exp z)))
      (modMathieuKe (2 * m + 1) z h) := by
  sorry

open DLMF.Bessel in
/-- **Modified-Bessel cross-product expansion** (DLMF 28.24.13), as 28.24.10,
`A^{2m+1}_{2s+1}(h²) ≠ 0`:
`Ko_{2m+1}(z, h) = ∑_ℓ (A^{2m+1}_{2ℓ+1}/A^{2m+1}_{2s+1}) (I_{ℓ-s} K_{ℓ+s+1} + I_{ℓ+s+1} K_{ℓ-s})`.
-/
@[dlmf 28.24.E13]
theorem hasSum_modMathieuKo_odd (m s : ℕ) {h : ℝ} (hh : 0 < h)
    (hA : mathieuFourierA (2 * m + 1) (2 * s + 1) (h ^ 2) ≠ 0) {z : ℂ} (hz : |z.im| < π) :
    HasSum (fun ℓ : ℕ =>
        (mathieuFourierA (2 * m + 1) (2 * ℓ + 1) (h ^ 2) /
          mathieuFourierA (2 * m + 1) (2 * s + 1) (h ^ 2)) *
        (besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp (-z)) *
            besselK ((ℓ + s + 1 : ℕ) : ℂ) (h * Complex.exp z) +
          besselI ((ℓ + s + 1 : ℕ) : ℂ) (h * Complex.exp (-z)) *
            besselK ((ℓ : ℤ) - s : ℤ) (h * Complex.exp z)))
      (modMathieuKo (2 * m + 1) z h) := by
  sorry

end DLMF.Mathieu
