/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.SymmetricSpecialCases
public import Carlson.Elliptic.Landen
public import Carlson.TwoVariable.QuadraticHybrid

/-!
# Symmetric elliptic integrals: quadratic transformations (DLMF §19.22)

Gauss and Landen transformations of the complete integrals (§19.22(i)), Bartky's
transformation, the AGM algorithms (§19.22(ii); `M(a₀, g₀)` is Mathlib's `NNReal.agm`), and
the incomplete transformations (§19.22(iii)).

**Proved from `lean-codes`:** (19.22.1) from `Carlson.TwoVariable.carlsonRK_sq_eq`, (19.22.8)
from `Carlson.TwoVariable.carlsonRK_sq_eq_inv_agm`, (19.22.22) from
`Carlson.TwoVariable.carlsonRC_sq_eq`, and (19.22.18) for real positive `x, y, z` with
`(z - x)(z - y) ≥ 0` (Landen/Gauss, `Carlson.carlsonRF_landen_explicit`) and for
`x < z < y` (conjugate `z±`, `Carlson.carlsonRF_landen_conj`).

**Branches.** `p±`, `z±` are defined with principal square roots as printed in (19.22.5),
(19.22.16). The identities `p₊p₋ = pa`, `p₊² + p₋² = p² + xy` (19.22.6) hold for all complex
values; the last two identities of (19.22.6), (19.22.17) involve `√((p²-x²)(p²-y²))` and are
stated for real `p ≥ x, y > 0` (for complex arguments the printed square roots need a branch
convention). The second equation of (19.22.23) is stated likewise for real positive data with
`z ≥ x, y`.

Prose 19.22.iii.p2–p4 (ascending Landen versus descending Gauss; conjugate `z±` when `z` lies
between `x` and `y`; caution on (19.22.23)) is commentary on the stated formulas.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Real Topology NNReal

namespace DLMF.EllipticIntegrals

theorem ei19c_sq_mem_slitPlane {x : ℂ} (hx : 0 < x.re) : x ^ 2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases h : x.im = 0
  · left; simp [pow_two, h]; positivity
  · right; simp only [pow_two, mul_im]
    intro h'
    have : x.re * x.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact h h1

theorem ei19c_mul_mem_slitPlane {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) : x * y ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases h : (x * y).im = 0
  · left
    simp only [mul_im] at h
    simp only [mul_re]
    have : y.re * (x.re * y.re - x.im * y.im) = x.re * (y.re ^ 2 + y.im ^ 2) := by
      linear_combination (-y.im) * h
    have h2 : 0 < x.re * (y.re ^ 2 + y.im ^ 2) := mul_pos hx (by nlinarith)
    nlinarith
  · exact Or.inr h

theorem ei19c_half_add_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) : 0 < ((x + y) / 2).re := by
  simp; linarith

/-! ### §19.22(i) Complete integrals -/

/-- DLMF 19.22.1: `R_F(0, x², y²) = R_F(0, xy, a²)`, `a = (x + y)/2`, `Re x, Re y > 0`. -/
@[dlmf 19.22.E1]
theorem symEllIntRF_zero_sq {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    symEllIntRF 0 (x ^ 2) (y ^ 2) = symEllIntRF 0 (x * y) (((x + y) / 2) ^ 2) := by
  have ha := ei19c_half_add_re_pos hx hy
  rw [symEllIntRF_zero_left (ei19c_sq_mem_slitPlane hx) (ei19c_sq_mem_slitPlane hy),
    symEllIntRF_zero_left (ei19c_mul_mem_slitPlane hx hy) (ei19c_sq_mem_slitPlane ha),
    symEllIntR_of_mem _ _ (ei19c_slit2 (ei19c_sq_mem_slitPlane hx) (ei19c_sq_mem_slitPlane hy)),
    symEllIntR_of_mem _ _ (ei19c_slit2 (ei19c_mul_mem_slitPlane hx hy) (ei19c_sq_mem_slitPlane ha))]
  have h := Carlson.TwoVariable.carlsonRK_sq_eq x y hx hy
  rw [Carlson.TwoVariable.carlsonRK_comm (ei19c_sq_mem_slitPlane ha)
    (ei19c_mul_mem_slitPlane hx hy)] at h
  unfold Carlson.TwoVariable.carlsonRK Carlson.TwoVariable.pair at h
  rw [show (-(1 / 2) : ℂ) = -1 / 2 by ring, h]

/-- DLMF 19.22.2: `2R_G(0, x², y²) = 4R_G(0, xy, a²) - xy R_F(0, xy, a²)`, `Re x, Re y > 0`. -/
@[dlmf 19.22.E2]
theorem symEllIntRG_zero_sq {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    2 * symEllIntRG 0 (x ^ 2) (y ^ 2) =
      4 * symEllIntRG 0 (x * y) (((x + y) / 2) ^ 2) - x * y * symEllIntRF 0 (x * y) (((x + y) / 2) ^ 2) := by
  sorry

/-- DLMF 19.22.3: `2y² R_D(0, x², y²) = (1/4)(y² - x²) R_D(0, xy, a²) + 3R_F(0, xy, a²)`. -/
@[dlmf 19.22.E3]
theorem symEllIntRD_zero_sq {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    2 * y ^ 2 * symEllIntRD 0 (x ^ 2) (y ^ 2) =
      (1 / 4) * (y ^ 2 - x ^ 2) * symEllIntRD 0 (x * y) (((x + y) / 2) ^ 2) +
        3 * symEllIntRF 0 (x * y) (((x + y) / 2) ^ 2) := by
  sorry

/-- DLMF 19.22.5: `2p± = √((p + x)(p + y)) ± √((p - x)(p - y))` (principal roots); `s = ±1`. -/
def symEllIntPm (s x y p : ℂ) : ℂ :=
  ((((p + x) * (p + y)) ^ (1 / 2 : ℂ)) + s * (((p - x) * (p - y)) ^ (1 / 2 : ℂ))) / 2

/-- DLMF 19.22.4 with 19.22.5: `(p±² - p∓²) R_J(0, x², y², p²) = 2(p±² - a²) R_J(0, xy, a², p±²)
- 3R_F(0, xy, a²) + 3π/(2p)`, `Re x, Re y > 0`, `p ≠ 0`; `s = ±1` selects the sign. We assume
`Re p > 0` so that `p²` is in the slit plane. -/
@[dlmf 19.22.E4, dlmf 19.22.E5]
theorem symEllIntRJ_zero_sq {x y p s : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) (hp : 0 < p.re)
    (hs : s = 1 ∨ s = -1) :
    (symEllIntPm s x y p ^ 2 - symEllIntPm (-s) x y p ^ 2) * symEllIntRJ 0 (x ^ 2) (y ^ 2) (p ^ 2) =
      2 * (symEllIntPm s x y p ^ 2 - ((x + y) / 2) ^ 2) *
          symEllIntRJ 0 (x * y) (((x + y) / 2) ^ 2) (symEllIntPm s x y p ^ 2) -
        3 * symEllIntRF 0 (x * y) (((x + y) / 2) ^ 2) + 3 * π / (2 * p) := by
  sorry

/-- DLMF 19.22.6 (first two identities, all complex values): `p₊ p₋ = pa`,
`p₊² + p₋² = p² + xy`, `a = (x + y)/2`. -/
@[dlmf 19.22.E6]
theorem symEllIntPm_mul_add (x y p : ℂ) :
    symEllIntPm 1 x y p * symEllIntPm (-1) x y p = p * ((x + y) / 2) ∧
      symEllIntPm 1 x y p ^ 2 + symEllIntPm (-1) x y p ^ 2 = p ^ 2 + x * y := by
  have h1 := ei19c_cpow_half_sq ((p + x) * (p + y))
  have h2 := ei19c_cpow_half_sq ((p - x) * (p - y))
  unfold symEllIntPm
  constructor
  · linear_combination (1 / 4 : ℂ) * h1 - (1 / 4 : ℂ) * h2
  · linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2

/-- DLMF 19.22.6 (last two identities), real case `p ≥ x > 0`, `p ≥ y > 0`:
`p₊² - p₋² = √((p² - x²)(p² - y²))`, `4(p±² - a²) = (√(p² - x²) ± √(p² - y²))²`. -/
@[dlmf 19.22.E6]
theorem symEllIntPm_sub_real {x y p : ℝ} (hx : 0 < x) (hy : 0 < y) (hpx : x ≤ p) (hpy : y ≤ p)
    {s : ℝ} (hs : s = 1 ∨ s = -1) :
    let P : ℝ := (Real.sqrt ((p + x) * (p + y)) + s * Real.sqrt ((p - x) * (p - y))) / 2
    let Q : ℝ := (Real.sqrt ((p + x) * (p + y)) - s * Real.sqrt ((p - x) * (p - y))) / 2
    P ^ 2 - Q ^ 2 = s * Real.sqrt ((p ^ 2 - x ^ 2) * (p ^ 2 - y ^ 2)) ∧
      4 * (P ^ 2 - ((x + y) / 2) ^ 2) =
        (Real.sqrt (p ^ 2 - x ^ 2) + s * Real.sqrt (p ^ 2 - y ^ 2)) ^ 2 := by
  intro P Q
  have hA : 0 ≤ (p + x) * (p + y) := mul_nonneg (by linarith) (by linarith)
  have hB : 0 ≤ (p - x) * (p - y) := mul_nonneg (by linarith) (by linarith)
  have hC : 0 ≤ p ^ 2 - x ^ 2 := by nlinarith
  have hD : 0 ≤ p ^ 2 - y ^ 2 := by nlinarith
  have hAB : Real.sqrt ((p + x) * (p + y)) * Real.sqrt ((p - x) * (p - y)) =
      Real.sqrt (p ^ 2 - x ^ 2) * Real.sqrt (p ^ 2 - y ^ 2) := by
    rw [← Real.sqrt_mul hA, ← Real.sqrt_mul hC]; congr 1; ring
  have hCD : Real.sqrt ((p ^ 2 - x ^ 2) * (p ^ 2 - y ^ 2)) =
      Real.sqrt (p ^ 2 - x ^ 2) * Real.sqrt (p ^ 2 - y ^ 2) := Real.sqrt_mul hC _
  have hA2 := Real.sq_sqrt hA
  have hB2 := Real.sq_sqrt hB
  have hC2 := Real.sq_sqrt hC
  have hD2 := Real.sq_sqrt hD
  have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  rw [hCD]
  constructor
  · simp only [P, Q]; linear_combination s * hAB
  · simp only [P]
    linear_combination hA2 + s ^ 2 * hB2 - hC2 - s ^ 2 * hD2 + 2 * s * hAB +
      (-p * x - p * y + x * y + y ^ 2) * hs2
/-- DLMF 19.22.7 (Bartky's transformation): `2p² R_J(0, x², y², p²) = v₊ v₋ R_J(0, xy, a², v₊²)
+ 3R_F(0, xy, a²)`, `v± = (p² ± xy)/(2p)`; `Re x, Re y, Re p > 0`. -/
@[dlmf 19.22.E7]
theorem symEllIntRJ_zero_sq_bartky {x y p : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) (hp : 0 < p.re) :
    2 * p ^ 2 * symEllIntRJ 0 (x ^ 2) (y ^ 2) (p ^ 2) =
      (p ^ 2 + x * y) / (2 * p) * ((p ^ 2 - x * y) / (2 * p)) *
          symEllIntRJ 0 (x * y) (((x + y) / 2) ^ 2) (((p ^ 2 + x * y) / (2 * p)) ^ 2) +
        3 * symEllIntRF 0 (x * y) (((x + y) / 2) ^ 2) := by
  sorry

/-! ### §19.22(ii) The AGM -/

/-- DLMF 19.22.8: `(2/π) R_F(0, a₀², g₀²) = 1/M(a₀, g₀)` for `a₀, g₀ > 0` (DLMF assumes
`a₀ ≥ g₀`; not needed). -/
@[dlmf 19.22.E8]
theorem symEllIntRF_zero_eq_inv_agm {a₀ g₀ : ℝ≥0} (ha : 0 < a₀) (hg : 0 < g₀) :
    (2 / π) * symEllIntRF 0 (((a₀ : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) =
      ((NNReal.agm a₀ g₀ : ℝ) : ℂ)⁻¹ := by
  have hx : (0 : ℝ) < (((a₀ : ℝ) : ℂ)).re := by simpa using ha
  have hy : (0 : ℝ) < (((g₀ : ℝ) : ℂ)).re := by simpa using hg
  rw [symEllIntRF_zero_left (ei19c_sq_mem_slitPlane hx) (ei19c_sq_mem_slitPlane hy),
    symEllIntR_of_mem _ _ (ei19c_slit2 (ei19c_sq_mem_slitPlane hx) (ei19c_sq_mem_slitPlane hy)),
    ← Carlson.TwoVariable.carlsonRK_sq_eq_inv_agm ha hg]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold Carlson.TwoVariable.carlsonRK Carlson.TwoVariable.pair
  rw [show (-(1 / 2) : ℂ) = -1 / 2 by ring]
  field_simp

/-- The AGM sequences `(aₙ, gₙ)` of DLMF §19.8(i) (Mathlib's `NNReal.agmSequences`, which
returns `(gₙ₊₁, aₙ₊₁)`), with `a₀, g₀` themselves at index 0, and `cₙ² = aₙ² - gₙ²`. -/
def agmA (a₀ g₀ : ℝ≥0) : ℕ → ℝ
  | 0 => a₀
  | n + 1 => ((NNReal.agmSequences a₀ g₀ (n + 1)).2 : ℝ)

/-- The geometric-mean sequence `gₙ` (`g₀` at index 0). -/
def agmG (a₀ g₀ : ℝ≥0) : ℕ → ℝ
  | 0 => g₀
  | n + 1 => ((NNReal.agmSequences a₀ g₀ (n + 1)).1 : ℝ)

/-- DLMF 19.22.9: `(4/π) R_G(0, a₀², g₀²) = (1/M)(a₀² - ∑_{n≥0} 2^{n-1} cₙ²)
= (1/M)(a₁² - ∑_{n≥2} 2^{n-1} cₙ²)`, `cₙ² = aₙ² - gₙ²`, `a₀ ≥ g₀ > 0`. -/
@[dlmf 19.22.E9]
theorem symEllIntRG_zero_agm {a₀ g₀ : ℝ≥0} (hg : 0 < g₀) (hag : g₀ ≤ a₀) :
    (4 / π) * symEllIntRG 0 (((a₀ : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) =
        ((((NNReal.agm a₀ g₀ : ℝ))⁻¹ * ((a₀ : ℝ) ^ 2 -
          ∑' n : ℕ, (2 : ℝ) ^ ((n : ℤ) - 1) * (agmA a₀ g₀ n ^ 2 - agmG a₀ g₀ n ^ 2)) : ℝ) : ℂ) ∧
      (4 / π) * symEllIntRG 0 (((a₀ : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) =
        ((((NNReal.agm a₀ g₀ : ℝ))⁻¹ * (agmA a₀ g₀ 1 ^ 2 -
          ∑' n : ℕ, (2 : ℝ) ^ ((n : ℤ) + 1) * (agmA a₀ g₀ (n + 2) ^ 2 - agmG a₀ g₀ (n + 2) ^ 2)) : ℝ) : ℂ) := by
  sorry

/-- DLMF 19.22.11: `Q₀ = 1`, `Qₙ₊₁ = (1/2) Qₙ (aₙ - gₙ)/(aₙ + gₙ)`. -/
def agmQ (a₀ g₀ : ℝ≥0) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (1 / 2) * agmQ a₀ g₀ n * (agmA a₀ g₀ n - agmG a₀ g₀ n) / (agmA a₀ g₀ n + agmG a₀ g₀ n)

/-- DLMF 19.22.10 with 19.22.11: `R_D(0, g₀², a₀²) = 3π/(4 M a₀²) ∑ Qₙ`, `a₀, g₀ > 0`
(here DLMF does not need `a₀ ≥ g₀`). -/
@[dlmf 19.22.E10, dlmf 19.22.E11]
theorem symEllIntRD_zero_agm {a₀ g₀ : ℝ≥0} (ha : 0 < a₀) (hg : 0 < g₀) :
    HasSum (fun n => ((3 * π / (4 * (NNReal.agm a₀ g₀ : ℝ) * (a₀ : ℝ) ^ 2) * agmQ a₀ g₀ n : ℝ) : ℂ))
      (symEllIntRD 0 (((g₀ : ℝ) : ℂ) ^ 2) (((a₀ : ℝ) : ℂ) ^ 2)) := by
  sorry

/-- DLMF 19.22.11 (last sentence): `Qₙ` has the sign of `a₀ - g₀` for `n ≥ 1`. -/
@[dlmf 19.22.E11]
theorem agmQ_sign {a₀ g₀ : ℝ≥0} (ha : 0 < a₀) (hg : 0 < g₀) (n : ℕ) :
    SignType.sign (agmQ a₀ g₀ (n + 1)) = SignType.sign ((a₀ : ℝ) - g₀) := by
  sorry

/-- DLMF 19.22.13: `pₙ₊₁ = (pₙ² + aₙgₙ)/(2pₙ)`, `εₙ = (pₙ² - aₙgₙ)/(pₙ² + aₙgₙ)`, `Q₀ = 1`,
`Qₙ₊₁ = (1/2) Qₙ εₙ`. -/
def agmP (a₀ g₀ : ℝ≥0) (p₀ : ℝ) : ℕ → ℝ
  | 0 => p₀
  | n + 1 => (agmP a₀ g₀ p₀ n ^ 2 + agmA a₀ g₀ n * agmG a₀ g₀ n) / (2 * agmP a₀ g₀ p₀ n)

/-- DLMF 19.22.13: the sequence `Qₙ` for `R_J`. -/
def agmQJ (a₀ g₀ : ℝ≥0) (p₀ : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (1 / 2) * agmQJ a₀ g₀ p₀ n *
      ((agmP a₀ g₀ p₀ n ^ 2 - agmA a₀ g₀ n * agmG a₀ g₀ n) /
        (agmP a₀ g₀ p₀ n ^ 2 + agmA a₀ g₀ n * agmG a₀ g₀ n))

/-- DLMF 19.22.12 with 19.22.13: `R_J(0, g₀², a₀², p₀²) = 3π/(4 M p₀²) ∑ Qₙ`, `p₀ > 0`. -/
@[dlmf 19.22.E12, dlmf 19.22.E13]
theorem symEllIntRJ_zero_agm {a₀ g₀ : ℝ≥0} (ha : 0 < a₀) (hg : 0 < g₀) {p₀ : ℝ} (hp : 0 < p₀) :
    HasSum (fun n => ((3 * π / (4 * (NNReal.agm a₀ g₀ : ℝ) * p₀ ^ 2) * agmQJ a₀ g₀ p₀ n : ℝ) : ℂ))
      (symEllIntRJ 0 (((g₀ : ℝ) : ℂ) ^ 2) (((a₀ : ℝ) : ℂ) ^ 2) ((p₀ : ℂ) ^ 2)) := by
  sorry

/-- DLMF 19.22.13 (convergence statement): `pₙ → M(a₀, g₀)` and `εₙ → 0` (quadratically). -/
@[dlmf 19.22.E13]
theorem tendsto_agmP {a₀ g₀ : ℝ≥0} (ha : 0 < a₀) (hg : 0 < g₀) {p₀ : ℝ} (hp : 0 < p₀) :
    Tendsto (agmP a₀ g₀ p₀) atTop (𝓝 (NNReal.agm a₀ g₀ : ℝ)) := by
  sorry

/-- DLMF 19.22.14 with 19.22.15: the Cauchy principal value
`R_J(0, g₀², a₀², -q₀²) = -3π/(4M(q₀² + a₀²)) (2 + (a₀² - g₀²)/(q₀² + g₀²) ∑ Qₙ)`, with (19.22.13)
started from `p₀² = a₀²(q₀² + g₀²)/(q₀² + a₀²)`, `q₀ > 0`. -/
@[dlmf 19.22.E14, dlmf 19.22.E15]
theorem symEllIntRJ_zero_agm_neg {a₀ g₀ : ℝ≥0} (ha : 0 < a₀) (hg : 0 < g₀) {q₀ : ℝ} (hq : 0 < q₀) :
    let p₀ : ℝ := Real.sqrt ((a₀ : ℝ) ^ 2 * (q₀ ^ 2 + (g₀ : ℝ) ^ 2) / (q₀ ^ 2 + (a₀ : ℝ) ^ 2))
    symEllIntRJ 0 (((g₀ : ℝ) : ℂ) ^ 2) (((a₀ : ℝ) : ℂ) ^ 2) ((-q₀ ^ 2 : ℝ) : ℂ) =
      ((-3 * π / (4 * (NNReal.agm a₀ g₀ : ℝ) * (q₀ ^ 2 + (a₀ : ℝ) ^ 2)) *
        (2 + ((a₀ : ℝ) ^ 2 - (g₀ : ℝ) ^ 2) / (q₀ ^ 2 + (g₀ : ℝ) ^ 2) *
          ∑' n, agmQJ a₀ g₀ p₀ n) : ℝ) : ℂ) := by
  sorry

/-! ### §19.22(iii) Incomplete integrals -/

/-- DLMF 19.22.18: `R_F(x², y², z²) = R_F(a², z₋², z₊²)` with (19.22.16)
`2z± = √((z + x)(z + y)) ± √((z - x)(z - y))`; `Re x, Re y, Re z > 0`. -/
@[dlmf 19.22.E18, dlmf 19.22.E16]
theorem symEllIntRF_sq_landen {x y z : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) (hz : 0 < z.re) :
    symEllIntRF (x ^ 2) (y ^ 2) (z ^ 2) =
      symEllIntRF (((x + y) / 2) ^ 2) (symEllIntPm (-1) x y z ^ 2) (symEllIntPm 1 x y z ^ 2) := by
  sorry

/-- DLMF 19.22.18, real case `x, y, z > 0`, `(z - x)(z - y) ≥ 0` (ascending Landen for
`x, y < z`, descending Gauss for `z < x, y`). From `Carlson.carlsonRF_landen_explicit`. -/
@[dlmf 19.22.E18]
theorem symEllIntRF_sq_landen_real {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hzxy : 0 ≤ (z - x) * (z - y)) :
    symEllIntRF ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) ((z ^ 2 : ℝ) : ℂ) =
      symEllIntRF ((((x + y) / 2) ^ 2 : ℝ) : ℂ)
        ((((Real.sqrt ((z + x) * (z + y)) - Real.sqrt ((z - x) * (z - y))) / 2) ^ 2 : ℝ) : ℂ)
        ((((Real.sqrt ((z + x) * (z + y)) + Real.sqrt ((z - x) * (z - y))) / 2) ^ 2 : ℝ) : ℂ) := by
  have hpos : ∀ {w : ℝ}, 0 < w → ((w ^ 2 : ℝ) : ℂ) ∈ slitPlane := fun hw =>
    ofReal_mem_slitPlane.mpr (by positivity)
  set P := Real.sqrt ((z + x) * (z + y))
  set Q := Real.sqrt ((z - x) * (z - y))
  have hP2 : P ^ 2 = (z + x) * (z + y) := Real.sq_sqrt (by positivity)
  have hQ2 : Q ^ 2 = (z - x) * (z - y) := Real.sq_sqrt hzxy
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  have hPQ : Q < P := Real.sqrt_lt_sqrt hzxy (by nlinarith)
  have h := Carlson.carlsonRF_landen_explicit hx hy hz hzxy
  rw [symEllIntRF_eq_carlsonRF (hpos hx) (hpos hy) (hpos hz), h,
    symEllIntRF_comm_right, symEllIntRF_eq_carlsonRF (hpos (by positivity)) (hpos (by linarith))
      (hpos (by linarith))]

/-- DLMF 19.22.18, real case `x < z < y` (then `z±` are complex conjugates). From
`Carlson.carlsonRF_landen_conj`. -/
@[dlmf 19.22.E18]
theorem symEllIntRF_sq_landen_conj {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxz : x < z) (hzy : z < y) :
    symEllIntRF ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) ((z ^ 2 : ℝ) : ℂ) =
      symEllIntRF ((((x + y) / 2) ^ 2 : ℝ) : ℂ)
        ((((Real.sqrt ((z + x) * (z + y)) : ℂ) + I * Real.sqrt ((z - x) * (y - z))) / 2) ^ 2)
        ((((Real.sqrt ((z + x) * (z + y)) : ℂ) - I * Real.sqrt ((z - x) * (y - z))) / 2) ^ 2) := by
  sorry

/-- DLMF 19.22.17 (first two identities, all complex values): `z₊ z₋ = za`,
`z₊² + z₋² = z² + xy`. (The other two are those of `symEllIntPm_sub_real` with `p := z`.) -/
@[dlmf 19.22.E17]
theorem symEllIntPm_mul_add_z (x y z : ℂ) :
    symEllIntPm 1 x y z * symEllIntPm (-1) x y z = z * ((x + y) / 2) ∧
      symEllIntPm 1 x y z ^ 2 + symEllIntPm (-1) x y z ^ 2 = z ^ 2 + x * y :=
  symEllIntPm_mul_add x y z

/-- DLMF 19.22.19: `(z±² - z∓²) R_D(x², y², z²) = 2(z±² - a²) R_D(a², z∓², z±²)
- 3R_F(x², y², z²) + 3/z`; `Re x, Re y, Re z > 0`, `s = ±1`. -/
@[dlmf 19.22.E19]
theorem symEllIntRD_sq_landen {x y z s : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) (hz : 0 < z.re)
    (hs : s = 1 ∨ s = -1) :
    (symEllIntPm s x y z ^ 2 - symEllIntPm (-s) x y z ^ 2) * symEllIntRD (x ^ 2) (y ^ 2) (z ^ 2) =
      2 * (symEllIntPm s x y z ^ 2 - ((x + y) / 2) ^ 2) *
          symEllIntRD (((x + y) / 2) ^ 2) (symEllIntPm (-s) x y z ^ 2) (symEllIntPm s x y z ^ 2) -
        3 * symEllIntRF (x ^ 2) (y ^ 2) (z ^ 2) + 3 / z := by
  sorry

/-- DLMF 19.22.20: `(p±² - p∓²) R_J(x², y², z², p²) = 2(p±² - a²) R_J(a², z₊², z₋², p±²)
- 3R_F(x², y², z²) + 3R_C(z², p²)`; `Re x, Re y, Re z, Re p > 0`, `s = ±1`. -/
@[dlmf 19.22.E20]
theorem symEllIntRJ_sq_landen {x y z p s : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) (hz : 0 < z.re)
    (hp : 0 < p.re) (hs : s = 1 ∨ s = -1) :
    (symEllIntPm s x y p ^ 2 - symEllIntPm (-s) x y p ^ 2) *
        symEllIntRJ (x ^ 2) (y ^ 2) (z ^ 2) (p ^ 2) =
      2 * (symEllIntPm s x y p ^ 2 - ((x + y) / 2) ^ 2) *
          symEllIntRJ (((x + y) / 2) ^ 2) (symEllIntPm 1 x y z ^ 2) (symEllIntPm (-1) x y z ^ 2)
            (symEllIntPm s x y p ^ 2) -
        3 * symEllIntRF (x ^ 2) (y ^ 2) (z ^ 2) + 3 * symEllIntRC (z ^ 2) (p ^ 2) := by
  sorry

/-- DLMF 19.22.21: `2R_G(x², y², z²) = 4R_G(a², z₊², z₋²) - xy R_F(x², y², z²) - z`;
`Re x, Re y, Re z > 0`. -/
@[dlmf 19.22.E21]
theorem symEllIntRG_sq_landen {x y z : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) (hz : 0 < z.re) :
    2 * symEllIntRG (x ^ 2) (y ^ 2) (z ^ 2) =
      4 * symEllIntRG (((x + y) / 2) ^ 2) (symEllIntPm 1 x y z ^ 2) (symEllIntPm (-1) x y z ^ 2) -
        x * y * symEllIntRF (x ^ 2) (y ^ 2) (z ^ 2) - z := by
  sorry

/-- DLMF 19.22.22: `R_C(x², y²) = R_C(a², ay)`, `a = (x + y)/2`, `Re x, Re y > 0`. From
`Carlson.TwoVariable.carlsonRC_sq_eq`. -/
@[dlmf 19.22.E22]
theorem symEllIntRC_sq {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    symEllIntRC (x ^ 2) (y ^ 2) = symEllIntRC (((x + y) / 2) ^ 2) ((x + y) / 2 * y) := by
  have ha := ei19c_half_add_re_pos hx hy
  rw [symEllIntRC_eq_carlsonRC (ei19c_sq_mem_slitPlane hx) (ei19c_sq_mem_slitPlane hy),
    symEllIntRC_eq_carlsonRC (ei19c_sq_mem_slitPlane ha) (ei19c_mul_mem_slitPlane ha hy),
    Carlson.TwoVariable.carlsonRC_sq_eq x y hx hy]

/-- DLMF 19.22.23 (first and third equations, all complex values with `a ≠ 0`):
`x + y = 2a` and `z = z₊ z₋ / a`, `a = (x + y)/2`. -/
@[dlmf 19.22.E23]
theorem symEllIntPm_inverse (x y z : ℂ) (ha : (x + y) / 2 ≠ 0) :
    x + y = 2 * ((x + y) / 2) ∧
      z = symEllIntPm 1 x y z * symEllIntPm (-1) x y z / ((x + y) / 2) := by
  refine ⟨by ring, ?_⟩
  have h2 : x + y ≠ 0 := by intro h; apply ha; simp [h]
  rw [(symEllIntPm_mul_add x y z).1]; field_simp

/-- DLMF 19.22.23 (second equation), real case `x ≥ y > 0`, `z ≥ x`:
`x - y = (2/a) √((a² - z₊²)(a² - z₋²))`. -/
@[dlmf 19.22.E23]
theorem symEllIntPm_inverse_sub_real {x y z : ℝ} (hy : 0 < y) (hxy : y ≤ x) (hzx : x ≤ z) :
    let zp : ℝ := (Real.sqrt ((z + x) * (z + y)) + Real.sqrt ((z - x) * (z - y))) / 2
    let zm : ℝ := (Real.sqrt ((z + x) * (z + y)) - Real.sqrt ((z - x) * (z - y))) / 2
    x - y = 2 / ((x + y) / 2) * Real.sqrt ((((x + y) / 2) ^ 2 - zp ^ 2) * (((x + y) / 2) ^ 2 - zm ^ 2)) := by
  sorry

end DLMF.EllipticIntegrals
