/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.SymmetricSpecialCases
public import Carlson.Elliptic.AGMSecondKind
public import DLMF.EllipticIntegrals.SymmetricConnection

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

lemma ei19c_sq_mem_slitPlane {x : ℂ} (hx : 0 < x.re) : x ^ 2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases h : x.im = 0
  · left; simp [pow_two, h]; positivity
  · right; simp only [pow_two, mul_im]
    intro h'
    have : x.re * x.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact h h1

lemma ei19c_mul_mem_slitPlane {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) : x * y ∈ slitPlane := by
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

lemma ei19c_half_add_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) : 0 < ((x + y) / 2).re := by
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


/-- Round-1 helper: `R_G(0, y, z) = (π/4) R_E(y, z)` on the slit plane. -/
theorem p19sR1_symEllIntRG_zero_eq_carlsonRE {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symEllIntRG 0 y z = (π / 4) * Carlson.carlsonRE y z := by
  rw [(symEllIntRG_zero_left hy hz).1, symEllIntR_of_mem _ _ (ei19c_slit2 hy hz),
    Carlson.carlsonRE]
  congr 2; norm_num

/-- Round-1 helper: `R_F(0, y, z) = (π/2) R_K(y, z)` on the slit plane. -/
theorem p19sR1_symEllIntRF_zero_eq_carlsonRK {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symEllIntRF 0 y z = (π / 2) * Carlson.TwoVariable.carlsonRK y z := by
  rw [symEllIntRF_zero_left hy hz, symEllIntR_of_mem _ _ (ei19c_slit2 hy hz),
    Carlson.TwoVariable.carlsonRK]
  congr 2; norm_num

theorem p19sR1_carlsonRE_comm {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    Carlson.carlsonRE y z = Carlson.carlsonRE z y := by
  unfold Carlson.carlsonRE Carlson.carlsonR
  rw [Carlson.TwoVariable.regCarlsonR_pair_swap _ _ _ hz hy]

/-- DLMF 19.22.2: `2R_G(0, x², y²) = 4R_G(0, xy, a²) - xy R_F(0, xy, a²)`, `Re x, Re y > 0`. -/
@[dlmf 19.22.E2]
theorem symEllIntRG_zero_sq {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    2 * symEllIntRG 0 (x ^ 2) (y ^ 2) =
      4 * symEllIntRG 0 (x * y) (((x + y) / 2) ^ 2) - x * y * symEllIntRF 0 (x * y) (((x + y) / 2) ^ 2) := by
  have ha := ei19c_half_add_re_pos hx hy
  have hx2 := ei19c_sq_mem_slitPlane hx
  have hy2 := ei19c_sq_mem_slitPlane hy
  have hxy := ei19c_mul_mem_slitPlane hx hy
  have ha2 := ei19c_sq_mem_slitPlane ha
  have hF := symEllIntRF_zero_sq hx hy
  rw [p19sR1_symEllIntRG_zero_eq_carlsonRE hx2 hy2, p19sR1_symEllIntRG_zero_eq_carlsonRE hxy ha2,
    ← hF, p19sR1_symEllIntRF_zero_eq_carlsonRK hx2 hy2, Carlson.carlsonRE_sq_eq hx hy,
    p19sR1_carlsonRE_comm ha2 hxy]
  ring

/-- DLMF 19.22.3: `2y² R_D(0, x², y²) = (1/4)(y² - x²) R_D(0, xy, a²) + 3R_F(0, xy, a²)`. -/
@[dlmf 19.22.E3]
theorem symEllIntRD_zero_sq {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    2 * y ^ 2 * symEllIntRD 0 (x ^ 2) (y ^ 2) =
      (1 / 4) * (y ^ 2 - x ^ 2) * symEllIntRD 0 (x * y) (((x + y) / 2) ^ 2) +
        3 * symEllIntRF 0 (x * y) (((x + y) / 2) ^ 2) := by
  have ha := ei19c_half_add_re_pos hx hy
  have hx2 := ei19c_sq_mem_slitPlane hx
  have hy2 := ei19c_sq_mem_slitPlane hy
  have hxy := ei19c_mul_mem_slitPlane hx hy
  have ha2 := ei19c_sq_mem_slitPlane ha
  have F1 := symEllIntRF_zero_sq hx hy
  by_cases hne : x ^ 2 - y ^ 2 = 0
  · have hxy' : x = y := by
      have : (x - y) * (x + y) = 0 := by linear_combination hne
      rcases mul_eq_zero.mp this with h | h
      · exact sub_eq_zero.mp h
      · have := congrArg re h; simp at this; linarith
    subst hxy'
    have hc := symEllIntRF_zero_eq_symEllIntRD hx2 hx2
    rw [show (x + x) / 2 = x by ring, ← sq] at *
    rw [show x ^ 2 - x ^ 2 = 0 by ring]
    linear_combination -hc
  · have A1 := (symEllIntRG_zero_eq hx2 hy2).2
    have A2 := (symEllIntRG_zero_eq hxy ha2).2
    have L := symEllIntRG_zero_sq hx hy
    apply mul_left_cancel₀ hne
    linear_combination (-2 : ℂ) * A1 + 6 * L + 4 * A2 + (-6 * y ^ 2) * F1

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

/-- The AGM sequences `(aₙ, gₙ)` of DLMF §19.8(i) (Mathlib's `NNReal.agmSequences`, whose
index `n` holds `(gₙ₊₁, aₙ₊₁)`), with `a₀, g₀` themselves at index 0, and `cₙ² = aₙ² - gₙ²`.
Corrected 2026-10-25: index `n + 1` used `agmSequences (n + 1)`, i.e. `aₙ₊₂`, skipping `a₁`. -/
def agmA (a₀ g₀ : ℝ≥0) : ℕ → ℝ
  | 0 => a₀
  | n + 1 => ((NNReal.agmSequences a₀ g₀ n).2 : ℝ)

/-- The geometric-mean sequence `gₙ` (`g₀` at index 0). -/
def agmG (a₀ g₀ : ℝ≥0) : ℕ → ℝ
  | 0 => g₀
  | n + 1 => ((NNReal.agmSequences a₀ g₀ n).1 : ℝ)

lemma p19sR1_agmA_succ (a₀ g₀ : ℝ≥0) (n : ℕ) :
    agmA a₀ g₀ (n + 1) = (agmA a₀ g₀ n + agmG a₀ g₀ n) / 2 := by
  cases n with
  | zero => simp only [agmA, agmG, NNReal.agmSequences_zero]; push_cast; ring
  | succ k =>
    simp only [agmA, agmG]
    rw [NNReal.agmSequences_succ' (n := k)]
    push_cast; ring

lemma p19sR1_agmG_succ (a₀ g₀ : ℝ≥0) (n : ℕ) :
    agmG a₀ g₀ (n + 1) = Real.sqrt (agmA a₀ g₀ n * agmG a₀ g₀ n) := by
  cases n with
  | zero => simp only [agmA, agmG, NNReal.agmSequences_zero, Real.coe_sqrt, NNReal.coe_mul]
  | succ k =>
    simp only [agmA, agmG]
    rw [NNReal.agmSequences_succ' (n := k)]
    simp only [Real.coe_sqrt, NNReal.coe_mul, mul_comm]

/-- The DLMF AGM sequences agree with lean-codes' `Carlson.agmSeq`. -/
lemma p19sR1_agmSeq_eq (a₀ g₀ : ℝ≥0) (n : ℕ) :
    Carlson.agmSeq a₀ g₀ n = (agmA a₀ g₀ n, agmG a₀ g₀ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Carlson.agmSeq_succ, ih, p19sR1_agmA_succ, p19sR1_agmG_succ]
    rfl

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
  have ha : (0 : ℝ) < a₀ := lt_of_lt_of_le (by exact_mod_cast hg) (by exact_mod_cast hag)
  have hg' : (0 : ℝ) < g₀ := by exact_mod_cast hg
  set M : ℝ := (NNReal.agm a₀ g₀ : ℝ) with hM_def
  have hMpos : 0 < M := by
    have := NNReal.agm_pos (x := a₀) (y := g₀) (by exact_mod_cast ha) hg
    exact_mod_cast this
  have hM0 : (M : ℂ) ≠ 0 := ofReal_ne_zero.mpr hMpos.ne'
  have hK : Carlson.TwoVariable.carlsonRK (((a₀ : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) = (M : ℂ)⁻¹ :=
    Carlson.TwoVariable.carlsonRK_sq_eq_inv_agm (x := a₀) (y := g₀) (by exact_mod_cast ha) hg
  have hX : ∀ n, Carlson.agmX a₀ g₀ n = (agmA a₀ g₀ n : ℂ) := fun n => by
    simp [Carlson.agmX, p19sR1_agmSeq_eq]
  have hY : ∀ n, Carlson.agmY a₀ g₀ n = (agmG a₀ g₀ n : ℂ) := fun n => by
    simp [Carlson.agmY, p19sR1_agmSeq_eq]
  set RE := Carlson.carlsonRE (((a₀ : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) with hRE
  have hRG : (4 / π) * symEllIntRG 0 (((a₀ : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) = RE := by
    rw [p19sR1_symEllIntRG_zero_eq_carlsonRE (ei19c_sq_mem_slitPlane (by simpa using ha))
      (ei19c_sq_mem_slitPlane (by simpa using hg'))]
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [hRE]
    field_simp
  have hH := Carlson.hasSum_agmA_zero (x := a₀) (y := g₀) ha hg'
  have hA0 : Carlson.agmA a₀ g₀ 0 = 2 * (RE - ((a₀ : ℝ) : ℂ) ^ 2 * (M : ℂ)⁻¹) := by
    rw [← hK]
    simp [Carlson.agmA, Carlson.agmX, Carlson.agmY, Carlson.agmSeq_zero, RE]
  rw [hK, hA0] at hH
  have hS : HasSum (fun n : ℕ => (((2 : ℝ) ^ ((n : ℤ) - 1) *
      (agmA a₀ g₀ n ^ 2 - agmG a₀ g₀ n ^ 2) : ℝ) : ℂ)) (((a₀ : ℝ) : ℂ) ^ 2 - RE * M) := by
    convert hH.mul_left (-(M : ℂ) / 2) using 1
    · funext n
      rw [hX, hY, zpow_sub₀ two_ne_zero, zpow_natCast, zpow_one]
      push_cast
      field_simp
      ring
    · field_simp
      ring
  have hsumR : Summable (fun n : ℕ => (2 : ℝ) ^ ((n : ℤ) - 1) *
      (agmA a₀ g₀ n ^ 2 - agmG a₀ g₀ n ^ 2)) := Complex.summable_ofReal.mp hS.summable
  have hT : ((∑' n : ℕ, (2 : ℝ) ^ ((n : ℤ) - 1) * (agmA a₀ g₀ n ^ 2 - agmG a₀ g₀ n ^ 2) : ℝ) : ℂ)
      = ((a₀ : ℝ) : ℂ) ^ 2 - RE * M := by
    rw [Complex.ofReal_tsum]; exact hS.tsum_eq
  have h1 : (4 / π) * symEllIntRG 0 (((a₀ : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) =
      ((((NNReal.agm a₀ g₀ : ℝ))⁻¹ * ((a₀ : ℝ) ^ 2 -
        ∑' n : ℕ, (2 : ℝ) ^ ((n : ℤ) - 1) * (agmA a₀ g₀ n ^ 2 - agmG a₀ g₀ n ^ 2)) : ℝ) : ℂ) := by
    rw [hRG, ← hM_def, ofReal_mul, ofReal_sub, hT, ofReal_inv]
    push_cast
    field_simp
    ring
  refine ⟨h1, h1.trans ?_⟩
  congr 1
  congr 1
  rw [← hsumR.sum_add_tsum_nat_add 2]
  have hA1 := p19sR1_agmA_succ a₀ g₀ 0
  have hG1 := p19sR1_agmG_succ a₀ g₀ 0
  have hG1sq : agmG a₀ g₀ 1 ^ 2 = agmA a₀ g₀ 0 * agmG a₀ g₀ 0 := by
    rw [hG1, Real.sq_sqrt (by simp only [agmA, agmG]; positivity)]
  have htail : ∀ n : ℕ, (2 : ℝ) ^ (((n + 2 : ℕ) : ℤ) - 1) *
      (agmA a₀ g₀ (n + 2) ^ 2 - agmG a₀ g₀ (n + 2) ^ 2) =
      (2 : ℝ) ^ ((n : ℤ) + 1) * (agmA a₀ g₀ (n + 2) ^ 2 - agmG a₀ g₀ (n + 2) ^ 2) := by
    intro n; congr 2; push_cast; ring
  simp_rw [htail]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one]
  rw [hA1, hG1sq]
  simp only [agmA, agmG]
  norm_num
  ring

/-- DLMF 19.22.11: `Q₀ = 1`, `Qₙ₊₁ = (1/2) Qₙ (aₙ - gₙ)/(aₙ + gₙ)`. -/
def agmQ (a₀ g₀ : ℝ≥0) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (1 / 2) * agmQ a₀ g₀ n * (agmA a₀ g₀ n - agmG a₀ g₀ n) / (agmA a₀ g₀ n + agmG a₀ g₀ n)

/-- Helper for 19.22.9/19.22.10 (any `a₀, g₀ > 0`): `∑ₙ 2^{n-1} cₙ² = a₀² - (4/π) M R_G(0, a₀², g₀²)`. -/
lemma p19sR1_RG_agm_hasSum {a₀ g₀ : ℝ≥0} (ha₀ : 0 < a₀) (hg : 0 < g₀) :
    HasSum (fun n : ℕ => (((2 : ℝ) ^ ((n : ℤ) - 1) *
      (agmA a₀ g₀ n ^ 2 - agmG a₀ g₀ n ^ 2) : ℝ) : ℂ))
      (((a₀ : ℝ) : ℂ) ^ 2 - (4 / π) * symEllIntRG 0 (((a₀ : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) *
        (NNReal.agm a₀ g₀ : ℝ)) := by
  have ha : (0 : ℝ) < a₀ := by exact_mod_cast ha₀
  have hg' : (0 : ℝ) < g₀ := by exact_mod_cast hg
  set M : ℝ := (NNReal.agm a₀ g₀ : ℝ) with hM_def
  have hMpos : 0 < M := by
    have := NNReal.agm_pos (x := a₀) (y := g₀) ha₀ hg
    exact_mod_cast this
  have hK : Carlson.TwoVariable.carlsonRK (((a₀ : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) = (M : ℂ)⁻¹ :=
    Carlson.TwoVariable.carlsonRK_sq_eq_inv_agm (x := a₀) (y := g₀) ha₀ hg
  have hX : ∀ n, Carlson.agmX a₀ g₀ n = (agmA a₀ g₀ n : ℂ) := fun n => by
    simp [Carlson.agmX, p19sR1_agmSeq_eq]
  have hY : ∀ n, Carlson.agmY a₀ g₀ n = (agmG a₀ g₀ n : ℂ) := fun n => by
    simp [Carlson.agmY, p19sR1_agmSeq_eq]
  set RE := Carlson.carlsonRE (((a₀ : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) with hRE
  have hRG : (4 / π) * symEllIntRG 0 (((a₀ : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) = RE := by
    rw [p19sR1_symEllIntRG_zero_eq_carlsonRE (ei19c_sq_mem_slitPlane (by simpa using ha))
      (ei19c_sq_mem_slitPlane (by simpa using hg'))]
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [hRE]
    field_simp
  have hH := Carlson.hasSum_agmA_zero (x := a₀) (y := g₀) ha hg'
  have hA0 : Carlson.agmA a₀ g₀ 0 = 2 * (RE - ((a₀ : ℝ) : ℂ) ^ 2 * (M : ℂ)⁻¹) := by
    rw [← hK]
    simp [Carlson.agmA, Carlson.agmX, Carlson.agmY, Carlson.agmSeq_zero, RE]
  rw [hK, hA0] at hH
  rw [hRG]
  have hM0 : (M : ℂ) ≠ 0 := ofReal_ne_zero.mpr hMpos.ne'
  convert hH.mul_left (-(M : ℂ) / 2) using 1
  · funext n
    rw [hX, hY, zpow_sub₀ two_ne_zero, zpow_natCast, zpow_one]
    push_cast
    field_simp
    ring
  · field_simp
    ring

/-- Helper for 19.22.10: `Qₙ (a₀² - g₀²) = 2ⁿ cₙ²`. -/
lemma p19sR1_agmQ_mul {a₀ g₀ : ℝ≥0} (ha₀ : 0 < a₀) (hg : 0 < g₀) (n : ℕ) :
    agmQ a₀ g₀ n * ((a₀ : ℝ) ^ 2 - (g₀ : ℝ) ^ 2) =
      2 ^ n * (agmA a₀ g₀ n ^ 2 - agmG a₀ g₀ n ^ 2) := by
  have ha' : (0 : ℝ) < a₀ := ha₀
  have hg' : (0 : ℝ) < g₀ := hg
  have hnn : ∀ m, 0 ≤ agmA a₀ g₀ m ∧ 0 ≤ agmG a₀ g₀ m := fun m => by
    cases m <;> simp only [agmA, agmG] <;> exact ⟨NNReal.coe_nonneg _, NNReal.coe_nonneg _⟩
  have hpos : ∀ m, 0 < agmA a₀ g₀ m + agmG a₀ g₀ m := by
    intro m
    cases m with
    | zero => simp only [agmA, agmG]; linarith
    | succ m =>
      have h := p19sR1_agmA_succ a₀ g₀ m
      have hm := hnn m
      have hm' := hnn (m + 1)
      by_contra hc
      have h0 : agmA a₀ g₀ (m + 1) = 0 := by linarith
      rw [h0] at h
      -- then aₘ = gₘ = 0, impossible by induction from a₀ > 0
      have : ∀ k, 0 < agmA a₀ g₀ k + agmG a₀ g₀ k → 0 < agmA a₀ g₀ (k + 1) := fun k hk => by
        rw [p19sR1_agmA_succ]; linarith
      have hk : ∀ k, 0 < agmA a₀ g₀ k := by
        intro k
        induction k with
        | zero => simpa [agmA] using ha'
        | succ k ih => exact this k (by linarith [(hnn k).2])
      linarith [hk (m + 1)]
  induction n with
  | zero => simp [agmQ, agmA, agmG]
  | succ n ih =>
    have hA := p19sR1_agmA_succ a₀ g₀ n
    have hG : agmG a₀ g₀ (n + 1) ^ 2 = agmA a₀ g₀ n * agmG a₀ g₀ n := by
      rw [p19sR1_agmG_succ, Real.sq_sqrt (mul_nonneg (hnn n).1 (hnn n).2)]
    have hp := (hpos n).ne'
    rw [agmQ, hG, hA]
    field_simp
    linear_combination 2 * (agmA a₀ g₀ n - agmG a₀ g₀ n) * ih

/-- DLMF 19.22.10 with 19.22.11: `R_D(0, g₀², a₀²) = 3π/(4 M a₀²) ∑ Qₙ`, `a₀, g₀ > 0`
(here DLMF does not need `a₀ ≥ g₀`). -/
@[dlmf 19.22.E10, dlmf 19.22.E11]
theorem symEllIntRD_zero_agm {a₀ g₀ : ℝ≥0} (ha : 0 < a₀) (hg : 0 < g₀) :
    HasSum (fun n => ((3 * π / (4 * (NNReal.agm a₀ g₀ : ℝ) * (a₀ : ℝ) ^ 2) * agmQ a₀ g₀ n : ℝ) : ℂ))
      (symEllIntRD 0 (((g₀ : ℝ) : ℂ) ^ 2) (((a₀ : ℝ) : ℂ) ^ 2)) := by
  have ha' : (0 : ℝ) < a₀ := ha
  have hg' : (0 : ℝ) < g₀ := hg
  set M : ℝ := (NNReal.agm a₀ g₀ : ℝ) with hM_def
  have hMpos : 0 < M := by
    have := NNReal.agm_pos (x := a₀) (y := g₀) ha hg
    exact_mod_cast this
  have hy : (((g₀ : ℝ) : ℂ) ^ 2) ∈ slitPlane := ei19c_sq_mem_slitPlane (by simpa using hg')
  have hz : (((a₀ : ℝ) : ℂ) ^ 2) ∈ slitPlane := ei19c_sq_mem_slitPlane (by simpa using ha')
  by_cases hag : a₀ = g₀
  · subst hag
    have hM : M = a₀ := by rw [hM_def, NNReal.agm_self]
    have hQ : ∀ n, agmQ a₀ a₀ (n + 1) = 0 := by
      intro n
      induction n with
      | zero => simp [agmQ, agmA, agmG]
      | succ n ih => rw [agmQ, ih]; ring
    rw [symEllIntRD_zero_self hz]
    have hpow : (((a₀ : ℝ) : ℂ) ^ 2) ^ (-3 / 2 : ℂ) = (((a₀ : ℝ) ^ 3 : ℝ) : ℂ)⁻¹ := by
      rw [show (((a₀ : ℝ) : ℂ) ^ 2) = (((a₀ : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring,
        show (-3 / 2 : ℂ) = ((-3 / 2 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_cpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul ha'.le]
      rw [← ofReal_inv, ← Real.rpow_natCast, ← Real.rpow_neg ha'.le]
      norm_num
    rw [hpow]
    convert hasSum_ite_eq 0 ((3 * π / (4 * M * (a₀ : ℝ) ^ 2) : ℝ) : ℂ) using 1
    · funext n
      cases n with
      | zero => simp [agmQ]
      | succ n => simp [hQ n]
    · rw [hM]; push_cast; field_simp
  · have hc0 : (a₀ : ℝ) ^ 2 - (g₀ : ℝ) ^ 2 ≠ 0 := by
      intro h
      apply hag
      have : (a₀ : ℝ) = g₀ := by nlinarith [sq_nonneg ((a₀ : ℝ) - g₀), sq_nonneg ((a₀ : ℝ) + g₀)]
      exact_mod_cast this
    have H := (p19sR1_RG_agm_hasSum ha hg).mul_left
      (((3 * π / (4 * M * (a₀ : ℝ) ^ 2) * (2 / ((a₀ : ℝ) ^ 2 - (g₀ : ℝ) ^ 2)) : ℝ) : ℂ))
    convert H using 1
    · funext n
      have hq := p19sR1_agmQ_mul ha hg n
      have hq' : agmQ a₀ g₀ n = 2 * ((2 : ℝ) ^ ((n : ℤ) - 1) *
          (agmA a₀ g₀ n ^ 2 - agmG a₀ g₀ n ^ 2)) / ((a₀ : ℝ) ^ 2 - (g₀ : ℝ) ^ 2) := by
        rw [zpow_sub₀ two_ne_zero, zpow_natCast, zpow_one, eq_div_iff hc0, hq]
        ring
      rw [← ofReal_mul, hq']
      congr 1
      ring
    · have h2 := p19sR1_two_mul_symEllIntRG (x := 0) (Or.inr rfl) hy hz
      rw [zero_cpow (by norm_num), zero_mul, zero_mul, add_zero] at h2
      have hF := symEllIntRF_zero_eq_inv_agm ha hg
      have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      have hM0 : (M : ℂ) ≠ 0 := ofReal_ne_zero.mpr hMpos.ne'
      have hc0' : (((a₀ : ℝ) : ℂ) ^ 2 - ((g₀ : ℝ) : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hc0
      have ha0 : ((a₀ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha'.ne'
      have hFv : symEllIntRF 0 (((a₀ : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) = π / (2 * M) := by
        have h' := hF
        rw [div_mul_eq_mul_div, div_eq_iff hπ] at h'
        have hMinv : (M : ℂ) * (M : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hM0
        rw [eq_div_iff (mul_ne_zero two_ne_zero hM0)]
        linear_combination (M : ℂ) * h' + π * hMinv
      rw [symEllIntRF_comm_right, hFv, symEllIntRG_comm_right] at h2
      have hRD : symEllIntRD 0 (((g₀ : ℝ) : ℂ) ^ 2) (((a₀ : ℝ) : ℂ) ^ 2) =
          3 * (((a₀ : ℝ) : ℂ) ^ 2 * (π / (2 * M)) -
            2 * symEllIntRG 0 (((a₀ : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2)) /
          (((a₀ : ℝ) : ℂ) ^ 2 * (((a₀ : ℝ) : ℂ) ^ 2 - ((g₀ : ℝ) : ℂ) ^ 2)) := by
        rw [eq_div_iff (mul_ne_zero (pow_ne_zero 2 ha0) hc0')]
        linear_combination 3 * h2
      rw [hRD]
      push_cast
      field_simp
      ring

/-- DLMF 19.22.11 (last sentence): `Qₙ` has the sign of `a₀ - g₀` for `n ≥ 1`. -/
@[dlmf 19.22.E11]
theorem agmQ_sign {a₀ g₀ : ℝ≥0} (ha : 0 < a₀) (hg : 0 < g₀) (n : ℕ) :
    SignType.sign (agmQ a₀ g₀ (n + 1)) = SignType.sign ((a₀ : ℝ) - g₀) := by
  have ha' : (0 : ℝ) < a₀ := ha
  have hg' : (0 : ℝ) < g₀ := hg
  have hpos : ∀ n, 0 < agmA a₀ g₀ n + agmG a₀ g₀ n := by
    intro n
    cases n with
    | zero => simp only [agmA, agmG]; linarith
    | succ n =>
      simp only [agmA, agmG]
      have h0 : (0 : ℝ≥0) < (NNReal.agmSequences a₀ g₀ 0).1 := by
        rw [NNReal.agmSequences_zero]; exact NNReal.sqrt_pos.mpr (mul_pos ha hg)
      have h1 : (0 : ℝ≥0) < (NNReal.agmSequences a₀ g₀ n).1 :=
        lt_of_lt_of_le h0 (NNReal.agmSequences_fst_monotone (Nat.zero_le n))
      have h2 := NNReal.agmSequences_fst_le_snd (x := a₀) (y := g₀) n n
      have h1' : (0 : ℝ) < ((NNReal.agmSequences a₀ g₀ n).1 : ℝ) := by exact_mod_cast h1
      have h2' : ((NNReal.agmSequences a₀ g₀ n).1 : ℝ) ≤
          ((NNReal.agmSequences a₀ g₀ n).2 : ℝ) := by exact_mod_cast h2
      linarith
  have hrec : ∀ m, agmQ a₀ g₀ (m + 2) = agmQ a₀ g₀ (m + 1) *
      ((agmA a₀ g₀ (m + 1) - agmG a₀ g₀ (m + 1)) *
        (1 / (2 * (agmA a₀ g₀ (m + 1) + agmG a₀ g₀ (m + 1))))) := by
    intro m
    rw [agmQ]
    have := (hpos (m + 1)).ne'
    field_simp
  have hQ1 : agmQ a₀ g₀ 1 = ((a₀ : ℝ) - g₀) * (1 / (2 * ((a₀ : ℝ) + g₀))) := by
    simp only [agmQ, agmA, agmG]
    have : (a₀ : ℝ) + g₀ ≠ 0 := by linarith
    field_simp
  have hc : ∀ m, 0 < 1 / (2 * (agmA a₀ g₀ m + agmG a₀ g₀ m)) := fun m => by
    have := hpos m; positivity
  by_cases he : a₀ = g₀
  · subst he
    have h0 : ∀ m, agmQ a₀ a₀ (m + 1) = 0 := by
      intro m
      induction m with
      | zero => rw [hQ1]; simp
      | succ m ih => rw [hrec, ih, zero_mul]
    rw [h0]; simp
  · have hd : ∀ m, 0 < agmA a₀ g₀ (m + 1) - agmG a₀ g₀ (m + 1) := by
      intro m
      simp only [agmA, agmG]
      have h := NNReal.agmSequences_fst_lt_snd_of_ne he m m
      have h' : ((NNReal.agmSequences a₀ g₀ m).1 : ℝ) <
          ((NNReal.agmSequences a₀ g₀ m).2 : ℝ) := by exact_mod_cast h
      linarith
    induction n with
    | zero =>
      have hc0 : (0 : ℝ) < 1 / (2 * ((a₀ : ℝ) + g₀)) := by positivity
      rw [hQ1, sign_mul, sign_pos hc0, mul_one]
    | succ m ih =>
      rw [hrec, sign_mul, ih, sign_pos (mul_pos (hd m) (hc (m + 1))), mul_one]

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

/-- Helper for 19.22.13: the Heron-type iteration `pₙ₊₁ = (pₙ² + aₙgₙ)/(2pₙ)` along a genuine
AGM pair `(aₙ, gₙ)` converges to the common limit, via
`pₙ₊₁² - aₙ₊₁² = (pₙ² - aₙ²)(pₙ² - gₙ²)/(4pₙ²)`. -/
lemma p19sR1_tendsto_heron {a g p : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hg : ∀ n, 0 < g n)
    (hga : ∀ n, g n ≤ a n)
    (ha : ∀ n, a (n + 1) = (a n + g n) / 2) (hgs : ∀ n, g (n + 1) ^ 2 = a n * g n)
    (hp0 : 0 < p 0) (hp : ∀ n, p (n + 1) = (p n ^ 2 + a n * g n) / (2 * p n))
    (haM : Tendsto a atTop (𝓝 M)) : Tendsto p atTop (𝓝 M) := by
  have hpos : ∀ n, 0 < p n := by
    intro n
    induction n with
    | zero => exact hp0
    | succ n ih =>
      rw [hp]
      have hn := hg n
      have han : 0 < a n := hn.trans_le (hga n)
      positivity
  have he : ∀ n, p (n + 1) ^ 2 - a (n + 1) ^ 2 =
      (p n ^ 2 - a n ^ 2) * ((p n ^ 2 - g n ^ 2) / (4 * p n ^ 2)) := by
    intro n
    rw [hp, ha]
    have := (hpos n).ne'
    field_simp
    ring
  have hpg : ∀ n, g (n + 1) ^ 2 ≤ p (n + 1) ^ 2 := by
    intro n
    have h : p (n + 1) ^ 2 - g (n + 1) ^ 2 = (p n ^ 2 - a n * g n) ^ 2 / (4 * p n ^ 2) := by
      rw [hp, hgs]
      have := (hpos n).ne'
      field_simp
      ring
    have : 0 ≤ (p n ^ 2 - a n * g n) ^ 2 / (4 * p n ^ 2) := by positivity
    linarith
  have hr : ∀ n, |p (n + 2) ^ 2 - a (n + 2) ^ 2| ≤ |p (n + 1) ^ 2 - a (n + 1) ^ 2| / 4 := by
    intro n
    rw [he (n + 1), abs_mul]
    have hp2 : 0 < p (n + 1) ^ 2 := by have := hpos (n + 1); positivity
    have h0 : 0 ≤ (p (n + 1) ^ 2 - g (n + 1) ^ 2) / (4 * p (n + 1) ^ 2) :=
      div_nonneg (by linarith [hpg n]) (by positivity)
    have h1 : (p (n + 1) ^ 2 - g (n + 1) ^ 2) / (4 * p (n + 1) ^ 2) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (g (n + 1))]
    rw [abs_of_nonneg h0]
    have := abs_nonneg (p (n + 1) ^ 2 - a (n + 1) ^ 2)
    nlinarith
  have hgeom : ∀ n, |p (n + 1) ^ 2 - a (n + 1) ^ 2| ≤
      |p 1 ^ 2 - a 1 ^ 2| * (1 / 4 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc |p (n + 1 + 1) ^ 2 - a (n + 1 + 1) ^ 2| ≤ |p (n + 1) ^ 2 - a (n + 1) ^ 2| / 4 := hr n
        _ ≤ (|p 1 ^ 2 - a 1 ^ 2| * (1 / 4 : ℝ) ^ n) / 4 := by gcongr
        _ = _ := by ring
  have he0 : Tendsto (fun n => p (n + 1) ^ 2 - a (n + 1) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n => |p 1 ^ 2 - a 1 ^ 2| * (1 / 4 : ℝ) ^ n)
      (fun n => ?_) ?_
    · exact (Real.norm_eq_abs _).le.trans (hgeom n)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num)).const_mul |p 1 ^ 2 - a 1 ^ 2|
  have ha1 : Tendsto (fun n => a (n + 1)) atTop (𝓝 M) :=
    haM.comp (tendsto_add_atTop_nat 1)
  have hsq : Tendsto (fun n => p (n + 1) ^ 2) atTop (𝓝 (M ^ 2)) := by
    have := he0.add (ha1.pow 2)
    simpa using this
  have hsqrt := (Real.continuous_sqrt.tendsto _).comp hsq
  rw [Real.sqrt_sq hM] at hsqrt
  rw [← tendsto_add_atTop_iff_nat 1]
  refine hsqrt.congr fun n => ?_
  simp only [Function.comp_apply]
  exact Real.sqrt_sq (hpos (n + 1)).le

/-- DLMF 19.22.13 (convergence statement): `pₙ → M(a₀, g₀)` and `εₙ → 0` (quadratically). -/
@[dlmf 19.22.E13]
theorem tendsto_agmP {a₀ g₀ : ℝ≥0} (ha : 0 < a₀) (hg : 0 < g₀) {p₀ : ℝ} (hp : 0 < p₀) :
    Tendsto (agmP a₀ g₀ p₀) atTop (𝓝 (NNReal.agm a₀ g₀ : ℝ)) := by
  have hA : ∀ n, agmA a₀ g₀ (n + 2) = (agmA a₀ g₀ (n + 1) + agmG a₀ g₀ (n + 1)) / 2 := by
    intro n
    simp only [agmA, agmG]
    rw [NNReal.agmSequences_succ' (n := n)]
    push_cast; ring
  have hG : ∀ n, agmG a₀ g₀ (n + 2) ^ 2 = agmA a₀ g₀ (n + 1) * agmG a₀ g₀ (n + 1) := by
    intro n
    simp only [agmA, agmG]
    rw [NNReal.agmSequences_succ' (n := n)]
    rw [← NNReal.coe_pow, NNReal.sq_sqrt]
    push_cast
    ring
  have hG0 : ∀ n, 0 < agmG a₀ g₀ (n + 1) := by
    intro n
    simp only [agmG]
    have h0 : (0 : ℝ≥0) < (NNReal.agmSequences a₀ g₀ 0).1 := by
      rw [NNReal.agmSequences_zero]; exact NNReal.sqrt_pos.mpr (mul_pos ha hg)
    have h1 : (0 : ℝ≥0) < (NNReal.agmSequences a₀ g₀ n).1 :=
      lt_of_lt_of_le h0 (NNReal.agmSequences_fst_monotone (Nat.zero_le n))
    exact_mod_cast h1
  have hGA : ∀ n, agmG a₀ g₀ (n + 1) ≤ agmA a₀ g₀ (n + 1) := by
    intro n
    simp only [agmA, agmG]
    exact_mod_cast NNReal.agmSequences_fst_le_snd n n
  have hP1 : 0 < agmP a₀ g₀ p₀ 1 := by
    simp only [agmP, agmA, agmG]
    have : (0 : ℝ) < a₀ := ha
    have : (0 : ℝ) < g₀ := hg
    positivity
  have hlim : Tendsto (fun n => agmA a₀ g₀ (n + 1)) atTop (𝓝 (NNReal.agm a₀ g₀ : ℝ)) := by
    have := NNReal.tendsto_coe.mpr (NNReal.tendsto_agmSequences_snd_agm (x := a₀) (y := g₀))
    refine this.congr fun n => ?_
    simp [agmA]
  rw [← tendsto_add_atTop_iff_nat 1]
  exact p19sR1_tendsto_heron (a := fun n => agmA a₀ g₀ (n + 1)) (g := fun n => agmG a₀ g₀ (n + 1))
    (NNReal.coe_nonneg _) hG0 hGA hA hG hP1 (fun n => rfl) hlim

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
  have h := Carlson.carlsonRF_landen_conj hx hy hz hxz hzy
  have hpos : ∀ {w : ℝ}, 0 < w → ((w ^ 2 : ℝ) : ℂ) ∈ slitPlane := fun hw =>
    ofReal_mem_slitPlane.mpr (by positivity)
  have ha : 0 < Real.sqrt ((z + x) * (z + y)) := Real.sqrt_pos.mpr (by positivity)
  have h1 : (((Real.sqrt ((z + x) * (z + y)) : ℂ) + I * Real.sqrt ((z - x) * (y - z))) / 2) ^ 2
      ∈ slitPlane := ei19c_sq_mem_slitPlane (by simp; positivity)
  have h2 : (((Real.sqrt ((z + x) * (z + y)) : ℂ) - I * Real.sqrt ((z - x) * (y - z))) / 2) ^ 2
      ∈ slitPlane := ei19c_sq_mem_slitPlane (by simp; positivity)
  rw [symEllIntRF_eq_carlsonRF (hpos hx) (hpos hy) (hpos hz), h,
    symEllIntRF_eq_carlsonRF (hpos (by positivity)) h1 h2]

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
