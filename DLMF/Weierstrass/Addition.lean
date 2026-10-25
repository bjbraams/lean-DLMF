/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Addition, duplication, `n`-tuple formulas and homogeneity (DLMF §23.10)

Derivatives of `ζ` and `℘'` are Lean derivatives. Each identity is stated where its
denominators are defined (points off the lattice, distinct values of `℘`).

**Source corrections in §23.10(iii).** DLMF 23.10.14 prints the product over
`ℓ ≠ j`; the correct index set (the nonzero `n`-division points) is `(j, ℓ) ≠ (0, 0)`. With
the printed index set 23.10.13 fails numerically (e.g. a relative error `0.71` for `n = 2`,
`ω₁ = 1.1 + 0.2i`, `ω₃ = 0.3 + 0.9i`), with the corrected one it holds to `10⁻⁹`. In 23.10.15
the factor `(π²G²/ω₁)^{n²-1}` must be `(πG²/ω₁)^{n²-1}`: the printed value differs from the
corrected 23.10.14 by exactly `π^{n²-1}` (checked for `n = 2, 3, 4` and three lattices).
Both corrected forms are acquired.
-/

@[expose] public section

open Complex PeriodPair
open scoped Real

noncomputable section

namespace DLMF.Weierstrass

/-! ### Addition theorems (§23.10(i)) -/

/-- DLMF 23.10.1: `℘(u + v) = ¼((℘'(u) - ℘'(v))/(℘(u) - ℘(v)))² - ℘(u) - ℘(v)` for
`u, v, u ± v ∉ 𝕃`. -/
@[dlmf 23.10.E1]
theorem weierstrassP_add (L : PeriodPair) {u v : ℂ} (hu : u ∉ L.lattice) (hv : v ∉ L.lattice)
    (huv : u + v ∉ L.lattice) (huv' : u - v ∉ L.lattice) :
    ℘[L] (u + v) = 1 / 4 * ((℘'[L] u - ℘'[L] v) / (℘[L] u - ℘[L] v)) ^ 2 - ℘[L] u - ℘[L] v := by
  sorry

/-- DLMF 23.10.2: `ζ(u + v) = ζ(u) + ζ(v) + ½(ζ''(u) - ζ''(v))/(ζ'(u) - ζ'(v))` for
`u, v, u ± v ∉ 𝕃`. -/
@[dlmf 23.10.E2]
theorem weierstrassZeta_add (L : PeriodPair) {u v : ℂ} (hu : u ∉ L.lattice) (hv : v ∉ L.lattice)
    (huv : u + v ∉ L.lattice) (huv' : u - v ∉ L.lattice) :
    weierstrassZeta L (u + v) = weierstrassZeta L u + weierstrassZeta L v +
      1 / 2 * ((deriv (deriv (weierstrassZeta L)) u - deriv (deriv (weierstrassZeta L)) v) /
        (deriv (weierstrassZeta L) u - deriv (weierstrassZeta L) v)) := by
  sorry

/-- DLMF 23.10.3: `σ(u + v)σ(u - v)/(σ²(u)σ²(v)) = ℘(v) - ℘(u)` for `u, v ∉ 𝕃`. -/
@[dlmf 23.10.E3]
theorem weierstrassSigma_add_mul_sub (L : PeriodPair) {u v : ℂ} (hu : u ∉ L.lattice)
    (hv : v ∉ L.lattice) :
    weierstrassSigma L (u + v) * weierstrassSigma L (u - v) /
        (weierstrassSigma L u ^ 2 * weierstrassSigma L v ^ 2) = ℘[L] v - ℘[L] u := by
  sorry

/-- DLMF 23.10.4: the three-term identity
`σ(u+v)σ(u-v)σ(x+y)σ(x-y) + σ(v+x)σ(v-x)σ(u+y)σ(u-y) + σ(x+u)σ(x-u)σ(v+y)σ(v-y) = 0`. -/
@[dlmf 23.10.E4]
theorem weierstrassSigma_three_term (L : PeriodPair) (u v x y : ℂ) :
    weierstrassSigma L (u + v) * weierstrassSigma L (u - v) * weierstrassSigma L (x + y) *
          weierstrassSigma L (x - y) +
        weierstrassSigma L (v + x) * weierstrassSigma L (v - x) * weierstrassSigma L (u + y) *
          weierstrassSigma L (u - y) +
        weierstrassSigma L (x + u) * weierstrassSigma L (x - u) * weierstrassSigma L (v + y) *
          weierstrassSigma L (v - y) = 0 := by
  sorry

/-- DLMF 23.10.5: if `u + v + w = 0` (`u, v, w ∉ 𝕃`), then
`det [[1, ℘(u), ℘'(u)], [1, ℘(v), ℘'(v)], [1, ℘(w), ℘'(w)]] = 0`. -/
@[dlmf 23.10.E5]
theorem weierstrassP_det_eq_zero (L : PeriodPair) {u v w : ℂ} (hu : u ∉ L.lattice)
    (hv : v ∉ L.lattice) (hw : w ∉ L.lattice) (h : u + v + w = 0) :
    Matrix.det !![1, ℘[L] u, ℘'[L] u; 1, ℘[L] v, ℘'[L] v; 1, ℘[L] w, ℘'[L] w] = 0 := by
  sorry

/-- DLMF 23.10.6: if `u + v + w = 0` (`u, v, w ∉ 𝕃`), then
`(ζ(u) + ζ(v) + ζ(w))² + ζ'(u) + ζ'(v) + ζ'(w) = 0`. -/
@[dlmf 23.10.E6]
theorem weierstrassZeta_sum_sq (L : PeriodPair) {u v w : ℂ} (hu : u ∉ L.lattice)
    (hv : v ∉ L.lattice) (hw : w ∉ L.lattice) (h : u + v + w = 0) :
    (weierstrassZeta L u + weierstrassZeta L v + weierstrassZeta L w) ^ 2 +
      deriv (weierstrassZeta L) u + deriv (weierstrassZeta L) v +
        deriv (weierstrassZeta L) w = 0 := by
  sorry

/-! ### Duplication formulas (§23.10(ii)) -/

/-- DLMF 23.10.7: `℘(2z) = -2℘(z) + ¼(℘''(z)/℘'(z))²` for `z, 2z ∉ 𝕃`. -/
@[dlmf 23.10.E7]
theorem weierstrassP_two_mul (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice)
    (h2z : 2 * z ∉ L.lattice) :
    ℘[L] (2 * z) = -2 * ℘[L] z + 1 / 4 * (deriv ℘'[L] z / ℘'[L] z) ^ 2 := by
  sorry

namespace HalfPeriods

variable (H : HalfPeriods)

/-- DLMF 23.10.8 and its cyclic permutations: for `z, 2z ∉ 𝕃`,
`(℘(2z) - e₁)℘'²(z) = ((℘(z) - e₁)² - (e₁ - e₂)(e₁ - e₃))²`, and likewise with
`(e₁, e₂, e₃)` permuted cyclically. -/
@[dlmf 23.10.E8]
theorem weierstrassP_two_mul_sub_e {z : ℂ} (hz : z ∉ H.lattice) (h2z : 2 * z ∉ H.lattice) :
    (H.weierstrassP (2 * z) - H.e 1) * H.derivWeierstrassP z ^ 2 =
        ((H.weierstrassP z - H.e 1) ^ 2 - (H.e 1 - H.e 2) * (H.e 1 - H.e 3)) ^ 2 ∧
      (H.weierstrassP (2 * z) - H.e 2) * H.derivWeierstrassP z ^ 2 =
        ((H.weierstrassP z - H.e 2) ^ 2 - (H.e 2 - H.e 3) * (H.e 2 - H.e 1)) ^ 2 ∧
      (H.weierstrassP (2 * z) - H.e 3) * H.derivWeierstrassP z ^ 2 =
        ((H.weierstrassP z - H.e 3) ^ 2 - (H.e 3 - H.e 1) * (H.e 3 - H.e 2)) ^ 2 := by
  sorry

end HalfPeriods

/-- DLMF 23.10.9: `ζ(2z) = 2ζ(z) + ½ζ'''(z)/ζ''(z)` for `z, 2z ∉ 𝕃`. -/
@[dlmf 23.10.E9]
theorem weierstrassZeta_two_mul (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice)
    (h2z : 2 * z ∉ L.lattice) :
    weierstrassZeta L (2 * z) = 2 * weierstrassZeta L z +
      1 / 2 * (deriv (deriv (deriv (weierstrassZeta L))) z /
        deriv (deriv (weierstrassZeta L)) z) := by
  sorry

/-- DLMF 23.10.10: `σ(2z) = -℘'(z)σ⁴(z)` for `z ∈ ℂ` (both sides vanish on `𝕃`). -/
@[dlmf 23.10.E10]
theorem weierstrassSigma_two_mul (L : PeriodPair) (z : ℂ) :
    weierstrassSigma L (2 * z) = -℘'[L] z * weierstrassSigma L z ^ 4 := by
  sorry

/-! ### `n`-tuple formulas (§23.10(iii)) -/

namespace HalfPeriods

variable (H : HalfPeriods)

/-- The `n²` shifts `2jω₁/n + 2ℓω₃/n`, `0 ≤ j, ℓ < n`. -/
def divisionPoint (n j l : ℕ) : ℂ := 2 * j / n * H.ω₁ + 2 * l / n * H.ω₃

/-- DLMF 23.10.11: `n²℘(nz) = ∑_{j,ℓ=0}^{n-1} ℘(z + 2jω₁/n + 2ℓω₃/n)`, `n ≥ 2`, `nz ∉ 𝕃`. -/
@[dlmf 23.10.E11]
theorem weierstrassP_nsmul {n : ℕ} (hn : 2 ≤ n) {z : ℂ} (hz : (n : ℂ) * z ∉ H.lattice) :
    (n : ℂ) ^ 2 * H.weierstrassP (n * z) =
      ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n, H.weierstrassP (z + H.divisionPoint n j l) := by
  sorry

/-- DLMF 23.10.12: `nζ(nz) = -n(n-1)(η₁ + η₃) + ∑_{j,ℓ=0}^{n-1} ζ(z + 2jω₁/n + 2ℓω₃/n)`,
`n ≥ 2`, `nz ∉ 𝕃`. -/
@[dlmf 23.10.E12]
theorem weierstrassZeta_nsmul {n : ℕ} (hn : 2 ≤ n) {z : ℂ} (hz : (n : ℂ) * z ∉ H.lattice) :
    (n : ℂ) * H.weierstrassZeta (n * z) = -(n * (n - 1)) * (H.eta 1 + H.eta 3) +
      ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n,
        H.weierstrassZeta (z + H.divisionPoint n j l) := by
  sorry

/-- The constant `A_n` of 23.10.13, by the **corrected** DLMF 23.10.14:
`A_n = n ∏_{(j,ℓ) ≠ (0,0)} 1/σ((2jω₁ + 2ℓω₃)/n)`, `0 ≤ j, ℓ < n`.
Corrected from the printed DLMF formula: the printed index set `ℓ ≠ j` is wrong (relative error
0.71 at `n = 2`); the product runs over `(j, ℓ) ≠ (0, 0)`, excluding only the zero of `σ`. -/
@[dlmf 23.10.E14]
def nTupleConst (n : ℕ) : ℂ :=
  n * ∏ p ∈ (Finset.range n ×ˢ Finset.range n).erase (0, 0),
    1 / H.weierstrassSigma (H.divisionPoint n p.1 p.2)

/-- DLMF 23.10.13: `σ(nz) = A_n e^{-n(n-1)(η₁+η₃)z} ∏_{j,ℓ=0}^{n-1} σ(z + 2jω₁/n + 2ℓω₃/n)`,
`n ≥ 2`, `z ∈ ℂ`, with `A_n` as in the corrected 23.10.14. -/
@[dlmf 23.10.E13]
theorem weierstrassSigma_nsmul {n : ℕ} (hn : 2 ≤ n) (z : ℂ) :
    H.weierstrassSigma (n * z) = H.nTupleConst n * cexp (-(n * (n - 1)) * (H.eta 1 + H.eta 3) * z) *
      ∏ j ∈ Finset.range n, ∏ l ∈ Finset.range n,
        H.weierstrassSigma (z + H.divisionPoint n j l) := by
  sorry

/-- `G = ∏_{n≥1} (1 - q^{2n})`, `q = e^{πiω₃/ω₁}` (DLMF 23.10.16). -/
@[dlmf 23.10.E16]
def nTupleG : ℂ := ∏' n : ℕ, (1 - H.nome ^ (2 * (n + 1)))

/-- DLMF 23.10.15, **corrected** (`π` in place of the printed `π²`):
`A_n = (πG²/ω₁)^{n²-1} q^{n(n-1)/2} i^{-(n-1)}
exp(-((n-1)η₁/(3ω₁))((2n-1)(ω₁² + ω₃²) + 3(n-1)ω₁ω₃))`, `n ≥ 2`.
Corrected from the printed DLMF formula: the printed `π²` should be `π`; with `π` the ratio of
the two sides is exactly 1, with `π²` it is `π^{-(n²-1)}` (n = 2, 3, 4, three lattices). -/
@[dlmf 23.10.E15]
theorem nTupleConst_eq {n : ℕ} (hn : 2 ≤ n) :
    H.nTupleConst n = (π * H.nTupleG ^ 2 / H.ω₁) ^ (n ^ 2 - 1) *
      H.nome ^ (n * (n - 1) / 2) / I ^ (n - 1) *
      cexp (-((n - 1 : ℂ) * H.eta 1 / (3 * H.ω₁)) *
        ((2 * n - 1) * (H.ω₁ ^ 2 + H.ω₃ ^ 2) + 3 * (n - 1) * H.ω₁ * H.ω₃)) := by
  sorry

end HalfPeriods

/-! ### Homogeneity (§23.10(iv)) -/

/-- The period pair `c𝕃` with periods `cω₁, cω₂` (`c ≠ 0`). -/
def scalePeriodPair (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) : PeriodPair :=
  ⟨c * L.ω₁, c * L.ω₂, by
    refine LinearIndependent.pair_iff.mpr fun s t h => ?_
    refine LinearIndependent.pair_iff.mp L.indep s t ?_
    have : c * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← h]; simp only [Complex.real_smul]; ring
    simpa [hc] using this⟩

theorem wp23_mem_scale_iff (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) {z : ℂ} :
    z ∈ (scalePeriodPair c hc L).lattice ↔ z / c ∈ L.lattice := by
  simp only [PeriodPair.mem_lattice, scalePeriodPair]
  constructor
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by field_simp⟩
  · rintro ⟨m, n, h⟩; exact ⟨m, n, by rw [← mul_div_cancel₀ z hc, ← h]; ring⟩

/-- Multiplication by `c` as a bijection `𝕃 ≃ c𝕃`. -/
def wp23_scaleEquiv (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) :
    L.lattice ≃ (scalePeriodPair c hc L).lattice where
  toFun l := ⟨c * l, (wp23_mem_scale_iff c hc L).mpr (by simp [hc])⟩
  invFun l := ⟨l / c, (wp23_mem_scale_iff c hc L).mp l.2⟩
  left_inv l := by ext; simp [hc]
  right_inv l := by ext; simp [mul_div_cancel₀ _ hc]

/-- DLMF 23.10.17: `℘(cz|c𝕃) = c⁻²℘(z|𝕃)`. -/
@[dlmf 23.10.E17]
theorem weierstrassP_scale (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) (z : ℂ) :
    ℘[scalePeriodPair c hc L] (c * z) = c⁻¹ ^ 2 * ℘[L] z := by
  simp only [PeriodPair.weierstrassP]
  rw [← (wp23_scaleEquiv c hc L).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  simp only [wp23_scaleEquiv, Equiv.coe_fn_mk]
  rw [← mul_sub, mul_pow, mul_pow]
  simp only [one_div, mul_inv, inv_pow]
  ring

/-- DLMF 23.10.18: `ζ(cz|c𝕃) = c⁻¹ζ(z|𝕃)`. -/
@[dlmf 23.10.E18]
theorem weierstrassZeta_scale (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) (z : ℂ) :
    weierstrassZeta (scalePeriodPair c hc L) (c * z) = c⁻¹ * weierstrassZeta L z := by
  simp only [weierstrassZeta]
  rw [← (wp23_scaleEquiv c hc L).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  simp only [wp23_scaleEquiv, Equiv.coe_fn_mk]
  rw [← mul_sub, mul_pow]
  simp only [mul_inv, div_eq_mul_inv]
  field_simp

/-- DLMF 23.10.19: `σ(cz|c𝕃) = cσ(z|𝕃)`. -/
@[dlmf 23.10.E19]
theorem weierstrassSigma_scale (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) (z : ℂ) :
    weierstrassSigma (scalePeriodPair c hc L) (c * z) = c * weierstrassSigma L z := by
  simp only [weierstrassSigma]
  rw [← (wp23_scaleEquiv c hc L).tprod_eq, mul_assoc]
  congr 2
  refine tprod_congr fun l => ?_
  simp only [wp23_scaleEquiv, Equiv.coe_fn_mk]
  rw [mul_div_mul_left _ _ hc, mul_pow, mul_pow,
    show c ^ 2 * z ^ 2 / (2 * (c ^ 2 * (l : ℂ) ^ 2)) = z ^ 2 / (2 * (l : ℂ) ^ 2) by
      rw [mul_left_comm 2, mul_div_mul_left _ _ (pow_ne_zero 2 hc)]]

/-- `G_k(c𝕃) = c^{-k}G_k(𝕃)`. -/
theorem wp23_G_scale (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) (k : ℕ) :
    (scalePeriodPair c hc L).G k = c⁻¹ ^ k * L.G k := by
  simp only [PeriodPair.G]
  rw [← (wp23_scaleEquiv c hc L).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  simp only [wp23_scaleEquiv, Equiv.coe_fn_mk]
  rw [mul_pow, mul_inv, inv_pow]

/-- DLMF §23.10(iv): replacing `𝕃` by `c𝕃` divides `g₂` by `c⁴` and `g₃` by `c⁶`. -/
@[dlmf 23.10.iv]
theorem invariants_scale (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) :
    (scalePeriodPair c hc L).g₂ = L.g₂ / c ^ 4 ∧ (scalePeriodPair c hc L).g₃ = L.g₃ / c ^ 6 := by
  simp only [PeriodPair.g₂, PeriodPair.g₃, wp23_G_scale]
  constructor <;> field_simp

end DLMF.Weierstrass
