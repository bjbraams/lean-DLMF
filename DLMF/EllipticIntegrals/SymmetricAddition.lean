/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.Addition
public import Carlson.Elliptic.Applications
public import Carlson.R.SlitDeriv
public import DLMF.EllipticIntegrals.SymmetricNodeDerivatives
public import Carlson.Elliptic.ZeroVariable
public import Carlson.TwoVariable.QuadraticHybrid
public import Carlson.TwoVariable.R.ElementaryValues
public import Carlson.TwoVariable.Reduction
public import DLMF.EllipticIntegrals.Symmetric

/-!
# Addition theorems for the symmetric elliptic integrals (DLMF §19.26)

* §19.26(i): the addition theorems (19.26.1), (19.26.7), (19.26.8), (19.26.9) for `R_F`, `R_D`,
  `R_G`, `R_J`, with Euler's algebraic relation between `λ` and `μ` in the forms (19.26.2),
  (19.26.3), (19.26.5), (19.26.6); the addition theorem (19.26.11)–(19.26.12) of `R_C` and its
  equivalent forms (19.26.13)–(19.26.15). DLMF's standing assumption (19.26.i.p1): `λ, x, y, z`
  are positive, except that at most one of `x, y, z` can be `0` (`Ei19dPosDomain`).
* §19.26(ii): the case `x = 0`, where `λμ = yz` (19.26.ii.p1), (19.26.16), (19.26.17).
* §19.26(iii): the duplication formulas (19.26.18)–(19.26.27), with
  `λ = √x√y + √y√z + √z√x` (19.26.19, `symEllIntDupLambda`).

Proved here from `lean-codes`: the duplication theorem (19.26.18) on the whole slit plane
(**stronger than DLMF**; `Carlson.carlsonRF_duplication`) and at one zero variable
(`Carlson.carlsonRK_duplication`), the boundary case `x = 0` of (19.26.26) using
`Carlson.TwoVariable.pi_eq_four_mul_carlsonRC`, the addition theorem with `x = 0` (19.26.16;
`Carlson.carlsonRF_add_carlsonRF_zero`), and the algebraic identities (19.26.2) (permuted forms),
(19.26.4) (the note), (19.26.5), (19.26.12), (19.26.23) and (19.26.24).
The `R_D` duplication formula (19.26.20) follows by differentiating `R_F` duplication,
including the zero-variable boundary. The `R_G` duplication formula (19.26.21) then follows
from the connection between `R_G`, `R_F` and `R_D` and real square-root identities.
The same differentiation argument proves `R_D` addition (19.26.7); its `R_G` counterpart
(19.26.8) follows from the connection formula and the algebraic addition relations.

**Corrections of DLMF's hypotheses** (numerical evidence with mpmath, see the ledger):
* (19.26.13) needs `α, β > 0`: DLMF's conditions `0 < γ² - θ < γ²` for `γ = α, β, σ` do not fix
  the signs, and e.g. `α = -2, β = 3, θ = 3/2` satisfies them while the identity fails (the left
  side depends on `α², β²` only).
* (19.26.27) needs `ℜ x > 0` (as in (19.26.26)); `θ ≠ x², s²` does not suffice: it fails for
  `x = -2, θ = -3`.
* (19.26.14) divides by `x`; we assume `x > 0` (DLMF writes `x ≥ 0`).
* (19.26.9) is stated for `p > 0` (DLMF's standing positivity assumption); it fails for `p < 0`
  with the principal value.

## References

* NIST DLMF §19.26.
* B. C. Carlson, *Special Functions of Applied Mathematics*, 1977, §§9.6–9.7; formalized in
  `lean-codes` (`Carlson.Elliptic.Addition`, `Carlson.Elliptic.ZeroVariable`).
* D. G. Zill and B. C. Carlson, *Symmetric elliptic integrals of the third kind*, Math. Comp. 24
  (1970), §8.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-- DLMF 19.26.i.p1: the standing assumption of §19.26: `x, y, z ≥ 0`, at most one of them `0`
(and `λ > 0`, assumed separately). -/
def Ei19dPosDomain (x y z : ℝ) : Prop :=
  0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ (x = 0 → 0 < y ∧ 0 < z) ∧ (y = 0 → 0 < z)

/-! ### §19.26(i) General formulas -/

/-- Identity under the stated parameter and domain assumptions: `√(a * b * c) = √a * √b * √c`. -/
lemma ei19d_sqrt_mul3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (_hc : 0 ≤ c) :
    √(a * b * c) = √a * √b * √c := by
  rw [Real.sqrt_mul (mul_nonneg ha hb), Real.sqrt_mul ha]

/-- Identity under the stated parameter and domain assumptions: `(b ^ 2 + m) * l ^ 2 = (B * a * c
+ b * A * C) ^ 2 ∧ (c ^ 2 + m) * l ^ 2 = (C * a * b + c * A * B) ^ 2`. -/
lemma ei19d_perm_alg {a b c A B C l m : ℝ} (hA : A ^ 2 = a ^ 2 + l) (hB : B ^ 2 = b ^ 2 + l)
    (hC : C ^ 2 = c ^ 2 + l) (h : (a ^ 2 + m) * l ^ 2 = (A * b * c + a * B * C) ^ 2) :
    (b ^ 2 + m) * l ^ 2 = (B * a * c + b * A * C) ^ 2 ∧
      (c ^ 2 + m) * l ^ 2 = (C * a * b + c * A * B) ^ 2 := by
  constructor
  · linear_combination h + (b ^ 2 * (c - C) * (C + c)) * hA - (a ^ 2 * (c - C) * (C + c)) * hB +
      (l * (a - b) * (a + b)) * hC
  · linear_combination h + (c ^ 2 * (b - B) * (B + b)) * hA +
      (C ^ 2 * a ^ 2 - a ^ 2 * c ^ 2 - c ^ 2 * l) * hB + (a ^ 2 * l) * hC

/-- DLMF 19.26.2 ("corresponding equations for `y + μ` and `z + μ` obtained by permuting
`x, y, z`"): under the standing assumptions, the `x`-form of (19.26.2) implies the `y`- and
`z`-forms. -/
@[dlmf 19.26.E2]
theorem symEllInt_addition_mu_perm {x y z l m : ℝ} (h : Ei19dPosDomain x y z) (hl : 0 < l)
    (hμ : x + m = (√((x + l) * y * z) + √(x * (y + l) * (z + l))) ^ 2 / l ^ 2) :
    y + m = (√((y + l) * x * z) + √(y * (x + l) * (z + l))) ^ 2 / l ^ 2 ∧
      z + m = (√((z + l) * x * y) + √(z * (x + l) * (y + l))) ^ 2 / l ^ 2 := by
  obtain ⟨hx, hy, hz, -, -⟩ := h
  have hxl : 0 ≤ x + l := by linarith
  have hyl : 0 ≤ y + l := by linarith
  have hzl : 0 ≤ z + l := by linarith
  rw [ei19d_sqrt_mul3 hxl hy hz, ei19d_sqrt_mul3 hx hyl hzl] at hμ
  rw [ei19d_sqrt_mul3 hyl hx hz, ei19d_sqrt_mul3 hy hxl hzl, ei19d_sqrt_mul3 hzl hx hy,
    ei19d_sqrt_mul3 hz hxl hyl]
  have hl2 : l ^ 2 ≠ 0 := by positivity
  have ha := Real.sq_sqrt hx
  have hb := Real.sq_sqrt hy
  have hc := Real.sq_sqrt hz
  rw [eq_div_iff hl2] at hμ
  rw [eq_div_iff hl2, eq_div_iff hl2]
  have key := ei19d_perm_alg (a := √x) (b := √y) (c := √z) (l := l) (m := m)
    (by rw [Real.sq_sqrt hxl, ha]) (by rw [Real.sq_sqrt hyl, hb]) (by rw [Real.sq_sqrt hzl, hc])
    (by rw [ha]; exact hμ)
  rw [hb, hc] at key
  exact key

/-- Algebraic identity behind the square-root addition formula. -/
private lemma ei19d_sqrt_z_algebra {a b c A B C l : ℝ} (hA : A ^ 2 = a ^ 2 + l)
    (hC : C ^ 2 = c ^ 2 + l) :
    c * (A * B * (C * a * b + c * A * B) * l +
      (A * b * c + a * B * C) * (B * a * c + b * A * C) * C) =
    A ^ 2 * (C * a * b + c * A * B) ^ 2 +
      (B * a * c + b * A * C) ^ 2 * C ^ 2 -
      A ^ 2 * (B * a * c + b * A * C) ^ 2 := by
  linear_combination
    (-(A ^ 2 * B ^ 2 * c ^ 2) + A ^ 2 * C ^ 2 * b ^ 2 - C ^ 4 * b ^ 2 +
      C ^ 2 * b ^ 2 * c ^ 2 + C ^ 2 * b ^ 2 * l) * hA +
    (-(A * B * C * a * b * c) - C ^ 2 * a ^ 2 * b ^ 2 - C ^ 2 * b ^ 2 * l) * hC

/-- The defining shifted-square equation yields its nonnegative square root. -/
private lemma ei19d_shifted_sqrt {q r s l m : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hl : 0 < l) (hm : 0 < m)
    (he : q + m = (√((q + l) * r * s) + √(q * (r + l) * (s + l))) ^ 2 / l ^ 2) :
    √(q + m) * l = √(q + l) * √r * √s + √q * √(r + l) * √(s + l) := by
  have hqL : 0 ≤ q + l := by linarith
  have hrL : 0 ≤ r + l := by linarith
  have hsL : 0 ≤ s + l := by linarith
  rw [ei19d_sqrt_mul3 hqL hr hs, ei19d_sqrt_mul3 hq hrL hsL] at he
  have hl2 : l ^ 2 ≠ 0 := by positivity
  rw [eq_div_iff hl2] at he
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ q + m)]
  exact he

/-- DLMF 19.26.3 with 19.26.4: with `(ξ, η, ζ) = (x + λ, y + λ, z + λ)` and
`(ξ', η', ζ') = (x + μ, y + μ, z + μ)`, `√z = (ξζ' + η'ζ - ξη')/(√(ξηζ') + √(ξ'η'ζ))` (and the
permuted formulas for `√x`, `√y`). -/
@[dlmf 19.26.E3, dlmf 19.26.E4]
theorem symEllInt_addition_sqrt_z {x y z l m : ℝ} (h : Ei19dPosDomain x y z) (hl : 0 < l)
    (hm : 0 < m)
    (hμ : x + m = (√((x + l) * y * z) + √(x * (y + l) * (z + l))) ^ 2 / l ^ 2) :
    let ξ := x + l; let η := y + l; let ζ := z + l
    let ξ' := x + m; let η' := y + m; let ζ' := z + m
    √z = (ξ * ζ' + η' * ζ - ξ * η') / (√(ξ * η * ζ') + √(ξ' * η' * ζ)) := by
  have hx := h.1
  have hy := h.2.1
  have hz := h.2.2.1
  have hxL : 0 < x + l := by linarith
  have hyL : 0 < y + l := by linarith
  have hzL : 0 < z + l := by linarith
  have hxM : 0 < x + m := by linarith
  have hyM : 0 < y + m := by linarith
  have hzM : 0 < z + m := by linarith
  have hl0 : l ≠ 0 := ne_of_gt hl
  have hp := symEllInt_addition_mu_perm h hl hμ
  have hU := ei19d_shifted_sqrt hx hy hz hl hm hμ
  have hV := ei19d_shifted_sqrt hy hx hz hl hm hp.1
  have hW := ei19d_shifted_sqrt hz hx hy hl hm hp.2
  have hA : √(x + l) ^ 2 = √x ^ 2 + l := by rw [Real.sq_sqrt hxL.le, Real.sq_sqrt hx]
  have hC : √(z + l) ^ 2 = √z ^ 2 + l := by rw [Real.sq_sqrt hzL.le, Real.sq_sqrt hz]
  have ha := ei19d_sqrt_z_algebra (a := √x) (b := √y) (c := √z)
    (A := √(x + l)) (B := √(y + l)) (C := √(z + l)) (l := l) hA hC
  rw [← hU, ← hV, ← hW] at ha
  have he : √z * (√(x + l) * √(y + l) * √(z + m) + √(x + m) * √(y + m) * √(z + l)) =
      √(x + l) ^ 2 * √(z + m) ^ 2 + √(y + m) ^ 2 * √(z + l) ^ 2 -
        √(x + l) ^ 2 * √(y + m) ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hl0)
    linear_combination ha
  have hd : 0 < √(x + l) * √(y + l) * √(z + m) + √(x + m) * √(y + m) * √(z + l) :=
    by positivity
  dsimp only
  rw [ei19d_sqrt_mul3 hxL.le hyL.le hzM.le,
    ei19d_sqrt_mul3 hxM.le hyM.le hzL.le, eq_div_iff (ne_of_gt hd)]
  rw [Real.sq_sqrt hxL.le, Real.sq_sqrt hzM.le, Real.sq_sqrt hyM.le,
    Real.sq_sqrt hzL.le] at he
  exact he

/-- DLMF 19.26.4 (the note): `ξζ' + η'ζ - ξη' = ξ'ζ + ηζ' - ξ'η`, an identity for all
`x, y, z, λ, μ`. -/
@[dlmf 19.26.E4]
theorem symEllInt_addition_note (x y z l m : ℝ) :
    (x + l) * (z + m) + (y + m) * (z + l) - (x + l) * (y + m) =
      (x + m) * (z + l) + (y + l) * (z + m) - (x + m) * (y + l) := by
  ring

/-- `R_F(0, y, z) = (π/2) R_K(y, z)` with `lean-codes`' `Carlson.TwoVariable.carlsonRK`. -/
theorem ei19d_symEllIntRF_zero_eq_carlsonRK {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symEllIntRF 0 y z = (π / 2 : ℂ) * Carlson.TwoVariable.carlsonRK y z := by
  rw [symEllIntRF_zero_left hy hz, symEllIntR_of_mem _ _ (ei19c_slit2 hy hz)]
  unfold Carlson.TwoVariable.carlsonRK Carlson.TwoVariable.pair
  congr 2; ring

/-- DLMF 19.26.16: for `x = 0` (then `λμ = yz`, 19.26.ii.p1),
`R_F(λ, y + λ, z + λ) = R_F(0, y, z) - R_F(μ, y + μ, z + μ)`, `λ, μ, y, z > 0`. From
`lean-codes`' `Carlson.carlsonRF_add_carlsonRF_zero` (Carlson (9.7-17)). -/
@[dlmf 19.26.E16]
theorem symEllIntRF_addition_zero {y z l m : ℝ} (hy : 0 < y) (hz : 0 < z) (hl : 0 < l)
    (hm : 0 < m) (hlm : l * m = y * z) :
    symEllIntRF (l : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) =
      symEllIntRF 0 y z - symEllIntRF (m : ℂ) ((y + m : ℝ) : ℂ) ((z + m : ℝ) : ℂ) := by
  have hs : ∀ r : ℝ, 0 < r → (r : ℂ) ∈ slitPlane := fun r hr => ofReal_mem_slitPlane.mpr hr
  have H := Carlson.carlsonRF_add_carlsonRF_zero hy hz hl hm hlm
  have hrot : ∀ a b c : ℂ, symEllIntRF a b c = symEllIntRF b c a := fun a b c => by
    rw [symEllIntRF_comm_left, symEllIntRF_comm_right]
  rw [hrot (l : ℂ), hrot (m : ℂ), ei19d_symEllIntRF_zero_eq_carlsonRK (hs y hy) (hs z hz),
    symEllIntRF_eq_carlsonRF (hs _ (by linarith)) (hs _ (by linarith)) (hs l hl),
    symEllIntRF_eq_carlsonRF (hs _ (by linarith)) (hs _ (by linarith)) (hs m hm), ← H]
  ring

/-- Identity under the stated parameter and domain assumptions: `l * (l * m - (x * y + x * z + y *
z)) = 2 * √(x * y * z) * (√(x * y * z) + √((x + l) * (y + l) * (z + l))) ∧ l ^ 2 * (l + m + x
+ y + z) = (√(x * y * z) + √((x + l) * (y + l) * (z + l))) ^ 2`. -/
lemma ei19d_addition_core {x y z l m : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hl : 0 < l)
    (h5 : m = (√(x * y * z) + √((x + l) * (y + l) * (z + l))) ^ 2 / l ^ 2 - l - x - y - z) :
    l * (l * m - (x * y + x * z + y * z)) =
        2 * √(x * y * z) * (√(x * y * z) + √((x + l) * (y + l) * (z + l))) ∧
      l ^ 2 * (l + m + x + y + z) = (√(x * y * z) + √((x + l) * (y + l) * (z + l))) ^ 2 := by
  have hP := Real.sq_sqrt (show 0 ≤ x * y * z by positivity)
  have hQ := Real.sq_sqrt (show 0 ≤ (x + l) * (y + l) * (z + l) by
    have : 0 ≤ x + l := by linarith
    have : 0 ≤ y + l := by linarith
    have : 0 ≤ z + l := by linarith
    positivity)
  have hl2 : l ^ 2 ≠ 0 := by positivity
  have h2 : l ^ 2 * (l + m + x + y + z) = (√(x * y * z) + √((x + l) * (y + l) * (z + l))) ^ 2 := by
    rw [h5]; field_simp; ring
  refine ⟨?_, h2⟩
  linear_combination h2 + hQ - hP

/-- DLMF 19.26.5: (19.26.2) is equivalent to
`μ = λ^{-2} (√(xyz) + √((x + λ)(y + λ)(z + λ)))² - λ - x - y - z`. -/
@[dlmf 19.26.E5]
theorem symEllInt_addition_mu_iff {x y z l m : ℝ} (h : Ei19dPosDomain x y z) (hl : 0 < l) :
    x + m = (√((x + l) * y * z) + √(x * (y + l) * (z + l))) ^ 2 / l ^ 2 ↔
      m = (√(x * y * z) + √((x + l) * (y + l) * (z + l))) ^ 2 / l ^ 2 - l - x - y - z := by
  obtain ⟨hx, hy, hz, -, -⟩ := h
  have hxl : 0 ≤ x + l := by linarith
  have hyl : 0 ≤ y + l := by linarith
  have hzl : 0 ≤ z + l := by linarith
  rw [ei19d_sqrt_mul3 hxl hy hz, ei19d_sqrt_mul3 hx hyl hzl, ei19d_sqrt_mul3 hx hy hz,
    ei19d_sqrt_mul3 hxl hyl hzl]
  have hl2 : l ^ 2 ≠ 0 := by positivity
  have ha := Real.sq_sqrt hx
  have hb := Real.sq_sqrt hy
  have hc := Real.sq_sqrt hz
  have hA := Real.sq_sqrt hxl
  have hB := Real.sq_sqrt hyl
  have hC := Real.sq_sqrt hzl
  have alg : (√(x + l) * √y * √z + √x * √(y + l) * √(z + l)) ^ 2 -
      (√x * √y * √z + √(x + l) * √(y + l) * √(z + l)) ^ 2 + l ^ 2 * (l + √y ^ 2 + √z ^ 2) = 0 := by
    have hA' : √(x + l) ^ 2 = √x ^ 2 + l := by rw [hA, ha]
    have hB' : √(y + l) ^ 2 = √y ^ 2 + l := by rw [hB, hb]
    have hC' : √(z + l) ^ 2 = √z ^ 2 + l := by rw [hC, hc]
    linear_combination ((-(√(y + l) * √(z + l)) + √y * √z) * (√(y + l) * √(z + l) + √y * √z)) *
      hA' - (√(z + l) ^ 2 * l) * hB' - (l * (√y ^ 2 + l)) * hC'
  rw [hb, hc] at alg
  have key : (√(x + l) * √y * √z + √x * √(y + l) * √(z + l)) ^ 2 / l ^ 2 - x =
      (√x * √y * √z + √(x + l) * √(y + l) * √(z + l)) ^ 2 / l ^ 2 - l - x - y - z := by
    field_simp
    linear_combination alg
  constructor
  · intro h'; rw [← key]; linarith
  · intro h'; rw [h', ← key]; ring

/-- DLMF 19.26.6: (19.26.2) implies `(λμ - xy - xz - yz)² = 4xyz(λ + μ + x + y + z)`. -/
@[dlmf 19.26.E6]
theorem symEllInt_addition_quadratic {x y z l m : ℝ} (h : Ei19dPosDomain x y z) (hl : 0 < l)
    (hμ : x + m = (√((x + l) * y * z) + √(x * (y + l) * (z + l))) ^ 2 / l ^ 2) :
    (l * m - x * y - x * z - y * z) ^ 2 = 4 * x * y * z * (l + m + x + y + z) := by
  have h5 := (symEllInt_addition_mu_iff h hl).mp hμ
  obtain ⟨hx, hy, hz, -, -⟩ := h
  obtain ⟨h1, h2⟩ := ei19d_addition_core hx hy hz hl h5
  have hP := Real.sq_sqrt (show 0 ≤ x * y * z by positivity)
  have hl2 : l ^ 2 ≠ 0 := by positivity
  refine mul_left_cancel₀ hl2 ?_
  linear_combination (l * (l * m - (x * y + x * z + y * z)) + 2 * √(x * y * z) *
      (√(x * y * z) + √((x + l) * (y + l) * (z + l)))) * h1 +
    4 * (√(x * y * z) + √((x + l) * (y + l) * (z + l))) ^ 2 * hP - 4 * (x * y * z) * h2

/-- Identity under the stated parameter and domain assumptions: `symEllIntRF ((x + l : ℝ) : ℂ) ((y
+ l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) + symEllIntRF ((x + m : ℝ) : ℂ) ((y + m : ℝ) : ℂ) ((z + m : ℝ)
: ℂ) = symEllIntRF x y z`. -/
lemma ei19d_addition_pos {x y z l m : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hl : 0 < l)
    (hm : 0 < m)
    (h5 : m = (√(x * y * z) + √((x + l) * (y + l) * (z + l))) ^ 2 / l ^ 2 - l - x - y - z) :
    symEllIntRF ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) +
        symEllIntRF ((x + m : ℝ) : ℂ) ((y + m : ℝ) : ℂ) ((z + m : ℝ) : ℂ) =
      symEllIntRF x y z := by
  have hs : ∀ r : ℝ, 0 < r → (r : ℂ) ∈ slitPlane := fun r hr => ofReal_mem_slitPlane.mpr hr
  obtain ⟨h1, h2⟩ := ei19d_addition_core hx.le hy.le hz.le hl h5
  set P := √(x * y * z)
  set Q := √((x + l) * (y + l) * (z + l))
  have hPQ : 0 ≤ P + Q := by positivity
  have hsq : √(l + m + x + y + z) = (P + Q) / l := by
    rw [show l + m + x + y + z = ((P + Q) / l) ^ 2 by
      rw [div_pow, eq_div_iff (by positivity)]; linear_combination h2,
      Real.sqrt_sq (by positivity)]
  have h13 : l * m - x * y - x * z - y * z = 2 * P * √(l + m + x + y + z) := by
    rw [hsq]; field_simp; linear_combination h1
  rw [symEllIntRF_eq_carlsonRF (hs _ (by linarith)) (hs _ (by linarith)) (hs _ (by linarith)),
    symEllIntRF_eq_carlsonRF (hs _ (by linarith)) (hs _ (by linarith)) (hs _ (by linarith)),
    symEllIntRF_eq_carlsonRF (hs x hx) (hs y hy) (hs z hz)]
  exact Carlson.carlsonRF_add_carlsonRF hx hy hz hl hm h13

/-- Identity under the stated parameter and domain assumptions: `symEllIntRF ((x + l : ℝ) : ℂ) ((y
+ l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) + symEllIntRF ((x + m : ℝ) : ℂ) ((y + m : ℝ) : ℂ) ((z + m : ℝ)
: ℂ) = symEllIntRF x y z`. -/
lemma ei19d_addition_of_first {x y z l m : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z)
    (hl : 0 < l) (hm : 0 < m)
    (h5 : m = (√(x * y * z) + √((x + l) * (y + l) * (z + l))) ^ 2 / l ^ 2 - l - x - y - z) :
    symEllIntRF ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) +
        symEllIntRF ((x + m : ℝ) : ℂ) ((y + m : ℝ) : ℂ) ((z + m : ℝ) : ℂ) =
      symEllIntRF x y z := by
  rcases hx.eq_or_lt with h0 | hx'
  · subst h0
    obtain ⟨h1, -⟩ := ei19d_addition_core le_rfl hy.le hz.le hl h5
    have hlm : l * m = y * z := by
      have : l * (l * m - y * z) = 0 := by simpa using h1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hl.ne'
      · linarith
    have H := symEllIntRF_addition_zero hy hz hl hm hlm
    simp only [zero_add, ofReal_zero]
    rw [H]; ring
  · exact ei19d_addition_pos hx' hy hz hl hm h5

/-- DLMF 19.26.1 with 19.26.2: the addition theorem
`R_F(x + λ, y + λ, z + λ) + R_F(x + μ, y + μ, z + μ) = R_F(x, y, z)`, where `λ, μ > 0` and
`x + μ = λ^{-2} (√((x + λ) y z) + √(x (y + λ)(z + λ)))²` (19.26.2; the permuted equations for
`y + μ`, `z + μ` follow, `symEllInt_addition_mu_perm`). -/
@[dlmf 19.26.E1, dlmf 19.26.E2]
theorem symEllIntRF_add_symEllIntRF {x y z l m : ℝ} (h : Ei19dPosDomain x y z) (hl : 0 < l)
    (hm : 0 < m)
    (hμ : x + m = (√((x + l) * y * z) + √(x * (y + l) * (z + l))) ^ 2 / l ^ 2) :
    symEllIntRF ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) +
        symEllIntRF ((x + m : ℝ) : ℂ) ((y + m : ℝ) : ℂ) ((z + m : ℝ) : ℂ) =
      symEllIntRF x y z := by
  have h5 := (symEllInt_addition_mu_iff h hl).mp hμ
  obtain ⟨hx, hy, hz, h0x, h0y⟩ := h
  have hrot : ∀ a b c : ℂ, symEllIntRF a b c = symEllIntRF b c a := fun a b c => by
    rw [symEllIntRF_comm_left, symEllIntRF_comm_right]
  rcases hy.eq_or_lt with hy0 | hy'
  · -- `y = 0`: then `x, z > 0`
    have hx' : 0 < x := hx.lt_of_ne (fun hx0 => (h0x hx0.symm).1.ne' hy0.symm)
    have hz' : 0 < z := (h0y hy0.symm)
    have H := ei19d_addition_of_first hy hx' hz' hl hm (by
      rw [h5, show y * x * z = x * y * z by ring,
        show (y + l) * (x + l) * (z + l) = (x + l) * (y + l) * (z + l) by ring]; ring)
    rw [symEllIntRF_comm_left ((x + l : ℝ) : ℂ), symEllIntRF_comm_left ((x + m : ℝ) : ℂ),
      symEllIntRF_comm_left (x : ℂ)] at H
    exact H
  rcases hz.eq_or_lt with hz0 | hz'
  · -- `z = 0`: then `x, y > 0`
    have hx' : 0 < x := hx.lt_of_ne (fun hx0 => (h0x hx0.symm).2.ne' hz0.symm)
    have H := ei19d_addition_of_first hz hx' hy' hl hm (by
      rw [h5, show z * x * y = x * y * z by ring,
        show (z + l) * (x + l) * (y + l) = (x + l) * (y + l) * (z + l) by ring]; ring)
    rw [hrot ((z + l : ℝ) : ℂ), hrot ((z + m : ℝ) : ℂ), hrot (z : ℂ)] at H
    exact H
  · exact ei19d_addition_of_first hx hy' hz' hl hm h5

/-- The canonical node derivative expressed using the continued Carlson `R_F`. -/
lemma hasDerivAt_carlsonRF_right {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    HasDerivAt (fun w => Carlson.carlsonRF x y w) (-(1 / 6) * symEllIntRD x y z) z := by
  apply (hasDerivAt_symEllIntRF_right hx hy hz).congr_of_eventuallyEq
  filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
  exact (symEllIntRF_eq_carlsonRF hx hy hw).symm

open scoped Classical in
/-- The real final-variable derivative of `R_F` also holds when its first variable is zero. -/
lemma hasDerivAt_symEllIntRF_right_real {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => symEllIntRF x y w) (-(1 / 6) * symEllIntRD x y z) z := by
  classical
  have hyc := ofReal_mem_slitPlane.mpr hy
  have hzc := ofReal_mem_slitPlane.mpr hz
  by_cases hx0 : x = 0
  · subst x
    have H := (Carlson.hasDerivAt_regCarlsonR_update (-(1 / 2))
      (![1 / 2, 1 / 2] : Fin 2 → ℂ) (ei19c_slit2 hyc hzc) 1).const_mul (π / 2 : ℂ)
    have he : Dirichlet.addDirichletUnit (![1 / 2, 1 / 2] : Fin 2 → ℂ) 1 = ![1 / 2, 3 / 2] := by
      funext i; fin_cases i <;> norm_num [Dirichlet.addDirichletUnit]
    have H' : HasDerivAt (fun w : ℂ => symEllIntRF 0 y w)
        ((π / 2 : ℂ) * (-(1 / 2) * (1 / 2) * Carlson.regCarlsonR (-(1 / 2) - 1)
          (Dirichlet.addDirichletUnit (![1 / 2, 1 / 2] : Fin 2 → ℂ) 1) ![(y : ℂ), z])) (z : ℂ) := by
      apply H.congr_of_eventuallyEq
      filter_upwards [isOpen_slitPlane.mem_nhds hzc] with w hw
      rw [symEllIntRF_zero_left hyc hw, symEllIntR_of_mem _ _ (ei19c_slit2 hyc hw), Carlson.carlsonR]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
      congr 2
      funext i; fin_cases i <;> simp [Function.update]
    refine H'.comp_ofReal.congr_deriv ?_
    simp only [ofReal_zero]
    rw [he, symEllIntRD_zero_left hyc hzc, symEllIntR_of_mem _ _ (ei19c_slit2 hyc hzc), Carlson.carlsonR]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num [ei19c_Gamma_two]
    ring
  · have hxc := ofReal_mem_slitPlane.mpr (lt_of_le_of_ne hx (Ne.symm hx0))
    exact (hasDerivAt_symEllIntRF_right hxc hyc hzc).comp_ofReal

/-- A variable common translation and a variable final coordinate separate in the derivative
of `R_F`. The two contributions are the diagonal derivative and `-R_D/6`. -/
lemma hasDerivAt_carlsonRF_translate_right {x y z l' : ℝ} {l : ℝ → ℝ}
    (hl : HasDerivAt l l' z) (hx : 0 < x + l z) (hy : 0 < y + l z) (hz : 0 < z + l z) :
    HasDerivAt (fun w : ℝ => Carlson.carlsonRF (x + l w : ℝ) (y + l w : ℝ) (w + l w : ℝ))
      (-(1 / 2) * (l' : ℂ) * ((x + l z : ℝ) : ℂ) ^ (-1 / 2 : ℂ) *
        ((y + l z : ℝ) : ℂ) ^ (-1 / 2 : ℂ) * ((z + l z : ℝ) : ℂ) ^ (-1 / 2 : ℂ) -
        (1 / 6) * symEllIntRD (x + l z : ℝ) (y + l z : ℝ) (z + l z : ℝ)) z := by
  let p : Fin 3 → ℂ := ![((x + l z : ℝ) : ℂ), ((y + l z : ℝ) : ℂ), ((z + l z : ℝ) : ℂ)]
  let F : (Fin 3 → ℂ) → ℂ := Carlson.carlsonR (-1 / 2) (fun _ => 1 / 2)
  let v : Fin 3 → ℂ := fun _ => 1
  let e : Fin 3 → ℂ := ![0, 0, 1]
  have hp : p ∈ Carlson.carlsonRSlitDomain :=
    ei19c_slit3 (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz)
  have hF : DifferentiableAt ℂ F p := by
    have HF : AnalyticAt ℂ F p := by
      unfold F Carlson.carlsonR
      exact analyticAt_const.mul (Carlson.analyticOnNhd_regCarlsonR (-1 / 2) (fun _ => 1 / 2) p hp)
    exact HF.differentiableAt
  let L := fderiv ℂ F p
  have hv : HasDerivAt (fun w : ℂ => p + w • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add p
  have HV := hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hv (by simp)
  have hfv : (F ∘ fun w : ℂ => p + w • v) = fun w =>
      Carlson.carlsonRF (w + (x + l z : ℝ)) (w + (y + l z : ℝ)) (w + (z + l z : ℝ)) := by
    funext w
    change Carlson.carlsonR (-1 / 2) (fun _ : Fin 3 => (1 / 2 : ℂ)) (p + w • v) =
      Carlson.carlsonR (-1 / 2) (fun _ : Fin 3 => (1 / 2 : ℂ))
        ![w + (x + l z : ℝ), w + (y + l z : ℝ), w + (z + l z : ℝ)]
    congr 1
    funext i; fin_cases i <;> simp [p, v, smul_eq_mul] <;> ring
  rw [hfv] at HV
  have HT := Carlson.hasDerivAt_carlsonRF_add (l := 0)
    (x := ((x + l z : ℝ) : ℂ)) (y := ((y + l z : ℝ) : ℂ)) (z := ((z + l z : ℝ) : ℂ))
    (by simpa only [zero_add] using (ofReal_mem_slitPlane.mpr hx))
    (by simpa only [zero_add] using (ofReal_mem_slitPlane.mpr hy))
    (by simpa only [zero_add] using (ofReal_mem_slitPlane.mpr hz))
  have hLV : L v = -(1 / 2) * (((x + l z : ℝ) : ℂ) ^ (-1 / 2 : ℂ) *
      ((y + l z : ℝ) : ℂ) ^ (-1 / 2 : ℂ) * ((z + l z : ℝ) : ℂ) ^ (-1 / 2 : ℂ)) := by
    convert HV.unique HT using 1; simp only [zero_add]
    ring
  have he : HasDerivAt (fun w : ℂ => ![p 0, p 1, w]) e (p 2) := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_id _
  have HE := hF.hasFDerivAt.comp_hasDerivAt_of_eq (p 2) he (by funext i; fin_cases i <;> rfl)
  have hfe : (F ∘ fun w : ℂ => ![p 0, p 1, w]) = fun w => Carlson.carlsonRF (p 0) (p 1) w := rfl
  rw [hfe] at HE
  have hLE : L e = -(1 / 6) * symEllIntRD (p 0) (p 1) (p 2) :=
    HE.unique (hasDerivAt_carlsonRF_right (hp 0) (hp 1) (hp 2))
  have hN : HasDerivAt (fun w : ℝ =>
      ![((x + l w : ℝ) : ℂ), ((y + l w : ℝ) : ℂ), ((w + l w : ℝ) : ℂ)])
      ((l' : ℂ) • v + e) z := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [v, e] using (hl.const_add x).ofReal_comp
    · simpa [v, e] using (hl.const_add y).ofReal_comp
    · convert ((hasDerivAt_id z).add hl).ofReal_comp using 1 <;> simp [v, e]; ring
  have HC := hF.hasFDerivAt.restrictScalars ℝ |>.comp_hasDerivAt_of_eq z hN rfl
  change HasDerivAt _ (L ((l' : ℂ) • v + e)) z at HC
  rw [map_add, map_smul, hLV, hLE] at HC
  refine HC.congr_deriv ?_
  simp only [smul_eq_mul, p, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- Differentiation of the first-kind addition theorem gives the third-kind addition
formula, including a possible zero first argument. -/
lemma symEllIntRD_add_of_nonneg {x y z l m : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z)
    (hl : 0 < l) (hm : 0 < m)
    (hmu : x + m = (√((x + l) * y * z) + √(x * (y + l) * (z + l))) ^ 2 / l ^ 2) :
    symEllIntRD (x + l : ℝ) (y + l : ℝ) (z + l : ℝ) + symEllIntRD (x + m : ℝ) (y + m : ℝ) (z + m : ℝ) =
      symEllIntRD x y z - ((3 / √(z * (z + l) * (z + m)) : ℝ) : ℂ) := by
  let u := √(x + l) * √y
  let v := √x * √(y + l)
  let M : ℝ → ℝ := fun w => (u * √w + v * √(w + l)) ^ 2 / l ^ 2 - x
  let d := 2 * (u * √z + v * √(z + l)) * (u / (2 * √z) + v / (2 * √(z + l))) / l ^ 2
  have hxL : 0 < x + l := by linarith
  have hyL : 0 < y + l := by linarith
  have hzL : 0 < z + l := by linarith
  have hxM : 0 < x + m := by linarith
  have hyM : 0 < y + m := by linarith
  have hzM : 0 < z + m := by linarith
  have hsz : 0 < √z := Real.sqrt_pos.mpr hz
  have hszL : 0 < √(z + l) := Real.sqrt_pos.mpr hzL
  have hszM : 0 < √(z + m) := Real.sqrt_pos.mpr hzM
  have heq : M z = m := by
    rw [ei19d_sqrt_mul3 hxL.le hy.le hz.le,
      ei19d_sqrt_mul3 hx hyL.le hzL.le] at hmu
    dsimp only [M, u, v]
    linarith
  have hM : HasDerivAt M d z := by
    have H := (((Real.hasDerivAt_sqrt hz.ne').const_mul u).add
      (((hasDerivAt_id z).add_const l).sqrt hzL.ne' |>.const_mul v)).pow 2
    convert (H.div_const (l ^ 2)).sub_const x using 1 <;> simp [M, d]
    ring
  have hdom (w : ℝ) (hw : 0 < w) : Ei19dPosDomain x y w :=
    ⟨hx, hy.le, hw.le, fun _ => ⟨hy, hw⟩, fun hh => False.elim (hy.ne' hh)⟩
  have hev : (fun w : ℝ => symEllIntRF x y w) =ᶠ[𝓝 z] fun w : ℝ =>
      Carlson.carlsonRF (x + l : ℝ) (y + l : ℝ) (w + l : ℝ) +
      Carlson.carlsonRF (x + M w : ℝ) (y + M w : ℝ) (w + M w : ℝ) := by
    have hMpos : ∀ᶠ w in 𝓝 z, 0 < M w := hM.continuousAt.eventually
      (eventually_gt_nhds (show 0 < M z by rw [heq]; exact hm))
    filter_upwards [eventually_gt_nhds hz, hMpos] with w hw hMw
    have H := symEllIntRF_add_symEllIntRF (hdom w hw) hl hMw (m := M w) (by
      rw [ei19d_sqrt_mul3 hxL.le hy.le hw.le,
        ei19d_sqrt_mul3 hx hyL.le (by linarith : 0 ≤ w + l)]
      dsimp only [M, u, v]; ring)
    rw [symEllIntRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr hxL) (ofReal_mem_slitPlane.mpr hyL)
      (ofReal_mem_slitPlane.mpr (by linarith)),
      symEllIntRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr (by linarith))
        (ofReal_mem_slitPlane.mpr (by linarith)) (ofReal_mem_slitPlane.mpr (by linarith))] at H
    exact H.symm
  have HL := hasDerivAt_carlsonRF_translate_right (x := x) (y := y) (z := z)
    (hasDerivAt_const z l) hxL hyL hzL
  have HM := hasDerivAt_carlsonRF_translate_right hM
    (by rw [heq]; exact hxM) (by rw [heq]; exact hyM) (by rw [heq]; exact hzM)
  have HE := ((hasDerivAt_symEllIntRF_right_real hx hy hz).congr_of_eventuallyEq hev.symm).unique
    (HL.add HM)
  simp only [ofReal_zero, mul_zero, zero_mul, zero_sub, heq] at HE
  rw [← ei19c_inv_cpow_half, ← ei19c_inv_cpow_half, ← ei19c_inv_cpow_half,
    Carlson.ofReal_cpow_half hxM.le, Carlson.ofReal_cpow_half hyM.le,
    Carlson.ofReal_cpow_half hzM.le] at HE
  have hU := ei19d_shifted_sqrt hx hy.le hz.le hl hm hmu
  have hV := ei19d_shifted_sqrt hy.le hx hz.le hl hm
    ((symEllInt_addition_mu_perm (hdom z hz) hl hmu).1)
  have hd : d * (√z * √(z + l)) = √(x + m) * √(y + m) := by
    dsimp only [d, u, v]
    apply mul_right_cancel₀ (pow_ne_zero 2 hl.ne')
    calc _ = (√(x + l) * √y * √z + √x * √(y + l) * √(z + l)) *
        (√(y + l) * √x * √z + √y * √(x + l) * √(z + l)) := by field_simp; ring
         _ = _ := by rw [← hU, ← hV]; ring
  have hs : d * (√(x + m) * √(y + m) * √(z + m))⁻¹ = (√(z * (z + l) * (z + m)))⁻¹ := by
    rw [ei19d_sqrt_mul3 hz.le hzL.le hzM.le]
    apply (mul_right_inj' (show √z * √(z + l) * √(z + m) ≠ 0 by positivity)).mp
    field_simp
    nlinarith [hd]
  have hSC := congrArg (fun r : ℝ => (r : ℂ)) hs
  push_cast at HE hSC ⊢
  simp only [mul_inv_rev] at hSC
  linear_combination (6 : ℂ) * HE - (3 : ℂ) * hSC

/-- DLMF 19.26.7: `R_D(x + λ, y + λ, z + λ) + R_D(x + μ, y + μ, z + μ)
= R_D(x, y, z) - 3/√(z (z + λ)(z + μ))`, with `λ, μ` as in (19.26.1)–(19.26.2) and `z > 0`
(`R_D`'s third argument is nonzero). -/
@[dlmf 19.26.E7]
theorem symEllIntRD_add_symEllIntRD {x y z l m : ℝ} (h : Ei19dPosDomain x y z) (hz : 0 < z)
    (hl : 0 < l) (hm : 0 < m)
    (hμ : x + m = (√((x + l) * y * z) + √(x * (y + l) * (z + l))) ^ 2 / l ^ 2) :
    symEllIntRD ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) +
        symEllIntRD ((x + m : ℝ) : ℂ) ((y + m : ℝ) : ℂ) ((z + m : ℝ) : ℂ) =
      symEllIntRD x y z - ((3 / √(z * (z + l) * (z + m)) : ℝ) : ℂ) := by
  rcases h with ⟨hx, hy, _, hx0, hy0⟩
  by_cases hyz : y = 0
  · subst y
    have hx' : 0 < x := by
      by_contra hh
      have hxx : x = 0 := by linarith
      exact (hx0 hxx).1.ne' rfl
    have hdom : Ei19dPosDomain x 0 z := ⟨hx, le_rfl, hz.le, hx0, hy0⟩
    have hp := (symEllInt_addition_mu_perm hdom hl hμ).1
    have H := symEllIntRD_add_of_nonneg (x := 0) (by norm_num) hx' hz hl hm hp
    simpa only [ofReal_zero, symEllIntRD_comm] using H
  · exact symEllIntRD_add_of_nonneg hx (lt_of_le_of_ne hy (Ne.symm hyz)) hz hl hm hμ

/-- Polynomial identity behind the square-root correction in second-kind addition. -/
private lemma rg_addition_root_algebra {a b c A B C l : ℝ}
    (hA : A ^ 2 = a ^ 2 + l) (hB : B ^ 2 = b ^ 2 + l) (hC : C ^ 2 = c ^ 2 + l) :
    (A * b * c + a * B * C) * (B * a * c + b * A * C) * c * C -
      (C * a * b + c * A * B) * (A * B * c ^ 3 + a * b * C ^ 3) +
      (a ^ 2 - c ^ 2) * (b ^ 2 - c ^ 2) * l ^ 2 = 0 := by
  linear_combination (-B ^ 2 * c ^ 4 + C ^ 2 * b ^ 2 * c ^ 2) * hA +
    (C ^ 2 * a ^ 2 * c ^ 2 - a ^ 2 * c ^ 4 - c ^ 4 * l) * hB +
    (-C ^ 2 * a ^ 2 * b ^ 2 + a ^ 2 * b ^ 2 * c ^ 2 - a ^ 2 * b ^ 2 * l +
      a ^ 2 * c ^ 2 * l + b ^ 2 * c ^ 2 * l) * hC

/-- The second-kind addition theorem when its final two arguments are positive. -/
lemma symEllIntRG_add_of_nonneg {x y z l m : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z)
    (hl : 0 < l) (hm : 0 < m)
    (hmu : x + m = (√((x + l) * y * z) + √(x * (y + l) * (z + l))) ^ 2 / l ^ 2) :
    2 * symEllIntRG (x + l : ℝ) (y + l : ℝ) (z + l : ℝ) +
        2 * symEllIntRG (x + m : ℝ) (y + m : ℝ) (z + m : ℝ) =
      2 * symEllIntRG x y z + l * symEllIntRF (x + l : ℝ) (y + l : ℝ) (z + l : ℝ) +
        m * symEllIntRF (x + m : ℝ) (y + m : ℝ) (z + m : ℝ) + (√(l + m + x + y + z) : ℂ) := by
  have hdom : Ei19dPosDomain x y z := ⟨hx, hy.le, hz.le, fun _ => ⟨hy, hz⟩,
    fun hh => False.elim (hy.ne' hh)⟩
  have hxL : 0 < x + l := by linarith
  have hyL : 0 < y + l := by linarith
  have hzL : 0 < z + l := by linarith
  have hxM : 0 < x + m := by linarith
  have hyM : 0 < y + m := by linarith
  have hzM : 0 < z + m := by linarith
  have hs : 0 < l + m + x + y + z := by linarith
  have hU := ei19d_shifted_sqrt hx hy.le hz.le hl hm hmu
  have hp := symEllInt_addition_mu_perm hdom hl hmu
  have hV := ei19d_shifted_sqrt hy.le hx hz.le hl hm hp.1
  have hW := ei19d_shifted_sqrt hz.le hx hy.le hl hm hp.2
  have hsum := (ei19d_addition_core hx hy.le hz.le hl ((symEllInt_addition_mu_iff hdom hl).mp hmu)).2
  rw [ei19d_sqrt_mul3 hx hy.le hz.le, ei19d_sqrt_mul3 hxL.le hyL.le hzL.le] at hsum
  have hS : √(l + m + x + y + z) * l = √x * √y * √z + √(x + l) * √(y + l) * √(z + l) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hs.le]
    linear_combination hsum
  have hdif : (x - z) * (y - z) = (√x ^ 2 - √z ^ 2) * (√y ^ 2 - √z ^ 2) := by
    rw [Real.sq_sqrt hx, Real.sq_sqrt hy.le, Real.sq_sqrt hz.le]
  have hscalar : √(x + l) * √(y + l) / √(z + l) + √(x + m) * √(y + m) / √(z + m) - √x * √y / √z +
      (x - z) * (y - z) / √(z * (z + l) * (z + m)) = √(l + m + x + y + z) := by
    have hU' := (eq_div_iff hl.ne').mpr hU
    have hV' := (eq_div_iff hl.ne').mpr hV
    have hW' := (eq_div_iff hl.ne').mpr hW
    have hS' := (eq_div_iff hl.ne').mpr hS
    rw [hdif, ei19d_sqrt_mul3 hz.le hzL.le hzM.le]
    apply (mul_right_inj' (show √z * √(z + l) * √(z + m) * l ^ 2 ≠ 0 by positivity)).mp
    field_simp
    rw [hU', hV', hW', hS']
    field_simp
    have hA : √(x + l) ^ 2 = √x ^ 2 + l := by rw [Real.sq_sqrt hxL.le, Real.sq_sqrt hx]
    have hB : √(y + l) ^ 2 = √y ^ 2 + l := by rw [Real.sq_sqrt hyL.le, Real.sq_sqrt hy.le]
    have hC : √(z + l) ^ 2 = √z ^ 2 + l := by rw [Real.sq_sqrt hzL.le, Real.sq_sqrt hz.le]
    have H := rg_addition_root_algebra hA hB hC
    linear_combination H + (√(z + l) ^ 2 * √x ^ 2 * √y ^ 2 - √z ^ 2 * √(x + l) ^ 2 * √(y + l) ^ 2) * hC
  have hxC : SymEllIntArg (x : ℂ) := by
    by_cases hh : x = 0
    · exact Or.inr (by simp [hh])
    · exact Or.inl (ofReal_mem_slitPlane.mpr (lt_of_le_of_ne hx (Ne.symm hh)))
  have hG := p19sR1_two_mul_symEllIntRG hxC (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz)
  have hGL := p19sR1_two_mul_symEllIntRG (Or.inl (ofReal_mem_slitPlane.mpr hxL))
    (ofReal_mem_slitPlane.mpr hyL) (ofReal_mem_slitPlane.mpr hzL)
  have hGM := p19sR1_two_mul_symEllIntRG (Or.inl (ofReal_mem_slitPlane.mpr hxM))
    (ofReal_mem_slitPlane.mpr hyM) (ofReal_mem_slitPlane.mpr hzM)
  rw [← ei19c_inv_cpow_half, Carlson.ofReal_cpow_half hx,
    Carlson.ofReal_cpow_half hy.le, Carlson.ofReal_cpow_half hz.le] at hG
  rw [← ei19c_inv_cpow_half, Carlson.ofReal_cpow_half hxL.le,
    Carlson.ofReal_cpow_half hyL.le, Carlson.ofReal_cpow_half hzL.le] at hGL
  rw [← ei19c_inv_cpow_half, Carlson.ofReal_cpow_half hxM.le,
    Carlson.ofReal_cpow_half hyM.le, Carlson.ofReal_cpow_half hzM.le] at hGM
  have hRF := symEllIntRF_add_symEllIntRF hdom hl hm hmu
  have hRD := symEllIntRD_add_of_nonneg hx hy hz hl hm hmu
  have hSC := congrArg (fun r : ℝ => (r : ℂ)) hscalar
  push_cast at hG hGL hGM hRF hRD hSC ⊢
  simp only [div_eq_mul_inv] at hSC hRD
  linear_combination hGL + hGM - hG + (z : ℂ) * hRF -
    (1 / 3 : ℂ) * ((x : ℂ) - z) * ((y : ℂ) - z) * hRD + hSC

/-- DLMF 19.26.8: `2R_G(x + λ, …) + 2R_G(x + μ, …) = 2R_G(x, y, z) + λ R_F(x + λ, …)
+ μ R_F(x + μ, …) + √(λ + μ + x + y + z)`, with `λ, μ` as in (19.26.1)–(19.26.2). -/
@[dlmf 19.26.E8]
theorem symEllIntRG_add_symEllIntRG {x y z l m : ℝ} (h : Ei19dPosDomain x y z) (hl : 0 < l)
    (hm : 0 < m)
    (hμ : x + m = (√((x + l) * y * z) + √(x * (y + l) * (z + l))) ^ 2 / l ^ 2) :
    2 * symEllIntRG ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) +
        2 * symEllIntRG ((x + m : ℝ) : ℂ) ((y + m : ℝ) : ℂ) ((z + m : ℝ) : ℂ) =
      2 * symEllIntRG x y z +
        l * symEllIntRF ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) +
        m * symEllIntRF ((x + m : ℝ) : ℂ) ((y + m : ℝ) : ℂ) ((z + m : ℝ) : ℂ) +
        ((√(l + m + x + y + z) : ℝ) : ℂ) := by
  by_cases hz0 : z = 0
  · rcases h with ⟨hx, hy, hz, hx0, hy0⟩
    subst z
    have hx' : 0 < x := by
      by_contra hh
      have hxx : x = 0 := by linarith
      exact (hx0 hxx).2.ne' rfl
    have hy' : 0 < y := by
      by_contra hh
      have hyy : y = 0 := by linarith
      exact (hy0 hyy).ne' rfl
    have hdom : Ei19dPosDomain x y 0 := ⟨hx, hy, le_rfl, hx0, hy0⟩
    have hp := (symEllInt_addition_mu_perm hdom hl hμ).2
    have H := symEllIntRG_add_of_nonneg (x := 0) (by norm_num) hx' hy' hl hm hp
    simpa only [ofReal_zero, zero_add, add_zero, symEllIntRG_comm_left, symEllIntRG_comm_right,
      symEllIntRF_comm_left, symEllIntRF_comm_right, add_comm, add_left_comm, add_assoc] using H
  · rcases h with ⟨hx, hy, hz, hx0, hy0⟩
    have hz' : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    by_cases hyz : y = 0
    · subst y
      have hx' : 0 < x := by
        by_contra hh
        have hxx : x = 0 := by linarith
        exact (hx0 hxx).1.ne' rfl
      have hdom : Ei19dPosDomain x 0 z := ⟨hx, le_rfl, hz, hx0, hy0⟩
      have hp := (symEllInt_addition_mu_perm hdom hl hμ).1
      have H := symEllIntRG_add_of_nonneg (x := 0) (by norm_num) hx' hz' hl hm hp
      simpa only [ofReal_zero, zero_add, add_zero, symEllIntRG_comm_left,
        symEllIntRF_comm_left, add_comm, add_left_comm, add_assoc] using H
    · exact symEllIntRG_add_of_nonneg hx (lt_of_le_of_ne hy (Ne.symm hyz)) hz' hl hm hμ


/-- DLMF 19.26.9 with 19.26.10: `R_J(x + λ, y + λ, z + λ, p + λ) + R_J(x + μ, y + μ, z + μ, p + μ)
= R_J(x, y, z, p) - 3 R_C(γ - δ, γ)`, `γ = p(p + λ)(p + μ)`, `δ = (p - x)(p - y)(p - z)`, with
`λ, μ` as in (19.26.1)–(19.26.2) and `p > 0` (the identity fails for `p < 0`). -/
@[dlmf 19.26.E9, dlmf 19.26.E10]
theorem symEllIntRJ_add_symEllIntRJ {x y z p l m : ℝ} (h : Ei19dPosDomain x y z) (hp : 0 < p)
    (hl : 0 < l) (hm : 0 < m)
    (hμ : x + m = (√((x + l) * y * z) + √(x * (y + l) * (z + l))) ^ 2 / l ^ 2) :
    let γ := p * (p + l) * (p + m)
    let δ := (p - x) * (p - y) * (p - z)
    symEllIntRJ ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) ((p + l : ℝ) : ℂ) +
        symEllIntRJ ((x + m : ℝ) : ℂ) ((y + m : ℝ) : ℂ) ((z + m : ℝ) : ℂ) ((p + m : ℝ) : ℂ) =
      symEllIntRJ x y z p - 3 * symEllIntRC ((γ - δ : ℝ) : ℂ) (γ : ℂ) := by
  sorry

/-- DLMF 19.26.11 with 19.26.12: `R_C(x + λ, y + λ) + R_C(x + μ, y + μ) = R_C(x, y)` for
`λ > 0`, `y > 0`, `x ≥ 0`, where `x + μ = λ^{-2} (√(x + λ) y + √x (y + λ))²`. -/
@[dlmf 19.26.E11, dlmf 19.26.E12]
theorem symEllIntRC_add_symEllIntRC {x y l m : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hl : 0 < l)
    (hμ : x + m = (√(x + l) * y + √x * (y + l)) ^ 2 / l ^ 2) :
    symEllIntRC ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) + symEllIntRC ((x + m : ℝ) : ℂ)
        ((y + m : ℝ) : ℂ) =
      symEllIntRC x y := by
  have hnn : ∀ r : ℝ, 0 ≤ r → ¬ IsNegReal (r : ℂ) := fun r hr ⟨_, h⟩ => by
    simp at h; linarith
  have hsx := Real.sq_sqrt hx
  have hsxl := Real.sq_sqrt (show 0 ≤ x + l by linarith)
  have hsx0 := Real.sqrt_nonneg x
  have hsxl0 : 0 < √(x + l) := Real.sqrt_pos.mpr (by linarith)
  have hm : 0 < m := by
    have hl2 : 0 < l ^ 2 := by positivity
    rw [eq_div_iff hl2.ne'] at hμ
    have : (√(x + l) * y + √x * (y + l)) ^ 2 > x * l ^ 2 := by
      have hB : (√x * (y + l)) ^ 2 = x * (y + l) ^ 2 := by rw [mul_pow, hsx]
      have hA : 0 < (√(x + l) * y) ^ 2 := by positivity
      have hAB : 0 ≤ (√(x + l) * y) * (√x * (y + l)) :=
        mul_nonneg (by positivity) (mul_nonneg hsx0 (by linarith))
      have hxl : x * l ^ 2 ≤ x * (y + l) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith) hx
      nlinarith
    nlinarith
  have hμ' : x + m = (√((x + l) * y * y) + √(x * (y + l) * (y + l))) ^ 2 / l ^ 2 := by
    rw [hμ, show (x + l) * y * y = (x + l) * (y * y) by ring, Real.sqrt_mul (by linarith),
      Real.sqrt_mul_self hy.le, show x * (y + l) * (y + l) = x * ((y + l) * (y + l)) by ring,
      Real.sqrt_mul hx, Real.sqrt_mul_self (by linarith)]
  have h := symEllIntRF_add_symEllIntRF (x := x) (y := y) (z := y)
    ⟨hx, hy.le, hy.le, fun _ => ⟨hy, hy⟩, fun h0 => absurd h0 hy.ne'⟩ hl hm hμ'
  rw [symEllIntRC_eq_symEllIntRF _ (hnn _ (by linarith)), symEllIntRC_eq_symEllIntRF _ (hnn _ (by linarith)),
    symEllIntRC_eq_symEllIntRF _ (hnn _ hy.le)]
  exact h

/-- DLMF 19.26.12 (second equation): `x + μ = λ^{-2} (√(x + λ) y + √x (y + λ))²` implies
`y + μ = (y (y + λ)/λ²) (√x + √(x + λ))²`. -/
@[dlmf 19.26.E12]
theorem symEllIntRC_addition_mu {x y l m : ℝ} (hx : 0 ≤ x) (hl : 0 < l)
    (hμ : x + m = (√(x + l) * y + √x * (y + l)) ^ 2 / l ^ 2) :
    y + m = y * (y + l) / l ^ 2 * (√x + √(x + l)) ^ 2 := by
  have hl2 : l ^ 2 ≠ 0 := by positivity
  have hs := Real.sq_sqrt hx
  have hr := Real.sq_sqrt (show 0 ≤ x + l by linarith)
  rw [eq_div_iff hl2] at hμ
  have h2 : (y + m) * l ^ 2 = y * (y + l) * (√x + √(x + l)) ^ 2 := by
    linear_combination hμ - (l * y) * hr + (l * y + l ^ 2) * hs
  rw [div_mul_eq_mul_div, eq_div_iff hl2]
  exact h2

/-- DLMF 19.26.13: `R_C(α², α² - θ) + R_C(β², β² - θ) = R_C(σ², σ² - θ)`,
`σ = (αβ + θ)/(α + β)`, where `0 < γ² - θ < γ²` for `γ = α, β, σ`, except that `σ² - θ` can be
`0`. **Corrected**: we also assume `α, β > 0` (DLMF's conditions do not fix the signs of `α, β`;
the identity fails for `α = -2, β = 3, θ = 3/2`). -/
@[dlmf 19.26.E13]
theorem symEllIntRC_addition_theta {α β θ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hα₁ : 0 < α ^ 2 - θ) (hα₂ : α ^ 2 - θ < α ^ 2) (hβ₁ : 0 < β ^ 2 - θ) :
    let σ := (α * β + θ) / (α + β)
    symEllIntRC ((α ^ 2 : ℝ) : ℂ) ((α ^ 2 - θ : ℝ) : ℂ) + symEllIntRC ((β ^ 2 : ℝ) : ℂ)
        ((β ^ 2 - θ : ℝ) : ℂ) =
      symEllIntRC ((σ ^ 2 : ℝ) : ℂ) ((σ ^ 2 - θ : ℝ) : ℂ) := by
  let σ := (α * β + θ) / (α + β)
  have hd : 0 < α + β := by linarith
  have hθ : 0 < θ := by linarith
  have hs : 0 < σ := div_pos (by positivity) hd
  have hsα : σ < α := (div_lt_iff₀ hd).mpr (by nlinarith [hα₁])
  have hsβ : σ < β := (div_lt_iff₀ hd).mpr (by nlinarith [hβ₁])
  have hσ : σ * (α + β) = α * β + θ := div_mul_cancel₀ _ hd.ne'
  have hprod : (σ ^ 2 - θ) * (α + β) ^ 2 = (α ^ 2 - θ) * (β ^ 2 - θ) := by
    dsimp only [σ]
    field_simp
    ring
  have hy : 0 < σ ^ 2 - θ := by
    by_contra h
    have hn := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) (sq_nonneg (α + β))
    rw [hprod] at hn
    exact (not_le_of_gt (mul_pos hα₁ hβ₁)) hn
  let l := α ^ 2 - σ ^ 2
  let m := β ^ 2 - σ ^ 2
  have hl : 0 < l := by dsimp only [l]; nlinarith
  have h1 : σ ^ 2 + l = α ^ 2 := by dsimp only [l]; ring
  have h2 : σ ^ 2 - θ + l = α ^ 2 - θ := by dsimp only [l]; ring
  have h3 : σ ^ 2 + m = β ^ 2 := by dsimp only [m]; ring
  have h4 : σ ^ 2 - θ + m = β ^ 2 - θ := by dsimp only [m]; ring
  have hnum : α * (σ ^ 2 - θ) + σ * (α ^ 2 - θ) = β * l := by
    dsimp only [l]
    linear_combination (α + σ) * hσ
  have hμ : σ ^ 2 + m = (√(σ ^ 2 + l) * (σ ^ 2 - θ) +
      √(σ ^ 2) * (σ ^ 2 - θ + l)) ^ 2 / l ^ 2 := by
    rw [h1, h2, h3, Real.sqrt_sq hα.le, Real.sqrt_sq hs.le, hnum]
    field_simp
  have H := symEllIntRC_add_symEllIntRC (sq_nonneg σ) hy hl hμ
  rw [h1, h2, h3, h4] at H
  exact H

/-- DLMF 19.26.14 with 19.26.15: `(p - y) R_C(x, p) + (q - y) R_C(x, q) = (η - ξ) R_C(ξ, η)`, for
`y ≥ 0`, `p, q ∈ ℝ \ {0}` with `(p - x)(q - x) = (y - x)²`, `ξ = y²/x`, `η = pq/x`. DLMF writes
`x ≥ 0` but divides by `x`; we assume `x > 0`. (`R_C` with a negative second argument is the
Cauchy principal value.) -/
@[dlmf 19.26.E14, dlmf 19.26.E15]
theorem symEllIntRC_addition_pq {x y p q : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hp : p ≠ 0)
    (hq : q ≠ 0) (hpq : (p - x) * (q - x) = (y - x) ^ 2) :
    let ξ := y ^ 2 / x
    let η := p * q / x
    ((p - y : ℝ) : ℂ) * symEllIntRC x p + ((q - y : ℝ) : ℂ) * symEllIntRC x q =
      ((η - ξ : ℝ) : ℂ) * symEllIntRC ξ η := by
  sorry

/-- DLMF 19.26.15 (last equation): `η - ξ = p + q - 2y` under `(p - x)(q - x) = (y - x)²`,
`ξ = y²/x`, `η = pq/x`, `x ≠ 0`. -/
@[dlmf 19.26.E15]
theorem symEllIntRC_addition_eta_sub_xi {x y p q : ℝ} (hx : x ≠ 0)
    (hpq : (p - x) * (q - x) = (y - x) ^ 2) :
    p * q / x - y ^ 2 / x = p + q - 2 * y := by
  field_simp
  linear_combination hpq

/-! ### §19.26(ii) Case `x = 0` -/

/-- DLMF 19.26.17: `√α R_C(β, α + β) + √β R_C(α, α + β) = π/2`, for
`α, β ∈ ℂ \ (-∞, 0)` with `α + β > 0`. -/
@[dlmf 19.26.E17]
theorem symEllIntRC_addition_zero {α β : ℂ} (hα : SymEllIntArg α) (hβ : SymEllIntArg β)
    (hαβ : 0 < (α + β).re) (hαβ' : (α + β).im = 0) :
    α ^ (1 / 2 : ℂ) * symEllIntRC β (α + β) + β ^ (1 / 2 : ℂ) * symEllIntRC α (α + β) = π / 2 := by
  sorry

/-! ### §19.26(iii) Duplication formulas -/

/-- DLMF 19.26.19: `λ = √x √y + √y √z + √z √x` (principal square roots). -/
@[dlmf 19.26.E19]
def symEllIntDupLambda (x y z : ℂ) : ℂ :=
  x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) + y ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) +
    z ^ (1 / 2 : ℂ) * x ^ (1 / 2 : ℂ)

/-- DLMF's `λ` is `lean-codes`' `Carlson.dupLambda`. -/
theorem symEllIntDupLambda_eq_dupLambda (x y z : ℂ) :
    symEllIntDupLambda x y z = Carlson.dupLambda x y z := by
  unfold symEllIntDupLambda Carlson.dupLambda; ring

/-- DLMF 19.26.18 (first equality), **stronger than DLMF**:
`R_F(x, y, z) = 2 R_F(x + λ, y + λ, z + λ)` for all `x, y, z ∈ ℂ \ (-∞, 0]`
(DLMF: positive `x, y, z`). From `lean-codes`' `Carlson.carlsonRF_duplication`. -/
@[dlmf 19.26.E18]
theorem symEllIntRF_duplication {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    symEllIntRF x y z = 2 * symEllIntRF (x + symEllIntDupLambda x y z)
      (y + symEllIntDupLambda x y z) (z + symEllIntDupLambda x y z) := by
  rw [symEllIntDupLambda_eq_dupLambda, symEllIntRF_eq_carlsonRF hx hy hz,
    symEllIntRF_eq_carlsonRF (Carlson.add_dupLambda_mem hx hy hz)
      (by rw [← Carlson.dupLambda_comm_left]; exact Carlson.add_dupLambda_mem hy hx hz)
      (by rw [← Carlson.dupLambda_comm_right, ← Carlson.dupLambda_comm_left]
          exact Carlson.add_dupLambda_mem hz hx hy)]
  exact Carlson.carlsonRF_duplication hx hy hz

/-- DLMF 19.26.18 (first equality) at one vanishing variable:
`R_F(0, y, z) = 2 R_F(λ, y + λ, z + λ)` with `λ = √y √z`, for `y, z ∈ ℂ \ (-∞, 0]`. From
`lean-codes`' `Carlson.carlsonRK_duplication`. Together with `symEllIntRF_duplication` and the
symmetry of `R_F` this covers DLMF's domain (positive variables, at most one zero). -/
@[dlmf 19.26.E18]
theorem symEllIntRF_duplication_zero {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symEllIntRF 0 y z = 2 * symEllIntRF (0 + symEllIntDupLambda 0 y z)
      (y + symEllIntDupLambda 0 y z) (z + symEllIntDupLambda 0 y z) := by
  have hL : symEllIntDupLambda 0 y z = y ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) := by
    simp [symEllIntDupLambda]
  have hm : y ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) ∈ slitPlane :=
    Carlson.mul_mem_slitPlane_of_re_pos (Carlson.re_cpow_half_pos hy) (Carlson.re_cpow_half_pos hz)
  have hadd : ∀ a b : ℂ, a ∈ slitPlane → b ∈ slitPlane →
      a + a ^ (1 / 2 : ℂ) * b ^ (1 / 2 : ℂ) ∈ slitPlane := by
    intro a b ha hb
    have he : a + a ^ (1 / 2 : ℂ) * b ^ (1 / 2 : ℂ) =
        a ^ (1 / 2 : ℂ) * (a ^ (1 / 2 : ℂ) + b ^ (1 / 2 : ℂ)) := by
      linear_combination (-1 : ℂ) * Carlson.cpow_half_sq a
    rw [he]
    refine Carlson.mul_mem_slitPlane_of_re_pos (Carlson.re_cpow_half_pos ha) ?_
    rw [add_re]; linarith [Carlson.re_cpow_half_pos ha, Carlson.re_cpow_half_pos hb]
  have hz' : z + y ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) ∈ slitPlane := by
    rw [mul_comm]; exact hadd z y hz hy
  have hrot : ∀ a b c : ℂ, symEllIntRF a b c = symEllIntRF b c a := fun a b c => by
    rw [symEllIntRF_comm_left, symEllIntRF_comm_right]
  rw [hL, zero_add, hrot (y ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ)),
    ei19d_symEllIntRF_zero_eq_carlsonRK hy hz,
    symEllIntRF_eq_carlsonRF (hadd y z hy hz) hz' hm, Carlson.carlsonRK_duplication hy hz]

/-- Formula under the stated hypotheses: `a / 4 ∈ slitPlane`. -/
lemma ei19d_div_four_mem {a : ℂ} (ha : a ∈ slitPlane) : a / 4 ∈ slitPlane := by
  rw [mem_slitPlane_iff] at ha ⊢
  rcases ha with h | h
  · left; simp only [div_re]; norm_num; positivity
  · right; simp only [div_im]; norm_num; exact h

/-- Identity under the stated parameter and domain assumptions: `((1 / 4 : ℝ) : ℂ) ^ (-1 / 2 : ℂ)
= 2`. -/
lemma ei19d_quarter_cpow : ((1 / 4 : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = 2 := by
  rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have h : (1 / 4 : ℝ) ^ (-1 / 2 : ℝ) = 2 := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow,
      show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  rw [h]; push_cast; ring

/-- DLMF 19.26.18 (second equality), **stronger than DLMF**:
`2 R_F(x + λ, y + λ, z + λ) = R_F((x + λ)/4, (y + λ)/4, (z + λ)/4)` for all
`x, y, z ∈ ℂ \ (-∞, 0]`, by homogeneity (`Carlson.carlsonRF_mul_of_pos`). -/
@[dlmf 19.26.E18]
theorem symEllIntRF_duplication_quarter {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    2 * symEllIntRF (x + symEllIntDupLambda x y z) (y + symEllIntDupLambda x y z)
        (z + symEllIntDupLambda x y z) =
      symEllIntRF ((x + symEllIntDupLambda x y z) / 4) ((y + symEllIntDupLambda x y z) / 4)
        ((z + symEllIntDupLambda x y z) / 4) := by
  rw [symEllIntDupLambda_eq_dupLambda]
  have h1 := Carlson.add_dupLambda_mem hx hy hz
  have h2 : y + Carlson.dupLambda x y z ∈ slitPlane := by
    rw [← Carlson.dupLambda_comm_left]; exact Carlson.add_dupLambda_mem hy hx hz
  have h3 : z + Carlson.dupLambda x y z ∈ slitPlane := by
    rw [← Carlson.dupLambda_comm_right, ← Carlson.dupLambda_comm_left]
    exact Carlson.add_dupLambda_mem hz hx hy
  have hq : ∀ w : ℂ, w / 4 = ((1 / 4 : ℝ) : ℂ) * w := fun w => by push_cast; ring
  rw [symEllIntRF_eq_carlsonRF h1 h2 h3,
    symEllIntRF_eq_carlsonRF (ei19d_div_four_mem h1) (ei19d_div_four_mem h2)
      (ei19d_div_four_mem h3), hq, hq, hq,
    Carlson.carlsonRF_mul_of_pos (by norm_num) h1 h2 h3, ei19d_quarter_cpow]

/-- Differentiating duplication of `R_F` gives duplication of `R_D`, including a zero first
argument. The other two arguments are positive. -/
lemma symEllIntRD_duplication_of_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z) :
    let l := √x * √y + √y * √z + √z * √x
    symEllIntRD x y z = 2 * symEllIntRD ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) +
      ((3 / (√z * (z + l)) : ℝ) : ℂ) := by
  let l : ℝ → ℝ := fun w => √x * √y + √y * √w + √w * √x
  let d := (√x + √y) / (2 * √z)
  have hsx : 0 ≤ √x := Real.sqrt_nonneg _
  have hsy : 0 < √y := Real.sqrt_pos.mpr hy
  have hsz : 0 < √z := Real.sqrt_pos.mpr hz
  have hl (w : ℝ) (hw : 0 < w) : 0 < l w := by dsimp only [l]; positivity
  have hX : 0 < x + l z := by linarith [hl z hz]
  have hY : 0 < y + l z := by linarith [hl z hz]
  have hZ : 0 < z + l z := by linarith [hl z hz]
  have hD : HasDerivAt l d z := by
    have H := (((Real.hasDerivAt_sqrt hz.ne').const_mul (√y)).const_add (√x * √y)).add
      ((Real.hasDerivAt_sqrt hz.ne').mul_const (√x))
    convert H using 1
    dsimp only [d]
    ring
  have HC := (hasDerivAt_carlsonRF_translate_right hD hX hY hZ).const_mul (2 : ℂ)
  have hev : (fun w : ℝ => symEllIntRF x y w) =ᶠ[𝓝 z] fun w : ℝ =>
      2 * Carlson.carlsonRF (x + l w : ℝ) (y + l w : ℝ) (w + l w : ℝ) := by
    filter_upwards [eventually_gt_nhds hz] with w hw
    have hwc := ofReal_mem_slitPlane.mpr hw
    have hyc := ofReal_mem_slitPlane.mpr hy
    have hscale : symEllIntDupLambda x y w = ((l w : ℝ) : ℂ) := by
      unfold symEllIntDupLambda
      rw [Carlson.ofReal_cpow_half hx, Carlson.ofReal_cpow_half hy.le, Carlson.ofReal_cpow_half hw.le]
      dsimp only [l]; push_cast; ring
    have H : symEllIntRF x y w = 2 * symEllIntRF (x + l w : ℝ) (y + l w : ℝ) (w + l w : ℝ) := by
      by_cases hx0 : x = 0
      · subst x
        have H := symEllIntRF_duplication_zero hyc hwc
        simp only [ofReal_zero] at hscale
        rw [hscale] at H
        simpa only [ofReal_zero, zero_add, ← ofReal_add] using H
      · have H := symEllIntRF_duplication
          (ofReal_mem_slitPlane.mpr (lt_of_le_of_ne hx (Ne.symm hx0))) hyc hwc
        rw [hscale] at H
        simpa only [← ofReal_add] using H
    rw [H, symEllIntRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr (by linarith [hl w hw]))
      (ofReal_mem_slitPlane.mpr (by linarith [hl w hw])) (ofReal_mem_slitPlane.mpr (by linarith [hl w hw]))]
  have HE := ((hasDerivAt_symEllIntRF_right_real hx hy hz).congr_of_eventuallyEq hev.symm).unique HC
  rw [← ei19c_inv_cpow_half, ← ei19c_inv_cpow_half, ← ei19c_inv_cpow_half,
    Carlson.ofReal_cpow_half hX.le, Carlson.ofReal_cpow_half hY.le, Carlson.ofReal_cpow_half hZ.le] at HE
  have HR : symEllIntRD x y z = 2 * symEllIntRD (x + l z : ℝ) (y + l z : ℝ) (z + l z : ℝ) +
      ((6 * d * (√(x + l z) * √(y + l z) * √(z + l z))⁻¹ : ℝ) : ℂ) := by
    push_cast at HE ⊢
    simp only [mul_inv_rev]
    linear_combination (-6 : ℂ) * HE
  have hA : 0 < √x + √y := by positivity
  have hB : 0 < √x + √z := by positivity
  have hC : 0 < √y + √z := by positivity
  have heX : x + l z = (√x + √y) * (√x + √z) := by
    dsimp only [l]; nlinarith [Real.sq_sqrt hx]
  have heY : y + l z = (√x + √y) * (√y + √z) := by
    dsimp only [l]; nlinarith [Real.sq_sqrt hy.le]
  have heZ : z + l z = (√x + √z) * (√y + √z) := by
    dsimp only [l]; nlinarith [Real.sq_sqrt hz.le]
  have hS : √(x + l z) * √(y + l z) * √(z + l z) = (√x + √y) * (z + l z) := by
    rw [heX, heY, heZ, Real.sqrt_mul hA.le, Real.sqrt_mul hA.le, Real.sqrt_mul hB.le]
    calc _ = Real.sqrt (√x + √y) ^ 2 * Real.sqrt (√x + √z) ^ 2 * Real.sqrt (√y + √z) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hA.le, Real.sq_sqrt hB.le, Real.sq_sqrt hC.le]; ring
  have hcorr : 6 * d * (√(x + l z) * √(y + l z) * √(z + l z))⁻¹ = 3 / (√z * (z + l z)) := by
    rw [hS]
    dsimp only [d]
    field_simp
    ring
  change symEllIntRD x y z = 2 * symEllIntRD (x + l z : ℝ) (y + l z : ℝ) (z + l z : ℝ) + _
  rw [HR, hcorr]

/-- DLMF 19.26.20: `R_D(x, y, z) = 2 R_D(x + λ, y + λ, z + λ) + 3/(√z (z + λ))`, `λ` as in
(19.26.19), under the standing assumptions with `z > 0`. -/
@[dlmf 19.26.E20]
theorem symEllIntRD_duplication {x y z : ℝ} (h : Ei19dPosDomain x y z) (hz : 0 < z) :
    let l := √x * √y + √y * √z + √z * √x
    symEllIntRD x y z = 2 * symEllIntRD ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) +
      ((3 / (√z * (z + l)) : ℝ) : ℂ) := by
  rcases h with ⟨hx, hy, _, hx0, hy0⟩
  by_cases hyz : y = 0
  · subst y
    have hx' : 0 < x := by
      by_contra hh
      have hxx : x = 0 := by linarith
      exact (hx0 hxx).1.ne' rfl
    have H := symEllIntRD_duplication_of_nonneg (x := (0 : ℝ)) (by norm_num) hx' hz
    simp only [Real.sqrt_zero, zero_mul, mul_zero, zero_add, add_zero] at H
    simpa only [ofReal_zero, symEllIntRD_comm, Real.sqrt_zero, zero_mul, mul_zero,
      zero_add, add_zero, mul_comm] using H
  · have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm hyz)
    exact symEllIntRD_duplication_of_nonneg hx hy' hz


/-- The real duplication formula for `R_G` with the last two arguments positive. -/
lemma symEllIntRG_duplication_of_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z) :
    let l := √x * √y + √y * √z + √z * √x
    2 * symEllIntRG x y z = 4 * symEllIntRG ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) -
      l * symEllIntRF x y z - √x - √y - √z := by
  let l := √x * √y + √y * √z + √z * √x
  have hl : 0 < l := by dsimp only [l]; positivity
  have hX : 0 < x + l := by linarith
  have hY : 0 < y + l := by linarith
  have hZ : 0 < z + l := by linarith
  have hsz : 0 < √z := Real.sqrt_pos.mpr hz
  have hsZ : 0 < √(z + l) := Real.sqrt_pos.mpr hZ
  have hA : 0 < √x + √y := by positivity
  have heX : x + l = (√x + √y) * (√x + √z) := by
    dsimp only [l]; nlinarith [Real.sq_sqrt hx]
  have heY : y + l = (√x + √y) * (√y + √z) := by
    dsimp only [l]; nlinarith [Real.sq_sqrt hy.le]
  have heZ : z + l = (√x + √z) * (√y + √z) := by
    dsimp only [l]; nlinarith [Real.sq_sqrt hz.le]
  have hprod : √(x + l) * √(y + l) = (√x + √y) * √(z + l) := by
    apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg hA.le (Real.sqrt_nonneg _))).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt hX.le, Real.sq_sqrt hY.le, Real.sq_sqrt hZ.le]
    rw [heX, heY, heZ]
    ring
  have hratio : √(x + l) * √(y + l) / √(z + l) = √x + √y := by
    rw [hprod, mul_div_cancel_right₀ _ hsZ.ne']
  have hdif : (x - z) * (y - z) = (√x - √z) * (√y - √z) * (z + l) := by
    calc _ = (√x ^ 2 - √z ^ 2) * (√y ^ 2 - √z ^ 2) := by
           rw [Real.sq_sqrt hx, Real.sq_sqrt hy.le, Real.sq_sqrt hz.le]
         _ = _ := by rw [heZ]; ring
  have hscalar : -√x * √y / √z + 2 * (√(x + l) * √(y + l) / √(z + l)) +
      (x - z) * (y - z) / (√z * (z + l)) = √x + √y + √z := by
    rw [hratio, hdif]
    field_simp
    nlinarith [Real.sq_sqrt hz.le]
  have hxC : SymEllIntArg (x : ℂ) := by
    by_cases h : x = 0
    · exact Or.inr (by simp [h])
    · exact Or.inl (ofReal_mem_slitPlane.mpr (lt_of_le_of_ne hx (Ne.symm h)))
  have hG := p19sR1_two_mul_symEllIntRG hxC (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz)
  have hGs := p19sR1_two_mul_symEllIntRG (Or.inl (ofReal_mem_slitPlane.mpr hX))
    (ofReal_mem_slitPlane.mpr hY) (ofReal_mem_slitPlane.mpr hZ)
  rw [← ei19c_inv_cpow_half, Carlson.ofReal_cpow_half hx, Carlson.ofReal_cpow_half hy.le,
    Carlson.ofReal_cpow_half hz.le] at hG
  rw [← ei19c_inv_cpow_half, Carlson.ofReal_cpow_half hX.le, Carlson.ofReal_cpow_half hY.le,
    Carlson.ofReal_cpow_half hZ.le] at hGs
  have hscale : symEllIntDupLambda x y z = (l : ℂ) := by
    unfold symEllIntDupLambda
    rw [Carlson.ofReal_cpow_half hx, Carlson.ofReal_cpow_half hy.le, Carlson.ofReal_cpow_half hz.le]
    dsimp only [l]; push_cast; ring
  have hRF : symEllIntRF x y z = 2 * symEllIntRF (x + l : ℝ) (y + l : ℝ) (z + l : ℝ) := by
    by_cases hx0 : x = 0
    · subst x
      have H := symEllIntRF_duplication_zero (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz)
      simp only [ofReal_zero] at hscale
      rw [hscale] at H
      simpa only [ofReal_zero, zero_add, ← ofReal_add] using H
    · have H := symEllIntRF_duplication
        (ofReal_mem_slitPlane.mpr (lt_of_le_of_ne hx (Ne.symm hx0)))
        (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz)
      rw [hscale] at H
      simpa only [← ofReal_add] using H
  have hRD := symEllIntRD_duplication_of_nonneg hx hy hz
  change symEllIntRD x y z = 2 * symEllIntRD (x + l : ℝ) (y + l : ℝ) (z + l : ℝ) +
    ((3 / (√z * (z + l)) : ℝ) : ℂ) at hRD
  have hSC := congrArg (fun r : ℝ => (r : ℂ)) hscalar
  change 2 * symEllIntRG x y z = 4 * symEllIntRG (x + l : ℝ) (y + l : ℝ) (z + l : ℝ) -
    l * symEllIntRF x y z - √x - √y - √z
  push_cast at hG hGs hRF hRD hSC ⊢
  simp only [div_eq_mul_inv, mul_inv_rev] at hSC hRD
  linear_combination hG - 2 * hGs + ((z : ℂ) + l) * hRF -
    (1 / 3 : ℂ) * ((x : ℂ) - z) * ((y : ℂ) - z) * hRD - hSC

/-- DLMF 19.26.21: `2 R_G(x, y, z) = 4 R_G(x + λ, y + λ, z + λ) - λ R_F(x, y, z) - √x - √y - √z`,
`λ` as in (19.26.19), under the standing assumptions. -/
@[dlmf 19.26.E21]
theorem symEllIntRG_duplication {x y z : ℝ} (h : Ei19dPosDomain x y z) :
    let l := √x * √y + √y * √z + √z * √x
    2 * symEllIntRG x y z = 4 * symEllIntRG ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) -
      l * symEllIntRF x y z - √x - √y - √z := by
  rcases h with ⟨hx, hy, hz, hx0, hy0⟩
  by_cases hz0 : z = 0
  · subst z
    have hx' : 0 < x := by
      by_contra hh
      have hxx : x = 0 := by linarith
      exact (hx0 hxx).2.ne' rfl
    have hy' : 0 < y := by
      by_contra hh
      have hyy : y = 0 := by linarith
      exact (hy0 hyy).ne' rfl
    have H := symEllIntRG_duplication_of_nonneg (x := (0 : ℝ)) (by norm_num) hx' hy'
    simp only [Real.sqrt_zero, zero_mul, mul_zero, zero_add, add_zero] at H ⊢
    simpa only [ofReal_zero, sub_zero, symEllIntRG_comm_left, symEllIntRG_comm_right,
      symEllIntRF_comm_left, symEllIntRF_comm_right, add_comm, add_left_comm, add_assoc, mul_comm] using H
  · have hz' : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    by_cases hyz : y = 0
    · subst y
      have hx' : 0 < x := by
        by_contra hh
        have hxx : x = 0 := by linarith
        exact (hx0 hxx).1.ne' rfl
      have H := symEllIntRG_duplication_of_nonneg (x := (0 : ℝ)) (by norm_num) hx' hz'
      simp only [Real.sqrt_zero, zero_mul, mul_zero, zero_add, add_zero] at H ⊢
      simpa only [ofReal_zero, sub_zero, symEllIntRG_comm_left, symEllIntRF_comm_left,
        add_comm, add_left_comm, add_assoc, mul_comm] using H
    · exact symEllIntRG_duplication_of_nonneg hx (lt_of_le_of_ne hy (Ne.symm hyz)) hz'

/-- DLMF 19.26.22 with 19.26.23: `R_J(x, y, z, p) = 2 R_J(x + λ, y + λ, z + λ, p + λ)
+ 3 R_C(α², β²)`, `α = p(√x + √y + √z) + √x√y√z`, `β = √p (p + λ)`, `λ` as in (19.26.19),
under the standing assumptions and `p > 0`. -/
@[dlmf 19.26.E22, dlmf 19.26.E23]
theorem symEllIntRJ_duplication {x y z p : ℝ} (h : Ei19dPosDomain x y z) (hp : 0 < p) :
    let l := √x * √y + √y * √z + √z * √x
    let α := p * (√x + √y + √z) + √x * √y * √z
    let β := √p * (p + l)
    symEllIntRJ x y z p = 2 * symEllIntRJ ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ)
      ((p + l : ℝ) : ℂ) + 3 * symEllIntRC ((α ^ 2 : ℝ) : ℂ) ((β ^ 2 : ℝ) : ℂ) := by
  sorry

/-- DLMF 19.26.23 (identities): with `α, β` as in (19.26.23),
`β ± α = (√p ± √x)(√p ± √y)(√p ± √z)` (either sign throughout) and
`β² - α² = (p - x)(p - y)(p - z)`, for `x, y, z, p ≥ 0`. -/
@[dlmf 19.26.E23]
theorem symEllIntRJ_duplication_alpha_beta {x y z p : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hp : 0 ≤ p) :
    let l := √x * √y + √y * √z + √z * √x
    let α := p * (√x + √y + √z) + √x * √y * √z
    let β := √p * (p + l)
    β + α = (√p + √x) * (√p + √y) * (√p + √z) ∧ β - α = (√p - √x) * (√p - √y) * (√p - √z) ∧
      β ^ 2 - α ^ 2 = (p - x) * (p - y) * (p - z) := by
  have hP := Real.sq_sqrt hp
  have hX := Real.sq_sqrt hx
  have hY := Real.sq_sqrt hy
  have hZ := Real.sq_sqrt hz
  have h1 : √p * (p + (√x * √y + √y * √z + √z * √x)) + (p * (√x + √y + √z) + √x * √y * √z) =
      (√p + √x) * (√p + √y) * (√p + √z) := by
    linear_combination (-(√p) - √x - √y - √z) * hP
  have h2 : √p * (p + (√x * √y + √y * √z + √z * √x)) - (p * (√x + √y + √z) + √x * √y * √z) =
      (√p - √x) * (√p - √y) * (√p - √z) := by
    linear_combination (-(√p) + √x + √y + √z) * hP
  refine ⟨h1, h2, ?_⟩
  rw [sq_sub_sq, h1, h2]
  conv_rhs => rw [← hP, ← hX, ← hY, ← hZ]
  ring

/-- DLMF 19.26.24: the inverse of `z + λ = (√z + √x)(√z + √y)` (and its permutations):
`z = (ξζ + ηζ - ξη)²/(4ξηζ)`, `(ξ, η, ζ) = (x + λ, y + λ, z + λ)`, `λ` as in (19.26.19), for
`x, y, z ≥ 0` at most one of them `0`; the formulas for `x`, `y` follow by permutation. -/
@[dlmf 19.26.E24]
theorem symEllInt_duplication_inverse {x y z : ℝ} (h : Ei19dPosDomain x y z) :
    let l := √x * √y + √y * √z + √z * √x
    let ξ := x + l; let η := y + l; let ζ := z + l
    z = (ξ * ζ + η * ζ - ξ * η) ^ 2 / (4 * ξ * η * ζ) := by
  intro l ξ η ζ
  obtain ⟨hx, hy, hz, h0x, h0y⟩ := h
  have ha := Real.sq_sqrt hx
  have hb := Real.sq_sqrt hy
  have hc := Real.sq_sqrt hz
  have pos : ∀ {u v : ℝ}, 0 ≤ u → 0 ≤ v → (u = 0 → v ≠ 0) → 0 < √u + √v := by
    intro u v hu hv huv
    rcases hu.eq_or_lt with hu0 | hu0
    · have := huv hu0.symm
      have : 0 < √v := Real.sqrt_pos.mpr (lt_of_le_of_ne hv (Ne.symm this))
      positivity
    · have : 0 < √u := Real.sqrt_pos.mpr hu0
      positivity
  have hab : 0 < √x + √y := pos hx hy (fun h => (h0x h).1.ne')
  have hac : 0 < √x + √z := pos hx hz (fun h => (h0x h).2.ne')
  have hbc : 0 < √y + √z := pos hy hz (fun h => (h0y h).ne')
  have e1 : ξ = (√x + √y) * (√x + √z) := by
    simp only [ξ, l]; linear_combination -ha
  have e2 : η = (√x + √y) * (√y + √z) := by
    simp only [η, l]; linear_combination -hb
  have e3 : ζ = (√x + √z) * (√y + √z) := by
    simp only [ζ, l]; linear_combination -hc
  set K := (√x + √y) * (√x + √z) * (√y + √z)
  have hK : K ≠ 0 := by positivity
  have hN : ξ * ζ + η * ζ - ξ * η = 2 * √z * K := by rw [e1, e2, e3]; ring
  have hD : 4 * ξ * η * ζ = 4 * K ^ 2 := by rw [e1, e2, e3]; ring
  rw [hN, hD, show (2 * √z * K) ^ 2 / (4 * K ^ 2) = √z ^ 2 by field_simp; ring, hc]

/-- DLMF 19.26.25: `R_C(x, y) = 2 R_C(x + λ, y + λ)`, `λ = y + 2√x√y`, for `x ≥ 0`, `y > 0`. -/
@[dlmf 19.26.E25]
theorem symEllIntRC_duplication {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    let l := y + 2 * √x * √y
    symEllIntRC x y = 2 * symEllIntRC ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) := by
  let l := y + 2 * √x * √y
  have hl : 0 < l := by dsimp [l]; positivity
  have hnn (r : ℝ) (hr : 0 < r) : ¬ IsNegReal (r : ℂ) :=
    ei19c_not_isNegReal_of_mem_slitPlane (ofReal_mem_slitPlane.mpr hr)
  have hroot (r : ℝ) (hr : 0 ≤ r) : (r : ℂ) ^ (1 / 2 : ℂ) = (√r : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hr, ← Real.sqrt_eq_rpow]
  have hdup : symEllIntDupLambda (x : ℂ) y y = (l : ℂ) := by
    unfold symEllIntDupLambda
    rw [hroot x hx, hroot y hy.le]
    dsimp [l]
    have hy2 : (√y : ℂ) * √y = (y : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt hy.le
    rw [hy2]
    push_cast
    ring
  change symEllIntRC x y = 2 * symEllIntRC ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ)
  rw [symEllIntRC_eq_symEllIntRF _ (hnn y hy),
    symEllIntRC_eq_symEllIntRF _ (hnn (y + l) (by linarith))]
  by_cases hx0 : x = 0
  · subst x
    have h := symEllIntRF_duplication_zero (ofReal_mem_slitPlane.mpr hy)
      (ofReal_mem_slitPlane.mpr hy)
    change symEllIntDupLambda 0 (y : ℂ) y = (l : ℂ) at hdup
    rw [hdup] at h
    simpa only [zero_add, Complex.ofReal_add, ofReal_zero] using h
  · have h := symEllIntRF_duplication (ofReal_mem_slitPlane.mpr (lt_of_le_of_ne hx (Ne.symm hx0)))
      (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hy)
    simpa only [hdup, ← Complex.ofReal_add] using h

/-- DLMF 19.26.26: `R_C(x², y²) = R_C(a², a y)`, `a = (x + y)/2`, for
`x = 0` or `ℜ x > 0`, and `ℜ y > 0`. The first squared argument must avoid the negative
real cut; a nonzero purely imaginary `x` is outside this domain. -/
@[dlmf 19.26.E26]
theorem symEllIntRC_sq_eq {x y : ℂ} (hx : x = 0 ∨ 0 < x.re) (hy : 0 < y.re) :
    symEllIntRC (x ^ 2) (y ^ 2) = symEllIntRC (((x + y) / 2) ^ 2) ((x + y) / 2 * y) := by
  have hy2 : y ^ 2 ∈ slitPlane := by
    simpa only [pow_two] using Carlson.mul_mem_slitPlane_of_re_pos hy hy
  have hy0 : y ≠ 0 := slitPlane_ne_zero (Or.inl hy)
  have ha : 0 < ((x + y) / 2).re := by rcases hx with rfl | hx <;> simp only [add_re, div_ofNat_re, zero_re] <;> linarith
  have ha2 : ((x + y) / 2) ^ 2 ∈ slitPlane := by
    simpa only [pow_two] using Carlson.mul_mem_slitPlane_of_re_pos ha ha
  have hay : (x + y) / 2 * y ∈ slitPlane := Carlson.mul_mem_slitPlane_of_re_pos ha hy
  rcases hx with rfl | hx
  · simp only [zero_pow two_ne_zero, zero_add] at *
    have hleft : symEllIntRC 0 (y ^ 2) = (π / 2) * y⁻¹ := by
      rw [symEllIntRC_eq_symEllIntRF _ (ei19c_not_isNegReal_of_mem_slitPlane hy2),
        symEllIntRF_zero_left hy2 hy2]
      have hv : (![y ^ 2, y ^ 2] : Fin 2 → ℂ) = fun _ => y ^ 2 := by
        funext i; fin_cases i <;> rfl
      rw [hv, symEllIntR_const _ _ hy2 (Gamma_ne_zero_of_re_pos (by norm_num))]
      rw [show -(1 / 2 : ℂ) = -(2⁻¹) by norm_num, cpow_neg, sq_cpow_two_inv hy]
    have hμarg : ∀ i : Fin 2, arg ((y / 2) ^ 2) + arg ((![1, 2] : Fin 2 → ℂ) i) ∈ Ioo (-π) π := by
      intro i
      have harg2 : arg (2 : ℂ) = 0 := arg_ofReal_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      fin_cases i
      · change arg ((y / 2) ^ 2) + arg 1 ∈ Ioo (-π) π
        rw [arg_one, add_zero]
        exact ⟨neg_pi_lt_arg _, lt_of_le_of_ne (arg_le_pi _) (mem_slitPlane_iff_arg.mp ha2).1⟩
      · change arg ((y / 2) ^ 2) + arg 2 ∈ Ioo (-π) π
        rw [harg2, add_zero]
        exact ⟨neg_pi_lt_arg _, lt_of_le_of_ne (arg_le_pi _) (mem_slitPlane_iff_arg.mp ha2).1⟩
    have htwo : (2 : ℂ) ∈ slitPlane := Or.inl (by norm_num)
    have H := symEllIntR_mul (1 / 2) ![1 / 2, 1]
      (ei19c_slit2 one_mem_slitPlane htwo) ha2 hμarg
    have hv : (fun i => (y / 2) ^ 2 * (![1, 2] : Fin 2 → ℂ) i) = ![(y / 2) ^ 2, y / 2 * y] := by
      funext i; fin_cases i <;> simp; ring
    rw [hv, ← symEllIntRC_eq_symEllIntR ha2 hay,
      ← symEllIntRC_eq_symEllIntR one_mem_slitPlane htwo,
      symEllIntRC_eq_carlsonRC one_mem_slitPlane htwo] at H
    have hconst := Carlson.TwoVariable.pi_eq_four_mul_carlsonRC.1
    have hhalf : ((y / 2) ^ 2) ^ (-(1 / 2) : ℂ) = (y / 2)⁻¹ := by
      rw [show -(1 / 2 : ℂ) = -(2⁻¹) by norm_num, cpow_neg, sq_cpow_two_inv (by simpa only [div_ofNat_re] using (half_pos hy))]
    rw [hhalf] at H
    rw [hleft, H]
    field_simp
    linear_combination hconst
  · rw [symEllIntRC_eq_carlsonRC
      (by simpa only [pow_two] using Carlson.mul_mem_slitPlane_of_re_pos hx hx) hy2,
      symEllIntRC_eq_carlsonRC ha2 hay]
    exact Carlson.TwoVariable.carlsonRC_sq_eq x y hx hy

/-- DLMF 19.26.27: `R_C(x², x² - θ) = 2 R_C(s², s² - θ)`, `s = x + √(x² - θ)`, `θ ≠ x², s²`.
**Corrected from the printed DLMF formula**: we also assume `ℜ x > 0` and
`x² - θ ∈ ℂ \ (-∞, 0]`. DLMF's conditions do not suffice: the identity fails for `x = -2`,
`θ = -3` (the left side depends on `x²` only), and for `x = 1`, `θ = 2`, where the left side is
a Cauchy principal value (19.2.20) but the right side is not (they differ by `-π i/(2√θ)`).
The proof reuses lean-codes' `Carlson.TwoVariable.carlsonRC_sq_eq` and
`Carlson.TwoVariable.carlsonRC_mul_of_pos`.
Checked numerically at 3000 random complex points under the stated hypotheses. -/
@[dlmf 19.26.E27]
theorem symEllIntRC_duplication_theta {x θ : ℂ} (hx : 0 < x.re)
    (hθx : x ^ 2 - θ ∈ slitPlane) :
    let s := x + (x ^ 2 - θ) ^ (1 / 2 : ℂ)
    symEllIntRC (x ^ 2) (x ^ 2 - θ) = 2 * symEllIntRC (s ^ 2) (s ^ 2 - θ) := by
  let y := (x ^ 2 - θ) ^ (1 / 2 : ℂ)
  have hy : 0 < y.re := Carlson.re_cpow_half_pos hθx
  have hy2 : y ^ 2 = x ^ 2 - θ := by
    dsimp only [y]
    rw [pow_two, ei19c_cpow_half_sq]
  have hs : 0 < (x + y).re := by simp only [add_re]; linarith
  have ha : 0 < ((x + y) / 2).re := by simp only [div_ofNat_re]; linarith
  have he : (x + y) ^ 2 - θ = (x + y) * (2 * y) := by linear_combination -hy2
  have h1 := Carlson.TwoVariable.carlsonRC_sq_eq x y hx hy
  rw [hy2] at h1
  have hscale := Carlson.TwoVariable.carlsonRC_mul_of_pos (l := (1 / 4 : ℝ))
    (x := (x + y) ^ 2) (y := (x + y) ^ 2 - θ)
    (by norm_num) (by simpa only [pow_two] using Carlson.mul_mem_slitPlane_of_re_pos hs hs)
    (he ▸ Carlson.mul_mem_slitPlane_of_re_pos hs (by simp [hy]))
  have hsarg : ((1 / 4 : ℝ) : ℂ) * (x + y) ^ 2 = ((x + y) / 2) ^ 2 := by push_cast; ring
  have hsarg2 : ((1 / 4 : ℝ) : ℂ) * ((x + y) ^ 2 - θ) = (x + y) / 2 * y := by
    rw [he]; push_cast; ring
  rw [hsarg, hsarg2, ei19d_quarter_cpow] at hscale
  change symEllIntRC (x ^ 2) (x ^ 2 - θ) =
    2 * symEllIntRC ((x + y) ^ 2) ((x + y) ^ 2 - θ)
  have hright := he ▸ Carlson.mul_mem_slitPlane_of_re_pos hs (by simp [hy])
  rw [symEllIntRC_eq_carlsonRC
      (by simpa only [pow_two] using Carlson.mul_mem_slitPlane_of_re_pos hx hx) hθx,
    symEllIntRC_eq_carlsonRC
      (by simpa only [pow_two] using Carlson.mul_mem_slitPlane_of_re_pos hs hs) hright]
  exact h1.trans hscale

end DLMF.EllipticIntegrals
