/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Symmetric
public import Carlson.Elliptic.Addition
public import Carlson.Elliptic.ZeroVariable
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Addition theorems for the symmetric elliptic integrals (DLMF §19.26)

* §19.26(i): the addition theorems (19.26.1), (19.26.7), (19.26.8), (19.26.9) for `R_F`, `R_D`,
  `R_G`, `R_J`, with Euler's algebraic relation between `λ` and `μ` in the forms (19.26.2),
  (19.26.3), (19.26.5), (19.26.6); the addition theorem (19.26.11)–(19.26.12) of `R_C` and its
  equivalent forms (19.26.13)–(19.26.15). DLMF's standing assumption (19.26.i.p1): `λ, x, y, z`
  are positive, except that at most one of `x, y, z` can be `0` (`ei19d_posDomain`).
* §19.26(ii): the case `x = 0`, where `λμ = yz` (19.26.ii.p1), (19.26.16), (19.26.17).
* §19.26(iii): the duplication formulas (19.26.18)–(19.26.27), with
  `λ = √x√y + √y√z + √z√x` (19.26.19, `symEllIntDupLambda`).

Proved here from `lean-codes`: the duplication theorem (19.26.18) on the whole slit plane
(**stronger than DLMF**; `Carlson.carlsonRF_duplication`) and at one zero variable
(`Carlson.carlsonRK_duplication`), the addition theorem with `x = 0` (19.26.16;
`Carlson.carlsonRF_add_carlsonRF_zero`), and the algebraic identities (19.26.2) (permuted forms),
(19.26.4) (the note), (19.26.5), (19.26.12), (19.26.23) and (19.26.24).

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

open Complex Set
open scoped Real

namespace DLMF.EllipticIntegrals

/-- DLMF 19.26.i.p1: the standing assumption of §19.26: `x, y, z ≥ 0`, at most one of them `0`
(and `λ > 0`, assumed separately). -/
def ei19d_posDomain (x y z : ℝ) : Prop :=
  0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ (x = 0 → 0 < y ∧ 0 < z) ∧ (y = 0 → 0 < z)

/-! ### §19.26(i) General formulas -/

theorem ei19d_sqrt_mul3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (_hc : 0 ≤ c) :
    √(a * b * c) = √a * √b * √c := by
  rw [Real.sqrt_mul (mul_nonneg ha hb), Real.sqrt_mul ha]

theorem ei19d_perm_alg {a b c A B C l m : ℝ} (hA : A ^ 2 = a ^ 2 + l) (hB : B ^ 2 = b ^ 2 + l)
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
theorem symEllInt_addition_mu_perm {x y z l m : ℝ} (h : ei19d_posDomain x y z) (hl : 0 < l)
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

/-- DLMF 19.26.3 with 19.26.4: with `(ξ, η, ζ) = (x + λ, y + λ, z + λ)` and
`(ξ', η', ζ') = (x + μ, y + μ, z + μ)`, `√z = (ξζ' + η'ζ - ξη')/(√(ξηζ') + √(ξ'η'ζ))` (and the
permuted formulas for `√x`, `√y`). -/
@[dlmf 19.26.E3, dlmf 19.26.E4]
theorem symEllInt_addition_sqrt_z {x y z l m : ℝ} (h : ei19d_posDomain x y z) (hl : 0 < l)
    (hm : 0 < m)
    (hμ : x + m = (√((x + l) * y * z) + √(x * (y + l) * (z + l))) ^ 2 / l ^ 2) :
    let ξ := x + l; let η := y + l; let ζ := z + l
    let ξ' := x + m; let η' := y + m; let ζ' := z + m
    √z = (ξ * ζ' + η' * ζ - ξ * η') / (√(ξ * η * ζ') + √(ξ' * η' * ζ)) := by
  sorry

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

theorem ei19d_addition_core {x y z l m : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hl : 0 < l)
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
theorem symEllInt_addition_mu_iff {x y z l m : ℝ} (h : ei19d_posDomain x y z) (hl : 0 < l) :
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
theorem symEllInt_addition_quadratic {x y z l m : ℝ} (h : ei19d_posDomain x y z) (hl : 0 < l)
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

theorem ei19d_addition_pos {x y z l m : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hl : 0 < l)
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

theorem ei19d_addition_of_first {x y z l m : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z)
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
theorem symEllIntRF_add_symEllIntRF {x y z l m : ℝ} (h : ei19d_posDomain x y z) (hl : 0 < l)
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


/-- DLMF 19.26.7: `R_D(x + λ, y + λ, z + λ) + R_D(x + μ, y + μ, z + μ)
= R_D(x, y, z) - 3/√(z (z + λ)(z + μ))`, with `λ, μ` as in (19.26.1)–(19.26.2) and `z > 0`
(`R_D`'s third argument is nonzero). -/
@[dlmf 19.26.E7]
theorem symEllIntRD_add_symEllIntRD {x y z l m : ℝ} (h : ei19d_posDomain x y z) (hz : 0 < z)
    (hl : 0 < l) (hm : 0 < m)
    (hμ : x + m = (√((x + l) * y * z) + √(x * (y + l) * (z + l))) ^ 2 / l ^ 2) :
    symEllIntRD ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) +
        symEllIntRD ((x + m : ℝ) : ℂ) ((y + m : ℝ) : ℂ) ((z + m : ℝ) : ℂ) =
      symEllIntRD x y z - ((3 / √(z * (z + l) * (z + m)) : ℝ) : ℂ) := by
  sorry

/-- DLMF 19.26.8: `2R_G(x + λ, …) + 2R_G(x + μ, …) = 2R_G(x, y, z) + λ R_F(x + λ, …)
+ μ R_F(x + μ, …) + √(λ + μ + x + y + z)`, with `λ, μ` as in (19.26.1)–(19.26.2). -/
@[dlmf 19.26.E8]
theorem symEllIntRG_add_symEllIntRG {x y z l m : ℝ} (h : ei19d_posDomain x y z) (hl : 0 < l)
    (hm : 0 < m)
    (hμ : x + m = (√((x + l) * y * z) + √(x * (y + l) * (z + l))) ^ 2 / l ^ 2) :
    2 * symEllIntRG ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) +
        2 * symEllIntRG ((x + m : ℝ) : ℂ) ((y + m : ℝ) : ℂ) ((z + m : ℝ) : ℂ) =
      2 * symEllIntRG x y z +
        l * symEllIntRF ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) +
        m * symEllIntRF ((x + m : ℝ) : ℂ) ((y + m : ℝ) : ℂ) ((z + m : ℝ) : ℂ) +
        ((√(l + m + x + y + z) : ℝ) : ℂ) := by
  sorry

/-- DLMF 19.26.9 with 19.26.10: `R_J(x + λ, y + λ, z + λ, p + λ) + R_J(x + μ, y + μ, z + μ, p + μ)
= R_J(x, y, z, p) - 3 R_C(γ - δ, γ)`, `γ = p(p + λ)(p + μ)`, `δ = (p - x)(p - y)(p - z)`, with
`λ, μ` as in (19.26.1)–(19.26.2) and `p > 0` (the identity fails for `p < 0`). -/
@[dlmf 19.26.E9, dlmf 19.26.E10]
theorem symEllIntRJ_add_symEllIntRJ {x y z p l m : ℝ} (h : ei19d_posDomain x y z) (hp : 0 < p)
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
  sorry

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
    (hα₁ : 0 < α ^ 2 - θ) (hα₂ : α ^ 2 - θ < α ^ 2) (hβ₁ : 0 < β ^ 2 - θ) (hβ₂ : β ^ 2 - θ < β ^ 2)
    (hσ₁ : 0 ≤ ((α * β + θ) / (α + β)) ^ 2 - θ)
    (hσ₂ : ((α * β + θ) / (α + β)) ^ 2 - θ < ((α * β + θ) / (α + β)) ^ 2) :
    let σ := (α * β + θ) / (α + β)
    symEllIntRC ((α ^ 2 : ℝ) : ℂ) ((α ^ 2 - θ : ℝ) : ℂ) + symEllIntRC ((β ^ 2 : ℝ) : ℂ)
        ((β ^ 2 - θ : ℝ) : ℂ) =
      symEllIntRC ((σ ^ 2 : ℝ) : ℂ) ((σ ^ 2 - θ : ℝ) : ℂ) := by
  sorry

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
theorem symEllIntRC_addition_zero {α β : ℂ} (hα : symEllIntArg α) (hβ : symEllIntArg β)
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

theorem ei19d_div_four_mem {a : ℂ} (ha : a ∈ slitPlane) : a / 4 ∈ slitPlane := by
  rw [mem_slitPlane_iff] at ha ⊢
  rcases ha with h | h
  · left; simp only [div_re]; norm_num; positivity
  · right; simp only [div_im]; norm_num; exact h

theorem ei19d_quarter_cpow : ((1 / 4 : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = 2 := by
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

/-- DLMF 19.26.20: `R_D(x, y, z) = 2 R_D(x + λ, y + λ, z + λ) + 3/(√z (z + λ))`, `λ` as in
(19.26.19), under the standing assumptions with `z > 0`. -/
@[dlmf 19.26.E20]
theorem symEllIntRD_duplication {x y z : ℝ} (h : ei19d_posDomain x y z) (hz : 0 < z) :
    let l := √x * √y + √y * √z + √z * √x
    symEllIntRD x y z = 2 * symEllIntRD ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) +
      ((3 / (√z * (z + l)) : ℝ) : ℂ) := by
  sorry

/-- DLMF 19.26.21: `2 R_G(x, y, z) = 4 R_G(x + λ, y + λ, z + λ) - λ R_F(x, y, z) - √x - √y - √z`,
`λ` as in (19.26.19), under the standing assumptions. -/
@[dlmf 19.26.E21]
theorem symEllIntRG_duplication {x y z : ℝ} (h : ei19d_posDomain x y z) :
    let l := √x * √y + √y * √z + √z * √x
    2 * symEllIntRG x y z = 4 * symEllIntRG ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) -
      l * symEllIntRF x y z - √x - √y - √z := by
  sorry

/-- DLMF 19.26.22 with 19.26.23: `R_J(x, y, z, p) = 2 R_J(x + λ, y + λ, z + λ, p + λ)
+ 3 R_C(α², β²)`, `α = p(√x + √y + √z) + √x√y√z`, `β = √p (p + λ)`, `λ` as in (19.26.19),
under the standing assumptions and `p > 0`. -/
@[dlmf 19.26.E22, dlmf 19.26.E23]
theorem symEllIntRJ_duplication {x y z p : ℝ} (h : ei19d_posDomain x y z) (hp : 0 < p) :
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
theorem symEllInt_duplication_inverse {x y z : ℝ} (h : ei19d_posDomain x y z) :
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
  sorry

/-- DLMF 19.26.26: `R_C(x², y²) = R_C(a², a y)`, `a = (x + y)/2`, `ℜ x ≥ 0`, `ℜ y > 0`. -/
@[dlmf 19.26.E26]
theorem symEllIntRC_sq_eq {x y : ℂ} (hx : 0 ≤ x.re) (hy : 0 < y.re) :
    symEllIntRC (x ^ 2) (y ^ 2) = symEllIntRC (((x + y) / 2) ^ 2) ((x + y) / 2 * y) := by
  sorry

/-- DLMF 19.26.27: `R_C(x², x² - θ) = 2 R_C(s², s² - θ)`, `s = x + √(x² - θ)`, `θ ≠ x², s²`.
**Corrected from the printed DLMF formula**: we also assume `ℜ x > 0` and
`x² - θ ∈ ℂ \ (-∞, 0]`. DLMF's conditions do not suffice: the identity fails for `x = -2`,
`θ = -3` (the left side depends on `x²` only), and for `x = 1`, `θ = 2`, where the left side is
a Cauchy principal value (19.2.20) but the right side is not (they differ by `-π i/(2√θ)`).
Checked numerically at 3000 random complex points under the stated hypotheses. -/
@[dlmf 19.26.E27]
theorem symEllIntRC_duplication_theta {x θ : ℂ} (hx : 0 < x.re) (hθ : θ ≠ x ^ 2)
    (hθx : x ^ 2 - θ ∈ slitPlane)
    (hθ' : θ ≠ (x + (x ^ 2 - θ) ^ (1 / 2 : ℂ)) ^ 2) :
    let s := x + (x ^ 2 - θ) ^ (1 / 2 : ℂ)
    symEllIntRC (x ^ 2) (x ^ 2 - θ) = 2 * symEllIntRC (s ^ 2) (s ^ 2 - θ) := by
  sorry

end DLMF.EllipticIntegrals
