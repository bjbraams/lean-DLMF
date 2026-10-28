/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.Basic
public import DLMF.Confluent.Recurrence
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Coulomb wave functions (Temme §7.3.2; DLMF §33.2)

The regular Coulomb wave function is
`F_ℓ(η,ρ) = C_ℓ(η) ρ^{ℓ+1} e^{-iρ} M(ℓ + 1 - iη, 2ℓ + 2, 2iρ)` (DLMF 33.2.4) with the
normalization `C_ℓ(η)` of DLMF 33.2.5. The unnormalized function `coulombWave` is entire in `ρ`
for `ℓ ∈ ℕ`.

## Main results

* `conj_kummerM`: Kummer's function commutes with complex conjugation.
* `hasDerivAt_coulombWave`, `hasDerivAt_coulombWaveDeriv`, `deriv_deriv_coulombWave`: the Coulomb
  wave equation `w'' + (1 - 2η/ρ - ℓ(ℓ+1)/ρ²) w = 0` (DLMF 33.2.1), from Kummer's equation.
* `coulombWave_eq_conj_form`: the lower-sign form of 33.2.4, by Kummer's transformation.
* `conj_coulombWave`, `ofReal_coulombF`: `F_ℓ(η,ρ)` is real for real `η`, `ρ`.

The irregular functions `H_ℓ^±` (DLMF 33.2.8) and their asymptotic expansions (DLMF 33.11.1) are
in `DLMF.Confluent.CoulombAsymptotics`. The irregular function `G_ℓ`, the relation
`H_ℓ^± = G_ℓ ± i F_ℓ` (DLMF 33.2.11), the Wronskian 33.2.12 and the limits
`F_ℓ ~ sin θ_ℓ`, `G_ℓ ~ cos θ_ℓ` (33.10.1) are in `DLMF.Confluent.CoulombIrregular`.
-/

@[expose] public section

open Complex Filter MeasureTheory Asymptotics Set
open scoped Real Topology Nat ComplexConjugate
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- Complex conjugation commutes with the Pochhammer symbol: `conj((a)_n) = (conj a)_n`. -/
theorem conj_poch (a : ℂ) (n : ℕ) : conj (poch a n) = poch (conj a) n := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih => rw [poch_succ, poch_succ, map_mul, ih, map_add, map_natCast]

/-- Kummer's function commutes with complex conjugation. -/
theorem conj_kummerM (a c z : ℂ) :
    conj (kummerM a c z) = kummerM (conj a) (conj c) (conj z) := by
  rw [kummerM, kummerM, Complex.conj_tsum]
  congr 1
  funext n
  simp [conj_poch, map_div₀, map_mul, map_pow]

/-- `2ℓ + 2` is not a nonpositive integer. -/
theorem two_mul_nat_add_two_ne_neg_nat (ℓ : ℕ) : ∀ k : ℕ, (2 * (ℓ : ℂ) + 2) ≠ -k := fun k h => by
  have := congrArg Complex.re h
  simp at this
  linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- Derivative of `z ↦ M(α, b, 2iz)`: it is `2i (α/b) M(α+1, b+1, 2iz)`. -/
theorem hasDerivAt_kummerM_two_I_mul {α b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasDerivAt (fun z : ℂ => kummerM α b (2 * I * z))
      (2 * I * (α / b * kummerM (α + 1) (b + 1) (2 * I * z))) z := by
  have h := (hasDerivAt_kummerM_shift (a := α) hb (2 * I * z)).comp z
    ((hasDerivAt_id z).const_mul (2 * I))
  exact h.congr_deriv (by simp only [mul_one]; ring)

/-- The Kummer-function form of the Coulomb wave has derivative `coulombWaveDeriv ℓ η z`. -/
theorem hasDerivAt_coulombWave (ℓ : ℕ) (η z : ℂ) :
    HasDerivAt (coulombWave ℓ η) (coulombWaveDeriv ℓ η z) z := by
  have hE : HasDerivAt (fun z : ℂ => exp (-I * z)) (-I * exp (-I * z)) z := by
    have := ((hasDerivAt_id z).const_mul (-I)).cexp
    exact this.congr_deriv (by simp only [mul_one, id]; ring)
  have h := ((hasDerivAt_pow (ℓ + 1) z).mul hE).mul
    (hasDerivAt_kummerM_two_I_mul (α := ℓ + 1 - I * η) (two_mul_nat_add_two_ne_neg_nat ℓ) z)
  exact h.congr_deriv (by unfold coulombWaveDeriv; simp only [Nat.add_sub_cancel, Pi.mul_apply]; ring)

/-- **The Coulomb wave equation** (DLMF 33.2.1, Temme 7.19), multiplied by `z²`:
`z² w'' + (z² - 2ηz - ℓ(ℓ+1)) w = 0` for the regular solution. -/
@[dlmf 33.2.E1]
theorem hasDerivAt_coulombWaveDeriv (ℓ : ℕ) (η : ℂ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (coulombWaveDeriv ℓ η)
      ((2 * η / z + ℓ * (ℓ + 1) / z ^ 2 - 1) * coulombWave ℓ η z) z := by
  set a : ℂ := ℓ + 1 - I * η with ha
  set b : ℂ := 2 * ℓ + 2 with hb
  have hb0 := two_mul_nat_add_two_ne_neg_nat ℓ
  have hb1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb0 1
  have hE : HasDerivAt (fun z : ℂ => exp (-I * z)) (-I * exp (-I * z)) z := by
    have := ((hasDerivAt_id z).const_mul (-I)).cexp
    exact this.congr_deriv (by simp only [mul_one, id]; ring)
  have h0 := hasDerivAt_kummerM_two_I_mul (α := a) hb0 z
  have h1 := hasDerivAt_kummerM_two_I_mul (α := a + 1) hb1 z
  have hP : HasDerivAt (fun z : ℂ => ((ℓ + 1 : ℕ) : ℂ) * z ^ ℓ * kummerM a b (2 * I * z) -
      I * z ^ (ℓ + 1) * kummerM a b (2 * I * z) +
      2 * I * (a / b) * z ^ (ℓ + 1) * kummerM (a + 1) (b + 1) (2 * I * z)) _ z :=
    ((((hasDerivAt_pow ℓ z).const_mul _).mul h0).sub
      (((hasDerivAt_pow (ℓ + 1) z).const_mul I).mul h0)).add
      (((hasDerivAt_pow (ℓ + 1) z).const_mul (2 * I * (a / b))).mul h1)
  have h := hE.mul hP
  have hc := kummerM_ode_contiguous (a := a) (b := b) hb0 (z := 2 * I * z)
  refine h.congr_deriv ?_
  unfold coulombWave
  rw [show a + 1 + 1 = a + 2 by ring, show b + 1 + 1 = b + 2 by ring]
  have hbne : b ≠ 0 := by simpa using hb0 0
  have hb1ne : b + 1 ≠ 0 := by simpa using hb1 0
  generalize kummerM a b (2 * I * z) = M0 at hc ⊢
  generalize kummerM (a + 1) (b + 1) (2 * I * z) = M1 at hc ⊢
  generalize kummerM (a + 2) (b + 2) (2 * I * z) = M2 at hc ⊢
  generalize exp (-I * z) = E
  rw [hb] at hc ⊢
  rcases ℓ with _ | m
  · simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero, mul_zero, Nat.zero_sub] at hc ⊢
    field_simp
    linear_combination (norm := skip) (I * E * a * z) * hc
    rw [ha]
    ring_nf
    simp only [Complex.I_sq]
    ring_nf
  · simp only [Nat.add_sub_cancel] at hc ⊢
    push_cast at hc ⊢
    have h1 : (m : ℂ) + 2 ≠ 0 := by norm_cast
    have h2 : 2 * ((m : ℂ) + 1) + 2 ≠ 0 := by norm_cast
    have h3 : 2 * ((m : ℂ) + 1) + 2 + 1 ≠ 0 := by norm_cast
    have h4 : (m : ℂ) + 1 + 1 ≠ 0 := by norm_cast
    have h5 : ((m : ℂ) + 1 + 1) * 2 + 1 ≠ 0 := by norm_cast
    field_simp
    linear_combination (norm := skip) (I * E * a * z ^ (m + 3)) * hc
    rw [ha]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring_nf

/-- The Coulomb wave equation in `deriv` form, for `z ≠ 0`. -/
theorem deriv_deriv_coulombWave (ℓ : ℕ) (η : ℂ) {z : ℂ} (hz : z ≠ 0) :
    deriv (deriv (coulombWave ℓ η)) z +
      (1 - 2 * η / z - ℓ * (ℓ + 1) / z ^ 2) * coulombWave ℓ η z = 0 := by
  have : deriv (coulombWave ℓ η) = coulombWaveDeriv ℓ η :=
    funext fun w => (hasDerivAt_coulombWave ℓ η w).deriv
  rw [this, (hasDerivAt_coulombWaveDeriv ℓ η hz).deriv]
  ring

/-- The lower-sign form of DLMF 33.2.4, by Kummer's transformation:
`ρ^{ℓ+1} e^{-iρ} M(ℓ+1-iη, 2ℓ+2, 2iρ) = ρ^{ℓ+1} e^{iρ} M(ℓ+1+iη, 2ℓ+2, -2iρ)`. -/
@[dlmf 33.2.E4]
theorem coulombWave_eq_conj_form (ℓ : ℕ) (η z : ℂ) :
    coulombWave ℓ η z =
      z ^ (ℓ + 1) * exp (I * z) * kummerM (ℓ + 1 + I * η) (2 * ℓ + 2) (-(2 * I * z)) := by
  rw [coulombWave, kummerM_kummer_transform (two_mul_nat_add_two_ne_neg_nat ℓ),
    show 2 * (ℓ : ℂ) + 2 - (ℓ + 1 - I * η) = ℓ + 1 + I * η by ring]
  have he : exp (-I * z) * exp (2 * I * z) = exp (I * z) := by
    rw [← Complex.exp_add]; ring_nf
  linear_combination (z ^ (ℓ + 1) * kummerM (ℓ + 1 + I * η) (2 * ℓ + 2) (-(2 * I * z))) * he

/-- For real `η` and `ρ` the regular Coulomb wave function is real (Temme §7.3.2). -/
theorem conj_coulombWave (ℓ : ℕ) (η ρ : ℝ) :
    conj (coulombWave ℓ η ρ) = coulombWave ℓ η ρ := by
  conv_rhs => rw [coulombWave_eq_conj_form]
  rw [coulombWave, map_mul, map_mul, map_pow, Complex.conj_ofReal, ← Complex.exp_conj,
    conj_kummerM]
  simp only [map_mul, map_neg, map_add, map_sub, map_one, map_ofNat, map_natCast,
    Complex.conj_I, Complex.conj_ofReal]
  ring_nf

/-- The regular Coulomb function is `F_ℓ(η,ρ) = C_ℓ(η) · coulombWave ℓ η ρ` (DLMF 33.2.4). -/
theorem ofReal_coulombF (ℓ : ℕ) (η ρ : ℝ) :
    (coulombF ℓ η ρ : ℂ) = coulombC ℓ η * coulombWave ℓ η ρ := by
  have h := conj_coulombWave ℓ η ρ
  rw [coulombF]
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero]
    have him : (coulombWave ℓ η ρ).im = 0 := by
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
    rw [him, mul_zero]

end DLMF.Confluent
