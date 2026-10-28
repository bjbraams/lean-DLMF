/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Differential
public import DLMF.OrthogonalPolynomials.BinomialSeries

/-!
# Gegenbauer polynomials and the formal series `G_λ(wX) G_λ(X/w)`

Let `G_λ = ∑ (λ)_n / n! Xⁿ` be the formal binomial series `(1 - X)^{-λ}`. The product
`G_λ(wX) G_λ(X/w)` is the formal Gegenbauer generating function at `x = (w + w⁻¹)/2`.
It satisfies the generating-function differential equation, whose coefficients give the
three-term recurrence. Comparing with `ultrasphPoly_recurrence` identifies its coefficients
with `C_n^{(λ)}((w + w⁻¹)/2)` for `Re λ > -1/2`. This gives the trigonometric sum
DLMF 18.5.11 (`ultrasphPoly_cos_sum`) and, with `|w| = 1` and binomial series, the
generating functions. The explicit sum DLMF 18.5.10 (`ultrasphPoly_finite_sum`) is proved
separately: its terms satisfy the same three-term recurrence. Comparing coefficients
with the Jacobi hypergeometric sum in `x²` then gives the quadratic transformations
DLMF 18.7.15–18.7.16; the Jacobi forms 18.7.13–18.7.14 follow by the Gegenbauer–Jacobi
relation, extended to `α = -1/2` by continuity in `α`. The multiplicativity `G_λ G_μ = G_{λ+μ}`
(Chu–Vandermonde, `poch_add_binomial_sum`) gives the convolution identities in `Series.lean`.
-/

@[expose] public section

open Complex
open scoped Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- The Gegenbauer generating series `G_λ(wX) G_λ(X/w)`. -/
def gegenbauerSeries (lam w : ℂ) : PowerSeries ℂ := binomProductSeries lam lam w

open PowerSeries in
/-- The Gegenbauer generating-function differential equation. -/
theorem gegenbauerSeries_ode (lam : ℂ) {w : ℂ} (hw : w ≠ 0) :
    (1 - C (w + w⁻¹) * X + X ^ 2) * d⁄dX (gegenbauerSeries lam w) =
      C lam * (C (w + w⁻¹) - C 2 * X) * gegenbauerSeries lam w := by
  have h := binomProductSeries_ode lam lam hw
  have hC : (C (lam * w + lam * w⁻¹) - C (lam + lam) * X : PowerSeries ℂ) =
      C lam * (C (w + w⁻¹) - C 2 * X) := by
    simp only [map_add, map_mul, map_ofNat]; ring
  rwa [hC] at h

open PowerSeries in
/-- The Gegenbauer three-term recurrence for the series coefficients. -/
theorem coeff_gegenbauerSeries_recurrence (lam : ℂ) {w : ℂ} (hw : w ≠ 0) (n : ℕ) :
    (n + 2 : ℂ) * coeff (n + 2) (gegenbauerSeries lam w) =
      (w + w⁻¹) * (n + 1 + lam) * coeff (n + 1) (gegenbauerSeries lam w) -
        (n + 2 * lam) * coeff n (gegenbauerSeries lam w) := by
  have h := coeff_binomProductSeries_recurrence lam lam hw n
  unfold gegenbauerSeries
  linear_combination h

open PowerSeries in
/-- The constant coefficient of the Gegenbauer series. -/
theorem coeff_zero_gegenbauerSeries (lam w : ℂ) : coeff 0 (gegenbauerSeries lam w) = 1 := by
  exact coeff_zero_binomProductSeries lam lam w

open PowerSeries in
/-- The linear coefficient of the Gegenbauer series. -/
theorem coeff_one_gegenbauerSeries (lam w : ℂ) :
    coeff 1 (gegenbauerSeries lam w) = lam * (w + w⁻¹) := by
  rw [gegenbauerSeries, coeff_one_binomProductSeries]; ring

open PowerSeries in
/-- The Gegenbauer polynomial at `(w + w⁻¹)/2` is the `n`-th coefficient of `G_λ(wX) G_λ(X/w)`. -/
theorem ultrasphPoly_eq_coeff_gegenbauerSeries {lam : ℂ} (hlam : -1 / 2 < lam.re) {w : ℂ}
    (hw : w ≠ 0) (n : ℕ) :
    ultrasphPoly lam n ((w + w⁻¹) / 2) = coeff n (gegenbauerSeries lam w) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [coeff_zero_gegenbauerSeries]
    · rw [ultrasphPoly_one_eq hlam, coeff_one_gegenbauerSeries]; ring
    · have hrec := ultrasphPoly_recurrence hlam n ((w + w⁻¹) / 2)
      have hser := coeff_gegenbauerSeries_recurrence lam hw n
      rw [ih n (by omega), ih (n + 1) (by omega)] at hrec
      have hn2 : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
      apply mul_left_cancel₀ hn2
      linear_combination hrec - hser


open PowerSeries in
/-- Products of Gegenbauer series add the parameters. -/
theorem gegenbauerSeries_mul (lam μ w : ℂ) :
    gegenbauerSeries lam w * gegenbauerSeries μ w = gegenbauerSeries (lam + μ) w := by
  unfold gegenbauerSeries binomProductSeries
  rw [← binomSeries_mul, map_mul, map_mul]
  ring

open PowerSeries in
/-- Explicit coefficients of the Gegenbauer series. -/
theorem coeff_gegenbauerSeries (lam w : ℂ) (n : ℕ) :
    coeff n (gegenbauerSeries lam w) = ∑ k ∈ Finset.range (n + 1),
      poch lam k * poch lam (n - k) / ((k.factorial : ℂ) * (n - k).factorial) *
        (w ^ k * w⁻¹ ^ (n - k)) := by
  exact coeff_binomProductSeries lam lam w n

/-- Gegenbauer polynomials as a trigonometric sum, DLMF 18.5.11, for complex angles. -/
@[dlmf 18.5.E11]
theorem ultrasphPoly_cos_sum {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (θ : ℂ) :
    ultrasphPoly lam n (cos θ) = ∑ k ∈ Finset.range (n + 1),
      poch lam k * poch lam (n - k) / ((k.factorial : ℂ) * (n - k).factorial) *
        cos (((n : ℂ) - 2 * k) * θ) := by
  set w := exp (θ * I) with hw
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have hwinv : w⁻¹ = exp (-θ * I) := by rw [hw, ← Complex.exp_neg]; ring_nf
  have hcos : cos θ = (w + w⁻¹) / 2 := by
    rw [hwinv, hw, Complex.cos]
  rw [hcos, ultrasphPoly_eq_coeff_gegenbauerSeries hlam hw0, coeff_gegenbauerSeries]
  have hterm : ∀ k ∈ Finset.range (n + 1), cos (((n : ℂ) - 2 * k) * θ) =
      (w ^ (n - k) * w⁻¹ ^ k + w ^ k * w⁻¹ ^ (n - k)) / 2 := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Complex.cos, hwinv, hw, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
    push_cast [Nat.cast_sub hkn]
    congr 2 <;> ring_nf
  conv_rhs => rw [Finset.sum_congr rfl fun k hk => by rw [hterm k hk]]
  set c : ℕ → ℂ := fun k => poch lam k * poch lam (n - k) /
    ((k.factorial : ℂ) * (n - k).factorial) with hc
  have hrefl : ∑ k ∈ Finset.range (n + 1), c k * (w ^ (n - k) * w⁻¹ ^ k) =
      ∑ k ∈ Finset.range (n + 1), c k * (w ^ k * w⁻¹ ^ (n - k)) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show n + 1 - 1 - k = n - k by omega, Nat.sub_sub_self hkn, hc]
    simp only [Nat.sub_sub_self hkn]
    ring
  have hsplit : ∑ k ∈ Finset.range (n + 1),
      c k * ((w ^ (n - k) * w⁻¹ ^ k + w ^ k * w⁻¹ ^ (n - k)) / 2) =
      (∑ k ∈ Finset.range (n + 1), c k * (w ^ (n - k) * w⁻¹ ^ k) +
        ∑ k ∈ Finset.range (n + 1), c k * (w ^ k * w⁻¹ ^ (n - k))) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hsplit, hrefl]
  ring

/-- Every complex number is `(w + w⁻¹)/2` for some nonzero `w`. -/
theorem exists_eq_half_add_recip (x : ℂ) : ∃ w : ℂ, w ≠ 0 ∧ x = (w + w⁻¹) / 2 := by
  obtain ⟨θ, rfl⟩ := Complex.cos_surjective x
  refine ⟨exp (θ * I), Complex.exp_ne_zero _, ?_⟩
  rw [← Complex.exp_neg, Complex.cos]
  ring_nf

open PowerSeries in
/-- `(1 - 2yX + X²) P_{λ+1} = P_λ`. -/
theorem gegenbauerSeries_add_one (lam : ℂ) {w : ℂ} (hw : w ≠ 0) :
    (1 - C (w + w⁻¹) * X + X ^ 2) * gegenbauerSeries (lam + 1) w = gegenbauerSeries lam w := by
  have this : C w * C w⁻¹ = (1 : PowerSeries ℂ) := by rw [← map_mul, mul_inv_cancel₀ hw, map_one]
  rw [← gegenbauerSeries_mul]
  have h1 := one_sub_mul_rescale_binomSeries_one w
  have h2 := one_sub_mul_rescale_binomSeries_one w⁻¹
  unfold gegenbauerSeries binomProductSeries at *
  simp only [map_add] at *
  linear_combination (rescale w (binomSeries lam) * rescale w⁻¹ (binomSeries lam)) *
    (((1 - C w⁻¹ * X) * rescale w⁻¹ (binomSeries 1)) * h1 + h2 -
      (X ^ 2 * rescale w (binomSeries 1) *
      rescale w⁻¹ (binomSeries 1)) * this)


open PowerSeries in
/-- Coefficient form of `G_λ(wX) G_λ(X/w) · G_μ(wX) G_μ(X/w) = G_{λ+μ}(wX) G_{λ+μ}(X/w)`. -/
theorem sum_coeff_mul_coeff_gegenbauerSeries (lam μ w : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), coeff k (gegenbauerSeries lam w) *
      coeff (n - k) (gegenbauerSeries μ w) = coeff n (gegenbauerSeries (lam + μ) w) := by
  rw [← gegenbauerSeries_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

open PowerSeries in
/-- The weighted series `∑ (n + 2λ)/(2λ) tₙ Xⁿ = P + X P' / (2λ)`, where `P` is
`gegenbauerSeries lam w`. -/
def weightedGegenbauerSeries (lam w : ℂ) : PowerSeries ℂ :=
  gegenbauerSeries lam w + C (1 / (2 * lam)) * (X * d⁄dX (gegenbauerSeries lam w))

open PowerSeries in
/-- Coefficients of the weighted Gegenbauer series. -/
theorem coeff_weightedGegenbauerSeries {lam : ℂ} (hlam0 : lam ≠ 0) (w : ℂ) (k : ℕ) :
    coeff k (weightedGegenbauerSeries lam w) =
      (k + 2 * lam) / (2 * lam) * coeff k (gegenbauerSeries lam w) := by
  rw [weightedGegenbauerSeries, map_add, coeff_C_mul]
  rcases k with _ | k
  · simp [div_self (mul_ne_zero two_ne_zero hlam0)]
  · rw [coeff_succ_X_mul, coeff_derivative]
    field_simp
    push_cast
    ring

open PowerSeries in
/-- The weighted series equals `(1 - yX)` times the series for `λ + 1`, `y = (w + w⁻¹)/2`. -/
theorem weightedGegenbauerSeries_eq {lam : ℂ} (hlam0 : lam ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    weightedGegenbauerSeries lam w =
      (1 - C ((w + w⁻¹) / 2) * X) * gegenbauerSeries (lam + 1) w := by
  have hode := gegenbauerSeries_ode lam hw
  have hQ := gegenbauerSeries_add_one lam hw
  simp only [map_ofNat] at hode
  set P := gegenbauerSeries lam w
  set Q := gegenbauerSeries (lam + 1) w
  -- multiply by `1 - 2yX + X²`, which is nonzero
  have hD : (1 - C (w + w⁻¹) * X + X ^ 2 : PowerSeries ℂ) ≠ 0 := by
    intro h
    have := congrArg (coeff 0) h
    simp at this
  apply mul_left_cancel₀ hD
  have hc : C (1 / (2 * lam)) * C lam = (C (1 / 2) : PowerSeries ℂ) := by
    rw [← map_mul]; congr 1; field_simp
  have hy' : C ((w + w⁻¹) / 2) = C (1 / 2) * C (w + w⁻¹) := by rw [← map_mul]; ring_nf
  have h2 : C (1 / 2) * 2 = (1 : PowerSeries ℂ) := by
    rw [← map_ofNat C 2, ← map_mul]; norm_num
  rw [weightedGegenbauerSeries, hy']
  linear_combination (C (1 / (2 * lam)) * X) * hode - (1 - C (1 / 2) * C (w + w⁻¹) * X) * hQ +
    (X * (C (w + w⁻¹) - 2 * X) * P) * hc + (P * (C (w + w⁻¹) * X - X ^ 2)) * h2

open PowerSeries in
/-- Coefficient form of `weightedGegenbauerSeries_eq` after multiplying by `1/(1 - yX)`. -/
theorem sum_weighted_coeff_gegenbauerSeries {lam : ℂ} (hlam0 : lam ≠ 0) {w : ℂ} (hw : w ≠ 0)
    (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (k + 2 * lam) / (2 * lam) * coeff k (gegenbauerSeries lam w) *
      ((w + w⁻¹) / 2) ^ (n - k) = coeff n (gegenbauerSeries (lam + 1) w) := by
  set y := (w + w⁻¹) / 2
  have hgeo : (1 - C y * X) * mk (fun m => y ^ m) = 1 := by
    have := one_sub_mul_rescale_binomSeries_one y
    convert this using 2
    ext m
    rw [coeff_mk, coeff_rescale, coeff_binomSeries, poch_nat_one,
      div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)), mul_one]
  have hsum : coeff n (weightedGegenbauerSeries lam w * mk fun m => y ^ m) =
      coeff n (gegenbauerSeries (lam + 1) w) := by
    rw [weightedGegenbauerSeries_eq hlam0 hw, mul_comm (1 - C y * X), mul_assoc, hgeo, mul_one]
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_weightedGegenbauerSeries hlam0, coeff_mk]

/-! ### The explicit sum DLMF 18.5.10 -/

/-- Totalized coefficients of the explicit Gegenbauer sum DLMF 18.5.10. -/
def gegenbauerCoeff (lam : ℂ) (n k : ℕ) : ℂ :=
  if 2 * k ≤ n then (-1 : ℂ) ^ k * poch lam (n - k) / ((k.factorial : ℂ) * (n - 2 * k).factorial)
  else 0

/-- The explicit sum of DLMF 18.5.10 over any range containing `0, …, n/2`. -/
theorem ultrasphPoly_sum_eq_sum_coeff (lam y : ℂ) (n M : ℕ) (hM : n / 2 + 1 ≤ M) :
    ∑ k ∈ Finset.range (n / 2 + 1), (-1 : ℂ) ^ k * poch lam (n - k) /
        ((k.factorial : ℂ) * (n - 2 * k).factorial) * y ^ (n - 2 * k) =
      ∑ k ∈ Finset.range M, gegenbauerCoeff lam n k * y ^ (n - 2 * k) := by
  simp only [gegenbauerCoeff, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_range, Finset.mem_filter]
  omega


/-- The recurrence for the constant terms of the explicit sum. -/
theorem gegenbauerCoeff_rec_zero (lam : ℂ) (n : ℕ) :
    (n + 2 : ℂ) * gegenbauerCoeff lam (n + 2) 0 =
      (n + lam + 1) * gegenbauerCoeff lam (n + 1) 0 := by
  simp only [gegenbauerCoeff, mul_zero, zero_le, ↓reduceIte, pow_zero, one_mul,
    Nat.factorial_zero, Nat.cast_one, Nat.sub_zero]
  rw [poch_succ lam (n + 1), Nat.factorial_succ (n + 1)]
  have h : ((n + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (n : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
  push_cast
  field_simp
  ring

/-- The termwise recurrence for the explicit sum DLMF 18.5.10. -/
theorem gegenbauerCoeff_rec_succ (lam : ℂ) (n k : ℕ) :
    (n + 2 : ℂ) * gegenbauerCoeff lam (n + 2) (k + 1) =
      (n + lam + 1) * gegenbauerCoeff lam (n + 1) (k + 1) -
        (n + 2 * lam) * gegenbauerCoeff lam n k := by
  unfold gegenbauerCoeff
  rcases lt_trichotomy (2 * k) n with h | h | h
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * k + 1 + m := ⟨n - 2 * k - 1, by omega⟩
    have c1 : 2 * (k + 1) ≤ 2 * k + 1 + m + 2 := by omega
    have c2 : 2 * (k + 1) ≤ 2 * k + 1 + m + 1 := by omega
    have c3 : 2 * k ≤ 2 * k + 1 + m := by omega
    simp only [c1, c2, c3, ↓reduceIte]
    rw [show 2 * k + 1 + m + 2 - (k + 1) = (k + 1 + m) + 1 by omega,
      show 2 * k + 1 + m + 2 - 2 * (k + 1) = m + 1 by omega,
      show 2 * k + 1 + m + 1 - (k + 1) = k + 1 + m by omega,
      show 2 * k + 1 + m + 1 - 2 * (k + 1) = m by omega,
      show 2 * k + 1 + m - k = k + 1 + m by omega,
      show 2 * k + 1 + m - 2 * k = m + 1 by omega,
      poch_succ lam (k + 1 + m), Nat.factorial_succ k, Nat.factorial_succ m, pow_succ]
    have h1 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h3 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have h4 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    push_cast
    field_simp
    ring
  · subst h
    have c1 : 2 * (k + 1) ≤ 2 * k + 2 := by omega
    have c2 : ¬ 2 * (k + 1) ≤ 2 * k + 1 := by omega
    have c3 : 2 * k ≤ 2 * k := le_rfl
    simp only [c1, c2, c3, ↓reduceIte]
    rw [show 2 * k + 2 - (k + 1) = k + 1 by omega, show 2 * k + 2 - 2 * (k + 1) = 0 by omega,
      show 2 * k - k = k by omega, show 2 * k - 2 * k = 0 by omega,
      poch_succ lam k, Nat.factorial_succ k, pow_succ]
    have h1 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h3 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    push_cast
    field_simp
    ring
  · have c1 : ¬ 2 * (k + 1) ≤ n + 2 := by omega
    have c2 : ¬ 2 * (k + 1) ≤ n + 1 := by omega
    have c3 : ¬ 2 * k ≤ n := by omega
    simp only [c1, c2, c3, ↓reduceIte]
    ring


/-- Absorbing a factor `y` into the power in the explicit sum. -/
theorem gegenbauerCoeff_mul_pow_succ (lam y : ℂ) (n k : ℕ) :
    gegenbauerCoeff lam (n + 1) (k + 1) * (y * y ^ (n + 1 - 2 * (k + 1))) =
      gegenbauerCoeff lam (n + 1) (k + 1) * y ^ (n - 2 * k) := by
  by_cases h : 2 * (k + 1) ≤ n + 1
  · rw [← pow_succ', show n + 1 - 2 * (k + 1) + 1 = n - 2 * k by omega]
  · simp [gegenbauerCoeff, h]

/-- The explicit sums of DLMF 18.5.10 satisfy the Gegenbauer recurrence. -/
theorem gegenbauerExplicit_rec (lam y : ℂ) (n : ℕ) :
    (n + 2 : ℂ) * ∑ k ∈ Finset.range ((n + 2) / 2 + 1), (-1 : ℂ) ^ k * poch lam (n + 2 - k) /
        ((k.factorial : ℂ) * (n + 2 - 2 * k).factorial) * y ^ (n + 2 - 2 * k) =
      (n + lam + 1) * y * ∑ k ∈ Finset.range ((n + 1) / 2 + 1), (-1 : ℂ) ^ k *
          poch lam (n + 1 - k) / ((k.factorial : ℂ) * (n + 1 - 2 * k).factorial) *
            y ^ (n + 1 - 2 * k) -
        (n + 2 * lam) * ∑ k ∈ Finset.range (n / 2 + 1), (-1 : ℂ) ^ k * poch lam (n - k) /
          ((k.factorial : ℂ) * (n - 2 * k).factorial) * y ^ (n - 2 * k) := by
  rw [ultrasphPoly_sum_eq_sum_coeff lam y (n + 2) (n + 3) (by omega),
    ultrasphPoly_sum_eq_sum_coeff lam y (n + 1) (n + 3) (by omega),
    ultrasphPoly_sum_eq_sum_coeff lam y n (n + 2) (by omega),
    Finset.sum_range_succ' _ (n + 2), Finset.sum_range_succ' _ (n + 2)]
  have key : ∀ k ∈ Finset.range (n + 2),
      (n + 2 : ℂ) * (gegenbauerCoeff lam (n + 2) (k + 1) * y ^ (n + 2 - 2 * (k + 1))) =
        (n + lam + 1) * y * (gegenbauerCoeff lam (n + 1) (k + 1) * y ^ (n + 1 - 2 * (k + 1))) -
          (n + 2 * lam) * (gegenbauerCoeff lam n k * y ^ (n - 2 * k)) := by
    intro k _
    have h1 := gegenbauerCoeff_rec_succ lam n k
    have h2 := gegenbauerCoeff_mul_pow_succ lam y n k
    rw [show n + 2 - 2 * (k + 1) = n - 2 * k by omega]
    linear_combination (y ^ (n - 2 * k)) * h1 - (n + lam + 1) * h2
  rw [mul_add, Finset.mul_sum, Finset.sum_congr rfl key, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have h0 := gegenbauerCoeff_rec_zero lam n
  simp only [Nat.mul_zero, Nat.sub_zero]
  linear_combination (y ^ (n + 2)) * h0

/-- The explicit Gegenbauer sum, DLMF 18.5.10. -/
@[dlmf 18.5.E10]
theorem ultrasphPoly_finite_sum {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    ultrasphPoly lam n x = ∑ k ∈ Finset.range (n / 2 + 1),
      (-1 : ℂ) ^ k * poch lam (n - k) /
        ((k.factorial : ℂ) * (n - 2 * k).factorial) * (2 * x) ^ (n - 2 * k) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [poch_zero]
    · simp [ultrasphPoly_one_eq hlam, poch_succ, poch_zero]
      ring
    · have hrec := ultrasphPoly_recurrence hlam n x
      have hexp := gegenbauerExplicit_rec lam (2 * x) n
      rw [ih n (by omega), ih (n + 1) (by omega)] at hrec
      have hn2 : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
      apply mul_left_cancel₀ hn2
      rw [show n + 1 + 1 = n + 2 by ring, hexp]
      linear_combination hrec

/-! ### Quadratic transformations DLMF 18.7.13–18.7.16 -/

@[dlmf 18.7.E15]
theorem ultrasphPoly_quadratic_even {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    ultrasphPoly lam (2 * n) x = poch lam n / poch (1 / 2) n
        * jacobiPolyP (lam - 1 / 2) (-1 / 2) n (2 * x ^ 2 - 1) := by
  have hα : -1 < (lam - 1 / 2).re := by simp; linarith
  have hβ : -1 < (-1 / 2 : ℂ).re := by norm_num
  rw [show 2 * x ^ 2 - 1 = -(1 - 2 * x ^ 2) by ring, jacobi_reflection hα hβ,
    ultrasphPoly_finite_sum hlam, jacobiPolyP, ordinaryHypergeometric_eq_sum_neg_nat,
    show (1 - (1 - 2 * x ^ 2)) / 2 = x ^ 2 by ring, Finset.mul_sum, Finset.mul_sum,
    show 2 * n / 2 = n by omega, Finset.mul_sum]
  refine (Finset.sum_range_reflect _ (n + 1)).symm.trans (Finset.sum_congr rfl fun k hk => ?_)
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show n + 1 - 1 - k = n - k by omega, show 2 * n - (n - k) = n + k by omega,
    show 2 * n - 2 * (n - k) = 2 * k by omega, gaussHGCoeff, poch_add,
    show (n : ℂ) + -1 / 2 + (lam - 1 / 2) + 1 = lam + n by ring,
    show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num, ← two_pow_mul_poch_half k]
  have hpk := poch_neg_nat_mul_factorial hkn
  have hh : ∀ m, poch (1 / 2 : ℂ) m ≠ 0 := poch_ne_zero_of_re_pos (by norm_num)
  have f1 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f2 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f3 : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hsign : (-1 : ℂ) ^ (n - k) * (-1) ^ k = (-1) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hkn]
  have hpn : poch (-(n : ℂ)) k = (-1) ^ k * n.factorial / (n - k).factorial := by
    field_simp; linear_combination hpk
  rw [hpn, mul_pow, ← pow_mul, pow_mul (2 : ℂ)]
  have h4 : ((2 : ℂ) ^ 2) ^ k = (2 : ℂ) ^ (2 * k) := by rw [← pow_mul]
  have h2k : (2 : ℂ) ^ (2 * k) ≠ 0 := pow_ne_zero _ two_ne_zero
  have := hh n
  have := hh k
  rw [← hsign]
  field_simp
  rw [← pow_mul, show (-1 : ℂ) ^ (k * 2) = 1 from Even.neg_one_pow ⟨k, by ring⟩]
  ring

@[dlmf 18.7.E16]
theorem ultrasphPoly_quadratic_odd {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    ultrasphPoly lam (2 * n + 1) x = poch lam (n + 1) / poch (1 / 2) (n + 1) * x *
      jacobiPolyP (lam - 1 / 2) (1 / 2) n (2 * x ^ 2 - 1) := by
  have hα : -1 < (lam - 1 / 2).re := by simp; linarith
  have hβ : -1 < (1 / 2 : ℂ).re := by norm_num
  rw [show 2 * x ^ 2 - 1 = -(1 - 2 * x ^ 2) by ring, jacobi_reflection hα hβ,
    ultrasphPoly_finite_sum hlam, jacobiPolyP, ordinaryHypergeometric_eq_sum_neg_nat,
    show (1 - (1 - 2 * x ^ 2)) / 2 = x ^ 2 by ring, Finset.mul_sum, Finset.mul_sum,
    show (2 * n + 1) / 2 = n by omega, Finset.mul_sum]
  refine (Finset.sum_range_reflect _ (n + 1)).symm.trans (Finset.sum_congr rfl fun k hk => ?_)
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show n + 1 - 1 - k = n - k by omega, show 2 * n + 1 - (n - k) = (n + 1) + k by omega,
    show 2 * n + 1 - 2 * (n - k) = 2 * k + 1 by omega, gaussHGCoeff, poch_add,
    show (n : ℂ) + 1 / 2 + (lam - 1 / 2) + 1 = lam + (n + 1 : ℕ) by push_cast; ring,
    show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, poch_succ_left (1 / 2 : ℂ) n,
    show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num]
  have hpk := poch_neg_nat_mul_factorial hkn
  have h3 := two_pow_mul_poch_three_half k
  have hh : ∀ m, poch (3 / 2 : ℂ) m ≠ 0 := poch_ne_zero_of_re_pos (by norm_num)
  have f1 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f2 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f3 : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f4 : ((2 * k + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hsign : (-1 : ℂ) ^ (n - k) * (-1) ^ k = (-1) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hkn]
  have hpn : poch (-(n : ℂ)) k = (-1) ^ k * n.factorial / (n - k).factorial := by
    field_simp; linear_combination hpk
  rw [hpn, ← h3, mul_pow, pow_succ (2 : ℂ), pow_succ x, ← pow_mul x 2 k, mul_comm 2 k]
  have := hh n
  have := hh k
  rw [← hsign]
  field_simp
  rw [← pow_mul, show (-1 : ℂ) ^ (k * 2) = 1 from Even.neg_one_pow ⟨k, by ring⟩]
  ring

open Filter Topology in
/-- `α ↦ P_n^{(α, g α)}(y)` is continuous where `Re α > -1`. -/
theorem continuousAt_jacobiPolyP {g : ℂ → ℂ} (hg : Continuous g) (n : ℕ) (y : ℂ) {α₀ : ℂ}
    (h0 : -1 < α₀.re) : ContinuousAt (fun α => jacobiPolyP α (g α) n y) α₀ := by
  have hU : IsOpen {α : ℂ | -1 < α.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq : (fun α => jacobiPolyP α (g α) n y) =ᶠ[𝓝 α₀] fun α => ∑ k ∈ Finset.range (n + 1),
      poch (n + α + g α + 1) k * poch (α + k + 1) (n - k) /
        ((k.factorial : ℂ) * (n - k).factorial) * ((y - 1) / 2) ^ k := by
    filter_upwards [hU.mem_nhds h0] with α hα
    exact jacobi_finite_sum hα n y
  refine ContinuousAt.congr ?_ heq.symm
  exact (by fun_prop : Continuous fun α : ℂ => ∑ k ∈ Finset.range (n + 1),
      poch (n + α + g α + 1) k * poch (α + k + 1) (n - k) /
        ((k.factorial : ℂ) * (n - k).factorial) * ((y - 1) / 2) ^ k).continuousAt


/-- `2α + 1` is not a nonpositive integer when `Re α > -1` and `α ≠ -1/2`. -/
theorem two_mul_add_one_ne_neg_nat {α : ℂ} (hα : -1 < α.re) (hα2 : α ≠ -1 / 2) :
    ∀ k : ℕ, 2 * α + 1 ≠ -(k : ℂ) := by
  intro k hk
  have hre := congrArg Complex.re hk
  simp at hre
  have hk0 : k = 0 := by
    have : (k : ℝ) < 1 := by linarith
    exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
  subst hk0
  exact hα2 (by linear_combination hk / 2)

open Filter Topology in
/-- Equality at `α = -1/2` from equality nearby, for functions continuous there. -/
theorem eq_at_neg_half {F G : ℂ → ℂ} (hF : ContinuousAt F (-1 / 2)) (hG : ContinuousAt G (-1 / 2))
    (h : ∀ α : ℂ, -1 < α.re → α ≠ -1 / 2 → F α = G α) : F (-1 / 2) = G (-1 / 2) := by
  have hU : IsOpen {α : ℂ | -1 < α.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : F =ᶠ[𝓝[≠] (-1 / 2 : ℂ)] G := by
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds (by norm_num : (-1 : ℝ) < (-1 / 2 : ℂ).re)),
      self_mem_nhdsWithin] with α hα hα2
    exact h α hα hα2
  exact tendsto_nhds_unique (hF.tendsto.mono_left nhdsWithin_le_nhds)
    ((hG.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm)

@[dlmf 18.7.E13]
theorem jacobi_quadratic_even {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    jacobiPolyP α α (2 * n) x / jacobiPolyP α α (2 * n) 1 =
      jacobiPolyP α (-1 / 2) n (2 * x ^ 2 - 1) / jacobiPolyP α (-1 / 2) n 1 := by
  -- the generic case, from the Gegenbauer form
  have generic : ∀ α : ℂ, -1 < α.re → α ≠ -1 / 2 →
      jacobiPolyP α α (2 * n) x / jacobiPolyP α α (2 * n) 1 =
        jacobiPolyP α (-1 / 2) n (2 * x ^ 2 - 1) / jacobiPolyP α (-1 / 2) n 1 := by
    intro α hα hα2
    set lam := α + 1 / 2 with hlamdef
    have hlam : -1 / 2 < lam.re := by simp [lam]; linarith
    have hp1 : poch (lam + 1 / 2) (2 * n) ≠ 0 :=
      poch_ne_zero_of_re_pos (by simp [lam]; linarith) _
    have hp2 : poch (2 * lam) (2 * n) ≠ 0 := poch_ne_zero_of_not_neg_nat (by
      have := two_mul_add_one_ne_neg_nat hα hα2
      simpa [lam, mul_add] using this) _
    have hpl : poch lam n ≠ 0 := poch_ne_zero_of_not_neg_nat (by
      intro k hk
      have := two_mul_add_one_ne_neg_nat hα hα2 (2 * k)
      apply this; simp only [lam] at hk; push_cast; linear_combination 2 * hk) _
    have hph : poch (1 / 2 : ℂ) n ≠ 0 := poch_ne_zero_of_re_pos (by norm_num) _
    have hg := fun y => ultrasphPoly_eq_jacobiPolyP (lam := lam) (2 * n) y hp1
    have hq := fun y => ultrasphPoly_quadratic_even hlam n y
    have hαl : lam - 1 / 2 = α := by simp [lam]
    rw [hαl] at hg hq
    have hJ : ∀ y, jacobiPolyP α α (2 * n) y =
        poch (lam + 1 / 2) (2 * n) / poch (2 * lam) (2 * n) * ultrasphPoly lam (2 * n) y := by
      intro y; rw [hg y, ← mul_assoc, div_mul_div_comm, mul_comm (poch (lam + 1 / 2) (2 * n)),
        div_self (mul_ne_zero hp2 hp1), one_mul]
    rw [hJ, hJ, hq, hq, show (2 : ℂ) * 1 ^ 2 - 1 = 1 by norm_num]
    have h1 := jacobiPolyP_one_ne_zero (β := -1 / 2) hα n
    rw [mul_div_mul_left _ _ (div_ne_zero hp1 hp2), mul_div_mul_left _ _ (div_ne_zero hpl hph)]
  rcases eq_or_ne α (-1 / 2) with rfl | hα2
  · have hc : ∀ y : ℂ, ∀ g : ℂ → ℂ, Continuous g → ∀ m,
        ContinuousAt (fun α => jacobiPolyP α (g α) m y) (-1 / 2) :=
      fun y g hg m => continuousAt_jacobiPolyP hg m y (by norm_num)
    refine eq_at_neg_half (F := fun α => jacobiPolyP α α (2 * n) x / jacobiPolyP α α (2 * n) 1)
      (G := fun α => jacobiPolyP α (-1 / 2) n (2 * x ^ 2 - 1) / jacobiPolyP α (-1 / 2) n 1) ?_ ?_
      generic
    · exact (hc x id continuous_id _).div (hc 1 id continuous_id _)
        (jacobiPolyP_one_ne_zero (by norm_num) _)
    · exact (hc _ _ continuous_const _).div (hc 1 _ continuous_const _)
        (jacobiPolyP_one_ne_zero (by norm_num) _)
  · exact generic α hα hα2

@[dlmf 18.7.E14]
theorem jacobi_quadratic_odd {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    jacobiPolyP α α (2 * n + 1) x / jacobiPolyP α α (2 * n + 1) 1 =
      x * jacobiPolyP α (1 / 2) n (2 * x ^ 2 - 1) / jacobiPolyP α (1 / 2) n 1 := by
  -- the generic case, from the Gegenbauer form
  have generic : ∀ α : ℂ, -1 < α.re → α ≠ -1 / 2 →
      jacobiPolyP α α (2 * n + 1) x / jacobiPolyP α α (2 * n + 1) 1 =
        x * jacobiPolyP α (1 / 2) n (2 * x ^ 2 - 1) / jacobiPolyP α (1 / 2) n 1 := by
    intro α hα hα2
    set lam := α + 1 / 2 with hlamdef
    have hlam : -1 / 2 < lam.re := by simp [lam]; linarith
    have hp1 : poch (lam + 1 / 2) (2 * n + 1) ≠ 0 :=
      poch_ne_zero_of_re_pos (by simp [lam]; linarith) _
    have hp2 : poch (2 * lam) (2 * n + 1) ≠ 0 := poch_ne_zero_of_not_neg_nat (by
      have := two_mul_add_one_ne_neg_nat hα hα2
      simpa [lam, mul_add] using this) _
    have hpl : poch lam (n + 1) ≠ 0 := poch_ne_zero_of_not_neg_nat (by
      intro k hk
      have := two_mul_add_one_ne_neg_nat hα hα2 (2 * k)
      apply this; simp only [lam] at hk; push_cast; linear_combination 2 * hk) _
    have hph : poch (1 / 2 : ℂ) (n + 1) ≠ 0 := poch_ne_zero_of_re_pos (by norm_num) _
    have hg := fun y => ultrasphPoly_eq_jacobiPolyP (lam := lam) (2 * n + 1) y hp1
    have hq := fun y => ultrasphPoly_quadratic_odd hlam n y
    have hαl : lam - 1 / 2 = α := by simp [lam]
    rw [hαl] at hg hq
    have hJ : ∀ y, jacobiPolyP α α (2 * n + 1) y =
        poch (lam + 1 / 2) (2 * n + 1) / poch (2 * lam) (2 * n + 1) *
          ultrasphPoly lam (2 * n + 1) y := by
      intro y; rw [hg y, ← mul_assoc, div_mul_div_comm, mul_comm (poch (lam + 1 / 2) (2 * n + 1)),
        div_self (mul_ne_zero hp2 hp1), one_mul]
    rw [hJ, hJ, hq, hq, show (2 : ℂ) * 1 ^ 2 - 1 = 1 by norm_num]
    have h1 := jacobiPolyP_one_ne_zero (β := 1 / 2) hα n
    rw [mul_div_mul_left _ _ (div_ne_zero hp1 hp2), mul_one, mul_assoc,
      mul_div_mul_left _ _ (div_ne_zero hpl hph)]
  rcases eq_or_ne α (-1 / 2) with rfl | hα2
  · have hc : ∀ y : ℂ, ∀ g : ℂ → ℂ, Continuous g → ∀ m,
        ContinuousAt (fun α => jacobiPolyP α (g α) m y) (-1 / 2) :=
      fun y g hg m => continuousAt_jacobiPolyP hg m y (by norm_num)
    refine eq_at_neg_half
        (F := fun α => jacobiPolyP α α (2 * n + 1) x / jacobiPolyP α α (2 * n + 1) 1)
      (G := fun α => x * jacobiPolyP α (1 / 2) n (2 * x ^ 2 - 1) / jacobiPolyP α (1 / 2) n 1) ?_ ?_
      generic
    · exact (hc x id continuous_id _).div (hc 1 id continuous_id _)
        (jacobiPolyP_one_ne_zero (by norm_num) _)
    · exact (continuousAt_const.mul (hc _ _ continuous_const _)).div (hc 1 _ continuous_const _)
        (jacobiPolyP_one_ne_zero (by norm_num) _)
  · exact generic α hα hα2

/-! ### Analytic generating functions -/

/-- For `‖w‖ = 1` and `‖z‖ < 1` the factor `1 - w z` has positive real part. -/
theorem re_one_sub_mul_pos_of_norm_eq_one {w z : ℂ} (hw : ‖w‖ = 1) (hz : ‖z‖ < 1) :
    0 < (1 - w * z).re := by
  have h := Complex.re_le_norm (w * z)
  rw [norm_mul, hw, one_mul] at h
  rw [Complex.sub_re, Complex.one_re]
  linarith

open PowerSeries in
/-- The analytic Gegenbauer generating function at `x = cos θ` for real `θ`, in terms of the
formal series: `∑ tₙ zⁿ = (1 - 2 x z + z²)^{-λ}` for `‖z‖ < 1`. -/
theorem hasSum_coeff_gegenbauerSeries_mul_pow (lam : ℂ) (θ : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => coeff n (gegenbauerSeries lam (exp (θ * I))) * z ^ n)
      ((1 - 2 * Real.cos θ * z + z ^ 2) ^ (-lam)) := by
  set w : ℂ := exp (θ * I) with hwdef
  have hw : ‖w‖ = 1 := by rw [hwdef, Complex.norm_exp_ofReal_mul_I]
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have hwi : ‖w⁻¹‖ = 1 := by rw [norm_inv, hw, inv_one]
  have h1 : ‖w * z‖ < 1 := by rwa [norm_mul, hw, one_mul]
  have h2 : ‖w⁻¹ * z‖ < 1 := by rwa [norm_mul, hwi, one_mul]
  have hx : (1 - 2 * Real.cos θ * z + z ^ 2 : ℂ) = (1 - w * z) * (1 - w⁻¹ * z) := by
    have hcos : (2 * Real.cos θ : ℂ) = w + w⁻¹ := by
      rw [hwdef, ← Complex.exp_neg, Complex.ofReal_cos, Complex.cos]; ring_nf
    have : w * w⁻¹ = 1 := mul_inv_cancel₀ hw0
    linear_combination (-z) * hcos - z ^ 2 * this
  rw [hx, DLMF.Hypergeometric.mul_cpow_of_re_pos (re_one_sub_mul_pos_of_norm_eq_one hw hz)
    (re_one_sub_mul_pos_of_norm_eq_one hwi hz)]
  exact hasSum_coeff_binomProductSeries_mul_pow lam lam h1 h2


/-- For `|x| ≤ 1`, `x = (w + w⁻¹)/2` with `w = exp (i arccos x)`. -/
theorem ofReal_eq_half_add_recip_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    (x : ℂ) = (exp (Real.arccos x * I) + (exp (Real.arccos x * I))⁻¹) / 2 := by
  rw [← Complex.exp_neg, ← neg_mul, ← Complex.cos, ← Complex.ofReal_cos,
    Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2]

open PowerSeries in
/-- If `∑ coeff n F zⁿ = s` then `∑ coeff n ((1 - aX) F) zⁿ = (1 - a z) s`. -/
theorem hasSum_coeff_one_sub_mul {F : PowerSeries ℂ} {z s : ℂ}
    (hs : HasSum (fun n => coeff n F * z ^ n) s) (a : ℂ) :
    HasSum (fun n => coeff n ((1 - C a * X) * F) * z ^ n) ((1 - a * z) * s) := by
  have hX : HasSum (fun n => coeff n (X * F) * z ^ n) (z * s) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, coeff_zero_X_mul, zero_mul, sub_zero,
      coeff_succ_X_mul]
    convert hs.mul_left z using 1
    funext n; ring
  convert hs.sub (hX.mul_left a) using 1
  · funext n
    rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul]
    ring
  · ring

end DLMF.OrthogonalPolynomials
