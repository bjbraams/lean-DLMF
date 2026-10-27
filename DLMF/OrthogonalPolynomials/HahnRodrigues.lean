/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Hahn
public import Mathlib.Algebra.Group.ForwardDiff

/-!
# The finite Hahn Rodrigues formula

The weight in the existing Hahn orthogonality theorem is extended by zero to
all integers. The Hahn forward difference and second-order difference equation
give the Rodrigues raising step; iteration produces Beals–Wong §§6.2 and 6.6.
-/

@[expose] public noncomputable section

open Complex
open scoped Nat
open DLMF.Hypergeometric

namespace DLMF.OrthogonalPolynomials

/-- The finite Hahn weight with zero extension at both ends of the support. -/
def hahnWeightInt (α β : ℂ) (N : ℕ) (x : ℤ) : ℂ :=
  if 0 ≤ x ∧ x ≤ N then
    poch (α + 1) x.toNat * poch (β + 1) (N - x.toNat) /
      ((x.toNat.factorial : ℂ) * (N - x.toNat).factorial)
  else 0

/-- The Hahn weight at a point of its natural support. -/
theorem hahnWeightInt_nat (α β : ℂ) {N x : ℕ} (hx : x ≤ N) :
    hahnWeightInt α β N x = poch (α + 1) x * poch (β + 1) (N - x) /
      ((x.factorial : ℂ) * (N - x).factorial) := by
  simp [hahnWeightInt, hx]

/-- The Hahn weight vanishes off its support. -/
theorem hahnWeightInt_eq_zero (α β : ℂ) (N : ℕ) {x : ℤ}
    (hx : ¬(0 ≤ x ∧ x ≤ N)) : hahnWeightInt α β N x = 0 := by
  rw [hahnWeightInt, ite_eq_right hx]

/-- The first shifted Hahn weight is the original weight times its forward coefficient. -/
private lemma hahnWeightInt_shift (α β : ℂ) (N : ℕ) (x : ℤ) :
    (α + 1) * (β + 1) * hahnWeightInt (α + 1) (β + 1) N x =
      ((x : ℂ) + α + 1) * ((N : ℂ) + 1 - x) * hahnWeightInt α β (N + 1) x := by
  by_cases hx : 0 ≤ x
  · lift x to ℕ using hx
    by_cases hxN : x ≤ N
    · rw [hahnWeightInt_nat _ _ hxN, hahnWeightInt_nat _ _ (by omega : x ≤ N + 1)]
      have hsub : N + 1 - x = (N - x) + 1 := by omega
      rw [hsub, Nat.factorial_succ]
      have hA := poch_succ_left (α + 1) x
      have hB := poch_succ_left (β + 1) (N - x)
      rw [poch_succ] at hA
      have hN : (N : ℂ) + 1 - x = (N - x : ℕ) + 1 := by push_cast [Nat.cast_sub hxN]; ring
      push_cast
      rw [hN]
      calc
        _ = ((α + 1) * poch (α + 1 + 1) x) *
            ((β + 1) * poch (β + 1 + 1) (N - x)) /
              ((x.factorial : ℂ) * (N - x).factorial) := by ring
        _ = (poch (α + 1) x * (α + 1 + x)) * poch (β + 1) (N - x + 1) /
              ((x.factorial : ℂ) * (N - x).factorial) := by rw [← hA, ← hB]
        _ = _ := by
          have hj : ((N - x : ℕ) : ℂ) + 1 ≠ 0 := by exact_mod_cast (N - x).succ_ne_zero
          rw [show (x.factorial : ℂ) * ((((N - x : ℕ) : ℂ) + 1) * (N - x).factorial) =
            (((N - x : ℕ) : ℂ) + 1) * ((x.factorial : ℂ) * (N - x).factorial) by ring]
          rw [show ((x : ℂ) + α + 1) * (((N - x : ℕ) : ℂ) + 1) *
              (poch (α + 1) x * poch (β + 1) (N - x + 1) /
                ((((N - x : ℕ) : ℂ) + 1) * ((x.factorial : ℂ) * (N - x).factorial))) =
            ((x : ℂ) + α + 1) *
              ((((N - x : ℕ) : ℂ) + 1) * (poch (α + 1) x * poch (β + 1) (N - x + 1)) /
                ((((N - x : ℕ) : ℂ) + 1) * ((x.factorial : ℂ) * (N - x).factorial))) by ring,
            mul_div_mul_left _ _ hj]
          ring
    · by_cases he : x = N + 1
      · subst x
        rw [hahnWeightInt_eq_zero _ _ _ (by omega)]
        push_cast
        ring
      · rw [hahnWeightInt_eq_zero _ _ _ (by omega),
          hahnWeightInt_eq_zero _ _ _ (by omega)]
        ring
  · rw [hahnWeightInt_eq_zero _ _ _ (by omega), hahnWeightInt_eq_zero _ _ _ (by omega)]
    ring

/-- The backward adjacent shifted weight gives the other Hahn difference coefficient. -/
private lemma hahnWeightInt_shift_sub_one (α β : ℂ) (N : ℕ) (x : ℤ) :
    (α + 1) * (β + 1) * hahnWeightInt (α + 1) (β + 1) N (x - 1) =
      (x : ℂ) * ((N : ℂ) + β + 2 - x) * hahnWeightInt α β (N + 1) x := by
  by_cases hx : 0 ≤ x
  · lift x to ℕ using hx
    cases x with
    | zero =>
      rw [hahnWeightInt_eq_zero _ _ _ (by norm_num)]
      simp
    | succ x =>
      have hcast : ((x + 1 : ℕ) : ℤ) - 1 = (x : ℤ) := by omega
      rw [hcast]
      by_cases hxN : x ≤ N
      · rw [hahnWeightInt_nat _ _ hxN,
          hahnWeightInt_nat _ _ (by omega : x + 1 ≤ N + 1)]
        rw [show N + 1 - (x + 1) = N - x by omega, Nat.factorial_succ]
        have hA := poch_succ_left (α + 1) x
        have hB := poch_succ_left (β + 1) (N - x)
        rw [poch_succ] at hB
        have hN : (N : ℂ) + β + 2 - (x + 1) = β + 1 + (N - x : ℕ) := by
          push_cast [Nat.cast_sub hxN]; ring
        push_cast
        rw [hN]
        calc
          _ = ((α + 1) * poch (α + 1 + 1) x) *
              ((β + 1) * poch (β + 1 + 1) (N - x)) /
                ((x.factorial : ℂ) * (N - x).factorial) := by ring
          _ = poch (α + 1) (x + 1) * (poch (β + 1) (N - x) * (β + 1 + (N - x : ℕ))) /
                ((x.factorial : ℂ) * (N - x).factorial) := by rw [← hA, ← hB]
          _ = _ := by
            field_simp [Nat.cast_ne_zero.mpr x.factorial_ne_zero,
              Nat.cast_ne_zero.mpr (N - x).factorial_ne_zero,
              show (x : ℂ) + 1 ≠ 0 by exact_mod_cast x.succ_ne_zero]
      · rw [hahnWeightInt_eq_zero _ _ _ (by omega),
          hahnWeightInt_eq_zero _ _ _ (by omega)]
        ring
  · rw [hahnWeightInt_eq_zero _ _ _ (by omega), hahnWeightInt_eq_zero _ _ _ (by omega)]
    ring

/-- The weighted Hahn raising step, with no division by a weight at an endpoint. -/
private lemma hahn_rodrigues_step {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re)
    {N n : ℕ} (hn : n ≤ N) (x : ℤ) :
    (β + 1) * fwdDiff (-1 : ℤ)
        (fun x => hahnWeightInt (α + 1) (β + 1) N x *
          hahn (α + 1) (β + 1) N n (x : ℂ)) x =
      -((N : ℂ) + 1) * hahnWeightInt α β (N + 1) x *
        hahn α β (N + 1) (n + 1) (x : ℂ) := by
  let ev : ℂ := ((n : ℂ) + 1) * (n + α + β + 2)
  have hev : ev ≠ 0 := by
    apply mul_ne_zero (by exact_mod_cast n.succ_ne_zero)
    apply ne_zero_of_re_pos
    simp only [add_re, natCast_re, show (2 : ℂ).re = 2 by rfl]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hα0 : α + 1 ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have hN0 : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast N.succ_ne_zero
  have hfd (t : ℂ) := hahn_forward_difference (β := β) hα (by omega : n + 1 ≤ N + 1) t
  have hfd' (t : ℂ) : (α + 1) * ((N : ℂ) + 1) *
      (hahn α β (N + 1) (n + 1) (t + 1) - hahn α β (N + 1) (n + 1) t) =
        -ev * hahn (α + 1) (β + 1) N n t := by
    rw [hfd]
    dsimp [ev]
    field_simp
  have hE := hahn_difference_equation (β := β) hα (by omega : n + 1 ≤ N + 1) (x : ℂ)
  have hA := hahnWeightInt_shift α β N x
  have hB := hahnWeightInt_shift_sub_one α β N x
  have h1 := hfd' (x : ℂ)
  have h2 := hfd' ((x : ℂ) - 1)
  rw [sub_add_cancel] at h2
  simp only [fwdDiff, ← sub_eq_add_neg, Int.cast_sub, Int.cast_one]
  apply (mul_left_cancel₀ hev)
  push_cast at hE
  dsimp only [ev] at *
  linear_combination
    -(hahnWeightInt α β (N + 1) x * ((N : ℂ) + 1)) * hE +
    (hahnWeightInt (α + 1) (β + 1) N (x - 1) * (β + 1)) * h2 -
    (hahnWeightInt (α + 1) (β + 1) N x * (β + 1)) * h1 +
    (((N : ℂ) + 1) *
      (hahn α β (N + 1) (n + 1) ((x : ℂ) + 1) - hahn α β (N + 1) (n + 1) x)) * hA -
    (((N : ℂ) + 1) *
      (hahn α β (N + 1) (n + 1) x - hahn α β (N + 1) (n + 1) ((x : ℂ) - 1))) * hB

/-- The `n`th shifted Hahn weight, in the original orthogonality normalization.
For `n ≤ N` it has support `0 ≤ x ≤ N-n` and equals the original weight times the product
of the `n` shifted forward coefficients. -/
def hahnRodriguesWeight (α β : ℂ) (N n : ℕ) (x : ℤ) : ℂ :=
  poch (α + 1) n * poch (β + 1) n * hahnWeightInt (α + n) (β + n) (N - n) x

/-- Consecutive shifted Hahn weights, retaining the finite support exactly. -/
private lemma hahnRodriguesWeight_succ (α β : ℂ) (N n : ℕ) :
    hahnRodriguesWeight α β (N + 1) (n + 1) =
      ((α + 1) * (β + 1)) • hahnRodriguesWeight (α + 1) (β + 1) N n := by
  funext x
  simp only [hahnRodriguesWeight, Pi.smul_apply, smul_eq_mul, poch_succ_left,
    Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one]
  rw [show α + ((n : ℂ) + 1) = (α + 1) + n by ring,
    show β + ((n : ℂ) + 1) = (β + 1) + n by ring]
  ring

/-- The shifted Hahn weight equals the original weight times the product of its
forward coefficients, expressed by two Pochhammer symbols. This identity is valid
at both endpoints and outside the support as well. -/
theorem hahnRodriguesWeight_eq (α β : ℂ) {N n : ℕ} (hn : n ≤ N) (x : ℤ) :
    hahnRodriguesWeight α β N n x = hahnWeightInt α β N x *
      poch ((x : ℂ) + α + 1) n * (-1 : ℂ) ^ n * poch ((x : ℂ) - N) n := by
  induction n generalizing α β N with
  | zero => simp [hahnRodriguesWeight, poch_zero]
  | succ n ih =>
    cases N with
    | zero => omega
    | succ N =>
      rw [hahnRodriguesWeight_succ, Pi.smul_apply, smul_eq_mul, ih (α + 1) (β + 1) (by omega),
        poch_succ_left, poch_succ_left, pow_succ]
      push_cast
      rw [show (x : ℂ) + (α + 1) + 1 = ((x : ℂ) + α + 1) + 1 by ring,
        show (x : ℂ) - ((N : ℂ) + 1) + 1 = (x : ℂ) - N by ring]
      linear_combination (poch ((x : ℂ) + α + 1 + 1) n * (-1 : ℂ) ^ n *
        poch ((x : ℂ) - N) n) * hahnWeightInt_shift α β N x

/-- Hahn's finite Rodrigues formula for all integer arguments, including the support
endpoints. It uses the existing hypergeometric normalization and complex parameters
with real parts greater than `-1`. -/
theorem hahn_rodrigues {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re)
    {N n : ℕ} (hn : n ≤ N) (x : ℤ) :
    (fwdDiff (-1 : ℤ))^[n] (hahnRodriguesWeight α β N n) x =
      poch (α + 1) n * poch (-(N : ℂ)) n * hahnWeightInt α β N x *
        hahn α β N n (x : ℂ) := by
  induction n generalizing α β N x with
  | zero =>
    simp [hahnRodriguesWeight, hahn, terminatingHG, poch_zero]
  | succ n ih =>
    cases N with
    | zero => omega
    | succ N =>
      have hnN : n ≤ N := by omega
      have hα' : -1 < (α + 1).re := by simp; linarith
      have hβ' : -1 < (β + 1).re := by simp; linarith
      have hi : (fwdDiff (-1 : ℤ))^[n] (hahnRodriguesWeight (α + 1) (β + 1) N n) =
          (poch (α + 1 + 1) n * poch (-(N : ℂ)) n) •
            (fun x : ℤ => hahnWeightInt (α + 1) (β + 1) N x *
              hahn (α + 1) (β + 1) N n (x : ℂ)) := by
        funext x
        simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using ih hα' hβ' hnN x
      rw [hahnRodriguesWeight_succ, fwdDiff_iter_const_smul, Pi.smul_apply, smul_eq_mul,
        Function.iterate_succ_apply', hi, fwdDiff_const_smul, Pi.smul_apply, smul_eq_mul,
        poch_succ_left, poch_succ_left]
      push_cast
      rw [show -((N : ℂ) + 1) + 1 = -(N : ℂ) by ring]
      linear_combination ((α + 1) * poch (α + 1 + 1) n * poch (-(N : ℂ)) n) *
        hahn_rodrigues_step hα hβ hnN x

end DLMF.OrthogonalPolynomials
