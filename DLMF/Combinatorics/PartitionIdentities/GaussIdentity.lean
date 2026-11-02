/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.NumberTheory.RamanujanCongruences

/-!
# Gauss's triangular-number identity

Gauss's identity `∏_{m≥1} (1 - xᵐ)(1 + xᵐ)² = ∑_{n≥0} x^{n(n+1)/2}` follows from the product
formula for `θ₂(0|τ)` (DLMF 20.4.3) and the cosine series of `θ₂` (DLMF 20.2.2). Multiplied by
`∏ (1 - xᵐ)`, it becomes `(∑ x^{n(n+1)/2}) ∏ (1 - xᵐ) = (∏ (1 - x^{2m}))²`, which is transferred
to `ℤ⟦X⟧` by the uniqueness of power series coefficients. It is used for DLMF 26.10.8.

## Main definitions

* `DLMF.Combinatorics.triangularSeries`: the series `∑_{n≥0} X^{n(n+1)/2}` in `ℤ⟦X⟧`.

## Main results

* `DLMF.Combinatorics.hasSum_pow_triangular_mul_eulerFunction`: Gauss's identity in the unit
  disc, in the form `(∑ x^{n(n+1)/2}) f(x) = f(x²)²`.
* `DLMF.Combinatorics.expand_pentagonalSeries_sq`: the same identity in `ℤ⟦X⟧`.
-/

@[expose] public section

open Complex Filter Topology DLMF.Elliptic DLMF.Theta
open scoped Real

namespace DLMF.Combinatorics

open PowerSeries

private lemma two_mul_triangle (n : ℕ) : 2 * (n * (n + 1) / 2) = n * (n + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd

private lemma triangle_strictMono : StrictMono (fun n : ℕ ↦ n * (n + 1) / 2) := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  have h1 := two_mul_triangle n
  have h2 := two_mul_triangle (n + 1)
  nlinarith

/-- Gauss's identity `∏ (1 - xᵐ)(1 + xᵐ)² = ∑ x^{n(n+1)/2}` for `0 < |x| < 1`. -/
private theorem hasSum_pow_tri_of_ne_zero {x : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ < 1) :
    Multipliable (fun k : ℕ => (1 - x ^ (k + 1)) * (1 + x ^ (k + 1)) ^ 2) ∧
    HasSum (fun n : ℕ => x ^ (n * (n + 1) / 2))
      (∏' k : ℕ, ((1 - x ^ (k + 1)) * (1 + x ^ (k + 1)) ^ 2)) := by
  set τ : ℂ := Complex.log x / (2 * π * I) with hτdef
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hτI : 2 * π * I * τ = Complex.log x := by
    rw [hτdef]; field_simp
  have hτ : 0 < τ.im := by
    have : τ = -(I * Complex.log x) / (2 * π) := by
      rw [hτdef]; field_simp; rw [show I ^ 2 = -1 from I_sq]; ring
    rw [this, show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring, div_ofReal_im]
    simp only [neg_im, mul_im, I_re, zero_mul, I_im, one_mul, zero_add, log_re]
    have hl : Real.log ‖x‖ < 0 := Real.log_neg (norm_pos_iff.mpr hx0) hx
    have := Real.pi_pos
    exact div_pos (by linarith) (by positivity)
  set E := cexp (π * I * τ) with hE
  have hE2 : E ^ 2 = x := by
    rw [hE, ← exp_nat_mul, show ((2 : ℕ) : ℂ) * (π * I * τ) = 2 * π * I * τ by push_cast; ring,
      hτI, exp_log hx0]
  obtain ⟨hm, hprod⟩ := jacobiThetaTwoNullTau_prod hτ
  have hser := jacobiThetaTwoTau_hasSum_cos 0 hτ
  have hEk : ∀ k : ℕ, E ^ (2 * (k + 1)) = x ^ (k + 1) := fun k ↦ by rw [pow_mul, hE2]
  simp_rw [← hE, hEk] at hm hprod
  refine ⟨hm, ?_⟩
  rw [show jacobiThetaTwoTau 0 τ = jacobiThetaTwoNullTau τ from rfl, hprod] at hser
  set C : ℂ := 2 * cexp (π * I * τ / 4) with hC
  have hC0 : C ≠ 0 := mul_ne_zero two_ne_zero (exp_ne_zero _)
  have hterm : ∀ n : ℕ, 2 * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) * cos ((2 * n + 1) * 0) =
      C * x ^ (n * (n + 1) / 2) := by
    intro n
    have hm : n * (n + 1) / 2 * 2 = n * (n + 1) :=
      Nat.div_mul_cancel (Nat.even_mul_succ_self n).two_dvd
    have : x ^ (n * (n + 1) / 2) = cexp (π * I * τ * ((n : ℂ) * (n + 1))) := by
      rw [← hE2, ← pow_mul, mul_comm 2, hm, hE, ← exp_nat_mul]; push_cast; ring_nf
    rw [this, hC, mul_zero, cos_zero, mul_one]
    have e : cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) =
        cexp (π * I * τ / 4) * cexp (π * I * τ * ((n : ℂ) * (n + 1))) := by
      rw [← exp_add]; congr 1; ring
    rw [e]; ring
  simp_rw [hterm] at hser
  exact (hasSum_mul_left_iff hC0).mp hser

/-- Gauss's identity in the form `(∑ x^{n(n+1)/2}) f(x) = f(x²)²`, `f(x) = ∏ (1 - xᵐ)`. -/
theorem hasSum_pow_triangular_mul_eulerFunction {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => x ^ (n * (n + 1) / 2) * eulerFunction x)
      (eulerFunction (x ^ 2) ^ 2) := by
  have hx2 : ‖x ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg x]
  rcases eq_or_ne x 0 with rfl | hx0
  · have h1 : eulerFunction (0 : ℂ) = 1 := by
      rw [← (hasProd_eulerFunction hx).tprod_eq]; simp
    rw [show (0 : ℂ) ^ 2 = 0 by simp, h1, one_pow]
    convert hasSum_ite_eq 0 (1 : ℂ) using 1
    funext n
    rcases n with _ | n
    · simp
    · have : (n + 1) * (n + 1 + 1) / 2 ≠ 0 := by
        rw [Nat.div_ne_zero_iff_of_dvd (Nat.even_mul_succ_self _).two_dvd]; simp
      simp [this]
  · obtain ⟨hm, hs⟩ := hasSum_pow_tri_of_ne_zero hx0 hx
    convert hs.mul_right (eulerFunction x) using 1
    have hE := hasProd_eulerFunction hx
    have hE2 := (hasProd_eulerFunction hx2).pow 2
    rw [← hE.tprod_eq, ← hE2.tprod_eq, ← hm.tprod_mul hE.multipliable]
    congr 1; funext k; ring


/-- The series `∑_{n≥0} X^{n(n+1)/2}` of triangular powers in `ℤ⟦X⟧`. -/
noncomputable def triangularSeries : PowerSeries ℤ :=
  PowerSeries.mk (Function.extend (fun n : ℕ ↦ n * (n + 1) / 2) (fun _ ↦ (1 : ℤ)) 0)

/-- The coefficient of `triangularSeries` at a triangular number is `1`. -/
theorem coeff_triangularSeries_tri (n : ℕ) : coeff (n * (n + 1) / 2) triangularSeries = 1 := by
  rw [triangularSeries, coeff_mk]
  exact triangle_strictMono.injective.extend_apply _ _ _

/-- The coefficient of `triangularSeries` at a non-triangular number is `0`. -/
theorem coeff_triangularSeries_eq_zero {m : ℕ} (h : ∀ n, n * (n + 1) / 2 ≠ m) :
    coeff m triangularSeries = 0 := by
  rw [triangularSeries, coeff_mk]
  exact Function.extend_apply' _ _ _ (by simpa using h)

private lemma hasSumAt_triangularSeries {x : ℂ} (hx : ‖x‖ < 1) :
    PowerSeries.HasSumAt triangularSeries x (∑' n : ℕ, x ^ (n * (n + 1) / 2)) := by
  have hsum : Summable (fun n : ℕ ↦ x ^ (n * (n + 1) / 2)) := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg x) hx) fun n ↦ ?_
    rw [norm_pow]
    refine pow_le_pow_of_le_one (norm_nonneg x) hx.le ?_
    have : n * 2 ≤ n * (n + 1) := by rcases n with _ | n <;> [simp; nlinarith]
    exact (Nat.le_div_iff_mul_le two_pos).mpr this
  rw [PowerSeries.hasSumAt_int_iff, ← triangle_strictMono.injective.hasSum_iff]
  · convert hsum.hasSum using 1
    funext n
    simp [coeff_triangularSeries_tri]
  · intro m hm
    rw [coeff_triangularSeries_eq_zero (by simpa using hm)]
    simp

private lemma hasSumAt_expand_pentagonalSeries {x : ℂ} (hx : ‖x‖ < 1) :
    PowerSeries.HasSumAt (expand 2 two_ne_zero (pentagonalSeries ℤ)) x (eulerFunction (x ^ 2)) := by
  have hx2 : ‖x ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg x]
  have h := DLMF.NumberTheory.RamanujanCongruences.hasSumAt_pentagonalSeries hx2
  rw [PowerSeries.hasSumAt_int_iff] at h ⊢
  have hinj : Function.Injective (fun j : ℕ ↦ 2 * j) := fun a b h ↦ by simpa using h
  rw [← hinj.hasSum_iff]
  · convert h using 1
    funext j
    simp [coeff_expand_mul, pow_mul]
  · intro m hm
    have : ¬ 2 ∣ m := by
      rintro ⟨j, rfl⟩; exact hm ⟨j, rfl⟩
    simp [coeff_expand_of_not_dvd 2 two_ne_zero _ this]

/-- Gauss's identity as a formal power series identity:
`(∏ (1 - X^{2m}))² = (∑ X^{n(n+1)/2}) ∏ (1 - Xᵐ)` in `ℤ⟦X⟧`. -/
theorem expand_pentagonalSeries_sq :
    expand 2 two_ne_zero (pentagonalSeries ℤ) ^ 2 = triangularSeries * pentagonalSeries ℤ := by
  have key := Complex.eq_of_hasSum_mul_pow_ball (ρ := 1) one_pos
    (c := fun n ↦ ((coeff n (expand 2 two_ne_zero (pentagonalSeries ℤ) ^ 2) : ℤ) : ℂ))
    (d := fun n ↦ ((coeff n (triangularSeries * pentagonalSeries ℤ) : ℤ) : ℂ))
    (g := fun x ↦ eulerFunction (x ^ 2) ^ 2)
    (fun x hx ↦ by
      simpa [PowerSeries.hasSumAt_int_iff] using (hasSumAt_expand_pentagonalSeries hx).pow 2)
    (fun x hx ↦ by
      have h := (hasSumAt_triangularSeries hx).mul
        (DLMF.NumberTheory.RamanujanCongruences.hasSumAt_pentagonalSeries hx)
      have he : (∑' n : ℕ, x ^ (n * (n + 1) / 2)) * eulerFunction x =
          eulerFunction (x ^ 2) ^ 2 := by
        have hs : Summable (fun n : ℕ ↦ x ^ (n * (n + 1) / 2)) := by
          have := hasSumAt_triangularSeries hx
          rw [PowerSeries.hasSumAt_int_iff, ← triangle_strictMono.injective.hasSum_iff] at this
          · simpa [Function.comp_def, coeff_triangularSeries_tri] using this.summable
          · intro m hm
            rw [coeff_triangularSeries_eq_zero (by simpa using hm)]
            simp
        exact (hs.hasSum.mul_right _).unique (hasSum_pow_triangular_mul_eulerFunction hx)
      rw [he] at h
      simpa [PowerSeries.hasSumAt_int_iff] using h)
  ext n
  exact_mod_cast congr_fun key n

end DLMF.Combinatorics
