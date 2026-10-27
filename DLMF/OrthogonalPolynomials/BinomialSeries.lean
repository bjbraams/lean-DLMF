/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Classical
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Products of binomial series

`binomSeries a = ∑ (a)_n / n! Xⁿ` is the formal binomial series `(1 - X)^{-a}`. It satisfies
`(1 - X) G' = a G` and `G_a G_b = G_{a+b}` (Chu–Vandermonde). The product
`binomProductSeries a b u = G_a(uX) G_b(X/u)` satisfies a first-order differential equation,
which gives a three-term recurrence for its coefficients. The coefficients are therefore
identified with any sequence satisfying the same recurrence and initial values; this is used
for the Gegenbauer, Meixner–Pollaczek and Pollaczek polynomials. For `‖u z‖, ‖z / u‖ < 1`
the coefficient series sums to `(1 - u z)^{-a} (1 - z/u)^{-b}`.
-/

@[expose] public section

open Complex
open scoped Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.OrthogonalPolynomials

open PowerSeries in
/-- The binomial series `(1 - X)^{-λ} = ∑ (λ)_n / n! Xⁿ` as a formal power series. -/
def binomSeries (lam : ℂ) : PowerSeries ℂ := PowerSeries.mk fun n => poch lam n / (n.factorial : ℂ)

open PowerSeries in
/-- Coefficients of the binomial series. -/
theorem coeff_binomSeries (lam : ℂ) (n : ℕ) :
    coeff n (binomSeries lam) = poch lam n / (n.factorial : ℂ) := by
  simp [binomSeries]

open PowerSeries in
/-- The binomial series satisfies `(1 - X) G' = λ G`. -/
theorem one_sub_X_mul_derivative_binomSeries (lam : ℂ) :
    (1 - X) * d⁄dX (binomSeries lam) = C lam * binomSeries lam := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_C_mul, coeff_derivative, coeff_binomSeries,
    coeff_binomSeries]
  rcases n with _ | n
  · simp [poch_succ, poch_zero]
  · rw [coeff_succ_X_mul, coeff_derivative, coeff_binomSeries, poch_succ lam (n + 1),
      poch_succ lam n]
    have h1 : ((n + 1 : ℕ) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : ((n : ℕ) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [Nat.factorial_succ (n + 1), Nat.factorial_succ n]
    push_cast
    have h3 : (n : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
    have h4 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp
    ring


open PowerSeries in
/-- Derivative of a rescaled power series. -/
theorem derivative_rescale (a : ℂ) (f : PowerSeries ℂ) :
    d⁄dX (rescale a f) = C a * rescale a (d⁄dX f) := by
  ext n
  simp only [coeff_derivative, coeff_rescale, coeff_C_mul, pow_succ]
  ring

open PowerSeries in
/-- The rescaled binomial series satisfies `(1 - aX) G' = a λ G`. -/
theorem one_sub_mul_derivative_rescale_binomSeries (lam a : ℂ) :
    (1 - C a * X) * d⁄dX (rescale a (binomSeries lam)) =
      C (a * lam) * rescale a (binomSeries lam) := by
  have h := congrArg (rescale a) (one_sub_X_mul_derivative_binomSeries lam)
  rw [map_mul, map_mul, map_sub, map_one, rescale_X] at h
  have hC : rescale a (C lam) = C lam := by
    ext n; rcases n with _ | n <;> simp [coeff_rescale, coeff_C]
  rw [hC] at h
  rw [derivative_rescale, map_mul]
  linear_combination (C a) * h

open PowerSeries in
/-- `G_λ G_μ = G_{λ+μ}` (Chu–Vandermonde). -/
theorem binomSeries_mul (lam μ : ℂ) :
    binomSeries lam * binomSeries μ = binomSeries (lam + μ) := by
  ext n
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_binomSeries,
    ← poch_add_binomial, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [coeff_binomSeries]
  rw [Nat.cast_choose ℂ hkn]
  have h1 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

open PowerSeries in
/-- `(1 - aX) G_1(aX) = 1`: the geometric series. -/
theorem one_sub_mul_rescale_binomSeries_one (a : ℂ) :
    (1 - C a * X) * rescale a (binomSeries 1) = 1 := by
  have hG : binomSeries 1 = mk fun _ => (1 : ℂ) := by
    ext n
    rw [coeff_binomSeries, coeff_mk, poch_nat_one]
    exact div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  ext n
  rw [hG, rescale_mk, sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul]
    simp [pow_succ]
    ring

/-- `‖(λ)_j‖ ≤ (‖λ‖)_j`. -/
theorem norm_poch_le_norm_poch_norm (lam : ℂ) (j : ℕ) : ‖poch lam j‖ ≤ ‖poch (‖lam‖ : ℂ) j‖ := by
  induction j with
  | zero => simp [poch_zero]
  | succ j ih =>
    rw [poch_succ, poch_succ, norm_mul, norm_mul]
    gcongr
    calc ‖lam + j‖ ≤ ‖lam‖ + j := by
          refine (norm_add_le _ _).trans ?_; simp
      _ = ‖(‖lam‖ : ℂ) + j‖ := by
          rw [show (‖lam‖ : ℂ) + j = ((‖lam‖ + j : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- The binomial series converges absolutely in the open unit disk. -/
theorem summable_norm_poch_div_factorial_mul_pow (lam : ℂ) {u : ℂ} (hu : ‖u‖ < 1) :
    Summable fun j : ℕ => ‖poch lam j / (j.factorial : ℂ) * u ^ j‖ := by
  have hr : ‖((‖u‖ : ℝ) : ℂ)‖ < 1 := by simpa using hu
  have hs := (hasSum_poch_div_factorial (β := (‖lam‖ : ℂ)) hr).summable.norm
  refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) fun j => ?_
  rw [norm_mul, norm_mul, norm_div, norm_div, norm_pow, norm_pow]
  gcongr
  · exact norm_poch_le_norm_poch_norm lam j
  · simp


open PowerSeries in
/-- The product `G_a(uX) G_b(X/u)` of two rescaled binomial series. -/
def binomProductSeries (a b u : ℂ) : PowerSeries ℂ :=
  rescale u (binomSeries a) * rescale u⁻¹ (binomSeries b)

open PowerSeries in
/-- The differential equation of `G_a(uX) G_b(X/u)`. -/
theorem binomProductSeries_ode (a b : ℂ) {u : ℂ} (hu : u ≠ 0) :
    (1 - C (u + u⁻¹) * X + X ^ 2) * d⁄dX (binomProductSeries a b u) =
      (C (a * u + b * u⁻¹) - C (a + b) * X) * binomProductSeries a b u := by
  have hA := one_sub_mul_derivative_rescale_binomSeries a u
  have hB := one_sub_mul_derivative_rescale_binomSeries b u⁻¹
  set A := rescale u (binomSeries a)
  set B := rescale u⁻¹ (binomSeries b)
  have this : C u * C u⁻¹ = (1 : PowerSeries ℂ) := by rw [← map_mul, mul_inv_cancel₀ hu, map_one]
  unfold binomProductSeries
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  simp only [map_mul, map_add] at hA hB ⊢
  linear_combination (1 - C u⁻¹ * X) * B * hA + (1 - C u * X) * A * hB +
    (-(C a + C b) * X * A * B - (X ^ 2) * (A * d⁄dX B + B * d⁄dX A)) * this

open PowerSeries in
/-- The three-term recurrence for the coefficients of `G_a(uX) G_b(X/u)`. -/
theorem coeff_binomProductSeries_recurrence (a b : ℂ) {u : ℂ} (hu : u ≠ 0) (n : ℕ) :
    (n + 2 : ℂ) * coeff (n + 2) (binomProductSeries a b u) =
      ((n + 1) * (u + u⁻¹) + a * u + b * u⁻¹) * coeff (n + 1) (binomProductSeries a b u) -
        (n + a + b) * coeff n (binomProductSeries a b u) := by
  have h := congrArg (coeff (n + 1)) (binomProductSeries_ode a b hu)
  set P := binomProductSeries a b u
  set s := u + u⁻¹
  set c := a * u + b * u⁻¹
  set d := a + b
  have hL : (1 - C s * X + X ^ 2) * d⁄dX P =
      d⁄dX P - C s * (X * d⁄dX P) + X * (X * d⁄dX P) := by ring
  have hR : (C c - C d * X) * P = C c * P - C d * (X * P) := by ring
  rw [hL, hR] at h
  simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_derivative] at h
  rcases n with _ | n
  · simp only [coeff_zero_X_mul] at h
    push_cast at h ⊢
    linear_combination h
  · simp only [coeff_succ_X_mul, coeff_derivative] at h
    push_cast at h ⊢
    linear_combination h

open PowerSeries in
/-- The constant coefficient of `G_a(uX) G_b(X/u)`. -/
theorem coeff_zero_binomProductSeries (a b u : ℂ) : coeff 0 (binomProductSeries a b u) = 1 := by
  simp [binomProductSeries, coeff_mul, coeff_rescale, coeff_binomSeries, poch_zero]

open PowerSeries in
/-- The linear coefficient of `G_a(uX) G_b(X/u)`. -/
theorem coeff_one_binomProductSeries (a b u : ℂ) :
    coeff 1 (binomProductSeries a b u) = a * u + b * u⁻¹ := by
  simp [binomProductSeries, coeff_mul, coeff_rescale, coeff_binomSeries,
    Finset.Nat.antidiagonal_succ, poch_succ, poch_zero]
  ring

open PowerSeries in
/-- A sequence with the initial values and the three-term recurrence of
`G_a(uX) G_b(X/u)` is its coefficient sequence. -/
theorem eq_coeff_binomProductSeries {a b u : ℂ} (hu : u ≠ 0) {f : ℕ → ℂ} (h0 : f 0 = 1)
    (h1 : f 1 = a * u + b * u⁻¹)
    (hrec : ∀ n : ℕ, (n + 2 : ℂ) * f (n + 2) =
      ((n + 1) * (u + u⁻¹) + a * u + b * u⁻¹) * f (n + 1) - (n + a + b) * f n) (n : ℕ) :
    f n = coeff n (binomProductSeries a b u) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · rw [h0, coeff_zero_binomProductSeries]
    · rw [h1, coeff_one_binomProductSeries]
    · have hf := hrec n
      have hs := coeff_binomProductSeries_recurrence a b hu n
      rw [ih n (by omega), ih (n + 1) (by omega)] at hf
      have hn2 : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
      exact mul_left_cancel₀ hn2 (hf.trans hs.symm)

open PowerSeries in
/-- Explicit coefficients of `G_a(uX) G_b(X/u)`. -/
theorem coeff_binomProductSeries (a b u : ℂ) (n : ℕ) :
    coeff n (binomProductSeries a b u) = ∑ k ∈ Finset.range (n + 1),
      poch a k * poch b (n - k) / ((k.factorial : ℂ) * (n - k).factorial) *
        (u ^ k * u⁻¹ ^ (n - k)) := by
  rw [binomProductSeries, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [coeff_rescale, coeff_binomSeries]
  ring

open PowerSeries in
/-- The analytic sum of `G_a(uX) G_b(X/u)` where both binomial series converge. -/
theorem hasSum_coeff_binomProductSeries_mul_pow (a b : ℂ) {u z : ℂ} (h1 : ‖u * z‖ < 1)
    (h2 : ‖u⁻¹ * z‖ < 1) :
    HasSum (fun n : ℕ => coeff n (binomProductSeries a b u) * z ^ n)
      ((1 - u * z) ^ (-a) * (1 - u⁻¹ * z) ^ (-b)) := by
  set f : ℕ → ℂ := fun j => poch a j / (j.factorial : ℂ) * (u * z) ^ j with hf
  set g : ℕ → ℂ := fun j => poch b j / (j.factorial : ℂ) * (u⁻¹ * z) ^ j with hg
  have hfs := summable_norm_poch_div_factorial_mul_pow a h1
  have hgs := summable_norm_poch_div_factorial_mul_pow b h2
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfs hgs
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfs hgs).of_norm.hasSum
  rw [← hprod, (hasSum_poch_div_factorial h1).tsum_eq,
    (hasSum_poch_div_factorial h2).tsum_eq] at hsum
  have hcoeff : ∀ n : ℕ, coeff n (binomProductSeries a b u) * z ^ n =
      ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2 := by
    intro n
    rw [binomProductSeries, coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.mem_antidiagonal] at hij
    simp only [coeff_rescale, coeff_binomSeries, hf, hg, mul_pow]
    rw [← hij, pow_add]
    ring
  simpa only [hcoeff] using hsum

end DLMF.OrthogonalPolynomials
