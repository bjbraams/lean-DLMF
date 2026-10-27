/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# Partial fractions for tan, csc and sec (DLMF 4.22.3–4.22.5)

Mathlib proves the Mittag-Leffler expansion of the cotangent (`cot_series_rep'`). From it, with
`tan z = cot z - 2 cot 2z` and `csc z = cot(z/2) - cot z`, this file derives:
* `hasSum_tan_partial_fraction`: `π tan(πx) = ∑ₖ 8x/((2k+1)² - 4x²)` for `2x ∉ ℤ`;
* `hasSum_csc_partial_fraction`: `π/sin(πx) = 1/x + ∑ₙ (-1)ⁿ⁺¹ 2x/(x² - (n+1)²)` for `x ∉ ℤ`;
* `tendsto_sec_partial_fraction`: `π/cos(πx) = ∑ₖ (-1)ᵏ(2k+1)/((k+½)² - x²)`, a conditionally
  convergent series stated through partial sums, from the cosecant at `x + ½`.
The even and odd parts of a summable series are separated with `HasSum.even_add_odd`.
-/

@[expose] public section

open Filter
open scoped Real Topology

noncomputable section

namespace Complex

/-- The Mittag-Leffler series for the cotangent as a `HasSum`. -/
theorem hasSum_cotTerm {x : ℂ} (hx : x ∈ integerComplement) :
    HasSum (fun n => cotTerm x n) (π * cot (π * x) - 1 / x) := by
  rw [cot_series_rep' hx]; exact (summable_cotTerm hx).hasSum

/-- Partial fractions for the tangent (Duverney (2.41)):
`π tan(πx) = ∑ₖ 8x/((2k+1)² - 4x²)` for `2x ∉ ℤ`. -/
theorem hasSum_tan_partial_fraction {x : ℂ} (hx : 2 * x ∈ integerComplement) :
    HasSum (fun k : ℕ => 8 * x / ((2 * k + 1) ^ 2 - 4 * x ^ 2)) (π * tan (π * x)) := by
  have hx1 : x ∈ integerComplement := by
    rintro ⟨n, hn⟩; exact hx ⟨2 * n, by push_cast; rw [hn]⟩
  set f : ℕ → ℂ := fun n => cotTerm (2 * x) n
  have hc2 := hasSum_cotTerm hx
  have hs := hc2.summable
  have he := (hs.comp_injective (mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0))).hasSum
  have ho := (hs.comp_injective (fun a b h => by simpa using h :
    Function.Injective fun k : ℕ => 2 * k + 1)).hasSum
  have htot := (he.even_add_odd ho).unique hc2
  have hc1 := hasSum_cotTerm hx1
  have hodd : (fun n => cotTerm x n) = fun k => 2 * f (2 * k + 1) := by
    funext n
    simp only [f, cotTerm]
    have h1 : x - (n + 1) ≠ 0 := by
      simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hx1 (-(n + 1) : ℤ)
    have h2 : x + (n + 1) ≠ 0 := by
      simpa using integerComplement_add_ne_zero hx1 ((n : ℤ) + 1)
    push_cast
    rw [show 2 * x - (2 * (n : ℂ) + 1 + 1) = 2 * (x - (n + 1)) by ring,
      show 2 * x + (2 * (n : ℂ) + 1 + 1) = 2 * (x + (n + 1)) by ring]
    field_simp
  rw [hodd] at hc1
  have h1val := hc1.unique (ho.mul_left 2)
  have hs1 := sin_pi_mul_ne_zero hx1
  have hs2 := sin_pi_mul_ne_zero hx
  have hcos : cos (π * x) ≠ 0 := by
    intro h; apply hs2; rw [show (π : ℂ) * (2 * x) = 2 * (π * x) by ring, sin_two_mul, h]; ring
  have hx0 : x ≠ 0 := by rintro rfl; exact hx1 ⟨0, by simp⟩
  have htan : (π : ℂ) * tan (π * x) =
      (π * cot (π * x) - 1 / x) - 2 * (π * cot (π * (2 * x)) - 1 / (2 * x)) := by
    rw [tan_eq_sin_div_cos, cot_eq_cos_div_sin, cot_eq_cos_div_sin,
      show (π : ℂ) * (2 * x) = 2 * (π * x) by ring, sin_two_mul, cos_two_mul]
    field_simp
    have := sin_sq_add_cos_sq ((π : ℂ) * x)
    linear_combination ((π : ℂ) * x) * this
  have hfun : (fun k : ℕ => 8 * x / ((2 * k + 1) ^ 2 - 4 * x ^ 2)) =
      fun k => -2 * ((fun n => cotTerm (2 * x) n) ∘ fun k => 2 * k) k := by
    funext k
    simp only [Function.comp, cotTerm]
    have h1 : 2 * x - ((2 * k : ℕ) + 1) ≠ 0 := by
      simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hx (-((2 * k : ℕ) + 1) : ℤ)
    have h2 : 2 * x + ((2 * k : ℕ) + 1) ≠ 0 := by
      simpa using integerComplement_add_ne_zero hx (((2 * k : ℕ) : ℤ) + 1)
    have h3 : ((2 * k + 1 : ℂ)) ^ 2 - 4 * x ^ 2 ≠ 0 := by
      rw [show ((2 * k + 1 : ℂ)) ^ 2 - 4 * x ^ 2 = -((2 * x - ((2 * k : ℕ) + 1)) *
        (2 * x + ((2 * k : ℕ) + 1))) by push_cast; ring]
      exact neg_ne_zero.mpr (mul_ne_zero h1 h2)
    push_cast at h1 h2 ⊢
    have hx4 : 4 * x = (2 * x - (2 * k + 1)) + (2 * x + (2 * k + 1)) := by ring
    rw [show (2 * (k : ℂ) + 1) ^ 2 - 4 * x ^ 2 =
      -((2 * x - (2 * k + 1)) * (2 * x + (2 * k + 1))) by ring,
      show (8 : ℂ) * x = 2 * (4 * x) by ring, hx4]
    generalize 2 * x - (2 * (k : ℂ) + 1) = u at *
    generalize 2 * x + (2 * (k : ℂ) + 1) = v at *
    field_simp
    ring
  rw [hfun, htan, h1val, ← htot]
  convert he.mul_left (-2) using 1
  ring

/-- Partial fractions for the cosecant (DLMF 4.22.5, Duverney (2.43)):
`π/sin(πx) = 1/x + ∑ₙ (-1)ⁿ⁺¹ 2x/(x² - (n+1)²)` for `x ∉ ℤ`. -/
@[dlmf 4.22.E5]
theorem hasSum_csc_partial_fraction {x : ℂ} (hx : x ∈ integerComplement) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ (n + 1) * cotTerm x n) (π / sin (π * x) - 1 / x) := by
  have hx2 : x / 2 ∈ integerComplement := by
    rintro ⟨n, hn⟩; exact hx ⟨2 * n, by push_cast; rw [hn]; ring⟩
  have hc1 := hasSum_cotTerm hx
  have hs := hc1.summable
  have he := (hs.comp_injective (mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0))).hasSum
  have ho := (hs.comp_injective (fun a b h => by simpa using h :
    Function.Injective fun k : ℕ => 2 * k + 1)).hasSum
  have htot := (he.even_add_odd ho).unique hc1
  have hc2 := hasSum_cotTerm hx2
  have hhalf : (fun n => cotTerm (x / 2) n) = fun k => 2 * cotTerm x (2 * k + 1) := by
    funext n
    simp only [cotTerm]
    have h1 : x - (2 * n + 2) ≠ 0 := by
      simpa [sub_eq_add_neg, two_mul] using integerComplement_add_ne_zero hx (-(2 * n + 2) : ℤ)
    have h2 : x + (2 * n + 2) ≠ 0 := by
      simpa [two_mul] using integerComplement_add_ne_zero hx ((2 * n : ℤ) + 2)
    push_cast
    rw [show x / 2 - ((n : ℂ) + 1) = (x - (2 * n + 2)) / 2 by ring,
      show x / 2 + ((n : ℂ) + 1) = (x + (2 * n + 2)) / 2 by ring,
      show x - (2 * (n : ℂ) + 1 + 1) = x - (2 * n + 2) by ring,
      show x + (2 * (n : ℂ) + 1 + 1) = x + (2 * n + 2) by ring]
    field_simp
  rw [hhalf] at hc2
  have h2val := hc2.unique (ho.mul_left 2)
  have hs1 := sin_pi_mul_ne_zero hx
  have hs2 := sin_pi_mul_ne_zero hx2
  have hx0 : x ≠ 0 := by rintro rfl; exact hx ⟨0, by simp⟩
  have hcsc : (π : ℂ) / sin (π * x) - 1 / x =
      (π * cot (π * (x / 2)) - 1 / (x / 2)) - (π * cot (π * x) - 1 / x) := by
    rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin,
      show (π : ℂ) * x = 2 * (π * (x / 2)) by ring, sin_two_mul, cos_two_mul]
    rw [show (π : ℂ) * x = 2 * (π * (x / 2)) by ring, sin_two_mul] at hs1
    generalize (π : ℂ) * (x / 2) = w at *
    have hc : cos w ≠ 0 := fun h => hs1 (by rw [h]; ring)
    have hsw : sin w ≠ 0 := fun h => hs1 (by rw [h]; ring)
    field_simp
    ring
  rw [hcsc, h2val, ← htot]
  have he' : HasSum (fun k => (-1 : ℂ) ^ (2 * k + 1) * cotTerm x (2 * k))
      (-∑' b, ((fun n => cotTerm x n) ∘ fun x => 2 * x) b) :=
    he.neg.congr_fun fun k => by simp [pow_succ, pow_mul]
  have ho' : HasSum (fun k => (-1 : ℂ) ^ (2 * k + 1 + 1) * cotTerm x (2 * k + 1))
      (∑' b, ((fun n => cotTerm x n) ∘ fun k => 2 * k + 1) b) :=
    ho.congr_fun fun k => by simp [pow_succ, pow_mul]
  convert HasSum.even_add_odd (f := fun n => (-1 : ℂ) ^ (n + 1) * cotTerm x n) he' ho' using 1
  ring

/-- Partial fractions for the secant (Duverney (2.44)): for `x + ½ ∉ ℤ`, the
partial sums of `∑ₖ (-1)ᵏ (2k+1)/((k+½)² - x²)` tend to `π/cos(πx)`. The series converges only
conditionally. -/
theorem tendsto_sec_partial_fraction {x : ℂ} (hx : x + 1 / 2 ∈ integerComplement) :
    Tendsto (fun N => ∑ k ∈ Finset.range N,
      (-1 : ℂ) ^ k * (2 * k + 1) / ((k + 1 / 2) ^ 2 - x ^ 2)) atTop (𝓝 (π / cos (π * x))) := by
  set y := x + 1 / 2 with hy
  have hc := hasSum_csc_partial_fraction hx
  have hsin : sin (π * y) = cos (π * x) := by
    rw [hy, mul_add, show (π : ℂ) * (1 / 2) = π / 2 by ring, sin_add_pi_div_two]
  rw [hsin] at hc
  have hne1 (k : ℕ) : y - (k + 1) ≠ 0 := by
    simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hx (-(k + 1) : ℤ)
  have hne2 (k : ℕ) : y + k ≠ 0 := by
    simpa using integerComplement_add_ne_zero hx (k : ℤ)
  -- the terms split as `Aₖ + (-1)ᵏ/(y+k)`
  have hT (k : ℕ) : (-1 : ℂ) ^ k * (2 * k + 1) / ((k + 1 / 2) ^ 2 - x ^ 2) =
      (-1 : ℂ) ^ (k + 1) / (y - (k + 1)) + (-1 : ℂ) ^ k / (y + k) := by
    have h1 := hne1 k
    have h2 := hne2 k
    rw [show ((k : ℂ) + 1 / 2) ^ 2 - x ^ 2 = -((y - (k + 1)) * (y + k)) by rw [hy]; ring,
      show (2 * (k : ℂ) + 1) = (y + k) - (y - (k + 1)) by rw [hy]; ring]
    generalize y - (k + 1) = u at *
    generalize y + k = v at *
    field_simp
    ring
  have hpart (N : ℕ) : ∑ k ∈ Finset.range (N + 1),
      (-1 : ℂ) ^ k * (2 * k + 1) / ((k + 1 / 2) ^ 2 - x ^ 2) =
      ∑ n ∈ Finset.range N, (-1 : ℂ) ^ (n + 1) * cotTerm y n + 1 / y +
        (-1 : ℂ) ^ (N + 1) / (y - (N + 1)) := by
    induction N with
    | zero =>
      rw [Finset.sum_range_one, hT 0]
      simp only [Finset.range_zero, Finset.sum_empty]
      push_cast; ring
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, hT, Finset.sum_range_succ]
      simp only [cotTerm]
      push_cast
      ring
  have hA : Tendsto (fun N : ℕ => (-1 : ℂ) ^ (N + 1) / (y - (N + 1))) atTop (𝓝 0) := by
    have hn : Tendsto (fun N : ℕ => y - ((N : ℂ) + 1)) atTop (Bornology.cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]
      refine tendsto_atTop_mono (fun N => ?_) (tendsto_atTop_add_const_right _ (-‖y‖ - 1)
        tendsto_natCast_atTop_atTop)
      have := norm_sub_norm_le ((N : ℂ) + 1) y
      rw [norm_sub_rev] at this
      have h1 : ‖(N : ℂ) + 1‖ = N + 1 := by
        rw [show (N : ℂ) + 1 = ((N + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
        push_cast; ring
      linarith
    have hb : ∀ N : ℕ, ‖(-1 : ℂ) ^ (N + 1)‖ ≤ 1 := fun N => by simp
    have := tendsto_inv₀_cobounded.comp hn
    refine squeeze_zero_norm (fun N => ?_) (tendsto_norm_zero.comp this)
    rw [div_eq_mul_inv, norm_mul]
    simp only [Function.comp]
    calc ‖(-1 : ℂ) ^ (N + 1)‖ * ‖(y - ((N : ℂ) + 1))⁻¹‖ ≤ 1 * ‖(y - ((N : ℂ) + 1))⁻¹‖ := by
          gcongr; exact hb N
      _ = _ := one_mul _
  have hlim : Tendsto (fun N => ∑ k ∈ Finset.range (N + 1),
      (-1 : ℂ) ^ k * (2 * k + 1) / ((k + 1 / 2) ^ 2 - x ^ 2)) atTop (𝓝 (π / cos (π * x))) := by
    simp_rw [hpart]
    have := (hc.tendsto_sum_nat.add_const (1 / y)).add hA
    rwa [sub_add_cancel, add_zero] at this
  exact (tendsto_add_atTop_iff_nat 1).mp hlim

end Complex

end
