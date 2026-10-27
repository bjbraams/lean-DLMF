/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.SphericalSeriesTools

/-!
# Series in products of spherical Bessel functions (DLMF §§6.10, 10.51, 10.60)

The series `Cin(z) = ∑ aₙ jₙ(z/2)²` of DLMF 6.10.5 does not telescope termwise. It is reduced
here to three sums of squares of spherical Bessel functions, each of which does telescope:

* `sphProd_hasSum_sq`: `∑ (2n+1) jₙ(z)² = 1`;
* `sphProd_hasSum_alt_mul`: `∑ (-1)ⁿ (2n+1) jₙ(x) jₙ(y) = j₀(x+y)` (a case of the addition
  theorem DLMF 10.60.2); along the line `x + y = const` the derivative of the `n`-th term is a
  difference `Eₙ - Eₙ₊₁` of antisymmetric products;
* `sphProd_hasSum_alt_sq`: `∑ (-1)ⁿ (2n+1) jₙ(z)² = j₀(2z)`.

Also provided: the unified derivative `(2n+1) jₙ' = n jₙ₋₁ - (n+1) jₙ₊₁` (DLMF 10.51.2),
the Euler form `z jₙ'(z) = n jₙ(z) - z jₙ₊₁(z)`, the values `jₙ(0)`, and summable bounds for
spherical Bessel functions weighted by geometrically growing coefficients.
-/

@[expose] public noncomputable section
open Complex Filter Set
open scoped Real Topology Nat

namespace DLMF

/-! ### Values and derivatives -/

/-- `jₙ(0) = 0` for `n ≥ 1`. -/
theorem sphProd_sphericalJ_succ_zero (n : ℕ) : sphericalJ (n+1) 0 = 0 := by
  simp [sphericalJ]

/-- Unified derivative `(2n+1) jₙ' = n jₙ₋₁ - (n+1) jₙ₊₁` (DLMF 10.51.2); the term `n jₙ₋₁`
vanishes at `n = 0`. -/
theorem sphProd_hasDerivAt_sphericalJ (n : ℕ) (z : ℂ) :
    HasDerivAt (sphericalJ n)
      ((n * sphericalJ (n-1) z - (n+1) * sphericalJ (n+1) z) / (2*n+1)) z := by
  rcases n with _ | n
  · simpa using sphSeries_hasDerivAt_sphericalJ_zero z
  · refine (sphSeries_hasDerivAt_sphericalJ_succ n z).congr_deriv ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

/-- Euler form of the derivative: `z jₙ'(z) = n jₙ(z) - z jₙ₊₁(z)` (DLMF 10.51.2). -/
theorem sphProd_mul_deriv_sphericalJ (n : ℕ) (z : ℂ) :
    z * ((n * sphericalJ (n-1) z - (n+1) * sphericalJ (n+1) z) / (2*n+1)) =
      n * sphericalJ n z - z * sphericalJ (n+1) z := by
  have h3 : (2*n+1 : ℂ) ≠ 0 := by
    have : (0:ℝ) < 2*n+1 := by positivity
    exact_mod_cast this.ne'
  rcases n with _ | n
  · simp
  · have hr := sphSeries_sphericalJ_recurrence n z
    simp only [Nat.add_sub_cancel]
    push_cast at h3 ⊢
    rw [mul_div_assoc', div_eq_iff h3]
    linear_combination ((n:ℂ)+1) * hr

/-- Derivative of a square: `(2n+1) (jₙ²)' = 2 (qₙ - qₙ₊₁)` with `qₙ = n jₙ₋₁ jₙ`. -/
theorem sphProd_hasDerivAt_sphericalJ_sq (n : ℕ) (z : ℂ) :
    HasDerivAt (fun w => sphericalJ n w ^ 2)
      (2 * (n * sphericalJ (n-1) z * sphericalJ n z -
        ((n+1:ℕ):ℂ) * sphericalJ n z * sphericalJ (n+1) z) / (2*n+1)) z := by
  refine ((sphProd_hasDerivAt_sphericalJ n z).pow 2).congr_deriv ?_
  push_cast
  ring

/-! ### Bounds -/

/-- The bound of `sphSeries_norm_sphericalJ_le` absorbs geometric weights. -/
theorem sphProd_bound (R : ℝ) : ∃ u : ℕ → ℝ, (∀ ρ : ℝ, 0 ≤ ρ → Summable (fun n => ρ^n * u n)) ∧
    (∀ n, 0 ≤ u n) ∧ ∀ n z, ‖z‖ ≤ R → ‖sphericalJ n z‖ ≤ u n := by
  set B : ℝ → ℕ → ℝ := fun S n => Real.sqrt π * S^n / 2^(n+1) *
    (Real.exp (S^2/4) / Real.Gamma (n+3/2)) with hB
  have hB0 : ∀ S, 0 ≤ S → ∀ n, 0 ≤ B S n := fun S hS n => by
    have : 0 < Real.Gamma ((n:ℝ)+3/2) := Real.Gamma_pos_of_pos (by positivity)
    simp only [hB]; positivity
  refine ⟨B |R|, fun ρ hρ => ?_, hB0 _ (abs_nonneg R), fun n z hz => ?_⟩
  · have hs := (sphSeries_summable_bound (mul_nonneg hρ (abs_nonneg R))).mul_left
      (Real.exp (|R|^2/4) / Real.exp ((ρ*|R|)^2/4))
    refine hs.congr fun n => ?_
    simp only [hB]
    have he : (0:ℝ) < Real.exp ((ρ*|R|)^2/4) := Real.exp_pos _
    have hG : 0 < Real.Gamma ((n:ℝ) + 3/2) := Real.Gamma_pos_of_pos (by positivity)
    field_simp
    ring
  · have hz' : ‖z‖ ≤ |R| := hz.trans (le_abs_self R)
    refine (sphSeries_norm_sphericalJ_le n z).trans ?_
    have hG : 0 < Real.Gamma ((n:ℝ) + 3/2) := Real.Gamma_pos_of_pos (by positivity)
    simp only [hB]
    gcongr

/-- A uniform bound for all `jₙ` on a closed ball. -/
theorem sphProd_bound_uniform (R : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ n z, ‖z‖ ≤ R → ‖sphericalJ n z‖ ≤ M := by
  obtain ⟨u, hu, hu0, h⟩ := sphProd_bound R
  have hs : Summable u := by simpa using hu 1 zero_le_one
  exact ⟨∑' k, u k, tsum_nonneg hu0, fun n z hz =>
    (h n z hz).trans (hs.le_tsum n (fun k _ => hu0 k))⟩

/-- Summable bounds on balls for `cₙ jₙ(w) j_{σ n}(w)`, `‖cₙ‖ ≤ C ρⁿ`. -/
theorem sphProd_bound_coeff_mul (c : ℕ → ℂ) {C ρ : ℝ} (hρ : 0 ≤ ρ) (hc : ∀ n, ‖c n‖ ≤ C * ρ^n)
    (σ : ℕ → ℕ) (R : ℝ) : ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n w, ‖w‖ ≤ R → ‖c n * sphericalJ n w * sphericalJ (σ n) w‖ ≤ u n := by
  obtain ⟨u, hu, hu0, h⟩ := sphProd_bound R
  obtain ⟨M, hM0, hM⟩ := sphProd_bound_uniform R
  refine ⟨fun n => C * M * (ρ^n * u n), (hu ρ hρ).mul_left _, fun n w hw => ?_⟩
  rw [norm_mul, norm_mul]
  have hC : 0 ≤ C := le_trans (norm_nonneg _) ((hc 0).trans (by simp))
  calc ‖c n‖ * ‖sphericalJ n w‖ * ‖sphericalJ (σ n) w‖ ≤ (C * ρ^n) * u n * M :=
        mul_le_mul (mul_le_mul (hc n) (h n w hw) (norm_nonneg _) (by positivity)) (hM _ w hw)
          (norm_nonneg _) (by have := hu0 n; positivity)
    _ = _ := by ring

/-- Summability of `cₙ jₙ(w) j_{σ n}(w)` at a point, `‖cₙ‖ ≤ C ρⁿ`. -/
theorem sphProd_summable_coeff_mul (c : ℕ → ℂ) {C ρ : ℝ} (hρ : 0 ≤ ρ) (hc : ∀ n, ‖c n‖ ≤ C * ρ^n)
    (σ : ℕ → ℕ) (w : ℂ) : Summable (fun n => c n * sphericalJ n w * sphericalJ (σ n) w) := by
  obtain ⟨u, hu, h⟩ := sphProd_bound_coeff_mul c hρ hc σ ‖w‖
  exact Summable.of_norm_bounded hu (fun n => h n w le_rfl)

/-- `2n+1 ≤ 2·2ⁿ`. -/
theorem sphProd_two_mul_add_one_le (n : ℕ) : (2*n+1 : ℝ) ≤ 2 * 2^n := by
  have h : (n:ℝ) + 1 ≤ 2^n := by
    have := Nat.lt_two_pow_self (n := n)
    exact_mod_cast this
  linarith [show (n:ℝ) ≤ n + 1 by linarith]

/-! ### Sums of squares -/

/-- `∑ (2n+1) jₙ(z)² = 1` (DLMF 10.60). -/
theorem sphProd_hasSum_sq (z : ℂ) :
    HasSum (fun n : ℕ => (2*n+1 : ℂ) * sphericalJ n z ^ 2) 1 := by
  refine sphSeries_hasSum_of_hasDerivAt (f := fun n w => (2*n+1 : ℂ) * sphericalJ n w ^ 2)
    (g := fun n w => 2 * (n * sphericalJ (n-1) w * sphericalJ n w)) (F := fun _ => 1)
    (fun n w => ?_) (fun w => ?_) (fun R => ?_) (fun w => ?_) ?_ z
  · have h := (sphProd_hasDerivAt_sphericalJ_sq n w).const_mul (2*n+1 : ℂ)
    refine h.congr_deriv ?_
    have h3 : (2*n+1 : ℂ) ≠ 0 := by
      have : (0:ℝ) < 2*n+1 := by positivity
      exact_mod_cast this.ne'
    simp only [Nat.add_sub_cancel]
    field_simp
  · -- `2 n jₙ₋₁ jₙ → 0`
    obtain ⟨u, hu, hu0, h⟩ := sphProd_bound ‖w‖
    obtain ⟨M, hM0, hM⟩ := sphProd_bound_uniform ‖w‖
    have ht := ((hu 2 zero_le_two).tendsto_atTop_zero).const_mul (2*M)
    rw [mul_zero] at ht
    refine squeeze_zero_norm (fun n => ?_) ht
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast]
    simp only [Complex.norm_ofNat]
    have hn : (n:ℝ) ≤ 2^n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
    calc 2 * ((n:ℝ) * ‖sphericalJ (n-1) w‖ * ‖sphericalJ n w‖) ≤ 2 * (2^n * M * u n) := by
          gcongr
          · exact hM _ w le_rfl
          · exact h n w le_rfl
      _ = _ := by ring
  · obtain ⟨u, hu, h⟩ := sphProd_bound_coeff_mul (fun n => (2*n+1 : ℂ)) (C := 2) (ρ := 2)
      zero_le_two (fun n => by
        have : ‖(2*(n:ℂ)+1)‖ = 2*n+1 := by
          rw [show (2*(n:ℂ)+1) = ((2*n+1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
            Real.norm_of_nonneg (by positivity)]
        rw [this]; exact sphProd_two_mul_add_one_le n) id R
    exact ⟨u, hu, fun n w hw => by simpa [sq, mul_assoc] using h n w hw.le⟩
  · simpa using hasDerivAt_const w (1:ℂ)
  · rw [← hasSum_nat_add_iff' 1]
    simp [sphProd_sphericalJ_succ_zero, sphSeries_sphericalJ_zero_zero]

/-- Two-variable alternating sum along a line: `∑ (-1)ⁿ (2n+1) jₙ(2u-w) jₙ(w) = j₀(2u)`. -/
theorem sphProd_hasSum_alt_line (u w : ℂ) :
    HasSum (fun n : ℕ => (-1:ℂ)^n * (2*n+1) * sphericalJ n (2*u-w) * sphericalJ n w)
      (sphericalJ 0 (2*u)) := by
  refine sphSeries_hasSum_of_hasDerivAt
    (f := fun n v => (-1:ℂ)^n * (2*n+1) * sphericalJ n (2*u-v) * sphericalJ n v)
    (g := fun n v => (-1:ℂ)^n * n * (sphericalJ n (2*u-v) * sphericalJ (n-1) v -
      sphericalJ (n-1) (2*u-v) * sphericalJ n v)) (F := fun _ => sphericalJ 0 (2*u))
    (fun n v => ?_) (fun v => ?_) (fun R => ?_) (fun v => ?_) ?_ w
  · have h1 : HasDerivAt (fun v => sphericalJ n (2*u-v))
        (-((n * sphericalJ (n-1) (2*u-v) - (n+1) * sphericalJ (n+1) (2*u-v)) / (2*n+1))) v := by
      have := (sphProd_hasDerivAt_sphericalJ n (2*u-v)).comp v ((hasDerivAt_id v).const_sub (2*u))
      simpa [Function.comp_def] using this
    have h := ((h1.const_mul ((-1:ℂ)^n * (2*n+1))).mul (sphProd_hasDerivAt_sphericalJ n v))
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun v => by simp only [Pi.mul_apply])).congr_deriv ?_
    have h3 : (2*n+1 : ℂ) ≠ 0 := by
      have : (0:ℝ) < 2*n+1 := by positivity
      exact_mod_cast this.ne'
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
    push_cast
    ring
  · -- `gₙ → 0`
    obtain ⟨u', hu, hu0, h⟩ := sphProd_bound (‖2*u-v‖ + ‖v‖)
    obtain ⟨M, hM0, hM⟩ := sphProd_bound_uniform (‖2*u-v‖ + ‖v‖)
    have ht := ((hu 2 zero_le_two).tendsto_atTop_zero).const_mul (2*M)
    rw [mul_zero] at ht
    refine squeeze_zero_norm (fun n => ?_) ht
    have hx : ‖2*u-v‖ ≤ ‖2*u-v‖ + ‖v‖ := le_add_of_nonneg_right (norm_nonneg _)
    have hy : ‖v‖ ≤ ‖2*u-v‖ + ‖v‖ := le_add_of_nonneg_left (norm_nonneg _)
    have hn : (n:ℝ) ≤ 2^n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
    calc (n:ℝ) * ‖sphericalJ n (2*u-v) * sphericalJ (n-1) v -
          sphericalJ (n-1) (2*u-v) * sphericalJ n v‖
        ≤ 2^n * (u' n * M + M * u' n) := by
          gcongr
          refine (norm_sub_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
          · exact mul_le_mul (h n _ hx) (hM _ _ hy) (norm_nonneg _) (hu0 n)
          · exact mul_le_mul (hM _ _ hx) (h n _ hy) (norm_nonneg _) hM0
      _ = _ := by ring
  · obtain ⟨u', hu, hu0, h⟩ := sphProd_bound (2*‖u‖ + |R|)
    obtain ⟨M, hM0, hM⟩ := sphProd_bound_uniform (2*‖u‖ + |R|)
    refine ⟨fun n => 2 * M * (2^n * u' n), (hu 2 zero_le_two).mul_left _, fun n v hv => ?_⟩
    have hv' : ‖v‖ ≤ 2*‖u‖ + |R| := by
      linarith [le_abs_self R, norm_nonneg u]
    have hx : ‖2*u-v‖ ≤ 2*‖u‖ + |R| := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]; simp only [Complex.norm_ofNat]
      linarith [le_abs_self R]
    have h2 : ‖(2*(n:ℂ)+1)‖ ≤ 2 * 2^n := by
      rw [show (2*(n:ℂ)+1) = ((2*n+1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      exact sphProd_two_mul_add_one_le n
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc ‖(2*(n:ℂ)+1)‖ * ‖sphericalJ n (2*u-v)‖ * ‖sphericalJ n v‖ ≤ (2 * 2^n) * M * u' n := by
          gcongr
          · exact hM _ _ hx
          · exact h n v hv'
      _ = _ := by ring
  · simpa using hasDerivAt_const v (sphericalJ 0 (2*u))
  · rw [← hasSum_nat_add_iff' 1]
    simp [sphProd_sphericalJ_succ_zero, sphSeries_sphericalJ_zero_zero]

/-- `∑ (-1)ⁿ (2n+1) jₙ(x) jₙ(y) = j₀(x+y)` (DLMF 10.60). -/
theorem sphProd_hasSum_alt_mul (x y : ℂ) :
    HasSum (fun n : ℕ => (-1:ℂ)^n * (2*n+1) * sphericalJ n x * sphericalJ n y)
      (sphericalJ 0 (x+y)) := by
  have h := sphProd_hasSum_alt_line ((x+y)/2) y
  rw [show 2*((x+y)/2) - y = x by ring, show 2*((x+y)/2) = x+y by ring] at h
  exact h

/-- `∑ (-1)ⁿ (2n+1) jₙ(z)² = j₀(2z)` (DLMF 10.60). -/
theorem sphProd_hasSum_alt_sq (z : ℂ) :
    HasSum (fun n : ℕ => (-1:ℂ)^n * (2*n+1) * sphericalJ n z ^ 2) (sphericalJ 0 (2*z)) := by
  have h := sphProd_hasSum_alt_mul z z
  rw [show z + z = 2*z by ring] at h
  simpa [sq, mul_assoc] using h

end DLMF
