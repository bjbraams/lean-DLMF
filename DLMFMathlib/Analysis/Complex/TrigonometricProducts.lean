/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.PSeries

/-!
# Infinite products for hyperbolic sine and cosine

The normalized hyperbolic sine product follows from Mathlib's Euler sine product. Splitting its
factors into even and odd indices gives the hyperbolic cosine product, including its zeros by
locally uniform convergence. These proofs were moved from the DLMF elementary layer.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory
open scoped Real Topology
namespace Complex

/-- Euler's product for hyperbolic sine divided by its argument, with its removable value at zero. -/
theorem hasProd_sinh_div (z : ℂ) :
    HasProd (fun n : ℕ => 1+z^2/(((n+1:ℂ)^2)*π^2)) (if z=0 then 1 else Complex.sinh z/z) := by
  let sinhc : ℂ → ℂ := fun z => if z=0 then 1 else Complex.sinh z/z
  change HasProd (fun n : ℕ => 1+z^2/(((n+1:ℂ)^2)*π^2)) (sinhc z)
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases hz0 : z = 0
  · subst hz0; simp [sinhc]
  have hx0 : I*z/π ≠ 0 := by simp [hz0, hπ, Complex.I_ne_zero]
  have hf : (fun n : ℕ => 1+z^2/(((n+1:ℂ)^2)*π^2)) = fun n => 1 + sineTerm (I*z/π) n := by
    funext n; simp only [sineTerm]; congr 1
    have : ((n:ℂ)+1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp
    linear_combination Complex.I_sq
  rw [hf, (multipliable_sineTerm _).hasProd_iff_tendsto_nat]
  convert tendsto_euler_sin_prod' hx0 using 2
  rw [show (π:ℂ)*(I*z/π) = z*I by field_simp, Complex.sin_mul_I]
  simp only [sinhc, hz0, ↓reduceIte]
  field_simp

/-- Euler’s product for complex hyperbolic cosine over the odd positive integers. -/
theorem hasProd_cosh_product (z : ℂ) : HasProd (fun n : ℕ => 1+4*z^2/(((2*n+1:ℂ)^2)*π^2)) (Complex.cosh z) := by
  let sinhc : ℂ → ℂ := fun z => if z=0 then 1 else Complex.sinh z/z
  have hasProd_sinh (w : ℂ) : HasProd (fun n : ℕ => 1+w^2/(((n+1:ℂ)^2)*π^2)) (sinhc w) := by
    simpa [sinhc] using Complex.hasProd_sinh_div w
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  set R : ℝ := ‖z‖+1 with hR
  have hR0 : 0 ≤ R := by positivity
  set K : Set ℂ := Metric.closedBall (0:ℂ) R with hK
  have hzK : z ∈ Metric.ball (0:ℂ) R := by simp [hR]
  have hu : Summable (fun n : ℕ => 4*R^2/(((2*n+1:ℝ))^2*π^2)) := by
    have hs : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
      have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
      simpa using this
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (hs.mul_left (4*R^2/π^2))
    have h1 : ((n:ℝ)+1)^2 ≤ (2*n+1)^2 := by nlinarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    have hp : 0 < π^2 := by positivity
    rw [div_mul_div_comm, mul_one, mul_comm (π^2)]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right h1 hp.le
  have hb : ∀ᶠ n : ℕ in atTop, ∀ x ∈ K,
      ‖4*x^2/(((2*n+1:ℂ)^2)*π^2)‖ ≤ 4*R^2/(((2*n+1:ℝ))^2*π^2) := by
    refine Filter.Eventually.of_forall fun (n : ℕ) (x : ℂ) hx => ?_
    have hx' : ‖x‖ ≤ R := by simpa [hK] using hx
    have e : ‖4*x^2/(((2*n+1:ℂ)^2)*π^2)‖ = 4*‖x‖^2/(((2*n+1:ℝ))^2*π^2) := by
      rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
      have h1 : ‖(2*n+1:ℂ)‖ = 2*n+1 := by
        rw [show (2*n+1:ℂ) = ((2*n+1:ℝ):ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
      rw [h1, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      norm_num
    rw [e]
    gcongr
  have hcts : ∀ n : ℕ, ContinuousOn (fun x : ℂ => 4*x^2/(((2*n+1:ℂ)^2)*π^2)) K :=
    fun n => (by fun_prop : Continuous (fun x : ℂ => 4*x^2/(((2*n+1:ℂ)^2)*π^2))).continuousOn
  have H := Summable.hasProdUniformlyOn_nat_one_add (isCompact_closedBall (0:ℂ) R) hu hb hcts
  set F : ℂ → ℂ := fun x => ∏' i : ℕ, (1+4*x^2/(((2*i+1:ℂ)^2)*π^2)) with hF
  have hFc : ContinuousOn F K := by
    refine H.tendstoUniformlyOn_finsetRange.continuousOn (Filter.Frequently.of_forall fun n => ?_)
    exact continuousOn_finsetProd _ fun i _ => continuousOn_const.add (hcts i)
  have hsinhc2 : ∀ x : ℂ, sinhc (2*x) = sinhc x * Complex.cosh x := by
    intro x
    by_cases hx : x = 0
    · simp [sinhc, hx]
    · have h2 : 2*x ≠ 0 := mul_ne_zero two_ne_zero hx
      simp only [sinhc, hx, h2, ↓reduceIte, Complex.sinh_two_mul]
      field_simp
  have hgood : ∀ x ∈ K, sinhc x ≠ 0 → F x = Complex.cosh x := by
    intro x hx hs
    have h1 := H.hasProd hx
    have h2 := hasProd_sinh x
    have h3 := hasProd_sinh (2*x)
    have h4 : HasProd (fun k : ℕ => 1+(2*x)^2/(((k+1:ℂ)^2)*π^2)) (F x * sinhc x) := by
      refine HasProd.even_mul_odd ?_ ?_
      · convert h1 using 2 with k
        push_cast; ring
      · convert h2 using 2 with k
        have : (k:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        rw [show (((2*k+1:ℕ):ℂ)+1) = 2*((k:ℂ)+1) by push_cast; ring]
        field_simp
    have := h4.unique h3
    rw [hsinhc2, mul_comm] at this
    exact mul_left_cancel₀ hs this
  have hFz : F z = Complex.cosh z := by
    by_cases hs : sinhc z ≠ 0
    · exact hgood z (Metric.ball_subset_closedBall hzK) hs
    push Not at hs
    have hz0 : z ≠ 0 := by intro h; simp [sinhc, h] at hs
    have hsh : Complex.sinh z = 0 := by
      simp only [sinhc, hz0, ↓reduceIte] at hs
      exact (div_eq_zero_iff.mp hs).resolve_right hz0
    have hch : Complex.cosh z ≠ 0 := by
      intro h
      have := Complex.cosh_sq_sub_sinh_sq z
      rw [h, hsh] at this; norm_num at this
    have hlim : Tendsto (fun t : ℝ => z+t) (𝓝[≠] 0) (𝓝 z) := by
      have : Tendsto (fun t : ℝ => z+t) (𝓝 0) (𝓝 (z+((0:ℝ):ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have hK : K ∈ 𝓝 z := Metric.closedBall_mem_nhds_of_mem hzK
    have hA := ((hFc.continuousAt hK).tendsto).comp hlim
    have hB := ((Complex.continuous_cosh.continuousAt (x := z)).tendsto).comp hlim
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] 0, F (z+t) = Complex.cosh (z+t) := by
      have hin : ∀ᶠ t : ℝ in 𝓝[≠] 0, z+(t:ℂ) ∈ K := hlim.eventually (Filter.mem_of_superset hK
        (fun w hw => hw)) |>.mono fun t ht => ht
      filter_upwards [hin, self_mem_nhdsWithin] with t ht ht0
      apply hgood _ ht
      have hsh' : Complex.sinh (z+t) ≠ 0 := by
        rw [Complex.sinh_add, hsh, zero_mul, zero_add]
        refine mul_ne_zero hch ?_
        rw [← Complex.ofReal_sinh]
        exact_mod_cast fun h => ht0 (Real.sinh_eq_zero.mp h)
      by_cases h0 : z+(t:ℂ) = 0
      · simp [sinhc, h0]
      · simp only [sinhc, h0, ↓reduceIte]
        exact div_ne_zero hsh' h0
    exact tendsto_nhds_unique (hA.congr' (hev.mono fun t ht => by simp [Function.comp, ht])) hB
  have := H.hasProd (Metric.ball_subset_closedBall hzK)
  rw [hFz] at this
  exact this


end Complex

end
