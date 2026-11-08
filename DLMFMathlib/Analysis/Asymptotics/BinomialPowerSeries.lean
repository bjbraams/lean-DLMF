/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticInversion
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Derivative
public import DLMFMathlib.RingTheory.Binomial

/-!
# Binomial powers of asymptotic power series

An asymptotic power series with zero constant coefficient may be substituted into the
binomial expansion at one. The resulting coefficients are finite sums of coefficients of
powers, even when the original asymptotic series does not converge.
-/

@[expose] public noncomputable section

open Filter Finset PowerSeries
open scoped Topology

namespace PowerSeries

/-- The formal binomial power `(1+P)^β` when `P` has zero constant coefficient. -/
def binomialSubstitution {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (P : 𝕜⟦X⟧) (β : 𝕜) : 𝕜⟦X⟧ :=
  (mk fun n => Ring.choose β n).subst P

/-- Coefficients above the degree of extraction cannot contribute to a binomial substitution. -/
theorem coeff_binomialSubstitution {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    {P : 𝕜⟦X⟧} (hP : constantCoeff P = 0) (β : 𝕜) (n : ℕ) :
    coeff n (binomialSubstitution P β) =
      ∑ k ∈ range (n + 1), Ring.choose β k * coeff n (P ^ k) := by
  rw [binomialSubstitution, coeff_subst' (HasSubst.of_constantCoeff_zero' hP)]
  simp only [coeff_mk, smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  apply mem_range.mpr
  by_contra hn
  have hnk : n < k := by omega
  obtain ⟨Q, hQ⟩ := X_dvd_iff.mpr hP
  have he : coeff n (P ^ k) = 0 := by
    rw [hQ, mul_pow, coeff_X_pow_mul', ite_eq_right (by omega)]
  exact hk (by simp only [he, mul_zero])

/-- Adding binomial exponents multiplies the substituted formal series. -/
theorem binomialSubstitution_add {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    {P : 𝕜⟦X⟧} (hP : constantCoeff P = 0) (β γ : 𝕜) :
    binomialSubstitution P (β + γ) = binomialSubstitution P β * binomialSubstitution P γ := by
  have he (a : 𝕜) : (mk fun n => Ring.choose a n) = PowerSeries.binomialSeries 𝕜 a := by
    ext n
    simp only [coeff_mk, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]
  simp only [binomialSubstitution, he, PowerSeries.binomialSeries_add,
    subst_mul (HasSubst.of_constantCoeff_zero' hP)]

/-- The zero binomial power is the constant series one. -/
theorem binomialSubstitution_zero {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    {P : 𝕜⟦X⟧} (_hP : constantCoeff P = 0) : binomialSubstitution P 0 = 1 := by
  have he : (mk fun n => Ring.choose (0 : 𝕜) n) = (1 : 𝕜⟦X⟧) := by
    ext n
    simp only [coeff_mk, Ring.choose_zero_ite, coeff_one]
  rw [binomialSubstitution, he, show (1 : 𝕜⟦X⟧) = C 1 by simp only [map_one], subst_C]
  rfl

/-- The first binomial power is the original unit series. -/
theorem binomialSubstitution_one {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    {P : 𝕜⟦X⟧} (hP : constantCoeff P = 0) : binomialSubstitution P 1 = 1 + P := by
  have he : (mk fun n => Ring.choose (1 : 𝕜) n) = PowerSeries.binomialSeries 𝕜 (1 : 𝕜) := by
    ext n
    simp only [coeff_mk, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]
  rw [binomialSubstitution, he, ← Nat.cast_one (R := 𝕜), PowerSeries.binomialSeries_nat]
  simp only [pow_one, subst_add (HasSubst.of_constantCoeff_zero' hP), subst_X
    (HasSubst.of_constantCoeff_zero' hP)]
  rw [show (1 : 𝕜⟦X⟧) = C 1 by simp only [map_one], subst_C]
  rfl

/-- Differentiating a formal binomial power obeys the ordinary chain rule. -/
theorem derivative_binomialSubstitution {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    {P : 𝕜⟦X⟧} (hP : constantCoeff P = 0) (β : 𝕜) :
    PowerSeries.derivative (binomialSubstitution P β) =
      C β * binomialSubstitution P (β - 1) * PowerSeries.derivative P := by
  have he : PowerSeries.derivative (mk fun n => Ring.choose β n) =
      C β * (mk fun n => Ring.choose (β - 1) n) := by
    ext n
    simp only [coeff_derivative, coeff_mk, coeff_C_mul]
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using Ring.natCast_mul_choose_succ β n
  rw [binomialSubstitution, derivative_subst (HasSubst.of_constantCoeff_zero' hP), he,
    subst_mul (HasSubst.of_constantCoeff_zero' hP),
    subst_C]
  rfl

/-- Ring homomorphisms commute with a substituted binomial power. -/
theorem map_binomialSubstitution {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L]
    (f : K →+* L) {P : K⟦X⟧} (hP : constantCoeff P = 0) (β : K) :
    PowerSeries.map f (binomialSubstitution P β) =
      binomialSubstitution (PowerSeries.map f P) (f β) := by
  change MvPowerSeries.map f ((mk fun n => Ring.choose β n).subst P) = _
  rw [PowerSeries.map_subst (HasSubst.of_constantCoeff_zero' hP)]
  have he : PowerSeries.map f (mk fun n => Ring.choose β n) =
      (mk fun n => Ring.choose (f β) n) := by
    ext n
    simp only [coeff_map, coeff_mk, Ring.map_choose]
  rw [he]
  rfl

/-- Finite convolution formula for an amplitude times a substituted binomial power. -/
theorem coeff_mul_binomialSubstitution {K : Type*} [Field K] [CharZero K]
    {P Q : K⟦X⟧} (hP : constantCoeff P = 0) (β : K) (n : ℕ) :
    coeff n (Q * binomialSubstitution P β) =
      ∑ j ∈ range (n + 1), coeff j Q *
        ∑ k ∈ range (n - j + 1), Ring.choose β k * coeff (n - j) (P ^ k) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun j _ => ?_
  rw [coeff_binomialSubstitution hP]

end PowerSeries

namespace Asymptotics.HasAsymptoticPowerSeries

/-- Complex binomial powers of a null asymptotic power series. -/
theorem one_add_cpow {α : Type*} {l : Filter α} {w f : α → ℂ} {P : ℂ⟦X⟧}
    (hw : Tendsto w l (𝓝 0)) (hf : HasAsymptoticPowerSeries l w P f)
    (hP : PowerSeries.constantCoeff P = 0) (β : ℂ) :
    HasAsymptoticPowerSeries l w (PowerSeries.binomialSubstitution P β)
      (fun x => (1 + f x) ^ β) := by
  have hφ : HasFPowerSeriesAt (fun z : ℂ => (1 + z) ^ β) (_root_.binomialSeries ℂ β)
      (PowerSeries.constantCoeff P) := by
    rw [hP]
    exact Complex.one_add_cpow_hasFPowerSeriesAt_zero
  simpa only [hP, map_zero, sub_zero, _root_.binomialSeries,
    FormalMultilinearSeries.coeff_ofScalars, PowerSeries.binomialSubstitution] using
    hf.analytic_comp hφ hw

/-- Real binomial powers of a null asymptotic power series. -/
theorem one_add_rpow {α : Type*} {l : Filter α} {w f : α → ℝ} {P : ℝ⟦X⟧}
    (hw : Tendsto w l (𝓝 0)) (hf : HasAsymptoticPowerSeries l w P f)
    (hP : PowerSeries.constantCoeff P = 0) (β : ℝ) :
    HasAsymptoticPowerSeries l w (PowerSeries.binomialSubstitution P β)
      (fun x => (1 + f x) ^ β) := by
  have hφ : HasFPowerSeriesAt (fun z : ℝ => (1 + z) ^ β) (_root_.binomialSeries ℝ β)
      (PowerSeries.constantCoeff P) := by
    rw [hP]
    exact Real.one_add_rpow_hasFPowerSeriesAt_zero
  simpa only [hP, map_zero, sub_zero, _root_.binomialSeries,
    FormalMultilinearSeries.coeff_ofScalars, PowerSeries.binomialSubstitution] using
    hf.analytic_comp hφ hw

end Asymptotics.HasAsymptoticPowerSeries
