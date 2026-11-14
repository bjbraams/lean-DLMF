/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Summable samples of integrable functions of bounded variation

An integrable function of bounded variation on a half-line has absolutely summable samples
at every translated nonnegative integer lattice. A single summable majorant controls all
translations in a unit interval. The proof bounds a point value by the integral of the norm
on its unit cell plus the variation on that cell; the cell variations telescope.

The target may be any seminormed additive commutative group. Only the scalar norm is
integrated, so no scalar-space or completeness assumption on the target is needed. The cell
variation summability itself holds in any pseudometric target. The proof uses Mathlib's
variation additivity and improper integral convergence, with no copied proof bodies.

## Main results

* `BoundedVariationOn.norm_le_integral_norm_add_variation_unit`: the unit-cell bound.
* `BoundedVariationOn.summable_variation_nat_unit`: summable cell variations.
* `BoundedVariationOn.exists_summable_bound_nat_unit`: a uniform summable majorant.
* `BoundedVariationOn.summable_norm_comp_nat_add_of_integrableOn`: absolute lattice summability.
-/

public noncomputable section

open Set MeasureTheory Filter Topology

variable {E : Type*} [SeminormedAddCommGroup E]
/-- A point value on a unit cell is bounded by its norm integral plus its variation. -/
lemma BoundedVariationOn.norm_le_integral_norm_add_variation_unit {f : ℝ → E} {a x : ℝ}
    (hbv : BoundedVariationOn f (Icc a (a + 1)))
    (hi : IntervalIntegrable (fun t => ‖f t‖) volume a (a + 1))
    (hx : x ∈ Icc a (a + 1)) :
    ‖f x‖ ≤ (∫ t in a..(a + 1), ‖f t‖) + (eVariationOn f (Icc a (a + 1))).toReal := by
  have hle (y : ℝ) (hy : y ∈ Icc a (a + 1)) :
      ‖f x‖ ≤ ‖f y‖ + (eVariationOn f (Icc a (a + 1))).toReal := by
    exact norm_le_norm_add_const_of_dist_le (hbv.dist_le hx hy)
  have h := intervalIntegral.integral_mono_on (by linarith : a ≤ a + 1)
    (intervalIntegrable_const (c := ‖f x‖)) (hi.add intervalIntegrable_const) hle
  rw [intervalIntegral.integral_add hi intervalIntegrable_const] at h
  simpa only [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul, one_mul] using h

/-- Variations on adjacent nonnegative unit cells form a summable real sequence. -/
lemma BoundedVariationOn.summable_variation_nat_unit
    {F : Type*} [PseudoMetricSpace F] {f : ℝ → F}
    (hbv : BoundedVariationOn f (Ici 0)) :
    Summable (fun n : ℕ => (eVariationOn f (Icc (n : ℝ) (n + 1))).toReal) := by
  have hc (n : ℕ) : eVariationOn f (Icc (n : ℝ) (n + 1)) ≠ ⊤ :=
    hbv.mono (fun t ht => (Nat.cast_nonneg n).trans ht.1)
  apply summable_of_sum_range_le (fun _ => ENNReal.toReal_nonneg)
    (c := (eVariationOn f (Ici 0)).toReal)
  intro N
  have hs := eVariationOn.sum' f (I := fun n : ℕ => (n : ℝ))
    (fun _ _ h => Nat.cast_le.mpr h) (n := N)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at hs
  rw [← ENNReal.toReal_sum (fun n _ => hc n), hs]
  exact ENNReal.toReal_mono hbv (eVariationOn.mono f (fun t ht => ht.1))

/-- The norm integrals of adjacent unit cells are summable on an integrable half-line. -/
lemma MeasureTheory.IntegrableOn.summable_integral_norm_nat_unit {f : ℝ → E}
    (hi : IntegrableOn (fun t => ‖f t‖) (Ioi 0)) :
    Summable (fun n : ℕ => ∫ t in (n : ℝ)..(n + 1), ‖f t‖) := by
  have hint (n : ℕ) : IntervalIntegrable (fun t => ‖f t‖) volume (n : ℝ) (n + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact hi.mono_set (fun t ht => lt_of_le_of_lt (Nat.cast_nonneg n) ht.1)
  apply HasSum.summable (a := ∫ t in Ioi (0 : ℝ), ‖f t‖)
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n =>
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => norm_nonneg (f t))) _).mpr
  have h := intervalIntegral_tendsto_integral_Ioi 0 hi
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  apply h.congr
  intro N
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => (n : ℝ)) (fun k (_ : k < N) => by
      simpa only [Nat.cast_add, Nat.cast_one] using hint k)
  simpa only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] using hs.symm

/-- One summable majorant bounds all unit translates of the nonnegative integer samples. -/
lemma BoundedVariationOn.exists_summable_bound_nat_unit {f : ℝ → E}
    (hbv : BoundedVariationOn f (Ici 0))
    (hi : IntegrableOn (fun t => ‖f t‖) (Ioi 0)) :
    ∃ B : ℕ → ℝ, Summable B ∧ ∀ n : ℕ, ∀ x ∈ Icc (0 : ℝ) 1, ‖f (x + n)‖ ≤ B n := by
  have hI := hi.summable_integral_norm_nat_unit
  have hV := hbv.summable_variation_nat_unit
  refine ⟨fun n => (∫ t in (n : ℝ)..(n + 1), ‖f t‖) +
    (eVariationOn f (Icc (n : ℝ) (n + 1))).toReal, hI.add hV, ?_⟩
  intro n x hx
  apply BoundedVariationOn.norm_le_integral_norm_add_variation_unit
  · exact hbv.mono (fun t ht => (Nat.cast_nonneg n).trans ht.1)
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact hi.mono_set (fun t ht => lt_of_le_of_lt (Nat.cast_nonneg n) ht.1)
  · exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The norm of each translated nonnegative integer sampling is summable. -/
lemma BoundedVariationOn.summable_norm_comp_nat_add_of_integrableOn {f : ℝ → E}
    (hbv : BoundedVariationOn f (Ici 0))
    (hi : IntegrableOn (fun t => ‖f t‖) (Ioi 0)) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Summable (fun n : ℕ => ‖f (x + n)‖) := by
  obtain ⟨B, hB, hbound⟩ := hbv.exists_summable_bound_nat_unit hi
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hbound n x hx) hB



/-- An integrable function of bounded variation on a half-line tends to zero at infinity. -/
lemma BoundedVariationOn.tendsto_zero_of_integrableOn_Ioi {f : ℝ → E}
    (hbv : BoundedVariationOn f (Ici 0))
    (hi : IntegrableOn (fun t => ‖f t‖) (Ioi 0)) : Tendsto f atTop (𝓝 0) := by
  have hnorm := lipschitzWith_one_norm.comp_boundedVariationOn hbv
  obtain ⟨L, hL⟩ := hnorm.exists_tendsto_atTop
  have hp : (𝓟 (Ici (0 : ℝ)) ⊓ atTop) = atTop :=
    inf_eq_right.mpr (le_principal_iff.mpr (Ici_mem_atTop 0))
  rw [hp] at hL
  have hs := hbv.summable_norm_comp_nat_add_of_integrableOn hi
    (x := 0) ⟨le_rfl, zero_le_one⟩
  simp only [zero_add] at hs
  have hLn := hL.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hL0 : L = 0 := tendsto_nhds_unique hLn hs.tendsto_atTop_zero
  rw [hL0] at hL
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hL

/-- The norm at a nonnegative point is bounded by the variation on its remaining half-line. -/
lemma BoundedVariationOn.norm_le_variation_Ici_of_integrableOn {f : ℝ → E}
    (hbv : BoundedVariationOn f (Ici 0))
    (hi : IntegrableOn (fun t => ‖f t‖) (Ioi 0)) {x : ℝ} (hx : 0 ≤ x) :
    ‖f x‖ ≤ (eVariationOn f (Ici x)).toReal := by
  have htail : BoundedVariationOn f (Ici x) := hbv.mono (fun t ht => hx.trans ht)
  have hlim := (hbv.tendsto_zero_of_integrableOn_Ioi hi).norm.add_const
    (eVariationOn f (Ici x)).toReal
  simp only [norm_zero, zero_add] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop x] with y hy
  exact norm_le_norm_add_const_of_dist_le (htail.dist_le (le_refl x) hy)

/-- Even extension of a function of bounded variation on a half-line has bounded variation. -/
lemma BoundedVariationOn.comp_abs {E : Type*} [PseudoMetricSpace E] {f : ℝ → E}
    (hf : BoundedVariationOn f (Ici 0)) :
    BoundedVariationOn (fun t : ℝ => f |t|) univ := by
  have hleft := eVariationOn.comp_le_of_antitoneOn f abs
    (t := Iic (0 : ℝ)) (s := Ici 0)
    (fun x hx y hy hxy => by
      rw [abs_of_nonpos hx, abs_of_nonpos hy]
      exact neg_le_neg hxy)
    (fun t _ => abs_nonneg t)
  have hright := eVariationOn.comp_le_of_monotoneOn f abs
    (t := Ici (0 : ℝ)) (s := Ici 0)
    (fun x hx y hy hxy => by
      rw [abs_of_nonneg hx, abs_of_nonneg hy]
      exact hxy)
    (fun t _ => abs_nonneg t)
  have hu := eVariationOn.union (fun t : ℝ => f |t|)
    (isGreatest_Iic : IsGreatest (Iic (0 : ℝ)) 0)
    (isLeast_Ici : IsLeast (Ici (0 : ℝ)) 0)
  rw [Iic_union_Ici] at hu
  rw [BoundedVariationOn, hu]
  exact ne_of_lt (ENNReal.add_lt_top.mpr ⟨hleft.trans_lt hf.lt_top, hright.trans_lt hf.lt_top⟩)

