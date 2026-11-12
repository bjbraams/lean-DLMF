/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.ZonalSeries.Endpoint
public import DLMF.Legendre.IntegralRepresentations.Ferrers

/-!
# Fractional integration of the Legendre expansion

Dougall's Ferrers expansion (DLMF 14.18.9) follows by fractional integration of the
order-zero Legendre expansion. A summable majorant controls both singular endpoints of
the fractional kernel. At order zero and argument one the ordered coefficient sums are
used, since absolute convergence is not asserted there.

## Main results

* `ZonalSeries.hasSum_negative_order`: the expansion on `(-1,1)` for positive real order.
* `ZonalSeries.tendsto_partialSum_negative_order`: ordered convergence on `(-1,1]` for
  nonnegative real order.
-/

open Complex Filter Set MeasureTheory
open scoped Real Topology Nat
@[expose] public noncomputable section
namespace DLMF.Legendre.ZonalSeries
open DLMF.OrthogonalPolynomials DLMF.Hypergeometric

/-- A summable coefficient majorant permits fractional integration of the Legendre series. -/
private lemma hasSum_negative_order_of_bound {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n)
    {μ : ℝ} (hμ : 0 < μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1)
    (u : ℕ → ℝ) (hu : Summable u)
    (hbd : ∀ n, ∀ t ∈ Ioo (-1:ℝ) 1,
      ‖legendreCoeff ν n * legendrePolynomialP n t‖ ≤ u n * (1-t^2)^(-1/2:ℝ)) :
    HasSum (fun n : ℕ => legendreCoeff ν n * ferrersP n (-μ) x) (ferrersP ν (-μ) x) := by
  let W : ℝ → ℝ := fun t => (1-t^2)^(-1/2:ℝ) * (t-x)^(μ-1)
  have hW : IntervalIntegrable W volume x 1 := by
    let m : ℝ := (x+1)/2
    have hxm : x < m := by dsimp [m];linarith [hx.2]
    have hm1 : m < 1 := by dsimp [m];linarith [hx.2]
    have hpow : IntervalIntegrable (fun t : ℝ => (t-x)^(μ-1)) volume x m := by
      have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := m-x)
        (by linarith : -1 < μ-1)).comp_sub_right x
      simpa only [zero_add,sub_add_cancel] using h
    have hwc : ContinuousOn (fun t : ℝ => (1-t^2)^(-1/2:ℝ)) (uIcc x m) := by
      refine (by fun_prop : ContinuousOn (fun t : ℝ => 1-t^2) (uIcc x m)).rpow_const ?_
      intro t ht
      rw [uIcc_of_le hxm.le] at ht
      left
      have h0 : -1 < t := lt_of_lt_of_le hx.1 ht.1
      have h1 : t < 1 := lt_of_le_of_lt ht.2 hm1
      nlinarith
    have hleft : IntervalIntegrable W volume x m := hpow.continuousOn_mul hwc
    have hwr : IntervalIntegrable (fun t : ℝ => (1-t^2)^(-1/2:ℝ)) volume m 1 := by
      refine (OrthogonalityIntegrals.intervalIntegrable_rpow (Or.inl rfl)).mono_set ?_
      rw [uIcc_of_le hm1.le,uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)]
      exact Icc_subset_Icc (by dsimp [m];linarith [hx.1]) le_rfl
    have hpc : ContinuousOn (fun t : ℝ => (t-x)^(μ-1)) (uIcc m 1) := by
      refine (by fun_prop : ContinuousOn (fun t : ℝ => t-x) (uIcc m 1)).rpow_const ?_
      intro t ht
      rw [uIcc_of_le hm1.le] at ht
      exact Or.inl (ne_of_gt (by linarith [ht.1]))
    exact hleft.trans (hwr.mul_continuousOn hpc)
  let F : ℕ → ℝ → ℂ := fun n t => legendreCoeff ν n * legendrePolynomialP n t *
    ((t-x:ℝ):ℂ)^((μ:ℂ)-1)
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := x) (b := 1) (μ := volume) (F := F)
    (f := fun t : ℝ => ferrersP ν 0 t * ((t-x:ℝ):ℂ)^((μ:ℂ)-1))
    (fun n t => u n * W t)
    (fun n =>
      (((continuous_legendrePolynomialP_ofReal n).const_mul (legendreCoeff ν n)).measurable.mul
        (by fun_prop : Measurable (fun t : ℝ =>
          ((t-x:ℝ):ℂ)^((μ:ℂ)-1)))).aestronglyMeasurable) (fun n => ?_)
    (Eventually.of_forall fun t _ => hu.mul_right (W t))
    (by simp_rw [tsum_mul_right];exact hW.const_mul _) ?_
  · let A : ℂ := (1-(x:ℂ)^2)^(-(μ:ℂ)/2)/Gamma μ
    have hμc : 0 < (μ:ℂ).re := hμ
    have hterm (n : ℕ) : A*(∫ t : ℝ in x..1,F n t) =
        legendreCoeff ν n * ferrersP n (-μ) x := by
      have hfr : ferrersP n (-μ) x = A*(∫ t : ℝ in x..1,
          ferrersP n 0 t * ((t-x:ℝ):ℂ)^((μ:ℂ)-1)) := by
        simpa only [A,ofReal_sub] using ferrersP_fractional_integral hμc (n:ℂ) hx
      rw [hfr]
      dsimp [A]
      calc _ = (1-(x:ℂ)^2)^(-(μ:ℂ)/2)/Gamma μ *
          (∫ t : ℝ in x..1,legendreCoeff ν n *
            (ferrersP n 0 t * ((t-x:ℝ):ℂ)^((μ:ℂ)-1))) := by
              congr 1
              apply intervalIntegral.integral_congr_Ioo_of_le hx.2.le
              intro t ht
              have htI : t ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hx.1,ht.1],ht.2⟩
              dsimp [F]
              rw [ferrersP_nat_polynomial n htI]
              ring
        _ = _ := by rw [intervalIntegral.integral_const_mul];ring
    have hs' := hs.mul_left A
    simp_rw [hterm] at hs'
    have hval : A*(∫ t : ℝ in x..1, ferrersP ν 0 t * ((t-x:ℝ):ℂ)^((μ:ℂ)-1)) =
        ferrersP ν (-μ) x := by
      simpa only [A,ofReal_sub] using (ferrersP_fractional_integral hμc ν hx).symm
    rw [hval] at hs'
    exact hs'
  · filter_upwards [volume.ae_ne (1:ℝ)] with t ht hmem
    rw [uIoc_of_le hx.2.le] at hmem
    have ht1 : t < 1 := lt_of_le_of_ne hmem.2 ht
    have htI : t ∈ Ioo (-1:ℝ) 1 := ⟨lt_trans hx.1 hmem.1,ht1⟩
    dsimp [F,W]
    rw [norm_mul,norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hmem.1)]
    simp only [sub_re,ofReal_re,one_re]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbd n t htI)
      (Real.rpow_nonneg (sub_nonneg.mpr hmem.1.le) (μ-1))
  · filter_upwards [volume.ae_ne (1:ℝ)] with t ht hmem
    rw [uIoc_of_le hx.2.le] at hmem
    have ht1 : t < 1 := lt_of_le_of_ne hmem.2 ht
    have htI : t ∈ Ioo (-1:ℝ) 1 := ⟨lt_trans hx.1 hmem.1,ht1⟩
    exact (hasSum_legendreCoeff_mul hν htI).mul_right _

/-- Dougall's Ferrers series converges absolutely in the open interval for positive order. -/
theorem hasSum_negative_order {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n)
    {μ : ℝ} (hμ : 0 < μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasSum (fun n : ℕ => legendreCoeff ν n * ferrersP n (-μ) x) (ferrersP ν (-μ) x) := by
  obtain ⟨u, hu, _, hbound⟩ := exists_summable_bound ν
  exact hasSum_negative_order_of_bound hν hμ hx u hu hbound

/-- The totalized Ferrers definition vanishes at one for nonzero order. -/
private lemma ferrersP_one_of_ne_zero (ν μ : ℂ) (hμ : μ ≠ 0) : ferrersP ν μ 1 = 0 := by
  have he : μ / 2 ≠ 0 := div_ne_zero hμ (by norm_num)
  simp [ferrersP, Complex.zero_cpow he]

/-- The order-zero Ferrers function has value one at the endpoint. -/
private lemma ferrersP_zero_one (ν : ℂ) : ferrersP ν 0 1 = 1 := by
  simp only [ferrersP, zero_div, cpow_zero, one_mul, ofReal_one, sub_self]
  have hc : ∀ n : ℕ, (1:ℂ) ≠ -(n:ℂ) := by
    intro n hn
    have hr := congrArg Complex.re hn
    simp only [one_re, neg_re, natCast_re] at hr
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  simp [regularizedGaussHypergeometric_zero_of_regular hc]

/-- Ordered partial sums in Dougall's expansion converge, including at the endpoint. -/
theorem tendsto_partialSum_negative_order {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n)
    {μ : ℝ} (hμ : 0 ≤ μ) {x : ℝ} (hx : x ∈ Ioc (-1:ℝ) 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      legendreCoeff ν n * ferrersP n (-μ) x) atTop (𝓝 (ferrersP ν (-μ) x)) := by
  rcases eq_or_lt_of_le hμ with hμ0 | hμpos
  · subst μ
    simp only [ofReal_zero, neg_zero]
    rcases eq_or_lt_of_le hx.2 with rfl | hx1
    · simpa only [ferrersP_zero_one, mul_one] using tendsto_sum_legendreCoeff hν
    · have hseries := hasSum_legendreCoeff_mul hν ⟨hx.1,hx1⟩
      have hfun : (fun n : ℕ => legendreCoeff ν n * ferrersP n 0 x) =
          (fun n : ℕ => legendreCoeff ν n * legendrePolynomialP n x) := by
        funext n
        rw [ferrersP_nat_polynomial n ⟨hx.1,hx1⟩]
      rw [hfun]
      exact hseries.tendsto_sum_nat
  · rcases eq_or_lt_of_le hx.2 with rfl | hx1
    · have hnz : -(μ:ℂ) ≠ 0 := neg_ne_zero.mpr (ofReal_ne_zero.mpr hμpos.ne')
      simp only [ferrersP_one_of_ne_zero _ _ hnz, mul_zero, Finset.sum_const_zero]
      exact tendsto_const_nhds
    · exact (hasSum_negative_order hν hμpos ⟨hx.1,hx1⟩).tendsto_sum_nat

end DLMF.Legendre.ZonalSeries
