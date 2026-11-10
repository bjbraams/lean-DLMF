/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Asymptotics.LargeArgument
public import DLMFMathlib.Analysis.Asymptotics.WatsonSector

/-!
# Kummer expansions in the right half-plane

The dominant expansion of the regularized Kummer function in closed sectors
`δ |z| ≤ re z`, with `δ > 0` and `re b > re a > 0`, follows from the Euler integral
and Watson's lemma in a sector. The coefficients agree with DLMF 13.7.1.
-/

@[expose] public noncomputable section
open Complex Filter MeasureTheory Asymptotics
open scoped Real Topology Nat
open DLMF.Hypergeometric

namespace DLMF.Confluent

/-- The regularized Kummer expansion is uniform in every closed right-half-plane sector
when `re b > re a > 0`. -/
theorem hasAsymptoticExpansion_regularizedConfluent_sector_of_re_pos {a b : ℂ} (ha : 0 < a.re)
    (hba : 0 < (b - a).re) {δ : ℝ} (hδ : 0 < δ) :
    HasAsymptoticExpansion (sectorAtTop δ)
      (fun (n : ℕ) (z : ℂ) => exp z * z ^ (a - b - n))
      (kummerCoeff a b) (fun z : ℂ => regularizedHGFun {a} {b} z) := by
  set G : ℝ → ℂ := fun t => (t : ℂ) ^ (b - a - 1) * (1 - (t : ℂ)) ^ (a - 1) with hGdef
  set F : ℝ → ℂ := Set.indicator (Set.Iio 1) G with hFdef
  have hGint : IntegrableOn G (Set.Ioo 0 1) := by
    have h := betaIntegral_convergent (u := b - a) (v := a) hba ha
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp h
  have hint : IntegrableOn (fun t => Real.exp (-0 * t) • F t) (Set.Ioi 0) := by
    simp only [neg_zero, zero_mul, Real.exp_zero, one_smul, hFdef]
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Iio]
    change Integrable G ((volume.restrict (Set.Ioi 0)).restrict (Set.Iio 1))
    rw [Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi]
    exact hGint
  have hF : ∀ N : ℕ, (fun t => F t - ∑ n ∈ Finset.range N,
      ((t : ℂ) ^ ((n : ℂ) + (b - a) - 1)) • ((-1) ^ n * Ring.choose (a - 1) n)) =O[𝓝[>] 0]
      fun t => t ^ ((N : ℝ) + (b - a).re - 1) := by
    intro N
    have h1 : (fun t : ℝ => (t : ℂ) ^ (b - a - 1)) =O[𝓝[>] 0] fun t => t ^ ((b - a).re - 1) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht : (0 : ℝ) < t := ht
      rw [norm_cpow_eq_rpow_re_of_pos ht, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos ht _)]
      simp
    refine ((h1.mul (one_sub_cpow_sub_sum_isBigO (a - 1) N)).congr' ?_ ?_)
    · have h1mem : Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
        nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
      filter_upwards [self_mem_nhdsWithin, h1mem] with t ht ht1
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
      simp only [hFdef, hGdef, Set.indicator_of_mem (show t ∈ Set.Iio 1 from ht1), smul_eq_mul,
        mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [show (n : ℂ) + (b - a) - 1 = (n : ℂ) + (b - a - 1) by ring, Complex.cpow_add _ _ ht0,
        Complex.cpow_natCast, neg_pow]
      ring
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht : (0 : ℝ) < t := ht
      rw [show (N : ℝ) + (b - a).re - 1 = ((b - a).re - 1) + N by ring, Real.rpow_add ht,
        Real.rpow_natCast]
  have hW := ((hasAsymptoticExpansion_integral_cexp_smul_sector hba hδ hint hF).const_smul
    (1 / (Gamma a * Gamma (b - a)))).mul_left (fun z : ℂ => exp z)
  have hba' : ∀ k : ℕ, b - a ≠ -k := fun k hk => by
    have := congrArg Complex.re hk
    simp only [Complex.neg_re, Complex.natCast_re] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have ha' : ∀ k : ℕ, a ≠ -k := fun k hk => by
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  refine ((hW.congr' ?_).congr_scale fun n => Eventually.of_forall fun x => ?_).congr_coeff ?_
  · refine Eventually.of_forall fun x => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    have hI : ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-(x * (t : ℂ))) • F t =
        ∫ t in (0 : ℝ)..1, Complex.exp (-(x * (t : ℂ))) • G t := by
      have hfun : (fun t : ℝ => Complex.exp (-(x * (t : ℂ))) • F t) =
          Set.indicator (Set.Iio 1) (fun t : ℝ => Complex.exp (-(x * (t : ℂ))) • G t) := by
        funext t
        by_cases ht : t < 1 <;> simp [hFdef, Set.indicator, ht]
      rw [hfun, setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio,
        intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    have hsub := intervalIntegral.integral_comp_sub_left
      (fun t : ℝ => exp (x * t) * (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1))
      (a := 0) (b := 1) 1
    simp only [sub_self, sub_zero] at hsub
    have hcongr : ∀ t : ℝ, exp x * (Complex.exp (-(x * (t : ℂ))) • G t) =
        exp (x * ((1 - t : ℝ) : ℂ)) * (((1 - t : ℝ) : ℂ)) ^ (a - 1) *
          (1 - (((1 - t : ℝ) : ℂ))) ^ (b - a - 1) := by
      intro t
      simp only [hGdef, smul_eq_mul]
      push_cast
      rw [show (1 : ℂ) - (1 - t) = t by ring]
      rw [← mul_assoc, ← Complex.exp_add]
      ring_nf
    have hI2 : (∫ t in (0 : ℝ)..1, exp (x * ((1 - t : ℝ) : ℂ)) *
        (((1 - t : ℝ) : ℂ)) ^ (a - 1) * (1 - (((1 - t : ℝ) : ℂ))) ^ (b - a - 1)) =
        exp x * ∫ t in (0 : ℝ)..1, Complex.exp (-(x * (t : ℂ))) • G t := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ => (hcongr t).symm
    simp only [smul_eq_mul] at hI hI2
    rw [regularized_euler_integral ha hba, ← hsub, hI]
    simp only [Complex.ofReal_sub, Complex.ofReal_one] at hI2 ⊢
    rw [hI2]
    ring
  · ring_nf
  · funext n
    have hG : Gamma (b - a + n) / Gamma (b - a) = pochhammer (b - a) n :=
      Gamma_add_nat_div_Gamma_eq (n := n) (b - a) hba'
    have hG0 : Gamma (b - a) ≠ 0 := Complex.Gamma_ne_zero hba'
    have hGa : Gamma a ≠ 0 := Complex.Gamma_ne_zero ha'
    simp only [Pi.smul_apply, smul_eq_mul, kummerCoeff]
    rw [show a - 1 = -(1 - a) by ring, ring_choose_neg_eq_pochhammer,
      show (n : ℂ) + (b - a) = b - a + n by ring, ← hG]
    field_simp
    have h1 : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    rw [h1, mul_one]

/-- The leading Kummer term gives a normalized limit in every closed right-half-plane sector. -/
theorem tendsto_regularizedHGFun_mul_exp_neg_sector {a b : ℂ} (ha : 0 < a.re)
    (hba : 0 < (b - a).re) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun z : ℂ => regularizedHGFun {a} {b} z * Gamma a /
      (exp z * z ^ (a - b))) (sectorAtTop δ) (𝓝 1) := by
  have hG : Gamma a ≠ 0 := Gamma_ne_zero fun k hk => by
    have h := congrArg Complex.re hk
    simp only [neg_re, natCast_re] at h
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h1 := hasAsymptoticExpansion_regularizedConfluent_sector_of_re_pos ha hba hδ 1
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, sub_zero, kummerCoeff_zero,
    smul_eq_mul, Nat.cast_one] at h1
  have hO := h1.mul (isBigO_refl (fun z : ℂ => Gamma a / (exp z * z ^ (a - b)))
    (sectorAtTop δ))
  have hT : Tendsto (fun z : ℂ => exp z * z ^ (a - b - 1) *
      (Gamma a / (exp z * z ^ (a - b)))) (sectorAtTop δ) (𝓝 0) := by
    have hi : Tendsto (fun z : ℂ => z⁻¹) (sectorAtTop δ) (𝓝 0) :=
      tendsto_inv₀_cobounded.comp ((tendsto_norm_atTop_iff_cobounded).mp
        (tendsto_norm_sectorAtTop δ))
    have ht := hi.const_mul (Gamma a)
    simp only [mul_zero] at ht
    refine ht.congr' ?_
    refine eventually_sectorAtTop (R := 1) fun z hz _ => ?_
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have hc := (cpow_ne_zero_iff.mpr (Or.inl hz0) : z ^ (a - b) ≠ 0)
    dsimp only
    rw [cpow_sub _ _ hz0, cpow_one]
    field_simp
  have ht := (hO.trans_tendsto hT).add_const 1
  simp only [zero_add] at ht
  refine ht.congr' ?_
  refine eventually_sectorAtTop (R := 1) fun z hz _ => ?_
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
  have hc := (cpow_ne_zero_iff.mpr (Or.inl hz0) : z ^ (a - b) ≠ 0)
  have he := exp_ne_zero z
  dsimp only
  field_simp
  ring

end DLMF.Confluent
