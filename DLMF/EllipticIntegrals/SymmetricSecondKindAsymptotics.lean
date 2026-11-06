/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.SymmetricThirdKindAsymptotics

/-!
# Two-small-node asymptotics of the second symmetric elliptic integral

The exact connection between `R_G`, `R_F` and the regularized third-kind combination
controls the two-small-node limit of `R_G`. Its first-kind coefficient vanishes with the
arithmetic mean, while the regularized third-kind remainder has logarithmic order.

## Main results

* `symmetricEllipticRG_asymp_large_z`: the two-small-node approximation, DLMF 19.27.4.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory Asymptotics
open scoped Real Topology

namespace DLMF.EllipticIntegrals
namespace SymmetricSecondKindEndpoint

open SymmetricLogarithmicEndpoint SymmetricThirdKindEndpoint

/-- The coefficient of `R_F` in the regularized second-kind connection. -/
def firstKindCoefficient (x y z : ℝ) : ℝ := z - (x - z) * (y - z) / z

/-- The coefficient of the regularized third-kind combination. -/
def regularizedCoefficient (x y z : ℝ) : ℝ := (x - z) * (y - z) / (3 * z)

/-- The elementary remainder in the regularized second-kind connection. -/
def constantTerm (x y z : ℝ) : ℝ :=
  (x - z) * (y - z) / (z * √z) + ellAsymG x y / √z - √z

/-- The second-kind connection with nonnegative first node and positive other nodes. -/
theorem two_mul_symmetricEllipticRG_of_pos {x y z : ℝ} (hx : 0 ≤ x)
    (hy : 0 < y) (hz : 0 < z) :
    2 * symmetricEllipticRG x y z = (z : ℂ) * symmetricEllipticRF x y z -
      (((x - z) * (y - z) / 3 : ℝ) : ℂ) * symmetricEllipticRD x y z +
        ((ellAsymG x y / √z : ℝ) : ℂ) := by
  have hxc : IsCarlsonArgument (x : ℂ) := by
    rcases hx.eq_or_lt with h | h
    · right; exact_mod_cast h.symm
    · exact Or.inl (ofReal_mem_slitPlane.mpr h)
  have H := two_mul_symmetricEllipticRG hxc (ofReal_mem_slitPlane.mpr hy)
    (ofReal_mem_slitPlane.mpr hz)
  rw [Carlson.ofReal_cpow_half hx, Carlson.ofReal_cpow_half hy.le,
    show (-1 / 2 : ℂ) = -(1 / 2 : ℂ) by ring,
    cpow_neg, Carlson.ofReal_cpow_half hz.le] at H
  dsimp only [ellAsymG]
  rw [Real.sqrt_mul hx]
  push_cast at H ⊢
  linear_combination H

/-- The second-kind connection allows either of its small nodes to be zero. -/
theorem two_mul_symmetricEllipticRG_of_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 < z) (ha : 0 < ellAsymA x y) :
    2 * symmetricEllipticRG x y z = (z : ℂ) * symmetricEllipticRF x y z -
      (((x - z) * (y - z) / 3 : ℝ) : ℂ) * symmetricEllipticRD x y z +
        ((ellAsymG x y / √z : ℝ) : ℂ) := by
  rcases hy.eq_or_lt with hy0 | hy0
  · have hx' : 0 < x := by dsimp only [ellAsymA] at ha; linarith
    have H := two_mul_symmetricEllipticRG_of_pos hy hx' hz
    have hRD : symmetricEllipticRD y x z = symmetricEllipticRD x y z :=
      symmetricEllipticRJ_comm_left x y z z
    have hg : ellAsymG y x = ellAsymG x y := by simp only [ellAsymG, mul_comm]
    rw [symmetricEllipticRG_comm_left x y z, symmetricEllipticRF_comm_left x y z,
      hRD, hg] at H
    push_cast at H ⊢
    linear_combination H
  · exact two_mul_symmetricEllipticRG_of_pos hx hy0 hz

/-- The regularized second-kind connection isolates the nonzero endpoint value. -/
theorem symmetricEllipticRG_sub_sqrt_eq {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 < z) (ha : 0 < ellAsymA x y) :
    symmetricEllipticRG x y z - ((√z / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) *
      ((firstKindCoefficient x y z : ℂ) * symmetricEllipticRF x y z -
        (regularizedCoefficient x y z : ℂ) * regularizedThirdKind x y z z +
          (constantTerm x y z : ℂ)) := by
  have hRC : symmetricEllipticRC z z = (√z : ℂ)⁻¹ := by
    have H := symmetricEllipticRC_special.1 z (ofReal_mem_slitPlane.mpr hz)
    rwa [cpow_neg, Carlson.ofReal_cpow_half hz.le] at H
  have hD : symmetricEllipticRD x y z =
      (regularizedThirdKind x y z z + 3 * symmetricEllipticRF x y z -
        3 * (√z : ℂ)⁻¹) / z := by
    dsimp only [regularizedThirdKind, symmetricEllipticRD]
    rw [hRC]
    field_simp [ofReal_ne_zero.mpr hz.ne',
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hz).ne']
    ring
  have H := two_mul_symmetricEllipticRG_of_nonneg hx hy hz ha
  rw [hD] at H
  dsimp only [firstKindCoefficient, regularizedCoefficient, constantTerm]
  push_cast at H ⊢
  linear_combination (1 / 2 : ℂ) * H

/-- The elementary coefficients vanish at arithmetic-mean rate near the endpoint. -/
theorem coefficient_bounds {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z)
    (haz : ellAsymA x y ≤ z) :
    (0 ≤ firstKindCoefficient x y z ∧ firstKindCoefficient x y z ≤ 2 * ellAsymA x y) ∧
      |constantTerm x y z| ≤ 2 * ellAsymA x y / √z := by
  let a : ℝ := ellAsymA x y
  have ha : 0 ≤ a := by dsimp only [a, ellAsymA]; positivity
  have hmean : x + y = 2 * a := by dsimp only [a, ellAsymA]; ring
  have hxy : 0 ≤ x * y := mul_nonneg hx hy
  have hxya : x * y ≤ a ^ 2 := by dsimp only [a, ellAsymA]; nlinarith [sq_nonneg (x - y)]
  have hxydiv : x * y / z ≤ a := by
    apply (div_le_iff₀ hz).mpr
    exact hxya.trans (by nlinarith [mul_nonneg ha (sub_nonneg.mpr haz)])
  have hxydiv0 : 0 ≤ x * y / z := div_nonneg hxy hz.le
  have hg0 : 0 ≤ ellAsymG x y := Real.sqrt_nonneg _
  have hga : ellAsymG x y ≤ a := by
    have H := (comparisonParameter_bounds hx hy).2
    dsimp only [comparisonParameter] at H
    linarith
  have hU : firstKindCoefficient x y z = x + y - x * y / z := by
    unfold firstKindCoefficient
    field_simp
    ring
  have hroot := Real.sqrt_pos.mpr hz
  have hV : constantTerm x y z = (-(x + y) + x * y / z + ellAsymG x y) / √z := by
    calc constantTerm x y z = (x - z) * (y - z) / (z * √z) +
        ellAsymG x y / √z - z / √z := by
          unfold constantTerm
          congr 1
          apply (eq_div_iff hroot.ne').mpr
          exact Real.mul_self_sqrt hz.le
      _ = _ := by field_simp; ring
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hU]; linarith
  · rw [hU]; linarith
  · rw [hV, abs_div, abs_of_pos hroot]
    apply div_le_div_of_nonneg_right _ hroot.le
    apply abs_le.mpr
    constructor <;> linarith

/-- The comparison logarithm has ordinary logarithmic order in the arithmetic mean. -/
theorem logarithmicTerm_isBigO_log {z : ℝ} (hz : 0 < z) :
    (fun q : ℝ × ℝ => ((logarithmicTerm z (comparisonParameter q.1 q.2) : ℝ) : ℂ))
      =O[𝓝[ellAsymPair] 0] (fun q : ℝ × ℝ => (Real.log (z / ellAsymA q.1 q.2) : ℂ)) := by
  have HC : (fun q : ℝ × ℝ => ((logarithmicTerm z (comparisonParameter q.1 q.2) : ℝ) : ℂ))
      =O[𝓝[ellAsymPair] 0] (fun q : ℝ × ℝ => (Real.log (8 * z / ellAsymA q.1 q.2) : ℂ)) := by
    refine isBigO_iff.mpr ⟨1 / (2 * √z), ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      tendsto_arithmeticMean_zero.eventually (eventually_lt_nhds hz)] with q hq hsmall
    have ha := arithmeticMean_pos_of_mem hq
    have hs := comparisonParameter_pos ha
    have hslo := (comparisonParameter_bounds hq.1 hq.2.1).1
    have hshi := (comparisonParameter_bounds hq.1 hq.2.1).2
    have hL := logarithmicTerm_nonneg hz hs (hshi.trans hsmall.le)
    have hlog : 0 ≤ Real.log (8 * z / ellAsymA q.1 q.2) :=
      Real.log_nonneg ((le_div_iff₀ ha).mpr (by linarith))
    have hratio : 4 * z / comparisonParameter q.1 q.2 ≤ 8 * z / ellAsymA q.1 q.2 := by
      apply (div_le_div_iff₀ hs ha).mpr
      nlinarith [mul_le_mul_of_nonneg_left hslo (show 0 ≤ 8 * z by positivity)]
    have hlogle := Real.log_le_log (div_pos (by positivity : 0 < 4 * z) hs) hratio
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
    change Real.log (4 * z / comparisonParameter q.1 q.2) / (2 * √z) ≤ _
    calc _ ≤ Real.log (8 * z / ellAsymA q.1 q.2) / (2 * √z) :=
        div_le_div_of_nonneg_right hlogle (by positivity : 0 ≤ 2 * √z)
      _ = _ := by ring
  have HL := (Real.isBigO_log_const_div_log_const_div_nhdsGT_zero
    (by positivity : 0 < 8 * z) hz).comp_tendsto tendsto_arithmeticMean_zero_pos
  have HL' : (fun q : ℝ × ℝ => (Real.log (8 * z / ellAsymA q.1 q.2) : ℂ))
      =O[𝓝[ellAsymPair] 0] (fun q : ℝ × ℝ => (Real.log (z / ellAsymA q.1 q.2) : ℂ)) := by
    apply Complex.isBigO_ofReal_left.mpr
    apply Complex.isBigO_ofReal_right.mpr
    simpa only [Function.comp_def] using HL
  exact HC.trans HL'

/-- A linear arithmetic-mean error is dominated by its logarithmic multiple. -/
theorem arithmeticMean_isBigO_mul_log {z : ℝ} (hz : 0 < z) :
    (fun q : ℝ × ℝ => (ellAsymA q.1 q.2 : ℂ)) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((ellAsymA q.1 q.2 * Real.log (z / ellAsymA q.1 q.2) : ℝ) : ℂ)) := by
  have H := (Real.isLittleO_const_log_const_div_nhdsGT_zero hz (1 : ℝ)).isBigO.comp_tendsto
    tendsto_arithmeticMean_zero_pos
  have HC : (fun _ : ℝ × ℝ => (1 : ℂ)) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => (Real.log (z / ellAsymA q.1 q.2) : ℂ)) := by
    apply Complex.isBigO_ofReal_left.mpr
    apply Complex.isBigO_ofReal_right.mpr
    simpa only [Function.comp_def, ofReal_one] using H
  simpa only [← ofReal_mul, mul_one] using
    (isBigO_refl (fun q : ℝ × ℝ => (ellAsymA q.1 q.2 : ℂ)) (𝓝[ellAsymPair] 0)).mul HC

/-- The first symmetric integral has logarithmic order in the arithmetic mean. -/
theorem symmetricEllipticRF_isBigO_log {z : ℝ} (hz : 0 < z) :
    (fun q : ℝ × ℝ => symmetricEllipticRF q.1 q.2 z) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => (Real.log (z / ellAsymA q.1 q.2) : ℂ)) := by
  have hA : (fun q : ℝ × ℝ => (ellAsymA q.1 q.2 : ℂ)) =O[𝓝[ellAsymPair] 0]
      (fun _ => (1 : ℂ)) :=
    Complex.isBigO_ofReal_left.mpr (tendsto_arithmeticMean_zero.isBigO_one ℂ)
  have hAL : (fun q : ℝ × ℝ => ((ellAsymA q.1 q.2 * Real.log (z / ellAsymA q.1 q.2) : ℝ) : ℂ))
      =O[𝓝[ellAsymPair] 0] (fun q : ℝ × ℝ => (Real.log (z / ellAsymA q.1 q.2) : ℂ)) := by
    simpa only [← ofReal_mul, one_mul] using hA.mul
      (isBigO_refl (fun q : ℝ × ℝ => (Real.log (z / ellAsymA q.1 q.2) : ℂ)) (𝓝[ellAsymPair] 0))
  have H := ((symmetricEllipticRF_sub_logarithmicTerm_isBigO hz hz).trans hAL).add
    (logarithmicTerm_isBigO_log hz)
  apply H.congr_left
  intro q
  ring


/-- The first-kind coefficient vanishes at arithmetic-mean rate. -/
theorem firstKindCoefficient_isBigO_mean {z : ℝ} (hz : 0 < z) :
    (fun q : ℝ × ℝ => (firstKindCoefficient q.1 q.2 z : ℂ)) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => (ellAsymA q.1 q.2 : ℂ)) := by
  refine isBigO_iff.mpr ⟨2, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    tendsto_arithmeticMean_zero.eventually (eventually_lt_nhds hz)] with q hq hsmall
  have ha := arithmeticMean_pos_of_mem hq
  have H := coefficient_bounds hq.1 hq.2.1 hz hsmall.le
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg H.1.1,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha.le]
  exact H.1.2

/-- The elementary constant term vanishes at arithmetic-mean rate. -/
theorem constantTerm_isBigO_mean {z : ℝ} (hz : 0 < z) :
    (fun q : ℝ × ℝ => (constantTerm q.1 q.2 z : ℂ)) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => (ellAsymA q.1 q.2 : ℂ)) := by
  refine isBigO_iff.mpr ⟨2 / √z, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    tendsto_arithmeticMean_zero.eventually (eventually_lt_nhds hz)] with q hq hsmall
  have ha := arithmeticMean_pos_of_mem hq
  have H := coefficient_bounds hq.1 hq.2.1 hz hsmall.le
  rw [Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha.le]
  calc _ ≤ 2 * ellAsymA q.1 q.2 / √z := H.2
    _ = _ := by ring

/-- The third-kind coefficient stays bounded at the two-small-node endpoint. -/
theorem regularizedCoefficient_isBigO_one {z : ℝ} :
    (fun q : ℝ × ℝ => (regularizedCoefficient q.1 q.2 z : ℂ)) =O[𝓝[ellAsymPair] 0]
      (fun _ => (1 : ℂ)) := by
  have H : Continuous (fun q : ℝ × ℝ => (regularizedCoefficient q.1 q.2 z : ℂ)) := by
    unfold regularizedCoefficient
    fun_prop
  exact ((H.tendsto (0 : ℝ × ℝ)).mono_left nhdsWithin_le_nhds).isBigO_one ℂ

end SymmetricSecondKindEndpoint
/-- DLMF 19.27.4: `R_G(x, y, z) = (√z/2)(1 + O((a/z) ln(z/a)))` as `a/z → 0`: for fixed
`z > 0`, as `(x, y) → 0` through nonnegative pairs not both zero. -/
@[dlmf 19.27.E4]
theorem symmetricEllipticRG_asymp_large_z {z : ℝ} (hz : 0 < z) :
    (fun q : ℝ × ℝ => symmetricEllipticRG q.1 q.2 z - ((√z / 2 : ℝ) : ℂ)) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((√z / 2 * (ellAsymA q.1 q.2 / z *
        Real.log (z / ellAsymA q.1 q.2)) : ℝ) : ℂ)) := by
  have H1 : (fun q : ℝ × ℝ =>
      (SymmetricSecondKindEndpoint.firstKindCoefficient q.1 q.2 z : ℂ) *
        symmetricEllipticRF q.1 q.2 z) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((ellAsymA q.1 q.2 * Real.log (z / ellAsymA q.1 q.2) : ℝ) : ℂ)) := by
    simpa only [← ofReal_mul] using
      (SymmetricSecondKindEndpoint.firstKindCoefficient_isBigO_mean hz).mul
        (SymmetricSecondKindEndpoint.symmetricEllipticRF_isBigO_log hz)
  have H2 : (fun q : ℝ × ℝ =>
      (SymmetricSecondKindEndpoint.regularizedCoefficient q.1 q.2 z : ℂ) *
        SymmetricThirdKindEndpoint.regularizedThirdKind q.1 q.2 z z) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((ellAsymA q.1 q.2 * Real.log (z / ellAsymA q.1 q.2) : ℝ) : ℂ)) := by
    simpa only [one_mul] using SymmetricSecondKindEndpoint.regularizedCoefficient_isBigO_one.mul
      (SymmetricThirdKindEndpoint.regularizedThirdKind_isBigO hz hz)
  have H3 := (SymmetricSecondKindEndpoint.constantTerm_isBigO_mean hz).trans
    (SymmetricSecondKindEndpoint.arithmeticMean_isBigO_mul_log hz)
  have H := ((H1.sub H2).add H3).const_mul_left (1 / 2 : ℂ)
  let κ : ℝ := √z / (2 * z)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have H' := Asymptotics.IsBigO.const_mul_right (ofReal_ne_zero.mpr hκ.ne') H
  apply H'.congr' ?_ (Filter.Eventually.of_forall fun q => ?_)
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact (SymmetricSecondKindEndpoint.symmetricEllipticRG_sub_sqrt_eq hq.1 hq.2.1 hz
      (SymmetricLogarithmicEndpoint.arithmeticMean_pos_of_mem hq)).symm
  · dsimp only [κ]
    push_cast
    ring

end DLMF.EllipticIntegrals
