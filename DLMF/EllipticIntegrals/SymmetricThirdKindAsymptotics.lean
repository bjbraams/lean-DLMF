/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.SymmetricLogarithmicAsymptotics
public import DLMFMathlib.Analysis.Integral.SquareRootPairRegularization

/-!
# Logarithmic endpoint asymptotics of the third symmetric elliptic integral

The combination `p R_J(x,y,z,p)-3 R_F(x,y,z)+3 R_C(z,p)` removes the two-small-node
logarithmic singularity. Its regular real kernel has a numerator bounded by `a/(t+a)`,
where `a=(x+y)/2`, giving uniform logarithmic error bounds for positive parameters.
The negative-parameter formula follows by a principal-value change of parameter to a
positive companion. Specializing the parameter to the outer node gives the corresponding
`R_D` approximation.

## Main results

* `symmetricEllipticRJ_zero_asymptotic`: the one-zero-node formula for nonzero real
  parameters, DLMF 19.20.11.
* `symmetricEllipticRJ_asymp_small_xy`: the two-small-node formula with positive parameter,
  DLMF 19.27.13.
* `symmetricEllipticRD_asymp_large_z`: the two-small-node specialization, DLMF 19.27.7.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory Asymptotics
open scoped Real Topology

namespace DLMF.EllipticIntegrals
namespace SymmetricThirdKindEndpoint

open SymmetricLogarithmicEndpoint

/-- The third-kind combination after removing its first-kind logarithmic part.
For negative real parameters, the `R_J` and `R_C` values use their principal-value definitions. -/
def regularizedThirdKind (x y z p : ℝ) : ℂ :=
  (p : ℂ) * symmetricEllipticRJ x y z p - 3 * symmetricEllipticRF x y z +
    3 * symmetricEllipticRC z p

/-- The logarithmic singularities cancel to give a regular real integral. -/
theorem regularizedThirdKind_eq_integral {x y z p : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 < z) (hp : 0 < p) (ha : 0 < ellAsymA x y) :
    regularizedThirdKind x y z p = (3 / 2 : ℂ) *
      ((∫ t in Ioi (0 : ℝ), SquareRootPairRegularization.kernel x y z p t : ℝ) : ℂ) := by
  have hFJ := integrableOn_carlsonRootProduct_inv_of_nonneg hz hx hy
    (fun h => by dsimp only [ellAsymA] at ha; intro h'; rw [h, h'] at ha; norm_num at ha) hp
  have hF : IntegrableOn (fun t => (carlsonRootProduct x y z t)⁻¹) (Ioi 0) := by
    simpa only [carlsonRootProduct, mul_comm, mul_left_comm, mul_assoc] using hFJ.1
  have hJ : IntegrableOn (fun t =>
      (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹) (Ioi 0) := by
    simpa only [carlsonRootProduct, mul_comm, mul_left_comm, mul_assoc] using hFJ.2
  have hC := integrableOn_symmetricEllipticRC_integrand
    (Or.inl (ofReal_mem_slitPlane.mpr hz)) (ofReal_mem_slitPlane.mpr hp)
  have hJF : IntegrableOn (fun t : ℝ =>
      (p : ℂ) * (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹ -
        (carlsonRootProduct x y z t)⁻¹) (Ioi 0) := (hJ.const_mul _).sub hF
  have H : (p : ℂ) * (∫ t in Ioi (0 : ℝ),
      (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹) -
      (∫ t in Ioi (0 : ℝ), (carlsonRootProduct x y z t)⁻¹) +
      (∫ t in Ioi (0 : ℝ), (((t : ℂ) + z) ^ (1 / 2 : ℂ) * ((t : ℂ) + p))⁻¹) =
      ((∫ t in Ioi (0 : ℝ), SquareRootPairRegularization.kernel x y z p t : ℝ) : ℂ) := by
    rw [← integral_const_mul, ← integral_sub (hJ.const_mul _) hF,
      ← integral_add hJF hC, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have htx : 0 < t + x := add_pos_of_pos_of_nonneg ht hx
    have hty : 0 < t + y := add_pos_of_pos_of_nonneg ht hy
    have htz : 0 < t + z := add_pos ht hz
    have htp : 0 < t + p := add_pos ht hp
    simp only [carlsonRootProduct, ← ofReal_add]
    rw [Carlson.ofReal_cpow_half htx.le, Carlson.ofReal_cpow_half hty.le,
      Carlson.ofReal_cpow_half htz.le]
    dsimp only [SquareRootPairRegularization.kernel, SquareRootPairRegularization.numerator]
    simp only [ofReal_div, ofReal_sub, ofReal_one, ofReal_mul, ofReal_add]
    have hpc : (t : ℂ) + p ≠ 0 := by exact_mod_cast htp.ne'
    field_simp [hpc, ofReal_ne_zero.mpr (Real.sqrt_pos.mpr htx).ne',
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hty).ne',
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr htz).ne']
    ring
  simp only [regularizedThirdKind, symmetricEllipticRF, symmetricEllipticRJ,
    symmetricEllipticRC, not_isNegReal_of_mem_slitPlane (ofReal_mem_slitPlane.mpr hp),
    ↓reduceIte]
  linear_combination (3 / 2 : ℂ) * H

/-- A uniform logarithmic bound for the regularized third-kind integral. -/
theorem norm_regularizedThirdKind_le_uniform {x y z p m P : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) (ha : 0 < ellAsymA x y)
    (hm : 0 < m) (hmp : m ≤ p) (hpP : p ≤ P) (ham : ellAsymA x y ≤ m / 2) :
    ‖regularizedThirdKind x y z p‖ ≤
      (3 / (m * √z)) * (ellAsymA x y * Real.log (P / ellAsymA x y)) := by
  have hp : 0 < p := hm.trans_le hmp
  have hap : ellAsymA x y < p := by linarith
  have hI := SquareRootPairRegularization.integral_kernel_bounds hx hy hz ha hap
  have H := SquareRootPairRegularization.integral_kernel_le_uniform hx hy hz ha hm hmp hpP ham
  rw [regularizedThirdKind_eq_integral hx hy hz hp ha, norm_mul,
    show ‖(3 / 2 : ℂ)‖ = (3 / 2 : ℝ) by norm_num [norm_div],
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hI.1]
  calc _ ≤ (3 / 2 : ℝ) * ((2 / (m * √z)) *
      (ellAsymA x y * Real.log (P / ellAsymA x y))) :=
        mul_le_mul_of_nonneg_left H (by norm_num)
    _ = _ := by ring


/-- The arithmetic mean approaches zero through positive values on the endpoint domain. -/
theorem tendsto_arithmeticMean_zero_pos :
    Tendsto (fun q : ℝ × ℝ => ellAsymA q.1 q.2) (𝓝[ellAsymPair] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_arithmeticMean_zero, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact arithmeticMean_pos_of_mem hq

/-- The first-kind remainder has arithmetic-mean logarithmic order. -/
theorem symmetricEllipticRF_sub_logarithmicTerm_isBigO {z p : ℝ} (hz : 0 < z) (hp : 0 < p) :
    (fun q : ℝ × ℝ => symmetricEllipticRF q.1 q.2 z -
      ((logarithmicTerm z (comparisonParameter q.1 q.2) : ℝ) : ℂ)) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((ellAsymA q.1 q.2 * Real.log (p / ellAsymA q.1 q.2) : ℝ) : ℂ)) := by
  have hRF : (fun q : ℝ × ℝ => symmetricEllipticRF q.1 q.2 z -
      ((logarithmicTerm z (comparisonParameter q.1 q.2) : ℝ) : ℂ)) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((ellAsymA q.1 q.2 / z *
        logarithmicTerm z (comparisonParameter q.1 q.2) : ℝ) : ℂ)) := by
    simpa only [logarithmicTerm_comparisonParameter] using symmetricEllipticRF_asymp_large_z hz
  have hcompare : (fun q : ℝ × ℝ => ((ellAsymA q.1 q.2 / z *
      logarithmicTerm z (comparisonParameter q.1 q.2) : ℝ) : ℂ)) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((ellAsymA q.1 q.2 * Real.log (8 * z / ellAsymA q.1 q.2) : ℝ) : ℂ)) := by
    refine isBigO_iff.mpr ⟨1 / (2 * z * √z), ?_⟩
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
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (div_nonneg ha.le hz.le) hL),
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha.le hlog)]
    change ellAsymA q.1 q.2 / z * (Real.log (4 * z / comparisonParameter q.1 q.2) /
      (2 * √z)) ≤ _
    calc _ ≤ ellAsymA q.1 q.2 / z * (Real.log (8 * z / ellAsymA q.1 q.2) /
        (2 * √z)) := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hlogle (by positivity)) (by positivity)
      _ = _ := by ring
  have hlog := (Real.isBigO_log_const_div_log_const_div_nhdsGT_zero
    (by positivity : 0 < 8 * z) hp).comp_tendsto tendsto_arithmeticMean_zero_pos
  have hreal : (fun q : ℝ × ℝ => ellAsymA q.1 q.2 * Real.log (8 * z / ellAsymA q.1 q.2))
      =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ellAsymA q.1 q.2 * Real.log (p / ellAsymA q.1 q.2)) := by
    simpa only [Function.comp_def] using
      (isBigO_refl (fun q : ℝ × ℝ => ellAsymA q.1 q.2) (𝓝[ellAsymPair] 0)).mul hlog
  exact (hRF.trans hcompare).trans
    (Complex.isBigO_ofReal_left.mpr (Complex.isBigO_ofReal_right.mpr hreal))

/-- The regularized third-kind combination has arithmetic-mean logarithmic order. -/
theorem regularizedThirdKind_isBigO {z p : ℝ} (hz : 0 < z) (hp : 0 < p) :
    (fun q : ℝ × ℝ => regularizedThirdKind q.1 q.2 z p) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((ellAsymA q.1 q.2 * Real.log (p / ellAsymA q.1 q.2) : ℝ) : ℂ)) := by
  refine isBigO_iff.mpr ⟨3 / (p * √z), ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    tendsto_arithmeticMean_zero.eventually (eventually_lt_nhds (half_pos hp))] with q hq hsmall
  have ha := arithmeticMean_pos_of_mem hq
  have hlog : 0 ≤ Real.log (p / ellAsymA q.1 q.2) :=
    Real.log_nonneg ((le_div_iff₀ ha).mpr (by linarith))
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha.le hlog)]
  exact norm_regularizedThirdKind_le_uniform hq.1 hq.2.1 hz ha hp le_rfl le_rfl hsmall.le


/-- The single-zero-node path lies in the two-node approach domain. -/
theorem tendsto_zero_pair :
    Tendsto (fun y : ℝ => ((0 : ℝ), y)) (𝓝[>] 0) (𝓝[ellAsymPair] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have he : ((0 : ℝ), (0 : ℝ)) = (0 : ℝ × ℝ) := by ext <;> simp
    rw [← he]
    exact (continuous_const.prodMk continuous_id).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact ⟨le_rfl, hy.le, fun h => hy.ne' (congrArg Prod.snd h)⟩

/-- The arithmetic-mean logarithmic remainder along a single-zero-node path. -/
theorem mean_log_zero_isBigO {p : ℝ} (hp : 0 < p) :
    (fun y : ℝ => ((ellAsymA 0 y * Real.log (p / ellAsymA 0 y) : ℝ) : ℂ))
      =O[𝓝[>] 0] (fun y : ℝ => ((y * Real.log y : ℝ) : ℂ)) := by
  have H := ((isBigO_refl (fun y : ℝ => y) (𝓝[>] (0 : ℝ))).mul
    (Real.isBigO_log_const_div_log_nhdsGT_zero (by positivity : 0 < 2 * p))).const_mul_left
      (1 / 2 : ℝ)
  apply Complex.isBigO_ofReal_left.mpr
  apply Complex.isBigO_ofReal_right.mpr
  apply H.congr_left
  intro y
  simp only [ellAsymA, zero_add]
  have he : p / (y / 2) = 2 * p / y := by rw [div_div_eq_mul_div]; ring
  rw [he]
  ring

/-- The comparison logarithm on the single-zero-node path. -/
theorem logarithmicTerm_zero (y z : ℝ) :
    logarithmicTerm z (comparisonParameter 0 y) = Real.log (16 * z / y) / (2 * √z) := by
  rw [logarithmicTerm_comparisonParameter]
  simp only [ellAsymA, ellAsymG, zero_add, zero_mul, Real.sqrt_zero, add_zero]
  rw [div_div_eq_mul_div]
  congr 2
  ring

/-- The first-kind logarithmic remainder along the single-zero-node path. -/
theorem symmetricEllipticRF_zero_sub_log_isBigO {z : ℝ} (hz : 0 < z) :
    (fun y : ℝ => symmetricEllipticRF 0 y z -
      ((Real.log (16 * z / y) / (2 * √z) : ℝ) : ℂ)) =O[𝓝[>] 0]
      (fun y : ℝ => ((y * Real.log y : ℝ) : ℂ)) := by
  have H := ((symmetricEllipticRF_sub_logarithmicTerm_isBigO hz (p := 1) (by norm_num)).comp_tendsto
    tendsto_zero_pair).trans (mean_log_zero_isBigO (p := 1) (by norm_num))
  simpa only [Function.comp_def, logarithmicTerm_zero, ofReal_zero] using H

/-- The first symmetric integral has logarithmic growth on the single-zero-node path. -/
theorem symmetricEllipticRF_zero_isBigO_log {z : ℝ} (hz : 0 < z) :
    (fun y : ℝ => symmetricEllipticRF 0 y z) =O[𝓝[>] 0] (fun y : ℝ => (Real.log y : ℂ)) := by
  have H := (Real.isBigO_log_const_div_log_nhdsGT_zero (by positivity : 0 < 16 * z)).const_mul_left
    (1 / (2 * √z))
  have HL : (fun y : ℝ => ((Real.log (16 * z / y) / (2 * √z) : ℝ) : ℂ))
      =O[𝓝[>] 0] (fun y : ℝ => (Real.log y : ℂ)) := by
    apply Complex.isBigO_ofReal_left.mpr
    apply Complex.isBigO_ofReal_right.mpr
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using H
  exact (symmetricEllipticRF_zero_isEquivalent hz).isBigO.trans HL

/-- The regularized single-zero-node remainder is uniform for a parameter with positive limit. -/
theorem regularizedThirdKind_zero_isBigO_of_tendsto {z p : ℝ} {P : ℝ → ℝ}
    (hz : 0 < z) (hp : 0 < p) (hP : Tendsto P (𝓝[>] 0) (𝓝 p)) :
    (fun y : ℝ => regularizedThirdKind 0 y z (P y)) =O[𝓝[>] 0]
      (fun y : ℝ => ((y * Real.log y : ℝ) : ℂ)) := by
  have H : (fun y : ℝ => regularizedThirdKind 0 y z (P y)) =O[𝓝[>] 0]
      (fun y : ℝ => ((ellAsymA 0 y * Real.log (2 * p / ellAsymA 0 y) : ℝ) : ℂ)) := by
    refine isBigO_iff.mpr ⟨3 / ((p / 2) * √z), ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      hP.eventually (eventually_gt_nhds (half_lt_self hp)),
      hP.eventually (eventually_lt_nhds (by linarith : p < 2 * p)),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds (half_pos hp))]
      with y hy hlo hhi hsmall
    have hy0 : 0 < y := hy
    have ha : 0 < ellAsymA 0 y := by simp only [ellAsymA, zero_add]; positivity
    have ham : ellAsymA 0 y ≤ (p / 2) / 2 := by simp only [ellAsymA, zero_add]; linarith
    have hlog : 0 ≤ Real.log (2 * p / ellAsymA 0 y) :=
      Real.log_nonneg ((le_div_iff₀ ha).mpr (by linarith))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha.le hlog)]
    exact norm_regularizedThirdKind_le_uniform le_rfl hy.le hz ha (half_pos hp)
      hlo.le hhi.le ham
  exact H.trans (mean_log_zero_isBigO (mul_pos (by norm_num) hp))


/-- The positive companion parameter for a negative third-kind parameter. -/
def negativeParameterCompanion (z p y : ℝ) : ℝ := z * (p - y) / (p - z)

/-- The companion of a negative parameter is positive for nonnegative nodes. -/
theorem negativeParameterCompanion_pos {z p y : ℝ} (hz : 0 < z) (hp : p < 0) (hy : 0 ≤ y) :
    0 < negativeParameterCompanion z p y := by
  unfold negativeParameterCompanion
  exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hz (by linarith)) (by linarith)

/-- The positive companion stays below the outer node when the small node does. -/
theorem negativeParameterCompanion_lt {z p y : ℝ} (hz : 0 < z) (hp : p < 0) (hy : y < z) :
    negativeParameterCompanion z p y < z := by
  unfold negativeParameterCompanion
  apply (div_lt_iff_of_neg (by linarith : p - z < 0)).mpr
  nlinarith [mul_pos hz (sub_pos.mpr hy)]

/-- The fixed-endpoint companion transforms the principal-value `R_C` into a positive value. -/
theorem symmetricEllipticRC_negativeParameterCompanion {z p : ℝ} (hz : 0 < z) (hp : p < 0) :
    symmetricEllipticRC z p = ((z / (z - p) : ℝ) : ℂ) *
      symmetricEllipticRC z (negativeParameterCompanion z p 0) := by
  let l : ℝ := z / (z - p)
  have hzp : 0 < z - p := by linarith
  have hl : 0 < l := div_pos hz hzp
  have hpz : p - z ≠ 0 := by linarith
  have hlz : l * (z - p) = z := by dsimp only [l]; field_simp
  have hlp : l * (-p) = negativeParameterCompanion z p 0 := by
    dsimp only [l, negativeParameterCompanion]
    simp only [sub_zero]
    field_simp [hzp.ne', hpz]
    ring
  have H := symmetricEllipticRC_mul_ofReal_pos hl hzp (neg_pos.mpr hp)
  rw [hlz, hlp] at H
  have Hneg := (symmetricEllipticRC_of_neg hp hz.le).1
  simp only [← ofReal_sub, ← ofReal_neg] at Hneg
  change symmetricEllipticRC z p = (√l : ℂ) * symmetricEllipticRC (z - p : ℝ) (-p : ℝ) at Hneg
  have hsquare : (√l : ℂ) ^ 2 = (l : ℂ) := by exact_mod_cast Real.sq_sqrt hl.le
  change symmetricEllipticRC z p = (l : ℂ) * symmetricEllipticRC z _
  rw [Hneg, H, ← hsquare]
  field_simp [ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hl).ne']

/-- The negative-parameter change connects `R_J` to its positive companion. -/
theorem negativeParameterCompanion_change {z p y : ℝ} (hz : 0 < z) (hp : p < 0) (hy : 0 < y) :
    ((p - z : ℝ) : ℂ) * symmetricEllipticRJ 0 y z p +
      ((negativeParameterCompanion z p y - z : ℝ) : ℂ) *
        symmetricEllipticRJ 0 y z (negativeParameterCompanion z p y) =
      3 * symmetricEllipticRF 0 y z := by
  have hQ := negativeParameterCompanion_pos hz hp hy.le
  have hpz : p - z ≠ 0 := by linarith
  have hrel : (p - z) * (negativeParameterCompanion z p y - z) = (0 - z) * (y - z) := by
    dsimp only [negativeParameterCompanion]
    field_simp [hpz]
    ring
  have H := symmetricEllipticRJ_change_parameter' (x := z) (y := 0) (z := y)
    (p := p) (q := negativeParameterCompanion z p y) hz le_rfl hy.le
    (fun _ => hy.ne') hp.ne hQ.ne' hrel
  simp only [ofReal_zero] at H
  rw [symmetricEllipticRJ_comm_left 0 z y p, symmetricEllipticRJ_comm_right 0 y z p,
    symmetricEllipticRJ_comm_left 0 z y (negativeParameterCompanion z p y),
    symmetricEllipticRJ_comm_right 0 y z (negativeParameterCompanion z p y),
    symmetricEllipticRF_comm_left 0 z y, symmetricEllipticRF_comm_right 0 y z] at H
  simp only [zero_mul, zero_div, ofReal_zero] at H
  have hneg : p * negativeParameterCompanion z p y / z < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hp hQ) hz
  rw [symmetricEllipticRC_special.2.2.2 _ hneg, mul_zero, sub_zero] at H
  exact H


/-- The regularized logarithmic remainder for a fixed negative parameter. -/
theorem regularizedThirdKind_zero_isBigO_of_neg {z p : ℝ} (hz : 0 < z) (hp : p < 0) :
    (fun y : ℝ => regularizedThirdKind 0 y z p) =O[𝓝[>] 0]
      (fun y : ℝ => ((y * Real.log y : ℝ) : ℂ)) := by
  let Q : ℝ → ℝ := negativeParameterCompanion z p
  let B : ℝ → ℝ := fun y => (Q y - z) / ((p - z) * Q y)
  let C : ℝ → ℝ := fun y => p * (3 * z / ((p - z) * Q y)) - 3
  let G : ℝ → ℝ := fun y => 3 * B y *
    (Real.log ((√z + √(z - Q y)) / √(Q y)) / √(z - Q y))
  have hpzneg : p - z < 0 := by linarith
  have hpz : p - z ≠ 0 := hpzneg.ne
  have hzp : z - p ≠ 0 := by linarith
  have hQ0 : 0 < Q 0 := negativeParameterCompanion_pos hz hp le_rfl
  have hQ0z : Q 0 < z := negativeParameterCompanion_lt hz hp hz
  have hZQ0 : 0 < z - Q 0 := sub_pos.mpr hQ0z
  have hrootz : 0 < √z := Real.sqrt_pos.mpr hz
  have hrootQ : 0 < √(Q 0) := Real.sqrt_pos.mpr hQ0
  have hrootZQ : 0 < √(z - Q 0) := Real.sqrt_pos.mpr hZQ0
  have hQ : DifferentiableAt ℝ Q 0 := by unfold Q negativeParameterCompanion; fun_prop
  have hB : DifferentiableAt ℝ B 0 := by unfold B; fun_prop (disch := positivity)
  have hC : DifferentiableAt ℝ C 0 := by unfold C; fun_prop (disch := positivity)
  have hG : DifferentiableAt ℝ G 0 := by unfold G; fun_prop (disch := positivity)
  have hC0 : C 0 = 0 := by
    dsimp only [C, Q, negativeParameterCompanion]
    simp only [sub_zero]
    field_simp [hpz, hp.ne, hz.ne']
    ring
  have hGval (y : ℝ) (hy : 0 ≤ y) (hyz : y < z) :
      (G y : ℂ) = 3 * (B y : ℂ) * symmetricEllipticRC z (Q y) := by
    have hQy := negativeParameterCompanion_pos hz hp hy
    have hQyz := negativeParameterCompanion_lt hz hp hyz
    rw [(symmetricEllipticRC_of_gt hQy hQyz).2]
    dsimp only [G]
    push_cast
    ring
  have hG0 : (p : ℂ) * (G 0 : ℂ) + 3 * symmetricEllipticRC z p = 0 := by
    rw [hGval 0 le_rfl hz, symmetricEllipticRC_negativeParameterCompanion hz hp]
    have hc : p * (3 * B 0) + 3 * (z / (z - p)) = 0 := by
      dsimp only [B, Q, negativeParameterCompanion]
      simp only [sub_zero]
      field_simp [hpz, hzp, hp.ne, hz.ne']
      ring
    have hcC := congrArg (fun v : ℝ => (v : ℂ)) hc
    push_cast at hcC
    change (p : ℂ) * (3 * (B 0 : ℂ) * symmetricEllipticRC z (Q 0)) +
      3 * (((z / (z - p) : ℝ) : ℂ) * symmetricEllipticRC z (Q 0)) = 0
    push_cast
    linear_combination symmetricEllipticRC z (Q 0) * hcC
  have hCY : C =O[𝓝[>] 0] (fun y : ℝ => y) := by
    have H := hC.isBigO_sub.mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [hC0, sub_zero] using H
  have hCYc : (fun y : ℝ => (C y : ℂ)) =O[𝓝[>] 0] (fun y : ℝ => (y : ℂ)) :=
    Complex.isBigO_ofReal_left.mpr (Complex.isBigO_ofReal_right.mpr hCY)
  have H1 : (fun y : ℝ => (C y : ℂ) * symmetricEllipticRF 0 y z) =O[𝓝[>] 0]
      (fun y : ℝ => ((y * Real.log y : ℝ) : ℂ)) := by
    simpa only [← ofReal_mul] using hCYc.mul (symmetricEllipticRF_zero_isBigO_log hz)
  have hGY : (fun y : ℝ => (G y : ℂ) - (G 0 : ℂ)) =O[𝓝[>] 0]
      (fun y : ℝ => (y : ℂ)) := by
    have H : (fun y : ℝ => G y - G 0) =O[𝓝[>] 0] (fun y : ℝ => y) := by
      simpa only [sub_zero] using hG.isBigO_sub.mono
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [ofReal_sub] using Complex.isBigO_ofReal_left.mpr
      (Complex.isBigO_ofReal_right.mpr H)
  have hYlog : (fun y : ℝ => (y : ℂ)) =O[𝓝[>] 0]
      (fun y : ℝ => ((y * Real.log y : ℝ) : ℂ)) :=
    Complex.isBigO_ofReal_left.mpr
      (Complex.isBigO_ofReal_right.mpr Real.isBigO_id_mul_log_nhdsGT_zero)
  have H2 := (hGY.trans hYlog).const_mul_left (p : ℂ)
  have hB1 : (fun y : ℝ => (B y : ℂ)) =O[𝓝[>] 0] (fun _ => (1 : ℂ)) :=
    Complex.isBigO_ofReal_left.mpr
      ((hB.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).isBigO_one ℂ)
  have hR := regularizedThirdKind_zero_isBigO_of_tendsto hz hQ0
    (hQ.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  have H3 : (fun y : ℝ => (p : ℂ) * ((B y : ℂ) * regularizedThirdKind 0 y z (Q y)))
      =O[𝓝[>] 0] (fun y : ℝ => ((y * Real.log y : ℝ) : ℂ)) := by
    simpa only [one_mul] using (hB1.mul hR).const_mul_left (p : ℂ)
  have H := (H1.add H2).sub H3
  apply H.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hz)] with y hy hyz
  have hy0 : 0 < y := hy
  have hQy : 0 < Q y := negativeParameterCompanion_pos hz hp hy0.le
  have hAc : (p : ℂ) - z ≠ 0 := by exact_mod_cast hpz
  have hQc : (Q y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hQy.ne'
  have hparam := negativeParameterCompanion_change hz hp hy0
  have hsolve : (p : ℂ) * symmetricEllipticRJ 0 y z p =
      ((3 * p / (p - z) : ℝ) : ℂ) * symmetricEllipticRF 0 y z -
        ((p * (Q y - z) / (p - z) : ℝ) : ℂ) * symmetricEllipticRJ 0 y z (Q y) := by
    change ((p - z : ℝ) : ℂ) * symmetricEllipticRJ 0 y z p +
      ((Q y - z : ℝ) : ℂ) * symmetricEllipticRJ 0 y z (Q y) =
        3 * symmetricEllipticRF 0 y z at hparam
    push_cast at hparam ⊢
    field_simp [hAc]
    linear_combination (p : ℂ) * hparam
  have hGdiff : (p : ℂ) * ((G y : ℂ) - (G 0 : ℂ)) =
      (p : ℂ) * (G y : ℂ) + 3 * symmetricEllipticRC z p := by
    linear_combination -hG0
  rw [hGdiff, hGval y hy0.le hyz]
  dsimp only [regularizedThirdKind, C, B]
  simp only [ofReal_zero]
  rw [hsolve]
  push_cast
  field_simp [hAc, hQc]
  ring


/-- The regularized single-zero-node remainder for every nonzero real parameter. -/
theorem regularizedThirdKind_zero_isBigO {z p : ℝ} (hz : 0 < z) (hp : p ≠ 0) :
    (fun y : ℝ => regularizedThirdKind 0 y z p) =O[𝓝[>] 0]
      (fun y : ℝ => ((y * Real.log y : ℝ) : ℂ)) := by
  rcases lt_or_gt_of_ne hp with hp | hp
  · exact regularizedThirdKind_zero_isBigO_of_neg hz hp
  · exact regularizedThirdKind_zero_isBigO_of_tendsto hz hp tendsto_const_nhds

end SymmetricThirdKindEndpoint
/-- DLMF 19.27.13: `R_J(x, y, z, p) = (3/(2√z p))(ln(8z/(a + g)) - 2 R_C(1, p/z)
+ O((a/z + a/p) ln(p/a)))` as `max(x, y)/min(z, p) → 0`: for fixed `z, p > 0`, as
`(x, y) → 0` through nonnegative pairs not both zero. -/
@[dlmf 19.27.E13]
theorem symmetricEllipticRJ_asymp_small_xy {z p : ℝ} (hz : 0 < z) (hp : 0 < p) :
    (fun q : ℝ × ℝ => symmetricEllipticRJ q.1 q.2 z p -
        ((3 / (2 * √z * p) : ℝ) : ℂ) *
          (((Real.log (8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2)) : ℝ) : ℂ) -
            2 * symmetricEllipticRC 1 (p / z : ℝ))) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((3 / (2 * √z * p) * ((ellAsymA q.1 q.2 / z + ellAsymA q.1 q.2 / p) *
        Real.log (p / ellAsymA q.1 q.2)) : ℝ) : ℂ)) := by
  have hRF := SymmetricThirdKindEndpoint.symmetricEllipticRF_sub_logarithmicTerm_isBigO hz hp
  have hRJ := SymmetricThirdKindEndpoint.regularizedThirdKind_isBigO hz hp
  let D : ℝ := 3 / (2 * √z * p) * (1 / z + 1 / p)
  have hD : 0 < D := by dsimp only [D]; positivity
  have H := (hRJ.const_mul_left (1 / (p : ℂ))).add
    (hRF.const_mul_left (3 / (p : ℂ)))
  have H' := Asymptotics.IsBigO.const_mul_right (ofReal_ne_zero.mpr hD.ne') H
  have hscale : symmetricEllipticRC z p = (√z : ℂ)⁻¹ * symmetricEllipticRC 1 (p / z : ℝ) := by
    have H := symmetricEllipticRC_mul_ofReal_pos hz (x := 1) (y := p / z)
      (by norm_num) (div_pos hp hz)
    have he : z * (p / z) = p := by field_simp
    simpa only [mul_one, he, ofReal_one] using H
  apply H'.congr
  · intro q
    dsimp only [SymmetricThirdKindEndpoint.regularizedThirdKind]
    rw [SymmetricLogarithmicEndpoint.logarithmicTerm_comparisonParameter, hscale]
    push_cast
    field_simp [ofReal_ne_zero.mpr hp.ne',
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hz).ne']
    ring
  · intro q
    dsimp only [D]
    push_cast
    ring

/-- DLMF 19.20.11: `R_J(0, y, z, p) = 3/(2p√z) ln(16z/y) - (3/p) R_C(z, p) + O(y ln y)` as
`y → 0+`, for real `p ≠ 0` and `z > 0`. -/
@[dlmf 19.20.E11]
theorem symmetricEllipticRJ_zero_asymptotic {z p : ℝ} (hz : 0 < z) (hp : p ≠ 0) :
    (fun y : ℝ => symmetricEllipticRJ 0 y z p -
        ((3 / (2 * p * Real.sqrt z) * Real.log (16 * z / y) : ℝ) -
        3 / (p : ℂ) * symmetricEllipticRC z p)) =O[𝓝[>] 0] fun y => ((y * Real.log y : ℝ) : ℂ) := by
  have hRJ := SymmetricThirdKindEndpoint.regularizedThirdKind_zero_isBigO hz hp
  have hRF := SymmetricThirdKindEndpoint.symmetricEllipticRF_zero_sub_log_isBigO hz
  have H := (hRJ.const_mul_left (1 / (p : ℂ))).add (hRF.const_mul_left (3 / (p : ℂ)))
  apply H.congr_left
  intro y
  dsimp only [SymmetricThirdKindEndpoint.regularizedThirdKind]
  simp only [ofReal_zero]
  push_cast
  field_simp [ofReal_ne_zero.mpr hp, ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hz).ne']
  ring

/-- DLMF 19.27.7: `R_D(x, y, z) = (3/(2z^{3/2}))(ln(8z/(a + g)) - 2)(1 + O(a/z))` as
`a/z → 0`: for fixed `z > 0`, as `(x, y) → 0` through nonnegative pairs not both zero. -/
@[dlmf 19.27.E7]
theorem symmetricEllipticRD_asymp_large_z {z : ℝ} (hz : 0 < z) :
    (fun q : ℝ × ℝ => symmetricEllipticRD q.1 q.2 z - ((3 / (2 * z ^ (3 / 2 : ℝ)) *
        (Real.log (8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2)) - 2) : ℝ) : ℂ))
      =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((ellAsymA q.1 q.2 / z * (3 / (2 * z ^ (3 / 2 : ℝ)) *
        (Real.log (8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2)) - 2)) : ℝ) : ℂ)) := by
  have hpower : z ^ (3 / 2 : ℝ) = z * √z := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hz,
      Real.rpow_one, Real.sqrt_eq_rpow]
  have hRC : symmetricEllipticRC 1 1 = 1 := by
    simpa using symmetricEllipticRC_special.1 1 one_mem_slitPlane
  have hloglim : Tendsto (fun q : ℝ × ℝ => Real.log (z / ellAsymA q.1 q.2))
      (𝓝[ellAsymPair] 0) atTop := by
    have HI : Tendsto (fun a : ℝ => a⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
    simpa only [Function.comp_def, div_eq_mul_inv] using Real.tendsto_log_atTop.comp
      ((HI.const_mul_atTop hz).comp SymmetricThirdKindEndpoint.tendsto_arithmeticMean_zero_pos)
  have hcompare : (fun q : ℝ × ℝ => ((3 / (2 * √z * z) *
      ((ellAsymA q.1 q.2 / z + ellAsymA q.1 q.2 / z) *
        Real.log (z / ellAsymA q.1 q.2)) : ℝ) : ℂ)) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((ellAsymA q.1 q.2 / z * (3 / (2 * z ^ (3 / 2 : ℝ)) *
        (Real.log (8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2)) - 2)) : ℝ) : ℂ)) := by
    refine isBigO_iff.mpr ⟨4, ?_⟩
    filter_upwards [self_mem_nhdsWithin, hloglim.eventually (eventually_ge_atTop 4)] with q hq h4
    have ha := SymmetricLogarithmicEndpoint.arithmeticMean_pos_of_mem hq
    have hg : 0 ≤ ellAsymG q.1 q.2 := Real.sqrt_nonneg _
    have hga : ellAsymG q.1 q.2 ≤ ellAsymA q.1 q.2 := by
      have H := (SymmetricLogarithmicEndpoint.comparisonParameter_bounds hq.1 hq.2.1).2
      dsimp only [SymmetricLogarithmicEndpoint.comparisonParameter] at H
      linarith
    have has : 0 < ellAsymA q.1 q.2 + ellAsymG q.1 q.2 := by linarith
    have hratio : z / ellAsymA q.1 q.2 ≤
        8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2) := by
      apply (div_le_div_iff₀ ha has).mpr
      nlinarith [mul_le_mul_of_nonneg_left hga hz.le, mul_pos hz ha]
    have hL := Real.log_le_log (div_pos hz ha) hratio
    have hrem : 0 ≤ Real.log (8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2)) - 2 := by
      linarith
    have hdom : Real.log (z / ellAsymA q.1 q.2) ≤
        2 * (Real.log (8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2)) - 2) := by linarith
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ = 2 * (ellAsymA q.1 q.2 / z * (3 / (2 * z ^ (3 / 2 : ℝ)))) *
          Real.log (z / ellAsymA q.1 q.2) := by rw [hpower]; ring
      _ ≤ 2 * (ellAsymA q.1 q.2 / z * (3 / (2 * z ^ (3 / 2 : ℝ)))) *
          (2 * (Real.log (8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2)) - 2)) :=
        mul_le_mul_of_nonneg_left hdom (by positivity)
      _ = _ := by ring
  have H := (symmetricEllipticRJ_asymp_small_xy hz hz).trans hcompare
  apply H.congr
  · intro q
    rw [div_self hz.ne', ofReal_one, hRC]
    dsimp only [symmetricEllipticRD]
    rw [hpower]
    push_cast
    ring
  · intro q
    rfl

end DLMF.EllipticIntegrals
