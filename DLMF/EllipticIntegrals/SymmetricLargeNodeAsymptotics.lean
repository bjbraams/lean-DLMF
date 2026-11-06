/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.SymmetricSecondKindAsymptotics
public import DLMFMathlib.Analysis.Integral.QuadraticSquareRootSubstitution

/-!
# Large-first-node asymptotics of the third symmetric elliptic integral

The pair-root change of variables gives the exact `R_C` leading term. Subtracting the
constant first-node weight bounds the remainder by a multiple of `R_F`, uniformly in the
positive third-kind parameter.

## Main results

* `symmetricEllipticRJ_asymp_large_x`: the quadratic-tail approximation, DLMF 19.27.16.
* `symmetricEllipticRD_asymp_large_x`: its repeated-node specialization, DLMF 19.27.9.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory Asymptotics
open scoped Real Topology

namespace DLMF.EllipticIntegrals
namespace SymmetricLargeNodeEndpoint

/-- The pair-root integral is an elementary quadratic tail of `R_C`. -/
theorem symmetricEllipticRC_eq_pair_root_integral {y z p : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hp : 0 < p) (ha : 0 < ellAsymB y z) :
    IntegrableOn (fun t : ℝ => 1 / (√(t + y) * √(t + z) * (t + p))) (Ioi 0) ∧
      symmetricEllipticRC ((ellAsymH y z + p) ^ 2 : ℝ)
          (2 * (ellAsymB y z + ellAsymH y z) * p : ℝ) =
        (1 / 2 : ℂ) * ((∫ t in Ioi (0 : ℝ),
          1 / (√(t + y) * √(t + z) * (t + p)) : ℝ) : ℂ) := by
  let h : ℝ := ellAsymH y z
  let b : ℝ := ellAsymB y z
  let X : ℝ := (h + p) ^ 2
  let Y : ℝ := 2 * (b + h) * p
  let φ : ℝ → ℝ := QuadraticSquareRoot.substitution y z p
  let G : ℝ → ℂ := fun u => ((u ^ 2 + Y - X : ℝ) : ℂ)⁻¹
  have hb : 0 < b := ha
  have hh : 0 ≤ h := Real.sqrt_nonneg _
  have hY : 0 < Y := by dsimp only [Y]; positivity
  have hRC := symmetricEllipticRC_eq_integral_quadratic_tail (x := X) (by positivity) hY
  have hrootX : √X = h + p := by dsimp only [X]; rw [Real.sqrt_sq (by positivity)]
  rw [hrootX] at hRC
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt φ (QuadraticSquareRoot.jacobian y z t)
      (Ioi 0) t := fun t ht =>
    (QuadraticSquareRoot.hasDerivAt_substitution hy hz ht).hasDerivWithinAt
  have hm : MonotoneOn φ (Ioi 0) := QuadraticSquareRoot.monotoneOn_substitution hy hz
  have himage : φ '' Ioi 0 = Ioi (h + p) := QuadraticSquareRoot.image_substitution_Ioi hy hz
  have heq (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      QuadraticSquareRoot.jacobian y z t • G (φ t) =
        (1 / 2 : ℂ) * ((1 / (√(t + y) * √(t + z) * (t + p)) : ℝ) : ℂ) := by
    have ht0 : 0 < t := ht
    have hty : 0 < t + y := add_pos_of_pos_of_nonneg ht0 hy
    have htp : 0 < t + p := add_pos ht0 hp
    have H := QuadraticSquareRoot.jacobian_div_quadratic hy hz ht0 htp.ne'
    rw [Real.sqrt_mul hty.le] at H
    have HC := congrArg (fun v : ℝ => (v : ℂ)) H
    dsimp only [G, φ, X, Y, h, b, ellAsymH, ellAsymB]
    simp only [Complex.real_smul]
    push_cast at HC ⊢
    simp only [div_eq_mul_inv, mul_inv] at HC ⊢
    linear_combination HC
  have htrans := integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioi hd hm G
  rw [himage, setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
    integral_complex_ofReal] at htrans
  have hi := (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
    measurableSet_Ioi hd hm G).mp (by simpa only [himage] using hRC.1)
  have hiHalf : IntegrableOn (fun t : ℝ => (1 / 2 : ℂ) *
      ((1 / (√(t + y) * √(t + z) * (t + p)) : ℝ) : ℂ)) (Ioi 0) :=
    hi.congr_fun heq measurableSet_Ioi
  have hiPair := hiHalf.const_mul (2 : ℂ)
  simp only [← mul_assoc, show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_mul] at hiPair
  have hiReal : IntegrableOn (fun t : ℝ =>
      (((1 / (√(t + y) * √(t + z) * (t + p)) : ℝ) : ℂ)).re) (Ioi 0) := hiPair.re
  refine ⟨hiReal.congr_fun (fun t _ => Complex.ofReal_re _) measurableSet_Ioi, ?_⟩
  exact hRC.2.trans htrans

/-- The real square-root kernels agree with their complex principal-branch forms. -/
theorem root_product_inv_eq_ofReal {x y z t : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 < t) :
    (carlsonRootProduct x y z t)⁻¹ =
      ((1 / (√(t + x) * √(t + y) * √(t + z)) : ℝ) : ℂ) := by
  simp only [carlsonRootProduct, ← ofReal_add]
  rw [Carlson.ofReal_cpow_half (by linarith : 0 ≤ t + x),
    Carlson.ofReal_cpow_half (by linarith : 0 ≤ t + y),
    Carlson.ofReal_cpow_half (by linarith : 0 ≤ t + z)]
  simp only [one_div]
  push_cast
  rfl

/-- Real integral representations on the nonnegative two-node domain. -/
theorem real_kernel_representations {x y z p : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ha : 0 < ellAsymB y z) (hp : 0 < p) :
    IntegrableOn (fun t : ℝ => 1 / (√(t + x) * √(t + y) * √(t + z))) (Ioi 0) ∧
    IntegrableOn (fun t : ℝ => 1 / (√(t + x) * √(t + y) * √(t + z) * (t + p)))
      (Ioi 0) ∧
    symmetricEllipticRF x y z = (1 / 2 : ℂ) * ((∫ t in Ioi (0 : ℝ),
      1 / (√(t + x) * √(t + y) * √(t + z)) : ℝ) : ℂ) ∧
    symmetricEllipticRJ x y z p = (3 / 2 : ℂ) * ((∫ t in Ioi (0 : ℝ),
      1 / (√(t + x) * √(t + y) * √(t + z) * (t + p)) : ℝ) : ℂ) := by
  have hyz : y = 0 → z ≠ 0 := by
    intro h h'; dsimp only [ellAsymB] at ha; rw [h, h'] at ha; norm_num at ha
  obtain ⟨hF, hJ⟩ := integrableOn_carlsonRootProduct_inv_of_nonneg hx hy hz hyz hp
  have heF (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) := root_product_inv_eq_ofReal hx hy hz ht
  have heJ (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹ =
        ((1 / (√(t + x) * √(t + y) * √(t + z) * (t + p)) : ℝ) : ℂ) := by
    rw [mul_inv, heF t ht]
    simp only [one_div, mul_inv]
    push_cast
    rfl
  have hiF : IntegrableOn (fun t : ℝ =>
      ((1 / (√(t + x) * √(t + y) * √(t + z)) : ℝ) : ℂ)) (Ioi 0) :=
    hF.congr_fun heF measurableSet_Ioi
  have hiJ : IntegrableOn (fun t : ℝ =>
      ((1 / (√(t + x) * √(t + y) * √(t + z) * (t + p)) : ℝ) : ℂ)) (Ioi 0) :=
    hJ.congr_fun heJ measurableSet_Ioi
  have hiFr : IntegrableOn (fun t : ℝ =>
      (((1 / (√(t + x) * √(t + y) * √(t + z)) : ℝ) : ℂ)).re) (Ioi 0) := hiF.re
  have hiJr : IntegrableOn (fun t : ℝ =>
      (((1 / (√(t + x) * √(t + y) * √(t + z) * (t + p)) : ℝ) : ℂ)).re) (Ioi 0) := hiJ.re
  refine ⟨hiFr.congr_fun (fun t _ => ofReal_re _) measurableSet_Ioi,
    hiJr.congr_fun (fun t _ => ofReal_re _) measurableSet_Ioi, ?_, ?_⟩
  · simp only [symmetricEllipticRF]
    rw [setIntegral_congr_fun measurableSet_Ioi heF, integral_complex_ofReal]
  · simp only [symmetricEllipticRJ,
      not_isNegReal_of_mem_slitPlane (ofReal_mem_slitPlane.mpr hp), ↓reduceIte]
    rw [setIntegral_congr_fun measurableSet_Ioi heJ, integral_complex_ofReal]

/-- The exact quadratic-tail approximation has a first-kind remainder bound uniform in `p`. -/
theorem norm_symmetricEllipticRJ_sub_quadratic_tail_le {x y z p : ℝ}
    (hx : 0 < x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hp : 0 < p) (ha : 0 < ellAsymB y z) :
    ‖symmetricEllipticRJ x y z p - 3 / (√x : ℝ) *
      symmetricEllipticRC ((ellAsymH y z + p) ^ 2 : ℝ)
        (2 * (ellAsymB y z + ellAsymH y z) * p : ℝ)‖ ≤
      (3 / x) * ‖symmetricEllipticRF x y z‖ := by
  obtain ⟨hF, hJ, hRF, hRJ⟩ := real_kernel_representations hx hy hz ha hp
  obtain ⟨hW, hRC⟩ := symmetricEllipticRC_eq_pair_root_integral hy hz hp ha
  let f : ℝ → ℝ := fun t => 1 / (√(t + x) * √(t + y) * √(t + z))
  let j : ℝ → ℝ := fun t => 1 / (√(t + x) * √(t + y) * √(t + z) * (t + p))
  let w : ℝ → ℝ := fun t => 1 / (√(t + y) * √(t + z) * (t + p))
  have hbound (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      0 ≤ w t / √x - j t ∧ w t / √x - j t ≤ (1 / x) * f t := by
    have ht0 : 0 < t := ht
    have hu : 0 < √x := Real.sqrt_pos.mpr hx
    have hv : 0 < √(t + x) := Real.sqrt_pos.mpr (by linarith)
    have hy' : 0 < √(t + y) := Real.sqrt_pos.mpr (by linarith)
    have hz' : 0 < √(t + z) := Real.sqrt_pos.mpr (by linarith)
    have hp' : 0 < t + p := by linarith
    have hle : √x ≤ √(t + x) := Real.sqrt_le_sqrt (by linarith)
    dsimp only [w, j, f]
    constructor
    · apply sub_nonneg.mpr
      rw [div_div]
      apply one_div_le_one_div_of_le (by positivity)
      calc _ = √x * (√(t + y) * √(t + z) * (t + p)) := by ring
        _ ≤ √(t + x) * (√(t + y) * √(t + z) * (t + p)) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
        _ = _ := by ring
    · apply (sub_le_iff_le_add).mpr
      field_simp
      nlinarith [Real.sq_sqrt hx.le, Real.sq_sqrt (show 0 ≤ t + x by linarith),
        mul_nonneg (sub_nonneg.mpr hle) (show 0 ≤ √x * √(t + x) by positivity)]
  have he : symmetricEllipticRJ x y z p - 3 / (√x : ℝ) *
      symmetricEllipticRC ((ellAsymH y z + p) ^ 2 : ℝ)
        (2 * (ellAsymB y z + ellAsymH y z) * p : ℝ) =
      -(3 / 2 : ℂ) * ((∫ t in Ioi (0 : ℝ), w t / √x - j t : ℝ) : ℂ) := by
    rw [hRJ, hRC, integral_sub (hW.div_const _) hJ, integral_div]
    push_cast
    ring
  have hnonneg : 0 ≤ ∫ t in Ioi (0 : ℝ), w t / √x - j t :=
    setIntegral_nonneg measurableSet_Ioi (fun t ht => (hbound t ht).1)
  have hupper : (∫ t in Ioi (0 : ℝ), w t / √x - j t) ≤
      (1 / x) * ∫ t in Ioi (0 : ℝ), f t := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on ((hW.div_const _).sub hJ) (hF.const_mul _)
      measurableSet_Ioi (fun t ht => (hbound t ht).2)
  have hFpos : 0 ≤ ∫ t in Ioi (0 : ℝ), f t :=
    setIntegral_nonneg measurableSet_Ioi (fun t ht => by dsimp only [f]; positivity)
  rw [he, norm_mul, norm_neg, show ‖(3 / 2 : ℂ)‖ = (3 / 2 : ℝ) by norm_num [norm_div],
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg, hRF, norm_mul,
    show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num [norm_div],
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hFpos]
  change (3 / 2 : ℝ) * _ ≤ (3 / x) * ((1 / 2) * _)
  calc _ ≤ (3 / 2 : ℝ) * ((1 / x) * ∫ t in Ioi (0 : ℝ), f t) :=
      mul_le_mul_of_nonneg_left hupper (by norm_num)
    _ = _ := by ring

open SymmetricLogarithmicEndpoint

/-- Forgetting the third-kind parameter preserves the punctured quadrant approach. -/
theorem tendsto_pair_of_triple :
    Tendsto (fun q : ℝ × ℝ × ℝ => (q.1, q.2.1))
      (𝓝[{q | 0 ≤ q.1 ∧ 0 ≤ q.2.1 ∧ (q.1, q.2.1) ≠ 0 ∧ 0 < q.2.2}] 0)
      (𝓝[ellAsymPair] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have H : Continuous (fun q : ℝ × ℝ × ℝ => (q.1, q.2.1)) := by fun_prop
    exact (H.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact ⟨hq.1, hq.2.1, hq.2.2.1⟩

/-- Adding the geometric mean does not change the logarithmic endpoint scale. -/
theorem log_mean_isBigO_log_mean_add_geom {x : ℝ} (hx : 0 < x) :
    (fun q : ℝ × ℝ => (Real.log (x / ellAsymB q.1 q.2) : ℂ)) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => (Real.log (x / (ellAsymB q.1 q.2 + ellAsymH q.1 q.2)) : ℂ)) := by
  refine isBigO_iff.mpr ⟨2, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    tendsto_arithmeticMean_zero.eventually (eventually_lt_nhds (by linarith : 0 < x / 4))]
    with q hq hsmall
  let b := ellAsymB q.1 q.2
  let h := ellAsymH q.1 q.2
  have hb : 0 < b := arithmeticMean_pos_of_mem hq
  have hh : 0 ≤ h := Real.sqrt_nonneg _
  have hhb : h ≤ b := by
    have H := (comparisonParameter_bounds hq.1 hq.2.1).2
    dsimp only [comparisonParameter, ellAsymA, ellAsymG] at H
    dsimp only [h, b, ellAsymB, ellAsymH]
    linarith
  change b < x / 4 at hsmall
  have hbh : 0 < b + h := by positivity
  have hratio : x / b ≤ (x / (b + h)) ^ 2 := by
    have H : (b + h) ^ 2 ≤ x * b := by
      calc _ ≤ (2 * b) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
        _ ≤ x * b := by nlinarith
    rw [div_pow]
    apply (div_le_div_iff₀ hb (sq_pos_of_pos hbh)).mpr
    nlinarith [mul_le_mul_of_nonneg_left H hx.le]
  have hlog := Real.log_le_log (div_pos hx hb) hratio
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hlog0 : 0 ≤ Real.log (x / b) := Real.log_nonneg ((le_div_iff₀ hb).mpr (by linarith))
  have hlog1 : 0 ≤ Real.log (x / (b + h)) :=
    Real.log_nonneg ((le_div_iff₀ hbh).mpr (by linarith))
  change ‖(Real.log (x / b) : ℂ)‖ ≤ 2 * ‖(Real.log (x / (b + h)) : ℂ)‖
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0,
    abs_of_nonneg hlog1] using hlog

/-- The uniform third-kind remainder has logarithmic arithmetic-mean order. -/
theorem symmetricEllipticRJ_remainder_isBigO_log_mean {x : ℝ} (hx : 0 < x) :
    (fun q : ℝ × ℝ × ℝ => symmetricEllipticRJ x q.1 q.2.1 q.2.2 -
        3 / (√x : ℝ) * symmetricEllipticRC ((ellAsymH q.1 q.2.1 + q.2.2) ^ 2 : ℝ)
          (2 * (ellAsymB q.1 q.2.1 + ellAsymH q.1 q.2.1) * q.2.2 : ℝ))
      =O[𝓝[{q | 0 ≤ q.1 ∧ 0 ≤ q.2.1 ∧ (q.1, q.2.1) ≠ 0 ∧ 0 < q.2.2}] 0]
      (fun q : ℝ × ℝ × ℝ => (Real.log (x / ellAsymB q.1 q.2.1) : ℂ)) := by
  have H := (SymmetricSecondKindEndpoint.symmetricEllipticRF_isBigO_log hx).comp_tendsto
    tendsto_pair_of_triple
  obtain ⟨C, hC⟩ := isBigO_iff.mp H
  refine isBigO_iff.mpr ⟨(3 / x) * C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with q hq hdom
  have ha : 0 < ellAsymB q.1 q.2.1 :=
    arithmeticMean_pos_of_mem ⟨hdom.1, hdom.2.1, hdom.2.2.1⟩
  calc _ ≤ (3 / x) * ‖symmetricEllipticRF x q.1 q.2.1‖ :=
      norm_symmetricEllipticRJ_sub_quadratic_tail_le hx hdom.1 hdom.2.1 hdom.2.2.2 ha
    _ = (3 / x) * ‖symmetricEllipticRF q.1 q.2.1 x‖ := by
      rw [← symmetricEllipticRF_comm_left (x : ℂ) (q.1 : ℂ) (q.2.1 : ℂ),
        ← symmetricEllipticRF_comm_right (q.1 : ℂ) (x : ℂ) (q.2.1 : ℂ)]
    _ ≤ (3 / x) * (C * ‖(Real.log (x / ellAsymB q.1 q.2.1) : ℂ)‖) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by ring

/-- Setting the third-kind parameter to the repeated node makes the quadratic tail elementary. -/
theorem quadratic_tail_repeated_node {x y z : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hz : 0 < z) :
    3 / (√x : ℝ) * symmetricEllipticRC ((ellAsymH y z + z) ^ 2 : ℝ)
        (2 * (ellAsymB y z + ellAsymH y z) * z : ℝ) =
      ((3 / (√(x * z) * (√y + √z)) : ℝ) : ℂ) := by
  have hh : 0 ≤ ellAsymH y z := Real.sqrt_nonneg _
  have hsum : 0 < ellAsymH y z + z := by positivity
  have hargs : 2 * (ellAsymB y z + ellAsymH y z) * z = (ellAsymH y z + z) ^ 2 := by
    dsimp only [ellAsymB, ellAsymH]
    nlinarith [Real.sq_sqrt (mul_nonneg hy hz.le)]
  have hRC := symmetricEllipticRC_special.1 ((ellAsymH y z + z) ^ 2 : ℝ)
    (ofReal_mem_slitPlane.mpr (sq_pos_of_pos hsum))
  rw [cpow_neg, Carlson.ofReal_cpow_half (sq_nonneg _), Real.sqrt_sq hsum.le] at hRC
  have hden : √(x * z) * (√y + √z) = √x * (ellAsymH y z + z) := by
    rw [Real.sqrt_mul hx.le]
    dsimp only [ellAsymH]
    rw [Real.sqrt_mul hy]
    calc _ = √x * (√y * √z + (√z) ^ 2) := by ring
      _ = _ := by rw [Real.sq_sqrt hz.le]
  rw [hargs, hRC, hden]
  push_cast
  field_simp [ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne',
    ofReal_ne_zero.mpr hsum.ne']

/-- The relative second-kind error scale dominates the logarithmic absolute error scale. -/
theorem repeated_node_error_scale_le {x y z : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hz : 0 < z) :
    (1 / (x * √x)) ≤
      3 / (√(x * z) * (√y + √z)) * (ellAsymB y z / x) := by
  have hu : 0 < √x := Real.sqrt_pos.mpr hx
  have hv : 0 < √z := Real.sqrt_pos.mpr hz
  have hw : 0 ≤ √y := Real.sqrt_nonneg _
  have hmean : √y * √z ≤ ellAsymB y z := by
    dsimp only [ellAsymB]
    nlinarith [sq_nonneg (√y - √z), Real.sq_sqrt hy, Real.sq_sqrt hz.le]
  have hden : √z * (√y + √z) ≤ 3 * ellAsymB y z := by
    dsimp only [ellAsymB] at hmean ⊢
    nlinarith [Real.sq_sqrt hz.le]
  rw [Real.sqrt_mul hx.le]
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (by positivity : 0 < x * √x)
    (by positivity : 0 < √x * √z * (√y + √z) * x)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hden (mul_pos hx hu).le]

end SymmetricLargeNodeEndpoint

open SymmetricLargeNodeEndpoint SymmetricLogarithmicEndpoint

/-- DLMF 19.27.9: `R_D(x, y, z) = 3/(√(xz)(√y + √z)) (1 + O((b/x) ln(x/b)))` as `b/x → 0`: for
fixed `x > 0`, as `(y, z) → 0` with `y ≥ 0`, `z > 0`. -/
@[dlmf 19.27.E9]
theorem symmetricEllipticRD_asymp_large_x {x : ℝ} (hx : 0 < x) :
    (fun q : ℝ × ℝ => symmetricEllipticRD x q.1 q.2 -
        ((3 / (√(x * q.2) * (√q.1 + √q.2)) : ℝ) : ℂ)) =O[𝓝[{q | 0 ≤ q.1 ∧ 0 < q.2}] 0]
      (fun q : ℝ × ℝ => ((3 / (√(x * q.2) * (√q.1 + √q.2)) *
        (ellAsymB q.1 q.2 / x * Real.log (x / ellAsymB q.1 q.2)) : ℝ) : ℂ)) := by
  have ht : Tendsto (fun q : ℝ × ℝ => q) (𝓝[{q | 0 ≤ q.1 ∧ 0 < q.2}] 0)
      (𝓝[ellAsymPair] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_id.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with q hq
    refine ⟨hq.1, hq.2.le, ?_⟩
    intro heq
    exact hq.2.ne' (congrArg Prod.snd heq)
  have H := (SymmetricSecondKindEndpoint.symmetricEllipticRF_isBigO_log hx).comp_tendsto ht
  obtain ⟨C, hCpos, hC⟩ := isBigO_iff'.mp H
  refine isBigO_iff.mpr ⟨3 * √x * C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin,
    (tendsto_arithmeticMean_zero.comp ht).eventually (eventually_lt_nhds hx)]
    with q hq hdom hsmall
  have hy := hdom.1
  have hz := hdom.2
  have hb : 0 < ellAsymB q.1 q.2 := by dsimp only [ellAsymB]; positivity
  change ellAsymB q.1 q.2 < x at hsmall
  have hu : 0 < √x := Real.sqrt_pos.mpr hx
  have hlog : 0 ≤ Real.log (x / ellAsymB q.1 q.2) :=
    Real.log_nonneg ((le_div_iff₀ hb).mpr (by linarith))
  have hE := norm_symmetricEllipticRJ_sub_quadratic_tail_le hx hdom.1 hdom.2.le hdom.2 hb
  rw [quadratic_tail_repeated_node hx hdom.1 hdom.2] at hE
  change ‖symmetricEllipticRD x q.1 q.2 -
      ((3 / (√(x * q.2) * (√q.1 + √q.2)) : ℝ) : ℂ)‖ ≤ _ at hE
  have hperm : symmetricEllipticRF x q.1 q.2 = symmetricEllipticRF q.1 q.2 x := by
    rw [← symmetricEllipticRF_comm_left (x : ℂ) (q.1 : ℂ) (q.2 : ℂ),
      ← symmetricEllipticRF_comm_right (q.1 : ℂ) (x : ℂ) (q.2 : ℂ)]
  rw [hperm] at hE
  have hRF : ‖symmetricEllipticRF q.1 q.2 x‖ ≤
      C * Real.log (x / ellAsymB q.1 q.2) := by
    change ‖symmetricEllipticRF q.1 q.2 x‖ ≤
      C * ‖(Real.log (x / ellAsymB q.1 q.2) : ℂ)‖ at hq
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog] using hq
  have hscale := repeated_node_error_scale_le hx hdom.1 hdom.2
  have href : 0 ≤ 3 / (√(x * q.2) * (√q.1 + √q.2)) *
      (ellAsymB q.1 q.2 / x * Real.log (x / ellAsymB q.1 q.2)) := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg href]
  calc _ ≤ (3 / x) * (C * Real.log (x / ellAsymB q.1 q.2)) :=
      hE.trans (mul_le_mul_of_nonneg_left hRF (by positivity))
    _ = (3 * √x * C) * ((1 / (x * √x)) *
        Real.log (x / ellAsymB q.1 q.2)) := by field_simp
    _ ≤ (3 * √x * C) * ((3 / (√(x * q.2) * (√q.1 + √q.2)) *
        (ellAsymB q.1 q.2 / x)) * Real.log (x / ellAsymB q.1 q.2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hscale hlog) (by positivity)
    _ = _ := by ring

/-- DLMF 19.27.16: `R_J(x, y, z, p) = (3/√x) R_C((h + p)², 2(b + h)p)
+ O(x^{-3/2} ln(x/(b + h)))` as `max(y, z, p)/x → 0`: for fixed `x > 0`, as `(y, z, p) → 0` with
`y, z ≥ 0` not both zero and `p > 0`. -/
@[dlmf 19.27.E16]
theorem symmetricEllipticRJ_asymp_large_x {x : ℝ} (hx : 0 < x) :
    (fun q : ℝ × ℝ × ℝ => symmetricEllipticRJ x q.1 q.2.1 q.2.2 -
        3 / (√x : ℝ) * symmetricEllipticRC ((ellAsymH q.1 q.2.1 + q.2.2) ^ 2 : ℝ)
          (2 * (ellAsymB q.1 q.2.1 + ellAsymH q.1 q.2.1) * q.2.2 : ℝ))
      =O[𝓝[{q | 0 ≤ q.1 ∧ 0 ≤ q.2.1 ∧ (q.1, q.2.1) ≠ 0 ∧ 0 < q.2.2}] 0]
      (fun q : ℝ × ℝ × ℝ => ((x ^ (-(3 / 2) : ℝ) *
        Real.log (x / (ellAsymB q.1 q.2.1 + ellAsymH q.1 q.2.1)) : ℝ) : ℂ)) := by
  simp only [ofReal_mul]
  apply (isBigO_const_mul_right_iff (ofReal_ne_zero.mpr
    (Real.rpow_pos_of_pos hx (-(3 / 2) : ℝ)).ne')).mpr
  have H := SymmetricLargeNodeEndpoint.symmetricEllipticRJ_remainder_isBigO_log_mean hx |>.trans
    ((SymmetricLargeNodeEndpoint.log_mean_isBigO_log_mean_add_geom hx).comp_tendsto
      SymmetricLargeNodeEndpoint.tendsto_pair_of_triple)
  simpa only [ofReal_mul, Function.comp_def] using H

end DLMF.EllipticIntegrals
