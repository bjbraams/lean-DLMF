/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.SymmetricAsymptotics
public import DLMFMathlib.Analysis.Integral.LogarithmicSquareRootKernel
public import Mathlib.Analysis.Complex.Asymptotics

/-!
# Logarithmic asymptotics for the symmetric elliptic integrals

Comparing the two-small-node kernel of `R_F(x,y,z)` with `R_C(z,σ)`, where
`σ=(√x+√y)²/4`, cancels its unweighted logarithmic mass. The remaining outer square-root
weight has a rational majorant, giving the relative error in DLMF 19.27.2.

## Main results

* `symmetricEllipticRF_asymp_large_z`: the two-small-node logarithmic approximation,
  DLMF 19.27.2.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory Asymptotics
open scoped Real Topology

namespace DLMF.EllipticIntegrals
namespace SymmetricLogarithmicEndpoint

/-- The comparison parameter determined by the arithmetic and geometric means. -/
def comparisonParameter (x y : ℝ) : ℝ := (ellAsymA x y + ellAsymG x y) / 2

/-- The comparison parameter is the squared mean of the two square roots. -/
theorem comparisonParameter_eq_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    comparisonParameter x y = (√x + √y) ^ 2 / 4 := by
  dsimp only [comparisonParameter, ellAsymA, ellAsymG]
  rw [Real.sqrt_mul hx]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]

/-- The comparison parameter lies between half the arithmetic mean and that mean. -/
theorem comparisonParameter_bounds {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ellAsymA x y / 2 ≤ comparisonParameter x y ∧ comparisonParameter x y ≤ ellAsymA x y := by
  have hg : 0 ≤ ellAsymG x y := Real.sqrt_nonneg _
  have hga : ellAsymG x y ≤ ellAsymA x y := by
    dsimp only [ellAsymG, ellAsymA]
    nlinarith [Real.sq_sqrt (mul_nonneg hx hy), sq_nonneg (x - y), Real.sqrt_nonneg (x * y)]
  unfold comparisonParameter
  constructor <;> linarith

/-- The comparison parameter is positive whenever the arithmetic mean is positive. -/
theorem comparisonParameter_pos {x y : ℝ} (ha : 0 < ellAsymA x y) :
    0 < comparisonParameter x y := by
  dsimp only [comparisonParameter, ellAsymG]
  linarith [Real.sqrt_nonneg (x * y)]

/-- The comparison parameter is symmetric. -/
theorem comparisonParameter_comm (x y : ℝ) : comparisonParameter x y = comparisonParameter y x := by
  simp only [comparisonParameter, ellAsymA, ellAsymG, add_comm, mul_comm]

/-- The regularized pair-root kernel is integrable on the nonnegative domain. -/
theorem integrableOn_comparison_kernel {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : 0 < ellAsymA x y) :
    IntegrableOn (fun t : ℝ => 1 / (√(t + x) * √(t + y)) -
      1 / (t + comparisonParameter x y)) (Ioi 0) := by
  have hp := comparisonParameter_pos ha
  have hpa := (comparisonParameter_bounds hx hy).2
  rcases hx.eq_or_lt with hx0 | hx0
  · have hy' : 0 < y := by dsimp only [ellAsymA] at ha; linarith
    have hpa' : comparisonParameter x y ≤ (y + x) / 2 := by
      simpa only [ellAsymA, add_comm] using hpa
    have H := LogarithmicSquareRoot.integrableOn_inv_sqrt_product_sub_inv hy' hx hp hpa'
    convert H using 1
    ext t
    rw [mul_comm (√(t + x)) (√(t + y))]
  · exact LogarithmicSquareRoot.integrableOn_inv_sqrt_product_sub_inv hx0 hy hp hpa

/-- The first-kind difference is exactly the weighted pair-root comparison. -/
theorem symmetricEllipticRF_sub_symmetricEllipticRC_eq_integral {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 < ellAsymA x y) (hz : 0 < z) :
    symmetricEllipticRF x y z - symmetricEllipticRC z (comparisonParameter x y) =
      (1 / 2 : ℂ) * ((∫ t in Ioi (0 : ℝ),
        (1 / (√(t + x) * √(t + y)) - 1 / (t + comparisonParameter x y)) /
          √(t + z) : ℝ) : ℂ) := by
  have hp := comparisonParameter_pos ha
  have hF : IntegrableOn (fun t => (carlsonRootProduct x y z t)⁻¹) (Ioi 0) := by
    have H := (integrableOn_carlsonRootProduct_inv_of_nonneg hz hx hy
      (fun h => by dsimp only [ellAsymA] at ha; intro h'; rw [h, h'] at ha; norm_num at ha)
      (p := 1) (by norm_num)).1
    simpa only [carlsonRootProduct, mul_comm, mul_left_comm, mul_assoc] using H
  have hRC := integrableOn_symmetricEllipticRC_integrand
    (Or.inl (ofReal_mem_slitPlane.mpr hz)) (ofReal_mem_slitPlane.mpr hp)
  have he : (∫ t in Ioi (0 : ℝ), (carlsonRootProduct x y z t)⁻¹) -
      (∫ t in Ioi (0 : ℝ), (((t : ℂ) + z) ^ (1 / 2 : ℂ) *
        ((t : ℂ) + comparisonParameter x y))⁻¹) =
      ((∫ t in Ioi (0 : ℝ),
        (1 / (√(t + x) * √(t + y)) - 1 / (t + comparisonParameter x y)) /
          √(t + z) : ℝ) : ℂ) := by
    rw [← integral_sub hF hRC, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have htx : 0 < t + x := add_pos_of_pos_of_nonneg ht hx
    have hty : 0 < t + y := add_pos_of_pos_of_nonneg ht hy
    have htz : 0 < t + z := add_pos ht hz
    simp only [carlsonRootProduct, ← ofReal_add]
    rw [Carlson.ofReal_cpow_half htx.le, Carlson.ofReal_cpow_half hty.le,
      Carlson.ofReal_cpow_half htz.le]
    simp only [ofReal_div, ofReal_sub, ofReal_one, ofReal_mul, ofReal_add]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  simp only [symmetricEllipticRF, symmetricEllipticRC,
    not_isNegReal_of_mem_slitPlane (ofReal_mem_slitPlane.mpr hp), ↓reduceIte]
  linear_combination (1 / 2 : ℂ) * he

/-- Zero comparison mass removes the constant outer square-root weight. -/
theorem symmetricEllipticRF_sub_symmetricEllipticRC_eq_regularized_integral {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 < ellAsymA x y) (haz : ellAsymA x y < z) :
    symmetricEllipticRF x y z - symmetricEllipticRC z (comparisonParameter x y) =
      -(1 / 2 : ℂ) * ((∫ t in Ioi (0 : ℝ),
        (1 / (√(t + x) * √(t + y)) - 1 / (t + comparisonParameter x y)) *
          ((√z)⁻¹ - (√(t + z))⁻¹) : ℝ) : ℂ) := by
  let d : ℝ → ℝ := fun t => 1 / (√(t + x) * √(t + y)) -
    1 / (t + comparisonParameter x y)
  have hi : IntegrableOn d (Ioi 0) := integrableOn_comparison_kernel hx hy ha
  have hD := LogarithmicSquareRoot.integrableOn_pair_kernel_mul_sqrt_shift
    hx hy (comparisonParameter_pos ha).le (comparisonParameter_bounds hx hy).2 ha haz
  have hzero : (∫ t in Ioi (0 : ℝ), d t) = 0 := by
    dsimp only [d]
    rw [comparisonParameter_eq_sq hx hy]
    exact LogarithmicSquareRoot.integral_Ioi_inv_sqrt_product_sub_inv_eq_zero hx hy
  have he : (∫ t in Ioi (0 : ℝ), d t / √(t + z)) =
      -(∫ t in Ioi (0 : ℝ), d t * ((√z)⁻¹ - (√(t + z))⁻¹)) := by
    calc
      _ = (∫ t in Ioi (0 : ℝ), (√z)⁻¹ * d t - d t * ((√z)⁻¹ - (√(t + z))⁻¹)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        ring
      _ = _ := by
        rw [integral_sub (hi.const_mul _) hD, integral_const_mul, hzero]
        ring
  rw [symmetricEllipticRF_sub_symmetricEllipticRC_eq_integral hx hy ha (ha.trans haz), he]
  push_cast
  ring


/-- The logarithmic leading term for a positive outer node and a small comparison parameter. -/
def logarithmicTerm (z s : ℝ) : ℝ := Real.log (4 * z / s) / (2 * √z)

/-- The leading logarithm can be written as a difference of logarithms of square roots. -/
theorem logarithmicTerm_eq {z s : ℝ} (hz : 0 < z) (hs : 0 < s) :
    logarithmicTerm z s = (Real.log (2 * √z) - Real.log (√s)) / √z := by
  have hlog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  dsimp only [logarithmicTerm]
  rw [Real.log_div (by positivity) hs.ne', Real.log_mul (by norm_num) hz.ne',
    Real.log_mul (by norm_num) (Real.sqrt_pos.mpr hz).ne',
    Real.log_sqrt hz.le, Real.log_sqrt hs.le, hlog]
  ring

/-- The elementary logarithmic representation of `R_C` has the expected relative remainder. -/
theorem elementaryRC_sub_logarithmicTerm_isBigO {z : ℝ} (hz : 0 < z) :
    (fun s : ℝ => Real.log ((√z + √(z - s)) / √s) / √(z - s) - logarithmicTerm z s)
      =O[𝓝[>] 0] (fun s : ℝ => s * logarithmicTerm z s) := by
  let A : ℝ → ℝ := fun s => (√(z - s))⁻¹
  let B : ℝ → ℝ := fun s => Real.log ((√z + √(z - s)) / (2 * √z))
  let T : ℝ → ℝ := fun s => Real.log (4 * z / s) / 2
  have hroot := Real.sqrt_pos.mpr hz
  have hA : DifferentiableAt ℝ A 0 := by unfold A; fun_prop (disch := positivity)
  have hB : DifferentiableAt ℝ B 0 := by unfold B; fun_prop (disch := positivity)
  have hB0 : B 0 = 0 := by
    simp only [B, sub_zero]
    rw [show √z + √z = 2 * √z by ring, div_self (by positivity), Real.log_one]
  have hAO : (fun s : ℝ => A s - A 0) =O[𝓝 (0 : ℝ)] (fun s => s) := by
    simpa only [sub_zero] using hA.isBigO_sub
  have hBO : B =O[𝓝 (0 : ℝ)] (fun s => s) := by
    simpa only [hB0, sub_zero] using hB.isBigO_sub
  have hA1 : A =O[𝓝 (0 : ℝ)] (fun _ => (1 : ℝ)) := hA.continuousAt.tendsto.isBigO_one ℝ
  have hAB : (fun s : ℝ => A s * B s) =O[𝓝[>] 0] (fun s => s) := by
    simpa only [one_mul] using (hA1.mul hBO).mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hT1 : (fun _ : ℝ => (1 : ℝ)) =O[𝓝[>] 0] T := by
    refine isBigO_iff.mpr ⟨1, ?_⟩
    have hδ : 0 < 4 * z / Real.exp 2 := by positivity
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hδ)] with s hs hsmall
    have hs0 : 0 < s := hs
    have hratio : Real.exp 2 ≤ 4 * z / s := by
      apply (le_div_iff₀ hs0).mpr
      have H := (lt_div_iff₀ (Real.exp_pos (2 : ℝ))).mp hsmall
      nlinarith
    have hlog : (2 : ℝ) ≤ Real.log (4 * z / s) := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (2 : ℝ)) hratio
    have hT : 1 ≤ T s := by dsimp only [T]; linarith
    rw [norm_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ T s)]
    exact hT
  have hsT : (fun s : ℝ => s) =O[𝓝[>] 0] (fun s => s * T s) := by
    simpa only [mul_one] using (isBigO_refl (fun s : ℝ => s) (𝓝[>] (0 : ℝ))).mul hT1
  have H := ((hAO.mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).mul
    (isBigO_refl T (𝓝[>] (0 : ℝ)))).add (hAB.trans hsT)
  have he (s : ℝ) (hs : 0 < s) :
      Real.log ((√z + √(z - s)) / √s) / √(z - s) - logarithmicTerm z s =
        (A s - A 0) * T s + A s * B s := by
    have hS : 0 < √z + √(z - s) := by positivity
    have hT : T s = Real.log (2 * √z) - Real.log (√s) := by
      have H := logarithmicTerm_eq hz hs
      dsimp only [logarithmicTerm, T] at H ⊢
      field_simp at H ⊢
      exact H
    rw [logarithmicTerm_eq hz hs]
    dsimp only [A, B, sub_zero]
    rw [Real.log_div hS.ne' (Real.sqrt_pos.mpr hs).ne',
      Real.log_div hS.ne' (by positivity : 2 * √z ≠ 0), hT]
    ring
  have H' := H.congr' (show _ =ᶠ[𝓝[>] (0 : ℝ)] _ from by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (he s hs).symm) Filter.EventuallyEq.rfl
  have H'' := Asymptotics.IsBigO.const_mul_right (inv_ne_zero hroot.ne') H'
  convert H'' using 1
  funext s
  dsimp only [T, logarithmicTerm]
  ring

/-- The logarithmic remainder of `R_C(z,s)` for a positive fixed outer node. -/
theorem symmetricEllipticRC_sub_logarithmicTerm_isBigO {z : ℝ} (hz : 0 < z) :
    (fun s : ℝ => symmetricEllipticRC z s - ((logarithmicTerm z s : ℝ) : ℂ))
      =O[𝓝[>] 0] (fun s : ℝ => ((s * logarithmicTerm z s : ℝ) : ℂ)) := by
  have H : (fun s : ℝ => ((Real.log ((√z + √(z - s)) / √s) / √(z - s) -
      logarithmicTerm z s : ℝ) : ℂ)) =O[𝓝[>] 0]
      (fun s : ℝ => ((s * logarithmicTerm z s : ℝ) : ℂ)) :=
    Complex.isBigO_ofReal_left.mpr
      (Complex.isBigO_ofReal_right.mpr (elementaryRC_sub_logarithmicTerm_isBigO hz))
  apply H.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hz)] with s hs hsz
  rw [(symmetricEllipticRC_of_gt hs hsz).2, ofReal_sub]


/-- The rational comparison gives a uniform relative logarithmic error. -/
theorem norm_symmetricEllipticRF_sub_symmetricEllipticRC_le {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 < ellAsymA x y) (hz : 0 < z)
    (haz : ellAsymA x y ≤ z / 2) :
    ‖symmetricEllipticRF x y z - symmetricEllipticRC z (comparisonParameter x y)‖ ≤
      8 * (ellAsymA x y / z * logarithmicTerm z (comparisonParameter x y)) := by
  let a : ℝ := ellAsymA x y
  let s : ℝ := comparisonParameter x y
  have hs : 0 < s := comparisonParameter_pos ha
  have hsa : s ≤ a := (comparisonParameter_bounds hx hy).2
  have haz' : a < z := by dsimp only [a]; linarith
  have hlog : 0 ≤ Real.log (z / a) := Real.log_nonneg ((le_div_iff₀ ha).mpr (by linarith))
  have hratio : z / a ≤ 4 * z / s := by
    apply (div_le_div_iff₀ ha hs).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsa hz.le, mul_pos hz ha]
  have hlogle := Real.log_le_log (div_pos hz ha) hratio
  have H := LogarithmicSquareRoot.abs_integral_pair_kernel_mul_sqrt_shift_le
    hx hy hs.le hsa ha haz'
  rw [symmetricEllipticRF_sub_symmetricEllipticRC_eq_regularized_integral hx hy ha haz',
    norm_mul, norm_neg, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num [norm_div],
    Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (1 / 2 : ℝ) * ((4 * a / √z) * (Real.log (z / a) / (z - a))) :=
      mul_le_mul_of_nonneg_left H (by norm_num)
    _ = (2 * a / √z) * (Real.log (z / a) / (z - a)) := by ring
    _ ≤ (2 * a / √z) * (Real.log (z / a) / (z / 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left hlog (half_pos hz) (by linarith)
    _ ≤ (2 * a / √z) * (Real.log (4 * z / s) / (z / 2)) := by
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlogle (half_pos hz).le)
        (by positivity)
    _ = 8 * (a / z * logarithmicTerm z s) := by dsimp only [logarithmicTerm]; ring

/-- Positivity of the arithmetic mean on the punctured nonnegative quadrant. -/
theorem arithmeticMean_pos_of_mem {q : ℝ × ℝ} (hq : q ∈ ellAsymPair) :
    0 < ellAsymA q.1 q.2 := by
  rcases hq with ⟨hx, hy, hq⟩
  have hxy : 0 < q.1 + q.2 := by
    by_contra h
    have hx0 : q.1 = 0 := by linarith
    have hy0 : q.2 = 0 := by linarith
    exact hq (Prod.ext hx0 hy0)
  dsimp only [ellAsymA]
  positivity

/-- The arithmetic mean tends to zero on the two-node approach domain. -/
theorem tendsto_arithmeticMean_zero :
    Tendsto (fun q : ℝ × ℝ => ellAsymA q.1 q.2) (𝓝[ellAsymPair] 0) (𝓝 0) := by
  have H : Continuous (fun q : ℝ × ℝ => ellAsymA q.1 q.2) := by unfold ellAsymA; fun_prop
  simpa only [ellAsymA, Prod.fst_zero, Prod.snd_zero, zero_add, zero_div] using
    (H.tendsto (0 : ℝ × ℝ)).mono_left nhdsWithin_le_nhds

/-- The comparison parameter approaches zero through positive values. -/
theorem tendsto_comparisonParameter_zero :
    Tendsto (fun q : ℝ × ℝ => comparisonParameter q.1 q.2) (𝓝[ellAsymPair] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have H : Continuous (fun q : ℝ × ℝ => comparisonParameter q.1 q.2) := by
      unfold comparisonParameter ellAsymA ellAsymG
      fun_prop
    simpa [comparisonParameter, ellAsymA, ellAsymG] using
      (H.tendsto (0 : ℝ × ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact comparisonParameter_pos (arithmeticMean_pos_of_mem hq)

/-- Positivity of the leading logarithm when its comparison parameter is small. -/
theorem logarithmicTerm_nonneg {z s : ℝ} (hz : 0 < z) (hs : 0 < s) (hsz : s ≤ z) :
    0 ≤ logarithmicTerm z s := by
  apply div_nonneg (Real.log_nonneg _) (by positivity)
  apply (le_div_iff₀ hs).mpr
  linarith

/-- The two-small-node comparison with `R_C` has relative arithmetic-mean error. -/
theorem symmetricEllipticRF_sub_symmetricEllipticRC_isBigO {z : ℝ} (hz : 0 < z) :
    (fun q : ℝ × ℝ => symmetricEllipticRF q.1 q.2 z -
      symmetricEllipticRC z (comparisonParameter q.1 q.2)) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((ellAsymA q.1 q.2 / z *
        logarithmicTerm z (comparisonParameter q.1 q.2) : ℝ) : ℂ)) := by
  refine isBigO_iff.mpr ⟨8, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    tendsto_arithmeticMean_zero.eventually (eventually_lt_nhds (half_pos hz))] with q hq hsmall
  have ha := arithmeticMean_pos_of_mem hq
  have hs := comparisonParameter_pos ha
  have hsa := (comparisonParameter_bounds hq.1 hq.2.1).2
  have hL := logarithmicTerm_nonneg hz hs (hsa.trans (by linarith))
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (div_nonneg ha.le hz.le) hL)]
  exact norm_symmetricEllipticRF_sub_symmetricEllipticRC_le hq.1 hq.2.1 ha hz hsmall.le

/-- The DLMF arithmetic-geometric leading term is the comparison logarithm. -/
theorem logarithmicTerm_comparisonParameter (x y z : ℝ) :
    logarithmicTerm z (comparisonParameter x y) =
      Real.log (8 * z / (ellAsymA x y + ellAsymG x y)) / (2 * √z) := by
  dsimp only [logarithmicTerm, comparisonParameter]
  rw [div_div_eq_mul_div]
  congr 2
  ring

end SymmetricLogarithmicEndpoint
open SymmetricLogarithmicEndpoint

/-- DLMF 19.27.2: `R_F(x, y, z) = (1/(2√z)) ln(8z/(a + g)) (1 + O(a/z))` as `a/z → 0`: for fixed
`z > 0`, as `(x, y) → 0` through nonnegative pairs not both zero. -/
@[dlmf 19.27.E2]
theorem symmetricEllipticRF_asymp_large_z {z : ℝ} (hz : 0 < z) :
    (fun q : ℝ × ℝ => symmetricEllipticRF q.1 q.2 z -
        ((Real.log (8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2)) / (2 * √z) : ℝ) : ℂ))
            =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((ellAsymA q.1 q.2 / z *
        (Real.log (8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2)) / (2 * √z)) : ℝ) : ℂ)) := by
  have hsmall : ∀ᶠ q : ℝ × ℝ in 𝓝[ellAsymPair] 0, ellAsymA q.1 q.2 < z / 2 :=
    tendsto_arithmeticMean_zero.eventually (eventually_lt_nhds (half_pos hz))
  have hcompare : (fun q : ℝ × ℝ => ((comparisonParameter q.1 q.2 *
      logarithmicTerm z (comparisonParameter q.1 q.2) : ℝ) : ℂ)) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((ellAsymA q.1 q.2 / z *
        logarithmicTerm z (comparisonParameter q.1 q.2) : ℝ) : ℂ)) := by
    refine isBigO_iff.mpr ⟨z, ?_⟩
    filter_upwards [self_mem_nhdsWithin, hsmall] with q hq hhalf
    have ha := arithmeticMean_pos_of_mem hq
    have hs := comparisonParameter_pos ha
    have hsa := (comparisonParameter_bounds hq.1 hq.2.1).2
    have hL := logarithmicTerm_nonneg hz hs (hsa.trans (by linarith))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs.le hL),
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (div_nonneg ha.le hz.le) hL)]
    calc
      _ ≤ ellAsymA q.1 q.2 * logarithmicTerm z (comparisonParameter q.1 q.2) :=
        mul_le_mul_of_nonneg_right hsa hL
      _ = z * (ellAsymA q.1 q.2 / z * logarithmicTerm z (comparisonParameter q.1 q.2)) := by
        field_simp
  have hRC := ((symmetricEllipticRC_sub_logarithmicTerm_isBigO hz).comp_tendsto
    tendsto_comparisonParameter_zero).trans hcompare
  have H := (symmetricEllipticRF_sub_symmetricEllipticRC_isBigO hz).add hRC
  apply H.congr
  · intro q
    simp only [Function.comp_apply]
    rw [logarithmicTerm_comparisonParameter]
    ring
  · intro q
    rw [logarithmicTerm_comparisonParameter]

end DLMF.EllipticIntegrals
