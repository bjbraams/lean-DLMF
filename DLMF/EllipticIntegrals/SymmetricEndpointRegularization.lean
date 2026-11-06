/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.SymmetricAsymptotics
public import DLMFMathlib.Analysis.Integral.SquareRootKernel

/-!
# Endpoint regularization of the third symmetric elliptic integral

Subtracting `3 R_C(x,p)/√(yz)` from `R_J(x,y,z,p)` removes the singularity as the first node
and the third-kind parameter approach zero. The remaining real kernel has a numerator that
vanishes linearly at the origin, so square-root shift bounds control its endpoint error.
The same estimates give the simultaneous zero-node limit with positive parameter, and a
linear remainder after subtracting the leading square-root term at a single zero node.

## Main results

* `symmetricEllipticRJ_asymp_large_p`: the simultaneous small-node expansion, DLMF 19.27.11.
* `symmetricEllipticRJ_asymp_small_xp`: the joint first-node and parameter expansion,
  DLMF 19.27.14.
* `symmetricEllipticRJ_asymp_small_x`: the single-node expansion, DLMF 19.27.15.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory Asymptotics
open scoped Real Topology

namespace DLMF.EllipticIntegrals

namespace SymmetricEndpoint

/-- The regular numerator after subtracting the constant square-root factor at the endpoint. -/
def numerator (y z t : ℝ) : ℝ :=
  (√y * √z)⁻¹ - (√(t + y) * √(t + z))⁻¹

/-- The regular numerator is nonnegative on the positive half-line. -/
theorem nonneg_numerator {y z t : ℝ} (hy : 0 < y) (hz : 0 < z) (ht : 0 ≤ t) :
    0 ≤ numerator y z t := by
  unfold numerator
  apply sub_nonneg.mpr
  apply inv_anti₀ (mul_pos (Real.sqrt_pos.mpr hy) (Real.sqrt_pos.mpr hz))
  exact mul_le_mul (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_le_sqrt (by linarith))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The regular numerator is bounded by its limiting value at infinity. -/
theorem numerator_le {y z t : ℝ} :
    numerator y z t ≤ (√y * √z)⁻¹ := by
  unfold numerator
  exact sub_le_self _ (inv_nonneg.mpr (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

/-- A global linear bound for the regular numerator. -/
theorem numerator_le_mul {y z t : ℝ} (hy : 0 < y) (hz : 0 < z) (ht : 0 ≤ t) :
    numerator y z t ≤ ((√y * √z)⁻¹ * (y⁻¹ + z⁻¹)) * t := by
  have hty : 0 < t + y := by linarith
  have htz : 0 < t + z := by linarith
  have hY := SquareRootShift.inv_sqrt_sub_inv_sqrt_add_le hy ht
  have hZ := SquareRootShift.inv_sqrt_sub_inv_sqrt_add_le hz ht
  rw [add_comm y t] at hY
  rw [add_comm z t] at hZ
  have hdiffZ : 0 ≤ (√z)⁻¹ - (√(t + z))⁻¹ :=
    sub_nonneg.mpr (inv_anti₀ (Real.sqrt_pos.mpr hz) (Real.sqrt_le_sqrt (by linarith)))
  have hinvY : (√(t + y))⁻¹ ≤ (√y)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.mpr hy) (Real.sqrt_le_sqrt (by linarith))
  calc numerator y z t = ((√y)⁻¹ - (√(t + y))⁻¹) * (√z)⁻¹ +
      (√(t + y))⁻¹ * ((√z)⁻¹ - (√(t + z))⁻¹) := by
        dsimp only [numerator]
        rw [mul_inv, mul_inv]
        ring
    _ ≤ (t / (y * √y)) * (√z)⁻¹ + (√y)⁻¹ * (t / (z * √z)) :=
      add_le_add (mul_le_mul_of_nonneg_right hY (inv_nonneg.mpr (Real.sqrt_nonneg _)))
        (mul_le_mul hinvY hZ hdiffZ (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    _ = ((√y * √z)⁻¹ * (y⁻¹ + z⁻¹)) * t := by ring

/-- The endpoint regularized kernel is integrable. -/
theorem integrableOn_numerator_div_sqrt_mul {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => numerator y z t / (√t * t)) (Ioi 0) := by
  exact integrableOn_div_sqrt_mul_self (by unfold numerator; fun_prop)
    (fun t ht => nonneg_numerator hy hz ht.le) (fun t ht => numerator_le_mul hy hz ht.le)
    (fun t _ => numerator_le)

/-- The singular part of `R_J` is exactly an `R_C` kernel. -/
theorem symmetricEllipticRC_sub_symmetricEllipticRJ_eq_integral {x y z p : ℝ}
    (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z) (hp : 0 < p) :
    3 / (√y * √z : ℝ) * symmetricEllipticRC x p - symmetricEllipticRJ x y z p =
      (3 / 2 : ℂ) * ((∫ t in Ioi (0 : ℝ),
        numerator y z t / (√(t + x) * (t + p)) : ℝ) : ℂ) := by
  have hxc : IsCarlsonArgument (x : ℂ) := by
    rcases hx.eq_or_lt with h | h
    · right; exact_mod_cast h.symm
    · exact Or.inl (ofReal_mem_slitPlane.mpr h)
  have hys := ofReal_mem_slitPlane.mpr hy
  have hzs := ofReal_mem_slitPlane.mpr hz
  have hps := ofReal_mem_slitPlane.mpr hp
  have hRC := integrableOn_symmetricEllipticRC_integrand hxc hps
  have hRJ : IntegrableOn (fun t : ℝ =>
      (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹) (Ioi 0) := by
    simpa only [carlsonRootProduct] using
      integrableOn_symmetricEllipticRJ_integrand hxc hys hzs hps
  have hi := integrableOn_div_sqrt_mul_add (by unfold numerator; fun_prop) hx hp.le
    (fun t ht => nonneg_numerator hy hz ht.le) (integrableOn_numerator_div_sqrt_mul hy hz)
  have H : ((√y * √z : ℝ) : ℂ)⁻¹ * (∫ t in Ioi (0 : ℝ),
      (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + p))⁻¹) -
      (∫ t in Ioi (0 : ℝ), (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹) =
      ((∫ t in Ioi (0 : ℝ), numerator y z t / (√(t + x) * (t + p)) : ℝ) : ℂ) := by
    rw [← integral_const_mul, ← integral_sub (hRC.const_mul _) hRJ, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    have htx : 0 < t + x := by linarith
    have hty : 0 < t + y := by linarith
    have htz : 0 < t + z := by linarith
    simp only [carlsonRootProduct, ← ofReal_add, Carlson.ofReal_cpow_half htx.le,
      Carlson.ofReal_cpow_half hty.le, Carlson.ofReal_cpow_half htz.le]
    dsimp only [numerator]
    simp only [ofReal_sub, ofReal_inv, ofReal_mul, ofReal_div, ofReal_add]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  simp only [symmetricEllipticRC, symmetricEllipticRJ,
    not_isNegReal_of_mem_slitPlane hps, ↓reduceIte]
  push_cast at H ⊢
  linear_combination (3 / 2 : ℂ) * H

/-- The `R_F` and positive-parameter `R_J` kernels are integrable on the nonnegative domain. -/
theorem integrableOn_root_product_of_mem {q : ℝ × ℝ × ℝ} (hq : q ∈ ellAsymTriple)
    {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t => (carlsonRootProduct q.1 q.2.1 q.2.2 t)⁻¹) (Ioi 0) ∧
      IntegrableOn (fun t =>
        (carlsonRootProduct q.1 q.2.1 q.2.2 t * ((t : ℂ) + p))⁻¹) (Ioi 0) := by
  rcases hq with ⟨hx, hy, hz, hxy, hyz⟩
  rcases hx.eq_or_lt with hx0 | hx0
  · have hy' : 0 < q.2.1 := lt_of_le_of_ne hy (Ne.symm (hxy hx0.symm).1)
    have hz' : q.2.2 ≠ 0 := (hxy hx0.symm).2
    have H := integrableOn_carlsonRootProduct_inv_of_nonneg hy' hx hz
      (fun _ => hz') hp
    simpa only [carlsonRootProduct, mul_comm, mul_left_comm, mul_assoc] using H
  · exact integrableOn_carlsonRootProduct_inv_of_nonneg hx0 hy hz hyz hp

/-- Subtracting `R_J` from `3R_F/p` cancels the nonintegrable zero-node part. -/
theorem symmetricEllipticRF_sub_symmetricEllipticRJ_eq_integral
    {q : ℝ × ℝ × ℝ} (hq : q ∈ ellAsymTriple) {p : ℝ} (hp : 0 < p) :
    3 / (p : ℂ) * symmetricEllipticRF q.1 q.2.1 q.2.2 -
        symmetricEllipticRJ q.1 q.2.1 q.2.2 p =
      (3 / (2 * p) : ℂ) * ((∫ t in Ioi (0 : ℝ),
        t / (√(t + q.1) * √(t + q.2.1) * √(t + q.2.2) * (t + p)) : ℝ) : ℂ) := by
  obtain ⟨hF, hJ⟩ := integrableOn_root_product_of_mem hq hp
  have he : (∫ t in Ioi (0 : ℝ), (carlsonRootProduct q.1 q.2.1 q.2.2 t)⁻¹) -
      (p : ℂ) * (∫ t in Ioi (0 : ℝ),
        (carlsonRootProduct q.1 q.2.1 q.2.2 t * ((t : ℂ) + p))⁻¹) =
      ((∫ t in Ioi (0 : ℝ),
        t / (√(t + q.1) * √(t + q.2.1) * √(t + q.2.2) * (t + p)) : ℝ) : ℂ) := by
    rw [← integral_const_mul, ← integral_sub hF (hJ.const_mul _), ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have h1 : 0 < t + q.1 := add_pos_of_pos_of_nonneg ht hq.1
    have h2 : 0 < t + q.2.1 := add_pos_of_pos_of_nonneg ht hq.2.1
    have h3 : 0 < t + q.2.2 := add_pos_of_pos_of_nonneg ht hq.2.2.1
    have h4 : 0 < t + p := add_pos ht hp
    simp only [carlsonRootProduct, ← ofReal_add, Carlson.ofReal_cpow_half h1.le,
      Carlson.ofReal_cpow_half h2.le, Carlson.ofReal_cpow_half h3.le]
    simp only [ofReal_div, ofReal_mul, ofReal_add]
    have h4c : (t : ℂ) + p ≠ 0 := by exact_mod_cast h4.ne'
    field_simp [h4c]
    ring
  simp only [symmetricEllipticRF, symmetricEllipticRJ,
    not_isNegReal_of_mem_slitPlane (ofReal_mem_slitPlane.mpr hp), ↓reduceIte]
  have hp0 : (p : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  field_simp [hp0] at he ⊢
  linear_combination he

/-- The regular numerator after subtracting the endpoint weight in the third-kind integral. -/
def thirdKindNumerator (y z p t : ℝ) : ℝ :=
  (√y * √z * p)⁻¹ - (√(t + y) * √(t + z) * (t + p))⁻¹

/-- The regular third-kind numerator lies between zero and its limiting value. -/
theorem thirdKindNumerator_bounds {y z p t : ℝ}
    (hy : 0 < y) (hz : 0 < z) (hp : 0 < p) (ht : 0 ≤ t) :
    0 ≤ thirdKindNumerator y z p t ∧ thirdKindNumerator y z p t ≤ (√y * √z * p)⁻¹ := by
  have hle : √y * √z * p ≤ √(t + y) * √(t + z) * (t + p) := by
    gcongr <;> linarith
  constructor
  · exact sub_nonneg.mpr (inv_anti₀ (by positivity) hle)
  · exact sub_le_self _ (inv_nonneg.mpr (by positivity))

/-- The third-kind regular numerator vanishes at least linearly at the origin. -/
theorem thirdKindNumerator_le_mul {y z p t : ℝ}
    (hy : 0 < y) (hz : 0 < z) (hp : 0 < p) (ht : 0 ≤ t) :
    thirdKindNumerator y z p t ≤
      ((√y * √z)⁻¹ * (y⁻¹ + z⁻¹) / p + (√y * √z)⁻¹ / p ^ 2) * t := by
  have hN := numerator_le_mul hy hz ht
  have hN0 := nonneg_numerator hy hz ht
  have htp : 0 < t + p := add_pos_of_nonneg_of_pos ht hp
  have he : thirdKindNumerator y z p t = numerator y z t / (t + p) +
      (√y * √z)⁻¹ * (p⁻¹ - (t + p)⁻¹) := by
    dsimp only [thirdKindNumerator, numerator]
    simp only [mul_inv, div_eq_mul_inv]
    ring
  have hpbound : p⁻¹ - (t + p)⁻¹ ≤ t / p ^ 2 := by
    have heq : p⁻¹ - (t + p)⁻¹ = t / (p * (t + p)) := by field_simp; ring
    rw [heq]
    apply div_le_div_of_nonneg_left ht (sq_pos_of_pos hp)
    nlinarith
  rw [he]
  calc
    _ ≤ (((√y * √z)⁻¹ * (y⁻¹ + z⁻¹)) * t) / p +
      (√y * √z)⁻¹ * (t / p ^ 2) := by
      apply add_le_add
      · exact (div_le_div_of_nonneg_left hN0 hp (by linarith)).trans
          (div_le_div_of_nonneg_right hN hp.le)
      · exact mul_le_mul_of_nonneg_left hpbound (by positivity)
    _ = _ := by ring

/-- The regular third-kind numerator gives an integrable first moment. -/
theorem integrableOn_thirdKindNumerator_div_sqrt_mul {y z p : ℝ}
    (hy : 0 < y) (hz : 0 < z) (hp : 0 < p) :
    IntegrableOn (fun t : ℝ => thirdKindNumerator y z p t / (√t * t)) (Ioi 0) :=
  integrableOn_div_sqrt_mul_self (by unfold thirdKindNumerator; fun_prop)
    (fun t ht => (thirdKindNumerator_bounds hy hz hp ht.le).1)
    (fun t ht => thirdKindNumerator_le_mul hy hz hp ht.le)
    (fun t ht => (thirdKindNumerator_bounds hy hz hp ht.le).2)

/-- The real integral representation of `R_J` for nonnegative first node and positive others. -/
theorem symmetricEllipticRJ_eq_real_integral {x y z p : ℝ}
    (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z) (hp : 0 < p) :
    symmetricEllipticRJ x y z p = (3 / 2 : ℂ) * ((∫ t in Ioi (0 : ℝ),
      1 / (√(t + x) * √(t + y) * √(t + z) * (t + p)) : ℝ) : ℂ) := by
  simp only [symmetricEllipticRJ,
    not_isNegReal_of_mem_slitPlane (ofReal_mem_slitPlane.mpr hp), ↓reduceIte]
  congr 1
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have h1 : 0 < t + x := add_pos_of_pos_of_nonneg ht hx
  have h2 : 0 < t + y := add_pos ht hy
  have h3 : 0 < t + z := add_pos ht hz
  simp only [carlsonRootProduct, ← ofReal_add]
  rw [Carlson.ofReal_cpow_half h1.le, Carlson.ofReal_cpow_half h2.le,
    Carlson.ofReal_cpow_half h3.le]
  simp only [one_div, ofReal_inv, ofReal_mul, ofReal_add]

/-- The real third-kind kernel is integrable on the nonnegative domain. -/
theorem integrableOn_real_third_kind_kernel {x y z p : ℝ}
    (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z) (hp : 0 < p) :
    IntegrableOn (fun t : ℝ => 1 / (√(t + x) * √(t + y) * √(t + z) * (t + p))) (Ioi 0) := by
  have hxc : IsCarlsonArgument (x : ℂ) := by
    rcases hx.eq_or_lt with h | h
    · right; exact_mod_cast h.symm
    · exact Or.inl (ofReal_mem_slitPlane.mpr h)
  have H := (integrableOn_symmetricEllipticRJ_integrand hxc
    (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz)
    (ofReal_mem_slitPlane.mpr hp)).re
  refine H.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  have h1 : 0 < t + x := add_pos_of_pos_of_nonneg ht hx
  have h2 : 0 < t + y := add_pos ht hy
  have h3 : 0 < t + z := add_pos ht hz
  simp only [← ofReal_add]
  rw [Carlson.ofReal_cpow_half h1.le, Carlson.ofReal_cpow_half h2.le,
    Carlson.ofReal_cpow_half h3.le]
  simp only [← ofReal_mul, ← ofReal_inv, one_div]
  exact Complex.ofReal_re _

/-- Subtracting the endpoint weight leaves a regular third-kind numerator. -/
theorem symmetricEllipticRJ_sub_zero_node_eq_integral {x y z p : ℝ}
    (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z) (hp : 0 < p) :
    symmetricEllipticRJ x y z p - symmetricEllipticRJ 0 y z p +
        ((3 * √x / (√y * √z * p) : ℝ) : ℂ) =
      (3 / 2 : ℂ) * ((∫ t in Ioi (0 : ℝ), thirdKindNumerator y z p t *
        ((√t)⁻¹ - (√(t + x))⁻¹) : ℝ) : ℂ) := by
  let M : ℝ := (√y * √z * p)⁻¹
  let K : ℝ → ℝ → ℝ := fun a t => 1 / (√(t + a) * √(t + y) * √(t + z) * (t + p))
  have hK (a : ℝ) (ha : 0 ≤ a) : IntegrableOn (K a) (Ioi 0) :=
    integrableOn_real_third_kind_kernel ha hy hz hp
  have hD := integrableOn_inv_sqrt_sub_inv_sqrt_add hx
  have he : (∫ t in Ioi (0 : ℝ), thirdKindNumerator y z p t *
        ((√t)⁻¹ - (√(t + x))⁻¹)) =
      M * (2 * √x) + (∫ t in Ioi (0 : ℝ), K x t) - ∫ t in Ioi (0 : ℝ), K 0 t := by
    calc _ = ∫ t in Ioi (0 : ℝ),
        (M * ((√t)⁻¹ - (√(t + x))⁻¹) + K x t) - K 0 t := by
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
          dsimp only [thirdKindNumerator, M, K]
          simp only [add_zero, one_div, mul_inv]
          ring
      _ = _ := by
        have hDK : IntegrableOn (fun t : ℝ =>
            M * ((√t)⁻¹ - (√(t + x))⁻¹) + K x t) (Ioi 0) :=
          (hD.const_mul M).add (hK x hx)
        rw [integral_sub hDK (hK 0 le_rfl),
          integral_add (hD.const_mul M) (hK x hx), integral_const_mul,
          integral_Ioi_inv_sqrt_sub_inv_sqrt_add hx]
  have hzero := symmetricEllipticRJ_eq_real_integral (x := 0) le_rfl hy hz hp
  simp only [ofReal_zero] at hzero
  rw [symmetricEllipticRJ_eq_real_integral hx hy hz hp, hzero, he]
  change (3 / 2 : ℂ) * ((∫ t in Ioi (0 : ℝ), K x t : ℝ) : ℂ) -
      (3 / 2 : ℂ) * ((∫ t in Ioi (0 : ℝ), K 0 t : ℝ) : ℂ) + _ = _
  dsimp only [M]
  push_cast
  ring

end SymmetricEndpoint

/-- DLMF 19.27.14: `R_J(x, y, z, p) = (3/√(yz)) R_C(x, p) - (6/(yz)) R_G(0, y, z)
+ O(√(x + 2p)/(yz))` as `max(x, p)/min(y, z) → 0`: for fixed `y, z > 0`, as `(x, p) → 0` with
`x ≥ 0`, `p > 0`. -/
@[dlmf 19.27.E14]
theorem symmetricEllipticRJ_asymp_small_xp {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    (fun q : ℝ × ℝ => symmetricEllipticRJ q.1 y z q.2 -
        (3 / (√(y * z) : ℝ) * symmetricEllipticRC q.1 q.2 - 6 / (y * z : ℝ) *
            symmetricEllipticRG 0 y z))
      =O[𝓝[{q | 0 ≤ q.1 ∧ 0 < q.2}] 0]
      (fun q : ℝ × ℝ => ((√(q.1 + 2 * q.2) / (y * z) : ℝ) : ℂ)) := by
  let H : ℝ → ℝ → ℝ := fun x p =>
    ∫ t in Ioi (0 : ℝ), SymmetricEndpoint.numerator y z t / (√(t + x) * (t + p))
  let I : ℝ := ∫ t in Ioi (0 : ℝ), SymmetricEndpoint.numerator y z t / (√t * t)
  let C : ℝ := (√y * √z)⁻¹ * (y⁻¹ + z⁻¹)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hi := SymmetricEndpoint.integrableOn_numerator_div_sqrt_mul hy hz
  have hbound (x p : ℝ) (hx : 0 ≤ x) (hp : 0 ≤ p) :
      |H x p - I| ≤ C * (2 * √x + 4 * √p) :=
    abs_integral_div_sqrt_mul_add_sub_le (by unfold SymmetricEndpoint.numerator; fun_prop)
      hC.le hx hp (fun t ht => SymmetricEndpoint.nonneg_numerator hy hz ht.le)
      (fun t ht => SymmetricEndpoint.numerator_le_mul hy hz ht.le) hi
  have hdiagonal : Tendsto (fun s : ℝ => (H s s : ℂ)) (𝓝[>] 0) (𝓝 (I : ℂ)) := by
    have hzero : Tendsto (fun s : ℝ => (H s s : ℂ) - I) (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun s : ℝ => 6 * C * √s) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with s hs
        rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        have H := hbound s s (le_of_lt hs) (le_of_lt hs)
        nlinarith
      · have hs : Tendsto (fun s : ℝ => √s) (𝓝[>] 0) (𝓝 0) := by
          simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left
            (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa using hs.const_mul (6 * C)
    convert hzero.add_const (I : ℂ) using 1 <;> simp
  have hRemainder := symmetricEllipticRD_asymp_small_z hy hz
  have hRlim : Tendsto (fun s : ℝ => symmetricEllipticRD y z s -
      (((3 / √(y * z * s) : ℝ) : ℂ) - 6 / (y * z : ℝ) * symmetricEllipticRG y z 0))
      (𝓝[>] 0) (𝓝 0) := by
    apply hRemainder.trans_tendsto
    have hc : Continuous (fun s : ℝ => 6 / (y * z : ℝ) * symmetricEllipticRG y z 0 *
        ((√(s / ellAsymG y z) : ℝ) : ℂ)) := by fun_prop
    simpa only [zero_div, Real.sqrt_zero, ofReal_zero, mul_zero] using
      (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hdiagEq (s : ℝ) (hs : 0 < s) : (H s s : ℂ) =
      (2 / 3 : ℂ) * (((3 / √(y * z * s) : ℝ) : ℂ) - symmetricEllipticRD y z s) := by
    have h := SymmetricEndpoint.symmetricEllipticRC_sub_symmetricEllipticRJ_eq_integral
      hs.le hy hz hs
    rw [symmetricEllipticRC_special.1 (s : ℂ) (ofReal_mem_slitPlane.mpr hs),
      cpow_neg, Carlson.ofReal_cpow_half hs.le] at h
    rw [symmetricEllipticRJ_comm_left, symmetricEllipticRJ_comm_right] at h
    change 3 / (√y * √z : ℝ) * (√s : ℂ)⁻¹ - symmetricEllipticRD y z s =
      (3 / 2 : ℂ) * (H s s : ℂ) at h
    rw [Real.sqrt_mul (mul_pos hy hz).le, Real.sqrt_mul hy.le]
    push_cast at h ⊢
    linear_combination -(2 / 3 : ℂ) * h
  have hvalue : (I : ℂ) = 4 / (y * z : ℝ) * symmetricEllipticRG y z 0 := by
    have HL := ((tendsto_const_nhds (x := 6 / (y * z : ℝ) * symmetricEllipticRG y z 0)).sub
      hRlim).const_mul (2 / 3 : ℂ)
    have H' : Tendsto (fun s : ℝ => (H s s : ℂ)) (𝓝[>] 0)
        (𝓝 (4 / (y * z : ℝ) * symmetricEllipticRG y z 0)) := by
      convert HL.congr' (show _ =ᶠ[𝓝[>] (0 : ℝ)] (fun s : ℝ => (H s s : ℂ)) from ?_) using 1
      · ring
      · filter_upwards [self_mem_nhdsWithin] with s hs
        rw [hdiagEq s hs]
        ring
    exact tendsto_nhds_unique hdiagonal H'
  apply IsBigO.of_bound (9 * C * y * z)
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hx : 0 ≤ q.1 := hq.1
  have hp : 0 < q.2 := hq.2
  have hEq : symmetricEllipticRJ q.1 y z q.2 -
      (3 / (√(y * z) : ℝ) * symmetricEllipticRC q.1 q.2 - 6 / (y * z : ℝ) *
        symmetricEllipticRG 0 y z) = -(3 / 2 : ℂ) * ((H q.1 q.2 : ℂ) - I) := by
    have H := SymmetricEndpoint.symmetricEllipticRC_sub_symmetricEllipticRJ_eq_integral
      hx hy hz hp
    have hG : symmetricEllipticRG y z 0 = symmetricEllipticRG 0 y z := by
      rw [symmetricEllipticRG_comm_right, symmetricEllipticRG_comm_left]
    rw [Real.sqrt_mul hy.le]
    rw [hG] at hvalue
    linear_combination -H - (3 / 2 : ℂ) * hvalue
  rw [hEq, norm_mul]
  norm_num only [norm_neg, norm_div, norm_ofNat]
  rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.sqrt_nonneg (q.1 + 2 * q.2)) (mul_pos hy hz).le)]
  have hxS : √q.1 ≤ √(q.1 + 2 * q.2) := Real.sqrt_le_sqrt (by linarith)
  have hpS : √q.2 ≤ √(q.1 + 2 * q.2) := Real.sqrt_le_sqrt (by linarith)
  have hb := hbound q.1 q.2 hx hp.le
  have hbc : C * (2 * √q.1 + 4 * √q.2) ≤ 6 * C * √(q.1 + 2 * q.2) := by
    nlinarith [mul_le_mul_of_nonneg_left hxS hC.le, mul_le_mul_of_nonneg_left hpS hC.le]
  calc
    (3 / 2 : ℝ) * |H q.1 q.2 - I| ≤ (3 / 2 : ℝ) * (6 * C * √(q.1 + 2 * q.2)) := by
      gcongr
      exact hb.trans hbc
    _ = 9 * C * y * z * (√(q.1 + 2 * q.2) / (y * z)) := by field_simp; ring


/-- DLMF 19.27.11: `R_J(x, y, z, p) = (3/p) R_F(x, y, z) - (3π/(2p^{3/2}))(1 + O(√(c/p)))` as
`c/p → 0`: for fixed `p > 0`, as `(x, y, z) → 0` through nonnegative triples with at most one
zero. -/
@[dlmf 19.27.E11]
theorem symmetricEllipticRJ_asymp_large_p {p : ℝ} (hp : 0 < p) :
    (fun q : ℝ × ℝ × ℝ => symmetricEllipticRJ q.1 q.2.1 q.2.2 p -
        (3 / (p : ℂ) * symmetricEllipticRF q.1 q.2.1 q.2.2 -
            ((3 * π / (2 * p ^ (3 / 2 : ℝ)) : ℝ) : ℂ)))
      =O[𝓝[ellAsymTriple] 0]
      (fun q : ℝ × ℝ × ℝ => ((3 * π / (2 * p ^ (3 / 2 : ℝ)) *
        √(ellAsymC q.1 q.2.1 q.2.2 / p) : ℝ) : ℂ)) := by
  let B : ℝ := 3 * π / (2 * p ^ (3 / 2 : ℝ))
  have hB : 0 < B := by dsimp only [B]; positivity
  have hpower : p ^ (3 / 2 : ℝ) = p * √p := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp,
      Real.rpow_one, Real.sqrt_eq_rpow]
  have hBc : (B : ℂ) = (3 / (2 * p) : ℂ) * ((π / √p : ℝ) : ℂ) := by
    dsimp only [B]
    rw [hpower]
    push_cast
    ring
  have hbound (q : ℝ × ℝ × ℝ) (hq : q ∈ ellAsymTriple) :
      ‖symmetricEllipticRJ q.1 q.2.1 q.2.2 p -
        (3 / (p : ℂ) * symmetricEllipticRF q.1 q.2.1 q.2.2 - B)‖ ≤
        (3 / p ^ 2) * (√q.1 + √q.2.1 + √q.2.2) := by
    have he := SymmetricEndpoint.symmetricEllipticRF_sub_symmetricEllipticRJ_eq_integral hq hp
    have herr : symmetricEllipticRJ q.1 q.2.1 q.2.2 p -
        (3 / (p : ℂ) * symmetricEllipticRF q.1 q.2.1 q.2.2 - B) =
        (3 / (2 * p) : ℂ) * (((π / √p - ∫ t in Ioi (0 : ℝ),
          t / (√(t + q.1) * √(t + q.2.1) * √(t + q.2.2) * (t + p))) : ℝ) : ℂ) := by
      rw [hBc]
      push_cast
      linear_combination -he
    rw [herr, norm_mul, ← ofReal_ofNat 3, ← ofReal_ofNat 2, ← ofReal_mul, ← ofReal_div,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (3 : ℝ) / (2 * p)), Complex.norm_real,
      Real.norm_eq_abs, abs_sub_comm]
    calc _ ≤ (3 / (2 * p)) * ((2 / p) * (√q.1 + √q.2.1 + √q.2.2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact abs_integral_div_sqrt_product_sub_le
            hq.1 hq.2.1 hq.2.2.1 hp
      _ = (3 / p ^ 2) * (√q.1 + √q.2.1 + √q.2.2) := by ring
  refine isBigO_iff.mpr ⟨(9 / p ^ 2) * √(3 * p) / B, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with q hq
  change q ∈ ellAsymTriple at hq
  change ‖symmetricEllipticRJ _ _ _ p - (3 / (p : ℂ) * symmetricEllipticRF _ _ _ - B)‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hB.le (Real.sqrt_nonneg _))]
  have hsum : 0 ≤ q.1 + q.2.1 + q.2.2 := by linarith [hq.1, hq.2.1, hq.2.2.1]
  have h1 : √q.1 ≤ √(q.1 + q.2.1 + q.2.2) :=
    Real.sqrt_le_sqrt (by linarith [hq.2.1, hq.2.2.1])
  have h2 : √q.2.1 ≤ √(q.1 + q.2.1 + q.2.2) :=
    Real.sqrt_le_sqrt (by linarith [hq.1, hq.2.2.1])
  have h3 : √q.2.2 ≤ √(q.1 + q.2.1 + q.2.2) :=
    Real.sqrt_le_sqrt (by linarith [hq.1, hq.2.1])
  have heq : √(q.1 + q.2.1 + q.2.2) = √(3 * p) * √(ellAsymC q.1 q.2.1 q.2.2 / p) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 3 * p)]
    congr 1
    dsimp only [ellAsymC]
    field_simp
  calc _ ≤ (3 / p ^ 2) * (√q.1 + √q.2.1 + √q.2.2) := hbound q hq
    _ ≤ (9 / p ^ 2) * √(q.1 + q.2.1 + q.2.2) := by
      have H : √q.1 + √q.2.1 + √q.2.2 ≤ 3 * √(q.1 + q.2.1 + q.2.2) := by linarith
      convert mul_le_mul_of_nonneg_left H (by positivity : 0 ≤ 3 / p ^ 2) using 1; ring
    _ = (9 / p ^ 2) * √(3 * p) / B * (B * √(ellAsymC q.1 q.2.1 q.2.2 / p)) := by
      rw [heq]
      field_simp

/-- DLMF 19.27.15: `R_J(x, y, z, p) = R_J(0, y, z, p) - (3√x/(hp))(1 + O((b/h + h/p)√(x/h)))`
as `x/min(y, z, p) → 0`: for fixed `y, z, p > 0`, as `x → 0+`. -/
@[dlmf 19.27.E15]
theorem symmetricEllipticRJ_asymp_small_x {y z p : ℝ} (hy : 0 < y) (hz : 0 < z) (hp : 0 < p) :
    (fun x : ℝ => symmetricEllipticRJ x y z p - symmetricEllipticRJ 0 y z p +
        ((3 * √x / (ellAsymH y z * p) : ℝ) : ℂ)) =O[𝓝[≥] 0]
      (fun x : ℝ => ((3 * √x / (ellAsymH y z * p) *
        ((ellAsymB y z / ellAsymH y z + ellAsymH y z / p) * √(x / ellAsymH y z)) : ℝ) : ℂ)) := by
  let h : ℝ := ellAsymH y z
  let b : ℝ := ellAsymB y z
  let A : ℝ := 3 / (h * p) * (b / h + h / p) / √h
  let I : ℝ := ∫ t in Ioi (0 : ℝ), SymmetricEndpoint.thirdKindNumerator y z p t / (√t * t)
  have hh : 0 < h := Real.sqrt_pos.mpr (mul_pos hy hz)
  have hb : 0 < b := by dsimp [b, ellAsymB]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  have hs : √y * √z = h := (Real.sqrt_mul hy.le z).symm
  have hbound (x : ℝ) (hx : 0 ≤ x) :
      ‖symmetricEllipticRJ x y z p - symmetricEllipticRJ 0 y z p +
        ((3 * √x / (h * p) : ℝ) : ℂ)‖ ≤ (3 / 2 : ℝ) * x * I := by
    have he := SymmetricEndpoint.symmetricEllipticRJ_sub_zero_node_eq_integral hx hy hz hp
    rw [hs] at he
    rw [he, norm_mul]
    have H := integral_mul_inv_sqrt_sub_inv_sqrt_add_le
      (h := SymmetricEndpoint.thirdKindNumerator y z p)
      (by unfold SymmetricEndpoint.thirdKindNumerator; fun_prop) hx
      (fun t ht => (SymmetricEndpoint.thirdKindNumerator_bounds hy hz hp ht.le).1)
      (SymmetricEndpoint.integrableOn_thirdKindNumerator_div_sqrt_mul hy hz hp)
    rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2),
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg H.1]
    calc _ ≤ (3 / 2 : ℝ) * (x * I) := mul_le_mul_of_nonneg_left H.2 (by norm_num)
      _ = _ := by ring
  refine isBigO_iff.mpr ⟨(3 / 2 : ℝ) * I / A, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 ≤ x at hx
  have href : 3 * √x / (h * p) * ((b / h + h / p) * √(x / h)) = A * x := by
    rw [Real.sqrt_div hx, div_eq_mul_inv]
    dsimp only [A]
    have hprod : √x * √x = x := Real.mul_self_sqrt hx
    calc _ = 3 / (h * p) * (b / h + h / p) / √h * (√x * √x) := by ring
      _ = _ := by rw [hprod]
  change ‖symmetricEllipticRJ x y z p - symmetricEllipticRJ 0 y z p +
    ((3 * √x / (h * p) : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs, href, abs_of_nonneg (mul_nonneg hA.le hx)]
  calc _ ≤ (3 / 2 : ℝ) * x * I := hbound x hx
    _ = ((3 / 2 : ℝ) * I / A) * (A * x) := by field_simp

end DLMF.EllipticIntegrals
