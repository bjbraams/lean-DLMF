/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Complex.Liouville

/-!
# Uniform discs inside a complex sector

A closed sector properly inside an open sector has discs whose radii are a fixed
positive multiple of the norm of their centers. Compactness of the arc of unit
directions supplies the uniform radius. Mathlib's
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` then bounds derivatives in
an interior sector.
-/

@[expose] public noncomputable section

open Set Metric Complex
open scoped Topology Real

namespace Complex

/-- A uniform relative disc around a point of a closed sector stays in a larger open
sector, and the norms in the disc remain comparable to the center norm. -/
theorem exists_pos_forall_closedBall_arg_lt {ω ω' : ℝ} (hω : ω ≤ π) (_hω' : 0 ≤ ω')
    (hωω' : ω' < ω) : ∃ c > 0, c ≤ 1 / 2 ∧ ∀ z : ℂ, 0 < ‖z‖ → |z.arg| ≤ ω' →
      ∀ w ∈ closedBall z (c * ‖z‖), |w.arg| < ω ∧ ‖z‖ / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * ‖z‖ := by
  let K : Set ℂ := (fun φ : ℝ => exp (φ * I)) '' Icc (-ω') ω'
  let U : Set ℂ := slitPlane ∩ (fun z : ℂ => |z.arg|) ⁻¹' Iio ω
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hU : IsOpen U := continuousOn_arg.abs.isOpen_inter_preimage isOpen_slitPlane isOpen_Iio
  have hKU : K ⊆ U := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hp : -π < φ ∧ φ ≤ π := by constructor <;> linarith [hφ.1, hφ.2]
    have ha : (exp (φ * I)).arg = φ := by
      rw [arg_exp_mul_I, toIocMod_eq_self]
      constructor <;> linarith [hp.1, hp.2]
    refine ⟨mem_slitPlane_iff_arg.mpr ⟨?_, exp_ne_zero _⟩, ?_⟩
    · rw [ha]
      linarith [hφ.2]
    · change |(exp (φ * I)).arg| < ω
      rw [ha, abs_lt]
      constructor <;> linarith [hφ.1, hφ.2]
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let c := min δ (1 / 2)
  have hc : 0 < c := lt_min hδ (by norm_num)
  have hcδ : c ≤ δ := min_le_left _ _
  have hc2 : c ≤ 1 / 2 := min_le_right _ _
  refine ⟨c, hc, hc2, fun z hz harg w hw => ?_⟩
  rw [mem_closedBall, dist_eq_norm] at hw
  have hz0 : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz.ne'
  have hunit : z / (‖z‖ : ℂ) ∈ K := by
    refine ⟨z.arg, abs_le.mp harg, ?_⟩
    apply (eq_div_iff hz0).mpr
    rw [mul_comm, norm_mul_exp_arg_mul_I]
  have hdist : dist (w / (‖z‖ : ℂ)) (z / (‖z‖ : ℂ)) ≤ δ := by
    rw [dist_eq_norm, ← sub_div, norm_div, norm_real, Real.norm_of_nonneg hz.le]
    exact ((div_le_iff₀ hz).mpr hw).trans hcδ
  have hwU := hδU (mem_cthickening_of_dist_le _ _ _ K hunit hdist)
  have hargw : |w.arg| < ω := by
    have h := hwU.2
    change |(w / (‖z‖ : ℂ)).arg| < ω at h
    rwa [div_eq_mul_inv, ← ofReal_inv, arg_mul_real (inv_pos.mpr hz)] at h
  have hnear : ‖w - z‖ ≤ ‖z‖ / 2 := by
    calc ‖w - z‖ ≤ c * ‖z‖ := hw
      _ ≤ (1 / 2) * ‖z‖ := mul_le_mul_of_nonneg_right hc2 hz.le
      _ = ‖z‖ / 2 := by ring
  have ht1 := norm_le_norm_add_norm_sub z w
  have ht2 := norm_le_norm_add_norm_sub w z
  rw [norm_sub_rev] at ht1
  exact ⟨hargw, by linarith, by linarith⟩

end Complex

/-- Real powers of two comparable positive numbers differ by at most a factor
`2 ^ |p|`, for positive and negative exponents alike. -/
theorem Real.rpow_le_two_rpow_abs_mul {x y p : ℝ} (hx : 0 < x)
    (hxy : x / 2 ≤ y) (hyx : y ≤ 2 * x) : y ^ p ≤ 2 ^ |p| * x ^ p := by
  rcases le_total 0 p with hp | hp
  · calc y ^ p ≤ (2 * x) ^ p := Real.rpow_le_rpow (by linarith) hyx hp
      _ = 2 ^ |p| * x ^ p := by rw [Real.mul_rpow (by norm_num) hx.le, abs_of_nonneg hp]
  · calc y ^ p ≤ (x / 2) ^ p := Real.rpow_le_rpow_of_nonpos (by positivity) hxy hp
      _ = 2 ^ |p| * x ^ p := by
        rw [Real.div_rpow hx.le (by norm_num), abs_of_nonpos hp, Real.rpow_neg (by norm_num)]
        ring

namespace Complex

/-- The uniform relative-disc estimate is invariant under rotation of the sector. -/
theorem exists_pos_forall_closedBall_rotated_arg_lt {ω ω' : ℝ} (hω : ω ≤ π) (hω' : 0 ≤ ω')
    (hωω' : ω' < ω) (θ : ℝ) : ∃ c > 0, c ≤ 1 / 2 ∧ ∀ z : ℂ,
      0 < ‖z‖ → |(z * exp (-(θ * I))).arg| ≤ ω' →
      ∀ w ∈ closedBall z (c * ‖z‖), |(w * exp (-(θ * I))).arg| < ω ∧
        ‖z‖ / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * ‖z‖ := by
  obtain ⟨c, hc, hc2, hb⟩ := exists_pos_forall_closedBall_arg_lt hω hω' hωω'
  have hr : ‖exp (-(θ * I))‖ = 1 := by rw [norm_exp]; simp [mul_re]
  have hn (v : ℂ) : ‖v * exp (-(θ * I))‖ = ‖v‖ := by rw [norm_mul, hr, mul_one]
  refine ⟨c, hc, hc2, fun z hz harg w hw => ?_⟩
  have h := hb (z * exp (-(θ * I))) (by rwa [hn]) harg (w * exp (-(θ * I))) (by
    rw [mem_closedBall, dist_eq_norm, ← sub_mul, hn, hn]
    simpa only [mem_closedBall, dist_eq_norm] using hw)
  simpa only [hn] using h

/-- Cauchy's derivative estimate transfers a power bound in an open sector to the next
power in an interior closed sector. The constant is independent of the function and the
radial cutoff, which also permits little-o applications. -/
theorem exists_pos_norm_deriv_le_of_sector_bound {ω ω' : ℝ} (hω : ω ≤ π) (hω' : 0 ≤ ω')
    (hωω' : ω' < ω) (θ ν : ℝ) : ∃ K > 0, ∀ (f : ℂ → ℂ) (A B : ℝ), 0 ≤ B →
      DifferentiableOn ℂ f {w | A < ‖w‖ ∧ |(w * exp (-(θ * I))).arg| < ω} →
      (∀ w, A < ‖w‖ → |(w * exp (-(θ * I))).arg| < ω → ‖f w‖ ≤ B * ‖w‖ ^ ν) →
      ∀ z : ℂ, 2 * max A 0 < ‖z‖ → |(z * exp (-(θ * I))).arg| ≤ ω' →
        ‖deriv f z‖ ≤ K * B * ‖z‖ ^ (ν - 1) := by
  obtain ⟨c, hc, _hc2, hb⟩ := exists_pos_forall_closedBall_rotated_arg_lt hω hω' hωω' θ
  refine ⟨2 ^ |ν| / c, by positivity, fun f A B hB hf hbound z hz harg => ?_⟩
  have hz0 : 0 < ‖z‖ := by linarith [le_max_right A 0]
  have hsub : closedBall z (c * ‖z‖) ⊆ {w | A < ‖w‖ ∧ |(w * exp (-(θ * I))).arg| < ω} := by
    intro w hw
    have h := hb z hz0 harg w hw
    exact ⟨by linarith [le_max_left A 0, h.2.1], h.1⟩
  have hd := norm_deriv_le_of_forall_mem_sphere_norm_le (mul_pos hc hz0)
    (hf.diffContOnCl_ball hsub) (C := B * 2 ^ |ν| * ‖z‖ ^ ν) (fun w hw => by
      have hwc := sphere_subset_closedBall hw
      have h := hb z hz0 harg w hwc
      calc ‖f w‖ ≤ B * ‖w‖ ^ ν := hbound w (hsub hwc).1 h.1
        _ ≤ B * (2 ^ |ν| * ‖z‖ ^ ν) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_two_rpow_abs_mul hz0 h.2.1 h.2.2) hB
        _ = B * 2 ^ |ν| * ‖z‖ ^ ν := by ring)
  refine hd.trans_eq ?_
  rw [Real.rpow_sub hz0, Real.rpow_one]
  field_simp

end Complex
