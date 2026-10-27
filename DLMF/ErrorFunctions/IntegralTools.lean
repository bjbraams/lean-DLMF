/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.BoundsAsymptotics

/-!
# Tools for the integral representations of DLMF §§7.7 and 7.14

Helpers (prefix `erfInt_`) for `DLMF.ErrorFunctions.Integrals`:

* `erfInt_fresnelAux_laplace`: the Laplace forms of the Fresnel auxiliary functions
  (DLMF 7.7.10–7.7.11) on the closed sector `|arg z| ≤ π/4`, extending
  `fresnelAux_laplace_open` by continuity.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- If `Re w > 0` and `Re w² > 0`, then `|arg w| < π/4`. -/
theorem erfInt_abs_arg_lt_of_re_sq {w : ℂ} (hw : 0 < w.re) (hw2 : 0 < (w^2).re) :
    |arg w| < π/4 := by
  have h1 : |arg w| < π/2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hw)
  have hre : (w^2).re = ‖w‖^2*Real.cos (2*arg w) := by
    have e1 := Complex.norm_mul_cos_arg w
    have e2 := Complex.norm_mul_sin_arg w
    have h3 : (w^2).re = w.re*w.re - w.im*w.im := by simp [sq]
    rw [Real.cos_two_mul, h3, ← e1, ← e2]
    have hsc := Real.sin_sq_add_cos_sq (arg w)
    nlinarith [hsc]
  by_contra hcon
  push Not at hcon
  have hc : Real.cos (2*arg w) ≤ 0 := by
    rw [← Real.cos_abs, abs_mul, abs_two]
    exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [Real.pi_pos])
  have : (w^2).re ≤ 0 := by rw [hre]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
  linarith

/-- In the closed sector `|arg z| ≤ π/4`, `Re z ≥ 0` and `Re z² ≥ 0`. -/
theorem erfInt_re_nonneg_of_abs_arg_le {z : ℂ} (hz : |arg z| ≤ π/4) :
    0 ≤ z.re ∧ 0 ≤ (z^2).re := by
  constructor
  · rw [← Complex.norm_mul_cos_arg z]
    exact mul_nonneg (norm_nonneg _) (Real.cos_nonneg_of_mem_Icc ⟨by linarith [neg_abs_le (arg z),
      Real.pi_pos], by linarith [le_abs_self (arg z), Real.pi_pos]⟩)
  · have h := norm_sq_mul_cos_le_re_sq (by linarith [Real.pi_pos]) hz
    rwa [show 2*(π/4) = π/2 by ring, Real.cos_pi_div_two, mul_zero] at h

/-- For `|arg z| ≤ π/4` and `ε > 0`, the shifted point `z + ε` lies in the open sector. -/
theorem erfInt_shift_mem_open {z : ℂ} (hz : |arg z| ≤ π/4) {ε : ℝ} (hε : 0 < ε) :
    z + ε ≠ 0 ∧ |arg (z+ε)| < π/4 := by
  obtain ⟨h1, h2⟩ := erfInt_re_nonneg_of_abs_arg_le hz
  have hr : 0 < (z+ε).re := by simp; linarith
  have hr2 : 0 < ((z+ε)^2).re := by
    have : ((z+ε)^2).re = (z^2).re + 2*ε*z.re + ε^2 := by simp [sq, mul_re]; ring
    rw [this]; positivity
  exact ⟨fun h => by rw [h] at hr; simp at hr, erfInt_abs_arg_lt_of_re_sq hr hr2⟩

/-- Integrability of `t^{k-1/2}/(t²+1)` on `(0, ∞)` for `k ∈ {0, 1}`. -/
theorem erfInt_integrableOn_rpow_div (k : ℕ) (hk : k ≤ 1) :
    IntegrableOn (fun t : ℝ => t ^ ((k:ℝ) - 1/2) / (t^2+1)) (Ioi 0) := by
  have hs : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hs]
  have hk' : (k:ℝ) ≤ 1 := by exact_mod_cast hk
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  refine IntegrableOn.union ?_ ?_
  · have hi : IntegrableOn (fun t : ℝ => t ^ (-(1/2):ℝ)) (Ioc 0 1) := by
      have := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := -(1/2)) zero_lt_one).2
        (by norm_num)
      exact this.congr_set_ae Ioo_ae_eq_Ioc.symm
    refine hi.mono' ?_ ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall
      fun t ht => ?_))
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioc
      exact ((Real.continuousAt_rpow_const _ _ (Or.inl ht.1.ne')).div (by fun_prop)
        (by positivity)).continuousWithinAt
    · have ht0 : 0 < t := ht.1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc t ^ ((k:ℝ) - 1/2) / (t^2+1) ≤ t ^ ((k:ℝ) - 1/2) / 1 := by
            gcongr; nlinarith
        _ ≤ t ^ (-(1/2):ℝ) := by
            rw [div_one]
            exact Real.rpow_le_rpow_of_exponent_ge ht0 ht.2 (by linarith)
  · have hi : IntegrableOn (fun t : ℝ => t ^ (-(3/2):ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_iff zero_lt_one).2 (by norm_num)
    refine hi.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall
      fun t ht => ?_))
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
      have ht0 : (0:ℝ) < t := lt_trans zero_lt_one ht
      exact ((Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')).div (by fun_prop)
        (by positivity)).continuousWithinAt
    · have ht1 : (1:ℝ) < t := ht
      have ht0 : (0:ℝ) < t := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have e : t ^ (-(3/2):ℝ) = t ^ ((k:ℝ) - 1/2) * (t ^ ((1:ℝ) - k) / t^2) := by
        rw [mul_div_assoc', ← Real.rpow_add ht0, ← Real.rpow_natCast t 2, ← Real.rpow_sub ht0]
        congr 1; push_cast; ring
      rw [e, div_eq_mul_inv]
      gcongr
      have h1 : 1 ≤ t ^ ((1:ℝ) - k) := Real.one_le_rpow ht1.le (by linarith)
      rw [le_div_iff₀ (by positivity)]
      calc (t^2+1)⁻¹ * t^2 ≤ 1 := by
            rw [inv_mul_le_iff₀ (by positivity)]; linarith
        _ ≤ _ := h1

/-- **DLMF 7.7.10–7.7.11 on the closed sector** `|arg z| ≤ π/4` (including `z = 0`): the open-sector
Laplace forms `fresnelAux_laplace_open` extend by continuity along `z + ε`, `ε → 0⁺`. -/
theorem erfInt_fresnelAux_laplace (aux : Bool) {z : ℂ} (hz : |arg z| ≤ π/4) :
    (if aux then fresnelAuxGComplex z else fresnelAuxFComplex z) = 1/(π*Real.sqrt 2) *
      ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^(((if aux then 1 else 0 : ℕ) : ℂ) - 1/2) /
        ((t:ℂ)^2+1) := by
  set k : ℕ := if aux then 1 else 0 with hkdef
  have hk : k ≤ 1 := by simp only [k]; split_ifs <;> norm_num
  set F : ℂ → ℂ := fun w => ∫ t in Ioi (0:ℝ), exp (-π*w^2*t/2) * (t:ℂ)^((k : ℂ) - 1/2) /
    ((t:ℂ)^2+1) with hF
  set Φ : ℂ → ℂ := fun w => if aux then fresnelAuxGComplex w else fresnelAuxFComplex w with hΦ
  have hΦc : Continuous Φ := by
    simp only [Φ]; split_ifs
    · exact fresnelAuxGComplex_entire.continuous
    · exact fresnelAuxFComplex_entire.continuous
  have hL : Tendsto (fun ε : ℝ => Φ (z+ε)) (𝓝[>] 0) (𝓝 (Φ z)) := by
    have hc : Continuous fun ε : ℝ => Φ (z+ε) := hΦc.comp (by fun_prop)
    have h := hc.tendsto 0
    simp only [ofReal_zero, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hnorm : ∀ w : ℂ, 0 ≤ (w^2).re → ∀ t : ℝ, 0 < t →
      ‖exp (-π*w^2*t/2) * (t:ℂ)^((k : ℂ) - 1/2) / ((t:ℂ)^2+1)‖ ≤
        t ^ ((k:ℝ) - 1/2) / (t^2+1) := by
    intro w hw t ht
    have h1 : ((t:ℂ)^2+1) = ((t^2+1:ℝ):ℂ) := by push_cast; ring
    rw [h1, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos ht]
    have hre : (-π*w^2*t/2 : ℂ).re ≤ 0 := by
      have : (-π*w^2*t/2 : ℂ) = ((-(π*t/2):ℝ):ℂ) * w^2 := by push_cast; ring
      rw [this, re_ofReal_mul]
      have : 0 ≤ π*t/2 := by positivity
      nlinarith
    have he := Real.exp_le_one_iff.mpr hre
    have hkre : ((k:ℂ) - 1/2).re = (k:ℝ) - 1/2 := by simp
    rw [hkre]
    gcongr
    calc Real.exp (-π*w^2*t/2 : ℂ).re * t ^ ((k:ℝ) - 1/2) ≤ 1 * t ^ ((k:ℝ) - 1/2) := by
          gcongr
      _ = _ := one_mul _
  have hR : Tendsto (fun ε : ℝ => F (z+ε)) (𝓝[>] 0) (𝓝 (F z)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => t ^ ((k:ℝ) - 1/2) / (t^2+1)) ?_ ?_ (erfInt_integrableOn_rpow_div k hk) ?_
    · refine Eventually.of_forall fun ε => ContinuousOn.aestronglyMeasurable
        (fun t ht => ?_) measurableSet_Ioi
      have ht : (0:ℝ) < t := ht
      have h1 : ((t:ℂ)^2+1) ≠ 0 := by
        have : (0:ℝ) < t^2+1 := by positivity
        rw [show ((t:ℂ)^2+1) = ((t^2+1:ℝ):ℂ) by push_cast; ring]; exact_mod_cast this.ne'
      refine ContinuousAt.continuousWithinAt (ContinuousAt.div (ContinuousAt.mul (by fun_prop)
        (continuousAt_ofReal_cpow_const _ _ (Or.inr ht.ne'))) (by fun_prop) h1)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0:ℝ) < ε := hε
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      obtain ⟨h1, h2⟩ := erfInt_re_nonneg_of_abs_arg_le hz
      have : 0 ≤ ((z+ε)^2).re := by
        have : ((z+ε)^2).re = (z^2).re + 2*ε*z.re + ε^2 := by simp [sq, mul_re]; ring
        rw [this]; positivity
      exact hnorm _ this t ht
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t _ => ?_)
      have : Continuous fun ε : ℝ => exp (-π*(z+ε)^2*t/2) * (t:ℂ)^((k : ℂ) - 1/2) /
          ((t:ℂ)^2+1) := by fun_prop
      have h := this.tendsto 0
      simp only [ofReal_zero, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
  have heq : (fun ε : ℝ => Φ (z+ε)) =ᶠ[𝓝[>] 0] fun ε => 1/(π*Real.sqrt 2) * F (z+ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    obtain ⟨h0, ha⟩ := erfInt_shift_mem_open hz hε
    exact fresnelAux_laplace_open aux h0 ha
  have := tendsto_nhds_unique hL ((hR.const_mul ((1:ℂ)/(π*Real.sqrt 2))).congr' heq.symm)
  exact this

end DLMF.Confluent
