/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Transforms.MellinHilbertStieltjes
public import DLMF.Gamma.MellinBarnes

/-!
# The Stieltjes transform of a power

For `0 < ℜs < 1` and `z` in the cut plane `ℂ \ (-∞, 0]`,
`∫₀^∞ t^{s-1}/(z + t) dt = π z^{s-1}/sin(πs)` (principal power). For real `z > 0` this is the
Beta integral after the substitution `t = z u`; the general case follows from the analyticity of
the Stieltjes transform (DLMF §1.14(vi)) and the identity theorem. These integrals feed the
Mellin transforms of the Poisson-type kernels in DLMF Table 1.14.5.

## Main results

* `integrableOn_cpow_sub_one_div_one_add`: `t^{s-1}/(1 + t)` is integrable on `(0, ∞)`.
* `integral_cpow_sub_one_div_add`: `∫₀^∞ t^{s-1}/(z + t) dt = π z^{s-1}/sin(πs)`, `z ∈ slitPlane`.
* `integral_cpow_sub_one_mul_div_add`, `integrableOn_cpow_sub_one_mul_div_add`: the Mellin
  transform of `z/(z + t)` is `π z^s/sin(πs)`.
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology

namespace DLMF.AlgebraicAnalytic

/-- `t^{s-1}/(1 + t)` is integrable on `(0, ∞)` for `0 < ℜs < 1`. -/
theorem integrableOn_cpow_sub_one_div_one_add {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) / (((1 : ℝ) : ℂ) + t)) (Ioi 0) := by
  have h := DLMF.Gamma.integrableOn_rpow_mul_one_add_rpow (σ := s.re) (α := 1) hs0 hs1
  refine h.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) < t := ht
    have hn : ((1 : ℝ) : ℂ) + t ≠ 0 := by
      rw [← ofReal_add]; exact ofReal_ne_zero.mpr (by linarith)
    have hc1 : ContinuousAt (fun u : ℝ => (u : ℂ) ^ (s - 1)) t :=
      ContinuousAt.cpow (f := fun u : ℝ => (u : ℂ)) continuous_ofReal.continuousAt
        continuousAt_const (by simpa using ht0)
    have hc2 : ContinuousAt (fun u : ℝ => ((1 : ℝ) : ℂ) + u) t := by fun_prop
    exact (hc1.div hc2 hn).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_div, norm_cpow_eq_rpow_re_of_pos ht0, ← ofReal_add, Complex.norm_real,
      Real.norm_of_nonneg (by linarith), Real.rpow_neg_one, sub_re, one_re, div_eq_mul_inv]

/-- The Mellin transform `∫₀^∞ t^{s-1}/(1 + t) dt = π/sin(πs)`, `0 < ℜs < 1`. -/
private lemma mellin_one_div_one_add {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun x => 1 / (1 + (x : ℂ))) s = Real.pi / Complex.sin (s * Real.pi) := by
  have h := DLMF.Gamma.mellin_one_add_cpow_neg (a := 1) hs0 (by simpa using hs1)
  simpa [Complex.cpow_neg, Complex.Gamma_one, Complex.Gamma_mul_Gamma_one_sub,
    mul_comm] using h

/-- The Stieltjes transform of a power at a positive real point:
`∫₀^∞ t^{s-1}/(c + t) dt = π c^{s-1}/sin(πs)`. -/
private lemma integral_cpow_sub_one_div_ofReal_add {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) / ((c : ℂ) + t) =
      Real.pi * (c : ℂ) ^ (s - 1) / Complex.sin (s * Real.pi) := by
  have h := mellin_comp_mul_left (fun x : ℝ => 1 / (1 + (x : ℂ))) s (inv_pos.mpr hc)
  rw [mellin_one_div_one_add hs0 hs1] at h
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have he : ∀ t : ℝ, (t : ℂ) ^ (s - 1) / ((c : ℂ) + t) =
      (c : ℂ)⁻¹ * ((t : ℂ) ^ (s - 1) • (1 / (1 + ((c⁻¹ * t : ℝ) : ℂ)))) := by
    intro t
    push_cast
    rw [smul_eq_mul]
    have : (c : ℂ) + t ≠ 0 ∨ (c : ℂ) + t = 0 := by tauto
    rcases this with h1 | h1
    · field_simp
    · have : (1 : ℂ) + (c : ℂ)⁻¹ * t = 0 := by
        rw [show (1 : ℂ) + (c : ℂ)⁻¹ * t = (c : ℂ)⁻¹ * (c + t) by field_simp, h1, mul_zero]
      rw [h1, this]; simp
  simp_rw [he]
  rw [integral_const_mul]
  unfold mellin at h
  rw [h, ofReal_inv,
    inv_cpow _ _ (by simpa [arg_ofReal_of_nonneg hc.le] using Real.pi_ne_zero.symm),
    ← cpow_neg, neg_neg, smul_eq_mul, cpow_sub _ _ hc0, cpow_one]
  field_simp

/-- The Stieltjes transform of a power on the cut plane: for `0 < ℜs < 1` and
`z ∈ ℂ \ (-∞, 0]`, `∫₀^∞ t^{s-1}/(z + t) dt = π z^{s-1}/sin(πs)` (principal power). -/
theorem integral_cpow_sub_one_div_add {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {z : ℂ}
    (hz : z ∈ slitPlane) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) / (z + t) =
      Real.pi * z ^ (s - 1) / Complex.sin (s * Real.pi) := by
  have hF := differentiableOn_stieltjesTransform (f := fun t : ℝ => (t : ℂ) ^ (s - 1))
    one_pos (integrableOn_cpow_sub_one_div_one_add hs0 hs1)
  have hG : DifferentiableOn ℂ (fun w : ℂ => Real.pi * w ^ (s - 1) / Complex.sin (s * Real.pi))
      slitPlane := fun w hw =>
    (((differentiableAt_id.cpow_const hw).const_mul _).div_const _).differentiableWithinAt
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), stieltjesTransform (fun t : ℝ => (t : ℂ) ^ (s - 1)) w =
      Real.pi * w ^ (s - 1) / Complex.sin (s * Real.pi) := by
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 1) (𝓝[≠] 1) :=
      continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun x hx => by
        simpa using hx
    refine ht.frequently (Eventually.frequently ?_)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds one_pos)] with c hc
    exact integral_cpow_sub_one_div_ofReal_add hs0 hs1 hc
  exact (hF.analyticOnNhd isOpen_slitPlane).eqOn_of_preconnected_of_frequently_eq
    (hG.analyticOnNhd isOpen_slitPlane) (starConvex_one_slitPlane.isPathConnected
      one_mem_slitPlane).isConnected.isPreconnected one_mem_slitPlane hfreq hz

/-- `sin(πs) ≠ 0` on the strip `0 < ℜs < 1`. -/
private lemma sin_mul_pi_ne_zero_of_re {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Complex.sin (s * Real.pi) ≠ 0 := by
  rw [Ne, Complex.sin_eq_zero_iff]
  rintro ⟨k, hk⟩
  have hs : s = k := mul_right_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) hk
  have h0 : (0 : ℝ) < k := by simpa [hs] using hs0
  have h1 : (k : ℝ) < 1 := by simpa [hs] using hs1
  have h0' : 0 < k := by exact_mod_cast h0
  have h1' : k < 1 := by exact_mod_cast h1
  omega

/-- The Mellin transform of `z/(z + t)`: `∫₀^∞ t^{s-1} z/(z + t) dt = π z^s/sin(πs)` for
`0 < ℜs < 1` and `z ∈ ℂ \ (-∞, 0]`. -/
theorem integral_cpow_sub_one_mul_div_add {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {z : ℂ}
    (hz : z ∈ slitPlane) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (z / (z + t)) =
      Real.pi * z ^ s / Complex.sin (s * Real.pi) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have he : ∀ t : ℝ, (t : ℂ) ^ (s - 1) * (z / (z + t)) = z * ((t : ℂ) ^ (s - 1) / (z + t)) :=
    fun t => by ring
  simp_rw [he]
  rw [integral_const_mul, integral_cpow_sub_one_div_add hs0 hs1 hz, cpow_sub _ _ hz0, cpow_one]
  field_simp

/-- `t^{s-1} z/(z + t)` is integrable on `(0, ∞)` for `0 < ℜs < 1` and `z ∈ ℂ \ (-∞, 0]`. -/
theorem integrableOn_cpow_sub_one_mul_div_add {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * (z / (z + t))) (Ioi 0) := by
  by_contra h
  have hi := integral_cpow_sub_one_mul_div_add hs0 hs1 hz
  rw [integral_undef h] at hi
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have : (Real.pi : ℂ) * z ^ s / Complex.sin (s * Real.pi) ≠ 0 :=
    div_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
      ((cpow_ne_zero_iff_of_exponent_ne_zero (fun h => by simp [h] at hs0)).mpr hz0))
      (sin_mul_pi_ne_zero_of_re hs0 hs1)
  exact this hi.symm

end DLMF.AlgebraicAnalytic
