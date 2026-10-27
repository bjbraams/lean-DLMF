/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Asymptotics
public import DLMF.Bessel.Lommel

/-!
# Monotonicity of the first zero of `J_ν` (DLMF 10.21(iv); Watson §15.6)

With `B_ν(z) = ν J_ν(z) - z J_{ν+1}(z) = z J_ν'(z)`, Bessel's equation reads
`B_ν' = (ν²/z - z) J_ν`,
so `W = J_ν B_μ - B_ν J_μ` satisfies `W' = (μ² - ν²)/z · J_ν J_μ`.

For real `0 ≤ ν < μ`, suppose `j_{μ,1} ≤ j_{ν,1}`. Then `W` is strictly increasing on
`(0, j_{μ,1}]` and tends to `0` at `0⁺`, so `W(j_{μ,1}) = J_ν(j_{μ,1}) J_μ'(j_{μ,1}) j_{μ,1} > 0`.
This contradicts `J_μ > 0` on `(0, j_{μ,1})`. Hence the first positive zero
`sInf {x > 0 | J_ν(x) = 0}`
is strictly increasing in `ν ≥ 0`. The infimum is attained because `J_ν > 0` near `0⁺` and the
zero set is closed, using `DLMF.Bessel.besselJ_infinite_zeros_of_real` for nonemptiness.
-/

@[expose] public section

open Complex Filter Set
open scoped Real Topology

noncomputable section

namespace DLMF.Bessel

/-- `x J_ν'(x)` written as `ν J_ν - z J_{ν+1}`. -/
def besselB (ν z : ℂ) : ℂ := ν * besselJ ν z - z * besselJ (ν + 1) z

/-- `J_ν' = B_ν / z`. -/
theorem hasDerivAt_besselJ_B (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (besselJ ν) (besselB ν z / z) z := by
  have hz0 := slitPlane_ne_zero hz
  refine (hasDerivAt_besselJ hz).congr_deriv ?_
  simp only [besselB]; field_simp

/-- `B_ν' = (ν²/z - z) J_ν`: Bessel's equation in Sturm–Liouville form. -/
theorem hasDerivAt_besselB (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (besselB ν) ((ν ^ 2 / z - z) * besselJ ν z) z := by
  have hz0 := slitPlane_ne_zero hz
  have h1 := hasDerivAt_besselJ (ν := ν) hz
  have h2 := hasDerivAt_besselJ' (ν := ν + 1) hz
  rw [add_sub_cancel_right] at h2
  have h := (h1.const_mul ν).sub ((hasDerivAt_id z).mul h2)
  refine h.congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- The Wronskian-type function `J_ν B_μ - B_ν J_μ`. -/
def besselW (ν μ z : ℂ) : ℂ := besselJ ν z * besselB μ z - besselB ν z * besselJ μ z

/-- `(J_ν B_μ - B_ν J_μ)' = (μ² - ν²)/z · J_ν J_μ`. -/
theorem hasDerivAt_besselW (ν μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (besselW ν μ) ((μ ^ 2 - ν ^ 2) / z * besselJ ν z * besselJ μ z) z := by
  have hz0 := slitPlane_ne_zero hz
  have h := ((hasDerivAt_besselJ_B ν hz).mul (hasDerivAt_besselB μ hz)).sub
    ((hasDerivAt_besselB ν hz).mul (hasDerivAt_besselJ_B μ hz))
  refine h.congr_deriv ?_
  field_simp
  ring


/-- For real `ν > -1`, `J_ν(x) > 0` for small `x > 0`. -/
theorem eventually_re_besselJ_pos {ν : ℝ} (hν : -1 < ν) :
    ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), 0 < (besselJ ν x).re := by
  set G : ℝ → ℂ := fun x => regularizedHGFun (∅ : Multiset ℂ) {(ν : ℂ) + 1} (-((x : ℂ) ^ 2 / 4))
  have hG : ContinuousAt G 0 :=
    (analyticAt_regularized0F1 _ _).continuousAt.comp (by fun_prop)
  have hG0 : G 0 = ((Real.Gamma (ν + 1))⁻¹ : ℝ) := by
    simp only [G]
    rw [show -(((0 : ℝ) : ℂ) ^ 2 / 4) = 0 by simp, DLMF.Confluent.regularizedHGFun_zero,
      regularizedHGFunCoeff_empty]
    push_cast
    rw [← Gamma_ofReal]; push_cast; simp
  have hpos : 0 < (G 0).re := by
    rw [hG0, ofReal_re]; exact inv_pos.mpr (Real.Gamma_pos_of_pos (by linarith))
  have hev : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < (G x).re :=
    (continuous_re.continuousAt.comp hG).eventually (lt_mem_nhds hpos)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with x hx hx0
  have hx0 : (0 : ℝ) < x := hx0
  have hJ : besselJ ν x = (((x / 2) ^ ν : ℝ) : ℂ) * G x := by
    simp only [besselJ_eq_regularized, G]
    rw [ofReal_cpow (by positivity)]
    push_cast; ring_nf
  rw [hJ, re_ofReal_mul]
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) hx


/-- The first positive zero of `J_ν` (`ν > -1` real) is attained, and `J_ν > 0` before it. -/
theorem sInf_besselJ_zeros_spec {ν : ℝ} (hν : -1 < ν) :
    sInf {x : ℝ | 0 < x ∧ besselJ ν x = 0} ∈ {x : ℝ | 0 < x ∧ besselJ ν x = 0} ∧
      ∀ x ∈ Ioo 0 (sInf {x : ℝ | 0 < x ∧ besselJ ν x = 0}), 0 < (besselJ ν x).re := by
  set S := {x : ℝ | 0 < x ∧ besselJ ν x = 0}
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, x ∈ Ioo 0 δ → 0 < (besselJ ν x).re := by
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (eventually_re_besselJ_pos hν)
    exact ⟨u, hu, fun x hx => hsub hx⟩
  have hδS : ∀ x : ℝ, x ∈ S → δ ≤ x := by
    intro x hx
    by_contra h
    push Not at h
    have := hδ x ⟨hx.1, h⟩
    rw [hx.2, zero_re] at this
    exact lt_irrefl _ this
  have hne : S.Nonempty := (DLMF.Bessel.besselJ_infinite_zeros_of_real ν).nonempty
  have hbdd : BddBelow S := ⟨δ, hδS⟩
  have hclosed : IsClosed S := by
    have hc : ContinuousOn (fun x : ℝ => besselJ ν x) (Ici δ) := by
      intro x hx
      have hs : (x : ℂ) ∈ slitPlane := Or.inl (by simp; linarith [show δ ≤ x from hx])
      exact ((hasDerivAt_besselJ (ν := ν) hs).continuousAt.comp
        continuous_ofReal.continuousAt).continuousWithinAt
    have h := hc.preimage_isClosed_of_isClosed isClosed_Ici (isClosed_singleton (x := (0 : ℂ)))
    convert h using 1
    ext x
    simp only [S, mem_ofPred_eq, mem_inter_iff, mem_Ici, mem_preimage, mem_singleton_iff]
    constructor
    · intro hx; exact ⟨hδS x hx, hx.2⟩
    · intro hx; exact ⟨by linarith [hx.1], hx.2⟩
  have hmem := hclosed.csInf_mem hne hbdd
  refine ⟨hmem, fun x hx => ?_⟩
  by_cases hxδ : x < δ
  · exact hδ x ⟨hx.1, hxδ⟩
  by_contra hneg
  push Not at hneg
  push Not at hxδ
  have hcont : ContinuousOn (fun y : ℝ => (besselJ ν y).re) (Icc (δ / 2) x) :=
    (DLMF.Bessel.continuousOn_re_besselJ (ν : ℂ)).mono fun y hy =>
      show (0 : ℝ) < y by linarith [hy.1]
  have hpos : 0 < (besselJ ν (δ / 2 : ℝ)).re := hδ _ ⟨by linarith, by linarith⟩
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc' (by linarith : δ / 2 ≤ x) hcont
    ⟨hneg, hpos.le⟩
  have hy0' : (0 : ℝ) < y := by linarith [hy.1]
  have hyS : y ∈ S := ⟨hy0', by
    rw [DLMF.Bessel.besselJ_ofReal_eq_re ν y hy0']; simp only at hy0; rw [hy0, ofReal_zero]⟩
  have := csInf_le hbdd hyS
  linarith [hy.2, hx.2]


/-- `|J_ν(t)|, |B_ν(t)| ≤ C t^ν` on `(0, 1]` for real `ν`. -/
theorem exists_bound_besselJ_besselB (ν : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖besselJ ν t‖ ≤ C * t ^ ν ∧ ‖besselB ν t‖ ≤ C * t ^ ν := by
  obtain ⟨M, hM⟩ := exists_norm_besselJ_mul_le (ν : ℂ) (c := 1) one_pos
  obtain ⟨N, hN⟩ := exists_norm_besselJ_mul_le ((ν : ℂ) + 1) (c := 1) one_pos
  simp only [ofReal_one, one_mul, ofReal_re, add_re, one_re] at hM hN
  have hM0 : 0 ≤ M := by
    have := hM 1 ⟨one_pos, le_rfl⟩; rw [Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hN0 : 0 ≤ N := by
    have := hN 1 ⟨one_pos, le_rfl⟩; rw [Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  refine ⟨M + |ν| * M + N, by positivity, fun t ht => ⟨?_, ?_⟩⟩
  · have hp : 0 ≤ t ^ ν := Real.rpow_nonneg ht.1.le _
    calc ‖besselJ ν t‖ ≤ M * t ^ ν := hM t ht
      _ ≤ (M + |ν| * M + N) * t ^ ν := by gcongr; nlinarith [abs_nonneg ν]
  · have ht0 := ht.1
    have hp : 0 ≤ t ^ ν := Real.rpow_nonneg ht0.le _
    have h1 : t ^ (ν + 1) = t ^ ν * t := by rw [Real.rpow_add ht0, Real.rpow_one]
    have hJ := hM t ht
    have hJ1 := hN t ht
    rw [h1] at hJ1
    calc ‖besselB ν t‖ ≤ |ν| * ‖besselJ ν t‖ + t * ‖besselJ (ν + 1) t‖ := by
          unfold besselB
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_real, norm_real, Real.norm_eq_abs,
            Real.norm_of_nonneg ht0.le]
      _ ≤ |ν| * (M * t ^ ν) + t * (N * (t ^ ν * t)) := by gcongr
      _ ≤ (M + |ν| * M + N) * t ^ ν := by
          have ht1 : t ≤ 1 := ht.2
          have : t * (N * (t ^ ν * t)) ≤ N * t ^ ν := by
            have h2 : t * t ≤ 1 := by nlinarith
            calc t * (N * (t ^ ν * t)) = N * t ^ ν * (t * t) := by ring
              _ ≤ N * t ^ ν * 1 := by gcongr
              _ = N * t ^ ν := by ring
          nlinarith [mul_nonneg hM0 hp]

/-- `J_ν B_μ - B_ν J_μ → 0` at `0⁺` for real `ν + μ > 0`. -/
theorem tendsto_besselW_zero {ν μ : ℝ} (h : 0 < ν + μ) :
    Tendsto (fun x : ℝ => besselW ν μ x) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_besselJ_besselB ν
  obtain ⟨D, hD0, hD⟩ := exists_bound_besselJ_besselB μ
  have hlim : Tendsto (fun t : ℝ => 2 * C * D * t ^ (ν + μ)) (𝓝[>] 0) (𝓝 0) := by
    have h0 := (Real.continuousAt_rpow_const 0 (ν + μ) (Or.inr h.le)).tendsto
    rw [Real.zero_rpow h.ne'] at h0
    have := (h0.const_mul (2 * C * D)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  obtain ⟨h1, h2⟩ := hC t ht
  obtain ⟨h3, h4⟩ := hD t ht
  have hp := Real.rpow_nonneg ht.1.le ν
  have hq := Real.rpow_nonneg ht.1.le μ
  rw [Real.rpow_add ht.1]
  unfold besselW
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  calc ‖besselJ ν t‖ * ‖besselB μ t‖ + ‖besselB ν t‖ * ‖besselJ μ t‖
      ≤ C * t ^ ν * (D * t ^ μ) + C * t ^ ν * (D * t ^ μ) := by gcongr
    _ = 2 * C * D * (t ^ ν * t ^ μ) := by ring


/-- Sturm comparison for the first zeros: for real `0 ≤ ν < μ`, `j_{ν,1} < j_{μ,1}`. -/
theorem besselJ_first_zero_lt {ν μ : ℝ} (hν : 0 ≤ ν) (hνμ : ν < μ) :
    sInf {x : ℝ | 0 < x ∧ besselJ ν x = 0} < sInf {x : ℝ | 0 < x ∧ besselJ μ x = 0} := by
  obtain ⟨hmν, hposν⟩ := sInf_besselJ_zeros_spec (ν := ν) (by linarith)
  obtain ⟨hmμ, hposμ⟩ := sInf_besselJ_zeros_spec (ν := μ) (by linarith)
  set jν := sInf {x : ℝ | 0 < x ∧ besselJ ν x = 0}
  set J := sInf {x : ℝ | 0 < x ∧ besselJ μ x = 0}
  by_contra hle
  push Not at hle
  have hJ0 : 0 < J := hmμ.1
  set w : ℝ → ℝ := fun x => (besselW ν μ x).re with hwdef
  have hw' : ∀ x : ℝ, 0 < x → HasDerivAt w
      ((μ ^ 2 - ν ^ 2) / x * ((besselJ ν x).re * (besselJ μ x).re)) x := by
    intro x hx
    have hs : (x : ℂ) ∈ slitPlane := Or.inl (by simpa using hx)
    refine (hasDerivAt_besselW ν μ hs).real_of_complex.congr_deriv ?_
    rw [besselJ_ofReal_eq_re ν x hx, besselJ_ofReal_eq_re μ x hx]
    rw [show ((μ : ℂ) ^ 2 - (ν : ℂ) ^ 2) / (x : ℂ) * ((besselJ ν x).re : ℂ) *
        ((besselJ μ x).re : ℂ) = (((μ ^ 2 - ν ^ 2) / x * ((besselJ ν x).re * (besselJ μ x).re) :
          ℝ) : ℂ) by push_cast; ring, ofReal_re]
    simp only [ofReal_re]
  have hmono : StrictMonoOn w (Ioc 0 J) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioc 0 J) ?_ ?_
    · intro x hx; exact (hw' x hx.1).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(hw' x hx.1).deriv]
      have h1 : 0 < (besselJ ν x).re := hposν x ⟨hx.1, lt_of_lt_of_le hx.2 hle⟩
      have h2 : 0 < (besselJ μ x).re := hposμ x hx
      have h3 : 0 < μ ^ 2 - ν ^ 2 := by nlinarith
      exact mul_pos (div_pos h3 hx.1) (mul_pos h1 h2)
  have hwlim : Tendsto w (𝓝[>] 0) (𝓝 0) := by
    have := (continuous_re.tendsto 0).comp (tendsto_besselW_zero (ν := ν) (μ := μ) (by linarith))
    exact this
  have hhalf : 0 ≤ w (J / 2) := by
    refine le_of_tendsto hwlim ?_
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < J / 2 by linarith), self_mem_nhdsWithin]
      with x hx hx0
    exact (hmono.le_iff_le ⟨hx.1, hx.2.trans (by linarith)⟩ ⟨by linarith, by linarith⟩).mpr hx.2
  have hwJ : 0 < w J := lt_of_le_of_lt hhalf
    (hmono ⟨by linarith, by linarith⟩ ⟨hJ0, le_rfl⟩ (by linarith))
  have hfμJ : besselJ μ J = 0 := hmμ.2
  have hwJ' : w J = (besselJ ν J).re * (besselB μ J).re := by
    simp only [hwdef, besselW, hfμJ, mul_zero, sub_zero]
    rw [besselJ_ofReal_eq_re ν J hJ0, re_ofReal_mul, ofReal_re]
  have hfνJ : 0 ≤ (besselJ ν J).re := by
    rcases lt_or_eq_of_le hle with h | h
    · exact (hposν J ⟨hJ0, h⟩).le
    · rw [h, hmν.2, zero_re]
  have hb : 0 < (besselB μ J).re := by
    rw [hwJ'] at hwJ
    rcases lt_or_eq_of_le hfνJ with h | h
    · exact pos_of_mul_pos_right hwJ h.le
    · rw [← h, zero_mul] at hwJ; exact absurd hwJ (lt_irrefl _)
  have hs : (J : ℂ) ∈ slitPlane := Or.inl (by simpa using hJ0)
  have hd := (hasDerivAt_besselJ_B μ hs).real_of_complex
  rw [div_ofReal_re] at hd
  have hslope := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).1
  have hev : ∀ᶠ x in 𝓝[<] J, 0 < slope (fun x : ℝ => (besselJ μ x).re) J x :=
    hslope.eventually (lt_mem_nhds (div_pos hb hJ0))
  obtain ⟨x, hx1, hx2⟩ := (hev.and (Ioo_mem_nhdsLT hJ0)).exists
  rw [slope_def_field, hfμJ, zero_re, sub_zero] at hx1
  have hfx := hposμ x hx2
  have hneg : (besselJ μ x).re / (x - J) < 0 := div_neg_of_pos_of_neg hfx (by linarith [hx2.2])
  linarith

/-- The first positive Bessel zero is strictly increasing with the nonnegative order. -/
theorem besselJ_first_positive_zero_strictMono :
    StrictMonoOn (fun ν : ℝ => sInf {x : ℝ | 0 < x ∧ besselJ ν x = 0}) (Set.Ici 0) :=
  fun _ hν _ _ hlt => besselJ_first_zero_lt hν hlt

end DLMF.Bessel

end
