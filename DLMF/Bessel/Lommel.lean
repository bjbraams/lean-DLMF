/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.SecondKind

/-!
# Lommel's integral and Fourier–Bessel orthogonality (DLMF 10.22.5, 10.22.37)

The function `F(t) = t (β J_ν(αt) J_{ν-1}(βt) - α J_{ν-1}(αt) J_ν(βt))` has derivative
`(α² - β²) t J_ν(αt) J_ν(βt)`. For `re ν > -1` the leading terms of the two products cancel at
`t = 0`, so `F(t) = O(t^{2 re ν + 2})` and `F(0⁺) = 0`; the integrand is `O(t^{2 re ν + 1})` and
hence integrable. The fundamental theorem of calculus then gives Lommel's integral on `[0, 1]`,
and orthogonality of `t ↦ J_ν(j t)` over distinct positive zeros `j` of `J_ν`. The normalization
`∫₀¹ t J_ν(jt)² dt = J_{ν+1}(j)²/2` uses the primitive
`t²(J_{ν+1}(jt)² + J_ν(jt)²)/2 - (ν/j) t J_ν(jt) J_{ν+1}(jt)`, whose `ν²` terms have cancelled so
that it vanishes at `0⁺` for every `re ν > -1`.
-/

@[expose] public section

open Complex Filter Set
open scoped Real Topology

noncomputable section

namespace DLMF.Bessel

/-- Chain rule for `s ↦ J_μ(cs)` in the form `J_μ' = -(μ/z) J_μ + J_{μ-1}`. -/
theorem hasDerivAt_besselJ_mul (μ : ℂ) {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => besselJ μ (c * s))
      (c * (-(μ / (c * t)) * besselJ μ (c * t) + besselJ (μ - 1) (c * t))) t := by
  have hs : (c : ℂ) * t ∈ slitPlane := by
    rw [← ofReal_mul]; exact Or.inl (by simpa using mul_pos hc ht)
  have h := (hasDerivAt_besselJ' (ν := μ) hs).comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).const_mul (c : ℂ))
  simpa [mul_comm] using h.comp_ofReal

/-- Chain rule for `s ↦ J_μ(cs)` in the form `J_μ' = (μ/z) J_μ - J_{μ+1}`. -/
theorem hasDerivAt_besselJ_mul' (μ : ℂ) {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => besselJ μ (c * s))
      (c * (μ / (c * t) * besselJ μ (c * t) - besselJ (μ + 1) (c * t))) t := by
  have hs : (c : ℂ) * t ∈ slitPlane := by
    rw [← ofReal_mul]; exact Or.inl (by simpa using mul_pos hc ht)
  have h := (hasDerivAt_besselJ (ν := μ) hs).comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).const_mul (c : ℂ))
  simpa [mul_comm] using h.comp_ofReal

/-- The Lommel primitive `t (β J_ν(αt) J_{ν-1}(βt) - α J_{ν-1}(αt) J_ν(βt))` has derivative
`(α² - β²) t J_ν(αt) J_ν(βt)`. -/
theorem hasDerivAt_lommel (ν : ℂ) {α β t : ℝ} (hα : 0 < α) (hβ : 0 < β) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * (β * besselJ ν (α * s) * besselJ (ν - 1) (β * s) -
        α * besselJ (ν - 1) (α * s) * besselJ ν (β * s)))
      (((α : ℂ) ^ 2 - (β : ℂ) ^ 2) * t * besselJ ν (α * t) * besselJ ν (β * t)) t := by
  have hA := hasDerivAt_besselJ_mul ν hα ht
  have hB := hasDerivAt_besselJ_mul' (ν - 1) hβ ht
  have hC := hasDerivAt_besselJ_mul' (ν - 1) hα ht
  rw [sub_add_cancel] at hB hC
  have hD := hasDerivAt_besselJ_mul ν hβ ht
  have h : HasDerivAt (fun s : ℝ => (s : ℂ) * (β * besselJ ν (α * s) * besselJ (ν - 1) (β * s) -
        α * besselJ (ν - 1) (α * s) * besselJ ν (β * s))) _ t :=
    (hasDerivAt_id (t : ℝ)).ofReal_comp.mul
      ((((hA.const_mul (β : ℂ)).mul hB)).sub ((hC.const_mul (α : ℂ)).mul hD))
  convert h using 1
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hα' : (α : ℂ) ≠ 0 := ofReal_ne_zero.mpr hα.ne'
  have hβ' : (β : ℂ) ≠ 0 := ofReal_ne_zero.mpr hβ.ne'
  simp only [id, ofReal_one]
  field_simp
  ring

/-- The entire factor `₀F̃₁(μ+1; -s/4)` of `J_μ`. -/
noncomputable def besselJCore (μ s : ℂ) : ℂ :=
  regularizedHGFun (∅ : Multiset ℂ) {μ + 1} (-(s / 4))

/-- The core is entire. -/
theorem differentiable_besselJCore (μ : ℂ) : Differentiable ℂ (besselJCore μ) := by
  intro s
  have h := analyticAt_regularizedHGFun_zero (b := {μ + 1}) (-(s / 4))
  rw [← Multiset.empty_eq_zero] at h
  exact h.differentiableAt.comp s (by fun_prop)

/-- `J_μ(ct) = (ct/2)^μ · core(c²t²)` for real `c, t`. -/
theorem besselJ_ofReal_mul {μ : ℂ} {c t : ℝ} :
    besselJ μ (c * t) =
      (((c * t / 2 : ℝ)) : ℂ) ^ μ * besselJCore μ ((c : ℂ) ^ 2 * (t : ℂ) ^ 2) := by
  rw [besselJ_eq_regularized, besselJCore]
  push_cast
  ring_nf

open Asymptotics in
/-- The Lommel primitive vanishes at `0⁺` when `re ν > -1`: it is `O(t^{2 re ν + 2})`, since the
leading terms of its two products cancel. -/
theorem tendsto_lommel_zero {ν : ℂ} (hν : -1 < ν.re) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (fun s : ℝ => (s : ℂ) * (β * besselJ ν (α * s) * besselJ (ν - 1) (β * s) -
        α * besselJ (ν - 1) (α * s) * besselJ ν (β * s))) (𝓝[>] 0) (𝓝 0) := by
  set r := ν.re
  set E : ℂ → ℂ := fun s =>
    besselJCore ν ((α : ℂ) ^ 2 * s) * besselJCore (ν - 1) ((β : ℂ) ^ 2 * s) -
    besselJCore (ν - 1) ((α : ℂ) ^ 2 * s) * besselJCore ν ((β : ℂ) ^ 2 * s) with hEdef
  have hEd : Differentiable ℂ E := by
    have h1 := differentiable_besselJCore ν
    have h2 := differentiable_besselJCore (ν - 1)
    intro s
    simp only [hEdef]
    fun_prop
  have hEO : E =O[𝓝 0] (fun s : ℂ => s) := by
    have h := (hEd 0).hasDerivAt.isBigO_sub
    have h0 : E 0 = 0 := by simp only [hEdef, mul_zero]; ring
    simpa [h0] using h
  have ht2 : Tendsto (fun t : ℝ => (t : ℂ) ^ 2) (𝓝[>] 0) (𝓝 0) :=
    ((continuous_ofReal.pow 2).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
  have hD : (fun t : ℝ => E ((t : ℂ) ^ 2)) =O[𝓝[>] 0] (fun t : ℝ => t ^ (2 : ℝ)) :=
    (hEO.comp_tendsto ht2).trans (IsBigO.of_bound 1 (Eventually.of_forall fun t => by
      simp))
  set K := α * β / 2 * (α / 2) ^ (r - 1) * (β / 2) ^ (r - 1)
  set P : ℝ → ℂ := fun t => (t : ℂ) * (α * β * t / 2) * (((α * t / 2 : ℝ)) : ℂ) ^ (ν - 1) *
    (((β * t / 2 : ℝ)) : ℂ) ^ (ν - 1) with hPdef
  have hP : P =O[𝓝[>] 0] (fun t : ℝ => t ^ (2 * r)) := by
    refine IsBigO.of_bound K ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht : (0 : ℝ) < t := ht
    simp only [hPdef, norm_mul, norm_real, Real.norm_eq_abs]
    rw [norm_cpow_eq_rpow_re_of_pos (by positivity), norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have hn : ‖(α : ℂ) * β * t / 2‖ = α * β * t / 2 := by
      rw [show (α : ℂ) * β * t / 2 = ((α * β * t / 2 : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_of_nonneg (by positivity)]
    have hre : (ν - 1).re = r - 1 := by simp [r]
    have e1 : (α * t / 2) ^ (r - 1) = (α / 2) ^ (r - 1) * t ^ (r - 1) := by
      rw [show α * t / 2 = (α / 2) * t by ring, Real.mul_rpow (by positivity) ht.le]
    have e2 : (β * t / 2) ^ (r - 1) = (β / 2) ^ (r - 1) * t ^ (r - 1) := by
      rw [show β * t / 2 = (β / 2) * t by ring, Real.mul_rpow (by positivity) ht.le]
    have e3 : t ^ (2 * r) = t * t * (t ^ (r - 1) * t ^ (r - 1)) := by
      rw [← Real.rpow_add ht, show 2 * r = (r - 1 + (r - 1)) + 1 + 1 by ring,
        Real.rpow_add ht, Real.rpow_add ht, Real.rpow_one]
      ring
    rw [abs_of_pos ht, abs_of_pos (Real.rpow_pos_of_pos ht _), hn, hre, e1, e2, e3]
    apply le_of_eq
    simp only [K]
    ring
  have hF : (fun s : ℝ => (s : ℂ) * (β * besselJ ν (α * s) * besselJ (ν - 1) (β * s) -
        α * besselJ (ν - 1) (α * s) * besselJ ν (β * s))) =ᶠ[𝓝[>] 0]
      fun t => P t * E ((t : ℂ) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht : (0 : ℝ) < t := ht
    have hxa : (((α * t / 2 : ℝ)) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
    have hxb : (((β * t / 2 : ℝ)) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
    simp only [besselJ_ofReal_mul, hPdef, hEdef, cpow_sub _ _ hxa, cpow_sub _ _ hxb, cpow_one]
    generalize (((α * t / 2 : ℝ)) : ℂ) ^ ν = Ua
    generalize (((β * t / 2 : ℝ)) : ℂ) ^ ν = Ub
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have hα' : (α : ℂ) ≠ 0 := ofReal_ne_zero.mpr hα.ne'
    have hβ' : (β : ℂ) ≠ 0 := ofReal_ne_zero.mpr hβ.ne'
    push_cast
    field_simp
  have hO := ((hP.mul hD).congr' hF.symm (Eventually.of_forall fun t => rfl))
  have hO' : (fun s : ℝ => (s : ℂ) * (β * besselJ ν (α * s) * besselJ (ν - 1) (β * s) -
        α * besselJ (ν - 1) (α * s) * besselJ ν (β * s))) =O[𝓝[>] 0]
      (fun t : ℝ => t ^ (2 * r + 2)) := by
    refine hO.congr' (Eventually.of_forall fun t => rfl) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [Real.rpow_add ht]
  refine hO'.trans_tendsto ?_
  have h := (Real.continuousAt_rpow_const 0 (2 * r + 2) (Or.inr (by linarith))).tendsto
  rw [Real.zero_rpow (by linarith)] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- `s ↦ J_μ(cs)` is continuous at positive points. -/
theorem continuousAt_besselJ_mul (μ : ℂ) {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    ContinuousAt (fun s : ℝ => besselJ μ (c * s)) t :=
  (hasDerivAt_besselJ_mul μ hc ht).continuousAt

/-- `|J_ν(ct)| ≤ M t^{re ν}` on `(0, 1]`. -/
theorem exists_norm_besselJ_mul_le (ν : ℂ) {c : ℝ} (hc : 0 < c) :
    ∃ M, ∀ t ∈ Ioc (0 : ℝ) 1, ‖besselJ ν (c * t)‖ ≤ M * t ^ ν.re := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    (f := fun t : ℝ => besselJCore ν ((c : ℂ) ^ 2 * (t : ℂ) ^ 2))
    ((differentiable_besselJCore ν).continuous.comp (by fun_prop)).continuousOn
  refine ⟨(c / 2) ^ ν.re * M, fun t ht => ?_⟩
  rw [besselJ_ofReal_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos (by positivity [ht.1]),
    show c * t / 2 = (c / 2) * t by ring, Real.mul_rpow (by positivity) ht.1.le]
  have h := hM t (Ioc_subset_Icc_self ht)
  have h1 : 0 ≤ (c / 2) ^ ν.re := by positivity
  have h2 : 0 ≤ t ^ ν.re := Real.rpow_nonneg ht.1.le _
  calc (c / 2) ^ ν.re * t ^ ν.re * ‖besselJCore ν ((c : ℂ) ^ 2 * (t : ℂ) ^ 2)‖
      ≤ (c / 2) ^ ν.re * t ^ ν.re * M := by gcongr
    _ = (c / 2) ^ ν.re * M * t ^ ν.re := by ring

open MeasureTheory in
/-- The Lommel integrand is integrable on `[0, 1]` for `re ν > -1`. -/
theorem intervalIntegrable_lommel {ν : ℂ} (hν : -1 < ν.re) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) * besselJ ν (α * t) * besselJ ν (β * t))
      volume 0 1 := by
  obtain ⟨Ma, hMa⟩ := exists_norm_besselJ_mul_le ν hα
  obtain ⟨Mb, hMb⟩ := exists_norm_besselJ_mul_le ν hβ
  have hg := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
    (by linarith : -1 < 2 * ν.re + 1)).const_mul (Ma * Mb)
  refine hg.mono_fun' ?_ ?_
  · rw [uIoc_of_le zero_le_one]
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioc
    exact ((continuous_ofReal.continuousAt.mul (continuousAt_besselJ_mul ν hα ht.1)).mul
      (continuousAt_besselJ_mul ν hβ ht.1)).continuousWithinAt
  · rw [uIoc_of_le zero_le_one]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have ha := hMa t ht
    have hb := hMb t ht
    have h0 : 0 ≤ ‖besselJ ν (α * t)‖ := norm_nonneg _
    have hr : 0 ≤ t ^ ν.re := Real.rpow_nonneg ht.1.le _
    have he : t ^ (2 * ν.re + 1) = t * (t ^ ν.re * t ^ ν.re) := by
      rw [← Real.rpow_add ht.1, Real.rpow_add ht.1, Real.rpow_one]; ring_nf
    simp only
    rw [norm_mul, norm_mul, norm_real, Real.norm_of_nonneg ht.1.le, he]
    have hMa0 : 0 ≤ Ma * t ^ ν.re := le_trans h0 ha
    calc t * ‖besselJ ν (α * t)‖ * ‖besselJ ν (β * t)‖
        ≤ t * (Ma * t ^ ν.re) * (Mb * t ^ ν.re) := by
          have := ht.1.le; gcongr
      _ = Ma * Mb * (t * (t ^ ν.re * t ^ ν.re)) := by ring

/-- **Lommel's integral** (DLMF 10.22.5 on `[0, 1]`): for `re ν > -1` and distinct `α, β > 0`,
`∫₀¹ t J_ν(αt) J_ν(βt) dt = (β J_ν(α) J_{ν-1}(β) - α J_{ν-1}(α) J_ν(β)) / (α² - β²)`. -/
@[dlmf 10.22.E5]
theorem integral_mul_besselJ_mul_besselJ {ν : ℂ} (hν : -1 < ν.re) {α β : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (hαβ : α ≠ β) :
    ∫ t in (0 : ℝ)..1, (t : ℂ) * besselJ ν (α * t) * besselJ ν (β * t) =
      (β * besselJ ν α * besselJ (ν - 1) β - α * besselJ (ν - 1) α * besselJ ν β) /
        ((α : ℂ) ^ 2 - (β : ℂ) ^ 2) := by
  set F : ℝ → ℂ := fun s => (s : ℂ) * (β * besselJ ν (α * s) * besselJ (ν - 1) (β * s) -
    α * besselJ (ν - 1) (α * s) * besselJ ν (β * s)) with hFdef
  have hab : (α : ℂ) ^ 2 - (β : ℂ) ^ 2 ≠ 0 := by
    rw [← ofReal_pow, ← ofReal_pow, ← ofReal_sub, ofReal_ne_zero, sub_ne_zero]
    intro h
    exact hαβ (by nlinarith [sq_nonneg (α - β), sq_nonneg (α + β)])
  have hcont : ContinuousOn F (Icc 0 1) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · subst h0
      have hlim := tendsto_lommel_zero hν hα hβ
      have hF0 : F 0 = 0 := by simp [hFdef]
      refine ContinuousWithinAt.mono ?_ (Icc_subset_Ici_self)
      rw [← continuousWithinAt_Ioi_iff_Ici]
      rw [ContinuousWithinAt, hF0]
      exact hlim
    · exact (hasDerivAt_lommel ν hα hβ hpos).continuousAt.continuousWithinAt
  have hint := (intervalIntegrable_lommel hν hα hβ).const_mul ((α : ℂ) ^ 2 - (β : ℂ) ^ 2)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont
    (fun t ht => by
      have h := hasDerivAt_lommel ν hα hβ ht.1
      convert h using 1
      ring) hint
  rw [intervalIntegral.integral_const_mul] at hftc
  rw [eq_div_iff hab, mul_comm, hftc]
  simp [hFdef]

/-- **Orthogonality of Fourier–Bessel functions** (DLMF 10.22.37, `ℓ ≠ m`): for distinct positive
zeros `α, β` of `J_ν` with `re ν > -1`, `∫₀¹ t J_ν(αt) J_ν(βt) dt = 0`. -/
@[dlmf 10.22.E37]
theorem integral_besselJ_orthogonal {ν : ℂ} (hν : -1 < ν.re) {α β : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (hαβ : α ≠ β) (hzα : besselJ ν α = 0) (hzβ : besselJ ν β = 0) :
    ∫ t in (0 : ℝ)..1, (t : ℂ) * besselJ ν (α * t) * besselJ ν (β * t) = 0 := by
  rw [integral_mul_besselJ_mul_besselJ hν hα hβ hαβ, hzα, hzβ]
  simp

/-- The primitive `t²(J_{ν+1}(αt)² + J_ν(αt)²)/2 - (ν/α) t J_ν(αt) J_{ν+1}(αt)` of
`t J_ν(αt)²`. -/
def besselNormPrimitive (ν : ℂ) (α t : ℝ) : ℂ :=
  (t : ℂ) ^ 2 * (besselJ (ν + 1) (α * t) ^ 2 + besselJ ν (α * t) ^ 2) / 2 -
    ν / α * t * besselJ ν (α * t) * besselJ (ν + 1) (α * t)

/-- The primitive has derivative `t J_ν(αt)²`, by the recurrences for `J_ν'` and `J_{ν+1}'`. -/
theorem hasDerivAt_besselNormPrimitive (ν : ℂ) {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    HasDerivAt (besselNormPrimitive ν α) ((t : ℂ) * besselJ ν (α * t) ^ 2) t := by
  have hJ := hasDerivAt_besselJ_mul' ν hα ht
  have hK := hasDerivAt_besselJ_mul (ν + 1) hα ht
  rw [add_sub_cancel_right] at hK
  have hid : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have h := (((hid.pow 2).mul ((hK.pow 2).add (hJ.pow 2))).div_const 2).sub
    ((((hid.const_mul ((ν : ℂ) / α)).mul hJ).mul hK))
  refine h.congr_deriv ?_
  have hα' : (α : ℂ) ≠ 0 := ofReal_ne_zero.mpr hα.ne'
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  simp only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply]
  norm_num
  field_simp
  ring


/-- The primitive vanishes at `0⁺` for `re ν > -1`: it is `O(t^{2 re ν + 2})`. -/
theorem tendsto_besselNormPrimitive {ν : ℂ} (hν : -1 < ν.re) {α : ℝ} (hα : 0 < α) :
    Tendsto (besselNormPrimitive ν α) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M, hM⟩ := exists_norm_besselJ_mul_le ν hα
  obtain ⟨N, hN⟩ := exists_norm_besselJ_mul_le (ν + 1) hα
  set r := ν.re
  have hM0 : 0 ≤ M := by
    have := hM 1 ⟨one_pos, le_rfl⟩; rw [Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hN0 : 0 ≤ N := by
    have := hN 1 ⟨one_pos, le_rfl⟩; rw [Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  set K := (N ^ 2 + M ^ 2) / 2 + ‖ν‖ / α * M * N
  have hlim : Tendsto (fun t : ℝ => K * (t ^ (r + 1)) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (r + 1) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith)] at h
    have := ((h.pow 2).const_mul K).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have ht0 := ht.1
  have hJ := hM t ht
  have hJ1 := hN t ht
  have hre : (ν + 1).re = r + 1 := by simp [r]
  rw [hre, Real.rpow_add ht0, Real.rpow_one] at hJ1
  set p := t ^ r
  have hp : 0 ≤ p := Real.rpow_nonneg ht0.le _
  have htp : t ^ (r + 1) = t * p := by rw [Real.rpow_add ht0, Real.rpow_one, mul_comm]
  rw [htp]
  set A := ‖besselJ ν (α * t)‖
  set B := ‖besselJ (ν + 1) (α * t)‖
  have hnorm : ‖besselNormPrimitive ν α t‖ ≤ t ^ 2 * (B ^ 2 + A ^ 2) / 2 + ‖ν‖ / α * t * A * B := by
    unfold besselNormPrimitive
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_div, norm_mul, norm_pow, norm_real, Real.norm_of_nonneg ht0.le, Complex.norm_two]
      gcongr
      refine (norm_add_le _ _).trans ?_
      rw [norm_pow, norm_pow]
    · rw [norm_mul, norm_mul, norm_mul, norm_div, norm_real, norm_real,
        Real.norm_of_nonneg hα.le, Real.norm_of_nonneg ht0.le]
  refine hnorm.trans ?_
  have ht1 : t ≤ 1 := ht.2
  have hA : A ≤ M * p := hJ
  have hB : B ≤ N * (p * t) := hJ1
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have hνα : 0 ≤ ‖ν‖ / α := by positivity
  calc t ^ 2 * (B ^ 2 + A ^ 2) / 2 + ‖ν‖ / α * t * A * B
      ≤ t ^ 2 * ((N * (p * t)) ^ 2 + (M * p) ^ 2) / 2 + ‖ν‖ / α * t * (M * p) * (N * (p * t)) := by
        gcongr
    _ ≤ K * (t * p) ^ 2 := by
        simp only [K]
        have ht2 : t ^ 2 ≤ 1 := by nlinarith
        have : (N * (p * t)) ^ 2 ≤ (N * p) ^ 2 := by
          calc (N * (p * t)) ^ 2 = (N * p) ^ 2 * t ^ 2 := by ring
            _ ≤ (N * p) ^ 2 * 1 := by gcongr
            _ = (N * p) ^ 2 := by ring
        nlinarith [sq_nonneg (N * p), sq_nonneg (M * p), mul_nonneg hνα (mul_nonneg hM0 hN0),
          mul_nonneg (mul_nonneg hνα (mul_nonneg hM0 hN0)) (sq_nonneg (t * p)),
          sq_nonneg t, mul_nonneg (sq_nonneg t) (sq_nonneg p), ht0.le]


/-- **Normalization of Fourier–Bessel functions** (DLMF 10.22.37 with `ℓ = m`): if `α > 0` is a
zero of `J_ν` with `re ν > -1`, then `∫₀¹ t J_ν(αt)² dt = J_{ν+1}(α)²/2`. -/
@[dlmf 10.22.E37]
theorem integral_mul_besselJ_sq {ν : ℂ} (hν : -1 < ν.re) {α : ℝ} (hα : 0 < α)
    (hz : besselJ ν α = 0) :
    ∫ t in (0 : ℝ)..1, (t : ℂ) * besselJ ν (α * t) ^ 2 = besselJ (ν + 1) α ^ 2 / 2 := by
  have hcont : ContinuousOn (besselNormPrimitive ν α) (Icc 0 1) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · subst h0
      refine ContinuousWithinAt.mono ?_ Icc_subset_Ici_self
      rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
      have h0 : besselNormPrimitive ν α 0 = 0 := by simp [besselNormPrimitive]
      rw [h0]
      exact tendsto_besselNormPrimitive hν hα
    · exact (hasDerivAt_besselNormPrimitive ν hα hpos).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun t : ℝ => (t : ℂ) * besselJ ν (α * t) ^ 2)
      MeasureTheory.volume 0 1 := by
    refine (intervalIntegrable_lommel hν hα hα).congr ?_
    exact fun t _ => by ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont
    (fun t ht => hasDerivAt_besselNormPrimitive ν hα ht.1) hint]
  simp [besselNormPrimitive, hz]

/-- **Fourier–Bessel coefficients** (Temme §9.9, §10.3.1): for a finite combination
`f(t) = ∑ᵢ cᵢ J_ν(jᵢ t)` over distinct positive zeros `jᵢ` of `J_ν` with `re ν > -1`,
`∫₀¹ t J_ν(jₖ t) f(t) dt = cₖ J_{ν+1}(jₖ)²/2`. -/
theorem integral_mul_fourierBessel_sum {ι : Type*} {ν : ℂ} (hν : -1 < ν.re) (s : Finset ι)
    {j : ι → ℝ} (hj : ∀ i, 0 < j i) (hzero : ∀ i, besselJ ν (j i) = 0) (hinj : Set.InjOn j s)
    (c : ι → ℂ) {k : ι} (hk : k ∈ s) :
    ∫ t in (0 : ℝ)..1, (t : ℂ) * besselJ ν (j k * t) * ∑ i ∈ s, c i * besselJ ν (j i * t) =
      c k * besselJ (ν + 1) (j k) ^ 2 / 2 := by
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun i _ => by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (intervalIntegrable_lommel hν (hj k) (hj i)).const_mul (c i))]
  rw [Finset.sum_eq_single k]
  · have h := integral_mul_besselJ_sq hν (hj k) (hzero k)
    rw [show (fun t : ℝ => (t : ℂ) * besselJ ν (j k * t) * (c k * besselJ ν (j k * t))) =
      fun t : ℝ => c k * ((t : ℂ) * besselJ ν (j k * t) ^ 2) by funext t; ring,
      intervalIntegral.integral_const_mul, h]
    ring
  · intro i hi hik
    have hne : j k ≠ j i := fun h => hik (hinj hi hk h.symm)
    rw [show (fun t : ℝ => (t : ℂ) * besselJ ν (j k * t) * (c i * besselJ ν (j i * t))) =
      fun t : ℝ => c i * ((t : ℂ) * besselJ ν (j k * t) * besselJ ν (j i * t)) by
        funext t; ring,
      intervalIntegral.integral_const_mul,
      integral_besselJ_orthogonal hν (hj k) (hj i) hne (hzero k) (hzero i), mul_zero]
  · intro h; exact absurd hk h

end DLMF.Bessel
