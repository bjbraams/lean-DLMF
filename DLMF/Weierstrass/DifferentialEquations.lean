/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.EllipticFunctionsAndInvariants

/-!
# Differential equations for `℘` (DLMF §23.3(ii))

The first-order equation 23.3.10 is Mathlib's `PeriodPair.derivWeierstrassP_sq` (pointer in
`MathlibCoverage`). Here the factored form 23.3.11 and the higher-order equations 23.3.12–13
are stated for `z ∉ 𝕃`. Derivatives are Lean's `deriv`; Mathlib's `deriv_weierstrassP`
identifies `deriv ℘` with `℘'` everywhere (with junk values on the lattice).
-/

@[expose] public section

open Complex PeriodPair

noncomputable section

namespace DLMF.Weierstrass

namespace HalfPeriods

variable (H : HalfPeriods)

/-- DLMF 23.3.11: `℘'(z)² = 4(℘(z) - e₁)(℘(z) - e₂)(℘(z) - e₃)` for `z ∉ 𝕃`. -/
@[dlmf 23.3.E11]
theorem derivWeierstrassP_sq_eq_prod {z : ℂ} (hz : z ∉ H.lattice) :
    H.derivWeierstrassP z ^ 2 =
      4 * (H.weierstrassP z - H.e 1) * (H.weierstrassP z - H.e 2) * (H.weierstrassP z - H.e 3) := by
  rw [← H.cubic_eq_mul]
  exact H.periodPair.derivWeierstrassP_sq z hz

end HalfPeriods

/-- `℘'` does not vanish identically off the lattice. -/
lemma p23R1_exists_derivWeierstrassP_ne_zero (L : PeriodPair) :
    ¬ ∀ w ∈ (L.latticeᶜ : Set ℂ), ℘'[L] w = 0 := by
  intro h
  have hU : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have hD : ∀ w ∈ (L.latticeᶜ : Set ℂ), HasDerivAt ℘[L] 0 w := by
    intro w hw
    have := (L.differentiableOn_weierstrassP w hw).differentiableAt (hU.mem_nhds hw)
    simpa [h w hw] using this.hasDerivAt
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, z₀ ∉ L.lattice := ⟨_, L.ω₁_div_two_notMem_lattice⟩
  have hc : ∀ w ∈ (L.latticeᶜ : Set ℂ), ℘[L] w = ℘[L] z₀ := fun w hw =>
    hU.is_const_of_deriv_eq_zero (wp23_isPreconnected_compl_lattice L)
      (fun z hz => (hD z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hD z hz).deriv) hw hz₀
  have hev : ℘[L] =ᶠ[nhdsWithin 0 {0}ᶜ] fun _ ↦ ℘[L] z₀ := by
    filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      self_mem_nhdsWithin] with w hw hw0
    exact hc w fun hl => hw ⟨hl, hw0⟩
  have h1 := L.order_weierstrassP 0 (zero_mem _)
  rw [meromorphicOrderAt_congr hev] at h1
  classical
  rw [meromorphicOrderAt_const] at h1
  split_ifs at h1 <;> revert h1 <;> decide

/-- DLMF 23.3.12: `℘''(z) = 6℘(z)² - g₂/2` for `z ∉ 𝕃`. -/
@[dlmf 23.3.E12]
theorem deriv_derivWeierstrassP (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 := by
  set U : Set ℂ := (L.latticeᶜ : Set ℂ)
  have hU : IsOpen U := L.isClosed_lattice.isOpen_compl
  have hP : AnalyticOnNhd ℂ ℘[L] U := L.analyticOnNhd_weierstrassP
  have hP' : AnalyticOnNhd ℂ ℘'[L] U := L.analyticOnNhd_derivWeierstrassP
  have hP'' : AnalyticOnNhd ℂ (deriv ℘'[L]) U := hP'.deriv
  have hkey : ∀ w ∈ U, ℘'[L] w * (deriv ℘'[L] w - (6 * ℘[L] w ^ 2 - L.g₂ / 2)) = 0 := by
    intro w hw
    have hd : HasDerivAt ℘[L] (℘'[L] w) w := by
      have := (hP w hw).differentiableAt
      simpa using this.hasDerivAt
    have hd' : HasDerivAt ℘'[L] (deriv ℘'[L] w) w := (hP' w hw).differentiableAt.hasDerivAt
    have hev : (fun x ↦ ℘'[L] x ^ 2) =ᶠ[nhds w]
        fun x ↦ 4 * ℘[L] x ^ 3 - L.g₂ * ℘[L] x - L.g₃ :=
      Filter.eventually_of_mem (hU.mem_nhds hw) fun x hx ↦ L.derivWeierstrassP_sq x hx
    have h1 : HasDerivAt (fun x ↦ ℘'[L] x ^ 2) (2 * ℘'[L] w * deriv ℘'[L] w) w := by
      convert hd'.fun_pow 2 using 1; push_cast; ring
    have h2 : HasDerivAt (fun x ↦ 4 * ℘[L] x ^ 3 - L.g₂ * ℘[L] x - L.g₃)
        ((12 * ℘[L] w ^ 2 - L.g₂) * ℘'[L] w) w := by
      convert (((hd.fun_pow 3).const_mul 4).sub (hd.const_mul L.g₂)).sub_const L.g₃ using 1
      push_cast; ring
    have := (hev.hasDerivAt_iff.mpr h2).unique h1
    linear_combination (-1/2 : ℂ) * this
  by_contra hne
  have hg : AnalyticAt ℂ (fun w ↦ deriv ℘'[L] w - (6 * ℘[L] w ^ 2 - L.g₂ / 2)) z :=
    (hP'' z hz).sub ((analyticAt_const.mul ((hP z hz).pow 2)).sub analyticAt_const)
  have hgne : ∀ᶠ w in nhds z, deriv ℘'[L] w - (6 * ℘[L] w ^ 2 - L.g₂ / 2) ≠ 0 :=
    hg.continuousAt.eventually_ne (sub_ne_zero.mpr hne)
  have hzero : ℘'[L] =ᶠ[nhds z] 0 := by
    filter_upwards [hgne, hU.mem_nhds hz] with w hw hwU
    simpa [hw] using hkey w hwU
  exact p23R1_exists_derivWeierstrassP_ne_zero L fun w hw =>
    hP'.eqOn_zero_of_preconnected_of_eventuallyEq_zero (wp23_isPreconnected_compl_lattice L)
      hz hzero hw

/-- DLMF 23.3.13: `℘'''(z) = 12℘(z)℘'(z)` for `z ∉ 𝕃` (derived from 23.3.12). -/
@[dlmf 23.3.E13]
theorem deriv_deriv_derivWeierstrassP (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    deriv (deriv ℘'[L]) z = 12 * ℘[L] z * ℘'[L] z := by
  have hU : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have hev : deriv ℘'[L] =ᶠ[nhds z] fun w ↦ 6 * ℘[L] w ^ 2 - L.g₂ / 2 :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw ↦ deriv_derivWeierstrassP L hw
  rw [hev.deriv_eq]
  have hd : HasDerivAt ℘[L] (℘'[L] z) z := by
    have := (L.differentiableOn_weierstrassP z hz).differentiableAt (hU.mem_nhds hz)
    simpa using this.hasDerivAt
  have : HasDerivAt (fun w ↦ 6 * ℘[L] w ^ 2 - L.g₂ / 2) (12 * ℘[L] z * ℘'[L] z) z := by
    convert ((hd.fun_pow 2).const_mul 6).sub_const (L.g₂ / 2) using 1
    push_cast; ring
  exact this.deriv

end DLMF.Weierstrass
