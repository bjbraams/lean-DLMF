/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic

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

/-- DLMF 23.3.12: `℘''(z) = 6℘(z)² - g₂/2` for `z ∉ 𝕃`. -/
@[dlmf 23.3.E12]
theorem deriv_derivWeierstrassP (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 := by
  sorry

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
