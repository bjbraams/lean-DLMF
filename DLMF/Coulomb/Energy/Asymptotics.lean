/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.Energy.Basic

/-!
# Coulomb functions `f`, `h`, `s`, `c`: large `|r|` (DLMF §33.21)

DLMF §33.21(i) describes how the limiting forms of `f`, `h`, `s`, `c` as `r → ±∞` follow from
the connection formulas of §33.16 and the limiting forms of `F_ℓ`, `G_ℓ` (33.10.1), of the
Whittaker functions `ζ_ℓ`, `ξ_ℓ` (33.21.1–33.21.2, acquired here) and of the Bessel functions
(§§10.7(ii), 10.30(ii)). §33.21(ii) cites Curtis (1964a, §6) for asymptotic expansions. Checked
numerically (mpmath, 40 digits, `ν = 2.3`, `ℓ = 1`, `|r|` up to 300); the convergence of `ξ_ℓ`
requires the principal branch `ph(e^{iπ} 2r/ν) = π` built into `coulombXi`.
-/

@[expose] public section

open Complex Filter Asymptotics
open scoped Real Topology

noncomputable section

namespace DLMF.Coulomb

/-- **DLMF 33.21.1**: for `ν > 0`, as `r → ∞`, `ζ_ℓ(ν,r) ~ e^{-r/ν} (2r/ν)^ν` and
`ξ_ℓ(ν,r) ~ e^{r/ν} (2r/ν)^{-ν}`. -/
@[dlmf 33.21.E1]
theorem coulombZeta_coulombXi_isEquivalent_atTop (ℓ : ℕ) {ν : ℝ} (hν : 0 < ν) :
    (fun r : ℝ => coulombZeta ℓ ν r) ~[atTop]
        (fun r : ℝ => ((Real.exp (-r / ν) * (2 * r / ν) ^ ν : ℝ) : ℂ)) ∧
      (fun r : ℝ => coulombXi ℓ ν r) ~[atTop]
        (fun r : ℝ => Real.exp (r / ν) * (2 * r / ν) ^ (-ν)) := by
  sorry

/-- **DLMF 33.21.2**: for `ν > 0`, as `r → -∞`, `ζ_ℓ(-ν,r) ~ e^{r/ν} (-2r/ν)^{-ν}` and
`ξ_ℓ(-ν,r) ~ e^{-r/ν} (-2r/ν)^ν`. -/
@[dlmf 33.21.E2]
theorem coulombZeta_coulombXi_isEquivalent_atBot (ℓ : ℕ) {ν : ℝ} (hν : 0 < ν) :
    (fun r : ℝ => coulombZeta ℓ (-ν) r) ~[atBot]
        (fun r : ℝ => ((Real.exp (r / ν) * (-2 * r / ν) ^ (-ν) : ℝ) : ℂ)) ∧
      (fun r : ℝ => coulombXi ℓ (-ν) r) ~[atBot]
        (fun r : ℝ => Real.exp (-r / ν) * (-2 * r / ν) ^ ν) := by
  sorry

end DLMF.Coulomb
