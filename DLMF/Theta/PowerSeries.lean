/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Basic

/-!
# Theta functions: power series (DLMF §20.6)

The exponential power series 20.6.2–20.6.5 of `θⱼ(πz|τ)` about `z = 0`, with the lattice sums
`δ_{2j}, α_{2j}, β_{2j}, γ_{2j}` of 20.6.6–20.6.9. The lattice sums are defined as iterated sums,
inner over `m` and outer over `n` (the Eisenstein order of DLMF); for `2j ≥ 4` the order is
irrelevant (`thetaDelta_hasSum_lattice`), for `2j = 2` it matters. The power series are stated with
an explicit summability claim, so that Lean's convention `∑' = 0` for divergent series plays no
role.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic

/-- DLMF 20.6.6: `δ_k(τ) = ∑_n ∑'_m (m + nτ)^{-k}` (`(m,n) ≠ (0,0)`; DLMF writes `δ_{2j}`,
`k = 2j`).
Iterated sum, inner over `m`. -/
@[dlmf 20.6.E6]
def thetaDelta (k : ℕ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, ∑' m : ℤ, if m = 0 ∧ n = 0 then 0 else ((m : ℂ) + n * τ) ^ (-(k : ℤ))

/-- DLMF 20.6.7: `α_k(τ) = ∑_n ∑_m (m - 1/2 + nτ)^{-k}` (`k = 2j`). -/
@[dlmf 20.6.E7]
def thetaAlpha (k : ℕ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, ∑' m : ℤ, ((m : ℂ) - 1 / 2 + n * τ) ^ (-(k : ℤ))

/-- DLMF 20.6.8: `β_k(τ) = ∑_n ∑_m (m - 1/2 + (n - 1/2)τ)^{-k}` (`k = 2j`). -/
@[dlmf 20.6.E8]
def thetaBeta (k : ℕ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, ∑' m : ℤ, ((m : ℂ) - 1 / 2 + (n - 1 / 2) * τ) ^ (-(k : ℤ))

/-- DLMF 20.6.9: `γ_k(τ) = ∑_n ∑_m (m + (n - 1/2)τ)^{-k}` (`k = 2j`). -/
@[dlmf 20.6.E9]
def thetaGamma (k : ℕ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, ∑' m : ℤ, ((m : ℂ) + (n - 1 / 2) * τ) ^ (-(k : ℤ))

/-- DLMF 20.6.1: the radius `min_{(m,n) ≠ (0,0)} |z_{m,n}| = min |(m + nτ)π|`; the power series
20.6.2–20.6.5 hold for `|πz|` below it. -/
@[dlmf 20.6.E1]
def thetaLatticeMinNorm (τ : ℂ) : ℝ :=
  ⨅ p : {p : ℤ × ℤ // p ≠ 0}, ‖((p.1.1 : ℂ) + p.1.2 * τ) * π‖

/-- DLMF 20.6.2: for `|πz| < min |z_{m,n}|`,
`θ₁(πz|τ) = πz θ₁'(0|τ) exp(-∑_{j≥1} δ_{2j}(τ) z^{2j}/(2j))`. -/
@[dlmf 20.6.E2]
theorem jacobiThetaOneTau_powerSeries {τ z : ℂ} (hτ : 0 < τ.im)
    (hz : ‖π * z‖ < thetaLatticeMinNorm τ) :
    ∃ S : ℂ, HasSum (fun j : ℕ => thetaDelta (2 * (j + 1)) τ * z ^ (2 * (j + 1)) /
        (2 * (j + 1))) S ∧
      jacobiThetaOneTau (π * z) τ = π * z * jacobiThetaOneDerivNullTau τ * cexp (-S) := by
  sorry

/-- DLMF 20.6.3: for `|πz| < min |z_{m,n}|`,
`θ₂(πz|τ) = θ₂(0|τ) exp(-∑_{j≥1} α_{2j}(τ) z^{2j}/(2j))`. -/
@[dlmf 20.6.E3]
theorem jacobiThetaTwoTau_powerSeries {τ z : ℂ} (hτ : 0 < τ.im)
    (hz : ‖π * z‖ < thetaLatticeMinNorm τ) :
    ∃ S : ℂ, HasSum (fun j : ℕ => thetaAlpha (2 * (j + 1)) τ * z ^ (2 * (j + 1)) /
        (2 * (j + 1))) S ∧
      jacobiThetaTwoTau (π * z) τ = jacobiThetaTwoNullTau τ * cexp (-S) := by
  sorry

/-- DLMF 20.6.4: for `|πz| < min |z_{m,n}|`,
`θ₃(πz|τ) = θ₃(0|τ) exp(-∑_{j≥1} β_{2j}(τ) z^{2j}/(2j))`. -/
@[dlmf 20.6.E4]
theorem jacobiThetaThreeTau_powerSeries {τ z : ℂ} (hτ : 0 < τ.im)
    (hz : ‖π * z‖ < thetaLatticeMinNorm τ) :
    ∃ S : ℂ, HasSum (fun j : ℕ => thetaBeta (2 * (j + 1)) τ * z ^ (2 * (j + 1)) /
        (2 * (j + 1))) S ∧
      jacobiThetaThreeTau (π * z) τ = jacobiThetaThreeNullTau τ * cexp (-S) := by
  sorry

/-- DLMF 20.6.5: for `|πz| < min |z_{m,n}|`,
`θ₄(πz|τ) = θ₄(0|τ) exp(-∑_{j≥1} γ_{2j}(τ) z^{2j}/(2j))`. -/
@[dlmf 20.6.E5]
theorem jacobiThetaFourTau_powerSeries {τ z : ℂ} (hτ : 0 < τ.im)
    (hz : ‖π * z‖ < thetaLatticeMinNorm τ) :
    ∃ S : ℂ, HasSum (fun j : ℕ => thetaGamma (2 * (j + 1)) τ * z ^ (2 * (j + 1)) /
        (2 * (j + 1))) S ∧
      jacobiThetaFourTau (π * z) τ = jacobiThetaFourNullTau τ * cexp (-S) := by
  sorry

/-- DLMF 20.6.10: `α_{2j}(τ) = 2^{2j} δ_{2j}(2τ) - δ_{2j}(τ)` and
`β_{2j}(τ) = 2^{2j} γ_{2j}(2τ) - γ_{2j}(τ)`, `j ≥ 1`, `Im τ > 0`. -/
@[dlmf 20.6.E10]
theorem thetaAlpha_thetaBeta_eq {τ : ℂ} (hτ : 0 < τ.im) (j : ℕ) (hj : 1 ≤ j) :
    thetaAlpha (2 * j) τ = 2 ^ (2 * j) * thetaDelta (2 * j) (2 * τ) - thetaDelta (2 * j) τ ∧
      thetaBeta (2 * j) τ = 2 ^ (2 * j) * thetaGamma (2 * j) (2 * τ) - thetaGamma (2 * j) τ := by
  sorry

/-- DLMF §20.6: for `2j ≥ 4` the order of summation in the lattice sums does not matter: the
double series converge absolutely, and their unordered sums equal the iterated sums. -/
@[dlmf 20.6]
theorem thetaDelta_hasSum_lattice {τ : ℂ} (hτ : 0 < τ.im) {j : ℕ} (hj : 2 ≤ j) :
    HasSum (fun p : ℤ × ℤ => if p.1 = 0 ∧ p.2 = 0 then 0 else
        ((p.1 : ℂ) + p.2 * τ) ^ (-((2 * j : ℕ) : ℤ))) (thetaDelta (2 * j) τ) ∧
      HasSum (fun p : ℤ × ℤ => ((p.1 : ℂ) - 1 / 2 + p.2 * τ) ^ (-((2 * j : ℕ) : ℤ)))
        (thetaAlpha (2 * j) τ) ∧
      HasSum (fun p : ℤ × ℤ => ((p.1 : ℂ) - 1 / 2 + (p.2 - 1 / 2) * τ) ^ (-((2 * j : ℕ) : ℤ)))
        (thetaBeta (2 * j) τ) ∧
      HasSum (fun p : ℤ × ℤ => ((p.1 : ℂ) + (p.2 - 1 / 2) * τ) ^ (-((2 * j : ℕ) : ℤ)))
        (thetaGamma (2 * j) τ) := by
  sorry

/-- DLMF §20.6: for `j = 1` the order matters: the double series for `δ₂` is not absolutely
summable. -/
@[dlmf 20.6]
theorem thetaDelta_two_not_summable {τ : ℂ} (hτ : 0 < τ.im) :
    ¬ Summable (fun p : ℤ × ℤ => if p.1 = 0 ∧ p.2 = 0 then (0 : ℂ) else
        ((p.1 : ℂ) + p.2 * τ) ^ (-2 : ℤ)) := by
  sorry

end DLMF.Theta

end
