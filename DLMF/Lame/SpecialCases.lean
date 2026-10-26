/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Eigenvalues
public import DLMF.Mathieu.Basic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-!
# Lamé functions: special cases and limiting forms (DLMF §29.5)

* `k = 0`: `a^m_ν(0) = b^m_ν(0) = m²`, `Ec^0_ν(z, 0) = 2^{-1/2}`,
  `Ec^m_ν(z, 0) = cos(m(π/2 - z))`, `Es^m_ν(z, 0) = sin(m(π/2 - z))` (29.5.1–29.5.3);
* `k → 1⁻`: the eigenvalue limits 29.5.4 and the limits 29.5.5–29.5.6 of normalized Lamé
  functions in terms of the Gauss function `F` (Mathlib's `ordinaryHypergeometric`, the series
  converges since `tanh² x < 1`);
* `k → 0⁺`, `ν → ∞` with `k²ν(ν+1) = 4θ`: the Mathieu limits 29.5.7, with the Mathieu
  functions `ce_m`, `se_m` of `DLMF.Mathieu.Basic` (agent ACQ28A).

The definitions of `DLMF.Lame.Basic` make sense at `k = 0` (then `K = π/2` and `sn = sin`), so
29.5.1–29.5.3 are statements about the same functions. All statements are admitted.
-/

@[expose] public section

open Complex DLMF.JacobiElliptic DLMF.Elliptic Filter Set
open scoped Real Topology

noncomputable section

namespace DLMF.Lame

/-- 29.5.1: `a^m_ν(0) = m²`. Admitted. -/
@[dlmf 29.5.E1]
theorem Real.lameAk_zero {ν : ℝ} (hν : -1 / 2 ≤ ν) (m : ℕ) : Real.lameAk ν m 0 = m ^ 2 := by
  sorry

/-- 29.5.1: `b^m_ν(0) = m²`, `m ≥ 1`. Admitted. -/
@[dlmf 29.5.E1]
theorem Real.lameBk_zero {ν : ℝ} (hν : -1 / 2 ≤ ν) {m : ℕ} (hm : 1 ≤ m) :
    Real.lameBk ν m 0 = m ^ 2 := by
  sorry

/-- 29.5.2: `Ec^0_ν(x, 0) = 2^{-1/2}`. Admitted. -/
@[dlmf 29.5.E2]
theorem Real.lameEck_zero_zero {ν : ℝ} (hν : -1 / 2 ≤ ν) (x : ℝ) :
    Real.lameEck ν 0 x 0 = 1 / Real.sqrt 2 := by
  sorry

/-- 29.5.3: `Ec^m_ν(x, 0) = cos(m(π/2 - x))`, `m ≥ 1`. Admitted. -/
@[dlmf 29.5.E3]
theorem Real.lameEck_modulus_zero {ν : ℝ} (hν : -1 / 2 ≤ ν) {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    Real.lameEck ν m x 0 = Real.cos (m * (π / 2 - x)) := by
  sorry

/-- 29.5.3: `Es^m_ν(x, 0) = sin(m(π/2 - x))`, `m ≥ 1`. Admitted. -/
@[dlmf 29.5.E3]
theorem Real.lameEsk_modulus_zero {ν : ℝ} (hν : -1 / 2 ≤ ν) {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    Real.lameEsk ν m x 0 = Real.sin (m * (π / 2 - x)) := by
  sorry

/-- 29.5.4: `lim_{k→1⁻} a^m_ν(k²) = ν(ν+1) - μ²` with `μ = max(ν - m, 0)`. Admitted. -/
@[dlmf 29.5.E4]
theorem Real.tendsto_lameAk_one {ν : ℝ} (hν : -1 / 2 ≤ ν) (m : ℕ) :
    Tendsto (fun k => Real.lameAk ν m k) (𝓝[<] 1) (𝓝 (ν * (ν + 1) - max (ν - m) 0 ^ 2)) := by
  sorry

/-- 29.5.4: `lim_{k→1⁻} b^{m+1}_ν(k²) = ν(ν+1) - μ²` with `μ = max(ν - m, 0)`. Admitted. -/
@[dlmf 29.5.E4]
theorem Real.tendsto_lameBk_one {ν : ℝ} (hν : -1 / 2 ≤ ν) (m : ℕ) :
    Tendsto (fun k => Real.lameBk ν (m + 1) k) (𝓝[<] 1)
      (𝓝 (ν * (ν + 1) - max (ν - m) 0 ^ 2)) := by
  sorry

/-- 29.5.5, `Ec`: for even `m`,
`lim_{k→1⁻} Ec^m_ν(x, k²)/Ec^m_ν(0, k²) = (cosh x)^{-μ} F(½μ - ½ν, ½μ + ½ν + ½; ½; tanh² x)`,
`μ = max(ν - m, 0)`, real `x`. Admitted. -/
@[dlmf 29.5.E5]
theorem Real.tendsto_lameEck_div_one {ν : ℝ} (hν : -1 / 2 ≤ ν) {m : ℕ} (hm : Even m) (x : ℝ) :
    Tendsto (fun k => Real.lameEck ν m x k / Real.lameEck ν m 0 k) (𝓝[<] 1)
      (𝓝 (Real.cosh x ^ (-max (ν - m) 0) *
        ordinaryHypergeometric (max (ν - m) 0 / 2 - ν / 2) (max (ν - m) 0 / 2 + ν / 2 + 1 / 2)
          (1 / 2 : ℝ) (Real.tanh x ^ 2))) := by
  sorry

/-- 29.5.5, `Es`: for even `m`, `lim_{k→1⁻} Es^{m+1}_ν(x, k²)/Es^{m+1}_ν(0, k²)` is the same
limit as in `Real.tendsto_lameEck_div_one`. Admitted. -/
@[dlmf 29.5.E5]
theorem Real.tendsto_lameEsk_div_one {ν : ℝ} (hν : -1 / 2 ≤ ν) {m : ℕ} (hm : Even m) (x : ℝ) :
    Tendsto (fun k => Real.lameEsk ν (m + 1) x k / Real.lameEsk ν (m + 1) 0 k) (𝓝[<] 1)
      (𝓝 (Real.cosh x ^ (-max (ν - m) 0) *
        ordinaryHypergeometric (max (ν - m) 0 / 2 - ν / 2) (max (ν - m) 0 / 2 + ν / 2 + 1 / 2)
          (1 / 2 : ℝ) (Real.tanh x ^ 2))) := by
  sorry

/-- 29.5.6, `Ec`: for odd `m`, `lim_{k→1⁻} Ec^m_ν(x, k²)/(dEc^m_ν/dz)(0, k²) =
tanh x (cosh x)^{-μ} F(½μ - ½ν + ½, ½μ + ½ν + 1; 3/2; tanh² x)`, `μ = max(ν - m, 0)`.
Admitted. -/
@[dlmf 29.5.E6]
theorem Real.tendsto_lameEck_div_deriv_one {ν : ℝ} (hν : -1 / 2 ≤ ν) {m : ℕ} (hm : Odd m)
    (x : ℝ) :
    Tendsto (fun k => Real.lameEck ν m x k / deriv (fun z => Real.lameEck ν m z k) 0) (𝓝[<] 1)
      (𝓝 (Real.tanh x * Real.cosh x ^ (-max (ν - m) 0) *
        ordinaryHypergeometric (max (ν - m) 0 / 2 - ν / 2 + 1 / 2) (max (ν - m) 0 / 2 + ν / 2 + 1)
          (3 / 2 : ℝ) (Real.tanh x ^ 2))) := by
  sorry

/-- 29.5.6, `Es`: for odd `m`, `lim_{k→1⁻} Es^{m+1}_ν(x, k²)/(dEs^{m+1}_ν/dz)(0, k²)` is the
same limit as in `Real.tendsto_lameEck_div_deriv_one`. Admitted. -/
@[dlmf 29.5.E6]
theorem Real.tendsto_lameEsk_div_deriv_one {ν : ℝ} (hν : -1 / 2 ≤ ν) {m : ℕ} (hm : Odd m)
    (x : ℝ) :
    Tendsto (fun k => Real.lameEsk ν (m + 1) x k / deriv (fun z => Real.lameEsk ν (m + 1) z k) 0)
      (𝓝[<] 1)
      (𝓝 (Real.tanh x * Real.cosh x ^ (-max (ν - m) 0) *
        ordinaryHypergeometric (max (ν - m) 0 / 2 - ν / 2 + 1 / 2) (max (ν - m) 0 / 2 + ν / 2 + 1)
          (3 / 2 : ℝ) (Real.tanh x ^ 2))) := by
  sorry

/-- 29.5.7, `Ec`: if `k → 0⁺` and `ν → ∞` with `k²ν(ν+1) = 4θ` (`θ > 0`), then
`Ec^m_ν(x, k²) → ce_m(π/2 - x, θ)` (Mathieu function, §28.2(vi)), real `x`. Stated along
sequences `(νⱼ, kⱼ)`. Admitted. -/
@[dlmf 29.5.E7]
theorem Real.tendsto_lameEck_mathieuCe {θ : ℝ} (hθ : 0 < θ) (m : ℕ) (x : ℝ) {ν k : ℕ → ℝ}
    (hν : Tendsto ν atTop atTop) (hk : Tendsto k atTop (𝓝[>] 0))
    (hνk : ∀ j, k j ^ 2 * (ν j * (ν j + 1)) = 4 * θ) :
    Tendsto (fun j => (Real.lameEck (ν j) m x (k j) : ℂ)) atTop
      (𝓝 (DLMF.Mathieu.mathieuCe m (π / 2 - x) θ)) := by
  sorry

/-- 29.5.7, `Es`: under the same limit, `Es^m_ν(x, k²) → se_m(π/2 - x, θ)`, `m ≥ 1`.
Admitted. -/
@[dlmf 29.5.E7]
theorem Real.tendsto_lameEsk_mathieuSe {θ : ℝ} (hθ : 0 < θ) {m : ℕ} (hm : 1 ≤ m) (x : ℝ)
    {ν k : ℕ → ℝ} (hν : Tendsto ν atTop atTop) (hk : Tendsto k atTop (𝓝[>] 0))
    (hνk : ∀ j, k j ^ 2 * (ν j * (ν j + 1)) = 4 * θ) :
    Tendsto (fun j => (Real.lameEsk (ν j) m x (k j) : ℂ)) atTop
      (𝓝 (DLMF.Mathieu.mathieuSe m (π / 2 - x) θ)) := by
  sorry

end DLMF.Lame
