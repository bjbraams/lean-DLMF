/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Asymptotic approximations of the Riemann zeta function (DLMF §25.9)

The approximate functional equation of Hardy and Littlewood (25.9.1) with the factor
`χ(s) = π^{s-½} Γ(½ - s/2)/Γ(s/2)` (25.9.2) of the functional equation `ζ(s) = χ(s) ζ(1-s)`, and
its symmetric case on the critical line (25.9.3).

The `O`-terms of 25.9.1 are uniform in `x, y ≥ 1` subject to `2πxy = t`: the statement gives a
constant `C` and a threshold `T₀`, depending only on `σ`, with the error bounded by
`C (x^{-σ} + y^{σ-1} t^{½-σ})` for all `t ≥ T₀`. Sums `∑_{1 ≤ n ≤ x}` are over
`n ∈ [1, ⌊x⌋]`. 25.9.3 is proved from 25.9.1.
-/

@[expose] public noncomputable section

open Complex Filter Topology Finset Asymptotics
open scoped Real

namespace DLMF.Zeta

/-- DLMF 25.9.2: `χ(s) = π^{s-½} Γ(½ - s/2) / Γ(s/2)`. -/
@[dlmf 25.9.E2]
def riemannChi (s : ℂ) : ℂ :=
  (π : ℂ) ^ (s - 1 / 2) * Gamma (1 / 2 - s / 2) / Gamma (s / 2)

/-- DLMF 25.9.1 (approximate functional equation): for fixed `0 ≤ σ ≤ 1`, as `t → ∞`,
`ζ(σ+it) = ∑_{1≤n≤x} n^{-s} + χ(s) ∑_{1≤n≤y} n^{s-1} + O(x^{-σ}) + O(y^{σ-1} t^{½-σ})`,
`s = σ + it`, uniformly for `x, y ≥ 1` with `2πxy = t`. -/
@[dlmf 25.9.E1]
theorem approximate_functional_equation {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∃ C T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t → ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → 2 * π * x * y = t →
      ‖riemannZeta (σ + t * I) - ∑ n ∈ Icc 1 ⌊x⌋₊, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I) -
          riemannChi (σ + t * I) * ∑ n ∈ Icc 1 ⌊y⌋₊, 1 / (n : ℂ) ^ (1 - ((σ : ℂ) + t * I))‖ ≤
        C * (x ^ (-σ) + y ^ (σ - 1) * t ^ (1 / 2 - σ)) := by
  sorry

/-- DLMF 25.9.3: with `m = ⌊√(t/(2π))⌋`, as `t → ∞`,
`ζ(½+it) = ∑_{n=1}^{m} n^{-½-it} + χ(½+it) ∑_{n=1}^{m} n^{-½+it} + O(t^{-1/4})`.
Proved from 25.9.1 with `σ = ½`, `x = y = √(t/(2π))`. -/
@[dlmf 25.9.E3]
theorem riemannZeta_critical_line_approx :
    (fun t : ℝ => riemannZeta (1 / 2 + t * I) -
        ∑ n ∈ Icc 1 ⌊√(t / (2 * π))⌋₊, 1 / (n : ℂ) ^ (1 / 2 + t * I) -
        riemannChi (1 / 2 + t * I) * ∑ n ∈ Icc 1 ⌊√(t / (2 * π))⌋₊, 1 / (n : ℂ) ^ (1 / 2 - t * I))
      =O[atTop] fun t : ℝ => t ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨C, T₀, hC⟩ := approximate_functional_equation (σ := 1 / 2) (by norm_num) (by norm_num)
  refine IsBigO.of_bound (2 * |C| * (2 * π) ^ (1 / 4 : ℝ)) ?_
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (2 * π)] with t ht ht2
  have hπ : 0 < 2 * π := by positivity
  have ht0 : 0 < t := lt_of_lt_of_le hπ ht2
  set x := √(t / (2 * π)) with hx
  have hx1 : 1 ≤ x := by
    rw [hx, Real.one_le_sqrt, one_le_div hπ]; exact ht2
  have hxy : 2 * π * x * x = t := by
    rw [mul_assoc, Real.mul_self_sqrt (by positivity)]; field_simp
  have h := hC t ht x x hx1 hx1 hxy
  have e1 : ((1 / 2 : ℝ) : ℂ) + t * I = 1 / 2 + t * I := by push_cast; ring
  have e2 : (1 : ℂ) - (1 / 2 + t * I) = 1 / 2 - t * I := by ring
  rw [e1, e2] at h
  have hxpow : x ^ (-(1 / 2 : ℝ)) = (2 * π) ^ (1 / 4 : ℝ) * t ^ (-(1 / 4 : ℝ)) := by
    rw [hx, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity),
      Real.div_rpow ht0.le hπ.le, show (1 / 2 : ℝ) * -(1 / 2) = -(1 / 4) by norm_num,
      Real.rpow_neg hπ.le (1 / 4), div_inv_eq_mul, mul_comm]
  have hrhs : x ^ (-(1 / 2 : ℝ)) + x ^ ((1 / 2 : ℝ) - 1) * t ^ ((1 / 2 : ℝ) - 1 / 2) =
      2 * ((2 * π) ^ (1 / 4 : ℝ) * t ^ (-(1 / 4 : ℝ))) := by
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, sub_self, Real.rpow_zero, mul_one,
      hxpow]
    ring
  rw [hrhs] at h
  have hpos : 0 ≤ t ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg ht0.le _
  rw [Real.norm_of_nonneg hpos]
  calc _ ≤ C * (2 * ((2 * π) ^ (1 / 4 : ℝ) * t ^ (-(1 / 4 : ℝ)))) := h
    _ ≤ |C| * (2 * ((2 * π) ^ (1 / 4 : ℝ) * t ^ (-(1 / 4 : ℝ)))) := by
        gcongr; exact le_abs_self C
    _ = _ := by ring

end DLMF.Zeta
