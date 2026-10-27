/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.Energy.Defs
public import DLMF.Coulomb.Energy.Q2eRegular

/-!
# Coulomb functions `f`, `h`: recurrences, derivatives and large `ℓ` (DLMF §§33.17–33.18)

The three-term recurrences in `ℓ` (33.17.1–33.17.2, for `ℓ ≥ 1`), the derivative formulas
(33.17.3–33.17.4) and the limiting forms as `ℓ → ∞` (33.18.1). All are verified numerically
(mpmath, 30 digits) for `ε ∈ {0.3, -0.13, 0}` and both signs of `r`.
-/

@[expose] public section

open Filter Asymptotics
open scoped Real Nat Topology

noncomputable section

namespace DLMF.Coulomb

/-- **DLMF 33.17.1**: for `ℓ ≥ 1`,
`(ℓ+1) r f(ε,ℓ-1;r) - (2ℓ+1)(ℓ(ℓ+1) - r) f(ε,ℓ;r) + ℓ(1 + (ℓ+1)²ε) r f(ε,ℓ+1;r) = 0`. -/
@[dlmf 33.17.E1]
theorem coulombf_recurrence (ε : ℝ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (r : ℝ) :
    (ℓ + 1) * r * coulombf ε (ℓ - 1) r - (2 * ℓ + 1) * (ℓ * (ℓ + 1) - r) * coulombf ε ℓ r +
      ℓ * (1 + (ℓ + 1) ^ 2 * ε) * r * coulombf ε (ℓ + 1) r = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hℓ
  have h := congrArg Complex.re (q2e_Phi_three_term ε m r)
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, Complex.add_im, Complex.sub_im,
    Complex.mul_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.zero_re, pow_two] at h
  rw [Nat.add_sub_cancel, q2e_coulombf_eq_re, q2e_coulombf_eq_re, q2e_coulombf_eq_re]
  push_cast
  linear_combination h

/-- **DLMF 33.17.2**: for `ℓ ≥ 1` and `r ≠ 0`,
`(ℓ+1)(1 + ℓ²ε) r h(ε,ℓ-1;r) - (2ℓ+1)(ℓ(ℓ+1) - r) h(ε,ℓ;r) + ℓ r h(ε,ℓ+1;r) = 0`. -/
@[dlmf 33.17.E2]
theorem coulombh_recurrence (ε : ℝ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {r : ℝ} (hr : r ≠ 0) :
    (ℓ + 1) * (1 + ℓ ^ 2 * ε) * r * coulombh ε (ℓ - 1) r -
      (2 * ℓ + 1) * (ℓ * (ℓ + 1) - r) * coulombh ε ℓ r + ℓ * r * coulombh ε (ℓ + 1) r = 0 := by
  sorry

/-- **DLMF 33.17.3**: `(ℓ+1) r f'(ε,ℓ;r) = ((ℓ+1)² - r) f(ε,ℓ;r) - (1 + (ℓ+1)²ε) r f(ε,ℓ+1;r)`,
the derivative being in `r`. -/
@[dlmf 33.17.E3]
theorem coulombf_deriv (ε : ℝ) (ℓ : ℕ) (r : ℝ) :
    HasDerivAt (coulombf ε ℓ) (deriv (coulombf ε ℓ) r) r ∧
      (ℓ + 1) * r * deriv (coulombf ε ℓ) r =
        ((ℓ + 1) ^ 2 - r) * coulombf ε ℓ r - (1 + (ℓ + 1) ^ 2 * ε) * r * coulombf ε (ℓ + 1) r := by
  have hd := q2e_hasDerivAt_coulombf ε ℓ r
  refine ⟨hd.deriv ▸ hd, ?_⟩
  have h := congrArg Complex.re (q2e_Phi_raise ε ℓ r)
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, Complex.add_im, Complex.sub_im,
    Complex.mul_im, Complex.one_re, Complex.one_im, pow_two] at h
  rw [hd.deriv, q2e_coulombf_eq_re, q2e_coulombf_eq_re]
  linear_combination h

/-- **DLMF 33.17.4**: `(ℓ+1) r h'(ε,ℓ;r) = ((ℓ+1)² - r) h(ε,ℓ;r) - r h(ε,ℓ+1;r)` for `r ≠ 0`. -/
@[dlmf 33.17.E4]
theorem coulombh_deriv (ε : ℝ) (ℓ : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (coulombh ε ℓ) (deriv (coulombh ε ℓ) r) r ∧
      (ℓ + 1) * r * deriv (coulombh ε ℓ) r =
        ((ℓ + 1) ^ 2 - r) * coulombh ε ℓ r - r * coulombh ε (ℓ + 1) r := by
  sorry

/-- **DLMF 33.18.1**: as `ℓ → ∞` with `ε` and `r ≠ 0` fixed,
`f(ε,ℓ;r) ~ (2r)^{ℓ+1}/(2ℓ+1)!` and `h(ε,ℓ;r) ~ (2ℓ)!/(π(2r)^ℓ)`. -/
@[dlmf 33.18.E1]
theorem coulombf_coulombh_isEquivalent_atTop (ε : ℝ) {r : ℝ} (hr : r ≠ 0) :
    (fun ℓ : ℕ => coulombf ε ℓ r) ~[atTop] (fun ℓ : ℕ => (2 * r) ^ (ℓ + 1) / (2 * ℓ + 1)!) ∧
      (fun ℓ : ℕ => coulombh ε ℓ r) ~[atTop] (fun ℓ : ℕ => (2 * ℓ)! / (π * (2 * r) ^ ℓ)) := by
  sorry

end DLMF.Coulomb
