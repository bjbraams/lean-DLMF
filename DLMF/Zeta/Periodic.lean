/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Polylog
public import DLMF.Zeta.S25bDirichletTest

/-!
# The periodic zeta function (DLMF §25.13)

DLMF's periodic zeta function `F(x, s) = ∑_{n≥1} e^{2πinx}/n^s` (25.13.1, real `x`) is Mathlib's
`HurwitzZeta.expZeta (x : UnitAddCircle) s`, the meromorphic continuation in `s` of the series
(entire in `s` for `x ∉ ℤ`; for `x ∈ ℤ` it is `ζ(s)`, with Lean's junk value at `s = 1`). The
convergence of the series for `Re s > 1` is `HurwitzZeta.hasSum_expZeta_of_one_lt_re`
(pointer in `DLMF.Zeta.MathlibCoverageB`); its conditional convergence for `0 < Re s ≤ 1`,
`x ∉ ℤ`, is acquired here as a limit of partial sums. The identification with the polylogarithm,
`F(x, s) = Li_s(e^{2πix})`, is `DLMF.Polylog.polylogSeries_exp_eq_expZeta` for natural `s ≥ 2` and
`polylog_exp_eq_expZeta` below for `Re s > 1`.

Since Mathlib's parameter lives in `ℝ/ℤ`, periodicity in `x` holds by construction.
For `0 < x < 1`, DLMF's `ζ(1 - s, x)` is Mathlib's `hurwitzZeta x (1 - s)`.
-/

@[expose] public section

open Complex Filter Set HurwitzZeta
open scoped Real Topology

noncomputable section

namespace DLMF.Zeta

/-- **The defining series** (DLMF 25.13.1) in its conditional range: for `x ∉ ℤ` and `Re s > 0`,
`F(x, s) = ∑_{n≥1} e^{2πinx}/n^s` as a limit of partial sums. (For `Re s > 1` and all real `x` the
series converges absolutely: `HurwitzZeta.hasSum_expZeta_of_one_lt_re`.) -/
@[dlmf 25.13.E1]
theorem tendsto_expZeta_partialSum {x : ℝ} (hx : ∀ m : ℤ, x ≠ m) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        cexp (2 * π * I * (n + 1) * x) / ((n : ℂ) + 1) ^ s) atTop
      (𝓝 (expZeta (x : UnitAddCircle) s)) :=
  s25b_tendsto_expZeta (Or.inl ⟨hx, hs⟩)

/-- **`F(x, s)` is the polylogarithm on the unit circle** (DLMF §25.13): `F(x, s) = Li_s(e^{2πix})`
for real `x` and `Re s > 1`. -/
@[dlmf 25.13]
theorem polylog_exp_eq_expZeta (x : ℝ) {s : ℂ} (hs : 1 < s.re) :
    polylog s (cexp (2 * π * I * x)) = expZeta (x : UnitAddCircle) s := by
  have hz : ‖cexp (2 * π * I * x)‖ = 1 := by
    rw [show 2 * π * I * x = ((2 * π * x : ℝ) : ℂ) * I by push_cast; ring]
    exact norm_exp_ofReal_mul_I _
  have h1 := hasSum_polylog_of_norm_eq_one hs hz
  have h2 := (hasSum_nat_add_iff' 1).mpr (hasSum_expZeta_of_one_lt_re x hs)
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, Complex.exp_zero,
    zero_cpow (ne_zero_of_one_lt_re hs), div_zero, sub_zero] at h2
  refine h1.unique (h2.congr_fun fun n => ?_)
  rw [← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- **Periodicity** (DLMF §25.13): `F(x + 1, s) = F(x, s)`. -/
@[dlmf 25.13]
theorem expZeta_add_one (x : ℝ) (s : ℂ) :
    expZeta ((x + 1 : ℝ) : UnitAddCircle) s = expZeta (x : UnitAddCircle) s := by
  rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]

/-- **Integer `x`** (DLMF §25.13): `F(m, s) = ζ(s)` for `m ∈ ℤ`. -/
@[dlmf 25.13]
theorem expZeta_intCast (m : ℤ) (s : ℂ) :
    expZeta ((m : ℝ) : UnitAddCircle) s = riemannZeta s := by
  have h : ((m : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨m, by simp⟩
  rw [h, expZeta_zero]

/-- **`F` in terms of Hurwitz zeta** (DLMF 25.13.2): for `0 < x < 1` (here, with Mathlib's
periodic parameter, for every real `x`),
`F(x, s) = (Γ(1-s)/(2π)^{1-s}) (e^{πi(1-s)/2} ζ(1-s, x) + e^{πi(s-1)/2} ζ(1-s, 1-x))`.
DLMF states it for `Re s > 1`; it holds for all non-integer `s` (stronger than DLMF). At integers
`s ≥ 2` both terms of the bracket are finite while `Γ(1-s)` has a pole, so the printed formula is a
limit there (implicit condition `s ∉ ℤ`; Lean's `Γ(1-s) = 0` there). -/
@[dlmf 25.13.E2]
theorem expZeta_eq_hurwitzZeta (x : ℝ) {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ n) :
    expZeta (x : UnitAddCircle) s = Gamma (1 - s) / (2 * π) ^ (1 - s) *
      (cexp (π * I * (1 - s) / 2) * hurwitzZeta (x : UnitAddCircle) (1 - s) +
        cexp (π * I * (s - 1) / 2) * hurwitzZeta ((1 - x : ℝ) : UnitAddCircle) (1 - s)) := by
  have hs' : ∀ n : ℕ, 1 - s ≠ 1 - n := fun n h => hs n (by linear_combination -h)
  have h := expZeta_one_sub (x : UnitAddCircle) hs'
  rw [sub_sub_cancel] at h
  have hneg : ((1 - x : ℝ) : UnitAddCircle) = -(x : UnitAddCircle) := by
    rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub]
  rw [h, hneg, cpow_neg, div_eq_mul_inv]
  ring_nf

/-- **Hurwitz zeta in terms of `F`** (DLMF 25.13.3): `ζ(1-s, x) = (Γ(s)/(2π)^s)(e^{-πis/2} F(x, s)
+ e^{πis/2} F(-x, s))` for `Re s > 0` if `0 < x < 1`, and `Re s > 1` if `x = 1`. -/
@[dlmf 25.13.E3]
theorem hurwitzZeta_one_sub_eq_expZeta {x : ℝ} {s : ℂ}
    (h : (0 < x ∧ x < 1 ∧ 0 < s.re) ∨ (x = 1 ∧ 1 < s.re)) :
    hurwitzZeta (x : UnitAddCircle) (1 - s) = Gamma s / (2 * π) ^ s *
      (cexp (-π * I * s / 2) * expZeta (x : UnitAddCircle) s +
        cexp (π * I * s / 2) * expZeta ((-x : ℝ) : UnitAddCircle) s) := by
  have hre : 0 < s.re := by rcases h with ⟨-, -, h⟩ | ⟨-, h⟩ <;> linarith
  have hs : ∀ n : ℕ, s ≠ -n := fun n hn => by
    have := congrArg Complex.re hn; simp at this; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hs' : (x : UnitAddCircle) ≠ 0 ∨ s ≠ 1 := by
    rcases h with ⟨h0, h1, -⟩ | ⟨-, h1⟩
    · left
      rw [Ne, AddCircle.coe_eq_zero_iff]
      rintro ⟨m, hm⟩
      simp only [zsmul_eq_mul, mul_one] at hm
      have h0' : (0 : ℝ) < m := by rw [hm]; exact h0
      have h1' : (m : ℝ) < 1 := by rw [hm]; exact h1
      have : (0 : ℤ) < m := by exact_mod_cast h0'
      have : m < (1 : ℤ) := by exact_mod_cast h1'
      omega
    · right; intro hs1; rw [hs1] at h1; simp at h1
  rw [hurwitzZeta_one_sub _ hs hs', cpow_neg, AddCircle.coe_neg, div_eq_mul_inv]
  ring

end DLMF.Zeta

end
