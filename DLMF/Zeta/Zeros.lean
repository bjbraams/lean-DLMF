/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Order
public import DLMF.Zeta.Basic.RiemannProperties
public import Mathlib.NumberTheory.LSeries.HardyZ
public import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# Zeros of the Riemann zeta function (DLMF §25.10)

The distribution of the zeros of `ζ` (DLMF §25.10(i)), the Riemann–Siegel functions `θ` and
`Z`, and the counting functions and Riemann–Siegel formula of §25.10(ii). Mathlib proves
`ζ(s) ≠ 0` for `Re s ≥ 1` (`riemannZeta_ne_zero_of_one_le_re`) and the trivial zeros
`ζ(-2n) = 0` (`riemannZeta_neg_two_mul_nat_add_one`); pointers are in
`DLMF.Zeta.MathlibCoverage`. The Riemann hypothesis is a conjecture and is not stated here;
Mathlib's `RiemannHypothesis` is the statement (pointer only).

## Main definitions

* `criticalStripZeros`: the zeros of `ζ` in the critical strip `0 < Re s < 1`.
* `riemannZeroCount`, `criticalLineZeroCount`: `N(T)`, the number of zeros in the critical strip
  with `0 < Im s < T` counted with multiplicity, and the number of those on the critical line.
* `riemannSiegelRemainder`: the remainder `R(t)` of the Riemann–Siegel formula (DLMF 25.10.3).

## Main results

* `riemannZeta_ne_zero_of_re_nonpos`: `ζ(s) ≠ 0` for `Re s ≤ 0` except at the trivial zeros.
* `riemannZeta_conj_eq_zero_iff`, `riemannZeta_one_sub_eq_zero_iff`: the symmetries of the zeros
  about the real axis and about the critical line.
* `riemannSiegelZ_sign_changes`: Hardy's theorem, `Z` changes sign infinitely often.
* `exists_riemannZeta_critical_line_zero_gt`, `criticalStripZeros_infinite`: infinitely many
  zeros on the critical line and in the critical strip, derived from Hardy's theorem.
* `finite_criticalStripZerosBelow`: finitely many zeros in the strip with `0 < Im s < T`.
* `riemannSiegelRemainder_isBigO`, `riemannSiegelRemainder_sub_leading_isBigO`: the
  Riemann–Siegel formula (DLMF 25.10.3) and the first term of its asymptotic series (25.10.4).
* `eventually_criticalLineZeroCount_gt`: more than 41% of the zeros lie on the critical line
  (Bui, Conrey and Young), as an eventual inequality.

## Implementation notes

The Riemann–Siegel functions `riemannSiegelTheta` and `riemannSiegelZ` (DLMF 25.10.1–25.10.2)
are defined in `DLMF.Zeta.Basic.Riemann`, and their basic properties (`Z` is Mathlib's `hardyZ`,
real, with `|Z(t)| = |ζ(½+it)|`) are in `DLMF.Zeta.Basic.RiemannProperties`.
`riemannSiegelTheta` uses the principal phase, as DLMF prescribes. It is then discontinuous (it
differs from the usual continuous Riemann–Siegel theta function by integer multiples of `2π`),
but `e^{iθ}`, and hence `Z`, do not depend on the choice. The asymptotic term 25.10.4 is stated
along the `t` with `cos √(2πt) ≠ 0`; at the other `t` the printed quotient is a removable `0/0`
form. The statement about the first ten billion zeros is numerical and excluded.
-/

@[expose] public noncomputable section

open Complex Filter Topology Finset Asymptotics
open scoped Real

namespace DLMF.Zeta

/-! ### §25.10(i) Distribution -/

/-- DLMF §25.10(i): except for the trivial zeros `-2, -4, …`, `ζ(s) ≠ 0` for `Re s ≤ 0`.
Proved from the functional equation and the nonvanishing of `ζ` on `Re s ≥ 1`. -/
@[dlmf 25.10.i]
theorem riemannZeta_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0)
    (htriv : ∀ n : ℕ, s ≠ -2 * (n + 1)) : riemannZeta s ≠ 0 := by
  rcases eq_or_ne s 0 with rfl | hs0
  · rw [riemannZeta_zero]; norm_num
  have h1 : ∀ n : ℕ, 1 - s ≠ -n := by
    intro n h
    have := congrArg re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 : 1 - s ≠ 1 := fun h => hs0 (by linear_combination -h)
  have h := riemannZeta_one_sub h1 h2
  rw [sub_sub_cancel] at h
  rw [h]
  have hre : 1 ≤ (1 - s).re := by simp; linarith
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_)
    (riemannZeta_ne_zero_of_one_le_re hre)
  · exact cpow_ne_zero_iff.mpr (Or.inl (by simp [Real.pi_ne_zero]))
  · exact Gamma_ne_zero h1
  · intro hc
    rw [Complex.cos_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    have hsk : s = -2 * k := by
      have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      have : (π : ℂ) * (1 - s) = (2 * k + 1) * π := by linear_combination 2 * hk
      have := mul_left_cancel₀ hπ (this.trans (mul_comm _ _))
      linear_combination -this / 1
    have hkre : (k : ℝ) ≥ 0 := by
      have := congrArg re hsk
      simp at this
      linarith
    have hk0 : k ≠ 0 := by rintro rfl; simp at hsk; exact hs0 hsk
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 1 := by
      refine ⟨(k - 1).toNat, ?_⟩
      have : (0 : ℤ) < k := lt_of_le_of_ne (by exact_mod_cast hkre) (Ne.symm hk0)
      omega
    exact htriv n (by rw [hsk]; push_cast; ring)

/-- DLMF §25.10(i): the zeros of `ζ` are symmetric about the real axis. -/
@[dlmf 25.10.i]
theorem riemannZeta_conj_eq_zero_iff (s : ℂ) :
    riemannZeta ((starRingEnd ℂ) s) = 0 ↔ riemannZeta s = 0 := by
  rw [riemannZeta_conj, map_eq_zero]

/-- DLMF §25.10(i): in the critical strip `0 < Re s < 1` the zeros of `ζ` are symmetric about the
critical line, `ζ(s) = 0 ↔ ζ(1 - s) = 0` (with the conjugation symmetry this gives the reflection
`s ↦ 1 - s̄` in the line `Re s = ½`). -/
@[dlmf 25.10.i]
theorem riemannZeta_one_sub_eq_zero_iff {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    riemannZeta (1 - s) = 0 ↔ riemannZeta s = 0 := by
  have h1 : ∀ n : ℕ, s ≠ -n := by
    intro n h
    have := congrArg re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 : s ≠ 1 := by rintro rfl; simp at hs1
  rw [riemannZeta_one_sub h1 h2]
  have hc : cos (π * s / 2) ≠ 0 := by
    intro hc
    rw [Complex.cos_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have hsk : s = 2 * k + 1 := by
      have : (π : ℂ) * s = (2 * k + 1) * π := by linear_combination 2 * hk
      exact mul_left_cancel₀ hπ (this.trans (mul_comm _ _))
    have := congrArg re hsk
    simp at this
    have hk1 : (k : ℝ) < 0 := by linarith
    have hk2 : (-1 : ℝ) < k := by linarith
    have : k < 0 := by exact_mod_cast hk1
    have : -1 < k := by exact_mod_cast hk2
    omega
  have hp : (2 * (π : ℂ)) ^ (-s) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (by simp [Real.pi_ne_zero]))
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exfalso
      rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact two_ne_zero h
          · exact hp h
        · exact Gamma_ne_zero h1 h
      · exact hc h
    · exact h
  · intro h; rw [h, mul_zero]

/-- DLMF §25.10(i): the set of zeros of `ζ` in the critical strip `0 < Re s < 1`. -/
@[dlmf 25.10.i]
def criticalStripZeros : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- DLMF §25.10(i) (Hardy's theorem): `Z(t)` changes sign infinitely often as `t → ∞`. -/
@[dlmf 25.10.i]
theorem riemannSiegelZ_sign_changes (T : ℝ) :
    ∃ t₁ t₂ : ℝ, T < t₁ ∧ T < t₂ ∧ (riemannSiegelZ t₁).re < 0 ∧ 0 < (riemannSiegelZ t₂).re := by
  sorry

/-- DLMF §25.10(i): `ζ(½ + it)` has infinitely many zeros with `t` real (arbitrarily large `t`).
Proved from the sign changes of `Z` by the intermediate value theorem. -/
@[dlmf 25.10.i]
theorem exists_riemannZeta_critical_line_zero_gt (T : ℝ) :
    ∃ t : ℝ, T < t ∧ riemannZeta (1 / 2 + t * I) = 0 := by
  obtain ⟨t₁, t₂, h1, h2, hneg, hpos⟩ := riemannSiegelZ_sign_changes T
  simp only [riemannSiegelZ_eq_hardyZ, ofReal_re] at hneg hpos
  have hmem : (0 : ℝ) ∈ Set.uIcc (hardyZ t₁) (hardyZ t₂) :=
    Set.mem_uIcc.mpr (Or.inl ⟨hneg.le, hpos.le⟩)
  obtain ⟨t, ht, hzero⟩ :=
    intermediate_value_uIcc continuous_hardyZ.continuousOn hmem
  refine ⟨t, ?_, (hardyZ_eq_zero_iff t).mp hzero⟩
  rcases Set.mem_uIcc.mp ht with ⟨ha, _⟩ | ⟨ha, _⟩ <;> linarith

/-- DLMF §25.10(i): `ζ` has infinitely many zeros in the critical strip. -/
@[dlmf 25.10.i]
theorem criticalStripZeros_infinite : criticalStripZeros.Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := (hfin.image Complex.im).bddAbove
  obtain ⟨t, ht, hz⟩ := exists_riemannZeta_critical_line_zero_gt B
  have hmem : (1 / 2 + t * I : ℂ) ∈ criticalStripZeros :=
    ⟨hz, by simp, by simp; norm_num⟩
  have := hB ⟨_, hmem, rfl⟩
  simp at this
  linarith

/-! ### §25.10(ii) Riemann–Siegel formula -/

/-- The nontrivial zeros `ρ` with `0 < Im ρ < T` (a finite set,
`finite_criticalStripZerosBelow`). -/
def criticalStripZerosBelow (T : ℝ) : Set ℂ :=
  {ρ | ρ ∈ criticalStripZeros ∧ 0 < ρ.im ∧ ρ.im < T}

/-- DLMF §25.10(ii): there are only finitely many zeros in the critical strip with `0 < t < T`. -/
theorem finite_criticalStripZerosBelow (T : ℝ) : (criticalStripZerosBelow T).Finite := by
  have hK : IsCompact (Metric.closedBall (0 : ℂ) (1 + |T|)) := isCompact_closedBall _ _
  refine (hK.inter_riemannZetaZeros_finite).subset fun ρ hρ => ⟨?_, hρ.1.1⟩
  obtain ⟨⟨-, h0, h1⟩, h2, h3⟩ := hρ
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := norm_le_abs_re_add_abs_im ρ
    _ ≤ 1 + |T| := add_le_add (by rw [abs_of_pos h0]; exact h1.le)
        (by rw [abs_of_pos h2]; exact h3.le.trans (le_abs_self T))

/-- DLMF §25.10(ii): `N(T)`, the number of zeros of `ζ` in the critical strip with `0 < t < T`,
counted with multiplicity. -/
@[dlmf 25.10.ii]
def riemannZeroCount (T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ criticalStripZerosBelow T, analyticOrderNatAt riemannZeta ρ

/-- The number of zeros of `ζ` on the critical line with `0 < t < T`, counted with
multiplicity. -/
@[dlmf 25.10.ii]
def criticalLineZeroCount (T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ | ρ ∈ criticalStripZerosBelow T ∧ ρ.re = 1 / 2}, analyticOrderNatAt riemannZeta ρ

/-- DLMF 25.10.3: the remainder `R(t) = Z(t) - 2 ∑_{n=1}^{m} cos(θ(t) - t ln n)/√n`,
`m = ⌊√(t/(2π))⌋`, of the Riemann–Siegel formula (`Z` is real, so its real part is taken). -/
@[dlmf 25.10.E3]
def riemannSiegelRemainder (t : ℝ) : ℝ :=
  (riemannSiegelZ t).re - 2 * ∑ n ∈ Icc 1 ⌊√(t / (2 * π))⌋₊,
    Real.cos (riemannSiegelTheta t - t * Real.log n) / √n

/-- DLMF 25.10.3 (Riemann–Siegel formula): `R(t) = O(t^{-1/4})` as `t → ∞`. -/
@[dlmf 25.10.E3]
theorem riemannSiegelRemainder_isBigO :
    riemannSiegelRemainder =O[atTop] fun t : ℝ => t ^ (-(1 / 4 : ℝ)) := by
  sorry

/-- DLMF 25.10.4: `R(t) = (-1)^{m-1} (2π/t)^{1/4} cos(t - (2m+1)√(2πt) - π/8)/cos(√(2πt))
+ O(t^{-3/4})`, `m = ⌊√(t/(2π))⌋`, as `t → ∞` along the `t` with `cos √(2πt) ≠ 0`. -/
@[dlmf 25.10.E4]
theorem riemannSiegelRemainder_sub_leading_isBigO :
    (fun t : ℝ => riemannSiegelRemainder t -
        (-1) ^ (⌊√(t / (2 * π))⌋₊ - 1) * (2 * π / t) ^ (1 / 4 : ℝ) *
          Real.cos (t - (2 * ⌊√(t / (2 * π))⌋₊ + 1) * √(2 * π * t) - π / 8) /
          Real.cos √(2 * π * t))
      =O[atTop ⊓ 𝓟 {t | Real.cos √(2 * π * t) ≠ 0}] fun t : ℝ => t ^ (-(3 / 4 : ℝ)) := by
  sorry

/-- DLMF §25.10(ii) (Bui, Conrey and Young, 2011): more than 41% of the zeros in the critical
strip lie on the critical line; stated as `N₀(T) > 0.41 N(T)` for all large `T`, where `N₀`
counts the zeros on the line. -/
@[dlmf 25.10.ii]
theorem eventually_criticalLineZeroCount_gt :
    ∀ᶠ T in atTop, (41 / 100 : ℝ) * riemannZeroCount T < criticalLineZeroCount T := by
  sorry

end DLMF.Zeta
