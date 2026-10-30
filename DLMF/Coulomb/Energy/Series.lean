/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.Energy.Basic
public import DLMF.Coulomb.Energy.Q2eRegular
public import DLMF.Bessel.Modified

/-!
# Coulomb functions `f`, `h`: power series in `r` and expansions in `ε` (DLMF §§33.19–33.20)

The power series of `f(ε,ℓ;r)` and `h(ε,ℓ;r)` in `r` (33.19.1–33.19.7), the Bessel forms at
`ε = 0` (33.20.1–33.20.2), the convergent expansion of `f` in powers of `ε` (33.20.3–33.20.6) and
the asymptotic expansion of `h` as `ε → 0` (33.20.7–33.20.9).

## Source correction: DLMF 33.19.3

Checked numerically (mpmath, 40 digits; `ε ∈ {0.3, 2.5, -0.13, -0.6}`, `ℓ ≤ 3`, both signs of
`r`, after fitting the series coefficients), 33.19.3 as printed fails in two ways:

* the finite sum `∑_{k=0}^{2ℓ} (2ℓ-k)! γ_k (2r)^{k-ℓ}/k!` must be doubled (as printed, the leading
  behaviour would be `h ~ (2ℓ)!/(2π(2r)^ℓ)`, contradicting 33.18.1 and §33.14(i));
* for `ε < 0` and `r < 0` the digamma terms must be evaluated at `κ = +(-ε)^{-1/2}` (the
  `r > 0` value of 33.14.6), not at `κ = -(-ε)^{-1/2}`.

The acquired statement `coulombh_hasSum` is
`2πh = 2∑_{k=0}^{2ℓ} (2ℓ-k)! γ_k (2r)^{k-ℓ}/k! - ∑ δ_k r^{k+ℓ+1}
  - A(ε,ℓ)(2 ln|2r/κ| + Re ψ(ℓ+1+κ) + Re ψ(-ℓ+κ)) f(ε,ℓ;r)` with `κ = coulombKappa ε 1`.
-/

@[expose] public section

open Complex Filter Asymptotics
open scoped Real Nat Topology

noncomputable section

namespace DLMF.Coulomb

open DLMF.Bessel

/-! ### Coefficients -/

/-- The initial values `α₀ = 2^{ℓ+1}/(2ℓ+1)!`, `α₁ = -α₀/(ℓ+1)` (DLMF 33.19.2). -/
@[dlmf 33.19.E2]
theorem coulombAlpha_zero_one (ε : ℝ) (ℓ : ℕ) :
    coulombAlpha ε ℓ 0 = 2 ^ (ℓ + 1) / (2 * ℓ + 1)! ∧
      coulombAlpha ε ℓ 1 = -coulombAlpha ε ℓ 0 / (ℓ + 1) :=
  ⟨rfl, rfl⟩

/-- The recurrence `k(k+2ℓ+1)α_k + 2α_{k-1} + εα_{k-2} = 0`, `k ≥ 2` (DLMF 33.19.2). -/
@[dlmf 33.19.E2]
theorem coulombAlpha_recurrence (ε : ℝ) (ℓ k : ℕ) (hk : 2 ≤ k) :
    k * (k + 2 * ℓ + 1) * coulombAlpha ε ℓ k + 2 * coulombAlpha ε ℓ (k - 1) +
      ε * coulombAlpha ε ℓ (k - 2) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simp only [Nat.add_sub_cancel, show j + 2 - 1 = j + 1 by omega]
  rw [coulombAlpha]
  have h : ((j : ℝ) + 2) * ((j : ℝ) + 2 + 2 * ℓ + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The recurrence `γ_k - γ_{k-1} + (1/4)(k-1)(k-2ℓ-2)εγ_{k-2} = 0`, `k ≥ 2`, with
`γ₀ = γ₁ = 1` (DLMF 33.19.4). -/
@[dlmf 33.19.E4]
theorem coulombGammaCoeff_recurrence (ε : ℝ) (ℓ k : ℕ) (hk : 2 ≤ k) :
    coulombGammaCoeff ε ℓ k - coulombGammaCoeff ε ℓ (k - 1) +
      ((k : ℝ) - 1) * ((k : ℝ) - 2 * ℓ - 2) * ε * coulombGammaCoeff ε ℓ (k - 2) / 4 = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simp only [Nat.add_sub_cancel, show j + 2 - 1 = j + 1 by omega]
  rw [coulombGammaCoeff]
  push_cast
  ring

/-- The recurrence 33.19.7 for `β_k`, `k ≥ 2`, with `β₀ = β₁ = 0`. -/
@[dlmf 33.19.E7]
theorem coulombBetaCoeff_recurrence (ε : ℝ) (ℓ k : ℕ) (hk : 2 ≤ k) :
    coulombBetaCoeff ε ℓ k - coulombBetaCoeff ε ℓ (k - 1) +
      ((k : ℝ) - 1) * ((k : ℝ) - 2 * ℓ - 2) * ε * coulombBetaCoeff ε ℓ (k - 2) / 4 +
      ((k : ℝ) - 1) * ε * coulombGammaCoeff ε ℓ (k - 2) / 2 = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simp only [Nat.add_sub_cancel, show j + 2 - 1 = j + 1 by omega]
  rw [coulombBetaCoeff]
  push_cast
  ring

/-- The recurrence 33.19.6 for `δ_k`, `k ≥ 2`:
`k(k+2ℓ+1)δ_k + 2δ_{k-1} + εδ_{k-2} + 2(2k+2ℓ+1)A(ε,ℓ)α_k = 0`. -/
@[dlmf 33.19.E6]
theorem coulombDeltaCoeff_recurrence (ε : ℝ) (ℓ k : ℕ) (hk : 2 ≤ k) :
    k * (k + 2 * ℓ + 1) * coulombDeltaCoeff ε ℓ k + 2 * coulombDeltaCoeff ε ℓ (k - 1) +
      ε * coulombDeltaCoeff ε ℓ (k - 2) +
      2 * (2 * k + 2 * ℓ + 1) * coulombAProd ε ℓ * coulombAlpha ε ℓ k = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simp only [Nat.add_sub_cancel, show j + 2 - 1 = j + 1 by omega]
  rw [coulombDeltaCoeff]
  have h : ((j : ℝ) + 2) * ((j : ℝ) + 2 + 2 * ℓ + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The initial values `δ₀`, `δ₁` of DLMF 33.19.5 (with `β₀ = β₁ = 0`). -/
@[dlmf 33.19.E5]
theorem coulombDeltaCoeff_zero_one (ε : ℝ) (ℓ : ℕ) :
    coulombDeltaCoeff ε ℓ 0 = (coulombBetaCoeff ε ℓ (2 * ℓ + 1) -
        2 * (digamma (2 * ℓ + 2) + digamma 1).re * coulombAProd ε ℓ) * coulombAlpha ε ℓ 0 ∧
      coulombDeltaCoeff ε ℓ 1 = (coulombBetaCoeff ε ℓ (2 * ℓ + 2) -
        2 * (digamma (2 * ℓ + 3) + digamma 2).re * coulombAProd ε ℓ) * coulombAlpha ε ℓ 1 ∧
      coulombBetaCoeff ε ℓ 0 = 0 ∧ coulombBetaCoeff ε ℓ 1 = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `C_{0,0} = 1`, `C_{1,0} = 0`, and `C_{k,p} = 0` for `p < 2k` or `p > 3k` (DLMF 33.20.6). -/
@[dlmf 33.20.E6]
theorem coulombCkp_eq_zero (ℓ : ℕ) :
    coulombCkp ℓ 0 0 = 1 ∧ coulombCkp ℓ 1 0 = 0 ∧
      ∀ k p : ℕ, (p < 2 * k ∨ 3 * k < p) → coulombCkp ℓ k p = 0 := by
  refine ⟨rfl, by simp [coulombCkp], ?_⟩
  intro k p hp
  cases k with
  | zero => simp only [coulombCkp]; split_ifs with h <;> first | rfl | omega
  | succ k => simp only [coulombCkp]; split_ifs with h <;> first | rfl | omega

/-- The recurrence `C_{k,p} = (-(2ℓ+p) C_{k-1,p-2} + C_{k-1,p-3})/(4p)` for `k > 0`,
`2k ≤ p ≤ 3k` (DLMF 33.20.6). -/
@[dlmf 33.20.E6]
theorem coulombCkp_recurrence (ℓ k p : ℕ) (hk : 0 < k) (hp : 2 * k ≤ p ∧ p ≤ 3 * k) :
    coulombCkp ℓ k p =
      (-(2 * (ℓ : ℝ) + p) * coulombCkp ℓ (k - 1) (p - 2) +
        (if 3 ≤ p then coulombCkp ℓ (k - 1) (p - 3) else 0)) / (4 * p) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have h2 : 2 ≤ p := by omega
  simp only [Nat.add_sub_cancel, coulombCkp, hp, h2, and_self, ↓reduceIte]

/-! ### Power series in `r` -/

/-- **DLMF 33.19.1**: `f(ε,ℓ;r) = r^{ℓ+1} ∑_{k≥0} α_k r^k`, convergent for all real `r` and
`ε`. -/
@[dlmf 33.19.E1]
theorem coulombf_hasSum (ε : ℝ) (ℓ : ℕ) (r : ℝ) :
    HasSum (fun k => coulombAlpha ε ℓ k * r ^ (k + ℓ + 1)) (coulombf ε ℓ r) := by
  have h := Complex.hasSum_re (q2e_Phi_hasSum ε ℓ r)
  rw [← q2e_coulombf_eq_re] at h
  convert h using 1
  funext k
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **DLMF 33.19.3, corrected** (see the module docstring): for `ε ≠ 0`, `r ≠ 0` and
`A(ε,ℓ) ≠ 0`, with `κ = coulombKappa ε 1` (the `r > 0` value of 33.14.6),
`∑_{k≥0} δ_k r^{k+ℓ+1} = 2∑_{k=0}^{2ℓ} (2ℓ-k)! γ_k (2r)^{k-ℓ}/k!
  - A(ε,ℓ)(2 ln|2r/κ| + Re ψ(ℓ+1+κ) + Re ψ(-ℓ+κ)) f(ε,ℓ;r) - 2π h(ε,ℓ;r)`.
The series converges for all `r ≠ 0`. -/
@[dlmf 33.19.E3]
theorem coulombh_hasSum {ε : ℝ} (hε : ε ≠ 0) (ℓ : ℕ) {r : ℝ} (hr : r ≠ 0)
    (hA : coulombAProd ε ℓ ≠ 0) :
    HasSum (fun k => coulombDeltaCoeff ε ℓ k * r ^ (k + ℓ + 1))
      (2 * ∑ k ∈ Finset.range (2 * ℓ + 1),
          (2 * ℓ - k)! * coulombGammaCoeff ε ℓ k / k ! * (2 * r) ^ ((k : ℤ) - ℓ) -
        coulombAProd ε ℓ * (2 * Real.log ‖(2 * r : ℂ) / coulombKappa ε 1‖ +
          (digamma (ℓ + 1 + coulombKappa ε 1)).re + (digamma (-ℓ + coulombKappa ε 1)).re) *
          coulombf ε ℓ r -
        2 * π * coulombh ε ℓ r) := by
  sorry

/-! ### `ε = 0`: Bessel functions -/

/-- `√(8r)/2 = √(2r)`. -/
lemma c33b_sqrt_eight (r : ℝ) : Real.sqrt (8 * r) / 2 = Real.sqrt (2 * r) := by
  rw [show 8 * r = 2 ^ 2 * (2 * r) by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num)]
  ring

/-- For `x ≥ 0`, `√x (√x)^{2ℓ+1} = x^{ℓ+1}`. -/
lemma c33b_pow_sqrt {x : ℝ} (hx : 0 ≤ x) (ℓ : ℕ) :
    (Real.sqrt x : ℂ) * (Real.sqrt x : ℂ) ^ (2 * ℓ + 1) = (x : ℂ) ^ (ℓ + 1) := by
  rw [← pow_succ', show 2 * ℓ + 1 + 1 = 2 * (ℓ + 1) by ring, pow_mul, ← Complex.ofReal_pow,
    Real.sq_sqrt hx]

/-- **DLMF 33.20.1 (`f`)**: `f(0,ℓ;r) = (2r)^{1/2} J_{2ℓ+1}((8r)^{1/2})` for `r > 0`. -/
@[dlmf 33.20.E1]
theorem coulombf_zero_eq_besselJ (ℓ : ℕ) {r : ℝ} (hr : 0 < r) :
    coulombf 0 ℓ r = Real.sqrt (2 * r) * (besselJ (2 * ℓ + 1) (Real.sqrt (8 * r))).re := by
  rw [← Complex.re_ofReal_mul]
  simp only [coulombf, ↓reduceIte]
  congr 1
  rw [Complex.besselJ, show (2 * (ℓ : ℂ) + 1) = ((2 * ℓ + 1 : ℕ) : ℂ) by push_cast; ring,
    cpow_natCast, show ((Real.sqrt (8 * r) : ℝ) : ℂ) / 2 = ((Real.sqrt (8 * r) / 2 : ℝ) : ℂ) by
      push_cast; ring, c33b_sqrt_eight r, ← mul_assoc, c33b_pow_sqrt (by positivity)]
  have hsq : ((Real.sqrt (2 * r) : ℝ) : ℂ) ^ 2 = 2 * r := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  rw [hsq, show (((2 * ℓ + 1 : ℕ) : ℂ)) + 1 = 2 * ℓ + 2 by push_cast; ring]
  push_cast
  ring

/-- **DLMF 33.20.2 (`f`)**: `f(0,ℓ;r) = (-1)^{ℓ+1} (2|r|)^{1/2} I_{2ℓ+1}((8|r|)^{1/2})` for
`r < 0`. -/
@[dlmf 33.20.E2]
theorem coulombf_zero_eq_besselI (ℓ : ℕ) {r : ℝ} (hr : r < 0) :
    coulombf 0 ℓ r =
      (-1) ^ (ℓ + 1) * Real.sqrt (2 * |r|) * (besselI (2 * ℓ + 1) (Real.sqrt (8 * |r|))).re := by
  rw [← Complex.re_ofReal_mul]
  simp only [coulombf, ↓reduceIte]
  congr 1
  rw [besselI, show (2 * (ℓ : ℂ) + 1) = ((2 * ℓ + 1 : ℕ) : ℂ) by push_cast; ring,
    cpow_natCast, show ((Real.sqrt (8 * |r|) : ℝ) : ℂ) / 2 = ((Real.sqrt (8 * |r|) / 2 : ℝ) : ℂ) by
      push_cast; ring, c33b_sqrt_eight |r|]
  have h2 : ((Real.sqrt (8 * |r|) : ℝ) : ℂ) ^ 2 / 4 = -(2 * (r : ℂ)) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity), abs_of_neg hr]
    push_cast; ring
  rw [h2]
  push_cast
  rw [show ((-1 : ℂ)) ^ (ℓ + 1) * (Real.sqrt (2 * |r|) : ℂ) *
      ((Real.sqrt (2 * |r|) : ℂ) ^ (2 * ℓ + 1) * regularizedHGFun ∅ {(2 * (ℓ : ℂ) + 1) + 1}
        (-(2 * (r : ℂ)))) =
      (-1) ^ (ℓ + 1) * ((Real.sqrt (2 * |r|) : ℂ) * (Real.sqrt (2 * |r|) : ℂ) ^ (2 * ℓ + 1)) *
        regularizedHGFun ∅ {(2 * (ℓ : ℂ) + 1) + 1} (-(2 * (r : ℂ))) by ring]
  have hp := c33b_pow_sqrt (abs_nonneg (2 * r)) ℓ
  rw [abs_mul, abs_two] at hp
  rw [hp, abs_of_neg hr, Multiset.empty_eq_zero,
    show (2 * (ℓ : ℂ) + 1) + 1 = 2 * ℓ + 2 by ring]
  push_cast
  have hm : ((-1 : ℂ)) ^ (ℓ + 1) * (2 * -(r : ℂ)) ^ (ℓ + 1) = (2 * r) ^ (ℓ + 1) := by
    rw [← mul_pow]; congr 1; ring
  linear_combination (-(regularizedHGFun 0 {2 * (ℓ : ℂ) + 2} (-(2 * (r : ℂ))))) * hm

/-- **DLMF 33.20.1 (`h`)**: `h(0,ℓ;r) = -(2r)^{1/2} Y_{2ℓ+1}((8r)^{1/2})` for `r > 0`. -/
@[dlmf 33.20.E1]
theorem coulombh_zero_eq_besselY (ℓ : ℕ) {r : ℝ} (hr : 0 < r) :
    coulombh 0 ℓ r = -(Real.sqrt (2 * r) * (besselY (2 * ℓ + 1) (Real.sqrt (8 * r))).re) := by
  sorry

/-- **DLMF 33.20.2 (`h`)**: `h(0,ℓ;r) = (-1)^ℓ (2/π) (2|r|)^{1/2} K_{2ℓ+1}((8|r|)^{1/2})` for
`r < 0`. -/
@[dlmf 33.20.E2]
theorem coulombh_zero_eq_besselK (ℓ : ℕ) {r : ℝ} (hr : r < 0) :
    coulombh 0 ℓ r =
      (-1) ^ ℓ * (2 / π) * Real.sqrt (2 * |r|) *
        (besselK (2 * ℓ + 1) (Real.sqrt (8 * |r|))).re := by
  sorry

/-! ### Expansions in `ε` -/

/-- **DLMF 33.20.3–33.20.4**: for `r > 0` and every real `ε`,
`f(ε,ℓ;r) = ∑_{k≥0} ε^k 𝖥_k(ℓ;r)` with
`𝖥_k(ℓ;r) = ∑_{p=2k}^{3k} (2r)^{(p+1)/2} C_{k,p} J_{2ℓ+1+p}((8r)^{1/2})`. -/
@[dlmf 33.20.E3, dlmf 33.20.E4]
theorem coulombf_hasSum_eps_pos (ε : ℝ) (ℓ : ℕ) {r : ℝ} (hr : 0 < r) :
    HasSum (fun k : ℕ => ε ^ k * ∑ p ∈ Finset.Icc (2 * k) (3 * k),
        (2 * r) ^ (((p : ℝ) + 1) / 2) * coulombCkp ℓ k p *
          (besselJ (2 * ℓ + 1 + p) (Real.sqrt (8 * r))).re)
      (coulombf ε ℓ r) := by
  sorry

/-- **DLMF 33.20.3, 33.20.5**: for `r < 0` and every real `ε`,
`f(ε,ℓ;r) = ∑_{k≥0} ε^k 𝖥_k(ℓ;r)` with
`𝖥_k(ℓ;r) = ∑_{p=2k}^{3k} (-1)^{ℓ+1+p} (2|r|)^{(p+1)/2} C_{k,p} I_{2ℓ+1+p}((8|r|)^{1/2})`. -/
@[dlmf 33.20.E3, dlmf 33.20.E5]
theorem coulombf_hasSum_eps_neg (ε : ℝ) (ℓ : ℕ) {r : ℝ} (hr : r < 0) :
    HasSum (fun k : ℕ => ε ^ k * ∑ p ∈ Finset.Icc (2 * k) (3 * k),
        (-1) ^ (ℓ + 1 + p) * (2 * |r|) ^ (((p : ℝ) + 1) / 2) * coulombCkp ℓ k p *
          (besselI (2 * ℓ + 1 + p) (Real.sqrt (8 * |r|))).re)
      (coulombf ε ℓ r) := by
  sorry

/-- **DLMF 33.20.7–33.20.8**: for `r > 0`, as `ε → 0` (from either side),
`h(ε,ℓ;r) ~ -A(ε,ℓ) ∑_{k≥0} ε^k 𝖧_k(ℓ;r)` with
`𝖧_k(ℓ;r) = ∑_{p=2k}^{3k} (2r)^{(p+1)/2} C_{k,p} Y_{2ℓ+1+p}((8r)^{1/2})`, in the sense that
`h + A ∑_{k=0}^{n} ε^k 𝖧_k = O(ε^{n+1})` for every `n`. -/
@[dlmf 33.20.E7, dlmf 33.20.E8]
theorem coulombh_asymptotic_eps_pos (ℓ : ℕ) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (fun ε : ℝ => coulombh ε ℓ r + coulombAProd ε ℓ * ∑ k ∈ Finset.range (n + 1), ε ^ k *
        ∑ p ∈ Finset.Icc (2 * k) (3 * k), (2 * r) ^ (((p : ℝ) + 1) / 2) * coulombCkp ℓ k p *
          (besselY (2 * ℓ + 1 + p) (Real.sqrt (8 * r))).re)
      =O[𝓝[≠] 0] (fun ε : ℝ => ε ^ (n + 1)) := by
  sorry

/-- **DLMF 33.20.7, 33.20.9**: for `r < 0`, as `ε → 0`,
`h(ε,ℓ;r) ~ -A(ε,ℓ) ∑_{k≥0} ε^k 𝖧_k(ℓ;r)` with
`𝖧_k(ℓ;r) = (-1)^{ℓ+1} (2/π) ∑_{p=2k}^{3k} (2|r|)^{(p+1)/2} C_{k,p} K_{2ℓ+1+p}((8|r|)^{1/2})`. -/
@[dlmf 33.20.E7, dlmf 33.20.E9]
theorem coulombh_asymptotic_eps_neg (ℓ : ℕ) {r : ℝ} (hr : r < 0) (n : ℕ) :
    (fun ε : ℝ => coulombh ε ℓ r + coulombAProd ε ℓ * ∑ k ∈ Finset.range (n + 1), ε ^ k *
        ((-1) ^ (ℓ + 1) * (2 / π) * ∑ p ∈ Finset.Icc (2 * k) (3 * k),
          (2 * |r|) ^ (((p : ℝ) + 1) / 2) * coulombCkp ℓ k p *
            (besselK (2 * ℓ + 1 + p) (Real.sqrt (8 * |r|))).re))
      =O[𝓝[≠] 0] (fun ε : ℝ => ε ^ (n + 1)) := by
  sorry

end DLMF.Coulomb
