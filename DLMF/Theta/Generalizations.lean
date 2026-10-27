/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Relations

/-!
# Theta functions: generalizations and analogs (DLMF §20.11)

The Gauss sum `G(m,n)` and its reciprocity law (20.11.1–20.11.2), Ramanujan's theta function
`f(a,b)` (20.11.3–20.11.4), Ramanujan's change of base `₂F₁(1/2,1/2;1;k²) = θ₃²(0|τ)` (20.11.5,
rectangular case `τ = it` with Mathlib's series `₂F₁`), and the twelve combined theta functions
`φ_{m,n}` of Carlson with their permutation symmetry (20.11.6–20.11.9).

Theta functions with characteristics (§20.11(iv)) are the one-dimensional case of the Riemann theta
functions of DLMF Chapter 21 and are acquired there.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic

/-! ### §20.11(i) Gauss sum -/

/-- DLMF 20.11.1: the Gauss sum `G(m,n) = ∑_{k=0}^{n-1} e^{-πik²m/n}` (DLMF assumes `m, n` coprime,
`n > 0`, `mn` even). -/
@[dlmf 20.11.E1]
def thetaGaussSum (m : ℤ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n, cexp (-(π * I * k ^ 2 * m / n))

/-- DLMF 20.11.2: for coprime positive `m, n` with `mn` even,
`n^{-1/2} G(m,n) = e^{-πi/4} m^{-1/2} ∑_{j=0}^{m-1} e^{πij²n/m} = e^{-πi/4} m^{-1/2} G(-n,m)`. -/
@[dlmf 20.11.E2]
theorem thetaGaussSum_reciprocity {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n)
    (heven : Even (m * n)) :
    1 / Real.sqrt n * thetaGaussSum m n =
        cexp (-(π * I / 4)) / Real.sqrt m *
          ∑ j ∈ Finset.range m, cexp (π * I * j ^ 2 * n / m) ∧
      cexp (-(π * I / 4)) / Real.sqrt m * ∑ j ∈ Finset.range m, cexp (π * I * j ^ 2 * n / m) =
        cexp (-(π * I / 4)) / Real.sqrt m * thetaGaussSum (-(n : ℤ)) m := by
  refine ⟨?_, ?_⟩
  · sorry
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    push_cast
    ring

/-! ### §20.11(ii) Ramanujan's theta function -/

/-- DLMF 20.11.3: Ramanujan's theta function `f(a,b) = ∑_{n∈ℤ} a^{n(n+1)/2} b^{n(n-1)/2}`,
`|ab| < 1` (the exponents are integers). -/
@[dlmf 20.11.E3]
def ramanujanThetaF (a b : ℂ) : ℂ := ∑' n : ℤ, a ^ (n * (n + 1) / 2) * b ^ (n * (n - 1) / 2)

/-- DLMF 20.11.4: `f(q e^{2iz}, q e^{-2iz}) = θ₃(z|τ)`, `q = e^{iπτ}` (for every `τ`). -/
@[dlmf 20.11.E4]
theorem ramanujanThetaF_eq_jacobiThetaThreeTau (z τ : ℂ) :
    ramanujanThetaF (cexp (π * I * τ) * cexp (2 * I * z)) (cexp (π * I * τ) * cexp (-(2 * I * z))) =
      jacobiThetaThreeTau z τ := by
  rw [ramanujanThetaF, jacobiThetaThreeTau_eq_tsum]
  refine tsum_congr fun n => ?_
  have hA : ((n * (n + 1) / 2 : ℤ) : ℂ) * 2 = n * (n + 1) := by
    exact_mod_cast Int.ediv_mul_cancel (Int.even_mul_succ_self n).two_dvd
  have hB : ((n * (n - 1) / 2 : ℤ) : ℂ) * 2 = n * (n - 1) := by
    exact_mod_cast Int.ediv_mul_cancel (Int.even_mul_pred_self n).two_dvd
  rw [← exp_add, ← exp_add, th20_exp_zpow, th20_exp_zpow, ← exp_add]
  congr 1
  linear_combination (π * I * τ + 2 * I * z) / 2 * hA + (π * I * τ - 2 * I * z) / 2 * hB

/-- `∑ r^{m(m-1)/2} A^m` converges for `0 ≤ r < 1`, `A ≥ 0` (helper). -/
lemma p20R1_summable_quad {r A : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hA : 0 ≤ A) :
    Summable (fun m : ℕ => r ^ (m * (m - 1) / 2) * A ^ m) := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, r ^ M * A ≤ 1 / 2 := by
    have ht : Tendsto (fun M : ℕ => r ^ M * A) atTop (𝓝 (0 * A)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).mul_const A
    rw [zero_mul] at ht
    exact ((ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists).imp
      fun _ h => h.le
  refine Summable.of_norm_bounded_eventually_nat
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) ?_
  filter_upwards [eventually_ge_atTop (2 * M + 1)] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hexp : M * m ≤ m * (m - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : 2 * M ≤ m - 1 := by omega
    calc M * m * 2 = (2 * M) * m := by ring
      _ ≤ (m - 1) * m := Nat.mul_le_mul_right _ this
      _ = m * (m - 1) := by ring
  calc r ^ (m * (m - 1) / 2) * A ^ m ≤ r ^ (M * m) * A ^ m := by
        exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hr0 hr.le hexp) (by positivity)
    _ = (r ^ M * A) ^ m := by rw [mul_pow, pow_mul]
    _ ≤ (1 / 2) ^ m := by gcongr


/-- `m(m+1)/2 = m(m-1)/2 + m` in `ℕ` (helper). -/
lemma p20R1_tri_succ (m : ℕ) : m * (m + 1) / 2 = m * (m - 1) / 2 + m := by
  have h : m * (m + 1) = m * (m - 1) + 2 * m := by
    rcases m with _ | k
    · simp
    · simp only [Nat.add_sub_cancel]; ring
  rw [h, Nat.add_mul_div_left _ _ two_pos]

/-- DLMF §20.11(ii): `f(a,b)` converges absolutely for `|ab| < 1`. -/
@[dlmf 20.11.ii]
theorem summable_ramanujanThetaF {a b : ℂ} (hab : ‖a * b‖ < 1) :
    Summable (fun n : ℤ => ‖a ^ (n * (n + 1) / 2) * b ^ (n * (n - 1) / 2)‖) := by
  have hr0 : 0 ≤ ‖a * b‖ := norm_nonneg _
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine (p20R1_summable_quad hr0 hab (norm_nonneg a)).congr fun m => ?_
    have e1 : (m : ℤ) * ((m : ℤ) + 1) / 2 = ((m * (m + 1) / 2 : ℕ) : ℤ) := by push_cast; ring_nf
    have e2 : (m : ℤ) * ((m : ℤ) - 1) / 2 = ((m * (m - 1) / 2 : ℕ) : ℤ) := by
      rcases m with _ | k
      · simp
      · push_cast; ring_nf
    symm
    rw [e1, e2, zpow_natCast, zpow_natCast, norm_mul, norm_pow, norm_pow, p20R1_tri_succ, pow_add,
      norm_mul, mul_pow]
    ring
  · have hs := (summable_nat_add_iff 1).mpr (p20R1_summable_quad hr0 hab (norm_nonneg b))
    refine hs.congr fun m => ?_
    have e1 : (-((m : ℤ) + 1)) * (-((m : ℤ) + 1) + 1) / 2 = ((m * (m + 1) / 2 : ℕ) : ℤ) := by
      push_cast; ring_nf
    have e2 : (-((m : ℤ) + 1)) * (-((m : ℤ) + 1) - 1) / 2 =
        (((m + 1) * (m + 1 + 1) / 2 : ℕ) : ℤ) := by
      push_cast; ring_nf
    symm
    rw [e1, e2, zpow_natCast, zpow_natCast, norm_mul, norm_pow, norm_pow, p20R1_tri_succ (m + 1),
      pow_add, norm_mul, mul_pow, Nat.add_sub_cancel, show (m + 1) * m = m * (m + 1) by ring]
    ring

/-! ### §20.11(iii) Ramanujan's change of base -/

/-- DLMF 20.11.5 (rectangular case `τ = it`, `t > 0`): `₂F₁(1/2, 1/2; 1; k²) = θ₃²(0|τ)` with
`k = θ₂²(0|τ)/θ₃²(0|τ)` (20.9.1); equivalent to the first of 20.9.2 by DLMF 19.5.1. -/
@[dlmf 20.11.E5]
theorem ordinaryHypergeometric_half_half_one_thetaModulusK {t : ℝ} (ht : 0 < t) :
    ₂F₁ (1 / 2 : ℂ) (1 / 2) 1 (thetaModulusK (I * t) ^ 2) =
      jacobiThetaThreeNullTau (I * t) ^ 2 := by
  obtain ⟨h0, h1, -⟩ := DLMF.JacobiElliptic.p22R1_real_at ht
  obtain ⟨-, hK, -⟩ := compEllIntK_eq_jacobiThetaThreeNullTau ht
  rw [p22R1_thetaModulusK_I_mul ht] at hK ⊢
  simp only [ofReal_re] at hK
  have hm : |DLMF.JacobiElliptic.p22R1_rho t ^ 2| < 1 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  rw [Real.compEllIntKm_eq_ordinaryHypergeometric hm] at hK
  have hpi : (π : ℂ) / 2 ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : π / 2 ≠ 0)
  push_cast at hK
  exact mul_left_cancel₀ hpi hK

/-! ### §20.11(v) Permutation symmetry -/

/-- The normalizing constants of Carlson's combined theta functions: `θ₁'(0|τ)` for `j = 1` and
`θⱼ(0|τ)` for `j = 2, 3, 4`. -/
def th20_combinedConst (j : ℕ) (τ : ℂ) : ℂ :=
  if j = 1 then jacobiThetaOneDerivNullTau τ else jacobiThetaTau j 0 τ

/-- DLMF 20.11.6–20.11.8: the twelve combined theta functions
`φ_{m,n}(z,q) = c_n θ_m(z|τ)/(c_m θ_n(z|τ))` for `m ≠ n` in `{1,2,3,4}`, where `c₁ = θ₁'(0|τ)` and
`cⱼ = θⱼ(0|τ)` for `j = 2,3,4`; this single formula is 20.11.6 (`n = 1`), 20.11.7 (`m = 1`) and
20.11.8 (`m, n ≥ 2`). -/
@[dlmf 20.11.E6]
def combinedTheta (m n : ℕ) (z τ : ℂ) : ℂ :=
  th20_combinedConst n τ * jacobiThetaTau m z τ / (th20_combinedConst m τ * jacobiThetaTau n z τ)

/-- DLMF 20.11.6: `φ_{m,1} = θ₁'(0) θ_m(z)/(θ_m(0) θ₁(z))`, `m = 2,3,4`. -/
@[dlmf 20.11.E6]
theorem combinedTheta_m_one (m : ℕ) (hm : m ≠ 1) (z τ : ℂ) :
    combinedTheta m 1 z τ = jacobiThetaOneDerivNullTau τ * jacobiThetaTau m z τ /
      (jacobiThetaTau m 0 τ * jacobiThetaOneTau z τ) := by
  simp [combinedTheta, th20_combinedConst, hm, jacobiThetaTau]

/-- DLMF 20.11.7: `φ_{1,n} = θ_n(0) θ₁(z)/(θ₁'(0) θ_n(z))`, `n = 2,3,4`. -/
@[dlmf 20.11.E7]
theorem combinedTheta_one_n (n : ℕ) (hn : n ≠ 1) (z τ : ℂ) :
    combinedTheta 1 n z τ = jacobiThetaTau n 0 τ * jacobiThetaOneTau z τ /
      (jacobiThetaOneDerivNullTau τ * jacobiThetaTau n z τ) := by
  simp [combinedTheta, th20_combinedConst, hn, jacobiThetaTau]

/-- DLMF 20.11.8: `φ_{m,n} = θ_n(0) θ_m(z)/(θ_m(0) θ_n(z))`, `m, n = 2,3,4`. -/
@[dlmf 20.11.E8]
theorem combinedTheta_m_n (m n : ℕ) (hm : m ≠ 1) (hn : n ≠ 1) (z τ : ℂ) :
    combinedTheta m n z τ = jacobiThetaTau n 0 τ * jacobiThetaTau m z τ /
      (jacobiThetaTau m 0 τ * jacobiThetaTau n z τ) := by
  simp [combinedTheta, th20_combinedConst, hm, hn]

/-- DLMF 20.11.9: `φ_{m,n} = φ_{m,1} φ_{1,n} = 1/φ_{n,m} = φ_{m,1}/φ_{n,1} = φ_{1,n}/φ_{1,m}`, for
`m, n ∈ {1,2,3,4}`, `m ≠ n`, at points `z` where `θ₁(z), θ_m(z), θ_n(z)` do not vanish, given that
the normalizing constants do not vanish (true for `Im τ > 0`).
Corrected from the printed DLMF formula: the nonvanishing hypotheses are added, since with
Lean's `x / 0 = 0` the quotient identities are false at the zeros of the theta functions. -/
@[dlmf 20.11.E9]
theorem combinedTheta_symmetry {m n : ℕ} {z τ : ℂ}
    (hc1 : th20_combinedConst 1 τ ≠ 0) (hcm : th20_combinedConst m τ ≠ 0)
    (hcn : th20_combinedConst n τ ≠ 0) (h1 : jacobiThetaTau 1 z τ ≠ 0)
    (hm : jacobiThetaTau m z τ ≠ 0) (hn : jacobiThetaTau n z τ ≠ 0) :
    combinedTheta m n z τ = combinedTheta m 1 z τ * combinedTheta 1 n z τ ∧
      combinedTheta m n z τ = 1 / combinedTheta n m z τ ∧
      combinedTheta m n z τ = combinedTheta m 1 z τ / combinedTheta n 1 z τ ∧
      combinedTheta m n z τ = combinedTheta 1 n z τ / combinedTheta 1 m z τ := by
  simp only [combinedTheta]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp

/-- The normalizing constants of the combined theta functions do not vanish for `Im τ > 0`. -/
lemma th20_combinedConst_ne_zero {τ : ℂ} (hτ : 0 < τ.im) {j : ℕ} (hj1 : 1 ≤ j) (hj4 : j ≤ 4) :
    th20_combinedConst j τ ≠ 0 := by
  obtain ⟨h2, h3, h4⟩ := jacobiThetaNullTau_ne_zero hτ
  interval_cases j
  · simp only [th20_combinedConst, ite_true]
    rw [jacobiThetaOneDerivNullTau_eq_mul hτ]
    exact mul_ne_zero (mul_ne_zero h2 h3) h4
  · simpa [th20_combinedConst, jacobiThetaTau] using h2
  · simpa [th20_combinedConst, jacobiThetaTau] using h3
  · simpa [th20_combinedConst, jacobiThetaTau] using h4

end DLMF.Theta

end
