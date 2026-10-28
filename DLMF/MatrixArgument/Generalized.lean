/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.MatrixArgument.Zonal
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-!
# Generalized hypergeometric functions of matrix argument (DLMF §35.8)

The series `hypergeometricPFQ a b T` (35.8.1) is defined in `DLMF.MatrixArgument.Basic`. This
file proves

* the partitions of weight `k` (`mem_partitions`, `partitions_zero`), and the nonvanishing of
  `[b]_κ` when `Γ_m(b) ≠ 0` (which is DLMF's condition `-b + (j+1)/2 ∉ ℕ`, `1 ≤ j ≤ m`);
* termination when some `a_j` is a nonpositive integer (§35.8(i), **corrected**, see below);
* 35.8.8 (`hypergeometricPFQ_zero`), 35.8.11 (`hypergeometricPFQ_conj`), the first equality of
  35.8.3 (`hyp2F1_self_right`) and 35.8.4 (`besselA_eq_hyp0F1`);
* the case `m = 1`: the series reduces to the classical one (`hypergeometricPFQ_fin_one`), and
  `₂F₁` is Mathlib's `ordinaryHypergeometric` (`hyp2F1_fin_one`).

The convergence statements of §35.8(i), 35.8.2, the second equality of 35.8.3, the `₃F₂`
formulas 35.8.5–35.8.7, the confluence limits 35.8.9–35.8.10 and the integrals 35.8.12–35.8.13
are admitted.

**Source corrections** (all checked numerically for `m = 2` with zonal polynomials computed
from 35.4.2–35.4.3, and for `m = 1` against mpmath):

* §35.8(i), first paragraph: DLMF says the series terminates if `-a_j + (k+1)/2 ∈ ℕ` for some
  `1 ≤ k ≤ m`. Only `k = 1` (`a_j ∈ {0, -1, -2, …}`) gives termination: for `k ≥ 2` the factor
  `(a_j - (k-1)/2)_{κ_k}` vanishes only on partitions with `κ_k` large, and the partitions
  `(n, 0, …, 0)` still contribute (for `m = 2`, `a = 1/2`: `[1/2]_{(n,0)} = (1/2)_n ≠ 0`).
* 35.8.6 (Pfaff–Saalschütz): the printed right-hand side is the reciprocal of the correct one;
  already for `m = 1` it contradicts the classical formula 16.4.3.
* 35.8.7 (Thomae): the numerator parameter `b₂ - a₂` must be `b₂ - a₁`, and `Γ(c)`, `Γ(c + a₃)`
  must be `Γ_m(c)`, `Γ_m(c + a₃)`; for `m = 1` it is then the classical Thomae relation.
* 35.8.13 (Euler integral): the factor is `B_m(b₁ - a₁, a₁)`, not its reciprocal
  (compare 35.6.4; for `m = 1`, `p = q = 0` the printed formula fails).
-/

@[expose] public noncomputable section

open MeasureTheory Matrix Finset Filter
open scoped Nat MatrixOrder Topology

namespace DLMF.MatrixArgument

/-! ## Partitions -/

/-- Formula under the stated hypotheses: `κ ∈ partitions m k ↔ Antitone κ ∧ ∑ j, κ j = k`. -/
theorem mem_partitions {m k : ℕ} {κ : Fin m → ℕ} :
    κ ∈ partitions m k ↔ Antitone κ ∧ ∑ j, κ j = k := by
  unfold partitions
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨fun i j hij => h1 i j hij, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun i j hij => h1 hij, h2⟩
    have := Finset.single_le_sum (fun i _ => Nat.zero_le (κ i)) (Finset.mem_univ j)
    omega

/-- Identity under the stated parameter and domain assumptions: `partitions m 0 = {0}`. -/
theorem partitions_zero (m : ℕ) : partitions m 0 = {0} := by
  ext κ
  rw [mem_partitions, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    funext j
    exact (Finset.sum_eq_zero_iff.mp h) j (Finset.mem_univ _)
  · rintro rfl
    exact ⟨fun _ _ _ => le_rfl, by simp⟩

/-- Identity under the stated parameter and domain assumptions: `partitions 1 k = {fun _ => k}`. -/
theorem partitions_fin_one (k : ℕ) : partitions 1 k = {fun _ => k} := by
  ext κ
  rw [mem_partitions, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    funext j
    rw [Subsingleton.elim j 0]
    simpa using h
  · rintro rfl
    exact ⟨fun _ _ _ => le_rfl, by simp⟩

/-- Identity under the stated parameter and domain assumptions: `partitionalShiftedFactorial a (0
: Fin m → ℕ) = 1`. -/
theorem partitionalShiftedFactorial_zero {𝕜 : Type*} [Field 𝕜] {m : ℕ} (a : 𝕜) :
    partitionalShiftedFactorial a (0 : Fin m → ℕ) = 1 := by
  simp [partitionalShiftedFactorial]

/-- If `Γ_m(b) ≠ 0` (equivalently `-b + (j+1)/2 ∉ ℕ` for `1 ≤ j ≤ m`), no `[b]_κ` vanishes. -/
theorem partitionalShiftedFactorial_ne_zero {m : ℕ} {b : ℂ} (hb : multivariateGamma m b ≠ 0)
    (κ : Fin m → ℕ) : partitionalShiftedFactorial b κ ≠ 0 := by
  unfold multivariateGamma at hb
  have hΓ : ∀ j : Fin m, Complex.Gamma (b - (j : ℂ) / 2) ≠ 0 :=
    fun j => Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hb) j (Finset.mem_univ _)
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  intro h
  obtain ⟨i, -, hi⟩ := (ascPochhammer_eval_eq_zero_iff _ _).mp h
  apply hΓ j
  rw [Complex.Gamma_eq_zero_iff]
  exact ⟨i, by rw [hi]; ring⟩

/-! ## §35.8(i) Termination and convergence -/

/-- DLMF §35.8(i) (**corrected**): if some numerator parameter is a nonpositive integer,
`a_i = -n`, then `[a_i]_κ = 0` whenever `|κ| > mn`, so the series 35.8.1 terminates. DLMF
states termination under `-a_j + (k+1)/2 ∈ ℕ` for some `1 ≤ k ≤ m`; only `k = 1` is correct
(see the module docstring). -/
@[dlmf 35.8.i "corrected: termination only for a_j a nonpositive integer (k = 1)"]
theorem hypergeometricPFQ_eq_sum_of_neg_nat {m p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (T : Matrix (Fin m) (Fin m) ℝ) {i : Fin p} {n : ℕ} (hn : a i = -n) :
    hypergeometricPFQ a b T = ∑ k ∈ Finset.range (m * n + 1), (1 / (k ! : ℂ)) *
      ∑ κ ∈ partitions m k, (∏ i, partitionalShiftedFactorial (a i) κ) /
        (∏ j, partitionalShiftedFactorial (b j) κ) * (zonalPolynomial κ T : ℂ) := by
  unfold hypergeometricPFQ
  refine tsum_eq_sum fun k hk => ?_
  rw [Finset.mem_range, not_lt] at hk
  rw [Finset.sum_eq_zero, mul_zero]
  intro κ hκ
  obtain ⟨hanti, hw⟩ := mem_partitions.mp hκ
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp at hw
    omega
  have h0 : n < κ ⟨0, hm⟩ := by
    by_contra hc
    rw [not_lt] at hc
    have hle : ∑ j, κ j ≤ ∑ _j : Fin m, n :=
      Finset.sum_le_sum fun j _ => (hanti (Fin.le_def.mpr (Nat.zero_le j.1))).trans hc
    simp at hle
    omega
  have hz : partitionalShiftedFactorial (a i) κ = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨0, hm⟩) ?_
    simp only [Nat.cast_zero, zero_div, sub_zero, hn]
    exact ascPochhammer_eval_neg_coe_nat_of_lt h0
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, zero_div, zero_mul]

/-- DLMF §35.8(i): for `p ≤ q` the series 35.8.1 converges absolutely for every `T ∈ 𝓢`
(the double series over `k` and `|κ| = k` of absolute values converges), and its sum is
`hypergeometricPFQ a b T`. -/
@[dlmf 35.8.i]
theorem hypergeometricPFQ_summable_of_le {m p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (hb : ∀ j, multivariateGamma m (b j) ≠ 0) (hpq : p ≤ q)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.IsHermitian) :
    Summable (fun k : ℕ => ∑ κ ∈ partitions m k, ‖(∏ i, partitionalShiftedFactorial (a i) κ) /
        (∏ j, partitionalShiftedFactorial (b j) κ) * (zonalPolynomial κ T : ℂ)‖ / (k ! : ℝ)) ∧
      HasSum (fun k : ℕ => (1 / (k ! : ℂ)) * ∑ κ ∈ partitions m k,
        (∏ i, partitionalShiftedFactorial (a i) κ) / (∏ j, partitionalShiftedFactorial (b j) κ) *
          (zonalPolynomial κ T : ℂ)) (hypergeometricPFQ a b T) := by
  sorry

/-- DLMF §35.8(i): for `p = q + 1` the series 35.8.1 converges absolutely for `‖T‖ < 1`. -/
@[dlmf 35.8.i]
theorem hypergeometricPFQ_summable_of_eq_succ {m p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (hb : ∀ j, multivariateGamma m (b j) ≠ 0) (hpq : p = q + 1)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.IsHermitian) (hT1 : matrixSpectralNorm T < 1) :
    Summable (fun k : ℕ => ∑ κ ∈ partitions m k, ‖(∏ i, partitionalShiftedFactorial (a i) κ) /
        (∏ j, partitionalShiftedFactorial (b j) κ) * (zonalPolynomial κ T : ℂ)‖ / (k ! : ℝ)) ∧
      HasSum (fun k : ℕ => (1 / (k ! : ℂ)) * ∑ κ ∈ partitions m k,
        (∏ i, partitionalShiftedFactorial (a i) κ) / (∏ j, partitionalShiftedFactorial (b j) κ) *
          (zonalPolynomial κ T : ℂ)) (hypergeometricPFQ a b T) := by
  sorry

/-- DLMF §35.8(i): for `p = q + 1` and `‖T‖ > 1` the series 35.8.1 diverges (its absolute
series diverges), unless it terminates; non-termination is the hypothesis that no `a_i` is a
nonpositive integer (see `hypergeometricPFQ_eq_sum_of_neg_nat`). -/
@[dlmf 35.8.i]
theorem not_summable_hypergeometricPFQ_of_eq_succ {m p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (ha : ∀ i (n : ℕ), a i ≠ -n) (hb : ∀ j, multivariateGamma m (b j) ≠ 0) (hpq : p = q + 1)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.IsHermitian) (hT1 : 1 < matrixSpectralNorm T) :
    ¬ Summable (fun k : ℕ => ∑ κ ∈ partitions m k, ‖(∏ i, partitionalShiftedFactorial (a i) κ) /
        (∏ j, partitionalShiftedFactorial (b j) κ) * (zonalPolynomial κ T : ℂ)‖ / (k ! : ℝ)) := by
  sorry

/-- DLMF §35.8(i): for `p > q + 1` the series 35.8.1 diverges for every `T ≠ 0` in `𝓢`, unless
it terminates (no `a_i` is a nonpositive integer). -/
@[dlmf 35.8.i]
theorem not_summable_hypergeometricPFQ_of_lt {m p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (ha : ∀ i (n : ℕ), a i ≠ -n) (hb : ∀ j, multivariateGamma m (b j) ≠ 0) (hpq : q + 1 < p)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.IsHermitian) (hT0 : T ≠ 0) :
    ¬ Summable (fun k : ℕ => ∑ κ ∈ partitions m k, ‖(∏ i, partitionalShiftedFactorial (a i) κ) /
        (∏ j, partitionalShiftedFactorial (b j) κ) * (zonalPolynomial κ T : ℂ)‖ / (k ! : ℝ)) := by
  sorry

/-! ## §35.8(iv) General properties -/

/-- DLMF 35.8.8: `pFq(a; b; 0) = 1`. -/
@[dlmf 35.8.E8]
theorem hypergeometricPFQ_zero {m p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) :
    hypergeometricPFQ (m := m) a b 0 = 1 := by
  unfold hypergeometricPFQ
  rw [tsum_eq_single 0]
  · simp [partitions_zero, zonalPolynomial_zero, partitionalShiftedFactorial_zero]
  · intro k hk
    rw [Finset.sum_eq_zero, mul_zero]
    intro κ hκ
    have hne : κ ≠ 0 := by
      rintro rfl
      exact hk (by simpa using (mem_partitions.mp hκ).2.symm)
    simp [zonalPolynomial_zero, hne]

/-- DLMF 35.8.11: `pFq(a; b; H T H⁻¹) = pFq(a; b; T)` for `H ∈ O(m)`. -/
@[dlmf 35.8.E11]
theorem hypergeometricPFQ_conj {m p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (H : Matrix.orthogonalGroup (Fin m) ℝ) (T : Matrix (Fin m) (Fin m) ℝ) :
    hypergeometricPFQ a b ((H : Matrix (Fin m) (Fin m) ℝ) * T * (H : Matrix (Fin m) (Fin m) ℝ)⁻¹)
      = hypergeometricPFQ a b T := by
  unfold hypergeometricPFQ
  simp_rw [zonalPolynomial_conj]

/-! ## §35.8(ii) Relations to other functions -/

/-- DLMF 35.8.2: `₀F₀(−; −; T) = etr(T)` for `T ∈ 𝓢`. -/
@[dlmf 35.8.E2]
theorem hyp0F0_eq_etr {m : ℕ} (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.IsHermitian) :
    hyp0F0 T = (etr T : ℂ) := by
  sorry

/-- DLMF 35.8.3 (first equality): `₂F₁(a, b; b; T) = ₁F₀(a; −; T)` when `Γ_m(b) ≠ 0`. -/
@[dlmf 35.8.E3]
theorem hyp2F1_self_right {m : ℕ} (a b : ℂ) (hb : multivariateGamma m b ≠ 0)
    (T : Matrix (Fin m) (Fin m) ℝ) : hyp2F1 a b b T = hyp1F0 a T := by
  unfold hyp2F1 hyp1F0 hypergeometricPFQ
  congr 1
  funext k
  congr 1
  refine Finset.sum_congr rfl fun κ _ => ?_
  have h := partitionalShiftedFactorial_ne_zero hb κ
  simp only [Fin.prod_univ_two, Fin.prod_univ_one, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one, div_one]
  rw [mul_div_assoc, div_self h, mul_one]

/-- DLMF 35.8.3 (second equality): `₁F₀(a; −; T) = |I - T|^{-a}` for `0 < T < I`. -/
@[dlmf 35.8.E3]
theorem hyp1F0_eq_det_cpow {m : ℕ} (a : ℂ) {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef)
    (hT1 : (1 - T).PosDef) : hyp1F0 a T = (((1 - T).det : ℝ) : ℂ) ^ (-a) := by
  sorry

/-- DLMF 35.8.4: `A_ν(T) = ₀F₁(−; ν + (m+1)/2; -T) / Γ_m(ν + (m+1)/2)` for `T ∈ 𝓢`. -/
@[dlmf 35.8.E4]
theorem besselA_eq_hyp0F1 {m : ℕ} (ν : ℂ) (T : Matrix (Fin m) (Fin m) ℝ) :
    besselA ν T = 1 / multivariateGamma m (ν + ((m : ℂ) + 1) / 2) *
      hyp0F1 (ν + ((m : ℂ) + 1) / 2) (-T) := by
  unfold besselA hyp0F1 hypergeometricPFQ
  congr 1
  refine tsum_congr fun k => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  obtain ⟨hanti, hw⟩ := mem_partitions.mp hκ
  rw [zonalPolynomial_neg κ hanti, hw]
  simp only [Fin.prod_univ_one, Fin.prod_univ_zero, Matrix.cons_val_zero]
  push_cast
  ring

/-! ## §35.8(iii) The `₃F₂` case -/

/-- DLMF 35.8.5 (Kummer transformation): with `c = b₁ + b₂ - a₁ - a₂ - a₃`,
`₃F₂(a₁, a₂, a₃; b₁, b₂; I) = Γ_m(b₂) Γ_m(c) / (Γ_m(b₂ - a₃) Γ_m(c + a₃))
  ₃F₂(b₁ - a₁, b₁ - a₂, a₃; b₁, c + a₃; I)` for `ℜb₂, ℜc > (m-1)/2`. The hypothesis
`ℜ(b₂ - a₃) > (m-1)/2`, which makes the right-hand series converge, and the regularity of the
denominator parameters are added. -/
@[dlmf 35.8.E5]
theorem hyp3F2_one_kummer {m : ℕ} (a₁ a₂ a₃ b₁ b₂ : ℂ)
    (hb₂ : ((m : ℝ) - 1) / 2 < b₂.re) (hc : ((m : ℝ) - 1) / 2 < (b₁ + b₂ - a₁ - a₂ - a₃).re)
    (hb₂a₃ : ((m : ℝ) - 1) / 2 < (b₂ - a₃).re) (hb₁ : multivariateGamma m b₁ ≠ 0)
    (hca : multivariateGamma m (b₁ + b₂ - a₁ - a₂) ≠ 0) :
    hyp3F2 a₁ a₂ a₃ b₁ b₂ (1 : Matrix (Fin m) (Fin m) ℝ) =
      multivariateGamma m b₂ * multivariateGamma m (b₁ + b₂ - a₁ - a₂ - a₃) /
        (multivariateGamma m (b₂ - a₃) * multivariateGamma m (b₁ + b₂ - a₁ - a₂)) *
        hyp3F2 (b₁ - a₁) (b₁ - a₂) a₃ b₁ (b₁ + b₂ - a₁ - a₂) (1 : Matrix (Fin m) (Fin m) ℝ) := by
  sorry

/-- DLMF 35.8.6 (Pfaff–Saalschütz, **corrected**): if `a₁ + a₂ + a₃ + (m+1)/2 = b₁ + b₂`, one of
the `a_j` is a negative integer and `ℜ(b₁ - a₁), ℜ(b₁ - a₂), ℜ(b₁ - a₃),
ℜ(b₁ - a₁ - a₂ - a₃) > (m-1)/2`, then
`₃F₂(a₁, a₂, a₃; b₁, b₂; I) = Γ_m(b₁) Γ_m(b₁ - a₁ - a₂) Γ_m(b₁ - a₁ - a₃) Γ_m(b₁ - a₂ - a₃) /
  (Γ_m(b₁ - a₁) Γ_m(b₁ - a₂) Γ_m(b₁ - a₃) Γ_m(b₁ - a₁ - a₂ - a₃))`.
DLMF prints the reciprocal of this quotient. Regularity of `b₁, b₂` is added. -/
@[dlmf 35.8.E6 "corrected: DLMF prints the reciprocal"]
theorem hyp3F2_one_saalschutz {m : ℕ} (a₁ a₂ a₃ b₁ b₂ : ℂ)
    (hsum : a₁ + a₂ + a₃ + ((m : ℂ) + 1) / 2 = b₁ + b₂)
    (hneg : ∃ n : ℕ, 0 < n ∧ (a₁ = -n ∨ a₂ = -n ∨ a₃ = -n))
    (h₁ : ((m : ℝ) - 1) / 2 < (b₁ - a₁).re) (h₂ : ((m : ℝ) - 1) / 2 < (b₁ - a₂).re)
    (h₃ : ((m : ℝ) - 1) / 2 < (b₁ - a₃).re) (h₄ : ((m : ℝ) - 1) / 2 < (b₁ - a₁ - a₂ - a₃).re)
    (hb₁ : multivariateGamma m b₁ ≠ 0) (hb₂ : multivariateGamma m b₂ ≠ 0) :
    hyp3F2 a₁ a₂ a₃ b₁ b₂ (1 : Matrix (Fin m) (Fin m) ℝ) =
      multivariateGamma m b₁ * multivariateGamma m (b₁ - a₁ - a₂) *
          multivariateGamma m (b₁ - a₁ - a₃) * multivariateGamma m (b₁ - a₂ - a₃) /
        (multivariateGamma m (b₁ - a₁) * multivariateGamma m (b₁ - a₂) *
          multivariateGamma m (b₁ - a₃) * multivariateGamma m (b₁ - a₁ - a₂ - a₃)) := by
  sorry

/-- DLMF 35.8.7 (Thomae transformation, **corrected**): with `c = b₁ + b₂ - a₁ - a₂ - a₃`,
`₃F₂(a₁, a₂, a₃; b₁, b₂; I) = Γ_m(b₁) Γ_m(b₂) Γ_m(c) / (Γ_m(a₁) Γ_m(c + a₂) Γ_m(c + a₃))
  ₃F₂(b₁ - a₁, b₂ - a₁, c; c + a₂, c + a₃; I)` for `ℜb₁, ℜb₂, ℜc > (m-1)/2`. DLMF prints
`b₂ - a₂` for `b₂ - a₁` and `Γ(c)`, `Γ(c + a₃)` for `Γ_m(c)`, `Γ_m(c + a₃)`. The hypothesis
`ℜa₁ > (m-1)/2` (convergence of the right-hand series) and regularity of the denominator
parameters are added. -/
@[dlmf 35.8.E7 "corrected: b₂ - a₁ for b₂ - a₂, and Γ_m for Γ"]
theorem hyp3F2_one_thomae {m : ℕ} (a₁ a₂ a₃ b₁ b₂ : ℂ)
    (hb₁ : ((m : ℝ) - 1) / 2 < b₁.re) (hb₂ : ((m : ℝ) - 1) / 2 < b₂.re)
    (hc : ((m : ℝ) - 1) / 2 < (b₁ + b₂ - a₁ - a₂ - a₃).re) (ha₁ : ((m : ℝ) - 1) / 2 < a₁.re)
    (hc₂ : multivariateGamma m (b₁ + b₂ - a₁ - a₃) ≠ 0)
    (hc₃ : multivariateGamma m (b₁ + b₂ - a₁ - a₂) ≠ 0) :
    hyp3F2 a₁ a₂ a₃ b₁ b₂ (1 : Matrix (Fin m) (Fin m) ℝ) =
      multivariateGamma m b₁ * multivariateGamma m b₂ *
          multivariateGamma m (b₁ + b₂ - a₁ - a₂ - a₃) /
        (multivariateGamma m a₁ * multivariateGamma m (b₁ + b₂ - a₁ - a₃) *
          multivariateGamma m (b₁ + b₂ - a₁ - a₂)) *
        hyp3F2 (b₁ - a₁) (b₂ - a₁) (b₁ + b₂ - a₁ - a₂ - a₃) (b₁ + b₂ - a₁ - a₃)
          (b₁ + b₂ - a₁ - a₂) (1 : Matrix (Fin m) (Fin m) ℝ) := by
  sorry

/-! ## §35.8(iv) Confluence, Laplace transform and Euler integral -/

/-- DLMF 35.8.9: `lim_{γ→∞} p+1Fq(a, γ; b; γ⁻¹T) = pFq(a; b; T)` (real `γ → +∞`), for `p ≤ q`
(where the left side converges for large `γ`), `T ∈ 𝓢` and regular `b`. -/
@[dlmf 35.8.E9]
theorem tendsto_hypergeometricPFQ_snoc {m p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (hb : ∀ j, multivariateGamma m (b j) ≠ 0) (hpq : p ≤ q)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.IsHermitian) :
    Tendsto (fun γ : ℝ => hypergeometricPFQ (Fin.snoc a (γ : ℂ)) b (γ⁻¹ • T)) atTop
      (𝓝 (hypergeometricPFQ a b T)) := by
  sorry

/-- DLMF 35.8.10: `lim_{γ→∞} pFq+1(a; b, γ; γT) = pFq(a; b; T)` (real `γ → +∞`), where the
right side converges: `p ≤ q`, or `p = q + 1` and `‖T‖ < 1`. -/
@[dlmf 35.8.E10]
theorem tendsto_hypergeometricPFQ_snoc_denom {m p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (hb : ∀ j, multivariateGamma m (b j) ≠ 0)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.IsHermitian)
    (hpq : p ≤ q ∨ (p = q + 1 ∧ matrixSpectralNorm T < 1)) :
    Tendsto (fun γ : ℝ => hypergeometricPFQ a (Fin.snoc b (γ : ℂ)) (γ • T)) atTop
      (𝓝 (hypergeometricPFQ a b T)) := by
  sorry

/-- DLMF 35.8.12 (Laplace transform): for `T ∈ Ω` and `ℜγ > (m-1)/2`,
`∫_Ω etr(-TX) |X|^{γ-(m+1)/2} pFq(a; b; -X) dX = Γ_m(γ) |T|^{-γ} p+1Fq(a, γ; b; -T⁻¹)`.
Restricted to the parameters where both series converge (`p < q`, or `p = q` and `T > I`);
regularity of `b` is added. -/
@[dlmf 35.8.E12]
theorem hasIntegralOn_hypergeometricPFQ_laplace {m p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (hb : ∀ j, multivariateGamma m (b j) ≠ 0) {γ : ℂ} (hγ : ((m : ℝ) - 1) / 2 < γ.re)
    {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef)
    (hpq : p < q ∨ (p = q ∧ (T - 1).PosDef)) :
    HasIntegralOn (posDefCone m)
      (fun X => (etr (-(T * X)) : ℂ) * ((X.det : ℂ) ^ (γ - ((m : ℂ) + 1) / 2)) *
        hypergeometricPFQ a b (-X))
      (multivariateGamma m γ * (T.det : ℂ) ^ (-γ) *
        hypergeometricPFQ (Fin.snoc a γ) b (-T⁻¹)) := by
  sorry

/-- DLMF 35.8.13 (Euler integral, **corrected**): for `ℜ(b₁ - a₁), ℜa₁ > (m-1)/2`,
`∫_{0<X<I} |X|^{a₁-(m+1)/2} |I - X|^{b₁-a₁-(m+1)/2} pFq(a₂, …; b₂, …; TX) dX
  = B_m(b₁ - a₁, a₁) p+1Fq+1(a₁, a₂, …; b₁, b₂, …; T)`;
DLMF prints `1/B_m(b₁ - a₁, a₁)`. `pFq(TX)` is the function of the eigenvalues of `TX`, written
`pFq(X^{1/2} T X^{1/2})`. Restricted to `T ∈ 𝓢` where the series converge (`p ≤ q`, or
`p = q + 1` and `‖T‖ < 1`); regularity of the denominator parameters is added. -/
@[dlmf 35.8.E13 "corrected: factor B_m(b₁ - a₁, a₁), not its reciprocal"]
theorem hasIntegralOn_hypergeometricPFQ_euler {m p q : ℕ} (a₁ b₁ : ℂ) (a : Fin p → ℂ)
    (b : Fin q → ℂ) (hb₁ : multivariateGamma m b₁ ≠ 0) (hb : ∀ j, multivariateGamma m (b j) ≠ 0)
    (h₁ : ((m : ℝ) - 1) / 2 < (b₁ - a₁).re) (h₂ : ((m : ℝ) - 1) / 2 < a₁.re)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.IsHermitian)
    (hpq : p ≤ q ∨ (p = q + 1 ∧ matrixSpectralNorm T < 1)) :
    HasIntegralOn (m := m) (matrixInterval 0 1)
      (fun X => ((X.det : ℂ) ^ (a₁ - ((m : ℂ) + 1) / 2)) *
        (((1 - X).det : ℂ) ^ (b₁ - a₁ - ((m : ℂ) + 1) / 2)) *
        hypergeometricPFQ a b (CFC.sqrt X * T * CFC.sqrt X))
      (multivariateBeta m (b₁ - a₁) a₁ * hypergeometricPFQ (Fin.cons a₁ a) (Fin.cons b₁ b) T) := by
  sorry

/-! ## The case `m = 1` -/

/-- For `m = 1` the partitional shifted factorial of `(k)` is the Pochhammer symbol `(a)_k`. -/
theorem partitionalShiftedFactorial_fin_one {𝕜 : Type*} [Field 𝕜] (a : 𝕜) (k : ℕ) :
    partitionalShiftedFactorial a (fun _ : Fin 1 => k) = (ascPochhammer 𝕜 k).eval a := by
  simp [partitionalShiftedFactorial]

/-- For `m = 1` the series 35.8.1 is the classical generalized hypergeometric series in
`t = T₁₁`: `pFq(a; b; t) = ∑_k (a₁)_k ⋯ (a_p)_k / ((b₁)_k ⋯ (b_q)_k) t^k / k!`. -/
theorem hypergeometricPFQ_fin_one {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (T : Matrix (Fin 1) (Fin 1) ℝ) :
    hypergeometricPFQ a b T = ∑' k : ℕ, (1 / (k ! : ℂ)) *
      ((∏ i, (ascPochhammer ℂ k).eval (a i)) / (∏ j, (ascPochhammer ℂ k).eval (b j)) *
        ((T 0 0 : ℂ) ^ k)) := by
  unfold hypergeometricPFQ
  refine tsum_congr fun k => ?_
  rw [partitions_fin_one, Finset.sum_singleton, zonalPolynomial_fin_one]
  simp only [partitionalShiftedFactorial_fin_one]
  push_cast
  rfl

/-- For `m = 1`, `₂F₁(a, b; c; T)` is Mathlib's `ordinaryHypergeometric` at `t = T₁₁`. -/
lemma hyp2F1_fin_one (a b c : ℂ) (T : Matrix (Fin 1) (Fin 1) ℝ) :
    hyp2F1 a b c T = ordinaryHypergeometric a b c (T 0 0 : ℂ) := by
  rw [hyp2F1, hypergeometricPFQ_fin_one, ordinaryHypergeometric_eq_tsum]
  refine tsum_congr fun k => ?_
  simp only [Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    smul_eq_mul]
  rw [div_eq_mul_inv]
  ring

end DLMF.MatrixArgument
