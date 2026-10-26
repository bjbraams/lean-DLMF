/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Eigenvalues

/-!
# Lamé functions: Fourier series (DLMF §29.6)

DLMF §29.6 expands the four Lamé functions in Fourier series in `φ = π/2 - am(x, k)`
(29.2.5): `Ec^{2m}_ν = ½A₀ + ∑ A_{2p} cos 2pφ`, `Ec^{2m+1}_ν = ∑ A_{2p+1} cos(2p+1)φ`,
`Es^{2m+1}_ν = ∑ B_{2p+1} sin(2p+1)φ`, `Es^{2m+2}_ν = ∑ B_{2p+2} sin(2p+2)φ`, and in the same
series multiplied by `dn(x, k)` (coefficients `C`, `D`). The coefficients are defined here by
the Fourier integrals `Real.lameCosCoeff` and `Real.lameSinCoeff` of `DLMF.Lame.Basic`
(`(4/π)∫₀^{π/2} f cos(jφ) dφ` and `(4/π)∫₀^{π/2} (f/dn) cos(jφ) dφ`, written as integrals over
`x ∈ [0, K]`), so that the expansions 29.6.1, 29.6.8, … are theorems; the coefficient list is
indexed from `0` (`A p = A_{2p}`, `A_{2p+1}`, `B_{2p+1}` or `B_{2p+2}`).

The recurrences use `LameRecurrence` (`A0`, `C0` for `Ec^{2m}`; `A1`, `C1` for `Ec^{2m+1}`;
`B1`, `D1` for `Es^{2m+1}`; `B2`, `D2` for `Es^{2m+2}`), with `H = 2a - ν(ν+1)k²` (29.6.2,
29.6.17, 29.6.32, 29.6.47). The positivity conditions 29.6.6, 29.6.13, 29.6.21 and 29.6.28
(values at `x = K`) are proved from the expansions and `Ec(K) > 0`; all other statements are
admitted.

The prose of §29.6(i) (unique recessive solution of the recurrence for `ν ≠ 2n`; for
`ν = 2n`, `m ≤ n`, the coefficients `A_{2p}` vanish for `p > n`) is acquired as
`Real.lameEck_even_fourierA_eq_zero` (the terminating case).
-/

@[expose] public section

open Complex DLMF.JacobiElliptic DLMF.Elliptic Filter Set
open scoped Real Topology

noncomputable section

namespace DLMF.Lame

variable {ν k : ℝ}

/-- `φ(K) = π/2 - am(K, k) = 0`. -/
lemma l29_lamePhi_K (hk0 : 0 < k) (hk1 : k < 1) :
    Real.lamePhi (Real.compEllIntKm (k ^ 2)) k = 0 := by
  rw [Real.lamePhi, Real.jacobiAmm_compEllIntKm (l29_sq_lt_one hk0 hk1), sub_self]

/-- DLMF 29.6.1: `Ec^{2m}_ν(x, k²) = ½A₀ + ∑_{p≥1} A_{2p} cos(2pφ)` for real `x`, with `φ = π/2 -
am(x, k)` and the Fourier coefficients `A_{2p}` of `Real.lameCosCoeff` (weighted by `dn`). Admitted.
-/
@[dlmf 29.6.E1]
theorem Real.lameEck_even_hasSum_fourierA
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∀ x : ℝ, HasSum (fun p : ℕ => (if p = 0 then 1 / 2 else 1) *
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k true (2 * p) *
      Real.cos (((2 * p : ℕ) : ℝ) * Real.lamePhi x k)) (Real.lameEck ν (2 * m) x k) := by
  sorry

/-- DLMF 29.6.2–29.6.3: with `H = 2·(eigenvalue) - ν(ν+1)k²`, `(β₀ - H)A₀ + α₀A₁ = 0` for the
recurrence `A0` (index `p` of the coefficient list). Admitted. -/
@[dlmf 29.6.E2, dlmf 29.6.E3]
theorem Real.lameEck_even_fourierA_rec_zero
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k true (2 * p)
    let H : ℝ := 2 * Real.lameAk ν (2 * m) k - ν * (ν + 1) * k ^ 2
    (LameRecurrence.A0.beta ν k 0 - H) * A 0 +
      LameRecurrence.A0.alpha ν k 0 * A 1 = 0 := by
  sorry

/-- DLMF 29.6.4: `γ_p A_{p-1} + (β_p - H)A_p + α_p A_{p+1} = 0`, `p ≥ 1` (indices of the coefficient
list), for the recurrence `A0`. Admitted. -/
@[dlmf 29.6.E4]
theorem Real.lameEck_even_fourierA_rec
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k true (2 * p)
    let H : ℝ := 2 * Real.lameAk ν (2 * m) k - ν * (ν + 1) * k ^ 2
    ∀ p : ℕ, 1 ≤ p → LameRecurrence.A0.gamma ν k p * A (p - 1) +
      (LameRecurrence.A0.beta ν k p - H) * A p +
      LameRecurrence.A0.alpha ν k p * A (p + 1) = 0 := by
  sorry

/-- DLMF 29.6.5: the normalization of the coefficients `A_{2p}`. Admitted. -/
@[dlmf 29.6.E5]
theorem Real.lameEck_even_fourierA_normalization
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k true (2 * p)
    HasSum (fun p => (if p = 0 then 1 / 2 else 1) * A p ^ 2) 1 := by
  sorry

/-- DLMF 29.6.6: positivity (the value at `x = K`, where `φ = 0`; proved from the Fourier series and
`Ec(K) > 0`). -/
@[dlmf 29.6.E6]
theorem Real.lameEck_even_fourierA_pos
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k true (2 * p)
    ∃ S, HasSum (fun p => (if p = 0 then 1 / 2 else 1) * A p) S ∧ 0 < S := by
  intro A
  have hs := Real.lameEck_even_hasSum_fourierA hν hk0 hk1 m (Real.compEllIntKm (k ^ 2))
  simp only [l29_lamePhi_K hk0 hk1, mul_zero, Real.cos_zero, mul_one] at hs
  exact ⟨_, hs, Real.lameEck_K_pos hν hk0 hk1 _⟩

/-- DLMF 29.6.7: `A_{p+1}/A_p → k²/(1 + k')²` unless `ν = 2 * n` with `m ≤ n`. Admitted. -/
@[dlmf 29.6.E7]
theorem Real.lameEck_even_fourierA_ratio
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k true (2 * p)
    (∀ n : ℕ, ν = ((2 * n : ℕ) : ℝ) → n < m) →
      Tendsto (fun p => A (p + 1) / A p) atTop
        (𝓝 (k ^ 2 / (1 + Real.sqrt (1 - k ^ 2)) ^ 2)) := by
  sorry

/-- DLMF 29.6.8: `Ec^{2m}_ν(x, k²) = dn(x, k) ∑_p C_{2p} (trig)` for real `x`, with the unweighted
Fourier coefficients `C_{2p}`. Admitted. -/
@[dlmf 29.6.E8]
theorem Real.lameEck_even_hasSum_fourierC
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∀ x : ℝ, HasSum (fun p : ℕ => Real.jacobiDnm x (k ^ 2) * ((if p = 0 then 1 / 2 else 1) *
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k false (2 * p) *
      Real.cos (((2 * p : ℕ) : ℝ) * Real.lamePhi x k))) (Real.lameEck ν (2 * m) x k) := by
  sorry

/-- DLMF 29.6.9: `(β₀ - H)C₀ + α₀C₁ = 0` for the recurrence `C0`. Admitted. -/
@[dlmf 29.6.E9]
theorem Real.lameEck_even_fourierC_rec_zero
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k false (2 * p)
    let H : ℝ := 2 * Real.lameAk ν (2 * m) k - ν * (ν + 1) * k ^ 2
    (LameRecurrence.C0.beta ν k 0 - H) * C 0 +
      LameRecurrence.C0.alpha ν k 0 * C 1 = 0 := by
  sorry

/-- DLMF 29.6.10: `γ_p C_{p-1} + (β_p - H)C_p + α_p C_{p+1} = 0`, `p ≥ 1`, for the recurrence `C0`.
Admitted. -/
@[dlmf 29.6.E10]
theorem Real.lameEck_even_fourierC_rec
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k false (2 * p)
    let H : ℝ := 2 * Real.lameAk ν (2 * m) k - ν * (ν + 1) * k ^ 2
    ∀ p : ℕ, 1 ≤ p → LameRecurrence.C0.gamma ν k p * C (p - 1) +
      (LameRecurrence.C0.beta ν k p - H) * C p +
      LameRecurrence.C0.alpha ν k p * C (p + 1) = 0 := by
  sorry

/-- DLMF 29.6.12: the normalization of the coefficients `C_{2p}` (both series converge). Admitted.
-/
@[dlmf 29.6.E12]
theorem Real.lameEck_even_fourierC_normalization
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k false (2 * p)
    ∃ S T : ℝ, HasSum (fun p => (if p = 0 then 1 / 2 else 1) * C p ^ 2) S ∧
      HasSum (fun p => C p * C (p + 1)) T ∧
      (1 - k ^ 2 / 2) * S - k ^ 2 / 2 * T = 1 := by
  sorry

/-- DLMF 29.6.13: positivity (the value of `Ec/dn` at `x = K`; proved from the series and `Ec(K) >
0`). -/
@[dlmf 29.6.E13]
theorem Real.lameEck_even_fourierC_pos
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k false (2 * p)
    ∃ S, HasSum (fun p => (if p = 0 then 1 / 2 else 1) * C p) S ∧ 0 < S := by
  intro C
  have hs := Real.lameEck_even_hasSum_fourierC hν hk0 hk1 m (Real.compEllIntKm (k ^ 2))
  simp only [l29_lamePhi_K hk0 hk1, mul_zero, Real.cos_zero, mul_one] at hs
  have hd := Real.jacobiDnm_pos (l29_sq_lt_one hk0 hk1) (Real.compEllIntKm (k ^ 2))
  rw [show Real.lameEck ν (2 * m) (Real.compEllIntKm (k ^ 2)) k =
      Real.jacobiDnm (Real.compEllIntKm (k ^ 2)) (k ^ 2) *
        (Real.lameEck ν (2 * m) (Real.compEllIntKm (k ^ 2)) k /
          Real.jacobiDnm (Real.compEllIntKm (k ^ 2)) (k ^ 2)) by field_simp,
    hasSum_mul_left_iff hd.ne'] at hs
  exact ⟨_, hs, div_pos (Real.lameEck_K_pos hν hk0 hk1 _) hd⟩

/-- DLMF 29.6.14: `C_{p+1}/C_p → k²/(1 + k')²` unless `ν = 2 * n + 1` with `m ≤ n`. Admitted. -/
@[dlmf 29.6.E14]
theorem Real.lameEck_even_fourierC_ratio
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k false (2 * p)
    (∀ n : ℕ, ν = ((2 * n + 1 : ℕ) : ℝ) → n < m) →
      Tendsto (fun p => C (p + 1) / C p) atTop
        (𝓝 (k ^ 2 / (1 + Real.sqrt (1 - k ^ 2)) ^ 2)) := by
  sorry

/-- DLMF 29.6.15: `∑ AC = (4/π) ∫₀^K (Ec^{2m}_ν)² dx`. Admitted. -/
@[dlmf 29.6.E15]
theorem Real.lameEck_even_fourier_parseval
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k true (2 * p)
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k false (2 * p)
    HasSum (fun p => (if p = 0 then 1 / 2 else 1) * A p * C p)
      (4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.lameEck ν (2 * m) x k ^ 2) := by
  sorry

/-- DLMF 29.6.16: `Ec^{2m+1}_ν(x, k²) = ∑_{p≥0} A_{2p+1} cos((2p+1)φ)` for real `x`, with `φ = π/2 -
am(x, k)` and the Fourier coefficients `A_{2p+1}` of `Real.lameCosCoeff` (weighted by `dn`).
Admitted. -/
@[dlmf 29.6.E16]
theorem Real.lameEck_odd_hasSum_fourierA
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∀ x : ℝ, HasSum (fun p : ℕ =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k true (2 * p + 1) *
      Real.cos (((2 * p + 1 : ℕ) : ℝ) * Real.lamePhi x k)) (Real.lameEck ν (2 * m + 1) x k) := by
  sorry

/-- DLMF 29.6.17–29.6.18: with `H = 2·(eigenvalue) - ν(ν+1)k²`, `(β₀ - H)A₀ + α₀A₁ = 0` for the
recurrence `A1` (index `p` of the coefficient list). Admitted. -/
@[dlmf 29.6.E17, dlmf 29.6.E18]
theorem Real.lameEck_odd_fourierA_rec_zero
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k true (2 * p + 1)
    let H : ℝ := 2 * Real.lameAk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2
    (LameRecurrence.A1.beta ν k 0 - H) * A 0 +
      LameRecurrence.A1.alpha ν k 0 * A 1 = 0 := by
  sorry

/-- DLMF 29.6.19: `γ_p A_{p-1} + (β_p - H)A_p + α_p A_{p+1} = 0`, `p ≥ 1` (indices of the
coefficient list), for the recurrence `A1`. Admitted. -/
@[dlmf 29.6.E19]
theorem Real.lameEck_odd_fourierA_rec
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k true (2 * p + 1)
    let H : ℝ := 2 * Real.lameAk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2
    ∀ p : ℕ, 1 ≤ p → LameRecurrence.A1.gamma ν k p * A (p - 1) +
      (LameRecurrence.A1.beta ν k p - H) * A p +
      LameRecurrence.A1.alpha ν k p * A (p + 1) = 0 := by
  sorry

/-- DLMF 29.6.20: the normalization of the coefficients `A_{2p+1}`. Admitted. -/
@[dlmf 29.6.E20]
theorem Real.lameEck_odd_fourierA_normalization
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k true (2 * p + 1)
    HasSum (fun p => A p ^ 2) 1 := by
  sorry

/-- DLMF 29.6.21: positivity (the value at `x = K`, where `φ = 0`; proved from the Fourier series
and `Ec(K) > 0`). -/
@[dlmf 29.6.E21]
theorem Real.lameEck_odd_fourierA_pos
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k true (2 * p + 1)
    ∃ S, HasSum (fun p => A p) S ∧ 0 < S := by
  intro A
  have hs := Real.lameEck_odd_hasSum_fourierA hν hk0 hk1 m (Real.compEllIntKm (k ^ 2))
  simp only [l29_lamePhi_K hk0 hk1, mul_zero, Real.cos_zero, mul_one] at hs
  exact ⟨_, hs, Real.lameEck_K_pos hν hk0 hk1 _⟩

/-- DLMF 29.6.22: `A_{p+1}/A_p → k²/(1 + k')²` unless `ν = 2 * n + 1` with `m ≤ n`. Admitted. -/
@[dlmf 29.6.E22]
theorem Real.lameEck_odd_fourierA_ratio
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k true (2 * p + 1)
    (∀ n : ℕ, ν = ((2 * n + 1 : ℕ) : ℝ) → n < m) →
      Tendsto (fun p => A (p + 1) / A p) atTop
        (𝓝 (k ^ 2 / (1 + Real.sqrt (1 - k ^ 2)) ^ 2)) := by
  sorry

/-- DLMF 29.6.23: `Ec^{2m+1}_ν(x, k²) = dn(x, k) ∑_p C_{2p+1} (trig)` for real `x`, with the
unweighted Fourier coefficients `C_{2p+1}`. Admitted. -/
@[dlmf 29.6.E23]
theorem Real.lameEck_odd_hasSum_fourierC
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∀ x : ℝ, HasSum (fun p : ℕ => Real.jacobiDnm x (k ^ 2) * (
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k false (2 * p + 1) *
      Real.cos (((2 * p + 1 : ℕ) : ℝ) * Real.lamePhi x k))) (Real.lameEck ν (2 * m + 1) x k) := by
  sorry

/-- DLMF 29.6.24: `(β₀ - H)C₀ + α₀C₁ = 0` for the recurrence `C1`. Admitted. -/
@[dlmf 29.6.E24]
theorem Real.lameEck_odd_fourierC_rec_zero
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k false (2 * p + 1)
    let H : ℝ := 2 * Real.lameAk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2
    (LameRecurrence.C1.beta ν k 0 - H) * C 0 +
      LameRecurrence.C1.alpha ν k 0 * C 1 = 0 := by
  sorry

/-- DLMF 29.6.25: `γ_p C_{p-1} + (β_p - H)C_p + α_p C_{p+1} = 0`, `p ≥ 1`, for the recurrence `C1`.
Admitted. -/
@[dlmf 29.6.E25]
theorem Real.lameEck_odd_fourierC_rec
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k false (2 * p + 1)
    let H : ℝ := 2 * Real.lameAk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2
    ∀ p : ℕ, 1 ≤ p → LameRecurrence.C1.gamma ν k p * C (p - 1) +
      (LameRecurrence.C1.beta ν k p - H) * C p +
      LameRecurrence.C1.alpha ν k p * C (p + 1) = 0 := by
  sorry

/-- DLMF 29.6.27: the normalization of the coefficients `C_{2p+1}` (both series converge). Admitted.
-/
@[dlmf 29.6.E27]
theorem Real.lameEck_odd_fourierC_normalization
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k false (2 * p + 1)
    ∃ S T : ℝ, HasSum (fun p => C p ^ 2) S ∧
      HasSum (fun p => C p * C (p + 1)) T ∧
      (1 - k ^ 2 / 2) * S - k ^ 2 / 2 * (C 0 ^ 2 / 2 + T) = 1 := by
  sorry

/-- DLMF 29.6.28: positivity (the value of `Ec/dn` at `x = K`; proved from the series and `Ec(K) >
0`). -/
@[dlmf 29.6.E28]
theorem Real.lameEck_odd_fourierC_pos
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k false (2 * p + 1)
    ∃ S, HasSum (fun p => C p) S ∧ 0 < S := by
  intro C
  have hs := Real.lameEck_odd_hasSum_fourierC hν hk0 hk1 m (Real.compEllIntKm (k ^ 2))
  simp only [l29_lamePhi_K hk0 hk1, mul_zero, Real.cos_zero, mul_one] at hs
  have hd := Real.jacobiDnm_pos (l29_sq_lt_one hk0 hk1) (Real.compEllIntKm (k ^ 2))
  rw [show Real.lameEck ν (2 * m + 1) (Real.compEllIntKm (k ^ 2)) k =
      Real.jacobiDnm (Real.compEllIntKm (k ^ 2)) (k ^ 2) *
        (Real.lameEck ν (2 * m + 1) (Real.compEllIntKm (k ^ 2)) k /
          Real.jacobiDnm (Real.compEllIntKm (k ^ 2)) (k ^ 2)) by field_simp,
    hasSum_mul_left_iff hd.ne'] at hs
  exact ⟨_, hs, div_pos (Real.lameEck_K_pos hν hk0 hk1 _) hd⟩

/-- DLMF 29.6.29: `C_{p+1}/C_p → k²/(1 + k')²` unless `ν = 2 * n + 2` with `m ≤ n`. Admitted. -/
@[dlmf 29.6.E29]
theorem Real.lameEck_odd_fourierC_ratio
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k false (2 * p + 1)
    (∀ n : ℕ, ν = ((2 * n + 2 : ℕ) : ℝ) → n < m) →
      Tendsto (fun p => C (p + 1) / C p) atTop
        (𝓝 (k ^ 2 / (1 + Real.sqrt (1 - k ^ 2)) ^ 2)) := by
  sorry

/-- DLMF 29.6.30: `∑ AC = (4/π) ∫₀^K (Ec^{2m+1}_ν)² dx`. Admitted. -/
@[dlmf 29.6.E30]
theorem Real.lameEck_odd_fourier_parseval
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k true (2 * p + 1)
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k false (2 * p + 1)
    HasSum (fun p => A p * C p)
      (4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.lameEck ν (2 * m + 1) x k ^ 2) := by
  sorry

/-- DLMF 29.6.31: `Es^{2m+1}_ν(x, k²) = ∑_{p≥0} B_{2p+1} sin((2p+1)φ)` for real `x`, with `φ = π/2 -
am(x, k)` and the Fourier coefficients `B_{2p+1}` of `Real.lameSinCoeff` (weighted by `dn`).
Admitted. -/
@[dlmf 29.6.E31]
theorem Real.lameEsk_odd_hasSum_fourierB
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∀ x : ℝ, HasSum (fun p : ℕ =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k true (2 * p + 1) *
      Real.sin (((2 * p + 1 : ℕ) : ℝ) * Real.lamePhi x k)) (Real.lameEsk ν (2 * m + 1) x k) := by
  sorry

/-- DLMF 29.6.32–29.6.33: with `H = 2·(eigenvalue) - ν(ν+1)k²`, `(β₀ - H)B₀ + α₀B₁ = 0` for the
recurrence `B1` (index `p` of the coefficient list). Admitted. -/
@[dlmf 29.6.E32, dlmf 29.6.E33]
theorem Real.lameEsk_odd_fourierB_rec_zero
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k true (2 * p + 1)
    let H : ℝ := 2 * Real.lameBk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2
    (LameRecurrence.B1.beta ν k 0 - H) * B 0 +
      LameRecurrence.B1.alpha ν k 0 * B 1 = 0 := by
  sorry

/-- DLMF 29.6.34: `γ_p B_{p-1} + (β_p - H)B_p + α_p B_{p+1} = 0`, `p ≥ 1` (indices of the
coefficient list), for the recurrence `B1`. Admitted. -/
@[dlmf 29.6.E34]
theorem Real.lameEsk_odd_fourierB_rec
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k true (2 * p + 1)
    let H : ℝ := 2 * Real.lameBk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2
    ∀ p : ℕ, 1 ≤ p → LameRecurrence.B1.gamma ν k p * B (p - 1) +
      (LameRecurrence.B1.beta ν k p - H) * B p +
      LameRecurrence.B1.alpha ν k p * B (p + 1) = 0 := by
  sorry

/-- DLMF 29.6.35: the normalization of the coefficients `B_{2p+1}`. Admitted. -/
@[dlmf 29.6.E35]
theorem Real.lameEsk_odd_fourierB_normalization
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k true (2 * p + 1)
    HasSum (fun p => B p ^ 2) 1 := by
  sorry

/-- DLMF 29.6.36: positivity (`-dEs/dz` at `z = K` divided by `dn(K)`). Admitted. -/
@[dlmf 29.6.E36]
theorem Real.lameEsk_odd_fourierB_pos
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k true (2 * p + 1)
    ∃ S, HasSum (fun p => ((2 * p + 1 : ℕ) : ℝ) * B p) S ∧ 0 < S := by
  sorry

/-- DLMF 29.6.37: `B_{p+1}/B_p → k²/(1 + k')²` unless `ν = 2 * n + 1` with `m ≤ n`. Admitted. -/
@[dlmf 29.6.E37]
theorem Real.lameEsk_odd_fourierB_ratio
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k true (2 * p + 1)
    (∀ n : ℕ, ν = ((2 * n + 1 : ℕ) : ℝ) → n < m) →
      Tendsto (fun p => B (p + 1) / B p) atTop
        (𝓝 (k ^ 2 / (1 + Real.sqrt (1 - k ^ 2)) ^ 2)) := by
  sorry

/-- DLMF 29.6.38: `Es^{2m+1}_ν(x, k²) = dn(x, k) ∑_p D_{2p+1} (trig)` for real `x`, with the
unweighted Fourier coefficients `D_{2p+1}`. Admitted. -/
@[dlmf 29.6.E38]
theorem Real.lameEsk_odd_hasSum_fourierD
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∀ x : ℝ, HasSum (fun p : ℕ => Real.jacobiDnm x (k ^ 2) * (
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k false (2 * p + 1) *
      Real.sin (((2 * p + 1 : ℕ) : ℝ) * Real.lamePhi x k))) (Real.lameEsk ν (2 * m + 1) x k) := by
  sorry

/-- DLMF 29.6.39: `(β₀ - H)D₀ + α₀D₁ = 0` for the recurrence `D1`. Admitted. -/
@[dlmf 29.6.E39]
theorem Real.lameEsk_odd_fourierD_rec_zero
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k false (2 * p + 1)
    let H : ℝ := 2 * Real.lameBk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2
    (LameRecurrence.D1.beta ν k 0 - H) * D 0 +
      LameRecurrence.D1.alpha ν k 0 * D 1 = 0 := by
  sorry

/-- DLMF 29.6.40: `γ_p D_{p-1} + (β_p - H)D_p + α_p D_{p+1} = 0`, `p ≥ 1`, for the recurrence `D1`.
Admitted. -/
@[dlmf 29.6.E40]
theorem Real.lameEsk_odd_fourierD_rec
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k false (2 * p + 1)
    let H : ℝ := 2 * Real.lameBk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2
    ∀ p : ℕ, 1 ≤ p → LameRecurrence.D1.gamma ν k p * D (p - 1) +
      (LameRecurrence.D1.beta ν k p - H) * D p +
      LameRecurrence.D1.alpha ν k p * D (p + 1) = 0 := by
  sorry

/-- DLMF 29.6.42: the normalization of the coefficients `D_{2p+1}` (both series converge). Admitted.
-/
@[dlmf 29.6.E42]
theorem Real.lameEsk_odd_fourierD_normalization
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k false (2 * p + 1)
    ∃ S T : ℝ, HasSum (fun p => D p ^ 2) S ∧
      HasSum (fun p => D p * D (p + 1)) T ∧
      (1 - k ^ 2 / 2) * S + k ^ 2 / 2 * (D 0 ^ 2 / 2 - T) = 1 := by
  sorry

/-- DLMF 29.6.43: positivity Admitted. -/
@[dlmf 29.6.E43]
theorem Real.lameEsk_odd_fourierD_pos
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k false (2 * p + 1)
    ∃ S, HasSum (fun p => ((2 * p + 1 : ℕ) : ℝ) * D p) S ∧ 0 < S := by
  sorry

/-- DLMF 29.6.44: `D_{p+1}/D_p → k²/(1 + k')²` unless `ν = 2 * n + 2` with `m ≤ n`. Admitted. -/
@[dlmf 29.6.E44]
theorem Real.lameEsk_odd_fourierD_ratio
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k false (2 * p + 1)
    (∀ n : ℕ, ν = ((2 * n + 2 : ℕ) : ℝ) → n < m) →
      Tendsto (fun p => D (p + 1) / D p) atTop
        (𝓝 (k ^ 2 / (1 + Real.sqrt (1 - k ^ 2)) ^ 2)) := by
  sorry

/-- DLMF 29.6.45: `∑ BD = (4/π) ∫₀^K (Es^{2m+1}_ν)² dx`. Admitted. -/
@[dlmf 29.6.E45]
theorem Real.lameEsk_odd_fourier_parseval
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k true (2 * p + 1)
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k false (2 * p + 1)
    HasSum (fun p => B p * D p)
      (4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.lameEsk ν (2 * m + 1) x k ^ 2) := by
  sorry

/-- DLMF 29.6.46: `Es^{2m+2}_ν(x, k²) = ∑_{p≥0} B_{2p+2} sin((2p+2)φ)` for real `x`, with `φ = π/2 -
am(x, k)` and the Fourier coefficients `B_{2p+2}` of `Real.lameSinCoeff` (weighted by `dn`).
Admitted. -/
@[dlmf 29.6.E46]
theorem Real.lameEsk_even_hasSum_fourierB
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∀ x : ℝ, HasSum (fun p : ℕ =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k true (2 * p + 2) *
      Real.sin (((2 * p + 2 : ℕ) : ℝ) * Real.lamePhi x k)) (Real.lameEsk ν (2 * m + 2) x k) := by
  sorry

/-- DLMF 29.6.47–29.6.48: with `H = 2·(eigenvalue) - ν(ν+1)k²`, `(β₀ - H)B₀ + α₀B₁ = 0` for the
recurrence `B2` (index `p` of the coefficient list). Admitted. -/
@[dlmf 29.6.E47, dlmf 29.6.E48]
theorem Real.lameEsk_even_fourierB_rec_zero
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k true (2 * p + 2)
    let H : ℝ := 2 * Real.lameBk ν (2 * m + 2) k - ν * (ν + 1) * k ^ 2
    (LameRecurrence.B2.beta ν k 0 - H) * B 0 +
      LameRecurrence.B2.alpha ν k 0 * B 1 = 0 := by
  sorry

/-- DLMF 29.6.49: `γ_p B_{p-1} + (β_p - H)B_p + α_p B_{p+1} = 0`, `p ≥ 1` (indices of the
coefficient list), for the recurrence `B2`. Admitted. -/
@[dlmf 29.6.E49]
theorem Real.lameEsk_even_fourierB_rec
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k true (2 * p + 2)
    let H : ℝ := 2 * Real.lameBk ν (2 * m + 2) k - ν * (ν + 1) * k ^ 2
    ∀ p : ℕ, 1 ≤ p → LameRecurrence.B2.gamma ν k p * B (p - 1) +
      (LameRecurrence.B2.beta ν k p - H) * B p +
      LameRecurrence.B2.alpha ν k p * B (p + 1) = 0 := by
  sorry

/-- DLMF 29.6.50: the normalization of the coefficients `B_{2p+2}`. Admitted. -/
@[dlmf 29.6.E50]
theorem Real.lameEsk_even_fourierB_normalization
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k true (2 * p + 2)
    HasSum (fun p => B p ^ 2) 1 := by
  sorry

/-- DLMF 29.6.51: positivity (`-dEs/dz` at `z = K` divided by `dn(K)`). Admitted. -/
@[dlmf 29.6.E51]
theorem Real.lameEsk_even_fourierB_pos
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k true (2 * p + 2)
    ∃ S, HasSum (fun p => ((2 * p + 2 : ℕ) : ℝ) * B p) S ∧ 0 < S := by
  sorry

/-- DLMF 29.6.52: `B_{p+1}/B_p → k²/(1 + k')²` unless `ν = 2 * n + 2` with `m ≤ n`. Admitted. -/
@[dlmf 29.6.E52]
theorem Real.lameEsk_even_fourierB_ratio
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k true (2 * p + 2)
    (∀ n : ℕ, ν = ((2 * n + 2 : ℕ) : ℝ) → n < m) →
      Tendsto (fun p => B (p + 1) / B p) atTop
        (𝓝 (k ^ 2 / (1 + Real.sqrt (1 - k ^ 2)) ^ 2)) := by
  sorry

/-- DLMF 29.6.53: `Es^{2m+2}_ν(x, k²) = dn(x, k) ∑_p D_{2p+2} (trig)` for real `x`, with the
unweighted Fourier coefficients `D_{2p+2}`. Admitted. -/
@[dlmf 29.6.E53]
theorem Real.lameEsk_even_hasSum_fourierD
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∀ x : ℝ, HasSum (fun p : ℕ => Real.jacobiDnm x (k ^ 2) * (
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k false (2 * p + 2) *
      Real.sin (((2 * p + 2 : ℕ) : ℝ) * Real.lamePhi x k))) (Real.lameEsk ν (2 * m + 2) x k) := by
  sorry

/-- DLMF 29.6.54: `(β₀ - H)D₀ + α₀D₁ = 0` for the recurrence `D2`. Admitted. -/
@[dlmf 29.6.E54]
theorem Real.lameEsk_even_fourierD_rec_zero
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k false (2 * p + 2)
    let H : ℝ := 2 * Real.lameBk ν (2 * m + 2) k - ν * (ν + 1) * k ^ 2
    (LameRecurrence.D2.beta ν k 0 - H) * D 0 +
      LameRecurrence.D2.alpha ν k 0 * D 1 = 0 := by
  sorry

/-- DLMF 29.6.55: `γ_p D_{p-1} + (β_p - H)D_p + α_p D_{p+1} = 0`, `p ≥ 1`, for the recurrence `D2`.
Admitted. -/
@[dlmf 29.6.E55]
theorem Real.lameEsk_even_fourierD_rec
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k false (2 * p + 2)
    let H : ℝ := 2 * Real.lameBk ν (2 * m + 2) k - ν * (ν + 1) * k ^ 2
    ∀ p : ℕ, 1 ≤ p → LameRecurrence.D2.gamma ν k p * D (p - 1) +
      (LameRecurrence.D2.beta ν k p - H) * D p +
      LameRecurrence.D2.alpha ν k p * D (p + 1) = 0 := by
  sorry

/-- DLMF 29.6.57: the normalization of the coefficients `D_{2p+2}` (both series converge). Admitted.
-/
@[dlmf 29.6.E57]
theorem Real.lameEsk_even_fourierD_normalization
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k false (2 * p + 2)
    ∃ S T : ℝ, HasSum (fun p => D p ^ 2) S ∧
      HasSum (fun p => D p * D (p + 1)) T ∧
      (1 - k ^ 2 / 2) * S - k ^ 2 / 2 * T = 1 := by
  sorry

/-- DLMF 29.6.58: positivity Admitted. -/
@[dlmf 29.6.E58]
theorem Real.lameEsk_even_fourierD_pos
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k false (2 * p + 2)
    ∃ S, HasSum (fun p => ((2 * p + 2 : ℕ) : ℝ) * D p) S ∧ 0 < S := by
  sorry

/-- DLMF 29.6.59: `D_{p+1}/D_p → k²/(1 + k')²` unless `ν = 2 * n + 3` with `m ≤ n`. Admitted. -/
@[dlmf 29.6.E59]
theorem Real.lameEsk_even_fourierD_ratio
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k false (2 * p + 2)
    (∀ n : ℕ, ν = ((2 * n + 3 : ℕ) : ℝ) → n < m) →
      Tendsto (fun p => D (p + 1) / D p) atTop
        (𝓝 (k ^ 2 / (1 + Real.sqrt (1 - k ^ 2)) ^ 2)) := by
  sorry

/-- DLMF 29.6.60: `∑ BD = (4/π) ∫₀^K (Es^{2m+2}_ν)² dx`. Admitted. -/
@[dlmf 29.6.E60]
theorem Real.lameEsk_even_fourier_parseval
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k true (2 * p + 2)
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k false (2 * p + 2)
    HasSum (fun p => B p * D p)
      (4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.lameEsk ν (2 * m + 2) x k ^ 2) := by
  sorry

/-- §29.6(i): for `ν = 2n` and `m = 0, 1, …, n` the Fourier coefficients `A_{2p}` of
`Ec^{2m}_{2n}` vanish for `p > n`, so `Ec^{2m}_{2n}` reduces to a Lamé polynomial (compare
§§29.12(i), 29.15(i)). Admitted. -/
@[dlmf 29.6.i]
theorem Real.lameEck_even_fourierA_eq_zero (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n)
    {p : ℕ} (hp : n < p) :
    Real.lameCosCoeff (fun x => Real.lameEck (2 * n : ℕ) (2 * m) x k) k true (2 * p) = 0 := by
  sorry

end DLMF.Lame
