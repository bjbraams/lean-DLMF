/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.FourierSeries.CoefficientRecurrences

/-!
# Normalized Fourier series of Lame eigenfunctions

Parseval identities, normalization and the Fourier expansions of the Lame eigenfunction
families.

Source references and common attribution are retained in
`DLMF.Lame.FourierSeries`.
-/

@[expose] public section

open Complex DLMF.JacobiElliptic DLMF.Elliptic Filter Set

open scoped Real Topology

noncomputable section

namespace DLMF.Lame

variable {ν k : ℝ}

/-- DLMF 29.6.15: `∑ AC = (4/π) ∫₀^K (Ec^{2m}_ν)² dx`. -/
@[dlmf 29.6.E15]
theorem Real.lameEck_even_fourier_parseval
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k true (2 * p)
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k false (2 * p)
    HasSum (fun p => (if p = 0 then 1 / 2 else 1) * A p * C p)
      (4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.lameEck ν (2 * m) x k ^ 2) := by
  intro A C
  have hk := l29_sq_lt_one hk0 hk1
  have h := p2l_lameEck_cos_integral hν hk0 hk1 (2 * m) true
    (g := fun x => Real.lameEck ν (2 * m) x k) (p2l_continuous_lameEck hν hk0 hk1 _)
  simp only [↓reduceIte, div_one, p2l_integral_cos_false] at h
  have h2 := h.mul_left (4 / π)
  convert p2l_hasSum_two_mul_add 0 (fun j hj => ?_) h2 using 1
  · funext p
    simp only [A, C, pow_succ, pow_mul]; norm_num
    split_ifs <;> field_simp
  · congr 1; congr 1; funext t; ring
  · have := (p2l_neg_one_pow_mod j).2.2 (by omega)
    simp [pow_succ, pow_mul, this]

/-- DLMF 29.6.16: `Ec^{2m+1}_ν(x, k²) = ∑_{p≥0} A_{2p+1} cos((2p+1)φ)` for real `x`, with `φ = π/2 -
am(x, k)` and the Fourier coefficients `A_{2p+1}` of `Real.lameCosCoeff` (weighted by `dn`). -/
@[dlmf 29.6.E16]
theorem Real.lameEck_odd_hasSum_fourierA
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∀ x : ℝ, HasSum (fun p : ℕ =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k true (2 * p + 1) *
      Real.cos (((2 * p + 1 : ℕ) : ℝ) * Real.lamePhi x k)) (Real.lameEck ν (2 * m + 1) x k) := by
  intro x
  have hs := p2l_lameEck_cos hν hk0 hk1 (2 * m + 1) true x
  simp only [↓reduceIte, div_one] at hs
  convert p2l_hasSum_two_mul_add 1 (fun j hj => ?_) hs using 1
  · funext p
    simp [pow_succ, pow_mul]
  · have := (p2l_neg_one_pow_mod j).1.2 (by omega)
    simp [pow_succ, pow_mul, this]

/-- DLMF 29.6.17–29.6.18: with `H = 2·(eigenvalue) - ν(ν+1)k²`, `(β₀ - H)A₀ + α₀A₁ = 0` for the
recurrence `A1` (index `p` of the coefficient list). Proved from Lamé's equation
by Green's identity (`p1l_cos_rec`, `p1l_sin_rec`). -/
@[dlmf 29.6.E17, dlmf 29.6.E18]
theorem Real.lameEck_odd_fourierA_rec_zero
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k true (2 * p + 1)
    let H : ℝ := 2 * Real.lameAk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2
    (LameRecurrence.A1.beta ν k 0 - H) * A 0 +
      LameRecurrence.A1.alpha ν k 0 * A 1 = 0 := by
  intro X H
  have hk := l29_sq_lt_one hk0 hk1
  obtain ⟨hw, hb, -⟩ := Real.lameEck_isLameEigenfunction hν hk0 hk1 (2 * m + 1)
  simp [Real.LameBoundary] at hb
  have key := p1l_cos_rec hk hw true (j := 1) (by simp [hb.1])
    (by simp) hb.2
  simp only [X, H, Real.lameCosCoeff, LameRecurrence.alpha, LameRecurrence.beta, ite_true]
  norm_num [Real.cos_neg, Real.sin_neg] at key ⊢
  linear_combination key

/-- DLMF 29.6.19: `γ_p A_{p-1} + (β_p - H)A_p + α_p A_{p+1} = 0`, `p ≥ 1` (indices of the
coefficient list), for the recurrence `A1`. Proved from Lamé's equation
by Green's identity (`p1l_cos_rec`, `p1l_sin_rec`). -/
@[dlmf 29.6.E19]
theorem Real.lameEck_odd_fourierA_rec
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k true (2 * p + 1)
    let H : ℝ := 2 * Real.lameAk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2
    ∀ p : ℕ, 1 ≤ p → LameRecurrence.A1.gamma ν k p * A (p - 1) +
      (LameRecurrence.A1.beta ν k p - H) * A p +
      LameRecurrence.A1.alpha ν k p * A (p + 1) = 0 := by
  intro X H p hp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hk := l29_sq_lt_one hk0 hk1
  obtain ⟨hw, hb, -⟩ := Real.lameEck_isLameEigenfunction hν hk0 hk1 (2 * m + 1)
  simp [Real.LameBoundary] at hb
  have key := p1l_cos_rec hk hw true (j := ((2 * (q + 1) + 1 : ℕ) : ℝ))
    (by simp [hb.1])
    (by rw [show ((2 * (q + 1) + 1 : ℕ) : ℝ) * (π / 2) = ((q + 1 : ℕ) : ℝ) * π + π / 2 by
      push_cast; ring, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero, mul_zero]) hb.2
  rw [show ((2 * (q + 1) + 1 : ℕ) : ℝ) + 2 = ((2 * (q + 1 + 1) + 1 : ℕ) : ℝ) by push_cast; ring,
    show ((2 * (q + 1) + 1 : ℕ) : ℝ) - 2 = ((2 * (q) + 1 : ℕ) : ℝ) by push_cast; ring] at key
  simp only [X, H, Real.lameCosCoeff, LameRecurrence.alpha, LameRecurrence.beta,
    LameRecurrence.gamma, Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false, ite_true]
  simp only [↓reduceIte] at key ⊢
  push_cast at key ⊢
  linear_combination key

/-- DLMF 29.6.20: the normalization of the coefficients `A_{2p+1}`. -/
@[dlmf 29.6.E20]
theorem Real.lameEck_odd_fourierA_normalization
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k true (2 * p + 1)
    HasSum (fun p => A p ^ 2) 1 := by
  intro A
  have hk := l29_sq_lt_one hk0 hk1
  have h := p2l_lameEck_cos_integral hν hk0 hk1 (2 * m + 1) true
    (g := fun x => Real.lameEck ν (2 * m + 1) x k * Real.jacobiDnm x (k ^ 2))
    ((p2l_continuous_lameEck hν hk0 hk1 _).mul (p2l_continuous_dn hk))
  simp only [↓reduceIte, div_one, p2l_integral_cos_true] at h
  rw [show (∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.lameEck ν (2 * m + 1) t k *
      (Real.lameEck ν (2 * m + 1) t k * Real.jacobiDnm t (k ^ 2))) =
      ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm t (k ^ 2) *
        Real.lameEck ν (2 * m + 1) t k ^ 2 by congr 1; funext t; ring,
    Real.lameEck_normalization hν hk0 hk1] at h
  have h2 := h.mul_left (4 / π)
  rw [show 4 / π * (π / 4) = 1 by field_simp] at h2
  convert p2l_hasSum_two_mul_add 1 (fun j hj => ?_) h2 using 1
  · funext p
    simp only [A, pow_succ, pow_mul]; norm_num
    field_simp
  · have := (p2l_neg_one_pow_mod j).1.2 (by omega)
    simp [pow_succ, pow_mul, this]

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
unweighted Fourier coefficients `C_{2p+1}`. -/
@[dlmf 29.6.E23]
theorem Real.lameEck_odd_hasSum_fourierC
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∀ x : ℝ, HasSum (fun p : ℕ => Real.jacobiDnm x (k ^ 2) * (
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k false (2 * p + 1) *
      Real.cos (((2 * p + 1 : ℕ) : ℝ) * Real.lamePhi x k))) (Real.lameEck ν (2 * m + 1) x k) := by
  intro x
  have hd := (Real.jacobiDnm_pos (l29_sq_lt_one hk0 hk1) x).ne'
  have hs := (p2l_lameEck_cos hν hk0 hk1 (2 * m + 1) false x).mul_left
    (Real.jacobiDnm x (k ^ 2))
  simp only [Bool.false_eq_true, ↓reduceIte, mul_div_cancel₀ _ hd] at hs
  convert p2l_hasSum_two_mul_add 1 (fun j hj => ?_) hs using 1
  · funext p
    simp [pow_succ, pow_mul]
  · have := (p2l_neg_one_pow_mod j).1.2 (by omega)
    simp [pow_succ, pow_mul, this]

/-- DLMF 29.6.24: `(β₀ - H)C₀ + α₀C₁ = 0` for the recurrence `C1`.
Proved from Lamé's equation by Green's identity (`p1l_cos_rec`, `p1l_sin_rec`). -/
@[dlmf 29.6.E24]
theorem Real.lameEck_odd_fourierC_rec_zero
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k false (2 * p + 1)
    let H : ℝ := 2 * Real.lameAk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2
    (LameRecurrence.C1.beta ν k 0 - H) * C 0 +
      LameRecurrence.C1.alpha ν k 0 * C 1 = 0 := by
  intro X H
  have hk := l29_sq_lt_one hk0 hk1
  obtain ⟨hw, hb, -⟩ := Real.lameEck_isLameEigenfunction hν hk0 hk1 (2 * m + 1)
  simp [Real.LameBoundary] at hb
  have key := p1l_cos_rec hk hw false (j := 1) (by simp [hb.1])
    (by simp) hb.2
  simp only [X, H, Real.lameCosCoeff, LameRecurrence.alpha, LameRecurrence.beta]
  norm_num [Real.cos_neg, Real.sin_neg] at key ⊢
  linear_combination key

/-- DLMF 29.6.25: `γ_p C_{p-1} + (β_p - H)C_p + α_p C_{p+1} = 0`, `p ≥ 1`, for the recurrence `C1`.
Proved from Lamé's equation by Green's identity (`p1l_cos_rec`, `p1l_sin_rec`). -/
@[dlmf 29.6.E25]
theorem Real.lameEck_odd_fourierC_rec
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k false (2 * p + 1)
    let H : ℝ := 2 * Real.lameAk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2
    ∀ p : ℕ, 1 ≤ p → LameRecurrence.C1.gamma ν k p * C (p - 1) +
      (LameRecurrence.C1.beta ν k p - H) * C p +
      LameRecurrence.C1.alpha ν k p * C (p + 1) = 0 := by
  intro X H p hp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hk := l29_sq_lt_one hk0 hk1
  obtain ⟨hw, hb, -⟩ := Real.lameEck_isLameEigenfunction hν hk0 hk1 (2 * m + 1)
  simp [Real.LameBoundary] at hb
  have key := p1l_cos_rec hk hw false (j := ((2 * (q + 1) + 1 : ℕ) : ℝ))
    (by simp [hb.1])
    (by rw [show ((2 * (q + 1) + 1 : ℕ) : ℝ) * (π / 2) = ((q + 1 : ℕ) : ℝ) * π + π / 2 by
      push_cast; ring, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero, mul_zero]) hb.2
  rw [show ((2 * (q + 1) + 1 : ℕ) : ℝ) + 2 = ((2 * (q + 1 + 1) + 1 : ℕ) : ℝ) by push_cast; ring,
    show ((2 * (q + 1) + 1 : ℕ) : ℝ) - 2 = ((2 * (q) + 1 : ℕ) : ℝ) by push_cast; ring] at key
  simp only [X, H, Real.lameCosCoeff, LameRecurrence.alpha, LameRecurrence.beta,
    LameRecurrence.gamma, Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false]
  simp only [↓reduceIte, Bool.false_eq_true] at key ⊢
  push_cast at key ⊢
  linear_combination key

/-- DLMF 29.6.27: the normalization of the coefficients `C_{2p+1}` (both series converge). -/
@[dlmf 29.6.E27]
theorem Real.lameEck_odd_fourierC_normalization
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k false (2 * p + 1)
    ∃ S T : ℝ, HasSum (fun p => C p ^ 2) S ∧
      HasSum (fun p => C p * C (p + 1)) T ∧
      (1 - k ^ 2 / 2) * S - k ^ 2 / 2 * (C 0 ^ 2 / 2 + T) = 1 := by
  intro C
  have hk := l29_sq_lt_one hk0 hk1
  have hE := p2l_continuous_lameEck hν hk0 hk1 (2 * m + 1)
  have h := p2l_lameEck_cos_integral hν hk0 hk1 (2 * m + 1) false
    (g := fun x => Real.lameEck ν (2 * m + 1) x k * Real.jacobiDnm x (k ^ 2) ^ 2)
    (hE.mul ((p2l_continuous_dn hk).pow 2))
  simp only [Bool.false_eq_true, ↓reduceIte, p2l_integral_cos_dn_sq hk hE] at h
  rw [show (∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.lameEck ν (2 * m + 1) t k /
      Real.jacobiDnm t (k ^ 2) * (Real.lameEck ν (2 * m + 1) t k * Real.jacobiDnm t (k ^ 2) ^ 2)) =
      ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm t (k ^ 2) *
        Real.lameEck ν (2 * m + 1) t k ^ 2 by
      congr 1; funext t; field_simp [(Real.jacobiDnm_pos hk t).ne'],
    Real.lameEck_normalization hν hk0 hk1] at h
  have h2 := h.mul_left (4 / π)
  rw [show 4 / π * (π / 4) = 1 by field_simp] at h2
  have hCs : Summable fun p => |C p| := by
    have hs := p2l_lame_summable_cos hk0 hk1
      (p2l_contDiff_lame hk (Real.lameEck_isLameEigenfunction hν hk0 hk1 (2 * m + 1)).1)
      (fun x => (Real.lameEck_parity hν hk0 hk1 _ x).2.2.2.2)
      (fun x => (Real.lameEck_parity hν hk0 hk1 _ x).2.1)
      (fun x => (Real.lameEck_parity hν hk0 hk1 _ x).1) false
    refine (hs.comp_injective (fun a b hab => by simpa using hab :
      Function.Injective fun p : ℕ => 2 * p + 1)).of_nonneg_of_le
      (fun _ => abs_nonneg _) fun p => ?_
    simp only [Function.comp, C, pow_mul, pow_succ]; norm_num
  have h3 := p2l_hasSum_two_mul_add 1 (fun j hj => ?_) h2
  · obtain ⟨S, T, hS, hT, hST⟩ := p2l_norm_seq hCs k 1 (C 0) (by
      convert h3 using 1
      funext p
      rcases p with _ | p
      · simp only [C]; norm_num [pow_mul, pow_succ]; field_simp
      · have e : Int.natAbs (((2 * (p + 1) + 1 : ℕ) : ℤ) - 2) = 2 * p + 1 := by omega
        simp only [C, e]; norm_num [pow_mul, pow_succ]
        rw [show 2 * (p + 1) + 1 + 2 = 2 * (p + 1 + 1) + 1 by ring]
        field_simp)
    exact ⟨S, T, by simpa using hS, hT, by linear_combination hST⟩
  · have := (p2l_neg_one_pow_mod j).1.2 (by omega)
    simp [pow_mul, pow_succ, this]

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

/-- DLMF 29.6.30: `∑ AC = (4/π) ∫₀^K (Ec^{2m+1}_ν)² dx`. -/
@[dlmf 29.6.E30]
theorem Real.lameEck_odd_fourier_parseval
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k true (2 * p + 1)
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m + 1) x k) k false (2 * p + 1)
    HasSum (fun p => A p * C p)
      (4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.lameEck ν (2 * m + 1) x k ^ 2) := by
  intro A C
  have hk := l29_sq_lt_one hk0 hk1
  have h := p2l_lameEck_cos_integral hν hk0 hk1 (2 * m + 1) true
    (g := fun x => Real.lameEck ν (2 * m + 1) x k) (p2l_continuous_lameEck hν hk0 hk1 _)
  simp only [↓reduceIte, div_one, p2l_integral_cos_false] at h
  have h2 := h.mul_left (4 / π)
  convert p2l_hasSum_two_mul_add 1 (fun j hj => ?_) h2 using 1
  · funext p
    simp only [A, C, pow_succ, pow_mul]; norm_num
    field_simp
  · congr 1; congr 1; funext t; ring
  · have := (p2l_neg_one_pow_mod j).1.2 (by omega)
    simp [pow_succ, pow_mul, this]

/-- DLMF 29.6.31: `Es^{2m+1}_ν(x, k²) = ∑_{p≥0} B_{2p+1} sin((2p+1)φ)` for real `x`, with `φ = π/2 -
am(x, k)` and the Fourier coefficients `B_{2p+1}` of `Real.lameSinCoeff` (weighted by `dn`). -/
@[dlmf 29.6.E31]
theorem Real.lameEsk_odd_hasSum_fourierB
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∀ x : ℝ, HasSum (fun p : ℕ =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k true (2 * p + 1) *
      Real.sin (((2 * p + 1 : ℕ) : ℝ) * Real.lamePhi x k)) (Real.lameEsk ν (2 * m + 1) x k) := by
  intro x
  have hs := p2l_lameEsk_sin hν hk0 hk1 (2 * m + 1) true x
  simp only [↓reduceIte, div_one] at hs
  convert p2l_hasSum_two_mul_add 1 (fun j hj => ?_) hs using 1
  · funext p
    simp [pow_succ, pow_mul]
  · have := (p2l_neg_one_pow_mod j).1.2 (by omega)
    simp [pow_succ, pow_mul, this]

/-- DLMF 29.6.32–29.6.33: with `H = 2·(eigenvalue) - ν(ν+1)k²`, `(β₀ - H)B₀ + α₀B₁ = 0` for the
recurrence `B1` (index `p` of the coefficient list). Proved from Lamé's equation
by Green's identity (`p1l_cos_rec`, `p1l_sin_rec`). -/
@[dlmf 29.6.E32, dlmf 29.6.E33]
theorem Real.lameEsk_odd_fourierB_rec_zero
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k true (2 * p + 1)
    let H : ℝ := 2 * Real.lameBk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2
    (LameRecurrence.B1.beta ν k 0 - H) * B 0 +
      LameRecurrence.B1.alpha ν k 0 * B 1 = 0 := by
  intro X H
  have hk := l29_sq_lt_one hk0 hk1
  obtain ⟨hw, hb, -⟩ := Real.lameEsk_isLameEigenfunction hν hk0 hk1 (2 * m + 1)
  simp [Real.LameBoundary] at hb
  have key := p1l_sin_rec hk hw true (j := 1) (by simp)
    (by simp [hb.1]) hb.2
  simp only [X, H, Real.lameSinCoeff, LameRecurrence.alpha, LameRecurrence.beta, ite_true]
  norm_num [Real.cos_neg, Real.sin_neg] at key ⊢
  linear_combination key

/-- DLMF 29.6.34: `γ_p B_{p-1} + (β_p - H)B_p + α_p B_{p+1} = 0`, `p ≥ 1` (indices of the
coefficient list), for the recurrence `B1`. Proved from Lamé's equation
by Green's identity (`p1l_cos_rec`, `p1l_sin_rec`). -/
@[dlmf 29.6.E34]
theorem Real.lameEsk_odd_fourierB_rec
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k true (2 * p + 1)
    let H : ℝ := 2 * Real.lameBk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2
    ∀ p : ℕ, 1 ≤ p → LameRecurrence.B1.gamma ν k p * B (p - 1) +
      (LameRecurrence.B1.beta ν k p - H) * B p +
      LameRecurrence.B1.alpha ν k p * B (p + 1) = 0 := by
  intro X H p hp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hk := l29_sq_lt_one hk0 hk1
  obtain ⟨hw, hb, -⟩ := Real.lameEsk_isLameEigenfunction hν hk0 hk1 (2 * m + 1)
  simp [Real.LameBoundary] at hb
  have key := p1l_sin_rec hk hw true (j := ((2 * (q + 1) + 1 : ℕ) : ℝ))
    (by rw [show ((2 * (q + 1) + 1 : ℕ) : ℝ) * (π / 2) = ((q + 1 : ℕ) : ℝ) * π + π / 2 by
      push_cast; ring, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero, mul_zero])
    (by simp [hb.1]) hb.2
  rw [show ((2 * (q + 1) + 1 : ℕ) : ℝ) + 2 = ((2 * (q + 1 + 1) + 1 : ℕ) : ℝ) by push_cast; ring,
    show ((2 * (q + 1) + 1 : ℕ) : ℝ) - 2 = ((2 * (q) + 1 : ℕ) : ℝ) by push_cast; ring] at key
  simp only [X, H, Real.lameSinCoeff, LameRecurrence.alpha, LameRecurrence.beta,
    LameRecurrence.gamma, Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false, ite_true]
  simp only [↓reduceIte] at key ⊢
  push_cast at key ⊢
  linear_combination key

/-- DLMF 29.6.35: the normalization of the coefficients `B_{2p+1}`. -/
@[dlmf 29.6.E35]
theorem Real.lameEsk_odd_fourierB_normalization
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k true (2 * p + 1)
    HasSum (fun p => B p ^ 2) 1 := by
  intro B
  have hk := l29_sq_lt_one hk0 hk1
  have h := p2l_lameEsk_sin_integral hν hk0 hk1 (2 * m + 1) true
    (g := fun x => Real.lameEsk ν (2 * m + 1) x k * Real.jacobiDnm x (k ^ 2))
    ((p2l_continuous_lameEsk hν hk0 hk1 _).mul (p2l_continuous_dn hk))
  simp only [↓reduceIte, div_one, p2l_integral_sin_true] at h
  rw [show (∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.lameEsk ν (2 * m + 1) t k *
      (Real.lameEsk ν (2 * m + 1) t k * Real.jacobiDnm t (k ^ 2))) =
      ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm t (k ^ 2) *
        Real.lameEsk ν (2 * m + 1) t k ^ 2 by congr 1; funext t; ring,
    Real.lameEsk_normalization hν hk0 hk1] at h
  have h2 := h.mul_left (4 / π)
  rw [show 4 / π * (π / 4) = 1 by field_simp] at h2
  convert p2l_hasSum_two_mul_add 1 (fun j hj => ?_) h2 using 1
  · funext p
    simp only [B, pow_succ, pow_mul]; norm_num
    field_simp
  · have := (p2l_neg_one_pow_mod j).1.2 (by omega)
    simp [pow_succ, pow_mul, this]

/-- DLMF 29.6.36: positivity (`-dEs/dz` at `z = K` divided by `dn(K)`). -/
@[dlmf 29.6.E36]
theorem Real.lameEsk_odd_fourierB_pos
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k true (2 * p + 1)
    ∃ S, HasSum (fun p => ((2 * p + 1 : ℕ) : ℝ) * B p) S ∧ 0 < S := by
  intro B
  have hk := l29_sq_lt_one hk0 hk1
  have hpar := Real.lameEsk_parity hν hk0 hk1 (2 * m + 1)
  have hsol := (Real.lameEsk_isLameEigenfunction hν hk0 hk1 (2 * m + 1)).1
  have hs := p2l_hasSum_mul_sinCoeff hk0 hk1 hsol (fun x => (hpar x).2.2.2.2)
    (fun x => (hpar x).2.1) (fun x => (hpar x).1) true
  have hK : Real.lameEsk ν (2 * m + 1) (Real.compEllIntKm (k ^ 2)) k = 0 := by
    have := (hpar (Real.compEllIntKm (k ^ 2))).2.1
    rw [show 2 * Real.compEllIntKm (k ^ 2) - Real.compEllIntKm (k ^ 2) =
      Real.compEllIntKm (k ^ 2) by ring] at this
    linarith
  have hpos := p2l_deriv_phiFun_pos hk hsol.differentiable hK
    (Real.lameEsk_deriv_K_neg hν hk0 hk1 _) true
  refine ⟨_, ?_, hpos⟩
  convert p2l_hasSum_two_mul_add 1 (fun j hj => ?_) hs using 1
  · funext p
    simp only [B, pow_succ, pow_mul]; norm_num
  · have := (p2l_neg_one_pow_mod j).1.2 (by omega)
    simp [pow_succ, pow_mul, this]

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
unweighted Fourier coefficients `D_{2p+1}`. -/
@[dlmf 29.6.E38]
theorem Real.lameEsk_odd_hasSum_fourierD
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∀ x : ℝ, HasSum (fun p : ℕ => Real.jacobiDnm x (k ^ 2) * (
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k false (2 * p + 1) *
      Real.sin (((2 * p + 1 : ℕ) : ℝ) * Real.lamePhi x k))) (Real.lameEsk ν (2 * m + 1) x k) := by
  intro x
  have hd := (Real.jacobiDnm_pos (l29_sq_lt_one hk0 hk1) x).ne'
  have hs := (p2l_lameEsk_sin hν hk0 hk1 (2 * m + 1) false x).mul_left
    (Real.jacobiDnm x (k ^ 2))
  simp only [Bool.false_eq_true, ↓reduceIte, mul_div_cancel₀ _ hd] at hs
  convert p2l_hasSum_two_mul_add 1 (fun j hj => ?_) hs using 1
  · funext p
    simp [pow_succ, pow_mul]
  · have := (p2l_neg_one_pow_mod j).1.2 (by omega)
    simp [pow_succ, pow_mul, this]

/-- DLMF 29.6.39: `(β₀ - H)D₀ + α₀D₁ = 0` for the recurrence `D1`.
Proved from Lamé's equation by Green's identity (`p1l_cos_rec`, `p1l_sin_rec`). -/
@[dlmf 29.6.E39]
theorem Real.lameEsk_odd_fourierD_rec_zero
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k false (2 * p + 1)
    let H : ℝ := 2 * Real.lameBk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2
    (LameRecurrence.D1.beta ν k 0 - H) * D 0 +
      LameRecurrence.D1.alpha ν k 0 * D 1 = 0 := by
  intro X H
  have hk := l29_sq_lt_one hk0 hk1
  obtain ⟨hw, hb, -⟩ := Real.lameEsk_isLameEigenfunction hν hk0 hk1 (2 * m + 1)
  simp [Real.LameBoundary] at hb
  have key := p1l_sin_rec hk hw false (j := 1) (by simp)
    (by simp [hb.1]) hb.2
  simp only [X, H, Real.lameSinCoeff, LameRecurrence.alpha, LameRecurrence.beta]
  norm_num [Real.cos_neg, Real.sin_neg] at key ⊢
  linear_combination key

/-- DLMF 29.6.40: `γ_p D_{p-1} + (β_p - H)D_p + α_p D_{p+1} = 0`, `p ≥ 1`, for the recurrence `D1`.
Proved from Lamé's equation by Green's identity (`p1l_cos_rec`, `p1l_sin_rec`). -/
@[dlmf 29.6.E40]
theorem Real.lameEsk_odd_fourierD_rec
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k false (2 * p + 1)
    let H : ℝ := 2 * Real.lameBk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2
    ∀ p : ℕ, 1 ≤ p → LameRecurrence.D1.gamma ν k p * D (p - 1) +
      (LameRecurrence.D1.beta ν k p - H) * D p +
      LameRecurrence.D1.alpha ν k p * D (p + 1) = 0 := by
  intro X H p hp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hk := l29_sq_lt_one hk0 hk1
  obtain ⟨hw, hb, -⟩ := Real.lameEsk_isLameEigenfunction hν hk0 hk1 (2 * m + 1)
  simp [Real.LameBoundary] at hb
  have key := p1l_sin_rec hk hw false (j := ((2 * (q + 1) + 1 : ℕ) : ℝ))
    (by rw [show ((2 * (q + 1) + 1 : ℕ) : ℝ) * (π / 2) = ((q + 1 : ℕ) : ℝ) * π + π / 2 by
      push_cast; ring, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero, mul_zero])
    (by simp [hb.1]) hb.2
  rw [show ((2 * (q + 1) + 1 : ℕ) : ℝ) + 2 = ((2 * (q + 1 + 1) + 1 : ℕ) : ℝ) by push_cast; ring,
    show ((2 * (q + 1) + 1 : ℕ) : ℝ) - 2 = ((2 * (q) + 1 : ℕ) : ℝ) by push_cast; ring] at key
  simp only [X, H, Real.lameSinCoeff, LameRecurrence.alpha, LameRecurrence.beta,
    LameRecurrence.gamma, Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false]
  simp only [↓reduceIte, Bool.false_eq_true] at key ⊢
  push_cast at key ⊢
  linear_combination key

/-- DLMF 29.6.42: the normalization of the coefficients `D_{2p+1}` (both series converge). -/
@[dlmf 29.6.E42]
theorem Real.lameEsk_odd_fourierD_normalization
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k false (2 * p + 1)
    ∃ S T : ℝ, HasSum (fun p => D p ^ 2) S ∧
      HasSum (fun p => D p * D (p + 1)) T ∧
      (1 - k ^ 2 / 2) * S + k ^ 2 / 2 * (D 0 ^ 2 / 2 - T) = 1 := by
  intro D
  have hk := l29_sq_lt_one hk0 hk1
  have hE := p2l_continuous_lameEsk hν hk0 hk1 (2 * m + 1)
  have h := p2l_lameEsk_sin_integral hν hk0 hk1 (2 * m + 1) false
    (g := fun x => Real.lameEsk ν (2 * m + 1) x k * Real.jacobiDnm x (k ^ 2) ^ 2)
    (hE.mul ((p2l_continuous_dn hk).pow 2))
  simp only [Bool.false_eq_true, ↓reduceIte, p2l_integral_sin_dn_sq hk hE] at h
  rw [show (∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.lameEsk ν (2 * m + 1) t k /
      Real.jacobiDnm t (k ^ 2) * (Real.lameEsk ν (2 * m + 1) t k * Real.jacobiDnm t (k ^ 2) ^ 2)) =
      ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm t (k ^ 2) *
        Real.lameEsk ν (2 * m + 1) t k ^ 2 by
      congr 1; funext t; field_simp [(Real.jacobiDnm_pos hk t).ne'],
    Real.lameEsk_normalization hν hk0 hk1] at h
  have h2 := h.mul_left (4 / π)
  rw [show 4 / π * (π / 4) = 1 by field_simp] at h2
  have hCs : Summable fun p => |D p| := by
    have hs := p2l_lame_summable_sin hk0 hk1
      (p2l_contDiff_lame hk (Real.lameEsk_isLameEigenfunction hν hk0 hk1 (2 * m + 1)).1)
      (fun x => (Real.lameEsk_parity hν hk0 hk1 _ x).2.2.2.2)
      (fun x => (Real.lameEsk_parity hν hk0 hk1 _ x).2.1)
      (fun x => (Real.lameEsk_parity hν hk0 hk1 _ x).1) false
    refine (hs.comp_injective (fun a b hab => by simpa using hab :
      Function.Injective fun p : ℕ => 2 * p + 1)).of_nonneg_of_le
      (fun _ => abs_nonneg _) fun p => ?_
    simp only [Function.comp, D, pow_mul, pow_succ]; norm_num
  have h3 := p2l_hasSum_two_mul_add 1 (fun j hj => ?_) h2
  · obtain ⟨S, T, hS, hT, hST⟩ := p2l_norm_seq hCs k 1 (-D 0) (by
      convert h3 using 1
      funext p
      rcases p with _ | p
      · simp only [D]; norm_num [pow_mul, pow_succ]; field_simp
      · have e : Int.natAbs (((2 * (p + 1) + 1 : ℕ) : ℤ) - 2) = 2 * p + 1 := by omega
        simp only [D, e]; norm_num [pow_mul, pow_succ]
        rw [show 2 * (p + 1) + 1 + 2 = 2 * (p + 1 + 1) + 1 by ring]
        field_simp)
    exact ⟨S, T, by simpa using hS, hT, by linear_combination hST⟩
  · have := (p2l_neg_one_pow_mod j).1.2 (by omega)
    simp [pow_mul, pow_succ, this]

/-- DLMF 29.6.43: positivity (`-d(Es/dn)/dz` at `z = K`). -/
@[dlmf 29.6.E43]
theorem Real.lameEsk_odd_fourierD_pos
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k false (2 * p + 1)
    ∃ S, HasSum (fun p => ((2 * p + 1 : ℕ) : ℝ) * D p) S ∧ 0 < S := by
  intro D
  have hk := l29_sq_lt_one hk0 hk1
  have hpar := Real.lameEsk_parity hν hk0 hk1 (2 * m + 1)
  have hsol := (Real.lameEsk_isLameEigenfunction hν hk0 hk1 (2 * m + 1)).1
  have hs := p2l_hasSum_mul_sinCoeff hk0 hk1 hsol (fun x => (hpar x).2.2.2.2)
    (fun x => (hpar x).2.1) (fun x => (hpar x).1) false
  have hK : Real.lameEsk ν (2 * m + 1) (Real.compEllIntKm (k ^ 2)) k = 0 := by
    have := (hpar (Real.compEllIntKm (k ^ 2))).2.1
    rw [show 2 * Real.compEllIntKm (k ^ 2) - Real.compEllIntKm (k ^ 2) =
      Real.compEllIntKm (k ^ 2) by ring] at this
    linarith
  have hpos := p2l_deriv_phiFun_pos hk hsol.differentiable hK
    (Real.lameEsk_deriv_K_neg hν hk0 hk1 _) false
  refine ⟨_, ?_, hpos⟩
  convert p2l_hasSum_two_mul_add 1 (fun j hj => ?_) hs using 1
  · funext p
    simp only [D, pow_succ, pow_mul]; norm_num
  · have := (p2l_neg_one_pow_mod j).1.2 (by omega)
    simp [pow_succ, pow_mul, this]

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

/-- DLMF 29.6.45: `∑ BD = (4/π) ∫₀^K (Es^{2m+1}_ν)² dx`. -/
@[dlmf 29.6.E45]
theorem Real.lameEsk_odd_fourier_parseval
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k true (2 * p + 1)
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 1) x k) k false (2 * p + 1)
    HasSum (fun p => B p * D p)
      (4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.lameEsk ν (2 * m + 1) x k ^ 2) := by
  intro B D
  have hk := l29_sq_lt_one hk0 hk1
  have h := p2l_lameEsk_sin_integral hν hk0 hk1 (2 * m + 1) true
    (g := fun x => Real.lameEsk ν (2 * m + 1) x k) (p2l_continuous_lameEsk hν hk0 hk1 _)
  simp only [↓reduceIte, div_one, p2l_integral_sin_false] at h
  have h2 := h.mul_left (4 / π)
  convert p2l_hasSum_two_mul_add 1 (fun j hj => ?_) h2 using 1
  · funext p
    simp only [B, D, pow_succ, pow_mul]; norm_num
    field_simp
  · congr 1; congr 1; funext t; ring
  · have := (p2l_neg_one_pow_mod j).1.2 (by omega)
    simp [pow_succ, pow_mul, this]

/-- DLMF 29.6.46: `Es^{2m+2}_ν(x, k²) = ∑_{p≥0} B_{2p+2} sin((2p+2)φ)` for real `x`, with `φ = π/2 -
am(x, k)` and the Fourier coefficients `B_{2p+2}` of `Real.lameSinCoeff` (weighted by `dn`). -/
@[dlmf 29.6.E46]
theorem Real.lameEsk_even_hasSum_fourierB
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∀ x : ℝ, HasSum (fun p : ℕ =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k true (2 * p + 2) *
      Real.sin (((2 * p + 2 : ℕ) : ℝ) * Real.lamePhi x k)) (Real.lameEsk ν (2 * m + 2) x k) := by
  intro x
  have hs := p2l_lameEsk_sin hν hk0 hk1 (2 * m + 2) true x
  simp only [↓reduceIte, div_one] at hs
  have h2 := p2l_hasSum_two_mul_add 0 (fun j hj => ?_) hs
  · rw [← hasSum_nat_add_iff' 1] at h2
    convert h2 using 1
    · funext p
      simp [pow_succ, pow_mul, mul_add]
    · simp
  · have := (p2l_neg_one_pow_mod j).2.2 (by omega)
    simp [pow_succ, pow_mul, this]

/-- DLMF 29.6.47–29.6.48: with `H = 2·(eigenvalue) - ν(ν+1)k²`, `(β₀ - H)B₀ + α₀B₁ = 0` for the
recurrence `B2` (index `p` of the coefficient list). Proved from Lamé's equation
by Green's identity (`p1l_cos_rec`, `p1l_sin_rec`). -/
@[dlmf 29.6.E47, dlmf 29.6.E48]
theorem Real.lameEsk_even_fourierB_rec_zero
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k true (2 * p + 2)
    let H : ℝ := 2 * Real.lameBk ν (2 * m + 2) k - ν * (ν + 1) * k ^ 2
    (LameRecurrence.B2.beta ν k 0 - H) * B 0 +
      LameRecurrence.B2.alpha ν k 0 * B 1 = 0 := by
  intro X H
  have hk := l29_sq_lt_one hk0 hk1
  obtain ⟨hw, hb, -⟩ := Real.lameEsk_isLameEigenfunction hν hk0 hk1 (2 * m + 2)
  simp [Real.LameBoundary] at hb
  have key := p1l_sin_rec hk hw true (j := 2) (by simp [hb.1])
    (by rw [show (2 : ℝ) * (π / 2) = π by ring]; simp) hb.2
  simp only [X, H, Real.lameSinCoeff, LameRecurrence.alpha, LameRecurrence.beta, ite_true]
  norm_num [Real.cos_neg, Real.sin_neg] at key ⊢
  linear_combination key

/-- DLMF 29.6.49: `γ_p B_{p-1} + (β_p - H)B_p + α_p B_{p+1} = 0`, `p ≥ 1` (indices of the
coefficient list), for the recurrence `B2`. Proved from Lamé's equation
by Green's identity (`p1l_cos_rec`, `p1l_sin_rec`). -/
@[dlmf 29.6.E49]
theorem Real.lameEsk_even_fourierB_rec
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k true (2 * p + 2)
    let H : ℝ := 2 * Real.lameBk ν (2 * m + 2) k - ν * (ν + 1) * k ^ 2
    ∀ p : ℕ, 1 ≤ p → LameRecurrence.B2.gamma ν k p * B (p - 1) +
      (LameRecurrence.B2.beta ν k p - H) * B p +
      LameRecurrence.B2.alpha ν k p * B (p + 1) = 0 := by
  intro X H p hp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hk := l29_sq_lt_one hk0 hk1
  obtain ⟨hw, hb, -⟩ := Real.lameEsk_isLameEigenfunction hν hk0 hk1 (2 * m + 2)
  simp [Real.LameBoundary] at hb
  have key := p1l_sin_rec hk hw true (j := ((2 * (q + 1) + 2 : ℕ) : ℝ))
    (by simp [hb.1])
    (by rw [show ((2 * (q + 1) + 2 : ℕ) : ℝ) * (π / 2) = ((q + 2 : ℕ) : ℝ) * π by push_cast; ring,
      Real.sin_nat_mul_pi, mul_zero]) hb.2
  rw [show ((2 * (q + 1) + 2 : ℕ) : ℝ) + 2 = ((2 * (q + 1 + 1) + 2 : ℕ) : ℝ) by push_cast; ring,
    show ((2 * (q + 1) + 2 : ℕ) : ℝ) - 2 = ((2 * (q) + 2 : ℕ) : ℝ) by push_cast; ring] at key
  simp only [X, H, Real.lameSinCoeff, LameRecurrence.alpha, LameRecurrence.beta,
    LameRecurrence.gamma, Nat.add_sub_cancel, ite_true]
  simp only [↓reduceIte] at key ⊢
  push_cast at key ⊢
  linear_combination key

/-- DLMF 29.6.50: the normalization of the coefficients `B_{2p+2}`. -/
@[dlmf 29.6.E50]
theorem Real.lameEsk_even_fourierB_normalization
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k true (2 * p + 2)
    HasSum (fun p => B p ^ 2) 1 := by
  intro B
  have hk := l29_sq_lt_one hk0 hk1
  have h := p2l_lameEsk_sin_integral hν hk0 hk1 (2 * m + 2) true
    (g := fun x => Real.lameEsk ν (2 * m + 2) x k * Real.jacobiDnm x (k ^ 2))
    ((p2l_continuous_lameEsk hν hk0 hk1 _).mul (p2l_continuous_dn hk))
  simp only [↓reduceIte, div_one, p2l_integral_sin_true] at h
  rw [show (∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.lameEsk ν (2 * m + 2) t k *
      (Real.lameEsk ν (2 * m + 2) t k * Real.jacobiDnm t (k ^ 2))) =
      ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm t (k ^ 2) *
        Real.lameEsk ν (2 * m + 2) t k ^ 2 by congr 1; funext t; ring,
    Real.lameEsk_normalization hν hk0 hk1] at h
  have h2 := h.mul_left (4 / π)
  rw [show 4 / π * (π / 4) = 1 by field_simp] at h2
  have h3 := p2l_hasSum_two_mul_add 0 (fun j hj => ?_) h2
  · rw [← hasSum_nat_add_iff' 1] at h3
    convert h3 using 1
    · funext p
      simp only [B, pow_succ, pow_mul]; norm_num
      rw [show 2 * (p + 1) = 2 * p + 2 by ring]
      field_simp
    · simp [Real.lameSinCoeff]
  · have := (p2l_neg_one_pow_mod j).2.2 (by omega)
    simp [pow_succ, pow_mul, this]

/-- DLMF 29.6.51: positivity (`-dEs/dz` at `z = K` divided by `dn(K)`). -/
@[dlmf 29.6.E51]
theorem Real.lameEsk_even_fourierB_pos
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k true (2 * p + 2)
    ∃ S, HasSum (fun p => ((2 * p + 2 : ℕ) : ℝ) * B p) S ∧ 0 < S := by
  intro B
  have hk := l29_sq_lt_one hk0 hk1
  have hpar := Real.lameEsk_parity hν hk0 hk1 (2 * m + 2)
  have hsol := (Real.lameEsk_isLameEigenfunction hν hk0 hk1 (2 * m + 2)).1
  have hs := p2l_hasSum_mul_sinCoeff hk0 hk1 hsol (fun x => (hpar x).2.2.2.2)
    (fun x => (hpar x).2.1) (fun x => (hpar x).1) true
  have hK : Real.lameEsk ν (2 * m + 2) (Real.compEllIntKm (k ^ 2)) k = 0 := by
    have := (hpar (Real.compEllIntKm (k ^ 2))).2.1
    rw [show 2 * Real.compEllIntKm (k ^ 2) - Real.compEllIntKm (k ^ 2) =
      Real.compEllIntKm (k ^ 2) by ring] at this
    linarith
  have hpos := p2l_deriv_phiFun_pos hk hsol.differentiable hK
    (Real.lameEsk_deriv_K_neg hν hk0 hk1 _) true
  refine ⟨_, ?_, hpos⟩
  have h3 := p2l_hasSum_two_mul_add 0 (fun j hj => ?_) hs
  · rw [← hasSum_nat_add_iff' 1] at h3
    convert h3 using 1
    · funext p
      simp only [B, pow_succ, pow_mul]; norm_num
      rw [show 2 * (p + 1) = 2 * p + 2 by ring]; ring
    · simp
  · have := (p2l_neg_one_pow_mod j).2.2 (by omega)
    simp [pow_succ, pow_mul, this]

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
unweighted Fourier coefficients `D_{2p+2}`. -/
@[dlmf 29.6.E53]
theorem Real.lameEsk_even_hasSum_fourierD
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∀ x : ℝ, HasSum (fun p : ℕ => Real.jacobiDnm x (k ^ 2) * (
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k false (2 * p + 2) *
      Real.sin (((2 * p + 2 : ℕ) : ℝ) * Real.lamePhi x k))) (Real.lameEsk ν (2 * m + 2) x k) := by
  intro x
  have hd := (Real.jacobiDnm_pos (l29_sq_lt_one hk0 hk1) x).ne'
  have hs := (p2l_lameEsk_sin hν hk0 hk1 (2 * m + 2) false x).mul_left
    (Real.jacobiDnm x (k ^ 2))
  simp only [Bool.false_eq_true, ↓reduceIte, mul_div_cancel₀ _ hd] at hs
  have h2 := p2l_hasSum_two_mul_add 0 (fun j hj => ?_) hs
  · rw [← hasSum_nat_add_iff' 1] at h2
    convert h2 using 1
    · funext p
      simp [pow_succ, pow_mul, mul_add]
    · simp
  · have := (p2l_neg_one_pow_mod j).2.2 (by omega)
    simp [pow_succ, pow_mul, this]

/-- DLMF 29.6.54: `(β₀ - H)D₀ + α₀D₁ = 0` for the recurrence `D2`.
Proved from Lamé's equation by Green's identity (`p1l_cos_rec`, `p1l_sin_rec`). -/
@[dlmf 29.6.E54]
theorem Real.lameEsk_even_fourierD_rec_zero
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k false (2 * p + 2)
    let H : ℝ := 2 * Real.lameBk ν (2 * m + 2) k - ν * (ν + 1) * k ^ 2
    (LameRecurrence.D2.beta ν k 0 - H) * D 0 +
      LameRecurrence.D2.alpha ν k 0 * D 1 = 0 := by
  intro X H
  have hk := l29_sq_lt_one hk0 hk1
  obtain ⟨hw, hb, -⟩ := Real.lameEsk_isLameEigenfunction hν hk0 hk1 (2 * m + 2)
  simp [Real.LameBoundary] at hb
  have key := p1l_sin_rec hk hw false (j := 2) (by simp [hb.1])
    (by rw [show (2 : ℝ) * (π / 2) = π by ring]; simp) hb.2
  simp only [X, H, Real.lameSinCoeff, LameRecurrence.alpha, LameRecurrence.beta]
  norm_num [Real.cos_neg, Real.sin_neg] at key ⊢
  linear_combination key

/-- DLMF 29.6.55: `γ_p D_{p-1} + (β_p - H)D_p + α_p D_{p+1} = 0`, `p ≥ 1`, for the recurrence `D2`.
Proved from Lamé's equation by Green's identity (`p1l_cos_rec`, `p1l_sin_rec`). -/
@[dlmf 29.6.E55]
theorem Real.lameEsk_even_fourierD_rec
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k false (2 * p + 2)
    let H : ℝ := 2 * Real.lameBk ν (2 * m + 2) k - ν * (ν + 1) * k ^ 2
    ∀ p : ℕ, 1 ≤ p → LameRecurrence.D2.gamma ν k p * D (p - 1) +
      (LameRecurrence.D2.beta ν k p - H) * D p +
      LameRecurrence.D2.alpha ν k p * D (p + 1) = 0 := by
  intro X H p hp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hk := l29_sq_lt_one hk0 hk1
  obtain ⟨hw, hb, -⟩ := Real.lameEsk_isLameEigenfunction hν hk0 hk1 (2 * m + 2)
  simp [Real.LameBoundary] at hb
  have key := p1l_sin_rec hk hw false (j := ((2 * (q + 1) + 2 : ℕ) : ℝ))
    (by simp [hb.1])
    (by rw [show ((2 * (q + 1) + 2 : ℕ) : ℝ) * (π / 2) = ((q + 2 : ℕ) : ℝ) * π by push_cast; ring,
      Real.sin_nat_mul_pi, mul_zero]) hb.2
  rw [show ((2 * (q + 1) + 2 : ℕ) : ℝ) + 2 = ((2 * (q + 1 + 1) + 2 : ℕ) : ℝ) by push_cast; ring,
    show ((2 * (q + 1) + 2 : ℕ) : ℝ) - 2 = ((2 * (q) + 2 : ℕ) : ℝ) by push_cast; ring] at key
  simp only [X, H, Real.lameSinCoeff, LameRecurrence.alpha, LameRecurrence.beta,
    LameRecurrence.gamma, Nat.add_sub_cancel]
  simp only [↓reduceIte, Bool.false_eq_true] at key ⊢
  push_cast at key ⊢
  linear_combination key

/-- DLMF 29.6.57: the normalization of the coefficients `D_{2p+2}` (both series converge). -/
@[dlmf 29.6.E57]
theorem Real.lameEsk_even_fourierD_normalization
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k false (2 * p + 2)
    ∃ S T : ℝ, HasSum (fun p => D p ^ 2) S ∧
      HasSum (fun p => D p * D (p + 1)) T ∧
      (1 - k ^ 2 / 2) * S - k ^ 2 / 2 * T = 1 := by
  intro D
  have hk := l29_sq_lt_one hk0 hk1
  have hE := p2l_continuous_lameEsk hν hk0 hk1 (2 * m + 2)
  have h := p2l_lameEsk_sin_integral hν hk0 hk1 (2 * m + 2) false
    (g := fun x => Real.lameEsk ν (2 * m + 2) x k * Real.jacobiDnm x (k ^ 2) ^ 2)
    (hE.mul ((p2l_continuous_dn hk).pow 2))
  simp only [Bool.false_eq_true, ↓reduceIte, p2l_integral_sin_dn_sq hk hE] at h
  rw [show (∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.lameEsk ν (2 * m + 2) t k /
      Real.jacobiDnm t (k ^ 2) * (Real.lameEsk ν (2 * m + 2) t k * Real.jacobiDnm t (k ^ 2) ^ 2)) =
      ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm t (k ^ 2) *
        Real.lameEsk ν (2 * m + 2) t k ^ 2 by
      congr 1; funext t; field_simp [(Real.jacobiDnm_pos hk t).ne'],
    Real.lameEsk_normalization hν hk0 hk1] at h
  have h2 := h.mul_left (4 / π)
  rw [show 4 / π * (π / 4) = 1 by field_simp] at h2
  have hCs : Summable fun p => |D p| := by
    have hs := p2l_lame_summable_sin hk0 hk1
      (p2l_contDiff_lame hk (Real.lameEsk_isLameEigenfunction hν hk0 hk1 (2 * m + 2)).1)
      (fun x => (Real.lameEsk_parity hν hk0 hk1 _ x).2.2.2.2)
      (fun x => (Real.lameEsk_parity hν hk0 hk1 _ x).2.1)
      (fun x => (Real.lameEsk_parity hν hk0 hk1 _ x).1) false
    refine (hs.comp_injective (fun a b hab => by simpa using hab :
      Function.Injective fun p : ℕ => 2 * p + 2)).of_nonneg_of_le
      (fun _ => abs_nonneg _) fun p => ?_
    simp only [Function.comp, D, pow_mul, pow_succ]; norm_num
  have h3 := p2l_hasSum_two_mul_add 0 (fun j hj => ?_) h2
  · rw [← hasSum_nat_add_iff' 1] at h3
    obtain ⟨S, T, hS, hT, hST⟩ := p2l_norm_seq hCs k 1 0 (by
      convert h3 using 1
      · funext p
        rcases p with _ | p
        · have hz : Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k false 0 = 0 := by
            simp [Real.lameSinCoeff]
          simp only [D]; norm_num [pow_mul, pow_succ, hz]; field_simp
        · have e : Int.natAbs (((2 * (p + 1 + 1) + 0 : ℕ) : ℤ) - 2) = 2 * p + 2 := by omega
          simp only [D, e]; norm_num [pow_mul, pow_succ]
          rw [show 2 * (p + 1) + 2 = 2 * (p + 1 + 1) by ring]
          simp only [show ¬ (2 * (p + 1 + 1) ≤ 1) by omega, ↓reduceIte]
          field_simp
      · simp [Real.lameSinCoeff])
    exact ⟨S, T, by simpa using hS, hT, by linear_combination hST⟩
  · have := (p2l_neg_one_pow_mod j).2.2 (by omega)
    simp [pow_mul, pow_succ, this]

/-- DLMF 29.6.58: positivity (`-d(Es/dn)/dz` at `z = K`). -/
@[dlmf 29.6.E58]
theorem Real.lameEsk_even_fourierD_pos
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k false (2 * p + 2)
    ∃ S, HasSum (fun p => ((2 * p + 2 : ℕ) : ℝ) * D p) S ∧ 0 < S := by
  intro D
  have hk := l29_sq_lt_one hk0 hk1
  have hpar := Real.lameEsk_parity hν hk0 hk1 (2 * m + 2)
  have hsol := (Real.lameEsk_isLameEigenfunction hν hk0 hk1 (2 * m + 2)).1
  have hs := p2l_hasSum_mul_sinCoeff hk0 hk1 hsol (fun x => (hpar x).2.2.2.2)
    (fun x => (hpar x).2.1) (fun x => (hpar x).1) false
  have hK : Real.lameEsk ν (2 * m + 2) (Real.compEllIntKm (k ^ 2)) k = 0 := by
    have := (hpar (Real.compEllIntKm (k ^ 2))).2.1
    rw [show 2 * Real.compEllIntKm (k ^ 2) - Real.compEllIntKm (k ^ 2) =
      Real.compEllIntKm (k ^ 2) by ring] at this
    linarith
  have hpos := p2l_deriv_phiFun_pos hk hsol.differentiable hK
    (Real.lameEsk_deriv_K_neg hν hk0 hk1 _) false
  refine ⟨_, ?_, hpos⟩
  have h3 := p2l_hasSum_two_mul_add 0 (fun j hj => ?_) hs
  · rw [← hasSum_nat_add_iff' 1] at h3
    convert h3 using 1
    · funext p
      simp only [D, pow_succ, pow_mul]; norm_num
      rw [show 2 * (p + 1) = 2 * p + 2 by ring]; ring
    · simp
  · have := (p2l_neg_one_pow_mod j).2.2 (by omega)
    simp [pow_succ, pow_mul, this]

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

/-- DLMF 29.6.60: `∑ BD = (4/π) ∫₀^K (Es^{2m+2}_ν)² dx`. -/
@[dlmf 29.6.E60]
theorem Real.lameEsk_even_fourier_parseval
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let B : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k true (2 * p + 2)
    let D : ℕ → ℝ := fun p =>
      Real.lameSinCoeff (fun x => Real.lameEsk ν (2 * m + 2) x k) k false (2 * p + 2)
    HasSum (fun p => B p * D p)
      (4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.lameEsk ν (2 * m + 2) x k ^ 2) := by
  intro B D
  have hk := l29_sq_lt_one hk0 hk1
  have h := p2l_lameEsk_sin_integral hν hk0 hk1 (2 * m + 2) true
    (g := fun x => Real.lameEsk ν (2 * m + 2) x k) (p2l_continuous_lameEsk hν hk0 hk1 _)
  simp only [↓reduceIte, div_one, p2l_integral_sin_false] at h
  have h2 := h.mul_left (4 / π)
  have h3 := p2l_hasSum_two_mul_add 0 (fun j hj => ?_) h2
  · rw [← hasSum_nat_add_iff' 1] at h3
    convert h3 using 1
    · funext p
      simp only [B, D, pow_succ, pow_mul]; norm_num
      rw [show 2 * (p + 1) = 2 * p + 2 by ring]
      field_simp
    · simp only [Real.lameSinCoeff]; norm_num
      congr 1; funext t; ring
  · have := (p2l_neg_one_pow_mod j).2.2 (by omega)
    simp [pow_succ, pow_mul, this]

/-- §29.6(i): for `ν = 2n` and `m = 0, 1, …, n` the Fourier coefficients `A_{2p}` of
`Ec^{2m}_{2n}` vanish for `p > n`, so `Ec^{2m}_{2n}` reduces to a Lamé polynomial (compare
§§29.12(i), 29.15(i)). Admitted. -/
@[dlmf 29.6.i]
theorem Real.lameEck_even_fourierA_eq_zero (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n)
    {p : ℕ} (hp : n < p) :
    Real.lameCosCoeff (fun x => Real.lameEck (2 * n : ℕ) (2 * m) x k) k true (2 * p) = 0 := by
  sorry

end DLMF.Lame

end
end
