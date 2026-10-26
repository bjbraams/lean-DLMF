/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.P2lFourier

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
(values at `x = K`) are proved from the expansions and `Ec(K) > 0`. The three-term
recurrences (29.6.3–29.6.4 and their analogues) are proved from Lamé's equation for the
coefficients defined as Fourier integrals: Green's identity against the test functions
`cos(jφ(x))`, `sin(jφ(x))` (unweighted) and `dn(x) cos(jφ(x))`, `dn(x) sin(jφ(x))` (weighted),
whose image under the Lamé operator is a combination of three such functions (`p1l_int_unw`,
`p1l_int_w`). All other statements are admitted.

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

/-! ### Fourier series from the `C²` theory (helpers) -/

/-- Reindexing a series supported on the residue class `r` mod `2`. -/
lemma p2l_hasSum_two_mul_add {f : ℕ → ℝ} {a : ℝ} (r : ℕ)
    (h0 : ∀ j, j % 2 ≠ r → f j = 0) (h : HasSum f a) : HasSum (fun p => f (2 * p + r)) a := by
  have hg : Function.Injective fun p : ℕ => 2 * p + r := fun a b hab => by simp at hab; omega
  refine (hg.hasSum_iff fun j hj => h0 j fun hjr => hj ⟨j / 2, ?_⟩).2 h
  simp only; omega

lemma p2l_neg_one_pow_mod (j : ℕ) : ((-1 : ℝ) ^ j = 1 ↔ j % 2 = 0) ∧
    ((-1 : ℝ) ^ j = -1 ↔ j % 2 = 1) := by
  rcases Nat.even_or_odd j with h | h
  · rw [h.neg_one_pow, Nat.even_iff.1 h]; norm_num
  · rw [h.neg_one_pow, Nat.odd_iff.1 h]; norm_num

/-- The cosine series of `Ec^m_ν / ρ` in `φ` (all indices, with the parity factor). -/
lemma p2l_lameEck_cos (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) (weighted : Bool)
    (x : ℝ) :
    HasSum (fun j : ℕ => (if j = 0 then 1 / 2 else 1) *
      ((1 + (-1) ^ m * (-1) ^ j) / 2 *
        Real.lameCosCoeff (fun x => Real.lameEck ν m x k) k weighted j) *
        Real.cos (j * Real.lamePhi x k))
      (Real.lameEck ν m x k / (if weighted then 1 else Real.jacobiDnm x (k ^ 2))) :=
  p2l_lame_hasSum_cos hk0 hk1
    (p2l_contDiff_lame (l29_sq_lt_one hk0 hk1) (Real.lameEck_isLameEigenfunction hν hk0 hk1 m).1)
    (fun x => (Real.lameEck_parity hν hk0 hk1 m x).2.2.2.2)
    (fun x => (Real.lameEck_parity hν hk0 hk1 m x).2.1)
    (fun x => (Real.lameEck_parity hν hk0 hk1 m x).1) weighted x

/-- The sine series of `Es^m_ν / ρ` in `φ` (all indices, with the parity factor). -/
lemma p2l_lameEsk_sin (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) (weighted : Bool)
    (x : ℝ) :
    HasSum (fun j : ℕ => ((1 - (-1) ^ (m + 1) * (-1) ^ j) / 2 *
        Real.lameSinCoeff (fun x => Real.lameEsk ν m x k) k weighted j) *
        Real.sin (j * Real.lamePhi x k))
      (Real.lameEsk ν m x k / (if weighted then 1 else Real.jacobiDnm x (k ^ 2))) :=
  p2l_lame_hasSum_sin hk0 hk1
    (p2l_contDiff_lame (l29_sq_lt_one hk0 hk1) (Real.lameEsk_isLameEigenfunction hν hk0 hk1 m).1)
    (fun x => (Real.lameEsk_parity hν hk0 hk1 m x).2.2.2.2)
    (fun x => (Real.lameEsk_parity hν hk0 hk1 m x).2.1)
    (fun x => (Real.lameEsk_parity hν hk0 hk1 m x).1) weighted x

lemma p2l_continuous_cos_phi (hk : k ^ 2 < 1) (j : ℕ) :
    Continuous fun t => Real.cos (j * Real.lamePhi t k) :=
  Real.continuous_cos.comp (continuous_const.mul
    (continuous_iff_continuousAt.2 fun t => (p1l_hasDerivAt_phi hk t).continuousAt))

lemma p2l_continuous_sin_phi (hk : k ^ 2 < 1) (j : ℕ) :
    Continuous fun t => Real.sin (j * Real.lamePhi t k) :=
  Real.continuous_sin.comp (continuous_const.mul
    (continuous_iff_continuousAt.2 fun t => (p1l_hasDerivAt_phi hk t).continuousAt))

/-- Termwise integration of the cosine series of `Ec^m_ν / ρ` against a continuous `g`. -/
lemma p2l_lameEck_cos_integral (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ)
    (weighted : Bool) {g : ℝ → ℝ} (hg : Continuous g) :
    HasSum (fun j : ℕ => (if j = 0 then 1 / 2 else 1) *
      ((1 + (-1) ^ m * (-1) ^ j) / 2 *
        Real.lameCosCoeff (fun x => Real.lameEck ν m x k) k weighted j) *
        ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.cos (j * Real.lamePhi t k) * g t)
      (∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
        Real.lameEck ν m t k / (if weighted then 1 else Real.jacobiDnm t (k ^ 2)) * g t) := by
  have hk := l29_sq_lt_one hk0 hk1
  have hpar := Real.lameEck_parity hν hk0 hk1 m
  exact p2l_hasSum_integral_mul (p2l_lame_summable_cos hk0 hk1
    (p2l_contDiff_lame hk (Real.lameEck_isLameEigenfunction hν hk0 hk1 m).1)
    (fun x => (hpar x).2.2.2.2) (fun x => (hpar x).2.1) (fun x => (hpar x).1) weighted)
    (p2l_continuous_cos_phi hk) (fun _ _ => Real.abs_cos_le_one _) hg
    (fun t => p2l_lameEck_cos hν hk0 hk1 m weighted t) _ _

/-- Termwise integration of the sine series of `Es^m_ν / ρ` against a continuous `g`. -/
lemma p2l_lameEsk_sin_integral (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ)
    (weighted : Bool) {g : ℝ → ℝ} (hg : Continuous g) :
    HasSum (fun j : ℕ => ((1 - (-1) ^ (m + 1) * (-1) ^ j) / 2 *
        Real.lameSinCoeff (fun x => Real.lameEsk ν m x k) k weighted j) *
        ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.sin (j * Real.lamePhi t k) * g t)
      (∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
        Real.lameEsk ν m t k / (if weighted then 1 else Real.jacobiDnm t (k ^ 2)) * g t) := by
  have hk := l29_sq_lt_one hk0 hk1
  have hpar := Real.lameEsk_parity hν hk0 hk1 m
  exact p2l_hasSum_integral_mul (p2l_lame_summable_sin hk0 hk1
    (p2l_contDiff_lame hk (Real.lameEsk_isLameEigenfunction hν hk0 hk1 m).1)
    (fun x => (hpar x).2.2.2.2) (fun x => (hpar x).2.1) (fun x => (hpar x).1) weighted)
    (p2l_continuous_sin_phi hk) (fun _ _ => Real.abs_sin_le_one _) hg
    (fun t => p2l_lameEsk_sin hν hk0 hk1 m weighted t) _ _

/-- `∫₀^K cos(jφ) w dn = (π/4) A_j`. -/
lemma p2l_integral_cos_true (w : ℝ → ℝ) (j : ℕ) :
    ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.cos (j * Real.lamePhi t k) *
      (w t * Real.jacobiDnm t (k ^ 2)) = π / 4 * Real.lameCosCoeff w k true j := by
  rw [Real.lameCosCoeff, ← mul_assoc, show π / 4 * (4 / π) = 1 by field_simp, one_mul]
  congr 1; funext t; simp only [↓reduceIte]; ring

/-- `∫₀^K cos(jφ) w = (π/4) C_j`. -/
lemma p2l_integral_cos_false (w : ℝ → ℝ) (j : ℕ) :
    ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.cos (j * Real.lamePhi t k) * w t =
      π / 4 * Real.lameCosCoeff w k false j := by
  rw [Real.lameCosCoeff, ← mul_assoc, show π / 4 * (4 / π) = 1 by field_simp, one_mul]
  congr 1; funext t; simp only [Bool.false_eq_true, ↓reduceIte]; ring

/-- `∫₀^K sin(jφ) w dn = (π/4) B_j`. -/
lemma p2l_integral_sin_true (w : ℝ → ℝ) (j : ℕ) :
    ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.sin (j * Real.lamePhi t k) *
      (w t * Real.jacobiDnm t (k ^ 2)) = π / 4 * Real.lameSinCoeff w k true j := by
  rw [Real.lameSinCoeff, ← mul_assoc, show π / 4 * (4 / π) = 1 by field_simp, one_mul]
  congr 1; funext t; simp only [↓reduceIte]; ring

/-- `∫₀^K sin(jφ) w = (π/4) D_j`. -/
lemma p2l_integral_sin_false (w : ℝ → ℝ) (j : ℕ) :
    ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.sin (j * Real.lamePhi t k) * w t =
      π / 4 * Real.lameSinCoeff w k false j := by
  rw [Real.lameSinCoeff, ← mul_assoc, show π / 4 * (4 / π) = 1 by field_simp, one_mul]
  congr 1; funext t; simp only [Bool.false_eq_true, ↓reduceIte]; ring

lemma p2l_continuous_lameEck (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    Continuous fun x => Real.lameEck ν m x k :=
  (Real.lameEck_isLameEigenfunction hν hk0 hk1 m).1.differentiable.continuous

lemma p2l_continuous_lameEsk (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    Continuous fun x => Real.lameEsk ν m x k :=
  (Real.lameEsk_isLameEigenfunction hν hk0 hk1 m).1.differentiable.continuous

lemma p2l_continuous_dn (hk : k ^ 2 < 1) : Continuous fun x => Real.jacobiDnm x (k ^ 2) :=
  continuous_iff_continuousAt.2 fun x => (Real.hasDerivAt_jacobiDnm hk x).continuousAt

/-- The sequence identity behind the normalizations 29.6.12, 29.6.27, 29.6.42, 29.6.57. -/
lemma p2l_norm_seq {C : ℕ → ℝ} (hC : Summable fun p => |C p|) (k e a : ℝ)
    (h : HasSum (fun p => (if p = 0 then e else 1) * C p *
      ((1 - k ^ 2 / 2) * C p - k ^ 2 / 4 * (C (p + 1) + if p = 0 then a else C (p - 1)))) 1) :
    ∃ S T : ℝ, HasSum (fun p => (if p = 0 then e else 1) * C p ^ 2) S ∧
      HasSum (fun p => C p * C (p + 1)) T ∧
      (1 - k ^ 2 / 2) * S - k ^ 2 / 4 * (2 * T + e * C 0 * a - (1 - e) * C 0 * C 1) = 1 := by
  have hC' : Summable C := hC.of_abs
  obtain ⟨M, hM⟩ : ∃ M, ∀ p, |C p| ≤ M := ⟨_, fun p => hC.le_tsum p (fun _ _ => abs_nonneg _)⟩
  have hprod : ∀ g : ℕ → ℕ, Summable fun p => C p * C (g p) := fun g =>
    Summable.of_norm_bounded (hC.mul_right M) fun p => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
  have hsq : Summable fun p => (if p = 0 then e else 1) * C p ^ 2 := by
    refine (summable_nat_add_iff 1).1 ?_
    simpa [sq] using (summable_nat_add_iff 1).2 (hprod id)
  obtain ⟨T, hT⟩ := hprod (· + 1)
  refine ⟨_, T, hsq.hasSum, hT, ?_⟩
  have h1 : HasSum (fun p => (if p = 0 then e else 1) * C p * C (p + 1))
      (T - (1 - e) * C 0 * C 1) := by
    convert hT.sub (hasSum_ite_eq 0 ((1 - e) * C 0 * C 1)) using 1
    funext p; split_ifs with hp <;> simp [hp]; ring
  have h2 : HasSum (fun p => (if p = 0 then e else 1) * C p *
      (if p = 0 then a else C (p - 1))) (T + e * C 0 * a) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, ite_true, add_sub_cancel_right,
      Nat.add_one_ne_zero, ite_false, one_mul, add_tsub_cancel_right]
    convert hT using 1; funext p; ring
  have h3 := ((hsq.hasSum.mul_left (1 - k ^ 2 / 2)).sub
    ((h1.add h2).mul_left (k ^ 2 / 4)))
  have := h.unique (by convert h3 using 1; funext p; ring)
  linear_combination -this

/-- `cos(|j - 2| φ) = cos((j - 2) φ)`. -/
lemma p2l_cos_natAbs (j : ℕ) (φ : ℝ) :
    Real.cos (((Int.natAbs ((j : ℤ) - 2) : ℕ) : ℝ) * φ) = Real.cos (((j : ℝ) - 2) * φ) := by
  rw [Nat.cast_natAbs, Int.cast_abs]; push_cast
  rcases abs_choice ((j : ℝ) - 2) with h | h <;> rw [h]
  rw [neg_mul, Real.cos_neg]

/-- `sin(|j - 2| φ) = ± sin((j - 2) φ)`. -/
lemma p2l_sin_natAbs (j : ℕ) (φ : ℝ) :
    (if j < 2 then -1 else 1) * Real.sin (((Int.natAbs ((j : ℤ) - 2) : ℕ) : ℝ) * φ) =
      Real.sin (((j : ℝ) - 2) * φ) := by
  rw [Nat.cast_natAbs, Int.cast_abs]; push_cast
  split_ifs with hj
  · rw [abs_of_neg (by linarith [show (j : ℝ) < 2 by exact_mod_cast hj])]
    simp only [neg_mul, Real.sin_neg, one_mul, neg_neg]
  · rw [abs_of_nonneg (by linarith [show (2 : ℝ) ≤ j by exact_mod_cast not_lt.1 hj]),
      one_mul]

/-- `∫₀^K cos(jφ) w dn² = (π/4)((1 - k²/2) C_j - (k²/4)(C_{j+2} + C_{|j-2|}))`. -/
lemma p2l_integral_cos_dn_sq (hk : k ^ 2 < 1) {w : ℝ → ℝ} (hw : Continuous w) (j : ℕ) :
    ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.cos (j * Real.lamePhi t k) *
      (w t * Real.jacobiDnm t (k ^ 2) ^ 2) =
      π / 4 * ((1 - k ^ 2 / 2) * Real.lameCosCoeff w k false j - k ^ 2 / 4 *
        (Real.lameCosCoeff w k false (j + 2) +
          Real.lameCosCoeff w k false (Int.natAbs ((j : ℤ) - 2)))) := by
  have hi : ∀ i : ℕ, IntervalIntegrable (fun t => Real.cos (i * Real.lamePhi t k) * w t)
      MeasureTheory.volume 0 (Real.compEllIntKm (k ^ 2)) := fun i =>
    ((p2l_continuous_cos_phi hk i).mul hw).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (g := fun t => (1 - k ^ 2 / 2) *
      (Real.cos (j * Real.lamePhi t k) * w t) - k ^ 2 / 4 *
      (Real.cos ((↑(j + 2) : ℝ) * Real.lamePhi t k) * w t + (Real.cos
        ((↑(Int.natAbs ((j : ℤ) - 2)) : ℝ) * Real.lamePhi t k) * w t))) fun t _ => ?_]
  · rw [intervalIntegral.integral_sub ((hi _).const_mul _)
      (((hi _).add ((hi _))).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hi _) (hi _),
      p2l_integral_cos_false, p2l_integral_cos_false, p2l_integral_cos_false]
    ring
  simp only
  have hd := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hk t
  rw [p2l_cos_natAbs, ← p2l_lamePhi_cos] at *
  have e1 : Real.cos (((j + 2 : ℕ) : ℝ) * Real.lamePhi t k) = Real.cos (j * Real.lamePhi t k) *
      Real.cos (2 * Real.lamePhi t k) - Real.sin (j * Real.lamePhi t k) *
        Real.sin (2 * Real.lamePhi t k) := by rw [← Real.cos_add]; push_cast; ring_nf
  have e2 : Real.cos (((j : ℝ) - 2) * Real.lamePhi t k) = Real.cos (j * Real.lamePhi t k) *
      Real.cos (2 * Real.lamePhi t k) + Real.sin (j * Real.lamePhi t k) *
        Real.sin (2 * Real.lamePhi t k) := by rw [← Real.cos_sub]; ring_nf
  rw [e1, e2, Real.cos_two_mul]
  linear_combination (Real.cos (j * Real.lamePhi t k) * w t) * hd

/-- `∫₀^K sin(jφ) w dn² = (π/4)((1 - k²/2) D_j - (k²/4)(D_{j+2} ± D_{|j-2|}))`. -/
lemma p2l_integral_sin_dn_sq (hk : k ^ 2 < 1) {w : ℝ → ℝ} (hw : Continuous w) (j : ℕ) :
    ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.sin (j * Real.lamePhi t k) *
      (w t * Real.jacobiDnm t (k ^ 2) ^ 2) =
      π / 4 * ((1 - k ^ 2 / 2) * Real.lameSinCoeff w k false j - k ^ 2 / 4 *
        (Real.lameSinCoeff w k false (j + 2) + (if j < 2 then -1 else 1) *
          Real.lameSinCoeff w k false (Int.natAbs ((j : ℤ) - 2)))) := by
  have hi : ∀ i : ℕ, IntervalIntegrable (fun t => Real.sin (i * Real.lamePhi t k) * w t)
      MeasureTheory.volume 0 (Real.compEllIntKm (k ^ 2)) := fun i =>
    ((p2l_continuous_sin_phi hk i).mul hw).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (g := fun t => (1 - k ^ 2 / 2) *
      (Real.sin (j * Real.lamePhi t k) * w t) - k ^ 2 / 4 *
      (Real.sin ((↑(j + 2) : ℝ) * Real.lamePhi t k) * w t + (if j < 2 then -1 else 1) * (Real.sin
        ((↑(Int.natAbs ((j : ℤ) - 2)) : ℝ) * Real.lamePhi t k) * w t))) fun t _ => ?_]
  · rw [intervalIntegral.integral_sub ((hi _).const_mul _)
      (((hi _).add (((hi _).const_mul _))).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hi _) ((hi _).const_mul _),
      intervalIntegral.integral_const_mul, p2l_integral_sin_false, p2l_integral_sin_false,
      p2l_integral_sin_false]
    ring
  simp only
  have hd := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hk t
  have hs := p2l_sin_natAbs j (Real.lamePhi t k)
  rw [← p2l_lamePhi_cos] at hd
  have e1 : Real.sin (((j + 2 : ℕ) : ℝ) * Real.lamePhi t k) = Real.sin (j * Real.lamePhi t k) *
      Real.cos (2 * Real.lamePhi t k) + Real.cos (j * Real.lamePhi t k) *
        Real.sin (2 * Real.lamePhi t k) := by rw [← Real.sin_add]; push_cast; ring_nf
  have e2 : Real.sin (((j : ℝ) - 2) * Real.lamePhi t k) = Real.sin (j * Real.lamePhi t k) *
      Real.cos (2 * Real.lamePhi t k) - Real.cos (j * Real.lamePhi t k) *
        Real.sin (2 * Real.lamePhi t k) := by rw [← Real.sin_sub]; ring_nf
  rw [e2] at hs; rw [e1]; rw [Real.cos_two_mul] at hs ⊢
  linear_combination (Real.sin (j * Real.lamePhi t k) * w t) * hd + k ^ 2 / 4 * w t * hs

/-! ### Fourier recurrences from Green's identity (helpers) -/

/-- Green's identity for a solution of 29.2.1 against a `C²` test function `F`. -/
lemma p1l_green {h : ℝ} {w F F1 F2 : ℝ → ℝ} (hk : k ^ 2 < 1) (hw : Real.IsLameSolution h ν k w)
    (hF : ∀ x, HasDerivAt F (F1 x) x) (hF1 : ∀ x, HasDerivAt F1 (F2 x) x)
    (hF2 : Continuous F2) (a b : ℝ) :
    ∫ x in a..b, w x * (F2 x + (h - ν * (ν + 1) * k ^ 2 * Real.jacobiSnm x (k ^ 2) ^ 2) * F x) =
      (w b * F1 b - deriv w b * F b) - (w a * F1 a - deriv w a * F a) := by
  have hd : ∀ x, HasDerivAt (fun y => w y * F1 y - deriv w y * F y)
      (w x * (F2 x + (h - ν * (ν + 1) * k ^ 2 * Real.jacobiSnm x (k ^ 2) ^ 2) * F x)) x := by
    intro x
    have := (((hw.differentiable x).hasDerivAt).mul (hF1 x)).sub
      ((hw.hasDerivAt_deriv x).mul (hF x))
    convert this using 1; ring
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => (hF x).continuousAt
  have hcont : Continuous fun x =>
      w x * (F2 x + (h - ν * (ν + 1) * k ^ 2 * Real.jacobiSnm x (k ^ 2) ^ 2) * F x) :=
    hw.differentiable.continuous.mul (hF2.add ((continuous_const.sub
      (continuous_const.mul ((l29_continuous_sn hk).pow 2))).mul hFc))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hcont.intervalIntegrable a b)

lemma p1l_cos_phi (x : ℝ) : Real.cos (Real.lamePhi x k) = Real.jacobiSnm x (k ^ 2) := by
  simp [Real.lamePhi, Real.cos_pi_div_two_sub, Real.jacobiSnm]

lemma p1l_sin_phi (x : ℝ) : Real.sin (Real.lamePhi x k) = Real.jacobiCnm x (k ^ 2) := by
  simp [Real.lamePhi, Real.sin_pi_div_two_sub, Real.jacobiCnm]

lemma p1l_continuous_dn (hk : k ^ 2 < 1) : Continuous fun x => Real.jacobiDnm x (k ^ 2) :=
  continuous_iff_continuousAt.2 fun x => (Real.hasDerivAt_jacobiDnm hk x).continuousAt

lemma p1l_continuous_cn (hk : k ^ 2 < 1) : Continuous fun x => Real.jacobiCnm x (k ^ 2) :=
  continuous_iff_continuousAt.2 fun x => (Real.hasDerivAt_jacobiCnm hk x).continuousAt

lemma p1l_continuous_phi (hk : k ^ 2 < 1) : Continuous fun x => Real.lamePhi x k :=
  continuous_iff_continuousAt.2 fun x => (p1l_hasDerivAt_phi hk x).continuousAt

lemma p1l_phi_zero (hk : k ^ 2 < 1) : Real.lamePhi 0 k = π / 2 := by
  simp [Real.lamePhi, Real.jacobiAmm_zero hk]

lemma p1l_phi_K (hk : k ^ 2 < 1) : Real.lamePhi (Real.compEllIntKm (k ^ 2)) k = 0 := by
  rw [Real.lamePhi, Real.jacobiAmm_compEllIntKm hk, sub_self]

lemma p1l_sn_zero (hk : k ^ 2 < 1) : Real.jacobiSnm 0 (k ^ 2) = 0 := by
  simp [Real.jacobiSnm, Real.jacobiAmm_zero hk]

lemma p1l_cn_K (hk : k ^ 2 < 1) : Real.jacobiCnm (Real.compEllIntKm (k ^ 2)) (k ^ 2) = 0 := by
  simp [Real.jacobiCnm, Real.jacobiAmm_compEllIntKm hk]

/-- The integral identity behind the Fourier recurrences of §29.6, for a real index `j` and a
trigonometric kernel `g` (`cos` or `sin`, with `g' = g₁`, `g₁' = -g`); unweighted case. -/
lemma p1l_int_unw {h j : ℝ} {w g g1 : ℝ → ℝ} (hk : k ^ 2 < 1)
    (hw : Real.IsLameSolution h ν k w)
    (hg : ∀ t, HasDerivAt g (g1 t) t) (hg1 : ∀ t, HasDerivAt g1 (-g t) t)
    (hadd : ∀ a b, g (a + b) = g a * Real.cos b + g1 a * Real.sin b)
    (h0 : w 0 * g1 (j * (π / 2)) = 0) (h0' : deriv w 0 * g (j * (π / 2)) = 0)
    (hK : w (Real.compEllIntKm (k ^ 2)) * g1 0 = 0)
    (hK' : deriv w (Real.compEllIntKm (k ^ 2)) * g 0 = 0) :
    (j ^ 2 * (2 - k ^ 2) - (2 * h - ν * (ν + 1) * k ^ 2)) *
        (∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), w x * g (j * Real.lamePhi x k)) +
      k ^ 2 / 2 * (ν - j) * (ν + j + 1) *
        (∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), w x * g ((j + 2) * Real.lamePhi x k)) +
      k ^ 2 / 2 * (ν - j + 1) * (ν + j) *
        (∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), w x * g ((j - 2) * Real.lamePhi x k)) =
      0 := by
  set K := Real.compEllIntKm (k ^ 2)
  set S := fun x => Real.jacobiSnm x (k ^ 2)
  set Cn := fun x => Real.jacobiCnm x (k ^ 2)
  set D := fun x => Real.jacobiDnm x (k ^ 2)
  set φ := fun x => Real.lamePhi x k
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  have hg1c : Continuous g1 := continuous_iff_continuousAt.2 fun t => (hg1 t).continuousAt
  have hφ := p1l_hasDerivAt_phi hk
  have hF : ∀ x, HasDerivAt (fun x => g (j * φ x)) (-(j * D x * g1 (j * φ x))) x := fun x =>
    ((hg _).comp x ((hφ x).const_mul j)).congr_deriv (by simp only [D]; ring)
  have hF1 : ∀ x, HasDerivAt (fun x => -(j * D x * g1 (j * φ x)))
      (j * k ^ 2 * S x * Cn x * g1 (j * φ x) - j ^ 2 * D x ^ 2 * g (j * φ x)) x := by
    intro x
    have h1 := (((Real.hasDerivAt_jacobiDnm hk x).mul
      ((hg1 _).comp x ((hφ x).const_mul j))).const_mul j).neg
    convert h1 using 1
    · funext y; simp only [Pi.neg_apply, Pi.mul_apply, Function.comp_apply, D, φ]; ring
    · simp only [D, S, Cn, φ, Function.comp_apply]; ring
  have hS : Continuous S := l29_continuous_sn hk
  have hC : Continuous Cn := p1l_continuous_cn hk
  have hD : Continuous D := p1l_continuous_dn hk
  have hP : Continuous φ := p1l_continuous_phi hk
  have hF2 : Continuous fun x =>
      j * k ^ 2 * S x * Cn x * g1 (j * φ x) - j ^ 2 * D x ^ 2 * g (j * φ x) := by
    fun_prop
  have hG := p1l_green hk hw hF hF1 hF2 0 K
  have hφ0 : φ 0 = π / 2 := p1l_phi_zero hk
  have hφK : φ K = 0 := p1l_phi_K hk
  simp only [hφ0, hφK, mul_zero] at hG
  have hpt : ∀ x, w x * ((j * k ^ 2 * S x * Cn x * g1 (j * φ x) - j ^ 2 * D x ^ 2 * g (j * φ x)) +
      (h - ν * (ν + 1) * k ^ 2 * Real.jacobiSnm x (k ^ 2) ^ 2) * g (j * φ x)) =
      -(1 / 2) * ((j ^ 2 * (2 - k ^ 2) - (2 * h - ν * (ν + 1) * k ^ 2)) * (w x * g (j * φ x)) +
        k ^ 2 / 2 * (ν - j) * (ν + j + 1) * (w x * g ((j + 2) * φ x)) +
        k ^ 2 / 2 * (ν - j + 1) * (ν + j) * (w x * g ((j - 2) * φ x))) := by
    intro x
    have hD2 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hk x
    have hc := p1l_cos_phi (k := k) x
    have hs := p1l_sin_phi (k := k) x
    rw [show (j + 2) * φ x = j * φ x + 2 * φ x by ring,
      show (j - 2) * φ x = j * φ x + -(2 * φ x) by ring, hadd, hadd, Real.cos_neg, Real.sin_neg,
      Real.cos_two_mul, Real.sin_two_mul]
    simp only [S, Cn, D, φ] at *
    rw [hc, hs]
    linear_combination (-j ^ 2 * w x * g (j * Real.lamePhi x k)) * hD2
  have hwc : Continuous w := hw.differentiable.continuous
  rw [intervalIntegral.integral_congr (fun x _ => hpt x), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hG
  simp only [φ] at hG
  linear_combination (-2) * hG + 2 * (j * D K) * hK + 2 * hK' - 2 * (j * D 0) * h0 - 2 * h0'

/-- The weighted analogue of `p1l_int_unw` (test function `dn(x) g(jφ(x))`). -/
lemma p1l_int_w {h j : ℝ} {w g g1 : ℝ → ℝ} (hk : k ^ 2 < 1)
    (hw : Real.IsLameSolution h ν k w)
    (hg : ∀ t, HasDerivAt g (g1 t) t) (hg1 : ∀ t, HasDerivAt g1 (-g t) t)
    (hadd : ∀ a b, g (a + b) = g a * Real.cos b + g1 a * Real.sin b)
    (h0 : w 0 * g1 (j * (π / 2)) = 0) (h0' : deriv w 0 * g (j * (π / 2)) = 0)
    (hK : w (Real.compEllIntKm (k ^ 2)) * g1 0 = 0)
    (hK' : deriv w (Real.compEllIntKm (k ^ 2)) * g 0 = 0) :
    (j ^ 2 * (2 - k ^ 2) - (2 * h - ν * (ν + 1) * k ^ 2)) *
        (∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
          w x * g (j * Real.lamePhi x k) * Real.jacobiDnm x (k ^ 2)) +
      k ^ 2 / 2 * (ν - j - 1) * (ν + j + 2) *
        (∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
          w x * g ((j + 2) * Real.lamePhi x k) * Real.jacobiDnm x (k ^ 2)) +
      k ^ 2 / 2 * (ν - j + 2) * (ν + j - 1) *
        (∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
          w x * g ((j - 2) * Real.lamePhi x k) * Real.jacobiDnm x (k ^ 2)) =
      0 := by
  set K := Real.compEllIntKm (k ^ 2)
  set S := fun x => Real.jacobiSnm x (k ^ 2)
  set Cn := fun x => Real.jacobiCnm x (k ^ 2)
  set D := fun x => Real.jacobiDnm x (k ^ 2)
  set φ := fun x => Real.lamePhi x k
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  have hg1c : Continuous g1 := continuous_iff_continuousAt.2 fun t => (hg1 t).continuousAt
  have hφ := p1l_hasDerivAt_phi hk
  have hG0 : ∀ x, HasDerivAt (fun x => g (j * φ x)) (-(j * D x * g1 (j * φ x))) x := fun x =>
    ((hg _).comp x ((hφ x).const_mul j)).congr_deriv (by simp only [D]; ring)
  have hG1 : ∀ x, HasDerivAt (fun x => g1 (j * φ x)) (j * D x * g (j * φ x)) x := fun x =>
    ((hg1 _).comp x ((hφ x).const_mul j)).congr_deriv (by simp only [D]; ring)
  have hF : ∀ x, HasDerivAt (fun x => D x * g (j * φ x))
      (-(k ^ 2 * S x * Cn x) * g (j * φ x) - j * D x ^ 2 * g1 (j * φ x)) x := by
    intro x
    have h1 := (Real.hasDerivAt_jacobiDnm hk x).mul (hG0 x)
    convert h1 using 1
    simp only [D, S, Cn]; ring
  have hF1 : ∀ x, HasDerivAt
      (fun x => -(k ^ 2 * S x * Cn x) * g (j * φ x) - j * D x ^ 2 * g1 (j * φ x))
      (-(k ^ 2) * D x * (Cn x ^ 2 - S x ^ 2) * g (j * φ x) +
        3 * j * k ^ 2 * D x * S x * Cn x * g1 (j * φ x) - j ^ 2 * D x ^ 3 * g (j * φ x)) x := by
    intro x
    have h1 := (((((Real.hasDerivAt_jacobiSnm hk x).const_mul (k ^ 2)).mul
      (Real.hasDerivAt_jacobiCnm hk x)).neg).mul (hG0 x)).sub
      ((((Real.hasDerivAt_jacobiDnm hk x).pow 2).const_mul j).mul (hG1 x))
    convert h1 using 1
    simp only [D, S, Cn, Pi.mul_apply, Pi.neg_apply, Pi.pow_apply]; ring
  have hS : Continuous S := l29_continuous_sn hk
  have hC : Continuous Cn := p1l_continuous_cn hk
  have hD : Continuous D := p1l_continuous_dn hk
  have hP : Continuous φ := p1l_continuous_phi hk
  have hF2 : Continuous fun x => -(k ^ 2) * D x * (Cn x ^ 2 - S x ^ 2) * g (j * φ x) +
        3 * j * k ^ 2 * D x * S x * Cn x * g1 (j * φ x) - j ^ 2 * D x ^ 3 * g (j * φ x) := by
    fun_prop
  have hG := p1l_green hk hw hF hF1 hF2 0 K
  have hφ0 : φ 0 = π / 2 := p1l_phi_zero hk
  have hφK : φ K = 0 := p1l_phi_K hk
  have hS0 : S 0 = 0 := p1l_sn_zero hk
  have hCK : Cn K = 0 := p1l_cn_K hk
  simp only [hφ0, hφK, mul_zero, hS0, hCK, zero_mul, mul_zero, neg_zero, zero_sub] at hG
  have hpt : ∀ x, w x * ((-(k ^ 2) * D x * (Cn x ^ 2 - S x ^ 2) * g (j * φ x) +
        3 * j * k ^ 2 * D x * S x * Cn x * g1 (j * φ x) - j ^ 2 * D x ^ 3 * g (j * φ x)) +
      (h - ν * (ν + 1) * k ^ 2 * Real.jacobiSnm x (k ^ 2) ^ 2) * (D x * g (j * φ x))) =
      -(1 / 2) * ((j ^ 2 * (2 - k ^ 2) - (2 * h - ν * (ν + 1) * k ^ 2)) *
          (w x * g (j * φ x) * D x) +
        k ^ 2 / 2 * (ν - j - 1) * (ν + j + 2) * (w x * g ((j + 2) * φ x) * D x) +
        k ^ 2 / 2 * (ν - j + 2) * (ν + j - 1) * (w x * g ((j - 2) * φ x) * D x)) := by
    intro x
    have hD2 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hk x
    have hSC := Real.jacobiSnm_sq_add_jacobiCnm_sq x (k ^ 2)
    have hc := p1l_cos_phi (k := k) x
    have hs := p1l_sin_phi (k := k) x
    rw [show (j + 2) * φ x = j * φ x + 2 * φ x by ring,
      show (j - 2) * φ x = j * φ x + -(2 * φ x) by ring, hadd, hadd, Real.cos_neg, Real.sin_neg,
      Real.cos_two_mul, Real.sin_two_mul]
    simp only [S, Cn, D, φ] at *
    rw [hc, hs]
    linear_combination (-j ^ 2 * Real.jacobiDnm x (k ^ 2) * w x * g (j * Real.lamePhi x k)) * hD2 +
      (-k ^ 2 * Real.jacobiDnm x (k ^ 2) * w x * g (j * Real.lamePhi x k)) * hSC
  have hwc : Continuous w := hw.differentiable.continuous
  rw [intervalIntegral.integral_congr (fun x _ => hpt x), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hG
  simp only [φ, D] at hG
  linear_combination (-2) * hG + 2 * j * Real.jacobiDnm K (k ^ 2) ^ 2 * hK -
    2 * j * Real.jacobiDnm 0 (k ^ 2) ^ 2 * h0 + 2 * Real.jacobiDnm K (k ^ 2) * hK' -
    2 * Real.jacobiDnm 0 (k ^ 2) * h0'

/-- The integral identity of `p1l_int_unw`/`p1l_int_w` for the cosine kernel, as an identity
between the (real-index) Fourier coefficients `(4/π)∫₀^K w cos(jφ) ρ dx`. -/
lemma p1l_cos_rec {h j : ℝ} {w : ℝ → ℝ} (hk : k ^ 2 < 1) (hw : Real.IsLameSolution h ν k w)
    (b : Bool) (h0 : w 0 * Real.sin (j * (π / 2)) = 0)
    (h0' : deriv w 0 * Real.cos (j * (π / 2)) = 0)
    (hK' : deriv w (Real.compEllIntKm (k ^ 2)) = 0) :
    (j ^ 2 * (2 - k ^ 2) - (2 * h - ν * (ν + 1) * k ^ 2)) *
        (4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), w x * Real.cos (j * Real.lamePhi x k) *
          (if b then Real.jacobiDnm x (k ^ 2) else 1)) +
      (if b then k ^ 2 / 2 * (ν - j - 1) * (ν + j + 2) else k ^ 2 / 2 * (ν - j) * (ν + j + 1)) *
        (4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
          w x * Real.cos ((j + 2) * Real.lamePhi x k) *
            (if b then Real.jacobiDnm x (k ^ 2) else 1)) +
      (if b then k ^ 2 / 2 * (ν - j + 2) * (ν + j - 1) else k ^ 2 / 2 * (ν - j + 1) * (ν + j)) *
        (4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
          w x * Real.cos ((j - 2) * Real.lamePhi x k) *
            (if b then Real.jacobiDnm x (k ^ 2) else 1)) = 0 := by
  have hg : ∀ t, HasDerivAt Real.cos (-Real.sin t) t := Real.hasDerivAt_cos
  have hg1 : ∀ t, HasDerivAt (fun t => -Real.sin t) (-Real.cos t) t :=
    fun t => (Real.hasDerivAt_sin t).neg
  have hadd : ∀ a b, Real.cos (a + b) = Real.cos a * Real.cos b + -Real.sin a * Real.sin b :=
    fun a b => by rw [Real.cos_add]; ring
  have h0n : w 0 * -Real.sin (j * (π / 2)) = 0 := by rw [mul_neg, h0, neg_zero]
  have hKn : w (Real.compEllIntKm (k ^ 2)) * -Real.sin 0 = 0 := by simp
  have hK'' : deriv w (Real.compEllIntKm (k ^ 2)) * Real.cos 0 = 0 := by simp [hK']
  cases b
  · have := p1l_int_unw hk hw hg hg1 hadd h0n h0' hKn hK''
    simp only [Bool.false_eq_true, ite_false, mul_one]
    linear_combination (4 / π) * this
  · have := p1l_int_w hk hw hg hg1 hadd h0n h0' hKn hK''
    simp only [ite_true]
    linear_combination (4 / π) * this

/-- The sine-kernel analogue of `p1l_cos_rec`. -/
lemma p1l_sin_rec {h j : ℝ} {w : ℝ → ℝ} (hk : k ^ 2 < 1) (hw : Real.IsLameSolution h ν k w)
    (b : Bool) (h0 : w 0 * Real.cos (j * (π / 2)) = 0)
    (h0' : deriv w 0 * Real.sin (j * (π / 2)) = 0)
    (hK : w (Real.compEllIntKm (k ^ 2)) = 0) :
    (j ^ 2 * (2 - k ^ 2) - (2 * h - ν * (ν + 1) * k ^ 2)) *
        (4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), w x * Real.sin (j * Real.lamePhi x k) *
          (if b then Real.jacobiDnm x (k ^ 2) else 1)) +
      (if b then k ^ 2 / 2 * (ν - j - 1) * (ν + j + 2) else k ^ 2 / 2 * (ν - j) * (ν + j + 1)) *
        (4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
          w x * Real.sin ((j + 2) * Real.lamePhi x k) *
            (if b then Real.jacobiDnm x (k ^ 2) else 1)) +
      (if b then k ^ 2 / 2 * (ν - j + 2) * (ν + j - 1) else k ^ 2 / 2 * (ν - j + 1) * (ν + j)) *
        (4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
          w x * Real.sin ((j - 2) * Real.lamePhi x k) *
            (if b then Real.jacobiDnm x (k ^ 2) else 1)) = 0 := by
  have hg : ∀ t, HasDerivAt Real.sin (Real.cos t) t := Real.hasDerivAt_sin
  have hg1 : ∀ t, HasDerivAt Real.cos (-Real.sin t) t := Real.hasDerivAt_cos
  have hadd : ∀ a b, Real.sin (a + b) = Real.sin a * Real.cos b + Real.cos a * Real.sin b :=
    fun a b => Real.sin_add a b
  have hKn : w (Real.compEllIntKm (k ^ 2)) * Real.cos 0 = 0 := by simp [hK]
  have hK'' : deriv w (Real.compEllIntKm (k ^ 2)) * Real.sin 0 = 0 := by simp
  cases b
  · have := p1l_int_unw hk hw hg hg1 hadd h0 h0' hKn hK''
    simp only [Bool.false_eq_true, ite_false, mul_one]
    linear_combination (4 / π) * this
  · have := p1l_int_w hk hw hg hg1 hadd h0 h0' hKn hK''
    simp only [ite_true]
    linear_combination (4 / π) * this

/-- DLMF 29.6.1: `Ec^{2m}_ν(x, k²) = ½A₀ + ∑_{p≥1} A_{2p} cos(2pφ)` for real `x`, with `φ = π/2 -
am(x, k)` and the Fourier coefficients `A_{2p}` of `Real.lameCosCoeff` (weighted by `dn`). Admitted.
-/
@[dlmf 29.6.E1]
theorem Real.lameEck_even_hasSum_fourierA
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∀ x : ℝ, HasSum (fun p : ℕ => (if p = 0 then 1 / 2 else 1) *
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k true (2 * p) *
      Real.cos (((2 * p : ℕ) : ℝ) * Real.lamePhi x k)) (Real.lameEck ν (2 * m) x k) := by
  intro x
  have hs := p2l_lameEck_cos hν hk0 hk1 (2 * m) true x
  simp only [↓reduceIte, div_one] at hs
  convert p2l_hasSum_two_mul_add 0 (fun j hj => ?_) hs using 1
  · funext p
    simp [pow_mul]
  · have := (p2l_neg_one_pow_mod j).2.2 (by omega)
    simp [pow_mul, this]

/-- DLMF 29.6.2–29.6.3: with `H = 2·(eigenvalue) - ν(ν+1)k²`, `(β₀ - H)A₀ + α₀A₁ = 0` for the
recurrence `A0` (index `p` of the coefficient list). Proved from Lamé's equation
by Green's identity (`p1l_cos_rec`, `p1l_sin_rec`). -/
@[dlmf 29.6.E2, dlmf 29.6.E3]
theorem Real.lameEck_even_fourierA_rec_zero
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k true (2 * p)
    let H : ℝ := 2 * Real.lameAk ν (2 * m) k - ν * (ν + 1) * k ^ 2
    (LameRecurrence.A0.beta ν k 0 - H) * A 0 +
      LameRecurrence.A0.alpha ν k 0 * A 1 = 0 := by
  intro X H
  have hk := l29_sq_lt_one hk0 hk1
  obtain ⟨hw, hb, -⟩ := Real.lameEck_isLameEigenfunction hν hk0 hk1 (2 * m)
  simp [Real.LameBoundary] at hb
  have key := p1l_cos_rec hk hw true (j := 0) (by simp)
    (by simp [hb.1]) hb.2
  simp only [X, H, Real.lameCosCoeff, LameRecurrence.alpha, LameRecurrence.beta, ite_true]
  norm_num [Real.cos_neg, Real.sin_neg] at key ⊢
  linear_combination key

/-- DLMF 29.6.4: `γ_p A_{p-1} + (β_p - H)A_p + α_p A_{p+1} = 0`, `p ≥ 1` (indices of the coefficient
list), for the recurrence `A0`. Proved from Lamé's equation
by Green's identity (`p1l_cos_rec`, `p1l_sin_rec`). -/
@[dlmf 29.6.E4]
theorem Real.lameEck_even_fourierA_rec
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k true (2 * p)
    let H : ℝ := 2 * Real.lameAk ν (2 * m) k - ν * (ν + 1) * k ^ 2
    ∀ p : ℕ, 1 ≤ p → LameRecurrence.A0.gamma ν k p * A (p - 1) +
      (LameRecurrence.A0.beta ν k p - H) * A p +
      LameRecurrence.A0.alpha ν k p * A (p + 1) = 0 := by
  intro X H p hp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hk := l29_sq_lt_one hk0 hk1
  obtain ⟨hw, hb, -⟩ := Real.lameEck_isLameEigenfunction hν hk0 hk1 (2 * m)
  simp [Real.LameBoundary] at hb
  have key := p1l_cos_rec hk hw true (j := ((2 * (q + 1) : ℕ) : ℝ))
    (by rw [show ((2 * (q + 1) : ℕ) : ℝ) * (π / 2) = ((q + 1 : ℕ) : ℝ) * π by push_cast; ring,
      Real.sin_nat_mul_pi, mul_zero])
    (by simp [hb.1]) hb.2
  rw [show ((2 * (q + 1) : ℕ) : ℝ) + 2 = ((2 * (q + 1 + 1) : ℕ) : ℝ) by push_cast; ring,
    show ((2 * (q + 1) : ℕ) : ℝ) - 2 = ((2 * (q) : ℕ) : ℝ) by push_cast; ring] at key
  simp only [X, H, Real.lameCosCoeff, LameRecurrence.alpha, LameRecurrence.beta,
    LameRecurrence.gamma, Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false, ite_true]
  simp only [↓reduceIte] at key ⊢
  push_cast at key ⊢
  linear_combination key

/-- DLMF 29.6.5: the normalization of the coefficients `A_{2p}`. Admitted. -/
@[dlmf 29.6.E5]
theorem Real.lameEck_even_fourierA_normalization
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let A : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k true (2 * p)
    HasSum (fun p => (if p = 0 then 1 / 2 else 1) * A p ^ 2) 1 := by
  intro A
  have hk := l29_sq_lt_one hk0 hk1
  have h := p2l_lameEck_cos_integral hν hk0 hk1 (2 * m) true
    (g := fun x => Real.lameEck ν (2 * m) x k * Real.jacobiDnm x (k ^ 2))
    ((p2l_continuous_lameEck hν hk0 hk1 _).mul (p2l_continuous_dn hk))
  simp only [↓reduceIte, div_one, p2l_integral_cos_true] at h
  rw [show (∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.lameEck ν (2 * m) t k *
      (Real.lameEck ν (2 * m) t k * Real.jacobiDnm t (k ^ 2))) =
      ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm t (k ^ 2) *
        Real.lameEck ν (2 * m) t k ^ 2 by congr 1; funext t; ring,
    Real.lameEck_normalization hν hk0 hk1] at h
  have h2 := h.mul_left (4 / π)
  rw [show 4 / π * (π / 4) = 1 by field_simp] at h2
  convert p2l_hasSum_two_mul_add 0 (fun j hj => ?_) h2 using 1
  · funext p
    simp only [A, add_zero, pow_mul]; norm_num
    split_ifs <;> field_simp
  · have := (p2l_neg_one_pow_mod j).2.2 (by omega)
    simp [pow_mul, this]

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
  intro x
  have hd := (Real.jacobiDnm_pos (l29_sq_lt_one hk0 hk1) x).ne'
  have hs := (p2l_lameEck_cos hν hk0 hk1 (2 * m) false x).mul_left (Real.jacobiDnm x (k ^ 2))
  simp only [Bool.false_eq_true, ↓reduceIte, mul_div_cancel₀ _ hd] at hs
  convert p2l_hasSum_two_mul_add 0 (fun j hj => ?_) hs using 1
  · funext p
    simp [pow_mul]
  · have := (p2l_neg_one_pow_mod j).2.2 (by omega)
    simp [pow_mul, this]

/-- DLMF 29.6.9: `(β₀ - H)C₀ + α₀C₁ = 0` for the recurrence `C0`.
Proved from Lamé's equation by Green's identity (`p1l_cos_rec`, `p1l_sin_rec`). -/
@[dlmf 29.6.E9]
theorem Real.lameEck_even_fourierC_rec_zero
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k false (2 * p)
    let H : ℝ := 2 * Real.lameAk ν (2 * m) k - ν * (ν + 1) * k ^ 2
    (LameRecurrence.C0.beta ν k 0 - H) * C 0 +
      LameRecurrence.C0.alpha ν k 0 * C 1 = 0 := by
  intro X H
  have hk := l29_sq_lt_one hk0 hk1
  obtain ⟨hw, hb, -⟩ := Real.lameEck_isLameEigenfunction hν hk0 hk1 (2 * m)
  simp [Real.LameBoundary] at hb
  have key := p1l_cos_rec hk hw false (j := 0) (by simp)
    (by simp [hb.1]) hb.2
  simp only [X, H, Real.lameCosCoeff, LameRecurrence.alpha, LameRecurrence.beta]
  norm_num [Real.cos_neg, Real.sin_neg] at key ⊢
  linear_combination key

/-- DLMF 29.6.10: `γ_p C_{p-1} + (β_p - H)C_p + α_p C_{p+1} = 0`, `p ≥ 1`, for the recurrence `C0`.
Proved from Lamé's equation by Green's identity (`p1l_cos_rec`, `p1l_sin_rec`). -/
@[dlmf 29.6.E10]
theorem Real.lameEck_even_fourierC_rec
    (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    let C : ℕ → ℝ := fun p =>
      Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k false (2 * p)
    let H : ℝ := 2 * Real.lameAk ν (2 * m) k - ν * (ν + 1) * k ^ 2
    ∀ p : ℕ, 1 ≤ p → LameRecurrence.C0.gamma ν k p * C (p - 1) +
      (LameRecurrence.C0.beta ν k p - H) * C p +
      LameRecurrence.C0.alpha ν k p * C (p + 1) = 0 := by
  intro X H p hp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hk := l29_sq_lt_one hk0 hk1
  obtain ⟨hw, hb, -⟩ := Real.lameEck_isLameEigenfunction hν hk0 hk1 (2 * m)
  simp [Real.LameBoundary] at hb
  have key := p1l_cos_rec hk hw false (j := ((2 * (q + 1) : ℕ) : ℝ))
    (by rw [show ((2 * (q + 1) : ℕ) : ℝ) * (π / 2) = ((q + 1 : ℕ) : ℝ) * π by push_cast; ring,
      Real.sin_nat_mul_pi, mul_zero])
    (by simp [hb.1]) hb.2
  rw [show ((2 * (q + 1) : ℕ) : ℝ) + 2 = ((2 * (q + 1 + 1) : ℕ) : ℝ) by push_cast; ring,
    show ((2 * (q + 1) : ℕ) : ℝ) - 2 = ((2 * (q) : ℕ) : ℝ) by push_cast; ring] at key
  simp only [X, H, Real.lameCosCoeff, LameRecurrence.alpha, LameRecurrence.beta,
    LameRecurrence.gamma, Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false]
  simp only [↓reduceIte, Bool.false_eq_true] at key ⊢
  push_cast at key ⊢
  linear_combination key

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
  intro C
  have hk := l29_sq_lt_one hk0 hk1
  have hE := p2l_continuous_lameEck hν hk0 hk1 (2 * m)
  have h := p2l_lameEck_cos_integral hν hk0 hk1 (2 * m) false
    (g := fun x => Real.lameEck ν (2 * m) x k * Real.jacobiDnm x (k ^ 2) ^ 2)
    (hE.mul ((p2l_continuous_dn hk).pow 2))
  simp only [Bool.false_eq_true, ↓reduceIte, p2l_integral_cos_dn_sq hk hE] at h
  rw [show (∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.lameEck ν (2 * m) t k /
      Real.jacobiDnm t (k ^ 2) * (Real.lameEck ν (2 * m) t k * Real.jacobiDnm t (k ^ 2) ^ 2)) =
      ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm t (k ^ 2) *
        Real.lameEck ν (2 * m) t k ^ 2 by
      congr 1; funext t; field_simp [(Real.jacobiDnm_pos hk t).ne'],
    Real.lameEck_normalization hν hk0 hk1] at h
  have h2 := h.mul_left (4 / π)
  rw [show 4 / π * (π / 4) = 1 by field_simp] at h2
  have hCs : Summable fun p => |C p| := by
    have hs := p2l_lame_summable_cos hk0 hk1
      (p2l_contDiff_lame hk (Real.lameEck_isLameEigenfunction hν hk0 hk1 (2 * m)).1)
      (fun x => (Real.lameEck_parity hν hk0 hk1 _ x).2.2.2.2)
      (fun x => (Real.lameEck_parity hν hk0 hk1 _ x).2.1)
      (fun x => (Real.lameEck_parity hν hk0 hk1 _ x).1) false
    refine ((hs.comp_injective (fun a b hab => by simpa using hab :
      Function.Injective fun p : ℕ => 2 * p)).mul_left 2).of_nonneg_of_le
      (fun _ => abs_nonneg _) fun p => ?_
    simp only [Function.comp, C, pow_mul]; norm_num
    split_ifs <;> (try simp only [abs_mul]) <;> norm_num <;>
      linarith [abs_nonneg
        (Real.lameCosCoeff (fun x => Real.lameEck ν (2 * m) x k) k false (2 * p))]
  have h3 := p2l_hasSum_two_mul_add 0 (fun j hj => ?_) h2
  · obtain ⟨S, T, hS, hT, hST⟩ := p2l_norm_seq hCs k (1 / 2) (C 1) (by
      convert h3 using 1
      funext p
      rcases p with _ | p
      · simp only [C]; norm_num; field_simp
      · have e : Int.natAbs (((2 * (p + 1) + 0 : ℕ) : ℤ) - 2) = 2 * p := by omega
        simp only [C, e]; norm_num [pow_mul]
        rw [show 2 * (p + 1) + 2 = 2 * (p + 1 + 1) by ring]
        field_simp)
    exact ⟨S, T, hS, hT, by linear_combination hST⟩
  · have := (p2l_neg_one_pow_mod j).2.2 (by omega)
    simp [pow_mul, this]

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
am(x, k)` and the Fourier coefficients `A_{2p+1}` of `Real.lameCosCoeff` (weighted by `dn`).
Admitted. -/
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

/-- DLMF 29.6.20: the normalization of the coefficients `A_{2p+1}`. Admitted. -/
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
unweighted Fourier coefficients `C_{2p+1}`. Admitted. -/
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
am(x, k)` and the Fourier coefficients `B_{2p+1}` of `Real.lameSinCoeff` (weighted by `dn`).
Admitted. -/
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

/-- DLMF 29.6.35: the normalization of the coefficients `B_{2p+1}`. Admitted. -/
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
am(x, k)` and the Fourier coefficients `B_{2p+2}` of `Real.lameSinCoeff` (weighted by `dn`).
Admitted. -/
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

/-- DLMF 29.6.50: the normalization of the coefficients `B_{2p+2}`. Admitted. -/
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
