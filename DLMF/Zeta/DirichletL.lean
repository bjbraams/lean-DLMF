/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Hurwitz
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.Analysis.Fourier.ZMod

/-!
# Dirichlet `L`-functions (DLMF §25.15)

DLMF's `L(s, χ)` for a Dirichlet character `χ (mod k)` is Mathlib's
`DirichletCharacter.LFunction χ s` (`χ : DirichletCharacter ℂ k`), the meromorphic continuation of
`LSeries χ`; it is *defined* in Mathlib as `k^{-s} ∑_{j mod k} χ(j) ζ(s, j/k)` with Mathlib's
Hurwitz zeta function, which is DLMF 25.15.3. The principal character `χ₁ (mod k)` is `1`, the
complex conjugate character `χ̄` is `star χ` (`= χ⁻¹`, `MulChar.star_eq_inv`), and DLMF's Gauss sum
`G(χ) = ∑_{r=1}^{k-1} χ(r) e^{2πir/k}` (25.15.6) is `gaussSum χ ZMod.stdAddChar` for `k ≥ 2`
(`gaussSum_stdAddChar_eq_sum`).

**Implicit conditions.** For the modulus `k = 1` (the trivial character, which is primitive and
principal) DLMF's finite sums `∑_{r=1}^{k-1}` are empty, so 25.15.3, 25.15.6 (hence 25.15.5) and
the case `χ = χ₁` of 25.15.10 (`L(0, χ₁) = 0`; in fact `L(0, χ₁) = ζ(0) = -1/2` for `k = 1`) need
`k ≥ 2`; 25.15.7 at `n = 0` likewise. The functional equation 25.15.5 is stated with Mathlib's Gauss
sum, which makes it valid also for `k = 1`; it needs `s ≠ 0, -1, -2, …` (implicit: there `Γ(s)` has
a pole and the right side is a limit).

Upstream pointers for 25.15.1, 25.15.2, 25.15.4, 25.15.8, 25.15.9 and the analyticity statements
of §25.15(i) are in `DLMF.Zeta.MathlibCoverageB`.
-/

@[expose] public section

open Complex Filter Set HurwitzZeta DirichletCharacter
open scoped ZMod
open scoped Real Topology ComplexConjugate

noncomputable section

namespace DLMF.Zeta

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
lemma z25b_map_zero {χ : DirichletCharacter ℂ N} (hN : N ≠ 1) : χ 0 = 0 := by
  have := ZMod.nontrivial_iff.mpr hN
  exact MulChar.map_zero χ

/-- Reindexing a sum over `ZMod N` as a sum over `0 ≤ r < N`. -/
lemma z25b_sum_zmod_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ZMod N → M) :
    ∑ j : ZMod N, f j = ∑ r ∈ Finset.range N, f (r : ZMod N) := by
  refine Finset.sum_bij' (fun j _ => j.val) (fun r _ => (r : ZMod N)) ?_ ?_ ?_ ?_ ?_
  · intro j _; simpa using ZMod.val_lt j
  · intro r _; simp
  · intro j _; simp
  · intro r hr; simpa using ZMod.val_cast_of_lt (Finset.mem_range.mp hr)
  · intro j _; simp

/-- **Pole of the principal `L`-function** (DLMF §25.15(i)): `L(s, χ₁)` has a simple pole at `s = 1`
with residue `φ(k)/k`. -/
@[dlmf 25.15.i]
theorem LFunction_one_residue :
    Tendsto (fun s => (s - 1) * LFunction (1 : DirichletCharacter ℂ N) s) (𝓝[≠] 1)
      (𝓝 ((N.totient : ℂ) / N)) := by
  have h := LFunctionTrivChar_residue_one (N := N)
  have hQ : ((N.totient : ℚ) / N) = ∏ p ∈ N.primeFactors, (1 - (p : ℚ)⁻¹) := by
    rw [Nat.totient_eq_mul_prod_factors, mul_div_cancel_left₀]
    exact Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hC : ((N.totient : ℂ) / N) = ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹) := by
    have := congrArg (fun q : ℚ => (q : ℂ)) hQ
    push_cast at this
    exact this
  rw [hC]
  exact h

/-- **`L` as a combination of Hurwitz zeta functions** (DLMF 25.15.3): for `k ≥ 2` (implicit
condition), `L(s, χ) = k^{-s} ∑_{r=1}^{k-1} χ(r) ζ(s, r/k)`, for all `s` (Mathlib's definition; at
`s = 1` for `χ = χ₁` both sides carry the same junk value). -/
@[dlmf 25.15.E3]
theorem LFunction_eq_sum_hurwitzZeta (χ : DirichletCharacter ℂ N) (hN : N ≠ 1) (s : ℂ) :
    LFunction χ s = (N : ℂ) ^ (-s) *
      ∑ r ∈ Finset.Ico 1 N, χ r * hurwitzZeta ((r / N : ℝ) : UnitAddCircle) s := by
  simp only [DirichletCharacter.LFunction, ZMod.LFunction]
  rw [z25b_sum_zmod_eq_sum_range (fun j => χ j * hurwitzZeta (ZMod.toAddCircle j) s),
    Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.pos_of_ne_zero (NeZero.ne N))]
  simp only [Nat.cast_zero, z25b_map_zero hN, zero_mul, zero_add, ZMod.toAddCircle_natCast]

/-- **The Gauss sum** (DLMF 25.15.6): for `k ≥ 2`, Mathlib's `gaussSum χ ZMod.stdAddChar` is
`G(χ) = ∑_{r=1}^{k-1} χ(r) e^{2πir/k}`. -/
@[dlmf 25.15.E6]
theorem gaussSum_stdAddChar_eq_sum (χ : DirichletCharacter ℂ N) (hN : N ≠ 1) :
    gaussSum χ ZMod.stdAddChar = ∑ r ∈ Finset.Ico 1 N, χ r * cexp (2 * π * I * r / N) := by
  rw [gaussSum, z25b_sum_zmod_eq_sum_range (fun j => χ j * ZMod.stdAddChar j), Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (Nat.pos_of_ne_zero (NeZero.ne N))]
  simp only [Nat.cast_zero, z25b_map_zero hN, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun r _ => ?_
  have := ZMod.stdAddChar_coe (N := N) (r : ℤ)
  simp only [Int.cast_natCast] at this
  rw [this]

/-- **Functional equation** (DLMF 25.15.5): for a primitive character `χ (mod k)`,
`L(1-s, χ) = (k^{s-1} Γ(s)/(2π)^s)(e^{-πis/2} + χ(-1) e^{πis/2}) G(χ) L(s, χ̄)`, with
`G(χ) = gaussSum χ ZMod.stdAddChar` (25.15.6 for `k ≥ 2`). Conditions: `s ≠ 0, -1, -2, …`
(implicit) and, for `k = 1`, `s ≠ 1`. -/
@[dlmf 25.15.E5]
theorem LFunction_one_sub_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hN : N ≠ 1 ∨ s ≠ 1) :
    LFunction χ (1 - s) = (N : ℂ) ^ (s - 1) * Gamma s / (2 * π) ^ s *
      (cexp (-π * I * s / 2) + χ (-1) * cexp (π * I * s / 2)) * gaussSum χ ZMod.stdAddChar *
        LFunction (star χ) s := by
  have hs' : (χ : ZMod N → ℂ) 0 = 0 ∨ s ≠ 1 := hN.imp_left z25b_map_zero
  have h := ZMod.LFunction_one_sub (χ : ZMod N → ℂ) hs hs'
  have hm1 : χ⁻¹ (-1) = χ (-1) := by
    rw [MulChar.inv_apply_eq_inv']
    rcases χ.even_or_odd with he | ho
    · rw [show χ (-1) = 1 from he, inv_one]
    · rw [show χ (-1) = -1 from ho, inv_neg, inv_one]
  have hF1 : 𝓕 (χ : ZMod N → ℂ) =
      fun k => (χ (-1) * gaussSum χ ZMod.stdAddChar) * χ⁻¹ k := by
    funext k
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, show -k = -1 * k by ring, map_mul, hm1]
    ring
  have hF2 : 𝓕 (fun x => (χ : ZMod N → ℂ) (-x)) =
      fun k => gaussSum χ ZMod.stdAddChar * χ⁻¹ k := by
    rw [ZMod.dft_comp_neg]
    funext k
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, neg_neg]
    ring
  have hlin : ∀ (c : ℂ) (Φ : ZMod N → ℂ),
      ZMod.LFunction (fun k => c * Φ k) s = c * ZMod.LFunction Φ s := by
    intro c Φ
    simp only [ZMod.LFunction, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [DirichletCharacter.LFunction]
  rw [h, hF1, hF2, hlin, hlin, MulChar.star_eq_inv, cpow_neg]
  ring

/-! ### §25.15(ii) Zeros -/

/-- **Trivial zeros, even characters** (DLMF 25.15.7): `L(-2n, χ) = 0` for `n = 0, 1, 2, …` if
`χ(-1) = 1`, for every even character `χ (mod k)` with `k ≥ 2` (DLMF: `χ` primitive; stronger
than DLMF apart from the implicit condition `k ≥ 2`, needed at `n = 0`). -/
@[dlmf 25.15.E7]
theorem LFunction_neg_two_mul_nat_eq_zero {χ : DirichletCharacter ℂ N} (hχ : χ.Even)
    (hN : N ≠ 1) (n : ℕ) : LFunction χ (-(2 * n)) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, mul_zero, neg_zero]
    simp only [DirichletCharacter.LFunction]
    rw [ZMod.LFunction_apply_zero_of_even hχ.to_fun, z25b_map_zero hN]
    simp
  · have : NeZero n := ⟨hn.ne'⟩
    exact hχ.LFunction_neg_two_mul_nat n

/-- The Gauss sum of a primitive character does not vanish (Fourier inversion on `ZMod N`). -/
lemma q25b_gaussSum_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar ≠ 0 := by
  intro hG
  have hF : 𝓕 (χ : ZMod N → ℂ) = 0 := by
    funext k; rw [hχ.fourierTransform_eq_inv_mul_gaussSum, hG, mul_zero]; rfl
  have h2 := congrFun (ZMod.dft_dft (χ : ZMod N → ℂ)) (-1)
  rw [hF, map_zero] at h2
  simp only [Pi.zero_apply, neg_neg, MulChar.map_one, smul_eq_mul, mul_one] at h2
  exact (NeZero.ne N) (by exact_mod_cast h2.symm)

/-- **The only zeros in `Re s < 0`** (DLMF §25.15(ii)): for a primitive character `χ (mod k)`,
`k ≥ 2`, the zeros of `L(s, χ)` with `Re s < 0` are the trivial zeros `-2n` (`χ` even) and
`-2n - 1` (`χ` odd). -/
@[dlmf 25.15.ii]
theorem eq_trivial_zero_of_LFunction_eq_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) {s : ℂ} (hs : s.re < 0) (h0 : LFunction χ s = 0) :
    (χ.Even ∧ ∃ n : ℕ, s = -(2 * n)) ∨ (χ.Odd ∧ ∃ n : ℕ, s = -(2 * n) - 1) := by
  set w := 1 - s with hw
  have hwre : 1 < w.re := by simp [hw]; linarith
  have hwn : ∀ n : ℕ, w ≠ -n := fun n h => by
    have := congrArg Complex.re h; simp at this; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hFE := LFunction_one_sub_of_isPrimitive hχ hwn (Or.inl hN)
  rw [hw, sub_sub_cancel, ← hw, h0] at hFE
  have hL : LFunction (star χ) w ≠ 0 :=
    LFunction_ne_zero_of_one_le_re (star χ) (Or.inr fun h => by rw [h] at hwre; simp at hwre)
      hwre.le
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h2π : (2 * π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hE : cexp (-π * I * w / 2) + χ (-1) * cexp (π * I * w / 2) = 0 := by
    rcases mul_eq_zero.mp hFE.symm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exfalso
          rcases div_eq_zero_iff.mp h with h | h
          · rcases mul_eq_zero.mp h with h | h
            · exact cpow_ne_zero_iff.mpr (Or.inl hN0) h
            · exact Gamma_ne_zero_of_re_pos (by linarith) h
          · exact cpow_ne_zero_iff.mpr (Or.inl h2π) h
        · exact h
      · exact absurd h (q25b_gaussSum_ne_zero hχ)
    · exact absurd h hL
  rcases χ.even_or_odd with he | ho
  · left
    refine ⟨he, ?_⟩
    rw [show χ (-1) = 1 from he, one_mul] at hE
    have hc : Complex.cos (π * w / 2) = 0 := by
      have : Complex.cos (π * w / 2) = (cexp (-π * I * w / 2) + cexp (π * I * w / 2)) / 2 := by
        rw [Complex.cos]; ring_nf
      rw [this, hE, zero_div]
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
    have hwk : w = 2 * k + 1 := by
      have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      apply mul_left_cancel₀ hπ; linear_combination 2 * hk
    have hk0 : 0 < k := by
      have := congrArg Complex.re hwk; simp at this
      have : (0 : ℝ) < k := by linarith
      exact_mod_cast this
    refine ⟨k.toNat, ?_⟩
    rw [show ((k.toNat : ℕ) : ℂ) = (k : ℂ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hk0.le]]
    linear_combination -hwk + hw
  · right
    refine ⟨ho, ?_⟩
    rw [show χ (-1) = -1 from ho] at hE
    have hc : Complex.sin (π * w / 2) = 0 := by
      have : Complex.sin (π * w / 2) = (cexp (-π * I * w / 2) + -1 * cexp (π * I * w / 2)) *
          (I / 2) := by
        rw [Complex.sin]; ring_nf
      rw [this, hE, zero_mul]
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hc
    have hwk : w = 2 * k := by
      have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      apply mul_left_cancel₀ hπ; linear_combination 2 * hk
    have hk0 : 0 < k := by
      have := congrArg Complex.re hwk; simp at this
      have : (0 : ℝ) < k := by linarith
      exact_mod_cast this
    refine ⟨(k - 1).toNat, ?_⟩
    rw [show (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring]
    linear_combination -hwk + hw

/-- `L(s̄, χ̄) = conj L(s, χ)` for a non-principal Dirichlet character. -/
theorem r25b_LFunction_star_conj {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (s : ℂ) :
    LFunction (star χ) (conj s) = conj (LFunction χ s) := by
  have hχ' : star χ ≠ 1 := by
    rw [MulChar.star_eq_inv]; exact fun h => hχ (inv_eq_one.mp h)
  set F : ℂ → ℂ := conj ∘ LFunction χ ∘ conj
  have hF : Differentiable ℂ F := fun z => by
    have := (differentiable_LFunction hχ (conj z)).conj_conj
    simpa [F] using this
  have hG : Differentiable ℂ (LFunction (star χ)) := differentiable_LFunction hχ'
  have heq : LFunction (star χ) = F := by
    have hEq := (hG.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
      (hF.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ (2 : ℂ)) ?_
    · funext z; exact hEq (mem_univ z)
    have hopen : IsOpen {t : ℂ | 1 < t.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with t ht
    have ht' : 1 < (conj t).re := by simpa using ht
    simp only [F, Function.comp_apply]
    rw [LFunction_eq_LSeries _ ht, LFunction_eq_LSeries _ ht', LSeries, LSeries, conj_tsum]
    congr 1; funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀]
    congr 1
    rw [cpow_conj _ _ (by simp [Complex.natCast_arg, Real.pi_ne_zero.symm]), conj_conj,
      Complex.conj_natCast]
  rw [heq]
  simp [F]

/-- **Infinitely many zeros in the critical strip** (DLMF §25.15(ii)), for primitive `χ`. -/
@[dlmf 25.15.ii]
theorem infinite_LFunction_zeros_criticalStrip {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) :
    {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ LFunction χ s = 0}.Infinite := by
  sorry

/-- **Symmetry about the critical line** (DLMF §25.15(ii)): for primitive `χ (mod k)`, `k ≥ 2`, if
`ρ ≠ 0` is a zero in the closed critical strip then so is `1 - ρ̄`. (Not necessarily symmetric
about the real axis: `ρ̄` is a zero of `L(s, χ̄)`.) Correction: DLMF states the symmetry for all
zeros in `0 ≤ ℜ s ≤ 1`, but for even `χ` the trivial zero `s = 0` lies in that strip while
`L(1, χ) ≠ 0`; see `q25b_LFunction_one_sub_conj_counterexample`. -/
@[dlmf 25.15.ii]
theorem LFunction_one_sub_conj_eq_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) {ρ : ℂ} (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) (hρ0 : ρ ≠ 0)
    (hρ : LFunction χ ρ = 0) :
    LFunction χ (1 - (starRingEnd ℂ) ρ) = 0 := by
  have _ := h1
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    apply hN
    rw [IsPrimitive, conductor_one] at hχ
    exact hχ.symm
  have hs : ∀ n : ℕ, conj ρ ≠ -n := by
    intro n h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp at hre him
    have hn : (n : ℝ) = 0 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    exact hρ0 (Complex.ext (by simp; linarith) (by simpa using him))
  rw [LFunction_one_sub_of_isPrimitive hχ hs (Or.inl hN), r25b_LFunction_star_conj hχ1, hρ,
    map_zero, mul_zero]


/-- **Evidence that `LFunction_one_sub_conj_eq_zero` needs `ρ ≠ 0`** (DLMF's closed-strip
wording is too broad): for an even character
`χ ≠ χ₁ (mod k)`, `k ≥ 2` (e.g. a primitive even character such as the quadratic character
mod 5), `ρ = 0` is a zero with `0 ≤ Re ρ ≤ 1`, but `L(1 - ρ̄, χ) = L(1, χ) ≠ 0`. (The trivial zero
at `s = 0` lies on the boundary of the closed critical strip; hence the hypothesis `ρ ≠ 0`.) -/
theorem q25b_LFunction_one_sub_conj_counterexample {χ : DirichletCharacter ℂ N} (hχ : χ.Even)
    (hN : N ≠ 1) (h1 : χ ≠ 1) :
    LFunction χ 0 = 0 ∧ LFunction χ (1 - (starRingEnd ℂ) 0) ≠ 0 := by
  refine ⟨by simpa using LFunction_neg_two_mul_nat_eq_zero hχ hN 0, ?_⟩
  rw [map_zero, sub_zero]
  exact LFunction_apply_one_ne_zero h1

/-- **`L(0, χ)`** (DLMF 25.15.10), non-principal case: `L(0, χ) = -(1/k) ∑_{r=1}^{k-1} r χ(r)` for
`χ ≠ χ₁`. -/
@[dlmf 25.15.E10]
theorem LFunction_zero_of_ne_one {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    LFunction χ 0 = -(1 / N) * ∑ r ∈ Finset.Ico 1 N, (r : ℂ) * χ r := by
  have hN : N ≠ 1 := fun h => hχ (level_one' χ h)
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hsum : ∑ r ∈ Finset.Ico 1 N, χ r = 0 := by
    have h := MulChar.sum_eq_zero_of_ne_one hχ
    rw [z25b_sum_zmod_eq_sum_range (fun j => χ j), Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (Nat.pos_of_ne_zero (NeZero.ne N))] at h
    simpa [z25b_map_zero hN] using h
  rw [LFunction_eq_sum_hurwitzZeta χ hN 0, neg_zero, cpow_zero, one_mul]
  have hterm : ∀ r ∈ Finset.Ico 1 N, χ r * hurwitzZeta ((r / N : ℝ) : UnitAddCircle) 0 =
      1 / 2 * χ r - 1 / N * ((r : ℂ) * χ r) := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have h1 : (0 : ℝ) < r / N := by
      have : (0 : ℝ) < r := by exact_mod_cast hr.1
      positivity
    have h2 : (r : ℝ) / N ≤ 1 := by
      rw [div_le_one (by positivity)]; exact_mod_cast hr.2.le
    rw [r25b_hurwitzZeta_zero h1 h2]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hsum]
  ring


/-- **`L(0, χ₁) = 0`** (DLMF 25.15.10), principal case, for `k ≥ 2` (implicit condition; for
`k = 1`, `L(0, χ₁) = ζ(0) = -1/2`). -/
@[dlmf 25.15.E10]
theorem LFunction_one_zero (hN : N ≠ 1) : LFunction (1 : DirichletCharacter ℂ N) 0 = 0 := by
  have h := LFunctionTrivChar_eq_mul_riemannZeta (N := N) (by norm_num : (0 : ℂ) ≠ 1)
  simp only [LFunctionTrivChar] at h
  rw [h]
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr
    (lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) (Ne.symm hN))
  rw [Finset.prod_eq_zero hp (by simp), zero_mul]

end DLMF.Zeta

end
