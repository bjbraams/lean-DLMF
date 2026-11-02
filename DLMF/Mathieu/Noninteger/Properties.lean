/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Noninteger.Basic
public import DLMF.Mathieu.Noninteger.ExpSeries
public import DLMF.Mathieu.Noninteger.RealContinuation
public import DLMF.Mathieu.Properties
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Mathieu functions of noninteger order: basic properties

This file proves the statements of DLMF §28.12 (eigenvalues `λ_ν(q)`, Floquet solutions
`me_ν(z, q)`, the functions `ce_ν`, `se_ν`) and the recurrence and normalization of §28.14 for
the definitions of `DLMF.Mathieu.Noninteger.Basic`. The values at `q = 0` follow because along
the segment `[0, 0]` the only continuation is the constant one (a continuous path in the
countable set `{(ν + 2m)²}` is constant, and the sign of `c_0` is fixed by continuity). The
symmetries are obtained by transporting continuation paths along the involutions
`c_m ↦ c_{-m}` (`ν ↦ -ν`), `c_m ↦ (-1)^m c_m` (`q ↦ -q`) and complex conjugation. The key
analytic step is that an absolutely summable solution of the recurrence 28.14.4 decays faster
than every exponential, so `∑ c_m e^{i(ν+2m)z}` is entire and can be differentiated termwise
(`DLMF.Mathieu.Noninteger.ExpSeries`). Normality of real parameters follows the root of
`cos πν = w_I(π; a, tq)` along `t ∈ [0, 1]` (`DLMF.Mathieu.Noninteger.RealContinuation`).

## Main results

* `isMeCoeffSeq_mathieuLambdaData`: at a normal value the continuation data solve 28.14.4 with
  the normalization 28.14.5.
* `mathieuLambda_zero`, `mathieuMe_zero`: the values at `q = 0` (DLMF 28.12.1, 28.12.4).
* `isMathieuCharExp_iff_exists_mathieuLambda`, `mathieuNormalSegment_real`,
  `not_continuousAt_mathieuLambda`: the roots of 28.2.16, normality of real parameters and the
  discontinuity in `ν` at the integers (DLMF §28.12(i)).
* `mathieuLambda_neg_q_and_neg_nu`, `mathieuLambda_intCast_eq`: DLMF 28.12.2, 28.12.3.
* `integral_mathieuMe_mul_neg`, `integral_mathieuMe_orthogonal`: the normalization 28.12.5 and
  the orthogonality 28.12.7.
* `mathieuMe_add_pi`: the pseudoperiodicity 28.12.6.
* `mathieuMe_neg_nu`, `mathieuMe_neg_q`, `conj_mathieuMe`: DLMF 28.12.8–28.12.10.
* `mathieuMe_natCast`, `mathieuMe_neg_natCast`: the integer-order values 28.12.11.
* `isFloquetSolution_mathieuMe`, `isMathieuCharExp_mathieuLambda`: the Floquet property of
  `me_ν` and the characteristic equation `cos πν = w_I(π; λ_ν(q), q)` (DLMF §28.12(i), (ii)).
* `mathieuCeNu_mathieuSeNu_real`: reality of `ce_ν`, `se_ν` for real `ν`, `q`, `x`
  (DLMF §28.12(iii)).
* `mathieu_periodic_of_rational`: periodicity of all solutions for rational noninteger `ν`
  (DLMF §28.12(iii)), from the Floquet dichotomy of `DLMF.Mathieu.Properties`.
* `mathieuCeNu_neg`, `mathieuSeNu_neg`: DLMF 28.12.14, 28.12.15.

## Implementation notes

All statements are for `ν ∉ ℤ`, as in DLMF §28.12 ("we now restrict `ν̂ ≠ 0, 1`"); several of
them are false for integer `ν` with DLMF's completion 28.12.3, 28.12.11 (for example
`λ_1(-q) = a_1(-q) = b_1(q) ≠ λ_1(q)`).

**Stronger than DLMF (28.12.10).** DLMF warns that 28.12.10 "is not valid for cuts on the real
axis in the `q`-plane for special complex values of `ν`". With the straight-segment
continuation used here (`DLMF.Mathieu.MathieuNormalSegment`), conjugation maps continuation
paths to continuation paths, and 28.12.10 holds for every `ν ∉ ℤ` and every `q` (when `q` is
not normal along the segment both sides are junk values).
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics MeasureTheory
open scoped Topology Real Classical ComplexConjugate

namespace DLMF.Mathieu

/-! ### The continuation endpoint -/

/-- If `p` is an endpoint of a continuation path and every endpoint equals `p`, then
`mathieuLambdaData ν q = p`. -/
private lemma mathieuLambdaData_eq_of_unique {ν q : ℂ} {p : ℂ × (ℤ → ℂ)}
    (hp : ∃ Λ c, IsMathieuLambdaPath ν q Λ c ∧ Λ 1 = p.1 ∧ c 1 = p.2)
    (hu : ∀ p' : ℂ × (ℤ → ℂ), (∃ Λ c, IsMathieuLambdaPath ν q Λ c ∧ Λ 1 = p'.1 ∧ c 1 = p'.2) →
      p' = p) :
    mathieuLambdaData ν q = p := by
  have h : MathieuNormalSegment ν q := ⟨p, hp, hu⟩
  simp only [mathieuLambdaData, h, dite_true]
  exact hu _ h.choose_spec.1

/-- At a normal value the endpoint is attained by a continuation path. -/
private lemma exists_isMathieuLambdaPath_mathieuLambdaData {ν q : ℂ} (h : MathieuNormalSegment ν q) :
    ∃ Λ c, IsMathieuLambdaPath ν q Λ c ∧ Λ 1 = (mathieuLambdaData ν q).1 ∧
      c 1 = (mathieuLambdaData ν q).2 := by
  simp only [mathieuLambdaData, h, dite_true]
  exact h.choose_spec.1

/-- At a normal value, `(λ_ν(q), c^ν(q))` solves the recurrence 28.14.4 with the normalization
28.14.5. -/
theorem isMeCoeffSeq_mathieuLambdaData {ν q : ℂ} (h : MathieuNormalSegment ν q) :
    IsMeCoeffSeq ν q (mathieuLambdaData ν q).1 (mathieuLambdaData ν q).2 := by
  obtain ⟨Λ, c, hp, h1, h2⟩ := exists_isMathieuLambdaPath_mathieuLambdaData h
  have := hp.isMeCoeffSeq 1 ⟨zero_le_one, le_rfl⟩
  rw [h1, h2] at this
  simpa using this

/-- **Transport of continuation data** along an involution `F` of `ℂ × (ℤ → ℂ)` fixing the
junk value `(0, 0)`, when `F` maps the continuation paths for `(ν, q)` to those for
`(ν', q')` and back. -/
private lemma mathieuLambdaData_transport {ν q ν' q' : ℂ} (F : ℂ × (ℤ → ℂ) → ℂ × (ℤ → ℂ))
    (hF : Function.Involutive F) (hF0 : F (0, 0) = (0, 0))
    (h₁ : ∀ Λ c, IsMathieuLambdaPath ν q Λ c →
      ∃ Λ' c', IsMathieuLambdaPath ν' q' Λ' c' ∧ (Λ' 1, c' 1) = F (Λ 1, c 1))
    (h₂ : ∀ Λ c, IsMathieuLambdaPath ν' q' Λ c →
      ∃ Λ' c', IsMathieuLambdaPath ν q Λ' c' ∧ (Λ' 1, c' 1) = F (Λ 1, c 1)) :
    mathieuLambdaData ν' q' = F (mathieuLambdaData ν q) := by
  -- endpoints
  have e₁ : ∀ p : ℂ × (ℤ → ℂ), (∃ Λ c, IsMathieuLambdaPath ν q Λ c ∧ Λ 1 = p.1 ∧ c 1 = p.2) →
      ∃ Λ c, IsMathieuLambdaPath ν' q' Λ c ∧ Λ 1 = (F p).1 ∧ c 1 = (F p).2 := by
    rintro ⟨a, b⟩ ⟨Λ, c, hp, rfl, rfl⟩
    obtain ⟨Λ', c', hp', he⟩ := h₁ Λ c hp
    exact ⟨Λ', c', hp', by rw [← he], by rw [← he]⟩
  have e₂ : ∀ p : ℂ × (ℤ → ℂ), (∃ Λ c, IsMathieuLambdaPath ν' q' Λ c ∧ Λ 1 = p.1 ∧ c 1 = p.2) →
      ∃ Λ c, IsMathieuLambdaPath ν q Λ c ∧ Λ 1 = (F p).1 ∧ c 1 = (F p).2 := by
    rintro ⟨a, b⟩ ⟨Λ, c, hp, rfl, rfl⟩
    obtain ⟨Λ', c', hp', he⟩ := h₂ Λ c hp
    exact ⟨Λ', c', hp', by rw [← he], by rw [← he]⟩
  by_cases h : MathieuNormalSegment ν q
  · obtain ⟨p, hp, hu⟩ := h
    have hdata : mathieuLambdaData ν q = p := mathieuLambdaData_eq_of_unique hp hu
    rw [hdata]
    refine mathieuLambdaData_eq_of_unique (e₁ p hp) fun p' hp' => ?_
    have := hu _ (e₂ p' hp')
    rw [← this, hF p']
  · have h' : ¬ MathieuNormalSegment ν' q' := by
      rintro ⟨p, hp, hu⟩
      refine h ⟨F p, e₂ p hp, fun p' hp' => ?_⟩
      have := hu _ (e₁ p' hp')
      rw [← this, hF p']
    simp only [mathieuLambdaData, h, h', dite_false, hF0]

/-! ### The case `q = 0` -/

/-- For `ν ∉ ℤ` and `m ≠ 0`, `ν² ≠ (ν + 2m)²`. -/
private lemma sq_sub_add_two_mul_sq_ne_zero {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {m : ℤ} (hm : m ≠ 0) :
    ν ^ 2 - (ν + 2 * m) ^ 2 ≠ 0 := by
  have e : ν ^ 2 - (ν + 2 * m) ^ 2 = -4 * m * (ν + m) := by ring
  rw [e]
  refine mul_ne_zero (mul_ne_zero (by norm_num) (Int.cast_ne_zero.mpr hm)) fun h => ?_
  exact hν (-m) (by push_cast; linear_combination -h)

/-- At `q = 0`, the sequence `δ_{m,0}` is a coefficient sequence for `me_ν` with `λ = ν²`. -/
private lemma isMeCoeffSeq_single_zero (ν : ℂ) (t : ℝ) :
    IsMeCoeffSeq ν ((t : ℂ) * 0) (ν ^ 2) (Pi.single 0 1) := by
  refine ⟨fun m => ?_, ?_, ?_⟩
  · by_cases hm : m = 0
    · subst hm; simp
    · simp [hm]
  · exact (hasSum_single (0 : ℤ) fun m hm => by simp [hm]).summable
  · have := hasSum_single (f := fun m : ℤ => (Pi.single 0 1 : ℤ → ℂ) m ^ 2) (0 : ℤ)
      fun m hm => by simp [hm]
    simpa using this

/-- A continuous function on `[0, 1]` with values in a countable set is constant there. -/
private lemma eq_of_countable_continuousOn_Icc {f : ℝ → ℂ} {S : Set ℂ} (hS : S.Countable)
    (hf : ContinuousOn f (Icc 0 1)) (hfS : ∀ t ∈ Icc (0 : ℝ) 1, f t ∈ S) :
    ∀ t ∈ Icc (0 : ℝ) 1, f t = f 0 := by
  intro t ht
  have hsub : f '' Icc 0 1 ⊆ S := by rintro _ ⟨s, hs, rfl⟩; exact hfS s hs
  have hsing := hS.isTotallyDisconnected _ hsub (isPreconnected_Icc.image f hf)
  exact hsing ⟨t, ht, rfl⟩ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩

/-- Every continuation path for `q = 0` is the constant path `(ν², δ_0)`. -/
private lemma isMathieuLambdaPath_zero_eq_const {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {Λ : ℝ → ℂ} {c : ℝ → ℤ → ℂ}
    (hp : IsMathieuLambdaPath ν 0 Λ c) :
    ∀ t ∈ Icc (0 : ℝ) 1, Λ t = ν ^ 2 ∧ c t = Pi.single 0 1 := by
  have hrec : ∀ t ∈ Icc (0 : ℝ) 1, ∀ m : ℤ, (Λ t - (ν + 2 * m) ^ 2) * c t m = 0 := by
    intro t ht m
    have := (hp.isMeCoeffSeq t ht).1 m
    simp only [mul_zero, zero_mul, zero_sub, add_zero, neg_eq_zero] at this
    exact this
  have hΛS : ∀ t ∈ Icc (0 : ℝ) 1, Λ t ∈ Set.range (fun m : ℤ => (ν + 2 * m) ^ 2) := by
    intro t ht
    by_contra hns
    have h0 : ∀ m, c t m = 0 := fun m => by
      have := hrec t ht m
      rcases mul_eq_zero.mp this with h | h
      · exact absurd ⟨m, (sub_eq_zero.mp h).symm⟩ hns
      · exact h
    have := (hp.isMeCoeffSeq t ht).2.2
    simp only [h0] at this
    exact one_ne_zero ((hasSum_zero.congr_fun (by simp)).unique this).symm
  have hΛ : ∀ t ∈ Icc (0 : ℝ) 1, Λ t = ν ^ 2 := by
    intro t ht
    rw [eq_of_countable_continuousOn_Icc (Set.countable_range _) hp.continuousOn_lambda hΛS t ht,
      hp.lambda_zero]
  have hcm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ m : ℤ, m ≠ 0 → c t m = 0 := by
    intro t ht m hm
    have := hrec t ht m
    rw [hΛ t ht] at this
    exact (mul_eq_zero.mp this).resolve_left (sq_sub_add_two_mul_sq_ne_zero hν hm)
  have hc0 : ∀ t ∈ Icc (0 : ℝ) 1, c t 0 ∈ ({1, -1} : Set ℂ) := by
    intro t ht
    have h1 := (hp.isMeCoeffSeq t ht).2.2
    have h2 := hasSum_single (f := fun m : ℤ => c t m ^ 2) (0 : ℤ)
      fun m hm => by simp [hcm t ht m hm]
    have := h2.unique h1
    rw [sq] at this
    rcases mul_self_eq_one_iff.mp this with h | h <;> simp [h]
  have hc0' : ∀ t ∈ Icc (0 : ℝ) 1, c t 0 = 1 := by
    intro t ht
    rw [eq_of_countable_continuousOn_Icc (Set.toFinite _).countable (hp.continuousOn_coeff 0) hc0 t ht,
      hp.coeff_zero]
  intro t ht
  refine ⟨hΛ t ht, funext fun m => ?_⟩
  by_cases hm : m = 0
  · subst hm; simp [hc0' t ht]
  · simp [hm, hcm t ht m hm]

/-- The continuation data at `q = 0`: `(ν², δ_0)`. -/
theorem mathieuLambdaData_zero {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) :
    mathieuLambdaData ν 0 = (ν ^ 2, Pi.single 0 1) := by
  refine mathieuLambdaData_eq_of_unique ⟨fun _ => ν ^ 2, fun _ => Pi.single 0 1,
    ⟨continuousOn_const, fun m => continuousOn_const, rfl, by simp,
      fun t _ => isMeCoeffSeq_single_zero ν t⟩, rfl, rfl⟩ ?_
  rintro ⟨a, b⟩ ⟨Λ, c, hp, rfl, rfl⟩
  obtain ⟨h1, h2⟩ := isMathieuLambdaPath_zero_eq_const hν hp 1 ⟨zero_le_one, le_rfl⟩
  rw [h1, h2]

/-- `0` is normal along the segment for `ν ∉ ℤ`. -/
theorem mathieuNormalSegment_zero {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) :
    MathieuNormalSegment ν 0 := by
  refine ⟨(ν ^ 2, Pi.single 0 1), ⟨fun _ => ν ^ 2, fun _ => Pi.single 0 1,
    ⟨continuousOn_const, fun m => continuousOn_const, rfl, by simp,
      fun t _ => isMeCoeffSeq_single_zero ν t⟩, rfl, rfl⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨Λ, c, hp, rfl, rfl⟩
  obtain ⟨h1, h2⟩ := isMathieuLambdaPath_zero_eq_const hν hp 1 ⟨zero_le_one, le_rfl⟩
  rw [h1, h2]

/-! ### §28.12(i) Eigenvalues -/

/-- `ν ∉ ℤ` implies `ν + 2n ∉ ℤ`, `-ν ∉ ℤ`, `conj ν ∉ ℤ`. -/
theorem intCast_ne_neg_of_not_int {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) : ∀ m : ℤ, (m : ℂ) ≠ -ν :=
  fun m h => hν (-m) (by push_cast; rw [h, neg_neg])

/-- If `ν ∉ ℤ` then `ν̄ ∉ ℤ`. -/
private lemma intCast_ne_conj_of_not_int {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) :
    ∀ m : ℤ, (m : ℂ) ≠ conj ν :=
  fun m h => hν m (by rw [← Complex.conj_conj ν, ← h]; simp)

/-- If `ν ∉ ℤ` then `ν + 2n ∉ ℤ` for every integer `n`. -/
private lemma intCast_ne_add_two_mul_of_not_int {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (n : ℤ) :
    ∀ m : ℤ, (m : ℂ) ≠ ν + 2 * n :=
  fun m h => hν (m - 2 * n) (by push_cast; rw [h]; ring)

/-- **Eigenvalues at `q = 0`** (DLMF 28.12.1): `λ_ν(0) = ν²` for `ν ∉ ℤ` (DLMF writes
`λ_{ν+2n}(0) = (ν + 2n)²`; with `ν` replaced by `ν + 2n` this is the same statement). -/
@[dlmf 28.12.E1]
theorem mathieuLambda_zero {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) : mathieuLambda ν 0 = ν ^ 2 := by
  rw [mathieuLambda_of_not_int hν, mathieuLambdaData_zero hν]

/-- **The roots of 28.2.16** (DLMF §28.12(i)): for `ν ∉ ℤ`, if `q` is normal along the segment
with respect to every `ν + 2n`, the roots `a` of `cos(πν) = w_I(π; a, q)` are exactly the
values `λ_{ν+2n}(q)`, `n ∈ ℤ`. -/
@[dlmf 28.12.i]
theorem isMathieuCharExp_iff_exists_mathieuLambda {ν q a : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    (hq : ∀ n : ℤ, MathieuNormalSegment (ν + 2 * n) q) :
    IsMathieuCharExp a q ν ↔ ∃ n : ℤ, a = mathieuLambda (ν + 2 * n) q := by
  sorry

/-- **Discontinuity in `ν`** (DLMF §28.12(i)): for fixed real `q ≠ 0`, `λ_ν(q)` is
discontinuous (as a function of real `ν`) at `ν = ±1, ±2, …`. -/
@[dlmf 28.12.i]
theorem not_continuousAt_mathieuLambda {q : ℝ} (hq : q ≠ 0) {n : ℤ} (hn : n ≠ 0) :
    ¬ ContinuousAt (fun ν : ℝ => mathieuLambda ν q) n := by
  sorry

/-- The continuation paths for `-ν` are those for `ν` with `c_m` replaced by `c_{-m}`. -/
private lemma isMathieuLambdaPath_neg_nu {ν q : ℂ} {Λ : ℝ → ℂ} {c : ℝ → ℤ → ℂ}
    (hp : IsMathieuLambdaPath ν q Λ c) :
    IsMathieuLambdaPath (-ν) q Λ (fun t m => c t (-m)) := by
  refine ⟨hp.continuousOn_lambda, fun m => hp.continuousOn_coeff (-m), by
    rw [hp.lambda_zero]; ring, by simpa using hp.coeff_zero, fun t ht => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hp.isMeCoeffSeq t ht
  refine ⟨fun m => ?_, (Equiv.neg ℤ).summable_iff.mpr h2, (Equiv.neg ℤ).hasSum_iff.mpr h3⟩
  have := h1 (-m)
  rw [show -m + 1 = -(m - 1) by ring, show -m - 1 = -(m + 1) by ring] at this
  push_cast at this ⊢
  linear_combination this

/-- The continuation data for `-ν` (proved by transport). -/
theorem mathieuLambdaData_neg_nu (ν q : ℂ) :
    mathieuLambdaData (-ν) q =
      ((mathieuLambdaData ν q).1, fun m => (mathieuLambdaData ν q).2 (-m)) := by
  have := mathieuLambdaData_transport (ν := ν) (q := q) (ν' := -ν) (q' := q)
    (fun p => (p.1, fun m => p.2 (-m))) (fun p => by simp) (by ext m <;> simp)
    (fun Λ c hp => ⟨_, _, isMathieuLambdaPath_neg_nu hp, rfl⟩)
    (fun Λ c hp => ⟨_, _, by simpa using isMathieuLambdaPath_neg_nu hp, rfl⟩)
  exact this

/-- `(-1)^m (-1)^m = 1` for an integer `m`. -/
theorem neg_one_zpow_mul_self_eq_one (m : ℤ) : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
  rcases Int.even_or_odd m with h | h
  · rw [h.neg_one_zpow]; ring
  · rw [h.neg_one_zpow]; ring

/-- The continuation paths for `-q` are those for `q` with `c_m` replaced by `(-1)^m c_m`. -/
private lemma isMathieuLambdaPath_neg_q {ν q : ℂ} {Λ : ℝ → ℂ} {c : ℝ → ℤ → ℂ}
    (hp : IsMathieuLambdaPath ν q Λ c) :
    IsMathieuLambdaPath ν (-q) Λ (fun t m => (-1 : ℂ) ^ m * c t m) := by
  refine ⟨hp.continuousOn_lambda, fun m => continuousOn_const.mul (hp.continuousOn_coeff m),
    hp.lambda_zero, by simpa using hp.coeff_zero, fun t ht => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hp.isMeCoeffSeq t ht
  have hne : (-1 : ℂ) ≠ 0 := by norm_num
  refine ⟨fun m => ?_, ?_, ?_⟩
  · have := h1 m
    beta_reduce
    rw [zpow_add_one₀ hne, zpow_sub_one₀ hne]
    linear_combination ((-1 : ℂ) ^ m) * this
  · refine h2.congr fun m => ?_
    rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]
  · refine h3.congr_fun fun m => ?_
    rw [mul_pow, sq ((-1 : ℂ) ^ m), neg_one_zpow_mul_self_eq_one, one_mul]

/-- The continuation data for `-q` (proved by transport). -/
theorem mathieuLambdaData_neg_q (ν q : ℂ) :
    mathieuLambdaData ν (-q) =
      ((mathieuLambdaData ν q).1, fun m => (-1 : ℂ) ^ m * (mathieuLambdaData ν q).2 m) := by
  have := mathieuLambdaData_transport (ν := ν) (q := q) (ν' := ν) (q' := -q)
    (fun p => (p.1, fun m => (-1 : ℂ) ^ m * p.2 m))
    (fun p => by ext m <;> simp [← mul_assoc, neg_one_zpow_mul_self_eq_one]) (by ext m <;> simp)
    (fun Λ c hp => ⟨_, _, isMathieuLambdaPath_neg_q hp, rfl⟩)
    (fun Λ c hp => ⟨_, _, by simpa using isMathieuLambdaPath_neg_q hp, rfl⟩)
  exact this

/-- The continuation paths for `(conj ν, conj q)` are the conjugates of those for `(ν, q)`. -/
private lemma isMathieuLambdaPath_conj {ν q : ℂ} {Λ : ℝ → ℂ} {c : ℝ → ℤ → ℂ}
    (hp : IsMathieuLambdaPath ν q Λ c) :
    IsMathieuLambdaPath (conj ν) (conj q) (fun t => conj (Λ t)) (fun t m => conj (c t m)) := by
  refine ⟨Complex.continuous_conj.comp_continuousOn hp.continuousOn_lambda,
    fun m => Complex.continuous_conj.comp_continuousOn (hp.continuousOn_coeff m), by
      rw [hp.lambda_zero, map_pow], by rw [hp.coeff_zero, map_one], fun t ht => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hp.isMeCoeffSeq t ht
  refine ⟨fun m => ?_, h2.congr fun m => (Complex.norm_conj _).symm, ?_⟩
  · have := congrArg conj (h1 m)
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_intCast, Complex.conj_ofReal,
      map_zero] at this
    exact this
  · have := (Complex.hasSum_conj' (L := SummationFilter.unconditional ℤ)).mpr h3
    simpa [map_pow] using this

/-- The continuation data for `(conj ν, conj q)` (proved by transport). -/
theorem mathieuLambdaData_conj (ν q : ℂ) :
    mathieuLambdaData (conj ν) (conj q) =
      (conj (mathieuLambdaData ν q).1, fun m => conj ((mathieuLambdaData ν q).2 m)) := by
  have := mathieuLambdaData_transport (ν := ν) (q := q) (ν' := conj ν) (q' := conj q)
    (fun p => (conj p.1, fun m => conj (p.2 m))) (fun p => by simp) (by ext m <;> simp)
    (fun Λ c hp => ⟨_, _, isMathieuLambdaPath_conj hp, rfl⟩)
    (fun Λ c hp => ⟨_, _, by simpa using isMathieuLambdaPath_conj hp, rfl⟩)
  exact this

/-- **Symmetries of `λ_ν`** (DLMF 28.12.2): `λ_ν(-q) = λ_ν(q) = λ_{-ν}(q)` for `ν ∉ ℤ`. -/
@[dlmf 28.12.E2]
theorem mathieuLambda_neg_q_and_neg_nu {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (q : ℂ) :
    mathieuLambda ν (-q) = mathieuLambda ν q ∧ mathieuLambda (-ν) q = mathieuLambda ν q := by
  rw [mathieuLambda_of_not_int hν, mathieuLambda_of_not_int hν,
    mathieuLambda_of_not_int (intCast_ne_neg_of_not_int hν), mathieuLambdaData_neg_q, mathieuLambdaData_neg_nu]
  exact ⟨rfl, rfl⟩

/-- **Integer order** (DLMF 28.12.3): `λ_m(q) = a_m(q)` for `m = 0, 1, …` and
`λ_m(q) = b_{-m}(q)` for `m = -1, -2, …` (real `q`). -/
@[dlmf 28.12.E3]
theorem mathieuLambda_intCast_eq (m : ℤ) (q : ℝ) :
    mathieuLambda m q = if 0 ≤ m then (mathieuA m.toNat q : ℂ) else mathieuB m.natAbs q := by
  rw [mathieuLambda_intCast, mathieuLambdaInt]
  split_ifs <;> rfl

/-! ### §28.12(ii) The functions `me_ν` -/

/-- **`me_ν` at `q = 0`** (DLMF 28.12.4): `me_ν(z, 0) = e^{iνz}` for `ν ∉ ℤ`. -/
@[dlmf 28.12.E4]
theorem mathieuMe_zero {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (z : ℂ) :
    mathieuMe ν z 0 = Complex.exp (I * ν * z) := by
  rw [mathieuMe_of_not_int hν]
  simp only [mathieuMeCoeff_of_not_int hν, mathieuLambdaData_zero hν]
  rw [tsum_eq_single 0 fun m hm => by simp [hm]]
  simp

/-- **Normalization** (DLMF 28.12.5): `∫₀^π me_ν(x, q) me_ν(-x, q) dx = π` for `ν ∉ ℤ` and `q`
normal along the segment. -/
@[dlmf 28.12.E5]
theorem integral_mathieuMe_mul_neg {ν q : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    (hq : MathieuNormalSegment ν q) :
    ∫ x in (0 : ℝ)..π, mathieuMe ν x q * mathieuMe ν (-x) q = π := by
  have hd := isMeCoeffSeq_mathieuLambdaData hq
  set c := (mathieuLambdaData ν q).2
  have hme : ∀ z, mathieuMe ν z q = ∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * z) := by
    intro z; rw [mathieuMe_of_not_int hν]; simp only [mathieuMeCoeff_of_not_int hν, c]
  have hsol := isMathieuSolution_tsum_exp_series hd.1 hd.2.1
  simp only [hme]
  rw [integral_tsum_exp_series_mul_neg hd.2.1 (hsol.differentiable.continuous.comp
    Complex.continuous_ofReal) hd.2.2, mul_one]

/-- **Pseudoperiodicity** (DLMF 28.12.6): `me_ν(z + π, q) = e^{πiν} me_ν(z, q)` for `ν ∉ ℤ`
(every `q`; at non-normal `q` both sides are junk values). -/
@[dlmf 28.12.E6]
theorem mathieuMe_add_pi {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (z q : ℂ) :
    mathieuMe ν (z + π) q = Complex.exp (π * I * ν) * mathieuMe ν z q := by
  rw [mathieuMe_of_not_int hν, mathieuMe_of_not_int hν, ← tsum_mul_left]
  congr 1; funext m
  have h : Complex.exp (I * (ν + 2 * m) * (z + π)) =
      Complex.exp (π * I * ν) * Complex.exp (I * (ν + 2 * m) * z) *
        Complex.exp (m * (2 * π * I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]; ring

/-- **Orthogonality** (DLMF 28.12.7):
`∫₀^π me_{ν+2m}(x, q) me_{ν+2n}(-x, q) dx = 0` for `m ≠ n`, `ν ∉ ℤ`, `q` normal along the
segment with respect to `ν + 2m` and `ν + 2n`. -/
@[dlmf 28.12.E7]
theorem integral_mathieuMe_orthogonal {ν q : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {m n : ℤ}
    (hmn : m ≠ n) (hm : MathieuNormalSegment (ν + 2 * m) q)
    (hn : MathieuNormalSegment (ν + 2 * n) q) :
    ∫ x in (0 : ℝ)..π, mathieuMe (ν + 2 * m) x q * mathieuMe (ν + 2 * n) (-x) q = 0 := by
  sorry

/-- **Change of sign of `ν`** (DLMF 28.12.8): `me_{-ν}(z, q) = me_ν(-z, q)` for `ν ∉ ℤ`. -/
@[dlmf 28.12.E8]
theorem mathieuMe_neg_nu {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (z q : ℂ) :
    mathieuMe (-ν) z q = mathieuMe ν (-z) q := by
  rw [mathieuMe_of_not_int (intCast_ne_neg_of_not_int hν), mathieuMe_of_not_int hν]
  simp only [mathieuMeCoeff_of_not_int (intCast_ne_neg_of_not_int hν), mathieuMeCoeff_of_not_int hν,
    mathieuLambdaData_neg_nu]
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1; funext m
  simp only [Equiv.neg_apply, neg_neg, Int.cast_neg]
  congr 2; ring

/-- **Floquet property** (DLMF §28.12(ii)): for `ν ∉ ℤ` and `q` normal along the segment,
`me_ν(z, q)` is a Floquet solution with respect to `ν` of Mathieu's equation with
`a = λ_ν(q)`; `me_ν(-z, q)` is a Floquet solution with respect to `-ν` with the same `a`. -/
@[dlmf 28.12.ii]
theorem isFloquetSolution_mathieuMe {ν q : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    (hq : MathieuNormalSegment ν q) :
    IsFloquetSolution (mathieuLambda ν q) q ν (fun z => mathieuMe ν z q) ∧
      IsFloquetSolution (mathieuLambda ν q) q (-ν) (fun z => mathieuMe ν (-z) q) := by
  have hd := isMeCoeffSeq_mathieuLambdaData hq
  set c := (mathieuLambdaData ν q).2
  have hme : ∀ z, mathieuMe ν z q = ∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * z) := by
    intro z; rw [mathieuMe_of_not_int hν]; simp only [mathieuMeCoeff_of_not_int hν, c]
  have hsol : IsMathieuSolution (mathieuLambda ν q) q (fun z => mathieuMe ν z q) := by
    rw [mathieuLambda_of_not_int hν]; simp only [hme]
    exact isMathieuSolution_tsum_exp_series hd.1 hd.2.1
  have hne : (fun z => mathieuMe ν z q) ≠ 0 := by
    intro h
    have h0 : ∀ z, mathieuMe ν z q = 0 := fun z => congrFun h z
    have := integral_mathieuMe_mul_neg hν hq
    simp only [h0, zero_mul, intervalIntegral.integral_zero] at this
    exact Real.pi_ne_zero (by exact_mod_cast this.symm)
  refine ⟨⟨hsol, hne, fun z => ?_⟩, ⟨?_, fun h => hne ?_, fun z => ?_⟩⟩
  · beta_reduce; rw [mathieuMe_add_pi hν]
  · have hrec' : ∀ m : ℤ, q * c (-(m + 1)) - ((mathieuLambdaData ν q).1 - (-ν + 2 * m) ^ 2) *
        c (-m) + q * c (-(m - 1)) = 0 := by
      intro m
      have := hd.1 (-m)
      rw [show -m + 1 = -(m - 1) by ring, show -m - 1 = -(m + 1) by ring] at this
      push_cast at this ⊢
      linear_combination this
    have hs' : Summable (fun m : ℤ => ‖c (-m)‖) := (Equiv.neg ℤ).summable_iff.mpr hd.2.1
    have := isMathieuSolution_tsum_exp_series (c := fun m => c (-m)) hrec' hs'
    rw [mathieuLambda_of_not_int hν]
    convert this using 2 with z
    rw [← mathieuMe_neg_nu hν, mathieuMe_of_not_int (intCast_ne_neg_of_not_int hν)]
    simp only [mathieuMeCoeff_of_not_int (intCast_ne_neg_of_not_int hν), mathieuLambdaData_neg_nu, c]
  · funext z
    have := congrFun h (-z)
    simpa using this
  · have h1 := mathieuMe_add_pi hν (-(z + π)) q
    rw [show -(z + π) + π = -z by ring] at h1
    beta_reduce
    rw [h1, ← mul_assoc, ← Complex.exp_add, show (π : ℂ) * I * -ν + π * I * ν = 0 by ring,
      Complex.exp_zero, one_mul]

/-- **Green's identity on a period**: solutions `f`, `g` of Mathieu's equation with eigenvalues
`a ≠ b` and reciprocal multipliers `f(z + π) = μ f(z)`, `g(z + π) = μ⁻¹ g(z)` satisfy
`∫₀^π f g = 0`. -/
private lemma integral_mul_eq_zero_of_pseudoperiodic {a b q μ : ℂ} {f g : ℂ → ℂ} (hf : IsMathieuSolution a q f)
    (hg : IsMathieuSolution b q g) (hμ : μ ≠ 0) (hfp : ∀ z, f (z + π) = μ * f z)
    (hgp : ∀ z, g (z + π) = μ⁻¹ * g z) (hab : a ≠ b) :
    ∫ x in (0 : ℝ)..π, f x * g x = 0 := by
  set h : ℂ → ℂ := fun z => deriv f z * g z - f z * deriv g z
  have hh : ∀ z : ℂ, HasDerivAt h ((b - a) * (f z * g z)) z := by
    intro z
    have := ((hf.hasDerivAt_deriv z).mul (hg.differentiable z).hasDerivAt).sub
      ((hf.differentiable z).hasDerivAt.mul (hg.hasDerivAt_deriv z))
    convert this using 1; ring
  have hint : ∫ x in (0 : ℝ)..π, (b - a) * (f x * g x) = h π - h 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => h x)
      (fun x _ => (hh x).comp_ofReal) ?_
    exact ((continuous_const.mul ((hf.differentiable.continuous.mul
      hg.differentiable.continuous))).comp Complex.continuous_ofReal).intervalIntegrable _ _
  have hdf : deriv f π = μ * deriv f 0 := by
    have e : (fun z => f (z + π)) = fun z => μ * f z := funext hfp
    have := deriv_comp_add_const (f := f) (a := (π : ℂ)) (x := 0)
    rw [e, zero_add] at this
    rw [← this]; exact ((hf.differentiable 0).hasDerivAt.const_mul μ).deriv
  have hdg : deriv g π = μ⁻¹ * deriv g 0 := by
    have e : (fun z => g (z + π)) = fun z => μ⁻¹ * g z := funext hgp
    have := deriv_comp_add_const (f := g) (a := (π : ℂ)) (x := 0)
    rw [e, zero_add] at this
    rw [← this]; exact ((hg.differentiable 0).hasDerivAt.const_mul μ⁻¹).deriv
  have hπ : h π = h 0 := by
    simp only [h, hdf, hdg]
    have f0 := hfp 0
    have g0 := hgp 0
    rw [zero_add] at f0 g0
    rw [f0, g0]
    field_simp
  rw [hπ, sub_self, intervalIntegral.integral_const_mul] at hint
  exact (mul_eq_zero.mp hint).resolve_left (sub_ne_zero.mpr hab.symm)

/-- **Orthogonality with distinct eigenvalues** (DLMF 28.12.7 under the extra hypothesis
`λ_{ν+2m}(q) ≠ λ_{ν+2n}(q)`; Green's identity on `[0, π]`). The statement
`integral_mathieuMe_orthogonal` without this hypothesis remains admitted. -/
private lemma integral_mathieuMe_orthogonal_of_mathieuLambda_ne {ν q : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    {m n : ℤ} (hm : MathieuNormalSegment (ν + 2 * m) q)
    (hn : MathieuNormalSegment (ν + 2 * n) q)
    (hne : mathieuLambda (ν + 2 * m) q ≠ mathieuLambda (ν + 2 * n) q) :
    ∫ x in (0 : ℝ)..π, mathieuMe (ν + 2 * m) x q * mathieuMe (ν + 2 * n) (-x) q = 0 := by
  obtain ⟨⟨h1, -, hp1⟩, -⟩ := isFloquetSolution_mathieuMe (intCast_ne_add_two_mul_of_not_int hν m) hm
  obtain ⟨-, ⟨h2, -, hp2⟩⟩ := isFloquetSolution_mathieuMe (intCast_ne_add_two_mul_of_not_int hν n) hn
  refine integral_mul_eq_zero_of_pseudoperiodic h1 h2 (Complex.exp_ne_zero _) hp1 (fun z => ?_) hne
  have h2z := hp2 z
  simp only at h2z
  rw [h2z, ← Complex.exp_neg]
  congr 1
  have e : Complex.exp (π * I * -(ν + 2 * n)) = Complex.exp (-(π * I * (ν + 2 * m))) := by
    rw [show (π : ℂ) * I * -(ν + 2 * n) = -(π * I * (ν + 2 * m)) + (m - n : ℤ) * (2 * π * I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  exact e

/-- A Floquet solution with respect to `ν ∉ ℤ` whose reflection `w(-z)` is a Floquet solution
with respect to `-ν` does not vanish at `0`, and `cos πν = w_I(π)`. -/
theorem isMathieuCharExp_of_isFloquetSolution_pair {a q ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {w : ℂ → ℂ}
    (h1 : IsFloquetSolution a q ν w) (h2 : IsFloquetSolution a q (-ν) (fun z => w (-z))) :
    w 0 ≠ 0 ∧ IsMathieuCharExp a q ν := by
  obtain ⟨hw, hw0, hper⟩ := h1
  obtain ⟨hw', -, hper'⟩ := h2
  set μ : ℂ := Complex.exp (π * I * ν)
  have hμ : μ ≠ 0 := Complex.exp_ne_zero _
  have hμ' : Complex.exp (π * I * -ν) = μ⁻¹ := by
    rw [show (π : ℂ) * I * -ν = -(π * I * ν) by ring, Complex.exp_neg]
  have hdneg : ∀ z, deriv (fun z => w (-z)) z = -deriv w (-z) := fun z => deriv_comp_neg w z
  have hdW : ∀ z, HasDerivAt w (deriv w z) z := fun z => (hw.differentiable z).hasDerivAt
  have hdW' : ∀ z, HasDerivAt (fun z => w (-z)) (-deriv w (-z)) z := fun z => by
    rw [← hdneg]; exact (hw'.differentiable z).hasDerivAt
  have h0 : w 0 ≠ 0 := by
    intro h0
    have hg : IsMathieuSolution a q (fun z => -1 * w (-z)) := hw'.const_mul (-1)
    have hdg : deriv (fun z => -1 * w (-z)) 0 = deriv w 0 := by
      rw [((hdW' 0).const_mul (-1)).deriv]; simp
    have hodd := hw.eq_of_initial hg (z₀ := 0) (by simp [h0]) hdg.symm
    have hμμ : ∀ z, μ * w z = μ⁻¹ * w z := by
      intro z
      have e1 := hper z
      have e2 := hper' z
      rw [hμ'] at e2
      have o1 := congrFun hodd (z + π)
      have o2 := congrFun hodd z
      simp only at o1 o2 e2
      linear_combination -e1 + o1 - e2 - μ⁻¹ * o2
    obtain ⟨z, hz⟩ : ∃ z, w z ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hw0 (funext hcon)
    have hμ2 : μ = μ⁻¹ := mul_right_cancel₀ hz (hμμ z)
    have hexp : Complex.exp (2 * π * I * ν) = 1 := by
      have : μ * μ = 1 := by nth_rewrite 1 [hμ2]; exact inv_mul_cancel₀ hμ
      rw [← this, ← Complex.exp_add]; congr 1; ring
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
    refine hν n ?_
    have hπ : (2 * π * I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ hπ
    linear_combination -hn
  refine ⟨h0, ?_⟩
  set W : ℂ → ℂ := fun z => (1 / (2 * w 0)) * (w z + w (-z))
  have hWs : IsMathieuSolution a q W := (hw.add hw').const_mul _
  have hW0 : W 0 = 1 := by
    simp only [W, neg_zero]; field_simp; ring
  have hWd : deriv W 0 = 0 := by
    have hd : HasDerivAt W (1 / (2 * w 0) * (deriv w 0 + -deriv w (-0))) 0 :=
      ((hdW 0).add (hdW' 0)).const_mul _
    rw [hd.deriv]; simp
  have hex : ∃ v, IsMathieuSolution a q v ∧ v 0 = 1 ∧ deriv v 0 = 0 := ⟨W, hWs, hW0, hWd⟩
  have hspec : IsMathieuSolution a q (mathieuWI a q) ∧ mathieuWI a q 0 = 1 ∧
      deriv (mathieuWI a q) 0 = 0 := by
    simp only [mathieuWI, hex, ↓reduceDIte]; exact hex.choose_spec
  have hWI : mathieuWI a q = W :=
    hspec.1.eq_of_initial hWs (z₀ := 0) (by rw [hspec.2.1, hW0]) (by rw [hspec.2.2, hWd])
  have e1 := hper 0
  have e2 := hper' 0
  rw [hμ'] at e2
  simp only [zero_add, neg_zero] at e1 e2
  rw [IsMathieuCharExp, hWI]
  simp only [W, e1, e2, Complex.cos]
  have : Complex.exp (-(π * ν) * I) = μ⁻¹ := by
    rw [← Complex.exp_neg]; congr 1; ring
  rw [this, show (π : ℂ) * ν * I = π * I * ν by ring]
  field_simp
  ring

/-- **Characterization of `λ_ν(q)`** (DLMF §28.12(i)): for `ν ∉ ℤ` and `q` normal along the
segment, `a = λ_ν(q)` is a root of the characteristic equation 28.2.16,
`cos(πν) = w_I(π; a, q)`. -/
@[dlmf 28.12.i]
theorem isMathieuCharExp_mathieuLambda {ν q : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    (hq : MathieuNormalSegment ν q) : IsMathieuCharExp (mathieuLambda ν q) q ν :=
  (isMathieuCharExp_of_isFloquetSolution_pair hν (isFloquetSolution_mathieuMe hν hq).1
    (isFloquetSolution_mathieuMe hν hq).2).2

/-- **Change of sign of `q`** (DLMF 28.12.9): `me_ν(z, -q) = e^{iνπ/2} me_ν(z - π/2, q)` for
`ν ∉ ℤ`. -/
@[dlmf 28.12.E9]
theorem mathieuMe_neg_q {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (z q : ℂ) :
    mathieuMe ν z (-q) = Complex.exp (I * ν * π / 2) * mathieuMe ν (z - π / 2) q := by
  rw [mathieuMe_of_not_int hν, mathieuMe_of_not_int hν, ← tsum_mul_left]
  simp only [mathieuMeCoeff_of_not_int hν, mathieuLambdaData_neg_q]
  congr 1; funext m
  have h : Complex.exp (I * ν * π / 2) * Complex.exp (I * (ν + 2 * m) * (z - π / 2)) =
      Complex.exp (m * (-(π * I))) * Complex.exp (I * (ν + 2 * m) * z) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  rw [mul_left_comm, h, Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  simp only [inv_neg, inv_one]
  ring

/-- **Complex conjugation** (DLMF 28.12.10): `conj (me_ν(z, q)) = me_{conj ν}(-conj z, conj q)`
for `ν ∉ ℤ`. Stronger than DLMF: with the straight-segment continuation it holds for all `q`
(DLMF excepts cuts on the real `q`-axis for special complex `ν`). -/
@[dlmf 28.12.E10]
theorem conj_mathieuMe {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (z q : ℂ) :
    conj (mathieuMe ν z q) = mathieuMe (conj ν) (-conj z) (conj q) := by
  rw [mathieuMe_of_not_int hν, mathieuMe_of_not_int (intCast_ne_conj_of_not_int hν), Complex.conj_tsum]
  simp only [mathieuMeCoeff_of_not_int hν, mathieuMeCoeff_of_not_int (intCast_ne_conj_of_not_int hν),
    mathieuLambdaData_conj]
  congr 1; funext m
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_add, Complex.conj_I, map_ofNat, map_intCast]
  ring

/-- **Integer order** (DLMF 28.12.11): `me_n(z, q) = √2 ce_n(z, q)` for `n = 0, 1, 2, …`
(real `q`). -/
@[dlmf 28.12.E11]
theorem mathieuMe_natCast (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuMe n z q = (Real.sqrt 2 : ℂ) * mathieuCe n z q := by
  have := mathieuMe_intCast (n : ℤ) z q
  push_cast at this
  rw [this]; simp [mathieuMeInt]

/-- **Integer order** (DLMF 28.12.11): `me_{-n}(z, q) = -√2 i se_n(z, q)` for `n = 1, 2, …`
(real `q`). -/
@[dlmf 28.12.E11]
theorem mathieuMe_neg_natCast {n : ℕ} (hn : n ≠ 0) (z : ℂ) (q : ℝ) :
    mathieuMe (-(n : ℂ)) z q = -((Real.sqrt 2 : ℂ) * I) * mathieuSe n z q := by
  have := mathieuMe_intCast (-(n : ℤ)) z q
  push_cast at this
  have h0 : ¬ (0 : ℤ) ≤ -(n : ℤ) := by omega
  rw [this, mathieuMeInt]
  simp only [h0, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]

/-! ### §28.12(iii) The functions `ce_ν`, `se_ν` -/

/-- **Reality** (DLMF §28.12(iii)): for real `ν ∉ ℤ`, real `q` and real `x`, `me_ν(-x, q)` is
the complex conjugate of `me_ν(x, q)`, so `ce_ν(x, q)` and `se_ν(x, q)` are real. -/
@[dlmf 28.12.iii]
theorem mathieuCeNu_mathieuSeNu_real {ν q x : ℝ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) :
    (mathieuCeNu ν x q).im = 0 ∧ (mathieuSeNu ν x q).im = 0 := by
  have h := conj_mathieuMe hν (x : ℂ) (q : ℂ)
  simp only [Complex.conj_ofReal] at h
  have hre : ∀ w : ℂ, (w + conj w).im = 0 := fun w => by simp
  have him : ∀ w : ℂ, (-(I / 2) * (w - conj w)).im = 0 := fun w => by
    simp [Complex.mul_im, Complex.sub_re, Complex.sub_im]
  constructor
  · simp only [mathieuCeNu, ← h, Complex.div_ofNat_im, hre, zero_div]
  · simp only [mathieuSeNu, ← h, him]

/-- Iterated pseudoperiodicity: `w(z + nπ) = μⁿ w(z)`. -/
theorem pseudoperiodic_add_nat_mul_pi {w : ℂ → ℂ} {μ : ℂ} (h : ∀ z, w (z + π) = μ * w z) (z : ℂ)
    (n : ℕ) : w (z + n * π) = μ ^ n * w z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show z + ((n + 1 : ℕ) : ℂ) * π = (z + n * π) + π by push_cast; ring, h, ih]; ring

/-- For `ν ∉ ℤ` the Floquet multipliers `e^{±iπν}` are distinct. -/
theorem exp_pi_mul_I_mul_ne_inv {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) :
    Complex.exp (π * I * ν) ≠ (Complex.exp (π * I * ν))⁻¹ := by
  intro hμ2
  have hμ : Complex.exp (π * I * ν) ≠ 0 := Complex.exp_ne_zero _
  have hexp : Complex.exp (2 * π * I * ν) = 1 := by
    have : Complex.exp (π * I * ν) * Complex.exp (π * I * ν) = 1 := by
      nth_rewrite 1 [hμ2]; exact inv_mul_cancel₀ hμ
    rw [← this, ← Complex.exp_add]; congr 1; ring
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  refine hν n ?_
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  apply mul_left_cancel₀ hπ
  linear_combination -hn

/-- A Floquet solution with respect to `ν` with `e^{2πimν} = 1` has period `2mπ`. -/
private lemma periodic_of_isFloquetSolution {a q ν : ℂ} {w : ℂ → ℂ} (hw : IsFloquetSolution a q ν w) {m : ℕ}
    (hm : Complex.exp (2 * m * π * I * ν) = 1) : Function.Periodic w (2 * m * π) := by
  intro z
  have := pseudoperiodic_add_nat_mul_pi hw.2.2 z (2 * m)
  push_cast at this
  rw [this, ← Complex.exp_nat_mul]
  push_cast
  rw [show (2 * m : ℂ) * (π * I * ν) = 2 * m * π * I * ν by ring, hm, one_mul]

/-- **Rational order** (DLMF §28.12(iii)): when `ν = s/m` is rational but not an integer, all
solutions of Mathieu's equation with characteristic exponent `ν` are periodic with period
`2mπ`. -/
@[dlmf 28.12.iii]
theorem mathieu_periodic_of_rational {a q : ℂ} {s : ℤ} {m : ℕ} (hm : m ≠ 0)
    (hν : ∀ k : ℤ, (k : ℂ) ≠ s / m) (hc : IsMathieuCharExp a q (s / m)) {w : ℂ → ℂ}
    (hw : IsMathieuSolution a q w) : Function.Periodic w (2 * m * π) := by
  set ν : ℂ := s / m
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have h1 : Complex.exp (2 * m * π * I * ν) = 1 := by
    rw [show (2 * m * π * I * ν : ℂ) = s * (2 * π * I) by simp only [ν]; field_simp,
      Complex.exp_int_mul_two_pi_mul_I]
  have h2 : Complex.exp (2 * m * π * I * -ν) = 1 := by
    rw [show (2 * m * π * I * -ν : ℂ) = (-s : ℤ) * (2 * π * I) by
      simp only [ν]; push_cast; field_simp, Complex.exp_int_mul_two_pi_mul_I]
  have hc' : IsMathieuCharExp a q (-ν) := by
    rw [IsMathieuCharExp, mul_neg, Complex.cos_neg]; exact hc
  by_cases hw0 : w = 0
  · intro z; simp [hw0]
  rcases hw.isFloquet_or hw0 hc with h | hu
  · exact periodic_of_isFloquetSolution h h1
  rcases hw.isFloquet_or hw0 hc' with h | hu'
  · exact periodic_of_isFloquetSolution h h2
  have pu := periodic_of_isFloquetSolution hu h2
  have pu' := periodic_of_isFloquetSolution hu' (by rw [neg_neg]; exact h1)
  have hD : Complex.exp (I * ν * π) - Complex.exp (I * -ν * π) ≠ 0 := by
    have := exp_pi_mul_I_mul_ne_inv (ν := ν) hν
    rw [sub_ne_zero, show I * -ν * π = -(π * I * ν) by ring, Complex.exp_neg,
      show I * ν * π = π * I * ν by ring]
    exact this
  have hrep : ∀ z, w z = ((w (z + π) - Complex.exp (I * -ν * π) * w z) -
      (w (z + π) - Complex.exp (I * ν * π) * w z)) /
      (Complex.exp (I * ν * π) - Complex.exp (I * -ν * π)) := by
    intro z; rw [eq_div_iff hD]; ring
  intro z
  rw [hrep (z + 2 * m * π), hrep z]
  have e1 := pu z
  have e2 := pu' z
  simp only at e1 e2
  rw [e1, e2]

/-- **Change of sign of `z` and `ν`** (DLMF 28.12.14): `ce_ν(z, q) = ce_ν(-z, q) = ce_{-ν}(z, q)`
for `ν ∉ ℤ`. -/
@[dlmf 28.12.E14]
theorem mathieuCeNu_neg {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (z q : ℂ) :
    mathieuCeNu ν z q = mathieuCeNu ν (-z) q ∧ mathieuCeNu ν z q = mathieuCeNu (-ν) z q := by
  refine ⟨by simp only [mathieuCeNu, neg_neg]; ring, ?_⟩
  simp only [mathieuCeNu, mathieuMe_neg_nu hν, neg_neg]; ring

/-- **Change of sign of `z` and `ν`** (DLMF 28.12.15):
`se_ν(z, q) = -se_ν(-z, q) = -se_{-ν}(z, q)` for `ν ∉ ℤ`. -/
@[dlmf 28.12.E15]
theorem mathieuSeNu_neg {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (z q : ℂ) :
    mathieuSeNu ν z q = -mathieuSeNu ν (-z) q ∧ mathieuSeNu ν z q = -mathieuSeNu (-ν) z q := by
  refine ⟨by simp only [mathieuSeNu, neg_neg]; ring, ?_⟩
  simp only [mathieuSeNu, mathieuMe_neg_nu hν, neg_neg]; ring

/-! ### Normality of real parameters (DLMF §28.12(i)) -/

/-- At `q = 0` and `a = ν²` an admissible coefficient sequence is `c₀ δ₀` with `c₀² = 1`. -/
private lemma isMeCoeffSeq_zero_q {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {c : ℤ → ℂ}
    (h : IsMeCoeffSeq ν 0 (ν ^ 2) c) : c = Pi.single 0 (c 0) ∧ c 0 ^ 2 = 1 := by
  have hcm : ∀ m : ℤ, m ≠ 0 → c m = 0 := by
    intro m hm
    have := h.1 m
    simp only [zero_mul, zero_sub, add_zero, neg_eq_zero] at this
    exact (mul_eq_zero.mp this).resolve_left (sq_sub_add_two_mul_sq_ne_zero hν hm)
  refine ⟨funext fun m => ?_, ?_⟩
  · by_cases hm : m = 0
    · subst hm; simp
    · simp [hm, hcm m hm]
  · have h2 := hasSum_single (f := fun m : ℤ => c m ^ 2) (0 : ℤ) fun m hm => by simp [hcm m hm]
    exact h2.unique h.2.2

/-- The coefficients of an absolutely convergent series `∑ c_m e^{i(ν+2m)x}` are determined by
its values on `ℝ`. -/
private lemma eq_of_tsum_exp_series_eq {ν : ℂ} {c d : ℤ → ℂ} (hc : Summable fun m => ‖c m‖)
    (hd : Summable fun m => ‖d m‖)
    (h : ∀ x : ℝ, ∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * x) =
      ∑' m : ℤ, d m * Complex.exp (I * (ν + 2 * m) * x)) : c = d := by
  funext n
  have h1 := integral_tsum_exp_series_mul_exp (ν := ν) hc n
  have h2 := integral_tsum_exp_series_mul_exp (ν := ν) hd n
  simp only [h] at h1
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact mul_left_cancel₀ hπ (h1.symm.trans h2)

/-- The series of an admissible coefficient sequence is a Floquet solution. -/
private lemma isFloquetSolution_tsum_of_isMeCoeffSeq {ν q a : ℂ} {c : ℤ → ℂ}
    (h : IsMeCoeffSeq ν q a c) :
    IsFloquetSolution a q ν (fun z => ∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * z)) := by
  refine ⟨isMathieuSolution_tsum_exp_series h.1 h.2.1, fun h0 => ?_, fun z => ?_⟩
  · have hc : c = 0 := by
      refine eq_of_tsum_exp_series_eq (ν := ν) h.2.1 (by simp) fun x => ?_
      simpa using congrFun h0 (x : ℂ)
    have : HasSum (fun m => c m ^ 2) 0 := by simp [hc]
    exact one_ne_zero (this.unique h.2.2).symm
  · beta_reduce
    rw [← tsum_mul_left]
    congr 1; funext m
    have e : Complex.exp (I * (ν + 2 * m) * (z + π)) =
        Complex.exp (π * I * ν) * Complex.exp (I * (ν + 2 * m) * z) *
          Complex.exp (m * (2 * π * I)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I]; ring

/-- The explicit Floquet solution along a real root path `Λ`. -/
private def realW (ν q : ℝ) (Λ : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  mathieuWII (Λ t) ((t * q : ℝ) : ℂ) π * mathieuWI (Λ t) ((t * q : ℝ) : ℂ) z +
    (Complex.exp (π * I * ν) - mathieuWI (Λ t) ((t * q : ℝ) : ℂ) π) *
      mathieuWII (Λ t) ((t * q : ℝ) : ℂ) z

/-- Its Fourier coefficients. -/
private def realCoeff (ν q : ℝ) (Λ : ℝ → ℝ) (t : ℝ) (n : ℤ) : ℂ :=
  (π : ℂ)⁻¹ * ∫ x in (0 : ℝ)..π, realW ν q Λ t x * Complex.exp (-(I * (ν + 2 * n) * x))

section RealPath

variable {ν q : ℝ} {Λ : ℝ → ℝ}

private lemma realW_charExp (hΛ : ∀ t, (mathieuWI (Λ t) ((t * q : ℝ) : ℂ) π).re = Real.cos (π * ν))
    (t : ℝ) : IsMathieuCharExp (Λ t) ((t * q : ℝ) : ℂ) ν := by
  have hr := Complex.conj_eq_iff_re.mp (conj_mathieuWI_ofReal (Λ t) (t * q) π)
  unfold IsMathieuCharExp
  rw [← hr, hΛ t, Complex.ofReal_cos]
  push_cast; ring_nf

private lemma realW_floquet (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    (hΛ : ∀ t, (mathieuWI (Λ t) ((t * q : ℝ) : ℂ) π).re = Real.cos (π * ν)) (t : ℝ) :
    IsFloquetSolution (Λ t) ((t * q : ℝ) : ℂ) ν (realW ν q Λ t) :=
  isFloquetSolution_mathieuWII_pi_mul_add (exp_pi_mul_I_mul_ne_inv hν) (realW_charExp hΛ t)

private lemma realCoeff_fourier (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    (hΛ : ∀ t, (mathieuWI (Λ t) ((t * q : ℝ) : ℂ) π).re = Real.cos (π * ν)) (t : ℝ) :
    Summable (fun n => ‖realCoeff ν q Λ t n‖) ∧
      (∀ z, HasSum (fun n => realCoeff ν q Λ t n * Complex.exp (I * (ν + 2 * n) * z))
        (realW ν q Λ t z)) ∧
      ∀ n : ℤ, ((t * q : ℝ) : ℂ) * realCoeff ν q Λ t (n + 1) -
        ((Λ t : ℂ) - (ν + 2 * n) ^ 2) * realCoeff ν q Λ t n +
          ((t * q : ℝ) : ℂ) * realCoeff ν q Λ t (n - 1) = 0 := by
  obtain ⟨c, hsum, hhas, hrec⟩ := (realW_floquet hν hΛ t).exists_fourier
  have hs0 : Summable (fun n => ‖c n‖) := by simpa using hsum 0
  have hc : c = realCoeff ν q Λ t := by
    funext n
    have h := integral_tsum_exp_series_mul_exp (ν := ν) hs0 n
    simp only [fun x : ℝ => (hhas x).tsum_eq] at h
    unfold realCoeff
    rw [h]
    field_simp [show (π : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero]
  subst hc
  exact ⟨hs0, hhas, hrec⟩

private lemma realW_neg (hΛ : ∀ t, (mathieuWI (Λ t) ((t * q : ℝ) : ℂ) π).re = Real.cos (π * ν))
    (t x : ℝ) : realW ν q Λ t (-(x : ℂ)) = conj (realW ν q Λ t x) := by
  have hc := realW_charExp hΛ t
  unfold IsMathieuCharExp at hc
  unfold realW
  rw [mathieuWI_neg, mathieuWII_neg]
  simp only [map_add, map_mul, map_sub, conj_mathieuWI_ofReal, conj_mathieuWII_ofReal,
    ← Complex.exp_conj]
  simp only [Complex.conj_ofReal, Complex.conj_I]
  have hcos : 2 * mathieuWI (Λ t) ((t * q : ℝ) : ℂ) π =
      Complex.exp (π * I * ν) + Complex.exp (π * -I * ν) := by
    rw [← hc, Complex.cos]
    rw [show (π : ℂ) * ν * I = π * I * ν by ring, show -((π : ℂ) * ν) * I = π * -I * ν by ring]
    ring
  linear_combination (mathieuWII (Λ t) ((t * q : ℝ) : ℂ) x) * hcos

private lemma conj_realCoeff (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    (hΛ : ∀ t, (mathieuWI (Λ t) ((t * q : ℝ) : ℂ) π).re = Real.cos (π * ν)) (t : ℝ) (n : ℤ) :
    conj (realCoeff ν q Λ t n) = realCoeff ν q Λ t n := by
  obtain ⟨hs, hhas, -⟩ := realCoeff_fourier hν hΛ t
  have hd : Summable (fun m => ‖conj (realCoeff ν q Λ t m)‖) := by simp [hs]
  have key := eq_of_tsum_exp_series_eq (ν := ν) hd hs fun x => ?_
  · exact congrFun key n
  · have e : ∀ m : ℤ, conj (realCoeff ν q Λ t m) * Complex.exp (I * (ν + 2 * m) * x) =
        conj (realCoeff ν q Λ t m * Complex.exp (I * (ν + 2 * m) * -(x : ℂ))) := by
      intro m
      rw [map_mul, ← Complex.exp_conj]
      congr 2
      simp only [map_mul, map_add, map_neg, Complex.conj_I, Complex.conj_ofReal, map_intCast,
        map_ofNat]
      ring
    simp only [e]
    rw [← Complex.conj_tsum, (hhas _).tsum_eq, (hhas _).tsum_eq, realW_neg hΛ, Complex.conj_conj]


/-- The sum of squares of the coefficients, as an integral. -/
private def realNorm (ν q : ℝ) (Λ : ℝ → ℝ) (t : ℝ) : ℂ :=
  (π : ℂ)⁻¹ * ∫ x in (0 : ℝ)..π, realW ν q Λ t x * realW ν q Λ t (-(x : ℂ))

private lemma summable_sq_of_summable_norm {c : ℤ → ℂ} (hs : Summable (fun n => ‖c n‖)) :
    Summable (fun n => ‖c n‖ ^ 2) := by
  have hB : ∀ m, ‖c m‖ ≤ ∑' m, ‖c m‖ := fun m => hs.le_tsum m (fun j _ => norm_nonneg _)
  exact Summable.of_nonneg_of_le (fun m => by positivity)
    (fun m => by rw [sq]; exact mul_le_mul_of_nonneg_right (hB m) (norm_nonneg _))
    (hs.mul_left _)

private lemma hasSum_realCoeff_sq (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    (hΛ : ∀ t, (mathieuWI (Λ t) ((t * q : ℝ) : ℂ) π).re = Real.cos (π * ν)) (t : ℝ) :
    HasSum (fun n => realCoeff ν q Λ t n ^ 2) (realNorm ν q Λ t) := by
  obtain ⟨hs, hhas, -⟩ := realCoeff_fourier hν hΛ t
  have hs2 : Summable (fun n => realCoeff ν q Λ t n ^ 2) :=
    Summable.of_norm (by simpa [norm_pow] using summable_sq_of_summable_norm hs)
  have hW := (realW_floquet hν hΛ t).1
  have hcont : Continuous (fun x : ℝ =>
      ∑' m : ℤ, realCoeff ν q Λ t m * Complex.exp (I * (ν + 2 * m) * x)) := by
    simp only [fun x : ℝ => (hhas x).tsum_eq]
    exact hW.differentiable.continuous.comp Complex.continuous_ofReal
  have h := integral_tsum_exp_series_mul_neg hs hcont hs2.hasSum
  simp only [fun x : ℝ => (hhas x).tsum_eq, fun x : ℝ => (hhas (-(x : ℂ))).tsum_eq] at h
  unfold realNorm
  rw [h, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Real.pi_ne_zero), one_mul]
  exact hs2.hasSum

/-- The real sum of squares. -/
private def realNormRe (ν q : ℝ) (Λ : ℝ → ℝ) (t : ℝ) : ℝ := (realNorm ν q Λ t).re

private lemma realNorm_eq (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    (hΛ : ∀ t, (mathieuWI (Λ t) ((t * q : ℝ) : ℂ) π).re = Real.cos (π * ν)) (t : ℝ) :
    realNorm ν q Λ t = (realNormRe ν q Λ t : ℂ) ∧ 0 < realNormRe ν q Λ t := by
  obtain ⟨hs, hhas, -⟩ := realCoeff_fourier hν hΛ t
  have hre : ∀ n, realCoeff ν q Λ t n = ((realCoeff ν q Λ t n).re : ℂ) := fun n =>
    (Complex.conj_eq_iff_re.mp (conj_realCoeff hν hΛ t n)).symm
  have hs2 : Summable (fun n => (realCoeff ν q Λ t n).re ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
      (summable_sq_of_summable_norm hs)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
  have hh : HasSum (fun n => realCoeff ν q Λ t n ^ 2)
      ((∑' n, (realCoeff ν q Λ t n).re ^ 2 : ℝ) : ℂ) := by
    have := (Complex.hasSum_ofReal.mpr hs2.hasSum)
    refine this.congr_fun fun n => ?_
    rw [hre n]; push_cast; simp
  have he := (hasSum_realCoeff_sq hν hΛ t).unique hh
  have hval : realNorm ν q Λ t = (realNormRe ν q Λ t : ℂ) := by
    unfold realNormRe; rw [he]; simp
  refine ⟨hval, ?_⟩
  have hne : ∃ n, realCoeff ν q Λ t n ≠ 0 := by
    by_contra h
    push Not at h
    apply (realW_floquet hν hΛ t).2.1
    funext z
    have := (hhas z).tsum_eq
    simp only [h, zero_mul, tsum_zero] at this
    exact this.symm
  obtain ⟨n, hn⟩ := hne
  have hn' : (realCoeff ν q Λ t n).re ≠ 0 := by
    intro h0; apply hn; rw [hre n, h0]; simp
  unfold realNormRe
  rw [he, Complex.ofReal_re]
  exact hs2.tsum_pos (fun _ => sq_nonneg _) n (by positivity)

private lemma continuous_realW (hΛc : Continuous Λ) :
    Continuous (fun p : ℝ × ℂ => realW ν q Λ p.1 p.2) := by
  have h1 := differentiable_mathieuWI_mathieuWII.1.continuous
  have h2 := differentiable_mathieuWI_mathieuWII.2.continuous
  have hp : Continuous (fun p : ℝ × ℂ => (p.2, ((Λ p.1 : ℝ) : ℂ), ((p.1 * q : ℝ) : ℂ))) := by
    fun_prop
  have hπ : Continuous (fun p : ℝ × ℂ => ((π : ℂ), ((Λ p.1 : ℝ) : ℂ), ((p.1 * q : ℝ) : ℂ))) := by
    fun_prop
  unfold realW
  exact ((h2.comp hπ).mul (h1.comp hp)).add
    ((continuous_const.sub (h1.comp hπ)).mul (h2.comp hp))

private lemma continuous_realCoeff (hΛc : Continuous Λ) (n : ℤ) :
    Continuous (fun t => realCoeff ν q Λ t n) := by
  unfold realCoeff
  refine continuous_const.mul ?_
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((continuous_realW hΛc).comp (by fun_prop :
    Continuous (fun p : ℝ × ℝ => (p.1, (p.2 : ℂ))))).mul (by fun_prop)

private lemma continuous_realNormRe (hΛc : Continuous Λ) :
    Continuous (realNormRe ν q Λ) := by
  unfold realNormRe realNorm
  refine Complex.continuous_re.comp (continuous_const.mul ?_)
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((continuous_realW hΛc).comp (by fun_prop :
    Continuous (fun p : ℝ × ℝ => (p.1, (p.2 : ℂ))))).mul
    ((continuous_realW hΛc).comp (by fun_prop :
    Continuous (fun p : ℝ × ℝ => (p.1, -(p.2 : ℂ)))))

/-- The normalized coefficients. -/
private def realNormCoeff (ν q : ℝ) (Λ : ℝ → ℝ) (t : ℝ) (n : ℤ) : ℂ :=
  realCoeff ν q Λ t n / (Real.sqrt (realNormRe ν q Λ t) : ℂ)

private lemma isMeCoeffSeq_realNormCoeff (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    (hΛ : ∀ t, (mathieuWI (Λ t) ((t * q : ℝ) : ℂ) π).re = Real.cos (π * ν)) (t : ℝ) :
    IsMeCoeffSeq ν ((t * q : ℝ) : ℂ) (Λ t) (realNormCoeff ν q Λ t) := by
  obtain ⟨hs, -, hrec⟩ := realCoeff_fourier hν hΛ t
  obtain ⟨hN, hpos⟩ := realNorm_eq hν hΛ t
  have hsq : (Real.sqrt (realNormRe ν q Λ t) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  refine ⟨fun m => ?_, ?_, ?_⟩
  · unfold realNormCoeff
    field_simp
    linear_combination hrec m
  · unfold realNormCoeff
    simpa [norm_div] using hs.div_const ‖(Real.sqrt (realNormRe ν q Λ t) : ℂ)‖
  · have h := (hasSum_realCoeff_sq hν hΛ t).div_const (realNormRe ν q Λ t : ℂ)
    rw [hN, div_self (by exact_mod_cast hpos.ne')] at h
    refine h.congr_fun fun n => ?_
    unfold realNormCoeff
    rw [div_pow, ← Complex.ofReal_pow, Real.sq_sqrt hpos.le]

private lemma continuous_realNormCoeff (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    (hΛ : ∀ t, (mathieuWI (Λ t) ((t * q : ℝ) : ℂ) π).re = Real.cos (π * ν))
    (hΛc : Continuous Λ) (n : ℤ) : Continuous (fun t => realNormCoeff ν q Λ t n) := by
  unfold realNormCoeff
  refine (continuous_realCoeff hΛc n).div
    (Complex.continuous_ofReal.comp (continuous_realNormRe hΛc).sqrt) fun t => ?_
  exact_mod_cast (Real.sqrt_pos.mpr (realNorm_eq hν hΛ t).2).ne'

end RealPath

/-- **Real parameters are normal** (DLMF §28.12(i)): for real `ν ∉ ℤ` and real `q` all the
`λ_ν(q)` are real and `q` is normal (along the whole segment `[0, q]`). The root
`λ_ν(tq)` of `cos πν = w_I(π; a, tq)` is continued along `t ∈ [0, 1]`
(`exists_continuous_re_mathieuWI_pi_eq`), the coefficients are the normalized Fourier
coefficients of the explicit Floquet solution `isFloquetSolution_mathieuWII_pi_mul_add`, and
uniqueness follows from the reality of the eigenvalues (`im_eq_zero_of_isMeCoeffSeq`), the
uniqueness of root paths (`eqOn_of_re_mathieuWI_pi_eq`), Ince's theorem
(`IsFloquetSolution.unique`) and the connectedness of `[0, 1]`. -/
@[dlmf 28.12.i]
theorem mathieuNormalSegment_real {ν q : ℝ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) :
    MathieuNormalSegment ν q ∧ (mathieuLambda ν q).im = 0 := by
  by_cases hq : q = 0
  · subst hq
    simp only [Complex.ofReal_zero]
    refine ⟨mathieuNormalSegment_zero hν, ?_⟩
    rw [mathieuLambda_zero hν, ← Complex.ofReal_pow, Complex.ofReal_im]
  have hc := abs_cos_pi_mul_lt_one hν
  have h0 : (mathieuWI ((ν ^ 2 : ℝ) : ℂ) 0 π).re = Real.cos (π * ν) := by
    have hF := (isFloquetSolution_mathieuMe hν (mathieuNormalSegment_zero hν)).1
    rw [mathieuLambda_zero hν] at hF
    have hch := (exists_isFloquetSolution_iff_charExp _ _ _).mp ⟨_, hF⟩
    unfold IsMathieuCharExp at hch
    rw [Complex.ofReal_pow, ← hch, ← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.ofReal_re]
  obtain ⟨Λ, hΛc, hΛ0, hΛ⟩ := exists_continuous_re_mathieuWI_pi_eq (q := q) hc h0
  set nc := realNormCoeff ν q Λ with hncdef
  have hnc := isMeCoeffSeq_realNormCoeff hν hΛ
  have hnc0 : IsMeCoeffSeq ν 0 ((ν : ℂ) ^ 2) (nc 0) := by
    have := hnc 0
    rwa [zero_mul, Complex.ofReal_zero, hΛ0, Complex.ofReal_pow] at this
  obtain ⟨-, hε2⟩ := isMeCoeffSeq_zero_q hν hnc0
  set ε := nc 0 0 with hεdef
  set cp : ℝ → ℤ → ℂ := fun t n => ε * nc t n with hcpdef
  have hcp : ∀ t, IsMeCoeffSeq ν ((t * q : ℝ) : ℂ) (Λ t) (cp t) := by
    intro t
    obtain ⟨hr, hs, hsq⟩ := hnc t
    refine ⟨fun m => by simp only [cp]; linear_combination ε * hr m, ?_, ?_⟩
    · simpa [cp, norm_mul] using hs.mul_left ‖ε‖
    · have := hsq.mul_left (ε ^ 2)
      rw [show ε ^ 2 * 1 = 1 by rw [hε2, one_mul]] at this
      refine this.congr_fun fun n => ?_
      simp only [cp]; ring
  have hcpc : ∀ m, Continuous (fun t => cp t m) := fun m =>
    continuous_const.mul (continuous_realNormCoeff hν hΛ hΛc m)
  have hcp00 : cp 0 0 = 1 := by simp only [cp]; rw [← sq]; exact hε2
  have hpath : IsMathieuLambdaPath ν q (fun t => (Λ t : ℂ)) cp := by
    refine ⟨(Complex.continuous_ofReal.comp hΛc).continuousOn, fun m => (hcpc m).continuousOn,
      ?_, hcp00, fun t _ => ?_⟩
    · simp [hΛ0]
    · have := hcp t; push_cast at this; exact this
  have huniq : ∀ p' : ℂ × (ℤ → ℂ), (∃ Λ' c', IsMathieuLambdaPath ν q Λ' c' ∧ Λ' 1 = p'.1 ∧
      c' 1 = p'.2) → p' = ((Λ 1 : ℂ), cp 1) := by
    rintro ⟨a', c''⟩ ⟨Λ', c', hp, rfl, rfl⟩
    have hseq : ∀ t ∈ Icc (0 : ℝ) 1, IsMeCoeffSeq ν ((t * q : ℝ) : ℂ) (Λ' t) (c' t) := by
      intro t ht; have := hp.isMeCoeffSeq t ht; push_cast; exact this
    have hreal : ∀ t ∈ Icc (0 : ℝ) 1, Λ' t = ((Λ' t).re : ℂ) := fun t ht =>
      Complex.ext (by simp) (by simp [im_eq_zero_of_isMeCoeffSeq (hseq t ht)])
    have hroot : ∀ t ∈ Icc (0 : ℝ) 1,
        (mathieuWI ((Λ' t).re : ℂ) ((t * q : ℝ) : ℂ) π).re = Real.cos (π * ν) := by
      intro t ht
      have hch := (exists_isFloquetSolution_iff_charExp _ _ _).mp
        ⟨_, isFloquetSolution_tsum_of_isMeCoeffSeq (hseq t ht)⟩
      unfold IsMathieuCharExp at hch
      rw [← hreal t ht, ← hch, ← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.ofReal_re]
    have heq := eqOn_of_re_mathieuWI_pi_eq hc (Λ₁ := fun t => (Λ' t).re) (Λ₂ := Λ)
      (Complex.continuous_re.comp_continuousOn hp.continuousOn_lambda) hΛc.continuousOn
      (by
        show (Λ' 0).re = Λ 0
        rw [hp.lambda_zero, hΛ0, ← Complex.ofReal_pow, Complex.ofReal_re]) hroot
      (fun t _ => hΛ t)
    have hΛeq : ∀ t ∈ Icc (0 : ℝ) 1, Λ' t = (Λ t : ℂ) := fun t ht => by
      rw [hreal t ht]; exact congrArg _ (heq ht)
    have hzero : c' 0 = cp 0 := by
      have h1 : IsMeCoeffSeq ν 0 ((ν : ℂ) ^ 2) (c' 0) := by
        have := hseq 0 ⟨le_rfl, zero_le_one⟩
        rwa [zero_mul, Complex.ofReal_zero, hp.lambda_zero] at this
      have h2 : IsMeCoeffSeq ν 0 ((ν : ℂ) ^ 2) (cp 0) := by
        have := hcp 0
        rwa [zero_mul, Complex.ofReal_zero, hΛ0, Complex.ofReal_pow] at this
      rw [(isMeCoeffSeq_zero_q hν h1).1, (isMeCoeffSeq_zero_q hν h2).1, hp.coeff_zero, hcp00]
    have hsign : ∀ t ∈ Icc (0 : ℝ) 1, c' t = cp t ∨ c' t = -cp t := by
      intro t ht
      rcases eq_or_ne t 0 with rfl | ht0
      · exact Or.inl hzero
      have hQ : ((t * q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero ht0 hq
      have hw := isFloquetSolution_tsum_of_isMeCoeffSeq (hcp t)
      have hw' := isFloquetSolution_tsum_of_isMeCoeffSeq (hseq t ht)
      rw [hΛeq t ht] at hw'
      obtain ⟨κ, hκ⟩ := IsFloquetSolution.unique hQ hw hw'
      have hcκ : c' t = fun m => κ * cp t m := by
        refine eq_of_tsum_exp_series_eq (ν := ν) (hseq t ht).2.1
          (by simpa [norm_mul] using (hcp t).2.1.mul_left ‖κ‖) fun x => ?_
        have := congrFun hκ x
        rw [this, ← tsum_mul_left]
        congr 1; funext m; ring
      have hκ2 : κ * κ = 1 := by
        have h1 := (hseq t ht).2.2
        have h2 := (hcp t).2.2.mul_left (κ ^ 2)
        rw [mul_one] at h2
        rw [hcκ] at h1
        have := h1.unique (h2.congr_fun fun m => by ring)
        rw [← sq]; exact this.symm
      rcases mul_self_eq_one_iff.mp hκ2 with h | h
      · left; rw [hcκ, h]; funext m; simp
      · right; rw [hcκ, h]; funext m; simp
    -- connectedness of `[0, 1]`
    set u : Set ℝ := ⋂ m : ℤ, Icc 0 1 ∩ (fun t => c' t m - cp t m) ⁻¹' {0} with hu
    set v : Set ℝ := ⋂ m : ℤ, Icc 0 1 ∩ (fun t => c' t m + cp t m) ⁻¹' {0} with hv
    have huc : IsClosed u := isClosed_iInter fun m =>
      ((hp.continuousOn_coeff m).sub (hcpc m).continuousOn).preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_singleton
    have hvc : IsClosed v := isClosed_iInter fun m =>
      ((hp.continuousOn_coeff m).add (hcpc m).continuousOn).preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_singleton
    have hmem_u : ∀ t, t ∈ u ↔ t ∈ Icc (0 : ℝ) 1 ∧ c' t = cp t := by
      intro t
      simp only [u, mem_iInter, mem_inter_iff, mem_preimage, mem_singleton_iff, sub_eq_zero]
      exact ⟨fun h => ⟨(h 0).1, funext fun m => (h m).2⟩,
        fun h m => ⟨h.1, congrFun h.2 m⟩⟩
    have hmem_v : ∀ t, t ∈ v ↔ t ∈ Icc (0 : ℝ) 1 ∧ c' t = -cp t := by
      intro t
      simp only [v, mem_iInter, mem_inter_iff, mem_preimage, mem_singleton_iff,
        add_eq_zero_iff_eq_neg]
      exact ⟨fun h => ⟨(h 0).1, funext fun m => (h m).2⟩,
        fun h m => ⟨h.1, congrFun h.2 m⟩⟩
    have hcover : Icc (0 : ℝ) 1 ⊆ u ∪ v := by
      intro t ht
      rcases hsign t ht with h | h
      · exact Or.inl ((hmem_u t).2 ⟨ht, h⟩)
      · exact Or.inr ((hmem_v t).2 ⟨ht, h⟩)
    have hdisj : Icc (0 : ℝ) 1 ∩ (u ∩ v) = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro ht htu htv
      have e1 := ((hmem_u t).1 htu).2
      have e2 := ((hmem_v t).1 htv).2
      have hz : cp t = 0 := by
        funext m
        have := congrFun (e1.symm.trans e2) m
        simp only [Pi.neg_apply, Pi.zero_apply] at this ⊢
        linear_combination this / 2
      have := (hcp t).2.2
      rw [hz] at this
      simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
      exact one_ne_zero (hasSum_zero.unique this).symm
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_Icc) u v huc hvc
      hcover hdisj with h | h
    · have h1 := ((hmem_u 1).1 (h ⟨zero_le_one, le_rfl⟩)).2
      rw [hΛeq 1 ⟨zero_le_one, le_rfl⟩, h1]
    · exfalso
      have h1 := ((hmem_v 0).1 (h ⟨le_rfl, zero_le_one⟩)).2
      rw [hzero] at h1
      have := congrFun h1 0
      simp only [Pi.neg_apply, hcp00] at this
      norm_num at this
  have hex : ∃ Λ' c', IsMathieuLambdaPath ν q Λ' c' ∧ Λ' 1 = ((Λ 1 : ℂ), cp 1).1 ∧
      c' 1 = ((Λ 1 : ℂ), cp 1).2 := ⟨fun t => (Λ t : ℂ), cp, hpath, rfl, rfl⟩
  refine ⟨⟨_, hex, huniq⟩, ?_⟩
  rw [mathieuLambda_of_not_int hν, mathieuLambdaData_eq_of_unique hex huniq]
  simp

end DLMF.Mathieu
