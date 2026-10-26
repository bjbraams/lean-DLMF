/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Noninteger.Defs
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Mathieu functions of noninteger order: basic properties and Fourier series
(DLMF §§28.12, 28.14)

Statements of DLMF §28.12 (eigenvalues `λ_ν(q)`, Floquet solutions `me_ν(z, q)`, the functions
`ce_ν`, `se_ν`) and §28.14 (Fourier series and their coefficients `c^ν_{2m}(q)`), for the
definitions of `DLMF.Mathieu.Noninteger.Defs`.

Proved here from the definitions (no admissions):

* the values at `q = 0` (28.12.1, 28.12.4, 28.14.9): along the segment `[0, 0]` the only
  continuation is the constant one (a continuous path in the countable set `{(ν + 2m)²}` is
  constant, and the sign of `c_0` is fixed by continuity);
* the symmetries 28.12.2, 28.12.8, 28.12.9, 28.12.10, 28.12.14, 28.12.15, 28.14.7, 28.14.8,
  obtained by transporting continuation paths along the involutions
  `c_m ↦ c_{-m}` (`ν ↦ -ν`), `c_m ↦ (-1)^m c_m` (`q ↦ -q`) and complex conjugation;
* the pseudoperiodicity 28.12.6, the reality of `ce_ν`, `se_ν` for real `ν`, `q`, `z`, and
  the recurrence and normalization 28.14.4–28.14.5 at normal values.

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

open Complex Set Filter Asymptotics
open scoped Topology Real Classical ComplexConjugate

namespace DLMF.Mathieu

/-! ### The continuation endpoint -/

/-- If `p` is an endpoint of a continuation path and every endpoint equals `p`, then
`mathieuLambdaData ν q = p`. -/
theorem m28b_data_eq {ν q : ℂ} {p : ℂ × (ℤ → ℂ)}
    (hp : ∃ Λ c, IsMathieuLambdaPath ν q Λ c ∧ Λ 1 = p.1 ∧ c 1 = p.2)
    (hu : ∀ p' : ℂ × (ℤ → ℂ), (∃ Λ c, IsMathieuLambdaPath ν q Λ c ∧ Λ 1 = p'.1 ∧ c 1 = p'.2) →
      p' = p) :
    mathieuLambdaData ν q = p := by
  have h : MathieuNormalSegment ν q := ⟨p, hp, hu⟩
  simp only [mathieuLambdaData, h, dite_true]
  exact hu _ h.choose_spec.1

/-- At a normal value the endpoint is attained by a continuation path. -/
theorem m28b_data_spec {ν q : ℂ} (h : MathieuNormalSegment ν q) :
    ∃ Λ c, IsMathieuLambdaPath ν q Λ c ∧ Λ 1 = (mathieuLambdaData ν q).1 ∧
      c 1 = (mathieuLambdaData ν q).2 := by
  simp only [mathieuLambdaData, h, dite_true]
  exact h.choose_spec.1

/-- At a normal value, `(λ_ν(q), c^ν(q))` solves the recurrence 28.14.4 with the normalization
28.14.5. -/
theorem m28b_isMeCoeffSeq_data {ν q : ℂ} (h : MathieuNormalSegment ν q) :
    IsMeCoeffSeq ν q (mathieuLambdaData ν q).1 (mathieuLambdaData ν q).2 := by
  obtain ⟨Λ, c, hp, h1, h2⟩ := m28b_data_spec h
  have := hp.isMeCoeffSeq 1 ⟨zero_le_one, le_rfl⟩
  rw [h1, h2] at this
  simpa using this

/-- **Transport of continuation data** along an involution `F` of `ℂ × (ℤ → ℂ)` fixing the
junk value `(0, 0)`, when `F` maps the continuation paths for `(ν, q)` to those for
`(ν', q')` and back. -/
theorem m28b_data_transport {ν q ν' q' : ℂ} (F : ℂ × (ℤ → ℂ) → ℂ × (ℤ → ℂ))
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
    have hdata : mathieuLambdaData ν q = p := m28b_data_eq hp hu
    rw [hdata]
    refine m28b_data_eq (e₁ p hp) fun p' hp' => ?_
    have := hu _ (e₂ p' hp')
    rw [← this, hF p']
  · have h' : ¬ MathieuNormalSegment ν' q' := by
      rintro ⟨p, hp, hu⟩
      refine h ⟨F p, e₂ p hp, fun p' hp' => ?_⟩
      have := hu _ (e₁ p' hp')
      rw [← this, hF p']
    simp only [mathieuLambdaData, h, h', dite_false, hF0]

/-! ### The case `q = 0` -/

theorem m28b_sq_sub_ne {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {m : ℤ} (hm : m ≠ 0) :
    ν ^ 2 - (ν + 2 * m) ^ 2 ≠ 0 := by
  have e : ν ^ 2 - (ν + 2 * m) ^ 2 = -4 * m * (ν + m) := by ring
  rw [e]
  refine mul_ne_zero (mul_ne_zero (by norm_num) (Int.cast_ne_zero.mpr hm)) fun h => ?_
  exact hν (-m) (by push_cast; linear_combination -h)

theorem m28b_isMeCoeffSeq_single (ν : ℂ) (t : ℝ) :
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
theorem m28b_const_of_countable {f : ℝ → ℂ} {S : Set ℂ} (hS : S.Countable)
    (hf : ContinuousOn f (Icc 0 1)) (hfS : ∀ t ∈ Icc (0 : ℝ) 1, f t ∈ S) :
    ∀ t ∈ Icc (0 : ℝ) 1, f t = f 0 := by
  intro t ht
  have hsub : f '' Icc 0 1 ⊆ S := by rintro _ ⟨s, hs, rfl⟩; exact hfS s hs
  have hsing := hS.isTotallyDisconnected _ hsub (isPreconnected_Icc.image f hf)
  exact hsing ⟨t, ht, rfl⟩ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩

/-- Every continuation path for `q = 0` is the constant path `(ν², δ_0)`. -/
theorem m28b_path_zero {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {Λ : ℝ → ℂ} {c : ℝ → ℤ → ℂ}
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
    rw [m28b_const_of_countable (Set.countable_range _) hp.continuousOn_lambda hΛS t ht,
      hp.lambda_zero]
  have hcm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ m : ℤ, m ≠ 0 → c t m = 0 := by
    intro t ht m hm
    have := hrec t ht m
    rw [hΛ t ht] at this
    exact (mul_eq_zero.mp this).resolve_left (m28b_sq_sub_ne hν hm)
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
    rw [m28b_const_of_countable (Set.toFinite _).countable (hp.continuousOn_coeff 0) hc0 t ht,
      hp.coeff_zero]
  intro t ht
  refine ⟨hΛ t ht, funext fun m => ?_⟩
  by_cases hm : m = 0
  · subst hm; simp [hc0' t ht]
  · simp [hm, hcm t ht m hm]

/-- The continuation data at `q = 0`: `(ν², δ_0)`. -/
theorem m28b_data_zero {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) :
    mathieuLambdaData ν 0 = (ν ^ 2, Pi.single 0 1) := by
  refine m28b_data_eq ⟨fun _ => ν ^ 2, fun _ => Pi.single 0 1,
    ⟨continuousOn_const, fun m => continuousOn_const, rfl, by simp,
      fun t _ => m28b_isMeCoeffSeq_single ν t⟩, rfl, rfl⟩ ?_
  rintro ⟨a, b⟩ ⟨Λ, c, hp, rfl, rfl⟩
  obtain ⟨h1, h2⟩ := m28b_path_zero hν hp 1 ⟨zero_le_one, le_rfl⟩
  rw [h1, h2]

/-- `0` is normal along the segment for `ν ∉ ℤ`. -/
theorem mathieuNormalSegment_zero {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) :
    MathieuNormalSegment ν 0 := by
  refine ⟨(ν ^ 2, Pi.single 0 1), ⟨fun _ => ν ^ 2, fun _ => Pi.single 0 1,
    ⟨continuousOn_const, fun m => continuousOn_const, rfl, by simp,
      fun t _ => m28b_isMeCoeffSeq_single ν t⟩, rfl, rfl⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨Λ, c, hp, rfl, rfl⟩
  obtain ⟨h1, h2⟩ := m28b_path_zero hν hp 1 ⟨zero_le_one, le_rfl⟩
  rw [h1, h2]

/-! ### §28.12(i) Eigenvalues -/

/-- `ν ∉ ℤ` implies `ν + 2n ∉ ℤ`, `-ν ∉ ℤ`, `conj ν ∉ ℤ`. -/
theorem m28b_not_int_neg {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) : ∀ m : ℤ, (m : ℂ) ≠ -ν :=
  fun m h => hν (-m) (by push_cast; rw [h, neg_neg])

theorem m28b_not_int_conj {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) :
    ∀ m : ℤ, (m : ℂ) ≠ conj ν :=
  fun m h => hν m (by rw [← Complex.conj_conj ν, ← h]; simp)

theorem m28b_not_int_add {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (n : ℤ) :
    ∀ m : ℤ, (m : ℂ) ≠ ν + 2 * n :=
  fun m h => hν (m - 2 * n) (by push_cast; rw [h]; ring)

/-- **Eigenvalues at `q = 0`** (DLMF 28.12.1): `λ_ν(0) = ν²` for `ν ∉ ℤ` (DLMF writes
`λ_{ν+2n}(0) = (ν + 2n)²`; with `ν` replaced by `ν + 2n` this is the same statement). -/
@[dlmf 28.12.E1]
theorem mathieuLambda_zero {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) : mathieuLambda ν 0 = ν ^ 2 := by
  rw [mathieuLambda_of_not_int hν, m28b_data_zero hν]

/-- **Characterization of `λ_ν(q)`** (DLMF §28.12(i)): for `ν ∉ ℤ` and `q` normal along the
segment, `a = λ_ν(q)` is a root of the characteristic equation 28.2.16,
`cos(πν) = w_I(π; a, q)`. -/
@[dlmf 28.12.i]
theorem isMathieuCharExp_mathieuLambda {ν q : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    (hq : MathieuNormalSegment ν q) : IsMathieuCharExp (mathieuLambda ν q) q ν := by
  sorry

/-- **The roots of 28.2.16** (DLMF §28.12(i)): for `ν ∉ ℤ`, if `q` is normal along the segment
with respect to every `ν + 2n`, the roots `a` of `cos(πν) = w_I(π; a, q)` are exactly the
values `λ_{ν+2n}(q)`, `n ∈ ℤ`. -/
@[dlmf 28.12.i]
theorem isMathieuCharExp_iff_exists_mathieuLambda {ν q a : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    (hq : ∀ n : ℤ, MathieuNormalSegment (ν + 2 * n) q) :
    IsMathieuCharExp a q ν ↔ ∃ n : ℤ, a = mathieuLambda (ν + 2 * n) q := by
  sorry

/-- **Real parameters are normal** (DLMF §28.12(i)): for real `ν ∉ ℤ` and real `q` all the
`λ_ν(q)` are real and `q` is normal (along the whole segment `[0, q]`). -/
@[dlmf 28.12.i]
theorem mathieuNormalSegment_real {ν q : ℝ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) :
    MathieuNormalSegment ν q ∧ (mathieuLambda ν q).im = 0 := by
  sorry

/-- **Discontinuity in `ν`** (DLMF §28.12(i)): for fixed real `q ≠ 0`, `λ_ν(q)` is
discontinuous (as a function of real `ν`) at `ν = ±1, ±2, …`. -/
@[dlmf 28.12.i]
theorem not_continuousAt_mathieuLambda {q : ℝ} (hq : q ≠ 0) {n : ℤ} (hn : n ≠ 0) :
    ¬ ContinuousAt (fun ν : ℝ => mathieuLambda ν q) n := by
  sorry

/-- The continuation paths for `-ν` are those for `ν` with `c_m` replaced by `c_{-m}`. -/
theorem m28b_path_neg_nu {ν q : ℂ} {Λ : ℝ → ℂ} {c : ℝ → ℤ → ℂ}
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
theorem m28b_data_neg_nu (ν q : ℂ) :
    mathieuLambdaData (-ν) q =
      ((mathieuLambdaData ν q).1, fun m => (mathieuLambdaData ν q).2 (-m)) := by
  have := m28b_data_transport (ν := ν) (q := q) (ν' := -ν) (q' := q)
    (fun p => (p.1, fun m => p.2 (-m))) (fun p => by simp) (by ext m <;> simp)
    (fun Λ c hp => ⟨_, _, m28b_path_neg_nu hp, rfl⟩)
    (fun Λ c hp => ⟨_, _, by simpa using m28b_path_neg_nu hp, rfl⟩)
  exact this

theorem m28b_negOnePow_mul_self (m : ℤ) : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
  rcases Int.even_or_odd m with h | h
  · rw [h.neg_one_zpow]; ring
  · rw [h.neg_one_zpow]; ring

/-- The continuation paths for `-q` are those for `q` with `c_m` replaced by `(-1)^m c_m`. -/
theorem m28b_path_neg_q {ν q : ℂ} {Λ : ℝ → ℂ} {c : ℝ → ℤ → ℂ}
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
    rw [mul_pow, sq ((-1 : ℂ) ^ m), m28b_negOnePow_mul_self, one_mul]

/-- The continuation data for `-q` (proved by transport). -/
theorem m28b_data_neg_q (ν q : ℂ) :
    mathieuLambdaData ν (-q) =
      ((mathieuLambdaData ν q).1, fun m => (-1 : ℂ) ^ m * (mathieuLambdaData ν q).2 m) := by
  have := m28b_data_transport (ν := ν) (q := q) (ν' := ν) (q' := -q)
    (fun p => (p.1, fun m => (-1 : ℂ) ^ m * p.2 m))
    (fun p => by ext m <;> simp [← mul_assoc, m28b_negOnePow_mul_self]) (by ext m <;> simp)
    (fun Λ c hp => ⟨_, _, m28b_path_neg_q hp, rfl⟩)
    (fun Λ c hp => ⟨_, _, by simpa using m28b_path_neg_q hp, rfl⟩)
  exact this

/-- The continuation paths for `(conj ν, conj q)` are the conjugates of those for `(ν, q)`. -/
theorem m28b_path_conj {ν q : ℂ} {Λ : ℝ → ℂ} {c : ℝ → ℤ → ℂ}
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
theorem m28b_data_conj (ν q : ℂ) :
    mathieuLambdaData (conj ν) (conj q) =
      (conj (mathieuLambdaData ν q).1, fun m => conj ((mathieuLambdaData ν q).2 m)) := by
  have := m28b_data_transport (ν := ν) (q := q) (ν' := conj ν) (q' := conj q)
    (fun p => (conj p.1, fun m => conj (p.2 m))) (fun p => by simp) (by ext m <;> simp)
    (fun Λ c hp => ⟨_, _, m28b_path_conj hp, rfl⟩)
    (fun Λ c hp => ⟨_, _, by simpa using m28b_path_conj hp, rfl⟩)
  exact this

/-- **Symmetries of `λ_ν`** (DLMF 28.12.2): `λ_ν(-q) = λ_ν(q) = λ_{-ν}(q)` for `ν ∉ ℤ`. -/
@[dlmf 28.12.E2]
theorem mathieuLambda_neg_q_and_neg_nu {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (q : ℂ) :
    mathieuLambda ν (-q) = mathieuLambda ν q ∧ mathieuLambda (-ν) q = mathieuLambda ν q := by
  rw [mathieuLambda_of_not_int hν, mathieuLambda_of_not_int hν,
    mathieuLambda_of_not_int (m28b_not_int_neg hν), m28b_data_neg_q, m28b_data_neg_nu]
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
  simp only [mathieuMeCoeff_of_not_int hν, m28b_data_zero hν]
  rw [tsum_eq_single 0 fun m hm => by simp [hm]]
  simp

/-- **Floquet property** (DLMF §28.12(ii)): for `ν ∉ ℤ` and `q` normal along the segment,
`me_ν(z, q)` is a Floquet solution with respect to `ν` of Mathieu's equation with
`a = λ_ν(q)`; `me_ν(-z, q)` is a Floquet solution with respect to `-ν` with the same `a`. -/
@[dlmf 28.12.ii]
theorem isFloquetSolution_mathieuMe {ν q : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    (hq : MathieuNormalSegment ν q) :
    IsFloquetSolution (mathieuLambda ν q) q ν (fun z => mathieuMe ν z q) ∧
      IsFloquetSolution (mathieuLambda ν q) q (-ν) (fun z => mathieuMe ν (-z) q) := by
  sorry

/-- **Normalization** (DLMF 28.12.5): `∫₀^π me_ν(x, q) me_ν(-x, q) dx = π` for `ν ∉ ℤ` and `q`
normal along the segment. -/
@[dlmf 28.12.E5]
theorem integral_mathieuMe_mul_neg {ν q : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    (hq : MathieuNormalSegment ν q) :
    ∫ x in (0 : ℝ)..π, mathieuMe ν x q * mathieuMe ν (-x) q = π := by
  sorry

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
  rw [mathieuMe_of_not_int (m28b_not_int_neg hν), mathieuMe_of_not_int hν]
  simp only [mathieuMeCoeff_of_not_int (m28b_not_int_neg hν), mathieuMeCoeff_of_not_int hν,
    m28b_data_neg_nu]
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1; funext m
  simp only [Equiv.neg_apply, neg_neg, Int.cast_neg]
  congr 2; ring

/-- **Change of sign of `q`** (DLMF 28.12.9): `me_ν(z, -q) = e^{iνπ/2} me_ν(z - π/2, q)` for
`ν ∉ ℤ`. -/
@[dlmf 28.12.E9]
theorem mathieuMe_neg_q {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (z q : ℂ) :
    mathieuMe ν z (-q) = Complex.exp (I * ν * π / 2) * mathieuMe ν (z - π / 2) q := by
  rw [mathieuMe_of_not_int hν, mathieuMe_of_not_int hν, ← tsum_mul_left]
  simp only [mathieuMeCoeff_of_not_int hν, m28b_data_neg_q]
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
  rw [mathieuMe_of_not_int hν, mathieuMe_of_not_int (m28b_not_int_conj hν), Complex.conj_tsum]
  simp only [mathieuMeCoeff_of_not_int hν, mathieuMeCoeff_of_not_int (m28b_not_int_conj hν),
    m28b_data_conj]
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

/-- **Rational order** (DLMF §28.12(iii)): when `ν = s/m` is rational but not an integer, all
solutions of Mathieu's equation with characteristic exponent `ν` are periodic with period
`2mπ`. -/
@[dlmf 28.12.iii]
theorem mathieu_periodic_of_rational {a q : ℂ} {s : ℤ} {m : ℕ} (hm : m ≠ 0)
    (hν : ∀ k : ℤ, (k : ℂ) ≠ s / m) (hc : IsMathieuCharExp a q (s / m)) {w : ℂ → ℂ}
    (hw : IsMathieuSolution a q w) : Function.Periodic w (2 * m * π) := by
  sorry

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

end DLMF.Mathieu
