/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Noninteger.Basic
public import DLMF.Mathieu.Properties
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Mathieu functions of noninteger order: basic properties and Fourier series
(DLMF §§28.12, 28.14)

Statements of DLMF §28.12 (eigenvalues `λ_ν(q)`, Floquet solutions `me_ν(z, q)`, the functions
`ce_ν`, `se_ν`) and §28.14 (Fourier series and their coefficients `c^ν_{2m}(q)`), for the
definitions of `DLMF.Mathieu.Noninteger.Basic`.

Proved here from the definitions (no admissions):

* the values at `q = 0` (28.12.1, 28.12.4, 28.14.9): along the segment `[0, 0]` the only
  continuation is the constant one (a continuous path in the countable set `{(ν + 2m)²}` is
  constant, and the sign of `c_0` is fixed by continuity);
* the symmetries 28.12.2, 28.12.8, 28.12.9, 28.12.10, 28.12.14, 28.12.15, 28.14.7, 28.14.8,
  obtained by transporting continuation paths along the involutions
  `c_m ↦ c_{-m}` (`ν ↦ -ν`), `c_m ↦ (-1)^m c_m` (`q ↦ -q`) and complex conjugation;
* the pseudoperiodicity 28.12.6, the reality of `ce_ν`, `se_ν` for real `ν`, `q`, `z`, and
  the recurrence and normalization 28.14.4–28.14.5 at normal values;
* at normal values: the Floquet property of `me_ν(±z, q)` (§28.12(ii)), the normalization
  28.12.5 and the characteristic equation `cos πν = w_I(π; λ_ν(q), q)` (§28.12(i)). The key
  step (`p1b_summable_norm_mul_exp`) is that an absolutely summable solution of the
  recurrence 28.14.4 decays faster than every exponential, so `∑ c_m e^{i(ν+2m)z}` is entire
  and can be differentiated termwise (`p1b_isMathieuSolution_series`);
* the periodicity of all solutions for rational noninteger `ν` (§28.12(iii)), from the
  Floquet dichotomy of `DLMF.Mathieu.Properties`.

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
lemma m28b_data_eq {ν q : ℂ} {p : ℂ × (ℤ → ℂ)}
    (hp : ∃ Λ c, IsMathieuLambdaPath ν q Λ c ∧ Λ 1 = p.1 ∧ c 1 = p.2)
    (hu : ∀ p' : ℂ × (ℤ → ℂ), (∃ Λ c, IsMathieuLambdaPath ν q Λ c ∧ Λ 1 = p'.1 ∧ c 1 = p'.2) →
      p' = p) :
    mathieuLambdaData ν q = p := by
  have h : MathieuNormalSegment ν q := ⟨p, hp, hu⟩
  simp only [mathieuLambdaData, h, dite_true]
  exact hu _ h.choose_spec.1

/-- At a normal value the endpoint is attained by a continuation path. -/
lemma m28b_data_spec {ν q : ℂ} (h : MathieuNormalSegment ν q) :
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
lemma m28b_data_transport {ν q ν' q' : ℂ} (F : ℂ × (ℤ → ℂ) → ℂ × (ℤ → ℂ))
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

/-- For `ν ∉ ℤ` and `m ≠ 0`, `ν² ≠ (ν + 2m)²`. -/
lemma m28b_sq_sub_ne {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {m : ℤ} (hm : m ≠ 0) :
    ν ^ 2 - (ν + 2 * m) ^ 2 ≠ 0 := by
  have e : ν ^ 2 - (ν + 2 * m) ^ 2 = -4 * m * (ν + m) := by ring
  rw [e]
  refine mul_ne_zero (mul_ne_zero (by norm_num) (Int.cast_ne_zero.mpr hm)) fun h => ?_
  exact hν (-m) (by push_cast; linear_combination -h)

/-- At `q = 0`, the sequence `δ_{m,0}` is a coefficient sequence for `me_ν` with `λ = ν²`. -/
lemma m28b_isMeCoeffSeq_single (ν : ℂ) (t : ℝ) :
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
lemma m28b_const_of_countable {f : ℝ → ℂ} {S : Set ℂ} (hS : S.Countable)
    (hf : ContinuousOn f (Icc 0 1)) (hfS : ∀ t ∈ Icc (0 : ℝ) 1, f t ∈ S) :
    ∀ t ∈ Icc (0 : ℝ) 1, f t = f 0 := by
  intro t ht
  have hsub : f '' Icc 0 1 ⊆ S := by rintro _ ⟨s, hs, rfl⟩; exact hfS s hs
  have hsing := hS.isTotallyDisconnected _ hsub (isPreconnected_Icc.image f hf)
  exact hsing ⟨t, ht, rfl⟩ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩

/-- Every continuation path for `q = 0` is the constant path `(ν², δ_0)`. -/
lemma m28b_path_zero {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {Λ : ℝ → ℂ} {c : ℝ → ℤ → ℂ}
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

/-- If `ν ∉ ℤ` then `ν̄ ∉ ℤ`. -/
lemma m28b_not_int_conj {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) :
    ∀ m : ℤ, (m : ℂ) ≠ conj ν :=
  fun m h => hν m (by rw [← Complex.conj_conj ν, ← h]; simp)

/-- If `ν ∉ ℤ` then `ν + 2n ∉ ℤ` for every integer `n`. -/
lemma m28b_not_int_add {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (n : ℤ) :
    ∀ m : ℤ, (m : ℂ) ≠ ν + 2 * n :=
  fun m h => hν (m - 2 * n) (by push_cast; rw [h]; ring)

/-- **Eigenvalues at `q = 0`** (DLMF 28.12.1): `λ_ν(0) = ν²` for `ν ∉ ℤ` (DLMF writes
`λ_{ν+2n}(0) = (ν + 2n)²`; with `ν` replaced by `ν + 2n` this is the same statement). -/
@[dlmf 28.12.E1]
theorem mathieuLambda_zero {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) : mathieuLambda ν 0 = ν ^ 2 := by
  rw [mathieuLambda_of_not_int hν, m28b_data_zero hν]

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
lemma m28b_path_neg_nu {ν q : ℂ} {Λ : ℝ → ℂ} {c : ℝ → ℤ → ℂ}
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

/-- `(-1)^m (-1)^m = 1` for an integer `m`. -/
theorem m28b_negOnePow_mul_self (m : ℤ) : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
  rcases Int.even_or_odd m with h | h
  · rw [h.neg_one_zpow]; ring
  · rw [h.neg_one_zpow]; ring

/-- The continuation paths for `-q` are those for `q` with `c_m` replaced by `(-1)^m c_m`. -/
lemma m28b_path_neg_q {ν q : ℂ} {Λ : ℝ → ℂ} {c : ℝ → ℤ → ℂ}
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
lemma m28b_path_conj {ν q : ℂ} {Λ : ℝ → ℂ} {c : ℝ → ℤ → ℂ}
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

/-! ### Absolutely convergent solutions of the recurrence 28.14.4 -/

/-- An absolutely summable solution of the recurrence 28.14.4 decays faster than every
exponential: `∑ |c_m| e^{K|m|} < ∞` for every real `K`. -/
lemma p1b_summable_norm_mul_exp {ν q a : ℂ} {c : ℤ → ℂ}
    (hrec : ∀ m : ℤ, q * c (m + 1) - (a - (ν + 2 * m) ^ 2) * c m + q * c (m - 1) = 0)
    (hs : Summable (fun m => ‖c m‖)) (K : ℝ) :
    Summable (fun m : ℤ => ‖c m‖ * Real.exp (K * |(m : ℝ)|)) := by
  set ρ : ℝ := Real.exp (-K) / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρK : ρ * Real.exp K = 1 / 2 := by
    rw [hρdef, div_mul_eq_mul_div, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  set B : ℝ := ∑' m, ‖c m‖
  have hB : ∀ m, ‖c m‖ ≤ B := fun m => hs.le_tsum m (fun j _ => norm_nonneg _)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨N, hN⟩ := exists_nat_ge (‖ν‖ + ‖a‖ + 2 * ‖q‖ / ρ + 1)
  have hqρ : 0 ≤ 2 * ‖q‖ / ρ := by positivity
  have hD : ∀ k : ℤ, N ≤ k.natAbs → 2 * ‖q‖ / ρ + 1 ≤ ‖a - (ν + 2 * k) ^ 2‖ := by
    intro k hk
    have hk' : (N : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs]; exact_mod_cast hk
    have h2k : ‖(2 : ℂ) * k‖ = 2 * |(k : ℝ)| := by
      rw [norm_mul, Complex.norm_intCast]; norm_num
    have h1 : 2 * |(k : ℝ)| - ‖ν‖ ≤ ‖ν + 2 * k‖ := by
      have := norm_sub_norm_le ((2 : ℂ) * k) (-ν)
      rw [h2k, norm_neg, sub_neg_eq_add, add_comm] at this
      exact this
    have h3 : ‖a‖ + (2 * ‖q‖ / ρ + 1) ≤ ‖ν + 2 * k‖ := by
      have := norm_nonneg ν; have := norm_nonneg a; linarith
    have h4 : ‖ν + 2 * k‖ ≤ ‖(ν + 2 * k) ^ 2‖ := by
      have : 1 ≤ ‖ν + 2 * k‖ := by linarith [norm_nonneg a]
      rw [norm_pow]; nlinarith
    have h5 := norm_sub_norm_le ((ν + 2 * k) ^ 2) a
    rw [norm_sub_rev] at h5
    linarith
  have hind : ∀ n : ℕ, ∀ k : ℤ, N + n ≤ k.natAbs → ‖c k‖ ≤ B * ρ ^ n := by
    intro n
    induction n with
    | zero => intro k _; simpa using hB k
    | succ n ih =>
      intro k hk
      have hp := ih (k + 1) (by omega)
      have hm := ih (k - 1) (by omega)
      have hDk := hD k (by omega)
      have hDpos : 0 < ‖a - (ν + 2 * k) ^ 2‖ := by linarith
      have he : (a - (ν + 2 * k) ^ 2) * c k = q * (c (k + 1) + c (k - 1)) := by
        linear_combination -(hrec k)
      have hn : ‖a - (ν + 2 * k) ^ 2‖ * ‖c k‖ ≤ ‖q‖ * (2 * (B * ρ ^ n)) := by
        rw [← norm_mul, he, norm_mul]
        gcongr
        exact (norm_add_le _ _).trans (by linarith)
      have hDρ : 2 * ‖q‖ ≤ ‖a - (ν + 2 * k) ^ 2‖ * ρ := by
        have : (2 * ‖q‖ / ρ + 1) * ρ ≤ ‖a - (ν + 2 * k) ^ 2‖ * ρ :=
          mul_le_mul_of_nonneg_right hDk hρ.le
        rw [add_mul, div_mul_cancel₀ _ hρ.ne', one_mul] at this
        linarith
      have hBρ : 0 ≤ B * ρ ^ n := by positivity
      refine le_of_mul_le_mul_left ?_ hDpos
      calc ‖a - (ν + 2 * k) ^ 2‖ * ‖c k‖ ≤ ‖q‖ * (2 * (B * ρ ^ n)) := hn
        _ = (2 * ‖q‖) * (B * ρ ^ n) := by ring
        _ ≤ (‖a - (ν + 2 * k) ^ 2‖ * ρ) * (B * ρ ^ n) := mul_le_mul_of_nonneg_right hDρ hBρ
        _ = ‖a - (ν + 2 * k) ^ 2‖ * (B * ρ ^ (n + 1)) := by ring
  set C : ℝ := B * (ρ ^ N)⁻¹
  have hg : Summable (fun k : ℤ => C * (1 / 2 : ℝ) ^ k.natAbs) := by
    have hgeo : Summable (fun n : ℕ => C * (1 / 2 : ℝ) ^ n) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
    refine Summable.of_nat_of_neg ?_ ?_
    · simpa using hgeo
    · simpa using hgeo
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Int.cofinite_eq, Filter.eventually_sup]
  have key : ∀ k : ℤ, N ≤ k.natAbs →
      ‖‖c k‖ * Real.exp (K * |(k : ℝ)|)‖ ≤ C * (1 / 2 : ℝ) ^ k.natAbs := by
    intro k hk
    have hc := hind (k.natAbs - N) k (by omega)
    have habs : |(k : ℝ)| = (k.natAbs : ℝ) := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs]; rfl
    rw [Real.norm_of_nonneg (by positivity), habs, mul_comm K, Real.exp_nat_mul]
    have hpow : ρ ^ (k.natAbs - N) = (ρ ^ N)⁻¹ * ρ ^ k.natAbs := by
      rw [pow_sub₀ _ hρ.ne' hk]; ring
    calc ‖c k‖ * Real.exp K ^ k.natAbs ≤ B * ρ ^ (k.natAbs - N) * Real.exp K ^ k.natAbs := by
          gcongr
      _ = C * (ρ * Real.exp K) ^ k.natAbs := by rw [hpow, mul_pow]; ring
      _ = C * (1 / 2 : ℝ) ^ k.natAbs := by rw [hρK]
  constructor
  · exact eventually_atBot.2 ⟨-(N : ℤ), fun k hk => key k (by omega)⟩
  · exact eventually_atTop.2 ⟨(N : ℤ), fun k hk => key k (by omega)⟩

/-- Bound on `(i(ν+2m))^j e^{i(ν+2m)z}` for `‖z‖ ≤ R`. -/
theorem p1b_norm_pow_exp_le (ν z : ℂ) (m : ℤ) {R : ℝ} (hz : ‖z‖ ≤ R) (j : ℕ) :
    ‖(I * (ν + 2 * m)) ^ j * Complex.exp (I * (ν + 2 * m) * z)‖ ≤
      Real.exp (‖ν‖ * (R + j)) * Real.exp (2 * (R + j) * |(m : ℝ)|) := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  set y : ℝ := ‖ν‖ + 2 * |(m : ℝ)|
  have hx : ‖ν + 2 * m‖ ≤ y := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_intCast]; norm_num [y]
  have hy : 0 ≤ y := by positivity
  have h1 : ‖(I * (ν + 2 * m)) ^ j‖ ≤ Real.exp (j * y) := by
    rw [norm_pow, norm_mul, Complex.norm_I, one_mul, Real.exp_nat_mul]
    refine pow_le_pow_left₀ (norm_nonneg _) (hx.trans ?_) j
    linarith [Real.add_one_le_exp y]
  have h2 : ‖Complex.exp (I * (ν + 2 * m) * z)‖ ≤ Real.exp (y * R) := by
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    exact mul_le_mul hx hz (norm_nonneg _) hy
  calc _ ≤ Real.exp (j * y) * Real.exp (y * R) := by
        rw [norm_mul]; exact mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; simp only [y]; ring

/-- The summable majorant (from faster-than-exponential decay) of the termwise
differentiated series. -/
lemma p1b_summable_bound_of {ν : ℂ} {c : ℤ → ℂ}
    (hb : ∀ K : ℝ, Summable (fun m : ℤ => ‖c m‖ * Real.exp (K * |(m : ℝ)|))) (R : ℝ) (j : ℕ) :
    Summable (fun m : ℤ => ‖c m‖ *
      (Real.exp (‖ν‖ * (R + j)) * Real.exp (2 * (R + j) * |(m : ℝ)|))) :=
  ((hb (2 * (R + j))).mul_left (Real.exp (‖ν‖ * (R + j)))).congr
    fun m => by ring

/-- Termwise differentiation of `∑ c_m (i(ν+2m))^j e^{i(ν+2m)z}`. -/
theorem p1b_hasDerivAt_series_of {ν : ℂ} {c : ℤ → ℂ}
    (hb : ∀ K : ℝ, Summable (fun m : ℤ => ‖c m‖ * Real.exp (K * |(m : ℝ)|))) (j : ℕ) (z : ℂ) :
    HasDerivAt (fun w => ∑' m : ℤ, c m * ((I * (ν + 2 * m)) ^ j *
        Complex.exp (I * (ν + 2 * m) * w)))
      (∑' m : ℤ, c m * ((I * (ν + 2 * m)) ^ (j + 1) * Complex.exp (I * (ν + 2 * m) * z))) z := by
  set R : ℝ := ‖z‖ + 1
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun m w => c m * ((I * (ν + 2 * m)) ^ j * Complex.exp (I * (ν + 2 * m) * w)))
    (g' := fun m w => c m * ((I * (ν + 2 * m)) ^ (j + 1) * Complex.exp (I * (ν + 2 * m) * w)))
    (p1b_summable_bound_of (ν := ν) hb R (j + 1))
    Metric.isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected (fun m w _ => ?_)
    (fun m w hw => ?_) (Metric.mem_ball_self (by positivity : (0 : ℝ) < R)) ?_
    (by rw [Metric.mem_ball, dist_zero_right]; simp [R])
  rotate_left
  · rw [norm_mul]
    gcongr
    have := p1b_norm_pow_exp_le ν w m (R := R)
      (by rw [Metric.mem_ball, dist_zero_right] at hw; exact hw.le) (j + 1)
    simpa using this
  · refine .of_norm_bounded (p1b_summable_bound_of (ν := ν) hb R j) fun m => ?_
    rw [norm_mul]
    gcongr
    have := p1b_norm_pow_exp_le ν (0 : ℂ) m (R := R) (by simp [R]; positivity) j
    simpa using this
  · have h := ((hasDerivAt_id w).const_mul (I * (ν + 2 * m))).cexp
    have := (h.const_mul ((I * (ν + 2 * m)) ^ j)).const_mul (c m)
    convert this using 1
    · funext w; simp [mul_assoc]
    · simp only [id]; ring

/-- Absolute convergence of `∑ c_m (i(ν+2m))^j e^{i(ν+2m)z}` for every complex `z`. -/
theorem p1b_summable_series_of {ν : ℂ} {c : ℤ → ℂ}
    (hb : ∀ K : ℝ, Summable (fun m : ℤ => ‖c m‖ * Real.exp (K * |(m : ℝ)|))) (j : ℕ) (z : ℂ) :
    Summable (fun m : ℤ => ‖c m * ((I * (ν + 2 * m)) ^ j * Complex.exp (I * (ν + 2 * m) * z))‖) :=
  .of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => by
    rw [norm_mul]; gcongr; exact p1b_norm_pow_exp_le ν z m le_rfl j)
    (p1b_summable_bound_of (ν := ν) hb ‖z‖ j)

/-- The summable majorant of the termwise differentiated series. -/
theorem p1b_summable_bound {ν q a : ℂ} {c : ℤ → ℂ}
    (hrec : ∀ m : ℤ, q * c (m + 1) - (a - (ν + 2 * m) ^ 2) * c m + q * c (m - 1) = 0)
    (hs : Summable (fun m => ‖c m‖)) (R : ℝ) (j : ℕ) :
    Summable (fun m : ℤ => ‖c m‖ *
      (Real.exp (‖ν‖ * (R + j)) * Real.exp (2 * (R + j) * |(m : ℝ)|))) :=
  p1b_summable_bound_of (p1b_summable_norm_mul_exp hrec hs) R j

/-- Termwise differentiation of `∑ c_m (i(ν+2m))^j e^{i(ν+2m)z}`. -/
lemma p1b_hasDerivAt_series {ν q a : ℂ} {c : ℤ → ℂ}
    (hrec : ∀ m : ℤ, q * c (m + 1) - (a - (ν + 2 * m) ^ 2) * c m + q * c (m - 1) = 0)
    (hs : Summable (fun m => ‖c m‖)) (j : ℕ) (z : ℂ) :
    HasDerivAt (fun w => ∑' m : ℤ, c m * ((I * (ν + 2 * m)) ^ j *
        Complex.exp (I * (ν + 2 * m) * w)))
      (∑' m : ℤ, c m * ((I * (ν + 2 * m)) ^ (j + 1) * Complex.exp (I * (ν + 2 * m) * z))) z :=
  p1b_hasDerivAt_series_of (p1b_summable_norm_mul_exp hrec hs) j z

/-- Absolute convergence of `∑ c_m (i(ν+2m))^j e^{i(ν+2m)z}` for every complex `z`. -/
theorem p1b_summable_series {ν q a : ℂ} {c : ℤ → ℂ}
    (hrec : ∀ m : ℤ, q * c (m + 1) - (a - (ν + 2 * m) ^ 2) * c m + q * c (m - 1) = 0)
    (hs : Summable (fun m => ‖c m‖)) (j : ℕ) (z : ℂ) :
    Summable (fun m : ℤ => ‖c m * ((I * (ν + 2 * m)) ^ j * Complex.exp (I * (ν + 2 * m) * z))‖) :=
  p1b_summable_series_of (p1b_summable_norm_mul_exp hrec hs) j z

/-- An absolutely summable solution of 28.14.4 gives an entire solution
`∑ c_m e^{i(ν+2m)z}` of Mathieu's equation. -/
lemma p1b_isMathieuSolution_series {ν q a : ℂ} {c : ℤ → ℂ}
    (hrec : ∀ m : ℤ, q * c (m + 1) - (a - (ν + 2 * m) ^ 2) * c m + q * c (m - 1) = 0)
    (hs : Summable (fun m => ‖c m‖)) :
    IsMathieuSolution a q (fun z => ∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * z)) := by
  set S : ℕ → ℂ → ℂ := fun j z => ∑' m : ℤ, c m * ((I * (ν + 2 * m)) ^ j *
    Complex.exp (I * (ν + 2 * m) * z)) with hS
  have h0 : (fun z => ∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * z)) = S 0 := by
    funext z; simp [hS]
  have hd : ∀ j z, HasDerivAt (S j) (S (j + 1) z) z := fun j z =>
    p1b_hasDerivAt_series hrec hs j z
  have hderiv : deriv (S 0) = S 1 := funext fun z => (hd 0 z).deriv
  rw [h0]
  refine ⟨fun z => (hd 0 z).differentiableAt, fun z => ?_⟩
  rw [hderiv]
  convert hd 1 z using 1
  -- the coefficient identity
  set e : ℤ → ℂ := fun m => Complex.exp (I * (ν + 2 * m) * z) with he
  set E : ℂ := Complex.exp (2 * I * z)
  set E' : ℂ := Complex.exp (-(2 * I * z))
  have hs0 : HasSum (fun m => c m * e m) (S 0 z) := by
    have := (p1b_summable_series hrec hs 0 z).of_norm.hasSum
    simpa [hS] using this
  have hs2 : HasSum (fun m => c m * ((I * (ν + 2 * m)) ^ 2 * e m)) (S 2 z) :=
    (p1b_summable_series hrec hs 2 z).of_norm.hasSum
  have hE : ∀ m : ℤ, e (m + 1) = E * e m := fun m => by
    simp only [he, E, ← Complex.exp_add]; congr 1; push_cast; ring
  have hE' : ∀ m : ℤ, e (m - 1) = E' * e m := fun m => by
    simp only [he, E', ← Complex.exp_add]; congr 1; push_cast; ring
  have H1 : HasSum (fun m => q * c (m - 1) * e m) (q * E * S 0 z) := by
    rw [← (Equiv.addRight (1 : ℤ)).hasSum_iff]
    refine (hs0.mul_left (q * E)).congr_fun fun m => ?_
    simp only [Function.comp, Equiv.coe_addRight, add_sub_cancel_right, hE]; ring
  have H2 : HasSum (fun m => q * c (m + 1) * e m) (q * E' * S 0 z) := by
    rw [← (Equiv.subRight (1 : ℤ)).hasSum_iff]
    refine (hs0.mul_left (q * E')).congr_fun fun m => ?_
    simp only [Function.comp, Equiv.subRight_apply, sub_add_cancel, hE']; ring
  have H := (H1.add H2).sub (hs0.mul_left a)
  have hcos : 2 * Complex.cos (2 * z) = E + E' := by
    rw [Complex.cos]; simp only [E, E']; ring_nf
  have key := H.unique (hs2.congr_fun fun m => ?_)
  · rw [show 1 + 1 = 2 from rfl, ← key]; linear_combination (q * S 0 z) * hcos
  · have := hrec m
    rw [mul_pow, Complex.I_sq]
    linear_combination (e m) * this

/-- `|e^{i(ν+2m)x}| = e^{-ℑν x}` for real `x`. -/
theorem p1b_norm_exp_real (ν : ℂ) (m : ℤ) (x : ℝ) :
    ‖Complex.exp (I * (ν + 2 * m) * x)‖ = Real.exp (-(ν.im * x)) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]

/-- `∫₀^π e^{2ikx} dx = π δ_{k0}`. -/
lemma p1b_integral_exp_int (k : ℤ) :
    ∫ x in (0 : ℝ)..π, Complex.exp (2 * I * k * x) = if k = 0 then (π : ℂ) else 0 := by
  split_ifs with hk
  · subst hk; simp
  · have hc : (2 * I * k : ℂ) ≠ 0 := by
      simp [hk, Complex.I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have : Complex.exp (2 * I * k * π) = 1 := by
      rw [show (2 * I * k * π : ℂ) = k * (2 * π * I) by ring, Complex.exp_int_mul_two_pi_mul_I]
    simp [this]

/-- Fourier coefficients of an absolutely convergent series `∑ c_m e^{i(ν+2m)x}` on `[0, π]`. -/
theorem p1b_integral_series_mul_exp {ν : ℂ} {c : ℤ → ℂ} (hs : Summable (fun m => ‖c m‖))
    (n : ℤ) :
    ∫ x in (0 : ℝ)..π, (∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * x)) *
      Complex.exp (-(I * (ν + 2 * n) * x)) = π * c n := by
  have hF : ∀ m : ℤ, ∀ x : ℝ, c m * Complex.exp (I * (ν + 2 * m) * x) *
      Complex.exp (-(I * (ν + 2 * n) * x)) = c m * Complex.exp (2 * I * (m - n : ℤ) * x) := by
    intro m x
    rw [mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
  have hnorm : ∀ m : ℤ, ∀ x : ℝ, ‖c m * Complex.exp (2 * I * (m - n : ℤ) * x)‖ = ‖c m‖ := by
    intro m x
    rw [norm_mul, Complex.norm_exp]
    simp [Complex.mul_re]
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := π)
    (F := fun m x => c m * Complex.exp (2 * I * (m - n : ℤ) * x))
    (f := fun x => (∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * x)) *
      Complex.exp (-(I * (ν + 2 * n) * x)))
    (fun m _ => ‖c m‖) (fun m => by fun_prop)
    (fun m => ae_of_all _ fun x _ => (hnorm m x).le) (ae_of_all _ fun _ _ => hs)
    intervalIntegrable_const (ae_of_all _ fun x _ => ?_)
  · have hval : ∀ m : ℤ, ∫ x in (0 : ℝ)..π, c m * Complex.exp (2 * I * (m - n : ℤ) * x) =
        if m = n then (π : ℂ) * c n else 0 := by
      intro m
      rw [intervalIntegral.integral_const_mul, p1b_integral_exp_int]
      by_cases h : m = n
      · subst h; simp; ring
      · simp [sub_eq_zero, h]
    simp only [hval] at hsum
    exact hsum.unique (hasSum_ite_eq n _)
  · have hs' : Summable (fun m : ℤ => c m * Complex.exp (I * (ν + 2 * m) * x)) := by
      refine Summable.of_norm ?_
      simp only [norm_mul, p1b_norm_exp_real]
      exact hs.mul_right _
    exact (hs'.hasSum.mul_right _).congr_fun fun m => (hF m x).symm


/-- `∫₀^π f(x) f(-x) dx = π ∑ c_m²` for `f(x) = ∑ c_m e^{i(ν+2m)x}` (absolutely convergent). -/
lemma p1b_integral_series_mul_neg {ν : ℂ} {c : ℤ → ℂ} (hs : Summable (fun m => ‖c m‖))
    (hf : Continuous (fun x : ℝ => ∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * x)))
    {s : ℂ} (hsq : HasSum (fun m => c m ^ 2) s) :
    ∫ x in (0 : ℝ)..π, (∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * x)) *
      (∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * -(x : ℂ))) = π * s := by
  set f : ℝ → ℂ := fun x => ∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * x)
  have hneg : ∀ (m : ℤ) (x : ℝ), Complex.exp (I * (ν + 2 * m) * -(x : ℂ)) =
      Complex.exp (-(I * (ν + 2 * m) * x)) := fun m x => by congr 1; ring
  have hnorm : ∀ (m : ℤ) (x : ℝ),
      ‖Complex.exp (I * (ν + 2 * m) * -(x : ℂ))‖ = Real.exp (ν.im * x) := by
    intro m x
    rw [show -(x : ℂ) = ((-x : ℝ) : ℂ) by push_cast; ring, p1b_norm_exp_real]
    congr 1; ring
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := π)
    (F := fun m x => f x * (c m * Complex.exp (I * (ν + 2 * m) * -(x : ℂ))))
    (f := fun x => f x * (∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * -(x : ℂ))))
    (fun m t => ‖f t‖ * (‖c m‖ * Real.exp (ν.im * t)))
    (fun m => (hf.mul (by fun_prop)).aestronglyMeasurable)
    (fun m => ae_of_all _ fun x _ => by rw [norm_mul, norm_mul, hnorm])
    (ae_of_all _ fun t _ => (hs.mul_right _).mul_left _) ?_ (ae_of_all _ fun x _ => ?_)
  · have hval : ∀ m : ℤ, ∫ x in (0 : ℝ)..π, f x * (c m * Complex.exp (I * (ν + 2 * m) *
        -(x : ℂ))) = π * c m ^ 2 := by
      intro m
      have : (fun x : ℝ => f x * (c m * Complex.exp (I * (ν + 2 * m) * -(x : ℂ)))) =
          fun x : ℝ => c m * (f x * Complex.exp (-(I * (ν + 2 * m) * x))) := by
        funext x; rw [hneg]; ring
      rw [this, intervalIntegral.integral_const_mul, p1b_integral_series_mul_exp hs]; ring
    simp only [hval] at hsum
    exact hsum.unique (hsq.mul_left _)
  · have : (fun t : ℝ => ∑' m : ℤ, ‖f t‖ * (‖c m‖ * Real.exp (ν.im * t))) =
        fun t => ‖f t‖ * ((∑' m : ℤ, ‖c m‖) * Real.exp (ν.im * t)) := by
      funext t; rw [tsum_mul_left, tsum_mul_right]
    rw [this]
    exact (hf.norm.mul (continuous_const.mul (by fun_prop))).intervalIntegrable _ _
  · have hs' : Summable (fun m : ℤ => c m * Complex.exp (I * (ν + 2 * m) * -(x : ℂ))) := by
      refine Summable.of_norm ?_
      simp only [norm_mul, hnorm]
      exact hs.mul_right _
    exact hs'.hasSum.mul_left _

/-! ### §28.12(ii) The functions `me_ν` -/

/-- **`me_ν` at `q = 0`** (DLMF 28.12.4): `me_ν(z, 0) = e^{iνz}` for `ν ∉ ℤ`. -/
@[dlmf 28.12.E4]
theorem mathieuMe_zero {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (z : ℂ) :
    mathieuMe ν z 0 = Complex.exp (I * ν * z) := by
  rw [mathieuMe_of_not_int hν]
  simp only [mathieuMeCoeff_of_not_int hν, m28b_data_zero hν]
  rw [tsum_eq_single 0 fun m hm => by simp [hm]]
  simp

/-- **Normalization** (DLMF 28.12.5): `∫₀^π me_ν(x, q) me_ν(-x, q) dx = π` for `ν ∉ ℤ` and `q`
normal along the segment. -/
@[dlmf 28.12.E5]
theorem integral_mathieuMe_mul_neg {ν q : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    (hq : MathieuNormalSegment ν q) :
    ∫ x in (0 : ℝ)..π, mathieuMe ν x q * mathieuMe ν (-x) q = π := by
  have hd := m28b_isMeCoeffSeq_data hq
  set c := (mathieuLambdaData ν q).2
  have hme : ∀ z, mathieuMe ν z q = ∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * z) := by
    intro z; rw [mathieuMe_of_not_int hν]; simp only [mathieuMeCoeff_of_not_int hν, c]
  have hsol := p1b_isMathieuSolution_series hd.1 hd.2.1
  simp only [hme]
  rw [p1b_integral_series_mul_neg hd.2.1 (hsol.differentiable.continuous.comp
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
  rw [mathieuMe_of_not_int (m28b_not_int_neg hν), mathieuMe_of_not_int hν]
  simp only [mathieuMeCoeff_of_not_int (m28b_not_int_neg hν), mathieuMeCoeff_of_not_int hν,
    m28b_data_neg_nu]
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
  have hd := m28b_isMeCoeffSeq_data hq
  set c := (mathieuLambdaData ν q).2
  have hme : ∀ z, mathieuMe ν z q = ∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * z) := by
    intro z; rw [mathieuMe_of_not_int hν]; simp only [mathieuMeCoeff_of_not_int hν, c]
  have hsol : IsMathieuSolution (mathieuLambda ν q) q (fun z => mathieuMe ν z q) := by
    rw [mathieuLambda_of_not_int hν]; simp only [hme]
    exact p1b_isMathieuSolution_series hd.1 hd.2.1
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
    have := p1b_isMathieuSolution_series (c := fun m => c (-m)) hrec' hs'
    rw [mathieuLambda_of_not_int hν]
    convert this using 2 with z
    rw [← mathieuMe_neg_nu hν, mathieuMe_of_not_int (m28b_not_int_neg hν)]
    simp only [mathieuMeCoeff_of_not_int (m28b_not_int_neg hν), m28b_data_neg_nu, c]
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
lemma p2x_integral_mul_eq_zero {a b q μ : ℂ} {f g : ℂ → ℂ} (hf : IsMathieuSolution a q f)
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
lemma p2x_integral_mathieuMe_orthogonal_of_ne {ν q : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    {m n : ℤ} (hm : MathieuNormalSegment (ν + 2 * m) q)
    (hn : MathieuNormalSegment (ν + 2 * n) q)
    (hne : mathieuLambda (ν + 2 * m) q ≠ mathieuLambda (ν + 2 * n) q) :
    ∫ x in (0 : ℝ)..π, mathieuMe (ν + 2 * m) x q * mathieuMe (ν + 2 * n) (-x) q = 0 := by
  obtain ⟨⟨h1, -, hp1⟩, -⟩ := isFloquetSolution_mathieuMe (m28b_not_int_add hν m) hm
  obtain ⟨-, ⟨h2, -, hp2⟩⟩ := isFloquetSolution_mathieuMe (m28b_not_int_add hν n) hn
  refine p2x_integral_mul_eq_zero h1 h2 (Complex.exp_ne_zero _) hp1 (fun z => ?_) hne
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
theorem p1b_charExp_of_floquet_pair {a q ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {w : ℂ → ℂ}
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
  (p1b_charExp_of_floquet_pair hν (isFloquetSolution_mathieuMe hν hq).1
    (isFloquetSolution_mathieuMe hν hq).2).2

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

/-- Iterated pseudoperiodicity: `w(z + nπ) = μⁿ w(z)`. -/
theorem p1b_add_nat_mul_pi {w : ℂ → ℂ} {μ : ℂ} (h : ∀ z, w (z + π) = μ * w z) (z : ℂ)
    (n : ℕ) : w (z + n * π) = μ ^ n * w z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show z + ((n + 1 : ℕ) : ℂ) * π = (z + n * π) + π by push_cast; ring, h, ih]; ring

/-- For `ν ∉ ℤ` the Floquet multipliers `e^{±iπν}` are distinct. -/
theorem p1b_exp_ne_inv {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) :
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
lemma p1b_floquet_periodic {a q ν : ℂ} {w : ℂ → ℂ} (hw : IsFloquetSolution a q ν w) {m : ℕ}
    (hm : Complex.exp (2 * m * π * I * ν) = 1) : Function.Periodic w (2 * m * π) := by
  intro z
  have := p1b_add_nat_mul_pi hw.2.2 z (2 * m)
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
  · exact p1b_floquet_periodic h h1
  rcases hw.isFloquet_or hw0 hc' with h | hu'
  · exact p1b_floquet_periodic h h2
  have pu := p1b_floquet_periodic hu h2
  have pu' := p1b_floquet_periodic hu' (by rw [neg_neg]; exact h1)
  have hD : Complex.exp (I * ν * π) - Complex.exp (I * -ν * π) ≠ 0 := by
    have := p1b_exp_ne_inv (ν := ν) hν
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

end DLMF.Mathieu
