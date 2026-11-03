/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Noninteger.Basic
public import DLMFMathlib.Analysis.SpecificLimits.QuarterRecurrence

/-!
# Continuation paths of the Fourier coefficients of `me_ν`

Along a continuation path `t ↦ (Λ(t), c_t)` of `λ_ν` and the coefficients `c^ν_{2m}` over the
segment `[0, q]` (`DLMF.Mathieu.IsMathieuLambdaPath`), the coefficients decay geometrically,
uniformly in `t`: the recurrence 28.14.4 is diagonally dominant for large `|m|`. Hence bilinear
forms `∑_j c_t(j) c'_t(j + d)` of two paths are continuous in `t`.

For two absolutely summable solutions `a`, `b` of 28.14.4 with respect to the same `ν ∉ ℤ` and
`q`, normalized by 28.14.5, the Casoratian `q (a_{j+1} b_j - a_j b_{j+1})` telescopes: if the
eigenvalues differ then `∑ a_j b_j = 0`, and if they agree the sequences are proportional and
`(∑ a_j b_j)² = 1`. Along the segment the bilinear form of the continuations of `λ_{ν+2m}` and
`λ_{ν+2n}` (`m ≠ n`) is therefore continuous with values in `{0, ±1}` and vanishes at `t = 0`,
so the two continued eigenvalues never meet. This gives the orthogonality 28.12.7.

## Main results

* `DLMF.Mathieu.IsMathieuLambdaPath.exists_bound_half_pow`: uniform geometric decay of the
  coefficients along a continuation path.
* `DLMF.Mathieu.IsMathieuLambdaPath.continuousOn_tsum_mul`: continuity of the bilinear form of
  two continuation paths.
* `DLMF.Mathieu.IsMeCoeffSeq.tsum_mul`: the bilinear relation of two coefficient sequences.
* `DLMF.Mathieu.IsMathieuLambdaPath.lambda_ne`: the continuations of `λ_{ν+2m}` and
  `λ_{ν+2n}`, `m ≠ n`, never meet along the segment.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real

namespace DLMF.Mathieu

namespace CoefficientPath

/-- The weights `(1/2)^{|j|}` are summable over `ℤ`. -/
theorem summable_half_pow_natAbs : Summable (fun j : ℤ => (1 / 2 : ℝ) ^ j.natAbs) := by
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  · simpa using summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)

end CoefficientPath

open CoefficientPath in
/-- **Uniform geometric decay along a continuation path**: the coefficients `c_t(j)` of a
continuation path are bounded by `C (1/2)^{|j|}` uniformly in `t ∈ [0, 1]`. -/
theorem IsMathieuLambdaPath.exists_bound_half_pow {ν q : ℂ} {Λ : ℝ → ℂ} {c : ℝ → ℤ → ℂ}
    (hp : IsMathieuLambdaPath ν q Λ c) :
    ∃ C, ∀ t ∈ Icc (0 : ℝ) 1, ∀ j : ℤ, ‖c t j‖ ≤ C * (1 / 2) ^ j.natAbs := by
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hp.continuousOn_lambda
  obtain ⟨J, hJ⟩ := exists_nat_ge (‖ν‖ + (L + 4 * ‖q‖ + 1))
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0 ⟨le_rfl, zero_le_one⟩)
  -- diagonal dominance for `|j| ≥ J`
  have hdom : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j : ℤ, (J : ℤ) ≤ |j| →
      ‖c t j‖ ≤ (‖c t (j + 1)‖ + ‖c t (j - 1)‖) / 4 := by
    intro t ht j hj
    have hrec := (hp.isMeCoeffSeq t ht).1 j
    have e : (Λ t - (ν + 2 * j) ^ 2) * c t j = (t * q) * (c t (j + 1) + c t (j - 1)) := by
      linear_combination -hrec
    have hn := congrArg norm e
    rw [norm_mul, norm_mul] at hn
    have htq : ‖(t : ℂ) * q‖ ≤ ‖q‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    have hjr : (J : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast hj
    have h2j : ‖(2 * j : ℂ)‖ = 2 * |(j : ℝ)| := by
      rw [norm_mul, Complex.norm_two, Complex.norm_intCast]
    have hnu : 2 * |(j : ℝ)| - ‖ν‖ ≤ ‖ν + 2 * j‖ := by
      have := norm_sub_le (ν + 2 * j) ν
      rw [add_sub_cancel_left, h2j] at this; linarith
    have hR : L + 4 * ‖q‖ + 1 ≤ ‖ν + 2 * j‖ := by linarith [norm_nonneg ν, norm_nonneg q]
    have h1 : (1 : ℝ) ≤ ‖ν + 2 * j‖ := by linarith [norm_nonneg q]
    have hsq : L + 4 * ‖q‖ + 1 ≤ ‖(ν + 2 * j) ^ 2‖ := by
      rw [norm_pow]; nlinarith
    have hD : 4 * ‖q‖ + 1 ≤ ‖Λ t - (ν + 2 * j) ^ 2‖ := by
      have := norm_sub_norm_le ((ν + 2 * j) ^ 2) (Λ t)
      rw [norm_sub_rev] at this
      linarith [hL t ht]
    have hS := norm_add_le (c t (j + 1)) (c t (j - 1))
    set x := ‖c t j‖
    set S := ‖c t (j + 1)‖ + ‖c t (j - 1)‖
    have hx : 0 ≤ x := norm_nonneg _
    have hS0 : 0 ≤ S := by positivity
    have hle : (4 * ‖q‖ + 1) * x ≤ ‖q‖ * S := by
      calc (4 * ‖q‖ + 1) * x ≤ ‖Λ t - (ν + 2 * j) ^ 2‖ * x := by gcongr
        _ = ‖(t : ℂ) * q‖ * ‖c t (j + 1) + c t (j - 1)‖ := hn
        _ ≤ ‖q‖ * S := by gcongr
    have hq0 := norm_nonneg q
    nlinarith
  -- bounds on the central block
  have hb := fun j => isCompact_Icc.exists_bound_of_continuousOn (hp.continuousOn_coeff j)
  choose Mf hMf using hb
  set M := ∑ j ∈ Finset.Icc (-(J : ℤ)) J, Mf j
  have hMf0 : ∀ j, 0 ≤ Mf j := fun j => (norm_nonneg _).trans (hMf j 0 ⟨le_rfl, zero_le_one⟩)
  have hMc : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j : ℤ, |j| ≤ J → ‖c t j‖ ≤ M := by
    intro t ht j hj
    refine (hMf j t ht).trans ?_
    exact Finset.single_le_sum (fun k _ => hMf0 k)
      (Finset.mem_Icc.mpr ⟨by rw [abs_le] at hj; omega, by rw [abs_le] at hj; omega⟩)
  refine ⟨M * 2 ^ J, fun t ht j => ?_⟩
  have hsum := (hp.isMeCoeffSeq t ht).2.1
  have hB : ∀ k, ‖c t k‖ ≤ ∑' i, ‖c t i‖ := fun k => hsum.le_tsum k (fun _ _ => norm_nonneg _)
  -- the two half-lines
  have hpos : ∀ k : ℕ, ‖c t k‖ ≤ M * 2 ^ J * (1 / 2) ^ k := by
    refine le_mul_half_pow_of_le_add_div_four (f := fun k : ℕ => ‖c t k‖)
      (fun _ => norm_nonneg _) (fun k => hB k) (fun k hk => ?_) (fun k hk => hMc t ht k (by
        rw [abs_of_nonneg (by positivity)]; exact_mod_cast hk))
    have := hdom t ht ((k : ℤ) + 1) (by rw [abs_of_nonneg (by positivity)]; omega)
    simp only [add_sub_cancel_right] at this
    push_cast
    rw [show (k : ℤ) + 2 = k + 1 + 1 by ring]
    linarith
  have hneg : ∀ k : ℕ, ‖c t (-k)‖ ≤ M * 2 ^ J * (1 / 2) ^ k := by
    refine le_mul_half_pow_of_le_add_div_four (f := fun k : ℕ => ‖c t (-k)‖)
      (fun _ => norm_nonneg _) (fun k => hB _) (fun k hk => ?_) (fun k hk => hMc t ht _ (by
        rw [abs_neg, abs_of_nonneg (by positivity)]; exact_mod_cast hk))
    have := hdom t ht (-((k : ℤ) + 1)) (by rw [abs_neg, abs_of_nonneg (by positivity)]; omega)
    rw [show -((k : ℤ) + 1) + 1 = -k by ring, show -((k : ℤ) + 1) - 1 = -(k + 2) by ring] at this
    push_cast
    linarith
  rcases Int.natAbs_eq j with h | h
  · have := hpos j.natAbs
    rwa [← h] at this
  · have := hneg j.natAbs
    rwa [← h] at this

/-- Shifting the index of a coefficient sequence by `d` replaces `ν` by `ν + 2d`. -/
theorem IsMeCoeffSeq.shift {ν q a : ℂ} {c : ℤ → ℂ} (hc : IsMeCoeffSeq ν q a c) (d : ℤ) :
    IsMeCoeffSeq (ν + 2 * d) q a (fun j => c (j + d)) := by
  refine ⟨fun j => ?_, (Equiv.addRight d).summable_iff.mpr hc.2.1,
    (Equiv.addRight d).hasSum_iff.mpr hc.2.2⟩
  have := hc.1 (j + d)
  rw [show j + d + 1 = j + 1 + d by ring, show j + d - 1 = j - 1 + d by ring] at this
  push_cast at this ⊢
  linear_combination this

/-- An absolutely summable sequence times a coefficient sequence is summable. -/
private lemma IsMeCoeffSeq.summable_mul {ν q a : ℂ} {b : ℤ → ℂ} (hb : IsMeCoeffSeq ν q a b)
    {f : ℤ → ℂ} (hf : Summable (fun j => ‖f j‖)) : Summable (fun j => f j * b j) := by
  refine Summable.of_norm_bounded (g := fun j => ‖f j‖ * ∑' i, ‖b i‖) (hf.mul_right _) ?_
  intro j
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb.2.1.le_tsum j (fun _ _ => norm_nonneg _)) (norm_nonneg _)

/-- The Casoratian `q (a_{j+1} b_j - a_j b_{j+1})` of two coefficient sequences: it is summable,
its increments are `(A - B) a_j b_j`, and `(A - B) ∑ a_j b_j = 0`. -/
private lemma IsMeCoeffSeq.casoratian {ν q A B : ℂ} {a b : ℤ → ℂ}
    (ha : IsMeCoeffSeq ν q A a) (hb : IsMeCoeffSeq ν q B b) :
    Summable (fun j => q * (a (j + 1) * b j - a j * b (j + 1))) ∧
    (∀ j, q * (a (j + 1) * b j - a j * b (j + 1)) - q * (a j * b (j - 1) - a (j - 1) * b j) =
      (A - B) * (a j * b j)) ∧ (A - B) * ∑' j, a j * b j = 0 := by
  obtain ⟨W, hWd⟩ : ∃ W : ℤ → ℂ, W = fun j => q * (a (j + 1) * b j - a j * b (j + 1)) := ⟨_, rfl⟩
  have hW : ∀ j, W j - W (j - 1) = (A - B) * (a j * b j) := by
    intro j
    simp only [hWd]; rw [sub_add_cancel]
    linear_combination b j * ha.1 j - a j * hb.1 j
  have ha1 : Summable (fun j => ‖a (j + 1)‖) := (Equiv.addRight (1 : ℤ)).summable_iff.mpr ha.2.1
  have hWs : Summable W := by
    have h1 := hb.summable_mul ha1
    have h2 := (hb.shift 1).summable_mul ha.2.1
    rw [hWd]
    exact (h1.sub h2).mul_left q
  have hab := hb.summable_mul ha.2.1
  have hWs' : Summable (fun j => W (j - 1)) := (Equiv.subRight (1 : ℤ)).summable_iff.mpr hWs
  have hmain : (A - B) * ∑' j, a j * b j = 0 := by
    rw [← hab.tsum_mul_left]
    simp only [← hW]
    rw [hWs.tsum_sub hWs']
    have := (Equiv.subRight (1 : ℤ)).tsum_eq W
    simp only [Equiv.subRight_apply] at this
    rw [this, sub_self]
  refine ⟨hWd ▸ hWs, fun j => ?_, hmain⟩
  have := hW j
  simp only [hWd, sub_add_cancel] at this
  exact this

/-- Two coefficient sequences with respect to the same `ν ∉ ℤ`, `q` and eigenvalue are
proportional. -/
private lemma IsMeCoeffSeq.exists_eq_mul {ν q A : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {a b : ℤ → ℂ}
    (ha : IsMeCoeffSeq ν q A a) (hb : IsMeCoeffSeq ν q A b) : ∃ α : ℂ, ∀ j, a j = α * b j := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, b j ≠ 0 := by
    by_contra hcon; push Not at hcon
    have := hb.2.2; simp only [hcon] at this
    exact one_ne_zero (this.unique (by simp))
  by_cases hq : q = 0
  · -- diagonal recurrence: both sequences live on a single index
    have hdiag : ∀ (c : ℤ → ℂ), IsMeCoeffSeq ν q A c → ∀ j, c j ≠ 0 → A = (ν + 2 * j) ^ 2 := by
      intro c hc j hj
      have := hc.1 j
      rw [hq] at this
      have : (A - (ν + 2 * j) ^ 2) * c j = 0 := by linear_combination -this
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hj)
    have hA := hdiag b hb j₀ hj₀
    have honly : ∀ (c : ℤ → ℂ), IsMeCoeffSeq ν q A c → ∀ j, j ≠ j₀ → c j = 0 := by
      intro c hc j hj
      by_contra hcj
      have h2 := hdiag c hc j hcj
      rw [hA] at h2
      have : (2 * (j₀ - j) : ℂ) * (2 * ν + 2 * j₀ + 2 * j) = 0 := by linear_combination h2
      rcases mul_eq_zero.mp this with h | h
      · exact hj (by exact_mod_cast (by linear_combination -h / 2 : (j : ℂ) = j₀))
      · exact hν (-(j₀ + j)) (by push_cast; linear_combination -h / 2)
    refine ⟨a j₀ / b j₀, fun j => ?_⟩
    by_cases hj : j = j₀
    · subst hj; field_simp
    · rw [honly a ha j hj, honly b hb j hj, mul_zero]
  obtain ⟨hWs, hW, -⟩ := ha.casoratian hb
  have hconst : ∀ j, q * (a (j + 1) * b j - a j * b (j + 1)) = q * (a 1 * b 0 - a 0 * b 1) := by
    intro j
    induction j using Int.induction_on with
    | zero => simp
    | succ i ih =>
      have := hW (i + 1)
      rw [sub_self, zero_mul, add_sub_cancel_right] at this
      rw [← ih]; linear_combination this
    | pred i ih =>
      have := hW (-i)
      rw [sub_self, zero_mul] at this
      rw [← ih, show -(i : ℤ) - 1 + 1 = -i by ring]; linear_combination -this
  have hW0 : q * (a 1 * b 0 - a 0 * b 1) = 0 :=
    (summable_const_iff _).mp (hWs.congr hconst)
  have hcas : ∀ j, a (j + 1) * b j = a j * b (j + 1) := by
    intro j
    have := hconst j
    rw [hW0] at this
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hq)
  set α := a j₀ / b j₀
  set e : ℤ → ℂ := fun j => a j - α * b j with he
  have he_rec : ∀ j, q * e (j + 1) - (A - (ν + 2 * j) ^ 2) * e j + q * e (j - 1) = 0 := by
    intro j; simp only [he]; linear_combination ha.1 j - α * hb.1 j
  have he0 : e j₀ = 0 := by simp only [he, α]; field_simp; ring
  have he1 : e (j₀ + 1) = 0 := by
    have h := hcas j₀
    have : e (j₀ + 1) * b j₀ = 0 := by
      simp only [he, α]; field_simp; linear_combination h
    exact (mul_eq_zero.mp this).resolve_right hj₀
  have hup : ∀ k : ℕ, e (j₀ + k) = 0 ∧ e (j₀ + k + 1) = 0 := by
    intro k
    induction k with
    | zero => simpa using ⟨he0, he1⟩
    | succ k ih =>
      refine ⟨by push_cast; rw [← add_assoc]; exact ih.2, ?_⟩
      have := he_rec (j₀ + k + 1)
      rw [ih.2, show j₀ + k + 1 - 1 = j₀ + k by ring, ih.1] at this
      have h' : q * e (j₀ + k + 1 + 1) = 0 := by linear_combination this
      push_cast; rw [← add_assoc]; exact (mul_eq_zero.mp h').resolve_left hq
  have hdown : ∀ k : ℕ, e (j₀ - k) = 0 ∧ e (j₀ - k + 1) = 0 := by
    intro k
    induction k with
    | zero => simpa using ⟨he0, he1⟩
    | succ k ih =>
      refine ⟨?_, by push_cast; rw [show j₀ - (k + 1) + 1 = j₀ - k by ring]; exact ih.1⟩
      have := he_rec (j₀ - k)
      rw [ih.1, ih.2] at this
      have h' : q * e (j₀ - k - 1) = 0 := by linear_combination this
      push_cast; rw [show j₀ - (k + 1) = j₀ - k - 1 by ring]
      exact (mul_eq_zero.mp h').resolve_left hq
  refine ⟨α, fun j => ?_⟩
  have : e j = 0 := by
    rcases le_or_gt j₀ j with h | h
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, j = j₀ + k := ⟨(j - j₀).toNat, by omega⟩
      rw [hk]; exact (hup k).1
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, j = j₀ - k := ⟨(j₀ - j).toNat, by omega⟩
      rw [hk]; exact (hdown k).1
  exact sub_eq_zero.mp this

/-- **Bilinear relation of two coefficient sequences** with respect to the same `ν ∉ ℤ` and
`q`: if the eigenvalues differ then `∑ a_j b_j = 0`; if they agree then `(∑ a_j b_j)² = 1`
(the sequences are then proportional, by the Casoratian of the recurrence 28.14.4). -/
theorem IsMeCoeffSeq.tsum_mul {ν q A B : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {a b : ℤ → ℂ}
    (ha : IsMeCoeffSeq ν q A a) (hb : IsMeCoeffSeq ν q B b) :
    (A ≠ B → ∑' j, a j * b j = 0) ∧ (A = B → (∑' j, a j * b j) ^ 2 = 1) := by
  refine ⟨fun hne => (mul_eq_zero.mp (ha.casoratian hb).2.2).resolve_left (sub_ne_zero.mpr hne),
    fun heq => ?_⟩
  subst heq
  obtain ⟨α, hα⟩ := ha.exists_eq_mul hν hb
  have hb2 := hb.2.2
  have ha2 := ha.2.2
  simp only [hα] at ha2 ⊢
  have e1 : (fun j => α * b j * b j) = fun j => α * b j ^ 2 := by funext j; ring
  have e2 : (fun j => (α * b j) ^ 2) = fun j => α ^ 2 * b j ^ 2 := by funext j; ring
  rw [e1, (hb2.mul_left α).tsum_eq, mul_one]
  rw [e2] at ha2
  have := ha2.unique (hb2.mul_left (α ^ 2))
  rw [this, mul_one]

/-- The bilinear form `∑ c_t(j) c'_t(j + d)` of two continuation paths is continuous on
`[0, 1]`. -/
theorem IsMathieuLambdaPath.continuousOn_tsum_mul {ν ν' q : ℂ} {Λ Λ' : ℝ → ℂ}
    {c c' : ℝ → ℤ → ℂ} (hp : IsMathieuLambdaPath ν q Λ c) (hp' : IsMathieuLambdaPath ν' q Λ' c')
    (d : ℤ) : ContinuousOn (fun t => ∑' j, c t j * c' t (j + d)) (Icc 0 1) := by
  obtain ⟨C, hC⟩ := hp.exists_bound_half_pow
  obtain ⟨C', hC'⟩ := hp'.exists_bound_half_pow
  have hC0 : 0 ≤ C' := by
    have := (norm_nonneg _).trans (hC' 0 ⟨le_rfl, zero_le_one⟩ 0); simpa using this
  refine continuousOn_tsum (u := fun j => C * C' * (1 / 2 : ℝ) ^ j.natAbs)
    (fun j => (hp.continuousOn_coeff j).mul (hp'.continuousOn_coeff (j + d)))
    (CoefficientPath.summable_half_pow_natAbs.mul_left _) (fun j t ht => ?_)
  rw [norm_mul]
  have h1 := hC t ht j
  have h2 : ‖c' t (j + d)‖ ≤ C' := by
    refine (hC' t ht (j + d)).trans ?_
    exact mul_le_of_le_one_right hC0 (pow_le_one₀ (by norm_num) (by norm_num))
  calc ‖c t j‖ * ‖c' t (j + d)‖ ≤ C * (1 / 2) ^ j.natAbs * C' :=
        mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    _ = C * C' * (1 / 2) ^ j.natAbs := by ring

/-- **No crossing of continued eigenvalues**: for `ν ∉ ℤ` and `m ≠ n`, the continuations of
`λ_{ν+2m}` and `λ_{ν+2n}` along the segment `[0, q]` never meet. Along the path the bilinear
form `∑ c^{(m)}_j c^{(n)}_{j+m-n}` is continuous, vanishes where the eigenvalues differ and has
square `1` where they agree; it vanishes at `t = 0`. -/
theorem IsMathieuLambdaPath.lambda_ne {ν q : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {m n : ℤ}
    (hmn : m ≠ n) {Λ₁ Λ₂ : ℝ → ℂ} {c₁ c₂ : ℝ → ℤ → ℂ}
    (h₁ : IsMathieuLambdaPath (ν + 2 * m) q Λ₁ c₁) (h₂ : IsMathieuLambdaPath (ν + 2 * n) q Λ₂ c₂)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : Λ₁ t ≠ Λ₂ t := by
  set B : ℝ → ℂ := fun t => ∑' j, c₁ t j * c₂ t (j + (m - n))
  have hμ : ∀ k : ℤ, (k : ℂ) ≠ ν + 2 * m := fun k h => hν (k - 2 * m) (by push_cast; rw [h]; ring)
  have hrel : ∀ s ∈ Icc (0 : ℝ) 1,
      (Λ₁ s ≠ Λ₂ s → B s = 0) ∧ (Λ₁ s = Λ₂ s → B s ^ 2 = 1) := by
    intro s hs
    have hsh := (h₂.isMeCoeffSeq s hs).shift (m - n)
    rw [show ν + 2 * n + 2 * ((m - n : ℤ) : ℂ) = ν + 2 * m by push_cast; ring] at hsh
    exact (h₁.isMeCoeffSeq s hs).tsum_mul hμ hsh
  have hB0 : B 0 = 0 := by
    refine (hrel 0 ⟨le_rfl, zero_le_one⟩).1 ?_
    rw [h₁.lambda_zero, h₂.lambda_zero]
    intro h
    have : (2 * (m - n) : ℂ) * (2 * ν + 2 * m + 2 * n) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h | h
    · exact hmn (by exact_mod_cast (by linear_combination h / 2 : (m : ℂ) = n))
    · exact hν (-(m + n)) (by push_cast; linear_combination -h / 2)
  intro heq
  have hBt := (hrel t ht).2 heq
  have hnt : ‖B t‖ = 1 := by
    have := congrArg norm hBt
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  have hcont : ContinuousOn (fun s => ‖B s‖) (Icc 0 t) :=
    (continuous_norm.comp_continuousOn (h₁.continuousOn_tsum_mul h₂ (m - n))).mono
      (Icc_subset_Icc le_rfl ht.2)
  obtain ⟨s, hs, hs'⟩ := intermediate_value_Icc ht.1 hcont
    (show (1 / 2 : ℝ) ∈ Icc ‖B 0‖ ‖B t‖ by rw [hB0, hnt, norm_zero]; norm_num)
  have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
  by_cases hl : Λ₁ s = Λ₂ s
  · have := congrArg norm ((hrel s hs1).2 hl)
    simp only at hs'
    rw [norm_pow, hs', norm_one] at this; norm_num at this
  · simp only at hs'
    rw [(hrel s hs1).1 hl, norm_zero] at hs'; norm_num at hs'

end DLMF.Mathieu
