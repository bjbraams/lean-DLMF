/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Convex.Deriv

/-!
# Inequalities (DLMF §1.7)

The inequalities of Cauchy–Schwarz, Hölder and Minkowski for finite sums (1.7.1–1.7.3) and
for integrals (1.7.4–1.7.6), the inequalities between means (1.7.7) and Jensen's inequality
(1.7.10) are in Mathlib (pointers in `DLMF.AlgebraicAnalytic.Calculus.MathlibCoverage`). This
file states the remaining parts: the equality cases, the converse statements, the reversed
Minkowski inequality for `0 < p < 1`, the power-mean inequalities 1.7.8–1.7.9 and DLMF's form
of Jensen's inequality on an open interval, together with 1.7.11.

**Equality cases.** For sums DLMF writes "equality iff `aⱼ = c bⱼ`" (1.7.1, 1.7.3) and
"`aⱼᵖ = c bⱼ^q`" (1.7.2); this misses `b = 0`, `a ≠ 0`, where equality holds. We use the
symmetric form of DLMF's integral statements: `A aⱼ = B bⱼ` with `A`, `B` not both zero.

**1.7.11.** DLMF prints the strict inequality `exp(∫₀¹ ln f) < ∫₀¹ f`, which fails for constant
`f`. We prove `≤` (`exp_integral_log_le_integral`) and state the strict inequality for `f` not
almost everywhere constant.

The means of §1.2(iv) are written out explicitly: `A = (∑ aⱼ)/n`, `G = (∏ aⱼ)^{1/n}`,
`1/H = (∑ 1/aⱼ)/n`, and `M(r) = (∑ pⱼ aⱼ^r)^{1/r}` (weights `pⱼ > 0`, `∑ pⱼ = 1`).
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Finset
open scoped Topology

namespace DLMF.AlgebraicAnalytic

/-! ### §1.7(i) Finite sums -/

/-- DLMF 1.7.1, equality case (corrected): `(∑ aⱼbⱼ)² = (∑ aⱼ²)(∑ bⱼ²)` iff `A aⱼ = B bⱼ` for
all `j`, with constants `A`, `B` not both zero. -/
@[dlmf 1.7.E1]
theorem sq_sum_mul_eq_iff {n : ℕ} (a b : Fin n → ℝ) :
    (∑ j, a j * b j) ^ 2 = (∑ j, a j ^ 2) * (∑ j, b j ^ 2) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ j, A * a j = B * b j := by
  sorry

/-- DLMF §1.7(i), converse of the Cauchy–Schwarz inequality: if `A, B > 0` and
`(∑ aⱼbⱼ)² ≤ AB` for all `b` with `∑ bⱼ² ≤ B`, then `∑ aⱼ² ≤ A`. -/
@[dlmf 1.7.i]
theorem sum_sq_le_of_forall_sq_sum_mul_le {n : ℕ} (a : Fin n → ℝ) {A B : ℝ} (hA : 0 < A)
    (hB : 0 < B)
    (h : ∀ b : Fin n → ℝ, ∑ j, b j ^ 2 ≤ B → (∑ j, a j * b j) ^ 2 ≤ A * B) :
    ∑ j, a j ^ 2 ≤ A := by
  set S := ∑ j, a j ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg (a j)
  rcases eq_or_lt_of_le hS0 with h0 | hpos
  · rw [← h0]
    exact hA.le
  set t := Real.sqrt (B / S)
  have ht2 : t ^ 2 = B / S := Real.sq_sqrt (div_nonneg hB.le hS0)
  have hb : ∑ j, (t * a j) ^ 2 ≤ B := by
    have : ∑ j, (t * a j) ^ 2 = t ^ 2 * S := by
      rw [hS, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, ht2, div_mul_cancel₀ _ hpos.ne']
  have := h (fun j => t * a j) hb
  have e : (∑ j, a j * (t * a j)) ^ 2 = t ^ 2 * S * S := by
    have : ∑ j, a j * (t * a j) = t * S := by
      rw [hS, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    ring
  rw [e, ht2, div_mul_cancel₀ _ hpos.ne'] at this
  nlinarith

/-- DLMF 1.7.2, equality case (corrected): for `p > 1`, `1/p + 1/q = 1` and `aⱼ, bⱼ ≥ 0`,
equality holds in Hölder's inequality iff `A aⱼᵖ = B bⱼ^q` for all `j`, with `A`, `B` not both
zero. -/
@[dlmf 1.7.E2]
theorem inner_eq_Lp_mul_Lq_iff {n : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    ∑ j, a j * b j = (∑ j, a j ^ p) ^ (1 / p) * (∑ j, b j ^ q) ^ (1 / q) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ j, A * a j ^ p = B * b j ^ q := by
  sorry

/-- DLMF §1.7(i), converse of Hölder's inequality: for `p > 1`, `1/p + 1/q = 1`, `aⱼ ≥ 0` and
`A, B > 0`, if `∑ aⱼbⱼ ≤ A^{1/p} B^{1/q}` for all `bⱼ ≥ 0` with `∑ bⱼ^q ≤ B`, then
`∑ aⱼᵖ ≤ A`. -/
@[dlmf 1.7.i]
theorem sum_rpow_le_of_forall_inner_le {n : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (a : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h : ∀ b : Fin n → ℝ, (∀ j, 0 ≤ b j) → ∑ j, b j ^ q ≤ B →
      ∑ j, a j * b j ≤ A ^ (1 / p) * B ^ (1 / q)) :
    ∑ j, a j ^ p ≤ A := by
  sorry

/-- DLMF 1.7.3, reversed Minkowski inequality: for `0 < p < 1` and `aⱼ, bⱼ ≥ 0`,
`(∑ (aⱼ + bⱼ)ᵖ)^{1/p} ≥ (∑ aⱼᵖ)^{1/p} + (∑ bⱼᵖ)^{1/p}`. -/
@[dlmf 1.7.E3]
theorem Lp_add_ge_of_lt_one {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (a b : Fin n → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    (∑ j, a j ^ p) ^ (1 / p) + (∑ j, b j ^ p) ^ (1 / p) ≤
      (∑ j, (a j + b j) ^ p) ^ (1 / p) := by
  sorry

/-- DLMF 1.7.3, equality case (corrected): for `p > 0`, `p ≠ 1` and `aⱼ, bⱼ ≥ 0`, equality holds
in Minkowski's inequality iff `A aⱼ = B bⱼ` for all `j`, with `A`, `B` not both zero. -/
@[dlmf 1.7.E3]
theorem Lp_add_eq_iff {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≠ 1) (a b : Fin n → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    (∑ j, (a j + b j) ^ p) ^ (1 / p) = (∑ j, a j ^ p) ^ (1 / p) + (∑ j, b j ^ p) ^ (1 / p) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ j, A * a j = B * b j := by
  sorry

/-! ### §1.7(ii) Integrals -/

/-- DLMF 1.7.4 (Cauchy–Schwarz inequality for integrals): for `f`, `g` square integrable on
`(a, b)` (possibly infinite), `(∫ fg)² ≤ ∫ f² ∫ g²`. -/
@[dlmf 1.7.E4]
theorem sq_integral_mul_le {f g : ℝ → ℝ} {s : Set ℝ} (hf : MemLp f 2 (volume.restrict s))
    (hg : MemLp g 2 (volume.restrict s)) :
    (∫ x in s, f x * g x) ^ 2 ≤ (∫ x in s, f x ^ 2) * ∫ x in s, g x ^ 2 := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hf' : MemLp (fun x => |f x|) (ENNReal.ofReal 2) (volume.restrict s) := by
    rw [ENNReal.ofReal_ofNat]; exact hf.abs
  have hg' : MemLp (fun x => |g x|) (ENNReal.ofReal 2) (volume.restrict s) := by
    rw [ENNReal.ofReal_ofNat]; exact hg.abs
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall fun x => abs_nonneg (f x))
    (Eventually.of_forall fun x => abs_nonneg (g x)) hf' hg'
  simp only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] at h
  have hA : 0 ≤ ∫ x in s, f x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ ∫ x in s, g x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have habs : |∫ x in s, f x * g x| ≤ ∫ x in s, |f x| * |g x| := by
    simpa [abs_mul] using abs_integral_le_integral_abs (f := fun x => f x * g x)
      (μ := volume.restrict s)
  have h2 := habs.trans h
  calc (∫ x in s, f x * g x) ^ 2 = |∫ x in s, f x * g x| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt (∫ x in s, f x ^ 2) * Real.sqrt (∫ x in s, g x ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h2 2
    _ = (∫ x in s, f x ^ 2) * ∫ x in s, g x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]

/-- DLMF 1.7.4, equality case: equality holds iff `A f = B g` almost everywhere, with `A`, `B`
not both zero (DLMF: "for all `x`"). -/
@[dlmf 1.7.E4]
theorem sq_integral_mul_eq_iff {f g : ℝ → ℝ} {s : Set ℝ} (hf : MemLp f 2 (volume.restrict s))
    (hg : MemLp g 2 (volume.restrict s)) :
    (∫ x in s, f x * g x) ^ 2 = (∫ x in s, f x ^ 2) * (∫ x in s, g x ^ 2) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ᵐ x ∂(volume.restrict s), A * f x = B * g x := by
  sorry

/-- DLMF 1.7.5, equality case: for `p > 1`, `1/p + 1/q = 1` and `f, g ≥ 0` with `fᵖ`, `g^q`
integrable, equality holds in Hölder's inequality iff `A fᵖ = B g^q` almost everywhere, with
`A`, `B` not both zero. -/
@[dlmf 1.7.E5]
theorem integral_mul_eq_Lp_mul_Lq_iff {f g : ℝ → ℝ} {s : Set ℝ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict s))
    (hg : MemLp g (ENNReal.ofReal q) (volume.restrict s)) :
    ∫ x in s, f x * g x =
        (∫ x in s, f x ^ p) ^ (1 / p) * (∫ x in s, g x ^ q) ^ (1 / q) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ᵐ x ∂(volume.restrict s), A * f x ^ p = B * g x ^ q := by
  sorry

/-- DLMF 1.7.6 (Minkowski's inequality for integrals, real form): for `p > 1` and `f, g ≥ 0`
in `Lᵖ(a, b)`, `(∫ (f + g)ᵖ)^{1/p} ≤ (∫ fᵖ)^{1/p} + (∫ gᵖ)^{1/p}`. -/
@[dlmf 1.7.E6]
theorem integral_add_rpow_le {f g : ℝ → ℝ} {s : Set ℝ} {p : ℝ} (hp : 1 < p)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict s))
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict s)) :
    (∫ x in s, (f x + g x) ^ p) ^ (1 / p) ≤
      (∫ x in s, f x ^ p) ^ (1 / p) + (∫ x in s, g x ^ p) ^ (1 / p) := by
  sorry

/-- DLMF 1.7.6, reversed for `0 < p < 1`: for `f, g ≥ 0` with `fᵖ`, `gᵖ` integrable,
`(∫ (f + g)ᵖ)^{1/p} ≥ (∫ fᵖ)^{1/p} + (∫ gᵖ)^{1/p}`. -/
@[dlmf 1.7.E6]
theorem integral_add_rpow_ge_of_lt_one {f g : ℝ → ℝ} {s : Set ℝ} {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : IntegrableOn (fun x => f x ^ p) s) (hg : IntegrableOn (fun x => g x ^ p) s) :
    (∫ x in s, f x ^ p) ^ (1 / p) + (∫ x in s, g x ^ p) ^ (1 / p) ≤
      (∫ x in s, (f x + g x) ^ p) ^ (1 / p) := by
  sorry

/-- DLMF 1.7.6, equality case: for `p > 0`, `p ≠ 1`, equality holds in Minkowski's inequality
iff `A f = B g` almost everywhere, with `A`, `B` not both zero. -/
@[dlmf 1.7.E6]
theorem integral_add_rpow_eq_iff {f g : ℝ → ℝ} {s : Set ℝ} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≠ 1)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : IntegrableOn (fun x => f x ^ p) s) (hg : IntegrableOn (fun x => g x ^ p) s) :
    (∫ x in s, (f x + g x) ^ p) ^ (1 / p) =
        (∫ x in s, f x ^ p) ^ (1 / p) + (∫ x in s, g x ^ p) ^ (1 / p) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ᵐ x ∂(volume.restrict s), A * f x = B * g x := by
  sorry

/-! ### §1.7(iii) Means -/

/-- DLMF 1.7.7: for positive `a₁, …, aₙ`, `H ≤ G ≤ A`. -/
@[dlmf 1.7.E7]
theorem harmMean_le_geomMean_le_arithMean {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ j, 0 < a j) :
    (n : ℝ) / ∑ j, 1 / a j ≤ (∏ j, a j) ^ (1 / (n : ℝ)) ∧
      (∏ j, a j) ^ (1 / (n : ℝ)) ≤ (∑ j, a j) / n := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have h1 := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 : ℝ)) a (by simp)
    (by simp [hn]) (fun j _ => (ha j).le)
  have h2 := Real.harm_mean_le_geom_mean Finset.univ hne (fun _ => (1 : ℝ)) a (by simp)
    (by simp [hn]) (fun j _ => ha j)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, one_mul] at h1 h2
  exact ⟨by simpa [one_div] using h2, by simpa [one_div] using h1⟩

/-- Helper: `G = A` iff all entries agree. -/
lemma g1b_GA {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) :
    (∏ j, a j) ^ (1 / (n : ℝ)) = (∑ j, a j) / n ↔ ∀ i j, a i = a j := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.geom_mean_eq_arith_mean_weighted_iff_of_pos (s := Finset.univ)
    (fun _ => 1 / (n : ℝ)) a (fun _ _ => by positivity) (by simp; field_simp) (fun j _ => (ha j).le)
  rw [Real.finsetProd_rpow _ _ (fun j _ => (ha j).le), ← Finset.mul_sum] at h
  rw [show (∑ j, a j) / n = 1 / n * ∑ j, a j by ring, h]
  simp

/-- Helper: `H = G` iff all entries agree. -/
lemma g1b_HG {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) :
    (n : ℝ) / ∑ j, 1 / a j = (∏ j, a j) ^ (1 / (n : ℝ)) ↔ ∀ i j, a i = a j := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := g1b_GA hn (fun j => 1 / a j) (fun j => by have := ha j; positivity)
  have hP : 0 < ∏ j, a j := Finset.prod_pos fun j _ => ha j
  have hS : 0 < ∑ j, 1 / a j :=
    Finset.sum_pos (fun j _ => by have := ha j; positivity) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hG : 0 < (∏ j, a j) ^ (1 / (n : ℝ)) := Real.rpow_pos_of_pos hP _
  have e : (∏ j, 1 / a j) ^ (1 / (n : ℝ)) = 1 / (∏ j, a j) ^ (1 / (n : ℝ)) := by
    rw [Finset.prod_div_distrib, Finset.prod_const_one, Real.div_rpow zero_le_one hP.le,
      Real.one_rpow]
  rw [e] at h
  have : (∀ i j, 1 / a i = 1 / a j) ↔ ∀ i j, a i = a j := by
    constructor
    · intro H i j; have := H i j; simpa [one_div, inv_inj] using this
    · intro H i j; rw [H i j]
  rw [← this, ← h]
  constructor
  · intro H; rw [← H]; field_simp
  · intro H; field_simp at H ⊢; linarith

/-- DLMF 1.7.7, equality case: `G = A`, and likewise `H = G`, iff `a₁ = ⋯ = aₙ`. -/
@[dlmf 1.7.E7]
theorem geomMean_eq_arithMean_iff {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) :
    ((∏ j, a j) ^ (1 / (n : ℝ)) = (∑ j, a j) / n ↔ ∀ i j, a i = a j) ∧
      ((n : ℝ) / ∑ j, 1 / a j = (∏ j, a j) ^ (1 / (n : ℝ)) ↔ ∀ i j, a i = a j) :=
  ⟨g1b_GA hn a ha, g1b_HG hn a ha⟩

/-- DLMF 1.7.8: for `r ≠ 0`, positive `aⱼ` and weights `pⱼ > 0` with `∑ pⱼ = 1`, the
weighted mean `M(r) = (∑ pⱼ aⱼ^r)^{1/r}` lies between `min aⱼ` and `max aⱼ`, with equality
(on either side) iff `a₁ = ⋯ = aₙ`. (DLMF's further case `r < 0` with some `aⱼ = 0` is the
convention `M(r) = 0 = min aⱼ` of 1.2.22.) -/
@[dlmf 1.7.E8]
theorem min_le_powerMean_le_max {n : ℕ} (hn : (Finset.univ : Finset (Fin n)).Nonempty)
    (w a : Fin n → ℝ) (hw : ∀ j, 0 < w j) (hw1 : ∑ j, w j = 1) (ha : ∀ j, 0 < a j) {r : ℝ}
    (hr : r ≠ 0) :
    Finset.univ.inf' hn a ≤ (∑ j, w j * a j ^ r) ^ (1 / r) ∧
      (∑ j, w j * a j ^ r) ^ (1 / r) ≤ Finset.univ.sup' hn a ∧
      ((Finset.univ.inf' hn a = (∑ j, w j * a j ^ r) ^ (1 / r) ∨
          (∑ j, w j * a j ^ r) ^ (1 / r) = Finset.univ.sup' hn a) ↔ ∀ i j, a i = a j) := by
  sorry

/-- DLMF 1.7.9: for positive `aⱼ`, weights `pⱼ > 0` with `∑ pⱼ = 1`, and nonzero `r < s`,
`M(r) ≤ M(s)`, with equality iff all `aⱼ` are equal. -/
@[dlmf 1.7.E9]
theorem powerMean_le_powerMean {n : ℕ} (w a : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (hw1 : ∑ j, w j = 1) (ha : ∀ j, 0 < a j) {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0)
    (hrs : r < s) :
    (∑ j, w j * a j ^ r) ^ (1 / r) ≤ (∑ j, w j * a j ^ s) ^ (1 / s) ∧
      ((∑ j, w j * a j ^ r) ^ (1 / r) = (∑ j, w j * a j ^ s) ^ (1 / s) ↔
        ∀ i j, a i = a j) := by
  sorry

/-! ### §1.7(iv) Jensen's inequality -/

/-- DLMF 1.7.10 (Jensen's inequality): for `f` integrable on `[0, 1]` with `a < f(x) < b` and
`φ` convex on `(a, b)`, `φ(∫₀¹ f) ≤ ∫₀¹ φ(f)`; `φ ∘ f` is assumed integrable. -/
@[dlmf 1.7.E10]
theorem convexOn_Ioo_map_integral_le {f φ : ℝ → ℝ} {a b : ℝ} (hφ : ConvexOn ℝ (Ioo a b) φ)
    (hf : IntegrableOn f (Icc 0 1)) (hfab : ∀ x ∈ Icc (0 : ℝ) 1, f x ∈ Ioo a b)
    (hφf : IntegrableOn (fun x => φ (f x)) (Icc 0 1)) :
    φ (∫ x in (0 : ℝ)..1, f x) ≤ ∫ x in (0 : ℝ)..1, φ (f x) := by
  have hfi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (hf.mono_set Ioc_subset_Icc_self)
  have hφi : IntervalIntegrable (fun x => φ (f x)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (hφf.mono_set Ioc_subset_Icc_self)
  set m := ∫ x in (0 : ℝ)..1, f x with hmdef
  have hma : a < m := by
    have := intervalIntegral.intervalIntegral_pos_of_pos_on (hfi.sub intervalIntegrable_const)
      (fun x hx => sub_pos.mpr (hfab x (Ioo_subset_Icc_self hx)).1) (zero_lt_one' ℝ)
    rw [intervalIntegral.integral_sub hfi intervalIntegrable_const] at this
    simpa using this
  have hmb : m < b := by
    have := intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_const.sub hfi)
      (fun x hx => sub_pos.mpr (hfab x (Ioo_subset_Icc_self hx)).2) (zero_lt_one' ℝ)
    rw [intervalIntegral.integral_sub intervalIntegrable_const hfi] at this
    simpa using this
  have hmi : m ∈ interior (Ioo a b) := by rw [interior_Ioo]; exact ⟨hma, hmb⟩
  set sl := derivWithin φ (Ioi m) m
  have hsupp : ∀ y ∈ Ioo a b, φ m + sl * (y - m) ≤ φ y := by
    intro y hy
    rcases lt_trichotomy y m with hym | rfl | hym
    · have h1 := hφ.slope_le_leftDeriv_of_mem_interior hy hmi hym
      have h2 := hφ.leftDeriv_le_rightDeriv_of_mem_interior hmi
      have h3 : slope φ y m ≤ sl := h1.trans h2
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hym)] at h3
      nlinarith
    · simp
    · have h3 : sl ≤ slope φ m y := hφ.rightDeriv_le_slope_of_mem_interior hmi hy hym
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hym)] at h3
      linarith
  have hgi : IntervalIntegrable (fun x => φ m + sl * (f x - m)) volume 0 1 :=
    intervalIntegrable_const.add ((hfi.sub intervalIntegrable_const).const_mul sl)
  have hle := intervalIntegral.integral_mono_on zero_le_one hgi hφi
    (fun x hx => hsupp (f x) (hfab x hx))
  rw [intervalIntegral.integral_add intervalIntegrable_const
      ((hfi.sub intervalIntegrable_const).const_mul sl), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hfi intervalIntegrable_const, ← hmdef] at hle
  simpa using hle

/-- DLMF 1.7.11 (corrected to `≤`): for `f > 0` on `[0, 1]` with `f` and `ln f` integrable,
`exp(∫₀¹ ln f) ≤ ∫₀¹ f`. DLMF prints `<`, which fails for constant `f`; see
`exp_integral_log_lt_integral` for the strict form. -/
@[dlmf 1.7.E11]
theorem exp_integral_log_le_integral {f : ℝ → ℝ} (hf0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 < f x)
    (hf : IntegrableOn f (Icc 0 1)) (hlog : IntegrableOn (fun x => Real.log (f x)) (Icc 0 1)) :
    Real.exp (∫ x in (0 : ℝ)..1, Real.log (f x)) ≤ ∫ x in (0 : ℝ)..1, f x := by
  have hfi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (hf.mono_set Ioc_subset_Icc_self)
  have hli : IntervalIntegrable (fun x => Real.log (f x)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (hlog.mono_set Ioc_subset_Icc_self)
  set m := ∫ x in (0 : ℝ)..1, f x
  have hm : 0 < m := intervalIntegral.intervalIntegral_pos_of_pos_on hfi
    (fun x hx => hf0 x (Ioo_subset_Icc_self hx)) zero_lt_one
  have hpt : ∀ x ∈ Icc (0 : ℝ) 1, Real.log (f x) ≤ Real.log m + (f x / m - 1) := by
    intro x hx
    have h := Real.log_le_sub_one_of_pos (div_pos (hf0 x hx) hm)
    rw [Real.log_div (hf0 x hx).ne' hm.ne'] at h
    linarith
  have hgi : IntervalIntegrable (fun x => Real.log m + (f x / m - 1)) volume 0 1 :=
    intervalIntegrable_const.add ((hfi.div_const m).sub intervalIntegrable_const)
  have hle := intervalIntegral.integral_mono_on zero_le_one hli hgi hpt
  rw [intervalIntegral.integral_add intervalIntegrable_const
      ((hfi.div_const m).sub intervalIntegrable_const),
    intervalIntegral.integral_sub (hfi.div_const m) intervalIntegrable_const,
    intervalIntegral.integral_div, div_self hm.ne'] at hle
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul, sub_self,
    add_zero] at hle
  calc Real.exp (∫ x in (0 : ℝ)..1, Real.log (f x)) ≤ Real.exp (Real.log m) :=
        Real.exp_le_exp.mpr hle
    _ = m := Real.exp_log hm

/-- DLMF 1.7.11 (strict form): if moreover `f` is not almost everywhere constant on `[0, 1]`,
then `exp(∫₀¹ ln f) < ∫₀¹ f`. -/
@[dlmf 1.7.E11]
theorem exp_integral_log_lt_integral {f : ℝ → ℝ} (hf0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 < f x)
    (hf : IntegrableOn f (Icc 0 1)) (hlog : IntegrableOn (fun x => Real.log (f x)) (Icc 0 1))
    (hnc : ¬ ∃ c, ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), f x = c) :
    Real.exp (∫ x in (0 : ℝ)..1, Real.log (f x)) < ∫ x in (0 : ℝ)..1, f x := by
  sorry

end DLMF.AlgebraicAnalytic
