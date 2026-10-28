/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Asymptotics
public import DLMF.BernoulliEuler.Series
public import DLMFMathlib.NumberTheory.EulerPolynomials
public import Mathlib.NumberTheory.ZetaValues

/-!
# Real zeros of Bernoulli polynomials

Zero enumerations, Rolle arguments and bounds for the first real Bernoulli zeros.

Source references and common attribution are retained in
`DLMF.BernoulliEuler.Zeros`.
-/

@[expose] public noncomputable section

open Filter Asymptotics Topology Polynomial

open scoped Nat Real

namespace DLMF.BernoulliEuler

/-- The real zeros in `[1/2, ∞)` of a real polynomial, increasing, with multiplicity. -/
def b24b_zerosGE (p : ℝ[X]) : List ℝ :=
  (p.roots.filter (fun x => 1 / 2 ≤ x)).sort (· ≤ ·)

/-- DLMF 24.12.1: the real zeros `x_1^{(n)} ≤ x_2^{(n)} ≤ ⋯` of `Bₙ(x)` in `[1/2, ∞)`,
increasing and counted with multiplicity. -/
@[dlmf 24.12.E1]
def bernoulliRealZerosGE (n : ℕ) : List ℝ :=
  b24b_zerosGE ((Polynomial.bernoulli n).map (algebraMap ℚ ℝ))

/-- DLMF §24.12(i): `x_j^{(n)}`, the `j`-th real zero of `Bₙ` in `[1/2, ∞)` (`j ≥ 1`); the
totalized value `0` is returned when there is no such zero. -/
@[dlmf 24.12.E1]
def bernoulliRealZero (n j : ℕ) : ℝ := (bernoulliRealZerosGE n).getD (j - 1) 0

/-- DLMF §24.12(i): `R(n)`, the total number of real zeros of `Bₙ(x)` (with multiplicity). -/
@[dlmf 24.12.i]
def bernoulliRealZeroCount (n : ℕ) : ℕ :=
  ((Polynomial.bernoulli n).map (algebraMap ℚ ℝ)).roots.card

/-- DLMF 24.12.7: the real zeros `y_1^{(n)} ≤ y_2^{(n)} ≤ ⋯` of `Eₙ(x)` in `[1/2, ∞)`,
increasing and counted with multiplicity. -/
@[dlmf 24.12.E7]
def eulerRealZerosGE (n : ℕ) : List ℝ :=
  b24b_zerosGE ((Polynomial.euler n).map (algebraMap ℚ ℝ))

/-- DLMF §24.12(ii): `y_j^{(n)}`, the `j`-th real zero of `Eₙ` in `[1/2, ∞)` (`j ≥ 1`); the
totalized value `0` is returned when there is no such zero. -/
@[dlmf 24.12.E7]
def eulerRealZero (n j : ℕ) : ℝ := (eulerRealZerosGE n).getD (j - 1) 0

/-! ### Basic properties of the zero lists -/

/-- Estimate under the stated parameter and domain assumptions: `(b24b_zerosGE p).Pairwise (· ≤
·)`. -/
lemma b24b_zerosGE_sorted (p : ℝ[X]) : (b24b_zerosGE p).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort _ _

/-- Estimate under the stated parameter and domain assumptions: `x ∈ b24b_zerosGE p ↔ 1 / 2 ≤ x ∧
p.eval x = 0`. -/
lemma b24b_mem_zerosGE {p : ℝ[X]} (hp : p ≠ 0) {x : ℝ} :
    x ∈ b24b_zerosGE p ↔ 1 / 2 ≤ x ∧ p.eval x = 0 := by
  rw [b24b_zerosGE, Multiset.mem_sort, Multiset.mem_filter, mem_roots hp, IsRoot.def, and_comm]

/-- Nonvanishing under the stated hypotheses: `Polynomial.bernoulli n ≠ 0`. -/
lemma b24b_bernoulli_ne_zero (n : ℕ) : Polynomial.bernoulli n ≠ 0 := by
  intro h
  have := congrArg (fun p => p.coeff n) h
  simp [coeff_bernoulli] at this

/-- Nonvanishing under the stated hypotheses: `Polynomial.euler n ≠ 0`. -/
lemma b24b_euler_ne_zero (n : ℕ) : Polynomial.euler n ≠ 0 := by
  intro h
  have h1 := euler_comp_X_add_one_add n
  rw [h, zero_comp, add_zero] at h1
  have := congrArg (fun p => p.coeff n) h1
  simp at this

/-- DLMF 24.12.1: the list `x_1^{(n)} ≤ x_2^{(n)} ≤ ⋯` is increasing. -/
@[dlmf 24.12.E1]
theorem bernoulliRealZerosGE_sorted (n : ℕ) : (bernoulliRealZerosGE n).Pairwise (· ≤ ·) :=
  b24b_zerosGE_sorted _

/-- DLMF 24.12.1: the list consists exactly of the zeros of `Bₙ` in `[1/2, ∞)`. -/
@[dlmf 24.12.E1]
theorem mem_bernoulliRealZerosGE {n : ℕ} {x : ℝ} :
    x ∈ bernoulliRealZerosGE n ↔ 1 / 2 ≤ x ∧ bernoulliFun n x = 0 := by
  rw [bernoulliRealZerosGE, b24b_mem_zerosGE, bernoulliFun]
  exact (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr (b24b_bernoulli_ne_zero n)

/-- DLMF §24.12(i) (after 24.12.1): the zeros in `(-∞, 1/2]` are the `1 - x_j^{(n)}`. -/
@[dlmf 24.12.i]
theorem bernoulliFun_eq_zero_iff_of_le_half {n : ℕ} {x : ℝ} (hx : x ≤ 1 / 2) :
    bernoulliFun n x = 0 ↔ 1 - x ∈ bernoulliRealZerosGE n := by
  rw [mem_bernoulliRealZerosGE, bernoulliFun_eval_one_sub]
  constructor
  · intro h; exact ⟨by linarith, by rw [h, mul_zero]⟩
  · rintro ⟨-, h⟩
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (pow_ne_zero _ (by norm_num))
    · exact h

/-- DLMF 24.12.7: the list `y_1^{(n)} ≤ y_2^{(n)} ≤ ⋯` is increasing. -/
@[dlmf 24.12.E7]
theorem eulerRealZerosGE_sorted (n : ℕ) : (eulerRealZerosGE n).Pairwise (· ≤ ·) :=
  b24b_zerosGE_sorted _

/-- DLMF 24.12.7: the list consists exactly of the zeros of `Eₙ` in `[1/2, ∞)`. -/
@[dlmf 24.12.E7]
theorem mem_eulerRealZerosGE {n : ℕ} {x : ℝ} :
    x ∈ eulerRealZerosGE n ↔ 1 / 2 ≤ x ∧ eulerFun n x = 0 := by
  rw [eulerRealZerosGE, b24b_mem_zerosGE, eulerFun]
  exact (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr (b24b_euler_ne_zero n)

/-- DLMF §24.12(ii) (after 24.12.7): the zeros in `(-∞, 1/2]` are the `1 - y_j^{(n)}`. -/
@[dlmf 24.12.ii]
theorem eulerFun_eq_zero_iff_of_le_half {n : ℕ} {x : ℝ} (hx : x ≤ 1 / 2) :
    eulerFun n x = 0 ↔ 1 - x ∈ eulerRealZerosGE n := by
  rw [mem_eulerRealZerosGE, eulerFun_one_sub]
  constructor
  · intro h; exact ⟨by linarith, by rw [h, mul_zero]⟩
  · rintro ⟨-, h⟩
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (pow_ne_zero _ (by norm_num))
    · exact h

/-- The first entry of a sorted list of reals that are all `≥ a` and contain `a` is `a`. -/
lemma b24b_getD_zero_eq {l : List ℝ} {a : ℝ} (hs : l.Pairwise (· ≤ ·)) (ha : a ∈ l)
    (hge : ∀ y ∈ l, a ≤ y) : l.getD (1 - 1) 0 = a := by
  cases l with
  | nil => simp at ha
  | cons b t =>
    simp only [Nat.sub_self, List.getD_cons_zero]
    rcases List.mem_cons.mp ha with h | h
    · exact h.symm
    · exact le_antisymm ((List.pairwise_cons.mp hs).1 a h) (hge b List.mem_cons_self)

/-! ### Helper lemmas on zeros (Rolle, sign changes) -/

section ZeroHelpers

open Finset

/-- Rolle for `Bₖ₊₁`: two zeros give a zero of `Bₖ` between them. -/
lemma q24b_rolle_bernoulli {k : ℕ} {a b : ℝ} (hab : a < b) (ha : bernoulliFun (k + 1) a = 0)
    (hb : bernoulliFun (k + 1) b = 0) : ∃ c ∈ Set.Ioo a b, bernoulliFun k c = 0 := by
  obtain ⟨c, hc, h⟩ := exists_hasDerivAt_eq_zero hab
    (continuous_bernoulliFun (k + 1)).continuousOn (ha.trans hb.symm)
    (fun x _ => hasDerivAt_bernoulliFun (k + 1) x)
  refine ⟨c, hc, ?_⟩
  simp only [Nat.add_sub_cancel] at h
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (by positivity)
  · exact h

/-- Rolle for `Eₖ₊₁`. -/
lemma q24b_rolle_euler {k : ℕ} {a b : ℝ} (hab : a < b) (ha : eulerFun (k + 1) a = 0)
    (hb : eulerFun (k + 1) b = 0) : ∃ c ∈ Set.Ioo a b, eulerFun k c = 0 := by
  obtain ⟨c, hc, h⟩ := exists_hasDerivAt_eq_zero hab
    (continuous_eulerFun (k + 1)).continuousOn (ha.trans hb.symm)
    (fun x _ => hasDerivAt_eulerFun (k + 1) x)
  refine ⟨c, hc, ?_⟩
  simp only [Nat.add_sub_cancel] at h
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (by positivity)
  · exact h

/-- `B₂ₙ₊₁` has no zero in `(0, 1/2)`. -/
lemma q24b_bernoulli_odd_ne_zero (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    bernoulliFun (2 * n + 1) x ≠ 0 := by
  induction n generalizing x with
  | zero =>
    have : bernoulliFun 1 x = x - 1 / 2 := by
      simp [bernoulliFun, Polynomial.bernoulli_one]
    rw [show 2 * 0 + 1 = 1 by rfl, this]; linarith [hx.2]
  | succ n ih =>
    intro hc
    have h0 : bernoulliFun (2 * (n + 1) + 1) 0 = 0 := by
      rw [bernoulliFun_eval_zero, bernoulli_eq_zero_of_odd (odd_two_mul_add_one _) (by omega)]
      simp
    have hh : bernoulliFun (2 * (n + 1) + 1) (1 / 2) = 0 := by
      rw [one_div]; exact bernoulliFun_eval_half_eq_zero _
    rw [show 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 by ring] at h0 hh hc
    obtain ⟨a, ha, ha0⟩ := q24b_rolle_bernoulli hx.1 h0 hc
    obtain ⟨b, hb, hb0⟩ := q24b_rolle_bernoulli hx.2 hc hh
    obtain ⟨d, hd, hd0⟩ := q24b_rolle_bernoulli (ha.2.trans hb.1) ha0 hb0
    exact ih ⟨ha.1.trans hd.1, hd.2.trans hb.2⟩ hd0

/-- `Eₖ₊₁(1) = -Eₖ₊₁(0)`. -/
lemma q24b_eulerFun_one (k : ℕ) : eulerFun (k + 1) 1 = -eulerFun (k + 1) 0 := by
  have h := eulerFun_add_one_add (k + 1) 0
  rw [zero_add, zero_pow (Nat.succ_ne_zero k), mul_zero] at h
  linarith

/-- `E₂ₘ₊₂(0) = 0`. -/
lemma q24b_eulerFun_two_mul_add_two_zero (m : ℕ) : eulerFun (2 * m + 2) 0 = 0 := by
  have h1 := q24b_eulerFun_one (2 * m + 1)
  have h2 := eulerFun_one_sub (2 * m + 2) 0
  rw [sub_zero, show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul] at h2
  rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring] at h1
  rw [show 2 * m + 2 = 2 * (m + 1) by ring]
  norm_num at h2
  linarith

/-- `E₂ₘ₊₁(1/2) = 0`. -/
lemma q24b_eulerFun_odd_half (m : ℕ) : eulerFun (2 * m + 1) (1 / 2) = 0 := by
  have h := eulerNumber_eq_zero_of_odd (odd_two_mul_add_one m)
  rw [eulerNumber, mul_eq_zero] at h
  have h' : (euler (2 * m + 1)).eval (1 / 2 : ℚ) = 0 := h.resolve_left (pow_ne_zero _ two_ne_zero)
  have : (1 / 2 : ℝ) = algebraMap ℚ ℝ (1 / 2) := by simp
  rw [eulerFun, this, eval_map, eval₂_at_apply, h', map_zero]

/-- `E₂ₘ₊₁` has no zero in `(0, 1/2)` and `E₂ₘ₊₂` has no zero in `(0, 1)`. -/
lemma q24b_euler_ne_zero (m : ℕ) :
    (∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2), eulerFun (2 * m + 1) x ≠ 0) ∧
      ∀ x ∈ Set.Ioo (0 : ℝ) 1, eulerFun (2 * m + 2) x ≠ 0 := by
  have step : ∀ m : ℕ, (∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2), eulerFun (2 * m + 1) x ≠ 0) →
      ∀ x ∈ Set.Ioo (0 : ℝ) 1, eulerFun (2 * m + 2) x ≠ 0 := by
    intro m hQ x hx hc
    have hQ' : ∀ y ∈ Set.Ioo (0 : ℝ) 1, eulerFun (2 * m + 1) y = 0 → y = 1 / 2 := by
      intro y hy hy0
      rcases lt_trichotomy y (1 / 2) with h | h | h
      · exact absurd hy0 (hQ y ⟨hy.1, h⟩)
      · exact h
      · refine absurd ?_ (hQ (1 - y) ⟨by linarith [hy.2], by linarith⟩)
        rw [eulerFun_one_sub, hy0, mul_zero]
    have h0 := q24b_eulerFun_two_mul_add_two_zero m
    have h1 : eulerFun (2 * m + 2) 1 = 0 := by
      rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, q24b_eulerFun_one,
        show 2 * m + 1 + 1 = 2 * m + 2 by ring, h0, neg_zero]
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring] at h0 h1 hc
    obtain ⟨a, ha, ha0⟩ := q24b_rolle_euler hx.1 h0 hc
    obtain ⟨b, hb, hb0⟩ := q24b_rolle_euler hx.2 hc h1
    have := hQ' a ⟨ha.1, ha.2.trans hx.2⟩ ha0
    have := hQ' b ⟨hx.1.trans hb.1, hb.2⟩ hb0
    linarith [ha.2, hb.1]
  induction m with
  | zero =>
    have hQ : ∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2), eulerFun (2 * 0 + 1) x ≠ 0 := by
      intro x hx
      have : eulerFun 1 x = x - 1 / 2 := by simp [eulerFun, Polynomial.euler_one]
      rw [show 2 * 0 + 1 = 1 by rfl, this]; linarith [hx.2]
    exact ⟨hQ, step 0 hQ⟩
  | succ m ih =>
    have hQ : ∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2), eulerFun (2 * (m + 1) + 1) x ≠ 0 := by
      intro x hx hc
      have hh := q24b_eulerFun_odd_half (m + 1)
      rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by ring] at hh hc
      obtain ⟨c, hc', hc0⟩ := q24b_rolle_euler hx.2 hc hh
      exact ih.2 c ⟨hx.1.trans hc'.1, hc'.2.trans (by norm_num)⟩ hc0
    exact ⟨hQ, step (m + 1) hQ⟩

/-- The second entry of a sorted list whose least entry `a` is simple and whose next value is
`b`. -/
lemma q24b_getD_one_eq {l : List ℝ} {a b : ℝ} (hs : l.Pairwise (· ≤ ·)) (ha : a ∈ l)
    (hb : b ∈ l) (hab : a < b) (hc : l.count a ≤ 1) (hge : ∀ y ∈ l, a ≤ y)
    (hgeb : ∀ y ∈ l, y ≠ a → b ≤ y) : l.getD (2 - 1) 0 = b := by
  match l, hs, ha, hb, hc, hge, hgeb with
  | [], _, ha, _, _, _, _ => simp at ha
  | [c], _, ha, hb, _, _, _ =>
    simp only [List.mem_singleton] at ha hb; subst ha; subst hb; exact absurd hab (lt_irrefl _)
  | c :: d :: t, hs, ha, hb, hc, hge, hgeb =>
    simp only [show 2 - 1 = 1 from rfl, List.getD_cons_succ, List.getD_cons_zero]
    have hca : c = a := by
      rcases List.mem_cons.mp ha with h | h
      · exact h.symm
      · exact le_antisymm ((List.pairwise_cons.mp hs).1 a h) (hge c List.mem_cons_self)
    subst hca
    have hdc : d ≠ c := by
      intro hdc; subst hdc
      simp at hc
    have h1 : b ≤ d := hgeb d (by simp) hdc
    have hbt : b ∈ d :: t := by
      rcases List.mem_cons.mp hb with h | h
      · exact absurd h (ne_of_gt hab)
      · exact h
    have h2 : d ≤ b := by
      rcases List.mem_cons.mp hbt with h | h
      · exact h ▸ le_rfl
      · exact (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 b h
    exact le_antisymm h2 h1

/-- `B₂ₖ ≠ 0` for `k ≥ 1` (from `ζ(2k) > 0`). -/
lemma q24b_bernoulli_two_mul_ne_zero {k : ℕ} (hk : 1 ≤ k) : _root_.bernoulli (2 * k) ≠ 0 := by
  intro h0
  have h := hasSum_zeta_nat (k := k) (by omega)
  rw [h0] at h
  have := le_hasSum h 1 (fun j _ => by positivity)
  norm_num at this

/-- `B₂, …, B₅`. -/
lemma q24b_bernoulli_small :
    _root_.bernoulli 2 = 1 / 6 ∧ _root_.bernoulli 3 = 0 ∧ _root_.bernoulli 4 = -1 / 30 ∧
      _root_.bernoulli 5 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  · exact bernoulli'_two
  · exact bernoulli'_three
  · exact bernoulli'_four
  · exact bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

/-- `Bₙ(x) = ∑ₖ (n choose k) Bₖ x^{n-k}`. -/
lemma q24b_bernoulliFun_expand (n : ℕ) (x : ℝ) :
    bernoulliFun n x =
      ∑ k ∈ range (n + 1), ((n.choose k : ℝ) * _root_.bernoulli k) * x ^ (n - k) := by
  simp only [bernoulliFun, Polynomial.bernoulli, Polynomial.map_sum, eval_finsetSum,
    Polynomial.map_monomial, eval_monomial]
  refine sum_congr rfl fun k _ => ?_
  simp only [map_mul, map_natCast, eq_ratCast]; ring

/-- Explicit `B₄(x)`. -/
lemma q24b_B4 (x : ℝ) : bernoulliFun 4 x = x ^ 4 - 2 * x ^ 3 + x ^ 2 - 1 / 30 := by
  obtain ⟨b2, b3, b4, -⟩ := q24b_bernoulli_small
  rw [q24b_bernoulliFun_expand]
  simp [sum_range_succ, b2, b3, b4, Nat.choose]
  norm_num; ring

/-- Explicit `B₅(x)`. -/
lemma q24b_B5 (x : ℝ) :
    bernoulliFun 5 x = x ^ 5 - 5 / 2 * x ^ 4 + 5 / 3 * x ^ 3 - 1 / 6 * x := by
  obtain ⟨b2, b3, b4, b5⟩ := q24b_bernoulli_small
  rw [q24b_bernoulliFun_expand]
  simp [sum_range_succ, b2, b3, b4, b5, Nat.choose]
  norm_num; ring

/-- Explicit `B₂(x)`. -/
lemma q24b_B2 (x : ℝ) : bernoulliFun 2 x = x ^ 2 - x + 1 / 6 := by
  obtain ⟨b2, -⟩ := q24b_bernoulli_small
  rw [q24b_bernoulliFun_expand]
  simp [sum_range_succ, b2, Nat.choose]
  norm_num; ring

/-- Explicit `B₃(x)`. -/
lemma q24b_B3 (x : ℝ) : bernoulliFun 3 x = x ^ 3 - 3 / 2 * x ^ 2 + 1 / 2 * x := by
  obtain ⟨b2, b3, -⟩ := q24b_bernoulli_small
  rw [q24b_bernoulliFun_expand]
  simp [sum_range_succ, b2, b3, Nat.choose]
  norm_num; ring

/-- Intermediate value theorem for a sign change. -/
lemma q24b_exists_root {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (h : f a * f b < 0) : ∃ c ∈ Set.Ioo a b, f c = 0 := by
  rcases lt_or_gt_of_ne (show f a ≠ 0 by intro h0; rw [h0, zero_mul] at h; exact lt_irrefl _ h)
    with ha | ha
  · have hb : 0 < f b := by nlinarith
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioo hab.le hf.continuousOn ⟨ha, hb⟩
    exact ⟨c, hc, hfc⟩
  · have hb : f b < 0 := by nlinarith
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioo' hab.le hf.continuousOn ⟨hb, ha⟩
    exact ⟨c, hc, hfc⟩

/-- A real polynomial of degree `≤ n` with `n` distinct real zeros has exactly `n` roots. -/
lemma q24b_roots_card_eq {p : ℝ[X]} {n : ℕ} (hdeg : p.natDegree ≤ n) (l : List ℝ)
    (hl : l.Pairwise (· < ·)) (hlen : l.length = n) (hr : ∀ x ∈ l, p.eval x = 0)
    (hp : p ≠ 0) : p.roots.card = n := by
  refine le_antisymm ((card_roots' p).trans hdeg) ?_
  rw [← hlen, ← List.toFinset_card_of_nodup (hl.imp ne_of_lt).nodup]
  refine (Finset.card_le_card fun x hx => ?_).trans (Multiset.toFinset_card_le _)
  rw [Multiset.mem_toFinset, mem_roots hp]
  exact hr x (List.mem_toFinset.mp hx)

end ZeroHelpers

/-! ### §24.12(i) Bernoulli polynomials: real zeros -/

/-- DLMF §24.12(i): for `n ≥ 1` the only zeros of `B₂ₙ₊₁(x)` in `[0, 1]` are `0, 1/2, 1`. -/
@[dlmf 24.12.i]
theorem bernoulliFun_odd_zeros_Icc {n : ℕ} (hn : 1 ≤ n) :
    {x : ℝ | x ∈ Set.Icc 0 1 ∧ bernoulliFun (2 * n + 1) x = 0} = {0, 1 / 2, 1} := by
  have h0 : bernoulliFun (2 * n + 1) 0 = 0 := by
    rw [bernoulliFun_eval_zero, bernoulli_eq_zero_of_odd (odd_two_mul_add_one _) (by omega)]
    simp
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hx0, hx1⟩, hx⟩
    by_contra hne
    push Not at hne
    rcases lt_or_gt_of_ne hne.2.1 with hlt | hgt
    · exact q24b_bernoulli_odd_ne_zero n ⟨lt_of_le_of_ne hx0 (Ne.symm hne.1), hlt⟩ hx
    · have h1 : (1 - x) ∈ Set.Ioo (0 : ℝ) (1 / 2) :=
        ⟨by linarith [lt_of_le_of_ne hx1 hne.2.2], by linarith⟩
      apply q24b_bernoulli_odd_ne_zero n h1
      rw [bernoulliFun_eval_one_sub, hx, mul_zero]
  · rintro (rfl | rfl | rfl)
    · exact ⟨⟨le_rfl, zero_le_one⟩, h0⟩
    · refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
      rw [one_div]; exact bernoulliFun_eval_half_eq_zero _
    · refine ⟨⟨zero_le_one, le_rfl⟩, ?_⟩
      rw [bernoulliFun_endpoints_eq_of_ne_one (by omega), h0]

/-- DLMF §24.12(i): for `n ≥ 1` the only zeros of `B₂ₙ(x) - B₂ₙ` in `[0, 1]` are `0, 1`. -/
@[dlmf 24.12.i]
theorem bernoulliFun_even_sub_zeros_Icc {n : ℕ} (hn : 1 ≤ n) :
    {x : ℝ | x ∈ Set.Icc 0 1 ∧ bernoulliFun (2 * n) x - _root_.bernoulli (2 * n) = 0} = {0, 1} := by
  have hn0 : n ≠ 0 := by omega
  have hB : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasSum (fun m : ℕ => 1 / (m : ℝ) ^ (2 * n) *
      (Real.cos (2 * π * m * x) - 1))
      ((-1 : ℝ) ^ (n + 1) * (2 * π) ^ (2 * n) / 2 / (2 * n)! *
        (bernoulliFun (2 * n) x - _root_.bernoulli (2 * n))) := by
    intro x hx
    have h1 := hasSum_one_div_nat_pow_mul_cos hn0 hx
    have h2 := hasSum_one_div_nat_pow_mul_cos hn0 (x := 0) ⟨le_rfl, zero_le_one⟩
    convert h1.sub h2 using 1
    · funext m; simp; ring
    · rw [← bernoulliFun_eval_zero]; simp only [bernoulliFun]; ring
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx01, hx⟩
    have hs := hB x hx01
    rw [hx, mul_zero] at hs
    have hnonneg : ∀ m : ℕ, 0 ≤ -(1 / (m : ℝ) ^ (2 * n) * (Real.cos (2 * π * m * x) - 1)) := by
      intro m
      have : Real.cos (2 * π * m * x) - 1 ≤ 0 := by linarith [Real.cos_le_one (2 * π * m * x)]
      have : 0 ≤ 1 / (m : ℝ) ^ (2 * n) := by positivity
      nlinarith
    have hz := (hasSum_zero_iff_of_nonneg hnonneg).mp (by simpa using hs.neg)
    have h1 := congrFun hz 1
    simp only [Nat.cast_one, one_pow, div_one, one_mul, mul_one, Pi.zero_apply, neg_eq_zero,
      sub_eq_zero] at h1
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp h1
    have hx' : x = k := by
      have := Real.pi_pos
      field_simp at hk; linarith
    have hk0 : (0 : ℝ) ≤ k := hx' ▸ hx01.1
    have hk1 : (k : ℝ) ≤ 1 := hx' ▸ hx01.2
    have : k = 0 ∨ k = 1 := by
      have : (0 : ℤ) ≤ k := by exact_mod_cast hk0
      have : k ≤ (1 : ℤ) := by exact_mod_cast hk1
      omega
    rcases this with rfl | rfl
    · left; simpa using hx'
    · right; simpa using hx'
  · rintro (rfl | rfl)
    · exact ⟨⟨le_rfl, zero_le_one⟩, by rw [bernoulliFun_eval_zero]; ring⟩
    · exact ⟨⟨zero_le_one, le_rfl⟩, by
        rw [bernoulliFun_endpoints_eq_of_ne_one (by omega), bernoulliFun_eval_zero]; ring⟩

/-! ### Helpers for 24.12.2 and 24.12.3: the first zero of `B₂ₖ`

By the Fourier series of `B₂ₖ` (Mathlib), `g(θ) = (-1)^{k+1} (2π)^{2k}/(2 (2k)!) B₂ₖ(3/4 + θ/(2π))`
is `sin θ - A cos 2θ - B sin 3θ + A² cos 4θ` up to `0.6 A²`, where `A = 2^{-2k}`, `B = 3^{-2k}`,
the tail being bounded by `ζ(4)`. For `k ≥ 3` this gives `g < 0` on `[-π/2, cA]` (`c + 2A ≤ 1`)
and `g(A) > 0`; `k = 1, 2` follow from the explicit polynomials. -/

/-- If `Bₙ ≠ 0` on `[1/2, lo]` and `Bₙ` changes sign on `[lo, hi]`, then `lo < x₁ < hi`. -/
lemma s24b_first_zero_bracket {n : ℕ} {lo hi : ℝ} (hlh : lo < hi)
    (hne : ∀ x ∈ Set.Icc (1 / 2 : ℝ) lo, bernoulliFun n x ≠ 0)
    (hlo : 1 / 2 ≤ lo) (hsign : bernoulliFun n lo * bernoulliFun n hi < 0) :
    lo < bernoulliRealZero n 1 ∧ bernoulliRealZero n 1 < hi := by
  obtain ⟨z, hz, hz0⟩ := q24b_exists_root (continuous_bernoulliFun n) hlh hsign
  have hzl : z ∈ bernoulliRealZerosGE n :=
    mem_bernoulliRealZerosGE.mpr ⟨hlo.trans hz.1.le, hz0⟩
  have hs := bernoulliRealZerosGE_sorted n
  have hmem : (bernoulliRealZerosGE n).getD (1 - 1) 0 ∈ bernoulliRealZerosGE n ∧
      (bernoulliRealZerosGE n).getD (1 - 1) 0 ≤ z := by
    cases h : bernoulliRealZerosGE n with
    | nil => rw [h] at hzl; simp at hzl
    | cons a t =>
      rw [h] at hzl hs
      simp only [Nat.sub_self, List.getD_cons_zero]
      refine ⟨List.mem_cons_self, ?_⟩
      rcases List.mem_cons.mp hzl with e | e
      · rw [e]
      · exact (List.pairwise_cons.mp hs).1 z e
  obtain ⟨h1, h2⟩ := mem_bernoulliRealZerosGE.mp hmem.1
  refine ⟨?_, hmem.2.trans_lt hz.2⟩
  by_contra hle
  push Not at hle
  exact hne _ ⟨h1, hle⟩ h2

/-- Tail bound for the Fourier series of `B₂ₖ`, `k ≥ 2`, after the first five terms. -/
lemma s24b_fourier_tail {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |(-1 : ℝ) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)! * bernoulliFun (2 * k) x -
      ∑ m ∈ Finset.range 5, 1 / (m : ℝ) ^ (2 * k) * Real.cos (2 * π * m * x)| ≤
      625 * (π ^ 4 / 90 - (1 + 1 / 16 + 1 / 81 + 1 / 256)) * (1 / 5) ^ (2 * k) := by
  have h := hasSum_one_div_nat_pow_mul_cos (by omega : k ≠ 0) hx
  have h5 := (hasSum_nat_add_iff' 5).mpr h
  have hz := (hasSum_nat_add_iff' 5).mpr hasSum_zeta_four
  have hz' : ∑ i ∈ Finset.range 5, (1 : ℝ) / (i : ℝ) ^ 4 = 1 + 1 / 16 + 1 / 81 + 1 / 256 := by
    simp [Finset.sum_range_succ]; norm_num
  rw [hz'] at hz
  have hg := hz.mul_left (625 * (1 / 5 : ℝ) ^ (2 * k))
  have hb := h5.norm_le_of_bounded hg fun m => by
    rw [Real.norm_eq_abs, abs_mul]
    have hy : (5 : ℝ) ≤ ((m + 5 : ℕ) : ℝ) := by push_cast; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
    set y : ℝ := ((m + 5 : ℕ) : ℝ)
    have hy0 : 0 < y := by linarith
    have hc := Real.abs_cos_le_one (2 * π * y * x)
    obtain ⟨j, hj⟩ : ∃ j, 2 * k = j + 4 := ⟨2 * k - 4, by omega⟩
    rw [hj, abs_of_pos (by positivity : (0 : ℝ) < 1 / y ^ (j + 4))]
    have hp : (5 : ℝ) ^ j ≤ y ^ j := pow_le_pow_left₀ (by norm_num) hy _
    calc 1 / y ^ (j + 4) * |Real.cos (2 * π * y * x)| ≤ 1 / y ^ (j + 4) :=
          mul_le_of_le_one_right (by positivity) hc
      _ = 1 / (y ^ 4 * y ^ j) := by rw [pow_add, mul_comm]
      _ ≤ 1 / (y ^ 4 * 5 ^ j) :=
          one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hp (by positivity))
      _ = 625 * (1 / 5) ^ (j + 4) * (1 / y ^ 4) := by
          rw [one_div_pow, pow_add]; field_simp; norm_num
  rw [Real.norm_eq_abs] at hb
  calc _ ≤ 625 * (1 / 5) ^ (2 * k) * (π ^ 4 / 90 - (1 + 1 / 16 + 1 / 81 + 1 / 256)) := hb
    _ = _ := by ring

/-- The first five Fourier terms of `B_N` at `x = 3/4 + θ/(2π)`. -/
lemma s24b_main_terms {N : ℕ} (hN : N ≠ 0) (θ : ℝ) :
    ∑ m ∈ Finset.range 5, 1 / (m : ℝ) ^ N * Real.cos (2 * π * m * (3 / 4 + θ / (2 * π))) =
      Real.sin θ - (1 / 2) ^ N * Real.cos (2 * θ) - (1 / 3) ^ N * Real.sin (3 * θ) +
        (1 / 4) ^ N * Real.cos (4 * θ) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have c1 : Real.cos (2 * π * ((1 : ℕ) : ℝ) * (3 / 4 + θ / (2 * π))) = Real.sin θ := by
    rw [show 2 * π * ((1 : ℕ) : ℝ) * (3 / 4 + θ / (2 * π)) = θ + π / 2 + π by
      push_cast; field_simp; ring, Real.cos_add_pi, Real.cos_add_pi_div_two, neg_neg]
  have c2 : Real.cos (2 * π * ((2 : ℕ) : ℝ) * (3 / 4 + θ / (2 * π))) = -Real.cos (2 * θ) := by
    rw [show 2 * π * ((2 : ℕ) : ℝ) * (3 / 4 + θ / (2 * π)) = 2 * θ + π + 2 * π by
      push_cast; field_simp; ring, Real.cos_add_two_pi, Real.cos_add_pi]
  have c3 : Real.cos (2 * π * ((3 : ℕ) : ℝ) * (3 / 4 + θ / (2 * π))) = -Real.sin (3 * θ) := by
    rw [show 2 * π * ((3 : ℕ) : ℝ) * (3 / 4 + θ / (2 * π)) = 3 * θ + π / 2 + 2 * π + 2 * π by
      push_cast; field_simp; ring, Real.cos_add_two_pi, Real.cos_add_two_pi,
      Real.cos_add_pi_div_two]
  have c4 : Real.cos (2 * π * ((4 : ℕ) : ℝ) * (3 / 4 + θ / (2 * π))) = Real.cos (4 * θ) := by
    rw [show 2 * π * ((4 : ℕ) : ℝ) * (3 / 4 + θ / (2 * π)) = 4 * θ + 2 * π + 2 * π + 2 * π by
      push_cast; field_simp; ring, Real.cos_add_two_pi, Real.cos_add_two_pi, Real.cos_add_two_pi]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  rw [c1, c2, c3, c4]
  simp only [Nat.cast_zero, zero_pow hN, div_zero, zero_mul, zero_add, Nat.cast_one, one_pow,
    div_one, one_mul, one_div_pow]
  push_cast
  ring

/-- The normalized `B₂ₖ` at `x = 3/4 + θ/(2π)`: `g(θ) = (-1)^{k+1} (2π)^{2k}/(2 (2k)!) B₂ₖ(x)`. -/
noncomputable def s24b_g (k : ℕ) (θ : ℝ) : ℝ :=
  (-1 : ℝ) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)! * bernoulliFun (2 * k) (3 / 4 + θ / (2 * π))

/-- Numerical constants for `k ≥ 3`. -/
lemma s24b_consts {k : ℕ} (hk : 3 ≤ k) :
    0 < (1 / 2 : ℝ) ^ (2 * k) ∧ (1 / 2 : ℝ) ^ (2 * k) ≤ 1 / 64 ∧
      (1 / 3 : ℝ) ^ (2 * k) ≤ 9 / 100 * (1 / 2) ^ (2 * k) ∧
      625 * (π ^ 4 / 90 - (1 + 1 / 16 + 1 / 81 + 1 / 256)) * (1 / 5 : ℝ) ^ (2 * k) ≤
        6 / 10 * ((1 / 2) ^ (2 * k)) ^ 2 := by
  have h6 : 6 ≤ 2 * k := by omega
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · calc (1 / 2 : ℝ) ^ (2 * k) ≤ (1 / 2) ^ 6 := pow_le_pow_of_le_one (by norm_num) (by norm_num) h6
      _ = 1 / 64 := by norm_num
  · have e : (1 / 3 : ℝ) ^ (2 * k) = (2 / 3) ^ (2 * k) * (1 / 2) ^ (2 * k) := by
      rw [← mul_pow]; norm_num
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc (2 / 3 : ℝ) ^ (2 * k) ≤ (2 / 3) ^ 6 := pow_le_pow_of_le_one (by norm_num) (by norm_num) h6
      _ ≤ 9 / 100 := by norm_num
  · have e : (1 / 5 : ℝ) ^ (2 * k) = (4 / 5) ^ (2 * k) * ((1 / 2) ^ (2 * k)) ^ 2 := by
      rw [show ((1 / 2 : ℝ) ^ (2 * k)) ^ 2 = ((1 / 2) ^ 2) ^ (2 * k) by
        rw [← pow_mul, ← pow_mul, mul_comm], ← mul_pow]
      norm_num
    rw [e, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hp := Real.pi_lt_d4
    have hp0 := Real.pi_pos
    have hS : π ^ 4 / 90 - (1 + 1 / 16 + 1 / 81 + 1 / 256) ≤ 36 / 10000 := by
      have : π ^ 4 < 3.1416 ^ 4 := by gcongr
      norm_num at this ⊢; linarith
    have hS0 : 0 ≤ π ^ 4 / 90 - (1 + 1 / 16 + 1 / 81 + 1 / 256) := by
      have : (3.1415 : ℝ) ^ 4 < π ^ 4 := by gcongr; exact Real.pi_gt_d4
      norm_num at this ⊢; linarith
    have h45 : (4 / 5 : ℝ) ^ (2 * k) ≤ (4 / 5) ^ 6 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h6
    calc 625 * (π ^ 4 / 90 - (1 + 1 / 16 + 1 / 81 + 1 / 256)) * (4 / 5 : ℝ) ^ (2 * k)
        ≤ 625 * (36 / 10000) * (4 / 5) ^ 6 := by gcongr
      _ ≤ 6 / 10 := by norm_num

/-- `|g(θ) - main(θ)| ≤ 0.6 A²` on `[-3π/2, π/2]`, `A = 2^{-2k}`, `k ≥ 3`. -/
lemma s24b_g_approx {k : ℕ} (hk : 3 ≤ k) {θ : ℝ} (h1 : -(3 * π / 2) ≤ θ) (h2 : θ ≤ π / 2) :
    |s24b_g k θ - (Real.sin θ - (1 / 2) ^ (2 * k) * Real.cos (2 * θ) -
      (1 / 3) ^ (2 * k) * Real.sin (3 * θ) + (1 / 4) ^ (2 * k) * Real.cos (4 * θ))| ≤
      6 / 10 * ((1 / 2) ^ (2 * k)) ^ 2 := by
  have hx : 3 / 4 + θ / (2 * π) ∈ Set.Icc (0 : ℝ) 1 := by
    have := Real.pi_pos
    constructor
    · have : -(3 / 4) ≤ θ / (2 * π) := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    · have : θ / (2 * π) ≤ 1 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
      linarith
  have ht := s24b_fourier_tail (by omega : 2 ≤ k) hx
  rw [s24b_main_terms (by omega : 2 * k ≠ 0)] at ht
  exact ht.trans (s24b_consts hk).2.2.2

/-- `g(A) > 0` for `A = 2^{-2k}`, `k ≥ 3`. -/
lemma s24b_g_pos {k : ℕ} (hk : 3 ≤ k) : 0 < s24b_g k ((1 / 2) ^ (2 * k)) := by
  obtain ⟨hA0, hA1, hB, -⟩ := s24b_consts hk
  set A : ℝ := (1 / 2) ^ (2 * k) with hAd
  set B : ℝ := (1 / 3) ^ (2 * k) with hBd
  have hB0 : 0 ≤ B := by positivity
  have hQ : (1 / 4 : ℝ) ^ (2 * k) = A ^ 2 := by
    rw [show (A : ℝ) ^ 2 = ((1 / 2) ^ 2) ^ (2 * k) by rw [← pow_mul, ← pow_mul, mul_comm]]
    norm_num
  have hπ := Real.pi_gt_three
  have hap := s24b_g_approx hk (θ := A) (by linarith) (by linarith)
  rw [hQ, ← hAd, ← hBd] at hap
  have h1 := Real.sin_ge_sub_cube hA0.le
  have h2 := Real.cos_le_one (2 * A)
  have h3 : B * Real.sin (3 * A) ≤ B * (3 * A) :=
    mul_le_mul_of_nonneg_left (Real.sin_le (by positivity)) hB0
  have h4 : A ^ 2 * (1 - (4 * A) ^ 2 / 2) ≤ A ^ 2 * Real.cos (4 * A) :=
    mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos) (by positivity)
  have h5 : A * Real.cos (2 * A) ≤ A := by nlinarith
  rw [abs_le] at hap
  have hA2 : 0 < A ^ 2 := by positivity
  have f1 : A * B ≤ 9 / 100 * A ^ 2 := by nlinarith
  have f2 : A ^ 3 ≤ A ^ 2 / 64 := by nlinarith
  have f3 : A ^ 4 ≤ A ^ 2 / 4096 := by nlinarith
  nlinarith [hap.1]

/-- `g(θ) < 0` for `-π/2 ≤ θ ≤ cA` when `0 ≤ c` and `c + 2A ≤ 1`, `A = 2^{-2k}`, `k ≥ 3`. -/
lemma s24b_g_neg {k : ℕ} (hk : 3 ≤ k) {c θ : ℝ} (hc0 : 0 ≤ c)
    (hc : c + 2 * (1 / 2) ^ (2 * k) ≤ 1) (h1 : -(π / 2) ≤ θ)
    (h2 : θ ≤ c * (1 / 2) ^ (2 * k)) : s24b_g k θ < 0 := by
  obtain ⟨hA0, hA1, hB, -⟩ := s24b_consts hk
  set A : ℝ := (1 / 2) ^ (2 * k) with hAd
  set B : ℝ := (1 / 3) ^ (2 * k) with hBd
  have hB0 : 0 ≤ B := by positivity
  have hQ : (1 / 4 : ℝ) ^ (2 * k) = A ^ 2 := by
    rw [show (A : ℝ) ^ 2 = ((1 / 2) ^ 2) ^ (2 * k) by rw [← pow_mul, ← pow_mul, mul_comm]]
    norm_num
  have hπ := Real.pi_gt_three
  have hc1 : c ≤ 1 := by linarith
  have hθ2 : θ ≤ π / 2 := by nlinarith
  have hap := s24b_g_approx hk (θ := θ) (by linarith) hθ2
  rw [hQ, ← hAd, ← hBd, abs_le] at hap
  have h4 : A ^ 2 * Real.cos (4 * θ) ≤ A ^ 2 :=
    mul_le_of_le_one_right (by positivity) (Real.cos_le_one _)
  rcases le_total θ 0 with hθ | hθ
  · set s := Real.sin θ
    have hs0 : s ≤ 0 := Real.sin_nonpos_of_nonpos_of_neg_pi_le hθ (by linarith)
    have hs1 : -1 ≤ s := Real.neg_one_le_sin θ
    have hc2 : Real.cos (2 * θ) = 1 - 2 * s ^ 2 := by
      rw [Real.cos_two_mul, Real.cos_sq']; ring
    have hs3 : Real.sin (3 * θ) = 3 * s - 4 * s ^ 3 := Real.sin_three_mul θ
    rw [hc2, hs3] at hap
    have e1 : B * s ^ 3 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hB0 (by nlinarith [sq_nonneg s])
    have e2 : A * (s ^ 2 + s) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA0.le (by nlinarith)
    have e3 : s * (1 - 2 * A - 3 * B) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hs0 (by nlinarith)
    nlinarith
  · have hs : Real.sin θ ≤ c * A := (Real.sin_le hθ).trans h2
    have hc2 : 1 - (2 * θ) ^ 2 / 2 ≤ Real.cos (2 * θ) := Real.one_sub_sq_div_two_le_cos
    have hs3 : 0 ≤ Real.sin (3 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by nlinarith)
    have hθA : θ ≤ A := h2.trans (by nlinarith)
    have e1 : A * (1 - (2 * θ) ^ 2 / 2) ≤ A * Real.cos (2 * θ) :=
      mul_le_mul_of_nonneg_left hc2 hA0.le
    have e2 : 0 ≤ B * Real.sin (3 * θ) := mul_nonneg hB0 hs3
    have e3 : θ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hθ hθA 2
    nlinarith [mul_le_mul_of_nonneg_left e3 hA0.le]

/-- For `k ≥ 3`, `0 ≤ c < 1` and `c + 2A ≤ 1` (`A = 2^{-2k}`):
`3/4 + cA/(2π) < x_1^{(2k)} < 3/4 + A/(2π)`. -/
lemma s24b_bracket {k : ℕ} (hk : 3 ≤ k) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hc : c + 2 * (1 / 2) ^ (2 * k) ≤ 1) :
    3 / 4 + c * (1 / 2) ^ (2 * k) / (2 * π) < bernoulliRealZero (2 * k) 1 ∧
      bernoulliRealZero (2 * k) 1 < 3 / 4 + (1 / 2) ^ (2 * k) / (2 * π) := by
  obtain ⟨hA0, hA1, -, -⟩ := s24b_consts hk
  set A : ℝ := (1 / 2) ^ (2 * k) with hAd
  have hπ := Real.pi_pos
  have h2π : 0 < 2 * π := by positivity
  set K : ℝ := (-1 : ℝ) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)!
  have hK : K ≠ 0 := by
    have : (2 * k)! ≠ 0 := Nat.factorial_ne_zero _
    simp only [K]; positivity
  have hg : ∀ θ, s24b_g k θ = K * bernoulliFun (2 * k) (3 / 4 + θ / (2 * π)) := fun _ => rfl
  have hx : ∀ x : ℝ, 3 / 4 + 2 * π * (x - 3 / 4) / (2 * π) = x := by
    intro x; field_simp; ring
  refine s24b_first_zero_bracket ?_ (fun x hx' => ?_) ?_ ?_
  · have : c * A < A := by nlinarith
    linarith [div_lt_div_of_pos_right this h2π]
  · intro h0
    have hθ1 : -(π / 2) ≤ 2 * π * (x - 3 / 4) := by nlinarith [hx'.1]
    have hθ2 : 2 * π * (x - 3 / 4) ≤ c * A := by
      have := hx'.2
      have : x - 3 / 4 ≤ c * A / (2 * π) := by linarith
      rwa [le_div_iff₀ h2π, mul_comm] at this
    have hneg := s24b_g_neg hk hc0 hc hθ1 hθ2
    rw [hg, hx, h0, mul_zero] at hneg
    exact lt_irrefl _ hneg
  · have : 0 ≤ c * A / (2 * π) := by positivity
    linarith
  · have h1 := s24b_g_neg hk hc0 hc (θ := c * A) (by nlinarith) le_rfl
    have h2 := s24b_g_pos hk
    rw [hg] at h1 h2
    rw [← hAd] at h2
    have hKK : 0 < K * K := mul_self_pos.mpr hK
    have : K * bernoulliFun (2 * k) (3 / 4 + c * A / (2 * π)) *
        (K * bernoulliFun (2 * k) (3 / 4 + A / (2 * π))) < 0 := mul_neg_of_neg_of_pos h1 h2
    have e : K * bernoulliFun (2 * k) (3 / 4 + c * A / (2 * π)) *
        (K * bernoulliFun (2 * k) (3 / 4 + A / (2 * π))) = (K * K) *
        (bernoulliFun (2 * k) (3 / 4 + c * A / (2 * π)) *
          bernoulliFun (2 * k) (3 / 4 + A / (2 * π))) := by ring
    rw [e] at this
    by_contra hge
    push Not at hge
    exact absurd this (not_lt.mpr (mul_nonneg hKK.le hge))

/-- Estimate under the stated parameter and domain assumptions: `3 / 4 + 1 / (2 ^ (2 + 2) * π) <
bernoulliRealZero 2 1 ∧ bernoulliRealZero 2 1 < 3 / 4 + 1 / (2 ^ (2 + 1) * π)`. -/
lemma s24b_bounds_two :
    3 / 4 + 1 / (2 ^ (2 + 2) * π) < bernoulliRealZero 2 1 ∧
      bernoulliRealZero 2 1 < 3 / 4 + 1 / (2 ^ (2 + 1) * π) := by
  have hπ1 := Real.pi_gt_three
  have hπ2 := Real.pi_lt_d2
  set u := 1 / π with hu
  have hu1 : u < 1 / 3 := by rw [hu]; exact one_div_lt_one_div_of_lt (by norm_num) hπ1
  have hu2 : 1 / 3.15 < u := by rw [hu]; exact one_div_lt_one_div_of_lt Real.pi_pos hπ2
  have e1 : 1 / (2 ^ (2 + 2) * π) = u / 16 := by rw [hu]; field_simp; norm_num
  have e2 : 1 / (2 ^ (2 + 1) * π) = u / 8 := by rw [hu]; field_simp; norm_num
  rw [e1, e2]
  have hu0 : 0 < u := by linarith [show (0 : ℝ) < 1 / 3.15 by norm_num]
  refine s24b_first_zero_bracket (by linarith) (fun x hx => ?_) (by linarith) ?_
  · rw [q24b_B2]
    have h1 := hx.1; have h2 := hx.2
    nlinarith
  · rw [q24b_B2, q24b_B2]
    norm_num at hu2
    refine mul_neg_of_neg_of_pos (by nlinarith) (by nlinarith)

/-- Estimate under the stated parameter and domain assumptions: `3 / 4 + 1 / (2 ^ (4 + 2) * π) <
bernoulliRealZero 4 1 ∧ bernoulliRealZero 4 1 < 3 / 4 + 1 / (2 ^ (4 + 1) * π)`. -/
lemma s24b_bounds_four :
    3 / 4 + 1 / (2 ^ (4 + 2) * π) < bernoulliRealZero 4 1 ∧
      bernoulliRealZero 4 1 < 3 / 4 + 1 / (2 ^ (4 + 1) * π) := by
  have hπ1 := Real.pi_gt_d2
  have hπ2 := Real.pi_lt_d2
  set u := 1 / π with hu
  have hu1 : u < 1 / 3.14 := by rw [hu]; exact one_div_lt_one_div_of_lt (by norm_num) hπ1
  have hu2 : 1 / 3.15 < u := by rw [hu]; exact one_div_lt_one_div_of_lt Real.pi_pos hπ2
  norm_num at hu1 hu2
  have e1 : 1 / (2 ^ (4 + 2) * π) = u / 64 := by rw [hu]; field_simp; norm_num
  have e2 : 1 / (2 ^ (4 + 1) * π) = u / 32 := by rw [hu]; field_simp; norm_num
  rw [e1, e2]
  have hB4 : ∀ x, bernoulliFun 4 x = (x * (1 - x)) ^ 2 - 1 / 30 := by
    intro x; rw [q24b_B4]; ring
  refine s24b_first_zero_bracket (by linarith) (fun x hx => ?_) (by linarith) ?_
  · rw [hB4]
    have h1 := hx.1; have h2 := hx.2
    have hw : 0.184975 ≤ x * (1 - x) := by nlinarith
    nlinarith
  · rw [hB4, hB4]
    have hl1 : 3 / 4 + u / 64 ≤ 0.755 := by linarith
    have hl2 : 0.245 ≤ 3 / 4 + u / 64 := by linarith
    have hh1 : 0.7599 ≤ 3 / 4 + u / 32 := by linarith
    have hh2 : 3 / 4 + u / 32 ≤ 1 := by linarith
    have hw1 : 0.184975 ≤ (3 / 4 + u / 64) * (1 - (3 / 4 + u / 64)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hl1) (sub_nonneg.mpr hl2)]
    have hw2 : (3 / 4 + u / 32) * (1 - (3 / 4 + u / 32)) ≤ 0.182452 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hh1) (sub_nonneg.mpr hh2)]
    have hw3 : 0 ≤ (3 / 4 + u / 32) * (1 - (3 / 4 + u / 32)) := by
      apply mul_nonneg <;> linarith
    refine mul_neg_of_pos_of_neg (by nlinarith) (by nlinarith)

/-- DLMF 24.12.2: for even `n ≥ 2`,
`3/4 + 1/(2^{n+2} π) < x_1^{(n)} < 3/4 + 1/(2^{n+1} π)`. -/
@[dlmf 24.12.E2]
theorem bernoulliRealZero_one_bounds {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    3 / 4 + 1 / (2 ^ (n + 2) * π) < bernoulliRealZero n 1 ∧
      bernoulliRealZero n 1 < 3 / 4 + 1 / (2 ^ (n + 1) * π) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by obtain ⟨j, hj⟩ := he; omega⟩
  rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | hk
  · exact s24b_bounds_two
  · exact s24b_bounds_four
  have h := s24b_bracket hk (c := 1 / 2) (by norm_num) (by norm_num)
    (by linarith [(s24b_consts hk).2.1])
  have hπ := Real.pi_pos
  have e1 : 1 / 2 * (1 / 2 : ℝ) ^ (2 * k) / (2 * π) = 1 / (2 ^ (2 * k + 2) * π) := by
    rw [one_div_pow, pow_add]; field_simp
  have e2 : (1 / 2 : ℝ) ^ (2 * k) / (2 * π) = 1 / (2 ^ (2 * k + 1) * π) := by
    rw [one_div_pow, pow_add]; field_simp
  rw [e1, e2] at h
  exact h

/-- DLMF 24.12.3: `x_1^{(n)} - 3/4 ∼ 1/(2^{n+1} π)` as `n → ∞` through even values. -/
@[dlmf 24.12.E3]
theorem bernoulliRealZero_one_sub_isEquivalent :
    (fun k : ℕ => bernoulliRealZero (2 * k) 1 - 3 / 4) ~[atTop]
      fun k => 1 / (2 ^ (2 * k + 1) * π) := by
  have hπ := Real.pi_pos
  have hv : ∀ k : ℕ, 1 / (2 ^ (2 * k + 1) * π) = (1 / 2 : ℝ) ^ (2 * k) / (2 * π) := by
    intro k; rw [one_div_pow, pow_add]; field_simp
  have hv0 : ∀ k : ℕ, 0 < 1 / (2 ^ (2 * k + 1) * π) := fun k => by positivity
  have hA : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ (2 * k)) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)
    refine this.congr fun k => ?_
    rw [pow_mul]; norm_num
  refine isEquivalent_of_tendsto_one (tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩)
  · set c := max a 0
    have hc0 : 0 ≤ c := le_max_right _ _
    have hc1 : c < 1 := max_lt ha (by norm_num)
    have hev := hA.eventually (gt_mem_nhds (show (0 : ℝ) < (1 - c) / 2 by linarith))
    filter_upwards [hev, eventually_ge_atTop 3] with k hk hk3
    have h := (s24b_bracket hk3 hc0 hc1 (by linarith)).1
    simp only [Pi.div_apply]
    rw [lt_div_iff₀ (hv0 k), hv]
    calc a * ((1 / 2 : ℝ) ^ (2 * k) / (2 * π)) ≤ c * (1 / 2) ^ (2 * k) / (2 * π) := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ < _ := by linarith
  · filter_upwards [eventually_ge_atTop 3] with k hk3
    have h := (s24b_bracket hk3 (c := 0) le_rfl (by norm_num)
      (by linarith [(s24b_consts hk3).2.1])).2
    simp only [Pi.div_apply]
    rw [div_lt_iff₀ (hv0 k), hv]
    have : 0 < (1 / 2 : ℝ) ^ (2 * k) / (2 * π) := by positivity
    nlinarith

end DLMF.BernoulliEuler
end
