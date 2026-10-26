/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Asymptotics
public import DLMF.BernoulliEuler.Series
public import DLMFMathlib.NumberTheory.EulerPolynomials
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.Multiset.Sort
public import Mathlib.FieldTheory.Separable
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Zeros of Bernoulli and Euler polynomials (DLMF §24.12)

DLMF's `Bₙ(x)` and `Eₙ(x)` on the real line are Mathlib's `bernoulliFun n` and the project's
`eulerFun n` (`DLMFMathlib.NumberTheory.EulerPolynomials`).

## Definitions

* `bernoulliRealZerosGE n`: the real zeros of `Bₙ` in `[1/2, ∞)`, in increasing order and
  counted with multiplicity (they are simple by §24.12(iv)); `bernoulliRealZero n j` is DLMF's
  `x_j^{(n)}` (1-based, `j = 1, 2, …`). Beyond the last zero the totalized value is `0`.
  `bernoulliRealZeroCount n` is DLMF's `R(n)`, the number of real zeros (with multiplicity).
* `eulerRealZerosGE n`, `eulerRealZero n j` (DLMF's `y_j^{(n)}`): the same for `Eₙ`.

## Conventions

* The limits "as `n → ∞` with `m` fixed" for even (odd) `n` are taken along `n = 2k`
  (`n = 2k + 1`), `k → ∞`. The zero `x_{2m}^{(n)}` exists for large `n`, so the totalized value
  does not matter in these limits.
* "No multiple zeros" (§24.12(iv)) is `Polynomial.Separable` over `ℚ`, i.e. no repeated roots in
  an algebraic closure (in particular in `ℂ`). The statement for `Bₙ` is proved for every
  `n ≥ 0` (`B₀ = 1` is a unit), which includes DLMF's `n = 1, 2, …`.
* §24.12(iii) (complex zeros, irreducibility) consists of bibliographic pointers only.
* The numerical tables of zeros referred to elsewhere in the chapter are out of scope.

## Status

The zero counts in `[0, 1]` (§24.12(i)) are proved by Rolle's theorem from the derivative and
shift relations together with the Fourier series of `B₂ₘ` (Mathlib); `R(n) = n` for `n ≤ 5` is
proved from the explicit polynomials. The limits 24.12.4, 24.12.5 and 24.12.8 are proved from the
uniform limits 24.11.5–24.11.6 by a zero-counting (Hurwitz-type) argument, and so is the
corrected 24.12.11. The bounds 24.12.2, 24.12.9, 24.12.10 and the equivalence 24.12.3 are
proved from the Fourier series of `B₂ₖ` and `E₂ₘ₋₁` with explicit tail bounds (sign changes
locate the zero; `n = 2, 4` for 24.12.2 and `n = 5` for 24.12.10, where `y₂` is the double zero
`(1 + √5)/2`, from the explicit polynomials). The count 24.12.6 and the separability statements
of §24.12(iv) remain admitted. 24.12.11 as printed is
false: for odd `n` the limit of `y_{2m}^{(n)}` is `2m - 1/2`, not `m - 1/2`; the corrected
statement `y_m^{(n)} → m - 1/2` is proved (with a proved counterexample to the printed form).

## References

* NIST DLMF §24.12; Brillhart (1969), Dilcher (1988), Delange (1987).
-/

@[expose] public noncomputable section

open Filter Asymptotics Topology Polynomial
open scoped Nat Real

namespace DLMF.BernoulliEuler

/-! ### Definitions -/

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

theorem b24b_zerosGE_sorted (p : ℝ[X]) : (b24b_zerosGE p).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort _ _

theorem b24b_mem_zerosGE {p : ℝ[X]} (hp : p ≠ 0) {x : ℝ} :
    x ∈ b24b_zerosGE p ↔ 1 / 2 ≤ x ∧ p.eval x = 0 := by
  rw [b24b_zerosGE, Multiset.mem_sort, Multiset.mem_filter, mem_roots hp, IsRoot.def, and_comm]

theorem b24b_bernoulli_ne_zero (n : ℕ) : Polynomial.bernoulli n ≠ 0 := by
  intro h
  have := congrArg (fun p => p.coeff n) h
  simp [coeff_bernoulli] at this

theorem b24b_euler_ne_zero (n : ℕ) : Polynomial.euler n ≠ 0 := by
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
theorem b24b_getD_zero_eq {l : List ℝ} {a : ℝ} (hs : l.Pairwise (· ≤ ·)) (ha : a ∈ l)
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
theorem q24b_rolle_bernoulli {k : ℕ} {a b : ℝ} (hab : a < b) (ha : bernoulliFun (k + 1) a = 0)
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
theorem q24b_rolle_euler {k : ℕ} {a b : ℝ} (hab : a < b) (ha : eulerFun (k + 1) a = 0)
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
theorem q24b_bernoulli_odd_ne_zero (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
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
theorem q24b_eulerFun_one (k : ℕ) : eulerFun (k + 1) 1 = -eulerFun (k + 1) 0 := by
  have h := eulerFun_add_one_add (k + 1) 0
  rw [zero_add, zero_pow (Nat.succ_ne_zero k), mul_zero] at h
  linarith

/-- `E₂ₘ₊₂(0) = 0`. -/
theorem q24b_eulerFun_two_mul_add_two_zero (m : ℕ) : eulerFun (2 * m + 2) 0 = 0 := by
  have h1 := q24b_eulerFun_one (2 * m + 1)
  have h2 := eulerFun_one_sub (2 * m + 2) 0
  rw [sub_zero, show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul] at h2
  rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring] at h1
  rw [show 2 * m + 2 = 2 * (m + 1) by ring]
  norm_num at h2
  linarith

/-- `E₂ₘ₊₁(1/2) = 0`. -/
theorem q24b_eulerFun_odd_half (m : ℕ) : eulerFun (2 * m + 1) (1 / 2) = 0 := by
  have h := eulerNumber_eq_zero_of_odd (odd_two_mul_add_one m)
  rw [eulerNumber, mul_eq_zero] at h
  have h' : (euler (2 * m + 1)).eval (1 / 2 : ℚ) = 0 := h.resolve_left (pow_ne_zero _ two_ne_zero)
  have : (1 / 2 : ℝ) = algebraMap ℚ ℝ (1 / 2) := by simp
  rw [eulerFun, this, eval_map, eval₂_at_apply, h', map_zero]

/-- `E₂ₘ₊₁` has no zero in `(0, 1/2)` and `E₂ₘ₊₂` has no zero in `(0, 1)`. -/
theorem q24b_euler_ne_zero (m : ℕ) :
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
theorem q24b_getD_one_eq {l : List ℝ} {a b : ℝ} (hs : l.Pairwise (· ≤ ·)) (ha : a ∈ l)
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
theorem q24b_bernoulli_two_mul_ne_zero {k : ℕ} (hk : 1 ≤ k) : _root_.bernoulli (2 * k) ≠ 0 := by
  intro h0
  have h := hasSum_zeta_nat (k := k) (by omega)
  rw [h0] at h
  have := le_hasSum h 1 (fun j _ => by positivity)
  norm_num at this

/-- `B₂, …, B₅`. -/
theorem q24b_bernoulli_small :
    _root_.bernoulli 2 = 1 / 6 ∧ _root_.bernoulli 3 = 0 ∧ _root_.bernoulli 4 = -1 / 30 ∧
      _root_.bernoulli 5 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  · exact bernoulli'_two
  · exact bernoulli'_three
  · exact bernoulli'_four
  · exact bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

/-- `Bₙ(x) = ∑ₖ (n choose k) Bₖ x^{n-k}`. -/
theorem q24b_bernoulliFun_expand (n : ℕ) (x : ℝ) :
    bernoulliFun n x =
      ∑ k ∈ range (n + 1), ((n.choose k : ℝ) * _root_.bernoulli k) * x ^ (n - k) := by
  simp only [bernoulliFun, Polynomial.bernoulli, Polynomial.map_sum, eval_finsetSum,
    Polynomial.map_monomial, eval_monomial]
  refine sum_congr rfl fun k _ => ?_
  simp only [map_mul, map_natCast, eq_ratCast]; ring

/-- Explicit `B₄(x)`. -/
theorem q24b_B4 (x : ℝ) : bernoulliFun 4 x = x ^ 4 - 2 * x ^ 3 + x ^ 2 - 1 / 30 := by
  obtain ⟨b2, b3, b4, -⟩ := q24b_bernoulli_small
  rw [q24b_bernoulliFun_expand]
  simp [sum_range_succ, b2, b3, b4, Nat.choose]
  norm_num; ring

/-- Explicit `B₅(x)`. -/
theorem q24b_B5 (x : ℝ) :
    bernoulliFun 5 x = x ^ 5 - 5 / 2 * x ^ 4 + 5 / 3 * x ^ 3 - 1 / 6 * x := by
  obtain ⟨b2, b3, b4, b5⟩ := q24b_bernoulli_small
  rw [q24b_bernoulliFun_expand]
  simp [sum_range_succ, b2, b3, b4, b5, Nat.choose]
  norm_num; ring

/-- Explicit `B₂(x)`. -/
theorem q24b_B2 (x : ℝ) : bernoulliFun 2 x = x ^ 2 - x + 1 / 6 := by
  obtain ⟨b2, -⟩ := q24b_bernoulli_small
  rw [q24b_bernoulliFun_expand]
  simp [sum_range_succ, b2, Nat.choose]
  norm_num; ring

/-- Explicit `B₃(x)`. -/
theorem q24b_B3 (x : ℝ) : bernoulliFun 3 x = x ^ 3 - 3 / 2 * x ^ 2 + 1 / 2 * x := by
  obtain ⟨b2, b3, -⟩ := q24b_bernoulli_small
  rw [q24b_bernoulliFun_expand]
  simp [sum_range_succ, b2, b3, Nat.choose]
  norm_num; ring

/-- Intermediate value theorem for a sign change. -/
theorem q24b_exists_root {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b)
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
theorem q24b_roots_card_eq {p : ℝ[X]} {n : ℕ} (hdeg : p.natDegree ≤ n) (l : List ℝ)
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
theorem s24b_first_zero_bracket {n : ℕ} {lo hi : ℝ} (hlh : lo < hi)
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
theorem s24b_fourier_tail {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
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
theorem s24b_main_terms {N : ℕ} (hN : N ≠ 0) (θ : ℝ) :
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
theorem s24b_consts {k : ℕ} (hk : 3 ≤ k) :
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
theorem s24b_g_approx {k : ℕ} (hk : 3 ≤ k) {θ : ℝ} (h1 : -(3 * π / 2) ≤ θ) (h2 : θ ≤ π / 2) :
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
theorem s24b_g_pos {k : ℕ} (hk : 3 ≤ k) : 0 < s24b_g k ((1 / 2) ^ (2 * k)) := by
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
theorem s24b_g_neg {k : ℕ} (hk : 3 ≤ k) {c θ : ℝ} (hc0 : 0 ≤ c)
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
theorem s24b_bracket {k : ℕ} (hk : 3 ≤ k) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
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

theorem s24b_bounds_two :
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

theorem s24b_bounds_four :
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


/-! ### Limits of zeros from uniform convergence (24.12.4, 24.12.5, 24.12.8)

If `c_k P_k → g` and `c_k P_k' → g'` uniformly on compact subsets of `[1/2, ∞)`, where `g` has
simple zeros `z_1 < z_2 < ⋯` in `[1/2, ∞)`, then the `j`-th zero of `P_k` in `[1/2, ∞)` tends
to `z_j` (Hurwitz-type argument by counting zeros, Rolle and the mean value theorem). The
uniform limits are DLMF 24.11.5–24.11.6 (`DLMF.BernoulliEuler.Asymptotics`). -/
/-- In a sorted list, an index below the number of entries `< c` gives an entry `< c`. -/
theorem r24b_getD_lt_of_length_filter {l : List ℝ} (hs : l.Pairwise (· ≤ ·)) {c : ℝ} {i : ℕ}
    (h : i < (l.filter (fun x => decide (x < c))).length) : l.getD i 0 < c := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
    have hs' := List.pairwise_cons.mp hs
    by_cases hac : a < c
    · rw [List.filter_cons_of_pos (by simpa using hac), List.length_cons] at h
      rcases i with _ | i
      · simpa using hac
      · simp only [List.getD_cons_succ]
        exact ih hs'.2 (by omega)
    · have : l.filter (fun x => decide (x < c)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        have := hs'.1 x hx
        simp only [decide_eq_true_eq, not_lt]
        linarith [not_lt.mp hac]
      rw [List.filter_cons_of_neg (by simpa using hac), this] at h
      simp at h

/-- In a sorted list, an entry `< c` at index `i` lies among the entries `< c`. -/
theorem r24b_length_filter_of_getD_lt {l : List ℝ} (hs : l.Pairwise (· ≤ ·)) {c : ℝ} {i : ℕ}
    (hi : i < l.length) (h : l.getD i 0 < c) : i < (l.filter (fun x => decide (x < c))).length := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    have hs' := List.pairwise_cons.mp hs
    rcases i with _ | i
    · simp only [List.getD_cons_zero] at h
      rw [List.filter_cons_of_pos (by simpa using h)]; simp
    · simp only [List.getD_cons_succ] at h
      simp only [List.length_cons] at hi
      have hmem : l.getD i 0 ∈ l := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
      have hac : a < c := lt_of_le_of_lt (hs'.1 _ hmem) h
      rw [List.filter_cons_of_pos (by simpa using hac), List.length_cons]
      have := ih hs'.2 (by omega) h
      omega

/-- The number of roots (with multiplicity) of `p` in `[1/2, c)`. -/
noncomputable def r24b_count (p : ℝ[X]) (c : ℝ) : ℕ :=
  Multiset.card (p.roots.filter (fun x => 1 / 2 ≤ x ∧ x < c))

/-- The number of listed zeros below `c` is `r24b_count p c`. -/
theorem r24b_length_filter_zerosGE (p : ℝ[X]) (c : ℝ) :
    ((b24b_zerosGE p).filter (fun x => decide (x < c))).length = r24b_count p c := by
  rw [r24b_count, ← Multiset.coe_card, ← Multiset.filter_coe, b24b_zerosGE, Multiset.sort_eq,
    Multiset.filter_filter]
  congr 2
  funext x; simp [and_comm]

/-- If `r24b_count p (z - r) = j - 1` and `r24b_count p (z + r) = j`, then the `j`-th zero of
`p` in `[1/2, ∞)` lies in `[z - r, z + r)`. -/
theorem r24b_getD_mem_of_count {p : ℝ[X]} {j : ℕ} (hj : 1 ≤ j) {a b : ℝ}
    (ha : r24b_count p a = j - 1) (hb : r24b_count p b = j) :
    a ≤ (b24b_zerosGE p).getD (j - 1) 0 ∧ (b24b_zerosGE p).getD (j - 1) 0 < b := by
  have hs := b24b_zerosGE_sorted p
  have hlb : j - 1 < ((b24b_zerosGE p).filter (fun x => decide (x < b))).length := by
    rw [r24b_length_filter_zerosGE, hb]; omega
  refine ⟨?_, r24b_getD_lt_of_length_filter hs hlb⟩
  by_contra hlt
  push Not at hlt
  have hlen : j - 1 < (b24b_zerosGE p).length :=
    lt_of_lt_of_le hlb (List.length_filter_le _ _)
  have := r24b_length_filter_of_getD_lt hs hlen hlt
  rw [r24b_length_filter_zerosGE, ha] at this
  omega

/-- Splitting the zero count at `a ≤ b`. -/
theorem r24b_count_add {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b) :
    r24b_count p b = r24b_count p a +
      Multiset.card (p.roots.filter (fun x => 1 / 2 ≤ x ∧ a ≤ x ∧ x < b)) := by
  rw [r24b_count, r24b_count, ← Multiset.card_add,
    ← Multiset.filter_add_not (fun x => x < a) (p.roots.filter fun x => 1 / 2 ≤ x ∧ x < b),
    Multiset.filter_filter, Multiset.filter_filter]
  congr 2
  · congr 1; funext x; apply propext; constructor
    · rintro ⟨h3, h1, h2⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h3, h1, by linarith⟩
  · congr 1; funext x; apply propext; constructor
    · rintro ⟨h3, h1, h2⟩; exact ⟨h1, not_lt.mp h3, h2⟩
    · rintro ⟨h1, h3, h2⟩; exact ⟨not_lt.mpr h3, h1, h2⟩

/-- No roots satisfy `q` if `p` does not vanish where `q` holds. -/
theorem r24b_card_filter_eq_zero {p : ℝ[X]} {q : ℝ → Prop} [DecidablePred q]
    (h : ∀ x, q x → p.eval x ≠ 0) : Multiset.card (p.roots.filter q) = 0 := by
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro x hx hq
  exact h x hq (isRoot_of_mem_roots hx)

/-- Exactly one root (with multiplicity) satisfies `q` when `ζ` is the unique zero there and
simple. -/
theorem r24b_card_filter_eq_one {p : ℝ[X]} (hp : p ≠ 0) {q : ℝ → Prop} [DecidablePred q] {ζ : ℝ}
    (hζ : q ζ) (hζ0 : p.eval ζ = 0) (hd : p.derivative.eval ζ ≠ 0)
    (huniq : ∀ x, q x → p.eval x = 0 → x = ζ) : Multiset.card (p.roots.filter q) = 1 := by
  have hfilt : p.roots.filter q = p.roots.filter (fun x => x = ζ) := by
    refine Multiset.filter_congr fun x hx => ⟨fun h => huniq x h (isRoot_of_mem_roots hx), ?_⟩
    rintro rfl; exact hζ
  rw [hfilt, Multiset.filter_eq', Multiset.card_replicate, count_roots]
  have h1 : 1 ≤ p.rootMultiplicity ζ := (rootMultiplicity_pos hp).mpr hζ0
  have h2 : p.rootMultiplicity ζ ≤ 1 := by
    by_contra h; push Not at h
    exact hd ((one_lt_rootMultiplicity_iff_isRoot hp).mp h).2
  omega

/-- Rolle: a function with nonvanishing derivative on `[a, b]` has at most one zero there. -/
theorem r24b_zero_unique {F F' : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (F' x) x) {a b : ℝ}
    (hF' : ∀ x ∈ Set.Icc a b, F' x ≠ 0) {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hFx : F x = 0) (hFy : F y = 0) : x = y := by
  by_contra hne
  have hcont : Continuous F := continuous_iff_continuousAt.mpr fun t => (hF t).continuousAt
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hlt hcont.continuousOn (hFx.trans hFy.symm)
      fun t _ => hF t
    exact hF' c ⟨by linarith [hx.1, hc.1], by linarith [hy.2, hc.2]⟩ hc0
  · obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hlt hcont.continuousOn (hFy.trans hFx.symm)
      fun t _ => hF t
    exact hF' c ⟨by linarith [hy.1, hc.1], by linarith [hx.2, hc.2]⟩ hc0

/-- Mean value estimate at a simple zero: if `g z = 0` and `|g' - s| < |s|/4` on `[z - r, z + r]`,
then `s g(z ± r) ≷ ± (3/4) r s²`. -/
theorem r24b_sign_at_zero {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) {z r s : ℝ}
    (hr : 0 < r) (hgz : g z = 0) (hd : ∀ x, |x - z| ≤ r → |g' x - s| < |s| / 4) :
    3 / 4 * r * s ^ 2 < s * g (z + r) ∧ s * g (z - r) < -(3 / 4 * r * s ^ 2) := by
  have hcont : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  have key : ∀ ξ, |ξ - z| ≤ r → 3 / 4 * s ^ 2 < s * g' ξ := by
    intro ξ hξ
    have h1 := hd ξ hξ
    have h2 : |s * (g' ξ - s)| < s ^ 2 / 4 + 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg s, abs_nonneg (g' ξ - s), sq_abs s]
    by_cases hs : s = 0
    · subst hs; simp at h1; linarith [abs_nonneg (g' ξ)]
    have hsp : 0 < |s| := abs_pos.mpr hs
    have h3 : |s * (g' ξ - s)| < s ^ 2 / 4 := by
      rw [abs_mul, ← sq_abs s]
      nlinarith
    have := (abs_lt.mp h3).1
    nlinarith
  constructor
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope g g' (by linarith : z < z + r)
      hcont.continuousOn fun t _ => hg t
    rw [hgz, sub_zero, show z + r - z = r by ring] at hξe
    have := key ξ (by rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2])
    rw [hξe] at this
    have h' : s * g (z + r) = r * (s * (g (z + r) / r)) := by field_simp
    rw [h']
    nlinarith
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope g g' (by linarith : z - r < z)
      hcont.continuousOn fun t _ => hg t
    rw [hgz, zero_sub, show z - (z - r) = r by ring] at hξe
    have := key ξ (by rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2])
    rw [hξe] at this
    have h' : s * g (z - r) = -(r * (s * (-g (z - r) / r))) := by field_simp
    rw [h']
    nlinarith

/-- Zeros of a uniformly convergent sequence of polynomials: if `c_k P_k → g` and
`c_k P_k' → g'` uniformly on bounded subsets of `[1/2, ∞)`, and the zeros of `g` in `[1/2, ∞)`
are the simple zeros `z₁ < z₂ < ⋯`, then the `j`-th zero of `P_k` in `[1/2, ∞)` tends to `z_j`.
(If `z₁ = 1/2` we require `P_k(1/2) = 0`.) -/
theorem r24b_tendsto_zerosGE (P : ℕ → ℝ[X]) (c : ℕ → ℝ) (hc : ∀ k, c k ≠ 0)
    (g g' : ℝ → ℝ) (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g')
    (z : ℕ → ℝ) (hz : StrictMono z) (hz1 : 1 / 2 ≤ z 1)
    (hzero : ∀ x, 1 / 2 ≤ x → g x = 0 → ∃ i, 1 ≤ i ∧ x = z i)
    (hgz : ∀ i, 1 ≤ i → g (z i) = 0) (hg'z : ∀ i, 1 ≤ i → g' (z i) ≠ 0)
    (hhalf : z 1 = 1 / 2 → ∀ k, (P k).eval (1 / 2) = 0)
    (hconv : ∀ M ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x, 1 / 2 ≤ x → x ≤ M →
      |c k * (P k).eval x - g x| < ε ∧ |c k * (P k).derivative.eval x - g' x| < ε)
    {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun k => (b24b_zerosGE (P k)).getD (j - 1) 0) atTop (𝓝 (z j)) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hgcont : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  -- choice of the radius `r`
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ε / 2 ∧ r < 1 ∧ (z 1 ≠ 1 / 2 → r < z 1 - 1 / 2) ∧
      (∀ i ∈ Finset.Icc 1 j, 2 * r < z (i + 1) - z i) ∧
      (∀ i ∈ Finset.Icc 1 j, ∀ x, |x - z i| ≤ r → |g' x - g' (z i)| < |g' (z i)| / 4) := by
    have hlt : ∀ a : ℝ, 0 < a → ∀ᶠ r in 𝓝[>] (0 : ℝ), r < a := fun a ha =>
      (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds
    have e3 : ∀ᶠ r in 𝓝[>] (0 : ℝ), z 1 ≠ 1 / 2 → r < z 1 - 1 / 2 := by
      by_cases h1 : z 1 = 1 / 2
      · exact Eventually.of_forall fun _ h => absurd h1 h
      · exact (hlt _ (by have := lt_of_le_of_ne hz1 (Ne.symm h1); linarith)).mono
          fun _ h _ => h
    have e4 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ i ∈ Finset.Icc 1 j, 2 * r < z (i + 1) - z i := by
      refine (eventually_all_finset _).mpr fun i _ => ?_
      have : 0 < z (i + 1) - z i := sub_pos.mpr (hz (Nat.lt_succ_self i))
      exact (hlt _ (by linarith : 0 < (z (i + 1) - z i) / 2)).mono fun r hr => by linarith
    have e5 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ i ∈ Finset.Icc 1 j, ∀ x, |x - z i| ≤ r →
        |g' x - g' (z i)| < |g' (z i)| / 4 := by
      refine (eventually_all_finset _).mpr fun i hi => ?_
      have hs : 0 < |g' (z i)| / 4 := by
        have := hg'z i (Finset.mem_Icc.mp hi).1; positivity
      obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff.mp
        ((hg'.tendsto (z i)).eventually (Metric.ball_mem_nhds _ hs))
      refine (hlt ρ hρ).mono fun r hr x hx => ?_
      have := hρ' (show dist x (z i) < ρ by rw [Real.dist_eq]; linarith)
      simpa [Metric.mem_ball, Real.dist_eq] using this
    filter_upwards [hlt (ε / 2) (by linarith), hlt 1 one_pos, e3, e4, e5] with r h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨r, ⟨hrε, hr1, hrz1, hgap, hg'r⟩, hr0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hr0 : (0 : ℝ) < r := hr0
  have hzle : ∀ {a b}, a ≤ b → z a ≤ z b := fun h => hz.monotone h
  have hzj : ∀ i ∈ Finset.Icc 1 j, z i ≤ z j := fun i hi => hzle (Finset.mem_Icc.mp hi).2
  -- the compact set where `g` has no zeros
  set Kc : Set ℝ := Set.Icc (1 / 2) (z j + r) ∩ ⋂ i ∈ Finset.Icc 1 j, {x | r ≤ |x - z i|}
  have hKc : IsCompact Kc := isCompact_Icc.inter_right (isClosed_biInter fun i _ =>
    isClosed_le continuous_const (continuous_id.sub continuous_const).abs)
  have hgK : ∀ x ∈ Kc, g x ≠ 0 := by
    intro x hx h0
    obtain ⟨i, hi, rfl⟩ := hzero x hx.1.1 h0
    have hx2 := Set.mem_iInter₂.mp hx.2
    by_cases hij : i ≤ j
    · have := hx2 i (Finset.mem_Icc.mpr ⟨hi, hij⟩)
      simp at this; linarith
    · have h1 := hgap j (Finset.mem_Icc.mpr ⟨hj, le_rfl⟩)
      have h2 : z (j + 1) ≤ z i := hzle (by omega)
      linarith [hx.1.2]
  obtain ⟨η0, hη0, hη0K⟩ : ∃ η0 : ℝ, 0 < η0 ∧ ∀ x ∈ Kc, η0 ≤ |g x| := by
    rcases Kc.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun x hx => by rw [he] at hx; exact hx.elim⟩
    · obtain ⟨x0, hx0, hmin⟩ := hKc.exists_isMinOn hne (hgcont.abs.continuousOn)
      exact ⟨|g x0|, abs_pos.mpr (hgK x0 hx0), fun x hx => hmin hx⟩
  set s : ℕ → ℝ := fun i => g' (z i)
  have hs0 : ∀ i ∈ Finset.Icc 1 j, 0 < |s i| := fun i hi =>
    abs_pos.mpr (hg'z i (Finset.mem_Icc.mp hi).1)
  have hk2 : ∀ i ∈ Finset.Icc 1 j, ∀ᶠ k in atTop, ∀ x, 1 / 2 ≤ x → x ≤ z j + 1 →
      |c k * (P k).eval x - g x| < min (r * |s i| / 2) (|s i| / 4) ∧
        |c k * (P k).derivative.eval x - g' x| < min (r * |s i| / 2) (|s i| / 4) := fun i hi =>
    hconv _ _ (lt_min (by have := hs0 i hi; positivity) (by have := hs0 i hi; positivity))
  filter_upwards [hconv (z j + 1) η0 hη0, (eventually_all_finset _).mpr hk2] with k hk1 hk2
  set F : ℝ → ℝ := fun x => c k * (P k).eval x
  set F' : ℝ → ℝ := fun x => c k * (P k).derivative.eval x
  have hF : ∀ x, HasDerivAt F (F' x) x := fun x => ((P k).hasDerivAt x).const_mul (c k)
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun t => (hF t).continuousAt
  have hPF : ∀ x, (P k).eval x = 0 ↔ F x = 0 := fun x => by
    simp only [F, mul_eq_zero, hc k, false_or]
  have hnoK : ∀ x ∈ Kc, (P k).eval x ≠ 0 := by
    intro x hx h0
    have := (hk1 x hx.1.1 (by linarith [hx.1.2])).1
    rw [show c k * (P k).eval x = 0 by rw [h0, mul_zero], zero_sub, abs_neg] at this
    linarith [hη0K x hx]
  -- one simple root near each `z i`
  have hone : ∀ i ∈ Finset.Icc 1 j, Multiset.card ((P k).roots.filter
      (fun x => 1 / 2 ≤ x ∧ z i - r ≤ x ∧ x < z i + r)) = 1 := by
    intro i hi
    have hi1 := (Finset.mem_Icc.mp hi).1
    have hbd := hk2 i hi
    have hF'ne : ∀ x, 1 / 2 ≤ x → |x - z i| ≤ r → F' x ≠ 0 := by
      intro x hx1 hx2 h0
      have h1 := (hbd x hx1 (by
        have := hzj i hi; rw [abs_le] at hx2; linarith)).2
      have h2 := hg'r i hi x hx2
      have hm := min_le_right (r * |s i| / 2) (|s i| / 4)
      change |F' x - g' x| < _ at h1
      rw [h0, zero_sub, abs_neg] at h1
      have : |s i| ≤ |g' x| + |g' x - s i| := by
        calc |s i| = |g' x - (g' x - s i)| := by ring_nf
          _ ≤ |g' x| + |g' x - s i| := abs_sub _ _
      have h2' : |g' x - s i| < |s i| / 4 := h2
      linarith [hs0 i hi]
    obtain ⟨ζ, hζ1, hζ2, hζ3, hζ0⟩ : ∃ ζ, 1 / 2 ≤ ζ ∧ z i - r ≤ ζ ∧ ζ < z i + r ∧ F ζ = 0 := by
      by_cases hzi : z i = 1 / 2
      · have hi1' : i = 1 := by
          by_contra hne
          have : z 1 < z i := hz (by omega)
          linarith
        subst hi1'
        refine ⟨1 / 2, le_rfl, by linarith, by linarith, (hPF _).mp (hhalf hzi k)⟩
      · have hzr : 1 / 2 ≤ z i - r := by
          rcases Nat.lt_or_ge i 2 with h | h
          · have : i = 1 := by omega
            subst this; linarith [hrz1 hzi]
          · have h12 := hgap 1 (Finset.mem_Icc.mpr ⟨le_rfl, hj⟩)
            have : z 2 ≤ z i := hzle h
            linarith
        obtain ⟨hp, hm⟩ := r24b_sign_at_zero hg hr0 (hgz i hi1) (hg'r i hi)
        have hb1 := (hbd (z i + r) (by linarith) (by linarith [hzj i hi])).1
        have hb2 := (hbd (z i - r) hzr (by linarith [hzj i hi])).1
        have hmin := min_le_left (r * |s i| / 2) (|s i| / 4)
        have hsi := hs0 i hi
        change |F (z i + r) - g (z i + r)| < _ at hb1
        change |F (z i - r) - g (z i - r)| < _ at hb2
        have e1 : |s i * (F (z i + r) - g (z i + r))| < r * s i ^ 2 / 2 := by
          rw [abs_mul, ← sq_abs (s i)]
          nlinarith
        have e2 : |s i * (F (z i - r) - g (z i - r))| < r * s i ^ 2 / 2 := by
          rw [abs_mul, ← sq_abs (s i)]
          nlinarith
        have f1 : 0 < s i * F (z i + r) := by
          have := (abs_lt.mp e1).1; nlinarith
        have f2 : s i * F (z i - r) < 0 := by
          have := (abs_lt.mp e2).2; nlinarith
        have hprod : F (z i - r) * F (z i + r) < 0 := by
          have : (s i * F (z i - r)) * (s i * F (z i + r)) < 0 := mul_neg_of_neg_of_pos f2 f1
          nlinarith [sq_nonneg (s i), sq_pos_of_pos hsi, sq_abs (s i)]
        obtain ⟨ζ, hζ, hζ0⟩ := q24b_exists_root hFc (by linarith) hprod
        exact ⟨ζ, by linarith [hζ.1], hζ.1.le, hζ.2, hζ0⟩
    have hP0 : P k ≠ 0 := fun h0 => hF'ne ζ hζ1 (by rw [abs_le]; constructor <;> linarith)
      (by simp only [F', h0, derivative_zero, eval_zero, mul_zero])
    have hIcc : ∀ x, 1 / 2 ≤ x → z i - r ≤ x → x < z i + r →
        x ∈ Set.Icc (max (1 / 2) (z i - r)) (z i + r) := fun x h1 h2 h3 =>
      ⟨max_le h1 h2, h3.le⟩
    refine r24b_card_filter_eq_one hP0 ⟨hζ1, hζ2, hζ3⟩ ((hPF ζ).mpr hζ0) ?_ ?_
    · intro hd
      exact hF'ne ζ hζ1 (by rw [abs_le]; constructor <;> linarith)
        (by simp only [F', hd, mul_zero])
    · rintro x ⟨hx1, hx2, hx3⟩ hx0
      refine r24b_zero_unique hF (fun y hy => hF'ne y (le_of_max_le_left hy.1)
        (by rw [abs_le]; constructor <;> linarith [le_of_max_le_right hy.1, hy.2]))
        (hIcc x hx1 hx2 hx3) (hIcc ζ hζ1 hζ2 hζ3) ((hPF x).mp hx0) hζ0
  -- counting
  have hC0 : r24b_count (P k) (z 1 - r) = 0 := by
    refine r24b_card_filter_eq_zero fun x ⟨hx1, hx2⟩ => hnoK x ⟨⟨hx1, ?_⟩, ?_⟩
    · linarith [hzj 1 (Finset.mem_Icc.mpr ⟨le_rfl, hj⟩)]
    · refine Set.mem_iInter₂.mpr fun l hl => ?_
      have := hzle (Finset.mem_Icc.mp hl).1
      show r ≤ |x - z l|
      rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
  have hCgap : ∀ i, 1 ≤ i → i < j →
      r24b_count (P k) (z (i + 1) - r) = r24b_count (P k) (z i + r) := by
    intro i hi hij
    have hg1 := hgap i (Finset.mem_Icc.mpr ⟨hi, hij.le⟩)
    rw [r24b_count_add (show z i + r ≤ z (i + 1) - r by linarith)]
    have h0 : ∀ x, (1 / 2 ≤ x ∧ z i + r ≤ x ∧ x < z (i + 1) - r) → (P k).eval x ≠ 0 := by
      rintro x ⟨hx1, hx2, hx3⟩
      refine hnoK x ⟨⟨hx1, ?_⟩, ?_⟩
      · linarith [hzj (i + 1) (Finset.mem_Icc.mpr ⟨by omega, hij⟩)]
      · refine Set.mem_iInter₂.mpr fun l hl => ?_
        show r ≤ |x - z l|
        rcases Nat.lt_or_ge i l with h | h
        · have := hzle (show i + 1 ≤ l by omega)
          rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
        · have := hzle h
          rw [abs_of_nonneg (by linarith)]; linarith
    rw [r24b_card_filter_eq_zero h0, add_zero]
  have hCstep : ∀ i ∈ Finset.Icc 1 j,
      r24b_count (P k) (z i + r) = r24b_count (P k) (z i - r) + 1 := by
    intro i hi
    rw [r24b_count_add (show z i - r ≤ z i + r by linarith), hone i hi]
  have hind : ∀ i, 1 ≤ i → i ≤ j → r24b_count (P k) (z i - r) = i - 1 ∧
      r24b_count (P k) (z i + r) = i := by
    intro i hi hij
    induction i, hi using Nat.le_induction with
    | base =>
      exact ⟨hC0, by rw [hCstep 1 (Finset.mem_Icc.mpr ⟨le_rfl, hj⟩), hC0]⟩
    | succ i hi ih =>
      obtain ⟨_, h2⟩ := ih (by omega)
      have h3 := hCgap i hi (by omega)
      refine ⟨by rw [h3, h2]; omega, ?_⟩
      rw [hCstep (i + 1) (Finset.mem_Icc.mpr ⟨by omega, hij⟩), h3, h2]
  obtain ⟨hA, hB⟩ := hind j hj le_rfl
  obtain ⟨h1, h2⟩ := r24b_getD_mem_of_count hj hA hB
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith


/-- Transfer complex uniform convergence on compacts to real bounds on `[1/2, M]`. -/
theorem r24b_real_of_unif {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    (h : ∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn F G atTop K) (a : ℂ)
    (f : ℕ → ℝ → ℝ) (gr : ℝ → ℝ) (hf : ∀ k x, (f k x : ℂ) = a * F k x)
    (hg : ∀ x, (gr x : ℂ) = a * G x) (M ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x : ℝ, 1 / 2 ≤ x → x ≤ M → |f k x - gr x| < ε := by
  have hpos : 0 < ε / (‖a‖ + 1) := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (h _ (isCompact_closedBall (0 : ℂ) M)) _ hpos]
    with k hk x hx1 hxM
  have hx : (x : ℂ) ∈ Metric.closedBall (0 : ℂ) M := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]; exact hxM
  have h1 := hk _ hx
  rw [dist_eq_norm, norm_sub_rev] at h1
  have h2 : |f k x - gr x| = ‖a‖ * ‖F k x - G x‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub, hf, hg, ← mul_sub, norm_mul]
  rw [h2]
  calc ‖a‖ * ‖F k x - G x‖ ≤ ‖a‖ * (ε / (‖a‖ + 1)) := by gcongr
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [norm_nonneg a]

/-- Shift an eventual statement by one index. -/
theorem r24b_eventually_shift {Q : ℕ → Prop} (h : ∀ᶠ k in atTop, Q k) :
    ∀ᶠ k in atTop, 1 ≤ k ∧ Q (k - 1) :=
  (eventually_ge_atTop 1).and ((tendsto_sub_atTop_nat 1).eventually h)

/-- `(-1)^(m-1) = -(-1)^m`. -/
theorem r24b_neg_one_zpow (m : ℕ) : (-1 : ℂ) ^ ((m : ℤ) - 1) = -(-1) ^ m := by
  rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_one]; ring

/-- Real evaluation of a rational polynomial, cast to `ℂ`, is complex evaluation. -/
theorem r24b_eval_map_cplx (p : ℚ[X]) (x : ℝ) :
    (((p.map (algebraMap ℚ ℝ)).eval x : ℝ) : ℂ) = aeval (x : ℂ) p :=
  (b24a_aeval_ofReal p x).symm


/-- Zeros of `cos (2πx)` in `[1/2, ∞)`. -/
theorem r24b_cos_zero {x : ℝ} (hx : 1 / 2 ≤ x) (h : Real.cos (2 * π * x) = 0) :
    ∃ i : ℕ, 1 ≤ i ∧ x = (i : ℝ) / 2 + 1 / 4 := by
  obtain ⟨l, hl⟩ := Real.cos_eq_zero_iff.mp h
  have hx' : x = (2 * l + 1) / 4 := by
    have := Real.pi_pos; field_simp at hl ⊢; nlinarith
  have hl1 : (1 : ℝ) ≤ l := by
    have : (0 : ℝ) < l := by rw [hx'] at hx; linarith
    have : (0 : ℤ) < l := by exact_mod_cast this
    exact_mod_cast (show (1 : ℤ) ≤ l by omega)
  lift l to ℕ using (by exact_mod_cast (by linarith : (0 : ℝ) ≤ l))
  exact ⟨l, by exact_mod_cast hl1, by rw [hx']; push_cast; ring⟩

/-- Zeros of `sin (a πx)` (`a > 0`) in `[1/2, ∞)`. -/
theorem r24b_sin_zero {a x : ℝ} (ha : 0 < a) (h : Real.sin (a * π * x) = 0) :
    ∃ n : ℤ, x = n / a := by
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
  refine ⟨n, ?_⟩
  have := Real.pi_pos; field_simp; nlinarith

/-- `x_j^{(2k)} → j/2 + 1/4` as `k → ∞` (the zeros of `cos 2πx`). -/
theorem r24b_bernoulli_even_zero {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun k => bernoulliRealZero (2 * k) j) atTop (𝓝 ((j : ℝ) / 2 + 1 / 4)) := by
  have hcplx : ∀ (k : ℕ) (x : ℝ), (((-(-1) ^ k * (2 * π) ^ (2 * k) / (2 * (2 * k)!) *
      ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℝ)).eval x : ℝ)) : ℂ) =
      1 * ((-1 : ℂ) ^ ((k : ℤ) - 1) * (2 * π) ^ (2 * k) / (2 * (2 * k)!) *
        bernoulliPolyB (2 * k) x) := by
    intro k x
    rw [r24b_neg_one_zpow, bernoulliPolyB, ← r24b_eval_map_cplx]; push_cast; ring
  have hcplx' : ∀ (m : ℕ) (x : ℝ), (((-(-1) ^ (m + 1) * (2 * π) ^ (2 * (m + 1)) /
      (2 * (2 * (m + 1))!) *
      ((Polynomial.bernoulli (2 * (m + 1))).map (algebraMap ℚ ℝ)).derivative.eval x : ℝ)) : ℂ) =
      (-(2 * π) : ℂ) * ((-1 : ℂ) ^ ((m : ℤ) - 1) * (2 * π) ^ (2 * m + 1) / (2 * (2 * m + 1)!) *
        bernoulliPolyB (2 * m + 1) x) := by
    intro m x
    rw [derivative_map, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, derivative_bernoulli_add_one,
      r24b_neg_one_zpow, bernoulliPolyB, ← r24b_eval_map_cplx, Nat.factorial_succ]
    simp only [Polynomial.map_mul, eval_mul, Polynomial.map_add, Polynomial.map_natCast,
      Polynomial.map_one, eval_add, eval_natCast, eval_one]
    have hf : ((2 * m + 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hm : (2 * (m : ℂ) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * m + 1)
    push_cast
    field_simp
    ring
  refine r24b_tendsto_zerosGE (fun k => (Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℝ))
    (fun k => -(-1) ^ k * (2 * π) ^ (2 * k) / (2 * (2 * k)!)) (fun k => ?_)
    (fun x => Real.cos (2 * π * x)) (fun x => -(2 * π) * Real.sin (2 * π * x)) (fun x => ?_)
    (by fun_prop) (fun i => (i : ℝ) / 2 + 1 / 4) (fun a b hab => ?_) (by norm_num)
    (fun x hx h => r24b_cos_zero hx h) (fun i _ => ?_) (fun i _ => ?_) (fun h => ?_) ?_ hj
  · have := Nat.factorial_pos (2 * k)
    have := Real.pi_pos
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (by norm_num)))
      (pow_ne_zero _ (by positivity))) (by positivity)
  · have := ((hasDerivAt_id x).const_mul (2 * π)).cos
    simpa [mul_comm] using this
  · have : (a : ℝ) < b := by exact_mod_cast hab
    simp only; linarith
  · show Real.cos (2 * π * ((i : ℝ) / 2 + 1 / 4)) = 0
    rw [Real.cos_eq_zero_iff]; exact ⟨i, by push_cast; ring⟩
  · have hc : Real.cos (2 * π * ((i : ℝ) / 2 + 1 / 4)) = 0 := by
      rw [Real.cos_eq_zero_iff]; exact ⟨i, by push_cast; ring⟩
    have hs := Real.sin_sq_add_cos_sq (2 * π * ((i : ℝ) / 2 + 1 / 4))
    rw [hc] at hs
    have := Real.pi_pos
    intro h0
    have : Real.sin (2 * π * ((i : ℝ) / 2 + 1 / 4)) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · linarith
      · exact h
    rw [this] at hs; norm_num at hs
  · norm_num at h
  · intro M ε hε
    filter_upwards [r24b_real_of_unif (fun K hK => tendstoUniformlyOn_bernoulli_even hK) 1 _
        (fun x => Real.cos (2 * π * x)) hcplx (fun x => by push_cast; ring) M ε hε,
      r24b_eventually_shift (r24b_real_of_unif (fun K hK => tendstoUniformlyOn_bernoulli_odd hK)
        (-(2 * π)) _ (fun x => -(2 * π) * Real.sin (2 * π * x)) hcplx'
        (fun x => by push_cast; ring) M ε hε)] with k h1 h2 x hx1 hxM
    obtain ⟨hk1, h2⟩ := h2
    refine ⟨h1 x hx1 hxM, ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact h2 x hx1 hxM


/-- Zeros of `sin (2πx)`, `sin (πx)` are simple: the derivative `cos` is nonzero there. -/
theorem r24b_cos_ne_of_sin {θ : ℝ} (h : Real.sin θ = 0) : Real.cos θ ≠ 0 := by
  intro h0; have hs := Real.sin_sq_add_cos_sq θ; rw [h, h0] at hs; norm_num at hs

/-- `x_j^{(2k+1)} → j/2` as `k → ∞` (the zeros of `sin 2πx`). -/
theorem r24b_bernoulli_odd_zero {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun k => bernoulliRealZero (2 * k + 1) j) atTop (𝓝 ((j : ℝ) / 2)) := by
  have hcplx : ∀ (k : ℕ) (x : ℝ), (((-(-1) ^ k * (2 * π) ^ (2 * k + 1) / (2 * (2 * k + 1)!) *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℝ)).eval x : ℝ)) : ℂ) =
      1 * ((-1 : ℂ) ^ ((k : ℤ) - 1) * (2 * π) ^ (2 * k + 1) / (2 * (2 * k + 1)!) *
        bernoulliPolyB (2 * k + 1) x) := by
    intro k x
    rw [r24b_neg_one_zpow, bernoulliPolyB, ← r24b_eval_map_cplx]; push_cast; ring
  have hcplx' : ∀ (k : ℕ) (x : ℝ), (((-(-1) ^ k * (2 * π) ^ (2 * k + 1) / (2 * (2 * k + 1)!) *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℝ)).derivative.eval x : ℝ)) : ℂ) =
      ((2 * π : ℝ) : ℂ) * ((-1 : ℂ) ^ ((k : ℤ) - 1) * (2 * π) ^ (2 * k) / (2 * (2 * k)!) *
        bernoulliPolyB (2 * k) x) := by
    intro k x
    rw [derivative_map, derivative_bernoulli_add_one,
      r24b_neg_one_zpow, bernoulliPolyB, ← r24b_eval_map_cplx, Nat.factorial_succ]
    simp only [Polynomial.map_mul, eval_mul, Polynomial.map_add, Polynomial.map_natCast,
      Polynomial.map_one, eval_add, eval_natCast, eval_one]
    have hf : ((2 * k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hm : (2 * (k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * k)
    push_cast
    field_simp
    ring
  refine r24b_tendsto_zerosGE (fun k => (Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℝ))
    (fun k => -(-1) ^ k * (2 * π) ^ (2 * k + 1) / (2 * (2 * k + 1)!)) (fun k => ?_)
    (fun x => Real.sin (2 * π * x)) (fun x => (2 * π) * Real.cos (2 * π * x)) (fun x => ?_)
    (by fun_prop) (fun i => (i : ℝ) / 2) (fun a b hab => ?_) (by norm_num)
    (fun x hx h => ?_) (fun i _ => ?_) (fun i _ => ?_) (fun _ k => ?_) ?_ hj
  · have := Nat.factorial_pos (2 * k + 1)
    have := Real.pi_pos
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (by norm_num)))
      (pow_ne_zero _ (by positivity))) (by positivity)
  · have := ((hasDerivAt_id x).const_mul (2 * π)).sin
    simpa [mul_comm] using this
  · have : (a : ℝ) < b := by exact_mod_cast hab
    simp only; linarith
  · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
    have hx' : x = n / 2 := by have := Real.pi_pos; field_simp at hn ⊢; nlinarith
    have : (0 : ℝ) < n := by rw [hx'] at hx; linarith
    have : (0 : ℤ) < n := by exact_mod_cast this
    lift n to ℕ using this.le
    exact ⟨n, by omega, by rw [hx']; push_cast; ring⟩
  · show Real.sin (2 * π * ((i : ℝ) / 2)) = 0
    rw [Real.sin_eq_zero_iff]; exact ⟨i, by push_cast; ring⟩
  · have hs : Real.sin (2 * π * ((i : ℝ) / 2)) = 0 := by
      rw [Real.sin_eq_zero_iff]; exact ⟨i, by push_cast; ring⟩
    have := Real.pi_pos
    exact mul_ne_zero (by positivity) (r24b_cos_ne_of_sin hs)
  · have := bernoulliFun_eval_half_eq_zero k
    rwa [bernoulliFun, ← one_div] at this
  · intro M ε hε
    filter_upwards [r24b_real_of_unif (fun K hK => tendstoUniformlyOn_bernoulli_odd hK) 1 _
        (fun x => Real.sin (2 * π * x)) hcplx (fun x => by push_cast; ring) M ε hε,
      r24b_real_of_unif (fun K hK => tendstoUniformlyOn_bernoulli_even hK)
        _ _ (fun x => (2 * π) * Real.cos (2 * π * x)) hcplx'
        (fun x => by push_cast; ring) M ε hε] with k h1 h2 x hx1 hxM
    exact ⟨h1 x hx1 hxM, h2 x hx1 hxM⟩

/-- `y_j^{(2k)} → j` as `k → ∞` (the zeros of `sin πx`). -/
theorem r24b_euler_even_zero {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun k => eulerRealZero (2 * k) j) atTop (𝓝 (j : ℝ)) := by
  have hcplx : ∀ (k : ℕ) (x : ℝ), ((((-1) ^ k * π ^ (2 * k + 1) / (4 * (2 * k)!) *
      ((Polynomial.euler (2 * k)).map (algebraMap ℚ ℝ)).eval x : ℝ)) : ℂ) =
      1 * ((-1 : ℂ) ^ k * (π : ℂ) ^ (2 * k + 1) / (4 * (2 * k)!) * eulerPolyE (2 * k) x) := by
    intro k x
    rw [eulerPolyE, ← r24b_eval_map_cplx]; push_cast; ring
  have hcplx' : ∀ (m : ℕ) (x : ℝ), ((((-1) ^ (m + 1) * π ^ (2 * (m + 1) + 1) /
      (4 * (2 * (m + 1))!) *
      ((Polynomial.euler (2 * (m + 1))).map (algebraMap ℚ ℝ)).derivative.eval x : ℝ)) : ℂ) =
      ((π : ℝ) : ℂ) * ((-1 : ℂ) ^ (m + 1) * (π : ℂ) ^ (2 * m + 2) / (4 * (2 * m + 1)!) *
        eulerPolyE (2 * m + 1) x) := by
    intro m x
    rw [derivative_map, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, derivative_euler_succ,
      eulerPolyE, ← r24b_eval_map_cplx, Nat.factorial_succ]
    simp only [Polynomial.map_mul, eval_mul, Polynomial.map_add, Polynomial.map_natCast,
      Polynomial.map_one, eval_add, eval_natCast, eval_one]
    have hf : ((2 * m + 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hm : (2 * (m : ℂ) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * m + 1)
    push_cast
    field_simp
    ring
  refine r24b_tendsto_zerosGE (fun k => (Polynomial.euler (2 * k)).map (algebraMap ℚ ℝ))
    (fun k => (-1) ^ k * π ^ (2 * k + 1) / (4 * (2 * k)!)) (fun k => ?_)
    (fun x => Real.sin (π * x)) (fun x => π * Real.cos (π * x)) (fun x => ?_)
    (by fun_prop) (fun i => (i : ℝ)) (fun a b hab => ?_) (by norm_num)
    (fun x hx h => ?_) (fun i _ => ?_) (fun i _ => ?_) (fun h => ?_) ?_ hj
  · have := Nat.factorial_pos (2 * k)
    have := Real.pi_pos
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by positivity))) (by positivity)
  · have := ((hasDerivAt_id x).const_mul π).sin
    simpa [mul_comm] using this
  · show (a : ℝ) < b; exact_mod_cast hab
  · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
    have hx' : x = n := by have := Real.pi_pos; nlinarith
    have : (0 : ℝ) < n := by rw [hx'] at hx; linarith
    have : (0 : ℤ) < n := by exact_mod_cast this
    lift n to ℕ using this.le
    exact ⟨n, by omega, by rw [hx']; push_cast; ring⟩
  · show Real.sin (π * (i : ℝ)) = 0
    rw [Real.sin_eq_zero_iff]; exact ⟨i, by push_cast; ring⟩
  · have hs : Real.sin (π * (i : ℝ)) = 0 := by
      rw [Real.sin_eq_zero_iff]; exact ⟨i, by push_cast; ring⟩
    have := Real.pi_pos
    exact mul_ne_zero (by positivity) (r24b_cos_ne_of_sin hs)
  · norm_num at h
  · intro M ε hε
    filter_upwards [r24b_real_of_unif (fun K hK => tendstoUniformlyOn_euler_even hK) 1 _
        (fun x => Real.sin (π * x)) hcplx (fun x => by push_cast; ring) M ε hε,
      r24b_eventually_shift (r24b_real_of_unif (fun K hK => tendstoUniformlyOn_euler_odd hK)
        _ _ (fun x => π * Real.cos (π * x)) hcplx'
        (fun x => by push_cast; ring) M ε hε)] with k h1 h2 x hx1 hxM
    obtain ⟨hk1, h2⟩ := h2
    refine ⟨h1 x hx1 hxM, ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact h2 x hx1 hxM

/-- Corrected form of DLMF 24.12.11: `y_j^{(2k+1)} → j - 1/2` as `k → ∞` (the zeros of
`cos πx`); in particular `y_{2m}^{(n)} → 2m - 1/2` for odd `n`, not `m - 1/2` as printed. -/
theorem r24b_euler_odd_zero {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun k => eulerRealZero (2 * k + 1) j) atTop (𝓝 ((j : ℝ) - 1 / 2)) := by
  have hcplx : ∀ (k : ℕ) (x : ℝ), ((((-1) ^ (k + 1) * π ^ (2 * k + 2) / (4 * (2 * k + 1)!) *
      ((Polynomial.euler (2 * k + 1)).map (algebraMap ℚ ℝ)).eval x : ℝ)) : ℂ) =
      1 * ((-1 : ℂ) ^ (k + 1) * (π : ℂ) ^ (2 * k + 2) / (4 * (2 * k + 1)!) *
        eulerPolyE (2 * k + 1) x) := by
    intro k x
    rw [eulerPolyE, ← r24b_eval_map_cplx]; push_cast; ring
  have hcplx' : ∀ (k : ℕ) (x : ℝ), ((((-1) ^ (k + 1) * π ^ (2 * k + 2) / (4 * (2 * k + 1)!) *
      ((Polynomial.euler (2 * k + 1)).map (algebraMap ℚ ℝ)).derivative.eval x : ℝ)) : ℂ) =
      ((-π : ℝ) : ℂ) * ((-1 : ℂ) ^ k * (π : ℂ) ^ (2 * k + 1) / (4 * (2 * k)!) *
        eulerPolyE (2 * k) x) := by
    intro k x
    rw [derivative_map, derivative_euler_succ, eulerPolyE, ← r24b_eval_map_cplx,
      Nat.factorial_succ]
    simp only [Polynomial.map_mul, eval_mul, Polynomial.map_add, Polynomial.map_natCast,
      Polynomial.map_one, eval_add, eval_natCast, eval_one]
    have hf : ((2 * k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hm : (2 * (k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * k)
    push_cast
    field_simp
    ring
  refine r24b_tendsto_zerosGE (fun k => (Polynomial.euler (2 * k + 1)).map (algebraMap ℚ ℝ))
    (fun k => (-1) ^ (k + 1) * π ^ (2 * k + 2) / (4 * (2 * k + 1)!)) (fun k => ?_)
    (fun x => Real.cos (π * x)) (fun x => -π * Real.sin (π * x)) (fun x => ?_)
    (by fun_prop) (fun i => (i : ℝ) - 1 / 2) (fun a b hab => ?_) (by norm_num)
    (fun x hx h => ?_) (fun i hi => ?_) (fun i hi => ?_) (fun _ k => ?_) ?_ hj
  · have := Nat.factorial_pos (2 * k + 1)
    have := Real.pi_pos
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by positivity))) (by positivity)
  · have := ((hasDerivAt_id x).const_mul π).cos
    simpa [mul_comm] using this
  · have : (a : ℝ) < b := by exact_mod_cast hab
    simp only; linarith
  · obtain ⟨l, hl⟩ := Real.cos_eq_zero_iff.mp h
    have hx' : x = l + 1 / 2 := by
      have := Real.pi_pos; field_simp at hl ⊢; nlinarith
    have : (-1 : ℝ) < l := by rw [hx'] at hx; linarith
    have : (0 : ℤ) ≤ l := by
      have : (-1 : ℤ) < l := by exact_mod_cast this
      omega
    lift l to ℕ using this
    exact ⟨l + 1, by omega, by rw [hx']; push_cast; ring⟩
  · have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
    show Real.cos (π * ((i : ℝ) - 1 / 2)) = 0
    rw [Real.cos_eq_zero_iff]
    obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by omega⟩
    exact ⟨l, by push_cast; ring⟩
  · have hc : Real.cos (π * ((i : ℝ) - 1 / 2)) = 0 := by
      rw [Real.cos_eq_zero_iff]
      obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by omega⟩
      exact ⟨l, by push_cast; ring⟩
    have hs := Real.sin_sq_add_cos_sq (π * ((i : ℝ) - 1 / 2))
    rw [hc] at hs
    have := Real.pi_pos
    intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · rw [h] at hs; norm_num at hs
  · exact q24b_eulerFun_odd_half k
  · intro M ε hε
    filter_upwards [r24b_real_of_unif (fun K hK => tendstoUniformlyOn_euler_odd hK) 1 _
        (fun x => Real.cos (π * x)) hcplx (fun x => by push_cast; ring) M ε hε,
      r24b_real_of_unif (fun K hK => tendstoUniformlyOn_euler_even hK)
        _ _ (fun x => -π * Real.sin (π * x)) hcplx'
        (fun x => by push_cast; ring) M ε hε] with k h1 h2 x hx1 hxM
    exact ⟨h1 x hx1 hxM, h2 x hx1 hxM⟩

/-- DLMF 24.12.4: for fixed `m ≥ 1`, `x_{2m-1}^{(n)} → m - 1/4` and `x_{2m}^{(n)} → m + 1/4` as
`n → ∞` through even values. -/
@[dlmf 24.12.E4]
theorem tendsto_bernoulliRealZero_even {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun k : ℕ => bernoulliRealZero (2 * k) (2 * m - 1)) atTop (𝓝 (m - 1 / 4)) ∧
      Tendsto (fun k : ℕ => bernoulliRealZero (2 * k) (2 * m)) atTop (𝓝 (m + 1 / 4)) := by
  refine ⟨?_, ?_⟩
  · convert r24b_bernoulli_even_zero (j := 2 * m - 1) (by omega) using 2
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  · convert r24b_bernoulli_even_zero (j := 2 * m) (by omega) using 2
    push_cast; ring

/-- DLMF §24.12(i): for odd `n`, `x_1^{(n)} = 1/2`. -/
@[dlmf 24.12.i]
theorem bernoulliRealZero_one_of_odd {n : ℕ} (hn : Odd n) : bernoulliRealZero n 1 = 1 / 2 := by
  obtain ⟨k, rfl⟩ := hn
  refine b24b_getD_zero_eq (bernoulliRealZerosGE_sorted _) ?_ fun y hy => ?_
  · rw [mem_bernoulliRealZerosGE, one_div, bernoulliFun_eval_half_eq_zero]; norm_num
  · exact (mem_bernoulliRealZerosGE.mp hy).1

/-- DLMF §24.12(i): for odd `n ≥ 3`, `x_2^{(n)} = 1`. -/
@[dlmf 24.12.i]
theorem bernoulliRealZero_two_of_odd {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) :
    bernoulliRealZero n 2 = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have hk : 1 ≤ k := by omega
  set P := (Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℝ) with hP
  have hP0 : P ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr (b24b_bernoulli_ne_zero _)
  have hroot : P.IsRoot (1 / 2) := by
    show bernoulliFun _ _ = 0; rw [one_div]; exact bernoulliFun_eval_half_eq_zero _
  have hd : (derivative P).eval (1 / 2) ≠ 0 := by
    have : (derivative P).eval (1 / 2) = ((2 * k + 1 : ℕ) : ℝ) * bernoulliFun (2 * k) (1 / 2) := by
      simp [P, Polynomial.derivative_map, Polynomial.derivative_bernoulli, bernoulliFun]
    rw [this, one_div, bernoulliFun_eval_half]
    have hB := q24b_bernoulli_two_mul_ne_zero hk
    have h2 : (2 : ℝ) / 2 ^ (2 * k) - 1 ≠ 0 := by
      have : (4 : ℝ) ≤ 2 ^ (2 * k) := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (2 * k) := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [sub_ne_zero, ne_eq, div_eq_one_iff_eq (by positivity)]
      intro h; linarith
    exact mul_ne_zero (by positivity) (mul_ne_zero h2 (by exact_mod_cast hB))
  have hmult : P.rootMultiplicity (1 / 2) ≤ 1 := by
    by_contra h; push Not at h
    exact hd ((one_lt_rootMultiplicity_iff_isRoot hP0).mp h).2
  have hcount : (bernoulliRealZerosGE (2 * k + 1)).count (1 / 2) ≤ 1 := by
    rw [bernoulliRealZerosGE, b24b_zerosGE, ← Multiset.coe_count, Multiset.sort_eq,
      Multiset.count_filter_of_pos (by norm_num), count_roots]
    exact hmult
  have hz1 : bernoulliFun (2 * k + 1) 1 = 0 := by
    rw [bernoulliFun_endpoints_eq_of_ne_one (by omega), bernoulliFun_eval_zero,
      bernoulli_eq_zero_of_odd (odd_two_mul_add_one _) (by omega)]; simp
  have hzeros : ∀ x ∈ Set.Ioo (1 / 2 : ℝ) 1, bernoulliFun (2 * k + 1) x ≠ 0 := by
    intro x hx h
    apply q24b_bernoulli_odd_ne_zero k (x := 1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rw [bernoulliFun_eval_one_sub, h, mul_zero]
  refine q24b_getD_one_eq (bernoulliRealZerosGE_sorted _) ?_ ?_ (by norm_num) hcount ?_ ?_
  · exact mem_bernoulliRealZerosGE.mpr
      ⟨le_rfl, by rw [one_div]; exact bernoulliFun_eval_half_eq_zero _⟩
  · exact mem_bernoulliRealZerosGE.mpr ⟨by norm_num, hz1⟩
  · intro y hy; exact (mem_bernoulliRealZerosGE.mp hy).1
  · intro y hy hne
    obtain ⟨hy1, hy0⟩ := mem_bernoulliRealZerosGE.mp hy
    by_contra hlt; push Not at hlt
    exact hzeros y ⟨lt_of_le_of_ne hy1 (Ne.symm hne), hlt⟩ hy0

/-- DLMF 24.12.5: for fixed `m ≥ 1`, `x_{2m-1}^{(n)} → m - 1/2` and `x_{2m}^{(n)} → m` as
`n → ∞` through odd values. -/
@[dlmf 24.12.E5]
theorem tendsto_bernoulliRealZero_odd {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun k : ℕ => bernoulliRealZero (2 * k + 1) (2 * m - 1)) atTop (𝓝 (m - 1 / 2)) ∧
      Tendsto (fun k : ℕ => bernoulliRealZero (2 * k + 1) (2 * m)) atTop (𝓝 m) := by
  refine ⟨?_, ?_⟩
  · convert r24b_bernoulli_odd_zero (j := 2 * m - 1) (by omega) using 2
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  · convert r24b_bernoulli_odd_zero (j := 2 * m) (by omega) using 2
    push_cast; ring

/-- DLMF §24.12(i): `R(n) = n` for `1 ≤ n ≤ 5`. -/
@[dlmf 24.12.i]
theorem bernoulliRealZeroCount_eq_self {n : ℕ} (h1 : 1 ≤ n) (h5 : n ≤ 5) :
    bernoulliRealZeroCount n = n := by
  have hdeg : ((Polynomial.bernoulli n).map (algebraMap ℚ ℝ)).natDegree ≤ n := by
    refine natDegree_map_le.trans (natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_)
    rw [coeff_bernoulli]
    have : ¬ N ≤ n := by exact_mod_cast not_le.mpr hN
    simp [this]
  have hp : (Polynomial.bernoulli n).map (algebraMap ℚ ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr (b24b_bernoulli_ne_zero _)
  have hc : Continuous (bernoulliFun n) := continuous_bernoulliFun n
  have key : ∀ l : List ℝ, l.Pairwise (· < ·) → l.length = n → (∀ x ∈ l, bernoulliFun n x = 0) →
      bernoulliRealZeroCount n = n := fun l hl hlen hr =>
    q24b_roots_card_eq hdeg l hl hlen hr hp
  interval_cases n
  · refine key [1 / 2] (by simp) rfl ?_
    intro x hx; simp only [List.mem_singleton] at hx; subst hx
    simp [bernoulliFun, Polynomial.bernoulli_one]
  · obtain ⟨a, ha, ha0⟩ := q24b_exists_root hc (show (0 : ℝ) < 1 / 2 by norm_num)
      (by rw [q24b_B2, q24b_B2]; norm_num)
    obtain ⟨b, hb, hb0⟩ := q24b_exists_root hc (show (1 / 2 : ℝ) < 1 by norm_num)
      (by rw [q24b_B2, q24b_B2]; norm_num)
    refine key [a, b] (by simp; linarith [ha.2, hb.1]) rfl ?_
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption
  · refine key [0, 1 / 2, 1] (by simp; norm_num) rfl ?_
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> rw [q24b_B3] <;> norm_num
  · obtain ⟨a, ha, ha0⟩ := q24b_exists_root hc (show (-1 : ℝ) < 0 by norm_num)
      (by rw [q24b_B4, q24b_B4]; norm_num)
    obtain ⟨b, hb, hb0⟩ := q24b_exists_root hc (show (0 : ℝ) < 1 / 2 by norm_num)
      (by rw [q24b_B4, q24b_B4]; norm_num)
    obtain ⟨c, hc', hc0⟩ := q24b_exists_root hc (show (1 / 2 : ℝ) < 1 by norm_num)
      (by rw [q24b_B4, q24b_B4]; norm_num)
    obtain ⟨d, hd, hd0⟩ := q24b_exists_root hc (show (1 : ℝ) < 2 by norm_num)
      (by rw [q24b_B4, q24b_B4]; norm_num)
    refine key [a, b, c, d] ?_ rfl ?_
    · simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
        forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, forall_const, List.Pairwise.nil, and_true]
      constructorm* _ ∧ _ <;> linarith [ha.1, ha.2, hb.1, hb.2, hc'.1, hc'.2, hd.1, hd.2]
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
  · obtain ⟨a, ha, ha0⟩ := q24b_exists_root hc (show (-1 : ℝ) < -1 / 10 by norm_num)
      (by rw [q24b_B5, q24b_B5]; norm_num)
    obtain ⟨d, hd, hd0⟩ := q24b_exists_root hc (show (11 / 10 : ℝ) < 2 by norm_num)
      (by rw [q24b_B5, q24b_B5]; norm_num)
    refine key [a, 0, 1 / 2, 1, d] ?_ rfl ?_
    · simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
        forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, forall_const, List.Pairwise.nil, and_true]
      constructorm* _ ∧ _ <;> linarith [ha.1, ha.2, hd.1, hd.2]
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> first | assumption | (rw [q24b_B5]; norm_num)

/-- DLMF 24.12.6: `R(n) ∼ 2n/(πe)` as `n → ∞`. -/
@[dlmf 24.12.E6]
theorem bernoulliRealZeroCount_isEquivalent :
    (fun n : ℕ => (bernoulliRealZeroCount n : ℝ)) ~[atTop]
      fun n => 2 * n / (π * Real.exp 1) := by
  sorry

/-! ### §24.12(ii) Euler polynomials: real zeros -/

/-- DLMF §24.12(ii): for even `n ≥ 2`, `y_1^{(n)} = 1`. -/
@[dlmf 24.12.ii]
theorem eulerRealZero_one_of_even {n : ℕ} (he : Even n) (h2 : 2 ≤ n) :
    eulerRealZero n 1 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 2 := ⟨n / 2 - 1, by obtain ⟨k, hk⟩ := he; omega⟩
  refine b24b_getD_zero_eq (eulerRealZerosGE_sorted _) ?_ fun y hy => ?_
  · refine mem_eulerRealZerosGE.mpr ⟨by norm_num, ?_⟩
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, q24b_eulerFun_one,
      show 2 * m + 1 + 1 = 2 * m + 2 by ring, q24b_eulerFun_two_mul_add_two_zero, neg_zero]
  · obtain ⟨hy1, hy0⟩ := mem_eulerRealZerosGE.mp hy
    by_contra hlt
    push Not at hlt
    exact (q24b_euler_ne_zero m).2 y ⟨by linarith, hlt⟩ hy0

/-- DLMF 24.12.8: for fixed `m ≥ 1`, `y_m^{(n)} → m` as `n → ∞` through even values. -/
@[dlmf 24.12.E8]
theorem tendsto_eulerRealZero_even {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun k : ℕ => eulerRealZero (2 * k) m) atTop (𝓝 m) :=
  r24b_euler_even_zero hm

/-- DLMF §24.12(ii): for odd `n`, `y_1^{(n)} = 1/2`. -/
@[dlmf 24.12.ii]
theorem eulerRealZero_one_of_odd {n : ℕ} (hn : Odd n) : eulerRealZero n 1 = 1 / 2 := by
  refine b24b_getD_zero_eq (eulerRealZerosGE_sorted _) ?_ fun y hy => ?_
  · refine mem_eulerRealZerosGE.mpr ⟨le_rfl, ?_⟩
    have h := eulerNumber_eq_zero_of_odd hn
    rw [eulerNumber, mul_eq_zero] at h
    have h' : (euler n).eval (1 / 2 : ℚ) = 0 := h.resolve_left (pow_ne_zero _ two_ne_zero)
    have : (1 / 2 : ℝ) = algebraMap ℚ ℝ (1 / 2) := by simp
    rw [eulerFun, this, eval_map, eval₂_at_apply, h', map_zero]
  · exact (mem_eulerRealZerosGE.mp hy).1

/-! ### Helpers for 24.12.9 and 24.12.10: the second zero of `E₂ₘ₋₁`

From the Fourier series 24.8.5 and `|sin((2k+1)θ)| ≤ (2k+1) sin θ`,
`(-1)^m E₂ₘ₋₁(t) ≥ 4(2m-1)!/π^{2m} (1 - π²/24)(1 - 2t)` on `[0, 1/2]`; with
`E(1 + t) = 2tⁿ - E(t)` and `E(1 - x) = -E(x)` this locates the zero next to `3/2`. -/

/-- `E₅(x) = (x - 1/2)(x² - x - 1)²` (proof of `euler_five`). -/
theorem s24b_euler_five_eq :
    Polynomial.euler 5 = (X - C (1 / 2)) * (X ^ 2 - X - 1) ^ 2 := by
  apply eq_of_comp_X_add_one_add_self_eq
  rw [euler_comp_X_add_one_add]
  simp only [mul_comp, sub_comp, pow_comp, X_comp, C_comp, one_comp]
  have h : C (1 / 2 : ℚ) * 2 = 1 := by rw [← C_ofNat, ← C_mul]; norm_num
  linear_combination (-(X ^ 2 - X - 1) ^ 2 - ((X + 1) ^ 2 - (X + 1) - 1) ^ 2 +
    3 * (X ^ 4 - X ^ 2 + 1)) * h


/-- `|sin (m θ)| ≤ m |sin θ|`. -/
theorem s24b_abs_sin_nat_mul_le (m : ℕ) (θ : ℝ) :
    |Real.sin (m * θ)| ≤ m * |Real.sin θ| := by
  induction m with
  | zero => simp
  | succ m ih =>
    push_cast
    rw [add_mul, one_mul, Real.sin_add]
    calc |Real.sin (m * θ) * Real.cos θ + Real.cos (m * θ) * Real.sin θ|
        ≤ |Real.sin (m * θ)| * |Real.cos θ| + |Real.cos (m * θ)| * |Real.sin θ| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |Real.sin (m * θ)| * 1 + 1 * |Real.sin θ| := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
      _ ≤ (m + 1) * |Real.sin θ| := by nlinarith

/-- `cos((2k+1)πt) ≥ -(2k+1) cos(πt)`. -/
theorem s24b_cos_odd_ge (k : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    -((2 * k + 1) * Real.cos (π * t)) ≤ Real.cos ((2 * k + 1) * π * t) := by
  set θ := π / 2 - π * t
  have hθ0 : 0 ≤ θ := by simp only [θ]; nlinarith [Real.pi_pos]
  have hθ1 : θ ≤ π := by simp only [θ]; nlinarith [Real.pi_pos]
  have e1 : Real.cos (π * t) = Real.sin θ := by
    simp only [θ]; rw [Real.sin_pi_div_two_sub]
  have e2 : Real.cos ((2 * k + 1) * π * t) = (-1) ^ k * Real.sin (((2 * k + 1 : ℕ) : ℝ) * θ) := by
    rw [show (2 * k + 1) * π * t = (π / 2 - ((2 * k + 1 : ℕ) : ℝ) * θ) + k * π by
      simp only [θ]; push_cast; ring, Real.cos_add_nat_mul_pi, Real.cos_pi_div_two_sub]
  have hs := s24b_abs_sin_nat_mul_le (2 * k + 1) θ
  rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθ1)] at hs
  rw [e1, e2]
  have h1 : |(-1 : ℝ) ^ k * Real.sin (((2 * k + 1 : ℕ) : ℝ) * θ)| ≤
      ((2 * k + 1 : ℕ) : ℝ) * Real.sin θ := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]; exact hs
  push_cast at h1 ⊢
  linarith [neg_abs_le ((-1 : ℝ) ^ k * Real.sin ((2 * (k : ℝ) + 1) * θ))]

/-- Lower bound for `(-1)ⁿ E₂ₙ₋₁(t)` on `[0, 1/2]`, `n ≥ 2`. -/
theorem s24b_euler_lower {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    4 * (2 * n - 1)! / π ^ (2 * n) * (1 - π ^ 2 / 24) * (1 - 2 * t) ≤
      (-1) ^ n * eulerFun (2 * n - 1) t := by
  set K : ℝ := 4 * (2 * n - 1)! / π ^ (2 * n)
  have hK : 0 < K := by positivity
  have hπ := Real.pi_pos
  have hE := (hasSum_cos_odd_eulerFun (n := n) (by omega) ht0 (by linarith)).mul_left ((-1) ^ n)
  have h1 : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have hE' : HasSum (fun k : ℕ => K * (Real.cos ((2 * k + 1) * π * t) / (2 * k + 1) ^ (2 * n)))
      ((-1) ^ n * eulerFun (2 * n - 1) t) := by
    refine hE.congr_fun fun k => ?_
    rw [← mul_assoc, ← mul_assoc, h1, one_mul]
  have hc : 0 ≤ Real.cos (π * t) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
  have hz := ((hasSum_zeta_two.mul_left (-(1 / 4 : ℝ))).add (hasSum_ite_eq 0 (1 : ℝ))).mul_left
    (K * Real.cos (π * t))
  have hle := hasSum_le (fun k => ?_) hz hE'
  · have hcos := Real.one_sub_mul_le_cos (x := π * t) (by positivity) (by nlinarith)
    have e : 2 / π * (π * t) = 2 * t := by field_simp
    rw [e] at hcos
    have hp : (0 : ℝ) ≤ 1 - π ^ 2 / 24 := by nlinarith [Real.pi_lt_d2]
    calc K * (1 - π ^ 2 / 24) * (1 - 2 * t) ≤ K * (1 - π ^ 2 / 24) * Real.cos (π * t) := by
          gcongr
      _ = K * Real.cos (π * t) * (-(1 / 4) * (π ^ 2 / 6) + 1) := by ring
      _ ≤ _ := hle
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · simp only [ite_eq_right_iff.mpr (fun h => absurd h hk.ne'), add_zero]
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hco := s24b_cos_odd_ge k ht0 ht1
      have hpow : 4 * (k : ℝ) ^ 2 ≤ (2 * (k : ℝ) + 1) ^ (2 * n - 1) := by
        calc 4 * (k : ℝ) ^ 2 ≤ (2 * (k : ℝ) + 1) ^ 2 := by nlinarith
          _ ≤ (2 * (k : ℝ) + 1) ^ (2 * n - 1) := pow_le_pow_right₀ (by linarith) (by omega)
      have hq : (2 * (k : ℝ) + 1) ^ (2 * n) = (2 * k + 1) * (2 * k + 1) ^ (2 * n - 1) := by
        rw [← pow_succ', show 2 * n - 1 + 1 = 2 * n by omega]
      have hpos : (0 : ℝ) < (2 * k + 1) ^ (2 * n - 1) := by positivity
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hK.le
      rw [hq, le_div_iff₀ (by positivity)]
      calc Real.cos (π * t) * (-(1 / 4) * (1 / (k : ℝ) ^ 2)) *
            ((2 * k + 1) * (2 * k + 1) ^ (2 * n - 1)) =
            -((2 * k + 1) * Real.cos (π * t)) * ((2 * k + 1) ^ (2 * n - 1) / (4 * k ^ 2)) := by
            field_simp
        _ ≤ -((2 * k + 1) * Real.cos (π * t)) * 1 := by
            refine mul_le_mul_of_nonpos_left ?_ (by nlinarith)
            exact (one_le_div (by positivity)).mpr hpow
        _ ≤ _ := by linarith

/-- Bracketing the second entry of a sorted list whose least entry `a` is simple. -/
theorem s24b_second_bracket {l : List ℝ} {a lo hi z : ℝ} (hs : l.Pairwise (· ≤ ·)) (ha : a ∈ l)
    (hc : l.count a ≤ 1) (hge : ∀ y ∈ l, a ≤ y) (hgt : ∀ y ∈ l, y ≠ a → lo < y) (hz : z ∈ l)
    (hza : z ≠ a) (hzh : z < hi) : lo < l.getD (2 - 1) 0 ∧ l.getD (2 - 1) 0 < hi := by
  match l, hs, ha, hc, hge, hgt, hz with
  | [], _, ha, _, _, _, _ => simp at ha
  | [c], _, ha, _, _, _, hz =>
    simp only [List.mem_singleton] at ha hz; exact absurd (hz.trans ha.symm) hza
  | c :: d :: t, hs, ha, hc, hge, hgt, hz =>
    simp only [show 2 - 1 = 1 from rfl, List.getD_cons_succ, List.getD_cons_zero]
    have hca : c = a := by
      rcases List.mem_cons.mp ha with h | h
      · exact h.symm
      · exact le_antisymm ((List.pairwise_cons.mp hs).1 a h) (hge c List.mem_cons_self)
    subst hca
    have hdc : d ≠ c := by
      intro hdc; subst hdc
      simp at hc
    refine ⟨hgt d (by simp) hdc, lt_of_le_of_lt ?_ hzh⟩
    have hzt : z ∈ d :: t := by
      rcases List.mem_cons.mp hz with h | h
      · exact absurd h hza
      · exact h
    rcases List.mem_cons.mp hzt with h | h
    · exact h ▸ le_rfl
    · exact (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 z h

/-- `1/2` is a simple zero of `E₂ₙ₋₁`, `n ≥ 2`. -/
theorem s24b_euler_count_half {n : ℕ} (hn : 2 ≤ n) :
    (eulerRealZerosGE (2 * n - 1)).count (1 / 2) ≤ 1 := by
  set P := (Polynomial.euler (2 * n - 1)).map (algebraMap ℚ ℝ) with hP
  have hP0 : P ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr (b24b_euler_ne_zero _)
  have hd : (derivative P).eval (1 / 2) ≠ 0 := by
    have : (derivative P).eval (1 / 2) =
        ((2 * n - 1 : ℕ) : ℝ) * eulerFun (2 * (n - 2) + 2) (1 / 2) := by
      rw [show 2 * (n - 2) + 2 = 2 * n - 1 - 1 by omega]
      simp [P, Polynomial.derivative_map, derivative_euler, eulerFun]
    rw [this]
    refine mul_ne_zero (by norm_cast; omega) ((q24b_euler_ne_zero (n - 2)).2 _ ⟨by norm_num,
      by norm_num⟩)
  have hmult : P.rootMultiplicity (1 / 2) ≤ 1 := by
    by_contra h; push Not at h
    exact hd ((one_lt_rootMultiplicity_iff_isRoot hP0).mp h).2
  rw [eulerRealZerosGE, b24b_zerosGE, ← Multiset.coe_count, Multiset.sort_eq,
    Multiset.count_filter_of_pos (by norm_num), count_roots]
  exact hmult

/-- `η (-1)^m E₂ₘ₋₁(t) ≥ 0.77 (1 - 2t)` on `[0, 1/2]`, `η = π^{2m}/(3 (2m-1)!)`, `m ≥ 2`. -/
theorem s24b_euler_key {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    77 / 100 * (1 - 2 * t) ≤
      π ^ (2 * m) / (3 * (2 * m - 1)!) * ((-1) ^ m * eulerFun (2 * m - 1) t) := by
  have h := s24b_euler_lower hm ht0 ht1
  have hπ := Real.pi_pos
  have hη : 0 < π ^ (2 * m) / (3 * (2 * m - 1)!) := by positivity
  have hKη : π ^ (2 * m) / (3 * (2 * m - 1)!) * (4 * (2 * m - 1)! / π ^ (2 * m)) = 4 / 3 := by
    have : ((2 * m - 1)! : ℝ) ≠ 0 := by positivity
    field_simp
  have hp : π ^ 2 / 24 ≤ 4225 / 10000 := by nlinarith [Real.pi_lt_d2]
  have h2t : 0 ≤ 1 - 2 * t := by linarith
  calc 77 / 100 * (1 - 2 * t) ≤ 4 / 3 * (1 - π ^ 2 / 24) * (1 - 2 * t) := by
        gcongr; linarith
    _ = π ^ (2 * m) / (3 * (2 * m - 1)!) *
        (4 * (2 * m - 1)! / π ^ (2 * m) * (1 - π ^ 2 / 24) * (1 - 2 * t)) := by
        rw [← hKη]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h hη.le

/-- `π^{N+1}/N! ≤ 3/4` for `N ≥ 9`. -/
theorem s24b_pi_pow_div_le {N : ℕ} (hN : 9 ≤ N) : π ^ (N + 1) / N ! ≤ 3 / 4 := by
  induction N, hN using Nat.le_induction with
  | base =>
    have hp := Real.pi_lt_d2
    have hp0 := Real.pi_pos
    have : π ^ 10 < 3.15 ^ 10 := by gcongr
    rw [div_le_iff₀ (by positivity)]
    norm_num [Nat.factorial] at this ⊢
    linarith
  | succ N hN ih =>
    have hp := Real.pi_lt_d2
    have hp0 := Real.pi_pos
    rw [Nat.factorial_succ, pow_succ, Nat.cast_mul]
    have hN' : (π : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      have : (10 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 10 ≤ N + 1)
      linarith
    calc π ^ (N + 1) * π / (((N + 1 : ℕ) : ℝ) * N !) =
        π ^ (N + 1) / N ! * (π / ((N + 1 : ℕ) : ℝ)) := by
          field_simp
      _ ≤ 3 / 4 * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; exact hN'
      _ = 3 / 4 := by ring

/-- Common facts on `E₂ₘ₋₁` for the zero bounds. -/
theorem s24b_euler_facts {m : ℕ} (hm : 2 ≤ m) :
    (∀ x, eulerFun (2 * m - 1) (1 - x) = -eulerFun (2 * m - 1) x) ∧
    (∀ t, eulerFun (2 * m - 1) (1 + t) = 2 * t ^ (2 * m - 1) - eulerFun (2 * m - 1) t) ∧
    eulerFun (2 * m - 1) (1 / 2) = 0 ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → t ^ (2 * m - 1) ≤ t ^ 3) := by
  have hodd : Odd (2 * m - 1) := ⟨m - 1, by omega⟩
  refine ⟨fun x => ?_, fun t => ?_, ?_, fun t h0 h1 => ?_⟩
  · rw [eulerFun_one_sub, hodd.neg_one_pow, neg_one_mul]
  · have := eulerFun_add_one_add (2 * m - 1) t
    rw [add_comm t 1] at this; linarith
  · have := q24b_eulerFun_odd_half (m - 1)
    rwa [show 2 * (m - 1) + 1 = 2 * m - 1 by omega] at this
  · exact pow_le_pow_of_le_one h0 h1 (by omega)

/-- 24.12.10 for `n = 5`, where `y₂ = y₃ = (1 + √5)/2` is a double zero. -/
theorem s24b_euler_five_bounds :
    3 / 2 < eulerRealZero 5 2 ∧ eulerRealZero 5 2 < 3 / 2 + π ^ (5 + 1) / (3 * 5 !) := by
  have h5 : ∀ x, eulerFun 5 x = (x - 1 / 2) * (x ^ 2 - x - 1) ^ 2 := by
    intro x; simp [eulerFun, s24b_euler_five_eq]
  set gr : ℝ := (1 + Real.sqrt 5) / 2 with hgd
  have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 5 < 2.24 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hg2 : gr ^ 2 - gr - 1 = 0 := by rw [hgd]; nlinarith
  have hπ := Real.pi_gt_three
  have hη : 2 < π ^ (5 + 1) / (3 * 5 !) := by
    have : (3 : ℝ) ^ 6 < π ^ 6 := by gcongr
    rw [lt_div_iff₀ (by positivity)]
    norm_num [Nat.factorial] at this ⊢; linarith
  refine s24b_second_bracket (eulerRealZerosGE_sorted _) (a := 1 / 2) (z := gr) ?_
    (s24b_euler_count_half (n := 3) (by norm_num)) (fun y hy => (mem_eulerRealZerosGE.mp hy).1)
    (fun y hy hne => ?_) ?_ ?_ ?_
  · exact mem_eulerRealZerosGE.mpr ⟨le_rfl, by rw [h5]; ring⟩
  · obtain ⟨hy1, hy0⟩ := mem_eulerRealZerosGE.mp hy
    rw [h5] at hy0
    rcases mul_eq_zero.mp hy0 with h | h
    · exact absurd (by linarith : y = 1 / 2) hne
    · have h' : y ^ 2 - y - 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      nlinarith
  · exact mem_eulerRealZerosGE.mpr ⟨by rw [hgd]; linarith, by rw [h5, hg2]; ring⟩
  · intro h; rw [hgd] at h; linarith
  · rw [hgd]; linarith

/-- DLMF 24.12.9: for `n = 3, 7, 11, …`, `3/2 - π^{n+1}/(3 n!) < y_2^{(n)} < 3/2`. -/
@[dlmf 24.12.E9]
theorem eulerRealZero_two_bounds_three {n : ℕ} (hn : n % 4 = 3) :
    3 / 2 - π ^ (n + 1) / (3 * n !) < eulerRealZero n 2 ∧ eulerRealZero n 2 < 3 / 2 := by
  obtain ⟨m, rfl, hm2, hme⟩ : ∃ m, n = 2 * m - 1 ∧ 2 ≤ m ∧ Even m :=
    ⟨(n + 1) / 2, by omega, by omega, ⟨(n + 1) / 4, by omega⟩⟩
  rw [show 2 * m - 1 + 1 = 2 * m by omega]
  set η := π ^ (2 * m) / (3 * (2 * m - 1)!) with hηd
  have hη : 0 < η := by positivity
  obtain ⟨hsym, hshift, hhalf, hpow3⟩ := s24b_euler_facts hm2
  set E := eulerFun (2 * m - 1) with hE
  have key : ∀ t, 0 ≤ t → t ≤ 1 / 2 → 77 / 100 * (1 - 2 * t) ≤ η * E t := by
    intro t h0 h1
    have := s24b_euler_key hm2 h0 h1
    rwa [hme.neg_one_pow, one_mul] at this
  have hp : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → 2 * t ^ (2 * m - 1) ≤ 1 / 4 := by
    intro t h0 h1
    have := hpow3 t h0 (by linarith)
    have : t ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ h0 h1 3
    norm_num at this; linarith
  have hF2 : ∀ x, 1 / 2 < x → x ≤ 1 → E x < 0 := by
    intro x h1 h2
    have := key (1 - x) (by linarith) (by linarith)
    rw [hsym] at this
    nlinarith
  have hF3 : ∀ t, 0 ≤ t → t ≤ 1 / 2 - η → E (1 + t) < 0 := by
    intro t h0 h1
    have hk := key t h0 (by linarith)
    rw [hshift]
    have hpt := hp t h0 (by linarith)
    have h3 : 77 / 100 * (2 * η) ≤ η * E t := le_trans (by nlinarith) hk
    have h4 : 154 / 100 ≤ E t := by nlinarith
    linarith
  have h32 : 0 < E (3 / 2) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, hshift, hhalf, sub_zero]; positivity
  obtain ⟨a0, ha1, ha2, ha3, ha0⟩ : ∃ a0 : ℝ, 1 ≤ a0 ∧ 3 / 2 - η ≤ a0 ∧ a0 < 3 / 2 ∧ E a0 < 0 := by
    by_cases hη2 : η < 1 / 2
    · refine ⟨3 / 2 - η, by linarith, le_rfl, by linarith, ?_⟩
      have := hF3 (1 / 2 - η) (by linarith) le_rfl
      rwa [show 1 + (1 / 2 - η) = 3 / 2 - η by ring] at this
    · push Not at hη2
      refine ⟨1, le_rfl, by linarith, by norm_num, ?_⟩
      have hk := key 0 le_rfl (by norm_num)
      have : 0 < E 0 := by nlinarith
      have h1 := hshift 0
      rw [add_zero, zero_pow (by omega), mul_zero, zero_sub] at h1
      linarith
  obtain ⟨z, hz, hz0⟩ := q24b_exists_root (continuous_eulerFun _) ha3
    (mul_neg_of_neg_of_pos ha0 h32)
  refine s24b_second_bracket (eulerRealZerosGE_sorted _) (a := 1 / 2) (z := z)
    (mem_eulerRealZerosGE.mpr ⟨le_rfl, hhalf⟩) (s24b_euler_count_half hm2)
    (fun y hy => (mem_eulerRealZerosGE.mp hy).1) (fun y hy hne => ?_)
    (mem_eulerRealZerosGE.mpr ⟨by linarith [hz.1], hz0⟩) (by linarith [hz.1]) hz.2
  obtain ⟨hy1, hy0⟩ := mem_eulerRealZerosGE.mp hy
  by_contra hle
  push Not at hle
  rcases le_or_gt y 1 with h | h
  · exact absurd hy0 (hF2 y (lt_of_le_of_ne hy1 (Ne.symm hne)) h).ne
  · have := hF3 (y - 1) (by linarith) (by linarith)
    rw [show 1 + (y - 1) = y by ring] at this
    exact absurd hy0 this.ne

/-- DLMF 24.12.10: for `n = 5, 9, 13, …`, `3/2 < y_2^{(n)} < 3/2 + π^{n+1}/(3 n!)`. -/
@[dlmf 24.12.E10]
theorem eulerRealZero_two_bounds_one {n : ℕ} (hn : n % 4 = 1) (h5 : 5 ≤ n) :
    3 / 2 < eulerRealZero n 2 ∧ eulerRealZero n 2 < 3 / 2 + π ^ (n + 1) / (3 * n !) := by
  rcases (show n = 5 ∨ 9 ≤ n by omega) with rfl | h9
  · exact s24b_euler_five_bounds
  obtain ⟨m, rfl, hm5, hmo⟩ : ∃ m, n = 2 * m - 1 ∧ 5 ≤ m ∧ Odd m :=
    ⟨(n + 1) / 2, by omega, by omega, ⟨(n - 1) / 4, by omega⟩⟩
  have hm2 : 2 ≤ m := by omega
  have hη4 : π ^ (2 * m - 1 + 1) / (3 * (2 * m - 1)!) ≤ 1 / 4 := by
    have := s24b_pi_pow_div_le h9
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  rw [show 2 * m - 1 + 1 = 2 * m by omega] at hη4 ⊢
  set η := π ^ (2 * m) / (3 * (2 * m - 1)!) with hηd
  have hη : 0 < η := by positivity
  obtain ⟨hsym, hshift, hhalf, hpow3⟩ := s24b_euler_facts hm2
  set E := eulerFun (2 * m - 1) with hE
  have key : ∀ t, 0 ≤ t → t ≤ 1 / 2 → 77 / 100 * (1 - 2 * t) ≤ η * -E t := by
    intro t h0 h1
    have := s24b_euler_key hm2 h0 h1
    rwa [hmo.neg_one_pow, neg_one_mul] at this
  have hF2 : ∀ x, 1 / 2 < x → x ≤ 1 → 0 < E x := by
    intro x h1 h2
    have := key (1 - x) (by linarith) (by linarith)
    rw [hsym, neg_neg] at this
    nlinarith
  have hF3 : ∀ t, 0 < t → t ≤ 1 / 2 → 0 < E (1 + t) := by
    intro t h0 h1
    have hk := key t h0.le h1
    have : 0 ≤ -E t := by nlinarith
    rw [hshift]
    have : 0 < t ^ (2 * m - 1) := by positivity
    linarith
  have h32 : 0 < E (3 / 2) := by
    have := hF3 (1 / 2) (by norm_num) le_rfl
    rwa [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num] at this
  have hneg : E (3 / 2 + η) < 0 := by
    rw [show 3 / 2 + η = 1 + (1 / 2 + η) by ring, hshift]
    have hk := key (1 / 2 - η) (by linarith) (by linarith)
    have hs := hsym (1 / 2 + η)
    rw [show 1 - (1 / 2 + η) = 1 / 2 - η by ring] at hs
    rw [hs, neg_neg] at hk
    have h1 : 154 / 100 ≤ E (1 / 2 + η) := by nlinarith
    have h2 : (1 / 2 + η) ^ (2 * m - 1) ≤ (3 / 4) ^ 9 := by
      calc (1 / 2 + η) ^ (2 * m - 1) ≤ (3 / 4) ^ (2 * m - 1) :=
            pow_le_pow_left₀ (by linarith) (by linarith) _
        _ ≤ (3 / 4) ^ 9 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num at h2
    linarith
  obtain ⟨z, hz, hz0⟩ := q24b_exists_root (continuous_eulerFun _)
    (show (3 / 2 : ℝ) < 3 / 2 + η by linarith) (mul_neg_of_pos_of_neg h32 hneg)
  refine s24b_second_bracket (eulerRealZerosGE_sorted _) (a := 1 / 2) (z := z)
    (mem_eulerRealZerosGE.mpr ⟨le_rfl, hhalf⟩) (s24b_euler_count_half hm2)
    (fun y hy => (mem_eulerRealZerosGE.mp hy).1) (fun y hy hne => ?_)
    (mem_eulerRealZerosGE.mpr ⟨by linarith [hz.1], hz0⟩) (by linarith [hz.1]) hz.2
  obtain ⟨hy1, hy0⟩ := mem_eulerRealZerosGE.mp hy
  by_contra hle
  push Not at hle
  rcases le_or_gt y 1 with h | h
  · exact absurd hy0 (hF2 y (lt_of_le_of_ne hy1 (Ne.symm hne)) h).ne'
  · have := hF3 (y - 1) (by linarith) (by linarith)
    rw [show 1 + (y - 1) = y by ring] at this
    exact absurd hy0 this.ne'

/-- DLMF 24.12.11 as printed, `y_{2m}^{(n)} → m - 1/2` through odd `n`, is false: already for
`m = 1` the zero `y_2^{(n)}` tends to `3/2` (it lies within `π^{n+1}/(3 n!)` of `3/2` by
24.12.9–24.12.10). -/
theorem r24b_tendsto_eulerRealZero_odd_counterexample :
    ¬ Tendsto (fun k : ℕ => eulerRealZero (2 * k + 1) (2 * 1)) atTop (𝓝 ((1 : ℕ) - 1 / 2 : ℝ)) := by
  intro h
  have h2 := r24b_euler_odd_zero (j := 2 * 1) (by norm_num)
  have := tendsto_nhds_unique h h2
  norm_num at this

/-- DLMF 24.12.11, corrected: for fixed `m ≥ 1`, `y_m^{(n)} → m - 1/2` as `n → ∞` through odd
values.

Corrected statement (2026-10-25): DLMF prints `y_{2m}^{(n)} → m - 1/2`, which is false for every
`m ≥ 1` (see `r24b_tendsto_eulerRealZero_odd_counterexample`); the zeros of `Eₙ` in `[1/2, ∞)`
for odd `n` tend to `1/2, 3/2, 5/2, …`, the zeros of `cos πx`. -/
@[dlmf 24.12.E11]
theorem tendsto_eulerRealZero_odd {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun k : ℕ => eulerRealZero (2 * k + 1) m) atTop (𝓝 (m - 1 / 2)) :=
  r24b_euler_odd_zero hm

/-! ### §24.12(iv) Multiple zeros -/

/-- DLMF §24.12(iv): `Bₙ(x)` has no multiple zeros (Brillhart 1969). Stated for all `n ≥ 0`
(stronger than DLMF's `n = 1, 2, …`; `B₀ = 1`). -/
@[dlmf 24.12.iv]
theorem bernoulli_separable (n : ℕ) : (Polynomial.bernoulli n).Separable := by
  sorry

/-- DLMF §24.12(iv): `E₅(x) = (x - 1/2)(x² - x - 1)²`. -/
@[dlmf 24.12.iv]
theorem euler_five : Polynomial.euler 5 = (X - C (1 / 2)) * (X ^ 2 - X - 1) ^ 2 :=
  s24b_euler_five_eq

/-- DLMF §24.12(iv): the only Euler polynomial with multiple zeros is `E₅(x)`. -/
@[dlmf 24.12.iv]
theorem euler_separable_iff (n : ℕ) : (Polynomial.euler n).Separable ↔ n ≠ 5 := by
  sorry

end DLMF.BernoulliEuler
