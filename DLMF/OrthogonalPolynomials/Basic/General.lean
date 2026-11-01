/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Orthogonal polynomials with respect to a measure

The definition of a sequence of polynomials orthogonal with respect to a Borel measure on `ℝ`
(DLMF §18.2(i)) and its basic API: the orthogonal polynomials form a basis, every polynomial is
square integrable, the three-term recurrence and the Christoffel–Darboux formula.

## Main definitions

* `IsOrthogonalPolynomials`: a sequence of real polynomials of exact degrees, orthogonal with
  respect to a Borel measure (DLMF 18.2.4–18.2.5).
* `IsOrthogonalPolynomials.basis`: the orthogonal polynomials as a basis of the polynomials.

## Main results

* `IsOrthogonalPolynomials.expansion`: the finite orthogonal expansion of a polynomial.
* `IsOrthogonalPolynomials.memLp_eval`,
  `IsOrthogonalPolynomials.integral_mul_eq_zero_of_degree_lt`: polynomials are square
  integrable, and `p k` is orthogonal to all polynomials of lower degree.
* `IsOrthogonalPolynomials.integral_eval_sq_pos`: positivity of the squared norm.
* `three_term_recurrence`: the three-term recurrence (DLMF 18.2.10).
* `christoffel_darboux`: the Christoffel–Darboux formula (DLMF 18.2.12).

## Implementation notes

Favard's theorem, Gauss quadrature, the zeros and Parseval's identity are in
`DLMF.OrthogonalPolynomials.General`; the kernels, moments and Hankel determinants are in
`DLMF.OrthogonalPolynomials.Basic.NormsAndKernels`.
-/

@[expose] public section

open Polynomial MeasureTheory

noncomputable section

namespace DLMF.OrthogonalPolynomials


/-- A sequence of real polynomials orthogonal with respect to a Borel measure. -/
@[dlmf 18.2.E4_5]
def IsOrthogonalPolynomials (μ : Measure ℝ) (p : ℕ → ℝ[X]) : Prop :=
  (∀ n, (p n).natDegree = n) ∧
    (∀ n, Integrable (fun x => (p n).eval x ^ 2) μ) ∧
    (∀ n, 0 < ∫ x, (p n).eval x ^ 2 ∂μ) ∧
    ∀ m n, m ≠ n → ∫ x, (p m).eval x * (p n).eval x ∂μ = 0

namespace IsOrthogonalPolynomials

variable {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p)

include h

/-- Orthogonal polynomials are nonzero. -/
theorem ne_zero (n : ℕ) : p n ≠ 0 := by
  intro hz
  have := h.2.2.1 n
  simp [hz] at this

/-- The polynomial basis supplied by the exact degrees and positive squared norms. -/
noncomputable def sequence : Polynomial.Sequence ℝ where
  elems' := p
  degree_eq' n := (degree_eq_natDegree (h.ne_zero n)).trans (by rw [h.1 n])

/-- An orthogonal polynomial of each degree forms a basis of the polynomial space. -/
noncomputable def basis : Module.Basis ℕ ℝ ℝ[X] :=
  h.sequence.basis (fun n => isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (h.ne_zero n)))

/-- The orthogonal-polynomial basis sends `n` to `p n`. -/
@[simp] theorem basis_apply (n : ℕ) : h.basis n = p n := by
  simp [basis, sequence]

/-- A polynomial of degree `< k` has zero `k`-th coordinate in the orthogonal basis. -/
theorem repr_eq_zero_of_degree_lt {q : ℝ[X]} {k : ℕ} (hq : q.degree < k) :
    h.basis.repr q k = 0 := by
  have hmem : q ∈ Submodule.span ℝ (h.basis '' Set.Iio k) := by
    have heq : h.basis '' Set.Iio k = h.sequence '' Set.Iio k := by
      congr 1
      funext i
      exact h.basis_apply i
    rw [heq, h.sequence.span_degreeLT (fun i _ =>
      isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (h.ne_zero i))), mem_degreeLT]
    exact hq
  have hs := h.basis.repr_support_subset_of_mem_span (Set.Iio k) hmem
  by_contra hn
  exact (lt_irrefl k) (hs (Finsupp.mem_support_iff.mpr hn))

/-- Expand a polynomial using only basis elements below a given degree bound. -/
theorem expansion {q : ℝ[X]} {N : ℕ} (hq : q.degree < N) :
    q = ∑ k ∈ Finset.range N, h.basis.repr q k • p k := by
  have hs : (h.basis.repr q).support ⊆ Finset.range N := by
    intro k hk
    rw [Finset.mem_range]
    by_contra hn
    exact Finsupp.mem_support_iff.mp hk
      (h.repr_eq_zero_of_degree_lt (hq.trans_le (by exact_mod_cast Nat.le_of_not_gt hn)))
  calc
    q = (h.basis.repr q).sum (fun i a => a • h.basis i) :=
      (h.basis.linearCombination_repr q).symm
    _ = ∑ i ∈ Finset.range N, h.basis.repr q i • p i := by
      simpa only [basis_apply] using
        (Finsupp.sum_of_support_subset (h.basis.repr q) hs
          (fun i a => a • h.basis i) (fun _ _ => zero_smul _ _))

/-- Every polynomial is square integrable, by its finite orthogonal expansion. -/
theorem memLp_eval (q : ℝ[X]) : MemLp (fun x => q.eval x) 2 μ := by
  have hq := h.expansion (q := q) (N := q.natDegree + 1)
    (degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_self q.natDegree))
  rw [hq]
  simp only [eval_finsetSum, smul_eq_C_mul, eval_mul, eval_C]
  apply memLp_finsetSum
  intro k _
  exact ((memLp_two_iff_integrable_sq (p k).continuous.aestronglyMeasurable).mpr
    (h.2.1 k)).const_mul (h.basis.repr q k)

/-- The product of two polynomials is `μ`-integrable. -/
theorem integrable_mul (q r : ℝ[X]) : Integrable (fun x => q.eval x * r.eval x) μ :=
  (h.memLp_eval q).integrable_mul (h.memLp_eval r)

/-- Orthogonal coordinates are computed by integrating against a basis polynomial. -/
theorem integral_mul (q : ℝ[X]) (k : ℕ) :
    ∫ x, q.eval x * (p k).eval x ∂μ =
      h.basis.repr q k * ∫ x, (p k).eval x ^ 2 ∂μ := by
  let N := max (q.natDegree + 1) (k + 1)
  have hq : q.degree < N := by
    apply degree_le_natDegree.trans_lt
    exact_mod_cast lt_of_lt_of_le (Nat.lt_succ_self q.natDegree)
      (le_max_left (q.natDegree + 1) (k + 1))
  have heval (x : ℝ) : q.eval x * (p k).eval x =
      ∑ i ∈ Finset.range N, h.basis.repr q i * ((p i).eval x * (p k).eval x) := by
    have he := congrArg (fun r : ℝ[X] => r.eval x) (h.expansion hq)
    rw [he]
    simp only [eval_finsetSum, smul_eq_C_mul, eval_mul, eval_C, Finset.sum_mul, mul_assoc]
  simp_rw [heval]
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [MeasureTheory.integral_const_mul]
    rw [Finset.sum_eq_single k]
    · congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      ring
    · intro i _ hik
      rw [h.2.2.2 i k hik, mul_zero]
    · intro hk
      exact False.elim (hk (Finset.mem_range.mpr
        (lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _))))
  · intro i _
    exact (h.integrable_mul (p i) (p k)).const_mul _

/-- `p k` is orthogonal to every polynomial of degree `< k`. -/
theorem integral_mul_eq_zero_of_degree_lt {q : ℝ[X]} {k : ℕ} (hq : q.degree < k) :
    ∫ x, q.eval x * (p k).eval x ∂μ = 0 := by
  rw [h.integral_mul, h.repr_eq_zero_of_degree_lt hq, zero_mul]

/-- `deg (X p_k) = k + 1`. -/
theorem degree_X_mul (k : ℕ) : (X * p k).degree = ((k + 1 : ℕ) : WithBot ℕ) := by
  rw [degree_mul, degree_X, degree_eq_natDegree (h.ne_zero k), h.1]
  norm_cast
  omega

/-- The top coefficient in multiplication by `X` is the ratio of leading coefficients. -/
theorem repr_X_mul_top (k : ℕ) :
    h.basis.repr (X * p k) (k + 1) = (p k).leadingCoeff / (p (k + 1)).leadingCoeff := by
  have he := congrArg (fun q : ℝ[X] => q.coeff (k + 1))
    (h.expansion (q := X * p k) (N := k + 2) (by
      rw [h.degree_X_mul]
      exact_mod_cast Nat.lt_succ_self (k + 1)))
  simp only [coeff_X_mul, finsetSum_coeff, coeff_smul, smul_eq_mul] at he
  rw [Finset.sum_range_succ] at he
  have hz : ∑ i ∈ Finset.range (k + 1),
      h.basis.repr (X * p k) i * (p i).coeff (k + 1) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [coeff_eq_zero_of_natDegree_lt (by rw [h.1]; exact Finset.mem_range.mp hi), mul_zero]
  have hcoeff (j : ℕ) : (p j).coeff j = (p j).leadingCoeff := by
    simpa only [h.1] using (p j).coeff_natDegree
  rw [hz, zero_add, hcoeff, hcoeff] at he
  apply (eq_div_iff (leadingCoeff_ne_zero.mpr (h.ne_zero (k + 1)))).mpr
  simpa only [h.1] using he.symm

/-- Symmetry of multiplication by `X` in orthogonal coordinates, with squared-norm weights. -/
theorem repr_X_mul_symm (i j : ℕ) :
    h.basis.repr (X * p i) j / (∫ x, (p i).eval x ^ 2 ∂μ) =
      h.basis.repr (X * p j) i / (∫ x, (p j).eval x ^ 2 ∂μ) := by
  have he : (∫ x, (X * p i).eval x * (p j).eval x ∂μ) =
      ∫ x, (X * p j).eval x * (p i).eval x ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    simp only [eval_mul, eval_X]
    ring
  rw [h.integral_mul, h.integral_mul] at he
  exact (div_eq_div_iff (ne_of_gt (h.2.2.1 i)) (ne_of_gt (h.2.2.1 j))).mpr he

/-- The squared L² norm of a polynomial is the sum of squared orthogonal coordinates. -/
theorem integral_eval_sq {q : ℝ[X]} {N : ℕ} (hq : q.degree < N) :
    ∫ x, q.eval x ^ 2 ∂μ =
      ∑ k ∈ Finset.range N, (h.basis.repr q k) ^ 2 * ∫ x, (p k).eval x ^ 2 ∂μ := by
  have heval (t : ℝ) : q.eval t ^ 2 =
      ∑ i ∈ Finset.range N, h.basis.repr q i * (q.eval t * (p i).eval t) := by
    have he := congrArg (fun r : ℝ[X] => r.eval t) (h.expansion hq)
    rw [pow_two, he]
    simp only [eval_finsetSum, smul_eq_C_mul, eval_mul, eval_C]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [heval]
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [MeasureTheory.integral_const_mul, h.integral_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · intro i _
    exact (h.integrable_mul q (p i)).const_mul _

/-- A nonzero polynomial of degree `< N` has positive squared norm. -/
theorem integral_eval_sq_pos {q : ℝ[X]} (hq : q ≠ 0) {N : ℕ} (hd : q.degree < N) :
    0 < ∫ x, q.eval x ^ 2 ∂μ := by
  rw [h.integral_eval_sq hd]
  have hsum := h.expansion hd
  have hex : ∃ k ∈ Finset.range N, h.basis.repr q k ≠ 0 := by
    by_contra! hz
    have : q = 0 := by
      rw [hsum]
      exact Finset.sum_eq_zero fun k hk => by rw [hz k hk, zero_smul]
    exact hq this
  obtain ⟨k, hk, hk0⟩ := hex
  refine Finset.sum_pos' (fun i _ => mul_nonneg (sq_nonneg _) (le_of_lt (h.2.2.1 i))) ?_
  refine ⟨k, hk, mul_pos (sq_pos_of_ne_zero hk0) (h.2.2.1 k)⟩

end IsOrthogonalPolynomials

/-- Three-term recurrence (AAR Theorem 5.2.2 and Remark 5.2.1, pp. 244–245).
Expand `X * p (n + 1)` in the polynomial basis; orthogonality kills the terms below `p n`. -/
@[dlmf 18.2.E10]
theorem three_term_recurrence {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials μ p) (n : ℕ) :
    ∃ a b c : ℝ,
      (X : ℝ[X]) * p (n + 1) =
        C a * p (n + 2) + C b * p (n + 1) + C c * p n := by
  let q : ℝ[X] := X * p (n + 1)
  have hq : q.degree < (n + 3 : ℕ) := by
    rw [h.degree_X_mul (n + 1)]
    exact_mod_cast Nat.lt_succ_self (n + 2)
  have hlow (k : ℕ) (hk : k < n) : h.basis.repr q k = 0 := by
    have hkdeg : (X * p k).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
      rw [h.degree_X_mul]
      exact_mod_cast (by omega : k + 1 < n + 1)
    have hz := h.integral_mul_eq_zero_of_degree_lt hkdeg
    have heq : (∫ x, (X * p k).eval x * (p (n + 1)).eval x ∂μ) =
        ∫ x, q.eval x * (p k).eval x ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      simp only [q, eval_mul, eval_X]
      ring
    rw [heq, h.integral_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt (h.2.2.1 k))
  refine ⟨h.basis.repr q (n + 2), h.basis.repr q (n + 1), h.basis.repr q n, ?_⟩
  change q = _
  conv_lhs => rw [h.expansion hq]
  simp only [Finset.sum_range_succ]
  have hz : ∑ k ∈ Finset.range n, h.basis.repr q k • p k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hlow k (Finset.mem_range.mp hk), zero_smul]
  rw [hz]
  simp only [smul_eq_C_mul]
  ring


/-- Christoffel–Darboux formula (AAR Theorem 5.2.4 and Remark 5.2.2, p. 246).
The cancellation in AAR's telescoping proof is implemented by symmetry of the weighted
multiplication coefficients: the interior double sum cancels, leaving its boundary term. -/
@[dlmf 18.2.E12]
theorem christoffel_darboux {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials μ p) {n : ℕ} (hn : n ≠ 0) {x y : ℝ} (hxy : x ≠ y) :
    ∑ k ∈ Finset.range n,
        (p k).eval x * (p k).eval y /
          (∫ t, (p k).eval t ^ 2 ∂μ) =
      ((p (n - 1)).leadingCoeff /
        ((p n).leadingCoeff * ∫ t, (p (n - 1)).eval t ^ 2 ∂μ)) *
        ((p n).eval x * (p (n - 1)).eval y -
          (p (n - 1)).eval x * (p n).eval y) / (x - y) := by
  let H (k : ℕ) : ℝ := ∫ t, (p k).eval t ^ 2 ∂μ
  let A (i j : ℕ) : ℝ := h.basis.repr (X * p i) j / H i
  let W (i j : ℕ) : ℝ := (p j).eval x * (p i).eval y - (p i).eval x * (p j).eval y
  have hterm (k : ℕ) (hk : k < n) :
      (x - y) * ((p k).eval x * (p k).eval y / H k) =
        ∑ j ∈ Finset.range (n + 1), A k j * W k j := by
    have hdeg : (X * p k).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
      rw [h.degree_X_mul]
      exact_mod_cast Nat.add_lt_add_right hk 1
    have he (t : ℝ) : t * (p k).eval t =
        ∑ j ∈ Finset.range (n + 1), h.basis.repr (X * p k) j * (p j).eval t := by
      simpa only [eval_mul, eval_X, eval_finsetSum, smul_eq_C_mul, eval_C] using
        congrArg (fun q : ℝ[X] => q.eval t) (h.expansion hdeg)
    calc
      _ = ((x * (p k).eval x) * (p k).eval y -
          (p k).eval x * (y * (p k).eval y)) / H k := by ring
      _ = _ := by
        rw [he x, he y]
        simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
          Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        dsimp [A, W]
        ring
  have hsym (i j : ℕ) : A i j = A j i := h.repr_X_mul_symm i j
  have hcancel : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, A i j * W i j = 0 := by
    have he : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, A i j * W i j) =
        -(∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, A i j * W i j) := by
      conv_lhs => rw [Finset.sum_comm]
      simp only [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsym j i]
      dsimp [W]
      ring
    linarith
  have hboundary : ∑ k ∈ Finset.range n, A k n * W k n = A (n - 1) n * W (n - 1) n := by
    apply Finset.sum_eq_single (n - 1)
    · intro k hk hkn
      have hkn' : k + 1 < n := by
        have := Finset.mem_range.mp hk
        omega
      have hz : h.basis.repr (X * p k) n = 0 :=
        h.repr_eq_zero_of_degree_lt (by rw [h.degree_X_mul]; exact_mod_cast hkn')
      simp [A, hz]
    · intro hk
      exact False.elim (hk (Finset.mem_range.mpr (by omega)))
  have hid : (x - y) * (∑ k ∈ Finset.range n, (p k).eval x * (p k).eval y / H k) =
      A (n - 1) n * W (n - 1) n := by
    rw [Finset.mul_sum]
    trans ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (n + 1), A k j * W k j
    · exact Finset.sum_congr rfl (fun k hk => hterm k (Finset.mem_range.mp hk))
    · simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
      rw [hcancel, zero_add, hboundary]
  have htop : A (n - 1) n = (p (n - 1)).leadingCoeff / ((p n).leadingCoeff * H (n - 1)) := by
    have he := h.repr_X_mul_top (n - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at he
    dsimp [A]
    rw [he, div_div]
  rw [htop] at hid
  apply (eq_div_iff (sub_ne_zero.mpr hxy)).mpr
  simpa only [H, W, mul_comm] using hid
end DLMF.OrthogonalPolynomials
