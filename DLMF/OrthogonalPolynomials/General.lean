/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import TauCeti.Analysis.InnerProductSpace.PolynomialCompleteness

/-!
# General orthogonal polynomials (AAR Chapter 5)

Chebyshev `T` orthogonality and Chebyshev–Gauss quadrature are in Mathlib
(`Polynomial.Chebyshev.measureT`, `integral_eq_sumZeroes`). This file records the general
three-term recurrence, Favard's theorem, Gauss quadrature, zeros, the Christoffel–Darboux
kernel, and the missing orthogonality of Chebyshev `U`. Compact-support Parseval
uses the Tau Ceti contributors’ polynomial completeness and weighted Hilbert-basis
construction, followed by Mathlib’s Hilbert-basis Parseval identity.
-/

@[expose] public section

open Polynomial MeasureTheory intervalIntegral
open scoped Real ENNReal

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

/-- Favard's theorem (AAR §5.2): a three-term recurrence with positive off-diagonal
coefficients is orthogonal with respect to a positive measure. -/
@[dlmf 18.2.iv]
theorem favard {p : ℕ → ℝ[X]} {a b c : ℕ → ℝ}
    (hdeg : ∀ n, (p n).natDegree = n) (hzero : p 0 ≠ 0)
    (hbase : (X : ℝ[X]) * p 0 = C (a 0) * p 1 + C (b 0) * p 0)
    (hrec : ∀ n,
      (X : ℝ[X]) * p (n + 1) =
        C (a (n + 1)) * p (n + 2) + C (b (n + 1)) * p (n + 1) +
          C (c (n + 1)) * p n)
    (ha : ∀ n, 0 < a n) (hc : ∀ n, 0 < c (n + 1)) :
    ∃ μ : Measure ℝ, IsOrthogonalPolynomials μ p := by
  sorry

/-- Gauss quadrature (AAR §5.3): a polynomial of degree `< 2n` is integrated exactly by
the `n`-point formula whose nodes are the zeros of `p n`. -/
@[dlmf 18.2.x]
theorem gauss_quadrature {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials μ p) {n : ℕ} (hn : n ≠ 0)
    (x : Fin n → ℝ)
    (hroot : ∀ i, (p n).eval (x i) = 0)
    (hinj : Function.Injective x) :
    ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧
      ∀ q : ℝ[X], q.natDegree < 2 * n →
        ∫ t, q.eval t ∂μ = ∑ i, w i * q.eval (x i) := by
  classical
  let s : Finset (Fin n) := Finset.univ
  have hvs : Set.InjOn x (s : Set (Fin n)) := fun _ _ _ _ hxy => hinj hxy
  let ℓ : Fin n → ℝ[X] := fun i => Lagrange.basis s x i
  let w : Fin n → ℝ := fun i => ∫ t, (ℓ i).eval t ∂μ
  have hlc : (p n).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (h.ne_zero n)
  have hquad (q : ℝ[X]) (hq : q.natDegree < 2 * n) :
      ∫ t, q.eval t ∂μ = ∑ i, w i * q.eval (x i) := by
    let g : ℝ[X] := p n * C (p n).leadingCoeff⁻¹
    have hg : g.Monic := monic_mul_leadingCoeff_inv (h.ne_zero n)
    have hgn : g.natDegree = n := by
      rw [natDegree_mul (h.ne_zero n) (C_ne_zero.mpr (inv_ne_zero hlc)), natDegree_C,
        add_zero, h.1]
    have hgdeg : g.degree = n := by rw [degree_eq_natDegree hg.ne_zero, hgn]
    have hquotdeg : (C (p n).leadingCoeff⁻¹ * (q /ₘ g)).degree < n := by
      have hqd : (q /ₘ g).natDegree < n := by
        rw [natDegree_divByMonic q hg, hgn]
        omega
      rw [degree_C_mul (inv_ne_zero hlc)]
      exact (degree_le_natDegree).trans_lt (by exact_mod_cast hqd)
    have hrem :
        q %ₘ g = Lagrange.interpolate s x (fun j => q.eval (x j)) := by
      have hcard : (Finset.univ.image x).card = n := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      refine eq_of_degrees_lt_of_eval_finset_eq (s := Finset.univ.image x) ?_ ?_ ?_
      · rw [hcard]
        exact (degree_modByMonic_lt q hg).trans_eq hgdeg
      · rw [hcard]
        simpa [s, Finset.card_univ, Fintype.card_fin] using
          Lagrange.degree_interpolate_lt (r := fun j => q.eval (x j)) hvs
      · intro y hy
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
        have hevalg : g.eval (x i) = 0 := by simp [g, hroot i]
        have hsum := congrArg (fun r : ℝ[X] => r.eval (x i)) (modByMonic_add_div q g)
        have : (q %ₘ g).eval (x i) = q.eval (x i) := by
          simpa [eval_add, eval_mul, hevalg] using hsum
        rw [this, Lagrange.eval_interpolate_at_node _ hvs (Finset.mem_univ i)]
    let r : ℝ[X] := C (p n).leadingCoeff⁻¹ * (q /ₘ g)
    have hinterg : ∫ t, (p n * r).eval t ∂μ = 0 := by
      simp only [eval_mul]
      convert h.integral_mul_eq_zero_of_degree_lt (q := r) (k := n) hquotdeg using 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with t
      ring
    have hqsplit : q = p n * r + q %ₘ g := by
      rw [add_comm]
      simpa [g, r, mul_assoc] using (modByMonic_add_div q g).symm
    have hsumw : ∫ t, (q %ₘ g).eval t ∂μ = ∑ i, w i * q.eval (x i) := by
      rw [hrem]
      simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C, w, ℓ, s]
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [MeasureTheory.integral_const_mul]
        ring
      · intro i _
        convert h.integrable_mul (C (q.eval (x i))) (ℓ i) using 1
        simp [eval_C, ℓ, s]
    calc
      ∫ t, q.eval t ∂μ
          = ∫ t, (p n * r + q %ₘ g).eval t ∂μ :=
            congrArg (fun f : ℝ[X] => ∫ t, f.eval t ∂μ) hqsplit
      _ = ∫ t, (p n * r).eval t ∂μ + ∫ t, (q %ₘ g).eval t ∂μ := by
          simp only [eval_add]
          apply MeasureTheory.integral_add
          · convert h.integrable_mul r (p n) using 1
            simp [eval_mul, mul_comm]
          · convert h.integrable_mul (q %ₘ g) 1 using 1
            simp
      _ = ∑ i, w i * q.eval (x i) := by
          rw [hinterg, zero_add, hsumw]
  refine ⟨w, ?_, hquad⟩
  intro i
  have hℓ : ℓ i ≠ 0 := Lagrange.basis_ne_zero hvs (Finset.mem_univ i)
  have hℓnat : (ℓ i).natDegree = n - 1 := by
    simpa [s] using Lagrange.natDegree_basis hvs (Finset.mem_univ i)
  have hℓdeg : (ℓ i).degree < n := by
    rw [degree_eq_natDegree hℓ, hℓnat]
    exact_mod_cast Nat.sub_lt (Nat.pos_of_ne_zero hn) Nat.one_pos
  have hsqdeg : ((ℓ i) ^ 2).natDegree < 2 * n := by
    have : ((ℓ i) ^ 2).natDegree ≤ 2 * (ℓ i).natDegree := natDegree_pow_le
    omega
  have hsq := hquad ((ℓ i) ^ 2) hsqdeg
  have hnodes : ∑ j, w j * ((ℓ i) ^ 2).eval (x j) = w i := by
    rw [Finset.sum_eq_single i]
    · have hi := Lagrange.eval_basis_self (s := s) (v := x) hvs (Finset.mem_univ i)
      simp [ℓ, hi]
    · intro j _ hij
      have hz : (ℓ i).eval (x j) = 0 :=
        Lagrange.eval_basis_of_ne (s := s) (v := x) hij.symm (Finset.mem_univ j)
      simp [ℓ, hz]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  have hsqeval : ∫ t, ((ℓ i) ^ 2).eval t ∂μ = ∫ t, (ℓ i).eval t ^ 2 ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with t
    simp [pow_two]
  have hw : w i = ∫ t, (ℓ i).eval t ^ 2 ∂μ := by
    rw [← hsqeval, hsq, hnodes]
  rw [hw]
  exact h.integral_eval_sq_pos hℓ hℓdeg

/-- A real polynomial whose real roots all have even multiplicity does not change sign. -/
theorem eval_nonneg_or_nonpos {p : ℝ[X]} (hp : p ≠ 0)
    (heven : ∀ x, Even (p.rootMultiplicity x)) :
    (∀ x, 0 ≤ p.eval x) ∨ (∀ x, p.eval x ≤ 0) := by
  have go : ∀ d, ∀ (p : ℝ[X]), p.natDegree = d → p ≠ 0 →
      (∀ x, Even (p.rootMultiplicity x)) →
      (∀ x, 0 ≤ p.eval x) ∨ (∀ x, p.eval x ≤ 0) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro p hn hp heven
      subst hn
      by_cases hroots : p.roots = 0
      · by_cases hpos : ∃ x, 0 < p.eval x
        · by_cases hneg : ∃ x, p.eval x < 0
          · obtain ⟨x, hx⟩ := hpos
            obtain ⟨y, hy⟩ := hneg
            have hf : ContinuousOn (fun t : ℝ => p.eval t) (Set.uIcc x y) :=
              p.continuous.continuousOn
            have h0 : (0 : ℝ) ∈ Set.uIcc (p.eval x) (p.eval y) := by
              rw [Set.mem_uIcc]
              exact Or.inr ⟨hy.le, hx.le⟩
            obtain ⟨z, -, hz⟩ := (intermediate_value_uIcc hf) h0
            have hzroot : z ∈ p.roots := (mem_roots hp).2 (by simpa using hz)
            simp [hroots] at hzroot
          · left
            intro x
            exact le_of_not_gt fun hx => hneg ⟨x, hx⟩
        · right
          intro x
          exact le_of_not_gt fun hx => hpos ⟨x, hx⟩
      · obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hroots
        have hm : p.rootMultiplicity a ≠ 0 := by
          have hpos : 0 < Multiset.count a p.roots := Multiset.count_pos.mpr ha
          rw [count_roots] at hpos
          exact hpos.ne'
        obtain ⟨q, hpq, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp a
        have hq0 : q ≠ 0 := fun hq => hp (by rw [hpq, hq, mul_zero])
        have hdeg : q.natDegree < p.natDegree := by
          have hmon : ((X - C a) ^ p.rootMultiplicity a).Monic := (monic_X_sub_C a).pow _
          have hmul := natDegree_mul hmon.ne_zero hq0
          have hpow : (((X - C a) ^ p.rootMultiplicity a).natDegree) = p.rootMultiplicity a := by
            rw [natDegree_pow, natDegree_X_sub_C, mul_one]
          rw [hpq, hmul, hpow]
          omega
        have hqeven : ∀ x, Even (q.rootMultiplicity x) := by
          intro x
          have hpq0 : (X - C a) ^ p.rootMultiplicity a * q ≠ 0 :=
            mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero a)) hq0
          have hsum := rootMultiplicity_mul (x := x) hpq0
          rw [← hpq] at hsum
          by_cases hx : x = a
          · subst hx
            have : q.rootMultiplicity x = 0 :=
              rootMultiplicity_eq_zero (mt dvd_iff_isRoot.2 hndvd)
            rw [this]
            exact show Even (0 : ℕ) from ⟨0, by simp⟩
          · have hz : ((X - C a) ^ p.rootMultiplicity a).rootMultiplicity x = 0 := by
              apply rootMultiplicity_eq_zero
              intro hx'
              have : (x - a) ^ p.rootMultiplicity a = 0 := by
                simpa [eval_pow, eval_sub, eval_X, eval_C] using hx'
              exact hx (eq_of_sub_eq_zero ((pow_eq_zero_iff hm).mp this))
            have : p.rootMultiplicity x = q.rootMultiplicity x := by
              rw [hsum, hz, zero_add]
            rw [← this]
            exact heven x
        have ihq := ih q.natDegree hdeg q rfl hq0 hqeven
        have hpow (x : ℝ) : 0 ≤ (x - a) ^ p.rootMultiplicity a := by
          obtain ⟨k, hk⟩ := even_iff_two_dvd.mp (heven a)
          rw [hk, pow_mul]
          exact pow_nonneg (sq_nonneg _) _
        rcases ihq with hq | hq
        · left
          intro x
          have : p.eval x = (x - a) ^ p.rootMultiplicity a * q.eval x := by
            simpa [eval_mul, eval_pow, eval_sub, eval_X, eval_C] using congrArg (eval x) hpq
          rw [this]
          exact mul_nonneg (hpow x) (hq x)
        · right
          intro x
          have : p.eval x = (x - a) ^ p.rootMultiplicity a * q.eval x := by
            simpa [eval_mul, eval_pow, eval_sub, eval_X, eval_C] using congrArg (eval x) hpq
          rw [this]
          exact mul_nonpos_of_nonneg_of_nonpos (hpow x) (hq x)
  exact go p.natDegree p rfl hp heven

/-- Each point of `s` is a simple root of `∏_{a ∈ s} (X - a)`. -/
theorem rootMultiplicity_prod_X_sub_C {s : Finset ℝ} {x : ℝ} (hx : x ∈ s) :
    (∏ a ∈ s, (X - C a : ℝ[X])).rootMultiplicity x = 1 := by
  have hsplit :
      (∏ a ∈ s, (X - C a : ℝ[X])) =
        (X - C x) * ∏ a ∈ s.erase x, (X - C a) := by
    rw [← Finset.mul_prod_erase s (fun a => X - C a) hx]
  have hne : (∏ a ∈ s.erase x, (X - C a : ℝ[X])) ≠ 0 :=
    (monic_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)).ne_zero
  have hnd : ¬ IsRoot (∏ a ∈ s.erase x, (X - C a : ℝ[X])) x := by
    intro hx'
    have : (∏ a ∈ s.erase x, (x - a : ℝ)) = 0 := by
      simpa [eval_prod, eval_sub, eval_X, eval_C] using hx'
    obtain ⟨a, ha, ha0⟩ := Finset.prod_eq_zero_iff.mp this
    have : a ≠ x := (Finset.mem_erase.mp ha).1
    exact this (sub_eq_zero.mp ha0).symm
  have hmul := rootMultiplicity_mul (x := x)
    (mul_ne_zero (X_sub_C_ne_zero x) hne)
  rw [hsplit, hmul, rootMultiplicity_X_sub_C_self,
    rootMultiplicity_eq_zero hnd, add_zero]

/-- If `P = q r` where `q = ∏_{a ∈ s} (X - a)` runs over the roots of `P` of odd multiplicity,
then every root of `r` has even multiplicity. -/
private lemma even_rootMultiplicity_of_eq_mul {P q r : ℝ[X]} {s : Finset ℝ} (hP0 : P ≠ 0)
    (hs : s = P.roots.toFinset.filter (fun a => ¬ Even (P.rootMultiplicity a)))
    (hq : q = ∏ a ∈ s, (X - C a)) (hr : P = q * r) (x : ℝ) : Even (r.rootMultiplicity x) := by
  classical
  have hq0 : q ≠ 0 := hq ▸ (monic_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)).ne_zero
  have hr0 : r ≠ 0 := fun hr0 => hP0 (by rw [hr, hr0, mul_zero])
  have hsum := rootMultiplicity_mul (x := x) (mul_ne_zero hq0 hr0)
  rw [← hr] at hsum
  by_cases hx : x ∈ s
  · have hqx : q.rootMultiplicity x = 1 := hq ▸ rootMultiplicity_prod_X_sub_C hx
    have hodd : ¬ Even (P.rootMultiplicity x) := by
      have hx' := hx; rw [hs] at hx'; exact (Finset.mem_filter.mp hx').2
    have : P.rootMultiplicity x = 1 + r.rootMultiplicity x := by
      rw [hsum, hqx]
    cases Nat.even_or_odd (r.rootMultiplicity x) with
    | inl h => exact h
    | inr h =>
      have : Even (P.rootMultiplicity x) := by
        rw [this, add_comm]
        obtain ⟨k, hk⟩ := h
        exact ⟨k + 1, by omega⟩
      exact (hodd this).elim
  · have hqx : q.rootMultiplicity x = 0 := by
      apply rootMultiplicity_eq_zero
      intro hxroot
      have : (∏ a ∈ s, (x - a : ℝ)) = 0 := by
        simpa [hq, eval_prod, eval_sub, eval_X, eval_C] using (hxroot : q.eval x = 0)
      obtain ⟨a, ha, ha0⟩ := Finset.prod_eq_zero_iff.mp this
      have : a = x := sub_eq_zero.mp ha0 |>.symm
      exact hx (this ▸ ha)
    have hpeven : Even (P.rootMultiplicity x) := by
      by_cases hmem : x ∈ P.roots.toFinset
      · have : x ∈ s ↔ ¬ Even (P.rootMultiplicity x) := by
          simp [hs, Finset.mem_filter, hmem]
        simpa [this] using hx
      · have : P.rootMultiplicity x = 0 := by
          apply rootMultiplicity_eq_zero
          intro hxroot
          exact hmem (Multiset.mem_toFinset.2 ((mem_roots hP0).2 hxroot))
        rw [this]
        exact show Even (0 : ℕ) from ⟨0, by simp⟩
    have : r.rootMultiplicity x = P.rootMultiplicity x := by
      rw [hsum, hqx, zero_add]
    rwa [this]

/-- If `r` has constant sign and `∫ (q r) q dμ = 0`, then `q r = 0` `μ`-almost everywhere. -/
private lemma ae_eval_mul_eq_zero {μ : Measure ℝ} {q r : ℝ[X]}
    (hsign : (∀ t, 0 ≤ r.eval t) ∨ (∀ t, r.eval t ≤ 0))
    (hfi : Integrable (fun t => (q * r).eval t * q.eval t) μ)
    (hint : ∫ t, (q * r).eval t * q.eval t ∂μ = 0) :
    (fun t => (q * r).eval t) =ᵐ[μ] 0 := by
  have key (t : ℝ) (ht : (q * r).eval t * q.eval t = 0) : (q * r).eval t = 0 := by
    simp only [eval_mul, mul_eq_zero] at ht ⊢; tauto
  rcases hsign with hpos | hneg
  · have hnn : ∀ t, 0 ≤ (q * r).eval t * q.eval t := fun t => by
      simp only [eval_mul]; nlinarith [hpos t, sq_nonneg (q.eval t)]
    exact ((integral_eq_zero_iff_of_nonneg hnn hfi).mp hint).mono fun t ht => key t ht
  · have hnn : ∀ t, 0 ≤ -((q * r).eval t * q.eval t) := fun t => by
      simp only [eval_mul]; nlinarith [hneg t, sq_nonneg (q.eval t)]
    have hz := (integral_eq_zero_iff_of_nonneg hnn hfi.neg).mp
      (by rw [MeasureTheory.integral_neg, hint, neg_zero])
    exact hz.mono fun t ht => key t (neg_eq_zero.mp ht)

/-- The degree-`n` orthogonal polynomial has `n` distinct real zeros (AAR §5.4). -/
@[dlmf 18.2.vi]
theorem orthogonal_polynomials_roots {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials μ p) (n : ℕ) :
    (p n).roots.card = n ∧ (p n).roots.Nodup := by
  classical
  have hp0 := h.ne_zero n
  let s := (p n).roots.toFinset.filter (fun a => ¬ Even ((p n).rootMultiplicity a))
  let q : ℝ[X] := ∏ a ∈ s, (X - C a)
  have hq0 : q ≠ 0 := (monic_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)).ne_zero
  have hqdeg : q.natDegree = s.card := by
    have hmonic : ∀ a ∈ s, (X - C a : ℝ[X]).Monic := fun a _ => monic_X_sub_C a
    have hdeg := natDegree_prod_of_monic (s := s) (f := fun a : ℝ => (X - C a : ℝ[X])) hmonic
    simp only [natDegree_X_sub_C, Finset.sum_const, nsmul_one] at hdeg
    exact hdeg
  have hcard_le : (p n).roots.card ≤ n := by
    simpa [h.1 n] using card_roots' (p n)
  have hsle : s.card ≤ (p n).roots.card :=
    (Finset.card_filter_le _ _).trans (p n).roots.toFinset_card_le
  have hdiv : q ∣ p n := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a ha b hb hab
      exact isCoprime_X_sub_C_of_isUnit_sub
        (isUnit_iff_ne_zero.2 (sub_ne_zero.2 hab))
    · intro a ha
      have haroot : a ∈ (p n).roots :=
        Multiset.mem_toFinset.mp (Finset.mem_filter.mp ha).1
      exact dvd_iff_isRoot.2 ((mem_roots hp0).1 haroot)
  have hge : n ≤ s.card := by
    by_contra! hlt
    obtain ⟨r, hr⟩ := hdiv
    have hr0 : r ≠ 0 := fun hr0 => hp0 (by rw [hr, hr0, mul_zero])
    have hqd : q.degree < ((n : ℕ) : WithBot ℕ) := by
      rw [degree_eq_natDegree hq0, hqdeg]
      exact_mod_cast hlt
    have hinter := h.integral_mul_eq_zero_of_degree_lt (q := q) hqd
    have heven : ∀ x, Even (r.rootMultiplicity x) :=
      even_rootMultiplicity_of_eq_mul hp0 rfl rfl hr
    have hsign := eval_nonneg_or_nonpos hr0 heven
    have hp0ae : (fun t => (p n).eval t) =ᵐ[μ] 0 := by
      rw [hr]
      exact ae_eval_mul_eq_zero hsign (by rw [← hr]; exact h.integrable_mul (p n) q)
        (by rw [← hr]; simpa [mul_comm] using hinter)
    have hsq : ∫ t, (p n).eval t ^ 2 ∂μ = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hp0ae] with t ht
      simp [ht]
    exact (ne_of_gt (h.2.2.1 n)) hsq
  have hnn : (p n).roots.card = n := le_antisymm hcard_le (hsle.trans' hge)
  have hnodup : (p n).roots.Nodup := by
    have hfin : (p n).roots.toFinset.card = (p n).roots.card := by
      have hle1 : s.card ≤ (p n).roots.toFinset.card := Finset.card_filter_le _ _
      have hle2 : (p n).roots.toFinset.card ≤ (p n).roots.card :=
        Multiset.toFinset_card_le _
      omega
    exact (Multiset.toFinset_card_eq_card_iff_nodup).1 hfin
  exact ⟨hnn, hnodup⟩

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

/-- Parseval identity for the orthogonal expansion (AAR §5.7). -/
@[dlmf 18.2.viii]
theorem orthogonal_polynomials_parseval {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials μ p) {f : ℝ → ℝ}
    (hf : MemLp f 2 μ) {a b : ℝ}
    (hsupport : μ (Set.Icc a b)ᶜ = 0) :
    ∫ t, f t ^ 2 ∂μ =
      ∑' n : ℕ,
        (∫ t, f t * (p n).eval t ∂μ) ^ 2 / (∫ t, (p n).eval t ^ 2 ∂μ) := by
  classical
  have hfinite : IsFiniteMeasure μ := by
    have hi := h.integrable_mul (1 : ℝ[X]) 1
    exact (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
      (by simpa using hi)
  let := hfinite
  have hexp : ∃ r : ℝ, 0 < r ∧ Integrable (fun x : ℝ => Real.exp (r * |x|)) μ := by
    refine ⟨1, one_pos, ?_⟩
    have hi := (show Continuous (fun x : ℝ => Real.exp (1 * |x|)) by fun_prop).continuousOn.integrableOn_compact
      (μ := μ) (isCompact_Icc (a := a) (b := b))
    simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupport)] using hi
  let c : ℕ → ℝ := fun n => ∫ x, (p n).eval x ^ 2 ∂μ
  have hc : ∀ n, 0 < c n := h.2.2.1
  have hmem : ∀ n, MemLp (fun x => (algebraMap ℝ ℝ) ((p n).eval x / Real.sqrt (c n))) 2
      (μ.withDensity (fun _ => ENNReal.ofReal (1 : ℝ))) := by
    intro n
    simpa [div_eq_mul_inv] using (h.memLp_eval (p n)).mul_const (Real.sqrt (c n))⁻¹
  have hcomplete := TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot (𝕜 := ℝ)
    p (fun _ => 1) c (fun n => (degree_eq_natDegree (h.ne_zero n)).trans (by rw [h.1 n]))
    hc (by simpa using hexp) hmem
  have horth : ∀ m n, (∫ x, (p m).eval x * (p n).eval x * 1 ∂μ) =
      if m = n then c n else 0 := by
    intro m n
    by_cases hmn : m = n
    · subst m; simp [c, pow_two]
    · simpa [hmn] using h.2.2.2 m n hmn
  let B := TauCeti.hilbertBasisOfOrthogonalSystem (𝕜 := ℝ) (fun n x => (p n).eval x)
    (fun _ => 1) c (Filter.Eventually.of_forall fun _ => one_pos)
    aemeasurable_const hc horth hmem hcomplete
  have hB (n : ℕ) : ⇑(B n) =ᵐ[μ] fun x => (p n).eval x / Real.sqrt (c n) := by
    simpa [B] using TauCeti.coeFn_hilbertBasisOfOrthogonalSystem (𝕜 := ℝ)
      (fun n x => (p n).eval x) (fun _ => 1) c
      (Filter.Eventually.of_forall fun _ => one_pos) aemeasurable_const hc horth hmem hcomplete n
  have hinner (n : ℕ) : inner ℝ (hf.toLp f) (B n) =
      (∫ x, f x * (p n).eval x ∂μ) / Real.sqrt (c n) := by
    rw [L2.inner_def, ← MeasureTheory.integral_div]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hB n] with x hx hb
    simp [hx, hb, mul_div_assoc, mul_comm]
  have hnorm : inner ℝ (hf.toLp f) (hf.toLp f) = ∫ x, f x ^ 2 ∂μ := by
    rw [L2.inner_def]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp [hx, pow_two]
  rw [← hnorm, ← B.tsum_inner_mul_inner (hf.toLp f) (hf.toLp f)]
  apply tsum_congr
  intro n
  rw [show inner ℝ (B n) (hf.toLp f) = inner ℝ (hf.toLp f) (B n) from real_inner_comm _ _, hinner]
  dsimp [c]
  rw [← pow_two, div_pow, Real.sq_sqrt (hc n).le]

/-- Helper lemma for Chebyshev `U` orthogonality: the substitution `x = cos θ`. -/
theorem integral_mul_sqrt_one_sub_sq (g : ℝ → ℝ) :
    ∫ x : ℝ in (-1 : ℝ)..1, g x * Real.sqrt (1 - x ^ 2) =
      ∫ θ : ℝ in (0 : ℝ)..π, g (Real.cos θ) * Real.sin θ ^ 2 := by
  have hmeas :
      ∫ x, g x * (1 - x ^ 2) ∂Polynomial.Chebyshev.measureT =
        ∫ θ : ℝ in (0 : ℝ)..π, g (Real.cos θ) * (1 - Real.cos θ ^ 2) := by
    simpa using
      Polynomial.Chebyshev.integral_measureT_eq_integral_cos
        (f := fun x => g x * (1 - x ^ 2))
  have hrhs :
      ∫ θ : ℝ in (0 : ℝ)..π, g (Real.cos θ) * (1 - Real.cos θ ^ 2) =
        ∫ θ : ℝ in (0 : ℝ)..π, g (Real.cos θ) * Real.sin θ ^ 2 :=
    intervalIntegral.integral_congr fun θ _ => by rw [← Real.sin_sq_add_cos_sq θ]; ring
  rw [← hrhs, ← hmeas, Polynomial.Chebyshev.integral_measureT]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  have hxI : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
  have hnn : 0 ≤ 1 - x ^ 2 := by
    rw [sub_nonneg, sq_le_one_iff_abs_le_one]
    exact hxI
  have hsqrt : (1 - x ^ 2) * (Real.sqrt (1 - x ^ 2))⁻¹ = Real.sqrt (1 - x ^ 2) := by
    by_cases h0 : Real.sqrt (1 - x ^ 2) = 0
    · have : 1 - x ^ 2 = 0 := (Real.sqrt_eq_zero hnn).mp h0
      simp [this]
    · have hsq : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hnn
      calc
        (1 - x ^ 2) * (Real.sqrt (1 - x ^ 2))⁻¹
            = (Real.sqrt (1 - x ^ 2) ^ 2) * (Real.sqrt (1 - x ^ 2))⁻¹ := by rw [hsq]
          _ = Real.sqrt (1 - x ^ 2) := by field [h0]
  have hmul :
      g x * Real.sqrt (1 - x ^ 2) =
        g x * (1 - x ^ 2) * (Real.sqrt (1 - x ^ 2))⁻¹ := by
    conv_lhs => rw [← hsqrt]
    ring
  convert hmul using 2
  exact Real.sqrt_inv (1 - x ^ 2)

/-- Helper lemma for Chebyshev `U` orthogonality. -/
theorem integral_cos_mul {k : ℝ} (hk : k ≠ 0) (hs : Real.sin (k * π) = 0) :
    ∫ θ : ℝ in (0 : ℝ)..π, Real.cos (k * θ) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) hk]
  simp [integral_cos, hs, smul_eq_mul]

/-- Chebyshev `U` polynomials are orthogonal on `[-1,1]` with weight `√(1-x²)`
(Mathlib currently records this only for `T`). -/
@[dlmf 18.3.T1]
theorem integral_eval_U_mul_of_ne {n m : ℕ} (h : n ≠ m) :
    ∫ x : ℝ in (-1 : ℝ)..1,
        (Polynomial.Chebyshev.U ℝ n).eval x * (Polynomial.Chebyshev.U ℝ m).eval x *
          Real.sqrt (1 - x ^ 2) = 0 := by
  rw [integral_mul_sqrt_one_sub_sq
    (fun x => (Polynomial.Chebyshev.U ℝ n).eval x * (Polynomial.Chebyshev.U ℝ m).eval x)]
  have heq : ∀ θ : ℝ,
      (Polynomial.Chebyshev.U ℝ n).eval (Real.cos θ) *
          (Polynomial.Chebyshev.U ℝ m).eval (Real.cos θ) * Real.sin θ ^ 2 =
        Real.sin ((n + 1 : ℝ) * θ) * Real.sin ((m + 1 : ℝ) * θ) := by
    intro θ
    have h1 := Polynomial.Chebyshev.U_real_cos (θ := θ) (n := n)
    have h2 := Polynomial.Chebyshev.U_real_cos (θ := θ) (n := m)
    calc
      _ = ((Polynomial.Chebyshev.U ℝ n).eval (Real.cos θ) * Real.sin θ) *
            ((Polynomial.Chebyshev.U ℝ m).eval (Real.cos θ) * Real.sin θ) := by ring
      _ = Real.sin (((n : ℤ) + 1) * θ) * Real.sin (((m : ℤ) + 1) * θ) := by rw [h1, h2]
      _ = Real.sin ((n + 1 : ℝ) * θ) * Real.sin ((m + 1 : ℝ) * θ) := by
        push_cast
        rfl
  have htrig : ∀ θ : ℝ,
      Real.sin ((n + 1 : ℝ) * θ) * Real.sin ((m + 1 : ℝ) * θ) =
        (Real.cos (((n : ℝ) - m) * θ) - Real.cos (((n : ℝ) + m + 2) * θ)) / 2 := by
    intro θ
    have := Real.two_mul_sin_mul_sin ((n + 1 : ℝ) * θ) ((m + 1 : ℝ) * θ)
    have hAB : ((n + 1 : ℝ) * θ - (m + 1 : ℝ) * θ) = ((n : ℝ) - m) * θ := by ring
    have hABadd : ((n + 1 : ℝ) * θ + (m + 1 : ℝ) * θ) = ((n : ℝ) + m + 2) * θ := by ring
    rw [hAB, hABadd] at this
    linarith
  rw [intervalIntegral.integral_congr fun θ _ => (heq θ).trans (htrig θ)]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub]
  · have hnm : (n : ℝ) - m ≠ 0 := sub_ne_zero.mpr (Nat.cast_injective.ne h)
    have hsum : (n : ℝ) + m + 2 ≠ 0 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hsin1 : Real.sin (((n : ℝ) - m) * π) = 0 := by
      have := Real.sin_int_mul_pi ((n : ℤ) - m)
      convert this using 2
      simp
    have hsin2 : Real.sin (((n : ℝ) + m + 2) * π) = 0 := by
      have := Real.sin_int_mul_pi ((n : ℤ) + m + 2)
      convert this using 2
      simp
    rw [integral_cos_mul hnm hsin1, integral_cos_mul hsum hsin2]
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

@[dlmf 18.3.T1]
theorem integral_eval_U_mul_self {n : ℕ} :
    ∫ x : ℝ in (-1 : ℝ)..1,
        (Polynomial.Chebyshev.U ℝ n).eval x ^ 2 * Real.sqrt (1 - x ^ 2) = π / 2 := by
  rw [integral_mul_sqrt_one_sub_sq (fun x => (Polynomial.Chebyshev.U ℝ n).eval x ^ 2)]
  have heq : ∀ θ : ℝ,
      (Polynomial.Chebyshev.U ℝ n).eval (Real.cos θ) ^ 2 * Real.sin θ ^ 2 =
        Real.sin ((n + 1 : ℝ) * θ) ^ 2 := by
    intro θ
    have h1 := Polynomial.Chebyshev.U_real_cos (θ := θ) (n := n)
    have : ((Polynomial.Chebyshev.U ℝ n).eval (Real.cos θ) * Real.sin θ) ^ 2 =
        Real.sin (((n : ℤ) + 1) * θ) ^ 2 := by rw [h1]
    convert this using 1 <;> ring
  rw [intervalIntegral.integral_congr fun θ _ => heq θ]
  have hn1 : (n + 1 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  rw [intervalIntegral.integral_comp_mul_left (f := fun x => Real.sin x ^ 2) hn1, integral_sin_sq]
  simp [smul_eq_mul]
  have hsin : Real.sin ((n + 1 : ℝ) * π) = 0 := by
    simpa using Real.sin_nat_mul_pi (n + 1)
  rw [hsin]
  field [hn1]

end DLMF.OrthogonalPolynomials
