/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Differential
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Lagrange

/-!
# The discriminant of a Jacobi polynomial (AAR Theorem 8.5.3, DLMF 18.16.19)

The product of squared differences of the zeros of `P_n^{(α,β)}`, by Schur's resultant route.
`jacobiPolyP_prod_sq_sub` gives it for the monic normalization; AAR 8.5.3
(`DLMF.Selberg.jacobiPolyP_discriminant`) and DLMF 18.16.19
(`jacobi_discriminant` in `BoundsZeros.lean`) are restatements.
-/

@[expose] public section

open Complex
open scoped Real Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-! ### The discriminant of a Jacobi polynomial

We follow Schur's route (Szegő §6.71) rather than Stieltjes' electrostatics. Over `ℂ` every
Jacobi polynomial splits. For monic `f` and `g` the products of `g` over the zeros of `f` and of
`f` over the zeros of `g` agree up to sign (`lc_pow_mul_prod_roots_eval`), and the three-term
recurrence evaluates `P_{n+2}` at the zeros of `P_{n+1}`. This gives a recursion for
`SS n = ∏_{P_{n+1}(x) = 0} P_n(x)`. The lowering relation
`(1 - x²) P_{n+1}' = c P_n` at the zeros, together with the values at `±1`, expresses the
discriminant through `SS`, and an induction identifies the closed form. -/

namespace JacobiDisc

open Polynomial Finset

/-- Coefficients of the Jacobi polynomial in powers of `(x - 1)/2`. -/
def coef (a b : ℂ) (n k : ℕ) : ℂ :=
  poch (n + a + b + 1) k * poch (a + k + 1) (n - k) / ((k ! : ℂ) * (n - k)!)

/-- The Jacobi polynomial as an element of `ℂ[X]`. -/
def jacPoly (a b : ℂ) (n : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (coef a b n k) * (C (1 / 2 : ℂ) * (X - C 1)) ^ k

theorem eval_jacPoly {a : ℂ} (hα : -1 < a.re) (b : ℂ) (n : ℕ) (x : ℂ) :
    (jacPoly a b n).eval x = jacobiPolyP a b n x := by
  rw [jacobi_finite_sum hα]
  simp only [jacPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, coef]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem degree_C_mul_le' (c : ℂ) (p : ℂ[X]) : (C c * p).degree ≤ p.degree := by
  rw [← smul_eq_C_mul]
  exact degree_smul_le c p

theorem degree_term_le (c : ℂ) (k : ℕ) :
    (C c * (C (1 / 2 : ℂ) * (X - C 1)) ^ k).degree ≤ (k : WithBot ℕ) := by
  refine (degree_C_mul_le' _ _).trans ?_
  rw [degree_pow, degree_C_mul (by norm_num), degree_X_sub_C]
  simp

theorem jacPoly_eq (a b : ℂ) (n : ℕ) :
    jacPoly a b n = (∑ k ∈ Finset.range n, C (coef a b n k) * (C (1 / 2 : ℂ) * (X - C 1)) ^ k) +
      C (coef a b n n * (1 / 2) ^ n) * (X - C 1) ^ n := by
  rw [jacPoly, Finset.sum_range_succ, mul_pow, ← C_pow, ← mul_assoc, ← C_mul]

theorem lower_degree_lt (a b : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range n, C (coef a b n k) * (C (1 / 2 : ℂ) * (X - C 1)) ^ k).degree <
      (n : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  exact (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 fun k hk =>
    lt_of_le_of_lt (degree_term_le _ k) (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hk))

theorem degree_top (c : ℂ) (hc : c ≠ 0) (n : ℕ) :
    (C c * (X - C (1 : ℂ)) ^ n).degree = (n : WithBot ℕ) := by
  rw [degree_C_mul hc, degree_pow, degree_X_sub_C]
  simp

theorem jacPoly_natDegree_lc (a b : ℂ) (n : ℕ) (hc : coef a b n n ≠ 0) :
    (jacPoly a b n).natDegree = n ∧
      (jacPoly a b n).leadingCoeff = coef a b n n * (1 / 2) ^ n := by
  have hc' : coef a b n n * (1 / 2 : ℂ) ^ n ≠ 0 := mul_ne_zero hc (by norm_num)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [jacPoly]
  rw [jacPoly_eq]
  have hlt : (∑ k ∈ Finset.range n, C (coef a b n k) * (C (1 / 2 : ℂ) * (X - C 1)) ^ k).degree <
      (C (coef a b n n * (1 / 2) ^ n) * (X - C (1 : ℂ)) ^ n).degree := by
    rw [degree_top _ hc']
    exact lower_degree_lt a b n
  refine ⟨?_, ?_⟩
  · rw [natDegree_add_eq_right_of_degree_lt hlt]
    exact natDegree_eq_of_degree_eq_some (degree_top _ hc' n)
  · rw [leadingCoeff_add_of_degree_lt hlt, leadingCoeff_mul, leadingCoeff_C,
      leadingCoeff_pow, leadingCoeff_X_sub_C, one_pow, mul_one]



theorem eval_eq_lc_mul_prod_roots (p : ℂ[X]) (x : ℂ) :
    p.eval x = p.leadingCoeff * (p.roots.map fun r => x - r).prod := by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := p))]
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
  simp

theorem prod_map_const_mul {s : Multiset ℂ} (c : ℂ) (f : ℂ → ℂ) :
    (s.map fun x => c * f x).prod = c ^ Multiset.card s * (s.map f).prod := by
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]

/-- Swapping the two polynomials in a resultant-type product over roots. -/
theorem lc_pow_mul_prod_roots_eval (p q : ℂ[X]) :
    p.leadingCoeff ^ q.natDegree * (p.roots.map fun x => q.eval x).prod =
      (-1) ^ (p.natDegree * q.natDegree) * q.leadingCoeff ^ p.natDegree *
        (q.roots.map fun y => p.eval y).prod := by
  have hp := IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := p)
  have hq := IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := q)
  simp_rw [eval_eq_lc_mul_prod_roots q, eval_eq_lc_mul_prod_roots p, prod_map_const_mul, hp, hq]
  have key : (q.roots.map fun y => (p.roots.map fun x => y - x).prod).prod =
      (-1) ^ (p.natDegree * q.natDegree) *
        (p.roots.map fun x => (q.roots.map fun y => x - y).prod).prod := by
    have h1 : ∀ y, (p.roots.map fun x => y - x).prod =
        (-1) ^ p.natDegree * (p.roots.map fun x => x - y).prod := by
      intro y
      rw [← hp, ← prod_map_const_mul]
      congr 1
      exact Multiset.map_congr rfl fun x _ => by ring
    simp_rw [h1, prod_map_const_mul, hq, ← pow_mul]
    rw [Multiset.prod_map_prod_map]
  rw [key]
  have hs : ((-1 : ℂ) ^ (p.natDegree * q.natDegree)) * (-1) ^ (p.natDegree * q.natDegree) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  linear_combination (-(p.leadingCoeff ^ q.natDegree * q.leadingCoeff ^ p.natDegree *
    (p.roots.map fun x => (q.roots.map fun y => x - y).prod).prod)) * hs



theorem prod_range_prod_range_ite_lt (c : ℂ) (N : ℕ) :
    ∏ i ∈ range N, ∏ j ∈ range N, (if i < j then c else 1) = c ^ N.choose 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [prod_range_succ]
    have h1 : ∀ i ∈ range N, ∏ j ∈ range (N + 1), (if i < j then c else 1) =
        (∏ j ∈ range N, (if i < j then c else 1)) * c := by
      intro i hi
      rw [prod_range_succ]
      simp [mem_range.mp hi]
    have h2 : ∏ j ∈ range (N + 1), (if N < j then c else (1 : ℂ)) = 1 := by
      refine prod_eq_one fun j hj => ?_
      have : ¬ N < j := by have := mem_range.mp hj; omega
      simp [this]
    rw [prod_congr rfl h1, prod_mul_distrib, ih, h2, prod_const, card_range,
      Nat.choose_succ_succ', Nat.choose_one_right, mul_one, ← pow_add, add_comm]

/-- Products over ordered pairs of distinct indices, against squares over `i < j`. -/
theorem prod_prod_erase_sub {N : ℕ} (v : Fin N → ℂ) :
    ∏ i, ∏ j ∈ univ.erase i, (v i - v j) =
      (-1) ^ N.choose 2 * ∏ i, ∏ j, (if i.val < j.val then (v i - v j) ^ 2 else 1) := by
  have hsplit : ∀ i, ∏ j ∈ univ.erase i, (v i - v j) =
      (∏ j, (if i.val < j.val then v i - v j else 1)) *
        ∏ j, (if j.val < i.val then v i - v j else 1) := by
    intro i
    rw [← prod_mul_distrib, ← prod_erase_mul _ _ (mem_univ i)]
    simp only [lt_irrefl, ite_false, mul_one]
    refine prod_congr rfl fun j hj => ?_
    have hne : j ≠ i := ne_of_mem_erase hj
    have hne' : j.val ≠ i.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with h | h
    · simp [h, not_lt.mpr h.le]
    · simp [h, not_lt.mpr h.le]
  rw [prod_congr rfl fun i _ => hsplit i, prod_mul_distrib]
  rw [prod_comm (s := univ) (t := univ) (f := fun i j => if j.val < i.val then v i - v j else 1)]
  rw [← prod_mul_distrib]
  simp_rw [← prod_mul_distrib]
  have hterm : ∀ i j : Fin N, (if i.val < j.val then v i - v j else 1) *
      (if i.val < j.val then v j - v i else 1) =
      (if i.val < j.val then (-1 : ℂ) else 1) * (if i.val < j.val then (v i - v j) ^ 2 else 1) := by
    intro i j
    split_ifs <;> ring
  simp_rw [hterm, prod_mul_distrib]
  congr 1
  have := prod_range_prod_range_ite_lt (-1) N
  rw [← this, ← Fin.prod_univ_eq_prod_range]
  refine prod_congr rfl fun i _ => ?_
  rw [← Fin.prod_univ_eq_prod_range (fun j => if (i : ℕ) < j then (-1 : ℂ) else 1)]


/-- The algebraic induction step for the closed form of the discriminant. -/
theorem disc_step_algebra (n : ℕ) {K K2 S0 S1 u1 v1 c1 u2 v2 c2 d e n2 pa1 pb1 f1 σ1 : ℂ}
    (hK : K ≠ 0) (hd : d ≠ 0) (hc2 : c2 ≠ 0) (hn2 : n2 ≠ 0) (he : e ≠ 0) (hc1 : c1 ≠ 0)
    (hu1 : u1 ≠ 0) (hv1 : v1 ≠ 0) (hu2 : u2 ≠ 0) (hv2 : v2 ≠ 0) (hpa : pa1 ≠ 0)
    (hpb : pb1 ≠ 0) (hf : f1 ≠ 0)
    (hK2 : K2 = K * (d * c2 / (2 * n2 * e)))
    (hS : K2 ^ (n + 1) * S1 =
      K ^ (n + 2) * ((-1) ^ (n + 1) * (u1 * v1 * c2 / (n2 * e * c1)) ^ (n + 1)) * S0) :
    (σ1 * (-1) ^ (n + 1)) * (2 * u2 * v2) ^ (n + 2) * S1 * (f1 * n2) ^ 2 * K2 ^ 2 /
        (c2 ^ (n + 2) * (pa1 * u2) * (pb1 * v2) * K2 ^ (n + 2)) =
      σ1 * (2 * u1 * v1) ^ (n + 1) * S0 * f1 ^ 2 * K ^ 2 /
        (c1 ^ (n + 1) * pa1 * pb1 * K ^ (n + 1)) *
      (2 ^ (2 * n + 2) * n2 ^ (n + 2) * u2 ^ (n + 1) * v2 ^ (n + 1) * e ^ n /
        (d ^ (2 * n + 1) * c2 ^ (2 * n + 2))) := by
  have hK2' : K2 ≠ 0 := by
    rw [hK2]; exact mul_ne_zero hK (div_ne_zero (mul_ne_zero hd hc2) (by simp [hn2, he]))
  have hS1 : S1 = K ^ (n + 2) * ((-1) ^ (n + 1) * (u1 * v1 * c2 / (n2 * e * c1)) ^ (n + 1)) *
      S0 / K2 ^ (n + 1) := by
    rw [← hS]; field_simp
  subst hS1
  subst hK2
  have hss : ((-1 : ℂ) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  generalize (-1 : ℂ) ^ (n + 1) = s at hss ⊢
  simp only [div_pow, mul_pow]
  field_simp
  rw [show s ^ 2 = 1 by rw [sq, hss]]
  ring

section Jacobi

variable {α β : ℝ}

theorem ne_zero_of_re_pos {z : ℂ} (h : 0 < z.re) : z ≠ 0 := fun h0 => by simp [h0] at h

/-- The leading coefficient of `P_n^{(α,β)}`. -/
def kk (a b : ℂ) (n : ℕ) : ℂ := coef a b n n * (1 / 2) ^ n

theorem coef_diag (a b : ℂ) (n : ℕ) : coef a b n n = poch (n + a + b + 1) n / n ! := by
  simp [coef, poch_zero]

theorem kk_ne_zero (hα : -1 < α) (hβ : -1 < β) (n : ℕ) : kk α β n ≠ 0 := by
  refine mul_ne_zero ?_ (by norm_num)
  rw [coef_diag]
  refine div_ne_zero ?_ (by exact_mod_cast n.factorial_ne_zero)
  rcases n with _ | n
  · simp [poch_zero]
  refine poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos ?_) _
  simp only [add_re, natCast_re, ofReal_re, one_re]
  push_cast
  linarith

theorem coef_diag_ne_zero (hα : -1 < α) (hβ : -1 < β) (n : ℕ) : coef α β n n ≠ 0 :=
  left_ne_zero_of_mul (kk_ne_zero hα hβ n)

theorem natDegree_jacPoly (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    (jacPoly α β n).natDegree = n :=
  (jacPoly_natDegree_lc α β n (coef_diag_ne_zero hα hβ n)).1

theorem leadingCoeff_jacPoly (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    (jacPoly α β n).leadingCoeff = kk α β n :=
  (jacPoly_natDegree_lc α β n (coef_diag_ne_zero hα hβ n)).2

theorem jacPoly_ne_zero (hα : -1 < α) (hβ : -1 < β) (n : ℕ) : jacPoly α β n ≠ 0 := by
  intro h
  have := leadingCoeff_jacPoly hα hβ n
  rw [h, leadingCoeff_zero] at this
  exact kk_ne_zero hα hβ n this.symm

theorem kk_succ (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    kk α β (n + 2) = kk α β (n + 1) *
      ((2 * n + α + β + 3) * (2 * ((n + 1 : ℕ) : ℂ) + α + β + 2) /
        (2 * ((n + 1 + 1 : ℕ) : ℂ) * (n + α + β + 2))) := by
  set x : ℂ := (n : ℂ) + α + β + 2 with hxdef
  have hx : x ≠ 0 := ne_zero_of_re_pos (by simp [x]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hp : poch (x + 1) (n + 2) * x = poch x (n + 1) * (x + (n + 1)) * (x + (n + 2)) := by
    have h1 := poch_add x 1 (n + 2)
    have h2 : poch x (n + 3) = poch x (n + 1) * (x + (n + 1)) * (x + (n + 2)) := by
      rw [show n + 3 = n + 1 + 1 + 1 by ring, poch_succ, poch_succ]
      push_cast; ring
    rw [show 1 + (n + 2) = n + 3 by ring, poch_one] at h1
    rw [← h2, h1, Nat.cast_one, mul_comm]
  have e1 : ((n + 1 : ℕ) : ℂ) + α + β + 1 = x := by push_cast; ring
  have e2 : ((n + 2 : ℕ) : ℂ) + α + β + 1 = x + 1 := by push_cast; ring
  simp only [kk, coef_diag, e1, e2]
  have hf : (((n + 2)! : ℕ) : ℂ) = ((n + 1)! : ℕ) * ((n + 1 + 1 : ℕ) : ℂ) := by
    rw [Nat.factorial_succ (n + 1)]; push_cast; ring
  rw [hf]
  have hpe : poch (x + 1) (n + 2) = poch x (n + 1) * (x + (n + 1)) * (x + (n + 2)) / x := by
    rw [← hp]; field_simp
  rw [hpe]
  have hn2 : ((n + 1 + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
  have hf1 : (((n + 1)! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n + 1)
  rw [hxdef]
  field_simp
  push_cast
  ring

/-- The constant in the three-term recurrence at a zero of `P_{n+1}`. -/
def recA (a b : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) + a + 1) * ((n : ℂ) + b + 1) * (2 * ((n + 1 : ℕ) : ℂ) + a + b + 2) /
    (((n + 1 + 1 : ℕ) : ℂ) * ((n : ℂ) + a + b + 2) * (2 * (n : ℂ) + a + b + 2))

theorem eval_jacPoly_two_of_root (hα : -1 < α) (hβ : -1 < β) (n : ℕ) {y : ℂ}
    (hy : (jacPoly α β (n + 1)).eval y = 0) :
    (jacPoly α β (n + 2)).eval y = -recA α β n * (jacPoly α β n).eval y := by
  have hα' : -1 < (α : ℂ).re := by simpa using hα
  have hrec := jacobi_recurrence (β := (β : ℂ)) hα' n y
  simp only [eval_jacPoly hα'] at hy ⊢
  rw [hy] at hrec
  have h1 : ((n : ℂ) + 2) ≠ 0 := ne_zero_of_re_pos (by simp; positivity)
  have h2 : ((n : ℂ) + α + β + 2) ≠ 0 :=
    ne_zero_of_re_pos (by simp; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have h3 : (2 * (n : ℂ) + α + β + 2) ≠ 0 :=
    ne_zero_of_re_pos (by simp; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hK : (2 * ((n : ℂ) + 2) * ((n : ℂ) + α + β + 2) * (2 * (n : ℂ) + α + β + 2)) ≠ 0 := by
    simp [h1, h2, h3]
  have hP : jacobiPolyP (α : ℂ) β (n + 2) y = -(2 * ((n : ℂ) + α + 1) * ((n : ℂ) + β + 1) *
      (2 * (n : ℂ) + α + β + 4)) * jacobiPolyP (α : ℂ) β n y /
        (2 * ((n : ℂ) + 2) * ((n : ℂ) + α + β + 2) * (2 * (n : ℂ) + α + β + 2)) := by
    rw [eq_div_iff hK]
    linear_combination hrec
  rw [hP]
  unfold recA
  have h1' : ((n : ℂ) + 1 + 1) ≠ 0 := by rw [add_assoc]; norm_num; exact h1
  push_cast
  field_simp
  ring

/-- The product of `P_n` over the zeros of `P_{n+1}`. -/
def SS (a b : ℂ) (n : ℕ) : ℂ :=
  ((jacPoly a b (n + 1)).roots.map fun x => (jacPoly a b n).eval x).prod

theorem SS_zero (a b : ℂ) : SS a b 0 = 1 := by
  have : ∀ x, (jacPoly a b 0).eval x = 1 := by
    intro x; simp [jacPoly, coef, poch_zero]
  simp [SS, this]

theorem SS_succ (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    kk α β (n + 2) ^ (n + 1) * SS α β (n + 1) =
      kk α β (n + 1) ^ (n + 2) * ((-1) ^ (n + 1) * recA α β n ^ (n + 1)) * SS α β n := by
  have h := lc_pow_mul_prod_roots_eval (jacPoly α β (n + 2)) (jacPoly α β (n + 1))
  rw [natDegree_jacPoly hα hβ, natDegree_jacPoly hα hβ, leadingCoeff_jacPoly hα hβ,
    leadingCoeff_jacPoly hα hβ] at h
  have hroots : ((jacPoly α β (n + 1)).roots.map fun y => (jacPoly α β (n + 2)).eval y) =
      (jacPoly α β (n + 1)).roots.map fun y => -recA α β n * (jacPoly α β n).eval y := by
    refine Multiset.map_congr rfl fun y hy => ?_
    exact eval_jacPoly_two_of_root hα hβ n
      ((mem_roots (jacPoly_ne_zero hα hβ _)).mp hy).eq_zero
  rw [hroots, prod_map_const_mul, IsAlgClosed.card_roots_eq_natDegree,
    natDegree_jacPoly hα hβ] at h
  have hev : Even ((n + 2) * (n + 1)) := by
    have := Nat.even_mul_succ_self (n + 1); rwa [mul_comm] at this
  rw [hev.neg_one_pow, one_mul] at h
  unfold SS
  rw [h, neg_pow]
  ring

end Jacobi
section ClosedForm

variable {α β : ℝ}

/-- The closed form of the Jacobi discriminant, indexed as in AAR Theorem 8.5.3. -/
def Fr (a b : ℂ) (N : ℕ) : ℂ :=
  (2 : ℂ) ^ (N * (N - 1)) * ∏ j ∈ range N,
    ((j : ℂ) + 1) ^ (j + 1) * ((j : ℂ) + 1 + a) ^ j * ((j : ℂ) + 1 + b) ^ j /
      ((N : ℂ) + j + 1 + a + b) ^ (N + j - 1)

/-- The ratio of consecutive closed forms. -/
def ratioR (a b : ℂ) (n : ℕ) : ℂ :=
  2 ^ (2 * n + 2) * ((n + 1 + 1 : ℕ) : ℂ) ^ (n + 2) * (((n + 1 : ℕ) : ℂ) + a + 1) ^ (n + 1) *
    (((n + 1 : ℕ) : ℂ) + b + 1) ^ (n + 1) * ((n : ℂ) + a + b + 2) ^ n /
    ((2 * (n : ℂ) + a + b + 3) ^ (2 * n + 1) * (2 * ((n + 1 : ℕ) : ℂ) + a + b + 2) ^ (2 * n + 2))

theorem Fr_succ (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    Fr α β (n + 2) = Fr α β (n + 1) * ratioR α β n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set g : ℕ → ℂ := fun i => ((n : ℂ) + i + 2 + α + β) ^ (n + i) with hg
  have hgne : ∀ i, g i ≠ 0 := fun i =>
    pow_ne_zero _ (ne_zero_of_re_pos (by simp; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]))
  have hden1 : ∏ j ∈ range (n + 1), (((n + 1 : ℕ) : ℂ) + j + 1 + α + β) ^ (n + 1 + j - 1) =
      ∏ i ∈ range (n + 1), g i := by
    refine prod_congr rfl fun j _ => ?_
    simp only [hg]
    rw [show n + 1 + j - 1 = n + j by omega]
    push_cast; ring_nf
  have hden2 : ∏ j ∈ range (n + 2), (((n + 2 : ℕ) : ℂ) + j + 1 + α + β) ^ (n + 2 + j - 1) =
      ∏ j ∈ range (n + 2), g (j + 1) := by
    refine prod_congr rfl fun j _ => ?_
    simp only [hg]
    rw [show n + 2 + j - 1 = n + (j + 1) by omega]
    push_cast; ring_nf
  have hsplit : (∏ j ∈ range (n + 2), g (j + 1)) * g 0 =
      (∏ i ∈ range (n + 1), g i) * g (n + 1) * g (n + 2) := by
    rw [← prod_range_succ' g (n + 2), prod_range_succ, prod_range_succ]
  have hg0 : g 0 = ((n : ℂ) + α + β + 2) ^ n := by simp only [hg]; push_cast; ring_nf
  have hg1 : g (n + 1) = (2 * (n : ℂ) + α + β + 3) ^ (2 * n + 1) := by
    simp only [hg]; push_cast; ring_nf
  have hg2 : g (n + 2) = (2 * ((n + 1 : ℕ) : ℂ) + α + β + 2) ^ (2 * n + 2) := by
    simp only [hg]; push_cast; ring_nf
  unfold Fr ratioR
  rw [prod_div_distrib, prod_div_distrib, hden1, hden2, prod_range_succ (fun j : ℕ =>
    ((j : ℂ) + 1) ^ (j + 1) * ((j : ℂ) + 1 + α) ^ j * ((j : ℂ) + 1 + β) ^ j) (n + 1)]
  have hD2 : ∏ j ∈ range (n + 2), g (j + 1) =
      (∏ i ∈ range (n + 1), g i) * g (n + 1) * g (n + 2) / g 0 := by
    rw [← hsplit]; field_simp [hgne 0]
  rw [hD2, hg0, hg1, hg2]
  have hD1 : ∏ i ∈ range (n + 1), g i ≠ 0 := prod_ne_zero_iff.mpr fun i _ => hgne i
  have he : ((n : ℂ) + α + β + 2) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have hd : (2 * (n : ℂ) + α + β + 3) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have hc : (2 * ((n + 1 : ℕ) : ℂ) + α + β + 2) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  rw [show (n + 2) * (n + 2 - 1) = (n + 1) * (n + 1 - 1) + (2 * n + 2) by
    rw [show n + 2 - 1 = n + 1 by omega, show n + 1 - 1 = n by omega]; ring]
  rw [pow_add]
  field_simp
  push_cast
  ring

end ClosedForm
section Assembly

variable {α β : ℝ}

/-- The discriminant expressed through the resultant-type product `SS`. -/
def EE (a b : ℂ) (n : ℕ) : ℂ :=
  (-1) ^ ((n + 1).choose 2) * (2 * ((n : ℂ) + a + 1) * ((n : ℂ) + b + 1)) ^ (n + 1) * SS a b n *
      (((n + 1)! : ℕ) : ℂ) ^ 2 * kk a b (n + 1) ^ 2 /
    ((2 * (n : ℂ) + a + b + 2) ^ (n + 1) * poch (a + 1) (n + 1) * poch (b + 1) (n + 1) *
      kk a b (n + 1) ^ (n + 1))

theorem EE_succ (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    EE α β (n + 1) = EE α β n * ratioR α β n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h := disc_step_algebra n (K := kk α β (n + 1)) (K2 := kk α β (n + 2))
    (S0 := SS α β n) (S1 := SS α β (n + 1)) (u1 := (n : ℂ) + α + 1) (v1 := (n : ℂ) + β + 1)
    (c1 := 2 * (n : ℂ) + α + β + 2) (u2 := ((n + 1 : ℕ) : ℂ) + α + 1)
    (v2 := ((n + 1 : ℕ) : ℂ) + β + 1) (c2 := 2 * ((n + 1 : ℕ) : ℂ) + α + β + 2)
    (d := 2 * (n : ℂ) + α + β + 3) (e := (n : ℂ) + α + β + 2) (n2 := ((n + 1 + 1 : ℕ) : ℂ))
    (pa1 := poch (α + 1) (n + 1)) (pb1 := poch (β + 1) (n + 1)) (f1 := (((n + 1)! : ℕ) : ℂ))
    (σ1 := (-1) ^ ((n + 1).choose 2))
    (kk_ne_zero hα hβ _) (ne_zero_of_re_pos (by simp; linarith))
    (ne_zero_of_re_pos (by simp; linarith)) (by exact_mod_cast Nat.succ_ne_zero (n + 1))
    (ne_zero_of_re_pos (by simp; linarith)) (ne_zero_of_re_pos (by simp; linarith))
    (ne_zero_of_re_pos (by simp; linarith)) (ne_zero_of_re_pos (by simp; linarith))
    (ne_zero_of_re_pos (by simp; linarith)) (ne_zero_of_re_pos (by simp; linarith))
    (poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) _)
    (poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) _)
    (by exact_mod_cast Nat.factorial_ne_zero (n + 1))
    (kk_succ hα hβ n) (SS_succ hα hβ n)
  have hσ : (-1 : ℂ) ^ ((n + 1 + 1).choose 2) = (-1) ^ ((n + 1).choose 2) * (-1) ^ (n + 1) := by
    rw [← pow_add, Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
  have hpa : poch ((α : ℂ) + 1) (n + 1 + 1) =
      poch (α + 1) (n + 1) * (((n + 1 : ℕ) : ℂ) + α + 1) := by
    rw [poch_succ]; ring
  have hpb : poch ((β : ℂ) + 1) (n + 1 + 1) =
      poch (β + 1) (n + 1) * (((n + 1 : ℕ) : ℂ) + β + 1) := by
    rw [poch_succ]; ring
  have hf : (((n + 1 + 1)! : ℕ) : ℂ) = (((n + 1)! : ℕ) : ℂ) * ((n + 1 + 1 : ℕ) : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  unfold EE ratioR
  rw [hσ, hpa, hpb, hf]
  exact h

theorem EE_zero (hα : -1 < α) (hβ : -1 < β) : EE α β 0 = 1 := by
  have hk : kk α β 1 = ((α : ℂ) + β + 2) / 2 := by
    simp [kk, coef_diag, poch_one]; ring
  have h1 : (α : ℂ) + 1 ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have h2 : (β : ℂ) + 1 ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have h3 : (α : ℂ) + β + 2 ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  simp only [EE, SS_zero, hk]
  norm_num [poch_one]
  field_simp

theorem EE_eq_Fr (hα : -1 < α) (hβ : -1 < β) (n : ℕ) : EE α β n = Fr α β (n + 1) := by
  induction n with
  | zero => rw [EE_zero hα hβ]; simp [Fr]
  | succ n ih => rw [EE_succ hα hβ, ih, Fr_succ hα hβ]

end Assembly
section Main

variable {α β : ℝ}

theorem roots_jacPoly_eq (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (x : Fin n → ℝ)
    (hroot : ∀ i, jacobiPolyP α β n (x i) = 0) (hinj : Function.Injective x) :
    (jacPoly α β n).roots = (univ.val.map fun i => (x i : ℂ)) := by
  have hα' : -1 < (α : ℂ).re := by simpa using hα
  have hne := jacPoly_ne_zero hα hβ n
  have hnd : (univ.val.map fun i => (x i : ℂ)).Nodup :=
    Multiset.Nodup.map (fun i j h => hinj (by exact_mod_cast h)) univ.nodup
  have hle : (univ.val.map fun i => (x i : ℂ)) ≤ (jacPoly α β n).roots := by
    rw [Multiset.le_iff_subset hnd]
    intro y hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hy
    rw [mem_roots hne, IsRoot, eval_jacPoly hα']
    exact hroot i
  refine (Multiset.eq_of_le_of_card_le hle ?_).symm
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_jacPoly hα hβ, Multiset.card_map,
    card_val, card_univ, Fintype.card_fin]

theorem jacPoly_eq_nodal (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (x : Fin n → ℝ)
    (hroot : ∀ i, jacobiPolyP α β n (x i) = 0) (hinj : Function.Injective x) :
    jacPoly α β n = C (kk α β n) * Lagrange.nodal univ fun i => (x i : ℂ) := by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := jacPoly α β n))]
  rw [leadingCoeff_jacPoly hα hβ, roots_jacPoly_eq hα hβ x hroot hinj, Multiset.map_map]
  rfl

theorem disc_eq_EE (hα : -1 < α) (hβ : -1 < β) (m : ℕ) (x : Fin (m + 1) → ℝ)
    (hroot : ∀ i, jacobiPolyP α β (m + 1) (x i) = 0) (hinj : Function.Injective x) :
    (∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
      if i.val < j.val then ((x i - x j : ℝ) : ℂ) ^ 2 else 1) = EE α β m := by
  have hα' : -1 < (α : ℂ).re := by simpa using hα
  have hβ' : -1 < (β : ℂ).re := by simpa using hβ
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set xc : Fin (m + 1) → ℂ := fun i => (x i : ℂ) with hxc
  set K := kk α β (m + 1) with hK
  have hK0 : K ≠ 0 := kk_ne_zero hα hβ _
  have hnodal := jacPoly_eq_nodal hα hβ x hroot hinj
  -- derivative at the nodes
  have hder : ∀ i, deriv (jacobiPolyP α β (m + 1)) (xc i) =
      K * ∏ j ∈ univ.erase i, (xc i - xc j) := by
    intro i
    have hfun : jacobiPolyP α β (m + 1) = fun z => (jacPoly α β (m + 1)).eval z :=
      funext fun z => (eval_jacPoly hα' _ _ z).symm
    rw [hfun, Polynomial.deriv, hnodal, derivative_C_mul, eval_mul, eval_C,
      Lagrange.eval_nodal_derivative_eval_node_eq (mem_univ i), Lagrange.eval_nodal]
  -- lowering relation at the nodes
  have hlow : ∀ i, (2 * (m : ℂ) + α + β + 2) * (1 - xc i ^ 2) *
      (K * ∏ j ∈ univ.erase i, (xc i - xc j)) =
      2 * ((m : ℂ) + α + 1) * ((m : ℂ) + β + 1) * jacobiPolyP α β m (xc i) := by
    intro i
    have h := jacobi_lowering_derivative (β := (β : ℂ)) hα' m (xc i)
    rw [hder i, hroot i] at h
    rw [h]; ring
  have hprod := congrArg (fun f : Fin (m + 1) → ℂ => ∏ i, f i) (funext hlow)
  simp only [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin] at hprod
  -- the product of `P_m` over the nodes
  have hSS : ∏ i, jacobiPolyP α β m (xc i) = SS α β m := by
    unfold SS
    rw [roots_jacPoly_eq hα hβ x hroot hinj, Multiset.map_map]
    simp only [Function.comp_def, eval_jacPoly hα']
    rfl
  -- values at `±1`
  have h1 : K * ∏ i, (1 - xc i) = poch (α + 1) (m + 1) / (m + 1)! := by
    have := congrArg (fun p => p.eval 1) hnodal
    simp only [eval_mul, eval_C, Lagrange.eval_nodal, eval_jacPoly hα'] at this
    rw [← this, jacobi_at_one hα']
  have h2 : K * ∏ i, (1 + xc i) = poch (β + 1) (m + 1) / (m + 1)! := by
    have := congrArg (fun p => p.eval (-1)) hnodal
    simp only [eval_mul, eval_C, Lagrange.eval_nodal, eval_jacPoly hα'] at this
    rw [jacobi_reflection hα' hβ' (m + 1) 1, jacobi_at_one hβ'] at this
    have hneg : ∏ i, (-1 - xc i) = (-1) ^ (m + 1) * ∏ i, (1 + xc i) := by
      have hc : ∏ _i : Fin (m + 1), (-1 : ℂ) = (-1) ^ (m + 1) := by simp
      rw [← hc, ← prod_mul_distrib]
      exact prod_congr rfl fun i _ => by ring
    rw [hneg, ← hK] at this
    have hs : ((-1 : ℂ) ^ (m + 1)) * (-1) ^ (m + 1) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    linear_combination (-(-1) ^ (m + 1)) * this -
      (K * ∏ i, (1 + xc i) - poch ((β : ℂ) + 1) (m + 1) / (m + 1)!) * hs
  have hsq : ∏ i, (1 - xc i ^ 2) = (∏ i, (1 - xc i)) * ∏ i, (1 + xc i) := by
    rw [← prod_mul_distrib]; exact prod_congr rfl fun i _ => by ring
  have hpair := prod_prod_erase_sub xc
  -- assemble
  have hLHS : (∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
      if i.val < j.val then ((x i - x j : ℝ) : ℂ) ^ 2 else 1) =
      ∏ i, ∏ j, (if i.val < j.val then (xc i - xc j) ^ 2 else 1) := by
    simp [hxc]
  rw [hLHS]
  set D := ∏ i, ∏ j, (if i.val < j.val then (xc i - xc j) ^ 2 else (1 : ℂ))
  set P := ∏ i, ∏ j ∈ univ.erase i, (xc i - xc j)
  rw [hSS, hsq] at hprod
  have hσ : ((-1 : ℂ) ^ (m + 1).choose 2) * (-1) ^ (m + 1).choose 2 = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hpa : poch ((α : ℂ) + 1) (m + 1) ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) _
  have hpb : poch ((β : ℂ) + 1) (m + 1) ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) _
  have hc : (2 * (m : ℂ) + α + β + 2) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have hf : (((m + 1)! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m + 1)
  have hA : ∏ i, (1 - xc i) = poch (α + 1) (m + 1) / (m + 1)! / K := by
    rw [← h1]; field_simp
  have hB : ∏ i, (1 + xc i) = poch (β + 1) (m + 1) / (m + 1)! / K := by
    rw [← h2]; field_simp
  rw [hA, hB] at hprod
  unfold EE
  rw [hpair] at hprod
  rw [← hK]
  have hden : (2 * (m : ℂ) + α + β + 2) ^ (m + 1) * poch (α + 1) (m + 1) * poch (β + 1) (m + 1) *
      K ^ (m + 1) ≠ 0 := by
    simp [hc, hpa, hpb, hK0]
  rw [eq_div_iff hden]
  field_simp at hprod
  simp only [mul_pow] at hprod ⊢
  linear_combination ((-1 : ℂ) ^ (m + 1).choose 2) * hprod -
    (D * ((2 * (m : ℂ) + α + β + 2) ^ (m + 1) * poch (α + 1) (m + 1) * poch (β + 1) (m + 1) *
      K ^ (m + 1))) * hσ

end Main

end JacobiDisc

/-- The product of squared differences of the Jacobi roots (AAR Theorem 8.5.3). -/
theorem jacobiPolyP_prod_sq_sub {α β : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hα : -1 < α) (hβ : -1 < β) (x : Fin n → ℝ)
    (hroot : ∀ i, jacobiPolyP α β n (x i) = 0) (hinj : Function.Injective x) :
    (Finset.univ.prod fun i : Fin n => Finset.univ.prod fun j : Fin n =>
      if i.val < j.val then ((x i - x j : ℝ) : ℂ) ^ (2 : ℕ) else (1 : ℂ)) =
      (2 : ℂ) ^ (n * (n - 1)) *
        Finset.univ.prod fun j : Fin n =>
          ((j : ℂ) + 1) ^ (j.val + 1) *
            ((j : ℂ) + 1 + α) ^ j.val *
            ((j : ℂ) + 1 + β) ^ j.val /
            ((n : ℂ) + j + 1 + α + β) ^ (n + j.val - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  rw [JacobiDisc.disc_eq_EE hα hβ m x hroot hinj, JacobiDisc.EE_eq_Fr hα hβ m, JacobiDisc.Fr]
  congr 1
  exact (Fin.prod_univ_eq_prod_range (fun j : ℕ => ((j : ℂ) + 1) ^ (j + 1) *
    ((j : ℂ) + 1 + α) ^ j * ((j : ℂ) + 1 + β) ^ j /
      (((m + 1 : ℕ) : ℂ) + j + 1 + α + β) ^ (m + 1 + j - 1)) (m + 1)).symm

end DLMF.OrthogonalPolynomials
