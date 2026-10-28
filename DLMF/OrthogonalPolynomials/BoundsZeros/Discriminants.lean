/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.BoundsZeros.PointwiseAndZeroBounds

/-!
# Discriminants of classical orthogonal polynomials

Resultant and product calculations give the Laguerre and Hermite discriminant formulas.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.BoundsZeros`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter

open scoped Real Nat Topology

open DLMF.Hypergeometric

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-! ### Helpers for the discriminant formulas -/

/-- For real `c`, the real part of `(c)_n` is `∏_{k<n} (c + k)`. -/
theorem re_poch_ofReal (c : ℝ) (n : ℕ) :
    (poch (c : ℂ) n).re = ∏ k ∈ Finset.range n, (c + k) := by
  have h := poch_mul_pow (c : ℂ) 1 n
  simp only [one_pow, mul_one] at h
  rw [h]
  have : (∏ k ∈ Finset.range n, ((c : ℂ) + k)) = ((∏ k ∈ Finset.range n, (c + k) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [this, Complex.ofReal_re]

/-- `∏_{j=1}^n f(j) = ∏_{k<n} f(k+1)`. -/
theorem prod_Icc_one_eq_prod_range {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∏ j ∈ Finset.Icc 1 n, f j = ∏ k ∈ Finset.range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

/-- The per-factor identity converting the AAR form of the Jacobi discriminant into the DLMF
form. -/
theorem jacobiDisc_factor {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {m k : ℕ} (hk : k ≤ m) :
    ((k + 1 : ℕ) : ℝ) ^ (((k + 1 : ℕ) : ℤ) - 2 * ((m + 1 : ℕ) : ℤ) + 2) *
        (((k + 1 : ℕ) : ℝ) + α) ^ (k + 1 - 1) * (((k + 1 : ℕ) : ℝ) + β) ^ (k + 1 - 1) *
        (((m + 1 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) + α + β) ^ (m + 1 - (k + 1)) =
      ((((m + 1 : ℕ) : ℝ) + α + β + 1 + k) ^ (2 * m) / ((k : ℝ) + 1) ^ (2 * m)) *
        (((k : ℝ) + 1) ^ (k + 1) * ((k : ℝ) + 1 + α) ^ k * ((k : ℝ) + 1 + β) ^ k /
          (((m + 1 : ℕ) : ℝ) + k + 1 + α + β) ^ (m + 1 + k - 1)) := by
  have hB : ((k : ℝ) + 1) ≠ 0 := by positivity
  set a : ℝ := ((m + 1 : ℕ) : ℝ) + α + β + 1 + k with ha
  have ha0 : a ≠ 0 := by
    have : (0 : ℝ) < a := by rw [ha]; push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k),
      (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    exact this.ne'
  have h1 : ((m + 1 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) + α + β = a := by rw [ha]; push_cast; ring
  have h2 : ((m + 1 : ℕ) : ℝ) + k + 1 + α + β = a := by rw [ha]; ring
  have hz : ((k + 1 : ℕ) : ℝ) ^ (((k + 1 : ℕ) : ℤ) - 2 * ((m + 1 : ℕ) : ℤ) + 2) =
      ((k : ℝ) + 1) ^ (k + 1) / ((k : ℝ) + 1) ^ (2 * m) := by
    rw [show (((k + 1 : ℕ) : ℤ) - 2 * ((m + 1 : ℕ) : ℤ) + 2) =
      ((k + 1 : ℕ) : ℤ) - ((2 * m : ℕ) : ℤ) by push_cast; ring]
    rw [zpow_sub₀ (by push_cast; exact hB), zpow_natCast, zpow_natCast]
    push_cast; ring
  rw [hz, h1, h2, show m + 1 - (k + 1) = m - k by omega, show m + 1 + k - 1 = m + k by omega,
    show k + 1 - 1 = k by omega, show 2 * m = (m + k) + (m - k) by omega, pow_add a]
  push_cast
  field_simp

/-- Formula under the stated hypotheses: `rootDiscriminant ((poch (n + α + β + 1) n).re / (2 ^ n *
n.factorial)) x = (2 : ℝ)⁻¹ ^ (n * (n - 1)) * ∏ j ∈ Finset.Icc 1 n, (j : ℝ) ^ ((j : ℤ) - 2 * n
+ 2) * (j + α) ^ (j - 1) * (j + β) ^ (j - 1) * (n + j + α + β) ^ (n - j)`. -/
@[dlmf 18.16.E19]
theorem jacobi_discriminant {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hinj : Function.Injective x) (hroot : ∀ i, jacobiPolyP α β n (x i) = 0) :
    rootDiscriminant ((poch (n + α + β + 1) n).re / (2 ^ n * n.factorial)) x =
      (2 : ℝ)⁻¹ ^ (n * (n - 1)) * ∏ j ∈ Finset.Icc 1 n,
        (j : ℝ) ^ ((j : ℤ) - 2 * n + 2) * (j + α) ^ (j - 1) * (j + β) ^ (j - 1) *
          (n + j + α + β) ^ (n - j) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  have hD := jacobiPolyP_prod_sq_sub (n := m + 1) (Nat.succ_ne_zero m) hα hβ x hroot hinj
  have hL : (Finset.univ.prod fun i : Fin (m + 1) => Finset.univ.prod fun j : Fin (m + 1) =>
      if i.val < j.val then ((x i - x j : ℝ) : ℂ) ^ (2 : ℕ) else (1 : ℂ)) =
      ((∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
        if i.val < j.val then (x i - x j) ^ 2 else (1 : ℝ) : ℝ) : ℂ) := by
    push_cast
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [hL] at hD
  have hDR : (∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
      if i.val < j.val then (x i - x j) ^ 2 else (1 : ℝ)) =
      (2 : ℝ) ^ ((m + 1) * (m + 1 - 1)) * ∏ j : Fin (m + 1), ((j : ℝ) + 1) ^ (j.val + 1) *
        ((j : ℝ) + 1 + α) ^ j.val * ((j : ℝ) + 1 + β) ^ j.val /
          (((m + 1 : ℕ) : ℝ) + j + 1 + α + β) ^ (m + 1 + j.val - 1) := by
    exact_mod_cast hD
  rw [Fin.prod_univ_eq_prod_range (fun k : ℕ => ((k : ℝ) + 1) ^ (k + 1) *
    ((k : ℝ) + 1 + α) ^ k * ((k : ℝ) + 1 + β) ^ k /
      (((m + 1 : ℕ) : ℝ) + k + 1 + α + β) ^ (m + 1 + k - 1)) (m + 1)] at hDR
  have hc : (((m + 1 : ℕ) : ℂ) + α + β + 1) = ((((m + 1 : ℕ) : ℝ) + α + β + 1 : ℝ) : ℂ) := by
    push_cast; ring
  unfold rootDiscriminant
  simp only [Fin.lt_def]
  rw [hDR, hc, re_poch_ofReal, prod_Icc_one_eq_prod_range,
    show (2 * ((m + 1 : ℕ) : ℤ) - 2) = ((2 * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    ← Finset.prod_range_add_one_eq_factorial]
  rw [Finset.prod_congr rfl fun k hk => jacobiDisc_factor hα hβ
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  simp only [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_pow, Nat.succ_eq_add_one]
  push_cast

  have h2 : (2 : ℝ)⁻¹ ^ ((m + 1) * m) = 2 ^ ((m + 1) * m) / (2 ^ (m + 1)) ^ (2 * m) := by
    rw [← pow_mul, inv_pow, show (m + 1) * (2 * m) = (m + 1) * m + (m + 1) * m by ring, pow_add]
    field_simp
  rw [h2]
  ring_nf
  simp only [one_div]
  ring

/-! ### The discriminant of a Laguerre polynomial

Schur's route as for Jacobi: `SSL m = ∏ L_m(y)` over the zeros of `L_{m+1}` satisfies a
first-order recursion from the three-term recurrence, and `x L_{m+1}'(x) = -(m+α+1) L_m(x)` at
the zeros, with `L_{m+1}(0) = (α+1)_{m+1}/(m+1)!`, expresses the discriminant through `SSL`. -/

namespace LagDisc

open Polynomial Finset JacobiDisc DLMF.Confluent

/-- Coefficient of `x^j` in `L_n^{(a)}`. -/
def lcoef (a : ℂ) (n j : ℕ) : ℂ := poch (a + 1) n / n ! * kummerMCoeff (-(n : ℂ)) (a + 1) j

/-- The Laguerre polynomial as an element of `ℂ[X]`. -/
def lagPoly (a : ℂ) (n : ℕ) : ℂ[X] := ∑ j ∈ range (n + 1), C (lcoef a n j) * X ^ j

/-- The leading coefficient `(-1)^n / n!`. -/
def KL (n : ℕ) : ℂ := (-1) ^ n / n !

/-- `lagPoly a n` evaluates to `L_n^{(a)}`. -/
theorem eval_lagPoly (a : ℂ) (n : ℕ) (x : ℂ) : (lagPoly a n).eval x = laguerrePolyL a n x := by
  rw [laguerrePolyL_eq_sum_coeff]
  simp [lagPoly, eval_finsetSum, lcoef]

/-- The coefficients of `lagPoly a n`. -/
theorem coeff_lagPoly (a : ℂ) (n k : ℕ) :
    (lagPoly a n).coeff k = if k < n + 1 then lcoef a n k else 0 := by
  simp only [lagPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

variable {α : ℝ}

/-- For `α > -1`, `(α+1)_n ≠ 0`. -/
theorem poch_ne_zero' (hα : -1 < α) (n : ℕ) : poch ((α : ℂ) + 1) n ≠ 0 :=
  poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) _

/-- The leading coefficient of `L_n^{(α)}` is `(-1)ⁿ/n!`. -/
theorem lcoef_self (hα : -1 < α) (n : ℕ) : lcoef α n n = KL n := by
  have hp := poch_ne_zero' hα n
  have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [lcoef, kummerMCoeff, poch_neg_coe_nat, Nat.descFactorial_self, KL]
  field_simp

/-- `(-1)ⁿ/n! ≠ 0`. -/
theorem KL_ne_zero (n : ℕ) : KL n ≠ 0 := by
  unfold KL
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast n.factorial_ne_zero)

/-- For `α > -1`, `lagPoly α n` has degree `n`. -/
theorem natDegree_lagPoly (hα : -1 < α) (n : ℕ) : (lagPoly α n).natDegree = n := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_lagPoly]
    split_ifs with h
    · omega
    · rfl
  · rw [coeff_lagPoly]
    split_ifs with h
    · rw [lcoef_self hα]; exact KL_ne_zero n
    · omega

/-- For `α > -1`, the leading coefficient of `lagPoly α n` is `(-1)ⁿ/n!`. -/
theorem leadingCoeff_lagPoly (hα : -1 < α) (n : ℕ) : (lagPoly α n).leadingCoeff = KL n := by
  rw [leadingCoeff, natDegree_lagPoly hα, coeff_lagPoly]
  split_ifs with h
  · exact lcoef_self hα n
  · omega

/-- For `α > -1`, `lagPoly α n ≠ 0`. -/
theorem lagPoly_ne_zero (hα : -1 < α) (n : ℕ) : lagPoly α n ≠ 0 := by
  intro h
  have := leadingCoeff_lagPoly hα n
  rw [h, leadingCoeff_zero] at this
  exact KL_ne_zero n this.symm

/-- If `x` lists `n` distinct real zeros of `L_n^{(α)}`, they are all its complex roots. -/
theorem roots_lagPoly_eq (hα : -1 < α) {n : ℕ} (x : Fin n → ℝ)
    (hroot : ∀ i, laguerrePolyL α n (x i) = 0) (hinj : Function.Injective x) :
    (lagPoly α n).roots = (univ.val.map fun i => (x i : ℂ)) := by
  have hne := lagPoly_ne_zero hα n
  have hnd : (univ.val.map fun i => (x i : ℂ)).Nodup :=
    Multiset.Nodup.map (fun i j h => hinj (by exact_mod_cast h)) univ.nodup
  have hle : (univ.val.map fun i => (x i : ℂ)) ≤ (lagPoly α n).roots := by
    rw [Multiset.le_iff_subset hnd]
    intro y hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hy
    rw [mem_roots hne, IsRoot, eval_lagPoly]
    exact hroot i
  refine (Multiset.eq_of_le_of_card_le hle ?_).symm
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_lagPoly hα, Multiset.card_map,
    card_val, card_univ, Fintype.card_fin]

/-- `L_n^{(α)} = (-1)ⁿ/n! ∏ (X - xᵢ)` over its `n` distinct real zeros. -/
theorem lagPoly_eq_nodal (hα : -1 < α) {n : ℕ} (x : Fin n → ℝ)
    (hroot : ∀ i, laguerrePolyL α n (x i) = 0) (hinj : Function.Injective x) :
    lagPoly α n = C (KL n) * Lagrange.nodal univ fun i => (x i : ℂ) := by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := lagPoly α n))]
  rw [leadingCoeff_lagPoly hα, roots_lagPoly_eq hα x hroot hinj, Multiset.map_map]
  rfl
/-- `∏ L_m(y)` over the zeros `y` of `L_{m+1}`. -/
def SSL (a : ℂ) (m : ℕ) : ℂ := ((lagPoly a (m + 1)).roots.map fun y => (lagPoly a m).eval y).prod

/-- `SSL a 0 = 1`. -/
theorem SSL_zero (a : ℂ) : SSL a 0 = 1 := by
  simp [SSL, lagPoly, lcoef, poch_zero, kummerMCoeff]

/-- At a zero of `L_{m+1}^{(α)}` the three-term recurrence gives
`L_{m+2}^{(α)} = -(m+α+1)/(m+2) L_m^{(α)}`. -/
theorem eval_lagPoly_two_of_root (hα : -1 < α) (m : ℕ) {y : ℂ}
    (hy : (lagPoly α (m + 1)).eval y = 0) :
    (lagPoly α (m + 2)).eval y = -((m : ℂ) + α + 1) / (m + 2) * (lagPoly α m).eval y := by
  have hα' : -1 < (α : ℂ).re := by simpa using hα
  rw [eval_lagPoly] at hy ⊢
  rw [eval_lagPoly]
  have h := laguerrePolyL_recurrence hα' m y
  rw [hy] at h
  have h2 : (m + 2 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + 1)
  field_simp
  linear_combination h

/-- The recursion for the product of `L_m^{(α)}` over the zeros of `L_{m+1}^{(α)}`. -/
theorem SSL_succ (hα : -1 < α) (m : ℕ) :
    SSL α (m + 1) = (-1) ^ (m + 1) * ((m : ℂ) + 1 + α) ^ (m + 1) / ((m + 1) ! : ℂ) * SSL α m := by
  have key := lc_pow_mul_prod_roots_eval (lagPoly α (m + 2)) (lagPoly α (m + 1))
  rw [natDegree_lagPoly hα, natDegree_lagPoly hα, leadingCoeff_lagPoly hα,
    leadingCoeff_lagPoly hα] at key
  have hne := lagPoly_ne_zero hα (m + 1)
  have hmap : ((lagPoly α (m + 1)).roots.map fun y => (lagPoly α (m + 2)).eval y) =
      ((lagPoly α (m + 1)).roots.map fun y =>
        (-((m : ℂ) + α + 1) / (m + 2)) * (lagPoly α m).eval y) := by
    refine Multiset.map_congr rfl fun y hy => ?_
    exact eval_lagPoly_two_of_root hα m ((mem_roots hne).mp hy)
  rw [hmap, prod_map_const_mul, IsAlgClosed.card_roots_eq_natDegree, natDegree_lagPoly hα] at key
  change KL (m + 2) ^ (m + 1) * SSL α (m + 1) = _ * (_ * SSL α m) at key
  have he : Even ((m + 2) * (m + 1)) := by
    rw [mul_comm]; exact Nat.even_mul_succ_self (m + 1)
  rw [he.neg_one_pow, one_mul] at key
  have hK := KL_ne_zero (m + 2)
  simp only [KL] at key hK
  have h2 : (m + 2 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + 1)
  have hf1 : ((m + 1) ! : ℂ) ≠ 0 := by exact_mod_cast (m + 1).factorial_ne_zero
  have hfac : ((m + 2) ! : ℂ) = (m + 2) * (m + 1) ! := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hfac] at key
  have e1 : ((-1 : ℂ) ^ (m + 2)) ^ (m + 1) = 1 := by
    rw [← pow_mul]; exact he.neg_one_pow
  have e2 : ((-1 : ℂ) ^ (m + 1)) ^ (m + 2) = 1 := by
    rw [← pow_mul, mul_comm]; exact he.neg_one_pow
  rw [div_pow, div_pow, e1, e2] at key
  field_simp at key
  rw [← mul_pow, show ((m : ℂ) + 2) * ((m + 1)! : ℂ) * -(((m : ℂ) + α + 1) / (m + 2)) =
    -((m : ℂ) + α + 1) * (m + 1)! by field_simp, mul_pow, neg_pow] at key
  rw [div_mul_eq_mul_div, eq_div_iff hf1]
  apply mul_right_cancel₀ (pow_ne_zero (m + 1) hf1)
  linear_combination key

/-- Closed form of the product of `L_m^{(α)}` over the zeros of `L_{m+1}^{(α)}`. -/
theorem SSL_eq (hα : -1 < α) (m : ℕ) :
    SSL α m = ∏ k ∈ range m, (-1) ^ (k + 1) * ((k : ℂ) + 1 + α) ^ (k + 1) / ((k + 1) ! : ℂ) := by
  induction m with
  | zero => simp [SSL_zero]
  | succ m ih => rw [SSL_succ hα, ih, prod_range_succ]; ring

/-- The Laguerre discriminant expressed through `SSL`. -/
theorem disc_eq (hα : -1 < α) (m : ℕ) (x : Fin (m + 1) → ℝ)
    (hroot : ∀ i, laguerrePolyL α (m + 1) (x i) = 0) (hinj : Function.Injective x) :
    (∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
      if i.val < j.val then ((x i - x j : ℝ) : ℂ) ^ 2 else 1) *
        (KL (m + 1) ^ (m + 1) * poch ((α : ℂ) + 1) (m + 1)) =
      (-1) ^ (m + 1).choose 2 * (-((m : ℂ) + α + 1)) ^ (m + 1) * SSL α m := by
  have hα' : -1 < (α : ℂ).re := by simpa using hα
  set xc : Fin (m + 1) → ℂ := fun i => (x i : ℂ) with hxc
  set K := KL (m + 1) with hK
  have hnodal := lagPoly_eq_nodal hα x hroot hinj
  have hder : ∀ i, deriv (laguerrePolyL α (m + 1)) (xc i) =
      K * ∏ j ∈ univ.erase i, (xc i - xc j) := by
    intro i
    have hfun : laguerrePolyL α (m + 1) = fun z => (lagPoly α (m + 1)).eval z :=
      funext fun z => (eval_lagPoly _ _ z).symm
    rw [hfun, Polynomial.deriv, hnodal, derivative_C_mul, eval_mul, eval_C,
      Lagrange.eval_nodal_derivative_eval_node_eq (mem_univ i), Lagrange.eval_nodal]
  have hrel : ∀ i, xc i * (K * ∏ j ∈ univ.erase i, (xc i - xc j)) =
      -((m : ℂ) + α + 1) * laguerrePolyL α m (xc i) := by
    intro i
    rw [← hder i, laguerrePolyL_derivative hα' m]
    have h := laguerrePolyL_mul_argument hα' m (xc i)
    rw [hroot i] at h
    linear_combination -h
  have hprod := congrArg (fun f : Fin (m + 1) → ℂ => ∏ i, f i) (funext hrel)
  simp only [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin] at hprod
  have hSS : ∏ i, laguerrePolyL α m (xc i) = SSL α m := by
    unfold SSL
    rw [roots_lagPoly_eq hα x hroot hinj, Multiset.map_map]
    simp only [Function.comp_def, eval_lagPoly]
    rfl
  have h0 : K * ∏ i, (0 - xc i) = poch ((α : ℂ) + 1) (m + 1) / (m + 1)! := by
    have := congrArg (fun p => p.eval 0) hnodal
    simp only [eval_mul, eval_C, Lagrange.eval_nodal, eval_lagPoly] at this
    rw [← this, laguerrePolyL_at_zero]
  have hneg : ∏ i, (0 - xc i) = (-1) ^ (m + 1) * ∏ i, xc i := by
    have hc : ∏ _i : Fin (m + 1), (-1 : ℂ) = (-1) ^ (m + 1) := by simp
    rw [← hc, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => by ring
  have hx : ∏ i, xc i = poch ((α : ℂ) + 1) (m + 1) := by
    rw [hneg, hK, KL] at h0
    have hf : ((m + 1)! : ℂ) ≠ 0 := by exact_mod_cast (m + 1).factorial_ne_zero
    have hs : ((-1 : ℂ) ^ (m + 1)) * (-1) ^ (m + 1) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    field_simp at h0
    linear_combination h0 - (∏ i, xc i) * hs
  have hpair := prod_prod_erase_sub xc
  have hLHS : (∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
      if i.val < j.val then ((x i - x j : ℝ) : ℂ) ^ 2 else 1) =
      ∏ i, ∏ j, (if i.val < j.val then (xc i - xc j) ^ 2 else 1) := by
    simp [hxc]
  rw [hLHS]
  rw [hSS, hx, hpair] at hprod
  have hσ : ((-1 : ℂ) ^ (m + 1).choose 2) * (-1) ^ (m + 1).choose 2 = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination ((-1 : ℂ) ^ (m + 1).choose 2) * hprod -
    ((∏ i, ∏ j, (if i.val < j.val then (xc i - xc j) ^ 2 else (1 : ℂ))) *
      (K ^ (m + 1) * poch ((α : ℂ) + 1) (m + 1))) * hσ

/-- Reindexing identity for the products `∏ (k+1+c)^{k+1}`. -/
theorem prod_pow_succ_shift (c : ℂ) (m : ℕ) :
    (∏ k ∈ range m, ((k : ℂ) + 1 + c) ^ (k + 1)) * ((m : ℂ) + 1 + c) ^ (m + 1) =
      (∏ k ∈ range (m + 1), ((k : ℂ) + 1 + c) ^ k) * ∏ k ∈ range (m + 1), ((k : ℂ) + 1 + c) := by
  rw [← prod_mul_distrib]
  simp_rw [← pow_succ]
  rw [prod_range_succ]

/-- `((m+1)!)^{m+1} = ∏_{k<m} (k+1)! · ∏_{k ≤ m} (k+1)^{k+1}`. -/
theorem factorial_pow_eq (m : ℕ) :
    (((m + 1)! : ℕ) : ℂ) ^ (m + 1) =
      (∏ k ∈ range m, (((k + 1)! : ℕ) : ℂ)) * ∏ k ∈ range (m + 1), ((k : ℂ) + 1) ^ (k + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, prod_range_succ (fun k => ((k : ℂ) + 1) ^ (k + 1)) (m + 1)]
    rw [show (m + 1 + 1)! = (m + 2) * (m + 1)! from Nat.factorial_succ (m + 1)]
    push_cast at ih ⊢
    rw [mul_pow, pow_succ (((m + 1)! : ℂ)), ih]
    ring

/-- `∏_{k<m} (-1)^{k+1} = (-1)^{C(m+1,2)}`. -/
theorem prod_neg_one_pow_succ (m : ℕ) :
    ∏ k ∈ range m, (-1 : ℂ) ^ (k + 1) = (-1) ^ (m + 1).choose 2 := by
  rw [prod_pow_eq_pow_sum]
  congr 1
  rw [Nat.choose_two_right, ← Finset.sum_range_id (m + 1), Finset.sum_range_succ']
  simp

/-- `(c)_n = ∏_{k<n} (c + k)`. -/
theorem poch_eq_prod (c : ℂ) (n : ℕ) : poch c n = ∏ k ∈ range n, (c + k) := by
  have h := poch_mul_pow c 1 n
  simp only [one_pow, mul_one] at h
  exact h

/-- Closed form of the discriminant of the Laguerre polynomial `L_{m+1}^{(α)}` (Stieltjes). -/
theorem disc_closed (hα : -1 < α) (m : ℕ) (x : Fin (m + 1) → ℝ)
    (hroot : ∀ i, laguerrePolyL α (m + 1) (x i) = 0) (hinj : Function.Injective x) :
    KL (m + 1) ^ (2 * m) * (∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
      if i.val < j.val then ((x i - x j : ℝ) : ℂ) ^ 2 else 1) =
      ∏ k ∈ range (m + 1), ((k : ℂ) + 1) ^ (k + 1) / ((k : ℂ) + 1) ^ (2 * m) *
        ((k : ℂ) + 1 + α) ^ k := by
  have hD := disc_eq hα m x hroot hinj
  generalize (∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
      if i.val < j.val then ((x i - x j : ℝ) : ℂ) ^ 2 else 1) = D at hD ⊢
  rw [SSL_eq hα, prod_div_distrib, prod_mul_distrib, prod_neg_one_pow_succ] at hD
  have hQ : poch ((α : ℂ) + 1) (m + 1) = ∏ k ∈ range (m + 1), ((k : ℂ) + 1 + α) := by
    rw [poch_eq_prod]; exact prod_congr rfl fun k _ => by ring
  rw [hQ] at hD
  rw [prod_mul_distrib, prod_div_distrib, prod_pow]
  have hfN : (∏ k ∈ range (m + 1), ((k : ℂ) + 1)) = (((m + 1)! : ℕ) : ℂ) := by
    rw [← Finset.prod_range_add_one_eq_factorial]; push_cast; rfl
  rw [hfN]
  have hP1 := prod_pow_succ_shift (α : ℂ) m
  have hP2 := factorial_pow_eq m
  have hQ0 : (∏ k ∈ range (m + 1), ((k : ℂ) + 1 + α)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun k _ => by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hF0 : (∏ k ∈ range m, (((k + 1)! : ℕ) : ℂ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun k _ => by exact_mod_cast (k + 1).factorial_ne_zero
  have hN0 : (((m + 1)! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (m + 1).factorial_ne_zero
  have hσ : ((-1 : ℂ) ^ (m + 1).choose 2) * (-1) ^ (m + 1).choose 2 = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hs2 : ((-1 : ℂ) ^ (m + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hsN : ((-1 : ℂ) ^ (m + 1)) * ((-1 : ℂ) ^ (m + 1)) ^ (m + 1) = 1 := by
    rw [← pow_succ', ← pow_mul]
    exact (Nat.even_mul_succ_self (m + 1)).neg_one_pow
  have hK2 : KL (m + 1) ^ (2 * m) = 1 / (((m + 1)! : ℕ) : ℂ) ^ (2 * m) := by
    rw [KL, div_pow, pow_mul, hs2, one_pow]
  have hKN : KL (m + 1) ^ (m + 1) = ((-1 : ℂ) ^ (m + 1)) ^ (m + 1) /
      (((m + 1)! : ℕ) : ℂ) ^ (m + 1) := by
    rw [KL, div_pow]
  rw [hK2]
  rw [hKN] at hD
  rw [show (m : ℂ) + α + 1 = (m : ℂ) + 1 + α by ring, neg_pow ((m : ℂ) + 1 + α)] at hD
  set sg := (-1 : ℂ) ^ (m + 1) with hsg
  set σ := (-1 : ℂ) ^ (m + 1).choose 2 with hσdef
  set A := ∏ k ∈ range m, ((k : ℂ) + 1 + α) ^ (k + 1)
  set F := ∏ k ∈ range m, (((k + 1)! : ℕ) : ℂ)
  set Q := ∏ k ∈ range (m + 1), ((k : ℂ) + 1 + α)
  set Nf := (((m + 1)! : ℕ) : ℂ)
  set c := (m : ℂ) + 1 + α
  set Ak := ∏ k ∈ range (m + 1), ((k : ℂ) + 1 + α) ^ k
  set Bp := ∏ k ∈ range (m + 1), ((k : ℂ) + 1) ^ (k + 1)
  clear_value sg σ A F Q Nf c Ak Bp
  have h1 : D * sg ^ (m + 1) * Q * F = sg * (A * c ^ (m + 1)) * Nf ^ (m + 1) := by
    have hNm : Nf ^ (m + 1) ≠ 0 := pow_ne_zero _ hN0
    calc D * sg ^ (m + 1) * Q * F
        = (D * (sg ^ (m + 1) / Nf ^ (m + 1) * Q)) * (Nf ^ (m + 1) * F) := by
          field_simp
      _ = (σ * (sg * c ^ (m + 1)) * (σ * A / F)) * (Nf ^ (m + 1) * F) := by rw [hD]
      _ = (σ * σ) * (sg * (A * c ^ (m + 1)) * Nf ^ (m + 1)) := by field_simp
      _ = sg * (A * c ^ (m + 1)) * Nf ^ (m + 1) := by rw [hσ, one_mul]
  rw [hP1, hP2] at h1
  have h2 : D * sg ^ (m + 1) = sg * (Ak * Bp) := by
    apply mul_right_cancel₀ (mul_ne_zero hQ0 hF0)
    linear_combination h1
  have h3 : D = Bp * Ak := by
    linear_combination sg * h2 - D * hsN + (Ak * Bp) * hs2
  rw [h3]
  field_simp

end LagDisc

/-- Formula under the stated hypotheses: `rootDiscriminant ((-1 : ℝ) ^ n / n.factorial) x = ∏ j ∈
Finset.Icc 1 n, (j : ℝ) ^ ((j : ℤ) - 2 * n + 2) * (j + α) ^ (j - 1)`. -/
@[dlmf 18.16.E20]
theorem laguerrePolyL_discriminant {α : ℝ} (hα : -1 < α) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hinj : Function.Injective x) (hroot : ∀ i, laguerrePolyL α n (x i) = 0) :
    rootDiscriminant ((-1 : ℝ) ^ n / n.factorial) x =
      ∏ j ∈ Finset.Icc 1 n, (j : ℝ) ^ ((j : ℤ) - 2 * n + 2) * (j + α) ^ (j - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  have hC := LagDisc.disc_closed hα m x hroot hinj
  have hL : (∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
      if i.val < j.val then ((x i - x j : ℝ) : ℂ) ^ 2 else (1 : ℂ)) =
      ((∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
        if i.val < j.val then (x i - x j) ^ 2 else (1 : ℝ) : ℝ) : ℂ) := by
    push_cast
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [hL, LagDisc.KL] at hC
  have hCR : ((-1 : ℝ) ^ (m + 1) / ((m + 1)! : ℝ)) ^ (2 * m) *
      (∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
        if i.val < j.val then (x i - x j) ^ 2 else (1 : ℝ)) =
      ∏ k ∈ Finset.range (m + 1), ((k : ℝ) + 1) ^ (k + 1) / ((k : ℝ) + 1) ^ (2 * m) *
        ((k : ℝ) + 1 + α) ^ k := by
    have hR : (∏ k ∈ Finset.range (m + 1), ((k : ℂ) + 1) ^ (k + 1) / ((k : ℂ) + 1) ^ (2 * m) *
        ((k : ℂ) + 1 + α) ^ k) = ((∏ k ∈ Finset.range (m + 1), ((k : ℝ) + 1) ^ (k + 1) /
          ((k : ℝ) + 1) ^ (2 * m) * ((k : ℝ) + 1 + α) ^ k : ℝ) : ℂ) := by
      push_cast; rfl
    have hK : ((-1 : ℂ) ^ (m + 1) / ((m + 1)! : ℂ)) =
        (((-1 : ℝ) ^ (m + 1) / ((m + 1)! : ℝ) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hR, hK, ← Complex.ofReal_pow, ← Complex.ofReal_mul] at hC
    exact Complex.ofReal_injective hC
  unfold rootDiscriminant
  simp only [Fin.lt_def]
  rw [show (2 * ((m + 1 : ℕ) : ℤ) - 2) = ((2 * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast, hCR,
    prod_Icc_one_eq_prod_range]
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hB : ((k : ℝ) + 1) ≠ 0 := by positivity
  rw [show (((k + 1 : ℕ) : ℤ) - 2 * ((m + 1 : ℕ) : ℤ) + 2) =
    ((k + 1 : ℕ) : ℤ) - ((2 * m : ℕ) : ℤ) by push_cast; ring,
    zpow_sub₀ (by push_cast; exact hB), zpow_natCast, zpow_natCast, show k + 1 - 1 = k by omega]
  push_cast
  ring

/-! ### The discriminant of a Hermite polynomial

Schur's route again: `H_{m+2} = -2(m+1) H_m` at the zeros of `H_{m+1}` and
`H_{m+1}' = 2(m+1) H_m`. -/

namespace HerDisc

open Polynomial Finset JacobiDisc

/-- `H_n` has degree at most `n` and leading coefficient `2ⁿ`. -/
theorem coeff_hermitePolyH_self (n : ℕ) :
    (hermitePolyH n).natDegree ≤ n ∧ (hermitePolyH n).coeff n = 2 ^ n := by
  induction n with
  | zero => simp [hermitePolyH_zero]
  | succ n ih =>
    obtain ⟨hd, hc⟩ := ih
    rw [hermitePolyH_succ]
    refine ⟨?_, ?_⟩
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_mul_le).trans ?_
        have : (2 * X : ℤ[X]).natDegree ≤ 1 := by
          refine (natDegree_mul_le).trans ?_
          simp
        omega
      · exact (natDegree_derivative_le _).trans (by omega)
    · have h1 : (derivative (hermitePolyH n)).coeff (n + 1) = 0 := by
        rw [coeff_derivative]
        rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      rw [coeff_sub, h1, sub_zero, mul_assoc, show (2 : ℤ[X]) = C 2 by rfl, coeff_C_mul,
        coeff_X_mul, hc, pow_succ]
      ring

/-- The Hermite polynomial over `ℂ`. -/
def hP (n : ℕ) : ℂ[X] := (hermitePolyH n).map (Int.castRingHom ℂ)

/-- The complex Hermite polynomial `H_n` has degree `n`. -/
theorem natDegree_hP (n : ℕ) : (hP n).natDegree = n := by
  obtain ⟨hd, hc⟩ := coeff_hermitePolyH_self n
  have hne : (hermitePolyH n).natDegree = n :=
    natDegree_eq_of_le_of_coeff_ne_zero hd (by rw [hc]; positivity)
  rw [hP, natDegree_map_eq_of_injective (RingHom.injective_int _), hne]

/-- The leading coefficient of `H_n` is `2ⁿ`. -/
theorem leadingCoeff_hP (n : ℕ) : (hP n).leadingCoeff = 2 ^ n := by
  rw [leadingCoeff, natDegree_hP, hP, coeff_map, (coeff_hermitePolyH_self n).2]
  simp

/-- The complex Hermite polynomial is nonzero. -/
theorem hP_ne_zero (n : ℕ) : hP n ≠ 0 := by
  intro h
  have := leadingCoeff_hP n
  rw [h, leadingCoeff_zero] at this
  exact (pow_ne_zero n two_ne_zero) this.symm

/-- At a real point the complex Hermite polynomial takes the real value of `H_n`. -/
theorem eval_hP_ofReal (n : ℕ) (r : ℝ) :
    (hP n).eval (r : ℂ) = ((aeval r (hermitePolyH n) : ℝ) : ℂ) := by
  rw [hP, eval_map, aeval_def]
  have h := Polynomial.hom_eval₂ (hermitePolyH n) (algebraMap ℤ ℝ) Complex.ofRealHom r
  rw [show Complex.ofRealHom.comp (algebraMap ℤ ℝ) = Int.castRingHom ℂ from
    RingHom.ext_int _ _] at h
  exact h.symm

/-- The Hermite recurrence `H_{n+2} = 2X H_{n+1} - 2(n+1) H_n`. -/
theorem hP_recurrence (n : ℕ) :
    hP (n + 2) = 2 * X * hP (n + 1) - C (2 * (n + 1) : ℂ) * hP n := by
  simp only [hP, hermitePolyH_recurrence, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_ofNat, map_X, map_C]
  simp

/-- `H_{n+1}' = 2(n+1) H_n`. -/
theorem derivative_hP (n : ℕ) : derivative (hP (n + 1)) = C (2 * (n + 1) : ℂ) * hP n := by
  simp only [hP, derivative_map, hermitePolyH_derivative, Polynomial.map_mul, map_C]
  simp

/-- If `x` lists `n` distinct real zeros of `H_n`, they are all its complex roots. -/
theorem roots_hP_eq {n : ℕ} (x : Fin n → ℝ)
    (hroot : ∀ i, (aeval (x i) (hermitePolyH n) : ℝ) = 0) (hinj : Function.Injective x) :
    (hP n).roots = (univ.val.map fun i => (x i : ℂ)) := by
  have hne := hP_ne_zero n
  have hnd : (univ.val.map fun i => (x i : ℂ)).Nodup :=
    Multiset.Nodup.map (fun i j h => hinj (by exact_mod_cast h)) univ.nodup
  have hle : (univ.val.map fun i => (x i : ℂ)) ≤ (hP n).roots := by
    rw [Multiset.le_iff_subset hnd]
    intro y hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hy
    rw [mem_roots hne, IsRoot, eval_hP_ofReal, hroot i, Complex.ofReal_zero]
  refine (Multiset.eq_of_le_of_card_le hle ?_).symm
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_hP, Multiset.card_map,
    card_val, card_univ, Fintype.card_fin]

/-- `H_n = 2ⁿ ∏ (X - xᵢ)` over its `n` distinct real zeros. -/
theorem hP_eq_nodal {n : ℕ} (x : Fin n → ℝ)
    (hroot : ∀ i, (aeval (x i) (hermitePolyH n) : ℝ) = 0) (hinj : Function.Injective x) :
    hP n = C (2 ^ n) * Lagrange.nodal univ fun i => (x i : ℂ) := by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := hP n))]
  rw [leadingCoeff_hP, roots_hP_eq x hroot hinj, Multiset.map_map]
  rfl

/-- `∏ H_m(y)` over the zeros `y` of `H_{m+1}`. -/
def SSH (m : ℕ) : ℂ := ((hP (m + 1)).roots.map fun y => (hP m).eval y).prod

/-- `SSH 0 = 1`. -/
theorem SSH_zero : SSH 0 = 1 := by
  simp [SSH, hP, hermitePolyH_zero]

/-- The recursion for the product of `H_m` over the zeros of `H_{m+1}`. -/
theorem SSH_succ (m : ℕ) : SSH (m + 1) = (-(2 * ((m : ℂ) + 1))) ^ (m + 1) * SSH m := by
  have key := lc_pow_mul_prod_roots_eval (hP (m + 2)) (hP (m + 1))
  rw [natDegree_hP, natDegree_hP, leadingCoeff_hP, leadingCoeff_hP] at key
  have hne := hP_ne_zero (m + 1)
  have hmap : ((hP (m + 1)).roots.map fun y => (hP (m + 2)).eval y) =
      ((hP (m + 1)).roots.map fun y => (-(2 * ((m : ℂ) + 1))) * (hP m).eval y) := by
    refine Multiset.map_congr rfl fun y hy => ?_
    have h0 := (mem_roots hne).mp hy
    rw [IsRoot] at h0
    rw [hP_recurrence, eval_sub, eval_mul, h0, mul_zero, zero_sub, eval_mul, eval_C]
    ring
  rw [hmap, prod_map_const_mul, IsAlgClosed.card_roots_eq_natDegree, natDegree_hP] at key
  change ((2 : ℂ) ^ (m + 2)) ^ (m + 1) * SSH (m + 1) = _ * (_ * SSH m) at key
  have he : Even ((m + 2) * (m + 1)) := by
    rw [mul_comm]; exact Nat.even_mul_succ_self (m + 1)
  rw [he.neg_one_pow, one_mul, ← pow_mul, ← pow_mul, mul_comm (m + 1) (m + 2)] at key
  exact mul_left_cancel₀ (pow_ne_zero _ two_ne_zero) key

/-- Closed form of the product of `H_m` over the zeros of `H_{m+1}`. -/
theorem SSH_eq (m : ℕ) : SSH m = ∏ k ∈ range m, (-(2 * ((k : ℂ) + 1))) ^ (k + 1) := by
  induction m with
  | zero => simp [SSH_zero]
  | succ m ih => rw [SSH_succ, ih, prod_range_succ]; ring

/-- The Hermite discriminant expressed through `SSH`. -/
theorem disc_eq (m : ℕ) (x : Fin (m + 1) → ℝ)
    (hroot : ∀ i, (aeval (x i) (hermitePolyH (m + 1)) : ℝ) = 0) (hinj : Function.Injective x) :
    (∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
      if i.val < j.val then ((x i - x j : ℝ) : ℂ) ^ 2 else 1) * (2 ^ (m + 1)) ^ (m + 1) =
      (-1) ^ (m + 1).choose 2 * (2 * ((m : ℂ) + 1)) ^ (m + 1) * SSH m := by
  set xc : Fin (m + 1) → ℂ := fun i => (x i : ℂ) with hxc
  have hnodal := hP_eq_nodal x hroot hinj
  have hder : ∀ i, (2 : ℂ) ^ (m + 1) * ∏ j ∈ univ.erase i, (xc i - xc j) =
      2 * ((m : ℂ) + 1) * (hP m).eval (xc i) := by
    intro i
    have h := congrArg (fun p => (derivative p).eval (xc i)) hnodal
    rw [derivative_hP, derivative_C_mul, eval_mul, eval_mul, eval_C, eval_C,
      Lagrange.eval_nodal_derivative_eval_node_eq (mem_univ i), Lagrange.eval_nodal] at h
    rw [h]
  have hprod := congrArg (fun f : Fin (m + 1) → ℂ => ∏ i, f i) (funext hder)
  simp only [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin] at hprod
  have hSS : ∏ i, (hP m).eval (xc i) = SSH m := by
    unfold SSH
    rw [roots_hP_eq x hroot hinj, Multiset.map_map]
    rfl
  have hpair := prod_prod_erase_sub xc
  have hLHS : (∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
      if i.val < j.val then ((x i - x j : ℝ) : ℂ) ^ 2 else 1) =
      ∏ i, ∏ j, (if i.val < j.val then (xc i - xc j) ^ 2 else 1) := by
    simp [hxc]
  rw [hLHS]
  rw [hSS, hpair] at hprod
  have hσ : ((-1 : ℂ) ^ (m + 1).choose 2) * (-1) ^ (m + 1).choose 2 = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  rw [mul_pow]
  linear_combination ((-1 : ℂ) ^ (m + 1).choose 2) * hprod -
    ((∏ i, ∏ j, (if i.val < j.val then (xc i - xc j) ^ 2 else (1 : ℂ))) *
      ((2 : ℂ) ^ (m + 1)) ^ (m + 1)) * hσ

/-- `∑_{k<m} (k+1) = C(m+1, 2)`. -/
theorem sum_range_succ_eq_choose (m : ℕ) : ∑ k ∈ range m, (k + 1) = (m + 1).choose 2 := by
  rw [Nat.choose_two_right, ← Finset.sum_range_id (m + 1), Finset.sum_range_succ']
  simp

/-- Closed form of the discriminant of the Hermite polynomial `H_{m+1}` (Stieltjes). -/
theorem disc_closed (m : ℕ) (x : Fin (m + 1) → ℝ)
    (hroot : ∀ i, (aeval (x i) (hermitePolyH (m + 1)) : ℝ) = 0) (hinj : Function.Injective x) :
    ((2 : ℂ) ^ (m + 1)) ^ (2 * m) * (∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
      if i.val < j.val then ((x i - x j : ℝ) : ℂ) ^ 2 else 1) =
      (2 : ℂ) ^ (3 * (m + 1).choose 2) * ∏ k ∈ range (m + 1), ((k : ℂ) + 1) ^ (k + 1) := by
  have hD := disc_eq m x hroot hinj
  generalize (∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
      if i.val < j.val then ((x i - x j : ℝ) : ℂ) ^ 2 else 1) = D at hD ⊢
  have hS : SSH m = (-1) ^ (m + 1).choose 2 * 2 ^ (m + 1).choose 2 *
      ∏ k ∈ range m, ((k : ℂ) + 1) ^ (k + 1) := by
    rw [SSH_eq]
    have : ∀ k ∈ range m, (-(2 * ((k : ℂ) + 1))) ^ (k + 1) =
        (-1) ^ (k + 1) * 2 ^ (k + 1) * ((k : ℂ) + 1) ^ (k + 1) := fun k _ => by
      rw [neg_eq_neg_one_mul, mul_pow, mul_pow]; ring
    rw [prod_congr rfl this, prod_mul_distrib, prod_mul_distrib, prod_pow_eq_pow_sum,
      prod_pow_eq_pow_sum, sum_range_succ_eq_choose]
  rw [hS] at hD
  set C2 := (m + 1).choose 2 with hC2
  have hC : 2 * C2 = (m + 1) * m := by
    rw [hC2, Nat.choose_two_right]
    exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (m + 1))
  have hσ : ((-1 : ℂ) ^ C2) * (-1) ^ C2 = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hprod : ∏ k ∈ range (m + 1), ((k : ℂ) + 1) ^ (k + 1) =
      (∏ k ∈ range m, ((k : ℂ) + 1) ^ (k + 1)) * ((m : ℂ) + 1) ^ (m + 1) := prod_range_succ _ _
  rw [hprod]
  have hexp : (m + 1) * (2 * m) + (m + 1) + C2 = 3 * C2 + (m + 1) * (m + 1) := by
    nlinarith [hC]
  have h2 : ((2 : ℂ) ^ (m + 1)) ^ (2 * m) * 2 ^ (m + 1) * 2 ^ C2 =
      2 ^ (3 * C2) * ((2 : ℂ) ^ (m + 1)) ^ (m + 1) := by
    simp only [← pow_mul, ← pow_add, hexp]
  have h2N : ((2 : ℂ) ^ (m + 1)) ^ (m + 1) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ two_ne_zero)
  set P := ∏ k ∈ range m, ((k : ℂ) + 1) ^ (k + 1)
  have hD' : D * ((2 : ℂ) ^ (m + 1)) ^ (m + 1) =
      2 ^ (m + 1) * 2 ^ C2 * (((m : ℂ) + 1) ^ (m + 1) * P) := by
    rw [hD, mul_pow]
    linear_combination ((2 : ℂ) ^ (m + 1) * ((m : ℂ) + 1) ^ (m + 1) * 2 ^ C2 * P) * hσ
  apply mul_right_cancel₀ h2N
  calc ((2 : ℂ) ^ (m + 1)) ^ (2 * m) * D * ((2 : ℂ) ^ (m + 1)) ^ (m + 1)
      = ((2 : ℂ) ^ (m + 1)) ^ (2 * m) * (D * ((2 : ℂ) ^ (m + 1)) ^ (m + 1)) := by ring
    _ = ((2 : ℂ) ^ (m + 1)) ^ (2 * m) * 2 ^ (m + 1) * 2 ^ C2 *
        (((m : ℂ) + 1) ^ (m + 1) * P) := by rw [hD']; ring
    _ = 2 ^ (3 * C2) * ((2 : ℂ) ^ (m + 1)) ^ (m + 1) * (((m : ℂ) + 1) ^ (m + 1) * P) := by
        rw [h2]
    _ = _ := by ring

end HerDisc

/-- Formula under the stated hypotheses: `rootDiscriminant (2 ^ n) x = (2 : ℝ) ^ (3 * n * (n - 1)
/ 2) * ∏ j ∈ Finset.Icc 1 n, (j : ℝ) ^ j`. -/
@[dlmf 18.16.E21]
theorem hermitePolyH_discriminant {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hinj : Function.Injective x)
    (hroot : ∀ i, (aeval (x i) (hermitePolyH n) : ℝ) = 0) :
    rootDiscriminant (2 ^ n) x = (2 : ℝ) ^ (3 * n * (n - 1) / 2) *
      ∏ j ∈ Finset.Icc 1 n, (j : ℝ) ^ j := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  have hC := HerDisc.disc_closed m x hroot hinj
  have hL : (∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
      if i.val < j.val then ((x i - x j : ℝ) : ℂ) ^ 2 else (1 : ℂ)) =
      ((∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
        if i.val < j.val then (x i - x j) ^ 2 else (1 : ℝ) : ℝ) : ℂ) := by
    push_cast
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hR : (2 : ℂ) ^ (3 * (m + 1).choose 2) *
      ∏ k ∈ Finset.range (m + 1), ((k : ℂ) + 1) ^ (k + 1) =
      (((2 : ℝ) ^ (3 * (m + 1).choose 2) *
        ∏ k ∈ Finset.range (m + 1), ((k : ℝ) + 1) ^ (k + 1) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hL, hR, show ((2 : ℂ) ^ (m + 1)) ^ (2 * m) = (((2 : ℝ) ^ (m + 1)) ^ (2 * m) : ℝ) by
    push_cast; rfl, ← Complex.ofReal_mul] at hC
  have hCR := Complex.ofReal_injective hC
  have hexp : 3 * (m + 1) * (m + 1 - 1) / 2 = 3 * (m + 1).choose 2 := by
    rw [Nat.choose_two_right, mul_assoc,
      Nat.mul_div_assoc 3 (Nat.even_mul_pred_self (m + 1)).two_dvd]
  unfold rootDiscriminant
  simp only [Fin.lt_def]
  rw [show (2 * ((m + 1 : ℕ) : ℤ) - 2) = ((2 * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast, hCR,
    hexp, prod_Icc_one_eq_prod_range]
  push_cast
  rfl

end DLMF.OrthogonalPolynomials

end
end
