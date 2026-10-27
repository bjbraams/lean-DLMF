/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Polynomials.Defs
public import Mathlib.Analysis.Matrix.Spectrum
public import DLMF.JacobiElliptic.PeriodsPolesZeros

/-!
# Lamé polynomials: the matrix eigenvalues, polynomial form, periods and parities

Moved below `DLMF.Lame.Polynomials.Series` (unchanged) so that the proofs that the Lamé
polynomials solve Lamé's equation (`DLMF.Lame.Polynomials.P2pODE`) can use them and in turn
be used in `Series`. Contents:

* 29.15.3: the eigenvalues of the tridiagonal matrix 29.15.2 are real and simple
  (`lamePolyH_strictMono`), by symmetrization and Mathlib's spectral theorem;
* Table 29.12.1: polynomial form (`lamePolyEk_polynomial_form`), periods
  (`lamePolyEk_periods`) and parities (`lamePolyEk_parities`) of the Lamé polynomials.
-/

@[expose] public section

open Complex DLMF.JacobiElliptic DLMF.Elliptic Polynomial Set
open scoped Real

noncomputable section

namespace DLMF.Lame

variable {k : ℝ}

/-! ### The matrix eigenvalues (29.15.3) -/

section p2pTridiag

open Matrix

/-- The tridiagonal matrix with `a p` above, `b p` on and `c p` below the diagonal in row `p`
(the shape of 29.15.2). -/
def p2p_tridiag (a b c : ℕ → ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    if (j : ℕ) = i + 1 then a i
    else if (j : ℕ) = i then b i
    else if (j : ℕ) + 1 = i then c i
    else 0

/-- The diagonal symmetrizer `d₀ = 1`, `d_{p+1} = d_p √(a_p / c_{p+1})` of a tridiagonal matrix. -/
def p2p_symD (a c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | p + 1 => p2p_symD a c p * Real.sqrt (a p / c (p + 1))

lemma p2p_symD_pos {a c : ℕ → ℝ} {n : ℕ} (h : ∀ p < n, 0 < a p * c (p + 1)) :
    ∀ p ≤ n, 0 < p2p_symD a c p := by
  intro p hp
  induction p with
  | zero => simp [p2p_symD]
  | succ p ih =>
    have h1 := h p (by omega)
    have hc : c (p + 1) ≠ 0 := by rintro h0; simp [h0] at h1
    have : 0 < a p / c (p + 1) := by
      rw [show a p / c (p + 1) = a p * c (p + 1) / c (p + 1) ^ 2 by field_simp]
      exact div_pos h1 (by positivity)
    exact mul_pos (ih (by omega)) (Real.sqrt_pos.mpr this)

/-- The symmetrized tridiagonal matrix. -/
def p2p_tridiagSym (a b c : ℕ → ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  diagonal (fun i : Fin (n + 1) => p2p_symD a c i) * p2p_tridiag a b c n *
    diagonal (fun i : Fin (n + 1) => (p2p_symD a c i)⁻¹)

lemma p2p_tridiagSym_apply (a b c : ℕ → ℝ) (n : ℕ) (i j : Fin (n + 1)) :
    p2p_tridiagSym a b c n i j =
      p2p_symD a c i * p2p_tridiag a b c n i j * (p2p_symD a c j)⁻¹ := by
  simp [p2p_tridiagSym, mul_diagonal, diagonal_mul]

lemma p2p_charpoly_tridiagSym {a b c : ℕ → ℝ} {n : ℕ} (h : ∀ p < n, 0 < a p * c (p + 1)) :
    (p2p_tridiagSym a b c n).charpoly = (p2p_tridiag a b c n).charpoly := by
  rw [p2p_tridiagSym, charpoly_mul_comm, ← mul_assoc, diagonal_mul_diagonal]
  congr 1
  convert one_mul _
  rw [← diagonal_one]
  congr 1
  funext i
  exact inv_mul_cancel₀ (p2p_symD_pos h i (by omega)).ne'

lemma p2p_tridiagSym_isHermitian {a b c : ℕ → ℝ} {n : ℕ} (h : ∀ p < n, 0 < a p * c (p + 1)) :
    (p2p_tridiagSym a b c n).IsHermitian := by
  refine IsHermitian.ext fun i j => ?_
  simp only [star_trivial, p2p_tridiagSym_apply, p2p_tridiag, of_apply]
  have hd := p2p_symD_pos h
  have key : ∀ p < n, p2p_symD a c p * a p * (p2p_symD a c (p + 1))⁻¹ =
      p2p_symD a c (p + 1) * c (p + 1) * (p2p_symD a c p)⁻¹ := by
    intro p hp
    have h1 := h p hp
    have hc : c (p + 1) ≠ 0 := by rintro h0; simp [h0] at h1
    have hpos : 0 ≤ a p / c (p + 1) := by
      rw [show a p / c (p + 1) = a p * c (p + 1) / c (p + 1) ^ 2 by field_simp]
      positivity
    have h0 := hd p (by omega)
    have h1' := hd (p + 1) (by omega)
    have hsq : p2p_symD a c (p + 1) ^ 2 = p2p_symD a c p ^ 2 * (a p / c (p + 1)) := by
      rw [p2p_symD, mul_pow, Real.sq_sqrt hpos]
    rw [div_eq_mul_inv] at hsq
    field_simp
    have := congrArg (· * c (p + 1)) hsq
    simp only [mul_assoc, inv_mul_cancel₀ hc, mul_one] at this
    linear_combination -this
  have hi := i.isLt
  have hj := j.isLt
  by_cases h1 : (i : ℕ) = j + 1
  · simp only [h1, show ¬ (j : ℕ) = j + 1 + 1 by omega, show ¬ (j : ℕ) = j + 1 by omega,
      ite_true, ite_false]
    rw [key j (by omega)]
  by_cases h2 : (j : ℕ) = i + 1
  · simp only [h2, show ¬ (i : ℕ) = i + 1 + 1 by omega, show ¬ (i : ℕ) = i + 1 by omega,
      ite_true, ite_false]
    rw [key i (by omega)]
  by_cases h3 : (i : ℕ) = j
  · rw [Fin.ext h3]
  · simp [h1, h2, h3, Ne.symm h3, show ¬ (i : ℕ) + 1 = j by omega,
      show ¬ (j : ℕ) + 1 = i by omega]

/-- An eigenvector of a matrix that vanishes above the superdiagonal and has nonzero
superdiagonal entries is zero if its first entry is zero. -/
theorem p2p_eigvec_zero_of_head {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA0 : ∀ i j : Fin (n + 1), (i : ℕ) + 1 < j → A i j = 0)
    (hA1 : ∀ i j : Fin (n + 1), (j : ℕ) = i + 1 → A i j ≠ 0) {v : Fin (n + 1) → ℝ} {μ : ℝ}
    (hv : A *ᵥ v = μ • v) (h0 : v 0 = 0) : v = 0 := by
  have key : ∀ p : ℕ, ∀ hp : p < n + 1, v ⟨p, hp⟩ = 0 := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro hp
      rcases p with _ | q
      · exact h0
      · have hq : q < n + 1 := by omega
        have hrow := congrFun hv ⟨q, hq⟩
        rw [mulVec, dotProduct, Pi.smul_apply, ih q (by omega) hq, smul_zero,
          Finset.sum_eq_single (⟨q + 1, hp⟩ : Fin (n + 1))] at hrow
        · exact (mul_eq_zero.mp hrow).resolve_left (hA1 _ _ rfl)
        · intro j _ hj
          by_cases hjq : (j : ℕ) ≤ q
          · rw [show v j = 0 from ih j (by omega) j.isLt, mul_zero]
          · rw [hA0 _ _ (by simp only; have : (j : ℕ) ≠ q + 1 := fun h => hj (Fin.ext h); omega),
              zero_mul]
        · simp
  funext i
  exact key i i.isLt

/-- The tridiagonal matrix with `0 < a p * c (p+1)` for `p < n` has `n + 1` distinct real
eigenvalues. -/
lemma p2p_tridiag_roots {a b c : ℕ → ℝ} {n : ℕ} (h : ∀ p < n, 0 < a p * c (p + 1)) :
    (p2p_tridiag a b c n).charpoly.roots.card = n + 1 ∧
      (p2p_tridiag a b c n).charpoly.roots.Nodup := by
  have hS := p2p_tridiagSym_isHermitian (b := b) h
  rw [← p2p_charpoly_tridiagSym h, hS.roots_charpoly_eq_eigenvalues]
  refine ⟨by simp, ?_⟩
  refine Multiset.Nodup.map (Function.Injective.comp (fun x y hxy => by simpa using hxy) ?_)
    Finset.univ.nodup
  have hA0 : ∀ i j : Fin (n + 1), (i : ℕ) + 1 < j → p2p_tridiagSym a b c n i j = 0 := by
    intro i j hij
    simp [p2p_tridiagSym_apply, p2p_tridiag, show ¬ (j : ℕ) = i + 1 by omega,
      show ¬ (j : ℕ) = i by omega, show ¬ (j : ℕ) + 1 = i by omega]
  have hA1 : ∀ i j : Fin (n + 1), (j : ℕ) = i + 1 → p2p_tridiagSym a b c n i j ≠ 0 := by
    intro i j hij
    have hd := p2p_symD_pos h
    have ha : a i ≠ 0 := by
      have := h i (by omega); rintro h0; simp [h0] at this
    simp only [p2p_tridiagSym_apply, p2p_tridiag, of_apply, hij, ite_true]
    exact mul_ne_zero (mul_ne_zero (hd i (by omega)).ne' ha)
      (inv_ne_zero (hd (i + 1) (by omega)).ne')
  intro i j hij
  by_contra hne
  set B := hS.eigenvectorBasis
  have hon := B.orthonormal
  have hev : ∀ l, p2p_tridiagSym a b c n *ᵥ ⇑(B l) = hS.eigenvalues l • ⇑(B l) :=
    hS.mulVec_eigenvectorBasis
  set w : EuclideanSpace ℝ (Fin (n + 1)) := (B j) 0 • B i - (B i) 0 • B j
  have hw : p2p_tridiagSym a b c n *ᵥ ⇑w = hS.eigenvalues i • ⇑w := by
    simp only [w, WithLp.ofLp_sub, WithLp.ofLp_smul, mulVec_sub, mulVec_smul, hev, hij]
    module
  have hw0 : w = 0 := by
    have := p2p_eigvec_zero_of_head hA0 hA1 hw (by simp [w]; ring)
    exact WithLp.ofLp_injective _ (by simpa using this)
  have hin : inner ℝ (B i) w = (B j) 0 := by
    simp only [w, inner_sub_right, inner_smul_right, hon.inner_eq_zero hne,
      real_inner_self_eq_norm_sq, hon.1 i]
    ring
  rw [hw0, inner_zero_right] at hin
  have hBj := p2p_eigvec_zero_of_head hA0 hA1 (hev j) hin.symm
  have : B j = 0 := WithLp.ofLp_injective _ (by simpa using hBj)
  have h1 := hon.1 j
  rw [this, norm_zero] at h1
  exact zero_ne_one h1

end p2pTridiag

/-- The products `α_p γ_{p+1}`, `p < n`, of the matrix 29.15.2 are positive for all eight types. -/
theorem p2p_alpha_gamma_pos {k : ℝ} (hk0 : 0 < k) (t : LamePolyType) (n : ℕ) :
    ∀ p < n, 0 < t.recurrence.alpha (t.order n) k p *
      t.recurrence.gamma (t.order n) k (p + 1) := by
  intro p hp
  have hp' : (p : ℝ) + 1 ≤ n := by exact_mod_cast hp
  have hk2 : 0 < k ^ 2 := by positivity
  cases t <;> simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.alpha,
    LameRecurrence.gamma] <;> push_cast <;> (try split_ifs) <;>
    apply_rules [mul_pos, div_pos] <;> norm_num <;> nlinarith


/-- 29.15.3: the eigenvalues of the tridiagonal matrix 29.15.2 (for any of the eight types)
are real and simple, `H₀ < H₁ < ⋯ < Hₙ`: the characteristic polynomial has `n + 1` distinct
real roots, and `lamePolyH` lists them increasingly. Proved by symmetrizing the matrix
(`α_p γ_{p+1} > 0`) and the spectral theorem. -/
@[dlmf 29.15.E3]
theorem lamePolyH_strictMono (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType) (n : ℕ) :
    (lameMatrix t.recurrence (t.order n) k n).charpoly.roots.card = n + 1 ∧
      (lameMatrix t.recurrence (t.order n) k n).charpoly.roots.Nodup ∧
      ∀ m < n, lamePolyH t n m k < lamePolyH t n (m + 1) k := by
  have _ := hk1
  obtain ⟨hc, hn⟩ := p2p_tridiag_roots (b := t.recurrence.beta (t.order n) k)
    (p2p_alpha_gamma_pos hk0 t n)
  refine ⟨hc, hn, fun m hm => ?_⟩
  set L := (lameMatrix t.recurrence (t.order n) k n).charpoly.roots.sort (· ≤ ·) with hL
  have hlen : L.length = n + 1 := by rw [hL, Multiset.length_sort]; exact hc
  have hpw : L.Pairwise (· < ·) := by
    have h1 : L.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
    have h2 : L.Nodup := by
      rw [hL]; exact (Multiset.coe_nodup.mp (by rw [Multiset.sort_eq]; exact hn))
    exact (h1.and h2).imp fun h => lt_of_le_of_ne h.1 h.2
  simp only [lamePolyH, lameMatrixEigenvalue]
  rw [← hL, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  exact List.pairwise_iff_getElem.mp hpw m (m + 1) (by omega) (by omega) (by omega)


/-! ### Polynomial form, periods and parities (Table 29.12.1) -/

section p2pPolyForm

open Matrix

/-- Extension by zero of a vector on `Fin (n + 1)` to `ℕ`. -/
def p2p_ext {n : ℕ} (u : Fin (n + 1) → ℝ) (q : ℕ) : ℝ :=
  if h : q < n + 1 then u ⟨q, h⟩ else 0

theorem p2p_row (a b c : ℕ → ℝ) {n : ℕ} (u : Fin (n + 1) → ℝ) {p : ℕ} (hp : p < n + 1) :
    (p2p_tridiag a b c n *ᵥ u) ⟨p, hp⟩ =
      a p * p2p_ext u (p + 1) + b p * p2p_ext u p +
        (if p = 0 then 0 else c p * p2p_ext u (p - 1)) := by
  set f : ℕ → ℝ := fun q =>
    (if q = p + 1 then a p else if q = p then b p else if q + 1 = p then c p else 0) *
      p2p_ext u q with hf
  have e : (p2p_tridiag a b c n *ᵥ u) ⟨p, hp⟩ = ∑ i : Fin (n + 1), f i := by
    rw [mulVec, dotProduct]
    exact Finset.sum_congr rfl fun q _ => by
      simp [hf, p2p_ext, p2p_tridiag]
      intro h; exact absurd q.isLt (by omega)
  rw [e, Fin.sum_univ_eq_sum_range f, hf]
  · have : ∀ q, (if q = p + 1 then a p else if q = p then b p else if q + 1 = p then c p else 0) *
        p2p_ext u q = (if q = p + 1 then a p * p2p_ext u q else 0) +
          (if q = p then b p * p2p_ext u q else 0) +
          (if p ≠ 0 ∧ q = p - 1 then c p * p2p_ext u q else 0) := by
      intro q
      split_ifs <;> first | (exfalso; omega) | ring1
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
    by_cases hp0 : p = 0
    · subst hp0
      by_cases h1 : 1 < n + 1
      · simp [h1]
      · simp [h1, p2p_ext]
    · have hq : ∀ q, (p ≠ 0 ∧ q = p - 1) ↔ q = p - 1 := fun q => by tauto
      simp only [hq, Finset.sum_ite_eq', Finset.mem_range, hp0, ite_false, hp,
        show p - 1 < n + 1 by omega, ite_true]
      by_cases h1 : p + 1 < n + 1
      · simp [h1]
      · simp [h1, p2p_ext]

theorem p2p_lameRecVec_succ (r : LameRecurrence) (ν k H : ℝ) (p : ℕ) :
    lameRecVec r ν k H (p + 1) = ((H - r.beta ν k p) * lameRecVec r ν k H p -
      r.gamma ν k p * (if p = 0 then 0 else lameRecVec r ν k H (p - 1))) / r.alpha ν k p := by
  rcases p with _ | p
  · simp [lameRecVec, lameRecVecPair]
  · simp [lameRecVec, lameRecVecPair]

theorem p2p_lameRecVec_zero (r : LameRecurrence) (ν k H : ℝ) : lameRecVec r ν k H 0 = 1 := rfl

/-- If `H` is an eigenvalue of the matrix 29.15.2 (with `α_p γ_{p+1} > 0`), the forward
recursion gives an eigenvector with nonzero last entry `v_n`. -/
lemma p2p_lameRecVec_last_ne_zero {r : LameRecurrence} {ν k H : ℝ} {n : ℕ}
    (hpos : ∀ p < n, 0 < r.alpha ν k p * r.gamma ν k (p + 1))
    (hH : (lameMatrix r ν k n).charpoly.eval H = 0) : lameRecVec r ν k H n ≠ 0 := by
  rw [eval_charpoly, ← exists_mulVec_eq_zero_iff] at hH
  obtain ⟨u, hu0, hu⟩ := hH
  have hMu : lameMatrix r ν k n *ᵥ u = H • u := by
    rw [sub_mulVec, sub_eq_zero, scalar_apply] at hu
    rw [← hu]; funext i; simp [mulVec_diagonal]
  set U := p2p_ext u with hU
  have hα : ∀ p < n, r.alpha ν k p ≠ 0 := fun p hp h0 => by
    have := hpos p hp; rw [h0, zero_mul] at this; exact lt_irrefl _ this
  have hγ : ∀ p < n, r.gamma ν k (p + 1) ≠ 0 := fun p hp h0 => by
    have := hpos p hp; rw [h0, mul_zero] at this; exact lt_irrefl _ this
  have hrow : ∀ p ≤ n, r.alpha ν k p * U (p + 1) + r.beta ν k p * U p +
      (if p = 0 then 0 else r.gamma ν k p * U (p - 1)) = H * U p := by
    intro p hp
    have h1 := congrFun hMu ⟨p, by omega⟩
    have h2 := p2p_row (r.alpha ν k) (r.beta ν k) (r.gamma ν k) u (p := p) (by omega)
    rw [show lameMatrix r ν k n = p2p_tridiag (r.alpha ν k) (r.beta ν k) (r.gamma ν k) n
      from rfl, h2] at h1
    rw [h1]
    simp [hU, p2p_ext, show p < n + 1 by omega]
  have hUgt : ∀ q, n < q → U q = 0 := fun q hq => by simp [hU, p2p_ext, show ¬ q < n + 1 by omega]
  -- the first entry is nonzero
  have hU0 : U 0 ≠ 0 := by
    intro h0
    refine hu0 (p2p_eigvec_zero_of_head (A := lameMatrix r ν k n) (μ := H) ?_ ?_ hMu ?_)
    · intro i j hij
      simp [lameMatrix, show ¬ (j : ℕ) = i + 1 by omega, show ¬ (j : ℕ) = i by omega,
        show ¬ (j : ℕ) + 1 = i by omega]
    · intro i j hij
      simp only [lameMatrix, of_apply, hij, ite_true]
      exact hα i (by omega)
    · simpa [hU, p2p_ext] using h0
  -- forward recursion
  have hfw : ∀ p ≤ n, U p = U 0 * lameRecVec r ν k H p := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro hp
      rcases p with _ | p
      · rw [p2p_lameRecVec_zero, mul_one]
      · have hr := hrow p (by omega)
        rw [p2p_lameRecVec_succ]
        rw [ih p (by omega) (by omega)] at hr
        have hap := hα p (by omega)
        rw [eq_comm, mul_div_assoc', div_eq_iff hap]
        rcases p with _ | p
        · simp only [ite_true] at hr ⊢
          linear_combination -hr
        · simp only [show p + 1 ≠ 0 by omega, ite_false, show p + 1 - 1 = p by omega] at hr ⊢
          rw [ih p (by omega) (by omega)] at hr
          linear_combination -hr
  -- backward recursion
  intro hvn
  have hbw : ∀ d ≤ n, ∀ q, n - d ≤ q → U q = 0 := by
    intro d
    induction d with
    | zero =>
      intro _ q hq
      rcases Nat.lt_or_ge n q with h | h
      · exact hUgt q h
      · rw [show q = n by omega, hfw n le_rfl, hvn, mul_zero]
    | succ d ih =>
      intro hd q hq
      rcases Nat.lt_or_ge q (n - d) with h | h
      · have hq' : q = n - d - 1 := by omega
        have hr := hrow (n - d) (by omega)
        rw [ih (by omega) (n - d) le_rfl, ih (by omega) (n - d + 1) (by omega)] at hr
        simp only [show n - d ≠ 0 by omega, ite_false] at hr
        have hg := hγ (n - d - 1) (by omega)
        rw [show n - d - 1 + 1 = n - d by omega] at hg
        rw [hq']
        have : r.gamma ν k (n - d) * U (n - d - 1) = 0 := by linear_combination hr
        exact (mul_eq_zero.mp this).resolve_left hg
      · exact ih (by omega) q h
  exact hU0 (hbw n le_rfl 0 (by omega))

/-- The eigenvalue `H_m` (`m ≤ n`) is a root of the characteristic polynomial of 29.15.2. -/
theorem p2p_lamePolyH_eval {k : ℝ} (hk0 : 0 < k) (t : LamePolyType) {n m : ℕ} (hm : m ≤ n) :
    (lameMatrix t.recurrence (t.order n) k n).charpoly.eval (lamePolyH t n m k) = 0 := by
  obtain ⟨hc, -⟩ := p2p_tridiag_roots (b := t.recurrence.beta (t.order n) k)
    (p2p_alpha_gamma_pos hk0 t n)
  set L := (lameMatrix t.recurrence (t.order n) k n).charpoly.roots.sort (· ≤ ·) with hL
  have hlen : L.length = n + 1 := by rw [hL, Multiset.length_sort]; exact hc
  have hmem : lamePolyH t n m k ∈ L := by
    simp only [lamePolyH, lameMatrixEigenvalue]
    rw [← hL, List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  rw [hL, Multiset.mem_sort] at hmem
  exact (isRoot_of_mem_roots hmem)

/-- `∑_{p ≤ n} c_p² - c₀²/2 - ∑_{p < n} c_p c_{p+1} = ½ ∑_{p<n} (c_p - c_{p+1})² + ½ c_n²`. -/
lemma p2p_sq_sub_cross (c : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ Finset.range (n + 1), c p ^ 2 - c 0 ^ 2 / 2 - ∑ p ∈ Finset.range n, c p * c (p + 1) =
      (∑ p ∈ Finset.range n, (c p - c (p + 1)) ^ 2) / 2 + c n ^ 2 / 2 := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun p => c p * c (p + 1)),
      Finset.sum_range_succ (fun p => (c p - c (p + 1)) ^ 2)]
    linear_combination ih

/-- The normalization forms 29.15.5, … are positive at a vector with `c₀ = 1`. -/
lemma p2p_normForm_pos {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType) (n : ℕ)
    {c : ℕ → ℝ} (hc : c 0 = 1) : 0 < t.normForm k n c := by
  have hid := p2p_sq_sub_cross c n
  have hnn : 0 ≤ (∑ p ∈ Finset.range n, (c p - c (p + 1)) ^ 2) / 2 + c n ^ 2 / 2 := by
    positivity
  have hsq : c 0 ^ 2 ≤ ∑ p ∈ Finset.range (n + 1), c p ^ 2 :=
    Finset.single_le_sum (f := fun p => c p ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_range.mpr (Nat.succ_pos n))
  rw [hc] at hsq hid
  have hk2 : 0 < k ^ 2 := by positivity
  have hk2' : k ^ 2 < 1 := by nlinarith
  set sq := ∑ p ∈ Finset.range (n + 1), c p ^ 2
  set cr := ∑ p ∈ Finset.range n, c p * c (p + 1)
  have h1 : 0 ≤ k ^ 2 * (sq - 1 / 2 - cr) := mul_nonneg hk2.le (by linarith)
  have h2 : 0 < (1 - k ^ 2) * (sq - 1 / 2) := mul_pos (by linarith) (by linarith)
  cases t <;> simp only [LamePolyType.normForm, hc] <;> nlinarith

/-- Even and odd parts `(E_p, O_p)` of the Chebyshev-type sequence with
`f₀ = e`, `f₁ = o X`, `f_{j+2} = 2X f_{j+1} - f_j`: `f_{2p}(s) = E_p(s²)`,
`f_{2p+1}(s) = s O_p(s²)`. -/
def p2p_chebPair (e o : ℝ) : ℕ → ℝ[X] × ℝ[X]
  | 0 => (C e, C o)
  | p + 1 =>
    (2 * X * (p2p_chebPair e o p).2 - (p2p_chebPair e o p).1,
      2 * (2 * X * (p2p_chebPair e o p).2 - (p2p_chebPair e o p).1) - (p2p_chebPair e o p).2)

lemma p2p_chebPair_degree {e o : ℝ} (he : e ≠ 0) (ho : o ≠ 0) (p : ℕ) :
    (p2p_chebPair e o p).1.degree = p ∧ (p2p_chebPair e o p).2.degree = p := by
  have h2X : ∀ q : ℝ[X], (2 * X * q).degree = q.degree + 1 := fun q => by
    rw [degree_mul, degree_mul, degree_X, (map_ofNat C 2).symm, degree_C (by norm_num),
      zero_add, add_comm]
  have h2 : ∀ q : ℝ[X], (2 * q).degree = q.degree := fun q => by
    rw [degree_mul, (map_ofNat C 2).symm, degree_C (by norm_num), zero_add]
  induction p with
  | zero => simp [p2p_chebPair, degree_C he, degree_C ho]
  | succ p ih =>
    have hlt : ((p : ℕ) : WithBot ℕ) < ((p + 1 : ℕ) : WithBot ℕ) := by
      exact_mod_cast Nat.lt_succ_self p
    have h1 : (2 * X * (p2p_chebPair e o p).2 - (p2p_chebPair e o p).1).degree =
        ((p + 1 : ℕ) : WithBot ℕ) := by
      rw [degree_sub_eq_left_of_degree_lt (by rw [h2X, ih.1, ih.2]; exact_mod_cast hlt), h2X,
        ih.2]
      rfl
    simp only [p2p_chebPair]
    refine ⟨h1, ?_⟩
    rw [degree_sub_eq_left_of_degree_lt (by rw [h2, h1, ih.2]; exact hlt), h2, h1]

lemma p2p_chebPair_eval_T (p : ℕ) (s : ℂ) :
    (Chebyshev.T ℂ ((2 * p : ℕ) : ℤ)).eval s =
        ((p2p_chebPair 1 1 p).1.map (algebraMap ℝ ℂ)).eval (s ^ 2) ∧
      (Chebyshev.T ℂ ((2 * p + 1 : ℕ) : ℤ)).eval s =
        s * ((p2p_chebPair 1 1 p).2.map (algebraMap ℝ ℂ)).eval (s ^ 2) := by
  induction p with
  | zero => simp [p2p_chebPair]
  | succ p ih =>
    have e1 : (((2 * (p + 1) : ℕ) : ℤ)) = ((2 * p : ℕ) : ℤ) + 2 := by push_cast; ring
    have e2 : (((2 * (p + 1) + 1 : ℕ) : ℤ)) = ((2 * p + 1 : ℕ) : ℤ) + 2 := by push_cast; ring
    have e3 : ((2 * p : ℕ) : ℤ) + 1 = ((2 * p + 1 : ℕ) : ℤ) := by push_cast; ring
    have e4 : ((2 * p + 1 : ℕ) : ℤ) + 1 = ((2 * (p + 1) : ℕ) : ℤ) := by push_cast; ring
    have hT0 : (Chebyshev.T ℂ ((2 * (p + 1) : ℕ) : ℤ)).eval s =
        ((p2p_chebPair 1 1 (p + 1)).1.map (algebraMap ℝ ℂ)).eval (s ^ 2) := by
      rw [e1, Chebyshev.T_add_two, e3]
      simp only [eval_sub, eval_mul, eval_X, ih.1, ih.2, p2p_chebPair, Polynomial.map_sub,
        Polynomial.map_mul, map_X]
      simp; ring
    refine ⟨hT0, ?_⟩
    rw [e2, Chebyshev.T_add_two, e4]
    simp only [eval_sub, eval_mul, eval_X, hT0, ih.2, p2p_chebPair, Polynomial.map_sub,
      Polynomial.map_mul, map_X]
    simp; ring

lemma p2p_chebPair_eval_U (p : ℕ) (s : ℂ) :
    (Chebyshev.U ℂ ((2 * p : ℕ) : ℤ)).eval s =
        ((p2p_chebPair 1 2 p).1.map (algebraMap ℝ ℂ)).eval (s ^ 2) ∧
      (Chebyshev.U ℂ ((2 * p + 1 : ℕ) : ℤ)).eval s =
        s * ((p2p_chebPair 1 2 p).2.map (algebraMap ℝ ℂ)).eval (s ^ 2) := by
  induction p with
  | zero => simp [p2p_chebPair]; ring
  | succ p ih =>
    have e1 : (((2 * (p + 1) : ℕ) : ℤ)) = ((2 * p : ℕ) : ℤ) + 2 := by push_cast; ring
    have e2 : (((2 * (p + 1) + 1 : ℕ) : ℤ)) = ((2 * p + 1 : ℕ) : ℤ) + 2 := by push_cast; ring
    have e3 : ((2 * p : ℕ) : ℤ) + 1 = ((2 * p + 1 : ℕ) : ℤ) := by push_cast; ring
    have e4 : ((2 * p + 1 : ℕ) : ℤ) + 1 = ((2 * (p + 1) : ℕ) : ℤ) := by push_cast; ring
    have hT0 : (Chebyshev.U ℂ ((2 * (p + 1) : ℕ) : ℤ)).eval s =
        ((p2p_chebPair 1 2 (p + 1)).1.map (algebraMap ℝ ℂ)).eval (s ^ 2) := by
      rw [e1, Chebyshev.U_add_two, e3]
      simp only [eval_sub, eval_mul, eval_X, ih.1, ih.2, p2p_chebPair, Polynomial.map_sub,
        Polynomial.map_mul, map_X]
      simp; ring
    refine ⟨hT0, ?_⟩
    rw [e2, Chebyshev.U_add_two, e4]
    simp only [eval_sub, eval_mul, eval_X, hT0, ih.2, p2p_chebPair, Polynomial.map_sub,
      Polynomial.map_mul, map_X]
    simp; ring

/-- The polynomial `Q_p` with `basis_p(s) = s^ε Q_p(s²)` for the Lamé polynomial type `t`. -/
def p2p_Q : LamePolyType → ℕ → ℝ[X]
  | .uE, p => C (if p = 0 then 1 / 2 else 1) * (p2p_chebPair 1 1 p).1
  | .dE, p => C (if p = 0 then 1 / 2 else 1) * (p2p_chebPair 1 1 p).1
  | .sE, p => (p2p_chebPair 1 1 p).2
  | .sdE, p => (p2p_chebPair 1 1 p).2
  | .cE, p => (p2p_chebPair 1 2 p).1
  | .cdE, p => (p2p_chebPair 1 2 p).1
  | .scE, p => (p2p_chebPair 1 2 p).2
  | .scdE, p => (p2p_chebPair 1 2 p).2

lemma p2p_Q_degree (t : LamePolyType) (p : ℕ) : (p2p_Q t p).degree = p := by
  have hT := p2p_chebPair_degree (e := 1) (o := 1) one_ne_zero one_ne_zero p
  have hU := p2p_chebPair_degree (e := 1) (o := 2) one_ne_zero two_ne_zero p
  have hc : (if p = 0 then (1 / 2 : ℝ) else 1) ≠ 0 := by split_ifs <;> norm_num
  cases t <;> simp only [p2p_Q, degree_C_mul hc, hT, hU]

lemma p2p_basis_eq (t : LamePolyType) (p : ℕ) (s : ℂ) :
    t.basis p s = (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then s else 1) *
      ((p2p_Q t p).map (algebraMap ℝ ℂ)).eval (s ^ 2) := by
  have hT := p2p_chebPair_eval_T p s
  have hU := p2p_chebPair_eval_U p s
  cases t <;> simp only [LamePolyType.basis, p2p_Q, hT.1, hT.2, hU.1, hU.2, Polynomial.map_mul,
    map_C, eval_mul, eval_C, reduceCtorEq, or_false, or_true, ite_true, ite_false,
    one_mul] <;> split_ifs <;> simp

/-- The top coefficient `c_n` of a Lamé polynomial is nonzero. -/
lemma p2p_lamePolyCoeff_last_ne_zero {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType)
    {n m : ℕ} (hm : m ≤ n) : lamePolyCoeff t n m k n ≠ 0 := by
  have hv := p2p_lameRecVec_last_ne_zero (p2p_alpha_gamma_pos hk0 t n)
    (p2p_lamePolyH_eval hk0 t hm)
  have hN := p2p_normForm_pos hk0 hk1 t n
    (c := lameRecVec t.recurrence (t.order n) k (lamePolyH t n m k)) rfl
  simp only [lamePolyCoeff, le_refl, ite_true]
  refine div_ne_zero (mul_ne_zero (by split_ifs <;> norm_num) hv) ?_
  exact (Real.sqrt_pos.mpr hN).ne'

end p2pPolyForm

/-- Parity of the Chebyshev basis functions of Table 29.12.1 in `s = sn`. -/
lemma p1l_basis_neg (t : LamePolyType) (p : ℕ) (s : ℂ) :
    t.basis p (-s) =
      (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then -1 else 1) * t.basis p s := by
  have hT : ∀ j : ℕ, (Chebyshev.T ℂ (j : ℤ)).eval (-s) =
      (-1) ^ j * (Chebyshev.T ℂ (j : ℤ)).eval s := fun j => by
    rw [Chebyshev.T_eval_neg, Int.negOnePow_def, zpow_natCast]; push_cast; ring
  have hU : ∀ j : ℕ, (Chebyshev.U ℂ (j : ℤ)).eval (-s) =
      (-1) ^ j * (Chebyshev.U ℂ (j : ℤ)).eval s := fun j => by
    rw [Chebyshev.U_eval_neg, Int.negOnePow_def, zpow_natCast]; push_cast; ring
  cases t <;> simp only [LamePolyType.basis, hT, hU, pow_succ, pow_mul] <;> simp

/-- How a Lamé polynomial transforms when `sn, cn, dn` are multiplied by constants
`ε = ±1`, `a`, `b`. -/
theorem p1l_lamePolyEk_transform (t : LamePolyType) (n m : ℕ) {z z' : ℂ} {ε a b : ℂ}
    (hε : ε = 1 ∨ ε = -1) (hs : jacobiSnk z' k = ε * jacobiSnk z k)
    (hc : jacobiCnk z' k = a * jacobiCnk z k) (hd : jacobiDnk z' k = b * jacobiDnk z k) :
    lamePolyEk t n m z' k =
      (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then ε else 1) *
        (if t = .cE ∨ t = .scE ∨ t = .cdE ∨ t = .scdE then a else 1) *
        (if t = .dE ∨ t = .sdE ∨ t = .cdE ∨ t = .scdE then b else 1) *
        lamePolyEk t n m z k := by
  have hsum : ∑ p ∈ Finset.range (n + 1), (lamePolyCoeff t n m k p : ℂ) *
      t.basis p (jacobiSnk z' k) =
      (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then ε else 1) *
      ∑ p ∈ Finset.range (n + 1), (lamePolyCoeff t n m k p : ℂ) * t.basis p (jacobiSnk z k) := by
    rw [hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases hε with rfl | rfl
    · simp
    · rw [neg_one_mul, p1l_basis_neg]
      split_ifs <;> ring
  rw [lamePolyEk, lamePolyEk, hsum]
  cases t <;> simp [LamePolyType.prefactor, hc, hd] <;> ring

/-- The shift identities used for the periods and parities of Lamé polynomials. -/
theorem p1l_shifts (hk0 : 0 < k) (hk1 : k < 1) (z : ℂ) :
    let K : ℂ := Real.compEllIntKm (k ^ 2)
    let K' : ℂ := Real.compEllIntKm (1 - k ^ 2)
    (jacobiSnk (z + 2 * K) k = -jacobiSnk z k ∧ jacobiCnk (z + 2 * K) k = -jacobiCnk z k ∧
      jacobiDnk (z + 2 * K) k = jacobiDnk z k) ∧
    (jacobiSnk (z + 2 * I * K') k = jacobiSnk z k ∧
      jacobiCnk (z + 2 * I * K') k = -jacobiCnk z k ∧
      jacobiDnk (z + 2 * I * K') k = -jacobiDnk z k) ∧
    (jacobiSnk (-z) k = -jacobiSnk z k ∧ jacobiCnk (-z) k = jacobiCnk z k ∧
      jacobiDnk (-z) k = jacobiDnk z k) ∧
    (jacobiSnk (K - z) k = jacobiSnk (K + z) k ∧ jacobiCnk (K - z) k = -jacobiCnk (K + z) k ∧
      jacobiDnk (K - z) k = jacobiDnk (K + z) k) ∧
    (jacobiSnk (K + I * K' - z) k = jacobiSnk (K + I * K' + z) k ∧
      jacobiCnk (K + I * K' - z) k = jacobiCnk (K + I * K' + z) k ∧
      jacobiDnk (K + I * K' - z) k = -jacobiDnk (K + I * K' + z) k) := by
  intro K K'
  have hkD : (k : ℂ) ∈ jacobiModulusDomain := p22R1_ofReal_mem hk0 hk1
  have hK : compEllIntKk (k : ℂ) = K := compEllIntKk_ofReal (by nlinarith)
  have hK' : compEllIntKpk (k : ℂ) = K' := compEllIntKpk_ofReal (by positivity)
  have neg : ∀ w : ℂ, jacobiSnk (-w) k = -jacobiSnk w k ∧ jacobiCnk (-w) k = jacobiCnk w k ∧
      jacobiDnk (-w) k = jacobiDnk w k ∧ jacobiCdk (-w) k = jacobiCdk w k ∧
      jacobiSdk (-w) k = -jacobiSdk w k ∧ jacobiNdk (-w) k = jacobiNdk w k ∧
      jacobiDck (-w) k = jacobiDck w k ∧ jacobiNck (-w) k = jacobiNck w k ∧
      jacobiSck (-w) k = -jacobiSck w k := fun w => by
    simp [jacobiSnk, jacobiCnk, jacobiDnk, jacobiCdk, jacobiSdk, jacobiNdk, jacobiDck, jacobiNck,
      jacobiSck, jacobiPQk_neg]
  have sn := jacobiSnk_shift hkD
  have cn := jacobiCnk_shift hkD
  have dn := jacobiDnk_shift hkD
  rw [hK, hK'] at sn cn dn
  have e1 : ∀ w : ℂ, w + 2 * I * K' = w + 2 * (I * K') := fun w => by ring
  have e2 : K - z = -z + K := by ring
  have e3 : K + z = z + K := by ring
  have e4 : K + I * K' - z = -z + K + I * K' := by ring
  have e5 : K + I * K' + z = z + K + I * K' := by ring
  refine ⟨⟨(sn z).2.2.2.1, (cn z).2.2.2.1, (dn z).2.2.2.1⟩,
    ⟨by rw [e1, (sn z).2.2.2.2.2], by rw [e1, (cn z).2.2.2.2.2], by rw [e1, (dn z).2.2.2.2.2]⟩,
    ⟨(neg z).1, (neg z).2.1, (neg z).2.2.1⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [e2, e3, (sn _).1, (sn _).1, (neg z).2.2.2.1]
  · rw [e2, e3, (cn _).1, (cn _).1, (neg z).2.2.2.2.1]; ring
  · rw [e2, e3, (dn _).1, (dn _).1, (neg z).2.2.2.2.2.1]
  · rw [e4, e5, (sn _).2.1, (sn _).2.1, (neg z).2.2.2.2.2.2.1]
  · rw [e4, e5, (cn _).2.1, (cn _).2.1, (neg z).2.2.2.2.2.2.2.1]
  · rw [e4, e5, (dn _).2.1, (dn _).2.1, (neg z).2.2.2.2.2.2.2.2]; ring


/-- The polynomial form with `deg P = n` (in particular `P ≠ 0`). -/
theorem p2p_polyForm (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType) {n m : ℕ} (hm : m ≤ n) :
    ∃ P : ℝ[X], P.degree = n ∧ ∀ z : ℂ,
      lamePolyEk t n m z k = t.prefactor z k *
        (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then jacobiSnk z k else 1) *
        (P.map (algebraMap ℝ ℂ)).eval (jacobiSnk z k ^ 2) := by
  set c := lamePolyCoeff t n m k
  have hcn : c n ≠ 0 := p2p_lamePolyCoeff_last_ne_zero hk0 hk1 t hm
  refine ⟨∑ p ∈ Finset.range (n + 1), C (c p) * p2p_Q t p, ?_, fun z => ?_⟩
  · rw [Finset.sum_range_succ]
    have htop : (C (c n) * p2p_Q t n).degree = n := by
      rw [degree_C_mul hcn, p2p_Q_degree]
    have hlow : (∑ p ∈ Finset.range n, C (c p) * p2p_Q t p).degree < n := by
      refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun p hp => ?_
      refine lt_of_le_of_lt (degree_mul_le _ _) ?_
      rw [p2p_Q_degree]
      refine lt_of_le_of_lt (add_le_add_left degree_C_le _) ?_
      rw [zero_add]
      exact WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hp)
    rw [degree_add_eq_right_of_degree_lt (by rw [htop]; exact hlow), htop]
  · rw [lamePolyEk, mul_assoc]
    congr 1
    simp only [p2p_basis_eq, Polynomial.map_sum, Polynomial.map_mul, map_C, eval_finsetSum,
      eval_mul, eval_C, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [c]
    split_ifs <;> simp; ring

/-- Table 29.12.1, polynomial form: each Lamé polynomial of type `t` is
`sn^a cn^b dn^c P(sn²)` with `P` a polynomial of degree `n`, where `sn`, `cn`, `dn` occur as
indicated by the type (`cn`, `dn` through `t.prefactor`, and a factor `sn` exactly for
`sE, scE, sdE, scdE`); `m ≤ n`. In particular (§29.12(i)) it is a doubly-periodic meromorphic
function of `z`. Proved from 29.15.3: the eigenvector of the eigenvalue `H_m` has nonzero last
entry, and `T_{2p}`, `T_{2p+1}/s`, `U_{2p}`, `U_{2p+1}/s` are polynomials of degree `p` in
`s²`. -/
@[dlmf 29.12.T1, dlmf 29.12.i]
theorem lamePolyEk_polynomial_form (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType)
    {n m : ℕ} (hm : m ≤ n) :
    ∃ P : ℝ[X], P.natDegree = n ∧ ∀ z : ℂ,
      lamePolyEk t n m z k = t.prefactor z k *
        (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then jacobiSnk z k else 1) *
        (P.map (algebraMap ℝ ℂ)).eval (jacobiSnk z k ^ 2) := by
  obtain ⟨P, hP, hE⟩ := p2p_polyForm hk0 hk1 t hm
  exact ⟨P, natDegree_eq_of_degree_eq_some hP, hE⟩

/-- Table 29.12.1, periods: the real period of the Lamé polynomial is `2K` for
`uE, dE, scE` and `4K` otherwise (`w(z + rK) = w(z)` with `r = 2` resp. `4`), and its
imaginary period is `2iK'` for `uE, sE` and `4iK'` otherwise. Proved from Table 22.4.3. -/
@[dlmf 29.12.T1]
theorem lamePolyEk_periods (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType) (n m : ℕ)
    (z : ℂ) :
    lamePolyEk t n m (z + (if t = .uE ∨ t = .dE ∨ t = .scE then 2 else 4) *
        Real.compEllIntKm (k ^ 2)) k = lamePolyEk t n m z k ∧
      lamePolyEk t n m (z + (if t = .uE ∨ t = .sE then 2 else 4) * I *
        Real.compEllIntKm (1 - k ^ 2)) k = lamePolyEk t n m z k := by
  set K : ℂ := ((Real.compEllIntKm (k ^ 2) : ℝ) : ℂ)
  set K' : ℂ := ((Real.compEllIntKm (1 - k ^ 2) : ℝ) : ℂ)
  have h2 : ∀ w, lamePolyEk t n m (w + 2 * K) k =
      (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then -1 else 1) *
        (if t = .cE ∨ t = .scE ∨ t = .cdE ∨ t = .scdE then -1 else 1) *
        (if t = .dE ∨ t = .sdE ∨ t = .cdE ∨ t = .scdE then 1 else 1) * lamePolyEk t n m w k :=
    fun w => p1l_lamePolyEk_transform t n m (Or.inr rfl)
      (by rw [(p1l_shifts hk0 hk1 w).1.1]; ring) (by rw [(p1l_shifts hk0 hk1 w).1.2.1]; ring)
      (by rw [(p1l_shifts hk0 hk1 w).1.2.2]; ring)
  have h2i : ∀ w, lamePolyEk t n m (w + 2 * I * K') k =
      (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then 1 else 1) *
        (if t = .cE ∨ t = .scE ∨ t = .cdE ∨ t = .scdE then -1 else 1) *
        (if t = .dE ∨ t = .sdE ∨ t = .cdE ∨ t = .scdE then -1 else 1) * lamePolyEk t n m w k :=
    fun w => p1l_lamePolyEk_transform t n m (Or.inl rfl)
      (by rw [(p1l_shifts hk0 hk1 w).2.1.1]; ring) (by rw [(p1l_shifts hk0 hk1 w).2.1.2.1]; ring)
      (by rw [(p1l_shifts hk0 hk1 w).2.1.2.2]; ring)
  have h4 : lamePolyEk t n m (z + 4 * K) k = lamePolyEk t n m z k := by
    rw [show z + 4 * K = z + 2 * K + 2 * K by ring, h2, h2]
    cases t <;> simp
  have h4i : lamePolyEk t n m (z + 4 * I * K') k = lamePolyEk t n m z k := by
    rw [show z + 4 * I * K' = z + 2 * I * K' + 2 * I * K' by ring, h2i, h2i]
    cases t <;> simp
  constructor
  · cases t <;> simp [h4, h2]
  · cases t <;> simp [h4i, h2i]

/-- Table 29.12.1, parities: `w(-z) = ±w(z)` with sign `-` exactly when the type has a factor
`sn`; `w(K - z) = ±w(K + z)` with `-` exactly for a factor `cn`; and
`w(K + iK' - z) = ±w(K + iK' + z)` with `-` exactly for a factor `dn`. Proved from
Table 22.4.3 and the parities of `sn, cn, dn` and of the Chebyshev polynomials. -/
@[dlmf 29.12.T1]
theorem lamePolyEk_parities (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType) (n m : ℕ)
    (z : ℂ) :
    lamePolyEk t n m (-z) k =
        (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then -1 else 1) * lamePolyEk t n m z k ∧
      lamePolyEk t n m (Real.compEllIntKm (k ^ 2) - z) k =
        (if t = .cE ∨ t = .scE ∨ t = .cdE ∨ t = .scdE then -1 else 1) *
          lamePolyEk t n m (Real.compEllIntKm (k ^ 2) + z) k ∧
      lamePolyEk t n m (Real.compEllIntKm (k ^ 2) + I * Real.compEllIntKm (1 - k ^ 2) - z) k =
        (if t = .dE ∨ t = .sdE ∨ t = .cdE ∨ t = .scdE then -1 else 1) *
          lamePolyEk t n m (Real.compEllIntKm (k ^ 2) + I * Real.compEllIntKm (1 - k ^ 2) + z) k
      := by
  obtain ⟨-, -, h1, h2, h3⟩ := p1l_shifts hk0 hk1 z
  refine ⟨?_, ?_, ?_⟩
  · rw [p1l_lamePolyEk_transform t n m (z' := -z) (z := z) (ε := -1) (a := 1) (b := 1) (Or.inr rfl)
      (by rw [h1.1]; ring) (by rw [h1.2.1]; ring) (by rw [h1.2.2]; ring)]
    cases t <;> simp
  · rw [p1l_lamePolyEk_transform t n m (z' := _ - z) (z := _ + z) (ε := 1) (a := -1) (b := 1)
      (Or.inl rfl)
      (by rw [h2.1]; ring) (by rw [h2.2.1]; ring) (by rw [h2.2.2]; ring)]
    cases t <;> simp
  · rw [p1l_lamePolyEk_transform t n m (z' := _ - z) (z := _ + z) (ε := 1) (a := 1)
      (b := -1) (Or.inl rfl)
      (by rw [h3.1]; ring) (by rw [h3.2.1]; ring) (by rw [h3.2.2]; ring)]
    cases t <;> simp

end DLMF.Lame
