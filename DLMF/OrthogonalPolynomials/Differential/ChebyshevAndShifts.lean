/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Differential.ClassicalEquations

/-!
# Chebyshev identities and shifted polynomial derivatives

Chebyshev contiguous identities and shifted-parameter differential formulas for classical
polynomial families.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.Differential`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter

open scoped Real Nat Topology

open DLMF.Hypergeometric

open DLMF.Confluent

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- Identity under the stated parameter and domain assumptions: `chebyshevV (n + 1) x + chebyshevV
n x = 2 * (Chebyshev.T ℂ (n + 1)).eval x`. -/
@[dlmf 18.9.E11]
theorem chebyshevV_contiguous (n : ℕ) (x : ℂ) :
    chebyshevV (n + 1) x + chebyshevV n x = 2 * (Chebyshev.T ℂ (n + 1)).eval x := by
  have hraise := jacobi_raise_beta (α := -1 / 2) (β := -1 / 2) (by norm_num) n x
  rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num] at hraise
  unfold chebyshevV
  have hT := chebyshevT_eq_jacobi (n + 1) x
  push_cast at hT
  rw [hT, jacobiPolyP_one, jacobiPolyP_one,
    jacobiPolyP_one, show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num, poch_succ,
    Nat.factorial_succ]
  have hp : poch (1 / 2 : ℂ) n ≠ 0 := poch_half_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hh : ((1 / 2 : ℂ) + n) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h12 : (1 + 2 * (n : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  push_cast
  field_simp
  simp only [neg_div] at hraise
  linear_combination (-2 : ℂ) * hraise

/-- Identity under the stated parameter and domain assumptions: `(Chebyshev.T ℂ (n + 1)).eval x +
(Chebyshev.T ℂ n).eval x = (1 + x) * chebyshevV n x`. -/
@[dlmf 18.9.E12]
theorem chebyshevV_mul_one_add (n : ℕ) (x : ℂ) :
    (Chebyshev.T ℂ (n + 1)).eval x + (Chebyshev.T ℂ n).eval x = (1 + x) * chebyshevV n x := by
  have hraise := jacobi_raise_degree_beta (α := -1 / 2) (β := -1 / 2) (by norm_num) n x
  rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num] at hraise
  unfold chebyshevV
  have hT := chebyshevT_eq_jacobi (n + 1) x
  push_cast at hT
  rw [hT, chebyshevT_eq_jacobi, jacobiPolyP_one,
    jacobiPolyP_one, jacobiPolyP_one,
    show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num, poch_succ, Nat.factorial_succ]
  have hp : poch (1 / 2 : ℂ) n ≠ 0 := poch_half_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hh : ((1 / 2 : ℂ) + n) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h12 : (1 + 2 * (n : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  push_cast
  field_simp
  simp only [neg_div] at hraise
  linear_combination (-2 : ℂ) * hraise

/-- Identity under the stated parameter and domain assumptions: `chebyshevV n (cos θ) * cos (θ /
2) = cos ((n + 1 / 2) * θ)`. -/
@[dlmf 18.5.E3]
theorem chebyshevV_cos (n : ℕ) (θ : ℂ) :
    chebyshevV n (cos θ) * cos (θ / 2) = cos ((n + 1 / 2) * θ) := by
  induction n with
  | zero =>
    simp only [chebyshevV, jacobiPolyP_zero, div_one, Nat.cast_zero, zero_add, one_mul]
    ring_nf
  | succ n ih =>
    have hV : chebyshevV (n + 1) (cos θ) =
        2 * (Chebyshev.T ℂ (n + 1)).eval (cos θ) - chebyshevV n (cos θ) := by
      linear_combination chebyshevV_contiguous n (cos θ)
    have hT : (Chebyshev.T ℂ (n + 1)).eval (cos θ) = cos (((n : ℂ) + 1) * θ) := by
      have := Polynomial.Chebyshev.T_complex_cos θ ((n + 1 : ℕ) : ℤ)
      push_cast at this ⊢
      exact this
    have hsum := Complex.cos_add_cos (((n : ℂ) + 1 + 1 / 2) * θ) (((n : ℂ) + 1 / 2) * θ)
    rw [show (((n : ℂ) + 1 + 1 / 2) * θ + ((n : ℂ) + 1 / 2) * θ) / 2 = ((n : ℂ) + 1) * θ by ring,
      show (((n : ℂ) + 1 + 1 / 2) * θ - ((n : ℂ) + 1 / 2) * θ) / 2 = θ / 2 by ring] at hsum
    push_cast
    rw [hV, hT]
    linear_combination -hsum - ih

/-- The companion of 18.9.5 raising `α`:
`(2n+α+β+3) P^{(α,β)}_{n+1} = (n+α+β+2) P^{(α+1,β)}_{n+1} - (n+β+1) P^{(α+1,β)}_n`. -/
theorem jacobi_raise_alpha {α β : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    (2 * n + α + β + 3) * jacobiPolyP α β (n + 1) x =
      (n + α + β + 2) * jacobiPolyP (α + 1) β (n + 1) x - (n + β + 1)
          * jacobiPolyP (α + 1) β n x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have key : (fun x : ℂ => (2 * n + α + β + 3) * jacobiPolyP α β (n + 1) x) =
      fun x => (n + α + β + 2) * jacobiPolyP (α + 1) β (n + 1) x -
        (n + β + 1) * jacobiPolyP (α + 1) β n x := by
    refine eq_of_eqOn_half_shift_disk (by intro x _; fun_prop) (by intro x _; fun_prop) ?_
    intro x hx
    have hrel := DLMF.Hypergeometric.contiguous_c_pair (a := -((n : ℂ) + 1))
      (b := (n : ℂ) + 1 + α + β + 1) (c := α + 1) hc hx
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hP0 : jacobiPolyP α β (n + 1) x * ((n + 1) * n.factorial) =
        (α + 1) * poch (α + 1 + 1) n *
          ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + 1 + α + β + 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [poch_succ_left, Nat.factorial_succ]
      push_cast
      field_simp
    have hP1 : jacobiPolyP (α + 1) β (n + 1) x * ((n + 1) * n.factorial) =
        poch (α + 1 + 1) n * (α + 1 + 1 + n) *
          ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + 1 + α + β + 1 + 1) (α + 1 + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [poch_succ, Nat.factorial_succ]
      push_cast
      rw [show (n : ℂ) + 1 + (α + 1) + β + 1 = (n : ℂ) + 1 + α + β + 1 + 1 by ring]
      field_simp
    have hP2 : jacobiPolyP (α + 1) β n x * ((n + 1) * n.factorial) =
        poch (α + 1 + 1) n * (n + 1) *
          ₂F₁ (-((n : ℂ) + 1) + 1) ((n : ℂ) + 1 + α + β + 1) (α + 1 + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [show (n : ℂ) + (α + 1) + β + 1 = (n : ℂ) + 1 + α + β + 1 by ring,
        show -(n : ℂ) = -((n : ℂ) + 1) + 1 by ring]
      field_simp
    have hM : ((n : ℂ) + 1) * n.factorial ≠ 0 := mul_ne_zero hn1 hf
    apply mul_right_cancel₀ hM
    linear_combination (2 * n + α + β + 3) * hP0 - (n + α + β + 2) * hP1 + (n + β + 1) * hP2 +
      (poch (α + 1 + 1) n) * hrel
  exact congrFun key x

/-- `(3/2)_n ≠ 0`. -/
theorem poch_three_half_ne_zero (n : ℕ) : poch (3 / 2 : ℂ) n ≠ 0 :=
  poch_ne_zero_of_not_neg_nat (fun k hk => by
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) n

/-- `W_{n+1} - W_n = 2 T_{n+1}`, the fourth-kind companion of 18.9.11. -/
theorem chebyshevW_contiguous (n : ℕ) (x : ℂ) :
    chebyshevW (n + 1) x - chebyshevW n x = 2 * (Chebyshev.T ℂ (n + 1)).eval x := by
  have hraise := jacobi_raise_alpha (α := -1 / 2) (β := -1 / 2) (by norm_num) n x
  rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num] at hraise
  unfold chebyshevW
  have hT := chebyshevT_eq_jacobi (n + 1) x
  push_cast at hT
  rw [hT, jacobiPolyP_one, jacobiPolyP_one, jacobiPolyP_one,
    show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num, show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num,
    poch_succ (3 / 2 : ℂ) n, poch_succ_left (1 / 2 : ℂ) n,
    show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, Nat.factorial_succ]
  have hp : poch (3 / 2 : ℂ) n ≠ 0 := poch_three_half_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hh : ((3 / 2 : ℂ) + n) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h32 : (3 + 2 * (n : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  push_cast
  field_simp
  simp only [neg_div] at hraise
  linear_combination (-2 * (3 + 2 * (n : ℂ))) * hraise

/-- Identity under the stated parameter and domain assumptions: `chebyshevW n (cos θ) * sin (θ /
2) = sin ((n + 1 / 2) * θ)`. -/
@[dlmf 18.5.E4]
theorem chebyshevW_cos (n : ℕ) (θ : ℂ) :
    chebyshevW n (cos θ) * sin (θ / 2) = sin ((n + 1 / 2) * θ) := by
  induction n with
  | zero =>
    simp only [chebyshevW, jacobiPolyP_zero, div_one, Nat.cast_zero, mul_zero, zero_add, one_mul]
    ring_nf
  | succ n ih =>
    have hW : chebyshevW (n + 1) (cos θ) =
        2 * (Chebyshev.T ℂ (n + 1)).eval (cos θ) + chebyshevW n (cos θ) := by
      linear_combination chebyshevW_contiguous n (cos θ)
    have hT : (Chebyshev.T ℂ (n + 1)).eval (cos θ) = cos (((n : ℂ) + 1) * θ) := by
      have := Polynomial.Chebyshev.T_complex_cos θ ((n + 1 : ℕ) : ℤ)
      push_cast at this ⊢
      exact this
    have hdiff := Complex.sin_sub_sin (((n : ℂ) + 1 + 1 / 2) * θ) (((n : ℂ) + 1 / 2) * θ)
    rw [show (((n : ℂ) + 1 + 1 / 2) * θ + ((n : ℂ) + 1 / 2) * θ) / 2 = ((n : ℂ) + 1) * θ by ring,
      show (((n : ℂ) + 1 + 1 / 2) * θ - ((n : ℂ) + 1 / 2) * θ) / 2 = θ / 2 by ring] at hdiff
    push_cast
    rw [hW, hT]
    linear_combination ih - hdiff

/-- Identity under the stated parameter and domain assumptions: `(Chebyshev.T ℂ (2 * n + 1)).eval
x = x * chebyshevV n (2 * x ^ 2 - 1)`. -/
@[dlmf 18.7.E18]
theorem chebyshevT_quadratic (n : ℕ) (x : ℂ) :
    (Chebyshev.T ℂ (2 * n + 1)).eval x = x * chebyshevV n (2 * x ^ 2 - 1) := by
  obtain ⟨θ, rfl⟩ := Complex.cos_surjective x
  have hT : (Chebyshev.T ℂ (2 * n + 1)).eval (cos θ) = cos ((2 * (n : ℂ) + 1) * θ) := by
    have := Polynomial.Chebyshev.T_complex_cos θ ((2 * n + 1 : ℕ) : ℤ)
    push_cast at this ⊢
    exact this
  have hV := chebyshevV_cos n (2 * θ)
  rw [Complex.cos_two_mul, show 2 * θ / 2 = θ by ring] at hV
  rw [hT, show (2 * (n : ℂ) + 1) * θ = ((n : ℂ) + 1 / 2) * (2 * θ) by ring, ← hV]
  ring

/-- `sin θ ≠ 0` when `cos θ ≠ ±1`. -/
theorem sin_ne_zero_of_cos_ne {θ : ℂ} (h1 : cos θ ≠ 1) (h2 : cos θ ≠ -1) : sin θ ≠ 0 := by
  intro h
  have hsc := Complex.sin_sq_add_cos_sq θ
  rw [h] at hsc
  have : (cos θ - 1) * (cos θ + 1) = 0 := by linear_combination hsc
  rcases mul_eq_zero.mp this with h3 | h3
  · exact h1 (by linear_combination h3)
  · exact h2 (by linear_combination h3)

/-- `sin (θ/2) ≠ 0` when `cos θ ≠ 1`. -/
theorem sin_half_ne_zero_of_cos_ne_one {θ : ℂ} (h1 : cos θ ≠ 1) : sin (θ / 2) ≠ 0 := by
  intro h
  apply h1
  have hsc := Complex.sin_sq_add_cos_sq (θ / 2)
  rw [h] at hsc
  rw [show θ = 2 * (θ / 2) by ring, Complex.cos_two_mul]
  linear_combination 2 * hsc

/-- Identity under the stated parameter and domain assumptions: `(Chebyshev.U ℂ (2 * n)).eval x =
chebyshevW n (2 * x ^ 2 - 1)`. -/
@[dlmf 18.7.E17]
theorem chebyshevU_quadratic (n : ℕ) (x : ℂ) :
    (Chebyshev.U ℂ (2 * n)).eval x = chebyshevW n (2 * x ^ 2 - 1) := by
  have hne : jacobiPolyP (1 / 2) (-1 / 2) n 1 ≠ 0 := jacobiPolyP_one_ne_zero (by norm_num) n
  have key : (fun x : ℂ => (Chebyshev.U ℂ (2 * n)).eval x) =
      fun x => chebyshevW n (2 * x ^ 2 - 1) := by
    refine DLMF.Hypergeometric.eq_of_analyticOnNhd_univ_of_eqOn ?_ ?_
      (isOpen_ne.inter isOpen_ne : IsOpen {x : ℂ | x ≠ 1 ∧ x ≠ -1})
      ⟨0, by norm_num, by exact (by norm_num : (0 : ℂ) ≠ -1)⟩ ?_
    · exact (Polynomial.differentiable _).differentiableOn.analyticOnNhd isOpen_univ
    · intro x _
      unfold chebyshevW
      have h1 : AnalyticAt ℂ (fun x : ℂ => jacobiPolyP (1 / 2) (-1 / 2) n (2 * x ^ 2 - 1)) x :=
        (analyticAt_jacobiPolyP _ _ n _).comp (f := fun x : ℂ => 2 * x ^ 2 - 1) (by fun_prop)
      exact AnalyticAt.fun_div (f := fun x : ℂ => (2 * (n : ℂ) + 1) *
        jacobiPolyP (1 / 2) (-1 / 2) n (2 * x ^ 2 - 1))
            (g := fun _ => jacobiPolyP (1 / 2) (-1 / 2) n 1)
        (x := x) (analyticAt_const.mul h1) analyticAt_const hne
    intro x hx
    obtain ⟨θ, rfl⟩ := Complex.cos_surjective x
    have hs : sin θ ≠ 0 := sin_ne_zero_of_cos_ne hx.1 hx.2
    have hU : (Chebyshev.U ℂ (2 * n)).eval (cos θ) * sin θ = sin ((2 * (n : ℂ) + 1) * θ) := by
      have := Polynomial.Chebyshev.U_complex_cos θ ((2 * n : ℕ) : ℤ)
      push_cast at this ⊢
      exact this
    have hW := chebyshevW_cos n (2 * θ)
    rw [Complex.cos_two_mul, show 2 * θ / 2 = θ by ring,
      show ((n : ℂ) + 1 / 2) * (2 * θ) = (2 * (n : ℂ) + 1) * θ by ring] at hW
    exact mul_right_cancel₀ hs (hU.trans hW.symm)
  exact congrFun key x

/-- Identity under the stated parameter and domain assumptions: `chebyshevV n (-x) = (-1 : ℂ) ^ n
* chebyshevW n x`. -/
@[dlmf 18.6.T1]
theorem chebyshevV_reflection (n : ℕ) (x : ℂ) :
    chebyshevV n (-x) = (-1 : ℂ) ^ n * chebyshevW n x := by
  have hneV : jacobiPolyP (-1 / 2) (1 / 2) n 1 ≠ 0 := jacobiPolyP_one_ne_zero (by norm_num) n
  have hneW : jacobiPolyP (1 / 2) (-1 / 2) n 1 ≠ 0 := jacobiPolyP_one_ne_zero (by norm_num) n
  have key : (fun x : ℂ => chebyshevV n (-x)) = fun x => (-1 : ℂ) ^ n * chebyshevW n x := by
    refine DLMF.Hypergeometric.eq_of_analyticOnNhd_univ_of_eqOn ?_ ?_
      (isOpen_ne : IsOpen {x : ℂ | x ≠ 1}) ⟨0, by norm_num⟩ ?_
    · intro x _
      unfold chebyshevV
      have h1 : AnalyticAt ℂ (fun x : ℂ => jacobiPolyP (-1 / 2) (1 / 2) n (-x)) x :=
        (analyticAt_jacobiPolyP _ _ n _).comp (f := fun x : ℂ => -x) (by fun_prop)
      exact AnalyticAt.fun_div (f := fun x : ℂ => jacobiPolyP (-1 / 2) (1 / 2) n (-x))
        (g := fun _ => jacobiPolyP (-1 / 2) (1 / 2) n 1) (x := x) h1 analyticAt_const hneV
    · intro x _
      unfold chebyshevW
      exact analyticAt_const.mul (AnalyticAt.fun_div (f := fun x : ℂ => (2 * (n : ℂ) + 1) *
        jacobiPolyP (1 / 2) (-1 / 2) n x) (g := fun _ => jacobiPolyP (1 / 2) (-1 / 2) n 1) (x := x)
        (analyticAt_const.mul (analyticAt_jacobiPolyP _ _ n x)) analyticAt_const hneW)
    intro x hx
    obtain ⟨θ, rfl⟩ := Complex.cos_surjective x
    have hs : sin (θ / 2) ≠ 0 := sin_half_ne_zero_of_cos_ne_one hx
    have hV := chebyshevV_cos n ((Real.pi : ℂ) - θ)
    rw [Complex.cos_pi_sub] at hV
    have h1 : cos (((Real.pi : ℂ) - θ) / 2) = sin (θ / 2) := by
      rw [show ((Real.pi : ℂ) - θ) / 2 = (Real.pi : ℂ) / 2 - θ / 2 by ring,
        Complex.cos_pi_div_two_sub]
    have hcos : cos ((n : ℂ) * (Real.pi : ℂ)) = (-1 : ℂ) ^ n := by
      rw [show (n : ℂ) * (Real.pi : ℂ) = ((n * Real.pi : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cos, Real.cos_nat_mul_pi]
      push_cast
      ring
    have hsin : sin ((n : ℂ) * (Real.pi : ℂ)) = 0 := by
      rw [show (n : ℂ) * (Real.pi : ℂ) = ((n * Real.pi : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_sin, Real.sin_nat_mul_pi]
      push_cast
      ring
    have h2 : cos (((n : ℂ) + 1 / 2) * ((Real.pi : ℂ) - θ)) =
        (-1 : ℂ) ^ n * sin (((n : ℂ) + 1 / 2) * θ) := by
      rw [show ((n : ℂ) + 1 / 2) * ((Real.pi : ℂ) - θ) =
          ((n : ℂ) * Real.pi + (Real.pi : ℂ) / 2) - ((n : ℂ) + 1 / 2) * θ by ring,
        Complex.cos_sub, Complex.cos_add_pi_div_two, Complex.sin_add_pi_div_two, hcos, hsin]
      ring
    have hW := chebyshevW_cos n θ
    rw [h1, h2, ← hW, ← mul_assoc] at hV
    exact mul_right_cancel₀ hs hV
  exact congrFun key x

/-- Identity under the stated parameter and domain assumptions: `chebyshevW n (-x) = (-1 : ℂ) ^ n
* chebyshevV n x`. -/
@[dlmf 18.6.T1]
theorem chebyshevW_reflection (n : ℕ) (x : ℂ) :
    chebyshevW n (-x) = (-1 : ℂ) ^ n * chebyshevV n x := by
  have h := chebyshevV_reflection n (-x)
  rw [neg_neg] at h
  have hsq : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by
    rw [← mul_pow]
    simp
  rw [h, ← mul_assoc, hsq, one_mul]

/-- Identity under the stated parameter and domain assumptions: `laguerrePolyL α (n + 1) x =
laguerrePolyL (α + 1) (n + 1) x - laguerrePolyL (α + 1) n x`. -/
@[dlmf 18.9.E13]
theorem laguerrePolyL_raise_parameter {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    laguerrePolyL α (n + 1) x = laguerrePolyL (α + 1) (n + 1) x - laguerrePolyL (α + 1) n x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hb : ∀ k : ℕ, α + 1 + 1 - 1 ≠ -(k : ℂ) := by simpa using hc
  have hc1 : ∀ k : ℕ, α + 1 + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hc 1
  have hM := DLMF.Confluent.kummerM_contiguous_a_b (a := -((n + 1 : ℕ) : ℂ)) hb (z := x)
  rw [show α + 1 + 1 - 1 = α + 1 by ring,
    show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring] at hM
  have hP : poch (α + 1 + 1) n ≠ 0 := poch_ne_zero_of_not_neg_nat hc1 n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [laguerrePolyL]
  rw [poch_succ_left (α + 1) n, poch_succ (α + 1 + 1) n, Nat.factorial_succ n]
  push_cast at hM ⊢
  field_simp
  linear_combination hM

/-- Identity under the stated parameter and domain assumptions: `x * laguerrePolyL (α + 1) n x =
-(n + 1) * laguerrePolyL α (n + 1) x + (n + α + 1) * laguerrePolyL α n x`. -/
@[dlmf 18.9.E14]
theorem laguerrePolyL_mul_argument {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    x * laguerrePolyL (α + 1) n x = -(n + 1) * laguerrePolyL α (n + 1) x + (n + α + 1)
        * laguerrePolyL α n x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hc0 : α + 1 ≠ 0 := by simpa using hc 0
  have hM := DLMF.Confluent.kummerM_contiguous_shift_a (a := -(n : ℂ)) hc (z := x)
  rw [show -(n : ℂ) - 1 = -((n + 1 : ℕ) : ℂ) by push_cast; ring] at hM
  have hQ : poch (α + 1) n ≠ 0 := poch_ne_zero_of_not_neg_nat hc n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hrel : (α + 1) * poch (α + 1 + 1) n = poch (α + 1) n * (α + 1 + n) := by
    rw [← poch_succ_left, poch_succ]
  have hX : poch (α + 1 + 1) n = poch (α + 1) n * (α + 1 + n) / (α + 1) := by
    rw [eq_div_iff hc0]; linear_combination hrel
  simp only [laguerrePolyL]
  rw [poch_succ (α + 1) n, Nat.factorial_succ n, hX]
  push_cast at hM ⊢
  field_simp
  linear_combination (-(α + 1 + (n : ℂ))) * hM

/-- Differentiating a terminating Gauss series is valid throughout the complex plane. -/
theorem deriv_gauss_neg_nat_succ (n : ℕ) (b : ℂ) {c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    deriv (₂F₁ (-((n + 1 : ℕ) : ℂ)) b c) = fun z =>
      (-((n + 1 : ℕ) : ℂ) * b / c) * ₂F₁ (-(n : ℂ)) (b + 1) (c + 1) z := by
  funext z
  have hd := (hasFPowerSeriesOnBall_gauss_neg_nat (n + 1) b c).deriv_ofScalars.hasSum_mul_pow
    (z := z) (by simp)
  have hs := ((hasFPowerSeriesOnBall_gauss_neg_nat n (b + 1) (c + 1)).hasSum_mul_pow
    (z := z) (by simp)).mul_left (-((n + 1 : ℕ) : ℂ) * b / c)
  simp_rw [gaussHGCoeff_shift hc] at hd
  rw [show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring] at hd
  simp only [mul_assoc] at hd hs
  exact hd.unique hs

/-- Identity under the stated parameter and domain assumptions: `deriv (jacobiPolyP α β (n + 1)) x
= (n + α + β + 2) / 2 * jacobiPolyP (α + 1) (β + 1) n x`. -/
@[dlmf 18.9.E15]
theorem jacobi_derivative {α β : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    deriv (jacobiPolyP α β (n + 1)) x = (n + α + β + 2) / 2 * jacobiPolyP (α + 1) (β + 1) n x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hc0 : α + 1 ≠ 0 := by simpa using hc 0
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have he : jacobiPolyP α β (n + 1) = fun z => poch (α + 1) (n + 1) / ((n + 1).factorial : ℂ) *
      ₂F₁ (-((n + 1 : ℕ) : ℂ)) ((n + 1 : ℕ) + α + β + 1) (α + 1) ((1 - z) / 2) := rfl
  rw [he]
  simp only [deriv_const_mul_field', deriv_half_shift, deriv_gauss_neg_nat_succ n _ hc]
  rw [jacobiPolyP, poch_succ_left, Nat.factorial_succ]
  push_cast
  rw [show (n : ℂ) + 1 + α + β + 1 + 1 = n + (α + 1) + (β + 1) + 1 by ring]
  field_simp
  <;> ring

/-- The derivative of a Jacobi polynomial on the disk `‖(1-x)/2‖ < 1`, from 15.5.1 and the
chain rule. -/
theorem hasDerivAt_jacobiPolyP {α β : ℂ} (hα : -1 < α.re) (n : ℕ) {x : ℂ} (hx : ‖(1 - x) / 2‖ < 1) :
    HasDerivAt (jacobiPolyP α β n)
      (poch (α + 1) n / n.factorial * (-(n : ℂ) * ((n : ℂ) + α + β + 1) / (α + 1) *
        ₂F₁ (-(n : ℂ) + 1) ((n : ℂ) + α + β + 1 + 1) (α + 1 + 1) ((1 - x) / 2) * (-1 / 2))) x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hF := hasDerivAt_ordinaryHypergeometric (a := -(n : ℂ)) (b := (n : ℂ) + α + β + 1) hc hx
  have hin : HasDerivAt (fun x : ℂ => (1 - x) / 2) (-1 / 2) x :=
    ((hasDerivAt_id' x).const_sub 1).div_const 2
  exact (hF.comp x hin).const_mul (poch (α + 1) n / n.factorial)

/-- Identity under the stated parameter and domain assumptions: `(2 * n + α + β + 2) * (1 - x ^ 2)
* deriv (jacobiPolyP α β (n + 1)) x = (n + 1) * (α - β - (2 * n + α + β + 2) * x) *
jacobiPolyP α β (n + 1) x + 2 * (n + α + 1) * (n + β + 1) * jacobiPolyP α β n x`. -/
@[dlmf 18.9.E17]
theorem jacobi_lowering_derivative {α β : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    (2 * n + α + β + 2) * (1 - x ^ 2) * deriv (jacobiPolyP α β (n + 1)) x =
      (n + 1) * (α - β - (2 * n + α + β + 2) * x) * jacobiPolyP α β (n + 1) x +
      2 * (n + α + 1) * (n + β + 1) * jacobiPolyP α β n x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have key : (fun x : ℂ => (2 * n + α + β + 2) * (1 - x ^ 2) * deriv (jacobiPolyP α β (n + 1)) x) =
      fun x => (n + 1) * (α - β - (2 * n + α + β + 2) * x) * jacobiPolyP α β (n + 1) x +
        2 * (n + α + 1) * (n + β + 1) * jacobiPolyP α β n x := by
    refine eq_of_eqOn_half_shift_disk ?_ (by intro x _; fun_prop) ?_
    · intro x _
      have hd : AnalyticAt ℂ (deriv (jacobiPolyP α β (n + 1))) x :=
        (analyticOnNhd_jacobiPolyP α β (n + 1)).deriv x (Set.mem_univ x)
      fun_prop
    intro x hx
    have hrel := DLMF.Hypergeometric.contiguous_jacobi_lowering (a := -((n : ℂ) + 1))
      (b := (n : ℂ) + 1 + α + β + 1) (c := α + 1) hc hx
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hD : (-((n : ℂ) + 1) - 1) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hrel' := (mul_eq_zero.mp hrel).resolve_left hD
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hc0 : (α + 1) ≠ 0 := by simpa using hc 0
    have hP1 : jacobiPolyP α β (n + 1) x * ((n + 1) * n.factorial * (α + 1)) =
        poch (α + 1) n * (α + 1 + n) * (α + 1) *
          ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + 1 + α + β + 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [poch_succ, Nat.factorial_succ]
      push_cast
      field_simp
    have hP0 : jacobiPolyP α β n x * ((n + 1) * n.factorial * (α + 1)) =
        poch (α + 1) n * ((n + 1) * (α + 1)) *
          ₂F₁ (-((n : ℂ) + 1) + 1) ((n : ℂ) + 1 + α + β + 1 - 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [show (n : ℂ) + 1 + α + β + 1 - 1 = (n : ℂ) + α + β + 1 by ring,
        show -((n : ℂ) + 1) + 1 = -(n : ℂ) by ring]
      field_simp
    have hDd : deriv (jacobiPolyP α β (n + 1)) x * ((n + 1) * n.factorial * (α + 1)) =
        poch (α + 1) n * (α + 1 + n) * (-((n : ℂ) + 1) * ((n : ℂ) + 1 + α + β + 1)) * (-1 / 2) *
          ₂F₁ (-((n : ℂ) + 1) + 1) ((n : ℂ) + 1 + α + β + 1 + 1) (α + 1 + 1) ((1 - x) / 2) := by
      rw [(hasDerivAt_jacobiPolyP hα (n + 1) hx).deriv, poch_succ, Nat.factorial_succ]
      push_cast
      field_simp
    have hM : ((n : ℂ) + 1) * n.factorial * (α + 1) ≠ 0 := mul_ne_zero (mul_ne_zero hn1 hf) hc0
    apply mul_right_cancel₀ hM
    linear_combination ((2 * n + α + β + 2) * (1 - x ^ 2)) * hDd -
      ((n + 1) * (α - β - (2 * n + α + β + 2) * x)) * hP1 -
      (2 * (n + α + 1) * (n + β + 1)) * hP0 + (poch (α + 1) n) * hrel'
  exact congrFun key x

/-- Identity under the stated parameter and domain assumptions: `(2 * n + α + β + 2) * (1 - x ^ 2)
* deriv (jacobiPolyP α β n) x = (n + α + β + 1) * (α - β + (2 * n + α + β + 2) * x) *
jacobiPolyP α β n x - 2 * (n + 1) * (n + α + β + 1) * jacobiPolyP α β (n + 1) x`. -/
@[dlmf 18.9.E18]
theorem jacobi_raising_derivative {α β : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    (2 * n + α + β + 2) * (1 - x ^ 2) * deriv (jacobiPolyP α β n) x =
      (n + α + β + 1) * (α - β + (2 * n + α + β + 2) * x) * jacobiPolyP α β n x -
      2 * (n + 1) * (n + α + β + 1) * jacobiPolyP α β (n + 1) x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have key : (fun x : ℂ => (2 * n + α + β + 2) * (1 - x ^ 2) * deriv (jacobiPolyP α β n) x) =
      fun x => (n + α + β + 1) * (α - β + (2 * n + α + β + 2) * x) * jacobiPolyP α β n x -
        2 * (n + 1) * (n + α + β + 1) * jacobiPolyP α β (n + 1) x := by
    refine eq_of_eqOn_half_shift_disk ?_ (by intro x _; fun_prop) ?_
    · intro x _
      have hd : AnalyticAt ℂ (deriv (jacobiPolyP α β n)) x :=
        (analyticOnNhd_jacobiPolyP α β n).deriv x (Set.mem_univ x)
      fun_prop
    intro x hx
    have hrel := DLMF.Hypergeometric.contiguous_jacobi_raising (a := -(n : ℂ))
      (b := (n : ℂ) + α + β + 1) (c := α + 1) hc hx
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hD : (-(n : ℂ) - 2) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hrel' := (mul_eq_zero.mp hrel).resolve_left hD
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hc0 : (α + 1) ≠ 0 := by simpa using hc 0
    have hP0 : jacobiPolyP α β n x * ((n + 1) * n.factorial * (α + 1)) =
        poch (α + 1) n * ((n + 1) * (α + 1)) *
          ₂F₁ (-(n : ℂ)) ((n : ℂ) + α + β + 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      field_simp
    have hP1 : jacobiPolyP α β (n + 1) x * ((n + 1) * n.factorial * (α + 1)) =
        poch (α + 1) n * (α + 1 + n) * (α + 1) *
          ₂F₁ (-(n : ℂ) - 1) ((n : ℂ) + α + β + 1 + 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [poch_succ, Nat.factorial_succ]
      push_cast
      rw [show -((n : ℂ) + 1) = -(n : ℂ) - 1 by ring,
        show (n : ℂ) + 1 + α + β + 1 = (n : ℂ) + α + β + 1 + 1 by ring]
      field_simp
    have hDd : deriv (jacobiPolyP α β n) x * ((n + 1) * n.factorial * (α + 1)) =
        poch (α + 1) n * (n + 1) * (-(n : ℂ) * ((n : ℂ) + α + β + 1)) * (-1 / 2) *
          ₂F₁ (-(n : ℂ) + 1) ((n : ℂ) + α + β + 1 + 1) (α + 1 + 1) ((1 - x) / 2) := by
      rw [(hasDerivAt_jacobiPolyP hα n hx).deriv]
      field_simp
    have hM : ((n : ℂ) + 1) * n.factorial * (α + 1) ≠ 0 := mul_ne_zero (mul_ne_zero hn1 hf) hc0
    apply mul_right_cancel₀ hM
    linear_combination ((2 * n + α + β + 2) * (1 - x ^ 2)) * hDd -
      ((n + α + β + 1) * (α - β + (2 * n + α + β + 2) * x)) * hP0 +
      (2 * (n + 1) * (n + α + β + 1)) * hP1 + (poch (α + 1) n) * hrel'
  exact congrFun key x

/-- Identity under the stated parameter and domain assumptions: `deriv (ultrasphPoly lam (n + 1))
x = 2 * lam * ultrasphPoly (lam + 1) n x`. -/
@[dlmf 18.9.E19]
theorem ultrasphPoly_derivative {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    deriv (ultrasphPoly lam (n + 1)) x = 2 * lam * ultrasphPoly (lam + 1) n x := by
  have hc : ∀ k : ℕ, lam + 1 / 2 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith)
  have hc0 : lam + 1 / 2 ≠ 0 := by simpa using hc 0
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hp : poch (2 * lam) (n + 1) * (n + 1 + 2 * lam) =
      2 * lam * (2 * lam + 1) * poch (2 * lam + 2) n := by
    rw [poch_succ_left]
    have h := poch_succ (2 * lam + 1) n
    rw [poch_succ_left] at h
    rw [show 2 * lam + 1 + 1 = 2 * lam + 2 by ring] at h
    linear_combination -(2 * lam) * h
  have hf : poch (2 * lam) (n + 1) / ((n + 1).factorial : ℂ) * (-1 / 2) *
      (-(n + 1 : ℂ) * (n + 1 + 2 * lam) / (lam + 1 / 2)) =
      2 * lam * (poch (2 * (lam + 1)) n / (n.factorial : ℂ)) := by
    calc
      _ = (poch (2 * lam) (n + 1) * (n + 1 + 2 * lam)) /
          (2 * (lam + 1 / 2) * (n.factorial : ℂ)) := by
        rw [Nat.factorial_succ]
        push_cast
        field_simp
      _ = _ := by
        have h2 : 2 * lam + 1 ≠ 0 := by
          intro hz
          apply hc0
          linear_combination hz / 2
        rw [hp, show 2 * (lam + 1) = 2 * lam + 2 by ring,
          show 2 * (lam + 1 / 2) * (n.factorial : ℂ) = (2 * lam + 1) * n.factorial by ring,
          show 2 * lam * (2 * lam + 1) * poch (2 * lam + 2) n =
            (2 * lam + 1) * (2 * lam * poch (2 * lam + 2) n) by ring,
          mul_div_mul_left _ _ h2]
        ring
  have he : ultrasphPoly lam (n + 1) = fun z => poch (2 * lam) (n + 1) / ((n + 1).factorial : ℂ) *
      ₂F₁ (-((n + 1 : ℕ) : ℂ)) ((n + 1 : ℕ) + 2 * lam) (lam + 1 / 2) ((1 - z) / 2) := rfl
  rw [he]
  simp only [deriv_const_mul_field', deriv_half_shift, deriv_gauss_neg_nat_succ n _ hc]
  rw [ultrasphPoly]
  push_cast
  rw [show (n : ℂ) + 1 + 2 * lam + 1 = n + 2 * (lam + 1) by ring,
    show lam + 1 / 2 + 1 = (lam + 1) + 1 / 2 by ring]
  linear_combination (₂F₁ (-(n : ℂ)) (n + 2 * (lam + 1)) ((lam + 1) + 1 / 2) ((1 - x) / 2)) * hf

/-- The derivative formula for Kummer's entire series at regular lower parameters. -/
@[dlmf 13.3.E15]
theorem deriv_kummerM_regular {a c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    deriv (kummerM a c) = fun z => a / c * kummerM (a + 1) (c + 1) z :=
  funext fun z => DLMF.Confluent.deriv_kummerM hc (by simpa using hc 0)

/-- Identity under the stated parameter and domain assumptions: `deriv (laguerrePolyL α (n + 1)) x
= -laguerrePolyL (α + 1) n x`. -/
@[dlmf 18.9.E23]
theorem laguerrePolyL_derivative {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    deriv (laguerrePolyL α (n + 1)) x = -laguerrePolyL (α + 1) n x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hc0 : α + 1 ≠ 0 := by simpa using hc 0
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have he : laguerrePolyL α (n + 1) = fun z => poch (α + 1) (n + 1) / ((n + 1).factorial : ℂ) *
      kummerM (-((n + 1 : ℕ) : ℂ)) (α + 1) z := rfl
  rw [he]
  simp only [deriv_const_mul_field', deriv_kummerM_regular hc]
  rw [laguerrePolyL, poch_succ_left, Nat.factorial_succ]
  push_cast
  rw [show -((n : ℂ) + 1) + 1 = -(n : ℂ) by ring]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `deriv (fun t : ℝ => Real.exp (-(t
^ 2)) * aeval t (hermitePolyH n)) x = -Real.exp (-(x ^ 2)) * aeval x (hermitePolyH (n + 1))`. -/
@[dlmf 18.9.E26]
theorem hermitePolyH_weighted_derivative (n : ℕ) (x : ℝ) :
    deriv (fun t : ℝ => Real.exp (-(t ^ 2)) * aeval t (hermitePolyH n)) x =
      -Real.exp (-(x ^ 2)) * aeval x (hermitePolyH (n + 1)) := by
  have hd := (((hasDerivAt_id x).pow 2).neg.exp).fun_mul ((hermitePolyH n).hasDerivAt_aeval x)
  simp only [Pi.pow_apply, Pi.neg_apply, id_eq] at hd
  rw [hd.deriv]
  simp only [hermitePolyH_succ, map_sub, map_mul, map_ofNat, aeval_X, mul_one]
  ring

/-- Identity under the stated parameter and domain assumptions: `deriv (fun t : ℝ => Real.exp (-(t
^ 2) / 2) * aeval t (hermite n)) x = -Real.exp (-(x ^ 2) / 2) * aeval x (hermite (n + 1))`. -/
@[dlmf 18.9.E28]
theorem hermite_weighted_derivative (n : ℕ) (x : ℝ) :
    deriv (fun t : ℝ => Real.exp (-(t ^ 2) / 2) * aeval t (hermite n)) x =
      -Real.exp (-(x ^ 2) / 2) * aeval x (hermite (n + 1)) := by
  have hd := ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp).fun_mul ((hermite n).hasDerivAt_aeval x)
  simp only [Pi.pow_apply, Pi.neg_apply, id_eq] at hd
  rw [hd.deriv]
  simp only [hermite_succ, map_sub, map_mul, aeval_X, mul_one]
  ring

/-- The derivative of a Gegenbauer polynomial on the disk `‖(1-x)/2‖ < 1`. -/
theorem hasDerivAt_ultrasphPoly {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) {x : ℂ}
    (hx : ‖(1 - x) / 2‖ < 1) :
    HasDerivAt (ultrasphPoly lam n)
      (poch (2 * lam) n / n.factorial * (-(n : ℂ) * ((n : ℂ) + 2 * lam) / (lam + 1 / 2) *
        ₂F₁ (-(n : ℂ) + 1) ((n : ℂ) + 2 * lam + 1) (lam + 1 / 2 + 1) ((1 - x) / 2) * (-1 / 2))) x := by
  have hc : ∀ k : ℕ, lam + 1 / 2 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith)
  have hF := hasDerivAt_ordinaryHypergeometric (a := -(n : ℂ)) (b := (n : ℂ) + 2 * lam) hc hx
  have hin : HasDerivAt (fun x : ℂ => (1 - x) / 2) (-1 / 2) x :=
    ((hasDerivAt_id' x).const_sub 1).div_const 2
  exact (hF.comp x hin).const_mul (poch (2 * lam) n / n.factorial)

/-- The polynomial identity behind 18.9.16:
`(1-x²) P' + (β(1-x) - α(1+x)) P = -2(n+1) P^{(α-1,β-1)}_{n+1}`. -/
theorem jacobi_weighted_identity {α β : ℂ} (hα : 0 < α.re) (n : ℕ) (x : ℂ) :
    (1 - x ^ 2) * deriv (jacobiPolyP α β n) x + (β * (1 - x) - α * (1 + x)) * jacobiPolyP α β n x +
      2 * (n + 1) * jacobiPolyP (α - 1) (β - 1) (n + 1) x = 0 := by
  have hα' : -1 < α.re := by linarith
  have hc : ∀ k : ℕ, α ≠ -(k : ℂ) := not_neg_nat_of_re_pos hα
  have hc1 : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have key : (fun x : ℂ => (1 - x ^ 2) * deriv (jacobiPolyP α β n) x +
      (β * (1 - x) - α * (1 + x)) * jacobiPolyP α β n x +
      2 * (n + 1) * jacobiPolyP (α - 1) (β - 1) (n + 1) x) = fun _ => 0 := by
    refine eq_of_eqOn_half_shift_disk ?_ analyticOnNhd_const ?_
    · intro x _
      have hd : AnalyticAt ℂ (deriv (jacobiPolyP α β n)) x :=
        (analyticOnNhd_jacobiPolyP α β n).deriv x (Set.mem_univ x)
      fun_prop
    intro x hx
    have hdiag := DLMF.Hypergeometric.contiguous_diagonal (a := -((n : ℂ) + 1))
      (b := (n : ℂ) + α + β) (c := α) hc hx
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hc0 : (α + 1) ≠ 0 := by simpa using hc1 0
    have hP : jacobiPolyP α β n x * (n.factorial * (n + 1) * (α + 1)) =
        poch (α + 1) n * (n + 1) * (α + 1) *
          ₂F₁ (-((n : ℂ) + 1) + 1) ((n : ℂ) + α + β + 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [show -((n : ℂ) + 1) + 1 = -(n : ℂ) by ring]
      field_simp
    have hD : deriv (jacobiPolyP α β n) x * (n.factorial * (n + 1) * (α + 1)) =
        poch (α + 1) n * (n + 1) * (-(n : ℂ) * ((n : ℂ) + α + β + 1)) * (-1 / 2) *
          ₂F₁ (-((n : ℂ) + 1) + 2) ((n : ℂ) + α + β + 2) (α + 2) ((1 - x) / 2) := by
      rw [(hasDerivAt_jacobiPolyP hα' n hx).deriv, show -((n : ℂ) + 1) + 2 = -(n : ℂ) + 1 by ring,
        show (n : ℂ) + α + β + 2 = (n : ℂ) + α + β + 1 + 1 by ring, show α + 2 = α + 1 + 1 by ring]
      field_simp
    have hQ : jacobiPolyP (α - 1) (β - 1) (n + 1) x * (n.factorial * (n + 1) * (α + 1)) =
        α * poch (α + 1) n * (α + 1) *
          ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + α + β) α ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [show α - 1 + 1 = α by ring, poch_succ_left, Nat.factorial_succ]
      push_cast
      rw [show (n : ℂ) + 1 + (α - 1) + (β - 1) + 1 = (n : ℂ) + α + β by ring]
      field_simp
    have hM : (n.factorial : ℂ) * (n + 1) * (α + 1) ≠ 0 := mul_ne_zero (mul_ne_zero hf hn1) hc0
    have : ((1 - x ^ 2) * deriv (jacobiPolyP α β n) x + (β * (1 - x) - α * (1 + x))
        * jacobiPolyP α β n x +
        2 * (n + 1) * jacobiPolyP (α - 1) (β - 1) (n + 1) x) * (n.factorial * (n + 1) * (α + 1))
            = 0 := by
      linear_combination (1 - x ^ 2) * hD + (β * (1 - x) - α * (1 + x)) * hP + (2 * (n + 1)) * hQ +
        (-2 * poch (α + 1) n * (n + 1)) * hdiag
    exact (mul_eq_zero.mp this).resolve_right hM
  exact congrFun key x

/-- The polynomial identity behind 18.9.20, multiplied by `2(λ-1)`:
`2(λ-1)((1-x²) C' - (2λ-1) x C) + (n+1)(n+2λ-1) C^{λ-1}_{n+1} = 0`. -/
theorem ultrasphPoly_weighted_identity {lam : ℂ} (hlam : 1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    2 * (lam - 1)
        * ((1 - x ^ 2) * deriv (ultrasphPoly lam n) x - (2 * lam - 1) * x * ultrasphPoly lam n x) +
      (n + 1) * (n + 2 * lam - 1) * ultrasphPoly (lam - 1) (n + 1) x = 0 := by
  have hlam' : -1 / 2 < lam.re := by linarith
  have hc : ∀ k : ℕ, lam - 1 / 2 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith)
  have hc1 : ∀ k : ℕ, lam + 1 / 2 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith)
  have key : (fun x : ℂ => 2 * (lam - 1) * ((1 - x ^ 2) * deriv (ultrasphPoly lam n) x -
      (2 * lam - 1) * x * ultrasphPoly lam n x) +
      (n + 1) * (n + 2 * lam - 1) * ultrasphPoly (lam - 1) (n + 1) x) = fun _ => 0 := by
    refine eq_of_eqOn_half_shift_disk ?_ analyticOnNhd_const ?_
    · intro x _
      have hd : AnalyticAt ℂ (deriv (ultrasphPoly lam n)) x :=
        (analyticOnNhd_ultrasphPoly lam n).deriv x (Set.mem_univ x)
      fun_prop
    intro x hx
    have hdiag := DLMF.Hypergeometric.contiguous_diagonal (a := -((n : ℂ) + 1))
      (b := (n : ℂ) + 2 * lam - 1) (c := lam - 1 / 2) hc hx
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hc0 : (lam + 1 / 2) ≠ 0 := by simpa using hc1 0
    have hN : (2 * lam - 1 + (n : ℂ)) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h2 : (2 * lam + 1) ≠ 0 := by
      intro h
      apply hc0
      linear_combination h / 2
    have hpq : poch (2 * (lam - 1)) (n + 1) * (2 * lam - 1 + n) =
        2 * (lam - 1) * (2 * lam - 1) * poch (2 * lam) n := by
      rw [poch_succ_left, show 2 * (lam - 1) + 1 = 2 * lam - 1 by ring, mul_assoc, ← poch_succ,
        poch_succ_left, show 2 * lam - 1 + 1 = 2 * lam by ring]
      ring
    have hM : (n.factorial : ℂ) * (n + 1) * (lam + 1 / 2) * (2 * lam - 1 + n) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hf hn1) hc0) hN
    have hP : ultrasphPoly lam n x * (n.factorial * (n + 1) * (lam + 1 / 2) * (2 * lam - 1 + n)) =
        poch (2 * lam) n * (n + 1) * (lam + 1 / 2) * (2 * lam - 1 + n) *
          ₂F₁ (-((n : ℂ) + 1) + 1) ((n : ℂ) + 2 * lam - 1 + 1) (lam - 1 / 2 + 1) ((1 - x) / 2) := by
      unfold ultrasphPoly
      rw [show -((n : ℂ) + 1) + 1 = -(n : ℂ) by ring,
        show (n : ℂ) + 2 * lam - 1 + 1 = (n : ℂ) + 2 * lam by ring,
        show lam - 1 / 2 + 1 = lam + 1 / 2 by ring]
      field_simp
    have hD : deriv (ultrasphPoly lam n) x
        * (n.factorial * (n + 1) * (lam + 1 / 2) * (2 * lam - 1 + n)) =
        poch (2 * lam) n * (n + 1) * (-(n : ℂ) * ((n : ℂ) + 2 * lam)) * (-1 / 2) * (2 * lam - 1 + n) *
          ₂F₁ (-((n : ℂ) + 1) + 2) ((n : ℂ) + 2 * lam - 1 + 2) (lam - 1 / 2 + 2) ((1 - x) / 2) := by
      rw [(hasDerivAt_ultrasphPoly hlam' n hx).deriv,
        show -((n : ℂ) + 1) + 2 = -(n : ℂ) + 1 by ring,
        show (n : ℂ) + 2 * lam - 1 + 2 = (n : ℂ) + 2 * lam + 1 by ring,
        show lam - 1 / 2 + 2 = lam + 1 / 2 + 1 by ring]
      field_simp
    have hQ' : ultrasphPoly (lam - 1) (n + 1) x * ((n + 1) * n.factorial) =
        poch (2 * (lam - 1)) (n + 1) *
          ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + 2 * lam - 1) (lam - 1 / 2) ((1 - x) / 2) := by
      unfold ultrasphPoly
      rw [Nat.factorial_succ]
      push_cast
      rw [show (n : ℂ) + 1 + 2 * (lam - 1) = (n : ℂ) + 2 * lam - 1 by ring,
        show lam - 1 + 1 / 2 = lam - 1 / 2 by ring]
      field_simp
    have hQ : ultrasphPoly (lam - 1) (n + 1) x
        * (n.factorial * (n + 1) * (lam + 1 / 2) * (2 * lam - 1 + n)) =
        2 * (lam - 1) * (2 * lam - 1) * poch (2 * lam) n * (lam + 1 / 2) *
          ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + 2 * lam - 1) (lam - 1 / 2) ((1 - x) / 2) := by
      linear_combination ((lam + 1 / 2) * (2 * lam - 1 + n)) * hQ' + ((lam + 1 / 2) *
        ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + 2 * lam - 1) (lam - 1 / 2) ((1 - x) / 2)) * hpq
    have : (2 * (lam - 1) * ((1 - x ^ 2) * deriv (ultrasphPoly lam n) x -
        (2 * lam - 1) * x * ultrasphPoly lam n x) +
        (n + 1) * (n + 2 * lam - 1) * ultrasphPoly (lam - 1) (n + 1) x) *
        (n.factorial * (n + 1) * (lam + 1 / 2) * (2 * lam - 1 + n)) = 0 := by
      linear_combination (2 * (lam - 1) * (1 - x ^ 2)) * hD - (2 * (lam - 1) * (2 * lam - 1) * x) * hP +
        ((n + 1) * (n + 2 * lam - 1)) * hQ +
        (-4 * (lam - 1) * poch (2 * lam) n * (n + 1) * (2 * lam - 1 + n)) * hdiag
    exact (mul_eq_zero.mp this).resolve_right hM
  exact congrFun key x

/-- Identity under the stated parameter and domain assumptions: `deriv (fun t : ℝ => (1 - (t : ℂ))
^ (α : ℂ) * (1 + (t : ℂ)) ^ (β : ℂ) * jacobiPolyP α β n t) x = -2 * (n + 1) * (1 - (x : ℂ)) ^
((α : ℂ) - 1) * (1 + (x : ℂ)) ^ ((β : ℂ) - 1) * jacobiPolyP (α - 1) (β - 1) (n + 1) x`. -/
@[dlmf 18.9.E16]
theorem jacobi_weighted_derivative {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    deriv (fun t : ℝ => (1 - (t : ℂ)) ^ (α : ℂ) * (1 + (t : ℂ)) ^ (β : ℂ) * jacobiPolyP α β n t) x =
      -2 * (n + 1) * (1 - (x : ℂ)) ^ ((α : ℂ) - 1) * (1 + (x : ℂ)) ^ ((β : ℂ) - 1) *
        jacobiPolyP (α - 1) (β - 1) (n + 1) x := by
  obtain ⟨hx1, hx2⟩ := hx
  have h1 : (1 - (x : ℂ)) ∈ slitPlane := by
    rw [show (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_mem_slitPlane.mpr (by linarith)
  have h2 : (1 + (x : ℂ)) ∈ slitPlane := by
    rw [show (1 + (x : ℂ)) = ((1 + x : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_mem_slitPlane.mpr (by linarith)
  have hne1 : (1 - (x : ℂ)) ≠ 0 := slitPlane_ne_zero h1
  have hne2 : (1 + (x : ℂ)) ≠ 0 := slitPlane_ne_zero h2
  have hA : HasDerivAt (fun t : ℝ => (1 - (t : ℂ)) ^ (α : ℂ))
      ((α : ℂ) * (1 - (x : ℂ)) ^ ((α : ℂ) - 1) * (-1)) x :=
    ((((hasDerivAt_id' (x : ℂ)).const_sub 1).cpow_const (c := (α : ℂ)) h1)).comp_ofReal
  have hB : HasDerivAt (fun t : ℝ => (1 + (t : ℂ)) ^ (β : ℂ))
      ((β : ℂ) * (1 + (x : ℂ)) ^ ((β : ℂ) - 1) * 1) x :=
    ((((hasDerivAt_id' (x : ℂ)).const_add 1).cpow_const (c := (β : ℂ)) h2)).comp_ofReal
  have hP : HasDerivAt (fun t : ℝ => jacobiPolyP α β n t) (deriv (jacobiPolyP α β n) x) x :=
    ((analyticOnNhd_jacobiPolyP α β n) x (Set.mem_univ _)).differentiableAt.hasDerivAt.comp_ofReal
  have hprod := (hA.mul hB).mul hP
  change deriv (((fun t : ℝ => (1 - (t : ℂ)) ^ (α : ℂ)) * fun t : ℝ => (1 + (t : ℂ)) ^ (β : ℂ)) *
    fun t : ℝ => jacobiPolyP α β n t) x = _
  rw [hprod.deriv]
  simp only [Pi.mul_apply]
  have hid := jacobi_weighted_identity (α := α) (β := β) (by simpa using hα) n x
  have hpowA : (1 - (x : ℂ)) ^ (α : ℂ) = (1 - (x : ℂ)) ^ ((α : ℂ) - 1) * (1 - x) := by
    rw [Complex.cpow_sub _ _ hne1, Complex.cpow_one]
    field_simp
  have hpowB : (1 + (x : ℂ)) ^ (β : ℂ) = (1 + (x : ℂ)) ^ ((β : ℂ) - 1) * (1 + x) := by
    rw [Complex.cpow_sub _ _ hne2, Complex.cpow_one]
    field_simp
  rw [hpowA, hpowB]
  linear_combination ((1 - (x : ℂ)) ^ ((α : ℂ) - 1) * (1 + (x : ℂ)) ^ ((β : ℂ) - 1)) * hid

/-- Identity under the stated parameter and domain assumptions: `deriv (fun t : ℝ => (1 - (t : ℂ)
^ 2) ^ ((lam : ℂ) - 1 / 2) * ultrasphPoly lam n t) x = -(n + 1) * (n + 2 * (lam : ℂ) - 1) / (2
* (lam - 1)) * (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 3 / 2) * ultrasphPoly (lam - 1) (n + 1) x`. -/
@[dlmf 18.9.E20]
theorem ultrasphPoly_weighted_derivative {lam : ℝ} (hlam : 1 / 2 < lam) (hlam1 : lam ≠ 1)
    (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    deriv (fun t : ℝ => (1 - (t : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2) * ultrasphPoly lam n t) x =
      -(n + 1) * (n + 2 * (lam : ℂ) - 1) / (2 * (lam - 1)) *
        (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 3 / 2) * ultrasphPoly (lam - 1) (n + 1) x := by
  obtain ⟨hx1, hx2⟩ := hx
  have h1 : (1 - (x : ℂ) ^ 2) ∈ slitPlane := by
    rw [show (1 - (x : ℂ) ^ 2) = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_mem_slitPlane.mpr (by nlinarith)
  have hne1 : (1 - (x : ℂ) ^ 2) ≠ 0 := slitPlane_ne_zero h1
  have hsq : HasDerivAt (fun w : ℂ => 1 - w ^ 2) (-(2 * (x : ℂ))) x := by
    simpa using (hasDerivAt_pow 2 (x : ℂ)).const_sub 1
  have hA : HasDerivAt (fun t : ℝ => (1 - (t : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2))
      (((lam : ℂ) - 1 / 2) * (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2 - 1) * -(2 * (x : ℂ))) x :=
    (hsq.cpow_const (c := (lam : ℂ) - 1 / 2) h1).comp_ofReal
  have hC : HasDerivAt (fun t : ℝ => ultrasphPoly lam n t) (deriv (ultrasphPoly lam n) x) x :=
    ((analyticOnNhd_ultrasphPoly lam n) x (Set.mem_univ _)).differentiableAt.hasDerivAt.comp_ofReal
  have hprod := hA.mul hC
  change deriv ((fun t : ℝ => (1 - (t : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2)) *
    fun t : ℝ => ultrasphPoly lam n t) x = _
  rw [hprod.deriv]
  have hid := ultrasphPoly_weighted_identity (lam := lam) (by simpa using hlam) n x
  have h2 : (2 * ((lam : ℂ) - 1)) ≠ 0 := by
    have : (lam : ℂ) - 1 ≠ 0 := by
      intro h
      apply hlam1
      exact_mod_cast (sub_eq_zero.mp h)
    exact mul_ne_zero two_ne_zero this
  have hpow : (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2) =
      (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 3 / 2) * (1 - (x : ℂ) ^ 2) := by
    rw [show (lam : ℂ) - 3 / 2 = (lam : ℂ) - 1 / 2 - 1 by ring,
      Complex.cpow_sub ((lam : ℂ) - 1 / 2) 1 hne1, Complex.cpow_one]
    field_simp
  rw [hpow, show (lam : ℂ) - 1 / 2 - 1 = (lam : ℂ) - 3 / 2 by ring, div_mul_eq_mul_div,
    div_mul_eq_mul_div, eq_div_iff h2]
  linear_combination ((1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 3 / 2)) * hid

/-- Identity under the stated parameter and domain assumptions: `deriv (fun t : ℝ => Real.sqrt (1
- t ^ 2) * (Chebyshev.U ℝ n).eval t) x = -(n + 1) / Real.sqrt (1 - x ^ 2) * (Chebyshev.T ℝ (n
+ 1)).eval x`. -/
@[dlmf 18.9.E22]
theorem chebyshevU_weighted_derivative (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    deriv (fun t : ℝ => Real.sqrt (1 - t ^ 2) * (Chebyshev.U ℝ n).eval t) x =
      -(n + 1) / Real.sqrt (1 - x ^ 2) * (Chebyshev.T ℝ (n + 1)).eval x := by
  obtain ⟨hx1, hx2⟩ := hx
  have hpos : 0 < 1 - x ^ 2 := by nlinarith
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hsq : Real.sqrt (1 - x ^ 2) * Real.sqrt (1 - x ^ 2) = 1 - x ^ 2 := Real.mul_self_sqrt hpos.le
  have hin : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_sub 1
  have hS : HasDerivAt (fun t : ℝ => Real.sqrt (1 - t ^ 2))
      (-(2 * x) / (2 * Real.sqrt (1 - x ^ 2))) x :=
    hin.sqrt hpos.ne'
  have hU : HasDerivAt (fun t : ℝ => (Chebyshev.U ℝ n).eval t)
      ((Chebyshev.U ℝ n).derivative.eval x) x :=
    Polynomial.hasDerivAt _ x
  have hprod := hS.mul hU
  change deriv ((fun t : ℝ => Real.sqrt (1 - t ^ 2)) * fun t : ℝ => (Chebyshev.U ℝ n).eval t) x = _
  rw [hprod.deriv]
  have hid := congrArg (Polynomial.eval x) (Polynomial.Chebyshev.add_one_mul_T_eq_poly_in_U (R := ℝ) n)
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_intCast] at hid
  push_cast at hid ⊢
  field_simp
  linear_combination hid + ((Chebyshev.U ℝ n).derivative.eval x) * hsq

/-- The polynomial identity behind 18.9.24: `x L' + (α - x) L = (n+1) L^{(α-1)}_{n+1}`, from the
Kummer relation 13.3.13. -/
theorem laguerrePolyL_weighted_identity {α : ℂ} (hα : 0 < α.re) (n : ℕ) (x : ℂ) :
    x * deriv (laguerrePolyL α n) x + (α - x) * laguerrePolyL α n x = (n + 1)
        * laguerrePolyL (α - 1) (n + 1) x := by
  have hb : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hb' : ∀ k : ℕ, α ≠ -(k : ℂ) := not_neg_nat_of_re_pos hα
  have hb0 : α + 1 ≠ 0 := by simpa using hb 0
  have hMd : DifferentiableAt ℂ (kummerM (-(n : ℂ)) (α + 1)) x :=
    ((hasFPowerSeriesOnBall_kummerM (a := -(n : ℂ)) hb).analyticAt_of_mem
      (by simp : x ∈ Metric.eball (0 : ℂ) ⊤)).differentiableAt
  have hderiv : deriv (laguerrePolyL α n) x =
      poch (α + 1) n / n.factorial
          * (-(n : ℂ) / (α + 1) * kummerM (-(n : ℂ) + 1) (α + 1 + 1) x) := by
    show deriv (fun x => poch (α + 1) n / n.factorial * kummerM (-(n : ℂ)) (α + 1) x) x = _
    rw [deriv_const_mul _ hMd, DLMF.Confluent.deriv_kummerM hb hb0]
  have hode := DLMF.Confluent.kummerM_ode_contiguous (a := -((n : ℂ) + 1)) (b := α) (z := x) hb'
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hM : (n.factorial : ℂ) * (n + 1) * (α + 1) ≠ 0 := mul_ne_zero (mul_ne_zero hf hn1) hb0
  have hL : laguerrePolyL α n x * (n.factorial * (n + 1) * (α + 1)) =
      poch (α + 1) n * (n + 1) * (α + 1) * kummerM (-((n : ℂ) + 1) + 1) (α + 1) x := by
    unfold laguerrePolyL
    rw [show -((n : ℂ) + 1) + 1 = -(n : ℂ) by ring]
    field_simp
  have hD : deriv (laguerrePolyL α n) x * (n.factorial * (n + 1) * (α + 1)) =
      poch (α + 1) n * (n + 1) * (-(n : ℂ)) * kummerM (-((n : ℂ) + 1) + 2) (α + 2) x := by
    rw [hderiv, show -((n : ℂ) + 1) + 2 = -(n : ℂ) + 1 by ring, show α + 2 = α + 1 + 1 by ring]
    field_simp
  have hQ : laguerrePolyL (α - 1) (n + 1) x * (n.factorial * (n + 1) * (α + 1)) =
      α * poch (α + 1) n * (α + 1) * kummerM (-((n : ℂ) + 1)) α x := by
    unfold laguerrePolyL
    rw [show α - 1 + 1 = α by ring, poch_succ_left, Nat.factorial_succ]
    push_cast
    field_simp
  apply mul_right_cancel₀ hM
  linear_combination x * hD + (α - x) * hL - (n + 1) * hQ + (poch (α + 1) n * (n + 1)) * hode

/-- Identity under the stated parameter and domain assumptions: `deriv (fun t : ℝ => exp (-t) * (t
: ℂ) ^ (α : ℂ) * laguerrePolyL α n t) x = (n + 1) * exp (-x) * (x : ℂ) ^ ((α : ℂ) - 1) *
laguerrePolyL (α - 1) (n + 1) x`. -/
@[dlmf 18.9.E24]
theorem laguerrePolyL_weighted_derivative {α : ℝ} (hα : 0 < α) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    deriv (fun t : ℝ => exp (-t) * (t : ℂ) ^ (α : ℂ) * laguerrePolyL α n t) x =
      (n + 1) * exp (-x) * (x : ℂ) ^ ((α : ℂ) - 1) * laguerrePolyL (α - 1) (n + 1) x := by
  have hxs : (x : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hx
  have hx0 : (x : ℂ) ≠ 0 := slitPlane_ne_zero hxs
  have hb : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith)
  have hMd : DifferentiableAt ℂ (kummerM (-(n : ℂ)) ((α : ℂ) + 1)) x :=
    ((hasFPowerSeriesOnBall_kummerM (a := -(n : ℂ)) hb).analyticAt_of_mem
      (by simp : (x : ℂ) ∈ Metric.eball (0 : ℂ) ⊤)).differentiableAt
  have hLd : DifferentiableAt ℂ (laguerrePolyL α n) x := by
    show DifferentiableAt ℂ (fun x => poch ((α : ℂ) + 1) n / n.factorial *
      kummerM (-(n : ℂ)) ((α : ℂ) + 1) x) x
    exact hMd.const_mul _
  have hE : HasDerivAt (fun t : ℝ => exp (-(t : ℂ))) (exp (-(x : ℂ)) * -1) x :=
    ((hasDerivAt_id' (x : ℂ)).neg.cexp).comp_ofReal
  have hT : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (α : ℂ)) ((α : ℂ) * (x : ℂ) ^ ((α : ℂ) - 1) * 1) x :=
    ((hasDerivAt_id' (x : ℂ)).cpow_const (c := (α : ℂ)) hxs).comp_ofReal
  have hL : HasDerivAt (fun t : ℝ => laguerrePolyL α n t) (deriv (laguerrePolyL α n) x) x :=
    hLd.hasDerivAt.comp_ofReal
  have hprod := (hE.mul hT).mul hL
  change deriv (((fun t : ℝ => exp (-(t : ℂ))) * fun t : ℝ => (t : ℂ) ^ (α : ℂ)) *
    fun t : ℝ => laguerrePolyL α n t) x = _
  rw [hprod.deriv]
  simp only [Pi.mul_apply]
  have hid := laguerrePolyL_weighted_identity (α := α) (by simpa using hα) n x
  have hpow : (x : ℂ) ^ (α : ℂ) = (x : ℂ) ^ ((α : ℂ) - 1) * x := by
    rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one]
    field_simp
  rw [hpow]
  linear_combination (exp (-(x : ℂ)) * (x : ℂ) ^ ((α : ℂ) - 1)) * hid

end DLMF.OrthogonalPolynomials

end
end
