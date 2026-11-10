/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.AsymptoticsZeros
public import DLMFMathlib.Analysis.ODE.SturmCount

/-!
# Positive real zeros of the cylinder functions and their derivatives

Sturm comparison gives arbitrarily many positive zeros of `U(-μ²/2,x)` as `μ` tends to
infinity. The positive zeros of `U` and `U'` form finite sets for each real parameter.
These facts justify enumeration from the largest zero in DLMF §12.11.
-/

@[expose] public noncomputable section

open Complex Filter Set Asymptotics
open scoped Topology

namespace DLMF.Confluent.CylinderRealZeros

/-- The real zeros of `U(a,·)` above any fixed point form a finite set. -/
theorem finite_zeros_Ioi (a c : ℝ) :
    {x : ℝ | c < x ∧ parabolicCylinderU a x = 0}.Finite := by
  let X : ℝ := 2 * (|a| + 1)
  have hfar : ∀ x, X ≤ x → (parabolicCylinderU a x).re ≠ 0 :=
    no_zero_far (fun x hx => by
      have habs := neg_abs_le a
      have ha0 := abs_nonneg a
      dsimp [X] at hx
      nlinarith)
  have hfin := ODE.SturmDeformation.finite (a := c) (b := X)
    (fun x _ => hasDerivAt_re a x) (fun x _ hx => zero_simple a x hx)
  refine hfin.subset fun x hx => ⟨⟨hx.1.le, ?_⟩, (re_eq_zero_iff a x).mpr hx.2⟩
  by_contra h
  exact hfar x (le_of_not_ge h) ((re_eq_zero_iff a x).mpr hx.2)

/-- The real zeros of `U'(a,·)` above any fixed point form a finite set. -/
theorem finite_derivative_zeros_Ioi (a c : ℝ) :
    {x : ℝ | c < x ∧ parabolicCylinderUDeriv a x = 0}.Finite := by
  have hq : {x : ℝ | x ^ 2 / 4 + a = 0}.Finite := by
    have hp : (Polynomial.X ^ 2 + Polynomial.C (4*a) : Polynomial ℝ) ≠ 0 := by
      intro h
      have := congrArg (fun p : Polynomial ℝ => p.coeff 2) h
      norm_num at this
    refine (Polynomial.finite_setOfPred_isRoot hp).subset fun x hx => ?_
    change Polynomial.eval x (Polynomial.X ^ 2 + Polynomial.C (4*a)) = 0
    rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    change x ^ 2 / 4 + a = 0 at hx
    nlinarith [hx]
  have hfin : {x : ℝ | c < x ∧ (x^2/4+a)*(parabolicCylinderU a x).re = 0}.Finite := by
    refine (hq.union (finite_zeros_Ioi a c)).subset fun x hx => ?_
    rcases mul_eq_zero.mp hx.2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hx.1, (re_eq_zero_iff a x).mp h⟩
  by_contra hinf
  have hinf' : {x : ℝ | x ∈ Ioi c ∧ (parabolicCylinderUDeriv a x).re = 0}.Infinite := by
    refine Set.Infinite.mono (s := {x : ℝ | c < x ∧ parabolicCylinderUDeriv a x = 0})
      (fun x hx => ⟨hx.1, ?_⟩) hinf
    rw [hx.2, Complex.zero_re]
  exact (ODE.sturmCount_infinite_deriv_zeros (s := Ioi c) (f := fun x : ℝ =>
    (parabolicCylinderUDeriv a x).re) ordConnected_Ioi
    (fun x _ => hasDerivAt_deriv_re a x) hinf') hfin

set_option maxHeartbeats 800000 in
/-- For large `μ`, `U(-μ²/2,·)` has a positive zero in each of the first `n` sine intervals. -/
theorem eventually_strictMono_positive_zeros (n : ℕ) :
    ∀ᶠ μ : ℝ in atTop, ∃ z : Fin n → ℝ, StrictMono z ∧
      (∀ j, 0 < z j) ∧ ∀ j, parabolicCylinderU ((-μ^2/2:ℝ):ℂ) (z j) = 0 := by
  filter_upwards [eventually_gt_atTop ((n:ℝ)*Real.pi+3)] with μ hμ
  have hπ := Real.pi_pos
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hzero : ∀ j : Fin n, ∃ x ∈ Ioo ((j:ℕ)*Real.pi) (((j:ℕ)+1)*Real.pi),
      (parabolicCylinderU ((-μ^2/2:ℝ):ℂ) x).re = 0 := by
    intro j
    have hab : ((j:ℕ):ℝ)*Real.pi < ((j:ℕ)+1)*Real.pi := by nlinarith
    refine ODE.sturm_comparison_strict (p := fun _ => 1) (q₁ := fun _ => 1)
      (q₂ := fun x => μ^2/2-x^2/4) (u := Real.sin) (u' := Real.cos)
      (v := fun x : ℝ => (parabolicCylinderU ((-μ^2/2:ℝ):ℂ) x).re)
      (v' := fun x : ℝ => (parabolicCylinderUDeriv ((-μ^2/2:ℝ):ℂ) x).re) hab
      (fun x _ => Real.hasDerivAt_sin x) (fun x _ => by simpa using Real.hasDerivAt_cos x)
      (fun x _ => hasDerivAt_re (-μ^2/2) x) (fun x _ => ?_)
      zero_le_one zero_le_one (fun x hx => ?_) (Real.sin_nat_mul_pi j)
      (by exact_mod_cast Real.sin_nat_mul_pi (j+1)) (fun x hx => ?_)
    · simpa only [one_mul] using (hasDerivAt_deriv_re (-μ^2/2) x).congr_deriv (by ring)
    · have hj : ((j:ℕ):ℝ)+1 ≤ n := by exact_mod_cast j.isLt
      have hx0 : 0 ≤ x := le_trans (by positivity) hx.1.le
      have hxN : x < (n:ℝ)*Real.pi := hx.2.trans_le (by gcongr)
      nlinarith
    · intro hs
      obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs
      have h1 : ((j:ℕ):ℝ) < k := (mul_lt_mul_iff_left₀ hπ).mp (by linarith [hx.1])
      have h2 : (k:ℝ) < (j:ℕ)+1 := (mul_lt_mul_iff_left₀ hπ).mp (by linarith [hx.2])
      have h1' : ((j:ℕ):ℤ) < k := by exact_mod_cast h1
      have h2' : k < ((j:ℕ):ℤ)+1 := by exact_mod_cast h2
      omega
  choose z hz hz0 using hzero
  refine ⟨z, ?_, fun j => lt_of_le_of_lt (by positivity) (hz j).1,
    fun j => by simpa using (re_eq_zero_iff _ _).mp (hz0 j)⟩
  intro i j hij
  have hij' : ((i:ℕ):ℝ)+1 ≤ j := by exact_mod_cast hij
  have hle : (((i:ℕ):ℝ)+1)*Real.pi ≤ (j:ℕ)*Real.pi := by gcongr
  exact ((hz i).2.trans_le hle).trans (hz j).1

/-- For large `μ`, the derivative of `U(-μ²/2,·)` has any prescribed number of positive zeros.
-/
theorem eventually_strictMono_positive_derivative_zeros (n : ℕ) :
    ∀ᶠ μ : ℝ in atTop, ∃ z : Fin n → ℝ, StrictMono z ∧
      (∀ j, 0 < z j) ∧ ∀ j, parabolicCylinderUDeriv ((-μ^2/2:ℝ):ℂ) (z j) = 0 := by
  filter_upwards [eventually_strictMono_positive_zeros (n+1)] with μ hμ
  obtain ⟨e, he, hepos, hezero⟩ := hμ
  have hezero' : ∀ j, (parabolicCylinderU ((-μ^2/2:ℝ):ℂ) (e j)).re = 0 := by
    intro j
    have h := congrArg Complex.re (hezero j)
    simpa using h
  have hrolle : ∀ j : Fin n, ∃ c ∈ Ioo (e j.castSucc) (e j.succ),
      (parabolicCylinderUDeriv ((-μ^2/2:ℝ):ℂ) c).re = 0 := by
    intro j
    exact exists_hasDerivAt_eq_zero (he Fin.castSucc_lt_succ)
      (fun t _ => (hasDerivAt_re (-μ^2/2) t).continuousAt.continuousWithinAt)
      (by rw [hezero', hezero']) (fun t _ => hasDerivAt_re (-μ^2/2) t)
  choose c hc hc0 using hrolle
  refine ⟨c, ?_, fun j => (hepos j.castSucc).trans (hc j).1, fun j => ?_⟩
  · intro i j hij
    exact ((hc i).2.trans_le (he.monotone (Fin.succ_le_castSucc_iff.mpr hij))).trans (hc j).1
  · have h : parabolicCylinderUDeriv ((-μ^2/2:ℝ):ℂ) (c j) = 0 := by
      rw [deriv_eq_re, hc0 j, Complex.ofReal_zero]
    simpa using h

end DLMF.Confluent.CylinderRealZeros
