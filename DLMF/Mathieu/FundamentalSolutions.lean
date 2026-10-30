/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import DLMFMathlib.Analysis.ODE.P1oEntireLinear
public import DLMFMathlib.Analysis.ODE.P1oParamHolomorphic
public import DLMFMathlib.Analysis.ODE.P2sSturmSpectrum
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

/-!
# Existence, uniqueness and normalization of fundamental Mathieu solutions
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real Classical

namespace DLMF.Mathieu

namespace IsMathieuSolution

variable {a q : ℂ} {w v : ℂ → ℂ}

/-- The second derivative of a solution of Mathieu's equation (DLMF 28.2.1). -/
theorem deriv_deriv (h : IsMathieuSolution a q w) (z : ℂ) :
    deriv (deriv w) z = (2 * q * Complex.cos (2 * z) - a) * w z :=
  (h.hasDerivAt_deriv z).deriv

/-- The derivative of a solution of Mathieu's equation is entire. -/
theorem differentiable_deriv (h : IsMathieuSolution a q w) : Differentiable ℂ (deriv w) :=
  fun z => (h.hasDerivAt_deriv z).differentiableAt

/-- Solutions of Mathieu's equation form a vector space: scalar multiples. -/
theorem const_mul (h : IsMathieuSolution a q w) (c : ℂ) :
    IsMathieuSolution a q (fun z => c * w z) := by
  have hd : deriv (fun z => c * w z) = fun z => c * deriv w z := by
    funext z; exact ((h.differentiable z).hasDerivAt.const_mul c).deriv
  refine ⟨fun z => (h.differentiable z).const_mul c, fun z => ?_⟩
  rw [hd]
  convert (h.hasDerivAt_deriv z).const_mul c using 1
  ring

/-- Solutions of Mathieu's equation form a vector space: sums. -/
theorem add (h : IsMathieuSolution a q w) (h' : IsMathieuSolution a q v) :
    IsMathieuSolution a q (fun z => w z + v z) := by
  have hd : deriv (fun z => w z + v z) = fun z => deriv w z + deriv v z := by
    funext z; exact ((h.differentiable z).hasDerivAt.add (h'.differentiable z).hasDerivAt).deriv
  refine ⟨fun z => (h.differentiable z).add (h'.differentiable z), fun z => ?_⟩
  rw [hd]
  convert (h.hasDerivAt_deriv z).add (h'.hasDerivAt_deriv z) using 1
  ring

/-- **Uniqueness** (DLMF §28.2(ii)): a solution of Mathieu's equation is determined by its value
and derivative at one point `z₀`. Proved from the uniqueness of analytic solutions of linear
second-order equations (`ODE.eqOn_of_ode`). -/
theorem eq_of_initial (h : IsMathieuSolution a q w) (h' : IsMathieuSolution a q v) {z₀ : ℂ}
    (h₀ : w z₀ = v z₀) (h₁ : deriv w z₀ = deriv v z₀) : w = v := by
  have hp : ContDiffAt ℂ (⊤ : ℕ∞) (fun _ : ℂ => (0 : ℂ)) z₀ := contDiffAt_const
  have hq : ContDiffAt ℂ (⊤ : ℕ∞) (fun z : ℂ => 2 * q * Complex.cos (2 * z) - a) z₀ := by
    fun_prop
  have key := ODE.eqOn_of_ode (U := univ) isOpen_univ isPreconnected_univ
    (fun z _ => h.differentiable.analyticAt z) (fun z _ => h'.differentiable.analyticAt z)
    (mem_univ z₀) hp hq (fun z _ => by rw [h.deriv_deriv]; ring)
    (fun z _ => by rw [h'.deriv_deriv]; ring) h₀ h₁
  funext z; exact key (mem_univ z)

end IsMathieuSolution

/-- **Existence of solutions** (DLMF §28.2(ii)): Mathieu's equation has an entire solution with
arbitrary initial value and derivative at any point `z₀`. Proved from the existence of entire
solutions of linear second-order ODEs with entire coefficients
(`ODE.exists_entire_solution_linear_ode'`, majorant series). -/
@[dlmf 28.2.ii]
theorem exists_isMathieuSolution (a q z₀ w₀ w₁ : ℂ) :
    ∃ w, IsMathieuSolution a q w ∧ w z₀ = w₀ ∧ deriv w z₀ = w₁ := by
  obtain ⟨w, hw, hode, h0, h1⟩ := ODE.exists_entire_solution_linear_ode' (p := fun _ => 0)
    (q := fun z => 2 * q * Complex.cos (2 * z) - a) (differentiable_const _) (by fun_prop)
    z₀ w₀ w₁
  exact ⟨w, ⟨hw, fun z => by simpa using hode z⟩, h0, h1⟩

/-- Characterization of `w_I` (DLMF 28.2.5). -/
@[dlmf 28.2.E5]
theorem mathieuWI_spec (a q : ℂ) :
    IsMathieuSolution a q (mathieuWI a q) ∧ mathieuWI a q 0 = 1 ∧
      deriv (mathieuWI a q) 0 = 0 := by
  have h := exists_isMathieuSolution a q 0 1 0
  simp only [mathieuWI, dite_eq_left h]
  exact h.choose_spec

/-- Characterization of `w_II` (DLMF 28.2.5). -/
@[dlmf 28.2.E5]
theorem mathieuWII_spec (a q : ℂ) :
    IsMathieuSolution a q (mathieuWII a q) ∧ mathieuWII a q 0 = 0 ∧
      deriv (mathieuWII a q) 0 = 1 := by
  have h := exists_isMathieuSolution a q 0 0 1
  simp only [mathieuWII, dite_eq_left h]
  exact h.choose_spec

/-- `w_I(z; a, q)` solves Mathieu's equation (DLMF 28.2.5). -/
theorem isMathieuSolution_mathieuWI (a q : ℂ) : IsMathieuSolution a q (mathieuWI a q) :=
  (mathieuWI_spec a q).1

/-- `w_II(z; a, q)` solves Mathieu's equation (DLMF 28.2.5). -/
theorem isMathieuSolution_mathieuWII (a q : ℂ) : IsMathieuSolution a q (mathieuWII a q) :=
  (mathieuWII_spec a q).1

/-- Every solution is the combination `w(z₀)… ` of the basic solutions:
`w = w(0) w_I + w'(0) w_II` (DLMF §28.2(ii), fundamental pair). -/
theorem IsMathieuSolution.eq_combination {a q : ℂ} {w : ℂ → ℂ} (h : IsMathieuSolution a q w) :
    w = fun z => w 0 * mathieuWI a q z + deriv w 0 * mathieuWII a q z := by
  obtain ⟨h1, h10, h11⟩ := mathieuWI_spec a q
  obtain ⟨h2, h20, h21⟩ := mathieuWII_spec a q
  have hc := (h1.const_mul (w 0)).add (h2.const_mul (deriv w 0))
  refine h.eq_of_initial hc (z₀ := 0) (by simp [h10, h20]) ?_
  rw [show deriv (fun z => w 0 * mathieuWI a q z + deriv w 0 * mathieuWII a q z) 0 =
      w 0 * deriv (mathieuWI a q) 0 + deriv w 0 * deriv (mathieuWII a q) 0 from
    (((h1.differentiable 0).hasDerivAt.const_mul _).add
      ((h2.differentiable 0).hasDerivAt.const_mul _)).deriv]
  simp [h11, h21]

/-! ### Basic API -/

/-- `ce_n(z, q)` solves Mathieu's equation with `a = a_n(q)`. -/
theorem isMathieuSolution_mathieuCe (n : ℕ) (q : ℝ) :
    IsMathieuSolution (mathieuA n q) q (fun z => mathieuCe n z q) :=
  (isMathieuSolution_mathieuWI _ _).const_mul _

/-- `se_n(z, q)` solves Mathieu's equation with `a = b_n(q)`. -/
theorem isMathieuSolution_mathieuSe (n : ℕ) (q : ℝ) :
    IsMathieuSolution (mathieuB n q) q (fun z => mathieuSe n z q) :=
  (isMathieuSolution_mathieuWII _ _).const_mul _

/-- `ge_n(z, q)` solves Mathieu's equation with `a = b_n(q)` (DLMF 28.5.2). -/
theorem isMathieuSolution_mathieuGe (n : ℕ) (q : ℝ) :
    IsMathieuSolution (mathieuB n q) q (fun z => mathieuGe n z q) :=
  (isMathieuSolution_mathieuWI _ _).const_mul _

/-- `fe_n(z, q)` solves Mathieu's equation with `a = a_n(q)` for `(n, q) ≠ (0, 0)`
(DLMF 28.5.1). -/
theorem isMathieuSolution_mathieuFe {n : ℕ} {q : ℝ} (h : ¬ (n = 0 ∧ q = 0)) :
    IsMathieuSolution (mathieuA n q) q (fun z => mathieuFe n z q) := by
  simp only [mathieuFe, h, ite_false]
  exact (isMathieuSolution_mathieuWII _ _).const_mul _

/-- `ce_n(0, q)` is the normalizing factor `mathieuCeZero n q`. -/
theorem mathieuCe_zero (n : ℕ) (q : ℝ) : mathieuCe n 0 q = mathieuCeZero n q := by
  simp [mathieuCe, (mathieuWI_spec _ _).2.1]

/-- `se_n'(0, q)` is the normalizing factor `mathieuSeDerivZero n q`. -/
theorem deriv_mathieuSe_zero (n : ℕ) (q : ℝ) :
    deriv (fun z => mathieuSe n z q) 0 = mathieuSeDerivZero n q := by
  have h := (mathieuWII_spec (mathieuB n q) q)
  rw [show deriv (fun z => mathieuSe n z q) 0 =
      (mathieuSeDerivZero n q : ℂ) * deriv (mathieuWII (mathieuB n q) q) 0 from
    ((h.1.differentiable 0).hasDerivAt.const_mul _).deriv, h.2.2, mul_one]

end DLMF.Mathieu
