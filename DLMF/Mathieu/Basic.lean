/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

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
# Mathieu's equation and the Mathieu functions of integer order (DLMF §28.2)

This is the definitions file of the Mathieu area (DLMF Chapter 28). It contains

* `IsMathieuSolution a q w`: `w` is an entire solution of Mathieu's equation 28.2.1
  `w'' + (a - 2q cos 2z) w = 0` (genuine differentiability, complex `z`, `a`, `q`);
* the basic solutions `mathieuWI a q`, `mathieuWII a q` (`w_I(z; a, q)`, `w_II(z; a, q)`,
  28.2.5), defined by choice from the existence theorem `exists_isMathieuSolution`
  (proved: entire solutions of linear ODEs with entire coefficients, majorant series);
  uniqueness is proved (`IsMathieuSolution.eq_of_initial`) from analytic uniqueness;
* Floquet notions (§28.2(iii)–(iv)): `IsMathieuCharExp a q ν` (`cos πν = w_I(π; a, q)`,
  28.2.16), `IsFloquetSolution a q ν w` (28.2.14) and the monodromy matrix
  `mathieuMonodromy a q` (28.2.15);
* the eigenvalues `mathieuA n q = a_n(q)` and `mathieuB n q = b_n(q)` for real `q`
  (Table 28.2.1, 28.2.21–28.2.22), the `⌊n/2⌋`-th smallest real root of the boundary condition
  of Table 28.2.1 (`nthLeast`); the theorems `mathieuSpecA_exists`, `mathieuSpecB_exists`
  (proved by Sturm–Liouville arguments, `DLMFMathlib/Analysis/ODE/P2sSturmSpectrum.lean`)
  assert that these roots exist;
* the eigenfunctions `mathieuCe n z q = ce_n(z, q)` and `mathieuSe n z q = se_n(z, q)`
  (Table 28.2.2), normalized by 28.2.30, with the sign `ce_n(0, q) > 0`, `se_n'(0, q) > 0`;
* the second solutions `mathieuFe n z q = fe_n(z, q)`, `mathieuGe n z q = ge_n(z, q)` with the
  factors `C_n(q)`, `S_n(q)` and periodic parts `f_n`, `g_n` (DLMF 28.5.1–28.5.5);
* the Fourier coefficients `mathieuFourierA n m q = A^n_m(q)` and
  `mathieuFourierB n m q = B^n_m(q)` of `ce_n`, `se_n` (DLMF 28.4.1–28.4.4).

## Design notes

* The eigenvalues are defined for real `q` only (DLMF §28.2(v); the analytic continuation to
  complex `q` of §28.7 is stated as theorems). For real `q` the four boundary-value problems
  of Table 28.2.1 are regular Sturm–Liouville problems with simple real eigenvalues, so the
  `k`-th smallest root is DLMF's `a_{2k}`, `a_{2k+1}`, `b_{2k+1}`, `b_{2k+2}`.
* DLMF fixes the sign of `ce_n`, `se_n` "by continuity" in `q` from `q = 0`. For real `q`,
  `ce_n(0, q) ≠ 0` and `se_n'(0, q) ≠ 0` (an even, resp. odd, nontrivial solution cannot have
  both initial data zero), so the continuity convention is equivalent to `ce_n(0, q) > 0` and
  `se_n'(0, q) > 0`, which is the definition used here (`ce_n = c · w_I(·; a_n(q), q)` with
  `c > 0`).
* Similarly `fe_n'(0, q) > 0` and `ge_n(0, q) > 0`: DLMF fixes the signs of `C_n(q)`, `S_n(q)`
  by `C_n f_n → sin nz`, `S_n g_n → cos nz` as `q → 0`. For `n = 0` the normalization 28.5.5
  cannot hold at `q = 0` (there `f_0 = 0`); `fe_0(z, 0) = z` (28.5.7) is used at `q = 0`.
* For real `q` the Mathieu functions are real on the real axis; the normalizing integrals are
  written with `‖·‖²`, which agrees with DLMF's squares there.
* `b_0` is not defined by DLMF; `mathieuB 0 q = 0` and `mathieuSe 0 z q` are junk values.
-/

@[expose] public noncomputable section

/-- `dif_pos` without the deprecation. -/
private lemma dif_pos' {c : Prop} [Decidable c] (h : c) {α : Sort*} {t : c → α} {e : ¬c → α} :
    dite c t e = t h := by simp [h]

open Complex Set Filter
open scoped Topology Real Classical

namespace DLMF.Mathieu

/-! ### Mathieu's equation -/

/-- **Mathieu's equation** (DLMF 28.2.1) `w'' + (a - 2q cos 2z) w = 0` in standard form, with
complex parameters `(a, q)` and complex variable `z`: `w` is entire and its derivative has
derivative `(2q cos 2z - a) w(z)` at every point. -/
@[dlmf 28.2.E1]
structure IsMathieuSolution (a q : ℂ) (w : ℂ → ℂ) : Prop where
  /-- Solutions are entire (DLMF §28.2(ii)). -/
  differentiable : Differentiable ℂ w
  /-- The equation `w'' = (2q cos 2z - a) w`. -/
  hasDerivAt_deriv : ∀ z, HasDerivAt (deriv w) ((2 * q * Complex.cos (2 * z) - a) * w z) z

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

/-! ### Basic solutions -/

/-- The **basic solution** `w_I(z; a, q)` of Mathieu's equation (DLMF 28.2.5): the solution with
`w_I(0) = 1`, `w_I'(0) = 0`; defined by choice (junk `0` if no such solution existed, which
`exists_isMathieuSolution` excludes). -/
@[dlmf 28.2.E5]
def mathieuWI (a q : ℂ) : ℂ → ℂ :=
  if h : ∃ w, IsMathieuSolution a q w ∧ w 0 = 1 ∧ deriv w 0 = 0 then h.choose else 0

/-- The **basic solution** `w_II(z; a, q)` of Mathieu's equation (DLMF 28.2.5): the solution with
`w_II(0) = 0`, `w_II'(0) = 1`; defined by choice. -/
@[dlmf 28.2.E5]
def mathieuWII (a q : ℂ) : ℂ → ℂ :=
  if h : ∃ w, IsMathieuSolution a q w ∧ w 0 = 0 ∧ deriv w 0 = 1 then h.choose else 0

/-- Characterization of `w_I` (DLMF 28.2.5). -/
@[dlmf 28.2.E5]
theorem mathieuWI_spec (a q : ℂ) :
    IsMathieuSolution a q (mathieuWI a q) ∧ mathieuWI a q 0 = 1 ∧
      deriv (mathieuWI a q) 0 = 0 := by
  have h := exists_isMathieuSolution a q 0 1 0
  simp only [mathieuWI, dif_pos' h]
  exact h.choose_spec

/-- Characterization of `w_II` (DLMF 28.2.5). -/
@[dlmf 28.2.E5]
theorem mathieuWII_spec (a q : ℂ) :
    IsMathieuSolution a q (mathieuWII a q) ∧ mathieuWII a q 0 = 0 ∧
      deriv (mathieuWII a q) 0 = 1 := by
  have h := exists_isMathieuSolution a q 0 0 1
  simp only [mathieuWII, dif_pos' h]
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

/-! ### Floquet theory (§28.2(iii)–(iv)) -/

/-- The **monodromy matrix** of Mathieu's equation (DLMF 28.2.15):
`[[w_I(π), w_II(π)], [w_I'(π), w_II'(π)]]`. -/
@[dlmf 28.2.E15]
def mathieuMonodromy (a q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![mathieuWI a q π, mathieuWII a q π; deriv (mathieuWI a q) π, deriv (mathieuWII a q) π]

/-- `ν` is a **characteristic exponent** of Mathieu's equation with parameters `(a, q)`: it
solves the characteristic equation `cos(πν) = w_I(π; a, q)` (DLMF 28.2.16). The principal
exponent `ν̂ = π⁻¹ arccos w_I(π; a, q)` with `0 ≤ ℜν̂ ≤ 1` is one solution; all solutions are
`±ν̂ + 2n`, `n ∈ ℤ`. -/
@[dlmf 28.2.E16]
def IsMathieuCharExp (a q ν : ℂ) : Prop :=
  Complex.cos (π * ν) = mathieuWI a q π

/-- A **Floquet solution** with respect to `ν` (DLMF 28.2.14, §28.2(iv)): a nontrivial solution of
Mathieu's equation with `w(z + π) = e^{πiν} w(z)`. -/
@[dlmf 28.2.E14]
def IsFloquetSolution (a q ν : ℂ) (w : ℂ → ℂ) : Prop :=
  IsMathieuSolution a q w ∧ w ≠ 0 ∧ ∀ z, w (z + π) = Complex.exp (π * I * ν) * w z

/-! ### The `n`-th smallest element of a set of reals -/

/-- The `n`-th smallest element (counting from `0`) of a set `S ⊆ ℝ`: the element `x ∈ S` with
exactly `n` elements of `S` below it (junk `0` if there is none). Used for the ordered
spectra of Table 28.2.1. -/
def nthLeast (S : Set ℝ) (n : ℕ) : ℝ :=
  if h : ∃ x ∈ S, (S ∩ Iio x).encard = n then h.choose else 0

/-- The defining property of `nthLeast`. -/
theorem nthLeast_spec {S : Set ℝ} {n : ℕ} (h : ∃ x ∈ S, (S ∩ Iio x).encard = n) :
    nthLeast S n ∈ S ∧ (S ∩ Iio (nthLeast S n)).encard = n := by
  simp only [nthLeast, dif_pos' h]; exact h.choose_spec

/-- The element of `S` with exactly `n` smaller elements is unique. -/
lemma m28a_eq_of_encard {S : Set ℝ} {n : ℕ} {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hxn : (S ∩ Iio x).encard = n) (hyn : (S ∩ Iio y).encard = n) : x = y := by
  by_contra hne
  have key : ∀ {x y : ℝ}, x ∈ S → x < y → (S ∩ Iio x).encard = n →
      (S ∩ Iio y).encard = n → False := by
    intro x y hx hxy hxn hyn
    have hsub : insert x (S ∩ Iio x) ⊆ S ∩ Iio y := by
      intro t ht
      rcases ht with rfl | ⟨htS, htx⟩
      · exact ⟨hx, hxy⟩
      · exact ⟨htS, lt_trans htx hxy⟩
    have h1 := Set.encard_le_encard hsub
    rw [Set.encard_insert_of_notMem (fun h : x ∈ S ∩ Iio x => lt_irrefl x h.2), hxn, hyn] at h1
    have : ((n : ℕ∞) + 1) ≤ n := h1
    norm_cast at this
    omega
  rcases lt_or_gt_of_ne hne with h | h
  · exact key hx h hxn hyn
  · exact key hy h hyn hxn

/-- `nthLeast S n` is the unique element of `S` with exactly `n` smaller elements. -/
theorem nthLeast_eq_of {S : Set ℝ} {n : ℕ} {x : ℝ} (hx : x ∈ S) (hxn : (S ∩ Iio x).encard = n) :
    nthLeast S n = x := by
  have h := nthLeast_spec ⟨x, hx, hxn⟩
  exact m28a_eq_of_encard h.1 hx h.2 hxn

/-! ### Eigenvalues `a_n(q)`, `b_n(q)` (§28.2(v)) -/

/-- The spectrum containing `a_n(q)` (Table 28.2.1, DLMF 28.2.21), for real `q`: for even `n` the
real `a` with `w_I'(π/2; a, q) = 0` (`w'(0) = w'(π/2) = 0`), for odd `n` the real `a` with
`w_I(π/2; a, q) = 0` (`w'(0) = w(π/2) = 0`). -/
@[dlmf 28.2.T1]
def mathieuSpecA (n : ℕ) (q : ℝ) : Set ℝ :=
  if Even n then {a | deriv (mathieuWI a q) (π / 2) = 0} else {a | mathieuWI a q (π / 2) = 0}

/-- The spectrum containing `b_n(q)` (Table 28.2.1, DLMF 28.2.22), for real `q`: for odd `n` the
real `a` with `w_II'(π/2; a, q) = 0` (`w(0) = w'(π/2) = 0`), for even `n` the real `a` with
`w_II(π/2; a, q) = 0` (`w(0) = w(π/2) = 0`). -/
@[dlmf 28.2.T1]
def mathieuSpecB (n : ℕ) (q : ℝ) : Set ℝ :=
  if Even n then {a | mathieuWII a q (π / 2) = 0} else {a | deriv (mathieuWII a q) (π / 2) = 0}

/-- The **eigenvalue** `a_n(q)` of Mathieu's equation for real `q`, `n = 0, 1, 2, …` (DLMF
§28.2(v), Table 28.2.1): `a_{2k}(q)` (resp. `a_{2k+1}(q)`) is the `k`-th smallest real root of
`w_I'(π/2; a, q) = 0` (resp. `w_I(π/2; a, q) = 0`). -/
@[dlmf 28.2.T1]
def mathieuA (n : ℕ) (q : ℝ) : ℝ :=
  nthLeast (mathieuSpecA n q) (n / 2)

/-- The **eigenvalue** `b_n(q)` of Mathieu's equation for real `q`, `n = 1, 2, …` (DLMF
§28.2(v), Table 28.2.1): `b_{2k+1}(q)` (resp. `b_{2k+2}(q)`) is the `k`-th smallest real root of
`w_II'(π/2; a, q) = 0` (resp. `w_II(π/2; a, q) = 0`). `b_0` is junk (`0`). -/
@[dlmf 28.2.T1]
def mathieuB (n : ℕ) (q : ℝ) : ℝ :=
  if n = 0 then 0 else nthLeast (mathieuSpecB n q) ((n - 1) / 2)

/-! #### Existence of the eigenvalues

For real `a`, `q` the basic solutions are real on `ℝ`, their values and derivatives at `π/2` are
entire functions of `a` (holomorphic parameter dependence), they do not vanish for
`a < -(2|q| + 1)`, and they change sign for arbitrarily large `a` (energy estimate against
`cos √a x`, `sin √a x / √a`); see `DLMFMathlib/Analysis/ODE/P2sSturmSpectrum.lean`. -/

/-- A solution of Mathieu's equation, restricted to the real line, with its derivative. -/
lemma p2s_hasDerivAt_real {a q : ℂ} {w : ℂ → ℂ} (h : IsMathieuSolution a q w) (t : ℝ) :
    HasDerivAt (fun t : ℝ => w t) (deriv w t) t ∧
      HasDerivAt (fun t : ℝ => deriv w t) ((2 * q * Complex.cos (2 * t) - a) * w t) t :=
  ⟨((h.differentiable t).hasDerivAt).comp_ofReal, (h.hasDerivAt_deriv t).comp_ofReal⟩

/-- The real family attached to a family of solutions of Mathieu's equation with real
parameters and real initial data at `0`: the solutions are real on `ℝ`, their real parts solve
the real equation, and their values and derivatives are entire in `a`. -/
theorem p2s_family (q : ℝ) {w : ℂ → ℂ → ℂ} (hw : ∀ a, IsMathieuSolution a q (w a)) {α β : ℝ}
    (h0 : ∀ a, w a 0 = α) (h1 : ∀ a, deriv (w a) 0 = β) :
    (∀ a x : ℝ, w a x = ((w a x).re : ℂ) ∧ deriv (w a) x = ((deriv (w a) x).re : ℂ)) ∧
    (∀ a x : ℝ, HasDerivAt (fun x : ℝ => (w a x).re) (deriv (w a) x).re x) ∧
    (∀ a x : ℝ, HasDerivAt (fun x : ℝ => (deriv (w a) x).re)
      ((2 * q * Real.cos (2 * x) - a) * (w a x).re) x) ∧
    (∀ x : ℝ, Differentiable ℂ (fun a => w a x) ∧ Differentiable ℂ (fun a => deriv (w a) x)) := by
  have hcoef : ∀ (a x : ℝ), (2 * (q : ℂ) * Complex.cos (2 * (x : ℂ)) - a) =
      ((2 * q * Real.cos (2 * x) - a : ℝ) : ℂ) := by
    intro a x; push_cast; rfl
  refine ⟨fun a x => ?_, fun a x => ?_, fun a x => ?_, fun x => ?_⟩
  · have hP : Continuous fun t : ℝ => 2 * q * Real.cos (2 * t) - a := by fun_prop
    have key := ODE.p2s_conj_eq_of_linear_ode hP (f := fun t : ℝ => w a t)
      (f' := fun t : ℝ => deriv (w a) t) (t₀ := 0) (fun t => by
        obtain ⟨k1, k2⟩ := p2s_hasDerivAt_real (hw a) t
        exact ⟨k1, by rw [← hcoef]; exact k2⟩)
      (by simp [h0]) (by simp [h1]) x
    exact ⟨(Complex.conj_eq_iff_re.mp key.1).symm, (Complex.conj_eq_iff_re.mp key.2).symm⟩
  · exact ((hw a).differentiable x).hasDerivAt.real_of_complex
  · have := ((hw a).hasDerivAt_deriv x).real_of_complex
    rw [hcoef, Complex.re_ofReal_mul] at this
    exact this
  · have := ODE.differentiable_param_of_linear_ode (p₀ := fun _ => 0) (p₁ := fun _ => 0)
      (q₀ := fun x : ℝ => 2 * (q : ℂ) * Complex.cos (2 * x)) (q₁ := fun _ => -1)
      continuous_const continuous_const (by fun_prop) continuous_const (t₀ := 0) (y₀ := α)
      (y₁ := β) (F := fun x μ => w μ x) (F' := fun x μ => deriv (w μ) x)
      (fun μ t => by
        obtain ⟨k1, k2⟩ := p2s_hasDerivAt_real (hw μ) t
        exact ⟨k1, k2.congr_deriv (by ring)⟩)
      (fun μ => by simpa using h0 μ) (fun μ => by simpa using h1 μ) x
    exact this

/-- `z = 0 ↔ re z = 0` for a real complex number `z`. -/
lemma p2s_eq_zero_iff_re {z : ℂ} (hz : z = (z.re : ℂ)) : z = 0 ↔ z.re = 0 := by
  constructor
  · intro h; simp [h]
  · intro h; rw [hz, h, Complex.ofReal_zero]

/-- The bound `|2 q cos 2x| ≤ 2|q| + 1`. -/
lemma p2s_coef_bound (q : ℝ) :
    ∀ x ∈ Icc (0 : ℝ) (π / 2), |2 * q * Real.cos (2 * x)| ≤ 2 * |q| + 1 := by
  intro x _
  rw [abs_mul, abs_mul, abs_two]
  have := Real.abs_cos_le_one (2 * x)
  nlinarith [abs_nonneg q]

/-- From a real family to the enumeration of the zeros of an endpoint function. -/
lemma p2s_exists_of_endpoint {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hre : ∀ a : ℝ, G a = ((G a).re : ℂ))
    (hlow : ∃ c, ∀ a : ℝ, a < c → (G a).re ≠ 0)
    (hs : (∀ N, ∃ a : ℝ, a > N ∧ 0 < (G a).re) ∧ (∀ N, ∃ a : ℝ, a > N ∧ (G a).re < 0))
    (k : ℕ) : ∃ x ∈ {a : ℝ | G a = 0}, ({a : ℝ | G a = 0} ∩ Iio x).encard = k := by
  have hset : {a : ℝ | G a = 0} = {a : ℝ | (G a).re = 0} := by
    ext a; exact p2s_eq_zero_iff_re (hre a)
  rw [hset]
  exact ODE.p2s_exists_encard_zeros (g := fun a : ℝ => (G a).re) hG (fun a => (hre a)) hlow
    hs.1 hs.2 k

/-- The real roots `a` of `w_I(π/2; a, q) = 0` (real `q`) can be enumerated in increasing
order. -/
lemma p2s_I_val (q : ℝ) (k : ℕ) : ∃ x ∈ {a : ℝ | mathieuWI a q (π / 2) = 0},
    ({a : ℝ | mathieuWI a q (π / 2) = 0} ∩ Iio x).encard = k := by
  obtain ⟨hre, hd, hd', hent⟩ := p2s_family q (w := fun a => mathieuWI a q)
    (fun a => isMathieuSolution_mathieuWI a q) (α := 1) (β := 0)
    (fun a => by simp [(mathieuWI_spec a q).2.1]) (fun a => by simp [(mathieuWI_spec a q).2.2])
  have hpi : ((π / 2 : ℝ) : ℂ) = (π : ℂ) / 2 := by push_cast; ring
  have hM : (0 : ℝ) < 2 * |q| + 1 := by positivity
  have h0 : ∀ a : ℝ, (mathieuWI a q ((0 : ℝ) : ℂ)).re = 1 := fun a => by
    simp [(mathieuWI_spec a q).2.1]
  have h1 : ∀ a : ℝ, (deriv (mathieuWI a q) ((0 : ℝ) : ℂ)).re = 0 := fun a => by
    simp [(mathieuWI_spec a q).2.2]
  rw [← hpi]
  refine p2s_exists_of_endpoint (G := fun μ => mathieuWI μ q ((π / 2 : ℝ) : ℂ))
    (hent _).1 (fun a => (hre a _).1) ⟨-(2 * |q| + 1), fun a ha => ?_⟩ ?_ k
  · exact (ODE.p2s_endpoint_ne_zero (by positivity) (p2s_coef_bound q) ha (hd a) (hd' a)
      (by rw [h0, h1]; norm_num) (Or.inl (by rw [h0]; norm_num))).1
  · exact ODE.p2s_signs_I_val (Y := fun a x => (mathieuWI a q x).re) hM (by positivity)
      (p2s_coef_bound q) hd hd' h0 h1

/-- The real roots `a` of `w_I'(π/2; a, q) = 0` (real `q`) can be enumerated in increasing
order. -/
lemma p2s_I_der (q : ℝ) (k : ℕ) : ∃ x ∈ {a : ℝ | deriv (mathieuWI a q) (π / 2) = 0},
    ({a : ℝ | deriv (mathieuWI a q) (π / 2) = 0} ∩ Iio x).encard = k := by
  obtain ⟨hre, hd, hd', hent⟩ := p2s_family q (w := fun a => mathieuWI a q)
    (fun a => isMathieuSolution_mathieuWI a q) (α := 1) (β := 0)
    (fun a => by simp [(mathieuWI_spec a q).2.1]) (fun a => by simp [(mathieuWI_spec a q).2.2])
  have hpi : ((π / 2 : ℝ) : ℂ) = (π : ℂ) / 2 := by push_cast; ring
  have hM : (0 : ℝ) < 2 * |q| + 1 := by positivity
  have h0 : ∀ a : ℝ, (mathieuWI a q ((0 : ℝ) : ℂ)).re = 1 := fun a => by
    simp [(mathieuWI_spec a q).2.1]
  have h1 : ∀ a : ℝ, (deriv (mathieuWI a q) ((0 : ℝ) : ℂ)).re = 0 := fun a => by
    simp [(mathieuWI_spec a q).2.2]
  rw [← hpi]
  refine p2s_exists_of_endpoint (G := fun μ => deriv (mathieuWI μ q) ((π / 2 : ℝ) : ℂ))
    (hent _).2 (fun a => (hre a _).2) ⟨-(2 * |q| + 1), fun a ha => ?_⟩ ?_ k
  · exact (ODE.p2s_endpoint_ne_zero (by positivity) (p2s_coef_bound q) ha (hd a) (hd' a)
      (by rw [h0, h1]; norm_num) (Or.inl (by rw [h0]; norm_num))).2
  · exact ODE.p2s_signs_I_der (Y := fun a x => (mathieuWI a q x).re) hM (by positivity)
      (p2s_coef_bound q) hd hd' h0 h1

/-- The real roots `a` of `w_II(π/2; a, q) = 0` (real `q`) can be enumerated in increasing
order. -/
lemma p2s_II_val (q : ℝ) (k : ℕ) : ∃ x ∈ {a : ℝ | mathieuWII a q (π / 2) = 0},
    ({a : ℝ | mathieuWII a q (π / 2) = 0} ∩ Iio x).encard = k := by
  obtain ⟨hre, hd, hd', hent⟩ := p2s_family q (w := fun a => mathieuWII a q)
    (fun a => isMathieuSolution_mathieuWII a q) (α := 0) (β := 1)
    (fun a => by simp [(mathieuWII_spec a q).2.1]) (fun a => by simp [(mathieuWII_spec a q).2.2])
  have hpi : ((π / 2 : ℝ) : ℂ) = (π : ℂ) / 2 := by push_cast; ring
  have hM : (0 : ℝ) < 2 * |q| + 1 := by positivity
  have h0 : ∀ a : ℝ, (mathieuWII a q ((0 : ℝ) : ℂ)).re = 0 := fun a => by
    simp [(mathieuWII_spec a q).2.1]
  have h1 : ∀ a : ℝ, (deriv (mathieuWII a q) ((0 : ℝ) : ℂ)).re = 1 := fun a => by
    simp [(mathieuWII_spec a q).2.2]
  rw [← hpi]
  refine p2s_exists_of_endpoint (G := fun μ => mathieuWII μ q ((π / 2 : ℝ) : ℂ))
    (hent _).1 (fun a => (hre a _).1) ⟨-(2 * |q| + 1), fun a ha => ?_⟩ ?_ k
  · exact (ODE.p2s_endpoint_ne_zero (by positivity) (p2s_coef_bound q) ha (hd a) (hd' a)
      (by rw [h0, h1]; norm_num) (Or.inr (by rw [h1]; norm_num))).1
  · exact ODE.p2s_signs_II_val (Y := fun a x => (mathieuWII a q x).re) hM (by positivity)
      (p2s_coef_bound q) hd hd' h0 h1

/-- The real roots `a` of `w_II'(π/2; a, q) = 0` (real `q`) can be enumerated in increasing
order. -/
lemma p2s_II_der (q : ℝ) (k : ℕ) : ∃ x ∈ {a : ℝ | deriv (mathieuWII a q) (π / 2) = 0},
    ({a : ℝ | deriv (mathieuWII a q) (π / 2) = 0} ∩ Iio x).encard = k := by
  obtain ⟨hre, hd, hd', hent⟩ := p2s_family q (w := fun a => mathieuWII a q)
    (fun a => isMathieuSolution_mathieuWII a q) (α := 0) (β := 1)
    (fun a => by simp [(mathieuWII_spec a q).2.1]) (fun a => by simp [(mathieuWII_spec a q).2.2])
  have hpi : ((π / 2 : ℝ) : ℂ) = (π : ℂ) / 2 := by push_cast; ring
  have hM : (0 : ℝ) < 2 * |q| + 1 := by positivity
  have h0 : ∀ a : ℝ, (mathieuWII a q ((0 : ℝ) : ℂ)).re = 0 := fun a => by
    simp [(mathieuWII_spec a q).2.1]
  have h1 : ∀ a : ℝ, (deriv (mathieuWII a q) ((0 : ℝ) : ℂ)).re = 1 := fun a => by
    simp [(mathieuWII_spec a q).2.2]
  rw [← hpi]
  refine p2s_exists_of_endpoint (G := fun μ => deriv (mathieuWII μ q) ((π / 2 : ℝ) : ℂ))
    (hent _).2 (fun a => (hre a _).2) ⟨-(2 * |q| + 1), fun a ha => ?_⟩ ?_ k
  · exact (ODE.p2s_endpoint_ne_zero (by positivity) (p2s_coef_bound q) ha (hd a) (hd' a)
      (by rw [h0, h1]; norm_num) (Or.inr (by rw [h1]; norm_num))).2
  · exact ODE.p2s_signs_II_der (Y := fun a x => (mathieuWII a q x).re) hM (by positivity)
      (p2s_coef_bound q) hd hd' h0 h1

/-- **Existence of the eigenvalues** (DLMF §28.2(v)): for real `q` each spectrum of Table 28.2.1
is an increasing sequence of reals tending to `+∞`, so its `k`-th smallest element exists.
Proved from `ODE.p2s_exists_encard_zeros`: the boundary function is the restriction of an
entire function of `a`, has no zeros for `a < -(2|q| + 1)`, and changes sign for arbitrarily
large `a`. -/
@[dlmf 28.2.v]
theorem mathieuSpecA_exists (n : ℕ) (q : ℝ) (k : ℕ) :
    ∃ x ∈ mathieuSpecA n q, (mathieuSpecA n q ∩ Iio x).encard = k := by
  unfold mathieuSpecA
  split_ifs
  · exact p2s_I_der q k
  · exact p2s_I_val q k

/-- **Existence of the eigenvalues** `b_n(q)` (DLMF §28.2(v)); proved as
`mathieuSpecA_exists`. -/
@[dlmf 28.2.v]
theorem mathieuSpecB_exists (n : ℕ) (q : ℝ) (k : ℕ) :
    ∃ x ∈ mathieuSpecB n q, (mathieuSpecB n q ∩ Iio x).encard = k := by
  unfold mathieuSpecB
  split_ifs
  · exact p2s_II_val q k
  · exact p2s_II_der q k

/-- `a_n(q)` lies in its spectrum and has `⌊n/2⌋` smaller elements of it (DLMF §28.2(v)). -/
theorem mathieuA_spec (n : ℕ) (q : ℝ) :
    mathieuA n q ∈ mathieuSpecA n q ∧
      (mathieuSpecA n q ∩ Iio (mathieuA n q)).encard = (n / 2 : ℕ) :=
  nthLeast_spec (mathieuSpecA_exists n q (n / 2))

/-- `b_n(q)`, `n ≥ 1`, lies in its spectrum and has `⌊(n-1)/2⌋` smaller elements of it. -/
theorem mathieuB_spec {n : ℕ} (hn : n ≠ 0) (q : ℝ) :
    mathieuB n q ∈ mathieuSpecB n q ∧
      (mathieuSpecB n q ∩ Iio (mathieuB n q)).encard = ((n - 1) / 2 : ℕ) := by
  simp only [mathieuB, hn, ite_false]
  exact nthLeast_spec (mathieuSpecB_exists n q ((n - 1) / 2))

/-! ### Eigenfunctions `ce_n`, `se_n` (§28.2(vi)) -/

/-- The positive normalizing factor `ce_n(0, q) = (π / ∫₀^{2π} w_I(x; a_n(q), q)² dx)^{1/2}`
(DLMF 28.2.30 together with 28.2.38), real `q`. -/
def mathieuCeZero (n : ℕ) (q : ℝ) : ℝ :=
  Real.sqrt (π / ∫ x in (0 : ℝ)..2 * π, ‖mathieuWI (mathieuA n q) q x‖ ^ 2)

/-- The positive normalizing factor `se_n'(0, q) = (π / ∫₀^{2π} w_II(x; b_n(q), q)² dx)^{1/2}`
(DLMF 28.2.30 together with 28.2.39), real `q`. -/
def mathieuSeDerivZero (n : ℕ) (q : ℝ) : ℝ :=
  Real.sqrt (π / ∫ x in (0 : ℝ)..2 * π, ‖mathieuWII (mathieuB n q) q x‖ ^ 2)

/-- The **Mathieu function** `ce_n(z, q)` (DLMF Table 28.2.2, 28.2.30, 28.2.38), real `q`,
complex `z`, `n = 0, 1, 2, …`: the even eigenfunction for `a_n(q)`,
`ce_n(z, q) = ce_n(0, q) w_I(z; a_n(q), q)`, normalized by `∫₀^{2π} ce_n² = π`, with
`ce_n(0, q) > 0` (DLMF's sign convention "by continuity from `q = 0`"). -/
@[dlmf 28.2.T2]
def mathieuCe (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  (mathieuCeZero n q : ℂ) * mathieuWI (mathieuA n q) q z

/-- The **Mathieu function** `se_n(z, q)` (DLMF Table 28.2.2, 28.2.30, 28.2.39), real `q`,
complex `z`, `n = 1, 2, …`: the odd eigenfunction for `b_n(q)`,
`se_n(z, q) = se_n'(0, q) w_II(z; b_n(q), q)`, normalized by `∫₀^{2π} se_n² = π`, with
`se_n'(0, q) > 0`. (`n = 0` gives a junk value.) -/
@[dlmf 28.2.T2]
def mathieuSe (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  (mathieuSeDerivZero n q : ℂ) * mathieuWII (mathieuB n q) q z

/-! ### Second solutions `fe_n`, `ge_n` (§28.5) -/

/-- The coefficient `μ` of the secular part of `w_II(z; a_n(q), q) = μ z w_I(z) + u(z)` with
`u` (anti)periodic: `μ = w_I(π) w_II(π) / π` (DLMF §28.5; uses 28.2.8–28.2.9). -/
def mathieuFeMu (n : ℕ) (q : ℝ) : ℂ :=
  mathieuWI (mathieuA n q) q π * mathieuWII (mathieuA n q) q π / π

/-- The (anti)periodic odd part `u(z) = w_II(z) - μ z w_I(z)` at `a = a_n(q)` (DLMF §28.5). -/
def mathieuFeU (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  mathieuWII (mathieuA n q) q z - mathieuFeMu n q * z * mathieuWI (mathieuA n q) q z

/-- The coefficient `μ = w_I'(π) w_II'(π) / π` of the secular part of
`w_I(z; b_n(q), q) = μ z w_II(z) + u(z)` (DLMF §28.5). -/
def mathieuGeMu (n : ℕ) (q : ℝ) : ℂ :=
  deriv (mathieuWI (mathieuB n q) q) π * deriv (mathieuWII (mathieuB n q) q) π / π

/-- The (anti)periodic even part `u(z) = w_I(z) - μ z w_II(z)` at `a = b_n(q)` (DLMF §28.5). -/
def mathieuGeU (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  mathieuWI (mathieuB n q) q z - mathieuGeMu n q * z * mathieuWII (mathieuB n q) q z

/-- The positive factor `fe_n'(0, q) = (π / ∫₀^{2π} u²)^{1/2}` (DLMF 28.5.5). -/
def mathieuFeDerivZero (n : ℕ) (q : ℝ) : ℝ :=
  Real.sqrt (π / ∫ x in (0 : ℝ)..2 * π, ‖mathieuFeU n x q‖ ^ 2)

/-- The positive factor `ge_n(0, q) = (π / ∫₀^{2π} u²)^{1/2}` (DLMF 28.5.5). -/
def mathieuGeZero (n : ℕ) (q : ℝ) : ℝ :=
  Real.sqrt (π / ∫ x in (0 : ℝ)..2 * π, ‖mathieuGeU n x q‖ ^ 2)

/-- The **second solution** `fe_n(z, q)` (DLMF 28.5.1, 28.5.5, 28.5.7), real `q`, `n ≥ 0`: the
odd solution of Mathieu's equation with `a = a_n(q)`, `fe_n = fe_n'(0, q) w_II(z; a_n(q), q)`,
normalized by 28.5.5 with `fe_n'(0, q) > 0`; `fe_0(z, 0) = z` (28.5.7). -/
@[dlmf 28.5.E1]
def mathieuFe (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  if n = 0 ∧ q = 0 then z else (mathieuFeDerivZero n q : ℂ) * mathieuWII (mathieuA n q) q z

/-- The **second solution** `ge_n(z, q)` (DLMF 28.5.2, 28.5.5, 28.5.7), real `q`, `n ≥ 1`: the
even solution with `a = b_n(q)`, `ge_n = ge_n(0, q) w_I(z; b_n(q), q)`, normalized by 28.5.5
with `ge_n(0, q) > 0`. -/
@[dlmf 28.5.E2]
def mathieuGe (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  (mathieuGeZero n q : ℂ) * mathieuWI (mathieuB n q) q z

/-- The factor `C_n(q)` of DLMF 28.5.1: `C_n = fe_n'(0) μ / ce_n(0)`, so that
`fe_n = C_n (z ce_n + f_n)`; `C_0(0) = √2`. Vanishes at `q = 0` for `n ≥ 1`. -/
@[dlmf 28.5.E1]
def mathieuFeC (n : ℕ) (q : ℝ) : ℂ :=
  if n = 0 ∧ q = 0 then Real.sqrt 2 else
    (mathieuFeDerivZero n q : ℂ) * mathieuFeMu n q / mathieuCeZero n q

/-- The factor `S_n(q)` of DLMF 28.5.2: `S_n = ge_n(0) μ / se_n'(0)`, so that
`ge_n = S_n (z se_n + g_n)`. Vanishes at `q = 0`. -/
@[dlmf 28.5.E2]
def mathieuGeS (n : ℕ) (q : ℝ) : ℂ :=
  (mathieuGeZero n q : ℂ) * mathieuGeMu n q / mathieuSeDerivZero n q

/-- The periodic or antiperiodic odd function `f_n(z, q) = fe_n / C_n - z ce_n` of DLMF 28.5.1
(meaningful for `C_n(q) ≠ 0`, i.e. `q ≠ 0` or `n = 0`). -/
@[dlmf 28.5.E3]
def mathieuFeF (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  mathieuFe n z q / mathieuFeC n q - z * mathieuCe n z q

/-- The periodic or antiperiodic even function `g_n(z, q) = ge_n / S_n - z se_n` of DLMF 28.5.2
(meaningful for `q ≠ 0`). -/
@[dlmf 28.5.E4]
def mathieuGeG (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  mathieuGe n z q / mathieuGeS n q - z * mathieuSe n z q

/-! ### Fourier coefficients (§28.4) -/

/-- The **Fourier coefficient** `A^n_m(q)` of `ce_n(z, q) = ∑ₘ A^n_m(q) cos mz` (DLMF
28.4.1–28.4.2; only `m ≡ n (mod 2)` occur), real `q`:
`A^n_0 = (2π)⁻¹ ∫₀^{2π} ce_n`, `A^n_m = π⁻¹ ∫₀^{2π} ce_n(x) cos mx dx` for `m ≥ 1`. -/
@[dlmf 28.4.E1]
def mathieuFourierA (n m : ℕ) (q : ℝ) : ℂ :=
  (if m = 0 then 1 / (2 * π) else 1 / π : ℂ) *
    ∫ x in (0 : ℝ)..2 * π, mathieuCe n x q * Complex.cos (m * x)

/-- The **Fourier coefficient** `B^n_m(q)` of `se_n(z, q) = ∑ₘ B^n_m(q) sin mz` (DLMF
28.4.3–28.4.4), real `q`: `B^n_m = π⁻¹ ∫₀^{2π} se_n(x) sin mx dx`. -/
@[dlmf 28.4.E3]
def mathieuFourierB (n m : ℕ) (q : ℝ) : ℂ :=
  (1 / π : ℂ) * ∫ x in (0 : ℝ)..2 * π, mathieuSe n x q * Complex.sin (m * x)

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
