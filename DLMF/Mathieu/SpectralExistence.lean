/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.FundamentalSolutions
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
# Existence and enumeration of Mathieu characteristic values
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real Classical

namespace DLMF.Mathieu

/-- The defining property of `nthLeast`. -/
theorem nthLeast_spec {S : Set ℝ} {n : ℕ} (h : ∃ x ∈ S, (S ∩ Iio x).encard = n) :
    nthLeast S n ∈ S ∧ (S ∩ Iio (nthLeast S n)).encard = n := by
  simp only [nthLeast, dite_eq_left h]; exact h.choose_spec

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

end DLMF.Mathieu
