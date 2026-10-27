/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Hill's equation and the equations of Whittaker–Hill and Ince: definitions (DLMF §§28.29–28.31)

Hill's equation (DLMF 28.29.1) is `w'' + (λ + Q(x)) w = 0` with a `π`-periodic potential `Q`
of mean zero (28.29.2, 28.29.3). DLMF allows either a continuous real-valued `Q` on `ℝ` or a
`Q` analytic in a strip around the real axis. Here the independent variable is real and
`Q : ℝ → ℂ` is continuous; this covers both cases on the real axis (an analytic `Q` restricts
to a continuous complex-valued function, and the solutions in the strip are determined by
their restrictions). The results of §28.29(iii) and §28.30 assume `Q` real-valued; they take
`Q : ℝ → ℝ` and use the coercion `fun x => (Q x : ℂ)`.

* `IsHillSolution Q λ w`: `w` is differentiable on `ℝ`, `deriv w` is differentiable and
  `(deriv w)' = -(λ + Q) w` (genuine derivatives, so a totalized `deriv` cannot fake a
  solution).
* `IsHillPotential Q`: continuity, period `π` (28.29.2) and mean zero (28.29.3). DLMF's remark
  that `π` is the *minimum* period of `Q` is not part of the predicate; no result below needs
  it.
* `hillWI Q z λ`, `hillWII Q z λ`: the basic solutions `w_I`, `w_II` with
  `w_I(0) = 1, w_I'(0) = 0`, `w_II(0) = 0, w_II'(0) = 1` (as in DLMF 28.2(ii)). They are
  **definitions by choice**: the chosen solution when one exists (existence for continuous
  `Q` is the flagged theorem `DLMF.Mathieu.hill_exists_solution`; uniqueness is proved), and
  `0` otherwise.
* `hillDiscriminant Q λ = w_I(π, λ) + w_II'(π, λ)` (28.29.15) and the monodromy matrix
  `hillMonodromy Q λ` (28.29.8).
* `IsHillFloquetSolution Q λ ν w`: a nontrivial solution with `w(x + π) = e^{πiν} w(x)`
  (28.29.7).
* `hillMultiplierSolutions Q λ s`: the `ℂ`-submodule of solutions with `w(x + π) = s w(x)`;
  `s = 1` gives the `π`-periodic and `s = -1` the `π`-antiperiodic (period `2π`) solutions.
* `hillPeriodicEigenvalue Q n` (`λ_n`, `n = 0, 1, …`, 28.29.16) and
  `hillAntiperiodicEigenvalue Q n` (`μ_n`, `n = 1, 2, …`, 28.29.17) for real `Q`: the real
  `λ` with a nontrivial `π`-periodic (resp. antiperiodic) solution, listed increasingly and
  counted with the dimension of the solution space (which is the multiplicity in DLMF's
  interlacing 28.29.18, where `λ_{2m-1} = λ_{2m}` or `μ_{2m-1} = μ_{2m}` when both solutions
  are periodic). **Definition by counting:** `λ_n` is the infimum of the `t` such that the
  eigenvalues `≤ t`, counted with multiplicity, number at least `n + 1`. If the counting
  function is not finite (which does not happen for real continuous `Q`, see
  `DLMF.Mathieu.hillPeriodicEigenvalue_spec`) the value is a junk value.
* `hillEigenvalueHat Q m` (`λ̂_m`, 28.30(i)): `λ_0, μ_1, μ_2, λ_1, λ_2, μ_3, …` merged in the
  natural order 28.29.18; `IsHillEigenfunctionFamily Q w`: `w` is an orthonormal family of
  real `2π`-periodic eigenfunctions for the `λ̂_m` (28.30.1–28.30.2; DLMF's eigenfunctions are
  such a choice).
* `hillMeanSquare Q` (`N`, 28.29.19).

§28.31 (Whittaker–Hill and Ince):

* `IsWhittakerHillSolution A B k c W` (28.31.1) and `IsInceSolution ξ η p w` (28.31.3), over
  `ℂ` (entire solutions).
* `IsEntireFourierCoeff A`: summability of `‖A_k‖ (k+1)² e^{kR}` for every `R` (the Fourier
  series 28.31.4–28.31.5 then define entire functions differentiable termwise).
* `IsInceCosPoly p f`, `IsInceSinPoly p f`: real trigonometric polynomials
  `∑ A_k cos(kz)` resp. `∑ B_k sin(kz)` with `k ≤ p`, `k ≡ p (mod 2)`.
* `inceA p m ξ` (`a_p^m(ξ)`) and `inceB p m ξ` (`b_p^m(ξ)`) for real `ξ`: **definitions by
  choice**, the unique real `η` for which Ince's equation has a nontrivial Ince polynomial
  solution of the right type with exactly `m` zeros in `[0, π)` (DLMF §28.31(ii), "can be
  ordered so that `C_p^m` and `S_p^m` have precisely `m` zeros, all simple, in `0 ≤ z < π`"),
  and `0` if there is no such unique `η`.
* `inceC p m z ξ` (`C_p^m(z, ξ)`) and `inceS p m z ξ` (`S_p^m(z, ξ)`): **definitions by
  choice**, the unique Ince polynomial with eigenvalue `a_p^m(ξ)` (resp. `b_p^m(ξ)`),
  normalized by 28.31.12 and with `C_p^m(0, ξ) > 0` (resp. `S_p^m'(0, ξ) > 0`); `0` if it does
  not exist uniquely. For `m ≢ p (mod 2)` or `m > p` (and `m = 0` for `S`) the values are
  junk `0`.
* `paraboloidalHc p m z ξ`, `paraboloidalHs p m z ξ`: the paraboloidal wave functions
  `hc_p^m`, `hs_p^m` (28.31.16, 28.31.17).
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory intervalIntegral
open scoped Topology Classical

namespace DLMF.Mathieu

/-! ### §28.29(i) Hill's equation -/

/-- **Hill's equation** (DLMF 28.29.1): `w'' + (λ + Q(x)) w = 0` on the real line, for a
complex-valued potential `Q` and complex `λ`, with genuine derivatives. -/
@[dlmf 28.29.E1]
structure IsHillSolution (Q : ℝ → ℂ) (lam : ℂ) (w : ℝ → ℂ) : Prop where
  differentiable : Differentiable ℝ w
  hasDerivAt_deriv : ∀ x : ℝ, HasDerivAt (deriv w) (-(lam + Q x) * w x) x

/-- The hypotheses on the potential of Hill's equation (DLMF 28.29.2, 28.29.3): `Q` is
continuous, `π`-periodic and has mean zero over a period. DLMF also says that `π` is the
minimum period; that is not required here. -/
@[dlmf 28.29.E2, dlmf 28.29.E3, dlmf 28.29.i]
structure IsHillPotential (Q : ℝ → ℂ) : Prop where
  continuous : Continuous Q
  periodic : Function.Periodic Q Real.pi
  integral_eq_zero : ∫ x in (0 : ℝ)..Real.pi, Q x = 0

/-! ### §28.29(ii) Basic solutions and Floquet solutions -/

/-- The basic solution `w_I(z, λ)` of Hill's equation (DLMF 28.29(ii), defined as in
28.2(ii)): `w_I(0) = 1`, `w_I'(0) = 0`. Definition by choice: the chosen solution when one
exists (always for continuous `Q`, `DLMF.Mathieu.hill_exists_solution`; it is unique), else
`0`. Argument order as in DLMF: potential, then `z`, then `λ`. -/
def hillWI (Q : ℝ → ℂ) (z : ℝ) (lam : ℂ) : ℂ :=
  if h : ∃ w : ℝ → ℂ, IsHillSolution Q lam w ∧ w 0 = 1 ∧ deriv w 0 = 0 then h.choose z else 0

/-- The basic solution `w_II(z, λ)` of Hill's equation (DLMF 28.29(ii)): `w_II(0) = 0`,
`w_II'(0) = 1`. Definition by choice as for `hillWI`. -/
def hillWII (Q : ℝ → ℂ) (z : ℝ) (lam : ℂ) : ℂ :=
  if h : ∃ w : ℝ → ℂ, IsHillSolution Q lam w ∧ w 0 = 0 ∧ deriv w 0 = 1 then h.choose z else 0

/-- The **discriminant** of Hill's equation (DLMF 28.29.15),
`Δ(λ) = w_I(π, λ) + w_II'(π, λ)`, the trace of the monodromy matrix 28.29.8. DLMF introduces
it in §28.29(iii) for real `Q`; the definition makes sense for every `Q`. -/
@[dlmf 28.29.E15]
def hillDiscriminant (Q : ℝ → ℂ) (lam : ℂ) : ℂ :=
  hillWI Q Real.pi lam + deriv (fun x => hillWII Q x lam) Real.pi

/-- The **monodromy matrix** of Hill's equation (DLMF 28.29.8),
`[[w_I(π, λ), w_II(π, λ)], [w_I'(π, λ), w_II'(π, λ)]]`. -/
@[dlmf 28.29.E8]
def hillMonodromy (Q : ℝ → ℂ) (lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![hillWI Q Real.pi lam, hillWII Q Real.pi lam;
    deriv (fun x => hillWI Q x lam) Real.pi, deriv (fun x => hillWII Q x lam) Real.pi]

/-- A **Floquet solution with respect to `ν`** of Hill's equation (DLMF 28.29.7): a
nontrivial solution with `w(x + π) = e^{πiν} w(x)`. -/
@[dlmf 28.29.E7]
def IsHillFloquetSolution (Q : ℝ → ℂ) (lam ν : ℂ) (w : ℝ → ℂ) : Prop :=
  IsHillSolution Q lam w ∧ (∃ x, w x ≠ 0) ∧
    ∀ x, w (x + Real.pi) = Complex.exp (Real.pi * I * ν) * w x

/-- Solutions of Hill's equation are closed under addition. -/
theorem IsHillSolution.add {Q : ℝ → ℂ} {lam : ℂ} {u v : ℝ → ℂ} (hu : IsHillSolution Q lam u)
    (hv : IsHillSolution Q lam v) : IsHillSolution Q lam (u + v) := by
  refine ⟨hu.differentiable.add hv.differentiable, fun x => ?_⟩
  have hd : deriv (u + v) = deriv u + deriv v := by
    funext y; exact deriv_add (hu.differentiable y) (hv.differentiable y)
  rw [hd]
  convert (hu.hasDerivAt_deriv x).add (hv.hasDerivAt_deriv x) using 1
  simp only [Pi.add_apply]; ring

/-- Solutions of Hill's equation are closed under scalar multiplication. -/
theorem IsHillSolution.const_smul {Q : ℝ → ℂ} {lam : ℂ} {u : ℝ → ℂ}
    (hu : IsHillSolution Q lam u) (c : ℂ) : IsHillSolution Q lam (c • u) := by
  refine ⟨hu.differentiable.const_smul c, fun x => ?_⟩
  have hd : deriv (c • u) = c • deriv u := by
    funext y; exact deriv_const_smul c (hu.differentiable y)
  rw [hd]
  convert (hu.hasDerivAt_deriv x).const_smul c using 1
  simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- The zero function solves Hill's equation. -/
theorem isHillSolution_zero (Q : ℝ → ℂ) (lam : ℂ) : IsHillSolution Q lam 0 := by
  refine ⟨differentiable_const _, fun x => ?_⟩
  have : deriv (0 : ℝ → ℂ) = 0 := by funext y; simp
  rw [this]; simp

/-- The solutions of Hill's equation with multiplier `s`, `w(x + π) = s w(x)`, as a
`ℂ`-submodule of `ℝ → ℂ`. For `s = 1` these are the `π`-periodic solutions, for `s = -1` the
`π`-antiperiodic solutions (of period `2π`), DLMF 28.29(ii)–(iii). -/
def hillMultiplierSolutions (Q : ℝ → ℂ) (lam s : ℂ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {w | IsHillSolution Q lam w ∧ ∀ x, w (x + Real.pi) = s * w x}
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    exact ⟨hu.add hv, fun x => by simp only [Pi.add_apply, hu' x, hv' x]; ring⟩
  zero_mem' := ⟨isHillSolution_zero Q lam, fun x => by simp⟩
  smul_mem' := by
    rintro c u ⟨hu, hu'⟩
    exact ⟨hu.const_smul c, fun x => by simp only [Pi.smul_apply, smul_eq_mul, hu' x]; ring⟩

/-! ### §28.29(iii) Periodic and antiperiodic eigenvalues (real `Q`) -/

/-- The number of real `λ ≤ t` for which Hill's equation with the real potential `Q` has a
nontrivial solution with multiplier `s`, each counted with the dimension of its solution
space (a `finsum`, so a junk `0` if infinitely many `λ ≤ t` contribute). -/
def hillEigenCount (Q : ℝ → ℝ) (s : ℂ) (t : ℝ) : ℕ :=
  ∑ᶠ (lam : ℝ) (_ : lam ≤ t),
    Module.finrank ℂ (hillMultiplierSolutions (fun x => (Q x : ℂ)) lam s)

/-- The **periodic eigenvalues** `λ_n`, `n = 0, 1, 2, …` of Hill's equation with real
potential `Q` (DLMF 28.29.16): the real `λ` with a nontrivial `π`-periodic solution, in
increasing order and repeated according to the dimension of the periodic solution space.
Definition by counting: `λ_n = inf {t | #{eigenvalues ≤ t} ≥ n + 1}`. -/
@[dlmf 28.29.E16]
def hillPeriodicEigenvalue (Q : ℝ → ℝ) (n : ℕ) : ℝ :=
  sInf {t : ℝ | n + 1 ≤ hillEigenCount Q 1 t}

/-- The **antiperiodic eigenvalues** `μ_n`, `n = 1, 2, 3, …` of Hill's equation with real
potential `Q` (DLMF 28.29.17): the real `λ` with a nontrivial solution satisfying
`w(x + π) = -w(x)` (so of period `2π`), increasing and repeated according to multiplicity.
Definition by counting: `μ_n = inf {t | #{eigenvalues ≤ t} ≥ n}`; `n = 0` is a junk index. -/
@[dlmf 28.29.E17]
def hillAntiperiodicEigenvalue (Q : ℝ → ℝ) (n : ℕ) : ℝ :=
  sInf {t : ℝ | n ≤ hillEigenCount Q (-1) t}

/-- The characteristic values `λ̂_m`, `m = 0, 1, 2, …` of DLMF 28.30(i): the periodic and
antiperiodic eigenvalues 28.29.16–28.29.17 merged in their natural order (28.29.18),
`λ_0, μ_1, μ_2, λ_1, λ_2, μ_3, μ_4, λ_3, λ_4, …`. -/
@[dlmf 28.30.i]
def hillEigenvalueHat (Q : ℝ → ℝ) (m : ℕ) : ℝ :=
  if m = 0 then hillPeriodicEigenvalue Q 0
  else if (m - 1) % 4 < 2 then hillAntiperiodicEigenvalue Q (2 * ((m - 1) / 4) + (m - 1) % 4 + 1)
  else hillPeriodicEigenvalue Q (2 * ((m - 1) / 4) + (m - 1) % 4 - 1)

/-- `w : ℕ → ℝ → ℝ` is an **orthonormal set of eigenfunctions** of Hill's equation with real
potential `Q` (DLMF 28.30.1–28.30.2): each `w m` is a `2π`-periodic solution with
`λ = λ̂_m`, and `(2π)⁻¹ ∫₀^{2π} w_m w_n = δ_{mn}`. -/
@[dlmf 28.30.i]
def IsHillEigenfunctionFamily (Q : ℝ → ℝ) (w : ℕ → ℝ → ℝ) : Prop :=
  (∀ m, IsHillSolution (fun x => (Q x : ℂ)) (hillEigenvalueHat Q m) (fun x => (w m x : ℂ)) ∧
      Function.Periodic (w m) (2 * Real.pi)) ∧
    ∀ m n, (1 / (2 * Real.pi)) * ∫ x in (0 : ℝ)..2 * Real.pi, w m x * w n x =
      if m = n then 1 else 0

/-- The **mean square** `N = (1/π) ∫₀^π Q(x)² dx` of a real potential (DLMF 28.29.19). -/
@[dlmf 28.29.E19]
def hillMeanSquare (Q : ℝ → ℝ) : ℝ :=
  (1 / Real.pi) * ∫ x in (0 : ℝ)..Real.pi, Q x ^ 2

/-! ### §28.31 Equations of Whittaker–Hill and Ince -/

/-- The **equation of Whittaker–Hill** (DLMF 28.31.1),
`W'' + (A + B cos 2z - ½ (kc)² cos 4z) W = 0`, for an entire function `W` and constants
`A, B, k, c`. -/
@[dlmf 28.31.E1]
def IsWhittakerHillSolution (A B k c : ℂ) (W : ℂ → ℂ) : Prop :=
  Differentiable ℂ W ∧ ∀ z : ℂ, HasDerivAt (deriv W)
    (-(A + B * Complex.cos (2 * z) - (k * c) ^ 2 / 2 * Complex.cos (4 * z)) * W z) z

/-- The **equation of Ince** (DLMF 28.31.3),
`w'' + ξ sin(2z) w' + (η - p ξ cos(2z)) w = 0`, for an entire function `w`. -/
@[dlmf 28.31.E3]
def IsInceSolution (ξ η p : ℂ) (w : ℂ → ℂ) : Prop :=
  Differentiable ℂ w ∧ ∀ z : ℂ, HasDerivAt (deriv w)
    (-(ξ * Complex.sin (2 * z) * deriv w z) - (η - p * ξ * Complex.cos (2 * z)) * w z) z

/-- The summability condition for a Fourier series `∑ A_k cos kz` (or `∑ B_k sin kz`) to
define an entire function that can be differentiated termwise twice. -/
def IsEntireFourierCoeff (A : ℕ → ℂ) : Prop :=
  ∀ R : ℝ, Summable (fun k : ℕ => ‖A k‖ * ((k : ℝ) + 1) ^ 2 * Real.exp (k * R))

/-- The frequencies `k ≤ p` with `k ≡ p (mod 2)` of the Ince polynomials of degree `p`. -/
def inceFrequencies (p : ℕ) : Finset ℕ :=
  (Finset.range (p + 1)).filter (fun k => k % 2 = p % 2)

/-- `f` is a cosine Ince polynomial of degree `p`: `f(z) = ∑ A_k cos(kz)` over
`k ≤ p`, `k ≡ p (mod 2)`, with real coefficients (the form of `C_p^m`, DLMF 28.31.10). -/
def IsInceCosPoly (p : ℕ) (f : ℂ → ℂ) : Prop :=
  ∃ A : ℕ → ℝ, ∀ z : ℂ, f z = ∑ k ∈ inceFrequencies p, (A k : ℂ) * Complex.cos (k * z)

/-- `f` is a sine Ince polynomial of degree `p`: `f(z) = ∑ B_k sin(kz)` over `k ≤ p`,
`k ≡ p (mod 2)`, with real coefficients (the form of `S_p^m`, DLMF 28.31.11). -/
def IsInceSinPoly (p : ℕ) (f : ℂ → ℂ) : Prop :=
  ∃ B : ℕ → ℝ, ∀ z : ℂ, f z = ∑ k ∈ inceFrequencies p, (B k : ℂ) * Complex.sin (k * z)

/-- The number of zeros of `f` on the real interval `[0, π)`. -/
def zerosIco (f : ℂ → ℂ) : ℕ := {x : ℝ | x ∈ Ico 0 Real.pi ∧ f x = 0}.ncard

/-- The Ince eigenvalue `a_p^m(ξ)` for real `ξ` (DLMF §28.31(ii)): the unique real `η` for
which Ince's equation 28.31.3 has a nontrivial cosine Ince polynomial solution of degree `p`
with exactly `m` zeros in `[0, π)`. Definition by choice; `0` if there is no unique such `η`
(in particular for `m ≢ p (mod 2)` or `m > p`). -/
def inceA (p m : ℕ) (ξ : ℝ) : ℝ :=
  if h : ∃! η : ℝ, ∃ f : ℂ → ℂ, IsInceCosPoly p f ∧ (∃ z, f z ≠ 0) ∧
      IsInceSolution ξ η p f ∧ zerosIco f = m then h.choose else 0

/-- The Ince eigenvalue `b_p^m(ξ)` for real `ξ` (DLMF §28.31(ii)), as `inceA` with sine Ince
polynomials (the zero at `z = 0` is counted). -/
def inceB (p m : ℕ) (ξ : ℝ) : ℝ :=
  if h : ∃! η : ℝ, ∃ f : ℂ → ℂ, IsInceSinPoly p f ∧ (∃ z, f z ≠ 0) ∧
      IsInceSolution ξ η p f ∧ zerosIco f = m then h.choose else 0

/-- The **Ince polynomial** `C_p^m(z, ξ)` (DLMF 28.31.10) for real `ξ`: the cosine Ince
polynomial solution of 28.31.3 with `η = a_p^m(ξ)`, normalized by
`(1/π) ∫₀^{2π} (C_p^m)² dx = 1` (28.31.12) and `C_p^m(0, ξ) > 0`. Definition by choice; `0`
if it does not exist uniquely. -/
@[dlmf 28.31.E10]
def inceC (p m : ℕ) (z : ℂ) (ξ : ℝ) : ℂ :=
  if h : ∃! f : ℂ → ℂ, IsInceCosPoly p f ∧ IsInceSolution ξ (inceA p m ξ) p f ∧
      (1 / Real.pi : ℂ) * ∫ x in (0 : ℝ)..2 * Real.pi, f x ^ 2 = 1 ∧ 0 < (f 0).re
  then h.choose z else 0

/-- The **Ince polynomial** `S_p^m(z, ξ)` (DLMF 28.31.11) for real `ξ`: the sine Ince
polynomial solution of 28.31.3 with `η = b_p^m(ξ)`, normalized by 28.31.12 and with
`S_p^m'(0, ξ) > 0`. Definition by choice; `0` if it does not exist uniquely. -/
@[dlmf 28.31.E11]
def inceS (p m : ℕ) (z : ℂ) (ξ : ℝ) : ℂ :=
  if h : ∃! f : ℂ → ℂ, IsInceSinPoly p f ∧ IsInceSolution ξ (inceB p m ξ) p f ∧
      (1 / Real.pi : ℂ) * ∫ x in (0 : ℝ)..2 * Real.pi, f x ^ 2 = 1 ∧ 0 < (deriv f 0).re
  then h.choose z else 0

/-- The **paraboloidal wave function** `hc_p^m(z, ξ) = e^{-ξ cos(2z)/4} C_p^m(z, ξ)`
(DLMF 28.31.16). -/
@[dlmf 28.31.E16]
def paraboloidalHc (p m : ℕ) (z : ℂ) (ξ : ℝ) : ℂ :=
  Complex.exp (-(ξ * Complex.cos (2 * z)) / 4) * inceC p m z ξ

/-- The **paraboloidal wave function** `hs_p^m(z, ξ) = e^{-ξ cos(2z)/4} S_p^m(z, ξ)`
(DLMF 28.31.17). -/
@[dlmf 28.31.E17]
def paraboloidalHs (p m : ℕ) (z : ℂ) (ξ : ℝ) : ℂ :=
  Complex.exp (-(ξ * Complex.cos (2 * z)) / 4) * inceS p m z ξ

end DLMF.Mathieu
