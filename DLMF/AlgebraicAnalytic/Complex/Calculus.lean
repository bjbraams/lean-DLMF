/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.AlgebraicAnalytic.Complex.Basic
public import DLMFMathlib.Analysis.Complex.PowerSeriesOperations
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import TauCeti.Analysis.Contour.AbsolutelyContinuous
public import TauCeti.Analysis.Contour.Curve.Integrability
public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Basic
public import TauCeti.Analysis.Contour.Winding.UnboundedComponent

/-!
# Calculus of a complex variable (DLMF §1.9)

Statements of DLMF §1.9 that are not, in the stated generality, in Mathlib or Tau Ceti; the
upstream items are recorded as `dlmf_upstream` pointers in
`DLMF.AlgebraicAnalytic.Complex.MathlibCoverage`.

Conventions.
* **Phase.** Mathlib's `Complex.arg` takes values in `(-π, π]`, which is the single-valued
  principal phase of DLMF §1.9(i) ("if we require a principal value to be single-valued, then
  we can restrict `-π < ph z ≤ π`"). DLMF's principal value `-π ≤ ph z ≤ π` is two-valued on the
  negative real axis, where Lean takes `π`. The multivalued phase is `IsPhase z θ`; the identities
  1.9.13, 1.9.18, 1.9.20 hold for general phases (proved here) but not for principal values
  (Mathlib: `Complex.arg_conj`, `Complex.arg_mul_coe_angle`, `Complex.arg_div_coe_angle`).
* **Contours.** Contours are Tau Ceti's piecewise `C¹` curves; `IsSimpleClosedContour`,
  `contourInterior`, `contourExterior`, `IsPositivelyOriented` and `contourIntegral` are in
  `DLMF.AlgebraicAnalytic.Complex.Basic`. Tau Ceti proves Cauchy's theorem and formula in the
  homology form (holomorphy on an open set containing the curve, null-homologous curve); the DLMF
  forms, with continuity up to a Jordan contour and holomorphy only inside, are admitted here.
* **Series.** DLMF's series converge as partial sums; Mathlib's `HasSum` is unconditional. They
  agree for absolutely convergent series; partial sums are used where DLMF's statement is about
  conditional convergence (1.9.51).

Proved here: the quadrant formulas 1.9.5–1.9.6 for `arg`, the characterization of the phase
1.9.7 and the general-phase identities 1.9.13, 1.9.18, 1.9.20, the division formula 1.9.16,
De Moivre's theorem 1.9.22 for `n ∈ ℤ` (and complex `θ`), the triangle inequality 1.9.23, the
Cauchy–Riemann equations 1.9.25, the arithmetic of `∞` (1.9.36–1.9.39), the bilinear
transformation formulas 1.9.41–1.9.44 and the invariance of the cross ratio 1.9.45, the
binomial decomposition 1.9.21, the Cauchy product identity 1.9.51–1.9.52 via Mathlib’s
Abel limit theorem, the reciprocal-series convergence 1.9.53–1.9.54 via analytic inversion,
the logarithm and principal-power series 1.9.57 and 1.9.60 via their differential identities,
termwise differentiation 1.9.63 via Mathlib’s Cauchy–Taylor theorem, the
recurrence values 1.9.55, 1.9.58, 1.9.61, the double-limit theorem of §1.9(vii), and the
vanishing of the winding number on the exterior of a closed contour (from Tau Ceti).
-/

@[expose] public noncomputable section

open Complex Filter Set Metric MeasureTheory
open scoped Topology OnePoint ComplexConjugate

namespace DLMF.AlgebraicAnalytic

/-! ## §1.9(i) Complex numbers -/

/-- Identity under the stated parameter and domain assumptions: `arg z = Real.arctan (z.im /
z.re)`. -/
private lemma g1c_arg_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    arg z = Real.arctan (z.im / z.re) := by
  have h := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  rw [← tan_arg, Real.arctan_tan h.1 h.2]

/-- DLMF 1.9.5–1.9.6, first quadrant: for `x > 0`, `y ≥ 0`, `ph z = ω = arctan |y/x|`. -/
@[dlmf 1.9.E5, dlmf 1.9.E6]
theorem arg_eq_arctan_of_re_pos_of_im_nonneg {z : ℂ} (hx : 0 < z.re) (hy : 0 ≤ z.im) :
    arg z = Real.arctan |z.im / z.re| := by
  rw [g1c_arg_of_re_pos hx, abs_of_nonneg (div_nonneg hy hx.le)]

/-- DLMF 1.9.5–1.9.6, fourth quadrant: for `x > 0`, `y < 0`, `ph z = -ω`. -/
@[dlmf 1.9.E5, dlmf 1.9.E6]
theorem arg_eq_neg_arctan_of_re_pos_of_im_neg {z : ℂ} (hx : 0 < z.re) (hy : z.im < 0) :
    arg z = -Real.arctan |z.im / z.re| := by
  rw [g1c_arg_of_re_pos hx, abs_of_neg (div_neg_of_neg_of_pos hy hx), Real.arctan_neg, neg_neg]

/-- DLMF 1.9.5–1.9.6, second quadrant: for `x < 0`, `y ≥ 0`, `ph z = π - ω` (on the negative
real axis this is Lean's single-valued choice `π`). -/
@[dlmf 1.9.E5, dlmf 1.9.E6]
theorem arg_eq_pi_sub_arctan_of_re_neg_of_im_nonneg {z : ℂ} (hx : z.re < 0) (hy : 0 ≤ z.im) :
    arg z = Real.pi - Real.arctan |z.im / z.re| := by
  have hn : 0 < (-z).re := by simpa using hx
  have h := g1c_arg_of_re_pos hn
  simp only [neg_re, neg_im, neg_div_neg_eq] at h
  rcases hy.lt_or_eq with hy | hy
  · rw [arg_neg_eq_arg_sub_pi_of_im_pos hy] at h
    rw [abs_of_neg (div_neg_of_pos_of_neg hy hx), Real.arctan_neg]
    linarith
  · rw [← hy, zero_div, abs_zero, Real.arctan_zero, sub_zero]
    exact arg_eq_pi_iff.mpr ⟨hx, hy.symm⟩

/-- DLMF 1.9.5–1.9.6, third quadrant: for `x < 0`, `y < 0`, `ph z = -π + ω`. -/
@[dlmf 1.9.E5, dlmf 1.9.E6]
theorem arg_eq_neg_pi_add_arctan_of_re_neg_of_im_neg {z : ℂ} (hx : z.re < 0) (hy : z.im < 0) :
    arg z = -Real.pi + Real.arctan |z.im / z.re| := by
  have hn : 0 < (-z).re := by simpa using hx
  have h := g1c_arg_of_re_pos hn
  simp only [neg_re, neg_im, neg_div_neg_eq] at h
  rw [arg_neg_eq_arg_add_pi_of_im_neg hy] at h
  rw [abs_of_pos (div_pos_of_neg_of_neg hy hx)]
  linarith

/-- DLMF 1.9.7: the principal value `arg z` is a phase of `z` (`z = |z| e^{i arg z}`). -/
@[dlmf 1.9.E7]
theorem isPhase_arg (z : ℂ) : IsPhase z (arg z) := (norm_mul_exp_arg_mul_I z).symm

/-- DLMF 1.9.7: for `z ≠ 0` the phases of `z` are exactly `ph z = arg z + 2nπ`, `n ∈ ℤ`. -/
@[dlmf 1.9.E7]
theorem isPhase_iff {z : ℂ} (hz : z ≠ 0) {θ : ℝ} :
    IsPhase z θ ↔ ∃ n : ℤ, θ = arg z + 2 * n * Real.pi := by
  have hn : (‖z‖ : ℂ) ≠ 0 := by simpa using hz
  have hz' := norm_mul_exp_arg_mul_I z
  constructor
  · intro h
    have he : exp (θ * I) = exp (arg z * I) := by
      apply mul_left_cancel₀ hn
      rw [hz', ← h]
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.mp he
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp at this
    linarith
  · rintro ⟨n, rfl⟩
    unfold IsPhase
    conv_lhs => rw [← hz']
    congr 1
    rw [exp_eq_exp_iff_exists_int]
    exact ⟨-n, by push_cast; ring⟩

/-- DLMF 1.9.13 (general phases): if `θ` is a phase of `z` then `-θ` is a phase of `z̄`. (For
principal values, `arg z̄ = -arg z` fails on the negative real axis; Mathlib's
`Complex.arg_conj`.) -/
@[dlmf 1.9.E13]
theorem IsPhase.conj {z : ℂ} {θ : ℝ} (h : IsPhase z θ) : IsPhase (conj z) (-θ) := by
  unfold IsPhase at h ⊢
  rw [norm_conj]
  conv_lhs => rw [h]
  rw [map_mul, Complex.conj_ofReal, ← exp_conj]
  congr 2
  simp [map_mul]

/-- DLMF 1.9.18 (general phases): `ph(z₁z₂) = ph z₁ + ph z₂`. -/
@[dlmf 1.9.E18]
theorem IsPhase.mul {z₁ z₂ : ℂ} {θ₁ θ₂ : ℝ} (h₁ : IsPhase z₁ θ₁) (h₂ : IsPhase z₂ θ₂) :
    IsPhase (z₁ * z₂) (θ₁ + θ₂) := by
  unfold IsPhase at *
  rw [norm_mul]
  conv_lhs => rw [h₁, h₂]
  push_cast
  rw [add_mul, exp_add]
  ring

/-- DLMF 1.9.20 (general phases): `ph(z₁/z₂) = ph z₁ - ph z₂` (for `z₂ = 0` both sides are
degenerate: `z₁/0 = 0` in Lean and every angle is a phase of `0`). -/
@[dlmf 1.9.E20]
theorem IsPhase.div {z₁ z₂ : ℂ} {θ₁ θ₂ : ℝ} (h₁ : IsPhase z₁ θ₁) (h₂ : IsPhase z₂ θ₂) :
    IsPhase (z₁ / z₂) (θ₁ - θ₂) := by
  unfold IsPhase at *
  rw [norm_div]
  conv_lhs => rw [h₁, h₂]
  push_cast
  rw [sub_mul, exp_sub]
  field_simp

/-- DLMF 1.9.16: `z₁/z₂ = z₁ z̄₂/|z₂|² = (x₁x₂ + y₁y₂ + i(x₂y₁ - x₁y₂))/(x₂² + y₂²)`. No
hypothesis is needed in Lean (for `z₂ = 0` all three expressions are `0`); DLMF assumes
`z₂ ≠ 0`. -/
@[dlmf 1.9.E16]
theorem div_eq_mul_conj_div (z₁ z₂ : ℂ) :
    z₁ / z₂ = z₁ * conj z₂ / (‖z₂‖ ^ 2 : ℝ) ∧
      z₁ / z₂ = (z₁.re * z₂.re + z₁.im * z₂.im + I * (z₂.re * z₁.im - z₁.re * z₂.im)) /
        (z₂.re ^ 2 + z₂.im ^ 2 : ℝ) := by
  have h1 : z₁ / z₂ = z₁ * conj z₂ / (‖z₂‖ ^ 2 : ℝ) := by
    rw [div_eq_mul_inv, inv_def, Complex.sq_norm, Complex.ofReal_inv]
    ring
  refine ⟨h1, ?_⟩
  rw [h1, Complex.sq_norm, normSq_apply]
  congr 1
  · apply Complex.ext <;> simp; ring
  · push_cast; ring

/-- Split a finite complex sum into its even and odd indices. -/
private lemma sum_range_even_odd (f : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ Finset.range N, f k =
      (∑ k ∈ Finset.range ((N + 1) / 2), f (2 * k)) +
        ∑ k ∈ Finset.range (N / 2), f (2 * k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rcases Nat.mod_two_eq_zero_or_one N with hN | hN
    · have h₁ : (N + 1) / 2 = N / 2 := by omega
      have h₂ : (N + 1 + 1) / 2 = N / 2 + 1 := by omega
      have h₃ : 2 * (N / 2) = N := by omega
      simp only [Finset.sum_range_succ, ih, h₁, h₂, h₃]
      ring
    · have h₁ : (N + 1) / 2 = N / 2 + 1 := by omega
      have h₂ : (N + 1 + 1) / 2 = N / 2 + 1 := by omega
      have h₃ : 2 * (N / 2) + 1 = N := by omega
      simp only [Finset.sum_range_succ, ih, h₁, h₂, h₃]
      ring

/-- DLMF 1.9.21: the real and imaginary parts of `zⁿ`, `z = x + iy`:
`zⁿ = (xⁿ - C(n,2) x^{n-2} y² + C(n,4) x^{n-4} y⁴ - ⋯) + i(C(n,1) x^{n-1} y - C(n,3) x^{n-3} y³
+ ⋯)`. -/
@[dlmf 1.9.E21]
theorem pow_eq_sum_choose (z : ℂ) (n : ℕ) :
    z ^ n = ((∑ k ∈ Finset.range (n / 2 + 1),
        (-1 : ℝ) ^ k * n.choose (2 * k) * z.re ^ (n - 2 * k) * z.im ^ (2 * k) : ℝ) : ℂ) +
      I * ((∑ k ∈ Finset.range ((n + 1) / 2),
        (-1 : ℝ) ^ k * n.choose (2 * k + 1) * z.re ^ (n - (2 * k + 1)) * z.im ^ (2 * k + 1) :
          ℝ) : ℂ) := by
  have hz : z = (z.im : ℂ) * I + (z.re : ℂ) := by apply Complex.ext <;> simp
  conv_lhs => rw [hz, add_pow, sum_range_even_odd]
  have heven : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
  rw [heven]
  push_cast
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [mul_pow, show I ^ (2 * k) = (-1 : ℂ) ^ k by rw [pow_mul, I_sq]]
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_pow, show I ^ (2 * k + 1) = (-1 : ℂ) ^ k * I by
      rw [pow_add, pow_mul, I_sq, pow_one]]
    ring

/-- DLMF 1.9.22 (De Moivre's theorem): `cos nθ + i sin nθ = (cos θ + i sin θ)ⁿ` for `n ∈ ℤ`.
Stronger than DLMF: `θ` may be complex. -/
@[dlmf 1.9.E22]
theorem cos_add_sin_mul_I_zpow (θ : ℂ) (n : ℤ) :
    cos (n * θ) + I * sin (n * θ) = (cos θ + I * sin θ) ^ n := by
  rw [mul_comm I, mul_comm I, cos_add_sin_I, cos_add_sin_I, ← exp_int_mul, mul_assoc]

/-- DLMF 1.9.23 (triangle inequality): `||z₁| - |z₂|| ≤ |z₁ + z₂| ≤ |z₁| + |z₂|`. -/
@[dlmf 1.9.E23]
theorem abs_norm_sub_norm_le_norm_add_le (z₁ z₂ : ℂ) :
    |‖z₁‖ - ‖z₂‖| ≤ ‖z₁ + z₂‖ ∧ ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := by
  refine ⟨?_, norm_add_le z₁ z₂⟩
  simpa [norm_neg, sub_neg_eq_add] using abs_norm_sub_norm_le z₁ (-z₂)

/-! ## §1.9(ii) Differentiation -/

/-- DLMF 1.9.25 (Cauchy–Riemann equations): if `f'(z)` exists at `z = x + iy` and
`f = u + iv`, then the partial derivatives of `u(x, y) = ℜf(x + iy)` and `v(x, y) = ℑf(x + iy)`
exist at `(x, y)` with `∂u/∂x = ∂v/∂y = ℜf'(z)` and `∂u/∂y = -∂v/∂x = -ℑf'(z)`. -/
@[dlmf 1.9.E25]
theorem hasDerivAt_re_im_of_hasDerivAt {f : ℂ → ℂ} {f' : ℂ} {x y : ℝ}
    (hf : HasDerivAt f f' (x + y * I)) :
    HasDerivAt (fun t : ℝ => (f (t + y * I)).re) f'.re x ∧
      HasDerivAt (fun t : ℝ => (f (x + t * I)).im) f'.re y ∧
      HasDerivAt (fun t : ℝ => (f (x + t * I)).re) (-f'.im) y ∧
      HasDerivAt (fun t : ℝ => (f (t + y * I)).im) f'.im x := by
  have hx : HasDerivAt (fun t : ℝ => f (t + y * I)) f' x := by
    have hγ : HasDerivAt (fun t : ℝ => (t : ℂ) + y * I) 1 x :=
      (Complex.ofRealCLM.hasDerivAt).add_const _
    exact (hf.comp x hγ).congr_deriv (mul_one f')
  have hy : HasDerivAt (fun t : ℝ => f (x + t * I)) (f' * I) y := by
    have hγ : HasDerivAt (fun t : ℝ => (x : ℂ) + t * I) I y := by
      simpa using ((Complex.ofRealCLM.hasDerivAt).mul_const I).const_add (x : ℂ)
    exact hf.comp y hγ
  have hre := fun {g : ℝ → ℂ} {g' : ℂ} {t : ℝ} (h : HasDerivAt g g' t) =>
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h)
  have him := fun {g : ℝ → ℂ} {g' : ℂ} {t : ℝ} (h : HasDerivAt g g' t) =>
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hre hx).congr_deriv (by simp)
  · exact (him hy).congr_deriv (by simp)
  · exact (hre hy).congr_deriv (by simp)
  · exact (him hx).congr_deriv (by simp)

/-- DLMF §1.9(ii) (converse of the Cauchy–Riemann equations): if at `z = x + iy` the partial
derivatives of `u = ℜf` and `v = ℑf` (as functions of `(x, y) ∈ ℝ²`) exist in a neighbourhood,
are continuous at `(x, y)` and satisfy 1.9.25 there, then `f` is complex differentiable at `z`.
Formalized with the real Fréchet derivative: if `f` is real `C¹` near `z` and its real
derivative at `z` is complex linear (`Df(z) i = i Df(z) 1`, which is 1.9.25), then `f` is
complex differentiable at `z`. -/
@[dlmf 1.9.ii]
theorem differentiableAt_of_cauchyRiemann {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 1 f z) (hcr : fderiv ℝ f z I = I * fderiv ℝ f z 1) :
    DifferentiableAt ℂ f z := by
  -- Mathlib's Cauchy–Riemann criterion only needs real differentiability.
  exact differentiableAt_complex_iff_differentiableAt_real.mpr
    ⟨hf.differentiableAt (by norm_num), by simpa only [smul_eq_mul] using hcr⟩

/-- DLMF 1.9.27 (Laplace's equation in polar coordinates): if `u` is harmonic at
`z = r e^{iθ}`, `r > 0`, then `U(ρ, φ) = u(ρ e^{iφ})` satisfies
`∂²U/∂r² + r⁻¹ ∂U/∂r + r⁻² ∂²U/∂θ² = 0` at `(r, θ)`. -/
@[dlmf 1.9.E27]
theorem harmonic_polar {u : ℂ → ℝ} {r θ : ℝ} (hr : 0 < r)
    (hu : InnerProductSpace.HarmonicAt u (r * exp (θ * I))) :
    deriv (deriv fun ρ : ℝ => u (ρ * exp (θ * I))) r +
        r⁻¹ * deriv (fun ρ : ℝ => u (ρ * exp (θ * I))) r +
        (r ^ 2)⁻¹ * deriv (deriv fun φ : ℝ => u (r * exp (φ * I))) θ = 0 := by
  sorry

/-! ## §1.9(iii) Integration -/

/-- DLMF §1.9(iii) (Jordan curve theorem): a simple closed contour `C` divides `ℂ` into two open
domains, the bounded interior and the unbounded exterior, that have `C` as common boundary.
Tau Ceti proves the separation (`TauCeti.IsJordanCurve.not_isPreconnected_compl`), the
nonemptiness of the inside (`TauCeti.IsJordanCurve.nonempty_filledHull_sdiff`) and that `C` is
the frontier of every complementary component
(`TauCeti.IsJordanCurve.frontier_connectedComponentIn`); the connectedness of the two domains
is admitted here. -/
@[dlmf 1.9.iii]
theorem IsSimpleClosedContour.jordan {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsSimpleClosedContour γ a b) :
    IsOpen (contourInterior γ a b) ∧ IsConnected (contourInterior γ a b) ∧
      Bornology.IsBounded (contourInterior γ a b) ∧
      IsOpen (contourExterior γ a b) ∧ IsConnected (contourExterior γ a b) ∧
      ¬ Bornology.IsBounded (contourExterior γ a b) ∧
      (γ '' Icc a b)ᶜ = contourInterior γ a b ∪ contourExterior γ a b ∧
      frontier (contourInterior γ a b) = γ '' Icc a b ∧
      frontier (contourExterior γ a b) = γ '' Icc a b := by
  sorry

/-- DLMF 1.9.29 (Cauchy's theorem): if `f` is continuous within and on a simple closed contour
`C` and analytic within `C`, then `∫_C f(z) dz = 0`. (Tau Ceti's
`TauCeti.Contour.homologyCauchyTheorem` assumes holomorphy on an open set containing `C`.) -/
@[dlmf 1.9.E29]
theorem IsSimpleClosedContour.contourIntegral_eq_zero {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    (hγ : IsSimpleClosedContour γ a b)
    (hc : ContinuousOn f (contourInterior γ a b ∪ γ '' Icc a b))
    (hd : DifferentiableOn ℂ f (contourInterior γ a b)) :
    contourIntegral γ a b f = 0 := by
  sorry

/-- DLMF 1.9.30 (Cauchy's integral formula): if `f` is continuous within and on a simple closed
contour `C`, analytic within `C`, `C` is described in the positive sense and `z₀` lies within
`C`, then `f(z₀) = (2πi)⁻¹ ∫_C f(z)/(z - z₀) dz`. -/
@[dlmf 1.9.E30]
theorem IsSimpleClosedContour.cauchyIntegralFormula {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (hγ : IsSimpleClosedContour γ a b) (hpos : IsPositivelyOriented γ a b)
    (hc : ContinuousOn f (contourInterior γ a b ∪ γ '' Icc a b))
    (hd : DifferentiableOn ℂ f (contourInterior γ a b)) (hz₀ : z₀ ∈ contourInterior γ a b) :
    f z₀ = (2 * Real.pi * I)⁻¹ * contourIntegral γ a b (fun z => f z / (z - z₀)) := by
  sorry

/-- DLMF 1.9.31 (Cauchy's integral formula for derivatives): under the hypotheses of 1.9.30,
`f⁽ⁿ⁾(z₀) = n!/(2πi) ∫_C f(z)/(z - z₀)^{n+1} dz`, `n = 1, 2, …` (also `n = 0`). -/
@[dlmf 1.9.E31]
theorem IsSimpleClosedContour.cauchyIntegralFormula_iteratedDeriv {γ : ℝ → ℂ} {a b : ℝ}
    {f : ℂ → ℂ} {z₀ : ℂ} (hγ : IsSimpleClosedContour γ a b) (hpos : IsPositivelyOriented γ a b)
    (hc : ContinuousOn f (contourInterior γ a b ∪ γ '' Icc a b))
    (hd : DifferentiableOn ℂ f (contourInterior γ a b)) (hz₀ : z₀ ∈ contourInterior γ a b)
    (n : ℕ) :
    iteratedDeriv n f z₀ =
      n.factorial / (2 * Real.pi * I) *
        contourIntegral γ a b (fun z => f z / (z - z₀) ^ (n + 1)) := by
  sorry

/-- DLMF 1.9.32: for a closed contour `C` and `z₀ ∉ C`, `(2πi)⁻¹ ∫_C dz/(z - z₀)` is an integer,
the winding number `𝒩(C, z₀)` (Tau Ceti's `TauCeti.Contour.windingNumber`, which equals this
integral off the curve). -/
@[dlmf 1.9.E32]
theorem windingNumber_eq_intCast {γ : ℝ → ℂ} {a b : ℝ} (hγ : TauCeti.Contour.IsPiecewiseC1On γ a b)
    (hcl : γ a = γ b) {z₀ : ℂ} (hz₀ : z₀ ∉ γ '' uIcc a b) :
    ∃ n : ℤ, TauCeti.Contour.windingNumber γ a b z₀ = n ∧
      (2 * Real.pi * I)⁻¹ * contourIntegral γ a b (fun z => (z - z₀)⁻¹) = n := by
  -- TauCeti supplies both integrality and the ordinary integral formula for this contour.
  have hac : AbsolutelyContinuousOnInterval γ a b :=
    TauCeti.Contour.IsPiecewiseC1On.absolutelyContinuousOnInterval hγ
  obtain ⟨n, hn⟩ := hac.exists_int_windingNumber hcl hz₀
  refine ⟨n, hn, ?_⟩
  rw [hac.windingNumber_eq_integral hz₀] at hn
  simpa [DLMF.AlgebraicAnalytic.contourIntegral, smul_eq_mul, mul_comm] using hn

/-- DLMF §1.9(iii) (winding number of a simple closed contour): the winding number of a simple
closed contour is constant, equal to `1` or to `-1`, on its interior; the positive sense
(`IsPositivelyOriented`) is the case `1`. -/
@[dlmf 1.9.iii]
theorem IsSimpleClosedContour.windingNumber_eq_one_or_neg_one {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : IsSimpleClosedContour γ a b) :
    (∀ z ∈ contourInterior γ a b, TauCeti.Contour.windingNumber γ a b z = 1) ∨
      ∀ z ∈ contourInterior γ a b, TauCeti.Contour.windingNumber γ a b z = -1 := by
  sorry

/-- DLMF §1.9(iii) (winding number outside a closed contour): `𝒩(C, z₀) = 0` for `z₀` in the
exterior of a closed contour. From Tau Ceti's
`TauCeti.Contour.IsPiecewiseC1On.windingNumber_eq_zero_of_unbounded_component`. -/
@[dlmf 1.9.iii]
theorem windingNumber_eq_zero_of_mem_contourExterior {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : TauCeti.Contour.IsPiecewiseC1On γ a b) (hcl : γ a = γ b) {z₀ : ℂ}
    (hz₀ : z₀ ∈ contourExterior γ a b) : TauCeti.Contour.windingNumber γ a b z₀ = 0 := by
  refine hγ.windingNumber_eq_zero_of_unbounded_component hcl ?_
  rw [uIcc_of_le hab]
  rw [contourExterior, Set.mem_compl_iff, TauCeti.mem_filledHull_iff] at hz₀
  exact hz₀

/-! ## §1.9(iv) Conformal mapping -/

/-- DLMF 1.9.35: the sets `S_r = {z | |z| > 1/r} ∪ {∞}`, `0 < r < ∞`, form a basis of
neighbourhoods of `∞` in the extended plane `OnePoint ℂ`. -/
@[dlmf 1.9.E35]
theorem hasBasis_nhds_infty :
    (𝓝 (∞ : OnePoint ℂ)).HasBasis (fun r : ℝ => 0 < r)
      (fun r => ((↑) : ℂ → OnePoint ℂ) '' {z | 1 / r < ‖z‖} ∪ {∞}) := by
  have hb : (Bornology.cobounded ℂ).HasBasis (fun r : ℝ => 0 < r)
      (fun r => {z : ℂ | 1 / r < ‖z‖}) := by
    refine (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).to_hasBasis
      (fun R _ => ?_) (fun r _ => ?_)
    · refine ⟨1 / (|R| + 1), by positivity, fun z hz => ?_⟩
      simp only [Set.mem_ofPred_eq, one_div_one_div] at hz
      simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using
        (lt_of_le_of_lt (le_abs_self R) (lt_trans (lt_add_one _) hz))
    · exact ⟨1 / r, trivial, by simp only [Set.compl_ofPred, Metric.closedBall,
        dist_zero_right, not_le]; exact Set.Subset.rfl⟩
  rw [OnePoint.nhds_infty_eq, coclosedCompact_eq_cocompact,
    ← Metric.cobounded_eq_cocompact]
  exact (hb.map ((↑) : ℂ → OnePoint ℂ)).sup_pure ∞

/-- DLMF 1.9.36: `∞ ± z = ∞`. -/
@[dlmf 1.9.E36]
theorem extAdd_infty (z : ℂ) : extAdd ∞ z = ∞ ∧ extAdd ∞ (-z) = ∞ := ⟨rfl, rfl⟩

/-- DLMF 1.9.37: `∞ · z = ∞` for `z ≠ 0`. -/
@[dlmf 1.9.E37]
theorem extMul_infty (z : ℂ) : extMul ∞ z = ∞ := rfl

/-- DLMF 1.9.38: `z/∞ = 0`. -/
@[dlmf 1.9.E38]
theorem extDiv_infty (z : ℂ) : extDiv z ∞ = ((0 : ℂ) : OnePoint ℂ) := rfl

/-- DLMF 1.9.39: `z/0 = ∞` (DLMF assumes `z ≠ 0`). -/
@[dlmf 1.9.E39]
theorem extDiv_zero (z : ℂ) : extDiv z ((0 : ℂ) : OnePoint ℂ) = ∞ := by
  simp [extDiv]

/-- DLMF §1.9(iv): the linear transformation `f(z) = az + b`, `a ≠ 0`, has `f'(z) = a` and maps
`ℂ` bijectively (and conformally, `f' ≠ 0`) onto `ℂ`. -/
@[dlmf 1.9.iv]
theorem linear_hasDerivAt_bijective {a : ℂ} (ha : a ≠ 0) (b z : ℂ) :
    HasDerivAt (fun w => a * w + b) a z ∧ Function.Bijective (fun w => a * w + b) := by
  refine ⟨by simpa using ((hasDerivAt_id z).const_mul a).add_const b, ?_, ?_⟩
  · intro w₁ w₂ h
    simpa [ha] using h
  · intro w
    exact ⟨(w - b) / a, by field_simp; ring⟩

/-- DLMF 1.9.41: `f(-d/c) = ∞` and `f(∞) = a/c` for the bilinear transformation with `c ≠ 0`. -/
@[dlmf 1.9.E41]
theorem mobiusExt_neg_div (a b : ℂ) {c : ℂ} (d : ℂ) (hc : c ≠ 0) :
    mobiusExt a b c d ((-d / c : ℂ) : OnePoint ℂ) = ∞ ∧
      mobiusExt a b c d ∞ = ((a / c : ℂ) : OnePoint ℂ) := by
  refine ⟨?_, by simp [mobiusExt, hc]⟩
  have : c * (-d / c) + d = 0 := by field_simp; ring
  simp [mobiusExt, this]

/-- DLMF 1.9.42: `f'(z) = (ad - bc)/(cz + d)²` for `z ≠ -d/c`. -/
@[dlmf 1.9.E42]
theorem hasDerivAt_mobius (a b c d : ℂ) {z : ℂ} (hz : c * z + d ≠ 0) :
    HasDerivAt (mobius a b c d) ((a * d - b * c) / (c * z + d) ^ 2) z := by
  have h1 : HasDerivAt (fun w => a * w + b) a z := by
    simpa using ((hasDerivAt_id z).const_mul a).add_const b
  have h2 : HasDerivAt (fun w => c * w + d) c z := by
    simpa using ((hasDerivAt_id z).const_mul c).add_const d
  have h := h1.div h2 hz
  rw [show (a * (c * z + d) - (a * z + b) * c) / (c * z + d) ^ 2 =
    (a * d - b * c) / (c * z + d) ^ 2 by ring] at h
  exact h

/-- Identity under the stated parameter and domain assumptions: `Function.update (fun z => mobius
a b c d z⁻¹) 0 (a / c) = fun z => (a + b * z) / (c + d * z)`. -/
private lemma g1c_mobius_inv_eq (a b c d : ℂ) :
    Function.update (fun z => mobius a b c d z⁻¹) 0 (a / c) =
      fun z => (a + b * z) / (c + d * z) := by
  funext z
  by_cases hz : z = 0
  · subst hz; simp
  · rw [Function.update_of_ne hz, mobius]
    by_cases h : c + d * z = 0
    · have h' : c * z⁻¹ + d = 0 := by
        rw [show c * z⁻¹ + d = (c + d * z) / z by field_simp, h, zero_div]
      rw [h, h', div_zero, div_zero]
    · rw [show a * z⁻¹ + b = (a + b * z) / z by field_simp,
        show c * z⁻¹ + d = (c + d * z) / z by field_simp]
      field_simp

/-- DLMF 1.9.43: `f'(∞) = (bc - ad)/c²` for the bilinear transformation with `c ≠ 0`, where
`f'(∞) = g'(0)` for `g(z) = f(1/z)`, `g(0) = f(∞) = a/c`. The transformation is analytic at
`∞`. -/
@[dlmf 1.9.E43]
theorem derivAtInfty_mobius (a b : ℂ) {c : ℂ} (d : ℂ) (hc : c ≠ 0) :
    AnalyticAtInfty (mobius a b c d) (a / c) ∧
      derivAtInfty (mobius a b c d) (a / c) = (b * c - a * d) / c ^ 2 := by
  have hh : HasDerivAt (fun z : ℂ => (a + b * z) / (c + d * z)) ((b * c - a * d) / c ^ 2) 0 := by
    have h1 : HasDerivAt (fun w : ℂ => a + b * w) b 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul b).const_add a
    have h2 : HasDerivAt (fun w : ℂ => c + d * w) d 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul d).const_add c
    convert h1.div h2 (by simpa using hc) using 1
    simp
  refine ⟨?_, ?_⟩
  · unfold AnalyticAtInfty
    rw [g1c_mobius_inv_eq]
    have : AnalyticAt ℂ (fun z : ℂ => a + b * z) 0 := by fun_prop
    have h2 : AnalyticAt ℂ (fun z : ℂ => c + d * z) 0 := by fun_prop
    exact this.div h2 (by simpa using hc)
  · unfold derivAtInfty
    rw [g1c_mobius_inv_eq]
    exact hh.deriv

/-- DLMF 1.9.44: the inverse of the bilinear transformation 1.9.40 is `z = (dw - b)/(-cw + a)`:
if `ad - bc ≠ 0` and `-cw + a ≠ 0`, then `f((dw - b)/(-cw + a)) = w`. -/
@[dlmf 1.9.E44]
theorem mobius_mobius_inv {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) {w : ℂ}
    (hw : -c * w + a ≠ 0) : mobius a b c d (mobius d (-b) (-c) a w) = w := by
  unfold mobius
  have e1 : a * ((d * w + -b) / (-c * w + a)) + b = (a * d - b * c) * w / (-c * w + a) := by
    rw [mul_div_assoc', div_add' _ _ _ hw]; congr 1; ring
  have e2 : c * ((d * w + -b) / (-c * w + a)) + d = (a * d - b * c) / (-c * w + a) := by
    rw [mul_div_assoc', div_add' _ _ _ hw]; congr 1; ring
  rw [e1, e2, div_div_div_cancel_right₀ hw, mul_div_cancel_left₀ w hdet]

/-- The inverse fractional-linear map cancels its forward map on the one-point compactification. -/
private lemma mobiusExt_leftInv {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) (hc : c ≠ 0) :
    Function.LeftInverse (mobiusExt d (-b) (-c) a) (mobiusExt a b c d) := by
  intro z
  induction z using OnePoint.rec with
  | infty =>
    have hh : -(c * (a / c)) + a = 0 := by field_simp; ring
    simp [mobiusExt, hc, hh]
  | coe z =>
    by_cases hz : c * z + d = 0
    · have hz' : d / (-c) = z := by
        apply (div_eq_iff (neg_ne_zero.mpr hc)).2
        linear_combination hz
      simp [mobiusExt, hz, hc, hz']
    · have hden : -c * mobius a b c d z + a ≠ 0 := by
        have he : -c * mobius a b c d z + a = (a * d - b * c) / (c * z + d) := by
          unfold mobius
          field_simp
          ring
        rw [he]
        exact div_ne_zero hdet hz
      simp only [mobiusExt, hz, ite_false, hden]
      have hd' : d * a - (-b) * (-c) ≠ 0 := by
        simpa only [neg_mul_neg, mul_comm] using hdet
      have hz' : -(-c) * z + d ≠ 0 := by simpa using hz
      have he := mobius_mobius_inv (a := d) (b := -b) (c := -c) (d := a) (w := z) hd' hz'
      simpa only [neg_neg] using congrArg (fun w : ℂ => (w : OnePoint ℂ)) he

/-- DLMF §1.9(iv): the bilinear transformation 1.9.40 (`ad - bc ≠ 0`, `c ≠ 0`) is a one-to-one
mapping of `ℂ ∪ {∞}` onto itself; its inverse is the transformation of 1.9.44. -/
@[dlmf 1.9.iv]
theorem mobiusExt_bijective {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) (hc : c ≠ 0) :
    Function.Bijective (mobiusExt a b c d) ∧
      Function.LeftInverse (mobiusExt d (-b) (-c) a) (mobiusExt a b c d) := by
  have hl := mobiusExt_leftInv hdet hc
  have hr := mobiusExt_leftInv (a := d) (b := -b) (c := -c) (d := a)
    (by simpa only [neg_mul_neg, mul_comm] using hdet)
    (neg_ne_zero.mpr hc)
  refine ⟨⟨hl.injective, ?_⟩, hl⟩
  intro z
  refine ⟨mobiusExt d (-b) (-c) a z, ?_⟩
  simpa only [neg_neg] using hr z

/-- DLMF 1.9.45: the cross ratio is invariant under bilinear transformations (for four finite
points with finite images, `ad - bc ≠ 0`). -/
@[dlmf 1.9.E45]
theorem crossRatio_mobius {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) {z₁ z₂ z₃ z₄ : ℂ}
    (h₁ : c * z₁ + d ≠ 0) (h₂ : c * z₂ + d ≠ 0) (h₃ : c * z₃ + d ≠ 0) (h₄ : c * z₄ + d ≠ 0) :
    crossRatio (mobius a b c d z₁) (mobius a b c d z₂) (mobius a b c d z₃)
      (mobius a b c d z₄) = crossRatio z₁ z₂ z₃ z₄ := by
  have key : ∀ {u v : ℂ}, c * u + d ≠ 0 → c * v + d ≠ 0 →
      mobius a b c d u - mobius a b c d v = (a * d - b * c) * (u - v) /
        ((c * u + d) * (c * v + d)) := by
    intro u v hu hv
    unfold mobius
    rw [div_sub_div _ _ hu hv]
    congr 1
    ring
  unfold crossRatio
  rw [key h₁ h₂, key h₃ h₄, key h₁ h₄, key h₃ h₂]
  by_cases h14 : z₁ - z₄ = 0
  · simp [h14]
  by_cases h32 : z₃ - z₂ = 0
  · simp [h32]
  field_simp

/-! ## §1.9(vi) Power series -/

/-- DLMF 1.9.51–1.9.52 (product of power series), corrected form: if `∑ aₙ zⁿ` and `∑ bₙ zⁿ`
converge and the Cauchy product `∑ cₙ zⁿ`, `cₙ = ∑_{k=0}^{n} a_k b_{n-k}`, also converges, then
`(∑ aₙ zⁿ)(∑ bₙ zⁿ) = ∑ cₙ zⁿ` (Abel's theorem). DLMF omits the hypothesis on `∑ cₙ zⁿ`, which is
needed: for `aₙ = bₙ = (-1)ⁿ/√(n+1)` and `z = 1` both series converge but the Cauchy product
diverges. For `|z|` less than both radii of convergence the product series converges
absolutely (Mathlib: `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`). -/
@[dlmf 1.9.E51, dlmf 1.9.E52]
theorem tendsto_cauchyProduct {a b : ℕ → ℂ} {z A B C : ℂ}
    (ha : Tendsto (fun N => ∑ n ∈ Finset.range N, a n * z ^ n) atTop (𝓝 A))
    (hb : Tendsto (fun N => ∑ n ∈ Finset.range N, b n * z ^ n) atTop (𝓝 B))
    (hc : Tendsto (fun N => ∑ n ∈ Finset.range N,
      (∑ k ∈ Finset.range (n + 1), a k * b (n - k)) * z ^ n) atTop (𝓝 C)) :
    C = A * B := by
  have hA := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt ha
  have hB := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hb
  have hC := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hc
  have heq : ∀ᶠ w : ℂ in ((𝓝[<] (1 : ℝ)).map Complex.ofReal),
      (∑' n, ((∑ k ∈ Finset.range (n + 1), a k * b (n - k)) * z ^ n) * w ^ n) =
        (∑' n, (a n * z ^ n) * w ^ n) * ∑' n, (b n * z ^ n) * w ^ n := by
    rw [Filter.eventually_map]
    filter_upwards [eventually_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with x hx hx0
    have hxnorm : ‖(x : ℂ)‖ < 1 := by
      simpa [Real.norm_of_nonneg (show 0 ≤ x from le_of_lt hx0)] using hx
    rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
      (summable_powerSeries_of_norm_lt_one ha.cauchySeq hxnorm).norm
      (summable_powerSeries_of_norm_lt_one hb.cauchySeq hxnorm).norm]
    apply tsum_congr
    intro n
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [show z ^ n = z ^ k * z ^ (n - k) by rw [← pow_add, Nat.add_sub_of_le hkn],
      show (x : ℂ) ^ n = (x : ℂ) ^ k * (x : ℂ) ^ (n - k) by
        rw [← pow_add, Nat.add_sub_of_le hkn]]
    ring
  exact tendsto_nhds_unique hC ((hA.mul hB).congr' (heq.mono fun _ h => h.symm))

/-- The coefficient convolution with a nonzero constant term uniquely determines its inverse. -/
private lemma eq_recipCoeff_of_convolution {a b : ℕ → ℂ} (ha : a 0 ≠ 0)
    (hab : ∀ n, ∑ k ∈ Finset.range (n + 1), a k * b (n - k) = if n = 0 then 1 else 0) :
    b = recipCoeff a := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have h := hab n
    by_cases hn : n = 0
    · subst n
      simp at h
      rw [recipCoeff, dite_eq_left rfl]
      exact (eq_div_iff ha).mpr (by simpa [mul_comm] using h)
    · rw [recipCoeff, dite_eq_right hn]
      rw [Finset.sum_range_succ'] at h
      simp only [Nat.sub_zero, ite_eq_right hn] at h
      have he : (∑ k ∈ Finset.range n, a (k + 1) * b (n - (k + 1))) =
          ∑ k : Fin n, a (k + 1) * recipCoeff a (n - 1 - k) := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro k hk
        rw [show n - (k.val + 1) = n - 1 - k.val by omega, ih _ (by omega)]
      rw [he] at h
      apply (eq_div_iff ha).mpr
      linear_combination h

/-- DLMF 1.9.53–1.9.54: if `f(z) = ∑ aₙ zⁿ` near `0` with `a₀ ≠ 0`, then
`1/f(z) = ∑ bₙ zⁿ` for all sufficiently small `|z|`, with `bₙ = recipCoeff a n` (1.9.55–1.9.56). -/
@[dlmf 1.9.E53, dlmf 1.9.E54]
theorem hasSum_recipCoeff {a : ℕ → ℂ} {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ∀ z ∈ ball (0 : ℂ) r, HasSum (fun n => a n * z ^ n) (f z)) (ha : a 0 ≠ 0) :
    ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n => recipCoeff a n * z ^ n) (1 / f z) := by
  have hp := Complex.hasFPowerSeriesOnBall_of_hasSum_ball (a := a) (f := f) (ρ := ⟨r / 2, by positivity⟩) (by exact_mod_cast half_pos hr) (half_lt_self hr)
    (fun z hz => hf z (by simpa using hz))
  have hfa : AnalyticAt ℂ f 0 := hp.hasFPowerSeriesAt.analyticAt
  have hf0 : f 0 = a 0 := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq] using
      (hp.coeff_zero (fun _ => 0)).symm
  have hne : f 0 ≠ 0 := by rwa [hf0]
  have hga : AnalyticAt ℂ (fun z => 1 / f z) 0 := by
    simpa only [one_div] using hfa.fun_inv hne
  let b : ℕ → ℂ := fun n => iteratedDeriv n (fun z => 1 / f z) 0 / n.factorial
  have hb : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n => b n * z ^ n) (1 / f z) := by
    simpa [b, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
      hga.hasFPowerSeriesAt.eventually_hasSum
  have hlocal : ∀ᶠ z in 𝓝 (0 : ℂ),
      HasSum (fun n => a n * z ^ n) (f z) ∧
        HasSum (fun n => b n * z ^ n) (1 / f z) ∧ f z ≠ 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr, hb, hfa.continuousAt.eventually_ne hne]
      with z hz hzb hzn
    exact ⟨hf z hz, hzb, hzn⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff.mp hlocal
  have hcoef : (fun n => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)) =
      fun n => if n = 0 then (1 : ℂ) else 0 := by
    apply Complex.trigR4_coeff_unique_ball hδ (g := fun _ => 1)
    · intro z hz
      obtain ⟨hza, hzb, hzn⟩ := hδsub (by simpa [dist_eq_norm] using hz)
      simpa [hzn] using Complex.hasSum_mul_powerSeries hza hzb
    · intro z hz
      convert hasSum_ite_eq 0 (1 : ℂ) using 1
      ext n
      by_cases hn : n = 0 <;> simp [hn]
  have heq : b = recipCoeff a := eq_recipCoeff_of_convolution ha (fun n => congrFun hcoef n)
  simpa [← heq] using hb

/-- DLMF 1.9.55: `b₀ = 1/a₀`, `b₁ = -a₁/a₀²`, `b₂ = (a₁² - a₀a₂)/a₀³`. -/
@[dlmf 1.9.E55]
theorem recipCoeff_zero_one_two (a : ℕ → ℂ) (ha : a 0 ≠ 0) :
    recipCoeff a 0 = 1 / a 0 ∧ recipCoeff a 1 = -a 1 / a 0 ^ 2 ∧
      recipCoeff a 2 = (a 1 ^ 2 - a 0 * a 2) / a 0 ^ 3 := by
  have h0 : recipCoeff a 0 = 1 / a 0 := by rw [recipCoeff]; simp
  have h1 : recipCoeff a 1 = -a 1 / a 0 ^ 2 := by
    rw [recipCoeff]; simp [h0]; field_simp
  refine ⟨h0, h1, ?_⟩
  rw [recipCoeff]
  simp [Fin.sum_univ_two, h0, h1]
  field_simp
  ring

/-- The logarithmic coefficient recurrence is uniquely determined by the identity `f * g′ = f′`. -/
private lemma eq_logCoeff_of_convolution {a b : ℕ → ℂ} (ha : a 0 = 1) (hb : b 0 = 0)
    (hab : ∀ n, ∑ k ∈ Finset.range (n + 1),
      a k * ((n - k + 1 : ℕ) : ℂ) * b (n - k + 1) = (n + 1 : ℂ) * a (n + 1)) :
    b = logCoeff a := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa [logCoeff] using hb
    · have hn' : n - 1 + 1 = n := by omega
      have h := hab (n - 1)
      rw [Finset.sum_range_succ', show ((n - 1 : ℕ) : ℂ) + 1 = n by exact_mod_cast hn'] at h
      simp only [Nat.sub_zero, hn', ha, one_mul] at h
      have he : (∑ k ∈ Finset.range (n - 1),
          a (k + 1) * ((n - 1 - (k + 1) + 1 : ℕ) : ℂ) * b (n - 1 - (k + 1) + 1)) =
          ∑ k : Fin (n - 1), ((n : ℂ) - (k + 1)) * a (k + 1) * logCoeff a (n - 1 - k) := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : n - 1 - (k.val + 1) + 1 = n - 1 - k.val := by omega
        have hk'' : ((n - 1 - k.val : ℕ) : ℂ) = (n : ℂ) - (k.val + 1) := by
          rw [show n - 1 - k.val = n - (k.val + 1) by omega,
            Nat.cast_sub (by omega : k.val + 1 ≤ n)]
          push_cast
          ring
        rw [hk', ih _ (by omega), hk'']
        ring
      rw [he] at h
      rw [logCoeff, dite_eq_right hn]
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      apply (eq_div_iff hn0).mpr
      linear_combination h

/-- DLMF 1.9.57: if `f(z) = 1 + a₁z + a₂z² + ⋯` near `0`, then the principal logarithm satisfies
`ln f(z) = ∑_{n ≥ 1} qₙ zⁿ` for all sufficiently small `|z|`, with `qₙ = logCoeff a n`
(1.9.58–1.9.59). -/
@[dlmf 1.9.E57]
theorem hasSum_logCoeff {a : ℕ → ℂ} {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ∀ z ∈ ball (0 : ℂ) r, HasSum (fun n => a n * z ^ n) (f z)) (ha : a 0 = 1) :
    ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n => logCoeff a n * z ^ n) (log (f z)) := by
  have hp := Complex.hasFPowerSeriesOnBall_of_hasSum_ball (a := a) (f := f)
    (ρ := ⟨r / 2, by positivity⟩) (by exact_mod_cast half_pos hr) (half_lt_self hr)
    (fun z hz => hf z (by simpa using hz))
  have hfa := hp.hasFPowerSeriesAt.analyticAt
  have hf0 : f 0 = 1 := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, ha] using
      (hp.coeff_zero (fun _ => 0)).symm
  have hslit0 : f 0 ∈ Complex.slitPlane := by rw [hf0]; exact one_mem_slitPlane
  let g : ℂ → ℂ := fun z => log (f z)
  have hga : AnalyticAt ℂ g 0 := hfa.clog hslit0
  let b : ℕ → ℂ := fun n : ℕ => iteratedDeriv n g 0 / n.factorial
  have hbp : HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℂ b) 0 :=
    hga.hasFPowerSeriesAt
  have hb : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n : ℕ => b n * z ^ n) (g z) := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
      hbp.eventually_hasSum
  have hlocal : ∀ᶠ z in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => a n * z ^ n) (f z) ∧
      HasSum (fun n : ℕ => (n + 1 : ℂ) * b (n + 1) * z ^ n) (deriv g z) ∧
      HasSum (fun n : ℕ => (n + 1 : ℂ) * a (n + 1) * z ^ n) (deriv f z) ∧
      f z * deriv g z = deriv f z := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr,
      Complex.eventually_hasSum_deriv_powerSeries hbp, Complex.eventually_hasSum_deriv_powerSeries hp.hasFPowerSeriesAt,
      hfa.eventually_analyticAt, hfa.continuousAt.eventually_mem (isOpen_slitPlane.mem_nhds hslit0)]
      with z hz hzg hzf hzfa hzslit
    refine ⟨hf z hz, hzg, hzf, ?_⟩
    have hd := hzfa.differentiableAt.hasDerivAt.clog hzslit
    rw [show deriv g z = deriv f z / f z from hd.deriv]
    field_simp [Complex.slitPlane_ne_zero hzslit]
  obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff.mp hlocal
  have hcoef : (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
      a k * (((n - k + 1 : ℕ) : ℂ) * b (n - k + 1))) =
      fun n : ℕ => (n + 1 : ℂ) * a (n + 1) := by
    apply Complex.trigR4_coeff_unique_ball hδ (g := deriv f)
    · intro z hz
      obtain ⟨hza, hzg, hzf, hzeq⟩ := hδsub (by simpa [dist_eq_norm] using hz)
      simpa only [hzeq, Nat.cast_add, Nat.cast_one] using Complex.hasSum_mul_powerSeries hza hzg
    · intro z hz
      exact (hδsub (by simpa [dist_eq_norm] using hz)).2.2.1
  have hb0 : b 0 = 0 := by simp [b, g, hf0]
  have heq : b = logCoeff a := by
    apply eq_logCoeff_of_convolution ha hb0
    intro n
    simpa [mul_assoc] using congrFun hcoef n
  simpa [← heq, g] using hb

/-- DLMF 1.9.58: `q₁ = a₁`, `q₂ = (2a₂ - a₁²)/2`, `q₃ = (3a₃ - 3a₁a₂ + a₁³)/3`. -/
@[dlmf 1.9.E58]
theorem logCoeff_one_two_three (a : ℕ → ℂ) :
    logCoeff a 1 = a 1 ∧ logCoeff a 2 = (2 * a 2 - a 1 ^ 2) / 2 ∧
      logCoeff a 3 = (3 * a 3 - 3 * a 1 * a 2 + a 1 ^ 3) / 3 := by
  have h1 : logCoeff a 1 = a 1 := by rw [logCoeff]; simp
  have h2 : logCoeff a 2 = (2 * a 2 - a 1 ^ 2) / 2 := by
    rw [logCoeff]; simp [h1]; ring
  refine ⟨h1, h2, ?_⟩
  rw [logCoeff]
  simp [Fin.sum_univ_two, h1, h2]
  ring

/-- The power coefficient recurrence is uniquely determined by `f * g′ = ν * f′ * g`. -/
private lemma eq_powCoeff_of_convolution {a b : ℕ → ℂ} (ν : ℂ) (ha : a 0 = 1) (hb : b 0 = 1)
    (hab : ∀ n, (∑ k ∈ Finset.range (n + 1),
      a k * ((n - k + 1 : ℕ) : ℂ) * b (n - k + 1)) =
        ν * ∑ k ∈ Finset.range (n + 1), (k + 1 : ℂ) * a (k + 1) * b (n - k)) :
    b = powCoeff ν a := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa [powCoeff] using hb
    · have hn' : n - 1 + 1 = n := by omega
      have h := hab (n - 1)
      rw [Finset.sum_range_succ'] at h
      simp only [Nat.sub_zero, hn', ha, one_mul] at h
      have hrest : (∑ k ∈ Finset.range (n - 1),
          a (k + 1) * ((n - 1 - (k + 1) + 1 : ℕ) : ℂ) * b (n - 1 - (k + 1) + 1)) =
          ∑ k ∈ Finset.range n, ((n : ℂ) - (k + 1)) * a (k + 1) * b (n - 1 - k) := by
        conv_rhs => rw [← hn', Finset.sum_range_succ]
        have hz : (n : ℂ) - (((n - 1 : ℕ) : ℂ) + 1) = 0 := by
          rw [show ((n - 1 : ℕ) : ℂ) + 1 = n by exact_mod_cast hn']
          ring
        simp only [hn', hz, zero_mul, add_zero]
        apply Finset.sum_congr rfl
        intro k hk
        have hk0 := Finset.mem_range.mp hk
        have hk' : n - 1 - (k + 1) + 1 = n - 1 - k := by omega
        have hk'' : ((n - 1 - k : ℕ) : ℂ) = (n : ℂ) - (k + 1) := by
          rw [show n - 1 - k = n - (k + 1) by omega, Nat.cast_sub (by omega : k + 1 ≤ n)]
          push_cast
          ring
        rw [hk', hk'']
        ring
      rw [hrest] at h
      have he : (∑ k : Fin n, ((ν + 1) * (k + 1) - n) * a (k + 1) *
          powCoeff ν a (n - 1 - k)) =
          ν * (∑ k ∈ Finset.range n, (k + 1 : ℂ) * a (k + 1) * b (n - 1 - k)) -
            ∑ k ∈ Finset.range n, ((n : ℂ) - (k + 1)) * a (k + 1) * b (n - 1 - k) := by
        change (∑ k : Fin n, (fun k : ℕ => ((ν + 1) * (k + 1) - n) * a (k + 1) *
          powCoeff ν a (n - 1 - k)) k.val) = _
        rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => ((ν + 1) * (k + 1) - n) * a (k + 1) *
          powCoeff ν a (n - 1 - k)) n, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        rw [← ih _ (by have := Finset.mem_range.mp hk; omega)]
        ring
      rw [powCoeff, dite_eq_right hn, he]
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      apply (eq_div_iff hn0).mpr
      linear_combination h

/-- DLMF 1.9.60: if `f(z) = 1 + a₁z + a₂z² + ⋯` near `0` and `ν ∈ ℂ`, then the principal power
satisfies `(f(z))^ν = ∑ pₙ zⁿ` for all sufficiently small `|z|`, with `pₙ = powCoeff ν a n`
(1.9.61–1.9.62). -/
@[dlmf 1.9.E60]
theorem hasSum_powCoeff {a : ℕ → ℂ} {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ∀ z ∈ ball (0 : ℂ) r, HasSum (fun n => a n * z ^ n) (f z)) (ha : a 0 = 1) (ν : ℂ) :
    ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n => powCoeff ν a n * z ^ n) (f z ^ ν) := by
  have hp := Complex.hasFPowerSeriesOnBall_of_hasSum_ball (a := a) (f := f)
    (ρ := ⟨r / 2, by positivity⟩) (by exact_mod_cast half_pos hr) (half_lt_self hr)
    (fun z hz => hf z (by simpa using hz))
  have hfa := hp.hasFPowerSeriesAt.analyticAt
  have hf0 : f 0 = 1 := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, ha] using
      (hp.coeff_zero (fun _ => 0)).symm
  have hslit0 : f 0 ∈ Complex.slitPlane := by rw [hf0]; exact one_mem_slitPlane
  let g : ℂ → ℂ := fun z => f z ^ ν
  have hga : AnalyticAt ℂ g 0 := hfa.cpow analyticAt_const hslit0
  let b : ℕ → ℂ := fun n => iteratedDeriv n g 0 / n.factorial
  have hbp : HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℂ b) 0 := hga.hasFPowerSeriesAt
  have hb : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n => b n * z ^ n) (g z) := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
      hbp.eventually_hasSum
  have hlocal : ∀ᶠ z in 𝓝 (0 : ℂ),
      HasSum (fun n => a n * z ^ n) (f z) ∧
      HasSum (fun n : ℕ => (n + 1 : ℂ) * b (n + 1) * z ^ n) (deriv g z) ∧
      HasSum (fun n : ℕ => (n + 1 : ℂ) * a (n + 1) * z ^ n) (deriv f z) ∧
      HasSum (fun n => b n * z ^ n) (g z) ∧
      f z * deriv g z = ν * (deriv f z * g z) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr, hb,
      Complex.eventually_hasSum_deriv_powerSeries hbp, Complex.eventually_hasSum_deriv_powerSeries hp.hasFPowerSeriesAt,
      hfa.eventually_analyticAt, hfa.continuousAt.eventually_mem (isOpen_slitPlane.mem_nhds hslit0)]
      with z hz hzb hzg hzf hzfa hzslit
    refine ⟨hf z hz, hzg, hzf, hzb, ?_⟩
    exact Complex.mul_deriv_cpow_const hzfa.differentiableAt hzslit ν
  obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff.mp hlocal
  have hcoef : (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
      a k * (((n - k + 1 : ℕ) : ℂ) * b (n - k + 1))) =
      fun n => ν * ∑ k ∈ Finset.range (n + 1), (k + 1 : ℂ) * a (k + 1) * b (n - k) := by
    apply Complex.trigR4_coeff_unique_ball hδ (g := fun z => f z * deriv g z)
    · intro z hz
      obtain ⟨hza, hzg, hzf, hzb, hzeq⟩ := hδsub (by simpa [dist_eq_norm] using hz)
      simpa only [Nat.cast_add, Nat.cast_one] using Complex.hasSum_mul_powerSeries hza hzg
    · intro z hz
      obtain ⟨hza, hzg, hzf, hzb, hzeq⟩ := hδsub (by simpa [dist_eq_norm] using hz)
      have h := (Complex.hasSum_mul_powerSeries hzf hzb).mul_left ν
      simpa only [← hzeq, mul_assoc] using h
  have hb0 : b 0 = 1 := by simp [b, g, hf0]
  have heq : b = powCoeff ν a := by
    apply eq_powCoeff_of_convolution ν ha hb0
    intro n
    simpa [mul_assoc] using congrFun hcoef n
  simpa [← heq, g] using hb

/-- DLMF 1.9.61: `p₀ = 1`, `p₁ = νa₁`, `p₂ = ν((ν - 1)a₁² + 2a₂)/2`. -/
@[dlmf 1.9.E61]
theorem powCoeff_zero_one_two (ν : ℂ) (a : ℕ → ℂ) :
    powCoeff ν a 0 = 1 ∧ powCoeff ν a 1 = ν * a 1 ∧
      powCoeff ν a 2 = ν * ((ν - 1) * a 1 ^ 2 + 2 * a 2) / 2 := by
  have h0 : powCoeff ν a 0 = 1 := by rw [powCoeff]; simp
  have h1 : powCoeff ν a 1 = ν * a 1 := by rw [powCoeff]; simp [h0]
  refine ⟨h0, h1, ?_⟩
  rw [powCoeff]
  simp [Fin.sum_univ_two, h0, h1]
  ring

/-- DLMF 1.9.63: a power series `f(z) = ∑ aₙ (z - z₀)ⁿ` with radius of convergence `R` can be
differentiated any number of times within its circle of convergence:
`f⁽ᵐ⁾(z) = ∑ (n + 1)_m a_{n+m} (z - z₀)ⁿ`, `|z - z₀| < R`. -/
@[dlmf 1.9.E63]
theorem hasSum_iteratedDeriv_powerSeries {a : ℕ → ℂ} {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hf : ∀ z ∈ ball z₀ R, HasSum (fun n => a n * (z - z₀) ^ n) (f z)) (m : ℕ) {z : ℂ}
    (hz : z ∈ ball z₀ R) :
    HasSum (fun n : ℕ => (ascPochhammer ℂ m).eval ((n : ℂ) + 1) * a (n + m) * (z - z₀) ^ n)
      (iteratedDeriv m f z) := by
  have hzR : ‖z - z₀‖ < R := by simpa [dist_eq_norm] using hz
  obtain ⟨ρ, hzρ, hρR⟩ := exists_between hzR
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hzρ
  let g : ℂ → ℂ := fun w => f (w + z₀)
  have hg (w : ℂ) (hw : ‖w‖ < R) : HasSum (fun n => a n * w ^ n) (g w) := by
    simpa [g] using hf (w + z₀) (by simpa [dist_eq_norm] using hw)
  let r : NNReal := ⟨ρ, hρ.le⟩
  have hp := Complex.hasFPowerSeriesOnBall_of_hasSum_ball
    (ρ := r) (by exact_mod_cast hρ) hρR hg
  have heball : Metric.eball (0 : ℂ) (r : ENNReal) = ball (0 : ℂ) ρ := Metric.eball_coe
  have hd : DifferentiableOn ℂ g (ball 0 ρ) := by
    simpa only [heball] using hp.differentiableOn
  have hcoef : a = fun n => iteratedDeriv n g 0 / n.factorial := by
    apply Complex.trigR4_coeff_unique_ball hρ
      (fun w hw => hg w (lt_trans hw hρR))
    intro w hw
    convert Complex.hasSum_taylorSeries_on_ball hd (z := w) (by simpa using hw) using 1
    funext n
    simp only [sub_zero, smul_eq_mul]
    ring
  have hdm : ∀ k, DifferentiableOn ℂ (iteratedDeriv k g) (ball 0 ρ) := by
    intro k
    induction k with
    | zero => simpa using hd
    | succ k ih => simpa [iteratedDeriv_succ] using ih.deriv isOpen_ball
  have hs := Complex.hasSum_taylorSeries_on_ball (hdm m) (z := z - z₀) (by simpa using hzρ)
  have he : ∀ n, iteratedDeriv n (iteratedDeriv m g) 0 = iteratedDeriv (n + m) g 0 := by
    intro n
    simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]
  have hc (n : ℕ) :
      (ascPochhammer ℂ m).eval ((n : ℂ) + 1) * a (n + m) =
        iteratedDeriv n (iteratedDeriv m g) 0 / n.factorial := by
    rw [hcoef, he]
    have hh := factorial_mul_ascPochhammer ℂ n m
    have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hnm : ((n + m).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n + m)
    field_simp
    linear_combination (iteratedDeriv (n + m) g 0) * hh
  convert hs using 1
  · funext n
    rw [hc]
    simp only [sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring
  · simp [g, iteratedDeriv_comp_add_const]

/-! ## §1.9(vii) Inversion of limits -/

/-- DLMF §1.9(vii) (double sequences, 1.9.64–1.9.65): if the double sequence `z_{m,n}` converges
to `z` and the repeated limits exist, then both repeated limits equal `z`. -/
@[dlmf 1.9.E64, dlmf 1.9.E65]
theorem tendsto_iterated_of_tendsto_prod {z : ℕ → ℕ → ℂ} {L : ℂ} {g h : ℕ → ℂ}
    (hz : Tendsto (fun p : ℕ × ℕ => z p.1 p.2) atTop (𝓝 L))
    (hg : ∀ m, Tendsto (z m) atTop (𝓝 (g m))) (hh : ∀ n, Tendsto (fun m => z m n) atTop (𝓝 (h n))) :
    Tendsto g atTop (𝓝 L) ∧ Tendsto h atTop (𝓝 L) := by
  constructor
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_nhds.mp hz (ε / 2) (half_pos hε)).exists_forall_of_atTop
    refine ⟨N.1, fun m hm => ?_⟩
    have hle : dist (g m) L ≤ ε / 2 :=
      le_of_tendsto ((hg m).dist tendsto_const_nhds)
        (eventually_atTop.mpr ⟨N.2, fun n hn => (hN (m, n) ⟨hm, hn⟩).le⟩)
    linarith
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_nhds.mp hz (ε / 2) (half_pos hε)).exists_forall_of_atTop
    refine ⟨N.2, fun n hn => ?_⟩
    have hle : dist (h n) L ≤ ε / 2 :=
      le_of_tendsto ((hh n).dist tendsto_const_nhds)
        (eventually_atTop.mpr ⟨N.1, fun m hm => (hN (m, n) ⟨hm, hn⟩).le⟩)
    linarith

/-- DLMF 1.9.68 (term-by-term integration): if the `fₙ` are continuous and `∑ fₙ` converges
uniformly on every compact subset of a domain `D`, then `∫_C ∑ fₙ(z) dz = ∑ ∫_C fₙ(z) dz` for
every contour `C` in `D`, the right-hand side converging as partial sums. -/
@[dlmf 1.9.E68]
theorem tendsto_contourIntegral_tsum {D : Set ℂ} {f : ℕ → ℂ → ℂ}
    (hf : ∀ n, ContinuousOn (f n) D) {F : ℂ → ℂ}
    (hu : ∀ K ⊆ D, IsCompact K →
      TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N, f n z) F atTop K)
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : TauCeti.Contour.IsPiecewiseC1On γ a b)
    (hγD : ∀ t ∈ uIcc a b, γ t ∈ D) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, contourIntegral γ a b (f n)) atTop
      (𝓝 (contourIntegral γ a b F)) := by
  let K := γ '' uIcc a b
  have hKD : K ⊆ D := Set.image_subset_iff.mpr hγD
  have hK : IsCompact K := isCompact_uIcc.image_of_continuousOn hγ.continuousOn
  let S : ℕ → ℂ → ℂ := fun N z => ∑ n ∈ Finset.range N, f n z
  have hS (N : ℕ) : ContinuousOn (S N) K :=
    continuousOn_finsetSum _ fun n _ => (hf n).mono hKD
  have hU : TendstoUniformlyOn S F atTop K := hu K hKD hK
  have hF : ContinuousOn F K := hU.continuousOn (Eventually.of_forall hS).frequently
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
  have hB : ∀ᶠ N in atTop, ∀ z ∈ K, ‖S N z‖ ≤ C + 1 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hU 1 zero_lt_one] with N hN z hz
    calc ‖S N z‖ ≤ ‖F z‖ + ‖F z - S N z‖ := norm_le_norm_add_norm_sub _ _
      _ ≤ C + 1 := add_le_add (hC z hz) (by simpa only [dist_eq_norm] using (hN z hz).le)
  have hI := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (F := fun (N : ℕ) (t : ℝ) => deriv γ t * S N (γ t))
      (f := fun t => deriv γ t * F (γ t)) (μ := volume)
      (fun t => ‖deriv γ t‖ * (C + 1))
      (Eventually.of_forall fun N => by
        simpa only [smul_eq_mul] using
          (hγ.intervalIntegrable_deriv_smul_comp (hS N)).aestronglyMeasurable_restrict_uIoc)
      (hB.mono fun N hN => Eventually.of_forall fun t ht => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hN (γ t) ⟨t, uIoc_subset_uIcc ht, rfl⟩)
          (norm_nonneg _))
      (hγ.intervalIntegrable_deriv.norm.mul_const (C + 1))
      (Eventually.of_forall fun t ht =>
        tendsto_const_nhds.mul (hU.tendsto_at ⟨t, uIoc_subset_uIcc ht, rfl⟩))
  have hsum (N : ℕ) : (∫ t in a..b, deriv γ t * S N (γ t)) =
      ∑ n ∈ Finset.range N, contourIntegral γ a b (f n) := by
    simp only [S, Finset.mul_sum, contourIntegral, smul_eq_mul]
    exact intervalIntegral.integral_finsetSum fun n _ =>
      hγ.intervalIntegrable_deriv_smul_comp ((hf n).mono hKD)
  simpa only [hsum, contourIntegral, smul_eq_mul] using hI

end DLMF.AlgebraicAnalytic
