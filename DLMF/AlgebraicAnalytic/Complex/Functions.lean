/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.AlgebraicAnalytic.Complex.Defs
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Analysis.Contour.Residue.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functions of a complex variable (DLMF §1.10)

Statements of DLMF §1.10 that are not, in the stated generality, in Mathlib or Tau Ceti; the
upstream items (Taylor's theorem, the identity theorem, the maximum-modulus principle, Schwarz's
lemma on discs, removable singularities, Rouché's theorem on discs, …) are recorded as
`dlmf_upstream` pointers in `DLMF.AlgebraicAnalytic.Complex.MathlibCoverage`.

Conventions.
* Contours, interiors and the positive sense are those of `DLMF.AlgebraicAnalytic.Complex.Defs`
  (simple closed piecewise `C¹` contours, Tau Ceti's filled hull and winding number).
* The residue is `residueAt f z₀`, the Laurent coefficient `a_{-1}` defined by a circle integral,
  so that it is meaningful also at essential singularities; at poles it is Tau Ceti's
  `TauCeti.Contour.residue` (`residueAt_eq_residue`).
* Products indexed by `n ≥ 1` in DLMF are indexed by `ℕ` here where the index is a dummy
  (Weierstrass products, Mittag-Leffler series); DLMF's convergence of infinite products is
  `ProdConvergesDLMF`.
* Logarithms and powers are principal (`Complex.log`, `cpow`).

Proved here: the exponential series 1.10.2 (from Mathlib), Schwarz's inequalities 1.10.11 (from
Mathlib's Schwarz lemma), the analyticity of a locally uniform limit of products 1.10.23 (from
Mathlib), the analyticity of the branches of `√z` and `(1 - z)^α (1 + z)^β` in the cut planes of
§1.10(vi). The logarithmic-derivative limit 1.10.24 uses Mathlib’s
`TendstoLocallyUniformlyOn.deriv` and `logDeriv_fun_prod`. The improper-integral
holomorphy statements and the integral M-test use the project’s dominated-holomorphy theorem,
Mathlib’s locally uniform limit theorem and `MeasureTheory.tendsto_integral_Ioi_zero`.
-/

@[expose] public noncomputable section

open Complex Filter Set Metric MeasureTheory
open scoped Topology

namespace DLMF.AlgebraicAnalytic

/-! ## §1.10(i) Taylor's theorem -/

/-- DLMF 1.10.2: `e^z = 1 + z/1! + z²/2! + ⋯`, `|z| < ∞`. From Mathlib's
`NormedSpace.expSeries_div_hasSum_exp`. -/
@[dlmf 1.10.E2]
theorem hasSum_exp_series (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / n.factorial) (exp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

/-! ## §1.10(iii) Laurent series -/

/-- DLMF 1.10.6–1.10.7 (Laurent's theorem): if `f` is analytic in the annulus
`r₁ < |z - z₀| < r₂` (`0 ≤ r₁ < r₂ ≤ ∞`; here `r₂` finite or the statement is applied for every
finite `r₂`) and `r₁ < r < r₂`, then `f(z) = ∑_{n ∈ ℤ} aₙ (z - z₀)ⁿ` in the annulus, with
`aₙ = laurentCoeff f z₀ r n`; the series converges absolutely (and uniformly on compact
subsets). -/
@[dlmf 1.10.E6]
theorem hasSum_laurentSeries {f : ℂ → ℂ} {z₀ : ℂ} {r₁ r₂ r : ℝ} (hr₁ : 0 ≤ r₁)
    (hf : DifferentiableOn ℂ f {z | r₁ < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂}) (hr : r ∈ Ioo r₁ r₂)
    {z : ℂ} (hz : r₁ < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂) :
    HasSum (fun n : ℤ => laurentCoeff f z₀ r n * (z - z₀) ^ n) (f z) := by
  sorry

/-- DLMF §1.10(iii) (removable singularities): if `f` is analytic in the punctured disc
`0 < |z - z₀| < r₂`, then `z₀` is removable (`f` agrees near `z₀`, off `z₀`, with a function
analytic at `z₀`) iff all Laurent coefficients `aₙ`, `n < 0`, vanish; the Laurent series is
then the Taylor series. -/
@[dlmf 1.10.iii]
theorem removable_iff_laurentCoeff_neg_eq_zero {f : ℂ → ℂ} {z₀ : ℂ} {r₂ r : ℝ}
    (hf : DifferentiableOn ℂ f {z | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂}) (hr : r ∈ Ioo 0 r₂) :
    (∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g) ↔
      ∀ n : ℤ, n < 0 → laurentCoeff f z₀ r n = 0 := by
  sorry

/-- DLMF §1.10(iii) (poles): for `f` analytic in a punctured disc, `z₀` is a pole of order
`m ≥ 1` (`f` is meromorphic at `z₀` of order `-m`) iff `a_{-m} ≠ 0` and `aₙ = 0` for `n < -m`.
An isolated singularity with infinitely many nonzero `aₙ`, `n < 0`, is essential. -/
@[dlmf 1.10.iii]
theorem meromorphicOrderAt_eq_neg_iff_laurentCoeff {f : ℂ → ℂ} {z₀ : ℂ} {r₂ r : ℝ}
    (hf : DifferentiableOn ℂ f {z | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂}) (hr : r ∈ Ioo 0 r₂)
    {m : ℕ} (hm : 1 ≤ m) :
    (MeromorphicAt f z₀ ∧ meromorphicOrderAt f z₀ = (-(m : ℤ) : ℤ)) ↔
      laurentCoeff f z₀ r (-(m : ℤ)) ≠ 0 ∧ ∀ n : ℤ, n < -(m : ℤ) → laurentCoeff f z₀ r n = 0 := by
  sorry

/-- DLMF §1.10(iii) (residue): at a pole, the Laurent residue `residueAt f z₀` (the coefficient
`a_{-1}`) is Tau Ceti's `TauCeti.Contour.residue f z₀`. -/
@[dlmf 1.10.iii]
theorem residueAt_eq_residue {f : ℂ → ℂ} {z₀ : ℂ} {r₂ : ℝ}
    (hf : DifferentiableOn ℂ f {z | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂}) (hm : MeromorphicAt f z₀) :
    residueAt f z₀ = TauCeti.Contour.residue f z₀ := by
  sorry

/-- DLMF §1.10(iii) (Picard's theorem): in any neighbourhood of an isolated essential
singularity (`f` analytic in a punctured disc and not meromorphic at `z₀`), `f` assumes every
value in `ℂ` with at most one exception. -/
@[dlmf 1.10.iii]
theorem picard_great {f : ℂ → ℂ} {z₀ : ℂ} {r₂ : ℝ}
    (hf : DifferentiableOn ℂ f {z | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂}) (hess : ¬ MeromorphicAt f z₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w₀ : ℂ, ∀ w : ℂ, w ≠ w₀ → ∃ z, 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < ε ∧ f z = w := by
  sorry

/-! ## §1.10(iv) Residue theorem -/

/-- DLMF 1.10.8 (residue theorem): if `f` is analytic within a simple closed contour `C` and
continuous within and on `C`, except at finitely many singularities `S` within `C`, and `C` is
described in the positive sense, then `(2πi)⁻¹ ∫_C f(z) dz` is the sum of the residues of `f`
within `C`. (Tau Ceti's `TauCeti.Contour.classicalResidueTheorem_nullHomologous` is the homology
form for meromorphic `f`.) -/
@[dlmf 1.10.E8]
theorem IsSimpleClosedContour.residueTheorem {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {S : Finset ℂ}
    (hγ : IsSimpleClosedContour γ a b) (hpos : IsPositivelyOriented γ a b)
    (hS : ↑S ⊆ contourInterior γ a b)
    (hc : ContinuousOn f ((contourInterior γ a b ∪ γ '' Icc a b) \ ↑S))
    (hd : DifferentiableOn ℂ f (contourInterior γ a b \ ↑S)) :
    (2 * Real.pi * I)⁻¹ * contourIntegral γ a b f = ∑ s ∈ S, residueAt f s := by
  sorry

/-- DLMF 1.10.9 (phase or argument principle): if the singularities of `f` within the simple
closed contour `C` are poles, the zeros and poles within `C` lie in the finite set `S`, `f` is
analytic and nonvanishing on `C` (and elsewhere within `C` off `S`), and `C` is described in the
positive sense, then `N - P = (2πi)⁻¹ ∫_C f'(z)/f(z) dz = (2π)⁻¹ Δ_C(ph f(z))`, where
`N - P = ∑_{s ∈ S} ord_s f` counts zeros and poles with multiplicity and `Δ_C(ph f)` is the
change of any continuous phase `θ(t)` of `f(γ(t))` along `C`. -/
@[dlmf 1.10.E9]
theorem IsSimpleClosedContour.argumentPrinciple {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    {S : Finset ℂ} (hγ : IsSimpleClosedContour γ a b) (hpos : IsPositivelyOriented γ a b)
    (hS : ↑S ⊆ contourInterior γ a b)
    (hf : ∀ z ∈ (contourInterior γ a b ∪ γ '' Icc a b) \ ↑S, AnalyticAt ℂ f z ∧ f z ≠ 0)
    (hm : ∀ s ∈ S, MeromorphicAt f s ∧ meromorphicOrderAt f s ≠ ⊤) :
    (2 * Real.pi * I)⁻¹ * contourIntegral γ a b (logDeriv f) =
        ∑ s ∈ S, ((meromorphicOrderAt f s).untop₀ : ℂ) ∧
      ∀ θ : ℝ → ℝ, ContinuousOn θ (Icc a b) →
        (∀ t ∈ Icc a b, IsPhase (f (γ t)) (θ t)) →
        (θ b - θ a) / (2 * Real.pi) = ∑ s ∈ S, ((meromorphicOrderAt f s).untop₀ : ℝ) := by
  sorry

/-- DLMF 1.10.10: under the hypotheses of 1.10.9,
`(2πi)⁻¹ ∫_C z f'(z)/f(z) dz = (sum of locations of zeros) - (sum of locations of poles)`, each
location counted with multiplicity. -/
@[dlmf 1.10.E10]
theorem IsSimpleClosedContour.argumentPrinciple_mul_id {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    {S : Finset ℂ} (hγ : IsSimpleClosedContour γ a b) (hpos : IsPositivelyOriented γ a b)
    (hS : ↑S ⊆ contourInterior γ a b)
    (hf : ∀ z ∈ (contourInterior γ a b ∪ γ '' Icc a b) \ ↑S, AnalyticAt ℂ f z ∧ f z ≠ 0)
    (hm : ∀ s ∈ S, MeromorphicAt f s ∧ meromorphicOrderAt f s ≠ ⊤) :
    (2 * Real.pi * I)⁻¹ * contourIntegral γ a b (fun z => z * logDeriv f z) =
      ∑ s ∈ S, ((meromorphicOrderAt f s).untop₀ : ℂ) * s := by
  sorry

/-- DLMF §1.10(iv) (Rouché's theorem): if `f` and `g` are analytic on and inside a simple closed
contour `C` and `|g(z)| < |f(z)|` on `C`, then `f` and `f + g` have the same number of zeros
inside `C`, counted with multiplicity. (Tau Ceti's `TauCeti.rouche_add` is the case of a
circle.) -/
@[dlmf 1.10.iv]
theorem IsSimpleClosedContour.rouche {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ}
    (hγ : IsSimpleClosedContour γ a b)
    (hf : AnalyticOnNhd ℂ f (contourInterior γ a b ∪ γ '' Icc a b))
    (hg : AnalyticOnNhd ℂ g (contourInterior γ a b ∪ γ '' Icc a b))
    (hlt : ∀ z ∈ γ '' Icc a b, ‖g z‖ < ‖f z‖) :
    (∑ᶠ z ∈ contourInterior γ a b, analyticOrderNatAt f z) =
      ∑ᶠ z ∈ contourInterior γ a b, analyticOrderNatAt (fun w => f w + g w) z := by
  sorry

/-! ## §1.10(v) Maximum-modulus principle -/

/-- DLMF §1.10(v) (maximum principle for harmonic functions): if `u` is harmonic in a domain
`D` and attains its maximum over `D` at `z₀ ∈ D`, then `u` is constant in `D`. -/
@[dlmf 1.10.v]
theorem harmonic_eqOn_of_isMaxOn {u : ℂ → ℝ} {D : Set ℂ} (hD : IsOpen D) (hc : IsConnected D)
    (hu : InnerProductSpace.HarmonicOnNhd u D) {z₀ : ℂ} (hz₀ : z₀ ∈ D) (hmax : IsMaxOn u D z₀) :
    EqOn u (fun _ => u z₀) D := by
  sorry

/-- DLMF §1.10(v) (maximum principle for harmonic functions on bounded domains): if `D` is
bounded and `u` is continuous on `D̄` and harmonic in `D`, then `u` attains its maximum over `D̄`
at some point of `∂D`. -/
@[dlmf 1.10.v]
theorem harmonic_exists_mem_frontier_isMaxOn {u : ℂ → ℝ} {D : Set ℂ} (hD : IsOpen D)
    (hb : Bornology.IsBounded D) (hne : D.Nonempty) (hc : ContinuousOn u (closure D))
    (hu : InnerProductSpace.HarmonicOnNhd u D) :
    ∃ z ∈ frontier D, IsMaxOn u (closure D) z := by
  sorry

/-- DLMF 1.10.11 (Schwarz's lemma, inequalities): if `f` is analytic in `|z| < R`,
`|f(z)| ≤ M` there and `f(0) = 0`, then `|f(z)| ≤ M|z|/R` and `|f'(0)| ≤ M/R`. From Mathlib's
`Complex.dist_le_div_mul_dist_of_mapsTo_ball` and `Complex.norm_deriv_le_div_of_mapsTo_ball`. -/
@[dlmf 1.10.E11]
theorem schwarz_lemma {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hM : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M) (h0 : f 0 = 0) :
    (∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M * ‖z‖ / R) ∧ ‖deriv f 0‖ ≤ M / R := by
  have hmaps : MapsTo f (ball 0 R) (closedBall (f 0) M) := fun z hz => by
    rw [h0, mem_closedBall, dist_zero_right]; exact hM z hz
  refine ⟨fun z hz => ?_, Complex.norm_deriv_le_div_of_mapsTo_ball hf hmaps hR⟩
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball hf hmaps hz
  rw [h0, dist_zero_right, dist_zero_right] at h
  calc ‖f z‖ ≤ M / R * ‖z‖ := h
    _ = M * ‖z‖ / R := by ring

/-- DLMF 1.10.11 (Schwarz's lemma, equality case): under the hypotheses of 1.10.11, equality
`|f(z₁)| = M|z₁|/R` at some `z₁ ≠ 0` or `|f'(0)| = M/R` holds iff `f(z) = Az` on `|z| < R`
with `|A| = M/R`. -/
@[dlmf 1.10.E11]
theorem schwarz_lemma_eq_iff {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hM : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M) (h0 : f 0 = 0) :
    ((∃ z₁ ∈ ball (0 : ℂ) R, z₁ ≠ 0 ∧ ‖f z₁‖ = M * ‖z₁‖ / R) ∨ ‖deriv f 0‖ = M / R) ↔
      ∃ A : ℂ, ‖A‖ = M / R ∧ EqOn f (fun z => A * z) (ball 0 R) := by
  sorry

/-! ## §1.10(vi) Multivalued functions -/

/-- DLMF §1.10(vi), example: in `D = ℂ \ (-∞, 0]` the principal branch `√r e^{iθ/2}`
(`-π < θ < π`), that is `z^{1/2}`, and its negative are analytic branches of `√z`. -/
@[dlmf 1.10.vi]
theorem sqrt_branch_slitPlane :
    DifferentiableOn ℂ (fun z : ℂ => z ^ (1 / 2 : ℂ)) slitPlane ∧
      ∀ z : ℂ, (z ^ (1 / 2 : ℂ)) ^ 2 = z ∧ (-(z ^ (1 / 2 : ℂ))) ^ 2 = z := by
  refine ⟨fun z hz => (differentiableAt_id.cpow_const hz).differentiableWithinAt, fun z => ?_⟩
  have h : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
    rw [show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num]
    exact cpow_nat_inv_pow z two_ne_zero
  exact ⟨h, by rw [neg_sq, h]⟩

/-- DLMF §1.10(vi), example: in `D = ℂ \ [0, ∞)` the branch `√r e^{iθ/2}` with `0 < θ < 2π`,
that is `i (-z)^{1/2}`, is analytic and squares to `z`. -/
@[dlmf 1.10.vi]
theorem sqrt_branch_compl_Ici :
    DifferentiableOn ℂ (fun z : ℂ => I * (-z) ^ (1 / 2 : ℂ)) {z | -z ∈ slitPlane} ∧
      ∀ z : ℂ, (I * (-z) ^ (1 / 2 : ℂ)) ^ 2 = z := by
  refine ⟨fun z hz => ?_, fun z => ?_⟩
  · exact ((differentiableAt_id.neg.cpow_const hz).const_mul I).differentiableWithinAt
  · rw [mul_pow, I_sq, show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num,
      cpow_nat_inv_pow _ two_ne_zero]
    ring

/-- DLMF §1.10(vi): `z = 0` is a branch point of `√z`: there is no continuous branch of `√z` in
any punctured neighbourhood of `0`. -/
@[dlmf 1.10.vi]
theorem not_exists_sqrt_branch_punctured {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ g : ℂ → ℂ, ContinuousOn g (ball 0 ε \ {0}) ∧ ∀ z ∈ ball (0 : ℂ) ε \ {0}, g z ^ 2 = z := by
  sorry

/-- DLMF §1.10(vi), example: for `α`, `β ∈ ℂ`, `F(z) = (1 - z)^α (1 + z)^β` with principal values
is analytic (a branch of `F`) in the plane cut along `[1, ∞)` and `(-∞, -1]`. -/
@[dlmf 1.10.vi]
theorem differentiableOn_one_sub_cpow_mul_one_add_cpow (α β : ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => (1 - z) ^ α * (1 + z) ^ β)
      {z | 1 - z ∈ slitPlane ∧ 1 + z ∈ slitPlane} := by
  intro z hz
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (1 - z) ^ α) z :=
    ((differentiableAt_const _).sub differentiableAt_id).cpow_const hz.1
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (1 + z) ^ β) z :=
    ((differentiableAt_const _).add differentiableAt_id).cpow_const hz.2
  exact (h1.mul h2).differentiableWithinAt

/-! ## §1.10(vii) Inverse functions -/

/-- DLMF 1.10.12–1.10.13 (Lagrange inversion theorem): if `f` is analytic at `z₀`,
`f'(z₀) ≠ 0` and `w₀ = f(z₀)`, then `f(z) = w` has a unique solution `z = F(w)` analytic at `w₀`
with `F(w₀) = z₀`, and `F(w) = z₀ + ∑_{n ≥ 1} Fₙ (w - w₀)ⁿ` near `w₀`, where `n Fₙ` is the
residue of `1/(f(z) - f(z₀))ⁿ` at `z₀`. Uniqueness is local: `F(f(z)) = z` near `z₀`. -/
@[dlmf 1.10.E12, dlmf 1.10.E13]
theorem lagrangeInversion {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) (hd : deriv f z₀ ≠ 0) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (f z₀) ∧ F (f z₀) = z₀ ∧
      (∀ᶠ w in 𝓝 (f z₀), f (F w) = w) ∧ (∀ᶠ z in 𝓝 z₀, F (f z) = z) ∧
      ∀ᶠ w in 𝓝 (f z₀), HasSum (fun n : ℕ =>
        residueAt (fun z => ((f z - f z₀) ^ (n + 1))⁻¹) z₀ / (n + 1) * (w - f z₀) ^ (n + 1))
        (F w - z₀) := by
  sorry

/-- DLMF 1.10.14: under the hypotheses of 1.10.12, for `g` analytic at `z₀`,
`g(F(w)) = g(z₀) + ∑_{n ≥ 1} Gₙ (w - w₀)ⁿ` near `w₀`, where `n Gₙ` is the residue of
`g'(z)/(f(z) - f(z₀))ⁿ` at `z₀`. -/
@[dlmf 1.10.E14]
theorem lagrangeBurmann {f g F : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) (hd : deriv f z₀ ≠ 0)
    (hg : AnalyticAt ℂ g z₀) (hF : AnalyticAt ℂ F (f z₀)) (hF₀ : F (f z₀) = z₀)
    (hFinv : ∀ᶠ w in 𝓝 (f z₀), f (F w) = w) :
    ∀ᶠ w in 𝓝 (f z₀), HasSum (fun n : ℕ =>
      residueAt (fun z => deriv g z / (f z - f z₀) ^ (n + 1)) z₀ / (n + 1) * (w - f z₀) ^ (n + 1))
      (g (F w) - g z₀) := by
  sorry

/-- DLMF 1.10.15–1.10.16 (extended inversion theorem), case of an integer `μ = m ≥ 1`:
suppose `f(z) - f(z₀)` has a zero of order `m` at `z₀` and `φ` is an analytic `m`-th root of it,
`φ(z)^m = f(z) - f(z₀)` near `z₀` with `φ(z₀) = 0`, `φ'(z₀) ≠ 0` (the choice of `φ` is the choice
of branch of `(f(z) - f(z₀))^{1/m}`). Then for every `ζ` near `0`, in particular for every
`m`-th root `ζ = (w - w₀)^{1/m}`, `z = z₀ + ∑_{n ≥ 1} Fₙ ζⁿ` solves `f(z) = w₀ + ζ^m` (1.10.12),
where `n Fₙ` is the residue of `1/φ(z)ⁿ = 1/(f(z) - f(z₀))^{n/m}` at `z₀`. Different roots `ζ`
give the different solutions. DLMF allows real `μ > 0` with a series in `(z - z₀)^{μ + n}`; only
integer `μ` is formalized. -/
@[dlmf 1.10.E15, dlmf 1.10.E16]
theorem extendedInversion {f φ : ℂ → ℂ} {z₀ : ℂ} {m : ℕ} (hm : 1 ≤ m) (hf : AnalyticAt ℂ f z₀)
    (hφ : AnalyticAt ℂ φ z₀) (hφ₀ : φ z₀ = 0) (hφd : deriv φ z₀ ≠ 0)
    (hroot : ∀ᶠ z in 𝓝 z₀, φ z ^ m = f z - f z₀) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ), ∃ z : ℂ,
      HasSum (fun n : ℕ => residueAt (fun z => (φ z ^ (n + 1))⁻¹) z₀ / (n + 1) * ζ ^ (n + 1))
        (z - z₀) ∧ f z = f z₀ + ζ ^ m := by
  sorry

/-- DLMF 1.10.17: in the setting of 1.10.15–1.10.16 (integer `μ = m`), for `g` analytic at `z₀`
and `z = z₀ + ∑ Fₙ ζⁿ` the solution belonging to `ζ`,
`g(z) = g(z₀) + ∑_{n ≥ 1} Gₙ ζⁿ`, where `n Gₙ` is the residue of
`g'(z)/(f(z) - f(z₀))^{n/m} = g'(z)/φ(z)ⁿ` at `z₀`. -/
@[dlmf 1.10.E17]
theorem extendedInversion_comp {f φ g : ℂ → ℂ} {z₀ : ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hf : AnalyticAt ℂ f z₀) (hφ : AnalyticAt ℂ φ z₀) (hφ₀ : φ z₀ = 0) (hφd : deriv φ z₀ ≠ 0)
    (hroot : ∀ᶠ z in 𝓝 z₀, φ z ^ m = f z - f z₀) (hg : AnalyticAt ℂ g z₀) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ), ∀ z : ℂ,
      HasSum (fun n : ℕ => residueAt (fun z => (φ z ^ (n + 1))⁻¹) z₀ / (n + 1) * ζ ^ (n + 1))
        (z - z₀) →
      HasSum (fun n : ℕ => residueAt (fun z => deriv g z / φ z ^ (n + 1)) z₀ / (n + 1) *
        ζ ^ (n + 1)) (g z - g z₀) := by
  sorry

/-! ## §1.10(viii) Functions defined by contour integrals -/

/-- DLMF 1.10.18: if `f(z, t)` is analytic in `z ∈ D` for each `t ∈ [a, b]` and continuous in
both variables, then `F(z) = ∫_a^b f(z, t) dt` is analytic in `D`, and its derivatives are
obtained by differentiating under the integral sign. -/
@[dlmf 1.10.E18]
theorem differentiableOn_intervalIntegral_param {f : ℂ → ℝ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    {a b : ℝ} (hab : a ≤ b) (hf : ∀ t ∈ Icc a b, DifferentiableOn ℂ (fun z => f z t) D)
    (hc : ContinuousOn (Function.uncurry f) (D ×ˢ Icc a b)) :
    DifferentiableOn ℂ (fun z => ∫ t in a..b, f z t) D ∧
      ∀ n : ℕ, ∀ z ∈ D, iteratedDeriv n (fun z => ∫ t in a..b, f z t) z =
        ∫ t in a..b, iteratedDeriv n (fun z => f z t) z := by
  have hmeas : ∀ z ∈ D, AEStronglyMeasurable (f z) (volume.restrict (uIoc a b)) := by
    intro z hz
    exact ((hc.uncurry_left z hz).aestronglyMeasurable measurableSet_Icc).mono_set
      (by rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self)
  have hdiff : ∀ᵐ t ∂(volume.restrict (uIoc a b)),
      DifferentiableOn ℂ (fun z => f z t) D := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    exact hf t (by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc ht)
  have hdom : ∀ z ∈ D, ∃ V ∈ 𝓝 z, ∃ g : ℝ → ℝ,
      Integrable g (volume.restrict (uIoc a b)) ∧
      ∀ᵐ t ∂(volume.restrict (uIoc a b)), ∀ w ∈ V, ‖f w t‖ ≤ g t := by
    intro z hz
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hD z hz
    have hr2 : 0 < r / 2 := half_pos hr
    have hK : IsCompact (closedBall z (r / 2) ×ˢ Icc a b) :=
      (isCompact_closedBall z (r / 2)).prod isCompact_Icc
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.mono fun p hp =>
      ⟨hsub (closedBall_subset_ball (by linarith) hp.1), hp.2⟩)
    refine ⟨ball z (r / 2), ball_mem_nhds z hr2, fun _ => C, (by
      rw [uIoc_of_le hab]
      exact (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume a b).1), ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht w hw
    refine hC (w, t) ⟨ball_subset_closedBall hw, ?_⟩
    simpa only [uIcc_of_le hab] using uIoc_subset_uIcc ht
  exact ⟨Complex.differentiableOn_intervalIntegral_of_locally_dominated hD a b hmeas hdiff hdom,
    fun n z hz => Complex.iteratedDeriv_intervalIntegral_of_locally_dominated
      hD a b hmeas hdiff hdom n hz⟩

/-- DLMF §1.10(viii) and 1.10.19 (improper integrals, `b = ∞`): if `f(z, t)` is analytic in
`z ∈ D` for each `t ≥ a`, continuous in both variables on `D × [a, ∞)`, and
`∫_a^∞ f(z, t) dt = F(z)` converges uniformly on compact subsets of `D` (1.10.19: the tails
`∫_{a₁}^∞` are uniformly small, equivalently the partial integrals `∫_a^c` converge uniformly
as `c → ∞`), then `F` is analytic in `D`. -/
@[dlmf 1.10.E19]
theorem differentiableOn_improperIntegral_param {f : ℂ → ℝ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    {a : ℝ} (hf : ∀ t ∈ Ici a, DifferentiableOn ℂ (fun z => f z t) D)
    (hc : ContinuousOn (Function.uncurry f) (D ×ˢ Ici a)) {F : ℂ → ℂ}
    (hu : ∀ K ⊆ D, IsCompact K →
      TendstoUniformlyOn (fun c z => ∫ t in a..c, f z t) F atTop K) :
    DifferentiableOn ℂ F D := by
  have hl : TendstoLocallyUniformlyOn (fun c z => ∫ t in a..c, f z t) F atTop D :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mpr hu
  apply hl.differentiableOn ?_ hD
  filter_upwards [eventually_ge_atTop a] with c hc'
  exact (differentiableOn_intervalIntegral_param hD hc'
    (fun t ht => hf t ht.1) (hc.mono fun p hp => ⟨hp.1, hp.2.1⟩)).1

/-- DLMF §1.10(viii) (improper integrals with a singularity at a finite `b`): if `f(z, t)` is
analytic in `z ∈ D` for each `t ∈ [a, b)`, continuous in both variables on `D × [a, b)`, and
`∫_a^b f(z, t) dt = F(z)` converges uniformly on compact subsets of `D` (the partial integrals
`∫_a^c` converge uniformly as `c → b-`), then `F` is analytic in `D`. -/
@[dlmf 1.10.viii]
theorem differentiableOn_improperIntegral_param_of_lt {f : ℂ → ℝ → ℂ} {D : Set ℂ}
    (hD : IsOpen D) {a b : ℝ} (hab : a < b)
    (hf : ∀ t ∈ Ico a b, DifferentiableOn ℂ (fun z => f z t) D)
    (hc : ContinuousOn (Function.uncurry f) (D ×ˢ Ico a b)) {F : ℂ → ℂ}
    (hu : ∀ K ⊆ D, IsCompact K →
      TendstoUniformlyOn (fun c z => ∫ t in a..c, f z t) F (𝓝[<] b) K) :
    DifferentiableOn ℂ F D := by
  have hl : TendstoLocallyUniformlyOn (fun c z => ∫ t in a..c, f z t) F (𝓝[<] b) D :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mpr hu
  apply hl.differentiableOn ?_ hD
  filter_upwards [Ioo_mem_nhdsLT hab] with c hc'
  exact (differentiableOn_intervalIntegral_param hD hc'.1.le
    (fun t ht => hf t ⟨ht.1, lt_of_le_of_lt ht.2 hc'.2⟩)
    (hc.mono fun p hp => ⟨hp.1, hp.2.1, lt_of_le_of_lt hp.2.2 hc'.2⟩)).1

/-- DLMF §1.10(viii) (`M`-test for integrals): if `|f(z, t)| ≤ M(t)` for `z ∈ S`, `t ≥ a`, and
`∫_a^∞ M(t) dt` converges, then `∫_a^∞ f(z, t) dt` converges absolutely and uniformly on `S`. -/
@[dlmf 1.10.viii]
theorem tendstoUniformlyOn_integral_of_norm_le {f : ℂ → ℝ → ℂ} {S : Set ℂ} {a : ℝ} {M : ℝ → ℝ}
    (hmeas : ∀ z ∈ S, AEStronglyMeasurable (f z) (volume.restrict (Ioi a)))
    (hM : IntegrableOn M (Ioi a)) (hle : ∀ z ∈ S, ∀ t ∈ Ioi a, ‖f z t‖ ≤ M t) :
    (∀ z ∈ S, IntegrableOn (f z) (Ioi a)) ∧
      TendstoUniformlyOn (fun c z => ∫ t in a..c, f z t) (fun z => ∫ t in Ioi a, f z t)
        atTop S := by
  have hi : ∀ z ∈ S, IntegrableOn (f z) (Ioi a) := by
    intro z hz
    apply hM.mono' (hmeas z hz)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hle z hz t ht
  have hMn : IntegrableOn (fun t => ‖M t‖) (Ioi a) := hM.norm
  refine ⟨hi, Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_⟩
  have ht : Tendsto (fun c : ℝ => ∫ t in Ioi c, ‖M t‖) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  filter_upwards [eventually_ge_atTop a, ht.eventually (gt_mem_nhds hε)] with c hc hεc z hz
  have hzi := hi z hz
  have htail : (∫ t in Ioi a, f z t) - (∫ t in a..c, f z t) = ∫ t in Ioi c, f z t := by
    have he := intervalIntegral.integral_interval_add_Ioi hzi (hzi.mono_set (Ioi_subset_Ioi hc))
    linear_combination -he
  rw [dist_eq_norm, htail]
  refine lt_of_le_of_lt (norm_integral_le_of_norm_le
    (hMn.mono_set (Ioi_subset_Ioi hc)) ?_) hεc
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (hle z hz t (lt_of_le_of_lt hc ht)).trans (le_abs_self _)

/-! ## §1.10(ix) Infinite products -/

/-- DLMF §1.10(ix): the product `∏_{n ≥ 1} (1 + aₙ)` with `aₙ ≠ -1` for all `n` converges iff
`∑_{n ≥ 1} ln(1 + aₙ)` converges (principal logarithms, partial sums). -/
@[dlmf 1.10.ix]
theorem prodConvergesDLMF_iff_log {a : ℕ → ℂ} (ha : ∀ n ≥ 1, a n ≠ -1) :
    ProdConvergesDLMF a ↔
      ∃ s, Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, log (1 + a n)) atTop (𝓝 s) := by
  sorry

/-- DLMF §1.10(ix): the product `∏_{n ≥ 1} (1 + aₙ)` converges absolutely (that is,
`∏ (1 + |aₙ|)` converges) iff `∑_{n ≥ 1} |aₙ|` converges. -/
@[dlmf 1.10.ix]
theorem prodConvergesDLMF_norm_iff {a : ℕ → ℂ} :
    ProdConvergesDLMF (fun n => (‖a n‖ : ℂ)) ↔ Summable (fun n => ‖a (n + 1)‖) := by
  sorry

/-- DLMF 1.10.20–1.10.21 (`M`-test for products): let `aₙ` be analytic in the domain `D`; if
`|ln(1 + aₙ(z))| ≤ Mₙ` for `n ≥ N` and `z ∈ D` and `∑ Mₙ < ∞`, then `∏_{n ≥ 1} (1 + aₙ(z))`
converges uniformly to a function `p` analytic in `D`, and `p(z) = 0` only where some factor
`1 + aₙ(z)` vanishes. -/
@[dlmf 1.10.E20]
theorem prod_mtest_log {a : ℕ → ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (ha : ∀ n, DifferentiableOn ℂ (a n) D) {M : ℕ → ℝ} {N : ℕ}
    (hM : ∀ n ≥ N, ∀ z ∈ D, ‖log (1 + a n z)‖ ≤ M n) (hs : Summable M) :
    ∃ p : ℂ → ℂ, DifferentiableOn ℂ p D ∧
      TendstoUniformlyOn (fun m z => ∏ n ∈ Finset.Icc 1 m, (1 + a n z)) p atTop D ∧
      ∀ z ∈ D, p z = 0 → ∃ n ≥ 1, 1 + a n z = 0 := by
  sorry

/-- DLMF §1.10(ix) (`M`-test for products, second form): the conclusion of 1.10.20–1.10.21 holds
if instead `|aₙ(z)| ≤ Mₙ` for all `n` and `z ∈ D`, with `∑ Mₙ < ∞`. -/
@[dlmf 1.10.E21]
theorem prod_mtest {a : ℕ → ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (ha : ∀ n, DifferentiableOn ℂ (a n) D) {M : ℕ → ℝ}
    (hM : ∀ n, ∀ z ∈ D, ‖a n z‖ ≤ M n) (hs : Summable M) :
    ∃ p : ℂ → ℂ, DifferentiableOn ℂ p D ∧
      TendstoUniformlyOn (fun m z => ∏ n ∈ Finset.Icc 1 m, (1 + a n z)) p atTop D ∧
      ∀ z ∈ D, p z = 0 → ∃ n ≥ 1, 1 + a n z = 0 := by
  sorry

/-- DLMF 1.10.22 (Weierstrass product): if `zₙ ≠ 0` and `∑ |zₙ|⁻²` converges, then
`P(z) = ∏ (1 - z/zₙ) e^{z/zₙ}` (an absolutely convergent product) is an entire function whose
zeros are exactly the points `zₙ`. -/
@[dlmf 1.10.E22]
theorem weierstrassProduct {zs : ℕ → ℂ} (hz : ∀ n, zs n ≠ 0)
    (hs : Summable (fun n => ‖zs n‖⁻¹ ^ 2)) :
    (∀ z, Multipliable (fun n => (1 - z / zs n) * exp (z / zs n))) ∧
      Differentiable ℂ (fun z => ∏' n, (1 - z / zs n) * exp (z / zs n)) ∧
      ∀ z, (∏' n, (1 - z / zs n) * exp (z / zs n)) = 0 ↔ ∃ n, z = zs n := by
  sorry

/-! ## §1.10(x) Infinite partial fractions -/

/-- DLMF 1.10.23: if the `aₙ` are analytic in the domain `D` and the partial products of
`F(z) = ∏ aₙ(z)` converge uniformly on compact subsets of `D`, then `F` is analytic in `D`. From
Mathlib's `TendstoLocallyUniformlyOn.differentiableOn`. -/
@[dlmf 1.10.E23]
theorem differentiableOn_of_tendstoUniformlyOn_prod {a : ℕ → ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (ha : ∀ n, DifferentiableOn ℂ (a n) D) {F : ℂ → ℂ}
    (hu : ∀ K ⊆ D, IsCompact K →
      TendstoUniformlyOn (fun m z => ∏ n ∈ Finset.range m, a n z) F atTop K) :
    DifferentiableOn ℂ F D := by
  have hl : TendstoLocallyUniformlyOn (fun m z => ∏ n ∈ Finset.range m, a n z) F atTop D :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mpr hu
  refine hl.differentiableOn (Eventually.of_forall fun m => ?_) hD
  exact DifferentiableOn.fun_finsetProd fun n _ => ha n

/-- DLMF 1.10.24: if, in addition to the hypotheses of 1.10.23, `aₙ(z) ≠ 0` on `D` and the
product converges in the sense of DLMF (nonzero limit, `F(z) ≠ 0` on `D`; this hypothesis is
part of DLMF's notion of convergence and cannot be dropped: `aₙ = ½` gives the uniform limit
`0`), then `F'/F = ∑ aₙ'/aₙ` on `D`, the series converging as partial sums. -/
@[dlmf 1.10.E24]
theorem tendsto_logDeriv_prod {a : ℕ → ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (ha : ∀ n, DifferentiableOn ℂ (a n) D) (ha0 : ∀ n, ∀ z ∈ D, a n z ≠ 0) {F : ℂ → ℂ}
    (hu : ∀ K ⊆ D, IsCompact K →
      TendstoUniformlyOn (fun m z => ∏ n ∈ Finset.range m, a n z) F atTop K)
    (hF : ∀ z ∈ D, F z ≠ 0) {z : ℂ} (hz : z ∈ D) :
    Tendsto (fun m => ∑ n ∈ Finset.range m, logDeriv (a n) z) atTop (𝓝 (logDeriv F z)) := by
  let P : ℕ → ℂ → ℂ := fun m z => ∏ n ∈ Finset.range m, a n z
  have hP : ∀ m, DifferentiableOn ℂ (P m) D :=
    fun _ => DifferentiableOn.fun_finsetProd fun n _ => ha n
  have hl : TendstoLocallyUniformlyOn P F atTop D :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mpr hu
  have hd := (hl.deriv (Eventually.of_forall hP) hD).tendsto_at hz
  have hv := hl.tendsto_at hz
  have hlim := hd.div hv (hF z hz)
  change Tendsto (fun m => deriv (P m) z / P m z) atTop (𝓝 (logDeriv F z)) at hlim
  refine hlim.congr' (Eventually.of_forall fun m => ?_)
  change logDeriv (fun w => ∏ n ∈ Finset.range m, a n w) z = _
  exact (logDeriv_fun_prod (fun n _ => ha0 n z hz)
    (fun n _ => (ha n).differentiableAt (hD.mem_nhds hz)))

/-- DLMF 1.10.25 (Mittag-Leffler expansion): if the `zₙ` are distinct and nonzero, `|zₙ| → ∞`,
and `∑ |aₙ zₙ⁻²|` converges, then `f(z) = ∑ aₙ (1/(z - zₙ) + 1/zₙ)` is analytic in `ℂ` except
for simple poles at the `zₙ` of residue `aₙ` (removable when `aₙ = 0`). The hypotheses
`zₙ ≠ 0` and `|zₙ| → ∞` are implicit in DLMF: without the latter the `zₙ` may accumulate at a
finite point, which is then a non-isolated singularity. -/
@[dlmf 1.10.E25]
theorem mittagLeffler {a zs : ℕ → ℂ} (hinj : Function.Injective zs) (hz : ∀ n, zs n ≠ 0)
    (hlim : Tendsto (fun n => ‖zs n‖) atTop atTop) (hs : Summable (fun n => ‖a n / zs n ^ 2‖)) :
    DifferentiableOn ℂ (fun z => ∑' n, a n * (1 / (z - zs n) + 1 / zs n)) (range zs)ᶜ ∧
      ∀ n, residueAt (fun z => ∑' k, a k * (1 / (z - zs k) + 1 / zs k)) (zs n) = a n ∧
        ∃ g : ℂ → ℂ, AnalyticAt ℂ g (zs n) ∧
          ∀ᶠ z in 𝓝[≠] (zs n),
            ∑' k, a k * (1 / (z - zs k) + 1 / zs k) = a n / (z - zs n) + g z := by
  sorry

/-! ## §1.10(xi) Generating functions -/

/-- DLMF 1.10.26–1.10.27: if `F(z) = ∑ pₙ zⁿ` for `|z| < R` (the generating function of the
`pₙ`; for a family `F(x; z)` apply this for each fixed `x`), then
`pₙ = (2πi)⁻¹ ∮_{|z| = r} F(z) z^{-n-1} dz` for `0 < r < R`. -/
@[dlmf 1.10.E26, dlmf 1.10.E27]
theorem coeff_eq_circleIntegral {p : ℕ → ℂ} {F : ℂ → ℂ} {R : ℝ}
    (hF : ∀ z ∈ ball (0 : ℂ) R, HasSum (fun n => p n * z ^ n) (F z)) {r : ℝ} (hr : r ∈ Ioo 0 R)
    (n : ℕ) : p n = (2 * Real.pi * I)⁻¹ * ∮ z in C(0, r), F z / z ^ (n + 1) := by
  sorry

end DLMF.AlgebraicAnalytic
