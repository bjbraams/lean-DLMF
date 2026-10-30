/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.Basic
public import DLMFMathlib.Analysis.ODE.Singularities

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion

/-!
# Singularities of linear second-order equations (DLMF §2.7(i), (ii), (iv))

* §2.7(i): ordinary points, regular singularities, the Frobenius solutions 2.7.4–2.7.6.
* §2.7(ii): the rank of a singularity, the formal solutions 2.7.8–2.7.11 at an irregular
  singularity of rank 1 at infinity, the actual solutions 2.7.14–2.7.16, the connection
  formulas with Stokes multipliers 2.7.17, the late-coefficient asymptotics 2.7.12–2.7.13
  with 2.7.18, and Fabry's transformation 2.7.19.
* §2.7(iv): the solution pairs of `w'' = w` (2.7.35–2.7.37).

Solutions near an irregular singularity at infinity live on sectors of opening up to `3π`, so
they are stated on the logarithmic plane (`IsLogPlaneSolOn`, `z = e^ζ`, `ph z = ℑζ`). The
phase of `(λ₂ - λ₁) z` in 2.7.15–2.7.16 is `ℑ(ζ + Log(λ₂ - λ₁))`, and the power
`((λ₂ - λ₁) z)^{μ}` is `exp(μ (ζ + Log(λ₂ - λ₁)))`. Sector conditions `θ₁ ≤ ph ≤ θ₂` as `|z| → ∞`
are expressed by the filter `logSectorFilter θ₁ θ₂ c`.
-/

@[expose] public noncomputable section

open Set Complex Filter Asymptotics
open scoped Topology Real

namespace DLMF.AsymptoticApproximations

/-! ### §2.7(i) Regular singularities: Fuchs–Frobenius theory -/

/-- DLMF 2.7.i: at an ordinary point the solutions are analytic. If `f` and `g` are holomorphic
on the disc `|z - z₀| < R`, then for all initial data there is a unique solution of 2.7.1 on
the whole disc; in particular its Taylor series at `z₀` converges in the disc (the radius of
convergence is at least the distance to the nearest singularity, 2.7.i.p5). -/
@[dlmf 2.7.i]
theorem exists_unique_solution_of_ordinary {f g : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R)) (hg : DifferentiableOn ℂ g (Metric.ball z₀ R))
    (w₀ w₁ : ℂ) :
    ∃ w : ℂ → ℂ, IsLinearODE2SolOn f g w (Metric.ball z₀ R) ∧ w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      AnalyticOnNhd ℂ w (Metric.ball z₀ R) ∧
      ∀ v : ℂ → ℂ, IsLinearODE2SolOn f g v (Metric.ball z₀ R) → v z₀ = w₀ → deriv v z₀ = w₁ →
        EqOn v w (Metric.ball z₀ R) := by
  sorry

/-- DLMF 2.7.i: `z₀` is a regular singularity of 2.7.1 iff it is not an ordinary point and both
`(z - z₀) f(z)` and `(z - z₀)² g(z)` are analytic at `z₀` (after removal of a removable
singularity), in DLMFMathlib's classification with the coefficient vector `![g, f]`. -/
@[dlmf 2.7.i]
theorem linearODERegularSingularAt_iff (f g : ℂ → ℂ) (z₀ : ℂ) :
    Complex.LinearODERegularSingularAt ![g, f] z₀ ↔
      ¬ Complex.LinearODEOrdinaryAt ![g, f] z₀ ∧
        (∃ F : ℂ → ℂ, AnalyticAt ℂ F z₀ ∧ (fun z => (z - z₀) * f z) =ᶠ[𝓝[≠] z₀] F) ∧
        ∃ G : ℂ → ℂ, AnalyticAt ℂ G z₀ ∧ (fun z => (z - z₀) ^ 2 * g z) =ᶠ[𝓝[≠] z₀] G := by
  unfold Complex.LinearODERegularSingularAt Complex.LinearODEAtMostRegularAt
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero,
    Fin.val_one, Nat.sub_zero]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by simpa using h2, h1⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, h2, by simpa using h1⟩

/-- DLMF 2.7.4–2.7.5 (with 2.7.2, 2.7.3 and the radius statement 2.7.i.p5): at a regular
singularity with `f(z) = ∑ f_s (z-z₀)^{s-1}`, `g(z) = ∑ g_s (z-z₀)^{s-2}` for
`0 < |z - z₀| < R` and indices `α₁, α₂` (roots of `Q(α) = 0`) with `α₁ - α₂ ∉ ℤ`, the series
`∑ a_{s,j} (z-z₀)^s` with the coefficients of 2.7.5 converge for `|z - z₀| < R`, and
`w_j(z) = (z-z₀)^{α_j} ∑ a_{s,j} (z-z₀)^s` are linearly independent solutions (principal
powers, on the slit disc). -/
@[dlmf 2.7.E4, dlmf 2.7.E2, dlmf 2.7.E3, dlmf 2.7.E5]
theorem frobenius_solutions {f g : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R) {fs gs : ℕ → ℂ}
    (hf : ∀ z, z ≠ z₀ → ‖z - z₀‖ < R → HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, z ≠ z₀ → ‖z - z₀‖ < R →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    {α₁ α₂ : ℂ} (h₁ : indicialPoly (fs 0) (gs 0) α₁ = 0) (h₂ : indicialPoly (fs 0) (gs 0) α₂ = 0)
    (h₁₂ : ∀ k : ℤ, α₁ - α₂ ≠ k) :
    (∀ z, ‖z - z₀‖ < R → Summable (fun s => frobeniusCoeff fs gs α₁ s * (z - z₀) ^ s) ∧
      Summable (fun s => frobeniusCoeff fs gs α₂ s * (z - z₀) ^ s)) ∧
    IsLinearODE2SolOn f g (fun z => (z - z₀) ^ α₁ *
      ∑' s, frobeniusCoeff fs gs α₁ s * (z - z₀) ^ s) (g2b_slitDisc z₀ R) ∧
    IsLinearODE2SolOn f g (fun z => (z - z₀) ^ α₂ *
      ∑' s, frobeniusCoeff fs gs α₂ s * (z - z₀) ^ s) (g2b_slitDisc z₀ R) ∧
    ¬ ∃ c : ℂ, ∀ z ∈ g2b_slitDisc z₀ R,
      (z - z₀) ^ α₁ * ∑' s, frobeniusCoeff fs gs α₁ s * (z - z₀) ^ s =
        c * ((z - z₀) ^ α₂ * ∑' s, frobeniusCoeff fs gs α₂ s * (z - z₀) ^ s) := by
  sorry

/-- DLMF 2.7.6: if `α₁ - α₂ = N ∈ {0, 1, 2, …}`, the Frobenius solution `w₁` exists, and there
is an independent solution
`w₂(z) = (z-z₀)^{α₂} ∑_{s ≠ N} b_s (z-z₀)^s + c w₁(z) ln(z - z₀)`, with `c = 1` if `N = 0` and
`b_0 = 1` if `N ≥ 1`; the series converges for `|z - z₀| < R` (2.7.i.p5). -/
@[dlmf 2.7.E6]
theorem frobenius_log_solution {f g : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R) {fs gs : ℕ → ℂ}
    (hf : ∀ z, z ≠ z₀ → ‖z - z₀‖ < R → HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, z ≠ z₀ → ‖z - z₀‖ < R →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    {α₁ α₂ : ℂ} (h₁ : indicialPoly (fs 0) (gs 0) α₁ = 0) (h₂ : indicialPoly (fs 0) (gs 0) α₂ = 0)
    {N : ℕ} (hN : α₁ - α₂ = N) :
    let w₁ : ℂ → ℂ := fun z => (z - z₀) ^ α₁ * ∑' s, frobeniusCoeff fs gs α₁ s * (z - z₀) ^ s
    IsLinearODE2SolOn f g w₁ (g2b_slitDisc z₀ R) ∧
    ∃ (b : ℕ → ℂ) (c : ℂ), (N = 0 → c = 1) ∧ (1 ≤ N → b 0 = 1) ∧
      (∀ z, ‖z - z₀‖ < R → Summable (fun s => b s * (z - z₀) ^ s)) ∧
      IsLinearODE2SolOn f g (fun z => (z - z₀) ^ α₂ *
          ∑' s, (if s = N then 0 else b s) * (z - z₀) ^ s + c * w₁ z * log (z - z₀))
        (g2b_slitDisc z₀ R) ∧
      ¬ ∃ d : ℂ, ∀ z ∈ g2b_slitDisc z₀ R, (z - z₀) ^ α₂ *
          ∑' s, (if s = N then 0 else b s) * (z - z₀) ^ s + c * w₁ z * log (z - z₀) =
        d * w₁ z := by
  sorry

/-! ### §2.7(ii) Irregular singularities of rank 1 -/

/-- DLMF 2.7.ii: a regular singularity has rank `0`. -/
@[dlmf 2.7.ii]
theorem hasSingularityRank_zero_of_regularSingular {f g : ℂ → ℂ} {z₀ : ℂ}
    (h : Complex.LinearODERegularSingularAt ![g, f] z₀) : HasSingularityRank f g z₀ 0 := by
  obtain ⟨-, hF, hG⟩ := (linearODERegularSingularAt_iff f g z₀).1 h
  refine ⟨⟨le_rfl, ?_, ?_⟩, fun ℓ hℓ => hℓ.1⟩
  · simpa using hF
  · simpa using hG

/-- DLMF 2.7.9 and the failure criterion after 2.7.11: if `λ₁, λ₂` are the roots of the
characteristic equation `λ² + f₀λ + g₀ = 0` (in Vieta form `λ₁ + λ₂ = -f₀`, `λ₁λ₂ = g₀`), then
`f₀ + 2λ₁ = λ₁ - λ₂`, so the recursion 2.7.11 for `j = 1` fails iff `λ₁ = λ₂`, iff
`f₀² = 4g₀`. -/
@[dlmf 2.7.E9]
theorem characteristic_roots_eq_iff {f₀ g₀ l₁ l₂ : ℂ} (hs : l₁ + l₂ = -f₀) (hp : l₁ * l₂ = g₀) :
    f₀ + 2 * l₁ = l₁ - l₂ ∧ (l₁ = l₂ ↔ f₀ ^ 2 = 4 * g₀) := by
  have hf : f₀ = -(l₁ + l₂) := by linear_combination hs
  rw [hf, ← hp]
  refine ⟨by ring, ⟨fun h => by subst h; ring, fun h => ?_⟩⟩
  have : (l₁ - l₂) ^ 2 = 0 := by linear_combination h
  exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)

/-- DLMF 2.7.14–2.7.16 (with 2.7.7–2.7.11): at a rank-one irregular singularity at infinity
with `λ₁ ≠ λ₂`, there are unique solutions `w₁, w₂` (on the logarithmic plane) with
`w_j(z) ∼ e^{λ_j z} ((λ₂-λ₁) z)^{μ_j} ∑ a_{s,j} z^{-s}` as `z → ∞` in the sectors
`-3π/2 + δ ≤ ph((λ₂-λ₁) z) ≤ 3π/2 - δ` (`j = 1`) and
`-π/2 + δ ≤ ph((λ₂-λ₁) z) ≤ 5π/2 - δ` (`j = 2`), for every `δ > 0`; `μ_j` and `a_{s,j}` are
given by 2.7.10–2.7.11. Uniqueness: any solution with the expansion in one such sector equals
`w_j`. -/
@[dlmf 2.7.E14, dlmf 2.7.E15, dlmf 2.7.E16, dlmf 2.7.E7, dlmf 2.7.E8]
theorem rankOne_exists_unique_solutions {f g : ℂ → ℂ} {fs gs : ℕ → ℂ} {a : ℝ} {l₁ l₂ : ℂ}
    (h : IsRankOneAtInfinity f g fs gs a l₁ l₂) :
    let c := Complex.log (l₂ - l₁)
    let μ₁ := rankOneExponent fs gs l₁
    let μ₂ := rankOneExponent fs gs l₂
    ∃ W₁ W₂ : ℂ → ℂ,
      IsLogPlaneSolOn f g W₁ (g2b_logExterior a) ∧ IsLogPlaneSolOn f g W₂ (g2b_logExterior a) ∧
      (∀ δ : ℝ, 0 < δ → δ < π →
        HasAsymptoticExpansion (logSectorFilter (-(3 * π / 2) + δ) (3 * π / 2 - δ) c)
          (rankOneScale l₁ μ₁ c) (rankOneCoeff fs gs l₁) W₁ ∧
        HasAsymptoticExpansion (logSectorFilter (-(π / 2) + δ) (5 * π / 2 - δ) c)
          (rankOneScale l₂ μ₂ c) (rankOneCoeff fs gs l₂) W₂) ∧
      (∀ δ : ℝ, 0 < δ → δ < π → ∀ V : ℂ → ℂ, IsLogPlaneSolOn f g V (g2b_logExterior a) →
        HasAsymptoticExpansion (logSectorFilter (-(3 * π / 2) + δ) (3 * π / 2 - δ) c)
          (rankOneScale l₁ μ₁ c) (rankOneCoeff fs gs l₁) V → EqOn V W₁ (g2b_logExterior a)) ∧
      (∀ δ : ℝ, 0 < δ → δ < π → ∀ V : ℂ → ℂ, IsLogPlaneSolOn f g V (g2b_logExterior a) →
        HasAsymptoticExpansion (logSectorFilter (-(π / 2) + δ) (5 * π / 2 - δ) c)
          (rankOneScale l₂ μ₂ c) (rankOneCoeff fs gs l₂) V → EqOn V W₂ (g2b_logExterior a)) := by
  sorry

/-- DLMF 2.7.17: connection formulas with the **Stokes multipliers** `C₁, C₂`: the solutions
`w₁, w₂` of 2.7.14 satisfy `w₁(z) = e^{2πiμ₁} w₁(z e^{-2πi}) + C₁ w₂(z)` and
`w₂(z) = e^{-2πiμ₂} w₂(z e^{2πi}) + C₂ w₁(z)` (on the logarithmic plane, `z e^{±2πi}` is
`ζ ± 2πi`). -/
@[dlmf 2.7.E17]
theorem rankOne_stokes_multipliers {f g : ℂ → ℂ} {fs gs : ℕ → ℂ} {a : ℝ} {l₁ l₂ : ℂ}
    (h : IsRankOneAtInfinity f g fs gs a l₁ l₂) {W₁ W₂ : ℂ → ℂ}
    (hW₁ : IsLogPlaneSolOn f g W₁ (g2b_logExterior a))
    (hW₂ : IsLogPlaneSolOn f g W₂ (g2b_logExterior a))
    (hE₁ : HasAsymptoticExpansion (logSectorFilter (-π) π (Complex.log (l₂ - l₁)))
      (rankOneScale l₁ (rankOneExponent fs gs l₁) (Complex.log (l₂ - l₁)))
      (rankOneCoeff fs gs l₁) W₁)
    (hE₂ : HasAsymptoticExpansion (logSectorFilter 0 (2 * π) (Complex.log (l₂ - l₁)))
      (rankOneScale l₂ (rankOneExponent fs gs l₂) (Complex.log (l₂ - l₁)))
      (rankOneCoeff fs gs l₂) W₂) :
    ∃ C₁ C₂ : ℂ, ∀ ζ ∈ g2b_logExterior a,
      W₁ ζ = exp (2 * π * I * rankOneExponent fs gs l₁) * W₁ (ζ - 2 * π * I) + C₁ * W₂ ζ ∧
      W₂ ζ = exp (-(2 * π * I * rankOneExponent fs gs l₂)) * W₂ (ζ + 2 * π * I) + C₂ * W₁ ζ := by
  sorry

/-- DLMF 2.7.12–2.7.13 with 2.7.18 (resurgence of the late coefficients): with the Stokes
multipliers `C₁, C₂` of 2.7.17 and `Λ₁ = -i e^{(μ₂-μ₁)πi} C₁/(2π)`, `Λ₂ = i C₂/(2π)`,
`a_{s,1} = Λ₁ (λ₁-λ₂)^{-s} (∑_{j<J} a_{j,2} (λ₁-λ₂)^j Γ(s+μ₂-μ₁-j)
  + O(Γ(s+μ₂-μ₁-J)))` as `s → ∞`, and symmetrically for `a_{s,2}`. The bound below is
`O(|λ₁-λ₂|^{-s} |Γ(s+μ₂-μ₁-J)|)`, without the factor `Λ₁`. -/
@[dlmf 2.7.E12, dlmf 2.7.E13, dlmf 2.7.E18]
theorem rankOne_late_coefficients {f g : ℂ → ℂ} {fs gs : ℕ → ℂ} {a : ℝ} {l₁ l₂ : ℂ}
    (h : IsRankOneAtInfinity f g fs gs a l₁ l₂) {W₁ W₂ : ℂ → ℂ}
    (hW₁ : IsLogPlaneSolOn f g W₁ (g2b_logExterior a))
    (hW₂ : IsLogPlaneSolOn f g W₂ (g2b_logExterior a))
    (hE₁ : HasAsymptoticExpansion (logSectorFilter (-π) π (Complex.log (l₂ - l₁)))
      (rankOneScale l₁ (rankOneExponent fs gs l₁) (Complex.log (l₂ - l₁)))
      (rankOneCoeff fs gs l₁) W₁)
    (hE₂ : HasAsymptoticExpansion (logSectorFilter 0 (2 * π) (Complex.log (l₂ - l₁)))
      (rankOneScale l₂ (rankOneExponent fs gs l₂) (Complex.log (l₂ - l₁)))
      (rankOneCoeff fs gs l₂) W₂)
    {C₁ C₂ : ℂ}
    (hC : ∀ ζ ∈ g2b_logExterior a,
      W₁ ζ = exp (2 * π * I * rankOneExponent fs gs l₁) * W₁ (ζ - 2 * π * I) + C₁ * W₂ ζ ∧
      W₂ ζ = exp (-(2 * π * I * rankOneExponent fs gs l₂)) * W₂ (ζ + 2 * π * I) + C₂ * W₁ ζ)
    (J : ℕ) :
    let μ₁ := rankOneExponent fs gs l₁
    let μ₂ := rankOneExponent fs gs l₂
    let Λ₁ := -I * exp ((μ₂ - μ₁) * π * I) * C₁ / (2 * π)
    let Λ₂ := I * C₂ / (2 * π)
    (fun s : ℕ => rankOneCoeff fs gs l₁ s - Λ₁ / (l₁ - l₂) ^ s *
        ∑ j ∈ Finset.range J, rankOneCoeff fs gs l₂ j * (l₁ - l₂) ^ j * Gamma (s + μ₂ - μ₁ - j))
      =O[atTop] (fun s : ℕ => ‖Gamma (s + μ₂ - μ₁ - J)‖ / ‖l₁ - l₂‖ ^ s) ∧
    (fun s : ℕ => rankOneCoeff fs gs l₂ s - Λ₂ / (l₂ - l₁) ^ s *
        ∑ j ∈ Finset.range J, rankOneCoeff fs gs l₁ j * (l₂ - l₁) ^ j * Gamma (s + μ₁ - μ₂ - j))
      =O[atTop] (fun s : ℕ => ‖Gamma (s + μ₁ - μ₂ - J)‖ / ‖l₁ - l₂‖ ^ s) := by
  sorry

/-- DLMF 2.7.19 (Fabry's transformation): if `w` solves 2.7.1 on an open set `U`, then
`W(t) = e^{f₀ t²/2} w(t²)` (that is, `w = e^{-f₀ z/2} W`, `t = z^{1/2}`) solves
`W'' + F(t) W' + G(t) W = 0` with `F(t) = 2t (f(t²) - f₀) - 1/t` and
`G(t) = 4t² (g(t²) - f₀ f(t²)/2 + f₀²/4)`, on `{t ≠ 0 : t² ∈ U}`. -/
@[dlmf 2.7.E19]
theorem fabry_transformation {f g w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hw : IsLinearODE2SolOn f g w U) (f₀ : ℂ) :
    IsLinearODE2SolOn (fun t => 2 * t * (f (t ^ 2) - f₀) - 1 / t)
      (fun t => 4 * t ^ 2 * (g (t ^ 2) - f₀ * f (t ^ 2) / 2 + f₀ ^ 2 / 4))
      (fun t => exp (f₀ * t ^ 2 / 2) * w (t ^ 2)) {t : ℂ | t ≠ 0 ∧ t ^ 2 ∈ U} := by
  sorry

/-- DLMF 2.7.ii (Fabry's transformation, the dichotomy): if `f₀² = 4g₀`, the coefficients of
the transformed equation of 2.7.19 have the expansions
`t F(t) = (2f₁ - 1) + ∑_{s≥1} 2 f_{s+1} t^{-2s}` and
`G(t) = ∑_{s≥0} 4 (g_{s+1} - f₀ f_{s+1}/2) t^{-2s}`, so its characteristic equation is
`λ² + 4(g₁ - f₀f₁/2) = 0`: either `g₁ ≠ f₀f₁/2` and the roots are unequal, or `t F(t)` and
`t² G(t)` are power series in `t⁻¹` and `t = ∞` is a regular singularity. -/
@[dlmf 2.7.ii]
theorem fabry_coefficients {f g : ℂ → ℂ} {fs gs : ℕ → ℂ} {a : ℝ}
    (hf : ∀ z : ℂ, a < ‖z‖ → HasSum (fun s => fs s * z⁻¹ ^ s) (f z))
    (hg : ∀ z : ℂ, a < ‖z‖ → HasSum (fun s => gs s * z⁻¹ ^ s) (g z))
    (h0 : fs 0 ^ 2 = 4 * gs 0) {t : ℂ} (ht : a < ‖t ^ 2‖) :
    HasSum (fun s => (if s = 0 then 2 * fs 1 - 1 else 2 * fs (s + 1)) * (t⁻¹ ^ 2) ^ s)
        (t * (2 * t * (f (t ^ 2) - fs 0) - 1 / t)) ∧
      HasSum (fun s => 4 * (gs (s + 1) - fs 0 * fs (s + 1) / 2) * (t⁻¹ ^ 2) ^ s)
        (4 * t ^ 2 * (g (t ^ 2) - fs 0 * f (t ^ 2) / 2 + fs 0 ^ 2 / 4)) := by
  sorry

/-! ### §2.7(iv) Numerically satisfactory solutions -/

/-- DLMF 2.7.35–2.7.36: `e^z` and `e^{-z}` solve `w'' = w`, and every entire solution is
`w = A e^z + B e^{-z}`. -/
@[dlmf 2.7.E35, dlmf 2.7.E36]
theorem eq_exp_combination {w : ℂ → ℂ} (hw : IsLinearODE2SolOn (fun _ => 0) (fun _ => -1) w univ) :
    ∃ A B : ℂ, ∀ z, w z = A * exp z + B * exp (-z) := by
  have hd : ∀ z, HasDerivAt w (deriv w z) z := fun z => (hw.differentiableAt z trivial).hasDerivAt
  have hdd : ∀ z, HasDerivAt (deriv w) (w z) z := fun z => by
    have := hw.hasDerivAt_deriv z trivial
    simpa using this
  -- `u = (w + w') e^{-z}` and `v = (w - w') e^{z}` are constant
  have hu : ∀ z, HasDerivAt (fun z => (w z + deriv w z) * exp (-z)) 0 z := fun z => by
    have h1 := ((hd z).add (hdd z)).mul ((hasDerivAt_neg z).cexp)
    convert h1 using 1
    simp only [Pi.add_apply]
    ring
  have hv : ∀ z, HasDerivAt (fun z => (w z - deriv w z) * exp z) 0 z := fun z => by
    have h1 := ((hd z).sub (hdd z)).mul (hasDerivAt_exp z)
    convert h1 using 1
    simp only [Pi.sub_apply]
    ring
  have cu := is_const_of_deriv_eq_zero (fun z => (hu z).differentiableAt)
    (fun z => (hu z).deriv)
  have cv := is_const_of_deriv_eq_zero (fun z => (hv z).differentiableAt)
    (fun z => (hv z).deriv)
  refine ⟨(w 0 + deriv w 0) / 2, (w 0 - deriv w 0) / 2, fun z => ?_⟩
  have e1 := cu z 0
  have e2 := cv z 0
  simp only [neg_zero, Complex.exp_zero, mul_one] at e1 e2
  have hz : exp z * exp (-z) = 1 := by rw [← Complex.exp_add]; simp
  linear_combination (exp z / 2) * e1 + (exp (-z) / 2) * e2 -
    (w z / 2 + deriv w z / 2) * hz + (deriv w z / 2 - w z / 2) * hz

/-- DLMF 2.7.35, 2.7.37: `cosh z` and `sinh z` also form a basis: every entire solution of
`w'' = w` is `w = C cosh z + D sinh z`. -/
@[dlmf 2.7.E37]
theorem eq_cosh_sinh_combination {w : ℂ → ℂ}
    (hw : IsLinearODE2SolOn (fun _ => 0) (fun _ => -1) w univ) :
    ∃ C D : ℂ, ∀ z, w z = C * cosh z + D * sinh z := by
  obtain ⟨A, B, h⟩ := eq_exp_combination hw
  refine ⟨A + B, A - B, fun z => ?_⟩
  rw [h z, Complex.cosh, Complex.sinh]
  ring

/-- DLMF 2.7.iv: `w₁ = e^z` is recessive and `w₂ = e^{-z}` dominant as `ℜz → -∞`:
`w₁/w₂ = e^{2z} → 0`; and vice versa as `ℜz → +∞`. -/
@[dlmf 2.7.iv]
theorem exp_div_exp_neg_tendsto :
    Tendsto (fun z : ℂ => exp z / exp (-z)) (comap re atBot) (𝓝 0) ∧
      Tendsto (fun z : ℂ => exp (-z) / exp z) (comap re atTop) (𝓝 0) := by
  constructor
  · have : (fun z : ℂ => exp z / exp (-z)) = fun z => exp (2 * z) := by
      funext z; rw [div_eq_iff (Complex.exp_ne_zero _), ← Complex.exp_add]; ring_nf
    rw [this, tendsto_zero_iff_norm_tendsto_zero]
    simp only [Complex.norm_exp]
    have h2 : Tendsto (fun z : ℂ => (2 * z).re) (comap re atBot) atBot := by
      simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
      exact (tendsto_comap.const_mul_atBot (by norm_num : (0 : ℝ) < 2))
    exact Real.tendsto_exp_atBot.comp h2
  · have : (fun z : ℂ => exp (-z) / exp z) = fun z => exp (-(2 * z)) := by
      funext z; rw [div_eq_iff (Complex.exp_ne_zero _), ← Complex.exp_add]; ring_nf
    rw [this, tendsto_zero_iff_norm_tendsto_zero]
    simp only [Complex.norm_exp]
    have h2 : Tendsto (fun z : ℂ => (-(2 * z)).re) (comap re atTop) atBot := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
        sub_zero]
      exact tendsto_neg_atTop_atBot.comp
        (tendsto_comap.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    exact Real.tendsto_exp_atBot.comp h2

end DLMF.AsymptoticApproximations
