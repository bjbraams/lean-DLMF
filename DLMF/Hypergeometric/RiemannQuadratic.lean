/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Riemann

/-!
# The quadratic pullback of Riemann's equation

Andrews, Askey and Roy, *Special Functions*, Theorem 3.9.1. The substitution
x=t² followed by u=(1+t)/2 places the two finite singularities at u=0,1.
Local inverse branches avoid u=1/2, where x=0 is a branch value.
-/

@[expose] public section

open scoped Classical

namespace DLMF.Hypergeometric

/-- Quadratic pullback identifies the two local Riemann solution equations.
Andrews–Askey–Roy, *Special Functions*, Theorem 3.9.1
(synopsis AAR-3.9.1). The exponent 1/2 at the branch value becomes ordinary,
while the exponents at infinity double. -/
theorem riemannNormalOperator_quadratic_iff (b₁ b₂ c₁ c₂ : ℂ)
    (hfuchs : 1 / 2 + c₁ + c₂ + b₁ + b₂ = 1)
    (f : ℂ → ℂ) {u : ℂ} (hu₀ : u ≠ 0) (hu₁ : u ≠ 1) (humid : u ≠ 1 / 2)
    (hf : ContDiffAt ℂ 2 f ((2 * u - 1) ^ 2)) :
    riemannNormalOperator 0 (1 / 2) b₁ b₂ c₁ c₂ f ((2 * u - 1) ^ 2) = 0 ↔
      riemannNormalOperator b₁ b₂ b₁ b₂ (2 * c₁) (2 * c₂)
        (fun v : ℂ => f ((2 * v - 1) ^ 2)) u = 0 := by
  sorry

/-- The coefficients of the transformed equation are analytic at the former branch point.
Andrews–Askey–Roy, *Special Functions*, Theorem 3.9.1
(synopsis AAR-3.9.1). -/
theorem analyticAt_riemannQuadratic_coefficients (b₁ b₂ c₁ c₂ : ℂ) :
    AnalyticAt ℂ (fun u : ℂ =>
      (1 - b₁ - b₂) / u + (1 - b₁ - b₂) / (u - 1)) (1 / 2) ∧
    AnalyticAt ℂ (fun u : ℂ =>
      (b₁ * b₂ / u + b₁ * b₂ / (1 - u) - (2 * c₁) * (2 * c₂)) /
        (u * (1 - u))) (1 / 2) := by
  constructor <;> fun_prop (disch := norm_num)


/-- A chosen analytic square-root branch gives a linear equivalence of the two local
Riemann solution spaces. Andrews–Askey–Roy, *Special Functions*, Theorem 3.9.1,
pp. 160–162 (synopsis AAR-3.9.1). The map is the actual quadratic pullback;
zero extension outside the open domains removes irrelevant function values. -/
theorem exists_linearMap_bijOn_riemannNormalSolutions_quadratic
    (b₁ b₂ c₁ c₂ : ℂ) (hfuchs : 1 / 2 + c₁ + c₂ + b₁ + b₂ = 1)
    (V : Set ℂ) (hV : IsOpen V) (hregular : ∀ z ∈ V, z ≠ 0 ∧ z ≠ 1)
    (σ : ℂ → ℂ) (hσ : AnalyticOnNhd ℂ σ V) (hsquare : ∀ z ∈ V, σ z ^ 2 = z) :
    let U := (fun z : ℂ => (1 + σ z) / 2) '' V
    ∃ L : (ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ),
      (∀ f u, L f u = U.indicator (fun v => f ((2 * v - 1) ^ 2)) u) ∧
      Set.BijOn L
        {f | ContDiffOn ℂ 2 f V ∧
          (∀ z ∈ V, riemannNormalOperator 0 (1 / 2) b₁ b₂ c₁ c₂ f z = 0) ∧
          ∀ z, z ∉ V → f z = 0}
        {g | ContDiffOn ℂ 2 g U ∧
          (∀ u ∈ U, riemannNormalOperator b₁ b₂ b₁ b₂ (2 * c₁) (2 * c₂) g u = 0) ∧
          ∀ u, u ∉ U → g u = 0} := by
  sorry

/-- Every local solution at the exponent pair `0,1/2` pulls back to an analytic solution
through the former quadratic branch point. Andrews–Askey–Roy, *Special Functions*,
Theorem 3.9.1, pp. 160–162 (synopsis AAR-3.9.1). The positive-real-part
half-neighborhood chooses the principal square-root sheet before continuation. -/
theorem exists_analytic_quadratic_pullback (b₁ b₂ c₁ c₂ : ℂ)
    (hfuchs : 1 / 2 + c₁ + c₂ + b₁ + b₂ = 1)
    {r : ℝ} (hr : 0 < r) (hrone : r < 1) (f : ℂ → ℂ)
    (hf : ContDiffOn ℂ 2 f (Metric.ball 0 r ∩ Complex.slitPlane))
    (heq : ∀ z ∈ Metric.ball 0 r ∩ Complex.slitPlane,
      riemannNormalOperator 0 (1 / 2) b₁ b₂ c₁ c₂ f z = 0) :
    ∃ ε > 0, ∃ G : ℂ → ℂ,
      AnalyticOnNhd ℂ G (Metric.ball (1 / 2) ε) ∧
      (∀ u ∈ Metric.ball (1 / 2) ε, 0 < (2 * u - 1).re →
        G u = f ((2 * u - 1) ^ 2)) ∧
      ∀ u ∈ Metric.ball (1 / 2) ε,
        riemannNormalOperator b₁ b₂ b₁ b₂ (2 * c₁) (2 * c₂) G u = 0 := by
  sorry

end DLMF.Hypergeometric
