/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Connections.SimplePole
public import DLMFMathlib.Analysis.ODE.SimplePoleScaling

/-!
# Frobenius normalization in a large-parameter simple-pole equation

Olver, *Asymptotics and Special Functions*, Chapter 13, §§5–6,
pp. 487–491, synopsis O-13.03. The canonical solution is an actual
dilation of the unit-parameter Frobenius series, with its positive-real
parameter power and chosen residue logarithm explicit.
-/

@[expose] public noncomputable section
open Complex Filter Set
open scoped Topology
namespace DLMF.AsymptoticApproximations.SimplePoleConnection

/-- The large-parameter recessive solution normalized like sqrt(zeta)*I_nu.
The logarithmic argument fixes the sheet; u is positive in all theorems. -/
def parameterRecessive (ν : ℝ) (ψ : ℂ → ℂ) (u : ℝ) (w : ℂ) : ℂ :=
  (u : ℂ)⁻¹ * recessive ν (ODE.SimplePoleScaling.perturbation ψ u)
    (w + 2 * Real.log u)

/-- The defining dilation of the actual Frobenius series. -/
theorem parameterRecessive_def (ν : ℝ) (ψ : ℂ → ℂ) (u : ℝ) (w : ℂ) :
    parameterRecessive ν ψ u w = (u : ℂ)⁻¹ *
      recessive ν (ODE.SimplePoleScaling.perturbation ψ u) (w + 2 * Real.log u) := rfl

/-- The canonical large-parameter solution has exactly the normalized leading
Frobenius coefficient, on every fixed logarithmic ray. Olver, Chapter 13, §5. -/
theorem tendsto_parameterRecessive_frobenius {ν R u : ℝ} (hν : 0 ≤ ν)
    (hR : 0 < R) (hu : 0 < u) {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (Metric.ball 0 R)) (θ : ℝ) :
    Tendsto (fun x : ℝ => parameterRecessive ν ψ u (x + I * θ) /
      exp (((1 + (ν : ℂ)) / 2) * (x + I * θ))) atBot
        (𝓝 (((u / 2) ^ ν : ℝ) / Gamma ((ν : ℂ) + 1))) := by
  sorry

/-- Pulling the solution back with a chosen analytic coordinate and amplitude
retains the exact residue-logarithm normalization multiplier.
Olver, Chapter 13, §5, pp. 487–489. Here ell fixes log(4*F(z0)); the
local coordinate logarithm is supplied explicitly, so no principal-branch
substitution crosses the intrinsic cut. -/
theorem tendsto_physical_frobenius_normalizer
    {ν R u : ℝ} (hν : 0 ≤ ν) (hR : 0 < R) (hu : 0 < u) {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (Metric.ball 0 R))
    {ℓ : ℂ} {L amplitude : ℝ → ℂ}
    (hLlimit : Tendsto (fun x : ℝ => L x - (x : ℂ)) atBot (𝓝 ℓ))
    (hamp : Tendsto amplitude atBot (𝓝 (exp (-ℓ / 2)))) :
    Tendsto (fun x : ℝ => amplitude x * parameterRecessive ν ψ u (L x) /
      exp (((1 + (ν : ℂ)) / 2) * x)) atBot
        (𝓝 (exp ((ν : ℂ) * ℓ / 2) * ((u / 2) ^ ν : ℝ) /
          Gamma ((ν : ℂ) + 1))) := by
  sorry

end DLMF.AsymptoticApproximations.SimplePoleConnection
