/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Properties
public import DLMF.Core.Framework

/-!
# Conventions for the DLMF Airy acquisition

Oscillatory integrals are stated as limits of finite integrals, not as totalized Bochner
integrals. Complex powers of the Bessel argument use an explicit logarithmic coordinate,
so that the substitution `ζ = 2 z^(3/2)/3` retains its analytically continued branch.
The sector filter contains the whole closed sector, hence Big-O statements are uniform
there. These conventions support DLMF §§9.2 and 9.4–9.14. Improper convergence and
straight-segment primitives use the canonical definitions in `DLMF.Core.Framework`.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory DLMF.Hypergeometric
open scoped Real Topology
namespace DLMF.Airy

/-- Ai restricted to the real axis. -/
def airyAiReal (x : ℝ) : ℝ := (airyAi x).re
/-- Bi restricted to the real axis. -/
def airyBiReal (x : ℝ) : ℝ := (airyBi x).re
/-- Ai' restricted to the real axis. -/
def airyAiDerivReal (x : ℝ) : ℝ := (airyAiDeriv x).re
/-- Bi' restricted to the real axis. -/
def airyBiDerivReal (x : ℝ) : ℝ := (airyBiDeriv x).re

/-- The totalized value of an improper integral with infinite lower endpoint. -/
def improperAtBot (f : ℝ → ℂ) (b : ℝ) : ℂ :=
  limUnder atBot (fun R : ℝ => ∫ t in R..b, f t)

/-- An oriented ray integral with its Jacobian, starting at radius `r`. -/
def rayIntegral (f : ℂ → ℂ) (θ r : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi r, exp (θ * I) * f ((t : ℂ) * exp (θ * I))
/-- A unit-circle arc, with its oriented tangent. -/
def arcIntegral (f : ℂ → ℂ) (α β : ℝ) : ℂ :=
  ∫ θ : ℝ in α..β, I * exp (θ * I) * f (exp (θ * I))
/-- A contour from infinity at angle `α` to infinity at angle `β`, avoiding zero at radius one. -/
def contourIntegral (f : ℂ → ℂ) (α β : ℝ) : ℂ :=
  -rayIntegral f α 1 + arcIntegral f α β + rayIntegral f β 1
/-- Symmetric Cauchy principal value on the positive half-line at the interior pole `a`. -/
def principalValueIoi (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ε =>
    (∫ t in (0 : ℝ)..(a - ε), f t) + improperAtTop f (a + ε))

/-- Existence of the tail integrals and of the symmetric principal-value limit. -/
def HasPrincipalValueIoi (f : ℝ → ℂ) (a : ℝ) (v : ℂ) : Prop :=
  (∀ ε : ℝ, 0 < ε → HasIntegralAtTop f (a + ε) (improperAtTop f (a + ε))) ∧
    Tendsto (fun ε : ℝ => (∫ t in (0 : ℝ)..(a - ε), f t) +
      improperAtTop f (a + ε)) (𝓝[>] (0 : ℝ)) (𝓝 v)

/-- Principal Airy change of variable. -/
@[dlmf 9.6.E1, dlmf 9.7.E1]
def airyZetaComplex (z : ℂ) : ℂ := 2 / 3 * z ^ (3 / 2 : ℂ)
/-- The logarithm of ζ inherited from the logarithm of z, before reduction modulo `2πi`. -/
def airyLogZeta (z : ℂ) : ℂ := log (2 / 3 : ℂ) + 3 / 2 * log z
/-- Uniform approach to infinity in a closed sector of half-angle `α`. -/
def airySector (α : ℝ) : Filter ℂ :=
  comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z : ℂ | z ≠ 0 ∧ |arg z| ≤ α}

/-- The modified Bessel I function on its logarithmic argument plane. -/
def airyBesselIOnLog (ν w : ℂ) : ℂ :=
  exp (ν * (w - log 2)) * regularizedHGFun ∅ {ν + 1} (exp (2 * w) / 4)
/-- The Bessel J function on its logarithmic argument plane. -/
def airyBesselJOnLog (ν w : ℂ) : ℂ :=
  exp (ν * (w - log 2)) * regularizedHGFun ∅ {ν + 1} (-exp (2 * w) / 4)
/-- Nonintegral-order K on the logarithmic plane; all orders in §9.6 are nonintegral. -/
def airyBesselKOnLog (ν w : ℂ) : ℂ :=
  π / (2 * sin (π * ν)) * (airyBesselIOnLog (-ν) w - airyBesselIOnLog ν w)
/-- Nonintegral-order Y on the logarithmic plane. -/
def airyBesselYOnLog (ν w : ℂ) : ℂ :=
  (cos (π * ν) * airyBesselJOnLog ν w - airyBesselJOnLog (-ν) w) / sin (π * ν)
/-- Hankel H1 on the logarithmic plane, at nonintegral order. -/
def airyHankel1OnLog (ν w : ℂ) : ℂ := airyBesselJOnLog ν w + I * airyBesselYOnLog ν w
/-- Hankel H2 on the logarithmic plane, at nonintegral order. -/
def airyHankel2OnLog (ν w : ℂ) : ℂ := airyBesselJOnLog ν w - I * airyBesselYOnLog ν w

/-- Upper incomplete Gamma continued on the logarithmic plane, including integral parameters.
The added segment integrates its entire logarithmic derivative, without subtracting Gamma poles. -/
def airyUpperGammaOnLog (s w : ℂ) : ℂ :=
  DLMF.Confluent.upperIncGamma s (exp w) -
    segmentIntegral (fun u => exp (s * u - exp u)) (log (exp w)) w

/-- A basis is uniformly separated in its value/derivative matrix after column normalization.
This quantitative version of numerical independence also accommodates oscillatory pairs. -/
def IsWellConditionedPairOn (f g : ℂ → ℂ) (s : Set ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z ∈ s,
    ‖f z‖ * ‖deriv g z‖ + ‖deriv f z‖ * ‖g z‖ ≤
      C * ‖f z * deriv g z - deriv f z * g z‖

end DLMF.Airy
