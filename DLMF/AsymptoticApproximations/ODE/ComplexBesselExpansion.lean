/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.ComplexBesselEnvelopes
public import DLMFMathlib.Analysis.ODE.SimplePoleCoefficients
public import DLMF.Bessel.LogarithmicMonodromy
public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On

/-!
# Complex simple-pole expansions on the logarithmic cover

The independent variable is `w=log(zeta)`. The comparison functions, Green kernel,
truncation residual and adaptive-weight constants are actual expressions. A fixed
radius-ratio relaxation is allowed, with its dependence retained in the constant.
Source: Olver, *Asymptotics and Special Functions*, Chapter 12,
Theorem 9.1 and §10, pp. 458–462.
-/

@[expose] public noncomputable section

open Complex Set Filter ODE
open scoped Real Topology

namespace DLMF.AsymptoticApproximations.BesselComplexEnvelope

/-- The exact cost of relaxing radial monotonicity by a fixed ratio.
Olver, Chapter 12, §10.1, pp. 460–461. -/
def radiusWeightRatio (ν r : ℝ) : ℝ :=
  sSup {a : ℝ | ∃ z t : ℂ, 0 ≤ t.re ∧ t.re ≤ z.re ∧ z ≠ 0 ∧ t ≠ 0 ∧
    ‖t‖ ≤ r * ‖z‖ ∧ a = (weight ν t / weight ν z) ^ 2}

/-- The defining supremum over the relaxed comparison region. -/
theorem radiusWeightRatio_def (ν r : ℝ) : radiusWeightRatio ν r =
    sSup {a : ℝ | ∃ z t : ℂ, 0 ≤ t.re ∧ t.re ≤ z.re ∧ z ≠ 0 ∧ t ≠ 0 ∧
      ‖t‖ ≤ r * ‖z‖ ∧ a = (weight ν t / weight ν z) ^ 2} := rfl

/-- The actual complex simple-pole error constant; `r` measures the ratio of
`abs(zeta)`, so its square root enters the Bessel-argument ratio.
Olver, Chapter 12, §9 and §10, pp. 458–461. -/
def kernelConstant (ν r : ℝ) : ℝ :=
  2 * (1 + radiusWeightRatio ν (Real.sqrt r)) *
    sSup ((fun z : ℂ => ‖z‖ * modulus ν z ^ 2) '' {z | 0 ≤ z.re ∧ z ≠ 0})

/-- The defining supremum kernel constant. -/
theorem kernelConstant_def (ν r : ℝ) : kernelConstant ν r =
    2 * (1 + radiusWeightRatio ν (Real.sqrt r)) *
      sSup ((fun z : ℂ => ‖z‖ * modulus ν z ^ 2) '' {z | 0 ≤ z.re ∧ z ≠ 0}) := rfl

/-- The relaxed constant is finite and locally bounded in order and radius ratio.
The original monotone case has ratio one. The constant cannot remain bounded
as the allowed radius ratio tends to infinity. Olver, Chapter 12, §10, pp. 460–462. -/
theorem radiusWeightRatio_properties {ν : ℝ} (hν : 0 ≤ ν) :
    radiusWeightRatio ν 1 = 1 ∧
      (∀ r : ℝ, 1 ≤ r → 1 ≤ radiusWeightRatio ν r ∧ 0 < kernelConstant ν r) ∧
      Tendsto (radiusWeightRatio ν) atTop atTop ∧
      ∀ N R : ℝ, 0 ≤ N → 1 ≤ R → ∃ C : ℝ,
        ∀ (μ r : ℝ), μ ∈ Icc 0 N → r ∈ Icc 1 R → kernelConstant μ r ≤ C := by
  sorry

end DLMF.AsymptoticApproximations.BesselComplexEnvelope

namespace DLMF.AsymptoticApproximations.ComplexBesselComparison

/-- The two lifted square-root Bessel comparison functions, `I` or `K`.
Olver, Chapter 12, §9, p. 458. -/
def comparison (k : Fin 2) (ν : ℝ) (u w : ℂ) : ℂ :=
  exp (w / 2) * if k = 0 then DLMF.Bessel.besselIOnLog ν (log u + w / 2)
    else DLMF.Bessel.besselKOnLog ν (log u + w / 2)

/-- The defining lifted comparison function. -/
theorem comparison_def (k : Fin 2) (ν : ℝ) (u w : ℂ) : comparison k ν u w =
    exp (w / 2) * if k = 0 then DLMF.Bessel.besselIOnLog ν (log u + w / 2)
      else DLMF.Bessel.besselKOnLog ν (log u + w / 2) := rfl

/-- The consecutive-order compound companion, with the negative `K` sign.
Olver, Chapter 12, (9.02)–(9.03), p. 458. -/
def companion (k : Fin 2) (ν : ℝ) (u w : ℂ) : ℂ :=
  exp w / u * if k = 0 then DLMF.Bessel.besselIOnLog (ν + 1) (log u + w / 2)
    else -DLMF.Bessel.besselKOnLog (ν + 1) (log u + w / 2)

/-- The defining lifted companion. -/
theorem companion_def (k : Fin 2) (ν : ℝ) (u w : ℂ) : companion k ν u w =
    exp w / u * if k = 0 then DLMF.Bessel.besselIOnLog (ν + 1) (log u + w / 2)
      else -DLMF.Bessel.besselKOnLog (ν + 1) (log u + w / 2) := rfl

/-- The exact Green kernel in the `zeta` variable; its Wronskian is `-1/2`.
Olver, Chapter 12, §9, p. 459. -/
def greenKernel (ν : ℝ) (u w v : ℂ) : ℂ :=
  -2 * (comparison 0 ν u v * comparison 1 ν u w -
    comparison 1 ν u v * comparison 0 ν u w)

/-- The defining square-root Bessel Green kernel. -/
theorem greenKernel_def (ν : ℝ) (u w v : ℂ) : greenKernel ν u w v =
    -2 * (comparison 0 ν u v * comparison 1 ν u w -
      comparison 1 ν u v * comparison 0 ν u w) := rfl

/-- The actual finite compound expression on the logarithmic cover. -/
def partialSum (A B : ℕ → ℂ → ℂ) (k : Fin 2) (ν : ℝ) (u : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  simplePolePartialSum (fun s t => A s (exp t)) (fun s t => B s (exp t))
    (comparison k ν u) (companion k ν u) u n w

/-- The defining lifted finite compound sum. -/
theorem partialSum_def (A B : ℕ → ℂ → ℂ) (k : Fin 2) (ν : ℝ)
    (u : ℂ) (n : ℕ) (w : ℂ) : partialSum A B k ν u n w =
    simplePolePartialSum (fun s t => A s (exp t)) (fun s t => B s (exp t))
      (comparison k ν u) (companion k ν u) u n w := rfl

/-- The exact positive envelope on the nonzero physical right half-plane. -/
def envelope (k : Fin 2) (ν : ℝ) (u w : ℂ) : ℝ :=
  ‖exp (w / 2)‖ * BesselComplexEnvelope.modulus ν (u * exp (w / 2)) *
    if k = 0 then BesselComplexEnvelope.weight ν (u * exp (w / 2))
    else (BesselComplexEnvelope.weight ν (u * exp (w / 2)))⁻¹

/-- The defining adaptive comparison envelope. -/
theorem envelope_def (k : Fin 2) (ν : ℝ) (u w : ℂ) : envelope k ν u w =
    ‖exp (w / 2)‖ * BesselComplexEnvelope.modulus ν (u * exp (w / 2)) *
      if k = 0 then BesselComplexEnvelope.weight ν (u * exp (w / 2))
      else (BesselComplexEnvelope.weight ν (u * exp (w / 2)))⁻¹ := rfl

/-- The explicit derivative-kernel majorant after inserting the known
function-error bound into the Volterra equation. Prefix variations are used, so
there is no unknown error under this integral. `k=0` uses an origin tail and
`k=1` a finite initial point. Olver, Chapter12 §9 and Chapter6 §10. -/
def derivativeMajorant (ψ : ℂ → ℂ) (B : ℕ → ℂ → ℂ)
    (k : Fin 2) (ν : ℝ) (u : ℂ) (r : ℝ) (n : ℕ) (γ : ℝ → ℂ) : ℝ :=
  let F := fun s t => exp (γ t / 2) * B s (exp (γ t))
  let V := fun s t => (eVariationOn (F s) (if k = 0 then Ioc 0 t else Icc 0 t)).toReal
  let c := BesselComplexEnvelope.kernelConstant ν r
  ∫ t : ℝ in 0..1, ‖deriv (fun w => greenKernel ν u w (γ t)) (γ 1) / exp (γ 1)‖ *
    (‖ψ (exp (γ t))‖ * envelope k ν u (γ t) * c * Real.exp (c * V 0 t / ‖u‖) *
      V n t / ‖u‖ ^ (2 * n + 1) * ‖deriv γ t‖ +
      ‖if k = 0 then DLMF.Bessel.besselIOnLog ν (log u + γ t / 2)
        else DLMF.Bessel.besselKOnLog ν (log u + γ t / 2)‖ *
          ‖deriv (F n) t‖ / ‖u‖ ^ (2 * n))

/-- The defining differentiated-kernel integral bound. -/
theorem derivativeMajorant_def (ψ : ℂ → ℂ) (B : ℕ → ℂ → ℂ)
    (k : Fin 2) (ν : ℝ) (u : ℂ) (r : ℝ) (n : ℕ) (γ : ℝ → ℂ) :
    derivativeMajorant ψ B k ν u r n γ =
      let F := fun s t => exp (γ t / 2) * B s (exp (γ t))
      let V := fun s t => (eVariationOn (F s) (if k = 0 then Ioc 0 t else Icc 0 t)).toReal
      let c := BesselComplexEnvelope.kernelConstant ν r
      ∫ t : ℝ in 0..1, ‖deriv (fun w => greenKernel ν u w (γ t)) (γ 1) / exp (γ 1)‖ *
        (‖ψ (exp (γ t))‖ * envelope k ν u (γ t) * c * Real.exp (c * V 0 t / ‖u‖) *
          V n t / ‖u‖ ^ (2 * n + 1) * ‖deriv γ t‖ +
          ‖if k = 0 then DLMF.Bessel.besselIOnLog ν (log u + γ t / 2)
            else DLMF.Bessel.besselKOnLog ν (log u + γ t / 2)‖ *
              ‖deriv (F n) t‖ / ‖u‖ ^ (2 * n)) := rfl

/-- Exact differential equation, Wronskian and finite residual on the cover.
No analyticity through the puncture is asserted for nonintegral order.
Olver, Chapter 12, §9, pp. 458–459. -/
theorem comparison_and_partialSum_equations {D : Set ℂ} (hD : IsOpen D)
    {ψ : ℂ → ℂ} {A B : ℕ → ℂ → ℂ} {ν : ℝ} {u : ℂ} (hu : u ≠ 0)
    (hseq : IsSimplePoleCoefficientSequence ψ ν A B D) (n : ℕ) {w : ℂ} (hw : exp w ∈ D) :
    (comparison 0 ν u w * deriv (comparison 1 ν u) w -
      deriv (comparison 0 ν u) w * comparison 1 ν u w) = -exp w / 2 ∧
      ∀ k : Fin 2,
        deriv (deriv (partialSum A B k ν u n)) w - deriv (partialSum A B k ν u n) w -
          (u ^ 2 * exp w / 4 + ((ν : ℂ) ^ 2 - 1) / 4 + exp w * ψ (exp w)) *
            partialSum A B k ν u n w =
          -exp w * comparison k ν u w *
            (2 * exp w * deriv (B n) (exp w) + B n (exp w)) / (2 * u ^ (2 * n)) := by
  sorry

/-- A finite-reference `K`-type exact solution has the complete adaptive-weight
variation estimate on every progressive path, including a fixed radius-ratio
relaxation. Its derivative is given by differentiating the displayed Green
integral, which supplies an explicit integral majorant as well.
Olver, Chapter 12, Theorem 9.1 and §10, pp. 458–462. -/
theorem exists_complex_simplePole_K_expansion
    {D : Set ℂ} (hD : IsOpen D) (hstar : StarConvex ℝ 0 D) (hzero : 0 ∈ D)
    {ψ : ℂ → ℂ} {A B : ℕ → ℂ → ℂ} {ν : ℝ} (hν : 0 ≤ ν)
    {u a : ℂ} (hu : u ≠ 0) (ha : exp a ∈ D)
    (hseq : IsSimplePoleCoefficientSequence ψ ν A B D) (n : ℕ) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε {w | exp w ∈ D} ∧ ε a = 0 ∧ deriv ε a = 0 ∧
      (∀ w : ℂ, exp w ∈ D →
        let W := fun t => partialSum A B 1 ν u n t + ε t
        deriv (deriv W) w - deriv W w =
          (u ^ 2 * exp w / 4 + ((ν : ℂ) ^ 2 - 1) / 4 + exp w * ψ (exp w)) * W w) ∧
      ∀ {r : ℝ}, 1 ≤ r → ∀ γ : ℝ → ℂ,
        TauCeti.IsPiecewiseC1On γ 0 1 → γ 0 = a → (∀ t ∈ Icc (0 : ℝ) 1, exp (γ t) ∈ D) →
        (∀ t ∈ Icc (0 : ℝ) 1, |(log u + γ t / 2).im| ≤ Real.pi / 2) →
        AntitoneOn (fun t => (u * exp (γ t / 2)).re) (Icc 0 1) →
        (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc s 1, ‖exp (γ t)‖ ≤ r * ‖exp (γ s)‖) →
        (∀ s ∈ ({0, n} : Set ℕ), BoundedVariationOn
          (fun t => exp (γ t / 2) * B s (exp (γ t))) (Icc 0 1)) →
        let F := fun s t => exp (γ t / 2) * B s (exp (γ t))
        let V := fun s => (eVariationOn (F s) (Icc 0 1)).toReal
        let c := BesselComplexEnvelope.kernelConstant ν r
        let L := partialSum A B 1 ν u n
        let residual := fun w => (deriv (deriv L) w - deriv L w -
          (u ^ 2 * exp w / 4 + ((ν : ℂ) ^ 2 - 1) / 4 + exp w * ψ (exp w)) * L w) /
            exp (2 * w)
        ‖ε (γ 1)‖ ≤ envelope 1 ν u (γ 1) * c * Real.exp (c * V 0 / ‖u‖) *
          V n / ‖u‖ ^ (2 * n + 1) ∧
        ε (γ 1) = ∫ t : ℝ in 0..1, greenKernel ν u (γ 1) (γ t) *
          (ψ (exp (γ t)) * ε (γ t) / exp (γ t) - residual (γ t)) *
            exp (γ t) * deriv γ t ∧
        deriv ε (γ 1) / exp (γ 1) = ∫ t : ℝ in 0..1,
          deriv (fun w => greenKernel ν u w (γ t)) (γ 1) / exp (γ 1) *
            (ψ (exp (γ t)) * ε (γ t) / exp (γ t) - residual (γ t)) *
              exp (γ t) * deriv γ t ∧
        ‖deriv ε (γ 1) / exp (γ 1)‖ ≤ derivativeMajorant ψ B 1 ν u r n γ := by
  sorry

/-- The `I`-type solution is normalized at the puncture. The complete weight
bound holds along progressive origin paths on the cover, with the same finite
radius-ratio cost. On other sheets the exact `I` monodromy continues the result.
Olver, Chapter 12, Theorem 9.1 and §10.3, pp. 458–462. -/
theorem exists_complex_simplePole_I_expansion
    {D : Set ℂ} (hD : IsOpen D) (hstar : StarConvex ℝ 0 D) (hzero : 0 ∈ D)
    {ψ : ℂ → ℂ} {A B : ℕ → ℂ → ℂ} {ν : ℝ} (hν : 0 ≤ ν)
    {u : ℂ} (hu : u ≠ 0) (hseq : IsSimplePoleCoefficientSequence ψ ν A B D) (n : ℕ) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε {w | exp w ∈ D} ∧
      (∀ w : ℂ, exp w ∈ D →
        let W := fun t => partialSum A B 0 ν u n t + ε t
        deriv (deriv W) w - deriv W w =
          (u ^ 2 * exp w / 4 + ((ν : ℂ) ^ 2 - 1) / 4 + exp w * ψ (exp w)) * W w) ∧
      ∀ {r : ℝ}, 1 ≤ r → ∀ γ : ℝ → ℂ, ContinuousOn γ (Ioc 0 1) →
        (∀ s : ℝ, 0 < s → s < 1 → TauCeti.IsPiecewiseC1On γ s 1) →
        (∀ t ∈ Ioc (0 : ℝ) 1, exp (γ t) ∈ D) →
        Tendsto (fun t => (γ t).re) (𝓝[>] 0) atBot →
        (∃ b : ℝ, Tendsto (fun t => (γ t).im) (𝓝[>] 0) (𝓝 b)) →
        (∀ t ∈ Ioc (0 : ℝ) 1, |(log u + γ t / 2).im| ≤ Real.pi / 2) →
        MonotoneOn (fun t => (u * exp (γ t / 2)).re) (Ioc 0 1) →
        (∀ s ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc s 1, ‖exp (γ s)‖ ≤ r * ‖exp (γ t)‖) →
        (∀ s ∈ ({0, n} : Set ℕ), BoundedVariationOn
          (fun t => exp (γ t / 2) * B s (exp (γ t))) (Ioc 0 1)) →
        let V := fun s => (eVariationOn
          (fun t => exp (γ t / 2) * B s (exp (γ t))) (Ioc 0 1)).toReal
        let c := BesselComplexEnvelope.kernelConstant ν r
        Tendsto (fun t => ε (γ t) / comparison 0 ν u (γ t)) (𝓝[>] 0) (𝓝 0) ∧
        ‖ε (γ 1)‖ ≤ envelope 0 ν u (γ 1) * c * Real.exp (c * V 0 / ‖u‖) *
          V n / ‖u‖ ^ (2 * n + 1) ∧
        ‖deriv ε (γ 1) / exp (γ 1)‖ ≤ derivativeMajorant ψ B 0 ν u r n γ := by
  sorry

/-- A convergent recessive infinity tail also supplies a `K` reference. All later
paths retain that same tail germ, so changing the sheet at infinity is not
silently treated as the same solution. The full prefix variations include the
infinite endpoint. Olver, Chapter12 Theorem9.1 and §10, pp. 458–462. -/
theorem exists_complex_simplePole_K_endpoint_expansion
    {D : Set ℂ} (hD : IsOpen D) (hstar : StarConvex ℝ 0 D) (hzero : 0 ∈ D)
    {ψ : ℂ → ℂ} {A B : ℕ → ℂ → ℂ} {ν : ℝ} (hν : 0 ≤ ν)
    {u : ℂ} (hu : u ≠ 0) (hseq : IsSimplePoleCoefficientSequence ψ ν A B D) (n : ℕ)
    (tail : ℝ → ℂ) (htail : ContinuousOn tail (Ioc 0 1))
    (hregular : ∀ s : ℝ, 0 < s → s < 1 → TauCeti.IsPiecewiseC1On tail s 1)
    (himage : ∀ t ∈ Ioc (0 : ℝ) 1, exp (tail t) ∈ D)
    (hargument : ∀ t ∈ Ioc (0 : ℝ) 1, |(log u + tail t / 2).im| ≤ Real.pi / 2)
    (hinfinity : Tendsto (fun t => (u * exp (tail t / 2)).re) (𝓝[>] 0) atTop)
    (hprogressive : AntitoneOn (fun t => (u * exp (tail t / 2)).re) (Ioc 0 1))
    (hradial : ∀ s ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc s 1,
      ‖exp (tail t)‖ ≤ ‖exp (tail s)‖)
    (hvariation : ∀ s ∈ ({0, n} : Set ℕ), BoundedVariationOn
      (fun t => exp (tail t / 2) * B s (exp (tail t))) (Ioc 0 1)) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε {w | exp w ∈ D} ∧
      (∀ w : ℂ, exp w ∈ D →
        let W := fun t => partialSum A B 1 ν u n t + ε t
        deriv (deriv W) w - deriv W w =
          (u ^ 2 * exp w / 4 + ((ν : ℂ) ^ 2 - 1) / 4 + exp w * ψ (exp w)) * W w) ∧
      Tendsto (fun t => ε (tail t) / comparison 1 ν u (tail t)) (𝓝[>] 0) (𝓝 0) ∧
      ∀ {r : ℝ}, 1 ≤ r → ∀ γ : ℝ → ℂ, γ =ᶠ[𝓝[>] 0] tail →
        ContinuousOn γ (Ioc 0 1) →
        (∀ s : ℝ, 0 < s → s < 1 → TauCeti.IsPiecewiseC1On γ s 1) →
        (∀ t ∈ Ioc (0 : ℝ) 1, exp (γ t) ∈ D) →
        (∀ t ∈ Ioc (0 : ℝ) 1, |(log u + γ t / 2).im| ≤ Real.pi / 2) →
        AntitoneOn (fun t => (u * exp (γ t / 2)).re) (Ioc 0 1) →
        (∀ s ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc s 1, ‖exp (γ t)‖ ≤ r * ‖exp (γ s)‖) →
        (∀ s ∈ ({0, n} : Set ℕ), BoundedVariationOn
          (fun t => exp (γ t / 2) * B s (exp (γ t))) (Ioc 0 1)) →
        let V := fun s => (eVariationOn
          (fun t => exp (γ t / 2) * B s (exp (γ t))) (Ioc 0 1)).toReal
        let c := BesselComplexEnvelope.kernelConstant ν r
        ‖ε (γ 1)‖ ≤ envelope 1 ν u (γ 1) * c * Real.exp (c * V 0 / ‖u‖) *
          V n / ‖u‖ ^ (2 * n + 1) ∧
        ‖deriv ε (γ 1) / exp (γ 1)‖ ≤ derivativeMajorant ψ B 1 ν u r n γ := by
  sorry

end DLMF.AsymptoticApproximations.ComplexBesselComparison
