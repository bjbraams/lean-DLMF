/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.LocalTheory
public import DLMFMathlib.Analysis.ODE.EndpointBasis

/-!
# The satisfactory principal Legendre pair and full complex endpoint limits

Olver, *Asymptotics and Special Functions*, Chapter 5, Theorem 12.1,
pp. 171–174, synopsis O-5.19. Scaled limits retain reciprocal-Gamma zeros
at exceptional leading coefficients; an equivalent with a zero leading term
is not asserted. The approach at infinity retains the principal cut.
-/

@[expose] public noncomputable section

open Complex Filter Asymptotics Bornology
open scoped Real Topology

namespace DLMF.Legendre

/-- The principal P endpoint normalization as a full complex cut-plane limit, including
zero reciprocal-Gamma coefficients. Olver, Theorem 12.1, synopsis O-5.19. -/
theorem tendsto_associatedP_neg_order_scaled_one (ν μ : ℂ) :
    Tendsto (fun z : ℂ => associatedP ν (-μ) z /
      exp (μ / 2 * log ((z - 1) / 2)))
      (𝓝[{z : ℂ | z - 1 ∈ slitPlane}] 1) (𝓝 ((Gamma (μ + 1))⁻¹)) := by
  sorry

/-- The normalized Q coefficient at infinity on the full principal cut, with its possible
reciprocal-Gamma zero. Olver, Theorem 12.1, synopsis O-5.19. -/
theorem tendsto_olverQ_scaled_cobounded (ν μ : ℂ) :
    Tendsto (fun z : ℂ => olverQ ν μ z / z ^ (-ν - 1))
      (cobounded ℂ ⊓ 𝓟 {z : ℂ | z - 1 ∈ slitPlane})
      (𝓝 ((Real.sqrt π : ℂ) / ((2 : ℂ) ^ (ν + 1) * Gamma (ν + 3 / 2)))) := by
  sorry

/-- The repeated-order endpoint logarithm, including vanishing leading coefficients.
Olver, Theorem 12.1, pp. 171–174, synopsis O-5.19. -/
theorem tendsto_olverQ_zero_order_div_log_one (ν : ℂ) :
    Tendsto (fun z : ℂ => olverQ ν 0 z / log (z - 1))
      (𝓝[{z : ℂ | z - 1 ∈ slitPlane}] 1) (𝓝 (-(2 * Gamma (ν + 1))⁻¹)) := by
  sorry

/-- The principal P/Q pair is satisfactory for both endpoints throughout the source's
right-half-plane parameter range. The span is the full solution space by its nonzero
Wronskian and the ordinary connected-domain uniqueness theorem.
Olver, Chapter 5, Theorem 12.1, pp. 171–174, synopsis O-5.19. -/
theorem isNumericallySatisfactoryPair_associatedP_olverQ {ν μ : ℂ}
    (hν : -1 / 2 ≤ ν.re) (hμ : 0 ≤ μ.re) :
    let U := {z : ℂ | z - 1 ∈ slitPlane ∧ 0 < z.re}
    let f : U → ℂ := fun z => associatedP ν (-μ) z
    let g : U → ℂ := fun z => olverQ ν μ z
    let V := Submodule.span ℂ ({f, g} : Set (U → ℂ))
    let approach : Fin 2 → Filter U :=
      ![comap (fun z : U => (z : ℂ)) (𝓝 (1 : ℂ)),
        comap (fun z : U => (z : ℂ)) (cobounded ℂ)]
    ODE.IsNumericallySatisfactoryPair V approach f g := by
  sorry

end DLMF.Legendre
