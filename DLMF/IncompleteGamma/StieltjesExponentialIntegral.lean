/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.ExponentialIntegral
public import DLMF.IncompleteGamma.Representations.LowerBarnes

/-!
# Stieltjes representation on the principal cut plane

Olver, *Asymptotics and Special Functions*, Chapter 2, Exercises 3.5–3.6,
p. 43, synopsis O-2.09. The order may be any complex number of positive real part.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set

namespace DLMF.Confluent

/-- The Stieltjes representation of `E_p` extends to the entire principal cut plane.
Olver, Chapter 2, Exercises 3.5–3.6, synopsis O-2.09; integer orders give the
factorial denominator in the source. -/
theorem expIntegralE_eq_stieltjes_integral_slitPlane {p z : ℂ}
    (hp : 0 < p.re) (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => exp (-t) * (t : ℂ) ^ (p - 1) / (z + t)) (Ioi 0) ∧
      expIntegralE p z = exp (-z) / Gamma p *
        ∫ t : ℝ in Ioi 0, exp (-t) * (t : ℂ) ^ (p - 1) / (z + t) := by
  sorry

end DLMF.Confluent
