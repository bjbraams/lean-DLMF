/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.StieltjesRemainder

/-!
# Periodic-Bernoulli-only form of Stirling's exact remainder

Andrews, Askey and Roy, *Special Functions*, Theorem D.3.2,
p. 622 (synopsis AAR-D.2.1–D.3.2), compared with Theorem 1.4.2,
p. 20 (synopsis AAR-1.4.1–1.4.5). The last Bernoulli term is separated explicitly.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Finset

namespace DLMF.Gamma

/-- Stirling's exact periodic-Bernoulli integral after the first `m` Bernoulli terms.
Andrews–Askey–Roy, Theorem D.3.2, p. 622, synopsis AAR-D.2.1–D.3.2. The logarithm is the
analytic `logGamma` real on the positive axis, rather than the logarithm of a Gamma value. -/
theorem logGamma_eq_sum_sub_periodicBernoulli_integral {m : ℕ} (hm : 1 ≤ m)
    {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => (periodicBernoulli (2 * m) t : ℂ) /
      ((t : ℂ) + z) ^ (2 * m)) (Set.Ioi 0) ∧
    TauCeti.logGamma z = (z - 1 / 2) * log z - z + (Real.log (2 * Real.pi) / 2 : ℝ) +
      (∑ k ∈ Finset.Icc 1 m, (bernoulli (2 * k) : ℂ) /
        ((2 * k : ℂ) * (2 * k - 1) * z ^ (2 * k - 1))) -
      (2 * m : ℂ)⁻¹ * ∫ t in Set.Ioi (0 : ℝ),
        (periodicBernoulli (2 * m) t : ℂ) / ((t : ℂ) + z) ^ (2 * m) := by
  sorry

end DLMF.Gamma
