/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.RamifiedPowerSeries

/-!
# Positive coefficients of a product of real binomial powers

Andrews, Askey and Roy, *Special Functions*, Lemma 7.6.3,
p. 389, synopsis AAR-7.4.1–7.6.4. The two factors use the canonical
formal binomial power at positive constant coefficient one.
-/

@[expose] public noncomputable section

namespace PowerSeries

/-- Every coefficient of `(1-r)^(-2*nu)*(1-2*x*r+r^2)^(-nu)` is nonnegative.
Andrews–Askey–Roy, Lemma 7.6.3, synopsis AAR-7.4.1–7.6.4. -/
theorem coeff_realPower_one_sub_mul_quadratic_nonneg {ν x : ℝ} (hν : 0 < ν)
    (hx : x ∈ Set.Icc (-1) 1) (n : ℕ) :
    0 ≤ coeff n (realPower (1 - X : ℝ⟦X⟧) (-2 * ν) *
      realPower (1 - C (2 * x) * X + X ^ 2 : ℝ⟦X⟧) (-ν)) := by
  sorry

end PowerSeries
