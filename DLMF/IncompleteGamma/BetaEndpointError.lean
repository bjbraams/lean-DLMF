/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.BetaEndpointBounds

/-!
# Exact endpoint bounds in the fixed-second-parameter beta expansion

Temme, *Special Functions* (1996), Chapter 11, equations (11.43)–(11.44),
pages 291–292. The approximation is assigned its exact limiting value zero at
`x=0`, so the uniform error includes both endpoints of the closed interval.
-/

@[expose] public noncomputable section

open Complex Filter Set Finset
open scoped Real Topology

namespace DLMF.Statistical

/-- The actual finite endpoint expansion, with the limiting value at zero.
Temme (11.43)–(11.44), synopsis TEM-11-13. -/
def betaEndpointApproximation (a b : ℝ) (N : ℕ) (x : ℝ) : ℂ :=
  if x = 0 then 0 else Gamma (a + b) / Gamma a *
    ∑ n ∈ range N, Real.betaGeneratingCoeff b (Real.betaXi x) n *
      betaAuxF n a b (Real.betaXi x)

/-- The defining finite approximation, including the endpoint convention. -/
theorem betaEndpointApproximation_def (a b : ℝ) (N : ℕ) (x : ℝ) :
    betaEndpointApproximation a b N x =
      if x = 0 then 0 else Gamma (a + b) / Gamma a *
        ∑ n ∈ range N, Real.betaGeneratingCoeff b (Real.betaXi x) n *
          betaAuxF n a b (Real.betaXi x) := rfl

/-- The endpoint approximation is exactly zero at the zero beta argument. -/
@[simp] theorem betaEndpointApproximation_zero (a b : ℝ) (N : ℕ) :
    betaEndpointApproximation a b N 0 = 0 := by
  simp [betaEndpointApproximation]

/-- The exact source moment bound, with the full rising-factorial constant.
Temme (11.43)–(11.44), synopsis TEM-11-13. -/
theorem norm_betaAuxF_le_pochhammer {a b ξ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hξ : 0 ≤ ξ) (N : ℕ) :
    ‖betaAuxF N a b ξ‖ ≤
      ‖DLMF.Hypergeometric.pochhammer b N‖ * a ^ (-(b + N)) := by
  sorry

/-- Every bound on the normalized `N`th derivative gives the precise finite beta error.
Taking the supremum of that derivative gives the source constant `M_N`, whose finiteness
is the existing bounded-derivative theorem for positive orders.
Temme (11.43)–(11.44), synopsis TEM-11-13. -/
theorem norm_regularizedIncompleteBeta_sub_endpointApproximation_le
    {a b x M : ℝ} {N : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hx1 : x ≤ 1) (hN : 1 ≤ N) (hM : 0 ≤ M)
    (hderiv : ∀ u : ℝ, 0 ≤ u →
      ‖iteratedDeriv N (Real.betaGeneratingKernel b) u‖ ≤ M * N.factorial) :
    ‖regularizedIncompleteBeta a b x - betaEndpointApproximation a b N x‖ ≤
      _root_.Real.Gamma (a + b) / _root_.Real.Gamma a * M *
        ‖betaAuxF N a b (Real.betaXi x)‖ := by
  sorry

/-- The absolute beta error is `O(a⁻ᴺ)` uniformly on the entire closed argument interval.
Temme (11.43)–(11.44), synopsis TEM-11-13. -/
theorem exists_betaEndpointApproximation_uniform_remainder {b : ℝ} (hb : 0 < b)
    {N : ℕ} (hN : 1 ≤ N) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ a x : ℝ, R ≤ a → 0 ≤ x → x ≤ 1 →
      ‖regularizedIncompleteBeta a b x - betaEndpointApproximation a b N x‖ ≤
        C * a ^ (-(N : ℝ)) := by
  sorry

end DLMF.Statistical
