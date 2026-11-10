/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.Basic.Properties
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Inverse error functions (DLMF 7.17.1)

## Main definitions

* `Real.invErf`, `Real.invErfc`: the inverse error functions on `(-1, 1)` and `(0, 2)`
  (DLMF 7.17.1), totalized by `0` outside these intervals.

## Main results

* `Real.invErf_spec`, `Real.invErfc_spec`: the inverse identities.
* `invErf_analyticAt`, `hasDerivAt_invErf`: analyticity and the derivative on `(-1, 1)`.
* `invErf_nonneg`: `inverf x ≥ 0` on `[0, 1)`.
* `Real.tendsto_invErfc_nhdsGT_zero`: `inverfc x → +∞` as `x → 0+`.

## Implementation notes

`Real.invErf` reuses TauCeti's real inverse error function (`Real.erf_erfInv`). The power
series and the asymptotic expansion of the inverse functions are in
`DLMF.ErrorFunctions.InverseGeneralized`.
-/

@[expose] public noncomputable section
open Complex Filter Set
open scoped Real Topology
namespace DLMF.Confluent

/-- Inverse erf on (-1,1), reusing TauCeti; zero outside that interval. -/
@[dlmf 7.17.E1]
def Real.invErf (x : ℝ) : ℝ :=
  _root_.Real.erfInv x

/-- Inverse erfc on (0,2), with totalization inherited from invErf. -/
@[dlmf 7.17.E1]
def Real.invErfc (x : ℝ) : ℝ :=
  Real.invErf (1-x)

/-- Inverse identity; `Real.erf_erfInv` from TauCeti supplies the real theorem. -/
theorem Real.invErf_spec {x : ℝ} (hx : |x| < 1) :
    (erf (Real.invErf x)).re=x := by
  rw [erf_ofReal]
  simpa [Real.invErf] using _root_.Real.erf_erfInv (abs_lt.mp hx)

/-- Inverse complementary error function identity. -/
theorem Real.invErfc_spec {x : ℝ} (hx : 0 < x) (hx2 : x < 2) :
    (erfc (Real.invErfc x)).re=x := by
  have h : |1-x| < 1 := abs_lt.mpr (by constructor <;> linarith)
  have he := Real.invErf_spec h
  change (erfc (Real.invErf (1-x))).re=x
  change (1-erf (Real.invErf (1-x))).re=x
  simp only [Complex.sub_re, Complex.one_re, he]
  ring

/-- Analyticity of the real inverse error function on its full interval. -/
theorem invErf_analyticAt {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    AnalyticAt ℝ Real.invErf x := by
  have hf : AnalyticAt ℝ TauCeti.Real.erf (_root_.Real.erfInv x) := by
    have h := (differentiable_erf_complex.analyticAt (_root_.Real.erfInv x : ℂ)).re_ofReal
    simpa only [erf_ofReal, Complex.ofReal_re] using h
  have hd : deriv TauCeti.Real.erf (_root_.Real.erfInv x) ≠ 0 := by
    rw [(TauCeti.Real.hasDerivAt_erf _).deriv]
    positivity
  have hcomp : AnalyticAt ℝ (_root_.Real.erfInv ∘ TauCeti.Real.erf) (_root_.Real.erfInv x) := by
    apply (analyticAt_id : AnalyticAt ℝ id (_root_.Real.erfInv x)).congr
    exact Eventually.of_forall fun y => (_root_.Real.erfInv_erf y).symm
  have h := (analyticAt_comp_iff_of_deriv_ne_zero hf hd).mp hcomp
  rw [_root_.Real.erf_erfInv hx] at h
  exact h.congr (Eventually.of_forall fun y => rfl)

/-- The derivative of the project's real inverse error function. -/
theorem hasDerivAt_invErf {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.invErf (Real.sqrt π / 2 * Real.exp (Real.invErf x ^ 2)) x := by
  change HasDerivAt _root_.Real.erfInv _ x
  exact _root_.Real.hasDerivAt_erfInv hx

/-- The real inverse error function is nonnegative on the positive half-interval. -/
theorem invErf_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) : 0 ≤ Real.invErf x := by
  have h := _root_.Real.strictMonoOn_erfInv.monotoneOn
    (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by norm_num)
    (show x ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith, hx1⟩) hx0
  simpa only [_root_.Real.erfInv_zero, Real.invErf] using h

/-- The inverse complementary error function tends to positive infinity at zero from above. -/
theorem Real.tendsto_invErfc_nhdsGT_zero : Tendsto Real.invErfc (𝓝[>] (0 : ℝ)) atTop := by
  exact _root_.Real.tendsto_erfInv_nhdsLT_one.comp
    (show Tendsto (fun x : ℝ => 1-x) (𝓝[>] (0 : ℝ)) (𝓝[<] 1) from
      tendsto_nhdsWithin_iff.mpr ⟨by
          have hc : Continuous (fun x : ℝ => 1-x) := by fun_prop
          have ht : Tendsto (fun x : ℝ => 1-x) (𝓝 0) (𝓝 1) := by
            simpa only [sub_zero] using hc.tendsto (0 : ℝ)
          exact ht.mono_left nhdsWithin_le_nhds,
        by filter_upwards [self_mem_nhdsWithin] with x hx; simp only [mem_Ioi] at hx;
           simp only [mem_Iio]; linarith⟩)

end DLMF.Confluent
