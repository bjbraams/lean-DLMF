/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Appell

/-!
# Coalescing Appell connection parameters (DLMF 16.16.10)

The combined large-variable connection expression for `F₄` is continued before it is evaluated
at integer exponent differences. This retains every upper parameter and avoids evaluating its
singular Gamma factors separately. The Appell double series is never evaluated outside its
convergence region in place of a continued value.

## Main definitions

* `appF4InfinityExpression`: the two-term connection expression of DLMF 16.16.10.
* `appF4InfinityBranch`: the connection branch at every upper parameter.
* `appellInfinityDomain`: the domain of convergence of the two large-variable series.

## Main results

* `appF4_infinity_parameter_limit`: the connection terms have a locally uniform limit in the
  upper parameters.
* `appF4_infinity_all_parameters`: the limiting expression is a continued `F₄` branch for all
  upper parameters.
-/

@[expose] public noncomputable section
open Complex Filter Set
open scoped Real Topology
namespace DLMF.Hypergeometric

/-- The full two-term F4 connection expression, meaningful before its combined parameter limit. -/
def appF4InfinityExpression (a b c c' : ℂ) (p : ℂ × ℂ) : ℂ :=
  Gamma c'*Gamma (b-a)/(Gamma (c'-a)*Gamma b)*(-p.2)^(-a)*
    appF4 a (a-c'+1) c (a-b+1) (p.1/p.2) (1/p.2)+
  Gamma c'*Gamma (a-b)/(Gamma (c'-b)*Gamma a)*(-p.2)^(-b)*
    appF4 b (b-c'+1) c (b-a+1) (p.1/p.2) (1/p.2)

/-- The connection branch at every upper parameter, including coalescing integer exponents. -/
def appF4InfinityBranch (a b c c' : ℂ) (p : ℂ × ℂ) : ℂ :=
  limUnder (𝓝[≠] a) (fun a' => appF4InfinityExpression a' b c c' p)

/-- The two large-variable series converge on this branch domain. -/
def appellInfinityDomain : Set (ℂ × ℂ) :=
  {p | (p.1/p.2,1/p.2)∈appellF4Domain ∧ -p.2∈slitPlane}

/-- The combined connection terms have an actual locally uniform upper-parameter limit. -/
@[dlmf 16.16.E10]
theorem appF4_infinity_parameter_limit (a b c c' : ℂ)
    (hc : AppellRegular c) (hc' : AppellRegular c') :
    TendstoLocallyUniformlyOn (fun a' p => appF4InfinityExpression a' b c c' p)
      (appF4InfinityBranch a b c c') (𝓝[≠] a) appellInfinityDomain := by
  sorry

/-- The limiting connection expression is a genuine continued F4 branch, at all upper parameters. -/
@[dlmf 16.16.E10]
theorem appF4_infinity_all_parameters (a b c c' : ℂ)
    (hc : AppellRegular c) (hc' : AppellRegular c') {p : ℂ × ℂ}
    (hp : p∈appellInfinityDomain) :
    IsAppellBranchAt (fun q : ℂ × ℂ => appF4 a b c c' q.1 q.2) p
      (appF4InfinityBranch a b c c') := by
  sorry

end DLMF.Hypergeometric
