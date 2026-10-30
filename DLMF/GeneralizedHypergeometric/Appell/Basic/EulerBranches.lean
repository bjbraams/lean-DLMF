/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Appell.Basic.Series

/-!
# Euler domains, kernels and integral branches of Appell functions
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open MeasureTheory

namespace DLMF.Hypergeometric

/-- Natural principal cut plane for the two separate Euler denominator factors. -/
def appellEulerDomain : Set (ℂ × ℂ) := {p | 1-p.1∈slitPlane ∧ 1-p.2∈slitPlane}

/-- The square-integral denominator stays on its principal branch at every integration point. -/
def appellSquareSlit (p : ℂ × ℂ) : Prop :=
  ∀ u∈Icc (0:ℝ) 1,∀ v∈Icc (0:ℝ) 1,1-(u:ℂ)*p.1-(v:ℂ)*p.2∈slitPlane

/-- Euler's integration triangle, including its measure-zero boundary. -/
def appellTriangle : Set (ℝ × ℝ) := {p | 0≤p.1 ∧ 0≤p.2 ∧ p.1+p.2≤1}

/-- The Euler kernel for F1, with all powers principal on their stated domain. -/
def appF1EulerKernel (a b b' c x y : ℂ) (u : ℝ) : ℂ :=
  (u:ℂ)^(a-1)*((1-u:ℝ):ℂ)^(c-a-1)/(1-u*x)^b/(1-u*y)^b'

/-- The Euler kernel for F2. -/
def appF2EulerKernel (a b b' c c' x y : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1:ℂ)^(b-1)*(p.2:ℂ)^(b'-1)*((1-p.1:ℝ):ℂ)^(c-b-1)*
    ((1-p.2:ℝ):ℂ)^(c'-b'-1)/(1-p.1*x-p.2*y)^a

/-- The simplex Euler kernel for F3. -/
def appF3EulerKernel (a a' b b' c x y : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1:ℂ)^(b-1)*(p.2:ℂ)^(b'-1)*((1-p.1-p.2:ℝ):ℂ)^(c-b-b'-1)/
    (1-p.1*x)^a/(1-p.2*y)^a'

/-- The transformed Euler kernel for F4. -/
def appF4EulerKernel (a b c c' x y : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1:ℂ)^(a-1)*(p.2:ℂ)^(b-1)*((1-p.1:ℝ):ℂ)^(c-a-1)*
    ((1-p.2:ℝ):ℂ)^(c'-b-1)/(1-p.1*x)^(c+c'-a-1)/(1-p.2*y)^(c+c'-b-1)/
    (1-p.1*x-p.2*y)^(a+b-c-c'+1)

/-- The Euler integral branch of F1, distinct from its totalized double series. -/
@[dlmf 16.15.E1]
def appF1Euler (a b b' c x y : ℂ) : ℂ :=
  Gamma c/(Gamma a*Gamma (c-a))*∫ u in (0:ℝ)..1,appF1EulerKernel a b b' c x y u

/-- The Euler square-integral branch of F2. -/
@[dlmf 16.15.E2]
def appF2Euler (a b b' c c' x y : ℂ) : ℂ :=
  Gamma c*Gamma c'/(Gamma b*Gamma b'*Gamma (c-b)*Gamma (c'-b'))*
    ∫ p in Icc (0:ℝ) 1×ˢIcc (0:ℝ) 1,appF2EulerKernel a b b' c c' x y p

/-- The Euler simplex-integral branch of F3. -/
@[dlmf 16.15.E3]
def appF3Euler (a a' b b' c x y : ℂ) : ℂ :=
  Gamma c/(Gamma b*Gamma b'*Gamma (c-b-b'))*
    ∫ p in appellTriangle,appF3EulerKernel a a' b b' c x y p

/-- The Euler branch at the transformed arguments x(1-y),y(1-x). -/
@[dlmf 16.15.E4]
def appF4Euler (a b c c' x y : ℂ) : ℂ :=
  Gamma c*Gamma c'/(Gamma a*Gamma b*Gamma (c-a)*Gamma (c'-b))*
    ∫ p in Icc (0:ℝ) 1×ˢIcc (0:ℝ) 1,appF4EulerKernel a b c c' x y p

end DLMF.Hypergeometric
