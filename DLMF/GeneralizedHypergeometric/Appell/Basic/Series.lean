/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import DLMF.Hypergeometric.Basic.AppellF4

/-!
# Appell and Horn series, domains and differential operators
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open MeasureTheory

namespace DLMF.Hypergeometric

/-- Appell denominator parameters avoid every nonpositive integer. -/
def AppellRegular (c : ℂ) : Prop := ∀ n : ℕ,c≠ -(n:ℂ)

/-- Bidisc of absolute convergence for F1 and F3. -/
def appellBidisc : Set (ℂ × ℂ) := {p | ‖p.1‖<1 ∧ ‖p.2‖<1}

/-- Diamond of absolute convergence for F2. -/
def appellDiamond : Set (ℂ × ℂ) := {p | ‖p.1‖+‖p.2‖<1}

/-- Exact open convergence region of F4. -/
def appellF4Domain : Set (ℂ × ℂ) := {p | Real.sqrt ‖p.1‖+Real.sqrt ‖p.2‖<1}

/-- The first-variable derivative of a bivariate complex function. -/
def appellDx (f : ℂ→ℂ→ℂ) (x y : ℂ) : ℂ := deriv (fun t => f t y) x

/-- The second-variable derivative of a bivariate complex function. -/
def appellDy (f : ℂ→ℂ→ℂ) (x y : ℂ) : ℂ := deriv (f x) y

/-- The first Euler operator in two variables. -/
def appellThetaX (f : ℂ→ℂ→ℂ) : ℂ→ℂ→ℂ := fun x y => x*appellDx f x y

/-- The second Euler operator in two variables. -/
def appellThetaY (f : ℂ→ℂ→ℂ) : ℂ→ℂ→ℂ := fun x y => y*appellDy f x y

/-- Analytic continuation of a two-variable germ along a continuous parameterized path.
This is the two-variable domain analogue of TauCeti.IsAnalyticContinuationAlong. -/
structure IsAppellContinuation (F : ℝ→(ℂ × ℂ→ℂ)) (γ : ℝ→ℂ × ℂ) : Prop where
  /-- The path is continuous on `[0,1]`. -/
  continuousOn : ContinuousOn γ (Icc 0 1)
  /-- Each germ `F t` is analytic at the path point `γ t`. -/
  analyticAt : ∀ t∈Icc 0 1,AnalyticAt ℂ (F t) (γ t)
  /-- Nearby germs agree near the path: `F u = F t` near `γ u` for `u` close to `t`. -/
  locallyEq : ∀ t∈Icc 0 1,∀ᶠ u in 𝓝[Icc 0 1] t,F u=ᶠ[𝓝 (γ u)] F t

/-- A chosen branch is reached from a seed germ by a specified analytic continuation. -/
def IsAppellBranchAt (seed : ℂ × ℂ→ℂ) (p : ℂ × ℂ) (f : ℂ × ℂ→ℂ) : Prop :=
  ∃ γ : ℝ→ℂ × ℂ,∃ F : ℝ→(ℂ × ℂ→ℂ),IsAppellContinuation F γ ∧ γ 0=(0,0) ∧ γ 1=p ∧
    F 0=ᶠ[𝓝 (0,0)] seed ∧ F 1=ᶠ[𝓝 p] f

/-- Appell F1 double-series coefficient. -/
@[dlmf 16.13.E1]
def appF1Coeff (a b b' c : ℂ) (m n : ℕ) : ℂ :=
  poch a (m+n)*poch b m*poch b' n/(poch c (m+n)*(m !*n !))

/-- Appell F2 double-series coefficient. -/
@[dlmf 16.13.E2]
def appF2Coeff (a b b' c c' : ℂ) (m n : ℕ) : ℂ :=
  poch a (m+n)*poch b m*poch b' n/(poch c m*poch c' n*(m !*n !))

/-- Appell F3 double-series coefficient. -/
@[dlmf 16.13.E3]
def appF3Coeff (a a' b b' c : ℂ) (m n : ℕ) : ℂ :=
  poch a m*poch a' n*poch b m*poch b' n/(poch c (m+n)*(m !*n !))

/-- Appell's F₁ as the totalized double series `∑ₘₙ cₘₙ xᵐ yⁿ` (DLMF 16.13.E1);
continuations are represented by analytic germs. -/
@[dlmf 16.13.E1]
def appF1 (a b b' c x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,appF1Coeff a b b' c p.1 p.2*x^p.1*y^p.2

/-- Appell's F₂ as the totalized double series `∑ₘₙ cₘₙ xᵐ yⁿ` (DLMF 16.13.E2);
continuations are represented by analytic germs. -/
@[dlmf 16.13.E2]
def appF2 (a b b' c c' x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,appF2Coeff a b b' c c' p.1 p.2*x^p.1*y^p.2

/-- Appell's F₃ as the totalized double series `∑ₘₙ cₘₙ xᵐ yⁿ` (DLMF 16.13.E3);
continuations are represented by analytic germs. -/
@[dlmf 16.13.E3]
def appF3 (a a' b b' c x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,appF3Coeff a a' b b' c p.1 p.2*x^p.1*y^p.2

/-- Horn G2 in the gamma-ratio normalization. -/
@[dlmf 16.14.E5]
def hornG2 (a a' b b' x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,Gamma (a+p.1)*Gamma (a'+p.2)*Gamma (b+p.2-p.1)*Gamma (b'+p.1-p.2)/
    (Gamma a*Gamma a'*Gamma b*Gamma b'*(p.1 !*p.2 !))*x^p.1*y^p.2

/-- Horn G3 in the gamma-ratio normalization. -/
@[dlmf 16.14.E6]
def hornG3 (a a' x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,Gamma (a+2*p.2-p.1)*Gamma (a'+2*p.1-p.2)/
    (Gamma a*Gamma a'*(p.1 !*p.2 !))*x^p.1*y^p.2

end DLMF.Hypergeometric
