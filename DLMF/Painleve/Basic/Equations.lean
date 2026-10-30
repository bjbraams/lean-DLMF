/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Painlevé equations and elementary Bäcklund maps in the DLMF normalization
-/

@[expose] public noncomputable section

open Set Filter Matrix
open scoped Topology

namespace DLMF.Painleve

/-! ## Second-order equations -/

/-- DLMF 32.2.7: `w` solves the second-order equation `w'' = F(z, w, w')` on `U`. Both `w` and
`w'` are required to be differentiable at every point of `U`, and the derivative of `w'` must
be `F(z, w(z), w'(z))`. Intended for open `U` (the statements take `IsOpen U`). -/
@[dlmf 32.2.E7]
structure IsODE2SolutionOn (F : ℂ → ℂ → ℂ → ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop where
  /-- The solution is differentiable at every point of the domain. -/
  differentiableAt : ∀ z ∈ U, DifferentiableAt ℂ w z
  /-- The first derivative has the derivative prescribed by the differential equation. -/
  hasDerivAt_deriv : ∀ z ∈ U, HasDerivAt (deriv w) (F z (w z) (deriv w z)) z

namespace IsODE2SolutionOn

variable {F G : ℂ → ℂ → ℂ → ℂ} {w : ℂ → ℂ} {U V : Set ℂ}

/-- The first derivative of a solution. -/
theorem hasDerivAt (h : IsODE2SolutionOn F w U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt w (deriv w z) z := (h.differentiableAt z hz).hasDerivAt

/-- The equation itself. -/
theorem ode (h : IsODE2SolutionOn F w U) {z : ℂ} (hz : z ∈ U) :
    deriv (deriv w) z = F z (w z) (deriv w z) := (h.hasDerivAt_deriv z hz).deriv

/-- Restriction to a smaller set. -/
theorem mono (h : IsODE2SolutionOn F w U) (hVU : V ⊆ U) : IsODE2SolutionOn F w V :=
  ⟨fun z hz => h.differentiableAt z (hVU hz), fun z hz => h.hasDerivAt_deriv z (hVU hz)⟩

/-- Change of right-hand side when the two agree along the solution. -/
theorem congr_rhs (h : IsODE2SolutionOn F w U)
    (hFG : ∀ z ∈ U, F z (w z) (deriv w z) = G z (w z) (deriv w z)) :
    IsODE2SolutionOn G w U :=
  ⟨h.differentiableAt, fun z hz => (hFG z hz) ▸ h.hasDerivAt_deriv z hz⟩

end IsODE2SolutionOn

/-- Build a solution from an explicit first-order pair `w' = v`, `v' = F(z, w, v)` on an open
set. -/
theorem isODE2SolutionOn_of_hasDerivAt {F : ℂ → ℂ → ℂ → ℂ} {w v : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hw : ∀ z ∈ U, HasDerivAt w (v z) z)
    (hv : ∀ z ∈ U, HasDerivAt v (F z (w z) (v z)) z) : IsODE2SolutionOn F w U := by
  refine ⟨fun z hz => (hw z hz).differentiableAt, fun z hz => ?_⟩
  have he : deriv w =ᶠ[𝓝 z] v := by
    filter_upwards [hU.mem_nhds hz] with y hy using (hw y hy).deriv
  rw [(hw z hz).deriv]
  exact (hv z hz).congr_of_eventuallyEq he

/-! ## The six Painlevé equations (32.2.1–32.2.6) -/

/-- The right-hand side `6w² + z` of DLMF 32.2.1 (`PI`); `v` stands for `w'`. -/
@[dlmf 32.2.E1]
def painleveIRhs (z w _v : ℂ) : ℂ := 6 * w ^ 2 + z

/-- The right-hand side `2w³ + zw + α` of DLMF 32.2.2 (`PII`). -/
@[dlmf 32.2.E2]
def painleveIIRhs (α : ℂ) (z w _v : ℂ) : ℂ := 2 * w ^ 3 + z * w + α

/-- The right-hand side of DLMF 32.2.3 (`PIII`):
`w'²/w - w'/z + (αw² + β)/z + γw³ + δ/w`. Junk values at `z = 0` or `w = 0`. -/
@[dlmf 32.2.E3]
def painleveIIIRhs (α β γ δ : ℂ) (z w v : ℂ) : ℂ :=
  v ^ 2 / w - v / z + (α * w ^ 2 + β) / z + γ * w ^ 3 + δ / w

/-- The right-hand side of DLMF 32.2.4 (`PIV`):
`w'²/(2w) + (3/2)w³ + 4zw² + 2(z² - α)w + β/w`. Junk values at `w = 0`. -/
@[dlmf 32.2.E4]
def painleveIVRhs (α β : ℂ) (z w v : ℂ) : ℂ :=
  v ^ 2 / (2 * w) + 3 / 2 * w ^ 3 + 4 * z * w ^ 2 + 2 * (z ^ 2 - α) * w + β / w

/-- The right-hand side of DLMF 32.2.5 (`PV`):
`(1/(2w) + 1/(w-1))w'² - w'/z + (w-1)²(αw + β/w)/z² + γw/z + δw(w+1)/(w-1)`.
Junk values at `z = 0`, `w = 0`, `w = 1`. -/
@[dlmf 32.2.E5]
def painleveVRhs (α β γ δ : ℂ) (z w v : ℂ) : ℂ :=
  (1 / (2 * w) + 1 / (w - 1)) * v ^ 2 - v / z + (w - 1) ^ 2 / z ^ 2 * (α * w + β / w) +
    γ * w / z + δ * w * (w + 1) / (w - 1)

/-- The right-hand side of DLMF 32.2.6 (`PVI`). Junk values at `z ∈ {0, 1}` or
`w ∈ {0, 1, z}`. -/
@[dlmf 32.2.E6]
def painleveVIRhs (α β γ δ : ℂ) (z w v : ℂ) : ℂ :=
  1 / 2 * (1 / w + 1 / (w - 1) + 1 / (w - z)) * v ^ 2 -
      (1 / z + 1 / (z - 1) + 1 / (w - z)) * v +
    w * (w - 1) * (w - z) / (z ^ 2 * (z - 1) ^ 2) *
      (α + β * z / w ^ 2 + γ * (z - 1) / (w - 1) ^ 2 + δ * z * (z - 1) / (w - z) ^ 2)

/-- DLMF 32.2.1: `w` is a solution of `PI`, `w'' = 6w² + z`, on `U` (where it is
holomorphic). -/
@[dlmf 32.2.E1]
def IsPainleveIOn (w : ℂ → ℂ) (U : Set ℂ) : Prop := IsODE2SolutionOn painleveIRhs w U

/-- DLMF 32.2.2: `w` is a solution of `PII`, `w'' = 2w³ + zw + α`, on `U`. This is
Beals–Wong's `PII(-α)` (`IsPIIOn (-α)`). -/
@[dlmf 32.2.E2]
def IsPainleveIIOn (α : ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop :=
  IsODE2SolutionOn (painleveIIRhs α) w U

/-- DLMF 32.2.3: `w` is a solution of `PIII` on `U`, which avoids `z = 0` and the zeros
of `w`. -/
@[dlmf 32.2.E3]
structure IsPainleveIIIOn (α β γ δ : ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop where
  /-- The solution satisfies the differential equation throughout the domain. -/
  ode : IsODE2SolutionOn (painleveIIIRhs α β γ δ) w U
  /-- The independent variable avoids zero throughout the domain. -/
  ne_zero : ∀ z ∈ U, z ≠ 0
  /-- The solution avoids zero, so the rational terms in the equation are defined. -/
  w_ne_zero : ∀ z ∈ U, w z ≠ 0

/-- DLMF 32.2.4: `w` is a solution of `PIV` on `U`, which avoids the zeros of `w`. -/
@[dlmf 32.2.E4]
structure IsPainleveIVOn (α β : ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop where
  /-- The solution satisfies the differential equation throughout the domain. -/
  ode : IsODE2SolutionOn (painleveIVRhs α β) w U
  /-- The solution avoids zero, so the rational terms in the equation are defined. -/
  w_ne_zero : ∀ z ∈ U, w z ≠ 0

/-- DLMF 32.2.5: `w` is a solution of `PV` on `U`, which avoids `z = 0` and the points where
`w ∈ {0, 1}`. -/
@[dlmf 32.2.E5]
structure IsPainleveVOn (α β γ δ : ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop where
  /-- The solution satisfies the differential equation throughout the domain. -/
  ode : IsODE2SolutionOn (painleveVRhs α β γ δ) w U
  /-- The independent variable avoids zero throughout the domain. -/
  ne_zero : ∀ z ∈ U, z ≠ 0
  /-- The solution avoids zero, so the rational terms in the equation are defined. -/
  w_ne_zero : ∀ z ∈ U, w z ≠ 0
  /-- The solution avoids one, so the rational terms in the equation are defined. -/
  w_ne_one : ∀ z ∈ U, w z ≠ 1

/-- DLMF 32.2.6: `w` is a solution of `PVI` on `U`, which avoids `z ∈ {0, 1}` and the points
where `w ∈ {0, 1, z}`. -/
@[dlmf 32.2.E6]
structure IsPainleveVIOn (α β γ δ : ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop where
  /-- The solution satisfies the differential equation throughout the domain. -/
  ode : IsODE2SolutionOn (painleveVIRhs α β γ δ) w U
  /-- The independent variable avoids zero throughout the domain. -/
  ne_zero : ∀ z ∈ U, z ≠ 0
  /-- The independent variable avoids one throughout the domain. -/
  ne_one : ∀ z ∈ U, z ≠ 1
  /-- The solution avoids zero, so the rational terms in the equation are defined. -/
  w_ne_zero : ∀ z ∈ U, w z ≠ 0
  /-- The solution avoids one, so the rational terms in the equation are defined. -/
  w_ne_one : ∀ z ∈ U, w z ≠ 1
  /-- The solution differs from the independent variable throughout the domain. -/
  w_ne_self : ∀ z ∈ U, w z ≠ z

/-- The right-hand side of DLMF 32.2.9 (`P'III`):
`u'²/u - u'/ζ + u²(α + γu)/(4ζ²) + β/(4ζ) + δ/(4u)`. -/
@[dlmf 32.2.E9]
def painleveIIIPrimeRhs (α β γ δ : ℂ) (ζ u v : ℂ) : ℂ :=
  v ^ 2 / u - v / ζ + u ^ 2 * (α + γ * u) / (4 * ζ ^ 2) + β / (4 * ζ) + δ / (4 * u)

/-- DLMF 32.2.9: `u` is a solution of `P'III` on `U`, which avoids `ζ = 0` and the zeros
of `u`. -/
@[dlmf 32.2.E9]
structure IsPainleveIIIPrimeOn (α β γ δ : ℂ) (u : ℂ → ℂ) (U : Set ℂ) : Prop where
  /-- The solution satisfies the differential equation throughout the domain. -/
  ode : IsODE2SolutionOn (painleveIIIPrimeRhs α β γ δ) u U
  /-- The independent variable avoids zero throughout the domain. -/
  ne_zero : ∀ z ∈ U, z ≠ 0
  /-- The solution avoids zero, so the rational terms in the equation are defined. -/
  w_ne_zero : ∀ z ∈ U, u z ≠ 0

/-! ## Bäcklund transformations of `PII` (32.7.2) -/

/-- DLMF 32.7.2, `T⁺`: `w(z; α+1) = -w - (2α+1)/(2w² + 2w' + z)` (junk value `-w` where the
denominator vanishes). -/
@[dlmf 32.7.E2]
def painleveIITPlus (α : ℂ) (w : ℂ → ℂ) (z : ℂ) : ℂ :=
  -w z - (2 * α + 1) / (2 * w z ^ 2 + 2 * deriv w z + z)

/-- DLMF 32.7.2, `T⁻`: `w(z; α-1) = -w - (2α-1)/(2w² - 2w' + z)`. -/
@[dlmf 32.7.E2]
def painleveIITMinus (α : ℂ) (w : ℂ → ℂ) (z : ℂ) : ℂ :=
  -w z - (2 * α - 1) / (2 * w z ^ 2 - 2 * deriv w z + z)

end DLMF.Painleve
