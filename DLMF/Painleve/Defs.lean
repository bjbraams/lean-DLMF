/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Painlevé equations in the DLMF normalization: definitions (DLMF Chapter 32)

This file holds the definitions of DLMF Chapter 32 (namespace `DLMF.Painleve`). The older
files of this area (`Basic`, `Backlund`, …) follow Beals–Wong, whose `PII(c)` is
`u'' = 2u³ + xu - c` (`IsPIIOn`); DLMF's `PII` with parameter `α` is the same equation with
`c = -α` (`isPainleveIIOn_iff_isPIIOn` in `DLMF.Painleve.Equations`).

* `IsODE2SolutionOn F w U` (32.2.7): `w'' = F(z, w, w')` on `U`, with genuine
  differentiability of `w` and of `w'` at every point of `U` (so totalized derivatives cannot
  make a nonsolution satisfy the equation). Statements use it on open sets.
* The right-hand sides `painleveIRhs` … `painleveVIRhs` of 32.2.1–32.2.6, as functions of the
  jet `(z, w, w')`, and the predicates `IsPainleveIOn` … `IsPainleveVIOn`. For `PIII`–`PVI` the
  predicate also requires that `U` avoids the points where DLMF divides (`z = 0`, `z = 1`,
  `w = 0`, `w = 1`, `w = z`), so the totalized divisions `x / 0 = 0` never enter.
* `IsPainleveIIIPrimeOn` (32.2.9, DLMF's `P'III`).
* The Hamiltonians of §32.6 and the Hamiltonian system `IsHamiltonianSystemOn` (32.6.1).
* The DLMF Bäcklund maps `painleveIITPlus`, `painleveIITMinus` of 32.7.2.
* The Lax matrices of 32.4.4–32.4.9.
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
  differentiableAt : ∀ z ∈ U, DifferentiableAt ℂ w z
  hasDerivAt_deriv : ∀ z ∈ U, HasDerivAt (deriv w) (F z (w z) (deriv w z)) z

namespace IsODE2SolutionOn

variable {F G : ℂ → ℂ → ℂ → ℂ} {w : ℂ → ℂ} {U V : Set ℂ}

/-- The first derivative of a solution. -/
lemma hasDerivAt (h : IsODE2SolutionOn F w U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt w (deriv w z) z := (h.differentiableAt z hz).hasDerivAt

/-- The equation itself. -/
lemma ode (h : IsODE2SolutionOn F w U) {z : ℂ} (hz : z ∈ U) :
    deriv (deriv w) z = F z (w z) (deriv w z) := (h.hasDerivAt_deriv z hz).deriv

/-- Restriction to a smaller set. -/
lemma mono (h : IsODE2SolutionOn F w U) (hVU : V ⊆ U) : IsODE2SolutionOn F w V :=
  ⟨fun z hz => h.differentiableAt z (hVU hz), fun z hz => h.hasDerivAt_deriv z (hVU hz)⟩

/-- Change of right-hand side when the two agree along the solution. -/
lemma congr_rhs (h : IsODE2SolutionOn F w U)
    (hFG : ∀ z ∈ U, F z (w z) (deriv w z) = G z (w z) (deriv w z)) :
    IsODE2SolutionOn G w U :=
  ⟨h.differentiableAt, fun z hz => (hFG z hz) ▸ h.hasDerivAt_deriv z hz⟩

end IsODE2SolutionOn

/-- Build a solution from an explicit first-order pair `w' = v`, `v' = F(z, w, v)` on an open
set. -/
lemma isODE2SolutionOn_of_hasDerivAt {F : ℂ → ℂ → ℂ → ℂ} {w v : ℂ → ℂ} {U : Set ℂ}
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
  ode : IsODE2SolutionOn (painleveIIIRhs α β γ δ) w U
  ne_zero : ∀ z ∈ U, z ≠ 0
  w_ne_zero : ∀ z ∈ U, w z ≠ 0

/-- DLMF 32.2.4: `w` is a solution of `PIV` on `U`, which avoids the zeros of `w`. -/
@[dlmf 32.2.E4]
structure IsPainleveIVOn (α β : ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop where
  ode : IsODE2SolutionOn (painleveIVRhs α β) w U
  w_ne_zero : ∀ z ∈ U, w z ≠ 0

/-- DLMF 32.2.5: `w` is a solution of `PV` on `U`, which avoids `z = 0` and the points where
`w ∈ {0, 1}`. -/
@[dlmf 32.2.E5]
structure IsPainleveVOn (α β γ δ : ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop where
  ode : IsODE2SolutionOn (painleveVRhs α β γ δ) w U
  ne_zero : ∀ z ∈ U, z ≠ 0
  w_ne_zero : ∀ z ∈ U, w z ≠ 0
  w_ne_one : ∀ z ∈ U, w z ≠ 1

/-- DLMF 32.2.6: `w` is a solution of `PVI` on `U`, which avoids `z ∈ {0, 1}` and the points
where `w ∈ {0, 1, z}`. -/
@[dlmf 32.2.E6]
structure IsPainleveVIOn (α β γ δ : ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop where
  ode : IsODE2SolutionOn (painleveVIRhs α β γ δ) w U
  ne_zero : ∀ z ∈ U, z ≠ 0
  ne_one : ∀ z ∈ U, z ≠ 1
  w_ne_zero : ∀ z ∈ U, w z ≠ 0
  w_ne_one : ∀ z ∈ U, w z ≠ 1
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
  ode : IsODE2SolutionOn (painleveIIIPrimeRhs α β γ δ) u U
  ne_zero : ∀ z ∈ U, z ≠ 0
  w_ne_zero : ∀ z ∈ U, u z ≠ 0

/-! ## Hamiltonian structure (§32.6) -/

/-- DLMF 32.6.1: `(q, p)` is a solution of the non-autonomous Hamiltonian system
`q' = ∂H/∂p`, `p' = -∂H/∂q` on `U`; the partial derivatives are `deriv` of the sections of
`H(q, p, z)` (in the theorems `H` is a polynomial, or rational with poles off `U`). -/
@[dlmf 32.6.E1]
structure IsHamiltonianSystemOn (H : ℂ → ℂ → ℂ → ℂ) (q p : ℂ → ℂ) (U : Set ℂ) : Prop where
  hasDerivAt_q : ∀ z ∈ U, HasDerivAt q (deriv (fun p' => H (q z) p' z) (p z)) z
  hasDerivAt_p : ∀ z ∈ U, HasDerivAt p (-deriv (fun q' => H q' (p z) z) (q z)) z

/-- DLMF 32.6.2: the Hamiltonian `H_I(q, p, z) = p²/2 - 2q³ - zq` of `PI`. -/
@[dlmf 32.6.E2]
def painleveHamiltonianI (q p z : ℂ) : ℂ := p ^ 2 / 2 - 2 * q ^ 3 - z * q

/-- DLMF 32.6.9: the Hamiltonian `H_II(q, p, z) = p²/2 - (q² + z/2)p - (α + 1/2)q` of
`PII`. -/
@[dlmf 32.6.E9]
def painleveHamiltonianII (α : ℂ) (q p z : ℂ) : ℂ :=
  p ^ 2 / 2 - (q ^ 2 + z / 2) * p - (α + 1 / 2) * q

/-- DLMF 32.6.16: the Hamiltonian of `PIII`,
`z H_III = q²p² - (κ∞zq² + (2θ₀+1)q - κ₀z)p + κ∞(θ₀+θ∞)zq`, divided by `z` (junk value `0`
at `z = 0`). Parameters in the order `κ₀ κ∞ θ₀ θ∞` (`κinf`, `θinf` in Lean). -/
@[dlmf 32.6.E16]
def painleveHamiltonianIII (κ₀ κinf θ₀ θinf : ℂ) (q p z : ℂ) : ℂ :=
  (q ^ 2 * p ^ 2 - (κinf * z * q ^ 2 + (2 * θ₀ + 1) * q - κ₀ * z) * p +
    κinf * (θ₀ + θinf) * z * q) / z

/-- DLMF 32.6.24: the Hamiltonian of `P'III`,
`ζ H = q²p² - (η∞q² + θ₀q - η₀ζ)p + η∞(θ₀+θ∞)q/2`, divided by `ζ`. Parameters in the order
`η₀ η∞ θ₀ θ∞`. -/
@[dlmf 32.6.E24]
def painleveHamiltonianIIIPrime (η₀ ηinf θ₀ θinf : ℂ) (q p ζ : ℂ) : ℂ :=
  (q ^ 2 * p ^ 2 - (ηinf * q ^ 2 + θ₀ * q - η₀ * ζ) * p + ηinf * (θ₀ + θinf) * q / 2) / ζ

/-- DLMF 32.6.32: the Hamiltonian of `PIII` with `γ = 0`,
`z H = q²p² + (θq - κ₀z)p - κ∞zq`, divided by `z`. -/
@[dlmf 32.6.E32]
def painleveHamiltonianIIIGammaZero (κ₀ κinf θ : ℂ) (q p z : ℂ) : ℂ :=
  (q ^ 2 * p ^ 2 + (θ * q - κ₀ * z) * p - κinf * z * q) / z

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

/-! ## Lax pairs (§32.4) -/

/-- The Pauli-type matrix `σ₃ = [[1,0],[0,-1]]` of §32.4. -/
def laxSigma3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Pauli-type matrix `σ₂ = [[0,-i],[i,0]]` of §32.4. -/
def laxSigma2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli-type matrix `σ₁ = [[0,1],[1,0]]` of §32.4. -/
def laxSigma1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- DLMF 32.4.4: the `λ`-matrix of the `PI` Lax pair, as a function of the jet
`(z, w, w') = (z, w, v)`:
`A = (4λ⁴ + 2w² + z)σ₃ - i(4λ²w + 2w² + z)σ₂ - (2λw' + 1/(2λ))σ₁`. -/
@[dlmf 32.4.E4]
def painleveILaxA (z w v l : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (4 * l ^ 4 + 2 * w ^ 2 + z) • laxSigma3 -
    (Complex.I * (4 * l ^ 2 * w + 2 * w ^ 2 + z)) • laxSigma2 -
    (2 * l * v + 1 / (2 * l)) • laxSigma1

/-- DLMF 32.4.5: the `z`-matrix of the `PI` Lax pair, `B = (λ + w/λ)σ₃ - (iw/λ)σ₂`. -/
@[dlmf 32.4.E5]
def painleveILaxB (w l : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (l + w / l) • laxSigma3 - (Complex.I * w / l) • laxSigma2

/-- DLMF 32.4.6: the `λ`-matrix of the `PII` Lax pair,
`A = -i(4λ² + 2w² + z)σ₃ - 2w'σ₂ + (4λw - α/λ)σ₁`. -/
@[dlmf 32.4.E6]
def painleveIILaxA (α z w v l : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-Complex.I * (4 * l ^ 2 + 2 * w ^ 2 + z)) • laxSigma3 - (2 * v) • laxSigma2 +
    (4 * l * w - α / l) • laxSigma1

/-- DLMF 32.4.7: the `z`-matrix of the `PII` Lax pair, `B = [[-iλ, w], [w, iλ]]`. -/
@[dlmf 32.4.E7]
def painleveIILaxB (w l : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-Complex.I * l, w; w, Complex.I * l]

/-- The residue matrix `[[v₀ - z/4, -v₁v₀], [(v₀ - z/2)/v₁, z/4 - v₀]]` common to 32.4.8 and
32.4.9. -/
def painleveIIILaxM (z v₀ v₁ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![v₀ - z / 4, -v₁ * v₀; (v₀ - z / 2) / v₁, z / 4 - v₀]

/-- DLMF 32.4.8: the `λ`-matrix of the `PIII` Lax pair,
`A = diag(z/4, -z/4) + [[-θ∞/2, u₀],[u₁, θ∞/2]]/λ + M/λ²`. -/
@[dlmf 32.4.E8]
def painleveIIILaxA (θinf z u₀ u₁ v₀ v₁ l : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![z / 4, 0; 0, -z / 4] + (1 / l) • !![-θinf / 2, u₀; u₁, θinf / 2] +
    (1 / l ^ 2) • painleveIIILaxM z v₀ v₁

/-- DLMF 32.4.9: the `z`-matrix of the `PIII` Lax pair,
`B = diag(1/4, -1/4)λ + [[0, u₀],[u₁, 0]]/z - M/(zλ)`. -/
@[dlmf 32.4.E9]
def painleveIIILaxB (z u₀ u₁ v₀ v₁ l : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  l • !![1 / 4, 0; 0, -1 / 4] + (1 / z) • !![0, u₀; u₁, 0] -
    (1 / (z * l)) • painleveIIILaxM z v₀ v₁

end DLMF.Painleve
