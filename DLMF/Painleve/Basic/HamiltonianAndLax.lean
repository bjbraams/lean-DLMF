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
# Painlevé Hamiltonian systems and Lax matrices
-/

@[expose] public noncomputable section

open Set Filter Matrix
open scoped Topology

namespace DLMF.Painleve

/-! ## Hamiltonian structure (§32.6) -/

/-- DLMF 32.6.1: `(q, p)` is a solution of the non-autonomous Hamiltonian system
`q' = ∂H/∂p`, `p' = -∂H/∂q` on `U`; the partial derivatives are `deriv` of the sections of
`H(q, p, z)` (in the theorems `H` is a polynomial, or rational with poles off `U`). -/
@[dlmf 32.6.E1]
structure IsHamiltonianSystemOn (H : ℂ → ℂ → ℂ → ℂ) (q p : ℂ → ℂ) (U : Set ℂ) : Prop where
  /-- The derivative of the position variable is the momentum partial derivative of the
  Hamiltonian. -/
  hasDerivAt_q : ∀ z ∈ U, HasDerivAt q (deriv (fun p' => H (q z) p' z) (p z)) z
  /-- The derivative of the momentum variable is minus the position partial derivative of the
  Hamiltonian. -/
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

/-- The `z`-derivative of the residue matrix `M` of 32.4.8–32.4.9 along functions with
derivatives `v₀' = dv₀`, `v₁' = dv₁`. -/
def painleveIIILaxMDeriv (z v₀ v₁ dv₀ dv₁ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![dv₀ - 1 / 4, -(dv₁ * v₀ + v₁ * dv₀);
    (dv₀ - 1 / 2) / v₁ - (v₀ - z / 2) * dv₁ / v₁ ^ 2, 1 / 4 - dv₀]

/-- The right-hand sides of the system 32.4.10–32.4.13, divided by `z`, in the order
`u₀', u₁', v₀', v₁'`. -/
def painleveIIISystemRhs (θinf z u₀ u₁ v₀ v₁ : ℂ) : ℂ × ℂ × ℂ × ℂ :=
  ((θinf * u₀ - z * v₀ * v₁) / z, (-θinf * u₁ - z * (2 * v₀ - z) / (2 * v₁)) / z,
    (2 * v₀ * u₁ * v₁ + v₀ + u₀ * (2 * v₀ - z) / v₁) / z,
    (2 * u₀ - 2 * u₁ * v₁ ^ 2 - θinf * v₁) / z)

end DLMF.Painleve
