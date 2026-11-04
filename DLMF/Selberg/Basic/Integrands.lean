/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Selberg integrands, cubes and Aomoto's integrals (AAR §8.1)

## Main definitions

* `selbergIntegrand`, `selbergIntegral`: the Selberg integrand on `[0,1]^n` and the Selberg integral
  as a function of its parameters.
* `unitCube`: the closed unit unitCube `[0,1]ⁿ`.
* `selbergWeight`, `selbergWeightReal`: the complex selbergWeight `x^{a-1}(1-x)^{b-1}` and the real
  product selbergWeight.
* `vandermondeAbsPow`, `vandermondeSq`, `linearFactorAbsPow`: the Vandermonde factor
  `∏_{i<j} |tᵢ - tⱼ|^{2c}`, the squared Vandermonde product and `∏ⱼ |x - yⱼ|^{2c}`.
* `integrationByPartsF`, `integrationByPartsD`, `integrationByPartsBound`: the function, derivative
  and majorant of the one-variable integration by parts.
* `monomialProduct`, `aomotoIntegral`, `aomotoFactor`: the monomials `∏_{i∈S} tᵢ`, Aomoto's
  integrals and the ratio in Aomoto's formula.
* `reflectUnitCube`: the reflection `t ↦ 1 - t` of the unitCube.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter
open scoped Real Topology

namespace DLMF.Selberg

/-- The Selberg integrand on `[0,1]^n` (AAR §8.1). -/
def selbergIntegrand (n : ℕ) (a b c : ℂ) (t : Fin n → ℝ) : ℂ :=
  (∏ i : Fin n, (t i : ℂ) ^ (a - 1) * (1 - (t i : ℂ)) ^ (b - 1)) *
    ∏ i : Fin n, ∏ j : Fin n,
      if i.val < j.val then ((abs (t i - t j) : ℝ) : ℂ) ^ (2 * c) else 1

/-- The closed unit unitCube `[0,1]ⁿ`. -/
abbrev unitCube (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

/-- The one-variable Selberg selbergWeight `x^{a-1}(1-x)^{b-1}`. -/
def selbergWeight (a b : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ (a - 1) * (1 - (x : ℂ)) ^ (b - 1)

/-- The Vandermonde factor `∏_{i<j} |tᵢ - tⱼ|^{2c}`. -/
def vandermondeAbsPow (n : ℕ) (c : ℂ) (t : Fin n → ℝ) : ℂ :=
  ∏ i : Fin n, ∏ j : Fin n, if i.val < j.val then ((|t i - t j| : ℝ) : ℂ) ^ (2 * c) else 1

/-- `∏ⱼ |x - yⱼ|^{2c}`. -/
def linearFactorAbsPow {n : ℕ} (y : Fin n → ℝ) (c : ℂ) (x : ℝ) : ℂ :=
  ∏ j : Fin n, ((|x - y j| : ℝ) : ℂ) ^ (2 * c)

/-- The function differentiated in the one-variable integration by parts. -/
def integrationByPartsF {n : ℕ} (y : Fin n → ℝ) (α β c : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ α * (1 - (x : ℂ)) ^ β * linearFactorAbsPow y c x

/-- Its derivative off the points `yⱼ`. -/
def integrationByPartsD {n : ℕ} (y : Fin n → ℝ) (α β c : ℂ) (x : ℝ) : ℂ :=
  (α * (x : ℂ) ^ (α - 1) * (1 - (x : ℂ)) ^ β - β * (x : ℂ) ^ α * (1 - (x : ℂ)) ^ (β - 1)) *
      linearFactorAbsPow y c x +
    (x : ℂ) ^ α * (1 - (x : ℂ)) ^ β *
        ((∑ j : Fin n, 2 * c / ((x : ℂ) - y j)) * linearFactorAbsPow y c x)

/-- An integrable majorant for `integrationByPartsD`, independent of `y`. -/
def integrationByPartsBound (n : ℕ) (α β c : ℂ) (x : ℝ) : ℝ :=
  ‖α‖ * x ^ (α.re - 1) + (if β = 0 then 0 else ‖β‖ * (1 - x) ^ (β.re - 1)) + n * (2 * ‖c‖)

/-- `∏ᵢ∈S tᵢ`. -/
def monomialProduct {N : ℕ} (S : Finset (Fin N)) (t : Fin N → ℝ) : ℂ := ∏ i ∈ S, (t i : ℂ)

/-- Aomoto's integrals `∫ ∏ᵢ∈S tᵢ · Φ(t) dt`. -/
def aomotoIntegral (N : ℕ) (a b c : ℂ) (S : Finset (Fin N)) : ℂ :=
  ∫ t in unitCube N, monomialProduct S t * selbergIntegrand N a b c t

/-- The preimage of `S` under `Fin.succ`. -/
def preimageSucc {n : ℕ} (S : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun j => j.succ ∈ S

/-- The initial segment `{i | i < m}`. -/
def initialSegment (N m : ℕ) : Finset (Fin N) := Finset.univ.filter fun i => i.val < m

/-- The ratio in Aomoto's formula. -/
def aomotoFactor (N : ℕ) (a b c : ℂ) (j : ℕ) : ℂ :=
  (a + ((N - 1 - j : ℕ) : ℂ) * c) / (a + b + ((2 * N - 2 - j : ℕ) : ℂ) * c)

/-- The Selberg integral as a function of its parameters. -/
def selbergIntegral (N : ℕ) (a b c : ℂ) : ℂ := ∫ t in unitCube N, selbergIntegrand N a b c t

/-- The reflection `t ↦ 1 - t` of the unitCube. -/
def reflectUnitCube {N : ℕ} (t : Fin N → ℝ) : Fin N → ℝ := fun i => 1 - t i

/-- `∏_{i<j} (tᵢ - tⱼ)²`. -/
def vandermondeSq (N : ℕ) (t : Fin N → ℝ) : ℝ :=
  ∏ i : Fin N, ∏ j : Fin N, if i.val < j.val then (t i - t j) ^ 2 else 1

/-- The real selbergWeight `∏ tᵢ^{α-1}(1-tᵢ)^{β-1}`. -/
def selbergWeightReal (N : ℕ) (α β : ℝ) (t : Fin N → ℝ) : ℝ :=
  ∏ i : Fin N, t i ^ (α - 1) * (1 - t i) ^ (β - 1)

end DLMF.Selberg
