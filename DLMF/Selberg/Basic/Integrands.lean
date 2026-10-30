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
# Selberg integrands, cubes and Aomoto defining data
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

/-- The closed unit cube `[0,1]ⁿ`. -/
abbrev cube (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

/-- The one-variable Selberg weight `x^{a-1}(1-x)^{b-1}`. -/
def weight (a b : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ (a - 1) * (1 - (x : ℂ)) ^ (b - 1)

/-- The Vandermonde factor `∏_{i<j} |tᵢ - tⱼ|^{2c}`. -/
def vdm (n : ℕ) (c : ℂ) (t : Fin n → ℝ) : ℂ :=
  ∏ i : Fin n, ∏ j : Fin n, if i.val < j.val then ((|t i - t j| : ℝ) : ℂ) ^ (2 * c) else 1

/-- `∏ⱼ |x - yⱼ|^{2c}`. -/
def vprod {n : ℕ} (y : Fin n → ℝ) (c : ℂ) (x : ℝ) : ℂ :=
  ∏ j : Fin n, ((|x - y j| : ℝ) : ℂ) ^ (2 * c)

/-- The function differentiated in the one-variable integration by parts. -/
def ibpF {n : ℕ} (y : Fin n → ℝ) (α β c : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ α * (1 - (x : ℂ)) ^ β * vprod y c x

/-- Its derivative off the points `yⱼ`. -/
def ibpD {n : ℕ} (y : Fin n → ℝ) (α β c : ℂ) (x : ℝ) : ℂ :=
  (α * (x : ℂ) ^ (α - 1) * (1 - (x : ℂ)) ^ β - β * (x : ℂ) ^ α * (1 - (x : ℂ)) ^ (β - 1)) *
      vprod y c x +
    (x : ℂ) ^ α * (1 - (x : ℂ)) ^ β * ((∑ j : Fin n, 2 * c / ((x : ℂ) - y j)) * vprod y c x)

/-- An integrable majorant for `ibpD`, independent of `y`. -/
def ibpBound (n : ℕ) (α β c : ℂ) (x : ℝ) : ℝ :=
  ‖α‖ * x ^ (α.re - 1) + (if β = 0 then 0 else ‖β‖ * (1 - x) ^ (β.re - 1)) + n * (2 * ‖c‖)

/-- `∏ᵢ∈S tᵢ`. -/
def mono {N : ℕ} (S : Finset (Fin N)) (t : Fin N → ℝ) : ℂ := ∏ i ∈ S, (t i : ℂ)

/-- Aomoto's integrals `∫ ∏ᵢ∈S tᵢ · Φ(t) dt`. -/
def aomotoInt (N : ℕ) (a b c : ℂ) (S : Finset (Fin N)) : ℂ :=
  ∫ t in cube N, mono S t * selbergIntegrand N a b c t

/-- The preimage of `S` under `Fin.succ`. -/
def succPre {n : ℕ} (S : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun j => j.succ ∈ S

/-- The initial segment `{i | i < m}`. -/
def iseg (N m : ℕ) : Finset (Fin N) := Finset.univ.filter fun i => i.val < m

/-- The ratio in Aomoto's formula. -/
def aomotoFactor (N : ℕ) (a b c : ℂ) (j : ℕ) : ℂ :=
  (a + ((N - 1 - j : ℕ) : ℂ) * c) / (a + b + ((2 * N - 2 - j : ℕ) : ℂ) * c)

/-- The Selberg integral as a function of its parameters. -/
def selbergInt (N : ℕ) (a b c : ℂ) : ℂ := ∫ t in cube N, selbergIntegrand N a b c t

/-- The reflection `t ↦ 1 - t` of the cube. -/
def reflect {N : ℕ} (t : Fin N → ℝ) : Fin N → ℝ := fun i => 1 - t i

/-- `∏_{i<j} (tᵢ - tⱼ)²`. -/
def vdmSq (N : ℕ) (t : Fin N → ℝ) : ℝ :=
  ∏ i : Fin N, ∏ j : Fin N, if i.val < j.val then (t i - t j) ^ 2 else 1

/-- The real weight `∏ tᵢ^{α-1}(1-tᵢ)^{β-1}`. -/
def weightR (N : ℕ) (α β : ℝ) (t : Fin N → ℝ) : ℝ :=
  ∏ i : Fin N, t i ^ (α - 1) * (1 - t i) ^ (β - 1)

end DLMF.Selberg
