/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import DLMF.Hypergeometric.Basic.Pochhammer
public import TauCeti.Analysis.SpecialFunctions.Erf
public import Mathlib.Analysis.Complex.IntegerCompl
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.Complex.AbsMax

/-!
# Kummer M and its defining coefficients
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open DLMF.Hypergeometric
open intervalIntegral

namespace DLMF.Confluent

/-- The coefficient of `z^n` in Kummer's confluent series. -/
abbrev kummerMCoeff (a c : ℂ) (n : ℕ) : ℂ :=
  poch a n / (poch c n * n !)

/-- Kummer's function `M(a,c,z) = ₁F₁(a;c;z)`. -/
@[dlmf 13.2.E2]
def kummerM (a c z : ℂ) : ℂ :=
  ∑' n : ℕ, poch a n / (poch c n * n !) * z ^ n

/-- `M(a,c,0) = 1`. -/
@[simp]
theorem kummerM_zero (a c : ℂ) : kummerM a c 0 = 1 := by
  unfold kummerM
  have h0 : (fun n : ℕ => poch a n / (poch c n * n !) * (0 : ℂ) ^ n) =
      fun n => if n = 0 then 1 else 0 := by
    ext n
    cases n with
    | zero => simp [poch_zero]
    | succ n => simp [pow_succ]
  rw [h0, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-- `₁F₁(0;c;z) = 1`. -/
@[dlmf 13.6.E3]
theorem kummerM_of_zero_param (c z : ℂ) : kummerM 0 c z = 1 := by
  unfold kummerM
  have h0 : (fun n : ℕ => poch 0 n / (poch c n * n !) * z ^ n) =
      fun n => if n = 0 then 1 else 0 := by
    ext n
    cases n with
    | zero => simp [poch_zero]
    | succ n => simp
  rw [h0, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

end DLMF.Confluent
