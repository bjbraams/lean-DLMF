/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.ZonalSeries
public import DLMFMathlib.Analysis.SpecialFunctions.Trigonometric.PartialFractions

/-!
# Endpoint sum of the Legendre expansion coefficients

The ordered partial sums of `ZonalSeries.legendreCoeff ν n` tend to one for noninteger
`ν`. This follows from the secant partial-fraction expansion at `ν + 1/2` and supplies
the order-zero endpoint in Dougall's expansion, DLMF 14.18.9.
-/

open Complex Filter Set
open scoped Real Topology
@[expose] public section

namespace DLMF.Legendre.ZonalSeries

/-- The ordered partial sums of the Legendre coefficients tend to one at the endpoint. -/
theorem tendsto_sum_legendreCoeff {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, legendreCoeff ν n) atTop (𝓝 1) := by
  have hνmem : ν ∈ integerComplement := by
    rintro ⟨n, hn⟩
    exact hν n hn.symm
  have hx : ν + 1 / 2+1/2 ∈ integerComplement := by
    rintro ⟨n, hn⟩
    apply hν (n - 1)
    push_cast
    linear_combination -hn
  have hs := (Complex.tendsto_sec_partial_fraction hx).const_mul (-sin (ν * π)/π)
  have hcos : cos (π * (ν + 1 / 2))  = -sin (ν * π) := by
    rw [mul_add,show (π : ℂ)*(1/2)=π/2 by ring, cos_add_pi_div_two,mul_comm (π : ℂ) ν]
  have hsin : sin (ν * π) ≠ 0 := by
    simpa only [mul_comm] using sin_pi_mul_ne_zero hνmem
  rw [hcos] at hs
  have hvalue : -sin (ν * π)/π * ((π : ℂ)/ -sin (ν * π)) = 1 := by
    field_simp
  rw [hvalue] at hs
  convert hs using 1
  funext N
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [legendreCoeff, show ((n : ℂ)+1/2)^2-(ν + 1 / 2)^2 = -((ν - n)*(ν + n + 1)) by ring,
    div_neg]
  ring

end DLMF.Legendre.ZonalSeries
