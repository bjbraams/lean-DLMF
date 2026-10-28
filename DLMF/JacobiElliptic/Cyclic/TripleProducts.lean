/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Cyclic.QuarterPeriodAndThreePoint

/-!
# Cyclic triple products of Jacobian elliptic functions

Cyclic relations among products and powers of three equally spaced Jacobian values.

Source references and common attribution are retained in
`DLMF.JacobiElliptic.Cyclic`.
-/

@[expose] public section

open Complex DLMF.Elliptic

open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

/-- DLMF 22.9.14: cyclic identity (three points, rank 3), at points where the
functions are finite. -/
@[dlmf 22.9.E7, dlmf 22.9.E14]
theorem jacobi_cyclic_c4_triple {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg4 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 4 m 3 z k) k) :
    jacobiCyclicC 4 1 3 z k * jacobiCyclicC 4 2 3 z k * jacobiCyclicC 4 3 3 z k =
      jacobiCyclicKappa k ^ 2 / (1 - jacobiCyclicKappa k ^ 2) * (jacobiCyclicC 4 1 3 z k +
        jacobiCyclicC 4 2 3 z k + jacobiCyclicC 4 3 3 z k) := by
  have V := p22R1_cyc43_vals hk z hreg4
  have W := p22R1_third_vals hk
  simp only at V W
  obtain ⟨hn, hD, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := V
  obtain ⟨hna, -, hsa, -, -, -, -, E1, E2⟩ := W
  obtain ⟨h1, h2⟩ := jacobi_sq_sum hk hn
  obtain ⟨ha1, ha2⟩ := jacobi_sq_sum hk hna
  have hκ := p22R1_kappa_ne hk
  have hk0 : k ≠ 0 := p22R1_k_ne hk
  simp only [jacobiCyclicKappa, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  generalize jacobiSnk z k = s at *
  generalize jacobiCnk z k = c at *
  generalize jacobiDnk z k = d at *
  generalize jacobiSnk (2 * compEllIntKk k / 3) k = sa at *
  generalize jacobiCnk (2 * compEllIntKk k / 3) k = ca at *
  generalize jacobiDnk (2 * compEllIntKk k / 3) k = κ at *
  generalize hDdef : 1 - k ^ 2 * s ^ 2 * sa ^ 2 = D at hD ⊢
  have hE : 1 - κ ^ 2 ≠ 0 := by
    intro h; apply hsa; have : k ^ 2 * sa ^ 2 = 0 := by linear_combination ha2 + h
    simpa [hk0] using this
  have hF : 1 + κ ≠ 0 := by
    intro h; apply hE; have : κ = -1 := by linear_combination h
    rw [this]; ring
  have hX := mul_inv_cancel₀ hκ
  generalize κ⁻¹ = X at hX
  field_simp
  linear_combination (c*d^2*ca^4*κ^3*k^2*X-2*c*d^2*ca^2*κ^3*k^2*X-c*d^2*ca^2*κ^4-c*ca^4*κ*k^2*X
      +c*d^2*κ^3*k^2*X+c*d^2*ca^2*κ^2+c*d^2*κ^4+c*ca^2*κ*k^2*X-c*d^2*κ^2) * h1 +
      (-1/2*c*ca^4*κ^3-1/2*c*ca^4*κ^2*X-c*ca^4*κ^2+c*ca^2*κ^3+c*ca^3*κ*D-c*ca^2*κ^2*D+c*ca^2*κ^2*X
        -c*ca^2*κ*D*X-1/2*c*ca^3*κ+2*c*ca^2*κ^2+c*ca^3*D-c*ca^2*κ*D-1/2*c*ca^3-1/2*c*κ^3+c*ca^2*D
          -c*ca*κ*D+c*κ^2*D-1/2*c*κ^2*X+c*κ*D*X+1/2*c*ca*κ-c*κ^2-c*ca*D+c*κ*D+1/2*c*ca-c*D) * h2 +
      (-s^2*c*d^2*ca^2*κ^3*k^2*X-c^3*d^2*ca^2*κ^3*k^2*X+s^2*c*d^2*κ^3*k^2*X+c^3*d^2*κ^3*k^2*X
        +c*d^2*ca^2*κ^3*k^2*X+1/2*c*d^2*sa^2*ca*κ*k^2*D*X+1/4*c*sa^2*ca*k^4*D*X^2
          +1/2*s^2*c*ca^2*κ^3*k^2+1/2*c*d^2*sa^2*ca*κ*k^2*D+1/2*c*d^2*ca^2*κ^4*X
            +1/2*s^2*c*ca^2*κ^2*k^2*X+1/2*c*d^2*sa^2*κ*k^2*D*X+1/2*c*sa^2*ca*k^4*D*X
              -1/4*c*sa^2*ca*k^4*X^2+1/4*c*sa^2*k^4*D*X^2+s^2*c*d^2*κ^4+s^2*c*ca^2*κ^2*k^2
                -1/2*c*d^2*sa^2*ca*k^2*D+1/2*c*d^2*sa^2*κ*k^2*D+s^2*c*ca^2*κ*k^2*X
                  +c^3*ca^2*κ*k^2*X-c*d^2*κ^3*k^2*X-1/2*c*sa^2*ca*k^4*X-1/2*c*d^2*ca*κ^3*D*X
                    -1/2*c*d^2*sa^2*k^2*D*X+1/2*c*ca^2*κ^2*k^2*D*X+1/2*c*sa^2*k^4*D*X
                      -1/4*c*sa^2*k^4*X^2-1/4*c*sa^2*ca*k^2*D*X^2-1/4*c*ca*κ^2*k^2*D*X^2
                        +1/4*c*d^2*sa^2*ca*k^2-1/2*s^2*c*κ^3*k^2+1/2*c*d^2*ca*κ^3*D
                          -c*d^2*sa^2*k^2*D-s^2*c*ca*κ*k^2*D+s^2*c*κ^2*k^2*D-1/2*c*d^2*κ^4*X
                            -1/2*c*ca^2*κ^4*X+1/4*c*d^2*sa^2*k^2*X-1/2*s^2*c*κ^2*k^2*X
                              -1/2*c*ca^2*κ^2*k^2*X-1/2*c*sa^2*k^4*X+1/2*c*d^2*κ^3*D*X
                                -c*sa^2*ca*k^2*D*X+s^2*c*κ*k^2*D*X-3/4*c*sa^2*κ*k^2*D*X
                                  +1/2*c*ca*κ^2*k^2*D*X+1/2*c*sa^2*k^2*D^2*X+1/4*c*sa^2*ca*k^2*X^2
                                    +1/4*c*ca*κ^2*k^2*X^2-1/4*c*sa^2*k^2*D*X^2-1/4*c*κ^2*k^2*D*X^2
                                      -s^2*c*d^2*κ^2+1/4*c*d^2*sa^2*k^2+1/2*s^2*c*ca*κ*k^2
                                        -s^2*c*κ^2*k^2-1/2*c*d^2*ca*κ^2*D+1/2*c*d^2*κ^3*D
                                          -s^2*c*ca*k^2*D-1/4*c*sa^2*ca*k^2*D+s^2*c*κ*k^2*D
                                            -3/4*c*sa^2*κ*k^2*D-1/2*c*ca^2*κ*k^2*D
                                              +1/2*c*sa^2*k^2*D^2+1/2*c*sa^2*ca*k^2*X
                                                -1/4*c*sa^2*κ*k^2*X-c*ca^2*κ*k^2*X
                                                  -1/2*c*ca*κ^2*k^2*X+1/2*c*d^2*κ^2*D*X
                                                    -3/4*c*sa^2*k^2*D*X-1/2*c*ca^2*k^2*D*X
                                                      +1/2*c*ca*κ*k^2*D*X+1/4*c*sa^2*k^2*X^2
                                                        +1/4*c*κ^2*k^2*X^2+1/4*c*ca*κ^2*D*X^2
                                                          +1/4*c*d^2*ca*κ^2+1/2*s^2*c*ca*k^2
                                                            -1/4*c*sa^2*κ*k^2+1/2*c*ca^2*κ*k^2
                                                              -c*d^2*κ^2*D-s^2*c*k^2*D
                                                                -c*ca^2*k^2*D-1/4*c*d^2*κ^2*X
                                                                  +1/2*c*κ^4*X+1/2*c*sa^2*k^2*X
                                                                    +1/2*c*ca^2*k^2*X
                                                                      +1/2*c*ca*κ^2*D*X
                                                                        -1/4*c*κ^3*D*X
                                                                          -1/2*c*ca*k^2*D*X
                                                                            +1/2*c*κ*k^2*D*X
                                                                              -1/2*c*κ^2*D^2*X
                                                                                -1/4*c*ca*κ^2*X^2
                                                                                  +1/4*c*κ^2*D*X^2
                                                                                    +1/4*c*d^2*κ^2
                                                                                      +1/4*c*sa^2*k^2+c*ca^2*k^2-1/4*c*ca*κ^2*D-3/4*c*κ^3*D-c*ca*k^2*D+1/2*c*κ*k^2*D+1/2*c*κ^2*D^2+1/4*c*κ^3*X+1/2*c*ca*k^2*X-1/2*c*κ*k^2*X+1/4*c*κ^2*D*X-1/4*c*κ^2*X^2-1/4*c*κ^3+1/2*c*ca*k^2-1/2*c*κ*k^2+1/4*c*κ^2) * ha1 +
      (c^3*d^2*ca^2*κ^3*X-c^3*d^2*κ^3*X-c*d^2*ca^2*κ^3*X-1/2*c*d^2*ca^3*κ*D*X-1/4*c*ca^3*k^2*D*X^2
        -1/2*c*d^2*ca^3*κ*D-1/2*c*d^2*ca^2*κ*D*X-1/2*c*ca^3*k^2*D*X+1/4*c*ca^3*k^2*X^2
          -1/4*c*ca^2*k^2*D*X^2+1/2*c*d^2*ca^3*D-1/2*c*d^2*ca^2*κ*D-c^3*ca^2*κ*X+c*d^2*κ^3*X
            +1/2*c*ca^3*k^2*X+1/2*c*d^2*ca^2*D*X+1/2*c*d^2*ca*κ*D*X-1/2*c*ca^2*k^2*D*X
              +1/4*c*ca^2*k^2*X^2+1/4*c*ca^3*D*X^2+1/4*c*ca*k^2*D*X^2-1/4*c*d^2*ca^3+c*d^2*ca^2*D
                +1/2*c*d^2*ca*κ*D-1/4*c*d^2*ca^2*X+1/2*c*ca^2*k^2*X+c*ca^3*D*X+1/2*c*d^2*κ*D*X
                  +3/4*c*ca^2*κ*D*X+1/2*c*ca*k^2*D*X-1/2*c*ca^2*D^2*X-1/4*c*ca^3*X^2
                    -1/4*c*ca*k^2*X^2+1/4*c*ca^2*D*X^2+1/4*c*k^2*D*X^2-1/4*c*d^2*ca^2
                      -1/2*c*d^2*ca*D+1/4*c*ca^3*D+1/2*c*d^2*κ*D+5/4*c*ca^2*κ*D-1/2*c*ca^2*D^2
                        -1/2*c*ca^3*X+5/4*c*ca^2*κ*X-1/2*c*ca*k^2*X-1/2*c*d^2*D*X+5/4*c*ca^2*D*X
                          -1/2*c*ca*κ*D*X+1/2*c*k^2*D*X-1/4*c*ca^2*X^2-1/4*c*k^2*X^2
                            -1/4*c*ca*D*X^2+1/4*c*d^2*ca-1/4*c*ca^2*κ-c*d^2*D+c*ca^2*D+1/4*c*d^2*X
                              -c*ca^2*X-1/2*c*k^2*X-1/2*c*ca*D*X-5/4*c*κ*D*X+1/2*c*D^2*X
                                +1/4*c*ca*X^2-1/4*c*D*X^2+1/4*c*d^2-5/4*c*ca^2+3/4*c*ca*D
                                  -5/4*c*κ*D+1/2*c*D^2+1/4*c*κ*X-3/4*c*D*X+1/4*c*X^2-1/2*c*ca
                                    +1/4*c*κ+1/2*c*X+1/4*c) * ha2 +
      (1/2*c*d^2*ca*κ*D*X+1/4*c*ca*k^2*D*X^2+1/2*c*d^2*ca*κ*D+1/2*c*d^2*κ*D*X+1/2*c*ca*k^2*D*X
        -1/4*c*ca*k^2*X^2+1/4*c*k^2*D*X^2-1/2*c*d^2*ca*D+1/2*c*d^2*κ*D-1/2*c*ca*k^2*X
          -1/2*c*d^2*D*X+1/2*c*k^2*D*X-1/4*c*k^2*X^2-1/4*c*ca*D*X^2+1/4*c*d^2*ca-c*d^2*D
            +1/4*c*d^2*X-1/2*c*k^2*X-c*ca*D*X-3/4*c*κ*D*X+1/2*c*D^2*X+1/4*c*ca*X^2-1/4*c*D*X^2
              +1/4*c*d^2-1/4*c*ca*D-3/4*c*κ*D+1/2*c*D^2+1/2*c*ca*X-1/4*c*κ*X-3/4*c*D*X+1/4*c*X^2
                -1/4*c*κ+1/2*c*X+1/4*c) * E1 +
      (1/2*c*d^2*ca^2*κ^2*X-1/2*c*d^2*ca*κ*D*X+1/2*c*ca^2*k^2*D*X-1/4*c*ca*k^2*D*X^2
        +1/2*c*d^2*ca*κ*D-1/2*c*d^2*κ^2*X-1/2*c*ca^2*κ^2*X-1/2*c*ca^2*k^2*X+1/2*c*d^2*κ*D*X
          +1/2*c*ca*k^2*D*X+1/4*c*ca*k^2*X^2-1/4*c*k^2*D*X^2-1/2*c*d^2*ca*D+1/2*c*d^2*κ*D
            -1/2*c*ca*k^2*X+1/2*c*d^2*D*X+1/4*c*k^2*X^2+1/4*c*ca*D*X^2+1/4*c*d^2*ca-c*d^2*D
              -1/4*c*d^2*X+1/2*c*κ^2*X+1/2*c*ca*D*X-1/4*c*κ*D*X-1/2*c*D^2*X-1/4*c*ca*X^2
                +1/4*c*D*X^2+1/4*c*d^2-1/4*c*ca*D-3/4*c*κ*D+1/2*c*D^2+1/4*c*κ*X+1/4*c*D*X
                  -1/4*c*X^2-1/4*c*κ+1/4*c) * E2 +
      (-c*d^2*ca^2*κ^3*X+c*d^2*κ^3*X+1/2*c*ca^2*κ^3+1/2*c*ca^2*κ^2*X+c*ca^2*κ^2+c*ca^2*κ*X
        -1/2*c*κ^3-c*ca*κ*D+c*κ^2*D-1/2*c*κ^2*X+c*κ*D*X+1/2*c*ca*κ-c*κ^2-c*ca*D+c*κ*D+1/2*c*ca
          -c*D) * hDdef +
      (-c^3*d^2*ca^2*κ^4-1/2*c*d^2*ca^4*κ^3+c^3*d^2*ca^2*κ^2-c*d^2*ca^4*κ^2+c^3*d^2*κ^4
        +c*d^2*ca^2*κ^4+c*d^2*ca^3*κ^2*D-1/2*c*ca^4*κ*k^2*D+1/2*c*ca^3*κ*k^2*D*X+c*d^2*ca^2*κ^3
          +1/2*c*ca^4*κ^3+1/2*c*ca^4*κ*k^2+c*d^2*ca^3*κ*D-c*d^2*ca^2*κ^2*D-c*ca^4*k^2*D
            -1/2*c*ca^3*κ*k^2*X+1/2*c*ca^3*k^2*D*X+1/2*c*ca^2*κ*k^2*D*X-c^3*d^2*κ^2+c^3*ca^2*κ^2
              +c*d^2*ca^2*κ^2+c*ca^4*κ^2-c*d^2*κ^4+c*ca^4*k^2-c*d^2*ca^2*κ*D-c*d^2*ca*κ^2*D
                -c*ca^3*k^2*D+c*ca^2*κ*k^2*D-1/2*c*ca^3*k^2*X-1/2*c*ca^2*κ*k^2*X-1/2*c*ca^3*κ*D*X
                  +c*ca^2*k^2*D*X-1/2*c*ca*κ*k^2*D*X-1/2*c*d^2*κ^3-c*ca^2*κ^3+1/2*c*ca^3*k^2
                    -c*ca^2*κ*k^2-c*d^2*ca^2*D+c*d^2*ca*κ*D-3/2*c*ca^3*κ*D+c*d^2*κ^2*D
                      -1/2*c*ca^2*κ^2*D+c*ca^2*k^2*D+c*ca^2*κ*D^2+1/2*c*ca^3*κ*X-c*ca^2*k^2*X
                        +1/2*c*ca*κ*k^2*X-1/2*c*ca^3*D*X-1/2*c*ca^2*κ*D*X+1/2*c*ca*k^2*D*X
                          -1/2*c*κ*k^2*D*X-c^3*ca^2+1/2*c*d^2*ca^2+1/2*c*ca^3*κ-5/2*c*ca^2*κ^2
                            -c*ca^2*k^2-c*d^2*ca*D-3/2*c*ca^3*D+c*d^2*κ*D-1/2*c*ca^2*κ*D
                              +1/2*c*ca*κ^2*D+c*ca*k^2*D-1/2*c*κ*k^2*D+c*ca^2*D^2+1/2*c*ca^3*X
                                +1/2*c*ca^2*κ*X-1/2*c*ca*k^2*X+1/2*c*κ*k^2*X-c*ca^2*D*X
                                  +1/2*c*ca*κ*D*X+1/2*c*d^2*ca+1/2*c*ca^3+1/2*c*ca^2*κ+1/2*c*κ^3
                                    -1/2*c*ca*k^2+1/2*c*κ*k^2-c*d^2*D-2*c*ca^2*D-1/2*c*ca*κ*D
                                      +c*κ^2*D+c*ca*D^2-c*κ*D^2+c*ca^2*X-1/2*c*ca*κ*X-1/2*c*ca*D*X
                                        +1/2*c*κ*D*X+3/2*c*ca^2-1/2*c*ca*κ-3/2*c*ca*D+1/2*c*κ*D
                                          +c*D^2+1/2*c*ca*X-1/2*c*κ*X+1/2*c*ca-1/2*c*κ) * hX

/-- DLMF 22.9.15: cyclic identity (three points, rank 3), at points where the
functions are finite. -/
@[dlmf 22.9.E7, dlmf 22.9.E15]
theorem jacobi_cyclic_d2_triple {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg2 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 2 m 3 z k) k) :
    jacobiCyclicD 2 1 3 z k * jacobiCyclicD 2 2 3 z k * jacobiCyclicD 2 3 3 z k =
      (jacobiCyclicKappa k ^ 2 + k ^ 2 - 1) / (1 - jacobiCyclicKappa k ^ 2) *
        (jacobiCyclicD 2 1 3 z k + jacobiCyclicD 2 2 3 z k + jacobiCyclicD 2 3 3 z k) := by
  have V := p22R1_cyc23_vals hk z hreg2
  have W := p22R1_third_vals hk
  simp only at V W
  obtain ⟨hn, hD, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := V
  obtain ⟨hna, -, hsa, -, -, -, -, E1, E2⟩ := W
  obtain ⟨h1, h2⟩ := jacobi_sq_sum hk hn
  obtain ⟨ha1, ha2⟩ := jacobi_sq_sum hk hna
  have hκ := p22R1_kappa_ne hk
  have hk0 : k ≠ 0 := p22R1_k_ne hk
  simp only [jacobiCyclicKappa, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  generalize jacobiSnk z k = s at *
  generalize jacobiCnk z k = c at *
  generalize jacobiDnk z k = d at *
  generalize jacobiSnk (2 * compEllIntKk k / 3) k = sa at *
  generalize jacobiCnk (2 * compEllIntKk k / 3) k = ca at *
  generalize jacobiDnk (2 * compEllIntKk k / 3) k = κ at *
  generalize hDdef : 1 - k ^ 2 * s ^ 2 * sa ^ 2 = D at hD ⊢
  have hE : 1 - κ ^ 2 ≠ 0 := by
    intro h; apply hsa; have : k ^ 2 * sa ^ 2 = 0 := by linear_combination ha2 + h
    simpa [hk0] using this
  have hF : 1 + κ ≠ 0 := by
    intro h; apply hE; have : κ = -1 := by linear_combination h
    rw [this]; ring
  have hX := mul_inv_cancel₀ hκ
  generalize κ⁻¹ = X at hX
  field_simp
  linear_combination (d^3*ca^4*κ^2*k^2-d^3*ca^4*k^2-d^3*ca^2*κ^2*k^2-d*ca^4*κ^2*k^2
      +1/2*d*ca^2*k^4*D*X+1/2*d*ca^2*k^4*X+d^3*ca^2*k^2+d*ca^4*k^2+d*ca^2*κ^2*k^2-1/2*d*k^4*D*X
        -1/2*d*k^4*X-d*ca^2*k^2-1/2*d*κ*k^2*D+1/2*d*k^2*D*X-1/2*d*κ*k^2+1/2*d*k^2*X) * h1 +
      (1/2*d^3*ca^6*κ^2-c^2*d*ca^4*κ^2*k^2+1/2*d^3*ca^6*κ*X+d^3*ca^6*κ+1/2*d^3*ca^5*κ
        -3/2*d^3*ca^4*κ^2+c^2*d*ca^4*k^2+c^2*d*ca^2*κ^2*k^2-1/2*d^3*ca^4*κ*X+1/2*d^3*ca^5
          -5/2*d^3*ca^4*κ-1/2*d^3*ca^4-d^3*ca^3*κ+3/2*d^3*ca^2*κ^2+d*ca^4*κ^2-c^2*d*ca^2*k^2
            +1/2*d*ca^2*κ^3*D+1/2*d^3*ca^2*κ*X+1/2*d*ca^2*κ^2*D*X-d^3*ca^3+2*d^3*ca^2*κ+4*d*ca^4*κ
              -7/2*d*ca^2*κ^3-2*d*ca^2*κ*k^2+2*d*ca^4*X-7/2*d*ca^2*κ^2*X-2*d*ca^2*k^2*X
                -d*ca^2*κ*D*X+5*d*ca^4+1/2*d^3*ca*κ+2*d*ca^3*κ-1/2*d^3*κ^2-6*d*ca^2*κ^2
                  -4*d*ca^2*k^2-1/2*d*ca^2*κ*D-1/2*d*κ^3*D+3*d*ca^3*X-1/2*d^3*κ*X+2*d*ca^2*κ*X
                    -1/2*d*ca^2*D*X-1/2*d*κ^2*D*X+1/2*d^3*ca+5*d*ca^3-1/2*d^3*κ-5/2*d*ca^2*κ
                      +7/2*d*κ^3+2*d*κ*k^2+d*ca^2*D-1/2*d*ca^2*X+7/2*d*κ^2*X+2*d*k^2*X+d*κ*D*X
                        +1/2*d^3-6*d*ca^2-2*d*ca*κ+5*d*κ^2+4*d*k^2+d*κ*D-3*d*ca*X-2*d*κ*X-5*d*ca
                          -d*κ-d*D-2*d*X+d) * h2 +
      (-1/2*d^3*sa^2*ca^3*κ^2*k^4*X-1/2*d^5*sa^2*ca^3*κ*k^2*X-1/2*d^3*sa^2*ca^2*κ^2*k^4*X
        -1/2*d^5*sa^2*ca^3*κ*k^2-1/2*s^2*d^3*ca^4*κ^2*k^2+s^2*c^2*d*ca^2*κ^2*k^4
          -1/2*d^5*ca^4*κ^3*X+1/4*d^5*sa^2*ca^3*k^2*X-1/2*d^5*sa^2*ca^2*κ*k^2*X
            -1/2*s^2*d^3*ca^4*κ*k^2*X-1/2*d^3*ca^3*κ^4*k^2*X+1/2*d^3*sa^2*ca^3*k^4*X
              +1/2*d^3*sa^2*ca^2*κ*k^4*X+1/2*d*sa^2*ca^3*κ^2*k^4*X+1/4*d^3*sa^2*ca^3*κ*k^2*D*X
                -1/2*d^5*sa^2*ca^2*κ*k^2-s^2*d^3*ca^4*κ*k^2+1/4*d^3*sa^2*ca^3*κ*k^2*D
                  +1/2*d^5*ca^3*κ^3*X-1/4*d^5*sa^2*ca^2*k^2*X+3/4*d^3*sa^2*ca^3*κ*k^2*X
                    +d^3*ca^3*κ^3*k^2*X-1/2*d^3*ca^2*κ^4*k^2*X+d^3*sa^2*ca*κ*k^4*X
                      +1/2*d*sa^2*ca^2*κ^2*k^4*X+1/4*d^3*sa^2*ca^3*k^2*D*X
                        +1/4*d^3*sa^2*ca^2*κ*k^2*D*X-d^3*sa^2*ca*k^4*X^2-1/2*d^5*ca^3*κ^3
                          +1/2*d^5*sa^2*ca^2*k^2-1/2*s^2*d^3*ca^3*κ*k^2+3/4*d^3*sa^2*ca^3*κ*k^2
                            -s^2*c^2*d*ca^2*k^4+1/4*d^3*sa^2*ca^3*k^2*D+1/4*d^3*sa^2*ca^2*κ*k^2*D
                              -1/4*d^5*ca^3*κ^2*X+1/2*d^5*ca^2*κ^3*X+1/2*d^3*ca^4*κ^3*X
                                +1/4*d^5*sa^2*ca*k^2*X-d^3*sa^2*ca^3*k^2*X
                                  +3/4*d^3*sa^2*ca^2*κ*k^2*X+1/2*d^3*ca^3*κ^2*k^2*X
                                    +3/2*d^3*ca^2*κ^3*k^2*X+1/2*d*ca^3*κ^4*k^2*X
                                      -3/2*d^3*sa^2*ca*k^4*X-1/2*d*sa^2*ca^3*k^4*X
                                        +d^3*sa^2*κ*k^4*X-1/2*d*sa^2*ca^2*κ*k^4*X
                                          -1/4*d^3*ca^3*κ^3*D*X+1/4*d^3*sa^2*ca^2*k^2*D*X
                                            +1/4*d^3*sa^2*ca*κ*k^2*D*X-3/2*d^3*sa^2*k^4*X^2
                                              -1/2*d^5*ca^2*κ^3+1/2*d^5*sa^2*ca*k^2
                                                -1/2*s^2*d^3*ca^3*k^2-3/4*d^3*sa^2*ca^3*k^2
                                                  +3/2*s^2*d^3*ca^2*κ*k^2+3/4*d^3*sa^2*ca^2*κ*k^2
                                                    +1/4*d^3*ca^3*κ^3*D+1/4*d^3*sa^2*ca^2*k^2*D
                                                      +1/4*d^3*sa^2*ca*κ*k^2*D+1/4*d^5*ca^2*κ^2*X
                                                        -3/4*d^3*ca^3*κ^3*X+1/4*d^5*sa^2*k^2*X
                                                          -5/4*d^3*sa^2*ca*κ*k^2*X
                                                            -d^3*ca^3*κ*k^2*X
                                                              -1/2*d*sa^2*ca^3*κ*k^2*X
                                                                -d^3*ca^2*κ^2*k^2*X
                                                                  +d^3*ca*κ^3*k^2*X
                                                                    -d*ca^3*κ^3*k^2*X
                                                                      +1/2*d*ca^2*κ^4*k^2*X
                                                                        -5/2*d^3*sa^2*k^4*X
                                                                          -d*sa^2*ca*κ*k^4*X
                                                                            -1/4*d^3*ca^3*κ^2*D*X
                                                                              -1/4*d^3*ca^2*κ^3*D*X-3/4*d^3*sa^2*ca*k^2*D*X+1/4*d^3*sa^2*κ*k^2*D*X+d^3*ca*κ^2*k^2*X^2+d*sa^2*ca*k^4*X^2+1/2*d^5*ca^2*κ^2+3/4*d^3*ca^3*κ^3+1/2*d^5*sa^2*k^2+3/2*s^2*d^3*ca^2*k^2-7/4*d^3*sa^2*ca^2*k^2+1/2*s^2*d^3*ca*κ*k^2-5/4*d^3*sa^2*ca*κ*k^2-d^3*ca^3*κ*k^2-1/2*d*sa^2*ca^3*κ*k^2-1/2*s^2*d^3*κ^2*k^2+1/4*d^3*ca^3*κ^2*D+1/4*d^3*ca^2*κ^3*D-3/4*d^3*sa^2*ca*k^2*D+1/4*d^3*sa^2*κ*k^2*D-1/2*s^2*d*κ^3*k^2*D-1/4*d^5*ca*κ^2*X+d^3*ca^3*κ^2*X-1/2*d^5*κ^3*X-3/4*d^3*ca^2*κ^3*X-d^3*sa^2*ca*k^2*X+1/2*d*sa^2*ca^3*k^2*X-1/2*s^2*d^3*κ*k^2*X-11/4*d^3*sa^2*κ*k^2*X-2*d^3*ca^2*κ*k^2*X-1/2*d*sa^2*ca^2*κ*k^2*X-7/2*d^3*ca*κ^2*k^2*X-1/2*d*ca^3*κ^2*k^2*X-3/2*d*ca^2*κ^3*k^2*X+3/2*d*sa^2*ca*k^4*X-d*sa^2*κ*k^4*X-1/4*d^3*ca^2*κ^2*D*X-1/4*d^3*ca*κ^3*D*X-1/2*d^3*κ^4*D*X-1/4*d^3*sa^2*k^2*D*X-1/2*s^2*d*κ^2*k^2*D*X-1/2*s^2*d*k^4*D*X-1/2*c^2*d*k^4*D*X+3/2*d^3*κ^2*k^2*X^2+3/2*d*sa^2*k^4*X^2+d*sa^2*ca*k^2*D*X^2+1/2*d^5*ca*κ^2-3/4*d^3*ca^3*κ^2+3/4*d^3*ca^2*κ^3+1/2*s^2*d^3*ca*k^2-3/4*d^3*sa^2*ca*k^2+d^3*ca^3*k^2+1/2*d*sa^2*ca^3*k^2-1/2*s^2*d^3*κ*k^2-11/4*d^3*sa^2*κ*k^2-4*s^2*d*ca^2*κ*k^2-d^3*ca^2*κ*k^2-1/2*d*sa^2*ca^2*κ*k^2+7/2*s^2*d*κ^3*k^2+2*s^2*d*κ*k^4+1/4*d^3*ca^2*κ^2*D+1/4*d^3*ca*κ^3*D-5/4*d^3*sa^2*k^2*D-1/4*d^5*κ^2*X-2*d^3*ca^2*κ^2*X+5/4*d^3*ca*κ^3*X+1/2*d*ca^3*κ^3*X+7/2*d^3*κ^4*X-d^3*sa^2*k^2*X-2*s^2*d*ca^2*k^2*X+2*d^3*ca^2*k^2*X-2*d^3*ca*κ*k^2*X+d*sa^2*ca*κ*k^2*X+d*ca^3*κ*k^2*X+7/2*s^2*d*κ^2*k^2*X-1/2*d^3*κ^2*k^2*X+d*ca^2*κ^2*k^2*X-d*ca*κ^3*k^2*X+3/2*s^2*d*k^4*X-1/2*c^2*d*k^4*X+5/2*d*sa^2*k^4*X+3/4*d^3*ca*κ^2*D*X+3/4*d^3*κ^3*D*X+3*d*sa^2*ca*k^2*D*X+s^2*d*κ*k^2*D*X-1/2*d*κ^2*k^2*D^2*X-d*sa^2*ca*k^2*X^2-d*ca*κ^2*k^2*X^2+3/2*d*sa^2*k^2*D*X^2+1/2*d^5*κ^2-7/4*d^3*ca^2*κ^2-5/4*d^3*ca*κ^3-1/2*d*ca^3*κ^3+1/2*s^2*d^3*k^2+3/4*d^3*sa^2*k^2-6*s^2*d*ca^2*k^2+4*d^3*ca^2*k^2+d*sa^2*ca^2*k^2-2*s^2*d*ca*κ*k^2+d*sa^2*ca*κ*k^2+d*ca^3*κ*k^2+5*s^2*d*κ^2*k^2+d^3*κ^2*k^2+4*s^2*d*k^4-3/4*d^3*ca*κ^2*D+1/4*d^3*κ^3*D+2*d*sa^2*ca*k^2*D+1/2*s^2*d*κ*k^2*D-2*d^3*ca*κ^2*X-1/2*d*ca^3*κ^2*X+5/4*d^3*κ^3*X+1/2*d*ca^2*κ^3*X-3*s^2*d*ca*k^2*X+3*d^3*ca*k^2*X-3/2*d*sa^2*ca*k^2*X-2*s^2*d*κ*k^2*X-4*d^3*κ*k^2*X+5/2*d*sa^2*κ*k^2*X+2*d*ca^2*κ*k^2*X+7/2*d*ca*κ^2*k^2*X-d*κ^3*k^2*X+3/4*d^3*κ^2*D*X+1/2*d*κ^4*D*X+1/2*s^2*d*k^2*D*X+7/2*d*sa^2*k^2*D*X+2*d*κ^2*k^2*D*X+1/2*d*k^4*D*X-3/2*d*sa^2*k^2*X^2-3/2*d*κ^2*k^2*X^2-d*ca*κ^2*D*X^2-3/4*d^3*ca*κ^2+1/2*d*ca^3*κ^2-11/4*d^3*κ^3-1/2*d*ca^2*κ^3-5*s^2*d*ca*k^2+5*d^3*ca*k^2-d*sa^2*ca*k^2-d*ca^3*k^2-3/2*s^2*d*κ*k^2+5/2*d*sa^2*κ*k^2+d*ca^2*κ*k^2-5/4*d^3*κ^2*D-s^2*d*k^2*D+3*d*sa^2*k^2*D+1/2*d*κ*k^2*D^2-1/2*d^3*κ^2*X+2*d*ca^2*κ^2*X-d*ca*κ^3*X-7/2*d*κ^4*X-3/2*s^2*d*k^2*X+2*d^3*k^2*X-5/2*d*sa^2*k^2*X-2*d*ca^2*k^2*X+4*d*ca*κ*k^2*X-d*κ^2*k^2*X+1/2*d*k^4*X-d*ca*κ^2*D*X-d*κ^3*D*X+1/2*d*k^2*D^2*X+d*ca*κ^2*X^2-3/2*d*κ^2*D*X^2+3/4*d^3*κ^2+d*ca^2*κ^2+d*ca*κ^3+s^2*d*k^2+5*d^3*k^2-3*d*sa^2*k^2-4*d*ca^2*k^2+2*d*ca*κ^2*D-2*d*κ*k^2*D+d*k^2*D^2+5/2*d*ca*κ^2*X-1/2*d*κ^3*X-3*d*ca*k^2*X+5*d*κ*k^2*X-d*κ^2*D*X-2*d*k^2*D*X+3/2*d*κ^2*X^2-d*ca*κ^2+5/2*d*κ^3-7*d*ca*k^2+7/2*d*κ*k^2+3*d*κ^2*D-4*d*k^2*D+d*κ^2*X-1/2*d*k^2*X-3*d*κ^2-2*d*k^2) * ha1 +
      (1/2*d^3*ca^5*κ^2*k^2*X+1/2*d^5*ca^5*κ*X+1/2*d^3*ca^4*κ^2*k^2*X+1/2*d^5*ca^5*κ
        -1/4*d^5*ca^5*X+1/2*d^5*ca^4*κ*X-1/2*d^3*ca^5*k^2*X-1/2*d^3*ca^4*κ*k^2*X
          -1/2*d^3*ca^3*κ^2*k^2*X-1/2*d*ca^5*κ^2*k^2*X-1/4*d^3*ca^5*κ*D*X+1/2*d^5*ca^4*κ
            -1/4*d^3*ca^5*κ*D+1/4*d^5*ca^4*X-1/2*d^5*ca^3*κ*X-3/4*d^3*ca^5*κ*X-d^3*ca^3*κ*k^2*X
              -1/2*d^3*ca^2*κ^2*k^2*X-1/2*d*ca^4*κ^2*k^2*X-1/4*d^3*ca^5*D*X-1/4*d^3*ca^4*κ*D*X
                +d^3*ca^3*k^2*X^2-1/2*d^5*ca^4-1/2*d^5*ca^3*κ-3/4*d^3*ca^5*κ-1/4*d^3*ca^5*D
                  -1/4*d^3*ca^4*κ*D+d^3*ca^5*X-1/2*d^5*ca^2*κ*X-3/4*d^3*ca^4*κ*X-d^3*ca^3*κ^2*X
                    +2*d^3*ca^3*k^2*X+1/2*d*ca^5*k^2*X-1/2*d^3*ca^2*κ*k^2*X+1/2*d*ca^4*κ*k^2*X
                      +1/2*d*ca^3*κ^2*k^2*X-1/4*d^3*ca^4*D*X+3/2*d^3*ca^2*k^2*X^2-1/2*d^5*ca^3
                        +3/4*d^3*ca^5-1/2*d^5*ca^2*κ-3/4*d^3*ca^4*κ-1/4*d^3*ca^4*D-1/2*d^5*ca^2*X
                          +3*d^3*ca^3*κ*X+1/2*d*ca^5*κ*X-d^3*ca^2*κ^2*X+5/2*d^3*ca^2*k^2*X
                            +d^3*ca*κ*k^2*X+d*ca^3*κ*k^2*X+1/2*d*ca^2*κ^2*k^2*X+d^3*ca^3*D*X
                              -d^3*ca*k^2*X^2-d*ca^3*k^2*X^2+7/4*d^3*ca^4+3*d^3*ca^3*κ
                                +1/2*d*ca^5*κ+d^3*ca^3*D+1/4*d^5*ca*X-1/2*d*ca^5*X
                                  +11/2*d^3*ca^2*κ*X+1/2*d*ca^4*κ*X+d*ca^3*κ^2*X-3/2*d^3*ca*k^2*X
                                    -2*d*ca^3*k^2*X+d^3*κ*k^2*X+1/2*d*ca^2*κ*k^2*X
                                      +1/2*d^3*ca^2*D*X+1/4*d^3*ca*κ*D*X+1/2*c^2*d*k^2*D*X
                                        -3/2*d^3*k^2*X^2-3/2*d*ca^2*k^2*X^2-d*ca^3*D*X^2
                                          +1/2*d^5*ca-d^3*ca^3-1/2*d*ca^5+9/2*d^3*ca^2*κ
                                            +1/2*d*ca^4*κ+3/2*d^3*ca^2*D+1/4*d^3*ca*κ*D+1/4*d^5*X
                                              -d^3*ca^2*X+3/4*d^3*ca*κ*X-5/2*d*ca^3*κ*X
                                                +d*ca^2*κ^2*X+1/2*c^2*d*k^2*X-5/2*d^3*k^2*X
                                                  -5/2*d*ca^2*k^2*X-d*ca*κ*k^2*X-3/4*d^3*ca*D*X
                                                    -3*d*ca^3*D*X+1/4*d^3*κ*D*X+d*ca^3*X^2
                                                      +d*ca*k^2*X^2-3/2*d*ca^2*D*X^2+1/2*d^5
                                                        -13/2*d^3*ca^2-d*ca^4-5/4*d^3*ca*κ
                                                          -5/2*d*ca^3*κ-d^3*κ^2-3/4*d^3*ca*D
                                                            -2*d*ca^3*D+1/4*d^3*κ*D-4*d^3*ca*X
                                                              +2*d*ca^3*X+5/4*d^3*κ*X-5*d*ca^2*κ*X
                                                                +3/2*d*ca*k^2*X-d*κ*k^2*X
                                                                  -1/4*d^3*D*X-7/2*d*ca^2*D*X
                                                                    -1/2*d*k^2*D*X+3/2*d*ca^2*X^2
                                                                      +3/2*d*k^2*X^2+d*ca*D*X^2
                                                                        -23/4*d^3*ca+5/2*d*ca^3
                                                                          -11/4*d^3*κ-4*d*ca^2*κ
                                                                            -5/4*d^3*D-3*d*ca^2*D
                                                                              -1/2*d*κ*D^2-3*d^3*X
                                                                                +9/2*d*ca^2*X
                                                                                  -3*d*ca*κ*X
                                                                                    +2*d*k^2*X+3*d*ca*D*X-1/2*d*D^2*X-d*ca*X^2+3/2*d*D*X^2-17/4*d^3+8*d*ca^2+d*ca*κ+2*d*ca*D+2*d*κ*D-d*D^2+3/2*d*ca*X-5/2*d*κ*X+11/2*d*D*X-3/2*d*X^2+6*d*ca-d*κ+7*d*D-2*d*X-d) * ha2 +
      (-1/2*d^3*ca^3*κ^2*k^2*X-1/2*d^5*ca^3*κ*X-1/2*d^3*ca^2*κ^2*k^2*X-1/2*d^5*ca^3*κ
        +1/4*d^5*ca^3*X-1/2*d^5*ca^2*κ*X+1/2*d^3*ca^3*k^2*X+1/2*d^3*ca^2*κ*k^2*X
          +1/2*d*ca^3*κ^2*k^2*X+1/4*d^3*ca^3*κ*D*X-1/2*d^5*ca^2*κ+1/4*d^3*ca^3*κ*D-1/4*d^5*ca^2*X
            +3/4*d^3*ca^3*κ*X+d^3*ca*κ*k^2*X+1/2*d*ca^2*κ^2*k^2*X+1/4*d^3*ca^3*D*X
              +1/4*d^3*ca^2*κ*D*X-d^3*ca*k^2*X^2+1/2*d^5*ca^2+3/4*d^3*ca^3*κ+1/4*d^3*ca^3*D
                +1/4*d^3*ca^2*κ*D+1/4*d^5*ca*X-d^3*ca^3*X+3/4*d^3*ca^2*κ*X-3/2*d^3*ca*k^2*X
                  -1/2*d*ca^3*k^2*X+d^3*κ*k^2*X-1/2*d*ca^2*κ*k^2*X+1/4*d^3*ca^2*D*X
                    +1/4*d^3*ca*κ*D*X-3/2*d^3*k^2*X^2+1/2*d^5*ca-3/4*d^3*ca^3+3/4*d^3*ca^2*κ
                      +1/4*d^3*ca^2*D+1/4*d^3*ca*κ*D+1/4*d^5*X-5/4*d^3*ca*κ*X-1/2*d*ca^3*κ*X
                        -5/2*d^3*k^2*X-d*ca*κ*k^2*X-3/4*d^3*ca*D*X+1/4*d^3*κ*D*X+d*ca*k^2*X^2
                          +1/2*d^5-7/4*d^3*ca^2-5/4*d^3*ca*κ-1/2*d*ca^3*κ-3/4*d^3*ca*D+1/4*d^3*κ*D
                            -d^3*ca*X+1/2*d*ca^3*X-11/4*d^3*κ*X-1/2*d*ca^2*κ*X+3/2*d*ca*k^2*X
                              -d*κ*k^2*X-1/4*d^3*D*X+3/2*d*k^2*X^2+d*ca*D*X^2-3/4*d^3*ca
                                +1/2*d*ca^3-11/4*d^3*κ-1/2*d*ca^2*κ-5/4*d^3*D-d^3*X+d*ca*κ*X
                                  +5/2*d*k^2*X+3*d*ca*D*X-d*ca*X^2+3/2*d*D*X^2+3/4*d^3+d*ca^2
                                    +d*ca*κ+2*d*ca*D-3/2*d*ca*X+5/2*d*κ*X+7/2*d*D*X-3/2*d*X^2-d*ca
                                      +5/2*d*κ+3*d*D-5/2*d*X-3*d) * E1 +
      (-1/2*d^5*ca^4*κ*X-1/2*d^3*ca^3*κ^2*k^2*X+1/2*d^5*ca^3*κ*X+d^3*ca^3*κ*k^2*X
        -1/2*d^3*ca^2*κ^2*k^2*X-1/2*d^5*ca^3*κ-1/4*d^5*ca^3*X+1/2*d^5*ca^2*κ*X+1/2*d^3*ca^4*κ*X
          -1/2*d^3*ca^3*k^2*X+3/2*d^3*ca^2*κ*k^2*X+1/2*d*ca^3*κ^2*k^2*X-1/4*d^3*ca^3*κ*D*X
            -1/2*d^5*ca^2*κ+1/4*d^3*ca^3*κ*D+1/4*d^5*ca^2*X-3/4*d^3*ca^3*κ*X-2*d^3*ca^2*k^2*X
              +d^3*ca*κ*k^2*X-d*ca^3*κ*k^2*X+1/2*d*ca^2*κ^2*k^2*X-1/4*d^3*ca^3*D*X
                -1/4*d^3*ca^2*κ*D*X+d^3*ca*k^2*X^2+1/2*d^5*ca^2+3/4*d^3*ca^3*κ+1/4*d^3*ca^3*D
                  +1/4*d^3*ca^2*κ*D-1/4*d^5*ca*X+d^3*ca^3*X-1/2*d^5*κ*X-3/4*d^3*ca^2*κ*X
                    -7/2*d^3*ca*k^2*X+1/2*d*ca^3*k^2*X-3/2*d*ca^2*κ*k^2*X-1/4*d^3*ca^2*D*X
                      -1/4*d^3*ca*κ*D*X-1/2*d^3*κ^2*D*X+3/2*d^3*k^2*X^2+1/2*d^5*ca-3/4*d^3*ca^3
                        +3/4*d^3*ca^2*κ+1/4*d^3*ca^2*D+1/4*d^3*ca*κ*D-1/4*d^5*X-2*d^3*ca^2*X
                          +5/4*d^3*ca*κ*X+1/2*d*ca^3*κ*X+7/2*d^3*κ^2*X-1/2*d^3*k^2*X
                            +2*d*ca^2*k^2*X-d*ca*κ*k^2*X+3/4*d^3*ca*D*X+3/4*d^3*κ*D*X
                              -1/2*d*k^2*D^2*X-d*ca*k^2*X^2+1/2*d^5-7/4*d^3*ca^2-5/4*d^3*ca*κ
                                -1/2*d*ca^3*κ-3/4*d^3*ca*D+1/4*d^3*κ*D-2*d^3*ca*X-1/2*d*ca^3*X
                                  +5/4*d^3*κ*X+1/2*d*ca^2*κ*X+7/2*d*ca*k^2*X-d*κ*k^2*X+3/4*d^3*D*X
                                    +1/2*d*κ^2*D*X+2*d*k^2*D*X-3/2*d*k^2*X^2-d*ca*D*X^2-3/4*d^3*ca
                                      +1/2*d*ca^3-11/4*d^3*κ-1/2*d*ca^2*κ-5/4*d^3*D-1/2*d^3*X
                                        +2*d*ca^2*X-d*ca*κ*X-7/2*d*κ^2*X-d*k^2*X-d*ca*D*X-d*κ*D*X
                                          +d*ca*X^2-3/2*d*D*X^2+3/4*d^3+d*ca^2+d*ca*κ+2*d*ca*D
                                            +5/2*d*ca*X-1/2*d*κ*X-d*D*X+3/2*d*X^2-d*ca+5/2*d*κ
                                              +3*d*D+d*X-3*d) * E2 +
      (-1/2*d^3*ca^4*κ^2-1/2*d^3*ca^4*κ*X-d^3*ca^4*κ-1/2*d^3*ca^3*κ-1/2*d^3*ca^3+3/2*d^3*ca^2*κ
        +3/2*d^3*ca^2+1/2*d^3*ca*κ-1/2*d^3*κ^2-1/2*d*κ^3*D-1/2*d^3*κ*X-1/2*d*κ^2*D*X-1/2*d*k^2*D*X
          +1/2*d^3*ca-1/2*d^3*κ-4*d*ca^2*κ+7/2*d*κ^3+2*d*κ*k^2-2*d*ca^2*X+7/2*d*κ^2*X+3/2*d*k^2*X
            +d*κ*D*X+1/2*d^3-6*d*ca^2-2*d*ca*κ+5*d*κ^2+4*d*k^2+1/2*d*κ*D-3*d*ca*X-2*d*κ*X
              +1/2*d*D*X-5*d*ca-3/2*d*κ-d*D-3/2*d*X+d) * hDdef +
      (1/2*d^5*ca^6*κ^2+d^5*ca^6*κ-d^5*ca^5*κ^2-1/2*d^5*ca^5*κ-3/2*d^5*ca^4*κ^2-1/2*d^3*ca^6*κ^2
        -d^3*ca^5*κ*k^2-d^3*ca^4*κ^2*k^2+1/2*d^3*ca^5*κ^2*D+1/2*d^5*ca^5-5/2*d^5*ca^4*κ-d^3*ca^6*κ
          +d^5*ca^3*κ^2+3/2*d^3*ca^5*κ^2+d^3*ca^5*k^2-d^3*ca^4*κ*k^2+d^3*ca^5*κ*D
            +1/2*d^3*ca^4*κ^2*D-2*d^3*ca^3*κ*k^2*X+1/2*d^5*ca^4-d^5*ca^3*κ-1/2*d^3*ca^5*κ
              +3/2*d^5*ca^2*κ^2+2*d^3*ca^4*κ^2+d^3*ca^3*κ^3+5*d^3*ca^4*k^2+d^3*ca^3*κ*k^2
                +d*ca^5*κ*k^2+2*d^3*ca^2*κ^2*k^2+d*ca^4*κ^2*k^2+1/2*d^3*ca^5*D+3/2*d^3*ca^4*κ*D
                  +1/2*d^3*ca^2*κ^3*D-2*d^3*ca^3*k^2*X-3*d^3*ca^2*κ*k^2*X-2*d^3*ca^5+2*d^5*ca^2*κ
                    +5*d^3*ca^4*κ-5*d^3*ca^3*κ^2-d*ca^5*κ^2-5/2*d^3*ca^2*κ^3+4*d^3*ca^3*k^2
                      -d*ca^5*k^2-d^3*ca^2*κ*k^2+d*ca^4*κ*k^2+1/2*d^3*ca^4*D-d^3*ca^3*κ*D
                        +1/2*d*ca^2*κ*k^2*D^2-5*d^3*ca^2*k^2*X+2*d^3*ca*κ*k^2*X+2*d*ca^3*κ*k^2*X
                          +d^5*ca^2+2*d^3*ca^4-1/2*d^5*ca*κ+d^3*ca^3*κ-1/2*d^5*κ^2
                            -29/2*d^3*ca^2*κ^2-d*ca^4*κ^2-d*ca^3*κ^3-4*d^3*ca^2*k^2-5*d*ca^4*k^2
                              -d*ca^3*κ*k^2-d^3*κ^2*k^2-d*ca^2*κ^2*k^2-d^3*ca^3*D-5/2*d^3*ca^2*κ*D
                                -1/2*d^3*ca*κ^2*D-1/2*d^3*κ^3*D-1/2*d*ca^2*κ^3*D-1/2*c^2*d*κ*k^2*D
                                  -2*d*ca^2*κ*k^2*D+d*ca^2*k^2*D^2-3*d^3*ca*k^2*X+2*d*ca^3*k^2*X
                                    +3*d^3*κ*k^2*X+3*d*ca^2*κ*k^2*X+2*d*ca^3*κ*D*X+1/2*d^5*ca
                                      +5*d^3*ca^3+d*ca^5-1/2*d^5*κ-13/2*d^3*ca^2*κ-4*d*ca^4*κ
                                        +1/2*d^3*ca*κ^2+4*d*ca^3*κ^2+7/2*d^3*κ^3+5/2*d*ca^2*κ^3
                                          -5*d^3*ca*k^2-6*d*ca^3*k^2-1/2*c^2*d*κ*k^2+2*d^3*κ*k^2
                                            +9/2*d*ca^2*κ*k^2-3*d^3*ca^2*D+2*d^3*ca*κ*D
                                              +4*d*ca^3*κ*D+1/2*d^3*κ^2*D-4*d*ca^2*k^2*D
                                                -1/2*d*κ*k^2*D^2-2*d*ca^3*κ*X+5*d*ca^2*k^2*X
                                                  -2*d*ca*κ*k^2*X+2*d*ca^3*D*X+3*d*ca^2*κ*D*X
                                                    +1/2*d^5+d^3*ca^2-3*d*ca^4-7/2*d^3*ca*κ
                                                      -3*d*ca^3*κ+13*d*ca^2*κ^2-d^3*k^2
                                                        +7*d*ca^2*k^2-1/2*d^3*ca*D+4*d*ca^3*D
                                                          +3/2*d^3*κ*D+13/2*d*ca^2*κ*D+1/2*d*κ^3*D
                                                            +5/2*d*κ*k^2*D-2*d*ca^3*X-3*d*ca^2*κ*X
                                                              +3*d*ca*k^2*X-3*d*κ*k^2*X
                                                                +5*d*ca^2*D*X-2*d*ca*κ*D*X
                                                                  -8*d*ca^3-d^3*κ+1/2*d*ca^2*κ
                                                                    +2*d*ca*κ^2-7/2*d*κ^3
                                                                      +7*d*ca*k^2-3*d*κ*k^2
                                                                        -3/2*d^3*D+11*d*ca^2*D
                                                                          -4*d*ca*κ*D-d*κ^2*D
                                                                            -5*d*ca^2*X+2*d*ca*κ*X
                                                                              +3*d*ca*D*X
                                                                                -3*d*κ*D*X+6*d^3
                                                                                  -10*d*ca^2+6*d*ca*κ+2*d*κ^2+2*d*k^2+5*d*ca*D-3*d*κ*D+d*D^2-3*d*ca*X+3*d*κ*X-7*d*ca+3*d*κ-5*d*D-2*d) * hX

/-- DLMF 22.9.16: cyclic identity (three points, rank 3), at points where the
functions are finite. -/
@[dlmf 22.9.E7, dlmf 22.9.E16]
theorem jacobi_cyclic_scc_triple {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg4 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 4 m 3 z k) k) :
    jacobiCyclicS 4 1 3 z k * jacobiCyclicC 4 2 3 z k * jacobiCyclicC 4 3 3 z k +
      jacobiCyclicS 4 2 3 z k * jacobiCyclicC 4 3 3 z k * jacobiCyclicC 4 1 3 z k +
        jacobiCyclicS 4 3 3 z k * jacobiCyclicC 4 1 3 z k * jacobiCyclicC 4 2 3 z k =
          jacobiCyclicKappa k * (jacobiCyclicKappa k + 2) / (1 - jacobiCyclicKappa k ^ 2) *
            (jacobiCyclicS 4 1 3 z k + jacobiCyclicS 4 2 3 z k + jacobiCyclicS 4 3 3 z k) := by
  have V := p22R1_cyc43_vals hk z hreg4
  have W := p22R1_third_vals hk
  simp only at V W
  obtain ⟨hn, hD, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := V
  obtain ⟨hna, -, hsa, -, -, -, -, E1, E2⟩ := W
  obtain ⟨h1, h2⟩ := jacobi_sq_sum hk hn
  obtain ⟨ha1, ha2⟩ := jacobi_sq_sum hk hna
  have hκ := p22R1_kappa_ne hk
  have hk0 : k ≠ 0 := p22R1_k_ne hk
  simp only [jacobiCyclicKappa, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  generalize jacobiSnk z k = s at *
  generalize jacobiCnk z k = c at *
  generalize jacobiDnk z k = d at *
  generalize jacobiSnk (2 * compEllIntKk k / 3) k = sa at *
  generalize jacobiCnk (2 * compEllIntKk k / 3) k = ca at *
  generalize jacobiDnk (2 * compEllIntKk k / 3) k = κ at *
  generalize hDdef : 1 - k ^ 2 * s ^ 2 * sa ^ 2 = D at hD ⊢
  have hE : 1 - κ ^ 2 ≠ 0 := by
    intro h; apply hsa; have : k ^ 2 * sa ^ 2 = 0 := by linear_combination ha2 + h
    simpa [hk0] using this
  have hF : 1 + κ ≠ 0 := by
    intro h; apply hE; have : κ = -1 := by linear_combination h
    rw [this]; ring
  have hX := mul_inv_cancel₀ hκ
  generalize κ⁻¹ = X at hX
  field_simp
  linear_combination (s*d^2*ca^4*κ^3*k^2*X+2*s*d^2*ca^4*κ^2*k^2*X-2*s*d^2*ca^2*κ^3*k^2*X
      -4*s*d^2*ca^2*κ^2*k^2*X-2*s*ca^4*κ^2*k^2*X-s*d^2*ca^2*κ^4-s*ca^4*κ*k^2*X+s*d^2*κ^3*k^2*X
        +2*s*d^2*κ^2*k^2*X+2*s*ca^2*κ^2*k^2*X+s*d^2*ca^2*κ^2+s*d^2*κ^4+s*ca^2*κ*k^2*X
          -s*d^2*κ^2) * h1 +
      (3/2*s*ca^4*κ^3+3/2*s*ca^4*κ^2*X+3*s*ca^4*κ^2-2*s*ca^4*κ-s*ca^2*κ^3-s*ca^3*κ*D-s*ca^2*κ^2*D
        -2*s*ca^4*X-s*ca^2*κ^2*X-s*ca^2*κ*D*X-4*s*ca^4-1/2*s*ca^3*κ-2*s*ca^2*κ^2-s*ca^3*D
          -s*ca^2*κ*D-2*s*ca^3*X-5/2*s*ca^3+4*s*ca^2*κ-1/2*s*κ^3+s*ca^2*D+s*ca*κ*D+s*κ^2*D
            +2*s*ca^2*X-1/2*s*κ^2*X+s*κ*D*X+6*s*ca^2+1/2*s*ca*κ-s*κ^2+s*ca*D+s*κ*D+2*s*ca*X
              +5/2*s*ca-2*s*κ-s*D-2*s) * h2 +
      (-s^3*d^2*ca^2*κ^3*k^2*X-s*c^2*d^2*ca^2*κ^3*k^2*X-2*s^3*d^2*ca^2*κ^2*k^2*X
        -2*s*c^2*d^2*ca^2*κ^2*k^2*X+s*d^2*sa^2*ca*k^4*X^2+s^3*d^2*κ^3*k^2*X+s*c^2*d^2*κ^3*k^2*X
          +s*d^2*ca^2*κ^3*k^2*X+2*s*d^2*sa^2*ca*k^4*X+1/2*s*d^2*sa^2*ca*κ*k^2*D*X
            +s*d^2*sa^2*k^4*X^2-3/4*s*sa^2*ca*k^4*D*X^2-3/2*s^3*ca^2*κ^3*k^2
              +1/2*s*d^2*sa^2*ca*κ*k^2*D-3/2*s*d^2*ca^2*κ^4*X+2*s^3*d^2*κ^2*k^2*X
                +2*s*c^2*d^2*κ^2*k^2*X+1/2*s^3*ca^2*κ^2*k^2*X+2*s*c^2*ca^2*κ^2*k^2*X
                  +4*s*d^2*ca^2*κ^2*k^2*X+2*s*d^2*sa^2*k^4*X+1/2*s*d^2*sa^2*κ*k^2*D*X
                    -3/2*s*sa^2*ca*k^4*D*X-s*d^2*ca*κ^2*k^2*X^2-1/4*s*sa^2*ca*k^4*X^2
                      +1/4*s*sa^2*k^4*D*X^2+s^3*d^2*κ^4-3*s^3*ca^2*κ^2*k^2+1/2*s*d^2*sa^2*ca*k^2*D
                        +1/2*s*d^2*sa^2*κ*k^2*D+s*d^2*sa^2*κ*k^2*X+s^3*ca^2*κ*k^2*X
                          +s*c^2*ca^2*κ*k^2*X+2*s*d^2*ca*κ^2*k^2*X-s*d^2*κ^3*k^2*X
                            -1/2*s*sa^2*ca*k^4*X-1/2*s*d^2*ca*κ^3*D*X+1/2*s*d^2*sa^2*k^2*D*X
                              -3/2*s*ca^2*κ^2*k^2*D*X+1/2*s*sa^2*k^4*D*X-s*d^2*κ^2*k^2*X^2
                                -1/4*s*sa^2*k^4*X^2-1/4*s*sa^2*ca*k^2*D*X^2+3/4*s*ca*κ^2*k^2*D*X^2
                                  -2*s*c^2*d^2*κ^3-3/4*s*d^2*sa^2*ca*k^2+s*d^2*sa^2*κ*k^2
                                    +2*s^3*ca^2*κ*k^2-2*s*d^2*ca^2*κ*k^2-1/2*s^3*κ^3*k^2
                                      +1/2*s*d^2*ca*κ^3*D+s^3*ca*κ*k^2*D+s^3*κ^2*k^2*D
                                        +2*s*d^2*ca^2*κ^2*X-1/2*s*d^2*κ^4*X+3/2*s*ca^2*κ^4*X
                                          +1/4*s*d^2*sa^2*k^2*X+2*s^3*ca^2*k^2*X
                                            -2*s*d^2*ca^2*k^2*X+2*s*d^2*ca*κ*k^2*X
                                              -1/2*s^3*κ^2*k^2*X-2*s*d^2*κ^2*k^2*X
                                                -5/2*s*ca^2*κ^2*k^2*X-1/2*s*sa^2*k^4*X
                                                  +1/2*s*d^2*κ^3*D*X-s*sa^2*ca*k^2*D*X
                                                    +s^3*κ*k^2*D*X-3/4*s*sa^2*κ*k^2*D*X
                                                      +1/2*s*ca*κ^2*k^2*D*X-1/2*s*sa^2*k^2*D^2*X
                                                        +1/4*s*sa^2*ca*k^2*X^2
                                                          +1/4*s*ca*κ^2*k^2*X^2
                                                            -5/4*s*sa^2*k^2*D*X^2
                                                              -1/4*s*κ^2*k^2*D*X^2-s^3*d^2*κ^2
                                                                -3/4*s*d^2*sa^2*k^2+4*s^3*ca^2*k^2
                                                                  -4*s*d^2*ca^2*k^2
                                                                    +1/2*s^3*ca*κ*k^2-s^3*κ^2*k^2
                                                                      +1/2*s*d^2*ca*κ^2*D
                                                                        +1/2*s*d^2*κ^3*D
                                                                          +s^3*ca*k^2*D
                                                                            -5/4*s*sa^2*ca*k^2*D
                                                                              +s^3*κ*k^2*D
                                                                                -3/4*s*sa^2*κ*k^2*D+3/2*s*ca^2*κ*k^2*D-1/2*s*sa^2*k^2*D^2+2*s*d^2*ca*κ^2*X-s*d^2*κ^3*X+2*s^3*ca*k^2*X-2*s*d^2*ca*k^2*X+1/2*s*sa^2*ca*k^2*X-1/4*s*sa^2*κ*k^2*X-s*ca^2*κ*k^2*X-1/2*s*ca*κ^2*k^2*X-1/2*s*d^2*κ^2*D*X-11/4*s*sa^2*k^2*D*X+3/2*s*ca^2*k^2*D*X-3/2*s*ca*κ*k^2*D*X+1/4*s*sa^2*k^2*X^2+1/4*s*κ^2*k^2*X^2+1/4*s*ca*κ^2*D*X^2+2*s*c^2*d^2*κ-3/4*s*d^2*ca*κ^2+s*d^2*κ^3+5/2*s^3*ca*k^2-4*s*d^2*ca*k^2+s*sa^2*ca*k^2-2*s^3*κ*k^2+2*s*d^2*κ*k^2-1/4*s*sa^2*κ*k^2+1/2*s*ca^2*κ*k^2-s^3*k^2*D-s*sa^2*k^2*D+3*s*ca^2*k^2*D-2*s*ca*κ*k^2*D-1/4*s*d^2*κ^2*X-2*s*ca^2*κ^2*X+1/2*s*κ^4*X+1/2*s*sa^2*k^2*X+1/2*s*ca^2*k^2*X-1/2*s*ca*κ*k^2*X+1/2*s*ca*κ^2*D*X-1/4*s*κ^3*D*X-1/2*s*ca*k^2*D*X+1/2*s*κ*k^2*D*X+1/2*s*κ^2*D^2*X-1/4*s*ca*κ^2*X^2+5/4*s*κ^2*D*X^2-3/4*s*d^2*κ^2-2*s^3*k^2+2*s*d^2*k^2+5/4*s*sa^2*k^2+s*ca^2*k^2-5/4*s*ca*κ^2*D-3/4*s*κ^3*D-s*ca*k^2*D+1/2*s*κ*k^2*D-1/2*s*κ^2*D^2-2*s*ca*κ^2*X+1/4*s*κ^3*X+1/2*s*ca*k^2*X-1/2*s*κ*k^2*X+1/4*s*κ^2*D*X-1/4*s*κ^2*X^2+s*ca*κ^2-1/4*s*κ^3+s*ca*k^2-1/2*s*κ*k^2-s*κ^2*D+5/4*s*κ^2) * ha1 +
      (s*c^2*d^2*ca^2*κ^3*X+2*s*c^2*d^2*ca^2*κ^2*X-s*d^2*ca^3*k^2*X^2-s*c^2*d^2*κ^3*X
        -s*d^2*ca^2*κ^3*X-2*s*d^2*ca^3*k^2*X-1/2*s*d^2*ca^3*κ*D*X-s*d^2*ca^2*k^2*X^2
          +3/4*s*ca^3*k^2*D*X^2-1/2*s*d^2*ca^3*κ*D-2*s*c^2*d^2*κ^2*X-2*s*c^2*ca^2*κ^2*X
            -2*s*d^2*ca^2*κ^2*X-2*s*d^2*ca^2*k^2*X-1/2*s*d^2*ca^2*κ*D*X+3/2*s*ca^3*k^2*D*X
              +s*d^2*ca*k^2*X^2+1/4*s*ca^3*k^2*X^2-1/4*s*ca^2*k^2*D*X^2-1/2*s*d^2*ca^3*D
                -1/2*s*d^2*ca^2*κ*D-s*c^2*ca^2*κ*X-s*d^2*ca^2*κ*X+s*d^2*κ^3*X+2*s*d^2*ca*k^2*X
                  +1/2*s*ca^3*k^2*X-1/2*s*d^2*ca^2*D*X+1/2*s*d^2*ca*κ*D*X-1/2*s*ca^2*k^2*D*X
                    +s*d^2*k^2*X^2+1/4*s*ca^2*k^2*X^2+1/4*s*ca^3*D*X^2-3/4*s*ca*k^2*D*X^2
                      +3/4*s*d^2*ca^3+s*d^2*ca^2*κ+1/2*s*d^2*ca*κ*D+7/4*s*d^2*ca^2*X
                        -2*s*d^2*ca*κ*X+2*s*d^2*κ^2*X+2*s*ca^2*κ^2*X+2*s*d^2*k^2*X
                          +1/2*s*ca^2*k^2*X+s*ca^3*D*X+1/2*s*d^2*κ*D*X+3/4*s*ca^2*κ*D*X
                            -3/2*s*ca*k^2*D*X+1/2*s*ca^2*D^2*X-1/4*s*ca^3*X^2-1/4*s*ca*k^2*X^2
                              +5/4*s*ca^2*D*X^2+1/4*s*k^2*D*X^2+19/4*s*d^2*ca^2+1/2*s*d^2*ca*D
                                +5/4*s*ca^3*D+1/2*s*d^2*κ*D-3/4*s*ca^2*κ*D+1/2*s*ca^2*D^2
                                  +2*s*d^2*ca*X-1/2*s*ca^3*X+s*d^2*κ*X+5/4*s*ca^2*κ*X
                                    -1/2*s*ca*k^2*X+1/2*s*d^2*D*X+5/4*s*ca^2*D*X+3/2*s*ca*κ*D*X
                                      +1/2*s*k^2*D*X-1/4*s*ca^2*X^2-1/4*s*k^2*X^2-1/4*s*ca*D*X^2
                                        +13/4*s*d^2*ca-s*ca^3-s*d^2*κ-1/4*s*ca^2*κ-2*s*ca^2*D
                                          +2*s*ca*κ*D+1/4*s*d^2*X-s*ca^2*X+1/2*s*ca*κ*X
                                            -1/2*s*k^2*X-1/2*s*ca*D*X-5/4*s*κ*D*X-1/2*s*D^2*X
                                              +1/4*s*ca*X^2-5/4*s*D*X^2-11/4*s*d^2-9/4*s*ca^2
                                                -1/4*s*ca*D-5/4*s*κ*D-1/2*s*D^2+1/4*s*κ*X
                                                  -11/4*s*D*X+1/4*s*X^2+1/4*s*κ-s*D+1/2*s*X
                                                    +5/4*s) * ha2 +
      (s*d^2*ca*k^2*X^2+2*s*d^2*ca*k^2*X+1/2*s*d^2*ca*κ*D*X+s*d^2*k^2*X^2-3/4*s*ca*k^2*D*X^2
        +1/2*s*d^2*ca*κ*D+2*s*d^2*k^2*X+1/2*s*d^2*κ*D*X-3/2*s*ca*k^2*D*X-1/4*s*ca*k^2*X^2
          +1/4*s*k^2*D*X^2+1/2*s*d^2*ca*D+1/2*s*d^2*κ*D+s*d^2*κ*X-1/2*s*ca*k^2*X+1/2*s*d^2*D*X
            +1/2*s*k^2*D*X-1/4*s*k^2*X^2-1/4*s*ca*D*X^2-3/4*s*d^2*ca+s*d^2*κ+1/4*s*d^2*X
              -1/2*s*k^2*X-s*ca*D*X-3/4*s*κ*D*X-1/2*s*D^2*X+1/4*s*ca*X^2-5/4*s*D*X^2-3/4*s*d^2
                -5/4*s*ca*D-3/4*s*κ*D-1/2*s*D^2+1/2*s*ca*X-1/4*s*κ*X-11/4*s*D*X+1/4*s*X^2+s*ca
                  -1/4*s*κ-s*D+1/2*s*X+5/4*s) * E1 +
      (-3/2*s*d^2*ca^2*κ^2*X+2*s*d^2*ca^2*k^2*X-s*d^2*ca*k^2*X^2+2*s*d^2*ca*k^2*X
        -1/2*s*d^2*ca*κ*D*X-3/2*s*ca^2*k^2*D*X-s*d^2*k^2*X^2+3/4*s*ca*k^2*D*X^2+1/2*s*d^2*ca*κ*D
          +2*s*d^2*ca^2*X-1/2*s*d^2*κ^2*X+3/2*s*ca^2*κ^2*X-1/2*s*ca^2*k^2*X+1/2*s*d^2*κ*D*X
            +1/2*s*ca*k^2*D*X+1/4*s*ca*k^2*X^2-1/4*s*k^2*D*X^2+1/2*s*d^2*ca*D+1/2*s*d^2*κ*D
              +2*s*d^2*ca*X-s*d^2*κ*X-1/2*s*ca*k^2*X-1/2*s*d^2*D*X+1/4*s*k^2*X^2+1/4*s*ca*D*X^2
                -3/4*s*d^2*ca+s*d^2*κ-1/4*s*d^2*X-2*s*ca^2*X+1/2*s*κ^2*X+1/2*s*ca*D*X-1/4*s*κ*D*X
                  +1/2*s*D^2*X-1/4*s*ca*X^2+5/4*s*D*X^2-3/4*s*d^2-5/4*s*ca*D-3/4*s*κ*D-1/2*s*D^2
                    -2*s*ca*X+1/4*s*κ*X+1/4*s*D*X-1/4*s*X^2+s*ca-1/4*s*κ-s*D+5/4*s) * E2 +
      (-s*d^2*ca^2*κ^3*X-2*s*d^2*ca^2*κ^2*X+s*d^2*κ^3*X-3/2*s*ca^2*κ^3+2*s*d^2*κ^2*X
        +1/2*s*ca^2*κ^2*X-3*s*ca^2*κ^2+s*ca^2*κ*X+2*s*ca^2*κ-1/2*s*κ^3+s*ca*κ*D+s*κ^2*D+2*s*ca^2*X
          -1/2*s*κ^2*X+s*κ*D*X+4*s*ca^2+1/2*s*ca*κ-s*κ^2+s*ca*D+s*κ*D+2*s*ca*X+5/2*s*ca-2*s*κ-s*D
            -2*s) * hDdef +
      (-s*c^2*d^2*ca^2*κ^4-2*s*c^2*d^2*ca^2*κ^3+3/2*s*d^2*ca^4*κ^3-2*s*d^2*ca^4*κ*k^2
        +2*s*d^2*ca^3*κ*k^2*X+s*c^2*d^2*ca^2*κ^2+3*s*d^2*ca^4*κ^2+s*c^2*d^2*κ^4+s*d^2*ca^2*κ^4
          -4*s*d^2*ca^4*k^2+s*d^2*ca^3*κ^2*D+3/2*s*ca^4*κ*k^2*D+2*s*d^2*ca^3*k^2*X
            +2*s*d^2*ca^2*κ*k^2*X-3/2*s*ca^3*κ*k^2*D*X+2*s*c^2*d^2*ca^2*κ-2*s*d^2*ca^4*κ
              +2*s*c^2*d^2*κ^3+2*s*c^2*ca^2*κ^3+s*d^2*ca^2*κ^3-3/2*s*ca^4*κ^3-4*s*d^2*ca^3*k^2
                +4*s*d^2*ca^2*κ*k^2+1/2*s*ca^4*κ*k^2+s*d^2*ca^3*κ*D-s*d^2*ca^2*κ^2*D
                  +3*s*ca^4*k^2*D-2*s*ca^3*κ*k^2*D+4*s*d^2*ca^2*k^2*X-2*s*d^2*ca*κ*k^2*X
                    -1/2*s*ca^3*κ*k^2*X-3/2*s*ca^3*k^2*D*X+1/2*s*ca^2*κ*k^2*D*X-4*s*d^2*ca^4
                      -2*s*d^2*ca^3*κ-s*c^2*d^2*κ^2+s*c^2*ca^2*κ^2+3*s*d^2*ca^2*κ^2-3*s*ca^4*κ^2
                        -s*d^2*κ^4+6*s*d^2*ca^2*k^2+s*ca^4*k^2-s*d^2*ca^2*κ*D-s*d^2*ca*κ^2*D
                          -s*ca^3*k^2*D-s*ca^2*κ*k^2*D+2*s*d^2*ca*k^2*X-1/2*s*ca^3*k^2*X
                            -2*s*d^2*κ*k^2*X-1/2*s*ca^2*κ*k^2*X-1/2*s*ca^3*κ*D*X-s*ca^2*k^2*D*X
                              +3/2*s*ca*κ*k^2*D*X-4*s*d^2*ca^3-2*s*c^2*d^2*κ-2*s*c^2*ca^2*κ
                                +4*s*d^2*ca^2*κ+2*s*ca^4*κ+2*s*d^2*ca*κ^2-5/2*s*d^2*κ^3-s*ca^2*κ^3
                                  +4*s*d^2*ca*k^2+s*ca^3*k^2-2*s*d^2*κ*k^2-s*ca^2*κ*k^2
                                    +s*d^2*ca^2*D+s*d^2*ca*κ*D-3/2*s*ca^3*κ*D+s*d^2*κ^2*D
                                      -1/2*s*ca^2*κ^2*D-3*s*ca^2*k^2*D+2*s*ca*κ*k^2*D-s*ca^2*κ*D^2
                                        +1/2*s*ca^3*κ*X-s*ca^2*k^2*X+1/2*s*ca*κ*k^2*X
                                          -1/2*s*ca^3*D*X-5/2*s*ca^2*κ*D*X+1/2*s*ca*k^2*D*X
                                            -1/2*s*κ*k^2*D*X-s*c^2*ca^2+1/2*s*d^2*ca^2+4*s*ca^4
                                              +2*s*d^2*ca*κ+5/2*s*ca^3*κ-2*s*d^2*κ^2
                                                -5/2*s*ca^2*κ^2-2*s*d^2*k^2-s*ca^2*k^2+s*d^2*ca*D
                                                  -3/2*s*ca^3*D+s*d^2*κ*D-1/2*s*ca^2*κ*D
                                                    -3/2*s*ca*κ^2*D+s*ca*k^2*D-1/2*s*κ*k^2*D
                                                      -s*ca^2*D^2+1/2*s*ca^3*X+1/2*s*ca^2*κ*X
                                                        -1/2*s*ca*k^2*X+1/2*s*κ*k^2*X-3*s*ca^2*D*X
                                                          +1/2*s*ca*κ*D*X-3/2*s*d^2*ca+9/2*s*ca^3
                                                            -3/2*s*ca^2*κ-1/2*s*ca*κ^2+1/2*s*κ^3
                                                              -s*ca*k^2+1/2*s*κ*k^2-s*d^2*D
                                                                -4*s*ca^2*D-1/2*s*ca*κ*D+s*κ^2*D
                                                                  -s*ca*D^2+s*κ*D^2+s*ca^2*X
                                                                    -1/2*s*ca*κ*X-5/2*s*ca*D*X
                                                                      +5/2*s*κ*D*X+3/2*s*ca^2
                                                                        -5/2*s*ca*κ-7/2*s*ca*D
                                                                          +5/2*s*κ*D+s*D^2
                                                                            +1/2*s*ca*X-1/2*s*κ*X
                                                                              +s*ca-1/2*s*κ
                                                                                +2*s*D) * hX

/-- DLMF 22.9.17: cyclic identity (four points, rank 3 (both signs)), at points where
the functions are finite. -/
@[dlmf 22.9.E17]
theorem jacobi_cyclic_d2_four {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg2 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 2 m 4 z k) k) :
    jacobiCyclicD 2 1 4 z k * jacobiCyclicD 2 2 4 z k * jacobiCyclicD 2 3 4 z k +
      jacobiCyclicD 2 2 4 z k * jacobiCyclicD 2 3 4 z k * jacobiCyclicD 2 4 4 z k +
        jacobiCyclicD 2 3 4 z k * jacobiCyclicD 2 4 4 z k * jacobiCyclicD 2 1 4 z k +
          jacobiCyclicD 2 4 4 z k * jacobiCyclicD 2 1 4 z k * jacobiCyclicD 2 2 4 z k =
            jacobiComodulusk k * (jacobiCyclicD 2 1 4 z k + jacobiCyclicD 2 2 4 z k +
              jacobiCyclicD 2 3 4 z k + jacobiCyclicD 2 4 4 z k) ∧
    jacobiCyclicD 2 1 4 z k * jacobiCyclicD 2 2 4 z k * jacobiCyclicD 2 3 4 z k -
      jacobiCyclicD 2 2 4 z k * jacobiCyclicD 2 3 4 z k * jacobiCyclicD 2 4 4 z k +
        jacobiCyclicD 2 3 4 z k * jacobiCyclicD 2 4 4 z k * jacobiCyclicD 2 1 4 z k -
          jacobiCyclicD 2 4 4 z k * jacobiCyclicD 2 1 4 z k * jacobiCyclicD 2 2 4 z k =
            jacobiComodulusk k * (-jacobiCyclicD 2 1 4 z k + jacobiCyclicD 2 2 4 z k -
              jacobiCyclicD 2 3 4 z k + jacobiCyclicD 2 4 4 z k) := by
  obtain ⟨a1, a2, a3, a4⟩ := p22R1_cyc4 k z
  have hn := hreg2 1
  have hnw := hreg2 2
  have hn3 := hreg2 3
  have hn4 := hreg2 4
  rw [a1] at hn; rw [a2] at hnw; rw [a3] at hn3; rw [a4] at hn4
  have hd := jacobiPQk_ne_zero (by decide) (p22R1_reg_d_of_n_add_K hk hn3) hn
  have hdw := jacobiPQk_ne_zero (by decide) (p22R1_reg_d_of_n_add_K hk hn4) hnw
  obtain ⟨-, -, v3⟩ := p22R1_add_K_vals hk hn
  obtain ⟨-, -, w3⟩ := p22R1_add_K_vals hk hnw
  simp only [jacobiCyclicD, a1, a2, a3, a4, v3, w3]
  change jacobiDnk z k ≠ 0 at hd
  change jacobiDnk _ k ≠ 0 at hdw
  generalize z + compEllIntKk k / 2 = w at *
  constructor <;> field_simp <;> ring

/-- DLMF 22.9.18: cyclic identity (four points, rank 3 (both signs)), at points where
the functions are finite. -/
@[dlmf 22.9.E18]
theorem jacobi_cyclic_d2_four_sq {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg2 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 2 m 4 z k) k) :
    jacobiCyclicD 2 1 4 z k ^ 2 * jacobiCyclicD 2 3 4 z k + jacobiCyclicD 2 2 4 z k ^ 2 *
      jacobiCyclicD 2 4 4 z k + jacobiCyclicD 2 3 4 z k ^ 2 * jacobiCyclicD 2 1 4 z k +
        jacobiCyclicD 2 4 4 z k ^ 2 * jacobiCyclicD 2 2 4 z k = jacobiComodulusk k *
          (jacobiCyclicD 2 1 4 z k + jacobiCyclicD 2 2 4 z k + jacobiCyclicD 2 3 4 z k +
            jacobiCyclicD 2 4 4 z k) ∧
    jacobiCyclicD 2 1 4 z k ^ 2 * jacobiCyclicD 2 3 4 z k - jacobiCyclicD 2 2 4 z k ^ 2 *
      jacobiCyclicD 2 4 4 z k + jacobiCyclicD 2 3 4 z k ^ 2 * jacobiCyclicD 2 1 4 z k -
        jacobiCyclicD 2 4 4 z k ^ 2 * jacobiCyclicD 2 2 4 z k = jacobiComodulusk k *
          (jacobiCyclicD 2 1 4 z k - jacobiCyclicD 2 2 4 z k + jacobiCyclicD 2 3 4 z k -
            jacobiCyclicD 2 4 4 z k) := by
  obtain ⟨a1, a2, a3, a4⟩ := p22R1_cyc4 k z
  have hn := hreg2 1
  have hnw := hreg2 2
  have hn3 := hreg2 3
  have hn4 := hreg2 4
  rw [a1] at hn; rw [a2] at hnw; rw [a3] at hn3; rw [a4] at hn4
  have hd := jacobiPQk_ne_zero (by decide) (p22R1_reg_d_of_n_add_K hk hn3) hn
  have hdw := jacobiPQk_ne_zero (by decide) (p22R1_reg_d_of_n_add_K hk hn4) hnw
  obtain ⟨-, -, v3⟩ := p22R1_add_K_vals hk hn
  obtain ⟨-, -, w3⟩ := p22R1_add_K_vals hk hnw
  simp only [jacobiCyclicD, a1, a2, a3, a4, v3, w3]
  change jacobiDnk z k ≠ 0 at hd
  change jacobiDnk _ k ≠ 0 at hdw
  generalize z + compEllIntKk k / 2 = w at *
  constructor <;> field_simp <;> ring

/-- DLMF 22.9.19: cyclic identity (four points, rank 3), at points where the functions
are finite. -/
@[dlmf 22.9.E19]
theorem jacobi_cyclic_csd_four {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg2 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 2 m 4 z k) k) :
    jacobiCyclicC 2 1 4 z k * jacobiCyclicS 2 1 4 z k * jacobiCyclicD 2 3 4 z k +
      jacobiCyclicC 2 3 4 z k * jacobiCyclicS 2 3 4 z k * jacobiCyclicD 2 1 4 z k = 0 ∧
    jacobiCyclicC 2 2 4 z k * jacobiCyclicS 2 2 4 z k * jacobiCyclicD 2 4 4 z k +
      jacobiCyclicC 2 4 4 z k * jacobiCyclicS 2 4 4 z k * jacobiCyclicD 2 2 4 z k = 0 := by
  obtain ⟨a1, a2, a3, a4⟩ := p22R1_cyc4 k z
  have hn := hreg2 1
  have hnw := hreg2 2
  have hn3 := hreg2 3
  have hn4 := hreg2 4
  rw [a1] at hn; rw [a2] at hnw; rw [a3] at hn3; rw [a4] at hn4
  have hd := jacobiPQk_ne_zero (by decide) (p22R1_reg_d_of_n_add_K hk hn3) hn
  have hdw := jacobiPQk_ne_zero (by decide) (p22R1_reg_d_of_n_add_K hk hn4) hnw
  obtain ⟨v1, v2, v3⟩ := p22R1_add_K_vals hk hn
  obtain ⟨w1, w2, w3⟩ := p22R1_add_K_vals hk hnw
  simp only [jacobiCyclicS, jacobiCyclicC, jacobiCyclicD, a1, a2, a3, a4, v1, v2, v3, w1, w2, w3]
  change jacobiDnk z k ≠ 0 at hd
  change jacobiDnk _ k ≠ 0 at hdw
  generalize z + compEllIntKk k / 2 = w at *
  constructor <;> field_simp <;> ring

/-- DLMF 22.9.20: cyclic identity (two points, rank 4 (both signs)), at points where
the functions are finite. -/
@[dlmf 22.9.E20]
theorem jacobi_cyclic_d2_two_rank4 {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg2 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 2 m 2 z k) k) :
    jacobiCyclicD 2 1 2 z k ^ 3 * jacobiCyclicD 2 2 2 z k + jacobiCyclicD 2 2 2 z k ^ 3 *
      jacobiCyclicD 2 1 2 z k = jacobiComodulusk k * (jacobiCyclicD 2 1 2 z k ^ 2 +
        jacobiCyclicD 2 2 2 z k ^ 2) ∧
    jacobiCyclicD 2 1 2 z k ^ 3 * jacobiCyclicD 2 2 2 z k - jacobiCyclicD 2 2 2 z k ^ 3 *
      jacobiCyclicD 2 1 2 z k = jacobiComodulusk k * (jacobiCyclicD 2 1 2 z k ^ 2 -
        jacobiCyclicD 2 2 2 z k ^ 2) := by
  obtain ⟨a1, a2⟩ := p22R1_cyc2 k z
  have hn := hreg2 1
  have hn2 := hreg2 2
  rw [a1] at hn; rw [a2] at hn2
  have hd := jacobiPQk_ne_zero (by decide) (p22R1_reg_d_of_n_add_K hk hn2) hn
  obtain ⟨v1, v2, v3⟩ := p22R1_add_K_vals hk hn
  simp only [jacobiCyclicD, a1, a2, v3]
  change jacobiDnk z k ≠ 0 at hd
  constructor <;> field_simp <;> ring

/-- DLMF 22.9.21: cyclic identity (two points, rank 4), at points where the functions
are finite. -/
@[dlmf 22.9.E21]
theorem jacobi_cyclic_cscs_two {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg2 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 2 m 2 z k) k) :
    k ^ 2 * jacobiCyclicC 2 1 2 z k * jacobiCyclicS 2 1 2 z k * jacobiCyclicC 2 2 2 z k *
      jacobiCyclicS 2 2 2 z k = jacobiComodulusk k * (1 - jacobiCyclicS 2 1 2 z k ^ 2 -
        jacobiCyclicS 2 2 2 z k ^ 2) := by
  obtain ⟨a1, a2⟩ := p22R1_cyc2 k z
  have hn := hreg2 1
  have hn2 := hreg2 2
  rw [a1] at hn; rw [a2] at hn2
  have hd := jacobiPQk_ne_zero (by decide) (p22R1_reg_d_of_n_add_K hk hn2) hn
  obtain ⟨v1, v2, v3⟩ := p22R1_add_K_vals hk hn
  obtain ⟨h1, h2⟩ := jacobi_sq_sum hk hn
  have hkp := jacobiComodulusk_sq k
  simp only [jacobiCyclicS, jacobiCyclicC, jacobiCyclicD, a1, a2, v1, v2, v3]
  change jacobiDnk z k ≠ 0 at hd
  field_simp
  linear_combination jacobiComodulusk k * jacobiDnk z k ^ 2 * h1 -
    jacobiComodulusk k * jacobiCnk z k ^ 2 * h2

end DLMF.JacobiElliptic
end
end
