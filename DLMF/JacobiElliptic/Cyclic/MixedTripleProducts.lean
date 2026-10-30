/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Cyclic.TripleProducts

/-!
# Mixed cyclic products of Jacobian elliptic functions

Mixed sn, cn and dn triple-product identities with their regularity and denominator hypotheses.

Source references and common attribution are retained in
`DLMF.JacobiElliptic.Cyclic`.
-/

@[expose] public section

open Complex DLMF.Elliptic

open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
/-- DLMF 22.9.22: cyclic identity (three points, rank 4), at points where the
functions are finite. -/
@[dlmf 22.9.E7, dlmf 22.9.E22]
theorem jacobi_cyclic_scdd_three {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg2 : ∀ m : ℕ, JacobiRegulark .n (jacobiCyclicArg 2 m 3 z k) k) :
    jacobiCyclicS 2 1 3 z k * jacobiCyclicC 2 1 3 z k * jacobiCyclicD 2 2 3 z k *
      jacobiCyclicD 2 3 3 z k + jacobiCyclicS 2 2 3 z k * jacobiCyclicC 2 2 3 z k *
        jacobiCyclicD 2 3 3 z k * jacobiCyclicD 2 1 3 z k + jacobiCyclicS 2 3 3 z k *
          jacobiCyclicC 2 3 3 z k * jacobiCyclicD 2 1 3 z k * jacobiCyclicD 2 2 3 z k =
            (jacobiCyclicKappa k ^ 2 + k ^ 2 - 1) / (1 - jacobiCyclicKappa k ^ 2) *
              (jacobiCyclicS 2 1 3 z k * jacobiCyclicC 2 1 3 z k + jacobiCyclicS 2 2 3 z k *
                jacobiCyclicC 2 2 3 z k + jacobiCyclicS 2 3 3 z k * jacobiCyclicC 2 3 3 z k) := by
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
  linear_combination (s*c*d^2*ca^4*κ^2*k^2*D+2*s*c*d^2*ca^4*κ^2*k^2-s*c*d^2*ca^4*k^2*D
      -s*c*d^2*ca^2*κ^2*k^2*D-s*c*ca^4*κ^2*k^2*D+1/2*s*c*ca^2*k^4*D^2*X-2*s*c*d^2*ca^4*k^2
        -2*s*c*d^2*ca^2*κ^2*k^2+1/2*s*c*ca^2*k^4*D*X+s*c*d^2*ca^2*k^2*D+s*c*ca^4*k^2*D
          +s*c*ca^2*κ^2*k^2*D-1/2*s*c*k^4*D^2*X+2*s*c*d^2*ca^2*k^2-1/2*s*c*k^4*D*X-s*c*ca^2*k^2*D
            -1/2*s*c*κ*k^2*D^2+1/2*s*c*k^2*D^2*X-1/2*s*c*κ*k^2*D+1/2*s*c*k^2*D*X) * h1 +
      (-1/2*s*c*d^2*ca^6*κ^3*D-1/2*s*c*d^2*ca^6*κ^2*D*X-s*c*d^2*ca^6*κ^2*D-s*c^3*ca^4*κ^2*k^2*D
        -2*s*c*d^2*ca^4*κ^4+1/2*s*c*d^2*ca^4*κ^3*D+1/2*s*c*d^2*ca^4*κ^2*D*X+4*s*c*d^2*ca^6*κ
          +1/2*s*c*d^2*ca^5*κ*D+s*c^3*ca^4*k^2*D+s*c^3*ca^2*κ^2*k^2*D-1/2*s*c*ca^6*κ*D^2
            +4*s*c*d^2*ca^6*X-1/2*s*c*ca^6*D^2*X+8*s*c*d^2*ca^6+2*s*c*d^2*ca^5*κ
              +2*s*c*d^2*ca^2*κ^4+1/2*s*c*d^2*ca^5*D-s*c*d^2*ca^4*κ*D+9/2*s*c*ca^6*κ*D
                +1/2*s*c*d^2*ca^2*κ^3*D-s*c*ca^6*D^2+6*s*c*d^2*ca^5*X+9/2*s*c*ca^6*D*X
                  +1/2*s*c*d^2*ca^2*κ^2*D*X-1/2*s*c*ca^5*D^2*X+8*s*c*d^2*ca^5-18*s*c*d^2*ca^4*κ
                    -4*s*c*ca^6*κ-4*s*c*d^2*ca^2*κ^3+9*s*c*ca^6*D+2*s*c*ca^5*κ*D
                      +s*c*d^2*ca^2*κ^2*D+s*c*ca^4*κ^2*D-s*c^3*ca^2*k^2*D-1/2*s*c*ca^5*D^2
                        +1/2*s*c*ca^4*κ*D^2+1/2*s*c*ca^2*κ^3*D^2-4*s*c*d^2*ca^4*X-4*s*c*ca^6*X
                          -4*s*c*d^2*ca^2*κ^2*X+13/2*s*c*ca^5*D*X-s*c*d^2*ca^2*κ*D*X
                            +1/2*s*c*ca^2*κ^2*D^2*X-20*s*c*d^2*ca^4-8*s*c*ca^6-16*s*c*d^2*ca^3*κ
                              -2*s*c*ca^5*κ+8*s*c*d^2*ca^2*κ^2+17/2*s*c*ca^5*D-9/2*s*c*ca^4*κ*D
                                -1/2*s*c*d^2*κ^3*D+1/2*s*c*ca^2*κ^3*D+1/2*s*c*ca^4*D^2
                                  -8*s*c*d^2*ca^3*X-6*s*c*ca^5*X+16*s*c*d^2*ca^2*κ*X
                                    -1/2*s*c*d^2*κ^2*D*X+1/2*s*c*ca^2*κ^2*D*X-s*c*ca^2*κ*D^2*X
                                      -24*s*c*d^2*ca^3-8*s*c*ca^5+32*s*c*d^2*ca^2*κ+6*s*c*ca^4*κ
                                        +4*s*c*d^2*κ^3+s*c*d^2*ca^2*D-11/2*s*c*ca^4*D
                                          -1/2*s*c*d^2*ca*κ*D-2*s*c*ca^2*κ^2*D-1/2*s*c*κ^3*D^2
                                            +4*s*c*d^2*κ^2*X-s*c*ca^3*D*X+s*c*d^2*κ*D*X
                                              -2*s*c*ca^2*κ*D*X-1/2*s*c*κ^2*D^2*X-2*s*c*d^2*ca^2
                                                +6*s*c*ca^4+14*s*c*d^2*ca*κ+2*s*c*ca^3*κ
                                                  -8*s*c*d^2*κ^2-1/2*s*c*d^2*ca*D-s*c*ca^3*D
                                                    +s*c*d^2*κ*D-7*s*c*ca^2*κ*D-1/2*s*c*κ^3*D
                                                      +2*s*c*ca^2*D^2+2*s*c*d^2*ca*X+2*s*c*ca^3*X
                                                        -16*s*c*d^2*κ*X-5*s*c*ca^2*D*X
                                                          -1/2*s*c*κ^2*D*X+1/2*s*c*ca*D^2*X
                                                            +s*c*κ*D^2*X+16*s*c*d^2*ca+4*s*c*ca^3
                                                              -18*s*c*d^2*κ+2*s*c*ca^2*κ-s*c*d^2*D
                                                                -7*s*c*ca^2*D-2*s*c*ca*κ*D
                                                                  +s*c*κ^2*D+1/2*s*c*ca*D^2
                                                                    +1/2*s*c*κ*D^2+4*s*c*ca^2*X
                                                                      -11/2*s*c*ca*D*X+2*s*c*κ*D*X
                                                                        +14*s*c*d^2+6*s*c*ca^2
                                                                          -15/2*s*c*ca*D
                                                                            +15/2*s*c*κ*D
                                                                              -3/2*s*c*D^2
                                                                                +4*s*c*ca*X
                                                                                  +4*s*c*ca-4*s*c*κ+7/2*s*c*D-4*s*c) * h2 +
      (-1/2*s*c*d^2*sa^2*ca^3*κ^2*k^4*D*X-2*s*c*d^4*sa^2*ca^3*k^4*X^2
        +1/4*s*c*d^2*sa^2*ca^3*k^4*D^2*X^2+1/2*s^3*c*d^2*ca^4*κ^3*k^2*D+2*s*c*d^4*ca^4*κ^3*k^2*X
          -3*s*c*d^4*sa^2*ca^3*k^4*X+2*s*c*d^4*sa^2*ca^2*κ*k^4*X-s*c*d^2*sa^2*ca^3*κ^2*k^4*X
            +1/2*s*c*d^4*ca^4*κ^4*D*X+1/2*s^3*c*d^2*ca^4*κ^2*k^2*D*X
              -1/2*s*c*d^2*sa^2*ca^2*κ^2*k^4*D*X+1/2*s*c*d^2*sa^2*ca^3*k^4*D^2*X
                -3*s*c*d^4*sa^2*ca^2*k^4*X^2-1/4*s*c*d^2*sa^2*ca^3*k^4*D*X^2
                  +1/4*s*c*d^2*sa^2*ca^2*k^4*D^2*X^2+2*s*c*d^4*sa^2*ca^3*k^4
                    +s^3*c*d^2*ca^4*κ^2*k^2*D+s^3*c^3*ca^2*κ^2*k^4*D-4*s*c*d^4*sa^2*ca^3*κ*k^2*X
                      -4*s*c*d^4*ca^4*κ^2*k^2*X-5*s*c*d^4*sa^2*ca^2*k^4*X
                        -2*s*c*d^4*sa^2*ca*κ*k^4*X-2*s*c*d^2*sa^2*ca^3*κ*k^4*X
                          -s*c*d^2*sa^2*ca^2*κ^2*k^4*X+1/2*s*c*d^4*sa^2*ca^3*k^2*D*X
                            -1/2*s*c*d^2*ca^3*κ^4*k^2*D*X+1/2*s*c*d^2*sa^2*ca^2*κ*k^4*D*X
                              +1/2*s*c*sa^2*ca^3*κ^2*k^4*D*X+1/2*s*c*d^2*ca^4*κ^2*k^2*D^2*X
                                +1/2*s*c*d^2*sa^2*ca^2*k^4*D^2*X+2*s*c*d^4*ca^3*κ^2*k^2*X^2
                                  +2*s*c*d^2*sa^2*ca^3*k^4*X^2-1/4*s*c*d^2*sa^2*ca^2*k^4*D*X^2
                                    -1/4*s*c*d^2*ca^3*κ^2*k^2*D^2*X^2
                                      +1/4*s*c*d^2*sa^2*ca*k^4*D^2*X^2-4*s*c*d^4*sa^2*ca^3*κ*k^2
                                        -2*s*c*d^4*ca^4*κ^2*k^2+2*s^3*c*d^2*ca^2*κ^4*k^2
                                          +1/4*s*c*d^4*sa^2*ca^3*k^2*D-7*s*c*d^4*sa^2*ca^2*κ*k^2*X
                                            -2*s*c*d^4*ca^4*κ*k^2*X-7*s*c*d^4*ca^3*κ^2*k^2*X
                                              -2*s*c*d^4*ca^2*κ^3*k^2*X-2*s*c*d^2*ca^4*κ^3*k^2*X
                                                -s*c*d^2*ca^3*κ^4*k^2*X-s*c*d^4*sa^2*ca*k^4*X
                                                  +4*s*c*d^2*sa^2*ca^3*k^4*X
                                                    -2*s*c*d^4*sa^2*κ*k^4*X
                                                      -s*c*d^2*sa^2*ca^2*κ*k^4*X
                                                        -1/2*s*c*d^2*ca^4*κ^4*D*X
                                                          -1/4*s*c*d^4*sa^2*ca^2*k^2*D*X
                                                            +1/2*s*c*d^4*sa^2*ca*κ*k^2*D*X
                                                              +1/2*s*c*d^2*sa^2*ca^3*κ*k^2*D*X
                                                                -1/2*s*c*d^2*ca^4*κ^2*k^2*D*X
                                                                  +s*c*d^2*ca^3*κ^3*k^2*D*X
                                                                    -1/2*s*c*d^2*ca^2*κ^4*k^2*D*X
                                                                      -1/2*s*c*d^2*sa^2*ca^2*k^4*D*X+2*s*c*d^2*sa^2*ca*κ*k^4*D*X+1/2*s*c*sa^2*ca^2*κ^2*k^4*D*X+1/4*s*c*d^2*sa^2*ca^2*κ*k^2*D^2*X+1/2*s*c*d^2*ca^3*κ^2*k^2*D^2*X+1/2*s*c*d^2*sa^2*ca*k^4*D^2*X+3*s*c*d^4*ca^2*κ^2*k^2*X^2+s*c*d^4*sa^2*k^4*X^2+3*s*c*d^2*sa^2*ca^2*k^4*X^2+1/4*s*c*d^2*ca^3*κ^2*k^2*D*X^2-9/4*s*c*d^2*sa^2*ca*k^4*D*X^2-1/4*s*c*d^2*ca^2*κ^2*k^2*D^2*X^2+1/4*s*c*d^2*sa^2*k^4*D^2*X^2-1/4*s*c*sa^2*ca^3*k^2*D^3*X^2+2*s*c*d^4*sa^2*ca^3*k^2-7*s*c*d^4*sa^2*ca^2*κ*k^2-4*s^3*c*d^2*ca^4*κ*k^2+2*s*c*d^4*ca^3*κ^2*k^2+1/4*s*c*d^4*sa^2*ca^2*k^2*D+1/2*s*c*d^4*sa^2*ca*κ*k^2*D-1/2*s^3*c*d^2*ca^3*κ*k^2*D+1/2*s*c*d^2*sa^2*ca^3*κ*k^2*D-s^3*c^3*ca^2*k^4*D-1/4*s*c*d^2*sa^2*ca^3*k^2*D^2+1/4*s*c*d^2*sa^2*ca^2*κ*k^2*D^2+1/2*s^3*c*ca^4*κ*k^2*D^2-1/2*s*c*d^2*ca^4*κ*k^2*D^2-4*s*c*d^4*ca^4*κ^2*X+4*s*c*d^4*ca^3*κ^3*X-s*c*d^4*sa^2*ca^2*k^2*X-4*s^3*c*d^2*ca^4*k^2*X+4*s*c*d^4*ca^4*k^2*X-4*s*c*d^4*sa^2*ca*κ*k^2*X+4*s*c*d^2*sa^2*ca^3*κ*k^2*X-s*c*d^4*ca^2*κ^2*k^2*X+4*s*c*d^2*ca^4*κ^2*k^2*X-2*s*c*d^4*ca*κ^3*k^2*X-s*c*d^2*ca^2*κ^4*k^2*X+s*c*d^4*sa^2*k^4*X+5*s*c*d^2*sa^2*ca^2*k^4*X-1/2*s*c*d^4*ca^3*κ^2*D*X-s*c*d^2*sa^2*ca^3*k^2*D*X+1/2*s*c*d^4*sa^2*κ*k^2*D*X+1/4*s*c*d^2*sa^2*ca^2*κ*k^2*D*X+3/2*s*c*d^2*ca^2*κ^3*k^2*D*X+1/2*s*c*ca^3*κ^4*k^2*D*X-4*s*c*d^2*sa^2*ca*k^4*D*X-1/2*s*c*sa^2*ca^3*k^4*D*X+2*s*c*d^2*sa^2*κ*k^4*D*X-1/2*s*c*sa^2*ca^2*κ*k^4*D*X+1/2*s*c*d^2*ca^4*κ^2*D^2*X+1/4*s*c*d^2*sa^2*ca^2*k^2*D^2*X+1/2*s^3*c*ca^4*k^2*D^2*X-1/2*s*c*d^2*ca^4*k^2*D^2*X+1/2*s*c*d^2*sa^2*ca*κ*k^2*D^2*X+1/2*s*c*d^2*ca^3*κ*k^2*D^2*X+1/2*s*c*d^2*ca^2*κ^2*k^2*D^2*X+1/2*s*c*d^2*sa^2*k^4*D^2*X-1/2*s*c*sa^2*ca^3*k^2*D^3*X-2*s*c*d^2*ca^3*κ^2*k^2*X^2+2*s*c*d^2*sa^2*ca*k^4*X^2+1/4*s*c*d^2*ca^2*κ^2*k^2*D*X^2-15/4*s*c*d^2*sa^2*k^4*D*X^2+9/4*s*c*sa^2*ca^3*k^2*D^2*X^2-1/4*s*c*d^2*ca*κ^2*k^2*D^2*X^2-1/4*s*c*sa^2*ca^2*k^2*D^3*X^2-4*s*c*d^4*ca^3*κ^3+6*s*c*d^4*sa^2*ca^2*k^2-8*s^3*c*d^2*ca^4*k^2+8*s*c*d^4*ca^4*k^2-4*s*c*d^4*sa^2*ca*κ*k^2-2*s^3*c*d^2*ca^3*κ*k^2+4*s*c*d^2*sa^2*ca^3*κ*k^2-2*s^3*c*d^2*ca^2*κ^2*k^2-2*s*c^3*d^2*ca^2*κ^2*k^2+4*s*c*d^4*ca^2*κ^2*k^2+2*s*c*d^2*ca^4*κ^2*k^2+1/4*s*c*d^4*ca^3*κ^2*D-1/4*s*c*d^4*sa^2*ca*k^2*D-1/2*s^3*c*d^2*ca^3*k^2*D+3/2*s*c*d^2*sa^2*ca^3*k^2*D+1/2*s*c*d^4*sa^2*κ*k^2*D+s^3*c*d^2*ca^2*κ*k^2*D+1/4*s*c*d^2*sa^2*ca^2*κ*k^2*D-9/2*s^3*c*ca^4*κ*k^2*D+1/2*s*c*d^2*ca^4*κ*k^2*D-1/2*s^3*c*d^2*κ^3*k^2*D+s^3*c*ca^4*k^2*D^2-s*c*d^2*ca^4*k^2*D^2+1/2*s*c*d^2*sa^2*ca*κ*k^2*D^2-1/4*s*c*sa^2*ca^3*k^2*D^3-6*s*c*d^4*ca^3*κ^2*X+7*s*c*d^4*ca^2*κ^3*X+4*s*c*d^4*sa^2*ca*k^2*X-6*s^3*c*d^2*ca^3*k^2*X+6*s*c*d^4*ca^3*k^2*X-3*s*c*d^4*sa^2*κ*k^2*X-6*s*c*d^4*ca^2*κ*k^2*X+7*s*c*d^2*sa^2*ca^2*κ*k^2*X+2*s*c*d^2*ca^4*κ*k^2*X+3*s*c*d^4*ca*κ^2*k^2*X+8*s*c*d^2*ca^3*κ^2*k^2*X+s*c*d^2*ca^2*κ^3*k^2*X+4*s*c*d^2*sa^2*ca*k^4*X+1/4*s*c*d^4*ca^2*κ^2*D*X-9/2*s*c*d^2*ca^4*κ^2*D*X-1/2*s*c*d^4*ca*κ^3*D*X-1/2*s*c*d^2*ca^3*κ^3*D*X-1/2*s*c*d^4*κ^4*D*X-1/4*s*c*d^4*sa^2*k^2*D*X-9/2*s^3*c*ca^4*k^2*D*X+1/2*s*c*d^2*ca^4*k^2*D*X-4*s*c*d^2*sa^2*ca*κ*k^2*D*X-3/2*s*c*d^2*ca^3*κ*k^2*D*X-1/2*s*c*sa^2*ca^3*κ*k^2*D*X-1/2*s^3*c*d^2*κ^2*k^2*D*X-7/2*s*c*d^2*ca^2*κ^2*k^2*D*X+2*s*c*d^2*ca*κ^3*k^2*D*X-s*c*ca^3*κ^3*k^2*D*X+1/2*s*c*ca^2*κ^4*k^2*D*X-6*s*c*d^2*sa^2*k^4*D*X+1/2*s*c*d^2*ca^3*κ^2*D^2*X-1/4*s*c*d^2*ca^2*κ^3*D^2*X-1/2*s*c*d^2*sa^2*ca*k^2*D^2*X+1/2*s^3*c*ca^3*k^2*D^2*X-1/2*s*c*d^2*ca^3*k^2*D^2*X+9/2*s*c*sa^2*ca^3*k^2*D^2*X+3/4*s*c*d^2*sa^2*κ*k^2*D^2*X+1/2*s*c*d^2*ca^2*κ*k^2*D^2*X+1/2*s*c*d^2*ca*κ^2*k^2*D^2*X-1/2*s*c*sa^2*ca^2*k^2*D^3*X-s*c*d^4*κ^2*k^2*X^2-3*s*c*d^2*ca^2*κ^2*k^2*X^2+2*s*c*d^2*sa^2*k^4*X^2-2*s*c*sa^2*ca^3*k^2*D*X^2+9/4*s*c*d^2*ca*κ^2*k^2*D*X^2+13/4*s*c*sa^2*ca^2*k^2*D^2*X^2-1/4*s*c*d^2*κ^2*k^2*D^2*X^2+1/4*s*c*ca^3*κ^2*D^3*X^2-1/4*s*c*sa^2*ca*k^2*D^3*X^2+2*s*c*d^4*ca^3*κ^2-7*s*c*d^4*ca^2*κ^3+10*s*c*d^4*sa^2*ca*k^2-8*s^3*c*d^2*ca^3*k^2+6*s*c*d^4*ca^3*k^2-4*s*c*d^2*sa^2*ca^3*k^2-3*s*c*d^4*sa^2*κ*k^2+14*s^3*c*d^2*ca^2*κ*k^2+7*s*c*d^2*sa^2*ca^2*κ*k^2+4*s^3*c*ca^4*κ*k^2+4*s^3*c*d^2*κ^3*k^2+1/4*s*c*d^4*ca^2*κ^2*D+1/2*s*c*d^4*ca*κ^3*D+1/2*s*c*d^2*ca^3*κ^3*D-3/4*s*c*d^4*sa^2*k^2*D+s^3*c*d^2*ca^2*k^2*D+7/4*s*c*d^2*sa^2*ca^2*k^2*D-9*s^3*c*ca^4*k^2*D+s*c*d^2*ca^4*k^2*D-1/2*s^3*c*d^2*ca*κ*k^2*D-4*s*c*d^2*sa^2*ca*κ*k^2*D-2*s^3*c*ca^3*κ*k^2*D-s*c*d^2*ca^3*κ*k^2*D-1/2*s*c*sa^2*ca^3*κ*k^2*D-1/4*s*c*d^2*ca^3*κ^2*D^2+1/4*s*c*d^2*ca^2*κ^3*D^2-3/4*s*c*d^2*sa^2*ca*k^2*D^2+1/2*s^3*c*ca^3*k^2*D^2-s*c*d^2*ca^3*k^2*D^2+5/2*s*c*sa^2*ca^3*k^2*D^2+3/4*s*c*d^2*sa^2*κ*k^2*D^2-1/2*s^3*c*κ^3*k^2*D^2-1/4*s*c*sa^2*ca^2*k^2*D^3+s*c*d^4*ca^2*κ^2*X+8*s*c*d^2*ca^4*κ^2*X+4*s*c*d^4*ca*κ^3*X-4*s*c*d^2*ca^3*κ^3*X+4*s*c*d^4*κ^4*X+7*s*c*d^4*sa^2*k^2*X+s*c*d^2*sa^2*ca^2*k^2*X+4*s^3*c*ca^4*k^2*X-4*s*c*d^2*ca^4*k^2*X+4*s*c*d^4*ca*κ*k^2*X+8*s*c*d^2*sa^2*ca*κ*k^2*X+6*s*c*d^2*ca^3*κ*k^2*X+4*s^3*c*d^2*κ^2*k^2*X+s*c*d^4*κ^2*k^2*X+7*s*c*d^2*ca^2*κ^2*k^2*X+4*s*c*d^2*sa^2*k^4*X-11/2*s*c*d^2*ca^3*κ^2*D*X+1/2*s*c*d^4*κ^3*D*X-1/4*s*c*d^2*ca^2*κ^3*D*X-5*s*c*d^2*sa^2*ca*k^2*D*X-13/2*s^3*c*ca^3*k^2*D*X+1/2*s*c*d^2*ca^3*k^2*D*X-7/2*s*c*sa^2*ca^3*k^2*D*X+s^3*c*d^2*κ*k^2*D*X-31/4*s*c*d^2*sa^2*κ*k^2*D*X-5/2*s*c*d^2*ca^2*κ*k^2*D*X-1/2*s*c*sa^2*ca^2*κ*k^2*D*X-8*s*c*d^2*ca*κ^2*k^2*D*X-1/2*s*c*ca^3*κ^2*k^2*D*X+s*c*d^2*κ^3*k^2*D*X-3/2*s*c*ca^2*κ^3*k^2*D*X-1/2*s*c*sa^2*ca*k^4*D*X+1/4*s*c*d^2*ca^2*κ^2*D^2*X-1/2*s*c*ca^4*κ^2*D^2*X-1/2*s*c*d^2*ca*κ^3*D^2*X-1/2*s*c*d^2*κ^4*D^2*X+1/4*s*c*d^2*sa^2*k^2*D^2*X+1/2*s^3*c*ca^2*k^2*D^2*X-1/2*s*c*d^2*ca^2*k^2*D^2*X+13/2*s*c*sa^2*ca^2*k^2*D^2*X+1/2*s*c*d^2*ca*κ*k^2*D^2*X-1/2*s^3*c*κ^2*k^2*D^2*X-1/2*s^3*c*k^4*D^2*X-1/2*s*c^3*k^4*D^2*X-1/2*s*c*sa^2*ca*k^2*D^3*X-2*s*c*d^2*ca*κ^2*k^2*X^2-3*s*c*sa^2*ca^2*k^2*D*X^2+15/4*s*c*d^2*κ^2*k^2*D*X^2-1/2*s*c*sa^2*k^4*D*X^2-9/4*s*c*ca^3*κ^2*D^2*X^2+9/4*s*c*sa^2*ca*k^2*D^2*X^2+1/4*s*c*ca^2*κ^2*D^3*X^2-1/4*s*c*sa^2*k^2*D^3*X^2+6*s*c*d^4*ca^2*κ^2-4*s*c*d^4*ca*κ^3+4*s*c*d^2*ca^3*κ^3+2*s*c*d^4*κ^4+14*s*c*d^4*sa^2*k^2+14*s^3*c*d^2*ca^2*k^2+2*s*c^3*d^2*ca^2*k^2+2*s*c*d^4*ca^2*k^2-9*s*c*d^2*sa^2*ca^2*k^2+8*s^3*c*ca^4*k^2-8*s*c*d^2*ca^4*k^2+14*s^3*c*d^2*ca*κ*k^2+8*s*c*d^2*sa^2*ca*κ*k^2+2*s^3*c*ca^3*κ*k^2-2*s*c*d^2*ca^3*κ*k^2-8*s^3*c*d^2*κ^2*k^2-2*s*c*d^4*κ^2*k^2-1/4*s*c*d^4*ca*κ^2*D+3/2*s*c*d^2*ca^3*κ^2*D+1/2*s*c*d^4*κ^3*D+1/4*s*c*d^2*ca^2*κ^3*D-1/2*s^3*c*d^2*ca*k^2*D-3*s*c*d^2*sa^2*ca*k^2*D-17/2*s^3*c*ca^3*k^2*D+2*s*c*d^2*ca^3*k^2*D-15/4*s*c*sa^2*ca^3*k^2*D+s^3*c*d^2*κ*k^2*D-31/4*s*c*d^2*sa^2*κ*k^2*D+s*c*d^2*ca^2*κ*k^2*D-1/2*s*c*sa^2*ca^2*κ*k^2*D-1/2*s^3*c*κ^3*k^2*D+1/2*s*c*d^2*ca*κ^3*D^2-s*c*d^2*sa^2*k^2*D^2+1/2*s^3*c*ca^2*k^2*D^2-s*c*d^2*ca^2*k^2*D^2+7/2*s*c*sa^2*ca^2*k^2*D^2-1/4*s*c*ca^3*κ^2*D^3-1/4*s*c*sa^2*ca*k^2*D^3-2*s*c*d^4*ca*κ^2*X+12*s*c*d^2*ca^3*κ^2*X-13*s*c*d^4*κ^3*X-7*s*c*d^2*ca^2*κ^3*X+2*s^3*c*d^2*ca*k^2*X-2*s*c*d^4*ca*k^2*X+6*s^3*c*ca^3*k^2*X-6*s*c*d^2*ca^3*k^2*X-16*s^3*c*d^2*κ*k^2*X+4*s*c*d^4*κ*k^2*X+10*s*c*d^2*sa^2*κ*k^2*X+6*s*c*d^2*ca^2*κ*k^2*X+4*s*c*d^2*ca*κ^2*k^2*X+1/4*s*c*d^4*κ^2*D*X-9/2*s*c*d^2*ca^2*κ^2*D*X+9/2*s*c*ca^4*κ^2*D*X+4*s*c*d^2*ca*κ^3*D*X+1/2*s*c*ca^3*κ^3*D*X-8*s*c*d^2*sa^2*k^2*D*X-9/2*s^3*c*ca^2*k^2*D*X+9/2*s*c*d^2*ca^2*k^2*D*X-6*s*c*sa^2*ca^2*k^2*D*X-17/2*s*c*d^2*ca*κ*k^2*D*X-s*c*sa^2*ca*κ*k^2*D*X+s*c*ca^3*κ*k^2*D*X-1/2*s^3*c*κ^2*k^2*D*X-3/2*s*c*d^2*κ^2*k^2*D*X-s*c*ca^2*κ^2*k^2*D*X-1/2*s^3*c*k^4*D*X-1/2*s*c^3*k^4*D*X-1/2*s*c*sa^2*k^4*D*X+s*c*d^2*ca*κ^2*D^2*X-1/2*s*c*ca^3*κ^2*D^2*X+1/4*s*c*d^2*κ^3*D^2*X+1/2*s^3*c*ca*k^2*D^2*X-1/2*s*c*d^2*ca*k^2*D^2*X+11/2*s*c*sa^2*ca*k^2*D^2*X+s^3*c*κ*k^2*D^2*X+1/2*s*c*d^2*κ*k^2*D^2*X-1/2*s*c*sa^2*k^2*D^3*X-1/2*s*c*κ^2*k^2*D^3*X-2*s*c*d^2*κ^2*k^2*X^2+2*s*c*ca^3*κ^2*D*X^2-2*s*c*sa^2*ca*k^2*D*X^2-13/4*s*c*ca^2*κ^2*D^2*X^2+11/4*s*c*sa^2*k^2*D^2*X^2+1/4*s*c*ca*κ^2*D^3*X^2+10*s*c*d^4*ca*κ^2-4*s*c*d^2*ca^3*κ^2-3*s*c*d^4*κ^3+7*s*c*d^2*ca^2*κ^3+16*s^3*c*d^2*ca*k^2-6*s*c*d^4*ca*k^2-8*s*c*d^2*sa^2*ca*k^2+8*s^3*c*ca^3*k^2-12*s*c*d^2*ca^3*k^2+2*s*c*sa^2*ca^3*k^2-18*s^3*c*d^2*κ*k^2+10*s*c*d^2*sa^2*κ*k^2-2*s^3*c*ca^2*κ*k^2-2*s*c*d^2*ca^2*κ*k^2-3/4*s*c*d^4*κ^2*D+7/4*s*c*d^2*ca^2*κ^2*D-4*s*c*d^2*ca*κ^3*D-1/2*s*c*ca^3*κ^3*D-s^3*c*d^2*k^2*D-25/4*s*c*d^2*sa^2*k^2*D-9/2*s^3*c*ca^2*k^2*D+9*s*c*d^2*ca^2*k^2*D-21/4*s*c*sa^2*ca^2*k^2*D-2*s^3*c*ca*κ*k^2*D-s*c*sa^2*ca*κ*k^2*D+s*c*ca^3*κ*k^2*D+s^3*c*κ^2*k^2*D+s*c*d^2*κ^2*k^2*D-3/4*s*c*d^2*ca*κ^2*D^2+5/2*s*c*ca^3*κ^2*D^2+3/4*s*c*d^2*κ^3*D^2+1/2*s^3*c*ca*k^2*D^2-s*c*d^2*ca*k^2*D^2+7/2*s*c*sa^2*ca*k^2*D^2+1/2*s*c*d^2*κ*k^2*D^2-1/4*s*c*ca^2*κ^2*D^3-1/4*s*c*sa^2*k^2*D^3-7*s*c*d^4*κ^2*X+3*s*c*d^2*ca^2*κ^2*X-4*s*c*ca^4*κ^2*X-8*s*c*d^2*ca*κ^3*X-4*s*c*d^2*κ^4*X+4*s^3*c*ca^2*k^2*X-4*s*c*d^2*ca^2*k^2*X+4*s*c*d^2*ca*κ*k^2*X-1/2*s*c*d^2*ca*κ^2*D*X+6*s*c*ca^3*κ^2*D*X+35/4*s*c*d^2*κ^3*D*X+1/2*s*c*ca^2*κ^3*D*X-11/2*s^3*c*ca*k^2*D*X+15/2*s*c*d^2*ca*k^2*D*X-7/2*s*c*sa^2*ca*k^2*D*X+2*s^3*c*κ*k^2*D*X-21/2*s*c*d^2*κ*k^2*D*X-3/2*s*c*sa^2*κ*k^2*D*X+2*s*c*ca^2*κ*k^2*D*X-1/2*s*c*ca*κ^2*k^2*D*X+1/4*s*c*d^2*κ^2*D^2*X-1/2*s*c*ca^2*κ^2*D^2*X+1/2*s*c*κ^4*D^2*X+1/2*s^3*c*k^2*D^2*X+6*s*c*sa^2*k^2*D^2*X+1/2*s*c*k^4*D^2*X+3*s*c*ca^2*κ^2*D*X^2-3/2*s*c*sa^2*k^2*D*X^2+1/2*s*c*κ^2*k^2*D*X^2-9/4*s*c*ca*κ^2*D^2*X^2+1/4*s*c*κ^2*D^3*X^2+12*s*c*d^4*κ^2-9*s*c*d^2*ca^2*κ^2+8*s*c*d^2*ca*κ^3+14*s^3*c*d^2*k^2-2*s*c*d^4*k^2-9*s*c*d^2*sa^2*k^2+2*s^3*c*ca^2*k^2-10*s*c*d^2*ca^2*k^2+3*s*c*sa^2*ca^2*k^2-3*s*c*d^2*ca*κ^2*D-15/4*s*c*ca^3*κ^2*D-23/4*s*c*d^2*κ^3*D-1/2*s*c*ca^2*κ^3*D-15/2*s^3*c*ca*k^2*D+16*s*c*d^2*ca*k^2*D-13/4*s*c*sa^2*ca*k^2*D-s*c*ca^3*k^2*D+7*s^3*c*κ*k^2*D-9/2*s*c*d^2*κ*k^2*D-3/2*s*c*sa^2*κ*k^2*D+3*s*c*ca^2*κ*k^2*D-s*c*d^2*κ^2*D^2+7/2*s*c*ca^2*κ^2*D^2-3/2*s^3*c*k^2*D^2+9/2*s*c*sa^2*k^2*D^2-1/4*s*c*ca*κ^2*D^3+1/2*s*c*κ*k^2*D^3+2*s*c*d^2*ca*κ^2*X-6*s*c*ca^3*κ^2*X+6*s*c*d^2*κ^3*X+4*s^3*c*ca*k^2*X-4*s*c*d^2*ca*k^2*X+4*s*c*d^2*κ*k^2*X+17/2*s*c*d^2*κ^2*D*X+9/2*s*c*ca^2*κ^2*D*X+s*c*ca*κ^3*D*X+1/2*s*c*κ^4*D*X+1/2*s^3*c*k^2*D*X-7/2*s*c*sa^2*k^2*D*X+1/2*s*c*k^4*D*X-3/2*s*c*ca*κ^2*D^2*X-s*c*κ^3*D^2*X+1/2*s*c*k^2*D^3*X+2*s*c*ca*κ^2*D*X^2-11/4*s*c*κ^2*D^2*X^2-8*s*c*d^2*ca*κ^2+2*s*c*ca^3*κ^2+10*s*c*d^2*κ^3+4*s^3*c*ca*k^2-8*s*c*d^2*ca*k^2+2*s*c*sa^2*ca*k^2-4*s^3*c*κ*k^2+4*s*c*d^2*κ*k^2-25/4*s*c*d^2*κ^2*D-21/4*s*c*ca^2*κ^2*D-s*c*ca*κ^3*D+7/2*s^3*c*k^2*D+3*s*c*d^2*k^2*D-13/4*s*c*sa^2*k^2*D+7/2*s*c*ca*κ^2*D^2-1/4*s*c*κ^2*D^3+s*c*k^2*D^3-4*s*c*ca^2*κ^2*X+5*s*c*ca*κ^2*D*X-1/2*s*c*κ^3*D*X+s*c*ca*k^2*D*X-s*c*κ*k^2*D*X-s*c*κ^2*D^2*X+3/2*s*c*κ^2*D*X^2-9*s*c*d^2*κ^2+3*s*c*ca^2*κ^2-4*s^3*c*k^2+2*s*c*sa^2*k^2-2*s*c*d^2*κ*D-13/4*s*c*ca*κ^2*D-3/2*s*c*κ^3*D+s*c*ca*k^2*D-1/2*s*c*κ*k^2*D+9/2*s*c*κ^2*D^2-4*s*c*ca*κ^2*X-1/2*s*c*k^2*D*X+2*s*c*ca*κ^2-13/4*s*c*κ^2*D+2*s*c*κ^2) * ha1 +
      (1/2*s*c*d^2*ca^5*κ^2*k^2*D*X+2*s*c*d^4*ca^5*k^2*X^2-1/4*s*c*d^2*ca^5*k^2*D^2*X^2
        +3*s*c*d^4*ca^5*k^2*X-2*s*c*d^4*ca^4*κ*k^2*X+s*c*d^2*ca^5*κ^2*k^2*X
          +1/2*s*c*d^2*ca^4*κ^2*k^2*D*X-1/2*s*c*d^2*ca^5*k^2*D^2*X+3*s*c*d^4*ca^4*k^2*X^2
            +1/4*s*c*d^2*ca^5*k^2*D*X^2-1/4*s*c*d^2*ca^4*k^2*D^2*X^2-2*s*c*d^4*ca^5*k^2
              +4*s*c*d^4*ca^5*κ*X+5*s*c*d^4*ca^4*k^2*X+2*s*c*d^4*ca^3*κ*k^2*X
                +2*s*c*d^2*ca^5*κ*k^2*X+s*c*d^2*ca^4*κ^2*k^2*X-1/2*s*c*d^4*ca^5*D*X
                  -1/2*s*c*d^2*ca^4*κ*k^2*D*X-1/2*s*c*d^2*ca^3*κ^2*k^2*D*X
                    -1/2*s*c*ca^5*κ^2*k^2*D*X-1/2*s*c*d^2*ca^4*k^2*D^2*X-2*s*c*d^4*ca^3*k^2*X^2
                      -2*s*c*d^2*ca^5*k^2*X^2+1/4*s*c*d^2*ca^4*k^2*D*X^2+4*s*c*d^4*ca^5*κ
                        +2*s*c*d^4*ca^4*κ^2-1/4*s*c*d^4*ca^5*D+9*s*c*d^4*ca^4*κ*X
                          -2*s*c*d^4*ca^3*k^2*X-4*s*c*d^2*ca^5*k^2*X+4*s*c*d^4*ca^2*κ*k^2*X
                            +s*c*d^2*ca^4*κ*k^2*X-s*c*d^2*ca^3*κ^2*k^2*X+1/4*s*c*d^4*ca^4*D*X
                              -1/2*s*c*d^4*ca^3*κ*D*X-1/2*s*c*d^2*ca^5*κ*D*X
                                +1/2*s*c*d^2*ca^4*k^2*D*X-2*s*c*d^2*ca^3*κ*k^2*D*X
                                  -1/2*s*c*d^2*ca^2*κ^2*k^2*D*X-1/2*s*c*ca^4*κ^2*k^2*D*X
                                    -1/4*s*c*d^2*ca^4*κ*D^2*X-4*s*c*d^4*ca^2*k^2*X^2
                                      -3*s*c*d^2*ca^4*k^2*X^2+2*s*c*d^2*ca^3*k^2*D*X^2
                                        +1/4*s*c*ca^5*D^3*X^2-2*s*c*d^4*ca^5+7*s*c*d^4*ca^4*κ
                                          +2*s*c*d^4*ca^3*k^2-1/4*s*c*d^4*ca^4*D
                                            -1/2*s*c*d^4*ca^3*κ*D-1/2*s*c*d^2*ca^5*κ*D
                                              +1/4*s*c*d^2*ca^5*D^2+1/4*s*c*d^2*ca^4*κ*D^2
                                                -3*s*c*d^4*ca^4*X-4*s*c*d^2*ca^5*κ*X
                                                  -6*s*c*d^4*ca^2*k^2*X-5*s*c*d^2*ca^4*k^2*X
                                                    -2*s*c*d^4*ca*κ*k^2*X-2*s*c*d^2*ca^3*κ*k^2*X
                                                      -s*c*d^2*ca^2*κ^2*k^2*X+1/2*s*c*d^4*ca^3*D*X
                                                        +s*c*d^2*ca^5*D*X-1/2*s*c*d^4*ca^2*κ*D*X
                                                          -1/4*s*c*d^2*ca^4*κ*D*X
                                                            -s*c*d^2*ca^3*κ^2*D*X
                                                              +4*s*c*d^2*ca^3*k^2*D*X
                                                                +1/2*s*c*ca^5*k^2*D*X
                                                                  -3/2*s*c*d^2*ca^2*κ*k^2*D*X
                                                                    +1/2*s*c*ca^4*κ*k^2*D*X
                                                                      +1/2*s*c*ca^3*κ^2*k^2*D*X
                                                                        +1/4*s*c*d^2*ca^4*D^2*X
                                                                          -s*c*d^2*ca^3*κ*D^2*X
                                                                            +1/2*s*c*ca^5*D^3*X
                                                                              +7/2*s*c*d^2*ca^2*k^2*D*X^2-9/4*s*c*ca^5*D^2*X^2+1/4*s*c*d^2*ca*k^2*D^2*X^2+1/4*s*c*ca^4*D^3*X^2-14*s*c*d^4*ca^4-4*s*c*d^2*ca^5*κ-4*s*c*d^4*ca^2*κ^2-2*s*c*d^2*ca^4*κ^2+1/2*s*c*d^4*ca^3*D-3/2*s*c*d^2*ca^5*D-1/2*s*c*d^4*ca^2*κ*D-3/4*s*c*d^2*ca^4*κ*D+s*c*d^2*ca^4*D^2-1/2*s*c*d^2*ca^3*κ*D^2+1/4*s*c*ca^5*D^3-10*s*c*d^4*ca^3*X+2*s*c*d^4*ca^2*κ*X-9*s*c*d^2*ca^4*κ*X-2*s*c*d^2*ca^3*κ^2*X-s*c*d^4*ca*k^2*X-2*s*c*d^4*κ*k^2*X-s*c*d^2*ca^2*κ*k^2*X-1/2*s*c*d^2*ca^4*D*X+1/2*s*c*d^4*ca*κ*D*X+6*s*c*d^2*ca^3*κ*D*X+1/2*s*c*ca^5*κ*D*X-s*c*d^2*ca^2*κ^2*D*X+11/2*s*c*d^2*ca^2*k^2*D*X+2*s*c*d^2*ca*κ*k^2*D*X+1/2*s*c*ca^2*κ^2*k^2*D*X+s*c*d^2*ca^3*D^2*X-9/2*s*c*ca^5*D^2*X-s*c*d^2*ca^2*κ*D^2*X+1/2*s*c*d^2*ca*k^2*D^2*X+1/2*s*c*ca^4*D^3*X+s*c*d^4*k^2*X^2+s*c*d^2*ca^2*k^2*X^2+2*s*c*ca^5*D*X^2-9/4*s*c*d^2*ca*k^2*D*X^2-13/4*s*c*ca^4*D^2*X^2+1/4*s*c*d^2*k^2*D^2*X^2-14*s*c*d^4*ca^3+4*s*c*d^2*ca^5-4*s*c*d^4*ca^2*κ-7*s*c*d^2*ca^4*κ+s*c*d^4*ca^2*D-11/4*s*c*d^2*ca^4*D+1/2*s*c*d^4*ca*κ*D+11/2*s*c*d^2*ca^3*κ*D+1/2*s*c*ca^5*κ*D+3/2*s*c*d^2*ca^3*D^2-5/2*s*c*ca^5*D^2-1/2*s*c*d^2*ca^2*κ*D^2+1/4*s*c*ca^4*D^3-8*s*c*d^4*ca^2*X+3*s*c*d^2*ca^4*X-8*s*c*d^4*ca*κ*X-10*s*c*d^2*ca^3*κ*X-2*s*c*d^2*ca^2*κ^2*X+s*c*d^4*k^2*X+s*c*d^2*ca^2*k^2*X+7/2*s*c*d^2*ca^3*D*X+7/2*s*c*ca^5*D*X+1/2*s*c*d^4*κ*D*X+21/2*s*c*d^2*ca^2*κ*D*X+1/2*s*c*ca^4*κ*D*X+s*c*ca^3*κ^2*D*X-4*s*c*d^2*ca*k^2*D*X+2*s*c*d^2*κ*k^2*D*X-1/2*s*c*ca^2*κ*k^2*D*X+1/2*s*c*d^2*ca^2*D^2*X-13/2*s*c*ca^4*D^2*X+1/2*s*c^3*k^2*D^2*X+1/2*s*c*d^2*k^2*D^2*X+2*s*c*d^2*ca*k^2*X^2+3*s*c*ca^4*D*X^2-15/4*s*c*d^2*k^2*D*X^2+1/2*s*c*ca^2*k^2*D*X^2-10*s*c*d^4*ca^2+17*s*c*d^2*ca^4-4*s*c*d^4*ca*κ-2*s*c*d^2*ca^3*κ+2*s*c*d^4*κ^2-1/4*s*c*d^4*ca*D+5/2*s*c*d^2*ca^3*D+15/4*s*c*ca^5*D+1/2*s*c*d^4*κ*D+7*s*c*d^2*ca^2*κ*D+1/2*s*c*ca^4*κ*D+2*s*c*d^2*ca^2*D^2-7/2*s*c*ca^4*D^2+1/2*s*c*d^2*ca*κ*D^2+6*s*c*d^4*ca*X+6*s*c*d^2*ca^3*X-7*s*c*d^4*κ*X-9*s*c*d^2*ca^2*κ*X+4*s*c*d^2*ca*k^2*X-1/4*s*c*d^4*D*X+7/2*s*c*d^2*ca^2*D*X+6*s*c*ca^4*D*X+9/2*s*c*d^2*ca*κ*D*X-1/2*s*c*ca^3*κ*D*X+s*c*ca^2*κ^2*D*X+1/2*s*c^3*k^2*D*X-6*s*c*d^2*k^2*D*X+1/2*s*c*ca^2*k^2*D*X-s*c*ca^3*D^2*X+1/4*s*c*d^2*κ*D^2*X+2*s*c*d^2*k^2*X^2+1/2*s*c*ca^2*D^2*X^2-1/4*s*c*ca*D^3*X^2+16*s*c*d^4*ca+16*s*c*d^2*ca^3-2*s*c*ca^5-3*s*c*d^4*κ-s*c*d^2*ca^2*κ-3/4*s*c*d^4*D-s*c*d^2*ca^2*D+21/4*s*c*ca^4*D-4*s*c*d^2*ca*κ*D-1/2*s*c*ca^3*κ*D-s*c*d^2*κ^2*D+1/4*s*c*d^2*ca*D^2-s*c*ca^3*D^2+1/4*s*c*d^2*κ*D^2+7*s*c*d^4*X+5*s*c*d^2*ca^2*X+4*s*c*d^2*ca*κ*X+4*s*c*d^2*k^2*X-25/2*s*c*d^2*ca*D*X+11/4*s*c*d^2*κ*D*X-s*c*ca^2*κ*D*X-1/2*s*c*ca*k^2*D*X+1/4*s*c*d^2*D^2*X+1/2*s*c*ca^2*D^2*X-1/2*s*c*k^2*D^2*X-1/2*s*c*ca*D^3*X-3/2*s*c*ca^2*D*X^2-1/2*s*c*k^2*D*X^2+9/4*s*c*ca*D^2*X^2-1/4*s*c*D^3*X^2+16*s*c*d^4+10*s*c*d^2*ca^2-3*s*c*ca^4+8*s*c*d^2*ca*κ-19*s*c*d^2*ca*D+1/2*s*c*ca^3*D-5/4*s*c*d^2*κ*D-2*s*c*ca^2*κ*D-s*c*d^2*D^2-s*c*ca^2*D^2-1/4*s*c*ca*D^3-1/2*s*c*κ*D^3+4*s*c*d^2*ca*X+6*s*c*d^2*κ*X-8*s*c*d^2*D*X-5/2*s*c*ca^2*D*X-s*c*ca*κ*D*X-s*c*k^2*D*X+11/2*s*c*ca*D^2*X-s*c*D^3*X-2*s*c*ca*D*X^2+11/4*s*c*D^2*X^2+6*s*c*d^2*κ-37/4*s*c*d^2*D-2*s*c*ca^2*D-s*c*ca*κ*D+7/2*s*c*ca*D^2-5/4*s*c*D^3-9/2*s*c*ca*D*X-1/2*s*c*κ*D*X+6*s*c*D^2*X-3/2*s*c*D*X^2-9*s*c*d^2+s*c*ca^2-17/4*s*c*ca*D-s*c*κ*D+9/2*s*c*D^2-3*s*c*D*X+2*s*c*ca-13/4*s*c*D+2*s*c) * ha2 +
      (-1/2*s*c*d^2*ca^3*κ^2*k^2*D*X-2*s*c*d^4*ca^3*k^2*X^2+1/4*s*c*d^2*ca^3*k^2*D^2*X^2
        -3*s*c*d^4*ca^3*k^2*X+2*s*c*d^4*ca^2*κ*k^2*X-s*c*d^2*ca^3*κ^2*k^2*X
          -1/2*s*c*d^2*ca^2*κ^2*k^2*D*X+1/2*s*c*d^2*ca^3*k^2*D^2*X-3*s*c*d^4*ca^2*k^2*X^2
            -1/4*s*c*d^2*ca^3*k^2*D*X^2+1/4*s*c*d^2*ca^2*k^2*D^2*X^2+2*s*c*d^4*ca^3*k^2
              -4*s*c*d^4*ca^3*κ*X-5*s*c*d^4*ca^2*k^2*X-2*s*c*d^4*ca*κ*k^2*X-2*s*c*d^2*ca^3*κ*k^2*X
                -s*c*d^2*ca^2*κ^2*k^2*X+1/2*s*c*d^4*ca^3*D*X+1/2*s*c*d^2*ca^2*κ*k^2*D*X
                  +1/2*s*c*ca^3*κ^2*k^2*D*X+1/2*s*c*d^2*ca^2*k^2*D^2*X+2*s*c*d^2*ca^3*k^2*X^2
                    -1/4*s*c*d^2*ca^2*k^2*D*X^2+1/4*s*c*d^2*ca*k^2*D^2*X^2-4*s*c*d^4*ca^3*κ
                      +1/4*s*c*d^4*ca^3*D-7*s*c*d^4*ca^2*κ*X-s*c*d^4*ca*k^2*X+4*s*c*d^2*ca^3*k^2*X
                        -2*s*c*d^4*κ*k^2*X-s*c*d^2*ca^2*κ*k^2*X-1/4*s*c*d^4*ca^2*D*X
                          +1/2*s*c*d^4*ca*κ*D*X+1/2*s*c*d^2*ca^3*κ*D*X-1/2*s*c*d^2*ca^2*k^2*D*X
                            +2*s*c*d^2*ca*κ*k^2*D*X+1/2*s*c*ca^2*κ^2*k^2*D*X
                              +1/4*s*c*d^2*ca^2*κ*D^2*X+1/2*s*c*d^2*ca*k^2*D^2*X+s*c*d^4*k^2*X^2
                                +3*s*c*d^2*ca^2*k^2*X^2-9/4*s*c*d^2*ca*k^2*D*X^2
                                  +1/4*s*c*d^2*k^2*D^2*X^2-1/4*s*c*ca^3*D^3*X^2+2*s*c*d^4*ca^3
                                    -7*s*c*d^4*ca^2*κ+1/4*s*c*d^4*ca^2*D+1/2*s*c*d^4*ca*κ*D
                                      +1/2*s*c*d^2*ca^3*κ*D-1/4*s*c*d^2*ca^3*D^2
                                        +1/4*s*c*d^2*ca^2*κ*D^2-s*c*d^4*ca^2*X-4*s*c*d^4*ca*κ*X
                                          +4*s*c*d^2*ca^3*κ*X+s*c*d^4*k^2*X+5*s*c*d^2*ca^2*k^2*X
                                            -s*c*d^2*ca^3*D*X+1/2*s*c*d^4*κ*D*X
                                              +1/4*s*c*d^2*ca^2*κ*D*X-4*s*c*d^2*ca*k^2*D*X
                                                -1/2*s*c*ca^3*k^2*D*X+2*s*c*d^2*κ*k^2*D*X
                                                  -1/2*s*c*ca^2*κ*k^2*D*X+1/4*s*c*d^2*ca^2*D^2*X
                                                    +1/2*s*c*d^2*ca*κ*D^2*X+1/2*s*c*d^2*k^2*D^2*X
                                                      -1/2*s*c*ca^3*D^3*X+2*s*c*d^2*ca*k^2*X^2
                                                        -15/4*s*c*d^2*k^2*D*X^2
                                                          +9/4*s*c*ca^3*D^2*X^2
                                                            -1/4*s*c*ca^2*D^3*X^2+6*s*c*d^4*ca^2
                                                              -4*s*c*d^4*ca*κ+4*s*c*d^2*ca^3*κ
                                                                -1/4*s*c*d^4*ca*D
                                                                  +3/2*s*c*d^2*ca^3*D
                                                                    +1/2*s*c*d^4*κ*D
                                                                      +1/4*s*c*d^2*ca^2*κ*D
                                                                        +1/2*s*c*d^2*ca*κ*D^2
                                                                          -1/4*s*c*ca^3*D^3
                                                                            +4*s*c*d^4*ca*X
                                                                              -3*s*c*d^4*κ*X
                                                                                +7*s*c*d^2*ca^2*κ*X+4*s*c*d^2*ca*k^2*X-1/4*s*c*d^4*D*X-4*s*c*d^2*ca*κ*D*X-1/2*s*c*ca^3*κ*D*X-6*s*c*d^2*k^2*D*X-1/2*s*c*d^2*ca*D^2*X+9/2*s*c*ca^3*D^2*X+3/4*s*c*d^2*κ*D^2*X-1/2*s*c*ca^2*D^3*X+2*s*c*d^2*k^2*X^2-2*s*c*ca^3*D*X^2+13/4*s*c*ca^2*D^2*X^2-1/4*s*c*ca*D^3*X^2+10*s*c*d^4*ca-4*s*c*d^2*ca^3-3*s*c*d^4*κ+7*s*c*d^2*ca^2*κ-3/4*s*c*d^4*D+7/4*s*c*d^2*ca^2*D-4*s*c*d^2*ca*κ*D-1/2*s*c*ca^3*κ*D-3/4*s*c*d^2*ca*D^2+5/2*s*c*ca^3*D^2+3/4*s*c*d^2*κ*D^2-1/4*s*c*ca^2*D^3+7*s*c*d^4*X+s*c*d^2*ca^2*X+8*s*c*d^2*ca*κ*X+4*s*c*d^2*k^2*X-5*s*c*d^2*ca*D*X-7/2*s*c*ca^3*D*X-31/4*s*c*d^2*κ*D*X-1/2*s*c*ca^2*κ*D*X-1/2*s*c*ca*k^2*D*X+1/4*s*c*d^2*D^2*X+13/2*s*c*ca^2*D^2*X-1/2*s*c*ca*D^3*X-3*s*c*ca^2*D*X^2-1/2*s*c*k^2*D*X^2+9/4*s*c*ca*D^2*X^2-1/4*s*c*D^3*X^2+14*s*c*d^4-9*s*c*d^2*ca^2+8*s*c*d^2*ca*κ-3*s*c*d^2*ca*D-15/4*s*c*ca^3*D-31/4*s*c*d^2*κ*D-1/2*s*c*ca^2*κ*D-s*c*d^2*D^2+7/2*s*c*ca^2*D^2-1/4*s*c*ca*D^3+10*s*c*d^2*κ*X-8*s*c*d^2*D*X-6*s*c*ca^2*D*X-s*c*ca*κ*D*X-1/2*s*c*k^2*D*X+11/2*s*c*ca*D^2*X-1/2*s*c*D^3*X-2*s*c*ca*D*X^2+11/4*s*c*D^2*X^2-8*s*c*d^2*ca+2*s*c*ca^3+10*s*c*d^2*κ-25/4*s*c*d^2*D-21/4*s*c*ca^2*D-s*c*ca*κ*D+7/2*s*c*ca*D^2-1/4*s*c*D^3-7/2*s*c*ca*D*X-3/2*s*c*κ*D*X+6*s*c*D^2*X-3/2*s*c*D*X^2-9*s*c*d^2+3*s*c*ca^2-13/4*s*c*ca*D-3/2*s*c*κ*D+9/2*s*c*D^2-7/2*s*c*D*X+2*s*c*ca-13/4*s*c*D+2*s*c) * E1 +
      (2*s*c*d^4*ca^4*κ*k^2*X+1/2*s*c*d^4*ca^4*κ^2*D*X-4*s*c*d^4*ca^4*k^2*X
        -1/2*s*c*d^2*ca^3*κ^2*k^2*D*X+1/2*s*c*d^2*ca^4*k^2*D^2*X+2*s*c*d^4*ca^3*k^2*X^2
          -1/4*s*c*d^2*ca^3*k^2*D^2*X^2-7*s*c*d^4*ca^3*k^2*X-2*s*c*d^4*ca^2*κ*k^2*X
            -2*s*c*d^2*ca^4*κ*k^2*X-s*c*d^2*ca^3*κ^2*k^2*X-1/2*s*c*d^2*ca^4*κ^2*D*X
              -1/2*s*c*d^2*ca^4*k^2*D*X+s*c*d^2*ca^3*κ*k^2*D*X-1/2*s*c*d^2*ca^2*κ^2*k^2*D*X
                +1/2*s*c*d^2*ca^3*k^2*D^2*X+3*s*c*d^4*ca^2*k^2*X^2+1/4*s*c*d^2*ca^3*k^2*D*X^2
                  -1/4*s*c*d^2*ca^2*k^2*D^2*X^2+2*s*c*d^4*ca^3*k^2-4*s*c*d^4*ca^4*X
                    +4*s*c*d^4*ca^3*κ*X-s*c*d^4*ca^2*k^2*X+4*s*c*d^2*ca^4*k^2*X
                      -2*s*c*d^4*ca*κ*k^2*X-s*c*d^2*ca^2*κ^2*k^2*X-1/2*s*c*d^4*ca^3*D*X
                        -s*c*d^2*ca^3*k^2*D*X+3/2*s*c*d^2*ca^2*κ*k^2*D*X+1/2*s*c*ca^3*κ^2*k^2*D*X
                          +1/2*s*c*d^2*ca^4*D^2*X+1/2*s*c*d^2*ca^2*k^2*D^2*X
                            -2*s*c*d^2*ca^3*k^2*X^2+1/4*s*c*d^2*ca^2*k^2*D*X^2
                              -1/4*s*c*d^2*ca*k^2*D^2*X^2-4*s*c*d^4*ca^3*κ+1/4*s*c*d^4*ca^3*D
                                -6*s*c*d^4*ca^3*X+7*s*c*d^4*ca^2*κ*X+3*s*c*d^4*ca*k^2*X
                                  +6*s*c*d^2*ca^3*k^2*X+s*c*d^2*ca^2*κ*k^2*X+1/4*s*c*d^4*ca^2*D*X
                                    -9/2*s*c*d^2*ca^4*D*X-1/2*s*c*d^4*ca*κ*D*X
                                      -1/2*s*c*d^2*ca^3*κ*D*X-1/2*s*c*d^4*κ^2*D*X
                                        -9/2*s*c*d^2*ca^2*k^2*D*X+2*s*c*d^2*ca*κ*k^2*D*X
                                          -s*c*ca^3*κ*k^2*D*X+1/2*s*c*ca^2*κ^2*k^2*D*X
                                            +1/2*s*c*d^2*ca^3*D^2*X-1/4*s*c*d^2*ca^2*κ*D^2*X
                                              +1/2*s*c*d^2*ca*k^2*D^2*X-s*c*d^4*k^2*X^2
                                                -3*s*c*d^2*ca^2*k^2*X^2+9/4*s*c*d^2*ca*k^2*D*X^2
                                                  -1/4*s*c*d^2*k^2*D^2*X^2+1/4*s*c*ca^3*D^3*X^2
                                                    +2*s*c*d^4*ca^3-7*s*c*d^4*ca^2*κ
                                                      +1/4*s*c*d^4*ca^2*D+1/2*s*c*d^4*ca*κ*D
                                                        +1/2*s*c*d^2*ca^3*κ*D-1/4*s*c*d^2*ca^3*D^2
                                                          +1/4*s*c*d^2*ca^2*κ*D^2+s*c*d^4*ca^2*X
                                                            +8*s*c*d^2*ca^4*X+4*s*c*d^4*ca*κ*X
                                                              -4*s*c*d^2*ca^3*κ*X+4*s*c*d^4*κ^2*X
                                                                +s*c*d^4*k^2*X
                                                                  +5*s*c*d^2*ca^2*k^2*X
                                                                    -11/2*s*c*d^2*ca^3*D*X
                                                                      +1/2*s*c*d^4*κ*D*X
                                                                        -1/4*s*c*d^2*ca^2*κ*D*X
                                                                          -8*s*c*d^2*ca*k^2*D*X
                                                                            +1/2*s*c*ca^3*k^2*D*X
                                                                              +s*c*d^2*κ*k^2*D*X
                                                                                -3/2*s*c*ca^2*κ*k^2*D*X+1/4*s*c*d^2*ca^2*D^2*X-1/2*s*c*ca^4*D^2*X-1/2*s*c*d^2*ca*κ*D^2*X-1/2*s*c*d^2*κ^2*D^2*X-2*s*c*d^2*ca*k^2*X^2+15/4*s*c*d^2*k^2*D*X^2-9/4*s*c*ca^3*D^2*X^2+1/4*s*c*ca^2*D^3*X^2+6*s*c*d^4*ca^2-4*s*c*d^4*ca*κ+4*s*c*d^2*ca^3*κ-1/4*s*c*d^4*ca*D+3/2*s*c*d^2*ca^3*D+1/2*s*c*d^4*κ*D+1/4*s*c*d^2*ca^2*κ*D+1/2*s*c*d^2*ca*κ*D^2-1/4*s*c*ca^3*D^3-2*s*c*d^4*ca*X+12*s*c*d^2*ca^3*X-13*s*c*d^4*κ*X-7*s*c*d^2*ca^2*κ*X+4*s*c*d^2*ca*k^2*X+1/4*s*c*d^4*D*X-9/2*s*c*d^2*ca^2*D*X+9/2*s*c*ca^4*D*X+4*s*c*d^2*ca*κ*D*X+1/2*s*c*ca^3*κ*D*X-3/2*s*c*d^2*k^2*D*X+s*c*d^2*ca*D^2*X-1/2*s*c*ca^3*D^2*X+1/4*s*c*d^2*κ*D^2*X-1/2*s*c*k^2*D^3*X-2*s*c*d^2*k^2*X^2+2*s*c*ca^3*D*X^2-13/4*s*c*ca^2*D^2*X^2+1/4*s*c*ca*D^3*X^2+10*s*c*d^4*ca-4*s*c*d^2*ca^3-3*s*c*d^4*κ+7*s*c*d^2*ca^2*κ-3/4*s*c*d^4*D+7/4*s*c*d^2*ca^2*D-4*s*c*d^2*ca*κ*D-1/2*s*c*ca^3*κ*D-3/4*s*c*d^2*ca*D^2+5/2*s*c*ca^3*D^2+3/4*s*c*d^2*κ*D^2-1/4*s*c*ca^2*D^3-7*s*c*d^4*X+3*s*c*d^2*ca^2*X-4*s*c*ca^4*X-8*s*c*d^2*ca*κ*X-4*s*c*d^2*κ^2*X-1/2*s*c*d^2*ca*D*X+6*s*c*ca^3*D*X+35/4*s*c*d^2*κ*D*X+1/2*s*c*ca^2*κ*D*X-1/2*s*c*ca*k^2*D*X+1/4*s*c*d^2*D^2*X-1/2*s*c*ca^2*D^2*X+1/2*s*c*κ^2*D^2*X+3*s*c*ca^2*D*X^2+1/2*s*c*k^2*D*X^2-9/4*s*c*ca*D^2*X^2+1/4*s*c*D^3*X^2+14*s*c*d^4-9*s*c*d^2*ca^2+8*s*c*d^2*ca*κ-3*s*c*d^2*ca*D-15/4*s*c*ca^3*D-31/4*s*c*d^2*κ*D-1/2*s*c*ca^2*κ*D-s*c*d^2*D^2+7/2*s*c*ca^2*D^2-1/4*s*c*ca*D^3+2*s*c*d^2*ca*X-6*s*c*ca^3*X+6*s*c*d^2*κ*X+17/2*s*c*d^2*D*X+9/2*s*c*ca^2*D*X+s*c*ca*κ*D*X+1/2*s*c*κ^2*D*X-3/2*s*c*ca*D^2*X-s*c*κ*D^2*X+2*s*c*ca*D*X^2-11/4*s*c*D^2*X^2-8*s*c*d^2*ca+2*s*c*ca^3+10*s*c*d^2*κ-25/4*s*c*d^2*D-21/4*s*c*ca^2*D-s*c*ca*κ*D+7/2*s*c*ca*D^2-1/4*s*c*D^3-4*s*c*ca^2*X+5*s*c*ca*D*X-1/2*s*c*κ*D*X-s*c*D^2*X+3/2*s*c*D*X^2-9*s*c*d^2+3*s*c*ca^2-13/4*s*c*ca*D-3/2*s*c*κ*D+9/2*s*c*D^2-4*s*c*ca*X+2*s*c*ca-13/4*s*c*D+2*s*c) * E2 +
      (1/2*s*c*d^2*ca^4*κ^3*D+1/2*s*c*d^2*ca^4*κ^2*D*X+s*c*d^2*ca^4*κ^2*D-4*s*c*d^2*ca^4*κ
        -1/2*s*c*d^2*ca^3*κ*D+1/2*s*c*ca^4*κ*D^2-4*s*c*d^2*ca^4*X+1/2*s*c*ca^4*D^2*X
          -8*s*c*d^2*ca^4-2*s*c*d^2*ca^3*κ-1/2*s*c*d^2*ca^3*D+s*c*d^2*ca^2*κ*D-9/2*s*c*ca^4*κ*D
            -1/2*s*c*d^2*κ^3*D+s*c*ca^4*D^2-6*s*c*d^2*ca^3*X-9/2*s*c*ca^4*D*X-1/2*s*c*d^2*κ^2*D*X
              +1/2*s*c*ca^3*D^2*X-8*s*c*d^2*ca^3+14*s*c*d^2*ca^2*κ+4*s*c*ca^4*κ+4*s*c*d^2*κ^3
                +s*c*d^2*ca^2*D-9*s*c*ca^4*D-1/2*s*c*d^2*ca*κ*D-2*s*c*ca^3*κ*D+1/2*s*c*ca^3*D^2
                  -1/2*s*c*κ^3*D^2+4*s*c*ca^4*X+4*s*c*d^2*κ^2*X-13/2*s*c*ca^3*D*X+s*c*d^2*κ*D*X
                    +1/2*s*c*ca^2*D^2*X-1/2*s*c*κ^2*D^2*X-1/2*s*c*k^2*D^2*X+14*s*c*d^2*ca^2
                      +8*s*c*ca^4+14*s*c*d^2*ca*κ+2*s*c*ca^3*κ-8*s*c*d^2*κ^2-1/2*s*c*d^2*ca*D
                        -17/2*s*c*ca^3*D+s*c*d^2*κ*D-1/2*s*c*κ^3*D+1/2*s*c*ca^2*D^2+2*s*c*d^2*ca*X
                          +6*s*c*ca^3*X-16*s*c*d^2*κ*X-9/2*s*c*ca^2*D*X-1/2*s*c*κ^2*D*X
                            -1/2*s*c*k^2*D*X+1/2*s*c*ca*D^2*X+s*c*κ*D^2*X+16*s*c*d^2*ca+8*s*c*ca^3
                              -18*s*c*d^2*κ-2*s*c*ca^2*κ-s*c*d^2*D-9/2*s*c*ca^2*D-2*s*c*ca*κ*D
                                +s*c*κ^2*D+1/2*s*c*ca*D^2+4*s*c*ca^2*X-11/2*s*c*ca*D*X+2*s*c*κ*D*X
                                  +1/2*s*c*D^2*X+14*s*c*d^2+2*s*c*ca^2-15/2*s*c*ca*D+7*s*c*κ*D
                                    -3/2*s*c*D^2+4*s*c*ca*X+1/2*s*c*D*X+4*s*c*ca-4*s*c*κ+7/2*s*c*D
                                      -4*s*c) * hDdef +
      (-2*s*c*d^4*ca^6*κ^2*k^2-1/2*s*c*d^4*ca^6*κ^3*D-s*c*d^4*ca^6*κ^2*D
        -1/2*s*c*d^2*ca^6*κ*k^2*D^2-4*s*c*d^4*ca^5*κ*k^2*X+1/2*s*c*d^2*ca^5*κ*k^2*D^2*X
          +8*s*c*d^4*ca^6*k^2+4*s*c*d^4*ca^5*κ*k^2+6*s*c*d^4*ca^4*κ^2*k^2+2*s*c*d^2*ca^6*κ^2*k^2
            +1/2*s*c*d^4*ca^4*κ^3*D+1/2*s*c*d^2*ca^6*κ^3*D+1/2*s*c*d^2*ca^6*κ*k^2*D
              -s*c*d^2*ca^6*k^2*D^2-4*s*c*d^4*ca^5*k^2*X-6*s*c*d^4*ca^4*κ*k^2*X
                -1/2*s*c*d^2*ca^5*κ*k^2*D*X+1/2*s*c*d^2*ca^5*k^2*D^2*X
                  +1/2*s*c*d^2*ca^4*κ*k^2*D^2*X+4*s*c*d^4*ca^6*κ-8*s*c*d^4*ca^5*κ^2
                    +10*s*c*d^4*ca^5*k^2-4*s*c*d^4*ca^4*κ*k^2+s*c*d^4*ca^5*κ*D+s*c*d^2*ca^6*κ^2*D
                      +s*c*d^2*ca^6*k^2*D-s*c*d^2*ca^5*κ*k^2*D-s*c*d^2*ca^4*κ^2*k^2*D
                        -1/2*s*c*d^2*ca^6*κ*D^2-s*c*d^2*ca^5*k^2*D^2+1/2*s*c*d^2*ca^4*κ*k^2*D^2
                          -10*s*c*d^4*ca^4*k^2*X+4*s*c*d^4*ca^3*κ*k^2*X+4*s*c*d^2*ca^5*κ*k^2*X
                            -1/2*s*c*d^2*ca^5*k^2*D*X-1/2*s*c*d^2*ca^4*κ*k^2*D*X
                              +s*c*d^2*ca^4*k^2*D^2*X+8*s*c*d^4*ca^6-2*s*c*d^4*ca^5*κ
                                -16*s*c*d^4*ca^4*κ^2-6*s*c*d^4*ca^4*k^2-8*s*c*d^2*ca^6*k^2
                                  -2*s*c*d^2*ca^5*κ*k^2-6*s*c*d^4*ca^2*κ^2*k^2
                                    -4*s*c*d^2*ca^4*κ^2*k^2+s*c*d^4*ca^5*D-s*c*d^4*ca^4*κ*D
                                      +9/2*s*c*d^2*ca^6*κ*D+s*c*d^4*ca^3*κ^2*D+s*c*d^2*ca^5*κ^2*D
                                        +1/2*s*c*d^4*ca^2*κ^3*D-1/2*s*c*d^2*ca^4*κ^3*D
                                          +2*s*c*d^2*ca^5*k^2*D+1/2*s*c*d^2*ca^4*κ*k^2*D
                                            -s*c*d^2*ca^6*D^2-1/2*s*c*d^2*ca^5*κ*D^2
                                              +1/2*s*c*d^2*ca^4*κ^2*D^2-6*s*c*d^4*ca^3*k^2*X
                                                +4*s*c*d^2*ca^5*k^2*X+8*s*c*d^4*ca^2*κ*k^2*X
                                                  +6*s*c*d^2*ca^4*κ*k^2*X-s*c*d^2*ca^4*k^2*D*X
                                                    -4*s*c*d^2*ca^3*κ*k^2*D*X
                                                      +s*c*d^2*ca^3*k^2*D^2*X-1/2*s*c*ca^5*κ*D^3*X
                                                        +12*s*c*d^4*ca^5-24*s*c*d^4*ca^4*κ
                                                          -8*s*c*d^2*ca^6*κ+8*s*c*d^2*ca^5*κ^2
                                                            -4*s*c*d^4*ca^2*κ^3
                                                              -12*s*c*d^4*ca^3*k^2
                                                                -12*s*c*d^2*ca^5*k^2
                                                                  -2*s*c*d^2*ca^4*κ*k^2
                                                                    +1/2*s*c*d^4*ca^4*D
                                                                      +9*s*c*d^2*ca^6*D
                                                                        +11/2*s*c*d^2*ca^5*κ*D
                                                                          +s*c*d^4*ca^2*κ^2*D
                                                                            +1/2*s*c*d^2*ca^4*κ^2*D+s*c*d^2*ca^3*κ^3*D+9*s*c*d^2*ca^4*k^2*D+s*c*d^2*ca^3*κ*k^2*D+s*c*ca^5*κ*k^2*D+2*s*c*d^2*ca^2*κ^2*k^2*D+s*c*ca^4*κ^2*k^2*D-s*c*d^2*ca^5*D^2+s*c*d^2*ca^4*κ*D^2+1/2*s*c*ca^6*κ*D^2+3/2*s*c*d^2*ca^3*κ^2*D^2+1/2*s*c*d^2*ca^2*κ^3*D^2+1/2*s*c*d^2*ca^2*κ*k^2*D^2-1/2*s*c*ca^5*κ*D^3+2*s*c*d^4*ca^2*k^2*X+10*s*c*d^2*ca^4*k^2*X-5*s*c*d^2*ca^3*k^2*D*X-7*s*c*d^2*ca^2*κ*k^2*D*X+9/2*s*c*ca^5*κ*D^2*X+s*c*d^2*ca^2*k^2*D^2*X-1/2*s*c*d^2*ca*κ*k^2*D^2*X-1/2*s*c*ca^5*D^3*X-1/2*s*c*ca^4*κ*D^3*X-16*s*c*d^2*ca^6-16*s*c*d^4*ca^3*κ-4*s*c*d^2*ca^5*κ+10*s*c*d^4*ca^2*κ^2+16*s*c*d^2*ca^4*κ^2+2*s*c*d^2*ca^3*κ^3-4*s*c*d^4*ca^2*k^2+2*s*c*d^2*ca^3*κ*k^2+2*s*c*d^4*κ^2*k^2+2*s*c*d^2*ca^2*κ^2*k^2-1/2*s*c*d^4*ca^3*D+11*s*c*d^2*ca^5*D+2*s*c*d^2*ca^4*κ*D-9/2*s*c*ca^6*κ*D-s*c*d^4*ca*κ^2*D-21/2*s*c*d^2*ca^3*κ^2*D-s*c*ca^5*κ^2*D-1/2*s*c*d^4*κ^3*D+s*c*d^2*ca^2*κ^3*D+14*s*c*d^2*ca^3*k^2*D-s*c*ca^5*k^2*D-11/2*s*c*d^2*ca^2*κ*k^2*D+3*s*c*ca^4*κ*k^2*D-1/2*s*c*d^2*ca^4*D^2+s*c*ca^6*D^2+5*s*c*ca^5*κ*D^2+3/2*s*c*d^2*ca^2*κ^2*D^2+s*c*d^2*ca^2*k^2*D^2-1/2*s*c*ca^5*D^3-1/2*s*c*ca^4*κ*D^3+1/2*s*c*ca^2*κ*k^2*D^3+2*s*c*d^4*ca*k^2*X+10*s*c*d^2*ca^3*k^2*X-2*s*c*d^4*κ*k^2*X-2*s*c*d^2*ca^2*κ*k^2*X-4*s*c*ca^5*κ*D*X-12*s*c*d^2*ca^2*k^2*D*X+9/2*s*c*d^2*ca*κ*k^2*D*X+9/2*s*c*ca^5*D^2*X+13/2*s*c*ca^4*κ*D^2*X+1/2*s*c*d^2*ca*k^2*D^2*X-1/2*s*c*d^2*κ*k^2*D^2*X-s*c*ca^4*D^3*X+2*s*c*d^4*ca^3-24*s*c*d^2*ca^5+34*s*c*d^4*ca^2*κ+24*s*c*d^2*ca^4*κ+4*s*c*ca^6*κ+12*s*c*d^4*ca*κ^2+14*s*c*d^2*ca^3*κ^2+4*s*c*d^4*κ^3+6*s*c*d^2*ca^2*κ^3+6*s*c*d^4*ca*k^2+4*s*c*d^2*ca^3*k^2+6*s*c*d^2*ca^2*κ*k^2-1/2*s*c*d^4*ca^2*D+7*s*c*d^2*ca^4*D-9*s*c*ca^6*D+s*c*d^4*ca*κ*D-17*s*c*d^2*ca^3*κ*D-21/2*s*c*ca^5*κ*D-39/2*s*c*d^2*ca^2*κ^2*D-s*c*ca^4*κ^2*D-s*c*ca^3*κ^3*D-7*s*c*d^2*ca^2*k^2*D-s*c*ca^4*k^2*D-s*c*ca^3*κ*k^2*D-s*c*d^2*κ^2*k^2*D-s*c*ca^2*κ^2*k^2*D-2*s*c*d^2*ca^3*D^2+11/2*s*c*ca^5*D^2+13/2*s*c*ca^4*κ*D^2-1/2*s*c*d^2*ca*κ^2*D^2-1/2*s*c*d^2*κ^3*D^2-1/2*s*c*ca^2*κ^3*D^2+s*c*d^2*ca*k^2*D^2-1/2*s*c^3*κ*k^2*D^2-1/2*s*c*d^2*κ*k^2*D^2-3/2*s*c*ca^4*D^3+s*c*ca^2*k^2*D^3+8*s*c*d^2*ca^2*k^2*X-4*s*c*d^2*ca*κ*k^2*X-4*s*c*ca^5*D*X-6*s*c*ca^4*κ*D*X-15/2*s*c*d^2*ca*k^2*D*X+15/2*s*c*d^2*κ*k^2*D*X-s*c*ca^2*κ*k^2*D*X+11*s*c*ca^4*D^2*X-s*c*ca^3*D^3*X+28*s*c*d^4*ca^2-8*s*c*d^2*ca^4+8*s*c*ca^6-14*s*c*d^4*ca*κ+32*s*c*d^2*ca^3*κ+6*s*c*ca^5*κ-6*s*c*d^4*κ^2+4*s*c*d^2*ca^2*κ^2+2*s*c*d^4*k^2+8*s*c*d^2*ca^2*k^2-1/2*s*c*d^4*ca*D+5/2*s*c*d^2*ca^3*D-16*s*c*ca^5*D+s*c*d^4*κ*D-43*s*c*d^2*ca^2*κ*D-8*s*c*ca^4*κ*D-1/2*s*c*d^2*ca*κ^2*D-3/2*s*c*ca^2*κ^3*D-16*s*c*d^2*ca*k^2*D+2*s*c*ca^3*k^2*D-1/2*s*c^3*κ*k^2*D+9/2*s*c*d^2*κ*k^2*D-3/2*s*c*ca^2*κ*k^2*D-2*s*c*d^2*ca^2*D^2+33/2*s*c*ca^4*D^2+5/2*s*c*d^2*ca*κ*D^2+2*s*c*ca^3*κ*D^2-s*c*ca^3*D^3-1/2*s*c*κ*k^2*D^3+4*s*c*d^2*ca*k^2*X-4*s*c*d^2*κ*k^2*X-10*s*c*ca^4*D*X-s*c*ca^2*k^2*D*X+11*s*c*ca^3*D^2*X-s*c*ca^2*κ*D^2*X-s*c*ca^2*D^3*X+1/2*s*c*ca*κ*D^3*X+10*s*c*d^4*ca-8*s*c*d^2*ca^3+12*s*c*ca^5-18*s*c*d^4*κ-12*s*c*d^2*ca*κ^2-4*s*c*d^2*κ^3+8*s*c*d^2*ca*k^2-4*s*c*d^2*κ*k^2-s*c*d^4*D-49/2*s*c*d^2*ca^2*D-22*s*c*ca^4*D-7/2*s*c*d^2*ca*κ*D-s*c*ca^3*κ*D+6*s*c*d^2*κ^2*D+s*c*ca^2*κ^2*D-3*s*c*d^2*k^2*D+s*c*ca^2*k^2*D+16*s*c*ca^3*D^2+2*s*c*ca^2*κ*D^2+1/2*s*c*κ^3*D^2+1/2*s*c*κ*k^2*D^2-s*c*ca^2*D^3+1/2*s*c*ca*κ*D^3-10*s*c*ca^3*D*X+3*s*c*ca^2*κ*D*X-s*c*ca*k^2*D*X+s*c*κ*k^2*D*X+10*s*c*ca^2*D^2*X-9/2*s*c*ca*κ*D^2*X-1/2*s*c*ca*D^3*X+1/2*s*c*κ*D^3*X+12*s*c*d^4-6*s*c*d^2*ca^2+8*s*c*ca^4+18*s*c*d^2*ca*κ-2*s*c*ca^3*κ-15/2*s*c*d^2*ca*D-23*s*c*ca^3*D+21*s*c*d^2*κ*D+7*s*c*ca^2*κ*D+2*s*c*ca*κ^2*D+1/2*s*c*κ^3*D-s*c*ca*k^2*D+s*c*κ*k^2*D-1/2*s*c*d^2*D^2+12*s*c*ca^2*D^2-7*s*c*ca*κ*D^2-s*c*κ^2*D^2-1/2*s*c*ca*D^3+1/2*s*c*κ*D^3-7*s*c*ca^2*D*X+4*s*c*ca*κ*D*X+11/2*s*c*ca*D^2*X-11/2*s*c*κ*D^2*X-4*s*c*d^2*ca+8*s*c*ca^3-4*s*c*ca^2*κ-15/2*s*c*d^2*D-6*s*c*ca^2*D+13/2*s*c*ca*κ*D+15/2*s*c*ca*D^2-15/2*s*c*κ*D^2+3/2*s*c*D^3-3*s*c*ca*D*X+3*s*c*κ*D*X-4*s*c*d^2-4*s*c*ca*κ-3*s*c*ca*D+3*s*c*κ*D-7/2*s*c*D^2+4*s*c*D) * hX

/-- DLMF 22.9.23: cyclic identity (three points, rank 4; corrected), at points where
the functions are finite. Corrected from the printed DLMF formula: the printed right side repeats
`s_{2,3}^{(4)} d_{2,3}^{(4)}`; the last term is `s_{3,3}^{(4)} d_{3,3}^{(4)}` (printed right side
≈ 4.208 - 0.036i against left side ≈ 0.552 + 0.183i at `k = 0.6`, `z = 0.37 + 0.21i`). -/
@[dlmf 22.9.E7,
  dlmf 22.9.E23 "corrected: last summand s_{3,3} d_{3,3} instead of the repeated s_{2,3} d_{2,3}"]
theorem jacobi_cyclic_sdcc_three {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg4 : ∀ m : ℕ, JacobiRegulark .n (jacobiCyclicArg 4 m 3 z k) k) :
    jacobiCyclicS 4 1 3 z k * jacobiCyclicD 4 1 3 z k * jacobiCyclicC 4 2 3 z k *
      jacobiCyclicC 4 3 3 z k + jacobiCyclicS 4 2 3 z k * jacobiCyclicD 4 2 3 z k *
        jacobiCyclicC 4 3 3 z k * jacobiCyclicC 4 1 3 z k + jacobiCyclicS 4 3 3 z k *
          jacobiCyclicD 4 3 3 z k * jacobiCyclicC 4 1 3 z k * jacobiCyclicC 4 2 3 z k =
            jacobiCyclicKappa k ^ 2 / (1 - jacobiCyclicKappa k ^ 2) * (jacobiCyclicS 4 1 3 z k *
              jacobiCyclicD 4 1 3 z k + jacobiCyclicS 4 2 3 z k * jacobiCyclicD 4 2 3 z k +
                jacobiCyclicS 4 3 3 z k * jacobiCyclicD 4 3 3 z k) := by
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
  linear_combination (2*s*d^3*ca^6*κ^3*k^2*X+s*d^3*ca^4*κ^3*k^2*D*X-2*s*d^3*ca^6*κ*k^2*X
      -2*s*d^3*ca^4*κ^3*k^2*X-2*s*d*ca^6*κ^3*k^2*X-2*s*d^3*ca^2*κ^3*k^2*D*X-2*s*c^2*d*ca^4*κ^2*k^2
        +4*s*d^3*ca^4*κ*k^2*X+2*s*d*ca^6*κ*k^2*X-2*s*d^3*ca^2*κ^3*k^2*X+2*s*d*ca^4*κ^3*k^2*X
          -s*d^3*ca^2*κ^4*D-s*d*ca^4*κ*k^2*D*X+s*d^3*κ^3*k^2*D*X+2*s*c^2*d*ca^4*k^2
            +2*s*c^2*d*ca^2*κ^2*k^2-2*s*d*ca^4*κ^2*k^2+2*s*d*ca^3*κ^2*k^2*D-2*s*d^3*ca^2*κ*k^2*X
              -4*s*d*ca^4*κ*k^2*X+2*s*d^3*κ^3*k^2*X+s*d^3*ca^2*κ^2*D+s*d^3*κ^4*D+2*s*d*ca^2*k^4*X
                +s*d*ca^2*κ*k^2*D*X-2*s*c^2*d*ca^2*k^2+2*s*d*ca^4*k^2+2*s*d*ca^2*κ^2*k^2
                  -2*s*d*ca*κ^2*k^2*D+2*s*d*ca^2*κ*k^2*X-s*d^3*κ^2*D-2*s*d*k^4*X-2*s*d*ca^2*k^2
                    -2*s*d*κ*k^2+2*s*d*k^2*X) * h1 +
      (-2*s*c^2*d*ca^4*κ^4+s*d*ca^6*κ^3*D+s*d*ca^6*κ^2*D*X+2*s*d*ca^6*κ^2*D+4*s*c^2*d*ca^4*κ^2
        +2*s*c^2*d*ca^2*κ^4-s*d*ca^4*κ^3*D-s*d*ca^4*κ^2*D*X+4*s*d*ca^6*κ-s*d*ca^5*κ*D
          -2*s*d*ca^4*κ^2*D+4*s*d*ca^6*X-2*s*c^2*d*ca^4+8*s*d*ca^6+2*s*d*ca^5*κ-4*s*c^2*d*ca^2*κ^2
            +2*s*d*ca^4*κ^2-s*d*ca^5*D-2*s*d*ca^3*κ^2*D-s*d*ca^2*κ^3*D+s*d*ca^3*κ*D^2
              -s*d*ca^2*κ^2*D^2+6*s*d*ca^5*X-s*d*ca^2*κ^2*D*X-s*d*ca^2*κ*D^2*X+8*s*d*ca^5
                -2*s*d*ca^4*κ-18*s*d*ca^2*κ^3-8*s*d*ca^2*κ*k^2-s*d*ca^3*κ*D+s*d*ca^2*κ^2*D
                  +s*d*ca^3*D^2-s*d*ca^2*κ*D^2+4*s*d*ca^4*X-18*s*d*ca^2*κ^2*X-8*s*d*ca^2*k^2*X
                    +3*s*d*ca^2*κ*D*X+2*s*c^2*d*ca^2-10*s*d*ca^3*κ-12*s*d*ca^2*κ^2-16*s*d*ca^2*k^2
                      -s*d*ca^3*D+3*s*d*ca^2*κ*D+2*s*d*ca*κ^2*D+s*d*κ^3*D+s*d*ca^2*D^2
                        -s*d*ca*κ*D^2+s*d*κ^2*D^2+4*s*d*ca^3*X+26*s*d*ca^2*κ*X+s*d*κ^2*D*X
                          +s*d*κ*D^2*X-6*s*d*ca^3+24*s*d*ca^2*κ+18*s*d*κ^3+8*s*d*κ*k^2
                            -3*s*d*ca^2*D+2*s*d*ca*κ*D-s*d*κ^2*D-s*d*ca*D^2+s*d*κ*D^2-2*s*d*ca^2*X
                              +18*s*d*κ^2*X+8*s*d*k^2*X-3*s*d*κ*D*X-28*s*d*ca^2+8*s*d*ca*κ
                                +10*s*d*κ^2+16*s*d*k^2+2*s*d*ca*D-3*s*d*κ*D-s*d*D^2-10*s*d*ca*X
                                  -26*s*d*κ*X-2*s*d*ca-24*s*d*κ+3*s*d*D-8*s*d*X+20*s*d) * h2 +
      (-2*s^3*d^3*ca^4*κ^3*k^2*X-2*s*c^2*d^3*ca^4*κ^3*k^2*X-s^3*d^3*ca^2*κ^3*k^2*D*X
        -s*c^2*d^3*ca^2*κ^3*k^2*D*X-2*s*d^3*sa^2*ca^3*k^4*X^2-1/2*s*d*sa^2*ca^3*k^4*D^2*X^2
          +2*s^3*c^2*d*ca^2*κ^4*k^2-s^3*d*ca^4*κ^3*k^2*D+2*s^3*d^3*ca^4*κ*k^2*X
            +2*s*c^2*d^3*ca^4*κ*k^2*X+2*s^3*d*ca^4*κ^3*k^2*X+2*s*c^2*d*ca^4*κ^3*k^2*X
              +4*s*d^3*ca^4*κ^3*k^2*X-3*s*d^3*sa^2*ca^3*k^4*X+2*s*d^3*sa^2*ca^2*κ*k^4*X
                +s*d*sa^2*ca^3*κ^2*k^4*X-s*d^3*ca^4*κ^4*D*X-s^3*d*ca^4*κ^2*k^2*D*X
                  -s*d*sa^2*ca^2*κ^2*k^4*D*X-s*d*sa^2*ca^3*k^4*D^2*X-3*s*d^3*sa^2*ca^2*k^4*X^2
                    +1/2*s*d*sa^2*ca^3*k^4*D*X^2-1/2*s*d*sa^2*ca^2*k^4*D^2*X^2
                      +2*s*d^3*sa^2*ca^3*k^4-2*s^3*d*ca^4*κ^2*k^2*D-2*s*d^3*sa^2*ca^3*κ*k^2*X
                        -4*s*d^3*ca^4*κ^2*k^2*X-5*s*d^3*sa^2*ca^2*k^4*X+2*s*d^3*sa^2*ca*κ*k^4*X
                          -2*s*d*sa^2*ca^3*κ*k^4*X+s*d*sa^2*ca^2*κ^2*k^4*X-s*d^3*sa^2*ca^3*k^2*D*X
                            -s*d^3*sa^2*ca^2*κ*k^2*D*X+s^3*d^3*κ^3*k^2*D*X+s*c^2*d^3*κ^3*k^2*D*X
                              +s*d^3*ca^2*κ^3*k^2*D*X+s*d*sa^2*ca^3*k^4*D*X
                                -s*d*sa^2*ca*κ^2*k^4*D*X+1/2*s*d^3*sa^2*ca*κ*k^2*D^2*X
                                  -s*d*ca^4*κ^2*k^2*D^2*X-s*d*sa^2*ca^2*k^4*D^2*X
                                    +2*s*d^3*ca^3*κ^2*k^2*X^2-4*s*d^3*sa^2*ca*k^4*X^2
                                      +2*s*d*sa^2*ca^3*k^4*X^2+1/2*s*d*sa^2*ca^2*k^4*D*X^2
                                        +1/2*s*d*sa^2*ca^3*k^2*D^2*X^2
                                          +1/2*s*d*ca^3*κ^2*k^2*D^2*X^2
                                            -1/2*s*d*sa^2*ca*k^4*D^2*X^2-2*s*d^3*sa^2*ca^3*κ*k^2
                                              -2*s^3*c^2*d*ca^2*κ^2*k^2+2*s*c^4*d*ca^2*κ^2*k^2
                                                -2*s*d^3*ca^4*κ^2*k^2-1/2*s*d^3*sa^2*ca^3*k^2*D
                                                  -s*d^3*sa^2*ca^2*κ*k^2*D
                                                    +1/2*s*d^3*sa^2*ca*κ*k^2*D^2
                                                      -2*s*d^3*sa^2*ca^3*k^2*X
                                                        -2*s^3*d^3*ca^2*κ*k^2*X
                                                          -2*s*c^2*d^3*ca^2*κ*k^2*X
                                                            -5*s*d^3*sa^2*ca^2*κ*k^2*X
                                                              -2*s^3*d*ca^4*κ*k^2*X
                                                                -2*s*c^2*d*ca^4*κ*k^2*X
                                                                  -4*s*d^3*ca^4*κ*k^2*X
                                                                    -7*s*d^3*ca^3*κ^2*k^2*X
                                                                      +2*s^3*d^3*κ^3*k^2*X
                                                                        +2*s*c^2*d^3*κ^3*k^2*X
                                                                          +2*s*d^3*ca^2*κ^3*k^2*X
                                                                            -4*s*d*ca^4*κ^3*k^2*X
                                                                              +s*d*ca^3*κ^4*k^2*X
                                                                                -7*s*d^3*sa^2*ca*k^4*X+2*s*d*sa^2*ca^3*k^4*X+2*s*d^3*sa^2*κ*k^4*X-3*s*d*sa^2*ca^2*κ*k^4*X+s*d*ca^4*κ^4*D*X+1/2*s*d^3*sa^2*ca^2*k^2*D*X-3/2*s*d^3*sa^2*ca*κ*k^2*D*X+s*d*ca^4*κ^2*k^2*D*X-s*d*ca^2*κ^4*k^2*D*X+s*d*sa^2*ca^2*k^4*D*X+s*d*sa^2*ca*κ*k^4*D*X+s*d*sa^2*ca^3*k^2*D^2*X+1/2*s*d^3*sa^2*κ*k^2*D^2*X-1/2*s*d*sa^2*ca^2*κ*k^2*D^2*X-s*d*ca^3*κ^2*k^2*D^2*X-s*d*sa^2*ca*k^4*D^2*X+3*s*d^3*ca^2*κ^2*k^2*X^2-5*s*d^3*sa^2*k^4*X^2+3*s*d*sa^2*ca^2*k^4*X^2+3/2*s*d*sa^2*ca^3*k^2*D*X^2-1/2*s*d*ca^3*κ^2*k^2*D*X^2-1/2*s*d*sa^2*ca*k^4*D*X^2+1/2*s*d*sa^2*ca^2*k^2*D^2*X^2+1/2*s*d*ca^2*κ^2*k^2*D^2*X^2-1/2*s*d*sa^2*k^4*D^2*X^2-5*s*d^3*sa^2*ca^2*κ*k^2-4*s^3*d*ca^4*κ*k^2+2*s*d^3*ca^3*κ^2*k^2+s^3*d^3*κ^4*D+1/2*s*d^3*sa^2*ca^2*k^2*D-3/2*s*d^3*sa^2*ca*κ*k^2*D+s^3*d*ca^3*κ*k^2*D-1/2*s*d^3*sa^2*ca*k^2*D^2+1/2*s*d*sa^2*ca^3*k^2*D^2+1/2*s*d^3*sa^2*κ*k^2*D^2-1/2*s*d*sa^2*ca^2*κ*k^2*D^2+s*d*ca^4*κ*k^2*D^2-4*s*d^3*ca^4*κ^2*X+2*s*d^3*ca^3*κ^3*X-s*d^3*sa^2*ca^2*k^2*X-4*s^3*d*ca^4*k^2*X+4*s*d^3*ca^4*k^2*X-11*s*d^3*sa^2*ca*κ*k^2*X-4*s*d^3*ca^3*κ*k^2*X+2*s*d*sa^2*ca^3*κ*k^2*X-9*s*d^3*ca^2*κ^2*k^2*X+4*s*d*ca^4*κ^2*k^2*X+2*s*d^3*ca*κ^3*k^2*X-4*s*d*ca^3*κ^3*k^2*X+s*d*ca^2*κ^4*k^2*X-9*s*d^3*sa^2*k^4*X+5*s*d*sa^2*ca^2*k^4*X-4*s*d*sa^2*ca*κ*k^4*X+s*d^3*ca^3*κ^2*D*X+s*d^3*ca^2*κ^3*D*X+s*d^3*sa^2*ca*k^2*D*X+4*s*d*sa^2*ca^3*k^2*D*X-1/2*s*d^3*sa^2*κ*k^2*D*X+s^3*d*ca^2*κ*k^2*D*X+s*c^2*d*ca^2*κ*k^2*D*X+3/2*s*d*sa^2*ca^2*κ*k^2*D*X+s*d*ca^3*κ^2*k^2*D*X-s*d^3*κ^3*k^2*D*X+2*s*d*ca^2*κ^3*k^2*D*X-s*d*ca*κ^4*k^2*D*X+4*s*d*sa^2*κ*k^4*D*X-1/2*s*d^3*ca*κ^3*D^2*X-1/2*s*d^3*sa^2*k^2*D^2*X+1/2*s*d*sa^2*ca^2*k^2*D^2*X+s*d*ca^4*k^2*D^2*X-s*d*sa^2*ca*κ*k^2*D^2*X-s*d*ca^2*κ^2*k^2*D^2*X-s*d*sa^2*k^4*D^2*X-2*s*d*sa^2*ca^3*k^2*X^2+4*s*d^3*ca*κ^2*k^2*X^2-2*s*d*ca^3*κ^2*k^2*X^2+6*s*d*sa^2*ca*k^4*X^2+5/2*s*d*sa^2*ca^2*k^2*D*X^2-1/2*s*d*ca^2*κ^2*k^2*D*X^2-7/2*s*d*sa^2*k^4*D*X^2-1/2*s*d*ca^3*κ^2*D^2*X^2+1/2*s*d*sa^2*ca*k^2*D^2*X^2+1/2*s*d*ca*κ^2*k^2*D^2*X^2-2*s*d^3*ca^3*κ^3-2*s*c^2*d^3*κ^4-2*s*c^4*d*ca^2*k^2+2*s*d^3*sa^2*ca^2*k^2-8*s^3*d*ca^4*k^2+8*s*d^3*ca^4*k^2-11*s*d^3*sa^2*ca*κ*k^2-2*s^3*d*ca^3*κ*k^2+2*s*d*sa^2*ca^3*κ*k^2+2*s*d*ca^4*κ^2*k^2-1/2*s*d^3*ca^3*κ^2*D-s*d^3*ca^2*κ^3*D+2*s*d^3*sa^2*ca*k^2*D+s^3*d*ca^3*k^2*D+2*s*d*sa^2*ca^3*k^2*D-1/2*s*d^3*sa^2*κ*k^2*D+3/2*s*d*sa^2*ca^2*κ*k^2*D-s*d*ca^4*κ*k^2*D-2*s*c^2*d*ca*κ^2*k^2*D+s^3*d*κ^3*k^2*D+1/2*s*d^3*ca*κ^3*D^2-s*d^3*sa^2*k^2*D^2+2*s*d*ca^4*k^2*D^2-s^3*d*ca*κ*k^2*D^2-s*d*sa^2*ca*κ*k^2*D^2+s^3*d*κ^2*k^2*D^2-4*s*d^3*ca^3*κ^2*X+5*s*d^3*ca^2*κ^3*X-6*s^3*d*ca^3*k^2*X+6*s*d^3*ca^3*k^2*X-2*s*d*sa^2*ca^3*k^2*X-16*s*d^3*sa^2*κ*k^2*X+2*s^3*d*ca^2*κ*k^2*X+2*s*c^2*d*ca^2*κ*k^2*X-8*s*d^3*ca^2*κ*k^2*X+5*s*d*sa^2*ca^2*κ*k^2*X+4*s*d*ca^4*κ*k^2*X-11*s*d^3*ca*κ^2*k^2*X+6*s*d*ca^3*κ^2*k^2*X-2*s*d^3*κ^3*k^2*X-5*s*d*ca^2*κ^3*k^2*X+10*s*d*sa^2*ca*k^4*X-4*s*d*sa^2*κ*k^4*X-1/2*s*d^3*ca^2*κ^2*D*X+3/2*s*d^3*ca*κ^3*D*X+s*d^3*κ^4*D*X+s*d^3*sa^2*k^2*D*X+5*s*d*sa^2*ca^2*k^2*D*X-s*d*ca^4*k^2*D*X+3/2*s*d*sa^2*ca*κ*k^2*D*X+s*d*ca^3*κ*k^2*D*X+s^3*d*κ^2*k^2*D*X+s*d*ca^2*κ^2*k^2*D*X+5*s*d*ca*κ^3*k^2*D*X-5*s*d*sa^2*k^4*D*X+1/2*s*d^3*κ^3*D^2*X+1/2*s*d*ca^2*κ^3*D^2*X+1/2*s*d*sa^2*ca*k^2*D^2*X+s*d*ca^3*k^2*D^2*X+s^3*d*κ*k^2*D^2*X-3/2*s*d*sa^2*κ*k^2*D^2*X-s*d*ca^2*κ*k^2*D^2*X-s*d*ca*κ^2*k^2*D^2*X+1/2*s*d*sa^2*k^2*D^3*X-3*s*d*sa^2*ca^2*k^2*X^2+5*s*d^3*κ^2*k^2*X^2-3*s*d*ca^2*κ^2*k^2*X^2+8*s*d*sa^2*k^4*X^2-3/2*s*d*ca^3*κ^2*D*X^2+9/2*s*d*sa^2*ca*k^2*D*X^2+1/2*s*d*ca*κ^2*k^2*D*X^2-1/2*s*d*ca^2*κ^2*D^2*X^2+1/2*s*d*sa^2*k^2*D^2*X^2+1/2*s*d*κ^2*k^2*D^2*X^2-5*s*d^3*ca^2*κ^3+9*s*d^3*sa^2*ca*k^2-8*s^3*d*ca^3*k^2+10*s*d^3*ca^3*k^2-2*s*d*sa^2*ca^3*k^2-16*s*d^3*sa^2*κ*k^2-2*s^3*d*ca^2*κ*k^2+5*s*d*sa^2*ca^2*κ*k^2+18*s^3*d*κ^3*k^2+8*s^3*d*κ*k^4-s^3*d^3*κ^2*D+1/2*s*d^3*ca^2*κ^2*D-3/2*s*d^3*ca*κ^3*D+5/2*s*d^3*sa^2*k^2*D+5/2*s*d*sa^2*ca^2*k^2*D-2*s*d*ca^4*k^2*D+2*s^3*d*ca*κ*k^2*D+3/2*s*d*sa^2*ca*κ*k^2*D-s^3*d*κ^2*k^2*D-1/2*s*d^3*ca*κ^2*D^2+1/2*s*d*ca^3*κ^2*D^2+1/2*s*d^3*κ^3*D^2-1/2*s*d*ca^2*κ^3*D^2-s^3*d*ca*k^2*D^2+1/2*s*d*sa^2*ca*k^2*D^2+s*d*ca^3*k^2*D^2+s^3*d*κ*k^2*D^2-3/2*s*d*sa^2*κ*k^2*D^2+1/2*s*d*sa^2*k^2*D^3-7*s*d^3*ca^2*κ^2*X+4*s*d*ca^4*κ^2*X+11*s*d^3*ca*κ^3*X-2*s*d*ca^3*κ^3*X+18*s*d^3*κ^4*X+4*s*d^3*sa^2*k^2*X-8*s^3*d*ca^2*k^2*X+8*s*d^3*ca^2*k^2*X-5*s*d*sa^2*ca^2*k^2*X-4*s*d*ca^4*k^2*X-12*s*d^3*ca*κ*k^2*X+13*s*d*sa^2*ca*κ*k^2*X+10*s*d*ca^3*κ*k^2*X+18*s^3*d*κ^2*k^2*X-s*d^3*κ^2*k^2*X+11*s*d*ca^2*κ^2*k^2*X-4*s*d*ca*κ^3*k^2*X+6*s^3*d*k^4*X-2*s*c^2*d*k^4*X+14*s*d*sa^2*k^4*X-s*d^3*ca*κ^2*D*X-s*d*ca^3*κ^2*D*X-5/2*s*d^3*κ^3*D*X-3/2*s*d*ca^2*κ^3*D*X+7*s*d*sa^2*ca*k^2*D*X-s*d*ca^3*k^2*D*X-3*s^3*d*κ*k^2*D*X-5*s*d*sa^2*κ*k^2*D*X-2*s*d*ca^2*κ*k^2*D*X-6*s*d*ca*κ^2*k^2*D*X+4*s*d*κ^3*k^2*D*X+1/2*s*d^3*κ^2*D^2*X+1/2*s*d*ca^2*κ^2*D^2*X+s*d*ca*κ^3*D^2*X+s*d*ca^2*k^2*D^2*X-s*d*ca*κ*k^2*D^2*X+2*s*d*ca^3*κ^2*X^2-6*s*d*sa^2*ca*k^2*X^2-6*s*d*ca*κ^2*k^2*X^2-5/2*s*d*ca^2*κ^2*D*X^2+17/2*s*d*sa^2*k^2*D*X^2+7/2*s*d*κ^2*k^2*D*X^2-1/2*s*d*ca*κ^2*D^2*X^2+2*s*c^2*d^3*κ^2+2*s*d^3*ca^2*κ^2-11*s*d^3*ca*κ^3+2*s*d*ca^3*κ^3+20*s*d^3*sa^2*k^2-10*s^3*d*ca^2*k^2+18*s*d^3*ca^2*k^2-5*s*d*sa^2*ca^2*k^2-8*s*d*ca^4*k^2+8*s^3*d*ca*κ*k^2+13*s*d*sa^2*ca*κ*k^2+2*s*d*ca^3*κ*k^2+10*s^3*d*κ^2*k^2+2*s*d^3*κ^2*k^2+16*s^3*d*k^4+2*s*d^3*ca*κ^2*D+2*s*d*ca^3*κ^2*D-1/2*s*d^3*κ^3*D+3/2*s*d*ca^2*κ^3*D+2*s^3*d*ca*k^2*D+3/2*s*d*sa^2*ca*k^2*D-2*s*d*ca^3*k^2*D-3*s^3*d*κ*k^2*D-5*s*d*sa^2*κ*k^2*D-2*s*d*ca^2*κ*k^2*D-2*s*d*ca*κ^2*k^2*D-s*d^3*κ^2*D^2-s*d*ca*κ^3*D^2-s^3*d*k^2*D^2+2*s*d*ca^2*k^2*D^2-10*s*d^3*ca*κ^2*X+4*s*d*ca^3*κ^2*X-10*s*d^3*κ^3*X-5*s*d*ca^2*κ^3*X-10*s^3*d*ca*k^2*X+10*s*d^3*ca*k^2*X-10*s*d*sa^2*ca*k^2*X-6*s*d*ca^3*k^2*X-26*s^3*d*κ*k^2*X-12*s*d^3*κ*k^2*X+21*s*d*sa^2*κ*k^2*X+12*s*d*ca^2*κ*k^2*X+18*s*d*ca*κ^2*k^2*X-4*s*d*κ^3*k^2*X-s*d^3*κ^2*D*X-3/2*s*d*ca*κ^3*D*X-s*d*κ^4*D*X+10*s*d*sa^2*k^2*D*X+s*d*ca^2*k^2*D*X-7*s*d*ca*κ*k^2*D*X+4*s*d*κ^2*k^2*D*X+1/2*s*d*ca*κ^2*D^2*X+1/2*s*d*κ^3*D^2*X+s*d*ca*k^2*D^2*X-s*d*κ*k^2*D^2*X-1/2*s*d*κ^2*D^3*X+3*s*d*ca^2*κ^2*X^2-8*s*d*sa^2*k^2*X^2-8*s*d*κ^2*k^2*X^2-9/2*s*d*ca*κ^2*D*X^2-1/2*s*d*κ^2*D^2*X^2+9*s*d^3*ca*κ^2-2*s*d*ca^3*κ^2-16*s*d^3*κ^3+5*s*d*ca^2*κ^3-2*s^3*d*ca*k^2+22*s*d^3*ca*k^2-13*s*d*sa^2*ca*k^2-16*s*d*ca^3*k^2-26*s^3*d*κ*k^2+21*s*d*sa^2*κ*k^2+2*s*d*ca^2*κ*k^2+5/2*s*d^3*κ^2*D+5/2*s*d*ca^2*κ^2*D+3/2*s*d*ca*κ^3*D+3*s^3*d*k^2*D+2*s*d*ca^2*k^2*D-2*s*d*ca*κ*k^2*D+1/2*s*d*ca*κ^2*D^2-3/2*s*d*κ^3*D^2+2*s*d*ca*k^2*D^2-s*d*κ*k^2*D^2+1/2*s*d*κ^2*D^3-10*s*d^3*κ^2*X+7*s*d*ca^2*κ^2*X-13*s*d*ca*κ^3*X-18*s*d*κ^4*X-6*s^3*d*k^2*X+8*s*d^3*k^2*X-14*s*d*sa^2*k^2*X-12*s*d*ca^2*k^2*X+20*s*d*ca*κ*k^2*X-4*s*d*κ^2*k^2*X+2*s*d*k^4*X+2*s*d*ca*κ^2*D*X+8*s*d*κ^3*D*X+7*s*d*ca*k^2*D*X-15*s*d*κ*k^2*D*X+s*d*κ^2*D^2*X+6*s*d*ca*κ^2*X^2-17/2*s*d*κ^2*D*X^2+20*s*d^3*κ^2-5*s*d*ca^2*κ^2+13*s*d*ca*κ^3+20*s^3*d*k^2+18*s*d^3*k^2-22*s*d*sa^2*k^2-26*s*d*ca^2*k^2+3/2*s*d*ca*κ^2*D-5*s*d*κ^3*D+16*s*d*ca*k^2*D-17*s*d*κ*k^2*D+8*s*d*ca*κ^2*X+5*s*d*κ^3*X-16*s*d*ca*k^2*X+24*s*d*κ*k^2*X+7*s*d*κ^2*D*X-6*s*d*k^2*D*X+8*s*d*κ^2*X^2-13*s*d*ca*κ^2+21*s*d*κ^3-36*s*d*ca*k^2+18*s*d*κ*k^2-8*s*d*k^2*D+4*s*d*κ^2*X-2*s*d*k^2*X-22*s*d*κ^2-8*s*d*k^2) * ha1 +
      (2*s*c^2*d^3*ca^4*κ^3*X+s*c^2*d^3*ca^2*κ^3*D*X+2*s*d^3*ca^5*k^2*X^2+1/2*s*d*ca^5*k^2*D^2*X^2
        -2*s*c^2*d^3*ca^4*κ*X-2*s*c^2*d*ca^4*κ^3*X-2*s*d^3*ca^4*κ^3*X+3*s*d^3*ca^5*k^2*X
          -2*s*d^3*ca^4*κ*k^2*X-s*d*ca^5*κ^2*k^2*X+s*d*ca^4*κ^2*k^2*D*X+s*d*ca^5*k^2*D^2*X
            +3*s*d^3*ca^4*k^2*X^2-1/2*s*d*ca^5*k^2*D*X^2+1/2*s*d*ca^4*k^2*D^2*X^2-2*s*d^3*ca^5*k^2
              +2*s*d^3*ca^5*κ*X+5*s*d^3*ca^4*k^2*X-2*s*d^3*ca^3*κ*k^2*X+2*s*d*ca^5*κ*k^2*X
                -s*d*ca^4*κ^2*k^2*X+s*d^3*ca^5*D*X+s*d^3*ca^4*κ*D*X-s*c^2*d^3*κ^3*D*X
                  -s*d^3*ca^2*κ^3*D*X-s*d*ca^5*k^2*D*X+s*d*ca^3*κ^2*k^2*D*X-1/2*s*d^3*ca^3*κ*D^2*X
                    +s*d*ca^4*k^2*D^2*X+2*s*d^3*ca^3*k^2*X^2-2*s*d*ca^5*k^2*X^2
                      -1/2*s*d*ca^4*k^2*D*X^2-1/2*s*d*ca^5*D^2*X^2+2*s*d^3*ca^5*κ+2*s*d^3*ca^4*κ^2
                        +1/2*s*d^3*ca^5*D+s*d^3*ca^4*κ*D-1/2*s*d^3*ca^3*κ*D^2+2*s*d^3*ca^5*X
                          +2*s*c^2*d^3*ca^2*κ*X+2*s*c^2*d*ca^4*κ*X+9*s*d^3*ca^4*κ*X
                            -2*s*c^2*d^3*κ^3*X+2*s*d*ca^4*κ^3*X+4*s*d^3*ca^3*k^2*X
                              -2*s*d*ca^5*k^2*X+3*s*d*ca^4*κ*k^2*X+s*d*ca^3*κ^2*k^2*X
                                -1/2*s*d^3*ca^4*D*X+3/2*s*d^3*ca^3*κ*D*X-s*d*ca^4*k^2*D*X
                                  -s*d*ca^3*κ*k^2*D*X-s*d*ca^2*κ^2*k^2*D*X-s*d*ca^5*D^2*X
                                    -1/2*s*d^3*ca^2*κ*D^2*X+1/2*s*d*ca^4*κ*D^2*X
                                      +2*s*d^3*ca^2*k^2*X^2-3*s*d*ca^4*k^2*X^2-3/2*s*d*ca^5*D*X^2
                                        +s*d*ca^3*k^2*D*X^2-1/2*s*d*ca^4*D^2*X^2+5*s*d^3*ca^4*κ
                                          +2*s*d^3*ca^3*k^2-1/2*s*d^3*ca^4*D+3/2*s*d^3*ca^3*κ*D
                                            +1/2*s*d^3*ca^3*D^2-1/2*s*d*ca^5*D^2
                                              -1/2*s*d^3*ca^2*κ*D^2-1/2*s*d*ca^4*κ*D^2
                                                -3*s*d^3*ca^4*X+13*s*d^3*ca^3*κ*X-2*s*d*ca^5*κ*X
                                                  +4*s*d^3*ca^2*k^2*X-5*s*d*ca^4*k^2*X
                                                    +2*s*d^3*ca*κ*k^2*X+2*s*d*ca^3*κ*k^2*X
                                                      +s*d*ca^2*κ^2*k^2*X-2*s*d^3*ca^3*D*X
                                                        -4*s*d*ca^5*D*X-s*c^2*d*ca^2*κ*D*X
                                                          -1/2*s*d^3*ca^2*κ*D*X-3/2*s*d*ca^4*κ*D*X
                                                            +s*d^3*κ^3*D*X+s*d*ca^3*k^2*D*X
                                                              -4*s*d*ca^2*κ*k^2*D*X
                                                                -s*d*ca*κ^2*k^2*D*X
                                                                  +1/2*s*d^3*ca^2*D^2*X
                                                                    -3/2*s*d*ca^4*D^2*X
                                                                      +1/2*s*d^3*ca*κ*D^2*X
                                                                        +s*d*ca^3*κ*D^2*X
                                                                          +2*s*d*ca^5*X^2
                                                                            -4*s*d^3*ca*k^2*X^2
                                                                              -4*s*d*ca^3*k^2*X^2
                                                                                -5/2*s*d*ca^4*D*X^2+4*s*d*ca^2*k^2*D*X^2-1/2*s*d*ca*k^2*D^2*X^2-10*s*d^3*ca^4+9*s*d^3*ca^3*κ-2*s*d*ca^5*κ-2*s*d*ca^4*κ^2-5/2*s*d^3*ca^3*D-2*s*d*ca^5*D-1/2*s*d^3*ca^2*κ*D-1/2*s*d*ca^4*κ*D+s*d^3*ca^2*D^2-2*s*d*ca^4*D^2+1/2*s*d^3*ca*κ*D^2+s*d*ca^3*κ*D^2-8*s*d^3*ca^3*X+2*s*d*ca^5*X-2*s*c^2*d*ca^2*κ*X+19*s*d^3*ca^2*κ*X-9*s*d*ca^4*κ*X+2*s*d*ca^3*κ^2*X+2*s*d^3*κ^3*X-7*s*d^3*ca*k^2*X-8*s*d*ca^3*k^2*X+2*s*d^3*κ*k^2*X+s*d*ca^2*κ*k^2*X-1/2*s*d^3*ca^2*D*X-4*s*d*ca^4*D*X-3/2*s*d^3*ca*κ*D*X-5/2*s*d*ca^3*κ*D*X-2*s*d*ca^2*κ^2*D*X+6*s*d*ca^2*k^2*D*X+s*d*ca*κ*k^2*D*X-1/2*s*d*ca^3*D^2*X+1/2*s*d^3*κ*D^2*X+2*s*d*ca^2*κ*D^2*X-s*d*ca*k^2*D^2*X-1/2*s*d*ca^2*D^3*X+3*s*d*ca^4*X^2-5*s*d^3*k^2*X^2-5*s*d*ca^2*k^2*X^2-3*s*d*ca^3*D*X^2-1/2*s*d*ca*k^2*D*X^2-1/2*s*d*k^2*D^2*X^2-19*s*d^3*ca^3+2*s*d*ca^5+11*s*d^3*ca^2*κ-5*s*d*ca^4*κ-2*s*d^3*ca^2*D-1/2*s*d*ca^4*D-3/2*s*d^3*ca*κ*D-3/2*s*d*ca^3*κ*D-1/2*s*d^3*ca*D^2-s*d*ca^3*D^2+1/2*s*d^3*κ*D^2+s*d*ca^2*κ*D^2-1/2*s*d*ca^2*D^3-13*s*d^3*ca^2*X+9*s*d*ca^4*X+s*d^3*ca*κ*X-21*s*d*ca^3*κ*X+2*s*d*ca^2*κ^2*X+2*s*c^2*d*k^2*X-9*s*d^3*k^2*X-9*s*d*ca^2*k^2*X-4*s*d*ca*κ*k^2*X+s*d^3*ca*D*X-2*s*d*ca^3*D*X-1/2*s*d^3*κ*D*X+17/2*s*d*ca^2*κ*D*X-2*s*d*ca*κ^2*D*X+4*s*d*κ*k^2*D*X-1/2*s*d^3*D^2*X-1/2*s*d*ca^2*D^2*X-s*d*k^2*D^2*X+4*s*d*ca^3*X^2+6*s*d*ca*k^2*X^2-6*s*d*ca^2*D*X^2-7/2*s*d*k^2*D*X^2+1/2*s*d*ca*D^2*X^2-36*s*d^3*ca^2+13*s*d*ca^4-11*s*d^3*ca*κ-13*s*d*ca^3*κ-2*s*d^3*κ^2+2*s*d^3*ca*D+5/2*s*d*ca^3*D-1/2*s*d^3*κ*D+17/2*s*d*ca^2*κ*D+2*s*d*ca*κ^2*D-s*d^3*D^2-2*s*d*ca^2*D^2-s*d*ca*κ*D^2-10*s*d^3*ca*X+14*s*d*ca^3*X-4*s*d^3*κ*X-28*s*d*ca^2*κ*X+10*s*d*ca*k^2*X-4*s*d*κ*k^2*X+s*d^3*D*X-6*s*d*ca^2*D*X+17/2*s*d*ca*κ*D*X-5*s*d*k^2*D*X-1/2*s*d*ca*D^2*X-1/2*s*d*κ*D^2*X+1/2*s*d*D^3*X+5*s*d*ca^2*X^2+8*s*d*k^2*X^2+9/2*s*d*ca*D*X^2+1/2*s*d*D^2*X^2-13*s*d^3*ca+27*s*d*ca^3-16*s*d^3*κ-18*s*d*ca^2*κ+5/2*s*d^3*D+1/2*s*d*ca^2*D+7/2*s*d*ca*κ*D-3/2*s*d*ca*D^2-1/2*s*d*κ*D^2+1/2*s*d*D^3-4*s*d^3*X+21*s*d*ca^2*X-7*s*d*ca*κ*X+12*s*d*k^2*X+10*s*d*κ*D*X-6*s*d*ca*X^2+17/2*s*d*D*X^2+2*s*d^3+43*s*d*ca^2+13*s*d*ca*κ-29/2*s*d*ca*D+12*s*d*κ*D+6*s*d*ca*X-3*s*d*κ*X+16*s*d*D*X-8*s*d*X^2+23*s*d*ca+3*s*d*κ+8*s*d*D-12*s*d*X-14*s*d) * ha2 +
      (-2*s*d^3*ca^3*k^2*X^2-1/2*s*d*ca^3*k^2*D^2*X^2-3*s*d^3*ca^3*k^2*X+2*s*d^3*ca^2*κ*k^2*X
        +s*d*ca^3*κ^2*k^2*X-s*d*ca^2*κ^2*k^2*D*X-s*d*ca^3*k^2*D^2*X-3*s*d^3*ca^2*k^2*X^2
          +1/2*s*d*ca^3*k^2*D*X^2-1/2*s*d*ca^2*k^2*D^2*X^2+2*s*d^3*ca^3*k^2-2*s*d^3*ca^3*κ*X
            -5*s*d^3*ca^2*k^2*X+2*s*d^3*ca*κ*k^2*X-2*s*d*ca^3*κ*k^2*X+s*d*ca^2*κ^2*k^2*X
              -s*d^3*ca^3*D*X-s*d^3*ca^2*κ*D*X+s*d*ca^3*k^2*D*X-s*d*ca*κ^2*k^2*D*X
                +1/2*s*d^3*ca*κ*D^2*X-s*d*ca^2*k^2*D^2*X-4*s*d^3*ca*k^2*X^2+2*s*d*ca^3*k^2*X^2
                  +1/2*s*d*ca^2*k^2*D*X^2+1/2*s*d*ca^3*D^2*X^2-1/2*s*d*ca*k^2*D^2*X^2
                    -2*s*d^3*ca^3*κ-1/2*s*d^3*ca^3*D-s*d^3*ca^2*κ*D+1/2*s*d^3*ca*κ*D^2
                      -2*s*d^3*ca^3*X-5*s*d^3*ca^2*κ*X-7*s*d^3*ca*k^2*X+2*s*d*ca^3*k^2*X
                        +2*s*d^3*κ*k^2*X-3*s*d*ca^2*κ*k^2*X+1/2*s*d^3*ca^2*D*X-3/2*s*d^3*ca*κ*D*X
                          +s*d*ca^2*k^2*D*X+s*d*ca*κ*k^2*D*X+s*d*ca^3*D^2*X+1/2*s*d^3*κ*D^2*X
                            -1/2*s*d*ca^2*κ*D^2*X-s*d*ca*k^2*D^2*X-5*s*d^3*k^2*X^2
                              +3*s*d*ca^2*k^2*X^2+3/2*s*d*ca^3*D*X^2-1/2*s*d*ca*k^2*D*X^2
                                +1/2*s*d*ca^2*D^2*X^2-1/2*s*d*k^2*D^2*X^2-5*s*d^3*ca^2*κ
                                  +1/2*s*d^3*ca^2*D-3/2*s*d^3*ca*κ*D-1/2*s*d^3*ca*D^2
                                    +1/2*s*d*ca^3*D^2+1/2*s*d^3*κ*D^2-1/2*s*d*ca^2*κ*D^2
                                      -s*d^3*ca^2*X-11*s*d^3*ca*κ*X+2*s*d*ca^3*κ*X-9*s*d^3*k^2*X
                                        +5*s*d*ca^2*k^2*X-4*s*d*ca*κ*k^2*X+s*d^3*ca*D*X
                                          +4*s*d*ca^3*D*X-1/2*s*d^3*κ*D*X+3/2*s*d*ca^2*κ*D*X
                                            +4*s*d*κ*k^2*D*X-1/2*s*d^3*D^2*X+1/2*s*d*ca^2*D^2*X
                                              -s*d*ca*κ*D^2*X-s*d*k^2*D^2*X-2*s*d*ca^3*X^2
                                                +6*s*d*ca*k^2*X^2+5/2*s*d*ca^2*D*X^2
                                                  -7/2*s*d*k^2*D*X^2+1/2*s*d*ca*D^2*X^2
                                                    +2*s*d^3*ca^2-11*s*d^3*ca*κ+2*s*d*ca^3*κ
                                                      +2*s*d^3*ca*D+2*s*d*ca^3*D-1/2*s*d^3*κ*D
                                                        +3/2*s*d*ca^2*κ*D-s*d^3*D^2-s*d*ca*κ*D^2
                                                          -2*s*d*ca^3*X-16*s*d^3*κ*X
                                                            +5*s*d*ca^2*κ*X+10*s*d*ca*k^2*X
                                                              -4*s*d*κ*k^2*X+s*d^3*D*X
                                                                +5*s*d*ca^2*D*X+3/2*s*d*ca*κ*D*X
                                                                  -5*s*d*k^2*D*X+1/2*s*d*ca*D^2*X
                                                                    -3/2*s*d*κ*D^2*X+1/2*s*d*D^3*X
                                                                      -3*s*d*ca^2*X^2
                                                                        +8*s*d*k^2*X^2
                                                                          +9/2*s*d*ca*D*X^2
                                                                            +1/2*s*d*D^2*X^2
                                                                              +9*s*d^3*ca
                                                                                -2*s*d*ca^3
                                                                                  -16*s*d^3*κ
                                                                                    +5*s*d*ca^2*κ
                                                                                      +5/2*s*d^3*D
                                                                                        +5/2*s*d*ca^2*D+3/2*s*d*ca*κ*D+1/2*s*d*ca*D^2-3/2*s*d*κ*D^2+1/2*s*d*D^3+4*s*d^3*X-5*s*d*ca^2*X+13*s*d*ca*κ*X+14*s*d*k^2*X+7*s*d*ca*D*X-5*s*d*κ*D*X-6*s*d*ca*X^2+17/2*s*d*D*X^2+20*s*d^3-5*s*d*ca^2+13*s*d*ca*κ+3/2*s*d*ca*D-5*s*d*κ*D-10*s*d*ca*X+21*s*d*κ*X+10*s*d*D*X-8*s*d*X^2-13*s*d*ca+21*s*d*κ-14*s*d*X-22*s*d) * E1 +
      (2*s*d^3*ca^4*κ*k^2*X-s*d^3*ca^4*κ^2*D*X-4*s*d^3*ca^4*k^2*X-s*d*ca^4*k^2*D^2*X
        +2*s*d^3*ca^3*k^2*X^2+1/2*s*d*ca^3*k^2*D^2*X^2-7*s*d^3*ca^3*k^2*X+2*s*d^3*ca^2*κ*k^2*X
          -2*s*d*ca^4*κ*k^2*X+s*d*ca^3*κ^2*k^2*X+s*d*ca^4*κ^2*D*X+s*d*ca^4*k^2*D*X
            -s*d*ca^2*κ^2*k^2*D*X-s*d*ca^3*k^2*D^2*X+3*s*d^3*ca^2*k^2*X^2-1/2*s*d*ca^3*k^2*D*X^2
              +1/2*s*d*ca^2*k^2*D^2*X^2+2*s*d^3*ca^3*k^2-4*s*d^3*ca^4*X+2*s*d^3*ca^3*κ*X
                -9*s*d^3*ca^2*k^2*X+4*s*d*ca^4*k^2*X+2*s*d^3*ca*κ*k^2*X-4*s*d*ca^3*κ*k^2*X
                  +s*d*ca^2*κ^2*k^2*X+s*d^3*ca^3*D*X+s*d^3*ca^2*κ*D*X+s*d*ca^3*k^2*D*X
                    +2*s*d*ca^2*κ*k^2*D*X-s*d*ca*κ^2*k^2*D*X-1/2*s*d^3*ca*κ*D^2*X
                      -s*d*ca^2*k^2*D^2*X+4*s*d^3*ca*k^2*X^2-2*s*d*ca^3*k^2*X^2
                        -1/2*s*d*ca^2*k^2*D*X^2-1/2*s*d*ca^3*D^2*X^2+1/2*s*d*ca*k^2*D^2*X^2
                          -2*s*d^3*ca^3*κ-1/2*s*d^3*ca^3*D-s*d^3*ca^2*κ*D+1/2*s*d^3*ca*κ*D^2
                            -4*s*d^3*ca^3*X+5*s*d^3*ca^2*κ*X-11*s*d^3*ca*k^2*X+8*s*d*ca^3*k^2*X
                              -5*s*d*ca^2*κ*k^2*X-1/2*s*d^3*ca^2*D*X+3/2*s*d^3*ca*κ*D*X
                                +s*d^3*κ^2*D*X-s*d*ca^2*k^2*D*X+5*s*d*ca*κ*k^2*D*X
                                  +1/2*s*d^3*κ*D^2*X+1/2*s*d*ca^2*κ*D^2*X-s*d*ca*k^2*D^2*X
                                    +5*s*d^3*k^2*X^2-3*s*d*ca^2*k^2*X^2-3/2*s*d*ca^3*D*X^2
                                      +1/2*s*d*ca*k^2*D*X^2-1/2*s*d*ca^2*D^2*X^2
                                        +1/2*s*d*k^2*D^2*X^2-5*s*d^3*ca^2*κ+1/2*s*d^3*ca^2*D
                                          -3/2*s*d^3*ca*κ*D-1/2*s*d^3*ca*D^2+1/2*s*d*ca^3*D^2
                                            +1/2*s*d^3*κ*D^2-1/2*s*d*ca^2*κ*D^2-7*s*d^3*ca^2*X
                                              +4*s*d*ca^4*X+11*s*d^3*ca*κ*X-2*s*d*ca^3*κ*X
                                                +18*s*d^3*κ^2*X-s*d^3*k^2*X+13*s*d*ca^2*k^2*X
                                                  -4*s*d*ca*κ*k^2*X-s*d^3*ca*D*X-s*d*ca^3*D*X
                                                    -5/2*s*d^3*κ*D*X-3/2*s*d*ca^2*κ*D*X
                                                      -8*s*d*ca*k^2*D*X+4*s*d*κ*k^2*D*X
                                                        +1/2*s*d^3*D^2*X+1/2*s*d*ca^2*D^2*X
                                                          +s*d*ca*κ*D^2*X+2*s*d*ca^3*X^2
                                                            -6*s*d*ca*k^2*X^2-5/2*s*d*ca^2*D*X^2
                                                              +7/2*s*d*k^2*D*X^2
                                                                -1/2*s*d*ca*D^2*X^2+2*s*d^3*ca^2
                                                                  -11*s*d^3*ca*κ+2*s*d*ca^3*κ
                                                                    +2*s*d^3*ca*D+2*s*d*ca^3*D
                                                                      -1/2*s*d^3*κ*D
                                                                        +3/2*s*d*ca^2*κ*D
                                                                          -s*d^3*D^2-s*d*ca*κ*D^2
                                                                            -10*s*d^3*ca*X
                                                                              +4*s*d*ca^3*X
                                                                                -10*s*d^3*κ*X
                                                                                  -5*s*d*ca^2*κ*X
                                                                                    +18*s*d*ca*k^2*X-4*s*d*κ*k^2*X-s*d^3*D*X-3/2*s*d*ca*κ*D*X-s*d*κ^2*D*X+4*s*d*k^2*D*X+1/2*s*d*ca*D^2*X+1/2*s*d*κ*D^2*X-1/2*s*d*D^3*X+3*s*d*ca^2*X^2-8*s*d*k^2*X^2-9/2*s*d*ca*D*X^2-1/2*s*d*D^2*X^2+9*s*d^3*ca-2*s*d*ca^3-16*s*d^3*κ+5*s*d*ca^2*κ+5/2*s*d^3*D+5/2*s*d*ca^2*D+3/2*s*d*ca*κ*D+1/2*s*d*ca*D^2-3/2*s*d*κ*D^2+1/2*s*d*D^3-10*s*d^3*X+7*s*d*ca^2*X-13*s*d*ca*κ*X-18*s*d*κ^2*X-4*s*d*k^2*X+2*s*d*ca*D*X+8*s*d*κ*D*X+s*d*D^2*X+6*s*d*ca*X^2-17/2*s*d*D*X^2+20*s*d^3-5*s*d*ca^2+13*s*d*ca*κ+3/2*s*d*ca*D-5*s*d*κ*D+8*s*d*ca*X+5*s*d*κ*X+7*s*d*D*X+8*s*d*X^2-13*s*d*ca+21*s*d*κ+4*s*d*X-22*s*d) * E2 +
      (-2*s*d^3*ca^4*κ^3*X-s*d^3*ca^2*κ^3*D*X-s*d*ca^4*κ^3*D+2*s*d^3*ca^4*κ*X+2*s*d*ca^4*κ^3*X
        -s*d*ca^4*κ^2*D*X-2*s*d*ca^4*κ^2*D+s*d^3*κ^3*D*X-2*s*d^3*ca^2*κ*X-2*s*d*ca^4*κ*X
          +2*s*d^3*κ^3*X-4*s*d*ca^4*κ+s*d*ca^3*κ*D-4*s*d*ca^4*X+s*d*ca^2*κ*D*X-8*s*d*ca^4
            -2*s*d*ca^3*κ+s*d*ca^3*D+s*d*κ^3*D-s*d*ca*κ*D^2+s*d*κ^2*D^2-6*s*d*ca^3*X
              +2*s*d*ca^2*κ*X+s*d*κ^2*D*X+s*d*κ*D^2*X-8*s*d*ca^3-2*s*d*ca^2*κ+18*s*d*κ^3
                +8*s*d*κ*k^2+2*s*d*ca*κ*D-s*d*κ^2*D-s*d*ca*D^2+s*d*κ*D^2-8*s*d*ca^2*X+18*s*d*κ^2*X
                  +6*s*d*k^2*X-3*s*d*κ*D*X-10*s*d*ca^2+8*s*d*ca*κ+10*s*d*κ^2+16*s*d*k^2+2*s*d*ca*D
                    -3*s*d*κ*D-s*d*D^2-10*s*d*ca*X-26*s*d*κ*X-2*s*d*ca-26*s*d*κ+3*s*d*D-6*s*d*X
                      +20*s*d) * hDdef +
      (-2*s*c^2*d^3*ca^4*κ^4-2*s*d^3*ca^6*κ^2*k^2+s*d^3*ca^6*κ^3*D+2*s*d^3*ca^6*κ^2*D
        -s*c^2*d^3*ca^2*κ^4*D+s*d*ca^6*κ*k^2*D^2-4*s*d^3*ca^5*κ*k^2*X-s*d*ca^5*κ*k^2*D^2*X
          +4*s*c^2*d^3*ca^4*κ^2+2*s*c^2*d*ca^4*κ^4+2*s*d^3*ca^4*κ^4+8*s*d^3*ca^6*k^2
            +4*s*d^3*ca^5*κ*k^2+2*s*d^3*ca^4*κ^2*k^2+2*s*d*ca^6*κ^2*k^2-s*d^3*ca^4*κ^3*D
              -s*d*ca^6*κ^3*D-s*d*ca^6*κ*k^2*D+2*s*d*ca^6*k^2*D^2-4*s*d^3*ca^5*k^2*X
                -6*s*d^3*ca^4*κ*k^2*X+s*d*ca^5*κ*k^2*D*X-s*d*ca^5*k^2*D^2*X-s*d*ca^4*κ*k^2*D^2*X
                  +4*s*d^3*ca^6*κ-4*s*d^3*ca^5*κ^2+14*s*d^3*ca^5*k^2-4*s*d^3*ca^4*κ*k^2
                    -2*s*d^3*ca^5*κ*D+s*c^2*d^3*ca^2*κ^2*D-4*s*d^3*ca^4*κ^2*D-2*s*d*ca^6*κ^2*D
                      +s*c^2*d^3*κ^4*D+s*d^3*ca^2*κ^4*D-2*s*d*ca^6*k^2*D+s*d^3*ca^3*κ^2*D^2
                        +s*d*ca^5*k^2*D^2-s*d*ca^4*κ*k^2*D^2-10*s*d^3*ca^4*k^2*X
                          -4*s*d^3*ca^3*κ*k^2*X+4*s*d*ca^5*κ*k^2*X+s*d*ca^5*k^2*D*X
                            +s*d*ca^4*κ*k^2*D*X+s*d*ca^5*κ*D^2*X-2*s*d*ca^4*k^2*D^2*X
                              -2*s*c^2*d^3*ca^4+8*s*d^3*ca^6-2*s*d^3*ca^5*κ-2*s*c^2*d^3*ca^2*κ^2
                                -4*s*c^2*d*ca^4*κ^2-14*s*d^3*ca^4*κ^2+2*s*c^2*d^3*κ^4
                                  -2*s*d*ca^4*κ^4+10*s*d^3*ca^4*k^2-8*s*d*ca^6*k^2
                                    +2*s*d*ca^5*κ*k^2+2*s*d^3*ca^2*κ^2*k^2-2*s*d^3*ca^5*D
                                      -3*s*d^3*ca^3*κ^2*D-s*d^3*ca^2*κ^3*D+s*d*ca^4*κ^3*D
                                        -2*s*d*ca^5*k^2*D-s*d*ca^4*κ*k^2*D-4*s*d*ca^3*κ^2*k^2*D
                                          +s*d^3*ca^3*κ*D^2+s*d*ca^5*κ*D^2-s*d^3*ca^2*κ^2*D^2
                                            -s*d*ca^4*κ^2*D^2-14*s*d^3*ca^3*k^2*X+4*s*d*ca^5*k^2*X
                                              -4*s*d^3*ca^2*κ*k^2*X+6*s*d*ca^4*κ*k^2*X
                                                +3*s*d*ca^5*κ*D*X+2*s*d*ca^4*k^2*D*X
                                                  -2*s*d*ca^3*κ*k^2*D*X+s*d*ca^5*D^2*X
                                                    +s*d*ca^4*κ*D^2*X-2*s*d*ca^3*k^2*D^2*X
                                                      +8*s*d^3*ca^5-8*s*d^3*ca^4*κ-4*s*d*ca^6*κ
                                                        -22*s*d^3*ca^3*κ^2+4*s*d*ca^5*κ^2
                                                          -18*s*d^3*ca^2*κ^3+12*s*d^3*ca^3*k^2
                                                            -16*s*d*ca^5*k^2-8*s*d^3*ca^2*κ*k^2
                                                              +2*s*d*ca^4*κ*k^2+s*d^3*ca^4*D
                                                                -s*d^3*ca^3*κ*D+5*s*d*ca^5*κ*D
                                                                  -s*c^2*d^3*κ^2*D
                                                                    +s*c^2*d*ca^2*κ^2*D
                                                                      +2*s*d^3*ca^2*κ^2*D
                                                                        +5*s*d*ca^4*κ^2*D
                                                                          -s*d^3*κ^4*D
                                                                            +4*s*d*ca^4*k^2*D
                                                                              -2*s*d*ca^3*κ*k^2*D
                                                                                +s*d*ca^5*D^2
                                                                                  -s*d^3*ca^2*κ*D^2-s*d*ca^4*κ*D^2-s*d^3*ca*κ^2*D^2-2*s*d*ca^3*κ^2*D^2+s*d*ca^3*k^2*D^2-s*d*ca^2*κ*k^2*D^2-4*s*d*ca^5*κ*X-18*s*d^3*ca^2*k^2*X+10*s*d*ca^4*k^2*X+8*s*d^3*ca*κ*k^2*X+8*s*d*ca^3*κ*k^2*X+3*s*d*ca^5*D*X+5*s*d*ca^4*κ*D*X-8*s*d*ca^2*κ*k^2*D*X+2*s*d*ca^4*D^2*X-2*s*d*ca^2*k^2*D^2*X+s*d*ca*κ*k^2*D^2*X+2*s*c^2*d^3*ca^2+2*s*c^2*d*ca^4+12*s*d^3*ca^4-8*s*d*ca^6-18*s*d^3*ca^3*κ-2*s*d*ca^5*κ-2*s*c^2*d^3*κ^2+2*s*c^2*d*ca^2*κ^2-40*s*d^3*ca^2*κ^2+14*s*d*ca^4*κ^2-2*s*d*ca^3*κ^3-2*s*d^3*κ^4-16*s*d^3*ca^2*k^2-20*s*d*ca^4*k^2-2*s*d*ca^3*κ*k^2-2*s*d^3*κ^2*k^2-2*s*d*ca^2*κ^2*k^2+3*s*d^3*ca^3*D+5*s*d*ca^5*D+3*s*d^3*ca^2*κ*D+7*s*d*ca^4*κ*D+3*s*d^3*ca*κ^2*D+4*s*d*ca^3*κ^2*D+s*d^3*κ^3*D+3*s*d*ca^2*κ^3*D+18*s*d*ca^3*k^2*D-15*s*d*ca^2*κ*k^2*D+4*s*d*ca*κ^2*k^2*D-s*d^3*ca^2*D^2+2*s*d*ca^4*D^2+s*d^3*ca*κ*D^2-3*s*d*ca^3*κ*D^2+s*d^3*κ^2*D^2-2*s*d*ca^2*κ^2*D^2-2*s*d*ca^2*k^2*D^2+s*d*ca^2*κ*D^3-4*s*d*ca^5*X-6*s*d*ca^4*κ*X-10*s*d^3*ca*k^2*X+18*s*d*ca^3*k^2*X+10*s*d^3*κ*k^2*X+10*s*d*ca^2*κ*k^2*X+8*s*d*ca^4*D*X+6*s*d*ca^3*κ*D*X-8*s*d*ca^2*k^2*D*X+s*d*ca*κ*k^2*D*X+2*s*d*ca^3*D^2*X-s*d*ca*k^2*D^2*X+s*d*κ*k^2*D^2*X+22*s*d^3*ca^3-12*s*d*ca^5+14*s*d^3*ca^2*κ+2*s*d*ca^4*κ+10*s*d^3*ca*κ^2+32*s*d*ca^3*κ^2+18*s*d^3*κ^3+16*s*d*ca^2*κ^3-22*s*d^3*ca*k^2-20*s*d*ca^3*k^2-2*s*c^2*d*κ*k^2+8*s*d^3*κ*k^2+24*s*d*ca^2*κ*k^2-s*c^2*d*ca^2*D+2*s*d^3*ca^2*D+11*s*d*ca^4*D-3*s*d^3*ca*κ*D+5*s*d*ca^3*κ*D-16*s*d*ca^2*κ^2*D+2*s*d*ca*κ^3*D-10*s*d*ca^2*k^2*D+2*s*d*ca*κ*k^2*D-s*d^3*ca*D^2+s*d^3*κ*D^2-3*s*d*ca^2*κ*D^2+s*d*ca*κ^2*D^2-2*s*d*ca*k^2*D^2+s*d*κ*k^2*D^2+s*d*ca^2*D^3-10*s*d*ca^4*X-8*s*d*ca^3*κ*X+28*s*d*ca^2*k^2*X-12*s*d*ca*κ*k^2*X+14*s*d*ca^3*D*X+12*s*d*ca^2*κ*D*X-7*s*d*ca*k^2*D*X+7*s*d*κ*k^2*D*X+2*s*d*ca^2*D^2*X-s*d*ca*κ*D^2*X-2*s*c^2*d*ca^2+30*s*d^3*ca^2-26*s*d*ca^4-32*s*d^3*ca*κ+20*s*d*ca^3*κ-6*s*d^3*κ^2+54*s*d*ca^2*κ^2-2*s*d^3*k^2+36*s*d*ca^2*k^2+2*s*d^3*ca*D+11*s*d*ca^3*D-3*s*d^3*κ*D-16*s*d*ca^2*κ*D-10*s*d*ca*κ^2*D-s*d*κ^3*D-16*s*d*ca*k^2*D+9*s*d*κ*k^2*D-s*d^3*D^2+s*d*ca^2*D^2-2*s*d*ca*κ*D^2+s*d*κ^2*D^2+s*d*ca*D^3-s*d*κ*D^3-18*s*d*ca^3*X-10*s*d*ca^2*κ*X+16*s*d*ca*k^2*X-16*s*d*κ*k^2*X+26*s*d*ca^2*D*X-9*s*d*ca*κ*D*X+s*d*ca*D^2*X-s*d*κ*D^2*X+20*s*d^3*ca-44*s*d*ca^3-24*s*d^3*κ-6*s*d*ca*κ^2-18*s*d*κ^3+36*s*d*ca*k^2-16*s*d*κ*k^2+3*s*d^3*D+15*s*d*ca^2*D-10*s*d*ca*κ*D-2*s*d*κ^2*D-8*s*d*k^2*D+2*s*d*κ*D^2+s*d*D^3-28*s*d*ca^2*X+12*s*d*ca*κ*X+17*s*d*ca*D*X-17*s*d*κ*D*X+38*s*d^3-52*s*d*ca^2+44*s*d*ca*κ+8*s*d*κ^2+8*s*d*k^2+18*s*d*ca*D+9*s*d*κ*D-3*s*d*D^2-16*s*d*ca*X+16*s*d*κ*X-36*s*d*ca+16*s*d*κ-28*s*d*D-8*s*d) * hX

end DLMF.JacobiElliptic

end
end
