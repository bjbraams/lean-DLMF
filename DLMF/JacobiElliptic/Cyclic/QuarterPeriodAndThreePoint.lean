/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.ElementaryIdentities

/-!
# Quarter-period data and Jacobi three-point identities

Quarter-period shifts and third-period values prepare the cyclic identities of Jacobian elliptic
functions.

Source references and common attribution are retained in
`DLMF.JacobiElliptic.Cyclic`.
-/

@[expose] public section

open Complex DLMF.Elliptic

open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

/-- The cyclic argument `z + N p⁻¹ (m - 1) K(k)` of DLMF 22.9.1–22.9.6 (`N = 2` or `4`). -/
@[dlmf 22.9.E1, dlmf 22.9.E4]
def jacobiCyclicArg (N m p : ℕ) (z k : ℂ) : ℂ := z + N * ((m : ℂ) - 1) / p * compEllIntKk k

/-- `s_{m,p}^{(N)} = sn(z + N p⁻¹(m - 1)K, k)` (DLMF 22.9.1, 22.9.4). -/
@[dlmf 22.9.E1, dlmf 22.9.E4]
def jacobiCyclicS (N m p : ℕ) (z k : ℂ) : ℂ := jacobiSnk (jacobiCyclicArg N m p z k) k

/-- `c_{m,p}^{(N)} = cn(z + N p⁻¹(m - 1)K, k)` (DLMF 22.9.2, 22.9.5). -/
@[dlmf 22.9.E2, dlmf 22.9.E5]
def jacobiCyclicC (N m p : ℕ) (z k : ℂ) : ℂ := jacobiCnk (jacobiCyclicArg N m p z k) k

/-- `d_{m,p}^{(N)} = dn(z + N p⁻¹(m - 1)K, k)` (DLMF 22.9.3, 22.9.6). -/
@[dlmf 22.9.E3, dlmf 22.9.E6]
def jacobiCyclicD (N m p : ℕ) (z k : ℂ) : ℂ := jacobiDnk (jacobiCyclicArg N m p z k) k

/-- `κ = dn(2K/3, k)` (DLMF 22.9.7). -/
@[dlmf 22.9.E7]
def jacobiCyclicKappa (k : ℂ) : ℂ := jacobiDnk (2 * compEllIntKk k / 3) k

/-! ### Helpers (quarter-period shifts and the points `2K/3`, `4K/3`) -/

/-- The stated relation follows from the given hypotheses: `jacobiRegulark .d z k`. -/
lemma p22R1_reg_d_of_n_add_K {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (h : jacobiRegulark .n (z + compEllIntKk k) k) : jacobiRegulark .d z k :=
  (p22R1_reg_add_K hk .n z).1 h

/-- Values at `z + K` in terms of `sn, cn, dn` at `z` (`dn z ≠ 0`). -/
lemma p22R1_add_K_vals {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : jacobiRegulark .n z k) :
    jacobiSnk (z + compEllIntKk k) k = jacobiCnk z k / jacobiDnk z k ∧
    jacobiCnk (z + compEllIntKk k) k =
      -jacobiComodulusk k * (jacobiSnk z k / jacobiDnk z k) ∧
    jacobiDnk (z + compEllIntKk k) k = jacobiComodulusk k * (1 / jacobiDnk z k) := by
  obtain ⟨-, -, -, -, -, -, e7, e8, e9⟩ := je22a_glaisher_via_n hn
  refine ⟨?_, ?_, ?_⟩
  · rw [(jacobiSnk_shift hk z).1, e8]
  · rw [(jacobiCnk_shift hk z).1, e7]
  · rw [(jacobiDnk_shift hk z).1, e9]

/-- Identity under the stated parameter and domain assumptions: `jacobiCyclicArg 2 1 2 z k = z ∧
jacobiCyclicArg 2 2 2 z k = z + compEllIntKk k`. -/
lemma p22R1_cyc2 (k z : ℂ) : jacobiCyclicArg 2 1 2 z k = z ∧
    jacobiCyclicArg 2 2 2 z k = z + compEllIntKk k := by
  constructor <;> (simp only [jacobiCyclicArg]; push_cast; ring)

/-- Identity under the stated parameter and domain assumptions: `jacobiCyclicArg 2 1 4 z k = z ∧
jacobiCyclicArg 2 2 4 z k = z + compEllIntKk k / 2 ∧ jacobiCyclicArg 2 3 4 z k = z +
compEllIntKk k ∧ jacobiCyclicArg 2 4 4 z k = (z + compEllIntKk k / 2) + compEllIntKk k`. -/
lemma p22R1_cyc4 (k z : ℂ) : jacobiCyclicArg 2 1 4 z k = z ∧
    jacobiCyclicArg 2 2 4 z k = z + compEllIntKk k / 2 ∧
    jacobiCyclicArg 2 3 4 z k = z + compEllIntKk k ∧
    jacobiCyclicArg 2 4 4 z k = (z + compEllIntKk k / 2) + compEllIntKk k := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [jacobiCyclicArg]; push_cast; ring)

/-- The three cyclic points `z, z + 4K/3, z + 8K/3` (`N = 4`, `p = 3`). -/
lemma p22R1_cyc43_vals {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg4 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 4 m 3 z k) k) :
    let s := jacobiSnk z k; let c := jacobiCnk z k; let d := jacobiDnk z k
    let a := 2 * compEllIntKk k / 3
    let sa := jacobiSnk a k; let ca := jacobiCnk a k; let κ := jacobiDnk a k
    let D := 1 - k ^ 2 * s ^ 2 * sa ^ 2
    jacobiRegulark .n z k ∧ D ≠ 0 ∧
    jacobiCyclicS 4 1 3 z k = s ∧ jacobiCyclicC 4 1 3 z k = c ∧ jacobiCyclicD 4 1 3 z k = d ∧
    jacobiCyclicS 4 2 3 z k = (-s * ca * κ + sa * c * d) / D ∧
    jacobiCyclicC 4 2 3 z k = (-c * ca - s * d * sa * κ) / D ∧
    jacobiCyclicD 4 2 3 z k = (d * κ + k ^ 2 * s * c * sa * ca) / D ∧
    jacobiCyclicS 4 3 3 z k = (-s * ca * κ - sa * c * d) / D ∧
    jacobiCyclicC 4 3 3 z k = (-c * ca + s * d * sa * κ) / D ∧
    jacobiCyclicD 4 3 3 z k = (d * κ - k ^ 2 * s * c * sa * ca) / D := by
  intro s c d a sa ca κ D
  obtain ⟨-, hnb, -, vs, vc, vd, -⟩ := p22R1_third_vals hk
  set b := 4 * compEllIntKk k / 3 with hb
  have g1 : jacobiCyclicArg 4 1 3 z k = z := by simp only [jacobiCyclicArg]; push_cast; ring
  have g2 : jacobiCyclicArg 4 2 3 z k = z + b := by simp only [jacobiCyclicArg, b]; push_cast; ring
  have g3 : jacobiCyclicArg 4 3 3 z k = z - b + 2 * compEllIntKk k + 2 * compEllIntKk k := by
    simp only [jacobiCyclicArg, b]; push_cast; ring
  have hn := hreg4 1; have hp := hreg4 2; have hm := hreg4 3
  rw [g1] at hn; rw [g2] at hp; rw [g3, p22R1_reg_add_two_K hk, p22R1_reg_add_two_K hk] at hm
  obtain ⟨hD, e1, e2, e3, e4, e5, e6⟩ := p22R1_add_sub_vals hk hn hnb hp hm
  simp only [vs, vc, vd] at hD e1 e2 e3 e4 e5 e6
  have s4 : ∀ w, jacobiSnk (w + 2 * compEllIntKk k + 2 * compEllIntKk k) k = jacobiSnk w k := by
    intro w; rw [(jacobiSnk_shift hk _).2.2.2.1, (jacobiSnk_shift hk _).2.2.2.1, neg_neg]
  have c4 : ∀ w, jacobiCnk (w + 2 * compEllIntKk k + 2 * compEllIntKk k) k = jacobiCnk w k := by
    intro w; rw [(jacobiCnk_shift hk _).2.2.2.1, (jacobiCnk_shift hk _).2.2.2.1, neg_neg]
  have d4 : ∀ w, jacobiDnk (w + 2 * compEllIntKk k + 2 * compEllIntKk k) k = jacobiDnk w k := by
    intro w; rw [(jacobiDnk_shift hk _).2.2.2.1, (jacobiDnk_shift hk _).2.2.2.1]
  refine ⟨hn, hD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [jacobiCyclicS, g1, s]
  · simp only [jacobiCyclicC, g1, c]
  · simp only [jacobiCyclicD, g1, d]
  · rw [jacobiCyclicS, g2, e1]; ring
  · rw [jacobiCyclicC, g2, e2]; ring
  · rw [jacobiCyclicD, g2, e3]; ring
  · rw [jacobiCyclicS, g3, s4, e4]; ring
  · rw [jacobiCyclicC, g3, c4, e5]; ring
  · rw [jacobiCyclicD, g3, d4, e6]; ring

/-- The three cyclic points `z, z + 2K/3, z + 4K/3` (`N = 2`, `p = 3`). -/
lemma p22R1_cyc23_vals {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg2 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 2 m 3 z k) k) :
    let s := jacobiSnk z k; let c := jacobiCnk z k; let d := jacobiDnk z k
    let a := 2 * compEllIntKk k / 3
    let sa := jacobiSnk a k; let ca := jacobiCnk a k; let κ := jacobiDnk a k
    let D := 1 - k ^ 2 * s ^ 2 * sa ^ 2
    jacobiRegulark .n z k ∧ D ≠ 0 ∧
    jacobiCyclicS 2 1 3 z k = s ∧ jacobiCyclicC 2 1 3 z k = c ∧ jacobiCyclicD 2 1 3 z k = d ∧
    jacobiCyclicS 2 2 3 z k = (s * ca * κ + sa * c * d) / D ∧
    jacobiCyclicC 2 2 3 z k = (c * ca - s * d * sa * κ) / D ∧
    jacobiCyclicD 2 2 3 z k = (d * κ - k ^ 2 * s * c * sa * ca) / D ∧
    jacobiCyclicS 2 3 3 z k = -((s * ca * κ - sa * c * d) / D) ∧
    jacobiCyclicC 2 3 3 z k = -((c * ca + s * d * sa * κ) / D) ∧
    jacobiCyclicD 2 3 3 z k = (d * κ + k ^ 2 * s * c * sa * ca) / D := by
  intro s c d a sa ca κ D
  obtain ⟨hna, -⟩ := p22R1_third_vals hk
  have g1 : jacobiCyclicArg 2 1 3 z k = z := by simp only [jacobiCyclicArg]; push_cast; ring
  have g2 : jacobiCyclicArg 2 2 3 z k = z + a := by simp only [jacobiCyclicArg, a]; push_cast; ring
  have g3 : jacobiCyclicArg 2 3 3 z k = z - a + 2 * compEllIntKk k := by
    simp only [jacobiCyclicArg, a]; push_cast; ring
  have hn := hreg2 1; have hp := hreg2 2; have hm := hreg2 3
  rw [g1] at hn; rw [g2] at hp; rw [g3, p22R1_reg_add_two_K hk] at hm
  obtain ⟨hD, e1, e2, e3, e4, e5, e6⟩ := p22R1_add_sub_vals hk hn hna hp hm
  refine ⟨hn, hD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [jacobiCyclicS, g1, s]
  · simp only [jacobiCyclicC, g1, c]
  · simp only [jacobiCyclicD, g1, d]
  · rw [jacobiCyclicS, g2, e1]
  · rw [jacobiCyclicC, g2, e2]
  · rw [jacobiCyclicD, g2, e3]
  · rw [jacobiCyclicS, g3, (jacobiSnk_shift hk _).2.2.2.1, e4]
  · rw [jacobiCyclicC, g3, (jacobiCnk_shift hk _).2.2.2.1, e5]
  · rw [jacobiCyclicD, g3, (jacobiDnk_shift hk _).2.2.2.1, e6]

/-- DLMF 22.9.8: cyclic identity (three points, rank 2), at points where the functions
are finite. -/
@[dlmf 22.9.E7, dlmf 22.9.E8]
theorem jacobi_cyclic_s4_pairs {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg4 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 4 m 3 z k) k) :
    jacobiCyclicS 4 1 3 z k * jacobiCyclicS 4 2 3 z k + jacobiCyclicS 4 2 3 z k *
      jacobiCyclicS 4 3 3 z k + jacobiCyclicS 4 3 3 z k * jacobiCyclicS 4 1 3 z k =
        (jacobiCyclicKappa k ^ 2 - 1) / k ^ 2 := by
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
  linear_combination (d^2*ca^2*k^2-d^2*k^2) * h1 +
      (-d^2*ca^3*κ-1/2*ca^4*κ^2-1/2*ca^4*κ*X-d^2*ca^3+d^2*ca^2*κ-ca^4*κ-ca^2*κ^2*D-ca^2*κ*D*X
        +d^2*ca*κ+3/2*ca^3*κ+ca^2*κ^2+ca^3*X+d^2*ca+5/2*ca^3-d^2*κ-1/2*ca^2*κ+2*ca^2*D-2*ca*κ*D
          +κ^2*D+κ*D*X-1/2*ca^2-3/2*ca*κ+1/2*κ^2-ca*X+1/2*κ*X-5/2*ca+3/2*κ-2*D+1/2) * h2 +
      (-1/2*d^4*sa^2*ca*k^2*X-1/2*d^2*sa^2*ca*k^4*X-1/2*d^2*sa^2*k^4*X^2+1/2*d^4*sa^2*k^2*X
        +1/2*d^2*sa^2*ca*κ*k^2*X-1/2*d^2*sa^2*k^4*X+s^2*d^2*ca*κ*k^2+1/2*d^2*sa^2*ca*κ*k^2
          +1/2*s^2*ca^2*κ^2*k^2+1/2*d^4*ca*κ^2*X+1/2*d^2*ca^2*κ^3*X+3/4*d^2*sa^2*ca*k^2*X
            +1/2*s^2*ca^2*κ*k^2*X-1/2*d^2*ca*κ^2*k^2*X-1/2*d^2*sa^2*k^2*D*X-1/4*sa^2*ca*κ*k^2*D*X
              +1/2*d^2*κ^2*k^2*X^2+s^2*d^2*ca*k^2-s^2*d^2*κ*k^2+s^2*ca^2*κ*k^2-3/2*d^2*sa^2*k^2*D
                -1/4*sa^2*ca*κ*k^2*D+s^2*κ^2*k^2*D-1/2*d^4*κ^2*X-1/2*d^2*ca*κ^3*X
                  -3/4*d^2*sa^2*k^2*X-1/4*sa^2*ca*κ*k^2*X-1/2*d^2*κ^2*k^2*X+d^2*κ^3*D*X
                    -1/4*sa^2*ca*k^2*D*X+s^2*κ*k^2*D*X-1/4*sa^2*κ*k^2*D*X+1/2*sa^2*k^2*D*X^2
                      +1/2*d^2*ca*κ^3-s^2*d^2*k^2-c^2*d^2*k^2-3/2*s^2*ca*κ*k^2-1/4*sa^2*ca*κ*k^2
                        +1/2*s^2*κ^2*k^2-1/4*sa^2*ca*k^2*D-1/4*sa^2*κ*k^2*D-7/4*d^2*ca*κ^2*X
                          +1/2*d^2*κ^3*X-1/2*ca^2*κ^3*X-s^2*ca*k^2*X+d^2*ca*k^2*X+1/2*s^2*κ*k^2*X
                            -1/4*sa^2*κ*k^2*X+1/2*d^2*κ^2*D*X+1/4*ca*κ^3*D*X+5/4*sa^2*k^2*D*X
                              -5/2*s^2*ca*k^2+d^2*ca*k^2+1/4*sa^2*ca*k^2+3/2*s^2*κ*k^2
                                -1/4*sa^2*κ*k^2-3/2*d^2*κ^2*D-1/4*ca*κ^3*D-2*s^2*k^2*D
                                  +7/4*sa^2*k^2*D+3/4*d^2*κ^2*X+1/4*ca*κ^3*X+1/4*ca*κ^2*D*X
                                    -3/4*κ^3*D*X-1/2*κ^2*D*X^2-1/4*ca*κ^3+1/2*s^2*k^2-1/4*sa^2*k^2
                                      -1/4*ca*κ^2*D-1/4*κ^3*D+ca*κ^2*X-1/4*κ^3*X-1/4*κ^2*D*X
                                        +1/4*ca*κ^2-1/4*κ^3+7/4*κ^2*D-1/4*κ^2) * ha1 +
      (1/2*d^4*ca^3*X+1/2*d^2*ca^3*k^2*X+1/2*d^2*ca^2*k^2*X^2-1/2*d^4*ca^2*X-1/2*d^2*ca^3*κ*X
        +1/2*d^2*ca^2*k^2*X-1/2*d^2*ca^3*κ-1/2*d^4*ca*X-3/4*d^2*ca^3*X-1/2*d^2*ca*k^2*X
          +1/2*d^2*ca^2*D*X+1/4*ca^3*κ*D*X-1/2*d^2*k^2*X^2+3/2*d^2*ca^2*D+1/4*ca^3*κ*D+1/2*d^4*X
            +3/4*d^2*ca^2*X+1/2*d^2*ca*κ*X+1/4*ca^3*κ*X-1/2*d^2*k^2*X+1/4*ca^3*D*X+1/4*ca^2*κ*D*X
              -1/2*ca^2*D*X^2+1/2*d^2*ca*κ+1/4*ca^3*κ+1/4*ca^3*D+1/4*ca^2*κ*D-1/4*d^2*ca*X
                +1/4*ca^2*κ*X-1/2*d^2*D*X-5/4*ca^2*D*X-1/4*ca*κ*D*X-d^2*ca-1/4*ca^3+1/4*ca^2*κ
                  -3/2*d^2*D-7/4*ca^2*D-1/4*ca*κ*D-3/4*d^2*X-1/4*ca*κ*X-1/4*ca*D*X-1/4*κ*D*X
                    +1/2*D*X^2+1/4*ca^2-1/4*ca*κ-1/4*ca*D-1/4*κ*D-1/4*κ*X+5/4*D*X+1/4*ca-1/4*κ
                      +7/4*D-1/4) * ha2 +
      (-1/2*d^4*ca*X-1/2*d^2*ca*k^2*X-1/2*d^2*k^2*X^2+1/2*d^4*X+1/2*d^2*ca*κ*X-1/2*d^2*k^2*X
        +1/2*d^2*ca*κ+3/4*d^2*ca*X-1/2*d^2*D*X-1/4*ca*κ*D*X-3/2*d^2*D-1/4*ca*κ*D-3/4*d^2*X
          -1/4*ca*κ*X-1/4*ca*D*X-1/4*κ*D*X+1/2*D*X^2-1/4*ca*κ-1/4*ca*D-1/4*κ*D-1/4*κ*X+5/4*D*X
            +1/4*ca-1/4*κ+7/4*D-1/4) * E1 +
      (1/2*d^4*ca*X+1/2*d^2*ca^2*κ*X-1/2*d^2*ca*k^2*X+1/2*d^2*k^2*X^2-1/2*d^4*X-1/2*d^2*ca*κ*X
        -1/2*d^2*k^2*X+d^2*κ*D*X+1/2*d^2*ca*κ-7/4*d^2*ca*X+1/2*d^2*κ*X-1/2*ca^2*κ*X+1/2*d^2*D*X
          +1/4*ca*κ*D*X-3/2*d^2*D-1/4*ca*κ*D+3/4*d^2*X+1/4*ca*κ*X+1/4*ca*D*X-3/4*κ*D*X-1/2*D*X^2
            -1/4*ca*κ-1/4*ca*D-1/4*κ*D+ca*X-1/4*κ*X-1/4*D*X+1/4*ca-1/4*κ+7/4*D-1/4) * E2 +
      (d^2*ca*κ+1/2*ca^2*κ^2+1/2*ca^2*κ*X+d^2*ca-d^2*κ+ca^2*κ+κ^2*D+κ*D*X-d^2-3/2*ca*κ+1/2*κ^2
        -ca*X+1/2*κ*X-5/2*ca+3/2*κ-2*D+1/2) * hDdef +
      (-d^4*ca^3*κ-1/2*d^2*ca^4*κ^2-d^2*ca^2*κ*k^2*X-d^4*ca^3+d^4*ca^2*κ-d^2*ca^4*κ+d^2*ca^3*κ^2
        +d^2*ca^3*k^2-d^2*ca^2*κ^2*D-d^2*ca^2*k^2*X+d^4*ca*κ+7/2*d^2*ca^3*κ+1/2*ca^4*κ^2
          -d^2*ca^2*k^2-3*d^2*ca^2*κ*D-1/2*ca^3*κ^2*D-d^2*ca*k^2*X+d^2*κ*k^2*X+d^4*ca+7/2*d^2*ca^3
            -d^4*κ-3/2*d^2*ca^2*κ+ca^4*κ-d^2*ca*κ^2-1/2*ca^3*κ^2-d^2*ca*k^2-d^2*ca^2*D-ca^3*κ*D
              +d^2*κ^2*D+1/2*ca^2*κ^2*D+ca^2*κ*D*X-1/2*d^2*ca^2-3/2*d^2*ca*κ-3/2*ca^3*κ
                +1/2*d^2*κ^2-1/2*ca^2*κ^2+d^2*k^2-d^2*ca*D-1/2*ca^3*D+d^2*κ*D+5/2*ca^2*κ*D
                  +1/2*ca*κ^2*D+ca^2*D*X-3/2*d^2*ca-2*ca^3+3/2*d^2*κ+1/2*ca*κ^2-d^2*D+3/2*ca^2*D
                    -1/2*κ^2*D+ca*D*X-κ*D*X-1/2*d^2+1/2*ca*κ+5/2*ca*D-3/2*κ*D+D^2-1/2*D) * hX

/-- DLMF 22.9.9: cyclic identity (three points, rank 2), at points where the functions
are finite. -/
@[dlmf 22.9.E7, dlmf 22.9.E9]
theorem jacobi_cyclic_c4_pairs {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg4 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 4 m 3 z k) k) :
    jacobiCyclicC 4 1 3 z k * jacobiCyclicC 4 2 3 z k + jacobiCyclicC 4 2 3 z k *
      jacobiCyclicC 4 3 3 z k + jacobiCyclicC 4 3 3 z k * jacobiCyclicC 4 1 3 z k =
        -(jacobiCyclicKappa k * (jacobiCyclicKappa k + 2)) / (1 + jacobiCyclicKappa k) ^ 2 := by
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
  linear_combination (-d^2*ca^4*κ^3*k^2*X-2*d^2*ca^4*κ^2*k^2*X-2*d^2*ca^4*κ*k^2*X
      +2*d^2*ca^2*κ^3*k^2*X-2*d^2*ca^4*k^2*X+4*d^2*ca^2*κ^2*k^2*X+d^2*ca^2*κ^4+4*d^2*ca^2*κ*k^2*X
        +ca^4*κ*k^2*X-d^2*κ^3*k^2*X-2*ca^3*κ*k^2*D*X+2*d^2*ca^2*κ^3+4*d^2*ca^2*k^2*X+2*ca^4*k^2*X
          -2*d^2*κ^2*k^2*X-2*ca^3*k^2*D*X+d^2*ca^2*κ^2-d^2*κ^4-2*d^2*κ*k^2*X-ca^2*κ*k^2*X
            -2*ca^2*k^2*D*X+2*ca*κ*k^2*D*X-2*d^2*κ^3-2*d^2*k^2*X-2*ca^2*k^2*X+2*ca*k^2*D*X-d^2*κ^2
              +2*k^2*D*X) * h1 +
      (1/2*ca^4*κ^3+1/2*ca^4*κ^2*X+ca^4*κ^2-2*ca^4*κ*D-2*ca^4*D*X-ca^2*κ^3-4*ca^4*D+3*ca^3*κ*D
        +ca^2*κ^2*D-2*c^2*ca^2*X-ca^2*κ^2*X+ca^2*κ*D*X-2*c^2*ca^2-3/2*ca^3*κ-2*ca^2*κ^2+3*ca^3*D
          +3*ca^2*κ*D+4*ca^2*D*X-3/2*ca^3+1/2*κ^3+5*ca^2*D-3*ca*κ*D-κ^2*D+2*c^2*X+1/2*κ^2*X-κ*D*X
            +2*c^2+3/2*ca*κ+κ^2-3*ca*D-κ*D-2*D*X+3/2*ca-D) * h2 +
      (s^2*d^2*ca^2*κ^3*k^2*X+c^2*d^2*ca^2*κ^3*k^2*X+2*s^2*d^2*ca^2*κ^2*k^2*X
        +2*c^2*d^2*ca^2*κ^2*k^2*X+c^2*d^2*sa^2*ca*k^2*X^2+c^2*d^2*sa^2*ca*k^2*X
          +2*s^2*d^2*ca^2*κ*k^2*X+2*c^2*d^2*ca^2*κ*k^2*X-s^2*d^2*κ^3*k^2*X-c^2*d^2*κ^3*k^2*X
            -d^2*ca^2*κ^3*k^2*X-1/2*d^2*sa^2*ca*κ*k^2*D*X-1/4*sa^2*ca*k^4*D*X^2
              -1/2*s^2*ca^2*κ^3*k^2-1/2*d^2*sa^2*ca*κ*k^2*D-1/2*d^2*ca^2*κ^4*X+c^2*d^2*sa^2*k^2*X
                +2*s^2*d^2*ca^2*k^2*X+2*c^2*d^2*ca^2*k^2*X-2*s^2*d^2*κ^2*k^2*X-2*c^2*d^2*κ^2*k^2*X
                  -1/2*s^2*ca^2*κ^2*k^2*X-2*d^2*ca^2*κ^2*k^2*X+d^2*sa^2*ca*k^2*D*X
                    -1/2*d^2*sa^2*κ*k^2*D*X-1/2*sa^2*ca*k^4*D*X-c^2*d^2*ca*κ^2*X^2
                      -c^2*sa^2*ca*k^2*X^2+1/4*sa^2*ca*k^4*X^2+c^2*sa^2*k^2*D*X^2
                        -1/4*sa^2*k^4*D*X^2-sa^2*ca*k^2*D^2*X^2-s^2*d^2*κ^4-s^2*ca^2*κ^2*k^2
                          -1/2*d^2*sa^2*ca*k^2*D-1/2*d^2*sa^2*κ*k^2*D+2*s^2*ca^2*κ*k^2*D
                            +c^2*d^2*ca*κ^2*X-c^2*sa^2*ca*k^2*X-2*s^2*d^2*κ*k^2*X
                              -2*c^2*d^2*κ*k^2*X-s^2*ca^2*κ*k^2*X-c^2*ca^2*κ*k^2*X
                                -2*d^2*ca^2*κ*k^2*X+d^2*κ^3*k^2*X+1/2*sa^2*ca*k^4*X
                                  +2*d^2*ca^2*κ^2*D*X+1/2*d^2*ca*κ^3*D*X+2*c^2*sa^2*k^2*D*X
                                    -3/2*d^2*sa^2*k^2*D*X+2*s^2*ca^2*k^2*D*X+2*s^2*ca*κ*k^2*D*X
                                      +2*c^2*ca*κ*k^2*D*X-1/2*ca^2*κ^2*k^2*D*X-1/2*sa^2*k^4*D*X
                                        -2*sa^2*ca*k^2*D^2*X+1/4*sa^2*k^4*X^2
                                          +5/4*sa^2*ca*k^2*D*X^2+1/4*ca*κ^2*k^2*D*X^2
                                            -sa^2*k^2*D^2*X^2-2*s^2*d^2*κ^3+3/4*d^2*sa^2*ca*k^2
                                              +1/2*s^2*κ^3*k^2-1/2*d^2*ca*κ^3*D+c^2*sa^2*k^2*D
                                                +4*s^2*ca^2*k^2*D-3*s^2*ca*κ*k^2*D-s^2*κ^2*k^2*D
                                                  -sa^2*ca*k^2*D^2+c^2*d^2*κ^2*X+1/2*d^2*κ^4*X
                                                    +1/2*ca^2*κ^4*X+2*s^2*c^2*k^2*X
                                                      -2*s^2*d^2*k^2*X-2*c^2*d^2*k^2*X
                                                        -c^2*sa^2*k^2*X+3/4*d^2*sa^2*k^2*X
                                                          -2*s^2*ca^2*k^2*X-2*c^2*ca^2*k^2*X
                                                            -2*d^2*ca^2*k^2*X+1/2*s^2*κ^2*k^2*X
                                                              +2*d^2*κ^2*k^2*X+1/2*ca^2*κ^2*k^2*X
                                                                +1/2*sa^2*k^4*X-d^2*ca*κ^2*D*X
                                                                  -1/2*d^2*κ^3*D*X
                                                                    +2*s^2*ca*k^2*D*X
                                                                      +2*c^2*ca*k^2*D*X
                                                                        +sa^2*ca*k^2*D*X
                                                                          -s^2*κ*k^2*D*X
                                                                            +3/4*sa^2*κ*k^2*D*X
                                                                              -1/2*ca*κ^2*k^2*D*X
                                                                                -1/2*sa^2*k^2*D^2*X+c^2*ca*κ^2*X^2-1/4*sa^2*ca*k^2*X^2-1/4*ca*κ^2*k^2*X^2-c^2*κ^2*D*X^2+1/4*sa^2*k^2*D*X^2+1/4*κ^2*k^2*D*X^2+ca*κ^2*D^2*X^2-s^2*d^2*κ^2+2*s^2*c^2*k^2+3/4*d^2*sa^2*k^2+3/2*s^2*ca*κ*k^2+s^2*κ^2*k^2-1/2*d^2*ca*κ^2*D-1/2*d^2*κ^3*D-3*s^2*ca*k^2*D+5/4*sa^2*ca*k^2*D-s^2*κ*k^2*D+3/4*sa^2*κ*k^2*D+1/2*ca^2*κ*k^2*D+1/2*sa^2*k^2*D^2-c^2*ca*κ^2*X-1/2*sa^2*ca*k^2*X+2*d^2*κ*k^2*X+1/4*sa^2*κ*k^2*X+ca^2*κ*k^2*X+1/2*ca*κ^2*k^2*X-1/2*d^2*κ^2*D*X-2*ca^2*κ^2*D*X+2*c^2*k^2*D*X+3/4*sa^2*k^2*D*X+1/2*ca^2*k^2*D*X-5/2*ca*κ*k^2*D*X-1/4*sa^2*k^2*X^2-1/4*κ^2*k^2*X^2-5/4*ca*κ^2*D*X^2+κ^2*D^2*X^2+3/4*d^2*ca*κ^2+3/2*s^2*ca*k^2-sa^2*ca*k^2+1/4*sa^2*κ*k^2-1/2*ca^2*κ*k^2+c^2*κ^2*D-s^2*k^2*D-sa^2*k^2*D+ca^2*k^2*D-ca*κ^2*D^2-c^2*κ^2*X-3/4*d^2*κ^2*X-1/2*κ^4*X+2*d^2*k^2*X-1/2*sa^2*k^2*X+3/2*ca^2*k^2*X+1/2*ca*κ*k^2*X+3/2*ca*κ^2*D*X+1/4*κ^3*D*X-3/2*ca*k^2*D*X-1/2*κ*k^2*D*X-3/2*κ^2*D^2*X+1/4*ca*κ^2*X^2-1/4*κ^2*D*X^2+3/4*d^2*κ^2-1/4*sa^2*k^2-ca^2*k^2+5/4*ca*κ^2*D+3/4*κ^3*D+ca*k^2*D-1/2*κ*k^2*D+1/2*κ^2*D^2-1/4*κ^3*X-1/2*ca*k^2*X+1/2*κ*k^2*X+7/4*κ^2*D*X-2*k^2*D*X+1/4*κ^2*X^2-ca*κ^2+1/4*κ^3-ca*k^2+1/2*κ*k^2-κ^2*D-1/4*κ^2) * ha1 +
      (-c^2*d^2*ca^2*κ^3*X-2*c^2*d^2*ca^2*κ^2*X-c^2*d^2*ca^3*X^2-c^2*d^2*ca^3*X-2*c^2*d^2*ca^2*κ*X
        +c^2*d^2*κ^3*X+d^2*ca^2*κ^3*X+1/2*d^2*ca^3*κ*D*X+1/4*ca^3*k^2*D*X^2+1/2*d^2*ca^3*κ*D
          -3*c^2*d^2*ca^2*X+2*c^2*d^2*κ^2*X+2*d^2*ca^2*κ^2*X-d^2*ca^3*D*X+1/2*d^2*ca^2*κ*D*X
            +1/2*ca^3*k^2*D*X+c^2*d^2*ca*X^2+c^2*ca^3*X^2-1/4*ca^3*k^2*X^2-c^2*ca^2*D*X^2
              +1/4*ca^2*k^2*D*X^2+ca^3*D^2*X^2+1/2*d^2*ca^3*D+1/2*d^2*ca^2*κ*D+c^2*d^2*ca*X
                +c^2*ca^3*X+2*c^2*d^2*κ*X+c^2*ca^2*κ*X+2*d^2*ca^2*κ*X-d^2*κ^3*X-1/2*ca^3*k^2*X
                  -2*c^2*ca^2*D*X+3/2*d^2*ca^2*D*X-2*c^2*ca*κ*D*X-1/2*d^2*ca*κ*D*X
                    +1/2*ca^2*k^2*D*X+2*ca^3*D^2*X-1/4*ca^2*k^2*X^2-5/4*ca^3*D*X^2
                      -1/4*ca*k^2*D*X^2+ca^2*D^2*X^2-3/4*d^2*ca^3-c^2*ca^2*D-1/2*d^2*ca*κ*D
                        +ca^3*D^2+3*c^2*d^2*X+3*c^2*ca^2*X+5/4*d^2*ca^2*X-2*d^2*κ^2*X
                          -1/2*ca^2*k^2*X-2*c^2*ca*D*X+d^2*ca*D*X-ca^3*D*X-1/2*d^2*κ*D*X
                            -3/4*ca^2*κ*D*X-1/2*ca*k^2*D*X+1/2*ca^2*D^2*X-c^2*ca*X^2+1/4*ca^3*X^2
                              +1/4*ca*k^2*X^2+c^2*D*X^2-1/4*ca^2*D*X^2-1/4*k^2*D*X^2-ca*D^2*X^2
                                -3/4*d^2*ca^2-1/2*d^2*ca*D-5/4*ca^3*D-1/2*d^2*κ*D-5/4*ca^2*κ*D
                                  -1/2*ca^2*D^2-c^2*ca*X+1/2*ca^3*X-2*d^2*κ*X-5/4*ca^2*κ*X
                                    +1/2*ca*k^2*X-3/2*d^2*D*X-5/4*ca^2*D*X+5/2*ca*κ*D*X
                                      -1/2*k^2*D*X-2*ca*D^2*X+1/4*ca^2*X^2+1/4*k^2*X^2
                                        +5/4*ca*D*X^2-D^2*X^2+3/4*d^2*ca+ca^3+1/4*ca^2*κ+c^2*D
                                          -ca*D^2-c^2*X-5/4*d^2*X-ca^2*X-1/2*ca*κ*X+1/2*k^2*X
                                            +5/2*ca*D*X+5/4*κ*D*X-1/2*D^2*X-1/4*ca*X^2+1/4*D*X^2
                                              +3/4*d^2+5/4*ca^2+1/4*ca*D+5/4*κ*D+1/2*D^2-1/4*κ*X
                                                +11/4*D*X-1/4*X^2-1/4*κ-D-1/2*X-1/4) * ha2 +
      (c^2*d^2*ca*X^2+c^2*d^2*ca*X-1/2*d^2*ca*κ*D*X-1/4*ca*k^2*D*X^2-1/2*d^2*ca*κ*D+c^2*d^2*X
        +d^2*ca*D*X-1/2*d^2*κ*D*X-1/2*ca*k^2*D*X-c^2*ca*X^2+1/4*ca*k^2*X^2+c^2*D*X^2-1/4*k^2*D*X^2
          -ca*D^2*X^2-1/2*d^2*ca*D-1/2*d^2*κ*D-c^2*ca*X+1/2*ca*k^2*X+2*c^2*D*X-3/2*d^2*D*X
            -1/2*k^2*D*X-2*ca*D^2*X+1/4*k^2*X^2+5/4*ca*D*X^2-D^2*X^2+3/4*d^2*ca+c^2*D-ca*D^2-c^2*X
              +3/4*d^2*X+1/2*k^2*X+ca*D*X+3/4*κ*D*X-1/2*D^2*X-1/4*ca*X^2+1/4*D*X^2+3/4*d^2
                +5/4*ca*D+3/4*κ*D+1/2*D^2-1/2*ca*X+1/4*κ*X+3/4*D*X-1/4*X^2-ca+1/4*κ-D-1/2*X
                  -1/4) * E1 +
      (-1/2*d^2*ca^2*κ^2*X-c^2*d^2*ca*X^2+c^2*d^2*ca*X+2*d^2*ca^2*D*X+1/2*d^2*ca*κ*D*X
        -1/2*ca^2*k^2*D*X+1/4*ca*k^2*D*X^2-1/2*d^2*ca*κ*D+c^2*d^2*X+1/2*d^2*κ^2*X+1/2*ca^2*κ^2*X
          +1/2*ca^2*k^2*X-d^2*ca*D*X-1/2*d^2*κ*D*X-1/2*ca*k^2*D*X+c^2*ca*X^2-1/4*ca*k^2*X^2
            -c^2*D*X^2+1/4*k^2*D*X^2+ca*D^2*X^2-1/2*d^2*ca*D-1/2*d^2*κ*D-c^2*ca*X+1/2*ca*k^2*X
              -1/2*d^2*D*X-2*ca^2*D*X-1/4*k^2*X^2-5/4*ca*D*X^2+D^2*X^2+3/4*d^2*ca+c^2*D-ca*D^2
                -c^2*X-3/4*d^2*X-1/2*κ^2*X+3/2*ca*D*X+1/4*κ*D*X-3/2*D^2*X+1/4*ca*X^2-1/4*D*X^2
                  +3/4*d^2+5/4*ca*D+3/4*κ*D+1/2*D^2-1/4*κ*X+7/4*D*X+1/4*X^2-ca+1/4*κ-D-1/4) * E2 +
      (d^2*ca^2*κ^3*X+2*d^2*ca^2*κ^2*X+2*d^2*ca^2*κ*X-d^2*κ^3*X-1/2*ca^2*κ^3+2*d^2*ca^2*X
        -2*d^2*κ^2*X-1/2*ca^2*κ^2*X-ca^2*κ^2+2*ca^2*κ*D-2*d^2*κ*X-ca^2*κ*X+2*ca^2*D*X+2*ca*κ*D*X
          +1/2*κ^3+4*ca^2*D-3*ca*κ*D-κ^2*D+2*c^2*X-2*d^2*X-2*ca^2*X+1/2*κ^2*X+2*ca*D*X-κ*D*X+2*c^2
            +3/2*ca*κ+κ^2-3*ca*D-κ*D+3/2*ca-D) * hDdef +
      (c^2*d^2*ca^2*κ^4+2*c^2*d^2*ca^2*κ^3+1/2*d^2*ca^4*κ^3+2*c^2*d^2*ca^3*κ*X+c^2*d^2*ca^2*κ^2
        +d^2*ca^4*κ^2-c^2*d^2*κ^4-d^2*ca^2*κ^4-2*d^2*ca^4*κ*D-d^2*ca^3*κ^2*D+1/2*ca^4*κ*k^2*D
          +2*c^2*d^2*ca^3*X-1/2*ca^3*κ*k^2*D*X-2*c^2*d^2*κ^3-3*d^2*ca^2*κ^3-1/2*ca^4*κ^3
            -1/2*ca^4*κ*k^2-4*d^2*ca^4*D+d^2*ca^3*κ*D+d^2*ca^2*κ^2*D+ca^4*k^2*D+2*c^2*d^2*ca^2*X
              -2*c^2*d^2*ca*κ*X-2*c^2*ca^3*κ*X+1/2*ca^3*κ*k^2*X+2*c^2*ca^2*κ*D*X-1/2*ca^3*k^2*D*X
                -1/2*ca^2*κ*k^2*D*X-2*ca^3*κ*D^2*X-2*c^2*d^2*ca^2-c^2*d^2*κ^2-c^2*ca^2*κ^2
                  -3*d^2*ca^2*κ^2-ca^4*κ^2+d^2*κ^4-ca^4*k^2+2*d^2*ca^3*D+2*c^2*ca^2*κ*D
                    +3*d^2*ca^2*κ*D+2*ca^4*κ*D+2*c^2*ca*κ^2*D+d^2*ca*κ^2*D+ca^3*k^2*D-ca^2*κ*k^2*D
                      -2*ca^3*κ*D^2-2*c^2*ca^3*X+1/2*ca^3*k^2*X+1/2*ca^2*κ*k^2*X+2*c^2*ca^2*D*X
                        +5/2*ca^3*κ*D*X-ca^2*k^2*D*X+1/2*ca*κ*k^2*D*X-2*ca^3*D^2*X-2*ca^2*κ*D^2*X
                          -2*c^2*ca^2*κ+5/2*d^2*κ^3+ca^2*κ^3-ca^3*k^2+ca^2*κ*k^2+2*c^2*ca^2*D
                            +5*d^2*ca^2*D+4*ca^4*D+2*c^2*ca*κ*D-3*d^2*ca*κ*D-1/2*ca^3*κ*D
                              -d^2*κ^2*D+1/2*ca^2*κ^2*D-ca^2*k^2*D-2*ca^3*D^2+ca^2*κ*D^2
                                -2*c^2*ca^2*X+2*c^2*ca*κ*X-1/2*ca^3*κ*X+ca^2*k^2*X-1/2*ca*κ*k^2*X
                                  +2*c^2*ca*D*X+5/2*ca^3*D*X-2*c^2*κ*D*X+1/2*ca^2*κ*D*X
                                    -1/2*ca*k^2*D*X+1/2*κ*k^2*D*X-4*ca^2*D^2*X+2*ca*κ*D^2*X
                                      +2*c^2*d^2+c^2*ca^2+3/2*d^2*ca^2-1/2*ca^3*κ+2*d^2*κ^2
                                        +5/2*ca^2*κ^2+ca^2*k^2+2*c^2*ca*D-3*d^2*ca*D-1/2*ca^3*D
                                          -d^2*κ*D-7/2*ca^2*κ*D-5/2*ca*κ^2*D-ca*k^2*D+1/2*κ*k^2*D
                                            -3*ca^2*D^2+2*ca*κ*D^2-1/2*ca^3*X-1/2*ca^2*κ*X
                                              +1/2*ca*k^2*X-1/2*κ*k^2*X+3*ca^2*D*X-5/2*ca*κ*D*X
                                                -2*ca*D^2*X+2*κ*D^2*X+3/2*d^2*ca-1/2*ca^3
                                                  +3/2*ca^2*κ+1/2*ca*κ^2-1/2*κ^3+ca*k^2-1/2*κ*k^2
                                                    -2*c^2*D-d^2*D-2*ca^2*D+1/2*ca*κ*D-κ^2*D
                                                      +3*ca*D^2-κ*D^2-ca^2*X+1/2*ca*κ*X+1/2*ca*D*X
                                                        -1/2*κ*D*X-3/2*ca^2+1/2*ca*κ-1/2*ca*D
                                                          -1/2*κ*D+D^2-1/2*ca*X+1/2*κ*X-ca
                                                            +1/2*κ) * hX

/-- DLMF 22.9.10: cyclic identity (three points, rank 2), at points where the
functions are finite. -/
@[dlmf 22.9.E7, dlmf 22.9.E10]
theorem jacobi_cyclic_d_pairs {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg2 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 2 m 3 z k) k)
        (hreg4 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 4 m 3 z k) k) :
    jacobiCyclicD 2 1 3 z k * jacobiCyclicD 2 2 3 z k + jacobiCyclicD 2 2 3 z k *
      jacobiCyclicD 2 3 3 z k + jacobiCyclicD 2 3 3 z k * jacobiCyclicD 2 1 3 z k =
        jacobiCyclicKappa k * (jacobiCyclicKappa k + 2) ∧
    jacobiCyclicD 4 1 3 z k * jacobiCyclicD 4 2 3 z k + jacobiCyclicD 4 2 3 z k *
      jacobiCyclicD 4 3 3 z k + jacobiCyclicD 4 3 3 z k * jacobiCyclicD 4 1 3 z k =
        jacobiCyclicKappa k * (jacobiCyclicKappa k + 2) := by
  constructor
  · have V := p22R1_cyc23_vals hk z hreg2
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
    linear_combination (-d^2*ca^4*k^2+d^2*ca^2*k^2+ca^4*k^2-ca^2*k^2) * h1 +
        (d^2*ca^5*κ+c^2*ca^4*k^2+1/2*ca^5*κ^2*D+1/2*ca^5*κ*D*X+d^2*ca^5-d^2*ca^4*κ+ca^5*κ*D
          -d^2*ca^3*κ-2*ca^5*κ-c^2*ca^2*k^2+1/2*ca^4*κ*D-1/2*ca^3*κ^2*D-ca^5*X-1/2*ca^3*κ*D*X
            -d^2*ca^3-3*ca^5+d^2*ca^2*κ+2*ca^4*κ+1/2*ca^4*D-3/2*ca^3*κ*D-3/2*ca^2*κ^2*D
              -3/2*ca^2*κ*D*X+ca^4+3*ca^3*κ-ca^2*κ^2-1/2*ca^3*D-2*ca^2*κ*D+ca^3*X-ca^2*κ*X+4*ca^3
                -3*ca^2*κ+ca^2*D+1/2*ca*κ*D+3/2*κ^2*D+3/2*κ*D*X-ca*κ+κ^2+1/2*ca*D+3/2*κ*D+κ*X-ca+κ
                  -3/2*D-1) * h2 +
        (1/2*d^4*sa^2*ca^3*k^2*X+1/2*d^2*sa^2*ca^3*k^4*X+1/2*d^2*sa^2*ca^2*k^4*X^2
          -1/2*d^4*sa^2*ca^2*k^2*X+1/2*d^2*sa^2*ca^2*k^4*X-s^2*d^2*ca^3*κ*k^2-s^2*c^2*ca^2*k^4
            -1/2*s^2*ca^3*κ^2*k^2*D-1/2*d^4*ca^3*κ^2*X-d^2*sa^2*ca^3*k^2*X
              +1/2*d^2*sa^2*ca^2*κ*k^2*X+1/2*d^2*ca^3*κ^2*k^2*X-1/2*sa^2*ca^3*k^4*X
                -1/2*d^2*ca^3*κ^3*D*X+1/4*d^2*sa^2*ca^2*k^2*D*X-1/2*s^2*ca^3*κ*k^2*D*X
                  +1/4*sa^2*ca^2*κ*k^2*D^2*X-1/2*d^2*ca^2*κ^2*k^2*X^2-1/2*sa^2*ca^2*k^4*X^2
                    -s^2*d^2*ca^3*k^2+s^2*d^2*ca^2*κ*k^2+1/2*d^2*sa^2*ca^2*κ*k^2-s^2*ca^3*κ*k^2*D
                      +1/4*sa^2*ca^2*κ*k^2*D^2+1/2*d^4*ca^2*κ^2*X+d^2*sa^2*ca^2*k^2*X
                        +1/2*d^2*sa^2*ca*κ*k^2*X+1/2*d^2*ca^2*κ^2*k^2*X-1/2*sa^2*ca^2*k^4*X
                          -3/4*d^2*sa^2*ca*k^2*D*X-1/4*sa^2*ca^2*κ*k^2*D*X+1/4*sa^2*ca^2*k^2*D^2*X
                            +1/4*sa^2*ca*κ*k^2*D^2*X-1/2*sa^2*ca^2*k^2*D*X^2+s^2*d^2*ca^2*k^2
                              -1/2*d^2*sa^2*ca^2*k^2+1/2*d^2*sa^2*ca*κ*k^2+2*s^2*ca^3*κ*k^2
                                -1/2*d^2*sa^2*ca*k^2*D-1/2*s^2*ca^2*κ*k^2*D-1/4*sa^2*ca^2*κ*k^2*D
                                  +1/4*sa^2*ca^2*k^2*D^2+1/4*sa^2*ca*κ*k^2*D^2+2*d^2*ca^3*κ^2*X
                                    -1/2*d^2*ca^2*κ^3*X+s^2*ca^3*k^2*X-d^2*ca^3*k^2*X
                                      +1/2*sa^2*ca^3*k^2*X+1/2*d^2*sa^2*κ*k^2*X
                                        -1/2*sa^2*ca^2*κ*k^2*X-1/2*ca^3*κ^2*k^2*X
                                          -1/4*d^2*ca^2*κ^2*D*X+1/2*ca^3*κ^3*D*X
                                            +1/4*d^2*sa^2*k^2*D*X-3/2*sa^2*ca^2*k^2*D*X
                                              -1/4*sa^2*ca*κ*k^2*D*X-1/4*ca^2*κ^3*D^2*X
                                                +1/4*sa^2*ca*k^2*D^2*X+1/4*sa^2*κ*k^2*D^2*X
                                                  +1/2*sa^2*ca^2*k^2*X^2+1/2*ca^2*κ^2*k^2*X^2
                                                    +1/2*d^2*ca^2*κ^3-1/2*d^2*sa^2*ca*k^2
                                                      +3*s^2*ca^3*k^2-d^2*ca^3*k^2
                                                        +1/2*d^2*sa^2*κ*k^2-2*s^2*ca^2*κ*k^2
                                                          -1/2*sa^2*ca^2*κ*k^2-1/2*d^2*sa^2*k^2*D
                                                            -1/2*s^2*ca^2*k^2*D
                                                              -3/4*sa^2*ca^2*k^2*D
                                                                +1/2*s^2*ca*κ*k^2*D
                                                                  -1/4*sa^2*ca*κ*k^2*D
                                                                    +3/2*s^2*κ^2*k^2*D
                                                                      +1/4*ca^2*κ^3*D^2
                                                                        +1/4*sa^2*ca*k^2*D^2
                                                                          +1/4*sa^2*κ*k^2*D^2
                                                                            -d^2*ca^2*κ^2*X
                                                                              -1/2*d^2*ca*κ^3*X
                                                                                -1/2*d^2*sa^2*k^2*X+1/2*sa^2*ca^2*k^2*X-1/2*sa^2*ca*κ*k^2*X-1/2*ca^2*κ^2*k^2*X+3/4*d^2*ca*κ^2*D*X+3/2*d^2*κ^3*D*X+1/4*ca^2*κ^3*D*X+1/2*sa^2*ca*k^2*D*X+3/2*s^2*κ*k^2*D*X-1/4*sa^2*κ*k^2*D*X-1/4*ca^2*κ^2*D^2*X-1/4*ca*κ^3*D^2*X-1/4*sa^2*k^2*D^2*X+1/2*ca^2*κ^2*D*X^2-1/2*d^2*ca^2*κ^2+1/2*d^2*ca*κ^3-d^2*sa^2*k^2-2*s^2*ca^2*k^2+sa^2*ca^2*k^2-s^2*ca*κ*k^2-1/2*sa^2*ca*κ*k^2+s^2*κ^2*k^2-1/2*d^2*ca*κ^2*D-1/4*ca^2*κ^3*D+1/2*s^2*ca*k^2*D+1/4*sa^2*ca*k^2*D+3/2*s^2*κ*k^2*D-1/4*sa^2*κ*k^2*D+1/4*ca^2*κ^2*D^2+1/4*ca*κ^3*D^2-1/4*sa^2*k^2*D^2-3/2*ca^3*κ^2*X+1/2*d^2*κ^3*X+1/2*ca^2*κ^3*X+ca^3*k^2*X+s^2*κ*k^2*X-1/2*sa^2*κ*k^2*X-ca^2*κ*k^2*X-1/4*d^2*κ^2*D*X+1/2*ca^2*κ^2*D*X+1/4*ca*κ^3*D*X+1/2*sa^2*k^2*D*X-1/4*ca*κ^2*D^2*X-1/4*κ^3*D^2*X-1/2*ca^2*κ^2*X^2-1/2*d^2*ca*κ^2+1/2*d^2*κ^3-1/2*ca^2*κ^3-s^2*ca*k^2+1/2*sa^2*ca*k^2+ca^3*k^2+s^2*κ*k^2-1/2*sa^2*κ*k^2-1/2*d^2*κ^2*D-3/4*ca^2*κ^2*D-1/4*ca*κ^3*D-3/2*s^2*k^2*D+5/4*sa^2*k^2*D+1/4*ca*κ^2*D^2+1/4*κ^3*D^2+1/2*d^2*κ^2*X+1/2*ca^2*κ^2*X+1/2*ca*κ^3*X-1/2*ca*κ^2*D*X-5/4*κ^3*D*X+1/4*κ^2*D^2*X-d^2*κ^2+ca^2*κ^2-1/2*ca*κ^3-s^2*k^2+1/2*sa^2*k^2+ca^2*k^2+1/4*ca*κ^2*D-1/4*κ^3*D-1/4*κ^2*D^2-1/2*κ^3*X-1/2*κ^2*D*X+1/2*ca*κ^2-1/2*κ^3+5/4*κ^2*D+1/2*κ^2) * ha1 +
        (-1/2*d^4*ca^5*X-1/2*d^2*ca^5*k^2*X-1/2*d^2*ca^4*k^2*X^2+1/2*d^4*ca^4*X-1/2*d^2*ca^4*k^2*X
          +1/2*d^4*ca^3*X+d^2*ca^5*X-1/2*d^2*ca^4*κ*X+1/2*d^2*ca^3*k^2*X+1/2*ca^5*k^2*X
            -1/4*d^2*ca^4*D*X-1/4*ca^4*κ*D^2*X+1/2*d^2*ca^2*k^2*X^2+1/2*ca^4*k^2*X^2
              -1/2*d^2*ca^4*κ-1/4*ca^4*κ*D^2-1/2*d^4*ca^2*X-d^2*ca^4*X-1/2*d^2*ca^3*κ*X
                +1/2*d^2*ca^2*k^2*X+1/2*ca^4*k^2*X+3/4*d^2*ca^3*D*X+1/4*ca^4*κ*D*X-1/4*ca^4*D^2*X
                  -1/4*ca^3*κ*D^2*X+1/2*ca^4*D*X^2+1/2*d^2*ca^4-1/2*d^2*ca^3*κ+1/2*d^2*ca^3*D
                    +1/4*ca^4*κ*D-1/4*ca^4*D^2-1/4*ca^3*κ*D^2-1/2*ca^5*X+1/2*ca^4*κ*X
                      -1/2*ca^3*k^2*X+3/2*ca^4*D*X+1/4*ca^3*κ*D*X-1/4*ca^3*D^2*X-1/2*ca^4*X^2
                        -1/2*ca^2*k^2*X^2+3/2*d^2*ca^3+1/2*ca^4*κ+1/2*d^2*ca^2*D+3/4*ca^4*D
                          +1/4*ca^3*κ*D-1/4*ca^3*D^2+3/2*d^2*ca^2*X-1/2*ca^4*X+1/2*d^2*ca*κ*X
                            +1/2*ca^3*κ*X-1/2*ca^2*k^2*X-3/4*d^2*ca*D*X-1/2*ca^3*D*X
                              +1/2*ca^2*D^2*X+1/4*ca*κ*D^2*X-1/2*ca^2*D*X^2+1/2*d^2*ca^2-ca^4
                                +1/2*d^2*ca*κ+1/2*ca^3*κ-1/2*d^2*ca*D-1/4*ca^3*D+1/2*ca^2*D^2
                                  +1/4*ca*κ*D^2-1/2*ca^3*X+1/2*d^2*κ*X+ca^2*κ*X+1/4*d^2*D*X
                                    -2*ca^2*D*X-1/4*ca*κ*D*X+1/4*ca*D^2*X+1/4*κ*D^2*X+1/2*ca^2*X^2
                                      -1/2*d^2*ca-3/2*ca^3+1/2*d^2*κ-1/2*d^2*D-2*ca^2*D-1/4*ca*κ*D
                                        +1/4*ca*D^2+1/4*κ*D^2-1/2*d^2*X+1/2*ca^2*X-1/2*ca*κ*X
                                          +1/2*ca*D*X-1/4*κ*D*X-1/4*D^2*X-d^2-1/2*ca^2-1/2*ca*κ
                                            +1/4*ca*D-1/4*κ*D-1/4*D^2-1/2*κ*X+1/2*D*X+1/2*ca-1/2*κ
                                              +5/4*D+1/2) * ha2 +
        (1/2*d^4*ca^3*X+1/2*d^2*ca^3*k^2*X+1/2*d^2*ca^2*k^2*X^2-1/2*d^4*ca^2*X+1/2*d^2*ca^2*k^2*X
          -d^2*ca^3*X+1/2*d^2*ca^2*κ*X-1/2*ca^3*k^2*X+1/4*d^2*ca^2*D*X+1/4*ca^2*κ*D^2*X
            -1/2*ca^2*k^2*X^2+1/2*d^2*ca^2*κ+1/4*ca^2*κ*D^2+d^2*ca^2*X+1/2*d^2*ca*κ*X
              -1/2*ca^2*k^2*X-3/4*d^2*ca*D*X-1/4*ca^2*κ*D*X+1/4*ca^2*D^2*X+1/4*ca*κ*D^2*X
                -1/2*ca^2*D*X^2-1/2*d^2*ca^2+1/2*d^2*ca*κ-1/2*d^2*ca*D-1/4*ca^2*κ*D+1/4*ca^2*D^2
                  +1/4*ca*κ*D^2+1/2*ca^3*X+1/2*d^2*κ*X-1/2*ca^2*κ*X+1/4*d^2*D*X-3/2*ca^2*D*X
                    -1/4*ca*κ*D*X+1/4*ca*D^2*X+1/4*κ*D^2*X+1/2*ca^2*X^2-1/2*d^2*ca+1/2*d^2*κ
                      -1/2*ca^2*κ-1/2*d^2*D-3/4*ca^2*D-1/4*ca*κ*D+1/4*ca*D^2+1/4*κ*D^2-1/2*d^2*X
                        +1/2*ca^2*X-1/2*ca*κ*X+1/2*ca*D*X-1/4*κ*D*X-1/4*D^2*X-d^2+ca^2-1/2*ca*κ
                          +1/4*ca*D-1/4*κ*D-1/4*D^2-1/2*κ*X+1/2*D*X+1/2*ca-1/2*κ+5/4*D+1/2) * E1 +
        (-1/2*d^4*ca^3*X+1/2*d^2*ca^3*k^2*X-1/2*d^2*ca^3*κ*D*X-1/2*d^2*ca^2*k^2*X^2+1/2*d^4*ca^2*X
          +1/2*d^2*ca^2*k^2*X+2*d^2*ca^3*X-1/2*d^2*ca^2*κ*X-1/2*ca^3*k^2*X-1/4*d^2*ca^2*D*X
            +1/2*ca^3*κ*D*X-1/4*ca^2*κ*D^2*X+1/2*ca^2*k^2*X^2+1/2*d^2*ca^2*κ+1/4*ca^2*κ*D^2
              -d^2*ca^2*X-1/2*d^2*ca*κ*X-1/2*ca^2*k^2*X+3/4*d^2*ca*D*X+3/2*d^2*κ*D*X
                +1/4*ca^2*κ*D*X-1/4*ca^2*D^2*X-1/4*ca*κ*D^2*X+1/2*ca^2*D*X^2-1/2*d^2*ca^2
                  +1/2*d^2*ca*κ-1/2*d^2*ca*D-1/4*ca^2*κ*D+1/4*ca^2*D^2+1/4*ca*κ*D^2-3/2*ca^3*X
                    +1/2*d^2*κ*X+1/2*ca^2*κ*X-1/4*d^2*D*X+1/2*ca^2*D*X+1/4*ca*κ*D*X-1/4*ca*D^2*X
                      -1/4*κ*D^2*X-1/2*ca^2*X^2-1/2*d^2*ca+1/2*d^2*κ-1/2*ca^2*κ-1/2*d^2*D
                        -3/4*ca^2*D-1/4*ca*κ*D+1/4*ca*D^2+1/4*κ*D^2+1/2*d^2*X+1/2*ca^2*X
                          +1/2*ca*κ*X-1/2*ca*D*X-5/4*κ*D*X+1/4*D^2*X-d^2+ca^2-1/2*ca*κ+1/4*ca*D
                            -1/4*κ*D-1/4*D^2-1/2*κ*X-1/2*D*X+1/2*ca-1/2*κ+5/4*D+1/2) * E2 +
        (-d^2*ca^3*κ-1/2*ca^3*κ^2*D-1/2*ca^3*κ*D*X-d^2*ca^3+d^2*ca^2*κ-ca^3*κ*D+d^2*ca^2+2*ca^3*κ
          -1/2*ca^2*κ*D+ca^3*X+3*ca^3-2*ca^2*κ-1/2*ca^2*D+1/2*ca*κ*D+3/2*κ^2*D+3/2*κ*D*X-2*ca^2
            -ca*κ+κ^2+1/2*ca*D+3/2*κ*D+κ*X-ca+κ-3/2*D-1) * hDdef +
        (d^4*ca^5*κ+1/2*d^2*ca^5*κ^2*D+d^2*ca^4*κ*k^2*X+d^4*ca^5-d^4*ca^4*κ-d^2*ca^5*k^2
          +d^2*ca^5*κ*D+d^2*ca^4*k^2*X-d^4*ca^3*κ-3*d^2*ca^5*κ+d^2*ca^4*κ^2+d^2*ca^4*k^2
            +1/2*d^2*ca^4*κ*D-1/2*d^2*ca^3*κ^2*D-1/2*ca^5*κ^2*D+1/2*ca^4*κ^2*D^2+d^2*ca^3*k^2*X
              -d^2*ca^2*κ*k^2*X-ca^4*κ*k^2*X-d^4*ca^3-4*d^2*ca^5+d^4*ca^2*κ+3*d^2*ca^4*κ
                +d^2*ca^3*κ^2+d^2*ca^3*k^2+ca^5*k^2+1/2*d^2*ca^4*D-3/2*d^2*ca^3*κ*D-ca^5*κ*D
                  -3/2*d^2*ca^2*κ^2*D-1/2*ca^4*κ^2*D+ca^4*κ*D^2+1/2*ca^3*κ^2*D^2-ca^4*k^2*X
                    -ca^4*κ*D*X+4*d^2*ca^3*κ+2*ca^5*κ-d^2*ca^2*κ^2-ca^4*κ^2-d^2*ca^2*k^2
                      -1/2*d^2*ca^3*D-3*d^2*ca^2*κ*D-5/2*ca^4*κ*D+1/2*ca^4*D^2+3/2*ca^3*κ*D^2
                        +ca^4*κ*X-ca^3*k^2*X+ca^2*κ*k^2*X-ca^4*D*X+2*d^2*ca^3+3*ca^5-3*d^2*ca^2*κ
                          -ca^4*κ-d^2*ca*κ^2-ca^3*κ^2-ca^3*k^2-d^2*ca^2*D-2*ca^4*D+3/2*d^2*ca*κ*D
                            +3/2*d^2*κ^2*D+3/2*ca^2*κ^2*D+1/2*ca^3*D^2-1/2*ca*κ^2*D^2+ca^4*X
                              -ca^3*D*X+ca^2*κ*D*X-d^2*ca^2+ca^4+d^2*ca*κ-3*ca^3*κ+1/2*d^2*ca*D
                                -2*ca^3*D-1/2*d^2*κ*D+5*ca^2*κ*D+1/2*ca*κ^2*D-1/2*κ^2*D^2+ca^3*X
                                  -ca^2*κ*X-d^2*ca+ca^3+d^2*κ+ca*κ^2-3/2*d^2*D+3*ca^2*D-3/2*ca*κ*D
                                    -κ^2*D-1/2*ca*D^2+1/2*κ*D^2-d^2-ca*κ+ca*D-κ*D+3/2*D^2+D) * hX
  · have V := p22R1_cyc43_vals hk z hreg4
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
    linear_combination (-d^2*ca^4*k^2+d^2*ca^2*k^2+ca^4*k^2-ca^2*k^2) * h1 +
        (d^2*ca^5*κ+c^2*ca^4*k^2+1/2*ca^5*κ^2*D+1/2*ca^5*κ*D*X+d^2*ca^5-d^2*ca^4*κ+ca^5*κ*D
          -d^2*ca^3*κ-2*ca^5*κ-c^2*ca^2*k^2+1/2*ca^4*κ*D-1/2*ca^3*κ^2*D-ca^5*X-1/2*ca^3*κ*D*X
            -d^2*ca^3-3*ca^5+d^2*ca^2*κ+2*ca^4*κ+1/2*ca^4*D-3/2*ca^3*κ*D-3/2*ca^2*κ^2*D
              -3/2*ca^2*κ*D*X+ca^4+3*ca^3*κ-ca^2*κ^2-1/2*ca^3*D-2*ca^2*κ*D+ca^3*X-ca^2*κ*X+4*ca^3
                -3*ca^2*κ+ca^2*D+1/2*ca*κ*D+3/2*κ^2*D+3/2*κ*D*X-ca*κ+κ^2+1/2*ca*D+3/2*κ*D+κ*X-ca+κ
                  -3/2*D-1) * h2 +
        (1/2*d^4*sa^2*ca^3*k^2*X+1/2*d^2*sa^2*ca^3*k^4*X+1/2*d^2*sa^2*ca^2*k^4*X^2
          -1/2*d^4*sa^2*ca^2*k^2*X+1/2*d^2*sa^2*ca^2*k^4*X-s^2*d^2*ca^3*κ*k^2-s^2*c^2*ca^2*k^4
            -1/2*s^2*ca^3*κ^2*k^2*D-1/2*d^4*ca^3*κ^2*X-d^2*sa^2*ca^3*k^2*X
              +1/2*d^2*sa^2*ca^2*κ*k^2*X+1/2*d^2*ca^3*κ^2*k^2*X-1/2*sa^2*ca^3*k^4*X
                -1/2*d^2*ca^3*κ^3*D*X+1/4*d^2*sa^2*ca^2*k^2*D*X-1/2*s^2*ca^3*κ*k^2*D*X
                  +1/4*sa^2*ca^2*κ*k^2*D^2*X-1/2*d^2*ca^2*κ^2*k^2*X^2-1/2*sa^2*ca^2*k^4*X^2
                    -s^2*d^2*ca^3*k^2+s^2*d^2*ca^2*κ*k^2+1/2*d^2*sa^2*ca^2*κ*k^2-s^2*ca^3*κ*k^2*D
                      +1/4*sa^2*ca^2*κ*k^2*D^2+1/2*d^4*ca^2*κ^2*X+d^2*sa^2*ca^2*k^2*X
                        +1/2*d^2*sa^2*ca*κ*k^2*X+1/2*d^2*ca^2*κ^2*k^2*X-1/2*sa^2*ca^2*k^4*X
                          -3/4*d^2*sa^2*ca*k^2*D*X-1/4*sa^2*ca^2*κ*k^2*D*X+1/4*sa^2*ca^2*k^2*D^2*X
                            +1/4*sa^2*ca*κ*k^2*D^2*X-1/2*sa^2*ca^2*k^2*D*X^2+s^2*d^2*ca^2*k^2
                              -1/2*d^2*sa^2*ca^2*k^2+1/2*d^2*sa^2*ca*κ*k^2+2*s^2*ca^3*κ*k^2
                                -1/2*d^2*sa^2*ca*k^2*D-1/2*s^2*ca^2*κ*k^2*D-1/4*sa^2*ca^2*κ*k^2*D
                                  +1/4*sa^2*ca^2*k^2*D^2+1/4*sa^2*ca*κ*k^2*D^2+2*d^2*ca^3*κ^2*X
                                    -1/2*d^2*ca^2*κ^3*X+s^2*ca^3*k^2*X-d^2*ca^3*k^2*X
                                      +1/2*sa^2*ca^3*k^2*X+1/2*d^2*sa^2*κ*k^2*X
                                        -1/2*sa^2*ca^2*κ*k^2*X-1/2*ca^3*κ^2*k^2*X
                                          -1/4*d^2*ca^2*κ^2*D*X+1/2*ca^3*κ^3*D*X
                                            +1/4*d^2*sa^2*k^2*D*X-3/2*sa^2*ca^2*k^2*D*X
                                              -1/4*sa^2*ca*κ*k^2*D*X-1/4*ca^2*κ^3*D^2*X
                                                +1/4*sa^2*ca*k^2*D^2*X+1/4*sa^2*κ*k^2*D^2*X
                                                  +1/2*sa^2*ca^2*k^2*X^2+1/2*ca^2*κ^2*k^2*X^2
                                                    +1/2*d^2*ca^2*κ^3-1/2*d^2*sa^2*ca*k^2
                                                      +3*s^2*ca^3*k^2-d^2*ca^3*k^2
                                                        +1/2*d^2*sa^2*κ*k^2-2*s^2*ca^2*κ*k^2
                                                          -1/2*sa^2*ca^2*κ*k^2-1/2*d^2*sa^2*k^2*D
                                                            -1/2*s^2*ca^2*k^2*D
                                                              -3/4*sa^2*ca^2*k^2*D
                                                                +1/2*s^2*ca*κ*k^2*D
                                                                  -1/4*sa^2*ca*κ*k^2*D
                                                                    +3/2*s^2*κ^2*k^2*D
                                                                      +1/4*ca^2*κ^3*D^2
                                                                        +1/4*sa^2*ca*k^2*D^2
                                                                          +1/4*sa^2*κ*k^2*D^2
                                                                            -d^2*ca^2*κ^2*X
                                                                              -1/2*d^2*ca*κ^3*X
                                                                                -1/2*d^2*sa^2*k^2*X+1/2*sa^2*ca^2*k^2*X-1/2*sa^2*ca*κ*k^2*X-1/2*ca^2*κ^2*k^2*X+3/4*d^2*ca*κ^2*D*X+3/2*d^2*κ^3*D*X+1/4*ca^2*κ^3*D*X+1/2*sa^2*ca*k^2*D*X+3/2*s^2*κ*k^2*D*X-1/4*sa^2*κ*k^2*D*X-1/4*ca^2*κ^2*D^2*X-1/4*ca*κ^3*D^2*X-1/4*sa^2*k^2*D^2*X+1/2*ca^2*κ^2*D*X^2-1/2*d^2*ca^2*κ^2+1/2*d^2*ca*κ^3-d^2*sa^2*k^2-2*s^2*ca^2*k^2+sa^2*ca^2*k^2-s^2*ca*κ*k^2-1/2*sa^2*ca*κ*k^2+s^2*κ^2*k^2-1/2*d^2*ca*κ^2*D-1/4*ca^2*κ^3*D+1/2*s^2*ca*k^2*D+1/4*sa^2*ca*k^2*D+3/2*s^2*κ*k^2*D-1/4*sa^2*κ*k^2*D+1/4*ca^2*κ^2*D^2+1/4*ca*κ^3*D^2-1/4*sa^2*k^2*D^2-3/2*ca^3*κ^2*X+1/2*d^2*κ^3*X+1/2*ca^2*κ^3*X+ca^3*k^2*X+s^2*κ*k^2*X-1/2*sa^2*κ*k^2*X-ca^2*κ*k^2*X-1/4*d^2*κ^2*D*X+1/2*ca^2*κ^2*D*X+1/4*ca*κ^3*D*X+1/2*sa^2*k^2*D*X-1/4*ca*κ^2*D^2*X-1/4*κ^3*D^2*X-1/2*ca^2*κ^2*X^2-1/2*d^2*ca*κ^2+1/2*d^2*κ^3-1/2*ca^2*κ^3-s^2*ca*k^2+1/2*sa^2*ca*k^2+ca^3*k^2+s^2*κ*k^2-1/2*sa^2*κ*k^2-1/2*d^2*κ^2*D-3/4*ca^2*κ^2*D-1/4*ca*κ^3*D-3/2*s^2*k^2*D+5/4*sa^2*k^2*D+1/4*ca*κ^2*D^2+1/4*κ^3*D^2+1/2*d^2*κ^2*X+1/2*ca^2*κ^2*X+1/2*ca*κ^3*X-1/2*ca*κ^2*D*X-5/4*κ^3*D*X+1/4*κ^2*D^2*X-d^2*κ^2+ca^2*κ^2-1/2*ca*κ^3-s^2*k^2+1/2*sa^2*k^2+ca^2*k^2+1/4*ca*κ^2*D-1/4*κ^3*D-1/4*κ^2*D^2-1/2*κ^3*X-1/2*κ^2*D*X+1/2*ca*κ^2-1/2*κ^3+5/4*κ^2*D+1/2*κ^2) * ha1 +
        (-1/2*d^4*ca^5*X-1/2*d^2*ca^5*k^2*X-1/2*d^2*ca^4*k^2*X^2+1/2*d^4*ca^4*X-1/2*d^2*ca^4*k^2*X
          +1/2*d^4*ca^3*X+d^2*ca^5*X-1/2*d^2*ca^4*κ*X+1/2*d^2*ca^3*k^2*X+1/2*ca^5*k^2*X
            -1/4*d^2*ca^4*D*X-1/4*ca^4*κ*D^2*X+1/2*d^2*ca^2*k^2*X^2+1/2*ca^4*k^2*X^2
              -1/2*d^2*ca^4*κ-1/4*ca^4*κ*D^2-1/2*d^4*ca^2*X-d^2*ca^4*X-1/2*d^2*ca^3*κ*X
                +1/2*d^2*ca^2*k^2*X+1/2*ca^4*k^2*X+3/4*d^2*ca^3*D*X+1/4*ca^4*κ*D*X-1/4*ca^4*D^2*X
                  -1/4*ca^3*κ*D^2*X+1/2*ca^4*D*X^2+1/2*d^2*ca^4-1/2*d^2*ca^3*κ+1/2*d^2*ca^3*D
                    +1/4*ca^4*κ*D-1/4*ca^4*D^2-1/4*ca^3*κ*D^2-1/2*ca^5*X+1/2*ca^4*κ*X
                      -1/2*ca^3*k^2*X+3/2*ca^4*D*X+1/4*ca^3*κ*D*X-1/4*ca^3*D^2*X-1/2*ca^4*X^2
                        -1/2*ca^2*k^2*X^2+3/2*d^2*ca^3+1/2*ca^4*κ+1/2*d^2*ca^2*D+3/4*ca^4*D
                          +1/4*ca^3*κ*D-1/4*ca^3*D^2+3/2*d^2*ca^2*X-1/2*ca^4*X+1/2*d^2*ca*κ*X
                            +1/2*ca^3*κ*X-1/2*ca^2*k^2*X-3/4*d^2*ca*D*X-1/2*ca^3*D*X
                              +1/2*ca^2*D^2*X+1/4*ca*κ*D^2*X-1/2*ca^2*D*X^2+1/2*d^2*ca^2-ca^4
                                +1/2*d^2*ca*κ+1/2*ca^3*κ-1/2*d^2*ca*D-1/4*ca^3*D+1/2*ca^2*D^2
                                  +1/4*ca*κ*D^2-1/2*ca^3*X+1/2*d^2*κ*X+ca^2*κ*X+1/4*d^2*D*X
                                    -2*ca^2*D*X-1/4*ca*κ*D*X+1/4*ca*D^2*X+1/4*κ*D^2*X+1/2*ca^2*X^2
                                      -1/2*d^2*ca-3/2*ca^3+1/2*d^2*κ-1/2*d^2*D-2*ca^2*D-1/4*ca*κ*D
                                        +1/4*ca*D^2+1/4*κ*D^2-1/2*d^2*X+1/2*ca^2*X-1/2*ca*κ*X
                                          +1/2*ca*D*X-1/4*κ*D*X-1/4*D^2*X-d^2-1/2*ca^2-1/2*ca*κ
                                            +1/4*ca*D-1/4*κ*D-1/4*D^2-1/2*κ*X+1/2*D*X+1/2*ca-1/2*κ
                                              +5/4*D+1/2) * ha2 +
        (1/2*d^4*ca^3*X+1/2*d^2*ca^3*k^2*X+1/2*d^2*ca^2*k^2*X^2-1/2*d^4*ca^2*X+1/2*d^2*ca^2*k^2*X
          -d^2*ca^3*X+1/2*d^2*ca^2*κ*X-1/2*ca^3*k^2*X+1/4*d^2*ca^2*D*X+1/4*ca^2*κ*D^2*X
            -1/2*ca^2*k^2*X^2+1/2*d^2*ca^2*κ+1/4*ca^2*κ*D^2+d^2*ca^2*X+1/2*d^2*ca*κ*X
              -1/2*ca^2*k^2*X-3/4*d^2*ca*D*X-1/4*ca^2*κ*D*X+1/4*ca^2*D^2*X+1/4*ca*κ*D^2*X
                -1/2*ca^2*D*X^2-1/2*d^2*ca^2+1/2*d^2*ca*κ-1/2*d^2*ca*D-1/4*ca^2*κ*D+1/4*ca^2*D^2
                  +1/4*ca*κ*D^2+1/2*ca^3*X+1/2*d^2*κ*X-1/2*ca^2*κ*X+1/4*d^2*D*X-3/2*ca^2*D*X
                    -1/4*ca*κ*D*X+1/4*ca*D^2*X+1/4*κ*D^2*X+1/2*ca^2*X^2-1/2*d^2*ca+1/2*d^2*κ
                      -1/2*ca^2*κ-1/2*d^2*D-3/4*ca^2*D-1/4*ca*κ*D+1/4*ca*D^2+1/4*κ*D^2-1/2*d^2*X
                        +1/2*ca^2*X-1/2*ca*κ*X+1/2*ca*D*X-1/4*κ*D*X-1/4*D^2*X-d^2+ca^2-1/2*ca*κ
                          +1/4*ca*D-1/4*κ*D-1/4*D^2-1/2*κ*X+1/2*D*X+1/2*ca-1/2*κ+5/4*D+1/2) * E1 +
        (-1/2*d^4*ca^3*X+1/2*d^2*ca^3*k^2*X-1/2*d^2*ca^3*κ*D*X-1/2*d^2*ca^2*k^2*X^2+1/2*d^4*ca^2*X
          +1/2*d^2*ca^2*k^2*X+2*d^2*ca^3*X-1/2*d^2*ca^2*κ*X-1/2*ca^3*k^2*X-1/4*d^2*ca^2*D*X
            +1/2*ca^3*κ*D*X-1/4*ca^2*κ*D^2*X+1/2*ca^2*k^2*X^2+1/2*d^2*ca^2*κ+1/4*ca^2*κ*D^2
              -d^2*ca^2*X-1/2*d^2*ca*κ*X-1/2*ca^2*k^2*X+3/4*d^2*ca*D*X+3/2*d^2*κ*D*X
                +1/4*ca^2*κ*D*X-1/4*ca^2*D^2*X-1/4*ca*κ*D^2*X+1/2*ca^2*D*X^2-1/2*d^2*ca^2
                  +1/2*d^2*ca*κ-1/2*d^2*ca*D-1/4*ca^2*κ*D+1/4*ca^2*D^2+1/4*ca*κ*D^2-3/2*ca^3*X
                    +1/2*d^2*κ*X+1/2*ca^2*κ*X-1/4*d^2*D*X+1/2*ca^2*D*X+1/4*ca*κ*D*X-1/4*ca*D^2*X
                      -1/4*κ*D^2*X-1/2*ca^2*X^2-1/2*d^2*ca+1/2*d^2*κ-1/2*ca^2*κ-1/2*d^2*D
                        -3/4*ca^2*D-1/4*ca*κ*D+1/4*ca*D^2+1/4*κ*D^2+1/2*d^2*X+1/2*ca^2*X
                          +1/2*ca*κ*X-1/2*ca*D*X-5/4*κ*D*X+1/4*D^2*X-d^2+ca^2-1/2*ca*κ+1/4*ca*D
                            -1/4*κ*D-1/4*D^2-1/2*κ*X-1/2*D*X+1/2*ca-1/2*κ+5/4*D+1/2) * E2 +
        (-d^2*ca^3*κ-1/2*ca^3*κ^2*D-1/2*ca^3*κ*D*X-d^2*ca^3+d^2*ca^2*κ-ca^3*κ*D+d^2*ca^2+2*ca^3*κ
          -1/2*ca^2*κ*D+ca^3*X+3*ca^3-2*ca^2*κ-1/2*ca^2*D+1/2*ca*κ*D+3/2*κ^2*D+3/2*κ*D*X-2*ca^2
            -ca*κ+κ^2+1/2*ca*D+3/2*κ*D+κ*X-ca+κ-3/2*D-1) * hDdef +
        (d^4*ca^5*κ+1/2*d^2*ca^5*κ^2*D+d^2*ca^4*κ*k^2*X+d^4*ca^5-d^4*ca^4*κ-d^2*ca^5*k^2
          +d^2*ca^5*κ*D+d^2*ca^4*k^2*X-d^4*ca^3*κ-3*d^2*ca^5*κ+d^2*ca^4*κ^2+d^2*ca^4*k^2
            +1/2*d^2*ca^4*κ*D-1/2*d^2*ca^3*κ^2*D-1/2*ca^5*κ^2*D+1/2*ca^4*κ^2*D^2+d^2*ca^3*k^2*X
              -d^2*ca^2*κ*k^2*X-ca^4*κ*k^2*X-d^4*ca^3-4*d^2*ca^5+d^4*ca^2*κ+3*d^2*ca^4*κ
                +d^2*ca^3*κ^2+d^2*ca^3*k^2+ca^5*k^2+1/2*d^2*ca^4*D-3/2*d^2*ca^3*κ*D-ca^5*κ*D
                  -3/2*d^2*ca^2*κ^2*D-1/2*ca^4*κ^2*D+ca^4*κ*D^2+1/2*ca^3*κ^2*D^2-ca^4*k^2*X
                    -ca^4*κ*D*X+4*d^2*ca^3*κ+2*ca^5*κ-d^2*ca^2*κ^2-ca^4*κ^2-d^2*ca^2*k^2
                      -1/2*d^2*ca^3*D-3*d^2*ca^2*κ*D-5/2*ca^4*κ*D+1/2*ca^4*D^2+3/2*ca^3*κ*D^2
                        +ca^4*κ*X-ca^3*k^2*X+ca^2*κ*k^2*X-ca^4*D*X+2*d^2*ca^3+3*ca^5-3*d^2*ca^2*κ
                          -ca^4*κ-d^2*ca*κ^2-ca^3*κ^2-ca^3*k^2-d^2*ca^2*D-2*ca^4*D+3/2*d^2*ca*κ*D
                            +3/2*d^2*κ^2*D+3/2*ca^2*κ^2*D+1/2*ca^3*D^2-1/2*ca*κ^2*D^2+ca^4*X
                              -ca^3*D*X+ca^2*κ*D*X-d^2*ca^2+ca^4+d^2*ca*κ-3*ca^3*κ+1/2*d^2*ca*D
                                -2*ca^3*D-1/2*d^2*κ*D+5*ca^2*κ*D+1/2*ca*κ^2*D-1/2*κ^2*D^2+ca^3*X
                                  -ca^2*κ*X-d^2*ca+ca^3+d^2*κ+ca*κ^2-3/2*d^2*D+3*ca^2*D-3/2*ca*κ*D
                                    -κ^2*D-1/2*ca*D^2+1/2*κ*D^2-d^2-ca*κ+ca*D-κ*D+3/2*D^2+D) * hX

/-- DLMF 22.9.11: cyclic identity (two points, rank 3 (both signs)), at points where
the functions are finite. -/
@[dlmf 22.9.E11]
theorem jacobi_cyclic_d2_two {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg2 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 2 m 2 z k) k) :
    jacobiCyclicD 2 1 2 z k ^ 2 * jacobiCyclicD 2 2 2 z k + jacobiCyclicD 2 2 2 z k ^ 2 *
      jacobiCyclicD 2 1 2 z k = jacobiComodulusk k * (jacobiCyclicD 2 1 2 z k +
        jacobiCyclicD 2 2 2 z k) ∧
    jacobiCyclicD 2 1 2 z k ^ 2 * jacobiCyclicD 2 2 2 z k - jacobiCyclicD 2 2 2 z k ^ 2 *
      jacobiCyclicD 2 1 2 z k = jacobiComodulusk k * (jacobiCyclicD 2 1 2 z k -
        jacobiCyclicD 2 2 2 z k) := by
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
  constructor <;> field_simp <;> ring

/-- DLMF 22.9.12: cyclic identity (two points, rank 3), at points where the functions
are finite. -/
@[dlmf 22.9.E12]
theorem jacobi_cyclic_csd_two {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg2 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 2 m 2 z k) k) :
    jacobiCyclicC 2 1 2 z k * jacobiCyclicS 2 1 2 z k * jacobiCyclicD 2 2 2 z k +
      jacobiCyclicC 2 2 2 z k * jacobiCyclicS 2 2 2 z k * jacobiCyclicD 2 1 2 z k = 0 := by
  obtain ⟨a1, a2⟩ := p22R1_cyc2 k z
  have hn := hreg2 1
  have hn2 := hreg2 2
  rw [a1] at hn; rw [a2] at hn2
  have hd := jacobiPQk_ne_zero (by decide) (p22R1_reg_d_of_n_add_K hk hn2) hn
  obtain ⟨v1, v2, v3⟩ := p22R1_add_K_vals hk hn
  simp only [jacobiCyclicS, jacobiCyclicC, jacobiCyclicD, a1, a2, v1, v2, v3]
  change jacobiDnk z k ≠ 0 at hd
  field_simp; ring

/-- DLMF 22.9.13: cyclic identity (three points, rank 3), at points where the
functions are finite. -/
@[dlmf 22.9.E7, dlmf 22.9.E13]
theorem jacobi_cyclic_s4_triple {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg4 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 4 m 3 z k) k) :
    jacobiCyclicS 4 1 3 z k * jacobiCyclicS 4 2 3 z k * jacobiCyclicS 4 3 3 z k = -(1 /
      (1 - jacobiCyclicKappa k ^ 2)) * (jacobiCyclicS 4 1 3 z k + jacobiCyclicS 4 2 3 z k +
        jacobiCyclicS 4 3 3 z k) := by
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
  linear_combination (-s*d^2*ca^4*κ*k^2*X+s*ca^4*κ^3*k^2*X+2*s*d^2*ca^2*κ*k^2*X-s*ca^2*κ^3*k^2*X
      -s*ca^2*κ^4-s*d^2*κ*k^2*X+s*ca^2*κ^2) * h1 +
      (-1/2*s*ca^4*κ^2-1/2*s*ca^4*κ*X-s*ca^4*κ-s*ca^3*κ*D+1/2*s*ca^3*κ-s*ca^3*D+s*ca^2*κ*D
        +1/2*s*ca^3+1/2*s*ca^2*κ+s*ca^2*D+s*ca*κ*D+1/2*s*ca^2-1/2*s*ca*κ+1/2*s*κ^2+s*ca*D-s*κ*D
          +1/2*s*κ*X-1/2*s*ca+1/2*s*κ-s*D-1/2*s) * h2 +
      (s^3*d^2*ca^2*κ*k^2*X+s*c^2*d^2*ca^2*κ*k^2*X-s^3*ca^2*κ^3*k^2*X-s*c^2*ca^2*κ^3*k^2*X
        +1/2*s*d^2*sa^2*ca*κ*k^2*X-1/2*s*d^2*sa^2*ca*k^2*D*X+1/2*s*d^2*sa^2*ca*κ*k^2
          +1/2*s^3*ca^2*κ^2*k^2+1/2*s*d^2*ca^2*κ^3*X+1/4*s*d^2*sa^2*ca*k^2*X-s^3*d^2*κ*k^2*X
            -s*c^2*d^2*κ*k^2*X+1/2*s*d^2*sa^2*κ*k^2*X+1/2*s^3*ca^2*κ*k^2*X-s*d^2*ca^2*κ*k^2*X
              +s*ca^2*κ^3*k^2*X+1/2*s*d^2*sa^2*k^2*D*X+1/4*s*sa^2*ca*κ*k^2*D*X
                +1/2*s*d^2*sa^2*κ*k^2+s^3*ca^2*κ*k^2+s^3*ca*κ*k^2*D+1/4*s*sa^2*ca*κ*k^2*D
                  -1/2*s*d^2*ca*κ^3*X-1/4*s*d^2*sa^2*k^2*X-1/4*s*sa^2*ca*κ*k^2*X
                    +1/2*s*d^2*ca*κ^2*D*X-1/4*s*sa^2*ca*k^2*D*X+1/4*s*sa^2*κ*k^2*D*X
                      -1/2*s*sa^2*k^2*D^2*X+s*c^2*d^2*κ^2+1/2*s*d^2*ca*κ^3-1/2*s*d^2*sa^2*k^2
                        -1/2*s^3*ca*κ*k^2-1/4*s*sa^2*ca*κ*k^2+1/2*s^3*κ^2*k^2+s^3*ca*k^2*D
                          -3/4*s*sa^2*ca*k^2*D-s^3*κ*k^2*D+1/4*s*sa^2*κ*k^2*D-1/2*s*sa^2*k^2*D^2
                            -1/4*s*d^2*ca*κ^2*X-1/2*s*ca^2*κ^3*X+1/2*s^3*κ*k^2*X+s*d^2*κ*k^2*X
                              -1/4*s*sa^2*κ*k^2*X-1/2*s*d^2*κ^2*D*X-1/4*s*ca*κ^3*D*X
                                +1/4*s*sa^2*k^2*D*X+1/2*s*d^2*κ^3-1/2*s^3*ca*k^2+1/4*s*sa^2*ca*k^2
                                  +1/2*s^3*κ*k^2-1/4*s*sa^2*κ*k^2+1/4*s*ca*κ^3*D-s^3*k^2*D
                                    +3/4*s*sa^2*k^2*D+1/4*s*d^2*κ^2*X+1/4*s*ca*κ^3*X
                                      +1/4*s*ca*κ^2*D*X-1/4*s*κ^3*D*X+1/2*s*κ^2*D^2*X-s*c^2*d^2
                                        -1/2*s*d^2*κ^2-1/4*s*ca*κ^3-1/2*s^3*k^2+1/4*s*sa^2*k^2
                                          -3/4*s*ca*κ^2*D+1/4*s*κ^3*D-1/2*s*κ^2*D^2-1/4*s*κ^3*X
                                            -1/4*s*κ^2*D*X+1/4*s*ca*κ^2-1/4*s*κ^3+3/4*s*κ^2*D
                                              +1/4*s*κ^2) * ha1 +
      (-s*c^2*d^2*ca^2*κ*X+s*c^2*ca^2*κ^3*X-1/2*s*d^2*ca^3*κ*X+1/2*s*d^2*ca^3*D*X-1/2*s*d^2*ca^3*κ
        -1/4*s*d^2*ca^3*X+s*c^2*d^2*κ*X+1/2*s*d^2*ca^2*κ*X-s*ca^2*κ^3*X-1/2*s*d^2*ca^2*D*X
          -1/4*s*ca^3*κ*D*X-1/2*s*d^2*ca^2*κ-1/4*s*ca^3*κ*D+1/4*s*d^2*ca^2*X+1/2*s*d^2*ca*κ*X
            +1/4*s*ca^3*κ*X-1/2*s*d^2*ca*D*X+1/4*s*ca^3*D*X-1/4*s*ca^2*κ*D*X+1/2*s*ca^2*D^2*X
              +1/2*s*d^2*ca^2+1/2*s*d^2*ca*κ+1/4*s*ca^3*κ+3/4*s*ca^3*D-1/4*s*ca^2*κ*D
                +1/2*s*ca^2*D^2+1/4*s*d^2*ca*X-1/2*s*d^2*κ*X+1/4*s*ca^2*κ*X+1/2*s*d^2*D*X
                  -1/4*s*ca^2*D*X+1/4*s*ca*κ*D*X-1/4*s*ca^3+1/2*s*d^2*κ+1/4*s*ca^2*κ-3/4*s*ca^2*D
                    +1/4*s*ca*κ*D-1/4*s*d^2*X-1/4*s*ca*κ*X-1/4*s*ca*D*X+1/4*s*κ*D*X-1/2*s*D^2*X
                      -1/2*s*d^2-1/4*s*ca^2-1/4*s*ca*κ-3/4*s*ca*D+1/4*s*κ*D-1/2*s*D^2-1/4*s*κ*X
                        +1/4*s*D*X+1/4*s*ca-1/4*s*κ+3/4*s*D+1/4*s) * ha2 +
      (1/2*s*d^2*ca*κ*X-1/2*s*d^2*ca*D*X+1/2*s*d^2*ca*κ+1/4*s*d^2*ca*X+1/2*s*d^2*κ*X+1/2*s*d^2*D*X
        +1/4*s*ca*κ*D*X+1/2*s*d^2*κ+1/4*s*ca*κ*D-1/4*s*d^2*X-1/4*s*ca*κ*X-1/4*s*ca*D*X+1/4*s*κ*D*X
          -1/2*s*D^2*X-1/2*s*d^2-1/4*s*ca*κ-3/4*s*ca*D+1/4*s*κ*D-1/2*s*D^2-1/4*s*κ*X+1/4*s*D*X
            +1/4*s*ca-1/4*s*κ+3/4*s*D+1/4*s) * E1 +
      (1/2*s*d^2*ca^2*κ*X-1/2*s*d^2*ca*κ*X+1/2*s*d^2*ca*D*X+1/2*s*d^2*ca*κ-1/4*s*d^2*ca*X
        -1/2*s*ca^2*κ*X-1/2*s*d^2*D*X-1/4*s*ca*κ*D*X+1/2*s*d^2*κ+1/4*s*ca*κ*D+1/4*s*d^2*X
          +1/4*s*ca*κ*X+1/4*s*ca*D*X-1/4*s*κ*D*X+1/2*s*D^2*X-1/2*s*d^2-1/4*s*ca*κ-3/4*s*ca*D
            +1/4*s*κ*D-1/2*s*D^2-1/4*s*κ*X-1/4*s*D*X+1/4*s*ca-1/4*s*κ+3/4*s*D+1/4*s) * E2 +
      (s*d^2*ca^2*κ*X-s*ca^2*κ^3*X+1/2*s*ca^2*κ^2-s*d^2*κ*X+1/2*s*ca^2*κ*X+s*ca^2*κ+s*ca*κ*D
        -1/2*s*ca*κ+1/2*s*κ^2+s*ca*D-s*κ*D+1/2*s*κ*X-1/2*s*ca+1/2*s*κ-s*D-1/2*s) * hDdef +
      (s*c^2*d^2*ca^2*κ^2-1/2*s*d^2*ca^4*κ^2-s*c^2*ca^2*κ^4-s*d^2*ca^4*κ+s*d^2*ca^3*κ^2
        -s*d^2*ca^3*κ*D-s*c^2*d^2*ca^2+3/2*s*d^2*ca^3*κ-s*c^2*d^2*κ^2+s*c^2*ca^2*κ^2
          +1/2*s*ca^4*κ^2+s*ca^2*κ^4-s*d^2*ca^3*D+s*d^2*ca^2*κ*D+1/2*s*ca^3*κ^2*D+1/2*s*d^2*ca^3
            +1/2*s*d^2*ca^2*κ+s*ca^4*κ-s*d^2*ca*κ^2-1/2*s*ca^3*κ^2+s*d^2*ca^2*D+s*d^2*ca*κ*D
              -1/2*s*ca^2*κ^2*D-s*ca^2*κ*D^2+s*c^2*d^2-1/2*s*d^2*ca^2+1/2*s*d^2*ca*κ-1/2*s*ca^3*κ
                +1/2*s*d^2*κ^2-1/2*s*ca^2*κ^2+s*d^2*ca*D-1/2*s*ca^3*D-s*d^2*κ*D+3/2*s*ca^2*κ*D
                  -1/2*s*ca*κ^2*D-s*ca^2*D^2-1/2*s*d^2*ca+1/2*s*d^2*κ+1/2*s*ca*κ^2-s*d^2*D
                    +1/2*s*ca^2*D+s*ca*κ*D-1/2*s*κ^2*D-s*ca*D^2+s*κ*D^2-1/2*s*d^2-1/2*s*ca*κ
                      +1/2*s*ca*D-1/2*s*κ*D+1/2*s*D) * hX

end DLMF.JacobiElliptic
end
end
