/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.ElementaryIdentities

/-!
# Jacobian elliptic functions: cyclic identities (DLMF §22.9)

The notation 22.9.1–22.9.6 (`s_{m,p}^{(N)} = sn(z + N p⁻¹(m - 1)K, k)` for `N = 2, 4`) and
`κ = dn(2K/3, k)` (22.9.7) are definitions; the cyclic identities 22.9.8–22.9.23 are proved
(stated at points where all functions involved are finite). For the shifts by `K` and `K/2`
(`p = 2, 4`) they follow from Table 22.4.3; for `p = 3` the points `z + 2K/3`, `z + 4K/3` are
expanded by the addition theorem, and the identities reduce to polynomial identities modulo
`sn² + cn² = 1`, `k² sn² + dn² = 1` and the duplication relations at `2K/3`
(`sn(4K/3) = sn(2K/3)`, `cn(4K/3) = -cn(2K/3)`), with certificates computed by Singular.

**Correction.** In 22.9.23 the right-hand side repeats `s_{2,3}^{(4)} d_{2,3}^{(4)}`; the
numerically correct last summand is `s_{3,3}^{(4)} d_{3,3}^{(4)}` (e.g. `k = 0.6`,
`z = 0.37 + 0.21i`: printed right side `≈ 4.208 - 0.036i`, left side `≈ 0.552 + 0.183i`,
corrected right side equal to the left side).
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

lemma p22R1_cyc2 (k z : ℂ) : jacobiCyclicArg 2 1 2 z k = z ∧
    jacobiCyclicArg 2 2 2 z k = z + compEllIntKk k := by
  constructor <;> (simp only [jacobiCyclicArg]; push_cast; ring)

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

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
/-- DLMF 22.9.22: cyclic identity (three points, rank 4), at points where the
functions are finite. -/
@[dlmf 22.9.E7, dlmf 22.9.E22]
theorem jacobi_cyclic_scdd_three {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg2 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 2 m 3 z k) k) :
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
    (hreg4 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 4 m 3 z k) k) :
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
