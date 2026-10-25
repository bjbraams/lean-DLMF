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
`κ = dn(2K/3, k)` (22.9.7) are definitions; the cyclic identities 22.9.8–22.9.23 are admitted
(stated at points where all functions involved are finite).

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

/-- **Admitted.** DLMF 22.9.8: cyclic identity (three points, rank 2), at points where the functions
are finite. -/
@[dlmf 22.9.E7, dlmf 22.9.E8]
theorem jacobi_cyclic_s4_pairs {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg4 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 4 m 3 z k) k) :
    jacobiCyclicS 4 1 3 z k * jacobiCyclicS 4 2 3 z k + jacobiCyclicS 4 2 3 z k *
      jacobiCyclicS 4 3 3 z k + jacobiCyclicS 4 3 3 z k * jacobiCyclicS 4 1 3 z k =
        (jacobiCyclicKappa k ^ 2 - 1) / k ^ 2 := by
  sorry

/-- **Admitted.** DLMF 22.9.9: cyclic identity (three points, rank 2), at points where the functions
are finite. -/
@[dlmf 22.9.E7, dlmf 22.9.E9]
theorem jacobi_cyclic_c4_pairs {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg4 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 4 m 3 z k) k) :
    jacobiCyclicC 4 1 3 z k * jacobiCyclicC 4 2 3 z k + jacobiCyclicC 4 2 3 z k *
      jacobiCyclicC 4 3 3 z k + jacobiCyclicC 4 3 3 z k * jacobiCyclicC 4 1 3 z k =
        -(jacobiCyclicKappa k * (jacobiCyclicKappa k + 2)) / (1 + jacobiCyclicKappa k) ^ 2 := by
  sorry

/-- **Admitted.** DLMF 22.9.10: cyclic identity (three points, rank 2), at points where the
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
  sorry

/-- **Admitted.** DLMF 22.9.11: cyclic identity (two points, rank 3 (both signs)), at points where
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
  sorry

/-- **Admitted.** DLMF 22.9.12: cyclic identity (two points, rank 3), at points where the functions
are finite. -/
@[dlmf 22.9.E12]
theorem jacobi_cyclic_csd_two {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg2 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 2 m 2 z k) k) :
    jacobiCyclicC 2 1 2 z k * jacobiCyclicS 2 1 2 z k * jacobiCyclicD 2 2 2 z k +
      jacobiCyclicC 2 2 2 z k * jacobiCyclicS 2 2 2 z k * jacobiCyclicD 2 1 2 z k = 0 := by
  sorry

/-- **Admitted.** DLMF 22.9.13: cyclic identity (three points, rank 3), at points where the
functions are finite. -/
@[dlmf 22.9.E7, dlmf 22.9.E13]
theorem jacobi_cyclic_s4_triple {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg4 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 4 m 3 z k) k) :
    jacobiCyclicS 4 1 3 z k * jacobiCyclicS 4 2 3 z k * jacobiCyclicS 4 3 3 z k = -(1 /
      (1 - jacobiCyclicKappa k ^ 2)) * (jacobiCyclicS 4 1 3 z k + jacobiCyclicS 4 2 3 z k +
        jacobiCyclicS 4 3 3 z k) := by
  sorry

/-- **Admitted.** DLMF 22.9.14: cyclic identity (three points, rank 3), at points where the
functions are finite. -/
@[dlmf 22.9.E7, dlmf 22.9.E14]
theorem jacobi_cyclic_c4_triple {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg4 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 4 m 3 z k) k) :
    jacobiCyclicC 4 1 3 z k * jacobiCyclicC 4 2 3 z k * jacobiCyclicC 4 3 3 z k =
      jacobiCyclicKappa k ^ 2 / (1 - jacobiCyclicKappa k ^ 2) * (jacobiCyclicC 4 1 3 z k +
        jacobiCyclicC 4 2 3 z k + jacobiCyclicC 4 3 3 z k) := by
  sorry

/-- **Admitted.** DLMF 22.9.15: cyclic identity (three points, rank 3), at points where the
functions are finite. -/
@[dlmf 22.9.E7, dlmf 22.9.E15]
theorem jacobi_cyclic_d2_triple {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg2 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 2 m 3 z k) k) :
    jacobiCyclicD 2 1 3 z k * jacobiCyclicD 2 2 3 z k * jacobiCyclicD 2 3 3 z k =
      (jacobiCyclicKappa k ^ 2 + k ^ 2 - 1) / (1 - jacobiCyclicKappa k ^ 2) *
        (jacobiCyclicD 2 1 3 z k + jacobiCyclicD 2 2 3 z k + jacobiCyclicD 2 3 3 z k) := by
  sorry

/-- **Admitted.** DLMF 22.9.16: cyclic identity (three points, rank 3), at points where the
functions are finite. -/
@[dlmf 22.9.E7, dlmf 22.9.E16]
theorem jacobi_cyclic_scc_triple {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg4 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 4 m 3 z k) k) :
    jacobiCyclicS 4 1 3 z k * jacobiCyclicC 4 2 3 z k * jacobiCyclicC 4 3 3 z k +
      jacobiCyclicS 4 2 3 z k * jacobiCyclicC 4 3 3 z k * jacobiCyclicC 4 1 3 z k +
        jacobiCyclicS 4 3 3 z k * jacobiCyclicC 4 1 3 z k * jacobiCyclicC 4 2 3 z k =
          jacobiCyclicKappa k * (jacobiCyclicKappa k + 2) / (1 - jacobiCyclicKappa k ^ 2) *
            (jacobiCyclicS 4 1 3 z k + jacobiCyclicS 4 2 3 z k + jacobiCyclicS 4 3 3 z k) := by
  sorry

/-- **Admitted.** DLMF 22.9.17: cyclic identity (four points, rank 3 (both signs)), at points where
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
  sorry

/-- **Admitted.** DLMF 22.9.18: cyclic identity (four points, rank 3 (both signs)), at points where
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
  sorry

/-- **Admitted.** DLMF 22.9.19: cyclic identity (four points, rank 3), at points where the functions
are finite. -/
@[dlmf 22.9.E19]
theorem jacobi_cyclic_csd_four {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg2 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 2 m 4 z k) k) :
    jacobiCyclicC 2 1 4 z k * jacobiCyclicS 2 1 4 z k * jacobiCyclicD 2 3 4 z k +
      jacobiCyclicC 2 3 4 z k * jacobiCyclicS 2 3 4 z k * jacobiCyclicD 2 1 4 z k = 0 ∧
    jacobiCyclicC 2 2 4 z k * jacobiCyclicS 2 2 4 z k * jacobiCyclicD 2 4 4 z k +
      jacobiCyclicC 2 4 4 z k * jacobiCyclicS 2 4 4 z k * jacobiCyclicD 2 2 4 z k = 0 := by
  sorry

/-- **Admitted.** DLMF 22.9.20: cyclic identity (two points, rank 4 (both signs)), at points where
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
  sorry

/-- **Admitted.** DLMF 22.9.21: cyclic identity (two points, rank 4), at points where the functions
are finite. -/
@[dlmf 22.9.E21]
theorem jacobi_cyclic_cscs_two {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ)
    (hreg2 : ∀ m : ℕ, jacobiRegulark .n (jacobiCyclicArg 2 m 2 z k) k) :
    k ^ 2 * jacobiCyclicC 2 1 2 z k * jacobiCyclicS 2 1 2 z k * jacobiCyclicC 2 2 2 z k *
      jacobiCyclicS 2 2 2 z k = jacobiComodulusk k * (1 - jacobiCyclicS 2 1 2 z k ^ 2 -
        jacobiCyclicS 2 2 2 z k ^ 2) := by
  sorry

/-- **Admitted.** DLMF 22.9.22: cyclic identity (three points, rank 4), at points where the
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
  sorry

/-- **Admitted.** DLMF 22.9.23: cyclic identity (three points, rank 4; corrected), at points where
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
  sorry

end DLMF.JacobiElliptic
