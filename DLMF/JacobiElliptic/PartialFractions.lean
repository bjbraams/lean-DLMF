/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.P3jEisenstein

/-!
# Doubly infinite partial fractions: Eisenstein series (DLMF §22.12)

With `τ = iK'(k)/K(k)` (DLMF 22.12.1, the project's `jacobiTauk`), DLMF 22.12.2–22.12.13
expand `pq(2Kt, k)` as series over `n ∈ ℤ` of `π/sin(π(t + a - (n + b)τ))` or
`π/tan(π(t + a - (n + b)τ))`, each term being itself the conditionally convergent partial
fraction series over `m ∈ ℤ`. Each DLMF line has two equalities; both are acquired:

* the outer series: `HasSum` over `ℤ` for the `sin` forms (they converge absolutely, the terms
  decay like `|q|^{|n|}`); symmetric partial sums `∑_{n=-N}^{N}`, exactly as printed, for the
  `tan` forms (22.12.4, 22.12.7, 22.12.10, 22.12.13), whose terms tend to `∓iπ(-1)ⁿ`;
* for each `n`, the inner series over `m` in symmetric partial sums `∑_{m=-M}^{M}`, which is how
  DLMF writes the limits and the only sense in which the `(−1)^m/(w - m)` and `1/(w - m)` series
  converge.

`t` is assumed not to be a pole (`t + a - m - (n + b)τ ≠ 0` for all `m, n`); `k` ranges over
`jacobiModulusDomain`, `K = K(k)`, `k' = √(1 - k²)`. The eight `sin` forms (22.12.2, 3, 5, 6, 8,
9, 11, 12) are proved: `2K ns(2Kt)` and `2K ds(2Kt)` are identified with the Eisenstein-type series
`∑ₙ (±1)ⁿ π/sin(π(t - nτ))` by a Liouville argument (`p3j_ps_eq_G` in `P3jEisenstein`), the other
six follow by the half-period shifts of Table 22.4.3, and the inner series is the alternating
cotangent expansion `p3j_tendsto_alt`. The four `tan` forms (22.12.4, 7, 10, 13) remain admitted;
they were checked numerically (mpmath, 2026-10-25) also for complex `k`.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.JacobiElliptic

variable {k : ℂ}

/-- DLMF 22.12.1: `τ = iK'(k)/K(k)`; this is the definition of `jacobiTauk`. -/
@[dlmf 22.12.E1]
theorem jacobiTauk_eq (k : ℂ) : jacobiTauk k = I * compEllIntKpk k / compEllIntKk k := rfl

/-- `2K(t + a) = (2Kt + c) + b` bookkeeping: `Kτ = iK'`. -/
lemma p3j_K_tau {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    compEllIntKk k * jacobiTauk k = I * compEllIntKpk k := by
  have := p22R1_compEllIntKk_ne_zero hk
  rw [jacobiTauk]; field_simp

/-- DLMF 22.12.2: the Eisenstein-type expansion of `sn(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (the outer series converges absolutely (`HasSum` over
`ℤ`), each inner series in symmetric partial sums). -/
@[dlmf 22.12.E2 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiSnk_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, t - m - (n + 1 / 2) * jacobiTauk k ≠ 0) :
    HasSum (fun n : ℤ => π / sin (π * (t - (n + 1 / 2) * jacobiTauk k))) (2 * compEllIntKk k * k *
        jacobiSnk (2 * compEllIntKk k * t) k) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1) ^ m / (t - (n + 1 / 2) *
          jacobiTauk k - m))
        atTop (𝓝 (π / sin (π * (t - (n + 1 / 2) * jacobiTauk k)))) := by
  have hK := p3j_K_tau hk
  refine ⟨?_, fun n => p3j_tendsto_alt fun m => by convert ht n m using 1; ring⟩
  have h := p3j_hasSum_ns hk (t := t - jacobiTauk k / 2)
    (p3j_not_latt fun m n => by convert ht n m using 1; ring)
  convert h using 1
  · funext n; congr 2; ring
  · have hs := (jacobiSnk_shift hk (2 * compEllIntKk k * t - 2 * (I * compEllIntKpk k))).2.2.2.2.2
    rw [sub_add_cancel] at hs
    rw [show 2 * compEllIntKk k * (t - jacobiTauk k / 2) = (2 * compEllIntKk k * t -
      2 * (I * compEllIntKpk k)) + I * compEllIntKpk k by linear_combination -hK,
      (jacobiNsk_shift hk _).2.2.1, ← hs]; ring

/-- DLMF 22.12.3: the Eisenstein-type expansion of `cn(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (the outer series converges absolutely (`HasSum` over
`ℤ`), each inner series in symmetric partial sums). -/
@[dlmf 22.12.E3 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiCnk_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, t - m - (n + 1 / 2) * jacobiTauk k ≠ 0) :
    HasSum (fun n : ℤ => (-1) ^ n * π / sin (π * (t - (n + 1 / 2) * jacobiTauk k))) (2 * I *
        compEllIntKk k * k * jacobiCnk (2 * compEllIntKk k * t) k) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1) ^ (m + n) / (t - (n + 1 /
          2) * jacobiTauk k - m))
        atTop (𝓝 ((-1) ^ n * π / sin (π * (t - (n + 1 / 2) * jacobiTauk k)))) := by
  have hK := p3j_K_tau hk
  refine ⟨?_, fun n => p3j_tendsto_alt' (fun m => by convert ht n m using 1; ring) n⟩
  have h := p3j_hasSum_ds hk (t := t - jacobiTauk k / 2)
    (p3j_not_latt fun m n => by convert ht n m using 1; ring)
  convert h using 1
  · funext n; congr 3; ring
  · have hs := (jacobiCnk_shift hk (2 * compEllIntKk k * t - 2 * (I * compEllIntKpk k))).2.2.2.2.2
    rw [sub_add_cancel] at hs
    rw [show 2 * compEllIntKk k * (t - jacobiTauk k / 2) = (2 * compEllIntKk k * t -
      2 * (I * compEllIntKpk k)) + I * compEllIntKpk k by linear_combination -hK,
      (jacobiDsk_shift hk _).2.2.1, hs]; ring

/-- DLMF 22.12.4: the Eisenstein-type expansion of `dn(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (both limits are symmetric partial sums, as printed).
Admitted. -/
@[dlmf 22.12.E4 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiDnk_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, t - m - (n + 1 / 2) * jacobiTauk k ≠ 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (-1) ^ n * π / tan (π * (t - (n + 1 / 2) *
        jacobiTauk k))) atTop
        (𝓝 (2 * I * compEllIntKk k * jacobiDnk (2 * compEllIntKk k * t) k)) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, 1 / (t - (n + 1 / 2) *
          jacobiTauk k - m))
        atTop (𝓝 (π / tan (π * (t - (n + 1 / 2) * jacobiTauk k)))) := by
  sorry

/-- DLMF 22.12.5: the Eisenstein-type expansion of `cd(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (the outer series converges absolutely (`HasSum` over
`ℤ`), each inner series in symmetric partial sums). -/
@[dlmf 22.12.E5 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiCdk_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, (t + 1 / 2) - m - (n + 1 / 2) * jacobiTauk k ≠ 0) :
    HasSum (fun n : ℤ => π / sin (π * ((t + 1 / 2) - (n + 1 / 2) * jacobiTauk k))) (2 *
        compEllIntKk k * k * jacobiCdk (2 * compEllIntKk k * t) k) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1) ^ m / ((t + 1 / 2) - (n +
          1 / 2) * jacobiTauk k - m))
        atTop (𝓝 (π / sin (π * ((t + 1 / 2) - (n + 1 / 2) * jacobiTauk k)))) := by
  have hK := p3j_K_tau hk
  refine ⟨?_, fun n => p3j_tendsto_alt fun m => by convert ht n m using 1; ring⟩
  have h := p3j_hasSum_ns hk (t := t + 1 / 2 - jacobiTauk k / 2)
    (p3j_not_latt fun m n => by convert ht n m using 1; ring)
  convert h using 1
  · funext n; congr 2; ring
  · have hs := (jacobiCdk_shift hk (2 * compEllIntKk k * t - 2 * (I * compEllIntKpk k))).2.2.2.2.2
    rw [sub_add_cancel] at hs
    rw [show 2 * compEllIntKk k * (t + 1 / 2 - jacobiTauk k / 2) = (2 * compEllIntKk k * t -
      2 * (I * compEllIntKpk k)) + compEllIntKk k + I * compEllIntKpk k by
      linear_combination -hK, (jacobiNsk_shift hk _).2.1, ← hs]; ring

/-- DLMF 22.12.6: the Eisenstein-type expansion of `sd(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (the outer series converges absolutely (`HasSum` over
`ℤ`), each inner series in symmetric partial sums). -/
@[dlmf 22.12.E6 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiSdk_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, (t + 1 / 2) - m - (n + 1 / 2) * jacobiTauk k ≠ 0) :
    HasSum (fun n : ℤ => (-1) ^ n * π / sin (π * ((t + 1 / 2) - (n + 1 / 2) * jacobiTauk k))) (-2 *
        I * compEllIntKk k * k * jacobiComodulusk k * jacobiSdk (2 * compEllIntKk k * t) k) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1) ^ (m + n) / ((t + 1 / 2) -
          (n + 1 / 2) * jacobiTauk k - m))
        atTop (𝓝 ((-1) ^ n * π / sin (π * ((t + 1 / 2) - (n + 1 / 2) * jacobiTauk k)))) := by
  have hK := p3j_K_tau hk
  refine ⟨?_, fun n => p3j_tendsto_alt' (fun m => by convert ht n m using 1; ring) n⟩
  have h := p3j_hasSum_ds hk (t := t + 1 / 2 - jacobiTauk k / 2)
    (p3j_not_latt fun m n => by convert ht n m using 1; ring)
  convert h using 1
  · funext n; congr 3; ring
  · have hs := (jacobiSdk_shift hk (2 * compEllIntKk k * t - 2 * (I * compEllIntKpk k))).2.2.2.2.2
    rw [sub_add_cancel] at hs
    rw [show 2 * compEllIntKk k * (t + 1 / 2 - jacobiTauk k / 2) = (2 * compEllIntKk k * t -
      2 * (I * compEllIntKpk k)) + compEllIntKk k + I * compEllIntKpk k by
      linear_combination -hK, (jacobiDsk_shift hk _).2.1, hs]; ring

/-- DLMF 22.12.7: the Eisenstein-type expansion of `nd(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (both limits are symmetric partial sums, as printed).
Admitted. -/
@[dlmf 22.12.E7 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiNdk_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, (t + 1 / 2) - m - (n + 1 / 2) * jacobiTauk k ≠ 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (-1) ^ n * π / tan (π * ((t + 1 / 2) -
        (n + 1 / 2) * jacobiTauk k))) atTop
        (𝓝 (2 * I * compEllIntKk k * jacobiComodulusk k * jacobiNdk (2 * compEllIntKk k * t) k)) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, 1 / ((t + 1 / 2) - (n + 1 /
          2) * jacobiTauk k - m))
        atTop (𝓝 (π / tan (π * ((t + 1 / 2) - (n + 1 / 2) * jacobiTauk k)))) := by
  sorry

/-- DLMF 22.12.8: the Eisenstein-type expansion of `dc(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (the outer series converges absolutely (`HasSum` over
`ℤ`), each inner series in symmetric partial sums). -/
@[dlmf 22.12.E8 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiDck_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, (t + 1 / 2) - m - n * jacobiTauk k ≠ 0) :
    HasSum (fun n : ℤ => π / sin (π * ((t + 1 / 2) - n * jacobiTauk k))) (2 * compEllIntKk k *
        jacobiDck (2 * compEllIntKk k * t) k) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1) ^ m / ((t + 1 / 2) - n *
          jacobiTauk k - m))
        atTop (𝓝 (π / sin (π * ((t + 1 / 2) - n * jacobiTauk k)))) := by
  refine ⟨?_, fun n => p3j_tendsto_alt fun m => by convert ht n m using 1; ring⟩
  have h := p3j_hasSum_ns hk (t := t + 1 / 2)
    (p3j_not_latt fun m n => ht n m)
  convert h using 1
  rw [show 2 * compEllIntKk k * (t + 1 / 2) = 2 * compEllIntKk k * t + compEllIntKk k by ring,
    (jacobiNsk_shift hk _).1]

/-- DLMF 22.12.9: the Eisenstein-type expansion of `nc(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (the outer series converges absolutely (`HasSum` over
`ℤ`), each inner series in symmetric partial sums). -/
@[dlmf 22.12.E9 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiNck_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, (t + 1 / 2) - m - n * jacobiTauk k ≠ 0) :
    HasSum (fun n : ℤ => (-1) ^ n * π / sin (π * ((t + 1 / 2) - n * jacobiTauk k))) (2 *
        compEllIntKk k * jacobiComodulusk k * jacobiNck (2 * compEllIntKk k * t) k) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1) ^ (m + n) / ((t + 1 / 2) -
          n * jacobiTauk k - m))
        atTop (𝓝 ((-1) ^ n * π / sin (π * ((t + 1 / 2) - n * jacobiTauk k)))) := by
  refine ⟨?_, fun n => p3j_tendsto_alt' (fun m => by convert ht n m using 1; ring) n⟩
  have h := p3j_hasSum_ds hk (t := t + 1 / 2)
    (p3j_not_latt fun m n => ht n m)
  convert h using 1
  rw [show 2 * compEllIntKk k * (t + 1 / 2) = 2 * compEllIntKk k * t + compEllIntKk k by ring,
    (jacobiDsk_shift hk _).1]; ring

/-- DLMF 22.12.10: the Eisenstein-type expansion of `sc(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (both limits are symmetric partial sums, as printed).
Admitted. -/
@[dlmf 22.12.E10 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiSck_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, (t + 1 / 2) - m - n * jacobiTauk k ≠ 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (-1) ^ n * π / tan (π * ((t + 1 / 2) - n *
        jacobiTauk k))) atTop
        (𝓝 (-2 * compEllIntKk k * jacobiComodulusk k * jacobiSck (2 * compEllIntKk k * t) k)) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, 1 / ((t + 1 / 2) - n *
          jacobiTauk k - m))
        atTop (𝓝 (π / tan (π * ((t + 1 / 2) - n * jacobiTauk k)))) := by
  sorry

/-- DLMF 22.12.11: the Eisenstein-type expansion of `ns(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (the outer series converges absolutely (`HasSum` over
`ℤ`), each inner series in symmetric partial sums). -/
@[dlmf 22.12.E11 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiNsk_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, t - m - n * jacobiTauk k ≠ 0) :
    HasSum (fun n : ℤ => π / sin (π * (t - n * jacobiTauk k))) (2 * compEllIntKk k * jacobiNsk (2 *
        compEllIntKk k * t) k) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1) ^ m / (t - n *
          jacobiTauk k - m))
        atTop (𝓝 (π / sin (π * (t - n * jacobiTauk k)))) := by
  exact ⟨p3j_hasSum_ns hk (p3j_not_latt fun m n => ht n m),
    fun n => p3j_tendsto_alt fun m => by convert ht n m using 1; ring⟩

/-- DLMF 22.12.12: the Eisenstein-type expansion of `ds(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (the outer series converges absolutely (`HasSum` over
`ℤ`), each inner series in symmetric partial sums). -/
@[dlmf 22.12.E12 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiDsk_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, t - m - n * jacobiTauk k ≠ 0) :
    HasSum (fun n : ℤ => (-1) ^ n * π / sin (π * (t - n * jacobiTauk k))) (2 * compEllIntKk k *
        jacobiDsk (2 * compEllIntKk k * t) k) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1) ^ (m + n) / (t - n *
          jacobiTauk k - m))
        atTop (𝓝 ((-1) ^ n * π / sin (π * (t - n * jacobiTauk k)))) := by
  exact ⟨p3j_hasSum_ds hk (p3j_not_latt fun m n => ht n m),
    fun n => p3j_tendsto_alt' (fun m => by convert ht n m using 1; ring) n⟩

/-- DLMF 22.12.13: the Eisenstein-type expansion of `cs(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (both limits are symmetric partial sums, as printed).
Admitted. -/
@[dlmf 22.12.E13 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiCsk_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, t - m - n * jacobiTauk k ≠ 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (-1) ^ n * π / tan (π * (t - n *
        jacobiTauk k))) atTop
        (𝓝 (2 * compEllIntKk k * jacobiCsk (2 * compEllIntKk k * t) k)) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, 1 / (t - n * jacobiTauk k - m))
        atTop (𝓝 (π / tan (π * (t - n * jacobiTauk k)))) := by
  sorry


end DLMF.JacobiElliptic
