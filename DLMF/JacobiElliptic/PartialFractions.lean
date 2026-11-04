/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.EisensteinCotSeries

/-!
# Doubly infinite partial fractions: Eisenstein series (DLMF §22.12)

With `τ = iK'(k)/K(k)` (DLMF 22.12.1, the project's `jacobiTau`), DLMF 22.12.2–22.12.13
expand `pq(2Kt, k)` as series over `n ∈ ℤ` of `π/sin(π(t + a - (n + b)τ))` or
`π/tan(π(t + a - (n + b)τ))`, each term being itself the conditionally convergent partial
fraction series over `m ∈ ℤ`.

## Main results

* `jacobiTau_eq`: DLMF 22.12.1.
* `jacobiSn_partialFractions`, `jacobiCn_partialFractions`, `jacobiDn_partialFractions`:
  DLMF 22.12.2–22.12.4.
* `jacobiCd_partialFractions`, `jacobiSd_partialFractions`, `jacobiNd_partialFractions`:
  DLMF 22.12.5–22.12.7.
* `jacobiDc_partialFractions`, `jacobiNc_partialFractions`, `jacobiSc_partialFractions`:
  DLMF 22.12.8–22.12.10.
* `jacobiNs_partialFractions`, `jacobiDs_partialFractions`, `jacobiCs_partialFractions`:
  DLMF 22.12.11–22.12.13.

## Implementation notes

Each DLMF line has two equalities, and both are stated:

* the outer series: `HasSum` over `ℤ` for the `sin` forms (they converge absolutely, the terms
  decay like `|q|^{|n|}`); symmetric partial sums `∑_{n=-N}^{N}`, exactly as printed, for the
  `tan` forms (22.12.4, 22.12.7, 22.12.10, 22.12.13), whose terms tend to `∓iπ(-1)ⁿ`;
* for each `n`, the inner series over `m` in symmetric partial sums `∑_{m=-M}^{M}`, which is how
  DLMF writes the limits and the only sense in which the `(−1)^m/(w - m)` and `1/(w - m)`
  series converge.

`t` is assumed not to be a pole (`t + a - m - (n + b)τ ≠ 0` for all `m, n`); `k` ranges over
`jacobiModulusDomain`, `K = K(k)`, `k' = √(1 - k²)`. For the eight `sin` forms (22.12.2, 3, 5, 6,
8, 9, 11, 12), `2K ns(2Kt)` and `2K ds(2Kt)` are identified with the Eisenstein-type series
`∑ₙ (±1)ⁿ π/sin(π(t - nτ))` by a Liouville argument (`jacobiPQ_s_eq_eisensteinSinSeries` in
`DLMF.JacobiElliptic.EisensteinSeries`), the other six follow by the half-period shifts of
Table 22.4.3, and the inner series is the alternating cotangent expansion
`tendsto_sum_Icc_neg_one_zpow_div_sub`. For the four `tan` forms (22.12.4, 7, 10, 13),
`2K cs(2Kt)` is identified with the regularized cotangent series
`∑ₙ (-1)ⁿ π cot(π(t - nτ))` (`jacobiCs_eq_eisensteinCotSeries` in
`DLMF.JacobiElliptic.EisensteinCotSeries`), whose regularizing constants cancel in symmetric
partial sums; the inner series is the cotangent expansion `tendsto_sum_Icc_one_div_sub`.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.JacobiElliptic

open DLMF.EllipticIntegrals (completeEllipticK completeEllipticKPrime)

variable {k : ℂ}

/-- DLMF 22.12.1: `τ = iK'(k)/K(k)`; this is the definition of `jacobiTau`. -/
@[dlmf 22.12.E1]
theorem jacobiTau_eq (k : ℂ) : jacobiTau k = I * completeEllipticKPrime k /
    completeEllipticK k := rfl

/-- `2K(t + a) = (2Kt + c) + b` bookkeeping: `Kτ = iK'`. -/
private lemma completeEllipticK_mul_jacobiTau {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    completeEllipticK k * jacobiTau k = I * completeEllipticKPrime k := by
  have := completeEllipticK_ne_zero_of_mem_jacobiModulusDomain hk
  rw [jacobiTau]; field_simp

/-- DLMF 22.12.2: the Eisenstein-type expansion of `sn(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (the outer series converges absolutely (`HasSum` over
`ℤ`), each inner series in symmetric partial sums). -/
@[dlmf 22.12.E2 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiSn_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, t - m - (n + 1 / 2) * jacobiTau k ≠ 0) :
    HasSum (fun n : ℤ => π / sin (π * (t - (n + 1 / 2) * jacobiTau k)))
        (2 * completeEllipticK k * k *
        jacobiSn (2 * completeEllipticK k * t) k) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1) ^ m / (t - (n + 1 / 2) *
          jacobiTau k - m))
        atTop (𝓝 (π / sin (π * (t - (n + 1 / 2) * jacobiTau k)))) := by
  have hK := completeEllipticK_mul_jacobiTau hk
  refine ⟨?_, fun n => tendsto_sum_Icc_neg_one_zpow_div_sub fun m =>
      by convert ht n m using 1; ring⟩
  have h := hasSum_pi_div_sin_jacobiNs hk (t := t - jacobiTau k / 2)
    (not_mem_eisensteinSinLattice fun m n => by convert ht n m using 1; ring)
  convert h using 1
  · funext n; congr 2; ring
  · have hs := (jacobiSn_shift hk
        (2 * completeEllipticK k * t - 2 * (I * completeEllipticKPrime k))).2.2.2.2.2
    rw [sub_add_cancel] at hs
    rw [show 2 * completeEllipticK k * (t - jacobiTau k / 2) = (2 * completeEllipticK k * t -
      2 * (I * completeEllipticKPrime k)) + I * completeEllipticKPrime k by linear_combination -hK,
      (jacobiNs_shift hk _).2.2.1, ← hs]; ring

/-- DLMF 22.12.3: the Eisenstein-type expansion of `cn(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (the outer series converges absolutely (`HasSum` over
`ℤ`), each inner series in symmetric partial sums). -/
@[dlmf 22.12.E3 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiCn_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, t - m - (n + 1 / 2) * jacobiTau k ≠ 0) :
    HasSum (fun n : ℤ => (-1) ^ n * π / sin (π * (t - (n + 1 / 2) * jacobiTau k))) (2 * I *
        completeEllipticK k * k * jacobiCn (2 * completeEllipticK k * t) k) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1) ^ (m + n) / (t - (n + 1 /
          2) * jacobiTau k - m))
        atTop (𝓝 ((-1) ^ n * π / sin (π * (t - (n + 1 / 2) * jacobiTau k)))) := by
  have hK := completeEllipticK_mul_jacobiTau hk
  refine ⟨?_, fun n =>
      tendsto_sum_Icc_neg_one_zpow_add_div_sub (fun m => by convert ht n m using 1; ring) n⟩
  have h := hasSum_neg_one_zpow_pi_div_sin_jacobiDs hk (t := t - jacobiTau k / 2)
    (not_mem_eisensteinSinLattice fun m n => by convert ht n m using 1; ring)
  convert h using 1
  · funext n; congr 3; ring
  · have hs := (jacobiCn_shift hk
        (2 * completeEllipticK k * t - 2 * (I * completeEllipticKPrime k))).2.2.2.2.2
    rw [sub_add_cancel] at hs
    rw [show 2 * completeEllipticK k * (t - jacobiTau k / 2) = (2 * completeEllipticK k * t -
      2 * (I * completeEllipticKPrime k)) + I * completeEllipticKPrime k by linear_combination -hK,
      (jacobiDs_shift hk _).2.2.1, hs]; ring

/-- DLMF 22.12.4: the Eisenstein-type expansion of `dn(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (both limits are symmetric partial sums, as
printed). -/
@[dlmf 22.12.E4 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiDn_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, t - m - (n + 1 / 2) * jacobiTau k ≠ 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (-1) ^ n * π / tan (π * (t - (n + 1 / 2) *
        jacobiTau k))) atTop
        (𝓝 (2 * I * completeEllipticK k * jacobiDn (2 * completeEllipticK k * t) k)) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, 1 / (t - (n + 1 / 2) *
          jacobiTau k - m))
        atTop (𝓝 (π / tan (π * (t - (n + 1 / 2) * jacobiTau k)))) := by
  have hK := completeEllipticK_mul_jacobiTau hk
  have hl := not_mem_eisensteinSinLattice (τ := jacobiTau k) (t := t - jacobiTau k / 2)
    fun m n => by convert ht n m using 1; ring
  refine ⟨?_, fun n => ?_⟩
  · have hv : 2 * I * completeEllipticK k * jacobiDn (2 * completeEllipticK k * t) k =
        eisensteinCotSeries (-1) (jacobiTau k) (t - jacobiTau k / 2) := by
      rw [← jacobiCs_eq_eisensteinCotSeries hk hl, show 2 * completeEllipticK k * t =
        2 * completeEllipticK k * (t - jacobiTau k / 2) + I * completeEllipticKPrime k by
        linear_combination hK, (jacobiDn_shift hk _).2.2.1]
      ring_nf; rw [I_sq]; ring
    rw [hv]
    refine (tendsto_sum_Icc_zpow_pi_mul_cot (Or.inr rfl) (jacobiTau_im_pos hk) _).congr
      fun N => Finset.sum_congr rfl fun n _ => ?_
    rw [mul_div_assoc, div_tan_eq_mul_cot]; congr 4; ring
  · rw [div_tan_eq_mul_cot]
    exact tendsto_sum_Icc_one_div_sub fun m => by convert ht n m using 1; ring

/-- DLMF 22.12.5: the Eisenstein-type expansion of `cd(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (the outer series converges absolutely (`HasSum` over
`ℤ`), each inner series in symmetric partial sums). -/
@[dlmf 22.12.E5 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiCd_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, (t + 1 / 2) - m - (n + 1 / 2) * jacobiTau k ≠ 0) :
    HasSum (fun n : ℤ => π / sin (π * ((t + 1 / 2) - (n + 1 / 2) * jacobiTau k))) (2 *
        completeEllipticK k * k * jacobiCd (2 * completeEllipticK k * t) k) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1) ^ m / ((t + 1 / 2) - (n +
          1 / 2) * jacobiTau k - m))
        atTop (𝓝 (π / sin (π * ((t + 1 / 2) - (n + 1 / 2) * jacobiTau k)))) := by
  have hK := completeEllipticK_mul_jacobiTau hk
  refine ⟨?_, fun n => tendsto_sum_Icc_neg_one_zpow_div_sub fun m =>
      by convert ht n m using 1; ring⟩
  have h := hasSum_pi_div_sin_jacobiNs hk (t := t + 1 / 2 - jacobiTau k / 2)
    (not_mem_eisensteinSinLattice fun m n => by convert ht n m using 1; ring)
  convert h using 1
  · funext n; congr 2; ring
  · have hs := (jacobiCd_shift hk
        (2 * completeEllipticK k * t - 2 * (I * completeEllipticKPrime k))).2.2.2.2.2
    rw [sub_add_cancel] at hs
    rw [show 2 * completeEllipticK k * (t + 1 / 2 - jacobiTau k / 2) =
        (2 * completeEllipticK k * t -
      2 * (I * completeEllipticKPrime k)) + completeEllipticK k + I * completeEllipticKPrime k by
      linear_combination -hK, (jacobiNs_shift hk _).2.1, ← hs]; ring

/-- DLMF 22.12.6: the Eisenstein-type expansion of `sd(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (the outer series converges absolutely (`HasSum` over
`ℤ`), each inner series in symmetric partial sums). -/
@[dlmf 22.12.E6 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiSd_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, (t + 1 / 2) - m - (n + 1 / 2) * jacobiTau k ≠ 0) :
    HasSum (fun n : ℤ => (-1) ^ n * π / sin (π * ((t + 1 / 2) - (n + 1 / 2) * jacobiTau k))) (-2 *
        I * completeEllipticK k * k * jacobiComodulus k *
            jacobiSd (2 * completeEllipticK k * t) k) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1) ^ (m + n) / ((t + 1 / 2) -
          (n + 1 / 2) * jacobiTau k - m))
        atTop (𝓝 ((-1) ^ n * π / sin (π * ((t + 1 / 2) - (n + 1 / 2) * jacobiTau k)))) := by
  have hK := completeEllipticK_mul_jacobiTau hk
  refine ⟨?_, fun n =>
      tendsto_sum_Icc_neg_one_zpow_add_div_sub (fun m => by convert ht n m using 1; ring) n⟩
  have h := hasSum_neg_one_zpow_pi_div_sin_jacobiDs hk (t := t + 1 / 2 - jacobiTau k / 2)
    (not_mem_eisensteinSinLattice fun m n => by convert ht n m using 1; ring)
  convert h using 1
  · funext n; congr 3; ring
  · have hs := (jacobiSd_shift hk
        (2 * completeEllipticK k * t - 2 * (I * completeEllipticKPrime k))).2.2.2.2.2
    rw [sub_add_cancel] at hs
    rw [show 2 * completeEllipticK k * (t + 1 / 2 - jacobiTau k / 2) =
        (2 * completeEllipticK k * t -
      2 * (I * completeEllipticKPrime k)) + completeEllipticK k + I * completeEllipticKPrime k by
      linear_combination -hK, (jacobiDs_shift hk _).2.1, hs]; ring

/-- DLMF 22.12.7: the Eisenstein-type expansion of `nd(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (both limits are symmetric partial sums, as
printed). -/
@[dlmf 22.12.E7 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiNd_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, (t + 1 / 2) - m - (n + 1 / 2) * jacobiTau k ≠ 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (-1) ^ n * π / tan (π * ((t + 1 / 2) -
        (n + 1 / 2) * jacobiTau k))) atTop
        (𝓝 (2 * I * completeEllipticK k * jacobiComodulus k *
            jacobiNd (2 * completeEllipticK k * t) k)) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, 1 / ((t + 1 / 2) - (n + 1 /
          2) * jacobiTau k - m))
        atTop (𝓝 (π / tan (π * ((t + 1 / 2) - (n + 1 / 2) * jacobiTau k)))) := by
  have hK := completeEllipticK_mul_jacobiTau hk
  have hl := not_mem_eisensteinSinLattice (τ := jacobiTau k)
    (t := t + 1 / 2 - jacobiTau k / 2) fun m n => by convert ht n m using 1; ring
  refine ⟨?_, fun n => ?_⟩
  · obtain ⟨w, hw⟩ : ∃ w, w = 2 * completeEllipticK k * t - completeEllipticK k - I *
        completeEllipticKPrime k :=
      ⟨_, rfl⟩
    have e1 : 2 * completeEllipticK k * t = w + completeEllipticK k + I *
        completeEllipticKPrime k := by
      rw [hw]; ring
    have e2 : 2 * completeEllipticK k * (t + 1 / 2 - jacobiTau k / 2) = w + 2 *
        completeEllipticK k := by
      rw [hw]; linear_combination -hK
    have hk' := jacobiComodulus_ne_zero hk
    have hv : 2 * I * completeEllipticK k * jacobiComodulus k *
        jacobiNd (2 * completeEllipticK k * t) k =
        eisensteinCotSeries (-1) (jacobiTau k) (t + 1 / 2 - jacobiTau k / 2) := by
      rw [← jacobiCs_eq_eisensteinCotSeries hk hl, e2, (jacobiCs_shift hk _).2.2.2.1, e1,
        (jacobiNd_shift hk _).2.1]
      field_simp; ring_nf; rw [I_sq]; ring
    rw [hv]
    refine (tendsto_sum_Icc_zpow_pi_mul_cot (Or.inr rfl) (jacobiTau_im_pos hk) _).congr
      fun N => Finset.sum_congr rfl fun n _ => ?_
    rw [mul_div_assoc, div_tan_eq_mul_cot]; congr 4; ring
  · rw [div_tan_eq_mul_cot]
    exact tendsto_sum_Icc_one_div_sub fun m => by convert ht n m using 1; ring

/-- DLMF 22.12.8: the Eisenstein-type expansion of `dc(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (the outer series converges absolutely (`HasSum` over
`ℤ`), each inner series in symmetric partial sums). -/
@[dlmf 22.12.E8 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiDc_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, (t + 1 / 2) - m - n * jacobiTau k ≠ 0) :
    HasSum (fun n : ℤ => π / sin (π * ((t + 1 / 2) - n * jacobiTau k))) (2 * completeEllipticK k *
        jacobiDc (2 * completeEllipticK k * t) k) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1) ^ m / ((t + 1 / 2) - n *
          jacobiTau k - m))
        atTop (𝓝 (π / sin (π * ((t + 1 / 2) - n * jacobiTau k)))) := by
  refine ⟨?_, fun n => tendsto_sum_Icc_neg_one_zpow_div_sub fun m =>
      by convert ht n m using 1; ring⟩
  have h := hasSum_pi_div_sin_jacobiNs hk (t := t + 1 / 2)
    (not_mem_eisensteinSinLattice fun m n => ht n m)
  convert h using 1
  rw [show 2 * completeEllipticK k * (t + 1 / 2) = 2 * completeEllipticK k * t +
      completeEllipticK k by ring,
    (jacobiNs_shift hk _).1]

/-- DLMF 22.12.9: the Eisenstein-type expansion of `nc(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (the outer series converges absolutely (`HasSum` over
`ℤ`), each inner series in symmetric partial sums). -/
@[dlmf 22.12.E9 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiNc_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, (t + 1 / 2) - m - n * jacobiTau k ≠ 0) :
    HasSum (fun n : ℤ => (-1) ^ n * π / sin (π * ((t + 1 / 2) - n * jacobiTau k))) (2 *
        completeEllipticK k * jacobiComodulus k * jacobiNc (2 * completeEllipticK k * t) k) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1) ^ (m + n) / ((t + 1 / 2) -
          n * jacobiTau k - m))
        atTop (𝓝 ((-1) ^ n * π / sin (π * ((t + 1 / 2) - n * jacobiTau k)))) := by
  refine ⟨?_, fun n =>
      tendsto_sum_Icc_neg_one_zpow_add_div_sub (fun m => by convert ht n m using 1; ring) n⟩
  have h := hasSum_neg_one_zpow_pi_div_sin_jacobiDs hk (t := t + 1 / 2)
    (not_mem_eisensteinSinLattice fun m n => ht n m)
  convert h using 1
  rw [show 2 * completeEllipticK k * (t + 1 / 2) = 2 * completeEllipticK k * t +
      completeEllipticK k by ring,
    (jacobiDs_shift hk _).1]; ring

/-- DLMF 22.12.10: the Eisenstein-type expansion of `sc(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (both limits are symmetric partial sums, as
printed). -/
@[dlmf 22.12.E10 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiSc_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, (t + 1 / 2) - m - n * jacobiTau k ≠ 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (-1) ^ n * π / tan (π * ((t + 1 / 2) - n *
        jacobiTau k))) atTop
        (𝓝 (-2 * completeEllipticK k * jacobiComodulus k *
            jacobiSc (2 * completeEllipticK k * t) k)) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, 1 / ((t + 1 / 2) - n *
          jacobiTau k - m))
        atTop (𝓝 (π / tan (π * ((t + 1 / 2) - n * jacobiTau k)))) := by
  have hl := not_mem_eisensteinSinLattice (τ := jacobiTau k) (t := t + 1 / 2)
    fun m n => ht n m
  refine ⟨?_, fun n => ?_⟩
  · have hv : -2 * completeEllipticK k * jacobiComodulus k *
        jacobiSc (2 * completeEllipticK k * t) k =
        eisensteinCotSeries (-1) (jacobiTau k) (t + 1 / 2) := by
      rw [← jacobiCs_eq_eisensteinCotSeries hk hl, show 2 * completeEllipticK k * (t + 1 / 2) =
        2 * completeEllipticK k * t + completeEllipticK k by ring, (jacobiCs_shift hk _).1]
      ring
    rw [hv]
    refine (tendsto_sum_Icc_zpow_pi_mul_cot (Or.inr rfl) (jacobiTau_im_pos hk) _).congr
      fun N => Finset.sum_congr rfl fun n _ => ?_
    rw [mul_div_assoc, div_tan_eq_mul_cot]
  · rw [div_tan_eq_mul_cot]
    exact tendsto_sum_Icc_one_div_sub fun m => by convert ht n m using 1; ring

/-- DLMF 22.12.11: the Eisenstein-type expansion of `ns(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (the outer series converges absolutely (`HasSum` over
`ℤ`), each inner series in symmetric partial sums). -/
@[dlmf 22.12.E11 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiNs_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, t - m - n * jacobiTau k ≠ 0) :
    HasSum (fun n : ℤ => π / sin (π * (t - n * jacobiTau k)))
        (2 * completeEllipticK k * jacobiNs (2 *
        completeEllipticK k * t) k) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1) ^ m / (t - n *
          jacobiTau k - m))
        atTop (𝓝 (π / sin (π * (t - n * jacobiTau k)))) := by
  exact ⟨hasSum_pi_div_sin_jacobiNs hk (not_mem_eisensteinSinLattice fun m n => ht n m),
    fun n => tendsto_sum_Icc_neg_one_zpow_div_sub fun m => by convert ht n m using 1; ring⟩

/-- DLMF 22.12.12: the Eisenstein-type expansion of `ds(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (the outer series converges absolutely (`HasSum` over
`ℤ`), each inner series in symmetric partial sums). -/
@[dlmf 22.12.E12 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiDs_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, t - m - n * jacobiTau k ≠ 0) :
    HasSum (fun n : ℤ => (-1) ^ n * π / sin (π * (t - n * jacobiTau k))) (2 * completeEllipticK k *
        jacobiDs (2 * completeEllipticK k * t) k) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1) ^ (m + n) / (t - n *
          jacobiTau k - m))
        atTop (𝓝 ((-1) ^ n * π / sin (π * (t - n * jacobiTau k)))) := by
  exact ⟨hasSum_neg_one_zpow_pi_div_sin_jacobiDs hk
      (not_mem_eisensteinSinLattice fun m n => ht n m),
    fun n => tendsto_sum_Icc_neg_one_zpow_add_div_sub (fun m => by convert ht n m using 1; ring) n⟩

/-- DLMF 22.12.13: the Eisenstein-type expansion of `cs(2Kt, k)`, `τ = iK'/K`, for
`k ∈ jacobiModulusDomain` and `t` not a pole (both limits are symmetric partial sums, as
printed). -/
@[dlmf 22.12.E13 "domain: k ∈ jacobiModulusDomain, t not a pole"]
theorem jacobiCs_partialFractions (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : ∀ n m : ℤ, t - m - n * jacobiTau k ≠ 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (-1) ^ n * π / tan (π * (t - n *
        jacobiTau k))) atTop
        (𝓝 (2 * completeEllipticK k * jacobiCs (2 * completeEllipticK k * t) k)) ∧
      ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, 1 / (t - n * jacobiTau k - m))
        atTop (𝓝 (π / tan (π * (t - n * jacobiTau k)))) := by
  have hl := not_mem_eisensteinSinLattice (τ := jacobiTau k) (t := t) fun m n => ht n m
  refine ⟨?_, fun n => ?_⟩
  · rw [jacobiCs_eq_eisensteinCotSeries hk hl]
    refine (tendsto_sum_Icc_zpow_pi_mul_cot (Or.inr rfl) (jacobiTau_im_pos hk) _).congr
      fun N => Finset.sum_congr rfl fun n _ => ?_
    rw [mul_div_assoc, div_tan_eq_mul_cot]
  · rw [div_tan_eq_mul_cot]
    exact tendsto_sum_Icc_one_div_sub fun m => by convert ht n m using 1; ring


end DLMF.JacobiElliptic
