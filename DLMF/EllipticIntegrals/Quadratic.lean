/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.AGMSecondKind
public import DLMF.EllipticIntegrals.Connection
public import DLMF.EllipticIntegrals.SymmetricQuadratic

/-!
# Quadratic transformations of Legendre's integrals (DLMF §19.8)

Gauss's arithmetic-geometric mean and its use for computing the complete integrals
(§19.8(i)), and the Landen and Gauss transformations (§19.8(ii)–(iii)).

## Main definitions

* `agmSeqA`, `agmSeqG`: DLMF's arithmetic and geometric means `aₙ`, `gₙ` (DLMF 19.8.1).
* `agmSeqC`: `cₙ = √(aₙ² - gₙ²)` (DLMF 19.8.2).
* `agmPiSeq`, `agmPiEps`: the sequences `pₙ, εₙ, Qₙ` of DLMF 19.8.8.

## Main results

* `agmSeq_succ`, `tendsto_agmSeq`: the recursion 19.8.1 and convergence to `M(a₀, g₀)`.
* `agmSeqC_succ`: DLMF 19.8.3.
* `inv_agm_eq_integral`: `1/M(a₀, g₀)` as an integral (DLMF 19.8.4).
* `completeEllipticK_eq_pi_div_agm`, `completeEllipticE_eq_agm`: `K` and `E` by the AGM
  (DLMF 19.8.5, 19.8.6).
* `completeEllipticPi_eq_agm`, `completeEllipticPi_eq_agm_of_one_lt`: `Π(α², k)` by the AGM
  (DLMF 19.8.7, 19.8.9–19.8.10).
* `landen_descending_amplitude`: the descending Landen modulus and amplitude (DLMF 19.8.11).
* `compEllInt_landen_descending_ofReal`, `compEllInt_landen_descending`: the descending Landen
  transformation of `K` and `E` for real and complex `k` (DLMF 19.8.12).
* `incEllInt_landen_descending`, `incompleteEllipticPi_landen_descending`: DLMF 19.8.13–19.8.15.
* `incEllInt_landen_ascending`: the ascending Landen transformation (DLMF 19.8.16–19.8.17).
* `incEllInt_gauss`, `incompleteEllipticPi_gauss`: the descending Gauss transformation
  (DLMF 19.8.18–19.8.21).

## Implementation notes

* The sequences `agmSeqA`, `agmSeqG` are read off Mathlib's `NNReal.agmSequences` (which lists
  `(g_{n+1}, a_{n+1})`), and `M(a₀, g₀)` is Mathlib's `NNReal.agm`.
* DLMF 19.8.5 for complex `k` with real `k² < 1` follows from the real
  `DLMF.Elliptic.Real.completeEllipticKOfParameter_eq_pi_div_agm`. DLMF 19.8.6 is proved from
  `lean-codes`' `Carlson.hasSum_agmA_zero` and `Carlson.carlsonRE_eq_agm` (Carlson, Exercises
  9.5-3/9.5-4), with `E(k) = (π/2) R_E(1, k'²)` and `K(k) = (π/2) R_K(1, k'²)` from 19.25.1, for all
  real `k² < 1`.
* The Landen and Gauss transformations are stated for real `0 < k < 1` and real amplitudes, as
  in DLMF's notes. DLMF 19.8.12 for real `k² < 1` comes from the real
  `Real.completeEllipticKOfParameter_landen_descending` and
  `Real.completeEllipticEOfParameter_landen_descending`, and for complex `k` with
  `1 - k² ∈ ℂ \ (-∞, 0]` from the real case by the identity theorem.

## References

* NIST DLMF §19.8.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology NNReal

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-! ### §19.8(i) Gauss's arithmetic-geometric mean -/

/-- DLMF's arithmetic means `aₙ` (19.8.1): `a₀`, `a_{n+1} = (aₙ + gₙ)/2`. -/
@[dlmf 19.8.E1]
def agmSeqA (a₀ g₀ : ℝ≥0) : ℕ → ℝ≥0
  | 0 => a₀
  | n + 1 => (NNReal.agmSequences a₀ g₀ n).2

/-- DLMF's geometric means `gₙ` (19.8.1): `g₀`, `g_{n+1} = √(aₙ gₙ)`. -/
@[dlmf 19.8.E1]
def agmSeqG (a₀ g₀ : ℝ≥0) : ℕ → ℝ≥0
  | 0 => g₀
  | n + 1 => (NNReal.agmSequences a₀ g₀ n).1

/-- DLMF 19.8.2: `cₙ = √(aₙ² - gₙ²)`. -/
@[dlmf 19.8.E2]
def agmSeqC (a₀ g₀ : ℝ≥0) (n : ℕ) : ℝ :=
  Real.sqrt ((agmSeqA a₀ g₀ n : ℝ) ^ 2 - (agmSeqG a₀ g₀ n : ℝ) ^ 2)

/-- DLMF 19.8.1: the recursion `a_{n+1} = (aₙ + gₙ)/2`, `g_{n+1} = √(aₙ gₙ)`. -/
@[dlmf 19.8.E1]
theorem agmSeq_succ (a₀ g₀ : ℝ≥0) (n : ℕ) :
    agmSeqA a₀ g₀ (n + 1) = (agmSeqA a₀ g₀ n + agmSeqG a₀ g₀ n) / 2 ∧
      agmSeqG a₀ g₀ (n + 1) = NNReal.sqrt (agmSeqA a₀ g₀ n * agmSeqG a₀ g₀ n) := by
  cases n with
  | zero => simp [agmSeqA, agmSeqG, NNReal.agmSequences_zero]
  | succ n =>
    simp only [agmSeqA, agmSeqG, NNReal.agmSequences_succ']
    exact ⟨by rw [add_comm], by rw [mul_comm]⟩

/-- DLMF §19.8(i): `aₙ` and `gₙ` converge to the common limit `M(a₀, g₀)` (Mathlib's
`NNReal.agm`). -/
@[dlmf 19.8.E1]
theorem tendsto_agmSeq (a₀ g₀ : ℝ≥0) :
    Tendsto (agmSeqA a₀ g₀) atTop (𝓝 (NNReal.agm a₀ g₀)) ∧
      Tendsto (agmSeqG a₀ g₀) atTop (𝓝 (NNReal.agm a₀ g₀)) := by
  constructor
  · rw [← Filter.tendsto_add_atTop_iff_nat 1]
    exact NNReal.tendsto_agmSequences_snd_agm
  · rw [← Filter.tendsto_add_atTop_iff_nat 1]
    exact NNReal.tendsto_agmSequences_fst_agm

/-- Estimate under the stated parameter and domain assumptions: `agmSeqG a₀ g₀ n ≤ agmSeqA a₀ g₀
n`. -/
private lemma agmSeqG_le_agmSeqA {a₀ g₀ : ℝ≥0} (h : g₀ ≤ a₀) (n : ℕ) :
    agmSeqG a₀ g₀ n ≤ agmSeqA a₀ g₀ n := by
  cases n with
  | zero => exact h
  | succ n => exact NNReal.agmSequences_fst_le_snd n n

/-- Estimate under the stated parameter and domain assumptions: `0 < agmSeqA a₀ g₀ n`. -/
private lemma agmSeqA_pos {a₀ g₀ : ℝ≥0} (h : 0 < a₀) (n : ℕ) : 0 < agmSeqA a₀ g₀ n := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [(agmSeq_succ a₀ g₀ n).1]
    exact div_pos (add_pos_of_pos_of_nonneg ih (by simp)) two_pos

/-- DLMF 19.8.3: for `0 < g₀ ≤ a₀`, `c_{n+1} = (aₙ - gₙ)/2 = cₙ²/(4a_{n+1})`. -/
@[dlmf 19.8.E3]
theorem agmSeqC_succ {a₀ g₀ : ℝ≥0} (hg : 0 < g₀) (h : g₀ ≤ a₀) (n : ℕ) :
    agmSeqC a₀ g₀ (n + 1) = ((agmSeqA a₀ g₀ n : ℝ) - agmSeqG a₀ g₀ n) / 2 ∧
      agmSeqC a₀ g₀ (n + 1) = agmSeqC a₀ g₀ n ^ 2 / (4 * agmSeqA a₀ g₀ (n + 1)) := by
  have hle := agmSeqG_le_agmSeqA h n
  have hpos := agmSeqA_pos (g₀ := g₀) (lt_of_lt_of_le hg h) n
  set a : ℝ := (agmSeqA a₀ g₀ n : ℝ) with ha
  set g : ℝ := (agmSeqG a₀ g₀ n : ℝ) with hgdef
  have hle' : g ≤ a := by exact_mod_cast hle
  have hg0 : 0 ≤ g := (agmSeqG a₀ g₀ n).2
  have ha0 : 0 < a := by exact_mod_cast hpos
  have hA : (agmSeqA a₀ g₀ (n + 1) : ℝ) = (a + g) / 2 := by
    rw [(agmSeq_succ a₀ g₀ n).1]; push_cast; rfl
  have hG : (agmSeqG a₀ g₀ (n + 1) : ℝ) = Real.sqrt (a * g) := by
    rw [(agmSeq_succ a₀ g₀ n).2, Real.coe_sqrt]; push_cast; rfl
  have h1 : agmSeqC a₀ g₀ (n + 1) = (a - g) / 2 := by
    rw [agmSeqC, hA, hG, Real.sq_sqrt (by positivity)]
    rw [show ((a + g) / 2) ^ 2 - a * g = ((a - g) / 2) ^ 2 by ring,
      Real.sqrt_sq (by linarith)]
  refine ⟨h1, ?_⟩
  rw [h1, agmSeqC, Real.sq_sqrt (by nlinarith), hA]
  field_simp
  ring

/-- DLMF 19.8.4 (second form): for `a₀, g₀ > 0`,
`1/M(a₀, g₀) = (1/π) ∫₀^∞ dt/√(t(t + a₀²)(t + g₀²))`. The first form,
`1/M = (2/π) ∫₀^{π/2} dθ/√(a₀² cos²θ + g₀² sin²θ)`, is the existing
`DLMF.Elliptic.agmIntegral_eq_pi_div_two_div_agm`. The proof goes through
`Carlson.TwoVariable.carlsonRK_sq_eq_inv_agm` from lean-codes. -/
@[dlmf 19.8.E4]
theorem inv_agm_eq_integral {a₀ g₀ : ℝ≥0} (ha : 0 < a₀) (hg : 0 < g₀) :
    1 / (NNReal.agm a₀ g₀ : ℝ) =
      1 / π *
        ∫ t in Ioi (0 : ℝ), (t * (t + (a₀ : ℝ) ^ 2) * (t + (g₀ : ℝ) ^ 2)) ^ (-(1 / 2) : ℝ) := by
  have ha' : (0 : ℝ) < a₀ := ha
  have hg' : (0 : ℝ) < g₀ := hg
  have hy : (((a₀ : ℝ) : ℂ) ^ 2) ∈ slitPlane := by
    rw [← ofReal_pow]; exact ofReal_mem_slitPlane.2 (by positivity)
  have hz : (((g₀ : ℝ) : ℂ) ^ 2) ∈ slitPlane := by
    rw [← ofReal_pow]; exact ofReal_mem_slitPlane.2 (by positivity)
  have hK := Carlson.TwoVariable.carlsonRK_sq_eq_inv_agm ha hg
  have hRF := symmetricEllipticRF_zero_left hy hz
  rw [symmetricEllipticR_of_mem _ _ (vec2_mem_carlsonRSlitDomain hy hz)] at hRF
  have hRK : Carlson.carlsonR (-(1 / 2)) ![1 / 2, 1 / 2] ![((a₀ : ℝ) : ℂ) ^ 2, ((g₀ : ℝ) : ℂ) ^ 2] =
      Carlson.TwoVariable.carlsonRK (((a₀ : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) := by
    unfold Carlson.TwoVariable.carlsonRK Carlson.TwoVariable.pair
    congr 1; ring
  rw [hRK, hK, symmetricEllipticRF] at hRF
  have hint : ∫ t in Ioi (0 : ℝ),
      (carlsonRootProduct 0 (((a₀ : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) t)⁻¹ =
      ((∫ t in Ioi (0 : ℝ),
        (t * (t + (a₀ : ℝ) ^ 2) * (t + (g₀ : ℝ) ^ 2)) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    simp only [carlsonRootProduct, add_zero]
    rw [show (((a₀ : ℝ) : ℂ) ^ 2) = (((a₀ : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; rfl,
      show (((g₀ : ℝ) : ℂ) ^ 2) = (((g₀ : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; rfl,
      ← ofReal_add, ← ofReal_add,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow ht'.le, ← ofReal_cpow (by positivity), ← ofReal_cpow (by positivity),
      ← ofReal_mul, ← ofReal_mul, ← ofReal_inv,
      ← Real.mul_rpow (by positivity) (by positivity),
      ← Real.mul_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity)]
  rw [hint] at hRF
  have hM : (0 : ℝ) < NNReal.agm a₀ g₀ := NNReal.agm_pos ha hg
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  apply ofReal_injective
  push_cast
  have hM' : ((NNReal.agm a₀ g₀ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hM.ne'
  field_simp at hRF ⊢
  linear_combination -hRF

/-- DLMF 19.8.5: `K(k) = π/(2M(1, k'))` for `-∞ < k² < 1` (complex `k` with real `k² = m < 1`,
`k' = √(1 - m)`). -/
@[dlmf 19.8.E5]
theorem completeEllipticK_eq_pi_div_agm {k : ℂ} {m : ℝ} (hk : k ^ 2 = m) (hm : m < 1) :
    completeEllipticK k = π / (2 * (NNReal.agm 1 (NNReal.sqrt (1 - m).toNNReal) : ℝ)) := by
  rw [completeEllipticK_eq_ofReal hk hm.le,
      DLMF.Elliptic.Real.completeEllipticKOfParameter_eq_pi_div_agm hm]
  push_cast; rfl

/-- Bridge between lean-codes' `Carlson.agmSeq` and DLMF's `agmSeqA`, `agmSeqG`. -/
private lemma agmSeq_eq_agmSeqA_agmSeqG (a₀ g₀ : ℝ≥0) (n : ℕ) :
    Carlson.agmSeq a₀ g₀ n = ((agmSeqA a₀ g₀ n : ℝ), (agmSeqG a₀ g₀ n : ℝ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Carlson.agmSeq_succ, ih, (agmSeq_succ a₀ g₀ n).1, (agmSeq_succ a₀ g₀ n).2]
    simp [Carlson.agmStep, Real.coe_sqrt]

/-- Identity under the stated parameter and domain assumptions: `agmSeqC a₀ g₀ (n + 1) ^ 2 =
(agmSeqA a₀ g₀ (n + 1) : ℝ) ^ 2 - (agmSeqG a₀ g₀ (n + 1) : ℝ) ^ 2`. -/
private lemma agmSeqC_sq_succ (a₀ g₀ : ℝ≥0) (n : ℕ) :
    agmSeqC a₀ g₀ (n + 1) ^ 2 =
      (agmSeqA a₀ g₀ (n + 1) : ℝ) ^ 2 - (agmSeqG a₀ g₀ (n + 1) : ℝ) ^ 2 := by
  have hle : agmSeqG a₀ g₀ (n + 1) ≤ agmSeqA a₀ g₀ (n + 1) :=
    NNReal.agmSequences_fst_le_snd n n
  have hle' : (agmSeqG a₀ g₀ (n + 1) : ℝ) ≤ agmSeqA a₀ g₀ (n + 1) := by exact_mod_cast hle
  have h0 : (0 : ℝ) ≤ agmSeqG a₀ g₀ (n + 1) := NNReal.coe_nonneg _
  rw [agmSeqC, Real.sq_sqrt (by nlinarith)]

/-- DLMF 19.8.6: for `-∞ < k² < 1` (`k² = m` real), `a₀ = 1`, `g₀ = k'`,
`E(k) = (π/(2M(1, k')))(a₀² - ∑ₙ 2^{n-1} cₙ²) = K(k)(a₁² - ∑_{n≥2} 2^{n-1} cₙ²)`.
The sum is written with `cₙ² = aₙ² - gₙ²` (DLMF 19.8.2), so that `c₀² = k² = m` also for `m < 0`.
Corrected 2026-10-25: the earlier `agmSeqC 1 g₀ n ^ 2` is a real square root and gave `c₀ = 0`
for `m < 0`, which made the first identity false (mpmath at `m = -1`). -/
@[dlmf 19.8.E6]
theorem completeEllipticE_eq_agm {k : ℂ} {m : ℝ} (hk : k ^ 2 = m) (hm : m < 1) :
    let g₀ : ℝ≥0 := NNReal.sqrt (1 - m).toNNReal
    HasSum (fun n : ℕ => (2 : ℝ) ^ ((n : ℤ) - 1) *
        ((agmSeqA 1 g₀ n : ℝ) ^ 2 - (agmSeqG 1 g₀ n : ℝ) ^ 2))
        (1 - (completeEllipticE k).re * (2 * (NNReal.agm 1 g₀ : ℝ)) / π) ∧
      completeEllipticE k = completeEllipticK k * ((agmSeqA 1 g₀ 1 : ℝ) ^ 2 -
        ∑' n : ℕ, (2 : ℝ) ^ (n + 1) * agmSeqC 1 g₀ (n + 2) ^ 2 : ℝ) := by
  intro g₀
  have hm1 : 0 < 1 - m := by linarith
  have hg₀ : ((g₀ : ℝ)) = Real.sqrt (1 - m) := by
    simp [g₀, Real.coe_sqrt, Real.coe_toNNReal _ hm1.le]
  have hgpos : (0 : ℝ) < g₀ := by rw [hg₀]; exact Real.sqrt_pos.2 hm1
  have hg2 : ((g₀ : ℝ) : ℂ) ^ 2 = 1 - k ^ 2 := by
    rw [hk, hg₀, ← ofReal_pow, Real.sq_sqrt hm1.le]; push_cast; ring
  have hslit : 1 - k ^ 2 ∈ slitPlane := by
    rw [hk, ← ofReal_one, ← ofReal_sub]; exact ofReal_mem_slitPlane.2 hm1
  have hg2s : ((g₀ : ℝ) : ℂ) ^ 2 ∈ slitPlane := hg2 ▸ hslit
  have h1s : ((1 : ℝ) : ℂ) ^ 2 ∈ slitPlane := by simp
  -- `E = (π/2) R_E(1, g₀²)` and `K = (π/2) R_K(1, g₀²)`
  have hE : completeEllipticE k = (π / 2) *
      Carlson.carlsonRE (((1 : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) := by
    rw [(completeEllipticE_eq_symmetricElliptic hslit).1, ← hg2,
      symmetricEllipticRG_zero_eq_carlsonRE hg2s one_mem_slitPlane,
      carlsonRE_comm_of_mem_slitPlane hg2s one_mem_slitPlane]
    push_cast; ring_nf
  have hK : completeEllipticK k =
      (π / 2) * Carlson.TwoVariable.carlsonRK (((1 : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) := by
    rw [completeEllipticK_eq_symmetricEllipticRF hslit, ← hg2,
      symmetricEllipticRF_zero_eq_carlsonRK hg2s one_mem_slitPlane,
      Carlson.TwoVariable.carlsonRK_comm hg2s one_mem_slitPlane]
    push_cast; rw [one_pow]
  have hRK : Carlson.TwoVariable.carlsonRK (((1 : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) =
      ((NNReal.agm 1 g₀ : ℝ) : ℂ)⁻¹ := by
    have := Carlson.TwoVariable.carlsonRK_sq_eq_inv_agm (x := 1) (y := g₀) one_pos
      (by exact_mod_cast hgpos)
    simpa using this
  have hMpos : (0 : ℝ) < NNReal.agm 1 g₀ := by
    exact_mod_cast NNReal.agm_pos one_pos (by exact_mod_cast hgpos)
  have hM0 : ((NNReal.agm 1 g₀ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hMpos.ne'
  have hseq : ∀ n, Carlson.agmSeq (1 : ℝ≥0) g₀ n =
      ((agmSeqA 1 g₀ n : ℝ), (agmSeqG 1 g₀ n : ℝ)) := agmSeq_eq_agmSeqA_agmSeqG 1 g₀
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  constructor
  · have h := Carlson.hasSum_agmA_zero (x := 1) (y := g₀) one_pos hgpos
    rw [hRK] at h
    have hA0 : Carlson.agmA 1 g₀ 0 = 2 * (Carlson.carlsonRE (((1 : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2)
        - ((NNReal.agm 1 g₀ : ℝ) : ℂ)⁻¹) := by
      simp only [Carlson.agmA, Carlson.agmX, Carlson.agmY, Carlson.agmSeq_zero]
      rw [hRK]; push_cast; ring
    rw [hA0] at h
    have h2 := h.mul_left (-(((NNReal.agm 1 g₀ : ℝ) : ℂ)) / 2)
    have h3 : HasSum (fun n : ℕ => (((2 : ℝ) ^ ((n : ℤ) - 1) *
        ((agmSeqA 1 g₀ n : ℝ) ^ 2 - (agmSeqG 1 g₀ n : ℝ) ^ 2) : ℝ) : ℂ))
        (1 - completeEllipticE k * (2 * ((NNReal.agm 1 g₀ : ℝ) : ℂ)) / π) := by
      convert h2 using 1
      · funext n
        have e : (1 : ℝ) = ((1 : ℝ≥0) : ℝ) := rfl
        simp only [Carlson.agmX, Carlson.agmY]
        rw [show ((1 : ℝ)) = ((1 : ℝ≥0) : ℝ) from rfl, hseq n]
        push_cast
        rw [zpow_sub₀ (two_ne_zero), zpow_natCast, zpow_one]
        field_simp
        ring
      · rw [hE]; field_simp; ring
    have h4 := Complex.reCLM.hasSum h3
    simp only [Complex.reCLM_apply, Complex.ofReal_re] at h4
    convert h4 using 1
    rw [show (2 * ((NNReal.agm 1 g₀ : ℝ) : ℂ)) =
        ((2 * (NNReal.agm 1 g₀ : ℝ) : ℝ) : ℂ) by push_cast; ring,
      show (π : ℂ) = ((π : ℝ) : ℂ) from rfl]
    rw [Complex.sub_re, Complex.one_re, Complex.div_ofReal_re, Complex.re_mul_ofReal]
  · have h := Carlson.carlsonRE_eq_agm (x := 1) (y := g₀) one_pos hgpos
    rw [hE, hK, h]
    simp only [Carlson.agmX, Carlson.agmY]
    rw [show ((1 : ℝ)) = ((1 : ℝ≥0) : ℝ) from rfl]
    simp only [hseq]
    have hc : ∀ n : ℕ, agmSeqC 1 g₀ (n + 2) ^ 2 =
        (agmSeqA 1 g₀ (n + 2) : ℝ) ^ 2 - (agmSeqG 1 g₀ (n + 2) : ℝ) ^ 2 :=
      fun n => agmSeqC_sq_succ 1 g₀ (n + 1)
    simp only [hc]
    rw [Complex.ofReal_sub, Complex.ofReal_tsum]
    push_cast
    ring

/-- The sequences `(pₙ, εₙ, Qₙ)` of DLMF 19.8.8 with `a₀ = 1`, `g₀`, initial `p₀`, `Q₀ = 1`:
`p_{n+1} = (pₙ² + aₙgₙ)/(2pₙ)`, `εₙ = (pₙ² - aₙgₙ)/(pₙ² + aₙgₙ)`, `Q_{n+1} = Qₙεₙ/2`
(returned as `(pₙ, Qₙ)`; `εₙ` is `agmPiEps`). -/
@[dlmf 19.8.E8]
def agmPiSeq (g₀ : ℝ≥0) (p₀ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (p₀, 1)
  | n + 1 =>
    let p := (agmPiSeq g₀ p₀ n).1
    let Q := (agmPiSeq g₀ p₀ n).2
    let ag : ℝ := agmSeqA 1 g₀ n * agmSeqG 1 g₀ n
    ((p ^ 2 + ag) / (2 * p), Q * ((p ^ 2 - ag) / (p ^ 2 + ag)) / 2)

/-- `εₙ = (pₙ² - aₙgₙ)/(pₙ² + aₙgₙ)` (DLMF 19.8.8). -/
@[dlmf 19.8.E8]
def agmPiEps (g₀ : ℝ≥0) (p₀ : ℝ) (n : ℕ) : ℝ :=
  ((agmPiSeq g₀ p₀ n).1 ^ 2 - agmSeqA 1 g₀ n * agmSeqG 1 g₀ n) /
    ((agmPiSeq g₀ p₀ n).1 ^ 2 + agmSeqA 1 g₀ n * agmSeqG 1 g₀ n)

/-- **Admitted.** DLMF 19.8.7: for `-∞ < k² < 1` (`k² = m` real) and real `α² < 1`, with
`a₀ = 1`, `g₀ = k'`, `p₀² = 1 - α²` (`p₀ = √(1 - α²)`) and `Q₀ = 1`,
`Π(α², k) = (π/(4M(1, k')))(2 + (α²/(1 - α²)) ∑ₙ Qₙ)`. -/
@[dlmf 19.8.E7]
theorem completeEllipticPi_eq_agm {k : ℂ} {m α2 : ℝ} (hk : k ^ 2 = m) (hm : m < 1) (hα : α2 < 1) :
    let g₀ : ℝ≥0 := NNReal.sqrt (1 - m).toNNReal
    ∃ S : ℝ, HasSum (fun n => (agmPiSeq g₀ (Real.sqrt (1 - α2)) n).2) S ∧
      completeEllipticPi α2 k = π / (4 * (NNReal.agm 1 g₀ : ℝ)) * (2 + α2 / (1 - α2) * S) := by
  sorry

/-- **Admitted.** DLMF 19.8.9–19.8.10: for `-∞ < k² < 1` (`k² = m` real) and real
`1 < α²`, the Cauchy principal value is `Π(α², k) = (π/(4M(1, k'))) (k²/(k² - α²)) ∑ₙ Qₙ`,
with 19.8.8 started at `p₀² = 1 - k²/α²`. -/
@[dlmf 19.8.E9, dlmf 19.8.E10]
theorem completeEllipticPi_eq_agm_of_one_lt {k : ℂ} {m α2 : ℝ} (hk : k ^ 2 = m) (hm : m < 1)
    (hα : 1 < α2) :
    let g₀ : ℝ≥0 := NNReal.sqrt (1 - m).toNNReal
    ∃ S : ℝ, HasSum (fun n => (agmPiSeq g₀ (Real.sqrt (1 - m / α2)) n).2) S ∧
      completeEllipticPi α2 k = π / (4 * (NNReal.agm 1 g₀ : ℝ)) * (m / (m - α2)) * S := by
  sorry

/-! ### §19.8(ii) Landen transformations -/

/-- For real `k` with `k² ≤ 1`, the principal `k' = √(1 - k²)` is the real square root. -/
private lemma jacobiComodulus_ofReal_of_sq_le {k : ℝ} (hk : k ^ 2 ≤ 1) :
    jacobiComodulus k = (Real.sqrt (1 - k ^ 2) : ℂ) := by
  rw [jacobiComodulus, Real.sqrt_eq_rpow, show (1 : ℂ) - (k : ℂ) ^ 2 = ((1 - k ^ 2 : ℝ) : ℂ) by
    push_cast; ring, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (by linarith)]

/-- DLMF 19.8.11 (descending Landen modulus and amplitude): for real `0 < k < 1` and
`0 < φ < π/2`, with `k₁ = (1 - k')/(1 + k')`, the two expressions for `φ₁` agree:
`sin(φ + arctan(k' tan φ)) = (1 + k') sin φ cos φ/√(1 - k² sin²φ)`, and `k₁ < k`. -/
@[dlmf 19.8.E11]
theorem landen_descending_amplitude {k φ : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) :
    Real.sin (φ + Real.arctan (Real.sqrt (1 - k ^ 2) * Real.tan φ)) =
        (1 + Real.sqrt (1 - k ^ 2)) * Real.sin φ * Real.cos φ /
          Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) ∧
      (1 - Real.sqrt (1 - k ^ 2)) / (1 + Real.sqrt (1 - k ^ 2)) < k := by
  set s := Real.sqrt (1 - k ^ 2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by nlinarith)
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hφ1⟩
  have hsn := Real.sin_sq_add_cos_sq φ
  constructor
  · set u := s * Real.tan φ
    rw [Real.sin_add, Real.cos_arctan, Real.sin_arctan]
    have h1 : 1 + u ^ 2 = (1 - k ^ 2 * Real.sin φ ^ 2) / Real.cos φ ^ 2 := by
      simp only [u, Real.tan_eq_sin_div_cos]
      field_simp
      nlinarith [hs2, hsn]
    have hpos : 0 < 1 - k ^ 2 * Real.sin φ ^ 2 := by
      nlinarith [Real.sin_sq_le_one φ, sq_nonneg (Real.sin φ)]
    rw [h1, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hc.le]
    have hq : 0 < Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) := Real.sqrt_pos.2 hpos
    simp only [u, Real.tan_eq_sin_div_cos]
    field_simp
  · have h1 : 1 ≤ 1 + s := by linarith
    rw [div_lt_iff₀ (by linarith)]
    nlinarith

/-- DLMF 19.8.12 (descending Landen transformation of the complete integrals) for real `k` with
`k² < 1`: `K(k) = (1 + k₁)K(k₁)` and `E(k) = (1 + k')E(k₁) - k'K(k)`,
`k₁ = (1 - k')/(1 + k')`. -/
@[dlmf 19.8.E12]
theorem compEllInt_landen_descending_ofReal {k : ℝ} (hk : k ^ 2 < 1) :
    let kp := jacobiComodulus k
    let k₁ := (1 - kp) / (1 + kp)
    completeEllipticK k = (1 + k₁) * completeEllipticK k₁ ∧
      completeEllipticE k = (1 + kp) * completeEllipticE k₁ - kp * completeEllipticK k := by
  intro kp k₁
  set s := Real.sqrt (1 - k ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs1 : s ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg k])
  have hkp : kp = s := jacobiComodulus_ofReal_of_sq_le hk.le
  have hk₁ : k₁ = (((1 - s) / (1 + s) : ℝ) : ℂ) := by
    simp only [k₁, hkp]; push_cast; rfl
  have hr : ((1 - s) / (1 + s)) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity)]; nlinarith
  have hm : 1 - (k ^ 2) = s ^ 2 := by rw [hs, Real.sq_sqrt (by linarith)]
  have hsq : Real.sqrt (1 - k ^ 2) = s := rfl
  rw [hk₁, hkp, completeEllipticK_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk.le,
    completeEllipticK_eq_ofReal (m := ((1 - s) / (1 + s)) ^ 2) (by push_cast; ring) hr,
    completeEllipticE_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk.le,
    completeEllipticE_eq_ofReal (m := ((1 - s) / (1 + s)) ^ 2) (by push_cast; ring) hr]
  have h1 := DLMF.Elliptic.Real.completeEllipticKOfParameter_landen_descending hk
  have h2 := DLMF.Elliptic.Real.completeEllipticEOfParameter_landen_descending hk
  rw [hsq] at h1 h2
  constructor
  · rw [h1]; push_cast; ring
  · rw [h2]; push_cast; ring

/-- For `ℜ c > 0`, `1 - ((1 - c)/(1 + c))² = 4c/(1 + c)²` has positive real part. -/
theorem one_sub_landen_sq_mem_slitPlane {c : ℂ} (hc : 0 < c.re) :
    1 - ((1 - c) / (1 + c)) ^ 2 ∈ slitPlane := by
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have h1c : 1 + c ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  set D := c + 2 + c⁻¹ with hD
  have hDre : 0 < D.re := by
    have : 0 < (c⁻¹).re := by
      rw [inv_re]; exact div_pos hc (normSq_pos.2 hc0)
    rw [inv_re] at this
    simp only [hD, add_re]; norm_num; linarith
  have hD0 : D ≠ 0 := fun h => by simp [h] at hDre
  have hw : 1 - ((1 - c) / (1 + c)) ^ 2 = 4 * D⁻¹ := by
    have hD' : D = (1 + c) ^ 2 / c := by rw [hD]; field_simp; ring
    rw [hD', inv_div]; field_simp; ring
  rw [hw]
  refine mem_slitPlane_iff.2 (Or.inl ?_)
  have : 0 < (D⁻¹).re := by rw [inv_re]; exact div_pos hDre (normSq_pos.2 hD0)
  rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, re_ofReal_mul]; positivity

/-- DLMF 19.8.12 for complex `k` in the principal domain `1 - k² ∈ ℂ \ (-∞, 0]`:
`K(k) = (1 + k₁)K(k₁)`, `E(k) = (1 + k')E(k₁) - k'K(k)`. -/
@[dlmf 19.8.E12]
theorem compEllInt_landen_descending {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    let kp := jacobiComodulus k
    let k₁ := (1 - kp) / (1 + kp)
    completeEllipticK k = (1 + k₁) * completeEllipticK k₁ ∧
      completeEllipticE k = (1 + kp) * completeEllipticE k₁ - kp * completeEllipticK k := by
  intro kp k₁
  set U := {k : ℂ | 1 - k ^ 2 ∈ slitPlane} with hU
  have hD := differentiableOn_completeEllipticK_completeEllipticE
  have hre : ∀ k ∈ U, 0 < (jacobiComodulus k).re := fun k hk => Carlson.re_cpow_half_pos hk
  have hne : ∀ k ∈ U, 1 + jacobiComodulus k ≠ 0 := fun k hk h => by
    have := congrArg re h; simp at this; linarith [hre k hk]
  have hc : DifferentiableOn ℂ jacobiComodulus U := fun k hk =>
    (differentiableAt_jacobiComodulus hk).differentiableWithinAt
  set φ : ℂ → ℂ := fun k => (1 - jacobiComodulus k) / (1 + jacobiComodulus k) with hφ
  have hφd : DifferentiableOn ℂ φ U :=
    ((differentiableOn_const 1).sub hc).div ((differentiableOn_const 1).add hc) hne
  have hmaps : MapsTo φ U U := fun k hk => one_sub_landen_sq_mem_slitPlane (hre k hk)
  constructor
  · exact eq_of_differentiableOn_of_eq_on_Ioo hD.1
        (g := fun k => (1 + φ k) * completeEllipticK (φ k))
      (((differentiableOn_const 1).add hφd).mul (hD.1.comp hφd hmaps))
      (fun x h0 h1 => (compEllInt_landen_descending_ofReal (k := x) (by nlinarith)).1) hk
  · exact eq_of_differentiableOn_of_eq_on_Ioo hD.2
      (g := fun k => (1 + jacobiComodulus k) * completeEllipticE (φ k) -
        jacobiComodulus k * completeEllipticK k)
      ((((differentiableOn_const 1).add hc).mul (hD.2.comp hφd hmaps)).sub (hc.mul hD.1))
      (fun x h0 h1 => (compEllInt_landen_descending_ofReal (k := x) (by nlinarith)).2) hk

/-- **Admitted.** DLMF 19.8.13 (descending Landen transformation of `F`, `E`): for real
`0 < k < 1` and `0 < φ < π/2`, with `k₁ = (1 - k')/(1 + k')`, `φ₁ = φ + arctan(k' tan φ)`:
`F(φ, k) = ½(1 + k₁)F(φ₁, k₁)` and
`E(φ, k) = ½(1 + k')E(φ₁, k₁) - k'F(φ, k) + ½(1 - k') sin φ₁`. -/
@[dlmf 19.8.E13]
theorem incEllInt_landen_descending {k φ : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) :
    let kp := Real.sqrt (1 - k ^ 2)
    let k₁ := (1 - kp) / (1 + kp)
    let φ₁ := φ + Real.arctan (kp * Real.tan φ)
    incompleteEllipticF φ k = (1 + k₁ : ℝ) / 2 * incompleteEllipticF φ₁ k₁ ∧
      incompleteEllipticE φ k = (1 + kp : ℝ) / 2 * incompleteEllipticE φ₁ k₁ - kp *
          incompleteEllipticF φ k +
        ((1 - kp) / 2 * Real.sin φ₁ : ℝ) := by
  sorry

/-- **Admitted.** DLMF 19.8.14–19.8.15: for real `0 < k < 1`, `0 < φ < π/2` and real `α²` with
`α² ≠ 1`, `α² ≠ k²`, with `ω² = (k² - α²)/(1 - α²)`, `α₁² = α²ω²/(1 + k')²`, `c₁ = csc²φ₁`
(Cauchy principal values where needed):
`2(k² - α²)Π(φ, α², k) = ((ω² - α²)/(1 + k'))Π(φ₁, α₁², k₁) + k²F(φ, k)
- (1 + k')α₁² R_C(c₁, c₁ - α₁²)`. -/
@[dlmf 19.8.E14, dlmf 19.8.E15]
theorem incompleteEllipticPi_landen_descending {k φ α2 : ℝ} (hk0 : 0 < k)
    (hk1 : k < 1) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) (hα1 : α2 ≠ 1) (hαk : α2 ≠ k ^ 2) :
    let kp := Real.sqrt (1 - k ^ 2)
    let k₁ := (1 - kp) / (1 + kp)
    let φ₁ := φ + Real.arctan (kp * Real.tan φ)
    let ω2 : ℝ := (k ^ 2 - α2) / (1 - α2)
    let α12 : ℝ := α2 * ω2 / (1 + kp) ^ 2
    let c₁ : ℝ := 1 / Real.sin φ₁ ^ 2
    (2 * (k ^ 2 - α2) : ℝ) * incompleteEllipticPi φ α2 k =
      ((ω2 - α2) / (1 + kp) : ℝ) * incompleteEllipticPi φ₁ α12 k₁ + (k ^ 2 : ℝ) *
          incompleteEllipticF φ k -
        ((1 + kp) * α12 : ℝ) * symmetricEllipticRC c₁ (c₁ - α12 : ℝ) := by
  sorry

/-! ### §19.8(iii) Gauss transformation -/

/-- `((1/s²)^{1/2})` for `s > 0`. -/
private lemma inv_sq_cpow_half {s : ℝ} (hs : 0 < s) :
    (((1 / s ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)) = ((1 / s : ℝ) : ℂ) := by
  rw [Carlson.ofReal_cpow_half (by positivity), Real.sqrt_div' _ (by positivity),
    Real.sqrt_one, Real.sqrt_sq hs.le]

/-- `F(φ, k) = sin φ R_F(cos²φ, Δ², 1)` for real `0 < φ < π/2` and `k² sin²φ < 1`. -/
private lemma incompleteEllipticF_eq_sin_mul_symmetricEllipticRF {φ k : ℝ} (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) :
    incompleteEllipticF φ k = (Real.sin φ : ℂ) *
      symmetricEllipticRF ((Real.cos φ ^ 2 : ℝ) : ℂ) ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) 1 := by
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  rw [incompleteEllipticF_eq_symmetricEllipticRF' hφ0 hφ1.le]
  have hsc := Real.sin_sq_add_cos_sq φ
  have h := symmetricEllipticRF_scale (l := 1 / Real.sin φ ^ 2) (by positivity)
    ((Real.cos φ ^ 2 : ℝ) : ℂ) ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) 1
  rw [inv_sq_cpow_half hs] at h
  have e1 : (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1) =
      ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) * ((Real.cos φ ^ 2 : ℝ) : ℂ) := by
    rw [← ofReal_one, ← ofReal_sub, ← ofReal_mul]; congr 1; field_simp; linarith
  have e2 : (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - (k : ℂ) ^ 2) =
      ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) * ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) := by
    rw [← ofReal_pow, ← ofReal_sub, ← ofReal_mul]; congr 1; field_simp
  rw [mul_one] at h
  rw [e1, e2, h, ← ofReal_inv, one_div, inv_inv]

/-- `E(φ, k) = (2/sin φ) R_G(cos²φ, Δ², 1) - (cos²φ/sin φ) R_F(cos²φ, Δ², 1) - cos φ Δ/sin φ`
for real `0 < φ < π/2` and `k² sin²φ < 1`, `Δ = √(1 - k² sin²φ)`. -/
private lemma incompleteEllipticE_eq_symmetricEllipticRG_sin {φ k : ℝ} (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2)
    (hk : k ^ 2 * Real.sin φ ^ 2 < 1) :
    incompleteEllipticE φ k =
      ((2 / Real.sin φ : ℝ) : ℂ) *
          symmetricEllipticRG ((Real.cos φ ^ 2 : ℝ) : ℂ) ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) 1 -
        ((Real.cos φ ^ 2 / Real.sin φ : ℝ) : ℂ) *
          symmetricEllipticRF ((Real.cos φ ^ 2 : ℝ) : ℂ) ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) 1 -
        ((Real.cos φ * √(1 - k ^ 2 * Real.sin φ ^ 2) / Real.sin φ : ℝ) : ℂ) := by
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hφ1⟩
  have hD : 0 < 1 - k ^ 2 * Real.sin φ ^ 2 := by linarith
  have hsc := Real.sin_sq_add_cos_sq φ
  have hkc : 1 - (k : ℂ) ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane := by
    rw [← ofReal_pow, ← ofReal_pow, ← ofReal_mul, ← ofReal_one, ← ofReal_sub]
    exact ofReal_mem_slitPlane.mpr hD
  rw [incompleteEllipticE_eq_symmetricEllipticRG hφ0 hφ1.le hkc]
  have hG := symmetricEllipticRG_scale (l := 1 / Real.sin φ ^ 2) (by positivity)
    ((Real.cos φ ^ 2 : ℝ) : ℂ) ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) 1
  have hF := symmetricEllipticRF_scale (l := 1 / Real.sin φ ^ 2) (by positivity)
    ((Real.cos φ ^ 2 : ℝ) : ℂ) ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) 1
  rw [inv_sq_cpow_half hs, mul_one] at hG hF
  have e1 : (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1) =
      ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) * ((Real.cos φ ^ 2 : ℝ) : ℂ) := by
    rw [← ofReal_one, ← ofReal_sub, ← ofReal_mul]; congr 1; field_simp; linarith
  have e2 : (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - (k : ℂ) ^ 2) =
      ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) * ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) := by
    rw [← ofReal_pow, ← ofReal_sub, ← ofReal_mul]; congr 1; field_simp
  have hsq : ((((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1) ^ (1 / 2 : ℂ) *
      (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - (k : ℂ) ^ 2) ^ (1 / 2 : ℂ) /
        ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)) =
      ((Real.cos φ * √(1 - k ^ 2 * Real.sin φ ^ 2) / Real.sin φ : ℝ) : ℂ) := by
    rw [e1, e2, ← ofReal_mul, ← ofReal_mul, Carlson.ofReal_cpow_half (by positivity),
      Carlson.ofReal_cpow_half (by positivity), Carlson.ofReal_cpow_half (by positivity),
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le]
    have h1 : √(1 / Real.sin φ ^ 2) = 1 / Real.sin φ := by
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_one, Real.sqrt_sq hs.le]
    rw [h1]
    push_cast
    field_simp
  rw [hsq, e1, e2, hG, hF]
  push_cast
  field_simp

/-- Landen's transformation of `R_F` and `R_G` (Carlson, Theorem 9.5-1 and Exercise 9.5-5) for
DLMF's integrals: for positive `x, y, z, v, w` with `v² + w² = z² + xy`, `vw = z(x + y)/2`. -/
private lemma symmetricElliptic_landen {x y z v w : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hv : 0 < v) (hw : 0 < w) (hv2 : v ^ 2 + w ^ 2 = z ^ 2 + x * y)
    (hvw : v * w = z * ((x + y) / 2)) :
    symmetricEllipticRF ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) ((z ^ 2 : ℝ) : ℂ) =
        symmetricEllipticRF ((((x + y) / 2) ^ 2 : ℝ) : ℂ) ((v ^ 2 : ℝ) : ℂ) ((w ^ 2 : ℝ) : ℂ) ∧
      2 * symmetricEllipticRG ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) ((z ^ 2 : ℝ) : ℂ) =
        4 * symmetricEllipticRG ((((x + y) / 2) ^ 2 : ℝ) : ℂ) ((v ^ 2 : ℝ) : ℂ) ((w ^ 2 : ℝ) : ℂ) -
          x * y * symmetricEllipticRF ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ)
              ((z ^ 2 : ℝ) : ℂ) - z := by
  have sl : ∀ {r : ℝ}, 0 < r → ((r ^ 2 : ℝ) : ℂ) ∈ slitPlane := fun hr =>
    ofReal_mem_slitPlane.mpr (by positivity)
  have hu : 0 < (x + y) / 2 := by positivity
  rw [symmetricEllipticRF_eq_carlsonRF (sl hx) (sl hy) (sl hz),
    symmetricEllipticRF_eq_carlsonRF (sl hu) (sl hv) (sl hw),
    symmetricEllipticRG_eq_carlsonRG (sl hx) (sl hy) (sl hz),
    symmetricEllipticRG_eq_carlsonRG (sl hu) (sl hv) (sl hw)]
  exact ⟨Carlson.carlsonRF_landen hx hy hz hv hw hv2 hvw,
    Carlson.carlsonRG_landen hx hy hz hv hw hv2 hvw⟩

/-- DLMF 19.8.18–19.8.19 (descending Gauss transformation): for real `0 < k < 1` and
`0 < φ < π/2`, with `k₁ = (1 - k')/(1 + k')`, `Δ = √(1 - k² sin²φ)` and
`sin ψ₁ = (1 + k') sin φ/(1 + Δ)`:
`F(φ, k) = (1 + k₁)F(ψ₁, k₁)` and `E(φ, k) = (1 + k')E(ψ₁, k₁) - k'F(φ, k) + (1 - Δ) cot φ`. -/
@[dlmf 19.8.E18, dlmf 19.8.E19]
theorem incEllInt_gauss {k φ : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 < φ) (hφ1 : φ < π / 2) :
    let kp := Real.sqrt (1 - k ^ 2)
    let k₁ := (1 - kp) / (1 + kp)
    let Δ := Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2)
    let ψ₁ := Real.arcsin ((1 + kp) * Real.sin φ / (1 + Δ))
    incompleteEllipticF φ k = (1 + k₁ : ℝ) * incompleteEllipticF ψ₁ k₁ ∧
      incompleteEllipticE φ k = (1 + kp : ℝ) * incompleteEllipticE ψ₁ k₁ - kp *
          incompleteEllipticF φ k +
        ((1 - Δ) * Real.cot φ : ℝ) := by
  intro kp k₁ Δ ψ₁
  set s := Real.sin φ with hsdef
  set c := Real.cos φ with hcdef
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hc : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith, hφ1⟩
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
  have hs1 : s < 1 := by nlinarith
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hkp2 : kp ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by linarith)
  have hkp0 : 0 < kp := Real.sqrt_pos.mpr (by linarith)
  have hkp1 : kp < 1 := by nlinarith
  have hD0 : 0 < 1 - k ^ 2 * s ^ 2 := by nlinarith
  have hΔ2 : Δ ^ 2 = 1 - k ^ 2 * s ^ 2 := Real.sq_sqrt hD0.le
  have hΔ0 : 0 < Δ := Real.sqrt_pos.mpr hD0
  have hΔkp : kp ≤ Δ := by nlinarith
  set a := (1 + kp) * s / (1 + Δ) with hadef
  have ha0 : 0 < a := by positivity
  have ha1 : a < 1 := by rw [hadef, div_lt_one (by linarith)]; nlinarith
  have hk10 : 0 ≤ k₁ := div_nonneg (by linarith) (by linarith)
  have hk11 : k₁ < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hsinψ : Real.sin ψ₁ = a := Real.sin_arcsin (by linarith) ha1.le
  have hcosψ : Real.cos ψ₁ ^ 2 = 1 - a ^ 2 := by
    rw [Real.cos_arcsin, Real.sq_sqrt (by nlinarith)]
  have hψ0 : 0 < ψ₁ := Real.arcsin_pos.mpr ha0
  have hψ1 : ψ₁ < π / 2 := Real.arcsin_lt_pi_div_two.mpr ha1
  set C1 := 1 - a ^ 2 with hC1def
  set D1 := 1 - k₁ ^ 2 * a ^ 2 with hD1def
  have hC1 : 0 < C1 := by nlinarith
  have hD1 : 0 < D1 := by nlinarith [mul_le_mul hk11.le ha1.le ha0.le zero_le_one]
  set u := (Δ + 1) / 2 with hudef
  have hu : 0 < u := by positivity
  have hua : u * a = (1 + kp) * s / 2 := by rw [hudef, hadef]; field_simp; ring
  have hk₁ : k₁ * (1 + kp) = 1 - kp := by simp only [k₁]; field_simp
  have huka : u * (k₁ * a) = (1 - kp) * s / 2 := by
    rw [show u * (k₁ * a) = k₁ * (u * a) by ring, hua]; linear_combination (s / 2) * hk₁
  -- Landen data
  set v := u * √C1 with hvdef
  set w := u * √D1 with hwdef
  have hv : 0 < v := by positivity
  have hw : 0 < w := by positivity
  have hv2' : v ^ 2 = u ^ 2 * C1 := by rw [hvdef, mul_pow, Real.sq_sqrt hC1.le]
  have hw2' : w ^ 2 = u ^ 2 * D1 := by rw [hwdef, mul_pow, Real.sq_sqrt hD1.le]
  have hsum : v ^ 2 + w ^ 2 = c ^ 2 + Δ * 1 := by
    rw [hv2', hw2', hC1def, hD1def]
    have e1 : u ^ 2 * a ^ 2 = ((1 + kp) * s / 2) ^ 2 := by rw [← hua]; ring
    have e2 : u ^ 2 * (k₁ ^ 2 * a ^ 2) = ((1 - kp) * s / 2) ^ 2 := by rw [← huka]; ring
    have e3 : u ^ 2 * (1 - a ^ 2) + u ^ 2 * (1 - k₁ ^ 2 * a ^ 2) =
        2 * u ^ 2 - u ^ 2 * a ^ 2 - u ^ 2 * (k₁ ^ 2 * a ^ 2) := by ring
    rw [e3, e1, e2, hudef]
    linear_combination (1 / 2 : ℝ) * hΔ2 - hsc - (s ^ 2 / 2) * hkp2
  have hprod : C1 * D1 = (c / u) ^ 2 := by
    have e1 : u ^ 2 * C1 = u ^ 2 - ((1 + kp) * s / 2) ^ 2 := by rw [hC1def, ← hua]; ring
    have e2 : u ^ 2 * D1 = u ^ 2 - ((1 - kp) * s / 2) ^ 2 := by rw [hD1def, ← huka]; ring
    have e3 : (u ^ 2 * C1) * (u ^ 2 * D1) = (u * c) ^ 2 := by
      rw [e1, e2, hudef]
      linear_combination (-(Δ + 1) ^ 2 / 4) * hsc +
        ((Δ ^ 2 + 4 * Δ - kp ^ 2 * s ^ 2 + s ^ 2 + 3) / 16) * hΔ2 +
        (-(Δ ^ 2 + 4 * Δ - kp ^ 2 * s ^ 2 + s ^ 2 + 3) / 16 * s ^ 2) * hkp2
    have hu2 : u ^ 2 ≠ 0 := by positivity
    have h4 := mul_left_cancel₀ hu2
      (show u ^ 2 * (C1 * D1 * u ^ 2) = u ^ 2 * c ^ 2 by linear_combination e3)
    rw [div_pow, eq_div_iff hu2]
    linarith
  have hCD : √C1 * √D1 = c / u := by
    rw [← Real.sqrt_mul hC1.le, hprod, Real.sqrt_sq (by positivity)]
  have hvw : v * w = c * ((Δ + 1) / 2) := by
    rw [hvdef, hwdef, ← hudef, show u * √C1 * (u * √D1) = u * u * (√C1 * √D1) by ring, hCD]
    field_simp
  obtain ⟨hLF, hLG⟩ := symmetricElliptic_landen hΔ0 one_pos hc hv hw hsum hvw
  simp only [hv2', hw2', one_pow, ofReal_one, mul_one, ofReal_mul] at hLF hLG
  -- scaling
  have hFs := symmetricEllipticRF_scale (l := u ^ 2) (by positivity) 1 (C1 : ℂ) (D1 : ℂ)
  have hGs := symmetricEllipticRG_scale (l := u ^ 2) (by positivity) 1 (C1 : ℂ) (D1 : ℂ)
  rw [mul_one, Carlson.ofReal_cpow_half (by positivity), Real.sqrt_sq hu.le] at hFs hGs
  have eF1 : symmetricEllipticRF 1 (C1 : ℂ) (D1 : ℂ) = symmetricEllipticRF (C1 : ℂ) (D1 : ℂ) 1 :=
    (symmetricEllipticRF_comm_left _ _ _).trans (symmetricEllipticRF_comm_right _ _ _)
  have eG1 : symmetricEllipticRG 1 (C1 : ℂ) (D1 : ℂ) = symmetricEllipticRG (C1 : ℂ) (D1 : ℂ) 1 :=
    (symmetricEllipticRG_comm_left _ _ _).trans (symmetricEllipticRG_comm_right _ _ _)
  rw [hFs, eF1] at hLF
  rw [← hudef, hGs, eG1, hLF] at hLG
  have eF0 : symmetricEllipticRF ((c ^ 2 : ℝ) : ℂ) ((1 - k ^ 2 * s ^ 2 : ℝ) : ℂ) 1 =
      symmetricEllipticRF ((Δ ^ 2 : ℝ) : ℂ) 1 ((c ^ 2 : ℝ) : ℂ) := by
    rw [hΔ2]; exact (symmetricEllipticRF_comm_left _ _ _).trans
        (symmetricEllipticRF_comm_right _ _ _)
  have eG0 : symmetricEllipticRG ((c ^ 2 : ℝ) : ℂ) ((1 - k ^ 2 * s ^ 2 : ℝ) : ℂ) 1 =
      symmetricEllipticRG ((Δ ^ 2 : ℝ) : ℂ) 1 ((c ^ 2 : ℝ) : ℂ) := by
    rw [hΔ2]; exact (symmetricEllipticRG_comm_left _ _ _).trans
        (symmetricEllipticRG_comm_right _ _ _)
  have hF0 := incompleteEllipticF_eq_sin_mul_symmetricEllipticRF (k := k) hφ0 hφ1
  have hE0 := incompleteEllipticE_eq_symmetricEllipticRG_sin (k := k) hφ0 hφ1 (by linarith)
  have hF1 := incompleteEllipticF_eq_sin_mul_symmetricEllipticRF (k := k₁) hψ0 hψ1
  have hE1 := incompleteEllipticE_eq_symmetricEllipticRG_sin (k := k₁) hψ0 hψ1
    (by have h := hD1; rw [hD1def] at h; rw [hsinψ]; linarith)
  have hcosψ' : Real.cos ψ₁ = √C1 := Real.cos_arcsin _
  rw [hsinψ, hcosψ, ← hD1def] at hF1 hE1
  rw [hcosψ'] at hE1
  rw [eF0, hLF] at hF0
  rw [eF0, eG0, hLF] at hE0
  have hΔdef : √(1 - k ^ 2 * s ^ 2) = Δ := rfl
  rw [← hsdef] at hF0
  rw [← hsdef, ← hcdef, hΔdef] at hE0
  have hG0 : symmetricEllipticRG ((Δ ^ 2 : ℝ) : ℂ) 1 ((c ^ 2 : ℝ) : ℂ) =
      (4 * ((u : ℂ) * symmetricEllipticRG (C1 : ℂ) (D1 : ℂ) 1) -
        (Δ : ℂ) * ((u : ℂ)⁻¹ * symmetricEllipticRF (C1 : ℂ) (D1 : ℂ) 1) - c) / 2 := by
    linear_combination hLG / 2
  rw [hG0] at hE0
  have hkey : s * u⁻¹ = (1 + k₁) * a := by
    field_simp
    linear_combination (-(1 + k₁)) * hua - (s / 2) * hk₁
  have hA : 4 * u / s = 2 * (1 + kp) / a := by
    field_simp
    linear_combination 4 * hua
  have hB : (Δ + c ^ 2) / (s * u) = (1 + kp) * C1 / a + kp * s / u := by
    rw [hC1def, hadef, hudef]
    have h1Δ : 1 + Δ ≠ 0 := by positivity
    field_simp
    linear_combination (1 + Δ) * (2 * hsc - hΔ2 + s ^ 2 * hkp2)
  have hC : (1 + kp) * (√C1 * √D1) / a = 2 * c / s := by
    rw [hCD]
    have := ha0.ne'
    have := hu.ne'
    have := hs.ne'
    have h1Δ : 1 + Δ ≠ 0 := by positivity
    rw [hadef, hudef]
    field_simp
    ring
  have hA' : (4 * u / s : ℂ) = 2 * (1 + kp) / a := by exact_mod_cast hA
  have hB' : ((Δ + c ^ 2) / (s * u) : ℂ) = (1 + kp) * C1 / a + kp * s / u := by
    exact_mod_cast hB
  have hC' : ((1 + kp) * ((√C1 : ℝ) * (√D1 : ℝ)) / a : ℂ) = 2 * c / s := by exact_mod_cast hC
  have hF : incompleteEllipticF φ k = ((1 + k₁ : ℝ) : ℂ) * incompleteEllipticF ψ₁ k₁ := by
    rw [hF0, hF1, ← mul_assoc, ← mul_assoc, ← ofReal_inv, ← ofReal_mul, ← ofReal_mul, hkey]
  refine ⟨hF, ?_⟩
  rw [hE0, hE1, hF0, Real.cot_eq_cos_div_sin, ← hsdef, ← hcdef]
  push_cast
  linear_combination symmetricEllipticRG (C1 : ℂ) (D1 : ℂ) 1 * hA' -
    symmetricEllipticRF (C1 : ℂ) (D1 : ℂ) 1 * hB' + hC'

/-- The ascending Landen transformation for `0 < φ < π/2`, from Landen's transformation of
`R_F`, `R_G` with the assignment `(cos φ, Δ, 1)`. -/
private theorem incEllInt_landen_ascending_of_lt {k φ : ℝ} (hk0 : 0 < k) (hk1 : k < 1)
    (hφ0 : 0 < φ) (hφ1 : φ < π / 2) :
    let k₂ := 2 * Real.sqrt k / (1 + k)
    let φ₂ := (φ + Real.arcsin (k * Real.sin φ)) / 2
    incompleteEllipticF φ k = (2 / (1 + k) : ℝ) * incompleteEllipticF φ₂ k₂ ∧
      incompleteEllipticE φ k = (1 + k : ℝ) * incompleteEllipticE φ₂ k₂ + (1 - k : ℝ) *
          incompleteEllipticF φ₂ k₂ -
        (k * Real.sin φ : ℝ) := by
  intro k₂ φ₂
  set s := Real.sin φ with hsdef
  set c := Real.cos φ with hcdef
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hc : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith, hφ1⟩
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
  have hs1 : s < 1 := by nlinarith
  have hks0 : 0 < k * s := by positivity
  have hks1 : k * s < 1 := by nlinarith
  have hD0 : 0 < 1 - k ^ 2 * s ^ 2 := by nlinarith
  set Δ := √(1 - k ^ 2 * s ^ 2) with hΔdef
  have hΔ2 : Δ ^ 2 = 1 - k ^ 2 * s ^ 2 := Real.sq_sqrt hD0.le
  have hΔ0 : 0 < Δ := Real.sqrt_pos.mpr hD0
  set θ := Real.arcsin (k * s) with hθdef
  have hθs : Real.sin θ = k * s := Real.sin_arcsin (by linarith) hks1.le
  have hθc : Real.cos θ = Δ := by
    rw [hθdef, Real.cos_arcsin, hΔdef]; ring_nf
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr hks0
  have hθ1 : θ < π / 2 := Real.arcsin_lt_pi_div_two.mpr hks1
  have hφ₂0 : 0 < φ₂ := by simp only [φ₂]; linarith
  have hφ₂1 : φ₂ < π / 2 := by simp only [φ₂]; linarith
  have hcos2 : Real.cos (2 * φ₂) = c * Δ - k * s ^ 2 := by
    rw [show 2 * φ₂ = φ + θ by simp only [φ₂]; ring, Real.cos_add, hθs, hθc]; ring
  set A := (1 - c * Δ + k * s ^ 2) / 2 with hAdef
  set B := (1 + c * Δ - k * s ^ 2) / 2 with hBdef
  set s₂ := Real.sin φ₂ with hs₂def
  set c₂ := Real.cos φ₂ with hc₂def
  have hs₂ : 0 < s₂ := Real.sin_pos_of_pos_of_lt_pi hφ₂0 (by linarith)
  have hc₂ : 0 < c₂ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hφ₂1⟩
  have hsc₂ : s₂ ^ 2 + c₂ ^ 2 = 1 := Real.sin_sq_add_cos_sq φ₂
  have hc22 : c₂ ^ 2 = B := by
    have := Real.cos_two_mul φ₂
    rw [hcos2] at this
    rw [hBdef]; linarith
  have hs22 : s₂ ^ 2 = A := by rw [hAdef]; linarith
  have hB : 0 < B := by rw [← hc22]; positivity
  have hA : 0 < A := by rw [← hs22]; positivity
  have hk₂ : k₂ ^ 2 = 4 * k / (1 + k) ^ 2 := by
    simp only [k₂]; rw [div_pow, mul_pow, Real.sq_sqrt hk0.le]; ring
  set u := (c + Δ) / 2 with hudef
  have hu : 0 < u := by positivity
  set D2 := 1 - k₂ ^ 2 * s₂ ^ 2 with hD2def
  have hD2' : D2 = 1 - 4 * k * A / (1 + k) ^ 2 := by rw [hD2def, hk₂, hs22]; ring
  have hk1' : (1 + k) ^ 2 ≠ 0 := by positivity
  have I1 : u ^ 2 * D2 = B ^ 2 := by
    rw [hD2']
    have h : u ^ 2 * ((1 + k) ^ 2 - 4 * k * A) = B ^ 2 * (1 + k) ^ 2 := by
      rw [hudef, hAdef, hBdef]
      linear_combination
        (-(Δ ^ 2 * k ^ 2 - 2 * Δ ^ 2 * k + Δ ^ 2 - 2 * Δ * c * k + 2 * k ^ 2 * s ^ 2 - k ^ 2 - 1)
          / 4) * hsc +
        (-(-2 * Δ * c * k + k ^ 2 * s ^ 2 + 2 * k * s ^ 2 - 2 * k - s ^ 2) / 4) * hΔ2
    field_simp
    linear_combination h
  have I2 : 4 * u ^ 2 * A = B * s ^ 2 * (1 + k) ^ 2 := by
    rw [hudef, hAdef, hBdef]
    linear_combination ((-2 * Δ ^ 2 - Δ * c + k * s ^ 2 + 1) / 2) * hsc +
      ((-Δ * c + k * s ^ 2 + 2 * s ^ 2 - 1) / 2) * hΔ2
  have I3 : 2 * c * (c + Δ) * A = s ^ 2 * (1 + k) * ((1 + k) * B - (1 - k) * A) := by
    rw [hAdef, hBdef]
    linear_combination (-Δ ^ 2 - Δ * c + k * s ^ 2 + 1) * hsc + ((s - 1) * (s + 1)) * hΔ2
  have hD2 : 0 < D2 := by
    by_contra h; push Not at h; nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg u) h]
  have hΔ₂ : √D2 = B / u := by
    rw [show D2 = (B / u) ^ 2 by field_simp; linarith, Real.sqrt_sq (by positivity)]
  set l := u ^ 2 / B with hldef
  have hl : 0 < l := by positivity
  set μ := √l with hμdef
  have hμ : 0 < μ := Real.sqrt_pos.mpr hl
  have hμ2 : μ ^ 2 = l := Real.sq_sqrt hl.le
  set w := μ * (B / u) with hwdef
  have hw : 0 < w := by positivity
  have hv2 : μ ^ 2 + w ^ 2 = 1 ^ 2 + c * Δ := by
    rw [hwdef, mul_pow, hμ2, ← hΔ₂, Real.sq_sqrt hD2.le, hldef, hD2']
    have h : u ^ 2 * (2 * (1 + k) ^ 2 - 4 * k * A) = (1 + c * Δ) * B * (1 + k) ^ 2 := by
      rw [hudef, hAdef, hBdef]
      linear_combination
        (-(Δ ^ 2 * k ^ 2 + Δ ^ 2 - Δ * c * k + k ^ 2 * s ^ 2 - k ^ 2 - k - 1) / 2) * hsc +
        ((Δ * c * k + k + s ^ 2) / 2) * hΔ2
    field_simp
    linear_combination h
  have hvw : μ * w = 1 * ((c + Δ) / 2) := by
    rw [hwdef, ← mul_assoc, ← sq, hμ2, hldef, ← hudef]
    field_simp
  -- key relations
  have hK : 2 * s₂ * μ = s * (1 + k) := by
    rw [← pow_left_inj₀ (by positivity) (by positivity) two_ne_zero, mul_pow, mul_pow, hμ2,
      hs22, hldef, mul_pow]
    field_simp
    linear_combination I2
  have hK2 : 2 * u * s₂ = s * (1 + k) * c₂ := by
    rw [← pow_left_inj₀ (by positivity) (by positivity) two_ne_zero, mul_pow, mul_pow, mul_pow,
      mul_pow, hs22, hc22]
    linear_combination I2
  obtain ⟨hLF, hLG⟩ := symmetricElliptic_landen hc hΔ0 one_pos hμ hw hv2 hvw
  have eu : ((c + Δ) / 2) ^ 2 = l * B := by rw [hldef, ← hudef]; field_simp
  have ew : w ^ 2 = l * D2 := by
    rw [hwdef, mul_pow, hμ2, ← hΔ₂, Real.sq_sqrt hD2.le]
  rw [eu, hμ2, ew, hΔ2] at hLF hLG
  simp only [one_pow, ofReal_one, ofReal_mul] at hLF hLG
  have hFs := symmetricEllipticRF_scale hl (B : ℂ) 1 (D2 : ℂ)
  have hGs := symmetricEllipticRG_scale hl (B : ℂ) 1 (D2 : ℂ)
  rw [mul_one, Carlson.ofReal_cpow_half hl.le, ← hμdef,
    symmetricEllipticRF_comm_right (B : ℂ) (D2 : ℂ) 1] at hFs
  rw [mul_one, Carlson.ofReal_cpow_half hl.le, ← hμdef,
    symmetricEllipticRG_comm_right (B : ℂ) (D2 : ℂ) 1] at hGs
  rw [hFs] at hLF
  rw [hGs, hLF] at hLG
  have hF0 := incompleteEllipticF_eq_sin_mul_symmetricEllipticRF (k := k) hφ0 hφ1
  have hE0 := incompleteEllipticE_eq_symmetricEllipticRG_sin (k := k) hφ0 hφ1 (by linarith)
  have hF1 := incompleteEllipticF_eq_sin_mul_symmetricEllipticRF (k := k₂) hφ₂0 hφ₂1
  have hE1 := incompleteEllipticE_eq_symmetricEllipticRG_sin (k := k₂) hφ₂0 hφ₂1 (by
    have h := hD2; rw [hD2def] at h; linarith)
  rw [← hs₂def, ← hc₂def, hc22, ← hD2def] at hF1 hE1
  rw [← hsdef, ← hcdef] at hF0 hE0
  rw [hLF] at hF0
  rw [hΔ₂] at hE1
  have hcoef : s * μ⁻¹ = 2 / (1 + k) * s₂ := by
    field_simp; linear_combination -hK
  constructor
  · rw [hF0, hF1, ← mul_assoc, ← mul_assoc, ← ofReal_inv, ← ofReal_mul, ← ofReal_mul, hcoef]
  have hμi : μ⁻¹ = 2 * s₂ / (s * (1 + k)) := by
    rw [← hK]; field_simp
  have hG' : 4 * μ / s = 2 * (1 + k) / s₂ := by
    field_simp; linear_combination 2 * hK
  have hF' : (c * Δ + c ^ 2) * μ⁻¹ / s = (1 + k) * B / s₂ - (1 - k) * s₂ := by
    rw [hμi]
    have key : 2 * (c * Δ + c ^ 2) * s₂ ^ 2 =
        s ^ 2 * (1 + k) * ((1 + k) * B - (1 - k) * s₂ ^ 2) := by
      rw [hs22]; linear_combination I3
    field_simp
    linear_combination key
  have hC' : (1 + c * Δ) / s = (1 + k) * (c₂ * (B / u)) / s₂ + k * s := by
    field_simp
    rw [hBdef]
    linear_combination ((1 + c * Δ - k * s ^ 2) / 2) * hK2
  rw [hE0, hE1, hF1, ← hΔdef]
  have hGc : (4 * μ / s : ℂ) = 2 * (1 + k) / s₂ := by exact_mod_cast hG'
  have hFc : ((c * Δ + c ^ 2) * (μ : ℂ)⁻¹ / s : ℂ) = (1 + k) * B / s₂ - (1 - k) * s₂ := by
    exact_mod_cast hF'
  have hCc : ((1 + c * Δ) / s : ℂ) = (1 + k) * (c₂ * (B / u)) / s₂ + k * s := by
    exact_mod_cast hC'
  push_cast at hLF hLG ⊢
  linear_combination (1 / (s : ℂ)) * hLG - ((c : ℂ) ^ 2 / s) * hLF +
    symmetricEllipticRG (B : ℂ) (D2 : ℂ) 1 * hGc -
        symmetricEllipticRF (B : ℂ) (D2 : ℂ) 1 * hFc - hCc

/-- For real `k` with `k² < 1`, `φ ↦ ∫₀^φ (1 - k² sin²θ)^e dθ` is continuous. -/
private lemma continuous_integral_one_sub_sq_mul_sin_sq_cpow {k : ℝ} (hk : k ^ 2 < 1) (e : ℂ) :
    Continuous fun φ : ℝ =>
      ∫ θ in (0 : ℝ)..φ, (1 - (k : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ e := by
  have hc : Continuous fun θ : ℝ => (1 - (k : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ e := by
    refine continuous_iff_continuousAt.2 fun θ => ?_
    refine (continuousAt_cpow_const ?_).comp (f := fun θ : ℝ =>
      1 - (k : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2) (by fun_prop)
    have h1 : 1 - (k : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2 = ((1 - k ^ 2 * Real.sin θ ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [h1]
    exact ofReal_mem_slitPlane.mpr (by nlinarith [Real.sin_sq_le_one θ, sq_nonneg k])
  exact intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0

/-- Two functions continuous at `b` that agree on `(a, b)` agree at `b`. -/
private lemma eq_of_continuousAt_of_eqOn_Ioo {f g : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousAt f b) (hg : ContinuousAt g b) (h : ∀ x ∈ Ioo a b, f x = g x) :
    f b = g b := by
  have h1 : Tendsto f (𝓝[<] b) (𝓝 (f b)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto f (𝓝[<] b) (𝓝 (g b)) :=
    (hg.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (eventually_of_mem (Ioo_mem_nhdsLT hab) fun x hx => (h x hx).symm)
  exact tendsto_nhds_unique h1 h2

/-- DLMF 19.8.16–19.8.17 (ascending Landen transformation): for real `0 < k < 1`
and `0 < φ ≤ π/2`, with `k₂ = 2√k/(1 + k)` and `2φ₂ = φ + arcsin(k sin φ)`:
`F(φ, k) = (2/(1 + k))F(φ₂, k₂)` and
`E(φ, k) = (1 + k)E(φ₂, k₂) + (1 - k)F(φ₂, k₂) - k sin φ`. -/
@[dlmf 19.8.E16, dlmf 19.8.E17]
theorem incEllInt_landen_ascending {k φ : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 < φ)
    (hφ1 : φ ≤ π / 2) :
    let k₂ := 2 * Real.sqrt k / (1 + k)
    let φ₂ := (φ + Real.arcsin (k * Real.sin φ)) / 2
    incompleteEllipticF φ k = (2 / (1 + k) : ℝ) * incompleteEllipticF φ₂ k₂ ∧
      incompleteEllipticE φ k = (1 + k : ℝ) * incompleteEllipticE φ₂ k₂ + (1 - k : ℝ) *
          incompleteEllipticF φ₂ k₂ -
        (k * Real.sin φ : ℝ) := by
  intro k₂ φ₂
  rcases hφ1.lt_or_eq with h | h
  · exact incEllInt_landen_ascending_of_lt hk0 hk1 hφ0 h
  have hk : k ^ 2 < 1 := by nlinarith
  have hk₂ : k₂ ^ 2 < 1 := by
    simp only [k₂]
    rw [div_pow, mul_pow, Real.sq_sqrt hk0.le, div_lt_one (by positivity)]
    nlinarith
  have hFc := continuous_integral_one_sub_sq_mul_sin_sq_cpow hk (-(1 / 2 : ℂ))
  have hEc := continuous_integral_one_sub_sq_mul_sin_sq_cpow hk (1 / 2 : ℂ)
  have hFc₂ := continuous_integral_one_sub_sq_mul_sin_sq_cpow hk₂ (-(1 / 2 : ℂ))
  have hEc₂ := continuous_integral_one_sub_sq_mul_sin_sq_cpow hk₂ (1 / 2 : ℂ)
  have hψ : Continuous fun x : ℝ => (x + Real.arcsin (k * Real.sin x)) / 2 := by fun_prop
  have hpi : (0 : ℝ) < π / 2 := by positivity
  subst h
  constructor
  · refine eq_of_continuousAt_of_eqOn_Ioo (f := fun x : ℝ => incompleteEllipticF x k)
      (g := fun x : ℝ => ((2 / (1 + k) : ℝ) : ℂ) *
        incompleteEllipticF ((x + Real.arcsin (k * Real.sin x)) / 2 : ℝ) k₂) hpi ?_ ?_
      (fun x hx => (incEllInt_landen_ascending_of_lt hk0 hk1 hx.1 hx.2).1)
    · simp only [incompleteEllipticF_ofReal_eq_integral]; exact hFc.continuousAt
    · simp only [incompleteEllipticF_ofReal_eq_integral]
      exact (continuous_const.mul (hFc₂.comp hψ)).continuousAt
  · refine eq_of_continuousAt_of_eqOn_Ioo (f := fun x : ℝ => incompleteEllipticE x k)
      (g := fun x : ℝ => ((1 + k : ℝ) : ℂ) *
        incompleteEllipticE ((x + Real.arcsin (k * Real.sin x)) / 2 : ℝ) k₂ + ((1 - k : ℝ) : ℂ) *
        incompleteEllipticF ((x + Real.arcsin (k * Real.sin x)) / 2 : ℝ) k₂ -
            ((k * Real.sin x : ℝ) : ℂ))
      hpi ?_ ?_ (fun x hx => (incEllInt_landen_ascending_of_lt hk0 hk1 hx.1 hx.2).2)
    · simp only [incompleteEllipticE_ofReal_eq_integral]; exact hEc.continuousAt
    · simp only [incompleteEllipticF_ofReal_eq_integral, incompleteEllipticE_ofReal_eq_integral]
      exact ((continuous_const.mul (hEc₂.comp hψ)).add (continuous_const.mul (hFc₂.comp hψ))
        |>.sub (by fun_prop)).continuousAt

/-- **Admitted.** DLMF 19.8.20–19.8.21: for real `0 < k < 1`, `0 < φ < π/2` and real `α² ≠ 0`
with `α² ≠ c = csc²φ`, with `ρ = √(1 - k²/α²)` (pure imaginary if `0 < α² < k²`),
`α₁² = α²(1 + ρ)²/(1 + k')²` and the Gauss data of 19.8.18:
`ρΠ(φ, α², k) = (4/(1 + k'))Π(ψ₁, α₁², k₁) + (ρ - 1)F(φ, k) - R_C(c - 1, c - α²)`. -/
@[dlmf 19.8.E20, dlmf 19.8.E21]
theorem incompleteEllipticPi_gauss {k φ α2 : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) (hα0 : α2 ≠ 0) (hαc : α2 ≠ 1 / Real.sin φ ^ 2) :
    let kp := Real.sqrt (1 - k ^ 2)
    let k₁ := (1 - kp) / (1 + kp)
    let Δ := Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2)
    let ψ₁ := Real.arcsin ((1 + kp) * Real.sin φ / (1 + Δ))
    let c := 1 / Real.sin φ ^ 2
    let ρ : ℂ := (1 - ((k ^ 2 / α2 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
    let α12 : ℂ := α2 * (1 + ρ) ^ 2 / (1 + kp) ^ 2
    ρ * incompleteEllipticPi φ α2 k = (4 / (1 + kp) : ℝ) * incompleteEllipticPi ψ₁ α12 k₁ +
      (ρ - 1) * incompleteEllipticF φ k - symmetricEllipticRC (c - 1 : ℝ) (c - α2 : ℝ) := by
  sorry

end DLMF.EllipticIntegrals
