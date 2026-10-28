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

* §19.8(i): Gauss's arithmetic-geometric mean. DLMF's sequences `aₙ, gₙ` (19.8.1) are
  `agmSeqA`, `agmSeqG`, read off Mathlib's `NNReal.agmSequences` (which lists
  `(g_{n+1}, a_{n+1})`); `M(a₀, g₀)` is Mathlib's `NNReal.agm`; `cₙ = √(aₙ² - gₙ²)` (19.8.2) is
  `agmSeqC`. The recursion (19.8.1), the convergence to `M` and 19.8.3 are proved; 19.8.5 for
  complex `k` with real `k² < 1` follows from the existing real
  `DLMF.Elliptic.Real.compEllIntKm_eq_pi_div_agm`. The sequences `pₙ, εₙ, Qₙ` of 19.8.8 are
  `agmPiSeq`. 19.8.6 is proved from `lean-codes`' `Carlson.hasSum_agmA_zero` and
  `Carlson.carlsonRE_eq_agm` (Carlson, Exercises 9.5-3/9.5-4), with `E(k) = (π/2) R_E(1, k'²)`
  and `K(k) = (π/2) R_K(1, k'²)` from 19.25.1, for all real `k² < 1`.
* §19.8(ii)–(iii): Landen and Gauss transformations, for real `0 < k < 1` and real amplitudes
  as in DLMF's notes; 19.8.12 for real `k² < 1` is proved from the existing real
  `Real.compEllIntKm_landen_descending` and `Real.compEllIntEm_landen_descending`, and for
  complex `k` with `1 - k² ∈ ℂ \ (-∞, 0]` from the real case by the identity theorem.
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
lemma ei19a_agmSeqG_le_agmSeqA {a₀ g₀ : ℝ≥0} (h : g₀ ≤ a₀) (n : ℕ) :
    agmSeqG a₀ g₀ n ≤ agmSeqA a₀ g₀ n := by
  cases n with
  | zero => exact h
  | succ n => exact NNReal.agmSequences_fst_le_snd n n

/-- Estimate under the stated parameter and domain assumptions: `0 < agmSeqA a₀ g₀ n`. -/
lemma ei19a_agmSeqA_pos {a₀ g₀ : ℝ≥0} (h : 0 < a₀) (n : ℕ) : 0 < agmSeqA a₀ g₀ n := by
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
  have hle := ei19a_agmSeqG_le_agmSeqA h n
  have hpos := ei19a_agmSeqA_pos (g₀ := g₀) (lt_of_lt_of_le hg h) n
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
  have hRF := symEllIntRF_zero_left hy hz
  rw [symEllIntR_of_mem _ _ (ei19c_slit2 hy hz)] at hRF
  have hRK : Carlson.carlsonR (-(1 / 2)) ![1 / 2, 1 / 2] ![((a₀ : ℝ) : ℂ) ^ 2, ((g₀ : ℝ) : ℂ) ^ 2] =
      Carlson.TwoVariable.carlsonRK (((a₀ : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) := by
    unfold Carlson.TwoVariable.carlsonRK Carlson.TwoVariable.pair
    congr 1; ring
  rw [hRK, hK, symEllIntRF] at hRF
  have hint : ∫ t in Ioi (0 : ℝ), (symEllIntS 0 (((a₀ : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) t)⁻¹ =
      ((∫ t in Ioi (0 : ℝ),
        (t * (t + (a₀ : ℝ) ^ 2) * (t + (g₀ : ℝ) ^ 2)) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    simp only [symEllIntS, add_zero]
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
theorem compEllIntKk_eq_pi_div_agm {k : ℂ} {m : ℝ} (hk : k ^ 2 = m) (hm : m < 1) :
    compEllIntKk k = π / (2 * (NNReal.agm 1 (NNReal.sqrt (1 - m).toNNReal) : ℝ)) := by
  rw [compEllIntKk_eq_ofReal hk hm.le, DLMF.Elliptic.Real.compEllIntKm_eq_pi_div_agm hm]
  push_cast; rfl

/-- Bridge between lean-codes' `Carlson.agmSeq` and DLMF's `agmSeqA`, `agmSeqG`. -/
lemma p19lR1_agmSeq_eq (a₀ g₀ : ℝ≥0) (n : ℕ) :
    Carlson.agmSeq a₀ g₀ n = ((agmSeqA a₀ g₀ n : ℝ), (agmSeqG a₀ g₀ n : ℝ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Carlson.agmSeq_succ, ih, (agmSeq_succ a₀ g₀ n).1, (agmSeq_succ a₀ g₀ n).2]
    simp [Carlson.agmStep, Real.coe_sqrt]

/-- Identity under the stated parameter and domain assumptions: `agmSeqC a₀ g₀ (n + 1) ^ 2 =
(agmSeqA a₀ g₀ (n + 1) : ℝ) ^ 2 - (agmSeqG a₀ g₀ (n + 1) : ℝ) ^ 2`. -/
lemma p19lR1_agmSeqC_sq_succ (a₀ g₀ : ℝ≥0) (n : ℕ) :
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
theorem compEllIntEk_eq_agm {k : ℂ} {m : ℝ} (hk : k ^ 2 = m) (hm : m < 1) :
    let g₀ : ℝ≥0 := NNReal.sqrt (1 - m).toNNReal
    HasSum (fun n : ℕ => (2 : ℝ) ^ ((n : ℤ) - 1) *
        ((agmSeqA 1 g₀ n : ℝ) ^ 2 - (agmSeqG 1 g₀ n : ℝ) ^ 2))
        (1 - (compEllIntEk k).re * (2 * (NNReal.agm 1 g₀ : ℝ)) / π) ∧
      compEllIntEk k = compEllIntKk k * ((agmSeqA 1 g₀ 1 : ℝ) ^ 2 -
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
  have hE : compEllIntEk k = (π / 2) * Carlson.carlsonRE (((1 : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) := by
    rw [(compEllIntEk_eq_symEllInt hslit).1, ← hg2,
      p19sR1_symEllIntRG_zero_eq_carlsonRE hg2s one_mem_slitPlane,
      p19sR1_carlsonRE_comm hg2s one_mem_slitPlane]
    push_cast; ring_nf
  have hK : compEllIntKk k =
      (π / 2) * Carlson.TwoVariable.carlsonRK (((1 : ℝ) : ℂ) ^ 2) (((g₀ : ℝ) : ℂ) ^ 2) := by
    rw [compEllIntKk_eq_symEllIntRF hslit, ← hg2,
      p19sR1_symEllIntRF_zero_eq_carlsonRK hg2s one_mem_slitPlane,
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
      ((agmSeqA 1 g₀ n : ℝ), (agmSeqG 1 g₀ n : ℝ)) := p19lR1_agmSeq_eq 1 g₀
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
        (1 - compEllIntEk k * (2 * ((NNReal.agm 1 g₀ : ℝ) : ℂ)) / π) := by
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
    rw [show (2 * ((NNReal.agm 1 g₀ : ℝ) : ℂ)) = ((2 * (NNReal.agm 1 g₀ : ℝ) : ℝ) : ℂ) by push_cast; ring,
      show (π : ℂ) = ((π : ℝ) : ℂ) from rfl]
    rw [Complex.sub_re, Complex.one_re, Complex.div_ofReal_re, Complex.re_mul_ofReal]
  · have h := Carlson.carlsonRE_eq_agm (x := 1) (y := g₀) one_pos hgpos
    rw [hE, hK, h]
    simp only [Carlson.agmX, Carlson.agmY]
    rw [show ((1 : ℝ)) = ((1 : ℝ≥0) : ℝ) from rfl]
    simp only [hseq]
    have hc : ∀ n : ℕ, agmSeqC 1 g₀ (n + 2) ^ 2 =
        (agmSeqA 1 g₀ (n + 2) : ℝ) ^ 2 - (agmSeqG 1 g₀ (n + 2) : ℝ) ^ 2 :=
      fun n => p19lR1_agmSeqC_sq_succ 1 g₀ (n + 1)
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
theorem compEllIntPik_eq_agm {k : ℂ} {m α2 : ℝ} (hk : k ^ 2 = m) (hm : m < 1) (hα : α2 < 1) :
    let g₀ : ℝ≥0 := NNReal.sqrt (1 - m).toNNReal
    ∃ S : ℝ, HasSum (fun n => (agmPiSeq g₀ (Real.sqrt (1 - α2)) n).2) S ∧
      compEllIntPik α2 k = π / (4 * (NNReal.agm 1 g₀ : ℝ)) * (2 + α2 / (1 - α2) * S) := by
  sorry

/-- **Admitted.** DLMF 19.8.9–19.8.10: for `-∞ < k² < 1` (`k² = m` real) and real
`1 < α²`, the Cauchy principal value is `Π(α², k) = (π/(4M(1, k'))) (k²/(k² - α²)) ∑ₙ Qₙ`,
with 19.8.8 started at `p₀² = 1 - k²/α²`. -/
@[dlmf 19.8.E9, dlmf 19.8.E10]
theorem compEllIntPik_eq_agm_of_one_lt {k : ℂ} {m α2 : ℝ} (hk : k ^ 2 = m) (hm : m < 1)
    (hα : 1 < α2) :
    let g₀ : ℝ≥0 := NNReal.sqrt (1 - m).toNNReal
    ∃ S : ℝ, HasSum (fun n => (agmPiSeq g₀ (Real.sqrt (1 - m / α2)) n).2) S ∧
      compEllIntPik α2 k = π / (4 * (NNReal.agm 1 g₀ : ℝ)) * (m / (m - α2)) * S := by
  sorry

/-! ### §19.8(ii) Landen transformations -/

/-- For real `k` with `k² ≤ 1`, the principal `k' = √(1 - k²)` is the real square root. -/
lemma ei19a_jacobiComodulusk_ofReal {k : ℝ} (hk : k ^ 2 ≤ 1) :
    jacobiComodulusk k = (Real.sqrt (1 - k ^ 2) : ℂ) := by
  rw [jacobiComodulusk, Real.sqrt_eq_rpow, show (1 : ℂ) - (k : ℂ) ^ 2 = ((1 - k ^ 2 : ℝ) : ℂ) by
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
    let kp := jacobiComodulusk k
    let k₁ := (1 - kp) / (1 + kp)
    compEllIntKk k = (1 + k₁) * compEllIntKk k₁ ∧
      compEllIntEk k = (1 + kp) * compEllIntEk k₁ - kp * compEllIntKk k := by
  intro kp k₁
  set s := Real.sqrt (1 - k ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs1 : s ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg k])
  have hkp : kp = s := ei19a_jacobiComodulusk_ofReal hk.le
  have hk₁ : k₁ = (((1 - s) / (1 + s) : ℝ) : ℂ) := by
    simp only [k₁, hkp]; push_cast; rfl
  have hr : ((1 - s) / (1 + s)) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity)]; nlinarith
  have hm : 1 - (k ^ 2) = s ^ 2 := by rw [hs, Real.sq_sqrt (by linarith)]
  have hsq : Real.sqrt (1 - k ^ 2) = s := rfl
  rw [hk₁, hkp, compEllIntKk_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk.le,
    compEllIntKk_eq_ofReal (m := ((1 - s) / (1 + s)) ^ 2) (by push_cast; ring) hr,
    compEllIntEk_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk.le,
    compEllIntEk_eq_ofReal (m := ((1 - s) / (1 + s)) ^ 2) (by push_cast; ring) hr]
  have h1 := DLMF.Elliptic.Real.compEllIntKm_landen_descending hk
  have h2 := DLMF.Elliptic.Real.compEllIntEm_landen_descending hk
  rw [hsq] at h1 h2
  constructor
  · rw [h1]; push_cast; ring
  · rw [h2]; push_cast; ring

/-- The principal square root of a slit-plane number has positive real part. -/
theorem p19lR1_cpow_half_re_pos {z : ℂ} (hz : z ∈ slitPlane) : 0 < (z ^ (1 / 2 : ℂ)).re := by
  rw [cpow_def_of_ne_zero (slitPlane_ne_zero hz), exp_re]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ?_)
  have him : (log z * (1 / 2)).im = arg z / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, mul_im, ofReal_re, ofReal_im,
      log_im]; ring
  rw [him]
  have h1 := neg_pi_lt_arg z
  have h2 : arg z < π := lt_of_le_of_ne (arg_le_pi z) (mem_slitPlane_iff_arg.1 hz).1
  constructor <;> linarith

/-- For `ℜ c > 0`, `1 - ((1 - c)/(1 + c))² = 4c/(1 + c)²` has positive real part. -/
theorem p19lR1_landen_mem {c : ℂ} (hc : 0 < c.re) :
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
    let kp := jacobiComodulusk k
    let k₁ := (1 - kp) / (1 + kp)
    compEllIntKk k = (1 + k₁) * compEllIntKk k₁ ∧
      compEllIntEk k = (1 + kp) * compEllIntEk k₁ - kp * compEllIntKk k := by
  intro kp k₁
  set U := {k : ℂ | 1 - k ^ 2 ∈ slitPlane} with hU
  have hD := differentiableOn_compEllIntKk_compEllIntEk
  have hre : ∀ k ∈ U, 0 < (jacobiComodulusk k).re := fun k hk => p19lR1_cpow_half_re_pos hk
  have hne : ∀ k ∈ U, 1 + jacobiComodulusk k ≠ 0 := fun k hk h => by
    have := congrArg re h; simp at this; linarith [hre k hk]
  have hc : DifferentiableOn ℂ jacobiComodulusk U := fun k hk =>
    (p19lR1_comod_differentiableAt hk).differentiableWithinAt
  set φ : ℂ → ℂ := fun k => (1 - jacobiComodulusk k) / (1 + jacobiComodulusk k) with hφ
  have hφd : DifferentiableOn ℂ φ U :=
    ((differentiableOn_const 1).sub hc).div ((differentiableOn_const 1).add hc) hne
  have hmaps : MapsTo φ U U := fun k hk => p19lR1_landen_mem (hre k hk)
  constructor
  · exact p19lR1_eqOn_U hD.1 (g := fun k => (1 + φ k) * compEllIntKk (φ k))
      (((differentiableOn_const 1).add hφd).mul (hD.1.comp hφd hmaps))
      (fun x h0 h1 => (compEllInt_landen_descending_ofReal (k := x) (by nlinarith)).1) hk
  · exact p19lR1_eqOn_U hD.2
      (g := fun k => (1 + jacobiComodulusk k) * compEllIntEk (φ k) -
        jacobiComodulusk k * compEllIntKk k)
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
    incEllIntFk φ k = (1 + k₁ : ℝ) / 2 * incEllIntFk φ₁ k₁ ∧
      incEllIntEk φ k = (1 + kp : ℝ) / 2 * incEllIntEk φ₁ k₁ - kp * incEllIntFk φ k +
        ((1 - kp) / 2 * Real.sin φ₁ : ℝ) := by
  sorry

/-- **Admitted.** DLMF 19.8.14–19.8.15: for real `0 < k < 1`, `0 < φ < π/2` and real `α²` with
`α² ≠ 1`, `α² ≠ k²`, with `ω² = (k² - α²)/(1 - α²)`, `α₁² = α²ω²/(1 + k')²`, `c₁ = csc²φ₁`
(Cauchy principal values where needed):
`2(k² - α²)Π(φ, α², k) = ((ω² - α²)/(1 + k'))Π(φ₁, α₁², k₁) + k²F(φ, k)
- (1 + k')α₁² R_C(c₁, c₁ - α₁²)`. -/
@[dlmf 19.8.E14, dlmf 19.8.E15]
theorem incEllIntPik_landen_descending {k φ α2 : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) (hα1 : α2 ≠ 1) (hαk : α2 ≠ k ^ 2) :
    let kp := Real.sqrt (1 - k ^ 2)
    let k₁ := (1 - kp) / (1 + kp)
    let φ₁ := φ + Real.arctan (kp * Real.tan φ)
    let ω2 : ℝ := (k ^ 2 - α2) / (1 - α2)
    let α12 : ℝ := α2 * ω2 / (1 + kp) ^ 2
    let c₁ : ℝ := 1 / Real.sin φ₁ ^ 2
    (2 * (k ^ 2 - α2) : ℝ) * incEllIntPik φ α2 k =
      ((ω2 - α2) / (1 + kp) : ℝ) * incEllIntPik φ₁ α12 k₁ + (k ^ 2 : ℝ) * incEllIntFk φ k -
        ((1 + kp) * α12 : ℝ) * symEllIntRC c₁ (c₁ - α12 : ℝ) := by
  sorry

/-- **Admitted.** DLMF 19.8.16–19.8.17 (ascending Landen transformation): for real `0 < k < 1`
and `0 < φ ≤ π/2`, with `k₂ = 2√k/(1 + k)` and `2φ₂ = φ + arcsin(k sin φ)`:
`F(φ, k) = (2/(1 + k))F(φ₂, k₂)` and
`E(φ, k) = (1 + k)E(φ₂, k₂) + (1 - k)F(φ₂, k₂) - k sin φ`. -/
@[dlmf 19.8.E16, dlmf 19.8.E17]
theorem incEllInt_landen_ascending {k φ : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 < φ)
    (hφ1 : φ ≤ π / 2) :
    let k₂ := 2 * Real.sqrt k / (1 + k)
    let φ₂ := (φ + Real.arcsin (k * Real.sin φ)) / 2
    incEllIntFk φ k = (2 / (1 + k) : ℝ) * incEllIntFk φ₂ k₂ ∧
      incEllIntEk φ k = (1 + k : ℝ) * incEllIntEk φ₂ k₂ + (1 - k : ℝ) * incEllIntFk φ₂ k₂ -
        (k * Real.sin φ : ℝ) := by
  sorry

/-! ### §19.8(iii) Gauss transformation -/

/-- **Admitted.** DLMF 19.8.18–19.8.19 (descending Gauss transformation): for real `0 < k < 1` and
`0 < φ < π/2`, with `k₁ = (1 - k')/(1 + k')`, `Δ = √(1 - k² sin²φ)` and
`sin ψ₁ = (1 + k') sin φ/(1 + Δ)`:
`F(φ, k) = (1 + k₁)F(ψ₁, k₁)` and `E(φ, k) = (1 + k')E(ψ₁, k₁) - k'F(φ, k) + (1 - Δ) cot φ`. -/
@[dlmf 19.8.E18, dlmf 19.8.E19]
theorem incEllInt_gauss {k φ : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 < φ) (hφ1 : φ < π / 2) :
    let kp := Real.sqrt (1 - k ^ 2)
    let k₁ := (1 - kp) / (1 + kp)
    let Δ := Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2)
    let ψ₁ := Real.arcsin ((1 + kp) * Real.sin φ / (1 + Δ))
    incEllIntFk φ k = (1 + k₁ : ℝ) * incEllIntFk ψ₁ k₁ ∧
      incEllIntEk φ k = (1 + kp : ℝ) * incEllIntEk ψ₁ k₁ - kp * incEllIntFk φ k +
        ((1 - Δ) * Real.cot φ : ℝ) := by
  sorry

/-- **Admitted.** DLMF 19.8.20–19.8.21: for real `0 < k < 1`, `0 < φ < π/2` and real `α² ≠ 0`
with `α² ≠ c = csc²φ`, with `ρ = √(1 - k²/α²)` (pure imaginary if `0 < α² < k²`),
`α₁² = α²(1 + ρ)²/(1 + k')²` and the Gauss data of 19.8.18:
`ρΠ(φ, α², k) = (4/(1 + k'))Π(ψ₁, α₁², k₁) + (ρ - 1)F(φ, k) - R_C(c - 1, c - α²)`. -/
@[dlmf 19.8.E20, dlmf 19.8.E21]
theorem incEllIntPik_gauss {k φ α2 : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) (hα0 : α2 ≠ 0) (hαc : α2 ≠ 1 / Real.sin φ ^ 2) :
    let kp := Real.sqrt (1 - k ^ 2)
    let k₁ := (1 - kp) / (1 + kp)
    let Δ := Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2)
    let ψ₁ := Real.arcsin ((1 + kp) * Real.sin φ / (1 + Δ))
    let c := 1 / Real.sin φ ^ 2
    let ρ : ℂ := (1 - ((k ^ 2 / α2 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
    let α12 : ℂ := α2 * (1 + ρ) ^ 2 / (1 + kp) ^ 2
    ρ * incEllIntPik φ α2 k = (4 / (1 + kp) : ℝ) * incEllIntPik ψ₁ α12 k₁ +
      (ρ - 1) * incEllIntFk φ k - symEllIntRC (c - 1 : ℝ) (c - α2 : ℝ) := by
  sorry

end DLMF.EllipticIntegrals
