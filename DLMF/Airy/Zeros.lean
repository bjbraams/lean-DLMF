/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.ModulusPhase
public import DLMF.ErrorFunctions.ZeroTools

/-!
# Airy zeros and their common asymptotic coefficients, DLMF §9.9

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent
open scoped Real Topology
namespace DLMF.Airy

/-- The k-th negative real zero, ordered from zero towards negative infinity (k≥1). -/
def airyRealZero (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  Classical.epsilon (fun x : ℝ => x < 0 ∧ f x = 0 ∧
    ({y : ℝ | x < y ∧ y < 0 ∧ f y = 0} : Set ℝ).ncard = k - 1)
/-- Negative zeros of Ai. -/
def airyAiZero : ℕ → ℝ := airyRealZero airyAiReal
/-- Negative zeros of Ai'. -/
def airyAiDerivZero : ℕ → ℝ := airyRealZero airyAiDerivReal
/-- Negative zeros of Bi. -/
def airyBiZero : ℕ → ℝ := airyRealZero airyBiReal
/-- Negative zeros of Bi'. -/
def airyBiDerivZero : ℕ → ℝ := airyRealZero airyBiDerivReal
/-- Zeros in the upper complex-zero sector of Bi or Bi'. -/
def airyUpperZeroSet (f : ℂ → ℂ) : Set ℂ := {z | π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0}
/-- Complex zeros ordered by increasing modulus; the specification theorem establishes existence. -/
def airyComplexZero (f : ℂ → ℂ) (k : ℕ) : ℂ :=
  Classical.epsilon (fun z : ℂ => z ∈ airyUpperZeroSet f ∧
    ({w : ℂ | w ∈ airyUpperZeroSet f ∧ ‖w‖ < ‖z‖} : Set ℂ).ncard = k - 1)
/-- Upper-half-plane complex zeros of Bi. -/
def airyBiComplexZero : ℕ → ℂ := airyComplexZero airyBi
/-- Upper-half-plane complex zeros of Bi'. -/
def airyBiDerivComplexZero : ℕ → ℂ := airyComplexZero airyBiDeriv
/-- The continuous extension of the Ai zero index, via the unwrapped phase. -/
def airyAiZeroContinuous (k : ℝ) : ℝ :=
  Classical.epsilon (fun x : ℝ => x ≤ 0 ∧ airyPhase x = k * π)
/-- The continuous extension of the Ai' zero index. -/
def airyAiDerivZeroContinuous (k : ℝ) : ℝ :=
  Classical.epsilon (fun x : ℝ => x ≤ 0 ∧ airyDerivPhase x = (k - 1) * π)
/-- An all-order expansion in the common reciprocal even-power scale used in 9.9.18–9.9.21. -/
def HasAiryZeroExpansion (q : ℝ) (f t : ℕ → ℂ) (c : ℕ → ℂ) : Prop :=
  HasAsymptoticExpansion atTop (fun n k => t k ^ (-2 * (n : ℂ))) c
    (fun k => f k / t k ^ (q : ℂ))
/-- The real argument of the T,V pair at the (k+1)-st Ai zero. -/
def airyZeroArgument (offset : ℝ) (k : ℕ) : ℂ := (3 * π / 8 * (4 * (k + 1 : ℝ) - offset) : ℝ)
/-- The complex argument of the T,V and U,W pairs for Bi's upper-sector zeros. -/
def airyComplexZeroArgument (offset : ℝ) (k : ℕ) : ℂ := airyZeroArgument offset k + 3 * I * Real.log 2 / 4

/-- `Ai(x) → 0` as `x → +∞` on the real axis. -/
theorem tendsto_airyAiReal_atTop : Tendsto airyAiReal atTop (𝓝 0) := by
  have hv : Tendsto (fun x : ℝ => Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (1 / 4 : ℝ)))
      atTop (𝓝 0) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_airyZeta).div_atTop
      ((tendsto_rpow_atTop (by norm_num)).const_mul_atTop
        (by have := Real.sqrt_pos.mpr Real.pi_pos; positivity))
  have hv' := (continuous_ofReal.tendsto 0).comp hv
  rw [ofReal_zero] at hv'
  have h := airyAi_isEquivalent.symm.tendsto_nhds hv'
  have h' := (continuous_re.tendsto 0).comp h
  rw [zero_re] at h'
  exact h'

/-- `Bi(x) > 0` for `x ≥ 0`. -/
theorem airyBiReal_pos {x : ℝ} (hx : 0 ≤ x) : 0 < airyBiReal x := by
  obtain ⟨r, hr, he⟩ := airyBi_ofReal_pos hx
  simp [airyBiReal, he, hr]

/-- `Ai(x) > 0` for `x ≥ 0`. -/
theorem airyAiReal_pos {x : ℝ} (hx : 0 ≤ x) : 0 < airyAiReal x := by
  obtain ⟨r, hr, he⟩ := airyAi_ofReal_pos hx
  simp [airyAiReal, he, hr]

/-- `Bi'(0) > 0`. -/
theorem airyBiDerivReal_zero_pos : 0 < airyBiDerivReal 0 := by
  have h := airyBiDeriv_zero
  rw [show (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
    ← Complex.ofReal_div] at h
  simp only [airyBiDerivReal, ofReal_zero, h, ofReal_re]
  have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)
  positivity

/-- `((-1)^n)^2 = 1`. -/
theorem neg_one_pow_sq_real (n : ℕ) : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul]; simp

/-! ### Real zeros through a monotone phase -/

section PhaseZeros

variable {f g : ℝ → ℝ} {c : ℝ}

/-- Hypotheses describing the zeros of `f` as the level crossings `g = c + jπ` of a phase `g`
that decreases on `(-∞, 0]` from `g 0 ∈ (c, c + π)` to `+∞`. -/
structure PhaseZeroData (f g : ℝ → ℝ) (c : ℝ) : Prop where
  /-- The phase is continuous. -/
  cont : Continuous g
  /-- The phase is strictly decreasing on `(-∞, 0]`. -/
  anti : StrictAntiOn g (Iic 0)
  /-- The phase tends to `+∞` as `x → -∞`. -/
  tendsto : Tendsto g atBot atTop
  /-- The phase at `0` lies above the level `c`. -/
  lt_zero : c < g 0
  /-- The phase at `0` lies below the level `c + π`. -/
  zero_lt : g 0 < c + π
  /-- On `x < 0` the zeros of `f` are exactly the level crossings `g x = c + jπ`. -/
  zero_iff : ∀ x < 0, f x = 0 ↔ ∃ j : ℤ, g x = c + j * π
  /-- All zeros of `f` are negative. -/
  neg : ∀ x, f x = 0 → x < 0

namespace PhaseZeroData

/-- Every level above `g 0` is attained on `(-∞, 0]`. -/
theorem exists_level (h : PhaseZeroData f g c) {L : ℝ} (hL : g 0 ≤ L) : ∃ x ≤ 0, g x = L := by
  obtain ⟨x0, hx0⟩ := (h.tendsto.eventually (eventually_ge_atTop L)).exists_forall_of_atBot
  set x1 := min x0 0
  have h1 : L ≤ g x1 := hx0 x1 (min_le_left _ _)
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc' (min_le_right x0 0) h.cont.continuousOn
    (mem_Icc.mpr ⟨hL, h1⟩)
  exact ⟨x, hx.2, hgx⟩

/-- A zero of `f` is negative and lies on a level `c + jπ` with `j ≥ 1`. -/
theorem level_of_zero (h : PhaseZeroData f g c) {x : ℝ} (hx : f x = 0) :
    x < 0 ∧ ∃ j : ℕ, 1 ≤ j ∧ g x = c + j * π := by
  have hneg := h.neg x hx
  obtain ⟨j, hj⟩ := (h.zero_iff x hneg).1 hx
  have hg0 : g 0 < g x := h.anti (mem_Iic.mpr hneg.le) (mem_Iic.mpr le_rfl) hneg
  have hπ := Real.pi_pos
  have hjpos : (0 : ℝ) < j := by
    by_contra hn; push Not at hn
    have := mul_nonpos_of_nonpos_of_nonneg hn hπ.le
    linarith [h.lt_zero]
  have hj1 : 1 ≤ j := by exact_mod_cast hjpos
  refine ⟨hneg, j.toNat, by omega, ?_⟩
  rw [hj]; congr 2
  have : ((j.toNat : ℤ) : ℝ) = (j : ℝ) := by rw [Int.toNat_of_nonneg (by omega)]
  exact_mod_cast this.symm

/-- A point of `(-∞, 0]` on a level `c + jπ`, `j ≥ 1`, is a negative zero of `f`. -/
theorem zero_of_level (h : PhaseZeroData f g c) {x : ℝ} (hx : x ≤ 0) {j : ℕ} (hj : 1 ≤ j)
    (hg : g x = c + j * π) : x < 0 ∧ f x = 0 := by
  have hπ := Real.pi_pos
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := h.zero_lt
    nlinarith
  have hlt : x < 0 := lt_of_le_of_ne hx hx0
  exact ⟨hlt, (h.zero_iff x hlt).2 ⟨j, by rw [hg]; norm_cast⟩⟩

/-- The level-`j` point. -/
noncomputable def pt (h : PhaseZeroData f g c) (j : ℕ) : ℝ :=
  Classical.choose (h.exists_level (le_max_right (c + j * π) (g 0)))

/-- The level-`j` point lies in `(-∞, 0]` on the level `c + jπ`. -/
theorem pt_spec (h : PhaseZeroData f g c) {j : ℕ} (hj : 1 ≤ j) :
    h.pt j ≤ 0 ∧ g (h.pt j) = c + j * π := by
  have hs := Classical.choose_spec (h.exists_level (le_max_right (c + j * π) (g 0)))
  refine ⟨hs.1, ?_⟩
  rw [pt, hs.2, max_eq_left]
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have := h.zero_lt; have := Real.pi_pos; nlinarith

/-- Uniqueness of the level-`j` point. -/
theorem eq_pt (h : PhaseZeroData f g c) {x : ℝ} (hx : x ≤ 0) {j : ℕ} (hj : 1 ≤ j)
    (hg : g x = c + j * π) : x = h.pt j :=
  h.anti.injOn (mem_Iic.mpr hx) (mem_Iic.mpr (h.pt_spec hj).1) (by rw [hg, (h.pt_spec hj).2])

/-- The level points decrease with the level. -/
theorem pt_lt_pt (h : PhaseZeroData f g c) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) :
    h.pt j < h.pt i := by
  have hj : 1 ≤ j := by omega
  by_contra hn; push Not at hn
  have h1 := h.anti.antitoneOn (mem_Iic.mpr (h.pt_spec hi).1) (mem_Iic.mpr (h.pt_spec hj).1) hn
  rw [(h.pt_spec hi).2, (h.pt_spec hj).2] at h1
  have : (i : ℝ) < j := by exact_mod_cast hij
  have := Real.pi_pos
  nlinarith

/-- Exactly `k - 1` zeros lie strictly between the level-`k` point and `0`. -/
theorem ncard_eq (h : PhaseZeroData f g c) {k : ℕ} (hk : 1 ≤ k) :
    ({y : ℝ | h.pt k < y ∧ y < 0 ∧ f y = 0} : Set ℝ).ncard = k - 1 := by
  have hS : ({y : ℝ | h.pt k < y ∧ y < 0 ∧ f y = 0} : Set ℝ) =
      h.pt '' (↑(Finset.Ico 1 k) : Set ℕ) := by
    ext y
    simp only [mem_ofPred_eq, mem_image, Finset.coe_Ico, mem_Ico]
    constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨-, j, hj, hgj⟩ := h.level_of_zero h3
      refine ⟨j, ⟨hj, ?_⟩, (h.eq_pt h2.le hj hgj).symm⟩
      by_contra hn; push Not at hn
      have := h.anti.antitoneOn (mem_Iic.mpr (h.pt_spec hk).1) (mem_Iic.mpr h2.le) h1.le
      rw [(h.pt_spec hk).2, hgj] at this
      have hkj : (k : ℝ) ≤ j := by exact_mod_cast hn
      have := h.anti (mem_Iic.mpr (h.pt_spec hk).1) (mem_Iic.mpr h2.le) h1
      rw [(h.pt_spec hk).2, hgj] at this
      have := Real.pi_pos
      nlinarith
    · rintro ⟨j, ⟨hj, hjk⟩, rfl⟩
      exact ⟨h.pt_lt_pt hj hjk, (h.zero_of_level (h.pt_spec hj).1 hj (h.pt_spec hj).2)⟩
  have hinj : Set.InjOn h.pt (↑(Finset.Ico 1 k) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_Ico, mem_Ico] at hi hj
    rcases lt_trichotomy i j with hl | rfl | hl
    · exact absurd hij (h.pt_lt_pt hi.1 hl).ne'
    · rfl
    · exact absurd hij (h.pt_lt_pt hj.1 hl).ne
  rw [hS, hinj.ncard_image, Set.ncard_coe_finset, Nat.card_Ico]

/-- The `k`-th ordered zero is the level-`k` point. -/
theorem airyRealZero_eq (h : PhaseZeroData f g c) {k : ℕ} (hk : 1 ≤ k) :
    airyRealZero f k = h.pt k := by
  set P : ℝ → Prop := fun x => x < 0 ∧ f x = 0 ∧
      ({y : ℝ | x < y ∧ y < 0 ∧ f y = 0} : Set ℝ).ncard = k - 1 with hPdef
  have hP : P (h.pt k) := by
    have := h.zero_of_level (h.pt_spec hk).1 hk (h.pt_spec hk).2
    exact ⟨this.1, this.2, h.ncard_eq hk⟩
  have hε : P (Classical.epsilon P) := Classical.epsilon_spec ⟨_, hP⟩
  change Classical.epsilon P = _
  set x := Classical.epsilon P
  obtain ⟨hx0, hfx, hcard⟩ := hε
  obtain ⟨-, j, hj, hgj⟩ := h.level_of_zero hfx
  have hxj := h.eq_pt hx0.le hj hgj
  rw [hxj, h.ncard_eq hj] at hcard
  have : j = k := by omega
  rw [hxj, this]

/-- The ordered-zero specification, with the phase value at the zero. -/
theorem spec (h : PhaseZeroData f g c) {k : ℕ} (hk : 1 ≤ k) :
    airyRealZero f k < 0 ∧ f (airyRealZero f k) = 0 ∧
      ({y : ℝ | airyRealZero f k < y ∧ y < 0 ∧ f y = 0} : Set ℝ).ncard = k - 1 ∧
      g (airyRealZero f k) = c + k * π := by
  rw [h.airyRealZero_eq hk]
  have := h.zero_of_level (h.pt_spec hk).1 hk (h.pt_spec hk).2
  exact ⟨this.1, this.2, h.ncard_eq hk, (h.pt_spec hk).2⟩

/-- The ordered zeros decrease and exhaust the zeros of `f`. -/
theorem enumeration (h : PhaseZeroData f g c) :
    StrictAntiOn (airyRealZero f) (Ici 1) ∧
      ∀ x : ℝ, f x = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ airyRealZero f k = x := by
  refine ⟨fun i hi j hj hij => ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · rw [h.airyRealZero_eq hi, h.airyRealZero_eq hj]; exact h.pt_lt_pt hi hij
  · obtain ⟨hx0, j, hj, hgj⟩ := h.level_of_zero hx
    exact ⟨j, hj, by rw [h.airyRealZero_eq hj, h.eq_pt hx0.le hj hgj]⟩
  · rintro ⟨k, hk, rfl⟩; exact (h.spec hk).2.1

/-- The zero set of `f` is infinite. -/
theorem infinite (h : PhaseZeroData f g c) : Set.Infinite {x : ℝ | f x = 0} := by
  have hinj : Set.InjOn (airyRealZero f) (Ici 1) := (h.enumeration).1.injOn
  have : airyRealZero f '' (Ici 1) ⊆ {x : ℝ | f x = 0} := by
    rintro _ ⟨k, hk, rfl⟩; exact (h.spec hk).2.1
  exact Set.Infinite.mono this ((Set.Ici_infinite 1).image hinj)

end PhaseZeroData

end PhaseZeros

/-- All real zeros are negative, DLMF §9.9(i). -/
theorem airyAi_real_zeros_negative {x : ℝ} (hx : airyAiReal x = 0) :
    x < 0 := by
  by_contra hn
  obtain ⟨r, hr, he⟩ := airyAi_ofReal_pos (not_lt.mp hn)
  have hx' : (airyAi x).re = 0 := hx
  rw [he] at hx'
  simp only [ofReal_re] at hx'
  linarith


/-- The zeros of `Ai` are the crossings `θ = jπ`. -/
theorem phaseZeroData_airyAi : PhaseZeroData airyAiReal airyPhase 0 := by
  have hπ := Real.pi_pos
  have h0 : airyPhase 0 = π / 6 := by simp [airyPhase]
  refine ⟨airyPhase_continuous, airy_phase_monotone, tendsto_airyPhase_atBot, ?_, ?_, ?_,
    fun x hx => airyAi_real_zeros_negative hx⟩
  · rw [h0]; positivity
  · rw [h0]; linarith
  · intro x _
    rw [airyAiReal_eq_modulus_sin, mul_eq_zero, or_iff_right (airyModulus_pos x).ne',
      Real.sin_eq_zero_iff]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, by rw [← hn]; ring⟩, fun ⟨n, hn⟩ => ⟨n, by rw [hn]; ring⟩⟩

/-- Infinitely many real zeros, DLMF §9.9(i). -/
theorem airyAi_infinite_real_zeros :
    Set.Infinite {x : ℝ | airyAiReal x = 0} := by
  exact phaseZeroData_airyAi.infinite

/-- The ordered real-zero specification in DLMF §9.9(i). -/
theorem airyAiZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyAiZero k < 0 ∧ airyAiReal (airyAiZero k) = 0 ∧
      ({y : ℝ | airyAiZero k < y ∧ y < 0 ∧ airyAiReal y = 0} : Set ℝ).ncard = k - 1 := by
  obtain ⟨h1, h2, h3, -⟩ := phaseZeroData_airyAi.spec hk
  exact ⟨h1, h2, h3⟩

/-- The real zeros are exhausted in their stated order, DLMF §9.9(i). -/
theorem airyAiZero_enumeration :
    StrictAntiOn airyAiZero (Ici 1) ∧ ∀ x : ℝ, airyAiReal x = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ airyAiZero k = x := by
  exact phaseZeroData_airyAi.enumeration

/-- All real zeros are negative, DLMF §9.9(i). -/
theorem airyAiDeriv_real_zeros_negative {x : ℝ} (hx : airyAiDerivReal x = 0) :
    x < 0 := by
  by_contra hn
  replace hn := not_lt.mp hn
  have hcont : Continuous airyAiDerivReal := continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_airyAiDerivReal t).continuousAt
  have hmono : StrictMonoOn airyAiDerivReal (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) hcont.continuousOn fun t ht => ?_
    rw [interior_Ici, mem_Ioi] at ht
    rw [(hasDerivAt_airyAiDerivReal t).deriv]
    exact mul_pos ht (airyAiReal_pos ht.le)
  have hpos : ∀ t, x < t → 0 < airyAiDerivReal t := fun t ht => by
    have := hmono (mem_Ici.mpr hn) (mem_Ici.mpr (hn.trans ht.le)) ht
    linarith
  have hAi : MonotoneOn airyAiReal (Ici x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici x)
      (continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_airyAiReal t).continuousAt).continuousOn
      (fun t _ => (hasDerivAt_airyAiReal t).differentiableAt.differentiableWithinAt)
      fun t ht => ?_
    rw [interior_Ici, mem_Ioi] at ht
    rw [(hasDerivAt_airyAiReal t).deriv]
    exact (hpos t ht).le
  have h0 := airyAiReal_pos hn
  obtain ⟨t, ht1, ht2⟩ := ((tendsto_order.1 tendsto_airyAiReal_atTop).2 _ h0).and
    (eventually_ge_atTop x) |>.exists
  have := hAi (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht2) ht2
  linarith


/-- The zeros of `Ai'` are the crossings `φ = (j - 1)π`. -/
theorem phaseZeroData_airyAiDeriv : PhaseZeroData airyAiDerivReal airyDerivPhase (-π) := by
  have hπ := Real.pi_pos
  have h0 : airyDerivPhase 0 = -π / 6 := by simp [airyDerivPhase]
  refine ⟨airyDerivPhase_continuous, airy_derivPhase_monotone, tendsto_airyDerivPhase_atBot,
    ?_, ?_, ?_, fun x hx => airyAiDeriv_real_zeros_negative hx⟩
  · rw [h0]; linarith
  · rw [h0]; linarith
  · intro x _
    rw [airyAiDerivReal_eq_modulus_sin, mul_eq_zero, or_iff_right (airyDerivModulus_pos x).ne',
      Real.sin_eq_zero_iff]
    exact ⟨fun ⟨n, hn⟩ => ⟨n + 1, by rw [← hn]; push_cast; ring⟩,
      fun ⟨n, hn⟩ => ⟨n - 1, by rw [hn]; push_cast; ring⟩⟩

/-- Infinitely many real zeros, DLMF §9.9(i). -/
theorem airyAiDeriv_infinite_real_zeros :
    Set.Infinite {x : ℝ | airyAiDerivReal x = 0} := by
  exact phaseZeroData_airyAiDeriv.infinite

/-- The ordered real-zero specification in DLMF §9.9(i). -/
theorem airyAiDerivZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyAiDerivZero k < 0 ∧ airyAiDerivReal (airyAiDerivZero k) = 0 ∧
      ({y : ℝ | airyAiDerivZero k < y ∧ y < 0 ∧ airyAiDerivReal y = 0} : Set ℝ).ncard = k - 1 := by
  obtain ⟨h1, h2, h3, -⟩ := phaseZeroData_airyAiDeriv.spec hk
  exact ⟨h1, h2, h3⟩

/-- The real zeros are exhausted in their stated order, DLMF §9.9(i). -/
theorem airyAiDerivZero_enumeration :
    StrictAntiOn airyAiDerivZero (Ici 1) ∧ ∀ x : ℝ, airyAiDerivReal x = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ airyAiDerivZero k = x := by
  exact phaseZeroData_airyAiDeriv.enumeration

/-- All real zeros are negative, DLMF §9.9(i). -/
theorem airyBi_real_zeros_negative {x : ℝ} (hx : airyBiReal x = 0) :
    x < 0 := by
  by_contra hn
  obtain ⟨r, hr, he⟩ := airyBi_ofReal_pos (not_lt.mp hn)
  have hx' : (airyBi x).re = 0 := hx
  rw [he] at hx'
  simp only [ofReal_re] at hx'
  linarith


/-- The zeros of `Bi` are the crossings `θ = (j - 1/2)π`. -/
theorem phaseZeroData_airyBi : PhaseZeroData airyBiReal airyPhase (-(π / 2)) := by
  have hπ := Real.pi_pos
  have h0 : airyPhase 0 = π / 6 := by simp [airyPhase]
  refine ⟨airyPhase_continuous, airy_phase_monotone, tendsto_airyPhase_atBot, ?_, ?_, ?_,
    fun x hx => airyBi_real_zeros_negative hx⟩
  · rw [h0]; linarith
  · rw [h0]; linarith
  · intro x _
    rw [airyBiReal_eq_modulus_cos, mul_eq_zero, or_iff_right (airyModulus_pos x).ne',
      Real.cos_eq_zero_iff]
    exact ⟨fun ⟨n, hn⟩ => ⟨n + 1, by rw [hn]; push_cast; ring⟩,
      fun ⟨n, hn⟩ => ⟨n - 1, by rw [hn]; push_cast; ring⟩⟩

/-- Infinitely many real zeros, DLMF §9.9(i). -/
theorem airyBi_infinite_real_zeros :
    Set.Infinite {x : ℝ | airyBiReal x = 0} := by
  exact phaseZeroData_airyBi.infinite

/-- The ordered real-zero specification in DLMF §9.9(i). -/
theorem airyBiZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyBiZero k < 0 ∧ airyBiReal (airyBiZero k) = 0 ∧
      ({y : ℝ | airyBiZero k < y ∧ y < 0 ∧ airyBiReal y = 0} : Set ℝ).ncard = k - 1 := by
  obtain ⟨h1, h2, h3, -⟩ := phaseZeroData_airyBi.spec hk
  exact ⟨h1, h2, h3⟩

/-- The real zeros are exhausted in their stated order, DLMF §9.9(i). -/
theorem airyBiZero_enumeration :
    StrictAntiOn airyBiZero (Ici 1) ∧ ∀ x : ℝ, airyBiReal x = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ airyBiZero k = x := by
  exact phaseZeroData_airyBi.enumeration

/-- All real zeros are negative, DLMF §9.9(i). -/
theorem airyBiDeriv_real_zeros_negative {x : ℝ} (hx : airyBiDerivReal x = 0) :
    x < 0 := by
  by_contra hn
  replace hn := not_lt.mp hn
  have hmono : MonotoneOn airyBiDerivReal (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_airyBiDerivReal t).continuousAt).continuousOn
      (fun t _ => (hasDerivAt_airyBiDerivReal t).differentiableAt.differentiableWithinAt)
      fun t ht => ?_
    rw [interior_Ici, mem_Ioi] at ht
    rw [(hasDerivAt_airyBiDerivReal t).deriv]
    exact mul_nonneg ht.le (airyBiReal_pos ht.le).le
  have := hmono ((mem_Ici.mpr le_rfl)) hn hn
  linarith [airyBiDerivReal_zero_pos]


/-- The zeros of `Bi'` are the crossings `φ = (j - 1/2)π`. -/
theorem phaseZeroData_airyBiDeriv : PhaseZeroData airyBiDerivReal airyDerivPhase (-(π / 2)) := by
  have hπ := Real.pi_pos
  have h0 : airyDerivPhase 0 = -π / 6 := by simp [airyDerivPhase]
  refine ⟨airyDerivPhase_continuous, airy_derivPhase_monotone, tendsto_airyDerivPhase_atBot,
    ?_, ?_, ?_, fun x hx => airyBiDeriv_real_zeros_negative hx⟩
  · rw [h0]; linarith
  · rw [h0]; linarith
  · intro x _
    rw [airyBiDerivReal_eq_modulus_cos, mul_eq_zero, or_iff_right (airyDerivModulus_pos x).ne',
      Real.cos_eq_zero_iff]
    exact ⟨fun ⟨n, hn⟩ => ⟨n + 1, by rw [hn]; push_cast; ring⟩,
      fun ⟨n, hn⟩ => ⟨n - 1, by rw [hn]; push_cast; ring⟩⟩

/-- Infinitely many real zeros, DLMF §9.9(i). -/
theorem airyBiDeriv_infinite_real_zeros :
    Set.Infinite {x : ℝ | airyBiDerivReal x = 0} := by
  exact phaseZeroData_airyBiDeriv.infinite

/-- The ordered real-zero specification in DLMF §9.9(i). -/
theorem airyBiDerivZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyBiDerivZero k < 0 ∧ airyBiDerivReal (airyBiDerivZero k) = 0 ∧
      ({y : ℝ | airyBiDerivZero k < y ∧ y < 0 ∧ airyBiDerivReal y = 0} : Set ℝ).ncard = k - 1 := by
  obtain ⟨h1, h2, h3, -⟩ := phaseZeroData_airyBiDeriv.spec hk
  exact ⟨h1, h2, h3⟩

/-- The real zeros are exhausted in their stated order, DLMF §9.9(i). -/
theorem airyBiDerivZero_enumeration :
    StrictAntiOn airyBiDerivZero (Ici 1) ∧ ∀ x : ℝ, airyBiDerivReal x = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ airyBiDerivZero k = x := by
  exact phaseZeroData_airyBiDeriv.enumeration

/-! ### Nonreal zeros of `Ai` and `Ai'`

For `u(t) = Ai(z₀ + t)` one has `(conj(u) u')' = |u'|² + (z₀ + t)|u|²`. If `Ai(z₀) = 0` or
`Ai'(z₀) = 0`, the boundary term `conj(u) u'` vanishes at `t = 0` and, by the exponential decay
of DLMF 9.7.5–9.7.6, at infinity. Its imaginary part then forces `Im z₀ = 0`, and its real part
forces `z₀ < 0`.
-/

/-- `re (2ζ(w)) = (4/3)|w|^{3/2} cos(3/2 arg w)`. -/
theorem airyZeroC_re_two_zeta {w : ℂ} (hw : w ≠ 0) :
    (2 * airyZetaComplex w).re = 4 / 3 * ‖w‖ ^ (3 / 2 : ℝ) * Real.cos (3 / 2 * arg w) := by
  have h := airyRot_re_W w 0
  rw [← airyRot_two_zeta_mul_exp hw 0, ofReal_zero, zero_mul, exp_zero, mul_one, add_zero] at h
  rw [h, ← airyRot_norm_two_zeta w]
  congr 1
  rw [← Complex.norm_exp, exp_log_two_add_airyLogZeta hw]

/-- Along a horizontal ray `z₀ + T`, `arg → 0`. -/
theorem airyZeroC_tendsto_arg (z0 : ℂ) :
    Tendsto (fun T : ℝ => arg (z0 + T)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℝ => z0 / T + 1) atTop (𝓝 (0 + 1)) := by
    refine Tendsto.add_const 1 ?_
    have : Tendsto (fun T : ℝ => ((T : ℂ))⁻¹) atTop (𝓝 0) := by
      have := (continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
      simpa [Function.comp_def] using this
    simpa [div_eq_mul_inv] using this.const_mul z0
  rw [zero_add] at h1
  have h2 := (continuousAt_arg (by simp : (1 : ℂ) ∈ slitPlane)).tendsto.comp h1
  rw [arg_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  simp only [Function.comp_apply]
  rw [← arg_real_mul _ hT]
  congr 1
  have hT0 : (T : ℂ) ≠ 0 := ofReal_ne_zero.mpr hT.ne'
  field_simp

/-- `‖z₀ + T‖ → ∞` as `T → +∞`. -/
theorem airyZeroC_tendsto_norm (z0 : ℂ) :
    Tendsto (fun T : ℝ => ‖z0 + T‖) atTop atTop := by
  refine tendsto_atTop_mono (fun T => ?_) (tendsto_atTop_add_const_left _ (-‖z0‖) tendsto_id)
  have := norm_sub_norm_le (T : ℂ) (-z0)
  simp only [norm_neg, sub_neg_eq_add, Complex.norm_real] at this
  rw [add_comm] at this
  have h2 := le_abs_self T
  simp only [id]
  rw [Real.norm_eq_abs] at this
  linarith

/-- The horizontal ray `z₀ + T`, `T → +∞`, eventually lies in the sector `|arg z| ≤ π/2`
and tends to infinity there. -/
theorem airyZeroC_tendsto_sector (z0 : ℂ) :
    Tendsto (fun T : ℝ => z0 + T) atTop (airySector (π / 2)) := by
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr (airyZeroC_tendsto_norm z0), ?_⟩
  refine tendsto_principal.mpr ?_
  filter_upwards [eventually_gt_atTop (-z0.re)] with T hT
  have hre : 0 < (z0 + T).re := by simp; linarith
  refine ⟨fun h => by simp [h] at hre, abs_arg_le_pi_div_two_iff.mpr hre.le⟩

/-- `re (2ζ(z₀ + T)) → ∞`. -/
theorem airyZeroC_tendsto_re_zeta (z0 : ℂ) :
    Tendsto (fun T : ℝ => (2 * airyZetaComplex (z0 + T)).re) atTop atTop := by
  have hc : Tendsto (fun T : ℝ => Real.cos (3 / 2 * arg (z0 + T))) atTop (𝓝 1) := by
    have h0 := (airyZeroC_tendsto_arg z0).const_mul (3 / 2)
    rw [mul_zero] at h0
    have := (Real.continuous_cos.tendsto 0).comp h0
    simpa [Function.comp_def] using this
  have hn : Tendsto (fun T : ℝ => 4 / 3 * ‖z0 + T‖ ^ (3 / 2 : ℝ)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num)).comp (airyZeroC_tendsto_norm z0)).const_mul_atTop
      (by norm_num)
  refine (hn.atTop_mul_pos one_pos hc).congr' ?_
  filter_upwards [eventually_gt_atTop (-z0.re)] with T hT
  have hre : 0 < (z0 + T).re := by simp; linarith
  have hw : z0 + T ≠ 0 := fun h => by simp [h] at hre
  rw [airyZeroC_re_two_zeta hw]

/-- The Wronskian-type boundary term `conj(Ai) Ai'` decays along horizontal rays. -/
theorem airyZeroC_tendsto_boundary (z0 : ℂ) :
    Tendsto (fun T : ℝ => (starRingEnd ℂ) (airyAi (z0 + T)) * airyAiDeriv (z0 + T)) atTop
      (𝓝 0) := by
  have hT := airyZeroC_tendsto_sector z0
  have hA := (airy_ai_poincare (δ := π / 2) (by positivity) (by linarith [Real.pi_pos]) 0).comp_tendsto
    (by rw [show π - π / 2 = π / 2 by ring]; exact hT)
  have hD := (airy_aiDeriv_poincare (δ := π / 2) (by positivity) (by linarith [Real.pi_pos]) 0).comp_tendsto
    (by rw [show π - π / 2 = π / 2 by ring]; exact hT)
  simp only [airyFunction, airyExponentialSum, Finset.range_zero, Finset.sum_empty, mul_zero,
    sub_zero, pow_zero, div_one, Function.comp_def] at hA hD
  have hP : (fun T : ℝ => (starRingEnd ℂ) (airyAi (z0 + T)) * airyAiDeriv (z0 + T)) =O[atTop]
      (fun T : ℝ => airyPrefactor .ai (z0 + T) * airyPrefactor .aiDeriv (z0 + T)) := by
    refine IsBigO.of_norm_left ?_
    have := (hA.norm_left.mul hD.norm_left)
    refine this.congr_left fun T => ?_
    rw [norm_mul, Complex.norm_conj]
  refine hP.trans_tendsto ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have he : Tendsto (fun T : ℝ => Real.exp (-(2 * airyZetaComplex (z0 + T)).re) / (4 * π)) atTop
      (𝓝 (0 / (4 * π))) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp (airyZeroC_tendsto_re_zeta z0)).div_const _
  rw [zero_div] at he
  refine he.congr' ?_
  filter_upwards [eventually_gt_atTop (-z0.re)] with T hT
  have hre : 0 < (z0 + T).re := by simp; linarith
  have hw : z0 + T ≠ 0 := fun h => by simp [h] at hre
  have hq : (z0 + T) ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hw)
  have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hprod : airyPrefactor .ai (z0 + T) * airyPrefactor .aiDeriv (z0 + T) =
      -(exp (-(2 * airyZetaComplex (z0 + T))) / (4 * π)) := by
    simp only [airyPrefactor]
    rw [show -(2 * airyZetaComplex (z0 + T)) = -airyZetaComplex (z0 + T) +
      -airyZetaComplex (z0 + T) by ring, exp_add]
    have hs : ((Real.sqrt π : ℝ) : ℂ) ^ 2 = π := by
      rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
    field_simp
    linear_combination 4 * hs
  rw [hprod, norm_neg, norm_div, Complex.norm_exp, neg_re]
  simp [abs_of_pos Real.pi_pos]

/-- `t ↦ Ai(z₀ + t)` has derivative `Ai'(z₀ + t)` along the real line. -/
theorem airyZeroC_hasDerivAt_u (z0 : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => airyAi (z0 + t)) (airyAiDeriv (z0 + t)) t := by
  have h := ((hasDerivAt_airyAi (z0 + t)).comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).const_add z0))
  simp only [mul_one] at h
  exact h.comp_ofReal

/-- `t ↦ Ai'(z₀ + t)` has derivative `(z₀ + t) Ai(z₀ + t)` along the real line. -/
theorem airyZeroC_hasDerivAt_v (z0 : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => airyAiDeriv (z0 + t)) ((z0 + t) * airyAi (z0 + t)) t := by
  have h := ((hasDerivAt_airyAiDeriv (z0 + t)).comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).const_add z0))
  simp only [mul_one] at h
  exact h.comp_ofReal

/-- A function with nonnegative derivative on `[0, ∞)`, vanishing at `0` and at infinity,
vanishes identically there, and so does its derivative on `(0, ∞)`. -/
theorem airyZeroC_deriv_eq_zero {φ ψ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (ψ t) t) (h0 : φ 0 = 0)
    (hlim : Tendsto φ atTop (𝓝 0)) (hψ : ∀ t, 0 ≤ t → 0 ≤ ψ t) {t : ℝ} (ht : 0 < t) :
    ψ t = 0 := by
  have hmono : MonotoneOn φ (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hφ x).continuousAt.continuousWithinAt)
      (fun x _ => (hφ x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Ici] at hx
    rw [(hφ x).deriv]
    exact hψ x (le_of_lt hx)
  have hzero : ∀ s, 0 ≤ s → φ s = 0 := by
    intro s hs
    refine le_antisymm ?_ (h0 ▸ hmono (mem_Ici.mpr (le_refl (0 : ℝ))) hs hs)
    exact ge_of_tendsto hlim ((eventually_ge_atTop s).mono fun r hr =>
      hmono hs (hs.trans hr) hr)
  have hev : φ =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
    (eventually_gt_nhds ht).mono fun s hs => hzero s hs.le
  exact (hφ t).unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev)

/-- `Ai` does not vanish on a whole horizontal ray. -/
theorem airyZeroC_not_forall (z0 : ℂ) : ¬ ∀ t : ℝ, 0 < t → airyAi (z0 + t) = 0 := by
  intro h
  have hf : AnalyticOnNhd ℂ airyAi univ := fun z _ => differentiable_airyAi.analyticAt z
  have hT : Tendsto (fun t : ℝ => z0 + t) (𝓝[>] 1) (𝓝[≠] (z0 + 1)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Continuous fun t : ℝ => z0 + (t : ℂ) := continuous_const.add continuous_ofReal
      have := (this.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi 1))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with t ht
      intro he
      have : (t : ℂ) = 1 := by simpa using he
      exact (ne_of_gt (show (1 : ℝ) < t from ht)) (by exact_mod_cast this)
  have hfreq : ∃ᶠ z in 𝓝[≠] (z0 + 1), airyAi z = 0 := by
    refine hT.frequently ?_
    refine Eventually.frequently ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact h t (lt_trans one_pos ht)
  have h0 := hf.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (mem_univ _) hfreq (mem_univ 0)
  have hp := airyAiReal_zero_pos
  simp only [airyAiReal, ofReal_zero, h0, Pi.zero_apply, zero_re] at hp
  exact lt_irrefl _ hp

/-- **Energy identity argument.** If `conj(Ai(z₀)) Ai'(z₀) = 0`, then `z₀` is real and negative. -/
theorem airyZeroC_real_neg {z0 : ℂ}
    (h0 : (starRingEnd ℂ) (airyAi z0) * airyAiDeriv z0 = 0) : z0.im = 0 ∧ z0.re < 0 := by
  set g : ℝ → ℂ := fun t => (starRingEnd ℂ) (airyAi (z0 + t)) * airyAiDeriv (z0 + t) with hgdef
  have hg : ∀ t : ℝ, HasDerivAt g ((starRingEnd ℂ) (airyAiDeriv (z0 + t)) * airyAiDeriv (z0 + t) +
      (starRingEnd ℂ) (airyAi (z0 + t)) * ((z0 + t) * airyAi (z0 + t))) t := fun t =>
    ((airyZeroC_hasDerivAt_u z0 t).star.mul (airyZeroC_hasDerivAt_v z0 t))
  have hg0 : g 0 = 0 := by simp [hgdef, h0]
  have hlim : Tendsto g atTop (𝓝 0) := airyZeroC_tendsto_boundary z0
  have hnv := airyZeroC_not_forall z0
  have him : z0.im = 0 := by
    by_contra hne
    apply hnv
    intro t ht
    have hψ := airyZeroC_deriv_eq_zero (φ := fun t => (g t).im / z0.im)
      (ψ := fun t => normSq (airyAi (z0 + t)))
      (fun t => by
        refine (((imCLM.hasFDerivAt).comp_hasDerivAt t (hg t)).div_const z0.im).congr_deriv ?_
        rw [imCLM_apply, div_eq_iff hne]
        simp only [add_im, mul_im, conj_re, conj_im, add_re, ofReal_re, ofReal_im, mul_re,
          normSq_apply]
        ring)
      (by simp only [hg0, zero_im, zero_div])
      (by simpa [Function.comp_def] using ((continuous_im.tendsto 0).comp hlim).div_const z0.im)
      (fun t _ => normSq_nonneg _) ht
    exact normSq_eq_zero.mp hψ
  refine ⟨him, ?_⟩
  by_contra hre
  push Not at hre
  apply hnv
  intro t ht
  have hψ := airyZeroC_deriv_eq_zero (φ := fun t => (g t).re)
    (ψ := fun t => normSq (airyAiDeriv (z0 + t)) + (z0.re + t) * normSq (airyAi (z0 + t)))
    (fun t => by
      refine ((reCLM.hasFDerivAt).comp_hasDerivAt t (hg t)).congr_deriv ?_
      rw [reCLM_apply]
      simp only [add_im, mul_im, conj_re, conj_im, add_re, ofReal_re, ofReal_im, mul_re,
        normSq_apply, him]
      ring)
    (by simp only [hg0, zero_re])
    (by simpa [Function.comp_def] using ((continuous_re.tendsto 0).comp hlim))
    (fun t ht => add_nonneg (normSq_nonneg _) (mul_nonneg (by linarith) (normSq_nonneg _))) ht
  have h1 := normSq_nonneg (airyAiDeriv (z0 + t))
  have h2 : 0 ≤ (z0.re + t) * normSq (airyAi (z0 + t)) :=
    mul_nonneg (by linarith) (normSq_nonneg _)
  have h3 : (z0.re + t) * normSq (airyAi (z0 + t)) = 0 := by linarith
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · exact normSq_eq_zero.mp h

/-- Ai and Ai' have no nonreal zeros, DLMF §9.9(i). -/
theorem airyAi_complex_zeros_real {z : ℂ} (hz : airyAi z = 0) :
    z.im = 0 ∧ z.re < 0 :=
  airyZeroC_real_neg (by rw [hz, map_zero, zero_mul])

/-- Ai and Ai' have no nonreal zeros, DLMF §9.9(i). -/
theorem airyAiDeriv_complex_zeros_real {z : ℂ} (hz : airyAiDeriv z = 0) :
    z.im = 0 ∧ z.re < 0 :=
  airyZeroC_real_neg (by rw [hz, mul_zero])

/-! ### Complex zeros of `Bi` and `Bi'` near the model zeros

In the variable `u = -2ζ`, the normalized `Bi` and `Bi'` are `1 ± (i/2) e^u + o(1)` in the upper
sector; a Rouché argument on discs of radius `1/2` gives one zero near each model zero. -/

section UpperZeros
open Metric

/-- The inverse of `z ↦ -2ζ(z)` on the upper sector. -/
noncomputable def airyZ_Z (u : ℂ) : ℂ := exp (2 / 3 * log (-(3 / 4 : ℂ) * u))

/-- The imaginary part of `(2/3) log(-(3/4) u)` lies in `(-π, π]`. -/
theorem airyZ_im_bound (u : ℂ) :
    -π < (2 / 3 * log (-(3 / 4 : ℂ) * u)).im ∧ (2 / 3 * log (-(3 / 4 : ℂ) * u)).im ≤ π := by
  have h1 := neg_pi_lt_arg (-(3 / 4 : ℂ) * u)
  have h2 := arg_le_pi (-(3 / 4 : ℂ) * u)
  have hπ := Real.pi_pos
  have : (2 / 3 * log (-(3 / 4 : ℂ) * u)).im = 2 / 3 * arg (-(3 / 4 : ℂ) * u) := by
    simp [log_im]
  rw [this]; constructor <;> nlinarith

/-- `log Z(u) = (2/3) log(-(3/4) u)`. -/
theorem airyZ_log_Z (u : ℂ) : log (airyZ_Z u) = 2 / 3 * log (-(3 / 4 : ℂ) * u) :=
  log_exp (airyZ_im_bound u).1 (airyZ_im_bound u).2

/-- `arg Z(u) = (2/3) arg(-(3/4) u)`. -/
theorem airyZ_arg_Z (u : ℂ) : arg (airyZ_Z u) = 2 / 3 * arg (-(3 / 4 : ℂ) * u) := by
  rw [← log_im, airyZ_log_Z]; simp [log_im]

/-- `Z(u) ≠ 0`. -/
theorem airyZ_Z_ne_zero (u : ℂ) : airyZ_Z u ≠ 0 := exp_ne_zero _

/-- Complex powers of `Z(u)`: `Z(u)^w = exp((2/3) log(-(3/4) u) w)`. -/
theorem airyZ_cpow_Z (u w : ℂ) :
    airyZ_Z u ^ w = exp (2 / 3 * log (-(3 / 4 : ℂ) * u) * w) := by
  rw [cpow_def_of_ne_zero (airyZ_Z_ne_zero u), airyZ_log_Z]

/-- `ζ(Z(u)) = -u/2` for `u ≠ 0`, so `Z` inverts `z ↦ -2ζ(z)`. -/
theorem airyZ_zeta_Z {u : ℂ} (hu : u ≠ 0) : airyZetaComplex (airyZ_Z u) = -u / 2 := by
  unfold airyZetaComplex
  rw [airyZ_cpow_Z, show 2 / 3 * log (-(3 / 4 : ℂ) * u) * (3 / 2) = log (-(3 / 4 : ℂ) * u) by ring,
    exp_log (mul_ne_zero (by norm_num) hu)]
  ring

/-- `Z(u)^{1/4} = exp(log(-(3/4) u)/6)`. -/
theorem airyZ_quarter_Z (u : ℂ) :
    airyZ_Z u ^ (1 / 4 : ℂ) = exp (log (-(3 / 4 : ℂ) * u) / 6) := by
  rw [airyZ_cpow_Z]; congr 1; ring

/-- `‖Z(u)‖ = exp((2/3) log ‖(3/4) u‖)`, the modulus `‖(3/4) u‖^{2/3}` for `u ≠ 0`. -/
theorem airyZ_norm_Z (u : ℂ) : ‖airyZ_Z u‖ = Real.exp (2 / 3 * Real.log ‖-(3 / 4 : ℂ) * u‖) := by
  rw [airyZ_Z, norm_exp]; congr 1; simp [log_re]

/-- Upper-sector bounds on the argument. -/
theorem airyZ_arg_bounds {v : ℂ} (h1 : v.re < 0) (h2 : -v.re < v.im) :
    π / 2 < arg v ∧ arg v < 3 * π / 4 := by
  have hπ := Real.pi_pos
  have hv : v ≠ 0 := fun h => by simp [h] at h1
  have ha : π / 2 < arg v := by
    by_contra h
    rcases arg_le_pi_div_two_iff.mp (not_lt.mp h) with h' | h' <;> linarith
  refine ⟨ha, ?_⟩
  have hrot := Complex.arg_mul_exp_ofReal_mul_I hv (α := -(π / 4)) (by linarith)
    (by linarith [arg_le_pi v])
  have hre : 0 < (v * exp (((-(π / 4) : ℝ) : ℂ) * I)).re := by
    rw [show (((-(π / 4) : ℝ) : ℂ) * I) = ((-(π / 4) : ℝ) : ℂ) * I from rfl, exp_mul_I]
    simp only [mul_re, add_re, mul_im, add_im, ← ofReal_cos, ← ofReal_sin, ofReal_re, ofReal_im,
      I_re, I_im]
    rw [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
    have : 0 < Real.sqrt 2 := by positivity
    nlinarith
  have := arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  rw [hrot] at this; linarith


/-- `1/ζ(z) → 0` as `z → ∞` in the sector `|arg z| ≤ α`. -/
theorem airyZ_zeta_recip_tendsto (α : ℝ) :
    Tendsto (fun z => ((airyZetaComplex z) ^ 1)⁻¹) (airySector α) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hn : ∀ z : ℂ, ‖((airyZetaComplex z) ^ 1)⁻¹‖ = (2 / 3 * ‖z‖ ^ (3 / 2 : ℝ))⁻¹ := by
    intro z
    rw [pow_one, norm_inv, airyZetaComplex, norm_mul,
      show ((3 / 2 : ℂ)) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]
    norm_num
  simp only [hn]
  exact ((((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp
    (tendsto_comap.mono_left inf_le_left)).const_mul_atTop (by norm_num : (0 : ℝ) < 2 / 3))).inv_tendsto_atTop

/-- The leading-order part of a normalized expansion, in quantitative form. -/
theorem airyZ_small {F : ℂ → ℂ} {c : ℕ → ℂ} {α : ℝ}
    (h : HasAsymptoticExpansion (airySector α) (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c F)
    (hc : c 0 = 1) {η : ℝ} (hη : 0 < η) :
    ∃ R, ∀ w : ℂ, w ≠ 0 → |arg w| ≤ α → R ≤ ‖w‖ → ‖F w - 1‖ < η := by
  have h1 := (h 1).trans_tendsto (airyZ_zeta_recip_tendsto α)
  have h2 : ∀ᶠ w in airySector α, ‖F w - 1‖ < η := by
    filter_upwards [(tendsto_zero_iff_norm_tendsto_zero.mp h1).eventually (gt_mem_nhds hη)]
      with w hw
    simpa [hc] using hw
  obtain ⟨s, hs, hsub⟩ := mem_comap.mp (mem_inf_principal.mp h2)
  obtain ⟨R, hR⟩ := mem_atTop_sets.mp hs
  exact ⟨R, fun w hw0 hwa hwR => hsub (hR _ hwR) ⟨hw0, hwa⟩⟩

/-- `e^{-πi/6} e^{-πi/3} = -i`. -/
theorem airyZ_exp_neg_pi_half : exp (-(π * I / 6)) * exp (-(π * I / 3)) = -I := by
  rw [← exp_add, show -(π * I / 6) + -(π * I / 3) = -((π / 2 : ℂ) * I) by ring, exp_neg,
    exp_pi_div_two_mul_I, inv_I]

/-- `Bi(z) = 2 e^{-πi/6} Ai(z e^{-2πi/3}) + i Ai(z)`, a rearranged connection formula. -/
theorem airyZ_bi_eq (z : ℂ) :
    airyBi z = 2 * exp (-(π * I / 6)) * airyAi (z * exp (-(2 * π * I / 3))) + I * airyAi (z * 1) := by
  rw [airyAi_mul_omega_recip, mul_one]
  have h := airyZ_exp_neg_pi_half
  linear_combination (-(airyAi z + I * airyBi z)) * h + airyBi z * I_sq

/-- The derivative form of `airyZ_bi_eq`:
`Bi'(z) = 2 e^{-πi/6} e^{-2πi/3} Ai'(z e^{-2πi/3}) + i Ai'(z)`. -/
theorem airyZ_biDeriv_eq (z : ℂ) :
    airyBiDeriv z = 2 * exp (-(π * I / 6)) * exp (-(2 * π * I / 3)) *
      airyAiDeriv (z * exp (-(2 * π * I / 3))) + I * 1 * airyAiDeriv (z * 1) :=
  airyRot_deriv_of_eq hasDerivAt_airyBi hasDerivAt_airyAi _ _ _ _ airyZ_bi_eq z

/-- The rotated point `Z(u) e^{-2πi/3}`. -/
noncomputable def airyZ_W (u : ℂ) : ℂ := airyZ_Z u * exp (((-(2 * π / 3)) : ℝ) * I)

/-- For `arg(-(3/4) u) ≥ 0`, the rotation of `Z(u)` by `-2π/3` stays within the principal
argument range. -/
theorem airyZ_arg_ok {u : ℂ} (hu : 0 ≤ arg (-(3 / 4 : ℂ) * u)) :
    -π < arg (airyZ_Z u) + (-(2 * π / 3)) ∧ arg (airyZ_Z u) + (-(2 * π / 3)) ≤ π := by
  rw [airyZ_arg_Z]
  have := arg_le_pi (-(3 / 4 : ℂ) * u)
  have hπ := Real.pi_pos
  constructor <;> nlinarith

/-- `ζ(W(u)) = u/2` when `u ≠ 0` and `arg(-(3/4) u) ≥ 0`. -/
theorem airyZ_zeta_W {u : ℂ} (hu0 : u ≠ 0) (hu : 0 ≤ arg (-(3 / 4 : ℂ) * u)) :
    airyZetaComplex (airyZ_W u) = u / 2 := by
  rw [airyZ_W, airyRot_zeta_mul_exp (airyZ_Z_ne_zero u) (airyZ_arg_ok hu).1 (airyZ_arg_ok hu).2,
    airyZ_zeta_Z hu0, show (((-(2 * π / 3)) : ℝ) : ℂ) * I * (3 / 2) = -(π * I) by push_cast; ring,
    exp_neg, exp_pi_mul_I]
  ring

/-- `W(u)^{1/4} = exp(log(-(3/4) u)/6) e^{-πi/6}` when `arg(-(3/4) u) ≥ 0`. -/
theorem airyZ_quarter_W {u : ℂ} (hu : 0 ≤ arg (-(3 / 4 : ℂ) * u)) :
    airyZ_W u ^ (1 / 4 : ℂ) = exp (log (-(3 / 4 : ℂ) * u) / 6) * exp (-(π * I / 6)) := by
  rw [airyZ_W, Complex.cpow_mul_exp_ofReal_mul_I (airyZ_Z_ne_zero u) (airyZ_arg_ok hu).1
    (airyZ_arg_ok hu).2, airyZ_quarter_Z]
  congr 2; push_cast; ring

/-- `W(u) = Z(u) e^{-2πi/3}`. -/
theorem airyZ_W_eq (u : ℂ) : airyZ_W u = airyZ_Z u * exp (-(2 * π * I / 3)) := by
  rw [airyZ_W, airyRot_exp_two_pi_div_three.2]

/-- The normalized `Bi` in the variable `u = -2ζ`. -/
noncomputable def airyZ_Fbi (u : ℂ) : ℂ :=
  airyBi (airyZ_Z u) * (Real.sqrt π * exp (log (-(3 / 4 : ℂ) * u) / 6) * exp (u / 2))

/-- The normalized `Bi` as a combination of the normalized `Ai` at `W(u)` and at `Z(u)`. -/
theorem airyZ_Fbi_eq {u : ℂ} (hu0 : u ≠ 0) (hu : 0 ≤ arg (-(3 / 4 : ℂ) * u)) :
    airyZ_Fbi u = airyAi (airyZ_W u) / airyPrefactor .ai (airyZ_W u) +
      I / 2 * exp u * (airyAi (airyZ_Z u) / airyPrefactor .ai (airyZ_Z u)) := by
  simp only [airyZ_Fbi, airyPrefactor]
  rw [airyZ_zeta_W hu0 hu, airyZ_quarter_W hu, airyZ_zeta_Z hu0, airyZ_quarter_Z, airyZ_bi_eq,
    mul_one, ← airyZ_W_eq]
  have hπs : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  set a := exp (u / 2)
  set b := exp (log (-(3 / 4 : ℂ) * u) / 6)
  have ha : exp (-(-u / 2)) = a := by congr 1; ring
  have ha' : exp (-(u / 2)) = a⁻¹ := by rw [exp_neg]
  have hu2 : exp u = a * a := by rw [← exp_add]; congr 1; ring
  have hq : exp (-(π * I / 6)) ≠ 0 := exp_ne_zero _
  have ha0 : a ≠ 0 := exp_ne_zero _
  have hb0 : b ≠ 0 := exp_ne_zero _
  rw [ha, ha', hu2]
  field_simp

/-- The normalized `Bi'` in the variable `u = -2ζ`. -/
noncomputable def airyZ_Fbid (u : ℂ) : ℂ :=
  airyBiDeriv (airyZ_Z u) * (Real.sqrt π * exp (-(log (-(3 / 4 : ℂ) * u) / 6)) * exp (u / 2))

/-- The normalized `Bi'` as a combination of the normalized `Ai'` at `W(u)` and `Z(u)`. -/
theorem airyZ_Fbid_eq {u : ℂ} (hu0 : u ≠ 0) (hu : 0 ≤ arg (-(3 / 4 : ℂ) * u)) :
    airyZ_Fbid u = airyAiDeriv (airyZ_W u) / airyPrefactor .aiDeriv (airyZ_W u) -
      I / 2 * exp u * (airyAiDeriv (airyZ_Z u) / airyPrefactor .aiDeriv (airyZ_Z u)) := by
  simp only [airyZ_Fbid, airyPrefactor]
  rw [airyZ_zeta_W hu0 hu, airyZ_quarter_W hu, airyZ_zeta_Z hu0, airyZ_quarter_Z, airyZ_biDeriv_eq,
    mul_one, mul_one, ← airyZ_W_eq]
  have hπs : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  set a := exp (u / 2)
  set L := log (-(3 / 4 : ℂ) * u)
  have ha : exp (-(-u / 2)) = a := by congr 1; ring
  have ha' : exp (-(u / 2)) = a⁻¹ := by rw [exp_neg]
  have hu2 : exp u = a * a := by rw [← exp_add]; congr 1; ring
  have hb' : exp (-(L / 6)) = (exp (L / 6))⁻¹ := by rw [exp_neg]
  have hq : exp (-(π * I / 6)) * exp (-(π * I / 6)) * exp (-(2 * π * I / 3)) = -1 := by
    rw [← exp_add, ← exp_add, show -(π * I / 6) + -(π * I / 6) + -(2 * π * I / 3) = -(π * I) by ring,
      exp_neg, exp_pi_mul_I]; norm_num
  have hq0 : exp (-(π * I / 6)) ≠ 0 := exp_ne_zero _
  have ha0 : a ≠ 0 := exp_ne_zero _
  have hb0 : exp (L / 6) ≠ 0 := exp_ne_zero _
  rw [ha, ha', hu2, hb']
  field_simp
  linear_combination 2 * airyAiDeriv (airyZ_W u) * hq

/-- Centres of the model zeros in the variable `u = -2ζ`. -/
noncomputable def airyZ_ctr (θ : ℝ) (k : ℕ) : ℂ :=
  ((Real.log 2 : ℝ) : ℂ) - ((2 * π * (k + θ) : ℝ) : ℂ) * I

/-- The model-zero centres have real part `log 2`. -/
theorem airyZ_ctr_re (θ : ℝ) (k : ℕ) : (airyZ_ctr θ k).re = Real.log 2 := by
  simp only [airyZ_ctr, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]; ring

/-- The model-zero centre `u_k` has imaginary part `-2π(k + θ)`. -/
theorem airyZ_ctr_im (θ : ℝ) (k : ℕ) : (airyZ_ctr θ k).im = -(2 * π * (k + θ)) := by
  simp only [airyZ_ctr, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]; ring

/-- `e^{u_k}` does not depend on `k`. -/
theorem airyZ_exp_ctr (θ : ℝ) (k : ℕ) : exp (airyZ_ctr θ k) = exp (airyZ_ctr θ 0) := by
  have : airyZ_ctr θ k = airyZ_ctr θ 0 + ((-(k : ℤ) : ℤ) : ℂ) * (2 * π * I) := by
    apply Complex.ext
    · simp only [airyZ_ctr_re, add_re, mul_re, intCast_re, intCast_im, ofReal_re, ofReal_im,
        I_re, I_im, re_ofNat, im_ofNat]; simp
    · simp only [airyZ_ctr_im, add_im, mul_im, mul_re, intCast_re, intCast_im, ofReal_re,
        ofReal_im, I_re, I_im, re_ofNat, im_ofNat]; push_cast; ring
  rw [this, exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/-- Geometry of the discs `|u - u_k| ≤ 1/2`. -/
theorem airyZ_geom {θ : ℝ} (hθ : |θ| ≤ 1 / 4) {k : ℕ} (hk : 1 ≤ k) {u : ℂ}
    (hu : u ∈ closedBall (airyZ_ctr θ k) (1 / 2)) :
    (-(3 / 4 : ℂ) * u).re < 0 ∧ -(-(3 / 4 : ℂ) * u).re < (-(3 / 4 : ℂ) * u).im ∧
      (k : ℝ) ≤ ‖-(3 / 4 : ℂ) * u‖ ∧ u.im < 0 := by
  rw [mem_closedBall, dist_eq_norm] at hu
  have h1 := (abs_le.mp ((abs_re_le_norm (u - airyZ_ctr θ k)).trans hu))
  have h2 := (abs_le.mp ((abs_im_le_norm (u - airyZ_ctr θ k)).trans hu))
  simp only [sub_re, sub_im, airyZ_ctr_re, airyZ_ctr_im] at h1 h2
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hπ := Real.pi_gt_three
  have hθ' := abs_le.mp hθ
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hre : (-(3 / 4 : ℂ) * u).re = -(3 / 4) * u.re := by simp
  have him : (-(3 / 4 : ℂ) * u).im = -(3 / 4) * u.im := by simp
  rw [hre, him]
  refine ⟨by nlinarith, by nlinarith, ?_, by nlinarith⟩
  refine le_trans ?_ (abs_im_le_norm _)
  rw [him, abs_of_pos (by nlinarith)]
  nlinarith

/-- `e^{1/2} < 2`. -/
theorem airyZ_exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

/-- Zeros near the model zeros, for a function of the shape `G(W u) + c e^u G(Z u)`. -/
theorem airyZ_zero_near {F G₁ G₂ : ℂ → ℂ} {c : ℂ} {θ : ℝ} (hθ : |θ| ≤ 1 / 4)
    (hFd : DifferentiableOn ℂ F {u | u.im < 0})
    (hG₁ : ∀ η > 0, ∃ R, ∀ w : ℂ, w ≠ 0 → |arg w| ≤ π / 2 → R ≤ ‖w‖ → ‖G₁ w - 1‖ < η)
    (hG₂ : ∀ η > 0, ∃ R, ∀ w : ℂ, w ≠ 0 → |arg w| ≤ π / 2 → R ≤ ‖w‖ → ‖G₂ w - 1‖ < η)
    (hF : ∀ u : ℂ, u ≠ 0 → 0 ≤ arg (-(3 / 4 : ℂ) * u) →
      F u = G₁ (airyZ_W u) + c * exp u * G₂ (airyZ_Z u))
    (hc : c * exp (airyZ_ctr θ 0) = -1) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ k, K ≤ k → ∃ u ∈ ball (airyZ_ctr θ k) (1 / 2), F u = 0 := by
  have hπ := Real.pi_pos
  obtain ⟨R₁, hR₁⟩ := hG₁ (1 / 13) (by norm_num)
  obtain ⟨R₂, hR₂⟩ := hG₂ (1 / 13) (by norm_num)
  set R := max (max R₁ R₂) 0
  refine ⟨max 1 ⌈Real.exp (3 / 2 * R)⌉₊, le_max_left _ _, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := (le_max_left _ _).trans hk
  have hkR : Real.exp (3 / 2 * R) ≤ k :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hk)
  refine erfZ_exists_zero_of_expModel (A := -1) (by norm_num) le_rfl (by norm_num) ?_ ?_
  · refine (hFd.analyticOnNhd (isOpen_lt continuous_im continuous_const)).mono fun u hu => ?_
    exact (airyZ_geom hθ hk1 hu).2.2.2
  · intro u hu
    have hu' : u ∈ closedBall (airyZ_ctr θ k) (1 / 2) := sphere_subset_closedBall hu
    obtain ⟨g1, g2, g3, -⟩ := airyZ_geom hθ hk1 hu'
    have hv0 : -(3 / 4 : ℂ) * u ≠ 0 := fun h => by simp [h] at g1
    have hu0 : u ≠ 0 := fun h => by simp [h] at hv0
    obtain ⟨a1, a2⟩ := airyZ_arg_bounds g1 g2
    have hargZ : π / 3 < arg (airyZ_Z u) ∧ arg (airyZ_Z u) < π / 2 := by
      rw [airyZ_arg_Z]; constructor <;> linarith
    have hargW : arg (airyZ_W u) = arg (airyZ_Z u) + (-(2 * π / 3)) :=
      Complex.arg_mul_exp_ofReal_mul_I (airyZ_Z_ne_zero u) (airyZ_arg_ok (by linarith)).1
        (airyZ_arg_ok (by linarith)).2
    have hnormZ : R ≤ ‖airyZ_Z u‖ := by
      rw [airyZ_norm_Z]
      have hpos : 0 < ‖-(3 / 4 : ℂ) * u‖ := norm_pos_iff.mpr hv0
      have hlog : 3 / 2 * R ≤ Real.log ‖-(3 / 4 : ℂ) * u‖ := by
        rw [Real.le_log_iff_exp_le hpos]; linarith
      have := Real.add_one_le_exp (2 / 3 * Real.log ‖-(3 / 4 : ℂ) * u‖)
      linarith
    have hnormW : ‖airyZ_W u‖ = ‖airyZ_Z u‖ := by
      rw [airyZ_W, norm_mul, norm_exp_ofReal_mul_I, mul_one]
    have hW0 : airyZ_W u ≠ 0 := mul_ne_zero (airyZ_Z_ne_zero u) (exp_ne_zero _)
    have e1 := hR₁ (airyZ_W u) hW0 (by rw [hargW]; exact abs_le.mpr ⟨by linarith, by linarith⟩)
      (by rw [hnormW]; exact (le_max_left _ _ |>.trans (le_max_left _ _)).trans hnormZ)
    have e2 := hR₂ (airyZ_Z u) (airyZ_Z_ne_zero u) (abs_le.mpr ⟨by linarith, by linarith⟩)
      ((le_max_right _ _ |>.trans (le_max_left _ _)).trans hnormZ)
    have hexp : c * exp u = -exp (u - airyZ_ctr θ k) := by
      rw [show u = airyZ_ctr θ k + (u - airyZ_ctr θ k) by ring, exp_add, airyZ_exp_ctr]
      simp only [add_sub_cancel_left]
      linear_combination exp (u - airyZ_ctr θ k) * hc
    have hd : ‖exp (u - airyZ_ctr θ k)‖ < 2 := by
      rw [norm_exp]
      have := (re_le_norm (u - airyZ_ctr θ k)).trans (le_of_eq (mem_sphere_iff_norm.mp hu))
      exact (Real.exp_le_exp.mpr this).trans_lt airyZ_exp_half_lt_two
    rw [hF u hu0 (by linarith), hexp]
    have : G₁ (airyZ_W u) + -exp (u - airyZ_ctr θ k) * G₂ (airyZ_Z u) -
        -1 * (exp (u - airyZ_ctr θ k) - 1) =
        (G₁ (airyZ_W u) - 1) + (-exp (u - airyZ_ctr θ k)) * (G₂ (airyZ_Z u) - 1) := by ring
    rw [this]
    calc _ ≤ ‖G₁ (airyZ_W u) - 1‖ + ‖exp (u - airyZ_ctr θ k)‖ * ‖G₂ (airyZ_Z u) - 1‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_neg]
      _ < 1 / 13 + 2 * (1 / 13) := by
          gcongr
      _ < ‖(-1 : ℂ)‖ * (1 / 2) / 2 := by norm_num

/-- `u ↦ log(-(3/4) u)` is holomorphic on the lower half-plane. -/
theorem airyZ_differentiableAt_Z {u : ℂ} (hu : u.im < 0) :
    DifferentiableAt ℂ (fun u => log (-(3 / 4 : ℂ) * u)) u := by
  have hs : -(3 / 4 : ℂ) * u ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right; simp; linarith
  exact ((differentiableAt_id.const_mul _).clog hs)

/-- The normalized `Bi` is holomorphic on the lower half-plane. -/
theorem airyZ_Fbi_differentiableOn : DifferentiableOn ℂ airyZ_Fbi {u | u.im < 0} := by
  intro u hu
  have hL := airyZ_differentiableAt_Z hu
  have hZ : DifferentiableAt ℂ airyZ_Z u := (hL.const_mul _).cexp
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold airyZ_Fbi
  exact ((differentiable_airyBi _).comp u hZ).mul
    (((differentiableAt_const _).mul (hL.div_const _).cexp).mul
      ((differentiableAt_id.div_const _).cexp))

/-- The normalized `Bi'` is holomorphic on the lower half-plane. -/
theorem airyZ_Fbid_differentiableOn : DifferentiableOn ℂ airyZ_Fbid {u | u.im < 0} := by
  intro u hu
  have hL := airyZ_differentiableAt_Z hu
  have hZ : DifferentiableAt ℂ airyZ_Z u := (hL.const_mul _).cexp
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold airyZ_Fbid
  exact ((hasDerivAt_airyBiDeriv _).differentiableAt.comp u hZ).mul
    (((differentiableAt_const _).mul (hL.div_const _).neg.cexp).mul
      ((differentiableAt_id.div_const _).cexp))

/-- `Ai(w)/(leading term) → 1` uniformly as `w → ∞` in `|arg w| ≤ π/2` (quantitative form). -/
theorem airyZ_small_ai {η : ℝ} (hη : 0 < η) :
    ∃ R, ∀ w : ℂ, w ≠ 0 → |arg w| ≤ π / 2 → R ≤ ‖w‖ →
      ‖airyAi w / airyPrefactor .ai w - 1‖ < η := by
  have h := airyRot_airyAi_expansion (δ := π / 2) (by positivity) (by linarith [Real.pi_pos])
  rw [show π - π / 2 = π / 2 by ring] at h
  exact airyZ_small h (by simp [airyExpansionCoeff, airyReal_airyU_zero]) hη

/-- `Ai'(w)/(leading term) → 1` as `w → ∞` in `|arg w| ≤ π/2` (quantitative form). -/
theorem airyZ_small_aiDeriv {η : ℝ} (hη : 0 < η) :
    ∃ R, ∀ w : ℂ, w ≠ 0 → |arg w| ≤ π / 2 → R ≤ ‖w‖ →
      ‖airyAiDeriv w / airyPrefactor .aiDeriv w - 1‖ < η := by
  have h := airyRot_airyAiDeriv_expansion (δ := π / 2) (by positivity) (by linarith [Real.pi_pos])
  rw [show π - π / 2 = π / 2 by ring] at h
  exact airyZ_small h (by simp [airyExpansionCoeff, airyReal_airyV_zero]) hη

/-- From zeros near the model zeros to infinitely many zeros in the upper sector. -/
theorem airyZ_infinite {f : ℂ → ℂ} {F : ℂ → ℂ} {θ : ℝ} (hθ : |θ| ≤ 1 / 4)
    (hfF : ∀ u, F u = 0 → f (airyZ_Z u) = 0)
    (hK : ∃ K : ℕ, 1 ≤ K ∧ ∀ k, K ≤ k → ∃ u ∈ ball (airyZ_ctr θ k) (1 / 2), F u = 0) :
    Set.Infinite (airyUpperZeroSet f) := by
  obtain ⟨K, hK1, hK⟩ := hK
  choose! g hgb hg0 using hK
  have hmem : ∀ n : ℕ, airyZ_Z (g (n + K)) ∈ airyUpperZeroSet f := by
    intro n
    have hk : K ≤ n + K := Nat.le_add_left K n
    obtain ⟨g1, g2, -, -⟩ := airyZ_geom hθ (hK1.trans hk) (ball_subset_closedBall (hgb _ hk))
    obtain ⟨a1, a2⟩ := airyZ_arg_bounds g1 g2
    refine ⟨?_, ?_, hfF _ (hg0 _ hk)⟩ <;> rw [airyZ_arg_Z] <;> linarith
  refine Set.infinite_of_injective_forall_mem (f := fun n => airyZ_Z (g (n + K))) ?_ hmem
  intro m n hmn
  have hu0 : ∀ j : ℕ, g (j + K) ≠ 0 := by
    intro j h
    obtain ⟨g1, -⟩ := airyZ_geom hθ (hK1.trans (Nat.le_add_left K j))
      (ball_subset_closedBall (hgb _ (Nat.le_add_left K j)))
    simp [h] at g1
  have hz := congrArg airyZetaComplex hmn
  simp only [airyZ_zeta_Z (hu0 _)] at hz
  have he : g (m + K) = g (n + K) := by linear_combination -2 * hz
  have hm := hgb _ (Nat.le_add_left K m)
  have hn := hgb _ (Nat.le_add_left K n)
  rw [he, mem_ball, dist_eq_norm] at hm
  rw [mem_ball, dist_eq_norm] at hn
  have h1 := abs_lt.mp ((abs_im_le_norm _).trans_lt hm)
  have h2 := abs_lt.mp ((abs_im_le_norm _).trans_lt hn)
  simp only [sub_im, airyZ_ctr_im] at h1 h2
  have hπ := Real.pi_gt_three
  have hlt : ((m : ℝ) - n) * (2 * π) < 1 ∧ -1 < ((m : ℝ) - n) * (2 * π) := by
    push_cast at h1 h2; constructor <;> nlinarith
  have c1 : (m : ℝ) - n < 1 := by nlinarith
  have c2 : -1 < (m : ℝ) - n := by nlinarith
  have d1 : (m : ℤ) - n < 1 := by exact_mod_cast c1
  have d2 : -1 < (m : ℤ) - n := by exact_mod_cast c2
  omega

end UpperZeros

/-- The nonreal-zero sectors of Bi and Bi', DLMF §9.9(i). -/
theorem airyBi_complex_zeros_sector {z : ℂ} (hz : airyBi z = 0) (him : z.im ≠ 0) :
    π / 3 < |arg z| ∧ |arg z| < π / 2 := by
  sorry

/-- Infinitely many zeros in the upper sector, DLMF §9.9(i). -/
theorem airyBi_infinite_complex_zeros :
    Set.Infinite (airyUpperZeroSet airyBi) := by
  refine airyZ_infinite (F := airyZ_Fbi) (θ := -(1 / 4)) (by norm_num [abs_of_neg]) ?_ ?_
  · intro u hu
    simp only [airyZ_Fbi, mul_eq_zero, ofReal_eq_zero, exp_ne_zero, or_false] at hu
    rcases hu with h | h
    · exact h
    · exact absurd h (Real.sqrt_pos.mpr Real.pi_pos).ne'
  refine airyZ_zero_near (by norm_num [abs_of_neg]) airyZ_Fbi_differentiableOn
    (fun η hη => airyZ_small_ai hη) (fun η hη => airyZ_small_ai hη)
    (fun u hu0 hu => airyZ_Fbi_eq hu0 hu) ?_
  rw [airyZ_ctr, exp_sub, ← ofReal_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have : exp (((2 * π * ((0 : ℕ) + -(1 / 4)) : ℝ) : ℂ) * I) = -I := by
    rw [show (((2 * π * ((0 : ℕ) + -(1 / 4)) : ℝ) : ℂ) * I) = -((π / 2 : ℂ) * I) by push_cast; ring,
      exp_neg, exp_pi_div_two_mul_I, inv_I]
  rw [this]; field_simp; push_cast; ring_nf

/-- The upper-sector complex-zero specification, DLMF §9.9(i). -/
theorem airyBiComplexZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyBiComplexZero k ∈ airyUpperZeroSet airyBi := by
  sorry

/-- Complex-zero enumeration in increasing modulus, DLMF §9.9(i). -/
theorem airyBiComplexZero_enumeration :
    StrictMonoOn (fun k => ‖airyBiComplexZero k‖) (Ici 1) ∧
      ∀ z ∈ airyUpperZeroSet airyBi, ∃ k : ℕ, 1 ≤ k ∧ airyBiComplexZero k = z := by
  sorry

/-- The nonreal-zero sectors of Bi and Bi', DLMF §9.9(i). -/
theorem airyBiDeriv_complex_zeros_sector {z : ℂ} (hz : airyBiDeriv z = 0) (him : z.im ≠ 0) :
    π / 3 < |arg z| ∧ |arg z| < π / 2 := by
  sorry

/-- Infinitely many zeros in the upper sector, DLMF §9.9(i). -/
theorem airyBiDeriv_infinite_complex_zeros :
    Set.Infinite (airyUpperZeroSet airyBiDeriv) := by
  refine airyZ_infinite (F := airyZ_Fbid) (θ := 1 / 4) (by norm_num [abs_of_pos]) ?_ ?_
  · intro u hu
    simp only [airyZ_Fbid, mul_eq_zero, ofReal_eq_zero, exp_ne_zero, or_false] at hu
    rcases hu with h | h
    · exact h
    · exact absurd h (Real.sqrt_pos.mpr Real.pi_pos).ne'
  refine airyZ_zero_near (c := -(I / 2)) (by norm_num [abs_of_pos]) airyZ_Fbid_differentiableOn
    (fun η hη => airyZ_small_aiDeriv hη) (fun η hη => airyZ_small_aiDeriv hη)
    (fun u hu0 hu => by rw [airyZ_Fbid_eq hu0 hu]; ring) ?_
  rw [airyZ_ctr, exp_sub, ← ofReal_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have : exp (((2 * π * ((0 : ℕ) + 1 / 4) : ℝ) : ℂ) * I) = I := by
    rw [show (((2 * π * ((0 : ℕ) + 1 / 4) : ℝ) : ℂ) * I) = ((π / 2 : ℂ) * I) by push_cast; ring,
      exp_pi_div_two_mul_I]
  rw [this]; field_simp; push_cast; ring_nf

/-- The upper-sector complex-zero specification, DLMF §9.9(i). -/
theorem airyBiDerivComplexZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyBiDerivComplexZero k ∈ airyUpperZeroSet airyBiDeriv := by
  sorry

/-- Complex-zero enumeration in increasing modulus, DLMF §9.9(i). -/
theorem airyBiDerivComplexZero_enumeration :
    StrictMonoOn (fun k => ‖airyBiDerivComplexZero k‖) (Ici 1) ∧
      ∀ z ∈ airyUpperZeroSet airyBiDeriv, ∃ k : ℕ, 1 ≤ k ∧ airyBiDerivComplexZero k = z := by
  sorry

/-- The phases at the zeros: `θ(a_k) = kπ` and `φ(a'_{k+1}) = kπ` (DLMF 9.9.1). -/
@[dlmf 9.9.E1]
theorem airyAiZero_phase {k : ℕ} (hk : 1 ≤ k) :
    airyPhase (airyAiZero k) = k * π ∧ airyDerivPhase (airyAiDerivZero (k + 1)) = k * π := by
  refine ⟨?_, ?_⟩
  · rw [airyAiZero, (phaseZeroData_airyAi.spec hk).2.2.2, zero_add]
  · rw [airyAiDerivZero, (phaseZeroData_airyAiDeriv.spec (by omega : 1 ≤ k + 1)).2.2.2]
    push_cast; ring

/-- The phases at the zeros: `θ(b_k) = (k - 1/2)π` and `φ(b'_k) = (k - 1/2)π` (DLMF 9.9.2). -/
@[dlmf 9.9.E2]
theorem airyBiZero_phase {k : ℕ} (hk : 1 ≤ k) :
    airyPhase (airyBiZero k) = ((k : ℝ) - 1 / 2) * π ∧
      airyDerivPhase (airyBiDerivZero k) = ((k : ℝ) - 1 / 2) * π := by
  refine ⟨?_, ?_⟩
  · rw [airyBiZero, (phaseZeroData_airyBi.spec hk).2.2.2]; ring
  · rw [airyBiDerivZero, (phaseZeroData_airyBiDeriv.spec hk).2.2.2]; ring

/-- `Ai'(a_k) = (-1)^{k-1}/(π M(a_k))` (DLMF 9.9.3). -/
@[dlmf 9.9.E3]
theorem airyAiZero_value {k : ℕ} (hk : 1 ≤ k) :
    airyAiDeriv (airyAiZero k) = (-1 : ℂ) ^ (k - 1) / (π * airyModulus (airyAiZero k)) := by
  obtain ⟨-, h0, -, hθ⟩ := phaseZeroData_airyAi.spec hk
  set x := airyRealZero airyAiReal k
  change airyAiDeriv x = _
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hW := wronskian_airyReal x
  have hb := airyBiReal_eq_modulus_cos x
  rw [hθ, zero_add, Real.cos_nat_mul_pi] at hb
  rw [h0, hb] at hW
  have hM := (airyModulus_pos x).ne'
  have hπ := Real.pi_ne_zero
  have hr : airyAiDerivReal x = (-1) ^ n / (π * airyModulus x) := by
    rw [eq_div_iff hπ] at hW
    rw [eq_div_iff (mul_ne_zero hπ hM)]
    linear_combination (-1 : ℝ) ^ n * hW - (airyAiDerivReal x * airyModulus x * π) *
      neg_one_pow_sq_real n
  rw [airyAiDeriv_ofReal_eq, hr, Nat.add_sub_cancel]
  push_cast; rfl

/-- `Bi'(b_k) = (-1)^{k-1}/(π M(b_k))` (DLMF 9.9.3). -/
@[dlmf 9.9.E3]
theorem airyBiZero_value {k : ℕ} (hk : 1 ≤ k) :
    airyBiDeriv (airyBiZero k) = (-1 : ℂ) ^ (k - 1) / (π * airyModulus (airyBiZero k)) := by
  obtain ⟨-, h0, -, hθ⟩ := phaseZeroData_airyBi.spec hk
  set x := airyRealZero airyBiReal k
  change airyBiDeriv x = _
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hW := wronskian_airyReal x
  have ha := airyAiReal_eq_modulus_sin x
  rw [hθ, show -(π / 2) + ((n + 1 : ℕ) : ℝ) * π = n * π + π / 2 by push_cast; ring,
    Real.sin_add_pi_div_two, Real.cos_nat_mul_pi] at ha
  rw [h0, ha] at hW
  have hM := (airyModulus_pos x).ne'
  have hπ := Real.pi_ne_zero
  have hr : airyBiDerivReal x = (-1) ^ n / (π * airyModulus x) := by
    rw [eq_div_iff hπ] at hW
    rw [eq_div_iff (mul_ne_zero hπ hM)]
    linear_combination (-1 : ℝ) ^ n * hW - (airyBiDerivReal x * airyModulus x * π) *
      neg_one_pow_sq_real n
  rw [airyBiDeriv_ofReal_eq, hr, Nat.add_sub_cancel]
  push_cast; rfl

/-- `Ai(a'_k) = (-1)^{k-1}/(π N(a'_k))` (DLMF 9.9.4). -/
@[dlmf 9.9.E4]
theorem airyAiDerivZero_value {k : ℕ} (hk : 1 ≤ k) :
    airyAi (airyAiDerivZero k) = (-1 : ℂ) ^ (k - 1) / (π * airyDerivModulus (airyAiDerivZero k)) := by
  obtain ⟨-, h0, -, hθ⟩ := phaseZeroData_airyAiDeriv.spec hk
  set x := airyRealZero airyAiDerivReal k
  change airyAi x = _
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hW := wronskian_airyReal x
  have hb := airyBiDerivReal_eq_modulus_cos x
  rw [hθ, show -π + ((n + 1 : ℕ) : ℝ) * π = n * π by push_cast; ring, Real.cos_nat_mul_pi] at hb
  rw [h0, hb] at hW
  have hM := (airyDerivModulus_pos x).ne'
  have hπ := Real.pi_ne_zero
  have hr : airyAiReal x = (-1) ^ n / (π * airyDerivModulus x) := by
    rw [eq_div_iff hπ] at hW
    rw [eq_div_iff (mul_ne_zero hπ hM)]
    linear_combination (-1 : ℝ) ^ n * hW - (airyAiReal x * airyDerivModulus x * π) *
      neg_one_pow_sq_real n
  rw [airyAi_ofReal_eq, hr, Nat.add_sub_cancel]
  push_cast; rfl

/-- `Bi(b'_k) = (-1)^k/(π N(b'_k))` (DLMF 9.9.4). -/
@[dlmf 9.9.E4]
theorem airyBiDerivZero_value {k : ℕ} (hk : 1 ≤ k) :
    airyBi (airyBiDerivZero k) = (-1 : ℂ) ^ (k) / (π * airyDerivModulus (airyBiDerivZero k)) := by
  obtain ⟨-, h0, -, hθ⟩ := phaseZeroData_airyBiDeriv.spec hk
  set x := airyRealZero airyBiDerivReal k
  change airyBi x = _
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hW := wronskian_airyReal x
  have ha := airyAiDerivReal_eq_modulus_sin x
  rw [hθ, show -(π / 2) + ((n + 1 : ℕ) : ℝ) * π = n * π + π / 2 by push_cast; ring,
    Real.sin_add_pi_div_two, Real.cos_nat_mul_pi] at ha
  rw [h0, ha] at hW
  have hM := (airyDerivModulus_pos x).ne'
  have hπ := Real.pi_ne_zero
  have hr : airyBiReal x = (-1) ^ (n + 1) / (π * airyDerivModulus x) := by
    rw [eq_div_iff hπ] at hW
    rw [eq_div_iff (mul_ne_zero hπ hM)]
    linear_combination (-(-1 : ℝ) ^ n) * hW - (airyBiReal x * airyDerivModulus x * π) *
      neg_one_pow_sq_real n
  rw [airyBi_ofReal_eq, hr]
  push_cast; rfl

/-- Differentiability of the continuous-index level function `t ↦ g⁻¹((t + d)π)` of a
decreasing phase `g` on `(-∞, 0]`. -/
theorem hasDerivAt_phaseLevel {g : ℝ → ℝ} {g' d t₀ : ℝ} (hgc : Continuous g)
    (hanti : StrictAntiOn g (Iic 0)) (htend : Tendsto g atBot atTop)
    (ht₀ : g 0 < (t₀ + d) * π)
    (hd : HasDerivAt g g' (Classical.epsilon fun x : ℝ => x ≤ 0 ∧ g x = (t₀ + d) * π))
    (hg' : g' ≠ 0) :
    HasDerivAt (fun t : ℝ => Classical.epsilon fun x : ℝ => x ≤ 0 ∧ g x = (t + d) * π)
      (π / g') t₀ := by
  have hπ := Real.pi_pos
  set α : ℝ → ℝ := fun t => Classical.epsilon fun x : ℝ => x ≤ 0 ∧ g x = (t + d) * π with hα
  set U : Set ℝ := {t | g 0 < (t + d) * π} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const ((continuous_id.add continuous_const).mul
    continuous_const)
  have hex : ∀ t ∈ U, ∃ x ≤ 0, g x = (t + d) * π := by
    intro t ht
    obtain ⟨x0, hx0⟩ := (htend.eventually (eventually_ge_atTop ((t + d) * π))).exists_forall_of_atBot
    obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc' (min_le_right x0 0) hgc.continuousOn
      (mem_Icc.mpr ⟨(ht : g 0 < _).le, hx0 _ (min_le_left _ _)⟩)
    exact ⟨x, hx.2, hgx⟩
  have hspec : ∀ t ∈ U, α t ≤ 0 ∧ g (α t) = (t + d) * π := fun t ht =>
    Classical.epsilon_spec (hex t ht)
  have hneg : ∀ t ∈ U, α t < 0 := fun t ht => by
    refine lt_of_le_of_ne (hspec t ht).1 fun h0 => ?_
    have := (hspec t ht).2; rw [h0] at this; exact absurd this (ht : g 0 < _).ne
  have hmono : MonotoneOn (fun t => -α t) U := by
    intro t₁ h₁ t₂ h₂ h12
    simp only [neg_le_neg_iff]
    by_contra hn; push Not at hn
    have := hanti (mem_Iic.mpr (hspec t₁ h₁).1) (mem_Iic.mpr (hspec t₂ h₂).1) hn
    rw [(hspec t₁ h₁).2, (hspec t₂ h₂).2] at this
    nlinarith
  have himage : (fun t => -α t) '' U = Ioi 0 := by
    ext y
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨t, ht, rfl⟩; linarith [hneg t ht]
    · intro hy
      have hgy : g 0 < g (-y) := hanti (mem_Iic.mpr (by linarith)) (mem_Iic.mpr le_rfl)
        (by linarith)
      set t := g (-y) / π - d
      have htU : t ∈ U := by
        show g 0 < (t + d) * π
        simp only [t]; field_simp; simpa using hgy
      refine ⟨t, htU, ?_⟩
      have h1 := hspec t htU
      have h2 : g (-y) = (t + d) * π := by simp only [t]; field_simp; ring
      have := hanti.injOn (mem_Iic.mpr h1.1) (mem_Iic.mpr (by linarith : -y ≤ 0))
        (h1.2.trans h2.symm)
      linarith
  have hcont : ContinuousAt α t₀ := by
    have h := continuousAt_of_monotoneOn_of_image_mem_nhds hmono (hUo.mem_nhds ht₀)
      (by rw [himage]; exact Ioi_mem_nhds (by linarith [hneg t₀ ht₀]))
    simpa using h.neg
  have hf : HasDerivAt (fun x => g x / π - d) (g' / π) (α t₀) := (hd.div_const π).sub_const d
  have := HasDerivAt.of_local_left_inverse hcont hf (div_ne_zero hg' hπ.ne')
    (Filter.mem_of_superset (hUo.mem_nhds ht₀) fun t ht => by
      simp only [mem_ofPred_eq, (hspec t ht).2]; field_simp; ring)
  simpa [inv_div] using this

/-- `(r²)^{-1/2} = r⁻¹` as a complex power, for `r > 0`. -/
theorem ofReal_sq_cpow_neg_half {r : ℝ} (hr : 0 < r) :
    ((r ^ 2 : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = ((r⁻¹ : ℝ) : ℂ) := by
  rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity)]
  congr 1
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq hr.le]

/-- Continuous-index interpolation used in DLMF §9.9(iii). -/
theorem airyAiZeroContinuous_natCast {k : ℕ} (hk : 1 ≤ k) :
    airyAiZeroContinuous k = airyAiZero k := by
  obtain ⟨h1, -, -, hθ⟩ := phaseZeroData_airyAi.spec hk
  have hP : airyAiZero k ≤ 0 ∧ airyPhase (airyAiZero k) = k * π := ⟨h1.le, by
    rw [airyAiZero, hθ, zero_add]⟩
  have hε := Classical.epsilon_spec (p := fun x : ℝ => x ≤ 0 ∧ airyPhase x = k * π) ⟨_, hP⟩
  exact airy_phase_monotone.injOn hε.1 hP.1 (hε.2.trans hP.2.symm)

/-- `Ai'(a_k) = (-1)^{k-1} (-a'(k))^{-1/2}`, with `a(k)` the continuous zero function
(DLMF 9.9.5). -/
@[dlmf 9.9.E5]
theorem airyAiZeroContinuous_derivative_value {k : ℕ} (hk : 1 ≤ k) :
    airyAiDeriv (airyAiZero k) = (-1 : ℂ) ^ (k - 1) *
      ((-deriv airyAiZeroContinuous k : ℝ) : ℂ) ^ (-1 / 2 : ℂ) := by
  have hπ := Real.pi_pos
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hfun : airyAiZeroContinuous =
      fun t : ℝ => Classical.epsilon fun x : ℝ => x ≤ 0 ∧ airyPhase x = (t + 0) * π := by
    funext t; simp only [add_zero]; rfl
  have hnat := airyAiZeroContinuous_natCast hk
  have hd := hasDerivAt_phaseLevel (d := 0) (t₀ := k) airyPhase_continuous airy_phase_monotone
    tendsto_airyPhase_atBot (by simp [airyPhase]; nlinarith)
    (hasDerivAt_airyPhase _)
    (neg_ne_zero.mpr (one_div_pos.mpr (mul_pos hπ (pow_pos (airyModulus_pos _) 2))).ne')
  have hε : (Classical.epsilon fun x : ℝ => x ≤ 0 ∧ airyPhase x = ((k : ℝ) + 0) * π) =
      airyAiZero k := by rw [← hnat, hfun]
  rw [← hfun, hε] at hd
  rw [hd.deriv, airyAiZero_value hk]
  have hM := airyModulus_pos (airyAiZero k)
  rw [show -(π / -(1 / (π * airyModulus (airyAiZero k) ^ 2))) =
      (π * airyModulus (airyAiZero k)) ^ 2 by field_simp,
    ofReal_sq_cpow_neg_half (by positivity)]
  push_cast
  ring

/-- Continuous-index interpolation used in DLMF §9.9(iii). -/
theorem airyAiDerivZeroContinuous_natCast {k : ℕ} (hk : 1 ≤ k) :
    airyAiDerivZeroContinuous k = airyAiDerivZero k := by
  obtain ⟨h1, -, -, hθ⟩ := phaseZeroData_airyAiDeriv.spec hk
  have hP : airyAiDerivZero k ≤ 0 ∧ airyDerivPhase (airyAiDerivZero k) = (k - 1) * π := ⟨h1.le, by
    rw [airyAiDerivZero, hθ]; ring⟩
  have hε := Classical.epsilon_spec
    (p := fun x : ℝ => x ≤ 0 ∧ airyDerivPhase x = ((k : ℝ) - 1) * π) ⟨_, hP⟩
  exact airy_derivPhase_monotone.injOn hε.1 hP.1 (hε.2.trans hP.2.symm)

/-- `Ai(a'_k) = (-1)^{k-1} (a'_k · da'(k)/dk)^{-1/2}`, with `a'(k)` the continuous zero
function (DLMF 9.9.5). -/
@[dlmf 9.9.E5]
theorem airyAiDerivZeroContinuous_derivative_value {k : ℕ} (hk : 1 ≤ k) :
    airyAi (airyAiDerivZero k) = (-1 : ℂ) ^ (k - 1) *
      ((airyAiDerivZero k * deriv airyAiDerivZeroContinuous k : ℝ) : ℂ) ^ (-1 / 2 : ℂ) := by
  have hπ := Real.pi_pos
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hfun : airyAiDerivZeroContinuous =
      fun t : ℝ => Classical.epsilon fun x : ℝ => x ≤ 0 ∧ airyDerivPhase x = (t + -1) * π := by
    funext t; simp only [← sub_eq_add_neg]; rfl
  have hnat := airyAiDerivZeroContinuous_natCast hk
  have hneg := (airyAiDerivZero_spec hk).1
  have hε : (Classical.epsilon fun x : ℝ => x ≤ 0 ∧ airyDerivPhase x = ((k : ℝ) + -1) * π) =
      airyAiDerivZero k := by rw [← hnat, hfun]
  have hd := hasDerivAt_phaseLevel (d := -1) (t₀ := k) airyDerivPhase_continuous
    airy_derivPhase_monotone tendsto_airyDerivPhase_atBot
    (by simp [airyDerivPhase]; nlinarith) (hasDerivAt_airyDerivPhase _)
    (by
      rw [hε]
      have := airyDerivModulus_pos (airyAiDerivZero k)
      exact div_ne_zero hneg.ne (by positivity))
  rw [← hfun, hε] at hd
  rw [hd.deriv, airyAiDerivZero_value hk]
  have hM := airyDerivModulus_pos (airyAiDerivZero k)
  rw [show airyAiDerivZero k * (π / (airyAiDerivZero k / (π * airyDerivModulus (airyAiDerivZero k) ^ 2))) =
      (π * airyDerivModulus (airyAiDerivZero k)) ^ 2 by
        have := hneg.ne; field_simp,
    ofReal_sq_cpow_neg_half (by positivity)]
  push_cast
  ring

/-- The common all-order T,U,V,W expansions, including every printed coefficient and real/complex zero family in DLMF 9.9.6–9.9.21 (DLMF 9.9.18). -/
@[dlmf 9.9.E6, dlmf 9.9.E7, dlmf 9.9.E8, dlmf 9.9.E9, dlmf 9.9.E10, dlmf 9.9.E11, dlmf 9.9.E12, dlmf 9.9.E13, dlmf 9.9.E14, dlmf 9.9.E15, dlmf 9.9.E16, dlmf 9.9.E17, dlmf 9.9.E18, dlmf 9.9.E19, dlmf 9.9.E20, dlmf 9.9.E21]
theorem airy_zero_common_asymptotic_coefficients :
    ∃ cT cU cV cW : ℕ → ℂ,
      (∀ n < 6, cT n = ([1, 5/48, -5/36, 77125/82944, -108056875/6967296, 162375596875/334430208] : List ℂ)[n]! ∧
      ∀ n < 6, cU n = ([1, -7/48, 35/288, -181223/207360, 18683371/1244160, -91145884361/191102976] : List ℂ)[n]! ∧
      ∀ n < 6, cV n = ([1, 5/48, -1525/4608, 2397875/663552, -74898940625/891813888, 144198303734375/42807066624] : List ℂ)[n]! ∧
      ∀ n < 6, cW n = ([1, -7/96, 1673/6144, -84394709/26542080, 780277135421/10192158720, -204449051051945/65229815808] : List ℂ)[n]!) ∧
      HasAiryZeroExpansion (2 / 3) (fun k => -(airyAiZero (k + 1) : ℂ)) (airyZeroArgument 1) cT ∧
      HasAiryZeroExpansion (2 / 3) (fun k => -(airyAiDerivZero (k + 1) : ℂ)) (airyZeroArgument 3) cU ∧
      HasAiryZeroExpansion (2 / 3) (fun k => -(airyBiZero (k + 1) : ℂ)) (airyZeroArgument 3) cT ∧
      HasAiryZeroExpansion (2 / 3) (fun k => -(airyBiDerivZero (k + 1) : ℂ)) (airyZeroArgument 1) cU ∧
      HasAiryZeroExpansion (1 / 6)
        (fun k => Real.sqrt π * (-1 : ℂ) ^ (k) * airyAiDeriv (airyAiZero (k + 1))) (airyZeroArgument 1) cV ∧
      HasAiryZeroExpansion (-1 / 6)
        (fun k => Real.sqrt π * (-1 : ℂ) ^ (k) * airyAi (airyAiDerivZero (k + 1))) (airyZeroArgument 3) cW ∧
      HasAiryZeroExpansion (1 / 6)
        (fun k => Real.sqrt π * (-1 : ℂ) ^ (k) * airyBiDeriv (airyBiZero (k + 1))) (airyZeroArgument 3) cV ∧
      HasAiryZeroExpansion (-1 / 6)
        (fun k => Real.sqrt π * (-1 : ℂ) ^ (k + 1) * airyBi (airyBiDerivZero (k + 1))) (airyZeroArgument 1) cW ∧
      HasAiryZeroExpansion (2 / 3)
        (fun k => exp (-π * I / 3) * airyBiComplexZero (k + 1)) (airyComplexZeroArgument 1) cT ∧
      HasAiryZeroExpansion (2 / 3)
        (fun k => exp (-π * I / 3) * airyBiDerivComplexZero (k + 1)) (airyComplexZeroArgument 3) cU ∧
      HasAiryZeroExpansion (1 / 6)
        (fun k => Real.sqrt π / Real.sqrt 2 * (-1 : ℂ) ^ (k + 1) * exp (π * I / 6) *
          airyBiDeriv (airyBiComplexZero (k + 1))) (airyComplexZeroArgument 1) cV ∧
      HasAiryZeroExpansion (-1 / 6)
        (fun k => Real.sqrt π / Real.sqrt 2 * (-1 : ℂ) ^ (k) * exp (-π * I / 6) *
          airyBi (airyBiDerivComplexZero (k + 1))) (airyComplexZeroArgument 3) cW := by
  sorry

/-- Interpolation on three disjoint injectively parametrized families of points. -/
private lemma airyZeros_exists_interp3 {a b c : ℕ → ℂ} (ha : Function.Injective a)
    (hb : Function.Injective b) (hc : Function.Injective c) (hab : ∀ k j, a k ≠ b j)
    (hac : ∀ k j, a k ≠ c j) (hbc : ∀ k j, b k ≠ c j) (fa fb fc : ℕ → ℂ) :
    ∃ F : ℂ → ℂ, ∀ k, F (a k) = fa k ∧ F (b k) = fb k ∧ F (c k) = fc k := by
  classical
  refine ⟨fun z => if h : ∃ k, a k = z then fa h.choose else if h : ∃ k, b k = z then
    fb h.choose else if h : ∃ k, c k = z then fc h.choose else 0, fun k => ⟨?_, ?_, ?_⟩⟩
  · have h : ∃ j, a j = a k := ⟨k, rfl⟩
    simp only [h, dite_true]
    rw [ha h.choose_spec]
  · have h : ∃ j, b j = b k := ⟨k, rfl⟩
    have h' : ¬ ∃ j, a j = b k := fun ⟨j, hj⟩ => hab j k hj
    simp only [h, h', dite_true, dite_false]
    rw [hb h.choose_spec]
  · have h : ∃ j, c j = c k := ⟨k, rfl⟩
    have h' : ¬ ∃ j, a j = c k := fun ⟨j, hj⟩ => hac j k hj
    have h'' : ¬ ∃ j, b j = c k := fun ⟨j, hj⟩ => hbc j k hj
    simp only [h, h', h'', dite_true, dite_false]
    rw [hc h.choose_spec]

/-- Real part of the real zero argument. -/
private lemma airyZeros_re_arg (o : ℝ) (k : ℕ) :
    (airyZeroArgument o k).re = 3 * π / 8 * (4 * (k + 1 : ℝ) - o) := by
  simp [airyZeroArgument]

/-- The real zero argument is real. -/
private lemma airyZeros_im_arg (o : ℝ) (k : ℕ) : (airyZeroArgument o k).im = 0 := by
  simp [airyZeroArgument]

/-- Real part of the complex argument. -/
private lemma airyZeros_re_carg (o : ℝ) (k : ℕ) :
    (airyComplexZeroArgument o k).re = 3 * π / 8 * (4 * (k + 1 : ℝ) - o) := by
  simp [airyComplexZeroArgument, airyZeroArgument, -ofNat_log]

/-- Imaginary part of the complex zero argument. -/
private lemma airyZeros_im_carg (o : ℝ) (k : ℕ) :
    (airyComplexZeroArgument o k).im = 3 * Real.log 2 / 4 := by
  simp [airyComplexZeroArgument, airyZeroArgument, -ofNat_log]

/-- Cancelling the common factor `3π/8`. -/
private lemma airyZeros_re_inj {o o' : ℝ} {k j : ℕ}
    (h : 3 * π / 8 * (4 * (k + 1 : ℝ) - o) = 3 * π / 8 * (4 * (j + 1 : ℝ) - o')) :
    4 * (k : ℝ) - o = 4 * j - o' := by
  have hπ : (3 * π / 8 : ℝ) ≠ 0 := by positivity
  have := mul_left_cancel₀ hπ h
  linarith

/-- The real zero arguments are injective in `k`. -/
private lemma airyZeros_inj (o : ℝ) : Function.Injective (airyZeroArgument o) := fun k j h => by
  have := airyZeros_re_inj (congrArg re h |>.trans (airyZeros_re_arg o j) |>.symm.trans
    (airyZeros_re_arg o k) |>.symm)
  exact_mod_cast (by linarith : (k : ℝ) = j)

/-- The complex zero arguments are injective in `k`. -/
private lemma airyZeros_cinj (o : ℝ) : Function.Injective (airyComplexZeroArgument o) :=
  fun k j h => by
  have := airyZeros_re_inj (congrArg re h |>.trans (airyZeros_re_carg o j) |>.symm.trans
    (airyZeros_re_carg o k) |>.symm)
  exact_mod_cast (by linarith : (k : ℝ) = j)

/-- The offsets `1` and `3` give disjoint real arguments. -/
private lemma airyZeros_ne13 (k j : ℕ) : airyZeroArgument 1 k ≠ airyZeroArgument 3 j := by
  intro h
  have := airyZeros_re_inj (congrArg re h |>.trans (airyZeros_re_arg 3 j) |>.symm.trans
    (airyZeros_re_arg 1 k) |>.symm)
  have h3 : (2 * ((j : ℤ) - k) - 1 : ℤ) = 0 := by
    have : (2 * ((j : ℝ) - k) - 1) = 0 := by linarith
    exact_mod_cast this
  omega

/-- Real and complex zero arguments never coincide. -/
private lemma airyZeros_rcne (o o' : ℝ) (k j : ℕ) :
    airyZeroArgument o k ≠ airyComplexZeroArgument o' j := by
  intro h
  have := congrArg im h
  rw [airyZeros_im_arg, airyZeros_im_carg] at this
  have : 0 < Real.log 2 := Real.log_pos one_lt_two
  linarith

/-- Exact common T,U,V,W parametrizations in DLMF 9.9.6–9.9.17.
Their all-order asymptotics, with the auxiliary functions eliminated, are given by
`airy_zero_common_asymptotic_coefficients`. No analytic continuation is asserted here. -/
@[dlmf 9.9.E6, dlmf 9.9.E7, dlmf 9.9.E8, dlmf 9.9.E9, dlmf 9.9.E10, dlmf 9.9.E11,
  dlmf 9.9.E12, dlmf 9.9.E13, dlmf 9.9.E14, dlmf 9.9.E15, dlmf 9.9.E16, dlmf 9.9.E17]
theorem exists_airy_zero_parametrizations :
    ∃ T U V W : ℂ → ℂ, ∀ k : ℕ,
      (airyAiZero (k + 1) : ℂ) = -T (airyZeroArgument 1 k) ∧
      airyAiDeriv (airyAiZero (k + 1)) = (-1 : ℂ) ^ k * V (airyZeroArgument 1 k) ∧
      (airyAiDerivZero (k + 1) : ℂ) = -U (airyZeroArgument 3 k) ∧
      airyAi (airyAiDerivZero (k + 1)) = (-1 : ℂ) ^ k * W (airyZeroArgument 3 k) ∧
      (airyBiZero (k + 1) : ℂ) = -T (airyZeroArgument 3 k) ∧
      airyBiDeriv (airyBiZero (k + 1)) = (-1 : ℂ) ^ k * V (airyZeroArgument 3 k) ∧
      (airyBiDerivZero (k + 1) : ℂ) = -U (airyZeroArgument 1 k) ∧
      airyBi (airyBiDerivZero (k + 1)) = (-1 : ℂ) ^ (k + 1) * W (airyZeroArgument 1 k) ∧
      airyBiComplexZero (k + 1) = exp (π * I / 3) * T (airyComplexZeroArgument 1 k) ∧
      airyBiDeriv (airyBiComplexZero (k + 1)) =
        (-1 : ℂ) ^ (k + 1) * Real.sqrt 2 * exp (-π * I / 6) * V (airyComplexZeroArgument 1 k) ∧
      airyBiDerivComplexZero (k + 1) = exp (π * I / 3) * U (airyComplexZeroArgument 3 k) ∧
      airyBi (airyBiDerivComplexZero (k + 1)) =
        (-1 : ℂ) ^ k * Real.sqrt 2 * exp (π * I / 6) * W (airyComplexZeroArgument 3 k) := by
  have i1 := airyZeros_inj 1
  have i3 := airyZeros_inj 3
  have c1 := airyZeros_cinj 1
  have c3 := airyZeros_cinj 3
  have hsgn (k : ℕ) : ((-1 : ℂ) ^ k) * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr two_pos).ne'
  obtain ⟨T, hT⟩ := airyZeros_exists_interp3 i1 i3 c1 airyZeros_ne13
    (fun k j => airyZeros_rcne 1 1 k j) (fun k j => airyZeros_rcne 3 1 k j)
    (fun k => -(airyAiZero (k + 1) : ℂ)) (fun k => -(airyBiZero (k + 1) : ℂ))
    (fun k => exp (-(π * I / 3)) * airyBiComplexZero (k + 1))
  obtain ⟨U, hU⟩ := airyZeros_exists_interp3 i3 i1 c3 (fun k j => (airyZeros_ne13 j k).symm)
    (fun k j => airyZeros_rcne 3 3 k j) (fun k j => airyZeros_rcne 1 3 k j)
    (fun k => -(airyAiDerivZero (k + 1) : ℂ)) (fun k => -(airyBiDerivZero (k + 1) : ℂ))
    (fun k => exp (-(π * I / 3)) * airyBiDerivComplexZero (k + 1))
  obtain ⟨V, hV⟩ := airyZeros_exists_interp3 i1 i3 c1 airyZeros_ne13
    (fun k j => airyZeros_rcne 1 1 k j) (fun k j => airyZeros_rcne 3 1 k j)
    (fun k => (-1 : ℂ) ^ k * airyAiDeriv (airyAiZero (k + 1)))
    (fun k => (-1 : ℂ) ^ k * airyBiDeriv (airyBiZero (k + 1)))
    (fun k => airyBiDeriv (airyBiComplexZero (k + 1)) /
      ((-1 : ℂ) ^ (k + 1) * Real.sqrt 2 * exp (-π * I / 6)))
  obtain ⟨W, hW⟩ := airyZeros_exists_interp3 i3 i1 c3 (fun k j => (airyZeros_ne13 j k).symm)
    (fun k j => airyZeros_rcne 3 3 k j) (fun k j => airyZeros_rcne 1 3 k j)
    (fun k => (-1 : ℂ) ^ k * airyAi (airyAiDerivZero (k + 1)))
    (fun k => (-1 : ℂ) ^ (k + 1) * airyBi (airyBiDerivZero (k + 1)))
    (fun k => airyBi (airyBiDerivComplexZero (k + 1)) /
      ((-1 : ℂ) ^ k * Real.sqrt 2 * exp (π * I / 6)))
  refine ⟨T, U, V, W, fun k => ?_⟩
  obtain ⟨T1, T3, TC⟩ := hT k
  obtain ⟨U3, U1, UC⟩ := hU k
  obtain ⟨V1, V3, VC⟩ := hV k
  obtain ⟨W3, W1, WC⟩ := hW k
  rw [T1, T3, TC, U1, U3, UC, V1, V3, VC, W1, W3, WC]
  have he (z : ℂ) : exp z * (exp (-z)) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  have hk1 : ((-1 : ℂ) ^ (k + 1)) * (-1 : ℂ) ^ (k + 1) = 1 := hsgn (k + 1)
  refine ⟨by ring, ?_, by ring, ?_, by ring, ?_, by ring, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← mul_assoc, hsgn, one_mul]
  · rw [← mul_assoc, hsgn, one_mul]
  · rw [← mul_assoc, hsgn, one_mul]
  · rw [← mul_assoc, hk1, one_mul]
  · rw [← mul_assoc, he, one_mul]
  · rw [mul_div_cancel₀]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hs2) (exp_ne_zero _)
  · rw [← mul_assoc, he, one_mul]
  · rw [mul_div_cancel₀]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hs2) (exp_ne_zero _)

end DLMF.Airy
