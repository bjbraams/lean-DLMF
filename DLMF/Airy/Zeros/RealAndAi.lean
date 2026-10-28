/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.ModulusPhase
public import DLMF.ErrorFunctions.ZeroTools

/-!
# Real Airy zeros and the absence of nonreal Ai zeros

Monotone phases enumerate the real zeros; analytic estimates exclude nonreal zeros of Ai and its
derivative.

Source references and common attribution are retained in
`DLMF.Airy.Zeros`.
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

end DLMF.Airy
end
