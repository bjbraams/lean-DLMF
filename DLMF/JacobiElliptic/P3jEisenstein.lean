/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.P3jJacobiODE
public import DLMF.Weierstrass.EllipticFunctionsAndInvariants

/-!
# Eisenstein-type series for `ns` and `ds` (helpers for DLMF §22.12, round 3)

* `p3j_G ε τ t = ∑ₙ εⁿ π/sin(π(t - nτ))` (`ε = ±1`, `Im τ > 0`) converges absolutely, is
  meromorphic with simple poles on the lattice `m + nτ`, odd, and satisfies
  `G(t + 1) = -G(t)`, `G(t + τ) = ε G(t)`.
* `p3j_eq_G`: a Liouville argument (via `DLMF.Weierstrass.p23R1_eq_const_of_elliptic` on the
  lattice `⟨2, 2τ⟩`) identifies any function with the same quasi-periods, oddness, poles and
  residue at `0` with `p3j_G`.
* `p3j_ps_eq_G`, `p3j_hasSum_ns`, `p3j_hasSum_ds`: `2K ns(2Kt) = G₊(t)`, `2K ds(2Kt) = G₋(t)`.
* `p3j_core`: expanding each `π/sin` term geometrically and interchanging the double series
  gives the Fourier coefficients (used for DLMF 22.11).
* `p3j_tendsto_alt`: `∑_{|m| ≤ M} (-1)^m/(w - m) → π/sin(πw)` (from Mathlib's cotangent
  Mittag-Leffler expansion and `cot(x/2) - cot x = 1/sin x`).
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.JacobiElliptic

/-- Lower bound `‖sin w‖ ≥ (e^{|Im w|} - e^{-|Im w|})/2`. -/
lemma p3j_norm_sin_ge (w : ℂ) :
    (Real.exp |w.im| - Real.exp (-|w.im|)) / 2 ≤ ‖sin w‖ := by
  have hs : sin w = (cexp (-w * I) - cexp (w * I)) * I / 2 := by rw [Complex.sin]
  have h1 : ‖cexp (-w * I)‖ = Real.exp w.im := by rw [Complex.norm_exp]; simp
  have h2 : ‖cexp (w * I)‖ = Real.exp (-w.im) := by rw [Complex.norm_exp]; simp
  have key : |Real.exp w.im - Real.exp (-w.im)| ≤ ‖cexp (-w * I) - cexp (w * I)‖ := by
    rw [← h1, ← h2]; exact abs_norm_sub_norm_le _ _
  have hn : ‖sin w‖ = ‖cexp (-w * I) - cexp (w * I)‖ / 2 := by
    rw [hs, norm_div, norm_mul, Complex.norm_I, mul_one]; simp
  rw [hn]
  have : Real.exp |w.im| - Real.exp (-|w.im|) ≤ |Real.exp w.im - Real.exp (-w.im)| := by
    rcases abs_cases w.im with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; exact le_abs_self _
    · rw [h, neg_neg, abs_sub_comm]; exact le_abs_self _
  linarith

/-- If `|Im w| ≥ a > 0`, then `‖1/sin w‖ ≤ (2/(1 - e^{-2a})) e^{-|Im w|}`. -/
lemma p3j_norm_inv_sin_le {w : ℂ} {a : ℝ} (ha : 0 < a) (hw : a ≤ |w.im|) :
    ‖1 / sin w‖ ≤ 2 / (1 - Real.exp (-(2 * a))) * Real.exp (-|w.im|) := by
  have hea : Real.exp (-(2 * a)) < 1 := by
    have := Real.exp_lt_exp.mpr (show -(2 * a) < 0 by linarith); simpa using this
  have hd : 0 < 1 - Real.exp (-(2 * a)) := by linarith
  have hy := Real.exp_pos |w.im|
  have h2 : Real.exp (-(2 * |w.im|)) ≤ Real.exp (-(2 * a)) := Real.exp_le_exp.mpr (by linarith)
  have hlow : Real.exp |w.im| * (1 - Real.exp (-(2 * a))) / 2 ≤ ‖sin w‖ := by
    refine le_trans ?_ (p3j_norm_sin_ge w)
    have : Real.exp (-|w.im|) = Real.exp |w.im| * Real.exp (-(2 * |w.im|)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    nlinarith
  have hpos : 0 < Real.exp |w.im| * (1 - Real.exp (-(2 * a))) / 2 := by positivity
  rw [norm_div, norm_one]
  rw [div_le_iff₀ (lt_of_lt_of_le hpos hlow)]
  calc (1 : ℝ) = 2 / (1 - Real.exp (-(2 * a))) * Real.exp (-|w.im|) *
        (Real.exp |w.im| * (1 - Real.exp (-(2 * a))) / 2) := by
          have e : Real.exp (-|w.im|) * Real.exp |w.im| = 1 := by
            rw [← Real.exp_add]; simp
          field_simp
          linear_combination (-1 : ℝ) * e
    _ ≤ _ := by gcongr

/-- Iterating a quasi-periodicity `g(t + a) = s g(t)` over the integers. -/
lemma p3j_iter {g : ℂ → ℂ} {a s : ℂ} (hs : s ≠ 0) (h : ∀ t, g (t + a) = s * g t) (m : ℤ)
    (t : ℂ) : g (t + m * a) = s ^ m * g t := by
  induction m using Int.induction_on generalizing t with
  | zero => simp
  | succ n ih =>
    rw [show t + (((n : ℤ) + 1 : ℤ) : ℂ) * a = (t + ((n : ℤ) : ℂ) * a) + a by push_cast; ring, h,
      ih, zpow_add_one₀ hs]; ring
  | pred n ih =>
    have := h (t + ((-(n : ℤ) - 1 : ℤ) : ℂ) * a)
    rw [show t + ((-(n : ℤ) - 1 : ℤ) : ℂ) * a + a = t + ((-(n : ℤ) : ℤ) : ℂ) * a by push_cast; ring,
      ih] at this
    rw [zpow_sub_one₀ hs]
    field_simp
    linear_combination this.symm

/-- The terms `εⁿ π / sin(π(t - nτ))` of the Eisenstein-type series of DLMF §22.12. -/
def p3j_term (ε τ : ℂ) (n : ℤ) (t : ℂ) : ℂ := ε ^ n * π / sin (π * (t - n * τ))

/-- The Eisenstein-type series `∑ₙ εⁿ π / sin(π(t - nτ))`. -/
def p3j_G (ε τ t : ℂ) : ℂ := ∑' n : ℤ, p3j_term ε τ n t

/-- The points `m + nτ` (poles of the series). -/
def p3j_latt (τ : ℂ) : Set ℂ := {t | ∃ m n : ℤ, t = m + n * τ}

/-- `ε = ±1` is nonzero. -/
lemma p3j_eps_ne {ε : ℂ} (hε : ε = 1 ∨ ε = -1) : ε ≠ 0 := by
  rcases hε with rfl | rfl <;> norm_num

/-- `ε⁻ⁿ = εⁿ` for `ε = ±1`. -/
lemma p3j_eps_zpow_neg {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (n : ℤ) : ε ^ (-n) = ε ^ n := by
  rcases hε with rfl | rfl
  · simp
  · rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]

/-- `‖εⁿ‖ = 1` for `ε = ±1`. -/
lemma p3j_norm_eps_zpow {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (n : ℤ) : ‖ε ^ n‖ = 1 := by
  rcases hε with rfl | rfl <;> simp [norm_zpow]

/-- Shifting `t` by `jτ` reindexes the terms. -/
lemma p3j_term_add_tau (ε τ : ℂ) (hε : ε ≠ 0) (n j : ℤ) (t : ℂ) :
    p3j_term ε τ n (t + j * τ) = ε ^ j * p3j_term ε τ (n - j) t := by
  simp only [p3j_term]
  rw [show t + j * τ - n * τ = t - ((n - j : ℤ) : ℂ) * τ by push_cast; ring,
    show ε ^ n = ε ^ j * ε ^ (n - j) by rw [← zpow_add₀ hε]; ring_nf]
  ring

/-- The terms change sign under `t ↦ t + 1`. -/
lemma p3j_term_add_one (ε τ : ℂ) (n : ℤ) (t : ℂ) :
    p3j_term ε τ n (t + 1) = -p3j_term ε τ n t := by
  simp only [p3j_term]
  rw [show π * (t + 1 - n * τ) = π * (t - n * τ) + π by ring, Complex.sin_add_pi]
  rw [div_neg]

/-- The terms are odd up to `n ↦ -n`. -/
lemma p3j_term_neg {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (τ : ℂ) (n : ℤ) (t : ℂ) :
    p3j_term ε τ n (-t) = -p3j_term ε τ (-n) t := by
  simp only [p3j_term, p3j_eps_zpow_neg hε]
  rw [show π * (-t - n * τ) = -(π * (t - ((-n : ℤ) : ℂ) * τ)) by push_cast; ring,
    Complex.sin_neg, div_neg]

/-- Exponential bound on the terms with `n ≠ 0` in the strip `|Im t| ≤ 3 Im τ/4`. -/
lemma p3j_term_bound {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1) (hτ : 0 < τ.im) {n : ℤ} (hn : n ≠ 0)
    {t : ℂ} (ht : |t.im| ≤ 3 / 4 * τ.im) :
    ‖p3j_term ε τ n t‖ ≤ π * (2 / (1 - Real.exp (-(2 * (π * τ.im / 4))))) *
      Real.exp (-(π * τ.im / 4)) ^ n.natAbs := by
  set w := π * (t - n * τ) with hw
  have hwim : w.im = π * (t.im - n * τ.im) := by simp [hw]
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    exact_mod_cast this
  have hb : π * τ.im / 4 * n.natAbs ≤ |w.im| := by
    rw [hwim, abs_mul, abs_of_pos Real.pi_pos]
    have h1 : |(n : ℝ)| * τ.im - |t.im| ≤ |t.im - n * τ.im| := by
      have := abs_sub_abs_le_abs_sub (n * τ.im) t.im
      rw [abs_mul, abs_of_pos hτ, abs_sub_comm] at this
      linarith
    have h2 : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2]
    have h3 : |(n : ℝ)| * τ.im / 4 ≤ |t.im - n * τ.im| := by nlinarith
    nlinarith [Real.pi_pos]
  have ha : 0 < π * τ.im / 4 := by positivity
  have hw1 : π * τ.im / 4 ≤ |w.im| := by
    refine le_trans ?_ hb
    have : (1 : ℝ) ≤ n.natAbs := by
      have := Int.natAbs_pos.mpr hn; exact_mod_cast this
    nlinarith
  have hs := p3j_norm_inv_sin_le ha hw1
  have he : Real.exp (-|w.im|) ≤ Real.exp (-(π * τ.im / 4)) ^ n.natAbs := by
    rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr; nlinarith
  have hC : 0 ≤ 2 / (1 - Real.exp (-(2 * (π * τ.im / 4)))) := by
    have : Real.exp (-(2 * (π * τ.im / 4))) < 1 := by
      have := Real.exp_lt_exp.mpr (show -(2 * (π * τ.im / 4)) < 0 by linarith); simpa using this
    have : 0 < 1 - Real.exp (-(2 * (π * τ.im / 4))) := by linarith
    positivity
  simp only [p3j_term]
  rw [← hw, mul_div_assoc, norm_mul, p3j_norm_eps_zpow hε, one_mul, div_eq_mul_one_div,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_assoc]
  gcongr
  exact hs.trans (mul_le_mul_of_nonneg_left he hC)

/-- `∑_{n ∈ ℤ} r^{|n|}` converges for `0 ≤ r < 1`. -/
lemma p3j_summable_geom {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun n : ℤ => r ^ n.natAbs := by
  apply Summable.of_nat_of_neg
  · simpa using summable_geometric_of_lt_one hr0 hr
  · simpa using summable_geometric_of_lt_one hr0 hr

/-- The series without its `n = 0` term. -/
def p3j_R (ε τ t : ℂ) : ℂ := ∑' n : ℤ, if n = 0 then 0 else p3j_term ε τ n t

/-- The geometric ratio `exp(-π Im τ/4)` lies in `[0, 1)`. -/
lemma p3j_C_r {τ : ℂ} (hτ : 0 < τ.im) :
    0 ≤ Real.exp (-(π * τ.im / 4)) ∧ Real.exp (-(π * τ.im / 4)) < 1 := by
  refine ⟨(Real.exp_pos _).le, ?_⟩
  have := Real.exp_lt_exp.mpr (show -(π * τ.im / 4) < 0 by
    have := Real.pi_pos; nlinarith)
  simpa using this

/-- Geometric bound for the terms with `n ≠ 0` on the strip. -/
lemma p3j_R_bound {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1) (hτ : 0 < τ.im) (n : ℤ) {t : ℂ}
    (ht : |t.im| ≤ 3 / 4 * τ.im) :
    ‖(if n = 0 then 0 else p3j_term ε τ n t)‖ ≤ π * (2 / (1 - Real.exp (-(2 * (π * τ.im / 4))))) *
      Real.exp (-(π * τ.im / 4)) ^ n.natAbs := by
  split_ifs with hn
  · rw [norm_zero]
    have : Real.exp (-(2 * (π * τ.im / 4))) < 1 := by
      have := Real.exp_lt_exp.mpr (show -(2 * (π * τ.im / 4)) < 0 by
        have := Real.pi_pos; nlinarith); simpa using this
    have : 0 < 1 - Real.exp (-(2 * (π * τ.im / 4))) := by linarith
    have := (p3j_C_r hτ).1
    positivity
  · exact p3j_term_bound hε hτ hn ht

/-- The terms with `n ≠ 0` are summable on the strip. -/
lemma p3j_summable_R {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1) (hτ : 0 < τ.im) {t : ℂ}
    (ht : |t.im| ≤ 3 / 4 * τ.im) :
    Summable fun n : ℤ => if n = 0 then 0 else p3j_term ε τ n t :=
  Summable.of_norm_bounded (((p3j_summable_geom (p3j_C_r hτ).1 (p3j_C_r hτ).2).mul_left _))
    fun n => p3j_R_bound hε hτ n ht

/-- On the strip the series is `π/sin(πt)` plus the regular part `p3j_R`. -/
lemma p3j_hasSum_strip {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1) (hτ : 0 < τ.im) {t : ℂ}
    (ht : |t.im| ≤ 3 / 4 * τ.im) :
    HasSum (fun n => p3j_term ε τ n t) (π / sin (π * t) + p3j_R ε τ t) := by
  have h1 := (p3j_summable_R hε hτ ht).hasSum
  have h2 := hasSum_ite_eq (0 : ℤ) (p3j_term ε τ 0 t)
  have := h2.add h1
  convert this using 1
  · funext n; split_ifs with hn <;> simp [hn]
  · simp [p3j_term, p3j_R]

/-- Every point can be translated by a multiple of `τ` into the strip `|Im t| ≤ Im τ/2`. -/
lemma p3j_exists_strip {τ : ℂ} (hτ : 0 < τ.im) (t : ℂ) :
    ∃ j : ℤ, |(t - j * τ).im| ≤ 1 / 2 * τ.im := by
  refine ⟨round (t.im / τ.im), ?_⟩
  have h := abs_sub_round (t.im / τ.im)
  have : (t - (round (t.im / τ.im) : ℂ) * τ).im = τ.im * (t.im / τ.im - round (t.im / τ.im)) := by
    simp; field_simp
  rw [this, abs_mul, abs_of_pos hτ]
  nlinarith

/-- The series converges for every `t`. -/
lemma p3j_summable_all {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1) (hτ : 0 < τ.im) (t : ℂ) :
    Summable fun n => p3j_term ε τ n t := by
  obtain ⟨j, hj⟩ := p3j_exists_strip hτ t
  have hs := (p3j_hasSum_strip hε hτ (t := t - j * τ) (by linarith)).summable
  have e : ∀ n, p3j_term ε τ n t = ε ^ j * p3j_term ε τ (n - j) (t - j * τ) := by
    intro n
    rw [← p3j_term_add_tau ε τ (p3j_eps_ne hε), sub_add_cancel]
  simp_rw [e]
  refine Summable.mul_left _ ?_
  exact (Equiv.subRight j).summable_iff.mpr hs

/-- `G(t + jτ) = εʲ G(t)`. -/
lemma p3j_G_add_tau {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1) (j : ℤ) (t : ℂ) :
    p3j_G ε τ (t + j * τ) = ε ^ j * p3j_G ε τ t := by
  simp only [p3j_G, p3j_term_add_tau ε τ (p3j_eps_ne hε), tsum_mul_left]
  congr 1
  exact (Equiv.subRight j).tsum_eq fun n => p3j_term ε τ n t

/-- `G(t + 1) = -G(t)`. -/
lemma p3j_G_add_one (ε τ t : ℂ) : p3j_G ε τ (t + 1) = -p3j_G ε τ t := by
  simp only [p3j_G, p3j_term_add_one, tsum_neg]

/-- `G` is odd. -/
lemma p3j_G_neg {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (τ t : ℂ) : p3j_G ε τ (-t) = -p3j_G ε τ t := by
  simp only [p3j_G, p3j_term_neg hε, tsum_neg]
  congr 1
  exact (Equiv.neg ℤ).tsum_eq fun n => p3j_term ε τ n t

/-- The open strip `|Im t| < 3 Im τ/4`. -/
def p3j_strip (τ : ℂ) : Set ℂ := {t | |t.im| < 3 / 4 * τ.im}

/-- The strip is open. -/
lemma p3j_isOpen_strip (τ : ℂ) : IsOpen (p3j_strip τ) :=
  isOpen_lt (continuous_abs.comp continuous_im) continuous_const

/-- No term with `n ≠ 0` has a pole on the strip. -/
lemma p3j_sin_ne_strip {τ : ℂ} (hτ : 0 < τ.im) {n : ℤ} (hn : n ≠ 0) {t : ℂ}
    (ht : |t.im| ≤ 3 / 4 * τ.im) : sin (π * (t - n * τ)) ≠ 0 := by
  intro h0
  have := p3j_term_bound (ε := 1) (Or.inl rfl) hτ hn ht
  set w := π * (t - n * τ)
  have hwim : w.im = π * (t.im - n * τ.im) := by simp [w]
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    exact_mod_cast this
  have hpos : 0 < |w.im| := by
    rw [hwim, abs_mul, abs_of_pos Real.pi_pos]
    have := abs_sub_abs_le_abs_sub (n * τ.im) t.im
    rw [abs_mul, abs_of_pos hτ, abs_sub_comm] at this
    have : 0 < |t.im - n * τ.im| := by nlinarith
    positivity
  have hlow := p3j_norm_sin_ge w
  rw [h0, norm_zero] at hlow
  have : Real.exp (-|w.im|) < Real.exp |w.im| := Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- The regular part is holomorphic on the strip. -/
lemma p3j_R_differentiableOn {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1) (hτ : 0 < τ.im) :
    DifferentiableOn ℂ (p3j_R ε τ) (p3j_strip τ) := by
  refine differentiableOn_tsum_of_summable_norm
    ((p3j_summable_geom (p3j_C_r hτ).1 (p3j_C_r hτ).2).mul_left _) (fun n => ?_)
    (p3j_isOpen_strip τ) (fun n w hw => p3j_R_bound hε hτ n (le_of_lt hw))
  by_cases hn : n = 0
  · simp only [hn, ite_true]; exact differentiableOn_const _
  · simp only [hn, ite_false, p3j_term]
    refine DifferentiableOn.div (differentiableOn_const _) (by fun_prop) fun w hw => ?_
    exact p3j_sin_ne_strip hτ hn (le_of_lt hw)

/-- Local form of the series near a point, after translating into the strip. -/
lemma p3j_G_eventuallyEq {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1) (hτ : 0 < τ.im) (t₀ : ℂ) :
    ∃ j : ℤ, |(t₀ - j * τ).im| ≤ 1 / 2 * τ.im ∧ p3j_G ε τ =ᶠ[𝓝 t₀]
      fun s => ε ^ j * (π / sin (π * (s - j * τ)) + p3j_R ε τ (s - j * τ)) := by
  obtain ⟨j, hj⟩ := p3j_exists_strip hτ t₀
  refine ⟨j, hj, ?_⟩
  have hU : (fun s => s - j * τ) ⁻¹' p3j_strip τ ∈ 𝓝 t₀ := by
    refine (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      ((p3j_isOpen_strip τ).mem_nhds ?_)
    show |(t₀ - j * τ).im| < 3 / 4 * τ.im
    linarith
  filter_upwards [hU] with s hs
  have e := p3j_G_add_tau (τ := τ) hε j (s - j * τ)
  rw [sub_add_cancel] at e
  rw [e, p3j_G, (p3j_hasSum_strip hε hτ (t := s - j * τ) (le_of_lt hs)).tsum_eq]

/-- `G` is meromorphic. -/
lemma p3j_G_meromorphicAt {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1) (hτ : 0 < τ.im) (t₀ : ℂ) :
    MeromorphicAt (p3j_G ε τ) t₀ := by
  obtain ⟨j, hj, he⟩ := p3j_G_eventuallyEq hε hτ t₀
  have hR : AnalyticAt ℂ (fun s => p3j_R ε τ (s - j * τ)) t₀ := by
    have hin : t₀ - j * τ ∈ p3j_strip τ := by
      show |(t₀ - j * τ).im| < 3 / 4 * τ.im; linarith
    have := ((p3j_R_differentiableOn hε hτ).analyticAt
      ((p3j_isOpen_strip τ).mem_nhds hin))
    exact this.comp_of_eq (by fun_prop) rfl
  have hm : MeromorphicAt (fun s => ε ^ j * (π / sin (π * (s - j * τ)) +
      p3j_R ε τ (s - j * τ))) t₀ := by
    refine MeromorphicAt.mul (MeromorphicAt.const _ _) (MeromorphicAt.add ?_ hR.meromorphicAt)
    exact (MeromorphicAt.const _ _).div (by fun_prop : AnalyticAt ℂ (fun s =>
      sin (π * (s - j * τ))) t₀).meromorphicAt
  exact hm.congr (he.symm.filter_mono nhdsWithin_le_nhds)

/-- `G` is analytic off the lattice. -/
lemma p3j_G_analyticAt {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1) (hτ : 0 < τ.im) {t₀ : ℂ}
    (ht : t₀ ∉ p3j_latt τ) : AnalyticAt ℂ (p3j_G ε τ) t₀ := by
  obtain ⟨j, hj, he⟩ := p3j_G_eventuallyEq hε hτ t₀
  have hR : AnalyticAt ℂ (fun s => p3j_R ε τ (s - j * τ)) t₀ := by
    have hin : t₀ - j * τ ∈ p3j_strip τ := by
      show |(t₀ - j * τ).im| < 3 / 4 * τ.im; linarith
    have := ((p3j_R_differentiableOn hε hτ).analyticAt
      ((p3j_isOpen_strip τ).mem_nhds hin))
    exact this.comp_of_eq (by fun_prop) rfl
  have hsin : sin (π * (t₀ - j * τ)) ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp h0
    apply ht
    refine ⟨m, j, ?_⟩
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : t₀ - j * τ = m := by
      apply mul_left_cancel₀ hpi; rw [hm]; ring
    linear_combination this
  have hm : AnalyticAt ℂ (fun s => ε ^ j * (π / sin (π * (s - j * τ)) +
      p3j_R ε τ (s - j * τ))) t₀ := by
    refine analyticAt_const.mul (AnalyticAt.add ?_ hR)
    exact analyticAt_const.div (by fun_prop) hsin
  exact hm.congr he.symm

/-- `S = t · dslope S 0 t` near `0` when `S 0 = 0`. -/
lemma p3j_eq_mul_dslope {S : ℂ → ℂ} (hS : S 0 = 0) (t : ℂ) : S t = t * dslope S 0 t := by
  by_cases ht : t = 0
  · rw [ht, hS, zero_mul]
  · rw [dslope_of_ne _ ht, slope_def_field, hS, sub_zero, sub_zero]; field_simp

/-- The slope function of an analytic function at `0` is analytic. -/
lemma p3j_dslope_analyticAt {S : ℂ → ℂ} (hS : AnalyticAt ℂ S 0) : AnalyticAt ℂ (dslope S 0) 0 := by
  obtain ⟨U, hU, hUo, h0U⟩ := mem_nhds_iff.mp hS.eventually_analyticAt
  have hd : DifferentiableOn ℂ S U := fun z hz => (hU hz).differentiableAt.differentiableWithinAt
  have := (Complex.differentiableOn_dslope (hUo.mem_nhds h0U)).mpr hd
  exact this.analyticAt (hUo.mem_nhds h0U)

/-- Two quotients with simple poles at `0` and equal residues differ by a function with a
removable singularity. -/
lemma p3j_removable {a b c₁ c₂ : ℂ} {N₁ S₁ N₂ S₂ : ℂ → ℂ} (hN₁ : AnalyticAt ℂ N₁ 0)
    (hN₂ : AnalyticAt ℂ N₂ 0) (hS₁ : AnalyticAt ℂ S₁ 0) (hS₂ : AnalyticAt ℂ S₂ 0)
    (h0₁ : S₁ 0 = 0) (h0₂ : S₂ 0 = 0) (hn₁ : N₁ 0 = 1) (hn₂ : N₂ 0 = 1)
    (hd₁ : HasDerivAt S₁ c₁ 0) (hd₂ : HasDerivAt S₂ c₂ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hab : a * c₂ = b * c₁) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧
      (fun t => a * N₁ t / S₁ t - b * N₂ t / S₂ t) =ᶠ[𝓝[≠] 0] A := by
  set g₁ := dslope S₁ 0
  set g₂ := dslope S₂ 0
  have hg₁ := p3j_dslope_analyticAt hS₁
  have hg₂ := p3j_dslope_analyticAt hS₂
  have hg₁0 : g₁ 0 = c₁ := by simp [g₁, dslope_same, hd₁.deriv]
  have hg₂0 : g₂ 0 = c₂ := by simp [g₂, dslope_same, hd₂.deriv]
  set φ := fun t => a * N₁ t * g₂ t - b * N₂ t * g₁ t
  have hφ : AnalyticAt ℂ φ 0 := ((analyticAt_const.mul hN₁).mul hg₂).sub
    ((analyticAt_const.mul hN₂).mul hg₁)
  have hφ0 : φ 0 = 0 := by simp only [φ, hn₁, hn₂, hg₁0, hg₂0]; linear_combination hab
  refine ⟨fun t => dslope φ 0 t / (g₁ t * g₂ t), (p3j_dslope_analyticAt hφ).div
    (hg₁.mul hg₂) (by rw [hg₁0, hg₂0]; exact mul_ne_zero hc₁ hc₂), ?_⟩
  have e1 : ∀ᶠ t in 𝓝 0, g₁ t ≠ 0 :=
    hg₁.continuousAt.eventually_ne (by change g₁ 0 ≠ 0; rw [hg₁0]; exact hc₁)
  have e2 : ∀ᶠ t in 𝓝 0, g₂ t ≠ 0 :=
    hg₂.continuousAt.eventually_ne (by change g₂ 0 ≠ 0; rw [hg₂0]; exact hc₂)
  filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, self_mem_nhdsWithin]
    with t ht1 ht2 ht0
  have ht0' : t ≠ 0 := ht0
  rw [p3j_eq_mul_dslope h0₁ t, p3j_eq_mul_dslope h0₂ t]
  have := p3j_eq_mul_dslope hφ0 t
  have hφt : φ t = a * N₁ t * g₂ t - b * N₂ t * g₁ t := rfl
  change a * N₁ t / (t * g₁ t) - b * N₂ t / (t * g₂ t) = dslope φ 0 t / (g₁ t * g₂ t)
  rw [div_sub_div _ _ (mul_ne_zero ht0' ht1) (mul_ne_zero ht0' ht2),
    div_eq_div_iff (mul_ne_zero (mul_ne_zero ht0' ht1) (mul_ne_zero ht0' ht2))
      (mul_ne_zero ht1 ht2)]
  linear_combination (t * g₁ t * g₂ t) * (hφt.symm.trans this)

/-- Liouville core for the Eisenstein-type series: a function with the same quasi-periods,
oddness, poles and residue at `0` as `∑ₙ εⁿ π/sin(π(t - nτ))` equals it off the lattice. -/
lemma p3j_eq_G {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1) (hτ : 0 < τ.im) {f : ℂ → ℂ}
    (hf : p3j_Dich f) (hf1 : ∀ t, f (t + 1) = -f t) (hfτ : ∀ t, f (t + τ) = ε * f t)
    (hfodd : ∀ t, f (-t) = -f t) (hfan : ∀ t ∉ p3j_latt τ, AnalyticAt ℂ f t)
    (hf0 : ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧
      (fun t => f t - π / sin (π * t)) =ᶠ[𝓝[≠] 0] A) :
    ∀ t ∉ p3j_latt τ, f t = p3j_G ε τ t := by
  set H := fun t => f t - p3j_G ε τ t with hH
  have hε0 := p3j_eps_ne hε
  have hHm : Meromorphic H := fun t =>
    (hf.meromorphicAt t).sub (p3j_G_meromorphicAt hε hτ t)
  have hH1 : ∀ t, H (t + 1) = -1 * H t := by
    intro t; simp only [hH, hf1, p3j_G_add_one]; ring
  have hHτ : ∀ t, H (t + τ) = ε * H t := by
    intro t
    have := p3j_G_add_tau (τ := τ) hε 1 t
    simp only [Int.cast_one, one_mul, zpow_one] at this
    simp only [hH, hfτ, this]; ring
  have hHmn : ∀ (m n : ℤ) t, H (t + (m + n * τ)) = (-1) ^ m * ε ^ n * H t := by
    intro m n t
    rw [← add_assoc, p3j_iter hε0 hHτ n, show (t + (m : ℂ)) = t + m * 1 by ring,
      p3j_iter (by norm_num) hH1 m]
    ring
  -- the lattice `⟨2, 2τ⟩`
  have hind : LinearIndependent ℝ ![(2 : ℂ), 2 * τ] := by
    refine LinearIndependent.pair_iff.mpr fun s u h => ?_
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp at him hre
    have hu : u = 0 := by
      rcases him with h | h
      · exact h
      · exact absurd h hτ.ne'
    subst hu
    simp at hre
    exact ⟨hre, rfl⟩
  let L : PeriodPair := ⟨2, 2 * τ, hind⟩
  have hper : ∀ z, ∀ l ∈ L.lattice, H (z + l) = H z := by
    intro z l hl
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hl
    have := hHmn (2 * m) (2 * n) z
    simp only [L] at this ⊢
    rw [show (m : ℂ) * 2 + n * (2 * τ) = ((2 * m : ℤ) : ℂ) + ((2 * n : ℤ) : ℂ) * τ by
      push_cast; ring, this]
    rw [zpow_mul, zpow_mul]
    rcases hε with rfl | rfl <;> norm_num
  -- orders
  have hord0 : 0 ≤ meromorphicOrderAt H 0 := by
    obtain ⟨A, hA, hfA⟩ := hf0
    obtain ⟨j, hj, he⟩ := p3j_G_eventuallyEq hε hτ 0
    have hR : AnalyticAt ℂ (p3j_R ε τ) 0 :=
      (p3j_R_differentiableOn hε hτ).analyticAt ((p3j_isOpen_strip τ).mem_nhds (by
        show |(0 : ℂ).im| < 3 / 4 * τ.im; simp; linarith))
    have hG0 : p3j_G ε τ =ᶠ[𝓝 0] fun s => π / sin (π * s) + p3j_R ε τ s := by
      have hU : p3j_strip τ ∈ 𝓝 (0 : ℂ) := (p3j_isOpen_strip τ).mem_nhds (by
        show |(0 : ℂ).im| < 3 / 4 * τ.im; simp; linarith)
      filter_upwards [hU] with s hs
      exact (p3j_hasSum_strip hε hτ (le_of_lt hs)).tsum_eq
    have hev : H =ᶠ[𝓝[≠] 0] fun s => A s - p3j_R ε τ s := by
      filter_upwards [hfA, nhdsWithin_le_nhds hG0] with s h1 h2
      simp only [hH, h2]
      rw [← h1]; ring
    rw [meromorphicOrderAt_congr hev]
    exact (hA.sub hR).meromorphicOrderAt_nonneg
  have hord : ∀ x, 0 ≤ meromorphicOrderAt H x := by
    intro x
    by_cases hx : x ∈ p3j_latt τ
    · obtain ⟨m, n, rfl⟩ := hx
      have e : H ∘ (· + ((m : ℂ) + n * τ)) = ((-1 : ℂ) ^ m * ε ^ n) • H := by
        funext t; simp [hHmn]
      have h1 := meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (x := (0 : ℂ))
        (c := (m : ℂ) + n * τ) (f := H)
      rw [zero_add, e, meromorphicOrderAt_const_smul_eq_meromorphicOrderAt
        (mul_ne_zero (zpow_ne_zero _ (by norm_num)) (zpow_ne_zero _ hε0))] at h1
      rw [← h1]; exact hord0
    · exact ((hfan x hx).sub (p3j_G_analyticAt hε hτ hx)).meromorphicOrderAt_nonneg
  obtain ⟨c, hc⟩ := DLMF.Weierstrass.p23R1_eq_const_of_elliptic L hHm hper hord
  have hhalf : ∀ s : ℂ, s = 1 / 2 ∨ s = -(1 / 2) → s ∉ p3j_latt τ := by
    rintro s hs ⟨m, n, hmn⟩
    have him := congrArg Complex.im hmn
    have hre := congrArg Complex.re hmn
    rcases hs with rfl | rfl <;> simp at him hre
    all_goals
      rcases him with h | h
      · subst h; simp at hre
        have h2 : (2 * m : ℝ) = 1 ∨ (2 * m : ℝ) = -1 := by
          first | (left; linarith) | (right; linarith)
        rcases h2 with h2 | h2
        · have : (2 * m : ℤ) = 1 := by exact_mod_cast h2
          omega
        · have : (2 * m : ℤ) = -1 := by exact_mod_cast h2
          omega
      · exact absurd h hτ.ne'
  have hp := hhalf (1 / 2) (Or.inl rfl)
  have hn := hhalf (-(1 / 2)) (Or.inr rfl)
  have hHodd : H (-(1 / 2)) = -H (1 / 2) := by
    simp only [hH, hfodd, p3j_G_neg hε]; ring
  have hc0 : c = 0 := by
    have e1 := hc _ ((hfan _ hp).sub (p3j_G_analyticAt hε hτ hp))
    have e2 := hc _ ((hfan _ hn).sub (p3j_G_analyticAt hε hτ hn))
    rw [hHodd, e1] at e2
    linear_combination -e2 / 2
  intro t ht
  have := hc t ((hfan t ht).sub (p3j_G_analyticAt hε hτ ht))
  rw [hc0] at this
  exact sub_eq_zero.mp this

/-- Membership in the integer complement from a non-integrality hypothesis. -/
lemma p3j_mem_intCompl {w : ℂ} (hw : ∀ m : ℤ, w - m ≠ 0) : w ∈ integerComplement := by
  rintro ⟨m, rfl⟩; exact hw m (sub_self _)

/-- Mittag-Leffler for the cotangent as a `HasSum` over `ℕ`. -/
lemma p3j_hasSum_cotTerm {x : ℂ} (hx : x ∈ integerComplement) :
    HasSum (fun n : ℕ => cotTerm x n) (π * cot (π * x) - 1 / x) := by
  rw [cot_series_rep' hx]; exact (summable_cotTerm hx).hasSum

/-- `cot (x/2) - cot x = 1/sin x`. -/
lemma p3j_cot_half_sub {x : ℂ} (hx : sin x ≠ 0) : cot (x / 2) - cot x = 1 / sin x := by
  have h2 : x = 2 * (x / 2) := by ring
  have hs : sin (x / 2) ≠ 0 := by
    intro h; apply hx; rw [h2, sin_two_mul, h]; ring
  have hc : cos (x / 2) ≠ 0 := by
    intro h; apply hx; rw [h2, sin_two_mul, h]; ring
  rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin]
  conv_lhs => rw [h2, sin_two_mul, cos_two_mul]
  conv_rhs => rw [h2, sin_two_mul]
  rw [show x / 2 = x / 2 from rfl]
  field_simp
  ring

/-- The symmetric partial sums of `∑ (-1)^m/(w - m)`. -/
lemma p3j_sum_Icc_alt (w : ℂ) (M : ℕ) :
    ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1 : ℂ) ^ m / (w - m) =
      1 / w + ∑ n ∈ Finset.range M, (-1 : ℂ) ^ (n + 1) * cotTerm w n := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hI : Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ) =
        insert (-((M : ℤ) + 1)) (insert ((M : ℤ) + 1) (Finset.Icc (-(M : ℤ)) M)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [hI, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), ih,
      Finset.sum_range_succ]
    have e1 : (-1 : ℂ) ^ (-((M : ℤ) + 1)) = (-1) ^ (M + 1) := by
      rw [zpow_neg, show ((M : ℤ) + 1) = ((M + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
      rw [show ((-1 : ℂ) ^ (M + 1))⁻¹ = (-1) ^ (M + 1) by
        rcases neg_one_pow_eq_or ℂ (M + 1) with h | h <;> rw [h] <;> norm_num]
    have e2 : (-1 : ℂ) ^ ((M : ℤ) + 1) = (-1) ^ (M + 1) := by
      rw [show ((M : ℤ) + 1) = ((M + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    rw [e1, e2, cotTerm]
    push_cast
    ring

/-- The alternating Mittag-Leffler expansion `π/sin(πw) = lim ∑_{|m| ≤ M} (-1)^m/(w - m)`. -/
theorem p3j_tendsto_alt {w : ℂ} (hw : ∀ m : ℤ, w - m ≠ 0) :
    Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1 : ℂ) ^ m / (w - m)) atTop
      (𝓝 (π / sin (π * w))) := by
  have hx := p3j_mem_intCompl hw
  have hx2 : w / 2 ∈ integerComplement := by
    rintro ⟨m, hm⟩; apply hw (2 * m); push_cast; rw [hm]; ring
  have hw0 : w ≠ 0 := by simpa using hw 0
  set f : ℕ → ℂ := fun n => if n % 2 = 1 then cotTerm w n else 0
  have hodd : HasSum f ((π * cot (π * (w / 2)) - 1 / (w / 2)) / 2) := by
    have he : HasSum (fun j => f (2 * j)) 0 := by
      convert hasSum_zero with j; simp [f]
    have ho : HasSum (fun j => f (2 * j + 1)) ((π * cot (π * (w / 2)) - 1 / (w / 2)) / 2) := by
      convert (p3j_hasSum_cotTerm hx2).div_const 2 using 1
      funext j
      simp only [f, cotTerm, Nat.mul_add_mod_self_left, ite_true, show (1 : ℕ) % 2 = 1 from rfl]
      push_cast
      rw [show w - (2 * (j : ℂ) + 1 + 1) = 2 * (w / 2 - (j + 1)) by ring,
        show w + (2 * (j : ℂ) + 1 + 1) = 2 * (w / 2 + (j + 1)) by ring]
      simp only [one_div, mul_inv]
      ring
    simpa using he.even_add_odd ho
  have hc : HasSum (fun n : ℕ => (-1 : ℂ) ^ (n + 1) * cotTerm w n)
      (-(π * cot (π * w) - 1 / w) + 2 * ((π * cot (π * (w / 2)) - 1 / (w / 2)) / 2)) := by
    convert (p3j_hasSum_cotTerm hx).neg.add (hodd.mul_left 2) using 1
    funext n
    simp only [f]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [if_neg (by omega), pow_succ, (Nat.even_iff.mpr h).neg_one_pow]; ring
    · rw [if_pos h, pow_succ, (Nat.odd_iff.mpr h).neg_one_pow]; ring
  have hlim := (hc.tendsto_sum_nat).const_add (1 / w)
  simp_rw [← p3j_sum_Icc_alt] at hlim
  convert hlim using 2
  have hs : sin (π * w) ≠ 0 := sin_pi_mul_ne_zero hx
  have := p3j_cot_half_sub hs
  rw [show π * (w / 2) = π * w / 2 by ring]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [div_eq_mul_one_div (π : ℂ), ← this]
  field_simp
  ring

/-- `2Kτ = 2iK'`. -/
lemma p3j_two_K_tau {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    2 * compEllIntKk k * jacobiTauk k = 2 * (I * compEllIntKpk k) := by
  have := p22R1_compEllIntKk_ne_zero hk
  rw [jacobiTauk]; field_simp

/-- A function with the pole dichotomy is analytic where its order is not negative. -/
theorem p3j_Dich.analyticAt_of_not_neg {f : ℂ → ℂ} (hf : p3j_Dich f) {z : ℂ}
    (h : ¬ meromorphicOrderAt f z < 0) : AnalyticAt ℂ f z :=
  (hf z).resolve_right fun h' => h h'.1

/-- `p s` (with `p ≠ s`) is analytic off the points congruent to `0`. -/
lemma p3j_ps_analyticAt {k : ℂ} (hk : k ∈ jacobiModulusDomain) {p : JacobiLetter}
    (hp : p ≠ .s) {z : ℂ} (hz : z ∉ jacobiCongruentk 0 k) :
    AnalyticAt ℂ (fun w => jacobiPQk p .s w k) z := by
  have h := jacobiPQk_zeros_poles hk hp z
  by_cases hzp : z ∈ jacobiCongruentk (jacobiLetterPointk p k) k
  · refine (p3j_dich_pq hk hp).analyticAt_of_not_neg ?_
    rw [h.1.mpr hzp]; decide
  · exact (h.2.2 hzp hz).1

/-- A letter function is analytic at a point where its denominator letter is nonzero. -/
lemma p3j_pq_analyticAt {k : ℂ} (hk : k ∈ jacobiModulusDomain) {p q : JacobiLetter}
    (hpq : p ≠ q) {z : ℂ} (hz : jacobiLetterTheta q (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    AnalyticAt ℂ (fun w => jacobiPQk p q w k) z :=
  Complex.analyticAt_iff_eventually_differentiableAt.mpr
    ((p22R1_eventually_ne hk hz).mono fun _ hw => (p22R1_hasDerivAt_PQ hk hpq hw).differentiableAt)

/-- The Eisenstein-type series identity for `ns` (`ε = 1`) and `ds` (`ε = -1`):
`2K · ps(2Kt) = ∑ₙ εⁿ π/sin(π(t - nτ))` off the lattice. -/
lemma p3j_ps_eq_G {k : ℂ} (hk : k ∈ jacobiModulusDomain) {p : JacobiLetter} {ε : ℂ}
    (hp : p = .n ∧ ε = 1 ∨ p = .d ∧ ε = -1) {t : ℂ} (ht : t ∉ p3j_latt (jacobiTauk k)) :
    2 * compEllIntKk k * jacobiPQk p .s (2 * compEllIntKk k * t) k = p3j_G ε (jacobiTauk k) t := by
  have hτ := jacobiTauk_im_pos hk
  have hK := p22R1_compEllIntKk_ne_zero hk
  have hK2 : 2 * compEllIntKk k ≠ 0 := mul_ne_zero two_ne_zero hK
  have hε : ε = 1 ∨ ε = -1 := by rcases hp with h | h; exacts [Or.inl h.2, Or.inr h.2]
  have hps : p ≠ .s := by rcases hp with h | h <;> rw [h.1] <;> decide
  set K := compEllIntKk k
  set f : ℂ → ℂ := fun t => 2 * K * jacobiPQk p .s (2 * K * t) k with hfdef
  -- lattice correspondence
  have hlat : ∀ t, t ∉ p3j_latt (jacobiTauk k) → 2 * K * t ∉ jacobiCongruentk 0 k := by
    rintro t ht ⟨m, n, hmn⟩
    apply ht
    refine ⟨m, n, ?_⟩
    have h2 := p3j_two_K_tau hk
    apply mul_left_cancel₀ hK2
    rw [hmn]; linear_combination (-(n : ℂ)) * h2
  have hdich : p3j_Dich f := by
    have := (p3j_dich_pq hk (p := p) (q := .s) hps).comp (a := (2 * K)⁻¹) (inv_ne_zero hK2) hK2
    convert this using 2 with w
    rw [div_inv_eq_mul, mul_comm w]
  have hf1 : ∀ t, f (t + 1) = -f t := by
    intro t
    simp only [hfdef, show 2 * K * (t + 1) = 2 * K * t + 2 * K by ring]
    rcases hp with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · have hs : jacobiPQk .n .s (2 * K * t + 2 * K) k = -jacobiPQk .n .s (2 * K * t) k :=
        (jacobiNsk_shift hk _).2.2.2.1
      rw [hs]; ring
    · have hs : jacobiPQk .d .s (2 * K * t + 2 * K) k = -jacobiPQk .d .s (2 * K * t) k :=
        (jacobiDsk_shift hk _).2.2.2.1
      rw [hs]; ring
  have hfτ : ∀ t, f (t + jacobiTauk k) = ε * f t := by
    intro t
    have h2 : 2 * K * jacobiTauk k = 2 * (I * compEllIntKpk k) := p3j_two_K_tau hk
    simp only [hfdef, show 2 * K * (t + jacobiTauk k) = 2 * K * t + 2 * K * jacobiTauk k by ring,
      h2]
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hs : jacobiPQk .n .s (2 * K * t + 2 * (I * compEllIntKpk k)) k =
          jacobiPQk .n .s (2 * K * t) k := (jacobiNsk_shift hk _).2.2.2.2.2
      rw [hs]; ring
    · have hs : jacobiPQk .d .s (2 * K * t + 2 * (I * compEllIntKpk k)) k =
          -jacobiPQk .d .s (2 * K * t) k := (jacobiDsk_shift hk _).2.2.2.2.2
      rw [hs]; ring
  have hfodd : ∀ t, f (-t) = -f t := by
    intro t
    simp only [hfdef, show 2 * K * -t = -(2 * K * t) by ring, jacobiPQk_neg]
    rcases hp with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hfan : ∀ t ∉ p3j_latt (jacobiTauk k), AnalyticAt ℂ f t := by
    intro t ht
    have h := p3j_ps_analyticAt hk hps (hlat t ht)
    have hl : AnalyticAt ℂ (fun t : ℂ => 2 * K * t) t := by fun_prop
    exact analyticAt_const.mul (h.comp hl)
  have hf0 : ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧
      (fun t => f t - π / sin (π * t)) =ᶠ[𝓝[≠] 0] A := by
    have hreg := p22R1_reg0 hk (q := .n) (by decide)
    have hlin : AnalyticAt ℂ (fun t : ℂ => 2 * K * t) 0 := by fun_prop
    set N₁ : ℂ → ℂ := fun t => jacobiPQk p .n (2 * K * t) k
    set S₁ : ℂ → ℂ := fun t => jacobiSnk (2 * K * t) k
    have hN₁ : AnalyticAt ℂ N₁ 0 := by
      rcases hp with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · simp only [N₁, jacobiPQk_self]; exact analyticAt_const
      · exact (p3j_pq_analyticAt hk (by decide) (by simpa using hreg)).comp_of_eq hlin
          (by simp)
    have hS₁ : AnalyticAt ℂ S₁ 0 :=
      (p3j_pq_analyticAt hk (p := .s) (q := .n) (by decide) (by simpa using hreg)).comp_of_eq hlin
        (by simp)
    have hn₁ : N₁ 0 = 1 := by
      rcases hp with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · simp [N₁, jacobiPQk_self]
      · simp only [N₁, mul_zero]; exact jacobiDnk_zero hk
    have h0₁ : S₁ 0 = 0 := by simp only [S₁, mul_zero]; exact jacobiSnk_zero hk
    have hd₁ : HasDerivAt S₁ (2 * K) 0 := by
      have h := (hasDerivAt_jacobiSnk hk (z := 2 * K * 0) (by simpa using hreg)).comp (0 : ℂ)
        ((hasDerivAt_id (0 : ℂ)).const_mul (2 * K))
      simp only [mul_zero, jacobiCnk_zero hk, jacobiDnk_zero hk, mul_one, one_mul] at h
      exact h
    have hd₂ : HasDerivAt (fun t : ℂ => sin (π * t)) (π : ℂ) 0 := by
      have := ((hasDerivAt_id (0 : ℂ)).const_mul (π : ℂ)).csin
      simpa using this
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    obtain ⟨A, hA, hev⟩ := p3j_removable (a := 2 * K) (b := π) (N₂ := fun _ => 1)
      (S₂ := fun t => sin (π * t)) hN₁ analyticAt_const hS₁ (by fun_prop) h0₁ (by simp) hn₁ rfl
      hd₁ hd₂ hK2 hπ (by ring)
    refine ⟨A, hA, ?_⟩
    have hfe : ∀ᶠ t in 𝓝 (0 : ℂ), f t = 2 * K * N₁ t / S₁ t := by
      have h1 := (p22R1_eventually_ne hk hreg)
      have ht : Tendsto (fun t : ℂ => 2 * K * t) (𝓝 0) (𝓝 0) := by
        have := (hlin.continuousAt.tendsto); simpa using this
      filter_upwards [ht.eventually h1] with t htn
      simp only [hfdef, N₁, S₁, jacobiSnk]
      rcases hp with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · rw [jacobiPQk_eq_one_div, jacobiPQk_self]; ring
      · rw [jacobiPQk_eq_div (r := .n) (by decide) (by decide) (by decide) htn]; ring
    filter_upwards [hev, nhdsWithin_le_nhds hfe] with t h1 h2
    rw [← h1, h2]; ring
  have := p3j_eq_G hε hτ hdich hf1 hfτ hfodd hfan hf0 t ht
  exact this


/-- A point avoiding all `m + nτ` is off the lattice. -/
theorem p3j_not_latt {τ t : ℂ} (h : ∀ m n : ℤ, t - m - n * τ ≠ 0) : t ∉ p3j_latt τ := by
  rintro ⟨m, n, rfl⟩; exact h m n (by ring)

/-- DLMF 22.12.11 (outer series): `∑ₙ π/sin(π(t - nτ)) = 2K ns(2Kt)`. -/
theorem p3j_hasSum_ns {k : ℂ} (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : t ∉ p3j_latt (jacobiTauk k)) :
    HasSum (fun n : ℤ => π / sin (π * (t - n * jacobiTauk k)))
      (2 * compEllIntKk k * jacobiNsk (2 * compEllIntKk k * t) k) := by
  have h := (p3j_summable_all (ε := 1) (Or.inl rfl) (jacobiTauk_im_pos hk) t).hasSum
  have e : (∑' n : ℤ, p3j_term 1 (jacobiTauk k) n t) =
      2 * compEllIntKk k * jacobiNsk (2 * compEllIntKk k * t) k :=
    (p3j_ps_eq_G hk (Or.inl ⟨rfl, rfl⟩) ht).symm
  rw [e] at h
  convert h using 2 with n
  simp [p3j_term]

/-- DLMF 22.12.12 (outer series): `∑ₙ (-1)ⁿ π/sin(π(t - nτ)) = 2K ds(2Kt)`. -/
theorem p3j_hasSum_ds {k : ℂ} (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : t ∉ p3j_latt (jacobiTauk k)) :
    HasSum (fun n : ℤ => (-1) ^ n * π / sin (π * (t - n * jacobiTauk k)))
      (2 * compEllIntKk k * jacobiDsk (2 * compEllIntKk k * t) k) := by
  have h := (p3j_summable_all (ε := -1) (Or.inr rfl) (jacobiTauk_im_pos hk) t).hasSum
  have e : (∑' n : ℤ, p3j_term (-1) (jacobiTauk k) n t) =
      2 * compEllIntKk k * jacobiDsk (2 * compEllIntKk k * t) k :=
    (p3j_ps_eq_G hk (Or.inr ⟨rfl, rfl⟩) ht).symm
  rw [e] at h
  exact h

/-- The twisted alternating Mittag-Leffler expansion
`∑_{|m| ≤ M} (-1)^(m+n)/(w - m) → (-1)ⁿ π/sin(πw)`. -/
theorem p3j_tendsto_alt' {w : ℂ} (hw : ∀ m : ℤ, w - m ≠ 0) (n : ℤ) :
    Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (-1 : ℂ) ^ (m + n) / (w - m)) atTop
      (𝓝 ((-1) ^ n * π / sin (π * w))) := by
  have h := (p3j_tendsto_alt hw).const_mul ((-1 : ℂ) ^ n)
  rw [← mul_div_assoc] at h
  refine h.congr fun M => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [zpow_add₀ (by norm_num)]; ring

/-! ### Fourier expansions: the double-series interchange -/

/-- `π / sin(πx)` as a geometric series in `exp(-πix)` for `Im x < 0`. -/
lemma p3j_hasSum_inv_sin_neg {x : ℂ} (hx : x.im < 0) :
    HasSum (fun j : ℕ => 2 * π * I * cexp (-(π * I * (2 * j + 1) * x))) (π / sin (π * x)) := by
  set a := cexp (-(π * I * x))
  have ha : ‖a‖ < 1 := by
    rw [Complex.norm_exp]
    have : (-(π * I * x)).re = π * x.im := by simp [Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have ha2 : ‖a ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg a]
  have h1 : a ^ 2 ≠ 1 := fun h => by rw [h] at ha2; simp at ha2
  have hg := (hasSum_geometric_of_norm_lt_one ha2).mul_left (2 * π * I * a)
  have hsin : sin (π * x) = (a - a⁻¹) * I / 2 := by
    rw [Complex.sin, show a⁻¹ = cexp (π * x * I) by rw [← Complex.exp_neg]; ring_nf]
    simp only [a]; ring_nf
  have ha0 : a ≠ 0 := Complex.exp_ne_zero _
  convert hg using 1
  · funext j
    rw [show -(π * I * (2 * (j : ℂ) + 1) * x) = (2 * j + 1 : ℕ) * (-(π * I * x)) by push_cast; ring,
      Complex.exp_nat_mul, ← pow_mul, pow_succ]
    ring
  · rw [hsin]
    have h2 : 1 - a ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    field_simp
    ring_nf
    rw [Complex.I_sq]; ring

/-- `π / sin(πx)` as a geometric series in `exp(πix)` for `Im x > 0`. -/
lemma p3j_hasSum_inv_sin_pos {x : ℂ} (hx : 0 < x.im) :
    HasSum (fun j : ℕ => -(2 * π * I * cexp (π * I * (2 * j + 1) * x))) (π / sin (π * x)) := by
  have h := (p3j_hasSum_inv_sin_neg (x := -x) (by simpa using hx)).neg
  convert h using 1
  · funext j; ring_nf
  · rw [show π * -x = -(π * x) by ring, Complex.sin_neg, div_neg, neg_neg]

/-- `‖sin w‖ ≤ exp |Im w|`. -/
lemma p3j_norm_sin_le (w : ℂ) : ‖sin w‖ ≤ Real.exp |w.im| := by
  rw [Complex.sin]
  have h1 : ‖cexp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; exact le_abs_self _
  have h2 : ‖cexp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; exact neg_le_abs _
  rw [norm_div, norm_mul, Complex.norm_I, mul_one]
  simp only [Complex.norm_ofNat]
  have := norm_sub_le (cexp (-w * I)) (cexp (w * I))
  linarith

/-- Core double-series interchange for the Fourier expansions: if
`∑ₙ εⁿ (a π/sin(π(t-(n+c)τ)) + b π/sin(π(t+(n+c)τ))) = S` with `|Im t| < c Im τ`, then
`S = ∑ⱼ 2πi (a e^{-πimt} - b e^{πimt}) e^{πiτmc}/(1 - ε qᵐ)`, `m = 2j+1`, `q = e^{πiτ}`. -/
theorem p3j_core {ε τ t : ℂ} {c : ℝ} (hε : ε = 1 ∨ ε = -1) (hτ : 0 < τ.im) (hc : 0 < c)
    (ht : |t.im| < c * τ.im) {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) {S : ℂ}
    (hS : HasSum (fun n : ℕ => ε ^ n * (a * (π / sin (π * (t - (n + c) * τ))) +
      b * (π / sin (π * (t + (n + c) * τ))))) S) :
    HasSum (fun j : ℕ => 2 * π * I * (a * cexp (-(π * I * (2 * j + 1) * t)) -
      b * cexp (π * I * (2 * j + 1) * t)) * cexp (π * I * τ * (2 * j + 1) * c) /
        (1 - ε * cexp (π * I * τ) ^ (2 * j + 1))) S := by
  have hεn : ∀ n : ℕ, ‖ε ^ n‖ = 1 := fun n => by
    rcases hε with rfl | rfl <;> simp
  set f : ℕ × ℕ → ℂ := fun p => ε ^ p.1 * (2 * π * I * (a * cexp (-(π * I * (2 * p.2 + 1) * t)) -
      b * cexp (π * I * (2 * p.2 + 1) * t)) * cexp (π * I * τ * (2 * p.2 + 1) * (p.1 + c)))
    with hf
  -- norm bound
  set α : ℝ := π * |t.im| - π * c * τ.im
  set β : ℝ := π * τ.im
  have hα : α < 0 := by simp only [α]; nlinarith [Real.pi_pos]
  have hβ : 0 < β := by simp only [β]; nlinarith [Real.pi_pos]
  have hbound : ∀ p : ℕ × ℕ, ‖f p‖ ≤ 4 * π * (Real.exp α ^ p.2 * Real.exp (-β) ^ p.1) := by
    rintro ⟨n, j⟩
    have e1 : ‖cexp (-(π * I * (2 * j + 1) * t))‖ ≤ Real.exp (π * (2 * j + 1) * |t.im|) := by
      rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
      have : (-(π * I * (2 * (j : ℂ) + 1) * t)).re = π * (2 * j + 1) * t.im := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [this]; gcongr; exact le_abs_self _
    have e2 : ‖cexp (π * I * (2 * j + 1) * t)‖ ≤ Real.exp (π * (2 * j + 1) * |t.im|) := by
      rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
      have : (π * I * (2 * (j : ℂ) + 1) * t).re = -(π * (2 * j + 1) * t.im) := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [this]
      have := neg_abs_le t.im
      have : 0 ≤ π * (2 * (j : ℝ) + 1) := by positivity
      nlinarith
    have e3 : ‖cexp (π * I * τ * (2 * j + 1) * (n + c))‖ =
        Real.exp (-(π * τ.im * (2 * j + 1) * (n + c))) := by
      rw [Complex.norm_exp]; congr 1
      simp [Complex.mul_re, Complex.mul_im] <;> ring
    have e4 : ‖a * cexp (-(π * I * (2 * j + 1) * t)) - b * cexp (π * I * (2 * j + 1) * t)‖ ≤
        2 * Real.exp (π * (2 * j + 1) * |t.im|) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have := mul_le_mul ha e1 (norm_nonneg _) zero_le_one
      have := mul_le_mul hb e2 (norm_nonneg _) zero_le_one
      linarith
    simp only [hf, norm_mul, hεn, one_mul, e3, Complex.norm_ofNat, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have key : Real.exp (π * (2 * j + 1) * |t.im|) *
        Real.exp (-(π * τ.im * (2 * j + 1) * (n + c))) ≤ Real.exp α ^ j * Real.exp (-β) ^ n := by
      rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      simp only [α, β]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have h1 : 0 ≤ π * τ.im := by positivity
      have h2 : 0 ≤ π * c * τ.im - π * |t.im| := by linarith
      nlinarith [mul_nonneg (mul_nonneg h1 hn) hj, mul_nonneg h2 hj]
    have hp := Real.pi_pos
    calc 2 * π * ‖a * cexp (-(π * I * (2 * j + 1) * t)) - b * cexp (π * I * (2 * j + 1) * t)‖ *
          Real.exp (-(π * τ.im * (2 * j + 1) * (n + c)))
        ≤ 2 * π * (2 * Real.exp (π * (2 * j + 1) * |t.im|)) *
          Real.exp (-(π * τ.im * (2 * j + 1) * (n + c))) := by gcongr
      _ = 4 * π * (Real.exp (π * (2 * j + 1) * |t.im|) *
          Real.exp (-(π * τ.im * (2 * j + 1) * (n + c)))) := by ring
      _ ≤ _ := by gcongr
  have hsum : Summable fun p : ℕ × ℕ => 4 * π * (Real.exp α ^ p.2 * Real.exp (-β) ^ p.1) := by
    refine Summable.mul_left _ ?_
    have h1 : Summable fun j : ℕ => Real.exp α ^ j :=
      summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr hα)
    have h2 : Summable fun n : ℕ => Real.exp (-β) ^ n :=
      summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))
    have := summable_mul_of_summable_norm (f := fun n : ℕ => Real.exp (-β) ^ n)
      (g := fun j : ℕ => Real.exp α ^ j) (by simpa using h2) (by simpa using h1)
    convert this using 2 with p; ring
  have hfs : Summable f := Summable.of_norm_bounded hsum hbound
  -- fibres in `n`
  have hfn : ∀ n : ℕ, HasSum (fun j => f (n, j)) (ε ^ n * (a * (π / sin (π * (t - (n + c) * τ))) +
      b * (π / sin (π * (t + (n + c) * τ))))) := by
    intro n
    have hm : (t - (n + c) * τ).im < 0 := by
      have : (t - ((n : ℂ) + c) * τ).im = t.im - (n + c) * τ.im := by simp
      rw [this]; have := le_abs_self t.im
      nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hτ.le]
    have hp : 0 < (t + (n + c) * τ).im := by
      have : (t + ((n : ℂ) + c) * τ).im = t.im + (n + c) * τ.im := by simp
      rw [this]; have := neg_abs_le t.im
      nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hτ.le]
    have h := (((p3j_hasSum_inv_sin_neg hm).mul_left a).add
      ((p3j_hasSum_inv_sin_pos hp).mul_left b)).mul_left (ε ^ n)
    convert h using 1
    funext j
    simp only [hf]
    have ex1 : cexp (-(π * I * (2 * j + 1) * (t - (n + c) * τ))) =
        cexp (-(π * I * (2 * j + 1) * t)) * cexp (π * I * τ * (2 * j + 1) * (n + c)) := by
      rw [← Complex.exp_add]; ring_nf
    have ex2 : cexp (π * I * (2 * j + 1) * (t + (n + c) * τ)) =
        cexp (π * I * (2 * j + 1) * t) * cexp (π * I * τ * (2 * j + 1) * (n + c)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [ex1, ex2]; ring
  -- fibres in `j`
  have hfj : ∀ j : ℕ, HasSum (fun n => f (n, j)) (2 * π * I * (a * cexp (-(π * I * (2 * j + 1) *
      t)) - b * cexp (π * I * (2 * j + 1) * t)) * cexp (π * I * τ * (2 * j + 1) * c) /
        (1 - ε * cexp (π * I * τ) ^ (2 * j + 1))) := by
    intro j
    set Q := cexp (π * I * τ) ^ (2 * j + 1)
    have hQ : ‖ε * Q‖ < 1 := by
      rw [norm_mul, show ‖ε‖ = 1 by simpa using hεn 1, one_mul, norm_pow, Complex.norm_exp]
      have : (π * I * τ).re = -(π * τ.im) := by simp [Complex.mul_re, Complex.mul_im]
      rw [this]
      exact pow_lt_one₀ (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith)) (by omega)
    have hg := (hasSum_geometric_of_norm_lt_one hQ).mul_left
      (2 * π * I * (a * cexp (-(π * I * (2 * j + 1) * t)) - b * cexp (π * I * (2 * j + 1) * t)) *
        cexp (π * I * τ * (2 * j + 1) * c))
    convert hg using 1
    · funext n
      simp only [hf, Q]
      have : cexp (π * I * τ * (2 * j + 1) * (n + c)) =
          cexp (π * I * τ * (2 * j + 1) * c) * (cexp (π * I * τ) ^ (2 * j + 1)) ^ n := by
        rw [← pow_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]; push_cast; ring_nf
      rw [this, mul_pow]; ring
    · rw [div_eq_mul_inv]
  have h1 := hfs.hasSum.prod_fiberwise hfn
  have hS' := h1.unique hS
  have h2 := ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hfs.hasSum).prod_fiberwise
    (g := fun j : ℕ => _) fun j => hfj j
  rw [hS'] at h2
  exact h2

/-- `e^{-πimt} - e^{πimt} = -2i sin(m πt)`. -/
theorem p3j_exp_sub (m t : ℂ) :
    cexp (-(π * I * m * t)) - cexp (π * I * m * t) = -2 * I * sin (m * (π * t)) := by
  rw [Complex.sin]
  ring_nf
  rw [Complex.I_sq]; ring_nf

/-- `e^{-πimt} + e^{πimt} = 2 cos(m πt)`. -/
theorem p3j_exp_add (m t : ℂ) :
    cexp (-(π * I * m * t)) + cexp (π * I * m * t) = 2 * cos (m * (π * t)) := by
  rw [Complex.cos]
  ring_nf

/-- The nome is `q = e^{πiτ}`. -/
theorem p3j_nome_eq {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiNomek k = cexp (π * I * jacobiTauk k) := by
  have := p22R1_compEllIntKk_ne_zero hk
  rw [jacobiNomek, jacobiTauk]
  congr 1
  field_simp
  ring_nf
  rw [Complex.I_sq]; ring

/-- `ζ = π t` for `z = 2Kt`. -/
theorem p3j_zeta_eq {k : ℂ} (hk : k ∈ jacobiModulusDomain) (t : ℂ) :
    jacobiZetak (2 * compEllIntKk k * t) k = π * t := by
  have := p22R1_compEllIntKk_ne_zero hk
  rw [jacobiZetak]; field_simp

/-- The strip condition `‖q‖ e^{c'|Im ζ|} < 1` in terms of `t`. -/
theorem p3j_strip_of {k : ℂ} (hk : k ∈ jacobiModulusDomain) {t : ℂ} {c : ℝ} (hc : 0 < c)
    (h : ‖jacobiNomek k‖ * Real.exp (c * |(jacobiZetak (2 * compEllIntKk k * t) k).im|) < 1) :
    |t.im| < 1 / c * (jacobiTauk k).im := by
  rw [p3j_nome_eq hk, Complex.norm_exp, p3j_zeta_eq hk, ← Real.exp_add, Real.exp_lt_one_iff] at h
  have e1 : (π * I * jacobiTauk k).re = -(π * (jacobiTauk k).im) := by
    simp [Complex.mul_re, Complex.mul_im]
  have e2 : (π * t).im = π * t.im := by simp
  rw [e1, e2, abs_mul, abs_of_pos Real.pi_pos] at h
  rw [div_mul_eq_mul_div, one_mul, lt_div_iff₀ hc]
  nlinarith [Real.pi_pos]

/-- The `ℕ`-pairing `n ↔ -n` of a `ℤ`-indexed sum, without the `n = 0` term. -/
theorem p3j_pair0 {F : ℤ → ℂ} {S : ℂ} (h : HasSum F S) :
    HasSum (fun n : ℕ => F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))) (S - F 0) := by
  have h2 := h.nat_add_neg
  have h3 := (hasSum_nat_add_iff' 1).mpr h2
  convert h3 using 1
  · funext n; push_cast; ring_nf
  · simp

/-- `k' ≠ 0` on `jacobiModulusDomain`. -/
theorem p3j_comod_ne {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiComodulusk k ≠ 0 := by
  rw [jacobiComodulusk]
  intro h
  rw [Complex.cpow_eq_zero_iff] at h
  have h1 : (k - 1) * (k + 1) = 0 := by linear_combination -h.1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · have : k = 1 := by linear_combination h2
    have := hk.2; simp_all
  · have e : k = -1 := by linear_combination h2
    have h3 := hk.1; rw [e] at h3; norm_num at h3

/-- The strip `|Im t| < Im τ/2` avoids the half-shifted lattice. -/
theorem p3j_half_ne {τ t : ℂ} (hτ : 0 < τ.im) (hs : |t.im| < 1 / 2 * τ.im) (n m : ℤ) :
    t - m - (n + 1 / 2) * τ ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp at him
  have e : t.im = (n + 1 / 2) * τ.im := by linarith
  rw [e, abs_mul, abs_of_pos hτ] at hs
  have hn : |(n : ℝ) + 1 / 2| < 1 / 2 := by nlinarith
  rw [abs_lt] at hn
  have h1 : (-1 : ℝ) < n := by linarith
  have h2 : (n : ℝ) < 0 := by linarith
  have h1' : (-1 : ℤ) < n := by exact_mod_cast h1
  have h2' : n < (0 : ℤ) := by exact_mod_cast h2
  omega

/-- `sin(A + jπ) = (-1)ʲ sin A` and `cos(A + jπ) = (-1)ʲ cos A`. -/
lemma p3j_add_nat_pi (A : ℂ) (j : ℕ) :
    sin (A + j * π) = (-1) ^ j * sin A ∧ cos (A + j * π) = (-1) ^ j * cos A := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show A + ((j + 1 : ℕ) : ℂ) * π = (A + j * π) + π by push_cast; ring, Complex.sin_add_pi,
      Complex.cos_add_pi, ih.1, ih.2, pow_succ]
    constructor <;> ring

/-- `sin(m(x + π/2)) = (-1)ʲ cos(mx)` for `m = 2j+1`. -/
theorem p3j_sin_shift (j : ℕ) (x : ℂ) :
    sin ((2 * j + 1) * (x + π / 2)) = (-1) ^ j * cos ((2 * j + 1) * x) := by
  rw [show (2 * (j : ℂ) + 1) * (x + π / 2) = ((2 * j + 1) * x + π / 2) + j * π by ring,
    (p3j_add_nat_pi _ j).1, Complex.sin_add_pi_div_two]

/-- `cos(m(x + π/2)) = -(-1)ʲ sin(mx)` for `m = 2j+1`. -/
theorem p3j_cos_shift (j : ℕ) (x : ℂ) :
    cos ((2 * j + 1) * (x + π / 2)) = -((-1) ^ j * sin ((2 * j + 1) * x)) := by
  rw [show (2 * (j : ℂ) + 1) * (x + π / 2) = ((2 * j + 1) * x + π / 2) + j * π by ring,
    (p3j_add_nat_pi _ j).2, Complex.cos_add_pi_div_two]; ring

/-- `ζ(z + K) = ζ + π/2`. -/
theorem p3j_zeta_add_K {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiZetak (z + compEllIntKk k) k = jacobiZetak z k + π / 2 := by
  have := p22R1_compEllIntKk_ne_zero hk
  simp only [jacobiZetak]; field_simp

end DLMF.JacobiElliptic
