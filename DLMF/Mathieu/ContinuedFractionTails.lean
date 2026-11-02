/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Basic.ContinuedFractions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Convergence of the continued fractions of Mathieu's equation

The truncations `q²/(s₀ - a - q²/(s₁ - a - ⋯ - q²/(s_{N-1} - a)))` of the infinite continued
fractions of DLMF 28.6.16–28.6.19 converge to `-q A₁/A₀` whenever `A` is a solution of the
three-term recurrence `q (A_k + A_{k+2}) = (a - s_k) A_{k+1}` that tends to `0`, with `A₀ ≠ 0` and
`|s_k| → ∞` (a form of Pincherle's theorem).

Beyond the index where `|s_k - a| ≥ 4|q|`, the maps `F ↦ q²/(s_k - a - F)` contract the disc
`|F| ≤ |q|` by the factor `1/9`, and a decaying solution has `|A_{k+1}| < |A_k|`, so the tails
converge to the ratios `-q A_{k+1}/A_k`. The finitely many remaining levels are handled in
projective form (`ContinuedFractionTail.numerator`,
`ContinuedFractionTail.denominator`), which avoids any assumption that intermediate
coefficients `A_k` are nonzero.

## Main results

* `mathieuCFTail_succ`: the recursion of the truncations.
* `tendsto_mathieuCFTail_of_tendsto_zero`: convergence of the truncations.
* `tendsto_neg_mathieuCFTail_mathieuCFHead`: the continued-fraction equations of
  DLMF 28.6.16–28.6.19 for a decaying solution of the recurrence.
-/

@[expose] public noncomputable section

open Filter Topology

namespace DLMF.Mathieu

/-- The recursion of the truncated tails: one more level on top. -/
theorem mathieuCFTail_succ (q a : ℂ) (s : ℕ → ℂ) (N : ℕ) :
    mathieuCFTail q a s (N + 1) =
      q ^ 2 / (s 0 - a - mathieuCFTail q a (fun k => s (k + 1)) N) := by
  simp only [mathieuCFTail, List.range_succ_eq_map, List.foldr_cons, List.foldr_map]

namespace ContinuedFractionTail

variable {q a : ℂ} {s A : ℕ → ℂ}

/-- The `L`-fold composition of the maps `F ↦ q²/(s_j - a - F)` from level `j + L` down to
level `j`. -/
noncomputable def fold (q a : ℂ) (s : ℕ → ℂ) : ℕ → ℕ → ℂ → ℂ
  | 0, _, T => T
  | L + 1, j, T => q ^ 2 / (s j - a - fold q a s L (j + 1) T)

/-- The coefficients `(α₁, β₁, α₂, β₂)` of the projective form of `fold`. -/
noncomputable def coefficients (q a : ℂ) (s : ℕ → ℂ) : ℕ → ℕ → ℂ × ℂ × ℂ × ℂ
  | 0, _ => (1, 0, 0, 1)
  | L + 1, j =>
    let m := coefficients q a s L (j + 1)
    (q ^ 2 * m.2.2.1, q ^ 2 * m.2.2.2, (s j - a) * m.2.2.1 - m.1, (s j - a) * m.2.2.2 - m.2.1)

/-- Numerator of the projective form. -/
noncomputable def numerator (q a : ℂ) (s : ℕ → ℂ) (L j : ℕ) (T : ℂ) : ℂ :=
  (coefficients q a s L j).1 * T + (coefficients q a s L j).2.1

/-- Denominator of the projective form. -/
noncomputable def denominator (q a : ℂ) (s : ℕ → ℂ) (L j : ℕ) (T : ℂ) : ℂ :=
  (coefficients q a s L j).2.2.1 * T + (coefficients q a s L j).2.2.2

/-- Recursion of the numerator. -/
lemma numerator_succ (L j : ℕ) (T : ℂ) : numerator q a s (L + 1) j T = q ^ 2 *
    denominator q a s L (j + 1) T := by
  simp only [numerator, denominator, coefficients]; ring

/-- Recursion of the denominator. -/
lemma denominator_succ (L j : ℕ) (T : ℂ) :
    denominator q a s (L + 1) j T = (s j - a) * denominator q a s L (j + 1) T -
        numerator q a s L (j + 1) T := by
  simp only [numerator, denominator, coefficients]; ring

/-- The determinant of the projective form is `q^{2L}`. -/
lemma det_coefficients (L j : ℕ) :
    (coefficients q a s L j).1 * (coefficients q a s L j).2.2.2 - (coefficients q a s L j).2.1 *
        (coefficients q a s L j).2.2.1 =
      q ^ (2 * L) := by
  induction L generalizing j with
  | zero => simp [coefficients]
  | succ L ih =>
    simp only [coefficients]
    have := ih (j + 1)
    rw [show 2 * (L + 1) = 2 * L + 2 by ring, pow_add, ← this]
    ring

/-- The non-vanishing of the intermediate denominators. -/
def DenominatorsNonzero (q a : ℂ) (s : ℕ → ℂ) : ℕ → ℕ → ℂ → Prop
  | 0, _, _ => True
  | L + 1, j, T => DenominatorsNonzero q a s L (j + 1) T ∧ denominator q a s L (j + 1) T ≠ 0

/-- `fold` is the quotient of the projective form when the intermediate denominators are
nonzero. -/
lemma fold_eq (L j : ℕ) (T : ℂ) (h : DenominatorsNonzero q a s L j T) :
    fold q a s L j T = numerator q a s L j T / denominator q a s L j T := by
  induction L generalizing j with
  | zero => simp [fold, numerator, denominator, coefficients]
  | succ L ih =>
    obtain ⟨h1, h2⟩ := h
    rw [fold, ih (j + 1) h1, numerator_succ, denominator_succ]
    rw [show s j - a - numerator q a s L (j + 1) T / denominator q a s L (j + 1) T =
      ((s j - a) * denominator q a s L (j + 1) T - numerator q a s L (j + 1) T) /
          denominator q a s L (j + 1) T by
        field_simp, div_div_eq_mul_div]

/-- The truncations at level `j` with `L` more terms are `fold` of those at level `j + L`. -/
lemma mathieuCFTail_add (L j N : ℕ) :
    mathieuCFTail q a (fun k => s (j + k)) (N + L) =
      fold q a s L j (mathieuCFTail q a (fun k => s (j + L + k)) N) := by
  induction L generalizing j with
  | zero => simp [fold]
  | succ L ih =>
    rw [show N + (L + 1) = N + L + 1 by ring, mathieuCFTail_succ, fold]
    have e1 : (fun k => s (j + (k + 1))) = fun k => s (j + 1 + k) :=
      funext fun k => by rw [show j + (k + 1) = j + 1 + k by ring]
    have e2 : (fun k => s (j + 1 + L + k)) = fun k => s (j + (L + 1) + k) :=
      funext fun k => by rw [show j + 1 + L + k = j + (L + 1) + k by ring]
    simp only [add_zero]
    rw [e1, ih (j + 1), e2]

/-- The ratio `u_j = -q A_{j+1}/A_j` and the projective identity. -/
lemma numerator_denominator_ratio
    (hrec : ∀ k, q * (A k + A (k + 2)) = (a - s k) * A (k + 1)) (L j : ℕ)
    (hA : A (j + L) ≠ 0) :
    numerator q a s L j (-(q * A (j + L + 1) / A (j + L))) =
        (-q) ^ L / A (j + L) * (-(q * A (j + 1))) ∧
      denominator q a s L j (-(q * A (j + L + 1) / A (j + L))) = (-q) ^ L / A (j + L) * A j := by
  induction L generalizing j with
  | zero =>
    simp only [add_zero] at hA
    simp only [numerator, denominator, coefficients, add_zero, pow_zero]
    constructor
    · field_simp
    · field_simp; ring
  | succ L ih =>
    have h := ih (j + 1) (by simpa [show j + 1 + L = j + (L + 1) by ring] using hA)
    simp only [show j + 1 + L = j + (L + 1) by ring] at h
    rw [numerator_succ, denominator_succ, h.1, h.2]
    have hr := hrec j
    rw [show j + 1 + 1 = j + 2 by ring]
    constructor
    · ring
    · rw [pow_succ]
      linear_combination (-q) ^ L / A (j + (L + 1)) * hr

/-- The numerator is continuous (affine). -/
lemma continuous_numerator (L j : ℕ) : Continuous (numerator q a s L j) := by
  unfold numerator; fun_prop

/-- The denominator is continuous (affine). -/
lemma continuous_denominator (L j : ℕ) : Continuous (denominator q a s L j) := by
  unfold denominator; fun_prop

/-- Eventually all intermediate denominators are nonzero along a sequence `T N → u` that never
takes the value `u`. -/
lemma eventually_denominatorsNonzero (hq : q ≠ 0) {T : ℕ → ℂ} {u : ℂ} (hT : Tendsto T atTop (𝓝 u))
    (hTu : ∀ N, T N ≠ u) (L j : ℕ) : ∀ᶠ N in atTop, DenominatorsNonzero q a s L j (T N) := by
  induction L generalizing j with
  | zero => exact Eventually.of_forall fun _ => trivial
  | succ L ih =>
    refine (ih (j + 1)).and ?_
    set α := (coefficients q a s L (j + 1)).2.2.1
    set β := (coefficients q a s L (j + 1)).2.2.2
    have hdet := det_coefficients (q := q) (a := a) (s := s) L (j + 1)
    have hden : ∀ T, denominator q a s L (j + 1) T = α * T + β := fun T => rfl
    by_cases hu : α * u + β = 0
    · have hα : α ≠ 0 := by
        intro h0
        have hβ : β = 0 := by simpa [h0] using hu
        rw [show (coefficients q a s L (j + 1)).2.2.1 = α from rfl,
          show (coefficients q a s L (j + 1)).2.2.2 = β from rfl, h0, hβ] at hdet
        simp only [mul_zero, sub_self] at hdet
        exact pow_ne_zero _ hq hdet.symm
      refine Eventually.of_forall fun N => ?_
      rw [hden, show α * T N + β = α * (T N - u) by linear_combination hu]
      exact mul_ne_zero hα (sub_ne_zero.2 (hTu N))
    · have hc := ((continuous_denominator (q := q) (a := a) (s := s) L (j + 1)).tendsto u).comp hT
      rw [hden u] at hc
      filter_upwards [hc.eventually_ne hu] with N hN
      simpa [hden] using hN

end ContinuedFractionTail

open ContinuedFractionTail in
/-- **Convergence of the tails** (Pincherle's theorem for the continued fractions of
DLMF 28.6.16–28.6.19): let `A` be a solution of `q (A_k + A_{k+2}) = (a - s_k) A_{k+1}` with
`A_0 ≠ 0` and `A_k → 0`, where `|s_k| → ∞`. Then the truncations
`q²/(s₀ - a - q²/(s₁ - a - ⋯))` converge to `-q A₁/A₀`. -/
theorem tendsto_mathieuCFTail_of_tendsto_zero {q a : ℂ} {s A : ℕ → ℂ} (hq : q ≠ 0)
    (hrec : ∀ k, q * (A k + A (k + 2)) = (a - s k) * A (k + 1))
    (hA0 : A 0 ≠ 0) (hlim : Tendsto A atTop (𝓝 0))
    (hs : Tendsto (fun k => ‖s k‖) atTop atTop) :
    Tendsto (fun N => mathieuCFTail q a s N) atTop (𝓝 (-(q * A 1 / A 0))) := by
  have hq0 : 0 < ‖q‖ := norm_pos_iff.2 hq
  -- (a) the region where `|s_k - a| ≥ 4|q|`
  obtain ⟨K, hK⟩ : ∃ K, ∀ k ≥ K, 4 * ‖q‖ ≤ ‖s k - a‖ := by
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hs.eventually_ge_atTop (4 * ‖q‖ + ‖a‖))
    refine ⟨K, fun k hk => ?_⟩
    have := hK k hk
    have := norm_sub_norm_le (s k) a
    linarith
  -- (b) no two consecutive zeros
  have hz : ∀ k, A k = 0 → A (k + 1) = 0 → False := by
    intro k
    induction k with
    | zero => exact fun h _ => hA0 h
    | succ k ih =>
      intro h1 h2
      have hr := hrec k
      rw [h1, h2, mul_zero, add_zero] at hr
      exact ih ((mul_eq_zero.1 hr).resolve_left hq) h1
  -- (c) growth is impossible
  have hgrow : ∀ k ≥ K, A (k + 1) ≠ 0 → ‖A k‖ ≤ ‖A (k + 1)‖ → False := by
    intro k hk hne hle
    have key : ∀ j, ‖A (k + 1)‖ ≤ ‖A (k + 1 + j)‖ ∧ ‖A (k + j)‖ ≤ ‖A (k + j + 1)‖ := by
      intro j
      induction j with
      | zero => simpa using hle
      | succ j ih =>
        have hr := hrec (k + j)
        have h4 := hK (k + j) (by omega)
        have e : q * A (k + j + 2) = (a - s (k + j)) * A (k + j + 1) - q * A (k + j) := by
          linear_combination hr
        have hn : ‖q‖ * ‖A (k + j + 2)‖ ≥ 4 * ‖q‖ * ‖A (k + j + 1)‖ - ‖q‖ * ‖A (k + j)‖ := by
          have := norm_sub_norm_le ((a - s (k + j)) * A (k + j + 1)) (q * A (k + j))
          rw [← e, norm_mul, norm_mul, norm_mul, norm_sub_rev a] at this
          nlinarith [norm_nonneg (A (k + j + 1))]
        have h3 : ‖A (k + j + 1)‖ ≤ ‖A (k + j + 2)‖ := by
          by_contra hcon
          push Not at hcon
          nlinarith [ih.2, norm_nonneg (A (k + j + 1))]
        refine ⟨?_, ?_⟩
        · rw [show k + 1 + (j + 1) = k + j + 2 by ring]
          exact ih.1.trans (by rw [show k + 1 + j = k + j + 1 by ring]; exact h3)
        · rw [show k + (j + 1) = k + j + 1 by ring, show k + j + 1 + 1 = k + j + 2 by ring]
          exact h3
    have hpos : 0 < ‖A (k + 1)‖ := norm_pos_iff.2 hne
    have hev := (tendsto_norm_zero.comp hlim).eventually (gt_mem_nhds hpos)
    obtain ⟨M, hM⟩ := eventually_atTop.1 hev
    have := hM (k + 1 + M) (by omega)
    have := (key M).1
    simp only [Function.comp] at *
    linarith
  -- (d) nonvanishing and decrease beyond `K`
  have hne1 : ∀ k ≥ K, A (k + 1) ≠ 0 := by
    intro k hk h0
    have hAk : A k ≠ 0 := fun h => hz k h h0
    have hr := hrec k
    rw [h0, mul_zero] at hr
    have h2 : A (k + 2) = -A k := by
      have := (mul_eq_zero.1 hr).resolve_left hq
      linear_combination this
    refine hgrow (k + 1) (by omega)
      (by rw [show k + 1 + 1 = k + 2 by ring, h2]; exact neg_ne_zero.2 hAk) ?_
    rw [h0, norm_zero]; exact norm_nonneg _
  have hdec : ∀ k ≥ K, ‖A (k + 1)‖ < ‖A k‖ := fun k hk =>
    lt_of_not_ge fun h => hgrow k hk (hne1 k hk) h
  set L₀ := K + 1 with hL₀
  set u : ℕ → ℂ := fun k => -(q * A (k + 1) / A k) with hu
  have hAne : ∀ k ≥ L₀, A k ≠ 0 := fun k hk => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact hne1 k' (by omega)
  set T : ℕ → ℕ → ℂ := fun L N => mathieuCFTail q a (fun k => s (L + k)) N with hT
  have hTsucc : ∀ L N, T L (N + 1) = q ^ 2 / (s L - a - T (L + 1) N) := by
    intro L N
    simp only [hT, mathieuCFTail_succ, add_zero]
    congr 3
    funext k; rw [show L + (k + 1) = L + 1 + k by ring]
  -- (e), (f) the contraction region
  have hden3 : ∀ L ≥ K, ∀ F : ℂ, ‖F‖ ≤ ‖q‖ → 3 * ‖q‖ ≤ ‖s L - a - F‖ := by
    intro L hL F hF
    have := norm_sub_norm_le (s L - a) F
    linarith [hK L hL]
  have hTb : ∀ N, ∀ L ≥ K, ‖T L N‖ ≤ ‖q‖ := by
    intro N
    induction N with
    | zero => intro L _; simp [hT, mathieuCFTail]
    | succ N ih =>
      intro L hL
      rw [hTsucc, norm_div, norm_pow]
      have h3 := hden3 L hL _ (ih (L + 1) (by omega))
      rw [div_le_iff₀ (by linarith)]
      nlinarith
  have hub : ∀ L ≥ L₀, ‖u L‖ ≤ ‖q‖ := by
    intro L hL
    simp only [hu, norm_neg, norm_div, norm_mul]
    rw [div_le_iff₀ (norm_pos_iff.2 (hAne L hL))]
    have := hdec L (by omega)
    nlinarith [norm_nonneg (A (L + 1))]
  have hurec : ∀ L ≥ L₀, u L = q ^ 2 / (s L - a - u (L + 1)) := by
    intro L hL
    have h1 := hAne L hL
    have h2 := hAne (L + 1) (by omega)
    have hr := hrec L
    have e : s L - a - u (L + 1) = -(q * A L) / A (L + 1) := by
      simp only [hu]
      rw [show L + 1 + 1 = L + 2 by ring]
      field_simp
      linear_combination hr
    rw [e]
    simp only [hu]
    field_simp
  have hdist : ∀ N, ∀ L ≥ L₀, ‖T L N - u L‖ ≤ ‖q‖ * (1 / 9) ^ N ∧ T L N ≠ u L := by
    intro N
    induction N with
    | zero =>
      intro L hL
      have hT0 : T L 0 = 0 := by simp [hT, mathieuCFTail]
      have hu0 : u L ≠ 0 := neg_ne_zero.2
        (div_ne_zero (mul_ne_zero hq (hAne (L + 1) (by omega))) (hAne L hL))
      rw [hT0, zero_sub, norm_neg, pow_zero, mul_one]
      exact ⟨hub L hL, fun h => hu0 h.symm⟩
    | succ N ih =>
      intro L hL
      obtain ⟨ih1, ih2⟩ := ih (L + 1) (by omega)
      have hD1 := hden3 L (by omega) _ (hTb N (L + 1) (by omega))
      have hD2 := hden3 L (by omega) _ (hub (L + 1) (by omega))
      have hD1' : s L - a - T (L + 1) N ≠ 0 := norm_pos_iff.1 (by linarith)
      have hD2' : s L - a - u (L + 1) ≠ 0 := norm_pos_iff.1 (by linarith)
      have e : T L (N + 1) - u L = q ^ 2 * (T (L + 1) N - u (L + 1)) /
          ((s L - a - T (L + 1) N) * (s L - a - u (L + 1))) := by
        rw [hTsucc, hurec L hL]
        field_simp
        ring
      refine ⟨?_, ?_⟩
      · rw [e, norm_div, norm_mul, norm_mul, norm_pow, div_le_iff₀ (by positivity)]
        have hprod : 9 * ‖q‖ ^ 2 ≤ ‖s L - a - T (L + 1) N‖ * ‖s L - a - u (L + 1)‖ := by
          nlinarith
        calc ‖q‖ ^ 2 * ‖T (L + 1) N - u (L + 1)‖ ≤ ‖q‖ ^ 2 * (‖q‖ * (1 / 9) ^ N) := by gcongr
          _ = ‖q‖ * (1 / 9) ^ (N + 1) * (9 * ‖q‖ ^ 2) := by ring
          _ ≤ ‖q‖ * (1 / 9) ^ (N + 1) *
              (‖s L - a - T (L + 1) N‖ * ‖s L - a - u (L + 1)‖) := by gcongr
      · intro h
        rw [← sub_eq_zero, e] at h
        simp only [div_eq_zero_iff, mul_eq_zero, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, sub_eq_zero] at h
        rcases h with (h | h) | h | h
        · exact hq h
        · exact ih2 h
        · exact hD1' (sub_eq_zero.2 h)
        · exact hD2' (sub_eq_zero.2 h)
  have hTlim : Tendsto (T L₀) atTop (𝓝 (u L₀)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => (hdist N L₀ le_rfl).1) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 9)
      (by norm_num)).const_mul ‖q‖
  -- (h), (i) the finite part
  have hgood := eventually_denominatorsNonzero (s := s) (a := a) hq hTlim
      (fun N => (hdist N L₀ le_rfl).2) L₀ 0
  have hrat := numerator_denominator_ratio (s := s) hrec L₀ 0 (by simpa using hAne L₀ le_rfl)
  simp only [zero_add] at hrat
  have hc : (-q) ^ L₀ / A L₀ ≠ 0 := div_ne_zero (pow_ne_zero _ (neg_ne_zero.2 hq)) (hAne L₀ le_rfl)
  have hnum := ((continuous_numerator (q := q) (a := a) (s := s) L₀ 0).tendsto _).comp hTlim
  have hden := ((continuous_denominator (q := q) (a := a) (s := s) L₀ 0).tendsto _).comp hTlim
  simp only [hu] at hnum hden
  rw [hrat.1] at hnum
  rw [hrat.2] at hden
  have hlim2 := hnum.div hden (mul_ne_zero hc hA0)
  rw [← tendsto_add_atTop_iff_nat L₀]
  rw [mul_div_mul_left _ _ hc, neg_div] at hlim2
  refine hlim2.congr' ?_
  filter_upwards [hgood] with N hN
  have := mathieuCFTail_add (q := q) (a := a) (s := s) L₀ 0 N
  simp only [zero_add] at this
  rw [Pi.div_apply, Function.comp_apply, Function.comp_apply, ← fold_eq _ _ _ hN]
  exact this.symm


/-- With `q = 0` all truncations vanish. -/
theorem mathieuCFTail_zero_left (a : ℂ) (s : ℕ → ℂ) (N : ℕ) : mathieuCFTail 0 a s N = 0 := by
  cases N with
  | zero => simp [mathieuCFTail]
  | succ N => rw [mathieuCFTail_succ]; simp

/-- **The continued-fraction equation from a decaying solution**: if `A` solves
`e₀ A₀ = q A₁`, `q (c_k A_k + A_{k+2}) = (a - s_k) A_{k+1}` with `c_k = 1` for `k ≥ n`, is not
identically zero and tends to `0`, and `|s_k| → ∞`, then the finite continued fraction
`mathieuCFHead q a e₀ c s n` (with nonzero intermediate values) is the limit of the negated tails
`-q²/(s_n - a - q²/(s_{n+1} - a - ⋯))`. -/
theorem tendsto_neg_mathieuCFTail_mathieuCFHead {q a e₀ : ℂ} {c s A : ℕ → ℂ} {n : ℕ}
    (hq : q ≠ 0) (h0 : e₀ * A 0 = q * A 1)
    (hrec : ∀ k, q * (c k * A k + A (k + 2)) = (a - s k) * A (k + 1))
    (hc : ∀ k, n ≤ k → c k = 1) (hA : ¬ ∀ k, A k = 0) (hlim : Tendsto A atTop (𝓝 0))
    (hs : Tendsto (fun k => ‖s k‖) atTop atTop)
    (hE : ∀ k < n, mathieuCFHead q a e₀ c s k ≠ 0) :
    Tendsto (fun N => -mathieuCFTail q a (fun k => s (n + k)) N) atTop
      (𝓝 (mathieuCFHead q a e₀ c s n)) := by
  -- `A₀ ≠ 0`
  have hA0 : A 0 ≠ 0 := by
    intro h00
    have h10 : A 1 = 0 := by
      rw [h00, mul_zero] at h0; exact (mul_eq_zero.1 h0.symm).resolve_left hq
    refine hA fun k => ?_
    have : ∀ k, A k = 0 ∧ A (k + 1) = 0 := by
      intro k
      induction k with
      | zero => exact ⟨h00, h10⟩
      | succ k ih =>
        refine ⟨ih.2, ?_⟩
        have hr := hrec k
        rw [ih.1, ih.2, mul_zero, mul_zero, zero_add] at hr
        exact (mul_eq_zero.1 hr).resolve_left hq
    exact (this k).1
  -- the head
  have hhead : ∀ k ≤ n, A k ≠ 0 ∧ mathieuCFHead q a e₀ c s k = q * A (k + 1) / A k := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨hA0, ?_⟩
      simp only [mathieuCFHead]
      field_simp
      linear_combination h0
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hne : A (k + 1) ≠ 0 := by
        intro h
        apply hE k (by omega)
        rw [h2, h, mul_zero, zero_div]
      refine ⟨hne, ?_⟩
      simp only [mathieuCFHead]
      rw [h2]
      have hr := hrec k
      rw [show k + 1 + 1 = k + 2 by ring]
      field_simp
      linear_combination -hr
  obtain ⟨hAn, hHn⟩ := hhead n le_rfl
  rw [hHn]
  have ht := tendsto_mathieuCFTail_of_tendsto_zero (q := q) (a := a) (s := fun k => s (n + k))
    (A := fun k => A (n + k)) hq (fun k => by
      have := hrec (n + k)
      rw [hc (n + k) (by omega), one_mul] at this
      simpa [add_assoc] using this) (by simpa using hAn)
    (hlim.comp (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega)
      (fun b => ⟨b, by omega⟩)))
    (hs.comp (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega) (fun b => ⟨b, by omega⟩)))
  simpa [neg_div] using ht.neg

end DLMF.Mathieu
