/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.ContinuedFractions
public import DLMFMathlib.Analysis.SpecificLimits.PoincarePerron

/-!
# Convergence of the continued fraction for the incomplete Beta function (DLMF 8.17.22)

The continued fraction `1/(1 + d₁/(1 + d₂/(1 + ⋯)))` of DLMF 8.17.22–8.17.23 is related to
the backward solution `W_k = F(a+b+⌊k/2⌋, ⌊(k+1)/2⌋; a+k; x)` of its three-term recurrence
`W_k = W_{k+1} + d_{k+1} W_{k+2}`, with `W₀ = 1`. For `a, b > 0` and `0 ≤ x < 1` the solution is
positive; Perron's theorem gives `W_{k+1}/W_k → 2/(1+√(1-x)) < 2`, and the real ratio criterion
for continued fractions with eventually negative partial numerators gives convergence to `W₁`.
When some `d_K` vanishes (`x = 0`, or `b` a positive integer) the fraction terminates and the
Pincherle invariants give the value directly.

## Main results

* `DLMF.Confluent.IncompleteBetaFraction.solution_rec`: the three-term recurrence.
* `DLMF.Confluent.IncompleteBetaFraction.tendsto_solution_ratio`: the ratio limit.
* `DLMF.Confluent.IncompleteBetaFraction.tendsto_continuedFractionTail`: convergence of the finite
  continued fractions to `W₁ = F(a+b, 1; a+1; x)`.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace DLMF.Confluent
namespace IncompleteBetaFraction

open DLMF.Hypergeometric

/-- The partial numerators `d_k` of the continued fraction DLMF 8.17.22, as real numbers. -/
def partialNumerator (a b x : ℝ) (k : ℕ) : ℝ :=
  if Even k then let m : ℝ := (k/2 : ℕ); m*(b-m)*x/((a+2*m-1)*(a+2*m)) else
      let m : ℝ := ((k-1)/2 : ℕ); -(a+m)*(a+b+m)*x/((a+2*m)*(a+2*m+1))

/-- The backward solution `W_k = F(a+b+⌊k/2⌋, ⌊(k+1)/2⌋; a+k; x)` (unregularized). -/
def solution (a b x : ℝ) (k : ℕ) : ℝ :=
  Real.Gamma (a + k) * GaussContinuedFraction.backwardSolutionReal (a + b) 0 a x k

/-- `d_{k+1} (a+k)(a+k+1)` is the Gauss partial numerator with parameters `(a+b, 0; a)`. -/
theorem partialNumerator_succ_mul (a b x : ℝ) (k : ℕ) (ha : 0 < a) :
    partialNumerator a b x (k + 1) * ((a + k) * (a + k + 1)) =
      GaussContinuedFraction.partialNumReal (a + b) 0 a x k := by
  have h1 : 0 < a + k := by positivity
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · have hne : ¬ Even (2 * m + 1) := by simp
    simp only [partialNumerator, GaussContinuedFraction.partialNumReal, hne, ↓reduceIte,
      show (2 * m + 1 - 1) / 2 = m by omega, show (2 * m + 1) % 2 = 1 by omega,
      show (2 * m + 1) / 2 = m by omega]
    push_cast
    field_simp
    ring
  · have he : Even (2 * m + 1 + 1) := ⟨m + 1, by ring⟩
    simp only [partialNumerator, GaussContinuedFraction.partialNumReal, he, ↓reduceIte,
      show (2 * m + 1 + 1) / 2 = m + 1 by omega, show (2 * m + 1 + 1) % 2 = 0 by omega]
    push_cast
    have hm : (0:ℝ) ≤ m := m.cast_nonneg
    rw [show a + 2 * ((m : ℝ) + 1) - 1 = a + 2 * m + 1 by ring,
      show a + 2 * ((m : ℝ) + 1) = a + 2 * m + 2 by ring]
    have h2 : a + 2 * (m : ℝ) + 1 ≠ 0 := by intro h; linarith
    have h3 : a + 2 * (m : ℝ) + 2 ≠ 0 := by intro h; linarith
    field_simp
    ring

/-- The recurrence `W_k = W_{k+1} + d_{k+1} W_{k+2}`. -/
theorem solution_rec {a b x : ℝ} (ha : 0 < a) (hx : |x| < 1) (k : ℕ) :
    solution a b x k =
      solution a b x (k + 1) + partialNumerator a b x (k + 1) * solution a b x (k + 2) := by
  have h := GaussContinuedFraction.backwardSolutionReal_rec (a + b) 0 a hx k
  have hk := partialNumerator_succ_mul a b x k ha
  have h1 : 0 < a + k := by positivity
  have hG1 : Real.Gamma (a + ((k + 1 : ℕ) : ℝ)) = (a + k) * Real.Gamma (a + k) := by
    rw [show a + ((k + 1 : ℕ) : ℝ) = (a + k) + 1 by push_cast; ring, Real.Gamma_add_one h1.ne']
  have hG2 : Real.Gamma (a + ((k + 2 : ℕ) : ℝ)) =
      (a + k + 1) * ((a + k) * Real.Gamma (a + k)) := by
    rw [show a + ((k + 2 : ℕ) : ℝ) = (a + k + 1) + 1 by push_cast; ring,
      Real.Gamma_add_one (by positivity), Real.Gamma_add_one h1.ne']
  simp only [solution]
  rw [hG1, hG2, h, ← hk]
  ring

/-- `W_k > 0` for `0 ≤ x < 1`. -/
theorem solution_pos {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (k : ℕ) : 0 < solution a b x k :=
  mul_pos (Real.Gamma_pos_of_pos (by positivity))
    (GaussContinuedFraction.realSum_pos (by positivity) (by positivity) (by positivity) hx0 hx1)

/-- The real regularized series with second parameter zero is `1/Γ(γ)`. -/
theorem realSum_zero_right (α γ x : ℝ) :
    GaussContinuedFraction.realSum α 0 γ x = (Real.Gamma γ)⁻¹ := by
  rw [GaussContinuedFraction.realSum, tsum_eq_single 0]
  · simp [GaussContinuedFraction.term]
  · intro n hn
    simp [GaussContinuedFraction.term, hn]

/-- `W₀ = 1`. -/
theorem solution_zero (a b x : ℝ) (ha : 0 < a) : solution a b x 0 = 1 := by
  simp only [solution, GaussContinuedFraction.backwardSolutionReal, Nat.zero_div,
    CharP.cast_eq_zero, add_zero, zero_add, Nat.reduceDiv, realSum_zero_right]
  exact mul_inv_cancel₀ (Real.Gamma_pos_of_pos ha).ne'

/-- `W_{2m+1} ≤ (a+2m)/m · W_{2m}` for `m ≥ 1`. -/
theorem solution_odd_le {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx0 : 0 ≤ x) (hx1 : x < 1)
    {m : ℕ} (hm : 1 ≤ m) :
    solution a b x (2 * m + 1) ≤ (a + 2 * m) / m * solution a b x (2 * m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h := GaussContinuedFraction.realSum_shift_le (α := a + b + m) (β := m) (γ := a + 2 * m)
    (x := x) (by positivity) hm0 (by linarith) hx0 hx1
  simp only [solution, GaussContinuedFraction.backwardSolutionReal,
    show (2 * m + 1) / 2 = m by omega, show (2 * m + 1 + 1) / 2 = m + 1 by omega,
    show 2 * m / 2 = m by omega]
  push_cast
  have hG : Real.Gamma (a + (2 * m + 1)) = (a + 2 * m) * Real.Gamma (a + 2 * m) := by
    rw [show a + (2 * (m:ℝ) + 1) = (a + 2 * m) + 1 by ring, Real.Gamma_add_one (by positivity)]
  rw [hG, show (0:ℝ) + m = m by ring, show (0:ℝ) + (m + 1) = m + 1 by ring,
    show a + (2 * (m:ℝ) + 1) = a + 2 * m + 1 by ring]
  have hGp : 0 < Real.Gamma (a + 2 * m) := Real.Gamma_pos_of_pos (by positivity)
  calc (a + 2 * m) * Real.Gamma (a + 2 * m) *
        GaussContinuedFraction.realSum (a + b + m) (m + 1) (a + 2 * m + 1) x
      ≤ (a + 2 * m) * Real.Gamma (a + 2 * m) *
        ((m:ℝ)⁻¹ * GaussContinuedFraction.realSum (a + b + m) m (a + 2 * m) x) := by
        gcongr
    _ = _ := by field_simp

/-- `W_{2m+2} ≤ (a+2m+1)/(a+b+m) · W_{2m+1}` for `b ≤ m + 1`. -/
theorem solution_even_le {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx0 : 0 ≤ x) (hx1 : x < 1)
    {m : ℕ} (hm : b ≤ m + 1) :
    solution a b x (2 * m + 2) ≤ (a + 2 * m + 1) / (a + b + m) * solution a b x (2 * m + 1) := by
  have h := GaussContinuedFraction.realSum_shift_le (α := m + 1) (β := a + b + m)
    (γ := a + 2 * m + 1) (x := x) (by positivity) (by positivity) (by linarith) hx0 hx1
  rw [GaussContinuedFraction.realSum_symm (m + 1), GaussContinuedFraction.realSum_symm (m + 1)]
    at h
  simp only [solution, GaussContinuedFraction.backwardSolutionReal,
    show (2 * m + 2) / 2 = m + 1 by omega, show (2 * m + 2 + 1) / 2 = m + 1 by omega,
    show (2 * m + 1) / 2 = m by omega]
  push_cast
  have hG : Real.Gamma (a + (2 * m + 2)) = (a + 2 * m + 1) * Real.Gamma (a + (2 * m + 1)) := by
    rw [show a + (2 * (m:ℝ) + 2) = (a + (2 * m + 1)) + 1 by ring,
      Real.Gamma_add_one (by positivity)]; ring
  rw [hG, show (0:ℝ) + (m + 1) = m + 1 by ring, show a + b + ((m:ℝ) + 1) = a + b + m + 1 by ring,
    show a + (2 * (m:ℝ) + 2) = a + 2 * m + 1 + 1 by ring,
    show a + (2 * (m:ℝ) + 1) = a + 2 * m + 1 by ring]
  have hGp : 0 < Real.Gamma (a + 2 * m + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hab : 0 < a + b + m := by positivity
  calc (a + 2 * m + 1) * Real.Gamma (a + 2 * m + 1) *
        GaussContinuedFraction.realSum (a + b + m + 1) (m + 1) (a + 2 * m + 1 + 1) x
      ≤ (a + 2 * m + 1) * Real.Gamma (a + 2 * m + 1) *
        ((a + b + m)⁻¹ * GaussContinuedFraction.realSum (a + b + m) (m + 1) (a + 2 * m + 1) x) := by
        gcongr
    _ = _ := by field_simp


/-- A real sequence converges if its even and odd subsequences converge to the same limit. -/
private theorem tendsto_of_even_odd {f : ℕ → ℝ} {L : ℝ}
    (h0 : Tendsto (fun m => f (2 * m)) atTop (𝓝 L))
    (h1 : Tendsto (fun m => f (2 * m + 1)) atTop (𝓝 L)) : Tendsto f atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at h0 h1 ⊢
  intro ε hε
  obtain ⟨N0, hN0⟩ := h0 ε hε
  obtain ⟨N1, hN1⟩ := h1 ε hε
  refine ⟨2 * (N0 + N1), fun n hn => ?_⟩
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact hN0 k (by omega)
  · exact hN1 k (by omega)

/-- `d_k → -x/4`. -/
theorem tendsto_partialNumerator {a : ℝ} (ha : 0 < a) (b x : ℝ) :
    Tendsto (partialNumerator a b x) atTop (𝓝 (-x/4)) := by
  have hu := tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine tendsto_of_even_odd ?_ ?_
  · have hf : Tendsto (fun u : ℝ => x * (b * u - 1) / ((a * u + 2 - u) * (a * u + 2))) (𝓝 0)
        (𝓝 (-x/4)) := by
      have : ContinuousAt (fun u : ℝ => x * (b * u - 1) / ((a * u + 2 - u) * (a * u + 2))) 0 := by
        refine ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
      convert this.tendsto using 2; norm_num
    refine (hf.comp hu).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (0:ℝ) < m := by exact_mod_cast hm
    have he : Even (2 * m) := ⟨m, by ring⟩
    simp only [Function.comp_apply, partialNumerator, he, ↓reduceIte, show 2 * m / 2 = m by omega]
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
    have h1 : a + 2 * (m:ℝ) - 1 ≠ 0 := by intro h; linarith
    have h2 : a * (m:ℝ)⁻¹ + 2 - (m:ℝ)⁻¹ ≠ 0 := by
      intro h
      have : (a * (m:ℝ)⁻¹ + 2 - (m:ℝ)⁻¹) * m = a + 2 * m - 1 := by field_simp
      rw [h, zero_mul] at this; exact h1 this.symm
    field_simp
  · have hf : Tendsto (fun u : ℝ => -(a * u + 1) * (a * u + b * u + 1) * x /
        ((a * u + 2) * (a * u + 2 + u))) (𝓝 0) (𝓝 (-x/4)) := by
      have : ContinuousAt (fun u : ℝ => -(a * u + 1) * (a * u + b * u + 1) * x /
          ((a * u + 2) * (a * u + 2 + u))) 0 := by
        refine ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
      convert this.tendsto using 2; norm_num
    refine (hf.comp hu).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (0:ℝ) < m := by exact_mod_cast hm
    have he : ¬ Even (2 * m + 1) := by simp
    simp only [Function.comp_apply, partialNumerator, he, ↓reduceIte,
      show (2 * m + 1 - 1) / 2 = m by omega]
    field_simp


/-- For every `λ > 2`, eventually `W_{k+1} ≤ λ W_k`. -/
theorem eventually_solution_succ_le {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx0 : 0 ≤ x)
    (hx1 : x < 1) {l : ℝ} (hl : 2 < l) :
    ∀ᶠ k in atTop, solution a b x (k + 1) ≤ l * solution a b x k := by
  obtain ⟨M, hM⟩ := exists_nat_ge (max (max 1 b) (max (a / (l - 2)) (1 / (l - 2))))
  have hl2 : 0 < l - 2 := by linarith
  have hM1 : (1:ℝ) ≤ M := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hM)
  have hMb : b ≤ M := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hM)
  have hMa : a / (l - 2) ≤ M := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hM)
  have hMo : 1 / (l - 2) ≤ M := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hM)
  filter_upwards [eventually_ge_atTop (2 * M)] with k hk
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · have hmM : (M:ℝ) ≤ m := by exact_mod_cast (show M ≤ m by omega)
    have hm1 : 1 ≤ m := by exact_mod_cast hM1.trans hmM
    have hm0 : (0:ℝ) < m := by linarith
    refine (solution_odd_le ha hb hx0 hx1 hm1).trans
      (mul_le_mul_of_nonneg_right ?_ (solution_pos ha hb hx0 hx1 _).le)
    rw [div_le_iff₀ hm0]
    have : a ≤ (l - 2) * m := by
      rw [div_le_iff₀ hl2] at hMa; nlinarith
    nlinarith
  · have hmM : (M:ℝ) ≤ m := by exact_mod_cast (show M ≤ m by omega)
    have hm1 : b ≤ m + 1 := by linarith
    have hpos : 0 < a + b + m := by positivity
    refine (show solution a b x (2 * m + 1 + 1) ≤ _ from
      solution_even_le ha hb hx0 hx1 hm1).trans
      (mul_le_mul_of_nonneg_right ?_ (solution_pos ha hb hx0 hx1 _).le)
    rw [div_le_iff₀ hpos]
    have : 1 ≤ (l - 2) * m := by
      rw [div_le_iff₀ hl2] at hMo; nlinarith
    nlinarith

/-- **Perron**: the ratios `W_{k+1}/W_k` tend to the smaller root `2/(1+√(1-x))`. -/
theorem tendsto_solution_ratio {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx0 : 0 < x)
    (hx1 : x < 1) :
    Tendsto (fun p => solution a b x (p + 1) / solution a b x p) atTop
      (𝓝 (2 / (1 + Real.sqrt (1 - x)))) := by
  set s := Real.sqrt (1 - x) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs2 : s ^ 2 = 1 - x := Real.sq_sqrt (by linarith)
  have hs1 : s < 1 := by nlinarith
  set l : ℝ := 2 / (1 - s / 2) with hl
  have hl0 : 0 < 1 - s / 2 := by linarith
  have hl2 : 2 < l := by rw [hl, lt_div_iff₀ hl0]; linarith
  have hlpos : 0 < l := by linarith
  set W := solution a b x with hW
  have hWpos : ∀ k, 0 < W k := solution_pos ha hb hx0.le hx1
  set y : ℕ → ℝ := fun p => W p / l ^ p with hy
  have hypos : ∀ p, 0 < y p := fun p => div_pos (hWpos p) (pow_pos hlpos p)
  -- boundedness of `y`
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_solution_succ_le ha hb hx0.le hx1 hl2)
  have hmono : ∀ j, y (K + j) ≤ y K := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      refine le_trans ?_ ih
      simp only [hy]
      rw [show K + (j + 1) = K + j + 1 by ring, pow_succ, div_le_div_iff₀ (by positivity)
        (by positivity)]
      have := hK (K + j) (by omega)
      have hp : 0 < l ^ (K + j) := pow_pos hlpos _
      nlinarith [hWpos (K + j)]
  set C := ∑ j ∈ Finset.range (K + 1), y j with hC
  have hbdd : ∀ p, ‖y p‖ ≤ C := by
    intro p
    rw [Real.norm_eq_abs, abs_of_pos (hypos p)]
    have hle : ∀ q ≤ K, y q ≤ C := fun q hq =>
      Finset.single_le_sum (fun j _ => (hypos j).le) (Finset.mem_range.mpr (by omega))
    rcases le_or_gt p K with h | h
    · exact hle p h
    · obtain ⟨j, rfl⟩ : ∃ j, p = K + j := ⟨p - K, by omega⟩
      exact (hmono j).trans (hle K le_rfl)
  -- the limits of the coefficients
  have hnum := (tendsto_partialNumerator ha b x).comp (tendsto_add_atTop_nat 1)
  have hx4 : -x / 4 ≠ 0 := by intro h; linarith
  set ρ₁ : ℝ := 2 / (1 + s) / l with hρ₁
  set ρ₂ : ℝ := 2 / (1 - s) / l with hρ₂
  have h1s : 0 < 1 - s := by linarith
  have hρ : ‖ρ₁‖ < ‖ρ₂‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos (by positivity)]
    rw [hρ₁, hρ₂]
    gcongr
    linarith
  have hρ2 : 1 < ‖ρ₂‖ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), hρ₂, hl]
    rw [div_div_eq_mul_div, lt_div_iff₀ (by positivity)]
    field_simp
    nlinarith
  have key := tendsto_succ_div_of_three_term_recurrence_of_bounded (𝕜 := ℝ) (x := y)
    (α := fun p => partialNumerator a b x (p + 1) * l ^ 2) (β := fun _ => l) (γ := fun _ => -1)
    hρ hρ2 ?hα ?hβ ?hγ ?hrec hbdd (Frequently.of_forall fun p => (hypos p).ne')
  case hα =>
    filter_upwards [hnum.eventually_ne hx4] with p hp
    exact mul_ne_zero hp (by positivity)
  case hβ =>
    have h := (tendsto_const_nhds (x := l)).div (hnum.mul_const (l ^ 2))
      (mul_ne_zero hx4 (by positivity))
    have hval : l / (-x / 4 * l ^ 2) = -(ρ₁ + ρ₂) := by
      rw [hρ₁, hρ₂]
      have hx : x = 1 - s ^ 2 := by linarith
      have h1 : (1 - s ^ 2) ≠ 0 := by nlinarith
      have h2 : (1 + s) ≠ 0 := by linarith
      have h3 : (1 - s) ≠ 0 := by linarith
      rw [hx]
      field_simp
      ring
    rw [hval] at h
    exact h
  case hγ =>
    have h := (tendsto_const_nhds (x := (-1 : ℝ))).div (hnum.mul_const (l ^ 2))
      (mul_ne_zero hx4 (by positivity))
    have hval : -1 / (-x / 4 * l ^ 2) = ρ₁ * ρ₂ := by
      rw [hρ₁, hρ₂]
      have hx : x = 1 - s ^ 2 := by linarith
      have h1 : (1 - s ^ 2) ≠ 0 := by nlinarith
      have h2 : (1 + s) ≠ 0 := by linarith
      have h3 : (1 - s) ≠ 0 := by linarith
      rw [hx]
      field_simp
      ring
    rw [hval] at h
    exact h
  case hrec =>
    refine Eventually.of_forall fun p => ?_
    have hr := solution_rec (b := b) ha (show |x| < 1 by rw [abs_of_pos hx0]; exact hx1) p
    simp only [hy]
    rw [pow_succ, pow_succ, pow_succ]
    field_simp
    rw [← hW] at hr
    linear_combination (-(l ^ p * l * l)) * hr
  have h2 := key.const_mul l
  convert h2 using 1
  · funext p
    simp only [hy]
    rw [pow_succ]
    field_simp [(hWpos p).ne']
  · rw [hρ₁]; field_simp


/-- Continuants of `continuedFractionContinuants` agree with Mathlib's while no partial numerator
vanishes. -/
private theorem continuedFractionContinuants_eq_of_lt {a b : ℕ → ℂ} {n : ℕ}
    (ha : ∀ k, 1 ≤ k → k < n → a k ≠ 0) :
    DLMF.Core.continuedFractionContinuants a b 0 n =
      ((GenContFract.ofFun 0 a b).nums n, (GenContFract.ofFun 0 a b).dens n, false) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [DLMF.Core.continuedFractionContinuants]; rfl
    · simp [DLMF.Core.continuedFractionContinuants, GenContFract.ofFun_nums_one,
          GenContFract.ofFun_dens_one]
    · have h1 := ih (n + 1) (by omega) fun k hk hkn => ha k hk (by omega)
      have h0 := ih n (by omega) fun k hk hkn => ha k hk (by omega)
      have han : a (n + 1) ≠ 0 := ha (n + 1) (by omega) (by omega)
      rw [DLMF.Core.continuedFractionContinuants, h1, h0, GenContFract.ofFun_nums_add_two,
        GenContFract.ofFun_dens_add_two]
      simp [han, GenContFract.nextConts, GenContFract.nextNum, GenContFract.nextDen]

/-- After the first vanishing partial numerator `a_K` the continuants freeze. -/
private theorem continuedFractionContinuants_freeze {a b : ℕ → ℂ} {K : ℕ} (hK : 1 ≤ K)
    (ha : ∀ k, 1 ≤ k → k < K → a k ≠ 0) (hK0 : a K = 0) (j : ℕ) :
    DLMF.Core.continuedFractionContinuants a b 0 (K + 1 + j) =
      ((GenContFract.ofFun 0 a b).nums K, (GenContFract.ofFun 0 a b).dens K, true) := by
  induction j with
  | zero =>
    obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
    rw [show n + 1 + 1 + 0 = n + 2 by ring, DLMF.Core.continuedFractionContinuants,
      continuedFractionContinuants_eq_of_lt ha]
    simp [hK0]
  | succ j ih =>
    rw [show K + 1 + (j + 1) = (K + j) + 2 by ring, DLMF.Core.continuedFractionContinuants,
      show K + j + 1 = K + 1 + j by ring, ih]
    simp

/-- The partial numerators `1, d₁, d₂, …` of DLMF 8.17.22. -/
def fractionNumerator (a b x : ℝ) (k : ℕ) : ℝ := if k = 0 then 1 else partialNumerator a b x k

private theorem fullNumer_succ (a b x : ℝ) (k : ℕ) :
    fractionNumerator a b x (k + 1) = partialNumerator a b x (k + 1) := by
  simp [fractionNumerator]

private theorem solution_rec_full {a b x : ℝ} (ha : 0 < a) (hx : |x| < 1) (k : ℕ) :
    solution a b x k = 1 * solution a b x (k + 1) +
      fractionNumerator a b x (k + 1) * solution a b x (k + 2) := by
  rw [fullNumer_succ, one_mul]; exact solution_rec ha hx k

/-- **DLMF 8.17.22, continued-fraction part**: the finite values of
`1/(1 + d₁/(1 + d₂/(1 + ⋯)))` tend to `W₁ = F(a+b, 1; a+1; x)`. -/
theorem tendsto_continuedFractionTail {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx0 : 0 ≤ x)
    (hx1 : x < 1) :
    Tendsto (DLMF.Core.continuedFractionTail (fun k => ((fractionNumerator a b x k : ℝ) : ℂ))
        (fun _ => 1) 0) atTop
      (𝓝 ((solution a b x 1 : ℝ) : ℂ)) := by
  have hxa : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  set A : ℕ → ℝ := fractionNumerator a b x with hA
  set W := solution a b x with hW
  have hWpos : ∀ k, 0 < W k := solution_pos ha hb hx0 hx1
  have hW0 : W 0 = 1 := solution_zero a b x ha
  have hA0 : A 0 = 1 := by simp [hA, fractionNumerator]
  have hrec : ∀ k, W k = 1 * W (k + 1) + A (k + 1) * W (k + 2) := solution_rec_full ha hxa
  by_cases hz : ∃ K, 1 ≤ K ∧ A K = 0
  · -- terminating case
    classical
    let K := Nat.find hz
    have hKspec : 1 ≤ K ∧ A K = 0 := Nat.find_spec hz
    have hlt : ∀ k, 1 ≤ k → k < K → ((A k : ℝ) : ℂ) ≠ 0 := by
      intro k hk hkK h0
      exact Nat.find_min hz hkK ⟨hk, by exact_mod_cast h0⟩
    have hK0 : ((A K : ℝ) : ℂ) = 0 := by rw [hKspec.2]; simp
    set g := GenContFract.ofFun (0 : ℂ) (fun k => ((A k : ℝ) : ℂ)) (fun _ => 1) with hg
    have hwC : ∀ k, ((W k : ℝ) : ℂ) = 1 * (W (k + 1) : ℂ) +
        ((A (k + 1) : ℝ) : ℂ) * (W (k + 2) : ℂ) := fun k => by
      rw [hrec k]; push_cast; ring
    obtain ⟨n, hn⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
    have inv := GenContFract.ofFun_backward_invariant (h := (0 : ℂ))
      (a := fun k => ((A k : ℝ) : ℂ)) (b := fun _ => (1 : ℂ)) hwC n
    rw [← hn, ← hg] at inv
    simp only [hK0, zero_mul, add_zero, hA0, hW0] at inv
    push_cast at inv
    have hval : g.nums K / g.dens K = ((W 1 : ℝ) : ℂ) := by
      have hd : g.dens K ≠ 0 := by
        intro h; rw [h, zero_mul] at inv; exact one_ne_zero inv.2.symm
      have hWK : ((W K : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hWpos K).ne'
      rw [div_eq_iff hd]
      linear_combination (g.dens K) * inv.1 - (g.nums K) * inv.2
    refine tendsto_atTop_of_eventually_const (i₀ := K + 1) fun N hN => ?_
    obtain ⟨j, rfl⟩ : ∃ j, N = K + 1 + j := ⟨N - (K + 1), by omega⟩
    simp only [DLMF.Core.continuedFractionTail]
    rw [continuedFractionContinuants_freeze hKspec.1 hlt hK0 j]
    exact hval
  · -- non-terminating case
    push Not at hz
    have hx0' : 0 < x := by
      rcases hx0.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hz 1 le_rfl
        simp [hA, fractionNumerator, partialNumerator, ← h]
    have hAne : ∀ k, A k ≠ 0 := by
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [hA0]; exact one_ne_zero
      · exact hz k hk
    have hcf : ∀ N, DLMF.Core.continuedFractionTail (fun k => ((A k : ℝ) : ℂ)) (fun _ => 1) 0 N =
        (((GenContFract.ofFun (0 : ℝ) A (fun _ => 1)).convs N : ℝ) : ℂ) := by
      intro N
      simp only [DLMF.Core.continuedFractionTail]
      rw [continuedFractionContinuants_eq_of_lt fun k hk _ => by exact_mod_cast hAne k]
      have hm := GenContFract.ofFun_convs_map (h := (0 : ℝ)) (a := A) (b := fun _ => (1 : ℝ))
        Complex.ofRealHom N
      exact hm
    rw [funext hcf]
    -- eventual bounds
    have hneg : ∀ᶠ k in atTop, A (k + 1) < 0 := by
      have ht := (tendsto_partialNumerator ha b x).comp (tendsto_add_atTop_nat 1)
      filter_upwards [ht.eventually (gt_mem_nhds (show -x / 4 < 0 by linarith))] with k hk
      rw [hA, fullNumer_succ]; exact hk
    have hratio : ∀ᶠ k in atTop, W (k + 1) < 2 * W k := by
      have ht := tendsto_solution_ratio ha hb hx0' hx1
      have hlt2 : 2 / (1 + Real.sqrt (1 - x)) < 2 := by
        have : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.mpr (by linarith)
        rw [div_lt_iff₀ (by linarith)]; linarith
      filter_upwards [ht.eventually (gt_mem_nhds hlt2)] with k hk
      rwa [div_lt_iff₀ (hWpos k)] at hk
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hneg.and hratio)
    have key := GenContFract.tendsto_ofFun_convs_of_ratio_real (h := (0 : ℝ)) (a := A)
      (b := fun _ => (1 : ℝ)) (w := W) hrec (by rw [hW0]; exact one_ne_zero) hAne (N := N)
      (fun k _ => (hWpos k).ne')
      (fun k hk => mul_neg_of_pos_of_neg (hWpos k)
        (mul_neg_of_neg_of_pos (hN k hk).1 (hWpos _)))
      (fun k hk => by
        have h1 := hrec k
        have h2 := (hN k hk).2
        have h3 : A (k + 1) * W (k + 2) < 0 := mul_neg_of_neg_of_pos (hN k hk).1 (hWpos _)
        rw [abs_of_neg h3, abs_of_pos (hWpos k)]
        linarith)
    rw [hA0, hW0, zero_add, one_mul, div_one] at key
    exact (Complex.continuous_ofReal.tendsto _).comp key

end IncompleteBetaFraction
end DLMF.Confluent
