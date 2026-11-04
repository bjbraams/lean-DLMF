/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.FourierSeries.EigenfunctionSeries

/-!
# The continued-fraction equation for Lamé eigenvalues (DLMF 29.3.10)

For non-integer `ν`, the eigenvalues `H = 2a^m_ν(k²) - ν(ν+1)k²` and `H = 2b^m_ν(k²) - ν(ν+1)k²`
satisfy the continued-fraction equation 29.3.10 with the coefficients of §29.3(iii). The
Fourier coefficients of the eigenfunction solve the corresponding three-term recurrence, are
nonzero at the start and have ratios tending to `k²/(1+k')² < 1` (DLMF 29.6.7 and its
analogues), so they form the minimal solution; the left side of 29.3.10 equals
`-α_p c_{p+1}/c_p` by induction, and the right side converges to the same value by
Pincherle's theorem `tendsto_nestedFraction_of_minimal`.

## Main results

* `LameRecurrence.tendsto_lameContinuedFractionRight_of_minimal`: the continued-fraction equation
  29.3.10 for a solution of the recurrence with ratios tending to `k²/(1+k')²`.
* `Real.lameCF_A0`, `Real.lameCF_A1`, `Real.lameCF_B1`, `Real.lameCF_B2`: the
  continued-fraction equation 29.3.10 for the four eigenvalue families.
-/

@[expose] public section

open Filter Set DLMF.Elliptic

open scoped Real Topology

noncomputable section

namespace DLMF.Lame

variable {ν k : ℝ}

/-- For non-integer `ν` and `k ≠ 0` the coefficient `α_q` of a Lamé recurrence never
vanishes. -/
theorem LameRecurrence.alpha_ne_zero (r : LameRecurrence) (hνZ : ∀ j : ℤ, ν ≠ j) (hk : k ≠ 0)
    (q : ℕ) : r.alpha ν k q ≠ 0 := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  cases r <;> simp only [LameRecurrence.alpha] <;> (try split_ifs) <;>
    simp only [ne_eq, mul_eq_zero, div_eq_zero_iff, pow_eq_zero_iff two_ne_zero, not_or,
      hk, h2, or_false] <;>
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    first
    | exact hνZ (2 * q + 1) (by push_cast; linarith)
    | exact hνZ (2 * q + 2) (by push_cast; linarith)
    | exact hνZ (2 * q + 3) (by push_cast; linarith)
    | exact hνZ (2 * q) (by push_cast; linarith)
    | exact hνZ (-(2 * q + 2)) (by push_cast; linarith)
    | exact hνZ (-(2 * q + 3)) (by push_cast; linarith)
    | exact hνZ (-(2 * q + 4)) (by push_cast; linarith)
    | exact hνZ (-(2 * q + 1)) (by push_cast; linarith)
    | exact hνZ 1 (by push_cast; linarith)
    | exact hνZ (-2) (by push_cast; linarith)
    | exact hνZ 0 (by push_cast; linarith)
    | exact hνZ (-1) (by push_cast; linarith)

/-- For non-integer `ν` and `k ≠ 0` the coefficient `γ_{q+1}` of a Lamé recurrence never
vanishes. -/
theorem LameRecurrence.gamma_succ_ne_zero (r : LameRecurrence) (hνZ : ∀ j : ℤ, ν ≠ j)
    (hk : k ≠ 0) (q : ℕ) : r.gamma ν k (q + 1) ≠ 0 := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  cases r <;> simp only [LameRecurrence.gamma] <;>
    simp only [ne_eq, mul_eq_zero, div_eq_zero_iff, pow_eq_zero_iff two_ne_zero, not_or,
      hk, h2, or_false] <;>
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> push_cast at h <;>
    first
    | exact hνZ (2 * q) (by push_cast; linarith)
    | exact hνZ (2 * q + 1) (by push_cast; linarith)
    | exact hνZ (2 * q + 2) (by push_cast; linarith)
    | exact hνZ (2 * q + 3) (by push_cast; linarith)
    | exact hνZ (-(2 * q + 1)) (by push_cast; linarith)
    | exact hνZ (-(2 * q + 2)) (by push_cast; linarith)
    | exact hνZ (-(2 * q + 3)) (by push_cast; linarith)
    | exact hνZ (-(2 * q + 4)) (by push_cast; linarith)

/-- **The continued-fraction equation 29.3.10** for a solution `c` of the Lamé recurrence `r`
with eigenparameter `H` whose ratios tend to `k²/(1+k')²`, for non-integer `ν`: if `c` is not
identically zero and the left side has nonvanishing denominators, the truncations of the right
side converge to the left side. -/
theorem LameRecurrence.tendsto_lameContinuedFractionRight_of_minimal (r : LameRecurrence)
    (hνZ : ∀ j : ℤ, ν ≠ j) (hk0 : 0 < k) (hk1 : k < 1) {H : ℝ} {c : ℕ → ℝ}
    (hrec0 : (r.beta ν k 0 - H) * c 0 + r.alpha ν k 0 * c 1 = 0)
    (hrec : ∀ p : ℕ, 1 ≤ p → r.gamma ν k p * c (p - 1) + (r.beta ν k p - H) * c p +
      r.alpha ν k p * c (p + 1) = 0)
    (hratio : Tendsto (fun p => c (p + 1) / c p) atTop
      (𝓝 (k ^ 2 / (1 + Real.sqrt (1 - k ^ 2)) ^ 2)))
    (hnz : ∃ p, c p ≠ 0) (p : ℕ) (hden : ∀ q < p, lameContinuedFractionLeft r ν k H q ≠ 0) :
    Tendsto (lameContinuedFractionRight r ν k H p) atTop
        (𝓝 (lameContinuedFractionLeft r ν k H p)) := by
  have hk := hk0.ne'
  have hα := r.alpha_ne_zero hνZ hk
  have hγ := r.gamma_succ_ne_zero hνZ hk
  have hf : ∀ q, r.gamma ν k (q + 1) * c q + (r.beta ν k (q + 1) - H) * c (q + 1) +
      r.alpha ν k (q + 1) * c (q + 2) = 0 := fun q => by
    simpa using hrec (q + 1) (by omega)
  -- `c₀ ≠ 0`
  have hc0 : c 0 ≠ 0 := by
    intro h0
    have h1 : c 1 = 0 := by
      rw [h0, mul_zero, zero_add] at hrec0
      exact (mul_eq_zero.1 hrec0).resolve_left (hα 0)
    have hall : ∀ n, c n = 0 ∧ c (n + 1) = 0 := by
      intro n
      induction n with
      | zero => exact ⟨h0, h1⟩
      | succ n ih =>
        refine ⟨ih.2, ?_⟩
        have := hf n
        rw [ih.1, ih.2, mul_zero, mul_zero, zero_add, zero_add] at this
        exact (mul_eq_zero.1 this).resolve_left (hα (n + 1))
    obtain ⟨n, hn⟩ := hnz
    exact hn (hall n).1
  -- the left side is `-α_q c_{q+1}/c_q`
  have hleft : ∀ q ≤ p, c q ≠ 0 ∧ lameContinuedFractionLeft r ν k H q = -r.alpha ν k q *
      c (q + 1) / c q := by
    intro q hq
    induction q with
    | zero =>
      refine ⟨hc0, ?_⟩
      simp only [lameContinuedFractionLeft]
      field_simp
      linear_combination hrec0
    | succ q ih =>
      obtain ⟨hcq, hL⟩ := ih (by omega)
      have hcq1 : c (q + 1) ≠ 0 := by
        intro h0
        apply hden q (by omega)
        rw [hL, h0, mul_zero, zero_div]
      refine ⟨hcq1, ?_⟩
      have hαq := hα q
      rw [lameContinuedFractionLeft, hL]
      field_simp
      linear_combination hf q
  -- the limit `ρ = k²/(1+k')²` lies in `(0, 1)`
  have hs0 : 0 ≤ Real.sqrt (1 - k ^ 2) := Real.sqrt_nonneg _
  have hρ0 : 0 < k ^ 2 / (1 + Real.sqrt (1 - k ^ 2)) ^ 2 := by positivity
  have hρ1 : k ^ 2 / (1 + Real.sqrt (1 - k ^ 2)) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have := tendsto_nestedFraction_of_minimal (R := lameContinuedFractionRight r ν k H)
    (β := fun q => r.beta ν k q - H) (fun q => rfl) (fun q d => rfl) hα hγ hf hc0 hρ0 hρ1
    hratio (r.tendsto_gamma_div_alpha ν k hk) (hleft p le_rfl).1
  rwa [(hleft p le_rfl).2]

/-- 29.3.9–29.3.12: `H = 2a^{2m}_ν(k²) - ν(ν+1)k²` satisfies the continued-fraction equation
29.3.10 with the coefficients 29.3.11–29.3.12 (`LameRecurrence.A0`), for every `p`: the
truncations of the right side converge to the (finite) left side. Stated for non-integer `ν`
and nonvanishing denominators on the left (DLMF's genericity assumption; for integer `ν` see
`Real.lameCF_A0_terminating`). -/
@[dlmf 29.3.E9, dlmf 29.3.E10]
theorem Real.lameCF_A0 (hν : -1 / 2 ≤ ν) (hνZ : ∀ j : ℤ, ν ≠ j) (hk0 : 0 < k) (hk1 : k < 1)
    (m p : ℕ)
    (hden : ∀ q < p,
      lameContinuedFractionLeft .A0 ν k (2 * Real.lameA ν (2 * m) k - ν * (ν + 1) * k ^ 2) q ≠ 0) :
    Tendsto (lameContinuedFractionRight .A0 ν k
        (2 * Real.lameA ν (2 * m) k - ν * (ν + 1) * k ^ 2) p) atTop
      (𝓝 (lameContinuedFractionLeft .A0 ν k
          (2 * Real.lameA ν (2 * m) k - ν * (ν + 1) * k ^ 2) p)) := by
  have h0 := Real.lameEc_even_fourierA_rec_zero (ν := ν) hk0 hk1 m
  have h1 := Real.lameEc_even_fourierA_rec (ν := ν) hk0 hk1 m
  have hr := Real.lameEc_even_fourierA_ratio (ν := ν) hν hk0 hk1 m
    (fun n hn => (hνZ (2 * n) (by rw [hn]; push_cast; ring)).elim)
  have hnz : ∃ q, Real.lameCosCoeff (fun x => Real.lameEc ν (2 * m) x k) k true (2 * q) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨S, hS, hSpos⟩ := Real.lameEc_even_fourierA_pos (ν := ν) hk0 hk1 m
    exact hSpos.ne' (hS.unique (by simp [h]))
  exact LameRecurrence.tendsto_lameContinuedFractionRight_of_minimal .A0 hνZ hk0 hk1 h0
      h1 hr hnz p hden

/-- §29.3(iii): `H = 2a^{2m+1}_ν(k²) - ν(ν+1)k²` satisfies 29.3.10 with the coefficients
29.3.13–29.3.14 (`LameRecurrence.A1`); non-integer `ν`. -/
@[dlmf 29.3.E10, dlmf 29.3.iii]
theorem Real.lameCF_A1 (hν : -1 / 2 ≤ ν) (hνZ : ∀ j : ℤ, ν ≠ j) (hk0 : 0 < k) (hk1 : k < 1)
    (m p : ℕ)
    (hden : ∀ q < p,
      lameContinuedFractionLeft .A1 ν k
          (2 * Real.lameA ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2) q ≠ 0) :
    Tendsto (lameContinuedFractionRight .A1 ν k
        (2 * Real.lameA ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2) p)
      atTop
      (𝓝 (lameContinuedFractionLeft .A1 ν k
          (2 * Real.lameA ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2) p)) := by
  have h0 := Real.lameEc_odd_fourierA_rec_zero (ν := ν) hk0 hk1 m
  have h1 := Real.lameEc_odd_fourierA_rec (ν := ν) hk0 hk1 m
  have hr := Real.lameEc_odd_fourierA_ratio (ν := ν) hν hk0 hk1 m
    (fun n hn => (hνZ (2 * n + 1) (by rw [hn]; push_cast; ring)).elim)
  have hnz : ∃ q,
      Real.lameCosCoeff (fun x => Real.lameEc ν (2 * m + 1) x k) k true (2 * q + 1) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨S, hS, hSpos⟩ := Real.lameEc_odd_fourierA_pos (ν := ν) hk0 hk1 m
    exact hSpos.ne' (hS.unique (by simp [h]))
  exact LameRecurrence.tendsto_lameContinuedFractionRight_of_minimal .A1 hνZ hk0 hk1 h0
      h1 hr hnz p hden

/-- §29.3(iii): `H = 2b^{2m+1}_ν(k²) - ν(ν+1)k²` satisfies 29.3.10 with the coefficients
29.3.15–29.3.16 (`LameRecurrence.B1`); non-integer `ν`. -/
@[dlmf 29.3.E10, dlmf 29.3.iii]
theorem Real.lameCF_B1 (hν : -1 / 2 ≤ ν) (hνZ : ∀ j : ℤ, ν ≠ j) (hk0 : 0 < k) (hk1 : k < 1)
    (m p : ℕ)
    (hden : ∀ q < p,
      lameContinuedFractionLeft .B1 ν k
          (2 * Real.lameB ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2) q ≠ 0) :
    Tendsto (lameContinuedFractionRight .B1 ν k
        (2 * Real.lameB ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2) p)
      atTop
      (𝓝 (lameContinuedFractionLeft .B1 ν k
          (2 * Real.lameB ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2) p)) := by
  have h0 := Real.lameEs_odd_fourierB_rec_zero (ν := ν) hk0 hk1 m
  have h1 := Real.lameEs_odd_fourierB_rec (ν := ν) hk0 hk1 m
  have hr := Real.lameEs_odd_fourierB_ratio (ν := ν) hν hk0 hk1 m
    (fun n hn => (hνZ (2 * n + 1) (by rw [hn]; push_cast; ring)).elim)
  have hnz : ∃ q,
      Real.lameSinCoeff (fun x => Real.lameEs ν (2 * m + 1) x k) k true (2 * q + 1) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨S, hS, hSpos⟩ := Real.lameEs_odd_fourierB_pos (ν := ν) hk0 hk1 m
    exact hSpos.ne' (hS.unique (by simp [h]))
  exact LameRecurrence.tendsto_lameContinuedFractionRight_of_minimal .B1 hνZ hk0 hk1 h0
      h1 hr hnz p hden

/-- §29.3(iii): `H = 2b^{2m+2}_ν(k²) - ν(ν+1)k²` satisfies 29.3.10 with the coefficients
29.3.17 (`LameRecurrence.B2`); non-integer `ν`. -/
@[dlmf 29.3.E10, dlmf 29.3.iii]
theorem Real.lameCF_B2 (hν : -1 / 2 ≤ ν) (hνZ : ∀ j : ℤ, ν ≠ j) (hk0 : 0 < k) (hk1 : k < 1)
    (m p : ℕ)
    (hden : ∀ q < p,
      lameContinuedFractionLeft .B2 ν k
          (2 * Real.lameB ν (2 * m + 2) k - ν * (ν + 1) * k ^ 2) q ≠ 0) :
    Tendsto (lameContinuedFractionRight .B2 ν k
        (2 * Real.lameB ν (2 * m + 2) k - ν * (ν + 1) * k ^ 2) p)
      atTop
      (𝓝 (lameContinuedFractionLeft .B2 ν k
          (2 * Real.lameB ν (2 * m + 2) k - ν * (ν + 1) * k ^ 2) p)) := by
  have h0 := Real.lameEs_even_fourierB_rec_zero (ν := ν) hk0 hk1 m
  have h1 := Real.lameEs_even_fourierB_rec (ν := ν) hk0 hk1 m
  have hr := Real.lameEs_even_fourierB_ratio (ν := ν) hν hk0 hk1 m
    (fun n hn => (hνZ (2 * n + 2) (by rw [hn]; push_cast; ring)).elim)
  have hnz : ∃ q,
      Real.lameSinCoeff (fun x => Real.lameEs ν (2 * m + 2) x k) k true (2 * q + 2) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨S, hS, hSpos⟩ := Real.lameEs_even_fourierB_pos (ν := ν) hk0 hk1 m
    exact hSpos.ne' (hS.unique (by simp [h]))
  exact LameRecurrence.tendsto_lameContinuedFractionRight_of_minimal .B2 hνZ hk0 hk1 h0
      h1 hr hnz p hden

end DLMF.Lame
