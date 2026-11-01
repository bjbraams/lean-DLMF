/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.FourierSeries
public import DLMF.Mathieu.SmallQJacobi

/-!
# The eigenvalues `a_n(q)`, `b_n(q)` near `q = 0`

The Fourier coefficients of `ce_n`, `se_n` solve the recurrences 28.4.5–28.4.8, which are
instances of the recurrences of `DLMF.Mathieu.SmallQJacobi`. Their maximum principle puts every
eigenvalue within `4|q|` of a square `k²` of the right parity. Together with the strict
ordering `a_m(q) < a_{m+1}(q)`, `b_m(q) < b_{m+1}(q)` (Sturm oscillation) and, for small `q`, a
sign change of the boundary functions `w_I'(π/2)`, `w_I(π/2)`, `w_II'(π/2)`, `w_II(π/2)` between
consecutive squares (from their explicit values at `q = 0`), this identifies the window of
`a_m(q)`: `|a_m(q) - m²| ≤ 4|q|` and `|b_m(q) - m²| ≤ 4|q|` for small `q`. In particular `a_m`,
`b_m` are continuous at `q = 0` (DLMF 28.2.23 and §28.6).

## Main results

* `solvesRecurrence_mathieuFourierA_even`, `solvesRecurrence_mathieuFourierA_odd`,
  `solvesRecurrence_mathieuFourierB_odd`, `solvesRecurrence_mathieuFourierB_even`: the
  recurrences 28.4.5–28.4.8 in `SolvesRecurrence` form.
* `tendsto_mathieuFourierA_even` and its companions: the Fourier coefficients tend to `0`.
* `eventually_abs_mathieuA_sub_sq_le`, `eventually_abs_mathieuB_sub_sq_le`: `|a_m(q) - m²|` and
  `|b_m(q) - m²|` are at most `4|q|` for small real `q`.
* `mathieuA_even_sub_isBigO_of_trial`, `mathieuA_odd_sub_isBigO_of_trial`,
  `mathieuB_odd_sub_isBigO_of_trial`, `mathieuB_even_sub_isBigO_of_trial`: the eigenvalue
  estimates from trial vectors for each of the recurrences 28.4.5–28.4.8.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

/-! ### The recurrences 28.4.5–28.4.8 as `SolvesRecurrence` -/

/-- The coefficients `A^{2n}_{2i}` satisfy the recurrence 28.4.5 in `SolvesRecurrence` form,
with diagonal `4i²` and `β = 2`. -/
theorem solvesRecurrence_mathieuFourierA_even (n : ℕ) (q : ℝ) :
    SolvesRecurrence (fun i => 4 * (i : ℂ) ^ 2) 2 q (mathieuA (2 * n) q)
      (fun i => mathieuFourierA (2 * n) (2 * i) q) := by
  intro i
  rcases i with _ | _ | j
  · have := mathieuFourierA_even_rec_zero n q
    simp only [recurrenceOperator, recurrenceLower]; push_cast
    linear_combination -this
  · have := mathieuFourierA_even_rec_one n q
    simp only [recurrenceOperator, recurrenceLower]; push_cast; norm_num
    linear_combination -this
  · have := mathieuFourierA_even_rec n q (m := j + 2) (by omega)
    simp only [recurrenceOperator, recurrenceLower]
    rw [show 2 * (j + 2) - 2 = 2 * (j + 1) by omega, show 2 * (j + 2) + 2 = 2 * (j + 2 + 1) by ring]
      at this
    push_cast at this ⊢
    linear_combination -this

/-- The coefficients `A^{2n+1}_{2i+1}` satisfy 28.4.6 in `SolvesRecurrence` form, with diagonal
`(2i+1)² + q δ_{i0}` and `β = 1`. -/
theorem solvesRecurrence_mathieuFourierA_odd (n : ℕ) (q : ℝ) :
    SolvesRecurrence (fun i => (2 * (i : ℂ) + 1) ^ 2 + if i = 0 then (q : ℂ) else 0) 1 q
      (mathieuA (2 * n + 1) q) (fun i => mathieuFourierA (2 * n + 1) (2 * i + 1) q) := by
  intro i
  rcases i with _ | j
  · have := mathieuFourierA_odd_rec_zero n q
    simp only [recurrenceOperator, recurrenceLower]; push_cast; norm_num
    linear_combination -this
  · have := mathieuFourierA_odd_rec n q (m := j + 1) (by omega)
    rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega,
      show 2 * (j + 1) + 3 = 2 * (j + 1 + 1) + 1 by ring]
      at this
    rcases j with _ | j
    · simp only [recurrenceOperator, recurrenceLower]; push_cast at this ⊢; norm_num at this ⊢
      linear_combination -this
    · simp only [recurrenceOperator, recurrenceLower]; push_cast at this ⊢; norm_num at this ⊢
      linear_combination -this

/-- The coefficients `B^{2n+1}_{2i+1}` satisfy 28.4.7 in `SolvesRecurrence` form, with diagonal
`(2i+1)² - q δ_{i0}` and `β = 1`. -/
theorem solvesRecurrence_mathieuFourierB_odd (n : ℕ) (q : ℝ) :
    SolvesRecurrence (fun i => (2 * (i : ℂ) + 1) ^ 2 - if i = 0 then (q : ℂ) else 0) 1 q
      (mathieuB (2 * n + 1) q) (fun i => mathieuFourierB (2 * n + 1) (2 * i + 1) q) := by
  intro i
  rcases i with _ | j
  · have := mathieuFourierB_odd_rec_zero n q
    simp only [recurrenceOperator, recurrenceLower]; push_cast; norm_num
    linear_combination -this
  · have := mathieuFourierB_odd_rec n q (m := j + 1) (by omega)
    rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega,
      show 2 * (j + 1) + 3 = 2 * (j + 1 + 1) + 1 by ring]
      at this
    rcases j with _ | j
    · simp only [recurrenceOperator, recurrenceLower]; push_cast at this ⊢; norm_num at this ⊢
      linear_combination -this
    · simp only [recurrenceOperator, recurrenceLower]; push_cast at this ⊢; norm_num at this ⊢
      linear_combination -this

/-- The coefficients `B^{2n+2}_{2i+2}` satisfy 28.4.8 in `SolvesRecurrence` form, with diagonal
`(2i+2)²` and `β = 1`. -/
theorem solvesRecurrence_mathieuFourierB_even (n : ℕ) (q : ℝ) :
    SolvesRecurrence (fun i => (2 * (i : ℂ) + 2) ^ 2) 1 q
      (mathieuB (2 * n + 2) q) (fun i => mathieuFourierB (2 * n + 2) (2 * i + 2) q) := by
  intro i
  rcases i with _ | j
  · have := mathieuFourierB_even_rec_zero n q
    simp only [recurrenceOperator, recurrenceLower]; push_cast; norm_num
    linear_combination -this
  · have := mathieuFourierB_even_rec n q (m := j + 2) (by omega)
    rw [show 2 * (j + 2) - 2 = 2 * j + 2 by omega,
      show 2 * (j + 2) + 2 = 2 * (j + 1 + 1) + 2 by ring,
      show 2 * (j + 2) = 2 * (j + 1) + 2 by ring] at this
    rcases j with _ | j
    · simp only [recurrenceOperator, recurrenceLower]; push_cast at this ⊢; norm_num at this ⊢
      linear_combination -this
    · simp only [recurrenceOperator, recurrenceLower]; push_cast at this ⊢
      linear_combination -this

/-- Some Fourier coefficient `A^n_m(q)` is nonzero (since `ce_n(0, q) > 0`). -/
private lemma exists_mathieuFourierA_ne_zero (n : ℕ) (q : ℝ) : ∃ m, mathieuFourierA n m q ≠ 0 := by
  by_contra h
  push Not at h
  have hs := hasSum_mathieuFourierA_mul_cos n q 0
  simp only [h, zero_mul] at hs
  have := hs.unique hasSum_zero
  rw [mathieuCe_zero, Complex.ofReal_eq_zero] at this
  exact (mathieuCeZero_pos n q).ne' this

/-- For `n ≥ 1`, some Fourier coefficient `B^n_m(q)` is nonzero (since `se_n'(0, q) > 0`). -/
private lemma exists_mathieuFourierB_ne_zero {n : ℕ} (hn : n ≠ 0) (q : ℝ) : ∃ m, mathieuFourierB n m q ≠ 0 := by
  by_contra h
  push Not at h
  have hs := (mathieuFourier_sign n q).2.1 hn
  simp only [h, mul_zero] at hs
  have := hs.unique hasSum_zero
  rw [deriv_mathieuSe_zero, Complex.ofReal_eq_zero] at this
  exact (mathieuSeDerivZero_pos n q).ne' this

/-- Some coefficient `A^{2n}_{2i}(q)` is nonzero. -/
theorem exists_mathieuFourierA_even_ne_zero (n : ℕ) (q : ℝ) : ∃ i, mathieuFourierA (2 * n) (2 * i) q ≠ 0 := by
  obtain ⟨m, hm⟩ := exists_mathieuFourierA_ne_zero (2 * n) q
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · exact ⟨j, hm⟩
  · exact absurd (mathieuFourierA_even_odd n j q) hm

/-- Some coefficient `A^{2n+1}_{2i+1}(q)` is nonzero. -/
theorem exists_mathieuFourierA_odd_ne_zero (n : ℕ) (q : ℝ) : ∃ i, mathieuFourierA (2 * n + 1) (2 * i + 1) q ≠ 0 := by
  obtain ⟨m, hm⟩ := exists_mathieuFourierA_ne_zero (2 * n + 1) q
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · exact absurd (mathieuFourierA_odd_even n j q) hm
  · exact ⟨j, hm⟩

/-- Some coefficient `B^{2n+1}_{2i+1}(q)` is nonzero. -/
theorem exists_mathieuFourierB_odd_ne_zero (n : ℕ) (q : ℝ) : ∃ i, mathieuFourierB (2 * n + 1) (2 * i + 1) q ≠ 0 := by
  obtain ⟨m, hm⟩ := exists_mathieuFourierB_ne_zero (n := 2 * n + 1) (by omega) q
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · exact absurd (mathieuFourierB_odd_even n j q) hm
  · exact ⟨j, hm⟩

/-- Some coefficient `B^{2n+2}_{2i+2}(q)` is nonzero. -/
theorem exists_mathieuFourierB_even_ne_zero (n : ℕ) (q : ℝ) : ∃ i, mathieuFourierB (2 * n + 2) (2 * i + 2) q ≠ 0 := by
  obtain ⟨m, hm⟩ := exists_mathieuFourierB_ne_zero (n := 2 * n + 2) (by omega) q
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · rcases j with _ | j
    · exact absurd (mathieuFourierB_zero_right _ q) hm
    · exact ⟨j, by rw [show 2 * j + 2 = 2 * (j + 1) by ring]; exact hm⟩
  · exact absurd (mathieuFourierB_even_odd n j q) hm

/-- A sequence with `|c_m| ≤ C e^{-m}` tends to `0` along any reindexing `f` with `i ≤ f i`. -/
private lemma tendsto_comp_of_norm_le_exp {c : ℕ → ℂ}
    (hc : ∃ C, 0 ≤ C ∧ ∀ m : ℕ, ‖c m‖ ≤ C * Real.exp (-(1 * m)))
    {f : ℕ → ℕ} (hf : ∀ i, i ≤ f i) : Tendsto (fun i => c (f i)) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := hc
  refine squeeze_zero_norm (fun i => ?_) ((Real.tendsto_exp_neg_atTop_nhds_zero.comp
    tendsto_natCast_atTop_atTop).const_mul C |>.trans_eq (by simp) : Tendsto
      (fun i : ℕ => C * Real.exp (-(i : ℝ))) atTop (𝓝 0))
  refine (hC (f i)).trans ?_
  simp only [Function.comp, one_mul]
  gcongr
  exact_mod_cast hf i

/-- `A^{2n}_{2i}(q) → 0` as `i → ∞`. -/
theorem tendsto_mathieuFourierA_even (n : ℕ) (q : ℝ) :
    Tendsto (fun i => mathieuFourierA (2 * n) (2 * i) q) atTop (𝓝 0) :=
  tendsto_comp_of_norm_le_exp (exists_norm_mathieuFourierA_le_exp _ q 1) (fun i => by omega)

/-- `A^{2n+1}_{2i+1}(q) → 0` as `i → ∞`. -/
theorem tendsto_mathieuFourierA_odd (n : ℕ) (q : ℝ) :
    Tendsto (fun i => mathieuFourierA (2 * n + 1) (2 * i + 1) q) atTop (𝓝 0) :=
  tendsto_comp_of_norm_le_exp (exists_norm_mathieuFourierA_le_exp _ q 1) (fun i => by omega)

/-- `B^{2n+1}_{2i+1}(q) → 0` as `i → ∞`. -/
theorem tendsto_mathieuFourierB_odd (n : ℕ) (q : ℝ) :
    Tendsto (fun i => mathieuFourierB (2 * n + 1) (2 * i + 1) q) atTop (𝓝 0) :=
  tendsto_comp_of_norm_le_exp (exists_norm_mathieuFourierB_le_exp (by omega) q 1) (fun i => by omega)

/-- `B^{2n+2}_{2i+2}(q) → 0` as `i → ∞`. -/
theorem tendsto_mathieuFourierB_even (n : ℕ) (q : ℝ) :
    Tendsto (fun i => mathieuFourierB (2 * n + 2) (2 * i + 2) q) atTop (𝓝 0) :=
  tendsto_comp_of_norm_le_exp (exists_norm_mathieuFourierB_le_exp (by omega) q 1) (fun i => by omega)

/-- For real `x, y`, `‖(x : ℂ) - y‖ = |x - y|`. -/
theorem norm_ofReal_sub_ofReal (x y : ℝ) : ‖(x : ℂ) - (y : ℂ)‖ = |x - y| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- **Window lemma** for `a_m(q)` (maximum principle for the Fourier coefficients): `a_m(q)`
lies within `4|q|` of `k²` for some `k ≡ m (mod 2)`. -/
private lemma exists_abs_mathieuA_sub_sq_le (m : ℕ) (q : ℝ) :
    ∃ k : ℕ, k % 2 = m % 2 ∧ |mathieuA m q - (k : ℝ) ^ 2| ≤ 4 * |q| := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨i, hi⟩ := exists_norm_sub_diag_le_of_solvesRecurrence (by norm_num) (solvesRecurrence_mathieuFourierA_even n q) (tendsto_mathieuFourierA_even n q) (exists_mathieuFourierA_even_ne_zero n q)
    refine ⟨2 * i, by omega, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs,
      show (4 * (i : ℂ) ^ 2) = (((2 * i : ℕ) : ℝ) ^ 2 : ℝ) by push_cast; ring,
      norm_ofReal_sub_ofReal] at hi
    linarith [abs_nonneg q]
  · obtain ⟨i, hi⟩ := exists_norm_sub_diag_le_of_solvesRecurrence (by norm_num) (solvesRecurrence_mathieuFourierA_odd n q) (tendsto_mathieuFourierA_odd n q) (exists_mathieuFourierA_odd_ne_zero n q)
    refine ⟨2 * i + 1, by omega, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs] at hi
    have e : ((2 * (i : ℂ) + 1) ^ 2 + if i = 0 then (q : ℂ) else 0) =
        ((((2 * i + 1 : ℕ) : ℝ) ^ 2 + if i = 0 then q else 0 : ℝ) : ℂ) := by
      split_ifs <;> push_cast <;> ring
    rw [e, norm_ofReal_sub_ofReal] at hi
    have : |(if i = 0 then q else 0)| ≤ |q| := by split_ifs <;> simp
    have h3 := abs_sub_abs_le_abs_sub (mathieuA (2 * n + 1) q - ((2 * i + 1 : ℕ) : ℝ) ^ 2)
      (if i = 0 then q else 0)
    rw [sub_sub] at h3
    linarith

/-- **Window lemma** for `b_m(q)`, `m ≥ 1`. -/
private lemma exists_abs_mathieuB_sub_sq_le {m : ℕ} (hm : m ≠ 0) (q : ℝ) :
    ∃ k : ℕ, k % 2 = m % 2 ∧ 1 ≤ k ∧ |mathieuB m q - (k : ℝ) ^ 2| ≤ 4 * |q| := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [show 2 * (n + 1) = 2 * n + 2 by ring]
    obtain ⟨i, hi⟩ := exists_norm_sub_diag_le_of_solvesRecurrence (by norm_num) (solvesRecurrence_mathieuFourierB_even n q) (tendsto_mathieuFourierB_even n q) (exists_mathieuFourierB_even_ne_zero n q)
    refine ⟨2 * i + 2, by omega, by omega, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs,
      show ((2 * (i : ℂ) + 2) ^ 2) = (((2 * i + 2 : ℕ) : ℝ) ^ 2 : ℝ) by push_cast; ring,
      norm_ofReal_sub_ofReal] at hi
    linarith [abs_nonneg q]
  · obtain ⟨i, hi⟩ := exists_norm_sub_diag_le_of_solvesRecurrence (by norm_num) (solvesRecurrence_mathieuFourierB_odd n q) (tendsto_mathieuFourierB_odd n q) (exists_mathieuFourierB_odd_ne_zero n q)
    refine ⟨2 * i + 1, by omega, by omega, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs] at hi
    have e : ((2 * (i : ℂ) + 1) ^ 2 - if i = 0 then (q : ℂ) else 0) =
        ((((2 * i + 1 : ℕ) : ℝ) ^ 2 - if i = 0 then q else 0 : ℝ) : ℂ) := by
      split_ifs <;> push_cast <;> ring
    rw [e, norm_ofReal_sub_ofReal] at hi
    have : |(if i = 0 then q else 0)| ≤ |q| := by split_ifs <;> simp
    have h3 := abs_sub_abs_le_abs_sub (mathieuB (2 * n + 1) q - ((2 * i + 1 : ℕ) : ℝ) ^ 2)
      (-(if i = 0 then q else 0))
    rw [abs_neg, sub_neg_eq_add] at h3
    rw [show mathieuB (2 * n + 1) q - (((2 * i + 1 : ℕ) : ℝ) ^ 2 - if i = 0 then q else 0) =
      mathieuB (2 * n + 1) q - ((2 * i + 1 : ℕ) : ℝ) ^ 2 + (if i = 0 then q else 0) by ring] at hi
    linarith

/-! ### Interlacing -/

/-- **Interlacing** of the Neumann and Dirichlet spectra at `L` (same condition at `0`),
in counting form. -/
private lemma sturmSpectrum_interlace {V : ℝ → ℝ} {B L : ℝ} (hV : Continuous V) (hB : ∀ x, |V x| ≤ B)
    (hL : 0 < L) (odd0 : Bool) {e d : ℝ} (he : e ∈ ODE.separatedSpectrum V L odd0 false)
    (hd : d ∈ ODE.separatedSpectrum V L odd0 true) :
    ((ODE.separatedSpectrum V L odd0 false ∩ Iio e).ncard ≤ (ODE.separatedSpectrum V L odd0 true ∩ Iio d).ncard →
      e < d) ∧
    ((ODE.separatedSpectrum V L odd0 true ∩ Iio d).ncard < (ODE.separatedSpectrum V L odd0 false ∩ Iio e).ncard →
      d < e) := by
  have hfinD := ODE.separatedSpectrum_inter_Iio_finite hV hB hL odd0 true
  have hfinN := ODE.separatedSpectrum_inter_Iio_finite hV hB hL odd0 false
  rw [ODE.separatedSpectrum_true_eq hV] at hd hfinD ⊢
  rw [ODE.separatedSpectrum_false_eq hV] at he hfinN ⊢
  have key := (ODE.basicSolutionZeroCount_eq_ncard_neumann_eigenvalues hV hB hL hfinD hfinN he).symm.trans
    (ODE.basicSolutionZeroCount_eq_ncard_dirichlet_eigenvalues_le hV hB hL hfinD e)
  set D := {e | ODE.basicSolution V odd0 e L = 0}
  set N := {e | deriv (ODE.basicSolution V odd0 e) L = 0}
  have hfinI : (D ∩ Iic e).Finite := (hfinD (e + 1)).subset fun x hx => ⟨hx.1, by
    have := hx.2; simp only [mem_Iic] at this; simp only [mem_Iio]; linarith⟩
  constructor
  · intro h
    by_contra hde
    push Not at hde
    have hsub : insert d (D ∩ Iio d) ⊆ D ∩ Iic e := by
      intro x hx
      rcases hx with rfl | ⟨hx1, hx2⟩
      · exact ⟨hd, hde⟩
      · exact ⟨hx1, (le_of_lt hx2).trans hde⟩
    have := Set.ncard_le_ncard hsub hfinI
    rw [Set.ncard_insert_of_notMem (fun h : d ∈ D ∩ Iio d => lt_irrefl d h.2) (hfinD d)] at this
    omega
  · intro h
    by_contra hde
    push Not at hde
    rcases hde.lt_or_eq with hlt | rfl
    · have hsub : D ∩ Iic e ⊆ D ∩ Iio d := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hlt⟩
      have := Set.ncard_le_ncard hsub (hfinD d)
      omega
    · exact ODE.basicSolution_ne_zero_of_deriv_eq_zero hV he hd

/-- `a_m(q)` lies in its Sturm–Liouville spectrum on `[0, π/2]` and has exactly `⌊m/2⌋`
smaller spectral values there. -/
private lemma mathieuA_mem_sturmSpectrum (m : ℕ) (q : ℝ) :
    mathieuA m q ∈ ODE.separatedSpectrum (fun x : ℝ => 2 * q * Real.cos (2 * x)) (π / 2) false
      (if Even m then false else true) ∧
    (ODE.separatedSpectrum (fun x : ℝ => 2 * q * Real.cos (2 * x)) (π / 2) false
      (if Even m then false else true) ∩ Iio (mathieuA m q)).ncard = m / 2 := by
  have h := mathieuA_spec m q
  rw [mathieuSpecA_eq_sturmSpectrum] at h
  exact ⟨h.1, ncard_eq_of_encard_eq_natCast h.2⟩

/-- For `m ≥ 1`, `b_m(q)` lies in its Sturm–Liouville spectrum on `[0, π/2]` and has exactly
`⌊(m-1)/2⌋` smaller spectral values there. -/
private lemma mathieuB_mem_sturmSpectrum {m : ℕ} (hm : m ≠ 0) (q : ℝ) :
    mathieuB m q ∈ ODE.separatedSpectrum (fun x : ℝ => 2 * q * Real.cos (2 * x)) (π / 2) true
      (if Even m then true else false) ∧
    (ODE.separatedSpectrum (fun x : ℝ => 2 * q * Real.cos (2 * x)) (π / 2) true
      (if Even m then true else false) ∩ Iio (mathieuB m q)).ncard = (m - 1) / 2 := by
  have h := mathieuB_spec hm q
  rw [mathieuSpecB_eq_sturmSpectrum] at h
  exact ⟨h.1, ncard_eq_of_encard_eq_natCast h.2⟩

/-- `a_m(q) < a_{m+1}(q)` for real `q` (interlacing of the two spectra with `w'(0) = 0`). -/
private lemma mathieuA_lt_mathieuA_succ (m : ℕ) (q : ℝ) : mathieuA m q < mathieuA (m + 1) q := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · have h1 := mathieuA_mem_sturmSpectrum (2 * j) q
    have h2 := mathieuA_mem_sturmSpectrum (2 * j + 1) q
    simp only [even_two_mul, ↓reduceIte, Nat.not_even_bit1] at h1 h2
    exact (sturmSpectrum_interlace (continuous_two_mul_cos_two_mul q) (abs_two_mul_cos_two_mul_le q) (by positivity) false h1.1 h2.1).1
      (by rw [h1.2, h2.2]; omega)
  · have h1 := mathieuA_mem_sturmSpectrum (2 * j + 2) q
    have h2 := mathieuA_mem_sturmSpectrum (2 * j + 1) q
    have he : Even (2 * j + 2) := ⟨j + 1, by ring⟩
    simp only [he, ↓reduceIte, Nat.not_even_bit1] at h1 h2
    exact (sturmSpectrum_interlace (continuous_two_mul_cos_two_mul q) (abs_two_mul_cos_two_mul_le q) (by positivity) false h1.1 h2.1).2
      (by rw [h1.2, h2.2]; omega)

/-- `b_m(q) < b_{m+1}(q)` for real `q`, `m ≥ 1`. -/
private lemma mathieuB_lt_mathieuB_succ {m : ℕ} (hm : m ≠ 0) (q : ℝ) : mathieuB m q < mathieuB (m + 1) q := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have h1 := mathieuB_mem_sturmSpectrum (m := 2 * (j + 1) + 1) (by omega) q
    have h2 := mathieuB_mem_sturmSpectrum (m := 2 * (j + 1)) (by omega) q
    have he : Even (2 * (j + 1)) := even_two_mul _
    simp only [he, ↓reduceIte, Nat.not_even_bit1] at h1 h2
    exact (sturmSpectrum_interlace (continuous_two_mul_cos_two_mul q) (abs_two_mul_cos_two_mul_le q) (by positivity) true h1.1 h2.1).2
      (by rw [h1.2, h2.2]; omega)
  · have h1 := mathieuB_mem_sturmSpectrum (m := 2 * j + 1) (by omega) q
    have h2 := mathieuB_mem_sturmSpectrum (m := 2 * j + 2) (by omega) q
    have he : Even (2 * j + 2) := ⟨j + 1, by ring⟩
    simp only [he, ↓reduceIte, Nat.not_even_bit1] at h1 h2
    exact (sturmSpectrum_interlace (continuous_two_mul_cos_two_mul q) (abs_two_mul_cos_two_mul_le q) (by positivity) true h1.1 h2.1).1
      (by rw [h1.2, h2.2]; omega)

/-! ### Identification of the window -/

/-- If `x` is within `4c < 1/2` of both `(k+s)²` and `(k'+s)²`, then `k = k'`. -/
private lemma eq_of_abs_sub_sq_le {k k' s : ℕ} {x c : ℝ} (hc : c < 1 / 8)
    (h1 : |x - ((k + s : ℕ) : ℝ) ^ 2| ≤ 4 * c) (h2 : |x - ((k' + s : ℕ) : ℝ) ^ 2| ≤ 4 * c) :
    k = k' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : ((k + s : ℕ) : ℝ) ^ 2 + 1 ≤ ((k' + s : ℕ) : ℝ) ^ 2 := by
      have : ((k + s : ℕ) : ℝ) + 1 ≤ ((k' + s : ℕ) : ℝ) := by exact_mod_cast (by omega)
      nlinarith [(Nat.cast_nonneg (k + s) : (0 : ℝ) ≤ _)]
    rw [abs_le] at h1 h2; linarith
  · have : ((k' + s : ℕ) : ℝ) ^ 2 + 1 ≤ ((k + s : ℕ) : ℝ) ^ 2 := by
      have : ((k' + s : ℕ) : ℝ) + 1 ≤ ((k + s : ℕ) : ℝ) := by exact_mod_cast (by omega)
      nlinarith [(Nat.cast_nonneg (k' + s) : (0 : ℝ) ≤ _)]
    rw [abs_le] at h1 h2; linarith

/-- Combinatorial core of the identification of `a_m(q)` near `q = 0`: a strictly increasing
sequence whose terms lie in windows of radius `4c` around `(k + s)²` (with `k` of the parity
of the index) and which meets each of the first `m + 1` windows has its `m`-th term in the
`m`-th window. -/
private lemma abs_sub_sq_le_of_strictMono_windows {x : ℕ → ℝ} {c : ℝ} {s m : ℕ} (hc : c < 1 / 8) (hx : StrictMono x)
    (hw : ∀ j, ∃ k : ℕ, k % 2 = j % 2 ∧ |x j - ((k + s : ℕ) : ℝ) ^ 2| ≤ 4 * c)
    (hE : ∀ k ≤ m, ∃ j, |x j - ((k + s : ℕ) : ℝ) ^ 2| ≤ 4 * c) :
    |x m - ((m + s : ℕ) : ℝ) ^ 2| ≤ 4 * c := by
  choose κ hκp hκ using hw
  have huniq : ∀ j k, |x j - ((k + s : ℕ) : ℝ) ^ 2| ≤ 4 * c → k = κ j := fun j k h =>
    eq_of_abs_sub_sq_le hc h (hκ j)
  have hstep : ∀ j, κ j < κ (j + 1) := by
    intro j
    have hne : κ j ≠ κ (j + 1) := fun h => by
      have := hκp j; have := hκp (j + 1); omega
    by_contra hle
    push Not at hle
    have hlt : κ (j + 1) < κ j := lt_of_le_of_ne hle (Ne.symm hne)
    have : ((κ (j + 1) + s : ℕ) : ℝ) ^ 2 + 1 ≤ ((κ j + s : ℕ) : ℝ) ^ 2 := by
      have : ((κ (j + 1) + s : ℕ) : ℝ) + 1 ≤ ((κ j + s : ℕ) : ℝ) := by exact_mod_cast (by omega)
      nlinarith [(Nat.cast_nonneg (κ (j + 1) + s) : (0 : ℝ) ≤ _)]
    have h1 := hκ j
    have h2 := hκ (j + 1)
    have h3 := hx (Nat.lt_succ_self j)
    rw [abs_le] at h1 h2; linarith
  have hmono : StrictMono κ := strictMono_nat_of_lt_succ hstep
  have hge : ∀ j, j ≤ κ j := fun j => hmono.le_apply
  have key : ∀ i ≤ m, κ i = i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro him
      obtain ⟨j, hj⟩ := hE i him
      have hj' := huniq j i hj
      have hij : i ≤ j := by
        by_contra hlt
        push Not at hlt
        have := ih j hlt (by omega)
        omega
      have := hmono.monotone hij
      have := hge i
      omega
  have := key m le_rfl
  have h := hκ m
  rwa [this] at h

/-- Sign change at the ends of `[α, β]` at `q = 0` persists for small `q` and gives a zero. -/
private lemma eventually_exists_zero_of_sign_change {G : ℝ → ℝ → ℝ} (hGa : ∀ q, Continuous fun a => G a q)
    (hGq : ∀ a, Continuous fun q => G a q) {α β : ℝ} (hαβ : α < β)
    (hs : G α 0 * G β 0 < 0) : ∀ᶠ q : ℝ in 𝓝 0, ∃ c ∈ Ioo α β, G c q = 0 := by
  have hc : Continuous fun q => G α q * G β q := (hGq α).mul (hGq β)
  have hev : ∀ᶠ q : ℝ in 𝓝 0, G α q * G β q < 0 :=
    hc.continuousAt.eventually (gt_mem_nhds hs)
  filter_upwards [hev] with q hq
  have hcont : ContinuousOn (fun a => G a q) (Icc α β) := (hGa q).continuousOn
  rcases lt_or_gt_of_ne (show G α q ≠ 0 by intro h; simp [h] at hq) with h1 | h1
  · have h2 : 0 < G β q := by nlinarith
    exact intermediate_value_Ioo hαβ.le hcont ⟨h1, h2⟩
  · have h2 : G β q < 0 := by nlinarith
    exact intermediate_value_Ioo' hαβ.le hcont ⟨h2, h1⟩

/-- `w_I(z; a, q)` and its `z`-derivative are entire functions of `a`. -/
private lemma differentiable_mathieuWI_and_deriv_a (q z : ℂ) :
    Differentiable ℂ (fun a => mathieuWI a q z) ∧
      Differentiable ℂ (fun a => deriv (mathieuWI a q) z) :=
  differentiable_family_in_a (W := mathieuWI) isMathieuSolution_mathieuWI
    (fun a q => (mathieuWI_spec a q).2.1) (fun a q => (mathieuWI_spec a q).2.2) q z

/-- `w_II(z; a, q)` and its `z`-derivative are entire functions of `a`. -/
private lemma differentiable_mathieuWII_and_deriv_a (q z : ℂ) :
    Differentiable ℂ (fun a => mathieuWII a q z) ∧
      Differentiable ℂ (fun a => deriv (mathieuWII a q) z) :=
  differentiable_family_in_a (W := mathieuWII) isMathieuSolution_mathieuWII
    (fun a q => (mathieuWII_spec a q).2.1) (fun a q => (mathieuWII_spec a q).2.2) q z

/-- `w_I(z; a, q)` and its `z`-derivative are entire functions of `q`. -/
private lemma differentiable_mathieuWI_and_deriv_q (a z : ℂ) :
    Differentiable ℂ (fun q => mathieuWI a q z) ∧
      Differentiable ℂ (fun q => deriv (mathieuWI a q) z) :=
  differentiable_family_in_q (W := mathieuWI) isMathieuSolution_mathieuWI
    (fun a q => (mathieuWI_spec a q).2.1) (fun a q => (mathieuWI_spec a q).2.2) a z

/-- `w_II(z; a, q)` and its `z`-derivative are entire functions of `q`. -/
private lemma differentiable_mathieuWII_and_deriv_q (a z : ℂ) :
    Differentiable ℂ (fun q => mathieuWII a q z) ∧
      Differentiable ℂ (fun q => deriv (mathieuWII a q) z) :=
  differentiable_family_in_q (W := mathieuWII) isMathieuSolution_mathieuWII
    (fun a q => (mathieuWII_spec a q).2.1) (fun a q => (mathieuWII_spec a q).2.2) a z

/-- For an entire `f`, `x ↦ Re f(x)` is continuous on `ℝ`. -/
private lemma continuous_re_comp_ofReal {f : ℂ → ℂ} (hf : Differentiable ℂ f) : Continuous fun x : ℝ => (f x).re :=
  Complex.continuous_re.comp (hf.continuous.comp Complex.continuous_ofReal)

/-- Cast identity `(s : ℂ) (π/2) = ((s π/2 : ℝ) : ℂ)`. -/
private lemma ofReal_mul_pi_div_two (s : ℝ) : (s : ℂ) * ((π : ℂ) / 2) = ((s * (π / 2) : ℝ) : ℂ) := by
  push_cast; ring

/-- At `q = 0`, `a = s²`: `Re w_I'(π/2) = -s sin(sπ/2)`. -/
private lemma re_deriv_mathieuWI_half_pi_q_zero (s : ℝ) :
    (deriv (mathieuWI ((s ^ 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ)) ((π : ℂ) / 2)).re =
      -Real.sin (s * (π / 2)) * s := by
  rw [Complex.ofReal_zero, deriv_mathieuWI_q_zero (s := (s : ℂ)) (by push_cast; ring),
    ofReal_mul_pi_div_two, ← Complex.ofReal_sin, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- At `q = 0`, `a = -1`: `Re w_I'(π/2) = sinh(π/2)`. -/
private lemma re_deriv_mathieuWI_half_pi_neg_one_q_zero :
    (deriv (mathieuWI ((-1 : ℝ) : ℂ) ((0 : ℝ) : ℂ)) ((π : ℂ) / 2)).re = Real.sinh (π / 2) := by
  rw [Complex.ofReal_zero, deriv_mathieuWI_q_zero (s := I) (by push_cast; simp)]
  rw [show I * ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) * I by push_cast; ring, Complex.sin_mul_I,
    ← Complex.ofReal_sinh]
  rw [show -(((Real.sinh (π / 2) : ℝ) : ℂ) * I) * I = ((Real.sinh (π / 2) : ℝ) : ℂ) by
    linear_combination (-(((Real.sinh (π / 2) : ℝ) : ℂ))) * Complex.I_sq]
  exact Complex.ofReal_re _

/-- At `q = 0`, `a = s²`: `Re w_I(π/2) = cos(sπ/2)`. -/
private lemma re_mathieuWI_half_pi_q_zero (s : ℝ) :
    (mathieuWI ((s ^ 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((π : ℂ) / 2)).re = Real.cos (s * (π / 2)) := by
  rw [Complex.ofReal_zero, mathieuWI_q_zero (s := (s : ℂ)) (by push_cast; ring),
    ofReal_mul_pi_div_two, ← Complex.ofReal_cos, Complex.ofReal_re]

/-- At `q = 0`, `a = s²`: `Re w_II'(π/2) = cos(sπ/2)`. -/
private lemma re_deriv_mathieuWII_half_pi_q_zero (s : ℝ) :
    (deriv (mathieuWII ((s ^ 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ)) ((π : ℂ) / 2)).re =
      Real.cos (s * (π / 2)) := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [show (((0 : ℝ) ^ 2 : ℝ) : ℂ) = 0 by simp, Complex.ofReal_zero,
      show mathieuWII 0 0 = fun z => z from funext mathieuWII_zero_zero, deriv_id'']
    simp
  · rw [Complex.ofReal_zero, deriv_mathieuWII_q_zero (s := (s : ℂ)) (by push_cast; ring)
      (by exact_mod_cast hs), ofReal_mul_pi_div_two, ← Complex.ofReal_cos, Complex.ofReal_re]

/-- At `q = 0`, `a = s²`, `s ≠ 0`: `Re w_II(π/2) = sin(sπ/2)/s`. -/
private lemma re_mathieuWII_half_pi_q_zero {s : ℝ} (hs : s ≠ 0) :
    (mathieuWII ((s ^ 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((π : ℂ) / 2)).re = Real.sin (s * (π / 2)) / s := by
  rw [Complex.ofReal_zero, mathieuWII_q_zero (s := (s : ℂ)) (by push_cast; ring)
    (by exact_mod_cast hs), ofReal_mul_pi_div_two, ← Complex.ofReal_sin, ← Complex.ofReal_div,
    Complex.ofReal_re]

/-- `sin((2i+1)π/2) = (-1)^i`. -/
private lemma sin_two_mul_add_one_mul_pi_div_two (i : ℕ) : Real.sin (((2 * i + 1 : ℕ) : ℝ) * (π / 2)) = (-1) ^ i := by
  rw [show ((2 * i + 1 : ℕ) : ℝ) * (π / 2) = (i : ℝ) * π + π / 2 by push_cast; ring,
    Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]

/-- `cos(2i · π/2) = (-1)^i`. -/
private lemma cos_two_mul_mul_pi_div_two (i : ℕ) : Real.cos (((2 * i : ℕ) : ℝ) * (π / 2)) = (-1) ^ i := by
  rw [show ((2 * i : ℕ) : ℝ) * (π / 2) = (i : ℝ) * π by push_cast; ring, Real.cos_nat_mul_pi]

/-- A complex number fixed by conjugation with zero real part is `0`. -/
private lemma eq_zero_of_conj_eq_of_re_eq_zero {z : ℂ} (hz : (starRingEnd ℂ) z = z) (h : z.re = 0) : z = 0 := by
  rw [← Complex.conj_eq_iff_re.1 hz, h, Complex.ofReal_zero]

/-- For real `a, q`, `w_I'(π/2; a, q)` is real (fixed by conjugation). -/
private lemma conj_deriv_mathieuWI_half_pi (a q : ℝ) :
    (starRingEnd ℂ) (deriv (mathieuWI a q) ((π : ℂ) / 2)) =
      deriv (mathieuWI a q) ((π : ℂ) / 2) := by
  rw [← ofReal_pi_div_two]; exact conj_deriv_mathieuWI_ofReal a q _

/-- For real `a, q`, `w_I(π/2; a, q)` is real (fixed by conjugation). -/
private lemma conj_mathieuWI_half_pi (a q : ℝ) :
    (starRingEnd ℂ) (mathieuWI a q ((π : ℂ) / 2)) = mathieuWI a q ((π : ℂ) / 2) := by
  rw [← ofReal_pi_div_two]; exact conj_mathieuWI_ofReal a q _

/-- For real `a, q`, `w_II'(π/2; a, q)` is real (fixed by conjugation). -/
private lemma conj_deriv_mathieuWII_half_pi (a q : ℝ) :
    (starRingEnd ℂ) (deriv (mathieuWII a q) ((π : ℂ) / 2)) =
      deriv (mathieuWII a q) ((π : ℂ) / 2) := by
  rw [← ofReal_pi_div_two]; exact conj_deriv_mathieuWII_ofReal a q _

/-- For real `a, q`, `w_II(π/2; a, q)` is real (fixed by conjugation). -/
private lemma conj_mathieuWII_half_pi (a q : ℝ) :
    (starRingEnd ℂ) (mathieuWII a q ((π : ℂ) / 2)) = mathieuWII a q ((π : ℂ) / 2) := by
  rw [← ofReal_pi_div_two]; exact conj_mathieuWII_ofReal a q _

/-- For small `q` the spectrum of the `a_k` contains a point between `(k-1)²` and `(k+1)²`
(`-1` instead of `(k-1)²` for `k = 0`). -/
private lemma eventually_exists_mem_mathieuSpecA_near_sq (k : ℕ) : ∀ᶠ q : ℝ in 𝓝 0, ∃ c ∈ mathieuSpecA k q,
    (if k = 0 then (-1 : ℝ) else ((k : ℝ) - 1) ^ 2) < c ∧ c < ((k : ℝ) + 1) ^ 2 := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
  · set G : ℝ → ℝ → ℝ := fun a q => (deriv (mathieuWI (a : ℂ) (q : ℂ)) ((π : ℂ) / 2)).re
    have hGa : ∀ q, Continuous fun a => G a q := fun q => continuous_re_comp_ofReal (differentiable_mathieuWI_and_deriv_a q _).2
    have hGq : ∀ a, Continuous fun q => G a q := fun a => continuous_re_comp_ofReal (differentiable_mathieuWI_and_deriv_q a _).2
    have hmem : ∀ q c, G c q = 0 → c ∈ mathieuSpecA (2 * i) q := fun q c h => by
      simp only [mathieuSpecA, even_two_mul, ↓reduceIte, mem_ofPred_eq]
      exact eq_zero_of_conj_eq_of_re_eq_zero (conj_deriv_mathieuWI_half_pi c q) h
    rcases i with _ | j
    · have h0 : G (-1) 0 * G ((1 : ℕ) ^ 2 : ℝ) 0 < 0 := by
        have e1 : G (-1) 0 = Real.sinh (π / 2) := re_deriv_mathieuWI_half_pi_neg_one_q_zero
        have e2 : G ((1 : ℕ) ^ 2 : ℝ) 0 = -Real.sin (((1 : ℕ) : ℝ) * (π / 2)) * ((1 : ℕ) : ℝ) :=
          re_deriv_mathieuWI_half_pi_q_zero _
        rw [e1, e2]
        have := sin_two_mul_add_one_mul_pi_div_two 0
        simp only [Nat.cast_one, one_mul, mul_one] at this ⊢
        rw [Real.sin_pi_div_two]
        have := Real.sinh_pos_iff.2 (by positivity : (0 : ℝ) < π / 2)
        linarith
      filter_upwards [eventually_exists_zero_of_sign_change hGa hGq (by norm_num) h0] with q ⟨c, hc, hz⟩
      refine ⟨c, hmem q c hz, ?_, ?_⟩
      · simpa using hc.1
      · have := hc.2; push_cast at this ⊢; linarith
    · have h0 : G (((2 * j + 1 : ℕ) : ℝ) ^ 2) 0 * G (((2 * (j + 1) + 1 : ℕ) : ℝ) ^ 2) 0 < 0 := by
        have e1 : G (((2 * j + 1 : ℕ) : ℝ) ^ 2) 0 = _ := re_deriv_mathieuWI_half_pi_q_zero _
        have e2 : G (((2 * (j + 1) + 1 : ℕ) : ℝ) ^ 2) 0 = _ := re_deriv_mathieuWI_half_pi_q_zero _
        rw [e1, e2, sin_two_mul_add_one_mul_pi_div_two, sin_two_mul_add_one_mul_pi_div_two, pow_succ]
        have : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
        have hp : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) := by positivity
        have hp' : (0 : ℝ) < ((2 * (j + 1) + 1 : ℕ) : ℝ) := by positivity
        nlinarith [mul_pos hp hp']
      have hlt : ((2 * j + 1 : ℕ) : ℝ) ^ 2 < ((2 * (j + 1) + 1 : ℕ) : ℝ) ^ 2 := by
        gcongr; omega
      filter_upwards [eventually_exists_zero_of_sign_change hGa hGq hlt h0] with q ⟨c, hc, hz⟩
      refine ⟨c, hmem q c hz, ?_, ?_⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        have := hc.1; push_cast at this ⊢; linarith
      · have := hc.2; push_cast at this ⊢; linarith
  · set G : ℝ → ℝ → ℝ := fun a q => (mathieuWI (a : ℂ) (q : ℂ) ((π : ℂ) / 2)).re
    have hGa : ∀ q, Continuous fun a => G a q := fun q => continuous_re_comp_ofReal (differentiable_mathieuWI_and_deriv_a q _).1
    have hGq : ∀ a, Continuous fun q => G a q := fun a => continuous_re_comp_ofReal (differentiable_mathieuWI_and_deriv_q a _).1
    have hmem : ∀ q c, G c q = 0 → c ∈ mathieuSpecA (2 * i + 1) q := fun q c h => by
      simp only [mathieuSpecA, Nat.not_even_bit1, ↓reduceIte, mem_ofPred_eq]
      exact eq_zero_of_conj_eq_of_re_eq_zero (conj_mathieuWI_half_pi c q) h
    have h0 : G (((2 * i : ℕ) : ℝ) ^ 2) 0 * G (((2 * (i + 1) : ℕ) : ℝ) ^ 2) 0 < 0 := by
      have e1 : G (((2 * i : ℕ) : ℝ) ^ 2) 0 = _ := re_mathieuWI_half_pi_q_zero _
      have e2 : G (((2 * (i + 1) : ℕ) : ℝ) ^ 2) 0 = _ := re_mathieuWI_half_pi_q_zero _
      rw [e1, e2, cos_two_mul_mul_pi_div_two, cos_two_mul_mul_pi_div_two, pow_succ]
      have : ((-1 : ℝ) ^ i) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      nlinarith
    have hlt : ((2 * i : ℕ) : ℝ) ^ 2 < ((2 * (i + 1) : ℕ) : ℝ) ^ 2 := by gcongr; omega
    filter_upwards [eventually_exists_zero_of_sign_change hGa hGq hlt h0] with q ⟨c, hc, hz⟩
    refine ⟨c, hmem q c hz, ?_, ?_⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      have := hc.1; push_cast at this ⊢; linarith
    · have := hc.2; push_cast at this ⊢; linarith

/-- For small `q` the spectrum of the `b_k`, `k ≥ 1`, contains a point between `(k-1)²` and
`(k+1)²`. -/
private lemma eventually_exists_mem_mathieuSpecB_near_sq {k : ℕ} (hk : k ≠ 0) : ∀ᶠ q : ℝ in 𝓝 0, ∃ c ∈ mathieuSpecB k q,
    ((k : ℝ) - 1) ^ 2 < c ∧ c < ((k : ℝ) + 1) ^ 2 := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
  · obtain ⟨i, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    set G : ℝ → ℝ → ℝ := fun a q => (mathieuWII (a : ℂ) (q : ℂ) ((π : ℂ) / 2)).re
    have hGa : ∀ q, Continuous fun a => G a q := fun q => continuous_re_comp_ofReal (differentiable_mathieuWII_and_deriv_a q _).1
    have hGq : ∀ a, Continuous fun q => G a q := fun a => continuous_re_comp_ofReal (differentiable_mathieuWII_and_deriv_q a _).1
    have hmem : ∀ q c, G c q = 0 → c ∈ mathieuSpecB (2 * (i + 1)) q := fun q c h => by
      simp only [mathieuSpecB, even_two_mul, ↓reduceIte, mem_ofPred_eq]
      exact eq_zero_of_conj_eq_of_re_eq_zero (conj_mathieuWII_half_pi c q) h
    have hp : (0 : ℝ) < ((2 * i + 1 : ℕ) : ℝ) := by positivity
    have hp' : (0 : ℝ) < ((2 * (i + 1) + 1 : ℕ) : ℝ) := by positivity
    have h0 : G (((2 * i + 1 : ℕ) : ℝ) ^ 2) 0 * G (((2 * (i + 1) + 1 : ℕ) : ℝ) ^ 2) 0 < 0 := by
      have e1 : G (((2 * i + 1 : ℕ) : ℝ) ^ 2) 0 = _ := re_mathieuWII_half_pi_q_zero hp.ne'
      have e2 : G (((2 * (i + 1) + 1 : ℕ) : ℝ) ^ 2) 0 = _ := re_mathieuWII_half_pi_q_zero hp'.ne'
      rw [e1, e2, sin_two_mul_add_one_mul_pi_div_two, sin_two_mul_add_one_mul_pi_div_two, pow_succ, div_mul_div_comm]
      have : ((-1 : ℝ) ^ i) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      apply div_neg_of_neg_of_pos _ (mul_pos hp hp')
      nlinarith
    have hlt : ((2 * i + 1 : ℕ) : ℝ) ^ 2 < ((2 * (i + 1) + 1 : ℕ) : ℝ) ^ 2 := by gcongr; omega
    filter_upwards [eventually_exists_zero_of_sign_change hGa hGq hlt h0] with q ⟨c, hc, hz⟩
    refine ⟨c, hmem q c hz, ?_, ?_⟩
    · have := hc.1; push_cast at this ⊢; linarith
    · have := hc.2; push_cast at this ⊢; linarith
  · set G : ℝ → ℝ → ℝ := fun a q => (deriv (mathieuWII (a : ℂ) (q : ℂ)) ((π : ℂ) / 2)).re
    have hGa : ∀ q, Continuous fun a => G a q := fun q => continuous_re_comp_ofReal (differentiable_mathieuWII_and_deriv_a q _).2
    have hGq : ∀ a, Continuous fun q => G a q := fun a => continuous_re_comp_ofReal (differentiable_mathieuWII_and_deriv_q a _).2
    have hmem : ∀ q c, G c q = 0 → c ∈ mathieuSpecB (2 * i + 1) q := fun q c h => by
      simp only [mathieuSpecB, Nat.not_even_bit1, ↓reduceIte, mem_ofPred_eq]
      exact eq_zero_of_conj_eq_of_re_eq_zero (conj_deriv_mathieuWII_half_pi c q) h
    have h0 : G (((2 * i : ℕ) : ℝ) ^ 2) 0 * G (((2 * (i + 1) : ℕ) : ℝ) ^ 2) 0 < 0 := by
      have e1 : G (((2 * i : ℕ) : ℝ) ^ 2) 0 = _ := re_deriv_mathieuWII_half_pi_q_zero _
      have e2 : G (((2 * (i + 1) : ℕ) : ℝ) ^ 2) 0 = _ := re_deriv_mathieuWII_half_pi_q_zero _
      rw [e1, e2, cos_two_mul_mul_pi_div_two, cos_two_mul_mul_pi_div_two, pow_succ]
      have : ((-1 : ℝ) ^ i) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      nlinarith
    have hlt : ((2 * i : ℕ) : ℝ) ^ 2 < ((2 * (i + 1) : ℕ) : ℝ) ^ 2 := by gcongr; omega
    filter_upwards [eventually_exists_zero_of_sign_change hGa hGq hlt h0] with q ⟨c, hc, hz⟩
    refine ⟨c, hmem q c hz, ?_, ?_⟩
    · have := hc.1; push_cast at this ⊢; linarith
    · have := hc.2; push_cast at this ⊢; linarith

/-- Every point of the spectrum `mathieuSpecA k q` is `a_m(q)` for some `m ≡ k (mod 2)`. -/
private lemma exists_mathieuA_eq_of_mem_mathieuSpecA {k : ℕ} {q c : ℝ} (hc : c ∈ mathieuSpecA k q) :
    ∃ m, m % 2 = k % 2 ∧ mathieuA m q = c := by
  have hfin : (mathieuSpecA k q ∩ Iio c).Finite := by
    rw [mathieuSpecA_eq_sturmSpectrum]
    exact ODE.separatedSpectrum_inter_Iio_finite (continuous_two_mul_cos_two_mul q) (abs_two_mul_cos_two_mul_le q) (by positivity) _ _ c
  obtain ⟨j, hj⟩ := exists_eq_nthLeast hc hfin
  refine ⟨2 * j + k % 2, by omega, ?_⟩
  have hS : mathieuSpecA (2 * j + k % 2) q = mathieuSpecA k q := by
    unfold mathieuSpecA
    have : Even (2 * j + k % 2) ↔ Even k := by
      rw [Nat.even_iff, Nat.even_iff]; omega
    simp only [this]
  rw [mathieuA, hS, show (2 * j + k % 2) / 2 = j by omega, hj]

/-- Every point of `mathieuSpecB k q` is `b_m(q)` for some `m ≥ 1`, `m ≡ k (mod 2)`. -/
private lemma exists_mathieuB_eq_of_mem_mathieuSpecB {k : ℕ} {q c : ℝ} (hc : c ∈ mathieuSpecB k q) :
    ∃ m, m ≠ 0 ∧ m % 2 = k % 2 ∧ mathieuB m q = c := by
  have hfin : (mathieuSpecB k q ∩ Iio c).Finite := by
    rw [mathieuSpecB_eq_sturmSpectrum]
    exact ODE.separatedSpectrum_inter_Iio_finite (continuous_two_mul_cos_two_mul q) (abs_two_mul_cos_two_mul_le q) (by positivity) _ _ c
  obtain ⟨j, hj⟩ := exists_eq_nthLeast hc hfin
  refine ⟨2 * j + 2 - k % 2, by omega, by omega, ?_⟩
  have hS : mathieuSpecB (2 * j + 2 - k % 2) q = mathieuSpecB k q := by
    unfold mathieuSpecB
    have : Even (2 * j + 2 - k % 2) ↔ Even k := by
      rw [Nat.even_iff, Nat.even_iff]; omega
    simp only [this]
  rw [mathieuB, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hS,
    show (2 * j + 2 - k % 2 - 1) / 2 = j by omega, hj]

/-- If `c` lies strictly between `(k-1)²` (or `-1` for `k = 0`) and `(k+1)²`, and is within
`4x < 1/2` of `k'²` with `k' ≡ k (mod 2)`, then `k' = k`. -/
private lemma eq_of_abs_sub_sq_le_of_mem_window {k k' : ℕ} {c x : ℝ} (hx : x < 1 / 8) (hpar : k' % 2 = k % 2)
    (hL : (if k = 0 then (-1 : ℝ) else ((k : ℝ) - 1) ^ 2) < c) (hR : c < ((k : ℝ) + 1) ^ 2)
    (h : |c - (k' : ℝ) ^ 2| ≤ 4 * x) : k' = k := by
  rw [abs_le] at h
  by_contra hne
  rcases (show k + 2 ≤ k' ∨ k' + 2 ≤ k by omega) with h1 | h1
  · have : (k : ℝ) + 2 ≤ k' := by exact_mod_cast h1
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ _)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at hL
    have : (k' : ℝ) + 2 ≤ k := by exact_mod_cast h1
    nlinarith [(Nat.cast_nonneg k' : (0 : ℝ) ≤ _)]

/-- Eventually as `q → 0`, `|q| < 1/8`. -/
theorem eventually_abs_lt_one_div_eight : ∀ᶠ q : ℝ in 𝓝 0, |q| < 1 / 8 := by
  have : ∀ᶠ q : ℝ in 𝓝 0, q ∈ Metric.ball (0 : ℝ) (1 / 8) := Metric.ball_mem_nhds _ (by norm_num)
  filter_upwards [this] with q hq
  rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hq

/-- **`a_m(q)` near `q = 0`**: for small real `q`, `|a_m(q) - m²| ≤ 4|q|`. In particular
`a_m` is continuous at `0` (DLMF 28.2.23 and §28.6). -/
theorem eventually_abs_mathieuA_sub_sq_le (m : ℕ) : ∀ᶠ q : ℝ in 𝓝 0, |mathieuA m q - (m : ℝ) ^ 2| ≤ 4 * |q| := by
  filter_upwards [(Finset.range (m + 1)).eventually_all.2 (fun k _ => eventually_exists_mem_mathieuSpecA_near_sq k),
    eventually_abs_lt_one_div_eight] with q hE hq
  have := abs_sub_sq_le_of_strictMono_windows (x := fun j => mathieuA j q) (c := |q|) (s := 0) (m := m) hq
    (strictMono_nat_of_lt_succ fun j => mathieuA_lt_mathieuA_succ j q)
    (fun j => by simpa using exists_abs_mathieuA_sub_sq_le j q) (fun k hk => ?_)
  · simpa using this
  obtain ⟨c, hc, hL, hR⟩ := hE k (Finset.mem_range.2 (by omega))
  obtain ⟨m', hm', rfl⟩ := exists_mathieuA_eq_of_mem_mathieuSpecA hc
  obtain ⟨k', hk', hw⟩ := exists_abs_mathieuA_sub_sq_le m' q
  have := eq_of_abs_sub_sq_le_of_mem_window hq (hk'.trans hm') hL hR hw
  subst this
  exact ⟨m', by simpa using hw⟩

/-- **`b_m(q)` near `q = 0`**: for `m ≥ 1` and small real `q`, `|b_m(q) - m²| ≤ 4|q|`. -/
theorem eventually_abs_mathieuB_sub_sq_le {m : ℕ} (hm : m ≠ 0) :
    ∀ᶠ q : ℝ in 𝓝 0, |mathieuB m q - (m : ℝ) ^ 2| ≤ 4 * |q| := by
  obtain ⟨m, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  filter_upwards [(Finset.range (m + 2)).eventually_all.2
    (fun k _ => eventually_exists_mem_mathieuSpecB_near_sq (k := k + 1) (by omega)), eventually_abs_lt_one_div_eight] with q hE hq
  have := abs_sub_sq_le_of_strictMono_windows (x := fun j => mathieuB (j + 1) q) (c := |q|) (s := 1) (m := m) hq
    (strictMono_nat_of_lt_succ fun j => mathieuB_lt_mathieuB_succ (by omega) q)
    (fun j => ?_) (fun k hk => ?_)
  · simpa using this
  · obtain ⟨k, hk, hk1, hw⟩ := exists_abs_mathieuB_sub_sq_le (m := j + 1) (by omega) q
    exact ⟨k - 1, by omega, by rw [show k - 1 + 1 = k by omega]; exact hw⟩
  · obtain ⟨c, hc, hL, hR⟩ := hE k (Finset.mem_range.2 (by omega))
    obtain ⟨m', hm'0, hm', rfl⟩ := exists_mathieuB_eq_of_mem_mathieuSpecB hc
    obtain ⟨k', hk', hk'1, hw⟩ := exists_abs_mathieuB_sub_sq_le hm'0 q
    have hL' : (if k + 1 = 0 then (-1 : ℝ) else (((k + 1 : ℕ) : ℝ) - 1) ^ 2) < mathieuB m' q := by
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact hL
    have := eq_of_abs_sub_sq_le_of_mem_window hq (hk'.trans hm') hL' hR hw
    subst this
    obtain ⟨m'', rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
    exact ⟨m'', hw⟩

/-! ### Eigenvalue estimates for the four classes -/

/-- Distinct squares of the same parity are separated: `|(2i+c)² - (2n+c)²| ≥ 4` for `i ≠ n`. -/
theorem four_le_abs_sq_sub_sq {i n : ℕ} (h : i ≠ n) (c : ℕ) :
    4 ≤ |(((2 * i + c : ℕ) : ℝ)) ^ 2 - (((2 * n + c : ℕ) : ℝ)) ^ 2| := by
  rcases lt_or_gt_of_ne h with h' | h'
  · have : ((2 * i + c : ℕ) : ℝ) + 2 ≤ ((2 * n + c : ℕ) : ℝ) := by exact_mod_cast (by omega)
    rw [abs_sub_comm, abs_of_nonneg (by nlinarith [(Nat.cast_nonneg (2 * i + c) : (0 : ℝ) ≤ _)])]
    nlinarith [(Nat.cast_nonneg (2 * i + c) : (0 : ℝ) ≤ _)]
  · have : ((2 * n + c : ℕ) : ℝ) + 2 ≤ ((2 * i + c : ℕ) : ℝ) := by exact_mod_cast (by omega)
    rw [abs_of_nonneg (by nlinarith [(Nat.cast_nonneg (2 * n + c) : (0 : ℝ) ≤ _)])]
    nlinarith [(Nat.cast_nonneg (2 * n + c) : (0 : ℝ) ≤ _)]

/-- Triangle-inequality gap: if `|x - y| ≤ 4|q| < 1/2`, `|z - y| ≥ 4` and `|e| ≤ |q|`,
then `|x - (z + e)| ≥ 1`. -/
theorem one_le_abs_sub_add_of_gap {x y z e q : ℝ} (hq : |q| < 1 / 8) (h1 : |x - y| ≤ 4 * |q|)
    (h2 : 4 ≤ |z - y|) (he : |e| ≤ |q|) : 1 ≤ |x - (z + e)| := by
  have := abs_add_three (-(x - (z + e))) (x - y) (-e)
  rw [show -(x - (z + e)) + (x - y) + -e = z - y by ring, abs_neg, abs_neg] at this
  linarith

/-- A real function whose complex cast is `O(k)` is itself `O(k)`. -/
theorem isBigO_of_ofReal_isBigO {f : ℝ → ℝ} {g : ℝ → ℂ} {k : ℝ → ℝ} {l : Filter ℝ}
    (h : g =O[l] k) (he : ∀ q, ((f q : ℝ) : ℂ) = g q) : f =O[l] k := by
  have : (fun q => ((f q : ℝ) : ℂ)) =O[l] k := by simpa only [he] using h
  rw [← isBigO_norm_left] at this ⊢
  simpa only [Complex.norm_real] using this

/-- If `f(q) = q^e s(q)` with `s` continuous and `e' ≤ e`, then `f = O(q^{e'})` at `0`. -/
theorem isBigO_pow_of_eq_pow_mul {f s : ℝ → ℂ} {e e' : ℕ} (he : e' ≤ e)
    (h : ∀ q : ℝ, f q = (q : ℂ) ^ e * s q) (hs : Continuous s) :
    f =O[𝓝 0] (fun q : ℝ => q ^ e') := by
  have h1 : s =O[𝓝 0] (fun _ => (1 : ℝ)) := (hs.tendsto 0).isBigO_one ℝ
  have h2 : (fun q : ℝ => (q : ℂ) ^ e) =O[𝓝 0] (fun q : ℝ => q ^ e) :=
    isBigO_of_le _ fun q => by simp [norm_pow]
  have := (h2.mul h1).trans (pow_isBigO_pow_of_le (by omega : e' ≤ e) |>.congr_left (fun q => by
    simp))
  simpa only [mul_one, ← h] using this

/-- A continuous function is `O(1)` at `0`. -/
theorem isBigO_one_of_continuous {s : ℝ → ℂ} (hs : Continuous s) :
    s =O[𝓝 0] (fun _ => (1 : ℝ)) := (hs.tendsto 0).isBigO_one ℝ

/-- Eigenvalue estimate for `a_{2n}(q)` from a trial vector (recurrence 28.4.5). -/
theorem mathieuA_even_sub_isBigO_of_trial (n : ℕ) {N K : ℕ} (hnN : n < N) {p : ℝ → ℂ} {v : ℝ → ℕ → ℂ}
    (hvN : ∀ q, v q N = 0) (hvN1 : ∀ q, v q (N + 1) = 0) (hvn : ∀ q, v q n = 1)
    (hv : ∀ i < N + 1, (fun q => v q i) =O[𝓝 0] (fun _ => (1 : ℝ)))
    (hr : ∀ i < N + 1, (fun q : ℝ => recurrenceOperator (fun i => 4 * (i : ℂ) ^ 2) 2 q (v q) i -
      p q * v q i) =O[𝓝 0] (fun q : ℝ => q ^ (K - Nat.dist i n))) :
    (fun q : ℝ => (mathieuA (2 * n) q : ℂ) - p q) =O[𝓝 0] (fun q : ℝ => q ^ K) := by
  refine eigenvalue_sub_isBigO_of_trial (d := fun _ i => 4 * (i : ℂ) ^ 2) (β := 2) (by norm_num) (by norm_num)
    (A := fun q i => mathieuFourierA (2 * n) (2 * i) q) hnN
    (Eventually.of_forall (solvesRecurrence_mathieuFourierA_even n)) (Eventually.of_forall (tendsto_mathieuFourierA_even n))
    (Eventually.of_forall (exists_mathieuFourierA_even_ne_zero n)) ?_ hvN hvN1 hvn hv hr
  filter_upwards [eventually_abs_mathieuA_sub_sq_le (2 * n), eventually_abs_lt_one_div_eight] with q h1 h2
  intro i hi
  rw [show (4 * (i : ℂ) ^ 2) = ((((2 * i + 0 : ℕ) : ℝ) ^ 2 + 0 : ℝ) : ℂ) by push_cast; ring,
    norm_ofReal_sub_ofReal]
  exact one_le_abs_sub_add_of_gap h2 (by simpa using h1) (four_le_abs_sq_sub_sq hi 0) (by simp)

/-- Eigenvalue estimate for `a_{2n+1}(q)` from a trial vector (recurrence 28.4.6). -/
theorem mathieuA_odd_sub_isBigO_of_trial (n : ℕ) {N K : ℕ} (hnN : n < N) {p : ℝ → ℂ} {v : ℝ → ℕ → ℂ}
    (hvN : ∀ q, v q N = 0) (hvN1 : ∀ q, v q (N + 1) = 0) (hvn : ∀ q, v q n = 1)
    (hv : ∀ i < N + 1, (fun q => v q i) =O[𝓝 0] (fun _ => (1 : ℝ)))
    (hr : ∀ i < N + 1, (fun q : ℝ => recurrenceOperator (fun i => (2 * (i : ℂ) + 1) ^ 2 +
      if i = 0 then (q : ℂ) else 0) 1 q (v q) i - p q * v q i) =O[𝓝 0]
      (fun q : ℝ => q ^ (K - Nat.dist i n))) :
    (fun q : ℝ => (mathieuA (2 * n + 1) q : ℂ) - p q) =O[𝓝 0] (fun q : ℝ => q ^ K) := by
  refine eigenvalue_sub_isBigO_of_trial (d := fun q i => (2 * (i : ℂ) + 1) ^ 2 + if i = 0 then (q : ℂ) else 0)
    (β := 1) (by norm_num) (by norm_num)
    (A := fun q i => mathieuFourierA (2 * n + 1) (2 * i + 1) q) hnN
    (Eventually.of_forall (solvesRecurrence_mathieuFourierA_odd n)) (Eventually.of_forall (tendsto_mathieuFourierA_odd n))
    (Eventually.of_forall (exists_mathieuFourierA_odd_ne_zero n)) ?_ hvN hvN1 hvn hv hr
  filter_upwards [eventually_abs_mathieuA_sub_sq_le (2 * n + 1), eventually_abs_lt_one_div_eight] with q h1 h2
  intro i hi
  rw [show ((2 * (i : ℂ) + 1) ^ 2 + if i = 0 then (q : ℂ) else 0) =
      ((((2 * i + 1 : ℕ) : ℝ) ^ 2 + (if i = 0 then q else 0) : ℝ) : ℂ) by
      split_ifs <;> push_cast <;> ring, norm_ofReal_sub_ofReal]
  exact one_le_abs_sub_add_of_gap h2 (by simpa using h1) (four_le_abs_sq_sub_sq hi 1) (by split_ifs <;> simp)

/-- Eigenvalue estimate for `b_{2n+1}(q)` from a trial vector (recurrence 28.4.7). -/
theorem mathieuB_odd_sub_isBigO_of_trial (n : ℕ) {N K : ℕ} (hnN : n < N) {p : ℝ → ℂ} {v : ℝ → ℕ → ℂ}
    (hvN : ∀ q, v q N = 0) (hvN1 : ∀ q, v q (N + 1) = 0) (hvn : ∀ q, v q n = 1)
    (hv : ∀ i < N + 1, (fun q => v q i) =O[𝓝 0] (fun _ => (1 : ℝ)))
    (hr : ∀ i < N + 1, (fun q : ℝ => recurrenceOperator (fun i => (2 * (i : ℂ) + 1) ^ 2 -
      if i = 0 then (q : ℂ) else 0) 1 q (v q) i - p q * v q i) =O[𝓝 0]
      (fun q : ℝ => q ^ (K - Nat.dist i n))) :
    (fun q : ℝ => (mathieuB (2 * n + 1) q : ℂ) - p q) =O[𝓝 0] (fun q : ℝ => q ^ K) := by
  refine eigenvalue_sub_isBigO_of_trial (d := fun q i => (2 * (i : ℂ) + 1) ^ 2 - if i = 0 then (q : ℂ) else 0)
    (β := 1) (by norm_num) (by norm_num)
    (A := fun q i => mathieuFourierB (2 * n + 1) (2 * i + 1) q) hnN
    (Eventually.of_forall (solvesRecurrence_mathieuFourierB_odd n)) (Eventually.of_forall (tendsto_mathieuFourierB_odd n))
    (Eventually.of_forall (exists_mathieuFourierB_odd_ne_zero n)) ?_ hvN hvN1 hvn hv hr
  filter_upwards [eventually_abs_mathieuB_sub_sq_le (m := 2 * n + 1) (by omega), eventually_abs_lt_one_div_eight]
    with q h1 h2
  intro i hi
  rw [show ((2 * (i : ℂ) + 1) ^ 2 - if i = 0 then (q : ℂ) else 0) =
      ((((2 * i + 1 : ℕ) : ℝ) ^ 2 + -(if i = 0 then q else 0) : ℝ) : ℂ) by
      split_ifs <;> push_cast <;> ring, norm_ofReal_sub_ofReal]
  exact one_le_abs_sub_add_of_gap h2 (by simpa using h1) (four_le_abs_sq_sub_sq hi 1) (by split_ifs <;> simp)

/-- Eigenvalue estimate for `b_{2n+2}(q)` from a trial vector (recurrence 28.4.8). -/
theorem mathieuB_even_sub_isBigO_of_trial (n : ℕ) {N K : ℕ} (hnN : n < N) {p : ℝ → ℂ} {v : ℝ → ℕ → ℂ}
    (hvN : ∀ q, v q N = 0) (hvN1 : ∀ q, v q (N + 1) = 0) (hvn : ∀ q, v q n = 1)
    (hv : ∀ i < N + 1, (fun q => v q i) =O[𝓝 0] (fun _ => (1 : ℝ)))
    (hr : ∀ i < N + 1, (fun q : ℝ => recurrenceOperator (fun i => (2 * (i : ℂ) + 2) ^ 2) 1 q (v q) i -
      p q * v q i) =O[𝓝 0] (fun q : ℝ => q ^ (K - Nat.dist i n))) :
    (fun q : ℝ => (mathieuB (2 * n + 2) q : ℂ) - p q) =O[𝓝 0] (fun q : ℝ => q ^ K) := by
  refine eigenvalue_sub_isBigO_of_trial (d := fun _ i => (2 * (i : ℂ) + 2) ^ 2) (β := 1) (by norm_num)
    (by norm_num) (A := fun q i => mathieuFourierB (2 * n + 2) (2 * i + 2) q) hnN
    (Eventually.of_forall (solvesRecurrence_mathieuFourierB_even n)) (Eventually.of_forall (tendsto_mathieuFourierB_even n))
    (Eventually.of_forall (exists_mathieuFourierB_even_ne_zero n)) ?_ hvN hvN1 hvn hv hr
  filter_upwards [eventually_abs_mathieuB_sub_sq_le (m := 2 * n + 2) (by omega), eventually_abs_lt_one_div_eight]
    with q h1 h2
  intro i hi
  rw [show ((2 * (i : ℂ) + 2) ^ 2) = ((((2 * i + 2 : ℕ) : ℝ) ^ 2 + 0 : ℝ) : ℂ) by
      push_cast; ring, norm_ofReal_sub_ofReal]
  exact one_le_abs_sub_add_of_gap h2 (by simpa using h1) (four_le_abs_sq_sub_sq hi 2) (by simp)

end DLMF.Mathieu
