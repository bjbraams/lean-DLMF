/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.P3qJacobi
public import DLMF.Mathieu.FourierSeries

/-!
# The eigenvalues `a_n(q)`, `b_n(q)` near `q = 0`

The Fourier coefficients of `ce_n`, `se_n` solve the recurrences 28.4.5–28.4.8, which are
instances of the recurrences of `DLMF.Mathieu.P3qJacobi` (`p3q_rec_AE`, `p3q_rec_AO`,
`p3q_rec_BO`, `p3q_rec_BE`). Their maximum principle puts every eigenvalue within `4|q|` of a
square `k²` of the right parity (`p3q_window_A`, `p3q_window_B`). Together with

* the interlacing `a_m(q) < a_{m+1}(q)`, `b_m(q) < b_{m+1}(q)` (Sturm oscillation:
  `p3q_mathieuA_lt_succ`, `p3q_mathieuB_lt_succ`), and
* for small `q`, a sign change of the boundary functions `w_I'(π/2)`, `w_I(π/2)`,
  `w_II'(π/2)`, `w_II(π/2)` between consecutive squares (`p3q_exists_spec_A`,
  `p3q_exists_spec_B`, from their explicit values at `q = 0`),

this identifies the window of `a_m(q)`: `|a_m(q) - m²| ≤ 4|q|` and `|b_m(q) - m²| ≤ 4|q|` for
small `q` (`p3q_mathieuA_near`, `p3q_mathieuB_near`). In particular `a_m`, `b_m` are continuous
at `q = 0`.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

/-! ### The recurrences 28.4.5–28.4.8 as `p3qRec` -/

/-- The coefficients `A^{2n}_{2i}` satisfy the recurrence 28.4.5 in `p3qRec` form,
with diagonal `4i²` and `β = 2`. -/
theorem p3q_rec_AE (n : ℕ) (q : ℝ) :
    p3qRec (fun i => 4 * (i : ℂ) ^ 2) 2 q (mathieuA (2 * n) q)
      (fun i => mathieuFourierA (2 * n) (2 * i) q) := by
  intro i
  rcases i with _ | _ | j
  · have := mathieuFourierA_even_rec_zero n q
    simp only [p3qL, p3qLo]; push_cast
    linear_combination -this
  · have := mathieuFourierA_even_rec_one n q
    simp only [p3qL, p3qLo]; push_cast; norm_num
    linear_combination -this
  · have := mathieuFourierA_even_rec n q (m := j + 2) (by omega)
    simp only [p3qL, p3qLo]
    rw [show 2 * (j + 2) - 2 = 2 * (j + 1) by omega, show 2 * (j + 2) + 2 = 2 * (j + 2 + 1) by ring]
      at this
    push_cast at this ⊢
    linear_combination -this

/-- The coefficients `A^{2n+1}_{2i+1}` satisfy 28.4.6 in `p3qRec` form, with diagonal
`(2i+1)² + q δ_{i0}` and `β = 1`. -/
theorem p3q_rec_AO (n : ℕ) (q : ℝ) :
    p3qRec (fun i => (2 * (i : ℂ) + 1) ^ 2 + if i = 0 then (q : ℂ) else 0) 1 q
      (mathieuA (2 * n + 1) q) (fun i => mathieuFourierA (2 * n + 1) (2 * i + 1) q) := by
  intro i
  rcases i with _ | j
  · have := mathieuFourierA_odd_rec_zero n q
    simp only [p3qL, p3qLo]; push_cast; norm_num
    linear_combination -this
  · have := mathieuFourierA_odd_rec n q (m := j + 1) (by omega)
    rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega,
      show 2 * (j + 1) + 3 = 2 * (j + 1 + 1) + 1 by ring]
      at this
    rcases j with _ | j
    · simp only [p3qL, p3qLo]; push_cast at this ⊢; norm_num at this ⊢
      linear_combination -this
    · simp only [p3qL, p3qLo]; push_cast at this ⊢; norm_num at this ⊢
      linear_combination -this

/-- The coefficients `B^{2n+1}_{2i+1}` satisfy 28.4.7 in `p3qRec` form, with diagonal
`(2i+1)² - q δ_{i0}` and `β = 1`. -/
theorem p3q_rec_BO (n : ℕ) (q : ℝ) :
    p3qRec (fun i => (2 * (i : ℂ) + 1) ^ 2 - if i = 0 then (q : ℂ) else 0) 1 q
      (mathieuB (2 * n + 1) q) (fun i => mathieuFourierB (2 * n + 1) (2 * i + 1) q) := by
  intro i
  rcases i with _ | j
  · have := mathieuFourierB_odd_rec_zero n q
    simp only [p3qL, p3qLo]; push_cast; norm_num
    linear_combination -this
  · have := mathieuFourierB_odd_rec n q (m := j + 1) (by omega)
    rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega,
      show 2 * (j + 1) + 3 = 2 * (j + 1 + 1) + 1 by ring]
      at this
    rcases j with _ | j
    · simp only [p3qL, p3qLo]; push_cast at this ⊢; norm_num at this ⊢
      linear_combination -this
    · simp only [p3qL, p3qLo]; push_cast at this ⊢; norm_num at this ⊢
      linear_combination -this

/-- The coefficients `B^{2n+2}_{2i+2}` satisfy 28.4.8 in `p3qRec` form, with diagonal
`(2i+2)²` and `β = 1`. -/
theorem p3q_rec_BE (n : ℕ) (q : ℝ) :
    p3qRec (fun i => (2 * (i : ℂ) + 2) ^ 2) 1 q
      (mathieuB (2 * n + 2) q) (fun i => mathieuFourierB (2 * n + 2) (2 * i + 2) q) := by
  intro i
  rcases i with _ | j
  · have := mathieuFourierB_even_rec_zero n q
    simp only [p3qL, p3qLo]; push_cast; norm_num
    linear_combination -this
  · have := mathieuFourierB_even_rec n q (m := j + 2) (by omega)
    rw [show 2 * (j + 2) - 2 = 2 * j + 2 by omega,
      show 2 * (j + 2) + 2 = 2 * (j + 1 + 1) + 2 by ring,
      show 2 * (j + 2) = 2 * (j + 1) + 2 by ring] at this
    rcases j with _ | j
    · simp only [p3qL, p3qLo]; push_cast at this ⊢; norm_num at this ⊢
      linear_combination -this
    · simp only [p3qL, p3qLo]; push_cast at this ⊢
      linear_combination -this


/-- Some Fourier coefficient `A^n_m(q)` is nonzero (since `ce_n(0, q) > 0`). -/
lemma p3q_fourierA_ne (n : ℕ) (q : ℝ) : ∃ m, mathieuFourierA n m q ≠ 0 := by
  by_contra h
  push Not at h
  have hs := p1a2_hasSum_mathieuCe n q 0
  simp only [h, zero_mul] at hs
  have := hs.unique hasSum_zero
  rw [mathieuCe_zero, Complex.ofReal_eq_zero] at this
  exact (mathieuCeZero_pos n q).ne' this

/-- For `n ≥ 1`, some Fourier coefficient `B^n_m(q)` is nonzero (since `se_n'(0, q) > 0`). -/
lemma p3q_fourierB_ne {n : ℕ} (hn : n ≠ 0) (q : ℝ) : ∃ m, mathieuFourierB n m q ≠ 0 := by
  by_contra h
  push Not at h
  have hs := (mathieuFourier_sign n q).2.1 hn
  simp only [h, mul_zero] at hs
  have := hs.unique hasSum_zero
  rw [deriv_mathieuSe_zero, Complex.ofReal_eq_zero] at this
  exact (mathieuSeDerivZero_pos n q).ne' this

/-- Some coefficient `A^{2n}_{2i}(q)` is nonzero. -/
theorem p3q_ne_AE (n : ℕ) (q : ℝ) : ∃ i, mathieuFourierA (2 * n) (2 * i) q ≠ 0 := by
  obtain ⟨m, hm⟩ := p3q_fourierA_ne (2 * n) q
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · exact ⟨j, hm⟩
  · exact absurd (p1a2_fourierA_even_odd n j q) hm

/-- Some coefficient `A^{2n+1}_{2i+1}(q)` is nonzero. -/
theorem p3q_ne_AO (n : ℕ) (q : ℝ) : ∃ i, mathieuFourierA (2 * n + 1) (2 * i + 1) q ≠ 0 := by
  obtain ⟨m, hm⟩ := p3q_fourierA_ne (2 * n + 1) q
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · exact absurd (p1a2_fourierA_odd_even n j q) hm
  · exact ⟨j, hm⟩

/-- Some coefficient `B^{2n+1}_{2i+1}(q)` is nonzero. -/
theorem p3q_ne_BO (n : ℕ) (q : ℝ) : ∃ i, mathieuFourierB (2 * n + 1) (2 * i + 1) q ≠ 0 := by
  obtain ⟨m, hm⟩ := p3q_fourierB_ne (n := 2 * n + 1) (by omega) q
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · exact absurd (p1a2_fourierB_odd_even n j q) hm
  · exact ⟨j, hm⟩

/-- Some coefficient `B^{2n+2}_{2i+2}(q)` is nonzero. -/
theorem p3q_ne_BE (n : ℕ) (q : ℝ) : ∃ i, mathieuFourierB (2 * n + 2) (2 * i + 2) q ≠ 0 := by
  obtain ⟨m, hm⟩ := p3q_fourierB_ne (n := 2 * n + 2) (by omega) q
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · rcases j with _ | j
    · exact absurd (p1a2_fourierB_zero _ q) hm
    · exact ⟨j, by rw [show 2 * j + 2 = 2 * (j + 1) by ring]; exact hm⟩
  · exact absurd (p1a2_fourierB_even_odd n j q) hm

/-- A sequence with `|c_m| ≤ C e^{-m}` tends to `0` along any reindexing `f` with `i ≤ f i`. -/
lemma p3q_tendsto_of_decay {c : ℕ → ℂ}
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
theorem p3q_lim_AE (n : ℕ) (q : ℝ) :
    Tendsto (fun i => mathieuFourierA (2 * n) (2 * i) q) atTop (𝓝 0) :=
  p3q_tendsto_of_decay (p2f_fourierA_decay _ q 1) (fun i => by omega)

/-- `A^{2n+1}_{2i+1}(q) → 0` as `i → ∞`. -/
theorem p3q_lim_AO (n : ℕ) (q : ℝ) :
    Tendsto (fun i => mathieuFourierA (2 * n + 1) (2 * i + 1) q) atTop (𝓝 0) :=
  p3q_tendsto_of_decay (p2f_fourierA_decay _ q 1) (fun i => by omega)

/-- `B^{2n+1}_{2i+1}(q) → 0` as `i → ∞`. -/
theorem p3q_lim_BO (n : ℕ) (q : ℝ) :
    Tendsto (fun i => mathieuFourierB (2 * n + 1) (2 * i + 1) q) atTop (𝓝 0) :=
  p3q_tendsto_of_decay (p2f_fourierB_decay (by omega) q 1) (fun i => by omega)

/-- `B^{2n+2}_{2i+2}(q) → 0` as `i → ∞`. -/
theorem p3q_lim_BE (n : ℕ) (q : ℝ) :
    Tendsto (fun i => mathieuFourierB (2 * n + 2) (2 * i + 2) q) atTop (𝓝 0) :=
  p3q_tendsto_of_decay (p2f_fourierB_decay (by omega) q 1) (fun i => by omega)

/-- For real `x, y`, `‖(x : ℂ) - y‖ = |x - y|`. -/
theorem p3q_norm_ofReal_sub (x y : ℝ) : ‖(x : ℂ) - (y : ℂ)‖ = |x - y| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- **Window lemma** for `a_m(q)` (maximum principle for the Fourier coefficients): `a_m(q)`
lies within `4|q|` of `k²` for some `k ≡ m (mod 2)`. -/
lemma p3q_window_A (m : ℕ) (q : ℝ) :
    ∃ k : ℕ, k % 2 = m % 2 ∧ |mathieuA m q - (k : ℝ) ^ 2| ≤ 4 * |q| := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨i, hi⟩ := p3q_window (by norm_num) (p3q_rec_AE n q) (p3q_lim_AE n q) (p3q_ne_AE n q)
    refine ⟨2 * i, by omega, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs,
      show (4 * (i : ℂ) ^ 2) = (((2 * i : ℕ) : ℝ) ^ 2 : ℝ) by push_cast; ring,
      p3q_norm_ofReal_sub] at hi
    linarith [abs_nonneg q]
  · obtain ⟨i, hi⟩ := p3q_window (by norm_num) (p3q_rec_AO n q) (p3q_lim_AO n q) (p3q_ne_AO n q)
    refine ⟨2 * i + 1, by omega, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs] at hi
    have e : ((2 * (i : ℂ) + 1) ^ 2 + if i = 0 then (q : ℂ) else 0) =
        ((((2 * i + 1 : ℕ) : ℝ) ^ 2 + if i = 0 then q else 0 : ℝ) : ℂ) := by
      split_ifs <;> push_cast <;> ring
    rw [e, p3q_norm_ofReal_sub] at hi
    have : |(if i = 0 then q else 0)| ≤ |q| := by split_ifs <;> simp
    have h3 := abs_sub_abs_le_abs_sub (mathieuA (2 * n + 1) q - ((2 * i + 1 : ℕ) : ℝ) ^ 2)
      (if i = 0 then q else 0)
    rw [sub_sub] at h3
    linarith

/-- **Window lemma** for `b_m(q)`, `m ≥ 1`. -/
lemma p3q_window_B {m : ℕ} (hm : m ≠ 0) (q : ℝ) :
    ∃ k : ℕ, k % 2 = m % 2 ∧ 1 ≤ k ∧ |mathieuB m q - (k : ℝ) ^ 2| ≤ 4 * |q| := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [show 2 * (n + 1) = 2 * n + 2 by ring]
    obtain ⟨i, hi⟩ := p3q_window (by norm_num) (p3q_rec_BE n q) (p3q_lim_BE n q) (p3q_ne_BE n q)
    refine ⟨2 * i + 2, by omega, by omega, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs,
      show ((2 * (i : ℂ) + 2) ^ 2) = (((2 * i + 2 : ℕ) : ℝ) ^ 2 : ℝ) by push_cast; ring,
      p3q_norm_ofReal_sub] at hi
    linarith [abs_nonneg q]
  · obtain ⟨i, hi⟩ := p3q_window (by norm_num) (p3q_rec_BO n q) (p3q_lim_BO n q) (p3q_ne_BO n q)
    refine ⟨2 * i + 1, by omega, by omega, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs] at hi
    have e : ((2 * (i : ℂ) + 1) ^ 2 - if i = 0 then (q : ℂ) else 0) =
        ((((2 * i + 1 : ℕ) : ℝ) ^ 2 - if i = 0 then q else 0 : ℝ) : ℂ) := by
      split_ifs <;> push_cast <;> ring
    rw [e, p3q_norm_ofReal_sub] at hi
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
lemma p3q_interlace {V : ℝ → ℝ} {B L : ℝ} (hV : Continuous V) (hB : ∀ x, |V x| ≤ B)
    (hL : 0 < L) (odd0 : Bool) {e d : ℝ} (he : e ∈ ODE.p2lSpec V L odd0 false)
    (hd : d ∈ ODE.p2lSpec V L odd0 true) :
    ((ODE.p2lSpec V L odd0 false ∩ Iio e).ncard ≤ (ODE.p2lSpec V L odd0 true ∩ Iio d).ncard →
      e < d) ∧
    ((ODE.p2lSpec V L odd0 true ∩ Iio d).ncard < (ODE.p2lSpec V L odd0 false ∩ Iio e).ncard →
      d < e) := by
  have hfinD := ODE.p2l_spec_Iio_finite hV hB hL odd0 true
  have hfinN := ODE.p2l_spec_Iio_finite hV hB hL odd0 false
  rw [ODE.p2s_spec_eq_dir hV] at hd hfinD ⊢
  rw [ODE.p2s_spec_eq_neu hV] at he hfinN ⊢
  have key := (ODE.p2s_neumann_count hV hB hL hfinD hfinN he).symm.trans
    (ODE.p2s_dirichlet_count hV hB hL hfinD e)
  set D := {e | ODE.p2lY V odd0 e L = 0}
  set N := {e | deriv (ODE.p2lY V odd0 e) L = 0}
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
    · exact ODE.p2s_ne_of_deriv hV he hd


/-- `a_m(q)` lies in its Sturm–Liouville spectrum on `[0, π/2]` and has exactly `⌊m/2⌋`
smaller spectral values there. -/
lemma p3q_A_mem (m : ℕ) (q : ℝ) :
    mathieuA m q ∈ ODE.p2lSpec (fun x : ℝ => 2 * q * Real.cos (2 * x)) (π / 2) false
      (if Even m then false else true) ∧
    (ODE.p2lSpec (fun x : ℝ => 2 * q * Real.cos (2 * x)) (π / 2) false
      (if Even m then false else true) ∩ Iio (mathieuA m q)).ncard = m / 2 := by
  have h := mathieuA_spec m q
  rw [p2s_specA] at h
  exact ⟨h.1, p2s_ncard_of_encard h.2⟩

/-- For `m ≥ 1`, `b_m(q)` lies in its Sturm–Liouville spectrum on `[0, π/2]` and has exactly
`⌊(m-1)/2⌋` smaller spectral values there. -/
lemma p3q_B_mem {m : ℕ} (hm : m ≠ 0) (q : ℝ) :
    mathieuB m q ∈ ODE.p2lSpec (fun x : ℝ => 2 * q * Real.cos (2 * x)) (π / 2) true
      (if Even m then true else false) ∧
    (ODE.p2lSpec (fun x : ℝ => 2 * q * Real.cos (2 * x)) (π / 2) true
      (if Even m then true else false) ∩ Iio (mathieuB m q)).ncard = (m - 1) / 2 := by
  have h := mathieuB_spec hm q
  rw [p2s_specB] at h
  exact ⟨h.1, p2s_ncard_of_encard h.2⟩

/-- `a_m(q) < a_{m+1}(q)` for real `q` (interlacing of the two spectra with `w'(0) = 0`). -/
lemma p3q_mathieuA_lt_succ (m : ℕ) (q : ℝ) : mathieuA m q < mathieuA (m + 1) q := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · have h1 := p3q_A_mem (2 * j) q
    have h2 := p3q_A_mem (2 * j + 1) q
    simp only [even_two_mul, ↓reduceIte, Nat.not_even_bit1] at h1 h2
    exact (p3q_interlace (p2s_hV q) (p2s_hB q) (by positivity) false h1.1 h2.1).1
      (by rw [h1.2, h2.2]; omega)
  · have h1 := p3q_A_mem (2 * j + 2) q
    have h2 := p3q_A_mem (2 * j + 1) q
    have he : Even (2 * j + 2) := ⟨j + 1, by ring⟩
    simp only [he, ↓reduceIte, Nat.not_even_bit1] at h1 h2
    exact (p3q_interlace (p2s_hV q) (p2s_hB q) (by positivity) false h1.1 h2.1).2
      (by rw [h1.2, h2.2]; omega)

/-- `b_m(q) < b_{m+1}(q)` for real `q`, `m ≥ 1`. -/
lemma p3q_mathieuB_lt_succ {m : ℕ} (hm : m ≠ 0) (q : ℝ) : mathieuB m q < mathieuB (m + 1) q := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have h1 := p3q_B_mem (m := 2 * (j + 1) + 1) (by omega) q
    have h2 := p3q_B_mem (m := 2 * (j + 1)) (by omega) q
    have he : Even (2 * (j + 1)) := even_two_mul _
    simp only [he, ↓reduceIte, Nat.not_even_bit1] at h1 h2
    exact (p3q_interlace (p2s_hV q) (p2s_hB q) (by positivity) true h1.1 h2.1).2
      (by rw [h1.2, h2.2]; omega)
  · have h1 := p3q_B_mem (m := 2 * j + 1) (by omega) q
    have h2 := p3q_B_mem (m := 2 * j + 2) (by omega) q
    have he : Even (2 * j + 2) := ⟨j + 1, by ring⟩
    simp only [he, ↓reduceIte, Nat.not_even_bit1] at h1 h2
    exact (p3q_interlace (p2s_hV q) (p2s_hB q) (by positivity) true h1.1 h2.1).1
      (by rw [h1.2, h2.2]; omega)

/-! ### Identification of the window -/

/-- If `x` is within `4c < 1/2` of both `(k+s)²` and `(k'+s)²`, then `k = k'`. -/
lemma p3q_sq_eq_of_close {k k' s : ℕ} {x c : ℝ} (hc : c < 1 / 8)
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
lemma p3q_comb {x : ℕ → ℝ} {c : ℝ} {s m : ℕ} (hc : c < 1 / 8) (hx : StrictMono x)
    (hw : ∀ j, ∃ k : ℕ, k % 2 = j % 2 ∧ |x j - ((k + s : ℕ) : ℝ) ^ 2| ≤ 4 * c)
    (hE : ∀ k ≤ m, ∃ j, |x j - ((k + s : ℕ) : ℝ) ^ 2| ≤ 4 * c) :
    |x m - ((m + s : ℕ) : ℝ) ^ 2| ≤ 4 * c := by
  choose κ hκp hκ using hw
  have huniq : ∀ j k, |x j - ((k + s : ℕ) : ℝ) ^ 2| ≤ 4 * c → k = κ j := fun j k h =>
    p3q_sq_eq_of_close hc h (hκ j)
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
lemma p3q_ivt {G : ℝ → ℝ → ℝ} (hGa : ∀ q, Continuous fun a => G a q)
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
lemma p3q_diff_I (q z : ℂ) :
    Differentiable ℂ (fun a => mathieuWI a q z) ∧
      Differentiable ℂ (fun a => deriv (mathieuWI a q) z) :=
  p2f_differentiable_param (W := mathieuWI) isMathieuSolution_mathieuWI
    (fun a q => (mathieuWI_spec a q).2.1) (fun a q => (mathieuWI_spec a q).2.2) q z

/-- `w_II(z; a, q)` and its `z`-derivative are entire functions of `a`. -/
lemma p3q_diff_II (q z : ℂ) :
    Differentiable ℂ (fun a => mathieuWII a q z) ∧
      Differentiable ℂ (fun a => deriv (mathieuWII a q) z) :=
  p2f_differentiable_param (W := mathieuWII) isMathieuSolution_mathieuWII
    (fun a q => (mathieuWII_spec a q).2.1) (fun a q => (mathieuWII_spec a q).2.2) q z

/-- `w_I(z; a, q)` and its `z`-derivative are entire functions of `q`. -/
lemma p3q_diff_I_q (a z : ℂ) :
    Differentiable ℂ (fun q => mathieuWI a q z) ∧
      Differentiable ℂ (fun q => deriv (mathieuWI a q) z) :=
  p2f_differentiable_param_q (W := mathieuWI) isMathieuSolution_mathieuWI
    (fun a q => (mathieuWI_spec a q).2.1) (fun a q => (mathieuWI_spec a q).2.2) a z

/-- `w_II(z; a, q)` and its `z`-derivative are entire functions of `q`. -/
lemma p3q_diff_II_q (a z : ℂ) :
    Differentiable ℂ (fun q => mathieuWII a q z) ∧
      Differentiable ℂ (fun q => deriv (mathieuWII a q) z) :=
  p2f_differentiable_param_q (W := mathieuWII) isMathieuSolution_mathieuWII
    (fun a q => (mathieuWII_spec a q).2.1) (fun a q => (mathieuWII_spec a q).2.2) a z

/-- For an entire `f`, `x ↦ Re f(x)` is continuous on `ℝ`. -/
lemma p3q_cont_re {f : ℂ → ℂ} (hf : Differentiable ℂ f) : Continuous fun x : ℝ => (f x).re :=
  Complex.continuous_re.comp (hf.continuous.comp Complex.continuous_ofReal)

/-- Cast identity `(s : ℂ) (π/2) = ((s π/2 : ℝ) : ℂ)`. -/
lemma p3q_ofReal_mul_half_pi (s : ℝ) : (s : ℂ) * ((π : ℂ) / 2) = ((s * (π / 2) : ℝ) : ℂ) := by
  push_cast; ring

/-- At `q = 0`, `a = s²`: `Re w_I'(π/2) = -s sin(sπ/2)`. -/
lemma p3q_AE0 (s : ℝ) :
    (deriv (mathieuWI ((s ^ 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ)) ((π : ℂ) / 2)).re =
      -Real.sin (s * (π / 2)) * s := by
  rw [Complex.ofReal_zero, p1a1_deriv_mathieuWI_q_zero (s := (s : ℂ)) (by push_cast; ring),
    p3q_ofReal_mul_half_pi, ← Complex.ofReal_sin, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- At `q = 0`, `a = -1`: `Re w_I'(π/2) = sinh(π/2)`. -/
lemma p3q_AE0_neg :
    (deriv (mathieuWI ((-1 : ℝ) : ℂ) ((0 : ℝ) : ℂ)) ((π : ℂ) / 2)).re = Real.sinh (π / 2) := by
  rw [Complex.ofReal_zero, p1a1_deriv_mathieuWI_q_zero (s := I) (by push_cast; simp)]
  rw [show I * ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) * I by push_cast; ring, Complex.sin_mul_I,
    ← Complex.ofReal_sinh]
  rw [show -(((Real.sinh (π / 2) : ℝ) : ℂ) * I) * I = ((Real.sinh (π / 2) : ℝ) : ℂ) by
    linear_combination (-(((Real.sinh (π / 2) : ℝ) : ℂ))) * Complex.I_sq]
  exact Complex.ofReal_re _

/-- At `q = 0`, `a = s²`: `Re w_I(π/2) = cos(sπ/2)`. -/
lemma p3q_AO0 (s : ℝ) :
    (mathieuWI ((s ^ 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((π : ℂ) / 2)).re = Real.cos (s * (π / 2)) := by
  rw [Complex.ofReal_zero, p1a1_mathieuWI_q_zero (s := (s : ℂ)) (by push_cast; ring),
    p3q_ofReal_mul_half_pi, ← Complex.ofReal_cos, Complex.ofReal_re]

/-- At `q = 0`, `a = s²`: `Re w_II'(π/2) = cos(sπ/2)`. -/
lemma p3q_BO0 (s : ℝ) :
    (deriv (mathieuWII ((s ^ 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ)) ((π : ℂ) / 2)).re =
      Real.cos (s * (π / 2)) := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [show (((0 : ℝ) ^ 2 : ℝ) : ℂ) = 0 by simp, Complex.ofReal_zero,
      show mathieuWII 0 0 = fun z => z from funext p1a1_mathieuWII_zero_zero, deriv_id'']
    simp
  · rw [Complex.ofReal_zero, p1a1_deriv_mathieuWII_q_zero (s := (s : ℂ)) (by push_cast; ring)
      (by exact_mod_cast hs), p3q_ofReal_mul_half_pi, ← Complex.ofReal_cos, Complex.ofReal_re]

/-- At `q = 0`, `a = s²`, `s ≠ 0`: `Re w_II(π/2) = sin(sπ/2)/s`. -/
lemma p3q_BE0 {s : ℝ} (hs : s ≠ 0) :
    (mathieuWII ((s ^ 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((π : ℂ) / 2)).re = Real.sin (s * (π / 2)) / s := by
  rw [Complex.ofReal_zero, p1a1_mathieuWII_q_zero (s := (s : ℂ)) (by push_cast; ring)
    (by exact_mod_cast hs), p3q_ofReal_mul_half_pi, ← Complex.ofReal_sin, ← Complex.ofReal_div,
    Complex.ofReal_re]

/-- `sin((2i+1)π/2) = (-1)^i`. -/
lemma p3q_sin_odd (i : ℕ) : Real.sin (((2 * i + 1 : ℕ) : ℝ) * (π / 2)) = (-1) ^ i := by
  rw [show ((2 * i + 1 : ℕ) : ℝ) * (π / 2) = (i : ℝ) * π + π / 2 by push_cast; ring,
    Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]

/-- `cos(2i · π/2) = (-1)^i`. -/
lemma p3q_cos_even (i : ℕ) : Real.cos (((2 * i : ℕ) : ℝ) * (π / 2)) = (-1) ^ i := by
  rw [show ((2 * i : ℕ) : ℝ) * (π / 2) = (i : ℝ) * π by push_cast; ring, Real.cos_nat_mul_pi]


/-- A complex number fixed by conjugation with zero real part is `0`. -/
lemma p3q_real_eq_zero {z : ℂ} (hz : (starRingEnd ℂ) z = z) (h : z.re = 0) : z = 0 := by
  rw [← Complex.conj_eq_iff_re.1 hz, h, Complex.ofReal_zero]

/-- For real `a, q`, `w_I'(π/2; a, q)` is real (fixed by conjugation). -/
lemma p3q_dI_real (a q : ℝ) :
    (starRingEnd ℂ) (deriv (mathieuWI a q) ((π : ℂ) / 2)) =
      deriv (mathieuWI a q) ((π : ℂ) / 2) := by
  rw [← p2s_hpi]; exact p1a1_deriv_mathieuWI_real a q _

/-- For real `a, q`, `w_I(π/2; a, q)` is real (fixed by conjugation). -/
lemma p3q_I_real (a q : ℝ) :
    (starRingEnd ℂ) (mathieuWI a q ((π : ℂ) / 2)) = mathieuWI a q ((π : ℂ) / 2) := by
  rw [← p2s_hpi]; exact p1a1_mathieuWI_real a q _

/-- For real `a, q`, `w_II'(π/2; a, q)` is real (fixed by conjugation). -/
lemma p3q_dII_real (a q : ℝ) :
    (starRingEnd ℂ) (deriv (mathieuWII a q) ((π : ℂ) / 2)) =
      deriv (mathieuWII a q) ((π : ℂ) / 2) := by
  rw [← p2s_hpi]; exact p1a1_deriv_mathieuWII_real a q _

/-- For real `a, q`, `w_II(π/2; a, q)` is real (fixed by conjugation). -/
lemma p3q_II_real (a q : ℝ) :
    (starRingEnd ℂ) (mathieuWII a q ((π : ℂ) / 2)) = mathieuWII a q ((π : ℂ) / 2) := by
  rw [← p2s_hpi]; exact p1a1_mathieuWII_real a q _

/-- For small `q` the spectrum of the `a_k` contains a point between `(k-1)²` and `(k+1)²`
(`-1` instead of `(k-1)²` for `k = 0`). -/
lemma p3q_exists_spec_A (k : ℕ) : ∀ᶠ q : ℝ in 𝓝 0, ∃ c ∈ mathieuSpecA k q,
    (if k = 0 then (-1 : ℝ) else ((k : ℝ) - 1) ^ 2) < c ∧ c < ((k : ℝ) + 1) ^ 2 := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
  · set G : ℝ → ℝ → ℝ := fun a q => (deriv (mathieuWI (a : ℂ) (q : ℂ)) ((π : ℂ) / 2)).re
    have hGa : ∀ q, Continuous fun a => G a q := fun q => p3q_cont_re (p3q_diff_I q _).2
    have hGq : ∀ a, Continuous fun q => G a q := fun a => p3q_cont_re (p3q_diff_I_q a _).2
    have hmem : ∀ q c, G c q = 0 → c ∈ mathieuSpecA (2 * i) q := fun q c h => by
      simp only [mathieuSpecA, even_two_mul, ↓reduceIte, mem_ofPred_eq]
      exact p3q_real_eq_zero (p3q_dI_real c q) h
    rcases i with _ | j
    · have h0 : G (-1) 0 * G ((1 : ℕ) ^ 2 : ℝ) 0 < 0 := by
        have e1 : G (-1) 0 = Real.sinh (π / 2) := p3q_AE0_neg
        have e2 : G ((1 : ℕ) ^ 2 : ℝ) 0 = -Real.sin (((1 : ℕ) : ℝ) * (π / 2)) * ((1 : ℕ) : ℝ) :=
          p3q_AE0 _
        rw [e1, e2]
        have := p3q_sin_odd 0
        simp only [Nat.cast_one, one_mul, mul_one] at this ⊢
        rw [Real.sin_pi_div_two]
        have := Real.sinh_pos_iff.2 (by positivity : (0 : ℝ) < π / 2)
        linarith
      filter_upwards [p3q_ivt hGa hGq (by norm_num) h0] with q ⟨c, hc, hz⟩
      refine ⟨c, hmem q c hz, ?_, ?_⟩
      · simpa using hc.1
      · have := hc.2; push_cast at this ⊢; linarith
    · have h0 : G (((2 * j + 1 : ℕ) : ℝ) ^ 2) 0 * G (((2 * (j + 1) + 1 : ℕ) : ℝ) ^ 2) 0 < 0 := by
        have e1 : G (((2 * j + 1 : ℕ) : ℝ) ^ 2) 0 = _ := p3q_AE0 _
        have e2 : G (((2 * (j + 1) + 1 : ℕ) : ℝ) ^ 2) 0 = _ := p3q_AE0 _
        rw [e1, e2, p3q_sin_odd, p3q_sin_odd, pow_succ]
        have : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
        have hp : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) := by positivity
        have hp' : (0 : ℝ) < ((2 * (j + 1) + 1 : ℕ) : ℝ) := by positivity
        nlinarith [mul_pos hp hp']
      have hlt : ((2 * j + 1 : ℕ) : ℝ) ^ 2 < ((2 * (j + 1) + 1 : ℕ) : ℝ) ^ 2 := by
        gcongr; omega
      filter_upwards [p3q_ivt hGa hGq hlt h0] with q ⟨c, hc, hz⟩
      refine ⟨c, hmem q c hz, ?_, ?_⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        have := hc.1; push_cast at this ⊢; linarith
      · have := hc.2; push_cast at this ⊢; linarith
  · set G : ℝ → ℝ → ℝ := fun a q => (mathieuWI (a : ℂ) (q : ℂ) ((π : ℂ) / 2)).re
    have hGa : ∀ q, Continuous fun a => G a q := fun q => p3q_cont_re (p3q_diff_I q _).1
    have hGq : ∀ a, Continuous fun q => G a q := fun a => p3q_cont_re (p3q_diff_I_q a _).1
    have hmem : ∀ q c, G c q = 0 → c ∈ mathieuSpecA (2 * i + 1) q := fun q c h => by
      simp only [mathieuSpecA, Nat.not_even_bit1, ↓reduceIte, mem_ofPred_eq]
      exact p3q_real_eq_zero (p3q_I_real c q) h
    have h0 : G (((2 * i : ℕ) : ℝ) ^ 2) 0 * G (((2 * (i + 1) : ℕ) : ℝ) ^ 2) 0 < 0 := by
      have e1 : G (((2 * i : ℕ) : ℝ) ^ 2) 0 = _ := p3q_AO0 _
      have e2 : G (((2 * (i + 1) : ℕ) : ℝ) ^ 2) 0 = _ := p3q_AO0 _
      rw [e1, e2, p3q_cos_even, p3q_cos_even, pow_succ]
      have : ((-1 : ℝ) ^ i) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      nlinarith
    have hlt : ((2 * i : ℕ) : ℝ) ^ 2 < ((2 * (i + 1) : ℕ) : ℝ) ^ 2 := by gcongr; omega
    filter_upwards [p3q_ivt hGa hGq hlt h0] with q ⟨c, hc, hz⟩
    refine ⟨c, hmem q c hz, ?_, ?_⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      have := hc.1; push_cast at this ⊢; linarith
    · have := hc.2; push_cast at this ⊢; linarith

/-- For small `q` the spectrum of the `b_k`, `k ≥ 1`, contains a point between `(k-1)²` and
`(k+1)²`. -/
lemma p3q_exists_spec_B {k : ℕ} (hk : k ≠ 0) : ∀ᶠ q : ℝ in 𝓝 0, ∃ c ∈ mathieuSpecB k q,
    ((k : ℝ) - 1) ^ 2 < c ∧ c < ((k : ℝ) + 1) ^ 2 := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
  · obtain ⟨i, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    set G : ℝ → ℝ → ℝ := fun a q => (mathieuWII (a : ℂ) (q : ℂ) ((π : ℂ) / 2)).re
    have hGa : ∀ q, Continuous fun a => G a q := fun q => p3q_cont_re (p3q_diff_II q _).1
    have hGq : ∀ a, Continuous fun q => G a q := fun a => p3q_cont_re (p3q_diff_II_q a _).1
    have hmem : ∀ q c, G c q = 0 → c ∈ mathieuSpecB (2 * (i + 1)) q := fun q c h => by
      simp only [mathieuSpecB, even_two_mul, ↓reduceIte, mem_ofPred_eq]
      exact p3q_real_eq_zero (p3q_II_real c q) h
    have hp : (0 : ℝ) < ((2 * i + 1 : ℕ) : ℝ) := by positivity
    have hp' : (0 : ℝ) < ((2 * (i + 1) + 1 : ℕ) : ℝ) := by positivity
    have h0 : G (((2 * i + 1 : ℕ) : ℝ) ^ 2) 0 * G (((2 * (i + 1) + 1 : ℕ) : ℝ) ^ 2) 0 < 0 := by
      have e1 : G (((2 * i + 1 : ℕ) : ℝ) ^ 2) 0 = _ := p3q_BE0 hp.ne'
      have e2 : G (((2 * (i + 1) + 1 : ℕ) : ℝ) ^ 2) 0 = _ := p3q_BE0 hp'.ne'
      rw [e1, e2, p3q_sin_odd, p3q_sin_odd, pow_succ, div_mul_div_comm]
      have : ((-1 : ℝ) ^ i) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      apply div_neg_of_neg_of_pos _ (mul_pos hp hp')
      nlinarith
    have hlt : ((2 * i + 1 : ℕ) : ℝ) ^ 2 < ((2 * (i + 1) + 1 : ℕ) : ℝ) ^ 2 := by gcongr; omega
    filter_upwards [p3q_ivt hGa hGq hlt h0] with q ⟨c, hc, hz⟩
    refine ⟨c, hmem q c hz, ?_, ?_⟩
    · have := hc.1; push_cast at this ⊢; linarith
    · have := hc.2; push_cast at this ⊢; linarith
  · set G : ℝ → ℝ → ℝ := fun a q => (deriv (mathieuWII (a : ℂ) (q : ℂ)) ((π : ℂ) / 2)).re
    have hGa : ∀ q, Continuous fun a => G a q := fun q => p3q_cont_re (p3q_diff_II q _).2
    have hGq : ∀ a, Continuous fun q => G a q := fun a => p3q_cont_re (p3q_diff_II_q a _).2
    have hmem : ∀ q c, G c q = 0 → c ∈ mathieuSpecB (2 * i + 1) q := fun q c h => by
      simp only [mathieuSpecB, Nat.not_even_bit1, ↓reduceIte, mem_ofPred_eq]
      exact p3q_real_eq_zero (p3q_dII_real c q) h
    have h0 : G (((2 * i : ℕ) : ℝ) ^ 2) 0 * G (((2 * (i + 1) : ℕ) : ℝ) ^ 2) 0 < 0 := by
      have e1 : G (((2 * i : ℕ) : ℝ) ^ 2) 0 = _ := p3q_BO0 _
      have e2 : G (((2 * (i + 1) : ℕ) : ℝ) ^ 2) 0 = _ := p3q_BO0 _
      rw [e1, e2, p3q_cos_even, p3q_cos_even, pow_succ]
      have : ((-1 : ℝ) ^ i) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      nlinarith
    have hlt : ((2 * i : ℕ) : ℝ) ^ 2 < ((2 * (i + 1) : ℕ) : ℝ) ^ 2 := by gcongr; omega
    filter_upwards [p3q_ivt hGa hGq hlt h0] with q ⟨c, hc, hz⟩
    refine ⟨c, hmem q c hz, ?_, ?_⟩
    · have := hc.1; push_cast at this ⊢; linarith
    · have := hc.2; push_cast at this ⊢; linarith

/-- Every point of the spectrum `mathieuSpecA k q` is `a_m(q)` for some `m ≡ k (mod 2)`. -/
lemma p3q_eq_mathieuA_of_mem {k : ℕ} {q c : ℝ} (hc : c ∈ mathieuSpecA k q) :
    ∃ m, m % 2 = k % 2 ∧ mathieuA m q = c := by
  have hfin : (mathieuSpecA k q ∩ Iio c).Finite := by
    rw [p2s_specA]
    exact ODE.p2l_spec_Iio_finite (p2s_hV q) (p2s_hB q) (by positivity) _ _ c
  obtain ⟨j, hj⟩ := p1a1_exists_eq_nthLeast hc hfin
  refine ⟨2 * j + k % 2, by omega, ?_⟩
  have hS : mathieuSpecA (2 * j + k % 2) q = mathieuSpecA k q := by
    unfold mathieuSpecA
    have : Even (2 * j + k % 2) ↔ Even k := by
      rw [Nat.even_iff, Nat.even_iff]; omega
    simp only [this]
  rw [mathieuA, hS, show (2 * j + k % 2) / 2 = j by omega, hj]

/-- Every point of `mathieuSpecB k q` is `b_m(q)` for some `m ≥ 1`, `m ≡ k (mod 2)`. -/
lemma p3q_eq_mathieuB_of_mem {k : ℕ} {q c : ℝ} (hc : c ∈ mathieuSpecB k q) :
    ∃ m, m ≠ 0 ∧ m % 2 = k % 2 ∧ mathieuB m q = c := by
  have hfin : (mathieuSpecB k q ∩ Iio c).Finite := by
    rw [p2s_specB]
    exact ODE.p2l_spec_Iio_finite (p2s_hV q) (p2s_hB q) (by positivity) _ _ c
  obtain ⟨j, hj⟩ := p1a1_exists_eq_nthLeast hc hfin
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
lemma p3q_window_eq {k k' : ℕ} {c x : ℝ} (hx : x < 1 / 8) (hpar : k' % 2 = k % 2)
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
theorem p3q_eventually_small : ∀ᶠ q : ℝ in 𝓝 0, |q| < 1 / 8 := by
  have : ∀ᶠ q : ℝ in 𝓝 0, q ∈ Metric.ball (0 : ℝ) (1 / 8) := Metric.ball_mem_nhds _ (by norm_num)
  filter_upwards [this] with q hq
  rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hq

/-- **`a_m(q)` near `q = 0`**: for small real `q`, `|a_m(q) - m²| ≤ 4|q|`. In particular
`a_m` is continuous at `0` (DLMF 28.2.23 and §28.6). -/
theorem p3q_mathieuA_near (m : ℕ) : ∀ᶠ q : ℝ in 𝓝 0, |mathieuA m q - (m : ℝ) ^ 2| ≤ 4 * |q| := by
  filter_upwards [(Finset.range (m + 1)).eventually_all.2 (fun k _ => p3q_exists_spec_A k),
    p3q_eventually_small] with q hE hq
  have := p3q_comb (x := fun j => mathieuA j q) (c := |q|) (s := 0) (m := m) hq
    (strictMono_nat_of_lt_succ fun j => p3q_mathieuA_lt_succ j q)
    (fun j => by simpa using p3q_window_A j q) (fun k hk => ?_)
  · simpa using this
  obtain ⟨c, hc, hL, hR⟩ := hE k (Finset.mem_range.2 (by omega))
  obtain ⟨m', hm', rfl⟩ := p3q_eq_mathieuA_of_mem hc
  obtain ⟨k', hk', hw⟩ := p3q_window_A m' q
  have := p3q_window_eq hq (hk'.trans hm') hL hR hw
  subst this
  exact ⟨m', by simpa using hw⟩

/-- **`b_m(q)` near `q = 0`**: for `m ≥ 1` and small real `q`, `|b_m(q) - m²| ≤ 4|q|`. -/
theorem p3q_mathieuB_near {m : ℕ} (hm : m ≠ 0) :
    ∀ᶠ q : ℝ in 𝓝 0, |mathieuB m q - (m : ℝ) ^ 2| ≤ 4 * |q| := by
  obtain ⟨m, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  filter_upwards [(Finset.range (m + 2)).eventually_all.2
    (fun k _ => p3q_exists_spec_B (k := k + 1) (by omega)), p3q_eventually_small] with q hE hq
  have := p3q_comb (x := fun j => mathieuB (j + 1) q) (c := |q|) (s := 1) (m := m) hq
    (strictMono_nat_of_lt_succ fun j => p3q_mathieuB_lt_succ (by omega) q)
    (fun j => ?_) (fun k hk => ?_)
  · simpa using this
  · obtain ⟨k, hk, hk1, hw⟩ := p3q_window_B (m := j + 1) (by omega) q
    exact ⟨k - 1, by omega, by rw [show k - 1 + 1 = k by omega]; exact hw⟩
  · obtain ⟨c, hc, hL, hR⟩ := hE k (Finset.mem_range.2 (by omega))
    obtain ⟨m', hm'0, hm', rfl⟩ := p3q_eq_mathieuB_of_mem hc
    obtain ⟨k', hk', hk'1, hw⟩ := p3q_window_B hm'0 q
    have hL' : (if k + 1 = 0 then (-1 : ℝ) else (((k + 1 : ℕ) : ℝ) - 1) ^ 2) < mathieuB m' q := by
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact hL
    have := p3q_window_eq hq (hk'.trans hm') hL' hR hw
    subst this
    obtain ⟨m'', rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
    exact ⟨m'', hw⟩

/-! ### Eigenvalue estimates for the four classes -/

/-- Distinct squares of the same parity are separated: `|(2i+c)² - (2n+c)²| ≥ 4` for `i ≠ n`. -/
theorem p3q_sq_sep {i n : ℕ} (h : i ≠ n) (c : ℕ) :
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
theorem p3q_gap_aux {x y z e q : ℝ} (hq : |q| < 1 / 8) (h1 : |x - y| ≤ 4 * |q|)
    (h2 : 4 ≤ |z - y|) (he : |e| ≤ |q|) : 1 ≤ |x - (z + e)| := by
  have := abs_add_three (-(x - (z + e))) (x - y) (-e)
  rw [show -(x - (z + e)) + (x - y) + -e = z - y by ring, abs_neg, abs_neg] at this
  linarith

/-- A real function whose complex cast is `O(k)` is itself `O(k)`. -/
theorem p3q_real_of_complex {f : ℝ → ℝ} {g : ℝ → ℂ} {k : ℝ → ℝ} {l : Filter ℝ}
    (h : g =O[l] k) (he : ∀ q, ((f q : ℝ) : ℂ) = g q) : f =O[l] k := by
  have : (fun q => ((f q : ℝ) : ℂ)) =O[l] k := by simpa only [he] using h
  rw [← isBigO_norm_left] at this ⊢
  simpa only [Complex.norm_real] using this

/-- If `f(q) = q^e s(q)` with `s` continuous and `e' ≤ e`, then `f = O(q^{e'})` at `0`. -/
theorem p3q_isBigO_of_eq {f s : ℝ → ℂ} {e e' : ℕ} (he : e' ≤ e)
    (h : ∀ q : ℝ, f q = (q : ℂ) ^ e * s q) (hs : Continuous s) :
    f =O[𝓝 0] (fun q : ℝ => q ^ e') := by
  have h1 : s =O[𝓝 0] (fun _ => (1 : ℝ)) := (hs.tendsto 0).isBigO_one ℝ
  have h2 : (fun q : ℝ => (q : ℂ) ^ e) =O[𝓝 0] (fun q : ℝ => q ^ e) :=
    isBigO_of_le _ fun q => by simp [norm_pow]
  have := (h2.mul h1).trans (p3q_pow_isBigO (by omega : e' ≤ e) |>.congr_left (fun q => by
    simp))
  simpa only [mul_one, ← h] using this

/-- A continuous function is `O(1)` at `0`. -/
theorem p3q_cont_isBigO_one {s : ℝ → ℂ} (hs : Continuous s) :
    s =O[𝓝 0] (fun _ => (1 : ℝ)) := (hs.tendsto 0).isBigO_one ℝ

/-- Eigenvalue estimate for `a_{2n}(q)` from a trial vector (recurrence 28.4.5). -/
theorem p3q_eig_AE (n : ℕ) {N K : ℕ} (hnN : n < N) {p : ℝ → ℂ} {v : ℝ → ℕ → ℂ}
    (hvN : ∀ q, v q N = 0) (hvN1 : ∀ q, v q (N + 1) = 0) (hvn : ∀ q, v q n = 1)
    (hv : ∀ i < N + 1, (fun q => v q i) =O[𝓝 0] (fun _ => (1 : ℝ)))
    (hr : ∀ i < N + 1, (fun q : ℝ => p3qL (fun i => 4 * (i : ℂ) ^ 2) 2 q (v q) i -
      p q * v q i) =O[𝓝 0] (fun q : ℝ => q ^ (K - Nat.dist i n))) :
    (fun q : ℝ => (mathieuA (2 * n) q : ℂ) - p q) =O[𝓝 0] (fun q : ℝ => q ^ K) := by
  refine p3q_eig_isBigO (d := fun _ i => 4 * (i : ℂ) ^ 2) (β := 2) (by norm_num) (by norm_num)
    (A := fun q i => mathieuFourierA (2 * n) (2 * i) q) hnN
    (Eventually.of_forall (p3q_rec_AE n)) (Eventually.of_forall (p3q_lim_AE n))
    (Eventually.of_forall (p3q_ne_AE n)) ?_ hvN hvN1 hvn hv hr
  filter_upwards [p3q_mathieuA_near (2 * n), p3q_eventually_small] with q h1 h2
  intro i hi
  rw [show (4 * (i : ℂ) ^ 2) = ((((2 * i + 0 : ℕ) : ℝ) ^ 2 + 0 : ℝ) : ℂ) by push_cast; ring,
    p3q_norm_ofReal_sub]
  exact p3q_gap_aux h2 (by simpa using h1) (p3q_sq_sep hi 0) (by simp)

/-- Eigenvalue estimate for `a_{2n+1}(q)` from a trial vector (recurrence 28.4.6). -/
theorem p3q_eig_AO (n : ℕ) {N K : ℕ} (hnN : n < N) {p : ℝ → ℂ} {v : ℝ → ℕ → ℂ}
    (hvN : ∀ q, v q N = 0) (hvN1 : ∀ q, v q (N + 1) = 0) (hvn : ∀ q, v q n = 1)
    (hv : ∀ i < N + 1, (fun q => v q i) =O[𝓝 0] (fun _ => (1 : ℝ)))
    (hr : ∀ i < N + 1, (fun q : ℝ => p3qL (fun i => (2 * (i : ℂ) + 1) ^ 2 +
      if i = 0 then (q : ℂ) else 0) 1 q (v q) i - p q * v q i) =O[𝓝 0]
      (fun q : ℝ => q ^ (K - Nat.dist i n))) :
    (fun q : ℝ => (mathieuA (2 * n + 1) q : ℂ) - p q) =O[𝓝 0] (fun q : ℝ => q ^ K) := by
  refine p3q_eig_isBigO (d := fun q i => (2 * (i : ℂ) + 1) ^ 2 + if i = 0 then (q : ℂ) else 0)
    (β := 1) (by norm_num) (by norm_num)
    (A := fun q i => mathieuFourierA (2 * n + 1) (2 * i + 1) q) hnN
    (Eventually.of_forall (p3q_rec_AO n)) (Eventually.of_forall (p3q_lim_AO n))
    (Eventually.of_forall (p3q_ne_AO n)) ?_ hvN hvN1 hvn hv hr
  filter_upwards [p3q_mathieuA_near (2 * n + 1), p3q_eventually_small] with q h1 h2
  intro i hi
  rw [show ((2 * (i : ℂ) + 1) ^ 2 + if i = 0 then (q : ℂ) else 0) =
      ((((2 * i + 1 : ℕ) : ℝ) ^ 2 + (if i = 0 then q else 0) : ℝ) : ℂ) by
      split_ifs <;> push_cast <;> ring, p3q_norm_ofReal_sub]
  exact p3q_gap_aux h2 (by simpa using h1) (p3q_sq_sep hi 1) (by split_ifs <;> simp)

/-- Eigenvalue estimate for `b_{2n+1}(q)` from a trial vector (recurrence 28.4.7). -/
theorem p3q_eig_BO (n : ℕ) {N K : ℕ} (hnN : n < N) {p : ℝ → ℂ} {v : ℝ → ℕ → ℂ}
    (hvN : ∀ q, v q N = 0) (hvN1 : ∀ q, v q (N + 1) = 0) (hvn : ∀ q, v q n = 1)
    (hv : ∀ i < N + 1, (fun q => v q i) =O[𝓝 0] (fun _ => (1 : ℝ)))
    (hr : ∀ i < N + 1, (fun q : ℝ => p3qL (fun i => (2 * (i : ℂ) + 1) ^ 2 -
      if i = 0 then (q : ℂ) else 0) 1 q (v q) i - p q * v q i) =O[𝓝 0]
      (fun q : ℝ => q ^ (K - Nat.dist i n))) :
    (fun q : ℝ => (mathieuB (2 * n + 1) q : ℂ) - p q) =O[𝓝 0] (fun q : ℝ => q ^ K) := by
  refine p3q_eig_isBigO (d := fun q i => (2 * (i : ℂ) + 1) ^ 2 - if i = 0 then (q : ℂ) else 0)
    (β := 1) (by norm_num) (by norm_num)
    (A := fun q i => mathieuFourierB (2 * n + 1) (2 * i + 1) q) hnN
    (Eventually.of_forall (p3q_rec_BO n)) (Eventually.of_forall (p3q_lim_BO n))
    (Eventually.of_forall (p3q_ne_BO n)) ?_ hvN hvN1 hvn hv hr
  filter_upwards [p3q_mathieuB_near (m := 2 * n + 1) (by omega), p3q_eventually_small]
    with q h1 h2
  intro i hi
  rw [show ((2 * (i : ℂ) + 1) ^ 2 - if i = 0 then (q : ℂ) else 0) =
      ((((2 * i + 1 : ℕ) : ℝ) ^ 2 + -(if i = 0 then q else 0) : ℝ) : ℂ) by
      split_ifs <;> push_cast <;> ring, p3q_norm_ofReal_sub]
  exact p3q_gap_aux h2 (by simpa using h1) (p3q_sq_sep hi 1) (by split_ifs <;> simp)

/-- Eigenvalue estimate for `b_{2n+2}(q)` from a trial vector (recurrence 28.4.8). -/
theorem p3q_eig_BE (n : ℕ) {N K : ℕ} (hnN : n < N) {p : ℝ → ℂ} {v : ℝ → ℕ → ℂ}
    (hvN : ∀ q, v q N = 0) (hvN1 : ∀ q, v q (N + 1) = 0) (hvn : ∀ q, v q n = 1)
    (hv : ∀ i < N + 1, (fun q => v q i) =O[𝓝 0] (fun _ => (1 : ℝ)))
    (hr : ∀ i < N + 1, (fun q : ℝ => p3qL (fun i => (2 * (i : ℂ) + 2) ^ 2) 1 q (v q) i -
      p q * v q i) =O[𝓝 0] (fun q : ℝ => q ^ (K - Nat.dist i n))) :
    (fun q : ℝ => (mathieuB (2 * n + 2) q : ℂ) - p q) =O[𝓝 0] (fun q : ℝ => q ^ K) := by
  refine p3q_eig_isBigO (d := fun _ i => (2 * (i : ℂ) + 2) ^ 2) (β := 1) (by norm_num)
    (by norm_num) (A := fun q i => mathieuFourierB (2 * n + 2) (2 * i + 2) q) hnN
    (Eventually.of_forall (p3q_rec_BE n)) (Eventually.of_forall (p3q_lim_BE n))
    (Eventually.of_forall (p3q_ne_BE n)) ?_ hvN hvN1 hvn hv hr
  filter_upwards [p3q_mathieuB_near (m := 2 * n + 2) (by omega), p3q_eventually_small]
    with q h1 h2
  intro i hi
  rw [show ((2 * (i : ℂ) + 2) ^ 2) = ((((2 * i + 2 : ℕ) : ℝ) ^ 2 + 0 : ℝ) : ℂ) by
      push_cast; ring, p3q_norm_ofReal_sub]
  exact p3q_gap_aux h2 (by simpa using h1) (p3q_sq_sep hi 2) (by simp)

end DLMF.Mathieu
