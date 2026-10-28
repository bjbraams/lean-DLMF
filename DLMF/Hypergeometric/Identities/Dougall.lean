/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Identities.CarlsonTools

/-!
# Dougall bilateral summation tools

Summability, analytic bounds and Carlson uniqueness for the bilateral Dougall summation.

Source references and common attribution are retained in
`DLMF.Hypergeometric.Identities`.
-/

@[expose] public section

open Complex

open scoped Real

noncomputable section

namespace DLMF.Hypergeometric

section CarlsonApplications

open Filter Set

open scoped Topology

namespace DougallAux

open CarlsonAux

variable {a b c : ℂ}

/-- The terms of Dougall's bilateral series. -/
def term (a b c d : ℂ) (n : ℤ) : ℂ :=
  Gamma (a + n) * Gamma (b + n) / (Gamma (c + n) * Gamma (d + n))

/-- The norm of a Dougall term factors into the norms of its four Gamma factors. -/
theorem norm_term (a b c d : ℂ) (n : ℤ) :
    ‖term a b c d n‖ = ‖Gamma (a + n)‖ * ‖Gamma (b + n)‖ * ‖(Gamma (c + n))⁻¹‖ *
      ‖(Gamma (d + n))⁻¹‖ := by
  rw [term, div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_mul]; ring

/-- A majorant for Dougall's terms, uniform for `x₁ ≤ Re d ≤ x₁ + 1`. -/
theorem exists_bound (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k) {x₁ : ℝ}
    (hx₁ : 1 + (a + b - c).re < x₁) :
    ∃ u : ℤ → ℝ, Summable u ∧ (∀ n, 0 ≤ u n) ∧ ∀ (n : ℤ) (d : ℂ), x₁ ≤ d.re → d.re ≤ x₁ + 1 →
      ‖term a b c d n‖ ≤ Real.exp (π * |d.im|) * u n := by
  simp only [Complex.sub_re, Complex.add_re] at hx₁
  set h : ℤ → ℝ := fun n => ‖Gamma (a + n)‖ * ‖Gamma (b + n)‖ * ‖(Gamma (c + n))⁻¹‖ with hh
  obtain ⟨B, hB0, hBpos, hBneg, hbound⟩ := exists_recip_Gamma_shift_bound x₁
  refine ⟨fun n => h n * B n, ?_, fun n => mul_nonneg (by positivity) (hB0 n),
    fun n d hd1 hd2 => ?_⟩
  swap
  · rw [norm_term]
    calc ‖Gamma (a + n)‖ * ‖Gamma (b + n)‖ * ‖(Gamma (c + n))⁻¹‖ * ‖(Gamma (d + n))⁻¹‖
        = h n * ‖(Gamma (d + n))⁻¹‖ := rfl
      _ ≤ h n * (Real.exp (π * |d.im|) * B n) := by
          gcongr; exact hbound n d hd1 hd2
      _ = Real.exp (π * |d.im|) * (h n * B n) := by ring
  -- summability over `ℤ`
  refine Summable.of_nat_of_neg ?_ ?_
  · -- `n → +∞`: a Gamma ratio with exponent `Re(a+b-c) - x₁ < -1`
    refine Summable.of_norm_bounded_eventually_nat
      (summable_norm_Gamma_ratio a b c x₁ (by simp; linarith)) ?_
    obtain ⟨K₀, hK₀⟩ := exists_nat_ge (2 - x₁)
    filter_upwards [eventually_ge_atTop K₀] with k hk
    have hk' : (2 : ℝ) ≤ x₁ + ((k : ℤ) : ℝ) := by
      push_cast; linarith [(show (K₀ : ℝ) ≤ k by exact_mod_cast hk)]
    have hBk : B k = (Real.Gamma (x₁ + k))⁻¹ := by
      rw [hBpos _ hk']; push_cast; rfl
    have hpos := Real.Gamma_pos_of_pos (show 0 < x₁ + k by push_cast at hk'; linarith)
    have hGx : ‖(Gamma ((k : ℂ) + (x₁ : ℂ)))⁻¹‖ = (Real.Gamma (x₁ + k))⁻¹ := by
      rw [show (k : ℂ) + (x₁ : ℂ) = ((x₁ + k : ℝ) : ℂ) by push_cast; ring,
        Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hpos)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hB0 _)), hBk]
    simp only [hh, norm_mul, hGx]
    push_cast
    rw [add_comm a, add_comm b, add_comm c]
  · -- `n → -∞`: reflect to a Gamma ratio at `1 - c, 1 - x₁; 1 - a, 1 - b`
    set Kc : ℝ := ‖Complex.sin (π * c)‖ / (‖Complex.sin (π * a)‖ * ‖Complex.sin (π * b)‖)
    refine Summable.of_norm_bounded_eventually_nat
      ((summable_norm_Gamma_ratio (1 - c) (1 - x₁) (1 - a) (1 - b)
        (by simp; linarith)).mul_left Kc) ?_
    obtain ⟨K₁, hK₁⟩ := exists_nat_ge (|x₁| + 2 + |c.re|)
    filter_upwards [eventually_ge_atTop K₁] with k hk
    have hkR' : |x₁| + 2 + |c.re| ≤ k := le_trans hK₁ (by exact_mod_cast hk)
    have hkR : x₁ + 2 + |c.re| ≤ k := le_trans (by linarith [le_abs_self x₁]) hkR'
    have hn1 : ¬ (2 : ℝ) ≤ x₁ + ((-(k : ℤ) : ℤ) : ℝ) := by
      push_cast; linarith [abs_nonneg c.re]
    have hn2 : x₁ + 1 + ((-(k : ℤ) : ℤ) : ℝ) ≤ -1 := by
      push_cast; linarith [abs_nonneg c.re]
    have hBk : B (-(k : ℤ)) = Real.Gamma (1 - x₁ + k) / π := by
      rw [hBneg _ hn1 hn2]; push_cast; ring_nf
    have hsa : ∀ n : ℤ, a - k ≠ n := fun n h => ha (n + k) (by push_cast; linear_combination h)
    have hsb : ∀ n : ℤ, b - k ≠ n := fun n h => hb (n + k) (by push_cast; linear_combination h)
    have hsc : ∀ m : ℕ, c - k ≠ m + 1 := by
      intro m h
      have := congrArg Complex.re h
      simp at this
      have : c.re ≤ |c.re| := le_abs_self _
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), abs_nonneg x₁]
    have hA := norm_Gamma_eq_reflect hsa
    have hB := norm_Gamma_eq_reflect hsb
    have hC := recip_Gamma_eq_reflect hsc
    have hsin (z : ℂ) : ‖Complex.sin (π * (z - k))‖ = ‖Complex.sin (π * z)‖ := by
      have := norm_sin_pi_mul_add_int z (-(k : ℤ)); push_cast at this
      rwa [← sub_eq_add_neg] at this
    have hGx : Real.Gamma (1 - x₁ + k) = ‖Gamma ((k : ℂ) + (1 - x₁ : ℂ))‖ := by
      have hpos := Real.Gamma_pos_of_pos (show 0 < 1 - x₁ + k by linarith [abs_nonneg c.re])
      rw [show (k : ℂ) + (1 - x₁ : ℂ) = ((1 - x₁ + k : ℝ) : ℂ) by push_cast; ring,
        Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    have hsa0 : Complex.sin (π * a) ≠ 0 := by
      rw [Ne, Complex.sin_eq_zero_iff]; rintro ⟨n, hn⟩
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact ha n (mul_left_cancel₀ hπ (by rw [hn]; ring))
    have hsb0 : Complex.sin (π * b) ≠ 0 := by
      rw [Ne, Complex.sin_eq_zero_iff]; rintro ⟨n, hn⟩
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact hb n (mul_left_cancel₀ hπ (by rw [hn]; ring))
    have hGa : Gamma ((k : ℂ) + (1 - a)) ≠ 0 := by
      intro h0
      have := hA; rw [show 1 - (a - k) = (k : ℂ) + (1 - a) by ring, h0, norm_zero,
        mul_zero, div_zero] at this
      exact (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero (fun m hm => hsa (-m)
        (by rw [hm]; push_cast; ring)))) this
    have hGb : Gamma ((k : ℂ) + (1 - b)) ≠ 0 := by
      intro h0
      have := hB; rw [show 1 - (b - k) = (k : ℂ) + (1 - b) by ring, h0, norm_zero,
        mul_zero, div_zero] at this
      exact (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero (fun m hm => hsb (-m)
        (by rw [hm]; push_cast; ring)))) this
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hB0 _)), hBk]
    simp only [hh]
    push_cast
    rw [← sub_eq_add_neg, ← sub_eq_add_neg, ← sub_eq_add_neg, hA, hB, hC,
      show 1 - (a - k) = (k : ℂ) + (1 - a) by ring, show 1 - (b - k) = (k : ℂ) + (1 - b) by ring,
      show 1 - (c - k) = (k : ℂ) + (1 - c) by ring, hsin, hsin, hGx, norm_div, norm_mul,
      norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, hsin]
    have hπn : ‖(π : ℂ)‖ = π := by simp [abs_of_pos Real.pi_pos]
    rw [hπn]
    simp only [Kc]
    have h1 := norm_ne_zero_iff.mpr hsa0
    have h2 := norm_ne_zero_iff.mpr hsb0
    have h3 := norm_ne_zero_iff.mpr hGa
    have h4 := norm_ne_zero_iff.mpr hGb
    have hπ0 : π ≠ 0 := Real.pi_ne_zero
    apply le_of_eq
    field_simp

/-- Dougall's bilateral series converges absolutely when `a, b` are not integers and `Re d > 1 + Re
  (a + b - c)`. -/
theorem summable_term (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k) {d : ℂ}
    (hd : 1 + (a + b - c).re < d.re) : Summable (term a b c d) := by
  obtain ⟨u, hu, -, hbd⟩ := exists_bound (c := c) ha hb hd
  exact Summable.of_norm_bounded (hu.mul_left (Real.exp (π * |d.im|)))
    fun n => hbd n d le_rfl (by linarith)

/-- Dougall's sum is holomorphic in `d` on its half-plane of convergence. -/
theorem differentiableOn_tsum (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k) :
    DifferentiableOn ℂ (fun d => ∑' n : ℤ, term a b c d n)
      {d : ℂ | 1 + (a + b - c).re < d.re} := by
  intro d₀ hd₀
  simp only [Set.mem_ofPred_eq] at hd₀
  set r : ℝ := min (1 / 2) ((d₀.re - (1 + (a + b - c).re)) / 2) with hr
  have hr0 : 0 < r := lt_min (by norm_num) (by linarith)
  have hr1 : r ≤ 1 / 2 := min_le_left _ _
  have hr2 : r ≤ (d₀.re - (1 + (a + b - c).re)) / 2 := min_le_right _ _
  obtain ⟨u, hu, hu0, hbd⟩ := exists_bound (c := c) ha hb (x₁ := d₀.re - r) (by linarith)
  have hball : DifferentiableOn ℂ (fun d => ∑' n : ℤ, term a b c d n) (Metric.ball d₀ r) := by
    refine differentiableOn_tsum_of_summable_norm
      (hu.mul_left (Real.exp (π * (|d₀.im| + 1)))) (fun n => ?_) Metric.isOpen_ball
      (fun n d hd => ?_)
    · have hfun : (fun d => term a b c d n) = fun d =>
          Gamma (a + n) * Gamma (b + n) * (Gamma (c + n))⁻¹ * (Gamma (d + n))⁻¹ := by
        funext d; rw [term, div_eq_mul_inv, mul_inv]; ring
      rw [hfun]
      exact ((Complex.differentiable_one_div_Gamma.comp
        (differentiable_id.add_const _)).const_mul _).differentiableOn
    · have hdist : ‖d - d₀‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hd
      have hre : |d.re - d₀.re| < r :=
        lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (d - d₀)) hdist
      have him : |d.im - d₀.im| < r :=
        lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (d - d₀)) hdist
      refine (hbd n d (by linarith [abs_lt.mp hre]) (by linarith [abs_lt.mp hre])).trans ?_
      have := hu0 n
      gcongr
      have : |d.im| ≤ |d₀.im| + |d.im - d₀.im| := by
        have := abs_add_le d₀.im (d.im - d₀.im); simp at this; linarith [abs_sub_comm d.im d₀.im]
      linarith [abs_lt.mp him]
  exact (hball.differentiableAt (Metric.ball_mem_nhds _ hr0)).differentiableWithinAt

/-- Termwise telescoping identity behind the recurrence in `d`. -/
theorem term_recurrence (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k) (d : ℂ) (n : ℤ) :
    (d - a) * (d - b) * term a b c (d + 1) n - (c + d - a - b - 1) * term a b c d n =
      term a b (c - 1) d (n + 1) - term a b (c - 1) d n := by
  have hA : a + n ≠ 0 := fun h => ha (-n) (by push_cast; linear_combination h)
  have hB : b + n ≠ 0 := fun h => hb (-n) (by push_cast; linear_combination h)
  have e1 : Gamma (a + ((n + 1 : ℤ) : ℂ)) = (a + n) * Gamma (a + n) := by
    rw [show a + ((n + 1 : ℤ) : ℂ) = (a + n) + 1 by push_cast; ring, Complex.Gamma_add_one _ hA]
  have e2 : Gamma (b + ((n + 1 : ℤ) : ℂ)) = (b + n) * Gamma (b + n) := by
    rw [show b + ((n + 1 : ℤ) : ℂ) = (b + n) + 1 by push_cast; ring, Complex.Gamma_add_one _ hB]
  have e3 : (Gamma (c - 1 + n))⁻¹ = (c - 1 + n) * (Gamma (c + n))⁻¹ := by
    rw [← mul_recip_Gamma_add_one (c - 1 + n)]; ring_nf
  have e4 : (Gamma (d + n))⁻¹ = (d + n) * (Gamma (d + n + 1))⁻¹ := by
    rw [← mul_recip_Gamma_add_one (d + n)]
  have e5 : c - 1 + ((n + 1 : ℤ) : ℂ) = c + n := by push_cast; ring
  have e6 : d + 1 + (n : ℂ) = d + n + 1 := by ring
  have e7 : d + ((n + 1 : ℤ) : ℂ) = d + n + 1 := by push_cast; ring
  simp only [term, div_eq_mul_inv, mul_inv]
  rw [e1, e2, e3, e5, e6, e7, e4]
  ring

/-- The first-order recurrence of Dougall's sum in `d`. -/
theorem tsum_recurrence (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k) {d : ℂ}
    (hd : 2 + (a + b - c).re < d.re) :
    (d - a) * (d - b) * ∑' n : ℤ, term a b c (d + 1) n =
      (c + d - a - b - 1) * ∑' n : ℤ, term a b c d n := by
  have h1 : Summable (term a b c (d + 1)) := summable_term ha hb (by simp at hd ⊢; linarith)
  have h2 : Summable (term a b c d) := summable_term ha hb (by linarith)
  have h3 : Summable (term a b (c - 1) d) :=
    summable_term ha hb (by simp at hd ⊢; linarith)
  have h4 : Summable fun n : ℤ => term a b (c - 1) d (n + 1) :=
    (Equiv.addRight (1 : ℤ)).summable_iff.mpr h3
  have hshift : ∑' n : ℤ, term a b (c - 1) d (n + 1) = ∑' n : ℤ, term a b (c - 1) d n :=
    (Equiv.addRight (1 : ℤ)).tsum_eq (term a b (c - 1) d)
  rw [← sub_eq_zero, ← tsum_mul_left, ← tsum_mul_left,
    ← (h1.mul_left _).tsum_sub (h2.mul_left _)]
  simp_rw [term_recurrence (c := c) ha hb d]
  rw [h4.tsum_sub h3, hshift, sub_self]

/-- `sin(π(z + j)) = (-1)^j sin(πz)` in the form used below. -/
theorem sin_pi_mul_add_int (z : ℂ) (j : ℤ) :
    Complex.sin (π * (z + j)) = ((j.negOnePow : ℤ) : ℂ) * Complex.sin (π * z) := by
  rw [show (π : ℂ) * (z + j) = π * z + j * π by ring, Complex.sin_antiperiodic.add_int_mul_eq j]

/-- `((-1)^j)² = 1` for `j ∈ ℤ`, cast to `ℂ`. -/
theorem negOnePow_sq_cast (j : ℤ) : ((j.negOnePow : ℤ) : ℂ) * ((j.negOnePow : ℤ) : ℂ) = 1 := by
  rcases Int.isUnit_iff.mp (Int.negOnePow j).isUnit with h | h <;> simp [h]

/-- **Dougall's sum at an integer `d`**, from Gauss's summation. -/
theorem tsum_at_int (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k) (m : ℤ)
    (hγ : ∀ k : ℕ, c + 1 - m ≠ -k) (hconv : 1 + (a + b).re < (c + m).re) :
    ∑' n : ℤ, term a b c m n =
      π ^ 2 * Gamma (c + m - a - b - 1) /
        (Complex.sin (π * a) * Complex.sin (π * b) * Gamma (c - a) * Gamma (m - a) *
          Gamma (c - b) * Gamma (m - b)) := by
  set α := a + 1 - m with hα
  set β := b + 1 - m with hβ
  set γ := c + 1 - m with hγdef
  -- the terms with `n + m ≤ 0` vanish
  set g : ℕ → ℤ := fun k => (k : ℤ) + 1 - m with hg
  have hginj : Function.Injective g := fun i j h => by
    simp only [hg] at h; exact_mod_cast (show (i : ℤ) = j by linarith)
  have hsupp : Function.support (term a b c m) ⊆ Set.range g := by
    intro n hn
    by_contra hnot
    apply hn
    have hle : n + m ≤ 0 := by
      by_contra hlt
      push Not at hlt
      exact hnot ⟨(n + m - 1).toNat, by simp only [hg]; rw [Int.toNat_of_nonneg (by omega)]; ring⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, n + m = -(j : ℤ) := ⟨(-(n + m)).toNat, by omega⟩
    have : (m : ℂ) + n = -(j : ℂ) := by exact_mod_cast (show (m : ℤ) + n = -(j : ℤ) by omega)
    simp only [term, this, Complex.Gamma_neg_nat_eq_zero, mul_zero, div_zero]
  rw [← hginj.tsum_eq hsupp]
  -- each surviving term is a Gauss coefficient
  have hαn : ∀ k : ℕ, α ≠ -k := fun k h => ha (m - 1 - k) (by
    rw [hα] at h; push_cast; linear_combination h)
  have hβn : ∀ k : ℕ, β ≠ -k := fun k h => hb (m - 1 - k) (by
    rw [hβ] at h; push_cast; linear_combination h)
  have hGα : Gamma α ≠ 0 := Complex.Gamma_ne_zero hαn
  have hGβ : Gamma β ≠ 0 := Complex.Gamma_ne_zero hβn
  have hGγ : Gamma γ ≠ 0 := Complex.Gamma_ne_zero hγ
  have hterm : ∀ k : ℕ, term a b c m (g k) =
      Gamma α * Gamma β / Gamma γ * gaussHGCoeff α β γ k := by
    intro k
    have e1 : a + ((g k : ℤ) : ℂ) = α + k := by simp only [hg, hα]; push_cast; ring
    have e2 : b + ((g k : ℤ) : ℂ) = β + k := by simp only [hg, hβ]; push_cast; ring
    have e3 : c + ((g k : ℤ) : ℂ) = γ + k := by simp only [hg, hγdef]; push_cast; ring
    have e4 : (m : ℂ) + ((g k : ℤ) : ℂ) = k + 1 := by simp only [hg]; push_cast; ring
    have pα : Gamma (α + k) = Gamma α * poch α k := by
      have h := Complex.Gamma_add_nat_div_Gamma_eq (n := k) α hαn
      rw [div_eq_iff hGα] at h
      rw [h, poch, mul_comm]
    have pβ : Gamma (β + k) = Gamma β * poch β k := by
      have h := Complex.Gamma_add_nat_div_Gamma_eq (n := k) β hβn
      rw [div_eq_iff hGβ] at h
      rw [h, poch, mul_comm]
    have pγ : Gamma (γ + k) = Gamma γ * poch γ k := by
      have h := Complex.Gamma_add_nat_div_Gamma_eq (n := k) γ hγ
      rw [div_eq_iff hGγ] at h
      rw [h, poch, mul_comm]
    have hpγ : poch γ k ≠ 0 := poch_ne_zero_of_not_neg_nat hγ k
    have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    rw [term, e1, e2, e3, e4, Complex.Gamma_nat_eq_factorial, pα, pβ, pγ, gaussHGCoeff]
    field_simp
  simp_rw [hterm]
  rw [tsum_mul_left, ← ordinaryHypergeometric_one_eq_tsum]
  have hre : 0 < (γ - α - β).re := by
    simp only [hα, hβ, hγdef, Complex.sub_re, Complex.add_re, Complex.one_re] at hconv ⊢
    linarith
  rw [gauss_summation hγ hre]
  have e5 : γ - α - β = c + m - a - b - 1 := by simp only [hα, hβ, hγdef]; ring
  have e6 : γ - α = c - a := by simp only [hα, hγdef]; ring
  have e7 : γ - β = c - b := by simp only [hβ, hγdef]; ring
  rw [e5, e6, e7]
  -- reflection: `Γ(α) Γ(m - a) = π / sin(πα)`, and likewise for `β`
  have rα := Complex.Gamma_mul_Gamma_one_sub α
  have rβ := Complex.Gamma_mul_Gamma_one_sub β
  rw [show 1 - α = (m : ℂ) - a by simp only [hα]; ring] at rα
  rw [show 1 - β = (m : ℂ) - b by simp only [hβ]; ring] at rβ
  have sα : Complex.sin (π * α) = (((1 - m).negOnePow : ℤ) : ℂ) * Complex.sin (π * a) := by
    rw [← sin_pi_mul_add_int]; congr 1; simp only [hα]; push_cast; ring
  have sβ : Complex.sin (π * β) = (((1 - m).negOnePow : ℤ) : ℂ) * Complex.sin (π * b) := by
    rw [← sin_pi_mul_add_int]; congr 1; simp only [hβ]; push_cast; ring
  have hsa0 : Complex.sin (π * a) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff]; rintro ⟨n, hn⟩
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact ha n (mul_left_cancel₀ hπ (by rw [hn]; ring))
  have hsb0 : Complex.sin (π * b) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff]; rintro ⟨n, hn⟩
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact hb n (mul_left_cancel₀ hπ (by rw [hn]; ring))
  have hma : Gamma ((m : ℂ) - a) ≠ 0 := Complex.Gamma_ne_zero fun k h =>
    ha (m + k) (by push_cast; linear_combination -h)
  have hmb : Gamma ((m : ℂ) - b) ≠ 0 := Complex.Gamma_ne_zero fun k h =>
    hb (m + k) (by push_cast; linear_combination -h)
  have hs := negOnePow_sq_cast (1 - m)
  set s : ℂ := (((1 - m).negOnePow : ℤ) : ℂ)
  have hs0 : s ≠ 0 := by intro h0; rw [h0, zero_mul] at hs; exact zero_ne_one hs
  rw [sα] at rα
  rw [sβ] at rβ
  have hGα' : Gamma α = π / (s * Complex.sin (π * a)) / Gamma ((m : ℂ) - a) := by
    rw [← rα]; field_simp
  have hGβ' : Gamma β = π / (s * Complex.sin (π * b)) / Gamma ((m : ℂ) - b) := by
    rw [← rβ]; field_simp
  rw [hGα', hGβ']
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases hca : Gamma (c - a) = 0
  · simp [hca]
  by_cases hcb : Gamma (c - b) = 0
  · simp [hcb]
  field_simp
  linear_combination (-Gamma (c + m - a - b - 1)) * hs

/-- **Dougall's bilateral sum** for non-integral `c`, by Carlson's theorem in `d`: the sum times
`Γ(d-a)Γ(d-b)/Γ(c+d-a-b-1)` is `1`-periodic in `d`, of exponential type `π/2` on vertical lines,
and takes the right value at the integers by Gauss's summation. -/
theorem tsum_eq_of_not_int (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k) (hc : ∀ k : ℤ, c ≠ k)
    {d : ℂ} (hconv : 1 + (a + b).re < (c + d).re) :
    ∑' n : ℤ, term a b c d n =
      π ^ 2 * Gamma (c + d - a - b - 1) /
        (Complex.sin (π * a) * Complex.sin (π * b) * Gamma (c - a) * Gamma (d - a) *
          Gamma (c - b) * Gamma (d - b)) := by
  set L : ℂ → ℂ := fun d => ∑' n : ℤ, term a b c d n with hL
  set K : ℂ := π ^ 2 /
    (Complex.sin (π * a) * Complex.sin (π * b) * Gamma (c - a) * Gamma (c - b)) with hK
  set R : ℂ → ℂ := fun d =>
    K * Gamma (c + d - a - b - 1) * (Gamma (d - a))⁻¹ * (Gamma (d - b))⁻¹ with hR
  have hRform : ∀ d : ℂ, π ^ 2 * Gamma (c + d - a - b - 1) /
      (Complex.sin (π * a) * Complex.sin (π * b) * Gamma (c - a) * Gamma (d - a) *
        Gamma (c - b) * Gamma (d - b)) = R d := by
    intro d; simp only [hR, hK, div_eq_mul_inv, mul_inv]; ring
  rw [hRform]
  set N : ℂ → ℂ := fun d =>
    Gamma (d - a) * Gamma (d - b) * (Gamma (c + d - a - b - 1))⁻¹ with hN
  set s : ℝ := (a + b - c).re with hs
  have hsre : s = a.re + b.re - c.re := by simp [hs]
  obtain ⟨m₀, hm₀⟩ := exists_nat_ge (4 + |s| + |a.re| + |b.re|)
  have hm₀' : (4 : ℝ) + |s| + |a.re| + |b.re| ≤ m₀ := hm₀
  have hsa := le_abs_self s
  have hna := neg_abs_le a.re
  have hnb := neg_abs_le b.re
  have hpa := le_abs_self a.re
  have hpb := le_abs_self b.re
  have hns := neg_abs_le s
  have hreg : ∀ d : ℂ, (m₀ : ℝ) - 1 / 2 < d.re →
      2 + s < d.re ∧ 0 < (d - a).re ∧ 0 < (d - b).re ∧ 0 < (c + d - a - b - 1).re := by
    intro d hd
    refine ⟨by linarith [abs_nonneg a.re, abs_nonneg b.re], ?_, ?_, ?_⟩
    · simp only [Complex.sub_re]; linarith [abs_nonneg s, abs_nonneg b.re]
    · simp only [Complex.sub_re]; linarith [abs_nonneg s, abs_nonneg a.re]
    · simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
      linarith [abs_nonneg a.re, abs_nonneg b.re]
  have hne : ∀ d : ℂ, (m₀ : ℝ) - 1 / 2 < d.re →
      Gamma (d - a) ≠ 0 ∧ Gamma (d - b) ≠ 0 ∧ Gamma (c + d - a - b - 1) ≠ 0 ∧
        d - a ≠ 0 ∧ d - b ≠ 0 ∧ c + d - a - b - 1 ≠ 0 := by
    intro d hd
    obtain ⟨-, h1, h2, h3⟩ := hreg d hd
    exact ⟨Complex.Gamma_ne_zero_of_re_pos h1, Complex.Gamma_ne_zero_of_re_pos h2,
      Complex.Gamma_ne_zero_of_re_pos h3, fun h => by rw [h] at h1; simp at h1,
      fun h => by rw [h] at h2; simp at h2, fun h => by rw [h] at h3; simp at h3⟩
  set F : ℂ → ℂ := fun w => L (m₀ + w) * N (m₀ + w) - K with hF
  -- holomorphy
  have hLd : DifferentiableOn ℂ L {d : ℂ | 1 + s < d.re} := differentiableOn_tsum ha hb
  have hFd : DifferentiableOn ℂ F {w : ℂ | -(1 / 2) < w.re} := by
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw
    have hd : (m₀ : ℝ) - 1 / 2 < ((m₀ : ℂ) + w).re := by simp; linarith
    obtain ⟨hd2, h1, h2, h3⟩ := hreg _ hd
    apply DifferentiableAt.differentiableWithinAt
    have hLw : DifferentiableAt ℂ (fun w => L (m₀ + w)) w := by
      have hU : {d : ℂ | 1 + s < d.re} ∈ 𝓝 ((m₀ : ℂ) + w) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
          simp only [Set.mem_ofPred_eq]; linarith)
      exact (hLd.differentiableAt hU).comp w (differentiableAt_id.const_add _)
    have hG1 : DifferentiableAt ℂ (fun w => Gamma ((m₀ : ℂ) + w - a)) w :=
      (Complex.differentiableAt_Gamma _ fun m hm => by
        rw [hm] at h1; simp at h1; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).comp w
        ((differentiableAt_id.const_add _).sub_const _)
    have hG2 : DifferentiableAt ℂ (fun w => Gamma ((m₀ : ℂ) + w - b)) w :=
      (Complex.differentiableAt_Gamma _ fun m hm => by
        rw [hm] at h2; simp at h2; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).comp w
        ((differentiableAt_id.const_add _).sub_const _)
    have hG3 : DifferentiableAt ℂ (fun w => (Gamma (c + ((m₀ : ℂ) + w) - a - b - 1))⁻¹) w :=
      (Complex.differentiable_one_div_Gamma _).comp w (by fun_prop)
    exact ((hLw.mul ((hG1.mul hG2).mul hG3)).sub_const K)
  -- periodicity
  have hper : ∀ w : ℂ, 0 ≤ w.re → F (w + 1) = F w := by
    intro w hw
    set d : ℂ := (m₀ : ℂ) + w with hd
    have hdre : (m₀ : ℝ) - 1 / 2 < d.re := by simp [hd]; linarith
    obtain ⟨hd2, -, -, -⟩ := hreg d hdre
    obtain ⟨-, -, hG3, hda, hdb, he⟩ := hne d hdre
    have hrec := tsum_recurrence (c := c) ha hb (d := d) hd2
    have e1 : (m₀ : ℂ) + (w + 1) = d + 1 := by rw [hd]; ring
    simp only [hF]
    rw [e1, ← hd]
    congr 1
    simp only [hN, hL]
    have g1 : Gamma (d + 1 - a) = (d - a) * Gamma (d - a) := by
      rw [show d + 1 - a = (d - a) + 1 by ring, Complex.Gamma_add_one _ hda]
    have g2 : Gamma (d + 1 - b) = (d - b) * Gamma (d - b) := by
      rw [show d + 1 - b = (d - b) + 1 by ring, Complex.Gamma_add_one _ hdb]
    have g3 : Gamma (c + (d + 1) - a - b - 1) =
        (c + d - a - b - 1) * Gamma (c + d - a - b - 1) := by
      rw [show c + (d + 1) - a - b - 1 = (c + d - a - b - 1) + 1 by ring,
        Complex.Gamma_add_one _ he]
    rw [g1, g2, g3, mul_inv]
    field_simp
    linear_combination (Gamma (d - a) * Gamma (d - b)) * hrec
  -- the value at `0`, from Gauss's summation at `d = m₀`
  have hF0 : F 0 = 0 := by
    have hγ : ∀ k : ℕ, c + 1 - ((m₀ : ℤ) : ℂ) ≠ -k := fun k h =>
      hc (m₀ - 1 - k) (by push_cast at h ⊢; linear_combination h)
    have hcv : 1 + (a + b).re < (c + ((m₀ : ℤ) : ℂ)).re := by
      simp only [Complex.add_re, Int.cast_natCast, Complex.natCast_re]
      linarith [abs_nonneg a.re, abs_nonneg b.re, abs_nonneg s, hsre]
    have h := tsum_at_int (c := c) ha hb (m₀ : ℤ) hγ hcv
    simp only [Int.cast_natCast] at h
    have hdre : (m₀ : ℝ) - 1 / 2 < ((m₀ : ℂ)).re := by simp
    obtain ⟨hGa, hGb, hG3, -, -, -⟩ := hne _ hdre
    simp only [hF, add_zero, hL, hN]
    rw [h, hRform, sub_eq_zero]
    simp only [hR]
    field_simp
  -- the strip bound
  obtain ⟨C₁, K₁, hC₁, hb₁⟩ := exists_norm_Gamma_add_le_strip (-a)
    (X₁ := m₀ - a.re) (X₂ := m₀ + 1 - a.re) (by linarith [abs_nonneg s, abs_nonneg b.re])
  obtain ⟨C₂, K₂, hC₂, hb₂⟩ := exists_norm_Gamma_add_le_strip (-b)
    (X₁ := m₀ - b.re) (X₂ := m₀ + 1 - b.re) (by linarith [abs_nonneg s, abs_nonneg a.re])
  obtain ⟨C₃, K₃, hC₃, hb₃⟩ := exists_norm_recip_Gamma_add_le_strip (c - a - b - 1)
    (m₀ + 1 + |(c - a - b - 1).re|)
  obtain ⟨u, hu, hu0, hbd⟩ := exists_bound (c := c) ha hb (x₁ := m₀)
    (by linarith [abs_nonneg a.re, abs_nonneg b.re])
  set S := ∑' n : ℤ, u n with hS
  have hS0 : 0 ≤ S := tsum_nonneg hu0
  have hstrip : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖F w‖ ≤ (S * (C₁ * C₂ * C₃) + ‖K‖) * (1 + |w.im|) ^ (K₁ + K₂ + K₃) *
        Real.exp (π / 2 * |w.im|) := by
    intro w hw0 hw1
    set d : ℂ := (m₀ : ℂ) + w with hd
    have hdre0 : (m₀ : ℝ) ≤ d.re := by simp [hd]; linarith
    have hdre1 : d.re ≤ m₀ + 1 := by simp [hd]; linarith
    have hdim : d.im = w.im := by simp [hd]
    set y := w.im
    have hLb : ‖L d‖ ≤ Real.exp (π * |y|) * S := by
      rw [← hdim]
      exact tsum_of_norm_bounded (hu.hasSum.mul_left _) fun n => hbd n d hdre0 hdre1
    have h1 : ‖Gamma (d - a)‖ ≤ C₁ * (1 + |y|) ^ K₁ * Real.exp (-(π * |y|) / 2) := by
      rw [← hdim, sub_eq_add_neg]
      exact hb₁ d (by simp; linarith) (by simp; linarith)
    have h2 : ‖Gamma (d - b)‖ ≤ C₂ * (1 + |y|) ^ K₂ * Real.exp (-(π * |y|) / 2) := by
      rw [← hdim, sub_eq_add_neg]
      exact hb₂ d (by simp; linarith) (by simp; linarith)
    have h3 : ‖(Gamma (c + d - a - b - 1))⁻¹‖ ≤
        C₃ * (1 + |y|) ^ K₃ * Real.exp (π * |y| / 2) := by
      rw [← hdim, show c + d - a - b - 1 = d + (c - a - b - 1) by ring]
      refine hb₃ d ?_
      rw [abs_le]
      have := abs_le.mp (le_refl |(c - a - b - 1).re|)
      constructor
      · simp only [Complex.add_re]; linarith [neg_abs_le (c - a - b - 1).re]
      · simp only [Complex.add_re]; linarith [le_abs_self (c - a - b - 1).re]
    have hNb : ‖N d‖ ≤ (C₁ * C₂ * C₃) * (1 + |y|) ^ (K₁ + K₂ + K₃) *
        Real.exp (-(π * |y|) / 2) := by
      simp only [hN, norm_mul]
      calc ‖Gamma (d - a)‖ * ‖Gamma (d - b)‖ * ‖(Gamma (c + d - a - b - 1))⁻¹‖
          ≤ (C₁ * (1 + |y|) ^ K₁ * Real.exp (-(π * |y|) / 2)) *
              (C₂ * (1 + |y|) ^ K₂ * Real.exp (-(π * |y|) / 2)) *
              (C₃ * (1 + |y|) ^ K₃ * Real.exp (π * |y| / 2)) := by
            gcongr
        _ = (C₁ * C₂ * C₃) * (1 + |y|) ^ (K₁ + K₂ + K₃) * Real.exp (-(π * |y|) / 2) := by
            have hEE : Real.exp (-(π * |y|) / 2) * Real.exp (π * |y| / 2) = 1 := by
              rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
            rw [pow_add, pow_add]
            linear_combination (C₁ * C₂ * C₃ * (1 + |y|) ^ K₁ * (1 + |y|) ^ K₂ *
              (1 + |y|) ^ K₃ * Real.exp (-(π * |y|) / 2)) * hEE
    have hpos : 1 ≤ (1 + |y|) ^ (K₁ + K₂ + K₃) * Real.exp (π / 2 * |y|) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [abs_nonneg y]))
        (Real.one_le_exp (by positivity))
    calc ‖F w‖ = ‖L d * N d - K‖ := rfl
      _ ≤ ‖L d‖ * ‖N d‖ + ‖K‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_mul]
      _ ≤ (Real.exp (π * |y|) * S) *
            ((C₁ * C₂ * C₃) * (1 + |y|) ^ (K₁ + K₂ + K₃) * Real.exp (-(π * |y|) / 2)) +
            ‖K‖ * ((1 + |y|) ^ (K₁ + K₂ + K₃) * Real.exp (π / 2 * |y|)) := by
          gcongr
          · exact le_mul_of_one_le_right (norm_nonneg _) hpos
      _ = (S * (C₁ * C₂ * C₃) + ‖K‖) * (1 + |y|) ^ (K₁ + K₂ + K₃) *
            Real.exp (π / 2 * |y|) := by
          have : Real.exp (π * |y|) * Real.exp (-(π * |y|) / 2) = Real.exp (π / 2 * |y|) := by
            rw [← Real.exp_add]; ring_nf
          linear_combination (S * (C₁ * C₂ * C₃) * (1 + |y|) ^ (K₁ + K₂ + K₃)) * this
  -- Carlson
  have hzero := CarlsonAux.eq_zero_of_periodic_of_bound (by norm_num : (0 : ℝ) < 1 / 2) hFd hper
    (σ := π / 2) (by linarith [Real.pi_pos]) hstrip hF0
  -- hence `L = R` on `Re d ≥ m₀`
  have hLR : ∀ d : ℂ, (m₀ : ℝ) ≤ d.re → L d = R d := by
    intro d hd
    have h := hzero (d - m₀) (by simp; linarith)
    simp only [hF, add_sub_cancel, sub_eq_zero] at h
    obtain ⟨hGa, hGb, hG3, -, -, -⟩ := hne d (by linarith)
    simp only [hN] at h
    simp only [hR]
    rw [← h]
    field_simp
  -- extend by the identity theorem
  set U : Set ℂ := {d : ℂ | 1 + s < d.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hdU : d ∈ U := by
    simp only [hU, Set.mem_ofPred_eq, hsre]
    simp only [Complex.add_re] at hconv
    linarith
  have hRd : DifferentiableOn ℂ R U := by
    intro z hz
    simp only [hU, Set.mem_ofPred_eq, hsre] at hz
    have hre : 0 < (c + z - a - b - 1).re := by
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; linarith
    apply DifferentiableAt.differentiableWithinAt
    have hG : DifferentiableAt ℂ (fun z => Gamma (c + z - a - b - 1)) z :=
      (Complex.differentiableAt_Gamma _ fun m hm => by
        rw [hm] at hre; simp at hre; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).comp z
        (by fun_prop)
    have hi1 : DifferentiableAt ℂ (fun z => (Gamma (z - a))⁻¹) z :=
      (Complex.differentiable_one_div_Gamma _).comp z (by fun_prop)
    have hi2 : DifferentiableAt ℂ (fun z => (Gamma (z - b))⁻¹) z :=
      (Complex.differentiable_one_div_Gamma _).comp z (by fun_prop)
    exact ((hG.const_mul K).mul hi1).mul hi2
  have hz₀ : (m₀ : ℂ) + 1 ∈ U := by
    simp only [hU, Set.mem_ofPred_eq]; simp
    linarith [abs_nonneg a.re, abs_nonneg b.re]
  have hev : L =ᶠ[𝓝 ((m₀ : ℂ) + 1)] R := by
    have hopen : {z : ℂ | (m₀ : ℝ) < z.re} ∈ 𝓝 ((m₀ : ℂ) + 1) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hopen] with z hz
    exact hLR z (le_of_lt hz)
  exact ((hLd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hRd.analyticOnNhd hUo)
    (convex_halfSpace_re_gt (1 + s)).isPreconnected hz₀ hev) hdU

/-- Dougall's terms are symmetric in the denominator parameters `c` and `d`. -/
theorem term_comm (a b c d : ℂ) (n : ℤ) : term a b c d n = term a b d c n := by
  simp only [term, mul_comm (Gamma (c + n))]

/-- The right-hand side of Dougall's formula is symmetric in `c` and `d`. -/
theorem rhs_comm (a b c d : ℂ) :
    π ^ 2 * Gamma (d + c - a - b - 1) /
        (Complex.sin (π * a) * Complex.sin (π * b) * Gamma (d - a) * Gamma (c - a) *
          Gamma (d - b) * Gamma (c - b)) =
      π ^ 2 * Gamma (c + d - a - b - 1) /
        (Complex.sin (π * a) * Complex.sin (π * b) * Gamma (c - a) * Gamma (d - a) *
          Gamma (c - b) * Gamma (d - b)) := by
  rw [add_comm d c]; ring

/-- Dougall's sum when both `c` and `d` are integers, with `d ≤ c`. -/
theorem tsum_at_int_int (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k) {j m : ℤ} (hjm : m ≤ j)
    (hconv : 1 + (a + b).re < ((j : ℂ) + m).re) :
    ∑' n : ℤ, term a b j m n =
      π ^ 2 * Gamma (j + m - a - b - 1) /
        (Complex.sin (π * a) * Complex.sin (π * b) * Gamma (j - a) * Gamma (m - a) *
          Gamma (j - b) * Gamma (m - b)) := by
  refine tsum_at_int ha hb m (fun k h => ?_) hconv
  have h' : ((j + 1 - m : ℤ) : ℂ) = ((-(k : ℤ) : ℤ) : ℂ) := by push_cast; linear_combination h
  have := Int.cast_injective h'
  omega

end DougallAux

namespace DixonAux

open CarlsonAux

variable {a b : ℂ}

end DixonAux
end CarlsonApplications
end DLMF.Hypergeometric
end
end
