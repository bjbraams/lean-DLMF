/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.SpecialFunctions.Trigonometric.PartialFractions
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Bernoulli numbers in the Taylor series of `cot`, `tan`, `z/sin z` and `z/(eᶻ-1)`

Mathlib has the Bernoulli generating function as a formal power series and the values
`ζ(2k) = (-1)^{k+1} 2^{2k-1} π^{2k} B₂ₖ/(2k)!`. Expanding each term `2z²/(z² - (n+1)²)` of the
cotangent's partial fractions as a geometric series and interchanging the double sum gives
`πz cot(πz) = 1 - 2 ∑ ζ(2k) z^{2k}` for `0 < ‖z‖ < 1` (Duverney (2.50)). The convergent Taylor
series follow:
* `hasSum_pi_mul_cot_bernoulli`: `πz cot(πz) = ∑ₖ (-1)ᵏ B₂ₖ (2πz)^{2k}/(2k)!` (DLMF 4.19.6);
* `hasSum_pi_mul_tan_bernoulli`: `πz tan(πz)`, from `tan z = cot z - 2 cot 2z` (DLMF 4.19.3);
* `hasSum_pi_mul_div_sin_bernoulli`: `πz/sin(πz)`, from `csc z = cot(z/2) - cot z` (DLMF 4.19.4);
* `hasSum_bernoulli_mul_pow_div`: `z/(eᶻ - 1) = ∑ Bₙ zⁿ/n!` for `0 < ‖z‖ < 2π` (DLMF 24.2.1,
  Duverney (2.46)), from the cotangent at `iz/(2π)`.
-/

@[expose] public section

open Filter
open scoped Real Topology Nat

noncomputable section

namespace Complex

/-- `∑ₙ 1/(n+1)^k = ζ(k)` for natural `k > 1`. -/
lemma hasSum_one_div_nat_succ_pow {k : ℕ} (hk : 1 < k) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ k) (riemannZeta k) := by
  have hs : Summable fun n : ℕ => 1 / (n : ℂ) ^ k :=
    Summable.of_norm (by simpa using Real.summable_one_div_nat_pow.mpr hk)
  have h := (hasSum_nat_add_iff' 1).mpr hs.hasSum
  rw [zeta_nat_eq_tsum_of_gt_one hk]
  simpa [Finset.sum_range_one, zero_pow (by omega : k ≠ 0)] using h

/-- **Cotangent Taylor series** (Duverney (2.50)): for `0 < ‖z‖ < 1`,
`πz cot(πz) = 1 - 2 ∑_{k≥1} ζ(2k) z^{2k}`. -/
theorem hasSum_pi_mul_cot_zeta {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasSum (fun k : ℕ => -2 * riemannZeta (2 * (k + 1)) * z ^ (2 * (k + 1)))
      (π * z * cot (π * z) - 1) := by
  have hzZ : z ∈ integerComplement := by
    rintro ⟨n, hn⟩
    rcases eq_or_ne n 0 with rfl | hn0
    · exact hz0 (by simpa using hn.symm)
    · have : (1 : ℝ) ≤ ‖z‖ := by
        rw [← hn, Complex.norm_intCast]; exact_mod_cast Int.one_le_abs hn0
      linarith
  set F : ℕ × ℕ → ℂ := fun p => -2 * (z ^ 2 / ((p.1 : ℂ) + 1) ^ 2) ^ (p.2 + 1) with hF
  have hw (n : ℕ) : ‖z ^ 2 / ((n : ℂ) + 1) ^ 2‖ < 1 := by
    have : (1 : ℝ) ≤ ‖(n : ℂ) + 1‖ := by
      rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      exact_mod_cast Nat.succ_pos n
    rw [norm_div, norm_pow, norm_pow, div_lt_one (pow_pos (lt_of_lt_of_le one_pos this) 2)]
    nlinarith [norm_nonneg z]
  have hn1 (n : ℕ) : (1 : ℝ) ≤ ‖((n : ℂ) + 1) ^ 2‖ := by
    rw [norm_pow, show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    exact one_le_pow₀ (by exact_mod_cast Nat.succ_pos n)
  have hsum : Summable F := by
    have h1 : Summable fun n : ℕ => 1 / ‖((n : ℂ) + 1) ^ 2‖ := by
      have := (Real.summable_one_div_nat_add_rpow 1 2).mpr one_lt_two
      refine this.congr fun n => ?_
      rw [norm_pow, show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_eq_abs, Real.rpow_two]
    have hg := h1.mul_of_nonneg (summable_geometric_of_lt_one (sq_nonneg ‖z‖)
      (by nlinarith [norm_nonneg z] : ‖z‖ ^ 2 < 1)) (fun n => by positivity)
      (fun k => by positivity)
    refine Summable.of_norm_bounded (hg.mul_left 2) fun p => ?_
    have hb := hn1 p.1
    have ha : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    simp only [hF, norm_mul, norm_neg, norm_pow, norm_div, Complex.norm_ofNat]
    rw [norm_pow] at hb
    set b := ‖(p.1 : ℂ) + 1‖ ^ 2
    have hb0 : 0 < b := lt_of_lt_of_le one_pos hb
    rw [div_pow]
    gcongr
    calc (‖z‖ ^ 2) ^ (p.2 + 1) / b ^ (p.2 + 1) ≤ (‖z‖ ^ 2) ^ p.2 / b :=
          div_le_div₀ (by positivity) (pow_le_pow_of_le_one (sq_nonneg _) ha (Nat.le_succ _))
            hb0 (le_self_pow₀ hb (Nat.succ_ne_zero _))
      _ = 1 / b * (‖z‖ ^ 2) ^ p.2 := by ring
  -- rows: geometric series in `k`
  have hrow (n : ℕ) : HasSum (fun k => F (n, k)) (z * cotTerm z n) := by
    have hg := (hasSum_geometric_of_norm_lt_one (hw n)).mul_left (-2 * (z ^ 2 / ((n : ℂ) + 1) ^ 2))
    have hn0 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hd : ((n : ℂ) + 1) ^ 2 - z ^ 2 ≠ 0 := by
      intro h
      have := hw n
      rw [show z ^ 2 = ((n : ℂ) + 1) ^ 2 by linear_combination -h, div_self (pow_ne_zero 2 hn0),
        norm_one] at this
      exact lt_irrefl _ this
    convert hg using 1
    · funext k; simp only [hF, pow_succ]; ring
    · rw [cotTerm_identity hzZ,
        show (z + (n + 1)) * (z - (n + 1)) = -(((n : ℂ) + 1) ^ 2 - z ^ 2) by ring,
        show 1 - z ^ 2 / ((n : ℂ) + 1) ^ 2 = (((n : ℂ) + 1) ^ 2 - z ^ 2) / ((n : ℂ) + 1) ^ 2 by
          field_simp]
      generalize ((n : ℂ) + 1) ^ 2 - z ^ 2 = d at *
      field_simp
  -- columns: zeta values
  have hcol (k : ℕ) : HasSum (fun n => F (n, k))
      (-2 * riemannZeta (2 * (k + 1)) * z ^ (2 * (k + 1))) := by
    have h := (hasSum_one_div_nat_succ_pow (k := 2 * (k + 1)) (by omega)).mul_left
      (-2 * z ^ (2 * (k + 1)))
    push_cast at h
    convert h using 1
    · funext n; simp only [hF]; rw [div_pow, ← pow_mul, ← pow_mul]; ring
    · ring
  have hT := hsum.hasSum
  have hrows := hT.prod_fiberwise hrow
  have hcot := (hasSum_cotTerm hzZ).mul_left z
  have hval := hrows.unique hcot
  have hT' : HasSum (F ∘ Prod.swap) (∑' p, F p) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hT
  have hcols := hT'.prod_fiberwise fun k => hcol k
  rw [hval] at hcols
  convert hcols using 1
  field_simp

/-- **Bernoulli numbers in the cotangent series** (Duverney (2.50), DLMF 4.19.6): for
`0 < ‖z‖ < 1`, `πz cot(πz) = ∑ₖ (-1)ᵏ B₂ₖ (2πz)^{2k}/(2k)!`. -/
@[dlmf 4.19.E6]
theorem hasSum_pi_mul_cot_bernoulli {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasSum (fun k : ℕ => (-1) ^ k * (bernoulli (2 * k) : ℂ) * (2 * π * z) ^ (2 * k) / (2 * k)!)
      (π * z * cot (π * z)) := by
  have h := hasSum_pi_mul_cot_zeta hz hz0
  refine (hasSum_nat_add_iff' 1).mp ?_
  simp only [Finset.sum_range_one, pow_zero, mul_zero, bernoulli_zero, Nat.factorial_zero,
    Nat.cast_one, Rat.cast_one, one_mul, div_one]
  refine h.congr_fun fun k => ?_
  have hk : k + 1 ≠ 0 := Nat.succ_ne_zero k
  have hz2 := riemannZeta_two_mul_nat hk
  push_cast at hz2
  rw [hz2, show 2 * (k + 1) - 1 = 2 * k + 1 by omega, mul_pow, mul_pow,
    show (2 : ℂ) ^ (2 * (k + 1)) = 2 ^ (2 * k + 1) * 2 by rw [← pow_succ]; ring_nf]
  have hf : ((2 * (k + 1))! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  ring

/-- **The Bernoulli generating function** (Duverney (2.46), DLMF 24.2.1): for `0 < ‖z‖ < 2π`,
`z/(eᶻ - 1) = ∑ₙ Bₙ zⁿ/n!`. -/
@[dlmf 24.2.E1]
theorem hasSum_bernoulli_mul_pow_div {z : ℂ} (hz : ‖z‖ < 2 * π) (hz0 : z ≠ 0) :
    HasSum (fun n : ℕ => (bernoulli n : ℂ) * z ^ n / n !) (z / (exp z - 1)) := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  set u : ℂ := I * z / (2 * π) with hu
  have hpi' : (2 * π : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
  have hun : ‖u‖ < 1 := by
    rw [hu, norm_div, norm_mul, norm_I, one_mul, show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by
      push_cast; ring, norm_real, Real.norm_of_nonneg hpi.le, div_lt_one hpi]
    exact hz
  have hu0 : u ≠ 0 := div_ne_zero (mul_ne_zero I_ne_zero hz0) hpi'
  have hexp : exp z ≠ 1 := by
    intro h
    obtain ⟨n, hn⟩ := exp_eq_one_iff.mp h
    rcases eq_or_ne n 0 with rfl | hn0
    · exact hz0 (by simpa using hn)
    · have : 2 * π ≤ ‖z‖ := by
        rw [hn, norm_mul, norm_mul, norm_mul, norm_I, Complex.norm_intCast, mul_one]
        have : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
        rw [show ‖(2 : ℂ)‖ = 2 by simp, show ‖(π : ℂ)‖ = π by simp [abs_of_pos Real.pi_pos]]
        nlinarith [Real.pi_pos]
      linarith
  have hcot := hasSum_pi_mul_cot_bernoulli hun hu0
  -- the value
  have hval : (π : ℂ) * u * cot (π * u) = z / (exp z - 1) + z / 2 := by
    have h1 : (π : ℂ) * u = (z / 2) * I := by rw [hu]; field_simp
    rw [h1, cot_eq_cos_div_sin, cos_mul_I, sin_mul_I, cosh, sinh]
    have hs : exp (z / 2) - exp (-(z / 2)) ≠ 0 := by
      intro h
      apply hexp
      rw [show z = z / 2 - -(z / 2) by ring, exp_sub, ← sub_eq_zero.mp h,
        div_self (exp_ne_zero _)]
    have he : exp z = exp (z / 2) * exp (z / 2) := by rw [← exp_add]; ring_nf
    have he' : exp (-(z / 2)) * exp (z / 2) = 1 := by rw [← exp_add]; simp
    have hz1 : exp z - 1 ≠ 0 := sub_ne_zero.mpr hexp
    have hA : exp (z / 2) ≠ 0 := exp_ne_zero _
    rw [he] at hz1 ⊢
    rw [eq_inv_of_mul_eq_one_left he'] at hs ⊢
    generalize exp (z / 2) = A at *
    rw [show A + A⁻¹ = (A * A + 1) / A by field_simp,
      show A - A⁻¹ = (A * A - 1) / A by field_simp]
    generalize hD : A * A - 1 = D at *
    have hI : I ≠ 0 := I_ne_zero
    field_simp
    linear_combination hD
  rw [hval] at hcot
  have heven : HasSum (fun k => (bernoulli (2 * k) : ℂ) * z ^ (2 * k) / (2 * k)!)
      (z / (exp z - 1) + z / 2) := by
    refine hcot.congr_fun fun k => ?_
    rw [show 2 * (π : ℂ) * u = I * z by rw [hu]; field_simp, mul_pow, pow_mul I, I_sq]
    have h1 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-((bernoulli (2 * k) : ℂ) * z ^ (2 * k) / (2 * k)!)) * h1
  have hodd : HasSum (fun k => (bernoulli (2 * k + 1) : ℂ) * z ^ (2 * k + 1) / (2 * k + 1)!)
      (-(z / 2)) := by
    convert hasSum_single (f := fun k => (bernoulli (2 * k + 1) : ℂ) * z ^ (2 * k + 1) /
      (2 * k + 1)!) 0 (fun k hk => ?_) using 1
    · simp only [mul_zero, zero_add, bernoulli_one, pow_one, Nat.factorial_one, Nat.cast_one,
        div_one]
      push_cast; ring
    · rw [bernoulli_eq_zero_of_odd (odd_two_mul_add_one k) (by omega)]
      simp
  have h := HasSum.even_add_odd (f := fun n : ℕ => (bernoulli n : ℂ) * z ^ n / n !) heven hodd
  rwa [show z / (exp z - 1) + z / 2 + -(z / 2) = z / (exp z - 1) by ring] at h

/-- A nonzero point of the open unit disc is not an integer. -/
lemma mem_integerComplement_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    z ∈ integerComplement := by
  rintro ⟨n, hn⟩
  rcases eq_or_ne n 0 with rfl | hn0
  · exact hz0 (by simpa using hn.symm)
  · have : (1 : ℝ) ≤ ‖z‖ := by
      rw [← hn, Complex.norm_intCast]; exact_mod_cast Int.one_le_abs hn0
    linarith

/-- **Tangent Taylor series** (Duverney (2.51), DLMF 4.19.3): for `0 < ‖z‖ < ½`,
`πz tan(πz) = ∑ₖ (-1)ᵏ B₂ₖ (1 - 4ᵏ) (2πz)^{2k}/(2k)!`. -/
@[dlmf 4.19.E3]
theorem hasSum_pi_mul_tan_bernoulli {z : ℂ} (hz : ‖z‖ < 1 / 2) (hz0 : z ≠ 0) :
    HasSum (fun k : ℕ => (-1) ^ k * (bernoulli (2 * k) : ℂ) * (1 - 4 ^ k) *
      (2 * π * z) ^ (2 * k) / (2 * k)!) (π * z * tan (π * z)) := by
  have h2z : ‖2 * z‖ < 1 := by rw [norm_mul, Complex.norm_ofNat]; linarith
  have h1 := hasSum_pi_mul_cot_bernoulli (by linarith) hz0
  have h2 := hasSum_pi_mul_cot_bernoulli h2z (mul_ne_zero two_ne_zero hz0)
  have hs1 := sin_pi_mul_ne_zero (mem_integerComplement_of_norm_lt_one (by linarith) hz0)
  have hs2 := sin_pi_mul_ne_zero (mem_integerComplement_of_norm_lt_one h2z
    (mul_ne_zero two_ne_zero hz0))
  have hcos : cos (π * z) ≠ 0 := by
    intro h; apply hs2; rw [show (π : ℂ) * (2 * z) = 2 * (π * z) by ring, sin_two_mul, h]; ring
  have htan : (π : ℂ) * z * tan (π * z) =
      π * z * cot (π * z) - π * (2 * z) * cot (π * (2 * z)) := by
    rw [tan_eq_sin_div_cos, cot_eq_cos_div_sin, cot_eq_cos_div_sin,
      show (π : ℂ) * (2 * z) = 2 * (π * z) by ring, sin_two_mul, cos_two_mul]
    field_simp
    have := sin_sq_add_cos_sq ((π : ℂ) * z)
    linear_combination this
  rw [htan]
  refine (h1.sub h2).congr_fun fun k => ?_
  rw [show 2 * (π : ℂ) * (2 * z) = 2 * (2 * π * z) by ring, mul_pow (2 : ℂ),
    pow_mul (2 : ℂ), show (2 : ℂ) ^ 2 = 4 by norm_num]
  ring

/-- **Taylor series of `z/sin z`** (Duverney (2.53), DLMF 4.19.4): for `0 < ‖z‖ < 1`,
`πz/sin(πz) = ∑ₖ (-1)ᵏ B₂ₖ (2 - 4ᵏ) (πz)^{2k}/(2k)!`. -/
@[dlmf 4.19.E4]
theorem hasSum_pi_mul_div_sin_bernoulli {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasSum (fun k : ℕ => (-1) ^ k * (bernoulli (2 * k) : ℂ) * (2 - 4 ^ k) *
      (π * z) ^ (2 * k) / (2 * k)!) (π * z / sin (π * z)) := by
  have hz2 : ‖z / 2‖ < 1 := by rw [norm_div, Complex.norm_ofNat]; linarith [norm_nonneg z]
  have hz20 : z / 2 ≠ 0 := div_ne_zero hz0 two_ne_zero
  have h1 := hasSum_pi_mul_cot_bernoulli hz hz0
  have h2 := hasSum_pi_mul_cot_bernoulli hz2 hz20
  have hs1 := sin_pi_mul_ne_zero (mem_integerComplement_of_norm_lt_one hz hz0)
  have hcsc : (π : ℂ) * z / sin (π * z) =
      2 * (π * (z / 2) * cot (π * (z / 2))) - π * z * cot (π * z) := by
    rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin,
      show (π : ℂ) * z = 2 * (π * (z / 2)) by ring, sin_two_mul, cos_two_mul]
    rw [show (π : ℂ) * z = 2 * (π * (z / 2)) by ring, sin_two_mul] at hs1
    generalize (π : ℂ) * (z / 2) = w at *
    have hc : cos w ≠ 0 := fun h => hs1 (by rw [h]; ring)
    have hsw : sin w ≠ 0 := fun h => hs1 (by rw [h]; ring)
    field_simp
    ring
  rw [hcsc]
  refine ((h2.mul_left 2).sub h1).congr_fun fun k => ?_
  rw [show 2 * (π : ℂ) * (z / 2) = π * z by ring, show 2 * (π : ℂ) * z = 2 * (π * z) by ring,
    mul_pow (2 : ℂ), pow_mul (2 : ℂ), show (2 : ℂ) ^ 2 = 4 by norm_num]
  ring

end Complex

end
