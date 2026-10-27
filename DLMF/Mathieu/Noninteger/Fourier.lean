/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Noninteger.Properties
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Fourier series of the Mathieu functions of noninteger order (DLMF §28.14)

`me_ν(z, q) = ∑_m c^ν_{2m}(q) e^{i(ν+2m)z}` (28.14.1), with the cosine and sine series of
`ce_ν`, `se_ν` (28.14.2–28.14.3), the recurrence 28.14.4, the normalization 28.14.5, the rate
of convergence 28.14.6, the symmetries 28.14.7–28.14.8, the values at `q = 0` (28.14.9) and the
leading small-`q` behaviour 28.14.10. The coefficient `c^ν_{2m}(q)` is
`DLMF.Mathieu.mathieuMeCoeff ν q m` (index `m`).

All statements are for `ν ∉ ℤ`; those about the continued coefficients assume `q` normal along
the segment `[0, q]` (`MathieuNormalSegment ν q`, automatic for real `ν`, `q`). Proved: the
convergence 28.14.1 (absolute, locally uniform on `ℂ`) and 28.14.2–28.14.3, 28.14.4, 28.14.5,
the rate 28.14.6 (via the monotone decay and nonvanishing of the tail of a minimal solution of
28.14.4), 28.14.7, 28.14.8, 28.14.9.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real Classical

namespace DLMF.Mathieu

variable {ν : ℂ}

/-- **Fourier series of `me_ν`** (DLMF 28.14.1): for `ν ∉ ℤ` and `q` normal along the segment,
`me_ν(z, q) = ∑_{m ∈ ℤ} c^ν_{2m}(q) e^{i(ν+2m)z}`, converging absolutely for every complex `z`
and uniformly on compact subsets of `ℂ`. -/
@[dlmf 28.14.E1]
theorem hasSum_mathieuMe (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {q : ℂ} (hq : MathieuNormalSegment ν q) :
    (∀ z : ℂ, Summable (fun m : ℤ => ‖mathieuMeCoeff ν q m * Complex.exp (I * (ν + 2 * m) * z)‖)
      ∧ HasSum (fun m : ℤ => mathieuMeCoeff ν q m * Complex.exp (I * (ν + 2 * m) * z))
        (mathieuMe ν z q)) ∧
    TendstoLocallyUniformly
      (fun (s : Finset ℤ) (z : ℂ) =>
        ∑ m ∈ s, mathieuMeCoeff ν q m * Complex.exp (I * (ν + 2 * m) * z))
      (fun z => mathieuMe ν z q) atTop := by
  have hd := m28b_isMeCoeffSeq_data hq
  set c := (mathieuLambdaData ν q).2
  have hcoef : ∀ m, mathieuMeCoeff ν q m = c m := fun m => mathieuMeCoeff_of_not_int hν q m
  have hme : ∀ z, mathieuMe ν z q = ∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * z) := by
    intro z; rw [mathieuMe_of_not_int hν]; simp only [hcoef]
  simp only [hcoef, hme]
  have hsum : ∀ z : ℂ,
      Summable (fun m : ℤ => ‖c m * Complex.exp (I * (ν + 2 * m) * z)‖) := fun z => by
    simpa using p1b_summable_series hd.1 hd.2.1 0 z
  refine ⟨fun z => ⟨hsum z, (hsum z).of_norm.hasSum⟩, ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine tendstoUniformlyOn_tsum (p1b_summable_bound hd.1 hd.2.1 R 0) fun m z hz => ?_
  have hzR : ‖z‖ ≤ R := by simpa using hR hz
  rw [norm_mul]
  gcongr
  simpa using p1b_norm_pow_exp_le ν z m hzR 0

/-- The Fourier series 28.14.1 on the **real axis** (proved): for `ν ∉ ℤ`, `q` normal along the
segment and real `x`, the series converges absolutely to `me_ν(x, q)` (the coefficients are
absolutely summable by construction). -/
@[dlmf 28.14.E1]
theorem hasSum_mathieuMe_ofReal (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {q : ℂ}
    (hq : MathieuNormalSegment ν q) (x : ℝ) :
    Summable (fun m : ℤ => ‖mathieuMeCoeff ν q m * Complex.exp (I * (ν + 2 * m) * x)‖) ∧
      HasSum (fun m : ℤ => mathieuMeCoeff ν q m * Complex.exp (I * (ν + 2 * m) * x))
        (mathieuMe ν x q) := by
  have hc := (m28b_isMeCoeffSeq_data hq).2.1
  have hn : ∀ m : ℤ, ‖mathieuMeCoeff ν q m * Complex.exp (I * (ν + 2 * m) * x)‖ =
      ‖(mathieuLambdaData ν q).2 m‖ * Real.exp (-(ν.im * x)) := by
    intro m
    rw [norm_mul, mathieuMeCoeff_of_not_int hν, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re, Complex.mul_im]
  have hs : Summable (fun m : ℤ => ‖mathieuMeCoeff ν q m * Complex.exp (I * (ν + 2 * m) * x)‖) :=
    by simp only [hn]; exact hc.mul_right _
  refine ⟨hs, ?_⟩
  rw [mathieuMe_of_not_int hν]
  exact (hs.of_norm).hasSum

/-- `e^{iθz} + e^{iθ(-z)} = 2 cos(θz)`. -/
lemma m28b_exp_add_exp_neg (θ z : ℂ) :
    Complex.exp (I * θ * z) + Complex.exp (I * θ * -z) = 2 * Complex.cos (θ * z) := by
  rw [show I * θ * z = (θ * z) * I by ring, show I * θ * -z = (-(θ * z)) * I by ring,
    Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  ring

/-- `-(i/2) (e^{iθz} - e^{iθ(-z)}) = sin(θz)`. -/
lemma m28b_exp_sub_exp_neg (θ z : ℂ) :
    -(I / 2) * (Complex.exp (I * θ * z) - Complex.exp (I * θ * -z)) = Complex.sin (θ * z) := by
  rw [show I * θ * z = (θ * z) * I by ring, show I * θ * -z = (-(θ * z)) * I by ring,
    Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  ring_nf
  rw [Complex.I_sq]; ring

/-- **Cosine series of `ce_ν`** (DLMF 28.14.2): `ce_ν(z, q) = ∑_m c^ν_{2m}(q) cos((ν+2m)z)` for
`ν ∉ ℤ` and `q` normal along the segment. Proved from 28.14.1. -/
@[dlmf 28.14.E2]
theorem hasSum_mathieuCeNu (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {q : ℂ} (hq : MathieuNormalSegment ν q)
    (z : ℂ) :
    HasSum (fun m : ℤ => mathieuMeCoeff ν q m * Complex.cos ((ν + 2 * m) * z))
      (mathieuCeNu ν z q) := by
  have h1 := ((hasSum_mathieuMe hν hq).1 z).2
  have h2 := ((hasSum_mathieuMe hν hq).1 (-z)).2
  have := (h1.add h2).div_const 2
  refine this.congr_fun fun m => ?_
  rw [← mul_add, m28b_exp_add_exp_neg]; ring

/-- **Sine series of `se_ν`** (DLMF 28.14.3): `se_ν(z, q) = ∑_m c^ν_{2m}(q) sin((ν+2m)z)` for
`ν ∉ ℤ` and `q` normal along the segment. Proved from 28.14.1. -/
@[dlmf 28.14.E3]
theorem hasSum_mathieuSeNu (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {q : ℂ} (hq : MathieuNormalSegment ν q)
    (z : ℂ) :
    HasSum (fun m : ℤ => mathieuMeCoeff ν q m * Complex.sin ((ν + 2 * m) * z))
      (mathieuSeNu ν z q) := by
  have h1 := ((hasSum_mathieuMe hν hq).1 z).2
  have h2 := ((hasSum_mathieuMe hν hq).1 (-z)).2
  have := (h1.sub h2).mul_left (-(I / 2))
  refine this.congr_fun fun m => ?_
  rw [← mul_sub, ← m28b_exp_sub_exp_neg]; ring

/-- **Recurrence** (DLMF 28.14.4): with `a = λ_ν(q)` and `c_{2m} = c^ν_{2m}(q)`,
`q c_{2m+2} - (a - (ν + 2m)²) c_{2m} + q c_{2m-2} = 0`, for `ν ∉ ℤ` and `q` normal along the
segment. -/
@[dlmf 28.14.E4]
theorem mathieuMeCoeff_recurrence (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {q : ℂ}
    (hq : MathieuNormalSegment ν q) (m : ℤ) :
    q * mathieuMeCoeff ν q (m + 1) - (mathieuLambda ν q - (ν + 2 * m) ^ 2) * mathieuMeCoeff ν q m
      + q * mathieuMeCoeff ν q (m - 1) = 0 := by
  simp only [mathieuMeCoeff_of_not_int hν, mathieuLambda_of_not_int hν]
  exact (m28b_isMeCoeffSeq_data hq).1 m

/-- **Normalization** (DLMF 28.14.5): `∑_m (c^ν_{2m}(q))² = 1` for `ν ∉ ℤ` and `q` normal along
the segment. -/
@[dlmf 28.14.E5]
theorem hasSum_mathieuMeCoeff_sq (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {q : ℂ}
    (hq : MathieuNormalSegment ν q) : HasSum (fun m : ℤ => mathieuMeCoeff ν q m ^ 2) 1 := by
  simp only [mathieuMeCoeff_of_not_int hν]
  exact (m28b_isMeCoeffSeq_data hq).2.2

/-- For large `k`, `‖a - (ν + 2k)²‖ ≥ 2k² + B` (any fixed `B`). -/
theorem p1b_norm_D_ge (ν a : ℂ) (B : ℝ) : ∃ M : ℕ, ∀ k : ℤ, (M : ℤ) ≤ k →
    2 * (k : ℝ) ^ 2 + B ≤ ‖a - (ν + 2 * k) ^ 2‖ := by
  obtain ⟨M, hM⟩ := exists_nat_ge (2 * ‖ν‖ + ‖a‖ + |B| + 1)
  refine ⟨M, fun k hk => ?_⟩
  have hk' : (M : ℝ) ≤ k := by exact_mod_cast hk
  have h2k : ‖(2 : ℂ) * k‖ = 2 * k := by
    have hk0 : (0 : ℝ) ≤ k := by linarith [norm_nonneg ν, abs_nonneg B, norm_nonneg a]
    rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hk0]; norm_num
  have h1 : 2 * (k : ℝ) - ‖ν‖ ≤ ‖ν + 2 * k‖ := by
    have := norm_sub_norm_le ((2 : ℂ) * k) (-ν)
    rw [h2k, norm_neg, sub_neg_eq_add, add_comm] at this
    exact this
  have hpos : 0 ≤ 2 * (k : ℝ) - ‖ν‖ := by linarith [norm_nonneg a, abs_nonneg B]
  have h4 : (2 * (k : ℝ) - ‖ν‖) ^ 2 ≤ ‖(ν + 2 * k) ^ 2‖ := by
    rw [norm_pow]; exact pow_le_pow_left₀ hpos h1 2
  have h5 := norm_sub_norm_le ((ν + 2 * k) ^ 2) a
  rw [norm_sub_rev] at h5
  have hB := le_abs_self B
  nlinarith [norm_nonneg ν, norm_nonneg a, abs_nonneg B]

/-- Ratio asymptotics on the right tail for a nontrivial absolutely summable solution of
28.14.4 with `q ≠ 0`: `c_m / c_{m-1} + q/(4m²) = O(m⁻³)`. -/
lemma p1b_ratio_tail {ν q a : ℂ} {c : ℤ → ℂ} (hq0 : q ≠ 0)
    (hrec : ∀ m : ℤ, q * c (m + 1) - (a - (ν + 2 * m) ^ 2) * c m + q * c (m - 1) = 0)
    (hs : Summable (fun m => ‖c m‖)) (hne : c ≠ 0) :
    (fun m : ℕ => c m / c (m - 1) + q / (4 * (m : ℂ) ^ 2))
      =O[atTop] (fun m : ℕ => ((m : ℝ) ^ 3)⁻¹) := by
  set D : ℤ → ℂ := fun k => a - (ν + 2 * k) ^ 2
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  obtain ⟨M, hM⟩ := p1b_norm_D_ge ν a (3 * ‖q‖)
  have hD3 : ∀ k : ℤ, (M : ℤ) ≤ k → 3 * ‖q‖ ≤ ‖D k‖ := fun k hk => by
    have := hM k hk; nlinarith [sq_nonneg (k : ℝ)]
  -- growth lemma
  have hgrow : ∀ k : ℤ, (M : ℤ) ≤ k → ‖c (k - 1)‖ < ‖c k‖ → 2 * ‖c k‖ ≤ ‖c (k + 1)‖ := by
    intro k hk hlt
    have he : D k * c k = q * c (k + 1) + q * c (k - 1) := by
      linear_combination -(hrec k)
    have h1 : ‖D k * c k‖ ≤ ‖q * c (k + 1)‖ + ‖q * c (k - 1)‖ := by
      rw [he]; exact norm_add_le _ _
    rw [norm_mul, norm_mul, norm_mul] at h1
    have : 3 * ‖q‖ * ‖c k‖ ≤ ‖D k‖ * ‖c k‖ := mul_le_mul_of_nonneg_right (hD3 k hk) (norm_nonneg _)
    nlinarith
  have hmono : ∀ k : ℤ, (M : ℤ) ≤ k → ‖c (k + 1)‖ ≤ ‖c k‖ := by
    intro k hk
    by_contra hlt
    push Not at hlt
    have hpos : 0 < ‖c (k + 1)‖ := lt_of_le_of_lt (norm_nonneg _) hlt
    have hind : ∀ j : ℕ, ‖c (k + 1)‖ ≤ ‖c (k + 1 + j)‖ ∧ ‖c (k + j)‖ < ‖c (k + 1 + j)‖ := by
      intro j
      induction j with
      | zero => simpa using hlt
      | succ j ih =>
        have hg := hgrow (k + 1 + j) (by omega) (by
          rw [show k + 1 + (j : ℤ) - 1 = k + j by ring]; exact ih.2)
        push_cast
        rw [show k + 1 + ((j : ℤ) + 1) = k + 1 + j + 1 by ring,
          show k + ((j : ℤ) + 1) = k + 1 + j by ring]
        constructor <;> nlinarith [norm_nonneg (c (k + 1 + j))]
    have ht : Tendsto (fun j : ℕ => ‖c (k + 1 + j)‖) atTop (𝓝 0) := by
      have h0 := hs.tendsto_cofinite_zero
      have hinj : Tendsto (fun j : ℕ => k + 1 + (j : ℤ)) atTop cofinite :=
        (Function.Injective.tendsto_cofinite (fun i j h => by simpa using h)).mono_left
          Nat.cofinite_eq_atTop.symm.le
      exact h0.comp hinj
    have : ‖c (k + 1)‖ ≤ 0 := ge_of_tendsto ht (Eventually.of_forall fun j => (hind j).1)
    linarith
  have hnz : ∀ k : ℤ, (M : ℤ) ≤ k → c k ≠ 0 := by
    intro k0 hk0 hc0
    have hfwd : ∀ j : ℕ, c (k0 + j) = 0 := by
      intro j
      induction j with
      | zero => simpa using hc0
      | succ j ih =>
        have := hmono (k0 + j) (by omega)
        rw [ih, norm_zero] at this
        push_cast
        rw [← add_assoc]
        exact norm_le_zero_iff.mp this
    have hbwd : ∀ j : ℕ, c (k0 + 1 - j) = 0 ∧ c (k0 - j) = 0 := by
      intro j
      induction j with
      | zero => exact ⟨by simpa using hfwd 1, by simpa using hc0⟩
      | succ j ih =>
        refine ⟨by push_cast; rw [show k0 + 1 - ((j : ℤ) + 1) = k0 - j by ring]; exact ih.2, ?_⟩
        have := hrec (k0 - j)
        rw [show k0 - (j : ℤ) + 1 = k0 + 1 - j by ring, ih.1, ih.2] at this
        push_cast
        rw [show k0 - ((j : ℤ) + 1) = k0 - j - 1 by ring]
        simpa [hq0] using this
    apply hne
    funext m
    rcases le_or_gt k0 m with h | h
    · have := hfwd (m - k0).toNat
      rwa [Int.toNat_of_nonneg (by omega), add_sub_cancel] at this
    · have := (hbwd (k0 - m).toNat).2
      rwa [Int.toNat_of_nonneg (by omega), sub_sub_cancel] at this
  set C1 : ℝ := ‖a‖ + ‖ν‖ ^ 2 + 4 * ‖ν‖ + ‖q‖
  refine IsBigO.of_bound (‖q‖ * C1 / 8) ?_
  filter_upwards [eventually_ge_atTop (M + 1)] with m hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  set k : ℤ := (m : ℤ) with hkdef
  have hkM : (M : ℤ) ≤ k := by simp only [k]; omega
  have hck : c k ≠ 0 := hnz k hkM
  have hck1 : c (k - 1) ≠ 0 := hnz (k - 1) (by simp only [k]; omega)
  set r : ℂ := c (k + 1) / c k
  have hr : ‖r‖ ≤ 1 := by
    rw [norm_div]; exact div_le_one_of_le₀ (hmono k hkM) (norm_nonneg _)
  set E : ℂ := D k - q * r
  have hDk := hM k hkM
  have hkr : (k : ℝ) = m := by simp [k]
  rw [hkr] at hDk
  have hE : 2 * (m : ℝ) ^ 2 ≤ ‖E‖ := by
    have : ‖q * r‖ ≤ ‖q‖ := by
      rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hr
    have := norm_sub_norm_le (D k) (q * r)
    linarith
  have hE0 : E ≠ 0 := by
    intro h; rw [h, norm_zero] at hE; nlinarith
  have hqr' : c k * (q * r) = q * c (k + 1) := by
    simp only [r]; field_simp
  have hid : c k * E = q * c (k - 1) := by
    simp only [E]; rw [mul_sub, hqr']
    simp only [D]
    linear_combination -(hrec k)
  have hratio : c k / c (k - 1) = q / E := by
    rw [div_eq_div_iff hck1 hE0]; linear_combination hid
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hcast : ((k : ℤ) : ℂ) = (m : ℂ) := by simp [k]
  have hcast' : ((k - 1 : ℤ) : ℂ) = (m : ℂ) - 1 := by push_cast [k]; ring
  show ‖c k / c (k - 1) + q / (4 * (m : ℂ) ^ 2)‖ ≤ _
  rw [hratio]
  have hnum : ‖4 * (m : ℂ) ^ 2 + E‖ ≤ C1 * m := by
    have he : 4 * (m : ℂ) ^ 2 + E = (a - ν ^ 2) - 4 * ν * m - q * r := by
      simp only [E, D, hcast]; ring
    rw [he]
    have h1 : ‖(a - ν ^ 2) - 4 * ν * m - q * r‖ ≤ ‖a‖ + ‖ν‖ ^ 2 + 4 * ‖ν‖ * m + ‖q‖ := by
      refine (norm_sub_le _ _).trans ?_
      have hqr : ‖q * r‖ ≤ ‖q‖ := by
        rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hr
      have h2 : ‖(a - ν ^ 2) - 4 * ν * m‖ ≤ ‖a‖ + ‖ν‖ ^ 2 + 4 * ‖ν‖ * m := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_natCast]
        have := norm_sub_le a (ν ^ 2)
        rw [norm_pow] at this
        norm_num
        linarith
      linarith
    refine h1.trans ?_
    simp only [C1]
    nlinarith [norm_nonneg a, norm_nonneg ν, norm_nonneg q, sq_nonneg ‖ν‖]
  have hsum : q / E + q / (4 * (m : ℂ) ^ 2) =
      q * (4 * (m : ℂ) ^ 2 + E) / (4 * (m : ℂ) ^ 2 * E) := by
    field_simp
  rw [hsum, norm_div, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_natCast,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ((m : ℝ) ^ 3)⁻¹)]
  have hden : 8 * (m : ℝ) ^ 4 ≤ ‖(4 : ℂ)‖ * (m : ℝ) ^ 2 * ‖E‖ := by
    rw [show ‖(4 : ℂ)‖ = 4 by norm_num]; nlinarith [sq_nonneg (m : ℝ)]
  have hpos : 0 < 8 * (m : ℝ) ^ 4 := by positivity
  rw [div_le_iff₀ (by linarith)]
  calc ‖q‖ * ‖4 * (m : ℂ) ^ 2 + E‖ ≤ ‖q‖ * (C1 * m) := by gcongr
    _ = ‖q‖ * C1 / 8 * ((m : ℝ) ^ 3)⁻¹ * (8 * (m : ℝ) ^ 4) := by field_simp
    _ ≤ ‖q‖ * C1 / 8 * ((m : ℝ) ^ 3)⁻¹ * (‖(4 : ℂ)‖ * (m : ℝ) ^ 2 * ‖E‖) := by
        have : 0 ≤ ‖q‖ * C1 / 8 * ((m : ℝ) ^ 3)⁻¹ := by positivity
        exact mul_le_mul_of_nonneg_left hden this

/-- **Rate of convergence** (DLMF 28.14.6): for `q ≠ 0`,
`c^ν_{2m}(q) / c^ν_{2m∓2}(q) = (-q/(4m²)) (1 + O(1/m))` as `m → ±∞`, i.e. the difference
`c_{2m}/c_{2m∓2} + q/(4m²)` is `O(m⁻³)`. -/
@[dlmf 28.14.E6]
theorem mathieuMeCoeff_ratio (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {q : ℂ} (hq0 : q ≠ 0)
    (hq : MathieuNormalSegment ν q) :
    (fun m : ℕ => mathieuMeCoeff ν q m / mathieuMeCoeff ν q (m - 1) + q / (4 * (m : ℂ) ^ 2))
        =O[atTop] (fun m : ℕ => ((m : ℝ) ^ 3)⁻¹) ∧
      (fun m : ℕ => mathieuMeCoeff ν q (-m) / mathieuMeCoeff ν q (-m + 1) + q / (4 * (m : ℂ) ^ 2))
        =O[atTop] (fun m : ℕ => ((m : ℝ) ^ 3)⁻¹) := by
  have hd := m28b_isMeCoeffSeq_data hq
  set c := (mathieuLambdaData ν q).2
  have hne : c ≠ 0 := by
    intro h
    have := hd.2.2
    rw [h] at this
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
    exact one_ne_zero (hasSum_zero.unique this).symm
  simp only [mathieuMeCoeff_of_not_int hν]
  refine ⟨p1b_ratio_tail hq0 hd.1 hd.2.1 hne, ?_⟩
  have hrec' : ∀ m : ℤ, q * c (-(m + 1)) - ((mathieuLambdaData ν q).1 - (-ν + 2 * m) ^ 2) *
      c (-m) + q * c (-(m - 1)) = 0 := by
    intro m
    have := hd.1 (-m)
    rw [show -m + 1 = -(m - 1) by ring, show -m - 1 = -(m + 1) by ring] at this
    push_cast at this ⊢
    linear_combination this
  have hs' : Summable (fun m : ℤ => ‖c (-m)‖) := (Equiv.neg ℤ).summable_iff.mpr hd.2.1
  have hne' : (fun m => c (-m)) ≠ 0 := by
    intro h; apply hne; funext m; simpa using congrFun h (-m)
  have := p1b_ratio_tail (c := fun m => c (-m)) hq0 hrec' hs' hne'
  refine this.congr_left fun m => ?_
  rw [show -((m : ℤ) - 1) = -(m : ℤ) + 1 by ring]

/-- **Change of sign of `ν` and `m`** (DLMF 28.14.7): `c^{-ν}_{-2m}(q) = c^ν_{2m}(q)` for
`ν ∉ ℤ`. -/
@[dlmf 28.14.E7]
theorem mathieuMeCoeff_neg (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (q : ℂ) (m : ℤ) :
    mathieuMeCoeff (-ν) q (-m) = mathieuMeCoeff ν q m := by
  rw [mathieuMeCoeff_of_not_int (m28b_not_int_neg hν), mathieuMeCoeff_of_not_int hν,
    m28b_data_neg_nu]
  simp

/-- **Change of sign of `q`** (DLMF 28.14.8): `c^ν_{2m}(-q) = (-1)^m c^ν_{2m}(q)` for
`ν ∉ ℤ`. -/
@[dlmf 28.14.E8]
theorem mathieuMeCoeff_neg_q (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (q : ℂ) (m : ℤ) :
    mathieuMeCoeff ν (-q) m = (-1 : ℂ) ^ m * mathieuMeCoeff ν q m := by
  rw [mathieuMeCoeff_of_not_int hν, mathieuMeCoeff_of_not_int hν, m28b_data_neg_q]

/-- **Values at `q = 0`** (DLMF 28.14.9): `c^ν_0(0) = 1` and `c^ν_{2m}(0) = 0` for `m ≠ 0`
(`ν ∉ ℤ`). -/
@[dlmf 28.14.E9]
theorem mathieuMeCoeff_zero (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) :
    mathieuMeCoeff ν 0 0 = 1 ∧ ∀ m : ℤ, m ≠ 0 → mathieuMeCoeff ν 0 m = 0 := by
  simp only [mathieuMeCoeff_of_not_int hν, m28b_data_zero hν]
  exact ⟨by simp, fun m hm => by simp [hm]⟩

/-- **Small-`q` behaviour of the coefficients** (DLMF 28.14.10): for fixed `m ≥ 1` and `ν ∉ ℤ`,
as `q → 0`,
`c^ν_{2m}(q) = ((-1)^m q^m Γ(ν+1) / (m! 2^{2m} Γ(ν+m+1)) + O(q^{m+2})) c^ν_0(q)`. -/
@[dlmf 28.14.E10]
theorem mathieuMeCoeff_isBigO_zero (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {m : ℕ} (hm : 1 ≤ m) :
    (fun q : ℂ => mathieuMeCoeff ν q m - (-1) ^ m * q ^ m * Complex.Gamma (ν + 1) /
        (m.factorial * 2 ^ (2 * m) * Complex.Gamma (ν + m + 1)) * mathieuMeCoeff ν q 0)
      =O[𝓝 0] (fun q : ℂ => q ^ (m + 2)) := by
  sorry

end DLMF.Mathieu
