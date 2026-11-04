/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Basic.Jacobi
public import DLMF.Elementary.Basic.Gudermannian
public import DLMF.Elementary.Trigonometric.ValuesAndIntegrals

/-!
# Expansions of the Jacobi amplitude near `k = 0` and `k = 1`

Quantitative error bounds behind DLMF 22.16.7 and 22.16.8 for the real amplitude
`am(x, k)`, the inverse of `φ ↦ F(φ|k²)`. Both are proved by expanding the integrand of
`F(φ|m)` (in `m` near `0`, respectively in `m' = 1 - m` near `0` for `|φ|` bounded away from
`π/2`) and inverting: near `k = 1` the comparison function is `gd⁻¹`, and the inversion uses
the second-order Taylor bound of the Gudermannian.

## Main results

* `Real.abs_jacobiAmOfParameter_sub_le_of_small_param`:
  `|am(x|m) - (x - (m/4)(x - sin x cos x))| ≤ 8|x|m²` for `0 ≤ m ≤ 1/4`.
* `Real.exists_abs_jacobiAmOfParameter_sub_le_comodulus`: for fixed `x` there are `φ₀ < π/2` and `K`
  with `|am(x,k) - (gd x - k'²(x - sinh x cosh x) sech x/4)| ≤ K k'⁴` whenever `0 < k < 1`
  and `|am(x,k)| ≤ φ₀`.
-/

@[expose] public section

open Real DLMF.Elliptic

noncomputable section

namespace DLMF.JacobiElliptic

/-- `1 + u/2 ≤ (1 - u)^{-1/2} ≤ 1 + u/2 + 3u²` for `0 ≤ u ≤ 1/2`. -/
private lemma abs_rpow_neg_half_sub_le {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    |(1 - u) ^ (-(1 / 2) : ℝ) - 1 - u / 2| ≤ 3 * u ^ 2 := by
  have hpos : 0 < 1 - u := by linarith
  set r := (1 - u) ^ (-(1 / 2) : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hpos _
  have hr2 : r ^ 2 * (1 - u) = 1 := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
    rw [Real.rpow_neg_one, inv_mul_cancel₀ hpos.ne']
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (r - 1 - u / 2), mul_pos hr0 hpos]
  · nlinarith [sq_nonneg (r - 1 - u / 2), mul_pos hr0 hpos, sq_nonneg u, mul_nonneg hu0 hu0,
      mul_nonneg (mul_nonneg hu0 hu0) hu0]

/-- `|F(φ|m) - φ - (m/4)(φ - sin φ cos φ)| ≤ 3m²|φ|` for `0 ≤ m ≤ 1/2`. -/
private lemma abs_incompleteEllipticFOfParameter_sub_le {m : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ 1 / 2) (φ : ℝ) :
    |Real.incompleteEllipticFOfParameter φ m - φ - m / 4 * (φ - sin φ * cos φ)| ≤ 3 *
        m ^ 2 * |φ| := by
  have hpos : ∀ θ, 0 < 1 - m * sin θ ^ 2 := fun θ => by
    nlinarith [sin_sq_le_one θ, sq_nonneg (sin θ)]
  have hc : Continuous fun θ => (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ) :=
    (by fun_prop : Continuous fun θ => 1 - m * sin θ ^ 2).rpow_const
      fun θ => Or.inl (hpos θ).ne'
  have hint : ∫ θ in (0 : ℝ)..φ, ((1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ) - 1 - m / 2 * sin θ ^ 2) =
      Real.incompleteEllipticFOfParameter φ m - φ - m / 4 * (φ - sin φ * cos φ) := by
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, integral_sin_sq]
    · simp [Real.incompleteEllipticFOfParameter]; ring
    · exact hc.intervalIntegrable _ _
    · exact intervalIntegrable_const
    · exact (hc.sub continuous_const).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun θ => m / 2 * sin θ ^ 2).intervalIntegrable _ _
  rw [← hint, ← Real.norm_eq_abs]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := φ) (C := 3 * m ^ 2)
    (f := fun θ => (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ) - 1 - m / 2 * sin θ ^ 2) (fun θ _ => by
      have hs0 := sq_nonneg (sin θ)
      have hs1 := sin_sq_le_one θ
      have h := abs_rpow_neg_half_sub_le (u := m * sin θ ^ 2) (mul_nonneg hm0 hs0)
        (by nlinarith)
      rw [Real.norm_eq_abs]
      calc _ = |(1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ) - 1 - m * sin θ ^ 2 / 2| := by ring_nf
        _ ≤ 3 * (m * sin θ ^ 2) ^ 2 := h
        _ ≤ 3 * m ^ 2 := by
          rw [mul_pow]
          have : (sin θ ^ 2) ^ 2 ≤ 1 := pow_le_one₀ hs0 hs1
          nlinarith [sq_nonneg m])
  simpa using this

/-- `|φ - sin φ cos φ| ≤ 2|φ|`. -/
private lemma abs_sub_sin_mul_cos_le (φ : ℝ) : |φ - sin φ * cos φ| ≤ 2 * |φ| := by
  have h1 : |sin φ| ≤ |φ| := by simpa using abs_sin_sub_sin_le φ 0
  have h2 : |sin φ * cos φ| ≤ |φ| := by
    rw [abs_mul]
    nlinarith [abs_cos_le_one φ, abs_nonneg (sin φ), abs_nonneg (cos φ)]
  calc _ ≤ |φ| + |sin φ * cos φ| := abs_sub _ _
    _ ≤ 2 * |φ| := by linarith

/-- `φ ↦ φ - sin φ cos φ` is `2`-Lipschitz. -/
private lemma abs_sub_sin_mul_cos_sub_le (a b : ℝ) :
    |(a - sin a * cos a) - (b - sin b * cos b)| ≤ 2 * |a - b| := by
  have e : ∀ x : ℝ, sin x * cos x = sin (2 * x) / 2 := fun x => by rw [sin_two_mul]; ring
  have h := abs_sin_sub_sin_le (2 * a) (2 * b)
  rw [e, e, show a - sin (2 * a) / 2 - (b - sin (2 * b) / 2) =
    (a - b) - (sin (2 * a) - sin (2 * b)) / 2 by ring]
  calc _ ≤ |a - b| + |(sin (2 * a) - sin (2 * b)) / 2| := abs_sub _ _
    _ ≤ 2 * |a - b| := by
      rw [abs_div, abs_two]
      rw [show 2 * a - 2 * b = 2 * (a - b) by ring, abs_mul, abs_two] at h
      linarith

/-- Quantitative form of DLMF 22.16.7: `|am(x|m) - (x - (m/4)(x - sin x cos x))| ≤ 8|x|m²`
for `0 ≤ m ≤ 1/4` (parameter `m = k²`). -/
theorem Real.abs_jacobiAmOfParameter_sub_le_of_small_param {m : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ 1 / 4) (x : ℝ) :
    |Real.jacobiAmOfParameter x m - (x - m / 4 * (x - sin x * cos x))| ≤ 8 * |x| * m ^ 2 := by
  set φ := Real.jacobiAmOfParameter x m
  have hF : Real.incompleteEllipticFOfParameter φ m = x :=
      Real.incompleteEllipticFOfParameter_jacobiAmOfParameter (by linarith) x
  have hE := abs_incompleteEllipticFOfParameter_sub_le hm0 (by linarith) φ
  rw [hF] at hE
  have hg := abs_sub_sin_mul_cos_le φ
  have hφ : |φ| ≤ 2 * |x| := by
    have h1 : |x - φ| ≤ m / 4 * |φ - sin φ * cos φ| + 3 * m ^ 2 * |φ| := by
      have := abs_add_le (x - φ - m / 4 * (φ - sin φ * cos φ)) (m / 4 * (φ - sin φ * cos φ))
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ m / 4)] at this
      have e : x - φ - m / 4 * (φ - sin φ * cos φ) + m / 4 * (φ - sin φ * cos φ) = x - φ := by
        ring
      rw [e] at this; linarith
    have h2 : |φ| ≤ |x| + |x - φ| := by
      have := abs_sub_abs_le_abs_sub φ x
      rw [abs_sub_comm] at this; linarith
    have a1 := mul_le_mul_of_nonneg_left hg (by linarith : 0 ≤ m / 4)
    have a2 := mul_le_mul_of_nonneg_right hm (abs_nonneg φ)
    have a3 : m ^ 2 * |φ| ≤ 1 / 16 * |φ| :=
      mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg φ)
    linarith [abs_nonneg x]
  have hd : |φ - x| ≤ 3 * m * |x| := by
    have h1 : |x - φ| ≤ m / 4 * |φ - sin φ * cos φ| + 3 * m ^ 2 * |φ| := by
      have := abs_add_le (x - φ - m / 4 * (φ - sin φ * cos φ)) (m / 4 * (φ - sin φ * cos φ))
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ m / 4)] at this
      have e : x - φ - m / 4 * (φ - sin φ * cos φ) + m / 4 * (φ - sin φ * cos φ) = x - φ := by
        ring
      rw [e] at this; linarith
    rw [abs_sub_comm]
    have a1 := mul_le_mul_of_nonneg_left hg (by linarith : 0 ≤ m / 4)
    have a2 := mul_le_mul_of_nonneg_left hφ (by linarith : 0 ≤ m / 2)
    have a3 := mul_le_mul_of_nonneg_left hφ (by positivity : 0 ≤ 3 * m ^ 2)
    have a4 : m ^ 2 * |x| ≤ m / 4 * |x| :=
      mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg x)
    nlinarith [mul_nonneg hm0 (abs_nonneg x)]
  have hL := abs_sub_sin_mul_cos_sub_le φ x
  have e : φ - (x - m / 4 * (x - sin x * cos x)) =
      -(m / 4 * ((φ - sin φ * cos φ) - (x - sin x * cos x))) -
        (x - φ - m / 4 * (φ - sin φ * cos φ)) := by ring
  rw [e]
  calc _ ≤ |m / 4 * ((φ - sin φ * cos φ) - (x - sin x * cos x))| +
        |x - φ - m / 4 * (φ - sin φ * cos φ)| := by
          refine (abs_sub _ _).trans ?_; rw [abs_neg]
    _ ≤ m / 4 * (2 * (3 * m * |x|)) + 3 * m ^ 2 * (2 * |x|) := by
          rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ m / 4)]
          gcongr
          · exact hL.trans (by gcongr)
          · exact hE.trans (by gcongr)
    _ ≤ 8 * |x| * m ^ 2 := by nlinarith [abs_nonneg x]

/-- `sech` is `1`-Lipschitz. -/
private lemma abs_inv_cosh_sub_le (s t : ℝ) : |(cosh t)⁻¹ - (cosh s)⁻¹| ≤ |t - s| := by
  have hd : ∀ y ∈ (Set.univ : Set ℝ), HasDerivWithinAt (fun y => (cosh y)⁻¹)
      (-(sinh y) / cosh y ^ 2) Set.univ y := fun y _ => by
    have := (hasDerivAt_cosh y).inv (cosh_pos y).ne'
    convert this.hasDerivWithinAt using 1
  have hb : ∀ y ∈ (Set.univ : Set ℝ), ‖-(sinh y) / cosh y ^ 2‖ ≤ 1 := fun y _ => by
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (by positivity : 0 < cosh y ^ 2),
      div_le_one (by positivity)]
    have h1 : |sinh y| ≤ cosh y := by
      rw [abs_le]; constructor <;> nlinarith [cosh_sq y, cosh_pos y, sinh_sq y]
    nlinarith [one_le_cosh y]
  have := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (Set.mem_univ s)
    (Set.mem_univ t)
  simpa [Real.norm_eq_abs] using this

open DLMF.Elementary in
/-- Second-order Taylor bound for `gd`: `|gd(x+δ) - gd x - δ sech x| ≤ δ²`, and
`|gd(x+δ) - gd x| ≤ |δ|`. -/
private lemma abs_gudermannian_add_sub_le (x δ : ℝ) :
    |gudermannian (x + δ) - gudermannian x - δ * (cosh x)⁻¹| ≤ δ ^ 2 ∧
      |gudermannian (x + δ) - gudermannian x| ≤ |δ| := by
  have hc : Continuous fun t => (cosh t)⁻¹ := continuous_cosh.inv₀ fun t => (cosh_pos t).ne'
  have hsub : gudermannian (x + δ) - gudermannian x = ∫ t in x..x + δ, (cosh t)⁻¹ :=
    intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)
  constructor
  · have e : gudermannian (x + δ) - gudermannian x - δ * (cosh x)⁻¹ =
        ∫ t in x..x + δ, ((cosh t)⁻¹ - (cosh x)⁻¹) := by
      rw [hsub, intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
        intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [e, ← Real.norm_eq_abs]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := x + δ)
      (C := |δ|) (f := fun t => (cosh t)⁻¹ - (cosh x)⁻¹) (fun t ht => by
        rw [Real.norm_eq_abs]
        refine (abs_inv_cosh_sub_le x t).trans ?_
        rcases Set.mem_uIoc.mp ht with h | h
        · rw [abs_le]; constructor <;> cases abs_cases δ <;> linarith
        · rw [abs_le]; constructor <;> cases abs_cases δ <;> linarith)
    rw [show x + δ - x = δ by ring] at this
    rw [← sq_abs, sq]; exact this
  · rw [hsub, ← Real.norm_eq_abs]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := x + δ)
      (C := 1) (f := fun t => (cosh t)⁻¹) (fun t _ => by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (cosh_pos t))]
        exact inv_le_one_of_one_le₀ (one_le_cosh t))
    rw [show x + δ - x = δ by ring, one_mul] at this
    exact this

/-- `1 - u/2 ≤ (1 + u)^{-1/2} ≤ 1 - u/2 + u²` for `u ≥ 0`, in the form `ρ²(1 + u) = 1`. -/
private lemma abs_sub_one_add_half_le {ρ u : ℝ} (hρ : 0 < ρ) (hu : 0 ≤ u)
    (h : ρ ^ 2 * (1 + u) = 1) : |ρ - 1 + u / 2| ≤ u ^ 2 := by
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (ρ - 1 + u / 2), sq_nonneg u, mul_nonneg hu (sq_nonneg u),
      mul_pos hρ hρ]
  · nlinarith [sq_nonneg (ρ - 1 + u / 2), sq_nonneg u, mul_nonneg hu (sq_nonneg u),
      mul_pos hρ hρ, mul_nonneg (mul_nonneg hu hu) (mul_nonneg hu hu)]

/-- Pointwise expansion of the integrand of `F(φ|1 - m')` in `m'`. -/
private lemma abs_integrand_comodulus_le {m' c₀ θ : ℝ} (hm0 : 0 ≤ m') (hc₀ : 0 < c₀)
    (hc : c₀ ≤ cos θ) :
    |(1 - (1 - m') * sin θ ^ 2) ^ (-(1 / 2) : ℝ) - (cos θ)⁻¹ +
        m' / 2 * (cos θ)⁻¹ * (sin θ / cos θ) ^ 2| ≤ m' ^ 2 / c₀ ^ 5 := by
  set c := cos θ
  set s := sin θ
  have hc0 : 0 < c := hc₀.trans_le hc
  have hsc : s ^ 2 + c ^ 2 = 1 := sin_sq_add_cos_sq θ
  have hw : 1 - (1 - m') * s ^ 2 = c ^ 2 + m' * s ^ 2 := by linear_combination -hsc
  have hwpos : 0 < c ^ 2 + m' * s ^ 2 := by positivity
  set r := (1 - (1 - m') * s ^ 2) ^ (-(1 / 2) : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (hw ▸ hwpos) _
  have hr2 : r ^ 2 * (c ^ 2 + m' * s ^ 2) = 1 := by
    rw [← hw, hr, ← Real.rpow_natCast, ← Real.rpow_mul (hw ▸ hwpos).le]
    norm_num
    rw [Real.rpow_neg_one, inv_mul_cancel₀ (hw ▸ hwpos).ne']
  set u := m' * s ^ 2 / c ^ 2
  have hu : 0 ≤ u := by positivity
  have hρ : (r * c) ^ 2 * (1 + u) = 1 := by
    have : (r * c) ^ 2 * (1 + u) = r ^ 2 * (c ^ 2 + m' * s ^ 2) := by
      simp only [u]; field_simp
    rw [this, hr2]
  have hb := abs_sub_one_add_half_le (mul_pos hr0 hc0) hu hρ
  have e : r - c⁻¹ + m' / 2 * c⁻¹ * (s / c) ^ 2 = (r * c - 1 + u / 2) / c := by
    simp only [u]; field_simp
  rw [e, abs_div, abs_of_pos hc0, div_le_div_iff₀ hc0 (by positivity)]
  have hs4 : (s ^ 2) ^ 2 ≤ 1 := pow_le_one₀ (sq_nonneg s) (by nlinarith [sq_nonneg c])
  have hu2 : u ^ 2 * c ^ 4 = m' ^ 2 * (s ^ 2) ^ 2 := by simp only [u]; field_simp
  have hc5 : c₀ ^ 5 ≤ c ^ 5 := pow_le_pow_left₀ hc₀.le hc 5
  calc |r * c - 1 + u / 2| * c₀ ^ 5 ≤ u ^ 2 * c ^ 5 := by
        gcongr
    _ = m' ^ 2 * (s ^ 2) ^ 2 * c := by rw [show u ^ 2 * c ^ 5 = u ^ 2 * c ^ 4 * c by ring, hu2]
    _ ≤ m' ^ 2 * c := by
        have := sq_nonneg m'
        nlinarith [mul_nonneg this hc0.le]

/-- `cos θ ≥ cos φ₀` for `|θ| ≤ φ₀ ≤ π`. -/
private lemma cos_le_cos_of_abs_le {θ φ₀ : ℝ} (h : |θ| ≤ φ₀) (hφ₀ : φ₀ ≤ π) :
    cos φ₀ ≤ cos θ := by
  rw [← Real.cos_abs θ]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) hφ₀ h

open DLMF.Elementary in
/-- `F(φ|1 - m') = gd⁻¹φ - (m'/4)(sin φ/cos² φ - gd⁻¹φ) + O(m'²)` for `|φ| ≤ φ₀ < π/2`. -/
private lemma abs_incompleteEllipticFOfParameter_comodulus_sub_le {m' φ₀ φ : ℝ} (hm0 : 0 ≤ m')
    (hφ₀ : φ₀ < π / 2) (hφ : |φ| ≤ φ₀) :
    |Real.incompleteEllipticFOfParameter φ (1 - m') - (inverseGudermannian φ -
        m' / 4 * (sin φ / cos φ ^ 2 - inverseGudermannian φ))| ≤ m' ^ 2 / cos φ₀ ^ 5 * |φ| := by
  have hφ₀0 : 0 ≤ φ₀ := (abs_nonneg φ).trans hφ
  have hc₀ : 0 < cos φ₀ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hφ₀⟩
  have hθ : ∀ θ ∈ Set.uIcc 0 φ, |θ| ≤ φ₀ := fun θ hθ => by
    refine le_trans ?_ hφ
    rcases Set.mem_uIcc.mp hθ with h | h
    · rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]; exact h.2
    · rw [abs_of_nonpos h.2, abs_of_nonpos (h.1.trans h.2)]; linarith [h.1]
  have hcos : ∀ θ ∈ Set.uIcc 0 φ, cos φ₀ ≤ cos θ := fun θ hθ' =>
    cos_le_cos_of_abs_le (hθ θ hθ') (by linarith [pi_pos])
  have hcos0 : ∀ θ ∈ Set.uIcc 0 φ, cos θ ≠ 0 := fun θ hθ' => (hc₀.trans_le (hcos θ hθ')).ne'
  have hw : ∀ θ ∈ Set.uIcc 0 φ, 1 - (1 - m') * sin θ ^ 2 ≠ 0 := fun θ hθ' => by
    have := hcos0 θ hθ'
    have h2 : 0 < cos θ ^ 2 := by positivity
    nlinarith [sin_sq_add_cos_sq θ, sq_nonneg (sin θ)]
  have csec : ContinuousOn (fun θ => (cos θ)⁻¹) (Set.uIcc 0 φ) :=
    continuous_cos.continuousOn.inv₀ hcos0
  have ctan : ContinuousOn (fun θ => (cos θ)⁻¹ * (sin θ / cos θ) ^ 2) (Set.uIcc 0 φ) :=
    csec.mul ((continuous_sin.continuousOn.div continuous_cos.continuousOn hcos0).pow 2)
  have cr : ContinuousOn (fun θ => (1 - (1 - m') * sin θ ^ 2) ^ (-(1 / 2) : ℝ))
      (Set.uIcc 0 φ) :=
    (by fun_prop : Continuous fun θ => 1 - (1 - m') * sin θ ^ 2).continuousOn.rpow_const
      fun θ hθ' => Or.inl (hw θ hθ')
  have hftc : ∫ θ in (0 : ℝ)..φ, (2 * ((cos θ)⁻¹ * (sin θ / cos θ) ^ 2) + (cos θ)⁻¹) =
      sin φ / cos φ ^ 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun θ => sin θ / cos θ ^ 2)]
    · simp
    · intro θ hθ'
      have hc := hcos0 θ hθ'
      have := (hasDerivAt_sin θ).div ((hasDerivAt_cos θ).pow 2) (pow_ne_zero 2 hc)
      convert this using 1
      simp only [Pi.pow_apply]
      field_simp
      ring
    · exact ((continuousOn_const.mul ctan).add csec).intervalIntegrable
  have hsec : ∫ θ in (0 : ℝ)..φ, (cos θ)⁻¹ = inverseGudermannian φ := rfl
  have i2 : IntervalIntegrable (fun θ => 2 * ((cos θ)⁻¹ * (sin θ / cos θ) ^ 2))
      MeasureTheory.volume 0 φ := (continuousOn_const.mul ctan).intervalIntegrable
  have im : IntervalIntegrable (fun θ => m' / 2 * ((cos θ)⁻¹ * (sin θ / cos θ) ^ 2))
      MeasureTheory.volume 0 φ := (continuousOn_const.mul ctan).intervalIntegrable
  have irs : IntervalIntegrable
      (fun θ => (1 - (1 - m') * sin θ ^ 2) ^ (-(1 / 2) : ℝ) - (cos θ)⁻¹)
      MeasureTheory.volume 0 φ := (cr.sub csec).intervalIntegrable
  have htan : ∫ θ in (0 : ℝ)..φ, (cos θ)⁻¹ * (sin θ / cos θ) ^ 2 =
      (sin φ / cos φ ^ 2 - inverseGudermannian φ) / 2 := by
    rw [intervalIntegral.integral_add i2 csec.intervalIntegrable,
      intervalIntegral.integral_const_mul, hsec] at hftc
    linarith
  have hint : ∫ θ in (0 : ℝ)..φ, ((1 - (1 - m') * sin θ ^ 2) ^ (-(1 / 2) : ℝ) - (cos θ)⁻¹ +
      m' / 2 * ((cos θ)⁻¹ * (sin θ / cos θ) ^ 2)) =
      Real.incompleteEllipticFOfParameter φ (1 - m') - (inverseGudermannian φ -
        m' / 4 * (sin φ / cos φ ^ 2 - inverseGudermannian φ)) := by
    rw [intervalIntegral.integral_add irs im,
      intervalIntegral.integral_sub cr.intervalIntegrable csec.intervalIntegrable,
      intervalIntegral.integral_const_mul, htan, hsec]
    simp only [Real.incompleteEllipticFOfParameter]
    ring
  rw [← hint, ← Real.norm_eq_abs]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := φ)
    (C := m' ^ 2 / cos φ₀ ^ 5) (f := fun θ => (1 - (1 - m') * sin θ ^ 2) ^ (-(1 / 2) : ℝ) -
      (cos θ)⁻¹ + m' / 2 * ((cos θ)⁻¹ * (sin θ / cos θ) ^ 2)) (fun θ hθ' => by
      rw [Real.norm_eq_abs, ← mul_assoc]
      exact abs_integrand_comodulus_le hm0 hc₀ (hcos θ (Set.uIoc_subset_uIcc hθ')))
  simpa using this

open DLMF.Elementary in
/-- `h(φ) = sin φ/cos² φ - gd⁻¹φ` is `2/cos³ φ₀`-Lipschitz on `[-φ₀, φ₀]`, `φ₀ < π/2`. -/
private lemma abs_comodulusAux_sub_le {φ₀ a b : ℝ} (hφ₀ : φ₀ < π / 2) (ha : |a| ≤ φ₀)
    (hb : |b| ≤ φ₀) :
    |(sin a / cos a ^ 2 - inverseGudermannian a) - (sin b / cos b ^ 2 - inverseGudermannian b)|
      ≤ 2 / cos φ₀ ^ 3 * |a - b| := by
  have hφ₀0 : 0 ≤ φ₀ := (abs_nonneg a).trans ha
  have hc₀ : 0 < cos φ₀ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hφ₀⟩
  set s := Set.Icc (-φ₀) φ₀
  have hmem : ∀ y ∈ s, |y| ≤ φ₀ := fun y hy => abs_le.mpr hy
  have hd : ∀ y ∈ s, HasDerivWithinAt (fun y => sin y / cos y ^ 2 - inverseGudermannian y)
      (2 * ((cos y)⁻¹ * (sin y / cos y) ^ 2)) s y := fun y hy => by
    have hy' : |y| < π / 2 := (hmem y hy).trans_lt hφ₀
    have hc : cos y ≠ 0 := (cos_pos_of_mem_Ioo (abs_lt.mp hy')).ne'
    have h1 := (hasDerivAt_sin y).div ((hasDerivAt_cos y).pow 2) (pow_ne_zero 2 hc)
    have h2 := hasDerivAt_inverse_gudermannian hy'
    refine (HasDerivAt.hasDerivWithinAt ?_)
    convert h1.sub h2 using 1
    simp only [Pi.pow_apply]
    field_simp
    ring
  have hbd : ∀ y ∈ s, ‖2 * ((cos y)⁻¹ * (sin y / cos y) ^ 2)‖ ≤ 2 / cos φ₀ ^ 3 := fun y hy => by
    have hcy : cos φ₀ ≤ cos y := cos_le_cos_of_abs_le (hmem y hy) (by linarith [pi_pos])
    have hc0 : 0 < cos y := hc₀.trans_le hcy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_pow,
      show 2 * ((cos y)⁻¹ * (sin y ^ 2 / cos y ^ 2)) = 2 * sin y ^ 2 / cos y ^ 3 by
        field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : cos φ₀ ^ 3 ≤ cos y ^ 3 := pow_le_pow_left₀ hc₀.le hcy 3
    nlinarith [sin_sq_le_one y, sq_nonneg (sin y), pow_pos hc₀ 3]
  have := (convex_Icc (-φ₀) φ₀).norm_image_sub_le_of_norm_hasDerivWithin_le hd hbd
    (abs_le.mp hb) (abs_le.mp ha)
  simpa [Real.norm_eq_abs] using this

open DLMF.Elementary in
/-- `h(gd x) = sinh x cosh x - x`. -/
private lemma comodulusAux_gudermannian (x : ℝ) :
    sin (gudermannian x) / cos (gudermannian x) ^ 2 -
        inverseGudermannian (gudermannian x) = sinh x * cosh x - x := by
  have hg := (gudermannian_elementary x).2.2
  have hy : |gudermannian x| < π / 2 := by
    rw [hg]; exact abs_lt.mpr ⟨neg_pi_div_two_lt_arctan _, arctan_lt_pi_div_two _⟩
  rw [(gudermannian_inverse hy x).2, hg, sin_arctan, cos_arctan]
  have hs : √(1 + sinh x ^ 2) = cosh x := by
    rw [show 1 + sinh x ^ 2 = cosh x ^ 2 by rw [cosh_sq]; ring, sqrt_sq (cosh_pos x).le]
  rw [hs]
  have := (cosh_pos x).ne'
  field_simp

open DLMF.Elementary in
/-- Quantitative form of DLMF 22.16.8: for fixed `x` there are `φ₀ < π/2` with `|gd x| < φ₀`
and a constant `K` such that `|am(x,k) - (gd x - k'²(x - sinh x cosh x) sech x/4)| ≤ K k'⁴`
(`k'² = 1 - k²`) for every `0 < k < 1` with `|am(x,k)| ≤ φ₀`. -/
theorem Real.exists_abs_jacobiAmOfParameter_sub_le_comodulus (x : ℝ) :
    ∃ φ₀ : ℝ, |gudermannian x| < φ₀ ∧ φ₀ < π / 2 ∧ ∃ K : ℝ, ∀ k : ℝ, 0 < k → k < 1 →
      |Real.jacobiAmOfParameter x (k ^ 2)| ≤ φ₀ →
      |Real.jacobiAmOfParameter x (k ^ 2) - (gudermannian x -
        (1 - k ^ 2) / 4 * (x - sinh x * cosh x) / cosh x)| ≤ K * (1 - k ^ 2) ^ 2 := by
  set ψ := gudermannian x
  have hψ : |ψ| < π / 2 := by
    rw [show ψ = arctan (sinh x) from (gudermannian_elementary x).2.2]
    exact abs_lt.mpr ⟨neg_pi_div_two_lt_arctan _, arctan_lt_pi_div_two _⟩
  set φ₀ := (|ψ| + π / 2) / 2
  have hφ₀ : φ₀ < π / 2 := by simp only [φ₀]; linarith
  have hψφ₀ : |ψ| < φ₀ := by simp only [φ₀]; linarith
  have hc₀ : 0 < cos φ₀ := cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg ψ, pi_pos], hφ₀⟩
  set L := 2 / cos φ₀ ^ 3
  set C₁ := φ₀ / cos φ₀ ^ 5
  set D := L * φ₀ / 4 + C₁
  have hL : 0 ≤ L := by positivity
  have hC₁ : 0 ≤ C₁ := by have := abs_nonneg ψ; positivity
  have hD : 0 ≤ D := by have := abs_nonneg ψ; positivity
  refine ⟨φ₀, hψφ₀, hφ₀, D ^ 2 + L * D / 4 + C₁, fun k hk0 hk1 hφk => ?_⟩
  have hk : k ∈ Set.Ioo (0 : ℝ) 1 := ⟨hk0, hk1⟩
  set m' := 1 - k ^ 2
  have hm0 : 0 ≤ m' := by simp only [m']; nlinarith [hk.1, hk.2]
  have hm1 : m' ≤ 1 := by simp only [m']; nlinarith
  set φ := Real.jacobiAmOfParameter x (k ^ 2)
  have hφ : |φ| ≤ φ₀ := hφk
  have hφ' : |φ| < π / 2 := hφ.trans_lt hφ₀
  have hF : Real.incompleteEllipticFOfParameter φ (1 - m') = x := by
    rw [show 1 - m' = k ^ 2 by simp only [m']; ring]
    exact Real.incompleteEllipticFOfParameter_jacobiAmOfParameter (by nlinarith [hk.1, hk.2]) x
  set h : ℝ → ℝ := fun y => sin y / cos y ^ 2 - inverseGudermannian y
  have hE := abs_incompleteEllipticFOfParameter_comodulus_sub_le hm0 hφ₀ hφ
  rw [hF] at hE
  set E := x - (inverseGudermannian φ - m' / 4 * h φ)
  have hEb : |E| ≤ m' ^ 2 * C₁ := by
    refine hE.trans ?_
    simp only [C₁]
    rw [show m' ^ 2 * (φ₀ / cos φ₀ ^ 5) = m' ^ 2 / cos φ₀ ^ 5 * φ₀ by ring]
    gcongr
  set δ := m' / 4 * h φ - E
  have hGφ : inverseGudermannian φ = x + δ := by simp only [δ, E]; ring
  have hφgd : φ = gudermannian (x + δ) := by
    rw [← hGφ]; exact ((gudermannian_inverse hφ' 0).1).symm
  have hhφ : |h φ| ≤ L * φ₀ := by
    have := abs_comodulusAux_sub_le (b := 0) hφ₀ hφ
      (by rw [abs_zero]; exact (abs_nonneg ψ).trans hψφ₀.le)
    simp only [sub_zero] at this
    have e : h φ = (sin φ / cos φ ^ 2 - inverseGudermannian φ) -
        (sin 0 / cos 0 ^ 2 - inverseGudermannian 0) := by
      simp [h, inverseGudermannian]
    rw [e]
    exact this.trans (by gcongr)
  have hδ : |δ| ≤ m' * D := by
    simp only [δ, D]
    calc |m' / 4 * h φ - E| ≤ |m' / 4 * h φ| + |E| := abs_sub _ _
      _ ≤ m' / 4 * (L * φ₀) + m' ^ 2 * C₁ := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          gcongr
      _ ≤ m' * (L * φ₀ / 4 + C₁) := by nlinarith [mul_nonneg hm0 hC₁]
  obtain ⟨hT, hLip⟩ := abs_gudermannian_add_sub_le x δ
  rw [← hφgd] at hT hLip
  have hφψ : |φ - ψ| ≤ m' * D := hLip.trans hδ
  have hhd : |h φ - h ψ| ≤ L * (m' * D) :=
    (abs_comodulusAux_sub_le hφ₀ hφ hψφ₀.le).trans (by gcongr)
  have hhψ : h ψ = sinh x * cosh x - x := comodulusAux_gudermannian x
  have hcx : 0 < cosh x := cosh_pos x
  have hsech : |(cosh x)⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr hcx)]; exact inv_le_one_of_one_le₀ (one_le_cosh x)
  have e : φ - (ψ - m' / 4 * (x - sinh x * cosh x) / cosh x) =
      (φ - ψ - δ * (cosh x)⁻¹) + (cosh x)⁻¹ * (m' / 4 * (h φ - h ψ) - E) := by
    rw [hhψ]; simp only [δ]; field_simp; ring
  rw [e]
  calc |(φ - ψ - δ * (cosh x)⁻¹) + (cosh x)⁻¹ * (m' / 4 * (h φ - h ψ) - E)|
      ≤ |φ - ψ - δ * (cosh x)⁻¹| + |(cosh x)⁻¹| * |m' / 4 * (h φ - h ψ) - E| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ δ ^ 2 + 1 * (m' / 4 * (L * (m' * D)) + m' ^ 2 * C₁) := by
        gcongr
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ m' / 4)]
        gcongr
    _ ≤ (m' * D) ^ 2 + 1 * (m' / 4 * (L * (m' * D)) + m' ^ 2 * C₁) := by
        have := pow_le_pow_left₀ (abs_nonneg δ) hδ 2
        rw [sq_abs] at this
        gcongr
    _ = (D ^ 2 + L * D / 4 + C₁) * m' ^ 2 := by ring

end DLMF.JacobiElliptic
