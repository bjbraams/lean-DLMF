/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Complete
public import Mathlib.Analysis.SpecialFunctions.ArithmeticGeometricMean
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The arithmetic-geometric mean and Landen's transformations (Temme §12.1.2, DLMF §19.8)

Following Temme's proof of Theorem 12.1, the integral
`agmIntegral a b = ∫₀^{π/2} (a² cos²θ + b² sin²θ)^{-1/2} dθ` equals
`∫₀^∞ ((t²+a²)(t²+b²))^{-1/2} dt` (substitution `t = b tan θ`), and the substitution
`u = (t - ab/t)/2` shows that this is invariant under `(a, b) ↦ ((a+b)/2, √(ab))`. Along
Mathlib's AGM iteration `NNReal.agmSequences` the integral is therefore constant and squeezed
between `(π/2)/aₙ` and `(π/2)/bₙ`, which gives Gauss's theorem `agmIntegral a b = π/(2 M(a,b))`.
The same invariance with homogeneity gives the descending and ascending Landen
transformations of `K`.
-/

@[expose] public section

open Real Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace DLMF.Elliptic

/-- `x^{-1/2} = (√x)⁻¹` for `x ≥ 0`. -/
lemma rpow_neg_half_eq_recip_sqrt {x : ℝ} (hx : 0 ≤ x) : x ^ (-(1 / 2) : ℝ) = (√x)⁻¹ := by
  rw [rpow_neg hx, sqrt_eq_rpow]

/-- The integral `∫₀^∞ ((t²+a²)(t²+b²))^{-1/2} dt`. -/
def gaussLineIntegral (a b : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)) ^ (-(1 / 2) : ℝ)

/-- The map `t ↦ (t - ab/t)/2`. -/
def gaussSubst (a b t : ℝ) : ℝ := (t - a * b / t) / 2

/-- `t ↦ (t - ab/t)/2` maps `(0, ∞)` onto `ℝ`. -/
lemma gaussSubst_image {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    gaussSubst a b '' Ioi 0 = univ := by
  refine eq_univ_of_forall fun y => ?_
  have hab : 0 < a * b := mul_pos ha hb
  have hs : |y| < √(y ^ 2 + a * b) := by
    rw [← sqrt_sq_eq_abs]; exact sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have ht : 0 < y + √(y ^ 2 + a * b) := by linarith [neg_abs_le y]
  refine ⟨y + √(y ^ 2 + a * b), ht, ?_⟩
  have hsq := sq_sqrt (by positivity : (0 : ℝ) ≤ y ^ 2 + a * b)
  simp only [gaussSubst]
  field_simp
  nlinarith [hsq]

/-- `t ↦ (t - ab/t)/2` is injective on `(0, ∞)`. -/
lemma gaussSubst_injOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : InjOn (gaussSubst a b) (Ioi 0) := by
  refine StrictMonoOn.injOn fun s hs t ht hst => ?_
  have hs : (0 : ℝ) < s := hs
  have ht : (0 : ℝ) < t := ht
  simp only [gaussSubst]
  have : a * b / t < a * b / s := div_lt_div_of_pos_left (mul_pos ha hb) hs hst
  linarith

/-- The derivative of `t ↦ (t - ab/t)/2`. -/
lemma hasDerivAt_gaussSubst (a b : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (gaussSubst a b) ((1 + a * b / t ^ 2) / 2) t := by
  have h := ((hasDerivAt_id t).sub ((hasDerivAt_inv ht).const_mul (a * b))).div_const 2
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  · field_simp; ring
  · simp only [gaussSubst, Pi.sub_apply, id]; ring

/-- The integrand identity behind Gauss's invariance. -/
lemma gaussSubst_pointwise {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    |(1 + a * b / t ^ 2) / 2| * ((gaussSubst a b t ^ 2 + ((a + b) / 2) ^ 2) *
      (gaussSubst a b t ^ 2 + √(a * b) ^ 2)) ^ (-(1 / 2) : ℝ) =
      2 * ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)) ^ (-(1 / 2) : ℝ) := by
  have hab : 0 ≤ a * b := (mul_pos ha hb).le
  set X := (t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2) with hX
  have hX0 : 0 < X := by positivity
  set Y := (t ^ 2 + a * b) / (4 * t ^ 2) with hY
  have hY0 : 0 < Y := by positivity
  have hprod : (gaussSubst a b t ^ 2 + ((a + b) / 2) ^ 2) * (gaussSubst a b t ^ 2 + √(a * b) ^ 2)
      = X * Y ^ 2 := by
    rw [sq_sqrt hab, hX, hY, gaussSubst]
    field_simp
    ring
  rw [hprod, rpow_neg_half_eq_recip_sqrt (by positivity), rpow_neg_half_eq_recip_sqrt hX0.le,
    sqrt_mul hX0.le, sqrt_sq hY0.le, abs_of_pos (by positivity)]
  have hsX : 0 < √X := sqrt_pos.mpr hX0
  rw [hY]
  field_simp
  ring

/-- **Gauss's invariance** `∫₀^∞ ((t²+a²)(t²+b²))^{-1/2} dt` is unchanged when `(a, b)` is
replaced by `((a+b)/2, √(ab))` (Temme, proof of Theorem 12.1). -/
theorem gaussLineIntegral_am_gm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    gaussLineIntegral ((a + b) / 2) √(a * b) = gaussLineIntegral a b := by
  have hcv := integral_image_eq_integral_abs_deriv_smul (f := gaussSubst a b)
    (f' := fun t => (1 + a * b / t ^ 2) / 2) measurableSet_Ioi
    (fun t ht => (hasDerivAt_gaussSubst a b (ne_of_gt ht)).hasDerivWithinAt)
    (gaussSubst_injOn ha hb)
    (fun u => ((u ^ 2 + ((a + b) / 2) ^ 2) * (u ^ 2 + √(a * b) ^ 2)) ^ (-(1 / 2) : ℝ))
  rw [gaussSubst_image ha hb, Measure.restrict_univ] at hcv
  have heven := integral_comp_abs
    (f := fun u => ((u ^ 2 + ((a + b) / 2) ^ 2) * (u ^ 2 + √(a * b) ^ 2)) ^ (-(1 / 2) : ℝ))
  simp only [sq_abs] at heven
  rw [heven] at hcv
  have hpt : ∫ t in Ioi (0 : ℝ), |(1 + a * b / t ^ 2) / 2| •
      ((gaussSubst a b t ^ 2 + ((a + b) / 2) ^ 2) * (gaussSubst a b t ^ 2 + √(a * b) ^ 2)) ^
        (-(1 / 2) : ℝ) =
      ∫ t in Ioi (0 : ℝ), 2 * ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)) ^ (-(1 / 2) : ℝ) :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      rw [smul_eq_mul]; exact gaussSubst_pointwise ha hb ht
  rw [hpt, integral_const_mul] at hcv
  unfold gaussLineIntegral
  linarith

/-- `∫₀^{π/2} (a² cos²θ + b² sin²θ)^{-1/2} dθ`, which is `(π/2)/M(a, b)` (Temme (12.9)). -/
def agmIntegral (a b : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(π / 2), (a ^ 2 * cos θ ^ 2 + b ^ 2 * sin θ ^ 2) ^ (-(1 / 2) : ℝ)

/-- `t ↦ arctan(t/b)` maps `(0, ∞)` onto `(0, π/2)`. -/
lemma arctan_div_image {b : ℝ} (hb : 0 < b) :
    (fun t => arctan (t / b)) '' Ioi 0 = Ioo 0 (π / 2) := by
  ext θ
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨arctan_pos.mpr (div_pos ht hb), arctan_lt_pi_div_two _⟩
  · rintro ⟨h0, h1⟩
    refine ⟨b * tan θ, mul_pos hb (tan_pos_of_pos_of_lt_pi_div_two h0 h1), ?_⟩
    simp only
    rw [mul_div_cancel_left₀ _ hb.ne', arctan_tan (by linarith [pi_pos]) h1]

/-- The integrand identity for the substitution `t = b tan θ`. -/
lemma agmIntegral_pointwise {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    |b / (b ^ 2 + t ^ 2)| * (a ^ 2 * cos (arctan (t / b)) ^ 2 +
      b ^ 2 * sin (arctan (t / b)) ^ 2) ^ (-(1 / 2) : ℝ) =
      ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)) ^ (-(1 / 2) : ℝ) := by
  have h1 := sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + (t / b) ^ 2)
  have hs1 : 0 < √(1 + (t / b) ^ 2) := sqrt_pos.mpr (by positivity)
  have hbase : a ^ 2 * cos (arctan (t / b)) ^ 2 + b ^ 2 * sin (arctan (t / b)) ^ 2 =
      b ^ 2 * ((t ^ 2 + a ^ 2) / (t ^ 2 + b ^ 2)) := by
    rw [cos_arctan, sin_arctan]
    generalize √(1 + (t / b) ^ 2) = S at h1 hs1 ⊢
    rw [div_pow, div_pow, h1]
    field_simp
    ring
  rw [hbase, rpow_neg_half_eq_recip_sqrt (by positivity), rpow_neg_half_eq_recip_sqrt (by positivity),
    sqrt_mul (by positivity), sqrt_mul' _ (by positivity), sqrt_sq hb.le,
    sqrt_div' _ (by positivity), abs_of_pos (by positivity)]
  have hA : 0 < √(t ^ 2 + a ^ 2) := sqrt_pos.mpr (by positivity)
  have hB : 0 < √(t ^ 2 + b ^ 2) := sqrt_pos.mpr (by positivity)
  have hB2 := sq_sqrt (by positivity : (0 : ℝ) ≤ t ^ 2 + b ^ 2)
  rw [show b ^ 2 + t ^ 2 = t ^ 2 + b ^ 2 by ring]
  generalize √(t ^ 2 + a ^ 2) = A at hA ⊢
  generalize √(t ^ 2 + b ^ 2) = B at hB hB2 ⊢
  rw [← hB2]
  field_simp

/-- `∫₀^{π/2} (a² cos²θ + b² sin²θ)^{-1/2} dθ = ∫₀^∞ ((t²+a²)(t²+b²))^{-1/2} dt`
(substitution `t = b tan θ`). -/
theorem agmIntegral_eq_gaussLineIntegral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    agmIntegral a b = gaussLineIntegral a b := by
  have hcv := integral_image_eq_integral_abs_deriv_smul (f := fun t => arctan (t / b))
    (f' := fun t => b / (b ^ 2 + t ^ 2)) (measurableSet_Ioi (a := (0 : ℝ)))
    (fun t _ => by
      have h := (hasDerivAt_arctan (t / b)).comp t ((hasDerivAt_id t).div_const b)
      refine (h.congr_deriv ?_).hasDerivWithinAt
      field_simp)
    (fun s _ t _ h => by
      have := arctan_injective h
      exact (div_left_inj' hb.ne').mp this)
    (fun θ => (a ^ 2 * cos θ ^ 2 + b ^ 2 * sin θ ^ 2) ^ (-(1 / 2) : ℝ))
  rw [arctan_div_image hb] at hcv
  rw [agmIntegral, intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo,
    hcv, gaussLineIntegral]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => by
    rw [smul_eq_mul]; exact agmIntegral_pointwise ha hb ht

/-- `agmIntegral` is symmetric. -/
lemma agmIntegral_comm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : agmIntegral a b = agmIntegral b a := by
  rw [agmIntegral_eq_gaussLineIntegral ha hb, agmIntegral_eq_gaussLineIntegral hb ha,
    gaussLineIntegral, gaussLineIntegral]
  simp_rw [mul_comm (_ ^ 2 + a ^ 2)]

/-- Gauss's invariance for `agmIntegral` (Temme, proof of Theorem 12.1). -/
theorem agmIntegral_am_gm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    agmIntegral ((a + b) / 2) √(a * b) = agmIntegral a b := by
  rw [agmIntegral_eq_gaussLineIntegral (by positivity) (sqrt_pos.mpr (mul_pos ha hb)),
    agmIntegral_eq_gaussLineIntegral ha hb, gaussLineIntegral_am_gm ha hb]

/-- Homogeneity: `agmIntegral (λa) (λb) = λ⁻¹ agmIntegral a b` for `λ > 0`. -/
lemma agmIntegral_mul {l a b : ℝ} (hl : 0 < l) :
    agmIntegral (l * a) (l * b) = l⁻¹ * agmIntegral a b := by
  rw [agmIntegral, agmIntegral, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [show (l * a) ^ 2 * cos θ ^ 2 + (l * b) ^ 2 * sin θ ^ 2 =
    l ^ 2 * (a ^ 2 * cos θ ^ 2 + b ^ 2 * sin θ ^ 2) by ring,
    mul_rpow (by positivity) (by positivity), ← rpow_natCast, ← rpow_mul hl.le,
    show ((2 : ℕ) : ℝ) * (-(1 / 2)) = -1 by norm_num, rpow_neg_one]

/-- Bounds: `(π/2)/max(a,b) ≤ agmIntegral a b ≤ (π/2)/min(a,b)` for `0 < b ≤ a`. -/
lemma agmIntegral_mem_Icc {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    π / 2 / a ≤ agmIntegral a b ∧ agmIntegral a b ≤ π / 2 / b := by
  have hbase : ∀ θ, b ^ 2 ≤ a ^ 2 * cos θ ^ 2 + b ^ 2 * sin θ ^ 2 ∧
      a ^ 2 * cos θ ^ 2 + b ^ 2 * sin θ ^ 2 ≤ a ^ 2 := by
    intro θ
    have h := sin_sq_add_cos_sq θ
    have h2 : b ^ 2 ≤ a ^ 2 := by nlinarith
    constructor <;> nlinarith [sq_nonneg (cos θ), sq_nonneg (sin θ)]
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  have hcont : Continuous fun θ : ℝ => (a ^ 2 * cos θ ^ 2 + b ^ 2 * sin θ ^ 2) ^ (-(1 / 2) : ℝ) :=
    (by fun_prop : Continuous fun θ : ℝ => a ^ 2 * cos θ ^ 2 + b ^ 2 * sin θ ^ 2).rpow_const
      fun θ => Or.inl (by nlinarith [(hbase θ).1, sq_pos_of_pos hb])
  have hpow : ∀ x : ℝ, 0 < x → (x ^ 2) ^ (-(1 / 2) : ℝ) = x⁻¹ := fun x hx => by
    rw [← rpow_natCast, ← rpow_mul hx.le]; norm_num; rw [rpow_neg_one]
  constructor
  · have h := intervalIntegral.integral_mono_on (a := 0) (b := π / 2) (by positivity)
      (f := fun _ => a⁻¹) (g := fun θ => (a ^ 2 * cos θ ^ 2 + b ^ 2 * sin θ ^ 2) ^ (-(1 / 2) : ℝ))
      (intervalIntegrable_const (μ := MeasureTheory.volume)) (hcont.intervalIntegrable _ _)
      fun θ _ => by
        rw [← hpow a (by linarith)]
        exact rpow_le_rpow_of_nonpos (by nlinarith [(hbase θ).1, sq_pos_of_pos hb]) (hbase θ).2
          (by norm_num)
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
    rw [agmIntegral]; linarith [show π / 2 / a = π / 2 * a⁻¹ by ring]
  · have h := intervalIntegral.integral_mono_on (a := 0) (b := π / 2) (by positivity)
      (g := fun _ => b⁻¹) (f := fun θ => (a ^ 2 * cos θ ^ 2 + b ^ 2 * sin θ ^ 2) ^ (-(1 / 2) : ℝ))
      (hcont.intervalIntegrable _ _)
      (intervalIntegrable_const (μ := MeasureTheory.volume)) fun θ _ => by
        rw [← hpow b hb]
        exact rpow_le_rpow_of_nonpos (by positivity) (hbase θ).1 (by norm_num)
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
    rw [agmIntegral]; linarith [show π / 2 / b = π / 2 * b⁻¹ by ring]

open NNReal in
/-- `agmIntegral` is constant along the AGM iteration. -/
lemma agmIntegral_agmSequences {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) (n : ℕ) :
    agmIntegral (NNReal.agmSequences x y n).1 (NNReal.agmSequences x y n).2 = agmIntegral x y := by
  induction n generalizing x y with
  | zero =>
    simp only [NNReal.agmSequences_zero, Real.coe_sqrt, NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_add, NNReal.coe_ofNat]
    have hx' : (0 : ℝ) < x := hx
    have hy' : (0 : ℝ) < y := hy
    rw [agmIntegral_comm (Real.sqrt_pos.mpr (mul_pos hx' hy')) (by positivity),
      agmIntegral_am_gm hx' hy']
  | succ n ih =>
    rw [NNReal.agmSequences_succ, ih (NNReal.sqrt_pos.mpr (mul_pos hx hy)) (by positivity)]
    have := ih (x := x) (y := y) hx hy
    simp only [Real.coe_sqrt, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_add,
      NNReal.coe_ofNat]
    have hx' : (0 : ℝ) < x := hx
    have hy' : (0 : ℝ) < y := hy
    rw [agmIntegral_comm (Real.sqrt_pos.mpr (mul_pos hx' hy')) (by positivity),
      agmIntegral_am_gm hx' hy']

open NNReal in
/-- **Gauss's theorem** (Temme Theorem 12.1, (12.9)):
`∫₀^{π/2} (a² cos²θ + b² sin²θ)^{-1/2} dθ = π / (2 M(a, b))` for `a, b > 0`. -/
@[dlmf 19.8.E4]
theorem agmIntegral_eq_pi_div_two_div_agm {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) :
    agmIntegral x y = π / 2 / (NNReal.agm x y : ℝ) := by
  have hM : (0 : ℝ) < NNReal.agm x y := NNReal.agm_pos hx hy
  set s := NNReal.agmSequences x y
  have hpos : ∀ n, (0 : ℝ) < (s n).1 := fun n => by
    have h1 : (s 0).1 ≤ (s n).1 := NNReal.agmSequences_fst_monotone (Nat.zero_le n)
    have h0 : (0 : ℝ≥0) < (s 0).1 := by
      simp only [s, NNReal.agmSequences_zero]; exact NNReal.sqrt_pos.mpr (mul_pos hx hy)
    exact_mod_cast lt_of_lt_of_le h0 h1
  have hb : ∀ n, π / 2 / ((s n).2 : ℝ) ≤ agmIntegral x y ∧
      agmIntegral x y ≤ π / 2 / ((s n).1 : ℝ) := fun n => by
      have hle : ((s n).1 : ℝ) ≤ (s n).2 := by exact_mod_cast NNReal.agmSequences_fst_le_snd n n
      rw [← agmIntegral_agmSequences hx hy n, agmIntegral_comm (hpos n) (by linarith [hpos n])]
      exact agmIntegral_mem_Icc (hpos n) hle
  have hc : ContinuousAt (fun z : ℝ => π / 2 / z) (NNReal.agm x y : ℝ) :=
    continuousAt_const.div continuousAt_id hM.ne'
  have h1 := hc.tendsto.comp (NNReal.tendsto_coe.mpr NNReal.tendsto_agmSequences_fst_agm)
  have h2 := hc.tendsto.comp (NNReal.tendsto_coe.mpr NNReal.tendsto_agmSequences_snd_agm)
  exact le_antisymm (ge_of_tendsto' h1 fun n => (hb n).2) (le_of_tendsto' h2 fun n => (hb n).1)

/-- `K(m) = ∫₀^{π/2} (cos²θ + (1-m) sin²θ)^{-1/2} dθ`. -/
lemma Real.compEllIntKm_eq_agmIntegral {m : ℝ} (hm : m < 1) :
    Real.compEllIntKm m = agmIntegral 1 √(1 - m) := by
  rw [Real.compEllIntKm, agmIntegral]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [sq_sqrt (by linarith), one_pow, one_mul, cos_sq']
  ring_nf

/-- **Gauss's AGM formula** `K(m) = π / (2 M(1, √(1-m)))` (Temme (12.10), DLMF 19.8.5). -/
@[dlmf 19.8.E5]
theorem Real.compEllIntKm_eq_pi_div_agm {m : ℝ} (hm : m < 1) :
    Real.compEllIntKm m = π / (2 * (NNReal.agm 1 (NNReal.sqrt (1 - m).toNNReal) : ℝ)) := by
  have hy : (0 : NNReal) < NNReal.sqrt (1 - m).toNNReal :=
    NNReal.sqrt_pos.mpr (Real.toNNReal_pos.mpr (by linarith))
  have h := agmIntegral_eq_pi_div_two_div_agm one_pos hy
  rw [Real.coe_sqrt, Real.coe_toNNReal _ (by linarith), NNReal.coe_one] at h
  rw [Real.compEllIntKm_eq_agmIntegral hm, h, div_div]

/-- **Descending Landen transformation** (Temme (12.11), DLMF 19.8.12): with
`k' = √(1-m)` and `k₁ = (1 - k')/(1 + k')`, `K(m) = (1 + k₁) K(k₁²)`. -/
@[dlmf 19.8.E12]
theorem Real.compEllIntKm_landen_descending {m : ℝ} (hm : m < 1) :
    Real.compEllIntKm m = (1 + (1 - √(1 - m)) / (1 + √(1 - m))) *
      Real.compEllIntKm (((1 - √(1 - m)) / (1 + √(1 - m))) ^ 2) := by
  set k' := √(1 - m) with hk'
  have hk0 : 0 < k' := sqrt_pos.mpr (by linarith)
  have hk1 : 0 < 1 + k' := by linarith
  have hk1' : (1 - k') / (1 + k') < 1 := by rw [div_lt_one hk1]; linarith
  have hsq : ((1 - k') / (1 + k')) ^ 2 < 1 := by
    have : -1 < (1 - k') / (1 + k') := by rw [lt_div_iff₀ hk1]; linarith
    nlinarith
  have hroot : √(1 - ((1 - k') / (1 + k')) ^ 2) = 2 * √k' / (1 + k') := by
    rw [show 1 - ((1 - k') / (1 + k')) ^ 2 = (2 * √k' / (1 + k')) ^ 2 by
      rw [show (2 * √k' / (1 + k')) ^ 2 = 4 * k' / (1 + k') ^ 2 by
        rw [div_pow, mul_pow, sq_sqrt hk0.le]; norm_num]
      field_simp; ring]
    exact sqrt_sq (by positivity)
  rw [Real.compEllIntKm_eq_agmIntegral hm, Real.compEllIntKm_eq_agmIntegral hsq, hroot,
    ← agmIntegral_am_gm one_pos hk0, one_mul]
  have hl : 0 < (1 + k') / 2 := by positivity
  rw [show (1 + k') / 2 = (1 + k') / 2 * 1 by ring,
    show √k' = (1 + k') / 2 * (2 * √k' / (1 + k')) by field_simp, agmIntegral_mul hl]
  field_simp
  ring

/-- **Ascending Landen transformation** (Temme (12.12)): for `0 ≤ m < 1`, `k = √m`,
`K(m) = K((2√k/(1+k))²)/(1+k)`. -/
theorem Real.compEllIntKm_landen_ascending {m : ℝ} (hm0 : 0 ≤ m) (hm : m < 1) :
    Real.compEllIntKm m = Real.compEllIntKm ((2 * √(√m) / (1 + √m)) ^ 2) / (1 + √m) := by
  set k := √m with hk
  have hk0 : 0 ≤ k := sqrt_nonneg m
  have hk1 : k < 1 := by rw [hk, sqrt_lt' one_pos]; simpa using hm
  have hkm : k ^ 2 = m := sq_sqrt hm0
  have hpos : 0 < 1 + k := by linarith
  have hsq : (2 * √k / (1 + k)) ^ 2 < 1 := by
    rw [div_pow, mul_pow, sq_sqrt hk0, div_lt_one (by positivity)]
    nlinarith [sq_nonneg (1 - k)]
  have hroot : √(1 - (2 * √k / (1 + k)) ^ 2) = (1 - k) / (1 + k) := by
    rw [show 1 - (2 * √k / (1 + k)) ^ 2 = ((1 - k) / (1 + k)) ^ 2 by
      rw [div_pow, mul_pow, sq_sqrt hk0]; field_simp; ring]
    exact sqrt_sq (div_nonneg (by linarith) hpos.le)
  have hgm : √((1 + k) * (1 - k)) = √(1 - m) := by rw [← hkm]; ring_nf
  rw [Real.compEllIntKm_eq_agmIntegral hm, Real.compEllIntKm_eq_agmIntegral hsq, hroot]
  have hinv := agmIntegral_am_gm hpos (by linarith : 0 < 1 - k)
  rw [show ((1 + k) + (1 - k)) / 2 = 1 by ring, hgm] at hinv
  have hmul := agmIntegral_mul (l := 1 + k) (a := 1) (b := (1 - k) / (1 + k)) hpos
  rw [mul_one, show (1 + k) * ((1 - k) / (1 + k)) = 1 - k by field_simp] at hmul
  rw [hinv, hmul]
  field_simp

/-- **Descending Landen transformation for `E`** (Temme (12.14)): with `k' = √(1-m)` and
`k₁ = (1-k')/(1+k')`, `E(m) = (1+k') E(k₁²) - k' K(m)`. Obtained by differentiating the descending
transformation of `K` and using `dK/dm` on both sides. -/
@[dlmf 19.8.E12]
theorem Real.compEllIntEm_landen_descending {m : ℝ} (hm : m < 1) :
    Real.compEllIntEm m =
      (1 + √(1 - m)) * Real.compEllIntEm (((1 - √(1 - m)) / (1 + √(1 - m))) ^ 2) -
        √(1 - m) * Real.compEllIntKm m := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp [Real.compEllIntEm_zero, Real.compEllIntKm_zero]; ring
  set s := √(1 - m) with hsdef
  have hs0 : 0 < s := sqrt_pos.mpr (by linarith)
  have hs2 : s ^ 2 = 1 - m := sq_sqrt (by linarith)
  have hs1 : s ≠ 1 := fun h => hm0 (by nlinarith)
  set k := (1 - s) / (1 + s) with hkdef
  have hk1 : 0 < 1 + s := by linarith
  have hμ1 : k ^ 2 < 1 := by
    have h1 : k < 1 := by rw [hkdef, div_lt_one hk1]; linarith
    have h2 : -1 < k := by rw [hkdef, lt_div_iff₀ hk1]; linarith
    nlinarith
  have hμ0 : k ^ 2 ≠ 0 := by
    have : k ≠ 0 := by rw [hkdef]; exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hs1)) hk1.ne'
    positivity
  -- derivatives
  have hsd : HasDerivAt (fun m => √(1 - m)) (-1 / (2 * s)) m := by
    have := ((hasDerivAt_id m).const_sub 1).sqrt (by simp; linarith)
    simpa using this
  have hkd : HasDerivAt (fun m => (1 - √(1 - m)) / (1 + √(1 - m)))
      ((-(-1 / (2 * s)) * (1 + s) - (1 - s) * (-1 / (2 * s))) / (1 + s) ^ 2) m :=
    (hsd.const_sub 1).div (hsd.const_add 1) hk1.ne'
  have hKμ := (Real.hasDerivAt_compEllIntKm hμ1 hμ0).comp m (hkd.pow 2)
  have hL := (hkd.const_add 1).mul hKμ
  have heq : Real.compEllIntKm =ᶠ[𝓝 m] fun m => (1 + (1 - √(1 - m)) / (1 + √(1 - m))) *
      Real.compEllIntKm (((1 - √(1 - m)) / (1 + √(1 - m))) ^ 2) := by
    filter_upwards [Iio_mem_nhds hm] with x hx
    exact Real.compEllIntKm_landen_descending hx
  have hd := (Real.hasDerivAt_compEllIntKm hm hm0).unique (hL.congr_of_eventuallyEq heq)
  have hK := Real.compEllIntKm_landen_descending hm
  rw [← hsdef, ← hkdef] at hK hd
  simp only [Function.comp] at hd
  generalize Real.compEllIntEm m = E at *
  generalize Real.compEllIntKm m = K at *
  generalize Real.compEllIntEm (k ^ 2) = Eμ at *
  generalize Real.compEllIntKm (k ^ 2) = Kμ at *
  rw [show m = 1 - s ^ 2 by linarith] at hd
  have h1 : (1 : ℝ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h2 : (1 : ℝ) - s ^ 2 ≠ 0 := by
    intro h; apply hm0; nlinarith
  have h3 : s ≠ 0 := hs0.ne'
  have h4 : (1 : ℝ) + s ≠ 0 := hk1.ne'
  have hk0 : k ≠ 0 := by rw [hkdef]; exact div_ne_zero h1 h4
  have hk2 : (1 : ℝ) - k ^ 2 ≠ 0 := by linarith
  have hks : k * (1 + s) = 1 - s := by rw [hkdef]; field_simp
  norm_num at hd
  field_simp at hd hK
  have hF : k * (1 - k ^ 2) * (1 + s) ^ 2 ≠ 0 := by positivity
  apply mul_left_cancel₀ hF
  linear_combination hd + (-k * s * (k - 1) * (k + 1) * (s + 1) ^ 3) * hK +
    (-(k + 1) * (s + 1) * (-Eμ * k * s - Eμ * k + 2 * Eμ * s + Kμ * k ^ 2 * s ^ 2 +
      Kμ * k ^ 2 * s - Kμ * k * s ^ 2 + Kμ * k * s - 2 * Kμ * s)) * hks

/-- **Ascending Landen transformation for `E`** (Temme (12.13)): for `0 ≤ m < 1`, `k = √m`,
`E(m) = (1+k)/2 · E((2√k/(1+k))²) + k'²/2 · K(m)`. -/
theorem Real.compEllIntEm_landen_ascending {m : ℝ} (hm0 : 0 ≤ m) (hm : m < 1) :
    Real.compEllIntEm m = (1 + √m) / 2 * Real.compEllIntEm ((2 * √(√m) / (1 + √m)) ^ 2) +
      (1 - m) / 2 * Real.compEllIntKm m := by
  have hKa := Real.compEllIntKm_landen_ascending hm0 hm
  set k := √m with hk
  have hk0 : 0 ≤ k := sqrt_nonneg m
  have hk1 : k < 1 := by rw [hk, sqrt_lt' one_pos]; simpa using hm
  have hkm : k ^ 2 = m := sq_sqrt hm0
  have hpos : 0 < 1 + k := by linarith
  have hsq : (2 * √k / (1 + k)) ^ 2 < 1 := by
    rw [div_pow, mul_pow, sq_sqrt hk0, div_lt_one (by positivity)]
    nlinarith [sq_nonneg (1 - k)]
  have hroot : √(1 - (2 * √k / (1 + k)) ^ 2) = (1 - k) / (1 + k) := by
    rw [show 1 - (2 * √k / (1 + k)) ^ 2 = ((1 - k) / (1 + k)) ^ 2 by
      rw [div_pow, mul_pow, sq_sqrt hk0]; field_simp; ring]
    exact sqrt_sq (div_nonneg (by linarith) hpos.le)
  have hd := Real.compEllIntEm_landen_descending hsq
  rw [hroot, show (1 - (1 - k) / (1 + k)) / (1 + (1 - k) / (1 + k)) = k by field_simp; ring,
    hkm] at hd
  rw [hd]
  rw [eq_div_iff hpos.ne'] at hKa
  rw [← hKa, ← hkm]
  field_simp
  ring

end DLMF.Elliptic
