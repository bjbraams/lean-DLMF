/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Digamma
public import DLMF.Gamma.ComplexBinet
public import DLMF.Gamma.Products
public import DLMF.Gamma.SpecialValues
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Inequalities (DLMF §5.6)

Real-variable inequalities and complex Gamma bounds from DLMF §5.6.
The Gamma-ratio bound has real shifts `0 ≤ a` and `1 ≤ b - a` and holds
on the open right half-plane. The final Gamma bound assumes `0 ≤ z.re`.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.Gamma

/-- By Binet's formula the middle term is `exp Φ(x)` with `0 < Φ(x) < 1/(12x)`
(Temme §3.6.1). -/
@[dlmf 5.6.E1]
theorem Gamma_stirling_bounds {x : ℝ} (hx : 0 < x) :
    1 < (2 * π) ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 - x) * Real.exp x * Real.Gamma x ∧
      (2 * π) ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 - x) * Real.exp x * Real.Gamma x <
        Real.exp (1 / (12 * x)) := by
  have hQ : (2 * π) ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 - x) * Real.exp x * Real.Gamma x =
      Real.exp (binetIntegral x) := by
    rw [← Real.exp_log (Real.Gamma_pos_of_pos hx), log_Gamma_eq_add_binetIntegral hx,
      Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos hx, ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  obtain ⟨h0, h1⟩ := binetIntegral_pos_lt hx
  rw [hQ]
  exact ⟨Real.one_lt_exp_iff.mpr h0, Real.exp_lt_exp.mpr h1⟩

section RecipGammaSq

/-! ### DLMF 5.6.2–5.6.3

For `1 ≤ x < 2` write `x = 1 + t` and `1/x = 1 - r`. Taylor bounds for `log Γ` at `1`,
from the monotonicity and a Lipschitz bound of the trigamma function, give
`log Γ(1/x) ≥ γr + ζ(2)r²/2` and `log Γ(x) ≥ -γt + ζ(2)t²/2 - 4t³/9`. The estimate
`cosh d ≤ e^{d²/2}` then reduces `Γ(x)⁻² + Γ(1/x)⁻² ≤ 2` to a polynomial inequality in `t`,
using `1/2 < γ < 3/5` and `π ≈ 3.14`. For `x ≥ 2` both terms are at most `1`.
-/

open Set


local notation "γ" => Real.eulerMascheroniConstant

/-- `γ < 3/5`, from `H₃₂ - log 32`. -/
theorem eulerMascheroniConstant_lt_three_fifths : γ < 3 / 5 := by
  refine (Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 32).trans ?_
  have h : Real.eulerMascheroniSeq' 32 = (harmonic 32 : ℝ) - Real.log 32 := by
    simp [Real.eulerMascheroniSeq']
  have hlog : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  have hH : (harmonic 32 : ℚ) < 3 / 5 + 5 * 0.6931471803 := by
    simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have hH' : (harmonic 32 : ℝ) < 3 / 5 + 5 * 0.6931471803 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hH
    push_cast at this
    exact this
  rw [h, hlog]
  linarith [Real.log_two_gt_d9]

/-- The trigamma function is antitone on `(0, ∞)`. -/
theorem trigamma_le_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.trigamma y ≤ Real.trigamma x := by
  have hy : 0 < y := hx.trans_le hxy
  rw [Real.trigamma_eq_tsum hy, Real.trigamma_eq_tsum hx]
  refine Summable.tsum_le_tsum (fun n => ?_) (Real.summable_trigamma hy)
    (Real.summable_trigamma hx)
  have h1 : 0 < x + n := by positivity
  have h2 : x + n ≤ y + n := by linarith
  exact pow_le_pow_left₀ (by positivity) (inv_anti₀ h1 h2) 2

theorem hasSum_recip_one_add_sq : HasSum (fun n : ℕ => ((1 : ℝ) + n)⁻¹ ^ 2) (π ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simp only [Finset.sum_range_one, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, div_zero, sub_zero] at h
  refine h.congr_fun fun n => ?_
  push_cast
  rw [one_div, inv_pow, add_comm]

theorem trigamma_one_eq : Real.trigamma 1 = π ^ 2 / 6 := by
  rw [Real.trigamma_eq_tsum one_pos]
  exact hasSum_recip_one_add_sq.tsum_eq

theorem summable_recip_one_add_cube : Summable fun n : ℕ => ((1 : ℝ) + n)⁻¹ ^ 3 := by
  refine hasSum_recip_one_add_sq.summable.of_nonneg_of_le (fun n => by positivity) fun n => ?_
  have h1 : (1 : ℝ) ≤ 1 + n := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h0 : ((1 : ℝ) + n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  rw [pow_succ]
  exact mul_le_of_le_one_right (by positivity) h0

/-- `ζ(3) ≤ 4/3`, from `n⁻³ ≤ n⁻²/2` for `n ≥ 2` and `ζ(2) = π²/6`. -/
theorem tsum_recip_one_add_cube_le : ∑' n : ℕ, ((1 : ℝ) + n)⁻¹ ^ 3 ≤ 4 / 3 := by
  set g : ℕ → ℝ := fun n : ℕ => ((1 : ℝ) + n)⁻¹ ^ 2 / 2 + if n = 0 then 1 / 2 else 0
  have hg : HasSum g (π ^ 2 / 6 / 2 + 1 / 2) :=
    (hasSum_recip_one_add_sq.div_const 2).add (hasSum_ite_eq 0 (1 / 2 : ℝ))
  have hle : ∀ n : ℕ, ((1 : ℝ) + n)⁻¹ ^ 3 ≤ g n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [g]
      norm_num
    · have h2 : (2 : ℝ) ≤ 1 + n := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have h0 : ((1 : ℝ) + n)⁻¹ ≤ 1 / 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        norm_num
        linarith
      simp only [g, hn.ne', ite_false, add_zero]
      rw [pow_succ, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left h0 (by positivity)
  calc ∑' n : ℕ, ((1 : ℝ) + n)⁻¹ ^ 3 ≤ ∑' n, g n :=
        Summable.tsum_le_tsum hle summable_recip_one_add_cube hg.summable
    _ = π ^ 2 / 6 / 2 + 1 / 2 := hg.tsum_eq
    _ ≤ 4 / 3 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]

theorem recip_sq_sub_recip_sq_le {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    a⁻¹ ^ 2 - (a + s)⁻¹ ^ 2 ≤ 2 * s * a⁻¹ ^ 3 := by
  have hb : 0 < a + s := by linarith
  have key : a⁻¹ ^ 2 - (a + s)⁻¹ ^ 2 = s * (2 * a + s) / (a ^ 2 * (a + s) ^ 2) := by
    field_simp
    ring
  rw [key, inv_pow, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ s * a ^ 2 * (a + 2 * (a + s)) * s := by positivity
  nlinarith [this]

/-- A Lipschitz bound for the trigamma function to the right of `1`. -/
theorem trigamma_one_sub_le {s : ℝ} (hs : 0 ≤ s) :
    Real.trigamma 1 - Real.trigamma (1 + s) ≤ 8 / 3 * s := by
  have h1s : 0 < 1 + s := by linarith
  rw [Real.trigamma_eq_tsum one_pos, Real.trigamma_eq_tsum h1s,
    ← (Real.summable_trigamma one_pos).tsum_sub (Real.summable_trigamma h1s)]
  calc ∑' n : ℕ, ((1 + (n : ℝ))⁻¹ ^ 2 - (1 + s + n)⁻¹ ^ 2)
      ≤ ∑' n : ℕ, 2 * s * ((1 : ℝ) + n)⁻¹ ^ 3 := by
        refine Summable.tsum_le_tsum (fun n => ?_)
          ((Real.summable_trigamma one_pos).sub (Real.summable_trigamma h1s))
          (summable_recip_one_add_cube.mul_left _)
        have := recip_sq_sub_recip_sq_le (a := 1 + n) (by positivity) hs
        rwa [show (1 : ℝ) + n + s = 1 + s + n by ring] at this
    _ = 2 * s * ∑' n : ℕ, ((1 : ℝ) + n)⁻¹ ^ 3 := tsum_mul_left
    _ ≤ 2 * s * (4 / 3) := mul_le_mul_of_nonneg_left tsum_recip_one_add_cube_le (by positivity)
    _ = 8 / 3 * s := by ring

theorem hasDerivAt_digamma_trigamma {x : ℝ} (hx : 0 < x) :
    HasDerivAt Real.digamma (Real.trigamma x) x := by
  rw [Real.trigamma_eq_tsum hx]
  exact Real.hasDerivAt_digamma hx

/-- Third-order Taylor lower bound for `log Γ` to the right of `1`. -/
theorem log_Gamma_one_add_ge {t : ℝ} (ht : 0 ≤ t) :
    -γ * t + π ^ 2 / 6 * t ^ 2 / 2 - 4 / 9 * t ^ 3 ≤ Real.log (Real.Gamma (1 + t)) := by
  -- first derivative bound
  set g : ℝ → ℝ := fun s => Real.digamma (1 + s) + γ - π ^ 2 / 6 * s + 4 / 3 * s ^ 2
  have hgd : ∀ s, 0 ≤ s → HasDerivAt g (Real.trigamma (1 + s) - π ^ 2 / 6 + 8 / 3 * s) s := by
    intro s hs
    have h1 := (hasDerivAt_digamma_trigamma (x := 1 + s) (by linarith)).comp_const_add 1 s
    have h2 := ((h1.add_const γ).sub ((hasDerivAt_id s).const_mul (π ^ 2 / 6))).add
      (((hasDerivAt_id s).pow 2).const_mul (4 / 3))
    exact h2.congr_deriv (by simp; ring)
  have hgmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun s hs => (hgd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hgd s (interior_subset hs)).hasDerivWithinAt) fun s hs => ?_
    rw [interior_Ici] at hs
    have := trigamma_one_sub_le (le_of_lt hs)
    rw [trigamma_one_eq] at this
    linarith
  have hg0 : g 0 = 0 := by simp [g, Real.digamma_one]
  have hgnn : ∀ s, 0 ≤ s → 0 ≤ g s := fun s hs =>
    hg0 ▸ hgmono ((Set.mem_Ici.mpr le_rfl)) hs hs
  set h : ℝ → ℝ := fun s => Real.log (Real.Gamma (1 + s)) -
    (-γ * s + π ^ 2 / 6 * s ^ 2 / 2 - 4 / 9 * s ^ 3)
  have hhd : ∀ s, 0 ≤ s → HasDerivAt h (g s) s := by
    intro s hs
    have h1 := (Real.hasDerivAt_log_Gamma (x := 1 + s) (by linarith)).comp_const_add 1 s
    have h2 := h1.sub (((((hasDerivAt_id s).const_mul (-γ)).add
      (((hasDerivAt_id s).pow 2).const_mul (π ^ 2 / 6) |>.div_const 2))).sub
      (((hasDerivAt_id s).pow 3).const_mul (4 / 9)))
    exact h2.congr_deriv (by simp [g]; ring)
  have hhmono : MonotoneOn h (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun s hs => (hhd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hhd s (interior_subset hs)).hasDerivWithinAt)
      fun s hs => hgnn s (interior_subset hs)
  have hh0 : h 0 = 0 := by simp [h]
  have := hhmono ((Set.mem_Ici.mpr le_rfl)) ht ht
  rw [hh0] at this
  simp only [h] at this
  linarith

/-- Second-order Taylor lower bound for `log Γ` to the left of `1`. -/
theorem log_Gamma_one_sub_ge {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    γ * r + π ^ 2 / 6 * r ^ 2 / 2 ≤ Real.log (Real.Gamma (1 - r)) := by
  set k1 : ℝ → ℝ := fun s => -Real.digamma (1 - s) - γ - π ^ 2 / 6 * s
  have hk1d : ∀ s ∈ Ico (0 : ℝ) 1, HasDerivAt k1 (Real.trigamma (1 - s) - π ^ 2 / 6) s := by
    intro s hs
    have h1 := (hasDerivAt_digamma_trigamma (x := 1 - s) (by linarith [hs.2])).comp_const_sub 1 s
    have h2 := (h1.neg.sub_const γ).sub ((hasDerivAt_id s).const_mul (π ^ 2 / 6))
    exact h2.congr_deriv (by simp)
  have hk1mono : MonotoneOn k1 (Ico 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
      (fun s hs => (hk1d s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hk1d s (interior_subset hs)).hasDerivWithinAt) fun s hs => ?_
    rw [interior_Ico] at hs
    have := trigamma_le_of_le (x := 1 - s) (y := 1) (by linarith [hs.2]) (by linarith [hs.1])
    rw [trigamma_one_eq] at this
    linarith
  have hk10 : k1 0 = 0 := by simp [k1, Real.digamma_one]
  have h0mem : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, one_pos⟩
  have hk1nn : ∀ s ∈ Ico (0 : ℝ) 1, 0 ≤ k1 s := fun s hs =>
    hk10 ▸ hk1mono h0mem hs hs.1
  set k : ℝ → ℝ := fun s => Real.log (Real.Gamma (1 - s)) - (γ * s + π ^ 2 / 6 * s ^ 2 / 2)
  have hkd : ∀ s ∈ Ico (0 : ℝ) 1, HasDerivAt k (k1 s) s := by
    intro s hs
    have h1 := (Real.hasDerivAt_log_Gamma (x := 1 - s) (by linarith [hs.2])).comp_const_sub 1 s
    have h2 := h1.sub (((hasDerivAt_id s).const_mul γ).add
      (((hasDerivAt_id s).pow 2).const_mul (π ^ 2 / 6) |>.div_const 2))
    exact h2.congr_deriv (by simp [k1]; ring)
  have hkmono : MonotoneOn k (Ico 0 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
      (fun s hs => (hkd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hkd s (interior_subset hs)).hasDerivWithinAt)
      fun s hs => hk1nn s (interior_subset hs)
  have hk0 : k 0 = 0 := by simp [k]
  have := hkmono h0mem ⟨hr0, hr1⟩ hr0
  rw [hk0] at this
  simp only [k] at this
  linarith

/-- `e^X + e^Y ≤ 2` once `4(X+Y) + (X-Y)² ≤ 0`, via `cosh d ≤ e^{d²/2}`. -/
theorem exp_add_exp_le_two {X Y : ℝ} (h : 4 * (X + Y) + (X - Y) ^ 2 ≤ 0) :
    Real.exp X + Real.exp Y ≤ 2 := by
  have hc := Real.cosh_le_exp_half_sq ((X - Y) / 2)
  have heq : Real.exp X + Real.exp Y =
      2 * Real.exp ((X + Y) / 2) * Real.cosh ((X - Y) / 2) := by
    rw [Real.cosh_eq, mul_assoc, mul_div_assoc', mul_add, ← Real.exp_add, ← Real.exp_add]
    field_simp
    ring_nf
  rw [heq]
  calc 2 * Real.exp ((X + Y) / 2) * Real.cosh ((X - Y) / 2)
      ≤ 2 * Real.exp ((X + Y) / 2) * Real.exp (((X - Y) / 2) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 2 * Real.exp ((X + Y) / 2 + ((X - Y) / 2) ^ 2 / 2) := by
        rw [mul_assoc, ← Real.exp_add]
    _ ≤ 2 * Real.exp 0 := by
        gcongr
        nlinarith
    _ = 2 := by simp

/-- The polynomial inequality behind DLMF 5.6.3. -/
theorem recip_Gamma_sq_poly {t g Z : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hg0 : 1 / 2 ≤ g)
    (hg1 : g ≤ 3 / 5) (hZ0 : 1643 / 1000 ≤ Z) (hZ1 : Z ≤ 1654 / 1000) :
    (g * ((1 + t) ^ 2 + (1 + t)) - Z * t ^ 2 * (2 + t) / 2 + 4 / 9 * t ^ 2 * (1 + t) ^ 2) ^ 2 ≤
      2 * (-g * (1 + t) + Z * ((1 + t) ^ 2 + 1) / 2 - 4 / 9 * t * (1 + t) ^ 2) *
        (1 + t) ^ 2 := by
  set e := g * ((1 + t) ^ 2 + (1 + t)) - Z * t ^ 2 * (2 + t) / 2 + 4 / 9 * t ^ 2 * (1 + t) ^ 2
  set f := -g * (1 + t) + Z * ((1 + t) ^ 2 + 1) / 2 - 4 / 9 * t * (1 + t) ^ 2
  set e' := 3 / 5 * ((1 + t) ^ 2 + (1 + t)) - 1643 / 1000 * t ^ 2 * (2 + t) / 2 +
    4 / 9 * t ^ 2 * (1 + t) ^ 2
  set f' := -(3 / 5) * (1 + t) + 1643 / 1000 * ((1 + t) ^ 2 + 1) / 2 -
    4 / 9 * t * (1 + t) ^ 2
  have ht2 : 0 ≤ t ^ 2 * (2 + t) := by positivity
  have he0 : 0 ≤ e := by
    have : Z * t ^ 2 * (2 + t) / 2 ≤ 1654 / 1000 * t ^ 2 * (2 + t) / 2 := by
      have := mul_le_mul_of_nonneg_right hZ1 ht2
      linarith
    have : 1 / 2 * ((1 + t) ^ 2 + (1 + t)) ≤ g * ((1 + t) ^ 2 + (1 + t)) :=
      mul_le_mul_of_nonneg_right hg0 (by positivity)
    simp only [e]
    nlinarith [mul_nonneg ht0 (sub_nonneg.2 ht1), mul_nonneg (mul_nonneg ht0 ht0)
      (sub_nonneg.2 ht1)]
  have hee : e ≤ e' := by
    have h1 := mul_le_mul_of_nonneg_right hg1 (by positivity : (0 : ℝ) ≤ (1 + t) ^ 2 + (1 + t))
    have h2 := mul_le_mul_of_nonneg_right hZ0 ht2
    simp only [e, e']
    nlinarith
  have hff : f' ≤ f := by
    have h1 := mul_le_mul_of_nonneg_right hg1 (by positivity : (0 : ℝ) ≤ 1 + t)
    have h2 := mul_le_mul_of_nonneg_right hZ0 (by positivity : (0 : ℝ) ≤ (1 + t) ^ 2 + 1)
    simp only [f, f']
    nlinarith
  have hpoly : e' ^ 2 ≤ 2 * f' * (1 + t) ^ 2 := by
    have h1 : t ^ 2 ≤ t := by nlinarith
    have h2 : t ^ 3 ≤ t ^ 2 := by nlinarith
    have h3 : t ^ 4 ≤ t ^ 3 := by nlinarith
    have h5 : t ^ 5 ≤ t ^ 4 := by nlinarith
    have h6 : 0 ≤ t ^ 6 := by positivity
    have h7 : t ^ 7 ≤ t ^ 4 := by nlinarith [pow_le_pow_of_le_one ht0 ht1 (by norm_num : 4 ≤ 7)]
    have h8 : t ^ 8 ≤ t ^ 4 := by nlinarith [pow_le_pow_of_le_one ht0 ht1 (by norm_num : 4 ≤ 8)]
    simp only [e', f']
    nlinarith
  calc e ^ 2 ≤ e' ^ 2 := pow_le_pow_left₀ he0 hee 2
    _ ≤ 2 * f' * (1 + t) ^ 2 := hpoly
    _ ≤ 2 * f * (1 + t) ^ 2 := by gcongr

theorem recip_sq_eq_exp {G : ℝ} (hG : 0 < G) : (1 / G) ^ 2 = Real.exp (-2 * Real.log G) := by
  rw [neg_mul, Real.exp_neg, show 2 * Real.log G = Real.log (G ^ 2) by
    rw [Real.log_pow]; norm_num, Real.exp_log (by positivity), one_div, inv_pow]

theorem recip_Gamma_sq_add_of_one_le_of_lt_two {x : ℝ} (h1 : 1 ≤ x) (h2 : x < 2) :
    (1 / Real.Gamma x) ^ 2 + (1 / Real.Gamma x⁻¹) ^ 2 ≤ 2 := by
  have hx0 : 0 < x := by linarith
  obtain ⟨t, rfl⟩ : ∃ t, x = 1 + t := ⟨x - 1, by ring⟩
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t ≤ 1 := by linarith
  have h1t : 0 < 1 + t := by linarith
  set r := t / (1 + t) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one h1t]; linarith
  have hxinv : (1 + t)⁻¹ = 1 - r := by rw [hr]; field_simp; ring
  set Plo := -γ * t + π ^ 2 / 6 * t ^ 2 / 2 - 4 / 9 * t ^ 3 with hPlo
  set Mlo := γ * r + π ^ 2 / 6 * r ^ 2 / 2 with hMlo
  have hP : Plo ≤ Real.log (Real.Gamma (1 + t)) := log_Gamma_one_add_ge ht0
  have hM : Mlo ≤ Real.log (Real.Gamma (1 + t)⁻¹) := by
    rw [hxinv]; exact log_Gamma_one_sub_ge hr0 hr1
  have hγ0 : 1 / 2 ≤ γ := Real.one_half_lt_eulerMascheroniConstant.le
  have hγ1 : γ ≤ 3 / 5 := eulerMascheroniConstant_lt_three_fifths.le
  have hZ0 : 1643 / 1000 ≤ π ^ 2 / 6 := by nlinarith [Real.pi_gt_d2, Real.pi_pos]
  have hZ1 : π ^ 2 / 6 ≤ 1654 / 1000 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hpoly := recip_Gamma_sq_poly ht0 ht1 hγ0 hγ1 hZ0 hZ1
  set e := γ * ((1 + t) ^ 2 + (1 + t)) - π ^ 2 / 6 * t ^ 2 * (2 + t) / 2 +
    4 / 9 * t ^ 2 * (1 + t) ^ 2 with he
  set f := -γ * (1 + t) + π ^ 2 / 6 * ((1 + t) ^ 2 + 1) / 2 - 4 / 9 * t * (1 + t) ^ 2
    with hf
  have hdiff : (Mlo - Plo) ^ 2 = t ^ 2 * e ^ 2 / (1 + t) ^ 4 := by
    rw [hMlo, hPlo, hr, he]; field_simp; ring
  have hsum : 2 * (Mlo + Plo) = t ^ 2 * (2 * f * (1 + t) ^ 2) / (1 + t) ^ 4 := by
    rw [hMlo, hPlo, hr, hf]; field_simp; ring
  have key : (Mlo - Plo) ^ 2 ≤ 2 * (Mlo + Plo) := by
    rw [hdiff, hsum]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (sq_nonneg t))
      (by positivity)
  rw [recip_sq_eq_exp (Real.Gamma_pos_of_pos hx0),
    recip_sq_eq_exp (Real.Gamma_pos_of_pos (inv_pos.2 hx0))]
  calc Real.exp (-2 * Real.log (Real.Gamma (1 + t))) +
        Real.exp (-2 * Real.log (Real.Gamma (1 + t)⁻¹))
      ≤ Real.exp (-2 * Plo) + Real.exp (-2 * Mlo) := by
        exact add_le_add (Real.exp_le_exp.2 (by linarith)) (Real.exp_le_exp.2 (by linarith))
    _ ≤ 2 := by
        apply exp_add_exp_le_two
        nlinarith [key]

/-- DLMF 5.6.3, the inequality `Γ(x)⁻² + Γ(1/x)⁻² ≤ 2` for `x > 0`. -/
theorem recip_Gamma_sq_add_le_two {x : ℝ} (hx : 0 < x) :
    (1 / Real.Gamma x) ^ 2 + (1 / Real.Gamma x⁻¹) ^ 2 ≤ 2 := by
  wlog h1 : 1 ≤ x generalizing x
  · have hx' : 1 ≤ x⁻¹ := (one_le_inv₀ hx).2 (le_of_lt (not_le.1 h1))
    have := this (inv_pos.2 hx) hx'
    rwa [inv_inv, add_comm] at this
  rcases lt_or_ge x 2 with h2 | h2
  · exact recip_Gamma_sq_add_of_one_le_of_lt_two h1 h2
  · have hG : 1 ≤ Real.Gamma x := by
      have := Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr le_rfl)
        (Set.mem_Ici.mpr h2) h2
      rwa [Real.Gamma_two] at this
    have hxi : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    have hG' : 1 ≤ Real.Gamma x⁻¹ := by
      have := Real.Gamma_strictAntiOn_Ioc.antitoneOn ⟨inv_pos.2 hx, hxi⟩
        ⟨one_pos, le_rfl⟩ hxi
      rwa [Real.Gamma_one] at this
    have a : (1 / Real.Gamma x) ^ 2 ≤ 1 := by
      rw [div_pow, one_pow]
      exact div_le_one_of_le₀ (one_le_pow₀ hG) (by positivity)
    have b : (1 / Real.Gamma x⁻¹) ^ 2 ≤ 1 := by
      rw [div_pow, one_pow]
      exact div_le_one_of_le₀ (one_le_pow₀ hG') (by positivity)
    linarith

end RecipGammaSq

@[dlmf 5.6.E2]
theorem recip_Gamma_add_recip_Gamma_recip {x : ℝ} (hx : 0 < x) :
    1 / Real.Gamma x + 1 / Real.Gamma x⁻¹ ≤ 2 := by
  have h := recip_Gamma_sq_add_le_two hx
  nlinarith [sq_nonneg (1 / Real.Gamma x - 1 / Real.Gamma x⁻¹),
    sq_nonneg (1 / Real.Gamma x + 1 / Real.Gamma x⁻¹ - 2)]

@[dlmf 5.6.E3]
theorem recip_Gamma_sq_add {x : ℝ} (hx : 0 < x) :
    (1 / Real.Gamma x) ^ 2 + (1 / Real.Gamma x⁻¹) ^ 2 ≤ 2 := by
  exact recip_Gamma_sq_add_le_two hx

/-- `ψ` is strictly increasing on `(0, ∞)`. -/
theorem digamma_strictMonoOn : StrictMonoOn Real.digamma (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  rw [Real.digamma_eq_tsum hx', Real.digamma_eq_tsum hy']
  have h := (Real.summable_digammaSeriesTerm hx').tsum_lt_tsum (i := 0)
    (fun n => by
      simp only [Real.digammaSeriesTerm]
      have : 0 < x + n := by positivity
      gcongr)
    (by simp only [Real.digammaSeriesTerm, Nat.cast_zero, add_zero]; gcongr)
    (Real.summable_digammaSeriesTerm hy')
  linarith

/-- `log Γ` is strictly convex on `(0, ∞)`. -/
theorem strictConvexOn_log_Gamma :
    StrictConvexOn ℝ (Set.Ioi 0) fun y : ℝ => Real.log (Real.Gamma y) := by
  refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi 0)
    (fun y hy => (Real.hasDerivAt_log_Gamma hy).continuousAt.continuousWithinAt) ?_
  rw [interior_Ioi]
  intro a ha b hb hab
  rw [(Real.hasDerivAt_log_Gamma ha).deriv, (Real.hasDerivAt_log_Gamma hb).deriv]
  exact digamma_strictMonoOn ha hb hab

theorem log_Gamma_add_one' {y : ℝ} (hy : 0 < y) :
    Real.log (Real.Gamma (y + 1)) = Real.log (Real.Gamma y) + Real.log y := by
  rw [Real.Gamma_add_one hy.ne', Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]

/-- Gautschi's inequality, from the strict log-convexity of `Γ`. -/
@[dlmf 5.6.E4]
theorem Gamma_ratio_bounds {x s : ℝ} (hx : 0 < x) (hs0 : 0 < s) (hs1 : s < 1) :
    x ^ (1 - s) < Real.Gamma (x + 1) / Real.Gamma (x + s) ∧
      Real.Gamma (x + 1) / Real.Gamma (x + s) < (x + 1) ^ (1 - s) := by
  set f : ℝ → ℝ := fun y => Real.log (Real.Gamma y) with hf
  have hsc := strictConvexOn_log_Gamma
  have hxs : 0 < x + s := by linarith
  have hfx : f (x + 1) = f x + Real.log x := log_Gamma_add_one' hx
  have hfxs : f (x + s + 1) = f (x + s) + Real.log (x + s) := log_Gamma_add_one' hxs
  have hlow : f (x + s) < (1 - s) * f x + s * f (x + 1) := by
    have := hsc.2 (show x ∈ Set.Ioi 0 from hx) (show x + 1 ∈ Set.Ioi 0 by
      simp only [Set.mem_Ioi]; linarith) (by linarith : x ≠ x + 1)
      (by linarith : (0 : ℝ) < 1 - s) hs0 (by ring : 1 - s + s = 1)
    simp only [smul_eq_mul] at this
    rwa [show (1 - s) * x + s * (x + 1) = x + s by ring] at this
  have hup : f (x + 1) < s * f (x + s) + (1 - s) * f (x + s + 1) := by
    have := hsc.2 (show x + s ∈ Set.Ioi 0 from hxs) (show x + s + 1 ∈ Set.Ioi 0 by
      simp only [Set.mem_Ioi]; linarith) (by linarith : x + s ≠ x + s + 1)
      hs0 (by linarith : (0 : ℝ) < 1 - s) (by ring : s + (1 - s) = 1)
    simp only [smul_eq_mul] at this
    rwa [show s * (x + s) + (1 - s) * (x + s + 1) = x + 1 by ring] at this
  have hGpos : 0 < Real.Gamma (x + 1) / Real.Gamma (x + s) :=
    div_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos hxs)
  have hratio : Real.log (Real.Gamma (x + 1) / Real.Gamma (x + s)) = f (x + 1) - f (x + s) :=
    Real.log_div (Real.Gamma_pos_of_pos (by linarith)).ne' (Real.Gamma_pos_of_pos hxs).ne'
  constructor
  · rw [← Real.exp_log hGpos, ← Real.exp_log (Real.rpow_pos_of_pos hx _), Real.exp_lt_exp,
      Real.log_rpow hx, hratio]
    rw [hfx] at hlow ⊢
    nlinarith
  · rw [← Real.exp_log hGpos, ← Real.exp_log (Real.rpow_pos_of_pos (by linarith : 0 < x + 1) _),
      Real.exp_lt_exp, Real.log_rpow (by linarith), hratio]
    have hl : Real.log (x + s) < Real.log (x + 1) := Real.log_lt_log hxs (by linarith)
    rw [hfxs] at hup
    nlinarith

/-- `log r ≤ (r - r⁻¹)/2` for `r ≥ 1` (logarithmic vs geometric mean). -/
theorem log_le_half_sub_recip {r : ℝ} (hr : 1 ≤ r) : Real.log r ≤ (r - r⁻¹) / 2 := by
  set k : ℝ → ℝ := fun r => (r - r⁻¹) / 2 - Real.log r with hk
  have hd : ∀ r : ℝ, 0 < r → HasDerivAt k ((1 + (r ^ 2)⁻¹) / 2 - r⁻¹) r := by
    intro r hr
    have := (((hasDerivAt_id r).sub (hasDerivAt_inv hr.ne')).div_const 2).sub
      (Real.hasDerivAt_log hr.ne')
    exact this.congr_deriv (by first | ring | (simp only [id_eq]; ring))
  have hmono : MonotoneOn k (Set.Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 1)
      (fun r hr => (hd r (by linarith [Set.mem_Ici.mp hr])).continuousAt.continuousWithinAt)
      (fun r hr => (hd r (by rw [interior_Ici] at hr; linarith [Set.mem_Ioi.mp hr]))
        |>.differentiableAt.differentiableWithinAt) fun r hr => ?_
    rw [interior_Ici] at hr
    have hr' : 0 < r := by linarith [Set.mem_Ioi.mp hr]
    rw [(hd r hr').deriv]
    have : (1 + (r ^ 2)⁻¹) / 2 - r⁻¹ = (1 - r⁻¹) ^ 2 / 2 := by field_simp; ring
    rw [this]; positivity
  have := hmono Set.self_mem_Ici hr hr
  simp only [hk, inv_one, sub_self, zero_div, Real.log_one] at this
  linarith

/-- `log(b/a) ≤ (b - a)/√(ab)` for `0 < a ≤ b`. -/
theorem log_div_le_sub_div_sqrt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log (b / a) ≤ (b - a) / Real.sqrt (a * b) := by
  set r := Real.sqrt (b / a) with hr
  have hba : 1 ≤ b / a := by rw [le_div_iff₀ ha]; linarith
  have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_sqrt.mpr hba
  have hr0 : 0 < r := by linarith
  have hsq : r ^ 2 = b / a := Real.sq_sqrt (by positivity)
  have hlog : Real.log (b / a) = 2 * Real.log r := by
    rw [← hsq, Real.log_pow]; push_cast; ring
  have hab' : Real.sqrt (a * b) = a * r := by
    have ha0 : a ≠ 0 := ha.ne'
    rw [hr, show a * b = a ^ 2 * (b / a) by field_simp, Real.sqrt_mul (sq_nonneg a),
      Real.sqrt_sq ha.le]
  rw [hlog, hab']
  have h := log_le_half_sub_recip hr1
  have hb : b = a * r ^ 2 := by rw [hsq]; field_simp
  rw [hb]
  have : (a * r ^ 2 - a) / (a * r) = r - r⁻¹ := by field_simp
  rw [this]
  linarith

/-- `2(b - a)/(a + b) ≤ log(b/a)` for `0 < a ≤ b` (logarithmic vs arithmetic mean). -/
theorem two_mul_sub_div_add_le_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    2 * (b - a) / (a + b) ≤ Real.log (b / a) := by
  set k : ℝ → ℝ := fun r => Real.log r - 2 * (r - 1) / (r + 1) with hk
  have hd : ∀ r : ℝ, 0 < r → HasDerivAt k (r⁻¹ - 4 / (r + 1) ^ 2) r := by
    intro r hr
    have h1 : r + 1 ≠ 0 := by linarith
    have := (Real.hasDerivAt_log hr.ne').sub
      ((((hasDerivAt_id r).sub_const 1).const_mul 2).div ((hasDerivAt_id r).add_const 1) h1)
    exact this.congr_deriv (by simp only [id_eq]; ring)
  have hmono : MonotoneOn k (Set.Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 1)
      (fun r hr => (hd r (by linarith [Set.mem_Ici.mp hr])).continuousAt.continuousWithinAt)
      (fun r hr => (hd r (by rw [interior_Ici] at hr; linarith [Set.mem_Ioi.mp hr]))
        |>.differentiableAt.differentiableWithinAt) fun r hr => ?_
    rw [interior_Ici] at hr
    have hr' : 0 < r := by linarith [Set.mem_Ioi.mp hr]
    rw [(hd r hr').deriv]
    have : r⁻¹ - 4 / (r + 1) ^ 2 = (r - 1) ^ 2 / (r * (r + 1) ^ 2) := by field_simp; ring
    rw [this]; positivity
  have hba : 1 ≤ b / a := by rw [le_div_iff₀ ha]; linarith
  have := hmono Set.self_mem_Ici hba hba
  simp only [hk, Real.log_one, sub_self, mul_zero, zero_div] at this
  have heq : 2 * (b / a - 1) / (b / a + 1) = 2 * (b - a) / (a + b) := by
    field_simp
    ring
  linarith

/-- `log Γ(z+1) - log Γ(z+s) - (1-s) ψ(z+c) → 0` as `z → ∞`, for `c > 0`. -/
theorem tendsto_log_Gamma_ratio_sub_digamma {s c : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 < c) :
    Tendsto (fun z : ℝ => Real.log (Real.Gamma (z + 1)) - Real.log (Real.Gamma (z + s)) -
      (1 - s) * Real.digamma (z + c)) atTop (𝓝 0) := by
  have hlogq : ∀ a b : ℝ, Tendsto (fun z : ℝ => Real.log (z + a) - Real.log (z + b)) atTop
      (𝓝 0) := by
    intro a b
    have h1 : Tendsto (fun z : ℝ => (z + a) / (z + b)) atTop (𝓝 1) := by
      have : Tendsto (fun z : ℝ => (1 + a * z⁻¹) / (1 + b * z⁻¹)) atTop (𝓝 ((1 + a * 0) /
          (1 + b * 0))) :=
        ((tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul a)).div
          (tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul b)) (by simp))
      simp only [mul_zero, add_zero, div_one] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with z hz
      field_simp
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    rw [Real.log_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (|a| + |b|)] with z hz
    have ha : 0 < z + a := by linarith [neg_abs_le a, abs_nonneg b]
    have hb : 0 < z + b := by linarith [neg_abs_le b, abs_nonneg a]
    simp only [Function.comp_apply]
    rw [Real.log_div ha.ne' hb.ne']
  have hinv : Tendsto (fun z : ℝ => (z + c)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ c tendsto_id)
  -- lower and upper bounds
  have hlo : Tendsto (fun z : ℝ => (1 - s) * (Real.log (z + 0) - Real.log (z + c))) atTop
      (𝓝 0) := by simpa using (hlogq 0 c).const_mul (1 - s)
  have hhi : Tendsto (fun z : ℝ => (1 - s) * ((Real.log (z + 1) - Real.log (z + c)) +
      (z + c)⁻¹)) atTop (𝓝 0) := by simpa using ((hlogq 1 c).add hinv).const_mul (1 - s)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with z hz
    obtain ⟨h1, -⟩ := Gamma_ratio_bounds hz hs0 hs1
    have hpos := div_pos (Real.Gamma_pos_of_pos (by linarith : 0 < z + 1))
      (Real.Gamma_pos_of_pos (by linarith : 0 < z + s))
    have hl := Real.log_lt_log (Real.rpow_pos_of_pos hz _) h1
    rw [Real.log_rpow hz, Real.log_div (Real.Gamma_pos_of_pos (by linarith)).ne'
      (Real.Gamma_pos_of_pos (by linarith)).ne'] at hl
    have hψ := (digamma_le_log_and (by linarith : 0 < z + c)).2
    rw [add_zero]
    nlinarith
  · filter_upwards [eventually_gt_atTop 0] with z hz
    obtain ⟨-, h2⟩ := Gamma_ratio_bounds hz hs0 hs1
    have hpos := div_pos (Real.Gamma_pos_of_pos (by linarith : 0 < z + 1))
      (Real.Gamma_pos_of_pos (by linarith : 0 < z + s))
    have hl := Real.log_lt_log hpos h2
    rw [Real.log_rpow (by linarith), Real.log_div (Real.Gamma_pos_of_pos (by linarith)).ne'
      (Real.Gamma_pos_of_pos (by linarith)).ne'] at hl
    have hψ := (digamma_le_log_and (by linarith : 0 < z + c)).1
    rw [one_div] at hψ
    nlinarith

/-- A function on `(0, ∞)` with `F(y+1) ≤ F(y)` and `F(z) → 0` as `z → ∞` is nonnegative. -/
theorem nonneg_of_antitone_step_of_tendsto {F : ℝ → ℝ} (hstep : ∀ y, 0 < y → F (y + 1) ≤ F y)
    (hlim : Tendsto F atTop (𝓝 0)) {y : ℝ} (hy : 0 < y) : 0 ≤ F y := by
  have hk : ∀ k : ℕ, F (y + k) ≤ F y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hstep (y + k) (by positivity)
      push_cast
      rw [← add_assoc]
      linarith
  have hseq : Tendsto (fun k : ℕ => F (y + k)) atTop (𝓝 0) :=
    hlim.comp (tendsto_atTop_add_const_left _ y tendsto_natCast_atTop_atTop)
  exact le_of_tendsto' hseq hk

/-- The bounds of Elezović, Giordano and Pečarić. Both follow by telescoping: the step
`y ↦ y + 1` changes the gap by `log((y+1)/(y+s)) - (1-s)/(y+c)`, whose sign is fixed by the
inequalities between the logarithmic mean and the geometric (`c = √s`) or arithmetic
(`c = (1+s)/2`) means, and the gap tends to `0`. -/
@[dlmf 5.6.E5]
theorem Gamma_ratio_digamma_bounds {x s : ℝ} (hx : 0 < x) (hs0 : 0 < s) (hs1 : s < 1) :
    Real.exp ((1 - s) * Real.digamma (x + Real.sqrt s)) ≤
        Real.Gamma (x + 1) / Real.Gamma (x + s) ∧
      Real.Gamma (x + 1) / Real.Gamma (x + s) ≤
        Real.exp ((1 - s) * Real.digamma (x + (s + 1) / 2)) := by
  have hGpos : ∀ y, 0 < y → 0 < Real.Gamma (y + 1) / Real.Gamma (y + s) := fun y hy =>
    div_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos (by linarith))
  have hratio : ∀ y, 0 < y → Real.log (Real.Gamma (y + 1) / Real.Gamma (y + s)) =
      Real.log (Real.Gamma (y + 1)) - Real.log (Real.Gamma (y + s)) := fun y hy =>
    Real.log_div (Real.Gamma_pos_of_pos (by linarith)).ne' (Real.Gamma_pos_of_pos (by linarith)).ne'
  -- the step of `log Γ(y+1) - log Γ(y+s)` under `y ↦ y + 1`
  have hstepΓ : ∀ y, 0 < y →
      (Real.log (Real.Gamma (y + 1 + 1)) - Real.log (Real.Gamma (y + 1 + s))) =
        (Real.log (Real.Gamma (y + 1)) - Real.log (Real.Gamma (y + s))) +
          (Real.log (y + 1) - Real.log (y + s)) := by
    intro y hy
    rw [log_Gamma_add_one' (by linarith : 0 < y + 1),
      show y + 1 + s = (y + s) + 1 by ring, log_Gamma_add_one' (by linarith : 0 < y + s)]
    ring
  have hsq0 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have hsq1 : Real.sqrt s ≤ 1 := Real.sqrt_le_one.mpr hs1.le
  constructor
  · set F : ℝ → ℝ := fun y => Real.log (Real.Gamma (y + 1)) - Real.log (Real.Gamma (y + s)) -
      (1 - s) * Real.digamma (y + Real.sqrt s) with hF
    have hstep : ∀ y, 0 < y → F (y + 1) ≤ F y := by
      intro y hy
      simp only [hF]
      rw [hstepΓ y hy, show y + 1 + Real.sqrt s = (y + Real.sqrt s) + 1 by ring,
        Real.digamma_add_one (by positivity)]
      -- `log((y+1)/(y+s)) ≤ (1-s)/(y+√s)`
      have hmean := log_div_le_sub_div_sqrt (a := y + s) (b := y + 1) (by linarith)
        (by linarith)
      rw [Real.log_div (by linarith) (by linarith)] at hmean
      have hgeo : y + Real.sqrt s ≤ Real.sqrt ((y + s) * (y + 1)) := by
        rw [Real.le_sqrt (by positivity) (by positivity)]
        have : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs0.le
        nlinarith [sq_nonneg (1 - Real.sqrt s), mul_nonneg hy.le (sq_nonneg (1 - Real.sqrt s))]
      have hfrac : (y + 1 - (y + s)) / Real.sqrt ((y + s) * (y + 1)) ≤
          (1 - s) * (y + Real.sqrt s)⁻¹ := by
        rw [show y + 1 - (y + s) = 1 - s by ring, div_eq_mul_inv]
        gcongr
      nlinarith
    have h := nonneg_of_antitone_step_of_tendsto hstep
      (tendsto_log_Gamma_ratio_sub_digamma hs0 hs1 hsq0) hx
    rw [← Real.exp_log (hGpos x hx), Real.exp_le_exp, hratio x hx]
    simp only [hF] at h
    linarith
  · set G : ℝ → ℝ := fun y => (1 - s) * Real.digamma (y + (s + 1) / 2) -
      (Real.log (Real.Gamma (y + 1)) - Real.log (Real.Gamma (y + s))) with hG
    have hc0 : 0 < (s + 1) / 2 := by linarith
    have hc1 : (s + 1) / 2 ≤ 1 := by linarith
    have hstep : ∀ y, 0 < y → G (y + 1) ≤ G y := by
      intro y hy
      simp only [hG]
      rw [hstepΓ y hy, show y + 1 + (s + 1) / 2 = (y + (s + 1) / 2) + 1 by ring,
        Real.digamma_add_one (by positivity)]
      have hmean := two_mul_sub_div_add_le_log (a := y + s) (b := y + 1) (by linarith)
        (by linarith)
      rw [Real.log_div (by linarith) (by linarith)] at hmean
      have : 2 * (y + 1 - (y + s)) / (y + s + (y + 1)) = (1 - s) * (y + (s + 1) / 2)⁻¹ := by
        have : y + (s + 1) / 2 ≠ 0 := by linarith
        field_simp
        ring
      rw [this] at hmean
      nlinarith
    have hlim : Tendsto G atTop (𝓝 0) := by
      simpa [hG] using (tendsto_log_Gamma_ratio_sub_digamma hs0 hs1 hc0).neg
    have h := nonneg_of_antitone_step_of_tendsto hstep hlim hx
    rw [← Real.exp_log (hGpos x hx), Real.exp_le_exp, hratio x hx]
    simp only [hG] at h
    linarith

@[dlmf 5.6.E6]
theorem norm_Gamma_add_mul_I_le {x y : ℝ} (hx : 0 < x) :
    ‖Complex.Gamma (x + I * y)‖ ≤ |Real.Gamma x| := by
  have hre : (0 : ℝ) < (x + I * y : ℂ).re := by simpa using hx
  rw [Complex.Gamma_eq_integral hre, Complex.GammaIntegral,
    abs_of_pos (Real.Gamma_pos_of_pos hx), Real.Gamma_eq_integral hx]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos ht']
  simp

@[dlmf 5.6.E7]
theorem norm_Gamma_add_mul_I_ge {x y : ℝ} (hx : 1 / 2 ≤ x) :
    ‖Complex.Gamma (x + I * y)‖ ≥ Real.sqrt (1 / Real.cosh (π * y)) * Real.Gamma x := by
  -- `|Γ(x)/Γ(x+iy)|² = ∏ (1 + y²/(x+k)²) ≤ ∏ (1 + y²/(1/2+k)²) = cosh(πy)` (DLMF 5.8.3)
  have hx0 : 0 < x := by linarith
  have hnp : ∀ s : ℝ, 0 < s → ∀ k : ℕ, (s : ℂ) ≠ -k := fun s hs k h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hz : ∀ s : ℝ, 0 < s → ∀ k : ℕ, (s : ℂ) + I * y ≠ -k := fun s hs k h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hP := Gamma_div_Gamma_add_mul_I_sq (y := y) (hnp x hx0)
  have hP' := Gamma_div_Gamma_add_mul_I_sq (x := 1 / 2) (y := y) (hnp _ (by norm_num))
  have hle : ∏' k : ℕ, (1 + y ^ 2 / (x + k) ^ 2) ≤ ∏' k : ℕ, (1 + y ^ 2 / (1 / 2 + k) ^ 2) := by
    refine le_of_tendsto_of_tendsto'
      (multipliable_one_add_sq_div_add_sq x y).hasProd.tendsto_prod_nat
      (multipliable_one_add_sq_div_add_sq (1 / 2) y).hasProd.tendsto_prod_nat
      fun n => Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ => ?_
    have hk : (1 / 2 : ℝ) + k ≤ x + k := by linarith
    gcongr
  -- the value at `x = 1/2`
  have hhalf : ∏' k : ℕ, (1 + y ^ 2 / (1 / 2 + k) ^ 2) = Real.cosh (π * y) := by
    rw [← hP', norm_div, Real.Gamma_one_half_eq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos), div_pow, Real.sq_sqrt Real.pi_pos.le]
    have h := (Gamma_half_add_mul_I y).2
    push_cast at h ⊢
    rw [h]
    have := Real.cosh_pos (π * y)
    field_simp
  have hGx := Real.Gamma_pos_of_pos hx0
  have hn : 0 < ‖Complex.Gamma (x + I * y)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero (hz x hx0))
  have hineq : Real.Gamma x ^ 2 ≤ Real.cosh (π * y) * ‖Complex.Gamma (x + I * y)‖ ^ 2 := by
    have h := hP.trans_le (hle.trans_eq hhalf)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hGx, div_pow,
      div_le_iff₀ (by positivity)] at h
    exact h
  have hc := Real.cosh_pos (π * y)
  rw [ge_iff_le, ← Real.sqrt_sq hn.le, ← Real.sqrt_sq hGx.le, ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hc]
  linarith

/-- A Gamma-ratio bound on the right half-plane for nonnegative real shifts
separated by at least one. These restrictions are essential in DLMF 5.6.8. -/
@[dlmf 5.6.E8]
theorem Gamma_ratio_norm_le {a b : ℝ} {z : ℂ} (hz : 0 < z.re)
    (ha : 0 ≤ a) (hba : 1 ≤ b - a) :
    ‖Complex.Gamma (z + a) / Complex.Gamma (z + b)‖ ≤ ‖z‖ ^ (-(b - a)) := by
  sorry

/-- A complex Gamma bound in the closed right half-plane, away from zero. -/
@[dlmf 5.6.E9]
theorem norm_Gamma_bound {z : ℂ} (hz : z ∈ slitPlane) (hre : 0 ≤ z.re) :
    ‖Complex.Gamma z‖ ≤
      Real.sqrt (2 * π) * ‖z‖ ^ (z.re - 1 / 2) * Real.exp (-π * |z.im| / 2) *
        Real.exp (1 / (6 * ‖z‖)) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hmu : (binetMu z).re ≤ 1 / (6 * ‖z‖) :=
    (re_le_norm _).trans (norm_binetMu_le_of_re_nonneg hz0 hre)
  have harg := pi_div_two_mul_abs_im_le hre
  rw [norm_Gamma_eq_binet hz]
  gcongr
  linarith

end DLMF.Gamma
