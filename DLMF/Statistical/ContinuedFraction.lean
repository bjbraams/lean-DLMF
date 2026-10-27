/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.TricomiRotated
public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import DLMF.Confluent.IncompleteGamma

/-!
# The continued fraction for `Γ(a,x)` (Temme §11.2.2; DLMF 8.9.2)

For real `a < 1` and `x > 0` this file proves that the convergents of Legendre's continued fraction
`Γ(a,x) = x^a e^{-x}/(x + (1-a)/(1 + 1/(x + (2-a)/(1 + 2/(x + ⋯)))))` converge to `Γ(a,x)`.
All partial numerators and denominators are then positive.

* **Exact tails.** Let `J_m(σ) = ∫₀^∞ t^m (1+t)^σ e^{-xt} dt`. Then `Γ(a,x) = x^a e^{-x} J₀(a-1)`
  (`upperIncGamma_eq_gammaTail`). Integration by parts gives
  `x J_m(σ) = 0^m + m J_{m-1}(σ) + σ J_m(σ-1)`
  (`gammaTail_ibp`), and `(1+t)^σ = (1+t)^{σ-1}(1+t)` gives `J_n(σ) = J_n(σ-1) + J_{n+1}(σ-1)`
  (`gammaTail_split`). Together these provide a positive backward solution `w` of the three-term
  recurrence of the fraction, with `Γ(a,x) = a₀ w₁ / w₀` (Temme's Exercise 11.5 route, without
  Kummer's `U`).
* **General convergence theorem** (`posContFract_tendsto`). For `a₀/(b₀ + a₁/(b₁ + ⋯))` with
  positive elements and a positive backward solution `w`, Pincherle-type invariants and the
  determinant formula bound the error by `∏ a_k / (B_{m+1} B_m)`. Scaling the denominators
  reduces this to the Seidel–Stern growth lemma `tendsto_mul_of_seidelStern`, which needs the
  divergence of `∑ b_k d_k / d_{k+1}`.
* For the `Γ(a,x)` fraction, `d_{2j}/d_{2j+1} ≥ c/(j+1)`, so the divergence follows from the
  harmonic series (`gammaInc_seidelStern_div`).

DLMF states convergence for every complex `a` and `|ph z| < π`. The positive real case proved here
is the one where all elements are positive.
-/

@[expose] public section

open Complex Filter Set MeasureTheory
open scoped Real Topology

noncomputable section

namespace DLMF.Statistical

/-- The tail integrals `∫₀^∞ t^m (1+t)^σ e^{-xt} dt`. -/
def gammaTail (x σ : ℝ) (m : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t ^ m * (1 + t) ^ σ * Real.exp (-x * t)

/-- `(1+t)^σ ≤ (1+t)^{⌈|σ|⌉}` for `t ≥ 0`. -/
theorem one_add_rpow_le_pow {t : ℝ} (ht : 0 ≤ t) (σ : ℝ) :
    (1 + t) ^ σ ≤ (1 + t) ^ (⌈|σ|⌉₊ : ℕ) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith)
    ((le_abs_self σ).trans (Nat.le_ceil _))

/-- The tail integrands are integrable on `(0, ∞)` for `x > 0`. -/
theorem integrableOn_gammaTail {x : ℝ} (hx : 0 < x) (σ : ℝ) (m : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ m * (1 + t) ^ σ * Real.exp (-x * t)) (Ioi 0) := by
  have h := DLMF.Confluent.integrableOn_exp_mul_rpow_mul_one_add_pow (s := (m : ℝ))
    (by have := m.cast_nonneg (α := ℝ); linarith) hx ⌈|σ|⌉₊
  refine h.mono' ?_ ?_
  · have hc : ContinuousOn (fun t : ℝ => t ^ m * (1 + t) ^ σ * Real.exp (-x * t)) (Ioi 0) := by
      refine ContinuousOn.mul (ContinuousOn.mul (continuousOn_pow m) ?_) (by fun_prop)
      exact ContinuousOn.rpow_const (by fun_prop) (fun t ht => Or.inl (by
        have : (0 : ℝ) < t := ht
        linarith))
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_natCast]
    have := one_add_rpow_le_pow ht0.le σ
    have h1 : 0 ≤ t ^ m * Real.exp (-x * t) := by positivity
    nlinarith

/-- The tail integrals are positive. -/
theorem gammaTail_pos {x : ℝ} (hx : 0 < x) (σ : ℝ) (m : ℕ) : 0 < gammaTail x σ m := by
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 < t ^ m * (1 + t) ^ σ * Real.exp (-x * t) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have : 0 < 1 + t := by linarith
    positivity
  rw [gammaTail, setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht =>
      (hpos t ht).le)) (integrableOn_gammaTail hx σ m)]
  have hsub : Ioi (0 : ℝ) ⊆ Function.support
      (fun t : ℝ => t ^ m * (1 + t) ^ σ * Real.exp (-x * t)) ∩ Ioi 0 :=
    fun t ht => ⟨(hpos t ht).ne', ht⟩
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  simp


/-- The boundary term `t^m (1+t)^σ e^{-xt}` vanishes at infinity. -/
theorem tendsto_gammaTail_boundary_atTop {x : ℝ} (hx : 0 < x) (σ : ℝ) (m : ℕ) :
    Tendsto (fun t : ℝ => t ^ m * (1 + t) ^ σ * Real.exp (-x * t)) atTop (𝓝 0) := by
  set N := ⌈|σ|⌉₊
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((m + N : ℕ) : ℝ) x hx).const_mul
    ((2 : ℝ) ^ N)
  rw [mul_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : (0 : ℝ) ≤ t := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_natCast]
  have h1 := one_add_rpow_le_pow ht0 σ
  have h2 : (1 + t) ^ N ≤ (2 * t) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
  rw [mul_pow, pow_add] at *
  have he : 0 ≤ Real.exp (-x * t) := (Real.exp_pos _).le
  have htm : 0 ≤ t ^ m := by positivity
  calc t ^ m * (1 + t) ^ σ * Real.exp (-x * t)
      ≤ t ^ m * (2 ^ N * t ^ N) * Real.exp (-x * t) := by gcongr; exact h1.trans h2
    _ = 2 ^ N * (t ^ m * t ^ N * Real.exp (-x * t)) := by ring

/-- Integration by parts: `x J_m(σ) = 0^m + m J_{m-1}(σ) + σ J_m(σ-1)`. -/
theorem gammaTail_ibp {x : ℝ} (hx : 0 < x) (σ : ℝ) (m : ℕ) :
    x * gammaTail x σ m = (0 : ℝ) ^ m + m * gammaTail x σ (m - 1) + σ * gammaTail x (σ - 1) m := by
  set u : ℝ → ℝ := fun t => t ^ m * (1 + t) ^ σ
  set u' : ℝ → ℝ := fun t => m * t ^ (m - 1) * (1 + t) ^ σ + t ^ m * (σ * (1 + t) ^ (σ - 1))
  set v : ℝ → ℝ := fun t => -(Real.exp (-x * t) / x)
  set v' : ℝ → ℝ := fun t => Real.exp (-x * t)
  have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt u (u' t) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have h1 : HasDerivAt (fun t : ℝ => (1 + t) ^ σ) (σ * (1 + t) ^ (σ - 1)) t := by
      have := ((hasDerivAt_id t).const_add 1).rpow_const (p := σ) (Or.inl (by
        show (1 : ℝ) + id t ≠ 0; simp; linarith))
      simpa using this
    exact (hasDerivAt_pow m t).mul h1
  have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt v (v' t) t := by
    intro t _
    have := ((hasDerivAt_id t).const_mul (-x)).exp.div_const x |>.neg
    refine this.congr_deriv ?_
    simp only [v', id]; field_simp
  have hI1 := integrableOn_gammaTail hx σ m
  have hI2 := integrableOn_gammaTail hx σ (m - 1)
  have hI3 := integrableOn_gammaTail hx (σ - 1) m
  have huv' : IntegrableOn (u * v') (Ioi 0) := by
    refine hI1.congr_fun (fun t _ => ?_) measurableSet_Ioi; simp only [Pi.mul_apply, u, v']
  have hu'v : IntegrableOn (u' * v) (Ioi 0) := by
    have : IntegrableOn (fun t : ℝ => -(1 / x) * ((m : ℝ) * (t ^ (m - 1) * (1 + t) ^ σ *
        Real.exp (-x * t)) + σ * (t ^ m * (1 + t) ^ (σ - 1) * Real.exp (-x * t)))) (Ioi 0) :=
      ((hI2.const_mul (m : ℝ)).add (hI3.const_mul σ)).const_mul (-(1 / x))
    refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, u', v]; field_simp
  have hzero : Tendsto (u * v) (𝓝[>] 0) (𝓝 (-((0 : ℝ) ^ m / x))) := by
    have hc : ContinuousAt (fun t : ℝ => u t * v t) 0 := by
      simp only [u, v]
      refine ContinuousAt.mul (ContinuousAt.mul (continuous_pow m).continuousAt ?_) (by fun_prop)
      exact (Real.continuousAt_rpow_const _ _ (Or.inl (by norm_num))).comp (by fun_prop)
    have h0 : u 0 * v 0 = -((0 : ℝ) ^ m / x) := by simp [u, v, div_eq_mul_inv]
    rw [← h0]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto (u * v) atTop (𝓝 0) := by
    have := (tendsto_gammaTail_boundary_atTop hx σ m).div_const x |>.neg
    simp only [zero_div, neg_zero] at this
    refine this.congr fun t => ?_
    simp only [Pi.mul_apply, u, v]; ring
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hzero hinf
  have hsplit : ∫ t in Ioi (0 : ℝ), u' t * v t =
      -(1 / x) * (m * gammaTail x σ (m - 1) + σ * gammaTail x (σ - 1) m) := by
    rw [gammaTail, gammaTail, ← integral_const_mul, ← integral_const_mul, ← integral_add
      (hI2.const_mul _) (hI3.const_mul _), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [u', v]; field_simp
  rw [hsplit] at hibp
  have hJ : gammaTail x σ m = ∫ t in Ioi (0 : ℝ), u t * v' t := rfl
  rw [hJ, hibp]
  field_simp
  ring


/-- The shift `s = 1 + t` on `(1, ∞)`. -/
theorem integral_Ioi_one_eq_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) : ∫ s in Ioi (1 : ℝ), g s = ∫ t in Ioi (0 : ℝ), g (1 + t) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have h : ∀ t : ℝ, (Ioi (0 : ℝ)).indicator (fun t => g (1 + t)) t =
      (Ioi (1 : ℝ)).indicator g (1 + t) := by
    intro t
    by_cases ht : 0 < t
    · rw [indicator_of_mem (show t ∈ Ioi 0 from ht),
        indicator_of_mem (show 1 + t ∈ Ioi 1 by simp [ht])]
    · rw [indicator_of_notMem (show t ∉ Ioi 0 from ht),
        indicator_of_notMem (show 1 + t ∉ Ioi 1 by simpa using ht)]
  simp_rw [h]
  exact (integral_add_left_eq_self (fun u => (Ioi (1 : ℝ)).indicator g u) 1).symm

/-- `Γ(a,x) = x^a e^{-x} ∫₀^∞ (1+t)^{a-1} e^{-xt} dt` for real `a` and `x > 0`. -/
theorem upperIncGamma_eq_gammaTail (a : ℝ) {x : ℝ} (hx : 0 < x) :
    DLMF.Confluent.upperIncGamma (a : ℂ) (x : ℂ) =
      ((x ^ a * Real.exp (-x) * gammaTail x (a - 1) 0 : ℝ) : ℂ) := by
  rw [DLMF.Confluent.upperIncGamma_eq_cpow_mul_integral_Ioi_one _ hx, integral_Ioi_one_eq_shift,
    gammaTail, ← ofReal_cpow hx.le]
  push_cast
  rw [← integral_complex_ofReal, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  simp only [Complex.real_smul]
  rw [show (1 : ℂ) + t = ((1 + t : ℝ) : ℂ) by push_cast; ring,
    show (a : ℂ) - 1 = ((a - 1 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (by linarith)]
  push_cast
  rw [show -(x : ℂ) * (1 + t) = -x + -x * t by ring, Complex.exp_add]
  ring


/-! ### Positive continued fractions -/

/-- The continued fraction `a₀/(b₀ + a₁/(b₁ + ⋯))` with zero integer part. -/
def posContFract (a b : ℕ → ℝ) : GenContFract ℝ where
  h := 0
  s := Stream'.Seq.ofStream fun k => ⟨a k, b k⟩

/-- `A₀ = 0`. -/
theorem posContFract_nums_zero (a b : ℕ → ℝ) : (posContFract a b).nums 0 = 0 := rfl
/-- `B₀ = 1`. -/
theorem posContFract_dens_zero (a b : ℕ → ℝ) : (posContFract a b).dens 0 = 1 :=
  GenContFract.zeroth_den_eq_one

/-- `A₁ = a₀`. -/
theorem posContFract_nums_one (a b : ℕ → ℝ) : (posContFract a b).nums 1 = a 0 := by
  rw [GenContFract.first_num_eq (g := posContFract a b) (gp := ⟨a 0, b 0⟩) rfl]
  simp [posContFract]

/-- `B₁ = b₀`. -/
theorem posContFract_dens_one (a b : ℕ → ℝ) : (posContFract a b).dens 1 = b 0 :=
  GenContFract.first_den_eq (g := posContFract a b) (gp := ⟨a 0, b 0⟩) rfl

/-- The numerator recurrence. -/
theorem posContFract_nums_step (a b : ℕ → ℝ) (n : ℕ) :
    (posContFract a b).nums (n + 2) =
      b (n + 1) * (posContFract a b).nums (n + 1) + a (n + 1) * (posContFract a b).nums n :=
  GenContFract.nums_recurrence (g := posContFract a b) (n := n)
    (gp := ⟨a (n + 1), b (n + 1)⟩) rfl rfl rfl

/-- The denominator recurrence. -/
theorem posContFract_dens_step (a b : ℕ → ℝ) (n : ℕ) :
    (posContFract a b).dens (n + 2) =
      b (n + 1) * (posContFract a b).dens (n + 1) + a (n + 1) * (posContFract a b).dens n :=
  GenContFract.dens_recurrence (g := posContFract a b) (n := n)
    (gp := ⟨a (n + 1), b (n + 1)⟩) rfl rfl rfl


section General

variable {a b w : ℕ → ℝ}


/-- Pincherle-type invariants: a backward solution `w` of the recurrence pairs with the
numerators and denominators. -/
theorem posContFract_invariant (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2))
    (m : ℕ) :
    (posContFract a b).nums (m + 1) * w (m + 1) +
        a (m + 1) * (posContFract a b).nums m * w (m + 2) = a 0 * w 1 ∧
      (posContFract a b).dens (m + 1) * w (m + 1) +
        a (m + 1) * (posContFract a b).dens m * w (m + 2) = w 0 := by
  induction m with
  | zero =>
    rw [posContFract_nums_one, posContFract_nums_zero, posContFract_dens_one,
      posContFract_dens_zero, hw 0]
    constructor <;> ring
  | succ m ih =>
    rw [posContFract_nums_step, posContFract_dens_step]
    constructor
    · rw [← ih.1, hw (m + 1)]; ring
    · rw [← ih.2, hw (m + 1)]; ring

/-- The determinant formula `N_{m+1} D_m - D_{m+1} N_m = (-1)^m ∏_{k ≤ m} a_k`. -/
theorem posContFract_det (m : ℕ) :
    (posContFract a b).nums (m + 1) * (posContFract a b).dens m -
        (posContFract a b).dens (m + 1) * (posContFract a b).nums m =
      (-1) ^ m * ∏ k ∈ Finset.range (m + 1), a k := by
  induction m with
  | zero =>
    rw [posContFract_nums_one, posContFract_nums_zero, posContFract_dens_one,
      posContFract_dens_zero]
    simp
  | succ m ih =>
    rw [posContFract_nums_step, posContFract_dens_step, Finset.prod_range_succ]
    linear_combination (-a (m + 1)) * ih

/-- With positive elements the denominators are positive. -/
theorem posContFract_dens_pos (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k) (m : ℕ) :
    0 < (posContFract a b).dens m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · rw [posContFract_dens_zero]; norm_num
    · rw [posContFract_dens_one]; exact hb 0
    · rw [posContFract_dens_step]
      have := ih (m + 1) (by omega)
      have := ih m (by omega)
      have := ha (m + 1)
      have := hb (m + 1)
      positivity

/-- The error of the `(m+1)`-st convergent is at most `∏_{k ≤ m} a_k / (D_{m+1} D_m)`. -/
theorem posContFract_error (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k) (hwpos : ∀ k, 0 < w k)
    (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2)) (m : ℕ) :
    |a 0 * w 1 / w 0 - (posContFract a b).nums (m + 1) / (posContFract a b).dens (m + 1)| ≤
      (∏ k ∈ Finset.range (m + 1), a k) /
        ((posContFract a b).dens (m + 1) * (posContFract a b).dens m) := by
  obtain ⟨h1, h2⟩ := posContFract_invariant hw m
  have hdet := posContFract_det (a := a) (b := b) m
  have hD1 := posContFract_dens_pos ha hb (m + 1)
  have hD0 := posContFract_dens_pos ha hb m
  have hw0 := hwpos 0
  have hP : 0 < ∏ k ∈ Finset.range (m + 1), a k := Finset.prod_pos fun k _ => ha k
  -- the exact error
  have herr : a 0 * w 1 / w 0 - (posContFract a b).nums (m + 1) / (posContFract a b).dens (m + 1) =
      -(a (m + 1) * w (m + 2) * ((-1) ^ m * ∏ k ∈ Finset.range (m + 1), a k)) /
        (w 0 * (posContFract a b).dens (m + 1)) := by
    rw [← hdet]
    field_simp
    linear_combination -((posContFract a b).dens (m + 1)) * h1 +
      (posContFract a b).nums (m + 1) * h2
  have hbound : a (m + 1) * w (m + 2) ≤ w 0 / (posContFract a b).dens m := by
    rw [le_div_iff₀ hD0]
    have := mul_pos (posContFract_dens_pos ha hb (m + 1)) (hwpos (m + 1))
    nlinarith
  have habs : |(-1 : ℝ) ^ m * ∏ k ∈ Finset.range (m + 1), a k| =
      ∏ k ∈ Finset.range (m + 1), a k := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hP]
  rw [herr, abs_div, abs_neg, abs_mul, abs_mul, habs, abs_of_pos (ha _), abs_of_pos (hwpos _),
    abs_of_pos (mul_pos hw0 hD1)]
  rw [div_le_div_iff₀ (mul_pos hw0 hD1) (mul_pos hD1 hD0)]
  have := mul_le_mul_of_nonneg_right hbound hP.le
  rw [div_mul_eq_mul_div, le_div_iff₀ hD0] at this
  nlinarith

/-- **Seidel–Stern growth**: if `q_{n+2} = β_{n+1} q_{n+1} + q_n` with `β ≥ 0`, `q₀, q₁ > 0` and
`∑ βₙ = ∞`, then `q_{n+1} q_n → ∞`. -/
theorem tendsto_mul_of_seidelStern {q β : ℕ → ℝ} (hβ : ∀ n, 0 ≤ β n) (hq0 : 0 < q 0)
    (hq1 : 0 < q 1) (hrec : ∀ n, q (n + 2) = β (n + 1) * q (n + 1) + q n)
    (hdiv : Tendsto (fun n => ∑ k ∈ Finset.range n, β k) atTop atTop) :
    Tendsto (fun n => q (n + 1) * q n) atTop atTop := by
  set c := min (q 0) (q 1)
  have hc : 0 < c := lt_min hq0 hq1
  have hlow : ∀ n, c ≤ q n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | _ | n
      · exact min_le_left _ _
      · exact min_le_right _ _
      · rw [hrec]
        have h1 := ih (n + 1) (by omega)
        have h2 := ih n (by omega)
        have := mul_nonneg (hβ (n + 1)) (hc.le.trans h1)
        linarith
  have hsum : ∀ n, c * (∑ k ∈ Finset.range (n + 1), β k - β 0) ≤ q (n + 1) + q n := by
    intro n
    induction n with
    | zero => simp; linarith [hlow 0, hlow 1]
    | succ n ih =>
      rw [Finset.sum_range_succ, hrec]
      have := mul_le_mul_of_nonneg_left (hlow (n + 1)) (hβ (n + 1))
      nlinarith
  have hprod : ∀ n, c / 2 * (c * (∑ k ∈ Finset.range (n + 1), β k - β 0)) ≤ q (n + 1) * q n := by
    intro n
    have h1 := hlow n
    have h2 := hlow (n + 1)
    have h3 := hsum n
    rcases le_total (q n) (q (n + 1)) with h | h
    · nlinarith
    · nlinarith
  refine tendsto_atTop_mono hprod ?_
  refine Tendsto.const_mul_atTop (by positivity) (Tendsto.const_mul_atTop hc ?_)
  exact tendsto_atTop_add_const_right _ _ ((hdiv.comp (tendsto_add_atTop_nat 1)))

/-- The scaling `d₀ = 1`, `d₁ = a₀`, `d_{n+2} = a_{n+1} d_n` that normalizes the continuants. -/
def cfScale (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => a 0
  | n + 2 => a (n + 1) * cfScale a n

/-- The scaling is positive for positive partial numerators. -/
theorem cfScale_pos (ha : ∀ k, 0 < a k) (n : ℕ) : 0 < cfScale a n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [cfScale]
    · exact ha 0
    · have := ih n (by omega); have := ha (n + 1); simp only [cfScale]; positivity

/-- `d_{m+1} d_m = ∏_{k ≤ m} a_k`. -/
theorem cfScale_mul (a : ℕ → ℝ) (m : ℕ) :
    cfScale a (m + 1) * cfScale a m = ∏ k ∈ Finset.range (m + 1), a k := by
  induction m with
  | zero => simp [cfScale]
  | succ m ih => rw [Finset.prod_range_succ, ← ih]; simp only [cfScale]; ring

/-- **Convergence of positive continued fractions** with a positive backward solution `w`:
if `∑ bₙ dₙ/d_{n+1} = ∞` the convergents tend to `a₀ w₁ / w₀`. -/
theorem posContFract_tendsto (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k) (hwpos : ∀ k, 0 < w k)
    (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2))
    (hdiv : Tendsto (fun n => ∑ k ∈ Finset.range n, b k * cfScale a k / cfScale a (k + 1))
      atTop atTop) :
    Tendsto (posContFract a b).convs atTop (𝓝 (a 0 * w 1 / w 0)) := by
  set q : ℕ → ℝ := fun n => (posContFract a b).dens n / cfScale a n
  have hq : ∀ n, 0 < q n := fun n =>
    div_pos (posContFract_dens_pos ha hb n) (cfScale_pos ha n)
  have hrec : ∀ n, q (n + 2) = b (n + 1) * cfScale a (n + 1) / cfScale a (n + 2) * q (n + 1) +
      q n := by
    intro n
    have h1 := cfScale_pos ha n
    have h2 := cfScale_pos ha (n + 1)
    have h3 := ha (n + 1)
    simp only [q]
    rw [posContFract_dens_step, show cfScale a (n + 2) = a (n + 1) * cfScale a n from rfl]
    field_simp
  have hgrow := tendsto_mul_of_seidelStern (q := q)
    (fun n => (div_pos (mul_pos (hb n) (cfScale_pos ha n)) (cfScale_pos ha (n + 1))).le)
    (hq 0) (hq 1) hrec hdiv
  have hinv : Tendsto (fun n => 1 / (q (n + 1) * q n)) atTop (𝓝 0) := by
    refine hgrow.inv_tendsto_atTop.congr fun n => ?_
    simp [one_div]
  show Tendsto (fun n => (posContFract a b).convs n) atTop _
  rw [← tendsto_add_atTop_iff_nat 1]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hinv
  have herr := posContFract_error ha hb hwpos hw n
  rw [Real.norm_eq_abs, abs_sub_comm]
  have hconv : (posContFract a b).convs (n + 1) =
      (posContFract a b).nums (n + 1) / (posContFract a b).dens (n + 1) := rfl
  rw [hconv]
  refine herr.trans (le_of_eq ?_)
  have h1 := cfScale_pos ha n
  have h2 := cfScale_pos ha (n + 1)
  have hD1 := posContFract_dens_pos ha hb (n + 1)
  have hD0 := posContFract_dens_pos ha hb n
  rw [← cfScale_mul]
  simp only [q]
  field_simp

end General

/-! ### The continued fraction for `Γ(a,x)` -/

/-- `J_n(σ) = J_n(σ-1) + J_{n+1}(σ-1)`, from `(1+t)^σ = (1+t)^{σ-1}(1+t)`. -/
theorem gammaTail_split {x : ℝ} (hx : 0 < x) (σ : ℝ) (n : ℕ) :
    gammaTail x σ n = gammaTail x (σ - 1) n + gammaTail x (σ - 1) (n + 1) := by
  rw [gammaTail, gammaTail, gammaTail, ← integral_add (integrableOn_gammaTail hx _ _)
    (integrableOn_gammaTail hx _ _)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  have h1 : (1 + t) ^ σ = (1 + t) ^ (σ - 1) * (1 + t) := by
    rw [Real.rpow_sub_one (by linarith)]; field_simp
  rw [h1]; ring

/-- Partial numerators of DLMF 8.9.2: `x^a e^{-x}, 1-a, 1, 2-a, 2, 3-a, 3, …`. -/
def gammaIncCFNum (α x : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then x ^ α * Real.exp (-x)
  else if k % 2 = 1 then ((k / 2 : ℕ) : ℝ) + 1 - α else ((k / 2 : ℕ) : ℝ)

/-- Partial denominators of DLMF 8.9.2: `x, 1, x, 1, …`. -/
def gammaIncCFDen (x : ℝ) (k : ℕ) : ℝ := if k % 2 = 0 then x else 1

/-- The continued fraction
`Γ(a,x) = x^a e^{-x}/(x + (1-a)/(1 + 1/(x + (2-a)/(1 + 2/(x + ⋯)))))` (DLMF 8.9.2). -/
def gammaIncContFract (α x : ℝ) : GenContFract ℝ :=
  posContFract (gammaIncCFNum α x) (gammaIncCFDen x)

/-- The backward solution: `1, J₀(a-1), J₀(a-2), J₁(a-2)/1!, J₁(a-3)/1!, …`. -/
def gammaIncCFTail (α x : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => if k % 2 = 0 then gammaTail x (α - 1 - (k / 2 : ℕ)) (k / 2) / (k / 2).factorial
      else gammaTail x (α - 2 - (k / 2 : ℕ)) (k / 2) / (k / 2).factorial

/-- The backward solution is positive. -/
theorem gammaIncCFTail_pos {α x : ℝ} (hx : 0 < x) (k : ℕ) : 0 < gammaIncCFTail α x k := by
  rcases k with _ | k
  · simp [gammaIncCFTail]
  · simp only [gammaIncCFTail]
    have := Nat.factorial_pos (k / 2)
    split_ifs <;> exact div_pos (gammaTail_pos hx _ _) (by exact_mod_cast this)

/-- `w_{2n+1} = J_n(a-1-n)/n!`. -/
theorem gammaIncCFTail_even (α x : ℝ) (n : ℕ) :
    gammaIncCFTail α x (2 * n + 1) = gammaTail x (α - 1 - n) n / n.factorial := by
  simp only [gammaIncCFTail]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), show 2 * n / 2 = n by omega]

/-- `w_{2n+2} = J_n(a-2-n)/n!`. -/
theorem gammaIncCFTail_odd (α x : ℝ) (n : ℕ) :
    gammaIncCFTail α x (2 * n + 2) = gammaTail x (α - 2 - n) n / n.factorial := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by ring]
  simp only [gammaIncCFTail]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), show (2 * n + 1) / 2 = n by omega]

/-- `a_{2n+1} = n+1-a`. -/
theorem gammaIncCFNum_odd (α x : ℝ) (n : ℕ) : gammaIncCFNum α x (2 * n + 1) = n + 1 - α := by
  simp only [gammaIncCFNum]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_left_of_eq_true _ _ (eq_true (by omega)), show (2 * n + 1) / 2 = n by omega]

/-- `a_{2n+2} = n+1`. -/
theorem gammaIncCFNum_even (α x : ℝ) (n : ℕ) : gammaIncCFNum α x (2 * n + 2) = n + 1 := by
  simp only [gammaIncCFNum]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega)), show (2 * n + 2) / 2 = n + 1 by omega]
  push_cast; ring

/-- `b_{2n} = x`. -/
theorem gammaIncCFDen_even (x : ℝ) (n : ℕ) : gammaIncCFDen x (2 * n) = x := by
  simp only [gammaIncCFDen]; rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]

/-- `b_{2n+1} = 1`. -/
theorem gammaIncCFDen_odd (x : ℝ) (n : ℕ) : gammaIncCFDen x (2 * n + 1) = 1 := by
  simp only [gammaIncCFDen]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- The backward recurrence `w_k = b_k w_{k+1} + a_{k+1} w_{k+2}`, from integration by parts
and `(1+t)^σ = (1+t)^{σ-1}(1+t)`. -/
theorem gammaIncCFTail_rec {α x : ℝ} (hx : 0 < x) (k : ℕ) :
    gammaIncCFTail α x k = gammaIncCFDen x k * gammaIncCFTail α x (k + 1) +
      gammaIncCFNum α x (k + 1) * gammaIncCFTail α x (k + 2) := by
  rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
  · rcases n with _ | m
    · -- `1 = x J₀(a-1) + (1-a) J₀(a-2)`
      have h := gammaTail_ibp hx (α - 1) 0
      have h1 := gammaIncCFTail_even α x 0
      have h2 := gammaIncCFTail_odd α x 0
      have h3 := gammaIncCFNum_odd α x 0
      have h4 := gammaIncCFDen_even x 0
      simp only [mul_zero, zero_add] at h1 h2 h3 h4 ⊢
      rw [h1, h2, h3, h4]
      simp only [gammaIncCFTail]
      norm_num at h ⊢
      rw [show α - 1 - 1 = α - 2 by ring] at h
      linarith
    · -- `k = 2m+2`: `(m+1) B_m = x A_{m+1} + (m+2-a) B_{m+1}`
      have h := gammaTail_ibp hx (α - 2 - m) (m + 1)
      rw [gammaIncCFTail_odd α x (m + 1), gammaIncCFTail_even α x (m + 1), gammaIncCFNum_odd,
        gammaIncCFDen_even, show 2 * (m + 1) = 2 * m + 2 by ring, gammaIncCFTail_odd]
      rw [show (m + 1) - 1 = m by omega, pow_succ, mul_zero, zero_add] at h
      rw [Nat.factorial_succ]
      push_cast at h ⊢
      have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
      rw [show α - 1 - (m + 1) = α - 2 - m by ring, show α - 2 - (m + 1) = α - 2 - m - 1 by ring]
      field_simp
      linear_combination -h
  · -- `k = 2n+1`: `A_n = B_n + A_{n+1}`
    have h := gammaTail_split hx (α - 1 - n) n
    rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring, show 2 * n + 1 + 2 = 2 * (n + 1) + 1 by ring,
      gammaIncCFTail_even, gammaIncCFTail_odd, gammaIncCFTail_even, gammaIncCFNum_even,
      gammaIncCFDen_odd, Nat.factorial_succ]
    push_cast
    rw [show α - 1 - (n + 1) = α - 1 - n - 1 by ring, show α - 2 - n = α - 1 - n - 1 by ring]
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    field_simp
    linear_combination h

/-- The partial numerators are positive for `a < 1`, `x > 0`. -/
theorem gammaIncCFNum_pos {α x : ℝ} (hα : α < 1) (hx : 0 < x) (k : ℕ) : 0 < gammaIncCFNum α x k := by
  simp only [gammaIncCFNum]
  split_ifs with h0 h1
  · positivity
  · have := (k / 2 : ℕ).cast_nonneg (α := ℝ); linarith
  · have : 0 < k / 2 := by omega
    exact_mod_cast this

/-- The partial denominators are positive. -/
theorem gammaIncCFDen_pos {x : ℝ} (hx : 0 < x) (k : ℕ) : 0 < gammaIncCFDen x k := by
  simp only [gammaIncCFDen]; split_ifs <;> linarith

/-- `d_{2j} = ∏_{i<j} (i+1-a)`. -/
theorem cfScale_gammaInc_even (α x : ℝ) (j : ℕ) :
    cfScale (gammaIncCFNum α x) (2 * j) = ∏ i ∈ Finset.range j, ((i : ℝ) + 1 - α) := by
  induction j with
  | zero => simp [cfScale]
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, show cfScale (gammaIncCFNum α x) (2 * j + 2) =
      gammaIncCFNum α x (2 * j + 1) * cfScale (gammaIncCFNum α x) (2 * j) from rfl, ih,
      gammaIncCFNum_odd, Finset.prod_range_succ]
    ring

/-- `d_{2j+1} = x^a e^{-x} j!`. -/
theorem cfScale_gammaInc_odd (α x : ℝ) (j : ℕ) :
    cfScale (gammaIncCFNum α x) (2 * j + 1) = x ^ α * Real.exp (-x) * j.factorial := by
  induction j with
  | zero => simp [cfScale, gammaIncCFNum]
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring, show cfScale (gammaIncCFNum α x)
      (2 * j + 1 + 2) = gammaIncCFNum α x (2 * j + 2) * cfScale (gammaIncCFNum α x) (2 * j + 1)
      from rfl, ih, gammaIncCFNum_even, Nat.factorial_succ]
    push_cast; ring

/-- `∏_{i<j} (i+1-a)/(i+1) ≥ (1-a)/j` for `a ≤ 1`, `j ≥ 1`. -/
theorem prod_ratio_ge {α : ℝ} (hα : α ≤ 1) (j : ℕ) :
    (1 - α) / (j + 1) ≤ (∏ i ∈ Finset.range (j + 1), ((i : ℝ) + 1 - α)) / (j + 1).factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.prod_range_succ, Nat.factorial_succ]
    push_cast
    have hj : (0 : ℝ) < j + 1 := by positivity
    have hP : 0 ≤ (∏ i ∈ Finset.range (j + 1), ((i : ℝ) + 1 - α)) / (j + 1).factorial := by
      linarith [div_nonneg (by linarith : (0 : ℝ) ≤ 1 - α) hj.le]
    have hf : (0 : ℝ) < (j + 1).factorial := by exact_mod_cast Nat.factorial_pos _
    have hq : 0 < ((j : ℝ) + 1 + 1 - α) := by linarith
    calc (1 - α) / ((j : ℝ) + 1 + 1)
        ≤ (1 - α) / (j + 1) * (((j : ℝ) + 1 + 1 - α) / (j + 1 + 1)) := by
          rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
          have h0 : (0 : ℝ) ≤ 1 - α := by linarith
          nlinarith [mul_nonneg (mul_nonneg h0 h0) (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1 + 1)]
      _ ≤ (∏ i ∈ Finset.range (j + 1), ((i : ℝ) + 1 - α)) / (j + 1).factorial *
          (((j : ℝ) + 1 + 1 - α) / (j + 1 + 1)) := by gcongr
      _ = _ := by field_simp

/-- The Seidel–Stern series of the `Γ(a,x)` fraction diverges. -/
theorem gammaInc_seidelStern_div {α x : ℝ} (hα : α < 1) (hx : 0 < x) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, gammaIncCFDen x k *
      cfScale (gammaIncCFNum α x) k / cfScale (gammaIncCFNum α x) (k + 1)) atTop atTop := by
  set β : ℕ → ℝ := fun k => gammaIncCFDen x k * cfScale (gammaIncCFNum α x) k /
    cfScale (gammaIncCFNum α x) (k + 1)
  have hβ : ∀ k, 0 ≤ β k := fun k => (div_pos (mul_pos (gammaIncCFDen_pos hx k)
    (cfScale_pos (gammaIncCFNum_pos hα hx) k)) (cfScale_pos (gammaIncCFNum_pos hα hx) (k + 1))).le
  set c₀ := x ^ α * Real.exp (-x)
  have hc₀ : 0 < c₀ := by positivity
  set κ := min 1 (1 - α)
  have hκ : 0 < κ := lt_min one_pos (by linarith)
  -- even terms are at least `x κ / (c₀ (j+1))`
  have heven : ∀ j : ℕ, x * κ / c₀ * (1 / ((j : ℝ) + 1)) ≤ β (2 * j) := by
    intro j
    simp only [β]
    rw [gammaIncCFDen_even, cfScale_gammaInc_even, cfScale_gammaInc_odd]
    have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos _
    have hr : κ / ((j : ℝ) + 1) ≤ (∏ i ∈ Finset.range j, ((i : ℝ) + 1 - α)) / j.factorial := by
      rcases j with _ | j
      · simp; exact min_le_left _ _
      · have := prod_ratio_ge hα.le j
        push_cast at this ⊢
        refine le_trans ?_ this
        have h1 : κ ≤ 1 - α := min_le_right _ _
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    calc x * κ / c₀ * (1 / ((j : ℝ) + 1)) = x / c₀ * (κ / ((j : ℝ) + 1)) := by ring
      _ ≤ x / c₀ * ((∏ i ∈ Finset.range j, ((i : ℝ) + 1 - α)) / j.factorial) := by gcongr
      _ = _ := by field_simp; simp only [c₀]; ring
  have hpair : ∀ N, ∑ j ∈ Finset.range N, β (2 * j) ≤ ∑ k ∈ Finset.range (2 * N), β k := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, show 2 * (N + 1) = 2 * N + 1 + 1 by ring,
        Finset.sum_range_succ, Finset.sum_range_succ]
      linarith [hβ (2 * N + 1)]
  have hharm := (Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop
    (show 0 < x * κ / c₀ by positivity))
  rw [tendsto_atTop_atTop] at hharm ⊢
  intro M
  obtain ⟨N, hN⟩ := hharm M
  refine ⟨2 * N, fun n hn => ?_⟩
  have h1 := hN N le_rfl
  rw [Finset.mul_sum] at h1
  have h2 : ∑ i ∈ Finset.range N, x * κ / c₀ * (1 / ((i : ℝ) + 1)) ≤
      ∑ j ∈ Finset.range N, β (2 * j) := Finset.sum_le_sum fun j _ => heven j
  have h3 : ∑ k ∈ Finset.range (2 * N), β k ≤ ∑ k ∈ Finset.range n, β k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) fun k _ _ => hβ k
  linarith [hpair N]

/-- **The continued fraction for `Γ(a,x)`** (DLMF 8.9.2, Temme (11.19)): for real `a < 1` and
`x > 0`, the convergents of
`x^a e^{-x}/(x + (1-a)/(1 + 1/(x + (2-a)/(1 + 2/(x + ⋯)))))` converge to `Γ(a,x)`. -/
@[dlmf 8.9.E2]
theorem tendsto_gammaIncContFract {α x : ℝ} (hα : α < 1) (hx : 0 < x) :
    Tendsto (gammaIncContFract α x).convs atTop (𝓝 (DLMF.Confluent.upperIncGamma α x).re) := by
  have h := posContFract_tendsto (gammaIncCFNum_pos hα hx) (gammaIncCFDen_pos hx)
    (gammaIncCFTail_pos (α := α) hx) (gammaIncCFTail_rec hx) (gammaInc_seidelStern_div hα hx)
  have hval : gammaIncCFNum α x 0 * gammaIncCFTail α x 1 / gammaIncCFTail α x 0 =
      (DLMF.Confluent.upperIncGamma α x).re := by
    rw [upperIncGamma_eq_gammaTail α hx, ofReal_re]
    have h1 := gammaIncCFTail_even α x 0
    simp only [mul_zero, zero_add] at h1
    rw [h1]
    simp [gammaIncCFNum, gammaIncCFTail]
  rw [← hval]
  exact h

end DLMF.Statistical

end
