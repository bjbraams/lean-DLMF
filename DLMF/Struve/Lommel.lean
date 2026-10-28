/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.Basic
public import DLMF.Bessel.Elementary
public import DLMF.Bessel.NeumannSeries
public import DLMF.Gamma.Simplex.GammaPochhammer

/-!
# Lommel functions and parameter continuation

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.

The small-Lommel equation and general solution reuse the proved regularized
`₁F₂` forcing and the all-order Bessel fundamental system in `DLMF.Struve.Basic`.
The parameter-continuation obligations for capital Lommel remain separate.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Struve

open DLMF.Bessel

/-- The finite product of the first `k` factors `(μ+2j+1)²-ν²` in the Lommel series denominator. -/
@[dlmf 11.9.E4]
def lommelA (μ ν : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range k, ((μ+2*j+1)^2-ν^2)

/-- Nonexceptional parameters of the small Lommel function. -/
def LommelRegular (μ ν : ℂ) : Prop :=
  ∀ n : ℕ, μ-ν ≠ -(2*n+1) ∧ μ+ν ≠ -(2*n+1)

/-- The totalized Lommel series `z^(μ+1) Σ (-1)^k z^(2k)/A(μ,ν,k+1)` on the principal power
branch. -/
@[dlmf 11.9.E3]
def lommelS (μ ν z : ℂ) : ℂ :=
  z^(μ+1) * ∑' k : ℕ, (-1)^k*z^(2*k)/lommelA μ ν (k+1)

/-- The regular-parameter capital Lommel solution obtained by adding the prescribed Gamma-weighted
J and Y connection terms to the Lommel series. -/
@[dlmf 11.9.E5]
def lommelCapitalRegular (μ ν z : ℂ) : ℂ :=
  lommelS μ ν z + 2^(μ-1)*Gamma ((μ+ν+1)/2)*Gamma ((μ-ν+1)/2)*(sin ((μ-ν)*π/2)*besselJ ν z-cos ((μ-ν)*π/2)*besselY ν z)

/-- The regular capital Lommel function is even in the order `ν`, for every parameter. -/
theorem lommelCapitalRegular_neg_order (μ ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    lommelCapitalRegular μ (-ν) z = lommelCapitalRegular μ ν z := by
  have hA : ∀ k, lommelA μ (-ν) k = lommelA μ ν k := fun k => by simp [lommelA]
  have hS : lommelS μ (-ν) z = lommelS μ ν z := by simp only [lommelS, hA]
  unfold lommelCapitalRegular
  rw [hS, besselJ_neg_eq ν hz, besselY_neg ν hz]
  have e1 : (μ+-ν+1)/2 = (μ-ν+1)/2 := by ring
  have e2 : (μ- -ν+1)/2 = (μ+ν+1)/2 := by ring
  have e3 : (μ- -ν)*π/2 = (μ-ν)*π/2 + ν*π := by ring
  rw [e1, e2, e3, sin_add, cos_add]
  linear_combination (2^(μ-1)*Gamma ((μ-ν+1)/2)*Gamma ((μ+ν+1)/2)*
    (sin ((μ-ν)*π/2)*besselJ ν z-cos ((μ-ν)*π/2)*besselY ν z))*sin_sq_add_cos_sq (ν*π)

/-- Removable parameter continuation of the capital Lommel function, including exceptional parameters. -/
def lommelCapital (μ ν z : ℂ) : ℂ :=
  limUnder (𝓝[≠] μ) (fun m => lommelCapitalRegular m ν z)

/-- Finitely many positive reals have a common positive lower bound. -/
theorem exists_pos_le_of_lt_nat (g : ℕ → ℝ) (J : ℕ) (hg : ∀ j < J, 0 < g j) :
    ∃ ε > 0, ∀ j < J, ε ≤ g j := by
  induction J with
  | zero => exact ⟨1, one_pos, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ J ih =>
    obtain ⟨ε, hε, hle⟩ := ih fun j hj => hg j (by omega)
    refine ⟨min ε (g J), lt_min hε (hg J (by omega)), fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · exact (min_le_left _ _).trans (hle j h)
    · exact min_le_right _ _

/-- Uniform linear lower bound for the factors of `lommelA` near a regular parameter. -/
theorem lommelA_factor_bound {μ ν : ℂ} (h : LommelRegular μ ν) :
    ∃ δ > 0, ∃ η > 0, ∀ m : ℂ, ‖m - μ‖ < δ → ∀ j : ℕ,
      η*(j+1) ≤ ‖m+2*j+1-ν‖ ∧ η*(j+1) ≤ ‖m+2*j+1+ν‖ := by
  set C : ℝ := ‖μ-ν‖ + ‖μ+ν‖ + 2
  obtain ⟨J, hJ⟩ := exists_nat_ge C
  have hpos : ∀ j < J, 0 < min ‖μ+2*j+1-ν‖ ‖μ+2*j+1+ν‖ := by
    intro j _
    apply lt_min
    · refine norm_pos_iff.2 fun h0 => (h j).1 ?_
      linear_combination h0
    · refine norm_pos_iff.2 fun h0 => (h j).2 ?_
      linear_combination h0
  obtain ⟨ε, hε, hle⟩ := exists_pos_le_of_lt_nat _ J hpos
  refine ⟨min 1 (ε/2), lt_min one_pos (by positivity), min 1 (ε/(2*(J+1))),
    lt_min one_pos (by positivity), fun m hm j => ?_⟩
  have hm1 : ‖m - μ‖ < 1 := lt_of_lt_of_le hm (min_le_left _ _)
  have hm2 : ‖m - μ‖ < ε/2 := lt_of_lt_of_le hm (min_le_right _ _)
  have hη1 : min 1 (ε/(2*(J+1))) ≤ 1 := min_le_left _ _
  have hη2 : min 1 (ε/(2*(J+1))) ≤ ε/(2*(J+1)) := min_le_right _ _
  have hη0 : 0 ≤ min 1 (ε/(2*(J+1))) := (lt_min one_pos (by positivity)).le
  -- generic estimate for both signs
  have key : ∀ σ : ℂ, (‖μ+σ‖ ≤ ‖μ-ν‖ + ‖μ+ν‖) → (∀ j < J, ε ≤ ‖μ+2*j+1+σ‖) →
      min 1 (ε/(2*(J+1))) * (j+1) ≤ ‖m+2*j+1+σ‖ := by
    intro σ hσ hsm
    have htri : ‖μ+2*j+1+σ‖ - ‖m-μ‖ ≤ ‖m+2*j+1+σ‖ := by
      have := norm_sub_norm_le (μ+2*j+1+σ) (μ - m)
      rw [show μ+2*j+1+σ - (μ-m) = m+2*j+1+σ by ring, norm_sub_rev] at this
      linarith
    by_cases hj : j < J
    · have h1 := hsm j hj
      have hjJ : (j:ℝ) < J := by exact_mod_cast hj
      have hJ1 : (j:ℝ)+1 ≤ J+1 := by linarith
      calc min 1 (ε/(2*(J+1))) * (j+1) ≤ ε/(2*(J+1)) * (J+1) :=
            mul_le_mul hη2 hJ1 (by positivity) (by positivity)
        _ = ε/2 := by field_simp
        _ ≤ ‖m+2*j+1+σ‖ := by linarith
    · push Not at hj
      have hjC : C ≤ j := hJ.trans (by exact_mod_cast hj)
      have h2 : ((2*j+1:ℝ)) - ‖μ+σ‖ ≤ ‖μ+2*j+1+σ‖ := by
        have := norm_sub_norm_le ((2*j+1:ℝ):ℂ) (-(μ+σ))
        rw [show ((2*j+1:ℝ):ℂ) - -(μ+σ) = μ+2*j+1+σ by push_cast; ring, norm_neg,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)] at this
        linarith
      have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
      calc min 1 (ε/(2*(J+1))) * (j+1) ≤ 1 * (j+1) := by gcongr
        _ ≤ ‖m+2*j+1+σ‖ := by simp only [C] at hjC; linarith
  constructor
  · have := key (-ν) (by rw [← sub_eq_add_neg]; linarith [norm_nonneg (μ+ν)])
      (fun j hj => by rw [← sub_eq_add_neg]; exact (hle j hj).trans (min_le_left _ _))
    rwa [← sub_eq_add_neg] at this
  · exact key ν (by linarith [norm_nonneg (μ-ν)]) (fun j hj => (hle j hj).trans (min_le_right _ _))

/-- Estimate under the stated parameter and domain assumptions: `η^(2*k) * ((k ! : ℝ))^2 ≤
‖lommelA m ν k‖`. -/
theorem norm_lommelA_ge {m ν : ℂ} {η : ℝ} (hη : 0 < η)
    (hb : ∀ j : ℕ, η*(j+1) ≤ ‖m+2*j+1-ν‖ ∧ η*(j+1) ≤ ‖m+2*j+1+ν‖) (k : ℕ) :
    η^(2*k) * ((k ! : ℝ))^2 ≤ ‖lommelA m ν k‖ := by
  induction k with
  | zero => simp [lommelA]
  | succ k ih =>
    have he : lommelA m ν (k+1) = lommelA m ν k * ((m+2*k+1-ν)*(m+2*k+1+ν)) := by
      simp only [lommelA, Finset.prod_range_succ]; ring
    rw [he, norm_mul, norm_mul, Nat.factorial_succ]
    obtain ⟨h1, h2⟩ := hb k
    have hp : 0 ≤ η*(k+1) := by positivity
    calc η^(2*(k+1)) * (((k+1)*k ! : ℕ) : ℝ)^2 =
        (η^(2*k) * ((k ! : ℝ))^2) * ((η*(k+1)) * (η*(k+1))) := by push_cast; ring
      _ ≤ ‖lommelA m ν k‖ * (‖m+2*k+1-ν‖ * ‖m+2*k+1+ν‖) := by
        gcongr

/-- The Lommel series is continuous in `μ` at regular parameters. -/
theorem continuousAt_lommelSeries {μ ν : ℂ} (h : LommelRegular μ ν) (z : ℂ) :
    ContinuousAt (fun m => ∑' k : ℕ, (-1)^k*z^(2*k)/lommelA m ν (k+1)) μ := by
  obtain ⟨δ, hδ, η, hη, hb⟩ := lommelA_factor_bound h
  set U : Set ℂ := Metric.ball μ δ
  have hU : ∀ m ∈ U, ‖m - μ‖ < δ := fun m hm => by simpa [U, dist_eq_norm] using hm
  set u : ℕ → ℝ := fun k => (1/η^2) * ((‖z‖^2/η^2)^k / k !)
  have hu : Summable u := (Real.summable_pow_div_factorial _).mul_left _
  have hbound : ∀ k : ℕ, ∀ m ∈ U, ‖(-1)^k*z^(2*k)/lommelA m ν (k+1)‖ ≤ u k := by
    intro k m hm
    have hA := norm_lommelA_ge hη (hb m (hU m hm)) (k+1)
    have hpos : 0 < η^(2*(k+1)) * (((k+1) ! : ℕ) : ℝ)^2 := by positivity
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
    calc ‖z‖^(2*k) / ‖lommelA m ν (k+1)‖ ≤ ‖z‖^(2*k) / (η^(2*(k+1)) * (((k+1) ! : ℕ) : ℝ)^2) :=
          div_le_div_of_nonneg_left (by positivity) hpos hA
      _ ≤ u k := by
          have hk : (0:ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
          have h2 : (1:ℝ) ≤ ((k+1) ! : ℕ) := by
            exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
          have h1 : (k ! : ℝ) ≤ ((k+1) ! : ℕ) := by
            exact_mod_cast Nat.factorial_le (by omega)
          have hf1 : (k ! : ℝ) ≤ (((k+1) ! : ℕ) : ℝ)^2 := by nlinarith
          have he : u k = ‖z‖^(2*k) / (η^(2*(k+1)) * (k ! : ℝ)) := by
            simp only [u]
            rw [div_pow, ← pow_mul]
            field_simp
            ring
          rw [he]
          exact div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left hf1 (by positivity))
  have hcont : ∀ k : ℕ, ContinuousOn (fun m => (-1)^k*z^(2*k)/lommelA m ν (k+1)) U := by
    intro k
    refine continuousOn_const.div ?_ fun m hm => ?_
    · simp only [lommelA]; fun_prop
    · have := norm_lommelA_ge hη (hb m (hU m hm)) (k+1)
      intro h0; rw [h0, norm_zero] at this
      have : 0 < η^(2*(k+1)) * (((k+1) ! : ℕ) : ℝ)^2 := by positivity
      linarith
  exact (continuousOn_tsum hcont hu hbound).continuousAt (Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self hδ))

/-- `lommelCapitalRegular` is continuous in `μ` at regular parameters. -/
theorem continuousAt_lommelCapitalRegular {μ ν : ℂ} (h : LommelRegular μ ν) {z : ℂ}
    (hz : z ≠ 0) : ContinuousAt (fun m => lommelCapitalRegular m ν z) μ := by
  have hA : ∀ k : ℕ, (μ-ν+1)/2 ≠ -k := fun k hk => (h k).1 (by linear_combination 2*hk)
  have hB : ∀ k : ℕ, (μ+ν+1)/2 ≠ -k := fun k hk => (h k).2 (by linear_combination 2*hk)
  have hS : ContinuousAt (fun m => lommelS m ν z) μ := by
    simp only [lommelS]
    exact ((continuousAt_const_cpow hz).comp (by fun_prop : ContinuousAt (fun m : ℂ => m+1) μ)).mul
      (continuousAt_lommelSeries h z)
  have hG1 : ContinuousAt (fun m : ℂ => Gamma ((m+ν+1)/2)) μ :=
    (Complex.differentiableAt_Gamma _ hB).continuousAt.comp
      (f := fun m : ℂ => (m+ν+1)/2) (x := μ) (by fun_prop)
  have hG2 : ContinuousAt (fun m : ℂ => Gamma ((m-ν+1)/2)) μ :=
    (Complex.differentiableAt_Gamma _ hA).continuousAt.comp
      (f := fun m : ℂ => (m-ν+1)/2) (x := μ) (by fun_prop)
  have h2 : ContinuousAt (fun m : ℂ => (2:ℂ)^(m-1)) μ :=
    (continuousAt_const_cpow two_ne_zero).comp (by fun_prop)
  unfold lommelCapitalRegular
  exact hS.add (((h2.mul hG1).mul hG2).mul (by fun_prop))

/-- Identity under the stated parameter and domain assumptions: `lommelCapital μ ν z =
lommelCapitalRegular μ ν z`. -/
@[dlmf 11.9.E5]
theorem lommelCapital_regular {μ ν z : ℂ} (h : LommelRegular μ ν) (hz : z ∈ slitPlane) :
    lommelCapital μ ν z = lommelCapitalRegular μ ν z :=
  ((continuousAt_lommelCapitalRegular h (slitPlane_ne_zero hz)).tendsto.mono_left
    nhdsWithin_le_nhds).limUnder_eq

/-- Existence of the limiting definition at exceptional parameters. -/
theorem lommelCapital_parameter_limit (μ ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    Tendsto (fun m => lommelCapitalRegular m ν z) (𝓝[≠] μ) (𝓝 (lommelCapital μ ν z)) := by
  sorry

/-- Identity under the stated parameter and domain assumptions: `lommelA μ ν k = 4^k*poch
((μ-ν+1)/2) k*poch ((μ+ν+1)/2) k`. -/
@[dlmf 11.9.E4]
theorem lommelA_poch (μ ν : ℂ) (k : ℕ) :
    lommelA μ ν k = 4^k*poch ((μ-ν+1)/2) k*poch ((μ+ν+1)/2) k := by
  induction k with
  | zero => simp [lommelA, poch_zero]
  | succ k ih =>
    have h : lommelA μ ν (k+1) = lommelA μ ν k*((μ+2*k+1)^2-ν^2) := by
      simp [lommelA, Finset.prod_range_succ]
    rw [h, ih, poch_succ, poch_succ, pow_succ]
    push_cast
    ring

/-- Regular Lommel parameters give nonpolar half-parameters of its hypergeometric series. -/
theorem lommelRegular_half_nonpole {μ ν : ℂ} (h : LommelRegular μ ν) :
    (∀ k : ℕ, (μ-ν+1)/2 ≠ -k) ∧ (∀ k : ℕ, (μ+ν+1)/2 ≠ -k) := by
  constructor
  · intro k hk
    exact (h k).1 (by linear_combination 2*hk)
  · intro k hk
    exact (h k).2 (by linear_combination 2*hk)

/-- The regularized 1F2 coefficient preserves the exact Lommel normalization. -/
theorem lommelCoeff_eq_regularized {μ ν : ℂ} (h : LommelRegular μ ν) (k : ℕ) :
    Gamma ((μ-ν+1)/2)*Gamma ((μ+ν+1)/2)/4 *
      regularizedHGFunCoeff {1} {(μ-ν+3)/2,(μ+ν+3)/2} k / 4^k =
        1/lommelA μ ν (k+1) := by
  obtain ⟨hA,hB⟩ := lommelRegular_half_nonpole h
  have hGA := Gamma_add_nat_div_Gamma_eq (n := k+1) ((μ-ν+1)/2) hA
  have hGB := Gamma_add_nat_div_Gamma_eq (n := k+1) ((μ+ν+1)/2) hB
  have hpA := poch_ne_zero_of_not_neg_nat hA (k+1)
  have hpB := poch_ne_zero_of_not_neg_nat hB (k+1)
  rw [← poch, div_eq_iff (Gamma_ne_zero hA)] at hGA
  rw [← poch, div_eq_iff (Gamma_ne_zero hB)] at hGB
  rw [regularizedHGFunCoeff]
  simp only [Multiset.map_singleton, Multiset.prod_singleton, Multiset.insert_eq_cons,
    Multiset.map_cons, Multiset.prod_cons]
  rw [show (ascPochhammer ℂ k).eval 1=(k.factorial:ℂ) by simpa [poch] using poch_nat_one k,
    show (μ-ν+3)/2+k=(μ-ν+1)/2+(k+1:ℕ) by push_cast; ring,
    show (μ+ν+3)/2+k=(μ+ν+1)/2+(k+1:ℕ) by push_cast; ring,
    hGA, hGB, lommelA_poch]
  field_simp [Gamma_ne_zero hA, Gamma_ne_zero hB, hpA, hpB,
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)]
  ring

/-- The small Lommel function is a regularized 1F2 specialization on its regular domain. -/
theorem lommelS_eq_regularized {μ ν : ℂ} (h : LommelRegular μ ν) (z : ℂ) :
    lommelS μ ν z = z^(μ+1)*(Gamma ((μ-ν+1)/2)*Gamma ((μ+ν+1)/2)/4)*
      regularizedHGFun {1} {(μ-ν+3)/2,(μ+ν+3)/2} (-z^2/4) := by
  rw [lommelS, mul_assoc]
  congr 1
  rw [regularizedHGFun_eq_tsum', ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [div_pow, neg_pow (z^2), ← pow_mul]
  have hc := lommelCoeff_eq_regularized h k
  linear_combination -(-1:ℂ)^k*z^(2*k)*hc

/-- The series with terms `(fun k : ℕ => z^(μ+1)*(-1)^k*z^(2*k)/lommelA μ ν (k+1))` converges to
`(lommelS μ ν z)`. -/
@[dlmf 11.9.E3]
theorem hasSum_lommelS {μ ν : ℂ} (h : LommelRegular μ ν) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => z^(μ+1)*(-1)^k*z^(2*k)/lommelA μ ν (k+1)) (lommelS μ ν z) := by
  have hr : (regularizedHGFunSeries {1} {(μ-ν+3)/2,(μ+ν+3)/2}).radius=⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  have hp : HasFPowerSeriesOnBall (regularizedHGFun {1} {(μ-ν+3)/2,(μ+ν+3)/2})
      (FormalMultilinearSeries.ofScalars ℂ (regularizedHGFunCoeff {1} {(μ-ν+3)/2,(μ+ν+3)/2})) 0 ⊤ := by
    change HasFPowerSeriesOnBall (regularizedHGFunSeries {1} {(μ-ν+3)/2,(μ+ν+3)/2}).sum
      (regularizedHGFunSeries {1} {(μ-ν+3)/2,(μ+ν+3)/2}) 0 ⊤
    rw [← hr]
    exact (regularizedHGFunSeries {1} {(μ-ν+3)/2,(μ+ν+3)/2}).hasFPowerSeriesOnBall (by rw [hr]; simp)
  have hs := (hp.hasSum_mul_pow (by simp : (-z^2/4) ∈ Metric.eball (0:ℂ) ⊤)).mul_left
    (z^(μ+1)*(Gamma ((μ-ν+1)/2)*Gamma ((μ+ν+1)/2)/4))
  rw [← lommelS_eq_regularized h] at hs
  refine hs.congr_fun fun k => ?_
  rw [div_pow, neg_pow (z^2), ← pow_mul]
  have hc := lommelCoeff_eq_regularized h k
  linear_combination -z^(μ+1)*(-1:ℂ)^k*z^(2*k)*hc

/-- Analyticity of the small Lommel function on its regular parameter domain. -/
theorem lommelS_analytic {μ ν : ℂ} (h : LommelRegular μ ν) :
    AnalyticOnNhd ℂ (lommelS μ ν) slitPlane := by
  rw [funext (lommelS_eq_regularized h)]
  intro z hz
  have hg : AnalyticAt ℂ (fun w : ℂ => w^(μ+1)) z :=
    analyticAt_id.cpow analyticAt_const hz
  have hF : AnalyticAt ℂ (fun w : ℂ =>
      regularizedHGFun {1} {(μ-ν+3)/2,(μ+ν+3)/2} (-w^2/4)) z :=
    ((hasFPowerSeriesOnBall_regularized1F2_one _ _).analyticAt_of_mem (by simp)).comp (by fun_prop)
  exact (hg.mul analyticAt_const).mul hF

/-- The small Lommel forcing follows from the regularized quadratic coefficient recurrence. -/
theorem lommelS_residual {μ ν : ℂ} (h : LommelRegular μ ν) {z : ℂ} (hz : z ∈ slitPlane) :
    besselResidual ν (-1) (lommelS μ ν) z=z^(μ+1) := by
  let C := Gamma ((μ-ν+1)/2)*Gamma ((μ+ν+1)/2)/4
  let g := fun w : ℂ => w^(μ+1)*C
  have hg (w : ℂ) (hw : w ∈ slitPlane) : HasDerivAt g (g w*((μ+1)/w)) w := by
    have hd := (((hasDerivAt_id w).cpow_const (c:=μ+1) hw).mul_const C)
    have hd' : HasDerivAt g _ w :=
      hd.congr_of_eventuallyEq (Eventually.of_forall fun y => rfl)
    refine hd'.congr_deriv ?_
    simp only [id_eq, mul_one]
    rw [cpow_sub _ _ (slitPlane_ne_zero hw), cpow_one]
    dsimp only [g]
    ring
  have he := regularized1F2_bessel_gauge (μ+1) ν (-1) g hg hz
  rw [show (μ+1-ν)/2+1=(μ-ν+3)/2 by ring,
    show (μ+1+ν)/2+1=(μ+ν+3)/2 by ring,
    show (μ+1-ν)/2=(μ-ν+1)/2 by ring,
    show (μ+1+ν)/2=(μ+ν+1)/2 by ring] at he
  change besselResidual ν (-1)
    (fun w => g w*regularizedHGFun {1} {(μ-ν+3)/2,(μ+ν+3)/2} (-1*w^2/4)) z=_ at he
  have hf : (fun w => g w*regularizedHGFun {1} {(μ-ν+3)/2,(μ+ν+3)/2} (-1*w^2/4)) =
      lommelS μ ν := by
    funext w
    rw [lommelS_eq_regularized h]
    simp only [g,C,neg_one_mul,neg_div]
  rw [hf] at he
  obtain ⟨hA,hB⟩ := lommelRegular_half_nonpole h
  have hGA := Gamma_ne_zero hA
  have hGB := Gamma_ne_zero hB
  dsimp only [g,C] at he
  convert he using 1
  field_simp

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv 2 (lommelS μ ν)
z+deriv (lommelS μ ν) z/z+(1-ν^2/z^2)*lommelS μ ν z = z^(μ-1)`. -/
@[dlmf 11.9.E1]
theorem lommelS_ode {μ ν : ℂ} (h : LommelRegular μ ν) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv 2 (lommelS μ ν) z+deriv (lommelS μ ν) z/z+(1-ν^2/z^2)*lommelS μ ν z = z^(μ-1) := by
  have he := lommelS_residual h hz
  have hp : z^(μ+1)=z^(μ-1)*z^2 := by
    rw [show μ+1=μ-1+(2:ℕ) by norm_num; ring,
      cpow_add _ _ (slitPlane_ne_zero hz), cpow_natCast]
  rw [hp] at he
  unfold besselResidual at he
  generalize iteratedDeriv 2 (lommelS μ ν) z=A, deriv (lommelS μ ν) z=B,
    lommelS μ ν z=C at he ⊢
  linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) he/z^2

/-- Identity under the stated parameter and domain assumptions: `lommelS μ (-ν) z = lommelS μ ν
z`. -/
@[dlmf 11.9.E6]
theorem lommelS_neg_order {μ ν : ℂ} (h : LommelRegular μ ν) {z : ℂ} (hz : z ∈ slitPlane) :
    lommelS μ (-ν) z = lommelS μ ν z := by
  have h (k : ℕ) : lommelA μ (-ν) k=lommelA μ ν k := by simp [lommelA]
  simp only [lommelS, h]

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv 2 (lommelCapital μ
ν) z+deriv (lommelCapital μ ν) z/z+(1-ν^2/z^2)*lommelCapital μ ν z = z^(μ-1)`. -/
@[dlmf 11.9.E1]
theorem lommelCapital_ode (μ ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv 2 (lommelCapital μ ν) z+deriv (lommelCapital μ ν) z/z+(1-ν^2/z^2)*lommelCapital μ ν z = z^(μ-1) := by
  sorry

/-- Identity under the stated parameter and domain assumptions: `lommelCapital μ (-ν) z =
lommelCapital μ ν z`. -/
@[dlmf 11.9.E6]
theorem lommelCapital_neg_order (μ ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    lommelCapital μ (-ν) z = lommelCapital μ ν z := by
  unfold lommelCapital
  simp only [lommelCapitalRegular_neg_order _ ν hz]

/-- Formula under the stated hypotheses: `(AnalyticOnNhd ℂ f slitPlane ∧ ∀ z ∈ slitPlane,
iteratedDeriv 2 f z+deriv f z/z+(1-ν^2/z^2)*f z=z^(μ-1)) ↔ ∃ A B : ℂ, ∀ z ∈ slitPlane, f
z=lommelS μ ν z+A*besselJ ν z+B*besselY ν z`. -/
@[dlmf 11.9.E2]
theorem lommel_general_solution {μ ν : ℂ} (h : LommelRegular μ ν) (f : ℂ → ℂ) :
    (AnalyticOnNhd ℂ f slitPlane ∧ ∀ z ∈ slitPlane, iteratedDeriv 2 f z+deriv f z/z+(1-ν^2/z^2)*f z=z^(μ-1)) ↔ ∃ A B : ℂ, ∀ z ∈ slitPlane, f z=lommelS μ ν z+A*besselJ ν z+B*besselY ν z := by
  rw [← bessel_inhomogeneous_general_solution ν (lommelS_analytic h)]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro z
  apply forall_congr'
  intro hz
  have hp := lommelS_residual h hz
  rw [hp]
  unfold besselResidual
  have hpow : z^(μ+1)=z^(μ-1)*z^2 := by
    rw [show μ+1=μ-1+(2:ℕ) by norm_num; ring,
      cpow_add _ _ (slitPlane_ne_zero hz), cpow_natCast]
  rw [hpow]
  constructor
  · intro hf
    linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) z^2*hf
  · intro hf
    linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) hf/z^2

/-- The series with terms `(fun k : ℕ => 2^(μ+1)*(2*k+μ+1)*Gamma
(k+μ+1)/((k.factorial:ℂ)*(2*k+μ-ν+1)*(2*k+μ+ν+1))*besselJ (2*k+μ+1) z)` converges to `(lommelS
μ ν z)`. -/
@[dlmf 11.9.E7]
theorem lommelS_bessel_series_7 {μ ν : ℂ} (h : ∀ n : ℕ, μ-ν ≠ -(n+1) ∧ μ+ν ≠ -(n+1)) (hm : ∀ n : ℕ, μ ≠ -(n+1)) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 2^(μ+1)*(2*k+μ+1)*Gamma (k+μ+1)/((k.factorial:ℂ)*(2*k+μ-ν+1)*(2*k+μ+ν+1))*besselJ (2*k+μ+1) z) (lommelS μ ν z) := by
  have hz0 := slitPlane_ne_zero hz
  have hl : ∀ n : ℕ, μ + 1 ≠ -n := fun n h' => hm n (by linear_combination h')
  have ha : ∀ n : ℕ, (n : ℂ) + (μ - ν + 1) / 2 ≠ 0 := fun n h' =>
    (h (2 * n)).1 (by push_cast; linear_combination 2 * h')
  have hb : ∀ n : ℕ, (n : ℂ) + (μ + ν + 1) / 2 ≠ 0 := fun n h' =>
    (h (2 * n)).2 (by push_cast; linear_combination 2 * h')
  have hL := (hasSum_besselJ_neumann_lommel (l := μ + 1) (a := (μ - ν + 1) / 2)
    (b := (μ + ν + 1) / 2) (by ring) hl ha hb hz0).mul_left ((2 : ℂ) ^ (μ + 1) / 4)
  have hA : ∀ j : ℕ, lommelA μ ν (j + 1) =
      4 ^ (j + 1) * ∏ i ∈ Finset.range (j + 1), (((i : ℂ) + (μ - ν + 1) / 2) * (i + (μ + ν + 1) / 2)) := by
    intro j
    rw [lommelA, show (4 : ℂ) ^ (j + 1) = ∏ _i ∈ Finset.range (j + 1), (4 : ℂ) by simp,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  convert hL using 1
  · funext k
    have h1 := ha k
    have h2 := hb k
    have h3 : (2 * k + μ - ν + 1 : ℂ) ≠ 0 := fun h' => h1 (by linear_combination h' / 2)
    have h4 : (2 * k + μ + ν + 1 : ℂ) ≠ 0 := fun h' => h2 (by linear_combination h' / 2)
    have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [powerNeumannCoeff, show (2 * k + μ + 1 : ℂ) = μ + 1 + 2 * k by ring,
      show (k + μ + 1 : ℂ) = μ + 1 + k by ring,
      show ((k ! : ℂ) * (2 * k + μ - ν + 1) * (2 * k + μ + ν + 1)) =
        k ! * (4 * ((k + (μ - ν + 1) / 2) * (k + (μ + ν + 1) / 2))) by ring]
    field_simp
  · have h2 : (2 : ℂ) ^ (μ + 1) ≠ 0 := cpow_ne_zero_iff_of_exponent_ne_zero
      (fun h' => hl 0 (by simpa using h')) |>.mpr two_ne_zero
    rw [lommelS, div_two_cpow hz0, show ∀ X Y : ℂ, 2 ^ (μ + 1) / 4 * (X / 2 ^ (μ + 1) * Y) =
      X * (1 / 4 * Y) from fun X Y => by field_simp, ← tsum_mul_left (α := ℂ) (a := 1 / 4)]
    congr 1
    refine tsum_congr fun j => ?_
    have hP : ∏ i ∈ Finset.range (j + 1), (((i : ℂ) + (μ - ν + 1) / 2) * (i + (μ + ν + 1) / 2)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (ha i) (hb i)
    rw [hA, div_pow, pow_mul, pow_mul, pow_succ]
    generalize ∏ i ∈ Finset.range (j + 1), (((i : ℂ) + (μ - ν + 1) / 2) * (i + (μ + ν + 1) / 2)) = P at hP ⊢
    field_simp
    ring

/-- The series with terms `(fun k : ℕ => 2^((μ+ν-1)/2)*Gamma
((μ+ν+1)/2)*z^((μ+1-ν)/2)*(z/2)^k/((k.factorial:ℂ)*(2*k+μ-ν+1))*besselJ (k+(μ+ν+1)/2) z)`
converges to `(lommelS μ ν z)`. -/
@[dlmf 11.9.E8]
theorem lommelS_bessel_series_8 {μ ν : ℂ} (h : ∀ n : ℕ, μ-ν ≠ -(n+1) ∧ μ+ν ≠ -(n+1)) (hm : ∀ n : ℕ, μ ≠ -(n+1)) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 2^((μ+ν-1)/2)*Gamma ((μ+ν+1)/2)*z^((μ+1-ν)/2)*(z/2)^k/((k.factorial:ℂ)*(2*k+μ-ν+1))*besselJ (k+(μ+ν+1)/2) z) (lommelS μ ν z) := by
  have hz0 := slitPlane_ne_zero hz
  have hw0 : z / 2 ≠ 0 := div_ne_zero hz0 two_ne_zero
  set α : ℂ := (μ - ν + 1) / 2 with hα
  set β : ℂ := (μ + ν + 1) / 2 with hβ
  have ha : ∀ n : ℕ, (n : ℂ) + α ≠ 0 := fun n h' =>
    (h (2 * n)).1 (by push_cast; linear_combination 2 * h')
  have hb : ∀ n : ℕ, (n : ℂ) + β ≠ 0 := fun n h' =>
    (h (2 * n)).2 (by push_cast; linear_combination 2 * h')
  have hx : ∀ i : ℕ, α + i ≠ 0 := fun i => by rw [add_comm]; exact ha i
  have hy : ∀ i : ℕ, β + i ≠ 0 := fun i => by rw [add_comm]; exact hb i
  have hGβ : Gamma β ≠ 0 := Complex.Gamma_ne_zero fun m h' => hy m (by rw [h']; ring)
  set c : ℕ → ℂ := fun k => 1 / ((k ! : ℂ) * (k + α)) with hc_def
  obtain ⟨B, hB0, hB⟩ := exists_norm_recip_nat_add_le α
  have hcb : ∀ k, ‖c k‖ ≤ B * 1 ^ k := fun k => by
    have hf : (1 : ℝ) ≤ k ! := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
    show ‖1 / ((k ! : ℂ) * (k + α))‖ ≤ B * 1 ^ k
    rw [one_pow, mul_one, one_div, mul_inv, norm_mul, norm_inv, Complex.norm_natCast]
    calc (k ! : ℝ)⁻¹ * ‖((k : ℂ) + α)⁻¹‖ ≤ 1 * B := by
          gcongr
          · exact inv_le_one_of_one_le₀ hf
          · exact hB k
      _ = B := one_mul B
  have hcoeff : ∀ j, neumannCoeff β (-1) c (fun k => k) j =
      (-1) ^ j / (Gamma (β + j + 1) * ∏ i ∈ Finset.range (j + 1), (α + (i : ℂ))) := by
    intro j
    rw [div_mul_eq_div_div_swap, ← sum_antidiagonal_neg_one_pow_div_add j hx, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [regularizedHGFunCoeff_empty, hc_def]
    dsimp only
    have hj : (j : ℂ) = p.1 + p.2 := by exact_mod_cast hp.symm
    rw [hj, show β + ((p.1 : ℕ) : ℂ) + 1 + ((p.2 : ℕ) : ℂ) = β + (p.1 + p.2) + 1 by ring,
      show (p.1 : ℂ) + α = α + p.1 by ring]
    simp only [div_eq_mul_inv, one_mul, mul_inv]
    ring
  have hN := hasSum_besselJ_neumann_of_coeff hz0 β c (fun k => k) (fun k => k)
    (fun k => by ring)
    (summable_neumann_of_norm_le zero_le_one hcb _ (fun k => ⟨le_rfl, by omega⟩) _) _ hcoeff
  have h2 := hN.mul_left (2 ^ ((μ + ν - 1) / 2) * Gamma β * z ^ ((μ + 1 - ν) / 2) / 2)
  convert h2 using 1
  · funext k
    have h1 := ha k
    have h3 : (2 * k + μ - ν + 1 : ℂ) = 2 * (k + α) := by rw [hα]; ring
    have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [h3, show (k : ℂ) + β = β + k by ring]
    simp only [hc_def]
    field_simp
  · have h2pos : (2 : ℂ) ^ β ≠ 0 := by
      exact cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
    have hpre : 2 ^ ((μ + ν - 1) / 2) * Gamma β * z ^ ((μ + 1 - ν) / 2) / 2 * (z / 2) ^ β =
        z ^ (μ + 1) * Gamma β / 4 := by
      rw [div_two_cpow hz0, show (μ + ν - 1) / 2 = β - 1 by rw [hβ]; ring,
        cpow_sub _ _ two_ne_zero, cpow_one, show (μ + 1 - ν) / 2 = α by rw [hα]; ring,
        show μ + 1 = α + β by rw [hα, hβ]; ring, cpow_add _ _ hz0]
      field_simp
      ring
    rw [lommelS, ← mul_assoc, hpre, show ∀ X Y : ℂ, X * Gamma β / 4 * Y = X * (Gamma β / 4 * Y) from
      fun X Y => by ring, ← tsum_mul_left (α := ℂ) (a := Gamma β / 4)]
    congr 1
    refine tsum_congr fun j => ?_
    have hP := Gamma_add_nat_succ_eq_prod hy j
    have hA : lommelA μ ν (j + 1) =
        4 ^ (j + 1) * ((∏ i ∈ Finset.range (j + 1), (α + (i : ℂ))) * ∏ i ∈ Finset.range (j + 1), (β + (i : ℂ))) := by
      rw [lommelA, show (4 : ℂ) ^ (j + 1) = ∏ _i ∈ Finset.range (j + 1), (4 : ℂ) by simp,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [hα, hβ]; ring
    have hq1 : ∏ i ∈ Finset.range (j + 1), (α + (i : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hx i
    have hq2 : ∏ i ∈ Finset.range (j + 1), (β + (i : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hy i
    rw [hA, hP, div_pow, pow_mul, pow_mul, pow_succ]
    generalize ∏ i ∈ Finset.range (j + 1), (α + (i : ℂ)) = P at hq1 ⊢
    generalize ∏ i ∈ Finset.range (j + 1), (β + (i : ℂ)) = Q at hq2 ⊢
    field_simp
    ring

/-- Asymptotic bound with the indicated comparison function: `(fun z : ℂ => lommelCapital μ ν
z-z^(μ-1)*∑ k ∈ Finset.range N, (-1)^k*lommelA (-μ) ν k*z^(-(2*k:ℤ))) =O[sector (π-δ)] (fun z
: ℂ => z^(μ-1-2*N))`. -/
@[dlmf 11.9.E9]
theorem lommelCapital_asymptotic (μ ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => lommelCapital μ ν z-z^(μ-1)*∑ k ∈ Finset.range N, (-1)^k*lommelA (-μ) ν k*z^(-(2*k:ℤ))) =O[sector (π-δ)] (fun z : ℂ => z^(μ-1-2*N)) := by
  sorry

/-- Formula under the stated hypotheses: `lommelCapital μ ν z = z^(μ-1)*∑ k ∈ Finset.range (n+1),
(-1)^k*lommelA (-μ) ν k*z^(-(2*k:ℤ))`. -/
@[dlmf 11.9.E9]
theorem lommelCapital_terminates {μ ν : ℂ} (n : ℕ) (h : μ+ν=2*n+1 ∨ μ-ν=2*n+1) {z : ℂ} (hz : z ∈ slitPlane) :
    lommelCapital μ ν z = z^(μ-1)*∑ k ∈ Finset.range (n+1), (-1)^k*lommelA (-μ) ν k*z^(-(2*k:ℤ)) := by
  sorry

/-- Shifting the degree by two preserves the regular Lommel parameter domain. -/
theorem LommelRegular.add_two {μ ν : ℂ} (h : LommelRegular μ ν) :
    LommelRegular (μ + 2) ν := by
  intro n
  constructor
  · intro hn
    exact (h (n + 1)).1 (by push_cast at *; linear_combination hn)
  · intro hn
    exact (h (n + 1)).2 (by push_cast at *; linear_combination hn)

/-- Removing the first Lommel product factor shifts the degree by two. -/
theorem lommelA_add_two (μ ν : ℂ) (k : ℕ) :
    lommelA μ ν (k + 1) = ((μ + 1)^2 - ν^2) * lommelA (μ + 2) ν k := by
  induction k with
  | zero => simp [lommelA]
  | succ k ih =>
    rw [show lommelA μ ν (k + 1 + 1) =
      lommelA μ ν (k + 1) * ((μ + 2 * (k + 1) + 1)^2 - ν^2) by
        simp [lommelA, Finset.prod_range_succ]]
    rw [ih]
    simp only [lommelA, Finset.prod_range_succ]
    ring

set_option maxHeartbeats 1000000 in
/-- The degree-two recurrence of the small Lommel function on its regular domain. -/
theorem lommelS_add_two {μ ν : ℂ} (h : LommelRegular μ ν) {z : ℂ}
    (hz : z ∈ slitPlane) :
    lommelS (μ + 2) ν z = z^(μ + 1) - ((μ + 1)^2 - ν^2) * lommelS μ ν z := by
  let D := (μ + 1)^2 - ν^2
  have hD : D ≠ 0 := by
    rw [show D = (μ + 1 - ν) * (μ + 1 + ν) by dsimp [D]; ring]
    refine mul_ne_zero (fun he => (h 0).1 ?_) (fun he => (h 0).2 ?_)
    · norm_num at *
      linear_combination he
    · norm_num at *
      linear_combination he
  have hpow : z^(μ + 2 + 1) = z^(μ + 1) * z^2 := by
    rw [show μ + 2 + 1 = μ + 1 + (2 : ℕ) by norm_num; ring,
      cpow_add _ _ (slitPlane_ne_zero hz), cpow_natCast]
  have hs := (hasSum_lommelS h.add_two hz).mul_left (-D⁻¹)
  have htail : HasSum
      (fun k : ℕ => z^(μ + 1) * (-1)^(k + 1) * z^(2*(k + 1)) /
        lommelA μ ν (k + 1 + 1)) (-D⁻¹ * lommelS (μ + 2) ν z) := by
    convert hs using 1
    funext k
    rw [lommelA_add_two μ ν (k + 1), hpow]
    dsimp only [D]
    rw [pow_succ, show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have heq := htail.unique ((hasSum_nat_add_iff' 1).mpr (hasSum_lommelS h hz))
  simp only [Finset.sum_range_one] at heq
  simp [lommelA] at heq
  change -(D⁻¹ * lommelS (μ + 2) ν z) = lommelS μ ν z - z^(μ + 1) / D at heq
  field_simp [hD] at heq
  linear_combination -heq

/-- The regular capital Lommel function is an analytic particular solution,
using the existing Bessel fundamental system rather than differentiating its
three summands again. This does not assume the exceptional-parameter limit. -/
theorem lommelCapital_analytic_ode_of_regular {μ ν : ℂ} (h : LommelRegular μ ν) :
    AnalyticOnNhd ℂ (lommelCapital μ ν) slitPlane ∧
      ∀ z ∈ slitPlane, iteratedDeriv 2 (lommelCapital μ ν) z +
        deriv (lommelCapital μ ν) z / z +
        (1 - ν^2 / z^2) * lommelCapital μ ν z = z^(μ - 1) := by
  apply (lommel_general_solution h (lommelCapital μ ν)).2
  let C := 2^(μ-1) * Gamma ((μ+ν+1)/2) * Gamma ((μ-ν+1)/2)
  refine ⟨C * sin ((μ-ν)*π/2), -C * cos ((μ-ν)*π/2), fun z hz => ?_⟩
  rw [lommelCapital_regular h hz]
  simp only [lommelCapitalRegular, C]
  ring

/-- The Bessel correction obeys the same degree recurrence as the small
Lommel solution, so their sum does as well. -/
theorem lommelCapitalRegular_add_two {μ ν : ℂ} (h : LommelRegular μ ν)
    {z : ℂ} (hz : z ∈ slitPlane) :
    lommelCapitalRegular (μ + 2) ν z =
      z^(μ + 1) - ((μ + 1)^2 - ν^2) * lommelCapitalRegular μ ν z := by
  obtain ⟨hA, hB⟩ := lommelRegular_half_nonpole h
  have hA0 : (μ-ν+1)/2 ≠ 0 := by simpa using hA 0
  have hB0 : (μ+ν+1)/2 ≠ 0 := by simpa using hB 0
  have hpow : (2 : ℂ)^(μ + 2 - 1) = 2^(μ - 1) * 4 := by
    rw [show μ + 2 - 1 = μ - 1 + (2 : ℕ) by norm_num; ring,
      cpow_add _ _ two_ne_zero, cpow_natCast]
    norm_num
  simp only [lommelCapitalRegular]
  rw [lommelS_add_two h hz, hpow,
    show (μ + 2 + ν + 1)/2 = (μ+ν+1)/2 + 1 by ring,
    show (μ + 2 - ν + 1)/2 = (μ-ν+1)/2 + 1 by ring,
    Gamma_add_one _ hB0, Gamma_add_one _ hA0,
    show (μ + 2 - ν)*π/2 = (μ-ν)*π/2 + π by ring,
    sin_add_pi, cos_add_pi]
  ring

/-- Degree recurrence for capital Lommel on the regular parameter domain;
it is independent of the outstanding exceptional-parameter limit theorem. -/
theorem lommelCapital_add_two_of_regular {μ ν : ℂ} (h : LommelRegular μ ν)
    {z : ℂ} (hz : z ∈ slitPlane) :
    lommelCapital (μ + 2) ν z =
      z^(μ + 1) - ((μ + 1)^2 - ν^2) * lommelCapital μ ν z := by
  rw [lommelCapital_regular h.add_two hz, lommelCapital_regular h hz]
  exact lommelCapitalRegular_add_two h hz

end DLMF.Struve

/-! ## Holomorphic lower-parameter support for exceptional continuation

The local uniform reciprocal-Gamma factorial bound and the general series-holomorphy
API establish joint holomorphy. Exceptional 1F2 tails reduce exactly to 0F1.
These support lemmas do not yet remove the capital-Lommel continuation admission.
-/

open Complex Filter Set
open scoped Topology Nat Real
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000
noncomputable section
namespace DLMF.Struve
open DLMF.Hypergeometric DLMF.Bessel

/-- The regularized 1F2 numerator is jointly entire in both lower parameters. -/
theorem differentiable_regularized1F2_params (q : ℂ) :
    Differentiable ℂ (fun p : ℂ × ℂ => regularizedHGFun {1} {p.1,p.2} q) := by
  have heq : (fun p : ℂ × ℂ => regularizedHGFun {1} {p.1,p.2} q) =
      fun p => ∑' n : ℕ, q^n * (Gamma (p.1+n))⁻¹ * (Gamma (p.2+n))⁻¹ := by
    funext p
    rw [(hasSum_regularized1F2 1 p.1 p.2 q).tsum_eq.symm]
    congr 1
    funext n
    rw [regularized1F2_one_coeff]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq, ← differentiableOn_univ]
  refine Complex.differentiableOn_tsum_of_eventually_dominated isOpen_univ
    (fun n => ?_) (fun p hp => ?_)
  · exact ((differentiable_const _).mul
      (differentiable_one_div_Gamma.comp (differentiable_fst.add_const _))).mul
      (differentiable_one_div_Gamma.comp (differentiable_snd.add_const _)) |>.differentiableOn
  · set K : Set ℂ := Metric.closedBall p.1 1 ∪ Metric.closedBall p.2 1
    have hK : IsCompact K := (isCompact_closedBall _ _).union (isCompact_closedBall _ _)
    obtain ⟨m,C,hC,hbound⟩ := DLMF.Gamma.Simplex.Complex.exists_uniform_norm_recip_Gamma_add_nat hK
    set u : ℕ → ℝ := fun n => C^2 * ‖q‖^n / ((n-m)!)
    have hu : Summable u := by
      rw [← summable_nat_add_iff m]
      have hh := (Real.summable_pow_div_factorial ‖q‖).mul_left (C^2*‖q‖^m)
      convert hh using 1
      funext n
      simp only [u, Nat.add_sub_cancel, pow_add]
      ring
    refine ⟨Metric.ball p 1, Metric.ball_mem_nhds p (by norm_num), m,u,hu,?_⟩
    intro n hn w hw
    have hw1 : w.1 ∈ K := by
      apply Or.inl
      change dist w.1 p.1 ≤ 1
      exact (le_max_left _ _).trans (le_of_lt hw)
    have hw2 : w.2 ∈ K := by
      apply Or.inr
      change dist w.2 p.2 ≤ 1
      exact (le_max_right _ _).trans (le_of_lt hw)
    have h1 := hbound w.1 hw1 (n-m)
    have h2 := hbound w.2 hw2 (n-m)
    rw [← Nat.cast_add, Nat.sub_add_cancel hn] at h1 h2
    have hf : (1:ℝ) ≤ ((n-m)! : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero (n-m))
    have hc : C / (((n-m)! : ℕ):ℝ) ≤ C := div_le_self hC hf
    simp only [norm_mul, norm_pow]
    calc ‖q‖^n * ‖(Gamma (w.1+n))⁻¹‖ * ‖(Gamma (w.2+n))⁻¹‖ ≤
        ‖q‖^n * C * (C / (((n-m)! : ℕ):ℝ)) := by gcongr; exact h1.trans hc
      _ = u n := by simp only [u]; ring

/-- The Weber continuation makes the second-kind Bessel function entire in its order. -/
theorem differentiable_besselY_order {z : ℂ} (hz : z ∈ slitPlane) :
    Differentiable ℂ (fun ν : ℂ => besselY ν z) := by
  intro ν
  by_cases hν : ∃ n : ℤ, ν = n
  · obtain ⟨n,rfl⟩ := hν
    have hD := ((differentiable_besselD (slitPlane_ne_zero hz)).analyticAt n).dslope (n:ℂ)
    have hS := ((show Differentiable ℂ (fun ν : ℂ => sin (ν*π)) by fun_prop).analyticAt n).dslope (n:ℂ)
    refine (hD.differentiableAt.div hS.differentiableAt
      (dslope_sin_ne_zero n (Metric.mem_ball_self (by norm_num)))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (n:ℂ) (by norm_num : (0:ℝ)<1/2)] with μ hμ
    exact besselY_eq_dslope n hμ hz
  · push Not at hν
    have hS : sin (ν*π) ≠ 0 := sin_mul_pi_ne_zero hν
    have hopen : IsOpen {μ : ℂ | sin (μ*π) ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
    refine ((differentiable_besselD (slitPlane_ne_zero hz) ν).div (show DifferentiableAt ℂ (fun μ : ℂ => sin (μ*π)) ν by fun_prop) hS).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hS] with μ hμ
    exact besselY_eq_of_not_int (fun k hk => hμ (by rw [hk, sin_int_mul_pi_complex])) z

/-- The entire numerator of the regular capital Lommel function in its two half-parameters. -/
def lommelNumerator (a b z : ℂ) : ℂ :=
  z^(a+b)/4*regularizedHGFun {1} {a+1,b+1} (-(z^2/4)) -
    2^(a+b-2)*(cos (b*π)*besselJ (a-b) z+sin (b*π)*besselY (a-b) z)

/-- When a lower half-parameter is a nonpositive integer, the 1F2 tail is a 0F1. -/
lemma regularized1F2_one_neg_nat (n : ℕ) (b q : ℂ) :
    regularizedHGFun {1} {1-(n:ℂ),b+1} q =
      q^n*regularizedHGFun (∅ : Multiset ℂ) {b+n+1} q := by
  have h := (hasSum_regularized1F2 1 (1-(n:ℂ)) (b+1) q).summable
  rw [(hasSum_regularized1F2 1 (1-(n:ℂ)) (b+1) q).tsum_eq.symm, ← h.sum_add_tsum_nat_add n]
  have hh : ∑ k ∈ Finset.range n, regularizedHGFunCoeff {1} {1-(n:ℂ),b+1} k*q^k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    rw [regularized1F2_one_coeff, show 1-(n:ℂ)+k = -((n-k-1:ℕ):ℂ) by
      rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]; push_cast; ring,
      Gamma_neg_nat_eq_zero]
    simp
  rw [hh, zero_add, regularized0F1_eq_tsum, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [regularized1F2_one_coeff,
    show 1-(n:ℂ)+(k+n:ℕ) = (k:ℂ)+1 by push_cast; ring,
    show b+1+(k+n:ℕ) = b+n+1+k by push_cast; ring,
    Gamma_nat_eq_factorial]
  simp only [pow_add, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The capital-Lommel cancellation numerator is symmetric in its half-parameters. -/
theorem lommelNumerator_symm (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    lommelNumerator a b z = lommelNumerator b a z := by
  unfold lommelNumerator
  rw [show ({b+1,a+1}:Multiset ℂ)={a+1,b+1} by simp only [Multiset.insert_eq_cons]; exact Multiset.cons_swap _ _ _, add_comm b a]
  have he : b-a = -(a-b) := by ring
  rw [he, besselJ_neg_eq (a-b) hz, besselY_neg (a-b) hz]
  have hc := cos_sub (a*π) (b*π)
  have hs := sin_sub (a*π) (b*π)
  rw [show a*π-b*π=(a-b)*π by ring] at hc hs
  have hca := sin_sq_add_cos_sq (a*π)
  have hcb := sin_sq_add_cos_sq (b*π)
  rw [hc,hs]
  linear_combination (2^(a+b-2)*cos (b*π)*besselJ (a-b) z)*hca +
    (2^(a+b-2)*sin (b*π)*besselY (a-b) z)*hca

end DLMF.Struve
