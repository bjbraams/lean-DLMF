/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic
public import DLMF.Weierstrass.DifferentialEquations
public import DLMF.Weierstrass.Relations.ThetaIdentities
public import DLMF.Theta.Products.InfiniteProducts
public import DLMF.Theta.Products.LogDerivativesAndDoubleProducts
public import DLMF.Elementary.Trigonometric.DirectIdentities

/-!
# Fourier series, series of cosecants, products and Laurent series (DLMF §§23.8–23.9)

Series are stated with `HasSum` (all of them converge absolutely). Sums from `n = 1` are
indexed by `n : ℕ` with the shift `n + 1`; the Eisenstein-bracketed cotangent series 23.8.4 is
stated as the absolutely convergent series of the bracketed pairs `n`, `-n`.

**Source correction.** The convergence condition of 23.8.1–23.8.2 is printed as
`ℑ(z/ω₁) < 2ℑ(ω₃/ω₁)`; the series diverge when `ℑ(z/ω₁) ≤ -2ℑ(ω₃/ω₁)` (the terms grow like
`e^{nπ(|ℑ(z/ω₁)| - 2ℑτ)}`; e.g. `ω₁ = 1.1 + 0.2i`, `ω₃ = 0.3 + 0.9i`,
`z/ω₁ = 0.3 - 2.5iℑτ` gives terms of size `10⁵, 10¹¹, 10²¹` at `n = 10, 20, 40`). The
acquired condition is `|ℑ(z/ω₁)| < 2ℑ(ω₃/ω₁)`.

The coefficients `a_{m,n}` of 23.9.7 are defined by the recursion 23.9.8 (`sigmaCoeff`), by
well-founded recursion on the weight `2m + 3n`.
-/

@[expose] public section

open Complex PeriodPair Asymptotics Filter Set
open scoped Real Topology

noncomputable section

namespace DLMF.Weierstrass

namespace HalfPeriods

variable (H : HalfPeriods)

/-! ### Fourier series (§23.8(i)) -/

/-- DLMF 23.8.2 (with the corrected condition `|ℑ(z/ω₁)| < 2ℑτ`), `z ∉ 𝕃`:
`ζ(z) - η₁z/ω₁ - (π/(2ω₁))cot(πz/(2ω₁)) = (2π/ω₁) ∑_{n≥1} q^{2n}/(1 - q^{2n}) sin(nπz/ω₁)`.
Corrected from the printed DLMF formula: the absolute value on `ℑ(z/ω₁)` is missing in the
printed condition, as in 23.8.1; without it the series diverges. -/
@[dlmf 23.8.E2]
theorem weierstrassZeta_fourier {z : ℂ} (hz : z ∉ H.lattice)
    (hzi : |(z / H.ω₁).im| < 2 * H.tau.im) :
    HasSum (fun n : ℕ ↦ 2 * π / H.ω₁ *
        (H.nome ^ (2 * (n + 1)) / (1 - H.nome ^ (2 * (n + 1))) *
          Complex.sin ((n + 1 : ℂ) * π * z / H.ω₁)))
      (H.weierstrassZeta z - H.eta 1 * z / H.ω₁ -
        π / (2 * H.ω₁) * Complex.cot (π * z / (2 * H.ω₁))) := by
  have hscale : (π * z / (2 * H.ω₁)).im = π / 2 * (z / H.ω₁).im := by
    rw [show π * z / (2 * H.ω₁) = (↑(π / 2) : ℂ) * (z / H.ω₁) by push_cast; ring]
    simp
  have hstrip : |(π * z / (2 * H.ω₁)).im| < π * H.tau.im := by
    rw [hscale, abs_mul, abs_of_pos (half_pos Real.pi_pos)]
    nlinarith [Real.pi_pos]
  have h := (DLMF.Theta.jacobiThetaOneTau_logDeriv H.tau_im_pos hstrip).2.mul_left
    (π / (2 * H.ω₁))
  convert h using 1
  · ext n
    simp only [HalfPeriods.nome]
    rw [show 2 * (n + 1 : ℂ) * (π * z / (2 * H.ω₁)) =
      (n + 1 : ℂ) * π * z / H.ω₁ by ring]
    ring
  · rw [H.p23R1_zeta_theta hz]
    ring



/-- Compact subsets of the convergence strip admit a common summable bound for the zeta Fourier terms. -/
private lemma weierstrassZeta_fourier_bound (H : HalfPeriods) {K : Set ℂ} (hK : IsCompact K)
    (hstrip : ∀ w ∈ K, |(w / H.ω₁).im| < 2 * H.tau.im) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℕ, ∀ w ∈ K,
      ‖2 * π / H.ω₁ * (H.nome ^ (2 * (n + 1)) / (1 - H.nome ^ (2 * (n + 1)))) *
        Complex.sin ((n + 1 : ℂ) * π * w / H.ω₁)‖ ≤ u n := by
  let f : ℂ → ℂ := fun w => π * w / (2 * H.ω₁)
  have hf : Continuous f := by dsimp only [f]; fun_prop
  obtain ⟨u, hu, hbound⟩ := (DLMF.Theta.jacobiTheta_logDeriv_series_uniform H.tau_im_pos
    (f '' K) (hK.image hf)).1 (by
      rintro _ ⟨w, hw, rfl⟩
      have hi : (f w).im = π / 2 * (w / H.ω₁).im := by
        dsimp only [f]
        rw [show π * w / (2 * H.ω₁) = (↑(π / 2) : ℂ) * (w / H.ω₁) by push_cast; ring]
        simp
      rw [hi, abs_mul, abs_of_pos (half_pos Real.pi_pos)]
      nlinarith [hstrip w hw, Real.pi_pos])
  refine ⟨fun n => ‖2 * π / H.ω₁‖ * u n, hu.mul_left _, fun n w hw => ?_⟩
  have he : 2 * π / H.ω₁ * (H.nome ^ (2 * (n + 1)) / (1 - H.nome ^ (2 * (n + 1)))) *
      Complex.sin ((n + 1 : ℂ) * π * w / H.ω₁) =
      (2 * π / H.ω₁) * ((H.nome ^ (2 * (n + 1)) / (1 - H.nome ^ (2 * (n + 1)))) *
        Complex.sin (2 * (n + 1) * f w)) := by
    dsimp only [f]
    rw [show 2 * (n + 1 : ℂ) * (π * w / (2 * H.ω₁)) =
      (n + 1 : ℂ) * π * w / H.ω₁ by ring]
    ring
  rw [he, norm_mul]
  exact mul_le_mul_of_nonneg_left (hbound n (f w) ⟨w, hw, rfl⟩).1 (norm_nonneg _)

/-- A zero of the sine prefactor would lie at a real lattice point. -/
private lemma sin_fourierArgument_ne_zero (H : HalfPeriods) {z : ℂ} (hz : z ∉ H.lattice) :
    Complex.sin (π * z / (2 * H.ω₁)) ≠ 0 := by
  intro he
  obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp he
  apply hz
  apply H.mem_lattice_iff.mpr
  refine ⟨m, 0, ?_⟩
  have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp at hm
  simp only [Int.cast_zero, mul_zero, zero_mul, add_zero]
  exact (div_eq_iff H.ω₁_ne_zero).mp hm

/-- DLMF 23.8.1 (with the corrected condition `|ℑ(z/ω₁)| < 2ℑτ`), `q = e^{iπω₃/ω₁}`, `z ∉ 𝕃`:
`℘(z) + η₁/ω₁ - (π²/(4ω₁²))csc²(πz/(2ω₁)) = -(2π²/ω₁²) ∑_{n≥1} nq^{2n}/(1 - q^{2n}) cos(nπz/ω₁)`.
Corrected from the printed DLMF formula: the printed condition lacks the absolute value on
`ℑ(z/ω₁)`; for `ℑ(z/ω₁) ≤ -2ℑτ` the series diverges (terms `10⁵, 10¹¹, 10²¹` at
`n = 10, 20, 40`). -/
@[dlmf 23.8.E1]
theorem weierstrassP_fourier {z : ℂ} (hz : z ∉ H.lattice) (hzi : |(z / H.ω₁).im| < 2 * H.tau.im) :
    HasSum (fun n : ℕ ↦ -(2 * π ^ 2 / H.ω₁ ^ 2) *
        ((n + 1 : ℂ) * H.nome ^ (2 * (n + 1)) / (1 - H.nome ^ (2 * (n + 1))) *
          Complex.cos ((n + 1 : ℂ) * π * z / H.ω₁)))
      (H.weierstrassP z + H.eta 1 / H.ω₁ -
        π ^ 2 / (4 * H.ω₁ ^ 2) * (1 / Complex.sin (π * z / (2 * H.ω₁)) ^ 2)) := by
  let T : ℕ → ℂ → ℂ := fun n w => 2 * π / H.ω₁ *
    (H.nome ^ (2 * (n + 1)) / (1 - H.nome ^ (2 * (n + 1)))) *
      Complex.sin ((n + 1 : ℂ) * π * w / H.ω₁)
  let S : Set ℂ := {w | w ∉ H.lattice ∧ |(w / H.ω₁).im| < 2 * H.tau.im}
  have hS : IsOpen S := by
    have hL : IsOpen {w : ℂ | w ∉ H.lattice} := H.periodPair.isClosed_lattice.isOpen_compl
    exact hL.inter (isOpen_lt (show Continuous (fun w : ℂ => |(w / H.ω₁).im|) by
      fun_prop) continuous_const)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS z ⟨hz, hzi⟩
  have hε2 : 0 < ε / 2 := half_pos hε
  have hK (w : ℂ) (hw : w ∈ Metric.closedBall z (ε / 2)) : w ∈ S := by
    have hw' : dist w z ≤ ε / 2 := hw
    exact hball (hw'.trans_lt (by linarith : ε / 2 < ε))
  obtain ⟨u, hu, hbound⟩ := weierstrassZeta_fourier_bound H (isCompact_closedBall z (ε / 2))
    (fun w hw => (hK w hw).2)
  have hdiff (n : ℕ) : Differentiable ℂ (T n) := by dsimp only [T]; fun_prop
  have hD := Complex.hasSum_deriv_of_summable_norm (F := T) (U := Metric.ball z (ε / 2))
    hu (fun n => (hdiff n).differentiableOn) Metric.isOpen_ball
    (fun n w hw => hbound n w (Metric.ball_subset_closedBall hw)) (Metric.mem_ball_self hε2)
  have heq : (fun w => ∑' n : ℕ, T n w) =ᶠ[𝓝 z]
      fun w => H.weierstrassZeta w - H.eta 1 * w / H.ω₁ -
        π / (2 * H.ω₁) * Complex.cot (π * w / (2 * H.ω₁)) := by
    filter_upwards [Metric.ball_mem_nhds z hε2] with w hw
    simpa only [T, mul_assoc] using (weierstrassZeta_fourier H
      (hK w (Metric.ball_subset_closedBall hw)).1 (hK w (Metric.ball_subset_closedBall hw)).2).tsum_eq
  have hsin := sin_fourierArgument_ne_zero H hz
  have hlin := ((hasDerivAt_id z).const_mul (π : ℂ)).div_const (2 * H.ω₁)
  have hcot := ((DLMF.Elementary.hasDerivAt_cot hsin).comp z hlin).const_mul
    (π / (2 * H.ω₁))
  have hder := ((hasDerivAt_weierstrassZeta H.periodPair hz).sub
    (((hasDerivAt_id z).const_mul (H.eta 1)).div_const H.ω₁)).sub hcot
  change HasDerivAt (fun w : ℂ => H.weierstrassZeta w - H.eta 1 * w / H.ω₁ -
      π / (2 * H.ω₁) * Complex.cot (π * w / (2 * H.ω₁))) _ z at hder
  have htarget := heq.deriv_eq
  rw [hder.deriv] at htarget
  rw [htarget] at hD
  have hterm (n : ℕ) : deriv (T n) z =
      (2 * π / H.ω₁ * (H.nome ^ (2 * (n + 1)) / (1 - H.nome ^ (2 * (n + 1))))) *
        (Complex.cos ((n + 1 : ℂ) * π * z / H.ω₁) * ((n + 1 : ℂ) * π / H.ω₁)) := by
    have ht := (((hasDerivAt_id z).const_mul ((n + 1 : ℂ) * π)).div_const H.ω₁).csin
    have ht' := ht.const_mul
      (2 * π / H.ω₁ * (H.nome ^ (2 * (n + 1)) / (1 - H.nome ^ (2 * (n + 1)))))
    simpa only [T, id_eq, mul_one] using! ht'.deriv
  have h := hD.neg
  convert h using 1
  · ext n
    rw [hterm]
    ring
  · simp only [HalfPeriods.weierstrassP, DLMF.Elementary.csc] at *
    ring


/-! ### Series of cosecants and cotangents (§23.8(ii)) -/

/-- DLMF 23.8.3: `℘(z) = -η₁/ω₁ + (π²/(4ω₁²)) ∑_{n ∈ ℤ} csc²(π(z + 2nω₃)/(2ω₁))`, `z ∉ 𝕃`. -/
@[dlmf 23.8.E3]
theorem weierstrassP_csc_series {z : ℂ} (hz : z ∉ H.lattice) :
    HasSum (fun n : ℤ ↦ π ^ 2 / (4 * H.ω₁ ^ 2) *
        (1 / Complex.sin (π * (z + 2 * n * H.ω₃) / (2 * H.ω₁)) ^ 2))
      (H.weierstrassP z + H.eta 1 / H.ω₁) := by
  sorry

/-- DLMF 23.8.4: `ζ(z) = η₁z/ω₁ + (π/(2ω₁)) ∑_{n ∈ ℤ} cot(π(z + 2nω₃)/(2ω₁))` with the terms
`n` and `-n` bracketed (Eisenstein summation), `z ∉ 𝕃`. -/
@[dlmf 23.8.E4]
theorem weierstrassZeta_cot_series {z : ℂ} (hz : z ∉ H.lattice) :
    HasSum (fun n : ℕ ↦ π / (2 * H.ω₁) *
        (Complex.cot (π * (z + 2 * (n + 1) * H.ω₃) / (2 * H.ω₁)) +
          Complex.cot (π * (z - 2 * (n + 1) * H.ω₃) / (2 * H.ω₁))))
      (H.weierstrassZeta z - H.eta 1 * z / H.ω₁ -
        π / (2 * H.ω₁) * Complex.cot (π * z / (2 * H.ω₁))) := by
  sorry

/-- DLMF 23.8.5: `η₁ = (π²/(2ω₁)) (1/6 + ∑_{n≥1} csc²(nπω₃/ω₁))`. -/
@[dlmf 23.8.E5]
theorem eta_one_csc_series :
    HasSum (fun n : ℕ ↦ π ^ 2 / (2 * H.ω₁) *
        (1 / Complex.sin ((n + 1 : ℂ) * π * H.ω₃ / H.ω₁) ^ 2))
      (H.eta 1 - π ^ 2 / (2 * H.ω₁) * (1 / 6)) := by
  sorry

/-! ### Infinite products (§23.8(iii)) -/

/-- DLMF 23.8.7: `σ(z) = (2ω₁/π) exp(η₁z²/(2ω₁)) sin(πz/(2ω₁))
∏_{n≥1} sin(π(2nω₃ + z)/(2ω₁)) sin(π(2nω₃ - z)/(2ω₁))/sin²(πnω₃/ω₁)`, `z ∈ ℂ`. -/
@[dlmf 23.8.E7]
theorem weierstrassSigma_sin_prod (z : ℂ) :
    Multipliable (fun n : ℕ ↦ Complex.sin (π * (2 * (n + 1) * H.ω₃ + z) / (2 * H.ω₁)) *
        Complex.sin (π * (2 * (n + 1) * H.ω₃ - z) / (2 * H.ω₁)) /
          Complex.sin (π * (n + 1) * H.ω₃ / H.ω₁) ^ 2) ∧
    H.weierstrassSigma z = 2 * H.ω₁ / π * cexp (H.eta 1 * z ^ 2 / (2 * H.ω₁)) *
      Complex.sin (π * z / (2 * H.ω₁)) *
      ∏' n : ℕ, Complex.sin (π * (2 * (n + 1) * H.ω₃ + z) / (2 * H.ω₁)) *
        Complex.sin (π * (2 * (n + 1) * H.ω₃ - z) / (2 * H.ω₁)) /
          Complex.sin (π * (n + 1) * H.ω₃ / H.ω₁) ^ 2 := by
  obtain ⟨hm, he⟩ := DLMF.Theta.jacobiThetaOneTau_hasProd_sin
    (π * z / (2 * H.ω₁)) H.tau_im_pos
  have hω := H.ω₁_ne_zero
  have hD := H.p23R1_thetaOneDeriv_ne_zero
  have hterm (n : ℕ) :
      Complex.sin ((n + 1 : ℂ) * π * H.tau + π * z / (2 * H.ω₁)) *
        Complex.sin ((n + 1 : ℂ) * π * H.tau - π * z / (2 * H.ω₁)) /
          Complex.sin ((n + 1 : ℂ) * π * H.tau) ^ 2 =
      Complex.sin (π * (2 * (n + 1) * H.ω₃ + z) / (2 * H.ω₁)) *
        Complex.sin (π * (2 * (n + 1) * H.ω₃ - z) / (2 * H.ω₁)) /
          Complex.sin (π * (n + 1) * H.ω₃ / H.ω₁) ^ 2 := by
    rw [HalfPeriods.tau]
    congr 2 <;> field_simp
  refine ⟨hm.congr hterm, ?_⟩
  rw [H.weierstrassSigma_eq_theta, he, tprod_congr hterm]
  field_simp
  congr 1
  apply tprod_congr
  intro n
  congr 2 <;> ring_nf


/-- DLMF 23.8.6: `σ(z) = (2ω₁/π) exp(η₁z²/(2ω₁)) sin(πz/(2ω₁))
∏_{n≥1} (1 - 2q^{2n}cos(πz/ω₁) + q^{4n})/(1 - q^{2n})²`, `z ∈ ℂ`.
Convergence and the product identity are stated separately so zeros of the sine prefactor
are retained. Dividing by that prefactor would incorrectly assert product value zero at `z=0`. -/
@[dlmf 23.8.E6]
theorem weierstrassSigma_prod (z : ℂ) :
    Multipliable (fun n : ℕ ↦ (1 - 2 * H.nome ^ (2 * (n + 1)) * Complex.cos (π * z / H.ω₁) +
        H.nome ^ (4 * (n + 1))) / (1 - H.nome ^ (2 * (n + 1))) ^ 2)
      ∧
    H.weierstrassSigma z = 2 * H.ω₁ / π * cexp (H.eta 1 * z ^ 2 / (2 * H.ω₁)) *
      Complex.sin (π * z / (2 * H.ω₁)) *
      ∏' n : ℕ, (1 - 2 * H.nome ^ (2 * (n + 1)) * Complex.cos (π * z / H.ω₁) +
        H.nome ^ (4 * (n + 1))) / (1 - H.nome ^ (2 * (n + 1))) ^ 2 := by
  obtain ⟨hm, he⟩ := H.weierstrassSigma_sin_prod z
  have hω := H.ω₁_ne_zero
  have hterm (n : ℕ) :
      Complex.sin (π * (2 * (n + 1) * H.ω₃ + z) / (2 * H.ω₁)) *
        Complex.sin (π * (2 * (n + 1) * H.ω₃ - z) / (2 * H.ω₁)) /
          Complex.sin (π * (n + 1) * H.ω₃ / H.ω₁) ^ 2 =
      (1 - 2 * H.nome ^ (2 * (n + 1)) * Complex.cos (π * z / H.ω₁) +
        H.nome ^ (4 * (n + 1))) / (1 - H.nome ^ (2 * (n + 1))) ^ 2 := by
    let a := π * (n + 1) * H.ω₃ / H.ω₁
    let w := π * z / (2 * H.ω₁)
    have hexp : cexp (2 * I * a) = H.nome ^ (2 * (n + 1)) := by
      rw [HalfPeriods.nome, ← Complex.exp_nat_mul]
      congr 1
      dsimp [a, HalfPeriods.tau]
      push_cast
      ring
    have hne : 1 - cexp (2 * I * a) ≠ 0 := by
      rw [hexp]
      exact DLMF.QSeries.one_sub_ne_zero_of_norm_lt_one
        (DLMF.Theta.p20R1_norm_nome_pow_lt_one H.tau_im_pos (by omega))
    have h := DLMF.Theta.p20R1_sin_ratio a w hne
    have hp : a + w = π * (2 * (n + 1) * H.ω₃ + z) / (2 * H.ω₁) := by
      dsimp [a, w]
      field_simp
    have hn : a - w = π * (2 * (n + 1) * H.ω₃ - z) / (2 * H.ω₁) := by
      dsimp [a, w]
      field_simp
    have hw : 2 * w = π * z / H.ω₁ := by dsimp [w]; field_simp
    rw [hp, hn, hw, hexp] at h
    convert h using 1
    rw [← pow_mul]
    congr 3
    ring
  exact ⟨hm.congr hterm, he.trans (by rw [tprod_congr hterm])⟩


end HalfPeriods

/-! ### Laurent series (§23.9) -/

/-- The Laurent coefficients `c_n = (2n - 1) ∑_{w ∈ 𝕃∖{0}} w^{-2n}` (DLMF 23.9.1), `n ≥ 2`
(Mathlib's `G (2n)` sums over `𝕃` with the `w = 0` term `0`). -/
@[dlmf 23.9.E1]
def laurentCoeff (L : PeriodPair) (n : ℕ) : ℂ := (2 * n - 1) * L.G (2 * n)

/-- DLMF 23.9.4: `c₂ = g₂/20`. -/
@[dlmf 23.9.E4]
theorem laurentCoeff_two (L : PeriodPair) : laurentCoeff L 2 = L.g₂ / 20 := by
  simp only [laurentCoeff, PeriodPair.g₂]; push_cast; ring

/-- DLMF 23.9.4: `c₃ = g₃/28`. -/
@[dlmf 23.9.E4]
theorem laurentCoeff_three (L : PeriodPair) : laurentCoeff L 3 = L.g₃ / 28 := by
  simp only [laurentCoeff, PeriodPair.g₃]; push_cast; ring

/-- DLMF 23.9.2: `℘(z) = 1/z² + ∑_{n≥2} c_n z^{2n-2}` for `0 < |z| < |z₀|`, `z₀` a nearest
nonzero lattice point. -/
@[dlmf 23.9.E2]
theorem weierstrassP_laurent (L : PeriodPair) {z : ℂ} (hz0 : z ≠ 0)
    (hz : ∀ w ∈ L.lattice, w ≠ 0 → ‖z‖ < ‖w‖) :
    HasSum (fun n : ℕ ↦ laurentCoeff L (n + 2) * z ^ (2 * (n + 2) - 2)) (℘[L] z - 1 / z ^ 2) := by
  clear hz0
  have h := L.weierstrassPExceptSeries_hasSum 0 z 0 (fun l hl => by simpa using hz l l.2 hl)
  have hdef := L.weierstrassPExcept_def ⟨0, zero_mem _⟩ z
  simp only [sub_zero] at hdef h
  rw [show ℘[L] z - 1 / z ^ 2 = L.weierstrassPExcept 0 z by rw [hdef]; simp; ring]
  have hcoeff : ∀ i, (L.weierstrassPExceptSeries 0 0).coeff i =
      if i = 0 then 0 else (i + 1) * L.G (i + 2) := by
    intro i
    simp only [weierstrassPExceptSeries, FormalMultilinearSeries.coeff_ofScalars]
    split_ifs with hi h0
    · simp
    · simp [sumInvPow, PeriodPair.G]
    · exact absurd (zero_mem _) h0
  have h2 := (Function.Injective.hasSum_iff
    (f := fun i => (L.weierstrassPExceptSeries 0 0).coeff i * z ^ i)
    (g := fun n : ℕ => 2 * n + 2) (fun a b hab => by simp only at hab; omega) ?_).mpr h
  · convert h2 using 1
    funext n
    simp only [Function.comp_apply, hcoeff, laurentCoeff]
    simp only [show ¬ (2 * n + 2 = 0) by omega, ↓reduceIte]
    rw [show 2 * (n + 2) - 2 = 2 * n + 2 by omega, show 2 * n + 2 + 2 = 2 * (n + 2) by ring]
    push_cast; ring
  · intro i hi
    rw [hcoeff]
    split_ifs with h0
    · simp
    · have hodd : Odd i := by
        rcases Nat.even_or_odd i with ⟨k, hk⟩ | ho
        · exact absurd ⟨k - 1, by simp only; omega⟩ hi
        · exact ho
      rw [L.G_eq_zero_of_odd _ (by rcases hodd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩)]
      simp

/-- DLMF 23.9.3: `ζ(z) = 1/z - ∑_{n≥2} c_n z^{2n-1}/(2n - 1)` for `0 < |z| < |z₀|`. -/
@[dlmf 23.9.E3]
theorem weierstrassZeta_laurent (L : PeriodPair) {z : ℂ} (hz0 : z ≠ 0)
    (hz : ∀ w ∈ L.lattice, w ≠ 0 → ‖z‖ < ‖w‖) :
    HasSum (fun n : ℕ ↦ -(laurentCoeff L (n + 2) / (2 * (n + 2) - 1) * z ^ (2 * (n + 2) - 1)))
      (weierstrassZeta L z - 1 / z) := by
  clear hz0
  set T : ℕ → L.lattice → ℂ := fun k l => -z ^ (k + 2) * ((l : ℂ) ^ (k + 3))⁻¹ with hTdef
  -- summability of the double series, from Mathlib's bound for `℘`
  have hW := L.summable_weierstrassPExceptSummand 0 z 0 (fun l hl => by simpa using hz l l.2 hl)
  have hinj : Function.Injective (fun p : ℕ × L.lattice => (p.1 + 1, p.2)) := by
    intro p q h; simp only [Prod.mk.injEq, add_left_inj] at h; exact Prod.ext h.1 h.2
  have hW' := (summable_norm_iff.mpr (hW.comp_injective hinj)).mul_left ‖z‖
  have hT : Summable (Function.uncurry T) := by
    refine Summable.of_norm_bounded hW' fun p => ?_
    obtain ⟨k, l⟩ := p
    simp only [Function.uncurry_apply_pair, Function.comp_apply, hTdef,
      weierstrassPExceptSummand]
    by_cases hl : (l : ℂ) = 0
    · simp [hl]
    · simp only [hl, ite_false, sub_zero, norm_mul, norm_neg, norm_pow, norm_inv]
      simp only [Pi.zero_apply, sub_zero, norm_mul, norm_zpow]
      rw [zpow_neg, zpow_natCast, show k + 1 + 2 = k + 3 by ring]
      have h1 : (1 : ℝ) ≤ ‖((k + 1 : ℕ) : ℂ) + 1‖ := by
        rw [show ((k + 1 : ℕ) : ℂ) + 1 = ((k + 2 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
        norm_cast; omega
      have h2 : 0 ≤ ‖z‖ ^ (k + 2) * (‖(l : ℂ)‖ ^ (k + 3))⁻¹ := by positivity
      calc ‖z‖ ^ (k + 2) * (‖(l : ℂ)‖ ^ (k + 3))⁻¹
          ≤ ‖((k + 1 : ℕ) : ℂ) + 1‖ * (‖z‖ ^ (k + 2) * (‖(l : ℂ)‖ ^ (k + 3))⁻¹) :=
            le_mul_of_one_le_left h2 h1
        _ = _ := by ring
  -- the fibres over `l`: geometric series
  have hfib : ∀ l : L.lattice, HasSum (fun k => T k l)
      ((1 / (z - l) + 1 / l + z / l ^ 2) - if (l : ℂ) = 0 then 1 / z else 0) := by
    intro l
    by_cases hl : (l : ℂ) = 0
    · simp [hTdef, hl]
    · have hzl : ‖z‖ < ‖(l : ℂ)‖ := hz l l.2 hl
      have hlz : z ≠ l := fun h => by rw [h] at hzl; exact lt_irrefl _ hzl
      have hq : ‖z / l‖ < 1 := by
        rw [norm_div, div_lt_one (norm_pos_iff.mpr hl)]; exact hzl
      have hg := (hasSum_geometric_of_norm_lt_one hq).mul_left (-z ^ 2 / (l : ℂ) ^ 3)
      simp only [hl, ite_false, sub_zero]
      rw [wp23_zeta_summand z l hl hlz]
      convert hg using 1
      · funext k
        simp only [hTdef, div_pow]
        field_simp
        ring
      · have h1 : (1 : ℂ) - z / l ≠ 0 := by
          intro h; apply hlz
          have : z / l = 1 := by linear_combination -h
          field_simp at this; exact this
        have h2 : (z : ℂ) - l ≠ 0 := sub_ne_zero.mpr hlz
        field_simp
        ring
  have hS : HasSum (fun l : L.lattice => 1 / (z - l) + 1 / l + z / l ^ 2) (weierstrassZeta L z) :=
    (hasSumLocallyUniformly_weierstrassZeta L).hasSum
  have hite : HasSum (fun l : L.lattice => if (l : ℂ) = 0 then 1 / z else 0) (1 / z) := by
    convert hasSum_ite_eq (⟨0, zero_mem _⟩ : L.lattice) (1 / z) using 1
    funext l
    simp only [Subtype.ext_iff]
  have htot := hS.sub hite
  have hswap : ∑' p : ℕ × L.lattice, Function.uncurry T p =
      weierstrassZeta L z - 1 / z := by
    rw [← (Equiv.prodComm L.lattice ℕ).tsum_eq]
    have hsw : Summable (fun q : L.lattice × ℕ =>
        Function.uncurry T ((Equiv.prodComm L.lattice ℕ) q)) :=
      (Equiv.prodComm L.lattice ℕ).summable_iff.mpr hT
    rw [hsw.tsum_prod' (fun l => (hfib l).summable)]
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair]
    rw [tsum_congr fun l => (hfib l).tsum_eq]
    exact htot.tsum_eq
  have hk := hT.hasSum.prod_fiberwise (fun k => (hT.prod_factor k).hasSum)
  rw [hswap] at hk
  have hk' : HasSum (fun k : ℕ => -z ^ (k + 2) * L.G (k + 3)) (weierstrassZeta L z - 1 / z) := by
    convert hk using 1
    funext k
    simp only [Function.uncurry_apply_pair, hTdef, PeriodPair.G]
    rw [tsum_mul_left]
  have hinj2 : Function.Injective (fun n : ℕ => 2 * n + 1) := fun a b h => by
    simp only at h; omega
  refine ((hinj2.hasSum_iff ?_).mpr hk').congr_fun ?_
  · intro k hk
    have heven : Even k := by
      rcases Nat.even_or_odd k with he | ⟨m, hm⟩
      · exact he
      · exact absurd ⟨m, by simp only; omega⟩ hk
    rw [L.G_eq_zero_of_odd _ (by rcases heven with ⟨m, hm⟩; exact ⟨m + 1, by omega⟩)]
    simp
  · intro n
    simp only [Function.comp_apply, laurentCoeff]
    have hne : (2 * ((n + 2 : ℕ) : ℂ) - 1) ≠ 0 := by
      have : (2 * ((n + 2 : ℕ) : ℂ) - 1) = ((2 * n + 3 : ℕ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast (by omega : 2 * n + 3 ≠ 0)
    rw [show 2 * (n + 2) - 1 = 2 * n + 1 + 2 by omega, show 2 * (n + 2) = 2 * n + 1 + 3 by omega]
    push_cast at hne ⊢
    field_simp


section p3wRecursion

open Topology Filter
open scoped Nat

/-- The ODE `z² g'' = 12 g + 6 z² g² - (g₂/2) z²` for `g = ℘ - 1/z²`, near `0`. -/
lemma p3w_regular_ode (L : PeriodPair) :
    (fun z => z ^ 2 * deriv (deriv ℘[L - (0 : ℂ)]) z) =ᶠ[𝓝 0]
      fun z => 12 * ℘[L - (0 : ℂ)] z + 6 * z ^ 2 * ℘[L - (0 : ℂ)] z ^ 2 - L.g₂ / 2 * z ^ 2 := by
  set U : Set ℂ := (L.lattice \ {(0 : ℂ)})ᶜ
  have hU : IsOpen U := L.isOpen_compl_lattice_sdiff
  have h0U : (0 : ℂ) ∈ U := by simp [U]
  filter_upwards [hU.mem_nhds h0U] with z hz
  by_cases hz0 : z = 0
  · subst hz0; simp
  have hzL : z ∉ L.lattice := fun h => hz ⟨h, hz0⟩
  -- `deriv g = ℘'[L - 0]` near `z`
  have hd : deriv ℘[L - (0 : ℂ)] =ᶠ[𝓝 z] ℘'[L - (0 : ℂ)] :=
    eventually_of_mem (hU.mem_nhds hz) fun w hw =>
      L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hw
  have h0 : (0 : ℂ) = ((0 : L.lattice) : ℂ) := rfl
  have hdp : ℘'[L - (0 : ℂ)] = fun w => ℘'[L] w + 2 / w ^ 3 := by
    funext w; rw [h0, L.derivWeierstrassPExcept_def]; simp
  have hp : ℘[L - (0 : ℂ)] z = ℘[L] z - 1 / z ^ 2 := by
    rw [h0, L.weierstrassPExcept_def]; simp [sub_eq_add_neg]
  have hD : HasDerivAt (fun w => ℘'[L] w + 2 / w ^ 3)
      (6 * ℘[L] z ^ 2 - L.g₂ / 2 + (-(6 / z ^ 4))) z := by
    have a := (L.analyticOnNhd_derivWeierstrassP z hzL).differentiableAt.hasDerivAt
    rw [deriv_derivWeierstrassP L hzL] at a
    have b : HasDerivAt (fun w : ℂ => 2 / w ^ 3) (-(6 / z ^ 4)) z := by
      have := ((hasDerivAt_pow 3 z).inv (pow_ne_zero 3 hz0)).const_mul 2
      convert this using 1
      · funext w; simp [div_eq_mul_inv]
      · field_simp; ring
    exact a.add b
  rw [hd.deriv_eq, hdp, hD.deriv, hp]
  field_simp
  ring

/-- `(z² f)^{(N+2)}(0) = (N+2)(N+1) f^{(N)}(0)`. -/
lemma p3w_iteratedDeriv_sq_mul {f : ℂ → ℂ} {N : ℕ} (hf : ContDiffAt ℂ (N + 2) f 0) :
    iteratedDeriv (N + 2) (fun z => z ^ 2 * f z) 0 = (N + 2) * (N + 1) * iteratedDeriv N f 0 := by
  have hp : ContDiffAt ℂ (N + 2) (fun z : ℂ => z ^ 2) 0 := by fun_prop
  rw [show (fun z => z ^ 2 * f z) = (fun z : ℂ => z ^ 2) * f from rfl,
    iteratedDeriv_mul hp hf]
  simp only [iteratedDeriv_fun_pow_zero]
  rw [Finset.sum_eq_single 2]
  · simp only [ite_true, Nat.cast_choose_two, show N + 2 - 2 = N by omega]
    push_cast; ring
  · intro b _ hb; simp [hb]
  · intro h; simp at h

/-- Splitting a sum over `range (2K+1)` into even and odd indices. -/
lemma p3w_sum_range_even_odd (f : ℕ → ℂ) (K : ℕ) :
    ∑ i ∈ Finset.range (2 * K + 1), f i =
      ∑ j ∈ Finset.range (K + 1), f (2 * j) + ∑ j ∈ Finset.range K, f (2 * j + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) + 1 = 2 * K + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ (fun j => f (2 * j)) (K + 1),
      Finset.sum_range_succ (fun j => f (2 * j + 1)) K,
      show 2 * (K + 1) = 2 * K + 1 + 1 by ring]
    ring

attribute [local fun_prop] AnalyticAt.contDiffAt in
/-- DLMF 23.9.5: `c_n = 3/((2n + 1)(n - 3)) ∑_{m=2}^{n-2} c_m c_{n-m}`, `n ≥ 4`. -/
@[dlmf 23.9.E5]
theorem laurentCoeff_recursion (L : PeriodPair) {n : ℕ} (hn : 4 ≤ n) :
    laurentCoeff L n = 3 / ((2 * n + 1) * (n - 3)) *
      ∑ m ∈ Finset.Icc 2 (n - 2), laurentCoeff L m * laurentCoeff L (n - m) := by
  obtain ⟨K, rfl⟩ : ∃ K, n = K + 2 := ⟨n - 2, by omega⟩
  set g := ℘[L - (0 : ℂ)] with hg
  have hga : AnalyticAt ℂ g 0 := L.analyticAt_weierstrassPExcept 0
  have hg2 : AnalyticAt ℂ (deriv (deriv g)) 0 := by
    have hU := L.analyticOnNhd_weierstrassPExcept 0
    exact (hU.deriv.deriv) 0 (by simp)
  have ha : ∀ i, iteratedDeriv i g 0 =
      if i = 0 then 0 else ((i + 1)! : ℂ) * L.G (i + 2) := by
    intro i; rw [hg, L.iteratedDeriv_weierstrassPExcept_self, L.sumInvPow_zero]; simp
  have key := (p3w_regular_ode L).iteratedDeriv_eq (2 * K + 2)
  rw [p3w_iteratedDeriv_sq_mul (hg2.contDiffAt)] at key
  rw [show iteratedDeriv (2 * K) (deriv (deriv g)) 0 = iteratedDeriv (2 * K + 2) g 0 by
    rw [iteratedDeriv_succ', iteratedDeriv_succ']] at key
  have e2 : iteratedDeriv (2 * K + 2) (fun z => 6 * z ^ 2 * g z ^ 2) 0 =
      6 * ((2 * K + 2) * (2 * K + 1) * ∑ i ∈ Finset.range (2 * K + 1),
        ((2 * K).choose i : ℂ) * iteratedDeriv i g 0 * iteratedDeriv (2 * K - i) g 0) := by
    rw [show (fun z => 6 * z ^ 2 * g z ^ 2) = fun z => 6 * (z ^ 2 * (g * g) z) by
      funext z; simp; ring]
    rw [iteratedDeriv_const_mul _ (by fun_prop), p3w_iteratedDeriv_sq_mul (by fun_prop),
      iteratedDeriv_mul (by fun_prop) (by fun_prop)]
    push_cast; ring
  have e1 : iteratedDeriv (2 * K + 2)
      (fun z => 12 * g z + 6 * z ^ 2 * g z ^ 2 - L.g₂ / 2 * z ^ 2) 0 =
      12 * iteratedDeriv (2 * K + 2) g 0 +
        iteratedDeriv (2 * K + 2) (fun z => 6 * z ^ 2 * g z ^ 2) 0 -
        L.g₂ / 2 * iteratedDeriv (2 * K + 2) (fun z : ℂ => z ^ 2) 0 := by
    rw [iteratedDeriv_fun_sub (by fun_prop) (by fun_prop),
      iteratedDeriv_fun_add (by fun_prop) (by fun_prop), iteratedDeriv_const_mul _ (by fun_prop),
      iteratedDeriv_const_mul _ (by fun_prop)]
  rw [e1, e2, iteratedDeriv_fun_pow_zero, ite_eq_right (by omega)] at key
  -- the convolution sum
  have hT : ∑ i ∈ Finset.range (2 * K + 1),
      ((2 * K).choose i : ℂ) * iteratedDeriv i g 0 * iteratedDeriv (2 * K - i) g 0 =
      ((2 * K)! : ℂ) * ∑ m ∈ Finset.Icc 2 (K + 2 - 2),
        laurentCoeff L m * laurentCoeff L (K + 2 - m) := by
    rw [p3w_sum_range_even_odd]
    have hodd : ∑ j ∈ Finset.range K, ((2 * K).choose (2 * j + 1) : ℂ) *
        iteratedDeriv (2 * j + 1) g 0 * iteratedDeriv (2 * K - (2 * j + 1)) g 0 = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ha, ite_eq_right (by omega), L.G_eq_zero_of_odd _ ⟨j + 1, by ring⟩]
      simp
    rw [hodd, add_zero, show K + 2 - 2 = K by omega, ← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ', Finset.mul_sum]
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [Finset.sum_range_succ, show K' + 1 + 1 - 2 = K' by omega]
    simp only [mul_zero, ha, ite_true, zero_mul, mul_zero, add_zero]
    have hlast : (2 * (K' + 1)) - 2 * (K' + 1) = 0 := by omega
    rw [hlast]
    simp only [ite_true, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    obtain ⟨r, rfl⟩ : ∃ r, K' = j + 1 + r := ⟨K' - (j + 1), by omega⟩
    rw [ite_eq_right (by omega), ite_eq_right (by omega),
      show 2 * (j + 1 + r + 1) - 2 * (j + 1) = 2 * r + 2 by omega,
      show j + 1 + r + 1 + 2 - (2 + j) = r + 2 by omega]
    have hc := Nat.add_choose_mul_factorial_mul_factorial (2 * r + 2) (2 * (j + 1))
    rw [show 2 * r + 2 + 2 * (j + 1) = 2 * (j + 1 + r + 1) by ring] at hc
    have hc' : ((2 * (j + 1 + r + 1)).choose (2 * (j + 1)) : ℂ) * ((2 * (j + 1))! : ℂ) *
        ((2 * r + 2)! : ℂ) = ((2 * (j + 1 + r + 1))! : ℂ) := by
      rw [← hc]; push_cast; ring
    rw [Nat.factorial_succ (2 * (j + 1)), Nat.factorial_succ (2 * r + 2), ← hc']
    simp only [laurentCoeff]
    push_cast
    ring_nf
  rw [hT, ha, ite_eq_right (by omega), show 2 * K + 2 + 2 = 2 * (K + 2) by ring,
    Nat.factorial_succ (2 * K + 2), Nat.factorial_succ (2 * K + 1),
    Nat.factorial_succ (2 * K)] at key
  rw [show laurentCoeff L (K + 2) = (2 * ((K + 2 : ℕ) : ℂ) - 1) * L.G (2 * (K + 2)) from rfl]
  generalize ∑ m ∈ Finset.Icc 2 (K + 2 - 2), laurentCoeff L m * laurentCoeff L (K + 2 - m) = T
    at key ⊢
  generalize L.G (2 * (K + 2)) = G at key ⊢
  have hF : ((2 * K)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hK : (K : ℂ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast (show 2 ≤ K by omega)
    intro h; have := congrArg Complex.re h; simp at this; linarith
  push_cast at key ⊢
  have h5 : (2 * (K : ℂ) + 5) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [(K.cast_nonneg : (0:ℝ) ≤ K)]
  have h2 : (2 * (K : ℂ) + 2) * (2 * K + 1) ≠ 0 := by
    refine mul_ne_zero ?_ ?_ <;> intro h <;> have := congrArg Complex.re h <;> simp at this <;>
      linarith [(K.cast_nonneg : (0:ℝ) ≤ K)]
  have hcore : (2 * ((2 * (K : ℂ) + 2) * (2 * K + 1)) * ((2 * K)! : ℂ)) *
      ((2 * K + 3) * G * (2 * K + 5) * (K - 1)) =
      (2 * ((2 * (K : ℂ) + 2) * (2 * K + 1)) * ((2 * K)! : ℂ)) * (3 * T) := by
    linear_combination key
  have hc := mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero h2) hF) hcore
  rw [show (K : ℂ) + 2 - 3 = K - 1 by ring, show 2 * ((K : ℂ) + 2) + 1 = 2 * K + 5 by ring]
  field_simp
  linear_combination hc

end p3wRecursion

namespace HalfPeriods

variable (H : HalfPeriods)

section p3wHalfPeriod

open Topology Filter

attribute [local fun_prop] AnalyticAt.contDiffAt in
/-- The ODE recursion for the derivatives of `℘` at a point off the lattice. -/
lemma p3w_iteratedDeriv_wp_succ_succ {x : ℂ} (hx : x ∉ H.lattice) (k : ℕ) :
    iteratedDeriv (k + 2) H.weierstrassP x =
      6 * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℂ) * iteratedDeriv i H.weierstrassP x *
        iteratedDeriv (k - i) H.weierstrassP x - if k = 0 then H.g₂ / 2 else 0 := by
  have hU : IsOpen (H.lattice : Set ℂ)ᶜ := H.periodPair.isClosed_lattice.isOpen_compl
  have hode : deriv (deriv H.weierstrassP) =ᶠ[𝓝 x]
      fun z => 6 * (H.weierstrassP * H.weierstrassP) z - H.g₂ / 2 := by
    filter_upwards [hU.mem_nhds hx] with z hz
    simp only [HalfPeriods.weierstrassP, PeriodPair.deriv_weierstrassP, Pi.mul_apply]
    rw [deriv_derivWeierstrassP _ hz]; ring
  have hPa : AnalyticOnNhd ℂ H.weierstrassP (H.lattice : Set ℂ)ᶜ :=
    H.periodPair.analyticOnNhd_weierstrassP
  have ha : AnalyticAt ℂ H.weierstrassP x := hPa x hx
  rw [iteratedDeriv_succ', iteratedDeriv_succ', hode.iteratedDeriv_eq,
    iteratedDeriv_fun_sub (by fun_prop) (by fun_prop), iteratedDeriv_const_mul _ (by fun_prop),
    iteratedDeriv_mul (by fun_prop) (by fun_prop), iteratedDeriv_const]

/-- DLMF 23.9.6: as `t → 0`, for `j = 1, 2, 3`,
`℘(ω_j + t) = e_j + (3e_j² - 5c₂)t² + (10c₂e_j + 21c₃)t⁴ + (7c₂e_j² + 21c₃e_j + 5c₂²)t⁶ + O(t⁸)`. -/
@[dlmf 23.9.E6]
theorem weierstrassP_halfPeriod_expansion {j : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    (fun t : ℂ ↦ H.weierstrassP (H.halfPeriod j + t) -
      (H.e j + (3 * H.e j ^ 2 - 5 * laurentCoeff H.periodPair 2) * t ^ 2 +
        (10 * laurentCoeff H.periodPair 2 * H.e j + 21 * laurentCoeff H.periodPair 3) * t ^ 4 +
        (7 * laurentCoeff H.periodPair 2 * H.e j ^ 2 +
          21 * laurentCoeff H.periodPair 3 * H.e j +
          5 * laurentCoeff H.periodPair 2 ^ 2) * t ^ 6)) =O[nhds 0] fun t ↦ t ^ 8 := by
  have hω := H.halfPeriod_notMem hj
  have ha : AnalyticAt ℂ H.weierstrassP (H.halfPeriod j) :=
    H.periodPair.analyticOnNhd_weierstrassP _ hω
  have hrec := H.p3w_iteratedDeriv_wp_succ_succ hω
  have p0 : iteratedDeriv 0 H.weierstrassP (H.halfPeriod j) = H.e j := by
    simp [HalfPeriods.e]
  have p1 : iteratedDeriv 1 H.weierstrassP (H.halfPeriod j) = 0 := by
    simp only [iteratedDeriv_one, PeriodPair.deriv_weierstrassP]
    exact H.derivWeierstrassP_halfPeriod hj
  have p2 : iteratedDeriv 2 H.weierstrassP (H.halfPeriod j) = 6 * H.e j ^ 2 - H.g₂ / 2 := by
    have := hrec 0; norm_num [Finset.sum_range_succ, p0] at this; rw [this]; ring
  have p3 : iteratedDeriv 3 H.weierstrassP (H.halfPeriod j) = 0 := by
    have := hrec 1; norm_num [Finset.sum_range_succ, p0, p1] at this; exact this
  have p4 : iteratedDeriv 4 H.weierstrassP (H.halfPeriod j) =
      12 * H.e j * (6 * H.e j ^ 2 - H.g₂ / 2) := by
    have := hrec 2; norm_num [Finset.sum_range_succ, p0, p1, p2] at this; rw [this]; ring
  have p5 : iteratedDeriv 5 H.weierstrassP (H.halfPeriod j) = 0 := by
    have := hrec 3; norm_num [Finset.sum_range_succ, p0, p1, p2, p3] at this; exact this
  have p6 : iteratedDeriv 6 H.weierstrassP (H.halfPeriod j) =
      144 * H.e j ^ 2 * (6 * H.e j ^ 2 - H.g₂ / 2) + 36 * (6 * H.e j ^ 2 - H.g₂ / 2) ^ 2 := by
    have := hrec 4
    norm_num [Finset.sum_range_succ, p0, p1, p2, p3, p4, Nat.choose] at this; rw [this]; ring
  have p7 : iteratedDeriv 7 H.weierstrassP (H.halfPeriod j) = 0 := by
    have := hrec 5; norm_num [Finset.sum_range_succ, p0, p1, p2, p3, p4, p5, p6] at this
    exact this
  have hbig := ha.hasFPowerSeriesAt.isBigO_sub_partialSum_pow 8
  have hcub := H.e_root_cubic hj
  have c2 := laurentCoeff_two H.periodPair
  have c3 := laurentCoeff_three H.periodPair
  have hn : (fun y : ℂ => ‖y‖ ^ 8) =O[𝓝 0] fun t : ℂ => t ^ 8 :=
    IsBigO.of_bound 1 (Eventually.of_forall fun y => by simp [norm_pow])
  refine (hbig.trans hn).congr_left fun t => ?_
  simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_range_zero,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, p0, p1, p2, p3, p4, p5, p6, p7]
  rw [c2, c3]
  norm_num [Nat.factorial]
  linear_combination (3 / 4 * t ^ 4 * (H.e j * t ^ 2 + 1)) * hcub

end p3wHalfPeriod

end HalfPeriods

/-- The coefficients `a_{m,n}` of the power series of `σ` (DLMF 23.9.8): `a_{0,0} = 1`,
`a_{m,n} = 0` if `m < 0` or `n < 0`, and for `(m, n) ≠ (0, 0)`
`a_{m,n} = 3(m+1)a_{m+1,n-1} + (16/3)(n+1)a_{m-2,n+1} - (1/3)(2m+3n-1)(4m+6n-1)a_{m-1,n}`.
The recursion is well founded in the weight `2m + 3n`. -/
@[dlmf 23.9.E8]
def sigmaCoeff (m n : ℕ) : ℚ :=
  if m = 0 ∧ n = 0 then 1 else
    (if hn : 1 ≤ n then 3 * (m + 1) * sigmaCoeff (m + 1) (n - 1) else 0) +
    (if hm : 2 ≤ m then 16 / 3 * (n + 1) * sigmaCoeff (m - 2) (n + 1) else 0) -
    (if hm' : 1 ≤ m then 1 / 3 * (2 * m + 3 * n - 1) * (4 * m + 6 * n - 1) *
      sigmaCoeff (m - 1) n else 0)
termination_by 2 * m + 3 * n
decreasing_by all_goals omega

/-- DLMF 23.9.7: `σ(z) = ∑_{m,n≥0} a_{m,n} (10c₂)^m (56c₃)^n z^{4m+6n+1}/(4m+6n+1)!`, `z ∈ ℂ`. -/
@[dlmf 23.9.E7]
theorem weierstrassSigma_series (L : PeriodPair) (z : ℂ) :
    HasSum (fun p : ℕ × ℕ ↦ (sigmaCoeff p.1 p.2 : ℂ) * (10 * laurentCoeff L 2) ^ p.1 *
        (56 * laurentCoeff L 3) ^ p.2 * z ^ (4 * p.1 + 6 * p.2 + 1) /
          ((4 * p.1 + 6 * p.2 + 1).factorial : ℂ))
      (weierstrassSigma L z) := by
  sorry

end DLMF.Weierstrass
