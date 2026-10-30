/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Products.InfiniteProducts

/-!
# Theta logarithmic derivatives and double products

Logarithmic derivative series, double products and theta-null product evaluations.

Source references and common attribution are retained in
`DLMF.Theta.Products`.
-/

@[expose] public section

open Complex Filter Topology

open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic DLMF.QSeries

/-! ### §20.5(ii) Logarithmic derivatives -/

/-- DLMF 20.5.10: for `|Im z| < π Im τ`,
`θ₁'/θ₁ - cot z = 4 sin 2z ∑ q^{2n}/(1 - 2q^{2n} cos 2z + q^{4n})
  = 4 ∑ q^{2n}/(1 - q^{2n}) sin 2nz`. -/
@[dlmf 20.5.E10]
theorem jacobiThetaOneTau_logDeriv {z τ : ℂ} (hτ : 0 < τ.im) (hz : |z.im| < π * τ.im) :
    HasSum (fun k : ℕ => 4 * sin (2 * z) * (cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 - 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))))
      (deriv (fun w => jacobiThetaOneTau w τ) z / jacobiThetaOneTau z τ - cot z) ∧
    HasSum (fun k : ℕ => 4 * (cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) * sin (2 * (k + 1) * z))
      (deriv (fun w => jacobiThetaOneTau w τ) z / jacobiThetaOneTau z τ - cot z) := by
  set E := cexp (π * I * τ) with hE
  have hEn : ‖E‖ = Real.exp (-(π * τ.im)) := by rw [hE, norm_exp]; simp
  have hQ : ‖E ^ 2‖ < 1 := th20_norm_nome_sq_lt_one hτ
  have hb : ‖E ^ 2‖ * Real.exp (2 * |z.im|) < 1 := by
    rw [norm_pow, hEn, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by push_cast; linarith)
  obtain ⟨hFz, hFd, hS1, hS2⟩ := p20R1_logDeriv_core hQ hb
  obtain ⟨hPm, hPne⟩ := p20R1_P_mult_ne hτ
  have hpow : ∀ k : ℕ, E ^ 2 * (E ^ 2) ^ k = E ^ (2 * (k + 1)) := fun k => by
    rw [← pow_mul, ← pow_add]; ring_nf
  have hpow4 : ∀ k : ℕ, E ^ (4 * (k + 1)) = (E ^ (2 * (k + 1))) ^ 2 := fun k => by
    rw [← pow_mul]; ring_nf
  set P := ∏' k : ℕ, (1 - E ^ (2 * (k + 1))) with hP
  set K := 2 * cexp (π * I * τ / 4) with hK
  have hK0 : K ≠ 0 := mul_ne_zero two_ne_zero (exp_ne_zero _)
  have hfun : (fun w => jacobiThetaOneTau w τ) =
      fun w => (K * P) * sin w * p20R1_F (E ^ 2) (E ^ 2) w := by
    funext w
    rw [(jacobiThetaOneTau_hasProd w hτ).2]
    have hc : ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
        (1 - 2 * E ^ (2 * (k + 1)) * cos (2 * w) + E ^ (4 * (k + 1)))) =
        ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
          (1 - 2 * (E ^ 2 * (E ^ 2) ^ k) * cos (2 * w) + (E ^ 2 * (E ^ 2) ^ k) ^ 2)) :=
      tprod_congr fun k => by rw [hpow, hpow4]
    rw [hc, hPm.tprod_mul (p20R1_F_mult _ _ w hQ), p20R1_F]
    ring
  have hL : deriv (fun w => jacobiThetaOneTau w τ) z / jacobiThetaOneTau z τ - cot z =
      logDeriv (p20R1_F (E ^ 2) (E ^ 2)) z := by
    by_cases hs : sin z = 0
    · have h2 : sin (2 * z) = 0 := by rw [sin_two_mul, hs]; ring
      have h0 : logDeriv (p20R1_F (E ^ 2) (E ^ 2)) z = 0 :=
        hS1.unique (by simp [h2])
      rw [h0, show jacobiThetaOneTau z τ = K * P * sin z * p20R1_F (E ^ 2) (E ^ 2) z from
        congrFun hfun z, hs, cot_eq_cos_div_sin, hs]
      simp
    · rw [show jacobiThetaOneTau z τ = K * P * sin z * p20R1_F (E ^ 2) (E ^ 2) z from
        congrFun hfun z, hfun, p20R1_logDeriv_shape (mul_ne_zero hK0 hPne) (hasDerivAt_sin z) hFd hs hFz,
        cot_eq_cos_div_sin]
      ring
  rw [hL]
  constructor
  · convert hS1 using 1; funext k; rw [hpow, hpow4]; ring
  · convert hS2 using 1; funext k; simp only [← pow_mul]

/-- DLMF 20.5.11: for `|Im z| < π Im τ`,
`θ₂'/θ₂ + tan z = -4 sin 2z ∑ q^{2n}/(1 + 2q^{2n} cos 2z + q^{4n})
  = 4 ∑ (-1)ⁿ q^{2n}/(1 - q^{2n}) sin 2nz`. -/
@[dlmf 20.5.E11]
theorem jacobiThetaTwoTau_logDeriv {z τ : ℂ} (hτ : 0 < τ.im) (hz : |z.im| < π * τ.im) :
    HasSum (fun k : ℕ => -4 * sin (2 * z) * (cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 + 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))))
      (deriv (fun w => jacobiThetaTwoTau w τ) z / jacobiThetaTwoTau z τ + tan z) ∧
    HasSum (fun k : ℕ => 4 * (-1 : ℂ) ^ (k + 1) * (cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) * sin (2 * (k + 1) * z))
      (deriv (fun w => jacobiThetaTwoTau w τ) z / jacobiThetaTwoTau z τ + tan z) := by
  set E := cexp (π * I * τ) with hE
  have hEn : ‖E‖ = Real.exp (-(π * τ.im)) := by rw [hE, norm_exp]; simp
  have hQ : ‖E ^ 2‖ < 1 := th20_norm_nome_sq_lt_one hτ
  have hb : ‖-E ^ 2‖ * Real.exp (2 * |z.im|) < 1 := by
    rw [norm_neg, norm_pow, hEn, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by push_cast; linarith)
  obtain ⟨hFz, hFd, hS1, hS2⟩ := p20R1_logDeriv_core hQ hb
  obtain ⟨hPm, hPne⟩ := p20R1_P_mult_ne hτ
  have hpow : ∀ k : ℕ, -E ^ 2 * (E ^ 2) ^ k = -E ^ (2 * (k + 1)) := fun k => by
    rw [neg_mul, ← pow_mul, ← pow_add]; ring_nf
  have hpow4 : ∀ k : ℕ, E ^ (4 * (k + 1)) = (E ^ (2 * (k + 1))) ^ 2 := fun k => by
    rw [← pow_mul]; ring_nf
  set P := ∏' k : ℕ, (1 - E ^ (2 * (k + 1))) with hP
  set K := 2 * cexp (π * I * τ / 4) with hK
  have hK0 : K ≠ 0 := mul_ne_zero two_ne_zero (exp_ne_zero _)
  have hfun : (fun w => jacobiThetaTwoTau w τ) =
      fun w => (K * P) * cos w * p20R1_F (-E ^ 2) (E ^ 2) w := by
    funext w
    rw [(jacobiThetaTwoTau_hasProd w hτ).2]
    have hc : ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
        (1 + 2 * E ^ (2 * (k + 1)) * cos (2 * w) + E ^ (4 * (k + 1)))) =
        ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
          (1 - 2 * (-E ^ 2 * (E ^ 2) ^ k) * cos (2 * w) + (-E ^ 2 * (E ^ 2) ^ k) ^ 2)) :=
      tprod_congr fun k => by rw [hpow, hpow4]; ring
    rw [hc, hPm.tprod_mul (p20R1_F_mult _ _ w hQ), p20R1_F]
    ring
  have hL : deriv (fun w => jacobiThetaTwoTau w τ) z / jacobiThetaTwoTau z τ + tan z =
      logDeriv (p20R1_F (-E ^ 2) (E ^ 2)) z := by
    by_cases hs : cos z = 0
    · have h2 : sin (2 * z) = 0 := by rw [sin_two_mul, hs]; ring
      have h0 : logDeriv (p20R1_F (-E ^ 2) (E ^ 2)) z = 0 := hS1.unique (by simp [h2])
      rw [h0, show jacobiThetaTwoTau z τ = K * P * cos z * p20R1_F (-E ^ 2) (E ^ 2) z from
        congrFun hfun z, hs, tan_eq_sin_div_cos, hs]
      simp
    · rw [show jacobiThetaTwoTau z τ = K * P * cos z * p20R1_F (-E ^ 2) (E ^ 2) z from
        congrFun hfun z, hfun, p20R1_logDeriv_shape (mul_ne_zero hK0 hPne) (hasDerivAt_cos z)
        hFd hs hFz, tan_eq_sin_div_cos]
      ring
  rw [hL]
  constructor
  · convert hS1 using 1; funext k; rw [hpow, hpow4]; ring
  · convert hS2 using 1; funext k; rw [neg_pow (E ^ 2), ← pow_mul]; ring

/-- DLMF 20.5.12: for `|Im z| < π Im τ / 2`,
`θ₃'/θ₃ = -4 sin 2z ∑ q^{2n-1}/(1 + 2q^{2n-1} cos 2z + q^{4n-2})
  = 4 ∑ (-1)ⁿ qⁿ/(1 - q^{2n}) sin 2nz`. -/
@[dlmf 20.5.E12]
theorem jacobiThetaThreeTau_logDeriv {z τ : ℂ} (hτ : 0 < τ.im) (hz : |z.im| < π * τ.im / 2) :
    HasSum (fun k : ℕ => -4 * sin (2 * z) * (cexp (π * I * τ) ^ (2 * k + 1) /
        (1 + 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))))
      (deriv (fun w => jacobiThetaThreeTau w τ) z / jacobiThetaThreeTau z τ) ∧
    HasSum (fun k : ℕ => 4 * (-1 : ℂ) ^ (k + 1) * (cexp (π * I * τ) ^ (k + 1) /
        (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) * sin (2 * (k + 1) * z))
      (deriv (fun w => jacobiThetaThreeTau w τ) z / jacobiThetaThreeTau z τ) := by
  set E := cexp (π * I * τ) with hE
  have hEn : ‖E‖ = Real.exp (-(π * τ.im)) := by rw [hE, norm_exp]; simp
  have hQ : ‖E ^ 2‖ < 1 := th20_norm_nome_sq_lt_one hτ
  have hb : ‖-E‖ * Real.exp (2 * |z.im|) < 1 := by
    rw [norm_neg, hEn, ← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  obtain ⟨hFz, hFd, hS1, hS2⟩ := p20R1_logDeriv_core hQ hb
  obtain ⟨hPm, hPne⟩ := p20R1_P_mult_ne hτ
  have hpow : ∀ k : ℕ, -E * (E ^ 2) ^ k = -E ^ (2 * k + 1) := fun k => by
    rw [neg_mul, ← pow_mul, ← pow_succ']
  have hpow4 : ∀ k : ℕ, E ^ (4 * k + 2) = (E ^ (2 * k + 1)) ^ 2 := fun k => by
    rw [← pow_mul]; ring_nf
  set P := ∏' k : ℕ, (1 - E ^ (2 * (k + 1))) with hP
  have hfun : (fun w => jacobiThetaThreeTau w τ) =
      fun w => P * (fun _ => (1 : ℂ)) w * p20R1_F (-E) (E ^ 2) w := by
    funext w
    rw [(jacobiThetaThreeTau_hasProd w hτ).2]
    have hc : ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
        (1 + 2 * E ^ (2 * k + 1) * cos (2 * w) + E ^ (4 * k + 2))) =
        ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
          (1 - 2 * (-E * (E ^ 2) ^ k) * cos (2 * w) + (-E * (E ^ 2) ^ k) ^ 2)) :=
      tprod_congr fun k => by rw [hpow, hpow4]; ring
    rw [hc, hPm.tprod_mul (p20R1_F_mult _ _ w hQ), p20R1_F]
    ring
  have hL : deriv (fun w => jacobiThetaThreeTau w τ) z / jacobiThetaThreeTau z τ =
      logDeriv (p20R1_F (-E) (E ^ 2)) z := by
    rw [show jacobiThetaThreeTau z τ = P * (fun _ => (1 : ℂ)) z * p20R1_F (-E) (E ^ 2) z from
      congrFun hfun z, hfun, p20R1_logDeriv_shape hPne (hasDerivAt_const z (1 : ℂ))
      hFd one_ne_zero hFz]
    ring
  rw [hL]
  constructor
  · convert hS1 using 1; funext k; rw [hpow, hpow4]; ring
  · convert hS2 using 1; funext k; rw [neg_pow E, ← pow_mul]; ring

/-- DLMF 20.5.13: for `|Im z| < π Im τ / 2`,
`θ₄'/θ₄ = 4 sin 2z ∑ q^{2n-1}/(1 - 2q^{2n-1} cos 2z + q^{4n-2}) = 4 ∑ qⁿ/(1 - q^{2n}) sin 2nz`. -/
@[dlmf 20.5.E13]
theorem jacobiThetaFourTau_logDeriv {z τ : ℂ} (hτ : 0 < τ.im) (hz : |z.im| < π * τ.im / 2) :
    HasSum (fun k : ℕ => 4 * sin (2 * z) * (cexp (π * I * τ) ^ (2 * k + 1) /
        (1 - 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))))
      (deriv (fun w => jacobiThetaFourTau w τ) z / jacobiThetaFourTau z τ) ∧
    HasSum (fun k : ℕ => 4 * (cexp (π * I * τ) ^ (k + 1) /
        (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) * sin (2 * (k + 1) * z))
      (deriv (fun w => jacobiThetaFourTau w τ) z / jacobiThetaFourTau z τ) := by
  set E := cexp (π * I * τ) with hE
  have hEn : ‖E‖ = Real.exp (-(π * τ.im)) := by rw [hE, norm_exp]; simp
  have hQ : ‖E ^ 2‖ < 1 := th20_norm_nome_sq_lt_one hτ
  have hb : ‖E‖ * Real.exp (2 * |z.im|) < 1 := by
    rw [hEn, ← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  obtain ⟨hFz, hFd, hS1, hS2⟩ := p20R1_logDeriv_core hQ hb
  obtain ⟨hPm, hPne⟩ := p20R1_P_mult_ne hτ
  have hpow : ∀ k : ℕ, E * (E ^ 2) ^ k = E ^ (2 * k + 1) := fun k => by
    rw [← pow_mul, ← pow_succ']
  have hpow4 : ∀ k : ℕ, E ^ (4 * k + 2) = (E ^ (2 * k + 1)) ^ 2 := fun k => by
    rw [← pow_mul]; ring_nf
  set P := ∏' k : ℕ, (1 - E ^ (2 * (k + 1))) with hP
  have hfun : (fun w => jacobiThetaFourTau w τ) =
      fun w => P * (fun _ => (1 : ℂ)) w * p20R1_F E (E ^ 2) w := by
    funext w
    rw [(jacobiThetaFourTau_hasProd w hτ).2]
    have hc : ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
        (1 - 2 * E ^ (2 * k + 1) * cos (2 * w) + E ^ (4 * k + 2))) =
        ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
          (1 - 2 * (E * (E ^ 2) ^ k) * cos (2 * w) + (E * (E ^ 2) ^ k) ^ 2)) :=
      tprod_congr fun k => by rw [hpow, hpow4]
    rw [hc, hPm.tprod_mul (p20R1_F_mult _ _ w hQ), p20R1_F]
    ring
  have hL : deriv (fun w => jacobiThetaFourTau w τ) z / jacobiThetaFourTau z τ =
      logDeriv (p20R1_F E (E ^ 2)) z := by
    rw [show jacobiThetaFourTau z τ = P * (fun _ => (1 : ℂ)) z * p20R1_F E (E ^ 2) z from
      congrFun hfun z, hfun, p20R1_logDeriv_shape hPne (hasDerivAt_const z (1 : ℂ))
      hFd one_ne_zero hFz]
    ring
  rw [hL]
  constructor
  · convert hS1 using 1; funext k; rw [hpow, hpow4]; ring
  · convert hS2 using 1; funext k; rw [← pow_mul]

/-- DLMF §20.5(ii): under the conditions of 20.5.10–20.5.13 the series converge absolutely and
uniformly on compact subsets. Stated for the Fourier series of 20.5.10/20.5.11 on compact subsets
of the strip `|Im z| < π Im τ` and of 20.5.12/20.5.13 on compact subsets of `|Im z| < π Im τ/2`,
in Weierstrass M-test form: there is a summable majorant. -/
@[dlmf 20.5.ii]
theorem jacobiTheta_logDeriv_series_uniform {τ : ℂ} (hτ : 0 < τ.im) (K : Set ℂ)
    (hK : IsCompact K) :
    ((∀ z ∈ K, |z.im| < π * τ.im) → ∃ u : ℕ → ℝ, Summable u ∧ ∀ k : ℕ, ∀ z ∈ K,
      ‖cexp (π * I * τ) ^ (2 * (k + 1)) / (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        sin (2 * (k + 1) * z)‖ ≤ u k ∧
      ‖cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 - 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))‖ ≤ u k ∧
      ‖cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 + 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))‖ ≤ u k) ∧
    ((∀ z ∈ K, |z.im| < π * τ.im / 2) → ∃ u : ℕ → ℝ, Summable u ∧ ∀ k : ℕ, ∀ z ∈ K,
      ‖cexp (π * I * τ) ^ (k + 1) / (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        sin (2 * (k + 1) * z)‖ ≤ u k ∧
      ‖cexp (π * I * τ) ^ (2 * k + 1) /
        (1 - 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))‖ ≤ u k ∧
      ‖cexp (π * I * τ) ^ (2 * k + 1) /
        (1 + 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))‖ ≤ u k) := by
  set E := cexp (π * I * τ) with hE
  have hEn : ‖E‖ = Real.exp (-(π * τ.im)) := by rw [hE, norm_exp]; simp
  have hs1 : ‖E‖ < 1 := th20_norm_nome_lt_one hτ
  have hs0 : 0 ≤ ‖E‖ := norm_nonneg _
  rcases K.eq_empty_or_nonempty with hKe | hKn
  · exact ⟨fun _ => ⟨fun _ => 0, summable_zero, fun k z hz => by simp [hKe] at hz⟩,
      fun _ => ⟨fun _ => 0, summable_zero, fun k z hz => by simp [hKe] at hz⟩⟩
  obtain ⟨z0, hz0K, hmax⟩ := hK.exists_isMaxOn hKn
    ((continuous_abs.comp continuous_im).continuousOn (s := K))
  set c := |z0.im| with hcdef
  have hc : ∀ z ∈ K, |z.im| ≤ c := fun z hz => hmax hz
  have hex : ∀ z ∈ K, Real.exp (2 * |z.im|) ≤ Real.exp (2 * c) := fun z hz =>
    Real.exp_le_exp.mpr (by linarith [hc z hz])
  have hpos : 0 < Real.exp (2 * c) := Real.exp_pos _
  refine ⟨fun hK1 => ?_, fun hK2 => ?_⟩
  · have hcl : c < π * τ.im := hK1 z0 hz0K
    set r := ‖E‖ ^ 2 with hr
    set ρ := r * Real.exp (2 * c) with hρdef
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r < 1 := by rw [hr]; nlinarith
    have hρ0 : 0 ≤ ρ := by positivity
    have hρ1 : ρ < 1 := by
      rw [hρdef, hr, hEn, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by push_cast; linarith)
    refine ⟨fun k => ρ ^ (k + 1) / (1 - r) + r ^ (k + 1) / (1 - ρ) ^ 2, ?_, fun k z hz => ?_⟩
    · exact (((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hρ0 hρ1)).div_const _).add
        (((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)).div_const _)
    have hxn : ‖E ^ (2 * (k + 1))‖ = r ^ (k + 1) := by rw [norm_pow, pow_mul]
    have hxr : r ^ (k + 1) ≤ r := pow_le_of_le_one hr0 hr1.le (by omega)
    have hA : ρ ^ (k + 1) / (1 - r) ≥ 0 := div_nonneg (by positivity) (by linarith)
    have hB : r ^ (k + 1) / (1 - ρ) ^ 2 ≥ 0 := by positivity
    have hq := p20R1_bound_quot (x := E ^ (2 * (k + 1))) (z := z) (R := r) (ρ := ρ)
      (by rw [hxn]; exact hxr)
      (mul_le_mul_of_nonneg_left (hex z hz) hr0) hρ1
    rw [show E ^ (4 * (k + 1)) = (E ^ (2 * (k + 1))) ^ 2 by rw [← pow_mul]; ring_nf]
    rw [hxn] at hq
    refine ⟨?_, by linarith [hq.1], by linarith [hq.2]⟩
    have hb := p20R1_bound_sin (x := E ^ (2 * (k + 1))) (y := E ^ (2 * (k + 1))) (z := z) k
      (by rw [hxn]; linarith)
    rw [hxn] at hb
    refine hb.trans ?_
    have : r ^ (k + 1) / (1 - r ^ (k + 1)) * Real.exp (2 * |z.im|) ^ (k + 1) ≤
        ρ ^ (k + 1) / (1 - r) := by
      rw [hρdef, mul_pow, div_mul_eq_mul_div]
      gcongr
      exact hc z hz
    linarith
  · have hcl : c < π * τ.im / 2 := hK2 z0 hz0K
    set s := ‖E‖ with hsdef
    set σ := s * Real.exp (2 * c) with hσdef
    have hσ0 : 0 ≤ σ := by positivity
    have hσ1 : σ < 1 := by
      rw [hσdef, hEn, ← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hs2 : s ^ 2 < 1 := by nlinarith
    refine ⟨fun k => σ ^ (k + 1) / (1 - s ^ 2) + s * (s ^ 2) ^ k / (1 - σ) ^ 2, ?_,
      fun k z hz => ?_⟩
    · exact (((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hσ0 hσ1)).div_const _).add
        (((summable_geometric_of_lt_one (by positivity) hs2).mul_left s).div_const _)
    have hyn : ‖E ^ (2 * k + 1)‖ = s * (s ^ 2) ^ k := by rw [norm_pow, ← pow_mul]; ring
    have hys : s * (s ^ 2) ^ k ≤ s := mul_le_of_le_one_right hs0 (pow_le_one₀ (by positivity) hs2.le)
    have hA : σ ^ (k + 1) / (1 - s ^ 2) ≥ 0 := div_nonneg (by positivity) (by linarith)
    have hB : s * (s ^ 2) ^ k / (1 - σ) ^ 2 ≥ 0 := by positivity
    have hq := p20R1_bound_quot (x := E ^ (2 * k + 1)) (z := z) (R := s) (ρ := σ)
      (by rw [hyn]; exact hys)
      (mul_le_mul_of_nonneg_left (hex z hz) hs0) hσ1
    rw [show E ^ (4 * k + 2) = (E ^ (2 * k + 1)) ^ 2 by rw [← pow_mul]; ring_nf]
    rw [hyn] at hq
    refine ⟨?_, by linarith [hq.1], by linarith [hq.2]⟩
    have hxn : ‖E ^ (2 * (k + 1))‖ = (s ^ 2) ^ (k + 1) := by rw [norm_pow, pow_mul]
    have hb := p20R1_bound_sin (x := E ^ (k + 1)) (y := E ^ (2 * (k + 1))) (z := z) k
      (by rw [hxn]; exact pow_lt_one₀ (by positivity) hs2 (by omega))
    rw [hxn, norm_pow] at hb
    refine hb.trans ?_
    have h1 : (s ^ 2) ^ (k + 1) ≤ s ^ 2 := pow_le_of_le_one (by positivity) hs2.le (by omega)
    have : s ^ (k + 1) / (1 - (s ^ 2) ^ (k + 1)) * Real.exp (2 * |z.im|) ^ (k + 1) ≤
        σ ^ (k + 1) / (1 - s ^ 2) := by
      rw [hσdef, mul_pow, div_mul_eq_mul_div]
      gcongr
      exact hc z hz
    linarith

/-! ### §20.5(iii) Double products -/

/-- Euler's partial sine product `w ∏_{k<M} (1 - w²/((k+1)π)²)`. -/
noncomputable def p3t_g (w : ℂ) (M : ℕ) : ℂ :=
  w * ∏ k ∈ Finset.range M, (1 - w ^ 2 / (((k : ℂ) + 1) * π) ^ 2)

/-- Euler's sine product: `p3t_g w M → sin w`. -/
lemma p3t_g_tendsto (w : ℂ) : Tendsto (p3t_g w) atTop (𝓝 (sin w)) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := Complex.tendsto_euler_sin_prod (w / π)
  rw [show (π : ℂ) * (w / π) = w by field_simp] at h
  refine h.congr fun M => ?_
  rw [p3t_g]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  field_simp

/-- Peeling the two end factors off `∏_{m=-(M+1)}^{M+1}`. -/
lemma p3t_prod_Icc_succ (f : ℤ → ℂ) (M : ℕ) :
    ∏ m ∈ Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ), f m =
      f (-((M : ℤ) + 1)) * f ((M : ℤ) + 1) * ∏ m ∈ Finset.Icc (-(M : ℤ)) M, f m := by
  have e : Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ) =
      insert (-((M : ℤ) + 1)) (insert ((M : ℤ) + 1) (Finset.Icc (-(M : ℤ)) M)) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
  rw [e, Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
    Finset.prod_insert (by simp only [Finset.mem_Icc]; omega), mul_assoc]

/-- Peeling the two end factors off `∏_{m=-M}^{M+1}`. -/
lemma p3t_prod_Icc_one_sub_succ (f : ℤ → ℂ) (M : ℕ) :
    ∏ m ∈ Finset.Icc (1 - ((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ), f m =
      f (-(M : ℤ)) * f ((M : ℤ) + 1) * ∏ m ∈ Finset.Icc (1 - (M : ℤ)) M, f m := by
  have e : Finset.Icc (1 - ((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ) =
      insert (-(M : ℤ)) (insert ((M : ℤ) + 1) (Finset.Icc (1 - (M : ℤ)) M)) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
  rw [e, Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
    Finset.prod_insert (by simp only [Finset.mem_Icc]; omega), mul_assoc]

/-- `mπ + b ≠ 0` when `sin b ≠ 0`. -/
lemma p3t_int_mul_pi_add_ne {b : ℂ} (hb : sin b ≠ 0) (n : ℤ) : (n : ℂ) * π + b ≠ 0 := by
  intro h
  apply hb
  rw [show b = ((-n : ℤ) : ℂ) * π by push_cast; linear_combination h]
  exact sin_int_mul_pi _

/-- `∏_{m=-M}^{M} (1 + z/(mπ + b)) → sin(b+z)/sin b` for `sin b ≠ 0`. -/
lemma p3t_tendsto_shift_prod {b : ℂ} (hb : sin b ≠ 0) (z : ℂ) :
    Tendsto (fun M : ℕ => ∏ m ∈ Finset.Icc (-(M : ℤ)) M, (1 + z / (m * π + b))) atTop
      (𝓝 (sin (b + z) / sin b)) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hne := p3t_int_mul_pi_add_ne hb
  have key : ∀ M : ℕ, (∏ m ∈ Finset.Icc (-(M : ℤ)) M, (1 + z / (m * π + b))) * p3t_g b M =
      p3t_g (b + z) M := by
    intro M
    induction M with
    | zero =>
      have h0 := hne 0
      simp only [Int.cast_zero, zero_mul, zero_add] at h0
      simp [p3t_g]
      field_simp
    | succ M ih =>
      rw [p3t_prod_Icc_succ]
      unfold p3t_g at ih ⊢
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      have h1 := hne (-((M : ℤ) + 1))
      have h2 := hne ((M : ℤ) + 1)
      push_cast at h1 h2 ⊢
      have h3 : ((M : ℂ) + 1) * π ≠ 0 := mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero M) hπ
      have hid : (1 + z / (-((M : ℂ) + 1) * π + b)) * (1 + z / (((M : ℂ) + 1) * π + b)) *
          (1 - b ^ 2 / (((M : ℂ) + 1) * π) ^ 2) = 1 - (b + z) ^ 2 / (((M : ℂ) + 1) * π) ^ 2 := by
        rw [neg_mul] at h1 ⊢
        generalize ((M : ℂ) + 1) * π = c at h1 h2 h3 ⊢
        have h1' : b - c ≠ 0 := by rwa [sub_eq_neg_add]
        rw [← sub_eq_neg_add]
        field_simp
        ring
      linear_combination ((1 + z / (-((M : ℂ) + 1) * π + b)) * (1 + z / (((M : ℂ) + 1) * π + b)) *
          (1 - b ^ 2 / (((M : ℂ) + 1) * π) ^ 2)) * ih +
        ((b + z) * ∏ x ∈ Finset.range M, (1 - (b + z) ^ 2 / ((x + 1) * π) ^ 2)) * hid
  have hlim := (p3t_g_tendsto (b + z)).div (p3t_g_tendsto b) hb
  refine hlim.congr' ?_
  filter_upwards [(p3t_g_tendsto b).eventually_ne hb] with M hM
  rw [Pi.div_apply, ← key M, mul_div_cancel_right₀ _ hM]

/-- `sin w ≠ 0` off the real axis. -/
lemma p3t_sin_ne_zero_of_im {w : ℂ} (h : w.im ≠ 0) : sin w ≠ 0 := by
  rw [Ne, sin_eq_zero_iff]; rintro ⟨k, rfl⟩; simp at h

/-- `cos w ≠ 0` off the real axis. -/
lemma p3t_cos_ne_zero_of_im {w : ℂ} (h : w.im ≠ 0) : cos w ≠ 0 := by
  rw [Ne, cos_eq_zero_iff]; rintro ⟨k, rfl⟩
  apply h
  rw [show (2 * (k : ℂ) + 1) * π / 2 = (((2 * k + 1 : ℤ) : ℝ) * π / 2 : ℝ) by push_cast; ring]
  exact ofReal_im _

/-- `∏_{m=1-M}^{M} (1 + z/(mπ + b)) → sin(b+z)/sin b` for `sin b ≠ 0`. -/
lemma p3t_tendsto_shift_prod' {b : ℂ} (hb : sin b ≠ 0) (z : ℂ) :
    Tendsto (fun M : ℕ => ∏ m ∈ Finset.Icc (1 - (M : ℤ)) M, (1 + z / (m * π + b))) atTop
      (𝓝 (sin (b + z) / sin b)) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsplit : ∀ M : ℕ, ∏ m ∈ Finset.Icc (-(M : ℤ)) M, (1 + z / (m * π + b)) =
      (1 + z / (((-(M : ℤ) : ℤ) : ℂ) * π + b)) *
        ∏ m ∈ Finset.Icc (1 - (M : ℤ)) M, (1 + z / (m * π + b)) := by
    intro M
    have e : Finset.Icc (-(M : ℤ)) M = insert (-(M : ℤ)) (Finset.Icc (1 - (M : ℤ)) M) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [e, Finset.prod_insert (by simp only [Finset.mem_Icc]; omega)]
  have hinv : Tendsto (fun M : ℕ => ((M : ℂ))⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp tendsto_natCast_atTop_atTop
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp this
    simpa [Function.comp_def] using h2
  have hf : Tendsto (fun M : ℕ => 1 + z / (((-(M : ℤ) : ℤ) : ℂ) * π + b)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun M : ℕ => 1 + z * ((M : ℂ))⁻¹ / (-π + b * ((M : ℂ))⁻¹)) atTop
        (𝓝 (1 + z * 0 / (-π + b * 0))) :=
      tendsto_const_nhds.add ((tendsto_const_nhds.mul hinv).div
        (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)) (by simp))
    rw [mul_zero, zero_div, add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with M hM
    have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
    push_cast
    congr 1
    rw [show -(M : ℂ) * π + b = (M : ℂ) * (-π + b * (M : ℂ)⁻¹) by field_simp]
    field_simp
  have hlim := (p3t_tendsto_shift_prod hb z).div hf one_ne_zero
  rw [div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hf.eventually_ne one_ne_zero] with M hM
  rw [Pi.div_apply, hsplit M, mul_div_cancel_left₀ _ hM]

/-- A symmetric product over `-N..N` as `L 0` times products of pairs `L(-n) L(n)`. -/
lemma p3t_prod_Icc_pairs (L : ℤ → ℂ) (N : ℕ) :
    ∏ n ∈ Finset.Icc (-(N : ℤ)) N, L n =
      L 0 * ∏ k ∈ Finset.range N, (L (-((k : ℤ) + 1)) * L ((k : ℤ) + 1)) := by
  induction N with
  | zero => simp
  | succ N ih => rw [p3t_prod_Icc_succ, ih, Finset.prod_range_succ]; ring

/-- A product over `1-N..N` as products of pairs `L(-k) L(k+1)`. -/
lemma p3t_prod_Icc_one_sub_pairs (L : ℤ → ℂ) (N : ℕ) :
    ∏ n ∈ Finset.Icc (1 - (N : ℤ)) N, L n =
      ∏ k ∈ Finset.range N, (L (-(k : ℤ)) * L ((k : ℤ) + 1)) := by
  induction N with
  | zero => simp
  | succ N ih => rw [p3t_prod_Icc_one_sub_succ, ih, Finset.prod_range_succ]; ring

/-- `z ∏'_{m=-M}^{M} (1 + z/(mπ)) = p3t_g z M` (the `m = 0` factor omitted). -/
lemma p3t_prod_zero_factor (z : ℂ) (M : ℕ) :
    z * ∏ m ∈ Finset.Icc (-(M : ℤ)) M, (if m = 0 then (1 : ℂ) else 1 + z / (m * π)) =
      p3t_g z M := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  induction M with
  | zero => simp [p3t_g]
  | succ M ih =>
    rw [p3t_prod_Icc_succ]
    unfold p3t_g at ih ⊢
    have hM1 : (M : ℤ) + 1 ≠ 0 := by omega
    have hM2 : -((M : ℤ) + 1) ≠ 0 := by omega
    simp only [hM1, hM2, ite_false]
    rw [Finset.prod_range_succ]
    have h3 : ((M : ℂ) + 1) * π ≠ 0 := mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero M) hπ
    have hid : (1 + z / (((-((M : ℤ) + 1) : ℤ) : ℂ) * π)) *
        (1 + z / ((((M : ℤ) + 1 : ℤ) : ℂ) * π)) =
        1 - z ^ 2 / (((M : ℂ) + 1) * π) ^ 2 := by
      push_cast
      rw [neg_mul]
      generalize ((M : ℂ) + 1) * π = c at h3 ⊢
      field_simp
      ring
    rw [← hid]
    linear_combination ((1 + z / (((-((M : ℤ) + 1) : ℤ) : ℂ) * π)) *
      (1 + z / ((((M : ℤ) + 1 : ℤ) : ℂ) * π))) * ih

/-- `Im((n - 1/2)τπ) ≠ 0` for `Im τ > 0`. -/
lemma p3t_half_int_im_ne {τ : ℂ} (hτ : 0 < τ.im) (n : ℤ) :
    (((n : ℂ) - 1 / 2) * τ * π).im ≠ 0 := by
  have e : (((n : ℂ) - 1 / 2) * τ * π).im = ((n : ℝ) - 1 / 2) * τ.im * π := by simp
  rw [e]
  refine mul_ne_zero (mul_ne_zero ?_ hτ.ne') Real.pi_ne_zero
  intro h
  have : ((2 * n : ℤ) : ℝ) = 1 := by push_cast; linarith
  have : (2 * n : ℤ) = 1 := by exact_mod_cast this
  omega

/-- `Im(nτπ) ≠ 0` for `n ≠ 0`, `Im τ > 0`. -/
lemma p3t_int_im_ne {τ : ℂ} (hτ : 0 < τ.im) {n : ℤ} (hn : n ≠ 0) :
    ((n : ℂ) * τ * π).im ≠ 0 := by
  have e : ((n : ℂ) * τ * π).im = (n : ℝ) * τ.im * π := by simp
  rw [e]
  exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hn) hτ.ne') Real.pi_ne_zero

/-- DLMF 20.5.14: `θ₁(z|τ) = z θ₁'(0|τ) lim_{N→∞} ∏_{n=-N}^{N} lim_{M→∞} ∏_{m=-M, |m|+|n|≠0}^{M}
(1 + z/((m + nτ)π))`, in this (Eisenstein) order of limits. -/
@[dlmf 20.5.E14]
theorem jacobiThetaOneTau_doubleProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ L : ℤ → ℂ,
      (∀ n : ℤ, Tendsto (fun M : ℕ => ∏ m ∈ Finset.Icc (-(M : ℤ)) M,
          if m = 0 ∧ n = 0 then (1 : ℂ) else 1 + z / ((m + n * τ) * π)) atTop (𝓝 (L n))) ∧
      Tendsto (fun N : ℕ => z * jacobiThetaOneDerivNullTau τ * ∏ n ∈ Finset.Icc (-(N : ℤ)) N, L n)
        atTop (𝓝 (jacobiThetaOneTau z τ)) := by
  have hsn : ∀ n : ℤ, n ≠ 0 → sin (n * τ * π) ≠ 0 := fun n hn =>
    p3t_sin_ne_zero_of_im (by
      simp only [mul_im, intCast_re, intCast_im, ofReal_re, ofReal_im, mul_zero, zero_mul,
        add_zero, zero_add]
      exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hn) hτ.ne') Real.pi_ne_zero)
  set L : ℤ → ℂ := fun n => if n = 0 then (if z = 0 then 1 else sin z / z)
      else sin (n * τ * π + z) / sin (n * τ * π) with hL
  refine ⟨L, fun n => ?_, ?_⟩
  · by_cases hn : n = 0
    · subst hn
      have e : ∀ M : ℕ, (∏ m ∈ Finset.Icc (-(M : ℤ)) M,
          if m = 0 ∧ (0 : ℤ) = 0 then (1 : ℂ) else 1 + z / ((m + ((0 : ℤ) : ℂ) * τ) * π)) =
          ∏ m ∈ Finset.Icc (-(M : ℤ)) M, (if m = 0 then (1 : ℂ) else 1 + z / (m * π)) :=
        fun M => Finset.prod_congr rfl fun m _ => by simp
      refine Tendsto.congr (fun M => (e M).symm) ?_
      simp only [hL, ite_true]
      split_ifs with hz
      · subst hz
        simp only [zero_div, add_zero, ite_self, Finset.prod_const_one]
        exact tendsto_const_nhds
      · refine ((p3t_g_tendsto z).div_const z).congr fun M => ?_
        rw [← p3t_prod_zero_factor, mul_div_cancel_left₀ _ hz]
    · simp only [hn, and_false, ite_false, hL]
      refine (p3t_tendsto_shift_prod (hsn n hn) z).congr fun M => ?_
      refine Finset.prod_congr rfl fun m _ => ?_
      congr 2; ring
  · obtain ⟨hm, he⟩ := jacobiThetaOneTau_hasProd_sin z hτ
    rw [he]
    refine (hm.hasProd.tendsto_prod_nat.const_mul
      (jacobiThetaOneDerivNullTau τ * sin z)).congr fun N => ?_
    rw [p3t_prod_Icc_pairs]
    have h0 : z * L 0 = sin z := by
      simp only [hL, ite_true]
      split_ifs with hz
      · simp [hz]
      · field_simp
    have hp : ∀ k : ℕ, L (-((k : ℤ) + 1)) * L ((k : ℤ) + 1) =
        sin ((k + 1) * π * τ + z) * sin ((k + 1) * π * τ - z) / sin ((k + 1) * π * τ) ^ 2 := by
      intro k
      have hk1 : (k : ℤ) + 1 ≠ 0 := by omega
      have hk2 : -((k : ℤ) + 1) ≠ 0 := by omega
      simp only [hL, hk1, hk2, ite_false]
      push_cast
      rw [show -((k : ℂ) + 1) * τ * π + z = -((k + 1) * π * τ - z) by ring,
        show -((k : ℂ) + 1) * τ * π = -((k + 1) * π * τ) by ring,
        show ((k : ℂ) + 1) * τ * π = (k + 1) * π * τ by ring, sin_neg, sin_neg]
      rw [neg_div_neg_eq]; ring
    rw [Finset.prod_congr rfl fun k _ => hp k, ← h0]
    ring

/-- DLMF 20.5.15: `θ₂(z|τ) = θ₂(0|τ) lim_{N→∞} ∏_{n=-N}^{N} lim_{M→∞} ∏_{m=1-M}^{M}
(1 + z/((m - 1/2 + nτ)π))`. -/
@[dlmf 20.5.E15]
theorem jacobiThetaTwoTau_doubleProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ L : ℤ → ℂ,
      (∀ n : ℤ, Tendsto (fun M : ℕ => ∏ m ∈ Finset.Icc (1 - (M : ℤ)) M,
          (1 + z / ((m - 1 / 2 + n * τ) * π))) atTop (𝓝 (L n))) ∧
      Tendsto (fun N : ℕ => jacobiThetaTwoNullTau τ * ∏ n ∈ Finset.Icc (-(N : ℤ)) N, L n)
        atTop (𝓝 (jacobiThetaTwoTau z τ)) := by
  have hcn : ∀ n : ℤ, cos (n * τ * π) ≠ 0 := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · exact p3t_cos_ne_zero_of_im (p3t_int_im_ne hτ hn)
  set L : ℤ → ℂ := fun n => cos (n * τ * π + z) / cos (n * τ * π) with hL
  refine ⟨L, fun n => ?_, ?_⟩
  · have hb : sin (n * τ * π - π / 2) ≠ 0 := by
      rw [sin_sub_pi_div_two]; exact neg_ne_zero.mpr (hcn n)
    have h := p3t_tendsto_shift_prod' hb z
    rw [show (n : ℂ) * τ * π - π / 2 + z = n * τ * π + z - π / 2 by ring, sin_sub_pi_div_two,
      sin_sub_pi_div_two, neg_div_neg_eq] at h
    refine h.congr fun M => Finset.prod_congr rfl fun m _ => ?_
    congr 2; ring
  · obtain ⟨hm, he⟩ := jacobiThetaTwoTau_hasProd_cos z hτ
    rw [he]
    refine (hm.hasProd.tendsto_prod_nat.const_mul
      (jacobiThetaTwoNullTau τ * cos z)).congr fun N => ?_
    rw [p3t_prod_Icc_pairs]
    have h0 : L 0 = cos z := by simp [hL]
    have hp : ∀ k : ℕ, L (-((k : ℤ) + 1)) * L ((k : ℤ) + 1) =
        cos ((k + 1) * π * τ + z) * cos ((k + 1) * π * τ - z) / cos ((k + 1) * π * τ) ^ 2 := by
      intro k
      simp only [hL]
      push_cast
      rw [show -((k : ℂ) + 1) * τ * π + z = -((k + 1) * π * τ - z) by ring,
        show -((k : ℂ) + 1) * τ * π = -((k + 1) * π * τ) by ring,
        show ((k : ℂ) + 1) * τ * π = (k + 1) * π * τ by ring, cos_neg, cos_neg]
      ring
    rw [Finset.prod_congr rfl fun k _ => hp k, h0]
    ring

/-- DLMF 20.5.16: `θ₃(z|τ) = θ₃(0|τ) lim_{N→∞} ∏_{n=1-N}^{N} lim_{M→∞} ∏_{m=1-M}^{M}
(1 + z/((m - 1/2 + (n - 1/2)τ)π))`. -/
@[dlmf 20.5.E16]
theorem jacobiThetaThreeTau_doubleProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ L : ℤ → ℂ,
      (∀ n : ℤ, Tendsto (fun M : ℕ => ∏ m ∈ Finset.Icc (1 - (M : ℤ)) M,
          (1 + z / ((m - 1 / 2 + (n - 1 / 2) * τ) * π))) atTop (𝓝 (L n))) ∧
      Tendsto (fun N : ℕ => jacobiThetaThreeNullTau τ * ∏ n ∈ Finset.Icc (1 - (N : ℤ)) N, L n)
        atTop (𝓝 (jacobiThetaThreeTau z τ)) := by
  have hcn : ∀ n : ℤ, cos ((n - 1 / 2) * τ * π) ≠ 0 := fun n =>
    p3t_cos_ne_zero_of_im (p3t_half_int_im_ne hτ n)
  set L : ℤ → ℂ := fun n => cos ((n - 1 / 2) * τ * π + z) / cos ((n - 1 / 2) * τ * π) with hL
  refine ⟨L, fun n => ?_, ?_⟩
  · have hb : sin ((n - 1 / 2) * τ * π - π / 2) ≠ 0 := by
      rw [sin_sub_pi_div_two]; exact neg_ne_zero.mpr (hcn n)
    have h := p3t_tendsto_shift_prod' hb z
    rw [show ((n : ℂ) - 1 / 2) * τ * π - π / 2 + z = (n - 1 / 2) * τ * π + z - π / 2 by ring,
      sin_sub_pi_div_two, sin_sub_pi_div_two, neg_div_neg_eq] at h
    refine h.congr fun M => Finset.prod_congr rfl fun m _ => ?_
    congr 2; ring
  · obtain ⟨hm, he⟩ := jacobiThetaThreeTau_hasProd_cos z hτ
    rw [he]
    refine (hm.hasProd.tendsto_prod_nat.const_mul (jacobiThetaThreeNullTau τ)).congr fun N => ?_
    rw [p3t_prod_Icc_one_sub_pairs]
    have hp : ∀ k : ℕ, L (-(k : ℤ)) * L ((k : ℤ) + 1) =
        cos ((k + 1 / 2) * π * τ + z) * cos ((k + 1 / 2) * π * τ - z) /
          cos ((k + 1 / 2) * π * τ) ^ 2 := by
      intro k
      simp only [hL]
      push_cast
      rw [show (-(k : ℂ) - 1 / 2) * τ * π + z = -((k + 1 / 2) * π * τ - z) by ring,
        show (-(k : ℂ) - 1 / 2) * τ * π = -((k + 1 / 2) * π * τ) by ring,
        show ((k : ℂ) + 1 - 1 / 2) * τ * π = (k + 1 / 2) * π * τ by ring, cos_neg, cos_neg]
      ring
    rw [Finset.prod_congr rfl fun k _ => hp k]

/-- DLMF 20.5.17: `θ₄(z|τ) = θ₄(0|τ) lim_{N→∞} ∏_{n=1-N}^{N} lim_{M→∞} ∏_{m=-M}^{M}
(1 + z/((m + (n - 1/2)τ)π))`. -/
@[dlmf 20.5.E17]
theorem jacobiThetaFourTau_doubleProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ L : ℤ → ℂ,
      (∀ n : ℤ, Tendsto (fun M : ℕ => ∏ m ∈ Finset.Icc (-(M : ℤ)) M,
          (1 + z / ((m + (n - 1 / 2) * τ) * π))) atTop (𝓝 (L n))) ∧
      Tendsto (fun N : ℕ => jacobiThetaFourNullTau τ * ∏ n ∈ Finset.Icc (1 - (N : ℤ)) N, L n)
        atTop (𝓝 (jacobiThetaFourTau z τ)) := by
  have hsn : ∀ n : ℤ, sin ((n - 1 / 2) * τ * π) ≠ 0 := fun n =>
    p3t_sin_ne_zero_of_im (p3t_half_int_im_ne hτ n)
  set L : ℤ → ℂ := fun n => sin ((n - 1 / 2) * τ * π + z) / sin ((n - 1 / 2) * τ * π) with hL
  refine ⟨L, fun n => ?_, ?_⟩
  · refine (p3t_tendsto_shift_prod (hsn n) z).congr fun M => Finset.prod_congr rfl fun m _ => ?_
    congr 2; ring
  · obtain ⟨hm, he⟩ := jacobiThetaFourTau_hasProd_sin z hτ
    rw [he]
    refine (hm.hasProd.tendsto_prod_nat.const_mul (jacobiThetaFourNullTau τ)).congr fun N => ?_
    rw [p3t_prod_Icc_one_sub_pairs]
    have hp : ∀ k : ℕ, L (-(k : ℤ)) * L ((k : ℤ) + 1) =
        sin ((k + 1 / 2) * π * τ + z) * sin ((k + 1 / 2) * π * τ - z) /
          sin ((k + 1 / 2) * π * τ) ^ 2 := by
      intro k
      simp only [hL]
      push_cast
      rw [show (-(k : ℂ) - 1 / 2) * τ * π + z = -((k + 1 / 2) * π * τ - z) by ring,
        show (-(k : ℂ) - 1 / 2) * τ * π = -((k + 1 / 2) * π * τ) by ring,
        show ((k : ℂ) + 1 - 1 / 2) * τ * π = (k + 1 / 2) * π * τ by ring, sin_neg, sin_neg,
        neg_div_neg_eq]
      ring
    rw [Finset.prod_congr rfl fun k _ => hp k]

/-- DLMF §20.5(iii): the double products are not absolutely convergent: for `z ≠ 0` the terms
`z/((m + nτ)π)` are not absolutely summable over the lattice. -/
@[dlmf 20.5.iii]
theorem jacobiTheta_doubleProd_not_absolutely_convergent {z τ : ℂ} (hz : z ≠ 0) :
    ¬ Summable (fun p : ℤ × ℤ => ‖z / ((p.1 + p.2 * τ) * π)‖) := by
  intro hs
  have hinj : Function.Injective (fun n : ℕ => (((n : ℤ) + 1), (0 : ℤ))) := by
    intro a b h; simp only [Prod.mk.injEq] at h; omega
  have h1 := hs.comp_injective hinj
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h2 : Summable (fun n : ℕ => (π / ‖z‖) * ‖z / ((((((n : ℤ) + 1 : ℤ)) : ℂ) +
      (((0 : ℤ)) : ℂ) * τ) * π)‖) := h1.mul_left _
  have h3 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    refine h2.congr fun n => ?_
    push_cast
    rw [zero_mul, add_zero, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, show ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
    field_simp
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp (by exact_mod_cast h3))

/-! ### Null values as products (DLMF 20.4.2–20.4.6), moved from `ZeroValues` -/

/-- Euler's identity `∏_{n≥1} (1 + Q^n)(1 - Q^{2n-1}) = 1` for `‖Q‖ < 1` (helper). -/
lemma p20R1_euler_hasProd {Q : ℂ} (hQ : ‖Q‖ < 1) :
    HasProd (fun k : ℕ => (1 + Q ^ (k + 1)) * (1 - Q ^ (2 * k + 1))) 1 := by
  have hgeo := summable_geometric_of_lt_one (norm_nonneg Q) hQ
  have hs1 : Summable (fun k : ℕ => ‖Q ^ (k + 1)‖) := by
    simpa [norm_pow] using (summable_nat_add_iff 1).mpr hgeo
  have hs2 : Summable (fun k : ℕ => ‖Q ^ (2 * k + 1)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hs1
    rw [norm_pow, norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) hQ.le (by omega)
  have hs3 : Summable (fun k : ℕ => ‖Q ^ (2 * (k + 1))‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hs1
    rw [norm_pow, norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) hQ.le (by omega)
  have hA := (multipliable_one_sub_of_summable hs1).hasProd
  have hB := (multipliable_one_add_of_summable hs1).hasProd
  have hC := (multipliable_one_sub_of_summable hs2).hasProd
  have hD := (multipliable_one_sub_of_summable hs3).hasProd
  have hAB : HasProd (fun k : ℕ => 1 - Q ^ (2 * (k + 1)))
      ((∏' k : ℕ, (1 - Q ^ (k + 1))) * ∏' k : ℕ, (1 + Q ^ (k + 1))) := by
    convert hA.mul hB using 1
    funext k; ring
  have hsplit : HasProd (fun m : ℕ => 1 - Q ^ (m + 1))
      ((∏' k : ℕ, (1 - Q ^ (2 * k + 1))) * ∏' k : ℕ, (1 - Q ^ (2 * (k + 1)))) := by
    refine HasProd.even_mul_odd ?_ ?_
    · convert hC using 2
    · convert hD using 3
  have hA0 : (∏' k : ℕ, (1 - Q ^ (k + 1))) ≠ 0 := by
    simpa only [sub_eq_add_neg] using tprod_one_add_ne_zero_of_summable
      (f := fun k : ℕ => -(Q ^ (k + 1))) (fun k h => by
        have h1 : Q ^ (k + 1) = 1 := by linear_combination -h
        have := congrArg norm h1
        rw [norm_pow, norm_one] at this
        exact absurd this (pow_lt_one₀ (norm_nonneg _) hQ (by omega)).ne) (by simpa using hs1)
  have heq := hA.unique hsplit
  rw [hD.unique hAB] at heq
  have h1 : (∏' k : ℕ, (1 + Q ^ (k + 1))) * ∏' k : ℕ, (1 - Q ^ (2 * k + 1)) = 1 := by
    apply mul_left_cancel₀ hA0
    linear_combination -heq
  convert hB.mul hC using 1
  exact h1.symm

/-- DLMF 20.4.2: `θ₁'(0,q) = 2q^{1/4} ∏_{n≥1} (1 - q^{2n})³ = 2q^{1/4} (q²;q²)_∞³`, `Im τ > 0`. -/
@[dlmf 20.4.E2]
theorem jacobiThetaOneDerivNullTau_prod {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) ^ 3) ∧
      jacobiThetaOneDerivNullTau τ = 2 * cexp (π * I * τ / 4) *
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) ^ 3) ∧
      jacobiThetaOneDerivNullTau τ = 2 * cexp (π * I * τ / 4) *
        qPochhammerInf (cexp (π * I * τ) ^ 2) (cexp (π * I * τ) ^ 2) ^ 3 := by
  obtain ⟨hm', hP, hd⟩ := p20R1_oneDeriv_tprod hτ
  exact ⟨hm'.pow 3, hd, p20R1_oneDeriv_qPochhammer hτ⟩

/-- DLMF 20.4.3: `θ₂(0,q) = 2q^{1/4} ∏_{n≥1} (1 - q^{2n})(1 + q^{2n})²`, `Im τ > 0`. -/
@[dlmf 20.4.E3]
theorem jacobiThetaTwoNullTau_prod {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + cexp (π * I * τ) ^ (2 * (k + 1))) ^ 2) ∧
      jacobiThetaTwoNullTau τ = 2 * cexp (π * I * τ / 4) *
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + cexp (π * I * τ) ^ (2 * (k + 1))) ^ 2) := by
  obtain ⟨hm, he⟩ := jacobiThetaTwoTau_hasProd 0 hτ
  have key : ∀ k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
      (1 + 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * 0) +
        cexp (π * I * τ) ^ (4 * (k + 1))) =
      (1 - cexp (π * I * τ) ^ (2 * (k + 1))) * (1 + cexp (π * I * τ) ^ (2 * (k + 1))) ^ 2 :=
    fun k => by rw [mul_zero, cos_zero]; ring
  refine ⟨hm.congr key, ?_⟩
  rw [jacobiThetaTwoNullTau, he, cos_zero, tprod_congr key, mul_one]

/-- DLMF 20.4.4: `θ₃(0,q) = ∏_{n≥1} (1 - q^{2n})(1 + q^{2n-1})²`, `Im τ > 0`. -/
@[dlmf 20.4.E4]
theorem jacobiThetaThreeNullTau_prod {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + cexp (π * I * τ) ^ (2 * k + 1)) ^ 2) ∧
      jacobiThetaThreeNullTau τ =
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + cexp (π * I * τ) ^ (2 * k + 1)) ^ 2) := by
  obtain ⟨hm, he⟩ := jacobiThetaThreeTau_hasProd 0 hτ
  have key : ∀ k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
      (1 + 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * 0) +
        cexp (π * I * τ) ^ (4 * k + 2)) =
      (1 - cexp (π * I * τ) ^ (2 * (k + 1))) * (1 + cexp (π * I * τ) ^ (2 * k + 1)) ^ 2 :=
    fun k => by rw [mul_zero, cos_zero]; ring
  exact ⟨hm.congr key, by rw [jacobiThetaThreeNullTau, he]; exact tprod_congr key⟩

/-- DLMF 20.4.5: `θ₄(0,q) = ∏_{n≥1} (1 - q^{2n})(1 - q^{2n-1})²`, `Im τ > 0`. -/
@[dlmf 20.4.E5]
theorem jacobiThetaFourNullTau_prod {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 - cexp (π * I * τ) ^ (2 * k + 1)) ^ 2) ∧
      jacobiThetaFourNullTau τ =
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 - cexp (π * I * τ) ^ (2 * k + 1)) ^ 2) := by
  obtain ⟨hm, he⟩ := jacobiThetaFourTau_hasProd 0 hτ
  have key : ∀ k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
      (1 - 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * 0) +
        cexp (π * I * τ) ^ (4 * k + 2)) =
      (1 - cexp (π * I * τ) ^ (2 * (k + 1))) * (1 - cexp (π * I * τ) ^ (2 * k + 1)) ^ 2 :=
    fun k => by rw [mul_zero, cos_zero]; ring
  exact ⟨hm.congr key, by rw [jacobiThetaFourNullTau, he]; exact tprod_congr key⟩

/-- DLMF 20.4.6: Jacobi's derivative formula `θ₁'(0,q) = θ₂(0,q) θ₃(0,q) θ₄(0,q)`, `Im τ > 0`. -/
@[dlmf 20.4.E6]
theorem jacobiThetaOneDerivNullTau_eq_mul {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiThetaOneDerivNullTau τ =
      jacobiThetaTwoNullTau τ * jacobiThetaThreeNullTau τ * jacobiThetaFourNullTau τ := by
  obtain ⟨m2, e2⟩ := jacobiThetaTwoNullTau_prod hτ
  obtain ⟨m3, e3⟩ := jacobiThetaThreeNullTau_prod hτ
  obtain ⟨m4, e4⟩ := jacobiThetaFourNullTau_prod hτ
  obtain ⟨m1, e1, -⟩ := jacobiThetaOneDerivNullTau_prod hτ
  have hQn := th20_norm_nome_sq_lt_one hτ
  set E := cexp (π * I * τ) with hE
  have hEu := p20R1_euler_hasProd hQn
  have hP := (m2.hasProd.mul m3.hasProd).mul m4.hasProd
  have hR := m1.hasProd.mul (hEu.mul hEu)
  have key : ∀ k : ℕ, (1 - E ^ (2 * (k + 1))) ^ 3 *
      (((1 + (E ^ 2) ^ (k + 1)) * (1 - (E ^ 2) ^ (2 * k + 1))) *
        ((1 + (E ^ 2) ^ (k + 1)) * (1 - (E ^ 2) ^ (2 * k + 1)))) =
      (1 - E ^ (2 * (k + 1))) * (1 + E ^ (2 * (k + 1))) ^ 2 *
        ((1 - E ^ (2 * (k + 1))) * (1 + E ^ (2 * k + 1)) ^ 2) *
        ((1 - E ^ (2 * (k + 1))) * (1 - E ^ (2 * k + 1)) ^ 2) := fun k => by ring
  have hR' : HasProd (fun k : ℕ => (1 - E ^ (2 * (k + 1))) * (1 + E ^ (2 * (k + 1))) ^ 2 *
        ((1 - E ^ (2 * (k + 1))) * (1 + E ^ (2 * k + 1)) ^ 2) *
        ((1 - E ^ (2 * (k + 1))) * (1 - E ^ (2 * k + 1)) ^ 2))
      ((∏' k : ℕ, (1 - E ^ (2 * (k + 1))) ^ 3) * (1 * 1)) := by
    convert hR using 1
    funext k
    exact (key k).symm
  have heq := hP.unique hR'
  rw [mul_one, mul_one] at heq
  rw [e1, e2, e3, e4, mul_assoc (2 * cexp (π * I * τ / 4)), mul_assoc (2 * cexp (π * I * τ / 4)),
    heq]

end DLMF.Theta

end

end
