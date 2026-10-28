/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Asymptotics.RealRemainders

/-!
# Sector bounds for Airy remainders

Uniform bounds for the Airy function and its derivative on the boundary rays and the remaining
closed sectors.

Source references and common attribution are retained in
`DLMF.Airy.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent

open scoped Real Topology Interval

namespace DLMF.Airy

/-! ### DLMF 9.7.17 for `Ai` on the closed rays and in the last sector

On `|arg z| = 2π/3` the `χ + 1` bound follows by continuity. For `2π/3 < |arg z| < π` the
connection formula 9.2.12 gives `R_N(z) = R_N(z₂) + κ e^{-2ζ(u)} F(u)` with `z = u e^{±2πi/3}`,
`z₂ = u e^{∓2πi/3}` and `|arg u| < π/3`; the last term is bounded through
`‖F(u)‖ ≤ cos(3/2 arg u)^{-1/6}` and the sharp Gamma inequality `airySt_gamma_ineq`. -/

/-- `‖F(u)‖ ≤ cos(3/2 arg u)^{-1/6}` for the normalized Ai on `|arg u| < π/3`. -/
theorem airySt_F_norm_le {u : ℂ} (hu : u ≠ 0) (harg : |arg u| < π / 3) :
    ‖airyAi u / airyPrefactor .ai u‖ ≤ Real.cos (3 / 2 * arg u) ^ (-(1 / 6 : ℝ)) := by
  have h0 : |(0 : ℝ)| < π := by simp [Real.pi_pos]
  have hab := abs_lt.mp harg
  have hzθ : |3 / 2 * arg u + 0| < π / 2 := by
    rw [add_zero, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]; linarith
  rw [airySt_F_eq hu h0 hzθ]
  set ℓ := log 2 + airyLogZeta u with hℓ
  set V := exp (ℓ + ((0 : ℝ) : ℂ) * I) with hVdef
  have hc : 0 < Real.cos (3 / 2 * arg u) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hVre : V.re = Real.exp ℓ.re * Real.cos (3 / 2 * arg u) := by
    rw [hVdef, airyRot_re_W]; simp [hℓ]
  have hV : 0 < V.re := by rw [hVre]; positivity
  have hL : ‖airyRot_lap (1 / 6) (-5 / 6) 0 V‖ ≤ Real.Gamma (1 / 6) * V.re ^ (-(1 / 6 : ℝ)) := by
    unfold airyRot_lap
    calc _ ≤ ∫ r in Ioi (0 : ℝ), r ^ ((1 / 6 : ℝ) - 1) * Real.exp (-(V.re * r)) := by
          refine norm_integral_le_of_norm_le (stRem_integrableOn_rpow_exp (by norm_num) hV) ?_
          refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
          have hr : (0 : ℝ) < r := hr
          simp only [airyRot_kernel, ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
          rw [norm_smul, norm_mul, norm_exp, show (1 : ℂ) + r = ((1 + r : ℝ) : ℂ) by push_cast; ring,
            norm_cpow_eq_rpow_re_of_pos hr, norm_cpow_eq_rpow_re_of_pos (by linarith)]
          have h1 : (1 + r) ^ (((-5 / 6 : ℝ) : ℂ)).re ≤ 1 := by
            simp only [ofReal_re]
            exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
          have hre : (-(V * r)).re = -(V.re * r) := by simp
          rw [hre]
          simp only [sub_re, ofReal_re, one_re]
          have := Real.rpow_nonneg hr.le ((1 / 6 : ℝ) - 1)
          calc Real.exp (-(V.re * r)) * (r ^ ((1 / 6 : ℝ) - 1) * (1 + r) ^ (-5 / 6 : ℝ))
              ≤ Real.exp (-(V.re * r)) * (r ^ ((1 / 6 : ℝ) - 1) * 1) := by
                gcongr; simpa using h1
            _ = _ := by ring
      _ = _ := airySt_gamma_int (by norm_num) hV
  have hG : ‖Gamma ((1 / 6 : ℝ) : ℂ)‖ = Real.Gamma (1 / 6) := by
    rw [Complex.Gamma_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le]
  have hGp := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 6 by norm_num)
  rw [norm_mul, norm_mul, norm_mul, norm_div, norm_one, hG, ofReal_zero, zero_mul,
    Complex.exp_zero, norm_one, one_mul, norm_exp]
  have hre : ((1 / 6 : ℂ) * ℓ).re = ℓ.re / 6 := by simp; ring
  rw [hre]
  calc Real.exp (ℓ.re / 6) * (1 / Real.Gamma (1 / 6) * ‖airyRot_lap (1 / 6) (-5 / 6) 0 V‖)
      ≤ Real.exp (ℓ.re / 6) * (1 / Real.Gamma (1 / 6) *
          (Real.Gamma (1 / 6) * V.re ^ (-(1 / 6 : ℝ)))) := by gcongr
    _ = Real.exp (ℓ.re / 6) * V.re ^ (-(1 / 6 : ℝ)) := by field_simp
    _ = _ := by
      rw [hVre, Real.mul_rpow (Real.exp_pos _).le hc.le, ← Real.exp_mul, ← mul_assoc,
        ← Real.exp_add]
      ring_nf; simp

/-- `Ai(u) + ω Ai(u ω) + ω̄ Ai(u ω̄) = 0` with `ω = e^{±2πi/3}`. -/
theorem airySt_conn {u : ℂ} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyAi u + exp (((ε * (2 * π / 3)) : ℝ) * I) * airyAi (u * exp (((ε * (2 * π / 3)) : ℝ) * I)) +
      exp ((((-ε) * (2 * π / 3)) : ℝ) * I) *
        airyAi (u * exp ((((-ε) * (2 * π / 3)) : ℝ) * I)) = 0 := by
  have h := airyAi_add_omega u
  have e1 : exp (((1 * (2 * π / 3)) : ℝ) * I) = exp (2 * π * I / 3) := by congr 1; push_cast; ring
  have e2 : exp ((((-1) * (2 * π / 3)) : ℝ) * I) = exp (-(2 * π * I / 3)) := by
    congr 1; push_cast; ring
  rcases hε with rfl | rfl
  · rw [e1, show (-(1 : ℝ)) = -1 by norm_num, e2]; linear_combination h
  · rw [e2, show (-(-1 : ℝ)) = 1 by norm_num, e1]; linear_combination h

/-- **The connection formula for the remainder** at `z = u e^{±2πi/3}`. -/
theorem airySt_third_rel {u : ℂ} (hu : u ≠ 0) (harg : |arg u| < π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (N : ℕ) :
    airyRemainder .ai N (u * exp (((ε * (2 * π / 3)) : ℝ) * I)) =
      airyRemainder .ai N (u * exp ((((-ε) * (2 * π / 3)) : ℝ) * I)) +
        (-exp ((((-ε) * (π / 2)) : ℝ) * I)) * exp (-(2 * airyZetaComplex u)) *
          (airyAi u / airyPrefactor .ai u) := by
  have hε' : -ε = 1 ∨ -ε = -1 := by rcases hε with rfl | rfl <;> norm_num
  have hz1 := airyRot_zeta_rot hu harg hε
  have hz2 := airyRot_zeta_rot hu harg hε'
  have hq1 := airyRot_quarter_rot hu harg hε
  have hq2 := airyRot_quarter_rot hu harg hε'
  have conn := airySt_conn (u := u) hε
  set E := exp (((ε * (π / 6)) : ℝ) * I) with hE
  have hE0 : E ≠ 0 := exp_ne_zero _
  have hpow : ∀ (c : ℝ) (n : ℕ), c = n * (ε * (π / 6)) → exp ((c : ℂ) * I) = E ^ n := by
    intro c n hc; rw [hE, ← exp_nat_mul]; congr 1; rw [hc]; push_cast; ring
  have hpowi : ∀ (c : ℝ) (n : ℕ), c = -(n * (ε * (π / 6))) → exp ((c : ℂ) * I) = (E ^ n)⁻¹ := by
    intro c n hc; rw [hE, ← exp_nat_mul, ← exp_neg]; congr 1; rw [hc]; push_cast; ring
  have hE6 : E ^ 6 = -1 := by
    rw [← hpow (ε * π) 6 (by push_cast; ring)]
    rcases hε with rfl | rfl
    · simp
    · rw [show (((-1 : ℝ) * π : ℝ) : ℂ) * I = -(π * I) by push_cast; ring, exp_neg, exp_pi_mul_I]
      norm_num
  simp only [airyRemainder, airyFunction, airyPrefactor, airyExponentialSum, hz1, hz2, hq1, hq2]
  generalize airyAi u = A0 at conn ⊢
  generalize airyAi (u * exp (((ε * (2 * π / 3)) : ℝ) * I)) = A1 at conn ⊢
  generalize airyAi (u * exp ((((-ε) * (2 * π / 3)) : ℝ) * I)) = A2 at conn ⊢
  rw [hpow (ε * (2 * π / 3)) 4 (by push_cast; ring),
    hpowi ((-ε) * (2 * π / 3)) 4 (by push_cast; ring)] at conn
  rw [hpowi ((-ε) * (π / 6)) 1 (by push_cast; ring), hpowi ((-ε) * (π / 2)) 3 (by push_cast; ring),
    pow_one]
  have hX0 : exp (airyZetaComplex u) ≠ 0 := exp_ne_zero _
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : u ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hu)
  rw [neg_neg, show -(2 * airyZetaComplex u) = -airyZetaComplex u + -airyZetaComplex u by ring,
    exp_add, exp_neg]
  generalize exp (airyZetaComplex u) = X at *
  field_simp
  have hF : E ^ 4 * (E ^ 4)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hE0)
  generalize (E ^ 4)⁻¹ = F at conn hF
  linear_combination (2 * (Real.sqrt π : ℂ) * u ^ (1 / 4 : ℂ)) * conn +
    (-(2 * (Real.sqrt π : ℂ) * u ^ (1 / 4 : ℂ)) * A2 * F) * hE6 +
    (2 * (Real.sqrt π : ℂ) * u ^ (1 / 4 : ℂ) * A2 * E ^ 2) * hF

/-- `Y^N e^{-2Y} ≤ (N/(2e))^N` for `Y ≥ 0`. -/
theorem airySt_pow_exp_le {Y : ℝ} (hY : 0 ≤ Y) (N : ℕ) :
    Y ^ N * Real.exp (-(2 * Y)) ≤ ((N : ℝ) / (2 * Real.exp 1)) ^ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [pow_zero, one_mul, Real.exp_le_one_iff]; linarith
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set x := 2 * Y / N with hx
  have hx0 : 0 ≤ x := by positivity
  have h1 : x * Real.exp (-x) ≤ Real.exp (-1) := by
    have := Real.add_one_le_exp (x - 1)
    have hx' : x ≤ Real.exp (x - 1) := by linarith
    calc x * Real.exp (-x) ≤ Real.exp (x - 1) * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right hx' (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; ring_nf
  have h2 : Y * Real.exp (-(2 * Y) / N) ≤ N / (2 * Real.exp 1) := by
    have hY' : Y = N / 2 * x := by rw [hx]; field_simp
    have : -(2 * Y) / N = -x := by rw [hx]; ring
    rw [this, hY', mul_assoc]
    calc (N : ℝ) / 2 * (x * Real.exp (-x)) ≤ N / 2 * Real.exp (-1) := by gcongr
      _ = _ := by rw [Real.exp_neg]; field_simp
  calc Y ^ N * Real.exp (-(2 * Y)) = (Y * Real.exp (-(2 * Y) / N)) ^ N := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; field_simp
    _ ≤ _ := pow_le_pow_left₀ (by positivity) h2 N

/-- The last term of 9.7.17: `e^{-2ρc} c^{-1/6} ≤ √(2π m) c^{-m} u_N ρ^{-N}`, `m = N + 1/6`. -/
theorem airySt_third_term {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c) (N : ℕ) :
    Real.exp (-(2 * (ρ * c))) * c ^ (-(1 / 6 : ℝ)) ≤
      Real.sqrt (2 * π * (N + 1 / 6)) / c ^ ((N : ℝ) + 1 / 6) * (airyU N / ρ ^ N) := by
  have hK := (airySt_pow_exp_le (mul_pos hρ hc).le N).trans (airySt_gamma_ineq N)
  have hcm : c ^ ((N : ℝ) + 1 / 6) = c ^ N * c ^ (1 / 6 : ℝ) := by
    rw [Real.rpow_add hc, Real.rpow_natCast]
  rw [hcm, Real.rpow_neg hc.le, mul_pow] at *
  have h16 : 0 < c ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hc _
  rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
  calc Real.exp (-(2 * (ρ * c))) * (c ^ (1 / 6 : ℝ))⁻¹ * (c ^ N * c ^ (1 / 6 : ℝ) * ρ ^ N)
      = ρ ^ N * c ^ N * Real.exp (-(2 * (ρ * c))) := by field_simp
    _ ≤ _ := by linarith [hK]

/-- `ζ(w) ≠ 0` for `w ≠ 0`. -/
theorem airySt_zeta_ne_zero {w : ℂ} (hw : w ≠ 0) : airyZetaComplex w ≠ 0 := by
  intro h0
  have := exp_log_two_add_airyLogZeta hw
  rw [h0, mul_zero] at this
  exact exp_ne_zero _ this

/-- `Re (2ζ(u)) = 2 |ζ(u)| cos ((3/2) arg u)` for `u ≠ 0`. -/
private lemma airySt_re_two_zeta {u : ℂ} (hu0 : u ≠ 0) :
    (2 * airyZetaComplex u).re = 2 * (‖airyZetaComplex u‖ * Real.cos (3 / 2 * arg u)) := by
  have h := airyRot_re_W u 0
  simp only [ofReal_zero, zero_mul, add_zero] at h
  rw [exp_log_two_add_airyLogZeta hu0] at h
  have hn : Real.exp (log 2 + airyLogZeta u).re = ‖2 * airyZetaComplex u‖ := by
    rw [← Complex.norm_exp, exp_log_two_add_airyLogZeta hu0]
  rw [h, hn, norm_mul]; simp; ring

/-- **The third sector of 9.7.17**, `2π/3 < |arg z| < π`. -/
theorem airySt_ai_third {z : ℂ} (hz : z ≠ 0) (h1 : 2 * π / 3 < |arg z|) (h2 : |arg z| < π)
    (N : ℕ) :
    ‖airyRemainder .ai N z‖ ≤ (Real.sqrt (2 * π * (N + 1 / 6)) /
      |Real.cos (3 * arg z / 2)| ^ ((N : ℝ) + 1 / 6) + airyChi (N + 1 / 6) + 1) *
      ‖airyExpansionCoeff .ai N / airyZetaComplex z ^ N‖ := by
  have hπ := Real.pi_pos
  obtain ⟨ε, hε, hεarg⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ arg z = |arg z| * ε := by
    rcases le_or_gt 0 (arg z) with h | h
    · exact ⟨1, Or.inl rfl, by rw [abs_of_nonneg h, mul_one]⟩
    · exact ⟨-1, Or.inr rfl, by rw [abs_of_neg h]; ring⟩
  have hε' : -ε = 1 ∨ -ε = -1 := by rcases hε with rfl | rfl <;> norm_num
  set u := z * exp ((((-ε) * (2 * π / 3)) : ℝ) * I) with hudef
  have hu0 : u ≠ 0 := mul_ne_zero hz (exp_ne_zero _)
  have hargu : arg u = arg z + (-ε) * (2 * π / 3) := by
    rw [hudef]
    apply Complex.arg_mul_exp_ofReal_mul_I hz <;> rcases hε with rfl | rfl <;> rw [hεarg]
        <;> nlinarith
  have hu : |arg u| < π / 3 := by
    rw [hargu, hεarg]; rcases hε with rfl | rfl <;> rw [abs_lt] <;> constructor <;> nlinarith
  have hzu : z = u * exp (((ε * (2 * π / 3)) : ℝ) * I) := by
    rw [hudef, mul_assoc, ← exp_add]
    rw [show (((-ε) * (2 * π / 3) : ℝ) : ℂ) * I + ((ε * (2 * π / 3) : ℝ) : ℂ) * I = 0 by
      push_cast; ring, exp_zero, mul_one]
  set z₂ := u * exp ((((-ε) * (2 * π / 3)) : ℝ) * I) with hz₂
  obtain ⟨b1, b2⟩ := airyRot_arg_rot_bounds hu hε'
  have hz₂0 : z₂ ≠ 0 := mul_ne_zero hu0 (exp_ne_zero _)
  have harg₂ : arg z₂ = arg u + (-ε) * (2 * π / 3) := Complex.arg_mul_exp_ofReal_mul_I hu0 b1 b2
  have hc : 0 < Real.cos (3 / 2 * arg u) := by
    have := abs_lt.mp hu
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcz : |Real.cos (3 * arg z / 2)| = Real.cos (3 / 2 * arg u) := by
    have : 3 * arg z / 2 = 3 / 2 * arg u + ε * π := by rw [hargu]; ring
    rw [this]
    rcases hε with rfl | rfl
    · rw [one_mul, Real.cos_add_pi, abs_neg, abs_of_pos hc]
    · rw [neg_one_mul, ← sub_eq_add_neg, Real.cos_sub_pi, abs_neg, abs_of_pos hc]
  have hζ1 := airyRot_zeta_rot hu0 hu hε
  have hζ2 := airyRot_zeta_rot hu0 hu hε'
  have hT : ‖airyExpansionCoeff .ai N / airyZetaComplex z ^ N‖ =
      airyU N / ‖airyZetaComplex u‖ ^ N := by
    rw [hzu, hζ1]
    simp only [airyExpansionCoeff, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul, Complex.norm_real, Real.norm_of_nonneg (airySt_airyU_pos N).le]
  have hR₂ : ‖airyRemainder .ai N z₂‖ ≤ (airyChi (N + 1 / 6) + 1) *
      ‖airyExpansionCoeff .ai N / airyZetaComplex z ^ N‖ := by
    have hz2a : |arg z₂| < 2 * π / 3 := by
      rw [harg₂]; have := abs_lt.mp hu
      rcases hε with rfl | rfl <;> rw [abs_lt] <;> constructor <;> nlinarith
    have hsin : Real.sin (3 * arg z₂ / 2) ≠ 0 := by
      rw [harg₂, show 3 * (arg u + (-ε) * (2 * π / 3)) / 2 = 3 / 2 * arg u - ε * π by ring]
      rcases hε with rfl | rfl
      all_goals
        first
          | rw [one_mul, Real.sin_sub_pi]
          | rw [neg_one_mul, sub_neg_eq_add, Real.sin_add_pi]
        refine neg_ne_zero.mpr fun h0 => ?_
        have := abs_lt.mp hu
        rcases Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith) |>.mp h0 with h'
        have hargu0 : arg u = 0 := by linarith
        have := hargu; rw [hargu0, hεarg] at this
        nlinarith
    have := airySt_ai_le_chi hz₂0 hz2a hsin N
    rwa [hz₂, hζ2, ← hζ1, ← hzu] at this
  have hrel := airySt_third_rel hu0 hu hε N
  rw [← hzu, ← hz₂] at hrel
  rw [hrel]
  have hκ : ‖-exp ((((-ε) * (π / 2)) : ℝ) * I)‖ = 1 := by rw [norm_neg, norm_exp_ofReal_mul_I]
  have hF := airySt_F_norm_le hu0 hu
  have hre := airySt_re_two_zeta hu0
  have hρ : 0 < ‖airyZetaComplex u‖ := norm_pos_iff.mpr (airySt_zeta_ne_zero hu0)
  have h3 := airySt_third_term hρ hc N
  rw [hcz, hT]
  calc ‖airyRemainder .ai N z₂ + -exp ((((-ε) * (π / 2)) : ℝ) * I) *
        exp (-(2 * airyZetaComplex u)) * (airyAi u / airyPrefactor .ai u)‖
      ≤ ‖airyRemainder .ai N z₂‖ + Real.exp (-(2 * (‖airyZetaComplex u‖ *
          Real.cos (3 / 2 * arg u)))) * Real.cos (3 / 2 * arg u) ^ (-(1 / 6 : ℝ)) := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_mul, norm_mul, hκ, one_mul, norm_exp, neg_re, hre]
        exact mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le
    _ ≤ (airyChi (N + 1 / 6) + 1) * (airyU N / ‖airyZetaComplex u‖ ^ N) +
        Real.sqrt (2 * π * (N + 1 / 6)) / Real.cos (3 / 2 * arg u) ^ ((N : ℝ) + 1 / 6) *
          (airyU N / ‖airyZetaComplex u‖ ^ N) := by
        rw [hT] at hR₂; exact add_le_add hR₂ h3
    _ = _ := by ring

/-- The first neglected term `(-1)^N u_N ζ^{-N}` is continuous on the slit plane. -/
theorem airySt_continuousAt_T {w : ℂ} (hw : w ∈ slitPlane) (N : ℕ) :
    ContinuousAt (fun w => airyExpansionCoeff .ai N / airyZetaComplex w ^ N) w :=
  continuousAt_const.div ((airyRot_differentiableAt_zeta hw).continuousAt.pow N)
    (pow_ne_zero _ (airySt_zeta_ne_zero (slitPlane_ne_zero hw)))

/-- The normalized `Ai` remainder is continuous on the slit plane. -/
theorem airySt_continuousAt_rem {w : ℂ} (hw : w ∈ slitPlane) (N : ℕ) :
    ContinuousAt (airyRemainder .ai N) w := by
  have hw0 := slitPlane_ne_zero hw
  have hz := (airyRot_differentiableAt_zeta hw).continuousAt
  have hq : ContinuousAt (fun w : ℂ => w ^ (1 / 4 : ℂ)) w := continuousAt_cpow_const hw
  have hp : ContinuousAt (airyPrefactor .ai) w := by
    have he : airyPrefactor .ai =
        fun w => exp (-airyZetaComplex w) / (2 * Real.sqrt π * w ^ (1 / 4 : ℂ)) := by
      funext w; rfl
    rw [he]
    exact (hz.neg.cexp).div (continuousAt_const.mul hq)
      (mul_ne_zero (mul_ne_zero two_ne_zero
        (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'))
        (cpow_ne_zero_iff.mpr (Or.inl hw0)))
  have hs : ContinuousAt (airyExponentialSum .ai N) w := by
    unfold airyExponentialSum
    exact tendsto_finsetSum _ fun k _ => airySt_continuousAt_T hw k
  unfold airyRemainder airyFunction
  exact (differentiable_airyAi.continuous.continuousAt.div hp
    (airyRot_prefactor_ne_zero .ai hw0)).sub hs

/-- `sin (3a/2) ≠ 0` for `π/3 < |a| < 2π/3`. -/
theorem airySt_sin_ne_zero {a : ℝ} (h1 : π / 3 < |a|) (h2 : |a| < 2 * π / 3) :
    Real.sin (3 * a / 2) ≠ 0 := by
  have hp : 0 < Real.sin (3 * |a| / 2) := Real.sin_pos_of_pos_of_lt_pi (by
    linarith [Real.pi_pos]) (by linarith)
  rcases le_or_gt 0 a with h | h
  · rw [abs_of_nonneg h] at hp; exact hp.ne'
  · rw [abs_of_neg h, show 3 * -a / 2 = -(3 * a / 2) by ring, Real.sin_neg] at hp; linarith

/-- `cos (3a/2) < 0` for `π/3 < |a| < 2π/3`. -/
theorem airySt_cos_neg {a : ℝ} (h1 : π / 3 < |a|) (h2 : |a| < 2 * π / 3) :
    Real.cos (3 / 2 * a) < 0 := by
  have hp : Real.cos (3 / 2 * |a|) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [Real.pi_pos])
  rcases le_or_gt 0 a with h | h
  · rwa [abs_of_nonneg h] at hp
  · rwa [abs_of_neg h, mul_neg, Real.cos_neg] at hp

/-- The `χ + 1` bound on the rays `|arg z| = 2π/3`, by continuity. -/
theorem airySt_ai_boundary {z : ℂ} (hz : z ≠ 0) (harg : |arg z| = 2 * π / 3) (N : ℕ) :
    ‖airyRemainder .ai N z‖ ≤ (airyChi (N + 1 / 6) + 1) *
      ‖airyExpansionCoeff .ai N / airyZetaComplex z ^ N‖ := by
  have hπ := Real.pi_pos
  set p : ℝ → ℂ := fun φ => (‖z‖ : ℂ) * exp (φ * I) with hp
  have hpz : p (arg z) = z := norm_mul_exp_arg_mul_I z
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hpc : Continuous p := by fun_prop
  have hzs : z ∈ slitPlane := by
    rw [mem_slitPlane_iff_arg]; refine ⟨fun h => ?_, hz⟩; rw [h, abs_of_pos hπ] at harg; linarith
  have hg := ((airySt_continuousAt_rem (hpz ▸ hzs) N).comp hpc.continuousAt).norm
  have hh := (((airySt_continuousAt_T (hpz ▸ hzs) N).comp hpc.continuousAt).norm).const_mul
    (airyChi (N + 1 / 6) + 1)
  have hb : ∀ φ : ℝ, π / 3 < |φ| → |φ| < 2 * π / 3 →
      ‖airyRemainder .ai N (p φ)‖ ≤ (airyChi (N + 1 / 6) + 1) *
        ‖airyExpansionCoeff .ai N / airyZetaComplex (p φ) ^ N‖ := by
    intro φ h1 h2
    have hφ : arg (p φ) = φ := airyRot_arg hr (by linarith [neg_abs_le φ])
      (by linarith [le_abs_self φ])
    have hp0 : p φ ≠ 0 := airyRot_ofReal_mul_exp_ne_zero hr φ
    exact airySt_ai_le_chi hp0 (by rw [hφ]; exact h2) (by rw [hφ]; exact airySt_sin_ne_zero h1 h2) N
  rw [← hpz]
  rcases le_or_gt 0 (arg z) with h0 | h0
  · rw [abs_of_nonneg h0] at harg
    have hev : ∀ᶠ φ in 𝓝[<] (arg z), φ ∈ Ioo (π / 3) (2 * π / 3) := by
      rw [harg]; exact Ioo_mem_nhdsLT (by linarith)
    refine le_of_tendsto_of_tendsto (hg.tendsto.mono_left nhdsWithin_le_nhds)
      (hh.tendsto.mono_left nhdsWithin_le_nhds) (hev.mono fun φ hφ => ?_)
    have : 0 < φ := by linarith [hφ.1]
    exact hb φ (by rw [abs_of_pos this]; exact hφ.1) (by rw [abs_of_pos this]; exact hφ.2)
  · rw [abs_of_neg h0] at harg
    have hev : ∀ᶠ φ in 𝓝[>] (arg z), φ ∈ Ioo (-(2 * π / 3)) (-(π / 3)) := by
      rw [show arg z = -(2 * π / 3) by linarith]; exact Ioo_mem_nhdsGT (by linarith)
    refine le_of_tendsto_of_tendsto (hg.tendsto.mono_left nhdsWithin_le_nhds)
      (hh.tendsto.mono_left nhdsWithin_le_nhds) (hev.mono fun φ hφ => ?_)
    have : φ < 0 := by linarith [hφ.2]
    exact hb φ (by rw [abs_of_neg this]; linarith [hφ.2]) (by rw [abs_of_neg this]; linarith [hφ.1])

/-- **The Bi remainder through 9.2.11**:
`R^{Bi}_N(x) = (R_N(x e^{2πi/3}) + R_N(x e^{-2πi/3}))/2`. -/
theorem airySt_bi_rem {x : ℝ} (hx : 0 < x) (N : ℕ) :
    airyRemainder .bi N x =
      (airyRemainder .ai N ((x : ℂ) * exp (((1 * (2 * π / 3)) : ℝ) * I)) +
        airyRemainder .ai N ((x : ℂ) * exp ((((-1) * (2 * π / 3)) : ℝ) * I))) / 2 := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have hz1 := airyRot_zeta_rot hx0 harg (Or.inl rfl)
  have hz2 := airyRot_zeta_rot hx0 harg (Or.inr rfl)
  have hq1 := airyRot_quarter_rot hx0 harg (Or.inl rfl)
  have hq2 := airyRot_quarter_rot hx0 harg (Or.inr rfl)
  have hB := airyBi_eq_airyAi_omega (x : ℂ)
  have e1 : exp (2 * π * I / 3) = exp (((1 * (2 * π / 3)) : ℝ) * I) := by congr 1; push_cast; ring
  have e2 : exp (-(2 * π * I / 3)) = exp ((((-1) * (2 * π / 3)) : ℝ) * I) := by
    congr 1; push_cast; ring
  set E := exp (((1 * (π / 6)) : ℝ) * I) with hE
  have e3 : exp (π * I / 6) = E := by rw [hE]; congr 1; push_cast; ring
  have e4 : exp (-(π * I / 6)) = E⁻¹ := by rw [hE, ← exp_neg]; congr 1; push_cast; ring
  have e5 : exp ((((-1) * (π / 6)) : ℝ) * I) = E⁻¹ := by rw [hE, ← exp_neg]; congr 1; push_cast; ring
  rw [e1, e2, e3, e4] at hB
  rw [e5] at hq2
  have hE0 : E ≠ 0 := exp_ne_zero _
  have hS : ∀ w : ℂ, airyZetaComplex w = -airyZetaComplex (x : ℂ) →
      airyExponentialSum .ai N w = airyExponentialSum .bi N x := by
    intro w hw
    unfold airyExponentialSum
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hw, airyExpansionCoeff, airyExpansionCoeff, neg_eq_neg_one_mul (airyZetaComplex (x : ℂ)),
      mul_pow]
    have : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2 : airyZetaComplex (x : ℂ) ^ k ≠ 0 := pow_ne_zero _ (airySt_zeta_ne_zero hx0)
    field_simp
  simp only [airyRemainder, airyFunction]
  rw [hS _ hz1, hS _ hz2, hB]
  simp only [airyPrefactor, hz1, hz2, hq1, hq2, neg_neg]
  have hX0 : exp (airyZetaComplex (x : ℂ)) ≠ 0 := exp_ne_zero _
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : (x : ℂ) ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  field_simp
  ring

/-- `‖e^{ζ}/(√π x^{1/4})‖ = e^{ζ(x)}/(√π x^{1/4})` for `x > 0`. -/
theorem airySt_norm_prefactor_bi {x : ℝ} (hx : 0 < x) :
    ‖airyPrefactor .bi x‖ = Real.exp (airyZeta x) / (Real.sqrt π * x ^ (1 / 4 : ℝ)) := by
  have hq : ‖(x : ℂ) ^ (1 / 4 : ℂ)‖ = x ^ (1 / 4 : ℝ) := by
    rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx.le,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [airyPrefactor, norm_div, norm_mul, hq, Complex.norm_exp, airyReal_zeta_ofReal hx, ofReal_re,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- First-neglected-term remainder bound and its sign, DLMF §9.7(iii). -/
theorem airy_bi_real_error {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 0 ≤ N) :
    ‖airyRemainder .bi N x‖ ≤ (airyChi (N + 1 / 6) + 1) * 
      ‖airyExpansionCoeff .bi N / airyZetaComplex x ^ N‖ := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have hT : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ‖airyRemainder .ai N ((x : ℂ) * exp (((ε * (2 * π / 3)) : ℝ) * I))‖ ≤
        (airyChi (N + 1 / 6) + 1) * ‖airyExpansionCoeff .bi N / airyZetaComplex x ^ N‖ := by
    intro ε hε
    have hw0 : (x : ℂ) * exp (((ε * (2 * π / 3)) : ℝ) * I) ≠ 0 :=
      airyRot_ofReal_mul_exp_ne_zero hx _
    have hwa : |arg ((x : ℂ) * exp (((ε * (2 * π / 3)) : ℝ) * I))| = 2 * π / 3 := by
      have hπ := Real.pi_pos
      rcases hε with rfl | rfl
      · rw [airyRot_arg hx (by linarith) (by linarith), one_mul, abs_of_pos (by positivity)]
      · rw [airyRot_arg hx (by linarith) (by linarith), abs_of_neg (by linarith)]; ring
    have h := airySt_ai_boundary hw0 hwa N
    rw [airyRot_zeta_rot hx0 harg hε] at h
    convert h using 2
    simp only [airyExpansionCoeff, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul]
  rw [airySt_bi_rem hx N]
  calc _ ≤ (‖airyRemainder .ai N ((x : ℂ) * exp (((1 * (2 * π / 3)) : ℝ) * I))‖ +
        ‖airyRemainder .ai N ((x : ℂ) * exp ((((-1) * (2 * π / 3)) : ℝ) * I))‖) / 2 := by
        rw [norm_div, Complex.norm_two]; gcongr; exact norm_add_le _ _
    _ ≤ _ := by linarith [hT 1 (Or.inl rfl), hT (-1) (Or.inr rfl)]

/-- First-neglected-term remainder bound and its sign, DLMF §9.7(iii). -/
theorem airy_biDeriv_real_error {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) :
    ‖airyRemainder .biDeriv N x‖ ≤ (airyChi (N + 0) + 1) * 
      ‖airyExpansionCoeff .biDeriv N / airyZetaComplex x ^ N‖ := by
  sorry

/-- For `x > 0`, `Ai(x) ≤ e^{-ζ}/(2√π x^{1/4})` (DLMF 9.7.15). -/
@[dlmf 9.7.E15]
theorem airy_ai_bound {x : ℝ} (hx : 0 < x) :
    airyAiReal x ≤ Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (1 / 4 : ℝ)) := by
  have h := (airyReal_pack (a := 5 / 6) (β := -1 / 6) (N := 0) (by norm_num) (by norm_num) hx
    (f := fun z => airyAi z / airyPrefactor .ai z) (airyReal_ai_repr hx) airyRot_coeff_ai).1
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, div_one,
    airyExpansionCoeff, airyReal_airyU_zero, ofReal_one, mul_one, norm_one] at h
  have hp : airyPrefactor .ai x ≠ 0 :=
    airyRot_prefactor_ne_zero .ai (ofReal_ne_zero.mpr hx.ne')
  calc airyAiReal x ≤ ‖airyAi x‖ := Complex.re_le_norm _
    _ = ‖airyPrefactor .ai x‖ * ‖airyAi x / airyPrefactor .ai x‖ := by
      rw [← norm_mul, mul_div_cancel₀ _ hp]
    _ ≤ ‖airyPrefactor .ai x‖ * 1 := by gcongr
    _ = _ := by rw [mul_one, airyReal_norm_prefactor_ai hx]

/-- For `x > 0`, `|Ai'(x)| ≤ x^{1/4} e^{-ζ}/(2√π) (1 + 7/(72ζ))` (DLMF 9.7.15). -/
@[dlmf 9.7.E15]
theorem airy_aiDeriv_bound {x : ℝ} (hx : 0 < x) :
    |airyAiDerivReal x| ≤ x ^ (1 / 4 : ℝ) * Real.exp (-airyZeta x) / (2 * Real.sqrt π) * (1 + 7 / (72 * airyZeta x)) := by
  have h := (airyReal_pack (a := 7 / 6) (β := 1 / 6) (N := 1) (by norm_num) (by norm_num) hx
    (f := fun z => airyAiDeriv z / airyPrefactor .aiDeriv z) (airyReal_aiDeriv_repr hx)
    airyRot_coeff_aiDeriv).1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, div_one, pow_one,
    airyExpansionCoeff, airyReal_airyV_zero, airyReal_airyV_one, ofReal_one, mul_one] at h
  have hp : airyPrefactor .aiDeriv x ≠ 0 :=
    airyRot_prefactor_ne_zero .aiDeriv (ofReal_ne_zero.mpr hx.ne')
  have hz := airyZeta_pos hx
  have h1 : ‖airyAiDeriv x / airyPrefactor .aiDeriv x‖ ≤ 1 + 7 / (72 * airyZeta x) := by
    have h2 : ‖(-1 : ℂ) * ((-7 / 72 : ℝ) : ℂ) / airyZetaComplex x‖ = 7 / (72 * airyZeta x) := by
      have hz0 : (airyZeta x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz.ne'
      rw [airyReal_zeta_ofReal hx, show (-1 : ℂ) * ((-7 / 72 : ℝ) : ℂ) / ((airyZeta x : ℝ) : ℂ) =
        ((7 / (72 * airyZeta x) : ℝ) : ℂ) by push_cast; field_simp,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [h2] at h
    calc ‖airyAiDeriv x / airyPrefactor .aiDeriv x‖
        = ‖(airyAiDeriv x / airyPrefactor .aiDeriv x - 1) + 1‖ := by ring_nf
      _ ≤ ‖airyAiDeriv x / airyPrefactor .aiDeriv x - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 7 / (72 * airyZeta x) + 1 := by rw [norm_one]; gcongr
      _ = _ := by ring
  calc |airyAiDerivReal x| ≤ ‖airyAiDeriv x‖ := Complex.abs_re_le_norm _
    _ = ‖airyPrefactor .aiDeriv x‖ * ‖airyAiDeriv x / airyPrefactor .aiDeriv x‖ := by
      rw [← norm_mul, mul_div_cancel₀ _ hp]
    _ ≤ ‖airyPrefactor .aiDeriv x‖ * (1 + 7 / (72 * airyZeta x)) := by gcongr
    _ = _ := by rw [airyReal_norm_prefactor_aiDeriv hx]

/-- For `x > 0`, `Bi(x) ≤ e^{ζ}/(√π x^{1/4}) (1 + (χ(7/6) + 1) · 5/(72ζ))` (DLMF 9.7.16). -/
@[dlmf 9.7.E16]
theorem airy_bi_bound {x : ℝ} (hx : 0 < x) :
    airyBiReal x ≤ Real.exp (airyZeta x) / (Real.sqrt π * x ^ (1 / 4 : ℝ)) * (1 + (airyChi (7 / 6) + 1) * 5 / (72 * airyZeta x)) := by
  have h := airy_bi_real_error hx (N := 1) (Nat.zero_le _)
  have hz := airyZeta_pos hx
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hp : airyPrefactor .bi x ≠ 0 := airyRot_prefactor_ne_zero .bi hx0
  have hT : ‖airyExpansionCoeff .bi 1 / airyZetaComplex x ^ 1‖ = 5 / (72 * airyZeta x) := by
    rw [airyExpansionCoeff, airyReal_airyU_one, pow_one, airyReal_zeta_ofReal hx, norm_div,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by norm_num),
      Real.norm_of_nonneg hz.le]
    ring
  rw [hT, show ((1 : ℕ) : ℝ) + 1 / 6 = 7 / 6 by norm_num] at h
  have hS : airyExponentialSum .bi 1 x = 1 := by
    simp [airyExponentialSum, airyExpansionCoeff, airyReal_airyU_zero]
  have h1 : ‖airyBi x / airyPrefactor .bi x‖ ≤ 1 + (airyChi (7 / 6) + 1) * 5 / (72 * airyZeta x) := by
    have he : airyBi x / airyPrefactor .bi x = 1 + airyRemainder .bi 1 x := by
      rw [airyRemainder, airyFunction, hS]; ring
    rw [he]
    calc ‖1 + airyRemainder .bi 1 x‖ ≤ ‖(1 : ℂ)‖ + ‖airyRemainder .bi 1 x‖ := norm_add_le _ _
      _ ≤ 1 + (airyChi (7 / 6) + 1) * (5 / (72 * airyZeta x)) := by rw [norm_one]; gcongr
      _ = _ := by ring
  calc airyBiReal x ≤ ‖airyBi x‖ := Complex.re_le_norm _
    _ = ‖airyPrefactor .bi x‖ * ‖airyBi x / airyPrefactor .bi x‖ := by
      rw [← norm_mul, mul_div_cancel₀ _ hp]
    _ ≤ ‖airyPrefactor .bi x‖ * (1 + (airyChi (7 / 6) + 1) * 5 / (72 * airyZeta x)) := by gcongr
    _ = _ := by rw [airySt_norm_prefactor_bi hx]

/-- A linear upper bound for the Chi multiplier above one. -/
theorem airyDer_chi_le {s : ℝ} (hs : 1 ≤ s) : airyChi s ≤ π*s/2 := by
  have hs0 : 0 < s := by linarith
  have h1 := airySt_chi_integral hs0 (show (0:ℝ)<1 by norm_num)
  have h0 := airySt_chi_integral (show (0:ℝ)<1 by norm_num) (show (0:ℝ)<1 by norm_num)
  have hChi : airySt_chi 1 = π/2 := by
    unfold airySt_chi
    have hG : Real.Gamma (3/2:ℝ) = Real.sqrt π/2 := by
      rw [show (3/2:ℝ)=(1/2)+1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
      ring
    norm_num only
    rw [hG, Real.Gamma_one]
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  have hI : (∫ t : ℝ in Ioi 0, (1^2+t^2)^(-(s+1)/2)) ≤
      ∫ t : ℝ in Ioi 0, (1^2+t^2)^(-((1:ℝ)+1)/2) := by
    have hi : ∀ q : ℝ, 0 < q → IntegrableOn (fun t : ℝ => (1^2+t^2)^(-(q+1)/2)) (Ioi 0) := by
      intro q hq
      have hh := TauCeti.integrable_one_add_sq_rpow (s := (q+1)/2) (by linarith)
      have he : (fun t : ℝ => (1^2+t^2)^(-(q+1)/2)) =
          (fun t : ℝ => (1+t^2)^(-((q+1)/2))) := by
        funext t; congr 1 <;> ring
      rw [he]
      exact hh.integrableOn
    refine setIntegral_mono_on (hi s hs0) (hi 1 one_pos) measurableSet_Ioi fun t ht => ?_
    exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg t]) (by linarith)
  rw [hChi] at h0
  simp only [one_pow, Real.one_rpow, Real.Gamma_one, one_mul, mul_one] at h0 h1 hI
  rw [Real.Gamma_add_one hs0.ne'] at h1
  change s*Real.Gamma s * _ = Real.Gamma s * airyChi s at h1
  have hGs := Real.Gamma_pos_of_pos hs0
  have hG2 : Real.Gamma ((1:ℝ)+1)=1 := by norm_num [Real.Gamma_add_one]
  rw [hG2, one_mul] at h0
  rw [h0] at hI
  have he : airyChi s = s * ∫ t : ℝ in Ioi 0, (1+t^2)^(-(s+1)/2) := by
    apply (mul_left_cancel₀ hGs.ne')
    linear_combination -h1
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hI hs0.le]

/-- A coarse Gamma bound used only for the derivative's real-axis estimate. -/
theorem airyDer_Gamma_third : (5/2:ℝ) ≤ Real.Gamma (1/3) := by
  have hG : 0 < Real.Gamma (1/3:ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  have hrec : Real.Gamma (4/3:ℝ) = Real.Gamma (1/3)/3 := by
    rw [show (4/3:ℝ)=(1/3)+1 by norm_num, Real.Gamma_add_one (by norm_num)]
    ring
  have hbin := DLMF.Gamma.log_Gamma_eq_add_binetIntegral (x := (4/3:ℝ)) (by norm_num)
  have hbin0 := (DLMF.Gamma.binetIntegral_mem (x := (4/3:ℝ)) (by norm_num)).1
  rw [hrec, Real.log_div hG.ne' (by norm_num)] at hbin
  have hlog : 6*Real.log 3 + 5*Real.log (4/3:ℝ) + 3*Real.log (2*π) - 8 ≤
      6*Real.log (Real.Gamma (1/3:ℝ)) := by linarith
  have hexp := Real.exp_le_exp.mpr hlog
  have heq : Real.exp (6*Real.log 3 + 5*Real.log (4/3:ℝ) + 3*Real.log (2*π) - 8) =
      24576*π^3/Real.exp 8 := by
    rw [Real.exp_sub, Real.exp_add, Real.exp_add,
      show 6*Real.log 3 = (6:ℕ)*Real.log 3 by norm_num,
      show 5*Real.log (4/3:ℝ) = (5:ℕ)*Real.log (4/3:ℝ) by norm_num,
      show 3*Real.log (2*π) = (3:ℕ)*Real.log (2*π) by norm_num,
      Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log (by norm_num), Real.exp_log (by norm_num), Real.exp_log (by positivity)]
    ring
  rw [heq, show 6*Real.log (Real.Gamma (1/3:ℝ)) = (6:ℕ)*Real.log (Real.Gamma (1/3:ℝ)) by norm_num,
    Real.exp_nat_mul, Real.exp_log hG] at hexp
  have he : Real.exp 8 ≤ (49/18:ℝ)^8 := by
    rw [show (8:ℝ)=(8:ℕ)*1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9]) _
  have hpi : (25/8:ℝ)^3 ≤ π^3 := pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_d6]) _
  rw [div_le_iff₀ (Real.exp_pos _)] at hexp
  by_contra h
  have hlt : Real.Gamma (1/3:ℝ)^6 < (5/2:ℝ)^6 :=
    pow_lt_pow_left₀ (not_le.mp h) hG.le (by omega)
  have hh := mul_le_mul_of_nonneg_left he (pow_nonneg hG.le 6)
  nlinarith

/-- The Airy energy on the positive axis is bounded by its initial value. -/
theorem airyDer_energy {x : ℝ} (hx : 0 ≤ x) :
    airyBiDerivReal x^2 ≤ x*airyBiReal x^2 + airyBiDerivReal 0^2 := by
  have hf (t : ℝ) : HasDerivAt airyBiReal (airyBiDerivReal t) t :=
    (hasDerivAt_airyBi t).real_of_complex
  have hg (t : ℝ) : HasDerivAt airyBiDerivReal (t*airyBiReal t) t := by
    exact ((hasDerivAt_airyBiDeriv t).real_of_complex).congr_deriv (by simp [airyBiReal])
  have hd (t : ℝ) : HasDerivAt (fun t => airyBiDerivReal t^2-t*airyBiReal t^2)
      (-airyBiReal t^2) t := by
    convert ((hg t).pow 2).sub ((hasDerivAt_id t).mul ((hf t).pow 2)) using 1
    · funext u; rfl
    · simp only [Pi.pow_apply, id_eq]; ring
  have hm := antitone_of_deriv_nonpos (fun t => (hd t).differentiableAt)
    (fun t => by rw [(hd t).deriv]; exact neg_nonpos.mpr (sq_nonneg _))
  have h := hm hx
  simp only [zero_mul, sub_zero] at h
  linarith

/-- A coarse bound on the initial derivative. -/
theorem airyDer_initial_sq : airyBiDerivReal 0^2 ≤ (52/225:ℝ) := by
  have hG := airyDer_Gamma_third
  have hG0 := Real.Gamma_pos_of_pos (show (0:ℝ)<1/3 by norm_num)
  have hr : ((3:ℝ)^(1/3:ℝ))^3 = 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hroot : (3:ℝ)^(1/3:ℝ) ≤ 13/9 := by
    apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _) (by norm_num) (by omega : 3≠0)).mp
    rw [hr]; norm_num
  have hq : ((3:ℝ)^(1/6:ℝ))^2 = (3:ℝ)^(1/3:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; norm_num
  have hz : airyBiDerivReal 0 = (3:ℝ)^(1/6:ℝ)/Real.Gamma (1/3) := by
    rw [airyBiDerivReal, ofReal_zero, airyBiDeriv_zero,
      show (1/3:ℂ)=((1/3:ℝ):ℂ) by norm_num, Complex.Gamma_ofReal, ← ofReal_div, ofReal_re]
  rw [hz, div_pow, hq, div_le_iff₀ (pow_pos hG0 2)]
  nlinarith

/-- Real power identities in the Airy saddle variable. -/
theorem airyDer_power_data {x : ℝ} (hx : 0 < x) :
    airyZeta x=2/3*(Real.sqrt x)^3 ∧ (x^(1/4:ℝ))^2=Real.sqrt x := by
  constructor
  · rw [airyZeta, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 2; norm_num
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1; norm_num

/-- A polynomial certificate for the elementary exponential envelope. -/
theorem airyDer_envelope_poly {u : ℝ} (hu : 0 ≤ u) :
    (181/2916:ℝ)*u^12 +
      (2155529/13436928:ℝ)*u^9 +
      (1529993/5971968:ℝ)*u^6 +
      (-1144/1575:ℝ)*u^5 +
      (904457/3981312:ℝ)*u^3 +
      (278921/5308416:ℝ) ≥ 0 := by
  by_cases hsmall : u ≤ 1/2
  · have hu3 : 0 ≤ u^3 := pow_nonneg hu 3
    have hu2 : u^2 ≤ (1/4:ℝ) := by nlinarith
    have hu5 : u^5 ≤ u^3/4 := by nlinarith [mul_le_mul_of_nonneg_left hu2 hu3]
    nlinarith [pow_nonneg hu 6, pow_nonneg hu 9, pow_nonneg hu 12]
  · have hu1 : (1/2:ℝ) ≤ u := le_of_lt (not_le.mp hsmall)
    let Q : ℝ := (181/2916:ℝ)*u^10 +
      (1991/17496:ℝ)*u^9 +
      (21901/139968:ℝ)*u^8 +
      (14175739/40310784:ℝ)*u^7 +
      (124132877/241864704:ℝ)*u^6 +
      (1248860723/1934917632:ℝ)*u^5 +
      (17557622459/17414258688:ℝ)*u^4 +
      (84803311431641/146279772979200:ℝ)*u^3 +
      (21030123845489/97519848652800:ℝ)*u^2 +
      (2852020772397883/21064287309004800:ℝ)*u +
      (1058802953579899/15798215481753600:ℝ)
    have hq : 0 ≤ Q := by dsimp only [Q]; positivity
    have hrem : 0 ≤ (1840275079998707/202217158166446080:ℝ)*u + (-8582440901337379/2274943029372518400:ℝ) := by linarith
    have he : (181/2916:ℝ)*u^12 +
      (2155529/13436928:ℝ)*u^9 +
      (1529993/5971968:ℝ)*u^6 +
      (-1144/1575:ℝ)*u^5 +
      (904457/3981312:ℝ)*u^3 +
      (278921/5308416:ℝ) =
        (u-11/12)^2*Q+((1840275079998707/202217158166446080:ℝ)*u + (-8582440901337379/2274943029372518400:ℝ)) := by dsimp only [Q]; ring
    rw [he]
    positivity

/-- An elementary gap between two positive exponential envelopes. -/
theorem airyDer_envelope_gap {x : ℝ} (hx : 0 < x) :
    (52/225:ℝ) ≤ Real.exp (2*airyZeta x)*Real.sqrt x/π *
      ((1+(287/1152:ℝ)/airyZeta x)^2-(1+(85/432:ℝ)/airyZeta x)^2) := by
  set u := Real.sqrt x with huDef
  have hu : 0 < u := Real.sqrt_pos.mpr hx
  have hz := (airyDer_power_data hx).1
  set z := airyZeta x with hzDef
  have hz0 : 0 < z := airyZeta_pos hx
  have hzEq : z=2/3*u^3 := hz
  set T : ℝ := 1+2*z+2*z^2+4*z^3/3
  set D : ℝ := (1+(287/1152:ℝ)/z)^2-(1+(85/432:ℝ)/z)^2
  have hD : 0 ≤ D := by
    have hh : 0 ≤ 1+(85/432:ℝ)/z := by positivity
    have hle : 1+(85/432:ℝ)/z ≤ 1+(287/1152:ℝ)/z := by
      have hh : (85/432:ℝ)/z ≤ (287/1152:ℝ)/z :=
        div_le_div_of_nonneg_right (by norm_num) hz0.le
      linarith
    dsimp only [D]
    nlinarith
  have hT : T ≤ Real.exp (2*z) := by
    have h := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ 2*z) 4
    norm_num [Finset.sum_range_succ] at h
    dsimp only [T]
    nlinarith
  have hpoly := airyDer_envelope_poly hu.le
  have he : T*u*D-(22/7:ℝ)*(52/225) = ((181/2916:ℝ)*u^12+(2155529/13436928:ℝ)*u^9+(1529993/5971968:ℝ)*u^6+(-1144/1575:ℝ)*u^5+(904457/3981312:ℝ)*u^3+(278921/5308416:ℝ))/u^5 := by
    dsimp only [T,D]
    rw [hzEq]
    field_simp
    ring
  have hmain : (22/7:ℝ)*(52/225) ≤ T*u*D := by
    rw [← sub_nonneg, he]
    exact div_nonneg hpoly (pow_nonneg hu.le 5)
  change (52/225:ℝ) ≤ Real.exp (2*z)*u/π*D
  rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
  calc (52/225:ℝ)*π ≤ (22/7:ℝ)*(52/225) := by nlinarith [Real.pi_lt_d6]
    _ ≤ T*u*D := hmain
    _ ≤ Real.exp (2*z)*u*D := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hT hu.le) hD

/-- The real-axis Bi derivative bound, DLMF 9.7.16. -/
@[dlmf 9.7.E16]
theorem airy_biDeriv_bound {x : ℝ} (hx : 0 < x) :
    airyBiDerivReal x ≤ x^(1/4:ℝ)*Real.exp (airyZeta x)/Real.sqrt π *
      (1+(π/2+1)*7/(72*airyZeta x)) := by
  have hz := airyZeta_pos hx
  have hπ := Real.pi_pos
  have hq : 0 < x^(1/4:ℝ) := Real.rpow_pos_of_pos hx _
  have hS := Real.sqrt_pos.mpr hπ
  have hc : (airyChi (7/6)+1)*5/72 ≤ (85/432:ℝ) := by
    have h := airyDer_chi_le (s := (7/6:ℝ)) (by norm_num)
    have hp : π ≤ (22/7:ℝ) := by linarith [Real.pi_lt_d6]
    nlinarith
  have hA : (287/1152:ℝ) ≤ (π/2+1)*7/72 := by linarith [Real.pi_gt_d6]
  set P := x^(1/4:ℝ)*Real.exp (airyZeta x)/Real.sqrt π
  set B := Real.exp (airyZeta x)/(Real.sqrt π*x^(1/4:ℝ)) *
    (1+(85/432:ℝ)/airyZeta x)
  have hP0 : 0 < P := by dsimp [P]; positivity
  have hB0 : 0 < B := by dsimp [B]; positivity
  have hB : airyBiReal x ≤ B := by
    have h := airy_bi_bound hx
    have he : (airyChi (7/6)+1)*5/(72*airyZeta x) =
        ((airyChi (7/6)+1)*5/72)/airyZeta x := by ring
    rw [he] at h
    refine h.trans ?_
    dsimp only [B]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [div_le_div_of_nonneg_right hc hz.le]
  have hBi0 : 0 ≤ airyBiReal x := by
    obtain ⟨r, hr, he⟩ := airyBi_ofReal_pos hx.le
    simpa [airyBiReal, he] using hr.le
  have hBiSq : airyBiReal x^2 ≤ B^2 := by nlinarith
  have hq4 : (x^(1/4:ℝ))^4=x := by
    calc (x^(1/4:ℝ))^4 = ((x^(1/4:ℝ))^2)^2 := by ring
      _ = x := by rw [(airyDer_power_data hx).2, Real.sq_sqrt hx.le]
  have hbase : x*(Real.exp (airyZeta x)/(Real.sqrt π*x^(1/4:ℝ)))^2=P^2 := by
    dsimp only [P]
    nth_rw 1 [← hq4]
    field_simp
  have hBsq : x*B^2 = P^2*(1+(85/432:ℝ)/airyZeta x)^2 := by
    dsimp only [B]
    rw [mul_pow, ← mul_assoc, hbase]
  have hPsq : P^2=Real.exp (2*airyZeta x)*Real.sqrt x/π := by
    dsimp only [P]
    rw [div_pow, mul_pow, (airyDer_power_data hx).2, Real.sq_sqrt hπ.le,
      ← Real.exp_nat_mul]
    norm_num only
    ring
  have hgap := airyDer_envelope_gap hx
  rw [← hPsq] at hgap
  have hsquares : airyBiDerivReal x^2 ≤ (P*(1+(287/1152:ℝ)/airyZeta x))^2 := by
    have henergy := airyDer_energy hx.le
    have hzero := airyDer_initial_sq
    have hBB := mul_le_mul_of_nonneg_left hBiSq hx.le
    rw [hBsq] at hBB
    nlinarith
  have hR0 : 0 ≤ P*(1+(287/1152:ℝ)/airyZeta x) := by positivity
  have hresult : airyBiDerivReal x ≤ P*(1+(287/1152:ℝ)/airyZeta x) := by nlinarith
  refine hresult.trans ?_
  change P*(1+(287/1152:ℝ)/airyZeta x) ≤ P*(1+(π/2+1)*7/(72*airyZeta x))
  have he : (π/2+1)*7/(72*airyZeta x) = ((π/2+1)*7/72)/airyZeta x := by ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ hP0.le
  linarith [div_le_div_of_nonneg_right hA hz.le]

/-- On the slit plane the remainder of the normalized `Ai` expansion is bounded by the error
multiplier times the first neglected term (DLMF 9.7.17). -/
@[dlmf 9.7.E17]
theorem airy_ai_complex_error {z : ℂ} (hz : z ∈ slitPlane) {N : ℕ} (hN : 0 ≤ N) :
    ‖airyRemainder .ai N z‖ ≤ airyErrorMultiplier N (1 / 6) z *
      ‖airyExpansionCoeff .ai N / airyZetaComplex z ^ N‖ := by
  have hπ := Real.pi_pos
  have hz0 := slitPlane_ne_zero hz
  have hlt : |arg z| < π := by
    rw [mem_slitPlane_iff_arg] at hz
    exact lt_of_le_of_ne (abs_le.mpr ⟨(neg_pi_lt_arg z).le, arg_le_pi z⟩) (fun h => by
      rcases abs_eq hπ.le |>.mp h with h' | h'
      · exact hz.1 h'
      · linarith [neg_pi_lt_arg z])
  unfold airyErrorMultiplier
  split_ifs with h1 h2 h3
  · have hM : airySt_M (-(3 / 2 * arg z)) = 1 := by
      unfold airySt_M
      rw [Real.cos_neg]
      split_ifs with hc
      · rfl
      · exact absurd (Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_le.mp h1],
          by linarith [abs_le.mp h1]⟩) hc
    have := airySt_ai_le_M hz0 (by linarith) N
    rwa [hM] at this
  · rcases lt_or_eq_of_le h2 with h | h
    · exact absurd h3 (airySt_sin_ne_zero (lt_of_not_ge h1) h)
    · exact airySt_ai_boundary hz0 h N
  · rcases lt_or_eq_of_le h2 with h | h
    · have hM : airySt_M (-(3 / 2 * arg z)) = |(Real.sin (3 * arg z / 2))⁻¹| := by
        unfold airySt_M
        rw [Real.cos_neg]
        split_ifs with hc
        · exact absurd hc (not_le.mpr (airySt_cos_neg (lt_of_not_ge h1) h))
        · rw [Real.sin_neg, abs_neg, abs_inv, show 3 / 2 * arg z = 3 * arg z / 2 by ring]
      have hA := airySt_ai_le_M hz0 h N
      have hB := airySt_ai_le_chi hz0 h h3 N
      rw [hM] at hA
      rw [min_mul_of_nonneg _ _ (norm_nonneg _)]
      exact le_min hA hB
    · exfalso; apply h3
      rcases le_or_gt 0 (arg z) with h0 | h0
      · rw [abs_of_nonneg h0] at h; rw [h, show 3 * (2 * π / 3) / 2 = π by ring, Real.sin_pi]
      · rw [abs_of_neg h0] at h
        rw [show arg z = -(2 * π / 3) by linarith, show 3 * -(2 * π / 3) / 2 = -π by ring,
          Real.sin_neg, Real.sin_pi, neg_zero]
  · exact airySt_ai_third hz0 (lt_of_not_ge h2) hlt N

/-- On the slit plane, for `N ≥ 1`, the remainder of the normalized `Ai'` expansion is bounded
by the error multiplier times the first neglected term (DLMF 9.7.17). -/
@[dlmf 9.7.E17]
theorem airy_aiDeriv_complex_error {z : ℂ} (hz : z ∈ slitPlane) {N : ℕ} (hN : 1 ≤ N) :
    ‖airyRemainder .aiDeriv N z‖ ≤ airyErrorMultiplier N (0) z *
      ‖airyExpansionCoeff .aiDeriv N / airyZetaComplex z ^ N‖ := by
  sorry

/-- `Ai(z)` is its prefactor times the truncated series plus the exact remainder
(DLMF 9.7.18). -/
@[dlmf 9.7.E18]
theorem airy_ai_exact_remainder {z : ℂ} (hz : z ≠ 0) (N : ℕ) :
    airyFunction .ai z = airyPrefactor .ai z *
      (airyExponentialSum .ai N z + airyRemainder .ai N z) := by
  have hp : airyPrefactor .ai z ≠ 0 := by
    dsimp only [airyPrefactor]
    have hπ : (Real.sqrt π : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hz' : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
    exact div_ne_zero (exp_ne_zero _) (mul_ne_zero (mul_ne_zero two_ne_zero hπ) hz')
  unfold airyRemainder
  field_simp
  ring

/-- `Ai'(z)` is its prefactor times the truncated series plus the exact remainder
(DLMF 9.7.19). -/
@[dlmf 9.7.E19]
theorem airy_aiDeriv_exact_remainder {z : ℂ} (hz : z ≠ 0) (N : ℕ) :
    airyFunction .aiDeriv z = airyPrefactor .aiDeriv z *
      (airyExponentialSum .aiDeriv N z + airyRemainder .aiDeriv N z) := by
  have hp : airyPrefactor .aiDeriv z ≠ 0 := by
    dsimp only [airyPrefactor]
    have hπ : (Real.sqrt π : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hz' : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hz') (exp_ne_zero _)) (mul_ne_zero two_ne_zero hπ)
  unfold airyRemainder
  field_simp
  ring

/-- Re-expansion of the `Ai` remainder in terminants `F_{n-k}(2ζ)` with second-level
remainder `airyHyperRemainder` (DLMF 9.7.20). -/
@[dlmf 9.7.E20]
theorem airy_R_hyper_reexpansion (m n : ℕ) (z : ℂ) :
    airyRemainder .ai n z =
      (-1 : ℂ) ^ (n) *
        (∑ k ∈ Finset.range m, (-1 : ℂ) ^ k * (airyU k : ℂ) *
          airyTerminator ((n : ℂ) - k) (log 2 + airyLogZeta z) / airyZetaComplex z ^ k) +
      airyHyperRemainder false m n z := by
  norm_num [airyHyperRemainder]

/-- Re-expansion of the `Ai'` remainder in terminants `F_{n-k}(2ζ)` with second-level
remainder `airyHyperRemainder` (DLMF 9.7.21). -/
@[dlmf 9.7.E21]
theorem airy_S_hyper_reexpansion (m n : ℕ) (z : ℂ) :
    airyRemainder .aiDeriv n z =
      (-1 : ℂ) ^ (n - 1) *
        (∑ k ∈ Finset.range m, (-1 : ℂ) ^ k * (airyV k : ℂ) *
          airyTerminator ((n : ℂ) - k) (log 2 + airyLogZeta z) / airyZetaComplex z ^ k) +
      airyHyperRemainder true m n z := by
  norm_num [airyHyperRemainder]

/-- At the optimal index `n ≈ 2|ζ|` the second-level `Ai` remainder is
`O(e^{-2|ζ|} |ζ|^{-m})` in `|arg z| ≤ 2π/3` (DLMF 9.7.23). -/
@[dlmf 9.7.E23]
theorem airy_R_hyper_error (m : ℕ) :
    IsBigO (airySector (2 * π / 3)) (fun z => airyHyperRemainder false m (airyOptimalIndex z) z)
      (fun z => Real.exp (-2 * ‖airyZetaComplex z‖) * ‖airyZetaComplex z‖ ^ (-(m : ℤ))) := by
  sorry

/-- At the optimal index `n ≈ 2|ζ|` the second-level `Ai'` remainder is
`O(e^{-2|ζ|} |ζ|^{-m})` in `|arg z| ≤ 2π/3` (DLMF 9.7.23). -/
@[dlmf 9.7.E23]
theorem airy_S_hyper_error (m : ℕ) :
    IsBigO (airySector (2 * π / 3)) (fun z => airyHyperRemainder true m (airyOptimalIndex z) z)
      (fun z => Real.exp (-2 * ‖airyZetaComplex z‖) * ‖airyZetaComplex z‖ ^ (-(m : ℤ))) := by
  sorry

/-- The exact even/odd coefficients obtained by inverting the real sine/cosine system. -/
def airyOscComponent (derivative : Bool) (parity : Fin 2) (x : ℝ) : ℂ :=
  let θ : ℂ := airyZeta x - π / 4
  let pref := airyOscPrefactor (if derivative then .aiDeriv else .ai) x
  if derivative then
    if parity.val = 0 then (sin θ * airyAiDeriv (-x) + cos θ * airyBiDeriv (-x)) / pref
    else (-cos θ * airyAiDeriv (-x) + sin θ * airyBiDeriv (-x)) / pref
  else
    if parity.val = 0 then (cos θ * airyAi (-x) - sin θ * airyBi (-x)) / pref
    else (sin θ * airyAi (-x) + cos θ * airyBi (-x)) / pref

end DLMF.Airy
end
