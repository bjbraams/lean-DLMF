/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Digamma
public import DLMF.Gamma.Multiplication

/-!
# Gauss's multiplication formula for the digamma function (AAR Theorem 1.2.7)

Logarithmic differentiation of Gauss multiplication (AAR 1.5.2) yields, for `m > 0` and
`s > 0`,

$$
\sum_{k=0}^{m-1}\psi\bigl(s+k/m\bigr)= m\,\psi(ms)-m\log m.
$$

This is the first identity of AAR Theorem 1.2.7 (in the form obtained from
`Γ(x+n) = (x)_n Γ(x)` by taking logarithmic derivatives, together with the multiplication
formula). Combined with reflection `ψ(1-x)-ψ(x)=π cot(πx)` one obtains Gauss's evaluation
of `ψ` at rational arguments; the case `ψ(1/2)` is recorded below.
-/

@[expose] public section

open Finset Set Filter

open scoped Topology Real

noncomputable section

namespace Real

local notation "γ" => eulerMascheroniConstant

theorem hasDerivAt_log_Gamma_add_div {m : ℕ} {s : ℝ} (hs : 0 < s) (k : ℕ) :
    HasDerivAt (fun y : ℝ => log (Gamma (y + k / m))) (digamma (s + k / m)) s := by
  have hpos : 0 < s + k / m :=
    add_pos_of_pos_of_nonneg hs (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hshift : HasDerivAt (fun y : ℝ => y + k / m) 1 s := (hasDerivAt_id s).add_const _
  have hG : DifferentiableAt ℝ Gamma (s + k / m) :=
    differentiableAt_Gamma fun t =>
      ((neg_nonpos.mpr t.cast_nonneg).trans_lt hpos).ne'
  have hlog := hG.hasDerivAt.log (Gamma_pos_of_pos hpos).ne'
  simpa [digamma, Function.comp_def] using hlog.comp s hshift

theorem hasDerivAt_sum_log_Gamma_add_div {m : ℕ} {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun y : ℝ => ∑ k ∈ range m, log (Gamma (y + k / m)))
      (∑ k ∈ range m, digamma (s + k / m)) s :=
  HasDerivAt.fun_sum fun k _ => hasDerivAt_log_Gamma_add_div hs k

theorem hasDerivAt_log_Gamma_mul {m : ℕ} (hm : 0 < m) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun y : ℝ => log (Gamma (m * y))) (m * digamma (m * s)) s := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hs' : 0 < m * s := mul_pos hm0 hs
  have hmul : HasDerivAt (fun y : ℝ => (m : ℝ) * y) m s := by
    simpa using (hasDerivAt_id s).const_mul (m : ℝ)
  have hG : DifferentiableAt ℝ Gamma (m * s) :=
    differentiableAt_Gamma fun t =>
      ((neg_nonpos.mpr t.cast_nonneg).trans_lt hs').ne'
  have hlog := hG.hasDerivAt.log (Gamma_pos_of_pos hs').ne'
  simpa [digamma, Function.comp_def, mul_comm] using hlog.comp s hmul

/-- Logarithmic derivative of Gauss multiplication (AAR Theorem 1.2.7, first formula). -/
@[dlmf 5.5.E9]
theorem digamma_sum_add_div {m : ℕ} (hm : 0 < m) {s : ℝ} (hs : 0 < s) :
    ∑ k ∈ range m, digamma (s + k / m) = m * digamma (m * s) - m * log m := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hlin : HasDerivAt (fun y : ℝ => (1 / 2 - m * y) * log m) (-m * log m) s := by
    have h1 : HasDerivAt (fun y : ℝ => (m : ℝ) * y) m s := by
      simpa using (hasDerivAt_id s).const_mul (m : ℝ)
    have h2 : HasDerivAt (fun y : ℝ => 1 / 2 - m * y) (-m) s := by
      have hsub := (hasDerivAt_const s (1 / 2 : ℝ)).sub h1
      have hfun : (fun y : ℝ => 1 / 2 - m * y) =ᶠ[𝓝 s]
          ((fun _ : ℝ => (1 / 2 : ℝ)) - fun y => (m : ℝ) * y) :=
        Eventually.of_forall fun y => by simp [Pi.sub_apply]
      simpa using hsub.congr_of_eventuallyEq hfun
    simpa using h2.mul_const (log m)
  have hconst : HasDerivAt (fun _ : ℝ => log ((2 * π) ^ ((m - 1 : ℝ) / 2))) 0 s :=
    hasDerivAt_const _ _
  have hG := hasDerivAt_log_Gamma_mul hm hs
  have hC : HasDerivAt
      (fun y : ℝ => log ((2 * π) ^ ((m - 1 : ℝ) / 2)) + (1 / 2 - m * y) * log m +
        log (Gamma (m * y)))
      (-m * log m + m * digamma (m * s)) s := by
    have hadd := (hconst.add hlin).add hG
    have hfun : (fun y : ℝ => log ((2 * π) ^ ((m - 1 : ℝ) / 2)) + (1 / 2 - m * y) * log m +
          log (Gamma (m * y))) =ᶠ[𝓝 s]
        (((fun _ : ℝ => log ((2 * π) ^ ((m - 1 : ℝ) / 2))) +
            fun y => (1 / 2 - m * y) * log m) + fun y => log (Gamma (m * y))) :=
      Eventually.of_forall fun y => by simp [Pi.add_apply]
    have hder : 0 + -m * log m + m * digamma (m * s) = -m * log m + m * digamma (m * s) := by
      ring
    simpa [hder] using hadd.congr_of_eventuallyEq hfun
  have hlhs := hasDerivAt_sum_log_Gamma_add_div hs (m := m)
  have heq : (fun y : ℝ => ∑ k ∈ range m, log (Gamma (y + k / m))) =ᶠ[𝓝 s]
      fun y => log ((2 * π) ^ ((m - 1 : ℝ) / 2)) + (1 / 2 - m * y) * log m +
        log (Gamma (m * y)) := by
    filter_upwards [Ioi_mem_nhds hs] with y hy
    have hprod := Gamma_prod_add_div_of_pos hm hy
    have hposP : 0 < ∏ k ∈ range m, Gamma (y + k / m) :=
      prod_pos fun k _ =>
        Gamma_pos_of_pos
          (add_pos_of_pos_of_nonneg hy (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    have hposC : 0 < (2 * π) ^ ((m - 1 : ℝ) / 2) :=
      rpow_pos_of_pos (mul_pos two_pos pi_pos) _
    have hposM : 0 < (m : ℝ) ^ (1 / 2 - m * y) := rpow_pos_of_pos hm0 _
    have hposG : 0 < Gamma (m * y) := Gamma_pos_of_pos (mul_pos hm0 hy)
    have : log (∏ k ∈ range m, Gamma (y + k / m)) =
        log ((2 * π) ^ ((m - 1 : ℝ) / 2) * (m : ℝ) ^ (1 / 2 - m * y) * Gamma (m * y)) := by
      rw [hprod]
    rw [log_prod fun k _ =>
        (Gamma_pos_of_pos
          (add_pos_of_pos_of_nonneg hy (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))).ne']
      at this
    rw [log_mul (mul_pos hposC hposM).ne' hposG.ne', log_mul hposC.ne' hposM.ne',
      log_rpow hm0] at this
    linarith
  have := (hC.congr_of_eventuallyEq heq).unique hlhs
  linarith

/-- Special case `m = 2` of the multiplication formula for `ψ`. -/
@[dlmf 5.5.E8]
theorem digamma_add_digamma_add_half {s : ℝ} (hs : 0 < s) :
    digamma s + digamma (s + 1 / 2) = 2 * digamma (2 * s) - 2 * log 2 := by
  have h2s : ∀ m : ℕ, 2 * (s : ℂ) ≠ -m := fun m h => by
    have : 2 * s = -(m : ℝ) := by exact_mod_cast h
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h := Complex.digamma_two_mul h2s
  have hlog : (Complex.log 2).re = log 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num),
      Complex.ofReal_re]
  rw [digamma_eq_re_digamma hs, digamma_eq_re_digamma (by linarith),
    digamma_eq_re_digamma (by linarith)]
  push_cast
  rw [h]
  simp only [Complex.add_re, Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.one_re, Complex.one_im, hlog]
  ring

/-- `ψ(1/2) = -γ - 2 log 2`, AAR Theorem 1.2.7 at `p/q = 1/2`. -/
@[dlmf 5.4.E13]
theorem digamma_one_div_two : digamma (1 / 2) = -γ - 2 * log 2 := by
  have hlog : (Complex.log 2).re = log 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num),
      Complex.ofReal_re]
  rw [digamma_eq_re_digamma (by norm_num)]
  push_cast
  rw [Complex.digamma_one_half]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hlog]
  norm_num
  ring

theorem cot_pi_div_three : cot (π / 3) = 1 / sqrt 3 := by
  rw [cot_eq_cos_div_sin, cos_pi_div_three, sin_pi_div_three, div_div_eq_mul_div]
  ring

theorem cot_pi_div_four : cot (π / 4) = 1 := by
  rw [cot_eq_cos_div_sin, cos_pi_div_four, sin_pi_div_four]
  have hne : sqrt 2 ≠ 0 := by positivity
  field [hne]

/-- `ψ(1/3) = -γ - (3/2) log 3 - π/(2√3)`, AAR Theorem 1.2.7 at `p/q = 1/3`. -/
theorem digamma_one_div_three :
    digamma (1 / 3) = -γ - (3 / 2) * log 3 - π / (2 * sqrt 3) := by
  have hs : (0 : ℝ) < 1 / 3 := by positivity
  have hmul := digamma_sum_add_div (m := 3) (by decide) hs
  rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero, zero_add] at hmul
  norm_cast at hmul
  norm_num at hmul
  rw [digamma_one] at hmul
  have hsum : digamma (1 / 3) + digamma (2 / 3) = -2 * γ - 3 * log 3 := by linarith
  have href := digamma_one_sub (by positivity : (0 : ℝ) < 1 / 3)
      (by norm_num : (1 / 3 : ℝ) < 1)
  have hcot : π * cot (π * (1 / 3)) = π / sqrt 3 := by
    have : π * (1 / 3 : ℝ) = π / 3 := by ring
    rw [this, cot_pi_div_three]
    field
  have hsub : (1 : ℝ) - 1 / 3 = 2 / 3 := by ring
  rw [hsub, hcot] at href
  have htwo : 2 * digamma (1 / 3) = -2 * γ - 3 * log 3 - π / sqrt 3 := by linarith [hsum, href]
  have hne : sqrt 3 ≠ 0 := by positivity
  have hrhs : 2 * (-γ - (3 / 2) * log 3 - π / (2 * sqrt 3)) =
      -2 * γ - 3 * log 3 - π / sqrt 3 := by field [hne]
  linarith [htwo, hrhs]

/-- `ψ(2/3) = -γ - (3/2) log 3 + π/(2√3)`. -/
theorem digamma_two_div_three :
    digamma (2 / 3) = -γ - (3 / 2) * log 3 + π / (2 * sqrt 3) := by
  have href := digamma_one_sub (by positivity : (0 : ℝ) < 1 / 3)
      (by norm_num : (1 / 3 : ℝ) < 1)
  have hcot : π * cot (π * (1 / 3)) = π / sqrt 3 := by
    have : π * (1 / 3 : ℝ) = π / 3 := by ring
    rw [this, cot_pi_div_three]
    field
  have hsub : (1 : ℝ) - 1 / 3 = 2 / 3 := by ring
  rw [hsub, hcot] at href
  have h13 := digamma_one_div_three
  have hne : sqrt 3 ≠ 0 := by positivity
  have : π / sqrt 3 = π / (2 * sqrt 3) + π / (2 * sqrt 3) := by field [hne]
  linarith [h13, href, this]

/-- `ψ(1/4) = -γ - 3 log 2 - π/2`, AAR Theorem 1.2.7 at `p/q = 1/4`. -/
theorem digamma_one_div_four :
    digamma (1 / 4) = -γ - 3 * log 2 - π / 2 := by
  have hs : (0 : ℝ) < 1 / 4 := by positivity
  have h := digamma_add_digamma_add_half hs
  have hhalf : (1 / 4 : ℝ) + 1 / 2 = 3 / 4 := by ring
  have h2 : (2 : ℝ) * (1 / 4) = 1 / 2 := by ring
  rw [hhalf, h2, digamma_one_div_two] at h
  have href := digamma_one_sub (by positivity : (0 : ℝ) < 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)
  have hcot : π * cot (π * (1 / 4)) = π := by
    have : π * (1 / 4 : ℝ) = π / 4 := by ring
    rw [this, cot_pi_div_four, mul_one]
  have hsub : (1 : ℝ) - 1 / 4 = 3 / 4 := by ring
  rw [hsub, hcot] at href
  have htwo : 2 * digamma (1 / 4) = -2 * γ - 6 * log 2 - π := by linarith
  linarith [htwo]

/-- `ψ(3/4) = -γ - 3 log 2 + π/2`. -/
theorem digamma_three_div_four :
    digamma (3 / 4) = -γ - 3 * log 2 + π / 2 := by
  have href := digamma_one_sub (by positivity : (0 : ℝ) < 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)
  have hcot : π * cot (π * (1 / 4)) = π := by
    have : π * (1 / 4 : ℝ) = π / 4 := by ring
    rw [this, cot_pi_div_four, mul_one]
  have hsub : (1 : ℝ) - 1 / 4 = 3 / 4 := by ring
  rw [hsub, hcot] at href
  linarith [digamma_one_div_four, href]

end Real
