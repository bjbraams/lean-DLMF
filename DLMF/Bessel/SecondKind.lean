/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Modified
public import DLMF.Bessel.Theorems
public import DLMF.Confluent.BasicProperties

/-!
# Bessel functions of the second kind and Hankel functions (Temme §§9.1–9.4, DLMF 10.2–10.6)

The series `J_ν(z) = (z/2)^ν ₀F₁(ν+1; -z²/4)` is jointly continuous in `(ν, z)` on `ℂ × slitPlane`
and entire in `ν`. Hence `D_ν(z) = J_ν(z) cos νπ - J_{-ν}(z)`, which vanishes at integer `ν`,
divided by `sin νπ` has a removable singularity at each integer. This shows that Weber's `Y_ν` at
integer order, defined in `besselY` as a limit, is the continuous extension, jointly in `(ν, z)`.
The recurrences, the derivative, the Bessel equation and the Wronskians then hold for every order.
-/

@[expose] public section

open Complex Filter Set
open scoped Real Nat Topology
open DLMF.Confluent

noncomputable section

namespace DLMF.Bessel

/-! ### The `₀F₁` series in the parameter -/

/-- Identity under the stated parameter and domain assumptions: `regularizedHGFun (∅ : Multiset ℂ)
{c} w = ∑' n : ℕ, w ^ n / n ! * (Gamma (c + n))⁻¹`. -/
theorem regularized0F1_eq_tsum (c w : ℂ) :
    regularizedHGFun (∅ : Multiset ℂ) {c} w = ∑' n : ℕ, w ^ n / n ! * (Gamma (c + n))⁻¹ := by
  rw [regularizedHGFun_eq_tsum]
  congr 1; funext n
  rw [regularizedHGFunCoeff_empty]; field_simp

/-- Summability of the indicated series: `Summable fun n : ℕ => w ^ n / n ! * (Gamma (c + n))⁻¹`. -/
theorem summable_regularized0F1_term (c w : ℂ) :
    Summable fun n : ℕ => w ^ n / n ! * (Gamma (c + n))⁻¹ := by
  have h := (hasFPowerSeriesOnBall_regularized0F1 c).hasSum_mul_pow
    (by simp : w ∈ Metric.eball (0 : ℂ) ⊤)
  refine h.summable.congr fun n => ?_
  rw [regularizedHGFunCoeff_empty]; field_simp

/-- Local domination of the `₀F₁` terms, uniformly for `c` near `c₀` and `|w| < R`. -/
theorem exists_regularized0F1_dominated (c₀ : ℂ) (R : ℝ) :
    ∃ V : Set ℂ, IsOpen V ∧ c₀ ∈ V ∧ ∃ N : ℕ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n, N ≤ n → ∀ c ∈ V, ∀ w : ℂ, ‖w‖ ≤ R → ‖w ^ n / n ! * (Gamma (c + n))⁻¹‖ ≤ u n := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 3 - c₀.re ≤ N := exists_nat_ge _
  have hre0 : 2 ≤ (c₀ + N).re := by simp only [add_re, natCast_re]; linarith
  obtain ⟨V, hVopen, hc₀V, hV⟩ := DLMF.Hypergeometric.exists_open_norm_Gamma_add_nat_gt hre0
  have hm : 0 < ‖Gamma (c₀ + N)‖ / 2 := by
    have hpole : ∀ k : ℕ, c₀ + N ≠ -k := fun k h => by
      have := congrArg re h
      simp only [neg_re, natCast_re, add_re] at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have := norm_pos_iff.mpr (Gamma_ne_zero hpole)
    positivity
  refine ⟨V ∩ {c | c₀.re - 1 < c.re}, hVopen.inter (isOpen_lt continuous_const continuous_re),
    ⟨hc₀V, by simp⟩, N, fun n => (‖Gamma (c₀ + N)‖ / 2)⁻¹ * (|R| ^ n / n !), ?_, ?_⟩
  · exact (Real.summable_pow_div_factorial |R|).mul_left _
  · rintro n hn c ⟨hcV, hcre⟩ w hw
    have hre : 1 ≤ (c + N).re := by
      simp only [add_re, natCast_re] at hre0 ⊢
      change c₀.re - 1 < c.re at hcre
      linarith
    have hG := DLMF.Hypergeometric.norm_recip_Gamma_add_nat_le hre hm (hV c hcV).le hn
    have hf : (1 : ℝ) ≤ ((n - N) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hG' : ‖(Gamma (c + n))⁻¹‖ ≤ (‖Gamma (c₀ + N)‖ / 2)⁻¹ := by
      refine hG.trans ?_
      have hm' : 0 < (‖Gamma (c₀ + N)‖ / 2)⁻¹ := inv_pos.mpr hm
      calc (((n - N) ! : ℝ))⁻¹ * (‖Gamma (c₀ + N)‖ / 2)⁻¹ ≤ 1 * (‖Gamma (c₀ + N)‖ / 2)⁻¹ := by
            gcongr; exact inv_le_one_of_one_le₀ hf
        _ = _ := one_mul _
    rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    have hwR : ‖w‖ ^ n ≤ |R| ^ n := pow_le_pow_left₀ (norm_nonneg w) (hw.trans (le_abs_self R)) n
    calc ‖w‖ ^ n / n ! * ‖(Gamma (c + n))⁻¹‖ ≤ |R| ^ n / n ! * (‖Gamma (c₀ + N)‖ / 2)⁻¹ := by
          gcongr
      _ = _ := by ring

/-- `₀F₁` is jointly continuous in the parameter and the argument. -/
theorem continuous_regularized0F1 :
    Continuous fun p : ℂ × ℂ => regularizedHGFun (∅ : Multiset ℂ) {p.1} p.2 := by
  simp_rw [regularized0F1_eq_tsum]
  refine DLMF.Confluent.continuous_tsum_of_eventually_dominated (fun n => ?_)
    (fun p => summable_regularized0F1_term _ _) fun p₀ => ?_
  · exact ((by fun_prop : Continuous fun p : ℂ × ℂ => p.2 ^ n / n !)).mul
      (differentiable_one_div_Gamma.continuous.comp (by fun_prop))
  obtain ⟨V, hV, hc₀, N, u, hu, hle⟩ := exists_regularized0F1_dominated p₀.1 (‖p₀.2‖ + 1)
  refine ⟨V ×ˢ {w | ‖w‖ < ‖p₀.2‖ + 1}, hV.prod (isOpen_lt continuous_norm continuous_const),
    ⟨hc₀, by simp⟩, N, u, hu, fun n hn p hp => hle n hn p.1 hp.1 p.2 (le_of_lt hp.2)⟩

/-- `₀F₁` is entire in the parameter. -/
theorem differentiable_regularized0F1_param (w : ℂ) :
    Differentiable ℂ fun c : ℂ => regularizedHGFun (∅ : Multiset ℂ) {c} w := by
  simp_rw [regularized0F1_eq_tsum]
  have h := DLMF.Hypergeometric.analyticOnNhd_tsum_of_eventually_dominated
    (F := fun n c => w ^ n / n ! * (Gamma (c + n))⁻¹)
    (fun n => (differentiable_const _).mul (differentiable_one_div_Gamma.comp (by fun_prop)))
    (fun c => summable_regularized0F1_term c w) fun c₀ => by
      obtain ⟨V, hV, hc₀, N, u, hu, hle⟩ := exists_regularized0F1_dominated c₀ ‖w‖
      exact ⟨V, hV, hc₀, N, u, hu, fun n hn c hc => hle n hn c hc w le_rfl⟩
  exact fun c => (h c (mem_univ c)).differentiableAt

/-! ### `J_ν` in the order -/

/-- `J_ν(z)` is jointly continuous in `(ν, z)` on `ℂ × slitPlane`. -/
theorem continuousOn_besselJ :
    ContinuousOn (fun p : ℂ × ℂ => besselJ p.1 p.2) (univ ×ˢ slitPlane) := by
  rintro ⟨ν, z⟩ ⟨-, hz⟩
  refine ContinuousAt.continuousWithinAt ?_
  simp only [besselJ_eq_regularized]
  refine ContinuousAt.mul ?_ ?_
  · exact ContinuousAt.cpow (by fun_prop) (by fun_prop) (div_two_mem_slitPlane hz)
  · exact (continuous_regularized0F1.comp (by fun_prop :
      Continuous fun p : ℂ × ℂ => (p.1 + 1, -(p.2 ^ 2 / 4)))).continuousAt

/-- `J_ν(z)` is entire in `ν` for `z ≠ 0`. -/
theorem differentiable_besselJ_order {z : ℂ} (hz : z ≠ 0) :
    Differentiable ℂ fun ν : ℂ => besselJ ν z := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  simp only [besselJ_eq_regularized]
  exact ((differentiable_id.const_cpow (Or.inl hz2))).mul
    ((differentiable_regularized0F1_param _).comp (differentiable_id.add_const 1))

/-! ### Weber's function at integer orders -/

/-- The numerator `D_ν(z) = J_ν(z) cos νπ - J_{-ν}(z)` of `Y_ν`. -/
def besselD (ν z : ℂ) : ℂ := besselJ ν z * cos (ν * π) - besselJ (-ν) z

/-- Identity under the stated parameter and domain assumptions: `cos ((n : ℂ) * π) = (-1) ^ n`. -/
theorem cos_int_mul_pi_complex (n : ℤ) : cos ((n : ℂ) * π) = (-1) ^ n := by
  rw [show ((n : ℂ) * π) = ((n * π : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
    Real.cos_int_mul_pi]; push_cast; rfl

/-- Identity under the stated parameter and domain assumptions: `besselD n z = 0`. -/
theorem besselD_int (n : ℤ) (z : ℂ) : besselD n z = 0 := by
  rw [besselD, besselJ_neg_int, cos_int_mul_pi_complex]; ring

/-- Nonvanishing under the stated hypotheses: `sin (ν * π) ≠ 0`. -/
theorem sin_mul_pi_ne_zero {ν : ℂ} (hν : ∀ k : ℤ, ν ≠ k) : sin (ν * π) ≠ 0 := by
  rw [Complex.sin_ne_zero_iff]
  intro k hk
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact hν k (mul_right_cancel₀ hπ hk)

/-- Identity under the stated parameter and domain assumptions: `besselY ν z = besselD ν z / sin
(ν * π)`. -/
theorem besselY_eq_of_not_int {ν : ℂ} (hν : ∀ k : ℤ, ν ≠ k) (z : ℂ) :
    besselY ν z = besselD ν z / sin (ν * π) := by
  have : ¬ ∃ k : ℤ, ν = k := fun ⟨k, hk⟩ => hν k hk
  simp [besselY, this, besselD]

/-- Differentiability of the indicated parameterized function: `Differentiable ℂ fun ν : ℂ =>
besselD ν z`. -/
theorem differentiable_besselD {z : ℂ} (hz : z ≠ 0) :
    Differentiable ℂ fun ν : ℂ => besselD ν z := by
  unfold besselD
  exact ((differentiable_besselJ_order hz).mul (by fun_prop)).sub
    ((differentiable_besselJ_order hz).comp differentiable_neg)

/-- The function `(fun p : ℂ × ℂ => besselD p.2 p.1)` is continuous on `(slitPlane ×ˢ univ)`. -/
theorem continuousOn_besselD :
    ContinuousOn (fun p : ℂ × ℂ => besselD p.2 p.1) (slitPlane ×ˢ univ) := by
  rintro ⟨z, ν⟩ ⟨hz, -⟩
  have hJ : ∀ f : ℂ × ℂ → ℂ, Continuous f →
      ContinuousAt (fun p : ℂ × ℂ => besselJ (f p) p.1) (z, ν) := fun f hf =>
    ContinuousAt.comp (g := fun q : ℂ × ℂ => besselJ q.1 q.2) (f := fun p : ℂ × ℂ => (f p, p.1))
      (continuousOn_besselJ.continuousAt (prod_mem_nhds univ_mem (isOpen_slitPlane.mem_nhds hz)))
      (by fun_prop)
  refine ContinuousAt.continuousWithinAt ?_
  unfold besselD
  exact ((hJ _ continuous_snd).mul (by fun_prop)).sub (hJ _ continuous_snd.neg)

/-- Nonvanishing under the stated hypotheses: `∀ k : ℤ, μ ≠ k`. -/
theorem not_int_of_mem_ball {n : ℤ} {μ : ℂ} (hμ : μ ∈ Metric.ball (n : ℂ) (1 / 2)) (hne : μ ≠ n) :
    ∀ k : ℤ, μ ≠ k := by
  intro k hk
  subst hk
  rw [Metric.mem_ball, dist_eq_norm, ← Int.cast_sub, norm_intCast] at hμ
  have h : k - n = 0 := by
    by_contra h0
    have : (1 : ℝ) ≤ |((k - n : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h0
    push_cast at this hμ; linarith
  exact hne (by rw [show k = n by omega])

/-- Identity under the stated parameter and domain assumptions: `dslope (fun ν : ℂ => sin (ν * π))
n μ ≠ 0`. -/
theorem dslope_sin_ne_zero (n : ℤ) {μ : ℂ} (hμ : μ ∈ Metric.ball (n : ℂ) (1 / 2)) :
    dslope (fun ν : ℂ => sin (ν * π)) n μ ≠ 0 := by
  by_cases hne : μ = n
  · subst hne
    rw [dslope_same]
    have hd : HasDerivAt (fun ν : ℂ => sin (ν * π)) (cos ((n : ℂ) * π) * π) n := by
      simpa using ((hasDerivAt_id (n : ℂ)).mul_const (π : ℂ)).csin
    rw [hd.deriv, cos_int_mul_pi_complex]
    exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) (by exact_mod_cast Real.pi_ne_zero)
  · rw [dslope_of_ne _ hne, slope_def_field, Complex.sin_int_mul_pi, sub_zero]
    exact div_ne_zero (sin_mul_pi_ne_zero (not_int_of_mem_ball hμ hne)) (sub_ne_zero.mpr hne)

/-- Near an integer `n`, `Y_μ(z)` is the quotient of the difference quotients of `D_μ(z)` and
`sin μπ` at `n`. -/
theorem besselY_eq_dslope (n : ℤ) {μ z : ℂ} (hμ : μ ∈ Metric.ball (n : ℂ) (1 / 2))
    (hz : z ∈ slitPlane) :
    besselY μ z = dslope (fun ν => besselD ν z) n μ / dslope (fun ν : ℂ => sin (ν * π)) n μ := by
  have hz0 := slitPlane_ne_zero hz
  by_cases hne : μ = n
  · subst hne
    have hD := differentiable_besselD hz0
    have hcont : ContinuousAt (fun μ => dslope (fun ν => besselD ν z) n μ /
        dslope (fun ν : ℂ => sin (ν * π)) n μ) n :=
      (continuousAt_dslope_same.mpr (hD n)).div
        (continuousAt_dslope_same.mpr (by fun_prop)) (dslope_sin_ne_zero n (Metric.mem_ball_self
          (by norm_num)))
    have ht : Tendsto (fun μ => besselD μ z / sin (μ * π)) (𝓝[≠] (n : ℂ))
        (𝓝 (dslope (fun ν => besselD ν z) n n / dslope (fun ν : ℂ => sin (ν * π)) n n)) := by
      refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with μ hμ
      rw [dslope_of_ne _ hμ, dslope_of_ne _ hμ, slope_def_field, slope_def_field,
        besselD_int, Complex.sin_int_mul_pi, sub_zero, sub_zero]
      have hμn : μ - n ≠ 0 := sub_ne_zero.mpr hμ
      field_simp
    have hex : ∃ k : ℤ, (n : ℂ) = k := ⟨n, rfl⟩
    simp only [besselY, hex, ite_true]
    exact ht.limUnder_eq
  · rw [besselY_eq_of_not_int (not_int_of_mem_ball hμ hne), dslope_of_ne _ hne,
      dslope_of_ne _ hne, slope_def_field, slope_def_field, besselD_int, Complex.sin_int_mul_pi,
      sub_zero, sub_zero]
    have hμn : μ - n ≠ 0 := sub_ne_zero.mpr hne
    field_simp

/-- **`Y_ν(z)` is jointly continuous** in `(ν, z)` on `ℂ × slitPlane`, including integer orders. -/
theorem continuousAt_besselY (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    ContinuousAt (fun p : ℂ × ℂ => besselY p.1 p.2) (ν, z) := by
  have hD := continuousOn_besselD
  by_cases hν : ∃ k : ℤ, ν = k
  · obtain ⟨n, rfl⟩ := hν
    have hds := DLMF.Confluent.continuousOn_dslope_param (X := ℂ) (f := fun w ν => besselD ν w)
      isOpen_slitPlane hD (fun w hw => differentiable_besselD (slitPlane_ne_zero hw)) n
    have h1 : ContinuousAt (fun p : ℂ × ℂ => dslope (fun ν => besselD ν p.2) n p.1) (n, z) :=
      ContinuousAt.comp (g := fun q : ℂ × ℂ => dslope (fun ν => besselD ν q.1) n q.2)
        (f := Prod.swap) (hds.continuousAt (prod_mem_nhds (isOpen_slitPlane.mem_nhds hz)
          univ_mem)) continuous_swap.continuousAt
    have h2 : ContinuousAt (fun p : ℂ × ℂ => dslope (fun ν : ℂ => sin (ν * π)) n p.1) (n, z) :=
      ContinuousAt.comp (g := dslope (fun ν : ℂ => sin (ν * π)) n) (f := Prod.fst)
        (continuousAt_dslope_same.mpr (by fun_prop)) continuous_fst.continuousAt
    refine (h1.div h2 (dslope_sin_ne_zero n (Metric.mem_ball_self (by norm_num)))).congr ?_
    filter_upwards [prod_mem_nhds (Metric.ball_mem_nhds (n : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
      (isOpen_slitPlane.mem_nhds hz)] with p hp
    exact (besselY_eq_dslope n hp.1 hp.2).symm
  · push Not at hν
    have hopen : IsOpen {μ : ℂ | sin (μ * π) ≠ 0} :=
      isOpen_ne_fun (by fun_prop) continuous_const
    have hc : ContinuousAt (fun p : ℂ × ℂ => besselD p.1 p.2 / sin (p.1 * π)) (ν, z) := by
      have h1 : ContinuousAt (fun p : ℂ × ℂ => besselD p.1 p.2) (ν, z) :=
        ContinuousAt.comp (g := fun q : ℂ × ℂ => besselD q.2 q.1) (f := Prod.swap)
          (hD.continuousAt (prod_mem_nhds (isOpen_slitPlane.mem_nhds hz) univ_mem))
          continuous_swap.continuousAt
      exact h1.div (by fun_prop) (sin_mul_pi_ne_zero hν)
    refine hc.congr ?_
    filter_upwards [prod_mem_nhds (hopen.mem_nhds (sin_mul_pi_ne_zero hν)) univ_mem] with p hp
    have hp' : ∀ k : ℤ, p.1 ≠ k := fun k hk => hp.1 (by rw [hk]; exact Complex.sin_int_mul_pi k)
    exact (besselY_eq_of_not_int hp' p.2).symm

/-! ### Recurrences, derivative and the Bessel equation for `Y_ν` -/

/-- `J_ν'(z) = -(ν/z) J_ν(z) + J_{ν-1}(z)` (DLMF 10.6.2). -/
theorem hasDerivAt_besselJ' {ν z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (besselJ ν) (-(ν / z) * besselJ ν z + besselJ (ν - 1) z) z := by
  have h := hasDerivAt_besselJ (ν := ν) hz
  convert h using 1
  have hr := besselJ_add_sub (ν := ν) (slitPlane_ne_zero hz)
  have hz0 := slitPlane_ne_zero hz
  field_simp at hr ⊢
  linear_combination -hr

/-- Identity under the stated parameter and domain assumptions: `cos ((ν + 1) * π) = -cos (ν *
π)`. -/
theorem cos_add_one_mul_pi (ν : ℂ) : cos ((ν + 1) * π) = -cos (ν * π) := by
  rw [add_mul, one_mul, cos_add_pi]
/-- Identity under the stated parameter and domain assumptions: `sin ((ν + 1) * π) = -sin (ν *
π)`. -/
theorem sin_add_one_mul_pi (ν : ℂ) : sin ((ν + 1) * π) = -sin (ν * π) := by
  rw [add_mul, one_mul, sin_add_pi]
/-- Identity under the stated parameter and domain assumptions: `cos ((ν - 1) * π) = -cos (ν *
π)`. -/
theorem cos_sub_one_mul_pi (ν : ℂ) : cos ((ν - 1) * π) = -cos (ν * π) := by
  rw [sub_mul, one_mul, cos_sub_pi]
/-- Identity under the stated parameter and domain assumptions: `sin ((ν - 1) * π) = -sin (ν *
π)`. -/
theorem sin_sub_one_mul_pi (ν : ℂ) : sin ((ν - 1) * π) = -sin (ν * π) := by
  rw [sub_mul, one_mul, sin_sub_pi]

/-- Nonvanishing under the stated hypotheses: `∀ k : ℤ, ν + 1 ≠ k`. -/
theorem not_int_add_one {ν : ℂ} (hν : ∀ k : ℤ, ν ≠ k) : ∀ k : ℤ, ν + 1 ≠ k := fun k h =>
  hν (k - 1) (by push_cast; linear_combination h)
/-- Nonvanishing under the stated hypotheses: `∀ k : ℤ, ν - 1 ≠ k`. -/
theorem not_int_sub_one {ν : ℂ} (hν : ∀ k : ℤ, ν ≠ k) : ∀ k : ℤ, ν - 1 ≠ k := fun k h =>
  hν (k + 1) (by push_cast; linear_combination h)

/-- The function `(fun μ => besselY (f μ) z)` is continuous at `ν`. -/
theorem continuousAt_besselY_order (f : ℂ → ℂ) (hf : Continuous f) (ν : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) : ContinuousAt (fun μ => besselY (f μ) z) ν :=
  ContinuousAt.comp (g := fun p : ℂ × ℂ => besselY p.1 p.2) (f := fun μ => (f μ, z))
    (continuousAt_besselY (f ν) hz) (by fun_prop)

/-- **The three-term recurrence for `Y_ν`** (DLMF 10.6.1), for every order. -/
theorem besselY_add_sub (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (2 * ν / z) * besselY ν z = besselY (ν - 1) z + besselY (ν + 1) z := by
  have hz0 := slitPlane_ne_zero hz
  refine DLMF.Confluent.eq_of_continuousAt_of_integerComplement
    (f := fun ν => (2 * ν / z) * besselY ν z)
    (g := fun ν => besselY (ν - 1) z + besselY (ν + 1) z)
    ((by fun_prop : Continuous fun ν : ℂ => 2 * ν / z).continuousAt.mul
      (continuousAt_besselY_order id continuous_id ν hz))
    ((continuousAt_besselY_order (· - 1) (by fun_prop) ν hz).add
      (continuousAt_besselY_order (· + 1) (by fun_prop) ν hz)) fun c hc => ?_
  have hcz := DLMF.Confluent.forall_of_mem_integerComplement hc
  have hs := sin_mul_pi_ne_zero hcz
  rw [besselY_eq_of_not_int hcz, besselY_eq_of_not_int (not_int_sub_one hcz),
    besselY_eq_of_not_int (not_int_add_one hcz), sin_sub_one_mul_pi, sin_add_one_mul_pi]
  simp only [besselD, cos_sub_one_mul_pi, cos_add_one_mul_pi]
  have h1 := besselJ_add_sub (ν := c) hz0
  have h2 := besselJ_add_sub (ν := -c) hz0
  rw [show -c - 1 = -(c + 1) by ring, show -c + 1 = -(c - 1) by ring] at h2
  rw [div_neg, div_neg]
  linear_combination (cos (c * π) / sin (c * π)) * h1 + (1 / sin (c * π)) * h2

/-- At `z`, the function `(besselY ν)` has derivative `((ν / z) * besselY ν z - besselY (ν + 1)
z)`. -/
theorem hasDerivAt_besselY_of_not_int {ν : ℂ} (hν : ∀ k : ℤ, ν ≠ k) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (besselY ν) ((ν / z) * besselY ν z - besselY (ν + 1) z) z := by
  have hs := sin_mul_pi_ne_zero hν
  have hY : besselY ν = fun w => besselD ν w / sin (ν * π) :=
    funext fun w => besselY_eq_of_not_int hν w
  have hJ1 := hasDerivAt_besselJ (ν := ν) hz
  have hJ2 := hasDerivAt_besselJ' (ν := -ν) hz
  have hD : HasDerivAt (fun w => besselD ν w)
      (((ν / z) * besselJ ν z - besselJ (ν + 1) z) * cos (ν * π) -
        (-(-ν / z) * besselJ (-ν) z + besselJ (-ν - 1) z)) z := by
    unfold besselD
    exact (hJ1.mul_const _).sub hJ2
  have h := hD.div_const (sin (ν * π))
  rw [← hY] at h
  convert h using 1
  rw [besselY_eq_of_not_int hν, besselY_eq_of_not_int (not_int_add_one hν), sin_add_one_mul_pi]
  simp only [besselD, cos_add_one_mul_pi, show -(ν + 1) = -ν - 1 by ring]
  field_simp
  ring

/-- **The derivative of `Y_ν`** (DLMF 10.6.2), for every order: `Y_ν' = (ν/z) Y_ν - Y_{ν+1}`. -/
theorem hasDerivAt_besselY (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (besselY ν) ((ν / z) * besselY ν z - besselY (ν + 1) z) z := by
  have := DLMF.Confluent.integerComplement_nhdsWithin_neBot ν
  refine hasDerivAt_of_tendstoUniformlyOnFilter (l := 𝓝[integerComplement] ν)
    (f := fun c => besselY c) (f' := fun c w => (c / w) * besselY c w - besselY (c + 1) w)
    (g' := fun w => (ν / w) * besselY ν w - besselY (ν + 1) w) ?_ ?_ ?_
  · have hc : ContinuousAt (fun p : ℂ × ℂ => (p.1 / p.2) * besselY p.1 p.2 -
        besselY (p.1 + 1) p.2) (ν, z) := by
      have h1 := continuousAt_besselY ν hz
      have h2 : ContinuousAt (fun p : ℂ × ℂ => besselY (p.1 + 1) p.2) (ν, z) :=
        ContinuousAt.comp (g := fun p : ℂ × ℂ => besselY p.1 p.2)
          (f := fun p : ℂ × ℂ => (p.1 + 1, p.2)) (continuousAt_besselY (ν + 1) hz) (by fun_prop)
      exact ((continuousAt_fst.div continuousAt_snd (slitPlane_ne_zero hz)).mul h1).sub h2
    exact DLMF.Confluent.tendstoUniformlyOnFilter_of_continuousAt
      (F := fun c w => (c / w) * besselY c w - besselY (c + 1) w) hc nhdsWithin_le_nhds
  · have hm : integerComplement ×ˢ slitPlane ∈
        𝓝[integerComplement] ν ×ˢ 𝓝 z :=
      prod_mem_prod self_mem_nhdsWithin (isOpen_slitPlane.mem_nhds hz)
    filter_upwards [hm] with p hp
    exact hasDerivAt_besselY_of_not_int (DLMF.Confluent.forall_of_mem_integerComplement hp.1) hp.2
  · filter_upwards [isOpen_slitPlane.mem_nhds hz] with y hy
    exact ((continuousAt_besselY_order id continuous_id ν hy).tendsto).mono_left
      nhdsWithin_le_nhds

/-- **Bessel's equation for `Y_ν`** (DLMF 10.2.1), for every order including the integers. -/
@[dlmf 10.2.E1]
theorem besselY_ode_all (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    z ^ 2 * iteratedDeriv 2 (besselY ν) z + z * deriv (besselY ν) z +
      (z ^ 2 - ν ^ 2) * besselY ν z = 0 := by
  have hz0 := slitPlane_ne_zero hz
  have hderiv : deriv (besselY ν) =ᶠ[𝓝 z] fun w => (ν / w) * besselY ν w - besselY (ν + 1) w := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    exact (hasDerivAt_besselY ν hw).deriv
  have h2 : HasDerivAt (fun w => (ν / w) * besselY ν w - besselY (ν + 1) w)
      ((-(ν / z ^ 2)) * besselY ν z + (ν / z) * ((ν / z) * besselY ν z - besselY (ν + 1) z) -
        (((ν + 1) / z) * besselY (ν + 1) z - besselY (ν + 1 + 1) z)) z := by
    have hinv : HasDerivAt (fun w : ℂ => ν / w) (-(ν / z ^ 2)) z := by
      have := (hasDerivAt_inv hz0).const_mul ν
      convert this using 1 <;> [funext w; skip] <;> field_simp
    exact (hinv.mul (hasDerivAt_besselY ν hz)).sub (hasDerivAt_besselY (ν + 1) hz)
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv.deriv_eq, h2.deriv,
    (hasDerivAt_besselY ν hz).deriv]
  have hr := besselY_add_sub (ν + 1) hz
  rw [show ν + 1 - 1 = ν by ring] at hr
  have hY2 : besselY (ν + 1 + 1) z = (2 * (ν + 1) / z) * besselY (ν + 1) z - besselY ν z := by
    linear_combination -hr
  rw [hY2]
  field_simp
  ring

/-! ### Wronskians and Hankel functions -/

/-- The entire function behind the Wronskian of `J_ν` and `J_{-ν}`. -/
def besselWronskianSeries (ν w : ℂ) : ℂ :=
  regularizedHGFun (∅ : Multiset ℂ) {ν + 1} w * regularizedHGFun ∅ {-ν} w -
    w * (regularizedHGFun ∅ {ν + 2} w * regularizedHGFun ∅ {1 - ν} w)

/-- Identity under the stated parameter and domain assumptions: `besselWronskianSeries ν w = -(sin
(π * ν) / π)`. -/
theorem besselWronskianSeries_eq (ν w : ℂ) :
    besselWronskianSeries ν w = -(sin (π * ν) / π) := by
  have hd : ∀ c w : ℂ, HasDerivAt (regularizedHGFun (∅ : Multiset ℂ) {c})
      (regularizedHGFun ∅ {c + 1} w) w := fun c w => hasDerivAt_regularized0F1 c w
  have hΦ : ∀ w, HasDerivAt (besselWronskianSeries ν) 0 w := by
    intro w
    have h := (((hd (ν + 1) w).mul (hd (-ν) w)).sub ((hasDerivAt_id w).mul
      ((hd (ν + 2) w).mul (hd (1 - ν) w))))
    convert h using 1
    · funext v; simp [besselWronskianSeries]
    have c1 := regularized0F1_contiguous (ν + 1) w
    have c2 := regularized0F1_contiguous (-ν) w
    rw [show ν + 1 + 1 = ν + 2 by ring, show ν + 2 + 1 = ν + 3 by ring] at c1 ⊢
    rw [show -ν + 1 = 1 - ν by ring, show 1 - ν + 1 = 2 - ν by ring] at c2 ⊢
    simp only [id, one_mul, Pi.mul_apply]
    linear_combination (-(regularizedHGFun (∅ : Multiset ℂ) {1 - ν} w)) * c1 -
      (regularizedHGFun (∅ : Multiset ℂ) {ν + 2} w) * c2
  have hconst := is_const_of_deriv_eq_zero (f := besselWronskianSeries ν)
    (fun w => (hΦ w).differentiableAt) (fun w => (hΦ w).deriv) w 0
  rw [hconst, besselWronskianSeries]
  simp only [zero_mul, sub_zero, DLMF.Confluent.regularizedHGFun_zero, regularizedHGFunCoeff_empty,
    Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, add_zero, one_div]
  have h := DLMF.Confluent.recip_Gamma_mul_Gamma_one_sub (-ν)
  rw [show 1 - -ν = ν + 1 by ring, mul_inv, mul_neg, sin_neg] at h
  linear_combination h

/-- **The Wronskian of `J_ν` and `J_{-ν}`** (DLMF 10.5.1):
`J_ν J_{-ν}' - J_ν' J_{-ν} = -2 sin(νπ)/(πz)`. -/
@[dlmf 10.5.E1]
theorem wronskian_besselJ_neg (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    besselJ ν z * deriv (besselJ (-ν)) z - deriv (besselJ ν) z * besselJ (-ν) z =
      -2 * sin (ν * π) / (π * z) := by
  have hz0 := slitPlane_ne_zero hz
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz0 two_ne_zero
  rw [(hasDerivAt_besselJ' (ν := -ν) hz).deriv, (hasDerivAt_besselJ (ν := ν) hz).deriv]
  have hW : besselJ ν z * (-(-ν / z) * besselJ (-ν) z + besselJ (-ν - 1) z) -
      (ν / z * besselJ ν z - besselJ (ν + 1) z) * besselJ (-ν) z =
      besselJ ν z * besselJ (-ν - 1) z + besselJ (ν + 1) z * besselJ (-ν) z := by ring
  rw [hW]
  have hS := besselWronskianSeries_eq ν (-(z ^ 2 / 4))
  unfold besselWronskianSeries at hS
  simp only [besselJ_eq_regularized]
  rw [show -ν - 1 + 1 = -ν by ring, show -ν + 1 = 1 - ν by ring, show ν + 1 + 1 = ν + 2 by ring]
  have hp1 : (z / 2) ^ ν * (z / 2) ^ (-ν - 1) = 2 / z := by
    rw [← cpow_add _ _ hz2, show ν + (-ν - 1) = -1 by ring, cpow_neg_one, inv_div]
  have hp2 : (z / 2) ^ (ν + 1) * (z / 2) ^ (-ν) = z / 2 := by
    rw [← cpow_add _ _ hz2, show ν + 1 + -ν = 1 by ring, cpow_one]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz' : (2 / z) * (z ^ 2 / 4) = z / 2 := by field_simp; ring
  rw [show sin (ν * π) = sin (π * ν) by ring_nf]
  linear_combination (2 / z) * hS + (regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(z ^ 2 / 4)) *
    regularizedHGFun ∅ {-ν} (-(z ^ 2 / 4))) * hp1 + (regularizedHGFun (∅ : Multiset ℂ) {ν + 2}
      (-(z ^ 2 / 4)) * regularizedHGFun ∅ {1 - ν} (-(z ^ 2 / 4))) * hp2 -
    (regularizedHGFun (∅ : Multiset ℂ) {ν + 2} (-(z ^ 2 / 4)) *
      regularizedHGFun ∅ {1 - ν} (-(z ^ 2 / 4))) * hz'

/-- The function `(fun μ => besselJ (f μ) z)` is continuous at `ν`. -/
theorem continuousAt_besselJ_order (f : ℂ → ℂ) (hf : Continuous f) (ν : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) : ContinuousAt (fun μ => besselJ (f μ) z) ν :=
  ContinuousAt.comp (g := fun p : ℂ × ℂ => besselJ p.1 p.2) (f := fun μ => (f μ, z))
    (continuousOn_besselJ.continuousAt (prod_mem_nhds univ_mem (isOpen_slitPlane.mem_nhds hz)))
    (by fun_prop)

/-- The cross product `J_{ν+1} Y_ν - J_ν Y_{ν+1} = 2/(πz)`, for every order. -/
theorem besselJ_succ_mul_besselY_sub (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    besselJ (ν + 1) z * besselY ν z - besselJ ν z * besselY (ν + 1) z = 2 / (π * z) := by
  have hz0 := slitPlane_ne_zero hz
  refine DLMF.Confluent.eq_of_continuousAt_of_integerComplement
    (f := fun ν => besselJ (ν + 1) z * besselY ν z - besselJ ν z * besselY (ν + 1) z)
    (g := fun _ => 2 / (π * z))
    (((continuousAt_besselJ_order (· + 1) (by fun_prop) ν hz).mul
      (continuousAt_besselY_order id continuous_id ν hz)).sub
      ((continuousAt_besselJ_order id continuous_id ν hz).mul
      (continuousAt_besselY_order (· + 1) (by fun_prop) ν hz))) continuousAt_const fun c hc => ?_
  have hcz := DLMF.Confluent.forall_of_mem_integerComplement hc
  have hs := sin_mul_pi_ne_zero hcz
  have hW := wronskian_besselJ_neg c hz
  rw [(hasDerivAt_besselJ' (ν := -c) hz).deriv, (hasDerivAt_besselJ (ν := c) hz).deriv] at hW
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [besselY_eq_of_not_int hcz, besselY_eq_of_not_int (not_int_add_one hcz), sin_add_one_mul_pi]
  simp only [besselD, cos_add_one_mul_pi, show -(c + 1) = -c - 1 by ring]
  field_simp at hW ⊢
  linear_combination (-1 : ℂ) * hW

/-- **The Wronskian of `J_ν` and `Y_ν`** (DLMF 10.5.2): `W{J_ν, Y_ν} = 2/(πz)`, for every order. -/
@[dlmf 10.5.E2]
theorem wronskian_besselJ_besselY (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    besselJ ν z * deriv (besselY ν) z - deriv (besselJ ν) z * besselY ν z = 2 / (π * z) := by
  rw [(hasDerivAt_besselY ν hz).deriv, (hasDerivAt_besselJ (ν := ν) hz).deriv,
    ← besselJ_succ_mul_besselY_sub ν hz]
  ring

/-- Hankel's function of the first kind, `H_ν^{(1)} = J_ν + i Y_ν` (DLMF 10.4.3). -/
@[dlmf 10.4.E3]
def hankelH1 (ν z : ℂ) : ℂ := besselJ ν z + I * besselY ν z

/-- Hankel's function of the second kind, `H_ν^{(2)} = J_ν - i Y_ν` (DLMF 10.4.3). -/
@[dlmf 10.4.E3]
def hankelH2 (ν z : ℂ) : ℂ := besselJ ν z - I * besselY ν z

/-- At `z`, the function `(hankelH1 ν)` has derivative `((ν / z) * hankelH1 ν z - hankelH1 (ν + 1)
z)`. -/
theorem hasDerivAt_hankelH1 (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (hankelH1 ν) ((ν / z) * hankelH1 ν z - hankelH1 (ν + 1) z) z := by
  have h := (hasDerivAt_besselJ (ν := ν) hz).add ((hasDerivAt_besselY ν hz).const_mul I)
  convert h using 1
  · funext w; simp [hankelH1]
  · simp only [hankelH1]; ring

/-- At `z`, the function `(hankelH2 ν)` has derivative `((ν / z) * hankelH2 ν z - hankelH2 (ν + 1)
z)`. -/
theorem hasDerivAt_hankelH2 (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (hankelH2 ν) ((ν / z) * hankelH2 ν z - hankelH2 (ν + 1) z) z := by
  have h := (hasDerivAt_besselJ (ν := ν) hz).sub ((hasDerivAt_besselY ν hz).const_mul I)
  convert h using 1
  · funext w; simp [hankelH2]
  · simp only [hankelH2]; ring

/-- **The Wronskian of the Hankel functions** (DLMF 10.5.5): `W{H^{(1)}, H^{(2)}} = -4i/(πz)`. -/
@[dlmf 10.5.E5]
theorem wronskian_hankelH1_hankelH2 (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    hankelH1 ν z * deriv (hankelH2 ν) z - deriv (hankelH1 ν) z * hankelH2 ν z =
      -4 * I / (π * z) := by
  have hW := wronskian_besselJ_besselY ν hz
  rw [(hasDerivAt_besselY ν hz).deriv, (hasDerivAt_besselJ (ν := ν) hz).deriv] at hW
  rw [(hasDerivAt_hankelH1 ν hz).deriv, (hasDerivAt_hankelH2 ν hz).deriv]
  simp only [hankelH1, hankelH2]
  linear_combination (-2 * I) * hW

/-! ### The modified functions `I_ν` and `K_ν` -/

/-- `I_ν' = (ν/z) I_ν + I_{ν+1}` (DLMF 10.29.2). -/
theorem hasDerivAt_besselI {ν z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (besselI ν) (ν / z * besselI ν z + besselI (ν + 1) z) z := by
  have hu : HasDerivAt (fun w : ℂ => w ^ 2 / 4) (z / 2) z := by
    convert! ((hasDerivAt_id z).pow 2).div_const 4 using 1
    simp
    ring
  have hd := (hasDerivAt_besselPrefactor ν hz).mul
    ((hasDerivAt_regularized0F1 (ν + 1) (z ^ 2 / 4)).comp z hu)
  convert! hd using 1
  simp only [besselI, Function.comp_apply]
  rw [cpow_add _ _ (div_ne_zero (slitPlane_ne_zero hz) (by norm_num)), cpow_one]
  ring

/-- `I_{ν-1} - I_{ν+1} = (2ν/z) I_ν` (DLMF 10.29.1). -/
@[dlmf 10.29.E1]
theorem besselI_sub_add {ν z : ℂ} (hz : z ≠ 0) :
    (2 * ν / z) * besselI ν z = besselI (ν - 1) z - besselI (ν + 1) z := by
  have he := regularized0F1_contiguous ν (z ^ 2 / 4)
  unfold besselI
  rw [cpow_sub _ _ (div_ne_zero hz (by norm_num)),
    cpow_add _ _ (div_ne_zero hz (by norm_num)), cpow_one]
  rw [show ν - 1 + 1 = ν by ring]
  linear_combination (norm := (field_simp [hz]; ring)) (-2 * (z / 2) ^ ν / z) * he

/-- `I_ν' = I_{ν-1} - (ν/z) I_ν` (DLMF 10.29.2). -/
theorem hasDerivAt_besselI' {ν z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (besselI ν) (besselI (ν - 1) z - ν / z * besselI ν z) z := by
  have h := hasDerivAt_besselI (ν := ν) hz
  convert h using 1
  have hr := besselI_sub_add (ν := ν) (slitPlane_ne_zero hz)
  have hz0 := slitPlane_ne_zero hz
  field_simp at hr ⊢
  linear_combination -hr

/-- `I_{-n} = I_n` for integer `n` (DLMF 10.27.1). -/
@[dlmf 10.27.E1]
theorem besselI_neg_int (n : ℤ) (z : ℂ) : besselI (-n) z = besselI n z := by
  wlog hn : 0 ≤ n
  · have he := this (-n) z (by omega)
    simp only [Int.cast_neg, neg_neg] at he
    exact he.symm
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have hp : (z / 2) ^ (n : ℂ) = (z / 2) ^ (-(n : ℂ)) * ((z / 2) ^ 2) ^ n := by
    by_cases hz : z = 0
    · by_cases hn : n = 0 <;> simp [hz, hn]
    rw [← pow_mul, ← cpow_natCast, ← cpow_add _ _ (by simpa using hz)]
    congr 1
    push_cast
    ring
  simp only [besselI, Int.cast_natCast]
  have hshift := regularizedHGFun_zero_singleton_neg_nat_add_one n (z ^ 2 / 4)
  change regularizedHGFun ∅ {-(n : ℂ) + 1} (z ^ 2 / 4) =
    (z ^ 2 / 4) ^ n * regularizedHGFun ∅ {(n : ℂ) + 1} (z ^ 2 / 4) at hshift
  rw [hshift, hp]
  rw [show z ^ 2 / 4 = (z / 2) ^ 2 by ring]
  ring

/-- The function `(fun p : ℂ × ℂ => besselI p.1 p.2)` is continuous on `(univ ×ˢ slitPlane)`. -/
theorem continuousOn_besselI :
    ContinuousOn (fun p : ℂ × ℂ => besselI p.1 p.2) (univ ×ˢ slitPlane) := by
  rintro ⟨ν, z⟩ ⟨-, hz⟩
  refine ContinuousAt.continuousWithinAt ?_
  unfold besselI
  refine ContinuousAt.mul ?_ ?_
  · exact ContinuousAt.cpow (by fun_prop) (by fun_prop) (div_two_mem_slitPlane hz)
  · exact (continuous_regularized0F1.comp (by fun_prop :
      Continuous fun p : ℂ × ℂ => (p.1 + 1, p.2 ^ 2 / 4))).continuousAt

/-- Differentiability of the indicated parameterized function: `Differentiable ℂ fun ν : ℂ =>
besselI ν z`. -/
theorem differentiable_besselI_order {z : ℂ} (hz : z ≠ 0) :
    Differentiable ℂ fun ν : ℂ => besselI ν z := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  unfold besselI
  exact ((differentiable_id.const_cpow (Or.inl hz2))).mul
    ((differentiable_regularized0F1_param _).comp (differentiable_id.add_const 1))

/-- The numerator `E_ν(z) = I_{-ν}(z) - I_ν(z)` of `K_ν`. -/
def besselE (ν z : ℂ) : ℂ := besselI (-ν) z - besselI ν z

/-- Identity under the stated parameter and domain assumptions: `besselE n z = 0`. -/
theorem besselE_int (n : ℤ) (z : ℂ) : besselE n z = 0 := by
  rw [besselE, besselI_neg_int, sub_self]

/-- Identity under the stated parameter and domain assumptions: `besselK ν z = π / 2 * besselE ν z
/ sin (ν * π)`. -/
theorem besselK_eq_of_not_int {ν : ℂ} (hν : ∀ k : ℤ, ν ≠ k) (z : ℂ) :
    besselK ν z = π / 2 * besselE ν z / sin (ν * π) := by
  have : ¬ ∃ k : ℤ, ν = k := fun ⟨k, hk⟩ => hν k hk
  simp [besselK, this, besselE]

/-- Differentiability of the indicated parameterized function: `Differentiable ℂ fun ν : ℂ =>
besselE ν z`. -/
theorem differentiable_besselE {z : ℂ} (hz : z ≠ 0) :
    Differentiable ℂ fun ν : ℂ => besselE ν z := by
  unfold besselE
  exact ((differentiable_besselI_order hz).comp differentiable_neg).sub
    (differentiable_besselI_order hz)

/-- The function `(fun p : ℂ × ℂ => besselE p.2 p.1)` is continuous on `(slitPlane ×ˢ univ)`. -/
theorem continuousOn_besselE :
    ContinuousOn (fun p : ℂ × ℂ => besselE p.2 p.1) (slitPlane ×ˢ univ) := by
  rintro ⟨z, ν⟩ ⟨hz, -⟩
  have hI : ∀ f : ℂ × ℂ → ℂ, Continuous f →
      ContinuousAt (fun p : ℂ × ℂ => besselI (f p) p.1) (z, ν) := fun f hf =>
    ContinuousAt.comp (g := fun q : ℂ × ℂ => besselI q.1 q.2) (f := fun p : ℂ × ℂ => (f p, p.1))
      (continuousOn_besselI.continuousAt (prod_mem_nhds univ_mem (isOpen_slitPlane.mem_nhds hz)))
      (by fun_prop)
  refine ContinuousAt.continuousWithinAt ?_
  unfold besselE
  exact (hI _ continuous_snd.neg).sub (hI _ continuous_snd)

/-- Identity under the stated parameter and domain assumptions: `besselK μ z = π / 2 * dslope (fun
ν => besselE ν z) n μ / dslope (fun ν : ℂ => sin (ν * π)) n μ`. -/
theorem besselK_eq_dslope (n : ℤ) {μ z : ℂ} (hμ : μ ∈ Metric.ball (n : ℂ) (1 / 2))
    (hz : z ∈ slitPlane) :
    besselK μ z = π / 2 * dslope (fun ν => besselE ν z) n μ /
      dslope (fun ν : ℂ => sin (ν * π)) n μ := by
  have hz0 := slitPlane_ne_zero hz
  by_cases hne : μ = n
  · subst hne
    have hE := differentiable_besselE hz0
    have hcont : ContinuousAt (fun μ => π / 2 * dslope (fun ν => besselE ν z) n μ /
        dslope (fun ν : ℂ => sin (ν * π)) n μ) n :=
      (continuousAt_const.mul (continuousAt_dslope_same.mpr (hE n))).div
        (continuousAt_dslope_same.mpr (by fun_prop)) (dslope_sin_ne_zero n (Metric.mem_ball_self
          (by norm_num)))
    have ht : Tendsto (fun μ => π / 2 * (besselI (-μ) z - besselI μ z) / sin (μ * π))
        (𝓝[≠] (n : ℂ)) (𝓝 (π / 2 * dslope (fun ν => besselE ν z) n n /
          dslope (fun ν : ℂ => sin (ν * π)) n n)) := by
      refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with μ hμ
      rw [dslope_of_ne _ hμ, dslope_of_ne _ hμ, slope_def_field, slope_def_field,
        besselE_int, Complex.sin_int_mul_pi, sub_zero, sub_zero]
      have hμn : μ - n ≠ 0 := sub_ne_zero.mpr hμ
      simp only [besselE]
      field_simp
    have hex : ∃ k : ℤ, (n : ℂ) = k := ⟨n, rfl⟩
    simp only [besselK, hex, ite_true]
    exact ht.limUnder_eq
  · rw [besselK_eq_of_not_int (not_int_of_mem_ball hμ hne), dslope_of_ne _ hne,
      dslope_of_ne _ hne, slope_def_field, slope_def_field, besselE_int, Complex.sin_int_mul_pi,
      sub_zero, sub_zero]
    have hμn : μ - n ≠ 0 := sub_ne_zero.mpr hne
    field_simp

/-- **`K_ν(z)` is jointly continuous** in `(ν, z)` on `ℂ × slitPlane`, including integer orders. -/
theorem continuousAt_besselK (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    ContinuousAt (fun p : ℂ × ℂ => besselK p.1 p.2) (ν, z) := by
  have hE := continuousOn_besselE
  by_cases hν : ∃ k : ℤ, ν = k
  · obtain ⟨n, rfl⟩ := hν
    have hds := DLMF.Confluent.continuousOn_dslope_param (X := ℂ) (f := fun w ν => besselE ν w)
      isOpen_slitPlane hE (fun w hw => differentiable_besselE (slitPlane_ne_zero hw)) n
    have h1 : ContinuousAt (fun p : ℂ × ℂ => dslope (fun ν => besselE ν p.2) n p.1) (n, z) :=
      ContinuousAt.comp (g := fun q : ℂ × ℂ => dslope (fun ν => besselE ν q.1) n q.2)
        (f := Prod.swap) (hds.continuousAt (prod_mem_nhds (isOpen_slitPlane.mem_nhds hz)
          univ_mem)) continuous_swap.continuousAt
    have h2 : ContinuousAt (fun p : ℂ × ℂ => dslope (fun ν : ℂ => sin (ν * π)) n p.1) (n, z) :=
      ContinuousAt.comp (g := dslope (fun ν : ℂ => sin (ν * π)) n) (f := Prod.fst)
        (continuousAt_dslope_same.mpr (by fun_prop)) continuous_fst.continuousAt
    refine (((continuousAt_const (y := (π / 2 : ℂ))).mul h1).div h2
      (dslope_sin_ne_zero n (Metric.mem_ball_self (by norm_num)))).congr ?_
    filter_upwards [prod_mem_nhds (Metric.ball_mem_nhds (n : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
      (isOpen_slitPlane.mem_nhds hz)] with p hp
    exact (besselK_eq_dslope n hp.1 hp.2).symm
  · push Not at hν
    have hopen : IsOpen {μ : ℂ | sin (μ * π) ≠ 0} :=
      isOpen_ne_fun (by fun_prop) continuous_const
    have hc : ContinuousAt (fun p : ℂ × ℂ => π / 2 * besselE p.1 p.2 / sin (p.1 * π)) (ν, z) := by
      have h1 : ContinuousAt (fun p : ℂ × ℂ => besselE p.1 p.2) (ν, z) :=
        ContinuousAt.comp (g := fun q : ℂ × ℂ => besselE q.2 q.1) (f := Prod.swap)
          (hE.continuousAt (prod_mem_nhds (isOpen_slitPlane.mem_nhds hz) univ_mem))
          continuous_swap.continuousAt
      exact (continuousAt_const.mul h1).div (by fun_prop) (sin_mul_pi_ne_zero hν)
    refine hc.congr ?_
    filter_upwards [prod_mem_nhds (hopen.mem_nhds (sin_mul_pi_ne_zero hν)) univ_mem] with p hp
    have hp' : ∀ k : ℤ, p.1 ≠ k := fun k hk => hp.1 (by rw [hk]; exact Complex.sin_int_mul_pi k)
    exact (besselK_eq_of_not_int hp' p.2).symm

/-- The function `(fun μ => besselK (f μ) z)` is continuous at `ν`. -/
theorem continuousAt_besselK_order (f : ℂ → ℂ) (hf : Continuous f) (ν : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) : ContinuousAt (fun μ => besselK (f μ) z) ν :=
  ContinuousAt.comp (g := fun p : ℂ × ℂ => besselK p.1 p.2) (f := fun μ => (f μ, z))
    (continuousAt_besselK (f ν) hz) (by fun_prop)

/-- The function `(fun μ => besselI (f μ) z)` is continuous at `ν`. -/
theorem continuousAt_besselI_order (f : ℂ → ℂ) (hf : Continuous f) (ν : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) : ContinuousAt (fun μ => besselI (f μ) z) ν :=
  ContinuousAt.comp (g := fun p : ℂ × ℂ => besselI p.1 p.2) (f := fun μ => (f μ, z))
    (continuousOn_besselI.continuousAt (prod_mem_nhds univ_mem (isOpen_slitPlane.mem_nhds hz)))
    (by fun_prop)

/-- **The recurrence for `K_ν`** (DLMF 10.29.1), for every order:
`K_{ν+1} - K_{ν-1} = (2ν/z) K_ν`. -/
@[dlmf 10.29.E1]
theorem besselK_add_sub (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (2 * ν / z) * besselK ν z = besselK (ν + 1) z - besselK (ν - 1) z := by
  have hz0 := slitPlane_ne_zero hz
  refine DLMF.Confluent.eq_of_continuousAt_of_integerComplement
    (f := fun ν => (2 * ν / z) * besselK ν z)
    (g := fun ν => besselK (ν + 1) z - besselK (ν - 1) z)
    ((by fun_prop : Continuous fun ν : ℂ => 2 * ν / z).continuousAt.mul
      (continuousAt_besselK_order id continuous_id ν hz))
    ((continuousAt_besselK_order (· + 1) (by fun_prop) ν hz).sub
      (continuousAt_besselK_order (· - 1) (by fun_prop) ν hz)) fun c hc => ?_
  have hcz := DLMF.Confluent.forall_of_mem_integerComplement hc
  have hs := sin_mul_pi_ne_zero hcz
  rw [besselK_eq_of_not_int hcz, besselK_eq_of_not_int (not_int_sub_one hcz),
    besselK_eq_of_not_int (not_int_add_one hcz), sin_sub_one_mul_pi, sin_add_one_mul_pi]
  simp only [besselE]
  have h1 := besselI_sub_add (ν := c) hz0
  have h2 := besselI_sub_add (ν := -c) hz0
  rw [show -c - 1 = -(c + 1) by ring, show -c + 1 = -(c - 1) by ring] at h2
  rw [div_neg, div_neg]
  linear_combination (-(π / 2 / sin (c * π))) * h1 - (π / 2 / sin (c * π)) * h2

/-- At `z`, the function `(besselK ν)` has derivative `((ν / z) * besselK ν z - besselK (ν + 1)
z)`. -/
theorem hasDerivAt_besselK_of_not_int {ν : ℂ} (hν : ∀ k : ℤ, ν ≠ k) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (besselK ν) ((ν / z) * besselK ν z - besselK (ν + 1) z) z := by
  have hs := sin_mul_pi_ne_zero hν
  have hK : besselK ν = fun w => π / 2 * besselE ν w / sin (ν * π) :=
    funext fun w => besselK_eq_of_not_int hν w
  have hI1 := hasDerivAt_besselI (ν := ν) hz
  have hI2 := hasDerivAt_besselI' (ν := -ν) hz
  have hE : HasDerivAt (fun w => besselE ν w)
      ((besselI (-ν - 1) z - -ν / z * besselI (-ν) z) -
        (ν / z * besselI ν z + besselI (ν + 1) z)) z := by
    unfold besselE
    exact hI2.sub hI1
  have h := (hE.const_mul (π / 2 : ℂ)).div_const (sin (ν * π))
  rw [← hK] at h
  convert h using 1
  rw [besselK_eq_of_not_int hν, besselK_eq_of_not_int (not_int_add_one hν), sin_add_one_mul_pi]
  simp only [besselE, show -(ν + 1) = -ν - 1 by ring]
  field_simp
  ring

/-- **The derivative of `K_ν`** (DLMF 10.29.2), for every order: `K_ν' = (ν/z) K_ν - K_{ν+1}`. -/
@[dlmf 10.29.E2]
theorem hasDerivAt_besselK (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (besselK ν) ((ν / z) * besselK ν z - besselK (ν + 1) z) z := by
  have := DLMF.Confluent.integerComplement_nhdsWithin_neBot ν
  refine hasDerivAt_of_tendstoUniformlyOnFilter (l := 𝓝[integerComplement] ν)
    (f := fun c => besselK c) (f' := fun c w => (c / w) * besselK c w - besselK (c + 1) w)
    (g' := fun w => (ν / w) * besselK ν w - besselK (ν + 1) w) ?_ ?_ ?_
  · have hc : ContinuousAt (fun p : ℂ × ℂ => (p.1 / p.2) * besselK p.1 p.2 -
        besselK (p.1 + 1) p.2) (ν, z) := by
      have h1 := continuousAt_besselK ν hz
      have h2 : ContinuousAt (fun p : ℂ × ℂ => besselK (p.1 + 1) p.2) (ν, z) :=
        ContinuousAt.comp (g := fun p : ℂ × ℂ => besselK p.1 p.2)
          (f := fun p : ℂ × ℂ => (p.1 + 1, p.2)) (continuousAt_besselK (ν + 1) hz) (by fun_prop)
      exact ((continuousAt_fst.div continuousAt_snd (slitPlane_ne_zero hz)).mul h1).sub h2
    exact DLMF.Confluent.tendstoUniformlyOnFilter_of_continuousAt
      (F := fun c w => (c / w) * besselK c w - besselK (c + 1) w) hc nhdsWithin_le_nhds
  · have hm : integerComplement ×ˢ slitPlane ∈ 𝓝[integerComplement] ν ×ˢ 𝓝 z :=
      prod_mem_prod self_mem_nhdsWithin (isOpen_slitPlane.mem_nhds hz)
    filter_upwards [hm] with p hp
    exact hasDerivAt_besselK_of_not_int (DLMF.Confluent.forall_of_mem_integerComplement hp.1) hp.2
  · filter_upwards [isOpen_slitPlane.mem_nhds hz] with y hy
    exact ((continuousAt_besselK_order id continuous_id ν hy).tendsto).mono_left
      nhdsWithin_le_nhds

/-- **The modified Bessel equation for `K_ν`** (DLMF 10.25.1), for every order. -/
@[dlmf 10.25.E1]
theorem besselK_ode_all (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    z ^ 2 * iteratedDeriv 2 (besselK ν) z + z * deriv (besselK ν) z -
      (z ^ 2 + ν ^ 2) * besselK ν z = 0 := by
  have hz0 := slitPlane_ne_zero hz
  have hderiv : deriv (besselK ν) =ᶠ[𝓝 z] fun w => (ν / w) * besselK ν w - besselK (ν + 1) w := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    exact (hasDerivAt_besselK ν hw).deriv
  have h2 : HasDerivAt (fun w => (ν / w) * besselK ν w - besselK (ν + 1) w)
      ((-(ν / z ^ 2)) * besselK ν z + (ν / z) * ((ν / z) * besselK ν z - besselK (ν + 1) z) -
        (((ν + 1) / z) * besselK (ν + 1) z - besselK (ν + 1 + 1) z)) z := by
    have hinv : HasDerivAt (fun w : ℂ => ν / w) (-(ν / z ^ 2)) z := by
      have := (hasDerivAt_inv hz0).const_mul ν
      convert this using 1 <;> [funext w; skip] <;> field_simp
    exact (hinv.mul (hasDerivAt_besselK ν hz)).sub (hasDerivAt_besselK (ν + 1) hz)
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv.deriv_eq, h2.deriv,
    (hasDerivAt_besselK ν hz).deriv]
  have hr := besselK_add_sub (ν + 1) hz
  rw [show ν + 1 - 1 = ν by ring] at hr
  have hK2 : besselK (ν + 1 + 1) z = (2 * (ν + 1) / z) * besselK (ν + 1) z + besselK ν z := by
    linear_combination -hr
  rw [hK2]
  field_simp
  ring

/-- **The Wronskian of `I_ν` and `I_{-ν}`** (DLMF 10.28.1). -/
@[dlmf 10.28.E1]
theorem wronskian_besselI_neg (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    besselI ν z * deriv (besselI (-ν)) z - deriv (besselI ν) z * besselI (-ν) z =
      -2 * sin (ν * π) / (π * z) := by
  have hz0 := slitPlane_ne_zero hz
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz0 two_ne_zero
  rw [(hasDerivAt_besselI' (ν := -ν) hz).deriv, (hasDerivAt_besselI (ν := ν) hz).deriv]
  have hW : besselI ν z * (besselI (-ν - 1) z - -ν / z * besselI (-ν) z) -
      (ν / z * besselI ν z + besselI (ν + 1) z) * besselI (-ν) z =
      besselI ν z * besselI (-ν - 1) z - besselI (ν + 1) z * besselI (-ν) z := by ring
  rw [hW]
  have hS := besselWronskianSeries_eq ν (z ^ 2 / 4)
  unfold besselWronskianSeries at hS
  unfold besselI
  rw [show -ν - 1 + 1 = -ν by ring, show -ν + 1 = 1 - ν by ring, show ν + 1 + 1 = ν + 2 by ring]
  have hp1 : (z / 2) ^ ν * (z / 2) ^ (-ν - 1) = 2 / z := by
    rw [← cpow_add _ _ hz2, show ν + (-ν - 1) = -1 by ring, cpow_neg_one, inv_div]
  have hp2 : (z / 2) ^ (ν + 1) * (z / 2) ^ (-ν) = z / 2 := by
    rw [← cpow_add _ _ hz2, show ν + 1 + -ν = 1 by ring, cpow_one]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz' : (2 / z) * (z ^ 2 / 4) = z / 2 := by field_simp; ring
  rw [show sin (ν * π) = sin (π * ν) by ring_nf]
  linear_combination (2 / z) * hS + (regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (z ^ 2 / 4) *
    regularizedHGFun ∅ {-ν} (z ^ 2 / 4)) * hp1 - (regularizedHGFun (∅ : Multiset ℂ) {ν + 2}
      (z ^ 2 / 4) * regularizedHGFun ∅ {1 - ν} (z ^ 2 / 4)) * hp2 +
    (regularizedHGFun (∅ : Multiset ℂ) {ν + 2} (z ^ 2 / 4) *
      regularizedHGFun ∅ {1 - ν} (z ^ 2 / 4)) * hz'

/-- Identity under the stated parameter and domain assumptions: `besselK ν z * besselI (ν + 1) z +
besselK (ν + 1) z * besselI ν z = 1 / z`. -/
theorem besselK_mul_besselI_succ_add (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    besselK ν z * besselI (ν + 1) z + besselK (ν + 1) z * besselI ν z = 1 / z := by
  have hz0 := slitPlane_ne_zero hz
  refine DLMF.Confluent.eq_of_continuousAt_of_integerComplement
    (f := fun ν => besselK ν z * besselI (ν + 1) z + besselK (ν + 1) z * besselI ν z)
    (g := fun _ => 1 / z)
    (((continuousAt_besselK_order id continuous_id ν hz).mul
      (continuousAt_besselI_order (· + 1) (by fun_prop) ν hz)).add
      ((continuousAt_besselK_order (· + 1) (by fun_prop) ν hz).mul
      (continuousAt_besselI_order id continuous_id ν hz))) continuousAt_const fun c hc => ?_
  have hcz := DLMF.Confluent.forall_of_mem_integerComplement hc
  have hs := sin_mul_pi_ne_zero hcz
  have hW := wronskian_besselI_neg c hz
  rw [(hasDerivAt_besselI' (ν := -c) hz).deriv, (hasDerivAt_besselI (ν := c) hz).deriv] at hW
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [besselK_eq_of_not_int hcz, besselK_eq_of_not_int (not_int_add_one hcz), sin_add_one_mul_pi]
  simp only [besselE, show -(c + 1) = -c - 1 by ring]
  field_simp at hW ⊢
  linear_combination (-1 : ℂ) * hW

/-- **The Wronskian of `K_ν` and `I_ν`** (DLMF 10.28.2): `W{K_ν, I_ν} = 1/z`, for every order. -/
@[dlmf 10.28.E2]
theorem wronskian_besselK_besselI (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    besselK ν z * deriv (besselI ν) z - deriv (besselK ν) z * besselI ν z = 1 / z := by
  rw [(hasDerivAt_besselK ν hz).deriv, (hasDerivAt_besselI (ν := ν) hz).deriv,
    ← besselK_mul_besselI_succ_add ν hz]
  ring

/-- `K_{-ν} = K_ν` (DLMF 10.27.3). -/
@[dlmf 10.27.E3]
theorem besselK_neg (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) : besselK (-ν) z = besselK ν z := by
  refine DLMF.Confluent.eq_of_continuousAt_of_integerComplement
    (f := fun μ => besselK (-μ) z) (g := fun μ => besselK μ z)
    (continuousAt_besselK_order (fun μ => -μ) continuous_neg ν hz)
    (continuousAt_besselK_order (fun μ => μ) continuous_id ν hz) (fun c hc => ?_)
  have hc' := DLMF.Confluent.forall_of_mem_integerComplement hc
  have hcn : ∀ k : ℤ, -c ≠ k := fun k h => hc' (-k) (by push_cast; linear_combination -h)
  have hs := sin_mul_pi_ne_zero hc'
  rw [besselK_eq_of_not_int hcn, besselK_eq_of_not_int hc', besselE, besselE, neg_neg, neg_mul,
    Complex.sin_neg]
  field_simp
  ring

end DLMF.Bessel
