/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Basics.OrderSymbols
public import DLMF.AsymptoticApproximations.Mellin.Transforms
public import DLMF.IncompleteGamma.ExponentialIntegral
public import DLMFMathlib.Analysis.Integral.LaplaceMoments

/-!
# Power-tail models for small-parameter Laplace expansions

The Laplace transform of `t^(-β)` on `(1, ∞)` separates into the singular power
`Γ(1-β) ζ^(β-1)` and an entire series. Truncating that series gives the model remainder
used in DLMF §2.5(iii).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Asymptotics Complex Finset
open scoped Topology

namespace DLMF.AsymptoticApproximations

/-- The Laplace transform of a complex power on `(1, ∞)` is absolutely convergent for
positive real Laplace parameter. -/
theorem integrableOn_exp_neg_mul_cpow_tail (β : ℂ) {ζ : ℝ} (hζ : 0 < ζ) :
    IntegrableOn (fun t : ℝ => exp (-(ζ : ℂ) * t) * (t : ℂ) ^ (-β)) (Ioi 1) := by
  refine IntegrableOn.congr_fun
    (DLMF.Confluent.GeneralizedExpIntegral.paramIntegrand_integrableOn 0 β
      (z := (ζ : ℂ)) (by simpa using hζ)) (fun t _ => ?_) measurableSet_Ioi
  simp only [pow_zero, one_mul]
  ring

/-- The truncated power-tail Laplace kernel is absolutely integrable. -/
theorem integrableOn_exp_neg_mul_truncHigh_cpow (β d : ℂ) {ζ : ℝ} (hζ : 0 < ζ) :
    IntegrableOn (fun t : ℝ => exp (-(ζ : ℂ) * t) *
      mellinTruncHigh (fun t => (t : ℂ) ^ (-β) * d) t) (Ioi 0) := by
  have hi' : IntegrableOn (fun t : ℝ => exp (-(ζ : ℂ) * t) *
      (t : ℂ) ^ (-β) * d) (Ioi 1) := (integrableOn_exp_neg_mul_cpow_tail β hζ).mul_const d
  have hi := IntegrableOn.integrable_indicator hi' measurableSet_Ioi
  refine IntegrableOn.congr_fun hi.integrableOn (fun t _ => ?_) measurableSet_Ioi
  rw [mellinTruncHigh_eq_indicator]
  by_cases ht : t ∈ Ioi (1 : ℝ) <;> simp [ht, mul_assoc]

/-- The truncated power-tail Laplace integral is the generalized exponential integral. -/
theorem integral_exp_neg_mul_truncHigh_cpow (β d : ℂ) {ζ : ℝ} (hζ : 0 < ζ) :
    (∫ t in Ioi (0 : ℝ), exp (-(ζ : ℂ) * t) *
      mellinTruncHigh (fun t => (t : ℂ) ^ (-β) * d) t) =
      DLMF.Confluent.expIntegralE β ζ * d := by
  rw [mellinTruncHigh_eq_indicator]
  have he : (fun t : ℝ => exp (-(ζ : ℂ) * t) *
      (Ioi (1 : ℝ)).indicator (fun t => (t : ℂ) ^ (-β) * d) t) =
      (Ioi (1 : ℝ)).indicator
        (fun t => exp (-(ζ : ℂ) * t) * (t : ℂ) ^ (-β) * d) := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ) <;> simp [ht, mul_assoc]
  rw [he, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    show Set.Ioi (1 : ℝ) ∩ Set.Ioi 0 = Set.Ioi 1 from
      inter_eq_left.mpr (Set.Ioi_subset_Ioi zero_le_one), integral_mul_const,
    ← DLMF.Confluent.expIntegralE_laplace_complex β (by simpa using hζ)]

/-- A complex power tail has its singular Gamma term and the displayed ordinary-power
correction, with error `O(ζ^M)`. Positive integral exponents require logarithmic terms and
are excluded here. -/
theorem laplace_cpow_tail_sub_sum_isBigO {β : ℂ} (hβ : ∀ n : ℕ, β ≠ n + 1) (M : ℕ) :
    (fun ζ : ℝ => (∫ t in Ioi (1 : ℝ), exp (-(ζ : ℂ) * t) * (t : ℂ) ^ (-β)) -
      Gamma (1 - β) * (ζ : ℂ) ^ (β - 1) +
        ∑ m ∈ range M, (-(ζ : ℂ)) ^ m / ((m.factorial : ℂ) * (1 - β + m)))
      =O[𝓝[>] 0] (fun ζ : ℝ => ζ ^ M) := by
  let A : ℕ → ℂ := fun m => (-1 : ℂ) ^ m / ((m.factorial : ℂ) * (1 - β + m))
  have hterm (z : ℂ) (m : ℕ) : A m * z ^ m =
      (-z) ^ m / ((m.factorial : ℂ) * (1 - β + m)) := by
    dsimp [A]
    rw [neg_pow]
    ring
  have hs (z : ℂ) : Summable (fun m : ℕ => A m * z ^ m) := by
    by_cases hz : z = 0
    · subst z
      apply summable_of_ne_finset_zero (s := {0})
      intro m hm
      have hm0 : m ≠ 0 := by simpa using hm
      simp [hm0]
    · simpa only [hterm] using (DLMF.Confluent.expIntegralE_hasSum_noninteger hβ hz).summable
  have htail := tsum_tail_isBigO_pow (a := A) ⟨1, one_pos, fun z _ => hs z⟩ M
  have hzero : Tendsto (fun ζ : ℝ => (ζ : ℂ)) (𝓝[>] 0) (𝓝 0) :=
    continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hscale : (fun ζ : ℝ => (ζ : ℂ) ^ M) =O[𝓝[>] 0] (fun ζ : ℝ => ζ ^ M) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun ζ => ?_)
    simp [norm_pow, norm_real, Real.norm_eq_abs, abs_pow]
  refine (((htail.comp_tendsto hzero).neg_left).trans hscale).congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with ζ hζ
  have hζ0 : (ζ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hζ)
  have hsum := (hs (ζ : ℂ)).sum_add_tsum_nat_add M
  have hv : (∑' m : ℕ, A m * (ζ : ℂ) ^ m) =
      (ζ : ℂ) ^ (β - 1) * Gamma (1 - β) - DLMF.Confluent.expIntegralE β ζ := by
    simpa only [hterm] using
      (DLMF.Confluent.expIntegralE_hasSum_noninteger hβ hζ0).tsum_eq
  rw [hv] at hsum
  rw [← DLMF.Confluent.expIntegralE_laplace_complex β (by simpa using hζ)]
  simp_rw [← hterm]
  dsimp only [Function.comp_def]
  linear_combination -hsum

/-- If the subtracted remainder has moments through degree `M`, the small-parameter
Laplace expansion through the displayed `N` singular powers has error `O(ζ^M)`. -/
theorem laplace_small_parameter_of_lt_re {h : ℝ → ℂ} {b β : ℕ → ℂ} {c : ℝ} {H : ℂ → ℂ}
    (hc : -1 < c) (hhc : LocallyIntegrableOn h (Ioi 0))
    (h0 : h =O[𝓝[>] 0] fun t => t ^ c) (hβ : StrictMono fun s => (β s).re)
    (hβint : ∀ s (m : ℕ), β s ≠ m + 1)
    (hh : HasAsymptoticExpansion atTop (fun s (t : ℝ) => (t : ℂ) ^ (-β s)) b h)
    (hH : ∀ z : ℂ, z.re < (β 0).re → H z = mellin (mellinTruncHigh h) z)
    (hHd : ∀ N : ℕ, DifferentiableOn ℂ (fun z => H z + ∑ s ∈ range N, b s / (z - β s))
      {z : ℂ | z.re < (β N).re}) (N M : ℕ) (hN : (M : ℝ) + 1 < (β N).re) :
    (fun ζ : ℝ => DLMF.AlgebraicAnalytic.laplaceTransform h ζ -
      ∑ s ∈ range N, b s * Gamma (1 - β s) * (ζ : ℂ) ^ (β s - 1) -
      ∑ m ∈ range M, (-(ζ : ℂ)) ^ m / (m.factorial : ℂ) *
        (mellin (mellinTruncLow h) (m + 1) + H (m + 1)))
      =O[𝓝[>] 0] (fun ζ : ℝ => ζ ^ M) := by
  let r : ℝ → ℂ := fun t => h t - ∑ s ∈ range N, (t : ℂ) ^ (-β s) * b s
  let g : ℝ → ℂ := fun t => mellinTruncLow h t + mellinTruncHigh r t
  have hlow (m : ℕ) : MellinConvergent (mellinTruncLow h) ((m : ℂ) + 1) := by
    apply mellinConvergent_truncLow hhc h0
    simp only [add_re, natCast_re, one_re]
    linarith [show 0 ≤ (m : ℝ) by positivity]
  have hzN (m : ℕ) (hm : m ≤ M) : ((m : ℂ) + 1).re < (β N).re := by
    have hm' : (m : ℝ) ≤ M := by exact_mod_cast hm
    simp only [add_re, natCast_re, one_re]
    linarith
  have hhigh (m : ℕ) (hm : m ≤ M) :
      MellinConvergent (mellinTruncHigh r) ((m : ℂ) + 1) := by
    simpa only [r, smul_eq_mul] using mellinConvergent_truncHigh_sub_sum hhc hh N (hzN m hm)
  have hconv (m : ℕ) (hm : m ≤ M) : MellinConvergent g ((m : ℂ) + 1) :=
    (hasMellin_add (hlow m) (hhigh m hm)).1
  have hmom (m : ℕ) (hm : m ≤ M) :
      IntegrableOn (fun t : ℝ => (t : ℂ) ^ m * g t) (Ioi 0) := by
    simpa only [MellinConvergent, add_sub_cancel_right, cpow_natCast, smul_eq_mul] using hconv m hm
  have hcoeff (m : ℕ) (hm : m ≤ M) :
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ m * g t) =
        (mellin (mellinTruncLow h) (m + 1) + H (m + 1)) +
          ∑ s ∈ range N, b s / ((m : ℂ) + 1 - β s) := by
    have hr := mellin_truncHigh_continuation_regularPart_eq hhc hβ hh hH hHd N (hzN m hm)
    have he := (hasMellin_add (hlow m) (hhigh m hm)).2
    have heg : mellin g ((m : ℂ) + 1) = ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ m * g t := by
      simp only [mellin, add_sub_cancel_right, cpow_natCast, smul_eq_mul]
    change mellin g ((m : ℂ) + 1) = _ at he
    rw [heg] at he
    have hr' : H (m + 1) + ∑ s ∈ range N, b s / ((m : ℂ) + 1 - β s) =
        mellin (mellinTruncHigh r) (m + 1) := by simpa only [r, smul_eq_mul] using hr
    rw [← hr'] at he
    exact he.trans (by ring)
  have hg : IntegrableOn g (Ioi 0) := by simpa using hmom 0 (Nat.zero_le M)
  have hpoint (t : ℝ) : h t = g t +
      ∑ s ∈ range N, mellinTruncHigh (fun t => (t : ℂ) ^ (-β s) * b s) t := by
    dsimp only [g, r]
    by_cases ht : t ≤ 1 <;> simp [mellinTruncHigh, mellinTruncLow, ht] <;> ring
  have hsplit (ζ : ℝ) (hζ : 0 < ζ) : DLMF.AlgebraicAnalytic.laplaceTransform h ζ =
      (∫ t in Ioi (0 : ℝ), exp (-(ζ : ℂ) * t) * g t) +
        ∑ s ∈ range N, (∫ t in Ioi (1 : ℝ), exp (-(ζ : ℂ) * t) *
          (t : ℂ) ^ (-β s)) * b s := by
    let Q : ℕ → ℝ → ℂ := fun s t => exp (-(ζ : ℂ) * t) *
      mellinTruncHigh (fun t => (t : ℂ) ^ (-β s) * b s) t
    have hi (s : ℕ) : IntegrableOn (Q s) (Ioi 0) :=
      integrableOn_exp_neg_mul_truncHigh_cpow (β s) (b s) hζ
    have he : (fun t : ℝ => exp (-(ζ : ℂ) * t) * h t) =
        (fun t : ℝ => exp (-(ζ : ℂ) * t) * g t) +
          (fun t => ∑ s ∈ range N, Q s t) := by
      funext t
      dsimp only [Pi.add_apply, Q]
      conv_lhs => rw [hpoint t]
      rw [mul_add, mul_sum]
    unfold DLMF.AlgebraicAnalytic.laplaceTransform
    rw [he, Pi.add_def, integral_add (hg.cexp_neg_mul_of_nonneg hζ.le)
      (integrable_finsetSum _ (fun s _ => hi s)), integral_finsetSum _ (fun s _ => hi s)]
    congr 1
    apply sum_congr rfl
    intro s _
    dsimp only [Q]
    rw [integral_exp_neg_mul_truncHigh_cpow (β s) (b s) hζ,
      DLMF.Confluent.expIntegralE_laplace_complex (β s) (by simpa using hζ)]
  have hmodels (s : ℕ) :
      (fun ζ : ℝ => ((∫ t in Ioi (1 : ℝ), exp (-(ζ : ℂ) * t) * (t : ℂ) ^ (-β s)) -
        Gamma (1 - β s) * (ζ : ℂ) ^ (β s - 1) +
          ∑ m ∈ range M, (-(ζ : ℂ)) ^ m / ((m.factorial : ℂ) * (1 - β s + m))) * b s)
        =O[𝓝[>] 0] (fun ζ : ℝ => ζ ^ M) :=
    ((laplace_cpow_tail_sub_sum_isBigO (hβint s) M).const_mul_left (b s)).congr_left
      (fun ζ => mul_comm (b s) _)
  have hbnd := (isBigO_integral_exp_neg_mul_sub_sum M hmom).add
    (IsBigO.fun_sum (s := range N) fun s _ => hmodels s)
  refine hbnd.congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with ζ hζ
  have hcorr : (∑ s ∈ range N, (∑ m ∈ range M,
      (-(ζ : ℂ)) ^ m / ((m.factorial : ℂ) * (1 - β s + m))) * b s) =
      ∑ m ∈ range M, (-(ζ : ℂ)) ^ m / (m.factorial : ℂ) *
        ∑ s ∈ range N, b s / ((m : ℂ) + 1 - β s) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro s _
    rw [show 1 - β s + (m : ℂ) = (m : ℂ) + 1 - β s by ring]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hmoment : (∑ m ∈ range M, (-(ζ : ℂ)) ^ m / (m.factorial : ℂ) *
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ m * g t) =
      (∑ m ∈ range M, (-(ζ : ℂ)) ^ m / (m.factorial : ℂ) *
        (mellin (mellinTruncLow h) (m + 1) + H (m + 1))) +
      ∑ m ∈ range M, (-(ζ : ℂ)) ^ m / (m.factorial : ℂ) *
        ∑ s ∈ range N, b s / ((m : ℂ) + 1 - β s) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro m hm
    rw [hcoeff m (Nat.le_of_lt (mem_range.mp hm)), mul_add]
  have hgamma : (∑ s ∈ range N, Gamma (1 - β s) * (ζ : ℂ) ^ (β s - 1) * b s) =
      ∑ s ∈ range N, b s * Gamma (1 - β s) * (ζ : ℂ) ^ (β s - 1) :=
    sum_congr rfl fun s _ => by ring
  rw [hsplit ζ hζ]
  simp_rw [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hcorr, hmoment, hgamma]
  ring

end DLMF.AsymptoticApproximations
