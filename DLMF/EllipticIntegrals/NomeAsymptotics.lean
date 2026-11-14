/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.JacobiElliptic.ModulusInversion
public import DLMFMathlib.Analysis.Asymptotics.SparsePowerSeries
import Mathlib.Tactic

/-!
# Asymptotic expansions of the elliptic nome

The theta-constant inversion formula expresses `k²/16` as a quotient of convergent
integer-power series in the nome. Sparse-series tail bounds and polynomial reversion
then give Jacobi's expansion at a vanishing positive real modulus.

## Main results

* `Real.tendsto_jacobiNome_zero`: the nome tends to zero at a vanishing positive modulus.
* `jacobiNome_theta_series_relation`: the modulus as a quotient of nome power series.
* `jacobiNome_isBigO`: the expansion through fourth order (DLMF 19.5.5).
-/

open Complex Set Filter Asymptotics
open scoped Real Topology
namespace DLMF.EllipticIntegrals.Real
private theorem eventually_norm_jacobiNome_le_sq :
    ∀ᶠ k : ℝ in 𝓝[>] 0, ‖DLMF.JacobiElliptic.jacobiNome k‖ ≤ k ^ 2 := by
  let F : ℝ → ℝ := fun k =>
    (2 / π * DLMF.Elliptic.Real.completeEllipticKOfParameter (k ^ 2)) ^ 2
  have hsq : ContinuousAt (fun k : ℝ => k ^ 2) 0 := by fun_prop
  have hK : ContinuousAt
      (fun k : ℝ => DLMF.Elliptic.Real.completeEllipticKOfParameter (k ^ 2)) 0 :=
    (DLMF.Elliptic.Real.continuousAt_completeEllipticKOfParameter
      (by norm_num : (0 : ℝ) < 1)).comp_of_eq hsq (by norm_num)
  have hc : ContinuousAt F 0 := (continuousAt_const.mul hK).pow 2
  have hz : F 0 = 1 := by
    dsimp only [F]
    rw [zero_pow (by decide : (2 : ℕ) ≠ 0),
      DLMF.Elliptic.Real.completeEllipticKOfParameter_zero]
    field_simp
  have hl := (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  rw [hz] at hl
  have hs := hl.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 16))
  filter_upwards [hs, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with k hk hk0
  have h := DLMF.JacobiElliptic.Real.norm_jacobiNome_le_sq_mul_completeEllipticKOfParameter_sq
    hk0.1 hk0.2
  apply h.trans
  dsimp only [F] at hk
  nlinarith [sq_nonneg k]

/-- The real nome tends to zero as its positive modulus tends to zero. -/
public theorem tendsto_jacobiNome_zero :
    Tendsto (fun k : ℝ => DLMF.JacobiElliptic.jacobiNome k) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero_norm' eventually_norm_jacobiNome_le_sq
  simpa using ((continuous_pow 2).tendsto (0 : ℝ)).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

/-- The real nome is bounded by a constant multiple of `k²/16` near zero. -/
public theorem jacobiNome_isBigO_sq_div_sixteen :
    (fun k : ℝ => DLMF.JacobiElliptic.jacobiNome k) =O[𝓝[>] 0]
      (fun k : ℝ => ((k ^ 2 / 16 : ℝ) : ℂ)) := by
  refine IsBigO.of_bound 16 ?_
  filter_upwards [eventually_norm_jacobiNome_le_sq] with k hk
  rw [norm_real, _root_.Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ k ^ 2 / 16)]
  nlinarith
end DLMF.EllipticIntegrals.Real

namespace DLMF.EllipticIntegrals
open DLMF.JacobiElliptic DLMF.Elliptic
/-- The theta-constant inversion formula expressed with integer-power nome series. -/
public theorem jacobiNome_theta_series_relation {k : ℂ}
    (hk : k ∈ jacobiModulusDomain) (hq : ‖jacobiNome k‖ < 1) :
    k ^ 2 / 16 = jacobiNome k * (∑' n : ℕ, jacobiNome k ^ (n * (n + 1))) ^ 4 /
      (2 * (∑' n : ℕ, jacobiNome k ^ (n ^ 2)) - 1) ^ 4 := by
  let q := jacobiNome k
  let p := cexp (π * I * jacobiTau k / 4)
  have hqexp : q = cexp (π * I * jacobiTau k) := jacobiNome_eq_exp_tau k
  have hp : p ^ 4 = q := by
    rw [hqexp, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hs := summable_nat_pow_of_le_exponent hq (fun n => n * (n + 1))
    (fun n => by nlinarith)
  have ht := summable_nat_pow_of_le_exponent hq (fun n => n ^ 2) (fun n => by nlinarith)
  have h2 := DLMF.Theta.jacobiThetaTwoTau_hasSum_cos 0 (jacobiTau_im_pos hk)
  have hterm2 (n : ℕ) : 2 * cexp (π * I * jacobiTau k * ((n : ℂ) + 1 / 2) ^ 2) *
      cos ((2 * n + 1) * 0) = (2 * p) * q ^ (n * (n + 1)) := by
    simp only [mul_zero, cos_zero, mul_one]
    dsimp only [p]
    rw [hqexp, ← Complex.exp_nat_mul]
    conv_rhs => rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have htheta2 : jacobiThetaTwoTau 0 (jacobiTau k) =
      2 * p * ∑' n : ℕ, q ^ (n * (n + 1)) := by
    exact ((h2.congr_fun fun n => (hterm2 n).symm).unique (hs.hasSum.mul_left (2 * p)))
  have h3 := DLMF.Theta.jacobiThetaThreeTau_hasSum_cos 0 (jacobiTau_im_pos hk)
  have hterm3 (n : ℕ) : 2 * cexp (π * I * jacobiTau k * ((n : ℂ) + 1) ^ 2) *
      cos (2 * ((n : ℂ) + 1) * 0) = 2 * q ^ ((n + 1) ^ 2) := by
    simp only [mul_zero, cos_zero, mul_one]
    rw [hqexp, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  have htheta3 : jacobiThetaThreeTau 0 (jacobiTau k) =
      2 * (∑' n : ℕ, q ^ (n ^ 2)) - 1 := by
    have H := (h3.congr_fun fun n => (hterm3 n).symm).tsum_eq
    rw [tsum_mul_left] at H
    have T := ht.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one, zero_pow (by decide : (2 : ℕ) ≠ 0), pow_zero] at T
    linear_combination -H + 2 * T
  have hm := (jacobi_inversion_k hk).1
  rw [jacobiModulusOfTau, htheta2, htheta3] at hm
  have hn : 2 * (∑' n : ℕ, q ^ (n ^ 2)) - 1 ≠ 0 := by
    rw [← htheta3]
    exact jacobiThetaThreeTau_zero_ne_zero (jacobiTau_im_pos hk)
  calc
    k ^ 2 / 16 = ((2 * p * ∑' n : ℕ, q ^ (n * (n + 1))) ^ 2 /
        (2 * (∑' n : ℕ, q ^ (n ^ 2)) - 1) ^ 2) ^ 2 / 16 :=
      congrArg (fun x : ℂ => x ^ 2 / 16) hm.symm
    _ = q * (∑' n : ℕ, q ^ (n * (n + 1))) ^ 4 /
        (2 * (∑' n : ℕ, q ^ (n ^ 2)) - 1) ^ 4 := by
      field_simp [hn]
      rw [show p ^ 4 = q from hp]
      ring
end DLMF.EllipticIntegrals

namespace DLMF.EllipticIntegrals
private theorem nome_forward_remainder :
    (fun q : ℂ => q * (∑' n : ℕ, q ^ (n * (n + 1))) ^ 4 /
        (2 * (∑' n : ℕ, q ^ (n ^ 2)) - 1) ^ 4 -
        (q - 8 * q ^ 2 + 44 * q ^ 3 - 192 * q ^ 4)) =O[𝓝 0] fun q => q ^ 5 := by
  let S : ℂ → ℂ := fun q => ∑' n : ℕ, q ^ (n * (n + 1))
  let D : ℂ → ℂ := fun q => 2 * (∑' n : ℕ, q ^ (n ^ 2)) - 1
  let S₀ : ℂ → ℂ := fun q => 1 + q ^ 2
  let D₀ : ℂ → ℂ := fun q => 1 + 2 * q
  let P : ℂ → ℂ := fun q => q - 8 * q ^ 2 + 44 * q ^ 3 - 192 * q ^ 4
  have hS : (fun q => S q - S₀ q) =O[𝓝 0] fun q => q ^ 4 := by
    simpa [S, S₀, Finset.sum_range_succ] using
      isBigO_tsum_nat_pow_sub_sum (K := ℂ) (fun n => n * (n + 1)) 2 4 (by
        intro n; nlinarith)
  have hD : (fun q => D q - D₀ q) =O[𝓝 0] fun q => q ^ 4 := by
    have H := (isBigO_tsum_nat_pow_sub_sum (K := ℂ) (fun n => n ^ 2) 2 4
      (by intro n; nlinarith)).const_mul_left (2 : ℂ)
    convert H using 1 ; funext q ; simp only [D, D₀, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), pow_zero,
      pow_one, one_pow] ; ring
  have hS1 : Tendsto S (𝓝 0) (𝓝 1) := by
    have H := (isBigO_tsum_nat_pow_sub_sum (K := ℂ) (fun n => n * (n + 1)) 1 1
      (by intro n; nlinarith)).trans_tendsto (by simpa using (continuous_pow 1).tendsto (0 : ℂ))
    simpa [S, Finset.sum_range_succ] using H.add_const 1
  have hD1 : Tendsto D (𝓝 0) (𝓝 1) := by
    have H := (isBigO_tsum_nat_pow_sub_sum (K := ℂ) (fun n => n ^ 2) 1 1
      (by intro n; nlinarith)).trans_tendsto (by simpa using (continuous_pow 1).tendsto (0 : ℂ))
    have H1 : Tendsto (fun q : ℂ => ∑' n : ℕ, q ^ (n ^ 2)) (𝓝 0) (𝓝 1) := by
      simpa [Finset.sum_range_succ] using H.add_const 1
    convert ((tendsto_const_nhds (x := (2 : ℂ))).mul H1).sub_const (1 : ℂ) using 1 ;
      norm_num [D]
  have hS₀ : Tendsto S₀ (𝓝 0) (𝓝 1) := by
    have hc : Continuous S₀ := by dsimp only [S₀]; fun_prop
    convert hc.tendsto 0 using 1 ; norm_num [S₀]
  have hD₀ : Tendsto D₀ (𝓝 0) (𝓝 1) := by
    have hc : Continuous D₀ := by dsimp only [D₀]; fun_prop
    convert hc.tendsto 0 using 1 ; norm_num [D₀]
  have hSF : (fun q => S q ^ 3 + S q ^ 2 * S₀ q + S q * S₀ q ^ 2 + S₀ q ^ 3)
      =O[𝓝 0] fun _ => (1 : ℂ) :=
    (((hS1.pow 3).add ((hS1.pow 2).mul hS₀)).add
      (hS1.mul (hS₀.pow 2)) |>.add (hS₀.pow 3)).isBigO_one ℂ
  have hDF : (fun q => D q ^ 3 + D q ^ 2 * D₀ q + D q * D₀ q ^ 2 + D₀ q ^ 3)
      =O[𝓝 0] fun _ => (1 : ℂ) :=
    (((hD1.pow 3).add ((hD1.pow 2).mul hD₀)).add
      (hD1.mul (hD₀.pow 2)) |>.add (hD₀.pow 3)).isBigO_one ℂ
  have hS4 : (fun q => S q ^ 4 - S₀ q ^ 4) =O[𝓝 0] fun q => q ^ 4 := by
    convert hS.mul hSF using 1 <;> funext q <;> ring
  have hD4 : (fun q => D q ^ 4 - D₀ q ^ 4) =O[𝓝 0] fun q => q ^ 4 := by
    convert hD.mul hDF using 1 <;> funext q <;> ring
  have hP : P =O[𝓝 0] fun q : ℂ => q := by
    have H : (fun q : ℂ => 1 - 8 * q + 44 * q ^ 2 - 192 * q ^ 3) =O[𝓝 0]
        fun _ => (1 : ℂ) := by
      have ht : Tendsto (fun q : ℂ => 1 - 8 * q + 44 * q ^ 2 - 192 * q ^ 3)
          (𝓝 0) (𝓝 1) := by
        convert ((by fun_prop : Continuous (fun q : ℂ =>
          1 - 8 * q + 44 * q ^ 2 - 192 * q ^ 3)).tendsto 0) using 1 ; norm_num
      exact ht.isBigO_one ℂ
    convert (isBigO_refl (fun q : ℂ => q) (𝓝 0)).mul H using 1 <;>
      funext q <;> (try dsimp only [P]) <;> ring
  have hpoly : (fun q : ℂ => q * S₀ q ^ 4 - D₀ q ^ 4 * P q) =O[𝓝 0]
      fun q => q ^ 5 := by
    have H : (fun q : ℂ => q ^ 4 + 3072 * q ^ 3 + 5444 * q ^ 2 + 3328 * q + 726)
        =O[𝓝 0] fun _ => (1 : ℂ) := by
      have ht : Tendsto (fun q : ℂ =>
          q ^ 4 + 3072 * q ^ 3 + 5444 * q ^ 2 + 3328 * q + 726) (𝓝 0) (𝓝 726) := by
        convert ((by fun_prop : Continuous (fun q : ℂ =>
          q ^ 4 + 3072 * q ^ 3 + 5444 * q ^ 2 + 3328 * q + 726)).tendsto 0)
          using 1 ; norm_num
      exact ht.isBigO_one ℂ
    convert (isBigO_refl (fun q : ℂ => q ^ 5) (𝓝 0)).mul H using 1 <;>
      funext q <;> (try dsimp only [S₀, D₀, P]) <;> ring
  have hnum : (fun q => q * S q ^ 4 - D q ^ 4 * P q) =O[𝓝 0] fun q => q ^ 5 := by
    have H1 : (fun q => q * (S q ^ 4 - S₀ q ^ 4)) =O[𝓝 0] fun q => q ^ 5 := by
      simpa only [← pow_succ', Nat.reduceAdd] using
        (isBigO_refl (fun q : ℂ => q) (𝓝 0)).mul hS4
    have H2 : (fun q => (D q ^ 4 - D₀ q ^ 4) * P q) =O[𝓝 0] fun q => q ^ 5 := by
      simpa only [← pow_succ, Nat.reduceAdd] using hD4.mul hP
    convert (H1.sub H2).add hpoly using 1 ; funext q ; ring
  have hinv : (fun q => (D q ^ 4)⁻¹) =O[𝓝 0] fun _ => (1 : ℂ) :=
    ((hD1.pow 4).inv₀ (by norm_num)).isBigO_one ℂ
  have hn : ∀ᶠ q in 𝓝 (0 : ℂ), D q ≠ 0 :=
    hD1.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)
  apply (hnum.mul hinv).congr'
  · filter_upwards [hn] with q hq
    dsimp only [D] at hq
    dsimp only [S, D, P]
    field_simp [hq]
  · filter_upwards [] with q
    simp
end DLMF.EllipticIntegrals

namespace DLMF.EllipticIntegrals
open DLMF.JacobiElliptic
/-- DLMF 19.5.5: Jacobi's nome `q = exp(-πK'(k)/K(k)) = r + 8r² + 84r³ + 992r⁴ + ⋯`
with `r = k²/16`, as `k → 0+` (the remainder is `O(r⁵)`). -/
@[dlmf 19.5.E5]
public theorem jacobiNome_isBigO :
    (fun k : ℝ => jacobiNome k - ((k ^ 2 / 16 : ℝ) + 8 * (k ^ 2 / 16 : ℝ) ^ 2 +
        84 * (k ^ 2 / 16 : ℝ) ^ 3 + 992 * (k ^ 2 / 16 : ℝ) ^ 4 : ℂ)) =O[𝓝[>] 0]
      fun k : ℝ => (k ^ 2 / 16) ^ 5 := by
  let q : ℝ → ℂ := fun k => jacobiNome k
  let r : ℝ → ℂ := fun k => ((k ^ 2 / 16 : ℝ) : ℂ)
  let p : ℝ → ℂ := fun k => q k - 8 * q k ^ 2 + 44 * q k ^ 3 - 192 * q k ^ 4
  have hq : Tendsto q (𝓝[>] 0) (𝓝 0) := Real.tendsto_jacobiNome_zero
  have hr : Tendsto r (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous r := by dsimp only [r]; fun_prop
    simpa [r] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hp : Tendsto p (𝓝[>] 0) (𝓝 0) := by
    have H := ((hq.sub ((tendsto_const_nhds (x := (8 : ℂ))).mul (hq.pow 2))).add
      ((tendsto_const_nhds (x := (44 : ℂ))).mul (hq.pow 3))).sub
        ((tendsto_const_nhds (x := (192 : ℂ))).mul (hq.pow 4))
    simpa only [mul_zero, sub_zero, add_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0)] using H
  have hforward : (fun k => r k - p k) =O[𝓝[>] 0] fun k => q k ^ 5 := by
    apply (nome_forward_remainder.comp_tendsto hq).congr'
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1),
        hq.eventually (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1))]
        with k hk hkq
      have H := jacobiNome_theta_series_relation (ofReal_mem_jacobiModulusDomain hk.1 hk.2)
        (by simpa only [Metric.mem_ball, dist_zero_right] using hkq)
      dsimp only [q, r, p]
      push_cast
      rw [H]
      rfl
    · exact Eventually.of_forall fun _ => rfl
  have hfactor : (fun k => 1 + 8 * (r k + p k) +
      84 * (r k ^ 2 + r k * p k + p k ^ 2) +
      992 * (r k ^ 3 + r k ^ 2 * p k + r k * p k ^ 2 + p k ^ 3)) =O[𝓝[>] 0]
        fun _ => (1 : ℂ) := by
    have H := (((tendsto_const_nhds (x := (1 : ℂ))).add
      ((tendsto_const_nhds (x := (8 : ℂ))).mul (hr.add hp))).add
      ((tendsto_const_nhds (x := (84 : ℂ))).mul
        (((hr.pow 2).add (hr.mul hp)).add (hp.pow 2)))).add
      ((tendsto_const_nhds (x := (992 : ℂ))).mul
        ((((hr.pow 3).add ((hr.pow 2).mul hp)).add (hr.mul (hp.pow 2))).add (hp.pow 3)))
    exact H.isBigO_one ℂ
  have hinverse : (fun k =>
      (r k + 8 * r k ^ 2 + 84 * r k ^ 3 + 992 * r k ^ 4) -
      (p k + 8 * p k ^ 2 + 84 * p k ^ 3 + 992 * p k ^ 4)) =O[𝓝[>] 0]
        fun k => q k ^ 5 := by
    convert hforward.mul hfactor using 1 <;> funext k <;> ring
  have hpoly : (fun z : ℂ =>
      ((z - 8 * z ^ 2 + 44 * z ^ 3 - 192 * z ^ 4) +
        8 * (z - 8 * z ^ 2 + 44 * z ^ 3 - 192 * z ^ 4) ^ 2 +
        84 * (z - 8 * z ^ 2 + 44 * z ^ 3 - 192 * z ^ 4) ^ 3 +
        992 * (z - 8 * z ^ 2 + 44 * z ^ 3 - 192 * z ^ 4) ^ 4) - z)
      =O[𝓝 0] fun z => z ^ 5 := by
    let Q : ℂ → ℂ := fun z =>
      1348082860032 * z ^ 11 - 1235742621696 * z ^ 10 + 649467002880 * z ^ 9 -
      247450828800 * z ^ 8 + 71873454080 * z ^ 7 - 16666984448 * z ^ 6 +
      3126022144 * z ^ 5 - 470094080 * z ^ 4 + 56430080 * z ^ 3 - 5147200 * z ^ 2 +
      326784 * z - 13232
    have hQ : Q =O[𝓝 0] fun _ => (1 : ℂ) :=
      ((by dsimp only [Q]; fun_prop : Continuous Q).tendsto 0).isBigO_one ℂ
    convert (isBigO_refl (fun z : ℂ => z ^ 5) (𝓝 0)).mul hQ using 1 <;>
      funext z <;> (try dsimp only [Q]) <;> ring
  have H : (fun k => q k - (r k + 8 * r k ^ 2 + 84 * r k ^ 3 + 992 * r k ^ 4))
      =O[𝓝[>] 0] fun k => q k ^ 5 := by
    convert (hinverse.add (hpoly.comp_tendsto hq)).neg_left using 1 ;
      funext k ; (dsimp only [p, Function.comp_def]) ; ring
  have Hfinal := H.trans (Real.jacobiNome_isBigO_sq_div_sixteen.pow 5)
  apply IsBigO.of_norm_right
  simpa only [r, q, norm_pow, norm_real] using Hfinal.norm_right
end DLMF.EllipticIntegrals
