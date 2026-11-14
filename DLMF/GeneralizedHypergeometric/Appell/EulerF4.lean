/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.GeneralizedHypergeometric.Appell.Basic.EulerBranches
public import DLMF.Hypergeometric.Basic.CutPlane
import DLMF.GeneralizedHypergeometric.Appell.BurchnallChaundy
import DLMFMathlib.Analysis.Integral.WeightedSeries
import Mathlib.MeasureTheory.Integral.Prod
public import DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuationExistence
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Euler moments and the separated Appell F4 kernel

The transformed Euler kernel in DLMF 16.15.4 separates into two Gauss Euler kernels and a
binomial cross-ratio factor. A small bidisc keeps all principal complex powers on compatible
branches. The normalized Gauss moments shift the two upper parameters and the denominator
parameter by the same natural number.

The factorization uses TauCeti's `mul_cpow_of_re_pos`, and the moments use the project's
proved Euler integral for the Gauss hypergeometric function.

* `integral_eulerWeight_mul_div_pow`: normalized shifted Gauss Euler moments.
* `integrableOn_eulerWeight_mul_div_pow`: integrability of those moments.
* `F4EulerSeries.norm_crossRatio_lt`: a uniform bound on the unit square.
* `F4EulerSeries.kernel_split`: the branch-compatible kernel factorization.
* `F4EulerSeries.euler_germ`: the Euler integral represents the composed F4 germ.
-/

public noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Nat
namespace DLMF.Hypergeometric
/-- A shifted Euler moment is a Gauss function with equally shifted parameters. -/
lemma integral_eulerWeight_mul_div_pow {a b c X : ℂ} (ha : 0 < a.re)
    (hca : 0 < (c - a).re) (hX : ‖X‖ < 1) (k : ℕ) :
    Gamma c / (Gamma a * Gamma (c - a)) *
      (∫ t : ℝ in Icc (0 : ℝ) 1, eulerWeight a c t * (1 - t * X) ^ (-b) *
        ((t : ℂ) / (1 - t * X)) ^ k) =
      pochhammer a k / pochhammer c k * ₂F₁ (b + k) (a + k) (c + k) X := by
  have hc : 0 < c.re := by simp only [sub_re] at hca;linarith
  have hak : 0 < (a + (k : ℂ)).re := by simp only [add_re,natCast_re];positivity
  have hck : 0 < (c + (k : ℂ) - (a + k)).re := by
    rwa [show c + (k : ℂ) - (a + k) = c - a by ring]
  have heq : (∫ t : ℝ in Icc (0 : ℝ) 1,
      eulerWeight a c t * (1 - t * X) ^ (-b) * ((t : ℂ) / (1 - t * X)) ^ k) =
      ∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (a + k - 1) *
        (1 - (t : ℂ)) ^ ((c + k) - (a + k) - 1) * (1 - X * t) ^ (-(b + k)) := by
    rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le zero_le_one]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    have htx : ‖(t : ℂ) * X‖ < 1 := by
      rw [norm_mul,norm_real,Real.norm_eq_abs,abs_of_pos ht.1]
      nlinarith [norm_nonneg X,ht.2]
    have hA0 : 1 - (t : ℂ) * X ≠ 0 := by
      intro h
      have he : (t : ℂ) * X = 1 := by linear_combination -h
      rw [he,norm_one] at htx
      exact lt_irrefl _ htx
    simp only [eulerWeight,div_pow]
    rw [← cpow_natCast (t : ℂ) k,← cpow_natCast (1 - t * X) k,
      show (c + (k : ℂ)) - (a + k) - 1 = c - a - 1 by ring,show X * t = (t : ℂ) * X by ring,
      div_eq_mul_inv,← cpow_neg]
    calc (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (c - a - 1) * (1 - t * X) ^ (-b) *
        ((t : ℂ) ^ (k : ℂ) * (1 - t * X) ^ (-(k : ℂ))) =
        ((t : ℂ) ^ (a - 1) * (t : ℂ) ^ (k : ℂ)) * (1 - (t : ℂ)) ^ (c - a - 1) *
          ((1 - t * X) ^ (-b) * (1 - t * X) ^ (-(k : ℂ))) := by ring
      _ = _ := by
        rw [← cpow_add _ _ ht0,← cpow_add _ _ hA0]
        rw [show a - 1 + (k : ℂ) = a + k - 1 by ring,show -b + -(k : ℂ)=-(b + k) by ring]
  have hg := ordinaryHypergeometric_eq_integral (a := b + k) hak hck hX
  rw [show c + (k : ℂ) - (a + k) = c - a by ring] at hg
  rw [heq,hg,Gamma_add_nat_eq_pochhammer_mul_Gamma ha k,
    Gamma_add_nat_eq_pochhammer_mul_Gamma hc k]
  have hGa := Gamma_ne_zero (not_neg_nat_of_re_pos ha)
  have hGc := Gamma_ne_zero (not_neg_nat_of_re_pos hc)
  have hGca := Gamma_ne_zero (not_neg_nat_of_re_pos hca)
  have hpa := pochhammer_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos ha) k
  have hpc := pochhammer_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hc) k
  field_simp [hGa, hGc, hGca, hpa, hpc]
  congr 1
  funext t
  rw [show c + (k : ℂ) - (a + k) - 1 = c - a - 1 by ring,mul_comm (t : ℂ) X]

/-- Shifted Gauss Euler moments are integrable on the closed unit interval. -/
lemma integrableOn_eulerWeight_mul_div_pow {a b c X : ℂ} (ha : 0 < a.re)
    (hca : 0 < (c - a).re) (hX : ‖X‖ < 1) (k : ℕ) :
    IntegrableOn (fun t : ℝ => eulerWeight a c t * (1 - t * X) ^ (-b) *
      ((t : ℂ) / (1 - t * X)) ^ k) (Icc (0 : ℝ) 1) := by
  have hw : IntegrableOn (fun t : ℝ => eulerWeight a c t) (Icc (0 : ℝ) 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc,
      ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact intervalIntegrable_eulerWeight ha hca
  have hbase : ContinuousOn (fun t : ℝ => 1 - (t : ℂ) * X) (Icc (0 : ℝ) 1) := by fun_prop
  have hslit : ∀ t ∈ Icc (0 : ℝ) 1, 1 - (t : ℂ) * X ∈ slitPlane := by
    intro t ht
    have hn : ‖(t : ℂ) * X‖ ≤ ‖X‖ := by
      rw [norm_mul,norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    left
    simp only [sub_re,one_re]
    linarith [re_le_norm ((t : ℂ) * X)]
  have hrat : ContinuousOn (fun t : ℝ => (t : ℂ) / (1 - t * X)) (Icc (0 : ℝ) 1) :=
    continuous_ofReal.continuousOn.div hbase (fun t ht => slitPlane_ne_zero (hslit t ht))
  simpa only [Pi.mul_apply,Pi.pow_apply,mul_assoc] using hw.mul_continuousOn
    ((hbase.cpow_const hslit).mul (hrat.pow k)) isCompact_Icc

namespace F4EulerSeries

/-- The cross ratio in the binomial expansion of the F4 Euler kernel. -/
def crossRatio (X Y : ℂ) (q : ℝ × ℝ) : ℂ :=
  ((q.1 : ℂ) * X) * ((q.2 : ℂ) * Y) / ((1 - q.1 * X) * (1 - q.2 * Y))

/-- The defining rational expression for the kernel cross ratio. -/
lemma crossRatio_def (X Y : ℂ) (q : ℝ × ℝ) :
    crossRatio X Y q = ((q.1 : ℂ) * X) * ((q.2 : ℂ) * Y) / ((1 - q.1 * X) * (1 - q.2 * Y)) := by rfl

/-- The kernel cross ratio lies uniformly in the one-quarter disk on a small bidisc. -/
lemma norm_crossRatio_lt {X Y : ℂ} (hX : ‖X‖ < 1 / 8) (hY : ‖Y‖ < 1 / 8)
    {q : ℝ × ℝ} (hq : q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    ‖crossRatio X Y q‖ < 1 / 4 := by
  let U : ℂ := q.1 * X
  let V : ℂ := q.2 * Y
  let A : ℂ := 1 - U
  let B : ℂ := 1 - V
  have hU : ‖U‖ < 1 / 8 := by
    dsimp only [U]
    rw [norm_mul,norm_real,Real.norm_eq_abs,abs_of_nonneg hq.1.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hq.1.2).trans_lt hX
  have hV : ‖V‖ < 1 / 8 := by
    dsimp only [V]
    rw [norm_mul,norm_real,Real.norm_eq_abs,abs_of_nonneg hq.2.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hq.2.2).trans_lt hY
  have hAre : 0 < A.re := by dsimp [A];linarith [re_le_norm U]
  have hBre : 0 < B.re := by dsimp [B];linarith [re_le_norm V]
  have hA0 : A ≠ 0 := ne_zero_of_re_pos hAre
  have hB0 : B ≠ 0 := ne_zero_of_re_pos hBre
  have hAN : 1-‖U‖ ≤ ‖A‖ := by simpa [A] using norm_sub_norm_le (1 : ℂ) U
  have hBN : 1-‖V‖ ≤ ‖B‖ := by simpa [B] using norm_sub_norm_le (1 : ℂ) V
  have hABN : (1-‖U‖) * (1-‖V‖) ≤ ‖A‖*‖B‖ :=
    mul_le_mul hAN hBN (by linarith) (by positivity)
  have heq : crossRatio X Y q = U * V / (A * B) := by rfl
  rw [heq,norm_div,norm_mul U V,norm_mul A B,
    div_lt_iff₀ (mul_pos (norm_pos_iff.mpr hA0) (norm_pos_iff.mpr hB0))]
  nlinarith [norm_nonneg U, norm_nonneg V,
    mul_pos (sub_pos.mpr hU) (sub_pos.mpr hV)]

/-- The F4 kernel separates into two Gauss kernels and a binomial cross-ratio factor. -/
lemma kernel_split (a b c c' : ℂ) {X Y : ℂ} (hX : ‖X‖ < 1 / 8) (hY : ‖Y‖ < 1 / 8)
    {q : ℝ × ℝ} (hq : q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    appellF4EulerKernel a b c c' X Y q =
      eulerWeight a c q.1 * eulerWeight b c' q.2 *
        (1 - q.1 * X) ^ (-b) * (1 - q.2 * Y) ^ (-a) *
        (1 - crossRatio X Y q) ^ (-(a + b - c - c'+1)) := by
  let U : ℂ := q.1 * X
  let V : ℂ := q.2 * Y
  let A : ℂ := 1 - U
  let B : ℂ := 1 - V
  let R : ℂ := U * V / (A * B)
  have hU : ‖U‖ < 1 / 8 := by
    dsimp only [U]
    rw [norm_mul,norm_real,Real.norm_eq_abs,abs_of_nonneg hq.1.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hq.1.2).trans_lt hX
  have hV : ‖V‖ < 1 / 8 := by
    dsimp only [V]
    rw [norm_mul,norm_real,Real.norm_eq_abs,abs_of_nonneg hq.2.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hq.2.2).trans_lt hY
  have hAre : 0 < A.re := by dsimp [A]; linarith [re_le_norm U]
  have hBre : 0 < B.re := by dsimp [B]; linarith [re_le_norm V]
  have hA0 : A ≠ 0 := ne_zero_of_re_pos hAre
  have hB0 : B ≠ 0 := ne_zero_of_re_pos hBre
  have hRN : ‖R‖ < 1 / 4 := norm_crossRatio_lt hX hY hq
  have hWre : 0 < (1 - R).re := by simp only [sub_re,one_re]; linarith [re_le_norm R]
  have hABnear : ‖A * B - 1‖ < 1 := by
    have heq : A * B - 1 = -(U + V - U * V) := by dsimp [A,B];ring
    rw [heq,norm_neg]
    have hb := (norm_sub_le (U + V) (U * V)).trans
      (add_le_add (norm_add_le U V) (le_refl ‖U * V‖))
    rw [norm_mul U V] at hb
    nlinarith [norm_nonneg U, norm_nonneg V,
      mul_pos (sub_pos.mpr hU) (sub_pos.mpr hV)]
  have hABre : 0 < (A * B).re := by
    have hh := re_le_norm (1 - A * B)
    rw [norm_sub_rev] at hh
    simp only [sub_re,one_re] at hh
    linarith
  have hCeq : 1 - U - V = (A * B) * (1 - R) := by
    dsimp only [R]
    field_simp [mul_ne_zero hA0 hB0]
    dsimp only [A,B]
    ring
  have hid : A ^ (-(c + c'-a - 1)) * B ^ (-(c + c'-b - 1)) *
      (1 - U - V) ^ (-(a + b - c - c'+1)) =
        A ^ (-b) * B ^ (-a) * (1 - R) ^ (-(a + b - c - c'+1)) := by
    rw [hCeq,TauCeti.mul_cpow_of_re_pos hABre hWre,
      TauCeti.mul_cpow_of_re_pos hAre hBre]
    calc A ^ (-(c + c'-a - 1)) * B ^ (-(c + c'-b - 1)) *
        (A ^ (-(a + b - c - c'+1)) * B ^ (-(a + b - c - c'+1)) *
          (1 - R) ^ (-(a + b - c - c'+1))) =
        (A ^ (-(c + c'-a - 1)) * A ^ (-(a + b - c - c'+1))) *
          (B ^ (-(c + c'-b - 1)) * B ^ (-(a + b - c - c'+1))) *
          (1 - R) ^ (-(a + b - c - c'+1)) := by ring
      _ = _ := by
        rw [← cpow_add _ _ hA0, ← cpow_add _ _ hB0]
        rw [show -(c + c'-a - 1) + -(a + b - c - c'+1) = -b by ring,
          show -(c + c'-b - 1) + -(a + b - c - c'+1) = -a by ring]
  calc appellF4EulerKernel a b c c' X Y q =
      (eulerWeight a c q.1 * eulerWeight b c' q.2) *
        (A ^ (-(c + c'-a - 1)) * B ^ (-(c + c'-b - 1)) *
          (1 - U - V) ^ (-(a + b - c - c'+1))) := by
        dsimp [appellF4EulerKernel,eulerWeight,A,B,U,V]
        simp only [ofReal_sub,ofReal_one,cpow_neg,div_eq_mul_inv]
        ring
    _ = _ := by rw [hid];dsimp [crossRatio, A, B, U, V, R];ring

/-- The separated two-variable moment is a product of shifted Gauss functions. -/
lemma integral_moment (a b c c' X Y : ℂ) (ha : 0 < a.re) (hb : 0 < b.re)
    (hca : 0 < (c - a).re) (hcb : 0 < (c'-b).re) (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) (k : ℕ) :
    Gamma c * Gamma c' / (Gamma a * Gamma b * Gamma (c - a) * Gamma (c'-b)) *
      (∫ q : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        eulerWeight a c q.1 * eulerWeight b c' q.2 *
          (1 - q.1 * X) ^ (-b) * (1 - q.2 * Y) ^ (-a) * crossRatio X Y q ^ k) =
      pochhammer a k * pochhammer b k / (pochhammer c k * pochhammer c' k) *
        X ^ k * Y ^ k * ₂F₁ (a + k) (b + k) (c + k) X * ₂F₁ (a + k) (b + k) (c'+k) Y := by
  let f : ℝ → ℂ := fun t => eulerWeight a c t * (1 - t * X) ^ (-b) * ((t : ℂ) / (1 - t * X)) ^ k
  let g : ℝ → ℂ := fun t => eulerWeight b c' t * (1 - t * Y) ^ (-a) * ((t : ℂ) / (1 - t * Y)) ^ k
  have heq : (fun q : ℝ × ℝ => eulerWeight a c q.1 * eulerWeight b c' q.2 *
      (1 - q.1 * X) ^ (-b) * (1 - q.2 * Y) ^ (-a) * crossRatio X Y q ^ k) =
      fun q => (X ^ k * Y ^ k) * (f q.1 * g q.2) := by
    funext q
    rw [crossRatio_def]
    simp only [f, g,mul_pow,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [heq,integral_const_mul,Measure.volume_eq_prod,setIntegral_prod_mul]
  have hx := integral_eulerWeight_mul_div_pow (a := a) (b := b) ha hca hX k
  have hy := integral_eulerWeight_mul_div_pow (a := b) (b := a) hb hcb hY k
  rw [ordinaryHypergeometric_symm (b + k) (a + k) (c + k)] at hx
  calc Gamma c * Gamma c' / (Gamma a * Gamma b * Gamma (c - a) * Gamma (c'-b)) *
        (X ^ k * Y ^ k * ((∫ t in Icc (0 : ℝ) 1, f t) * ∫ t in Icc (0 : ℝ) 1, g t)) =
      (Gamma c / (Gamma a * Gamma (c - a)) * ∫ t in Icc (0 : ℝ) 1, f t) *
        (Gamma c' / (Gamma b * Gamma (c'-b)) * ∫ t in Icc (0 : ℝ) 1, g t) * X ^ k * Y ^ k := by
          ring
    _ = _ := by rw [hx, hy];ring

/-- Termwise integration of the binomial cross-ratio expansion gives the Gauss-product series. -/
lemma hasSum_kernel_integral (a b c c' X Y : ℂ) (ha : 0 < a.re) (hb : 0 < b.re)
    (hca : 0 < (c - a).re) (hcb : 0 < (c'-b).re)
    (hX : ‖X‖ < 1 / 8) (hY : ‖Y‖ < 1 / 8) :
    HasSum (fun k : ℕ => pochhammer a k * pochhammer b k * pochhammer (a + b - c - c'+1) k /
      (pochhammer c k * pochhammer c' k * k !) * X ^ k * Y ^ k *
        ₂F₁ (a + k) (b + k) (c + k) X * ₂F₁ (a + k) (b + k) (c'+k) Y)
      (appellF4Euler a b c c' X Y) := by
  let S : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  let E : ℂ := a + b - c - c'+1
  let N : ℂ := Gamma c * Gamma c' / (Gamma a * Gamma b * Gamma (c - a) * Gamma (c'-b))
  let w : ℝ × ℝ → ℂ := fun q => eulerWeight a c q.1 * eulerWeight b c' q.2 *
    (1 - q.1 * X) ^ (-b) * (1 - q.2 * Y) ^ (-a)
  let d : ℕ → ℂ := fun k => pochhammer E k / (k ! : ℂ) * (1 / 4 : ℂ) ^ k
  let e : ℕ → ℝ × ℝ → ℂ := fun k q => (4 * crossRatio X Y q) ^ k
  let g : ℝ × ℝ → ℂ := fun q => (1 - crossRatio X Y q) ^ (-E)
  have hX1 : ‖X‖ < 1 := by linarith
  have hY1 : ‖Y‖ < 1 := by linarith
  have hw1 := integrableOn_eulerWeight_mul_div_pow (a := a) (b := b) ha hca hX1 0
  have hw2 := integrableOn_eulerWeight_mul_div_pow (a := b) (b := a) hb hcb hY1 0
  simp only [pow_zero,mul_one] at hw1 hw2
  have hw : Integrable w (volume.restrict S) := by
    have heq : w = fun q : ℝ × ℝ =>
      (eulerWeight a c q.1 * (1 - q.1 * X) ^ (-b)) *
        (eulerWeight b c' q.2 * (1 - q.2 * Y) ^ (-a)) := by funext q;dsimp [w];ring
    rw [heq]
    dsimp only [S]
    rw [Measure.volume_eq_prod,← Measure.prod_restrict]
    exact hw1.mul_prod hw2
  have hd : Summable (fun k => ‖d k‖) :=
    (hasSum_pochhammer_div_factorial (β := E) (z := (1 / 4 : ℂ)) (by norm_num)).summable.norm
  have he (k : ℕ) : AEStronglyMeasurable (e k) (volume.restrict S) := by
    dsimp only [e]
    simp only [crossRatio_def]
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hbd (k : ℕ) : ∀ᵐ q ∂volume.restrict S, ‖e k q‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem hS] with q hq
    have hr := norm_crossRatio_lt hX hY hq
    dsimp only [e]
    rw [norm_pow,norm_mul,show ‖(4 : ℂ)‖=(4 : ℝ) by norm_num]
    exact pow_le_one₀ (by positivity) (by linarith)
  have hg : ∀ᵐ q ∂volume.restrict S, HasSum (fun k => d k * e k q) (g q) := by
    filter_upwards [ae_restrict_mem hS] with q hq
    have hr := norm_crossRatio_lt hX hY hq
    have hh := hasSum_pochhammer_div_factorial (β := E)
      (by linarith : ‖crossRatio X Y q‖ < 1)
    refine hh.congr_fun fun k => ?_
    have hc4 : (1 / 4 : ℂ) ^ k * (4 : ℂ) ^ k = 1 := by rw [← mul_pow];norm_num
    dsimp only [d, e]
    rw [mul_pow]
    calc _ = (pochhammer E k / (k ! : ℂ)) *
        (((1 / 4 : ℂ) ^ k * (4 : ℂ) ^ k) * crossRatio X Y q ^ k) := by ring
      _ = _ := by rw [hc4,one_mul]
  have hs := (hasSum_integral_mul_of_norm_le_one hw hd he hbd hg).mul_left N
  have hi : (∫ q, w q * g q ∂volume.restrict S) =
      ∫ q in S, appellF4EulerKernel a b c c' X Y q := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hS] with q hq
    rw [kernel_split a b c c' hX hY hq]
  rw [hi] at hs
  have hv : N * (∫ q in S, appellF4EulerKernel a b c c' X Y q) =
      appellF4Euler a b c c' X Y := by rfl
  rw [hv] at hs
  refine hs.congr_fun fun k => ?_
  have he4 : (fun q => w q * e k q) =
      fun q => (4 : ℂ) ^ k * (w q * crossRatio X Y q ^ k) := by
    funext q
    dsimp only [e]
    rw [mul_pow]
    ring
  have hc4 : (1 / 4 : ℂ) ^ k * (4 : ℂ) ^ k = 1 := by rw [← mul_pow];norm_num
  have hm := integral_moment a b c c' X Y ha hb hca hcb hX1 hY1 k
  symm
  rw [he4,integral_const_mul]
  dsimp only [d]
  calc _ = (pochhammer E k / (k ! : ℂ)) *
      (N * ∫ q in S, w q * crossRatio X Y q ^ k) * ((1 / 4 : ℂ) ^ k * (4 : ℂ) ^ k) := by ring
    _ = (pochhammer E k / (k ! : ℂ)) * (N * ∫ q in S, w q * crossRatio X Y q ^ k) := by
      rw [hc4,mul_one]
    _ = _ := by rw [hm];dsimp only [E];ring

/-- The transformed F4 series agrees with its Euler double integral as a germ at the origin. -/
lemma euler_germ (a b c c' : ℂ) (ha : 0 < a.re) (hb : 0 < b.re)
    (hca : a.re < c.re) (hcb : b.re < c'.re) :
    (fun p : ℂ × ℂ => appellF4 a b c c' (p.1 * (1 - p.2)) (p.2 * (1 - p.1))) =ᶠ[𝓝 (0,0)]
      (fun p => appellF4Euler a b c c' p.1 p.2) := by
  have hc : AppellRegular c := not_neg_nat_of_re_pos (by linarith)
  have hc' : AppellRegular c' := not_neg_nat_of_re_pos (by linarith)
  obtain ⟨δ, hδ, hBC⟩ := BurchnallChaundy.hasSum_expansion a b c c' hc hc'
  have hδ' : 0 < min δ (1 / 8) := lt_min hδ (by norm_num)
  have hU : {p : ℂ × ℂ | ‖p.1‖ < min δ (1 / 8) ∧ ‖p.2‖ < min δ (1 / 8)} ∈ 𝓝 ((0 : ℂ),(0 : ℂ)) :=
    ((isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)).mem_nhds
      (by simpa using And.intro hδ' hδ')
  filter_upwards [hU] with p hp
  exact (hBC p.1 p.2 (hp.1.trans_le (min_le_left _ _)) (hp.2.trans_le (min_le_left _ _))).unique
    (hasSum_kernel_integral a b c c' p.1 p.2 ha hb (by simpa only [sub_re,sub_pos] using hca)
      (by simpa only [sub_re,sub_pos] using hcb) (hp.1.trans_le (min_le_right _ _))
      (hp.2.trans_le (min_le_right _ _)))

end F4EulerSeries
end DLMF.Hypergeometric
