/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ExpIntegrals.Asymptotics
public import DLMF.ExpIntegrals.Representations
public import DLMFMathlib.Topology.Order.ZeroEnumeration
public import DLMF.ExpIntegrals.TransformTools

/-!
# Zeros, transforms, sums and computational recurrences, DLMF §§6.13–6.18

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.

The transforms, integrals and sums of §§6.14–6.15 are proved with the helpers in
`DLMF/ExpIntegrals/TransformTools.lean`; the sums use Binet's formulas DLMF 5.9.10 and
5.9.15 from `DLMF/Gamma`.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- The unique real zero of Ei. -/
@[dlmf 6.13.E1]
def Real.expIntEiZero  : ℝ :=
  Classical.epsilon (fun x : ℝ => x ≠ 0 ∧ Real.expIntEi x=0)

/-- Positive Ci zeros, indexed from zero. -/
def Real.cosIntZero (k : ℕ) : ℝ :=
  Classical.epsilon (fun x : ℝ => 0 < x ∧ Real.cosInt x=0 ∧ ({y : ℝ | 0 < y ∧ y < x ∧ Real.cosInt y=0} : Set ℝ).ncard=k)

/-- Positive si zeros, indexed from zero. -/
def Real.sinIntTailZero (k : ℕ) : ℝ :=
  Classical.epsilon (fun x : ℝ => 0 < x ∧ Real.sinInt x-π/2=0 ∧ ({y : ℝ | 0 < y ∧ y < x ∧ Real.sinInt y-π/2=0} : Set ℝ).ncard=k)

/-! ### Real zeros of `Ei`, `Ci` and `si`

The signs of `Ci` and `si` at their critical points come from the positivity of the auxiliary
function `f(x) = Ci(x) sin x - si(x) cos x` (DLMF 6.7.13); between consecutive critical points the
functions are strictly monotone, which separates the zeros. -/

/-- The real auxiliary function `f(x) = Ci(x) sin x - si(x) cos x`. -/
lemma ezero_auxF_ofReal {x : ℝ} (hx : 0 < x) :
    expIntAuxF x = ((Real.cosInt x * Real.sin x - (Real.sinInt x - π / 2) * Real.cos x : ℝ) : ℂ) := by
  rw [expIntAuxF, cosInt_ofReal hx, sinIntTail, sinInt_ofReal, ← ofReal_sin, ← ofReal_cos]
  push_cast; ring

/-- `f(x) > 0` for `x > 0`, from the Laplace representation (DLMF 6.7.13). -/
lemma ezero_auxF_pos {x : ℝ} (hx : 0 < x) :
    0 < Real.cosInt x * Real.sin x - (Real.sinInt x - π / 2) * Real.cos x := by
  have h := expIntAuxF_laplace_integral (z := (x : ℂ)) (by simp; linarith)
  rw [ezero_auxF_ofReal hx] at h
  have h' := (Complex.continuous_re.tendsto _).comp h
  simp only [Function.comp_def, ofReal_re] at h'
  set g : ℝ → ℝ := fun t => Real.exp (-x * t) / (t ^ 2 + 1) with hg
  have hcg : Continuous g := by
    refine Continuous.div (by fun_prop) (by fun_prop) fun t => by positivity
  have hre : ∀ R : ℝ, (∫ t in (0 : ℝ)..R, (t : ℂ) ^ 0 * exp (-(x : ℂ) * t) / ((t : ℂ) ^ 2 + 1)).re =
      ∫ t in (0 : ℝ)..R, g t := by
    intro R
    have : (fun t : ℝ => (t : ℂ) ^ 0 * exp (-(x : ℂ) * t) / ((t : ℂ) ^ 2 + 1)) =
        fun t : ℝ => ((g t : ℝ) : ℂ) := by
      funext t; simp only [hg]; push_cast; ring
    rw [this, intervalIntegral.integral_ofReal, ofReal_re]
  simp only [hre] at h'
  have hlow : ∀ R : ℝ, 1 ≤ R → Real.exp (-x) / 2 ≤ ∫ t in (0 : ℝ)..R, g t := by
    intro R hR
    have h1 : ∫ t in (0 : ℝ)..1, g t ≤ ∫ t in (0 : ℝ)..R, g t :=
      intervalIntegral.integral_mono_interval le_rfl zero_le_one hR
        (Eventually.of_forall fun t => by simp only [hg, Pi.zero_apply]; positivity)
        (hcg.intervalIntegrable _ _)
    have h2 : ∫ t in (0 : ℝ)..1, Real.exp (-x) / 2 ≤ ∫ t in (0 : ℝ)..1, g t := by
      refine intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const
        (hcg.intervalIntegrable _ _) fun t ht => ?_
      simp only [hg]
      have he : Real.exp (-x) ≤ Real.exp (-x * t) := Real.exp_le_exp.mpr (by nlinarith [ht.2])
      have ht2 : t ^ 2 + 1 ≤ 2 := by nlinarith [ht.1, ht.2]
      calc Real.exp (-x) / 2 ≤ Real.exp (-x * t) / 2 := by gcongr
        _ ≤ Real.exp (-x * t) / (t ^ 2 + 1) := by
          gcongr
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at h2
    linarith
  have := ge_of_tendsto h' (eventually_atTop.mpr ⟨1, hlow⟩)
  linarith [Real.exp_pos (-x)]

/-- At the points `nπ`, `(-1)^n si(nπ) = -f(nπ)`. -/
lemma ezero_si_nat_mul_pi {n : ℕ} (hn : 1 ≤ n) :
    (-1) ^ n * (Real.sinInt (n * π) - π / 2) < 0 := by
  have hx : 0 < (n : ℝ) * π := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                                  positivity
  have h := ezero_auxF_pos hx
  rw [Real.sin_nat_mul_pi, Real.cos_nat_mul_pi] at h
  linarith

/-- At the points `(m + 1/2)π`, `Ci = (-1)^m f`. -/
lemma ezero_ci_half {m : ℕ} :
    0 < (-1) ^ m * Real.cosInt ((m + 1 / 2) * π) := by
  have hx : 0 < ((m : ℝ) + 1 / 2) * π := by positivity
  have h := ezero_auxF_pos hx
  have hs : Real.sin ((m + 1 / 2) * π) = (-1) ^ m := by
    rw [show ((m : ℝ) + 1 / 2) * π = π / 2 + m * π by ring, Real.sin_add_nat_mul_pi, Real.sin_pi_div_two,
      mul_one]
  have hc : Real.cos ((m + 1 / 2) * π) = 0 := by
    rw [show ((m : ℝ) + 1 / 2) * π = π / 2 + m * π by ring, Real.cos_add_nat_mul_pi, Real.cos_pi_div_two,
      mul_zero]
  rw [hs, hc] at h
  have h1 : ((-1 : ℝ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
  nlinarith

lemma ezero_sinInt_zero : Real.sinInt 0 = 0 := by simp [Real.sinInt]

lemma ezero_si_mono (n : ℕ) :
    StrictMonoOn (fun x => (-1) ^ n * (Real.sinInt x - π / 2)) (Icc (n * π) ((n + 1) * π)) := by
  have hπ := Real.pi_pos
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ fun x hx => ?_
  · exact fun x _ => ((((Real.hasDerivAt_sinInt x).sub_const (π / 2)).const_mul
      ((-1 : ℝ) ^ n)).continuousAt).continuousWithinAt
  · rw [interior_Icc] at hx
    have hx0 : 0 < x := lt_of_le_of_lt (by positivity) hx.1
    rw [(((Real.hasDerivAt_sinInt x).sub_const (π / 2)).const_mul ((-1 : ℝ) ^ n)).deriv,
      Real.sinc_of_ne_zero hx0.ne']
    have hs : (-1) ^ n * Real.sin x > 0 := by
      have hy : Real.sin x = (-1) ^ n * Real.sin (x - n * π) := by
        rw [← Real.sin_add_nat_mul_pi, sub_add_cancel]
      rw [hy, ← mul_assoc, ← mul_pow]; norm_num
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
    rw [mul_div_assoc']
    exact div_pos hs hx0

lemma ezero_si_unique (n : ℕ) :
    ∃! x, x ∈ Ioo ((n : ℝ) * π) ((n + 1 : ℕ) * π) ∧ Real.sinInt x - π / 2 = 0 := by
  have hπ := Real.pi_pos
  have hne : ((-1 : ℝ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hm := ezero_si_mono n
  have hlo : (-1) ^ n * (Real.sinInt (n * π) - π / 2) < 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ezero_sinInt_zero]; linarith
    · exact ezero_si_nat_mul_pi hn
  have hhi : 0 < (-1) ^ n * (Real.sinInt ((n + 1) * π) - π / 2) := by
    have := ezero_si_nat_mul_pi (n := n + 1) (by omega)
    push_cast at this
    rw [pow_succ] at this; linarith
  have hc : ContinuousOn (fun x => (-1) ^ n * (Real.sinInt x - π / 2)) (Icc (n * π) ((n + 1) * π)) :=
    fun x _ => ((((Real.hasDerivAt_sinInt x).sub_const (π / 2)).const_mul
      ((-1 : ℝ) ^ n)).continuousAt).continuousWithinAt
  obtain ⟨x, ⟨hx, hx0⟩, hxu⟩ := zcount_existsUnique_zero (by nlinarith) hc hm hlo hhi
  push_cast
  refine ⟨x, ⟨hx, ?_⟩, fun y ⟨hy, hy0⟩ => hxu y ⟨hy, by simp only [hy0, mul_zero]⟩⟩
  simpa [hne] using hx0

/-- The positive zeros of `si`, separated by the points `nπ`. -/
lemma ezero_si_enum :
    ∃ z : ℕ → ℝ, StrictMono z ∧ (∀ n : ℕ, z n ∈ Ioo ((n : ℝ) * π) (((n + 1 : ℕ) : ℝ) * π)) ∧
      (∀ x, 0 < x → (Real.sinInt x - π / 2 = 0 ↔ ∃ k, z k = x)) ∧
      (∀ k, 0 < z k ∧ Real.sinInt (z k) - π / 2 = 0 ∧
        {y : ℝ | 0 < y ∧ y < z k ∧ Real.sinInt y - π / 2 = 0}.ncard = k) ∧
      ∀ k, Classical.epsilon (fun x : ℝ => 0 < x ∧ Real.sinInt x - π / 2 = 0 ∧
        {y : ℝ | 0 < y ∧ y < x ∧ Real.sinInt y - π / 2 = 0}.ncard = k) = z k := by
  have hπ := Real.pi_pos
  refine zcount_enum (P := fun x => Real.sinInt x - π / 2 = 0) (t := fun n => n * π) (by simp)
    (fun m n h => by simp only; gcongr) (fun x => ⟨⌈x / π⌉₊, ?_⟩)
    ezero_si_unique (fun n h => ?_)
  · have := Nat.le_ceil (x / π)
    rwa [div_le_iff₀ hπ] at this
  · obtain ⟨x, ⟨hx, -⟩, -⟩ := ezero_si_unique n
    have := ezero_si_nat_mul_pi (n := n + 1) (by omega)
    rw [h, mul_zero] at this
    exact lt_irrefl _ this

lemma ezero_cosIntCin_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.cosIntCin x :=
  intervalIntegral.integral_nonneg hx fun t ht =>
    div_nonneg (sub_nonneg.mpr (Real.cos_le_one t)) ht.1

lemma ezero_ci_neg : Real.cosInt (Real.exp (-1)) < 0 := by
  rw [Real.cosInt, Real.log_exp]
  have := ezero_cosIntCin_nonneg (Real.exp_pos (-1)).le
  have := Real.eulerMascheroniConstant_lt_two_thirds
  linarith

lemma ezero_ci_contOn {s : Set ℝ} (hs : ∀ x ∈ s, 0 < x) : ContinuousOn Real.cosInt s :=
  fun x hx => (Real.hasDerivAt_cosInt (hs x hx)).continuousAt.continuousWithinAt

lemma ezero_ci_mono_first : StrictMonoOn Real.cosInt (Ioc 0 (π / 2)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioc _ _) (ezero_ci_contOn fun x hx => hx.1)
    fun x hx => ?_
  rw [interior_Ioc] at hx
  rw [(Real.hasDerivAt_cosInt hx.1).deriv]
  exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩) hx.1

lemma ezero_ci_mono (m : ℕ) :
    StrictMonoOn (fun x => (-1) ^ (m + 1) * Real.cosInt x)
      (Icc ((m + 1 / 2) * π) ((m + 1 + 1 / 2) * π)) := by
  have hπ := Real.pi_pos
  have hpos : ∀ x ∈ Icc (((m : ℝ) + 1 / 2) * π) ((m + 1 + 1 / 2) * π), 0 < x :=
    fun x hx => lt_of_lt_of_le (by positivity) hx.1
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun x hx => (((Real.hasDerivAt_cosInt (hpos x hx)).const_mul _).continuousAt).continuousWithinAt)
    fun x hx => ?_
  have hx0 := hpos x (interior_subset hx)
  rw [interior_Icc] at hx
  rw [((Real.hasDerivAt_cosInt hx0).const_mul _).deriv]
  have hc : 0 < (-1) ^ (m + 1) * Real.cos x := by
    have hy : Real.cos x = (-1) ^ (m + 1) * Real.cos (x - (m + 1 : ℕ) * π) := by
      rw [← Real.cos_add_nat_mul_pi, sub_add_cancel]
    rw [hy, ← mul_assoc, ← mul_pow]; norm_num
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [mul_div_assoc']
  exact div_pos hc hx0

/-- The separating points for the zeros of `Ci`. -/
noncomputable def ezero_ct (n : ℕ) : ℝ := if n = 0 then 0 else (n - 1 / 2) * π

lemma ezero_ct_succ (n : ℕ) : ezero_ct (n + 1) = (n + 1 / 2) * π := by
  simp [ezero_ct]; ring

lemma ezero_ci_unique (n : ℕ) :
    ∃! x, x ∈ Ioo (ezero_ct n) (ezero_ct (n + 1)) ∧ Real.cosInt x = 0 := by
  have hπ := Real.pi_pos
  rcases n with _ | m
  · rw [ezero_ct_succ, show ezero_ct 0 = 0 by simp [ezero_ct]]
    simp only [CharP.cast_eq_zero, zero_add, one_div]
    have he1 : Real.exp (-1) < π / 2 := by
      have := Real.exp_lt_one_iff.mpr (show (-1 : ℝ) < 0 by norm_num)
      linarith [Real.pi_gt_three]
    have hhi : 0 < Real.cosInt (π / 2) := by
      have := ezero_ci_half (m := 0); simpa [div_eq_inv_mul] using this
    obtain ⟨x, ⟨hx, hx0⟩, -⟩ := zcount_existsUnique_zero he1.le
      (ezero_ci_contOn fun x hx => (Real.exp_pos _).trans_le hx.1)
      (ezero_ci_mono_first.mono fun x hx => ⟨(Real.exp_pos _).trans_le hx.1, hx.2⟩)
      ezero_ci_neg hhi
    refine ⟨x, ⟨⟨(Real.exp_pos _).trans hx.1, by rw [← div_eq_inv_mul]; exact hx.2⟩, hx0⟩,
      fun y ⟨hy, hy0⟩ => ezero_ci_mono_first.injOn ⟨hy.1, ?_⟩ ⟨(Real.exp_pos _).trans hx.1,
        hx.2.le⟩ (hy0.trans hx0.symm)⟩
    rw [← div_eq_inv_mul] at hy; exact hy.2.le
  · rw [ezero_ct_succ, ezero_ct_succ]
    have hne : ((-1 : ℝ) ^ (m + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hlo : (-1) ^ (m + 1) * Real.cosInt ((m + 1 / 2) * π) < 0 := by
      have := ezero_ci_half (m := m); rw [pow_succ]; linarith
    have hhi : 0 < (-1) ^ (m + 1) * Real.cosInt ((m + 1 + 1 / 2) * π) := by
      have := ezero_ci_half (m := m + 1); push_cast at this; exact this
    have hπ' : ((m : ℝ) + 1 / 2) * π ≤ (m + 1 + 1 / 2) * π := by nlinarith
    obtain ⟨x, ⟨hx, hx0⟩, hxu⟩ := zcount_existsUnique_zero hπ'
      (fun x hx => (((Real.hasDerivAt_cosInt (lt_of_lt_of_le (by positivity) hx.1)).const_mul
        ((-1 : ℝ) ^ (m + 1))).continuousAt).continuousWithinAt) (ezero_ci_mono m) hlo hhi
    push_cast
    refine ⟨x, ⟨hx, by simpa [hne] using hx0⟩, fun y ⟨hy, hy0⟩ => hxu y ⟨hy, by simp [hy0]⟩⟩

lemma ezero_ci_enum :
    ∃ z : ℕ → ℝ, StrictMono z ∧ (∀ n : ℕ, z n ∈ Ioo (ezero_ct n) (ezero_ct (n + 1))) ∧
      (∀ x, 0 < x → (Real.cosInt x = 0 ↔ ∃ k, z k = x)) ∧
      (∀ k, 0 < z k ∧ Real.cosInt (z k) = 0 ∧
        {y : ℝ | 0 < y ∧ y < z k ∧ Real.cosInt y = 0}.ncard = k) ∧
      ∀ k, Classical.epsilon (fun x : ℝ => 0 < x ∧ Real.cosInt x = 0 ∧
        {y : ℝ | 0 < y ∧ y < x ∧ Real.cosInt y = 0}.ncard = k) = z k := by
  have hπ := Real.pi_pos
  refine zcount_enum (P := fun x => Real.cosInt x = 0) (t := ezero_ct) (by simp [ezero_ct])
    (strictMono_nat_of_lt_succ fun n => ?_) (fun x => ⟨⌈x / π⌉₊ + 1, ?_⟩)
    ezero_ci_unique (fun n h => ?_)
  · rw [ezero_ct_succ]
    rcases n with _ | m
    · simp [ezero_ct]; positivity
    · rw [ezero_ct_succ]; push_cast; nlinarith
  · rw [ezero_ct_succ]
    have := Nat.le_ceil (x / π)
    rw [div_le_iff₀ hπ] at this
    nlinarith
  · have := ezero_ci_half (m := n)
    rw [ezero_ct_succ] at h
    rw [h, mul_zero] at this
    exact lt_irrefl _ this

lemma ezero_ei_eq {x : ℝ} (hx : 0 < x) :
    Real.expIntEi x = Real.eulerMascheroniConstant + Real.log x - Real.expIntEin (-x) := by
  rw [Real.expIntEi, abs_of_pos hx, show -(x : ℂ) = ((-x : ℝ) : ℂ) by push_cast; ring,
    expIntEin_ofReal, ofReal_re]

lemma ezero_hasDerivAt_ein {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt Real.expIntEin ((1 - Real.exp (-t)) / t) t := by
  have h := (hasDerivAt_expIntEin_complex (z := (t : ℂ)) (by exact_mod_cast ht)).real_of_complex
  have hf : (fun y : ℝ => (expIntEin (y : ℂ)).re) = Real.expIntEin := by
    funext y; rw [expIntEin_ofReal, ofReal_re]
  rw [hf] at h
  convert h using 1
  rw [← ofReal_neg, ← ofReal_exp, ← ofReal_one, ← ofReal_sub, ← ofReal_div, ofReal_re]

/-- The negative part of the real axis: `Ei(-y) = -E₁(y) < 0`. -/
lemma ezero_ei_neg {y : ℝ} (hy : 0 < y) : Real.expIntEi (-y) < 0 := by
  have h := Real.expIntEi_negative hy
  rw [genExpIntE_one_eq_integral hy, ← ofReal_neg, ofReal_inj] at h
  rw [h, neg_lt_zero]
  have hint := integrableOn_exp_neg_div hy
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
  · have : Function.support (fun t : ℝ => Real.exp (-t) / t) ∩ Ioi y = Ioi y := by
      ext t
      simp only [mem_inter_iff, Function.mem_support, mem_Ioi, and_iff_right_iff_imp]
      intro ht; exact (div_pos (Real.exp_pos _) (hy.trans ht)).ne'
    rw [this]; simp [Real.volume_Ioi]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (div_pos (Real.exp_pos _) (hy.trans ht)).le

lemma ezero_ei_mono : StrictMonoOn
    (fun x => Real.eulerMascheroniConstant + Real.log x - Real.expIntEin (-x)) (Ioi 0) := by
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt
      (fun x => Real.eulerMascheroniConstant + Real.log x - Real.expIntEin (-x))
      (Real.exp x / x) x := by
    intro x hx
    have h1 := ((ezero_hasDerivAt_ein (t := -x) (by linarith)).comp x (hasDerivAt_neg x))
    have h2 := ((hasDerivAt_const x Real.eulerMascheroniConstant).add (Real.hasDerivAt_log hx.ne')).sub h1
    refine h2.congr_deriv ?_
    rw [neg_neg]; field_simp; ring
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Ioi] at hx
  rw [(hd x hx).deriv]
  exact div_pos (Real.exp_pos _) hx

lemma ezero_ein_neg_series (x : ℝ) :
    HasSum (fun k : ℕ => x ^ (k + 1) / ((k + 1) * (k + 1)!)) (-Real.expIntEin (-x)) := by
  refine (Real.hasSum_expIntEin (-x)).neg.congr_fun fun k => ?_
  have h1 : (-x) ^ (k + 1) = (-1) ^ (k + 1) * x ^ (k + 1) := neg_pow x (k + 1)
  have h2 : ((-1 : ℝ) ^ k) * (-1) ^ (k + 1) = -1 := by
    rw [← pow_add, show k + (k + 1) = 2 * k + 1 by ring, pow_succ, pow_mul]; norm_num
  rw [h1, ← mul_assoc, h2]
  ring

lemma ezero_ei_one_pos :
    0 < Real.eulerMascheroniConstant + Real.log 1 - Real.expIntEin (-1) := by
  have h := (ezero_ein_neg_series 1).nonneg fun k => by positivity
  have := Real.one_half_lt_eulerMascheroniConstant
  rw [Real.log_one]; linarith

lemma ezero_ei_small_neg :
    Real.eulerMascheroniConstant + Real.log (Real.exp (-2)) - Real.expIntEin (-Real.exp (-2)) < 0 := by
  set x := Real.exp (-2)
  have hx0 : 0 < x := Real.exp_pos _
  have hx2 : x ≤ 1 / 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    have h : x * Real.exp 2 = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 2]
  have hle := hasSum_le (fun k => ?_) (ezero_ein_neg_series x) (hasSum_geometric_two.mul_left x)
  · have := Real.eulerMascheroniConstant_lt_two_thirds
    rw [Real.log_exp]; linarith
  · have hk : (1 : ℝ) ≤ (k + 1) * (k + 1)! := by
      have : (1 : ℝ) ≤ (k + 1)! := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    have hp : x ^ (k + 1) ≤ x * (1 / 2) ^ k := by
      rw [pow_succ, mul_comm]; gcongr
    have : 0 ≤ x * (1 / 2) ^ k := by positivity
    nlinarith

/-- **The unique real zero of `Ei`** (DLMF 6.13). -/
lemma ezero_ei_existsUnique : ∃! x : ℝ, x ≠ 0 ∧ Real.expIntEi x = 0 := by
  set E := fun x => Real.eulerMascheroniConstant + Real.log x - Real.expIntEin (-x)
  have hlt : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hc : ContinuousOn E (Icc (Real.exp (-2)) 1) := by
    refine ContinuousOn.sub (continuousOn_const.add (Real.continuousOn_log.mono fun t ht =>
      ((Real.exp_pos _).trans_le ht.1).ne')) fun t ht => ?_
    exact ((ezero_hasDerivAt_ein (t := -t) (by linarith [(Real.exp_pos (-2)).trans_le ht.1])).comp t
      (hasDerivAt_neg t)).continuousAt.continuousWithinAt
  obtain ⟨x, ⟨hx, hx0⟩, -⟩ := zcount_existsUnique_zero hlt.le hc
    (ezero_ei_mono.mono fun t ht => (Real.exp_pos _).trans_le ht.1) ezero_ei_small_neg
    ezero_ei_one_pos
  have hxpos : 0 < x := (Real.exp_pos _).trans hx.1
  refine ⟨x, ⟨hxpos.ne', by rw [ezero_ei_eq hxpos]; exact hx0⟩, fun y ⟨hy0, hy⟩ => ?_⟩
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · have := ezero_ei_neg (y := -y) (by linarith)
    rw [neg_neg, hy] at this; exact absurd this (lt_irrefl _)
  · rw [ezero_ei_eq hpos] at hy
    exact ezero_ei_mono.injOn hpos hxpos (hy.trans hx0.symm)

/-- Real.expIntEi unique zero. -/
theorem Real.expIntEi_unique_zero  :
    Real.expIntEiZero ≠ 0 ∧ Real.expIntEi Real.expIntEiZero=0 ∧ ∀ x : ℝ, x ≠ 0 → Real.expIntEi x=0 → x=Real.expIntEiZero := by
  obtain ⟨x, hx, hu⟩ := ezero_ei_existsUnique
  have hs := Classical.epsilon_spec (p := fun x : ℝ => x ≠ 0 ∧ Real.expIntEi x = 0) ⟨x, hx⟩
  have he : Real.expIntEiZero = x := hu _ hs
  rw [he]
  exact ⟨hx.1, hx.2, fun y hy0 hy => hu y ⟨hy0, hy⟩⟩

/-- Real.cosIntZero spec. -/
theorem Real.cosIntZero_spec (k : ℕ) :
    0 < Real.cosIntZero k ∧ (Real.cosInt) (Real.cosIntZero k)=0 ∧ ({y : ℝ | 0 < y ∧ y < Real.cosIntZero k ∧ (Real.cosInt) y=0} : Set ℝ).ncard=k := by
  obtain ⟨z, -, -, -, hs, he⟩ := ezero_ci_enum
  have hZ : Real.cosIntZero = z := funext he
  rw [hZ]; exact hs k

/-- Real.cosIntZero enumeration. -/
theorem Real.cosIntZero_enumeration  :
    StrictMono Real.cosIntZero ∧ ∀ x : ℝ, 0 < x → ((Real.cosInt) x=0 ↔ ∃ k, Real.cosIntZero k=x) := by
  obtain ⟨z, hm, -, hi, -, he⟩ := ezero_ci_enum
  have hZ : Real.cosIntZero = z := funext he
  rw [hZ]; exact ⟨hm, hi⟩

/-- Real.sinIntTailZero spec. -/
theorem Real.sinIntTailZero_spec (k : ℕ) :
    0 < Real.sinIntTailZero k ∧ (fun x => Real.sinInt x-π/2) (Real.sinIntTailZero k)=0 ∧ ({y : ℝ | 0 < y ∧ y < Real.sinIntTailZero k ∧ (fun x => Real.sinInt x-π/2) y=0} : Set ℝ).ncard=k := by
  obtain ⟨z, -, -, -, hs, he⟩ := ezero_si_enum
  have hZ : Real.sinIntTailZero = z := funext he
  rw [hZ]; exact hs k

/-- Real.sinIntTailZero enumeration. -/
theorem Real.sinIntTailZero_enumeration  :
    StrictMono Real.sinIntTailZero ∧ ∀ x : ℝ, 0 < x → ((fun x => Real.sinInt x-π/2) x=0 ↔ ∃ k, Real.sinIntTailZero k=x) := by
  obtain ⟨z, hm, -, hi, -, he⟩ := ezero_si_enum
  have hZ : Real.sinIntTailZero = z := funext he
  rw [hZ]; exact ⟨hm, hi⟩

/-- Shared all-order zero expansions and signed next-term bounds. -/
@[dlmf 6.13.E2]
theorem Real.trigonometric_integral_zero_asymptotics  :
    ∃ c : ℕ → ℝ, (∀ n < 5, c n=([1,1,-16/3,1673/15,-507746/105] : List ℝ)[n]!) ∧ (∀ aux : Bool, let α := fun k : ℕ => ((k : ℝ)+(if aux then 1/2 else 0))*π; let zero := if aux then Real.sinIntTailZero else Real.cosIntZero; HasAsymptoticExpansion atTop (fun n k => (α k)^(-(2*n : ℤ)+1)) c zero ∧ ∀ k N : ℕ, 1 ≤ k → 1 ≤ N → |zero k-∑ n ∈ Finset.range N, c n*(α k)^(-(2*n : ℤ)+1)| ≤ |c N*(α k)^(-(2*N : ℤ)+1)| ∧ 0 ≤ (zero k-∑ n ∈ Finset.range N, c n*(α k)^(-(2*n : ℤ)+1))*(c N*(α k)^(-(2*N : ℤ)+1))) := by
  sorry

/-- expIntE1 laplace. -/
@[dlmf 6.14.E1]
theorem expIntE1_laplace {a : ℂ} (ha : -1 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*genExpIntE 1 t) = if a=0 then 1 else log (1+a)/a :=
  (eiTr_laplace_E1 ha).2

/-- cosInt laplace. -/
@[dlmf 6.14.E2]
theorem cosInt_laplace {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*cosInt t) = -log (1+a^2)/(2*a) := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  obtain ⟨hE, hEv⟩ := eiTr_laplace_E1 (a := a) (by linarith)
  rw [ite_eq_right_iff.2 (fun h => absurd h ha0)] at hEv
  set F : ℝ → ℝ → ℂ := fun t u => (((Real.cos (t * u) - Real.exp (-(t * u))) / u : ℝ) : ℂ)
  have hFm : Measurable (Function.uncurry F) := by
    simp only [F]; unfold Function.uncurry; fun_prop
  have hFb : ∀ t u : ℝ, 0 < t → u ∈ Ioc (0:ℝ) 1 → ‖F t u‖ ≤ 1 * (1 + t ^ 2) :=
    fun t u ht hu => eiTr_ein_cin_bound ht hu
  have hrep : ∀ t ∈ Ioi (0:ℝ), exp (-a*t)*cosInt t =
      (cexp (-a * t) * ∫ u in (0:ℝ)..1, F t u) - cexp (-a * t) * genExpIntE 1 t := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    simp only [F]
    rw [cosInt_ofReal ht0, genExpIntE_one_eq_Ein ht0, intervalIntegral.integral_ofReal,
      ← eiTr_ein_sub_cin_eq ht0.le, Real.cosInt]
    push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hrep, integral_sub (eiTr_integrable01 ha hFm hFb) hE,
    hEv, eiTr_swap01 ha hFm hFb]
  have hin : ∫ u in (0:ℝ)..1, ∫ t in Ioi (0:ℝ), cexp (-a * t) * F t u =
      ∫ u in (0:ℝ)..1, (a / (a ^ 2 + (u:ℂ) ^ 2) - 1 / (a + u)) / u := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => ?_)
    rw [uIoc_of_le zero_le_one] at hu
    have hu0 : (u:ℂ) ≠ 0 := by exact_mod_cast hu.1.ne'
    have hc : 0 < (a + u).re := by simp; linarith [hu.1]
    have he : ∀ t : ℝ, cexp (-a * t) * F t u =
        (cexp (-a * t) * ((Real.cos (t * u) : ℝ) : ℂ) - cexp (-(a + u) * t)) * (u:ℂ)⁻¹ := by
      intro t
      simp only [F]
      push_cast
      rw [show -(a + u) * (t:ℂ) = -a * t + -(t * u) by ring, Complex.exp_add]
      ring
    simp_rw [he]
    have hcos : IntegrableOn (fun t : ℝ => cexp (-a * t) * ((Real.cos (t * u) : ℝ) : ℂ)) (Ioi 0) := by
      refine (eiTr_integrableOn_exp_neg ha).norm.mono' (by fun_prop) (Eventually.of_forall fun t => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)
    rw [integral_mul_const, integral_sub hcos (eiTr_integrableOn_exp_neg hc), eiTr_laplace_cos ha,
      eiTr_integral_exp_neg hc]
    field_simp
  rw [hin, eiTr_integral_ci_kernel ha]
  field_simp
  ring

/-- sinIntTail laplace. -/
@[dlmf 6.14.E3]
theorem sinIntTail_laplace {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*sinIntTail t) = -arctan a/a := by
  obtain ⟨hi, hv⟩ := eiTr_laplace_sinInt ha
  have he : ∀ t : ℝ, exp (-a*t)*sinIntTail t =
      cexp (-a * t) * (Real.sinInt t : ℂ) - (π / 2 : ℂ) * cexp (-a * t) := fun t => by
    rw [sinIntTail, sinInt_ofReal]; ring
  simp_rw [he]
  rw [integral_sub hi ((eiTr_integrableOn_exp_neg ha).const_mul _), integral_const_mul, hv,
    eiTr_integral_exp_neg ha]
  have : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  field_simp
  ring

/-- expIntE1 squared integral. -/
@[dlmf 6.14.E4]
theorem expIntE1_squared_integral  :
    (∫ t : ℝ in Ioi 0, genExpIntE 1 t^2) = 2*Real.log 2 := by
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ => ((eiTr_e t ^ 2 : ℝ) : ℂ))
    (fun t ht => by rw [eiTr_E1_ofReal (show (0:ℝ) < t from ht)]; push_cast; rfl),
    integral_complex_ofReal, eiTr_integral_e_sq]
  push_cast; ring

/-- cosInt fourier integral. -/
@[dlmf 6.14.E5]
theorem cosInt_fourier_integral  :
    HasIntegralAtTop (fun t : ℝ => cos t*cosInt t) 0 (-π/4) ∧ HasIntegralAtTop (fun t : ℝ => sin t*sinIntTail t) 0 (-π/4) := by
  constructor
  · have h := (continuous_ofReal.tendsto _).comp eiTr_tendsto_integral_cos_mul_cosInt
    unfold HasIntegralAtTop
    rw [show (-π/4 : ℂ) = ((-(π/4) : ℝ) : ℂ) by push_cast; ring]
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with R hR
    rw [Function.comp_apply, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hR] at ht
    rw [cosInt_ofReal ht.1]; push_cast; ring
  · have h := (continuous_ofReal.tendsto _).comp eiTr_tendsto_integral_sin_mul_sinIntTail
    unfold HasIntegralAtTop
    rw [show (-π/4 : ℂ) = ((-(π/4) : ℝ) : ℂ) by push_cast; ring]
    refine h.congr' (Eventually.of_forall fun R => ?_)
    rw [Function.comp_apply, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [sinIntTail, sinInt_ofReal]; push_cast; ring

/-- trigIntegral squared integrals. -/
@[dlmf 6.14.E6]
theorem trigIntegral_squared_integrals  :
    (∫ t : ℝ in Ioi 0, cosInt t^2) = π/2 ∧ (∫ t : ℝ in Ioi 0, sinIntTail t^2) = π/2 := by
  constructor
  · rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ => ((Real.cosInt t ^ 2 : ℝ) : ℂ))
      (fun t ht => by simp only [cosInt_ofReal (show (0:ℝ) < t from ht)]; push_cast; rfl),
      integral_complex_ofReal, eiTr_integral_cosInt_sq]
    push_cast; ring
  · rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun t : ℝ => (((Real.sinInt t - π / 2) ^ 2 : ℝ) : ℂ))
      (fun t _ => by simp only [sinIntTail, sinInt_ofReal]; push_cast; ring),
      integral_complex_ofReal, eiTr_integral_sinIntTail_sq]
    push_cast; ring

/-- trigIntegral product integral. -/
@[dlmf 6.14.E7]
theorem trigIntegral_product_integral  :
    (∫ t : ℝ in Ioi 0, cosInt t*sinIntTail t) = Real.log 2 := by
  rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun t : ℝ => ((Real.cosInt t * (Real.sinInt t - π / 2) : ℝ) : ℂ))
      (fun t ht => by
        simp only [cosInt_ofReal (show (0:ℝ) < t from ht), sinIntTail, sinInt_ofReal]; push_cast; ring),
      integral_complex_ofReal, eiTr_integral_cosInt_mul_sinIntTail]

/-- trigIntegral hasSum 1. -/
@[dlmf 6.15.E1]
theorem trigIntegral_hasSum_1  :
    HasSum (fun n : ℕ => cosInt (π*(n+1 : ℂ))) ((Real.log 2-Real.eulerMascheroniConstant)/2) := by
  have h := eiTr_hasSum_g Real.pi_pos
  rw [eiTr_integral_fermi Real.pi_pos, eiTr_K_eq Real.pi_pos one_pos,
    eiTr_K_eq (by positivity : 0 < 2 * π) one_pos,
    show 1 * π / (2 * π) = 1 / 2 by field_simp, show 1 * (2 * π) / (2 * π) = 1 by field_simp,
    Real.digamma_one_div_two, Real.digamma_one, Real.log_one,
    show Real.log (1 / 2) = -Real.log 2 by rw [one_div, Real.log_inv]] at h
  have h' := Complex.hasSum_ofReal.2 h
  convert h' using 1
  · funext n
    have hx : 0 < π * ((n:ℝ) + 1) := by positivity
    rw [show (π : ℂ) * ((n:ℂ) + 1) = ((π * ((n:ℝ) + 1) : ℝ) : ℂ) by push_cast; ring,
      cosInt_ofReal hx, eiTr_cosInt_of_sin_eq_zero hx (by
        rw [mul_comm, show ((n:ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring]
        exact Real.sin_nat_mul_pi _),
      mul_comm π, show ((n:ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.cos_nat_mul_pi]
    push_cast; ring
  · push_cast; ring

/-- trigIntegral hasSum 2. -/
@[dlmf 6.15.E2]
theorem trigIntegral_hasSum_2  :
    HasSum (fun n : ℕ => sinIntTail (π*(n+1 : ℂ))/(n+1 : ℂ)) (π/2*(Real.log π-1)) := by
  have h := eiTr_hasSum_f Real.pi_pos
  rw [eiTr_integral_log_eq' Real.pi_pos, eiTr_arctanK_eq Real.pi_pos,
    eiTr_arctanK_eq (by positivity : 0 < 2 * π),
    show π / (2 * π) = 1 / 2 by field_simp, show 2 * π / (2 * π) = 1 by field_simp,
    Real.Gamma_one_half_eq, Real.Gamma_one, Real.log_one, Real.log_sqrt Real.pi_pos.le,
    show Real.log (1 / 2) = -Real.log 2 by rw [one_div, Real.log_inv],
    Real.log_mul (by norm_num) Real.pi_pos.ne'] at h
  have h' := Complex.hasSum_ofReal.2 h
  convert h' using 1
  · funext n
    have hx : 0 < π * ((n:ℝ) + 1) := by positivity
    have hn : π * ((n:ℝ) + 1) = ((n + 1 : ℕ) : ℝ) * π := by push_cast; ring
    rw [show (π : ℂ) * ((n:ℂ) + 1) = ((π * ((n:ℝ) + 1) : ℝ) : ℂ) by push_cast; ring,
      sinIntTail, sinInt_ofReal,
      show ((Real.sinInt (π * ((n:ℝ) + 1)) : ℂ) - π / 2) =
        ((Real.sinInt (π * ((n:ℝ) + 1)) - π / 2 : ℝ) : ℂ) by push_cast; ring,
      eiTr_sinIntTail_of_sin_eq_zero hx (by rw [hn]; exact Real.sin_nat_mul_pi _),
      hn, Real.cos_nat_mul_pi]
    push_cast; ring
  · field_simp
    push_cast; ring

/-- trigIntegral hasSum 3. -/
@[dlmf 6.15.E3]
theorem trigIntegral_hasSum_3  :
    HasSum (fun n : ℕ => (-1 : ℂ)^(n+1)*cosInt (2*π*(n+1 : ℂ))) (1-Real.log 2-Real.eulerMascheroniConstant/2) := by
  have hc : 0 < 2 * π := by positivity
  have h := eiTr_hasSum_g hc
  rw [eiTr_integral_fermi hc, eiTr_K_eq hc one_pos,
    eiTr_K_eq (by positivity : 0 < 2 * (2 * π)) one_pos,
    show 1 * (2 * π) / (2 * π) = 1 by field_simp, show 1 * (2 * (2 * π)) / (2 * π) = 2 by field_simp,
    eiTr_digamma_two, Real.digamma_one, Real.log_one] at h
  have h' := Complex.hasSum_ofReal.2 h
  convert h' using 1
  · funext n
    have hx : 0 < 2 * π * ((n:ℝ) + 1) := by positivity
    have hn : 2 * π * ((n:ℝ) + 1) = ((2 * (n + 1) : ℕ) : ℝ) * π := by push_cast; ring
    rw [show (2 : ℂ) * π * ((n:ℂ) + 1) = ((2 * π * ((n:ℝ) + 1) : ℝ) : ℂ) by push_cast; ring,
      cosInt_ofReal hx, eiTr_cosInt_of_sin_eq_zero hx (by rw [hn]; exact Real.sin_nat_mul_pi _),
      hn, Real.cos_nat_mul_pi, pow_mul]
    push_cast; ring
  · push_cast; ring

/-- trigIntegral hasSum 4. -/
@[dlmf 6.15.E4]
theorem trigIntegral_hasSum_4  :
    HasSum (fun n : ℕ => (-1 : ℂ)^(n+1)*sinIntTail (2*π*(n+1 : ℂ))/(n+1 : ℂ)) (π*(3/2*Real.log 2-1)) := by
  have hc : 0 < 2 * π := by positivity
  have h := eiTr_hasSum_f hc
  rw [eiTr_integral_log_eq' hc, eiTr_arctanK_eq hc,
    eiTr_arctanK_eq (by positivity : 0 < 2 * (2 * π)),
    show 2 * π / (2 * π) = 1 by field_simp, show 2 * (2 * π) / (2 * π) = 2 by field_simp,
    Real.Gamma_two, Real.Gamma_one, Real.log_one] at h
  have h' := Complex.hasSum_ofReal.2 h
  convert h' using 1
  · funext n
    have hx : 0 < 2 * π * ((n:ℝ) + 1) := by positivity
    have hn : 2 * π * ((n:ℝ) + 1) = ((2 * (n + 1) : ℕ) : ℝ) * π := by push_cast; ring
    rw [show (2 : ℂ) * π * ((n:ℂ) + 1) = ((2 * π * ((n:ℝ) + 1) : ℝ) : ℂ) by push_cast; ring,
      sinIntTail, sinInt_ofReal,
      show ((Real.sinInt (2 * π * ((n:ℝ) + 1)) : ℂ) - π / 2) =
        ((Real.sinInt (2 * π * ((n:ℝ) + 1)) - π / 2 : ℝ) : ℂ) by push_cast; ring,
      eiTr_sinIntTail_of_sin_eq_zero hx (by rw [hn]; exact Real.sin_nat_mul_pi _),
      hn, Real.cos_nat_mul_pi, pow_mul]
    push_cast; ring
  · field_simp
    push_cast; ring

/-- Acton auxiliary integral. -/
@[dlmf 6.18.E1]
def expIntActonA (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (t : ℂ)^1*exp (-z*t)/((t : ℂ)^2+1) * ((t : ℂ)^2/(1+(t : ℂ)^2))^n

/-- Acton auxiliary integral. -/
@[dlmf 6.18.E1]
def expIntActonB (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (t : ℂ)^0*exp (-z*t)/((t : ℂ)^2+1) * ((t : ℂ)^2/(1+(t : ℂ)^2))^n

/-- Acton auxiliary integral. -/
@[dlmf 6.18.E1]
def expIntActonC (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (t : ℂ)^0*exp (-z*t)/1 * ((t : ℂ)^2/(1+(t : ℂ)^2))^n

/-- Initial normalization in DLMF §6.18(ii). -/
theorem expIntActon_initial {z : ℂ} (hz : 0 < z.re) :
    expIntActonB 0 z=expIntAuxF z ∧ expIntActonA 0 z=expIntAuxG z ∧ expIntActonC 0 z=1/z := by
  obtain ⟨hf, hg⟩ := expIntAux_laplace_Ioi hz
  refine ⟨?_, ?_, ?_⟩
  · rw [expIntActonB, hf]; simp
  · rw [expIntActonA, hg]; simp only [pow_zero, mul_one, pow_one]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
  · rw [expIntActonC]
    have := (laplace_nat_pow hz 0).2
    simpa using this

/-- A bounded continuous real weight against `e^{-zt}`, `Re z > 0`, is integrable on `(0,∞)`. -/
theorem integrableOn_cexp_mul_bounded {z : ℂ} (hz : 0 < z.re) {g : ℝ → ℝ} (hg : Continuous g)
    {K : ℝ} (hK : ∀ t, 0 ≤ t → |g t| ≤ K) :
    IntegrableOn (fun t : ℝ => exp (-z*t)*(g t : ℂ)) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hz).const_mul K) ?_ ?_
  · exact (Continuous.mul (by fun_prop) (Complex.continuous_ofReal.comp hg)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have hre : (-z*(t:ℂ)).re = -z.re*t := by simp
    rw [hre, mul_comm]
    exact mul_le_mul_of_nonneg_right (hK t (le_of_lt ht)) (Real.exp_pos _).le

/-- `e^{-zt}` times a bounded real weight tends to zero, `Re z > 0`. -/
theorem tendsto_cexp_mul_bounded {z : ℂ} (hz : 0 < z.re) {g : ℝ → ℝ}
    {K : ℝ} (hK : ∀ t, 0 ≤ t → |g t| ≤ K) :
    Tendsto (fun t : ℝ => exp (-z*t)*(g t : ℂ)) atTop (𝓝 0) := by
  have hl : Tendsto (fun t : ℝ => K*Real.exp (-(z.re*t))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hz)).const_mul K
  refine squeeze_zero_norm' ?_ hl
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have hre : (-z*(t:ℂ)).re = -(z.re*t) := by simp
  rw [hre, mul_comm]
  exact mul_le_mul_of_nonneg_right (hK t ht) (Real.exp_pos _).le

/-- Integration by parts on `(0,∞)` against `e^{-zt}` for a real weight vanishing at zero. -/
theorem integral_cexp_mul_deriv {z : ℂ} (hz : 0 < z.re) {u v : ℝ → ℝ}
    (hu : ∀ t, HasDerivAt u (v t) t) (hv : Continuous v) (h0 : u 0 = 0)
    {K : ℝ} (hK : ∀ t, 0 ≤ t → |u t| ≤ K) {K' : ℝ} (hK' : ∀ t, 0 ≤ t → |v t| ≤ K') :
    (∫ t in Ioi (0:ℝ), exp (-z*t)*(v t : ℂ)) = z*∫ t in Ioi (0:ℝ), exp (-z*t)*(u t : ℂ) := by
  have hc : Continuous u := continuous_iff_continuousAt.mpr fun t => (hu t).continuousAt
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => exp (-z*t)*(u t : ℂ))
      (exp (-z*t)*(v t : ℂ) + (-z)*(exp (-z*t)*(u t : ℂ))) t := by
    have he : HasDerivAt (fun t : ℝ => exp (-z*t)) (exp (-z*t)*(-z)) t := by
      have := ((hasDerivAt_id (t:ℂ)).const_mul (-z)).cexp.comp_ofReal
      simpa using this
    convert he.mul (hu t).ofReal_comp using 1
    ring
  have hi1 := integrableOn_cexp_mul_bounded hz hv hK'
  have hi2 := (integrableOn_cexp_mul_bounded hz hc hK).const_mul (-z)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (hd 0).continuousAt.continuousWithinAt
    (fun t _ => hd t) (hi1.add hi2) (tendsto_cexp_mul_bounded hz hK)
  rw [integral_add hi1 hi2, integral_const_mul, h0] at h
  simp only [Complex.ofReal_zero, mul_zero, sub_zero] at h
  linear_combination h

/-- expIntActon recurrence. -/
@[dlmf 6.18.E2]
theorem expIntActon_recurrence {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : 1 ≤ n) :
    expIntActonA (n-1) z=expIntActonA n z+z/(2*n)*expIntActonC n z ∧ expIntActonB (n-1) z=(2*n*expIntActonB n z+z*expIntActonA (n-1) z)/(2*n-1) ∧ expIntActonC (n-1) z=expIntActonC n z+expIntActonB (n-1) z := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
  simp only [Nat.add_sub_cancel]
  let W : ℝ → ℝ := fun t => t^2/(1+t^2)
  let P : ℝ → ℝ := fun t => 1/(t^2+1)
  let Q : ℝ → ℝ := fun t => t/(t^2+1)
  have hpos (t : ℝ) : 0 < t^2+1 := by positivity
  have hpos' (t : ℝ) : 0 < 1+t^2 := by positivity
  have hW (t : ℝ) : |W t| ≤ 1 := by
    simp only [W]; rw [abs_div, abs_of_nonneg (sq_nonneg t), abs_of_pos (hpos' t),
      div_le_one (hpos' t)]; linarith
  have hP (t : ℝ) : |P t| ≤ 1 := by
    simp only [P]; rw [abs_div, abs_one, abs_of_pos (hpos t), div_le_one (hpos t)]
    nlinarith [sq_nonneg t]
  have hQ (t : ℝ) : |Q t| ≤ 1 := by
    simp only [Q]; rw [abs_div, abs_of_pos (hpos t), div_le_one (hpos t)]
    nlinarith [sq_nonneg (|t|-1), sq_abs t, abs_nonneg t]
  have hWk (k : ℕ) (t : ℝ) : |W t^k| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hW t)
  have hb (f : ℝ → ℝ) (hf : ∀ t, |f t| ≤ 1) (k : ℕ) (t : ℝ) : |f t*W t^k| ≤ 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg (f t), abs_nonneg (W t^k), hf t, hWk k t]
  have hcW : Continuous W := by
    exact Continuous.div (by fun_prop) (by fun_prop) fun t => (hpos' t).ne'
  have hcP : Continuous P := Continuous.div (by fun_prop) (by fun_prop) fun t => (hpos t).ne'
  have hcQ : Continuous Q := Continuous.div (by fun_prop) (by fun_prop) fun t => (hpos t).ne'
  -- rewrite the three integrals with real weights
  have hA (k : ℕ) : expIntActonA k z = ∫ t in Ioi (0:ℝ), exp (-z*t)*((Q t*W t^k : ℝ) : ℂ) := by
    unfold expIntActonA
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [Q, W]; push_cast; ring
  have hB (k : ℕ) : expIntActonB k z = ∫ t in Ioi (0:ℝ), exp (-z*t)*((P t*W t^k : ℝ) : ℂ) := by
    unfold expIntActonB
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [P, W]; push_cast; ring
  have hC (k : ℕ) : expIntActonC k z = ∫ t in Ioi (0:ℝ), exp (-z*t)*((W t^k : ℝ) : ℂ) := by
    unfold expIntActonC
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [W]; push_cast; ring
  have iA (k : ℕ) : IntegrableOn (fun t : ℝ => exp (-z*t)*((Q t*W t^k : ℝ) : ℂ)) (Ioi 0) :=
    integrableOn_cexp_mul_bounded hz (g := fun t => Q t*W t^k) (hcQ.mul (hcW.pow k))
      (fun t _ => hb Q hQ k t)
  have iB (k : ℕ) : IntegrableOn (fun t : ℝ => exp (-z*t)*((P t*W t^k : ℝ) : ℂ)) (Ioi 0) :=
    integrableOn_cexp_mul_bounded hz (g := fun t => P t*W t^k) (hcP.mul (hcW.pow k))
      (fun t _ => hb P hP k t)
  have iC (k : ℕ) : IntegrableOn (fun t : ℝ => exp (-z*t)*((W t^k : ℝ) : ℂ)) (Ioi 0) :=
    integrableOn_cexp_mul_bounded hz (g := fun t => W t^k) (hcW.pow k) (fun t _ => hWk k t)
  have hw0 (t : ℝ) : HasDerivAt W (2*t/(1+t^2)^2) t := by
    have h := (hasDerivAt_pow 2 t).div ((hasDerivAt_pow 2 t).const_add 1) (hpos' t).ne'
    refine h.congr_deriv ?_
    field_simp
    push_cast
    ring
  have hq0 (t : ℝ) : HasDerivAt Q ((1-t^2)/(t^2+1)^2) t := by
    have h := (hasDerivAt_id t).div ((hasDerivAt_pow 2 t).add_const 1) (hpos t).ne'
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
    push_cast
    ring
  have hm1 : ((m+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  refine ⟨?_, ?_, ?_⟩
  · -- integration by parts against W^(m+1)
    have hd (t : ℝ) : HasDerivAt (fun t => W t^(m+1))
        (2*(m+1)*(Q t*W t^m) - 2*(m+1)*(Q t*W t^(m+1))) t := by
      refine ((hw0 t).pow (m+1)).congr_deriv ?_
      have h1 : 1+t^2 ≠ 0 := (hpos' t).ne'
      have h2 : t^2+1 ≠ 0 := (hpos t).ne'
      simp only [Q, W, Nat.add_sub_cancel, div_pow]
      field_simp
      push_cast
      ring
    have hv : Continuous (fun t => 2*(m+1)*(Q t*W t^m) - 2*(m+1)*(Q t*W t^(m+1))) := by
      have := hcQ; have := hcW; fun_prop
    have h := integral_cexp_mul_deriv hz hd hv (by simp [W]) (fun t _ => hWk (m+1) t)
      (K' := 2*(m+1)+2*(m+1)) (fun t _ => by
        refine le_trans (abs_sub _ _) (add_le_add ?_ ?_) <;>
        · rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*(m+1))]
          exact mul_le_of_le_one_right (by positivity) (hb Q hQ _ t))
    have hs : (∫ t in Ioi (0:ℝ), exp (-z*t)*(((2*(m+1)*(Q t*W t^m) - 2*(m+1)*(Q t*W t^(m+1))) : ℝ) : ℂ)) =
        2*(m+1)*expIntActonA m z - 2*(m+1)*expIntActonA (m+1) z := by
      rw [hA, hA, ← integral_const_mul, ← integral_const_mul, ← integral_sub
        ((iA m).const_mul _) ((iA (m+1)).const_mul _)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      push_cast; ring
    rw [hs, ← hC] at h
    push_cast at hm1 ⊢
    field_simp
    linear_combination h
  · -- integration by parts against Q W^m
    have hd (t : ℝ) : HasDerivAt (fun t => Q t*W t^m)
        ((2*m+1)*(P t*W t^m) - (2*m+2)*(P t*W t^(m+1))) t := by
      refine ((hq0 t).mul ((hw0 t).pow m)).congr_deriv ?_
      have h1 : 1+t^2 ≠ 0 := (hpos' t).ne'
      have h2 : t^2+1 ≠ 0 := (hpos t).ne'
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; simp only [P, W, Pi.pow_apply, pow_zero, zero_add, pow_one, div_pow]; field_simp; ring
      · obtain ⟨j, rfl⟩ : ∃ j, m = j+1 := ⟨m-1, by omega⟩
        simp only [P, Q, W, Nat.add_sub_cancel, Pi.pow_apply, div_pow]
        field_simp
        push_cast
        ring
    have hv : Continuous (fun t => (2*m+1)*(P t*W t^m) - (2*m+2)*(P t*W t^(m+1))) := by
      have := hcP; have := hcW; fun_prop
    have h := integral_cexp_mul_deriv hz hd hv (by simp [Q]) (fun t _ => hb Q hQ m t)
      (K' := (2*m+1)+(2*m+2)) (fun t _ => by
        refine le_trans (abs_sub _ _) (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*m+1)]
          exact mul_le_of_le_one_right (by positivity) (hb P hP _ t)
        · rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*m+2)]
          exact mul_le_of_le_one_right (by positivity) (hb P hP _ t))
    have hs : (∫ t in Ioi (0:ℝ), exp (-z*t)*((((2*m+1)*(P t*W t^m) - (2*m+2)*(P t*W t^(m+1))) : ℝ) : ℂ)) =
        (2*m+1)*expIntActonB m z - (2*m+2)*expIntActonB (m+1) z := by
      rw [hB, hB, ← integral_const_mul, ← integral_const_mul, ← integral_sub
        ((iB m).const_mul _) ((iB (m+1)).const_mul _)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      push_cast; ring
    rw [hs, ← hA] at h
    have h2 : (2*((m+1:ℕ):ℂ)-1) ≠ 0 := by
      push_cast
      intro h0; have := congrArg Complex.re h0; simp at this; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    rw [eq_div_iff h2]
    push_cast
    linear_combination h
  · rw [hC, hC, hB, ← integral_add (iC (m+1)) (iB m)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have : W t^m = W t^(m+1) + P t*W t^m := by
      have h1 : 1+t^2 ≠ 0 := (hpos' t).ne'
      have h2 : t^2+1 ≠ 0 := (hpos t).ne'
      simp only [W, P, div_pow]; field_simp; ring
    rw [← mul_add, ← Complex.ofReal_add, ← this]

end DLMF.Confluent
