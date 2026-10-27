/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.ExponentialIntegral
public import DLMF.Bessel.SphericalProductTools

/-!
# Power, reciprocal factorial and spherical Bessel series, DLMF §§6.6 and 6.10–6.11

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- Real.hasSum expIntEi. -/
@[dlmf 6.6.E1]
theorem Real.hasSum_expIntEi {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => x^(k+1)/((k+1).factorial*(k+1 : ℝ))) (Real.expIntEi x - Real.eulerMascheroniConstant - Real.log x) := by
  have h := (DLMF.Confluent.Real.hasSum_expIntEin (-x)).neg
  have he : Real.expIntEi x - Real.eulerMascheroniConstant - Real.log x = -DLMF.Confluent.Real.expIntEin (-x) := by
    rw [Real.expIntEi, abs_of_pos hx, show -(x:ℂ) = ((-x:ℝ):ℂ) by push_cast; ring,
      DLMF.Confluent.expIntEin_ofReal, Complex.ofReal_re]
    ring
  rw [he]
  refine h.congr_fun fun k => ?_
  have hs : (-1:ℝ)^k*(-1)^(k+1) = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow ⟨k, by ring⟩
  have ht : (-1:ℝ)^k * (-x)^(k+1) = -x^(k+1) := by rw [neg_pow x, ← mul_assoc, hs]; ring
  rw [ht]
  ring

/-- expIntE1 digamma series. -/
@[dlmf 6.6.E3]
theorem expIntE1_digamma_series {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => z^k/(k.factorial : ℂ)*digamma (k+1)) (exp z*(genExpIntE 1 z+log z)) :=
  incG_expIntE1_digamma_series hz

/-- expIntE1 hasSum. -/
@[dlmf 6.6.E2]
theorem expIntE1_hasSum {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => (-z)^(k+1)/((k+1).factorial*(k+1 : ℂ))) (-genExpIntE 1 z - Real.eulerMascheroniConstant - log z) := by
  have h := (hasSum_Ein_complex z).neg
  rw [expIntE1_eq_Ein_complex hz]
  convert h using 1
  · funext k
    rw [neg_pow z, pow_succ]
    ring
  · ring

/-- hasSum Ci complex. -/
@[dlmf 6.6.E6]
theorem hasSum_Ci_complex (z : ℂ) :
    HasSum (fun k : ℕ => (-1 : ℂ)^(k+1)*z^(2*k+2)/((2*k+2).factorial*(2*k+2 : ℂ))) (cosInt z-Real.eulerMascheroniConstant-log z) := by
  have hs := (summable_factorial_div_nat (c := fun k => (-1:ℂ)^k)
    (d := fun k => 2*k+2) (by intro k; simp)
    (by intro i j hij; dsimp at hij; omega) (by intro k; omega) z).hasSum.neg
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hs
  convert hs using 1
  · funext k
    rw [pow_succ]
    ring
  · simp only [cosInt, cosIntCin]
    ring

/-- Reciprocal factorial coefficients, with the recurrence of DLMF 6.10.3. -/
@[dlmf 6.10.E3]
def expIntReciprocalFactorialCoeff : ℕ → ℂ
  | 0 => 1
  | k+1 => -∑ j ∈ Finset.range (k+1), expIntReciprocalFactorialCoeff (k-j) / (j+1 : ℂ)
termination_by k => k

/-- expIntReciprocalFactorialCoeff initial. -/
@[dlmf 6.10.E2]
theorem expIntReciprocalFactorialCoeff_initial  :
    ∀ k < 5, expIntReciprocalFactorialCoeff k = ([1,-1,1/2,-1/3,1/6] : List ℂ)[k]! := by
  intro k hk
  interval_cases k <;> norm_num [expIntReciprocalFactorialCoeff, Finset.sum_range_succ]

/-- The normalised falling polynomial `(-t)_k / k!`. -/
noncomputable def recipFac_g (k : ℕ) (t : ℝ) : ℝ := ∏ i ∈ Finset.range k, ((i:ℝ) - t) / ((i:ℝ) + 1)

theorem recipFac_g_zero (t : ℝ) : recipFac_g 0 t = 1 := by simp [recipFac_g]

theorem recipFac_g_succ (k : ℕ) (t : ℝ) :
    recipFac_g (k+1) t = recipFac_g k t * (((k:ℝ) - t) / ((k:ℝ) + 1)) := by
  simp only [recipFac_g, Finset.prod_range_succ]

theorem recipFac_g_at_zero (k : ℕ) : recipFac_g (k+1) 0 = 0 := by
  rw [recipFac_g, Finset.prod_eq_zero (i := 0) (by simp) (by simp)]

theorem recipFac_g_continuous (k : ℕ) : Continuous (recipFac_g k) := by
  unfold recipFac_g
  fun_prop

theorem recipFac_hasDerivAt_g (k : ℕ) (t : ℝ) :
    HasDerivAt (recipFac_g k) (-∑ i ∈ Finset.range k, recipFac_g i t / ((k:ℝ) - i)) t := by
  induction k with
  | zero =>
    have : recipFac_g 0 = fun _ => (1:ℝ) := by funext s; exact recipFac_g_zero s
    rw [this]; simpa using hasDerivAt_const t (1:ℝ)
  | succ k ih =>
    have hf : (recipFac_g (k+1)) = fun s => recipFac_g k s * (((k:ℝ) - s) / ((k:ℝ) + 1)) := by
      funext s; exact recipFac_g_succ k s
    rw [hf]
    have h2 : HasDerivAt (fun s : ℝ => ((k:ℝ) - s) / ((k:ℝ) + 1)) (-1 / ((k:ℝ)+1)) t := by
      simpa using ((hasDerivAt_id t).const_sub (k:ℝ)).div_const ((k:ℝ)+1)
    convert ih.mul h2 using 1
    have hk : (k:ℝ) + 1 ≠ 0 := by positivity
    have hlt : ∀ i ∈ Finset.range k, (k:ℝ) - i ≠ 0 := by
      intro i hi
      have : (i:ℝ) < k := by exact_mod_cast Finset.mem_range.1 hi
      linarith
    have hlt' : ∀ i ∈ Finset.range (k+1), (k:ℝ) + 1 - i ≠ 0 := by
      intro i hi
      have : (i:ℝ) < k + 1 := by exact_mod_cast Finset.mem_range.1 hi
      linarith
    push_cast
    have A : (∑ i ∈ Finset.range (k+1), recipFac_g i t / ((k:ℝ) + 1 - i)) * ((k:ℝ)+1) =
        (∑ i ∈ Finset.range (k+1), recipFac_g i t) +
          ∑ i ∈ Finset.range (k+1), (i:ℝ) * recipFac_g i t / ((k:ℝ) + 1 - i) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := hlt' i hi
      field_simp
      ring
    have B : (∑ i ∈ Finset.range (k+1), (i:ℝ) * recipFac_g i t / ((k:ℝ) + 1 - i)) =
        ∑ i ∈ Finset.range k, ((i:ℝ)+1) * recipFac_g (i+1) t / ((k:ℝ) - i) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring_nf
    have C : (∑ i ∈ Finset.range k, recipFac_g i t / ((k:ℝ) - i)) * ((k:ℝ) - t) =
        (∑ i ∈ Finset.range k, ((i:ℝ)+1) * recipFac_g (i+1) t / ((k:ℝ) - i)) +
          ∑ i ∈ Finset.range k, recipFac_g i t := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := hlt i hi
      rw [recipFac_g_succ]
      field_simp
      ring
    have D : (∑ i ∈ Finset.range (k+1), recipFac_g i t) =
        (∑ i ∈ Finset.range k, recipFac_g i t) + recipFac_g k t := Finset.sum_range_succ _ _
    have E : (∑ i ∈ Finset.range (k+1), recipFac_g i t / ((k:ℝ) + 1 - i)) * ((k:ℝ)+1) =
        (∑ i ∈ Finset.range k, recipFac_g i t / ((k:ℝ) - i)) * ((k:ℝ) - t) + recipFac_g k t := by
      rw [A, B, C, D]; ring
    field_simp
    linear_combination -E

theorem recipFac_abs_g_le_choose {t : ℝ} :
    ∀ k ≤ ⌈t⌉₊, |recipFac_g k t| ≤ (⌈t⌉₊.choose k : ℝ) := by
  intro k
  induction k with
  | zero => intro _; simp [recipFac_g_zero]
  | succ k ih =>
    intro hk
    have hk' : k < ⌈t⌉₊ := hk
    have hkt : (k:ℝ) < t := Nat.lt_ceil.1 hk'
    have htm : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    have hc := Nat.choose_succ_right_eq ⌈t⌉₊ k
    have hc' : ((⌈t⌉₊.choose (k+1) : ℕ) : ℝ) * ((k:ℝ)+1) =
        (⌈t⌉₊.choose k : ℝ) * ((⌈t⌉₊ : ℝ) - k) := by
      rw [← Nat.cast_sub hk'.le]; exact_mod_cast hc
    rw [recipFac_g_succ, abs_mul, abs_div, abs_of_neg (by linarith : (k:ℝ) - t < 0),
      abs_of_pos (by positivity : (0:ℝ) < k + 1)]
    have hpos : (0:ℝ) < k + 1 := by positivity
    rw [show (⌈t⌉₊.choose (k+1) : ℝ) = (⌈t⌉₊.choose k : ℝ) * ((⌈t⌉₊ : ℝ) - k) / ((k:ℝ)+1) by
      rw [← hc']; field_simp]
    rw [mul_div_assoc]
    exact mul_le_mul (ih hk'.le) (div_le_div_of_nonneg_right (by linarith) hpos.le)
      (div_nonneg (by linarith) hpos.le) (Nat.cast_nonneg _)

theorem recipFac_mul_abs_g_succ_le {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hk : t ≤ k) :
    ((k:ℝ)+1) * |recipFac_g (k+1) t| ≤ k * |recipFac_g k t| := by
  rw [recipFac_g_succ, abs_mul, abs_div, abs_of_nonneg (by linarith : (0:ℝ) ≤ k - t),
    abs_of_pos (by positivity : (0:ℝ) < k + 1)]
  have hpos : (0:ℝ) < k + 1 := by positivity
  field_simp
  have := abs_nonneg (recipFac_g k t)
  nlinarith

theorem recipFac_mul_abs_g_le_of_ceil_le {t : ℝ} (ht : 0 ≤ t) :
    ∀ k, ⌈t⌉₊ ≤ k → (k:ℝ) * |recipFac_g k t| ≤ ⌈t⌉₊ := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have h := recipFac_abs_g_le_choose ⌈t⌉₊ le_rfl
    rw [Nat.choose_self, Nat.cast_one] at h
    have : (0:ℝ) ≤ ⌈t⌉₊ := by positivity
    nlinarith
  | succ k hk ih =>
    have htk : t ≤ k := (Nat.le_ceil t).trans (by exact_mod_cast hk)
    have := recipFac_mul_abs_g_succ_le ht htk
    push_cast
    linarith

/-- The bound `(t+1) 2^(t+1)` controlling `k |(−t)_k/k!|`. -/
noncomputable def recipFac_B (t : ℝ) : ℝ := (t + 1) * Real.exp ((t + 1) * Real.log 2)

theorem recipFac_mul_abs_g_le {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (k:ℝ) * |recipFac_g k t| ≤ recipFac_B t := by
  have hm : (⌈t⌉₊ : ℝ) ≤ t + 1 := (Nat.ceil_lt_add_one ht).le
  have h2 : ((2:ℝ) ^ ⌈t⌉₊) ≤ Real.exp ((t + 1) * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
    gcongr
  have h2' : (1:ℝ) ≤ 2 ^ ⌈t⌉₊ := one_le_pow₀ (by norm_num)
  have hm0 : (0:ℝ) ≤ ⌈t⌉₊ := by positivity
  have hB : (⌈t⌉₊ : ℝ) * 2 ^ ⌈t⌉₊ ≤ recipFac_B t := by
    unfold recipFac_B; gcongr
  rcases le_or_gt k ⌈t⌉₊ with hk | hk
  · have h := recipFac_abs_g_le_choose k hk
    have hc : (⌈t⌉₊.choose k : ℝ) ≤ 2 ^ ⌈t⌉₊ := by exact_mod_cast Nat.choose_le_two_pow _ _
    have hkm : (k:ℝ) ≤ ⌈t⌉₊ := by exact_mod_cast hk
    calc (k:ℝ) * |recipFac_g k t| ≤ ⌈t⌉₊ * 2 ^ ⌈t⌉₊ := by
          gcongr
          · exact h.trans hc
      _ ≤ _ := hB
  · have h := recipFac_mul_abs_g_le_of_ceil_le ht k hk.le
    nlinarith

theorem recipFac_abs_g_le {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : |recipFac_g k t| ≤ recipFac_B t := by
  rcases k with _ | k
  · rw [recipFac_g_zero, abs_one]
    unfold recipFac_B
    have : (1:ℝ) ≤ Real.exp ((t + 1) * Real.log 2) :=
      Real.one_le_exp (by have := Real.log_pos (by norm_num : (1:ℝ) < 2); positivity)
    nlinarith
  · have h := recipFac_mul_abs_g_le ht (k+1)
    have : (1:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast Nat.succ_pos k
    have := abs_nonneg (recipFac_g (k+1) t)
    nlinarith

theorem recipFac_b_pos : 0 < 1 - Real.log 2 := by
  have := Real.log_two_lt_d9; linarith

theorem recipFac_exp_mul_B (t : ℝ) :
    Real.exp (-t) * recipFac_B t =
      2 * (t * Real.exp (-(1 - Real.log 2) * t) + Real.exp (-(1 - Real.log 2) * t)) := by
  unfold recipFac_B
  have : Real.exp (-t) * Real.exp ((t + 1) * Real.log 2) =
      2 * Real.exp (-(1 - Real.log 2) * t) := by
    rw [← Real.exp_add, show -t + (t + 1) * Real.log 2 = Real.log 2 + (-(1 - Real.log 2) * t) by
      ring, Real.exp_add, Real.exp_log (by norm_num)]
  linear_combination (t + 1) * this

theorem recipFac_integrable_B : IntegrableOn (fun t => Real.exp (-t) * recipFac_B t) (Ioi 0) := by
  have hb := recipFac_b_pos
  have h1 : IntegrableOn (fun t : ℝ => t * Real.exp (-(1 - Real.log 2) * t)) (Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (by norm_num) one_pos hb).congr_fun
      (fun t ht => ?_) measurableSet_Ioi
    simp [Real.rpow_one]
  have h2 := exp_neg_integrableOn_Ioi 0 hb
  have h3 : IntegrableOn (fun t : ℝ => 2 * (t * Real.exp (-(1 - Real.log 2) * t) +
      Real.exp (-(1 - Real.log 2) * t))) (Ioi 0) := (h1.add h2).const_mul 2
  refine h3.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [recipFac_exp_mul_B]

theorem recipFac_tendsto_B : Tendsto (fun t => Real.exp (-t) * recipFac_B t) atTop (𝓝 0) := by
  have hb := recipFac_b_pos
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 _ hb
  have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 _ hb
  have := (h1.add h0).const_mul 2
  simp only [Real.rpow_one, Real.rpow_zero, one_mul, add_zero, mul_zero] at this
  refine this.congr fun t => ?_
  rw [recipFac_exp_mul_B]

theorem recipFac_integrable_g (k : ℕ) :
    IntegrableOn (fun t => Real.exp (-t) * recipFac_g k t) (Ioi 0) := by
  refine recipFac_integrable_B.mono' ?_ ?_
  · exact ((Real.continuous_exp.comp continuous_neg).mul
      (recipFac_g_continuous k)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.abs_exp, Real.norm_eq_abs]
    gcongr
    exact recipFac_abs_g_le (le_of_lt ht) k

/-- The moments `∫₀^∞ e^{-t} (−t)_k/k! dt`. -/
noncomputable def recipFac_d (k : ℕ) : ℝ := ∫ t in Ioi 0, Real.exp (-t) * recipFac_g k t

theorem recipFac_d_succ (k : ℕ) :
    recipFac_d (k+1) = -∑ i ∈ Finset.range (k+1), recipFac_d i / ((k:ℝ) + 1 - i) := by
  set f : ℝ → ℝ := fun t => -(Real.exp (-t) * recipFac_g (k+1) t)
  set f' : ℝ → ℝ := fun t => Real.exp (-t) * recipFac_g (k+1) t +
      ∑ i ∈ Finset.range (k+1), Real.exp (-t) * recipFac_g i t / ((k:ℝ) + 1 - i)
  have hderiv : ∀ t, HasDerivAt f (f' t) t := by
    intro t
    have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_neg t).exp
    have h := (he.mul (recipFac_hasDerivAt_g (k+1) t)).neg
    convert h using 1
    simp only [f']
    push_cast
    rw [mul_neg, Finset.mul_sum]
    simp only [mul_div_assoc]
    ring
  have hint : ∀ i, IntegrableOn (fun t => Real.exp (-t) * recipFac_g i t / ((k:ℝ) + 1 - i)) (Ioi 0) :=
    fun i => (recipFac_integrable_g i).div_const _
  have f'int : IntegrableOn f' (Ioi 0) :=
    (recipFac_integrable_g (k+1)).add (integrable_finsetSum _ fun i _ => hint i)
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h := recipFac_tendsto_B
    have : Tendsto (fun t => Real.exp (-t) * recipFac_g (k+1) t) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ h
      filter_upwards [eventually_ge_atTop 0] with t ht
      rw [norm_mul, Real.norm_eq_abs, Real.abs_exp, Real.norm_eq_abs]
      gcongr
      exact recipFac_abs_g_le ht _
    simpa [f] using this.neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (hderiv 0).continuousAt.continuousWithinAt
    (fun t _ => hderiv t) f'int hlim
  simp only [f, recipFac_g_at_zero, mul_zero, neg_zero, sub_zero, f'] at h
  rw [integral_add (recipFac_integrable_g (k+1)) (integrable_finsetSum _ fun i _ => hint i),
    integral_finsetSum _ fun i _ => hint i] at h
  simp only [integral_div] at h
  unfold recipFac_d
  linarith

theorem recipFac_coeff_eq_d (k : ℕ) : expIntReciprocalFactorialCoeff k = (recipFac_d k : ℂ) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · rw [expIntReciprocalFactorialCoeff]
      simp only [recipFac_d, recipFac_g_zero, mul_one, integral_exp_neg_Ioi_zero, ofReal_one]
    · rw [expIntReciprocalFactorialCoeff, recipFac_d_succ]
      push_cast
      congr 1
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      rw [show k + 1 - 1 - j = k - j by omega, show k - (k - j) = j by omega, ih j (by omega),
        Nat.cast_sub hj']
      ring

theorem recipFac_norm_poch_ge {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∏ j ∈ Finset.range n, (z.re + j) ≤ ‖poch z n‖ := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [Finset.prod_range_succ, poch_succ, norm_mul]
    have h1 : z.re + n ≤ ‖z + n‖ := by
      have := Complex.re_le_norm (z + n); simpa using this
    exact mul_le_mul ih h1 (by positivity) (norm_nonneg _)

theorem recipFac_poch_ne_zero {z : ℂ} (hz : 0 < z.re) (n : ℕ) : poch z n ≠ 0 := by
  have h := recipFac_norm_poch_ge hz n
  have : 0 < ∏ j ∈ Finset.range n, (z.re + j) :=
    Finset.prod_pos fun j _ => by positivity
  exact norm_pos_iff.1 (this.trans_le h)

theorem recipFac_poch_bound {z : ℂ} (hz : 0 < z.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      ‖(((k+1).factorial : ℕ) : ℂ) / poch z (k+2)‖ ≤ C * ((k:ℝ)+1) ^ (-z.re) := by
  obtain ⟨C, hC⟩ := (Real.GammaSeq_tendsto_Gamma z.re).bddAbove_range
  refine ⟨max C 0, le_max_right _ _, fun k => ?_⟩
  have hprod : 0 < ∏ j ∈ Finset.range (k+2), (z.re + j) :=
    Finset.prod_pos fun j _ => by positivity
  have hk : (0:ℝ) < (k:ℝ) + 1 := by positivity
  rw [norm_div, Complex.norm_natCast]
  calc (((k+1).factorial : ℕ) : ℝ) / ‖poch z (k+2)‖
      ≤ (((k+1).factorial : ℕ) : ℝ) / ∏ j ∈ Finset.range (k+2), (z.re + j) :=
        div_le_div_of_nonneg_left (by positivity) hprod (recipFac_norm_poch_ge hz _)
    _ = Real.GammaSeq z.re (k+1) * ((k:ℝ)+1) ^ (-z.re) := by
        rw [Real.GammaSeq, Real.rpow_neg hk.le]
        push_cast
        have : ((k:ℝ)+1) ^ z.re ≠ 0 := (Real.rpow_pos_of_pos hk _).ne'
        field_simp
    _ ≤ max C 0 * ((k:ℝ)+1) ^ (-z.re) := by
        gcongr
        exact (hC ⟨k+1, rfl⟩).trans (le_max_left _ _)

/-- The integrand terms of the reciprocal factorial series. -/
noncomputable def recipFac_F (z : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  ((Real.exp (-t) * recipFac_g k t : ℝ) : ℂ) * ((k.factorial : ℂ) / poch z (k+1))

theorem recipFac_norm_F_succ_le {z : ℂ} {C : ℝ}
    (hC : ∀ k : ℕ, ‖(((k+1).factorial : ℕ) : ℂ) / poch z (k+2)‖ ≤ C * ((k:ℝ)+1) ^ (-z.re))
    {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    ‖recipFac_F z (k+1) t‖ ≤ Real.exp (-t) * recipFac_B t * (C * ((k:ℝ)+1) ^ (-z.re - 1)) := by
  have hk : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hg : |recipFac_g (k+1) t| ≤ recipFac_B t / ((k:ℝ)+1) := by
    rw [le_div_iff₀ hk, mul_comm]
    have := recipFac_mul_abs_g_le ht (k+1); push_cast at this; exact this
  rw [recipFac_F, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.abs_exp,
    Real.rpow_sub_one hk.ne']
  calc Real.exp (-t) * |recipFac_g (k+1) t| * ‖(((k+1).factorial : ℕ) : ℂ) / poch z (k+1+1)‖
      ≤ Real.exp (-t) * (recipFac_B t / ((k:ℝ)+1)) * (C * ((k:ℝ)+1) ^ (-z.re)) := by
        have hB : 0 ≤ recipFac_B t := (abs_nonneg _).trans (recipFac_abs_g_le ht 0)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le) (hC k) (norm_nonneg _)
          (by positivity)
    _ = _ := by ring

theorem recipFac_summable_u {z : ℂ} (hz : 0 < z.re) (C : ℝ) :
    Summable (fun k : ℕ => C * ((k:ℝ)+1) ^ (-z.re - 1)) := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by linarith : -z.re - 1 < -1))
  exact (h.mul_left C).congr fun k => by push_cast; rfl

theorem recipFac_hasSum_F {z : ℂ} (hz : 0 < z.re) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun k => recipFac_F z k t) (Complex.exp (-(t:ℂ)) / ((t:ℂ) + z)) := by
  obtain ⟨C, hC0, hC⟩ := recipFac_poch_bound hz
  have hsum : Summable (fun k => recipFac_F z k t) := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_norm_bounded ((recipFac_summable_u hz C).mul_left
      (Real.exp (-t) * recipFac_B t)) fun k => ?_
    exact recipFac_norm_F_succ_le hC ht k
  have hzt : (t:ℂ) + z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this; linarith
  -- telescoping
  set T : ℕ → ℂ := fun n => ((n.factorial : ℂ) * (recipFac_g n t : ℂ)) / poch z n with hT
  have htel : ∀ k, recipFac_F z k t = (Real.exp (-t) : ℂ) * ((T k - T (k+1)) / ((t:ℂ) + z)) := by
    intro k
    have h1 := recipFac_poch_ne_zero hz k
    have h2 : z + k ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    simp only [recipFac_F, hT, poch_succ, recipFac_g_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have hpart : ∀ N, ∑ k ∈ Finset.range N, recipFac_F z k t =
      (Real.exp (-t) : ℂ) * ((1 - T N) / ((t:ℂ) + z)) := by
    intro N
    simp only [htel, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_range_sub']
    simp [hT, recipFac_g_zero, poch_zero]
  have hTlim : Tendsto T atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 2]
    have hlim : Tendsto (fun k : ℕ => recipFac_B t * (C * ((k:ℝ)+1) ^ (-z.re))) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop hz).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      simpa using (h.const_mul C).const_mul (recipFac_B t)
    refine squeeze_zero_norm (fun k => ?_) hlim
    simp only [hT]
    have hg := recipFac_mul_abs_g_le ht (k+2)
    rw [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    have hb := hC k
    rw [norm_div, Complex.norm_natCast] at hb
    have hp : 0 < ‖poch z (k+2)‖ := norm_pos_iff.2 (recipFac_poch_ne_zero hz _)
    rw [div_le_iff₀ hp] at hb ⊢
    have e : (((k+2).factorial : ℕ) : ℝ) * |recipFac_g (k+2) t| =
        ((k+1).factorial : ℕ) * (((k+2 : ℕ) : ℝ) * |recipFac_g (k+2) t|) := by
      rw [Nat.factorial_succ (k+1)]; push_cast; ring
    rw [e]
    calc (((k+1).factorial : ℕ) : ℝ) * (((k+2 : ℕ) : ℝ) * |recipFac_g (k+2) t|)
        ≤ ((k+1).factorial : ℕ) * recipFac_B t := by gcongr
      _ = recipFac_B t * ((k+1).factorial : ℕ) := mul_comm _ _
      _ ≤ recipFac_B t * (C * ((k:ℝ)+1) ^ (-z.re) * ‖poch z (k+2)‖) := by
          have : 0 ≤ recipFac_B t := ((abs_nonneg _).trans (recipFac_abs_g_le ht 0))
          gcongr
      _ = _ := by ring
  rw [hsum.hasSum_iff_tendsto_nat]
  simp only [hpart]
  have := ((tendsto_const_nhds (x := (1:ℂ))).sub hTlim).div_const ((t:ℂ) + z)
  have := this.const_mul (Real.exp (-t) : ℂ)
  convert this using 2
  rw [sub_zero, Complex.ofReal_exp, Complex.ofReal_neg]; ring

/-- expIntE1 reciprocal factorial series. -/
@[dlmf 6.10.E1]
theorem expIntE1_reciprocal_factorial_series {z : ℂ} (hz : 0 < z.re) :
    HasSum (fun k : ℕ => (k.factorial : ℂ)*expIntReciprocalFactorialCoeff k / poch z (k+1)) (exp z*genExpIntE 1 z) := by
  obtain ⟨C, hC0, hC⟩ := recipFac_poch_bound hz
  have hint : ∀ k, Integrable (recipFac_F z k) (volume.restrict (Ioi 0)) := fun k =>
    ((recipFac_integrable_g k).ofReal).mul_const _
  have hnorm : Summable (fun k => ∫ t in Ioi 0, ‖recipFac_F z k t‖) := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _)
      (fun k => ?_) ((recipFac_summable_u hz C).mul_left (∫ t in Ioi 0, Real.exp (-t) * recipFac_B t))
    rw [← integral_mul_const]
    refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
      (recipFac_integrable_B.mul_const _) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    exact recipFac_norm_F_succ_le hC (le_of_lt ht) k
  have h := hasSum_integral_of_summable_integral_norm hint hnorm
  have hI : (∫ t in Ioi 0, ∑' k, recipFac_F z k t) =
      ∫ t : ℝ in Ioi 0, exp (-t : ℂ)/(t+z) :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => (recipFac_hasSum_F hz (le_of_lt ht)).tsum_eq
  rw [hI] at h
  have hE : exp z * genExpIntE 1 z = ∫ t : ℝ in Ioi 0, exp (-t : ℂ)/(t+z) := by
    rw [expIntE1_stieltjes (Complex.mem_slitPlane_iff.2 (Or.inl hz)), ← mul_assoc, ← Complex.exp_add,
      add_neg_cancel, Complex.exp_zero, one_mul]
  rw [hE]
  refine h.congr_fun fun k => ?_
  simp only [recipFac_F]
  rw [integral_mul_const, integral_complex_ofReal, recipFac_coeff_eq_d, recipFac_d]
  ring

/-- Spherical-Bessel expansion coefficients. -/
@[dlmf 6.10.E7]
def expIntSphericalCoeff (n : ℕ) : ℂ :=
  (2*n+1 : ℂ)*(1-(-1 : ℂ)^n+digamma (n+1)-digamma 1)

/-- sinInt spherical series. -/
@[dlmf 6.10.E4]
theorem sinInt_spherical_series (z : ℂ) :
    HasSum (fun n : ℕ => z*sphericalJ n (z/2)^2) (sinInt z) := by
  refine sphSeries_hasSum_of_hasDerivAt
    (f := fun n w => w * sphericalJ n (w/2)^2)
    (g := fun n w => if n = 0 then sphericalJ 0 (w/2) * cos (w/2) else
      w/2 * sphericalJ (n-1) (w/2) * sphericalJ n (w/2)) (F := sinInt)
    (fun n w => by
      rcases n with _ | n
      · simpa using sphSeries_hasDerivAt_mul_sphericalJ_zero_half_sq w
      · simpa using sphSeries_hasDerivAt_mul_sphericalJ_succ_half_sq n w)
    (fun w => by
      rw [← tendsto_add_atTop_iff_nat 1]
      have h := (((sphSeries_tendsto_sphericalJ (w/2)).mul
        ((sphSeries_tendsto_sphericalJ (w/2)).comp (tendsto_add_atTop_nat 1))).const_mul (w/2))
      simpa [Function.comp_def, mul_assoc] using h)
    sphSeries_bound_mul_sphericalJ_half_sq
    (fun w => by
      have he : sinInt = primitive (dslope sin 0) := by
        funext v; rw [sinInt_segment_integral, primitive_dslope_zero Complex.sin_zero]
      rw [he]
      have h := hasDerivAt_primitive (differentiable_dslope_entire Complex.differentiable_sin 0) w
      convert h using 1
      simp only [ite_true]
      rw [← sphSeries_sphericalJ_zero_eq_dslope]
      rcases eq_or_ne w 0 with rfl | hw
      · simp [sphSeries_sphericalJ_zero_zero]
      · have h1 := sphSeries_mul_sphericalJ_zero w
        have h2 := sphSeries_mul_sphericalJ_zero (w/2)
        have h3 : sin w = 2 * sin (w/2) * cos (w/2) := by
          rw [← Complex.sin_two_mul]; ring_nf
        apply mul_left_cancel₀ hw
        linear_combination -h1 - h3 + 2 * cos (w/2) * h2)
    (by simp [sinInt]) z

/-- Summation by parts for a sequence `q` with `q 0 = 0`. -/
theorem cinSph_hasSum_by_parts {c q : ℕ → ℂ} {L : ℂ} (hq0 : q 0 = 0)
    (hs : Summable (fun n => c n * q n)) (hs' : Summable (fun n => c n * q (n+1)))
    (h : HasSum (fun n => c n * (q n - q (n+1))) L) :
    HasSum (fun n => (c (n+1) - c n) * q (n+1)) L := by
  have h1 : HasSum (fun n => c (n+1) * q (n+1)) (∑' n, c n * q n) := by
    have := hs.hasSum
    rw [← hasSum_nat_add_iff' 1] at this
    simpa [hq0] using this
  have h3 : HasSum (fun n => c n * (q n - q (n+1))) (∑' n, c n * q n - ∑' n, c n * q (n+1)) :=
    (hs.hasSum.sub hs'.hasSum).congr_fun fun n => by ring
  rw [h.unique h3]
  exact (h1.sub hs'.hasSum).congr_fun fun n => by ring

/-- The harmonic-number form of the coefficients of DLMF 6.10.5. -/
def cinSphB (n : ℕ) : ℂ := 1 - (-1:ℂ)^n + (harmonic n : ℂ)

theorem cinSph_coeff (n : ℕ) : expIntSphericalCoeff n = (2*n+1) * cinSphB n := by
  rw [expIntSphericalCoeff, cinSphB, digamma_nat_add_one, digamma_one]
  ring

theorem cinSph_b_succ (n : ℕ) : cinSphB (n+1) - cinSphB n = 2*(-1:ℂ)^n + 1/((n:ℂ)+1) := by
  simp only [cinSphB, harmonic_succ]
  push_cast
  ring

theorem cinSph_norm_natCast_le (n : ℕ) : ‖((n:ℂ)+1)‖ ≤ 2^n := by
  rw [show ((n:ℂ)+1) = ((n+1:ℕ):ℂ) by push_cast; ring, Complex.norm_natCast]
  exact_mod_cast Nat.lt_two_pow_self (n := n)

theorem cinSph_norm_natCast_le' (n : ℕ) : ‖(n:ℂ)‖ ≤ 2^n := by
  rw [Complex.norm_natCast]
  exact_mod_cast (Nat.lt_two_pow_self (n := n)).le

theorem cinSph_norm_two_mul_add_one_le (n : ℕ) : ‖(2*(n:ℂ)+1)‖ ≤ 2*2^n := by
  rw [show (2*(n:ℂ)+1) = ((2*n+1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  exact sphProd_two_mul_add_one_le n

theorem cinSph_norm_harmonic_le (n : ℕ) : ‖(harmonic n : ℂ)‖ ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ]
    push_cast
    refine (norm_add_le _ _).trans ?_
    have : ‖((n:ℂ)+1)⁻¹‖ ≤ 1 := by
      rw [norm_inv, show ((n:ℂ)+1) = ((n+1:ℕ):ℂ) by push_cast; ring, Complex.norm_natCast]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_pos n)
    linarith

theorem cinSph_norm_b_le (n : ℕ) : ‖cinSphB n‖ ≤ 3*2^n := by
  rw [cinSphB]
  have h1 := cinSph_norm_harmonic_le n
  have h2 : (n:ℝ) ≤ 2^n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have h3 : (1:ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
  calc ‖1 - (-1:ℂ)^n + (harmonic n : ℂ)‖ ≤ ‖(1:ℂ)‖ + ‖(-1:ℂ)^n‖ + ‖(harmonic n : ℂ)‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ 1 + 1 + n := by rw [norm_one, norm_pow, norm_neg, norm_one, one_pow]; linarith
    _ ≤ 3*2^n := by linarith

theorem cinSph_norm_coeff_le (n : ℕ) : ‖expIntSphericalCoeff n‖ ≤ 6*4^n := by
  rw [cinSph_coeff, norm_mul]
  calc ‖(2*(n:ℂ)+1)‖ * ‖cinSphB n‖ ≤ (2*2^n) * (3*2^n) :=
        mul_le_mul (cinSph_norm_two_mul_add_one_le n) (cinSph_norm_b_le n) (norm_nonneg _)
          (by positivity)
    _ = 6*4^n := by rw [show (4:ℝ)^n = 2^n*2^n by rw [← mul_pow]; norm_num]; ring

/-- Ball bounds for `cₙ jₙ(w)²`. -/
theorem cinSph_bound_sq (c : ℕ → ℂ) {C ρ : ℝ} (hρ : 0 ≤ ρ) (hc : ∀ n, ‖c n‖ ≤ C * ρ^n) (R : ℝ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n w, ‖w‖ < R → ‖c n * sphericalJ n w ^ 2‖ ≤ u n := by
  obtain ⟨u, hu, h⟩ := sphProd_bound_coeff_mul c hρ hc id R
  exact ⟨u, hu, fun n w hw => by simpa [sq, mul_assoc] using h n w hw.le⟩

/-- The derivative of the square `jₙ²` as a difference. -/
theorem cinSph_hasDerivAt_sq (n : ℕ) (w : ℂ) :
    HasDerivAt (fun w => sphericalJ n w ^ 2)
      (2 * ((n:ℂ) * sphericalJ (n-1) w * sphericalJ n w -
        ((n+1:ℕ):ℂ) * sphericalJ (n+1-1) w * sphericalJ (n+1) w) / (2*n+1)) w := by
  simpa using sphProd_hasDerivAt_sphericalJ_sq n w

/-- Summability of `cₙ qₙ` and `cₙ qₙ₊₁`, `qₙ = n jₙ₋₁ jₙ`, for geometric `cₙ`. -/
theorem cinSph_summable_q (c : ℕ → ℂ) {C ρ : ℝ} (hρ : 0 ≤ ρ) (hc : ∀ n, ‖c n‖ ≤ C * ρ^n) (w : ℂ) :
    Summable (fun n => c n * ((n:ℂ) * sphericalJ (n-1) w * sphericalJ n w)) ∧
    Summable (fun n => c n * (((n+1:ℕ):ℂ) * sphericalJ (n+1-1) w * sphericalJ (n+1) w)) := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) ((hc 0).trans (by simp))
  constructor
  · have h := sphProd_summable_coeff_mul (fun n => c n * n) (C := C) (ρ := 2*ρ) (by positivity)
      (fun n => by
        rw [norm_mul, mul_pow, ← mul_assoc, mul_right_comm]
        exact mul_le_mul (hc n) (cinSph_norm_natCast_le' n) (norm_nonneg _) (by positivity))
      (fun n => n-1) w
    exact h.congr fun n => by ring
  · have h := sphProd_summable_coeff_mul (fun n => c n * ((n:ℂ)+1)) (C := C) (ρ := 2*ρ)
      (by positivity)
      (fun n => by
        rw [norm_mul, mul_pow, ← mul_assoc, mul_right_comm]
        exact mul_le_mul (hc n) (cinSph_norm_natCast_le n) (norm_nonneg _) (by positivity))
      (fun n => n+1) w
    refine h.congr fun n => ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

/-- Termwise Euler derivative of `∑ (-1)ⁿ (2n+1) jₙ(z)² = j₀(2z)`:
`∑ 4z (-1)ⁿ (n+1) jₙ(z) jₙ₊₁(z) = 2z j₁(2z)`. -/
theorem cinSph_hasSum_alt_prod (x : ℂ) :
    HasSum (fun n : ℕ => 4*x*(-1:ℂ)^n*((n:ℂ)+1)*(sphericalJ n x*sphericalJ (n+1) x))
      (2*x*sphericalJ 1 (2*x)) := by
  set f : ℕ → ℂ → ℂ := fun n w => (-1:ℂ)^n*(2*n+1)*sphericalJ n w^2 with hf
  obtain ⟨-, hS⟩ := sphSeries_euler_hasSum 0 (f := f)
    (f' := fun n w => (-1:ℂ)^n*(2*n+1)*(2 * ((n:ℂ) * sphericalJ (n-1) w * sphericalJ n w -
        ((n+1:ℕ):ℂ) * sphericalJ (n+1-1) w * sphericalJ (n+1) w) / (2*n+1)))
    (fun n w => (cinSph_hasDerivAt_sq n w).const_mul _)
    (fun R => cinSph_bound_sq (fun n => (-1:ℂ)^n*(2*n+1)) (C := 2) (ρ := 2) zero_le_two
      (fun n => by
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact cinSph_norm_two_mul_add_one_le n) R |>.imp fun u hu =>
        ⟨hu.1, fun n w hw => by simpa [hf, mul_assoc] using hu.2 n w hw⟩)
  have hT : (fun w => ∑' n, f n w) = fun w => sphericalJ 0 (2*w) :=
    funext fun w => (sphProd_hasSum_alt_sq w).tsum_eq
  have hd : deriv (fun w => ∑' n, f n w) x = 2*(-sphericalJ 1 (2*x)) := by
    rw [hT]
    have := (sphSeries_hasDerivAt_sphericalJ_zero (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
    simpa [Function.comp_def, mul_comm] using this.deriv
  have h := hS x
  rw [hd] at h
  set q : ℕ → ℂ := fun n => (n:ℂ) * sphericalJ (n-1) x * sphericalJ n x with hq
  set c : ℕ → ℂ := fun n => 2*x*(-1:ℂ)^n with hc
  have hcb : ∀ n, ‖c n‖ ≤ 2*‖x‖ * 1^n := fun n => by simp [hc]
  obtain ⟨hs1, hs2⟩ := cinSph_summable_q c zero_le_one hcb x
  have hbp := cinSph_hasSum_by_parts (c := c) (q := q) (by simp [hq]) hs1
    (hs2.congr fun n => by simp [hq]) (h.congr_fun fun n => by
      have h3 : (2*n+1 : ℂ) ≠ 0 := by
        have : (0:ℝ) < 2*n+1 := by positivity
        exact_mod_cast this.ne'
      simp only [hf, hq, hc]
      field_simp
      ring)
  have := hbp.neg
  convert this using 1
  · funext n
    simp only [hq, hc, Nat.add_sub_cancel, pow_succ]
    push_cast
    ring
  · ring

/-- Termwise Euler derivative of `Si(2z) = ∑ 2z jₙ(z)²` (DLMF 6.10.4):
`∑ 4z² jₙ(z) jₙ₊₁(z) = 2z - sin 2z`. -/
theorem cinSph_hasSum_prod {x : ℂ} (hx : x ≠ 0) :
    HasSum (fun n : ℕ => 4*x^2*(sphericalJ n x*sphericalJ (n+1) x)) (2*x - sin (2*x)) := by
  set f : ℕ → ℂ → ℂ := fun n w => 2*w*sphericalJ n w^2 with hf
  set D : ℕ → ℂ → ℂ := fun n w =>
    ((n:ℂ) * sphericalJ (n-1) w - (n+1) * sphericalJ (n+1) w) / (2*n+1) with hD
  obtain ⟨-, hS⟩ := sphSeries_euler_hasSum 0 (f := f)
    (f' := fun n w => 2*sphericalJ n w^2 + 2*w*(2*sphericalJ n w*D n w))
    (fun n w => by
      have h := ((hasDerivAt_id w).const_mul 2).mul ((sphProd_hasDerivAt_sphericalJ n w).pow 2)
      refine h.congr_deriv ?_
      simp only [hD, id, Pi.pow_apply]
      ring)
    (fun R => by
      obtain ⟨u, hu, h⟩ := cinSph_bound_sq (fun _ => (1:ℂ)) (C := 1) (ρ := 1) zero_le_one
        (fun n => by simp) R
      refine ⟨fun n => 2*|R| * u n, hu.mul_left _, fun n w hw => ?_⟩
      have h1 := h n w hw
      rw [one_mul] at h1
      simp only [hf]
      rw [mul_assoc, norm_mul, norm_mul]
      simp only [Complex.norm_ofNat]
      have : ‖w‖ ≤ |R| := hw.le.trans (le_abs_self R)
      calc 2 * (‖w‖ * ‖sphericalJ n w ^ 2‖) ≤ 2 * (|R| * u n) := by gcongr
        _ = _ := by ring)
  have hY : (fun w => ∑' n, f n w) = fun w => sinInt (2*w) := by
    funext w
    have := (sinInt_spherical_series (2*w)).tsum_eq
    rw [show 2*w/2 = w by ring] at this
    exact this
  have h2x : (2:ℂ)*x ≠ 0 := mul_ne_zero two_ne_zero hx
  have hd : deriv (fun w => ∑' n, f n w) x = 2*(sin (2*x)/(2*x)) := by
    rw [hY]
    have := (hasDerivAt_sinInt_complex h2x).comp x ((hasDerivAt_id x).const_mul 2)
    simpa [Function.comp_def, mul_comm] using this.deriv
  have h := hS x
  rw [hd] at h
  have hsq := (sphProd_hasSum_sq x).mul_left (2*x)
  have := hsq.sub h
  convert this using 1
  · funext n
    have hm := sphProd_mul_deriv_sphericalJ n x
    simp only [hf, hD]
    linear_combination (4*x*sphericalJ n x) * hm
  · field_simp
    ring

/-- Euler derivative of the series of DLMF 6.10.5: `z S'(z) = 1 - cos 2z`. -/
theorem cinSph_euler {x : ℂ} (hx : x ≠ 0) :
    Differentiable ℂ (fun w => ∑' n, expIntSphericalCoeff n * sphericalJ n w^2) ∧
    x * deriv (fun w => ∑' n, expIntSphericalCoeff n * sphericalJ n w^2) x = 1 - cos (2*x) := by
  set f : ℕ → ℂ → ℂ := fun n w => expIntSphericalCoeff n * sphericalJ n w^2 with hf
  obtain ⟨hDS, hS⟩ := sphSeries_euler_hasSum 0 (f := f)
    (f' := fun n w => expIntSphericalCoeff n * (2 * ((n:ℂ) * sphericalJ (n-1) w * sphericalJ n w -
        ((n+1:ℕ):ℂ) * sphericalJ (n+1-1) w * sphericalJ (n+1) w) / (2*n+1)))
    (fun n w => (cinSph_hasDerivAt_sq n w).const_mul _)
    (fun R => cinSph_bound_sq _ (C := 6) (ρ := 4) (by norm_num) cinSph_norm_coeff_le R)
  refine ⟨hDS, ?_⟩
  set S' := deriv (fun w => ∑' n, f n w) x with hS'
  have h := hS x
  set q : ℕ → ℂ := fun n => (n:ℂ) * sphericalJ (n-1) x * sphericalJ n x with hq
  set c : ℕ → ℂ := fun n => 2*x*cinSphB n with hc
  have hcb : ∀ n, ‖c n‖ ≤ (6*‖x‖) * 2^n := fun n => by
    simp only [hc, norm_mul, Complex.norm_ofNat]
    have := cinSph_norm_b_le n
    nlinarith [norm_nonneg x]
  obtain ⟨hs1, hs2⟩ := cinSph_summable_q c zero_le_two hcb x
  have hbp := cinSph_hasSum_by_parts (c := c) (q := q) (by simp [hq]) hs1
    (hs2.congr fun n => by simp [hq]) (h.congr_fun fun n => by
      have h3 : (2*n+1 : ℂ) ≠ 0 := by
        have : (0:ℝ) < 2*n+1 := by positivity
        exact_mod_cast this.ne'
      simp only [hf, hq, hc, cinSph_coeff]
      field_simp
      ring)
  have hA := ((cinSph_hasSum_alt_prod x).mul_left x).add ((cinSph_hasSum_prod hx).mul_left (1/2))
  have hB := hbp.mul_left x
  have e := hB.unique (hA.congr_fun fun n => by
    simp only [hq, hc, Nat.add_sub_cancel]
    rw [show 2*x*cinSphB (n+1) - 2*x*cinSphB n = 2*x*(cinSphB (n+1) - cinSphB n) by ring,
      cinSph_b_succ]
    have hn : ((n:ℂ)+1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    push_cast
    field_simp
    ring)
  have h0 := sphSeries_mul_sphericalJ_zero (2*x)
  have h1 := sphSeries_sphericalJ_zero_sub (2*x)
  apply mul_left_cancel₀ hx
  linear_combination e - x*h1 + h0/2

/-- DLMF 6.10.5 in the form `∑ₙ aₙ jₙ(x)² = Cin(2x)`, including the vanishing term `n = 0`. -/
theorem cinSph_hasSum (x : ℂ) :
    HasSum (fun n => expIntSphericalCoeff n * sphericalJ n x^2) (cosIntCin (2*x)) := by
  set S : ℂ → ℂ := fun w => ∑' n, expIntSphericalCoeff n * sphericalJ n w^2 with hS
  have hDS : Differentiable ℂ S := (cinSph_euler one_ne_zero).1
  have hC : Differentiable ℂ (fun w => cosIntCin (2*w)) :=
    cosIntCin_entire.comp (differentiable_id.const_mul 2)
  have hode : ∀ w, w * deriv (fun w => S w - cosIntCin (2*w)) w +
      0 * (S w - cosIntCin (2*w)) = 0 := by
    intro w
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    rw [deriv_fun_sub (hDS w) (hC w)]
    have h2w : (2:ℂ)*w ≠ 0 := mul_ne_zero two_ne_zero hw
    have hd : deriv (fun w => cosIntCin (2*w)) w = 2*((1-cos (2*w))/(2*w)) := by
      have := (hasDerivAt_cosIntCin_complex h2w).comp w ((hasDerivAt_id w).const_mul 2)
      simpa [Function.comp_def, mul_comm] using this.deriv
    rw [hd]
    have he := (cinSph_euler hw).2
    rw [← hS] at he
    field_simp
    rw [mul_comm w 2]
    linear_combination he
  have h0 : ∀ m : ℕ, (0:ℂ) + m = 0 → iteratedDeriv m (fun w => S w - cosIntCin (2*w)) 0 = 0 := by
    intro m hm
    have hm0 : m = 0 := by exact_mod_cast (by simpa using hm : (m:ℂ) = 0)
    subst hm0
    simp only [iteratedDeriv_zero, mul_zero, hS]
    have ht : ∀ n, expIntSphericalCoeff n * sphericalJ n 0^2 = 0 := by
      intro n
      rcases n with _ | n
      · simp [expIntSphericalCoeff]
      · simp [sphProd_sphericalJ_succ_zero]
    simp [ht, cosIntCin]
  have hz := sphSeries_eq_zero_of_euler (hDS.sub hC) 0 hode h0 x
  obtain ⟨u, hu, h⟩ := cinSph_bound_sq _ (C := 6) (ρ := 4) (by norm_num) cinSph_norm_coeff_le
    (‖x‖+1)
  have hs : Summable (fun n => expIntSphericalCoeff n * sphericalJ n x^2) :=
    Summable.of_norm_bounded hu (fun n => h n x (by linarith))
  have : S x = cosIntCin (2*x) := by simp only [Pi.sub_apply] at hz; linear_combination hz
  rw [← this]
  exact hs.hasSum

/-- cosIntCin spherical series. -/
@[dlmf 6.10.E5]
theorem cosIntCin_spherical_series (z : ℂ) :
    HasSum (fun n : ℕ => expIntSphericalCoeff (n+1)*sphericalJ (n+1) (z/2)^2) (cosIntCin z) := by
  have h := cinSph_hasSum (z/2)
  rw [show 2*(z/2) = z by ring, ← hasSum_nat_add_iff' 1] at h
  simpa [expIntSphericalCoeff] using h

/-- expIntEi spherical series. -/
@[dlmf 6.10.E6]
theorem expIntEi_spherical_series {x : ℝ} (hx : x ≠ 0) :
    HasSum (fun n : ℕ => (-1 : ℂ)^n*((x : ℂ)-expIntSphericalCoeff n)*sphericalI n (x/2)^2) ((Real.expIntEi x : ℂ)-Real.eulerMascheroniConstant-Real.log |x|) := by
  have hE : ((Real.expIntEi x : ℂ) - Real.eulerMascheroniConstant - Real.log |x|) =
      -cosIntCin (I*x) - I*sinInt (I*x) := by
    have h := expIntEin_mul_I (I*x)
    rw [show I*(I*(x:ℂ)) = ((-x:ℝ):ℂ) by push_cast; ring_nf; rw [I_sq]; ring,
      expIntEin_ofReal] at h
    rw [Real.expIntEi, show -(x:ℂ) = ((-x:ℝ):ℂ) by push_cast; ring, expIntEin_ofReal,
      Complex.ofReal_re]
    push_cast
    linear_combination -h
  rw [hE]
  have hS := (sinInt_spherical_series (I*x)).mul_left (-I)
  have hC := cinSph_hasSum (I*x/2)
  rw [show 2*(I*(x:ℂ)/2) = I*x by ring] at hC
  convert hS.sub hC using 1
  · funext n
    rw [sphSeries_sphericalI_eq, show I*((x:ℂ)/2) = I*x/2 by ring, div_pow, ← pow_mul,
      show (I:ℂ)^(n*2) = (-1)^n by rw [mul_comm, pow_mul, I_sq]]
    have h1 : ((-1:ℂ)^n)⁻¹ * (-1)^n = 1 := inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))
    rw [div_eq_mul_inv]
    have hI : -I*(I*(x:ℂ)) = x := by ring_nf; rw [I_sq]; ring
    linear_combination (((x:ℂ) - expIntSphericalCoeff n) * sphericalJ n (I*x/2)^2) * h1 +
      (sphericalJ n (I*x/2)^2) * hI + (2*(x:ℂ)*sphericalJ n (I*x/2)^2) * I_sq
  · ring

/-- Ein spherical series. -/
@[dlmf 6.10.E8]
theorem Ein_spherical_series (z : ℂ) :
    HasSum (fun n : ℕ => z*exp (-z/2)*(2*(n+1)+1 : ℂ)/((n+1 : ℂ)*(n+2))*sphericalI (n+1) (z/2)) (expIntEin z-z*exp (-z/2)*sphericalI 0 (z/2)) := by
  have hx : ∀ w : ℂ, HasDerivAt (fun w : ℂ => w/2) (1/2) w := fun w => by
    simpa using (hasDerivAt_id w).div_const 2
  have he : ∀ w : ℂ, HasDerivAt (fun w : ℂ => exp (-w/2)) (exp (-w/2) * (-1/2)) w := fun w => by
    have := ((hasDerivAt_id w).neg.div_const 2).cexp
    simpa [neg_div] using this
  refine sphSeries_hasSum_of_hasDerivAt
    (f := fun n w => w*exp (-w/2)*(2*(n+1)+1 : ℂ)/((n+1 : ℂ)*(n+2))*sphericalI (n+1) (w/2))
    (g := fun n w => exp (-w/2) * (w/2) * (sphericalI n (w/2) - sphericalI (n+1) (w/2)) / (n+1))
    (F := fun w => expIntEin w-w*exp (-w/2)*sphericalI 0 (w/2))
    (fun n w => ?_) (fun w => ?_) (fun R => ?_) (fun w => ?_) ?_ z
  · have h := ((((hasDerivAt_id w).mul (he w)).mul_const ((2*(n+1)+1 : ℂ))).div_const
      ((n+1 : ℂ)*(n+2))).mul ((sphSeries_hasDerivAt_sphericalI_succ n (w/2)).comp w (hx w))
    refine h.congr_deriv ?_
    have hr := sphSeries_sphericalI_recurrence n (w/2)
    have h3 : (2*n+3 : ℂ) ≠ 0 := by
      have : (0:ℝ) < 2*n+3 := by positivity
      exact_mod_cast this.ne'
    have h1 : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have h2 : (n+2 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n+1)
    have hI : sphericalI (n+1) (w/2) = w/2 * (sphericalI n (w/2) - sphericalI (n+2) (w/2)) /
        (2*n+3) := by
      rw [eq_div_iff h3]; linear_combination -hr
    simp only [id, Function.comp_apply, Pi.mul_apply]
    push_cast
    rw [show (n:ℂ)+1+1 = n+2 by ring, show n+1+1 = n+2 from rfl, hI]
    field_simp
    ring
  · have ht : Tendsto (fun n : ℕ => ‖exp (-w/2) * (w/2) * (sphericalI n (w/2) -
        sphericalI (n+1) (w/2))‖) atTop (𝓝 0) := by
      simpa [Function.comp_def] using ((((sphSeries_tendsto_sphericalI (w/2)).sub
        ((sphSeries_tendsto_sphericalI (w/2)).comp (tendsto_add_atTop_nat 1))).const_mul
        (exp (-w/2) * (w/2))).norm)
    refine squeeze_zero_norm (fun n => ?_) ht
    rw [norm_div]
    have h1 : (1:ℝ) ≤ ‖((n:ℂ)+1)‖ := by
      rw [show ((n:ℂ)+1) = ((n+1:ℕ):ℂ) by push_cast; ring, Complex.norm_natCast]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    exact div_le_self (norm_nonneg _) h1
  · obtain ⟨u, hu, hu0, h⟩ := sphSeries_sphericalI_bound R
    refine ⟨fun n => |R| * Real.exp (|R|/2) * 2 * u (n+1),
      ((summable_nat_add_iff 1).mpr hu).mul_left _, fun n w hw => ?_⟩
    have hwR : ‖w‖ ≤ |R| := hw.le.trans (le_abs_self R)
    have hw2 : ‖w/2‖ ≤ R := by
      rw [norm_div]; simp only [Complex.norm_ofNat]; have := norm_nonneg w; linarith
    have hc : ‖((2*(n+1)+1 : ℂ))/((n+1 : ℂ)*(n+2))‖ ≤ 2 := by
      rw [show ((2*(n+1)+1 : ℂ))/((n+1 : ℂ)*(n+2)) = (((2*n+3:ℝ)/((n+1)*(n+2)) : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        div_le_iff₀ (by positivity)]
      nlinarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    have hE : ‖exp (-w/2)‖ ≤ Real.exp (|R|/2) := by
      refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [neg_div, norm_neg, norm_div]; simp only [Complex.norm_ofNat]; linarith
    have e : w*exp (-w/2)*(2*(n+1)+1 : ℂ)/((n+1 : ℂ)*(n+2))*sphericalI (n+1) (w/2) =
        w * exp (-w/2) * ((2*(n+1)+1 : ℂ)/((n+1 : ℂ)*(n+2))) * sphericalI (n+1) (w/2) := by ring
    simp only
    rw [e, norm_mul, norm_mul, norm_mul]
    have := h (n+1) (w/2) hw2
    gcongr
  · have hEin : expIntEin = primitive (dslope (fun t => 1 - exp (-t)) 0) := by
      funext v; rw [expIntEin_segment_integral, primitive_dslope_zero (by simp)]
    have h0 := hasDerivAt_primitive (differentiable_dslope_entire
      (f := fun t => 1 - exp (-t)) (by fun_prop) 0) w
    rw [← hEin] at h0
    have h := h0.sub (((hasDerivAt_id w).mul (he w)).mul
      ((sphSeries_hasDerivAt_sphericalI_zero (w/2)).comp w (hx w)))
    refine h.congr_deriv ?_
    have hd : dslope (fun t => 1 - exp (-t)) 0 w = exp (-w/2) * sphericalI 0 (w/2) := by
      rcases eq_or_ne w 0 with rfl | hw
      · rw [dslope_same]
        have : HasDerivAt (fun t : ℂ => 1 - exp (-t)) 1 0 := by
          simpa using ((hasDerivAt_id (0:ℂ)).neg.cexp).const_sub 1
        rw [this.deriv]; simp [sphSeries_sphericalI_zero_zero]
      · rw [dslope_of_ne _ hw, slope_def_field]
        have hs := sphSeries_mul_sphericalI_zero (w/2)
        have hsh : 1 - exp (-w) = 2 * exp (-w/2) * sinh (w/2) := by
          have e1 : exp (-w/2) * exp (w/2) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
          have e2 : exp (-w/2) * exp (-(w/2)) = exp (-w) := by rw [← Complex.exp_add]; ring_nf
          rw [Complex.sinh]
          linear_combination -e1 + e2
        field_simp
        simp only [neg_zero, Complex.exp_zero, sub_self, sub_zero]
        rw [hsh, ← hs]
        rw [neg_div]; ring
    simp only [id, Function.comp_apply, Pi.mul_apply]
    rw [hd]
    ring
  · simp [expIntEin]

/-- expIntE1 eq upperIncGamma. -/
@[dlmf 6.11.E1]
theorem expIntE1_eq_upperIncGamma {z : ℂ} (hz : z ≠ 0) :
    genExpIntE 1 z = upperIncGamma 0 z := by
  simp [genExpIntE]

/-- expIntE1 eq kummerU. -/
@[dlmf 6.11.E2]
theorem expIntE1_eq_kummerU {z : ℂ} (hz : z ≠ 0) :
    genExpIntE 1 z = exp (-z)*kummerU 1 1 z := by
  simpa only [show (2 : ℂ)-1=1 by norm_num] using genExpIntE_eq_exp_mul_kummerU 1 hz

/-- expIntAux eq kummerU. -/
@[dlmf 6.11.E3]
theorem expIntAux_eq_kummerU {z : ℂ} (hz : 0 < z.re) :
    expIntAuxG z+I*expIntAuxF z = kummerU 1 1 (-I*z) := by
  have h := expIntAux_eq_E1 hz (ε:=1) (Or.inl rfl)
  simp only [Complex.ofReal_one,one_mul,neg_mul] at h
  have hz0 : -I*z≠0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (ne_zero_of_re_pos hz)
  rw [show -(I*z)= -I*z by ring,expIntE1_eq_kummerU hz0] at h
  have he : exp (-(-I*z))*exp (-I*z)=1 := by rw [←Complex.exp_add]; simp
  linear_combination h+kummerU 1 1 (-I*z)*he

end DLMF.Confluent
