/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.AnalyticProperties
public import DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuationExistence
public import DLMF.GeneralizedHypergeometric.Basic
public import DLMF.Hypergeometric.Basic.GeneralizedCalculus
public import Mathlib.RingTheory.PowerSeries.Basic
public import DLMF.Hypergeometric.ArgumentContinuation
public import DLMF.Hypergeometric.Solutions
public import DLMF.Hypergeometric.Identities
public import DLMF.Hypergeometric.Saalschutz
public import DLMF.Hypergeometric.FiniteConvolution
public import DLMF.QHypergeometric.HigherSummations
public import DLMF.GeneralizedHypergeometric.WhippleTerminating

/-!
# `ₚF_q` at unit argument (DLMF §16.4)

## Main definitions

* `gen3F2UnitThomae`: the Thomae expression continuing `₃F₂(1)` in its parameters.

## Main results

* `generalizedHypergeometric_finite_ratio_sum`, `generalizedHypergeometric_finite_ratio_sum_closed`:
  DLMF 16.4.2_5.
* `generalizedHypergeometric_dixon_terminating_even`,
  `generalizedHypergeometric_dixon_terminating_odd`: Dixon's sum, DLMF 16.4.5.
* `generalizedHypergeometric_watson_sum`: Watson's sum, DLMF 16.4.6, with terminating forms.
* `generalizedHypergeometric_whipple_3F2_sum`, `generalizedHypergeometric_whipple_3F2_terminating`:
  Whipple's sum, DLMF 16.4.7–16.4.8.
* `generalizedHypergeometric_dougall_5F4_sum`: Dougall's `₅F₄(1)` sum, DLMF 16.4.9; the finite
  forms are in `DLMF.GeneralizedHypergeometric.UnitArgumentDougall`.
* `generalizedHypergeometric_3F2_unit_transformation`, `analyticOnNhd_gen3F2UnitThomae_params`: DLMF
  16.4.11.
* `generalizedHypergeometric_3F2_unit_recurrence`,
  `generalizedHypergeometric_3F2_unit_recurrence_two`: DLMF 16.4.12–16.4.13.
* `generalizedHypergeometric_balanced_4F3_transformation`: DLMF 16.4.14.
* `generalizedHypergeometric_whipple_general`,
  `generalizedHypergeometric_whipple_nonterminating_left`: Whipple's transformation, DLMF 16.4.15.
* `generalizedHypergeometric_dougall_bilateral`: Dougall's bilateral sum, DLMF 16.4.17.

## Implementation notes

The predicates `IsWellPoised`, `IsVeryWellPoised` and `IsKBalanced` (DLMF 16.4.1–16.4.2) are in
`DLMF.GeneralizedHypergeometric.Basic.ParametersAndSeries`. Finite parity and finite Dougall
identities use Pochhammer quotients, which retain the removable cases hidden by quotients of poles
in the printed Gamma formulas. Lower parameters retain the chapter's nonpositive-integer exclusions,
except the explicitly cancelled finite pair in 16.4.2_5. Convergence at unity is always stated
before a nonterminating sum is used. The odd terminating Dixon evaluation follows from finite
inversion. The bilateral evaluation uses `dougall_bilateral` and Mathlib's
`Complex.Gamma_mul_Gamma_one_sub`, preserving integral lower parameters. The terminating Watson sums
reduce to the terminating Dixon sums by Sheppard's transformation, taken from the binomial
convolution `terminating_3F2_convolution`; the balanced `₄F₃` transformation 16.4.14 is the
convolution form `balanced_4F3_convolution_of_regular` of Whipple's transformation.
-/

@[expose] public section
open Complex Filter Set Finset
open scoped Topology Real
noncomputable section
namespace DLMF.Hypergeometric

/-- The canceled finite 3F2 sum in a form without an artificial singularity at c=1. -/
@[dlmf 16.4.E2_5]
theorem generalizedHypergeometric_finite_ratio_sum (n : ℕ) (a c : ℂ)
    (hc : LowerParametersRegular {c}) :
    generalizedHypergeometricTruncated n {(-n : ℂ), a, 1} {(-n : ℂ), c} 1 =
      ∑ k ∈ range (n + 1), pochhammer a k / pochhammer c k ∧
    (c - a - 1) * (∑ k ∈ range (n + 1), pochhammer a k / pochhammer c k) =
      c - 1 - (c + n) * pochhammer a (n + 1) / pochhammer c (n + 1) := by
  have hc' (k : ℕ) : pochhammer c k ≠ 0 := pochhammer_ne_zero_of_not_neg_nat (hc c (by simp)) k
  constructor
  · unfold generalizedHypergeometricTruncated
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hn : pochhammer (-(n : ℂ)) k ≠ 0 := by
      rw [pochhammer_neg_coe_nat]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.cast_ne_zero.mpr ((Nat.descFactorial_pos.mpr hkn).ne'))
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    simp only [generalizedHypergeometricCoeff, pochhammerProduct, Multiset.insert_eq_cons,
        Multiset.map_cons,
        Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton, one_pow, mul_one, pochhammer_nat_one]
    field_simp [hn, hf, hc' k]
  · induction n with
    | zero =>
      have hc0 : c ≠ 0 := by simpa using hc c (by simp) 0
      simp only [sum_range_one, pochhammer_zero, pochhammer_one, div_one, Nat.cast_zero, add_zero,
          zero_add, mul_one]
      field_simp [hc0]
      ring
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pochhammer_succ a (n + 1), pochhammer_succ c (n + 1)]
      have hcn : c + (n + 1 : ℕ) ≠ 0 := by
        intro hzero
        exact hc c (by simp) (n + 1) (eq_neg_of_add_eq_zero_left hzero)
      field_simp [hc' (n + 1), hcn]
      push_cast
      ring

/-- The printed closed form wherever its displayed divisors are nonzero. -/
@[dlmf 16.4.E2_5]
theorem generalizedHypergeometric_finite_ratio_sum_closed (n : ℕ) (a c : ℂ)
    (hc : LowerParametersRegular {c})
    (hca : c - a - 1 ≠ 0) (hc1 : pochhammer (c - 1) (n + 1) ≠ 0) :
    (∑ k ∈ range (n + 1), pochhammer a k / pochhammer c k) =
      (c - 1) / (c - a - 1) * (1 - pochhammer a (n + 1) / pochhammer (c - 1) (n + 1)) := by
  have hC : pochhammer c (n + 1) ≠ 0 := pochhammer_ne_zero_of_not_neg_nat (hc c (by simp)) _
  have hcross : pochhammer (c - 1) (n + 1) * (c + n) = (c - 1) * pochhammer c (n + 1) := by
    rw [pochhammer_succ_left, show c - 1 + 1 = c by ring, pochhammer_succ c]
    ring
  have hratio : (c + n) * pochhammer a (n + 1) / pochhammer c (n + 1) =
      (c - 1) * pochhammer a (n + 1) / pochhammer (c - 1) (n + 1) := by
    field_simp
    linear_combination pochhammer a (n + 1) * hcross
  have h := (generalizedHypergeometric_finite_ratio_sum n a c hc).2
  rw [hratio] at h
  field_simp [hc1] at h
  field_simp [hca, hc1]
  linear_combination h

/-- The limiting c=a+1 form; a=0 is retained separately as the removable value one. -/
@[dlmf 16.4.E2_5]
theorem generalizedHypergeometric_finite_ratio_sum_limit (n : ℕ) (a : ℂ)
    (ha : LowerParametersRegular {a}) :
    (∑ k ∈ range (n + 1), pochhammer a k / pochhammer (a + 1) k) =
      a * (Complex.digamma (a + n + 1) - Complex.digamma a) ∧
    (∑ k ∈ range (n + 1), pochhammer a k / pochhammer (a + 1) k) =
      a * deriv (fun a : ℂ => pochhammer a (n + 1)) a / pochhammer a (n + 1) := by
  have ha' : ∀ k : ℕ, a ≠ -(k : ℂ) := ha a (by simp)
  have hap (k : ℕ) : a + k ≠ 0 := fun h => ha' k (eq_neg_of_add_eq_zero_left h)
  have hp1 (k : ℕ) : pochhammer (a + 1) k ≠ 0 :=
    by simpa only [Nat.cast_one] using pochhammer_ne_zero_of_not_neg_nat
         (not_neg_nat_add_nat ha' 1) k
  have hratio (k : ℕ) : pochhammer a k / pochhammer (a + 1) k = a / (a + k) := by
    have h := (pochhammer_succ a k).symm.trans (pochhammer_succ_left a k)
    field_simp [hp1 k, hap k]
    exact h
  have hsum : (∑ k ∈ range (n + 1), pochhammer a k / pochhammer (a + 1) k) =
      a * ∑ k ∈ range (n + 1), (a + k)⁻¹ := by
    simp_rw [hratio, div_eq_mul_inv]
    rw [Finset.mul_sum]
  constructor
  · rw [hsum, show a + n + 1 = a + (n + 1 : ℕ) by push_cast; ring,
      Complex.digamma_apply_add_nat ha']
    ring
  · have hprod : (fun x : ℂ => pochhammer x (n + 1)) =
        (fun x : ℂ => ∏ k ∈ range (n + 1), (x + k)) := by
      funext x
      simpa using pochhammer_mul_pow x 1 (n + 1)
    have hlog : deriv (fun x : ℂ => ∏ k ∈ range (n + 1), (x + k)) a /
          (∏ k ∈ range (n + 1), (a + k)) = ∑ k ∈ range (n + 1), (a + k)⁻¹ := by
      simpa [logDeriv_apply] using (logDeriv_fun_prod
        (s := range (n + 1)) (f := fun k (x : ℂ) => x + k)
        (fun k _ => hap k) (fun k _ => by fun_prop))
    rw [← hprod] at hlog
    have hvalue := congrFun hprod a
    change pochhammer a (n + 1) = ∏ k ∈ range (n + 1), (a + k) at hvalue
    rw [← hvalue] at hlog
    rw [hsum, mul_div_assoc, hlog]

/-- The removable limiting value at a=0,c=1. -/
@[dlmf 16.4.E2_5]
theorem generalizedHypergeometric_finite_ratio_sum_zero (n : ℕ) :
    (∑ k ∈ range (n + 1), pochhammer (0 : ℂ) k / pochhammer 1 k) = 1 := by
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pochhammer_zero_succ, zero_div, add_zero]

section DixonDegenerate

open Polynomial

/-- `1/Γ(y) = (y)_r / Γ(y + r)` for every `y` and every `r`. -/
private lemma recip_Gamma_eq_pochhammer_mul_recip (y : ℂ) (r : ℕ) :
    (Gamma y)⁻¹ = pochhammer y r * (Gamma (y + r))⁻¹ := by
  rcases r with _ | p
  · simp [pochhammer_zero]
  · exact recip_Gamma_eq_pochhammer_mul p y

/-- The polynomial side of the even degenerate Dixon sum. -/
private def dixonEvenT (k : ℕ) (b c : ℂ) : ℂ :=
  ∑ n ∈ range (2 * k + 1), gaussHypergeometricCoeff (-(2 * k : ℂ)) b (1 - 2 * k - b) n *
      pochhammer c n *
    pochhammer (1 - 2 * k + n - c) (2 * k - n)

/-- The product side of the even degenerate Dixon sum. -/
private def dixonEvenQ (k : ℕ) (b c : ℂ) : ℂ :=
  (2 * k).factorial / (k.factorial * pochhammer (b + k) k) * pochhammer c k *
      pochhammer (c + (b + k)) k

/-- The Dixon terms with `a = -2k` vanish beyond `2k`. -/
private lemma gaussHypergeometricCoeff_neg_two_mul_eq_zero (k : ℕ) (b c : ℂ) {n : ℕ}
    (hn : 2 * k < n) :
    gaussHypergeometricCoeff (-(2 * k : ℂ)) b c n = 0 := by
  have : pochhammer (-((2 * k : ℕ) : ℂ)) n = 0 := pochhammer_neg_nat_eq_zero hn
  push_cast at this
  simp [gaussHypergeometricCoeff, this]

/-- The normalized Dixon series with `a = -2k` is a finite sum. -/
private lemma normalizedSeries_neg_two_mul (k : ℕ) (b c : ℂ) :
    DixonWZ.normalizedSeries (-(2 * k : ℂ)) b c =
      ∑ n ∈ range (2 * k + 1), DixonWZ.s (-(2 * k : ℂ)) b c n := by
  unfold DixonWZ.normalizedSeries
  refine tsum_eq_sum fun n hn => ?_
  have : 2 * k < n := by simpa using hn
  simp [DixonWZ.s, gaussHypergeometricCoeff_neg_two_mul_eq_zero k b _ this]

/-- The WZ recurrence in `c` for the degenerate Dixon series `a = -2k`, valid for every `c`. -/
private lemma normalizedSeries_neg_two_mul_recurrence (k : ℕ) (b : ℂ)
    (hb : ∀ n : ℕ, 1 - 2 * k - b ≠ -n) (c : ℂ) :
    (1 - k - b - c) * DixonWZ.normalizedSeries (-(2 * k : ℂ)) b c =
      (1 - k - c) * (1 - 2 * k - b - c) * DixonWZ.normalizedSeries (-(2 * k : ℂ)) b (c - 1) := by
  have hsum : ∀ c', Summable (DixonWZ.s (-(2 * k : ℂ)) b c') := fun c' =>
    summable_of_ne_finset_zero (s := range (2 * k + 1)) fun n hn => by
      have : 2 * k < n := by simpa using hn
      simp [DixonWZ.s, gaussHypergeometricCoeff_neg_two_mul_eq_zero k b _ this]
  have hH : Tendsto (DixonWZ.wzCertificate (-(2 * k : ℂ)) b c) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (2 * k)] with n hn
    simp [DixonWZ.wzCertificate, gaussHypergeometricCoeff_neg_two_mul_eq_zero k b _ hn]
  have hb' : ∀ n : ℕ, 1 + -(2 * k : ℂ) - b ≠ -n := fun n h => hb n (by linear_combination h)
  have h := DixonWZ.recurrence hb' (hsum c) (hsum (c - 1)) hH
  convert h using 2 <;> ring

/-- At `c = -m` the polynomial side is `m!` times the normalized series. -/
private lemma dixonEvenT_neg_nat (k : ℕ) (b : ℂ) (m : ℕ) :
    dixonEvenT k b (-(m : ℂ)) = m.factorial *
      DixonWZ.normalizedSeries (-(2 * k : ℂ)) b (-(m : ℂ)) := by
  rw [normalizedSeries_neg_two_mul, mul_sum]
  refine sum_congr rfl fun n hn => ?_
  have hn' : n ≤ 2 * k := Nat.lt_succ_iff.mp (mem_range.mp hn)
  have hr := recip_Gamma_eq_pochhammer_mul_recip (1 + -(2 * k : ℂ) - -(m : ℂ) + n) (2 * k - n)
  rw [show 1 + -(2 * k : ℂ) - -(m : ℂ) + n + ((2 * k - n : ℕ) : ℂ) = (m : ℂ) + 1 by
    push_cast [hn']; ring, Complex.Gamma_nat_eq_factorial] at hr
  simp only [DixonWZ.s]
  rw [show (1 : ℂ) - 2 * k - b = 1 + -(2 * k : ℂ) - b by ring, hr,
    show (1 : ℂ) - 2 * k + n - -(m : ℂ) = 1 + -(2 * k : ℂ) - -(m : ℂ) + n by ring]
  have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  field_simp

/-- The recurrence of the polynomial side at the negative integers. -/
private lemma dixonEvenT_recurrence (k : ℕ) (b : ℂ) (hb : ∀ n : ℕ, 1 - 2 * k - b ≠ -n)
    (m : ℕ) :
    (1 + m) * (1 - k - b + m) * dixonEvenT k b (-(m : ℂ)) =
      (1 - k + m) * (1 - 2 * k - b + m) * dixonEvenT k b (-((m + 1 : ℕ) : ℂ)) := by
  have h := normalizedSeries_neg_two_mul_recurrence k b hb (-(m : ℂ))
  rw [dixonEvenT_neg_nat, dixonEvenT_neg_nat, show -(m : ℂ) - 1 = -((m + 1 : ℕ) : ℂ) by
    push_cast; ring] at *
  rw [Nat.factorial_succ]
  push_cast at h ⊢
  linear_combination ((m : ℂ) + 1) * m.factorial * h

/-- The recurrence of the product side, for every `c`. -/
private lemma dixonEvenQ_recurrence (k : ℕ) (b c : ℂ) :
    (1 - c) * (1 - k - b - c) * dixonEvenQ k b c =
      (1 - k - c) * (1 - 2 * k - b - c) * dixonEvenQ k b (c - 1) := by
  unfold dixonEvenQ
  have h1 : pochhammer (c - 1) k * (c - 1 + k) = (c - 1) * pochhammer c k := by
    rw [← pochhammer_succ, pochhammer_succ_left, sub_add_cancel]
  have h2 : pochhammer (c - 1 + (b + k)) k * (c - 1 + (b + k) + k) =
      (c - 1 + (b + k)) * pochhammer (c + (b + k)) k := by
    rw [← pochhammer_succ, pochhammer_succ_left]; ring_nf
  linear_combination ((2 * k).factorial / (k.factorial * pochhammer (b + k) k)) *
    (-((c - 1 + (b + k)) * pochhammer (c + (b + k)) k) * h1 - pochhammer (c - 1) k *
        (c - 1 + k) * h2)

/-- The two sides agree at `c = -k`, where only one term survives. -/
private lemma dixonEvenT_neg_self (k : ℕ) (b : ℂ) (hb : ∀ n : ℕ, 1 - 2 * k - b ≠ -n) :
    dixonEvenT k b (-(k : ℂ)) = dixonEvenQ k b (-(k : ℂ)) := by
  unfold dixonEvenT dixonEvenQ
  rw [sum_eq_single k]
  · have hP : pochhammer (1 - 2 * k - b) k ≠ 0 := pochhammer_ne_zero_of_not_neg_nat hb k
    have hR : pochhammer (1 - 2 * k - b) k = (-1) ^ k * pochhammer (b + k) k := by
      rw [← pochhammer_reflect]; ring_nf
    have hA : pochhammer (-(2 * k : ℂ)) k = (-1) ^ k * ((2 * k).factorial / k.factorial) := by
      have h1 := pochhammer_reflect ((k : ℂ) + 1) k
      have h2 := Complex.Gamma_add_nat_div_Gamma_eq (n := k) ((k : ℂ) + 1)
        (fun m hm => by
          have : ((k + 1 + m : ℕ) : ℂ) = 0 := by push_cast; linear_combination hm
          exact absurd (by exact_mod_cast this) (Nat.succ_ne_zero (k + m) ∘ by omega))
      rw [show (k : ℂ) + 1 + k = ((2 * k : ℕ) : ℂ) + 1 by push_cast; ring,
        show (k : ℂ) + 1 = ((k : ℕ) : ℂ) + 1 from rfl, Complex.Gamma_nat_eq_factorial,
        Complex.Gamma_nat_eq_factorial] at h2
      rw [show (1 : ℂ) - (k + 1) - k = -(2 * k) by ring] at h1
      rw [h1, pochhammer, ← h2]
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hp1 : pochhammer (1 - 2 * k + k - -(k : ℂ)) (2 * k - k) = k.factorial := by
      rw [show (1 : ℂ) - 2 * k + k - -(k : ℂ) = 1 by ring, show 2 * k - k = k by omega,
        pochhammer, ascPochhammer_eval_one]
    rw [hp1, gaussHypergeometricCoeff, hA, hR]
    have hB : pochhammer (b + k) k ≠ 0 := fun h0 => hP (by rw [hR, h0, mul_zero])
    field_simp
    rw [show -(k : ℂ) + (b + k) = b by ring]
  · intro n hn hnk
    rcases lt_or_gt_of_ne hnk with hlt | hgt
    · have : pochhammer (1 - 2 * k + n - -(k : ℂ)) (2 * k - n) = 0 := by
        have := pochhammer_neg_nat_eq_zero (n := k - 1 - n) (k := 2 * k - n) (by omega)
        rwa [show -(((k - 1 - n : ℕ) : ℂ)) = 1 - 2 * k + n - -(k : ℂ) by
          push_cast [show n ≤ k - 1 by omega, show 1 ≤ k by omega]; ring] at this
      rw [this, mul_zero]
    · have := pochhammer_neg_nat_eq_zero (n := k) (k := n) hgt
      rw [this, mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- The two sides agree at every `c = -m` with `m ≥ k`. -/
private lemma dixonEvenT_neg_add (k : ℕ) (b : ℂ) (hb : ∀ n : ℕ, 1 - 2 * k - b ≠ -n) (i : ℕ) :
    dixonEvenT k b (-((k + i : ℕ) : ℂ)) = dixonEvenQ k b (-((k + i : ℕ) : ℂ)) := by
  induction i with
  | zero => simpa using dixonEvenT_neg_self k b hb
  | succ i ih =>
    have hT := dixonEvenT_recurrence k b hb (k + i)
    have hQ := dixonEvenQ_recurrence k b (-((k + i : ℕ) : ℂ))
    rw [show -((k + i : ℕ) : ℂ) - 1 = -((k + i + 1 : ℕ) : ℂ) by push_cast; ring] at hQ
    have h1 : (1 - k + ((k + i : ℕ) : ℂ)) ≠ 0 := by
      push_cast; rw [show (1 : ℂ) - k + (k + i) = ((i + 1 : ℕ) : ℂ) by push_cast; ring]
      exact_mod_cast i.succ_ne_zero
    have h2 : (1 - 2 * k - b + ((k + i : ℕ) : ℂ)) ≠ 0 := fun h0 =>
      hb (k + i) (by linear_combination h0)
    have h3 := mul_ne_zero h1 h2
    rw [show k + (i + 1) = k + i + 1 by ring]
    apply mul_left_cancel₀ h3
    rw [← hT, ih]
    linear_combination hQ

/-- The polynomial and product sides of the even degenerate Dixon sum agree for every `c`. -/
private lemma dixonEvenT_eq_dixonEvenQ (k : ℕ) (b : ℂ) (hb : ∀ n : ℕ, 1 - 2 * k - b ≠ -n)
    (c : ℂ) : dixonEvenT k b c = dixonEvenQ k b c := by
  let Tp : ℂ[X] := ∑ n ∈ range (2 * k + 1),
    (C (gaussHypergeometricCoeff (-(2 * k : ℂ)) b (1 - 2 * k - b) n) : ℂ[X]) * ascPochhammer ℂ n *
      (ascPochhammer ℂ (2 * k - n)).comp ((C (1 - 2 * k + n : ℂ) : ℂ[X]) - X)
  let Qp : ℂ[X] := (C ((2 * k).factorial / (k.factorial * pochhammer (b + k) k) : ℂ) : ℂ[X]) *
    ascPochhammer ℂ k * (ascPochhammer ℂ k).comp (X + (C (b + k) : ℂ[X]))
  have hT : ∀ c, Tp.eval c = dixonEvenT k b c := fun c => by
    simp [Tp, dixonEvenT, Polynomial.eval_finsetSum, pochhammer]
  have hQ : ∀ c, Qp.eval c = dixonEvenQ k b c := fun c => by
    simp [Qp, dixonEvenQ, pochhammer]
  have h0 : Tp - Qp = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ (Set.infinite_of_injective_forall_mem
      (f := fun i : ℕ => -((k + i : ℕ) : ℂ)) (fun i j hij => by simpa using hij) fun i => ?_)
    simp only [Set.mem_ofPred_eq, IsRoot.def, eval_sub, hT, hQ]
    rw [dixonEvenT_neg_add k b hb i, sub_self]
  rw [← hT, ← hQ, sub_eq_zero.mp h0]

/-- Dixon's even terminating evaluation, assuming only that the finite Pochhammer product of
the second lower parameter is nonzero. -/
private lemma generalizedHypergeometric_dixon_terminating_even_of_pochhammer (k : ℕ) (b c : ℂ)
    (hb1 : ∀ n : ℕ, 1 - b - 2 * k ≠ -n) (hpc : pochhammer (1 - c - 2 * k) (2 * k) ≠ 0) :
    generalizedHypergeometricTruncated (2 * k) {(-(2 * k) : ℂ), b, c}
      {1 - b - 2 * k, 1 - c - 2 * k} 1 =
      (2 * k).factorial * pochhammer (b + c + k) k /
        (k.factorial * pochhammer (b + k) k * pochhammer (c + k) k) := by
  have hb2 : ∀ n : ℕ, 1 - 2 * k - b ≠ -n := fun n h => hb1 n (by linear_combination h)
  have hrc : pochhammer (1 - c - 2 * k) (2 * k) = pochhammer c k * pochhammer (c + k) k := by
    have := pochhammer_reflect c (2 * k)
    push_cast at this
    rw [this, show 2 * k = k + k by ring, pochhammer_add, pow_add,
                                      ← pow_mul_pow_sub (-1 : ℂ) le_rfl]
    simp [← sq, ← pow_mul]
  have hck : pochhammer (c + k) k ≠ 0 := fun h0 => hpc (by rw [hrc, h0, mul_zero])
  have hrb : pochhammer (1 - 2 * k - b) k = (-1) ^ k * pochhammer (b + k) k := by
    rw [← pochhammer_reflect]; ring_nf
  have hbk : pochhammer (b + k) k ≠ 0 := fun h0 =>
    pochhammer_ne_zero_of_not_neg_nat hb2 k (by rw [hrb, h0, mul_zero])
  apply mul_right_cancel₀ hpc
  have hL : generalizedHypergeometricTruncated (2 * k) {(-(2 * k) : ℂ), b, c}
      {1 - b - 2 * k, 1 - c - 2 * k} 1 *
      pochhammer (1 - c - 2 * k) (2 * k) = dixonEvenT k b c := by
    unfold generalizedHypergeometricTruncated dixonEvenT
    rw [sum_mul]
    refine sum_congr rfl fun n hn => ?_
    have hn' : n ≤ 2 * k := Nat.lt_succ_iff.mp (mem_range.mp hn)
    have hsplit : pochhammer (1 - c - 2 * k) (2 * k) =
        pochhammer (1 - c - 2 * k) n * pochhammer (1 - 2 * k + n - c) (2 * k - n) := by
      rw [← show 1 - c - 2 * k + n = 1 - 2 * k + n - c by ring, ← pochhammer_add,
        Nat.add_sub_cancel' hn']
    have h1 := pochhammer_ne_zero_of_not_neg_nat hb1 n
    have h2 : pochhammer (1 - c - 2 * k) n ≠ 0 := left_ne_zero_of_mul (hsplit ▸ hpc)
    have h3 : pochhammer (1 - 2 * k - b) n = pochhammer (1 - b - 2 * k) n := by ring_nf
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    simp only [generalizedHypergeometricCoeff, pochhammerProduct, Multiset.insert_eq_cons,
        Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, one_pow, mul_one,
      gaussHypergeometricCoeff, hsplit, h3]
    field_simp
  rw [hL, dixonEvenT_eq_dixonEvenQ k b hb2, dixonEvenQ, hrc]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [show c + (b + k) = b + c + k by ring]
  field_simp

/-- Dixon even terminating evaluation with all removable Gamma ratios replaced by finite products.
-/
@[dlmf 16.4.E5]
theorem generalizedHypergeometric_dixon_terminating_even (k : ℕ) (b c : ℂ)
    (hb : LowerParametersRegular {1 - b - 2 * k, 1 - c - 2 * k}) :
    generalizedHypergeometricTruncated (2 * k) {(-(2 * k) : ℂ), b, c}
      {1 - b - 2 * k, 1 - c - 2 * k} 1 =
      (2 * k).factorial * pochhammer (b + c + k) k /
        (k.factorial * pochhammer (b + k) k * pochhammer (c + k) k) :=
  generalizedHypergeometric_dixon_terminating_even_of_pochhammer k b c (hb _ (by simp))
    (pochhammer_ne_zero_of_not_neg_nat (hb _ (by simp)) _)

end DixonDegenerate

/-- Dixon's odd terminating evaluation, assuming only that the finite Pochhammer product of
the lower parameters is nonzero. -/
private lemma generalizedHypergeometric_dixon_terminating_odd_of_pochhammer (k : ℕ) (b c : ℂ)
    (hB : pochhammerProduct {1 - b - ((2 * k + 1 : ℕ) : ℂ), 1 - c - ((2 * k + 1 : ℕ) : ℂ)}
      (2 * k + 1) ≠ 0) :
    generalizedHypergeometricTruncated (2 * k + 1) {(-(2 * k + 1) : ℂ), b, c}
      {1 - b - (2 * k + 1), 1 - c - (2 * k + 1)} 1 = 0 := by
  let N := 2 * k + 1
  have hs : (-1 : ℂ) ^ N = -1 := by simp [N, pow_add, pow_mul]
  have hp : pochhammerProduct {1 - b - N, 1 - c - N} N = pochhammerProduct {b, c} N := by
    simp only [pochhammerProduct, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
    rw [pochhammer_reflect b N, pochhammer_reflect c N, hs]
    ring
  have hA : pochhammerProduct {b, c} N ≠ 0 := by rw [← hp]; exact hB
  have hRA : ({b, c} : Multiset ℂ).map (fun x => 1 - (N : ℂ) - x) =
      {1 - b - N, 1 - c - N} := by
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    congr 1
    · ring
    · congr 1
      ring
  have hRB : ({1 - b - N, 1 - c - N} : Multiset ℂ).map
      (fun x => 1 - (N : ℂ) - x) = {b, c} := by
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    congr 1
    · ring
    · congr 1
      ring
  have hi := generalizedHypergeometricTruncated_inversion {b, c} {1 - b - N, 1 - c - N} N
    (z := 1) (by norm_num) hA hB
  rw [hRA, hRB, hs, hp, mul_neg_one, neg_div, div_self hA] at hi
  norm_num [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton] at hi
  have hzero : generalizedHypergeometricTruncated N ((-(N : ℂ)) ::ₘ {b, c})
      {1 - b - N, 1 - c - N} 1 = 0 := by
    linear_combination hi / 2
  simpa only [N, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      Multiset.insert_eq_cons] using hzero

/-- Dixon odd terminating evaluation, retaining every regular lower-parameter case. -/
@[dlmf 16.4.E5]
theorem generalizedHypergeometric_dixon_terminating_odd (k : ℕ) (b c : ℂ)
    (hb : LowerParametersRegular {1 - b - (2 * k + 1), 1 - c - (2 * k + 1)}) :
    generalizedHypergeometricTruncated (2 * k + 1) {(-(2 * k + 1) : ℂ), b, c}
      {1 - b - (2 * k + 1), 1 - c - (2 * k + 1)} 1 = 0 :=
  generalizedHypergeometric_dixon_terminating_odd_of_pochhammer k b c (by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      pochhammerProduct_ne_zero hb (2 * k + 1))

/-- Sheppard's terminating `₃F₂(1)` transformation, multiplied out so that only the lower
parameter `R` needs to avoid the nonpositive integers. -/
theorem generalizedHypergeometricTruncated_sheppard (n : ℕ) (P Q R D : ℂ) (hR : ∀ k : ℕ, R ≠ -k)
    (hD : pochhammer D n ≠ 0) (hDP : pochhammer (1 - D + P - n) n ≠ 0) :
    pochhammer D n * generalizedHypergeometricTruncated n {(-n : ℂ), Q, P} {R, D} 1 =
      pochhammer (D - P) n *
          generalizedHypergeometricTruncated n {(-n : ℂ), P, R - Q} {R, 1 + P - D - n} 1 := by
  have hconv := terminating_3F2_convolution P Q R D (pochhammer_ne_zero_of_not_neg_nat hR) n
  have hch (k : ℕ) : (-1 : ℂ) ^ k * n.choose k * k.factorial = pochhammer (-(n : ℂ)) k := by
    rw [pochhammer_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast; ring
  simp only [generalizedHypergeometricTruncated, generalizedHypergeometricCoeff, pochhammerProduct,
      Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, one_pow, mul_one]
  rw [mul_sum, mul_sum]
  convert hconv using 1
  · refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
    have hDn : pochhammer D n = pochhammer D k * pochhammer (D + k) (n - k) := by
      rw [← pochhammer_add, Nat.add_sub_cancel' hk']
    have hDk : pochhammer D k ≠ 0 := left_ne_zero_of_mul (hDn ▸ hD)
    have hRk := pochhammer_ne_zero_of_not_neg_nat hR k
    have hkf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    rw [← hch, hDn]
    field_simp
  · refine sum_congr rfl fun j hj => ?_
    have hj' : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
    have hn : n = (n - j) + j := by omega
    have hsplit : pochhammer (D - P) n =
        pochhammer (D - P) (n - j) * pochhammer (D - P + ((n - j : ℕ) : ℂ)) j := by
      rw [← pochhammer_add, ← hn]
    have hrefl : pochhammer (1 + P - D - n) j = (-1) ^ j *
        pochhammer (D - P + ((n - j : ℕ) : ℂ)) j := by
      rw [← pochhammer_reflect]; congr 1; push_cast [Nat.cast_sub hj']; ring
    have hsplit2 : pochhammer (1 - D + P - n) n = pochhammer (1 - D + P - n) j *
        pochhammer (1 - D + P - n + j) (n - j) := by
      rw [← pochhammer_add, Nat.add_sub_cancel' hj']
    have h1 : pochhammer (1 + P - D - n) j ≠ 0 := by
      have := left_ne_zero_of_mul (hsplit2 ▸ hDP)
      rwa [show 1 - D + P - (n : ℂ) = 1 + P - D - n by ring] at this
    rw [hrefl] at h1
    have h1' := right_ne_zero_of_mul h1
    have hRj := pochhammer_ne_zero_of_not_neg_nat hR j
    have hjf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    rw [← hch, hsplit, hrefl]
    field_simp

/-- Duplication for Pochhammer symbols: `(x)₂ₙ = 4ⁿ (x/2)ₙ ((x+1)/2)ₙ`. -/
private lemma pochhammer_two_mul_eq_four_pow_mul_pochhammer (x : ℂ) (n : ℕ) :
    pochhammer x (2 * n) = 4 ^ n * pochhammer (x / 2) n * pochhammer ((x + 1) / 2) n := by
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, pochhammer_succ, pochhammer_succ, ih,
                                              pochhammer_succ, pochhammer_succ]
    push_cast
    ring

/-- Watson sum in the full absolute convergence half-space. -/
@[dlmf 16.4.E6]
theorem generalizedHypergeometric_watson_sum (a b c : ℂ)
    (hb : LowerParametersRegular {(a + b + 1) / 2, 2 * c})
    (hconv : -1 < (2 * c - a - b).re) :
    generalizedHypergeometric {a, b, c} {(a + b + 1) / 2, 2 * c} 1 =
      Gamma (1 / 2) * Gamma (c + 1 / 2) * Gamma ((a + b + 1) / 2) *
      Gamma (c + (1 - a - b) / 2) /
      (Gamma ((a + 1) / 2) * Gamma ((b + 1) / 2) *
        Gamma (c + (1 - a) / 2) * Gamma (c + (1 - b) / 2)) := by
  sorry

/-- Watson even terminating evaluation without extra Gamma-pole exclusions. -/
@[dlmf 16.4.E6]
theorem generalizedHypergeometric_watson_terminating_even (k : ℕ) (b c : ℂ)
    (hb : LowerParametersRegular {(b - 2 * k + 1) / 2, 2 * c}) :
    generalizedHypergeometricTruncated (2 * k) {(-(2 * k) : ℂ), b, c}
      {(b - 2 * k + 1) / 2, 2 * c} 1 =
      pochhammer (1 / 2) k * pochhammer (c + (1 - b) / 2) k /
        (pochhammer ((1 - b) / 2) k * pochhammer (c + 1 / 2) k) := by
  set R : ℂ := (b - 2 * k + 1) / 2 with hRdef
  have hR : ∀ m : ℕ, R ≠ -m := hb _ (by simp)
  have h2c : ∀ m : ℕ, 2 * c ≠ -m := hb _ (by simp)
  have hD := pochhammer_ne_zero_of_not_neg_nat h2c (2 * k)
  have hdup := pochhammer_two_mul_eq_four_pow_mul_pochhammer (2 * c) k
  rw [show 2 * c / 2 = c by ring, show (2 * c + 1) / 2 = c + 1 / 2 by ring] at hdup
  have hc2 : pochhammer c (2 * k) = pochhammer c k * pochhammer (c + k) k := by
    rw [two_mul, pochhammer_add]
  have hcn : pochhammer c (2 * k) ≠ 0 := by
    intro h0
    rw [hc2] at h0
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact hD (by rw [hdup, h0]; ring)
    · obtain ⟨i, hi, hi'⟩ := (ascPochhammer_eval_eq_zero_iff (R := ℂ) k (c + k)).1 h0
      exact h2c (2 * (k + i)) (by push_cast; linear_combination 2 * hi')
  have hrefl : pochhammer (1 - 2 * c + c - ((2 * k : ℕ) : ℂ)) (2 * k) =
      (-1) ^ (2 * k) * pochhammer c (2 * k) := by
    rw [← pochhammer_reflect]; congr 1; ring
  have hDP : pochhammer (1 - 2 * c + c - ((2 * k : ℕ) : ℂ)) (2 * k) ≠ 0 := by
    rw [hrefl]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hcn
  have hsh := generalizedHypergeometricTruncated_sheppard (2 * k) c b R (2 * c) hR hD hDP
  have hR1 : ∀ m : ℕ, 1 - (R - b) - 2 * k ≠ -m := fun m h => hR m (by
    rw [← h, hRdef]; ring)
  have hpc : pochhammer (1 - c - 2 * k) (2 * k) ≠ 0 := by
    convert hDP using 2; push_cast; ring
  have hdx := generalizedHypergeometric_dixon_terminating_even_of_pochhammer k (R - b) c hR1 hpc
  have hG : generalizedHypergeometricTruncated (2 * k) {(-((2 * k : ℕ) : ℂ)), c, R - b}
      {R, 1 + c - 2 * c - ((2 * k : ℕ) : ℂ)} 1 =
      generalizedHypergeometricTruncated (2 * k) {(-(2 * k) : ℂ), R - b, c}
          {1 - (R - b) - 2 * k, 1 - c - 2 * k} 1 := by
    congr 1
    · rw [Multiset.pair_comm c (R - b)]
      push_cast
      rfl
    · simp only [Multiset.insert_eq_cons]
      push_cast
      congr 1
      · rw [hRdef]; ring
      · congr 1; ring
  have hL : generalizedHypergeometricTruncated (2 * k) {(-((2 * k : ℕ) : ℂ)), b, c} {R, 2 * c} 1 =
      generalizedHypergeometricTruncated (2 * k) {(-(2 * k) : ℂ), b, c}
          {(b - 2 * k + 1) / 2, 2 * c} 1 := by
    push_cast; rfl
  rw [← hL]
  rw [hG, hdx] at hsh
  have hRb : R - b + k = (1 - b) / 2 := by rw [hRdef]; ring
  have hRbc : R - b + c + k = c + (1 - b) / 2 := by rw [hRdef]; ring
  rw [hRb, hRbc] at hsh
  have hb2 : pochhammer ((1 - b) / 2) k ≠ 0 := by
    have := pochhammer_reflect R k
    rw [show 1 - R - k = (1 - b) / 2 by rw [hRdef]; ring] at this
    rw [this]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pochhammer_ne_zero_of_not_neg_nat hR k)
  have hck : pochhammer (c + k) k ≠ 0 := right_ne_zero_of_mul (hc2 ▸ hcn)
  have hc0 : pochhammer c k ≠ 0 := left_ne_zero_of_mul (hc2 ▸ hcn)
  have hch : pochhammer (c + 1 / 2) k ≠ 0 := by
    intro h0; exact hD (by rw [hdup, h0]; ring)
  have hfac := pochhammer_two_mul_eq_four_pow_mul_pochhammer 1 k
  rw [show ((1 : ℂ) + 1) / 2 = 1 by norm_num, pochhammer_nat_one, pochhammer_nat_one] at hfac
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h4 : (4 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [hdup, show 2 * c - c = c by ring, hc2,
    show ((2 * k).factorial : ℂ) = 4 ^ k * pochhammer (1 / 2) k * k.factorial by
      exact_mod_cast hfac] at hsh
  rw [eq_div_iff (mul_ne_zero hb2 hch)]
  field_simp at hsh
  rw [show (c * 2 + 1) / 2 = c + 1 / 2 by ring, show c * 2 = 2 * c by ring,
    show (2 * c + (1 - b)) / 2 = c + (1 - b) / 2 by ring] at hsh
  linear_combination hsh

/-- Watson odd terminating evaluation for every regular displayed lower parameter. -/
@[dlmf 16.4.E6]
theorem generalizedHypergeometric_watson_terminating_odd (k : ℕ) (b c : ℂ)
    (hb : LowerParametersRegular {(b - (2 * k + 1) + 1) / 2, 2 * c}) :
    generalizedHypergeometricTruncated (2 * k + 1) {(-(2 * k + 1) : ℂ), b, c}
      {(b - (2 * k + 1) + 1) / 2, 2 * c} 1 = 0 := by
  set R : ℂ := (b - (2 * k + 1) + 1) / 2 with hRdef
  have hR : ∀ m : ℕ, R ≠ -m := hb _ (by simp)
  have h2c : ∀ m : ℕ, 2 * c ≠ -m := hb _ (by simp)
  have hD := pochhammer_ne_zero_of_not_neg_nat h2c (2 * k + 1)
  have hcn : pochhammer c (2 * k + 1) ≠ 0 := by
    refine pochhammer_ne_zero_of_not_neg_nat (fun m hm => ?_) _
    exact h2c (2 * m) (by push_cast; linear_combination 2 * hm)
  have hrefl : pochhammer (1 - 2 * c + c - ((2 * k + 1 : ℕ) : ℂ)) (2 * k + 1) =
      (-1) ^ (2 * k + 1) * pochhammer c (2 * k + 1) := by
    rw [← pochhammer_reflect]; congr 1; ring
  have hDP : pochhammer (1 - 2 * c + c - ((2 * k + 1 : ℕ) : ℂ)) (2 * k + 1) ≠ 0 := by
    rw [hrefl]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hcn
  have hsh := generalizedHypergeometricTruncated_sheppard (2 * k + 1) c b R (2 * c) hR hD hDP
  have hB : pochhammerProduct {1 - (R - b) - ((2 * k + 1 : ℕ) : ℂ), 1 - c - ((2 * k + 1 : ℕ) : ℂ)}
      (2 * k + 1) ≠ 0 := by
    simp only [pochhammerProduct, Multiset.insert_eq_cons, Multiset.map_cons,
        Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton]
    refine mul_ne_zero ?_ ?_
    · convert pochhammer_ne_zero_of_not_neg_nat hR (2 * k + 1) using 2
      rw [hRdef]; push_cast; ring
    · convert hDP using 2; ring
  have hdx := generalizedHypergeometric_dixon_terminating_odd_of_pochhammer k (R - b) c hB
  have hG : generalizedHypergeometricTruncated (2 * k + 1) {(-((2 * k + 1 : ℕ) : ℂ)), c, R - b}
      {R, 1 + c - 2 * c - ((2 * k + 1 : ℕ) : ℂ)} 1 =
      generalizedHypergeometricTruncated (2 * k + 1) {(-(2 * k + 1) : ℂ), R - b, c}
        {1 - (R - b) - (2 * k + 1), 1 - c - (2 * k + 1)} 1 := by
    congr 1
    · rw [Multiset.pair_comm c (R - b)]
      push_cast
      rfl
    · simp only [Multiset.insert_eq_cons]
      push_cast
      congr 1
      · rw [hRdef]; ring
      · congr 1; ring
  rw [hG, hdx, mul_zero] at hsh
  have hL : generalizedHypergeometricTruncated (2 * k + 1)
      {(-((2 * k + 1 : ℕ) : ℂ)), b, c} {R, 2 * c} 1 =
      generalizedHypergeometricTruncated (2 * k + 1) {(-(2 * k + 1) : ℂ), b, c}
        {(b - (2 * k + 1) + 1) / 2, 2 * c} 1 := by
    push_cast; rfl
  rw [← hL]
  exact (mul_eq_zero.mp hsh).resolve_left hD

/-- Whipple 3F2 sum, including every terminating integer a. -/
@[dlmf 16.4.E7]
theorem generalizedHypergeometric_whipple_3F2_sum (a c d : ℂ)
    (hb : LowerParametersRegular {d, 2 * c - d + 1})
    (h : 0 < c.re ∨ ∃ n : ℤ, a = n) :
    generalizedHypergeometric {a, 1 - a, c} {d, 2 * c - d + 1} 1 =
      Real.pi * Gamma d * Gamma (2 * c - d + 1) * (2 : ℂ) ^ (1 - 2 * c) /
      (Gamma (c + (a - d + 1) / 2) * Gamma (c + 1 - (a + d) / 2) *
        Gamma ((a + d) / 2) * Gamma ((d - a + 1) / 2)) := by
  sorry

/-- Whipple terminating 3F2 sum in finite products. -/
@[dlmf 16.4.E8]
theorem generalizedHypergeometric_whipple_3F2_terminating (n : ℕ) (a d : ℂ)
    (hb : LowerParametersRegular {d, 1 - d - 2 * n}) :
    generalizedHypergeometricTruncated n {(-n : ℂ), a, 1 - a} {d, 1 - d - 2 * n} 1 =
      pochhammer ((a + d) / 2) n * pochhammer ((d - a + 1) / 2) n /
        (pochhammer (d / 2) n * pochhammer ((d + 1) / 2) n) :=
  generalizedHypergeometricTruncated_whipple_sum n a d hb

/-- Dougall very well-poised 5F4 in its full absolute convergence half-space. -/
@[dlmf 16.4.E9]
theorem generalizedHypergeometric_dougall_5F4_sum (a b c d : ℂ)
    (hb : LowerParametersRegular {a / 2, a - b + 1, a - c + 1, a - d + 1})
    (hconv : (b + c + d - a).re < 1) :
    generalizedHypergeometric {a, a / 2 + 1, b, c, d} {a / 2, a - b + 1, a - c + 1, a - d + 1} 1 =
      Gamma (a - b + 1) * Gamma (a - c + 1) * Gamma (a - d + 1) *
        Gamma (a - b - c - d + 1) /
      (Gamma (a + 1) * Gamma (a - b - c + 1) *
        Gamma (a - b - d + 1) * Gamma (a - c - d + 1)) := by
  sorry


/-- The two convergent 3F2 unity sums in the common region. -/
@[dlmf 16.4.E11]
theorem generalizedHypergeometric_3F2_unit_transformation (a b c d e : ℂ)
    (hb : LowerParametersRegular {d, e, d + e - b - c})
    (hconv : 0 < (d + e - a - b - c).re) (hea : 0 < (e - a).re) :
    generalizedHypergeometric {a, b, c} {d, e} 1 = Gamma e * Gamma (d + e - a - b - c) /
      (Gamma (e - a) * Gamma (d + e - b - c)) *
      generalizedHypergeometric {a, d - b, d - c} {d, d + e - b - c} 1 := by
  sorry

/-- A balanced three-over-two unit series sums to the declared value throughout its
absolute-convergence region, including every terminating upper-parameter case. -/
private lemma hasSum_gen3F2_one {a b c d e : ℂ} (hb : LowerParametersRegular {d, e})
    (hconv : 0 < (d + e - a - b - c).re ∨ IsTerminating {a, b, c}) :
    HasSum (generalizedHypergeometricCoeff {a, b, c} {d, e})
        (generalizedHypergeometric {a, b, c} {d, e} 1) := by
  rcases hconv with hconv | ha
  · apply generalizedHypergeometric_one_hasSum (by simp) hb
    have hE : parameterExcess {a, b, c} {d, e} = d + e - a - b - c := by
      simp only [parameterExcess, Multiset.insert_eq_cons, Multiset.sum_cons,
          Multiset.sum_singleton]
      ring
    rw [hE]
    exact hconv
  · exact generalizedHypergeometric_one_hasSum_of_summable hb
        (generalizedHypergeometricCoeff_summable_of_terminates ha)

/-- Consecutive coefficients of the second unity recurrence form an exact telescope. -/
private lemma generalizedHypergeometricCoeff_second_unit_recurrence_telescope (a b c d e : ℂ)
    (hb : LowerParametersRegular {d, d + 1, e, e + 1}) (n : ℕ) :
    generalizedHypergeometricCoeff {a, b, c} {d, e} (n + 1) -
      c * (e - a) / (d * e) *
          generalizedHypergeometricCoeff {a, b + 1, c + 1} {d + 1, e + 1} (n + 1) -
      (d - c) / d * generalizedHypergeometricCoeff {a, b + 1, c} {d + 1, e} (n + 1) =
      a * c / (d * e) * (generalizedHypergeometricCoeff {a + 1, b + 1, c + 1}
          {d + 1, e + 1} (n + 1) -
        generalizedHypergeometricCoeff {a + 1, b + 1, c + 1} {d + 1, e + 1} n) := by
  have hd : d ≠ 0 := by simpa using hb d (by simp) 0
  have he : e ≠ 0 := by simpa using hb e (by simp) 0
  have hdP : pochhammer (d + 1) n ≠ 0 := pochhammer_ne_zero_of_not_neg_nat (hb (d + 1) (by simp)) n
  have heP : pochhammer (e + 1) n ≠ 0 := pochhammer_ne_zero_of_not_neg_nat (hb (e + 1) (by simp)) n
  have hdn : d + 1 + n ≠ 0 := by
    intro hx
    exact hb (d + 1) (by simp) n (by linear_combination hx)
  have hen : e + 1 + n ≠ 0 := by
    intro hx
    exact hb (e + 1) (by simp) n (by linear_combination hx)
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  simp only [generalizedHypergeometricCoeff, pochhammerProduct, Multiset.insert_eq_cons,
      Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
  simp only [pochhammer_succ_left a n, pochhammer_succ_left b n, pochhammer_succ_left c n,
    pochhammer_succ_left d n, pochhammer_succ_left e n]
  simp only [pochhammer_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp [hd, he, hdP, heP, hdn, hen, hf, hn]
  ring

/-- Raising one regular lower parameter gives a linear relation between coefficients. -/
private lemma generalizedHypergeometricCoeff_lower_add_one (a b c d e : ℂ)
    (hb : LowerParametersRegular {d, e}) (n : ℕ) :
    (d + n) * generalizedHypergeometricCoeff {a, b, c} {d + 1, e} n = d *
        generalizedHypergeometricCoeff {a, b, c} {d, e} n := by
  have hd : d ≠ 0 := by simpa using hb d (by simp) 0
  have hdn : d + n ≠ 0 := by
    intro hx
    exact hb d (by simp) n (by linear_combination hx)
  have hdP : pochhammer d n ≠ 0 := pochhammer_ne_zero_of_not_neg_nat (hb d (by simp)) n
  have heP : pochhammer e n ≠ 0 := pochhammer_ne_zero_of_not_neg_nat (hb e (by simp)) n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hp : pochhammer (d + 1) n = pochhammer d n * (d + n) / d := by
    apply (eq_div_iff hd).2
    rw [← pochhammer_succ, pochhammer_succ_left]
    ring
  simp only [generalizedHypergeometricCoeff, pochhammerProduct, Multiset.insert_eq_cons,
      Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
  rw [hp]
  field_simp [hd, hdn, hdP, heP, hf]

/-- The first unit recurrence is an exact difference of adjacent weighted coefficients. -/
private lemma generalizedHypergeometricCoeff_first_unit_recurrence_telescope (a b c d e : ℂ)
    (hb : LowerParametersRegular {d - 1, d, d + 1, e}) (n : ℕ) :
    (a - d) * (b - d) * (c - d) *
      (generalizedHypergeometricCoeff {a, b, c} {d + 1, e} n -
          generalizedHypergeometricCoeff {a, b, c} {d, e} n) +
      a * b * c * generalizedHypergeometricCoeff {a, b, c} {d, e} n -
      d * (d - 1) * (a + b + c - d - e + 1) *
        (generalizedHypergeometricCoeff {a, b, c} {d, e} n -
            generalizedHypergeometricCoeff {a, b, c} {d - 1, e} n) =
      d * ((n + 1) * (e + n) * generalizedHypergeometricCoeff {a, b, c} {d, e} (n + 1) -
        n * (e + n - 1) * generalizedHypergeometricCoeff {a, b, c} {d, e} n) := by
  have hb0 : LowerParametersRegular {d, e} := by
    intro z hz
    exact hb z (by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
                     at hz ⊢; tauto)
  have hbm : LowerParametersRegular {d - 1, e} := by
    intro z hz
    exact hb z (by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
                     at hz ⊢; tauto)
  have hRaise := generalizedHypergeometricCoeff_lower_add_one a b c d e hb0 n
  have hLower := generalizedHypergeometricCoeff_lower_add_one a b c (d - 1) e hbm n
  rw [show d - 1 + 1 = d by ring] at hLower
  have hSucc := generalizedHypergeometricCoeff_succ_mul (a := {a, b, c}) hb0 n
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton] at hSucc
  have hdn : d + (n : ℂ) ≠ 0 := by
    intro hx
    exact hb d (by simp) n (by linear_combination hx)
  apply mul_left_cancel₀ hdn
  linear_combination (a - d) * (b - d) * (c - d) * hRaise +
    - (d + n) * d * (a + b + c - d - e + 1) * hLower - d * hSucc
/-- The weighted boundary coefficient in the first unit recurrence tends to zero. -/
private lemma tendsto_generalizedHypergeometricCoeff_boundary_zero (a b c d e : ℂ)
    (hb : LowerParametersRegular {d, e})
    (hconv : 1 < (d + e - a - b - c).re ∨ IsTerminating {a, b, c}) :
    Tendsto (fun n : ℕ => d * n * (e + n - 1) * generalizedHypergeometricCoeff {a, b, c} {d, e} n)
      atTop (𝓝 0) := by
  have hw := generalizedHypergeometricCoeff_mul_pow_tendsto_zero (a := {a, b, c})
      (b := {d, e}) (by simp) hb 2
    (by
      simpa only [parameterExcess, Multiset.insert_eq_cons, Multiset.sum_cons,
          Multiset.sum_singleton,
        Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num,
        show d + e - (a + (b + c)) = d + e - a - b - c by ring] using hconv)
  have hr : Tendsto (fun n : ℕ => d * (1 + (e - 1) / (n : ℂ))) atTop (𝓝 d) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).add
      (tendsto_const_div_atTop_nhds_zero_nat (e - 1))).const_mul d
  have hm := hr.mul hw
  rw [mul_zero] at hm
  apply hm.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring

/-- The contiguous unity recurrence with convergence of every displayed series. -/
@[dlmf 16.4.E12]
theorem generalizedHypergeometric_3F2_unit_recurrence (a b c d e : ℂ)
    (hb : LowerParametersRegular {d - 1, d, d + 1, e})
    (hconv : 1 < (d + e - a - b - c).re ∨ IsTerminating {a, b, c}) :
    (a - d) * (b - d) * (c - d) *
      (generalizedHypergeometric {a, b, c} {d + 1, e} 1 -
          generalizedHypergeometric {a, b, c} {d, e} 1) +
      a * b * c * generalizedHypergeometric {a, b, c} {d, e} 1 =
    d * (d - 1) * (a + b + c - d - e + 1) *
      (generalizedHypergeometric {a, b, c} {d, e} 1 -
          generalizedHypergeometric {a, b, c} {d - 1, e} 1) := by
  have hb0 : LowerParametersRegular {d, e} := by
    intro z hz
    exact hb z (by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
                     at hz ⊢; tauto)
  have hbp : LowerParametersRegular {d + 1, e} := by
    intro z hz
    exact hb z (by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
                     at hz ⊢; tauto)
  have hbm : LowerParametersRegular {d - 1, e} := by
    intro z hz
    exact hb z (by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
                     at hz ⊢; tauto)
  have hc0 : 0 < (d + e - a - b - c).re ∨ IsTerminating {a, b, c} := by
    rcases hconv with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr h
  have hcp : 0 < (d + 1 + e - a - b - c).re ∨ IsTerminating {a, b, c} := by
    rcases hconv with h | h
    · exact Or.inl (by simp only [add_re, sub_re, one_re] at h ⊢; linarith)
    · exact Or.inr h
  have hcm : 0 < (d - 1 + e - a - b - c).re ∨ IsTerminating {a, b, c} := by
    rcases hconv with h | h
    · exact Or.inl (by simp only [add_re, sub_re, one_re] at h ⊢; linarith)
    · exact Or.inr h
  let P := (a - d) * (b - d) * (c - d)
  let Q := d * (d - 1) * (a + b + c - d - e + 1)
  let C := fun n => P *
      (generalizedHypergeometricCoeff {a, b, c} {d + 1, e} n -
      generalizedHypergeometricCoeff {a, b, c} {d, e} n) +
    a * b * c * generalizedHypergeometricCoeff {a, b, c} {d, e} n -
    Q * (generalizedHypergeometricCoeff {a, b, c} {d, e} n -
        generalizedHypergeometricCoeff {a, b, c} {d - 1, e} n)
  let U := fun n : ℕ => d * n * (e + n - 1) * generalizedHypergeometricCoeff {a, b, c} {d, e} n
  have h0 := hasSum_gen3F2_one hb0 hc0
  have hp := hasSum_gen3F2_one hbp hcp
  have hm := hasSum_gen3F2_one hbm hcm
  have hC := (((hp.sub h0).mul_left P).add (h0.mul_left (a * b * c))).sub
    ((h0.sub hm).mul_left Q)
  change HasSum C _ at hC
  have hsum (N : ℕ) : ∑ n ∈ range N, C n = U N := by
    induction N with
    | zero => simp [U]
    | succ N ih =>
      rw [sum_range_succ, ih]
      have h := generalizedHypergeometricCoeff_first_unit_recurrence_telescope a b c d e hb N
      change C N = _ at h
      rw [h]
      dsimp [U]
      push_cast
      ring
  have hlim := hC.tendsto_sum_nat
  simp_rw [hsum] at hlim
  have heq := tendsto_nhds_unique hlim
      (tendsto_generalizedHypergeometricCoeff_boundary_zero a b c d e hb0 hconv)
  exact sub_eq_zero.mp heq

/-- The second unity recurrence, with the full common convergence half-space. -/
@[dlmf 16.4.E13]
theorem generalizedHypergeometric_3F2_unit_recurrence_two (a b c d e : ℂ)
    (hb : LowerParametersRegular {d, d + 1, e, e + 1})
    (hconv : 0 < (d + e - a - b - c).re) :
    generalizedHypergeometric {a, b, c} {d, e} 1 = c * (e - a) / (d * e) *
      generalizedHypergeometric {a, b + 1, c + 1} {d + 1, e + 1} 1 +
      (d - c) / d * generalizedHypergeometric {a, b + 1, c} {d + 1, e} 1 := by
  have hbparts : (∀ n : ℕ, d ≠ -n) ∧ (∀ n : ℕ, d + 1 ≠ -n) ∧
      (∀ n : ℕ, e ≠ -n) ∧ (∀ n : ℕ, e + 1 ≠ -n) := by
    simpa [LowerParametersRegular] using hb
  have hb0 : LowerParametersRegular {d, e} := by
    simpa [LowerParametersRegular] using And.intro hbparts.1 hbparts.2.2.1
  have hb1 : LowerParametersRegular {d + 1, e + 1} := by
    simpa [LowerParametersRegular] using And.intro hbparts.2.1 hbparts.2.2.2
  have hb2 : LowerParametersRegular {d + 1, e} := by
    simpa [LowerParametersRegular] using And.intro hbparts.2.1 hbparts.2.2.1
  have h0 := hasSum_gen3F2_one hb0 (Or.inl hconv)
  have h1 := hasSum_gen3F2_one (a := a) (b := b + 1) (c := c + 1) hb1
    (Or.inl (by
      convert hconv using 1
      congr 1
      ring))
  have h2 := hasSum_gen3F2_one (a := a) (b := b + 1) (c := c) hb2
    (Or.inl (by
      convert hconv using 1
      congr 1
      ring))
  let C : ℕ → ℂ := fun n => generalizedHypergeometricCoeff {a, b, c} {d, e} n -
    c * (e - a) / (d * e) * generalizedHypergeometricCoeff {a, b + 1, c + 1} {d + 1, e + 1} n -
    (d - c) / d * generalizedHypergeometricCoeff {a, b + 1, c} {d + 1, e} n
  let V : ℕ → ℂ := fun n => a * c / (d * e) *
    generalizedHypergeometricCoeff {a + 1, b + 1, c + 1} {d + 1, e + 1} n
  have hC : HasSum C (generalizedHypergeometric {a, b, c} {d, e} 1 - c * (e - a) / (d * e) *
      generalizedHypergeometric {a, b + 1, c + 1} {d + 1, e + 1} 1 -
      (d - c) / d * generalizedHypergeometric {a, b + 1, c} {d + 1, e} 1) :=
    (h0.sub (h1.mul_left _)).sub (h2.mul_left _)
  have hsum (N : ℕ) : ∑ n ∈ range (N + 1), C n = V N := by
    induction N with
    | zero =>
      simp [C, V, generalizedHypergeometricCoeff, pochhammerProduct, pochhammer_zero]
      have hd : d ≠ 0 := by simpa using hbparts.1 0
      have he : e ≠ 0 := by simpa using hbparts.2.2.1 0
      field_simp [hd, he]
      ring
    | succ N ih =>
      rw [sum_range_succ, ih]
      dsimp only [C, V]
      rw [generalizedHypergeometricCoeff_second_unit_recurrence_telescope a b c d e hb N]
      ring
  have hv0 := generalizedHypergeometricCoeff_tendsto_zero (a := {a + 1, b + 1, c + 1})
    (b := {d + 1, e + 1}) (by simp) hb1 (Or.inl (by
      simp only [parameterExcess, Multiset.insert_eq_cons, Multiset.sum_cons,
        Multiset.sum_singleton, add_re, sub_re, one_re]
      simp only [add_re, sub_re] at hconv
      linarith))
  have hv : Tendsto V atTop (𝓝 0) := by
    simpa only [mul_zero] using hv0.const_mul (a * c / (d * e))
  have hc := (tendsto_add_atTop_iff_nat 1).mpr hC.tendsto_sum_nat
  simp_rw [hsum] at hc
  have heq := tendsto_nhds_unique hc hv
  linear_combination heq

/-- The balanced terminating 4F3 transformation. -/
@[dlmf 16.4.E14]
theorem generalizedHypergeometric_balanced_4F3_transformation (n : ℕ) (a b c d e f : ℂ)
    (hbal : a + b + c - n + 1 = d + e + f)
    (hb : LowerParametersRegular {d, e, f, a - e - n + 1, a - f - n + 1}) :
    generalizedHypergeometricTruncated n {(-n : ℂ), a, b, c} {d, e, f} 1 =
      pochhammer (e - a) n * pochhammer (f - a) n / (pochhammer e n * pochhammer f n) *
        generalizedHypergeometricTruncated n {(-n : ℂ), a, d - b, d - c}
          {d, a - e - n + 1, a - f - n + 1} 1 := by
  have hd : ∀ k : ℕ, d ≠ -k := hb d (by simp)
  have he : ∀ k : ℕ, e ≠ -k := hb e (by simp)
  have hf : ∀ k : ℕ, f ≠ -k := hb f (by simp)
  have he' : ∀ k : ℕ, a - e - n + 1 ≠ -k := hb _ (by simp)
  have hf' : ∀ k : ℕ, a - f - n + 1 ≠ -k := hb _ (by simp)
  have hconv := balanced_4F3_convolution_of_regular a b c e f d he hf hd n
    (by linear_combination hbal)
  simp only [generalizedHypergeometricTruncated, generalizedHypergeometricCoeff, pochhammerProduct,
      Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, one_pow, mul_one]
  rw [Finset.mul_sum]
  convert hconv using 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ n := by simpa using hj
    have hn : n = (n - j) + j := by omega
    have hEa : pochhammer (e - a) n = pochhammer (e - a) (n - j) *
        pochhammer (e - a + ((n - j : ℕ) : ℂ)) j := by
      rw [← pochhammer_add, ← hn]
    have hFa : pochhammer (f - a) n = pochhammer (f - a) (n - j) *
        pochhammer (f - a + ((n - j : ℕ) : ℂ)) j := by
      rw [← pochhammer_add, ← hn]
    have hEn : pochhammer e n = pochhammer e j * pochhammer (e + j) (n - j) := by
      rw [← pochhammer_add, Nat.add_sub_cancel' hj']
    have hFn : pochhammer f n = pochhammer f j * pochhammer (f + j) (n - j) := by
      rw [← pochhammer_add, Nat.add_sub_cancel' hj']
    have hRe : pochhammer (a - e - n + 1) j = (-1) ^ j *
        pochhammer (e - a + ((n - j : ℕ) : ℂ)) j := by
      rw [← pochhammer_reflect]; congr 1; push_cast [Nat.cast_sub hj']; ring
    have hRf : pochhammer (a - f - n + 1) j = (-1) ^ j *
        pochhammer (f - a + ((n - j : ℕ) : ℂ)) j := by
      rw [← pochhammer_reflect]; congr 1; push_cast [Nat.cast_sub hj']; ring
    have h1 := pochhammer_ne_zero_of_not_neg_nat he j
    have h2 := pochhammer_ne_zero_of_not_neg_nat hf j
    have h3 := pochhammer_ne_zero_of_not_neg_nat (not_neg_nat_add_nat he j) (n - j)
    have h4 := pochhammer_ne_zero_of_not_neg_nat (not_neg_nat_add_nat hf j) (n - j)
    have h5 := pochhammer_ne_zero_of_not_neg_nat he' j
    have h6 := pochhammer_ne_zero_of_not_neg_nat hf' j
    have h7 := pochhammer_ne_zero_of_not_neg_nat hd j
    rw [hRe] at h5
    rw [hRf] at h6
    have h5' := right_ne_zero_of_mul h5
    have h6' := right_ne_zero_of_mul h6
    have h9 : (-1 : ℂ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
    have h8 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    rw [hEa, hFa, hEn, hFn, hRe, hRf]
    have hs : ((-1 : ℂ) ^ j) ^ 2 = 1 := by rw [← pow_mul, pow_mul']; norm_num
    field_simp
    rw [hs]
    ring

/-- Whipple transformation when the right side terminates through the transformed first upper
parameter and the left converges absolutely. -/
@[dlmf 16.4.E15]
theorem generalizedHypergeometric_whipple_nonterminating_left (n : ℕ) (a b c d e f : ℂ)
    (hn : a - b - c + 1 = -n)
    (hb : LowerParametersRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - e + 1, a - f + 1,
      d + e + f - a}) (hconv : 0 < (2 * a + 2 - b - c - d - e - f).re) :
    generalizedHypergeometric {a, a / 2 + 1, b, c, d, e, f}
      {a / 2, a - b + 1, a - c + 1, a - d + 1, a - e + 1, a - f + 1} 1 =
      Gamma (a - d + 1) * Gamma (a - e + 1) * Gamma (a - f + 1) *
      Gamma (a - d - e - f + 1) /
      (Gamma (a + 1) * Gamma (a - d - e + 1) *
        Gamma (a - d - f + 1) * Gamma (a - e - f + 1)) *
      generalizedHypergeometricTruncated n {a - b - c + 1, d, e, f}
        {a - b + 1, a - c + 1, d + e + f - a} 1 := by
  sorry

/-- Normalized Dougall bilateral sum in its full absolute convergence region. -/
@[dlmf 16.4.E17]
theorem generalizedHypergeometric_dougall_bilateral (a b c d : ℂ) (ha : ∀ k : ℤ, a ≠ k)
    (hb : ∀ k : ℤ, b ≠ k)
    (hcd : LowerParametersRegular {c, d}) (hconv : 1 < (c + d - a - b).re) :
    bilateralHypergeometric {a, b} {c, d} 1 =
      Gamma c * Gamma d * Gamma (1 - a) * Gamma (1 - b) * Gamma (c + d - a - b - 1) /
      (Gamma (c - a) * Gamma (d - a) * Gamma (c - b) * Gamma (d - b)) := by
  have ha' : ∀ j : ℕ, a ≠ -(j : ℂ) := fun j hj => ha (-(j : ℤ)) (by simpa using hj)
  have hb' : ∀ j : ℕ, b ≠ -(j : ℂ) := fun j hj => hb (-(j : ℤ)) (by simpa using hj)
  have hc' : ∀ j : ℕ, c ≠ -(j : ℂ) := hcd c (by simp)
  have hd' : ∀ j : ℕ, d ≠ -(j : ℂ) := hcd d (by simp)
  have hGa := Complex.Gamma_ne_zero ha'
  have hGb := Complex.Gamma_ne_zero hb'
  have hGc := Complex.Gamma_ne_zero hc'
  have hGd := Complex.Gamma_ne_zero hd'
  have hterm (n : ℤ) : bilateralHypergeometricCoeff {a, b} {c, d} n * (1 : ℂ) ^ n =
      Gamma c * Gamma d / (Gamma a * Gamma b) *
        (Gamma (a + n) * Gamma (b + n) / (Gamma (c + n) * Gamma (d + n))) := by
    simp only [bilateralHypergeometricCoeff, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, one_zpow,
      mul_one, pochhammerOfInt_eq_Gamma_div ha', pochhammerOfInt_eq_Gamma_div hb',
      pochhammerOfInt_eq_Gamma_div hc', pochhammerOfInt_eq_Gamma_div hd']
    field_simp
  have hconv' : 1 + (a + b).re < (c + d).re := by
    simp only [Complex.sub_re, Complex.add_re] at hconv ⊢
    linarith
  unfold bilateralHypergeometric
  simp_rw [hterm]
  -- Restore the existing proved Gamma-form sum before changing its normalization.
  rw [tsum_mul_left, dougall_bilateral ha hb hconv']
  have hπ : (Real.pi : ℂ) ^ 2 * Gamma (c + d - a - b - 1) /
      (Complex.sin (Real.pi * a) * Complex.sin (Real.pi * b) *
        Gamma (c - a) * Gamma (d - a) * Gamma (c - b) * Gamma (d - b)) =
      (Real.pi / Complex.sin (Real.pi * a)) * (Real.pi / Complex.sin (Real.pi * b)) *
        Gamma (c + d - a - b - 1) /
          (Gamma (c - a) * Gamma (d - a) * Gamma (c - b) * Gamma (d - b)) := by
    simp only [pow_two, div_eq_mul_inv, mul_inv]
    ring
  rw [hπ, ← Complex.Gamma_mul_Gamma_one_sub a, ← Complex.Gamma_mul_Gamma_one_sub b]
  field_simp

/-- Whipple transformation wherever the printed Gamma numerator is defined, including
all terminating upper choices. Removable Gamma-pole cases with d,e,f terminating
are covered by the proved finite Pochhammer form `whipple_7F6` and symmetry. -/
@[dlmf 16.4.E15]
theorem generalizedHypergeometric_whipple_general (a b c d e f : ℂ)
    (hb : LowerParametersRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - e + 1,
      a - f + 1, d + e + f - a})
    (hnum : LowerParametersRegular {a - d - e - f + 1})
    (hterm : IsTerminating {a - b - c + 1, d, e, f})
    (hconv : 0 < (2 * a + 2 - b - c - d - e - f).re ∨
      IsTerminating {a, b, c, d, e, f}) :
    generalizedHypergeometric {a, a / 2 + 1, b, c, d, e, f}
      {a / 2, a - b + 1, a - c + 1, a - d + 1, a - e + 1, a - f + 1} 1 =
      Gamma (a - d + 1) * Gamma (a - e + 1) * Gamma (a - f + 1) *
      Gamma (a - d - e - f + 1) /
      (Gamma (a + 1) * Gamma (a - d - e + 1) *
        Gamma (a - d - f + 1) * Gamma (a - e - f + 1)) *
      generalizedHypergeometric {a - b - c + 1, d, e, f}
          {a - b + 1, a - c + 1, d + e + f - a} 1 := by
  sorry

/-- The Thomae expression supplies parameter continuation beyond the original unit
series region; at Gamma poles its totalized value is not an assigned finite limit. -/
@[dlmf 16.4.E11]
def gen3F2UnitThomae (a b c d e : ℂ) : ℂ :=
  Gamma e * Gamma (d + e - a - b - c) /
    (Gamma (e - a) * Gamma (d + e - b - c)) *
    generalizedHypergeometric {a, d - b, d - c} {d, d + e - b - c} 1

/-- Joint analyticity in the convergent unit-series parameter region (16.4, prose). -/
private lemma analyticOnNhd_generalizedHypergeometric_three_two_one_params :
    AnalyticOnNhd ℂ (fun P : Fin 5 → ℂ => generalizedHypergeometric {P 0, P 1, P 2} {P 3, P 4} 1)
      {P | LowerParametersRegular {P 3, P 4} ∧ 0 < (P 3 + P 4 - P 0 - P 1 - P 2).re} := by
  sorry

/-- The continued expression is jointly analytic at its regular parameter points in
the full printed e−a half-space, including points outside original series convergence. -/
@[dlmf 16.4.E11]
theorem analyticOnNhd_gen3F2UnitThomae_params :
    AnalyticOnNhd ℂ (fun P : Fin 5 → ℂ => gen3F2UnitThomae (P 0) (P 1) (P 2) (P 3) (P 4))
      {P | LowerParametersRegular {P 3, P 4, P 3 + P 4 - P 1 - P 2,
        P 3 + P 4 - P 0 - P 1 - P 2} ∧ 0 < (P 4 - P 0).re} := by
  sorry

end DLMF.Hypergeometric
