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

/-!
# `ₚF_q` at unit argument (DLMF §16.4)

## Main definitions

* `gen3F2UnitThomae`: the Thomae expression continuing `₃F₂(1)` in its parameters.

## Main results

* `genHG_finite_ratio_sum`, `genHG_finite_ratio_sum_closed`: DLMF 16.4.2_5.
* `genHG_dixon_terminating_even`, `genHG_dixon_terminating_odd`: Dixon's sum, DLMF 16.4.5.
* `genHG_watson_sum`: Watson's sum, DLMF 16.4.6, with terminating forms.
* `genHG_whipple_3F2_sum`, `genHG_whipple_3F2_terminating`: Whipple's sum, DLMF 16.4.7–16.4.8.
* `genHG_dougall_5F4_sum`, `genHG_dougall_5F4_terminating`, `genHG_dougall_7F6`: Dougall's
  sums, DLMF 16.4.9–16.4.10.
* `genHG_3F2_unit_transformation`, `analyticOnNhd_gen3F2UnitThomae_params`: DLMF 16.4.11.
* `genHG_3F2_unit_recurrence`, `genHG_3F2_unit_recurrence_two`: DLMF 16.4.12–16.4.13.
* `genHG_balanced_4F3_transformation`: DLMF 16.4.14.
* `genHG_whipple_general`, `genHG_whipple_nonterminating_left`: Whipple's transformation,
  DLMF 16.4.15.
* `genHG_dougall_bilateral`: Dougall's bilateral sum, DLMF 16.4.17.

## Implementation notes

The predicates `GenWellPoised`, `GenVeryWellPoised` and `GenKBalanced` (DLMF 16.4.1–16.4.2) are in
`DLMF.GeneralizedHypergeometric.Basic.ParametersAndSeries`. Finite parity and finite Dougall
identities use Pochhammer quotients, which retain the removable cases hidden by quotients of poles
in the printed Gamma formulas. Lower parameters retain the chapter's nonpositive-integer exclusions,
except the explicitly cancelled finite pair in 16.4.2_5. Convergence at unity is always stated
before a nonterminating sum is used. The odd terminating Dixon evaluation follows from finite
inversion. The bilateral evaluation uses `dougall_bilateral` and Mathlib's
`Complex.Gamma_mul_Gamma_one_sub`, preserving integral lower parameters. The finite Dougall `₅F₄`
evaluation is the `q → 1` limit of the rational terminating `₆φ₅` identity
`DLMF.QHypergeometric.sum_sixTerm_eq`, with Bailey's polynomial unit factor handling the
very-well-poised pair without square-root branch restrictions. The finite Dougall `₇F₆` follows from
Whipple's transformation and Saalschütz's sum, with continuity of finite rational sums retaining the
removable cancelled-parameter cases. The terminating Watson sums reduce to the terminating Dixon
sums by Sheppard's transformation, taken from the binomial convolution
`terminating_3F2_convolution`; the balanced `₄F₃` transformation 16.4.14 is the convolution
form `balanced_4F3_convolution_of_regular` of Whipple's transformation.
-/

@[expose] public section
open Complex Filter Set Finset
open scoped Topology Real
noncomputable section
namespace DLMF.Hypergeometric

/-- The canceled finite 3F2 sum in a form without an artificial singularity at c=1. -/
@[dlmf 16.4.E2_5]
theorem genHG_finite_ratio_sum (n : ℕ) (a c : ℂ) (hc : GenDenRegular {c}) :
    genFiniteHG n {(-n : ℂ), a, 1} {(-n : ℂ), c} 1 =
      ∑ k ∈ range (n + 1), poch a k / poch c k ∧
    (c - a - 1) * (∑ k ∈ range (n + 1), poch a k / poch c k) =
      c - 1 - (c + n) * poch a (n + 1) / poch c (n + 1) := by
  have hc' (k : ℕ) : poch c k ≠ 0 := poch_ne_zero_of_not_neg_nat (hc c (by simp)) k
  constructor
  · unfold genFiniteHG
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hn : poch (-(n : ℂ)) k ≠ 0 := by
      rw [poch_neg_coe_nat]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.cast_ne_zero.mpr ((Nat.descFactorial_pos.mpr hkn).ne'))
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    simp only [genCoeff, genPoch, Multiset.insert_eq_cons, Multiset.map_cons,
        Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton, one_pow, mul_one, poch_nat_one]
    field_simp [hn, hf, hc' k]
  · induction n with
    | zero =>
      have hc0 : c ≠ 0 := by simpa using hc c (by simp) 0
      simp only [sum_range_one, poch_zero, poch_one, div_one, Nat.cast_zero, add_zero,
          zero_add, mul_one]
      field_simp [hc0]
      ring
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, poch_succ a (n + 1), poch_succ c (n + 1)]
      have hcn : c + (n + 1 : ℕ) ≠ 0 := by
        intro hzero
        exact hc c (by simp) (n + 1) (eq_neg_of_add_eq_zero_left hzero)
      field_simp [hc' (n + 1), hcn]
      push_cast
      ring

/-- The printed closed form wherever its displayed divisors are nonzero. -/
@[dlmf 16.4.E2_5]
theorem genHG_finite_ratio_sum_closed (n : ℕ) (a c : ℂ) (hc : GenDenRegular {c})
    (hca : c - a - 1 ≠ 0) (hc1 : poch (c - 1) (n + 1) ≠ 0) :
    (∑ k ∈ range (n + 1), poch a k / poch c k) =
      (c - 1) / (c - a - 1) * (1 - poch a (n + 1) / poch (c - 1) (n + 1)) := by
  have hC : poch c (n + 1) ≠ 0 := poch_ne_zero_of_not_neg_nat (hc c (by simp)) _
  have hcross : poch (c - 1) (n + 1) * (c + n) = (c - 1) * poch c (n + 1) := by
    rw [poch_succ_left, show c - 1 + 1 = c by ring, poch_succ c]
    ring
  have hratio : (c + n) * poch a (n + 1) / poch c (n + 1) =
      (c - 1) * poch a (n + 1) / poch (c - 1) (n + 1) := by
    field_simp
    linear_combination poch a (n + 1) * hcross
  have h := (genHG_finite_ratio_sum n a c hc).2
  rw [hratio] at h
  field_simp [hc1] at h
  field_simp [hca, hc1]
  linear_combination h

/-- The limiting c=a+1 form; a=0 is retained separately as the removable value one. -/
@[dlmf 16.4.E2_5]
theorem genHG_finite_ratio_sum_limit (n : ℕ) (a : ℂ) (ha : GenDenRegular {a}) :
    (∑ k ∈ range (n + 1), poch a k / poch (a + 1) k) =
      a * (Complex.digamma (a + n + 1) - Complex.digamma a) ∧
    (∑ k ∈ range (n + 1), poch a k / poch (a + 1) k) =
      a * deriv (fun a : ℂ => poch a (n + 1)) a / poch a (n + 1) := by
  have ha' : ∀ k : ℕ, a ≠ -(k : ℂ) := ha a (by simp)
  have hap (k : ℕ) : a + k ≠ 0 := fun h => ha' k (eq_neg_of_add_eq_zero_left h)
  have hp1 (k : ℕ) : poch (a + 1) k ≠ 0 :=
    by simpa only [Nat.cast_one] using poch_ne_zero_of_not_neg_nat (not_neg_nat_add_nat ha' 1) k
  have hratio (k : ℕ) : poch a k / poch (a + 1) k = a / (a + k) := by
    have h := (poch_succ a k).symm.trans (poch_succ_left a k)
    field_simp [hp1 k, hap k]
    exact h
  have hsum : (∑ k ∈ range (n + 1), poch a k / poch (a + 1) k) =
      a * ∑ k ∈ range (n + 1), (a + k)⁻¹ := by
    simp_rw [hratio, div_eq_mul_inv]
    rw [Finset.mul_sum]
  constructor
  · rw [hsum, show a + n + 1 = a + (n + 1 : ℕ) by push_cast; ring,
      Complex.digamma_apply_add_nat ha']
    ring
  · have hprod : (fun x : ℂ => poch x (n + 1)) =
        (fun x : ℂ => ∏ k ∈ range (n + 1), (x + k)) := by
      funext x
      simpa using poch_mul_pow x 1 (n + 1)
    have hlog : deriv (fun x : ℂ => ∏ k ∈ range (n + 1), (x + k)) a /
          (∏ k ∈ range (n + 1), (a + k)) = ∑ k ∈ range (n + 1), (a + k)⁻¹ := by
      simpa [logDeriv_apply] using (logDeriv_fun_prod
        (s := range (n + 1)) (f := fun k (x : ℂ) => x + k)
        (fun k _ => hap k) (fun k _ => by fun_prop))
    rw [← hprod] at hlog
    have hvalue := congrFun hprod a
    change poch a (n + 1) = ∏ k ∈ range (n + 1), (a + k) at hvalue
    rw [← hvalue] at hlog
    rw [hsum, mul_div_assoc, hlog]

/-- The removable limiting value at a=0,c=1. -/
@[dlmf 16.4.E2_5]
theorem genHG_finite_ratio_sum_zero (n : ℕ) :
    (∑ k ∈ range (n + 1), poch (0 : ℂ) k / poch 1 k) = 1 := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, poch_zero_succ, zero_div, add_zero]

section DixonDegenerate

open Polynomial

/-- `1/Γ(y) = (y)_r / Γ(y + r)` for every `y` and every `r`. -/
private lemma recip_Gamma_eq_poch_mul_recip (y : ℂ) (r : ℕ) :
    (Gamma y)⁻¹ = poch y r * (Gamma (y + r))⁻¹ := by
  rcases r with _ | p
  · simp [poch_zero]
  · exact recip_Gamma_eq_poch_mul p y

/-- The polynomial side of the even degenerate Dixon sum. -/
private def dixonEvenT (k : ℕ) (b c : ℂ) : ℂ :=
  ∑ n ∈ range (2 * k + 1), gaussHGCoeff (-(2 * k : ℂ)) b (1 - 2 * k - b) n * poch c n *
    poch (1 - 2 * k + n - c) (2 * k - n)

/-- The product side of the even degenerate Dixon sum. -/
private def dixonEvenQ (k : ℕ) (b c : ℂ) : ℂ :=
  (2 * k).factorial / (k.factorial * poch (b + k) k) * poch c k * poch (c + (b + k)) k

/-- The Dixon terms with `a = -2k` vanish beyond `2k`. -/
private lemma gaussHGCoeff_neg_two_mul_eq_zero (k : ℕ) (b c : ℂ) {n : ℕ} (hn : 2 * k < n) :
    gaussHGCoeff (-(2 * k : ℂ)) b c n = 0 := by
  have : poch (-((2 * k : ℕ) : ℂ)) n = 0 := poch_neg_nat_eq_zero hn
  push_cast at this
  simp [gaussHGCoeff, this]

/-- The normalized Dixon series with `a = -2k` is a finite sum. -/
private lemma normalizedSeries_neg_two_mul (k : ℕ) (b c : ℂ) :
    DixonWZ.normalizedSeries (-(2 * k : ℂ)) b c =
      ∑ n ∈ range (2 * k + 1), DixonWZ.s (-(2 * k : ℂ)) b c n := by
  unfold DixonWZ.normalizedSeries
  refine tsum_eq_sum fun n hn => ?_
  have : 2 * k < n := by simpa using hn
  simp [DixonWZ.s, gaussHGCoeff_neg_two_mul_eq_zero k b _ this]

/-- The WZ recurrence in `c` for the degenerate Dixon series `a = -2k`, valid for every `c`. -/
private lemma normalizedSeries_neg_two_mul_recurrence (k : ℕ) (b : ℂ)
    (hb : ∀ n : ℕ, 1 - 2 * k - b ≠ -n) (c : ℂ) :
    (1 - k - b - c) * DixonWZ.normalizedSeries (-(2 * k : ℂ)) b c =
      (1 - k - c) * (1 - 2 * k - b - c) * DixonWZ.normalizedSeries (-(2 * k : ℂ)) b (c - 1) := by
  have hsum : ∀ c', Summable (DixonWZ.s (-(2 * k : ℂ)) b c') := fun c' =>
    summable_of_ne_finset_zero (s := range (2 * k + 1)) fun n hn => by
      have : 2 * k < n := by simpa using hn
      simp [DixonWZ.s, gaussHGCoeff_neg_two_mul_eq_zero k b _ this]
  have hH : Tendsto (DixonWZ.wzCertificate (-(2 * k : ℂ)) b c) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (2 * k)] with n hn
    simp [DixonWZ.wzCertificate, gaussHGCoeff_neg_two_mul_eq_zero k b _ hn]
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
  have hr := recip_Gamma_eq_poch_mul_recip (1 + -(2 * k : ℂ) - -(m : ℂ) + n) (2 * k - n)
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
  have h1 : poch (c - 1) k * (c - 1 + k) = (c - 1) * poch c k := by
    rw [← poch_succ, poch_succ_left, sub_add_cancel]
  have h2 : poch (c - 1 + (b + k)) k * (c - 1 + (b + k) + k) =
      (c - 1 + (b + k)) * poch (c + (b + k)) k := by
    rw [← poch_succ, poch_succ_left]; ring_nf
  linear_combination ((2 * k).factorial / (k.factorial * poch (b + k) k)) *
    (-((c - 1 + (b + k)) * poch (c + (b + k)) k) * h1 - poch (c - 1) k * (c - 1 + k) * h2)

/-- The two sides agree at `c = -k`, where only one term survives. -/
private lemma dixonEvenT_neg_self (k : ℕ) (b : ℂ) (hb : ∀ n : ℕ, 1 - 2 * k - b ≠ -n) :
    dixonEvenT k b (-(k : ℂ)) = dixonEvenQ k b (-(k : ℂ)) := by
  unfold dixonEvenT dixonEvenQ
  rw [sum_eq_single k]
  · have hP : poch (1 - 2 * k - b) k ≠ 0 := poch_ne_zero_of_not_neg_nat hb k
    have hR : poch (1 - 2 * k - b) k = (-1) ^ k * poch (b + k) k := by
      rw [← poch_reflect]; ring_nf
    have hA : poch (-(2 * k : ℂ)) k = (-1) ^ k * ((2 * k).factorial / k.factorial) := by
      have h1 := poch_reflect ((k : ℂ) + 1) k
      have h2 := Complex.Gamma_add_nat_div_Gamma_eq (n := k) ((k : ℂ) + 1)
        (fun m hm => by
          have : ((k + 1 + m : ℕ) : ℂ) = 0 := by push_cast; linear_combination hm
          exact absurd (by exact_mod_cast this) (Nat.succ_ne_zero (k + m) ∘ by omega))
      rw [show (k : ℂ) + 1 + k = ((2 * k : ℕ) : ℂ) + 1 by push_cast; ring,
        show (k : ℂ) + 1 = ((k : ℕ) : ℂ) + 1 from rfl, Complex.Gamma_nat_eq_factorial,
        Complex.Gamma_nat_eq_factorial] at h2
      rw [show (1 : ℂ) - (k + 1) - k = -(2 * k) by ring] at h1
      rw [h1, poch, ← h2]
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hp1 : poch (1 - 2 * k + k - -(k : ℂ)) (2 * k - k) = k.factorial := by
      rw [show (1 : ℂ) - 2 * k + k - -(k : ℂ) = 1 by ring, show 2 * k - k = k by omega,
        poch, ascPochhammer_eval_one]
    rw [hp1, gaussHGCoeff, hA, hR]
    have hB : poch (b + k) k ≠ 0 := fun h0 => hP (by rw [hR, h0, mul_zero])
    field_simp
    rw [show -(k : ℂ) + (b + k) = b by ring]
  · intro n hn hnk
    rcases lt_or_gt_of_ne hnk with hlt | hgt
    · have : poch (1 - 2 * k + n - -(k : ℂ)) (2 * k - n) = 0 := by
        have := poch_neg_nat_eq_zero (n := k - 1 - n) (k := 2 * k - n) (by omega)
        rwa [show -(((k - 1 - n : ℕ) : ℂ)) = 1 - 2 * k + n - -(k : ℂ) by
          push_cast [show n ≤ k - 1 by omega, show 1 ≤ k by omega]; ring] at this
      rw [this, mul_zero]
    · have := poch_neg_nat_eq_zero (n := k) (k := n) hgt
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
    (C (gaussHGCoeff (-(2 * k : ℂ)) b (1 - 2 * k - b) n) : ℂ[X]) * ascPochhammer ℂ n *
      (ascPochhammer ℂ (2 * k - n)).comp ((C (1 - 2 * k + n : ℂ) : ℂ[X]) - X)
  let Qp : ℂ[X] := (C ((2 * k).factorial / (k.factorial * poch (b + k) k) : ℂ) : ℂ[X]) *
    ascPochhammer ℂ k * (ascPochhammer ℂ k).comp (X + (C (b + k) : ℂ[X]))
  have hT : ∀ c, Tp.eval c = dixonEvenT k b c := fun c => by
    simp [Tp, dixonEvenT, Polynomial.eval_finsetSum, poch]
  have hQ : ∀ c, Qp.eval c = dixonEvenQ k b c := fun c => by
    simp [Qp, dixonEvenQ, poch]
  have h0 : Tp - Qp = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ (Set.infinite_of_injective_forall_mem
      (f := fun i : ℕ => -((k + i : ℕ) : ℂ)) (fun i j hij => by simpa using hij) fun i => ?_)
    simp only [Set.mem_ofPred_eq, IsRoot.def, eval_sub, hT, hQ]
    rw [dixonEvenT_neg_add k b hb i, sub_self]
  rw [← hT, ← hQ, sub_eq_zero.mp h0]

/-- Dixon's even terminating evaluation, assuming only that the finite Pochhammer product of
the second lower parameter is nonzero. -/
private lemma genHG_dixon_terminating_even_of_poch (k : ℕ) (b c : ℂ)
    (hb1 : ∀ n : ℕ, 1 - b - 2 * k ≠ -n) (hpc : poch (1 - c - 2 * k) (2 * k) ≠ 0) :
    genFiniteHG (2 * k) {(-(2 * k) : ℂ), b, c}
      {1 - b - 2 * k, 1 - c - 2 * k} 1 =
      (2 * k).factorial * poch (b + c + k) k /
        (k.factorial * poch (b + k) k * poch (c + k) k) := by
  have hb2 : ∀ n : ℕ, 1 - 2 * k - b ≠ -n := fun n h => hb1 n (by linear_combination h)
  have hrc : poch (1 - c - 2 * k) (2 * k) = poch c k * poch (c + k) k := by
    have := poch_reflect c (2 * k)
    push_cast at this
    rw [this, show 2 * k = k + k by ring, poch_add, pow_add, ← pow_mul_pow_sub (-1 : ℂ) le_rfl]
    simp [← sq, ← pow_mul]
  have hck : poch (c + k) k ≠ 0 := fun h0 => hpc (by rw [hrc, h0, mul_zero])
  have hrb : poch (1 - 2 * k - b) k = (-1) ^ k * poch (b + k) k := by
    rw [← poch_reflect]; ring_nf
  have hbk : poch (b + k) k ≠ 0 := fun h0 =>
    poch_ne_zero_of_not_neg_nat hb2 k (by rw [hrb, h0, mul_zero])
  apply mul_right_cancel₀ hpc
  have hL : genFiniteHG (2 * k) {(-(2 * k) : ℂ), b, c} {1 - b - 2 * k, 1 - c - 2 * k} 1 *
      poch (1 - c - 2 * k) (2 * k) = dixonEvenT k b c := by
    unfold genFiniteHG dixonEvenT
    rw [sum_mul]
    refine sum_congr rfl fun n hn => ?_
    have hn' : n ≤ 2 * k := Nat.lt_succ_iff.mp (mem_range.mp hn)
    have hsplit : poch (1 - c - 2 * k) (2 * k) =
        poch (1 - c - 2 * k) n * poch (1 - 2 * k + n - c) (2 * k - n) := by
      rw [← show 1 - c - 2 * k + n = 1 - 2 * k + n - c by ring, ← poch_add,
        Nat.add_sub_cancel' hn']
    have h1 := poch_ne_zero_of_not_neg_nat hb1 n
    have h2 : poch (1 - c - 2 * k) n ≠ 0 := left_ne_zero_of_mul (hsplit ▸ hpc)
    have h3 : poch (1 - 2 * k - b) n = poch (1 - b - 2 * k) n := by ring_nf
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    simp only [genCoeff, genPoch, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, one_pow, mul_one,
      gaussHGCoeff, hsplit, h3]
    field_simp
  rw [hL, dixonEvenT_eq_dixonEvenQ k b hb2, dixonEvenQ, hrc]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [show c + (b + k) = b + c + k by ring]
  field_simp

/-- Dixon even terminating evaluation with all removable Gamma ratios replaced by finite products.
-/
@[dlmf 16.4.E5]
theorem genHG_dixon_terminating_even (k : ℕ) (b c : ℂ)
    (hb : GenDenRegular {1 - b - 2 * k, 1 - c - 2 * k}) :
    genFiniteHG (2 * k) {(-(2 * k) : ℂ), b, c}
      {1 - b - 2 * k, 1 - c - 2 * k} 1 =
      (2 * k).factorial * poch (b + c + k) k /
        (k.factorial * poch (b + k) k * poch (c + k) k) :=
  genHG_dixon_terminating_even_of_poch k b c (hb _ (by simp))
    (poch_ne_zero_of_not_neg_nat (hb _ (by simp)) _)

end DixonDegenerate

/-- Dixon's odd terminating evaluation, assuming only that the finite Pochhammer product of
the lower parameters is nonzero. -/
private lemma genHG_dixon_terminating_odd_of_poch (k : ℕ) (b c : ℂ)
    (hB : genPoch {1 - b - ((2 * k + 1 : ℕ) : ℂ), 1 - c - ((2 * k + 1 : ℕ) : ℂ)}
      (2 * k + 1) ≠ 0) :
    genFiniteHG (2 * k + 1) {(-(2 * k + 1) : ℂ), b, c}
      {1 - b - (2 * k + 1), 1 - c - (2 * k + 1)} 1 = 0 := by
  let N := 2 * k + 1
  have hs : (-1 : ℂ) ^ N = -1 := by simp [N, pow_add, pow_mul]
  have hp : genPoch {1 - b - N, 1 - c - N} N = genPoch {b, c} N := by
    simp only [genPoch, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
    rw [poch_reflect b N, poch_reflect c N, hs]
    ring
  have hA : genPoch {b, c} N ≠ 0 := by rw [← hp]; exact hB
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
  have hi := genFiniteHG_inversion {b, c} {1 - b - N, 1 - c - N} N
    (z := 1) (by norm_num) hA hB
  rw [hRA, hRB, hs, hp, mul_neg_one, neg_div, div_self hA] at hi
  norm_num [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton] at hi
  have hzero : genFiniteHG N ((-(N : ℂ)) ::ₘ {b, c}) {1 - b - N, 1 - c - N} 1 = 0 := by
    linear_combination hi / 2
  simpa only [N, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      Multiset.insert_eq_cons] using hzero

/-- Dixon odd terminating evaluation, retaining every regular lower-parameter case. -/
@[dlmf 16.4.E5]
theorem genHG_dixon_terminating_odd (k : ℕ) (b c : ℂ)
    (hb : GenDenRegular {1 - b - (2 * k + 1), 1 - c - (2 * k + 1)}) :
    genFiniteHG (2 * k + 1) {(-(2 * k + 1) : ℂ), b, c}
      {1 - b - (2 * k + 1), 1 - c - (2 * k + 1)} 1 = 0 :=
  genHG_dixon_terminating_odd_of_poch k b c (by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      genPoch_ne_zero hb (2 * k + 1))

/-- Sheppard's terminating `₃F₂(1)` transformation, multiplied out so that only the lower
parameter `R` needs to avoid the nonpositive integers. -/
private lemma genFiniteHG_sheppard (n : ℕ) (P Q R D : ℂ) (hR : ∀ k : ℕ, R ≠ -k)
    (hD : poch D n ≠ 0) (hDP : poch (1 - D + P - n) n ≠ 0) :
    poch D n * genFiniteHG n {(-n : ℂ), Q, P} {R, D} 1 =
      poch (D - P) n * genFiniteHG n {(-n : ℂ), P, R - Q} {R, 1 + P - D - n} 1 := by
  have hconv := terminating_3F2_convolution P Q R D (poch_ne_zero_of_not_neg_nat hR) n
  have hch (k : ℕ) : (-1 : ℂ) ^ k * n.choose k * k.factorial = poch (-(n : ℂ)) k := by
    rw [poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast; ring
  simp only [genFiniteHG, genCoeff, genPoch, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, one_pow, mul_one]
  rw [mul_sum, mul_sum]
  convert hconv using 1
  · refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
    have hDn : poch D n = poch D k * poch (D + k) (n - k) := by
      rw [← poch_add, Nat.add_sub_cancel' hk']
    have hDk : poch D k ≠ 0 := left_ne_zero_of_mul (hDn ▸ hD)
    have hRk := poch_ne_zero_of_not_neg_nat hR k
    have hkf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    rw [← hch, hDn]
    field_simp
  · refine sum_congr rfl fun j hj => ?_
    have hj' : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
    have hn : n = (n - j) + j := by omega
    have hsplit : poch (D - P) n =
        poch (D - P) (n - j) * poch (D - P + ((n - j : ℕ) : ℂ)) j := by
      rw [← poch_add, ← hn]
    have hrefl : poch (1 + P - D - n) j = (-1) ^ j * poch (D - P + ((n - j : ℕ) : ℂ)) j := by
      rw [← poch_reflect]; congr 1; push_cast [Nat.cast_sub hj']; ring
    have hsplit2 : poch (1 - D + P - n) n = poch (1 - D + P - n) j *
        poch (1 - D + P - n + j) (n - j) := by
      rw [← poch_add, Nat.add_sub_cancel' hj']
    have h1 : poch (1 + P - D - n) j ≠ 0 := by
      have := left_ne_zero_of_mul (hsplit2 ▸ hDP)
      rwa [show 1 - D + P - (n : ℂ) = 1 + P - D - n by ring] at this
    rw [hrefl] at h1
    have h1' := right_ne_zero_of_mul h1
    have hRj := poch_ne_zero_of_not_neg_nat hR j
    have hjf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    rw [← hch, hsplit, hrefl]
    field_simp

/-- Duplication for Pochhammer symbols: `(x)₂ₙ = 4ⁿ (x/2)ₙ ((x+1)/2)ₙ`. -/
private lemma poch_two_mul_eq_four_pow_mul_poch (x : ℂ) (n : ℕ) :
    poch x (2 * n) = 4 ^ n * poch (x / 2) n * poch ((x + 1) / 2) n := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, poch_succ, poch_succ, ih, poch_succ, poch_succ]
    push_cast
    ring

/-- Watson sum in the full absolute convergence half-space. -/
@[dlmf 16.4.E6]
theorem genHG_watson_sum (a b c : ℂ) (hb : GenDenRegular {(a + b + 1) / 2, 2 * c})
    (hconv : -1 < (2 * c - a - b).re) :
    genHG {a, b, c} {(a + b + 1) / 2, 2 * c} 1 =
      Gamma (1 / 2) * Gamma (c + 1 / 2) * Gamma ((a + b + 1) / 2) *
      Gamma (c + (1 - a - b) / 2) /
      (Gamma ((a + 1) / 2) * Gamma ((b + 1) / 2) *
        Gamma (c + (1 - a) / 2) * Gamma (c + (1 - b) / 2)) := by
  sorry

/-- Watson even terminating evaluation without extra Gamma-pole exclusions. -/
@[dlmf 16.4.E6]
theorem genHG_watson_terminating_even (k : ℕ) (b c : ℂ)
    (hb : GenDenRegular {(b - 2 * k + 1) / 2, 2 * c}) :
    genFiniteHG (2 * k) {(-(2 * k) : ℂ), b, c}
      {(b - 2 * k + 1) / 2, 2 * c} 1 =
      poch (1 / 2) k * poch (c + (1 - b) / 2) k /
        (poch ((1 - b) / 2) k * poch (c + 1 / 2) k) := by
  set R : ℂ := (b - 2 * k + 1) / 2 with hRdef
  have hR : ∀ m : ℕ, R ≠ -m := hb _ (by simp)
  have h2c : ∀ m : ℕ, 2 * c ≠ -m := hb _ (by simp)
  have hD := poch_ne_zero_of_not_neg_nat h2c (2 * k)
  have hdup := poch_two_mul_eq_four_pow_mul_poch (2 * c) k
  rw [show 2 * c / 2 = c by ring, show (2 * c + 1) / 2 = c + 1 / 2 by ring] at hdup
  have hc2 : poch c (2 * k) = poch c k * poch (c + k) k := by
    rw [two_mul, poch_add]
  have hcn : poch c (2 * k) ≠ 0 := by
    intro h0
    rw [hc2] at h0
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact hD (by rw [hdup, h0]; ring)
    · obtain ⟨i, hi, hi'⟩ := (ascPochhammer_eval_eq_zero_iff (R := ℂ) k (c + k)).1 h0
      exact h2c (2 * (k + i)) (by push_cast; linear_combination 2 * hi')
  have hrefl : poch (1 - 2 * c + c - ((2 * k : ℕ) : ℂ)) (2 * k) =
      (-1) ^ (2 * k) * poch c (2 * k) := by
    rw [← poch_reflect]; congr 1; ring
  have hDP : poch (1 - 2 * c + c - ((2 * k : ℕ) : ℂ)) (2 * k) ≠ 0 := by
    rw [hrefl]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hcn
  have hsh := genFiniteHG_sheppard (2 * k) c b R (2 * c) hR hD hDP
  have hR1 : ∀ m : ℕ, 1 - (R - b) - 2 * k ≠ -m := fun m h => hR m (by
    rw [← h, hRdef]; ring)
  have hpc : poch (1 - c - 2 * k) (2 * k) ≠ 0 := by
    convert hDP using 2; push_cast; ring
  have hdx := genHG_dixon_terminating_even_of_poch k (R - b) c hR1 hpc
  have hG : genFiniteHG (2 * k) {(-((2 * k : ℕ) : ℂ)), c, R - b}
      {R, 1 + c - 2 * c - ((2 * k : ℕ) : ℂ)} 1 =
      genFiniteHG (2 * k) {(-(2 * k) : ℂ), R - b, c} {1 - (R - b) - 2 * k, 1 - c - 2 * k} 1 := by
    congr 1
    · rw [Multiset.pair_comm c (R - b)]
      push_cast
      rfl
    · simp only [Multiset.insert_eq_cons]
      push_cast
      congr 1
      · rw [hRdef]; ring
      · congr 1; ring
  have hL : genFiniteHG (2 * k) {(-((2 * k : ℕ) : ℂ)), b, c} {R, 2 * c} 1 =
      genFiniteHG (2 * k) {(-(2 * k) : ℂ), b, c} {(b - 2 * k + 1) / 2, 2 * c} 1 := by
    push_cast; rfl
  rw [← hL]
  rw [hG, hdx] at hsh
  have hRb : R - b + k = (1 - b) / 2 := by rw [hRdef]; ring
  have hRbc : R - b + c + k = c + (1 - b) / 2 := by rw [hRdef]; ring
  rw [hRb, hRbc] at hsh
  have hb2 : poch ((1 - b) / 2) k ≠ 0 := by
    have := poch_reflect R k
    rw [show 1 - R - k = (1 - b) / 2 by rw [hRdef]; ring] at this
    rw [this]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (poch_ne_zero_of_not_neg_nat hR k)
  have hck : poch (c + k) k ≠ 0 := right_ne_zero_of_mul (hc2 ▸ hcn)
  have hc0 : poch c k ≠ 0 := left_ne_zero_of_mul (hc2 ▸ hcn)
  have hch : poch (c + 1 / 2) k ≠ 0 := by
    intro h0; exact hD (by rw [hdup, h0]; ring)
  have hfac := poch_two_mul_eq_four_pow_mul_poch 1 k
  rw [show ((1 : ℂ) + 1) / 2 = 1 by norm_num, poch_nat_one, poch_nat_one] at hfac
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h4 : (4 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [hdup, show 2 * c - c = c by ring, hc2,
    show ((2 * k).factorial : ℂ) = 4 ^ k * poch (1 / 2) k * k.factorial by
      exact_mod_cast hfac] at hsh
  rw [eq_div_iff (mul_ne_zero hb2 hch)]
  field_simp at hsh
  rw [show (c * 2 + 1) / 2 = c + 1 / 2 by ring, show c * 2 = 2 * c by ring,
    show (2 * c + (1 - b)) / 2 = c + (1 - b) / 2 by ring] at hsh
  linear_combination hsh

/-- Watson odd terminating evaluation for every regular displayed lower parameter. -/
@[dlmf 16.4.E6]
theorem genHG_watson_terminating_odd (k : ℕ) (b c : ℂ)
    (hb : GenDenRegular {(b - (2 * k + 1) + 1) / 2, 2 * c}) :
    genFiniteHG (2 * k + 1) {(-(2 * k + 1) : ℂ), b, c}
      {(b - (2 * k + 1) + 1) / 2, 2 * c} 1 = 0 := by
  set R : ℂ := (b - (2 * k + 1) + 1) / 2 with hRdef
  have hR : ∀ m : ℕ, R ≠ -m := hb _ (by simp)
  have h2c : ∀ m : ℕ, 2 * c ≠ -m := hb _ (by simp)
  have hD := poch_ne_zero_of_not_neg_nat h2c (2 * k + 1)
  have hcn : poch c (2 * k + 1) ≠ 0 := by
    refine poch_ne_zero_of_not_neg_nat (fun m hm => ?_) _
    exact h2c (2 * m) (by push_cast; linear_combination 2 * hm)
  have hrefl : poch (1 - 2 * c + c - ((2 * k + 1 : ℕ) : ℂ)) (2 * k + 1) =
      (-1) ^ (2 * k + 1) * poch c (2 * k + 1) := by
    rw [← poch_reflect]; congr 1; ring
  have hDP : poch (1 - 2 * c + c - ((2 * k + 1 : ℕ) : ℂ)) (2 * k + 1) ≠ 0 := by
    rw [hrefl]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hcn
  have hsh := genFiniteHG_sheppard (2 * k + 1) c b R (2 * c) hR hD hDP
  have hB : genPoch {1 - (R - b) - ((2 * k + 1 : ℕ) : ℂ), 1 - c - ((2 * k + 1 : ℕ) : ℂ)}
      (2 * k + 1) ≠ 0 := by
    simp only [genPoch, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton]
    refine mul_ne_zero ?_ ?_
    · convert poch_ne_zero_of_not_neg_nat hR (2 * k + 1) using 2
      rw [hRdef]; push_cast; ring
    · convert hDP using 2; ring
  have hdx := genHG_dixon_terminating_odd_of_poch k (R - b) c hB
  have hG : genFiniteHG (2 * k + 1) {(-((2 * k + 1 : ℕ) : ℂ)), c, R - b}
      {R, 1 + c - 2 * c - ((2 * k + 1 : ℕ) : ℂ)} 1 =
      genFiniteHG (2 * k + 1) {(-(2 * k + 1) : ℂ), R - b, c}
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
  have hL : genFiniteHG (2 * k + 1) {(-((2 * k + 1 : ℕ) : ℂ)), b, c} {R, 2 * c} 1 =
      genFiniteHG (2 * k + 1) {(-(2 * k + 1) : ℂ), b, c}
        {(b - (2 * k + 1) + 1) / 2, 2 * c} 1 := by
    push_cast; rfl
  rw [← hL]
  exact (mul_eq_zero.mp hsh).resolve_left hD

/-- Whipple 3F2 sum, including every terminating integer a. -/
@[dlmf 16.4.E7]
theorem genHG_whipple_3F2_sum (a c d : ℂ) (hb : GenDenRegular {d, 2 * c - d + 1})
    (h : 0 < c.re ∨ ∃ n : ℤ, a = n) :
    genHG {a, 1 - a, c} {d, 2 * c - d + 1} 1 =
      Real.pi * Gamma d * Gamma (2 * c - d + 1) * (2 : ℂ) ^ (1 - 2 * c) /
      (Gamma (c + (a - d + 1) / 2) * Gamma (c + 1 - (a + d) / 2) *
        Gamma ((a + d) / 2) * Gamma ((d - a + 1) / 2)) := by
  sorry

/-- Whipple terminating 3F2 sum in finite products. -/
@[dlmf 16.4.E8]
theorem genHG_whipple_3F2_terminating (n : ℕ) (a d : ℂ) (hb : GenDenRegular {d, 1 - d - 2 * n}) :
    genFiniteHG n {(-n : ℂ), a, 1 - a} {d, 1 - d - 2 * n} 1 =
      poch ((a + d) / 2) n * poch ((d - a + 1) / 2) n /
        (poch (d / 2) n * poch ((d + 1) / 2) n) := by
  sorry

/-- Dougall very well-poised 5F4 in its full absolute convergence half-space. -/
@[dlmf 16.4.E9]
theorem genHG_dougall_5F4_sum (a b c d : ℂ)
    (hb : GenDenRegular {a / 2, a - b + 1, a - c + 1, a - d + 1})
    (hconv : (b + c + d - a).re < 1) :
    genHG {a, a / 2 + 1, b, c, d} {a / 2, a - b + 1, a - c + 1, a - d + 1} 1 =
      Gamma (a - b + 1) * Gamma (a - c + 1) * Gamma (a - d + 1) *
        Gamma (a - b - c - d + 1) /
      (Gamma (a + 1) * Gamma (a - b - c + 1) *
        Gamma (a - b - d + 1) * Gamma (a - c - d + 1)) := by
  sorry

section DougallFinite

open DLMF.QSeries DLMF.QHypergeometric

/-- The normalized polynomial unit-Bailey factor has the expected classical limit. Bailey’s
cleared identity avoids square-root choices in the very-well-poised pair. -/
private lemma dougall_unitD_classical_limit (a : ℂ) (ha : a ≠ 0) (k : ℕ) :
    Tendsto (fun q : ℝ => DLMF.Bailey.unitD ((q : ℂ) ^ a) q k / (1 - (q : ℂ)) ^ k)
      (𝓝[<] 1) (𝓝 (poch a k * (a + 2 * k) / a)) := by
  have h := (tendsto_qPochhammer_normalized a k).mul
    ((tendsto_cpow_increment (a + 2 * k)).div (tendsto_cpow_increment a) ha)
  convert h.congr' ?_ using 1
  · ring
  filter_upwards [(tendsto_cpow_increment a).eventually_ne ha,
    Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with q hqa hq
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.1.ne'
  have hD : 1 - (q : ℂ) ≠ 0 := by
    intro h0
    have : q = 1 := by exact_mod_cast (sub_eq_zero.mp h0).symm
    exact hq.2.ne this
  have hA : 1 - (q : ℂ) ^ a ≠ 0 := by
    intro h0
    exact hqa (by rw [h0, zero_div])
  have hunit := DLMF.Bailey.qPochhammer_mul_one_sub_pow ((q : ℂ) ^ a) q k
  simp only [Pi.div_apply]
  rw [show (q : ℂ) ^ (a + 2 * k) = (q : ℂ) ^ a * (q : ℂ) ^ (2 * k : ℕ) by
    rw [Complex.cpow_add _ _ hq0]
    norm_cast]
  field_simp
  linear_combination hunit

/-- Dividing the unit-Bailey factor by the factorial q-Pochhammer gives its classical
coefficient normalization. -/
private lemma dougall_unitD_factorial_classical_limit (a : ℂ) (ha : a ≠ 0) (k : ℕ) :
    Tendsto (fun q : ℝ => DLMF.Bailey.unitD ((q : ℂ) ^ a) q k / qPochhammer q q k)
      (𝓝[<] 1) (𝓝 (poch a k * (a + 2 * k) / (a * (k.factorial : ℂ)))) := by
  have h := (dougall_unitD_classical_limit a ha k).div (tendsto_qPochhammer_normalized 1 k)
    (by simpa only [poch_nat_one] using
      (show (k.factorial : ℂ) ≠ 0 by exact_mod_cast k.factorial_ne_zero))
  simp only [Complex.cpow_one, poch_nat_one] at h
  convert h.congr' ?_ using 1
  · ring
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with q hq
  have hD : 1 - (q : ℂ) ≠ 0 := by
    intro h0
    have : q = 1 := by exact_mod_cast (sub_eq_zero.mp h0).symm
    exact hq.2.ne this
  simpa only [Pi.div_apply] using div_div_div_cancel_right₀ (pow_ne_zero k hD)
    (DLMF.Bailey.unitD ((q : ℂ) ^ a) q k) (qPochhammer q q k)

/-- The classical unit factor equals the usual half-parameter Pochhammer quotient whenever
the lower half-parameter is regular. -/
private lemma dougall_classical_unit_eq (a : ℂ) (ha : ∀ j : ℕ, a / 2 ≠ -j) (k : ℕ) :
    poch a k * (a + 2 * k) / a = poch a k * poch (a / 2 + 1) k / poch (a / 2) k := by
  have ha0 : a ≠ 0 := by intro h; simpa [h] using ha 0
  have hp := poch_ne_zero_of_not_neg_nat ha k
  have hs : (a / 2) * poch (a / 2 + 1) k = poch (a / 2) k * (a / 2 + k) := by
    rw [← poch_succ_left, poch_succ]
  generalize poch (a / 2 + 1) k = X at hs ⊢
  generalize poch (a / 2) k = Y at hs hp ⊢
  field_simp
  linear_combination -2 * poch a k * hs

/-- A finite q-Pochhammer product stays nonzero near the classical limit when its limiting
rising factorial is nonzero. -/
private lemma dougall_qPochhammer_eventually_ne_zero (a : ℂ) (n : ℕ) (ha : poch a n ≠ 0) :
    ∀ᶠ q : ℝ in 𝓝[<] 1, qPochhammer ((q : ℂ) ^ a) q n ≠ 0 := by
  filter_upwards [(tendsto_qPochhammer_normalized a n).eventually_ne ha] with q hq hzero
  exact hq (by rw [hzero, zero_div])

/-- The lower parameters and argument in the rational q-Dougall sum become sums and
differences of classical exponents. -/
private lemma dougall_qpow_params (a b c : ℂ) (n : ℕ) {q : ℂ} (hq : q ≠ 0) :
    q ^ a * q / q ^ b = q ^ (a - b + 1) ∧
    q ^ a * q ^ (n + 1) = q ^ (a + n + 1) ∧
    q ^ a * q ^ (n + 1) / (q ^ b * q ^ c) = q ^ (a + n + 1 - b - c) := by
  constructor
  · rw [Complex.cpow_add _ _ hq, Complex.cpow_sub _ _ hq, Complex.cpow_one]
    ring
  constructor
  · rw [show a + (n : ℂ) + 1 = a + ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.cpow_add _ _ hq, Complex.cpow_natCast]
  · rw [Complex.cpow_sub _ _ hq, Complex.cpow_sub _ _ hq,
      show a + (n : ℂ) + 1 = a + ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.cpow_add _ _ hq, Complex.cpow_natCast]
    ring

/-- Each rational terminating q-Dougall summand tends to the corresponding classical
very-well-poised `₅F₄` coefficient. -/
private lemma dougall_qterm_classical_limit (a b c : ℂ) (n k : ℕ)
    (hb : GenDenRegular {a / 2, a - b + 1, a - c + 1, a + n + 1}) :
    Tendsto (fun q : ℝ => sixTerm ((q : ℂ) ^ a) ((q : ℂ) ^ b) ((q : ℂ) ^ c) q n k)
      (𝓝[<] 1) (𝓝 (genCoeff {a, a / 2 + 1, b, c, (-n : ℂ)}
        {a / 2, a - b + 1, a - c + 1, a + n + 1} k)) := by
  have hA : ∀ j : ℕ, a / 2 ≠ -j := hb _ (by simp)
  have ha : a ≠ 0 := by intro h; simpa [h] using hA 0
  have hU := dougall_unitD_factorial_classical_limit a ha k
  have hR := tendsto_qPochhammerList_ratio [b, c, (-n : ℂ)]
    [a - b + 1, a - c + 1, a + n + 1] k rfl (by
      intro p hp j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> exact hb _ (by simp) j)
  have hq : Tendsto (fun q : ℝ => (q : ℂ)) (𝓝[<] 1) (𝓝 1) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun q : ℝ => (q : ℂ) ^ (a + n + 1 - b - c)) (𝓝[<] 1) (𝓝 1) := by
    simpa only [Function.comp_def, Complex.one_cpow] using
      (continuousAt_cpow_const (a := 1) (b := a + n + 1 - b - c)
      (by simp)).tendsto.comp hq
  convert ((hU.mul hR).mul (hz.pow k)).congr' ?_ using 1
  · congr 1
    simp only [genCoeff, genPoch, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton,
      Multiset.map_coe, Multiset.prod_coe, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, one_pow]
    rw [show poch a k * (a + 2 * k) / (a * (k.factorial : ℂ)) =
        (poch a k * (a + 2 * k) / a) / k.factorial by ring,
      dougall_classical_unit_eq a hA k]
    ring
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with q hq
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.1.ne'
  simp only [qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  have hB := (dougall_qpow_params a b c n hq0).1
  have hC := (dougall_qpow_params a c b n hq0).1
  obtain ⟨hN, hZ⟩ := (dougall_qpow_params a b c n hq0).2
  rw [sixTerm, hB, hC, hZ, hN,
    show (q : ℂ) ^ (-(n : ℤ)) = (q : ℂ) ^ (-(n : ℂ)) by
      rw [Complex.cpow_neg, Complex.cpow_natCast, zpow_neg, zpow_natCast]]
  ring

/-- Dougall terminating 5F4, with all removable cases retained by finite products. -/
@[dlmf 16.4.E9]
theorem genHG_dougall_5F4_terminating (n : ℕ) (a b c : ℂ)
    (hb : GenDenRegular {a / 2, a - b + 1, a - c + 1, a + n + 1}) :
    genFiniteHG n {a, a / 2 + 1, b, c, (-n : ℂ)}
      {a / 2, a - b + 1, a - c + 1, a + n + 1} 1 =
      poch (a + 1) n * poch (a - b - c + 1) n /
        (poch (a - b + 1) n * poch (a - c + 1) n) := by
  have hL := tendsto_finsetSum (range (n + 1)) fun k _ => dougall_qterm_classical_limit a b c n k hb
  have hR := tendsto_qPochhammerList_ratio [a + 1, a - b - c + 1]
    [a - b + 1, a - c + 1] n rfl (by
      intro p hp j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact hb _ (by simp) j)
  have hB := dougall_qPochhammer_eventually_ne_zero (a - b + 1) n
    (poch_ne_zero_of_not_neg_nat (hb _ (by simp)) n)
  have hC := dougall_qPochhammer_eventually_ne_zero (a - c + 1) n
    (poch_ne_zero_of_not_neg_nat (hb _ (by simp)) n)
  have hN := dougall_qPochhammer_eventually_ne_zero (a + n + 1) n
    (poch_ne_zero_of_not_neg_nat (hb _ (by simp)) n)
  have heq : (fun q : ℝ => ∑ k ∈ range (n + 1),
      sixTerm ((q : ℂ) ^ a) ((q : ℂ) ^ b) ((q : ℂ) ^ c) q n k) =ᶠ[𝓝[<] 1]
      (fun q => qPochhammerList ([a + 1, a - b - c + 1].map fun x => (q : ℂ) ^ x) q n /
        qPochhammerList ([a - b + 1, a - c + 1].map fun x => (q : ℂ) ^ x) q n) := by
    filter_upwards [hB, hC, hN, Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with q hB hC hN hq
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.1.ne'
    have hqn : ‖(q : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq.1]
      exact hq.2
    have hBpow := (dougall_qpow_params a b c n hq0).1
    have hCpow := (dougall_qpow_params a c b n hq0).1
    have hNpow := (dougall_qpow_params a b c n hq0).2.1
    have hS := sum_sixTerm_eq hq0 hqn n
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hq0))
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hq0))
      (by rwa [hBpow]) (by rwa [hCpow]) (by rwa [hNpow])
    have hAQ : (q : ℂ) ^ a * q = (q : ℂ) ^ (a + 1) := by
      rw [Complex.cpow_add _ _ hq0, Complex.cpow_one]
    have hABC : (q : ℂ) ^ a * q / ((q : ℂ) ^ b * (q : ℂ) ^ c) =
        (q : ℂ) ^ (a - b - c + 1) := by
      have h := (dougall_qpow_params a b c 0 hq0).2.2
      simpa only [Nat.cast_zero, add_zero, zero_add, pow_one,
        show a + 1 - b - c = a - b - c + 1 by ring] using h
    rw [hABC, hBpow, hCpow, hAQ] at hS
    simpa only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one] using hS
  have h := tendsto_nhds_unique hL (hR.congr' heq.symm)
  simpa [genFiniteHG, genPoch] using h

end DougallFinite

section DougallSeven

/-- The balancing relation reflects the last denominator Pochhammer into the regular lower
parameter paired with `f`, so that denominator stays nonzero. -/
private lemma dougall7_last_den_ne (n : ℕ) (a b c d f : ℂ)
    (hbal : 2 * a + 1 = b + c + d + f - n) (hF : poch (a - f + 1) n ≠ 0) :
    poch (a - b - c - d + 1) n ≠ 0 := by
  have hRef := poch_reflect (a - b - c - d + 1) n
  rw [show 1 - (a - b - c - d + 1) - n = a - f + 1 by linear_combination -hbal] at hRef
  intro hzero
  rw [hzero, mul_zero] at hRef
  exact hF hRef

/-- On a punctured neighborhood of any complex point, the nonpositive integers are avoided.
This combines their discreteness with openness of their complement. -/
private lemma dougall_eventually_not_neg_nat_at (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, ∀ j : ℕ, w ≠ -(j : ℂ) := by
  by_cases hz : ∀ j : ℕ, z ≠ -(j : ℂ)
  · exact nhdsWithin_le_nhds (isOpen_not_neg_nat.mem_nhds hz)
  · push Not at hz
    obtain ⟨j, rfl⟩ := hz
    exact eventually_nhdsWithin_ne_neg_nat j

/-- A fixed rising factorial is a polynomial in its parameter, hence continuous. -/
private lemma dougall_poch_continuous (k : ℕ) : Continuous (fun z : ℂ => poch z k) :=
  (ascPochhammer ℂ k).continuous

attribute [local fun_prop] dougall_poch_continuous

/-- Under the Dougall balance, Pochhammer reflection turns the Whipple prefactor times
Saalschütz’s value into the finite `₇F₆` product. -/
private lemma dougall7_product_eval (n : ℕ) (a b c d f : ℂ)
    (hbal : 2 * a + 1 = b + c + d + f - n)
    (hb : GenDenRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1}) :
    poch (a + 1) n * poch (a - d - f + 1) n / (poch (a - d + 1) n * poch (a - f + 1) n) *
      (poch (a - b + 1 - d) n * poch (a - b + 1 - f) n /
        (poch (a - b + 1) n * poch (a - b + 1 - d - f) n)) =
      poch (a + 1) n * poch (a - b - c + 1) n * poch (a - b - d + 1) n *
        poch (a - c - d + 1) n /
      (poch (a - b + 1) n * poch (a - c + 1) n * poch (a - d + 1) n *
        poch (a - b - c - d + 1) n) := by
  have hB := poch_ne_zero_of_not_neg_nat (hb (a - b + 1) (by simp)) n
  have hC := poch_ne_zero_of_not_neg_nat (hb (a - c + 1) (by simp)) n
  have hD := poch_ne_zero_of_not_neg_nat (hb (a - d + 1) (by simp)) n
  have hF := poch_ne_zero_of_not_neg_nat (hb (a - f + 1) (by simp)) n
  have hRef := poch_reflect (a - b - c - d + 1) n
  rw [show 1 - (a - b - c - d + 1) - n = a - f + 1 by linear_combination -hbal] at hRef
  have hBCD := dougall7_last_den_ne n a b c d f hbal hF
  rw [show a - d - f + 1 = 1 - (a - b - c + 1) - n by linear_combination hbal,
    poch_reflect, show a - b + 1 - d = a - b - d + 1 by ring,
    show a - b + 1 - f = 1 - (a - c - d + 1) - n by linear_combination hbal,
    poch_reflect, show a - b - d + 1 - f = 1 - (a - c + 1) - n by linear_combination hbal,
    poch_reflect, hRef]
  have hsign : (-1 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- Whipple’s terminating transformation and Saalschütz’s sum prove finite Dougall when the
parameter canceled from the transformed `₄F₃` is regular. -/
private lemma dougall7_generic (n : ℕ) (a b c d f : ℂ)
    (hbal : 2 * a + 1 = b + c + d + f - n)
    (hb : GenDenRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1})
    (hY : ∀ j : ℕ, a - b - c + 1 ≠ -j) :
    genFiniteHG n {a, a / 2 + 1, b, c, d, f, (-n : ℂ)}
      {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1} 1 =
      poch (a + 1) n * poch (a - b - c + 1) n * poch (a - b - d + 1) n *
        poch (a - c - d + 1) n /
      (poch (a - b + 1) n * poch (a - c + 1) n * poch (a - d + 1) n *
        poch (a - b - c - d + 1) n) := by
  have hYE : d + f - a - n = a - b - c + 1 := by linear_combination -hbal
  have hSA : 1 + d + f - (a - b + 1) - n = a - c + 1 := by linear_combination -hbal
  have hW := whipple_7F6 (a := a) (b := b) (c := c) (d := d) (e := f) n (by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hb _ (by simp)
    · exact hb _ (by simp)
    · exact hb _ (by simp)
    · exact hb _ (by simp)
    · exact hb _ (by simp)
    · exact hb _ (by simp)
    · rw [hYE]; exact hY)
  have hL : genFiniteHG n {a, a / 2 + 1, b, c, d, f, (-n : ℂ)}
      {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1} 1 =
      ∑ k ∈ range (n + 1),
        poch a k * poch (a / 2 + 1) k * poch b k * poch c k * poch d k * poch f k *
          poch (-n : ℂ) k /
          (poch (a / 2) k * poch (a - b + 1) k * poch (a - c + 1) k *
            poch (a - d + 1) k * poch (a - f + 1) k * poch (a + n + 1) k * k.factorial) := by
    unfold genFiniteHG
    refine sum_congr rfl fun k hk => ?_
    simp only [genCoeff, genPoch, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, one_pow, mul_one]
    ring
  have hR : (∑ k ∈ range (n + 1),
      poch (a - b - c + 1) k * poch d k * poch f k * poch (-n : ℂ) k /
        (poch (a - b + 1) k * poch (a - c + 1) k * poch (d + f - a - n) k * k.factorial)) =
      ∑ k ∈ range (n + 1), poch (-n : ℂ) k * poch d k * poch f k /
        (poch (a - b + 1) k * poch (a - c + 1) k * k.factorial) := by
    refine sum_congr rfl fun k hk => ?_
    rw [hYE]
    have hYk := poch_ne_zero_of_not_neg_nat hY k
    have hBk := poch_ne_zero_of_not_neg_nat (hb (a - b + 1) (by simp)) k
    have hCk := poch_ne_zero_of_not_neg_nat (hb (a - c + 1) (by simp)) k
    have hFk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  have hS := pfaff_saalschutz n (a := d) (b := f) (c := a - b + 1)
    (hb _ (by simp)) (by rw [hSA]; exact poch_ne_zero_of_not_neg_nat (hb _ (by simp)) n)
  rw [hSA] at hS
  rw [← hL, hR, hS] at hW
  exact hW.trans (dougall7_product_eval n a b c d f hbal hb)

/-- The difference of the finite Dougall sum and its product is continuous in a varying
parameter, because the displayed denominators are nonzero at the reference point. -/
private lemma dougall7_difference_continuous (n : ℕ) (a b c d f : ℂ) (F : ℂ → ℂ)
    (hFB : F b = f) (hFc : Continuous F)
    (hbal : 2 * a + 1 = b + c + d + f - n)
    (hb : GenDenRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1}) :
    ContinuousAt (fun t : ℂ =>
    genFiniteHG n {a, a / 2 + 1, t, c, d, F t, (-n : ℂ)}
      {a / 2, a - t + 1, a - c + 1, a - d + 1, a - F t + 1, a + n + 1} 1 -
      poch (a + 1) n * poch (a - t - c + 1) n * poch (a - t - d + 1) n *
        poch (a - c - d + 1) n /
      (poch (a - t + 1) n * poch (a - c + 1) n * poch (a - d + 1) n *
        poch (a - t - c - d + 1) n)) b := by
  refine ContinuousAt.sub ?_ ?_
  · simp only [genFiniteHG]
    refine tendsto_finsetSum _ fun k hk => ?_
    have hden : genPoch {a / 2, a - b + 1, a - c + 1, a - d + 1, a - F b + 1, a + n + 1} k *
        (k.factorial : ℂ) ≠ 0 := by
      rw [hFB]
      exact mul_ne_zero (genPoch_ne_zero hb k) (by exact_mod_cast k.factorial_ne_zero)
    simp only [genPoch, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton] at hden
    have hc : ContinuousAt (fun t : ℂ => genCoeff
        {a, a / 2 + 1, t, c, d, F t, (-n : ℂ)}
        {a / 2, a - t + 1, a - c + 1, a - d + 1, a - F t + 1, a + n + 1} k) b := by
      simp only [genCoeff, genPoch, Multiset.insert_eq_cons, Multiset.map_cons,
        Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
      fun_prop (disch := exact hden)
    simpa only [one_pow, mul_one] using hc.tendsto
  · have hden : poch (a - b + 1) n * poch (a - c + 1) n * poch (a - d + 1) n *
        poch (a - b - c - d + 1) n ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero
        (poch_ne_zero_of_not_neg_nat (hb _ (by simp)) n)
        (poch_ne_zero_of_not_neg_nat (hb _ (by simp)) n))
        (poch_ne_zero_of_not_neg_nat (hb _ (by simp)) n))
        (dougall7_last_den_ne n a b c d f hbal (poch_ne_zero_of_not_neg_nat (hb _ (by simp)) n))
    fun_prop (disch := exact hden)

/-- Dougall terminating 2-balanced 7F6, including n=0. -/
@[dlmf 16.4.E10]
theorem genHG_dougall_7F6 (n : ℕ) (a b c d f : ℂ)
    (hbal : 2 * a + 1 = b + c + d + f - n)
    (hb : GenDenRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1}) :
    genFiniteHG n {a, a / 2 + 1, b, c, d, f, (-n : ℂ)}
      {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1} 1 =
      poch (a + 1) n * poch (a - b - c + 1) n * poch (a - b - d + 1) n *
        poch (a - c - d + 1) n /
      (poch (a - b + 1) n * poch (a - c + 1) n * poch (a - d + 1) n *
        poch (a - b - c - d + 1) n) := by
  let F : ℂ → ℂ := fun t => f + b - t
  have hFB : F b = f := by dsimp [F]; ring
  have hFc : Continuous F := by dsimp [F]; fun_prop
  let G : ℂ → ℂ := fun t =>
    genFiniteHG n {a, a / 2 + 1, t, c, d, F t, (-n : ℂ)}
      {a / 2, a - t + 1, a - c + 1, a - d + 1, a - F t + 1, a + n + 1} 1 -
      poch (a + 1) n * poch (a - t - c + 1) n * poch (a - t - d + 1) n *
        poch (a - c - d + 1) n /
      (poch (a - t + 1) n * poch (a - c + 1) n * poch (a - d + 1) n *
        poch (a - t - c - d + 1) n)
  have hB := (show ContinuousAt (fun t : ℂ => a - t + 1) b by fun_prop).tendsto.eventually
    (isOpen_not_neg_nat.mem_nhds (hb (a - b + 1) (by simp)))
  have hF := (show ContinuousAt (fun t : ℂ => a - F t + 1) b by fun_prop).tendsto.eventually
    (isOpen_not_neg_nat.mem_nhds (by rw [hFB]; exact hb (a - f + 1) (by simp)))
  have hmap : Tendsto (fun t : ℂ => a - t - c + 1) (𝓝[≠] b) (𝓝[≠] (a - b - c + 1)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (show ContinuousAt (fun t : ℂ => a - t - c + 1) b by fun_prop).tendsto.mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change t ≠ b at ht
      change a - t - c + 1 ≠ a - b - c + 1
      intro heq
      apply ht
      linear_combination -heq
  have hY := hmap.eventually (dougall_eventually_not_neg_nat_at (a - b - c + 1))
  have heq : G =ᶠ[𝓝[≠] b] fun _ => 0 := by
    filter_upwards [nhdsWithin_le_nhds hB, nhdsWithin_le_nhds hF, hY] with t hBt hFt hYt
    have hbt : GenDenRegular {a / 2, a - t + 1, a - c + 1, a - d + 1, a - F t + 1, a + n + 1} := by
      intro z hz
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hb _ (by simp)
      · exact hBt
      · exact hb _ (by simp)
      · exact hb _ (by simp)
      · exact hFt
      · exact hb _ (by simp)
    exact sub_eq_zero.mpr (dougall7_generic n a t c d (F t)
      (by dsimp [F]; linear_combination hbal) hbt hYt)
  have hg : ContinuousAt G b :=
    dougall7_difference_continuous n a b c d f F hFB hFc hbal hb
  have hzero : G b = 0 := tendsto_nhds_unique
    (hg.tendsto.mono_left nhdsWithin_le_nhds) (tendsto_const_nhds.congr' heq.symm)
  simpa only [G, hFB, sub_eq_zero] using hzero

end DougallSeven

/-- The two convergent 3F2 unity sums in the common region. -/
@[dlmf 16.4.E11]
theorem genHG_3F2_unit_transformation (a b c d e : ℂ)
    (hb : GenDenRegular {d, e, d + e - b - c})
    (hconv : 0 < (d + e - a - b - c).re) (hea : 0 < (e - a).re) :
    genHG {a, b, c} {d, e} 1 = Gamma e * Gamma (d + e - a - b - c) /
      (Gamma (e - a) * Gamma (d + e - b - c)) *
      genHG {a, d - b, d - c} {d, d + e - b - c} 1 := by
  sorry

/-- A balanced three-over-two unit series sums to the declared value throughout its
absolute-convergence region, including every terminating upper-parameter case. -/
private lemma hasSum_gen3F2_one {a b c d e : ℂ} (hb : GenDenRegular {d, e})
    (hconv : 0 < (d + e - a - b - c).re ∨ GenTerminates {a, b, c}) :
    HasSum (genCoeff {a, b, c} {d, e}) (genHG {a, b, c} {d, e} 1) := by
  rcases hconv with hconv | ha
  · apply genHG_one_hasSum (by simp) hb
    have hE : genExcess {a, b, c} {d, e} = d + e - a - b - c := by
      simp only [genExcess, Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
      ring
    rw [hE]
    exact hconv
  · exact genHG_one_hasSum_of_summable hb (genCoeff_summable_of_terminates ha)

/-- Consecutive coefficients of the second unity recurrence form an exact telescope. -/
private lemma genCoeff_second_unit_recurrence_telescope (a b c d e : ℂ)
    (hb : GenDenRegular {d, d + 1, e, e + 1}) (n : ℕ) :
    genCoeff {a, b, c} {d, e} (n + 1) -
      c * (e - a) / (d * e) * genCoeff {a, b + 1, c + 1} {d + 1, e + 1} (n + 1) -
      (d - c) / d * genCoeff {a, b + 1, c} {d + 1, e} (n + 1) =
      a * c / (d * e) * (genCoeff {a + 1, b + 1, c + 1} {d + 1, e + 1} (n + 1) -
        genCoeff {a + 1, b + 1, c + 1} {d + 1, e + 1} n) := by
  have hd : d ≠ 0 := by simpa using hb d (by simp) 0
  have he : e ≠ 0 := by simpa using hb e (by simp) 0
  have hdP : poch (d + 1) n ≠ 0 := poch_ne_zero_of_not_neg_nat (hb (d + 1) (by simp)) n
  have heP : poch (e + 1) n ≠ 0 := poch_ne_zero_of_not_neg_nat (hb (e + 1) (by simp)) n
  have hdn : d + 1 + n ≠ 0 := by
    intro hx
    exact hb (d + 1) (by simp) n (by linear_combination hx)
  have hen : e + 1 + n ≠ 0 := by
    intro hx
    exact hb (e + 1) (by simp) n (by linear_combination hx)
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  simp only [genCoeff, genPoch, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
  simp only [poch_succ_left a n, poch_succ_left b n, poch_succ_left c n,
    poch_succ_left d n, poch_succ_left e n]
  simp only [poch_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp [hd, he, hdP, heP, hdn, hen, hf, hn]
  ring

/-- Raising one regular lower parameter gives a linear relation between coefficients. -/
private lemma genCoeff_lower_add_one (a b c d e : ℂ) (hb : GenDenRegular {d, e}) (n : ℕ) :
    (d + n) * genCoeff {a, b, c} {d + 1, e} n = d * genCoeff {a, b, c} {d, e} n := by
  have hd : d ≠ 0 := by simpa using hb d (by simp) 0
  have hdn : d + n ≠ 0 := by
    intro hx
    exact hb d (by simp) n (by linear_combination hx)
  have hdP : poch d n ≠ 0 := poch_ne_zero_of_not_neg_nat (hb d (by simp)) n
  have heP : poch e n ≠ 0 := poch_ne_zero_of_not_neg_nat (hb e (by simp)) n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hp : poch (d + 1) n = poch d n * (d + n) / d := by
    apply (eq_div_iff hd).2
    rw [← poch_succ, poch_succ_left]
    ring
  simp only [genCoeff, genPoch, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
  rw [hp]
  field_simp [hd, hdn, hdP, heP, hf]

/-- The first unit recurrence is an exact difference of adjacent weighted coefficients. -/
private lemma genCoeff_first_unit_recurrence_telescope (a b c d e : ℂ)
    (hb : GenDenRegular {d - 1, d, d + 1, e}) (n : ℕ) :
    (a - d) * (b - d) * (c - d) *
      (genCoeff {a, b, c} {d + 1, e} n - genCoeff {a, b, c} {d, e} n) +
      a * b * c * genCoeff {a, b, c} {d, e} n -
      d * (d - 1) * (a + b + c - d - e + 1) *
        (genCoeff {a, b, c} {d, e} n - genCoeff {a, b, c} {d - 1, e} n) =
      d * ((n + 1) * (e + n) * genCoeff {a, b, c} {d, e} (n + 1) -
        n * (e + n - 1) * genCoeff {a, b, c} {d, e} n) := by
  have hb0 : GenDenRegular {d, e} := by
    intro z hz
    exact hb z (by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
                     at hz ⊢; tauto)
  have hbm : GenDenRegular {d - 1, e} := by
    intro z hz
    exact hb z (by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
                     at hz ⊢; tauto)
  have hRaise := genCoeff_lower_add_one a b c d e hb0 n
  have hLower := genCoeff_lower_add_one a b c (d - 1) e hbm n
  rw [show d - 1 + 1 = d by ring] at hLower
  have hSucc := genCoeff_succ_mul (a := {a, b, c}) hb0 n
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton] at hSucc
  have hdn : d + (n : ℂ) ≠ 0 := by
    intro hx
    exact hb d (by simp) n (by linear_combination hx)
  apply mul_left_cancel₀ hdn
  linear_combination (a - d) * (b - d) * (c - d) * hRaise +
    - (d + n) * d * (a + b + c - d - e + 1) * hLower - d * hSucc
/-- The weighted boundary coefficient in the first unit recurrence tends to zero. -/
private lemma tendsto_genCoeff_boundary_zero (a b c d e : ℂ) (hb : GenDenRegular {d, e})
    (hconv : 1 < (d + e - a - b - c).re ∨ GenTerminates {a, b, c}) :
    Tendsto (fun n : ℕ => d * n * (e + n - 1) * genCoeff {a, b, c} {d, e} n)
      atTop (𝓝 0) := by
  have hw := genCoeff_mul_pow_tendsto_zero (a := {a, b, c}) (b := {d, e}) (by simp) hb 2
    (by
      simpa only [genExcess, Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton,
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
theorem genHG_3F2_unit_recurrence (a b c d e : ℂ) (hb : GenDenRegular {d - 1, d, d + 1, e})
    (hconv : 1 < (d + e - a - b - c).re ∨ GenTerminates {a, b, c}) :
    (a - d) * (b - d) * (c - d) *
      (genHG {a, b, c} {d + 1, e} 1 - genHG {a, b, c} {d, e} 1) +
      a * b * c * genHG {a, b, c} {d, e} 1 =
    d * (d - 1) * (a + b + c - d - e + 1) *
      (genHG {a, b, c} {d, e} 1 - genHG {a, b, c} {d - 1, e} 1) := by
  have hb0 : GenDenRegular {d, e} := by
    intro z hz
    exact hb z (by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
                     at hz ⊢; tauto)
  have hbp : GenDenRegular {d + 1, e} := by
    intro z hz
    exact hb z (by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
                     at hz ⊢; tauto)
  have hbm : GenDenRegular {d - 1, e} := by
    intro z hz
    exact hb z (by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
                     at hz ⊢; tauto)
  have hc0 : 0 < (d + e - a - b - c).re ∨ GenTerminates {a, b, c} := by
    rcases hconv with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr h
  have hcp : 0 < (d + 1 + e - a - b - c).re ∨ GenTerminates {a, b, c} := by
    rcases hconv with h | h
    · exact Or.inl (by simp only [add_re, sub_re, one_re] at h ⊢; linarith)
    · exact Or.inr h
  have hcm : 0 < (d - 1 + e - a - b - c).re ∨ GenTerminates {a, b, c} := by
    rcases hconv with h | h
    · exact Or.inl (by simp only [add_re, sub_re, one_re] at h ⊢; linarith)
    · exact Or.inr h
  let P := (a - d) * (b - d) * (c - d)
  let Q := d * (d - 1) * (a + b + c - d - e + 1)
  let C := fun n => P * (genCoeff {a, b, c} {d + 1, e} n - genCoeff {a, b, c} {d, e} n) +
    a * b * c * genCoeff {a, b, c} {d, e} n -
    Q * (genCoeff {a, b, c} {d, e} n - genCoeff {a, b, c} {d - 1, e} n)
  let U := fun n : ℕ => d * n * (e + n - 1) * genCoeff {a, b, c} {d, e} n
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
      have h := genCoeff_first_unit_recurrence_telescope a b c d e hb N
      change C N = _ at h
      rw [h]
      dsimp [U]
      push_cast
      ring
  have hlim := hC.tendsto_sum_nat
  simp_rw [hsum] at hlim
  have heq := tendsto_nhds_unique hlim (tendsto_genCoeff_boundary_zero a b c d e hb0 hconv)
  exact sub_eq_zero.mp heq

/-- The second unity recurrence, with the full common convergence half-space. -/
@[dlmf 16.4.E13]
theorem genHG_3F2_unit_recurrence_two (a b c d e : ℂ) (hb : GenDenRegular {d, d + 1, e, e + 1})
    (hconv : 0 < (d + e - a - b - c).re) :
    genHG {a, b, c} {d, e} 1 = c * (e - a) / (d * e) *
      genHG {a, b + 1, c + 1} {d + 1, e + 1} 1 +
      (d - c) / d * genHG {a, b + 1, c} {d + 1, e} 1 := by
  have hbparts : (∀ n : ℕ, d ≠ -n) ∧ (∀ n : ℕ, d + 1 ≠ -n) ∧
      (∀ n : ℕ, e ≠ -n) ∧ (∀ n : ℕ, e + 1 ≠ -n) := by
    simpa [GenDenRegular] using hb
  have hb0 : GenDenRegular {d, e} := by
    simpa [GenDenRegular] using And.intro hbparts.1 hbparts.2.2.1
  have hb1 : GenDenRegular {d + 1, e + 1} := by
    simpa [GenDenRegular] using And.intro hbparts.2.1 hbparts.2.2.2
  have hb2 : GenDenRegular {d + 1, e} := by
    simpa [GenDenRegular] using And.intro hbparts.2.1 hbparts.2.2.1
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
  let C : ℕ → ℂ := fun n => genCoeff {a, b, c} {d, e} n -
    c * (e - a) / (d * e) * genCoeff {a, b + 1, c + 1} {d + 1, e + 1} n -
    (d - c) / d * genCoeff {a, b + 1, c} {d + 1, e} n
  let V : ℕ → ℂ := fun n => a * c / (d * e) *
    genCoeff {a + 1, b + 1, c + 1} {d + 1, e + 1} n
  have hC : HasSum C (genHG {a, b, c} {d, e} 1 - c * (e - a) / (d * e) *
      genHG {a, b + 1, c + 1} {d + 1, e + 1} 1 -
      (d - c) / d * genHG {a, b + 1, c} {d + 1, e} 1) :=
    (h0.sub (h1.mul_left _)).sub (h2.mul_left _)
  have hsum (N : ℕ) : ∑ n ∈ range (N + 1), C n = V N := by
    induction N with
    | zero =>
      simp [C, V, genCoeff, genPoch, poch_zero]
      have hd : d ≠ 0 := by simpa using hbparts.1 0
      have he : e ≠ 0 := by simpa using hbparts.2.2.1 0
      field_simp [hd, he]
      ring
    | succ N ih =>
      rw [sum_range_succ, ih]
      dsimp only [C, V]
      rw [genCoeff_second_unit_recurrence_telescope a b c d e hb N]
      ring
  have hv0 := genCoeff_tendsto_zero (a := {a + 1, b + 1, c + 1})
    (b := {d + 1, e + 1}) (by simp) hb1 (Or.inl (by
      simp only [genExcess, Multiset.insert_eq_cons, Multiset.sum_cons,
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
theorem genHG_balanced_4F3_transformation (n : ℕ) (a b c d e f : ℂ)
    (hbal : a + b + c - n + 1 = d + e + f)
    (hb : GenDenRegular {d, e, f, a - e - n + 1, a - f - n + 1}) :
    genFiniteHG n {(-n : ℂ), a, b, c} {d, e, f} 1 =
      poch (e - a) n * poch (f - a) n / (poch e n * poch f n) *
        genFiniteHG n {(-n : ℂ), a, d - b, d - c}
          {d, a - e - n + 1, a - f - n + 1} 1 := by
  have hd : ∀ k : ℕ, d ≠ -k := hb d (by simp)
  have he : ∀ k : ℕ, e ≠ -k := hb e (by simp)
  have hf : ∀ k : ℕ, f ≠ -k := hb f (by simp)
  have he' : ∀ k : ℕ, a - e - n + 1 ≠ -k := hb _ (by simp)
  have hf' : ∀ k : ℕ, a - f - n + 1 ≠ -k := hb _ (by simp)
  have hconv := balanced_4F3_convolution_of_regular a b c e f d he hf hd n
    (by linear_combination hbal)
  simp only [genFiniteHG, genCoeff, genPoch, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, one_pow, mul_one]
  rw [Finset.mul_sum]
  convert hconv using 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ n := by simpa using hj
    have hn : n = (n - j) + j := by omega
    have hEa : poch (e - a) n = poch (e - a) (n - j) * poch (e - a + ((n - j : ℕ) : ℂ)) j := by
      rw [← poch_add, ← hn]
    have hFa : poch (f - a) n = poch (f - a) (n - j) * poch (f - a + ((n - j : ℕ) : ℂ)) j := by
      rw [← poch_add, ← hn]
    have hEn : poch e n = poch e j * poch (e + j) (n - j) := by
      rw [← poch_add, Nat.add_sub_cancel' hj']
    have hFn : poch f n = poch f j * poch (f + j) (n - j) := by
      rw [← poch_add, Nat.add_sub_cancel' hj']
    have hRe : poch (a - e - n + 1) j = (-1) ^ j * poch (e - a + ((n - j : ℕ) : ℂ)) j := by
      rw [← poch_reflect]; congr 1; push_cast [Nat.cast_sub hj']; ring
    have hRf : poch (a - f - n + 1) j = (-1) ^ j * poch (f - a + ((n - j : ℕ) : ℂ)) j := by
      rw [← poch_reflect]; congr 1; push_cast [Nat.cast_sub hj']; ring
    have h1 := poch_ne_zero_of_not_neg_nat he j
    have h2 := poch_ne_zero_of_not_neg_nat hf j
    have h3 := poch_ne_zero_of_not_neg_nat (not_neg_nat_add_nat he j) (n - j)
    have h4 := poch_ne_zero_of_not_neg_nat (not_neg_nat_add_nat hf j) (n - j)
    have h5 := poch_ne_zero_of_not_neg_nat he' j
    have h6 := poch_ne_zero_of_not_neg_nat hf' j
    have h7 := poch_ne_zero_of_not_neg_nat hd j
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
theorem genHG_whipple_nonterminating_left (n : ℕ) (a b c d e f : ℂ) (hn : a - b - c + 1 = -n)
    (hb : GenDenRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - e + 1, a - f + 1,
      d + e + f - a}) (hconv : 0 < (2 * a + 2 - b - c - d - e - f).re) :
    genHG {a, a / 2 + 1, b, c, d, e, f}
      {a / 2, a - b + 1, a - c + 1, a - d + 1, a - e + 1, a - f + 1} 1 =
      Gamma (a - d + 1) * Gamma (a - e + 1) * Gamma (a - f + 1) *
      Gamma (a - d - e - f + 1) /
      (Gamma (a + 1) * Gamma (a - d - e + 1) *
        Gamma (a - d - f + 1) * Gamma (a - e - f + 1)) *
      genFiniteHG n {a - b - c + 1, d, e, f}
        {a - b + 1, a - c + 1, d + e + f - a} 1 := by
  sorry

/-- Normalized Dougall bilateral sum in its full absolute convergence region. -/
@[dlmf 16.4.E17]
theorem genHG_dougall_bilateral (a b c d : ℂ) (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k)
    (hcd : GenDenRegular {c, d}) (hconv : 1 < (c + d - a - b).re) :
    genBilateralHG {a, b} {c, d} 1 =
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
  have hterm (n : ℤ) : genBilateralCoeff {a, b} {c, d} n * (1 : ℂ) ^ n =
      Gamma c * Gamma d / (Gamma a * Gamma b) *
        (Gamma (a + n) * Gamma (b + n) / (Gamma (c + n) * Gamma (d + n))) := by
    simp only [genBilateralCoeff, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, one_zpow,
      mul_one, genIntPoch_eq_Gamma_div ha', genIntPoch_eq_Gamma_div hb',
      genIntPoch_eq_Gamma_div hc', genIntPoch_eq_Gamma_div hd']
    field_simp
  have hconv' : 1 + (a + b).re < (c + d).re := by
    simp only [Complex.sub_re, Complex.add_re] at hconv ⊢
    linarith
  unfold genBilateralHG
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
theorem genHG_whipple_general (a b c d e f : ℂ)
    (hb : GenDenRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - e + 1,
      a - f + 1, d + e + f - a})
    (hnum : GenDenRegular {a - d - e - f + 1})
    (hterm : GenTerminates {a - b - c + 1, d, e, f})
    (hconv : 0 < (2 * a + 2 - b - c - d - e - f).re ∨
      GenTerminates {a, b, c, d, e, f}) :
    genHG {a, a / 2 + 1, b, c, d, e, f}
      {a / 2, a - b + 1, a - c + 1, a - d + 1, a - e + 1, a - f + 1} 1 =
      Gamma (a - d + 1) * Gamma (a - e + 1) * Gamma (a - f + 1) *
      Gamma (a - d - e - f + 1) /
      (Gamma (a + 1) * Gamma (a - d - e + 1) *
        Gamma (a - d - f + 1) * Gamma (a - e - f + 1)) *
      genHG {a - b - c + 1, d, e, f} {a - b + 1, a - c + 1, d + e + f - a} 1 := by
  sorry

/-- The Thomae expression supplies parameter continuation beyond the original unit
series region; at Gamma poles its totalized value is not an assigned finite limit. -/
@[dlmf 16.4.E11]
def gen3F2UnitThomae (a b c d e : ℂ) : ℂ :=
  Gamma e * Gamma (d + e - a - b - c) /
    (Gamma (e - a) * Gamma (d + e - b - c)) *
    genHG {a, d - b, d - c} {d, d + e - b - c} 1

/-- Joint analyticity in the convergent unit-series parameter region (16.4, prose). -/
private lemma analyticOnNhd_genHG_three_two_one_params :
    AnalyticOnNhd ℂ (fun P : Fin 5 → ℂ => genHG {P 0, P 1, P 2} {P 3, P 4} 1)
      {P | GenDenRegular {P 3, P 4} ∧ 0 < (P 3 + P 4 - P 0 - P 1 - P 2).re} := by
  sorry

/-- The continued expression is jointly analytic at its regular parameter points in
the full printed e−a half-space, including points outside original series convergence. -/
@[dlmf 16.4.E11]
theorem analyticOnNhd_gen3F2UnitThomae_params :
    AnalyticOnNhd ℂ (fun P : Fin 5 → ℂ => gen3F2UnitThomae (P 0) (P 1) (P 2) (P 3) (P 4))
      {P | GenDenRegular {P 3, P 4, P 3 + P 4 - P 1 - P 2,
        P 3 + P 4 - P 0 - P 1 - P 2} ∧ 0 < (P 4 - P 0).re} := by
  sorry

end DLMF.Hypergeometric
