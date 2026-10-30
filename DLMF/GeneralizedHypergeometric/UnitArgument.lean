/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.ParameterAndSeriesProperties
public import DLMF.Hypergeometric.Identities
public import DLMF.Hypergeometric.Saalschutz
public import DLMF.QHypergeometric.HigherSummations

/-!
# Argument unity: DLMF §16.4

Existing proofs of Pfaff–Saalschütz, Dixon, terminating Whipple, and Dougall's bilateral
sum are reused and indexed by the coverage ledger. Finite parity and finite Dougall
identities use Pochhammer quotients, which retain the removable cases hidden by
quotients of poles in the printed Gamma formulas. Lower parameters retain the
chapter's nonpositive-integer exclusions, except the explicitly canceled finite pair
in 16.4.2_5. Convergence at unity is always stated before using a nonterminating sum.
The odd terminating Dixon evaluation follows from finite inversion. The normalized
bilateral evaluation reuses the proved local `dougall_bilateral` and Mathlib's
`Complex.Gamma_mul_Gamma_one_sub`, preserving integral lower parameters. The finite Dougall
`₅F₄` evaluation is the q→1 limit of the proved rational terminating `₆φ₅` identity
`DLMF.QHypergeometric.qbR4_six_rational`, with Bailey’s polynomial unit factor handling the
very-well-poised pair without square-root branch restrictions. Finite Dougall `₇F₆` follows
from the proved Whipple transformation and Saalschütz sum, with continuity of finite
rational sums retaining the removable canceled-parameter cases.
-/

@[expose] public section
open Complex Filter Set Finset
open scoped Topology Real
noncomputable section
namespace DLMF.Hypergeometric

/-- Well-poised parameter vectors, in exactly the indexing order of16.4.1. -/
@[dlmf 16.4.E1]
def genWellPoised {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ) : Prop :=
  ∀ j, a j.castSucc + b j = a (Fin.last q) + 1

/-- Very well-poised vectors also differ by one in their first corresponding entries. -/
def genVeryWellPoised {q : ℕ} (a : Fin (q + 2) → ℂ) (b : Fin (q + 1) → ℂ) : Prop :=
  genWellPoised a b ∧ a 0 = b 0 + 1

/-- A k-balanced terminating unity series (16.4.2); balanced means k=1. -/
@[dlmf 16.4.E2]
def genKBalanced {q : ℕ} (k : ℤ) (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ) : Prop :=
  (∃ n : ℕ, a (Fin.last q) = -n) ∧ (∑ j, a j) + k = ∑ j, b j

/-- The canceled finite 3F2 sum in a form without an artificial singularity at c=1. -/
@[dlmf 16.4.E2_5]
theorem genHG_finite_ratio_sum (n : ℕ) (a c : ℂ) (hc : genDenRegular {c}) :
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
    simp only [genCoeff, genPoch, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton, one_pow, mul_one, poch_nat_one]
    field_simp [hn, hf, hc' k]
  · induction n with
    | zero =>
      have hc0 : c ≠ 0 := by simpa using hc c (by simp) 0
      simp only [sum_range_one, poch_zero, poch_one, div_one, Nat.cast_zero, add_zero, zero_add, mul_one]
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
theorem genHG_finite_ratio_sum_closed (n : ℕ) (a c : ℂ) (hc : genDenRegular {c})
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
theorem genHG_finite_ratio_sum_limit (n : ℕ) (a : ℂ) (ha : genDenRegular {a}) :
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
theorem genHG_finite_ratio_sum_zero (n : ℕ) : (∑ k ∈ range (n + 1), poch (0 : ℂ) k / poch 1 k) = 1 := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, poch_zero_succ, zero_div, add_zero]

/-- Dixon even terminating evaluation with all removable Gamma ratios replaced by finite products. -/
@[dlmf 16.4.E5]
theorem genHG_dixon_terminating_even (k : ℕ) (b c : ℂ) (hb : genDenRegular {1 - b - 2 * k, 1 - c - 2 * k}) :
    genFiniteHG (2 * k) {(-(2 * k) : ℂ), b, c}
      {1 - b - 2 * k, 1 - c - 2 * k} 1 =
      (2 * k).factorial * poch (b + c + k) k /
        (k.factorial * poch (b + k) k * poch (c + k) k) := by
  sorry

/-- Dixon odd terminating evaluation, retaining every regular lower-parameter case. -/
@[dlmf 16.4.E5]
theorem genHG_dixon_terminating_odd (k : ℕ) (b c : ℂ)
    (hb : genDenRegular {1 - b - (2 * k + 1), 1 - c - (2 * k + 1)}) :
    genFiniteHG (2 * k + 1) {(-(2 * k + 1) : ℂ), b, c}
      {1 - b - (2 * k + 1), 1 - c - (2 * k + 1)} 1 = 0 := by
  let N := 2 * k + 1
  have hB : genPoch {1 - b - N, 1 - c - N} N ≠ 0 := by
    simpa only [N, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using genPoch_ne_zero hb N
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
  simpa only [N, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Multiset.insert_eq_cons] using hzero

/-- Watson sum in the full absolute convergence half-space. -/
@[dlmf 16.4.E6]
theorem genHG_watson_sum (a b c : ℂ) (hb : genDenRegular {(a + b + 1) / 2, 2 * c})
    (hconv : -1 < (2 * c - a - b).re) :
    genHG {a, b, c} {(a + b + 1) / 2, 2 * c} 1 =
      Gamma (1 / 2) * Gamma (c + 1 / 2) * Gamma ((a + b + 1) / 2) *
      Gamma (c + (1 - a - b) / 2) /
      (Gamma ((a + 1) / 2) * Gamma ((b + 1) / 2) *
        Gamma (c + (1 - a) / 2) * Gamma (c + (1 - b) / 2)) := by
  sorry

/-- Watson even terminating evaluation without extra Gamma-pole exclusions. -/
@[dlmf 16.4.E6]
theorem genHG_watson_terminating_even (k : ℕ) (b c : ℂ) (hb : genDenRegular {(b - 2 * k + 1) / 2, 2 * c}) :
    genFiniteHG (2 * k) {(-(2 * k) : ℂ), b, c}
      {(b - 2 * k + 1) / 2, 2 * c} 1 =
      poch (1 / 2) k * poch (c + (1 - b) / 2) k /
        (poch ((1 - b) / 2) k * poch (c + 1 / 2) k) := by
  sorry

/-- Watson odd terminating evaluation for every regular displayed lower parameter. -/
@[dlmf 16.4.E6]
theorem genHG_watson_terminating_odd (k : ℕ) (b c : ℂ) (hb : genDenRegular {(b - (2 * k + 1) + 1) / 2, 2 * c}) :
    genFiniteHG (2 * k + 1) {(-(2 * k + 1) : ℂ), b, c}
      {(b - (2 * k + 1) + 1) / 2, 2 * c} 1 = 0 := by
  sorry

/-- Whipple 3F2 sum, including every terminating integer a. -/
@[dlmf 16.4.E7]
theorem genHG_whipple_3F2_sum (a c d : ℂ) (hb : genDenRegular {d, 2 * c - d + 1})
    (h : 0 < c.re ∨ ∃ n : ℤ, a = n) :
    genHG {a, 1 - a, c} {d, 2 * c - d + 1} 1 =
      Real.pi * Gamma d * Gamma (2 * c - d + 1) * (2 : ℂ) ^ (1 - 2 * c) /
      (Gamma (c + (a - d + 1) / 2) * Gamma (c + 1 - (a + d) / 2) *
        Gamma ((a + d) / 2) * Gamma ((d - a + 1) / 2)) := by
  sorry

/-- Whipple terminating 3F2 sum in finite products. -/
@[dlmf 16.4.E8]
theorem genHG_whipple_3F2_terminating (n : ℕ) (a d : ℂ) (hb : genDenRegular {d, 1 - d - 2 * n}) :
    genFiniteHG n {(-n : ℂ), a, 1 - a} {d, 1 - d - 2 * n} 1 =
      poch ((a + d) / 2) n * poch ((d - a + 1) / 2) n /
        (poch (d / 2) n * poch ((d + 1) / 2) n) := by
  sorry

/-- Dougall very well-poised 5F4 in its full absolute convergence half-space. -/
@[dlmf 16.4.E9]
theorem genHG_dougall_5F4_sum (a b c d : ℂ) (hb : genDenRegular {a / 2, a - b + 1, a - c + 1, a - d + 1})
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
    (hb : genDenRegular {a / 2, a - b + 1, a - c + 1, a + n + 1}) :
    Tendsto (fun q : ℝ => qbR4SixTerm ((q : ℂ) ^ a) ((q : ℂ) ^ b) ((q : ℂ) ^ c) q n k)
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
  rw [qbR4SixTerm, hB, hC, hZ, hN,
    show (q : ℂ) ^ (-(n : ℤ)) = (q : ℂ) ^ (-(n : ℂ)) by
      rw [Complex.cpow_neg, Complex.cpow_natCast, zpow_neg, zpow_natCast]]
  ring

/-- Dougall terminating 5F4, with all removable cases retained by finite products. -/
@[dlmf 16.4.E9]
theorem genHG_dougall_5F4_terminating (n : ℕ) (a b c : ℂ)
    (hb : genDenRegular {a / 2, a - b + 1, a - c + 1, a + n + 1}) :
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
      qbR4SixTerm ((q : ℂ) ^ a) ((q : ℂ) ^ b) ((q : ℂ) ^ c) q n k) =ᶠ[𝓝[<] 1]
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
    have hS := qbR4_six_rational hq0 hqn n
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
    (hb : genDenRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1}) :
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
    (hb : genDenRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1})
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
    (hb : genDenRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1}) :
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
    (hb : genDenRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1}) :
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
    have hbt : genDenRegular {a / 2, a - t + 1, a - c + 1, a - d + 1, a - F t + 1, a + n + 1} := by
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
    (hb : genDenRegular {d, e, d + e - b - c})
    (hconv : 0 < (d + e - a - b - c).re) (hea : 0 < (e - a).re) :
    genHG {a, b, c} {d, e} 1 = Gamma e * Gamma (d + e - a - b - c) /
      (Gamma (e - a) * Gamma (d + e - b - c)) *
      genHG {a, d - b, d - c} {d, d + e - b - c} 1 := by
  sorry

/-- The contiguous unity recurrence with convergence of every displayed series. -/
@[dlmf 16.4.E12]
theorem genHG_3F2_unit_recurrence (a b c d e : ℂ) (hb : genDenRegular {d - 1, d, d + 1, e})
    (hconv : 1 < (d + e - a - b - c).re ∨ genTerminates {a, b, c}) :
    (a - d) * (b - d) * (c - d) *
      (genHG {a, b, c} {d + 1, e} 1 - genHG {a, b, c} {d, e} 1) +
      a * b * c * genHG {a, b, c} {d, e} 1 =
    d * (d - 1) * (a + b + c - d - e + 1) *
      (genHG {a, b, c} {d, e} 1 - genHG {a, b, c} {d - 1, e} 1) := by
  sorry

/-- The second unity recurrence, with the full common convergence half-space. -/
@[dlmf 16.4.E13]
theorem genHG_3F2_unit_recurrence_two (a b c d e : ℂ) (hb : genDenRegular {d, d + 1, e, e + 1})
    (hconv : 0 < (d + e - a - b - c).re) :
    genHG {a, b, c} {d, e} 1 = c * (e - a) / (d * e) *
      genHG {a, b + 1, c + 1} {d + 1, e + 1} 1 +
      (d - c) / d * genHG {a, b + 1, c} {d + 1, e} 1 := by
  sorry

/-- The balanced terminating 4F3 transformation. -/
@[dlmf 16.4.E14]
theorem genHG_balanced_4F3_transformation (n : ℕ) (a b c d e f : ℂ) (hbal : a + b + c - n + 1 = d + e + f)
    (hb : genDenRegular {d, e, f, a - e - n + 1, a - f - n + 1}) :
    genFiniteHG n {(-n : ℂ), a, b, c} {d, e, f} 1 =
      poch (e - a) n * poch (f - a) n / (poch e n * poch f n) *
        genFiniteHG n {(-n : ℂ), a, d - b, d - c}
          {d, a - e - n + 1, a - f - n + 1} 1 := by
  sorry

/-- Whipple transformation when the right side terminates through the transformed first upper parameter and the left converges absolutely. -/
@[dlmf 16.4.E15]
theorem genHG_whipple_nonterminating_left (n : ℕ) (a b c d e f : ℂ) (hn : a - b - c + 1 = -n)
    (hb : genDenRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - e + 1, a - f + 1,
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
    (hcd : genDenRegular {c, d}) (hconv : 1 < (c + d - a - b).re) :
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
    (hb : genDenRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - e + 1,
      a - f + 1, d + e + f - a})
    (hnum : genDenRegular {a - d - e - f + 1})
    (hterm : genTerminates {a - b - c + 1, d, e, f})
    (hconv : 0 < (2 * a + 2 - b - c - d - e - f).re ∨
      genTerminates {a, b, c, d, e, f}) :
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
lemma gen3F2_unit_parameter_analytic :
    AnalyticOnNhd ℂ (fun P : Fin 5 → ℂ => genHG {P 0, P 1, P 2} {P 3, P 4} 1)
      {P | genDenRegular {P 3, P 4} ∧ 0 < (P 3 + P 4 - P 0 - P 1 - P 2).re} := by
  sorry

/-- The continued expression is jointly analytic at its regular parameter points in
the full printed e−a half-space, including points outside original series convergence. -/
@[dlmf 16.4.E11]
theorem gen3F2_thomae_parameter_analytic :
    AnalyticOnNhd ℂ (fun P : Fin 5 → ℂ => gen3F2UnitThomae (P 0) (P 1) (P 2) (P 3) (P 4))
      {P | genDenRegular {P 3, P 4, P 3 + P 4 - P 1 - P 2,
        P 3 + P 4 - P 0 - P 1 - P 2} ∧ 0 < (P 4 - P 0).re} := by
  sorry

end DLMF.Hypergeometric
