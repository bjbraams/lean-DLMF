/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.AnalyticProperties
public import DLMF.GeneralizedHypergeometric.GHATools
public import DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuationExistence
public import DLMF.GeneralizedHypergeometric.Basic
public import DLMF.Hypergeometric.Basic.GeneralizedCalculus
public import Mathlib.RingTheory.PowerSeries.Basic
public import DLMF.Hypergeometric.ArgumentContinuation
public import DLMF.Hypergeometric.Solutions
public import DLMF.Hypergeometric.Clausen

/-!
# Transformations, expansions and products of `ₚF_q` (DLMF §§16.6, 16.10, 16.12)

## Main definitions

* `genQuadraticDomain`, `genCubicDomain`: simultaneous principal domains of the variable
  transformations.
* `genFieldsWimpCoeff`, `genFieldsWimpTerm`, `genFieldsWimpDoubleTerm`: the terms of the
  Fields–Wimp expansion.

## Main results

* `genHG_quadratic_transformation`, `genHG_cubic_transformation`: DLMF 16.6.1–16.6.2.
* `genHG_fields_wimp_coeff`, `genHG_fields_wimp_hasSum`: the Fields–Wimp expansion,
  DLMF 16.10.1.
* `genHG_norlund_expansion`: Nørlund's expansion, DLMF 16.10.2.
* `genHG_0F1_product`: the product of two `₀F₁` functions, DLMF 16.12.1.
* `genHG_clausen_principal`: Clausen's formula on the principal slit plane, DLMF 16.12.2.
* `genHG_general_square_hasSum`: the general square series, DLMF 16.12.3.

## Implementation notes

Variable transformations use the component containing zero of the simultaneous principal
domains. This retains analytic continuation without equating unrelated branches on disconnected
preimages of cuts. The Fields–Wimp expansion has an unrestricted formal coefficient identity
and an analytic statement under absolute convergence of the expanded double series; DLMF does
not print a sharper convergence region. All terminating auxiliary functions are finite sums.
-/

@[expose] public section
open Complex Filter Set Finset
open scoped Topology Real Nat
noncomputable section
namespace DLMF.Hypergeometric

/-- Simultaneous principal domain for the quadratic variable transformation. -/
def genQuadraticDomain : Set ℂ := connectedComponentIn
  {z : ℂ | z ∈ cutPlane ∧ 1 - z ∈ Complex.slitPlane ∧ -4 * z / (1 - z) ^ 2 ∈ cutPlane} 0

/-- Simultaneous principal domain for the cubic variable transformation. -/
def genCubicDomain : Set ℂ := connectedComponentIn
  {z : ℂ | z / 4 ∈ cutPlane ∧ 1 - z ∈ Complex.slitPlane ∧
    -27 * z / (4 * (1 - z) ^ 3) ∈ cutPlane} 0

/-- Fields–Wimp prefactor with the power of z removed. -/
def genFieldsWimpCoeff (a b : Multiset ℂ) (α β γ : ℂ) (k : ℕ) : ℂ :=
  genPoch a k * poch α k * poch β k * (-1 : ℂ) ^ k /
    (genPoch b k * poch (γ + k) k * k.factorial)

/-- The kth Fields–Wimp summand, including its terminating auxiliary polynomial. -/
def genFieldsWimpTerm (a b c d : Multiset ℂ) (α β γ z ζ : ℂ) (k : ℕ) : ℂ :=
  genFieldsWimpCoeff a b α β γ k * z ^ k *
    genHG ((α + k) ::ₘ (β + k) ::ₘ genShift a k)
      ((γ + 2 * k + 1) ::ₘ genShift b k) z *
    genFiniteHG k ((-k : ℂ) ::ₘ (γ + k) ::ₘ c) (α ::ₘ β ::ₘ d) ζ

/-- The expanded two-index Fields–Wimp term used for its convergence condition. -/
def genFieldsWimpDoubleTerm (a b c d : Multiset ℂ) (α β γ z ζ : ℂ) (kn : ℕ × ℕ) : ℂ :=
  genFieldsWimpCoeff a b α β γ kn.1 * z ^ kn.1 *
    genCoeff ((α + kn.1) ::ₘ (β + kn.1) ::ₘ genShift a kn.1)
      ((γ + 2 * kn.1 + 1) ::ₘ genShift b kn.1) kn.2 * z ^ kn.2 *
    genFiniteHG kn.1 ((-kn.1 : ℂ) ::ₘ (γ + kn.1) ::ₘ c) (α ::ₘ β ::ₘ d) ζ

/-- Quadratic transformation on the full common principal component. -/
@[dlmf 16.6.E1]
theorem genHG_quadratic_transformation (a b c : ℂ) (hb : GenDenRegular {a - b + 1, a - c + 1})
    {z : ℂ} (hz : z ∈ genQuadraticDomain) :
    genHG {a, b, c} {a - b + 1, a - c + 1} z = (1 - z) ^ (-a) *
      genHG {a - b - c + 1, a / 2, (a + 1) / 2}
        {a - b + 1, a - c + 1} (-4 * z / (1 - z) ^ 2) := by
  sorry

/-- Cubic transformation on the full common principal component. -/
@[dlmf 16.6.E2]
theorem genHG_cubic_transformation (a b : ℂ) (hb : GenDenRegular {b, a - b + 3 / 2})
    {z : ℂ} (hz : z ∈ genCubicDomain) :
    genHG {a, 2 * b - a - 1, 2 - 2 * b + a} {b, a - b + 3 / 2} (z / 4) =
      (1 - z) ^ (-a) * genHG {a / 3, a / 3 + 1 / 3, a / 3 + 2 / 3}
        {b, a - b + 3 / 2} (-27 * z / (4 * (1 - z) ^ 3)) := by
  sorry

/-- The formal coefficient identity has no analytic convergence restriction. -/
@[dlmf 16.10.E1]
theorem genHG_fields_wimp_coeff (a b c d : Multiset ℂ) (α β γ ζ : ℂ)
    (hb : GenDenRegular (b + d)) (hαβ : GenDenRegular {α, β})
    (hγ : ∀ k : ℕ, poch (γ + k) k ≠ 0 ∧ GenDenRegular {γ + 2 * k + 1}) (N : ℕ) :
    genCoeff (a + c) (b + d) N * ζ ^ N =
      ∑ k ∈ range (N + 1), genFieldsWimpCoeff a b α β γ k *
        genCoeff ((α + k) ::ₘ (β + k) ::ₘ genShift a k)
          ((γ + 2 * k + 1) ::ₘ genShift b k) (N - k) *
        genFiniteHG k ((-k : ℂ) ::ₘ (γ + k) ::ₘ c) (α ::ₘ β ::ₘ d) ζ := by
  sorry

/-- The analytic expansion under explicit absolute double-series convergence and valid original
germs. -/
@[dlmf 16.10.E1]
theorem genHG_fields_wimp_hasSum (a b c d : Multiset ℂ) (α β γ z ζ : ℂ)
    (hb : GenDenRegular (b + d)) (hαβ : GenDenRegular {α, β})
    (hγ : ∀ k : ℕ, poch (γ + k) k ≠ 0 ∧ GenDenRegular {γ + 2 * k + 1})
    (hleft : HasSum (fun n => genCoeff (a + c) (b + d) n * (z * ζ) ^ n)
      (genHG (a + c) (b + d) (z * ζ)))
    (hinner : ∀ k : ℕ, HasSum (fun n =>
        genCoeff ((α + k) ::ₘ (β + k) ::ₘ genShift a k)
          ((γ + 2 * k + 1) ::ₘ genShift b k) n * z ^ n)
      (genHG ((α + k) ::ₘ (β + k) ::ₘ genShift a k)
        ((γ + 2 * k + 1) ::ₘ genShift b k) z))
    (habs : Summable (fun kn : ℕ × ℕ => ‖genFieldsWimpDoubleTerm a b c d α β γ z ζ kn‖)) :
    HasSum (genFieldsWimpTerm a b c d α β γ z ζ) (genHG (a + c) (b + d) (z * ζ)) := by
  sorry

/-- Norlund expansion with the full printed convergence half-plane and zeta disk. -/
@[dlmf 16.10.E2]
theorem genHG_norlund_expansion (a : ℂ) (A B : Multiset ℂ) (hcard : A.card = B.card)
    (hb : GenDenRegular B)
    {z ζ : ℂ} (hζ : ‖ζ - 1‖ < 1) (hz : z.re < 1 / 2) :
    HasSum (fun k : ℕ => (1 - z) ^ (-a) * poch a k / k.factorial *
      genFiniteHG k ((-k : ℂ) ::ₘ A) B ζ * (z / (z - 1)) ^ k)
      (genHG (a ::ₘ A) B (z * ζ)) := by
  sorry

/-- Duplication for Pochhammer symbols: `(x)₂ₙ = 4ⁿ (x/2)ₙ ((x+1)/2)ₙ`. -/
private lemma poch_two_mul_eq_four_pow_mul (x : ℂ) (n : ℕ) :
    poch x (2 * n) = 4 ^ n * poch (x / 2) n * poch ((x + 1) / 2) n := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, poch_succ, poch_succ, ih, poch_succ, poch_succ]
    push_cast
    ring

/-- A Chu–Vandermonde rearrangement: `∑ C(n,k) (a+k)ₙ₋ₖ (b+n-k)ₖ = (a+b+n-1)ₙ`. -/
private lemma sum_choose_mul_poch_mul_poch (a b : ℂ) (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℂ) * poch (a + k) (n - k) * poch (b + (n - k : ℕ)) k =
      poch (a + b + n - 1) n := by
  have h := chu_vandermonde_sum n (1 - b - n) a
  rw [show a - (1 - b - n) = a + b + n - 1 by ring] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hr := poch_reflect (b + (n - k : ℕ)) k
  rw [show 1 - (b + ((n - k : ℕ) : ℂ)) - k = 1 - b - n by push_cast [Nat.cast_sub hk']; ring] at hr
  rw [hr]
  have : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  linear_combination (n.choose k : ℂ) * poch (a + k) (n - k) * poch (b + (n - k : ℕ)) k * this.symm

/-- Cauchy-product coefficients of two `0F1` series (DLMF 16.12.1). -/
private lemma sum_inv_poch_mul_factorial_mul_inv_poch_mul_factorial (a b : ℂ) (ha : ∀ k : ℕ, a ≠ -k)
    (hb : ∀ k : ℕ, b ≠ -k)
    (hab : ∀ k : ℕ, a + b - 1 ≠ -k) (n : ℕ) :
    ∑ k ∈ range (n + 1), 1 / (poch a k * k !) * (1 / (poch b (n - k) * (n - k)!)) =
      4 ^ n * poch ((a + b) / 2) n * poch ((a + b - 1) / 2) n /
        (poch a n * poch b n * poch (a + b - 1) n * n !) := by
  have hpa := poch_ne_zero_of_not_neg_nat ha
  have hpb := poch_ne_zero_of_not_neg_nat hb
  have hpab := poch_ne_zero_of_not_neg_nat hab
  have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hterm : ∀ k ∈ range (n + 1), 1 / (poch a k * k !) * (1 / (poch b (n - k) * (n - k)!)) =
      (n.choose k : ℂ) * poch (a + k) (n - k) * poch (b + (n - k : ℕ)) k /
        (poch a n * poch b n * n !) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 := poch_add a k (n - k)
    have h2 := poch_add b (n - k) k
    rw [Nat.add_sub_of_le hk'] at h1
    rw [Nat.sub_add_cancel hk'] at h2
    have h3 : (n ! : ℂ) = n.choose k * k ! * (n - k)! := by
      exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hk').symm
    have hk0 : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hnk0 : ((n - k)! : ℂ) ≠ 0 := by exact_mod_cast (n - k).factorial_ne_zero
    have hA : poch (a + k) (n - k) ≠ 0 := fun h => hpa n (by rw [h1, h, mul_zero])
    have hB : poch (b + (n - k : ℕ)) k ≠ 0 := fun h => hpb n (by rw [h2, h, mul_zero])
    have hC : (n.choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk').ne'
    rw [h1, h2, h3]
    have := hpa k
    have := hpb (n - k)
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, sum_choose_mul_poch_mul_poch]
  have hdup := poch_two_mul_eq_four_pow_mul (a + b - 1) n
  rw [show (a + b - 1 + 1) / 2 = (a + b) / 2 by ring] at hdup
  have hsplit := poch_add (a + b - 1) n n
  rw [← two_mul] at hsplit
  rw [div_eq_div_iff (by simp [hpa n, hpb n, hn]) (by simp [hpa n, hpb n, hn, hpab n])]
  rw [show a + b + n - 1 = a + b - 1 + n by ring]
  linear_combination (poch a n * poch b n * n !) * (hsplit.symm.trans hdup)

/-- The `0F1` coefficient. -/
private lemma genCoeff_empty_singleton (a : ℂ) (n : ℕ) : genCoeff ∅ {a} n = 1 /
    (poch a n * n !) := by
  simp [genCoeff, genPoch]

/-- Absolute summability of the `0F1` series. -/
private lemma summable_norm_genCoeff_empty_singleton_mul_pow (a z : ℂ) (ha : ∀ k : ℕ, a ≠ -k) :
    Summable fun n : ℕ => ‖genCoeff ∅ {a} n * z ^ n‖ := by
  obtain ⟨C, hC0, hC⟩ := factorial_le_mul_norm_poch a ha (σ := 2) (by norm_num)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((Real.summable_pow_div_factorial (2 * ‖z‖)).mul_left C)
  have hp : 0 < ‖poch a n‖ := norm_pos_iff.mpr (poch_ne_zero_of_not_neg_nat ha n)
  have hf : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have hf1 : (1 : ℝ) ≤ n ! := by exact_mod_cast n.factorial_pos
  rw [genCoeff_empty_singleton, norm_mul, norm_div, norm_one, norm_mul, norm_pow,
      Complex.norm_natCast,
    mul_pow, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  have h := hC n
  calc ‖z‖ ^ n = ‖z‖ ^ n * 1 := by ring
    _ ≤ ‖z‖ ^ n * (C * 2 ^ n * ‖poch a n‖ / n !) := by
        gcongr; rw [le_div_iff₀ hf]; linarith
    _ ≤ ‖z‖ ^ n * (C * 2 ^ n * ‖poch a n‖ / n !) * n ! := by
        have : 0 ≤ ‖z‖ ^ n * (C * 2 ^ n * ‖poch a n‖ / n !) := by positivity
        nlinarith
    _ = C * (2 ^ n * ‖z‖ ^ n / n !) * (‖poch a n‖ * n !) := by field_simp

/-- The product of two 0F1 functions for every complex z. -/
@[dlmf 16.12.E1]
theorem genHG_0F1_product (a b z : ℂ) (hb : GenDenRegular {a, b, a + b - 1}) :
    genHG ∅ {a} z * genHG ∅ {b} z =
      genHG {(a + b) / 2, (a + b - 1) / 2} {a, b, a + b - 1} (4 * z) := by
  have ha' : ∀ k : ℕ, a ≠ -k := hb a (by simp)
  have hb' : ∀ k : ℕ, b ≠ -k := hb b (by simp)
  have hab' : ∀ k : ℕ, a + b - 1 ≠ -k := hb (a + b - 1) (by simp)
  have hA := genHG_hasSum_entire (a := ∅) (b := {a}) (by simp)
    (fun x hx => by rw [Multiset.mem_singleton] at hx; subst hx; exact ha') z
  have hB := genHG_hasSum_entire (a := ∅) (b := {b}) (by simp)
    (fun x hx => by rw [Multiset.mem_singleton] at hx; subst hx; exact hb') z
  have hC := genHG_hasSum_entire (a := {(a + b) / 2, (a + b - 1) / 2}) (b := {a, b, a + b - 1})
    (by simp) hb (4 * z)
  rw [← hA.tsum_eq, ← hB.tsum_eq, ← hC.tsum_eq,
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
        (summable_norm_genCoeff_empty_singleton_mul_pow a z ha')
      (summable_norm_genCoeff_empty_singleton_mul_pow b z hb')]
  congr 1
  funext n
  have hcoef := sum_inv_poch_mul_factorial_mul_inv_poch_mul_factorial a b ha' hb' hab' n
  have hsum : ∑ k ∈ range (n + 1), genCoeff ∅ {a} k * z ^ k *
      (genCoeff ∅ {b} (n - k) * z ^ (n - k)) =
      (∑ k ∈ range (n + 1), 1 / (poch a k * k !) * (1 / (poch b (n - k) * (n - k)!))) * z ^ n := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [genCoeff_empty_singleton, genCoeff_empty_singleton, ← Nat.add_sub_of_le hk', pow_add,
      Nat.add_sub_cancel_left]
    ring
  rw [hsum, hcoef]
  simp only [genCoeff, genPoch, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, mul_pow]
  ring

/-- The existing Clausen germ identity continued to its whole principal slit. -/
@[dlmf 16.12.E2]
theorem genHG_clausen_principal (a b : ℂ) (hb : GenDenRegular {a + b + 1 / 2, 2 * a + 2 * b})
    {z : ℂ} (hz : z ∈ cutPlane) :
    genHG {a, b} {a + b + 1 / 2} z ^ 2 =
      genHG {2 * a, 2 * b, a + b} {a + b + 1 / 2, 2 * a + 2 * b} z := by
  have hc : ∀ k : ℕ, a + b + 1 / 2 ≠ -k := fun k => hb _ (by simp) k
  have hd : ∀ k : ℕ, 2 * a + 2 * b ≠ -k := fun k => hb _ (by simp) k
  have hc' : GenDenRegular {a + b + 1 / 2} := fun x hx k => by
    rw [Multiset.mem_singleton] at hx; subst hx; exact hc k
  refine eqOn_cutPlane_of_eqOn_disk (f := fun z => genHG {a, b} {a + b + 1 / 2} z ^ 2)
    (g := genHG {2 * a, 2 * b, a + b} {a + b + 1 / 2, 2 * a + 2 * b})
    ((genHG_principal_analytic (by simp)).pow 2) (genHG_principal_analytic (by simp))
    (fun w hw => ?_) hz
  have h1 := genHG_hasSum_disk (a := {a, b}) (b := {a + b + 1 / 2}) (by simp) hc' hw
  have h2 := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b (a + b + 1 / 2)).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one hw)
  have h3 := genHG_hasSum_disk (a := {2 * a, 2 * b, a + b})
    (b := {a + b + 1 / 2, 2 * a + 2 * b}) (by simp) hb hw
  have h4 := clausen_formula hc hd hw
  have e12 : genHG {a, b} {a + b + 1 / 2} w = ₂F₁ a b (a + b + 1 / 2) w := by
    refine h1.unique (h2.congr_fun fun n => ?_)
    simp [genCoeff, genPoch, gaussHGCoeff]
  have e34 : genHG {2 * a, 2 * b, a + b} {a + b + 1 / 2, 2 * a + 2 * b} w =
      ₂F₁ a b (a + b + 1 / 2) w ^ 2 := by
    refine h3.unique (h4.congr_fun fun n => ?_)
    simp only [genCoeff, genPoch, clausenCoeff, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
    ring
  simp only [e12, e34]

/-- The full generalized square series; terminating inner sums preserve lower exceptions after
termination. -/
@[dlmf 16.12.E3]
theorem genHG_general_square_hasSum (a b c : ℂ)
    (hb : GenDenRegular {c, 2 * c - 1, a + 1 / 2, b + 1 / 2})
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => poch (2 * a) k * poch (2 * b) k * poch (c - 1 / 2) k /
      (poch c k * poch (2 * c - 1) k * k.factorial) *
      genFiniteHG k {-(k : ℂ) / 2, (1 - (k : ℂ)) / 2, a + b - c + 1 / 2, 1 / 2}
        {a + 1 / 2, b + 1 / 2, 3 / 2 - (k : ℂ) - c} 1 * z ^ k) (genHG {a, b} {c} z ^ 2) := by
  sorry

end DLMF.Hypergeometric
