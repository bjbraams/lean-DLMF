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

* `generalizedHypergeometric_quadratic_transformation`,
  `generalizedHypergeometric_cubic_transformation`: DLMF 16.6.1–16.6.2.
* `generalizedHypergeometric_fields_wimp_coeff`, `generalizedHypergeometric_fields_wimp_hasSum`: the
  Fields–Wimp expansion, DLMF 16.10.1, with the stronger forms
  `generalizedHypergeometric_fields_wimp_coeff'` and
  `generalizedHypergeometric_fields_wimp_hasSum'`.
* `generalizedHypergeometric_norlund_expansion`: Nørlund's expansion, DLMF 16.10.2.
* `generalizedHypergeometric_0F1_product`: the product of two `₀F₁` functions, DLMF 16.12.1.
* `generalizedHypergeometric_clausen_principal`: Clausen's formula on the principal slit plane, DLMF
  16.12.2.
* `generalizedHypergeometric_general_square_hasSum`: the general square series, DLMF 16.12.3.

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
  pochhammerProduct a k * pochhammer α k * pochhammer β k * (-1 : ℂ) ^ k /
    (pochhammerProduct b k * pochhammer (γ + k) k * k.factorial)

/-- The kth Fields–Wimp summand, including its terminating auxiliary polynomial. -/
def genFieldsWimpTerm (a b c d : Multiset ℂ) (α β γ z ζ : ℂ) (k : ℕ) : ℂ :=
  genFieldsWimpCoeff a b α β γ k * z ^ k *
    generalizedHypergeometric ((α + k) ::ₘ (β + k) ::ₘ shiftParameters a k)
      ((γ + 2 * k + 1) ::ₘ shiftParameters b k) z *
    generalizedHypergeometricTruncated k ((-k : ℂ) ::ₘ (γ + k) ::ₘ c) (α ::ₘ β ::ₘ d) ζ

/-- The expanded two-index Fields–Wimp term used for its convergence condition. -/
def genFieldsWimpDoubleTerm (a b c d : Multiset ℂ) (α β γ z ζ : ℂ) (kn : ℕ × ℕ) : ℂ :=
  genFieldsWimpCoeff a b α β γ kn.1 * z ^ kn.1 *
    generalizedHypergeometricCoeff ((α + kn.1) ::ₘ (β + kn.1) ::ₘ shiftParameters a kn.1)
      ((γ + 2 * kn.1 + 1) ::ₘ shiftParameters b kn.1) kn.2 * z ^ kn.2 *
    generalizedHypergeometricTruncated kn.1 ((-kn.1 : ℂ) ::ₘ (γ + kn.1) ::ₘ c) (α ::ₘ β ::ₘ d) ζ

/-- Quadratic transformation on the full common principal component. -/
@[dlmf 16.6.E1]
theorem generalizedHypergeometric_quadratic_transformation (a b c : ℂ)
    (hb : LowerParametersRegular {a - b + 1, a - c + 1})
    {z : ℂ} (hz : z ∈ genQuadraticDomain) :
    generalizedHypergeometric {a, b, c} {a - b + 1, a - c + 1} z = (1 - z) ^ (-a) *
      generalizedHypergeometric {a - b - c + 1, a / 2, (a + 1) / 2}
        {a - b + 1, a - c + 1} (-4 * z / (1 - z) ^ 2) := by
  sorry

/-- Cubic transformation on the full common principal component. -/
@[dlmf 16.6.E2]
theorem generalizedHypergeometric_cubic_transformation (a b : ℂ)
    (hb : LowerParametersRegular {b, a - b + 3 / 2})
    {z : ℂ} (hz : z ∈ genCubicDomain) :
    generalizedHypergeometric {a, 2 * b - a - 1, 2 - 2 * b + a} {b, a - b + 3 / 2} (z / 4) =
      (1 - z) ^ (-a) * generalizedHypergeometric {a / 3, a / 3 + 1 / 3, a / 3 + 2 / 3}
        {b, a - b + 3 / 2} (-27 * z / (4 * (1 - z) ^ 3)) := by
  sorry

/-- `(g + r + 1)ₙ ≠ 0` when `g` avoids the negative integers. -/
private lemma pochhammer_ne_zero_of_add_succ {g : ℂ} (hg : ∀ i : ℕ, g + (i + 1) ≠ 0)
    (r : ℕ) (n : ℕ) :
    pochhammer (g + (r + 1)) n ≠ 0 := by
  refine pochhammer_ne_zero_of_not_neg_nat (fun k hk => hg (r + k) ?_) n
  push_cast; linear_combination hk

private lemma fieldsWimp_inner_sum_eq_zero {g : ℂ} (hg : ∀ i : ℕ, g + (i + 1) ≠ 0) (M : ℕ) :
    ∑ m ∈ range (M + 2), (-1 : ℂ) ^ m * ((M + 1).choose m : ℂ) /
      (pochhammer (g + m) m * pochhammer (g + 2 * m + 1) (M + 1 - m)) = 0 := by
  let T : ℕ → ℂ := fun m => match m with
    | 0 => 0
    | m + 1 => (-1 : ℂ) ^ m * (M.choose m : ℂ) / pochhammer (g + m + 1) (M + 1)
  have hterm : ∀ m ∈ range (M + 2), (-1 : ℂ) ^ m * ((M + 1).choose m : ℂ) /
      (pochhammer (g + m) m * pochhammer (g + 2 * m + 1) (M + 1 - m)) = T (m + 1) - T m := by
    intro m hm
    rcases m with _ | m
    · simp [T, pochhammer_zero]
    · have hmM : m ≤ M := by simp at hm; omega
      set x : ℂ := g + m + 1 with hx
      have hx0 : x ≠ 0 := by rw [hx]; simpa [add_assoc] using hg m
      have hxM : x + 1 + M ≠ 0 := by
        have := hg (m + 1 + M); push_cast at this; rw [hx]
        exact fun h => this (by linear_combination h)
      have hxm : x + (m + 1) ≠ 0 := by
        have := hg (m + 1 + m); push_cast at this; rw [hx]
        exact fun h => this (by linear_combination h)
      have hP : pochhammer (x + 1) M ≠ 0 := by
        have := pochhammer_ne_zero_of_add_succ hg (m + 1) M
        rw [hx]; push_cast at this; convert this using 2; ring
      have hQ : pochhammer x (m + 1) * (x + (m + 1)) * pochhammer (x + (m + 1) + 1) (M - m) =
          x * pochhammer (x + 1) M * (x + 1 + M) := by
        have h1 : pochhammer x (m + 1 + 1 + (M - m)) = pochhammer x (m + 1) * (x + (m + 1)) *
            pochhammer (x + (m + 1) + 1) (M - m) := by
          rw [pochhammer_add, pochhammer_succ]; push_cast; ring_nf
        have h2 : pochhammer x (M + 1 + 1) = x * pochhammer (x + 1) M * (x + 1 + M) := by
          rw [pochhammer_succ_left, pochhammer_succ]; ring
        rw [← h1, show m + 1 + 1 + (M - m) = M + 1 + 1 by omega, h2]
      have hQ0 : pochhammer x (m + 1) * pochhammer (x + (m + 1) + 1) (M - m) ≠ 0 := by
        intro h0
        have : x * pochhammer (x + 1) M * (x + 1 + M) = 0 := by
          rw [← hQ]; linear_combination (x + (m + 1)) * h0
        simp [hx0, hP, hxM] at this
      have hT1 : pochhammer (g + ((m + 1 : ℕ) : ℂ) + 1) (M + 1) = pochhammer (x + 1) M *
          (x + 1 + M) := by
        rw [pochhammer_succ, hx]; push_cast; ring_nf
      have hT0 : pochhammer (g + (m : ℂ) + 1) (M + 1) = x * pochhammer (x + 1) M := by
        rw [pochhammer_succ_left]
      have hc : ((M.choose (m + 1) : ℕ) : ℂ) * (m + 1) = (M.choose m : ℂ) * ((M - m : ℕ) : ℂ) := by
        exact_mod_cast Nat.choose_succ_right_eq M m
      have hc2 : ((M + 1).choose (m + 1) : ℂ) = M.choose m + M.choose (m + 1) := by
        exact_mod_cast Nat.choose_succ_succ' M m
      simp only [T]
      rw [hT1, hT0]
      rw [show g + ((m + 1 : ℕ) : ℂ) = x by rw [hx]; push_cast; ring,
        show g + 2 * ((m + 1 : ℕ) : ℂ) + 1 = x + (m + 1) + 1 by rw [hx]; push_cast; ring,
        show M + 1 - (m + 1) = M - m by omega]
      push_cast [hmM] at hc ⊢
      rw [hc2]
      field_simp
      rw [div_eq_iff hQ0]
      linear_combination (-(-1 : ℂ) ^ (m + 1) * ((M.choose m : ℂ) + M.choose (m + 1))) * hQ +
        (-1 : ℂ) ^ (m + 1) * pochhammer x (m + 1) * pochhammer (x + (m + 1) + 1) (M - m) * hc
  rw [sum_congr rfl hterm, sum_range_sub]
  simp [T]

/-- Splitting `pochhammerProduct` at `k`. -/
private lemma pochhammerProduct_add_shift (a : Multiset ℂ) (k n : ℕ) :
    pochhammerProduct a (k + n) = pochhammerProduct a k *
        pochhammerProduct (shiftParameters a k) n := by
  simp only [pochhammerProduct, shiftParameters, Multiset.map_map, Function.comp_def,
      pochhammer_add,
    ← Multiset.prod_map_mul]

/-- `pochhammerProduct` of a cons. -/
private lemma pochhammerProduct_cons (x : ℂ) (s : Multiset ℂ) (n : ℕ) :
    pochhammerProduct (x ::ₘ s) n = pochhammer x n * pochhammerProduct s n := by
  simp [pochhammerProduct]

/-- `pochhammerProduct` of a sum of multisets. -/
private lemma pochhammerProduct_add' (s t : Multiset ℂ) (n : ℕ) :
    pochhammerProduct (s + t) n = pochhammerProduct s n * pochhammerProduct t n := by
  simp [pochhammerProduct]

/-- The kernel of the Fields–Wimp inversion. -/
private lemma fieldsWimp_kernel {γ : ℂ} (hγ : ∀ i : ℕ, γ + (i + 1) ≠ 0) {N j : ℕ}
    (hj : j ≤ N) :
    ∑ k ∈ range (N + 1), (-1 : ℂ) ^ k * pochhammer (-(k : ℂ)) j * pochhammer (γ + k) j /
      (pochhammer (γ + k) k * pochhammer (γ + 2 * k + 1) (N - k) * k.factorial *
          (N - k).factorial) =
      if j = N then 1 else 0 := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show j + M + 1 = j + (M + 1) by ring, sum_range_add]
  have h0 : ∑ k ∈ range j, (-1 : ℂ) ^ k * pochhammer (-(k : ℂ)) j * pochhammer (γ + k) j /
      (pochhammer (γ + k) k * pochhammer (γ + 2 * k + 1) (j + M - k) * k.factorial *
        (j + M - k).factorial) = 0 := by
    refine sum_eq_zero fun k hk => ?_
    rw [pochhammer_neg_nat_eq_zero (Finset.mem_range.mp hk)]
    simp
  rw [h0, zero_add]
  set g : ℂ := γ + 2 * j with hgdef
  have hg : ∀ i : ℕ, g + (i + 1) ≠ 0 := fun i h => hγ (2 * j + i) (by
    rw [hgdef] at h; push_cast; linear_combination h)
  have hterm : ∀ m ∈ range (M + 1), (-1 : ℂ) ^ (j + m) * pochhammer (-((j + m : ℕ) : ℂ)) j *
      pochhammer (γ + (j + m : ℕ)) j / (pochhammer (γ + (j + m : ℕ)) (j + m) *
        pochhammer (γ + 2 * (j + m : ℕ) + 1) (j + M - (j + m)) * (j + m).factorial *
        (j + M - (j + m)).factorial) =
      (M.factorial : ℂ)⁻¹ * ((-1 : ℂ) ^ m * (M.choose m : ℂ) /
        (pochhammer (g + m) m * pochhammer (g + 2 * m + 1) (M - m))) := by
    intro m hm
    have hmM : m ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [show j + M - (j + m) = M - m by omega, pochhammer_add, pochhammer_neg_coe_nat]
    have hP : pochhammer (γ + (j + m : ℕ)) j ≠ 0 := by
      rcases j with _ | j
      · simp [pochhammer_zero]
      · refine pochhammer_ne_zero_of_not_neg_nat (fun n hn => hγ (j + m + n) ?_) _
        push_cast at hn ⊢; linear_combination hn
    have hd : ((j + m).descFactorial j : ℂ) * m.factorial = (j + m).factorial := by
      have := Nat.factorial_mul_descFactorial (show j ≤ j + m by omega)
      rw [show j + m - j = m by omega] at this
      exact_mod_cast (by rw [mul_comm]; exact this)
    have hc : (M.choose m : ℂ) * m.factorial * (M - m).factorial = M.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hmM
    have e1 : γ + ((j + m : ℕ) : ℂ) + j = g + m := by rw [hgdef]; push_cast; ring
    have e2 : γ + 2 * ((j + m : ℕ) : ℂ) + 1 = g + 2 * m + 1 := by rw [hgdef]; push_cast; ring
    rw [e1, e2]
    have hf1 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hf2 : ((M - m).factorial : ℂ) ≠ 0 := by exact_mod_cast (M - m).factorial_ne_zero
    have hf3 : (M.factorial : ℂ) ≠ 0 := by exact_mod_cast M.factorial_ne_zero
    have hf4 : ((j + m).factorial : ℂ) ≠ 0 := by exact_mod_cast (j + m).factorial_ne_zero
    rw [← hc, ← hd]
    field_simp
    have hC : (M.choose m : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmM).ne'
    have hj2 : (-1 : ℂ) ^ j * (-1) ^ j = 1 := by rw [← mul_pow]; simp
    rw [pow_add, mul_comm (M.choose m : ℂ), mul_div_mul_right _ _ hC]
    congr 1
    linear_combination (-1 : ℂ) ^ m * hj2
  rw [sum_congr rfl hterm, ← mul_sum]
  rcases M with _ | M
  · simp [pochhammer_zero]
  · have hne : j ≠ j + (M + 1) := by omega
    simp only [hne, ↓reduceIte, fieldsWimp_inner_sum_eq_zero hg M, mul_zero]

/-- The formal coefficient identity has no analytic convergence restriction. Stronger than DLMF,
which assumes regular lower parameters `b + d` and `γ + 2k + 1` and `(γ + k)ₖ ≠ 0` for all `k`;
only `α, β` and `γ + 1` need to avoid the nonpositive integers. -/
@[dlmf 16.10.E1]
theorem generalizedHypergeometric_fields_wimp_coeff' (a b c d : Multiset ℂ) (α β γ ζ : ℂ)
    (hαβ : LowerParametersRegular {α, β}) (hγ : LowerParametersRegular {γ + 1}) (N : ℕ) :
    generalizedHypergeometricCoeff (a + c) (b + d) N * ζ ^ N =
      ∑ k ∈ range (N + 1), genFieldsWimpCoeff a b α β γ k *
        generalizedHypergeometricCoeff ((α + k) ::ₘ (β + k) ::ₘ shiftParameters a k)
          ((γ + 2 * k + 1) ::ₘ shiftParameters b k) (N - k) *
        generalizedHypergeometricTruncated k ((-k : ℂ) ::ₘ (γ + k) ::ₘ c) (α ::ₘ β ::ₘ d) ζ := by
  have hγ' : ∀ i : ℕ, γ + (i + 1) ≠ 0 := fun i h =>
    hγ (γ + 1) (by simp) i (by linear_combination h)
  have hα : pochhammer α N ≠ 0 := pochhammer_ne_zero_of_not_neg_nat (hαβ α (by simp)) N
  have hβ : pochhammer β N ≠ 0 := pochhammer_ne_zero_of_not_neg_nat (hαβ β (by simp)) N
  let A : ℕ → ℂ := fun j => pochhammerProduct a N * pochhammer α N * pochhammer β N /
      pochhammerProduct b N *
    (pochhammerProduct c j /
        (pochhammer α j * pochhammer β j * pochhammerProduct d j * j.factorial)) * ζ ^ j
  let B : ℕ → ℕ → ℂ := fun k j => (-1 : ℂ) ^ k * pochhammer (-(k : ℂ)) j * pochhammer (γ + k) j /
      (pochhammer (γ + k) k * pochhammer (γ + 2 * k + 1) (N - k) * k.factorial * (N - k).factorial)
  have hterm : ∀ k ∈ range (N + 1), genFieldsWimpCoeff a b α β γ k *
        generalizedHypergeometricCoeff ((α + k) ::ₘ (β + k) ::ₘ shiftParameters a k)
          ((γ + 2 * k + 1) ::ₘ shiftParameters b k) (N - k) *
        generalizedHypergeometricTruncated k ((-k : ℂ) ::ₘ (γ + k) ::ₘ c) (α ::ₘ β ::ₘ d) ζ =
      ∑ j ∈ range (N + 1), A j * B k j := by
    intro k hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    unfold generalizedHypergeometricTruncated
    rw [← sum_subset (range_subset_range.mpr (by omega : k + 1 ≤ N + 1)) ?_, mul_sum]
    · refine sum_congr rfl fun j _ => ?_
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hkN
      rw [show k + n - k = n by omega]
      simp only [A, B, genFieldsWimpCoeff, generalizedHypergeometricCoeff, pochhammerProduct_cons,
          pochhammerProduct_add_shift,
        pochhammer_add, show k + n - k = n by omega]
      ring
    · intro j hj hj'
      have hkj : k < j := by simp at hj hj'; omega
      simp [B, pochhammer_neg_nat_eq_zero hkj]
  rw [sum_congr rfl hterm, sum_comm]
  have hW : ∀ j ∈ range (N + 1), ∑ k ∈ range (N + 1), A j * B k j =
      A j * if j = N then 1 else 0 := fun j hj => by
    rw [← mul_sum]; congr 1
    exact fieldsWimp_kernel hγ' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  rw [sum_congr rfl hW]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', Finset.mem_range, Nat.lt_succ_self,
    ↓reduceIte]
  simp only [A, generalizedHypergeometricCoeff, pochhammerProduct_add']
  field_simp

/-- The formal coefficient identity has no analytic convergence restriction. -/
@[dlmf 16.10.E1]
theorem generalizedHypergeometric_fields_wimp_coeff (a b c d : Multiset ℂ) (α β γ ζ : ℂ)
    (_hb : LowerParametersRegular (b + d)) (hαβ : LowerParametersRegular {α, β})
    (hγ : ∀ k : ℕ, pochhammer (γ + k) k ≠ 0 ∧ LowerParametersRegular {γ + 2 * k + 1}) (N : ℕ) :
    generalizedHypergeometricCoeff (a + c) (b + d) N * ζ ^ N =
      ∑ k ∈ range (N + 1), genFieldsWimpCoeff a b α β γ k *
        generalizedHypergeometricCoeff ((α + k) ::ₘ (β + k) ::ₘ shiftParameters a k)
          ((γ + 2 * k + 1) ::ₘ shiftParameters b k) (N - k) *
        generalizedHypergeometricTruncated k ((-k : ℂ) ::ₘ (γ + k) ::ₘ c) (α ::ₘ β ::ₘ d) ζ :=
  generalizedHypergeometric_fields_wimp_coeff' a b c d α β γ ζ hαβ (by simpa using (hγ 0).2) N

/-- The analytic expansion under explicit absolute double-series convergence and valid original
germs. Stronger than DLMF, which assumes regular lower parameters `b + d` and `γ + 2k + 1` and
`(γ + k)ₖ ≠ 0` for all `k`; only `α, β` and `γ + 1` need to avoid the nonpositive integers. -/
@[dlmf 16.10.E1]
theorem generalizedHypergeometric_fields_wimp_hasSum' (a b c d : Multiset ℂ) (α β γ z ζ : ℂ)
    (hαβ : LowerParametersRegular {α, β}) (hγ : LowerParametersRegular {γ + 1})
    (hleft : HasSum (fun n => generalizedHypergeometricCoeff (a + c) (b + d) n * (z * ζ) ^ n)
      (generalizedHypergeometric (a + c) (b + d) (z * ζ)))
    (hinner : ∀ k : ℕ, HasSum (fun n =>
        generalizedHypergeometricCoeff ((α + k) ::ₘ (β + k) ::ₘ shiftParameters a k)
          ((γ + 2 * k + 1) ::ₘ shiftParameters b k) n * z ^ n)
      (generalizedHypergeometric ((α + k) ::ₘ (β + k) ::ₘ shiftParameters a k)
        ((γ + 2 * k + 1) ::ₘ shiftParameters b k) z))
    (habs : Summable (fun kn : ℕ × ℕ => ‖genFieldsWimpDoubleTerm a b c d α β γ z ζ kn‖)) :
    HasSum (genFieldsWimpTerm a b c d α β γ z ζ)
        (generalizedHypergeometric (a + c) (b + d) (z * ζ)) := by
  have hf : Summable (genFieldsWimpDoubleTerm a b c d α β γ z ζ) := habs.of_norm
  have h1 : HasSum (genFieldsWimpTerm a b c d α β γ z ζ)
      (∑' kn, genFieldsWimpDoubleTerm a b c d α β γ z ζ kn) :=
    hf.hasSum.prod_fiberwise fun k => by
      have := (hinner k).mul_left (genFieldsWimpCoeff a b α β γ k * z ^ k *
        generalizedHypergeometricTruncated k ((-k : ℂ) ::ₘ (γ + k) ::ₘ c) (α ::ₘ β ::ₘ d) ζ)
      convert this using 1
      · funext n; simp only [genFieldsWimpDoubleTerm]; ring
      · simp only [genFieldsWimpTerm]; ring
  have h2 : HasSum (fun N => generalizedHypergeometricCoeff (a + c) (b + d) N * (z * ζ) ^ N)
      (∑' kn, genFieldsWimpDoubleTerm a b c d α β γ z ζ kn) := by
    have hs := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).hasSum_iff.mpr
      hf.hasSum
    refine hs.sigma fun N => ?_
    convert hasSum_fintype _ using 1
    change _ = ∑ x : antidiagonal N, genFieldsWimpDoubleTerm a b c d α β γ z ζ (x : ℕ × ℕ)
    rw [Finset.sum_coe_sort (antidiagonal N)
      (fun x => genFieldsWimpDoubleTerm a b c d α β γ z ζ x),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      show generalizedHypergeometricCoeff (a + c) (b + d) N * (z * ζ) ^ N =
        z ^ N * (generalizedHypergeometricCoeff (a + c) (b + d) N * ζ ^ N) by ring,
      generalizedHypergeometric_fields_wimp_coeff' a b c d α β γ ζ hαβ hγ N, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    simp only [genFieldsWimpDoubleTerm]
    rw [show z ^ N = z ^ k * z ^ (N - k) by rw [← pow_add, Nat.add_sub_cancel' hkN]]
    ring
  rwa [h2.unique hleft] at h1

/-- The analytic expansion under explicit absolute double-series convergence and valid original
germs. -/
@[dlmf 16.10.E1]
theorem generalizedHypergeometric_fields_wimp_hasSum (a b c d : Multiset ℂ) (α β γ z ζ : ℂ)
    (_hb : LowerParametersRegular (b + d)) (hαβ : LowerParametersRegular {α, β})
    (hγ : ∀ k : ℕ, pochhammer (γ + k) k ≠ 0 ∧ LowerParametersRegular {γ + 2 * k + 1})
    (hleft : HasSum (fun n => generalizedHypergeometricCoeff (a + c) (b + d) n * (z * ζ) ^ n)
      (generalizedHypergeometric (a + c) (b + d) (z * ζ)))
    (hinner : ∀ k : ℕ, HasSum (fun n =>
        generalizedHypergeometricCoeff ((α + k) ::ₘ (β + k) ::ₘ shiftParameters a k)
          ((γ + 2 * k + 1) ::ₘ shiftParameters b k) n * z ^ n)
      (generalizedHypergeometric ((α + k) ::ₘ (β + k) ::ₘ shiftParameters a k)
        ((γ + 2 * k + 1) ::ₘ shiftParameters b k) z))
    (habs : Summable (fun kn : ℕ × ℕ => ‖genFieldsWimpDoubleTerm a b c d α β γ z ζ kn‖)) :
    HasSum (genFieldsWimpTerm a b c d α β γ z ζ)
        (generalizedHypergeometric (a + c) (b + d) (z * ζ)) :=
  generalizedHypergeometric_fields_wimp_hasSum' a b c d α β γ z ζ hαβ (by simpa using (hγ 0).2)
      hleft hinner habs

/-- Norlund expansion with the full printed convergence half-plane and zeta disk. -/
@[dlmf 16.10.E2]
theorem generalizedHypergeometric_norlund_expansion (a : ℂ) (A B : Multiset ℂ)
    (hcard : A.card = B.card)
    (hb : LowerParametersRegular B)
    {z ζ : ℂ} (hζ : ‖ζ - 1‖ < 1) (hz : z.re < 1 / 2) :
    HasSum (fun k : ℕ => (1 - z) ^ (-a) * pochhammer a k / k.factorial *
      generalizedHypergeometricTruncated k ((-k : ℂ) ::ₘ A) B ζ * (z / (z - 1)) ^ k)
      (generalizedHypergeometric (a ::ₘ A) B (z * ζ)) := by
  sorry

/-- Duplication for Pochhammer symbols: `(x)₂ₙ = 4ⁿ (x/2)ₙ ((x+1)/2)ₙ`. -/
private lemma pochhammer_two_mul_eq_four_pow_mul (x : ℂ) (n : ℕ) :
    pochhammer x (2 * n) = 4 ^ n * pochhammer (x / 2) n * pochhammer ((x + 1) / 2) n := by
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, pochhammer_succ, pochhammer_succ, ih,
                                              pochhammer_succ, pochhammer_succ]
    push_cast
    ring

/-- A Chu–Vandermonde rearrangement: `∑ C(n,k) (a+k)ₙ₋ₖ (b+n-k)ₖ = (a+b+n-1)ₙ`. -/
private lemma sum_choose_mul_pochhammer_mul_pochhammer (a b : ℂ) (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℂ) * pochhammer (a + k) (n - k) *
        pochhammer (b + (n - k : ℕ)) k =
      pochhammer (a + b + n - 1) n := by
  have h := chu_vandermonde_sum n (1 - b - n) a
  rw [show a - (1 - b - n) = a + b + n - 1 by ring] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hr := pochhammer_reflect (b + (n - k : ℕ)) k
  rw [show 1 - (b + ((n - k : ℕ) : ℂ)) - k = 1 - b - n by push_cast [Nat.cast_sub hk']; ring] at hr
  rw [hr]
  have : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  linear_combination (n.choose k : ℂ) * pochhammer (a + k) (n - k) *
      pochhammer (b + (n - k : ℕ)) k * this.symm

/-- Cauchy-product coefficients of two `0F1` series (DLMF 16.12.1). -/
private lemma sum_inv_pochhammer_mul_factorial_mul_inv_pochhammer_mul_factorial (a b : ℂ)
    (ha : ∀ k : ℕ, a ≠ -k)
    (hb : ∀ k : ℕ, b ≠ -k)
    (hab : ∀ k : ℕ, a + b - 1 ≠ -k) (n : ℕ) :
    ∑ k ∈ range (n + 1), 1 / (pochhammer a k * k !) * (1 / (pochhammer b (n - k) * (n - k)!)) =
      4 ^ n * pochhammer ((a + b) / 2) n * pochhammer ((a + b - 1) / 2) n /
        (pochhammer a n * pochhammer b n * pochhammer (a + b - 1) n * n !) := by
  have hpa := pochhammer_ne_zero_of_not_neg_nat ha
  have hpb := pochhammer_ne_zero_of_not_neg_nat hb
  have hpab := pochhammer_ne_zero_of_not_neg_nat hab
  have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hterm : ∀ k ∈ range (n + 1), 1 / (pochhammer a k * k !) *
      (1 / (pochhammer b (n - k) * (n - k)!)) =
      (n.choose k : ℂ) * pochhammer (a + k) (n - k) * pochhammer (b + (n - k : ℕ)) k /
        (pochhammer a n * pochhammer b n * n !) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 := pochhammer_add a k (n - k)
    have h2 := pochhammer_add b (n - k) k
    rw [Nat.add_sub_of_le hk'] at h1
    rw [Nat.sub_add_cancel hk'] at h2
    have h3 : (n ! : ℂ) = n.choose k * k ! * (n - k)! := by
      exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hk').symm
    have hk0 : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hnk0 : ((n - k)! : ℂ) ≠ 0 := by exact_mod_cast (n - k).factorial_ne_zero
    have hA : pochhammer (a + k) (n - k) ≠ 0 := fun h => hpa n (by rw [h1, h, mul_zero])
    have hB : pochhammer (b + (n - k : ℕ)) k ≠ 0 := fun h => hpb n (by rw [h2, h, mul_zero])
    have hC : (n.choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk').ne'
    rw [h1, h2, h3]
    have := hpa k
    have := hpb (n - k)
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, sum_choose_mul_pochhammer_mul_pochhammer]
  have hdup := pochhammer_two_mul_eq_four_pow_mul (a + b - 1) n
  rw [show (a + b - 1 + 1) / 2 = (a + b) / 2 by ring] at hdup
  have hsplit := pochhammer_add (a + b - 1) n n
  rw [← two_mul] at hsplit
  rw [div_eq_div_iff (by simp [hpa n, hpb n, hn]) (by simp [hpa n, hpb n, hn, hpab n])]
  rw [show a + b + n - 1 = a + b - 1 + n by ring]
  linear_combination (pochhammer a n * pochhammer b n * n !) * (hsplit.symm.trans hdup)

/-- The `0F1` coefficient. -/
private lemma generalizedHypergeometricCoeff_empty_singleton (a : ℂ) (n : ℕ) :
    generalizedHypergeometricCoeff ∅ {a} n = 1 /
    (pochhammer a n * n !) := by
  simp [generalizedHypergeometricCoeff, pochhammerProduct]

/-- Absolute summability of the `0F1` series. -/
private lemma summable_norm_generalizedHypergeometricCoeff_empty_singleton_mul_pow (a z : ℂ)
    (ha : ∀ k : ℕ, a ≠ -k) :
    Summable fun n : ℕ => ‖generalizedHypergeometricCoeff ∅ {a} n * z ^ n‖ := by
  obtain ⟨C, hC0, hC⟩ := factorial_le_mul_norm_pochhammer a ha (σ := 2) (by norm_num)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((Real.summable_pow_div_factorial (2 * ‖z‖)).mul_left C)
  have hp : 0 < ‖pochhammer a n‖ := norm_pos_iff.mpr (pochhammer_ne_zero_of_not_neg_nat ha n)
  have hf : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have hf1 : (1 : ℝ) ≤ n ! := by exact_mod_cast n.factorial_pos
  rw [generalizedHypergeometricCoeff_empty_singleton, norm_mul, norm_div, norm_one,
      norm_mul, norm_pow,
      Complex.norm_natCast,
    mul_pow, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  have h := hC n
  calc ‖z‖ ^ n = ‖z‖ ^ n * 1 := by ring
    _ ≤ ‖z‖ ^ n * (C * 2 ^ n * ‖pochhammer a n‖ / n !) := by
        gcongr; rw [le_div_iff₀ hf]; linarith
    _ ≤ ‖z‖ ^ n * (C * 2 ^ n * ‖pochhammer a n‖ / n !) * n ! := by
        have : 0 ≤ ‖z‖ ^ n * (C * 2 ^ n * ‖pochhammer a n‖ / n !) := by positivity
        nlinarith
    _ = C * (2 ^ n * ‖z‖ ^ n / n !) * (‖pochhammer a n‖ * n !) := by field_simp

/-- The product of two 0F1 functions for every complex z. -/
@[dlmf 16.12.E1]
theorem generalizedHypergeometric_0F1_product (a b z : ℂ)
    (hb : LowerParametersRegular {a, b, a + b - 1}) :
    generalizedHypergeometric ∅ {a} z * generalizedHypergeometric ∅ {b} z =
      generalizedHypergeometric {(a + b) / 2, (a + b - 1) / 2} {a, b, a + b - 1} (4 * z) := by
  have ha' : ∀ k : ℕ, a ≠ -k := hb a (by simp)
  have hb' : ∀ k : ℕ, b ≠ -k := hb b (by simp)
  have hab' : ∀ k : ℕ, a + b - 1 ≠ -k := hb (a + b - 1) (by simp)
  have hA := generalizedHypergeometric_hasSum_entire (a := ∅) (b := {a}) (by simp)
    (fun x hx => by rw [Multiset.mem_singleton] at hx; subst hx; exact ha') z
  have hB := generalizedHypergeometric_hasSum_entire (a := ∅) (b := {b}) (by simp)
    (fun x hx => by rw [Multiset.mem_singleton] at hx; subst hx; exact hb') z
  have hC := generalizedHypergeometric_hasSum_entire (a := {(a + b) / 2, (a + b - 1) / 2})
      (b := {a, b, a + b - 1})
    (by simp) hb (4 * z)
  rw [← hA.tsum_eq, ← hB.tsum_eq, ← hC.tsum_eq,
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
        (summable_norm_generalizedHypergeometricCoeff_empty_singleton_mul_pow a z ha')
      (summable_norm_generalizedHypergeometricCoeff_empty_singleton_mul_pow b z hb')]
  congr 1
  funext n
  have hcoef := sum_inv_pochhammer_mul_factorial_mul_inv_pochhammer_mul_factorial a b ha' hb' hab' n
  have hsum : ∑ k ∈ range (n + 1), generalizedHypergeometricCoeff ∅ {a} k * z ^ k *
      (generalizedHypergeometricCoeff ∅ {b} (n - k) * z ^ (n - k)) =
      (∑ k ∈ range (n + 1), 1 / (pochhammer a k * k !) *
          (1 / (pochhammer b (n - k) * (n - k)!))) * z ^ n := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [generalizedHypergeometricCoeff_empty_singleton,
        generalizedHypergeometricCoeff_empty_singleton, ← Nat.add_sub_of_le hk', pow_add,
      Nat.add_sub_cancel_left]
    ring
  rw [hsum, hcoef]
  simp only [generalizedHypergeometricCoeff, pochhammerProduct, Multiset.insert_eq_cons,
      Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, mul_pow]
  ring

/-- The existing Clausen germ identity continued to its whole principal slit. -/
@[dlmf 16.12.E2]
theorem generalizedHypergeometric_clausen_principal (a b : ℂ)
    (hb : LowerParametersRegular {a + b + 1 / 2, 2 * a + 2 * b})
    {z : ℂ} (hz : z ∈ cutPlane) :
    generalizedHypergeometric {a, b} {a + b + 1 / 2} z ^ 2 =
      generalizedHypergeometric {2 * a, 2 * b, a + b} {a + b + 1 / 2, 2 * a + 2 * b} z := by
  have hc : ∀ k : ℕ, a + b + 1 / 2 ≠ -k := fun k => hb _ (by simp) k
  have hd : ∀ k : ℕ, 2 * a + 2 * b ≠ -k := fun k => hb _ (by simp) k
  have hc' : LowerParametersRegular {a + b + 1 / 2} := fun x hx k => by
    rw [Multiset.mem_singleton] at hx; subst hx; exact hc k
  refine eqOn_cutPlane_of_eqOn_disk
      (f := fun z => generalizedHypergeometric {a, b} {a + b + 1 / 2} z ^ 2)
    (g := generalizedHypergeometric {2 * a, 2 * b, a + b} {a + b + 1 / 2, 2 * a + 2 * b})
    ((generalizedHypergeometric_principal_analytic (by simp)).pow 2)
        (generalizedHypergeometric_principal_analytic (by simp))
    (fun w hw => ?_) hz
  have h1 := generalizedHypergeometric_hasSum_disk (a := {a, b}) (b := {a + b + 1 / 2})
      (by simp) hc' hw
  have h2 := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b (a + b + 1 / 2)).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one hw)
  have h3 := generalizedHypergeometric_hasSum_disk (a := {2 * a, 2 * b, a + b})
    (b := {a + b + 1 / 2, 2 * a + 2 * b}) (by simp) hb hw
  have h4 := clausen_formula hc hd hw
  have e12 : generalizedHypergeometric {a, b} {a + b + 1 / 2} w = ₂F₁ a b (a + b + 1 / 2) w := by
    refine h1.unique (h2.congr_fun fun n => ?_)
    simp [generalizedHypergeometricCoeff, pochhammerProduct, gaussHypergeometricCoeff]
  have e34 : generalizedHypergeometric {2 * a, 2 * b, a + b} {a + b + 1 / 2, 2 * a + 2 * b} w =
      ₂F₁ a b (a + b + 1 / 2) w ^ 2 := by
    refine h3.unique (h4.congr_fun fun n => ?_)
    simp only [generalizedHypergeometricCoeff, pochhammerProduct, clausenCoeff,
        Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
    ring
  simp only [e12, e34]

/-- The full generalized square series; terminating inner sums preserve lower exceptions after
termination. -/
@[dlmf 16.12.E3]
theorem generalizedHypergeometric_general_square_hasSum (a b c : ℂ)
    (hb : LowerParametersRegular {c, 2 * c - 1, a + 1 / 2, b + 1 / 2})
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => pochhammer (2 * a) k * pochhammer (2 * b) k * pochhammer (c - 1 / 2) k /
      (pochhammer c k * pochhammer (2 * c - 1) k * k.factorial) *
      generalizedHypergeometricTruncated k
          {-(k : ℂ) / 2, (1 - (k : ℂ)) / 2, a + b - c + 1 / 2, 1 / 2}
        {a + 1 / 2, b + 1 / 2, 3 / 2 - (k : ℂ) - c} 1 *
            z ^ k) (generalizedHypergeometric {a, b} {c} z ^ 2) := by
  sorry

end DLMF.Hypergeometric
