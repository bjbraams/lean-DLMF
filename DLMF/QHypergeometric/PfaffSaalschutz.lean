/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.QExponential
public import DLMF.QSeries.Saalschutz
public import DLMF.QHypergeometric.Basic.ShiftedFactorials

/-!
# The terminating q-Pfaff–Saalschütz sum

The balanced terminating sum of DLMF 17.7.4 is proved from the polynomial
q-Pfaff–Saalschütz identity. Cleared products retain regular zero upper parameters.
-/

@[expose] public noncomputable section

open Complex Filter Finset Set DLMF.QSeries
open scoped Topology

namespace DLMF.QHypergeometric

attribute [local fun_prop] continuous_qPochhammer

/-- `(q^{-n};q)_m ≠ 0` for `m ≤ n` when `0<‖q‖<1`. -/
theorem PfaffSaalschutz.pochhammer_zpow_neg_ne_zero {q : ℂ} (hq0 : q≠0)
    (hq : ‖q‖<1) {n m : ℕ} (hm : m≤n) :
    qPochhammer (q^(-(n:ℤ))) q m ≠ 0 := by
  rw [qPochhammer_eq_prod, prod_ne_zero_iff]
  intro i hi h
  have hin : i < n := lt_of_lt_of_le (mem_range.mp hi) hm
  have h1 : q^i = q^n := by
    have := congrArg (· * q^n) h
    simp only [sub_mul, one_mul, zpow_neg, zpow_natCast] at this
    field_simp at this
    linear_combination -this
  have h2 : q^(n-i) = 1 := by
    have : q^n = q^i * q^(n-i) := by rw [← pow_add]; congr 1; omega
    rw [this] at h1
    exact (mul_eq_left₀ (pow_ne_zero i hq0)).mp h1.symm
  have : ‖q^(n-i)‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  rw [h2, norm_one] at this
  exact lt_irrefl _ this

/-- Clearing the denominators of `(c/a;q)_n`. -/
theorem PfaffSaalschutz.prod_sub_mul_pow_eq_pow_mul_qPochhammer {a c q : ℂ} (ha : a≠0) (n : ℕ) :
    (range n).prod (fun j => a-c*q^j) = a^n*qPochhammer (c/a) q n := by
  rw [qPochhammer_eq_prod, show a^n = ∏ _j∈range n, a by simp, ← prod_mul_distrib]
  refine prod_congr (by simp) fun j _ => ?_
  field_simp

/-- If `(abq^{1-n}/c;q)_n ≠ 0` then `ab ≠ cq^j` for `j<n`. -/
private lemma prod_mul_sub_mul_pow_ne_zero {a b c q : ℂ} (hc : c≠0) (hq0 : q≠0) (n : ℕ)
    (hX : qPochhammer (a*b*q^(1-(n:ℤ))/c) q n ≠ 0) :
    (range n).prod (fun j => a*b-c*q^j) ≠ 0 := by
  rw [prod_ne_zero_iff]
  intro j hj h
  apply hX
  rw [qPochhammer_eq_prod]
  have hjn := mem_range.mp hj
  refine prod_eq_zero (i := n-1-j) (mem_range.mpr (by omega)) ?_
  rw [sub_eq_zero.mp h]
  have : q^(1-(n:ℤ)) * q^(n-1-j) * q^j = 1 := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq0, ← zpow_add₀ hq0]
    rw [show (1-(n:ℤ)) + ((n-1-j : ℕ):ℤ) + (j:ℤ) = 0 by
                                                       push_cast [Nat.sub_sub, show 1+j ≤
                                                         n by omega]; ring]
    simp
  field_simp
  linear_combination -this

/-- The terminating q-Pfaff–Saalschütz sum for nonzero `a,b`, from
`DLMF.QSeries.sum_saalschutz_div`. -/
theorem PfaffSaalschutz.sum_eq_quotient_of_ne_zero {a b c q : ℂ}
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hq0 : q≠0)
    (hq : ‖q‖<1) (n : ℕ)
    (hX : qPochhammer (a*b*q^(1-(n:ℤ))/c) q n ≠ 0) (hC : qPochhammer c q n ≠ 0) :
    ∑ k ∈ range (n+1), qPochhammer a q k * qPochhammer b q k * qPochhammer (q^(-(n:ℤ))) q k /
      (qPochhammer c q k * qPochhammer (a*b*q^(1-(n:ℤ))/c) q k * qPochhammer q q k) * q^k =
    qPochhammer (c/a) q n * qPochhammer (c/b) q n /
      (qPochhammer c q n * qPochhammer (c/(a*b)) q n) := by
  set x := c/(a*b) with hx
  have hx0 : x ≠ 0 := by rw [hx]; exact div_ne_zero hc (mul_ne_zero ha hb)
  have hxrs : x*a*b = c := by rw [hx]; field_simp
  have hS := sum_saalschutz_div q x a b n (fun m _ => qPochhammer_self_ne_zero hq m)
    (by rw [hxrs]; exact hC)
  rw [hxrs, show x*a = c/b by rw [hx]; field_simp, show x*b = c/a by rw [hx]; field_simp] at hS
  have hxn : qPochhammer x q n ≠ 0 := by
    have h := prod_mul_sub_mul_pow_ne_zero hc hq0 n hX
    rw [PfaffSaalschutz.prod_sub_mul_pow_eq_pow_mul_qPochhammer (mul_ne_zero ha hb)] at h
    exact right_ne_zero_of_mul h
  have hQn : qPochhammer q q n ≠ 0 := qPochhammer_self_ne_zero hq n
  have hXp : q^(1-(n:ℤ))/x = a*b*q^(1-(n:ℤ))/c := by rw [hx]; field_simp
  have hQp : q^(1-(n:ℤ))/q = q^(-(n:ℤ)) := by
    rw [zpow_sub₀ hq0, zpow_one, zpow_neg]; field_simp
  have key : ∀ m ∈ range (n+1), qPochhammer a q m * qPochhammer b q m *
      qPochhammer (q^(-(n:ℤ))) q m /
      (qPochhammer c q m * qPochhammer (a*b*q^(1-(n:ℤ))/c) q m * qPochhammer q q m) * q^m =
      qPochhammer q q n / qPochhammer x q n *
      (qPochhammer a q m * qPochhammer b q m * qPochhammer x q (n - m) * x ^ m /
        (qPochhammer q q (n - m) * qPochhammer q q m * qPochhammer c q m)) := by
    intro m hm
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
    have hXm : qPochhammer (a*b*q^(1-(n:ℤ))/c) q m ≠ 0 := qPochhammer_ne_zero_of_le hX hmn
    have hNm : qPochhammer (q^(-(n:ℤ))) q m ≠ 0 :=
      PfaffSaalschutz.pochhammer_zpow_neg_ne_zero hq0 hq hmn
    have hCm : qPochhammer c q m ≠ 0 := qPochhammer_ne_zero_of_le hC hmn
    have hqm : qPochhammer q q m ≠ 0 := qPochhammer_self_ne_zero hq m
    have h1 := qPochhammer_sub_index hx0 hq0 hmn (by rw [hXp]; exact hXm)
    have h2 := qPochhammer_sub_index hq0 hq0 hmn (by rw [hQp]; exact hNm)
    rw [hXp] at h1
    rw [hQp] at h2
    rw [h1, h2]
    have hE : q^((m.choose 2:ℤ)-(n:ℤ)*m) ≠ 0 := zpow_ne_zero _ hq0
    rw [show (-q/q) = -1 by field_simp, show (-q/x)^m =
                              (-1)^m*(q^m/x^m) by rw [neg_div, neg_pow, div_pow]]
    have hm1 : ((-1:ℂ))^m ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  rw [sum_congr rfl key, ← mul_sum, hS]
  field_simp

/-- The summand of the terminating q-Pfaff–Saalschütz sum. -/
def saalTerm (a b c q : ℂ) (n k : ℕ) : ℂ :=
  qPochhammer a q k * qPochhammer b q k * qPochhammer (q^(-(n:ℤ))) q k /
      (qPochhammer c q k * qPochhammer (a*b*q^(1-(n:ℤ))/c) q k * qPochhammer q q k) * q^k

/-- The cleared product side of the terminating q-Pfaff–Saalschütz sum. -/
def saalValue (a b c q : ℂ) (n : ℕ) : ℂ :=
  ((range n).prod (fun j => a-c*q^j))*((range n).prod (fun j => b-c*q^j))/
        (qPochhammer c q n*((range n).prod (fun j => a*b-c*q^j)))

/-- The cleared q-Pfaff–Saalschütz identity at nonzero `a,b`. -/
private lemma sum_saalTerm_of_ne_zero {a b c q : ℂ} (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hq0 : q≠0) (hq : ‖q‖<1)
    (n : ℕ) (hC : qPochhammer c q n ≠ 0) (hX : qPochhammer (a*b*q^(1-(n:ℤ))/c) q n ≠ 0) :
    ∑ k ∈ range (n+1), saalTerm a b c q n k = saalValue a b c q n := by
  have hxn : qPochhammer (c/(a*b)) q n ≠ 0 := by
    have h := prod_mul_sub_mul_pow_ne_zero hc hq0 n hX
    rw [PfaffSaalschutz.prod_sub_mul_pow_eq_pow_mul_qPochhammer (mul_ne_zero ha hb)] at h
    exact right_ne_zero_of_mul h
  simp only [saalTerm, saalValue]
  rw [PfaffSaalschutz.sum_eq_quotient_of_ne_zero ha hb hc hq0 hq n hX hC,
    PfaffSaalschutz.prod_sub_mul_pow_eq_pow_mul_qPochhammer ha,
      PfaffSaalschutz.prod_sub_mul_pow_eq_pow_mul_qPochhammer hb,
    PfaffSaalschutz.prod_sub_mul_pow_eq_pow_mul_qPochhammer (mul_ne_zero ha hb)]
  field_simp
  ring

/-- Removable parameter values: continuity in the first parameter. -/
private lemma sum_saalTerm_of_punctured {b c q t0 : ℂ} (hq : ‖q‖<1) (hc : c≠0) (hq0 : q≠0) (n : ℕ)
    (hC : qPochhammer c q n ≠ 0) (hX : qPochhammer (t0*b*q^(1-(n:ℤ))/c) q n ≠ 0)
    (h : ∀ t, t ≠ t0 → qPochhammer (t*b*q^(1-(n:ℤ))/c) q n ≠ 0 →
      ∑ k ∈ range (n+1), saalTerm t b c q n k = saalValue t b c q n) :
    ∑ k ∈ range (n+1), saalTerm t0 b c q n k = saalValue t0 b c q n := by
  have hkd : ∀ k ∈ range (n+1), qPochhammer c q k * qPochhammer (t0*b*q^(1-(n:ℤ))/c) q k *
      qPochhammer q q k ≠ 0 := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    exact mul_ne_zero (mul_ne_zero (qPochhammer_ne_zero_of_le hC hkn)
      (qPochhammer_ne_zero_of_le hX hkn)) (qPochhammer_self_ne_zero hq k)
  have h2 : qPochhammer c q n * (range n).prod (fun j => t0*b-c*q^j) ≠ 0 :=
    mul_ne_zero hC (prod_mul_sub_mul_pow_ne_zero hc hq0 n hX)
  let g : ℂ → ℂ := fun t => ∑ k ∈ range (n+1), saalTerm t b c q n k - saalValue t b c q n
  have hg : ContinuousAt g t0 := by
    simp only [g, saalTerm, saalValue]
    refine ContinuousAt.sub ?_ (by fun_prop (disch := exact h2))
    exact tendsto_finsetSum _ fun k hk => (by fun_prop (disch := exact hkd k hk) :
      ContinuousAt (fun t : ℂ => qPochhammer t q k * qPochhammer b q k *
          qPochhammer (q^(-(n:ℤ))) q k /
        (qPochhammer c q k * qPochhammer (t*b*q^(1-(n:ℤ))/c) q k * qPochhammer q q k) * q^k) t0)
  have hXc : ContinuousAt (fun t : ℂ => qPochhammer (t*b*q^(1-(n:ℤ))/c) q n) t0 := by fun_prop
  have hev : g =ᶠ[𝓝[≠] t0] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hXc.eventually_ne hX)] with t ht hXt
    simp only [g, h t ht hXt, sub_self]
  have h1 : Tendsto g (𝓝[≠] t0) (𝓝 (g t0)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  have h0 := tendsto_nhds_unique h1 (tendsto_const_nhds.congr' hev.symm)
  exact sub_eq_zero.mp h0

/-- Swapping the first two parameters. -/
private lemma sum_saalTerm_comm_iff (a b c q : ℂ) (n : ℕ) :
    (∑ k ∈ range (n+1), saalTerm a b c q n k = saalValue a b c q n) ↔
    (∑ k ∈ range (n+1), saalTerm b a c q n k = saalValue b a c q n) := by
  simp only [saalTerm, saalValue, mul_comm a b]
  constructor <;> intro h <;> convert h using 2 <;> ring

/-- The cleared terminating q-Pfaff–Saalschütz identity for all `a,b`. -/
theorem PfaffSaalschutz.sum_eq_cleared_value {a b c q : ℂ} (hc : c≠0) (hq0 : q≠0) (hq : ‖q‖<1)
    (n : ℕ) (hC : qPochhammer c q n ≠ 0) (hX : qPochhammer (a*b*q^(1-(n:ℤ))/c) q n ≠ 0) :
    ∑ k ∈ range (n+1), saalTerm a b c q n k = saalValue a b c q n := by
  have step1 : ∀ a b : ℂ, b ≠ 0 → qPochhammer (a*b*q^(1-(n:ℤ))/c) q n ≠ 0 →
      ∑ k ∈ range (n+1), saalTerm a b c q n k = saalValue a b c q n := by
    intro a b hb hX
    by_cases ha : a = 0
    · subst ha
      exact sum_saalTerm_of_punctured hq hc hq0 n hC hX fun t ht hXt =>
        sum_saalTerm_of_ne_zero ht hb hc hq0 hq n hC hXt
    · exact sum_saalTerm_of_ne_zero ha hb hc hq0 hq n hC hX
  by_cases hb : b = 0
  · subst hb
    have hX' : qPochhammer (0*a*q^(1-(n:ℤ))/c) q n ≠ 0 := by simp
    by_cases ha : a = 0
    · subst ha
      exact sum_saalTerm_of_punctured hq hc hq0 n hC hX fun t ht hXt =>
        (sum_saalTerm_comm_iff t 0 c q n).mpr (step1 0 t ht (by simp))
    · exact (sum_saalTerm_comm_iff a 0 c q n).mpr (step1 0 a ha hX')
  · exact step1 a b hb hX

/-- A terminating series is the finite sum through the terminating index. -/
theorem PfaffSaalschutz.qPhi_eq_sum_of_mem {a b : List ℂ} {q z : ℂ} (hq0 : q≠0) (N : ℕ)
    (hmem : q^(-(N:ℤ)) ∈ a) :
    qPhi a b q z = ∑ k ∈ range (N+1), qPhiTerm a b q z k := by
  unfold qPhi
  apply tsum_eq_sum
  intro k hk
  have hNk : N<k := by simpa using hk
  have hz := qPochhammer_recip_pow_eq_zero hq0 hNk
  have h0 : qPochhammerList a q k = 0 := by
    apply List.prod_eq_zero
    exact List.mem_map.mpr ⟨_, hmem, by simpa [zpow_neg] using hz⟩
  simp [qPhiTerm, h0]

/-- The cleared finite product includes regular a=0 and b=0. -/
@[dlmf 17.7.E4]
theorem q_pfaff_saalschutz {a b c q : ℂ} (hc0 : c≠0) (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : QDenominatorRegularThrough [c,a*b*q^(1-(n:ℤ))/c] q n) :
    qPhi [a,b,q^(-(n:ℤ))] [c,a*b*q^(1-(n:ℤ))/c] q q=
      ((range n).prod (fun j => a-c*q^j))*((range n).prod (fun j => b-c*q^j))/
        (qPochhammer c q n*((range n).prod (fun j => a*b-c*q^j))) := by
  simp only [QDenominatorRegularThrough, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one] at hd
  rw [PfaffSaalschutz.qPhi_eq_sum_of_mem hq0 n (by simp)]
  have := PfaffSaalschutz.sum_eq_cleared_value hc0 hq0 hq n
    (left_ne_zero_of_mul hd) (right_ne_zero_of_mul hd)
  simp only [saalTerm, saalValue] at this
  rw [← this]
  refine sum_congr rfl fun k _ => ?_
  simp [qPhiTerm, qPhiExponent, qPochhammerList, mul_assoc]

end DLMF.QHypergeometric
