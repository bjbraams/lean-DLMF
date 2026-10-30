/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bailey
public import DLMF.QHypergeometric.Convergence

/-!
# Higher basic summations (DLMF §17.7)

Finite sums retain parameter poles occurring only after the final retained term. Infinite
sums retain their actual convergence disks. Cleared products handle regular zero upper
parameters without evaluating0 times an infinite product quotient.

Two printed DLMF formulas have explicit counterexamples below. The corrected 17.7.19 uses
Gasper–Rahman, Basic Hypergeometric Series, (1.9.7), with argument a⁻¹q^(−Σm).
The corrected 17.7.23 follows George Gasper, Lecture Notes for an Introductory Minicourse on
q-Series (1995), (4.1.23), with p and q interchanged:
https://sites.math.northwestern.edu/~george/preprints/ggLecNotesq-Series/ggLecNotesq-Series.pdf .
The first denominator is(p;p)_k and the final shifted-factorial base is p. No false printed
identity is admitted. These references support the corrected statements; their proofs remain
admitted where a complete local proof is not yet available.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory DLMF.QSeries
open scoped Real Topology
namespace DLMF.QHypergeometric

/-- Shifted upper parameters for the q-Karlsson–Minton formulas. -/
def qMintonUpper (p : List (ℂ × ℕ)) (q : ℂ) : List ℂ := p.map fun x => x.1*q^x.2
/-- The corresponding unshifted lower parameters. -/
def qMintonLower (p : List (ℂ × ℕ)) : List ℂ := p.map Prod.fst
/-- Total nonnegative parameter displacement. -/
def qMintonWeight (p : List (ℂ × ℕ)) : ℕ := (p.map Prod.snd).sum
/-- The square-root-product cancellation in the four-phi-three sum. -/
def qFourPhiThreeValue (a b c q : ℂ) : ℂ :=
  let r := Complex.sqrt a
  let t := Complex.sqrt q
  qPochhammerListInf [r*t,-r*t,-r*q,q*r/b,q*r/c,a*q/(b*c)] q/
    qPochhammerListInf [a*q/b,a*q/c,q*r/(b*c)] q
/-- Pointwise definedness of integer shifted factorials before taking ratios. -/
def QIntPochhammerListDefined (p : List ℂ) (q : ℂ) (k : ℤ) : Prop :=
  0≤k ∨ ∀ a∈p, qPochhammer (a*q^k) q (-k).toNat≠0
/-- The `2φ2` summation `2φ2(a,q/a;-q,b;q,-b) = (ab,bq/a;q²)_∞/(b;q)_∞` (DLMF 17.7.E1). -/
@[dlmf 17.7.E1]
theorem two_phi_two_sum {a b q : ℂ} (ha : a≠0) (hq : ‖q‖<1) (hd : QDenominatorRegular [-q,b] q) :
    qPhi [a,q/a] [-q,b] q (-b)=qPochhammerListInf [a*b,b*q/a] (q^2)/qPochhammerInf b q := by
  sorry

/-- The `2φ2` summation at argument `-q` with lower parameters `±ab√q` (DLMF 17.7.E2). -/
@[dlmf 17.7.E2]
theorem two_phi_two_square_sum {a b q : ℂ} (hq : ‖q‖<1)
    (hd : QDenominatorRegular [a*b*Complex.sqrt q,-a*b*Complex.sqrt q] q) :
    qPhi [a^2,b^2] [a*b*Complex.sqrt q,-a*b*Complex.sqrt q] q (-q)=
      qPochhammerListInf [a^2*q,b^2*q] (q^2)/qPochhammerListInf [q,a^2*b^2*q] (q^2) := by
  sorry

/-- The cancelled product retains b=±q^(-m) whenever the lower parameters are regular. -/
@[dlmf 17.7.E3]
theorem two_phi_two_even_sum {b c q : ℂ} (hb : b≠0) (hq : ‖q‖<1) (hd : QDenominatorRegular [c,c*q] (q^2)) :
    qPhi [c^2/b^2,b^2] [c,c*q] (q^2) q=
      qPochhammerInf q (q^2)/(2*qPochhammerListInf [c,c*q] (q^2))*
      (qPochhammerInf (-b) q*qPochhammerInf (c/b) q+
       qPochhammerInf b q*qPochhammerInf (-c/b) q) := by
  sorry

attribute [local fun_prop] continuous_qPochhammer

/-- `(q^{-n};q)_m ≠ 0` for `m ≤ n` when `0<‖q‖<1`. -/
lemma qbR4_qPochhammer_neg_ne_zero {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) {n m : ℕ} (hm : m≤n) :
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
lemma qbR4_prod_sub_eq {a c q : ℂ} (ha : a≠0) (n : ℕ) :
    (range n).prod (fun j => a-c*q^j) = a^n*qPochhammer (c/a) q n := by
  rw [qPochhammer_eq_prod, show a^n = ∏ _j∈range n, a by simp, ← prod_mul_distrib]
  refine prod_congr (by simp) fun j _ => ?_
  field_simp

/-- If `(abq^{1-n}/c;q)_n ≠ 0` then `ab ≠ cq^j` for `j<n`. -/
lemma qbR4_prod_ab_ne_zero {a b c q : ℂ} (hc : c≠0) (hq0 : q≠0) (n : ℕ)
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
    rw [show (1-(n:ℤ)) + ((n-1-j : ℕ):ℤ) + (j:ℤ) = 0 by push_cast [Nat.sub_sub, show 1+j ≤ n by omega]; ring]
    simp
  field_simp
  linear_combination -this

/-- The terminating q-Pfaff–Saalschütz sum for nonzero `a,b`, from `DLMF.QSeries.sum_saalschutz_div`. -/
lemma qbR4_saal_nonzero {a b c q : ℂ} (ha : a≠0) (hb : b≠0) (hc : c≠0) (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
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
    have h := qbR4_prod_ab_ne_zero hc hq0 n hX
    rw [qbR4_prod_sub_eq (mul_ne_zero ha hb)] at h
    exact right_ne_zero_of_mul h
  have hQn : qPochhammer q q n ≠ 0 := qPochhammer_self_ne_zero hq n
  have hXp : q^(1-(n:ℤ))/x = a*b*q^(1-(n:ℤ))/c := by rw [hx]; field_simp
  have hQp : q^(1-(n:ℤ))/q = q^(-(n:ℤ)) := by
    rw [zpow_sub₀ hq0, zpow_one, zpow_neg]; field_simp
  have key : ∀ m ∈ range (n+1), qPochhammer a q m * qPochhammer b q m * qPochhammer (q^(-(n:ℤ))) q m /
      (qPochhammer c q m * qPochhammer (a*b*q^(1-(n:ℤ))/c) q m * qPochhammer q q m) * q^m =
      qPochhammer q q n / qPochhammer x q n *
      (qPochhammer a q m * qPochhammer b q m * qPochhammer x q (n - m) * x ^ m /
        (qPochhammer q q (n - m) * qPochhammer q q m * qPochhammer c q m)) := by
    intro m hm
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
    have hXm : qPochhammer (a*b*q^(1-(n:ℤ))/c) q m ≠ 0 := qPochhammer_ne_zero_of_le hX hmn
    have hNm : qPochhammer (q^(-(n:ℤ))) q m ≠ 0 := qbR4_qPochhammer_neg_ne_zero hq0 hq hmn
    have hCm : qPochhammer c q m ≠ 0 := qPochhammer_ne_zero_of_le hC hmn
    have hqm : qPochhammer q q m ≠ 0 := qPochhammer_self_ne_zero hq m
    have h1 := qPochhammer_sub_index hx0 hq0 hmn (by rw [hXp]; exact hXm)
    have h2 := qPochhammer_sub_index hq0 hq0 hmn (by rw [hQp]; exact hNm)
    rw [hXp] at h1
    rw [hQp] at h2
    rw [h1, h2]
    have hE : q^((m.choose 2:ℤ)-(n:ℤ)*m) ≠ 0 := zpow_ne_zero _ hq0
    rw [show (-q/q) = -1 by field_simp, show (-q/x)^m = (-1)^m*(q^m/x^m) by rw [neg_div, neg_pow, div_pow]]
    have hm1 : ((-1:ℂ))^m ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  rw [sum_congr rfl key, ← mul_sum, hS]
  field_simp

/-- The summand of the terminating q-Pfaff–Saalschütz sum. -/
def qbR4SaalTerm (a b c q : ℂ) (n k : ℕ) : ℂ :=
  qPochhammer a q k * qPochhammer b q k * qPochhammer (q^(-(n:ℤ))) q k /
      (qPochhammer c q k * qPochhammer (a*b*q^(1-(n:ℤ))/c) q k * qPochhammer q q k) * q^k

/-- The cleared product side of the terminating q-Pfaff–Saalschütz sum. -/
def qbR4SaalValue (a b c q : ℂ) (n : ℕ) : ℂ :=
  ((range n).prod (fun j => a-c*q^j))*((range n).prod (fun j => b-c*q^j))/
        (qPochhammer c q n*((range n).prod (fun j => a*b-c*q^j)))

/-- The cleared q-Pfaff–Saalschütz identity at nonzero `a,b`. -/
lemma qbR4_saal_nonzero' {a b c q : ℂ} (ha : a≠0) (hb : b≠0) (hc : c≠0) (hq0 : q≠0) (hq : ‖q‖<1)
    (n : ℕ) (hC : qPochhammer c q n ≠ 0) (hX : qPochhammer (a*b*q^(1-(n:ℤ))/c) q n ≠ 0) :
    ∑ k ∈ range (n+1), qbR4SaalTerm a b c q n k = qbR4SaalValue a b c q n := by
  have hxn : qPochhammer (c/(a*b)) q n ≠ 0 := by
    have h := qbR4_prod_ab_ne_zero hc hq0 n hX
    rw [qbR4_prod_sub_eq (mul_ne_zero ha hb)] at h
    exact right_ne_zero_of_mul h
  simp only [qbR4SaalTerm, qbR4SaalValue]
  rw [qbR4_saal_nonzero ha hb hc hq0 hq n hX hC, qbR4_prod_sub_eq ha, qbR4_prod_sub_eq hb,
    qbR4_prod_sub_eq (mul_ne_zero ha hb)]
  field_simp
  ring

/-- Removable parameter values: continuity in the first parameter. -/
lemma qbR4_saal_continuity {b c q t0 : ℂ} (hq : ‖q‖<1) (hc : c≠0) (hq0 : q≠0) (n : ℕ)
    (hC : qPochhammer c q n ≠ 0) (hX : qPochhammer (t0*b*q^(1-(n:ℤ))/c) q n ≠ 0)
    (h : ∀ t, t ≠ t0 → qPochhammer (t*b*q^(1-(n:ℤ))/c) q n ≠ 0 →
      ∑ k ∈ range (n+1), qbR4SaalTerm t b c q n k = qbR4SaalValue t b c q n) :
    ∑ k ∈ range (n+1), qbR4SaalTerm t0 b c q n k = qbR4SaalValue t0 b c q n := by
  have hkd : ∀ k ∈ range (n+1), qPochhammer c q k * qPochhammer (t0*b*q^(1-(n:ℤ))/c) q k *
      qPochhammer q q k ≠ 0 := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    exact mul_ne_zero (mul_ne_zero (qPochhammer_ne_zero_of_le hC hkn)
      (qPochhammer_ne_zero_of_le hX hkn)) (qPochhammer_self_ne_zero hq k)
  have h2 : qPochhammer c q n * (range n).prod (fun j => t0*b-c*q^j) ≠ 0 :=
    mul_ne_zero hC (qbR4_prod_ab_ne_zero hc hq0 n hX)
  let g : ℂ → ℂ := fun t => ∑ k ∈ range (n+1), qbR4SaalTerm t b c q n k - qbR4SaalValue t b c q n
  have hg : ContinuousAt g t0 := by
    simp only [g, qbR4SaalTerm, qbR4SaalValue]
    refine ContinuousAt.sub ?_ (by fun_prop (disch := exact h2))
    exact tendsto_finsetSum _ fun k hk => (by fun_prop (disch := exact hkd k hk) :
      ContinuousAt (fun t : ℂ => qPochhammer t q k * qPochhammer b q k * qPochhammer (q^(-(n:ℤ))) q k /
        (qPochhammer c q k * qPochhammer (t*b*q^(1-(n:ℤ))/c) q k * qPochhammer q q k) * q^k) t0)
  have hXc : ContinuousAt (fun t : ℂ => qPochhammer (t*b*q^(1-(n:ℤ))/c) q n) t0 := by fun_prop
  have hev : g =ᶠ[𝓝[≠] t0] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hXc.eventually_ne hX)] with t ht hXt
    simp only [g, h t ht hXt, sub_self]
  have h1 : Tendsto g (𝓝[≠] t0) (𝓝 (g t0)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  have h0 := tendsto_nhds_unique h1 (tendsto_const_nhds.congr' hev.symm)
  exact sub_eq_zero.mp h0

/-- Swapping the first two parameters. -/
lemma qbR4_saal_swap (a b c q : ℂ) (n : ℕ) :
    (∑ k ∈ range (n+1), qbR4SaalTerm a b c q n k = qbR4SaalValue a b c q n) ↔
    (∑ k ∈ range (n+1), qbR4SaalTerm b a c q n k = qbR4SaalValue b a c q n) := by
  simp only [qbR4SaalTerm, qbR4SaalValue, mul_comm a b]
  constructor <;> intro h <;> convert h using 2 <;> ring

/-- The cleared terminating q-Pfaff–Saalschütz identity for all `a,b`. -/
lemma qbR4_saal_all {a b c q : ℂ} (hc : c≠0) (hq0 : q≠0) (hq : ‖q‖<1)
    (n : ℕ) (hC : qPochhammer c q n ≠ 0) (hX : qPochhammer (a*b*q^(1-(n:ℤ))/c) q n ≠ 0) :
    ∑ k ∈ range (n+1), qbR4SaalTerm a b c q n k = qbR4SaalValue a b c q n := by
  have step1 : ∀ a b : ℂ, b ≠ 0 → qPochhammer (a*b*q^(1-(n:ℤ))/c) q n ≠ 0 →
      ∑ k ∈ range (n+1), qbR4SaalTerm a b c q n k = qbR4SaalValue a b c q n := by
    intro a b hb hX
    by_cases ha : a = 0
    · subst ha
      exact qbR4_saal_continuity hq hc hq0 n hC hX fun t ht hXt =>
        qbR4_saal_nonzero' ht hb hc hq0 hq n hC hXt
    · exact qbR4_saal_nonzero' ha hb hc hq0 hq n hC hX
  by_cases hb : b = 0
  · subst hb
    have hX' : qPochhammer (0*a*q^(1-(n:ℤ))/c) q n ≠ 0 := by simp
    by_cases ha : a = 0
    · subst ha
      exact qbR4_saal_continuity hq hc hq0 n hC hX fun t ht hXt =>
        (qbR4_saal_swap t 0 c q n).mpr (step1 0 t ht (by simp))
    · exact (qbR4_saal_swap a 0 c q n).mpr (step1 0 a ha hX')
  · exact step1 a b hb hX

/-- A terminating series is the finite sum through the terminating index. -/
lemma qbR4_qPhi_eq_sum_of_mem {a b : List ℂ} {q z : ℂ} (hq0 : q≠0) (N : ℕ)
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
  rw [qbR4_qPhi_eq_sum_of_mem hq0 n (by simp)]
  have := qbR4_saal_all hc0 hq0 hq n (left_ne_zero_of_mul hd) (right_ne_zero_of_mul hd)
  simp only [qbR4SaalTerm, qbR4SaalValue] at this
  rw [← this]
  refine sum_congr rfl fun k _ => ?_
  simp [qPhiTerm, qPhiExponent, qPochhammerList, mul_assoc]

/-- The nonterminating q-Saalschütz sum, combining two balanced `3φ2` series at argument `q` (DLMF
17.7.E5). -/
@[dlmf 17.7.E5]
theorem nonterminating_saalschutz {a b c e f q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (he : e≠0) (hf : f≠0) (hbal : e*f=a*b*c*q)
    (hd : QDenominatorRegular [e,f,q^2/e,q*f/e,e/q,a*q/e,b*q/e,c*q/e] q) :
    qPhi [a,b,c] [e,f] q q+
      qPochhammerListInf [q/e,a,b,c,q*f/e] q/qPochhammerListInf [e/q,a*q/e,b*q/e,c*q/e,f] q*
        qPhi [a*q/e,b*q/e,c*q/e] [q^2/e,q*f/e] q q=
      qPochhammerListInf [q/e,f/a,f/b,f/c] q/qPochhammerListInf [a*q/e,b*q/e,c*q/e,f] q := by
  sorry

/-- The terminating q-Dixon sum of a well-poised `3φ2` with upper parameter `q^(-2n)` (DLMF
17.7.E6). -/
@[dlmf 17.7.E6]
theorem q_dixon_terminating {b c q : ℂ} (hb : b≠0) (hc : c≠0) (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : QDenominatorRegularThrough [q^(1-(2*n:ℤ))/b,q^(1-(2*n:ℤ))/c] q (2*n)) :
    qPhi [q^(-(2*n:ℤ)),b,c] [q^(1-(2*n:ℤ))/b,q^(1-(2*n:ℤ))/c] q (q^(2-(n:ℤ))/(b*c))=
      qPochhammerList [b,c] q n*qPochhammerList [q,b*c] q (2*n)/
        (qPochhammerList [q,b*c] q n*qPochhammerList [b,c] q (2*n)) := by
  sorry

/-- The very-well-poised `4φ3` summation at argument `q√a/(bc)` (DLMF 17.7.E7). -/
@[dlmf 17.7.E7]
theorem four_phi_three_sum {a b c q : ℂ} (hq : ‖q‖<1) (hz : ‖q*Complex.sqrt a‖<‖b*c‖)
    (hd : QDenominatorRegular [-Complex.sqrt a,a*q/b,a*q/c] q) :
    qPhi [a,-q*Complex.sqrt a,b,c] [-Complex.sqrt a,a*q/b,a*q/c] q
      (q*Complex.sqrt a/(b*c))=qFourPhiThreeValue a b c q := by
  sorry

/-- A quadratic very-well-poised `8φ7` summation with `ℓ = -c√(ab/q)` (DLMF 17.7.E8). -/
@[dlmf 17.7.E8]
theorem eight_phi_seven_quadratic_sum {a b c q ell : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hc : c≠0)
    (hell : ell= -c*Complex.sqrt (a*b/q)) (hz : ‖ell*q‖<‖a*b‖)
    (hd : QDenominatorRegular [Complex.sqrt ell,-Complex.sqrt ell,ell*q/a,ell*q/b,ell*q/c,-ell*q/c,c^2] q) :
    qPhi [ell,q*Complex.sqrt ell,-q*Complex.sqrt ell,a,b,c,-c,ell*q/c^2]
      [Complex.sqrt ell,-Complex.sqrt ell,ell*q/a,ell*q/b,ell*q/c,-ell*q/c,c^2] q (-ell*q/(a*b))=
      qPochhammerListInf [ell*q,c^2/ell] q*qPochhammerListInf [a*q,b*q,c^2*q/a,c^2*q/b] (q^2)/
        (qPochhammerListInf [ell*q/a,ell*q/b] q*qPochhammerListInf [q,a*b*q,c^2*q,c^2*q/(a*b)] (q^2)) := by
  sorry

/-- A terminating `4φ3` summation at argument `q` whose value depends on the parity of `n` (DLMF
17.7.E9). -/
@[dlmf 17.7.E9]
theorem four_phi_three_parity {a c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : QDenominatorRegularThrough [Complex.sqrt (a*q),-Complex.sqrt (a*q),c^2] q n) :
    qPhi [q^(-(n:ℤ)),a*q^n,c,-c] [Complex.sqrt (a*q),-Complex.sqrt (a*q),c^2] q q=
      if Odd n then 0 else qPochhammer q (q^2) (n/2)*
        ((range (n/2)).prod (fun j => c^2-a*q^(2*j+1)))/
        qPochhammerList [a*q,c^2*q] (q^2) (n/2) := by
  sorry

/-- A very-well-poised `8φ7` summation with parameters built from `-c` (DLMF 17.7.E10). -/
@[dlmf 17.7.E10]
theorem eight_phi_seven_even_sum {a c d q : ℂ} (ha : a≠0) (hd0 : d≠0) (hq : ‖q‖<1) (hc : ‖c‖<1)
    (hd : QDenominatorRegular [Complex.sqrt (-c),-Complex.sqrt (-c),-c*q/a,-a*c,-q,c*q/d,c*d] q) :
    qPhi [-c,q*Complex.sqrt (-c),-q*Complex.sqrt (-c),a,q/a,c,-d,-q/d]
      [Complex.sqrt (-c),-Complex.sqrt (-c),-c*q/a,-a*c,-q,c*q/d,c*d] q c=
      qPochhammerListInf [-c,-c*q] q*qPochhammerListInf [a*c*d,a*c*q/d,c*d*q/a,c*q^2/(a*d)] (q^2)/
        qPochhammerListInf [c*d,c*q/d,-a*c,-c*q/a] q := by
  sorry

/-- A terminating balanced `4φ3` with parameters `q^(-n), q^(n+1), c, -c` summed by infinite
products (DLMF 17.7.E11). -/
@[dlmf 17.7.E11]
theorem four_phi_three_infinite_product {c e q : ℂ} (he : e≠0) (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : QDenominatorRegular [e,c^2*q/e,-q] q) :
    qPhi [q^(-(n:ℤ)),q^(n+1),c,-c] [e,c^2*q/e,-q] q q=
      q^((n+1).choose 2)*qPochhammerListInf [e*q^(-(n:ℤ)),e*q^(n+1),c^2*q^(1-(n:ℤ))/e,c^2*q^(n+2)/e] (q^2)/
        qPochhammerListInf [e,c^2*q/e] q := by
  sorry

/-- The cleared product retains the regular upper parameter a=0. -/
@[dlmf 17.7.E12]
theorem four_phi_three_base_square_first {a b q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : QDenominatorRegularThrough [b,b*q,a^2*q^2] (q^2) n) :
    qPhi [a,a*q,b^2*q^(2*n),q^(-(2*n:ℤ))] [b,b*q,a^2*q^2] (q^2) (q^2)=
      qPochhammer (-q) q n*((range n).prod (fun j => a-b*q^j))/qPochhammerList [-a*q,b] q n := by
  sorry

/-- The n=0 removable quotient is 1, and the cleared product retains a=0. -/
@[dlmf 17.7.E13]
theorem four_phi_three_base_square_second {a b q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : QDenominatorRegularThrough [b,b*q,a^2] (q^2) n) :
    qPhi [a,a*q,b^2*q^(2*(n:ℤ)-2),q^(-(2*n:ℤ))] [b,b*q,a^2] (q^2) (q^2)=
      if n=0 then 1 else qPochhammer (-q) q n*((range n).prod (fun j => a-b*q^j))*(1-b*q^((n:ℤ)-1))/
        (qPochhammerList [-a,b] q n*(1-b*q^(2*(n:ℤ)-1))) := by
  sorry

/-- The very-well-poised factor of an `₈φ₇` term as the unit-Bailey numerator. -/
lemma qbR4_vwp_unitD {a q : ℂ} (k : ℕ) (hk : k = 0 ∨ (a ≠ 1 ∧
    qPochhammer (Complex.sqrt a) q k * qPochhammer (-Complex.sqrt a) q k ≠ 0)) :
    qPochhammer a q k * qPochhammer (q*Complex.sqrt a) q k * qPochhammer (-q*Complex.sqrt a) q k /
      (qPochhammer (Complex.sqrt a) q k * qPochhammer (-Complex.sqrt a) q k) =
    DLMF.Bailey.unitD a q k := by
  rcases hk with rfl | ⟨ha, hk⟩
  · simp [DLMF.Bailey.unitD]
  have hs : (Complex.sqrt a)^2 = a := by
    rw [Complex.sqrt, ← Complex.cpow_nat_mul]; norm_num
  have h1 := DLMF.Bailey.qPochhammer_sqrt_factor (q := q) hs k
  have h2 := DLMF.Bailey.qPochhammer_mul_one_sub_pow a q k
  have h1a : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  rw [div_eq_iff hk]
  apply mul_left_cancel₀ h1a
  linear_combination qPochhammer a q k * h1 + qPochhammer (Complex.sqrt a) q k *
    qPochhammer (-Complex.sqrt a) q k * h2

/-- Jackson's `₈φ₇` terms are the rational terms of Watson's transformation. -/
lemma qbR4_jackson_term {a b c d e q : ℂ} (hq0 : q≠0) (n : ℕ)
    (hbcde : b*c*d*e≠0) (hbal : a^2*q=b*c*d*e*q^(-(n:ℤ))) (k : ℕ)
    (hk : k = 0 ∨ (a ≠ 1 ∧
      qPochhammer (Complex.sqrt a) q k * qPochhammer (-Complex.sqrt a) q k ≠ 0)) :
    qPhiTerm [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e,q^(-(n:ℤ))]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e,a*q^(n+1)] q q k =
    DLMF.Bailey.watsonR8 a b c d e q n k := by
  have hz : a^2*q^2*q^n/(b*c*d*e) = q := by
    rw [div_eq_iff hbcde]
    have : a^2*q = b*c*d*e*q^(-(n:ℤ)) := hbal
    rw [zpow_neg, zpow_natCast] at this
    field_simp at this
    linear_combination q*this
  have hu := qbR4_vwp_unitD k hk
  set R := qPochhammer b q k * qPochhammer c q k * qPochhammer d q k * qPochhammer e q k *
      qPochhammer (q^(-(n:ℤ))) q k / (qPochhammer (a*q/b) q k * qPochhammer (a*q/c) q k *
      qPochhammer (a*q/d) q k * qPochhammer (a*q/e) q k * qPochhammer (a*q^(n+1)) q k *
      qPochhammer q q k) * q^k with hR
  calc _ = qPochhammer a q k * qPochhammer (q*Complex.sqrt a) q k *
        qPochhammer (-q*Complex.sqrt a) q k /
        (qPochhammer (Complex.sqrt a) q k * qPochhammer (-Complex.sqrt a) q k) * R := by
        simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil, hR]
        norm_num
        ring
    _ = _ := by
        rw [hu, hR, DLMF.Bailey.watsonR8, hz, zpow_neg, zpow_natCast, inv_pow,
          show a*q^(n+1) = a*q*q^n by ring]
        ring

/-- Jackson's sum when Watson's balanced `₄φ₃` has a regular cancelled parameter. -/
lemma qbR4_jackson_core {a b c d e q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hb : b≠0) (hc : c≠0) (hd : d≠0) (he : e≠0) (hbal : a^2*q=b*c*d*e*q^(-(n:ℤ)))
    (hS : qPochhammer (Complex.sqrt a) q n * qPochhammer (-Complex.sqrt a) q n ≠ 0)
    (hB : qPochhammer (a*q/b) q n ≠ 0) (hC : qPochhammer (a*q/c) q n ≠ 0)
    (hD : qPochhammer (a*q/d) q n ≠ 0) (hE : qPochhammer (a*q/e) q n ≠ 0)
    (hN : qPochhammer (a*q^(n+1)) q n ≠ 0) (hY : qPochhammer (a*q/(b*c)) q n ≠ 0) :
    ∑ k ∈ range (n+1), qPhiTerm [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e,q^(-(n:ℤ))]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e,a*q^(n+1)] q q k =
    qPochhammerList [a*q,a*q/(b*c),a*q/(b*d),a*q/(c*d)] q n/
        qPochhammerList [a*q/b,a*q/c,a*q/d,a*q/(b*c*d)] q n := by
  have hqn : q^(-(n:ℤ)) ≠ 0 := zpow_ne_zero _ hq0
  have ha : a ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hbal
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hb hc) hd) he) hqn) hbal.symm
  have hbcde : b*c*d*e ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hb hc) hd) he
  -- Step A: the terms are Watson's rational terms
  have hA : ∀ k ∈ range (n+1), qPhiTerm [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e,q^(-(n:ℤ))]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e,a*q^(n+1)] q q k =
      DLMF.Bailey.watsonR8 a b c d e q n k := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    refine qbR4_jackson_term hq0 n hbcde hbal k ?_
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exact Or.inl h0
    · right
      have h1 : qPochhammer (Complex.sqrt a) q k * qPochhammer (-Complex.sqrt a) q k ≠ 0 :=
        mul_ne_zero (qPochhammer_ne_zero_of_le (left_ne_zero_of_mul hS) hkn)
          (qPochhammer_ne_zero_of_le (right_ne_zero_of_mul hS) hkn)
      refine ⟨fun h1a => ?_, h1⟩
      have h2 : qPochhammer (Complex.sqrt a) q 1 * qPochhammer (-Complex.sqrt a) q 1 ≠ 0 :=
        mul_ne_zero (qPochhammer_ne_zero_of_le (left_ne_zero_of_mul hS) (by omega))
          (qPochhammer_ne_zero_of_le (right_ne_zero_of_mul hS) (by omega))
      have hs : (Complex.sqrt a)^2 = a := by
        rw [Complex.sqrt, ← Complex.cpow_nat_mul]; norm_num
      apply h2
      simp only [qPochhammer_one]
      linear_combination -hs - h1a
  have hYeq : d*e*q⁻¹^n/a = a*q/(b*c) := by
    rw [zpow_neg, zpow_natCast] at hbal
    rw [inv_pow]
    field_simp
    field_simp at hbal
    linear_combination -hbal
  have hW := DLMF.Bailey.watsonR n ha hb hc hd he hq0 (fun m _ => qPochhammer_self_ne_zero hq m)
    hB hC hD hE (by rw [hYeq]; exact hY) (by rw [show a*q*q^n = a*q^(n+1) by ring]; exact hN)
  rw [sum_congr rfl hA, hW]
  have hXeq : d*e*q^(1-(n:ℤ))/(a*q/b) = a*q/c := by
    rw [zpow_sub₀ hq0, zpow_one, zpow_natCast]
    rw [zpow_neg, zpow_natCast] at hbal
    field_simp
    field_simp at hbal
    linear_combination -hbal
  have hCs : ∀ k ∈ range (n+1), DLMF.Bailey.watsonR4 a b c d e q n k =
      qbR4SaalTerm d e (a*q/b) q n k := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hYk : qPochhammer (a*q/(b*c)) q k ≠ 0 := qPochhammer_ne_zero_of_le hY hkn
    rw [DLMF.Bailey.watsonR4, hYeq, qbR4SaalTerm, hXeq]
    simp only [zpow_neg, zpow_natCast, inv_pow]
    field_simp
  rw [sum_congr rfl hCs, qbR4_saal_all (div_ne_zero (mul_ne_zero ha hq0) hb) hq0 hq n hB
    (by rw [hXeq]; exact hC), qbR4SaalValue]
  have e2 : a*q/b/e = c*d/a*q^(-(n:ℤ)) := by field_simp; linear_combination hbal
  have e3 : a*q/b/(d*e) = c/a*q^(-(n:ℤ)) := by field_simp; linear_combination hbal
  have e4 : a*q/(d*e) = b*c/a*q^(-(n:ℤ)) := by field_simp; linear_combination hbal
  have e5 : a*q/e = b*c*d/a*q^(-(n:ℤ)) := by field_simp; linear_combination hbal
  rw [qbR4_prod_sub_eq hd, qbR4_prod_sub_eq he, qbR4_prod_sub_eq (mul_ne_zero hd he), e2, e3, e4,
    qPochhammer_shift_negative (div_ne_zero (mul_ne_zero hc hd) ha) hq0,
    qPochhammer_shift_negative (div_ne_zero hc ha) hq0,
    qPochhammer_shift_negative (div_ne_zero (mul_ne_zero hb hc) ha) hq0,
    show a*q/b/d = a*q/(b*d) by ring]
  rw [e5, qPochhammer_shift_negative (div_ne_zero (mul_ne_zero (mul_ne_zero hb hc) hd) ha) hq0]
    at hE
  rw [e5, qPochhammer_shift_negative (div_ne_zero (mul_ne_zero (mul_ne_zero hb hc) hd) ha) hq0]
  have hE' := left_ne_zero_of_mul (left_ne_zero_of_mul hE)
  rw [show q/(c*d/a) = a*q/(c*d) by field_simp, show q/(c/a) = a*q/c by field_simp,
    show q/(b*c/a) = a*q/(b*c) by field_simp, show q/(b*c*d/a) = a*q/(b*c*d) by field_simp] at *
  simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hC0 : q^(-(n.choose 2:ℤ)) ≠ 0 := zpow_ne_zero _ hq0
  simp only [neg_div]
  rw [neg_pow (c*d/a/q), neg_pow (c/a/q), neg_pow (b*c/a/q), neg_pow (b*c*d/a/q)]
  simp only [div_pow, mul_pow]
  have hm1 : ((-1:ℂ))^n ≠ 0 := pow_ne_zero _ (by norm_num)
  generalize qPochhammer (a*q) q n = P1 at *
  generalize qPochhammer (a*q/(b*c)) q n = P2 at *
  generalize qPochhammer (a*q/d) q n = P3 at *
  generalize qPochhammer (a*q/(b*c*d)) q n = P4 at *
  generalize qPochhammer (a*q/(b*d)) q n = P5 at *
  generalize qPochhammer (a*q/(c*d)) q n = P6 at *
  generalize qPochhammer (a*q/b) q n = P7 at *
  generalize qPochhammer (a*q/c) q n = P8 at *
  generalize q^(-(n.choose 2:ℤ)) = Z at *
  generalize ((-1:ℂ))^n = M at *
  field_simp

/-- Away from one point, `1 - X/t` has no zeros near a nonzero point. -/
lemma qbR4_eventually_one_sub_div_ne (X b : ℂ) (hb : b ≠ 0) :
    ∀ᶠ t in 𝓝[≠] b, 1 - X/t ≠ 0 := by
  by_cases h : 1 - X/b = 0
  · have hX : X = b := by field_simp at h; linear_combination -h
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_ne_nhds hb)] with t ht ht0
    rw [hX]
    intro h'
    apply ht
    rw [Set.mem_singleton_iff]
    field_simp at h'
    linear_combination h'
  · have hc : ContinuousAt (fun t : ℂ => 1 - X/t) b := by fun_prop (disch := exact hb)
    exact nhdsWithin_le_nhds (hc.eventually_ne h)

/-- `(aq/(tc);q)_n` is nonzero for `t` near, but distinct from, a nonzero point. -/
lemma qbR4_eventually_qPochhammer_ne (a c q b : ℂ) (n : ℕ) (hb : b ≠ 0) :
    ∀ᶠ t in 𝓝[≠] b, qPochhammer (a*q/(t*c)) q n ≠ 0 := by
  have h := (Finset.eventually_all (range n)).mpr fun j _ =>
    qbR4_eventually_one_sub_div_ne (a*q*q^j/c) b hb
  filter_upwards [h, nhdsWithin_le_nhds (eventually_ne_nhds hb)] with t ht ht0
  rw [qPochhammer_eq_prod, prod_ne_zero_iff]
  intro j hj
  have := ht j hj
  by_cases hc : c = 0
  · simp [hc]
  · convert this using 2; field_simp

/-- Nonvanishing of a list of shifted factorials passes to shorter lengths. -/
lemma qbR4_qPochhammerList_ne_zero_of_le {q : ℂ} {k n : ℕ} (hk : k ≤ n) :
    ∀ l : List ℂ, qPochhammerList l q n ≠ 0 → qPochhammerList l q k ≠ 0
  | [], _ => by simp [qPochhammerList]
  | x :: l, h => by
    simp only [qPochhammerList, List.map_cons, List.prod_cons] at h ⊢
    exact mul_ne_zero (qPochhammer_ne_zero_of_le (left_ne_zero_of_mul h) hk)
      (qbR4_qPochhammerList_ne_zero_of_le hk l (right_ne_zero_of_mul h))

/-- In Jackson's sum, `(aq/(bcd);q)_n ≠ 0` follows from `(aq/e;q)_n ≠ 0` by the balance. -/
lemma qbR4_jackson_bcd_ne {a b c d e q : ℂ} (hq0 : q≠0) (n : ℕ) (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hd : d≠0) (he : e≠0) (hbal : a^2*q=b*c*d*e*q^(-(n:ℤ))) (hE : qPochhammer (a*q/e) q n ≠ 0) :
    qPochhammer (a*q/(b*c*d)) q n ≠ 0 := by
  have e5 : a*q/e = b*c*d/a*q^(-(n:ℤ)) := by field_simp; linear_combination hbal
  rw [e5, qPochhammer_shift_negative (div_ne_zero (mul_ne_zero (mul_ne_zero hb hc) hd) ha) hq0,
    show q/(b*c*d/a) = a*q/(b*c*d) by field_simp] at hE
  exact left_ne_zero_of_mul (left_ne_zero_of_mul hE)

/-- Jackson's terminating very-well-poised balanced `8φ7` summation (DLMF 17.7.E14). -/
@[dlmf 17.7.E14]
theorem jackson_eight_phi_seven {a b c d e q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hbcd : b*c*d≠0) (he : e≠0) (hbal : a^2*q=b*c*d*e*q^(-(n:ℤ)))
    (hd : QDenominatorRegularThrough [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e,a*q^(n+1)] q n) :
    qPhi [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e,q^(-(n:ℤ))]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e,a*q^(n+1)] q q=
      qPochhammerList [a*q,a*q/(b*c),a*q/(b*d),a*q/(c*d)] q n/
        qPochhammerList [a*q/b,a*q/c,a*q/d,a*q/(b*c*d)] q n := by
  have hb : b ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hc : c ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hd0 : d ≠ 0 := right_ne_zero_of_mul hbcd
  have hqn : q^(-(n:ℤ)) ≠ 0 := zpow_ne_zero _ hq0
  have ha : a ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hbal
    exact (mul_ne_zero (mul_ne_zero hbcd he) hqn) hbal.symm
  have hdd := hd
  simp only [QDenominatorRegularThrough, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, ne_eq, mul_eq_zero, not_or] at hdd
  obtain ⟨hS1, hS2, hB, hC, hD, hE, hN⟩ := hdd
  rw [qbR4_qPhi_eq_sum_of_mem hq0 n (by simp)]
  by_cases hY : qPochhammer (a*q/(b*c)) q n ≠ 0
  · exact qbR4_jackson_core hq0 hq n hb hc hd0 he hbal (mul_ne_zero hS1 hS2) hB hC hD hE hN hY
  set E : ℂ → ℂ := fun t => a^2*q*q^n/(t*c*d) with hEdef
  have hEb : e = E b := by
    simp only [hEdef]
    rw [zpow_neg, zpow_natCast] at hbal
    field_simp
    field_simp at hbal
    linear_combination -hbal
  have hE0 : ∀ t, t ≠ 0 → E t ≠ 0 := fun t ht => by
    simp only [hEdef]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) hq0) (pow_ne_zero n hq0))
      (mul_ne_zero (mul_ne_zero ht hc) hd0)
  have hbalE : ∀ t, t ≠ 0 → a^2*q = t*c*d*E t*q^(-(n:ℤ)) := fun t ht => by
    simp only [hEdef, zpow_neg, zpow_natCast]
    field_simp
  subst hEb
  have hbcd' : b*c*d ≠ 0 := hbcd
  set g : ℂ → ℂ := fun t => (∑ k ∈ range (n+1),
      qPhiTerm [a,q*Complex.sqrt a,-q*Complex.sqrt a,t,c,d,E t,q^(-(n:ℤ))]
        [Complex.sqrt a,-Complex.sqrt a,a*q/t,a*q/c,a*q/d,a*q/E t,a*q^(n+1)] q q k) -
      qPochhammerList [a*q,a*q/(t*c),a*q/(t*d),a*q/(c*d)] q n/
        qPochhammerList [a*q/t,a*q/c,a*q/d,a*q/(t*c*d)] q n with hgdef
  suffices g b = 0 by simpa [hgdef, sub_eq_zero] using this
  have hcore : ∀ t, t ≠ 0 → qPochhammer (a*q/t) q n ≠ 0 → qPochhammer (a*q/E t) q n ≠ 0 →
      qPochhammer (a*q/(t*c)) q n ≠ 0 → g t = 0 := by
    intro t ht hBt hEt hYt
    simp only [hgdef, sub_eq_zero]
    exact qbR4_jackson_core hq0 hq n ht hc hd0 (hE0 t ht) (hbalE t ht) (mul_ne_zero hS1 hS2) hBt hC
      hD hEt hN hYt
  have hEc : ContinuousAt E b := by simp only [hEdef]; fun_prop (disch := exact hbcd')
  have hEb0 := hE0 b hb
  have hBc : ContinuousAt (fun t : ℂ => qPochhammer (a*q/t) q n) b := by
    fun_prop (disch := exact hb)
  have hEtc : ContinuousAt (fun t : ℂ => qPochhammer (a*q/E t) q n) b := by
    fun_prop (disch := exact hEb0)
  have hev : g =ᶠ[𝓝[≠] b] fun _ => 0 := by
    filter_upwards [nhdsWithin_le_nhds (eventually_ne_nhds hb),
      nhdsWithin_le_nhds (hBc.eventually_ne hB), nhdsWithin_le_nhds (hEtc.eventually_ne hE),
      qbR4_eventually_qPochhammer_ne a c q b n hb] with t h1 h2 h3 h4
    exact hcore t h1 h2 h3 h4
  have hbcdn := qbR4_jackson_bcd_ne hq0 n ha hb hc hd0 hEb0 hbal hE
  have hg : ContinuousAt g b := by
    simp only [hgdef]
    refine ContinuousAt.sub ?_ ?_
    · refine tendsto_finsetSum _ fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
      have hU := qbR4_qPochhammerList_ne_zero_of_le hkn _ hd
      have hden : qPochhammerList [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/E b,
          a*q^(n+1)] q k * qPochhammer q q k ≠ 0 := mul_ne_zero hU (qPochhammer_self_ne_zero hq k)
      have hform : (fun t => qPhiTerm [a,q*Complex.sqrt a,-q*Complex.sqrt a,t,c,d,E t,q^(-(n:ℤ))]
          [Complex.sqrt a,-Complex.sqrt a,a*q/t,a*q/c,a*q/d,a*q/E t,a*q^(n+1)] q q k) =
          fun t => qPochhammerList [a,q*Complex.sqrt a,-q*Complex.sqrt a,t,c,d,E t,q^(-(n:ℤ))] q k /
            (qPochhammerList [Complex.sqrt a,-Complex.sqrt a,a*q/t,a*q/c,a*q/d,a*q/E t,a*q^(n+1)]
              q k * qPochhammer q q k) * q^k := by
        funext t
        simp only [qPhiTerm, qPhiExponent, List.length_cons, List.length_nil]
        norm_num
      show ContinuousAt (fun t => qPhiTerm [a,q*Complex.sqrt a,-q*Complex.sqrt a,t,c,d,E t,
        q^(-(n:ℤ))] [Complex.sqrt a,-Complex.sqrt a,a*q/t,a*q/c,a*q/d,a*q/E t,a*q^(n+1)] q q k) b
      rw [hform]
      refine ContinuousAt.mul (ContinuousAt.div ?_ ?_ hden) continuousAt_const
      · simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
        fun_prop
      · simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
        fun_prop (disch := first | exact hb | exact hEb0)
    · have hden : qPochhammerList [a*q/b,a*q/c,a*q/d,a*q/(b*c*d)] q n ≠ 0 := by
        simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one]
        exact mul_ne_zero hB (mul_ne_zero hC (mul_ne_zero hD hbcdn))
      refine ContinuousAt.div ?_ ?_ hden
      · simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
        fun_prop (disch := first | exact hb | exact mul_ne_zero hb hc | exact mul_ne_zero hb hd0)
      · simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
        fun_prop (disch := first | exact hb | exact hbcd')
  have h1 : Tendsto g (𝓝[≠] b) (𝓝 (g b)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' hev.symm)

/-- The nonterminating very-well-poised `6φ5` summation (DLMF 17.7.E15). -/
@[dlmf 17.7.E15]
theorem six_phi_five_sum {a b c d q : ℂ} (hq : ‖q‖<1) (hz : ‖a*q‖<‖b*c*d‖)
    (hd : QDenominatorRegular [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d] q) :
    qPhi [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d] q (a*q/(b*c*d))=
      qPochhammerListInf [a*q,a*q/(b*c),a*q/(b*d),a*q/(c*d)] q/
        qPochhammerListInf [a*q/b,a*q/c,a*q/d,a*q/(b*c*d)] q := by
  sorry

/-- The rational terms of the terminating very-well-poised `₆φ₅` sum. -/
def qbR4SixTerm (a b c q : ℂ) (n k : ℕ) : ℂ :=
  DLMF.Bailey.unitD a q k * (qPochhammer b q k * qPochhammer c q k * qPochhammer (q^(-(n:ℤ))) q k) /
    (qPochhammer (a*q/b) q k * qPochhammer (a*q/c) q k * qPochhammer (a*q^(n+1)) q k *
      qPochhammer q q k) * (a*q^(n+1)/(b*c))^k

/-- The terminating `₆φ₅` sum in rational form when `(aq;q)_{2n} ≠ 0`, from Bailey's lemma. -/
lemma qbR4_six_rational_of_ne {a b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ) (hb : b≠0) (hc : c≠0)
    (hB : qPochhammer (a*q/b) q n ≠ 0) (hC : qPochhammer (a*q/c) q n ≠ 0)
    (haq : qPochhammer (a*q) q (n+n) ≠ 0) :
    ∑ k ∈ range (n+1), qbR4SixTerm a b c q n k =
      qPochhammer (a*q) q n * qPochhammer (a*q/(b*c)) q n /
        (qPochhammer (a*q/b) q n * qPochhammer (a*q/c) q n) := by
  have hqq : ∀ m, qPochhammer q q m ≠ 0 := qPochhammer_self_ne_zero hq
  have h := DLMF.Bailey.bailey_relation (a := a) (q := q) (n := n) (rho1 := b) (rho2 := c)
    (α := DLMF.Bailey.unitAlpha a q) (β := fun k => if k = 0 then 1 else 0)
    (fun k hk => DLMF.Bailey.unit_pair a q k (fun m _ => hqq m)
      (qPochhammer_ne_zero_of_le haq (by omega))) hb hc (fun m _ => hqq m) haq hB hC
  rw [Finset.sum_eq_single 0 (fun k _ hk => by simp [hk]) (by simp)] at h
  have han : qPochhammer (a*q) q n ≠ 0 := qPochhammer_ne_zero_of_le haq (by omega)
  have key : ∀ k ∈ range (n+1), qPochhammer b q k * qPochhammer c q k *
      (a*q/(b*c))^k * DLMF.Bailey.unitAlpha a q k / (qPochhammer (a*q/b) q k *
        qPochhammer (a*q/c) q k) / (qPochhammer q q (n-k) * qPochhammer (a*q) q (n+k)) =
      qbR4SixTerm a b c q n k / (qPochhammer q q n * qPochhammer (a*q) q n) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hQp : q^(1-(n:ℤ))/q = q^(-(n:ℤ)) := by
      rw [zpow_sub₀ hq0, zpow_one, zpow_neg]; field_simp
    have hNm : qPochhammer (q^(-(n:ℤ))) q k ≠ 0 := qbR4_qPochhammer_neg_ne_zero hq0 hq hkn
    have h2 := qPochhammer_sub_index hq0 hq0 hkn (by rw [hQp]; exact hNm)
    rw [hQp] at h2
    have h3 := qPochhammer_add (a*q) q n k
    rw [show a*q*q^n = a*q^(n+1) by ring] at h3
    have hBk := qPochhammer_ne_zero_of_le hB hkn
    have hCk := qPochhammer_ne_zero_of_le hC hkn
    have hNk : qPochhammer (a*q^(n+1)) q k ≠ 0 := by
      intro h0; apply haq
      rw [show n+n = (n+k) + (n-k) by omega, qPochhammer_add, h3, h0]; simp
    rw [h2, h3, DLMF.Bailey.unitAlpha, qbR4SixTerm,
      show (-q/q) = -1 by field_simp]
    have hE : q^((k.choose 2:ℤ)-(n:ℤ)*k) = q^(k.choose 2) / q^(n*k) := by
      rw [zpow_sub₀ hq0]; norm_cast
    rw [hE]
    have hm1 : ((-1:ℂ))^k ≠ 0 := pow_ne_zero _ (by norm_num)
    have hqk := hqq k
    have hc2 : q^(k.choose 2) ≠ 0 := pow_ne_zero _ hq0
    have hnk : q^(n*k) ≠ 0 := pow_ne_zero _ hq0
    simp only [div_pow, mul_pow, ← pow_mul]
    rw [show (n+1)*k = n*k + k by ring, pow_add]
    field_simp
    ring
  rw [sum_congr rfl key, ← sum_div] at h
  simp only [ite_true, pow_zero, mul_one, Nat.sub_zero, qPochhammer_zero, one_mul] at h
  have hqn := hqq n
  rw [eq_div_iff (mul_ne_zero hqn han)] at h
  rw [← h]
  field_simp

/-- Away from one point, `1 - tX` has no zeros near any point. -/
lemma qbR4_eventually_one_sub_mul_ne (X a : ℂ) : ∀ᶠ t in 𝓝[≠] a, 1 - t*X ≠ 0 := by
  by_cases h : 1 - a*X = 0
  · filter_upwards [self_mem_nhdsWithin] with t ht h'
    apply ht
    rw [Set.mem_singleton_iff]
    have hX : X ≠ 0 := by rintro rfl; simp at h
    apply mul_right_cancel₀ hX
    linear_combination h - h'
  · have hc : ContinuousAt (fun t : ℂ => 1 - t*X) a := by fun_prop
    exact nhdsWithin_le_nhds (hc.eventually_ne h)

attribute [local fun_prop] DLMF.Bailey.continuous_unitD

/-- The terminating `₆φ₅` sum in rational form for every regular `a`. -/
lemma qbR4_six_rational {a b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ) (hb : b≠0) (hc : c≠0)
    (hB : qPochhammer (a*q/b) q n ≠ 0) (hC : qPochhammer (a*q/c) q n ≠ 0)
    (hN : qPochhammer (a*q^(n+1)) q n ≠ 0) :
    ∑ k ∈ range (n+1), qbR4SixTerm a b c q n k =
      qPochhammer (a*q) q n * qPochhammer (a*q/(b*c)) q n /
        (qPochhammer (a*q/b) q n * qPochhammer (a*q/c) q n) := by
  set g : ℂ → ℂ := fun t => ∑ k ∈ range (n+1), qbR4SixTerm t b c q n k -
    qPochhammer (t*q) q n * qPochhammer (t*q/(b*c)) q n /
        (qPochhammer (t*q/b) q n * qPochhammer (t*q/c) q n) with hgdef
  suffices g a = 0 by simpa [hgdef, sub_eq_zero] using this
  have hBc : ContinuousAt (fun t : ℂ => qPochhammer (t*q/b) q n) a := by fun_prop
  have hCc : ContinuousAt (fun t : ℂ => qPochhammer (t*q/c) q n) a := by fun_prop
  have hNc : ContinuousAt (fun t : ℂ => qPochhammer (t*q^(n+1)) q n) a := by fun_prop
  have hev : g =ᶠ[𝓝[≠] a] fun _ => 0 := by
    have hA := (Finset.eventually_all (range (n+n))).mpr fun j _ =>
      qbR4_eventually_one_sub_mul_ne (q*q^j) a
    filter_upwards [nhdsWithin_le_nhds (hBc.eventually_ne hB),
      nhdsWithin_le_nhds (hCc.eventually_ne hC), hA] with t h1 h2 h3
    simp only [hgdef, sub_eq_zero]
    refine qbR4_six_rational_of_ne hq0 hq n hb hc h1 h2 ?_
    rw [qPochhammer_eq_prod, prod_ne_zero_iff]
    intro j hj
    have := h3 j hj
    rwa [show t*q*q^j = t*(q*q^j) by ring]
  have hg : ContinuousAt g a := by
    simp only [hgdef]
    refine ContinuousAt.sub ?_ ?_
    · refine tendsto_finsetSum _ fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
      have hden : qPochhammer (a*q/b) q k * qPochhammer (a*q/c) q k * qPochhammer (a*q^(n+1)) q k *
          qPochhammer q q k ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (qPochhammer_ne_zero_of_le hB hkn)
          (qPochhammer_ne_zero_of_le hC hkn)) (qPochhammer_ne_zero_of_le hN hkn))
          (qPochhammer_self_ne_zero hq k)
      have hbc : b*c ≠ 0 := mul_ne_zero hb hc
      show ContinuousAt (fun t => qbR4SixTerm t b c q n k) a
      simp only [qbR4SixTerm]
      fun_prop (disch := first | exact hden | exact hbc)
    · fun_prop (disch := first | exact mul_ne_zero hB hC | exact hb | exact hc | exact mul_ne_zero hb hc)
  have h1 : Tendsto g (𝓝[≠] a) (𝓝 (g a)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' hev.symm)

/-- The terminating very-well-poised `6φ5` summation with upper parameter `q^(-n)` (DLMF
17.7.E16). -/
@[dlmf 17.7.E16]
theorem six_phi_five_terminating {a b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ) (hbc : b*c≠0)
    (hd : QDenominatorRegularThrough [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q^(n+1)] q n) :
    qPhi [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,q^(-(n:ℤ))]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q^(n+1)] q (a*q^(n+1)/(b*c))=
      qPochhammerList [a*q,a*q/(b*c)] q n/qPochhammerList [a*q/b,a*q/c] q n := by
  have hb : b ≠ 0 := left_ne_zero_of_mul hbc
  have hc : c ≠ 0 := right_ne_zero_of_mul hbc
  have hdd := hd
  simp only [QDenominatorRegularThrough, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, ne_eq, mul_eq_zero, not_or] at hdd
  obtain ⟨hS1, hS2, hB, hC, hN⟩ := hdd
  rw [qbR4_qPhi_eq_sum_of_mem hq0 n (by simp)]
  have hterm : ∀ k ∈ range (n+1), qPhiTerm [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,q^(-(n:ℤ))]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q^(n+1)] q (a*q^(n+1)/(b*c)) k =
      qbR4SixTerm a b c q n k := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hk' : k = 0 ∨ (a ≠ 1 ∧
        qPochhammer (Complex.sqrt a) q k * qPochhammer (-Complex.sqrt a) q k ≠ 0) := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · exact Or.inl h0
      · right
        refine ⟨fun h1a => ?_, mul_ne_zero (qPochhammer_ne_zero_of_le hS1 hkn)
          (qPochhammer_ne_zero_of_le hS2 hkn)⟩
        have h2 : qPochhammer (Complex.sqrt a) q 1 * qPochhammer (-Complex.sqrt a) q 1 ≠ 0 :=
          mul_ne_zero (qPochhammer_ne_zero_of_le hS1 (by omega))
            (qPochhammer_ne_zero_of_le hS2 (by omega))
        have hs : (Complex.sqrt a)^2 = a := by
          rw [Complex.sqrt, ← Complex.cpow_nat_mul]; norm_num
        apply h2
        simp only [qPochhammer_one]
        linear_combination -hs - h1a
    have hu := qbR4_vwp_unitD k hk'
    calc _ = qPochhammer a q k * qPochhammer (q*Complex.sqrt a) q k *
          qPochhammer (-q*Complex.sqrt a) q k /
          (qPochhammer (Complex.sqrt a) q k * qPochhammer (-Complex.sqrt a) q k) *
          ((qPochhammer b q k * qPochhammer c q k * qPochhammer (q^(-(n:ℤ))) q k) /
          (qPochhammer (a*q/b) q k * qPochhammer (a*q/c) q k * qPochhammer (a*q^(n+1)) q k *
            qPochhammer q q k) * (a*q^(n+1)/(b*c))^k) := by
          simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
            List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil]
          norm_num
          ring
      _ = _ := by rw [hu, qbR4SixTerm]; ring
  rw [sum_congr rfl hterm, qbR4_six_rational hq0 hq n hb hc hB hC hN]
  simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

/-- The nonterminating very-well-poised balanced `8φ7` summation (DLMF 17.7.E17). -/
@[dlmf 17.7.E17]
theorem nonterminating_eight_phi_seven {a b c d e f q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (habcdef : a*b*c*d*e*f≠0) (hbal : q*a^2=b*c*d*e*f)
    (hd : QDenominatorRegular [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e,a*q/f,
      b/Complex.sqrt a,-b/Complex.sqrt a,b*q/a,b*q/c,b*q/d,b*q/e,b*q/f,
      b*c/a,b*d/a,b*e/a,b*f/a,b^2*q/a] q) :
    qPhi [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e,f]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e,a*q/f] q q-
      b/a*qPochhammerListInf [a*q,c,d,e,f,b*q/a,b*q/c,b*q/d,b*q/e,b*q/f] q/
        qPochhammerListInf [a*q/b,a*q/c,a*q/d,a*q/e,a*q/f,b*c/a,b*d/a,b*e/a,b*f/a,b^2*q/a] q*
        qPhi [b^2/a,q*b/Complex.sqrt a,-q*b/Complex.sqrt a,b,b*c/a,b*d/a,b*e/a,b*f/a]
          [b/Complex.sqrt a,-b/Complex.sqrt a,b*q/a,b*q/c,b*q/d,b*q/e,b*q/f] q q=
      qPochhammerListInf [a*q,b/a,a*q/(c*d),a*q/(c*e),a*q/(c*f),a*q/(d*e),a*q/(d*f),a*q/(e*f)] q/
        qPochhammerListInf [a*q/c,a*q/d,a*q/e,a*q/f,b*c/a,b*d/a,b*e/a,b*f/a] q := by
  sorry

/-- The cleared finite product includes b=0 without a spurious0 times infinity. -/
@[dlmf 17.7.E18]
theorem q_karlsson_minton {a b q : ℂ} (ha : a≠0) (hq0 : q≠0) (hq : ‖q‖<1) (p : List (ℂ × ℕ))
    (hz : ‖a⁻¹*q^(1-(qMintonWeight p:ℤ))‖<1)
    (hd : QDenominatorRegular (b*q::qMintonLower p) q) :
    qPhi (a::b::qMintonUpper p q) (b*q::qMintonLower p) q (a⁻¹*q^(1-(qMintonWeight p:ℤ)))=
      qPochhammerListInf [q,b*q/a] q/qPochhammerListInf [b*q,q/a] q*
      (p.map (fun x => (range x.2).prod (fun j => b-x.1*q^j))).prod/
        (p.map fun x => qPochhammer x.1 q x.2).prod := by
  sorry

/-- The primary-source argument is q^(−Σm)/a; the printed extra q is disproved below. -/
@[dlmf 17.7.E19]
theorem q_karlsson_minton_zero_corrected {a q : ℂ} (ha : a≠0) (hq0 : q≠0) (hq : ‖q‖<1) (p : List (ℂ × ℕ))
    (hz : ‖a⁻¹*q^(-(qMintonWeight p:ℤ))‖<1) (hd : QDenominatorRegular (qMintonLower p) q) :
    qPhi (a::qMintonUpper p q) (qMintonLower p) q (a⁻¹*q^(-(qMintonWeight p:ℤ)))=0 := by
  sorry

/-- Gosper's bibasic summation of a finite series in the two bases `p` and `q` (DLMF 17.7.E20). -/
@[dlmf 17.7.E20]
theorem bibasic_gosper {a c p q : ℂ} (ha : a≠1) (hc : c≠0) (n : ℕ)
    (hd : qPochhammer q q n*qPochhammer (a*p/c) p n≠0) :
    (∑ k∈range (n+1), (1-a*p^k*q^k)/(1-a)*qPochhammer a p k*qPochhammer c q k/
      (qPochhammer q q k*qPochhammer (a*p/c) p k)*c^(-(k:ℤ)))=
      qPochhammer (a*p) p n*qPochhammer (c*q) q n/
        (qPochhammer q q n*qPochhammer (a*p/c) p n)*c^(-(n:ℤ)) := by
  have h1a : 1-a≠0 := sub_ne_zero.mpr (Ne.symm ha)
  induction n with
  | zero => simp; field_simp; exact h1a
  | succ n ih =>
    have hq1 := qPochhammer_ne_zero_of_le (left_ne_zero_of_mul hd) (Nat.le_succ n)
    have hp1 := qPochhammer_ne_zero_of_le (right_ne_zero_of_mul hd) (Nat.le_succ n)
    rw [sum_range_succ, ih (mul_ne_zero hq1 hp1)]
    rw [qPochhammer_succ] at hd
    have e1 : 1 - q*q^n ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hd)
    have e2 : 1 - a*p/c*p^n ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul hd)
    rw [qPochhammer_succ' a, qPochhammer_succ' c, qPochhammer_succ (a*p), qPochhammer_succ (c*q),
      qPochhammer_succ q q n, qPochhammer_succ (a*p/c) p n]
    have e3 : c - a*p*p^n ≠ 0 := by
      intro h; apply e2; field_simp; linear_combination h
    simp only [zpow_neg, zpow_natCast]
    field_simp
    ring

/-- Gasper's bibasic summation of a finite series in the two bases `p` and `q` (DLMF 17.7.E21). -/
@[dlmf 17.7.E21]
theorem bibasic_gasper {a b c p q : ℂ} (ha : a≠1) (hb : b≠1) (hbc : b*c≠0) (hq : q≠0) (n : ℕ)
    (hd : qPochhammerList [q,a*q/b] q n*qPochhammerList [a*p/c,b*c*p] p n≠0) :
    (∑ k∈range (n+1), (1-a*p^k*q^k)*(1-b*p^k*q^(-(k:ℤ)))/((1-a)*(1-b))*
      qPochhammerList [a,b] p k*qPochhammerList [c,a/(b*c)] q k/
        (qPochhammerList [q,a*q/b] q k*qPochhammerList [a*p/c,b*c*p] p k)*q^k)=
      qPochhammerList [a*p,b*p] p n*qPochhammerList [c*q,a*q/(b*c)] q n/
        (qPochhammerList [q,a*q/b] q n*qPochhammerList [a*p/c,b*c*p] p n) := by
  have h1a : 1-a≠0 := sub_ne_zero.mpr (Ne.symm ha)
  have h1b : 1-b≠0 := sub_ne_zero.mpr (Ne.symm hb)
  have hb0 : b ≠ 0 := left_ne_zero_of_mul hbc
  have hc0 : c ≠ 0 := right_ne_zero_of_mul hbc
  simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one] at hd ⊢
  induction n with
  | zero => simp; field_simp; exact ⟨h1a, h1b⟩
  | succ n ih =>
    simp only [qPochhammer_succ] at hd
    have f1 : qPochhammer q q n ≠ 0 := by intro h; apply hd; simp [h]
    have f2 : qPochhammer (a*q/b) q n ≠ 0 := by intro h; apply hd; simp [h]
    have f3 : qPochhammer (a*p/c) p n ≠ 0 := by intro h; apply hd; simp [h]
    have f4 : qPochhammer (b*c*p) p n ≠ 0 := by intro h; apply hd; simp [h]
    have g1 : 1 - q*q^n ≠ 0 := by intro h; apply hd; simp [h]
    have g2 : b - a*q*q^n ≠ 0 := by
      intro h; apply hd
      have : 1 - a*q/b*q^n = 0 := by field_simp; linear_combination h
      simp [this]
    have g3 : c - a*p*p^n ≠ 0 := by
      intro h; apply hd
      have : 1 - a*p/c*p^n = 0 := by field_simp; linear_combination h
      simp [this]
    have g4 : 1 - b*c*p*p^n ≠ 0 := by intro h; apply hd; simp [h]
    rw [sum_range_succ, ih (by simp [f1, f2, f3, f4])]
    rw [qPochhammer_succ' a, qPochhammer_succ' b, qPochhammer_succ' c, qPochhammer_succ' (a/(b*c)),
      qPochhammer_succ (a*p), qPochhammer_succ (b*p), qPochhammer_succ (c*q),
      qPochhammer_succ (a*q/(b*c)), qPochhammer_succ q q n, qPochhammer_succ (a*q/b) q n,
      qPochhammer_succ (a*p/c) p n, qPochhammer_succ (b*c*p) p n]
    rw [show a/(b*c)*q = a*q/(b*c) by ring]
    have g5 : q^n ≠ 0 := pow_ne_zero n hq
    have g4' : 1 - p*b*c*p^n ≠ 0 := by rw [show p*b*c = b*c*p by ring]; exact g4
    have f4' : qPochhammer (p*b*c) p n ≠ 0 := by rw [show p*b*c = b*c*p by ring]; exact f4
    simp only [zpow_neg, zpow_natCast]
    field_simp
    ring

/-- A bilateral finite bibasic summation over the indices `-m ≤ k ≤ n` (DLMF 17.7.E22). -/
@[dlmf 17.7.E22]
theorem bibasic_bilateral_finite {a b c d p q : ℂ} (hbc : b*c≠0) (hp : p≠0) (hq : q≠0) (m n : ℕ)
    (hP : d*(1-a*d)*(1-b/d)*(1-c/d)*(1-a*d/(b*c))≠0)
    (hF : ∀ k∈Finset.Icc (-(m:ℤ)) (n:ℤ),
      QIntPochhammerListDefined [a,b] p k ∧ QIntPochhammerListDefined [c,a*d^2/(b*c)] q k ∧
      QIntPochhammerListDefined [d*q,a*d*q/b] q k ∧ QIntPochhammerListDefined [a*d*p/c,b*c*p/d] p k ∧
      qPochhammerListInt [d*q,a*d*q/b] q k*qPochhammerListInt [a*d*p/c,b*c*p/d] p k≠0)
    (hR : qPochhammerList [1/c,b*c/(a*d^2)] q (m+1)*qPochhammerList [1/a,1/b] p (m+1)≠0) :
    (∑ k∈Finset.Icc (-(m:ℤ)) (n:ℤ), (1-a*d*p^k*q^k)*(1-b*p^k/(d*q^k))/((1-a*d)*(1-b/d))*
      qPochhammerListInt [a,b] p k*qPochhammerListInt [c,a*d^2/(b*c)] q k/
        (qPochhammerListInt [d*q,a*d*q/b] q k*qPochhammerListInt [a*d*p/c,b*c*p/d] p k)*q^k)=
      (1-a)*(1-b)*(1-c)*(1-a*d^2/(b*c))/(d*(1-a*d)*(1-b/d)*(1-c/d)*(1-a*d/(b*c)))*
      (qPochhammerList [a*p,b*p] p n*qPochhammerList [c*q,a*d^2*q/(b*c)] q n/
        (qPochhammerList [d*q,a*d*q/b] q n*qPochhammerList [a*d*p/c,b*c*p/d] p n)-
       qPochhammerList [c/(a*d),d/(b*c)] p (m+1)*qPochhammerList [1/d,b/(a*d)] q (m+1)/
        (qPochhammerList [1/c,b*c/(a*d^2)] q (m+1)*qPochhammerList [1/a,1/b] p (m+1))) := by
  sorry

/-- Gasper1995(4.1.23), with p and q swapped, gives both corrected denominator entries. -/
@[dlmf 17.7.E23]
theorem bibasic_difference_corrected {a b p q : ℂ} (hb : b≠0) (hp : p≠0) (hq : q≠0) (n : ℕ)
    (h0 : n=0 → a≠q ∧ b≠q)
    (hP : qPochhammer p p n≠0)
    (hD : ∀ k≤n, qPochhammer (a*p^k/b) p (n+1)≠0) :
    (1-a/q)*(1-b/q)*(∑ k∈range (n+1), qPochhammerListInt [a*p^k,b*p^(-(k:ℤ))] q ((n:ℤ)-1)*
      (1-a*p^(2*k)/b)/(qPochhammer p p k*qPochhammer p p (n-k)*qPochhammer (a*p^k/b) p (n+1))*
      (-1:ℂ)^k*p^(k.choose 2))=(if n=0 then 1 else 0) := by
  sorry

/-- The printed argument in 17.7.19 gives a nonzero terminating series. -/
@[dlmf 17.7.E19]
theorem karlsson_printed_counter : qPhi [2] [] (1/2) (1/4)=(1/2:ℂ) := by
  have hzero (k : ℕ) (hk : 2≤k) : qPochhammer (2:ℂ) (1/2) k=0 := by
    have h := qPochhammer_recip_pow_eq_zero (q := (1/2:ℂ)) (by norm_num) (n := 1) (k := k) (by omega)
    norm_num at h
    exact h
  rw [qPhi_eq_basicHG (by simp)]
  unfold basicHG
  rw [tsum_eq_sum (s := range 2) (fun k hk => by
    have h := hzero k (by simp only [Finset.mem_range, not_lt] at hk; exact hk)
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,h,zero_div,zero_mul])]
  norm_num [sum_range_succ, qPochhammer]

/-- The expression printed in 17.7.23, before the primary-source corrections. -/
def bibasicDifferencePrinted (p q a b : ℂ) (n : ℕ) : ℂ :=
  (1-a/q)*(1-b/q)*∑ k∈range (n+1),
    qPochhammerListInt [a*p^k,b*p^(-(k:ℤ))] q ((n:ℤ)-1)*(1-a*p^(2*k)/b)/
      (qPochhammer p p n*qPochhammer p p (n-k)*qPochhammer (a*p^k/b) q (n+1))*
      (-1:ℂ)^k*p^(k.choose 2)

/-- An exact nonzero value disproving the printed n=1 delta identity. -/
@[dlmf 17.7.E23]
theorem bibasic_printed_counter :
    bibasicDifferencePrinted (1/2) (1/3) (1/4) 1 1= -(1884/1771:ℂ) := by
  norm_num [bibasicDifferencePrinted, sum_range_succ, qPochhammerListInt,
    qPochhammerInt, qPochhammer]

end DLMF.QHypergeometric
