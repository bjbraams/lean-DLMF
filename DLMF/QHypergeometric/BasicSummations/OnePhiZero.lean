/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Calculus
public import DLMFMathlib.Analysis.Complex.GeometricNewtonSeries
public import DLMFMathlib.Analysis.Complex.SeparatingContour
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# The q-binomial theorem and the continuation of one-phi-zero (DLMF §17.5)

The q-binomial theorem `₁φ₀(a;—;q,z) = (az;q)_∞/(z;q)_∞` with its terminating and
`a = 0` cases, the product quotient `qOnePhiZeroContinuation` as the meromorphic continuation,
and the q-derivative and shift identities for `₂φ₁` used by the later summations.

## Main results

* `one_phi_zero`, `one_phi_zero_terminating`, `one_phi_zero_upper_zero`: 17.5.2–17.5.4.
* `one_phi_zero_continuation_analytic`: analyticity of the product continuation.
* `one_phi_zero_common_zeros_removable`: common zeros of numerator and denominator are
  removable, stated as an analytic germ rather than another selected function.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory DLMF.QSeries
open scoped Real Topology
namespace DLMF.QHypergeometric

/-- The product quotient giving the meromorphic continuation of one-phi-zero on its regular set. -/
def qOnePhiZeroContinuation (a q z : ℂ) : ℂ := qPochhammerInf (a*z) q/qPochhammerInf z q

/-- The shared integer triangular exponent agrees with n-choose-two on nonnegative indices. -/
theorem qTri_nat (n : ℕ) : DLMF.QSeries.TripleProduct.tri n=(n.choose 2:ℤ) := by
  simpa using (DLMF.QSeries.TripleProduct.tri_sub_cast n 0).symm
/-- The `₂φ₁` term in phase-free form. -/
lemma qPhiTerm_two_one (a b c q z : ℂ) (n : ℕ) :
    qPhiTerm [a,b] [c] q z n=qPochhammer a q n*qPochhammer b q n/
      (qPochhammer c q n*qPochhammer q q n)*z^n := by
  have he : qPhiExponent [a,b] [c]=0 := by simp [qPhiExponent]
  simp [qPhiTerm,qPochhammerList,he]

/-- The phase-free `₂φ₁` series converges to `qPhi` in the unit disk. -/
lemma hasSum_qPhi_two_one {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hc : QDenominatorRegular [c] q) :
    HasSum (fun n : ℕ => qPochhammer a q n*qPochhammer b q n/
      (qPochhammer c q n*qPochhammer q q n)*z^n) (qPhi [a,b] [c] q z) := by
  have h := qPhi_hasSum (a := [a,b]) (b := [c]) (z := z) hq0 hq hc (by simp) (fun _ => hz)
  have e : (fun n : ℕ => qPochhammer a q n*qPochhammer b q n/
      (qPochhammer c q n*qPochhammer q q n)*z^n)=qPhiTerm [a,b] [c] q z :=
    funext fun n => (qPhiTerm_two_one a b c q z n).symm
  rw [e]
  exact h

/-- Regularity of a lower parameter passes to its `q`-multiple. -/
lemma qDenominatorRegular_mul_q {c q : ℂ} (hc : QDenominatorRegular [c] q) :
    QDenominatorRegular [c*q] q := by
  intro x hx n
  simp only [List.mem_singleton] at hx
  subst hx
  simpa [pow_succ',mul_assoc] using hc c (by simp) (n+1)

/-- Regularity of a lower parameter gives nonvanishing factorials. -/
lemma qPochhammer_ne_zero_of_qDenominatorRegular {c q : ℂ} (hq : ‖q‖<1)
    (hc : QDenominatorRegular [c] q) (n : ℕ) :
    qPochhammer c q n≠0 :=
  qPochhammer_ne_zero_of_factors hq (fun j h => hc c (by simp) j (sub_eq_zero.mp h).symm) n

/-- Regularity of a lower parameter gives `1-c≠0`. -/
lemma one_sub_ne_zero_of_qDenominatorRegular {c q : ℂ}
    (hc : QDenominatorRegular [c] q) : 1-c≠0 := by
  intro h; exact hc c (by simp) 0 (by simpa using (sub_eq_zero.mp h).symm)

/-- Prepending a zero term to a series. -/
def prependZero (f : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n+1 => f n

/-- Prepending a zero term keeps the sum. -/
lemma hasSum_prependZero {f : ℕ → ℂ} {s : ℂ} (h : HasSum f s) : HasSum (prependZero f) s := by
  apply (hasSum_nat_add_iff' 1).mp
  simpa [prependZero] using h

/-- Regularity of `c/q` gives regularity of `c`. -/
lemma qDenominatorRegular_of_div_q {c q : ℂ} (hq0 : q≠0) (hc : QDenominatorRegular [c/q] q) :
    QDenominatorRegular [c] q := by
  intro x hx n
  simp only [List.mem_singleton] at hx
  subst hx
  have h := hc (x/q) (by simp) (n+1)
  rwa [pow_succ',← mul_assoc,div_mul_cancel₀ _ hq0] at h

/-- The factorial at `xq` through the factorial at `x`. -/
lemma qPochhammer_mul_q {x q : ℂ} (hx : 1-x≠0) (n : ℕ) :
    qPochhammer (x*q) q n=qPochhammer x q n*(1-x*q^n)/(1-x) := by
  rw [← qPochhammer_succ,qPochhammer_succ']
  field_simp

/-- The `₂φ₁` series with its first upper parameter multiplied by `q`, premultiplied by `1-a`. -/
lemma hasSum_qPhi_two_one_mul_q {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hc : QDenominatorRegular [c] q) :
    HasSum (fun n : ℕ => qPochhammer a q (n+1)*qPochhammer b q n/
      (qPochhammer c q n*qPochhammer q q n)*z^n) ((1-a)*qPhi [a*q,b] [c] q z) := by
  refine ((hasSum_qPhi_two_one (a := a*q) (b := b) hq0 hq hz hc).mul_left (1-a)).congr_fun ?_
  intro n
  rw [qPochhammer_succ']
  ring

/-- The polynomial q-Chu–Vandermonde sum, from the q-Pfaff–Saalschütz sum at `s=0`. -/
private lemma sum_qBinom_qPochhammer_mul_pow (q x r : ℂ) (n : ℕ) :
    ∑ m ∈ range (n+1), qBinom q n m*qPochhammer r q m*qPochhammer x q (n-m)*x^m=
      qPochhammer (x*r) q n := by
  have h := sum_qBinom_saalschutz q x r 0 n
  simpa using h

/-- The polynomial q-Chu–Vandermonde sum with the weight on the complementary index. -/
lemma sum_qBinom_qPochhammer_mul_pow_sub (q a x : ℂ) (n : ℕ) :
    ∑ k ∈ range (n+1), qBinom q n k*qPochhammer a q k*qPochhammer x q (n-k)*a^(n-k)=
      qPochhammer (a*x) q n := by
  rw [← sum_qBinom_qPochhammer_mul_pow q a x n,← sum_range_reflect]
  apply sum_congr rfl
  intro k hk
  have hkn : k≤n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [show n+1-1-k=n-k by omega,Nat.sub_sub_self hkn]
  have hs := qBinom_add_symm q k (n-k)
  rw [Nat.add_sub_cancel' hkn] at hs
  rw [hs]
  ring

/-- Swapping the two upper parameters of a `₂φ₁`. -/
lemma qPhi_two_one_comm (a b c q z : ℂ) : qPhi [a,b] [c] q z=qPhi [b,a] [c] q z := by
  unfold qPhi qPhiTerm qPhiExponent qPochhammerList
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,List.length_cons,
    List.length_nil]
  congr 1; funext n; ring

/-- `C(k+m,2)=C(k,2)+C(m,2)+km`. -/
private lemma choose_two_add (k m : ℕ) : (k+m).choose 2=k.choose 2+m.choose 2+k*m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc,Nat.choose_succ_succ',Nat.choose_one_right,ih,Nat.choose_succ_succ',
      Nat.choose_one_right]
    ring

/-- The terminating `₂φ₁` term with the top parameter `q^{-n}` times `(c;q)_n`. -/
private lemma qPhiTerm_neg_pow_mul_qPochhammer {a c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hc0 : c≠0)
    {n k : ℕ} (hkn : k≤n)
    (hck : qPochhammer c q k≠0) (z : ℂ) :
    qPhiTerm [q^(-(n:ℤ)),a] [c] q z k*qPochhammer c q n=
      qBinom q n k*qPochhammer a q k*qPochhammer (q^(1-(n:ℤ))/c) q (n-k)*
        (-(z*q^(-(n:ℤ))))^k*(-c)^(n-k)*q^((n-k).choose 2+k*(n-k)+k.choose 2) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [Nat.add_sub_cancel_left,qPhiTerm_two_one,qBinom_terminating_ratio hq0 hq hkn,
    qPochhammer_add c q k m,qPochhammer_mul_pow_reverse hc0 hq0 k m]
  have hqq := qPochhammer_self_ne_zero hq k
  have hE : q^(((k+m:ℕ):ℤ)*k-(k.choose 2:ℤ))*q^(k.choose 2)=q^((k+m)*k) := by
    rw [← zpow_natCast q (k.choose 2),← zpow_add₀ hq0,← zpow_natCast]; congr 1; push_cast; ring
  have hN : (q^(-((k+m:ℕ):ℤ)))^k*q^((k+m)*k)=1 := by
    rw [← zpow_natCast (q^(-((k+m:ℕ):ℤ))),← zpow_mul,← zpow_natCast q ((k+m)*k),← zpow_add₀ hq0]
    rw [show -((k+m:ℕ):ℤ)*(k:ℤ)+(((k+m)*k:ℕ):ℤ)=0 by push_cast; ring,zpow_zero]
  have hs : (-1:ℂ)^k*(-1:ℂ)^k=1 := by rw [← mul_pow]; norm_num
  rw [neg_pow (c*q^k),mul_pow c (q^k),neg_pow (z*q^(-((k+m:ℕ):ℤ))),mul_pow z,neg_pow c,
    pow_add q,pow_add q,← pow_mul]
  generalize q^(((k+m:ℕ):ℤ)*k-(k.choose 2:ℤ)) = E at hE ⊢
  generalize (q^(-((k+m:ℕ):ℤ)))^k = W at hN ⊢
  generalize q^((k+m)*k) = N at hE hN
  generalize q^(k.choose 2) = Ck at hE ⊢
  generalize q^(m.choose 2) = M
  rw [mul_comm k m]
  generalize q^(m*k) = K
  generalize qPochhammer q q k = Q at hqq ⊢
  generalize qPochhammer c q k = C at hck ⊢
  field_simp
  linear_combination (qPochhammer (q^(-((k+m:ℕ):ℤ))) q k*qPochhammer a q k*z^k*
    qPochhammer (q^(1-((k+m:ℕ):ℤ))/c) q m*K*M)*(-hs-((-1:ℂ)^k*(-1:ℂ)^k)*hN-
      ((-1:ℂ)^k*(-1:ℂ)^k)*W*hE)

/-- The terminating `₂φ₁` sum with top parameter `q^{-n}`, cleared by `(c;q)_n`. -/
lemma qPhi_neg_pow_mul_qPochhammer {a c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hc0 : c≠0) {n : ℕ}
    (hcn : qPochhammer c q n≠0) (z : ℂ) :
    qPhi [q^(-(n:ℤ)),a] [c] q z*qPochhammer c q n=q^(n.choose 2)*
      ∑ k ∈ range (n+1), qBinom q n k*qPochhammer a q k*qPochhammer (q^(1-(n:ℤ))/c) q (n-k)*
        (-(z*q^(-(n:ℤ))))^k*(-c)^(n-k) := by
  rw [qPhi_terminates (a := [a]) hq0 n,qPhiPartial,sum_mul,mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k≤n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [qPhiTerm_neg_pow_mul_qPochhammer hq0 hq hc0 hkn (qPochhammer_ne_zero_of_le hcn hkn)]
  have he : (n-k).choose 2+k*(n-k)+k.choose 2=n.choose 2 := by
    have := choose_two_add (n-k) k
    rw [Nat.sub_add_cancel hkn] at this
    rw [this]; ring
  rw [he]
  ring

/-- The product `∏(a-cq^j)` as a reversed shifted factorial. -/
private lemma prod_sub_mul_pow_eq_qPochhammer_reverse {a c q : ℂ} (hq0 : q≠0) (hc0 : c≠0) (n : ℕ) :
    (∏ j ∈ range n, (a-c*q^j))=q^(n.choose 2)*(-c)^n*qPochhammer (q^(1-(n:ℤ))/c*a) q n := by
  rw [qPochhammer_eq_prod]
  conv_rhs => rw [← prod_range_reflect]
  have h1 : ∀ j ∈ range n, a-c*q^j=(-c*q^j)*(1-q^(1-(n:ℤ))/c*a*q^(n-1-j)) := by
    intro j hj
    have hjn : j<n := mem_range.mp hj
    have e : q^(1-(n:ℤ))*q^(n-1-j)*q^j=1 := by
      rw [← zpow_natCast q (n-1-j),← zpow_natCast q j,← zpow_add₀ hq0,← zpow_add₀ hq0]
      rw [show (1-(n:ℤ))+((n-1-j:ℕ):ℤ)+(j:ℤ)=0 by omega,zpow_zero]
    field_simp
    linear_combination (-a)*e
  rw [prod_congr rfl h1,prod_mul_distrib,prod_mul_distrib,prod_const,card_range,
    prod_pow_eq_pow_sum,sum_range_id,Nat.choose_two_right]
  ring

/-- Two functions continuous at `0` that agree on a punctured neighbourhood agree at `0`. -/
lemma eq_at_zero_of_eventually_punctured {f g : ℂ → ℂ} (hf : ContinuousAt f 0)
    (hg : ContinuousAt g 0) (h : ∀ᶠ c in 𝓝[≠] (0:ℂ), f c=g c) : f 0=g 0 :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' (h.mono fun _ h => h.symm))

/-- The cleared second q-Chu–Vandermonde sum for nonzero `c`. -/
lemma qPhi_neg_pow_q_mul_qPochhammer {a c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ) (hc0 : c≠0)
    (hcn : qPochhammer c q n≠0) :
    qPhi [q^(-(n:ℤ)),a] [c] q q*qPochhammer c q n=(range n).prod (fun j => a-c*q^j) := by
  rw [qPhi_neg_pow_mul_qPochhammer hq0 hq hc0 hcn,prod_sub_mul_pow_eq_qPochhammer_reverse hq0 hc0]
  have hz : -(q*q^(-(n:ℤ)))= -q^(1-(n:ℤ)) := by
    rw [zpow_sub₀ hq0,zpow_one,zpow_neg]; field_simp
  rw [hz]
  have hterm : ∀ k ∈ range (n+1),
      qBinom q n k*qPochhammer a q k*qPochhammer (q^(1-(n:ℤ))/c) q (n-k)*
      (-q^(1-(n:ℤ)))^k*(-c)^(n-k)=(-c)^n*(qBinom q n k*qPochhammer a q k*
        qPochhammer (q^(1-(n:ℤ))/c) q (n-k)*(q^(1-(n:ℤ))/c)^k) := by
    intro k hk
    have hkn : k≤n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hkn
    rw [Nat.add_sub_cancel_left,div_pow,pow_add (-c),neg_pow (q^(1-((k+m:ℕ):ℤ))),neg_pow c k]
    field_simp
  rw [sum_congr rfl hterm,← mul_sum,sum_qBinom_qPochhammer_mul_pow]
  ring

/-- The q-number `(1-q^c)/(1-q) → c` as `q → 1⁻` along the reals. -/
lemma tendsto_qNumber_one (c : ℂ) :
    Tendsto (fun q : ℝ => (1-(q:ℂ)^c)/(1-(q:ℂ))) (𝓝[<] 1) (𝓝 c) := by
  have h1 : (1:ℂ)∈slitPlane := by simp [slitPlane]
  have hd : HasDerivAt (fun q : ℝ => (q:ℂ)^c) c 1 := by
    have := (Complex.hasStrictDerivAt_cpow_const (c := c) h1).hasDerivAt
    simpa using this.comp_ofReal
  have hs := hd.tendsto_slope.mono_left (nhdsWithin_mono _
    (show Iio (1:ℝ) ⊆ {1}ᶜ from fun x hx => by simp only [Set.mem_Iio] at hx;
                                               simpa using ne_of_lt hx))
  refine hs.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq1 : (1:ℂ)-q≠0 := by
    rw [sub_ne_zero]; exact_mod_cast (ne_of_lt (show q<1 from hq)).symm
  rw [slope_def_module,Complex.real_smul]
  push_cast
  rw [Complex.one_cpow]
  have hq2 : (q:ℂ)-1≠0 := fun h => hq1 (by linear_combination -h)
  rw [show (1-(q:ℂ)^c)/(1-(q:ℂ))=((q:ℂ)^c-1)/((q:ℂ)-1) by
    rw [div_eq_div_iff hq1 hq2]; ring,div_eq_inv_mul]

/-- `q^c → 1` as `q → 1⁻` along the reals. -/
lemma tendsto_ofReal_cpow_one (c : ℂ) :
    Tendsto (fun q : ℝ => (q:ℂ)^c) (𝓝[<] 1) (𝓝 1) := by
  have h1 : (1:ℂ)∈slitPlane := by simp [slitPlane]
  have hd : HasDerivAt (fun q : ℝ => (q:ℂ)^c) c 1 := by
    have := (Complex.hasStrictDerivAt_cpow_const (c := c) h1).hasDerivAt
    simpa using this.comp_ofReal
  simpa using hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

/-- Every unilateral series takes the value `1` at the origin. -/
private lemma qPhi_zero_eq_one (a b : List ℂ) (q : ℂ) : qPhi a b q 0=1 := by
  unfold qPhi
  rw [tsum_eq_single 0]
  · simp [qPhiTerm,qPochhammerList,DLMF.QSeries.TripleProduct.tri,
      List.map_const',List.prod_replicate]
  · intro n hn
    simp [qPhiTerm,zero_pow hn]

/-- One q-derivative step for the `₂φ₁` series. -/
private lemma qDifference_qPhi_two_one {a b c q d w : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hc : QDenominatorRegular [c] q) (hw : w≠0) (hdw : ‖d*w‖<1) :
    (qPhi [a,b] [c] q (d*w)-qPhi [a,b] [c] q (d*(q*w)))/((1-q)*w)=
      (1-a)*(1-b)*d/((1-c)*(1-q))*qPhi [a*q,b*q] [c*q] q (d*w) := by
  have hdqw : ‖d*(q*w)‖<1 := by
    rw [show d*(q*w)=q*(d*w) by ring,norm_mul]
    calc ‖q‖*‖d*w‖ ≤ 1*‖d*w‖ := by gcongr
      _ < 1 := by linarith
  have hq1 : (1:ℂ)-q≠0 := one_sub_ne_zero_of_norm_lt_one hq
  have h1 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hdw hc
  have h2 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hdqw hc
  have h3 := hasSum_prependZero ((hasSum_qPhi_two_one (a := a*q) (b := b*q) hq0 hq hdw
    (qDenominatorRegular_mul_q hc)).mul_left ((1-a)*(1-b)*d/((1-c)*(1-q))))
  refine ((h1.sub h2).div_const ((1-q)*w)).unique (h3.congr_fun ?_)
  have hc1 := one_sub_ne_zero_of_qDenominatorRegular hc
  intro n
  cases n with
  | zero => simp [prependZero]
  | succ n =>
    simp only [prependZero]
    have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq (qDenominatorRegular_mul_q hc) n
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_succ' a,qPochhammer_succ' b,qPochhammer_succ' c,qPochhammer_succ q]
    generalize qPochhammer (a*q) q n = A
    generalize qPochhammer (b*q) q n = B
    generalize qPochhammer (c*q) q n = C at hcc ⊢
    generalize qPochhammer q q n = P at hqq ⊢
    rw [mul_pow,mul_pow,mul_pow,pow_succ d,pow_succ w,pow_succ q]
    generalize q^n = Q at hqn ⊢
    generalize hD0 : 1-q*Q = D0 at hqn ⊢
    generalize hD1 : 1-c = D1 at hc1 ⊢
    generalize hD2 : 1-q = D2 at hq1 ⊢
    field_simp
    simp only [← hD0]
    ring

/-- The derivative of a `₂φ₁` series at the origin. -/
private lemma hasDerivAt_qPhi_two_one_zero {a b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hc : QDenominatorRegular [c] q) :
    HasDerivAt (qPhi [a,b] [c] q) ((1-a)*(1-b)/((1-c)*(1-q))) 0 := by
  have han := qPhi_analytic_disc (a := [a,b]) (b := [c]) hq0 hq hc (by simp) 0 (by simp)
  have hd := han.differentiableAt.hasDerivAt
  have h1 := qPhi_iteratedDeriv_zero (a := [a,b]) (b := [c]) hq0 hq hc (by simp) 1
  rw [iteratedDeriv_one] at h1
  rw [h1] at hd
  convert hd using 1
  simp [qPhiCoeff,qPhiTerm_two_one,qPochhammer_one]

/-- The iterated q-derivative of `w ↦ ₂φ₁(dw)` on the whole disc `‖dw‖<1`. -/
lemma qDerivIterate_qPhi_two_one {a b c d q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hc : QDenominatorRegular [c] q) (k : ℕ) : ∀ w : ℂ, ‖d*w‖<1 →
    qDerivIterate k q (fun w => qPhi [a,b] [c] q (w*d)) w=
      qPochhammerList [a,b] q k*d^k/(qPochhammer c q k*(1-q)^k)*
        qPhi [a*q^k,b*q^k] [c*q^k] q (d*w) := by
  induction k with
  | zero =>
    intro w _
    simp [qDerivIterate,qPochhammerList,mul_comm]
  | succ k ih =>
    intro w hw
    have hck : QDenominatorRegular [c*q^k] q := by
      intro x hx n
      simp only [List.mem_singleton] at hx
      subst hx
      simpa [pow_add,mul_assoc] using hc c (by simp) (k+n)
    have hq1 : (1:ℂ)-q≠0 := one_sub_ne_zero_of_norm_lt_one hq
    have hcq := one_sub_ne_zero_of_qDenominatorRegular hck
    have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hc k
    have hstep : qPochhammerList [a,b] q (k+1)*d^(k+1)/(qPochhammer c q (k+1)*(1-q)^(k+1))=
        qPochhammerList [a,b] q k*d^k/(qPochhammer c q k*(1-q)^k)*
          ((1-a*q^k)*(1-b*q^k)*d/((1-c*q^k)*(1-q))) := by
      simp only [qPochhammerList,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
        qPochhammer_succ,pow_succ]
      field_simp
    have hpar : ∀ x : ℂ, x*q^k*q=x*q^(k+1) := fun x => by rw [pow_succ,mul_assoc]
    rw [qDerivIterate,Function.iterate_succ_apply',← qDerivIterate,hstep]
    by_cases hw0 : w=0
    · subst hw0
      rw [qDerivExtended_zero]
      have hev : qDerivIterate k q (fun w => qPhi [a,b] [c] q (w*d))=ᶠ[𝓝 0]
          fun w => qPochhammerList [a,b] q k*d^k/(qPochhammer c q k*(1-q)^k)*
            qPhi [a*q^k,b*q^k] [c*q^k] q (d*w) := by
        have ho : IsOpen {w : ℂ | ‖d*w‖<1} := isOpen_lt (by fun_prop) continuous_const
        filter_upwards [ho.mem_nhds (by simp)] with w hw
        exact ih w hw
      rw [hev.deriv_eq]
      have hD := ((hasDerivAt_qPhi_two_one_zero (a := a*q^k) (b := b*q^k) hq0 hq hck).comp_of_eq
        (0:ℂ) ((hasDerivAt_id (0:ℂ)).const_mul d) (by simp)).const_mul
        (qPochhammerList [a,b] q k*d^k/(qPochhammer c q k*(1-q)^k))
      simp only [Function.comp_def,mul_one,id] at hD
      rw [hD.deriv,mul_zero,qPhi_zero_eq_one]
      ring
    · rw [qDerivExtended_of_ne_zero hw0,qDeriv,ih w hw,ih (q*w) (by
        rw [show d*(q*w)=q*(d*w) by ring,norm_mul]
        calc ‖q‖*‖d*w‖ ≤ 1*‖d*w‖ := by gcongr
          _ < 1 := by linarith),mul_div_assoc,← mul_sub,mul_div_assoc,
        qDifference_qPhi_two_one hq0 hq hck hw0 hw,hpar,hpar,hpar]
      ring

/-- The `₂φ₁` series with all parameters shifted by `q^j`, premultiplied by its leading factors. -/
lemma hasSum_qPhi_two_one_shift {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hc : QDenominatorRegular [c] q) (j : ℕ) :
    HasSum (fun m : ℕ => qPochhammer a q (m+j)*qPochhammer b q (m+j)/
      (qPochhammer c q (m+j)*qPochhammer q q m)*z^m)
      (qPochhammer a q j*qPochhammer b q j/qPochhammer c q j*qPhi [a*q^j,b*q^j] [c*q^j] q z) := by
  have hcj : QDenominatorRegular [c*q^j] q := by
    intro x hx n
    simp only [List.mem_singleton] at hx
    subst hx
    simpa [pow_add,mul_assoc] using hc c (by simp) (j+n)
  have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hc j
  refine ((hasSum_qPhi_two_one (a := a*q^j) (b := b*q^j) hq0 hq hz hcj).mul_left
    (qPochhammer a q j*qPochhammer b q j/qPochhammer c q j)).congr_fun ?_
  intro m
  rw [Nat.add_comm m j,qPochhammer_add a,qPochhammer_add b,qPochhammer_add c]
  have hcm := qPochhammer_ne_zero_of_qDenominatorRegular hq hcj m
  by_cases hq' : qPochhammer q q m=0
  · simp [hq']
  field_simp

/-- The q-binomial theorem: `1φ0(a;-;q,z) = (az;q)_∞/(z;q)_∞` for `|z| < 1` (DLMF 17.5.E2). -/
@[dlmf 17.5.E2]
theorem one_phi_zero {a q z : ℂ} (hq : ‖q‖<1) (hz : ‖z‖<1) :
    qPhi [a] [] q z=qPochhammerInf (a*z) q/qPochhammerInf z q := by
  rw [qPhi_eq_basicHG (by simp)]
  simpa [basicHG] using (q_binomial_theorem (a := a) hq hz).symm

/-- Terminating q-binomial theorem: `1φ0(q^(-n);-;q,z) = (z q^(-n);q)_n` (DLMF 17.5.E3). -/
@[dlmf 17.5.E3]
theorem one_phi_zero_terminating {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (z : ℂ) (n : ℕ) :
    qPhi [q^(-(n:ℤ))] [] q z=qPochhammer (z*q^(-(n:ℤ))) q n := by
  rw [qPhi_terminates (a := []) hq0 n,
    qPochhammer_eq_sum_qBinom,qPhiPartial]
  apply sum_congr rfl
  intro k hk
  have hkn : k≤n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have he : qPhiExponent [q^(-(n:ℤ))] []=0 := by simp [qPhiExponent]
  simp only [qPhiTerm,qPochhammerList,he,List.map_cons,List.map_nil,List.prod_cons,
    List.prod_nil,mul_one,one_mul,zpow_zero]
  rw [qBinom_terminating_ratio hq0 hq hkn]
  have hqq := qPochhammer_self_ne_zero hq k
  have hs : (-1:ℂ)^k*(-1:ℂ)^k=1 := by rw [← mul_pow]; norm_num
  have hp : q^((n:ℤ)*k-(k.choose 2:ℤ))*q^(k.choose 2)*(q^(-(n:ℤ)))^k=1 := by
    rw [← zpow_natCast,← zpow_natCast (q^(-(n:ℤ))),← zpow_mul,← zpow_add₀ hq0,← zpow_add₀ hq0]
    rw [show (n:ℤ)*k-(k.choose 2:ℤ)+(k.choose 2:ℤ)+(-(n:ℤ))*(k:ℤ)=0 by ring,zpow_zero]
  rw [mul_pow]
  field_simp
  linear_combination (-(qPochhammer (q^(-(n:ℤ))) q k*z^k))*((-1:ℂ)^k*(-1:ℂ)^k*hp+hs)

/-- Euler's sum: `1φ0(0;-;q,z) = 1/(z;q)_∞` for `|z| < 1` (DLMF 17.5.E4). -/
@[dlmf 17.5.E4]
theorem one_phi_zero_upper_zero {q z : ℂ} (hq : ‖q‖<1) (hz : ‖z‖<1) :
    qPhi [0] [] q z=(qPochhammerInf z q)⁻¹ := by
  rw [one_phi_zero hq hz]
  simp [qPochhammerInf]

/-- The product quotient is analytic on its regular set, by Mathlib analytic composition/division.
-/
theorem one_phi_zero_continuation_analytic {a q : ℂ} (hq : ‖q‖<1) :
    AnalyticOnNhd ℂ (qOnePhiZeroContinuation a q) {z | qPochhammerInf z q≠0} := by
  intro z hz
  have hn : AnalyticAt ℂ (fun w : ℂ => qPochhammerInf (a*w) q) z := by
    simpa only [Function.comp_def] using
      (qPochhammerInf_analytic hq (a*z) (mem_univ _)).comp (analyticAt_const.mul analyticAt_id)
  have hd : AnalyticAt ℂ (fun w : ℂ => qPochhammerInf w q) z :=
    qPochhammerInf_analytic hq z (mem_univ _)
  unfold qOnePhiZeroContinuation
  simpa only [Pi.div_def] using hn.div hd hz

/-- Removing the vanishing factor of a q-product leaves an analytic unit. -/
private lemma qPochhammerInf_factor_at_zero {q w : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hw : qPochhammerInf w q = 0) :
    ∃ n : ℕ, w * q ^ n = 1 ∧ ∃ G : ℂ → ℂ, AnalyticAt ℂ G w ∧ G w ≠ 0 ∧
      ∀ z, qPochhammerInf z q = (1 - z * q ^ n) * G z := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, w * q ^ n = 1 := by
    by_contra h
    apply (qPochhammerInf_ne_zero hq ?_) hw
    intro n hn
    exact h ⟨n, (sub_eq_zero.mp hn).symm⟩
  have hw0 : w ≠ 0 := left_ne_zero_of_mul (hn ▸ one_ne_zero)
  have hinj : Function.Injective (fun j : ℕ => q ^ j) := by
    intro i j hij
    apply (pow_right_strictAnti₀ (norm_pos_iff.mpr hq0) hq).injective
    simpa only [norm_pow] using congrArg norm hij
  have huniq (j : ℕ) (hj : w * q ^ j = 1) : j = n :=
    hinj (mul_left_cancel₀ hw0 (hj.trans hn.symm))
  let G : ℂ → ℂ := fun z => qPochhammer z q n * qPochhammerInf (z * q ^ (n + 1)) q
  have hp (m : ℕ) : AnalyticAt ℂ (fun z => qPochhammer z q m) w := by
    induction m with
    | zero => simpa only [qPochhammer_zero] using (analyticAt_const (v := (1 : ℂ)))
    | succ m ih =>
      simpa only [qPochhammer_succ, Pi.mul_apply, Pi.sub_apply, id_eq] using!
        ih.mul (analyticAt_const.sub (analyticAt_id.mul analyticAt_const))
  have hG : AnalyticAt ℂ G w :=
    (hp n).mul ((qPochhammerInf_analytic hq _ (mem_univ _)).comp
      (analyticAt_id.mul analyticAt_const))
  have hGn : G w ≠ 0 := by
    apply mul_ne_zero
    · rw [qPochhammer_eq_prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj he
      have heq := huniq j (sub_eq_zero.mp he).symm
      have hjn := Finset.mem_range.mp hj
      omega
    · apply qPochhammerInf_ne_zero hq
      intro j hj
      have he := huniq (n + 1 + j) (by
        simpa only [pow_add, mul_assoc] using (sub_eq_zero.mp hj).symm)
      omega
  refine ⟨n, hn, G, hG, hGn, fun z => ?_⟩
  rw [qPochhammerInf_mul_qPochhammer hq (n + 1), qPochhammer_succ]
  dsimp [G]
  ring

/-- Common product zeros have a removable germ, rather than the quotient totalization 0/0. -/
theorem one_phi_zero_common_zeros_removable {a q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hd : qPochhammerInf z q=0) (hn : qPochhammerInf (a*z) q=0) :
    ∃ U : Set ℂ, IsOpen U ∧ z∈U ∧ ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F U ∧
      ∀ w∈U, qPochhammerInf w q≠0 → F w=qOnePhiZeroContinuation a q w := by
  obtain ⟨i, hi, G, hG, hG0, heG⟩ := qPochhammerInf_factor_at_zero hq0 hq hd
  obtain ⟨j, hj, H, hH, hH0, heH⟩ := qPochhammerInf_factor_at_zero hq0 hq hn
  have hz0 : z ≠ 0 := left_ne_zero_of_mul (hi ▸ one_ne_zero)
  have he : a * q ^ j = q ^ i := by
    apply mul_left_cancel₀ hz0
    calc z * (a * q ^ j) = a * z * q ^ j := by ring
      _ = 1 := hj
      _ = z * q ^ i := hi.symm
  let F : ℂ → ℂ := fun w => H (a * w) / G w
  have hFa : AnalyticAt ℂ F z :=
    (hH.comp (analyticAt_const.mul analyticAt_id)).div hG hG0
  refine ⟨{w | AnalyticAt ℂ F w}, isOpen_analyticAt _ _, hFa, F, fun w hw => hw, ?_⟩
  intro w _hw hden
  dsimp [F, qOnePhiZeroContinuation]
  rw [heH, heG]
  have hf : 1 - w * q ^ i ≠ 0 := by
    intro hf
    apply hden
    rw [heG, hf, zero_mul]
  rw [show a * w * q ^ j = w * q ^ i by calc
    a * w * q ^ j = w * (a * q ^ j) := by ring
    _ = w * q ^ i := by rw [he]]
  exact (mul_div_mul_left _ _ hf).symm

end DLMF.QHypergeometric
