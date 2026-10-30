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
# Low-order basic hypergeometric functions (DLMF §§17.5–17.6)

The series retain DLMF's integer phase exponents. Literal product quotients are used only
where their denominators are nonzero; cancelled product forms and removable-limit statements
retain exceptional upper parameters. The full-domain q-Gauss proof uses a normally
convergent Newton series and Mathlib’s analytic identity theorem, interpolating the
terminating q-Chu values without excluding exceptional upper parameters. Finite identities require lower-parameter regularity
only through the final retained term. Continuation is separate from totalized divergent sums.
The product-continuation proofs directly reuse Mathlib analytic composition/quotient rules
and the existing TauCeti `ContinuesInside` germ adapter.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory DLMF.QSeries
open scoped Real Topology
namespace DLMF.QHypergeometric

/-- The product quotient giving the meromorphic continuation of one-phi-zero on its regular set. -/
def qOnePhiZeroContinuation (a q z : ℂ) : ℂ := qPochhammerInf (a*z) q/qPochhammerInf z q
/-- The Jackson expression in Heine's integral, kept separate from its removable parameter values. -/
def qHeineJacksonValue (q : ℝ) (a b c z : ℂ) : ℂ :=
  qGamma q c/(qGamma q b*qGamma q (c-b))*
    jacksonIntegral q 1 (fun t => t^(b-1)*qPochhammerOrder (t*q) q (c-b-1)/qPochhammerOrder (z*t) q a)
/-- The integrand in the Mellin–Barnes representation of two-phi-one. -/
def qHeineBarnesKernel (a b c q z s : ℂ) : ℂ :=
  qPochhammerListInf [q^(1+s),c*q^s] q/qPochhammerListInf [a*q^s,b*q^s] q*
    π*(-z)^s/Complex.sin (π*s)
/-- The denominator-pole set on the logarithmic q-plane in the Barnes representation. -/
def qHeineBarnesLeft (a b q : ℂ) : Set ℂ :=
  {s | qPochhammerListInf [a*q^s,b*q^s] q=0}
/-- The nonnegative-integer poles belonging to the right side of the Barnes contour. -/
def qHeineBarnesRight : Set ℂ := Set.range (fun n : ℕ => (n:ℂ))

/-- The shared integer triangular exponent agrees with n-choose-two on nonnegative indices. -/
theorem qTri_nat (n : ℕ) : DLMF.QSeries.TripleProduct.tri n=(n.choose 2:ℤ) := by
  simpa using (DLMF.QSeries.TripleProduct.tri_sub_cast n 0).symm
/-- The `₂φ₁` term in phase-free form. -/
lemma qaR4_phi21_term (a b c q z : ℂ) (n : ℕ) :
    qPhiTerm [a,b] [c] q z n=qPochhammer a q n*qPochhammer b q n/
      (qPochhammer c q n*qPochhammer q q n)*z^n := by
  have he : qPhiExponent [a,b] [c]=0 := by simp [qPhiExponent]
  simp [qPhiTerm,qPochhammerList,he]

/-- The phase-free `₂φ₁` series converges to `qPhi` in the unit disk. -/
lemma qaR4_phi21_hasSum {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hc : QDenominatorRegular [c] q) :
    HasSum (fun n : ℕ => qPochhammer a q n*qPochhammer b q n/
      (qPochhammer c q n*qPochhammer q q n)*z^n) (qPhi [a,b] [c] q z) := by
  have h := qPhi_hasSum (a := [a,b]) (b := [c]) (z := z) hq0 hq hc (by simp) (fun _ => hz)
  have e : (fun n : ℕ => qPochhammer a q n*qPochhammer b q n/
      (qPochhammer c q n*qPochhammer q q n)*z^n)=qPhiTerm [a,b] [c] q z :=
    funext fun n => (qaR4_phi21_term a b c q z n).symm
  rw [e]
  exact h

/-- Regularity of a lower parameter passes to its `q`-multiple. -/
lemma qaR4_reg_mul_q {c q : ℂ} (hc : QDenominatorRegular [c] q) :
    QDenominatorRegular [c*q] q := by
  intro x hx n
  simp only [List.mem_singleton] at hx
  subst hx
  simpa [pow_succ',mul_assoc] using hc c (by simp) (n+1)

/-- Regularity of a lower parameter gives nonvanishing factorials. -/
lemma qaR4_reg_poch_ne {c q : ℂ} (hq : ‖q‖<1) (hc : QDenominatorRegular [c] q) (n : ℕ) :
    qPochhammer c q n≠0 :=
  qPochhammer_ne_zero_of_factors hq (fun j h => hc c (by simp) j (sub_eq_zero.mp h).symm) n

/-- Regularity of a lower parameter gives `1-c≠0`. -/
lemma qaR4_reg_one_sub_ne {c q : ℂ} (hc : QDenominatorRegular [c] q) : 1-c≠0 := by
  intro h; exact hc c (by simp) 0 (by simpa using (sub_eq_zero.mp h).symm)

/-- Prepending a zero term to a series. -/
def qaR4_shift (f : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n+1 => f n

/-- Prepending a zero term keeps the sum. -/
lemma qaR4_hasSum_shift {f : ℕ → ℂ} {s : ℂ} (h : HasSum f s) : HasSum (qaR4_shift f) s := by
  apply (hasSum_nat_add_iff' 1).mp
  simpa [qaR4_shift] using h

/-- Regularity of `c/q` gives regularity of `c`. -/
lemma qaR4_reg_of_div_q {c q : ℂ} (hq0 : q≠0) (hc : QDenominatorRegular [c/q] q) :
    QDenominatorRegular [c] q := by
  intro x hx n
  simp only [List.mem_singleton] at hx
  subst hx
  have h := hc (x/q) (by simp) (n+1)
  rwa [pow_succ',← mul_assoc,div_mul_cancel₀ _ hq0] at h

/-- The factorial at `xq` through the factorial at `x`. -/
lemma qaR4_poch_mul_q {x q : ℂ} (hx : 1-x≠0) (n : ℕ) :
    qPochhammer (x*q) q n=qPochhammer x q n*(1-x*q^n)/(1-x) := by
  rw [← qPochhammer_succ,qPochhammer_succ']
  field_simp

/-- The `₂φ₁` series with its first upper parameter multiplied by `q`, premultiplied by `1-a`. -/
lemma qaR4_phi21_hasSum_pre {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hc : QDenominatorRegular [c] q) :
    HasSum (fun n : ℕ => qPochhammer a q (n+1)*qPochhammer b q n/
      (qPochhammer c q n*qPochhammer q q n)*z^n) ((1-a)*qPhi [a*q,b] [c] q z) := by
  refine ((qaR4_phi21_hasSum (a := a*q) (b := b) hq0 hq hz hc).mul_left (1-a)).congr_fun ?_
  intro n
  rw [qPochhammer_succ']
  ring

/-- The polynomial q-Chu–Vandermonde sum, from the q-Pfaff–Saalschütz sum at `s=0`. -/
lemma qaR4_vandermonde_poly (q x r : ℂ) (n : ℕ) :
    ∑ m ∈ range (n+1), qBinom q n m*qPochhammer r q m*qPochhammer x q (n-m)*x^m=
      qPochhammer (x*r) q n := by
  have h := sum_qBinom_saalschutz q x r 0 n
  simpa using h

/-- The polynomial q-Chu–Vandermonde sum with the weight on the complementary index. -/
lemma qaR4_vandermonde_poly' (q a x : ℂ) (n : ℕ) :
    ∑ k ∈ range (n+1), qBinom q n k*qPochhammer a q k*qPochhammer x q (n-k)*a^(n-k)=
      qPochhammer (a*x) q n := by
  rw [← qaR4_vandermonde_poly q a x n,← sum_range_reflect]
  apply sum_congr rfl
  intro k hk
  have hkn : k≤n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [show n+1-1-k=n-k by omega,Nat.sub_sub_self hkn]
  have hs := qaR4_qBinom_symm q k (n-k)
  rw [Nat.add_sub_cancel' hkn] at hs
  rw [hs]
  ring

/-- Swapping the two upper parameters of a `₂φ₁`. -/
lemma qaR4_qPhi_swap21 (a b c q z : ℂ) : qPhi [a,b] [c] q z=qPhi [b,a] [c] q z := by
  unfold qPhi qPhiTerm qPhiExponent qPochhammerList
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,List.length_cons,
    List.length_nil]
  congr 1; funext n; ring

/-- `C(k+m,2)=C(k,2)+C(m,2)+km`. -/
lemma qaR4_choose_two_add (k m : ℕ) : (k+m).choose 2=k.choose 2+m.choose 2+k*m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc,Nat.choose_succ_succ',Nat.choose_one_right,ih,Nat.choose_succ_succ',
      Nat.choose_one_right]
    ring

/-- The terminating `₂φ₁` term with the top parameter `q^{-n}` times `(c;q)_n`. -/
lemma qaR4_term_chu {a c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hc0 : c≠0) {n k : ℕ} (hkn : k≤n)
    (hck : qPochhammer c q k≠0) (z : ℂ) :
    qPhiTerm [q^(-(n:ℤ)),a] [c] q z k*qPochhammer c q n=
      qBinom q n k*qPochhammer a q k*qPochhammer (q^(1-(n:ℤ))/c) q (n-k)*
        (-(z*q^(-(n:ℤ))))^k*(-c)^(n-k)*q^((n-k).choose 2+k*(n-k)+k.choose 2) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [Nat.add_sub_cancel_left,qaR4_phi21_term,qBinom_terminating_ratio hq0 hq hkn,
    qPochhammer_add c q k m,qaR4_reverse_tail hc0 hq0 k m]
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
lemma qaR4_sum_chu {a c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hc0 : c≠0) {n : ℕ}
    (hcn : qPochhammer c q n≠0) (z : ℂ) :
    qPhi [q^(-(n:ℤ)),a] [c] q z*qPochhammer c q n=q^(n.choose 2)*
      ∑ k ∈ range (n+1), qBinom q n k*qPochhammer a q k*qPochhammer (q^(1-(n:ℤ))/c) q (n-k)*
        (-(z*q^(-(n:ℤ))))^k*(-c)^(n-k) := by
  rw [qPhi_terminates (a := [a]) hq0 hq n (by simpa [QDenominatorRegularThrough,qPochhammerList]
    using hcn),qPhiPartial,sum_mul,mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k≤n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [qaR4_term_chu hq0 hq hc0 hkn (qPochhammer_ne_zero_of_le hcn hkn)]
  have he : (n-k).choose 2+k*(n-k)+k.choose 2=n.choose 2 := by
    have := qaR4_choose_two_add (n-k) k
    rw [Nat.sub_add_cancel hkn] at this
    rw [this]; ring
  rw [he]
  ring

/-- The product `∏(a-cq^j)` as a reversed shifted factorial. -/
lemma qaR4_prod_sub_eq {a c q : ℂ} (hq0 : q≠0) (hc0 : c≠0) (n : ℕ) :
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
lemma qaR4_eq_at_zero_of_punctured {f g : ℂ → ℂ} (hf : ContinuousAt f 0)
    (hg : ContinuousAt g 0) (h : ∀ᶠ c in 𝓝[≠] (0:ℂ), f c=g c) : f 0=g 0 :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' (h.mono fun _ h => h.symm))

/-- The cleared second q-Chu–Vandermonde sum for nonzero `c`. -/
lemma qaR4_chu_second_ne {a c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ) (hc0 : c≠0)
    (hcn : qPochhammer c q n≠0) :
    qPhi [q^(-(n:ℤ)),a] [c] q q*qPochhammer c q n=(range n).prod (fun j => a-c*q^j) := by
  rw [qaR4_sum_chu hq0 hq hc0 hcn,qaR4_prod_sub_eq hq0 hc0]
  have hz : -(q*q^(-(n:ℤ)))= -q^(1-(n:ℤ)) := by
    rw [zpow_sub₀ hq0,zpow_one,zpow_neg]; field_simp
  rw [hz]
  have hterm : ∀ k ∈ range (n+1), qBinom q n k*qPochhammer a q k*qPochhammer (q^(1-(n:ℤ))/c) q (n-k)*
      (-q^(1-(n:ℤ)))^k*(-c)^(n-k)=(-c)^n*(qBinom q n k*qPochhammer a q k*
        qPochhammer (q^(1-(n:ℤ))/c) q (n-k)*(q^(1-(n:ℤ))/c)^k) := by
    intro k hk
    have hkn : k≤n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hkn
    rw [Nat.add_sub_cancel_left,div_pow,pow_add (-c),neg_pow (q^(1-((k+m:ℕ):ℤ))),neg_pow c k]
    field_simp
  rw [sum_congr rfl hterm,← mul_sum,qaR4_vandermonde_poly]
  ring

/-- The q-number `(1-q^c)/(1-q) → c` as `q → 1⁻` along the reals. -/
lemma qaR4_tendsto_qnum (c : ℂ) :
    Tendsto (fun q : ℝ => (1-(q:ℂ)^c)/(1-(q:ℂ))) (𝓝[<] 1) (𝓝 c) := by
  have h1 : (1:ℂ)∈slitPlane := by simp [slitPlane]
  have hd : HasDerivAt (fun q : ℝ => (q:ℂ)^c) c 1 := by
    have := (Complex.hasStrictDerivAt_cpow_const (c := c) h1).hasDerivAt
    simpa using this.comp_ofReal
  have hs := hd.tendsto_slope.mono_left (nhdsWithin_mono _
    (show Iio (1:ℝ) ⊆ {1}ᶜ from fun x hx => by simp only [Set.mem_Iio] at hx; simpa using ne_of_lt hx))
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
lemma qaR4_tendsto_cpow_one (c : ℂ) :
    Tendsto (fun q : ℝ => (q:ℂ)^c) (𝓝[<] 1) (𝓝 1) := by
  have h1 : (1:ℂ)∈slitPlane := by simp [slitPlane]
  have hd : HasDerivAt (fun q : ℝ => (q:ℂ)^c) c 1 := by
    have := (Complex.hasStrictDerivAt_cpow_const (c := c) h1).hasDerivAt
    simpa using this.comp_ofReal
  simpa using hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

/-- Every unilateral series takes the value `1` at the origin. -/
lemma qaR4_qPhi_zero (a b : List ℂ) (q : ℂ) : qPhi a b q 0=1 := by
  unfold qPhi
  rw [tsum_eq_single 0]
  · simp [qPhiTerm,qPochhammerList,DLMF.QSeries.TripleProduct.tri,
      List.map_const',List.prod_replicate]
  · intro n hn
    simp [qPhiTerm,zero_pow hn]

/-- One q-derivative step for the `₂φ₁` series. -/
lemma qaR4_qDeriv_phi21 {a b c q d w : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hc : QDenominatorRegular [c] q) (hw : w≠0) (hdw : ‖d*w‖<1) :
    (qPhi [a,b] [c] q (d*w)-qPhi [a,b] [c] q (d*(q*w)))/((1-q)*w)=
      (1-a)*(1-b)*d/((1-c)*(1-q))*qPhi [a*q,b*q] [c*q] q (d*w) := by
  have hdqw : ‖d*(q*w)‖<1 := by
    rw [show d*(q*w)=q*(d*w) by ring,norm_mul]
    calc ‖q‖*‖d*w‖ ≤ 1*‖d*w‖ := by gcongr
      _ < 1 := by linarith
  have hq1 : (1:ℂ)-q≠0 := one_sub_ne_zero_of_norm_lt_one hq
  have h1 := qaR4_phi21_hasSum (a := a) (b := b) hq0 hq hdw hc
  have h2 := qaR4_phi21_hasSum (a := a) (b := b) hq0 hq hdqw hc
  have h3 := qaR4_hasSum_shift ((qaR4_phi21_hasSum (a := a*q) (b := b*q) hq0 hq hdw
    (qaR4_reg_mul_q hc)).mul_left ((1-a)*(1-b)*d/((1-c)*(1-q))))
  refine ((h1.sub h2).div_const ((1-q)*w)).unique (h3.congr_fun ?_)
  have hc1 := qaR4_reg_one_sub_ne hc
  intro n
  cases n with
  | zero => simp [qaR4_shift]
  | succ n =>
    simp only [qaR4_shift]
    have hcc := qaR4_reg_poch_ne hq (qaR4_reg_mul_q hc) n
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
lemma qaR4_hasDerivAt_phi21_zero {a b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hc : QDenominatorRegular [c] q) :
    HasDerivAt (qPhi [a,b] [c] q) ((1-a)*(1-b)/((1-c)*(1-q))) 0 := by
  have han := qPhi_analytic_disc (a := [a,b]) (b := [c]) hq0 hq hc (by simp) 0 (by simp)
  have hd := han.differentiableAt.hasDerivAt
  have h1 := qPhi_iteratedDeriv_zero (a := [a,b]) (b := [c]) hq0 hq hc (by simp) 1
  rw [iteratedDeriv_one] at h1
  rw [h1] at hd
  convert hd using 1
  simp [qPhiCoeff,qaR4_phi21_term,qPochhammer_one]

/-- The iterated q-derivative of `w ↦ ₂φ₁(dw)` on the whole disc `‖dw‖<1`. -/
lemma qaR4_qDerivIterate_phi21 {a b c d q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
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
    have hcq := qaR4_reg_one_sub_ne hck
    have hcc := qaR4_reg_poch_ne hq hc k
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
      have hD := ((qaR4_hasDerivAt_phi21_zero (a := a*q^k) (b := b*q^k) hq0 hq hck).comp_of_eq
        (0:ℂ) ((hasDerivAt_id (0:ℂ)).const_mul d) (by simp)).const_mul
        (qPochhammerList [a,b] q k*d^k/(qPochhammer c q k*(1-q)^k))
      simp only [Function.comp_def,mul_one,id] at hD
      rw [hD.deriv,mul_zero,qaR4_qPhi_zero]
      ring
    · rw [qDerivExtended_of_ne_zero hw0,qDeriv,ih w hw,ih (q*w) (by
        rw [show d*(q*w)=q*(d*w) by ring,norm_mul]
        calc ‖q‖*‖d*w‖ ≤ 1*‖d*w‖ := by gcongr
          _ < 1 := by linarith),mul_div_assoc,← mul_sub,mul_div_assoc,
        qaR4_qDeriv_phi21 hq0 hq hck hw0 hw,hpar,hpar,hpar]
      ring

/-- The `₂φ₁` series with all parameters shifted by `q^j`, premultiplied by its leading factors. -/
lemma qaR4_phi21_hasSum_shiftpar {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hc : QDenominatorRegular [c] q) (j : ℕ) :
    HasSum (fun m : ℕ => qPochhammer a q (m+j)*qPochhammer b q (m+j)/
      (qPochhammer c q (m+j)*qPochhammer q q m)*z^m)
      (qPochhammer a q j*qPochhammer b q j/qPochhammer c q j*qPhi [a*q^j,b*q^j] [c*q^j] q z) := by
  have hcj : QDenominatorRegular [c*q^j] q := by
    intro x hx n
    simp only [List.mem_singleton] at hx
    subst hx
    simpa [pow_add,mul_assoc] using hc c (by simp) (j+n)
  have hcc := qaR4_reg_poch_ne hq hc j
  refine ((qaR4_phi21_hasSum (a := a*q^j) (b := b*q^j) hq0 hq hz hcj).mul_left
    (qPochhammer a q j*qPochhammer b q j/qPochhammer c q j)).congr_fun ?_
  intro m
  rw [Nat.add_comm m j,qPochhammer_add a,qPochhammer_add b,qPochhammer_add c]
  have hcm := qaR4_reg_poch_ne hq hcj m
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
  rw [qPhi_terminates (a := []) hq0 hq n (by simp [QDenominatorRegularThrough,qPochhammerList]),
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

/-- The `1φ1` summation `1φ1(a;c;q,c/a) = (c/a;q)_∞/(c;q)_∞` (DLMF 17.5.E5). -/
@[dlmf 17.5.E5]
theorem one_phi_one_sum {a c q : ℂ} (ha : a≠0) (hq : ‖q‖<1) (hc : QDenominatorRegular [c] q) :
    qPhi [a] [c] q (c/a)=qPochhammerInf (c/a) q/qPochhammerInf c q := by
  sorry

/-- The product quotient is analytic on its regular set, by Mathlib analytic composition/division. -/
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

/-- The first q-Chu–Vandermonde sum `2φ1(a,q^(-n);c;q,c q^n/a) = (c/a;q)_n/(c;q)_n` (DLMF
17.6.E2). -/
@[dlmf 17.6.E2]
theorem q_chu_vandermonde_first {a c q : ℂ} (ha : a≠0) (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hc : QDenominatorRegularThrough [c] q n) :
    qPhi [a,q^(-(n:ℤ))] [c] q (c*q^n/a)=qPochhammer (c/a) q n/qPochhammer c q n := by
  have hcn : qPochhammer c q n≠0 := by simpa [QDenominatorRegularThrough,qPochhammerList] using hc
  rw [eq_div_iff hcn,qaR4_qPhi_swap21]
  by_cases hc0 : c=0
  · subst hc0
    rw [qPhi_terminates (a := [a]) hq0 hq n
      (by simp [QDenominatorRegularThrough, qPochhammerList]), qPhiPartial, sum_range_succ']
    simp [qaR4_phi21_term]
  rw [qaR4_sum_chu hq0 hq hc0 hcn]
  have hz : -(c*q^n/a*q^(-(n:ℤ)))=-c/a := by
    rw [zpow_neg,zpow_natCast]; field_simp
  rw [hz]
  have hterm : ∀ k ∈ range (n+1), qBinom q n k*qPochhammer a q k*qPochhammer (q^(1-(n:ℤ))/c) q (n-k)*
      (-c/a)^k*(-c)^(n-k)=(-c)^n*(a^n)⁻¹*(qBinom q n k*qPochhammer a q k*
        qPochhammer (q^(1-(n:ℤ))/c) q (n-k)*a^(n-k)) := by
    intro k hk
    have hkn : k≤n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hkn
    rw [Nat.add_sub_cancel_left,div_pow,pow_add a,pow_add (-c)]
    field_simp
  rw [sum_congr rfl hterm,← mul_sum,qaR4_vandermonde_poly']
  have hy : a*(q^(1-(n:ℤ))/c)≠0 := mul_ne_zero ha (div_ne_zero (zpow_ne_zero _ hq0) hc0)
  rw [qPochhammer_reverse hy hq0]
  have hy' : q^(1-(n:ℤ))/(a*(q^(1-(n:ℤ))/c))=c/a := by field_simp
  rw [hy']
  have hq1 : (q^(n.choose 2))^2*(q^(1-(n:ℤ)))^n=1 := by
    rw [← zpow_natCast (q^(1-(n:ℤ))),← zpow_mul,← pow_mul,← zpow_natCast q,← zpow_add₀ hq0]
    have h2 := qaR4_choose_two_mul n
    rw [show (((n.choose 2*2:ℕ)):ℤ)+(1-(n:ℤ))*(n:ℤ)=0 by
      have : ((n.choose 2*2:ℕ):ℤ)=(n:ℤ)*n-n := by
        rw [show n.choose 2*2=n*n-n by omega]; push_cast [Nat.le_mul_self n]; ring
      rw [this]; ring,zpow_zero]
  generalize q^(1-(n:ℤ)) = X at hq1 hy ⊢
  generalize q^(n.choose 2) = T at hq1 ⊢
  rw [neg_pow (a*(X/c)),mul_pow a,div_pow X c]
  have hs : (-1:ℂ)^n*(-1:ℂ)^n=1 := by rw [← mul_pow]; norm_num
  field_simp
  linear_combination (c^n*qPochhammer (c/a) q n)*(((-1:ℂ)^n*(-1:ℂ)^n)*hq1+hs)

/-- The cleared product retains the regular upper parameter a=0. -/
@[dlmf 17.6.E3]
theorem q_chu_vandermonde_second {a c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hc : QDenominatorRegularThrough [c] q n) :
    qPhi [a,q^(-(n:ℤ))] [c] q q=((range n).prod (fun j => a-c*q^j))/qPochhammer c q n := by
  have hcn : qPochhammer c q n≠0 := by simpa [QDenominatorRegularThrough,qPochhammerList] using hc
  rw [eq_div_iff hcn,qaR4_qPhi_swap21]
  by_cases hc0 : c=0
  · subst hc0
    let F : ℂ → ℂ := fun c => qPhiPartial [q^(-(n:ℤ)),a] [c] q q n*qPochhammer c q n
    let G : ℂ → ℂ := fun c => (range n).prod (fun j => a-c*q^j)
    have hF : ContinuousAt F 0 := by
      apply ContinuousAt.mul _ (continuous_qPochhammer q n).continuousAt
      unfold ContinuousAt qPhiPartial
      apply tendsto_finsetSum
      intro k _
      have h : ContinuousAt (fun c : ℂ => qPhiTerm [q^(-(n:ℤ)),a] [c] q q k) 0 := by
        simp only [qaR4_phi21_term]
        apply ContinuousAt.mul _ continuousAt_const
        apply ContinuousAt.div continuousAt_const
        · exact ((continuous_qPochhammer q k).mul continuous_const).continuousAt
        · simpa using qPochhammer_self_ne_zero hq k
      exact h
    have hG : ContinuousAt G 0 := by
      apply Continuous.continuousAt
      fun_prop
    have hev : ∀ᶠ c in 𝓝[≠] (0:ℂ), F c=G c := by
      have h1 : ∀ᶠ c in 𝓝 (0:ℂ), qPochhammer c q n≠0 :=
        (continuous_qPochhammer q n).continuousAt.eventually_ne hcn
      filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds h1] with c hc0 hcn'
      simp only [F,G]
      rw [← qPhi_terminates (a := [a]) hq0 hq n (by simpa [QDenominatorRegularThrough,
        qPochhammerList] using hcn')]
      exact qaR4_chu_second_ne hq0 hq n hc0 hcn'
    have := qaR4_eq_at_zero_of_punctured hF hG hev
    simp only [F,G] at this
    rw [qPhi_terminates (a := [a]) hq0 hq n (by simp [QDenominatorRegularThrough,
      qPochhammerList])]
    exact this
  exact qaR4_chu_second_ne hq0 hq n hc0 hcn

/-- The phase-free coefficients are bounded because the finite factorials have nonzero limiting denominators. -/
private lemma qGauss_coefficient_bound {a c q : ℂ} (hq : ‖q‖ < 1)
    (hc : QDenominatorRegular [c] q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖qPochhammer a q n / (qPochhammer c q n * qPochhammer q q n)‖ ≤ C := by
  have hc0 : qPochhammerInf c q ≠ 0 := qPochhammerInf_ne_zero hq fun n he =>
    hc c (by simp) n (sub_eq_zero.mp he).symm
  have hq0 : qPochhammerInf q q ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hq hq
  have ht := (tendsto_qPochhammer (w := a) hq).div
    ((tendsto_qPochhammer (w := c) hq).mul (tendsto_qPochhammer (w := q) hq))
    (mul_ne_zero hc0 hq0)
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ ht).exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun n => ?_⟩
  exact (hC _ ⟨n, rfl⟩).trans (le_max_left _ _)

/-- Reciprocal upper parameters turn the finite shifted factorial into a Newton polynomial. -/
private lemma qGauss_newton_product {q w : ℂ} (hw : w ≠ 0) (n : ℕ) :
    (∏ j ∈ range n, (w - q ^ j)) = w ^ n * qPochhammer w⁻¹ q n := by
  rw [qPochhammer_eq_prod, show w ^ n = ∏ _j ∈ range n, w by simp,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  field_simp

/-- The Newton series equals two-phi-one at every nonzero reciprocal upper parameter. -/
private lemma qGauss_newton_eq_phi {a c q w : ℂ} (hw : w ≠ 0) :
    (∑' n : ℕ, (qPochhammer a q n / (qPochhammer c q n * qPochhammer q q n) *
      (c / a) ^ n) * ∏ j ∈ range n, (w - q ^ j)) =
      qPhi [a, w⁻¹] [c] q (c * w / a) := by
  unfold qPhi
  apply tsum_congr
  intro n
  rw [qaR4_phi21_term, qGauss_newton_product hw]
  rw [show c * w / a = c / a * w by ring, mul_pow]
  ring

/-- The reciprocal-parameter Newton series is analytic throughout its convergence disc. -/
private lemma qGauss_analytic_newton {a c q : ℂ} (hq : ‖q‖ < 1) (hca : c / a ≠ 0)
    (hc : QDenominatorRegular [c] q) :
    AnalyticOnNhd ℂ (fun w => ∑' n : ℕ,
      (qPochhammer a q n / (qPochhammer c q n * qPochhammer q q n) * (c / a) ^ n) *
        ∏ j ∈ range n, (w - q ^ j)) (Metric.ball 0 ‖c / a‖⁻¹) := by
  obtain ⟨C, hC, hbound⟩ := qGauss_coefficient_bound hq hc
  apply Complex.analyticOnNhd_tsum_geometricNewton hq hC (norm_pos_iff.mpr hca)
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hbound n) (by positivity)

/-- The q-Gauss product quotient is analytic on the same reciprocal-parameter disc. -/
private lemma qGauss_analytic_product {a c q : ℂ} (hq : ‖q‖ < 1)
    (hc : QDenominatorRegular [c] q) :
    AnalyticOnNhd ℂ (fun w => qPochhammerInf (c / a) q * qPochhammerInf (c * w) q /
      (qPochhammerInf c q * qPochhammerInf (c / a * w) q))
      (Metric.ball 0 ‖c / a‖⁻¹) := by
  intro w hw
  have hw' : ‖c / a * w‖ < 1 := by
    rw [norm_mul]
    by_cases hca : c / a = 0
    · simp [hca]
    have hw' : ‖w‖ < ‖c / a‖⁻¹ := by simpa using hw
    have h := mul_lt_mul_of_pos_left hw' (norm_pos_iff.mpr hca)
    rwa [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hca)] at h
  apply AnalyticAt.div
    (analyticAt_const.mul ((qPochhammerInf_analytic hq _ (mem_univ _)).comp
      (analyticAt_const.mul analyticAt_id)))
    (analyticAt_const.mul ((qPochhammerInf_analytic hq _ (mem_univ _)).comp
      (analyticAt_const.mul analyticAt_id)))
  exact mul_ne_zero (qPochhammerInf_ne_zero hq fun n he =>
    hc c (by simp) n (sub_eq_zero.mp he).symm)
    (qPochhammerInf_ne_zero_of_norm_lt_one hw' hq)

/-- Terminating q-Chu values accumulate at zero and determine the analytic q-Gauss identity. -/
private lemma qGauss_nonzero {a b c q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc0 : c ≠ 0) (hz : ‖c‖ < ‖a * b‖)
    (hc : QDenominatorRegular [c] q) :
    qPhi [a,b] [c] q (c/(a*b)) =
      qPochhammerListInf [c/a,c/b] q / qPochhammerListInf [c,c/(a*b)] q := by
  let F : ℂ → ℂ := fun w => ∑' n : ℕ,
    (qPochhammer a q n / (qPochhammer c q n * qPochhammer q q n) * (c / a) ^ n) *
      ∏ j ∈ range n, (w - q ^ j)
  let G : ℂ → ℂ := fun w => qPochhammerInf (c / a) q * qPochhammerInf (c * w) q /
    (qPochhammerInf c q * qPochhammerInf (c / a * w) q)
  have hca : c / a ≠ 0 := div_ne_zero hc0 ha
  have hR : 0 < ‖c / a‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hca)
  have hF : AnalyticOnNhd ℂ F (Metric.ball 0 ‖c / a‖⁻¹) := qGauss_analytic_newton hq hca hc
  have hG : AnalyticOnNhd ℂ G (Metric.ball 0 ‖c / a‖⁻¹) := qGauss_analytic_product hq hc
  have hpow : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 (0 : ℂ)) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
  have hev : ∀ᶠ n : ℕ in atTop, F (q ^ n) = G (q ^ n) := by
    have hsmall : ∀ᶠ n : ℕ in atTop, ‖c / a * q ^ n‖ < 1 := by
      have ht' : Tendsto (fun n : ℕ => c / a * q ^ n) atTop (𝓝 (0 : ℂ)) := by
        simpa using hpow.const_mul (c / a)
      have he : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < 1 := by
        have he := Metric.ball_mem_nhds (0 : ℂ) (zero_lt_one : (0 : ℝ) < 1)
        change ∀ᶠ z : ℂ in 𝓝 0, z ∈ Metric.ball 0 1 at he
        simpa only [Metric.mem_ball, dist_zero_right] using he
      exact ht'.eventually he
    filter_upwards [hsmall] with n hn
    have hcn : qPochhammer c q n ≠ 0 := qaR4_reg_poch_ne hq hc n
    have htail : qPochhammerInf (c / a * q ^ n) q ≠ 0 :=
      qPochhammerInf_ne_zero_of_norm_lt_one hn hq
    have htail' : qPochhammerInf (c * q ^ n / a) q ≠ 0 := by
      simpa only [show c * q ^ n / a = c / a * q ^ n by ring] using htail
    have hctail : qPochhammerInf (c * q ^ n) q ≠ 0 :=
      qPochhammerInf_shift_ne_zero hq (fun k he => hc c (by simp) k
        (sub_eq_zero.mp he).symm) n
    dsimp only [F, G]
    rw [qGauss_newton_eq_phi (pow_ne_zero n hq0)]
    have hchu := q_chu_vandermonde_first ha hq0 hq n
      (show QDenominatorRegularThrough [c] q n by
        simpa only [QDenominatorRegularThrough, qPochhammerList, List.map_singleton,
          List.prod_singleton] using hcn)
    rw [zpow_neg, zpow_natCast] at hchu
    rw [hchu, qPochhammerInf_mul_qPochhammer (a := c / a) hq n,
      qPochhammerInf_mul_qPochhammer (a := c) hq n]
    field_simp [htail']
  have hpunct : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝[≠] (0 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpow, Eventually.of_forall fun n => by
      simpa using pow_ne_zero n hq0⟩
  have heq := hF.eqOn_of_preconnected_of_frequently_eq hG
    (convex_ball (0 : ℂ) ‖c / a‖⁻¹).isPreconnected (by simpa using hR)
    (hpunct.frequently hev.frequently)
  have hw : b⁻¹ ∈ Metric.ball 0 ‖c / a‖⁻¹ := by
    simp only [Metric.mem_ball, dist_zero_right, norm_inv, norm_div, norm_mul] at hz ⊢
    rw [inv_lt_inv₀ (norm_pos_iff.mpr hb) (div_pos (norm_pos_iff.mpr hc0)
      (norm_pos_iff.mpr ha))]
    exact (div_lt_iff₀ (norm_pos_iff.mpr ha)).mpr (by simpa [mul_comm] using hz)
  have h := heq hw
  dsimp only [F, G] at h
  rw [qGauss_newton_eq_phi (inv_ne_zero hb), inv_inv] at h
  simpa only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, show c * b⁻¹ = c / b by ring,
    show c / b / a = c / (a * b) by ring,
    show c / a * b⁻¹ = c / (a * b) by ring] using h

/-- At base zero, a nonempty finite shifted factorial retains only its first factor. -/
private lemma qGauss_poch_zero_base (a : ℂ) (n : ℕ) : qPochhammer a 0 (n + 1) = 1 - a := by
  rw [qPochhammer_eq_prod, prod_range_succ']
  simp

/-- At base zero, q-Gauss reduces to summing a geometric tail. -/
private lemma qGauss_zero_base {a b c : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hz : ‖c‖ < ‖a * b‖) (hc : QDenominatorRegular [c] 0) :
    qPhi [a,b] [c] 0 (c/(a*b)) =
      qPochhammerListInf [c/a,c/b] 0 / qPochhammerListInf [c,c/(a*b)] 0 := by
  let z := c / (a * b)
  have hz' : ‖z‖ < 1 := by
    dsimp [z]
    rw [norm_div, div_lt_one₀ (norm_pos_iff.mpr (mul_ne_zero ha hb))]
    exact hz
  have hc1 : 1 - c ≠ 0 := by
    intro he
    exact hc c (by simp) 0 (by simpa using (sub_eq_zero.mp he).symm)
  have hz1 : 1 - z ≠ 0 := one_sub_ne_zero_of_norm_lt_one hz'
  let A := (1 - a) * (1 - b) / (1 - c)
  have htail : HasSum (fun n : ℕ => qPhiTerm [a,b] [c] 0 z (n + 1))
      (A * z * (1 - z)⁻¹) := by
    convert (hasSum_geometric_of_norm_lt_one hz').mul_left (A * z) using 1
    ext n
    rw [qaR4_phi21_term]
    simp only [qGauss_poch_zero_base, sub_zero, mul_one, pow_succ]
    dsimp [A]
    ring
  have hsum := htail.zero_add
  have hzero : qPhiTerm [a,b] [c] 0 z 0 = 1 := by simp [qaR4_phi21_term]
  rw [hzero] at hsum
  change (∑' n : ℕ, qPhiTerm [a,b] [c] 0 z n) = _
  rw [hsum.tsum_eq]
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, DLMF.QSeries.TripleProduct.qPochhammerInf_zero_right]
  change 1 + A * z * (1 - z)⁻¹ = (1 - c / a) * (1 - c / b) / ((1 - c) * (1 - z))
  dsimp only [A]
  field_simp
  dsimp only [z]
  field_simp
  ring

/-- The q-Gauss sum `2φ1(a,b;c;q,c/(ab)) = (c/a,c/b;q)_∞/(c,c/(ab);q)_∞` for `|c| < |ab|` (DLMF
17.6.E1). -/
@[dlmf 17.6.E1]
theorem q_gauss {a b c q : ℂ} (hq : ‖q‖<1) (hz : ‖c‖<‖a*b‖)
    (hc : QDenominatorRegular [c] q) :
    qPhi [a,b] [c] q (c/(a*b))=qPochhammerListInf [c/a,c/b] q/qPochhammerListInf [c,c/(a*b)] q := by
  have hab : a * b ≠ 0 := norm_pos_iff.mp ((norm_nonneg c).trans_lt hz)
  have ha := left_ne_zero_of_mul hab
  have hb := right_ne_zero_of_mul hab
  by_cases hc0 : c = 0
  · subst hc0
    simp [qPhi_zero, qPochhammerListInf]
  by_cases hq0 : q = 0
  · subst hq0
    exact qGauss_zero_base ha hb hz hc
  exact qGauss_nonzero hq0 hq ha hb hc0 hz hc

/-- The cancelled product form retains b=±q^(-m) whenever the left series is regular. -/
@[dlmf 17.6.E4]
theorem q_even_heine {b c q : ℂ} (hb : b≠0) (hc0 : c≠0) (hq : ‖q‖<1) (hz : ‖c*q‖<‖b^2‖)
    (hc : QDenominatorRegular [c] (q^2)) :
    qPhi [b^2,b^2/c] [c] (q^2) (c*q/b^2)=
      qPochhammerInf q (q^2)/(2*qPochhammerListInf [c,c*q/b^2] (q^2))*
        (qPochhammerInf (-b) q*qPochhammerInf (c/b) q+
         qPochhammerInf b q*qPochhammerInf (-c/b) q) := by
  sorry

/-- A base-`q²` summation of `2φ1(b²,b²/c;cq²;q²,cq³/b²)` as a combination of infinite products
(DLMF 17.6.E4, E5). -/
@[dlmf 17.6.E4_5]
theorem q_odd_heine {b c q : ℂ} (hb : b≠0) (hc0 : c≠0) (hq : ‖q‖<1) (hz : ‖c*q^3‖<‖b^2‖)
    (hc : QDenominatorRegular [c*q^2] (q^2))
    (hd : qPochhammerInf (c*q/b^2) (q^2)≠0) :
    qPhi [b^2,b^2/c] [c*q^2] (q^2) (c*q^3/b^2)=
      qPochhammerInf q (q^2)/(2*b*qPochhammerListInf [c*q^2,c*q/b^2] (q^2))*
        (qPochhammerInf (-b) q*qPochhammerInf (c*q/b) q-
         qPochhammerInf b q*qPochhammerInf (-c*q/b) q) := by
  sorry

/-- The only additional common product zero inside the stated convergence domain is handled as a removable limit. -/
@[dlmf 17.6.E4_5]
theorem q_odd_heine_removable {b q : ℂ} (hb : b≠0) (hq0 : q≠0) (hq : ‖q‖<1)
    (hc : QDenominatorRegular [b^2*q] (q^2)) :
    Tendsto (fun c : ℂ => qPochhammerInf q (q^2)/(2*b*qPochhammerListInf [c*q^2,c*q/b^2] (q^2))*
      (qPochhammerInf (-b) q*qPochhammerInf (c*q/b) q-
       qPochhammerInf b q*qPochhammerInf (-c*q/b) q))
      (𝓝[≠] (b^2/q)) (𝓝 (qPhi [b^2,q] [b^2*q] (q^2) (q^2))) := by
  sorry

/-- The Bailey–Daum q-Kummer sum `2φ1(a,b;aq/b;q,-q/b)` as a product of infinite q-shifted
factorials (DLMF 17.6.E5). -/
@[dlmf 17.6.E5]
theorem q_bailey_daum {a b q : ℂ} (hq : ‖q‖<1) (hb : ‖q‖<‖b‖)
    (hc : QDenominatorRegular [a*q/b] q) :
    qPhi [a,b] [a*q/b] q (-q/b)=qPochhammerInf (-q) q*
      qPochhammerListInf [a*q,a*q^2/b^2] (q^2)/qPochhammerListInf [-q/b,a*q/b] q := by
  sorry

/-- Heine's first transformation of `2φ1(a,b;c;q,z)` into a multiple of `2φ1(c/b,z;az;q,b)` (DLMF
17.6.E6). -/
@[dlmf 17.6.E6]
theorem heine_first {a b c q z : ℂ} (hq : ‖q‖<1) (hz : ‖z‖<1) (hb : ‖b‖<1) (hb0 : b≠0)
    (hc : QDenominatorRegular [c,a*z] q) :
    qPhi [a,b] [c] q z=qPochhammerListInf [b,a*z] q/qPochhammerListInf [c,z] q*
      qPhi [c/b,z] [a*z] q b := by
  rw [qPhi_eq_basicHG (by simp),qPhi_eq_basicHG (by simp)]
  simpa [qPochhammerListInf] using DLMF.QSeries.heine_transformation hq hz hb hb0
    (hc c (by simp)) (hc (a*z) (by simp))

/-- Heine's second transformation of `2φ1(a,b;c;q,z)` into a multiple of `2φ1(abz/c,b;bz;q,c/b)`
(DLMF 17.6.E7). -/
@[dlmf 17.6.E7]
theorem heine_second {a b c q z : ℂ} (hq : ‖q‖<1) (hz : ‖z‖<1) (hc0 : c≠0) (hcb : ‖c‖<‖b‖)
    (hc : QDenominatorRegular [c,b*z] q) :
    qPhi [a,b] [c] q z=qPochhammerListInf [c/b,b*z] q/qPochhammerListInf [c,z] q*
      qPhi [a*b*z/c,b] [b*z] q (c/b) := by
  sorry

/-- Heine's third transformation: `2φ1(a,b;c;q,z) = (abz/c;q)_∞/(z;q)_∞ 2φ1(c/a,c/b;c;q,abz/c)`
(DLMF 17.6.E8). -/
@[dlmf 17.6.E8]
theorem heine_third {a b c q z : ℂ} (ha : a≠0) (hb : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hc0 : c≠0) (habz : ‖a*b*z‖<‖c‖) (hc : QDenominatorRegular [c] q) :
    qPhi [a,b] [c] q z=qPochhammerInf (a*b*z/c) q/qPochhammerInf z q*
      qPhi [c/a,c/b] [c] q (a*b*z/c) := by
  sorry

/-- Fine's first expansion of `2φ1(q,aq;bq;q,z)` (DLMF 17.6.E9). -/
@[dlmf 17.6.E9]
theorem heine_fine_expansion {a b q z : ℂ} (hb0 : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [b*q,a*z*q^2/b,a*q/b] q) :
    qPhi [q,a*q] [b*q] q z= -(1-b)*(a*q/b)/(1-a*q/b)*
      (∑' n : ℕ, qPochhammerList [a*q,a*z*q/b] q n*q^n/qPochhammer (a*z*q^2/b) q n)+
      qPochhammerListInf [a*q,a*z*q/b] q/qPochhammerInf (a*q/b) q*qPhi [q,0] [b*q] q z := by
  sorry

/-- Fine's second expansion: `(1-z) 2φ1(q,aq;bq;q,z)` as a series in `(b/a;q)_n (-az)^n
q^(n(n+1)/2)` (DLMF 17.6.E10). -/
@[dlmf 17.6.E10]
theorem heine_fine_expansion_second {a b q z : ℂ} (ha : a≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [b*q] q) :
    (1-z)*qPhi [q,a*q] [b*q] q z=
      ∑' n : ℕ, qPochhammer (b/a) q n*(-a*z)^n*q^((n*(n+1))/2)/qPochhammerList [b*q,z*q] q n := by
  sorry

/-- Fine's third expansion of `(1-z)/(1-b) 2φ1(q,aq;bq;q,z)` (DLMF 17.6.E11). -/
@[dlmf 17.6.E11]
theorem heine_fine_expansion_third {a b q z : ℂ} (hb0 : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1) (hb : ‖b‖<1)
    (hd : QDenominatorRegular [b*q,a*q/b] q) :
    (1-z)/(1-b)*qPhi [q,a*q] [b*q] q z=
      (∑' n : ℕ, qPochhammer (a*q) q n*qPochhammer (a*z*q/b) q (2*n)*b^n/qPochhammerList [z*q,a*q/b] q n)-
      a*q*∑' n : ℕ, qPochhammer (a*q) q n*qPochhammer (a*z*q/b) q (2*n+1)*(b*q)^n/
        (qPochhammer (z*q) q n*qPochhammer (a*q/b) q (n+1)) := by
  sorry

/-- Fine's fourth expansion of `(1-z) 2φ1(q,aq;bq;q,z)` as a well-poised type series (DLMF
17.6.E12). -/
@[dlmf 17.6.E12]
theorem heine_fine_expansion_fourth {a b q z : ℂ} (hb0 : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [b*q] q) :
    (1-z)*qPhi [q,a*q] [b*q] q z=∑' n : ℕ,
      qPochhammerList [a*q,a*z*q/b] q n/qPochhammerList [b*q,z*q] q n*
        (1-a*z*q^(2*n+1))*(b*z)^n*q^(n*n) := by
  sorry

/-- A nonterminating summation combining two `2φ1` series at argument `q` into infinite products
(DLMF 17.6.E13). -/
@[dlmf 17.6.E13]
theorem heine_nonterminating_sum {a b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hc0 : c≠0)
    (hd : QDenominatorRegular [c,q^2/c,c/q,a*q/c,b*q/c] q) :
    qPhi [a,b] [c] q q+qPochhammerListInf [q/c,a,b] q/qPochhammerListInf [c/q,a*q/c,b*q/c] q*
      qPhi [a*q/c,b*q/c] [q^2/c] q q=qPochhammerListInf [q/c,a*b*q/c] q/qPochhammerListInf [a*q/c,b*q/c] q := by
  sorry

/-- A mixed-base transformation between a series in bases `q` and `q²` and a `2φ1` in base `q²`
(DLMF 17.6.E14). -/
@[dlmf 17.6.E14]
theorem heine_mixed_base {a b q z : ℂ} (hq : ‖q‖<1)
    (hd : QDenominatorRegular [a*z*b,b*z] (q^2))
    (hD : qPochhammerListInf [z,a*z*b] (q^2)≠0)
    (hL : Summable (fun n : ℕ => qPochhammer a q n*qPochhammer b (q^2) n*z^n/
      (qPochhammer q q n*qPochhammer (a*z*b) (q^2) n)))
    (hR : Summable (qPhiTerm [a,b] [b*z] (q^2) (z*q))) :
    (∑' n : ℕ, qPochhammer a q n*qPochhammer b (q^2) n*z^n/
      (qPochhammer q q n*qPochhammer (a*z*b) (q^2) n))=
      qPochhammerListInf [a*z,b*z] (q^2)/qPochhammerListInf [z,a*z*b] (q^2)*qPhi [a,b] [b*z] (q^2) (z*q) := by
  sorry

/-- The first three-term connection formula for `2φ1(a,b;c;q,z)` (DLMF 17.6.E15). -/
@[dlmf 17.6.E15]
theorem heine_connection_first {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (habcz : a*b*c*z≠0) (hbc : ‖b*q‖<‖c‖)
    (hd : QDenominatorRegular [c,c*q/(a*z),q^2/c,a*z/c,q/a,c/q,b*q/c] q) :
    qPhi [a,b] [c] q z=qPochhammerListInf [a*b*z/c,q/c] q/qPochhammerListInf [a*z/c,q/a] q*
      qPhi [c/a,c*q/(a*b*z)] [c*q/(a*z)] q (b*q/c)-
      qPochhammerListInf [b,q/c,c/a,a*z/q,q^2/(a*z)] q/
        qPochhammerListInf [c/q,b*q/c,q/a,a*z/c,c*q/(a*z)] q*qPhi [a*q/c,b*q/c] [q^2/c] q z := by
  sorry

/-- The second three-term connection formula for `2φ1(a,b;c;q,z)`, in terms of `z ↦ cq/(abz)`
(DLMF 17.6.E16). -/
@[dlmf 17.6.E16]
theorem heine_connection_second {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (habcz : a*b*c*z≠0) (harg : ‖c*q‖<‖a*b*z‖)
    (hd : QDenominatorRegular [c,a*q/b,b*q/a,b/a,a/b,z,q/z] q) :
    qPhi [a,b] [c] q z=qPochhammerListInf [b,c/a,a*z,q/(a*z)] q/qPochhammerListInf [c,b/a,z,q/z] q*
      qPhi [a,a*q/c] [a*q/b] q (c*q/(a*b*z))+
      qPochhammerListInf [a,c/b,b*z,q/(b*z)] q/qPochhammerListInf [c,a/b,z,q/z] q*
      qPhi [b,b*q/c] [b*q/a] q (c*q/(a*b*z)) := by
  sorry

/-- Heine's contiguous relation in the lower parameter `c/q` versus `c` (DLMF 17.6.E17). -/
@[dlmf 17.6.E17]
theorem heine_contiguous_17 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c/q] q) :
    qPhi [a,b] [c/q] q z-qPhi [a,b] [c] q z=c*z*(1-a)*(1-b)/((q-c)*(1-c))*qPhi [a*q,b*q] [c*q] q z := by
  have hc := qaR4_reg_of_div_q hq0 hd
  have hc' := qaR4_reg_mul_q hc
  have h1 := qaR4_phi21_hasSum (a := a) (b := b) hq0 hq hz hd
  have h2 := qaR4_phi21_hasSum (a := a) (b := b) hq0 hq hz hc
  have h3 := qaR4_hasSum_shift ((qaR4_phi21_hasSum (a := a*q) (b := b*q) hq0 hq hz hc').mul_left
    (c*z*(1-a)*(1-b)/((q-c)*(1-c))))
  refine (h1.sub h2).unique (h3.congr_fun ?_)
  have hc1 := qaR4_reg_one_sub_ne hc
  have hcq1 := qaR4_reg_one_sub_ne hd
  have hqc : q-c≠0 := by
    intro h; apply hcq1; rw [show c=q by linear_combination -h]; field_simp; ring
  intro n
  cases n with
  | zero => simp [qaR4_shift]
  | succ n =>
    simp only [qaR4_shift]
    have hcc := qaR4_reg_poch_ne hq hc n
    have hcn : 1-c*q^n≠0 := fun h => hc c (by simp) n (by linear_combination -h)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_succ' a,qPochhammer_succ' b,qPochhammer_succ' (c/q),div_mul_cancel₀ _ hq0,
      qPochhammer_succ c,qaR4_poch_mul_q hc1,qPochhammer_succ q,pow_succ z]
    field_simp
    ring

/-- Heine's contiguous relation in the upper parameter `aq` versus `a` (DLMF 17.6.E18). -/
@[dlmf 17.6.E18]
theorem heine_contiguous_18 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    qPhi [a*q,b] [c] q z-qPhi [a,b] [c] q z=a*z*(1-b)/(1-c)*qPhi [a*q,b*q] [c*q] q z := by
  have h1 := qaR4_phi21_hasSum (a := a*q) (b := b) hq0 hq hz hd
  have h2 := qaR4_phi21_hasSum (a := a) (b := b) hq0 hq hz hd
  have hd' := qaR4_reg_mul_q hd
  have h3 := qaR4_hasSum_shift ((qaR4_phi21_hasSum (a := a*q) (b := b*q) hq0 hq hz hd').mul_left
    (a*z*(1-b)/(1-c)))
  refine (h1.sub h2).unique (h3.congr_fun ?_)
  intro n
  cases n with
  | zero => simp [qaR4_shift]
  | succ n =>
    simp only [qaR4_shift]
    have hc1 := qaR4_reg_one_sub_ne hd
    have hcq := qaR4_reg_poch_ne hq hd' n
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_succ (a*q),qPochhammer_succ' a,qPochhammer_succ' b,qPochhammer_succ' c,
      qPochhammer_succ q,pow_succ z]
    field_simp
    ring

/-- Heine's contiguous relation shifting `a` and `c` together (DLMF 17.6.E19). -/
@[dlmf 17.6.E19]
theorem heine_contiguous_19 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    qPhi [a*q,b] [c*q] q z-qPhi [a,b] [c] q z=z*(1-b)*(a-c)/((1-c)*(1-c*q))*qPhi [a*q,b*q] [c*q^2] q z := by
  have hc' := qaR4_reg_mul_q hd
  have hc'' : QDenominatorRegular [c*q^2] q := by
    simpa [pow_two,mul_assoc] using qaR4_reg_mul_q hc'
  have h1 := qaR4_phi21_hasSum (a := a*q) (b := b) hq0 hq hz hc'
  have h2 := qaR4_phi21_hasSum (a := a) (b := b) hq0 hq hz hd
  have h3 := qaR4_hasSum_shift ((qaR4_phi21_hasSum (a := a*q) (b := b*q) hq0 hq hz hc'').mul_left
    (z*(1-b)*(a-c)/((1-c)*(1-c*q))))
  refine (h1.sub h2).unique (h3.congr_fun ?_)
  have hc1 := qaR4_reg_one_sub_ne hd
  have hcq1 := qaR4_reg_one_sub_ne hc'
  intro n
  cases n with
  | zero => simp [qaR4_shift]
  | succ n =>
    simp only [qaR4_shift]
    have hcc := qaR4_reg_poch_ne hq hc' n
    have hcn : 1-c*q*q^n≠0 := fun h => hc' (c*q) (by simp) n (by linear_combination -h)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [show c*q^2=(c*q)*q by ring,qaR4_poch_mul_q hcq1,
      qPochhammer_succ (a*q),qPochhammer_succ' a,qPochhammer_succ' b,qPochhammer_succ (c*q),
      qPochhammer_succ' c,qPochhammer_succ q,pow_succ z]
    generalize qPochhammer (a*q) q n = A
    generalize qPochhammer (b*q) q n = B
    generalize qPochhammer (c*q) q n = C at hcc ⊢
    generalize qPochhammer q q n = P at hqq ⊢
    generalize q^n = Q at hcn hqn ⊢
    generalize hD0 : 1-q*Q = D0 at hqn ⊢
    generalize hD1 : 1-c*q*Q = D1 at hcn ⊢
    generalize hD2 : 1-c*q = D2 at hcq1 ⊢
    generalize hD3 : 1-c = D3 at hc1 ⊢
    field_simp
    simp only [← hD0,← hD1,← hD3]
    ring

/-- Heine's contiguous relation for `(aq, b/q)` versus `(a, b)` (DLMF 17.6.E20). -/
@[dlmf 17.6.E20]
theorem heine_contiguous_20 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    qPhi [a*q,b/q] [c] q z-qPhi [a,b] [c] q z=z*(a-b/q)/(1-c)*qPhi [a*q,b] [c*q] q z := by
  have hc' := qaR4_reg_mul_q hd
  have h1 := qaR4_phi21_hasSum (a := a*q) (b := b/q) hq0 hq hz hd
  have h2 := qaR4_phi21_hasSum (a := a) (b := b) hq0 hq hz hd
  have h3 := qaR4_hasSum_shift ((qaR4_phi21_hasSum (a := a*q) (b := b) hq0 hq hz hc').mul_left
    (z*(a-b/q)/(1-c)))
  refine (h1.sub h2).unique (h3.congr_fun ?_)
  have hc1 := qaR4_reg_one_sub_ne hd
  intro n
  cases n with
  | zero => simp [qaR4_shift]
  | succ n =>
    simp only [qaR4_shift]
    have hcc := qaR4_reg_poch_ne hq hc' n
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_succ (a*q),qPochhammer_succ' a,qPochhammer_succ' (b/q),div_mul_cancel₀ _ hq0,
      qPochhammer_succ b,qPochhammer_succ' c,qPochhammer_succ q,pow_succ z]
    field_simp
    ring

/-- Heine's contiguous relation `b(1-a)φ(aq,b) - a(1-b)φ(a,bq) = (b-a)φ(a,b)` (DLMF 17.6.E21). -/
@[dlmf 17.6.E21]
theorem heine_contiguous_21 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    b*(1-a)*qPhi [a*q,b] [c] q z-a*(1-b)*qPhi [a,b*q] [c] q z=(b-a)*qPhi [a,b] [c] q z := by
  have h1 := (qaR4_phi21_hasSum (a := a*q) (b := b) hq0 hq hz hd).mul_left (b*(1-a))
  have h2 := (qaR4_phi21_hasSum (a := a) (b := b*q) hq0 hq hz hd).mul_left (a*(1-b))
  have h3 := (qaR4_phi21_hasSum (a := a) (b := b) hq0 hq hz hd).mul_left (b-a)
  refine (h1.sub h2).unique (h3.congr_fun ?_)
  intro n
  have ha1 : (1-a)*qPochhammer (a*q) q n=qPochhammer a q n*(1-a*q^n) := by
    rw [← qPochhammer_succ',qPochhammer_succ]
  have hb1 : (1-b)*qPochhammer (b*q) q n=qPochhammer b q n*(1-b*q^n) := by
    rw [← qPochhammer_succ',qPochhammer_succ]
  have hcc := qaR4_reg_poch_ne hq hd n
  have hqq := qPochhammer_self_ne_zero hq n
  field_simp
  linear_combination (b*qPochhammer b q n*z^n)*ha1-(a*qPochhammer a q n*z^n)*hb1

/-- Heine's contiguous relation between `φ(a,b/q)`, `φ(a/q,b)` and `φ(a,b)` (DLMF 17.6.E22). -/
@[dlmf 17.6.E22]
theorem heine_contiguous_22 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    a*(c-b)*qPhi [a,b/q] [c] q z-b*(c-a)*qPhi [a/q,b] [c] q z=(a-b)*(c-a*b*z/q)*qPhi [a,b] [c] q z := by
  have h0 := qaR4_phi21_hasSum (a := a) (b := b) hq0 hq hz hd
  have h1 := (qaR4_phi21_hasSum (a := a) (b := b/q) hq0 hq hz hd).mul_left (a*(c-b))
  have h2 := (qaR4_phi21_hasSum (a := a/q) (b := b) hq0 hq hz hd).mul_left (b*(c-a))
  have h3 := (h0.mul_left ((a-b)*c)).sub (qaR4_hasSum_shift (h0.mul_left ((a-b)*(a*b/q)*z)))
  have key := (h1.sub h2).unique (h3.congr_fun ?_)
  · rw [key]; ring
  intro n
  cases n with
  | zero => simp [qaR4_shift]; ring
  | succ n =>
    simp only [qaR4_shift]
    have hcc := qaR4_reg_poch_ne hq hd n
    have hcn : 1-c*q^n≠0 := fun h => hd c (by simp) n (by linear_combination -h)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_succ' (b/q),qPochhammer_succ' (a/q),div_mul_cancel₀ _ hq0,div_mul_cancel₀ _ hq0,
      qPochhammer_succ a,qPochhammer_succ b,qPochhammer_succ c,qPochhammer_succ q,pow_succ z]
    generalize qPochhammer a q n = A
    generalize qPochhammer b q n = B
    generalize qPochhammer c q n = C at hcc ⊢
    generalize qPochhammer q q n = P at hqq ⊢
    generalize q^n = Q at hcn hqn ⊢
    generalize hD0 : 1-q*Q = D0 at hqn ⊢
    generalize hD1 : 1-c*Q = D1 at hcn ⊢
    field_simp
    simp only [← hD0,← hD1]
    ring

/-- Heine's three-term contiguous relation between `φ(a/q,b)`, `φ(aq,b)` and `φ(a,b)` (DLMF
17.6.E23). -/
@[dlmf 17.6.E23]
theorem heine_contiguous_23 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    q*(c-a)*qPhi [a/q,b] [c] q z+(1-a)*(c-a*b*z)*qPhi [a*q,b] [c] q z=(c*(1+q-a)-a*q+a^2*z-a*b*z)*qPhi [a,b] [c] q z := by
  have h0 := qaR4_phi21_hasSum (a := a) (b := b) hq0 hq hz hd
  have hp := qaR4_phi21_hasSum_pre (a := a) (b := b) hq0 hq hz hd
  have h1 := (qaR4_phi21_hasSum (a := a/q) (b := b) hq0 hq hz hd).mul_left (q*(c-a))
  have hL := (h1.add (hp.mul_left c)).sub (qaR4_hasSum_shift (hp.mul_left (a*b*z)))
  have hR := (h0.mul_left (c*(1+q-a)-a*q)).add (qaR4_hasSum_shift (h0.mul_left ((a^2-a*b)*z)))
  have key := hL.unique (hR.congr_fun ?_)
  · linear_combination key
  intro n
  cases n with
  | zero => simp [qaR4_shift,qPochhammer_one]; ring
  | succ n =>
    simp only [qaR4_shift]
    have hcc := qaR4_reg_poch_ne hq hd n
    have hcn : 1-c*q^n≠0 := fun h => hd c (by simp) n (by linear_combination -h)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_succ' (a/q),div_mul_cancel₀ _ hq0,qPochhammer_succ a q (n+1),
      qPochhammer_succ a q n,qPochhammer_succ b,qPochhammer_succ c,qPochhammer_succ q,pow_succ z]
    generalize qPochhammer a q n = A
    generalize qPochhammer b q n = B
    generalize qPochhammer c q n = C at hcc ⊢
    generalize qPochhammer q q n = P at hqq ⊢
    try simp only [pow_succ q n]
    generalize q^n = Q at hcn hqn ⊢
    generalize hD0 : 1-q*Q = D0 at hqn ⊢
    generalize hD1 : 1-c*Q = D1 at hcn ⊢
    field_simp
    simp only [← hD0,← hD1]
    ring

/-- Heine's three-term contiguous relation between `φ(;c/q)`, `φ(;cq)` and `φ(;c)` (DLMF
17.6.E24). -/
@[dlmf 17.6.E24]
theorem heine_contiguous_24 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c/q] q) :
    (1-c)*(q-c)*(a*b*z-c)*qPhi [a,b] [c/q] q z+z*(c-a)*(c-b)*qPhi [a,b] [c*q] q z=(c-1)*(c*(q-c)+z*(c*a+c*b-a*b-a*b*q))*qPhi [a,b] [c] q z := by
  have hc := qaR4_reg_of_div_q hq0 hd
  have hc' := qaR4_reg_mul_q hc
  have h0 := qaR4_phi21_hasSum (a := a) (b := b) hq0 hq hz hc
  have hm := qaR4_phi21_hasSum (a := a) (b := b) hq0 hq hz hd
  have hp := qaR4_phi21_hasSum (a := a) (b := b) hq0 hq hz hc'
  have hL := ((qaR4_hasSum_shift (hm.mul_left ((1-c)*(q-c)*(a*b)*z))).sub
    (hm.mul_left ((1-c)*(q-c)*c))).add (qaR4_hasSum_shift (hp.mul_left ((c-a)*(c-b)*z)))
  have hR := (h0.mul_left ((c-1)*(c*(q-c)))).add
    (qaR4_hasSum_shift (h0.mul_left ((c-1)*(c*a+c*b-a*b-a*b*q)*z)))
  have key := hL.unique (hR.congr_fun ?_)
  · linear_combination key
  have hc1 := qaR4_reg_one_sub_ne hc
  have hcq1 := qaR4_reg_one_sub_ne hd
  intro n
  cases n with
  | zero => simp [qaR4_shift]; ring
  | succ n =>
    simp only [qaR4_shift]
    obtain ⟨c0,rfl⟩ : ∃ c0, c=c0*q := ⟨c/q,by field_simp⟩
    simp only [mul_div_cancel_right₀ _ hq0] at hd ⊢
    have hcc := qaR4_reg_poch_ne hq hd n
    have hc01 : 1-c0≠0 := qaR4_reg_one_sub_ne hd
    have hcn : 1-c0*q^n≠0 := fun h => hd c0 (by simp) n (by linear_combination -h)
    have hcn' : 1-c0*q*q^n≠0 := fun h => hc (c0*q) (by simp) n (by linear_combination -h)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qaR4_poch_mul_q hc1,qPochhammer_succ (c0*q),qPochhammer_succ c0,qaR4_poch_mul_q hc01,
      qPochhammer_succ a,qPochhammer_succ b,qPochhammer_succ q,pow_succ z]
    generalize qPochhammer a q n = A
    generalize qPochhammer b q n = B
    generalize qPochhammer c0 q n = C at hcc ⊢
    generalize qPochhammer q q n = P at hqq ⊢
    generalize q^n = Q at hcn hcn' hqn ⊢
    generalize hD0 : 1-q*Q = D0 at hqn ⊢
    generalize hD1 : 1-c0*q*Q = D1 at hcn' ⊢
    generalize hD2 : 1-c0*Q = D2 at hcn ⊢
    generalize hD3 : 1-c0*q = D3 at hc1 ⊢
    generalize hD4 : 1-c0 = D4 at hc01 ⊢
    field_simp
    simp only [← hD0,← hD1,← hD2,← hD3,← hD4]
    ring

/-- The `n`-th q-derivative of `z ↦ 2φ1(a,b;c;q,dz)` raises all parameters by `q^n` (DLMF
17.6.E25). -/
@[dlmf 17.6.E25]
theorem heine_qDerivative {a b c d q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖d*z‖<1)
    (hc : QDenominatorRegular [c] q) (n : ℕ) :
    qDerivIterate n q (fun w => qPhi [a,b] [c] q (w*d)) z=
      qPochhammerList [a,b] q n*d^n/(qPochhammer c q n*(1-q)^n)*qPhi [a*q^n,b*q^n] [c*q^n] q (d*z) :=
  qaR4_qDerivIterate_phi21 hq0 hq hc n z hz

/-- The `n`-th q-derivative of `2φ1` weighted by the ratio of infinite products
`(z;q)_∞/(abz/c;q)_∞` (DLMF 17.6.E26). -/
@[dlmf 17.6.E26]
theorem heine_weighted_qDerivative {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1) (hc0 : c≠0)
    (hc : QDenominatorRegular [c] q) (hD : qPochhammerInf (a*b*z/c) q≠0) (n : ℕ) :
    qDerivIterate n q (fun w => qPochhammerInf w q/qPochhammerInf (a*b*w/c) q*qPhi [a,b] [c] q w) z=
      ((range n).prod (fun j => a-c*q^j))*((range n).prod (fun j => b-c*q^j))/
        (c^n*qPochhammer c q n*(1-q)^n)*qPochhammerInf (z*q^n) q/qPochhammerInf (a*b*z/c) q*
        qPhi [a,b] [c*q^n] q (z*q^n) := by
  sorry

/-- The second-order q-differential equation satisfied by `2φ1(a,b;c;q,z)` (DLMF 17.6.E27). -/
@[dlmf 17.6.E27]
theorem heine_qDifferentialEquation {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hc : QDenominatorRegular [c] q) :
    let F := fun w => qPhi [a,b] [c] q w
    z*(c-a*b*q*z)*qDerivIterate 2 q F z+
      ((1-c)/(1-q)+((1-a)*(1-b)-(1-a*b*q))/(1-q)*z)*qDerivExtended q F z-
      (1-a)*(1-b)/(1-q)^2*F z=0 := by
  intro F
  have hF : F=fun w => qPhi [a,b] [c] q (w*1) := funext fun w => by simp [F]
  have hz' : ‖1*z‖<1 := by simpa using hz
  have hD1 : qDerivExtended q F z=qDerivIterate 1 q F z := rfl
  rw [hD1,hF,qaR4_qDerivIterate_phi21 hq0 hq hc 1 z hz',qaR4_qDerivIterate_phi21 hq0 hq hc 2 z hz']
  simp only [mul_one,one_mul,one_pow]
  have h0 := qaR4_phi21_hasSum_shiftpar (a := a) (b := b) hq0 hq hz hc 0
  have h1 := qaR4_phi21_hasSum_shiftpar (a := a) (b := b) hq0 hq hz hc 1
  have h2 := qaR4_phi21_hasSum_shiftpar (a := a) (b := b) hq0 hq hz hc 2
  set S0 := qPochhammer a q 0*qPochhammer b q 0/qPochhammer c q 0*qPhi [a*q^0,b*q^0] [c*q^0] q z
  set S1 := qPochhammer a q 1*qPochhammer b q 1/qPochhammer c q 1*qPhi [a*q^1,b*q^1] [c*q^1] q z
  set S2 := qPochhammer a q 2*qPochhammer b q 2/qPochhammer c q 2*qPhi [a*q^2,b*q^2] [c*q^2] q z
  have hL := ((((qaR4_hasSum_shift (h2.mul_left (c*z))).sub
    (qaR4_hasSum_shift (qaR4_hasSum_shift (h2.mul_left (a*b*q*z^2))))).add
    (h1.mul_left (1-c))).add (qaR4_hasSum_shift (h1.mul_left (((1-a)*(1-b)-(1-a*b*q))*z)))).sub
    (h0.mul_left ((1-a)*(1-b)))
  have hq1 : (1:ℂ)-q≠0 := one_sub_ne_zero_of_norm_lt_one hq
  have hc1 := qaR4_reg_one_sub_ne hc
  have hcq : 1-c*q≠0 := qaR4_reg_one_sub_ne (qaR4_reg_mul_q hc)
  have key := hL.unique (hasSum_zero.congr_fun ?_)
  · have e : z*(c-a*b*q*z)*(qPochhammerList [a,b] q 2/(qPochhammer c q 2*(1-q)^2)*
        qPhi [a*q^2,b*q^2] [c*q^2] q z)+((1-c)/(1-q)+((1-a)*(1-b)-(1-a*b*q))/(1-q)*z)*
        (qPochhammerList [a,b] q 1/(qPochhammer c q 1*(1-q)^1)*qPhi [a*q^1,b*q^1] [c*q^1] q z)-
        (1-a)*(1-b)/(1-q)^2*qPhi [a,b] [c] q z=
        (c*z*S2-a*b*q*z^2*S2+(1-c)*S1+((1-a)*(1-b)-(1-a*b*q))*z*S1-(1-a)*(1-b)*S0)/(1-q)^2 := by
      simp only [S0,S1,S2,qPochhammerList,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
        mul_one,pow_zero,qPochhammer_zero]
      field_simp
      ring
    rw [e,key,zero_div]
  intro n
  rcases n with _ | _ | n
  · simp [qaR4_shift,qPochhammer_one]
    field_simp
    ring
  · simp [qaR4_shift]
    simp only [qPochhammer_succ _ _ 1,qPochhammer_one,pow_one]
    generalize hD0 : 1-q = D0 at hq1 ⊢
    generalize hD1 : 1-c = D1 at hc1 ⊢
    generalize hD2 : 1-c*q = D2 at hcq ⊢
    field_simp
    simp only [← hD0,← hD1,← hD2]
    ring
  · simp only [qaR4_shift]
    have hcc := qaR4_reg_poch_ne hq hc (n+2)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    have hqn1 : 1-q*q^(n+1)≠0 := by
      simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq (n+1)
    have hcn : 1-c*q^(n+2)≠0 := fun h => hc c (by simp) (n+2) (by linear_combination -h)
    rw [show n+1+2=(n+2)+1 by ring,show n+1+1=n+2 by ring,Nat.add_zero,
      qPochhammer_succ a q (n+2),qPochhammer_succ b q (n+2),qPochhammer_succ c q (n+2),
      qPochhammer_succ q q (n+1),qPochhammer_succ q q n]
    generalize qPochhammer a q (n+2) = A
    generalize qPochhammer b q (n+2) = B
    generalize qPochhammer c q (n+2) = C at hcc ⊢
    generalize qPochhammer q q n = P at hqq ⊢
    rw [pow_succ z (n+1),pow_succ z n,show q^(n+2)=q^n*q*q by ring,show q^(n+1)=q^n*q by ring] at *
    generalize q^n = Q at hqn hqn1 hcn ⊢
    generalize hD0 : 1-q*Q = D0 at hqn ⊢
    generalize hD1 : 1-q*(Q*q) = D1 at hqn1 ⊢
    generalize hD2 : 1-c*(Q*q*q) = D2 at hcn ⊢
    field_simp
    simp only [← hD0,← hD1,← hD2]
    ring

/-- As `q → 1⁻`, the iterated q-derivatives of `2φ1(q^a,q^b;q^c;q,z)` tend to the derivatives of
the Gauss function `F(a,b;c;z)`. -/
theorem heine_classical_derivative_limit {a b c z : ℂ} (hc : ∀ n : ℕ, c≠ -(n:ℂ)) (hz : ‖z‖<1) (n : ℕ) :
    Tendsto (fun q : ℝ => qDerivIterate n q
      (fun w => qPhi [(q:ℂ)^a,(q:ℂ)^b] [(q:ℂ)^c] q w) z)
      (𝓝[<] 1) (𝓝 (iteratedDeriv n (ordinaryHypergeometric a b c) z)) := by
  sorry

/-- As `q → 1⁻`, the coefficients of Heine's q-differential equation tend to those of the Gauss
hypergeometric equation. -/
theorem heine_qDifferentialEquation_classical_coefficients (a b c z : ℂ) :
    Tendsto (fun q : ℝ =>
      (z*((q:ℂ)^c-(q:ℂ)^(a+b+1)*z),
       (1-(q:ℂ)^c)/(1-q)+((1-(q:ℂ)^a)*(1-(q:ℂ)^b)-(1-(q:ℂ)^(a+b+1)))/(1-q)*z,
       -(1-(q:ℂ)^a)*(1-(q:ℂ)^b)/(1-q)^2))
      (𝓝[<] 1) (𝓝 (z*(1-z),c-(a+b+1)*z,-a*b)) := by
  have hc := qaR4_tendsto_cpow_one c
  have habc := qaR4_tendsto_cpow_one (a+b+1)
  have hb1 := qaR4_tendsto_cpow_one b
  have nc := qaR4_tendsto_qnum c
  have na := qaR4_tendsto_qnum a
  have nb := qaR4_tendsto_qnum b
  have nabc := qaR4_tendsto_qnum (a+b+1)
  refine Tendsto.prodMk_nhds ?_ (Tendsto.prodMk_nhds ?_ ?_)
  · have h := (hc.sub (habc.mul_const z)).const_mul z
    simpa using h
  · have h := nc.add (((na.mul ((tendsto_const_nhds (x := (1:ℂ))).sub hb1)).sub nabc).mul_const z)
    simp only [sub_self,mul_zero,zero_sub] at h
    convert h using 2 with q
    · by_cases hq : (1:ℂ)-q=0
      · simp [hq]
      field_simp
    · ring
  · have h := (na.mul nb).neg
    convert h using 2 with q
    · by_cases hq : (1:ℂ)-q=0
      · simp [hq]
      field_simp
    · ring

/-- Jackson integral representation of `2φ1(q^a,q^b;q^c;q,z)`, the q-analogue of Euler's integral
(DLMF 17.6.E28). -/
@[dlmf 17.6.E28]
theorem heine_jackson_integral {q : ℝ} (hq0 : 0<q) (hq1 : q<1) {a b c z : ℂ}
    (hb : 0<b.re) (hz : ‖z‖<1)
    (hc : QDenominatorRegular [(q:ℂ)^c,(q:ℂ)^(c-b)] q) :
    qPhi [(q:ℂ)^a,(q:ℂ)^b] [(q:ℂ)^c] q z=
      qGamma q c/(qGamma q b*qGamma q (c-b))*
      jacksonIntegral q 1 (fun t => t^(b-1)*qPochhammerOrder (t*q) q (c-b-1)/qPochhammerOrder (z*t) q a) := by
  sorry

/-- The q-Mellin–Barnes integral representation of `2φ1(a,b;c;q,z)` (DLMF 17.6.E29). -/
@[dlmf 17.6.E29]
theorem heine_mellin_barnes {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz0 : z≠0) (hz : ‖z‖<1)
    (harg : |Complex.arg (-z)|<π) (hc : QDenominatorRegular [c] q)
    (L : ℝ → ℂ) (hL : ContDiff ℝ 1 L) (htail : Complex.HasVerticalTails L)
    (hsep : Complex.SeparatesPoleSets L (qHeineBarnesLeft a b q) qHeineBarnesRight)
    (hleft : Complex.StaysAwayFrom L (qHeineBarnesLeft a b q))
    (hright : Complex.StaysAwayFrom L qHeineBarnesRight) :
    Integrable (fun t : ℝ => qHeineBarnesKernel a b c q z (L t)*deriv L t) ∧
    qPhi [a,b] [c] q z= -1/(2*π*I)*qPochhammerListInf [a,b] q/qPochhammerListInf [q,c] q*
      ∫ t : ℝ, qHeineBarnesKernel a b c q z (L t)*deriv L t := by
  sorry

/-- The one-phi-zero product gives continuation of the actual series germ from zero. -/
theorem one_phi_zero_continues {a q : ℂ} (hq : ‖q‖<1) :
    AnalyticOnNhd ℂ (qOnePhiZeroContinuation a q) {z | qPochhammerInf z q≠0} ∧
    (qPhi [a] [] q=ᶠ[𝓝 0] qOnePhiZeroContinuation a q) ∧
    TauCeti.ContinuesInside (qPhi [a] [] q) {z | qPochhammerInf z q≠0} 0 := by
  have hF := one_phi_zero_continuation_analytic (a := a) hq
  have hcont : Continuous (fun z : ℂ => qPochhammerInf z q) :=
    continuousOn_univ.mp (qPochhammerInf_analytic hq).continuousOn
  have hU : IsOpen {z : ℂ | qPochhammerInf z q≠0} := isOpen_ne_fun hcont continuous_const
  have h0 : (0:ℂ)∈{z : ℂ | qPochhammerInf z q≠0} := by simp [qPochhammerInf]
  have heq : qPhi [a] [] q=ᶠ[𝓝 0] qOnePhiZeroContinuation a q := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ)<1)] with z hz
    simpa only [qOnePhiZeroContinuation] using one_phi_zero (a := a) hq (by simpa using hz)
  exact ⟨hF,heq,qPhi_continuesInside_of_eq hU h0 hF heq⟩

/-- The Jackson representation at Gamma-factor poles is its regular-parameter limit. -/
@[dlmf 17.6.E28]
theorem heine_jackson_parameter_limit {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    {a b c₀ z : ℂ} (hb : 0<b.re) (hz : ‖z‖<1)
    (hc₀ : QDenominatorRegular [(q:ℂ)^c₀] q) :
    Tendsto (fun c : ℂ => qHeineJacksonValue q a b c z)
      (𝓝[{c : ℂ | QDenominatorRegular [(q:ℂ)^c,(q:ℂ)^(c-b)] q}] c₀)
      (𝓝 (qPhi [(q:ℂ)^a,(q:ℂ)^b] [(q:ℂ)^c₀] q z)) := by
  sorry

end DLMF.QHypergeometric
