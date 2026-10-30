/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Convergence
public import DLMF.QSeries.QCalculus
public import DLMF.QSeries.Saalschutz
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# q-calculus adapters and Gaussian coefficients (DLMF §17.2)

The shifted factorials, Gaussian polynomial, Jackson integral and q-derivative reuse
`DLMF.QSeries`. The derivative adapter supplies the removable value at 0 required by DLMF,
while the existing q-derivative remains the operator at every nonzero argument.
Finite-interval and bilateral integrals are the standard adapters around that Jackson API.
The finite Gaussian bridges reuse the proved q-Pochhammer reversal and Mathlib integer-power
laws; phase cancellation is kept valid at every stated natural/integer index.
The modular negative q-product uses Mathlib's Dedekind eta S-transformation,
including its principal complex square-root phase.
Natural partial-sum predicates retain the distinction between conditional convergence and
Lean's totalized, unordered `tsum`.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory Asymptotics
open scoped Real Topology
namespace DLMF.QHypergeometric

/-- Jackson's q-derivative with the derivative value at the origin specified in DLMF. -/
@[dlmf 17.2.E41]
def qDerivExtended (q : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z=0 then deriv f 0 else DLMF.QSeries.qDeriv q f z
/-- The n-fold q-derivative, including its DLMF value at the origin. -/
def qDerivIterate (n : ℕ) (q : ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  (fun g : ℂ → ℂ => qDerivExtended q g)^[n] f
/-- A finite two-endpoint Jackson integral, reusing the existing integral from zero. -/
def jacksonBetween (q a b : ℂ) (f : ℂ → ℂ) : ℂ :=
  DLMF.QSeries.jacksonIntegral q b f-DLMF.QSeries.jacksonIntegral q a f
/-- The bilateral Jackson integral, used only together with convergence hypotheses. -/
@[dlmf 17.2.E48]
def jacksonBilateral (q : ℂ) (f : ℂ → ℂ) : ℂ :=
  (1-q)*∑' n : ℤ, q^n*f (q^n)
/-- Natural-order convergence of the finite-interval Jackson series, permitting conditional sums. -/
def HasNaturalJacksonIntegral (q a : ℂ) (f : ℂ → ℂ) (v : ℂ) : Prop :=
  Tendsto (fun N : ℕ => a*(1-q)*∑ j∈range N, f (a*q^j)*q^j) atTop (𝓝 v)
/-- Bilateral natural convergence means convergence of both tails separately. -/
def HasNaturalJacksonBilateral (q : ℂ) (f : ℂ → ℂ) (v : ℂ) : Prop :=
  ∃ vp vm : ℂ,
    Tendsto (fun N : ℕ => ∑ j∈range N, q^j*f (q^j)) atTop (𝓝 vp) ∧
    Tendsto (fun N : ℕ => ∑ j∈range N, q^(-(j:ℤ)-1)*f (q^(-(j:ℤ)-1))) atTop (𝓝 vm) ∧
    v=(1-q)*(vp+vm)

/-- Away from the origin the existing q-derivative is reused exactly. -/
theorem qDerivExtended_of_ne_zero {z : ℂ} (hz : z≠0) (q : ℂ) (f : ℂ → ℂ) :
    qDerivExtended q f z=DLMF.QSeries.qDeriv q f z := by simp [qDerivExtended,hz]
/-- The value at the origin is the ordinary derivative, rather than division by zero. -/
theorem qDerivExtended_zero (q : ℂ) (f : ℂ → ℂ) : qDerivExtended q f 0=deriv f 0 := by
  simp [qDerivExtended]

open DLMF.QSeries

/-- Integer-upper Gaussian coefficient, extending the existing natural-upper polynomial. -/
def qBinomialInt (q : ℂ) (n : ℤ) (m : ℕ) : ℂ :=
  qPochhammer (q^(n-(m:ℤ)+1)) q m/qPochhammer q q m

/-- The principal complex square root on the positive imaginary axis separates its phase. -/
private lemma qModular_sqrt_imag {y : ℝ} (hy : 0 < y) :
    Complex.sqrt (I*(y:ℂ)) = Complex.sqrt I * (Real.sqrt y : ℂ) := by
  rw [Complex.sqrt_eq_real_add_ite, Complex.sqrt_I]
  simp only [mul_re, mul_im, Complex.I_re, Complex.I_im, ofReal_re, ofReal_im, zero_mul, one_mul,
    mul_zero, sub_zero, zero_add, norm_mul, norm_I, Complex.norm_real,
    Real.norm_of_nonneg hy.le, ite_eq_left hy.le, add_zero, sub_zero, one_mul]
  rw [Real.sqrt_div hy.le]
  have hs : (Real.sqrt (2:ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  rw [Real.sqrt_inv]
  push_cast
  field_simp

/-- The Dedekind eta product at an imaginary argument is a q-Pochhammer product. -/
private lemma qModular_eta_exp (t : ℝ) :
    ModularForm.eta (I*(t:ℂ)/(2*π)) =
      Complex.exp (-(t:ℂ)/24)*qPochhammerInf (Complex.exp (-(t:ℂ))) (Complex.exp (-(t:ℂ))) := by
  unfold ModularForm.eta Function.Periodic.qParam
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  have he : 2*π*I*(I*(t:ℂ)/(2*π)) = -(t:ℂ) := by field_simp; simp [I_sq]
  rw [he]
  congr 1
  unfold qPochhammerInf
  apply tprod_congr
  intro n
  rw [ModularForm.eta_q_eq_pow, he, pow_succ']

/-- Mathlib's eta S-transformation on the imaginary axis has a positive real square-root factor. -/
private lemma qModular_eta_imag_inv {y : ℝ} (hy : 0 < y) :
    ModularForm.eta (I/(y:ℂ)) = (Real.sqrt y : ℂ)*ModularForm.eta (I*(y:ℂ)) := by
  have h := ModularForm.eta_comp_eq_csqrt_I_inv
    (by simpa using hy : I*(y:ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet)
  simp only [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h
  have he : -1/(I*(y:ℂ)) = I/(y:ℂ) := by field_simp; simp [I_sq,div_eq_mul_inv]
  rw [he,qModular_sqrt_imag hy] at h
  have hs : Complex.sqrt I ≠ 0 := by simp [Complex.sqrt]
  simpa only [←mul_assoc,inv_mul_cancel₀ hs,one_mul] using h

/-- A negative real exponential has complex norm less than one. -/
private lemma qModular_norm_exp_neg {t : ℝ} (ht : 0<t) : ‖Complex.exp (-(t:ℂ))‖ < 1 := by
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  simpa using neg_lt_zero.mpr ht

/-- The factors of a q-Pochhammer product are multipliable inside the unit disk. -/
private lemma qModular_multipliable (a q : ℂ) (hq : ‖q‖<1) :
    Multipliable (fun n : ℕ => 1-a*q^n) := by
  simpa only [sub_eq_add_neg] using
    multipliable_one_add_of_summable (f := fun n : ℕ => -(a*q^n))
      (by simpa only [norm_neg,norm_mul,norm_pow] using
        (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖a‖)

/-- Multiplying the positive and negative q-products doubles their exponents. -/
private lemma qModular_negative_split {q : ℂ} (hq : ‖q‖<1) :
    qPochhammerInf (-q) q*qPochhammerInf q q = qPochhammerInf (q^2) (q^2) := by
  unfold qPochhammerInf
  rw [← (qModular_multipliable (-q) q hq).tprod_mul (qModular_multipliable q q hq)]
  apply tprod_congr
  intro n
  rw [pow_right_comm q 2 n]
  ring

/-- The even and odd factors split a q-product into two products with squared base. -/
private lemma qModular_positive_split {q : ℂ} (hq : ‖q‖<1) :
    qPochhammerInf q q = qPochhammerInf q (q^2)*qPochhammerInf (q^2) (q^2) := by
  unfold qPochhammerInf
  have hq2 : ‖q^2‖ < 1 := by
    simpa only [norm_pow] using
      pow_lt_one₀ (norm_nonneg q) hq (by norm_num : (2:ℕ)≠0)
  have he : Multipliable (fun k : ℕ => 1-q*q^(2*k)) := by
    simpa only [pow_mul] using qModular_multipliable q (q^2) hq2
  have ho : Multipliable (fun k : ℕ => 1-q*q^(2*k+1)) := by
    convert qModular_multipliable (q^2) (q^2) hq2 using 1
    funext k
    rw [pow_succ,pow_mul]
    ring
  have h := tprod_even_mul_odd (f := fun n : ℕ => 1-q*q^n) he ho
  rw [← h]
  congr 1
  · apply tprod_congr
    intro n
    rw [pow_mul]
  · apply tprod_congr
    intro n
    rw [pow_succ,pow_mul]
    ring

/-- The modular transformation of `(-e^(-t);e^(-t))_∞` for `t > 0`, relating it to a product in
the base `e^(-4π²/t)` (DLMF 17.2.E6, second relation). -/
@[dlmf 17.2.E6_2]
theorem qPochhammer_negative_modular {t : ℝ} (ht : 0<t) :
    qPochhammerInf (-Complex.exp (-(t:ℂ))) (Complex.exp (-(t:ℂ)))=
      (Real.sqrt 2:ℂ)⁻¹*Complex.exp ((π:ℂ)^2/(12*t)+t/24)*
        qPochhammerInf (Complex.exp (-2*(π:ℂ)^2/t)) (Complex.exp (-4*(π:ℂ)^2/t)) := by
  let r : ℝ := 2*π^2/t
  have hr : 0<r := by dsimp [r]; positivity
  have hpi : (π:ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  have ht0 : (t:ℂ)≠0 := ofReal_ne_zero.mpr ht.ne'
  have hc1 : I/((t/(2*π):ℝ):ℂ) = I*((2*r:ℝ):ℂ)/(2*π) := by
    dsimp [r]; push_cast; field_simp
  have hc2 : I/((t/π:ℝ):ℂ) = I*(r:ℂ)/(2*π) := by
    dsimp [r]; push_cast; field_simp
  have hc3 : I*((t/π:ℝ):ℂ) = I*((2*t:ℝ):ℂ)/(2*π) := by
    push_cast; field_simp
  have hc4 : I*((t/(2*π):ℝ):ℂ) = I*(t:ℂ)/(2*π) := by push_cast; ring
  have h1 := qModular_eta_imag_inv (y := t/(2*π)) (by positivity)
  have h2 := qModular_eta_imag_inv (y := t/π) (by positivity)
  rw [hc1,hc4,qModular_eta_exp,qModular_eta_exp] at h1
  rw [hc2,hc3,qModular_eta_exp,qModular_eta_exp] at h2
  have hs : Real.sqrt (t/π) = Real.sqrt 2*Real.sqrt (t/(2*π)) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]; congr 1; field_simp
  rw [hs] at h2
  let q := Complex.exp (-(t:ℂ))
  let p := Complex.exp (-(r:ℂ))
  have hqt : Complex.exp (-((2*t:ℝ):ℂ)) = q^2 := by
    dsimp [q]; rw [← exp_nat_mul]; congr 1; push_cast; ring
  have hpr : Complex.exp (-((2*r:ℝ):ℂ)) = p^2 := by
    dsimp [p]; rw [← exp_nat_mul]; congr 1; push_cast; ring
  rw [hpr] at h1
  rw [hqt] at h2
  have hneg := qModular_negative_split (qModular_norm_exp_neg ht)
  have hpos := qModular_positive_split (qModular_norm_exp_neg hr)
  change qPochhammerInf (-q) q*qPochhammerInf q q = qPochhammerInf (q^2) (q^2) at hneg
  change qPochhammerInf p p = qPochhammerInf p (p^2)*qPochhammerInf (p^2) (p^2) at hpos
  rw [←hneg,hpos] at h2
  have he1 : Complex.exp (-((2*r:ℝ):ℂ)/24) = Complex.exp (-(r:ℂ)/24)^2 := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  have he2 : Complex.exp (-((2*t:ℝ):ℂ)/24) = Complex.exp (-(t:ℂ)/24)^2 := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  rw [he1] at h1
  rw [he2,ofReal_mul] at h2
  have hA : qPochhammerInf q q ≠ 0 :=
    qPochhammerInf_ne_zero_of_norm_lt_one (qModular_norm_exp_neg ht) (qModular_norm_exp_neg ht)
  have ha : (Real.sqrt (t/(2*π)):ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (div_pos ht (mul_pos (by norm_num) Real.pi_pos))).ne'
  have H : (Real.sqrt 2:ℂ)*Complex.exp (-(r:ℂ)/24)*Complex.exp (-(t:ℂ)/24)*qPochhammerInf (-q) q =
      qPochhammerInf p (p^2) := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero ha (exp_ne_zero (-(t:ℂ)/24))) hA)
    linear_combination qPochhammerInf p (p^2)*h1-Complex.exp (-(r:ℂ)/24)*h2
  have hs2 : (Real.sqrt 2:ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have hex : Complex.exp ((π:ℂ)^2/(12*t)+t/24) =
      (Complex.exp (-(r:ℂ)/24)*Complex.exp (-(t:ℂ)/24))⁻¹ := by
    rw [← exp_add,← exp_neg]; congr 1; dsimp [r]; push_cast; field_simp; ring
  have hp1 : Complex.exp (-2*(π:ℂ)^2/t) = p := by
    dsimp [p,r]; congr 1; push_cast; ring
  have hp2 : Complex.exp (-4*(π:ℂ)^2/t) = p^2 := by
    rw [←hpr]; dsimp [p,r]; congr 1; push_cast; ring
  rw [hp1,hp2,hex]
  change qPochhammerInf (-q) q = _
  apply mul_left_cancel₀
    (mul_ne_zero (mul_ne_zero hs2 (exp_ne_zero (-(r:ℂ)/24))) (exp_ne_zero (-(t:ℂ)/24)))
  rw [H]
  field_simp

/-- The Gaussian binomial coefficient as a ratio of q-factorials: `[n,m]_q = (q;q)_n/((q;q)_m
(q;q)_(n-m))` (DLMF 17.2.E27). -/
@[dlmf 17.2.E27]
theorem qBinom_ratio {q : ℂ} (hq : ‖q‖<1) {m n : ℕ} (hm : m≤n) :
    qBinom q n m=qPochhammer q q n/(qPochhammer q q m*qPochhammer q q (n-m)) := by
  have h := qBinom_mul_qPochhammer q m (n-m)
  rw [Nat.add_sub_of_le hm] at h
  apply (eq_div_iff (mul_ne_zero (qPochhammer_self_ne_zero hq m)
    (qPochhammer_self_ne_zero hq (n-m)))).2
  simpa [mul_assoc] using h

/-- The Gaussian binomial coefficient in terms of `(q^(-n);q)_m`, the form used in terminating
series (DLMF 17.2.E27). -/
@[dlmf 17.2.E27]
theorem qBinom_terminating_ratio {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) {m n : ℕ} (hm : m≤n) :
    qBinom q n m=qPochhammer (q^(-(n:ℤ))) q m*(-1:ℂ)^m*
      q^((n:ℤ)*m-(m.choose 2:ℤ))/qPochhammer q q m := by
  have hB := qBinom_eq hq m (n-m)
  rw [Nat.add_sub_of_le hm] at hB
  rw [hB,qPochhammer_reverse (a := q^(-(n:ℤ))) (zpow_ne_zero _ hq0) hq0]
  have harg : q^(1-(m:ℤ))/q^(-(n:ℤ))=q*q^(n-m) := by
    rw [← zpow_sub₀ hq0,show (1-(m:ℤ))-(-(n:ℤ))=((n-m+1:ℕ):ℤ) by omega,zpow_natCast,pow_succ]
    ring
  rw [harg]
  have hs : (-1:ℂ)^m*(-1:ℂ)^m=1 := by rw [← mul_pow]; norm_num
  have hp : (q^(-(n:ℤ)))^m*q^(m.choose 2)*q^((n:ℤ)*m-(m.choose 2:ℤ))=1 := by
    calc
      _ = q^((-(n:ℤ))*(m:ℤ)+(m.choose 2:ℤ)+((n:ℤ)*m-(m.choose 2:ℤ))) := by
        simp only [zpow_add₀ hq0,zpow_mul,zpow_natCast]
      _ = 1 := by rw [show (-(n:ℤ))*(m:ℤ)+(m.choose 2:ℤ)+((n:ℤ)*m-(m.choose 2:ℤ))=0 by ring,zpow_zero]
  have hf : (-q^(-(n:ℤ)))^m*q^(m.choose 2)*(-1:ℂ)^m*q^((n:ℤ)*m-(m.choose 2:ℤ))=1 := by
    rw [neg_pow]
    calc
      _ = ((-1:ℂ)^m*(-1:ℂ)^m)*((q^(-(n:ℤ)))^m*q^(m.choose 2)*q^((n:ℤ)*m-(m.choose 2:ℤ))) := by ring
      _ = 1 := by rw [hs,hp]; norm_num
  linear_combination (norm := ring_nf) -(qPochhammer (q*q^(n-m)) q m/qPochhammer q q m)*hf

/-- At natural upper index the integer-indexed q-binomial coefficient agrees with the Gaussian
polynomial. -/
theorem qBinomialInt_nat {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n m : ℕ) :
    qBinomialInt q n m=qBinom q n m := by
  unfold qBinomialInt
  by_cases hm : m≤n
  · rw [show (n:ℤ)-(m:ℤ)+1=((n-m+1:ℕ):ℤ) by omega,zpow_natCast]
    simpa [Nat.add_sub_of_le hm,pow_succ,mul_comm] using (qBinom_eq hq m (n-m)).symm
  · have hmn : n<m := by omega
    rw [qBinom_eq_zero_of_lt q hmn]
    rw [show (n:ℤ)-(m:ℤ)+1= -((m-n-1:ℕ):ℤ) by omega]
    rw [zpow_neg,zpow_natCast,qPochhammer_recip_pow_eq_zero hq0 (by omega : m-n-1<m),zero_div]

/-- The q-binomial coefficient with negative upper index `-n` in terms of `[m+n-1,m]_q` (DLMF
17.2.E30). -/
@[dlmf 17.2.E30]
theorem qBinomialInt_negative {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) {n : ℕ} (hn : 0<n) (m : ℕ) :
    qBinomialInt q (-(n:ℤ)) m=qBinom q (m+n-1) m*(-1:ℂ)^m*
      q^(-(m:ℤ)*n-(m.choose 2:ℤ)) := by
  let N := m+n-1
  have hmN : m≤N := by dsimp [N]; omega
  have hN : (N:ℤ)=(m:ℤ)+(n:ℤ)-1 := by dsimp [N]; omega
  unfold qBinomialInt
  rw [show -(n:ℤ)-(m:ℤ)+1= -(N:ℤ) by omega]
  rw [qBinom_terminating_ratio hq0 hq hmN]
  have hs : (-1:ℂ)^m*(-1:ℂ)^m=1 := by rw [← mul_pow]; norm_num
  have htri : (m.choose 2:ℤ)*2=(m:ℤ)*((m:ℤ)-1) := by
    have h := DLMF.QSeries.TripleProduct.tri_mul_two (m:ℤ)
    have ht : DLMF.QSeries.TripleProduct.tri (m:ℤ)=(m.choose 2:ℤ) := by
      simpa using (DLMF.QSeries.TripleProduct.tri_sub_cast m 0).symm
    rw [ht] at h
    exact h
  have hexp : ((N:ℤ)*m-(m.choose 2:ℤ))+(-(m:ℤ)*n-(m.choose 2:ℤ))=0 := by
    rw [hN]
    nlinarith
  have hf : (-1:ℂ)^m*q^((N:ℤ)*m-(m.choose 2:ℤ))*(-1:ℂ)^m*q^(-(m:ℤ)*n-(m.choose 2:ℤ))=1 := by
    calc
      _ = ((-1:ℂ)^m*(-1:ℂ)^m)*(q^((N:ℤ)*m-(m.choose 2:ℤ))*q^(-(m:ℤ)*n-(m.choose 2:ℤ))) := by ring
      _ = 1 := by rw [hs,← zpow_add₀ hq0,hexp,zpow_zero]; norm_num
  linear_combination (norm := ring_nf) -(qPochhammer (q^(-(N:ℤ))) q m/qPochhammer q q m)*hf

/-- The second q-Pascal recurrence `[n+m+1,m+1]_q = [n+m,m+1]_q + q^n [n+m,m]_q` (DLMF 17.2.E32). -/
@[dlmf 17.2.E32]
theorem qBinom_pascal_second (q : ℂ) (n m : ℕ) :
    qBinom q (n+m+1) (m+1)=qBinom q (n+m) (m+1)+q^n*qBinom q (n+m) m := by
  simpa using DLMF.QSeries.qBinom_succ_succ' q (n+m) m

/-- For `|q| < 1` and fixed `m`, the Gaussian binomial `[n,m]_q` tends to `1/(q;q)_m` as `n → ∞`
(DLMF 17.2.E33). -/
@[dlmf 17.2.E33]
theorem qBinom_fixed_lower_limit {q : ℂ} (hq : ‖q‖<1) (m : ℕ) :
    Tendsto (fun n : ℕ => qBinom q n m) atTop (𝓝 (qPochhammer q q m)⁻¹) := by
  apply (tendsto_add_atTop_iff_nat m).1
  have hp := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).const_mul q
  have hc := (continuous_qPochhammer q m).continuousAt.tendsto.comp hp
  have h := hc.div_const (qPochhammer q q m)
  simp only [mul_zero,qPochhammer_zero_param,one_div] at h
  refine h.congr' (Eventually.of_forall fun n => ?_)
  simpa only [Function.comp_apply,Nat.add_comm n m] using (qBinom_eq hq m n).symm

/-- Both Gaussian indices tend to infinity; s>0 is necessary (s=0 gives a different fixed-index limit). -/
@[dlmf 17.2.E34]
theorem qBinom_two_growing_indices {q : ℂ} (hq : ‖q‖<1) {r s : ℕ} (hs : 0<s) (hrs : s<r)
    (u t : ℕ) : Tendsto (fun n : ℕ => qBinom q (r*n+u) (s*n+t)) atTop
      (𝓝 (qPochhammerInf q q)⁻¹) := by
  have hP := qPochhammerInf_ne_zero_of_norm_lt_one hq hq
  have htop : Tendsto (fun n : ℕ => r*n+u) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by nlinarith⟩
  have hbot : Tendsto (fun n : ℕ => s*n+t) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by nlinarith⟩
  have hdiff : Tendsto (fun n : ℕ => (r*n+u)-(s*n+t)) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b+t, fun n hn => by
      have : b+(s*n+t)≤r*n+u := by nlinarith
      omega⟩
  have hlim := ((tendsto_qPochhammer (w := q) hq).comp htop).div
    (((tendsto_qPochhammer (w := q) hq).comp hbot).mul ((tendsto_qPochhammer (w := q) hq).comp hdiff))
    (mul_ne_zero hP hP)
  have hval : qPochhammerInf q q/(qPochhammerInf q q*qPochhammerInf q q)=
      (qPochhammerInf q q)⁻¹ := by field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop t] with n hn
  exact (qBinom_ratio hq (by nlinarith : s*n+t≤r*n+u)).symm

-- DLMF 17.2.E36 is Mathlib `add_pow` specialized to -z and 1; see MathlibCoverage.

/-- The q-binomial series `∑_n [n+m,n]_q z^n = 1/(z;q)_(m+1)` for `|z| < 1` (DLMF 17.2.E38). -/
@[dlmf 17.2.E38]
theorem q_binomial_series {q z : ℂ} (hq : ‖q‖<1) (hz : ‖z‖<1) (m : ℕ) :
    HasSum (fun n : ℕ => qBinom q (n+m) n*z^n) (qPochhammer z q (m+1))⁻¹ := by
  have hs := (summable_q_binomial_series (a := q*q^m) hq hz).hasSum
  rw [← q_binomial_theorem hq hz] at hs
  have hshift := qPochhammerInf_mul_qPochhammer (a := z) hq (m+1)
  have hi := qPochhammerInf_ne_zero_of_norm_lt_one hz hq
  have htail := qPochhammerInf_shift_ne_zero hq
    (fun j => one_sub_mul_pow_ne_zero_of_norm hz hq j) (m+1)
  have hprod := qPochhammer_ne_zero_of_factors hq
    (fun j => one_sub_mul_pow_ne_zero_of_norm hz hq j) (m+1)
  have hv : qPochhammerInf ((q*q^m)*z) q/qPochhammerInf z q=
      (qPochhammer z q (m+1))⁻¹ := by
    rw [show (q*q^m)*z=z*q^(m+1) by rw [pow_succ]; ring]
    rw [hshift]
    field_simp
  rw [hv] at hs
  simpa [qBinom_eq hq] using hs

/-- The Jackson integral to `q^{-n}` as a tail sum of the bilateral series. -/
lemma qaR4_jackson_neg_pow {q : ℂ} (hq0 : q≠0) (f : ℂ → ℂ) (n : ℕ) :
    jacksonIntegral q (q^(-(n:ℤ))) f=(1-q)*∑' k : ℤ,
      (if -(n:ℤ)≤k then q^k*f (q^k) else 0) := by
  unfold jacksonIntegral
  have hinj : Function.Injective (fun j : ℕ => (j:ℤ)-n) := fun i j h => by simpa using h
  rw [← hinj.tsum_eq]
  · rw [mul_comm (q^(-(n:ℤ))),mul_assoc,← tsum_mul_left]
    congr 1
    apply tsum_congr
    intro j
    simp only [show -(n:ℤ)≤(j:ℤ)-n by omega,ite_true]
    have e : q^(-(n:ℤ))*q^j=q^((j:ℤ)-n) := by
      rw [← zpow_natCast q j,← zpow_add₀ hq0]; congr 1; ring
    rw [← e]
    ring
  · intro k hk
    simp only [Function.mem_support,ne_eq,ite_eq_right_iff,not_forall] at hk
    obtain ⟨hk,_⟩ := hk
    exact ⟨(k+n).toNat,by simp; omega⟩

/-- A finite Jackson sum to `q^{-n}` split into its negative part and a positive partial sum. -/
lemma qaR4_jackson_partial_split {q : ℂ} (hq0 : q≠0) (f : ℂ → ℂ) (n M : ℕ) :
    q^(-(n:ℤ))*(1-q)*∑ j∈range (n+M), f (q^(-(n:ℤ))*q^j)*q^j=
      (1-q)*((∑ i∈range n, q^(-(i:ℤ)-1)*f (q^(-(i:ℤ)-1)))+∑ j∈range M, q^j*f (q^j)) := by
  have e : ∀ j : ℕ, q^(-(n:ℤ))*q^j=q^((j:ℤ)-n) := fun j => by
    rw [← zpow_natCast q j,← zpow_add₀ hq0]; congr 1; ring
  have e2 : ∀ j : ℕ, q^(-(n:ℤ))*(f (q^(-(n:ℤ))*q^j)*q^j)=q^((j:ℤ)-n)*f (q^((j:ℤ)-n)) := by
    intro j; rw [← e j]; ring
  rw [mul_comm (q^(-(n:ℤ))),mul_assoc,mul_sum,sum_congr rfl (fun j _ => e2 j)]
  congr 1
  rw [sum_range_add]
  congr 1
  · rw [← sum_range_reflect]
    apply sum_congr rfl
    intro i hi
    have hin : i<n := mem_range.mp hi
    have : ((n-1-i:ℕ):ℤ)-n= -(i:ℤ)-1 := by omega
    rw [this]
  · apply sum_congr rfl
    intro j _
    have : ((n+j:ℕ):ℤ)-n=(j:ℤ) := by push_cast; ring
    rw [this,zpow_natCast]

/-- The coefficient in the finite-difference form of the iterated q-derivative. -/
noncomputable def qaR4_fdCoeff (q : ℂ) (n j : ℕ) : ℂ :=
  q^(-(n:ℤ)*j+((j+1).choose 2:ℤ))*(-1:ℂ)^j*qBinom q n j

/-- The q-Pascal step for the finite-difference coefficients. -/
lemma qaR4_fdCoeff_succ {q : ℂ} (hq0 : q≠0) (n j : ℕ) :
    qaR4_fdCoeff q (n+1) (j+1)=-(q^(-(n:ℤ))*qaR4_fdCoeff q n j)+qaR4_fdCoeff q n (j+1) := by
  simp only [qaR4_fdCoeff,qBinom_succ_succ]
  have h1 : q^(-((n+1:ℕ):ℤ)*((j+1:ℕ):ℤ)+((j+1+1).choose 2:ℤ))=
      q^(-(n:ℤ))*q^(-(n:ℤ)*j+((j+1).choose 2:ℤ)) := by
    rw [← zpow_add₀ hq0]; congr 1
    rw [Nat.choose_succ_succ' (j+1),Nat.choose_one_right]; push_cast; ring
  have h2 : q^(-((n+1:ℕ):ℤ)*((j+1:ℕ):ℤ)+((j+1+1).choose 2:ℤ))*q^(j+1)=
      q^(-(n:ℤ)*((j+1:ℕ):ℤ)+((j+1+1).choose 2:ℤ)) := by
    rw [← zpow_natCast q (j+1),← zpow_add₀ hq0]; congr 1; push_cast; ring
  rw [← h2,h1,pow_succ]
  ring

/-- The coefficient recursion behind 17.2.E42. -/
lemma qaR4_fdCoeff_sum {q : ℂ} (hq0 : q≠0) (F : ℕ → ℂ) (n : ℕ) :
    ∑ j∈range (n+1+1), qaR4_fdCoeff q (n+1) j*F j=
      ∑ j∈range (n+1), qaR4_fdCoeff q n j*F j-
        q^(-(n:ℤ))*∑ j∈range (n+1), qaR4_fdCoeff q n j*F (j+1) := by
  have h0 : ∀ m : ℕ, qaR4_fdCoeff q m 0=1 := fun m => by simp [qaR4_fdCoeff]
  have hl : qaR4_fdCoeff q n (n+1)=0 := by
    simp [qaR4_fdCoeff,qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)]
  rw [sum_range_succ',sum_congr rfl (fun j _ => by rw [qaR4_fdCoeff_succ hq0 n j]),h0]
  have e : ∑ j∈range (n+1), qaR4_fdCoeff q n j*F j=
      ∑ j∈range (n+1), qaR4_fdCoeff q n (j+1)*F (j+1)+1*F 0 := by
    rw [← h0 n,← sum_range_succ' (fun j => qaR4_fdCoeff q n j*F j),
      sum_range_succ (fun k => qaR4_fdCoeff q n k*F k) (n+1),hl]
    ring
  rw [e,mul_sum,← sub_add_eq_add_sub,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro j _
  ring

/-- Symmetry of the Gaussian polynomial `[n,k]=[n,n-k]`, for every `q`. -/
theorem qaR4_qBinom_symm (q : ℂ) (k m : ℕ) : qBinom q (k+m) k=qBinom q (k+m) m := by
  induction h : k+m generalizing k m with
  | zero => obtain ⟨rfl,rfl⟩ : k=0 ∧ m=0 := by omega
            rfl
  | succ n ih =>
    rcases k with _ | k
    · simp only [Nat.zero_add] at h; subst h; simp
    rcases m with _ | m
    · obtain rfl : k=n := by omega
      simp
    have h1 := ih k (m+1) (by omega)
    have h2 := ih (k+1) m (by omega)
    rw [qBinom_succ_succ,h1,h2,qBinom_succ_succ',show n-m=k+1 by omega]

/-- Gaussian polynomials are entire functions of the base. -/
lemma qaR4_qBinom_differentiable (n k : ℕ) : Differentiable ℂ (fun q : ℂ => qBinom q n k) := by
  induction n generalizing k with
  | zero => cases k <;> exact differentiable_const _
  | succ n ih =>
    cases k with
    | zero => exact differentiable_const _
    | succ k =>
      simp only [qBinom_succ_succ]
      exact (ih k).add ((differentiable_id.pow _).mul (ih (k+1)))

/-- An identity between entire functions of `q` that holds for `‖q‖<1` holds for all `q`. -/
lemma qaR4_entire_eq_of_disc {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ q : ℂ, ‖q‖<1 → f q=g q) (q : ℂ) : f q=g q := by
  have hfg : AnalyticOnNhd ℂ (f-g) univ := fun z _ => (hf.sub hg).analyticAt z
  have hev : (f-g)=ᶠ[𝓝 0] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) one_pos] with z hz
    simp [h z (by simpa using hz)]
  have := hfg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ 0) hev
    (mem_univ q)
  simpa [sub_eq_zero] using this

/-- The absorption identity `(1-q^{j+1})[m+1,j+1]=(1-q^{m+1})[m,j]`, for every `q`. -/
theorem qaR4_qBinom_absorb (q : ℂ) (m j : ℕ) :
    (1-q^(j+1))*qBinom q (m+1) (j+1)=(1-q^(m+1))*qBinom q m j := by
  rcases lt_or_ge m j with hjm | hjm
  · rw [qBinom_eq_zero_of_lt q (by omega : m+1<j+1),qBinom_eq_zero_of_lt q hjm]; ring
  apply qaR4_entire_eq_of_disc (f := fun q => (1-q^(j+1))*qBinom q (m+1) (j+1))
    (g := fun q => (1-q^(m+1))*qBinom q m j)
  · exact (by fun_prop : Differentiable ℂ fun q : ℂ => 1-q^(j+1)).mul (qaR4_qBinom_differentiable _ _)
  · exact (by fun_prop : Differentiable ℂ fun q : ℂ => 1-q^(m+1)).mul (qaR4_qBinom_differentiable _ _)
  intro q hq
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hjm
  have h1 := qBinom_mul_qPochhammer q (j+1) l
  have h2 := qBinom_mul_qPochhammer q j l
  have hj := qPochhammer_self_ne_zero hq j
  have hl := qPochhammer_self_ne_zero hq l
  rw [show j+1+l=j+l+1 by ring,qPochhammer_succ q q j,qPochhammer_succ q q (j+l)] at h1
  apply mul_right_cancel₀ (mul_ne_zero hj hl)
  rw [show j+l+1=j+1+l by ring] at h1 ⊢
  rw [show j+1+l=j+l+1 by ring] at h1 ⊢
  rw [← h2] at h1
  rw [show q^(j+1)=q*q^j by ring,show q^(j+l+1)=q*q^(j+l) by ring]
  linear_combination h1

/-- The alternating Gaussian sum `T_m=∑(-1)^j[m,j]`. -/
lemma qaR4_alt_sum_rec (q : ℂ) (m : ℕ) :
    ∑ j∈range (m+2+1), (-1:ℂ)^j*qBinom q (m+2) j=
      (1-q^(m+1))*∑ j∈range (m+1), (-1:ℂ)^j*qBinom q m j := by
  have hc : ∀ j : ℕ, qBinom q (m+2) (j+1)=qBinom q (m+1) (j+1)+qBinom q (m+1) j-
      (1-q^(m+1))*qBinom q m j := by
    intro j
    rw [← qaR4_qBinom_absorb q m j,qBinom_succ_succ]
    ring
  rw [sum_range_succ',sum_congr rfl (fun j _ => by rw [hc j])]
  have e1 : ∑ j∈range (m+2), (-1:ℂ)^(j+1)*qBinom q (m+1) (j+1)=
      ∑ j∈range (m+1+1), (-1:ℂ)^j*qBinom q (m+1) j-1 := by
    rw [sum_range_succ' (fun j => (-1:ℂ)^j*qBinom q (m+1) j),sum_range_succ,
      qBinom_eq_zero_of_lt q (by omega : m+1<m+1+1)]
    simp
  have e2 : ∑ j∈range (m+2), (-1:ℂ)^(j+1)*qBinom q (m+1) j=
      -∑ j∈range (m+1+1), (-1:ℂ)^j*qBinom q (m+1) j := by
    rw [← sum_neg_distrib]; apply sum_congr rfl; intro j _; ring
  have e3 : ∑ j∈range (m+2), (-1:ℂ)^(j+1)*((1-q^(m+1))*qBinom q m j)=
      -((1-q^(m+1))*∑ j∈range (m+1), (-1:ℂ)^j*qBinom q m j) := by
    rw [sum_range_succ,qBinom_eq_zero_of_lt q (by omega : m<m+1),mul_sum,← sum_neg_distrib]
    simp only [mul_zero,add_zero]
    apply sum_congr rfl; intro j _; ring
  simp only [mul_sub,mul_add,sum_sub_distrib,sum_add_distrib]
  rw [e1,e2,e3]
  simp only [qBinom_zero_right,pow_zero,one_mul]
  ring

/-- The sum `∑_j [n,j]_(q²) q^j = (-q;q)_n` (DLMF 17.2.E39). -/
@[dlmf 17.2.E39]
theorem q_binomial_base_square (q : ℂ) (n : ℕ) :
    ∑ j∈range (n+1), qBinom (q^2) n j*q^j=qPochhammer (-q) q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrefl : ∑ j∈range (n+1), qBinom (q^2) n j*q^(n-j)=∑ j∈range (n+1), qBinom (q^2) n j*q^j := by
      rw [← sum_range_reflect]
      apply sum_congr rfl
      intro j hj
      have hjn : j≤n := Nat.lt_succ_iff.mp (mem_range.mp hj)
      have hs := qaR4_qBinom_symm (q^2) j (n-j)
      rw [Nat.add_sub_cancel' hjn] at hs
      rw [show n+1-1-j=n-j by omega,Nat.sub_sub_self hjn,← hs]
    rw [sum_range_succ',qPochhammer_succ,← ih]
    simp only [qBinom_succ_succ',add_mul,sum_add_distrib]
    have e1 : ∑ j∈range (n+1), qBinom (q^2) n (j+1)*q^(j+1)+qBinom (q^2) (n+1) 0*q^0=
        ∑ j∈range (n+1), qBinom (q^2) n j*q^j := by
      rw [qBinom_zero_right,← qBinom_zero_right (q^2) n,← sum_range_succ' (fun j => qBinom (q^2) n j*q^j),
        sum_range_succ,qBinom_eq_zero_of_lt _ (Nat.lt_succ_self n)]
      ring
    have e2 : ∑ j∈range (n+1), (q^2)^(n-j)*qBinom (q^2) n j*q^(j+1)=
        q^(n+1)*∑ j∈range (n+1), qBinom (q^2) n j*q^(n-j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      have hjn : j≤n := Nat.lt_succ_iff.mp (mem_range.mp hj)
      rw [← pow_mul]
      have : 2*(n-j)+(j+1)=(n+1)+(n-j) := by omega
      rw [show q^(2*(n-j))*qBinom (q^2) n j*q^(j+1)=qBinom (q^2) n j*(q^(2*(n-j))*q^(j+1)) by ring,
        ← pow_add,this,pow_add]
      ring
    rw [add_right_comm,e1,e2,hrefl]
    ring

/-- The alternating sum `∑_j (-1)^j [2n,j]_q = (q;q²)_n` (DLMF 17.2.E40). -/
@[dlmf 17.2.E40]
theorem q_binomial_alternating_even (q : ℂ) (n : ℕ) :
    ∑ j∈range (2*n+1), (-1:ℂ)^j*qBinom q (2*n) j=qPochhammer q (q^2) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by ring,qaR4_alt_sum_rec,ih,qPochhammer_succ,← pow_mul,pow_succ]
    ring

/-- Away from the origin the `n`-th q-derivative is a finite q-difference: an alternating sum of
`f(zq^j)` weighted by q-binomials (DLMF 17.2.E42). -/
@[dlmf 17.2.E42]
theorem qDeriv_iterate_finite_difference {q z : ℂ} (hq0 : q≠0) (hq1 : q≠1) (hz : z≠0)
    (f : ℂ → ℂ) (n : ℕ) :
    qDerivIterate n q f z=z^(-(n:ℤ))*(1-q)^(-(n:ℤ))*
      ∑ j∈range (n+1), q^(-(n:ℤ)*j+((j+1).choose 2:ℤ))*(-1:ℂ)^j*qBinom q n j*f (z*q^j) := by
  change _=z^(-(n:ℤ))*(1-q)^(-(n:ℤ))*∑ j∈range (n+1), qaR4_fdCoeff q n j*f (z*q^j)
  have hq1' : (1:ℂ)-q≠0 := sub_ne_zero.mpr (Ne.symm hq1)
  induction n generalizing z with
  | zero => simp [qDerivIterate,qaR4_fdCoeff]
  | succ n ih =>
    have hqz : q*z≠0 := mul_ne_zero hq0 hz
    rw [qDerivIterate,Function.iterate_succ_apply',← qDerivIterate,qDerivExtended_of_ne_zero hz,
      qDeriv,ih hz,ih hqz,qaR4_fdCoeff_sum hq0 (fun j => f (z*q^j)) n]
    have e : ∀ j : ℕ, q*z*q^j=z*q^(j+1) := fun j => by rw [pow_succ]; ring
    simp only [e]
    generalize ∑ j∈range (n+1), qaR4_fdCoeff q n j*f (z*q^j) = A
    generalize ∑ j∈range (n+1), qaR4_fdCoeff q n j*f (z*q^(j+1)) = B
    rw [mul_zpow]
    simp only [zpow_neg,zpow_natCast]
    rw [pow_succ,pow_succ]
    field_simp

/-- The q-derivative shifts Taylor coefficients and multiplies them by q-numbers. -/
private lemma qDerivative_taylor_step {q : ℂ} (hq : q ≠ 1) {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt f p 0) :
    ∃ r : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (qDerivExtended q f) r 0 ∧
      ∀ n, r.coeff n = ((1-q^(n+1))/(1-q))*p.coeff (n+1) := by
  let u : ℂ →L[ℂ] ℂ := q • ContinuousLinearMap.id ℂ ℂ
  have hu (z : ℂ) : u z = q*z := by simp [u,smul_eq_mul]
  have hs := hp.dslope_fslope
  have hs0 : HasFPowerSeriesAt (dslope f 0) p.fslope (u 0) := by simpa [hu] using hs
  have hsc := hs0.compContinuousLinearMap
  let r : FormalMultilinearSeries ℂ ℂ ℂ :=
    (1-q)⁻¹ • (p.fslope - q • p.fslope.compContinuousLinearMap u)
  have hr : HasFPowerSeriesAt (qDerivExtended q f) r 0 := by
    have ht := ((hs.sub (hsc.const_smul (c := q))).const_smul (c := (1-q)⁻¹))
    apply ht.congr
    filter_upwards with z
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Function.comp_apply, hu]
    by_cases hz : z=0
    · subst z
      simp only [qDerivExtended, ite_true, mul_zero, dslope_same]
      have hq' : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
      field_simp
    · rw [qDerivExtended_of_ne_zero hz,qDeriv]
      have h1 := sub_smul_dslope f 0 z
      have h2 := sub_smul_dslope f 0 (q*z)
      simp only [sub_zero, smul_eq_mul] at h1 h2
      have hq' : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
      field_simp
      linear_combination h1-h2
  refine ⟨r,hr,?_⟩
  intro n
  change ((1-q)⁻¹ • (p.fslope - q • p.fslope.compContinuousLinearMap u)).coeff n = _
  simp only [FormalMultilinearSeries.coeff, FormalMultilinearSeries.smul_apply,
    FormalMultilinearSeries.sub_apply, _root_.smul_apply, _root_.sub_apply,
    FormalMultilinearSeries.compContinuousLinearMap_apply, smul_eq_mul, hu,
    Pi.one_apply, mul_one, Function.comp_def]
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  change (1-q)⁻¹ * (p.fslope.coeff n - q * (q^n * p.fslope.coeff n)) =
    (1-q^(n+1))/(1-q)*p.coeff (n+1)
  rw [FormalMultilinearSeries.coeff_fslope, pow_succ]
  ring

/-- Iterating q-differentiation at zero multiplies the Taylor coefficient by q-factorials. -/
private lemma qDerivative_taylor_iter {q : ℂ} (hq : q ≠ 1) (n : ℕ) {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt f p 0) :
    qDerivIterate n q f 0 = p.coeff n*qPochhammer q q n/(1-q)^n := by
  induction n generalizing f p with
  | zero =>
    simp only [qDerivIterate, Function.iterate_zero, id_eq, qPochhammer_zero,
      pow_zero,mul_one,div_one]
    exact (hp.coeff_zero 1).symm
  | succ n ih =>
    obtain ⟨r,hr,hcoeff⟩ := qDerivative_taylor_step hq hp
    have he : qDerivIterate (n+1) q f =
        qDerivIterate n q (qDerivExtended q f) := by
      change (fun g : ℂ → ℂ => qDerivExtended q g)^[n+1] f =
        (fun g : ℂ → ℂ => qDerivExtended q g)^[n] (qDerivExtended q f)
      rw [Function.iterate_succ_apply]
    rw [he, ih hr, hcoeff, qPochhammer_succ, pow_succ]
    have hq' : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
    field_simp
    ring


/-- At the origin the `n`-th q-derivative of an analytic function is `f^(n)(0) (q;q)_n/(n!
(1-q)^n)` (DLMF 17.2.E42). -/
@[dlmf 17.2.E42]
theorem qDeriv_iterate_origin {q : ℂ} (hq1 : q≠1) {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    qDerivIterate n q f 0=iteratedDeriv n f 0*qPochhammer q q n/
      ((n.factorial:ℂ)*(1-q)^n) := by
  obtain ⟨p,hp⟩ := hf
  rw [qDerivative_taylor_iter hq1 n hp]
  have heq := hp.eq_formalMultilinearSeries hp.analyticAt.hasFPowerSeriesAt
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
  have hn : (n.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hc' : p.coeff n = iteratedDeriv n f 0 / n.factorial := by simpa using hc
  rw [hc']
  field_simp

/-- The q-product rule `D_q(fg)(z) = g(z) D_q f(z) + f(zq) D_q g(z)` (DLMF 17.2.E43). -/
@[dlmf 17.2.E43]
theorem qDeriv_product_extended (q z : ℂ) (f g : ℂ → ℂ)
    (hf : z=0 → DifferentiableAt ℂ f 0) (hg : z=0 → DifferentiableAt ℂ g 0) :
    qDerivExtended q (fun w => f w*g w) z=
      g z*qDerivExtended q f z+f (z*q)*qDerivExtended q g z := by
  by_cases hz : z=0
  · subst z
    simpa [qDerivExtended,mul_comm] using deriv_fun_mul (hf rfl) (hg rfl)
  · simpa [qDerivExtended,hz,mul_comm] using qDeriv_mul q f g z

/-- The q-Pascal recurrence combines the two finite sums arising in the product rule. -/
private lemma qLeibniz_sum (q : ℂ) (n : ℕ) (F G : ℕ → ℂ) :
    (∑ j ∈ range (n+2), qBinom q (n+1) j * F j * G j) =
      (∑ j ∈ range (n+1), qBinom q n j * q^j * F j * G j) +
      (∑ j ∈ range (n+1), qBinom q n j * F (j+1) * G (j+1)) := by
  rw [sum_range_succ' _ (n+1)]
  simp only [qBinom_zero_right, one_mul]
  have h : ∑ j ∈ range (n+1), qBinom q (n+1) (j+1) * F (j+1) * G (j+1) =
      (∑ j ∈ range (n+1), qBinom q n j * F (j+1) * G (j+1)) +
      ∑ j ∈ range (n+1), q^(j+1) * qBinom q n (j+1) * F (j+1) * G (j+1) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    rw [qBinom_succ_succ]
    ring
  have hb : (∑ j ∈ range (n+1), qBinom q n j * q^j * F j * G j) =
      F 0 * G 0 + ∑ j ∈ range n, qBinom q n (j+1) * q^(j+1) * F (j+1) * G (j+1) := by
    rw [sum_range_succ' _ n]
    simp only [qBinom_zero_right,pow_zero,one_mul]
    ring
  have hc : (∑ j ∈ range (n+1), q^(j+1)*qBinom q n (j+1)*F (j+1)*G (j+1)) =
      ∑ j ∈ range n, qBinom q n (j+1)*q^(j+1)*F (j+1)*G (j+1) := by
    rw [sum_range_succ, qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)]
    simp only [mul_zero, zero_mul, add_zero]
    apply sum_congr rfl
    intro j hj
    ring
  rw [h, hb, hc]
  ring

/-- The q-difference of a product with its first argument scaled by a power of q. -/
private lemma qLeibniz_product {q z : ℂ} (hq : q ≠ 0) (hq1 : q ≠ 1) (hz : z ≠ 0)
    (f g : ℂ → ℂ) (j : ℕ) :
    (f (z*q^j)*g z - f (q*z*q^j)*g (q*z)) / ((1-q)*z) =
      q^j*qDeriv q f (z*q^j)*g z + f (z*q^(j+1))*qDeriv q g z := by
  have h1 : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  simp only [qDeriv,pow_succ]
  field_simp
  ring

/-- At a nonzero argument, the next extended q-derivative is the ordinary q-difference. -/
private lemma qLeibniz_iter_succ {q z : ℂ} (hz : z ≠ 0) (f : ℂ → ℂ) (n : ℕ) :
    qDeriv q (qDerivIterate n q f) z = qDerivIterate (n+1) q f z := by
  change qDeriv q (qDerivIterate n q f) z =
    ((fun g : ℂ → ℂ => qDerivExtended q g)^[n+1] f) z
  rw [Function.iterate_succ_apply',← qDerivIterate,qDerivExtended_of_ne_zero hz]

/-- The q-Leibniz rule for the `n`-th q-derivative of a product, away from the origin (DLMF
17.2.E44). -/
@[dlmf 17.2.E44]
theorem qDeriv_leibniz {q z : ℂ} (hq0 : q≠0) (hq1 : q≠1) (hz : z≠0)
    (f g : ℂ → ℂ) (n : ℕ) :
    qDerivIterate n q (fun w => f w*g w) z=
      ∑ j∈range (n+1), qBinom q n j*qDerivIterate (n-j) q f (z*q^j)*qDerivIterate j q g z := by
  induction n generalizing z with
  | zero => simp [qDerivIterate]
  | succ n ih =>
    have hqz : q*z ≠ 0 := mul_ne_zero hq0 hz
    rw [qDerivIterate,Function.iterate_succ_apply',← qDerivIterate,
      qDerivExtended_of_ne_zero hz,qDeriv, ih hz, ih hqz, ← sum_sub_distrib, sum_div]
    rw [qLeibniz_sum q n (fun j => qDerivIterate (n+1-j) q f (z*q^j))
      (fun j => qDerivIterate j q g z), ← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.le_of_lt_succ (mem_range.mp hj)
    have hpow : z*q^j ≠ 0 := mul_ne_zero hz (pow_ne_zero j hq0)
    have h := qLeibniz_product hq0 hq1 hz (qDerivIterate (n-j) q f)
      (qDerivIterate j q g) j
    rw [qLeibniz_iter_succ hpow, qLeibniz_iter_succ hz] at h
    have hindex : n+1-j = (n-j)+1 := by omega
    rw [hindex, show n+1-(j+1)=n-j by omega]
    convert congrArg (fun w : ℂ => qBinom q n j * w) h using 1 <;> ring

/-- The extended q-derivative of a germ analytic at zero is analytic there. -/
private lemma qLeibniz_analytic {q : ℂ} (hq : q ≠ 1) {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (qDerivExtended q f) 0 := by
  have hq' : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hd : AnalyticAt ℂ (dslope f 0) 0 := hf.dslope 0
  have ha : AnalyticAt ℂ (fun z : ℂ =>
      (dslope f 0 z - q*dslope f 0 (q*z))/(1-q)) 0 := by
    have hqz : AnalyticAt ℂ (fun z : ℂ => q*z) 0 := analyticAt_const.mul analyticAt_id
    have hc : AnalyticAt ℂ (fun z : ℂ => dslope f 0 (q*z)) 0 := by
      have hd' : AnalyticAt ℂ (dslope f 0) (q*0) := by rw [mul_zero]; exact hd
      exact hd'.comp hqz
    exact (hd.sub (analyticAt_const.mul hc)).div_const
  apply ha.congr
  filter_upwards with z
  by_cases hz : z=0
  · subst z
    simp only [qDerivExtended, ite_true, mul_zero, dslope_same]
    field_simp
  · rw [qDerivExtended_of_ne_zero hz,qDeriv]
    have h1 := sub_smul_dslope f 0 z
    have h2 := sub_smul_dslope f 0 (q*z)
    simp only [sub_zero, smul_eq_mul] at h1 h2
    field_simp
    linear_combination h1 - h2

/-- Every iterated extended q-derivative preserves analyticity at zero. -/
private lemma qLeibniz_iter_analytic {q : ℂ} (hq : q ≠ 1) {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (n : ℕ) : AnalyticAt ℂ (qDerivIterate n q f) 0 := by
  induction n with
  | zero => simpa [qDerivIterate] using hf
  | succ n ih =>
    rw [qDerivIterate,Function.iterate_succ_apply',← qDerivIterate]
    exact qLeibniz_analytic hq ih

/-- Extended q-differentiation is additive for germs analytic at zero. -/
private lemma qLeibniz_add {q : ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    qDerivExtended q (fun z => f z + g z) =
      fun z => qDerivExtended q f z + qDerivExtended q g z := by
  funext z
  by_cases hz : z=0
  · subst z
    simpa [qDerivExtended] using deriv_fun_add hf.differentiableAt hg.differentiableAt
  · simp only [qDerivExtended,hz,ite_false]
    exact qDeriv_add q f g z

/-- Extended q-differentiation commutes with constant multiplication. -/
private lemma qLeibniz_const {q c : ℂ} (f : ℂ → ℂ) :
    qDerivExtended q (fun z => c*f z) = fun z => c*qDerivExtended q f z := by
  funext z
  by_cases hz : z=0
  · subst z
    simp [qDerivExtended,deriv_const_mul_field]
  · simp only [qDerivExtended,hz,ite_false]
    exact qDeriv_const_mul q c f z

/-- An iterated q-derivative can be differentiated once more. -/
private lemma qLeibniz_succ (q : ℂ) (f : ℂ → ℂ) (n : ℕ) :
    qDerivIterate (n+1) q f = qDerivExtended q (qDerivIterate n q f) := by
  rw [qDerivIterate,Function.iterate_succ_apply',← qDerivIterate]

/-- An initial q-derivative can be incorporated into an iterate. -/
private lemma qLeibniz_succ_input (q : ℂ) (f : ℂ → ℂ) (n : ℕ) :
    qDerivIterate n q (qDerivExtended q f) = qDerivIterate (n+1) q f := by
  change (fun g : ℂ → ℂ => qDerivExtended q g)^[n] (qDerivExtended q f) =
    (fun g : ℂ → ℂ => qDerivExtended q g)^[n+1] f
  rw [Function.iterate_succ_apply]

/-- Iterated extended q-differentiation is additive on analytic germs. -/
private lemma qLeibniz_iter_add {q : ℂ} (hq : q≠1) {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    qDerivIterate n q (fun z => f z + g z) =
      fun z => qDerivIterate n q f z + qDerivIterate n q g z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [qLeibniz_succ]
    rw [ih, qLeibniz_add (qLeibniz_iter_analytic hq hf n) (qLeibniz_iter_analytic hq hg n)]

/-- Iterated extended q-differentiation commutes with constant multiplication. -/
private lemma qLeibniz_iter_const {q c : ℂ} (f : ℂ → ℂ) (n : ℕ) :
    qDerivIterate n q (fun z => c*f z) = fun z => c*qDerivIterate n q f z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [qLeibniz_succ]
    rw [ih,qLeibniz_const]

/-- At base zero the Gaussian coefficient is one in the triangular range. -/
private lemma qLeibniz_binom_zero (n j : ℕ) (hj : j ≤ n) : qBinom 0 n j = 1 := by
  induction n generalizing j with
  | zero =>
    have h : j=0 := by omega
    subst j
    simp
  | succ n ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [qBinom_succ_succ]
      simp [ih j (by omega)]

/-- At base zero, the q-derivatives of a product at zero form a convolution. -/
private lemma qLeibniz_zero_conv {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    qDerivIterate n 0 (fun z => f z*g z) 0 =
      ∑ j ∈ range (n+1), qDerivIterate (n-j) 0 f 0*qDerivIterate j 0 g 0 := by
  induction n generalizing f g with
  | zero => simp [qDerivIterate]
  | succ n ih =>
    have h0 : (0 : ℂ) ≠ 1 := by norm_num
    have hprod : qDerivExtended 0 (fun z => f z*g z) =
        fun z => qDerivExtended 0 f z*g z + f 0*qDerivExtended 0 g z := by
      funext z
      simpa [mul_comm] using qDeriv_product_extended 0 z f g
        (fun _ => hf.differentiableAt) (fun _ => hg.differentiableAt)
    have hs : qDerivIterate (n+1) 0 (fun z => f z*g z) =
        qDerivIterate n 0 (qDerivExtended 0 (fun z => f z*g z)) := by
      rw [qDerivIterate,Function.iterate_succ_apply,← qDerivIterate]
    rw [hs,hprod,qLeibniz_iter_add (f := fun z => qDerivExtended 0 f z*g z)
      (g := fun z => f 0*qDerivExtended 0 g z) h0 ((qLeibniz_analytic h0 hf).mul hg)
      (analyticAt_const.mul (qLeibniz_analytic h0 hg)),qLeibniz_iter_const]
    dsimp only
    rw [ih (qLeibniz_analytic h0 hf) hg]
    rw [qLeibniz_succ_input]
    conv_rhs => rw [sum_range_succ]
    have heq : (∑ j ∈ range (n+1),
        qDerivIterate (n-j) 0 (qDerivExtended 0 f) 0*qDerivIterate j 0 g 0) =
        ∑ j ∈ range (n+1), qDerivIterate (n+1-j) 0 f 0*qDerivIterate j 0 g 0 := by
      apply sum_congr rfl
      intro j hj
      rw [show n+1-j=(n-j)+1 by have := mem_range.mp hj; omega,
        qLeibniz_succ_input]
    rw [heq]
    simp [qDerivIterate]


/-- The q-Leibniz rule at the origin for analytic factors (DLMF 17.2.E44). -/
@[dlmf 17.2.E44]
theorem qDeriv_leibniz_origin {q : ℂ} (hq1 : q≠1) {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    qDerivIterate n q (fun w => f w*g w) 0=
      ∑ j∈range (n+1), qBinom q n j*qDerivIterate (n-j) q f 0*qDerivIterate j q g 0 := by
  by_cases hq0 : q=0
  · subst q
    rw [qLeibniz_zero_conv hf hg]
    apply sum_congr rfl
    intro j hj
    rw [qLeibniz_binom_zero n j (Nat.le_of_lt_succ (mem_range.mp hj))]
    ring
  have hL : ContinuousAt (qDerivIterate n q (fun w => f w*g w)) 0 :=
    (qLeibniz_iter_analytic hq1 (hf.mul hg) n).continuousAt
  have hR : ContinuousAt (fun z : ℂ => ∑ j ∈ range (n+1),
      qBinom q n j*qDerivIterate (n-j) q f (z*q^j)*qDerivIterate j q g z) 0 := by
    apply tendsto_finsetSum
    intro j hj
    have hF : ContinuousAt (fun z : ℂ => qDerivIterate (n-j) q f (z*q^j)) 0 := by
      have ht : ContinuousAt (qDerivIterate (n-j) q f) ((0:ℂ)*q^j) := by
        simpa using (qLeibniz_iter_analytic hq1 hf (n-j)).continuousAt
      exact ht.comp (f := fun z : ℂ => z*q^j) (continuousAt_id.mul_const (q^j))
    exact ((continuousAt_const.mul hF).mul (qLeibniz_iter_analytic hq1 hg j).continuousAt).tendsto
  have he : (fun z : ℂ => qDerivIterate n q (fun w => f w*g w) z) =ᶠ[𝓝[≠] 0]
      (fun z : ℂ => ∑ j ∈ range (n+1),
        qBinom q n j*qDerivIterate (n-j) q f (z*q^j)*qDerivIterate j q g z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact qDeriv_leibniz hq0 hq1 hz f g n
  have h := tendsto_nhds_unique (hL.tendsto.mono_left nhdsWithin_le_nhds)
    ((hR.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)
  simpa using h

/-- As `q → 1`, the q-derivative of a differentiable function tends to its derivative. -/
theorem qDeriv_limit {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    Tendsto (fun q : ℂ => qDerivExtended q f z) (𝓝[≠] 1) (𝓝 (deriv f z)) := by
  by_cases hz : z=0
  · subst z
    simp [qDerivExtended]
  · simpa [qDerivExtended,hz] using DLMF.QSeries.tendsto_qDeriv hf.hasDerivAt hz

/-- The finite geometric q-number tends to its integer index as the complex base tends to one. -/
private lemma qLimit_qnum_limit (m : ℕ) :
    Tendsto (fun q : ℂ => qNum q m) (𝓝[≠] 1) (𝓝 (m : ℂ)) := by
  have h : Tendsto (fun q : ℂ => ∑ j ∈ range m, q^j) (𝓝[≠] 1)
      (𝓝 (∑ j ∈ range m, (1 : ℂ)^j)) := by
    apply tendsto_finsetSum
    intro j hj
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).pow j
  simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq' : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  unfold qNum
  apply (eq_div_iff hq').2
  exact geom_sum_mul_neg q m

/-- The normalized finite q-factorial tends to the ordinary factorial as the complex base
tends to one. -/
private lemma qLimit_qfactorial_limit (n : ℕ) :
    Tendsto (fun q : ℂ => qPochhammer q q n/(1-q)^n) (𝓝[≠] 1)
      (𝓝 (n.factorial : ℂ)) := by
  induction n with
  | zero => simp [qPochhammer_zero]
  | succ n ih =>
    have ht := ih.mul (qLimit_qnum_limit (n+1))
    have heq : (fun q : ℂ => qPochhammer q q (n+1)/(1-q)^(n+1)) =ᶠ[𝓝[≠] 1]
        (fun q => qPochhammer q q n/(1-q)^n*qNum q (n+1)) := by
      filter_upwards [self_mem_nhdsWithin] with q hq
      have hq' : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
      rw [qPochhammer_succ,pow_succ,qNum,pow_succ]
      field_simp
    convert ht.congr' heq.symm using 1;
      simp [Nat.factorial_succ, mul_comm]

/-- The extended q-derivative of a monomial, including its removable value at the origin. -/
private lemma qLimit_qderiv_monomial {q : ℂ} (hq : q≠1) (m : ℕ) :
    qDerivExtended q (fun z : ℂ => z^m) = fun z => qNum q m*z^(m-1) := by
  funext z
  by_cases hz : z=0
  · subst z
    cases m with
    | zero => simp [qDerivExtended,qNum]
    | succ m =>
      cases m with
      | zero =>
        have hq' : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
        simp [qDerivExtended,qNum,deriv_id'',hq']
      | succ m => simp [qDerivExtended]
  · rw [qDerivExtended_of_ne_zero hz]
    exact qDeriv_pow hq hz m

/-- Constant scalar multiplication commutes with the extended q-derivative. -/
private lemma qLimit_qconst {q c : ℂ} (f : ℂ → ℂ) :
    qDerivExtended q (fun z => c*f z) = fun z => c*qDerivExtended q f z := by
  funext z
  by_cases hz : z=0
  · subst z
    simp [qDerivExtended,deriv_const_mul_field]
  · simp only [qDerivExtended,hz,ite_false]
    exact qDeriv_const_mul q c f z

/-- Repeated q-differentiation of a monomial multiplies by successive q-numbers. -/
private lemma qLimit_qmonomial_iter {q : ℂ} (hq : q≠1) (m n : ℕ) :
    qDerivIterate n q (fun z : ℂ => z^m) =
      fun z => (∏ j ∈ range n, qNum q (m-j))*z^(m-n) := by
  induction n with
  | zero => simp [qDerivIterate]
  | succ n ih =>
    rw [qDerivIterate,Function.iterate_succ_apply',← qDerivIterate,ih,qLimit_qconst,
      qLimit_qderiv_monomial hq, prod_range_succ]
    simp only [show m-(n+1)=(m-n)-1 by omega]
    funext z
    ring

/-- Each iterated q-derivative of a monomial tends to its ordinary iterated derivative. -/
private lemma qLimit_qmonomial_limit (m n : ℕ) (z : ℂ) :
    Tendsto (fun q : ℂ => qDerivIterate n q (fun z : ℂ => z^m) z) (𝓝[≠] 1)
      (𝓝 (iteratedDeriv n (fun z : ℂ => z^m) z)) := by
  have h : Tendsto (fun q : ℂ => (∏ j ∈ range n, qNum q (m-j))*z^(m-n))
      (𝓝[≠] 1) (𝓝 ((∏ j ∈ range n, ((m-j : ℕ):ℂ))*z^(m-n))) := by
    apply Tendsto.mul_const
    apply tendsto_finsetProd
    intro j hj
    exact qLimit_qnum_limit (m-j)
  have hprod : (∏ j ∈ range n, ((m-j : ℕ):ℂ)) = (m.descFactorial n : ℂ) := by
    rw [Nat.descFactorial_eq_prod_range]
    exact (Nat.cast_prod _ _).symm
  rw [hprod, ← iteratedDeriv_pow] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (congrFun (qLimit_qmonomial_iter hq m n) z).symm

/-- Away from zero, iterated q-differentiation commutes with finite linear combinations. -/
private lemma qLimit_qiter_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (F : ι → ℂ → ℂ)
    {q z : ℂ} (hq0 : q≠0) (hq1 : q≠1) (hz : z≠0) (n : ℕ) :
    qDerivIterate n q (fun w => ∑ i ∈ s, a i*F i w) z =
      ∑ i ∈ s, a i*qDerivIterate n q (F i) z := by
  rw [qDeriv_iterate_finite_difference hq0 hq1 hz]
  simp_rw [qDeriv_iterate_finite_difference hq0 hq1 hz]
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

/-- Away from zero, iterated q-differentiation commutes with finite linear combinations. -/
private lemma qLimit_qLimit_qiter_sum_limit {ι : Type*} (s : Finset ι) (a : ι → ℂ) (m : ι → ℕ)
    {z : ℂ} (hz : z≠0) (n : ℕ) :
    Tendsto (fun q : ℂ => qDerivIterate n q (fun w => ∑ i ∈ s, a i*w^(m i)) z)
      (𝓝[≠] 1) (𝓝 (iteratedDeriv n (fun w => ∑ i ∈ s, a i*w^(m i)) z)) := by
  have ht : Tendsto (fun q : ℂ => ∑ i ∈ s, a i*qDerivIterate n q (fun w : ℂ => w^(m i)) z)
      (𝓝[≠] 1) (𝓝 (∑ i ∈ s, a i*iteratedDeriv n (fun w : ℂ => w^(m i)) z)) := by
    apply tendsto_finsetSum
    intro i hi
    exact (qLimit_qmonomial_limit (m i) n z).const_mul (a i)
  have he : iteratedDeriv n (fun w : ℂ => ∑ i ∈ s, a i*w^(m i)) z =
      ∑ i ∈ s, a i*iteratedDeriv n (fun w : ℂ => w^(m i)) z := by
    rw [iteratedDeriv_fun_sum]
    · apply sum_congr rfl
      intro i hi
      exact iteratedDeriv_const_mul_field _ _
    · intro i hi
      fun_prop
  rw [he]
  apply ht.congr'
  have hq0 : ∀ᶠ q : ℂ in 𝓝[≠] 1, q≠0 := by
    exact (eventually_ne_nhds (by norm_num : (1:ℂ)≠0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hq0,self_mem_nhdsWithin] with q hq0 hq1
  exact (qLimit_qiter_sum s a (fun i w => w^(m i)) hq0 hq1 hz n).symm

/-- The iterated q-derivatives of a translated monomial have their classical limits. -/
private lemma qLimit_qiter_centered_limit (m n : ℕ) {z : ℂ} (hz : z≠0) :
    Tendsto (fun q : ℂ => qDerivIterate n q (fun w => (w-z)^m) z)
      (𝓝[≠] 1) (𝓝 (iteratedDeriv n (fun w => (w-z)^m) z)) := by
  have he : (fun w : ℂ => (w-z)^m) =
      fun w => ∑ k ∈ range (m+1), ((m.choose k:ℂ)*(-z)^(m-k))*w^k := by
    funext w
    rw [sub_eq_add_neg,add_pow]
    apply sum_congr rfl
    intro k hk
    ring
  rw [he]
  exact qLimit_qLimit_qiter_sum_limit (range (m+1)) _ _ hz n

/-- A Taylor remainder of order `n + 1` contributes zero to the classical limit of the
`n`th q-derivative. -/
private lemma qLimit_qiter_remainder_limit {R : ℂ → ℂ} {z : ℂ} (hz : z≠0) (n : ℕ)
    (hR : (fun h : ℂ => R (z+h)) =O[𝓝 0] fun h => ‖h‖^(n+1)) :
    Tendsto (fun q : ℂ => qDerivIterate n q R z) (𝓝[≠] 1) (𝓝 0) := by
  have hterm (j : ℕ) : Tendsto (fun q : ℂ => R (z*q^j)/(1-q)^n) (𝓝[≠] 1) (𝓝 0) := by
    have hh : Tendsto (fun q : ℂ => z*q^j-z) (𝓝[≠] 1) (𝓝 0) := by
      simpa using ((((tendsto_id : Tendsto (fun q : ℂ => q) (𝓝 1) (𝓝 1)).mono_left
        nhdsWithin_le_nhds).pow j).const_mul z).sub_const z
    have hd : DifferentiableAt ℂ (fun q : ℂ => z*q^j) 1 := by fun_prop
    have hb : (fun q : ℂ => z*q^j-z) =O[𝓝[≠] 1] fun q => q-1 := by
      simpa using hd.isBigO_sub.mono nhdsWithin_le_nhds
    have he := hR.comp_tendsto hh
    have hb' := hb.norm_left.pow (n+1)
    have hs : (fun q : ℂ => R (z*q^j)) =O[𝓝[≠] 1] fun q => ‖q-1‖^(n+1) := by
      have ht := he.trans hb'.norm_right
      simp only [norm_pow, Function.comp_def] at ht
      convert ht using 1
      funext q
      congr 1
      ring
    have hl := hs.trans_isLittleO
      ((isLittleO_pow_sub_pow_sub (1:ℂ) (Nat.lt_succ_self n)).mono nhdsWithin_le_nhds)
    have hl' : (fun q : ℂ => R (z*q^j)) =o[𝓝[≠] 1] fun q => (1-q)^n := by
      rw [← isLittleO_norm_right]
      simpa only [norm_pow, norm_sub_rev] using hl
    exact hl'.tendsto_div_nhds_zero
  have hsum : Tendsto (fun q : ℂ => ∑ j ∈ range (n+1),
      q^(-(n:ℤ)*j+((j+1).choose 2:ℤ))*(-1:ℂ)^j*qBinom q n j*
        (R (z*q^j)/(1-q)^n)) (𝓝[≠] 1) (𝓝 0) := by
    have hc (j : ℕ) : ContinuousAt (fun q : ℂ =>
        q^(-(n:ℤ)*j+((j+1).choose 2:ℤ))*(-1:ℂ)^j*qBinom q n j) 1 := by
      exact ((continuousAt_id.zpow₀ _ (by norm_num)).mul_const _).mul
        (continuous_qBinom n j).continuousAt
    have ht := tendsto_finsetSum (range (n+1)) (fun j hj =>
      ((hc j).tendsto.mono_left nhdsWithin_le_nhds).mul (hterm j))
    simpa only [mul_zero, sum_const_zero] using ht
  have ht := hsum.const_mul (z^(-(n:ℤ)))
  simp only [mul_zero] at ht
  apply ht.congr'
  have hq0 : ∀ᶠ q : ℂ in 𝓝[≠] 1, q≠0 :=
    (eventually_ne_nhds (by norm_num : (1:ℂ)≠0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hq0,self_mem_nhdsWithin] with q hq0 hq1
  rw [qDeriv_iterate_finite_difference hq0 hq1 hz]
  simp only [zpow_neg,zpow_natCast]
  rw [mul_sum,mul_sum]
  apply sum_congr rfl
  intro j hj
  ring

/-- Finite Taylor polynomials have the expected classical q-derivative limit. -/
private lemma qLimit_qiter_taylor_limit (a : ℕ → ℂ) (N n : ℕ) {z : ℂ} (hz : z≠0) :
    Tendsto (fun q : ℂ => qDerivIterate n q (fun w => ∑ k ∈ range N, a k*(w-z)^k) z)
      (𝓝[≠] 1) (𝓝 (iteratedDeriv n (fun w => ∑ k ∈ range N, a k*(w-z)^k) z)) := by
  have ht := tendsto_finsetSum (range N)
    (fun k hk => (qLimit_qiter_centered_limit k n hz).const_mul (a k))
  have he : iteratedDeriv n (fun w : ℂ => ∑ k ∈ range N, a k*(w-z)^k) z =
      ∑ k ∈ range N, a k*iteratedDeriv n (fun w : ℂ => (w-z)^k) z := by
    rw [iteratedDeriv_fun_sum]
    · apply sum_congr rfl
      intro k hk
      exact iteratedDeriv_const_mul_field _ _
    · intro k hk
      fun_prop
  rw [he]
  apply ht.congr'
  have hq0 : ∀ᶠ q : ℂ in 𝓝[≠] 1, q≠0 :=
    (eventually_ne_nhds (by norm_num : (1:ℂ)≠0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hq0,self_mem_nhdsWithin] with q hq0 hq1
  exact (qLimit_qiter_sum (range N) a (fun k w => (w-z)^k) hq0 hq1 hz n).symm

/-- The `n`th derivative of the degree-`n` Taylor polynomial at its center extracts its
top coefficient. -/
private lemma qLimit_deriv_taylor (a : ℕ → ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w => ∑ k ∈ range (n+1), a k*(w-z)^k) z = a n*n.factorial := by
  rw [iteratedDeriv_fun_sum]
  · simp_rw [iteratedDeriv_const_mul_field]
    have ht (k : ℕ) (hk : k ≤ n) :
        iteratedDeriv n (fun w : ℂ => (w-z)^k) z = if k=n then n.factorial else 0 := by
      rw [iteratedDeriv_comp_sub_const (f := fun w : ℂ => w^k)]
      simp only [sub_self, iteratedDeriv_pow]
      by_cases hkn : k=n
      · subst k
        simp [Nat.descFactorial_self]
      · have hlt : k<n := lt_of_le_of_ne hk hkn
        simp [hkn,Nat.descFactorial_of_lt hlt]
    calc (∑ i ∈ range (n+1), a i*iteratedDeriv n (fun w : ℂ => (w-z)^i) z) =
        ∑ i ∈ range (n+1), if i=n then a i*n.factorial else 0 := by
          apply sum_congr rfl
          intro k hk
          rw [ht k (Nat.le_of_lt_succ (mem_range.mp hk))]
          split_ifs <;> simp
      _ = a n*n.factorial := by simp
  · intro k hk
    fun_prop

/-- Away from zero, iterated q-differentiation commutes with subtraction. -/
private lemma qLimit_qiter_sub {f g : ℂ → ℂ} {q z : ℂ}
    (hq0 : q≠0) (hq1 : q≠1) (hz : z≠0) (n : ℕ) :
    qDerivIterate n q (fun w => f w-g w) z = qDerivIterate n q f z-qDerivIterate n q g z := by
  simp only [qDeriv_iterate_finite_difference hq0 hq1 hz,mul_sub,sum_sub_distrib]

/-- As `q → 1`, the `n`-th q-derivative of an analytic function tends to its `n`-th derivative. -/
theorem qDeriv_iterate_limit {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (n : ℕ) :
    Tendsto (fun q : ℂ => qDerivIterate n q f z) (𝓝[≠] 1) (𝓝 (iteratedDeriv n f z)) := by
  by_cases hz : z=0
  · subst z
    have ht := (qLimit_qfactorial_limit n).const_mul (iteratedDeriv n f 0/(n.factorial:ℂ))
    have hn : (n.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have ht' : Tendsto (fun q : ℂ => iteratedDeriv n f 0*qPochhammer q q n /
        ((n.factorial:ℂ)*(1-q)^n)) (𝓝[≠] 1) (𝓝 (iteratedDeriv n f 0)) := by
      convert ht using 1 <;> field_simp
    apply ht'.congr'
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (qDeriv_iterate_origin hq hf n).symm
  obtain ⟨p,hp⟩ := hf
  let P : ℂ → ℂ := fun w => ∑ k ∈ range (n+1), p.coeff k*(w-z)^k
  have hR : (fun h : ℂ => (f (z+h)-P (z+h))) =O[𝓝 0] fun h => ‖h‖^(n+1) := by
    have h := hp.isBigO_sub_partialSum_pow (n+1)
    convert h using 1
    funext w
    dsimp [P,FormalMultilinearSeries.partialSum]
    congr 1
    apply sum_congr rfl
    intro k hk
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
    simp [smul_eq_mul,mul_comm]
  have ht := (qLimit_qiter_taylor_limit p.coeff (n+1) n hz).add
    (qLimit_qiter_remainder_limit (R := fun w => f w-P w) hz n hR)
  simp only [add_zero] at ht
  have hcoeff : p.coeff n = iteratedDeriv n f z/n.factorial := by
    have heq := hp.eq_formalMultilinearSeries hp.analyticAt.hasFPowerSeriesAt
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
    simpa using hc
  rw [qLimit_deriv_taylor,hcoeff,
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))] at ht
  apply ht.congr'
  have hq0 : ∀ᶠ q : ℂ in 𝓝[≠] 1, q≠0 :=
    (eventually_ne_nhds (by norm_num : (1:ℂ)≠0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hq0,self_mem_nhdsWithin] with q hq0 hq1
  change qDerivIterate n q P z+qDerivIterate n q (fun w => f w-P w) z = _
  rw [qLimit_qiter_sub hq0 hq1 hz n]
  ring

/-- For `|q| < 1` and `f` continuous at `0`, the Jackson integral `∫_0^a f d_q t` is the sum of
its defining series (DLMF 17.2.E45, E46). -/
@[dlmf 17.2.E45, dlmf 17.2.E46]
theorem jackson_series_hasSum {q a : ℂ} (hq : ‖q‖<1) {f : ℂ → ℂ} (hf : ContinuousAt f 0) :
    HasSum (fun j : ℕ => a*(1-q)*f (a*q^j)*q^j) (jacksonIntegral q a f) := by
  have hpow := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).const_mul a
  simp only [mul_zero] at hpow
  have hcont : Tendsto (fun j : ℕ => f (a*q^j)) atTop (𝓝 (f 0)) := by
    simpa only [Function.comp_def] using hf.tendsto.comp hpow
  obtain ⟨B,hB⟩ := hcont.norm.bddAbove_range
  have hs : Summable (fun j : ℕ => f (a*q^j)*q^j) :=
    Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left B)
      (fun j => by simpa [norm_mul,norm_pow] using
        mul_le_mul_of_nonneg_right (hB ⟨j,rfl⟩) (pow_nonneg (norm_nonneg q) j))
  simpa only [jacksonIntegral,mul_assoc] using hs.hasSum.mul_left (a*(1-q))

/-- Additivity of the two-endpoint Jackson integral over adjacent intervals. -/
theorem jacksonBetween_additivity (q a b c : ℂ) (f : ℂ → ℂ) :
    jacksonBetween q a c f=jacksonBetween q a b f+jacksonBetween q b c f := by
  simp only [jacksonBetween]; ring

/-- As `q → 1⁻`, the Jackson integral of a continuous function tends to its Riemann integral (DLMF
17.2.E47). -/
@[dlmf 17.2.E47]
theorem jackson_classical_limit {f : ℝ → ℂ} {a : ℝ} (hf : ContinuousOn f (uIcc 0 a)) :
    Tendsto (fun q : ℝ => jacksonIntegral (q:ℂ) (a:ℂ) (fun z => f z.re))
      (𝓝[<] 1) (𝓝 (∫ x : ℝ in 0..a, f x)) := by
  sorry

/-- For an absolutely summable bilateral Jackson series, the integrals `∫_0^(q^(-n)) f d_q t` tend
to the bilateral Jackson integral (DLMF 17.2.E48). -/
@[dlmf 17.2.E48]
theorem jackson_bilateral_limit {q : ℝ} (hq0 : 0<q) (hq1 : q<1) {f : ℂ → ℂ}
    (hf : Summable (fun j : ℤ => (q:ℂ)^j*f ((q:ℂ)^j))) :
    Tendsto (fun n : ℕ => jacksonIntegral (q:ℂ) ((q:ℂ)^(-(n:ℤ))) f) atTop
      (𝓝 (jacksonBilateral q f)) := by
  have hq0' : (q:ℂ)≠0 := by exact_mod_cast hq0.ne'
  simp only [qaR4_jackson_neg_pow hq0' f]
  unfold jacksonBilateral
  apply Tendsto.const_mul
  apply tendsto_tsum_of_dominated_convergence (bound := fun k : ℤ => ‖(q:ℂ)^k*f ((q:ℂ)^k)‖)
  · exact summable_norm_iff.mpr hf
  · intro k
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k.natAbs] with n hn
    split_ifs <;> first | rfl | omega
  · refine Eventually.of_forall fun n k => ?_
    split_ifs <;> simp; positivity

/-- The same improper-integral identity for two naturally convergent tails, without assuming absolute summability. -/
@[dlmf 17.2.E48]
theorem jackson_bilateral_natural_limit {q : ℝ} (hq0 : 0<q) (hq1 : q<1) {f : ℂ → ℂ} {v : ℂ}
    (hf : HasNaturalJacksonBilateral q f v) :
    ∃ J : ℕ → ℂ,
      (∀ n : ℕ, HasNaturalJacksonIntegral q ((q:ℂ)^(-(n:ℤ))) f (J n)) ∧
      Tendsto J atTop (𝓝 v) := by
  obtain ⟨vp,vm,hp,hm,hv⟩ := hf
  have hq0' : (q:ℂ)≠0 := by exact_mod_cast hq0.ne'
  refine ⟨fun n => (1-(q:ℂ))*((∑ i∈range n, (q:ℂ)^(-(i:ℤ)-1)*f ((q:ℂ)^(-(i:ℤ)-1)))+vp),?_,?_⟩
  · intro n
    unfold HasNaturalJacksonIntegral
    have ht : Tendsto (fun N : ℕ => N-n) atTop atTop := tendsto_sub_atTop_nat n
    have h := ((hp.comp ht).const_add (∑ i∈range n, (q:ℂ)^(-(i:ℤ)-1)*f ((q:ℂ)^(-(i:ℤ)-1)))).const_mul
      (1-(q:ℂ))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop n] with N hN
    obtain ⟨M,rfl⟩ := Nat.exists_eq_add_of_le hN
    simp only [Function.comp_apply,Nat.add_sub_cancel_left]
    rw [qaR4_jackson_partial_split hq0' f n M]
  · rw [hv,add_comm vp vm]
    exact (hm.add_const vp).const_mul _

/-- The complete two-index Gaussian limit, including the fixed-index boundary s=0. -/
@[dlmf 17.2.E34]
theorem qBinom_two_index_limit {q : ℂ} (hq : ‖q‖<1) {r s : ℕ} (hrs : s<r)
    (u t : ℕ) : Tendsto (fun n : ℕ => qBinom q (r*n+u) (s*n+t)) atTop
      (𝓝 (if s=0 then (qPochhammer q q t)⁻¹ else (qPochhammerInf q q)⁻¹)) := by
  by_cases hs : s=0
  · subst s
    simp only [Nat.zero_mul,zero_add,ite_true]
    have hr : 0<r := hrs
    have ht : Tendsto (fun n : ℕ => r*n+u) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by nlinarith⟩
    exact (qBinom_fixed_lower_limit hq t).comp ht
  · simpa [hs] using qBinom_two_growing_indices hq (Nat.pos_of_ne_zero hs) hrs u t

end DLMF.QHypergeometric
