/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import DLMFMathlib.Analysis.Complex.SegmentPrimitive
public import DLMF.Confluent.ExpIntegral
public import DLMF.Confluent.ErrorFunctions
public import DLMF.Confluent.FresnelAsymptotics
public import DLMF.Statistical.IncompleteGamma
public import DLMF.Statistical.IncompleteBeta
public import DLMF.Bessel.SecondKind
public import DLMF.OrthogonalPolynomials.Classical
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Algebra.ContinuedFractions.Basic

/-!
# Convergence and branch conventions for the DLMF Chapters 6–8 acquisition

Improper integrals assert limits of finite integrals. Logarithmic coordinates
retain continuation across cuts. Continued fractions assert convergence of
finite truncations, rather than an equality to a totalized infinite expression.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory
open scoped Real Topology
namespace DLMF

/-- Improper integral on a right half-line, including convergence. -/
def HasIntegralAtTop (f : ℝ → ℂ) (a : ℝ) (v : ℂ) : Prop :=
  Tendsto (fun R => ∫ t in a..R, f t) atTop (𝓝 v)
/-- Improper integral on a left half-line, including convergence. -/
def HasIntegralAtBot (f : ℝ → ℂ) (a : ℝ) (v : ℂ) : Prop :=
  Tendsto (fun R => ∫ t in R..a, f t) atBot (𝓝 v)
/-- Convergence of both tails separately. -/
def HasIntegralWholeLine (f : ℝ → ℂ) (v : ℂ) : Prop :=
  ∃ u w, HasIntegralAtBot f 0 u ∧ HasIntegralAtTop f 0 w ∧ u + w = v
/-- Value of a convergent tail, with convergence always asserted separately. -/
def improperAtTop (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  limUnder atTop (fun R => ∫ t in a..R, f t)
/-- Symmetric principal value at the interior point of a right half-line. -/
def HasPrincipalValueIoi (f : ℝ → ℂ) (a c : ℝ) (v : ℂ) : Prop :=
  a < c ∧
  (∀ ε > 0, HasIntegralAtTop f (c + ε) (improperAtTop f (c + ε))) ∧
  Tendsto (fun ε : ℝ => (∫ t in a..c-ε, f t) + improperAtTop f (c+ε))
    (𝓝[>] (0 : ℝ)) (𝓝 v)
/-- Straight complex segment with its Jacobian. -/
def segmentIntegral (f : ℂ → ℂ) (a b : ℂ) : ℂ :=
  (b-a) * ∫ t : ℝ in 0..1, f (a + t * (b-a))
/-- Primitive based at zero of an entire integrand. -/
def primitive (f : ℂ → ℂ) (z : ℂ) : ℂ := segmentIntegral f 0 z
/-- The straight-segment primitive equals any entire antiderivative minus its base value. -/
theorem primitive_eq_sub {f g : ℂ → ℂ} (hf : Continuous f)
    (hg : ∀ z, HasDerivAt g (f z) z) (z : ℂ) :
    primitive f z=g z-g 0 := by
  simpa [primitive, segmentIntegral] using Complex.mul_integral_comp_mul_eq_sub hf hg z

/-- An entire antiderivative evaluates the integral on any straight segment. -/
theorem segmentIntegral_eq_sub {f g : ℂ → ℂ} (hf : Continuous f)
    (hg : ∀ z, HasDerivAt g (f z) z) (a b : ℂ) :
    segmentIntegral f a b=g b-g a := by
  have hd (w : ℂ) : HasDerivAt (fun u => g (a+u)) (f (a+w)) w := by
    convert! (hg (a+w)).comp w ((hasDerivAt_id w).const_add a) using 1
    simp
  have h := Complex.mul_integral_comp_mul_eq_sub (f:=fun w=>f (a+w))
    (by fun_prop) hd (b-a)
  simpa [segmentIntegral] using h

/-- A locally absolutely convergent monomial series may be integrated along a straight segment. -/
theorem hasSum_primitive_monomials {f : ℂ → ℂ} (c : ℕ → ℂ) (d : ℕ → ℕ)
    (hs : ∀ z, HasSum (fun n=>c n*z^(d n)) (f z))
    (hb : ∀ R : ℝ, 0≤R → Summable (fun n=>‖c n‖*R^(d n))) (z : ℂ) :
    HasSum (fun n=>c n*z^(d n+1)/(d n+1:ℂ)) (primitive f z) := by
  let F : ℕ → ℝ → ℂ := fun n t=>c n*((t:ℂ)*z)^(d n)
  let B : ℕ → ℝ → ℝ := fun n _=>‖c n‖*‖z‖^(d n)
  have hF (n : ℕ) : Continuous (F n) := by dsimp [F]; fun_prop
  have hi := intervalIntegral.hasSum_integral_of_dominated_convergence (μ:=volume) (a:=0) (b:=1) B
    (fun n=>(hF n).aestronglyMeasurable)
    (fun n=>ae_of_all _ fun t ht=>by
      have ht' : t∈Ioc (0:ℝ) 1 := by simpa using ht
      have ht1 : ‖(t:ℂ)‖≤1 := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht'.1]; exact ht'.2
      simp only [F,B,norm_mul,norm_pow]
      calc
        ‖c n‖*(‖(t:ℂ)‖*‖z‖)^(d n) ≤ ‖c n‖*(1*‖z‖)^(d n) := by gcongr
        _ = _ := by rw [one_mul])
    (ae_of_all _ fun _ _=>hb ‖z‖ (norm_nonneg _))
    (by dsimp only [B]; exact intervalIntegrable_const)
    (ae_of_all _ fun t _=>hs ((t:ℂ)*z))
  have hp (m : ℕ) : (∫ t : ℝ in 0..1, (t:ℂ)^m)=1/(m+1:ℂ) := by
    simp_rw [← Complex.ofReal_pow]
    rw [intervalIntegral.integral_ofReal,integral_pow]
    norm_num
  have he (n : ℕ) : z*(∫ t : ℝ in 0..1,F n t)=c n*z^(d n+1)/(d n+1:ℂ) := by
    simp only [F,mul_pow]
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_mul_const,hp,pow_succ]
    ring
  have h := hi.mul_left z
  simp_rw [he] at h
  simpa [primitive,segmentIntegral] using h

/-- Entire integrands have the expected derivative under the straight-segment convention. -/
theorem hasDerivAt_primitive {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    HasDerivAt (primitive f) (f z) z := by
  have he : primitive f = fun w => w*(∫ t : ℝ in 0..1, f (t*w)) := by
    funext w
    simp [primitive, segmentIntegral]
  rw [he]
  exact Complex.hasDerivAt_mul_integral_comp_mul hf z

/-- Straight-segment primitives of entire functions are entire. -/
theorem differentiable_primitive {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (primitive f) := fun z => (hasDerivAt_primitive hf z).differentiableAt

/-- Filling in a removable quotient at the origin does not change a segment integral. -/
theorem primitive_dslope_zero {f : ℂ → ℂ} (hf0 : f 0=0) (z : ℂ) :
    primitive (dslope f 0) z=primitive (fun t=>f t/t) z := by
  by_cases hz : z=0
  · subst z; simp [primitive,segmentIntegral]
  simp only [primitive,segmentIntegral,sub_zero,zero_add]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ t : ℝ, t≠0 := by simp [MeasureTheory.ae_iff]
  filter_upwards [hne] with t ht _
  rw [dslope_of_ne _ (mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) hz),slope_def_field,hf0]
  simp

/-- The straight-segment convention agrees with interval integration on the real axis. -/
theorem primitive_ofReal (f : ℂ → ℂ) (x : ℝ) :
    primitive f x=∫ t : ℝ in 0..x, f t := by
  have h := intervalIntegral.smul_integral_comp_mul_right (fun t : ℝ => f t)
    (a:=0) (b:=1) x
  simpa [primitive, segmentIntegral, Complex.real_smul] using h

/-- The based primitive vanishes at its base point. -/
@[simp] theorem primitive_zero (f : ℂ → ℂ) : primitive f 0=0 := by
  simp [primitive, segmentIntegral]

/-- Uniform approach to infinity in a closed principal sector. -/
def sector (α : ℝ) : Filter ℂ :=
  comap norm atTop ⊓ 𝓟 {z : ℂ | z ≠ 0 ∧ |arg z| ≤ α}
/-- Uniform approach to infinity in a closed sector on the logarithmic plane. -/
def logSector (α : ℝ) : Filter ℂ :=
  comap (fun w : ℂ => Real.exp w.re) atTop ⊓ 𝓟 {w : ℂ | |w.im| ≤ α}
/-- Numerator, denominator and termination flag of a finite continued fraction.
Mathlib’s `GenContFract.nextConts` supplies the recurrence. Continuants avoid
nested division by an intermediate zero. A zero numerator
at a positive index terminates the fraction and freezes subsequent convergents. -/
def cfContinuants (a b : ℕ → ℂ) (k : ℕ) : ℕ → ℂ × ℂ × Bool
  | 0 => (0, 1, false)
  | 1 => (a k, b k, false)
  | n+2 =>
    let u := cfContinuants a b k (n+1)
    let v := cfContinuants a b k n
    if u.2.2 = true ∨ a (k+n+1) = 0 then (u.1, u.2.1, true)
    else
      let p := GenContFract.nextConts (a (k+n+1)) (b (k+n+1))
        ⟨v.1, v.2.1⟩ ⟨u.1, u.2.1⟩
      (p.a, p.b, false)
/-- Finite continued fraction as a ratio of continuants, with exact termination. -/
def cfTail (a b : ℕ → ℂ) (k N : ℕ) : ℂ :=
  let p := cfContinuants a b k N
  p.1/p.2.1
/-- Convergence of the specified finite continued fractions. -/
def HasContinuedFraction (a b : ℕ → ℂ) (v : ℂ) : Prop :=
  Tendsto (cfTail a b 0) atTop (𝓝 v)
/-- The odd product 1·3···(2n+1). -/
def oddProduct (n : ℕ) : ℂ := ∏ j ∈ Finset.range (n+1), (2*j+1 : ℂ)
/-- Spherical j_n, with the removable value at zero supplied explicitly. -/
def sphericalJ (n : ℕ) (z : ℂ) : ℂ :=
  Real.sqrt π * z ^ n / (2 : ℂ) ^ (n+1) *
    regularizedHGFun ∅ {(n : ℂ)+3/2} (-z^2/4)
/-- Modified spherical i_n, including its removable value at zero. -/
def sphericalI (n : ℕ) (z : ℂ) : ℂ :=
  Real.sqrt π * z ^ n / (2 : ℂ) ^ (n+1) *
    regularizedHGFun ∅ {(n : ℂ)+3/2} (z^2/4)
/-- A zero chosen by the count of strictly closer zeros; existence is a theorem. -/
def orderedZero (f : ℂ → ℂ) (S : Set ℂ) (k : ℕ) : ℂ :=
  Classical.epsilon (fun z => z ∈ S ∧ f z = 0 ∧
    ({w : ℂ | w ∈ S ∧ f w = 0 ∧ ‖w‖ < ‖z‖} : Set ℂ).ncard = k-1)

/-- Coefficients extracted successively by limits at positive infinity.
Theorems asserting expansions must separately establish that these limits exist. -/
def asymptoticCoeff (f : ℝ → ℂ) : ℕ → ℂ
  | 0 => limUnder atTop f
  | n+1 => limUnder atTop (fun t : ℝ => (t : ℂ)^(n+1) *
      (f t-∑ j ∈ Finset.range (n+1), asymptoticCoeff f (n-j)*(t : ℂ)^(-((n-j : ℕ) : ℤ))))
termination_by n => n

end DLMF
