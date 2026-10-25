/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.MeijerG
public import DLMF.GeneralizedHypergeometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Meijer G expansions, identities and differential equations (DLMF §§16.17–16.27)

All G-function equalities retain actual convergence predicates and logarithmic arguments.
The residue formula is regularized before Gamma factors are cancelled; lower denominator poles
and repeated bottom poles are treated by regularized expansions and combined parameter limits.
The ordinary hypergeometric identity excludes terminating upper poles only in its direct Gamma
quotient form, with the terminating limits stated separately. Divergent-series Barnes values
use the separate convergence predicate from `Basic`.

The differential equation retains the integer parity exponent. Fundamental G-solutions require
nonresonance; a normalized parameter-limit statement supplies resonant frames. Bibliographic,
graphical, physical-application and numerical-software discussion is recorded in the ledger.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Polynomial
open scoped Real Topology Nat
namespace DLMF.Hypergeometric

/-- Integer parity exponent; natural subtraction would change the Meijer normalization. -/
def meijerParity (P : MeijerGParameters) : ℂ := (-1:ℂ)^((P.p:ℤ)-P.m-P.n)

/-- The simple numerator bottom poles needed for the individual residue expansion. -/
def MeijerGParameters.SimpleBottom (P : MeijerGParameters) : Prop :=
  ∀ j<P.m,∀ k<P.m,j≠k→∀ r : ℤ,P.b[j]!-P.b[k]!≠r

/-- Hypergeometric upper parameters in the residue at the kth numerator bottom pole. -/
def meijerResidueUpper (P : MeijerGParameters) (k : ℕ) : Multiset ℂ :=
  ((P.a.map fun a => 1+P.b[k]!-a) : Multiset ℂ)

/-- Lower parameters omit exactly the kth entry, preserving repeated other entries. -/
def meijerResidueLower (P : MeijerGParameters) (k : ℕ) : Multiset ℂ :=
  (((P.b.eraseIdx k).map fun b => 1+P.b[k]!-b) : Multiset ℂ)

/-- The source A_{p,q,k}^{m,n}, with indices starting at zero. It is used only for k<m≤q. -/
@[dlmf 16.17.E3]
def meijerResidueCoeff (P : MeijerGParameters) (k : ℕ) (w : ℂ) : ℂ :=
  (((P.b.take P.m).eraseIdx k).map fun b => Gamma (b-P.b[k]!)).prod*
  ((P.a.take P.n).map fun a => Gamma (1+P.b[k]!-a)).prod*Complex.exp (P.b[k]!*w)*
  ((P.b.drop P.m).map fun b => (Gamma (1+P.b[k]!-b))⁻¹).prod*
  ((P.a.drop P.n).map fun a => (Gamma (a-P.b[k]!))⁻¹).prod

/-- The residue coefficient after regularization of the pF(q-1) factor. Denominator Gamma
zeros are cancelled analytically before evaluation, including exceptional lower parameters. -/
def meijerResidueRegularCoeff (P : MeijerGParameters) (k : ℕ) (w : ℂ) : ℂ :=
  (((P.b.take P.m).eraseIdx k).map fun b => Gamma (b-P.b[k]!)).prod*
  ((P.a.take P.n).map fun a => Gamma (1+P.b[k]!-a)).prod*Complex.exp (P.b[k]!*w)*
  (((P.b.take P.m).eraseIdx k).map fun b => Gamma (1+P.b[k]!-b)).prod*
  ((P.a.drop P.n).map fun a => (Gamma (a-P.b[k]!))⁻¹).prod

/-- Actual hypergeometric-series region for the residue expansion; continuations follow below. -/
def meijerResidueRegion (P : MeijerGParameters) (w : ℂ) : Prop :=
  P.p<P.q ∨ (P.p=P.q ∧ 1≤P.p ∧ w.re<0)

/-- The finite sum of regularized residue contributions. -/
def meijerResidueExpansionLog (P : MeijerGParameters) (w : ℂ) : ℂ :=
  ∑ k∈Finset.range P.m,meijerResidueRegularCoeff P k w*
    genRegularizedHG (meijerResidueUpper P k) (meijerResidueLower P k) (meijerParity P*Complex.exp w)

/-- A generic perturbation splits all bottom-parameter integer collisions. -/
def meijerSplitBottom (P : MeijerGParameters) (t : ℂ) : MeijerGParameters :=
  {P with b:=(P.b.zipIdx.map (fun p => p.1+(p.2:ℂ)*t))}

/-- The full simple-bottom-pole formula, including exceptional nonnumerator lower parameters. -/
@[dlmf 16.17.E2]
theorem meijerG_regularized_residue_expansion {P : MeijerGParameters} (hP : P.Valid) (hs : P.SimpleBottom)
    {w : ℂ} (hw : meijerResidueRegion P w) : meijerGLog P w=meijerResidueExpansionLog P w := by
  sorry

/-- 16.17.E2: meijerG ordinary residue expansion. -/
@[dlmf 16.17.E2]
theorem meijerG_ordinary_residue_expansion {P : MeijerGParameters} (hP : P.Valid) (hs : P.SimpleBottom)
    (hreg : ∀ k<P.m,genDenRegular (meijerResidueLower P k))
    {w : ℂ} (hw : meijerResidueRegion P w) :
    meijerGLog P w=∑ k∈Finset.range P.m,meijerResidueCoeff P k w*
      genHG (meijerResidueUpper P k) (meijerResidueLower P k) (meijerParity P*Complex.exp w) := by
  sorry

/-- Integer bottom-pole collisions are combined before taking the parameter limit. -/
@[dlmf 16.17.E2]
theorem meijerG_coalescing_residue_limit {P : MeijerGParameters} (hP : P.Valid) {w : ℂ}
    (hw : meijerResidueRegion P w) :
    Tendsto (fun t : ℂ => meijerResidueExpansionLog (meijerSplitBottom P t) w)
      (𝓝[≠] 0) (𝓝 (meijerGLog P w)) := by
  sorry

/-- Matching branches of the residue identity continue beyond the hypergeometric series disk. -/
@[dlmf 16.17.E2]
theorem meijerG_residue_continuation {P : MeijerGParameters} (hP : P.Valid) (hs : P.SimpleBottom)
    {F G : ℝ→ℂ→ℂ} {γ : ℝ→ℂ} (hγ : ContinuousOn γ (Icc 0 1))
    (h0 : meijerResidueRegion P (γ 0))
    (hF : TauCeti.IsAnalyticContinuationAlong F γ (Icc 0 1))
    (hG : TauCeti.IsAnalyticContinuationAlong G γ (Icc 0 1))
    (hF0 : F 0=ᶠ[𝓝 (γ 0)] meijerGLog P)
    (hG0 : G 0=ᶠ[𝓝 (γ 0)] meijerResidueExpansionLog P) :
    F 1=ᶠ[𝓝 (γ 1)] G 1 := by
  sorry

/-- Inversion swaps the numerator Gamma blocks and maps every parameter to one minus itself. -/
def MeijerGParameters.dual (P : MeijerGParameters) : MeijerGParameters :=
  ⟨P.b.map (fun b => 1-b),P.a.map (fun a => 1-a),P.n,P.m⟩

/-- A common complex parameter shift preserves the full ordered block structure. -/
def MeijerGParameters.shift (P : MeijerGParameters) (μ : ℂ) : MeijerGParameters :=
  {P with a:=P.a.map (·+μ),b:=P.b.map (·+μ)}

/-- An added upper numerator Gamma factor and matching lower denominator factor. -/
def MeijerGParameters.cancelExtension (P : MeijerGParameters) (a : ℂ) : MeijerGParameters :=
  ⟨a::P.a,P.b++[a],P.m,P.n+1⟩

/-- Duplication of each ordered parameter, preserving both initial blocks. -/
def MeijerGParameters.double (P : MeijerGParameters) : MeijerGParameters :=
  ⟨P.a.flatMap (fun a => [a/2,a/2+1/2]),P.b.flatMap (fun b => [b/2,b/2+1/2]),2*P.m,2*P.n⟩

/-- The upper first-parameter lowering in the derivative identity. -/
def MeijerGParameters.lowerFirst (P : MeijerGParameters) : MeijerGParameters :=
  {P with a:=P.a.modify 0 (·-1)}

/-- The beta-convolution parameter extension. -/
def MeijerGParameters.betaExtension (P : MeijerGParameters) (a b : ℂ) : MeijerGParameters :=
  ⟨a::P.a,P.b++[b],P.m,P.n+1⟩

/-- Hypergeometric parameters as a Meijer G with first bottom parameter zero. -/
def meijerHypergeomData (A B : List ℂ) : MeijerGParameters :=
  ⟨A.map (fun a => 1-a),0::B.map (fun b => 1-b),1,A.length⟩

/-- The normalized G branch has the removable origin value supplied explicitly. -/
def meijerHypergeomBranch (A B : List ℂ) (z : ℂ) : ℂ :=
  if z=0 then 1 else genGamma (B:Multiset ℂ)/genGamma (A:Multiset ℂ)*
    meijerGLog (meijerHypergeomData A B) (Complex.log (-z))

/-- 16.18.E1: genHG meijerG. -/
@[dlmf 16.18.E1]
theorem genHG_meijerG (A B : List ℂ) (hcount : A.length≤B.length+1)
    (hA : genDenRegular (A:Multiset ℂ)) (hB : genDenRegular (B:Multiset ℂ))
    {z : ℂ} (hz : z∈cutPlane) : genHG (A:Multiset ℂ) (B:Multiset ℂ) z=meijerHypergeomBranch A B z := by
  sorry

/-- The dual G uses the inverse logarithmic sheet, avoiding a principal-log bank mismatch. -/
@[dlmf 16.18.E1]
theorem genHG_meijerG_dual (A B : List ℂ) (hcount : A.length≤B.length+1)
    (hA : genDenRegular (A:Multiset ℂ)) (hB : genDenRegular (B:Multiset ℂ))
    {z : ℂ} (hz : z∈cutPlane) (hz0 : z≠0) :
    genHG (A:Multiset ℂ) (B:Multiset ℂ) z=genGamma (B:Multiset ℂ)/genGamma (A:Multiset ℂ)*
      meijerGLog (meijerHypergeomData A B).dual (-Complex.log (-z)) := by
  sorry

/-- Terminating upper poles are retained as limits of the whole normalized G product. -/
@[dlmf 16.18.E1]
theorem genHG_meijerG_terminating_limit (A B : List ℂ) (hB : genDenRegular (B:Multiset ℂ))
    (hA : genDenRegular (A:Multiset ℂ)) (N : ℕ) {z : ℂ} (hz : z∈cutPlane) :
    Tendsto (fun a : ℂ => meijerHypergeomBranch (a::A) B z) (𝓝[≠] (-(N:ℂ)))
      (𝓝 (genFiniteHG N ((-(N:ℂ))::ₘ(A:Multiset ℂ)) (B:Multiset ℂ) z)) := by
  sorry

/-- Divergent-series regimes use actual Barnes convergence, never the totalized native sum. -/
@[dlmf 16.18.E1]
theorem genBarnes_meijerG (A B : List ℂ) (hA : genDenRegular (A:Multiset ℂ))
    (hB : genDenRegular (B:Multiset ℂ)) {w v : ℂ} {L : MeijerGContour}
    (hL : L.Admissible (meijerHypergeomData A B))
    (hw : meijerGContourRegion (meijerHypergeomData A B) L.kind w)
    (hBarnes : genHasBarnesValueLog (A:Multiset ℂ) (B:Multiset ℂ) L.path w v) :
    v=genGamma (B:Multiset ℂ)/genGamma (A:Multiset ℂ)*meijerGLog (meijerHypergeomData A B) w := by
  sorry

/-- 16.19.E1: meijerG inversion. -/
@[dlmf 16.19.E1]
theorem meijerG_inversion {P : MeijerGParameters} {w : ℂ} (h : MeijerGConvergesLog P (-w))
    (hdual : MeijerGConvergesLog P.dual w) : meijerGLog P (-w)=meijerGLog P.dual w := by
  sorry

/-- 16.19.E2: meijerG parameter shift. -/
@[dlmf 16.19.E2]
theorem meijerG_parameter_shift {P : MeijerGParameters} (μ : ℂ) {w : ℂ}
    (h : MeijerGConvergesLog P w) (hshift : MeijerGConvergesLog (P.shift μ) w) :
    Complex.exp (μ*w)*meijerGLog P w=meijerGLog (P.shift μ) w := by
  sorry

/-- 16.19.E3: meijerG cancel parameter. -/
@[dlmf 16.19.E3]
theorem meijerG_cancel_parameter {P : MeijerGParameters} (a : ℂ) {w : ℂ}
    (h : MeijerGConvergesLog P w) (hext : MeijerGConvergesLog (P.cancelExtension a) w) :
    meijerGLog (P.cancelExtension a) w=meijerGLog P w := by
  sorry

/-- 16.19.E4: meijerG duplication. -/
@[dlmf 16.19.E4]
theorem meijerG_duplication {P : MeijerGParameters} {w : ℂ} (h : MeijerGConvergesLog P w)
    (hd : MeijerGConvergesLog P.double (2*w+((2*P.p:ℂ)-2*P.q)*Real.log 2)) :
    meijerGLog P w=
      (2:ℂ)^((P.p:ℂ)+1+P.b.sum-P.m-P.n-P.a.sum)/
      (π:ℂ)^((P.m:ℂ)+P.n-((P.p:ℂ)+P.q)/2)*
      meijerGLog P.double (2*w+((2*P.p:ℂ)-2*P.q)*Real.log 2) := by
  sorry

/-- The displayed plus-sign recurrence requires the first upper parameter in the numerator block. -/
@[dlmf 16.19.E5]
theorem meijerG_log_derivative {P : MeijerGParameters} (hn : 0<P.n) {w : ℂ}
    (h : MeijerGConvergesLog P w) (hl : MeijerGConvergesLog P.lowerFirst w) :
    deriv (meijerGLog P) w=meijerGLog P.lowerFirst w+(P.a[0]!-1)*meijerGLog P w := by
  sorry

/-- Exact Fubini certificate for beta convolution. It states the actual joint integrability,
contour separation, and inner beta conditions omitted from the short DLMF formula. -/
def MeijerGBetaCertificate (P : MeijerGParameters) (w a b : ℂ) (L : MeijerGContour) : Prop :=
  L.Admissible P ∧ L.Admissible (P.betaExtension a b) ∧
  meijerGContourRegion P L.kind w ∧ meijerGContourRegion (P.betaExtension a b) L.kind w ∧
  0<(a-b).re ∧ (∀ u : ℝ,a.re-1<(L.path u).re) ∧
  (∀ t∈Ioo (0:ℝ) 1,meijerGContourRegion P L.kind (w+Real.log t)) ∧
  IntegrableOn (fun p : ℝ×ℝ => (p.1:ℂ)^(-a)*((1-p.1:ℝ):ℂ)^(a-b-1)*
    deriv L.path p.2*meijerGKernelLog P (w+Real.log p.1) (L.path p.2)) (Ioo (0:ℝ) 1×ˢuniv)

/-- 16.19.E6: meijerG beta convolution. -/
@[dlmf 16.19.E6]
theorem meijerG_beta_convolution {P : MeijerGParameters} {w a b : ℂ} {L : MeijerGContour}
    (h : MeijerGBetaCertificate P w a b L) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^(-a)*((1-t:ℝ):ℂ)^(a-b-1)*
      meijerGLog P (w+Real.log t)) (Ioo (0:ℝ) 1) ∧
    (∫ t in (0:ℝ)..1,(t:ℂ)^(-a)*((1-t:ℝ):ℂ)^(a-b-1)*meijerGLog P (w+Real.log t))=
      Gamma (a-b)*meijerGLog (P.betaExtension a b) w := by
  sorry

/-- A product of shifted ordinary derivatives on the logarithmic plane. -/
def meijerLogOperator : List ℂ→(ℂ→ℂ)→(ℂ→ℂ)
  | [],f => f
  | a::A,f => fun w => deriv (meijerLogOperator A f) w-a*meijerLogOperator A f w

/-- The Meijer differential equation on the logarithmic plane; d/dw is z*d/dz. -/
@[dlmf 16.21.E1]
def MeijerLogEquation (P : MeijerGParameters) (f : ℂ→ℂ) (w : ℂ) : Prop :=
  meijerParity P*Complex.exp w*meijerLogOperator (P.a.map (·-1)) f w-
    meijerLogOperator P.b f w=0

/-- Coefficients of a product of Euler operators, as ordinary-derivative polynomials. -/
def meijerThetaCoeff : List ℂ→ℕ→ℂ[X]
  | [],k => if k=0 then 1 else 0
  | a::A,k => X*(meijerThetaCoeff A k).derivative-C a*meijerThetaCoeff A k+
      if k=0 then 0 else X*meijerThetaCoeff A (k-1)

/-- Ordinary-derivative coefficients of the displayed Meijer equation. -/
def meijerODECoeff (P : MeijerGParameters) (k : ℕ) : ℂ[X] :=
  C (meijerParity P)*X*meijerThetaCoeff (P.a.map (·-1)) k-meijerThetaCoeff P.b k

/-- Fuchs's finite-point criterion, stated through actual analytic removable extensions. -/
def MeijerRegularSingularAt (P : MeijerGParameters) (z : ℂ) : Prop :=
  let N := max P.p P.q
  0<N ∧ (meijerODECoeff P N).eval z=0 ∧ ∀ k<N,∃ f : ℂ→ℂ,AnalyticAt ℂ f z ∧
    f=ᶠ[𝓝[≠] z] (fun u => (u-z)^(N-k)*(meijerODECoeff P k).eval u/(meijerODECoeff P N).eval u)

/-- Irregular means singular and not Fuchs regular for this ordinary differential equation. -/
def MeijerIrregularSingularAt (P : MeijerGParameters) (z : ℂ) : Prop :=
  (meijerODECoeff P (max P.p P.q)).eval z=0 ∧ ¬MeijerRegularSingularAt P z

/-- The jth displayed G-solution, with the jth bottom parameter moved to the first position. -/
@[dlmf 16.21.E2]
def meijerFundamentalTerm (P : MeijerGParameters) (j : ℕ) (w : ℂ) : ℂ :=
  meijerGLog ⟨P.a,P.b[j]!::P.b.eraseIdx j,1,P.p⟩
    (w+(((P.p:ℤ)-P.m-P.n-1:ℤ):ℂ)*π*I)

/-- Full generic hypotheses for the displayed G-frame. Resonance is handled by limits below. -/
def MeijerGenericFrame (P : MeijerGParameters) : Prop :=
  P.p≤P.q ∧ 0<P.q ∧
  (∀ j<P.q,∀ k<P.q,j≠k→∀ r : ℤ,P.b[j]!-P.b[k]!≠r) ∧
  (∀ a∈P.a,∀ b∈P.b,∀ k : ℕ,a-b≠(k:ℂ)+1)

/-- A perturbation avoids both numerator pole collisions and integer exponent resonances. -/
def meijerGenericDeformation (P : MeijerGParameters) (t : ℂ) : MeijerGParameters :=
  ⟨P.a.zipIdx.map (fun p => p.1+((p.2+P.q+1:ℕ):ℂ)*t),
    P.b.zipIdx.map (fun p => p.1+(p.2:ℂ)*t),P.m,P.n⟩

/-- 16.21.E1: meijerG log ode. -/
@[dlmf 16.21.E1]
theorem meijerG_log_ode {P : MeijerGParameters} {w : ℂ} (h : MeijerGConvergesLog P w) :
    MeijerLogEquation P (meijerGLog P) w := by
  sorry

/-- Euler-operator product coefficients vanish above the number of factors. -/
lemma ghbR4_meijerThetaCoeff_eq_zero (A : List ℂ) :
    ∀ k, A.length < k → meijerThetaCoeff A k = 0 := by
  induction A with
  | nil => intro k hk; simp [meijerThetaCoeff]; omega
  | cons a A ih =>
    intro k hk
    simp only [List.length_cons] at hk
    have h1 := ih k (by omega)
    have h2 := ih (k-1) (by omega)
    simp [meijerThetaCoeff, h1, h2]

/-- The top Euler-operator product coefficient is the monomial `X^length`. -/
lemma ghbR4_meijerThetaCoeff_length (A : List ℂ) :
    meijerThetaCoeff A A.length = X ^ A.length := by
  induction A with
  | nil => simp [meijerThetaCoeff]
  | cons a A ih =>
    have h1 := ghbR4_meijerThetaCoeff_eq_zero A (A.length + 1) (by omega)
    simp [meijerThetaCoeff, h1, ih, pow_succ, mul_comm]

/-- 16.21: meijerG equation order. -/
@[dlmf 16.21]
theorem meijerG_equation_order (P : MeijerGParameters) :
    (∀ k : ℕ,max P.p P.q<k→meijerODECoeff P k=0) ∧
    meijerODECoeff P (max P.p P.q)=
      if P.p<P.q then -(X:ℂ[X])^P.q else if P.q<P.p then
        C (meijerParity P)*X^(P.p+1) else (C (meijerParity P)*X-1)*X^P.p := by
  have hA : ∀ k, P.p < k → meijerThetaCoeff (P.a.map (·-1)) k = 0 := fun k hk =>
    ghbR4_meijerThetaCoeff_eq_zero _ k (by simpa [MeijerGParameters.p] using hk)
  have hB : ∀ k, P.q < k → meijerThetaCoeff P.b k = 0 := fun k hk =>
    ghbR4_meijerThetaCoeff_eq_zero _ k (by simpa [MeijerGParameters.q] using hk)
  have hA' : meijerThetaCoeff (P.a.map (·-1)) P.p = X ^ P.p := by
    simpa [MeijerGParameters.p] using ghbR4_meijerThetaCoeff_length (P.a.map (·-1))
  have hB' : meijerThetaCoeff P.b P.q = X ^ P.q := ghbR4_meijerThetaCoeff_length P.b
  refine ⟨fun k hk => ?_, ?_⟩
  · simp [meijerODECoeff, hA k (by omega), hB k (by omega)]
  · split_ifs with h1 h2
    · rw [max_eq_right h1.le]; simp [meijerODECoeff, hA _ h1, hB']
    · rw [max_eq_left h2.le]; simp [meijerODECoeff, hB _ h2, hA', pow_succ]; ring
    · have : P.p = P.q := by omega
      rw [this, max_self]; rw [← this]
      simp [meijerODECoeff, hA', this ▸ hB']; ring

/-- Each Euler-operator product coefficient is a constant multiple of `X^k`. -/
lemma ghbR4_meijerThetaCoeff_monomial (A : List ℂ) :
    ∀ k, ∃ c : ℂ, meijerThetaCoeff A k = C c * X ^ k := by
  induction A with
  | nil => intro k; refine ⟨if k = 0 then 1 else 0, ?_⟩; by_cases hk : k = 0 <;> simp [meijerThetaCoeff, hk]
  | cons a A ih =>
    intro k
    obtain ⟨c, hc⟩ := ih k
    rcases k with _ | k
    · refine ⟨-a * c, ?_⟩
      simp [meijerThetaCoeff, hc]
    · obtain ⟨c', hc'⟩ := ih k
      refine ⟨c * (k + 1) - a * c + c', ?_⟩
      simp only [meijerThetaCoeff, hc, hc', Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
      simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_X_pow]
      simp only [map_add, map_sub, map_mul, pow_succ]
      push_cast
      simp only [map_add, map_one, map_natCast]
      ring

/-- The integer parity sign squares to one. -/
lemma ghbR4_meijerParity_sq (P : MeijerGParameters) : meijerParity P ^ 2 = 1 := by
  unfold meijerParity
  rw [← zpow_natCast, ← zpow_mul]
  rw [mul_comm, zpow_mul]; norm_num

/-- Each Meijer ODE coefficient has the form `ε u c₁ u^k - c₂ u^k`. -/
lemma ghbR4_meijerODECoeff_form (P : MeijerGParameters) (k : ℕ) :
    ∃ c₁ c₂ : ℂ, ∀ u : ℂ, (meijerODECoeff P k).eval u =
      meijerParity P * u * c₁ * u ^ k - c₂ * u ^ k := by
  obtain ⟨c₁, h₁⟩ := ghbR4_meijerThetaCoeff_monomial (P.a.map (·-1)) k
  obtain ⟨c₂, h₂⟩ := ghbR4_meijerThetaCoeff_monomial P.b k
  refine ⟨c₁, c₂, fun u => ?_⟩
  simp [meijerODECoeff, h₁, h₂]; ring


/-- The integer parity sign is nonzero. -/
lemma ghbR4_meijerParity_ne_zero (P : MeijerGParameters) : meijerParity P ≠ 0 := by
  intro h; have := ghbR4_meijerParity_sq P; rw [h] at this; norm_num at this

/-- For `p ≤ q` and `q > 0`, zero is a regular singular point of the Meijer equation. -/
lemma ghbR4_regular_zero (P : MeijerGParameters) (hpq : P.p ≤ P.q) (hq : 0 < P.q) :
    MeijerRegularSingularAt P 0 := by
  have hN : max P.p P.q = P.q := max_eq_right hpq
  obtain ⟨-, hord⟩ := meijerG_equation_order P
  have hpar := ghbR4_meijerParity_ne_zero P
  refine ⟨by omega, ?_, ?_⟩
  · obtain ⟨c₁, c₂, h⟩ := ghbR4_meijerODECoeff_form P (max P.p P.q)
    rw [h]; rw [hN]; simp [zero_pow hq.ne']
  · intro k hk
    rw [hN] at hk ⊢
    obtain ⟨c₁, c₂, h⟩ := ghbR4_meijerODECoeff_form P k
    rw [← hN, hord, hN]
    rcases lt_or_eq_of_le hpq with hlt | heq
    · refine ⟨fun u => -(meijerParity P * u * c₁ - c₂), by fun_prop, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu : u ≠ 0 := hu
      simp only [hlt, ite_true, h, sub_zero, eval_neg, eval_pow, eval_X]
      have : u ^ (P.q - k) * u ^ k = u ^ P.q := by rw [← pow_add]; congr 1; omega
      field_simp
      linear_combination (meijerParity P * u * c₁ - c₂) * this
    · have h1 : ¬ P.p < P.q := by omega
      have h2 : ¬ P.q < P.p := by omega
      refine ⟨fun u => (meijerParity P * u * c₁ - c₂) / (meijerParity P * u - 1),
        AnalyticAt.div (by fun_prop) (by fun_prop) (by simp), ?_⟩
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu : u ≠ 0 := hu
      simp only [h1, h2, ite_false, h, sub_zero, eval_mul, eval_sub, eval_C, eval_X, eval_one,
        eval_pow]
      rw [heq]
      have : u ^ (P.q - k) * u ^ k = u ^ P.q := by rw [← pow_add]; congr 1; omega
      by_cases hd : meijerParity P * u - 1 = 0
      · simp [hd]
      · field_simp
        linear_combination (-(meijerParity P * u * c₁ - c₂)) * this


/-- Inversion represents infinity; the two source singularity regimes are retained. -/
@[dlmf 16.21]
theorem meijerG_singularities {P : MeijerGParameters} (hP : P.Valid) (hpq : P.p≤P.q) (hq : 0<P.q) :
    MeijerRegularSingularAt P 0 ∧
    (P.p<P.q→MeijerIrregularSingularAt P.dual 0) ∧
    (P.p=P.q→MeijerRegularSingularAt P (meijerParity P) ∧ MeijerRegularSingularAt P.dual 0) ∧
    (∀ z : ℂ,z≠0→(P.p=P.q→z≠meijerParity P)→
      (meijerODECoeff P (max P.p P.q)).eval z≠0) := by
  have hdp : P.dual.p = P.q := by simp [MeijerGParameters.dual, MeijerGParameters.p, MeijerGParameters.q]
  have hdq : P.dual.q = P.p := by simp [MeijerGParameters.dual, MeijerGParameters.p, MeijerGParameters.q]
  have hpar := ghbR4_meijerParity_ne_zero P
  have hsq := ghbR4_meijerParity_sq P
  obtain ⟨-, hord⟩ := meijerG_equation_order P
  refine ⟨ghbR4_regular_zero P hpq hq, fun hlt => ?_, fun heq => ⟨?_, ?_⟩, ?_⟩
  · -- irregular singularity of the dual at zero
    have hN : max P.dual.p P.dual.q = P.q := by rw [hdp, hdq]; exact max_eq_left hpq
    obtain ⟨-, hordd⟩ := meijerG_equation_order P.dual
    have hpard := ghbR4_meijerParity_ne_zero P.dual
    refine ⟨?_, ?_⟩
    · obtain ⟨c₁, c₂, h⟩ := ghbR4_meijerODECoeff_form P.dual (max P.dual.p P.dual.q)
      rw [h, hN]; simp [zero_pow hq.ne']
    · rintro ⟨-, -, hk⟩
      obtain ⟨f, hf, hfeq⟩ := hk P.p (by rw [hN]; exact hlt)
      obtain ⟨c, hc⟩ := ghbR4_meijerThetaCoeff_monomial (P.dual.a.map (·-1)) P.p
      have hb : meijerThetaCoeff P.dual.b P.p = X ^ P.p := by
        have := ghbR4_meijerThetaCoeff_length P.dual.b
        simpa [MeijerGParameters.dual, MeijerGParameters.p] using this
      have hcN : meijerODECoeff P.dual (max P.dual.p P.dual.q) =
          C (meijerParity P.dual) * X ^ (P.q + 1) := by
        rw [hordd]
        split_ifs <;> first | omega | rw [hdp]
      rw [hcN] at hfeq
      have hev : ∀ᶠ u in 𝓝[≠] (0:ℂ), u⁻¹ = meijerParity P.dual * (c - f u) := by
        filter_upwards [hfeq, self_mem_nhdsWithin] with u hu hu0
        have hu0 : u ≠ 0 := hu0
        rw [hu]
        simp only [meijerODECoeff, hc, hb, sub_zero, eval_mul, eval_sub, eval_C, eval_X,
          eval_pow, hN]
        have hpow : u ^ (P.q - P.p) * u ^ P.p = u ^ P.q := by
          rw [← pow_add]; congr 1; omega
        have hd2 : meijerParity P.dual ^ 2 = 1 := ghbR4_meijerParity_sq P.dual
        field_simp
        linear_combination (u * c * meijerParity P.dual - 1) * u * hpow
      have ht : Tendsto (fun u : ℂ => ‖meijerParity P.dual * (c - f u)‖) (𝓝[≠] 0)
          (𝓝 ‖meijerParity P.dual * (c - f 0)‖) :=
        ((hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).const_sub c
          |>.const_mul _).norm
      have hinf := tendsto_norm_inv_nhdsNE_zero_atTop (α := ℂ)
      have := hinf.congr' (hev.mono fun u hu => by rw [hu])
      exact not_tendsto_atTop_of_tendsto_nhds ht this
  · -- regular singularity at the parity point
    have hN : max P.p P.q = P.q := max_eq_right hpq
    have hcN : ∀ u, (meijerODECoeff P (max P.p P.q)).eval u =
        meijerParity P * (u - meijerParity P) * u ^ P.q := by
      intro u
      rw [hord]
      split_ifs <;> try omega
      rw [heq]
      simp only [eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_pow]
      linear_combination u ^ P.q * hsq
    refine ⟨by omega, by rw [hcN]; ring, ?_⟩
    intro k hk
    rw [hN] at hk
    refine ⟨fun u => (u - meijerParity P) ^ (P.q - k - 1) * (meijerODECoeff P k).eval u /
      (meijerParity P * u ^ P.q), AnalyticAt.div ((by fun_prop : AnalyticAt ℂ
        (fun u : ℂ => (u - meijerParity P) ^ (P.q - k - 1)) _).mul
          ((meijerODECoeff P k).differentiable.analyticAt _)) (by fun_prop)
        (mul_ne_zero hpar (pow_ne_zero _ hpar)), ?_⟩
    have hne : ∀ᶠ u in 𝓝[≠] (meijerParity P), u ≠ 0 :=
      nhdsWithin_le_nhds (isOpen_ne.mem_nhds hpar)
    filter_upwards [hne, self_mem_nhdsWithin] with u hu0 hu1
    have hu1 : u - meijerParity P ≠ 0 := sub_ne_zero.mpr hu1
    rw [hcN, hN]
    have hpow : (u - meijerParity P) ^ (P.q - k) =
        (u - meijerParity P) ^ (P.q - k - 1) * (u - meijerParity P) := by
      rw [← pow_succ]; congr 1; omega
    rw [hpow]
    field_simp
  · exact ghbR4_regular_zero P.dual (by omega) (by omega)
  · intro z hz hzp
    rcases lt_or_eq_of_le hpq with hlt | heq
    · rw [hord]; simp [hlt, hz]
    · rw [hord]
      split_ifs <;> try omega
      simp only [eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_pow]
      refine mul_ne_zero ?_ (pow_ne_zero _ hz)
      intro h0
      apply hzp heq
      linear_combination meijerParity P * h0 - z * hsq

/-- 16.21.E2: meijerG fundamental frame. -/
@[dlmf 16.21.E2]
theorem meijerG_fundamental_frame {P : MeijerGParameters} (hP : P.Valid) (hg : MeijerGenericFrame P)
    {w : ℂ} (hw : w.re<0) :
    (∀ j<P.q,AnalyticAt ℂ (meijerFundamentalTerm P j) w ∧
      MeijerLogEquation P (meijerFundamentalTerm P j) w) ∧
    Matrix.det (fun i j : Fin P.q => iteratedDeriv i.val (meijerFundamentalTerm P j.val) w)≠0 := by
  sorry

/-- At integer exponent collisions, normalized combinations of the generic G-frame have a fundamental analytic limit. -/
@[dlmf 16.21.E2]
theorem meijerG_resonant_fundamental_limits {P : MeijerGParameters} (hP : P.Valid) (hpq : P.p≤P.q)
    (hq : 0<P.q) {w : ℂ} (hw : w.re<0) :
    ∃ U : Set ℂ,IsOpen U ∧ w∈U ∧ ∃ F : Fin P.q→ℂ→ℂ,∃ c : ℂ→ℕ→Fin P.q→ℂ,
      (∀ k,AnalyticOnNhd ℂ (F k) U ∧ ∀ u∈U,MeijerLogEquation P (F k) u) ∧
      (∀ i k : Fin P.q,iteratedDeriv i.val (F k) w=if i=k then 1 else 0) ∧
      (∀ k,TendstoLocallyUniformlyOn
        (fun t u => ∑ j∈Finset.range P.q,c t j k*meijerFundamentalTerm (meijerGenericDeformation P t) j u)
        (F k) (𝓝[≠] 0) U) := by
  sorry

/-- Cancel the removable upper/lower parameter collision before evaluating the terminating
Askey-Gasper coefficient; in particular alpha=-1 is retained. -/
def askeyGasperPolynomial (n : ℕ) (α x : ℝ) : ℝ :=
  1+∑ k∈Finset.range n,
    (ascPochhammer ℝ (k+1)).eval (-(n:ℝ))*
      (ascPochhammer ℝ (k+1)).eval ((n:ℝ)+α+2)/
      ((α+2*(k+1)+1)*(ascPochhammer ℝ k).eval (α+2)*((k+1)!:ℝ))*x^(k+1)

/-- The analytical positivity inequality retained independently of its application discussion. -/
@[dlmf 16.23.E1]
theorem askey_gasper_dlmf (n : ℕ) {α x : ℝ} (hα : -2<α) (hx : 0≤x) (hx1 : x<1) :
    0<askeyGasperPolynomial n α x := by
  sorry


/-- The Meijer kernel for pFq is exactly its separately convergent Barnes kernel. -/
@[dlmf 16.18.E1]
theorem meijer_hypergeometric_kernel (A B : List ℂ) (w s : ℂ) :
    meijerGKernelLog (meijerHypergeomData A B) w s=
      genBarnesKernelLog (A:Multiset ℂ) (B:Multiset ℂ) w s := by
  simp [meijerGKernelLog,meijerHypergeomData,genBarnesKernelLog,genGamma,genShift,
    List.map_map,←List.map_take,←List.map_drop,List.prod_inv,Function.comp_def,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]

/-- The normalized G expression has the prescribed removable hypergeometric origin. -/
@[dlmf 16.18.E1]
theorem meijer_hypergeometric_origin (A B : List ℂ) : meijerHypergeomBranch A B 0=1 := by
  simp [meijerHypergeomBranch]

/-- Degree zero of the acquired Askey-Gasper polynomial, including alpha=-1. -/
@[dlmf 16.23.E1]
theorem askey_gasper_degree_zero (α x : ℝ) : askeyGasperPolynomial 0 α x=1 := by
  simp [askeyGasperPolynomial]

/-- Inversion of the ordered parameter blocks is an involution. -/
theorem meijer_parameter_dual_involutive (P : MeijerGParameters) : P.dual.dual=P := by
  cases P
  simp [MeijerGParameters.dual,List.map_map,Function.comp_def]

/-- Relative contamination by a dominating mode diverges in either integration direction.
This is the analytical instability behind the intermediate-solution warning in DLMF16.25. -/
@[dlmf 16.25]
theorem intermediate_solution_instability {ι : Type*} {L R : Filter ι} {u v w : ι→ℂ}
    (hfast : Tendsto (fun i => ‖w i/v i‖) L atTop)
    (hslow : Tendsto (fun i => ‖u i/v i‖) R atTop)
    {ε η : ℂ} (hε : ε≠0) (hη : η≠0) :
    Tendsto (fun i => ‖(v i+ε*w i-v i)/v i‖) L atTop ∧
    Tendsto (fun i => ‖(v i+η*u i-v i)/v i‖) R atTop := by
  constructor
  · simpa only [add_sub_cancel_left,mul_div_assoc,norm_mul] using
      hfast.const_mul_atTop (norm_pos_iff.mpr hε)
  · simpa only [add_sub_cancel_left,mul_div_assoc,norm_mul] using
      hslow.const_mul_atTop (norm_pos_iff.mpr hη)

end DLMF.Hypergeometric
