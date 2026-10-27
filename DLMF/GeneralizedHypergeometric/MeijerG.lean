/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework

/-!
# Meijer G contours, normalization and convergence (DLMF §16.17)

Acquired 2026-10-24. Parameters retain their order and the numerator/denominator Gamma blocks.
The logarithmic argument is explicit: the kernel contains exp(w*s), so z=exp w and all sheets
are retained. Admissible contours have actual affine tails, smooth compact middle portions,
separate both pole families by winding certificates, and avoid every numerator Gamma pole.
All three DLMF contour types and their orientations are represented. Convergence is a theorem,
not part of the geometric contour certificate. Every integral value requires integrability.
The totalized choice function is used only with an explicit convergence predicate.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory
open scoped Real Topology Nat
namespace DLMF.Hypergeometric

/-- Ordered upper/lower parameter blocks and the two numerator Gamma counts. -/
structure MeijerGParameters where
  a : List ℂ
  b : List ℂ
  m : ℕ
  n : ℕ
  deriving Inhabited

/-- The upper parameter count. -/
def MeijerGParameters.p (P : MeijerGParameters) : ℕ := P.a.length

/-- The lower parameter count. -/
def MeijerGParameters.q (P : MeijerGParameters) : ℕ := P.b.length

/-- DLMF pole separation: a_k-b_j is never a positive integer in the two numerator blocks.
Bottom-parameter collisions are permitted; the contour definition retains their multiplicities. -/
def MeijerGParameters.Valid (P : MeijerGParameters) : Prop :=
  P.m≤P.q ∧ P.n≤P.p ∧ ∀ a∈P.a.take P.n,∀ b∈P.b.take P.m,∀ k : ℕ,a-b≠(k:ℂ)+1

/-- The Meijer G Gamma-ratio kernel; denominator factors are entire reciprocal Gamma functions. -/
@[dlmf 16.17.E1]
def meijerGKernelLog (P : MeijerGParameters) (w s : ℂ) : ℂ :=
  ((P.b.take P.m).map fun b => Gamma (b-s)).prod*
  ((P.a.take P.n).map fun a => Gamma (1-a+s)).prod*
  ((P.b.drop P.m).map fun b => (Gamma (1-b+s))⁻¹).prod*
  ((P.a.drop P.n).map fun a => (Gamma (a-s))⁻¹).prod*Complex.exp (s*w)

/-- The three DLMF contour geometries; loops have the orientations encoded below. -/
inductive MeijerContourKind | vertical | rightLoop | leftLoop
  deriving DecidableEq,Inhabited

/-- A smooth parameterized contour, before imposing pole and tail geometry. -/
structure MeijerGContour where
  path : ℝ→ℂ
  smooth : ContDiff ℝ 1 path
  kind : MeijerContourKind

/-- The exact affine tails capture the three integration paths, rather than arbitrary
oscillatory curves with the same endpoints at infinity. -/
def MeijerGContour.Geometry (L : MeijerGContour) : Prop :=
  ∃ T>0,∃ u v : ℂ,
    match L.kind with
    | .vertical => (∀ t : ℝ,t≤ -T→L.path t=u+I*t) ∧ (∀ t : ℝ,T≤t→L.path t=v+I*t)
    | .rightLoop => (∀ t : ℝ,t≤ -T→L.path t=u-t) ∧ (∀ t : ℝ,T≤t→L.path t=v+t)
    | .leftLoop => (∀ t : ℝ,t≤ -T→L.path t=u+t) ∧ (∀ t : ℝ,T≤t→L.path t=v-t)

/-- Closing a vertical truncation to its right, or closing a loop truncation at infinity. -/
def MeijerGContour.closingIntegral (L : MeijerGContour) (f : ℂ→ℂ) (R : ℝ) : ℂ :=
  match L.kind with
  | .vertical =>
      let A : ℂ := R+I*(L.path R).im
      let B : ℂ := R+I*(L.path (-R)).im
      DLMF.segmentIntegral f (L.path R) A+DLMF.segmentIntegral f A B+
        DLMF.segmentIntegral f B (L.path (-R))
  | _ => DLMF.segmentIntegral f (L.path R) (L.path (-R))

/-- The winding number of a closed truncation, expressed as a contour integral. -/
def MeijerGContour.winding (L : MeijerGContour) (c : ℂ) (R : ℝ) : ℂ :=
  (2*π*I)⁻¹*((∫ t in (-R)..R,deriv L.path t/(L.path t-c))+
    L.closingIntegral (fun s => (s-c)⁻¹) R)

/-- The contour avoids every numerator Gamma pole. -/
def MeijerGContour.AvoidsPoles (L : MeijerGContour) (P : MeijerGParameters) : Prop :=
  (∀ b∈P.b.take P.m,∀ k : ℕ,∀ t : ℝ,L.path t≠b+k) ∧
  (∀ a∈P.a.take P.n,∀ k : ℕ,∀ t : ℝ,L.path t≠a-1-k)

/-- Winding certificates separate the two infinite pole arrays, including all repeated poles.
Vertical paths are closed to the right; right loops wind negatively, left loops positively. -/
def MeijerGContour.Separates (L : MeijerGContour) (P : MeijerGParameters) : Prop :=
  (∀ b∈P.b.take P.m,∀ k : ℕ,
    Tendsto (fun R : ℝ => L.winding (b+k) R) atTop
      (𝓝 (if L.kind=.leftLoop then 0 else -1))) ∧
  (∀ a∈P.a.take P.n,∀ k : ℕ,
    Tendsto (fun R : ℝ => L.winding (a-1-k) R) atTop
      (𝓝 (if L.kind=.leftLoop then 1 else 0)))

/-- The complete geometric admissibility certificate, independent of the G-kernel integral. -/
def MeijerGContour.Admissible (L : MeijerGContour) (P : MeijerGParameters) : Prop :=
  P.Valid ∧ L.Geometry ∧ L.AvoidsPoles P ∧ L.Separates P

/-- Sufficient convergence region in the logarithmic argument for each DLMF contour type. -/
@[dlmf 16.17]
def meijerGContourRegion (P : MeijerGParameters) (kind : MeijerContourKind) (w : ℂ) : Prop :=
  match kind with
  | .vertical => P.p+P.q<2*(P.m+P.n) ∧
      |w.im|<((P.m:ℝ)+P.n-((P.p:ℝ)+P.q)/2)*π
  | .rightLoop => P.p<P.q ∨ (P.p=P.q ∧ 1≤P.p ∧ w.re<0)
  | .leftLoop => P.q<P.p ∨ (P.p=P.q ∧ 1≤P.p ∧ 0<w.re)

/-- A genuine Meijer G value is a convergent, correctly normalized admissible contour integral. -/
@[dlmf 16.17.E1]
def MeijerGHasValueLog (P : MeijerGParameters) (w v : ℂ) : Prop :=
  ∃ L : MeijerGContour,L.Admissible P ∧ meijerGContourRegion P L.kind w ∧
    Integrable (fun t : ℝ => deriv L.path t*meijerGKernelLog P w (L.path t)) ∧
    v=(2*π*I)⁻¹*∫ t : ℝ,deriv L.path t*meijerGKernelLog P w (L.path t)

/-- Existence of an admissible convergent contour, including actual integrability. -/
def MeijerGConvergesLog (P : MeijerGParameters) (w : ℂ) : Prop := ∃ v,MeijerGHasValueLog P w v

/-- Meijer G on the logarithmic plane. Its totalized fallback is never used as convergence evidence. -/
@[dlmf 16.17.E1]
def meijerGLog (P : MeijerGParameters) (w : ℂ) : ℂ := by
  classical
  exact if h : ∃ v,MeijerGHasValueLog P w v then Classical.choose h else 0

/-- Principal nonzero-plane Meijer G, with log(-) branch differences kept explicit in identities. -/
def meijerG (P : MeijerGParameters) (z : ℂ) : ℂ := meijerGLog P (Complex.log z)

/-- 16.17: meijerG contour exists. -/
@[dlmf 16.17]
theorem meijerG_contour_exists (P : MeijerGParameters) (hP : P.Valid) (kind : MeijerContourKind) :
    ∃ L : MeijerGContour,L.kind=kind ∧ L.Admissible P := by
  sorry

/-- All three geometric contour classes converge in the exact sufficient regions stated by DLMF. -/
@[dlmf 16.17]
theorem meijerG_contour_integrable {P : MeijerGParameters} {L : MeijerGContour} {w : ℂ}
    (hL : L.Admissible P) (hw : meijerGContourRegion P L.kind w) :
    Integrable (fun t : ℝ => deriv L.path t*meijerGKernelLog P w (L.path t)) := by
  sorry

/-- Whenever more than one contour class applies, the values agree. -/
@[dlmf 16.17]
theorem meijerG_contour_independent {P : MeijerGParameters} {w v v' : ℂ}
    (h : MeijerGHasValueLog P w v) (h' : MeijerGHasValueLog P w v') : v=v' := by
  sorry

/-- 16.17: meijerG converges of region. -/
@[dlmf 16.17]
theorem meijerG_converges_of_region {P : MeijerGParameters} (hP : P.Valid) (kind : MeijerContourKind)
    {w : ℂ} (hw : meijerGContourRegion P kind w) : MeijerGConvergesLog P w := by
  sorry

/-- 16.17: meijerGLog has value. -/
@[dlmf 16.17]
theorem meijerGLog_has_value {P : MeijerGParameters} {w : ℂ} (h : MeijerGConvergesLog P w) :
    MeijerGHasValueLog P w (meijerGLog P w) := by
  unfold meijerGLog
  split_ifs with h'
  · exact Classical.choose_spec h'
  · exact False.elim (h' h)

/-- 16.17: meijerGLog eq of value. -/
@[dlmf 16.17]
theorem meijerGLog_eq_of_value {P : MeijerGParameters} {w v : ℂ} (h : MeijerGHasValueLog P w v) : meijerGLog P w=v := by
  sorry

/-- 16.17: meijerGLog analytic. -/
@[dlmf 16.17]
theorem meijerGLog_analytic (P : MeijerGParameters) (hP : P.Valid) :
    AnalyticOnNhd ℂ (meijerGLog P) {w | MeijerGConvergesLog P w} := by
  sorry

/-- Bottom-pole collisions remain meaningful in the contour definition; finite multiplicity collisions are not discarded. -/
@[dlmf 16.17]
theorem meijerGLog_parameter_continuous {A B : ℝ→List ℂ} {P : MeijerGParameters} {w : ℂ}
    (hA : A 0=P.a) (hB : B 0=P.b)
    (hparam : ∃ r>0,∃ a b : ℝ→ℕ→ℂ,
      (∀ t : ℝ,|t|<r→A t=List.ofFn (fun i : Fin P.p => a t i)) ∧
      (∀ t : ℝ,|t|<r→B t=List.ofFn (fun i : Fin P.q => b t i)) ∧
      (∀ i : Fin P.p,ContinuousAt (fun t => a t i) 0) ∧
      (∀ i : Fin P.q,ContinuousAt (fun t => b t i) 0))
    (hP : P.Valid) (hw : MeijerGConvergesLog P w) :
    Tendsto (fun t : ℝ => meijerGLog {P with a:=A t,b:=B t} w) (𝓝 0) (𝓝 (meijerGLog P w)) := by
  sorry


end DLMF.Hypergeometric
