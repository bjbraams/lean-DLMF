/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Zeros
public import DLMF.ParabolicCylinder.Uniform
public import DLMF.ParabolicCylinder.RealZeros

/-!
# Turning-point expansions and large-parameter zeros of parabolic cylinder functions

This file treats the parameter scaling of Weber's equation (DLMF 12.10.1–12.10.2), uniform
Airy-type expansions near the turning points (DLMF 12.10.35–12.10.38), and the asymptotic
expansions of the real zeros for large parameter (DLMF 12.11.4–12.11.9).

## Main definitions

* `pcfAiryEnvelope`: absolute Airy envelopes, which give uniform error bounds through zeros.
* `HasCylinderAiryExpansion`: a uniform Airy-type cylinder expansion on a real set.
* `pcfDescendingZero`: the real zeros counted in descending order.
* `pcfZeroP1`: the first correction in the turning-point zero expansion (DLMF 12.11.6).
* `pcfFirstZeroCoeff`: the exact coefficients of DLMF 12.11.9.

## Main results

* `pcf_parameter_scaling`: the scaled form of Weber's equation (DLMF 12.10.1–12.10.2).
* `pcf_airy_uniform`: uniform Airy-type expansions (DLMF 12.10.35–12.10.38).
* `pcfZeroP1_limit`: the removable limit defining `pcfZeroP1` (DLMF 12.11.6).
* `pcf_real_zero_expansion_4`, `pcf_real_zero_expansion_7`: the zero expansions
  DLMF 12.11.4–12.11.5 and 12.11.7–12.11.8.
* `pcfFirstZero_expansion`, `pcfFirstZero_coefficients`: the expansion of the largest zero
  and the structure of its coefficients (DLMF 12.11.9).

## Implementation notes

The removable limit 12.11.6 at `ζ = 0` is obtained by rationalizing `p₁` with the relation
`(t² - 1) = d² ζ` of the turning-point coordinate and inserting the Taylor polynomial of the
inverse coordinate (DLMF 12.10.41); the rationalized numerator vanishes to fifth order.
The coefficients of DLMF 12.11.9 are given exactly rather than by the rounded decimals of the
source; their decimal values are out of scope.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
open DLMF.Core

namespace DLMF.Confluent

open DLMF.Airy

/-- Second derivative of a linear rescaling: `(f(c t))'' = c² f''(c t)`. -/
theorem iteratedDeriv_two_comp_const_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf2 : Differentiable ℂ (deriv f)) (c t : ℂ) :
    iteratedDeriv 2 (fun t => f (c*t)) t = c^2 * iteratedDeriv 2 f (c*t) := by
  have hl : ∀ w : ℂ, HasDerivAt (fun w : ℂ => c*w) c w := fun w =>
    ((hasDerivAt_id w).const_mul c).congr_deriv (mul_one c)
  have d1 : deriv (fun t => f (c*t)) = fun t => deriv f (c*t) * c := by
    funext w; exact ((hf _).hasDerivAt.comp w (hl w)).deriv
  have d2 : deriv (fun t => deriv f (c*t) * c) t = deriv (deriv f) (c*t) * c * c :=
    (((hf2 _).hasDerivAt.comp t (hl t)).mul_const c).deriv
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ,
    iteratedDeriv_one, d1, d2]
  ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv 2 (fun t : ℂ => f
(μ*t*Real.sqrt 2)) t=(μ:ℂ)^4*(t^2+s)*f (μ*t*Real.sqrt 2)`. -/
@[dlmf 12.10.E1, dlmf 12.10.E2]
theorem pcf_parameter_scaling (μ : ℝ) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf2 : Differentiable ℂ (deriv f)) (s : ℂ)
    (hode : ∀ z, iteratedDeriv 2 f z-(z^2/4+s*μ^2/2)*f z=0) (t : ℂ) :
    iteratedDeriv 2 (fun t : ℂ => f (μ*t*Real.sqrt 2)) t=(μ:ℂ)^4*(t^2+s)*f (μ*t*Real.sqrt 2) := by
  have hs2 : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have e : (fun t : ℂ => f (μ*t*Real.sqrt 2)) = fun t => f ((μ*Real.sqrt 2)*t) := by
    funext t; ring_nf
  rw [e, iteratedDeriv_two_comp_const_mul hf hf2, show (μ:ℂ)*t*Real.sqrt 2 =
      (μ*Real.sqrt 2)*t by ring]
  have h := hode ((μ*Real.sqrt 2)*t)
  linear_combination (μ*Real.sqrt 2:ℂ)^2 * h + (μ:ℂ)^4 * f ((μ*Real.sqrt 2)*t) *
    (((Real.sqrt 2:ℂ)^2+2)*t^2/4 + s/2) * hs2

/-- Absolute Airy envelopes allow uniform error bounds through zeros. -/
def pcfAiryEnvelope (A D : ℂ → ℂ) (isDeriv : Bool) (μ t : ℝ) : ℝ :=
  let u : ℂ := ((μ^(4/3:ℝ):ℝ):ℂ)*pcfZeta t; if isDeriv then μ^(-4/3:ℝ)*‖A u‖+‖D u‖ else
      ‖A u‖+μ^(-8/3:ℝ)*‖D u‖

/-- A uniform Airy-type cylinder expansion on the indicated real set, with both coefficient series
and the derivative scaling controlled at every truncation order. -/
def HasCylinderAiryExpansion (F : ℝ → ℝ → ℂ) (A D : ℂ → ℂ) (isDeriv : Bool) (S : Set ℝ) : Prop :=
  ∀ N : ℕ, (fun p : ℝ × ℝ => let μ:=p.1; let t:=p.2; let ζ:=pcfZeta t;
      let u : ℂ:=((μ^(4/3:ℝ):ℝ):ℂ)*ζ;
      F μ t-(if isDeriv then
      A u/(μ:ℂ)^(4/3:ℂ)*(∑ s ∈ Finset.range N, pcfAiryC s ζ/(μ:ℂ)^(4*s))+D
      u*(∑ s ∈ Finset.range N, pcfAiryD s ζ/(μ:ℂ)^(4*s)) else
      A u*(∑ s ∈ Finset.range N, pcfAiryA s ζ/(μ:ℂ)^(4*s))+D
      u/(μ:ℂ)^(8/3:ℂ)*(∑ s ∈ Finset.range N, pcfAiryB s ζ/(μ:ℂ)^(4*s)))) =O[pcfUniformFilter S]
      (fun p : ℝ × ℝ => p.1^(-(4*N:ℝ))*pcfAiryEnvelope A D isDeriv p.1 p.2)

/-- A cylinder normalizer gives uniform Airy-type expansions of U and its derivative through the
turning point, for `t ≥ -1+δ`. -/
@[dlmf 12.10.E35, dlmf 12.10.E36, dlmf 12.10.E37, dlmf 12.10.E38]
theorem pcf_airy_uniform  :
    ∃ g : ℝ → ℂ, IsCylinderGNormalizer g ∧ ∀ δ : ℝ, 0 < δ → δ < 2 →
        HasCylinderAiryExpansion
        (fun μ t => parabolicCylinderU (-μ^2/2)
        (μ*t*Real.sqrt 2)/(2*Real.sqrt π*(μ:ℂ)^(1/3:ℂ)*g μ*pcfPhi (pcfZeta t))) airyAi airyAiDeriv
        false (Ici (-1+δ)) ∧
        HasCylinderAiryExpansion
        (fun μ t => parabolicCylinderUDeriv (-μ^2/2)
        (μ*t*Real.sqrt 2)/(Real.sqrt (2*π)*(μ:ℂ)^(2/3:ℂ)*g μ/pcfPhi (pcfZeta t))) airyAi airyAiDeriv
        true (Ici (-1+δ)) ∧ HasCylinderAiryExpansion
        (fun μ t => parabolicCylinderV (-μ^2/2)
        (μ*t*Real.sqrt 2)/(2*Real.sqrt π*(μ:ℂ)^(1/3:ℂ)*g μ*pcfPhi (pcfZeta t) /Gamma (1/2+μ^2/2)))
        airyBi airyBiDeriv false (Ici (-1+δ)) ∧
        HasCylinderAiryExpansion
        (fun μ t => parabolicCylinderVDeriv (-μ^2/2)
        (μ*t*Real.sqrt 2)/(Real.sqrt (2*π)*(μ:ℂ)^(2/3:ℂ)*g μ/pcfPhi (pcfZeta t) /Gamma (1/2+μ^2/2)))
        airyBi airyBiDeriv true (Ici (-1+δ)) := by
  sorry

/-- Real zero counted in descending order; existence and finiteness are separate assertions. -/
def pcfDescendingZero (a : ℝ) (isDeriv : Bool) (s : ℕ) : ℝ :=
  Classical.epsilon (fun x : ℝ =>
      let F : ℝ → ℂ:=if isDeriv then fun x => parabolicCylinderUDeriv a x
        else fun x => parabolicCylinderU a x
      F x=0 ∧
      ({y : ℝ | x < y ∧ F y=0}:Set ℝ).ncard=s-1)

set_option maxHeartbeats 800000 in
/-- The stated relation follows from the given hypotheses: `∀ᶠ μ : ℝ in atTop, let x`. -/
theorem pcfDescendingZero_eventually (s : ℕ) (hs : 0 < s) (isDeriv : Bool) :
    ∀ᶠ μ : ℝ in atTop, let x:=pcfDescendingZero (-μ^2/2) isDeriv s;
        let F : ℝ → ℂ:=if isDeriv then fun x => parabolicCylinderUDeriv (-μ^2/2) x
          else fun x => parabolicCylinderU (-μ^2/2) x
        F x=0 ∧ Set.Finite {y : ℝ | x < y ∧ F y=0} ∧ ({y : ℝ | x < y ∧ F y=0}:Set ℝ).ncard=s-1 := by
  have hmany : ∀ᶠ μ : ℝ in atTop, ∃ z : Fin s → ℝ, StrictMono z ∧
      (∀ j, 0 < z j) ∧ ∀ j,
        (if isDeriv then parabolicCylinderUDeriv ((-μ^2/2:ℝ):ℂ) (z j)
          else parabolicCylinderU ((-μ^2/2:ℝ):ℂ) (z j)) = 0 := by
    cases isDeriv
    · exact CylinderRealZeros.eventually_strictMono_positive_zeros s
    · exact CylinderRealZeros.eventually_strictMono_positive_derivative_zeros s
  filter_upwards [hmany] with μ hμ
  let F : ℝ → ℂ := if isDeriv then fun x => parabolicCylinderUDeriv ((-μ^2/2:ℝ):ℂ) x
    else fun x => parabolicCylinderU ((-μ^2/2:ℝ):ℂ) x
  have hfin : {x : ℝ | 0 < x ∧ F x = 0}.Finite := by
    cases isDeriv
    · exact CylinderRealZeros.finite_zeros_Ioi (-μ^2/2) 0
    · exact CylinderRealZeros.finite_derivative_zeros_Ioi (-μ^2/2) 0
  let f := hfin.toFinset
  let e := f.orderEmbOfFin rfl
  have he : ∀ j, 0 < e j ∧ F (e j) = 0 := by
    intro j
    exact hfin.mem_toFinset.mp (f.orderEmbOfFin_mem rfl j)
  have hcard : s ≤ f.card := by
    obtain ⟨z, hz, hzpos, hz0⟩ := hμ
    have hmem : ∀ j, z j ∈ f := by
      intro j
      refine hfin.mem_toFinset.mpr ⟨hzpos j, ?_⟩
      simpa only [F, ite_apply] using hz0 j
    have h := Finset.card_le_card_of_injOn z (s := Finset.univ)
      (fun j _ => hmem j) hz.injective.injOn
    simpa using h
  let i : Fin f.card := ⟨f.card-s, by omega⟩
  have hset : {y : ℝ | e i < y ∧ F y = 0} = e '' Set.Ioi i := by
    ext y
    constructor
    · intro hy
      have hyf : y ∈ f := hfin.mem_toFinset.mpr ⟨(he i).1.trans hy.1, hy.2⟩
      have hyr : y ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin]
        exact hyf
      obtain ⟨j, rfl⟩ := hyr
      exact ⟨j, e.lt_iff_lt.mp hy.1, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨e.strictMono hj, (he j).2⟩
  have htcard : ({y : ℝ | e i < y ∧ F y = 0} : Set ℝ).ncard = s-1 := by
    rw [hset, Set.ncard_image_of_injective _ e.injective]
    rw [← Finset.coe_Ioi, Set.ncard_coe_finset, Fin.card_Ioi]
    dsimp [i]
    omega
  have hex : ∃ x : ℝ, F x = 0 ∧ ({y : ℝ | x < y ∧ F y=0} : Set ℝ).ncard=s-1 :=
    ⟨e i, (he i).2, htcard⟩
  have hchosen := Classical.epsilon_spec hex
  have htopfin : Set.Finite {y : ℝ | pcfDescendingZero (-μ^2/2) isDeriv s < y ∧ F y=0} := by
    cases isDeriv
    · exact CylinderRealZeros.finite_zeros_Ioi (-μ^2/2) (pcfDescendingZero (-μ^2/2) false s)
    · exact CylinderRealZeros.finite_derivative_zeros_Ioi (-μ^2/2)
          (pcfDescendingZero (-μ^2/2) true s)
  have hparam : -(μ:ℂ)^2/2 = ((-μ^2/2:ℝ):ℂ) := by push_cast; ring
  dsimp only
  rw [hparam]
  exact ⟨hchosen.1, htopfin, hchosen.2⟩

/-- The first correction in the cylinder turning-point zero expansion, defined by its removable
limit in the uniform zeta coordinate. -/
@[dlmf 12.11.E6]
def pcfZeroP1 (ζ : ℝ) : ℝ :=
  limUnder (𝓝[≠] ζ) (fun u : ℝ => let t:=pcfInverseZeta u;
      (t^3-6*t)/(24*(t^2-1)^2)+5/(48*Real.sqrt ((t^2-1)*u^3)))

namespace TurningPointCorrection

/-- The correctionNumerator `25(t²-1)³ - 8w³(t³-6t)²` of the rationalized correction `p₁`. -/
private noncomputable def correctionNumerator (t w : ℝ) : ℝ :=
  25 * (t ^ 2 - 1) ^ 3 - 8 * w ^ 3 * (t ^ 3 - 6 * t) ^ 2

/-- The Taylor polynomial of the inverse coordinate in `w = 2^{-1/3} ζ` (DLMF 12.10.41). -/
private noncomputable def inverseTaylorPoly (w : ℝ) : ℝ :=
  1 + w - w^2/10 + 11*w^3/350 - 823*w^4/63000 + 150653*w^5/24255000

/-- The correctionQuotient of the correctionNumerator at the Taylor polynomial by `w⁵`. -/
private noncomputable def correctionQuotient (w : ℝ) : ℝ :=
    (1728/7) + (3712/21)*w^1 + (-1002112/13475)*w^2 + (-2161107/134750)*w^3 +
    (228666223/63669375)*w^4 + (555213691/463050000)*w^5 + (588111225613/490254187500)*w^6 +
    (-341688638033593/264737261250000)*w^7 + (22429632839239/137271172500000)*w^8 +
    (-164667500237771/5147668968750000)*w^9 + (610956284314975603/47564461271250000000)*w^10 +
    (26945363170789489/26755009465078125000)*w^11 +
    (-231636322447721917841/34246412115300000000000)*w^12 +
    (1644767009696853737161/599312212017750000000000)*w^13 +
    (-363236069299367072701/332951228898750000000000)*w^14 +
    (18352351718154466193957161/41532336292830075000000000000)*w^15 +
    (-5511477075149042700797/32962171660976250000000000)*w^16 +
    (79403079741547397095557293/1661293451713203000000000000000)*w^17 +
    (-4620947869600647806758567/330370856874784687500000000000)*w^18 +
    (7104188250656093811868377193/1794196927850259240000000000000000)*w^19 +
    (-4098520492596903262336403250289/4029467267130373876500000000000000000)*w^20 +
    (1785158828775922358496065911087/8058934534260747753000000000000000000)*w^21 +
    (-500543967190203721890332163589/10073668167825934691250000000000000000)*w^22 +
    (14585447648391149093041053615689/1410313543495630856775000000000000000000)*w^23 +
    (-6546053606780987953593189854719/3525783858739077141937500000000000000000)*w^24 +
    (251520449221824601184543709482801/904951190409696466430625000000000000000000)*w^25 +
    (-17799326581760567286877927211/400657256674895129765625000000000000000)*w^26 +
    (63868800060132355615865329739/11018074558559616068554687500000000000000)*w^27 +
    (-11691405024859197777153049235929/25451752230272713118361328125000000000000000)*w^28

/-- The difference correctionQuotient of the correctionNumerator in its first argument. -/
private noncomputable def correctionDiffQuotient (t s w : ℝ) : ℝ :=
  -8*s^5*w^3 + 25*s^5 - 8*s^4*t*w^3 + 25*s^4*t - 8*s^3*t^2*w^3 + 25*s^3*t^2 + 96*s^3*w^3
    - 75*s^3 - 8*s^2*t^3*w^3 + 25*s^2*t^3 + 96*s^2*t*w^3 - 75*s^2*t - 8*s*t^4*w^3 + 25*s*t^4
    + 96*s*t^2*w^3 - 75*s*t^2 - 288*s*w^3 + 75*s - 8*t^5*w^3 + 25*t^5 + 96*t^3*w^3 - 75*t^3
    - 288*t*w^3 + 75*t

/-- The correctionNumerator vanishes to fifth order at the Taylor polynomial. -/
private theorem correctionNumerator_inverseTaylorPoly (w : ℝ) :
    correctionNumerator (inverseTaylorPoly w) w = w ^ 5 * correctionQuotient w := by
  unfold correctionNumerator inverseTaylorPoly correctionQuotient; ring

/-- The correctionNumerator is Lipschitz in its first argument through `correctionDiffQuotient`. -/
private theorem correctionNumerator_sub (t s w : ℝ) :
    correctionNumerator t w - correctionNumerator s w = (t - s) * correctionDiffQuotient t s w := by
  unfold correctionNumerator correctionDiffQuotient; ring

/-- The correctionQuotient `(T(w) - 1)/w` of the Taylor polynomial. -/
private noncomputable def inverseTaylorQuotient (w : ℝ) : ℝ :=
  1 - w/10 + 11*w^2/350 - 823*w^3/63000 + 150653*w^4/24255000

/-- `T(w) - 1 = w Q(w)`. -/
private theorem inverseTaylorPoly_sub_one (w : ℝ) :
    inverseTaylorPoly w - 1 = w * inverseTaylorQuotient w := by
  unfold inverseTaylorPoly inverseTaylorQuotient; ring

end TurningPointCorrection

open TurningPointCorrection in
/-- The map `(fun u : ℝ => let t:=pcfInverseZeta u; (t^3-6*t)/(24*(t^2-1)^2)+5/(48*Real.sqrt
((t^2-1)*u^3)))` tends to `(𝓝 (pcfZeroP1 ζ))` along `(𝓝[≠] ζ)`. -/
@[dlmf 12.11.E6]
theorem pcfZeroP1_limit {ζ : ℝ} (hζ : -(3*π/4)^(2/3:ℝ) < ζ) :
    Tendsto (fun u : ℝ => let t:=pcfInverseZeta u;
        (t^3-6*t)/(24*(t^2-1)^2)+5/(48*Real.sqrt ((t^2-1)*u^3))) (𝓝[≠] ζ) (𝓝 (pcfZeroP1 ζ)) := by
  set f : ℝ → ℝ := fun u : ℝ => let t:=pcfInverseZeta u;
        (t^3-6*t)/(24*(t^2-1)^2)+5/(48*Real.sqrt ((t^2-1)*u^3)) with hf
  suffices h : ∃ L, Tendsto f (𝓝[≠] ζ) (𝓝 L) by
    obtain ⟨L, hL⟩ := h
    have : pcfZeroP1 ζ = L := hL.limUnder_eq
    rw [this]; exact hL
  set t : ℝ → ℝ := pcfInverseZeta with htdef
  rcases ne_or_eq ζ 0 with hz | rfl
  · -- regular point
    obtain ⟨d, hd, hdz, hder⟩ := CylinderTurningPoint.hasDerivAt_inverse hζ hz
    have hc := hder.continuousAt
    have hz2 : 0 < ζ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hz))
    have h1 : t ζ ^ 2 - 1 ≠ 0 := by
      rw [← hdz]; exact mul_ne_zero (pow_ne_zero _ hd.ne') hz
    have h2 : Real.sqrt ((t ζ ^ 2 - 1) * ζ ^ 3) ≠ 0 := by
      rw [← hdz]
      refine (Real.sqrt_pos.mpr ?_).ne'
      have : d ^ 2 * ζ * ζ ^ 3 = d ^ 2 * (ζ ^ 2) ^ 2 := by ring
      rw [this]; positivity
    have hcf : ContinuousAt f ζ := by
      show ContinuousAt (fun u => (t u ^ 3 - 6 * t u) / (24 * (t u ^ 2 - 1) ^ 2) +
        5 / (48 * Real.sqrt ((t u ^ 2 - 1) * u ^ 3))) ζ
      refine ContinuousAt.add ?_ ?_
      · exact ((hc.pow 3).sub (continuousAt_const.mul hc)).div
          (continuousAt_const.mul (((hc.pow 2).sub continuousAt_const).pow 2))
          (mul_ne_zero (by norm_num) (pow_ne_zero 2 h1))
      · exact continuousAt_const.div (continuousAt_const.mul
          (Real.continuous_sqrt.continuousAt.comp
            (((hc.pow 2).sub continuousAt_const).mul (continuousAt_id.pow 3))))
          (mul_ne_zero (by norm_num) h2)
    exact ⟨f ζ, hcf.tendsto.mono_left nhdsWithin_le_nhds⟩
  · -- the turning point
    set k : ℝ := (2:ℝ)^(-1/3:ℝ) with hk
    have hk0 : 0 < k := by positivity
    have hk3 : k ^ 3 = 1/2 := by
      rw [hk, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    obtain ⟨C, hC⟩ := pcfInverseZeta_taylor.bound
    set e : ℝ → ℝ := fun u => t u - inverseTaylorPoly (k * u) with he
    have heb : ∀ᶠ u in 𝓝 (0:ℝ), |e u| ≤ C * |u| ^ 6 := by
      filter_upwards [hC] with u hu
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow] at hu
      exact hu
    have hdiv : ∀ m : ℕ, m ≤ 5 → Tendsto (fun u => e u / u ^ m) (𝓝[≠] 0) (𝓝 0) := by
      intro m hm
      have hb : Tendsto (fun u : ℝ => C * |u| ^ (6 - m)) (𝓝[≠] 0) (𝓝 0) := by
        have := ((by fun_prop : Continuous fun u : ℝ => C * |u| ^ (6 - m)).tendsto (0:ℝ)).mono_left
          (nhdsWithin_le_nhds (s := {0}ᶜ))
        simpa [show 6 - m ≠ 0 by omega] using this
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [heb.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu hu0
      have hu0 : u ≠ 0 := hu0
      rw [Real.norm_eq_abs, abs_div, abs_pow, div_le_iff₀ (pow_pos (abs_pos.mpr hu0) _)]
      calc |e u| ≤ C * |u| ^ 6 := hu
        _ = C * |u| ^ (6 - m) * |u| ^ m := by
          rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]
    have he0 : Tendsto e (𝓝[≠] 0) (𝓝 0) := by simpa using hdiv 0 (by norm_num)
    have hT : Continuous inverseTaylorPoly := by unfold inverseTaylorPoly; fun_prop
    have hku : Tendsto (fun u : ℝ => k * u) (𝓝[≠] 0) (𝓝 0) := by
      simpa using ((by fun_prop : Continuous fun u : ℝ => k * u).tendsto (0:ℝ)).mono_left
        (nhdsWithin_le_nhds (s := {0}ᶜ))
    have htT : Tendsto (fun u => inverseTaylorPoly (k * u)) (𝓝[≠] (0:ℝ)) (𝓝 1) := by
      have := (hT.tendsto 0).comp hku
      simpa [Function.comp_def, inverseTaylorPoly] using this
    have ht1 : Tendsto t (𝓝[≠] 0) (𝓝 1) := by
      have := htT.add he0
      rw [add_zero] at this
      refine this.congr' (Eventually.of_forall fun u => ?_)
      simp [he]
    have hQ : Continuous inverseTaylorQuotient := by unfold inverseTaylorQuotient; fun_prop
    have hq1 : Tendsto (fun u => (t u - 1) / u) (𝓝[≠] 0) (𝓝 k) := by
      have h1 : Tendsto (fun u => k * inverseTaylorQuotient (k * u)) (𝓝[≠] (0:ℝ)) (𝓝 k) := by
        have := ((hQ.tendsto 0).comp hku).const_mul k
        simpa [Function.comp_def, inverseTaylorQuotient] using this
      have := h1.add (hdiv 1 (by norm_num))
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu : u ≠ 0 := hu
      have h := inverseTaylorPoly_sub_one (k * u)
      rw [pow_one, eq_div_iff hu, add_mul, div_mul_cancel₀ _ hu]
      simp only [he]
      linear_combination -h
    have hq : Tendsto (fun u => (t u ^ 2 - 1) / u) (𝓝[≠] 0) (𝓝 (2 * k)) := by
      have := hq1.mul (ht1.add_const 1)
      rw [show k * (1 + 1) = 2 * k by ring] at this
      refine this.congr' (Eventually.of_forall fun u => ?_)
      simp only
      ring
    have hsq := (Real.continuous_sqrt.tendsto _).comp hq
    have hX : Tendsto (fun u => t u ^ 3 - 6 * t u) (𝓝[≠] 0) (𝓝 (-5)) := by
      have := (ht1.pow 3).sub (ht1.const_mul 6)
      norm_num at this
      exact this
    have hP : Continuous correctionQuotient := by unfold correctionQuotient; fun_prop
    have hRc : Continuous (fun p : ℝ × ℝ × ℝ => correctionDiffQuotient p.1 p.2.1 p.2.2) := by
      unfold correctionDiffQuotient; fun_prop
    have hR := (hRc.tendsto (1, 1, 0)).comp (ht1.prodMk_nhds (htT.prodMk_nhds hku))
    have hPt := ((hP.tendsto 0).comp hku).const_mul (k ^ 5)
    have hN : Tendsto (fun u => correctionNumerator (t u) (k * u) / u ^ 5) (𝓝[≠] 0)
        (𝓝 (k ^ 5 * correctionQuotient 0 + 0 * correctionDiffQuotient 1 1 0)) := by
      refine (hPt.add ((hdiv 5 le_rfl).mul hR)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu : u ≠ 0 := hu
      have h1 := correctionNumerator_sub (t u) (inverseTaylorPoly (k * u)) (k * u)
      rw [correctionNumerator_inverseTaylorPoly] at h1
      simp only [Function.comp_apply, he]
      field_simp
      linear_combination -h1
    set m : ℝ := Real.sqrt (2 * k) with hm
    have hm0 : 0 < m := Real.sqrt_pos.mpr (by positivity)
    have hden : Tendsto (fun u => 48 * Real.sqrt ((t u ^ 2 - 1) / u) ^ 4 *
        (5 * Real.sqrt ((t u ^ 2 - 1) / u) ^ 3 - 2 * (t u ^ 3 - 6 * t u))) (𝓝[≠] 0)
        (𝓝 (48 * m ^ 4 * (5 * m ^ 3 - 2 * (-5)))) :=
      ((hsq.pow 4).const_mul 48).mul (((hsq.pow 3).const_mul 5).sub (hX.const_mul 2))
    have hdne : 48 * m ^ 4 * (5 * m ^ 3 - 2 * (-5)) ≠ 0 := by
      have : 0 < 5 * m ^ 3 - 2 * (-5) := by have := pow_pos hm0 3; linarith
      exact mul_ne_zero (by positivity) this.ne'
    refine ⟨_, (hN.div hden hdne).congr' ?_⟩
    -- the algebraic identity
    have hnb : -(3*π/4)^(2/3:ℝ) < (0:ℝ) := by
      have : 0 < (3*π/4)^(2/3:ℝ) := by positivity
      linarith
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hnb),
      ht1.eventually (Ioo_mem_nhds (show (0:ℝ) < 1 by norm_num) (show (1:ℝ) < 2 by norm_num))]
      with u hu hu1 htu
    have hu : u ≠ 0 := hu
    have hu1 : -(3*π/4)^(2/3:ℝ) < u := hu1
    obtain ⟨d, hd, hdz, -⟩ := CylinderTurningPoint.hasDerivAt_inverse hu1 hu
    have hsqd : Real.sqrt ((t u ^ 2 - 1) / u) = d := by
      rw [← hdz, mul_div_assoc, div_self hu, mul_one, Real.sqrt_sq hd.le]
    have hsq3 : Real.sqrt ((t u ^ 2 - 1) * u ^ 3) = d * u ^ 2 := by
      rw [← hdz, show d ^ 2 * u * u ^ 3 = (d * u ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    have hX0 : t u ^ 3 - 6 * t u < 0 := by
      obtain ⟨h0, h2⟩ := htu
      nlinarith
    have hNd : correctionNumerator (t u) (k * u) =
        25 * (d ^ 2 * u) ^ 3 - 4 * u ^ 3 * (t u ^ 3 - 6 * t u) ^ 2 := by
      unfold correctionNumerator; rw [← hdz]
      linear_combination (-8 * u ^ 3 * (t u ^ 3 - 6 * t u) ^ 2) * hk3
    show (correctionNumerator (t u) (k * u) / u ^ 5) / (48 * Real.sqrt ((t u ^ 2 - 1) / u) ^ 4 *
        (5 * Real.sqrt ((t u ^ 2 - 1) / u) ^ 3 - 2 * (t u ^ 3 - 6 * t u))) =
      (t u ^ 3 - 6 * t u) / (24 * (t u ^ 2 - 1) ^ 2) + 5 / (48 * Real.sqrt ((t u ^ 2 - 1) * u ^ 3))
    rw [hsqd, hsq3, hNd, ← hdz]
    have h5 : 5 * d ^ 3 - 2 * (t u ^ 3 - 6 * t u) ≠ 0 := by
      have : 0 < d ^ 3 := by positivity
      linarith
    generalize t u ^ 3 - 6 * t u = X at h5 ⊢
    have hnum : 25 * (d ^ 2 * u) ^ 3 - 4 * u ^ 3 * X ^ 2 =
        (5 * d ^ 3 - 2 * X) * (u ^ 3 * (5 * d ^ 3 + 2 * X)) := by ring
    rw [hnum, div_div, show u ^ 5 * (48 * d ^ 4 * (5 * d ^ 3 - 2 * X)) =
      (5 * d ^ 3 - 2 * X) * (u ^ 5 * (48 * d ^ 4)) by ring, mul_div_mul_left _ _ h5]
    field_simp
    ring

/-- Asymptotic bound with the indicated comparison function: `∃ p : ℕ → ℝ → ℝ, p 0=pcfInverseZeta
∧ p 1=pcfZeroP1 ∧ ∀ s : ℕ, 0 < s → ∀ N : ℕ, (fun μ : ℝ => pcfDescendingZero (-μ^2/2) false
s/(Real.sqrt 2*μ)-∑ j ∈ Finset.range N, p j (μ^(-4/3:ℝ)*airyAiZero s)/(μ^(4*j))) =O[atTop]
(fun μ : ℝ => μ^(-(4*N:ℝ)))`. -/
@[dlmf 12.11.E4, dlmf 12.11.E5]
theorem pcf_real_zero_expansion_4  :
    ∃ p : ℕ → ℝ → ℝ, p 0=pcfInverseZeta ∧ p 1=pcfZeroP1 ∧ ∀ s : ℕ, 0 < s → ∀ N : ℕ,
        (fun μ : ℝ => pcfDescendingZero (-μ^2/2) false s/(Real.sqrt 2*μ)-∑ j ∈ Finset.range N,
        p j (μ^(-4/3:ℝ)*airyAiZero s)/(μ^(4*j))) =O[atTop] (fun μ : ℝ => μ^(-(4*N:ℝ))) := by
  sorry

/-- Asymptotic bound with the indicated comparison function: `∃ p : ℕ → ℝ → ℝ, p 0=pcfInverseZeta
∧ ∀ s : ℕ, 0 < s → ∀ N : ℕ, (fun μ : ℝ => pcfDescendingZero (-μ^2/2) true s/(Real.sqrt 2*μ)-∑
j ∈ Finset.range N, p j (μ^(-4/3:ℝ)*airyAiDerivZero s)/(μ^(4*j))) =O[atTop] (fun μ : ℝ =>
μ^(-(4*N:ℝ)))`. -/
@[dlmf 12.11.E7, dlmf 12.11.E8]
theorem pcf_real_zero_expansion_7  :
    ∃ p : ℕ → ℝ → ℝ, p 0=pcfInverseZeta ∧ ∀ s : ℕ, 0 < s → ∀ N : ℕ,
        (fun μ : ℝ => pcfDescendingZero (-μ^2/2) true s/(Real.sqrt 2*μ)-∑ j ∈ Finset.range N,
        p j (μ^(-4/3:ℝ)*airyAiDerivZero s)/(μ^(4*j))) =O[atTop] (fun μ : ℝ => μ^(-(4*N:ℝ))) := by
  sorry

/-- Exact coefficients, rather than rounded decimals treated as exact asymptotic constants. -/
@[dlmf 12.11.E9]
def pcfFirstZeroCoeff (k : ℕ) : ℂ :=
  asymptoticCoeff (fun v : ℝ =>
      ((pcfDescendingZero (-v^3/2) false 1/(Real.sqrt 2*v^(3/2:ℝ)):ℝ):ℂ)) (2*k)

/-- Asymptotic bound with the indicated comparison function: `(fun μ : ℝ => (pcfDescendingZero
(-μ^2/2) false 1/(Real.sqrt 2*μ):ℂ)-∑ j ∈ Finset.range N, pcfFirstZeroCoeff
j*(μ:ℂ)^(-4*(j:ℂ)/3)) =O[atTop] (fun μ : ℝ => μ^(-4*(N:ℝ)/3))`. -/
@[dlmf 12.11.E9]
theorem pcfFirstZero_expansion (N : ℕ) :
    (fun μ : ℝ => (pcfDescendingZero (-μ^2/2) false 1/(Real.sqrt 2*μ):ℂ)-∑ j ∈ Finset.range N,
        pcfFirstZeroCoeff j*(μ:ℂ)^(-4*(j:ℂ)/3)) =O[atTop] (fun μ : ℝ => μ^(-4*(N:ℝ)/3)) := by
  sorry

/-- Structural facts about the coefficients of DLMF 12.11.9. The decimal values of the
coefficients printed there are numerical results and out of scope. -/
@[dlmf 12.11.E9]
theorem pcfFirstZero_coefficients :
    pcfFirstZeroCoeff 0 = 1 ∧ ∀ k : ℕ, (pcfFirstZeroCoeff k).im = 0 := by
  sorry

end DLMF.Confluent
