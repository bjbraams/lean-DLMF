/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.JacobiIdentities
public import DLMF.Lame.Basic
public import DLMFMathlib.Analysis.ODE.P2lSturmLiouville
public import DLMFMathlib.Analysis.ODE.P2sSturmOsc

/-!
# Lamé functions: eigenvalues, parity, normalization, orthogonality (DLMF §§29.3, 29.9)

The existence and ordering of the four spectra of Table 29.3.2 (`Real.lameEigenvalue_spec`)
and the existence and uniqueness of the normalized eigenfunctions
(`Real.lameEigenfunction_spec`) are proved from the separated Sturm–Liouville theory of
`DLMFMathlib.Analysis.ODE.P2lSturmLiouville` (Lamé's equation as `w'' = (V - h) w` with the
even potential `V = ν(ν+1)k² sn²`); the definitions of `DLMF.Lame.Basic` are by choice from
them. From these the following are proved:

* the eigenfunctions solve Lamé's equation with the boundary conditions, normalization
  29.3.18 and the sign rule of §29.3(v);
* the parities and periods of Tables 29.3.1 and 29.3.2, by uniqueness for linear ODEs
  (`ODE.eq_of_linear_ode`) and the symmetries `sn(-x) = -sn x`, `sn(2K - x) = sn x`;
* the orthogonality relations 29.3.19, by Green's identity for the Wronskian.

The zero counts of Table 29.3.2 and the interlacing 29.3.1–29.3.4 follow from Sturm's
oscillation theorem (`DLMFMathlib.Analysis.ODE.P2sSturmOsc`), applied on `[0, K]` and, for
29.3.1 and 29.3.3, to the problem on `[0, 2K]` with potential shifted by `K`. The coalescence
and sign 29.3.5–29.3.6, the duality 29.3.7–29.3.8, the continued fractions 29.3.10 and the
stability theorem of §29.9 are admitted.
-/

@[expose] public section

open Complex DLMF.JacobiElliptic DLMF.Elliptic Filter Set
open scoped Real Topology

noncomputable section

namespace DLMF.Lame

variable {h ν k : ℝ} {w : ℝ → ℝ}

/-! ### Existence theorems -/

/-- The Lamé potential `ν(ν+1) k² sn²(x, k)`. -/
def p2lPot (ν k : ℝ) (x : ℝ) : ℝ := ν * (ν + 1) * k ^ 2 * Real.jacobiSnm x (k ^ 2) ^ 2

/-- For `k² < 1` the Lamé potential `ν(ν+1) k² sn²(x, k)` is continuous in `x`. -/
theorem p2lPot_continuous (hk : k ^ 2 < 1) : Continuous (p2lPot ν k) :=
  continuous_const.mul
    ((continuous_iff_continuousAt.2 fun x => (Real.hasDerivAt_jacobiSnm hk x).continuousAt).pow 2)

/-- The Lamé potential is bounded: `|ν(ν+1) k² sn²(x, k)| ≤ |ν(ν+1)| k²`. -/
theorem p2lPot_abs_le (x : ℝ) : |p2lPot ν k x| ≤ |ν * (ν + 1)| * k ^ 2 := by
  have h1 : Real.jacobiSnm x (k ^ 2) ^ 2 ≤ 1 := by
    have := Real.jacobiSnm_sq_add_jacobiCnm_sq x (k ^ 2)
    nlinarith [sq_nonneg (Real.jacobiCnm x (k ^ 2))]
  rw [p2lPot, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.jacobiSnm x (k ^ 2))),
    abs_of_nonneg (sq_nonneg k)]
  have := abs_nonneg (ν * (ν + 1))
  have := sq_nonneg k
  calc |ν * (ν + 1)| * k ^ 2 * Real.jacobiSnm x (k ^ 2) ^ 2 ≤ |ν * (ν + 1)| * k ^ 2 * 1 := by
        gcongr
    _ = _ := mul_one _

/-- For `k² < 1` the Lamé potential is even in `x`. -/
lemma p2lPot_neg (hk : k ^ 2 < 1) (x : ℝ) : p2lPot ν k (-x) = p2lPot ν k x := by
  simp only [p2lPot, (jacobi_neg hk x).1, neg_sq]

/-- `w` solves the real Lamé equation 29.2.1 iff it solves the Hill-type equation
`w'' + (h - V(x)) w = 0` with the Lamé potential `V = p2lPot ν k`. -/
theorem p2l_isLameSolution_iff {h : ℝ} {w : ℝ → ℝ} :
    Real.IsLameSolution h ν k w ↔ ODE.P2lIsSol (p2lPot ν k) h w := by
  constructor
  · intro hw
    exact ⟨hw.differentiable, fun x => (hw.hasDerivAt_deriv x).congr_deriv (by
      simp only [p2lPot]; ring)⟩
  · intro hw
    exact ⟨hw.1, fun x => (hw.2 x).congr_deriv (by simp only [p2lPot]; ring)⟩

/-- The Lamé spectrum of boundary type `(odd0, oddK)` equals the Sturm–Liouville spectrum on
`[0, K]` of the Lamé potential with the same boundary conditions. -/
theorem p2l_lameSpectrum_eq (odd0 oddK : Bool) :
    Real.lameSpectrum ν k odd0 oddK =
      ODE.p2lSpec (p2lPot ν k) (Real.compEllIntKm (k ^ 2)) odd0 oddK := by
  ext h
  simp only [Real.lameSpectrum, Real.IsLameEigenfunction, ODE.p2lSpec, mem_ofPred_eq,
    p2l_isLameSolution_iff]
  rfl

/-- **Existence and ordering of the Lamé spectra** (DLMF §29.3(i)): for each pair `ν, k` and
each boundary type of Table 29.3.2, the eigenvalues form an infinite, unbounded, strictly
increasing sequence `h₀ < h₁ < ⋯` exhausting the spectrum, and the `j`th one is
characterized by `IsNthLameEigenvalue`. Proved by regular Sturm–Liouville theory on `[0, K]`
(`ODE.p2l_spec_Iio_finite`, `ODE.p2l_spec_not_bddAbove`, `ODE.p2l_enum`). -/
@[dlmf 29.3.i]
theorem Real.lameEigenvalue_spec (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1)
    (odd0 oddK : Bool) :
    (∀ j, ∃! h, Real.IsNthLameEigenvalue ν k odd0 oddK j h) ∧
      StrictMono (Real.lameEigenvalue ν k odd0 oddK) ∧
      Real.lameSpectrum ν k odd0 oddK = Set.range (Real.lameEigenvalue ν k odd0 oddK) ∧
      Tendsto (Real.lameEigenvalue ν k odd0 oddK) atTop atTop := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hK := Real.compEllIntKm_pos hk
  have hS := p2l_lameSpectrum_eq (ν := ν) (k := k) odd0 oddK
  have hinf : ¬BddAbove (Real.lameSpectrum ν k odd0 oddK) := hS ▸
    ODE.p2l_spec_not_bddAbove (p2lPot_continuous hk) p2lPot_abs_le (p2lPot_neg hk) hK odd0 oddK
  have hfin : ∀ c, (Real.lameSpectrum ν k odd0 oddK ∩ Iio c).Finite := fun c => hS ▸
    ODE.p2l_spec_Iio_finite (p2lPot_continuous hk) p2lPot_abs_le hK odd0 oddK c
  obtain ⟨h1, h2⟩ := ODE.p2l_enum hinf hfin
  have hj : ∀ j, ∃! h, Real.IsNthLameEigenvalue ν k odd0 oddK j h := h1
  have he : ∀ j, Real.IsNthLameEigenvalue ν k odd0 oddK j (Real.lameEigenvalue ν k odd0 oddK j) :=
    fun j => by
      rw [Real.lameEigenvalue, dite_eq_left (hj j)]
      exact (hj j).exists.choose_spec
  exact ⟨hj, h2 _ fun j => ⟨(he j).1, (he j).2.2⟩⟩

/-- The `j`th eigenvalue is the `j`th element of the spectrum. -/
theorem Real.isNthLameEigenvalue_lameEigenvalue (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1)
    (odd0 oddK : Bool) (j : ℕ) :
    Real.IsNthLameEigenvalue ν k odd0 oddK j (Real.lameEigenvalue ν k odd0 oddK j) := by
  have hs := (Real.lameEigenvalue_spec hν hk0 hk1 odd0 oddK).1 j
  rw [Real.lameEigenvalue, dite_eq_left hs]
  exact hs.exists.choose_spec

/-- Positivity of `∫₀^K dn · w²` for a nonzero solution `w`. -/
lemma p2l_integral_dn_sq_pos (hk : k ^ 2 < 1) {h : ℝ} {w : ℝ → ℝ}
    (hw : ODE.P2lIsSol (p2lPot ν k) h w) (hne : w ≠ 0) :
    0 < ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm x (k ^ 2) * w x ^ 2 := by
  have hK := Real.compEllIntKm_pos hk
  set K := Real.compEllIntKm (k ^ 2)
  set f : ℝ → ℝ := fun x => Real.jacobiDnm x (k ^ 2) * w x ^ 2
  have hdn : Continuous fun x => Real.jacobiDnm x (k ^ 2) :=
    continuous_iff_continuousAt.2 fun x => (Real.hasDerivAt_jacobiDnm hk x).continuousAt
  have hf : Continuous f := hdn.mul (hw.continuous.pow 2)
  have hf0 : ∀ x, 0 ≤ f x := fun x => mul_nonneg (Real.jacobiDnm_pos hk x).le (sq_nonneg _)
  obtain ⟨x₀, hx₀, hwx₀⟩ : ∃ x ∈ Ioo 0 K, w x ≠ 0 := by
    by_contra hno
    push Not at hno
    have hm : K / 2 ∈ Ioo 0 K := ⟨by linarith, by linarith⟩
    have hev : w =ᶠ[𝓝 (K / 2)] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds hm.1 hm.2] with x hx using hno x hx
    have hd := (hw.hasDerivAt (K / 2)).unique
      ((hasDerivAt_const (K / 2) (0 : ℝ)).congr_of_eventuallyEq hev)
    exact hne (ODE.p2l_eq_zero (p2lPot_continuous hk) hw (hno _ hm) hd)
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
    (Filter.Eventually.of_forall hf0) (hf.intervalIntegrable 0 K)]
  refine ⟨hK, ?_⟩
  have hU : IsOpen ({x | f x ≠ 0} ∩ Ioo 0 K) := (isOpen_ne_fun hf continuous_const).inter isOpen_Ioo
  have hpos := hU.measure_pos MeasureTheory.volume
    ⟨x₀, mul_ne_zero (Real.jacobiDnm_pos hk x₀).ne' (pow_ne_zero 2 hwx₀), hx₀⟩
  exact hpos.trans_le (MeasureTheory.measure_mono fun x hx => ⟨hx.1, Ioo_subset_Ioc_self hx.2⟩)

/-- **Existence and uniqueness of the normalized Lamé eigenfunctions** (DLMF §§29.3(iv)–(v)):
the eigenvalue `lameEigenvalue ν k odd0 oddK j` is simple, so there is exactly one
eigenfunction with the normalization 29.3.18 and the sign rule of §29.3(v). Every eigenfunction
is a multiple of the basic solution `ODE.p2lY` (`ODE.p2l_eq_mul_p2lY`). -/
@[dlmf 29.3.v]
theorem Real.lameEigenfunction_spec (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1)
    (odd0 oddK : Bool) (j : ℕ) :
    ∃! w, Real.IsNormalizedLameEigenfunction ν k odd0 oddK j w := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hV := p2lPot_continuous (ν := ν) hk
  set K := Real.compEllIntKm (k ^ 2)
  set h := Real.lameEigenvalue ν k odd0 oddK j
  have hmem : h ∈ ODE.p2lSpec (p2lPot ν k) K odd0 oddK :=
    p2l_lameSpectrum_eq (ν := ν) (k := k) odd0 oddK ▸
      (Real.isNthLameEigenvalue_lameEigenvalue hν hk0 hk1 odd0 oddK j).1
  obtain ⟨y0, y1, hy⟩ := ODE.p2lY_spec hV odd0 h
  set Y := ODE.p2lY (p2lPot ν k) odd0 h
  have hYne := ODE.p2lY_ne_zero hV odd0 h
  have hG := (ODE.p2l_mem_spec_iff hV odd0 oddK).1 hmem
  set I := ∫ x in (0 : ℝ)..K, Real.jacobiDnm x (k ^ 2) * Y x ^ 2
  have hI : 0 < I := p2l_integral_dn_sq_pos hk hy hYne
  -- the sign datum `a`: the normalized eigenfunction `c Y` satisfies the sign rule iff `0 < c a`
  set a := if oddK then -deriv Y K else Y K
  have ha : a ≠ 0 := by
    intro ha0
    simp only [ODE.p2lG, a] at hG ha0
    cases oddK
    · simp only [Bool.false_eq_true, ↓reduceIte] at hG ha0
      exact hYne (ODE.p2l_eq_zero hV hy ha0 hG)
    · simp only [↓reduceIte, neg_eq_zero] at hG ha0
      exact hYne (ODE.p2l_eq_zero hV hy hG ha0)
  have hderiv : ∀ c : ℝ, deriv (fun x => c * Y x) = fun x => c * deriv Y x := fun c =>
    funext fun x => ((hy.hasDerivAt x).const_mul c).deriv
  have hint : ∀ c : ℝ, ∫ x in (0 : ℝ)..K, Real.jacobiDnm x (k ^ 2) * (c * Y x) ^ 2 = c ^ 2 * I :=
    fun c => by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext x; ring
  have hsign : ∀ c : ℝ, (if oddK then deriv (fun x => c * Y x) K < 0 else 0 < c * Y K) ↔
      0 < c * a := fun c => by
    rw [hderiv]; simp only [a]; cases oddK
    · simp
    · simp only [↓reduceIte, mul_neg, neg_pos]
  -- every normalized eigenfunction is `c Y` with `c² I = π/4` and `0 < c a`
  have hform : ∀ w, Real.IsNormalizedLameEigenfunction ν k odd0 oddK j w →
      ∃ c : ℝ, w = (fun x => c * Y x) ∧ c ^ 2 * I = π / 4 ∧ 0 < c * a := by
    rintro w ⟨⟨hw, hb, -⟩, hn, hs⟩
    rw [p2l_isLameSolution_iff] at hw
    have he := ODE.p2l_eq_mul_p2lY hV hw hb.1
    set c := if odd0 then deriv w 0 else w 0
    refine ⟨c, he, ?_, ?_⟩
    · rw [← hint c, ← hn, he]
    · rw [he] at hs; exact (hsign c).1 hs
  set c₀ := Real.sqrt (π / (4 * I)) * a / |a|
  have hsq : Real.sqrt (π / (4 * I)) ^ 2 = π / (4 * I) := Real.sq_sqrt (by positivity)
  have hsqpos : 0 < Real.sqrt (π / (4 * I)) := Real.sqrt_pos.2 (by positivity)
  have haa : 0 < |a| := abs_pos.2 ha
  have hc₀ : c₀ ^ 2 * I = π / 4 := by
    simp only [c₀, div_pow, mul_pow, sq_abs, hsq]
    field_simp
  have hc₀a : 0 < c₀ * a := by
    simp only [c₀]
    rw [div_mul_eq_mul_div, mul_assoc, ← sq, ← sq_abs, sq, ← mul_assoc, mul_div_assoc,
      div_self haa.ne']
    positivity
  refine ⟨fun x => c₀ * Y x, ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, fun w hw => ?_⟩
  · rw [p2l_isLameSolution_iff]; exact hy.const_mul c₀
  · have hb := (ODE.p2l_mem_spec_iff hV odd0 oddK).2 hG
    refine ⟨?_, ?_⟩
    · rw [hderiv]; cases odd0 <;> simp_all [ODE.p2lD0, ODE.p2lD1]
    · rw [hderiv]; simp only [ODE.p2lG] at hG
      cases oddK
      · exact mul_eq_zero_of_right c₀ hG
      · exact mul_eq_zero_of_right c₀ hG
  · intro h0
    have hc0 : c₀ ≠ 0 := fun hc => by simp [hc] at hc₀a
    exact hYne (funext fun x => by
      have := congrFun h0 x; simp only [Pi.zero_apply, mul_eq_zero] at this
      exact this.resolve_left hc0)
  · exact (hint c₀).trans hc₀
  · exact (hsign c₀).2 hc₀a
  · obtain ⟨c, rfl, hc, hca⟩ := hform w hw
    have hcc : c ^ 2 = c₀ ^ 2 := by
      have := hc.trans hc₀.symm
      exact mul_right_cancel₀ hI.ne' this
    have : c = c₀ := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hcc with h' | h'
      · exact h'
      · rw [h', neg_mul] at hca; linarith
    rw [this]

/-- The normalized eigenfunction satisfies its defining properties. -/
theorem Real.isNormalizedLameEigenfunction_lameEigenfunction (hν : -1 / 2 ≤ ν) (hk0 : 0 < k)
    (hk1 : k < 1) (odd0 oddK : Bool) (j : ℕ) :
    Real.IsNormalizedLameEigenfunction ν k odd0 oddK j
      (Real.lameEigenfunction ν k odd0 oddK j) := by
  have hs := Real.lameEigenfunction_spec hν hk0 hk1 odd0 oddK j
  rw [Real.lameEigenfunction, dite_eq_left hs]
  exact hs.exists.choose_spec

/-! ### Helper lemmas: continuity, reflection, Green's identity -/

/-- For `0 < k < 1`, `k² < 1`. -/
theorem l29_sq_lt_one (hk0 : 0 < k) (hk1 : k < 1) : k ^ 2 < 1 := by nlinarith

/-- For `0 < k < 1`, the complementary modulus `k' = √(1 - k²)` again lies in `(0, 1)`, and
`k'² = 1 - k²`. -/
theorem l29_comodulus (hk0 : 0 < k) (hk1 : k < 1) :
    0 < Real.sqrt (1 - k ^ 2) ∧ Real.sqrt (1 - k ^ 2) < 1 ∧
      Real.sqrt (1 - k ^ 2) ^ 2 = 1 - k ^ 2 := by
  have h1 : 0 < 1 - k ^ 2 := by nlinarith
  refine ⟨Real.sqrt_pos.2 h1, ?_, Real.sq_sqrt h1.le⟩
  rw [Real.sqrt_lt' one_pos]; nlinarith

/-- For `k² < 1`, `x ↦ sn(x, k)` is continuous on `ℝ`. -/
theorem l29_continuous_sn (hk : k ^ 2 < 1) : Continuous fun x => Real.jacobiSnm x (k ^ 2) :=
  continuous_iff_continuousAt.2 fun x => (Real.hasDerivAt_jacobiSnm hk x).continuousAt

/-- `sn²` is even. -/
lemma l29_sn_sq_neg (hk : k ^ 2 < 1) (x : ℝ) :
    Real.jacobiSnm (2 * 0 - x) (k ^ 2) ^ 2 = Real.jacobiSnm x (k ^ 2) ^ 2 := by
  rw [show 2 * (0 : ℝ) - x = -x by ring, (jacobi_neg hk x).1, neg_sq]

/-- `sn²(2K - x) = sn²(x)`. -/
lemma l29_sn_sq_reflect_K (hk : k ^ 2 < 1) (x : ℝ) :
    Real.jacobiSnm (2 * Real.compEllIntKm (k ^ 2) - x) (k ^ 2) ^ 2 =
      Real.jacobiSnm x (k ^ 2) ^ 2 := by
  rw [show 2 * Real.compEllIntKm (k ^ 2) - x = -x + 2 * Real.compEllIntKm (k ^ 2) by ring,
    (Real.jacobi_add_two_compEllIntKm hk (-x)).1, (jacobi_neg hk x).1, neg_neg]

/-- **Reflection principle** for Lamé's equation: if `sn²` is symmetric about `c`, a solution
with `w'(c) = 0` is even about `c` and one with `w(c) = 0` is odd about `c`. -/
lemma l29_reflect {c : ℝ} (hk : k ^ 2 < 1) (hw : Real.IsLameSolution h ν k w)
    (hsym : ∀ x, Real.jacobiSnm (2 * c - x) (k ^ 2) ^ 2 = Real.jacobiSnm x (k ^ 2) ^ 2) :
    (deriv w c = 0 → ∀ x, w (2 * c - x) = w x) ∧ (w c = 0 → ∀ x, w (2 * c - x) = -w x) := by
  set q : ℝ → ℝ := fun x => -(h - ν * (ν + 1) * k ^ 2 * Real.jacobiSnm x (k ^ 2) ^ 2) with hq_def
  have hq : Continuous q :=
    (continuous_const.sub (continuous_const.mul ((l29_continuous_sn hk).pow 2))).neg
  have hw' : ∀ x, HasDerivAt w (deriv w x) x ∧
      HasDerivAt (deriv w) ((0 : ℝ) • deriv w x + q x • w x) x := fun x =>
    ⟨(hw.differentiable x).hasDerivAt, by simpa [q, smul_eq_mul] using hw.hasDerivAt_deriv x⟩
  have href : ∀ s x : ℝ,
      HasDerivAt (fun y => s * w (2 * c - y)) (-(s * deriv w (2 * c - x))) x ∧
      HasDerivAt (fun y => -(s * deriv w (2 * c - y)))
        ((0 : ℝ) • (-(s * deriv w (2 * c - x))) + q x • (s * w (2 * c - x))) x := by
    intro s x
    have h1 : HasDerivAt (fun y => 2 * c - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (2 * c)
    constructor
    · exact (((hw' (2 * c - x)).1.comp x h1).const_mul s).congr_deriv (by ring)
    · have hqx : q (2 * c - x) = q x := by simp only [hq_def, hsym]
      exact ((((hw' (2 * c - x)).2.comp x h1).const_mul s).neg).congr_deriv
        (by rw [hqx]; simp only [smul_eq_mul]; ring)
  have hc : 2 * c - c = c := by ring
  constructor
  · intro h0 x
    have := ODE.eq_of_linear_ode (t₀ := c) (p := fun _ => (0 : ℝ)) (q := q) continuous_const hq
      (f := fun y => 1 * w (2 * c - y)) (f' := fun y => -(1 * deriv w (2 * c - y)))
      (g := w) (g' := deriv w) (href 1) hw' (by simp [hc]) (by simp [hc, h0])
    simpa using congrFun this.1 x
  · intro h0 x
    have := ODE.eq_of_linear_ode (t₀ := c) (p := fun _ => (0 : ℝ)) (q := q) continuous_const hq
      (f := fun y => -1 * w (2 * c - y)) (f' := fun y => -(-1 * deriv w (2 * c - y)))
      (g := w) (g' := deriv w) (href (-1)) hw' (by simp [hc, h0]) (by simp [hc])
    have hx : -1 * w (2 * c - x) = w x := congrFun this.1 x
    linarith

/-- **Green's identity** for Lamé's equation: solutions `w₁, w₂` for distinct eigenvalues
whose Wronskians vanish at `a` and `b` are orthogonal on `[a, b]` with weight `1`. -/
lemma l29_integral_mul_eq_zero {h₁ h₂ : ℝ} {w₁ w₂ : ℝ → ℝ}
    (hne : h₁ ≠ h₂) (hw₁ : Real.IsLameSolution h₁ ν k w₁) (hw₂ : Real.IsLameSolution h₂ ν k w₂)
    {a b : ℝ} (ha : deriv w₁ a * w₂ a - w₁ a * deriv w₂ a = 0)
    (hb : deriv w₁ b * w₂ b - w₁ b * deriv w₂ b = 0) :
    ∫ x in a..b, w₁ x * w₂ x = 0 := by
  have hd : ∀ x, HasDerivAt (fun y => deriv w₁ y * w₂ y - w₁ y * deriv w₂ y)
      ((h₂ - h₁) * (w₁ x * w₂ x)) x := by
    intro x
    have := ((hw₁.hasDerivAt_deriv x).mul (hw₂.differentiable x).hasDerivAt).sub
      ((hw₁.differentiable x).hasDerivAt.mul (hw₂.hasDerivAt_deriv x))
    convert this using 1; ring
  have hcont : Continuous fun x => (h₂ - h₁) * (w₁ x * w₂ x) :=
    continuous_const.mul (hw₁.differentiable.continuous.mul hw₂.differentiable.continuous)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hcont.intervalIntegrable a b)
  rw [intervalIntegral.integral_const_mul, ha, hb, sub_zero] at hint
  exact (mul_eq_zero.1 hint).resolve_left (sub_ne_zero.2 hne.symm)

/-- Two functions with the same boundary types have vanishing Wronskian at `0` and `K`. -/
lemma l29_wronskian_boundary {odd0 oddK : Bool} {w₁ w₂ : ℝ → ℝ}
    (h₁ : Real.LameBoundary k odd0 oddK w₁) (h₂ : Real.LameBoundary k odd0 oddK w₂) :
    deriv w₁ 0 * w₂ 0 - w₁ 0 * deriv w₂ 0 = 0 ∧
      deriv w₁ (Real.compEllIntKm (k ^ 2)) * w₂ (Real.compEllIntKm (k ^ 2)) -
        w₁ (Real.compEllIntKm (k ^ 2)) * deriv w₂ (Real.compEllIntKm (k ^ 2)) = 0 := by
  obtain ⟨a₁, b₁⟩ := h₁
  obtain ⟨a₂, b₂⟩ := h₂
  constructor
  · cases odd0 <;> simp_all
  · cases oddK <;> simp_all

/-! ### Basic properties of `Ec` and `Es` -/

/-- `Ec^m_ν(x, k²)` is an eigenfunction for `a^m_ν(k²)` (Table 29.3.2): it solves 29.2.1 with
`h = a^m_ν(k²)`, satisfies the boundary conditions of its type and is not identically zero. -/
@[dlmf 29.3.iv]
theorem Real.lameEck_isLameEigenfunction (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1)
    (m : ℕ) :
    Real.IsLameEigenfunction (Real.lameAk ν m k) ν k m.bodd false
      (fun x => Real.lameEck ν m x k) :=
  (Real.isNormalizedLameEigenfunction_lameEigenfunction hν hk0 hk1 _ _ _).1

/-- `Es^m_ν(x, k²)` is an eigenfunction for `b^m_ν(k²)` (Table 29.3.2). -/
@[dlmf 29.3.iv]
theorem Real.lameEsk_isLameEigenfunction (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1)
    (m : ℕ) :
    Real.IsLameEigenfunction (Real.lameBk ν m k) ν k (!m.bodd) true
      (fun x => Real.lameEsk ν m x k) :=
  (Real.isNormalizedLameEigenfunction_lameEigenfunction hν hk0 hk1 _ _ _).1

/-- Normalization 29.3.18 for `Ec^{2m}_ν` and `Ec^{2m+1}_ν`:
`∫₀^K dn(x, k) (Ec^m_ν(x, k²))² dx = π/4`. -/
@[dlmf 29.3.E18]
theorem Real.lameEck_normalization (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm x (k ^ 2) * Real.lameEck ν m x k ^ 2
      = π / 4 :=
  (Real.isNormalizedLameEigenfunction_lameEigenfunction hν hk0 hk1 _ _ _).2.1

/-- Normalization 29.3.18 for `Es^{2m+1}_ν` and `Es^{2m+2}_ν`:
`∫₀^K dn(x, k) (Es^m_ν(x, k²))² dx = π/4` (`m ≥ 1`). -/
@[dlmf 29.3.E18]
theorem Real.lameEsk_normalization (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm x (k ^ 2) * Real.lameEsk ν m x k ^ 2
      = π / 4 :=
  (Real.isNormalizedLameEigenfunction_lameEigenfunction hν hk0 hk1 _ _ _).2.1

/-- The sign rule of §29.3(v): `Ec^m_ν(K, k²) > 0`. -/
@[dlmf 29.3.v]
theorem Real.lameEck_K_pos (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    0 < Real.lameEck ν m (Real.compEllIntKm (k ^ 2)) k := by
  have := (Real.isNormalizedLameEigenfunction_lameEigenfunction hν hk0 hk1 m.bodd false
    (m / 2)).2.2
  simpa [Real.lameEck] using this

/-- The sign rule of §29.3(v): `dEs^m_ν(z, k²)/dz < 0` at `z = K`. -/
@[dlmf 29.3.v]
theorem Real.lameEsk_deriv_K_neg (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    deriv (fun x => Real.lameEsk ν m x k) (Real.compEllIntKm (k ^ 2)) < 0 := by
  have := (Real.isNormalizedLameEigenfunction_lameEigenfunction hν hk0 hk1 (!m.bodd) true
    ((m - 1) / 2)).2.2
  simpa [Real.lameEsk] using this

/-! ### Parity and periodicity (Tables 29.3.1, 29.3.2) -/

/-- Parities of a Lamé eigenfunction: with `δ = ±1` according to `w(0) = 0` or `w'(0) = 0`
and `ε = ±1` according to `w(K) = 0` or `w'(K) = 0`, `w(-x) = δ w(x)`,
`w(2K - x) = ε w(x)`, `w(-x - K) = ε w(x - K)` and `w(x + 2K) = δε w(x)`. -/
theorem Real.IsLameEigenfunction.parity {odd0 oddK : Bool} (hk0 : 0 < k) (hk1 : k < 1)
    (hw : Real.IsLameEigenfunction h ν k odd0 oddK w) (x : ℝ) :
    w (-x) = (if odd0 then -1 else 1) * w x ∧
      w (2 * Real.compEllIntKm (k ^ 2) - x) = (if oddK then -1 else 1) * w x ∧
      w (-x - Real.compEllIntKm (k ^ 2)) =
        (if oddK then -1 else 1) * w (x - Real.compEllIntKm (k ^ 2)) ∧
      w (x + 2 * Real.compEllIntKm (k ^ 2)) =
        (if odd0 then -1 else 1) * (if oddK then -1 else 1) * w x := by
  have hk := l29_sq_lt_one hk0 hk1
  obtain ⟨hsol, ⟨h0, hK⟩, -⟩ := hw
  set K := Real.compEllIntKm (k ^ 2)
  have r0 := l29_reflect (c := 0) hk hsol (l29_sn_sq_neg hk)
  have rK := l29_reflect (c := K) hk hsol (l29_sn_sq_reflect_K hk)
  have P0 : ∀ y, w (-y) = (if odd0 then -1 else 1) * w y := by
    intro y
    cases odd0
    · simpa using r0.1 (by simpa using h0) y
    · simpa using r0.2 (by simpa using h0) y
  have PK : ∀ y, w (2 * K - y) = (if oddK then -1 else 1) * w y := by
    intro y
    cases oddK
    · simpa using rK.1 (by simpa using hK) y
    · simpa using rK.2 (by simpa using hK) y
  refine ⟨P0 x, PK x, ?_, ?_⟩
  · have e1 := P0 (x + K)
    have e2 := PK (K - x)
    have e3 := P0 (K - x)
    rw [show -(x + K) = -x - K by ring] at e1
    rw [show 2 * K - (K - x) = x + K by ring] at e2
    rw [show -(K - x) = x - K by ring] at e3
    rw [e1, e2, e3]
    ring
  · have e1 := PK (-x)
    rw [show 2 * K - -x = x + 2 * K by ring, P0 x] at e1
    rw [e1]; ring

/-- `(if m is odd then -1 else 1) = (-1)^m`. -/
lemma l29_ite_bodd (m : ℕ) : (if m.bodd then (-1 : ℝ) else 1) = (-1) ^ m := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m <;>
    simp [Nat.bodd_mul, pow_succ, pow_mul]

/-- `(if m is even then -1 else 1) = (-1)^(m+1)`. -/
lemma l29_ite_not_bodd (m : ℕ) : (if (!m.bodd) then (-1 : ℝ) else 1) = (-1) ^ (m + 1) := by
  rw [← l29_ite_bodd (m + 1), Nat.bodd_succ]

/-- Table 29.3.2, `Ec^m_ν`: `Ec^m_ν(-x) = (-1)^m Ec^m_ν(x)`, `Ec^m_ν(2K - x) = Ec^m_ν(x)`,
`z ↦ Ec^m_ν(z - K)` is even, and `Ec^m_ν(x + 2K) = (-1)^m Ec^m_ν(x)`, so that `Ec^{2m}_ν` has
period `2K` and `Ec^{2m+1}_ν` period `4K`. -/
@[dlmf 29.3.T1, dlmf 29.3.T2]
theorem Real.lameEck_parity (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) (x : ℝ) :
    Real.lameEck ν m (-x) k = (-1) ^ m * Real.lameEck ν m x k ∧
      Real.lameEck ν m (2 * Real.compEllIntKm (k ^ 2) - x) k = Real.lameEck ν m x k ∧
      Real.lameEck ν m (-x - Real.compEllIntKm (k ^ 2)) k =
        Real.lameEck ν m (x - Real.compEllIntKm (k ^ 2)) k ∧
      Real.lameEck ν m (x + 2 * Real.compEllIntKm (k ^ 2)) k = (-1) ^ m * Real.lameEck ν m x k ∧
      Real.lameEck ν m (x + 4 * Real.compEllIntKm (k ^ 2)) k = Real.lameEck ν m x k := by
  have hw := Real.lameEck_isLameEigenfunction hν hk0 hk1 m
  have P := fun y => Real.IsLameEigenfunction.parity hk0 hk1 hw y
  obtain ⟨p1, p2, p3, p4⟩ := P x
  have p5 := (P (x + 2 * Real.compEllIntKm (k ^ 2))).2.2.2
  simp only [l29_ite_bodd, Bool.false_eq_true, ↓reduceIte, mul_one, one_mul] at p1 p2 p3 p4 p5
  refine ⟨p1, p2, p3, p4, ?_⟩
  rw [show x + 4 * Real.compEllIntKm (k ^ 2) =
    x + 2 * Real.compEllIntKm (k ^ 2) + 2 * Real.compEllIntKm (k ^ 2) by ring, p5, p4,
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

/-- Table 29.3.2, `Es^m_ν` (`m ≥ 1`): `Es^m_ν(-x) = (-1)^{m+1} Es^m_ν(x)`,
`Es^m_ν(2K - x) = -Es^m_ν(x)`, `z ↦ Es^m_ν(z - K)` is odd, and
`Es^m_ν(x + 2K) = (-1)^m Es^m_ν(x)`, so that `Es^{2m+2}_ν` has period `2K` and `Es^{2m+1}_ν`
period `4K`. -/
@[dlmf 29.3.T1, dlmf 29.3.T2]
theorem Real.lameEsk_parity (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) (x : ℝ) :
    Real.lameEsk ν m (-x) k = (-1) ^ (m + 1) * Real.lameEsk ν m x k ∧
      Real.lameEsk ν m (2 * Real.compEllIntKm (k ^ 2) - x) k = -Real.lameEsk ν m x k ∧
      Real.lameEsk ν m (-x - Real.compEllIntKm (k ^ 2)) k =
        -Real.lameEsk ν m (x - Real.compEllIntKm (k ^ 2)) k ∧
      Real.lameEsk ν m (x + 2 * Real.compEllIntKm (k ^ 2)) k = (-1) ^ m * Real.lameEsk ν m x k ∧
      Real.lameEsk ν m (x + 4 * Real.compEllIntKm (k ^ 2)) k = Real.lameEsk ν m x k := by
  have hw := Real.lameEsk_isLameEigenfunction hν hk0 hk1 m
  have P := fun y => Real.IsLameEigenfunction.parity hk0 hk1 hw y
  obtain ⟨p1, p2, p3, p4⟩ := P x
  have p5 := (P (x + 2 * Real.compEllIntKm (k ^ 2))).2.2.2
  have hs : (-1 : ℝ) ^ (m + 1) * -1 = (-1) ^ m := by rw [pow_succ]; ring
  simp only [l29_ite_not_bodd, ↓reduceIte, neg_one_mul, hs] at p1 p2 p3 p4 p5
  refine ⟨p1, p2, p3, p4, ?_⟩
  rw [show x + 4 * Real.compEllIntKm (k ^ 2) =
    x + 2 * Real.compEllIntKm (k ^ 2) + 2 * Real.compEllIntKm (k ^ 2) by ring, p5, p4,
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

/-! ### Zeros (Table 29.3.2) -/

/-- Sturm oscillation for the Lamé eigenfunctions: the `j`th eigenfunction of each boundary
type has exactly `j` zeros in `(0, K)`. -/
lemma p2l_eigenfunction_zeros (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1)
    (odd0 oddK : Bool) (j : ℕ) :
    {x | x ∈ Ioo 0 (Real.compEllIntKm (k ^ 2)) ∧
      Real.lameEigenfunction ν k odd0 oddK j x = 0}.encard = j := by
  have hk := l29_sq_lt_one hk0 hk1
  have hK := Real.compEllIntKm_pos hk
  obtain ⟨⟨hw, hbc, hne⟩, -, -⟩ :=
    Real.isNormalizedLameEigenfunction_lameEigenfunction hν hk0 hk1 odd0 oddK j
  have hN := Real.isNthLameEigenvalue_lameEigenvalue hν hk0 hk1 odd0 oddK j
  rw [p2l_isLameSolution_iff] at hw
  rw [ODE.p2s_oscillation_of_sol (p2lPot_continuous hk) p2lPot_abs_le hK odd0 oddK hw hbc hne,
    ← p2l_lameSpectrum_eq, ← hN.2.1.cast_ncard_eq, hN.2.2]

/-- A set of reals with extended cardinality `n` is finite with `ncard = n`. -/
lemma p2l_finite_ncard_of_encard {s : Set ℝ} {n : ℕ} (h : s.encard = n) :
    s.Finite ∧ s.ncard = n := by
  have hf : s.Finite := Set.finite_of_encard_eq_coe h
  refine ⟨hf, ?_⟩
  have := hf.cast_ncard_eq
  rw [h] at this
  exact_mod_cast this

/-- Zeros in `[0, 2K)` of a function symmetric about `K` up to a nonzero factor. -/
lemma p2l_zeros_Ico {w : ℝ → ℝ} {K : ℝ} (hK : 0 < K) {s : ℝ}
    (hsym : ∀ x, w (2 * K - x) = s * w x) {n : ℕ}
    (hA : {x | x ∈ Ioo 0 K ∧ w x = 0}.encard = n) :
    {x ∈ Ico 0 (2 * K) | w x = 0}.encard =
      2 * n + ((if w 0 = 0 then 1 else 0) + (if w K = 0 then 1 else 0) : ℕ) := by
  set ZA := {x | x ∈ Ioo 0 K ∧ w x = 0}
  have hZ : {x ∈ Ico 0 (2 * K) | w x = 0} = ({x | x = 0 ∧ w x = 0} ∪ ZA) ∪
      ({x | x = K ∧ w x = 0} ∪ (fun x => 2 * K - x) '' ZA) := by
    ext x
    simp only [mem_ofPred_eq, mem_Ico, mem_union, mem_image, ZA, mem_Ioo]
    constructor
    · rintro ⟨⟨h0, h1⟩, hx⟩
      rcases h0.eq_or_lt with h | h
      · exact Or.inl (Or.inl ⟨h.symm, hx⟩)
      rcases lt_trichotomy x K with h' | h' | h'
      · exact Or.inl (Or.inr ⟨⟨h, h'⟩, hx⟩)
      · exact Or.inr (Or.inl ⟨h', hx⟩)
      · refine Or.inr (Or.inr ⟨2 * K - x, ⟨⟨by linarith, by linarith⟩, ?_⟩, by ring⟩)
        rw [hsym, hx, mul_zero]
    · rintro ((⟨rfl, hx⟩ | ⟨⟨h0, h1⟩, hx⟩) | (⟨rfl, hx⟩ | ⟨y, ⟨⟨h0, h1⟩, hy⟩, rfl⟩))
      · exact ⟨⟨le_rfl, by linarith⟩, hx⟩
      · exact ⟨⟨h0.le, by linarith⟩, hx⟩
      · exact ⟨⟨hK.le, by linarith⟩, hx⟩
      · exact ⟨⟨by linarith, by linarith⟩, by rw [hsym, hy, mul_zero]⟩
  have hpt : ∀ a : ℝ, {x | x = a ∧ w x = 0}.encard = ((if w a = 0 then 1 else 0 : ℕ) : ℕ∞) := by
    intro a
    split_ifs with ha
    · rw [show {x | x = a ∧ w x = 0} = {a} from by
        ext x; simp only [mem_ofPred_eq, mem_singleton_iff]
        exact ⟨fun h => h.1, fun h => ⟨h, h ▸ ha⟩⟩]
      simp
    · rw [show {x | x = a ∧ w x = 0} = ∅ from by
        ext x; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        rintro rfl; exact ha]
      simp
  have himg : ((fun x => 2 * K - x) '' ZA).encard = ZA.encard :=
    Set.InjOn.encard_image fun a _ b _ hab => by simpa using hab
  rw [hZ, encard_union_eq, encard_union_eq, encard_union_eq, himg, hpt, hpt, hA]
  · push_cast; ring
  · rw [Set.disjoint_left]; rintro x ⟨rfl, -⟩ ⟨y, ⟨⟨h0, h1⟩, -⟩, hy⟩; simp at hy; linarith
  · rw [Set.disjoint_left]; rintro x ⟨rfl, -⟩ ⟨⟨h0, h1⟩, -⟩; linarith
  · rw [Set.disjoint_left]
    rintro x (⟨rfl, -⟩ | ⟨⟨h0, h1⟩, -⟩) (⟨rfl, -⟩ | ⟨y, ⟨⟨h2, h3⟩, -⟩, hy⟩)
    · linarith
    · simp at hy; linarith
    · linarith
    · simp at hy; linarith

/-- Neumann and Dirichlet eigenvalues at `K` interlace (same condition at `0`):
`N_j < D_j < N_{j+1}`. -/
lemma p2l_interlace (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (odd0 : Bool) (j : ℕ) :
    Real.lameEigenvalue ν k odd0 false j < Real.lameEigenvalue ν k odd0 true j ∧
      Real.lameEigenvalue ν k odd0 true j < Real.lameEigenvalue ν k odd0 false (j + 1) := by
  have hk := l29_sq_lt_one hk0 hk1
  have hK := Real.compEllIntKm_pos hk
  set K := Real.compEllIntKm (k ^ 2)
  set V := p2lPot ν k
  have hV : Continuous V := p2lPot_continuous hk
  have hB : ∀ x, |V x| ≤ |ν * (ν + 1)| * k ^ 2 := p2lPot_abs_le
  set Dset := {e | ODE.p2lY V odd0 e K = 0}
  set Nset := {e | deriv (ODE.p2lY V odd0 e) K = 0}
  have hD : Real.lameSpectrum ν k odd0 true = Dset := by
    rw [p2l_lameSpectrum_eq, ODE.p2s_spec_eq_dir hV]
  have hN : Real.lameSpectrum ν k odd0 false = Nset := by
    rw [p2l_lameSpectrum_eq, ODE.p2s_spec_eq_neu hV]
  have hfinD : ∀ c, (Dset ∩ Iio c).Finite := fun c => by
    rw [← hD, p2l_lameSpectrum_eq]; exact ODE.p2l_spec_Iio_finite hV hB hK odd0 true c
  have hfinN : ∀ c, (Nset ∩ Iio c).Finite := fun c => by
    rw [← hN, p2l_lameSpectrum_eq]; exact ODE.p2l_spec_Iio_finite hV hB hK odd0 false c
  have hfinDc : ∀ c, (Dset ∩ Iic c).Finite := fun c =>
    (hfinD (c + 1)).subset fun x hx => ⟨hx.1, lt_of_le_of_lt (mem_Iic.1 hx.2) (lt_add_one c)⟩
  have cnt : ∀ i, (Dset ∩ Iic (Real.lameEigenvalue ν k odd0 false i)).ncard = i := fun i => by
    have hNi := Real.isNthLameEigenvalue_lameEigenvalue hν hk0 hk1 odd0 false i
    unfold Real.IsNthLameEigenvalue at hNi
    rw [hN] at hNi
    calc (Dset ∩ Iic (Real.lameEigenvalue ν k odd0 false i)).ncard
        = ODE.p2sN V odd0 (Real.lameEigenvalue ν k odd0 false i) K :=
          (ODE.p2s_dirichlet_count hV hB hK hfinD _).symm
      _ = (Nset ∩ Iio (Real.lameEigenvalue ν k odd0 false i)).ncard :=
          ODE.p2s_neumann_count hV hB hK hfinD hfinN hNi.1
      _ = i := hNi.2.2
  have hDj := Real.isNthLameEigenvalue_lameEigenvalue hν hk0 hk1 odd0 true j
  unfold Real.IsNthLameEigenvalue at hDj
  rw [hD] at hDj
  set d := Real.lameEigenvalue ν k odd0 true j
  have hins : (insert d (Dset ∩ Iio d)).ncard = j + 1 := by
    rw [Set.ncard_insert_of_notMem (by simp) hDj.2.1, hDj.2.2]
  constructor
  · by_contra hle
    push Not at hle
    have := Set.ncard_le_ncard (s := insert d (Dset ∩ Iio d))
      (t := Dset ∩ Iic (Real.lameEigenvalue ν k odd0 false j))
      (fun x hx => by
        rcases hx with rfl | ⟨hx1, hx2⟩
        · exact ⟨hDj.1, hle⟩
        · exact ⟨hx1, le_trans (le_of_lt hx2) hle⟩) (hfinDc _)
    rw [hins, cnt] at this
    omega
  · by_contra hle
    push Not at hle
    set e := Real.lameEigenvalue ν k odd0 false (j + 1)
    rcases hle.lt_or_eq with hlt | heq
    · have := Set.ncard_le_ncard (s := Dset ∩ Iic e) (t := Dset ∩ Iio d)
        (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hlt⟩) hDj.2.1
      rw [hDj.2.2, cnt] at this
      omega
    · have hNe := (Real.isNthLameEigenvalue_lameEigenvalue hν hk0 hk1 odd0 false (j + 1)).1
      rw [hN] at hNe
      have hDe : ODE.p2lY V odd0 e K = 0 := heq ▸ hDj.1
      exact ODE.p2lY_ne_zero hV odd0 e
        (ODE.p2l_eq_zero hV (ODE.p2lY_spec hV odd0 e).2.2 hDe hNe)

/-- Zeros in `(0, 2K)` of a function symmetric about `K` up to a factor. -/
lemma p2l_zeros_Ioo_two {w : ℝ → ℝ} {K : ℝ} (hK : 0 < K) {s : ℝ}
    (hsym : ∀ x, w (2 * K - x) = s * w x) {n : ℕ}
    (hA : {x | x ∈ Ioo 0 K ∧ w x = 0}.encard = n) :
    {x | x ∈ Ioo 0 (2 * K) ∧ w x = 0}.encard =
      2 * n + ((if w K = 0 then 1 else 0 : ℕ)) := by
  set ZA := {x | x ∈ Ioo 0 K ∧ w x = 0}
  have hZ : {x | x ∈ Ioo 0 (2 * K) ∧ w x = 0} =
      ZA ∪ ({x | x = K ∧ w x = 0} ∪ (fun x => 2 * K - x) '' ZA) := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_image, ZA, mem_Ioo]
    constructor
    · rintro ⟨⟨h0, h1⟩, hx⟩
      rcases lt_trichotomy x K with h' | h' | h'
      · exact Or.inl ⟨⟨h0, h'⟩, hx⟩
      · exact Or.inr (Or.inl ⟨h', hx⟩)
      · refine Or.inr (Or.inr ⟨2 * K - x, ⟨⟨by linarith, by linarith⟩, ?_⟩, by ring⟩)
        rw [hsym, hx, mul_zero]
    · rintro (⟨⟨h0, h1⟩, hx⟩ | (⟨rfl, hx⟩ | ⟨y, ⟨⟨h0, h1⟩, hy⟩, rfl⟩))
      · exact ⟨⟨h0, by linarith⟩, hx⟩
      · exact ⟨⟨hK, by linarith⟩, hx⟩
      · exact ⟨⟨by linarith, by linarith⟩, by rw [hsym, hy, mul_zero]⟩
  have hpt : {x | x = K ∧ w x = 0}.encard = ((if w K = 0 then 1 else 0 : ℕ) : ℕ∞) := by
    split_ifs with ha
    · rw [show {x | x = K ∧ w x = 0} = {K} from by
        ext x; simp only [mem_ofPred_eq, mem_singleton_iff]
        exact ⟨fun h => h.1, fun h => ⟨h, h ▸ ha⟩⟩]
      simp
    · rw [show {x | x = K ∧ w x = 0} = ∅ from by
        ext x; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        rintro rfl; exact ha]
      simp
  have himg : ((fun x => 2 * K - x) '' ZA).encard = ZA.encard :=
    Set.InjOn.encard_image fun a _ b _ hab => by simpa using hab
  rw [hZ, encard_union_eq, encard_union_eq, himg, hpt, hA]
  · push_cast; ring
  · rw [Set.disjoint_left]; rintro x ⟨rfl, -⟩ ⟨y, ⟨⟨h0, h1⟩, -⟩, hy⟩; simp at hy; linarith
  · rw [Set.disjoint_left]
    rintro x ⟨⟨h0, h1⟩, -⟩ (⟨rfl, -⟩ | ⟨y, ⟨⟨h2, h3⟩, -⟩, hy⟩)
    · linarith
    · simp at hy; linarith

/-- Zeros of `x ↦ w(x - K)` in `(0, K)` correspond to those of `w` in `(0, K)` when
`w(-y) = s w(y)`. -/
lemma p2l_zeros_shift {w : ℝ → ℝ} {K s : ℝ} (hpar : ∀ x, w (-x) = s * w x) :
    {x | x ∈ Ioo 0 K ∧ w (x - K) = 0}.encard = {x | x ∈ Ioo 0 K ∧ w x = 0}.encard := by
  have : {x | x ∈ Ioo 0 K ∧ w (x - K) = 0} =
      (fun x => K - x) '' {x | x ∈ Ioo 0 K ∧ w x = 0} := by
    ext x
    simp only [mem_ofPred_eq, mem_image, mem_Ioo]
    constructor
    · rintro ⟨⟨h0, h1⟩, hx⟩
      refine ⟨K - x, ⟨⟨by linarith, by linarith⟩, ?_⟩, by ring⟩
      have := hpar (x - K)
      rw [neg_sub, hx, mul_zero] at this
      exact this
    · rintro ⟨y, ⟨⟨h0, h1⟩, hy⟩, rfl⟩
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      rw [show K - y - K = -y by ring, hpar, hy, mul_zero]
  rw [this]
  exact Set.InjOn.encard_image fun a _ b _ hab => by simpa using hab

/-- The Lamé equation shifted by `K`. -/
lemma p2l_isSol_shift {V : ℝ → ℝ} {h K : ℝ} {w : ℝ → ℝ} (hw : ODE.P2lIsSol V h w) :
    ODE.P2lIsSol (fun x => V (x - K)) h (fun x => w (x - K)) := by
  have hd : deriv (fun x => w (x - K)) = fun x => deriv w (x - K) :=
    funext fun x => deriv_comp_sub_const (f := w) (a := K) (x := x)
  refine ⟨fun x => ((hw.1 (x - K)).hasDerivAt.comp_sub_const x K).differentiableAt,
    fun x => ?_⟩
  rw [hd]
  exact (hw.2 (x - K)).comp_sub_const x K

/-- `w'(-K) = 0` for a function with `w(-x) = s w(x)` and `w'(K) = 0`. -/
lemma p2l_deriv_neg_eq_zero {w : ℝ → ℝ} {K s : ℝ} (hw : Differentiable ℝ w)
    (hpar : ∀ x, w (-x) = s * w x) (hK : deriv w K = 0) : deriv w (-K) = 0 := by
  have h1 : deriv (fun x => w (-x)) K = -deriv w (-K) := deriv_comp_neg w K
  rw [show (fun x => w (-x)) = fun x => s * w x from funext hpar, deriv_const_mul _ (hw K),
    hK, mul_zero] at h1
  linarith

/-- In the problem on `[0, 2K]` with potential `V(x - K)` and Neumann conditions at both ends,
`a^m_ν` is an eigenvalue with exactly `m` smaller eigenvalues. -/
lemma p2l_lameAk_shift (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    Real.lameAk ν m k ∈ ODE.p2lSpec (fun x => p2lPot ν k (x - Real.compEllIntKm (k ^ 2)))
      (2 * Real.compEllIntKm (k ^ 2)) false false ∧
    (ODE.p2lSpec (fun x => p2lPot ν k (x - Real.compEllIntKm (k ^ 2)))
      (2 * Real.compEllIntKm (k ^ 2)) false false ∩ Iio (Real.lameAk ν m k)).encard = m := by
  have hk := l29_sq_lt_one hk0 hk1
  have hK := Real.compEllIntKm_pos hk
  set K := Real.compEllIntKm (k ^ 2)
  set E := fun x => Real.lameEck ν m x k with hE
  obtain ⟨hw, hb, hne⟩ := Real.lameEck_isLameEigenfunction hν hk0 hk1 m
  rw [p2l_isLameSolution_iff] at hw
  have hpar := Real.lameEck_parity hν hk0 hk1 m
  set u := fun x => E (x - K) with hu
  have hus := p2l_isSol_shift (K := K) hw
  have hdu : ∀ x, deriv u x = deriv E (x - K) := fun x => deriv_comp_sub_const E K x
  simp only [Real.LameBoundary, Bool.false_eq_true, ↓reduceIte] at hb
  have hbc : ODE.P2lBC (2 * K) false false u := by
    simp only [ODE.P2lBC, Bool.false_eq_true, ↓reduceIte]
    rw [hdu, hdu, zero_sub, show 2 * K - K = K by ring]
    exact ⟨p2l_deriv_neg_eq_zero hw.1 (fun x => (hpar x).1) hb.2, hb.2⟩
  have hune : u ≠ 0 := fun h0 => hne (funext fun y => by
    have := congrFun h0 (y + K); simpa [u] using this)
  have hmem : Real.lameAk ν m k ∈ ODE.p2lSpec (fun x => p2lPot ν k (x - K)) (2 * K) false false :=
    ⟨u, hus, hbc, hune⟩
  refine ⟨hmem, ?_⟩
  have hosc := ODE.p2s_oscillation_of_sol (V := fun x => p2lPot ν k (x - K))
    ((p2lPot_continuous hk).comp (by fun_prop))
    (fun x => p2lPot_abs_le (x - K)) (by linarith) false false hus hbc hune
  rw [← hosc]
  have hZ := p2l_zeros_Ioo_two (w := u) hK (s := (-1) ^ m)
    (fun x => by
      simp only [u]
      rw [show 2 * K - x - K = -(x - K) by ring]; exact (hpar _).1)
    (n := m / 2) (by
      refine (p2l_zeros_shift (w := E) (K := K) (fun x => (hpar x).1)).trans ?_
      exact p2l_eigenfunction_zeros hν hk0 hk1 _ _ _)
  refine hZ.trans ?_
  simp only [u, sub_self]
  have hnz : deriv E 0 = 0 → E 0 ≠ 0 :=
    fun hd h0 => hne (ODE.p2l_eq_zero (p2lPot_continuous hk) hw h0 hd)
  have hmod := Nat.mod_two_of_bodd m
  cases hbo : m.bodd <;> rw [hbo] at hmod <;>
    simp only [hbo, Bool.false_eq_true, ↓reduceIte] at hb <;> simp at hmod
  · simp only [hnz hb.1, ↓reduceIte]
    exact_mod_cast (show 2 * (m / 2) + 0 = m by omega)
  · simp only [show E 0 = 0 from hb.1, ↓reduceIte]
    exact_mod_cast (show 2 * (m / 2) + 1 = m by omega)

/-- In the problem on `[0, 2K]` with potential `V(x - K)` and Dirichlet conditions at both ends,
`b^m_ν` (`m ≥ 1`) is an eigenvalue with exactly `m - 1` smaller eigenvalues. -/
lemma p2l_lameBk_shift (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) {m : ℕ} (hm : 1 ≤ m) :
    Real.lameBk ν m k ∈ ODE.p2lSpec (fun x => p2lPot ν k (x - Real.compEllIntKm (k ^ 2)))
      (2 * Real.compEllIntKm (k ^ 2)) true true ∧
    (ODE.p2lSpec (fun x => p2lPot ν k (x - Real.compEllIntKm (k ^ 2)))
      (2 * Real.compEllIntKm (k ^ 2)) true true ∩ Iio (Real.lameBk ν m k)).encard =
        (m - 1 : ℕ) := by
  have hk := l29_sq_lt_one hk0 hk1
  have hK := Real.compEllIntKm_pos hk
  set K := Real.compEllIntKm (k ^ 2)
  set E := fun x => Real.lameEsk ν m x k with hE
  obtain ⟨hw, hb, hne⟩ := Real.lameEsk_isLameEigenfunction hν hk0 hk1 m
  rw [p2l_isLameSolution_iff] at hw
  have hpar := Real.lameEsk_parity hν hk0 hk1 m
  set u := fun x => E (x - K) with hu
  have hus := p2l_isSol_shift (K := K) hw
  simp only [Real.LameBoundary, ↓reduceIte] at hb
  have hbc : ODE.P2lBC (2 * K) true true u := by
    simp only [ODE.P2lBC, ↓reduceIte, u]
    rw [zero_sub, show 2 * K - K = K by ring]
    refine ⟨?_, hb.2⟩
    show Real.lameEsk ν m (-K) k = 0
    rw [(hpar K).1, show Real.lameEsk ν m K k = 0 from hb.2, mul_zero]
  have hune : u ≠ 0 := fun h0 => hne (funext fun y => by
    have := congrFun h0 (y + K); simpa [u] using this)
  have hmem : Real.lameBk ν m k ∈ ODE.p2lSpec (fun x => p2lPot ν k (x - K)) (2 * K) true true :=
    ⟨u, hus, hbc, hune⟩
  refine ⟨hmem, ?_⟩
  have hosc := ODE.p2s_oscillation_of_sol (V := fun x => p2lPot ν k (x - K))
    ((p2lPot_continuous hk).comp (by fun_prop))
    (fun x => p2lPot_abs_le (x - K)) (by linarith) true true hus hbc hune
  rw [← hosc]
  have hZ := p2l_zeros_Ioo_two (w := u) hK (s := (-1) ^ (m + 1))
    (fun x => by
      simp only [u]
      rw [show 2 * K - x - K = -(x - K) by ring]; exact (hpar _).1)
    (n := (m - 1) / 2) (by
      refine (p2l_zeros_shift (w := E) (K := K) (fun x => (hpar x).1)).trans ?_
      exact p2l_eigenfunction_zeros hν hk0 hk1 _ _ _)
  refine hZ.trans ?_
  simp only [u, sub_self]
  have hnz : deriv E 0 = 0 → E 0 ≠ 0 :=
    fun hd h0 => hne (ODE.p2l_eq_zero (p2lPot_continuous hk) hw h0 hd)
  have hmod := Nat.mod_two_of_bodd m
  cases hbo : m.bodd <;> rw [hbo] at hmod <;>
    simp only [hbo, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hb <;>
    simp at hmod
  · simp only [show E 0 = 0 from hb.1, ↓reduceIte]
    exact_mod_cast (show 2 * ((m - 1) / 2) + 1 = m - 1 by omega)
  · simp only [hnz hb.1, ↓reduceIte]
    exact_mod_cast (show 2 * ((m - 1) / 2) + 0 = m - 1 by omega)

/-- Table 29.3.2: `Ec^m_ν(x, k²)` has exactly `⌊m/2⌋` zeros in `(0, K)` (the "nonnegative
integer `m`" of the table for `Ec^{2m}`, `Ec^{2m+1}`). -/
@[dlmf 29.3.iv]
theorem Real.lameEck_zeros_Ioo (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    {x ∈ Set.Ioo 0 (Real.compEllIntKm (k ^ 2)) | Real.lameEck ν m x k = 0}.Finite ∧
      {x ∈ Set.Ioo 0 (Real.compEllIntKm (k ^ 2)) | Real.lameEck ν m x k = 0}.ncard = m / 2 :=
  p2l_finite_ncard_of_encard (p2l_eigenfunction_zeros hν hk0 hk1 _ _ _)

/-- Table 29.3.2: `Es^m_ν(x, k²)` (`m ≥ 1`) has exactly `⌊(m - 1)/2⌋` zeros in `(0, K)`. -/
@[dlmf 29.3.iv]
theorem Real.lameEsk_zeros_Ioo (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    {x ∈ Set.Ioo 0 (Real.compEllIntKm (k ^ 2)) | Real.lameEsk ν m x k = 0}.Finite ∧
      {x ∈ Set.Ioo 0 (Real.compEllIntKm (k ^ 2)) | Real.lameEsk ν m x k = 0}.ncard =
        (m - 1) / 2 :=
  p2l_finite_ncard_of_encard (p2l_eigenfunction_zeros hν hk0 hk1 _ _ _)

/-- §29.3(iv): the superscript `m` of `Ec^m_ν` is the number of zeros in `[0, 2K)`. -/
@[dlmf 29.3.iv]
theorem Real.lameEck_zeros_Ico (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    {x ∈ Set.Ico 0 (2 * Real.compEllIntKm (k ^ 2)) | Real.lameEck ν m x k = 0}.Finite ∧
      {x ∈ Set.Ico 0 (2 * Real.compEllIntKm (k ^ 2)) | Real.lameEck ν m x k = 0}.ncard = m := by
  have hk := l29_sq_lt_one hk0 hk1
  have hK := Real.compEllIntKm_pos hk
  obtain ⟨hw, hb, hne⟩ := Real.lameEck_isLameEigenfunction hν hk0 hk1 m
  rw [p2l_isLameSolution_iff] at hw
  have hnz : ∀ x, deriv (fun x => Real.lameEck ν m x k) x = 0 → Real.lameEck ν m x k ≠ 0 :=
    fun x hd h0 => hne (ODE.p2l_eq_zero (p2lPot_continuous hk) hw h0 hd)
  refine p2l_finite_ncard_of_encard ?_
  have hZ := p2l_zeros_Ico (w := fun x => Real.lameEck ν m x k) hK (s := 1)
    (fun x => by rw [one_mul]; exact (Real.lameEck_parity hν hk0 hk1 m x).2.1)
    (p2l_eigenfunction_zeros hν hk0 hk1 _ _ _)
  rw [hZ]
  simp only [Real.LameBoundary, Bool.false_eq_true, ↓reduceIte] at hb
  simp only [hnz _ hb.2, ↓reduceIte]
  have hmod := Nat.mod_two_of_bodd m
  cases hbo : m.bodd <;> rw [hbo] at hmod <;> simp only [hbo, Bool.false_eq_true, ↓reduceIte] at hb
    <;> simp at hmod
  · simp only [hnz _ hb.1, ↓reduceIte]
    exact_mod_cast (show 2 * (m / 2) + (0 + 0) = m by omega)
  · simp only [hb.1, ↓reduceIte]
    exact_mod_cast (show 2 * (m / 2) + (1 + 0) = m by omega)

/-- §29.3(iv): the superscript `m` of `Es^m_ν` (`m ≥ 1`) is the number of zeros in `[0, 2K)`. -/
@[dlmf 29.3.iv]
theorem Real.lameEsk_zeros_Ico (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ)
    (hm : 1 ≤ m) :
    {x ∈ Set.Ico 0 (2 * Real.compEllIntKm (k ^ 2)) | Real.lameEsk ν m x k = 0}.Finite ∧
      {x ∈ Set.Ico 0 (2 * Real.compEllIntKm (k ^ 2)) | Real.lameEsk ν m x k = 0}.ncard = m := by
  have hk := l29_sq_lt_one hk0 hk1
  have hK := Real.compEllIntKm_pos hk
  obtain ⟨hw, hb, hne⟩ := Real.lameEsk_isLameEigenfunction hν hk0 hk1 m
  rw [p2l_isLameSolution_iff] at hw
  have hnz : ∀ x, deriv (fun x => Real.lameEsk ν m x k) x = 0 → Real.lameEsk ν m x k ≠ 0 :=
    fun x hd h0 => hne (ODE.p2l_eq_zero (p2lPot_continuous hk) hw h0 hd)
  refine p2l_finite_ncard_of_encard ?_
  have hZ := p2l_zeros_Ico (w := fun x => Real.lameEsk ν m x k) hK (s := -1)
    (fun x => by rw [neg_one_mul]; exact (Real.lameEsk_parity hν hk0 hk1 m x).2.1)
    (p2l_eigenfunction_zeros hν hk0 hk1 _ _ _)
  rw [hZ]
  simp only [Real.LameBoundary, ↓reduceIte] at hb
  simp only [hb.2, ↓reduceIte]
  have hmod := Nat.mod_two_of_bodd m
  cases hbo : m.bodd <;> rw [hbo] at hmod <;>
    simp only [hbo, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hb <;>
    simp at hmod
  · simp only [hb.1, ↓reduceIte]
    exact_mod_cast (show 2 * ((m - 1) / 2) + (1 + 1) = m by omega)
  · simp only [hnz _ hb.1, ↓reduceIte]
    exact_mod_cast (show 2 * ((m - 1) / 2) + (0 + 1) = m by omega)

/-! ### Distribution of the eigenvalues (§29.3(ii)) -/

/-- Interlacing 29.3.1: `a^m_ν(k²) < a^{m+1}_ν(k²)`. -/
@[dlmf 29.3.E1]
theorem Real.lameAk_lt_lameAk_succ (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    Real.lameAk ν m k < Real.lameAk ν (m + 1) k := by
  obtain ⟨-, h1⟩ := p2l_lameAk_shift hν hk0 hk1 m
  obtain ⟨hm2, h2⟩ := p2l_lameAk_shift hν hk0 hk1 (m + 1)
  by_contra hle
  push Not at hle
  have := Set.encard_le_encard (Set.inter_subset_inter_right
    (ODE.p2lSpec (fun x => p2lPot ν k (x - Real.compEllIntKm (k ^ 2)))
      (2 * Real.compEllIntKm (k ^ 2)) false false) (Set.Iio_subset_Iio hle))
  rw [h1, h2] at this
  norm_cast at this
  omega

/-- Interlacing 29.3.2: `a^m_ν(k²) < b^{m+1}_ν(k²)`. -/
@[dlmf 29.3.E2]
theorem Real.lameAk_lt_lameBk_succ (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    Real.lameAk ν m k < Real.lameBk ν (m + 1) k := by
  have h := (p2l_interlace hν hk0 hk1 m.bodd (m / 2)).1
  rw [Real.lameAk, Real.lameBk, Nat.bodd_succ, Bool.not_not,
    show (m + 1 - 1) / 2 = m / 2 by omega]
  exact h

/-- Interlacing 29.3.3: `b^m_ν(k²) < b^{m+1}_ν(k²)`, `m ≥ 1`. -/
@[dlmf 29.3.E3]
theorem Real.lameBk_lt_lameBk_succ (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) {m : ℕ}
    (hm : 1 ≤ m) : Real.lameBk ν m k < Real.lameBk ν (m + 1) k := by
  obtain ⟨-, h1⟩ := p2l_lameBk_shift hν hk0 hk1 hm
  obtain ⟨-, h2⟩ := p2l_lameBk_shift hν hk0 hk1 (by omega : 1 ≤ m + 1)
  by_contra hle
  push Not at hle
  have := Set.encard_le_encard (Set.inter_subset_inter_right
    (ODE.p2lSpec (fun x => p2lPot ν k (x - Real.compEllIntKm (k ^ 2)))
      (2 * Real.compEllIntKm (k ^ 2)) true true) (Set.Iio_subset_Iio hle))
  rw [h1, h2] at this
  norm_cast at this
  omega

/-- Interlacing 29.3.4: `b^m_ν(k²) < a^{m+1}_ν(k²)`, `m ≥ 1`. -/
@[dlmf 29.3.E4]
theorem Real.lameBk_lt_lameAk_succ (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) {m : ℕ}
    (hm : 1 ≤ m) : Real.lameBk ν m k < Real.lameAk ν (m + 1) k := by
  have h := (p2l_interlace hν hk0 hk1 (!m.bodd) ((m - 1) / 2)).2
  rw [Real.lameAk, Real.lameBk, Nat.bodd_succ, show (m + 1) / 2 = (m - 1) / 2 + 1 by omega]
  exact h

/-- Coalescence 29.3.5: `a^m_ν(k²) = b^m_ν(k²)` for `ν = 0, 1, …, m - 1`. Admitted. -/
@[dlmf 29.3.E5]
theorem Real.lameAk_eq_lameBk (hk0 : 0 < k) (hk1 : k < 1) {m n : ℕ} (hn : n < m) :
    Real.lameAk n m k = Real.lameBk n m k := by
  sorry

/-- 29.3.6: if `ν ∉ {0, 1, …, m - 1}` then `(a^m_ν(k²) - b^m_ν(k²)) ν(ν-1)⋯(ν-m+1) > 0`
(`m ≥ 1`). Admitted. -/
@[dlmf 29.3.E6]
theorem Real.lameAk_sub_lameBk_mul_pos (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) {m : ℕ}
    (hm : 1 ≤ m) (hνm : ∀ j : ℕ, j < m → ν ≠ j) :
    0 < (Real.lameAk ν m k - Real.lameBk ν m k) * ∏ j ∈ Finset.range m, (ν - j) := by
  sorry

/-- 29.3.7: for a nonnegative integer `ν = n`, `a^m_n(k²) + a^{n-m}_n(1 - k²) = n(n+1)`,
`m = 0, 1, …, n` (the second eigenvalue has modulus `k' = √(1 - k²)`). Admitted. -/
@[dlmf 29.3.E7]
theorem Real.lameAk_add_lameAk_comodulus (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameAk n m k + Real.lameAk n (n - m) (Real.sqrt (1 - k ^ 2)) = n * (n + 1) := by
  sorry

/-- 29.3.8: for a nonnegative integer `ν = n`, `b^m_n(k²) + b^{n-m+1}_n(1 - k²) = n(n+1)`,
`m = 1, …, n`. Admitted. -/
@[dlmf 29.3.E8]
theorem Real.lameBk_add_lameBk_comodulus (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ n) :
    Real.lameBk n m k + Real.lameBk n (n - m + 1) (Real.sqrt (1 - k ^ 2)) = n * (n + 1) := by
  sorry

/-! ### Continued fractions (§29.3(iii)) -/

/-- 29.3.9–29.3.12: `H = 2a^{2m}_ν(k²) - ν(ν+1)k²` satisfies the continued-fraction equation
29.3.10 with the coefficients 29.3.11–29.3.12 (`LameRecurrence.A0`), for every `p`: the
truncations of the right side converge to the (finite) left side. Stated for non-integer `ν`
and nonvanishing denominators on the left (DLMF's genericity assumption; for integer `ν` see
`Real.lameCF_A0_terminating`). Admitted. -/
@[dlmf 29.3.E9, dlmf 29.3.E10]
theorem Real.lameCF_A0 (hν : -1 / 2 ≤ ν) (hνZ : ∀ j : ℤ, ν ≠ j) (hk0 : 0 < k) (hk1 : k < 1)
    (m p : ℕ)
    (hden : ∀ q < p, lameCFLeft .A0 ν k (2 * Real.lameAk ν (2 * m) k - ν * (ν + 1) * k ^ 2) q ≠ 0) :
    Tendsto (lameCFRight .A0 ν k (2 * Real.lameAk ν (2 * m) k - ν * (ν + 1) * k ^ 2) p) atTop
      (𝓝 (lameCFLeft .A0 ν k (2 * Real.lameAk ν (2 * m) k - ν * (ν + 1) * k ^ 2) p)) := by
  sorry

/-- §29.3(iii): `H = 2a^{2m+1}_ν(k²) - ν(ν+1)k²` satisfies 29.3.10 with the coefficients
29.3.13–29.3.14 (`LameRecurrence.A1`); non-integer `ν`. Admitted. -/
@[dlmf 29.3.E10, dlmf 29.3.iii]
theorem Real.lameCF_A1 (hν : -1 / 2 ≤ ν) (hνZ : ∀ j : ℤ, ν ≠ j) (hk0 : 0 < k) (hk1 : k < 1)
    (m p : ℕ)
    (hden : ∀ q < p,
      lameCFLeft .A1 ν k (2 * Real.lameAk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2) q ≠ 0) :
    Tendsto (lameCFRight .A1 ν k (2 * Real.lameAk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2) p)
      atTop (𝓝 (lameCFLeft .A1 ν k (2 * Real.lameAk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2) p)) := by
  sorry

/-- §29.3(iii): `H = 2b^{2m+1}_ν(k²) - ν(ν+1)k²` satisfies 29.3.10 with the coefficients
29.3.15–29.3.16 (`LameRecurrence.B1`); non-integer `ν`. Admitted. -/
@[dlmf 29.3.E10, dlmf 29.3.iii]
theorem Real.lameCF_B1 (hν : -1 / 2 ≤ ν) (hνZ : ∀ j : ℤ, ν ≠ j) (hk0 : 0 < k) (hk1 : k < 1)
    (m p : ℕ)
    (hden : ∀ q < p,
      lameCFLeft .B1 ν k (2 * Real.lameBk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2) q ≠ 0) :
    Tendsto (lameCFRight .B1 ν k (2 * Real.lameBk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2) p)
      atTop (𝓝 (lameCFLeft .B1 ν k (2 * Real.lameBk ν (2 * m + 1) k - ν * (ν + 1) * k ^ 2) p)) := by
  sorry

/-- §29.3(iii): `H = 2b^{2m+2}_ν(k²) - ν(ν+1)k²` satisfies 29.3.10 with the coefficients
29.3.17 (`LameRecurrence.B2`); non-integer `ν`. Admitted. -/
@[dlmf 29.3.E10, dlmf 29.3.iii]
theorem Real.lameCF_B2 (hν : -1 / 2 ≤ ν) (hνZ : ∀ j : ℤ, ν ≠ j) (hk0 : 0 < k) (hk1 : k < 1)
    (m p : ℕ)
    (hden : ∀ q < p,
      lameCFLeft .B2 ν k (2 * Real.lameBk ν (2 * m + 2) k - ν * (ν + 1) * k ^ 2) q ≠ 0) :
    Tendsto (lameCFRight .B2 ν k (2 * Real.lameBk ν (2 * m + 2) k - ν * (ν + 1) * k ^ 2) p)
      atTop (𝓝 (lameCFLeft .B2 ν k (2 * Real.lameBk ν (2 * m + 2) k - ν * (ν + 1) * k ^ 2) p)) := by
  sorry

/-- §29.3(iii), terminating case: if `ν = n` is a nonnegative integer and `2p ≤ n`, the right
side of 29.3.10 (type `A0`) terminates (its truncations are eventually constant), and the
solutions `H` of 29.3.10 (with nonvanishing left denominators) are exactly the
`2a^{2m}_n(k²) - n(n+1)k²` with `2m ≤ n`. Admitted. -/
@[dlmf 29.3.iii]
theorem Real.lameCF_A0_terminating (hk0 : 0 < k) (hk1 : k < 1) {n p : ℕ} (hp : 2 * p ≤ n)
    (H : ℝ) (hden : ∀ q < p, lameCFLeft .A0 n k H q ≠ 0) :
    (∀ᶠ d in atTop, lameCFRight .A0 n k H p d = lameCFRight .A0 n k H p (n + 1)) ∧
      (Tendsto (lameCFRight .A0 n k H p) atTop (𝓝 (lameCFLeft .A0 n k H p)) ↔
        ∃ m : ℕ, 2 * m ≤ n ∧ H = 2 * Real.lameAk n (2 * m) k - n * (n + 1) * k ^ 2) := by
  sorry

/-! ### Orthogonality (§29.3(vi)) -/

/-- Orthogonality of eigenfunctions of one boundary type for distinct indices. -/
theorem Real.lameEigenfunction_orthogonal (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1)
    (odd0 oddK : Bool) {i j : ℕ} (hij : i ≠ j) :
    ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
      Real.lameEigenfunction ν k odd0 oddK i x * Real.lameEigenfunction ν k odd0 oddK j x = 0 := by
  have hi := (Real.isNormalizedLameEigenfunction_lameEigenfunction hν hk0 hk1 odd0 oddK i).1
  have hj := (Real.isNormalizedLameEigenfunction_lameEigenfunction hν hk0 hk1 odd0 oddK j).1
  have hne : Real.lameEigenvalue ν k odd0 oddK i ≠ Real.lameEigenvalue ν k odd0 oddK j :=
    fun he => hij ((Real.lameEigenvalue_spec hν hk0 hk1 odd0 oddK).2.1.injective he)
  have hb := l29_wronskian_boundary hi.2.1 hj.2.1
  exact l29_integral_mul_eq_zero hne hi.1 hj.1 hb.1 hb.2

/-- Orthogonality 29.3.19, first line: `∫₀^K Ec^{2m}_ν Ec^{2p}_ν dx = 0` for `m ≠ p`. -/
@[dlmf 29.3.E19]
theorem Real.lameEck_even_orthogonal (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) {m p : ℕ}
    (hmp : m ≠ p) :
    ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
      Real.lameEck ν (2 * m) x k * Real.lameEck ν (2 * p) x k = 0 := by
  have := Real.lameEigenfunction_orthogonal hν hk0 hk1 false false hmp
  simpa [Real.lameEck, Nat.bodd_mul] using this

/-- Orthogonality 29.3.19, second line: `∫₀^K Ec^{2m+1}_ν Ec^{2p+1}_ν dx = 0` for `m ≠ p`. -/
@[dlmf 29.3.E19]
theorem Real.lameEck_odd_orthogonal (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) {m p : ℕ}
    (hmp : m ≠ p) :
    ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
      Real.lameEck ν (2 * m + 1) x k * Real.lameEck ν (2 * p + 1) x k = 0 := by
  have := Real.lameEigenfunction_orthogonal hν hk0 hk1 true false hmp
  simpa [Real.lameEck, Nat.bodd_mul, Nat.bodd_add, Nat.mul_add_div] using this

/-- Orthogonality 29.3.19, third line: `∫₀^K Es^{2m+1}_ν Es^{2p+1}_ν dx = 0` for `m ≠ p`. -/
@[dlmf 29.3.E19]
theorem Real.lameEsk_odd_orthogonal (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) {m p : ℕ}
    (hmp : m ≠ p) :
    ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
      Real.lameEsk ν (2 * m + 1) x k * Real.lameEsk ν (2 * p + 1) x k = 0 := by
  have := Real.lameEigenfunction_orthogonal hν hk0 hk1 false true hmp
  simpa [Real.lameEsk, Nat.bodd_mul, Nat.bodd_add] using this

/-- Orthogonality 29.3.19, fourth line: `∫₀^K Es^{2m+2}_ν Es^{2p+2}_ν dx = 0` for `m ≠ p`. -/
@[dlmf 29.3.E19]
theorem Real.lameEsk_even_orthogonal (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) {m p : ℕ}
    (hmp : m ≠ p) :
    ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
      Real.lameEsk ν (2 * m + 2) x k * Real.lameEsk ν (2 * p + 2) x k = 0 := by
  have := Real.lameEigenfunction_orthogonal hν hk0 hk1 true true hmp
  have e : ∀ q : ℕ, (2 * q + 2 - 1) / 2 = q := fun q => by omega
  have e' : ∀ q : ℕ, (2 * q + 1) / 2 = q := fun q => by omega
  simpa [Real.lameEsk, Nat.bodd_mul, Nat.bodd_add, e, e'] using this

/-! ### Stability (§29.9) -/

/-- §29.9, non-integer `ν`: Lamé's equation is unstable iff `h ≤ a^0_ν(k²)` or `h` lies in one
of the closed intervals with endpoints `a^m_ν(k²)`, `b^m_ν(k²)`, `m ≥ 1`. Admitted. -/
@[dlmf 29.9]
theorem Real.not_isLameStable_iff (hν : -1 / 2 ≤ ν) (hνZ : ∀ j : ℤ, ν ≠ j) (hk0 : 0 < k)
    (hk1 : k < 1) (h : ℝ) :
    ¬Real.IsLameStable h ν k ↔ h ≤ Real.lameAk ν 0 k ∨
      ∃ m : ℕ, 1 ≤ m ∧ h ∈ Set.uIcc (Real.lameAk ν m k) (Real.lameBk ν m k) := by
  sorry

/-- §29.9, nonnegative integer `ν = n`: Lamé's equation is unstable iff `h ≤ a^0_n(k²)` or
`h ∈ [b^m_n(k²), a^m_n(k²)]` for some `m = 1, …, n`. Admitted. -/
@[dlmf 29.9]
theorem Real.not_isLameStable_iff_nat (hk0 : 0 < k) (hk1 : k < 1) (n : ℕ) (h : ℝ) :
    ¬Real.IsLameStable h n k ↔ h ≤ Real.lameAk n 0 k ∨
      ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ h ∈ Set.Icc (Real.lameBk n m k) (Real.lameAk n m k) := by
  sorry

end DLMF.Lame
