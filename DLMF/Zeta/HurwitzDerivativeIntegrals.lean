/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Hurwitz
public import DLMFMathlib.Analysis.SpecialFunctions.Log.Ray
public import DLMFMathlib.Analysis.Calculus.Deriv.Appell

/-!
# Integrals of order derivatives of the Hurwitz zeta function

DLMF 25.11.32 and 25.11.34 follow from the mixed derivative formula for `ζ(s, a)`,
the Bernoulli polynomial values at negative integers and a harmonic-number correction
that makes the order derivatives into an Appell family. The recurrence at `a = 0` isolates
an integrable logarithmic monomial and identifies the endpoint with the derivative
of the Riemann zeta function.
-/

@[expose] public section

open Complex Filter Set MeasureTheory intervalIntegral
open scoped Nat Real Topology

noncomputable section

namespace DLMF.Zeta

/-- The derivative in the order of the shift recurrence for `ζ(s, a)`. -/
lemma deriv_hurwitzZetaComplex_eq_add_one {s a : ℂ} (hs : s ≠ 1) (ha : 0 < a.re) :
    deriv (fun z => hurwitzZetaComplex z a) s =
      deriv (fun z => hurwitzZetaComplex z (a + 1)) s - log a * a ^ (-s) := by
  have hz : ∀ n : ℕ, a + n ≠ 0 := by
    intro n hn
    have hpos : 0 < (a + n).re := by simp only [add_re, natCast_re]; positivity
    simp [hn] at hpos
  have ha0 : a ≠ 0 := by simpa using hz 0
  have hz1 : ∀ n : ℕ, a + 1 + n ≠ 0 := by
    intro n hn
    exact hz (n + 1) (by push_cast; linear_combination hn)
  have hEq : (fun z => hurwitzZetaComplex z a) =ᶠ[𝓝 s]
      (fun z => hurwitzZetaComplex z (a + 1) + a ^ (-z)) := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz'
    exact hurwitzZetaComplex_eq_add_one hz' (fun n hn => hz n (by rw [hn]; ring))
  have hD := (differentiableAt_hurwitzZetaComplex_of_add_ne_zero hs hz1).hasDerivAt.add
    ((hasDerivAt_id s).neg.const_cpow (c := a) (Or.inl ha0))
  change HasDerivAt (fun z => hurwitzZetaComplex z (a + 1) + a ^ (-z))
    (deriv (fun z => hurwitzZetaComplex z (a + 1)) s + a ^ (-s) * log a * (-1)) s at hD
  rw [hEq.deriv_eq, hD.deriv]
  ring

/-- Continuity in the argument of the order derivative, away from the pole and cut. -/
lemma continuousAt_deriv_hurwitzZetaComplex_param {s a : ℂ} (hs : s ≠ 1) (ha : 0 < a.re) :
    ContinuousAt (fun w => deriv (fun z => hurwitzZetaComplex z w) s) a :=
  (analyticAt_deriv_hurwitzZetaComplex_joint hs ha).continuousAt.comp
    (continuousAt_const.prodMk continuousAt_id)

/-- Integrability of `ζ'(-n, ta)` along a segment approaching the origin. -/
lemma intervalIntegrable_deriv_hurwitzZetaComplex_neg_nat (n : ℕ) {a : ℂ}
    (ha : 0 < a.re) :
    IntervalIntegrable (fun t : ℝ => deriv (fun s => hurwitzZetaComplex s (t * a)) (-n))
      volume 0 1 := by
  have hs : -(n : ℂ) ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    simp only [neg_re, natCast_re, one_re] at he
    linarith [n.cast_nonneg (α := ℝ)]
  have hc : ContinuousOn
      (fun t : ℝ => deriv (fun s => hurwitzZetaComplex s ((t : ℂ) * a + 1)) (-n))
      (Icc 0 1) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    apply (continuousAt_deriv_hurwitzZetaComplex_param hs ?_).comp
      (by fun_prop : ContinuousAt (fun t : ℝ => (t : ℂ) * a + 1) t)
    simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, one_re]
    have ht0 : 0 ≤ t := ht.1
    positivity
  rw [← uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hc
  have hi := hc.intervalIntegrable.sub (Complex.intervalIntegrable_log_mul_pow_ray a n)
  apply hi.congr_uIoo
  intro t ht
  have ht0 : 0 < t := by simpa using ht.1
  have hta : 0 < ((t : ℂ) * a).re := by simpa using mul_pos ht0 ha
  simpa only [neg_neg, cpow_natCast] using
    (deriv_hurwitzZetaComplex_eq_add_one hs hta).symm

/-- Endpoint of `ζ'(-n, ta)` at the origin for `n ≥ 1`. -/
lemma tendsto_deriv_hurwitzZetaComplex_neg_nat_zero {n : ℕ} (hn : 0 < n) {a : ℂ}
    (ha : 0 < a.re) :
    Tendsto (fun t : ℝ => deriv (fun s => hurwitzZetaComplex s (t * a)) (-n))
      (𝓝[>] 0) (𝓝 (deriv riemannZeta (-n))) := by
  have hs : -(n : ℂ) ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    simp only [neg_re, natCast_re, one_re] at he
    linarith [n.cast_nonneg (α := ℝ)]
  have hray : Continuous (fun t : ℝ => (t : ℂ) * a + 1) := by fun_prop
  have hraylim : Tendsto (fun t : ℝ => (t : ℂ) * a + 1) (𝓝[>] 0) (𝓝 1) := by
    simpa only [ofReal_zero, zero_mul, zero_add] using
      (hray.tendsto 0).mono_left nhdsWithin_le_nhds
  have hleft := (continuousAt_deriv_hurwitzZetaComplex_param hs
    (by norm_num : 0 < (1 : ℂ).re)).tendsto.comp hraylim
  change Tendsto (fun t : ℝ => deriv (fun s => hurwitzZetaComplex s (t * a + 1)) (-n))
    (𝓝[>] 0) (𝓝 (deriv (fun s => hurwitzZetaComplex s 1) (-n))) at hleft
  have hriemann : deriv (fun s => hurwitzZetaComplex s 1) (-n) =
      deriv riemannZeta (-n) := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_ne.mem_nhds hs] with s hs'
    exact hurwitzZetaComplex_one hs'
  rw [hriemann] at hleft
  have h := hleft.sub (Complex.tendsto_log_mul_pow_ray hn a)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hta : 0 < ((t : ℂ) * a).re := by simpa using mul_pos ht ha
  simpa only [neg_neg, cpow_natCast] using
    (deriv_hurwitzZetaComplex_eq_add_one hs hta).symm

/-- Integral of a nonpositive integral order of `ζ(s, a)` along a segment. -/
lemma integral_hurwitzZetaComplex_one_sub_nat {n : ℕ} (hn : 1 ≤ n) (a : ℂ) :
    ∫ t in (0 : ℝ)..1, a * hurwitzZetaComplex (1 - n) (t * a) =
      ((bernoulli (n + 1) : ℂ) -
        ((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)).eval a) / (n * (n + 1)) := by
  let P : Polynomial ℂ := (Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)
  let Q : Polynomial ℂ := (Polynomial.bernoulli n).map (algebraMap ℚ ℂ)
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  have hsn : (1 : ℂ) - n = -((n - 1 : ℕ) : ℂ) := by
    rw [Nat.cast_sub hn]
    push_cast
    ring
  have heq (t : ℝ) : hurwitzZetaComplex (1 - n) (t * a) = -Q.eval (t * a) / n := by
    rw [hsn, hurwitzZetaComplex_neg_nat']
    simp only [show n - 1 + 1 = n by omega, Nat.cast_sub hn, Nat.cast_one]
    simp only [sub_add_cancel]
    rfl
  have hP : P.derivative = (n + 1) * Q := by
    simp [P, Q, Polynomial.derivative_map, Polynomial.derivative_bernoulli_add_one]
  have hD (t : ℝ) :
      HasDerivAt (fun u : ℝ => -P.eval ((u : ℂ) * a) / (n * (n + 1)))
        (a * hurwitzZetaComplex (1 - n) (t * a)) t := by
    have hd := ((P.hasDerivAt ((t : ℂ) * a)).comp (t : ℂ)
      ((hasDerivAt_id (t : ℂ)).mul_const a)).comp_ofReal.neg.div_const (n * (n + 1))
    simp only [Function.comp_def, Pi.neg_apply, id_eq, one_mul] at hd
    change HasDerivAt (fun u : ℝ => -P.eval ((u : ℂ) * a) / (n * (n + 1)))
      (-(P.derivative.eval ((t : ℂ) * a) * a) / (n * (n + 1))) t at hd
    convert hd using 1
    rw [heq t, hP]
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_natCast,
      Polynomial.eval_one]
    field_simp
  have hi : IntervalIntegrable (fun t : ℝ => a * hurwitzZetaComplex (1 - n) (t * a))
      volume 0 1 := by
    simp_rw [heq]
    exact (show Continuous (fun t : ℝ => a * (-Q.eval ((t : ℂ) * a) / n)) by
      fun_prop).intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hD t) hi
  have hzero : P.eval 0 = (bernoulli (n + 1) : ℂ) := by
    simpa [P] using
      (Polynomial.eval_map_apply (p := Polynomial.bernoulli (n + 1)) (algebraMap ℚ ℂ) 0)
  simp only [ofReal_one, one_mul, ofReal_zero, zero_mul, hzero] at h
  rw [h]
  dsimp only [P]
  ring

/-- **Integral of `ζ'(1-n, x)`** (DLMF 25.11.34): for `n ≥ 1`, `Re a > 0`, along `[0, a]`,
`n ∫_0^a ζ'(1-n, x) dx = ζ'(-n, a) - ζ'(-n) + (B_{n+1} - B_{n+1}(a))/(n(n+1))`. -/
@[dlmf 25.11.E34]
theorem integral_deriv_hurwitzZetaComplex {n : ℕ} (hn : 1 ≤ n) {a : ℂ} (ha : 0 < a.re) :
    n * ∫ t in (0 : ℝ)..1, a * deriv (fun s => hurwitzZetaComplex s (t * a)) (1 - n) =
      deriv (fun s => hurwitzZetaComplex s a) (-n) - deriv riemannZeta (-n) +
        ((bernoulli (n + 1) : ℂ) - ((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)).eval a) /
          (n * (n + 1)) := by
  have hn0 : n ≠ 0 := by omega
  have hs0 : -(n : ℂ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hn0)
  have hs1 : -(n : ℂ) ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    simp only [neg_re, natCast_re, one_re] at he
    linarith [n.cast_nonneg (α := ℝ)]
  have hsn : (1 : ℂ) - n = -((n - 1 : ℕ) : ℂ) := by
    rw [Nat.cast_sub hn]
    push_cast
    ring
  let F : ℝ → ℂ := fun t => deriv (fun s => hurwitzZetaComplex s (t * a)) (-n)
  let G : ℝ → ℂ := fun t => a * deriv (fun s => hurwitzZetaComplex s (t * a)) (1 - n)
  let H : ℝ → ℂ := fun t => a * hurwitzZetaComplex (1 - n) (t * a)
  have hG : IntervalIntegrable G volume 0 1 := by
    dsimp only [G]
    rw [hsn]
    exact (intervalIntegrable_deriv_hurwitzZetaComplex_neg_nat (n - 1) ha).const_mul a
  have hH : IntervalIntegrable H volume 0 1 := by
    dsimp only [H]
    simp_rw [hsn, hurwitzZetaComplex_neg_nat']
    exact (show Continuous
      (fun t : ℝ => a *
        (-((Polynomial.bernoulli (n - 1 + 1)).map (algebraMap ℚ ℂ)).eval ((t : ℂ) * a) /
          ((n - 1 : ℕ) + 1 : ℂ))) by fun_prop).intervalIntegrable 0 1
  have hD (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt F (n * G t - H t) t := by
    have hta : 0 < ((t : ℂ) * a).re := by simpa using mul_pos ht.1 ha
    have hd := ((hasDerivAt_deriv_hurwitzZetaComplex_param hs0 hs1 hta).comp
      (t : ℂ) ((hasDerivAt_id (t : ℂ)).mul_const a)).comp_ofReal
    simp only [Function.comp_def, id_eq, one_mul] at hd
    rw [show -(n : ℂ) + 1 = 1 - n by ring] at hd
    change HasDerivAt F
      ((-hurwitzZetaComplex (1 - n) (t * a) -
        -(n : ℂ) * deriv (fun z => hurwitzZetaComplex z (t * a)) (1 - n)) * a) t at hd
    convert hd using 1
    dsimp only [G, H]
    ring
  have hzero : Tendsto F (𝓝[>] 0) (𝓝 (deriv riemannZeta (-n))) :=
    tendsto_deriv_hurwitzZetaComplex_neg_nat_zero (by omega) ha
  have hone : Tendsto F (𝓝[<] 1)
      (𝓝 (deriv (fun s => hurwitzZetaComplex s a) (-n))) := by
    have hray : Continuous (fun t : ℝ => (t : ℂ) * a) := by fun_prop
    have ht : Tendsto (fun t : ℝ => (t : ℂ) * a) (𝓝[<] 1) (𝓝 a) := by
      simpa only [ofReal_one, one_mul] using
        (hray.tendsto 1).mono_left nhdsWithin_le_nhds
    exact (continuousAt_deriv_hurwitzZetaComplex_param hs1 ha).tendsto.comp ht
  have hInt := integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num : (0 : ℝ) < 1)
    hD ((hG.const_mul (n : ℂ)).sub hH) hzero hone
  rw [integral_sub (hG.const_mul (n : ℂ)) hH, intervalIntegral.integral_const_mul] at hInt
  have hHval := integral_hurwitzZetaComplex_one_sub_nat hn a
  change ∫ t in (0 : ℝ)..1, H t = _ at hHval
  rw [hHval] at hInt
  dsimp only [G] at hInt
  linear_combination hInt

/-- The argument derivative of `ζ'(0, a)` is the digamma function on `Re a > 0`. -/
lemma hasDerivAt_deriv_hurwitzZetaComplex_zero_param {a : ℂ} (ha : 0 < a.re) :
    HasDerivAt (fun w => deriv (fun s => hurwitzZetaComplex s w) 0) (digamma a) a := by
  let F : ℂ → ℂ := fun w => deriv (fun s => hurwitzZetaComplex s w) 0
  have hF {w : ℂ} (hw : 0 < w.re) : AnalyticAt ℂ F w :=
    (analyticAt_deriv_hurwitzZetaComplex_joint (by norm_num : (0 : ℂ) ≠ 1) hw).comp
      (analyticAt_const.prod analyticAt_id)
  have hreal {x : ℝ} (hx : 0 < x) : deriv F x = digamma x := by
    have hEq : (fun y : ℝ => F y) =ᶠ[𝓝 x]
        (fun y : ℝ => ((Real.log (Real.Gamma y) - Real.log (2 * π) / 2 : ℝ) : ℂ)) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      exact deriv_hurwitzZetaComplex_zero hy
    have hL := (hF (by simpa using hx)).differentiableAt.hasDerivAt.comp_ofReal
    have hR := ((DLMF.Gamma.Real.hasDerivAt_log_Gamma hx).sub_const
      (Real.log (2 * π) / 2)).ofReal_comp
    rw [DLMF.Gamma.digamma_ofReal hx]
    exact hL.unique (hR.congr_of_eventuallyEq hEq)
  have hFn : AnalyticOnNhd ℂ (deriv F) {w : ℂ | 0 < w.re} :=
    fun w hw => (hF hw).deriv
  have hψ : AnalyticOnNhd ℂ digamma {w : ℂ | 0 < w.re} := by
    intro w hw
    apply DLMF.Gamma.analyticAt_digamma
    intro m hm
    exact Complex.add_natCast_ne_zero_of_re_pos hw m (by rw [hm]; ring)
  have heq : deriv F a = digamma a := by
    refine hFn.eqOn_of_preconnected_of_frequently_eq hψ
      (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected (z₀ := 1) (by norm_num) ?_ ha
    have hev : ∀ᶠ x : ℝ in 𝓝[≠] 1, deriv F x = digamma x := by
      filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
        with x hx
      exact hreal hx
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 1) (𝓝[≠] 1) :=
      continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun x hx => by simpa using hx
    simpa using ht.frequently hev.frequently
  exact heq ▸ (hF ha).differentiableAt.hasDerivAt

namespace HurwitzOrderDerivatives

/-- The order derivative at `-n` corrected by `Hₙ ζ(-n, a)`; this is an Appell family in `a`. -/
def harmonicCorrection (n : ℕ) (a : ℂ) : ℂ :=
  deriv (fun s => hurwitzZetaComplex s a) (-n) + (harmonic n : ℂ) * hurwitzZetaComplex (-n) a

/-- The degree-zero corrected order derivative has argument derivative `ψ(a)`. -/
lemma hasDerivAt_harmonicCorrection_zero {a : ℂ} (ha : 0 < a.re) :
    HasDerivAt (harmonicCorrection 0) (digamma a) a := by
  convert hasDerivAt_deriv_hurwitzZetaComplex_zero_param ha using 1
  funext w
  simp [harmonicCorrection]

/-- The harmonic correction makes the order derivatives into an Appell family. -/
lemma hasDerivAt_harmonicCorrection_succ (n : ℕ) {a : ℂ} (ha : 0 < a.re) :
    HasDerivAt (harmonicCorrection (n + 1)) ((n + 1) * harmonicCorrection n a) a := by
  have hs0 : -((n + 1 : ℕ) : ℂ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n)
  have hs1 : -((n + 1 : ℕ) : ℂ) ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    simp only [neg_re, natCast_re, one_re] at he
    linarith [n.cast_nonneg (α := ℝ)]
  have hd := (hasDerivAt_deriv_hurwitzZetaComplex_param hs0 hs1 ha).add
    ((hasDerivAt_hurwitzZetaComplex_param' hs0 hs1 ha).const_mul (harmonic (n + 1) : ℂ))
  have hshift : -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) := by push_cast; ring
  rw [hshift] at hd
  change HasDerivAt (harmonicCorrection (n + 1))
    (-hurwitzZetaComplex (-n) a - -((n + 1 : ℕ) : ℂ) *
      deriv (fun s => hurwitzZetaComplex s a) (-n) +
      (harmonic (n + 1) : ℂ) * (- -((n + 1 : ℕ) : ℂ) * hurwitzZetaComplex (-n) a)) a at hd
  convert hd using 1
  simp only [harmonicCorrection, harmonic_succ]
  push_cast
  field_simp
  ring

/-- A weighted corrected order derivative has a finite endpoint whenever its total degree is
positive. -/
lemma tendsto_harmonicCorrection_mul_pow_zero (j m : ℕ) (hjm : 0 < j + m) {a : ℂ}
    (ha : 0 < a.re) :
    Tendsto (fun t : ℝ => harmonicCorrection j (t * a) * ((t : ℂ) * a) ^ m) (𝓝[>] 0)
      (𝓝 (if m = 0 then deriv riemannZeta (-j) +
        (harmonic j : ℂ) * hurwitzZetaComplex (-j) 0 else 0)) := by
  let e : ℂ := if m = 0 then 1 else 0
  have hs : -(j : ℂ) ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    simp only [neg_re, natCast_re, one_re] at he
    linarith [j.cast_nonneg (α := ℝ)]
  have hray : Continuous (fun t : ℝ => (t : ℂ) * a + 1) := by fun_prop
  have hshift := (continuousAt_deriv_hurwitzZetaComplex_param hs
    (by norm_num : 0 < (1 : ℂ).re)).tendsto.comp
    (show Tendsto (fun t : ℝ => (t : ℂ) * a + 1) (𝓝[>] 0) (𝓝 1) by
      simpa only [ofReal_zero, zero_mul, zero_add] using
        (hray.tendsto 0).mono_left nhdsWithin_le_nhds)
  have hriemann : deriv (fun s => hurwitzZetaComplex s 1) (-j) =
      deriv riemannZeta (-j) := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_ne.mem_nhds hs] with s hs'
    exact hurwitzZetaComplex_one hs'
  rw [hriemann] at hshift
  have hpow : Tendsto (fun t : ℝ => ((t : ℂ) * a) ^ m) (𝓝[>] 0) (𝓝 e) := by
    have hc : Continuous (fun t : ℝ => ((t : ℂ) * a) ^ m) := by fun_prop
    simpa only [ofReal_zero, zero_mul, zero_pow_eq, e] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hd := (hshift.mul hpow).sub (Complex.tendsto_log_mul_pow_ray hjm a)
  simp only [sub_zero] at hd
  have hderiv : Tendsto (fun t : ℝ =>
      deriv (fun s => hurwitzZetaComplex s (t * a)) (-j) * ((t : ℂ) * a) ^ m)
      (𝓝[>] 0) (𝓝 (deriv riemannZeta (-j) * e)) := by
    apply hd.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hta : 0 < ((t : ℂ) * a).re := by simpa using mul_pos ht ha
    dsimp only [Function.comp_def]
    rw [deriv_hurwitzZetaComplex_eq_add_one hs hta, neg_neg, cpow_natCast, sub_mul,
      mul_assoc, ← pow_add]
  have hζ : Tendsto (fun t : ℝ => hurwitzZetaComplex (-j) (t * a)) (𝓝[>] 0)
      (𝓝 (hurwitzZetaComplex (-j) 0)) := by
    simp_rw [hurwitzZetaComplex_neg_nat']
    have hc : Continuous (fun t : ℝ =>
        -((Polynomial.bernoulli (j + 1)).map (algebraMap ℚ ℂ)).eval ((t : ℂ) * a) /
          (j + 1 : ℂ)) := by fun_prop
    simpa only [ofReal_zero, zero_mul] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := hderiv.add ((hζ.mul hpow).const_mul (harmonic j : ℂ))
  convert h using 1
  · funext t
    dsimp only [harmonicCorrection]
    ring
  · dsimp only [e]
    split_ifs <;> simp only [mul_one, mul_zero, zero_add]

end HurwitzOrderDerivatives

/-- A positive integral power cancels the simple pole of `ψ(ta)` at the origin. -/
lemma intervalIntegrable_pow_mul_digamma {n : ℕ} (hn : 1 ≤ n) {a : ℂ}
    (ha : 0 < a.re) :
    IntervalIntegrable (fun t : ℝ => a * ((t : ℂ) * a) ^ n * digamma (t * a))
      volume 0 1 := by
  have hψ : ContinuousOn (fun t : ℝ => digamma ((t : ℂ) * a + 1)) (Icc 0 1) := by
    intro t ht
    have hpos : 0 < ((t : ℂ) * a + 1).re := by
      simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, one_re]
      have ht0 : 0 ≤ t := ht.1
      positivity
    have hnat : ∀ m : ℕ, (t : ℂ) * a + 1 ≠ -m := by
      intro m hm
      exact Complex.add_natCast_ne_zero_of_re_pos hpos m (by rw [hm]; ring)
    have hcomp : ContinuousAt (fun u : ℝ => digamma ((u : ℂ) * a + 1)) t :=
      (DLMF.Gamma.analyticAt_digamma hnat).continuousAt.comp
        (f := fun u : ℝ => (u : ℂ) * a + 1) (x := t) (by fun_prop)
    exact hcomp.continuousWithinAt
  have hc : ContinuousOn (fun t : ℝ =>
      a * ((t : ℂ) * a) ^ n * digamma ((t : ℂ) * a + 1) - a * ((t : ℂ) * a) ^ (n - 1))
      (Icc 0 1) := by
    exact ((by fun_prop : ContinuousOn (fun t : ℝ => a * ((t : ℂ) * a) ^ n)
      (Icc 0 1)).mul hψ).sub (by fun_prop)
  rw [← uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hc
  apply hc.intervalIntegrable.congr_uIoo
  intro t ht
  have ht0 : 0 < t := by simpa using ht.1
  have hta : 0 < ((t : ℂ) * a).re := by simpa using mul_pos ht0 ha
  have hnat : ∀ m : ℕ, (t : ℂ) * a ≠ -m := by
    intro m hm
    exact Complex.add_natCast_ne_zero_of_re_pos hta m (by rw [hm]; ring)
  have hta0 : (t : ℂ) * a ≠ 0 := by
    simpa only [Nat.cast_zero, add_zero] using Complex.add_natCast_ne_zero_of_re_pos hta 0
  have hpow : ((t : ℂ) * a) ^ n * ((t : ℂ) * a)⁻¹ = ((t : ℂ) * a) ^ (n - 1) := by
    calc
      ((t : ℂ) * a) ^ n * ((t : ℂ) * a)⁻¹ =
          (((t : ℂ) * a) ^ (n - 1) * ((t : ℂ) * a)) * ((t : ℂ) * a)⁻¹ := by
            rw [← pow_succ, Nat.sub_add_cancel hn]
      _ = _ := by rw [mul_assoc, mul_inv_cancel₀ hta0, mul_one]
  dsimp only
  rw [Complex.digamma_apply_add_one _ hnat]
  linear_combination a * hpow

/-- **Moments of the digamma function** (DLMF 25.11.32): for `n ≥ 1` and `Re a > 0`, with the
harmonic numbers `H_k` (25.11.33) and `ζ'` the `s`-derivative,
`∫_0^a xⁿ ψ(x) dx = (-1)^{n-1} ζ'(-n) + (-1)ⁿ Hₙ B_{n+1}/(n+1)
 - ∑_{k=0}^{n} (-1)^k C(n,k) H_k (B_{k+1}(a)/(k+1)) a^{n-k}
 + ∑_{k=0}^{n} (-1)^k C(n,k) ζ'(-k, a) a^{n-k}`, the integral along `[0, a]`. -/
@[dlmf 25.11.E32]
theorem integral_pow_mul_digamma {n : ℕ} (hn : 1 ≤ n) {a : ℂ} (ha : 0 < a.re) :
    ∫ t in (0 : ℝ)..1, a * (t * a) ^ n * digamma (t * a) =
      (-1) ^ (n - 1) * deriv riemannZeta (-n) +
        (-1) ^ n * (harmonic n : ℂ) * bernoulli (n + 1) / (n + 1) -
        ∑ k ∈ Finset.range (n + 1), (-1) ^ k * (n.choose k : ℂ) * (harmonic k : ℂ) *
          (((Polynomial.bernoulli (k + 1)).map (algebraMap ℚ ℂ)).eval a / (k + 1)) * a ^ (n - k) +
        ∑ k ∈ Finset.range (n + 1), (-1) ^ k * (n.choose k : ℂ) *
          deriv (fun s => hurwitzZetaComplex s a) (-k) * a ^ (n - k) := by
  open HurwitzOrderDerivatives in
  let S : ℂ → ℂ := fun w => ∑ k ∈ Finset.range (n + 1),
    (-1) ^ k * (n.choose k : ℂ) * harmonicCorrection k w * w ^ (n - k)
  have hS {w : ℂ} (hw : 0 < w.re) : HasDerivAt S (w ^ n * digamma w) w := by
    exact HasDerivAt.sum_choose_mul_pow_appell n
      (HurwitzOrderDerivatives.hasDerivAt_harmonicCorrection_zero hw)
      (fun k _ => HurwitzOrderDerivatives.hasDerivAt_harmonicCorrection_succ k hw)
  have hD (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => S ((t : ℂ) * a))
        (a * ((t : ℂ) * a) ^ n * digamma (t * a)) t := by
    have hta : 0 < ((t : ℂ) * a).re := by simpa using mul_pos ht.1 ha
    have hd := ((hS hta).comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).mul_const a)).comp_ofReal
    simp only [Function.comp_def, id_eq, one_mul] at hd
    convert hd using 1
    ring
  have hzero : Tendsto (fun t : ℝ => S ((t : ℂ) * a)) (𝓝[>] 0)
      (𝓝 ((-1) ^ n * (deriv riemannZeta (-n) +
        (harmonic n : ℂ) * hurwitzZetaComplex (-n) 0))) := by
    have hends (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :=
      (HurwitzOrderDerivatives.tendsto_harmonicCorrection_mul_pow_zero k (n - k)
        (by have := Finset.mem_range.mp hk; omega) ha).const_mul
          ((-1) ^ k * (n.choose k : ℂ))
    have h := tendsto_finsetSum (Finset.range (n + 1)) hends
    have hsum : (∑ k ∈ Finset.range (n + 1),
        (-1) ^ k * (n.choose k : ℂ) * (if n - k = 0 then deriv riemannZeta (-k) +
          (harmonic k : ℂ) * hurwitzZetaComplex (-k) 0 else 0)) =
        (-1) ^ n * (deriv riemannZeta (-n) +
          (harmonic n : ℂ) * hurwitzZetaComplex (-n) 0) := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro k hk hkn
        have hnk : n - k ≠ 0 := by have := Finset.mem_range.mp hk; omega
        simp only [hnk, ite_false, mul_zero]
      · simp
    rw [hsum] at h
    simpa only [S, mul_assoc] using h
  have hone : Tendsto (fun t : ℝ => S ((t : ℂ) * a)) (𝓝[<] 1) (𝓝 (S a)) := by
    have hray : Continuous (fun t : ℝ => (t : ℂ) * a) := by fun_prop
    apply (hS ha).continuousAt.tendsto.comp
    simpa only [ofReal_one, one_mul] using
      (hray.tendsto 1).mono_left nhdsWithin_le_nhds
  have h := integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num : (0 : ℝ) < 1)
    hD (intervalIntegrable_pow_mul_digamma hn ha) hzero hone
  have hSa : S a =
      (∑ k ∈ Finset.range (n + 1), (-1) ^ k * (n.choose k : ℂ) *
        deriv (fun s => hurwitzZetaComplex s a) (-k) * a ^ (n - k)) -
      (∑ k ∈ Finset.range (n + 1), (-1) ^ k * (n.choose k : ℂ) * (harmonic k : ℂ) *
        (((Polynomial.bernoulli (k + 1)).map (algebraMap ℚ ℂ)).eval a / (k + 1)) *
          a ^ (n - k)) := by
    dsimp only [S]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [HurwitzOrderDerivatives.harmonicCorrection, hurwitzZetaComplex_neg_nat']
    ring
  have hζzero : hurwitzZetaComplex (-n) 0 = -(bernoulli (n + 1) : ℂ) / (n + 1) := by
    rw [hurwitzZetaComplex_neg_nat']
    congr 2
    simpa using (Polynomial.eval_map_apply (p := Polynomial.bernoulli (n + 1))
      (algebraMap ℚ ℂ) 0)
  have hsign : -(-1 : ℂ) ^ n = (-1) ^ (n - 1) := by
    conv_lhs => rw [← show n - 1 + 1 = n by omega, pow_succ]
    ring
  rw [hSa, hζzero] at h
  rw [h, ← hsign]
  ring

end DLMF.Zeta
