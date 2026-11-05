/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Basic.Hurwitz
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import DLMFMathlib.Analysis.Complex.BivariateCalculus
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Joint holomorphy of the Hurwitz zeta function

The Euler–Maclaurin continuation `ζ(s, a)` is jointly holomorphic for `s ≠ 1` and
`Re a > 0`. Its derivative in the parameter is `-s ζ(s+1, a)` (DLMF 25.11.17).
Joint holomorphy also gives analyticity and continuity of its order derivatives, using
TauCeti’s finite-dimensional Cauchy integral theorem.
-/

@[expose] public section

open Complex Filter Set MeasureTheory intervalIntegral
open scoped Nat Real Topology

noncomputable section

namespace DLMF.Zeta

open DLMF.Hypergeometric (pochhammer pochhammer_succ pochhammer_zero)

/-- **Holomorphy of `ζ(s, z)` in `s ≠ 1`** for `z ≠ 0, -1, -2, …`. -/
theorem differentiableAt_hurwitzZetaComplex_of_add_natCast_ne_zero' {s₀ z : ℂ} (hs₀ : s₀ ≠ 1)
    (hz : ∀ n : ℕ, z + n ≠ 0) :
    DifferentiableAt ℂ (fun s => DLMF.Zeta.hurwitzZetaComplex s z) s₀ :=
  differentiableAt_hurwitzZetaComplex_of_add_ne_zero hs₀ hz

/-- At `w`, the function `(fun x => (x + n) ^ c)` has derivative `(c * (w + n) ^ (c - 1))`. -/
private lemma hasDerivAt_add_cpow {w c : ℂ} (n : ℂ) (h : w + n ∈ slitPlane) :
    HasDerivAt (fun x => (x + n) ^ c) (c * (w + n) ^ (c - 1)) w := by
  simpa using ((hasDerivAt_id w).add_const n).cpow_const (c := c) h

/-- Identity under the stated parameter and domain assumptions:
`eulerMaclaurinCoeff s k * (-s - (2 * k + 1)) = -s * eulerMaclaurinCoeff (s + 1) k`. -/
private lemma eulerMaclaurinCoeff_mul_eq (s : ℂ) (k : ℕ) :
    eulerMaclaurinCoeff s k * (-s - (2 * k + 1)) = -s * eulerMaclaurinCoeff (s + 1) k := by
  have h : pochhammer s (2 * k + 1 + 1) = s * pochhammer (s + 1) (2 * k + 1) := by
    simp [pochhammer, ascPochhammer_succ_left, Polynomial.eval_comp]
  rw [pochhammer_succ] at h
  simp only [eulerMaclaurinCoeff]
  push_cast at h ⊢
  linear_combination (-(bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ)) * h

/-- The `z`-derivative of the Euler–Maclaurin sequence: `∂_z E_N(s, z) = -s E_N(s+1, z)`. -/
private lemma hasDerivAt_eulerMaclaurinSeq_param (M : ℕ) {s w : ℂ} (hs : s ≠ 0) (hs1' : s ≠ 1)
    (hw : 0 < w.re)
    (N : ℕ) :
    HasDerivAt (fun x => eulerMaclaurinSeq M s x N) (-s * eulerMaclaurinSeq M (s + 1) w N) w := by
  have hsl : ∀ n : ℕ, w + n ∈ slitPlane := fun n =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]))
  have h1 := HasDerivAt.fun_sum (u := Finset.range N)
    (fun n _ => hasDerivAt_add_cpow (c := -s) (n : ℂ) (hsl n))
  have h2 := (hasDerivAt_add_cpow (c := 1 - s) (N : ℂ) (hsl N)).div_const (s - 1)
  have h3 := (hasDerivAt_add_cpow (c := -s) (N : ℂ) (hsl N)).div_const 2
  have h4 := HasDerivAt.fun_sum (u := Finset.range M)
    (fun k _ => (hasDerivAt_add_cpow (c := -s - (2 * k + 1)) (N : ℂ) (hsl N)).const_mul
      (eulerMaclaurinCoeff s k))
  have := h1.add ((h2.add h3).add h4)
  unfold eulerMaclaurinSeq eulerMaclaurinTail
  convert this using 1
  have hs1 : (s + 1 - 1) = s := by ring
  rw [hs1, show 1 - (s + 1) = -s by ring]
  simp only [mul_add, Finset.mul_sum]
  have hs2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1'
  congr 1
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [show -(s + 1) = -s - 1 by ring]
  congr 1
  · rw [show -(s + 1) = -s - 1 by ring, show 1 - s - 1 = -s by ring]
    field_simp
    ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [show -(s + 1) - (2 * (k : ℂ) + 1) = -s - (2 * k + 1) - 1 by ring,
      ← mul_assoc (eulerMaclaurinCoeff s k), eulerMaclaurinCoeff_mul_eq]
    ring

/-- Each term of the Euler–Maclaurin sequence is holomorphic in `z` on `Re z > 0`. -/
private lemma differentiableAt_eulerMaclaurinSeq_param (M : ℕ) (s : ℂ) {w : ℂ}
    (hw : 0 < w.re) (N : ℕ) :
    DifferentiableAt ℂ (fun x => eulerMaclaurinSeq M s x N) w := by
  have hsl : ∀ n : ℕ, w + n ∈ slitPlane := fun n =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]))
  unfold eulerMaclaurinSeq eulerMaclaurinTail
  refine DifferentiableAt.add (DifferentiableAt.fun_sum fun n _ =>
    (hasDerivAt_add_cpow (n : ℂ) (hsl n)).differentiableAt) ?_
  refine DifferentiableAt.add (DifferentiableAt.add ?_ ?_) (DifferentiableAt.fun_sum fun k _ => ?_)
  · exact (hasDerivAt_add_cpow (N : ℂ) (hsl N)).differentiableAt.div_const _
  · exact (hasDerivAt_add_cpow (N : ℂ) (hsl N)).differentiableAt.div_const _
  · exact (hasDerivAt_add_cpow (N : ℂ) (hsl N)).differentiableAt.const_mul _

/-- Uniform convergence in `z` on a closed disk inside `Re z > 0`, for fixed `s ≠ 1`. -/
private lemma tendstoUniformlyOn_eulerMaclaurinSeq_param {s : ℂ} (a₀ : ℂ) (hs : s ≠ 1) :
    TendstoUniformlyOn (fun N (a : ℂ) => eulerMaclaurinSeq (⌈|s.re|⌉₊ + 1) s a
        (⌈max (‖s‖ + 1) (‖a₀‖ + a₀.re / 2)⌉₊ + 1 + N))
      (DLMF.Zeta.hurwitzZetaComplex s) atTop (Metric.closedBall a₀ (a₀.re / 2)) := by
  set r := a₀.re / 2
  set R : ℝ := max (‖s‖ + 1) (‖a₀‖ + r)
  have hR : 0 ≤ R := le_max_of_le_left (by positivity)
  have hσ : 0 < s.re + 2 * ((⌈|s.re|⌉₊ + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil |s.re|
    have := neg_abs_le s.re
    push_cast; linarith
  have hK : ∀ q ∈ (({s} : Set ℂ) ×ˢ Metric.closedBall a₀ r), ‖q.1‖ ≤ R ∧ ‖q.2‖ ≤ R ∧
      s.re ≤ q.1.re ∧ q.1 ≠ 1 := by
    rintro ⟨t, a⟩ ⟨ht, ha⟩
    simp only [Set.mem_singleton_iff] at ht
    subst ht
    rw [Metric.mem_closedBall, dist_eq_norm] at ha
    refine ⟨by simp only [R]; exact le_max_of_le_left (by linarith), ?_, le_rfl, hs⟩
    calc ‖a‖ = ‖(a - a₀) + a₀‖ := by ring_nf
      _ ≤ ‖a - a₀‖ + ‖a₀‖ := norm_add_le _ _
      _ ≤ R := by simp only [R]; exact le_max_of_le_right (by linarith)
  have hU := (tendstoUniformlyOn_eulerMaclaurinSeq_hurwitzZetaComplex hR hσ hK).comp
      (fun a : ℂ => (s, a))
  have hpre : (fun a : ℂ => (s, a)) ⁻¹' (({s} : Set ℂ) ×ˢ Metric.closedBall a₀ r) =
      Metric.closedBall a₀ r := by
    ext a; simp
  rw [hpre] at hU
  exact hU

/-- Estimate under the stated parameter and domain assumptions: `0 < a.re`. -/
private lemma re_pos_of_mem_ball_half_re {a₀ a : ℂ} (ha₀ : 0 < a₀.re)
    (ha : a ∈ Metric.ball a₀ (a₀.re / 2)) :
    0 < a.re := by
  rw [Metric.mem_ball, dist_eq_norm] at ha
  have := abs_re_le_norm (a - a₀)
  simp only [sub_re] at this
  linarith [neg_abs_le (a.re - a₀.re)]

/-- **Holomorphy of `ζ(s, a)` in `a`** on `Re a > 0`, for fixed `s ≠ 1`. -/
theorem differentiableOn_hurwitzZetaComplex_param' {s : ℂ} (hs : s ≠ 1) :
    DifferentiableOn ℂ (DLMF.Zeta.hurwitzZetaComplex s) {a | 0 < a.re} := by
  intro a₀ ha₀
  have ha₀' : 0 < a₀.re := ha₀
  have hr : 0 < a₀.re / 2 := by linarith
  have hU := ((tendstoUniformlyOn_eulerMaclaurinSeq_param a₀ hs).mono
    Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn
  have hdiff := hU.differentiableOn (Eventually.of_forall fun N a ha =>
    (differentiableAt_eulerMaclaurinSeq_param _ s (re_pos_of_mem_ball_half_re ha₀' ha)
        _).differentiableWithinAt)
    Metric.isOpen_ball
  exact (hdiff.differentiableAt (Metric.ball_mem_nhds _ hr)).differentiableWithinAt

/-- **`∂ζ(s, a)/∂a = -s ζ(s+1, a)`** (DLMF 25.11.17) for `s ≠ 0, 1`, `Re a > 0`. -/
theorem hasDerivAt_hurwitzZetaComplex_param' {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) {a₀ : ℂ}
    (ha₀ : 0 < a₀.re) :
    HasDerivAt (DLMF.Zeta.hurwitzZetaComplex s)
      (-s * DLMF.Zeta.hurwitzZetaComplex (s + 1) a₀) a₀ := by
  have hr : 0 < a₀.re / 2 := by linarith
  have hU := ((tendstoUniformlyOn_eulerMaclaurinSeq_param a₀ hs1).mono
    Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn
  have hF : ∀ᶠ N in atTop, DifferentiableOn ℂ (fun a => eulerMaclaurinSeq (⌈|s.re|⌉₊ + 1) s a
      (⌈max (‖s‖ + 1) (‖a₀‖ + a₀.re / 2)⌉₊ + 1 + N)) (Metric.ball a₀ (a₀.re / 2)) :=
    Eventually.of_forall fun N a ha =>
      (differentiableAt_eulerMaclaurinSeq_param _ s (re_pos_of_mem_ball_half_re ha₀ ha)
          _).differentiableWithinAt
  have hdiff := hU.differentiableOn hF Metric.isOpen_ball
  have hD := (hU.deriv hF Metric.isOpen_ball).tendsto_at (Metric.mem_ball_self hr)
  have hD' : Tendsto (fun N => -s * eulerMaclaurinSeq (⌈|s.re|⌉₊ + 1) (s + 1) a₀
      (⌈max (‖s‖ + 1) (‖a₀‖ + a₀.re / 2)⌉₊ + 1 + N)) atTop
      (𝓝 (-s * DLMF.Zeta.hurwitzZetaComplex (s + 1) a₀)) := by
    have hs1' : s + 1 ≠ 1 := by intro h; exact hs0 (by linear_combination h)
    have hM : 0 < (s + 1).re + 2 * ((⌈|s.re|⌉₊ + 1 : ℕ) : ℝ) := by
      have := Nat.le_ceil |s.re|
      have := neg_abs_le s.re
      simp; linarith
    have hT : Tendsto (fun N : ℕ => ⌈max (‖s‖ + 1) (‖a₀‖ + a₀.re / 2)⌉₊ + 1 + N) atTop atTop :=
      tendsto_atTop_mono (fun N => Nat.le_add_left N _) tendsto_id
    exact ((tendsto_eulerMaclaurinSeq_hurwitzZetaComplex (z := a₀) hs1' hM).comp hT).const_mul (-s)
  have heq : (fun N => (deriv ∘ fun N a => eulerMaclaurinSeq (⌈|s.re|⌉₊ + 1) s a
      (⌈max (‖s‖ + 1) (‖a₀‖ + a₀.re / 2)⌉₊ + 1 + N)) N a₀) =
      fun N => -s * eulerMaclaurinSeq (⌈|s.re|⌉₊ + 1) (s + 1) a₀
        (⌈max (‖s‖ + 1) (‖a₀‖ + a₀.re / 2)⌉₊ + 1 + N) := by
    funext N
    exact (hasDerivAt_eulerMaclaurinSeq_param _ hs0 hs1 ha₀ _).deriv
  have hval : deriv (DLMF.Zeta.hurwitzZetaComplex s) a₀ =
      -s * DLMF.Zeta.hurwitzZetaComplex (s + 1) a₀ := by
    refine tendsto_nhds_unique ?_ hD'
    rw [← heq]
    exact hD
  rw [← hval]
  exact (hdiff.differentiableAt (Metric.ball_mem_nhds _ hr)).hasDerivAt


/-- Each Euler–Maclaurin approximant is jointly continuous away from the pole and cut. -/
private lemma continuousAt_eulerMaclaurinSeq_joint (M N : ℕ) {p : ℂ × ℂ}
    (hs : p.1 ≠ 1) (ha : 0 < p.2.re) :
    ContinuousAt (fun q : ℂ × ℂ => eulerMaclaurinSeq M q.1 q.2 N) p := by
  have hf : ContinuousAt (fun q : ℂ × ℂ => q.1) p := continuous_fst.continuousAt
  have hg : ContinuousAt (fun q : ℂ × ℂ => q.2) p := continuous_snd.continuousAt
  have hsl : ∀ n : ℕ, p.2 + n ∈ slitPlane := fun n =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (by
      simp only [add_re, natCast_re]
      positivity))
  unfold eulerMaclaurinSeq eulerMaclaurinTail eulerMaclaurinCoeff
  refine ContinuousAt.add (tendsto_finsetSum _ fun n _ =>
    (hg.add_const (n : ℂ)).cpow hf.neg (hsl n)) ?_
  refine ContinuousAt.add (ContinuousAt.add ?_ ?_)
    (tendsto_finsetSum _ fun k _ => ?_)
  · exact ((hg.add_const (N : ℂ)).cpow (continuousAt_const.sub hf) (hsl N)).div
      (hf.sub continuousAt_const) (sub_ne_zero.mpr hs)
  · exact ((hg.add_const (N : ℂ)).cpow hf.neg (hsl N)).div_const _
  · exact (((differentiableAt_pochhammer _ p.1).continuousAt.comp hf).const_mul _).mul
      ((hg.add_const (N : ℂ)).cpow (hf.neg.sub continuousAt_const) (hsl N))

/-- Joint continuity of `ζ(s, a)` for `s ≠ 1` and `Re a > 0`. -/
theorem continuousAt_hurwitzZetaComplex_joint {s a : ℂ} (hs : s ≠ 1) (ha : 0 < a.re) :
    ContinuousAt (fun p : ℂ × ℂ => hurwitzZetaComplex p.1 p.2) (s, a) := by
  let R : ℝ := ‖s‖ + ‖a‖ + 2
  let σ : ℝ := s.re - 1
  let M : ℕ := ⌈|s.re|⌉₊ + 1
  let K : Set (ℂ × ℂ) := {p | ‖p.1‖ < R ∧ ‖p.2‖ < R ∧ σ < p.1.re ∧
    p.1 ≠ 1 ∧ 0 < p.2.re}
  have hKo : IsOpen K := by
    exact (isOpen_lt (f := fun p : ℂ × ℂ => ‖p.1‖) (g := fun _ => R)
      (continuous_norm.comp continuous_fst) continuous_const).inter
      ((isOpen_lt (f := fun p : ℂ × ℂ => ‖p.2‖) (g := fun _ => R)
        (continuous_norm.comp continuous_snd) continuous_const).inter
        ((isOpen_lt (f := fun _ : ℂ × ℂ => σ) (g := fun p => p.1.re)
          continuous_const (continuous_re.comp continuous_fst)).inter
          ((isOpen_ne_fun (f := fun p : ℂ × ℂ => p.1) (g := fun _ => 1)
            continuous_fst continuous_const).inter
            (isOpen_lt continuous_const (continuous_re.comp continuous_snd)))))
  have hp : (s, a) ∈ K := by
    exact ⟨by dsimp [R]; linarith [norm_nonneg a],
      by dsimp [R]; linarith [norm_nonneg s], by dsimp [σ]; linarith,
      hs, ha⟩
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hσ : 0 < σ + 2 * M := by
    have := Nat.le_ceil |s.re|
    have := neg_abs_le s.re
    dsimp [σ, M]
    push_cast
    linarith
  have hconv := tendstoUniformlyOn_eulerMaclaurinSeq_hurwitzZetaComplex
    (K := K) hR hσ (fun p hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.1.le, hp.2.2.2.1⟩)
  have hc := hconv.continuousOn (Eventually.of_forall fun N p hp =>
    (continuousAt_eulerMaclaurinSeq_joint M _ hp.2.2.2.1
      hp.2.2.2.2).continuousWithinAt).frequently
  exact hc.continuousAt (hKo.mem_nhds hp)

/-- Joint holomorphy of `ζ(s, a)` for `s ≠ 1` and `Re a > 0`. -/
theorem differentiableOn_hurwitzZetaComplex_joint :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => hurwitzZetaComplex p.1 p.2)
      {p | p.1 ≠ 1 ∧ 0 < p.2.re} := by
  have hU : IsOpen {p : ℂ × ℂ | p.1 ≠ 1 ∧ 0 < p.2.re} :=
    (isOpen_ne_fun continuous_fst continuous_const).inter
      (isOpen_lt continuous_const (continuous_re.comp continuous_snd))
  refine Complex.differentiableOn_prod_of_continuousOn_of_separately hU
    (fun p hp => (continuousAt_hurwitzZetaComplex_joint hp.1 hp.2).continuousWithinAt)
    (fun p hp => differentiableAt_hurwitzZetaComplex_of_add_ne_zero hp.1 ?_) ?_
  · intro n hn
    have hpos : 0 < (p.2 + n).re := by
      simp only [add_re, natCast_re]
      linarith [hp.2, (n.cast_nonneg : (0 : ℝ) ≤ n)]
    simp [hn] at hpos
  · intro p hp
    exact (differentiableOn_hurwitzZetaComplex_param' hp.1).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds hp.2)

/-- Joint analyticity of `ζ(s, a)` for `s ≠ 1` and `Re a > 0`. -/
theorem analyticAt_hurwitzZetaComplex_joint {s a : ℂ} (hs : s ≠ 1) (ha : 0 < a.re) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => hurwitzZetaComplex p.1 p.2) (s, a) := by
  exact (differentiableOn_hurwitzZetaComplex_joint.analyticOnNhd_of_finiteDimensional
    ((isOpen_ne_fun continuous_fst continuous_const).inter
      (isOpen_lt continuous_const (continuous_re.comp continuous_snd)))) (s, a) ⟨hs, ha⟩

/-- The order derivative of `ζ(s, a)` is jointly analytic away from its pole and cut. -/
theorem analyticAt_deriv_hurwitzZetaComplex_joint {s a : ℂ} (hs : s ≠ 1)
    (ha : 0 < a.re) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => deriv (fun z => hurwitzZetaComplex z p.2) p.1)
      (s, a) :=
  Complex.analyticAt_deriv_fst (analyticAt_hurwitzZetaComplex_joint hs ha)

/-- Differentiating the order derivative of `ζ(s, a)` in `a` commutes the two derivatives. -/
theorem hasDerivAt_deriv_hurwitzZetaComplex_param {s a : ℂ} (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) (ha : 0 < a.re) :
    HasDerivAt (fun w => deriv (fun z => hurwitzZetaComplex z w) s)
      (-hurwitzZetaComplex (s + 1) a -
        s * deriv (fun z => hurwitzZetaComplex z a) (s + 1)) a := by
  have hA := analyticAt_deriv_hurwitzZetaComplex_joint hs1 ha
  have hd : DifferentiableAt ℂ (fun w => deriv (fun z => hurwitzZetaComplex z w) s) a :=
    hA.differentiableAt.comp a (differentiableAt_const s |>.prodMk differentiableAt_id)
  have heq : (fun z => deriv (hurwitzZetaComplex z) a) =ᶠ[𝓝 s]
      (fun z => -z * hurwitzZetaComplex (z + 1) a) := by
    filter_upwards [(isOpen_ne.mem_nhds hs0), (isOpen_ne.mem_nhds hs1)] with z hz0 hz1
    exact (hasDerivAt_hurwitzZetaComplex_param' hz0 hz1 ha).deriv
  have hz : ∀ n : ℕ, a + n ≠ 0 := by
    intro n hn
    have hpos : 0 < (a + n).re := by
      simp only [add_re, natCast_re]
      positivity
    simp [hn] at hpos
  have hs : s + 1 ≠ 1 := by simpa using hs0
  have hD := ((hasDerivAt_id s).neg).mul
    ((differentiableAt_hurwitzZetaComplex_of_add_ne_zero hs hz).hasDerivAt.comp s
      ((hasDerivAt_id s).add_const 1))
  change HasDerivAt (fun z : ℂ => -z * hurwitzZetaComplex (z + 1) a)
    (-1 * hurwitzZetaComplex (s + 1) a +
      -s * (deriv (fun z => hurwitzZetaComplex z a) (s + 1) * 1)) s at hD
  have hcomm := Complex.deriv_snd_deriv_fst_comm
    (analyticAt_hurwitzZetaComplex_joint hs1 ha)
  have hval : deriv (fun w => deriv (fun z => hurwitzZetaComplex z w) s) a =
      -hurwitzZetaComplex (s + 1) a -
        s * deriv (fun z => hurwitzZetaComplex z a) (s + 1) := by
    rw [hcomm, heq.deriv_eq, hD.deriv]
    ring
  exact hval ▸ hd.hasDerivAt

end DLMF.Zeta
