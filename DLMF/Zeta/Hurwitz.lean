/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.ZerosIntegrals
public import DLMF.Gamma.PolygammaHurwitz
public import DLMF.Zeta.Q25bLerchContinuation
public import DLMF.Zeta.R25bHurwitzContinuation
public import DLMF.Zeta.S25bDirichletTest
public import DLMFMathlib.Analysis.EulerMaclaurin
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.LSeries.ZMod
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.RingTheory.Binomial
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Hurwitz zeta function: definition, Euler–Maclaurin forms, special values, derivatives
(DLMF §25.11(i)–(vi))

## Two Hurwitz zeta functions

* Mathlib's `HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s` is the meromorphic continuation in `s`
  of `∑ (n + a)^{-s}` **for real `0 ≤ a ≤ 1`**; its parameter lives in `ℝ/ℤ`, so it is periodic in
  `a` and agrees with DLMF's `ζ(s, a)` only for `0 < a ≤ 1` (and `hurwitzZeta 0 = ζ(s, 1)`).
* DLMF's `ζ(s, a)` (25.11.1) is defined for complex `a ≠ 0, -1, -2, …` with principal powers. The
  project's definition is `DLMF.Confluent.hurwitzZetaComplex s a`
  (`DLMF/IncompleteGamma/ZerosIntegrals.lean`, made for DLMF 8.15.2), the limit as `N → ∞` of the
  Euler–Maclaurin form `∑_{n<N} (a+n)^{-s} + (a+N)^{1-s}/(s-1) + (a+N)^{-s}/2 + ∑_{k<M} …`
  with `M` large enough for `Re s`. It is reused here, not redefined. Its bridge to Mathlib for
  `0 < a ≤ 1` is `DLMF.Zeta.r25b_hurwitzZetaComplex_mathlib` (a proved form of the admitted
  `DLMF.Confluent.hurwitzZetaComplex_mathlib`).

Convention used below: a DLMF formula whose parameter range is contained in `0 < a ≤ 1` is stated
with Mathlib's `hurwitzZeta` (this is DLMF's function there); a formula for complex `a` or for
unbounded real `a > 0` is stated with `hurwitzZetaComplex`.

The existence of the defining limit (`tendsto_hurwitzZetaComplex`, the content of the continuation
statement in §25.11(i)) is proved in `DLMF.Zeta.R25bHurwitzContinuation` by the one-interval
Euler–Maclaurin formula; the recurrences 25.11.3 and 25.11.4 follow from it.
-/

@[expose] public section

open Complex Filter Set MeasureTheory HurwitzZeta
open scoped Nat Real Topology

noncomputable section

namespace DLMF.Zeta

open DLMF.Confluent (hurwitzZetaComplex)
open DLMF.Hypergeometric (poch)

/-! ### §25.11(i) Definition -/

/-- The Euler–Maclaurin sequence whose limit defines `hurwitzZetaComplex s z`. -/
def z25b_emSeq (s z : ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, (z + n) ^ (-s)) + (z + N) ^ (1 - s) / (s - 1) + (z + N) ^ (-s) / 2 +
    ∑ k ∈ Finset.range (⌈(1 - s.re) / 2⌉₊ + 1),
      (bernoulli (2 * k + 2) : ℂ) / (2 * k + 2).factorial * poch s (2 * k + 1) *
        (z + N) ^ (-s - (2 * k + 1))

lemma z25b_hurwitzZetaComplex_eq_limUnder (s z : ℂ) :
    hurwitzZetaComplex s z = limUnder atTop (z25b_emSeq s z) := rfl

/-- Shifting the Euler–Maclaurin sequence: `E_{N+1}(z) = z^{-s} + E_N(z+1)`. -/
lemma z25b_emSeq_succ (s z : ℂ) (N : ℕ) :
    z25b_emSeq s z (N + 1) = z ^ (-s) + z25b_emSeq s (z + 1) N := by
  unfold z25b_emSeq
  rw [Finset.sum_range_succ']
  have h1 : z + ((N + 1 : ℕ) : ℂ) = z + 1 + (N : ℂ) := by push_cast; ring
  have h2 : ∀ n : ℕ, z + ((n + 1 : ℕ) : ℂ) = z + 1 + (n : ℂ) := fun n => by push_cast; ring
  simp only [h1, h2, Nat.cast_zero, add_zero]
  ring

/-- `(z + N)^w → 0` as `N → ∞`, for `Re w < 0`. -/
lemma q25b_tendsto_cpow_nat (z : ℂ) {w : ℂ} (hw : w.re < 0) :
    Tendsto (fun N : ℕ => (z + N) ^ w) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => ‖z + N‖) atTop atTop := by
    refine tendsto_atTop_mono (fun N => ?_)
      (tendsto_atTop_add_const_right _ (-‖z‖) tendsto_natCast_atTop_atTop)
    have := norm_sub_norm_le (N : ℂ) (-z)
    simp only [Complex.norm_natCast, norm_neg, sub_neg_eq_add] at this
    rw [add_comm z]; linarith
  have h2 : Tendsto (fun N : ℕ => ‖z + N‖ ^ w.re) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := -w.re) (by linarith)).comp h1
    simpa [Function.comp_def] using this
  refine squeeze_zero_norm (fun N => ?_) (by simpa using h2.mul_const (Real.exp (π * |w.im|)))
  refine (norm_cpow_le _ _).trans ?_
  rw [div_eq_mul_inv, ← Real.exp_neg]
  gcongr
  have harg := abs_arg_le_pi (z + N)
  calc -(arg (z + N) * w.im) ≤ |arg (z + N)| * |w.im| := by
        rw [← abs_mul]; exact neg_le_abs _
    _ ≤ π * |w.im| := by gcongr

/-- For `Re s > 1` the Euler–Maclaurin sequence converges to the sum of the series. -/
lemma q25b_tendsto_emSeq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) (a : ℂ) :
    Tendsto (z25b_emSeq s a) atTop (𝓝 (∑' n : ℕ, 1 / (a + n) ^ s)) := by
  have hsum := q25b_summable_one_div_cpow hs a
  have hP : Tendsto (fun N => ∑ n ∈ Finset.range N, (a + n) ^ (-s)) atTop
      (𝓝 (∑' n : ℕ, 1 / (a + n) ^ s)) := by
    have := hsum.hasSum.tendsto_sum_nat
    simpa only [cpow_neg, one_div] using this
  have h1 : Tendsto (fun N : ℕ => (a + N) ^ (1 - s) / (s - 1)) atTop (𝓝 0) := by
    simpa using (q25b_tendsto_cpow_nat a (w := 1 - s) (by simp; linarith)).div_const (s - 1)
  have h2 : Tendsto (fun N : ℕ => (a + N) ^ (-s) / 2) atTop (𝓝 0) := by
    simpa using (q25b_tendsto_cpow_nat a (w := -s) (by simp; linarith)).div_const 2
  have h3 : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (⌈(1 - s.re) / 2⌉₊ + 1),
      (bernoulli (2 * k + 2) : ℂ) / (2 * k + 2).factorial * poch s (2 * k + 1) *
        (a + N) ^ (-s - (2 * k + 1))) atTop (𝓝 0) := by
    rw [show (0 : ℂ) = ∑ k ∈ Finset.range (⌈(1 - s.re) / 2⌉₊ + 1), 0 by simp]
    refine tendsto_finsetSum _ fun k _ => ?_
    simpa using (q25b_tendsto_cpow_nat a (w := -s - (2 * k + 1))
      (by simp; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])).const_mul _
  have := ((hP.add h1).add h2).add h3
  simp only [add_zero] at this
  exact this

/-- **Continuation of `ζ(s, a)`** (DLMF §25.11(i), first paragraph after 25.11.1): for `s ≠ 1` and
`a ≠ 0, -1, -2, …` the Euler–Maclaurin limit defining `hurwitzZetaComplex s a` exists. -/
@[dlmf 25.11.i]
theorem tendsto_hurwitzZetaComplex {s a : ℂ} (hs : s ≠ 1) (ha : ∀ m : ℕ, a ≠ -m) :
    Tendsto (z25b_emSeq s a) atTop (𝓝 (hurwitzZetaComplex s a)) := by
  have _ := ha
  have h : z25b_emSeq s a = r25b_emSeq (⌈(1 - s.re) / 2⌉₊ + 1) s a := by
    funext N
    unfold z25b_emSeq r25b_emSeq r25b_emF r25b_emC
    ring
  rw [h]
  refine r25b_tendsto_hurwitzZetaComplex hs ?_
  have := Nat.le_ceil ((1 - s.re) / 2)
  push_cast; linarith

/-- **Meromorphy in `s`** (DLMF §25.11(i)): for `a ≠ 0, -1, -2, …`, `ζ(s, a)` is holomorphic in `s`
on `ℂ \ {1}`. -/
@[dlmf 25.11.i]
theorem differentiableAt_hurwitzZetaComplex {s a : ℂ} (hs : s ≠ 1) (ha : ∀ m : ℕ, a ≠ -m) :
    DifferentiableAt ℂ (fun t => hurwitzZetaComplex t a) s :=
  r25b_differentiableAt_hurwitzZetaComplex hs fun n h => ha n (by linear_combination h)

/-- **The pole at `s = 1`** (DLMF §25.11(i)): a simple pole with residue `1`. -/
@[dlmf 25.11.i]
theorem hurwitzZetaComplex_residue_one {a : ℂ} (ha : ∀ m : ℕ, a ≠ -m) :
    Tendsto (fun s => (s - 1) * hurwitzZetaComplex s a) (𝓝[≠] 1) (𝓝 1) :=
  r25b_hurwitzZetaComplex_residue_one fun n h => ha n (by linear_combination h)

/-- **Analyticity in `a`** (DLMF §25.11(i)): for fixed `s ≠ 1`, `ζ(s, a)` is analytic in the
half-plane `Re a > 0`. -/
@[dlmf 25.11.i]
theorem differentiableOn_hurwitzZetaComplex_param {s : ℂ} (hs : s ≠ 1) :
    DifferentiableOn ℂ (hurwitzZetaComplex s) {a | 0 < a.re} :=
  r25b_differentiableOn_hurwitzZetaComplex_param hs

/-- **Defining series** (DLMF 25.11.1) for complex `a ≠ 0, -1, -2, …` and `Re s > 1`, principal
powers. (Mathlib's real-parameter case `0 ≤ a ≤ 1` is
`HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re`.) -/
@[dlmf 25.11.E1]
theorem hasSum_hurwitzZetaComplex {s a : ℂ} (hs : 1 < s.re) (ha : ∀ m : ℕ, a ≠ -m) :
    HasSum (fun n : ℕ => 1 / (n + a) ^ s) (hurwitzZetaComplex s a) := by
  have _ := ha
  rw [z25b_hurwitzZetaComplex_eq_limUnder, (q25b_tendsto_emSeq_of_one_lt_re hs a).limUnder_eq]
  simp_rw [add_comm (_ : ℂ) a]
  exact (q25b_summable_one_div_cpow hs a).hasSum

/-- **`ζ(s, 1) = ζ(s)`** (DLMF 25.11.2) for `s ≠ 1`, for the complex-parameter function (from the
bridge to Mathlib). -/
@[dlmf 25.11.E2]
theorem hurwitzZetaComplex_one {s : ℂ} (hs : s ≠ 1) :
    hurwitzZetaComplex s 1 = riemannZeta s := by
  have h := r25b_hurwitzZetaComplex_mathlib (x := 1) one_pos le_rfl hs
  rw [Complex.ofReal_one] at h
  rw [h, AddCircle.coe_period, hurwitzZeta_zero]

/-- **Recurrence** `ζ(s, a) = ζ(s, a + 1) + a^{-s}` (DLMF 25.11.3), `s ≠ 1`, `a ≠ 0, -1, -2, …`. -/
@[dlmf 25.11.E3]
theorem hurwitzZetaComplex_eq_add_one {s a : ℂ} (hs : s ≠ 1) (ha : ∀ m : ℕ, a ≠ -m) :
    hurwitzZetaComplex s a = hurwitzZetaComplex s (a + 1) + a ^ (-s) := by
  have ha1 : ∀ m : ℕ, a + 1 ≠ -m := fun m h => ha (m + 1) (by push_cast; linear_combination h)
  have h1 := (tendsto_add_atTop_iff_nat 1).mpr (tendsto_hurwitzZetaComplex hs ha)
  have h2 := ((tendsto_hurwitzZetaComplex hs ha1).const_add (a ^ (-s)))
  simp_rw [← z25b_emSeq_succ] at h2
  rw [tendsto_nhds_unique h1 h2, add_comm]

/-- **Recurrence** `ζ(s, a) = ζ(s, a + m) + ∑_{n=0}^{m-1} (n + a)^{-s}` (DLMF 25.11.4), `s ≠ 1`,
`a ≠ 0, -1, -2, …` (valid also for `m = 0`). -/
@[dlmf 25.11.E4]
theorem hurwitzZetaComplex_eq_add_nat {s a : ℂ} (hs : s ≠ 1) (ha : ∀ m : ℕ, a ≠ -m) (m : ℕ) :
    hurwitzZetaComplex s a =
      hurwitzZetaComplex s (a + m) + ∑ n ∈ Finset.range m, 1 / ((n : ℂ) + a) ^ s := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ham : ∀ j : ℕ, a + m ≠ -j := fun j h => ha (j + m) (by push_cast; linear_combination h)
    rw [ih, hurwitzZetaComplex_eq_add_one hs ham, Finset.sum_range_succ, cpow_neg, one_div]
    push_cast
    ring_nf

/-! ### §25.11(iii) Representations by the Euler–Maclaurin formula -/

/-- The tail of the Euler–Maclaurin sequence as a convergent series of increments. -/
lemma r25b_hasSum_emD {M : ℕ} {s : ℂ} (hs : s ≠ 1) (hM : 0 < s.re + 2 * M) (z : ℂ) (N₀ : ℕ) :
    HasSum (fun m : ℕ => r25b_emD M s (z + (N₀ + m : ℕ)))
      (hurwitzZetaComplex s z - r25b_emSeq M s z N₀) := by
  have hK : ∀ q ∈ ({(s, z)} : Set (ℂ × ℂ)), ‖q.1‖ ≤ max ‖s‖ ‖z‖ ∧ ‖q.2‖ ≤ max ‖s‖ ‖z‖ ∧
      s.re ≤ q.1.re ∧ q.1 ≠ 1 := by
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨le_max_left _ _, le_max_right _ _, le_rfl, hs⟩
  obtain ⟨u, hu, -, hb⟩ := r25b_exists_summable_bound_emD (le_max_of_le_left (norm_nonneg _)) hM hK
  set c := ⌈max ‖s‖ ‖z‖⌉₊ + 1
  set f : ℕ → ℂ := fun m => r25b_emD M s (z + m)
  have h1 : Summable fun m => f (m + c) :=
    Summable.of_norm_bounded hu fun m => by
      simpa [f, add_comm] using hb m (s, z) rfl
  have h2 : Summable f := (summable_nat_add_iff c).mp h1
  have h3 : Summable fun m => f (m + N₀) := (summable_nat_add_iff N₀).mpr h2
  have h3' : Summable fun m : ℕ => r25b_emD M s (z + (N₀ + m : ℕ)) := by
    refine h3.congr fun m => ?_
    simp only [f]; push_cast; ring_nf
  rw [h3'.hasSum_iff_tendsto_nat]
  have hT : Tendsto (fun N : ℕ => N₀ + N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_add_left N _) tendsto_id
  have := ((r25b_tendsto_hurwitzZetaComplex (z := z) hs hM).comp hT).sub_const
    (r25b_emSeq M s z N₀)
  refine this.congr fun N => ?_
  simp only [Function.comp_apply, r25b_emSeq_add]
  ring

/-- The Euler–Maclaurin increment at a real point as an integral against `B̃_{2M+1}`. -/
lemma r25b_emD_eq_integral (M : ℕ) {s : ℂ} (hs : s ≠ 1) {a : ℝ} (ha : 0 < a) (k : ℕ) :
    r25b_emD M s ((a : ℂ) + k) = -(poch s (2 * M + 1) / (2 * M + 1 : ℕ)!) *
      ∫ x in (k : ℝ)..(k + 1), ((periodicBernoulli (2 * M + 1) x : ℝ) : ℂ) /
        (((x + a : ℝ)) : ℂ) ^ (s + (2 * M + 1 : ℕ)) := by
  have hw : 0 < ((a : ℂ) + k).re := by simp; positivity
  rw [r25b_emD, r25b_emF_diff hs hw M]
  congr 1
  have hsub := intervalIntegral.integral_comp_add_right (a := 0) (b := 1)
    (fun x : ℝ => ((periodicBernoulli (2 * M + 1) x : ℝ) : ℂ) /
      (((x + a : ℝ)) : ℂ) ^ (s + (2 * M + 1 : ℕ))) (k : ℝ)
  simp only [zero_add] at hsub
  rw [show (k : ℝ) + 1 = 1 + k by ring, ← hsub]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t ht htI
  rw [uIoc_of_le zero_le_one] at htI
  have hfr : Int.fract (t + k) = t := by
    rw [Int.fract_add_natCast, Int.fract_eq_self.mpr ⟨htI.1.le, lt_of_le_of_ne htI.2 ht⟩]
  have hpos : 0 < t + k + a := by
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    linarith [htI.1]
  rw [periodicBernoulli, hfr, div_eq_mul_inv, ← cpow_neg, mul_comm]
  congr 2
  · push_cast; ring
  · ring

/-- Splitting an integral over `(N₀, ∞)` into unit intervals. -/
lemma r25b_hasSum_intervalIntegral {g : ℝ → ℂ} {N₀ : ℕ} (hg : IntegrableOn g (Ioi (N₀ : ℝ))) :
    HasSum (fun m : ℕ => ∫ x in ((N₀ + m : ℕ) : ℝ)..((N₀ + m : ℕ) + 1), g x)
      (∫ x in Ioi (N₀ : ℝ), g x) := by
  have hU : (⋃ m : ℕ, Ioc ((N₀ + m : ℕ) : ℝ) ((N₀ + m : ℕ) + 1)) = Ioi (N₀ : ℝ) := by
    ext x
    simp only [mem_iUnion, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨m, h1, -⟩
      have : (N₀ : ℝ) ≤ ((N₀ + m : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right N₀ m
      linarith
    · intro hx
      refine ⟨⌈x - N₀⌉₊ - 1, ?_, ?_⟩
      · have h1 : 1 ≤ ⌈x - N₀⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
          rw [Ne, Nat.ceil_eq_zero, not_le]; linarith)
        have h2 := Nat.ceil_lt_add_one (show 0 ≤ x - N₀ by linarith)
        rw [Nat.cast_add, Nat.cast_sub h1]
        push_cast
        linarith
      · have h1 : 1 ≤ ⌈x - N₀⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
          rw [Ne, Nat.ceil_eq_zero, not_le]; linarith)
        have h2 := Nat.le_ceil (x - N₀)
        rw [Nat.cast_add, Nat.cast_sub h1]
        push_cast
        linarith
  have hd : Pairwise
      (Function.onFun Disjoint fun m : ℕ => Ioc ((N₀ + m : ℕ) : ℝ) ((N₀ + m : ℕ) + 1)) := by
    intro m m' hmm'
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨h1, h2⟩ ⟨h3, h4⟩
    push_cast at h1 h2 h3 h4
    have h5 : (m : ℝ) < m' + 1 := by linarith
    have h6 : (m' : ℝ) < m + 1 := by linarith
    have : m < m' + 1 := by exact_mod_cast h5
    have : m' < m + 1 := by exact_mod_cast h6
    exact hmm' (by omega)
  have := hasSum_integral_iUnion (fun m => measurableSet_Ioc) hd (hU ▸ hg)
  rw [hU] at this
  refine this.congr_fun fun m => ?_
  rw [intervalIntegral.integral_of_le (by linarith)]

/-- Integrability of `B̃_p(x)/(x+a)^w` on `(c, ∞)` for `Re w > 1`, `a ≥ 0`, `c > 0`. -/
lemma r25b_integrableOn_periodicBernoulli_div (p : ℕ) {w : ℂ} (hw : 1 < w.re) {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => ((periodicBernoulli p x : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ w)
      (Ioi c) := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ y ∈ Icc (0 : ℝ) 1, ‖bernoulliFun p y‖ ≤ B :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc (continuous_bernoulliFun p).continuousOn
  have hint : IntegrableOn (fun x : ℝ => B * x ^ (-w.re)) (Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hc).const_mul B
  refine hint.mono' ?_ ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    refine Measurable.div (Complex.measurable_ofReal.comp (measurable_periodicBernoulli p)) ?_
    exact (Complex.measurable_ofReal.comp (measurable_id.add_const a)).pow_const w
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans hc hx
    have hxa : 0 < x + a := by linarith
    rw [norm_div, Complex.norm_real, norm_cpow_eq_rpow_re_of_pos hxa, div_eq_mul_inv,
      ← Real.rpow_neg hxa.le]
    refine mul_le_mul (hB _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩)
      (Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)) (by positivity)
      ((norm_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩))

/-- `C(s + n - 1, n) = (s)_n / n!`. -/
lemma r25b_choose_eq_poch (s : ℂ) (n : ℕ) :
    Ring.choose (s + n - 1) n = poch s n / n ! := by
  have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [Ring.choose, show s + n - 1 - n + 1 = s by ring, eq_div_iff hf, mul_comm,
    ← nsmul_eq_mul, Ring.factorial_nsmul_multichoose_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval]


/-- Integrability of `f(x)/(x+a)^w` on `(c, ∞)` for bounded measurable real `f`, `Re w > 1`,
`a > 0`, `c ≥ 0`. -/
lemma r25b_integrableOn_bdd_div_cpow {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) {w : ℂ} (hw : 1 < w.re) {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    IntegrableOn (fun x : ℝ => ((f x : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ w) (Ioi c) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hmeas : Measurable fun x : ℝ => ((f x : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ w :=
    (Complex.measurable_ofReal.comp hf).div
      ((Complex.measurable_ofReal.comp (measurable_id.add_const a)).pow_const w)
  have hnorm : ∀ x, c ≤ x → ‖((f x : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ w‖ ≤
      B * (x + a) ^ (-w.re) := by
    intro x hx
    have hxa : 0 < x + a := by linarith
    rw [norm_div, Complex.norm_real, norm_cpow_eq_rpow_re_of_pos hxa, div_eq_mul_inv,
      ← Real.rpow_neg hxa.le, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB x) (by positivity)
  have hIoc : IntegrableOn (fun x : ℝ => ((f x : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ w)
      (Ioc c (c + 1)) := by
    refine IntegrableOn.of_bound measure_Ioc_lt_top hmeas.aestronglyMeasurable
      (B * a ^ (-w.re)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    refine (hnorm x hx.1.le).trans (mul_le_mul_of_nonneg_left ?_ hB0)
    exact Real.rpow_le_rpow_of_nonpos ha (by linarith [hx.1]) (by linarith)
  have hIoi : IntegrableOn (fun x : ℝ => ((f x : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ w)
      (Ioi (c + 1)) := by
    have hint : IntegrableOn (fun x : ℝ => B * x ^ (-w.re)) (Ioi (c + 1)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)).const_mul B
    refine hint.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
    refine (hnorm x (by linarith [mem_Ioi.mp hx])).trans (mul_le_mul_of_nonneg_left ?_ hB0)
    exact Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)
  have hU : Ioi c = Ioc c (c + 1) ∪ Ioi (c + 1) := (Ioc_union_Ioi_eq_Ioi (by linarith)).symm
  rw [hU]
  exact hIoc.union hIoi

/-- `s ∫_k^{k+1} (x+a)^{-(s+1)} dx = (k+a)^{-s} - (k+1+a)^{-s}` for real `a > 0`, `k ≥ 0`. -/
lemma r25b_integral_cpow_unit {s : ℂ} (hs : s ≠ 0) {a : ℝ} (ha : 0 < a) (k : ℕ) :
    s * ∫ x in (k : ℝ)..(k + 1), 1 / (((x + a : ℝ)) : ℂ) ^ (s + 1) =
      ((a : ℂ) + k) ^ (-s) - ((a : ℂ) + (k + 1 : ℕ)) ^ (-s) := by
  have hd : ∀ x ∈ uIcc (k : ℝ) (k + 1), HasDerivAt (fun y : ℝ => -((a : ℂ) + y) ^ (-s) / s)
      (1 / (((x + a : ℝ)) : ℂ) ^ (s + 1)) x := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hx0 : (0 : ℝ) ≤ x := le_trans k.cast_nonneg hx.1
    have h := ((r25b_hasDerivAt_cpow_shift (w := (a : ℂ)) (c := -s) (t := x)
      (r25b_mem_slitPlane (by simpa using ha) hx0)).neg).div_const s
    convert h using 1
    rw [one_div, ← cpow_neg, show -(s + 1) = -s - 1 by ring]
    field_simp
    push_cast; ring_nf
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · push_cast
    field_simp
    ring
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hxa : 0 < x + a := by linarith [le_trans k.cast_nonneg hx.1]
    have hx0 : (0 : ℝ) ≤ x := le_trans k.cast_nonneg hx.1
    have hc := (r25b_hasDerivAt_cpow_shift (w := (a : ℂ)) (c := -s - 1) (t := x)
      (r25b_mem_slitPlane (by simpa using ha) hx0)).continuousAt.continuousWithinAt
      (s := uIcc (k : ℝ) (k + 1))
    refine hc.congr (fun y hy => ?_) ?_
    · rw [one_div, ← cpow_neg, show -(s + 1) = -s - 1 by ring]; push_cast; ring_nf
    · rw [one_div, ← cpow_neg, show -(s + 1) = -s - 1 by ring]; push_cast; ring_nf

/-- **Euler–Maclaurin, first order** (DLMF 25.11.5): for `s ≠ 1`, `Re s > 0`, real `a > 0` and
`N = 0, 1, 2, …`,
`ζ(s,a) = ∑_{n=0}^{N} (n+a)^{-s} + (N+a)^{1-s}/(s-1) - s ∫_N^∞ (x - ⌊x⌋)/(x+a)^{s+1} dx`. -/
@[dlmf 25.11.E5]
theorem hurwitzZetaComplex_eulerMaclaurin_one {s : ℂ} (hs : s ≠ 1) (hs0 : 0 < s.re) {a : ℝ}
    (ha : 0 < a) (N : ℕ) :
    hurwitzZetaComplex s a = (∑ n ∈ Finset.range (N + 1), 1 / ((n : ℂ) + a) ^ s) +
      ((N : ℂ) + a) ^ (1 - s) / (s - 1) -
      s * ∫ x in Ioi (N : ℝ), ((Int.fract x : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (s + 1) := by
  have hsz : s ≠ 0 := by rintro rfl; simp at hs0
  have hM : 0 < s.re + 2 * ((0 : ℕ) : ℝ) := by simpa using hs0
  have h1 := r25b_hasSum_emD (M := 0) hs hM (a : ℂ) N
  simp_rw [r25b_emD_eq_integral 0 hs ha] at h1
  have hfr : IntegrableOn (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (s + 1))
      (Ioi (N : ℝ)) :=
    r25b_integrableOn_bdd_div_cpow measurable_fract (B := 1)
      (fun x => by rw [abs_of_nonneg (Int.fract_nonneg x)]; exact (Int.fract_lt_one x).le)
      (by simp; linarith) ha N.cast_nonneg
  have h2 := (r25b_hasSum_intervalIntegral hfr).mul_left (-s)
  have h3 := h1.sub h2
  set u : ℕ → ℂ := fun m => ((a : ℂ) + (N + m : ℕ)) ^ (-s)
  have hterm : ∀ m : ℕ, -(poch s (2 * 0 + 1) / ((2 * 0 + 1 : ℕ)! : ℂ)) *
      (∫ x in ((N + m : ℕ) : ℝ)..((N + m : ℕ) + 1), ((periodicBernoulli (2 * 0 + 1) x : ℝ) : ℂ) /
        (((x + a : ℝ)) : ℂ) ^ (s + (2 * 0 + 1 : ℕ))) -
      -s * ∫ x in ((N + m : ℕ) : ℝ)..((N + m : ℕ) + 1),
        ((Int.fract x : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (s + 1) = (u m - u (m + 1)) / 2 := by
    intro m
    set k := N + m
    have hk : (N : ℝ) ≤ k := by simp [k]
    have hsub : Ioc (k : ℝ) (k + 1) ⊆ Ioi (N : ℝ) := fun x hx => lt_of_le_of_lt hk hx.1
    have hI1 : IntervalIntegrable (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) /
        (((x + a : ℝ)) : ℂ) ^ (s + 1)) volume (k : ℝ) (k + 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr (hfr.mono_set hsub)
    have hone : IntegrableOn (fun x : ℝ => (((1 : ℝ) : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (s + 1))
        (Ioi (N : ℝ)) :=
      r25b_integrableOn_bdd_div_cpow measurable_const (B := 1) (fun x => by simp)
        (by simp; linarith) ha N.cast_nonneg
    have hI2 : IntervalIntegrable (fun x : ℝ => 1 / (((x + a : ℝ)) : ℂ) ^ (s + 1)) volume
        (k : ℝ) (k + 1) := by
      have := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
        (hone.mono_set hsub)
      simpa using this
    have hB : ∫ x in (k : ℝ)..(k + 1), ((periodicBernoulli (2 * 0 + 1) x : ℝ) : ℂ) /
        (((x + a : ℝ)) : ℂ) ^ (s + (2 * 0 + 1 : ℕ)) =
        (∫ x in (k : ℝ)..(k + 1), ((Int.fract x : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (s + 1)) -
          1 / 2 * ∫ x in (k : ℝ)..(k + 1), 1 / (((x + a : ℝ)) : ℂ) ^ (s + 1) := by
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub hI1 (hI2.const_mul _)]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [periodicBernoulli, Nat.mul_zero, Nat.zero_add]
      rw [bernoulliFun_one]
      push_cast
      ring
    have hU := r25b_integral_cpow_unit hsz ha k
    rw [hB]
    simp only [poch, ascPochhammer_one, Polynomial.eval_X, mul_zero, zero_add, Nat.factorial_one,
      Nat.cast_one, div_one]
    simp only [u, k] at hU ⊢
    rw [show N + (m + 1) = N + m + 1 by ring]
    linear_combination hU / 2
  have hT := h3.tendsto_sum_nat
  simp_rw [hterm] at hT
  have hU0 : Tendsto (fun K : ℕ => ∑ m ∈ Finset.range K, (u m - u (m + 1)) / 2) atTop
      (𝓝 (u 0 / 2)) := by
    have hlim : Tendsto (fun K : ℕ => u K) atTop (𝓝 0) := by
      have := r25b_tendsto_cpow_nat ((a : ℂ) + N) (w := -s) (by simp; linarith)
      refine this.congr fun K => ?_
      simp only [u]; push_cast; ring_nf
    have := (hlim.const_sub (u 0)).div_const 2
    rw [sub_zero] at this
    refine this.congr fun K => ?_
    rw [← Finset.sum_div, Finset.sum_range_sub']
  have hval := tendsto_nhds_unique hT hU0
  rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add] at hval
  rw [hval]
  simp only [u, r25b_emSeq, r25b_emF, Finset.range_zero, Finset.sum_empty, add_zero,
    Finset.sum_range_succ]
  simp only [one_div, ← cpow_neg]
  have hc : ∀ x : ℕ, (x : ℂ) + a = a + x := fun x => add_comm _ _
  simp only [hc]
  ring


/-- The `M = 0` Euler–Maclaurin increment via `B₂(t) - B₂`:
`emD₀(s, w) = -(s(s+1)/2) ∫_0^1 (B₂(t) - B₂)(w+t)^{-s-2} dt`. -/
lemma r25b_emD_zero_eq {s w : ℂ} (hs : s ≠ 1) (hw : 0 < w.re) :
    r25b_emD 0 s w = -(s * (s + 1) / 2) *
      ∫ t in (0 : ℝ)..1, (w + t) ^ (-s - 2) * ((bernoulliFun 2 t : ℂ) - bernoulli 2) := by
  have EM := r25b_integral_eq_sum_bernoulliFun (r25b_fam s w)
    (fun j x hx => r25b_hasDerivAt_fam hw j hx.1) 2
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hs2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  -- `∫_0^1 f = ((w+1)^{1-s} - w^{1-s})/(1-s)`
  have hint :
      ∫ t in (0 : ℝ)..1, r25b_fam s w 0 t = ((w + 1) ^ (1 - s) - w ^ (1 - s)) / (1 - s) := by
    have hF : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => (w + y) ^ (1 - s) / (1 - s))
        (r25b_fam s w 0 x) x := by
      intro x hx
      rw [uIcc_of_le zero_le_one] at hx
      have := (r25b_hasDerivAt_cpow_shift (c := 1 - s) (r25b_mem_slitPlane hw hx.1)).div_const
        (1 - s)
      convert this using 1
      simp only [r25b_fam, pow_zero, DLMF.Hypergeometric.poch_zero, Nat.cast_zero, sub_zero,
        one_mul]
      field_simp
      ring_nf
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF]
    · simp; ring
    · apply ContinuousOn.intervalIntegrable
      intro x hx
      exact (r25b_hasDerivAt_fam hw 0 (by rw [uIcc_of_le zero_le_one] at hx; exact hx.1)
        ).continuousAt.continuousWithinAt
  -- `∫_0^1 f₂ = f₁(1) - f₁(0)`
  have hint2 : ∫ t in (0 : ℝ)..1, r25b_fam s w 2 t = r25b_fam s w 1 1 - r25b_fam s w 1 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
    · intro x hx
      rw [uIcc_of_le zero_le_one] at hx
      exact r25b_hasDerivAt_fam hw 1 hx.1
    · apply ContinuousOn.intervalIntegrable
      intro x hx
      exact (r25b_hasDerivAt_fam hw 2 (by rw [uIcc_of_le zero_le_one] at hx; exact hx.1)
        ).continuousAt.continuousWithinAt
  have hI2 : IntervalIntegrable (r25b_fam s w 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact (r25b_hasDerivAt_fam hw 2 (by rw [uIcc_of_le zero_le_one] at hx; exact hx.1)
      ).continuousAt.continuousWithinAt
  have hsplit : s * (s + 1) * ∫ t in (0 : ℝ)..1,
      (w + t) ^ (-s - 2) * ((bernoulliFun 2 t : ℂ) - bernoulli 2) =
      (∫ t in (0 : ℝ)..1, r25b_fam s w 2 t * (bernoulliFun 2 t : ℂ)) -
        bernoulli 2 * ∫ t in (0 : ℝ)..1, r25b_fam s w 2 t := by
    have hB2 : IntervalIntegrable (fun t : ℝ => r25b_fam s w 2 t * (bernoulliFun 2 t : ℂ))
        volume 0 1 :=
      hI2.mul_continuousOn (Complex.continuous_ofReal.comp
        (continuous_bernoulliFun 2)).continuousOn
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub hB2 (hI2.const_mul _)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [r25b_fam, DLMF.Hypergeometric.poch_succ, DLMF.Hypergeometric.poch_zero]
    push_cast
    ring_nf
  have hb1 : bernoulliFun 2 1 = bernoulli 2 := by
    rw [bernoulliFun_endpoints_eq_of_ne_one (by norm_num), bernoulliFun_eval_zero]
  have hb0 : bernoulliFun 2 0 = bernoulli 2 := bernoulliFun_eval_zero _
  rw [hint, Finset.sum_range_succ, Finset.sum_range_one] at EM
  simp only [bernoulliFun_one, hb1, hb0, zero_add, pow_zero, pow_one, Nat.factorial_one,
    Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat, div_one, one_mul, even_two, Even.neg_pow,
    one_pow] at EM
  have h0 : r25b_fam s w 0 1 = (w + 1) ^ (-s) := by simp [r25b_fam, DLMF.Hypergeometric.poch_zero]
  have h0' : r25b_fam s w 0 0 = w ^ (-s) := by simp [r25b_fam, DLMF.Hypergeometric.poch_zero]
  rw [h0, h0'] at EM
  rw [hint2] at hsplit
  unfold r25b_emD r25b_emF
  simp only [Finset.range_zero, Finset.sum_empty, add_zero]
  rw [show ((w + 1) ^ (1 - s) - w ^ (1 - s)) / (1 - s) =
    -(((w + 1) ^ (1 - s) - w ^ (1 - s)) / (s - 1)) by rw [← div_neg, neg_sub]] at EM
  set I := ∫ t in (0 : ℝ)..1, (w + t) ^ (-s - 2) * ((bernoulliFun 2 t : ℂ) - bernoulli 2)
  set J := ∫ t in (0 : ℝ)..1, r25b_fam s w 2 t * (bernoulliFun 2 t : ℂ)
  have h2f : ((2 ! : ℕ) : ℂ) = 2 := by norm_num [Nat.factorial]
  rw [h2f] at EM
  push_cast at EM hsplit
  linear_combination (-1 : ℂ) * EM + (1 / 2 : ℂ) * hsplit

/-- The `M = 0` increment at a real point as an integral against `B̃₂ - B₂`. -/
lemma r25b_emD_zero_eq_integral {s : ℂ} (hs : s ≠ 1) {a : ℝ} (ha : 0 < a) (k : ℕ) :
    r25b_emD 0 s ((a : ℂ) + k) = -(s * (s + 1) / 2) *
      ∫ x in (k : ℝ)..(k + 1),
        ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (s + 2) := by
  rw [r25b_emD_zero_eq hs (by simp; positivity)]
  congr 1
  have hsub := intervalIntegral.integral_comp_add_right (a := 0) (b := 1)
    (fun x : ℝ => ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) /
      (((x + a : ℝ)) : ℂ) ^ (s + 2)) (k : ℝ)
  simp only [zero_add] at hsub
  rw [show (k : ℝ) + 1 = 1 + k by ring, ← hsub]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t ht htI
  rw [uIoc_of_le zero_le_one] at htI
  have hfr : Int.fract (t + k) = t := by
    rw [Int.fract_add_natCast, Int.fract_eq_self.mpr ⟨htI.1.le, lt_of_le_of_ne htI.2 ht⟩]
  rw [periodicBernoulli, hfr, div_eq_mul_inv, ← cpow_neg, mul_comm]
  congr 2 <;> push_cast <;> ring

/-- **Euler–Maclaurin with `B̃₂`** (DLMF 25.11.6): for `s ≠ 1`, `Re s > -1`, real `a > 0`,
`ζ(s,a) = a^{-s}(1/2 + a/(s-1)) - (s(s+1)/2) ∫_0^∞ (B̃₂(x) - B₂)/(x+a)^{s+2} dx`,
with the periodic Bernoulli function `B̃₂ = periodicBernoulli 2` (§24.2(iii)). -/
@[dlmf 25.11.E6]
theorem hurwitzZetaComplex_eulerMaclaurin_two {s : ℂ} (hs : s ≠ 1) (hs0 : -1 < s.re) {a : ℝ}
    (ha : 0 < a) :
    hurwitzZetaComplex s a = (a : ℂ) ^ (-s) * (1 / 2 + a / (s - 1)) -
      s * (s + 1) / 2 * ∫ x in Ioi (0 : ℝ),
        ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (s + 2) := by
  -- the `M = 0` sequence converges for `Re s > -1`
  have hT0 : Tendsto (r25b_emSeq 0 s a) atTop (𝓝 (hurwitzZetaComplex s a)) := by
    have h1 := r25b_tendsto_hurwitzZetaComplex (M := 1) (z := (a : ℂ)) hs (by simp; linarith)
    have h2 := (r25b_tendsto_cpow_nat (a : ℂ) (w := -s - (2 * ((0 : ℕ) : ℂ) + 1))
      (by simp; linarith)).const_mul (r25b_emC s 0)
    rw [mul_zero] at h2
    have := h1.sub h2
    rw [sub_zero] at this
    refine this.congr fun N => ?_
    rw [r25b_emSeq_succ_M]; ring
  have hP : Tendsto (fun K : ℕ => ∑ m ∈ Finset.range K, r25b_emD 0 s ((a : ℂ) + (0 + m : ℕ)))
      atTop (𝓝 (hurwitzZetaComplex s a - r25b_emSeq 0 s a 0)) := by
    refine (hT0.sub_const _).congr fun K => ?_
    rw [← zero_add K, r25b_emSeq_add, zero_add]; ring
  have hterm : ∀ m : ℕ, r25b_emD 0 s ((a : ℂ) + (0 + m : ℕ)) = -(s * (s + 1) / 2) *
      ∫ x in ((0 + m : ℕ) : ℝ)..((0 + m : ℕ) + 1),
        ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (s + 2) :=
    fun m => r25b_emD_zero_eq_integral hs ha (0 + m)
  simp_rw [hterm] at hP
  have hint : IntegrableOn (fun x : ℝ => ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) /
      (((x + a : ℝ)) : ℂ) ^ (s + 2)) (Ioi ((0 : ℕ) : ℝ)) := by
    obtain ⟨B, hB⟩ : ∃ B, ∀ y ∈ Icc (0 : ℝ) 1, ‖bernoulliFun 2 y‖ ≤ B :=
      IsCompact.exists_bound_of_continuousOn isCompact_Icc (continuous_bernoulliFun 2).continuousOn
    refine r25b_integrableOn_bdd_div_cpow ((measurable_periodicBernoulli 2).sub_const _)
      (B := B + |(bernoulli 2 : ℝ)|) (fun x => ?_) (by simp; linarith) ha (by simp)
    have := hB _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
    have h2 := abs_sub (periodicBernoulli 2 x) (bernoulli 2 : ℝ)
    rw [Real.norm_eq_abs] at this
    simp only [periodicBernoulli] at h2 ⊢
    linarith
  have h2 := ((r25b_hasSum_intervalIntegral hint).mul_left (-(s * (s + 1) / 2))).tendsto_sum_nat
  have hval := tendsto_nhds_unique hP h2
  rw [sub_eq_iff_eq_add] at hval
  rw [hval, Nat.cast_zero]
  simp only [r25b_emSeq, r25b_emF, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, add_zero,
    zero_add]
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hp : (a : ℂ) ^ (1 - s) = a * a ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ ha0, cpow_one]
  rw [hp]
  ring


/-- **Euler–Maclaurin of order `2n+1`** (DLMF 25.11.7): for `s ≠ 1`, real `a > 0`, `n ≥ 1` and
`Re s > -2n`,
`ζ(s,a) = a^{-s} + (1+a)^{-s}(1/2 + (1+a)/(s-1)) + ∑_{k=1}^{n} C(s+2k-2, 2k-1) (B_{2k}/2k)
(1+a)^{-(s+2k-1)} - C(s+2n, 2n+1) ∫_1^∞ B̃_{2n+1}(x)/(x+a)^{s+2n+1} dx`. -/
@[dlmf 25.11.E7]
theorem hurwitzZetaComplex_eulerMaclaurin {s : ℂ} (hs : s ≠ 1) {a : ℝ} (ha : 0 < a) {n : ℕ}
    (hn : 1 ≤ n) (hsn : -(2 * n : ℝ) < s.re) :
    hurwitzZetaComplex s a = (a : ℂ) ^ (-s) + (1 + (a : ℂ)) ^ (-s) * (1 / 2 + (1 + a) / (s - 1)) +
      (∑ k ∈ Finset.Icc 1 n, Ring.choose (s + 2 * k - 2) (2 * k - 1) *
        ((bernoulli (2 * k) : ℂ) / (2 * k)) * (1 + (a : ℂ)) ^ (-(s + 2 * k - 1))) -
      Ring.choose (s + 2 * n) (2 * n + 1) * ∫ x in Ioi (1 : ℝ),
        ((periodicBernoulli (2 * n + 1) x : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (s + 2 * n + 1) := by
  have _ := hn
  have hM : 0 < s.re + 2 * (n : ℝ) := by linarith
  have h1 := r25b_hasSum_emD (M := n) hs hM (a : ℂ) 1
  simp_rw [r25b_emD_eq_integral n hs ha] at h1
  have hint := r25b_integrableOn_periodicBernoulli_div (2 * n + 1)
    (w := s + (2 * n + 1 : ℕ)) (by push_cast; simp; linarith) ha.le (c := ((1 : ℕ) : ℝ)) (by simp)
  have h2 := (r25b_hasSum_intervalIntegral hint).mul_left
    (-(poch s (2 * n + 1) / (2 * n + 1 : ℕ)!))
  have heq := h1.unique h2
  rw [sub_eq_iff_eq_add] at heq
  rw [heq]
  have hI : ∫ x in Ioi ((1 : ℕ) : ℝ), ((periodicBernoulli (2 * n + 1) x : ℝ) : ℂ) /
      (((x + a : ℝ)) : ℂ) ^ (s + (2 * n + 1 : ℕ)) = ∫ x in Ioi (1 : ℝ),
        ((periodicBernoulli (2 * n + 1) x : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (s + 2 * n + 1) := by
    rw [Nat.cast_one]
    congr 1; funext x; congr 2; push_cast; ring
  have hc : Ring.choose (s + 2 * n) (2 * n + 1) = poch s (2 * n + 1) / (2 * n + 1 : ℕ)! := by
    rw [← r25b_choose_eq_poch]; congr 1; push_cast; ring
  have h1a : (1 + (a : ℂ)) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hp : (1 + (a : ℂ)) ^ (1 - s) = (1 + a) * (1 + a) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ h1a, cpow_one]
  have hsum : ∑ k ∈ Finset.Icc 1 n, Ring.choose (s + 2 * k - 2) (2 * k - 1) *
        ((bernoulli (2 * k) : ℂ) / (2 * k)) * (1 + (a : ℂ)) ^ (-(s + 2 * k - 1)) =
      ∑ k ∈ Finset.range n, r25b_emC s k * ((a : ℂ) + 1) ^ (-s - (2 * k + 1)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, add_tsub_cancel_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hck : Ring.choose (s + 2 * ((1 + k : ℕ) : ℂ) - 2) (2 * (1 + k) - 1) =
        poch s (2 * k + 1) / (2 * k + 1 : ℕ)! := by
      rw [show 2 * (1 + k) - 1 = 2 * k + 1 by omega, ← r25b_choose_eq_poch]
      congr 1; push_cast; ring
    rw [hck, r25b_emC, show 2 * k + 2 = 2 * (1 + k) by ring]
    have hf : ((2 * (1 + k))! : ℂ) = (2 * (1 + k) : ℕ) * ((2 * k + 1 : ℕ)! : ℂ) := by
      rw [show 2 * (1 + k) = (2 * k + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
    have hf0 : ((2 * k + 1 : ℕ)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hk0 : (2 * ((1 + k : ℕ) : ℂ)) ≠ 0 := by
      apply mul_ne_zero two_ne_zero; exact_mod_cast Nat.succ_ne_zero k ∘ (by omega)
    rw [hf, show (-(s + 2 * ((1 + k : ℕ) : ℂ) - 1)) = -s - (2 * k + 1) by push_cast; ring,
      add_comm (1 : ℂ) a]
    push_cast at hk0 ⊢
    field_simp
  rw [hI, hc, hsum]
  simp only [r25b_emSeq, r25b_emF, Finset.sum_range_one, Nat.cast_zero, add_zero, Nat.cast_one]
  rw [add_comm (a : ℂ) 1, hp]
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp
  ring


/-! ### §25.11(iv) Series representations -/

/-- **Duplication by the alternating series** (DLMF 25.11.8): for `Re s > 0`, `s ≠ 1` and
`0 < a ≤ 1`, `ζ(s, a/2) = ζ(s, a/2 + 1/2) + 2^s ∑_{n≥0} (-1)^n/(n+a)^s`. The alternating series
converges (conditionally for `Re s ≤ 1`); it is stated as the limit of its partial sums. -/
@[dlmf 25.11.E8]
theorem hurwitzZeta_half_eq_add_alternating {s : ℂ} (hs : s ≠ 1) (hs0 : 0 < s.re) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n / ((n : ℂ) + a) ^ s) atTop
      (𝓝 ((hurwitzZeta ((a / 2 : ℝ) : UnitAddCircle) s -
        hurwitzZeta ((a / 2 + 1 / 2 : ℝ) : UnitAddCircle) s) / 2 ^ s)) := by
  have hb : ∀ N, ‖∑ n ∈ Finset.range N, (-1 : ℂ) ^ n‖ ≤ 1 := by
    intro N
    rw [geom_sum_eq (by norm_num : (-1 : ℂ) ≠ 1), norm_div]
    have : ‖(-1 : ℂ) ^ N - 1‖ ≤ 2 := by
      calc ‖(-1 : ℂ) ^ N - 1‖ ≤ ‖(-1 : ℂ) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, norm_neg, norm_one, one_pow]; norm_num
    rw [show ‖(-1 : ℂ) - 1‖ = 2 by norm_num]
    linarith
  obtain ⟨G, hG, hT⟩ := s25b_dirichlet_test hb ha0
  have hterm : ∀ (n : ℕ) (t : ℂ), (-1 : ℂ) ^ n / ((n : ℂ) + a) ^ t =
      (-1 : ℂ) ^ n * (((n + a : ℝ)) : ℂ) ^ (-t) := by
    intro n t; rw [cpow_neg, div_eq_mul_inv]; push_cast; ring
  set H : ℂ → ℂ := fun t => (hurwitzZeta ((a / 2 : ℝ) : UnitAddCircle) t -
    hurwitzZeta ((a / 2 + 1 / 2 : ℝ) : UnitAddCircle) t) / 2 ^ t
  have hH : DifferentiableOn ℂ H ({t : ℂ | 0 < t.re} \ {1}) := by
    intro t ht
    have ht1 : t ≠ 1 := ht.2
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.div ((differentiableAt_hurwitzZeta _ ht1).sub
      (differentiableAt_hurwitzZeta _ ht1)) ?_ ?_
    · exact (differentiableAt_id.const_cpow (Or.inl two_ne_zero))
    · rw [Ne, cpow_eq_zero_iff]; simp
  have hU : IsOpen ({t : ℂ | 0 < t.re} \ {1}) :=
    (isOpen_lt continuous_const continuous_re).sdiff isClosed_singleton
  have heq : EqOn G H ({t : ℂ | 0 < t.re} \ {1}) := by
    refine ((hG.mono sdiff_subset).analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
      (hH.analyticOnNhd hU) s25b_isPreconnected_re_pos_diff_one
      (show (2 : ℂ) ∈ ({t : ℂ | 0 < t.re} \ {1}) by norm_num) ?_
    have hopen : IsOpen {t : ℂ | 1 < t.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with t ht
    refine tendsto_nhds_unique (hT t (by linarith)) ?_
    have h2 : (2 : ℂ) ^ t ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; simp
    have hsplit : ∀ k : ℕ, ∀ b : ℝ, 0 ≤ b → ((((2 * k : ℕ) : ℂ) + 2 * b)) ^ t =
        2 ^ t * ((k : ℂ) + b) ^ t := by
      intro k b hb
      rw [show (((2 * k : ℕ) : ℂ) + 2 * b) = ((2 : ℝ) : ℂ) * (((k + b : ℝ)) : ℂ) by push_cast; ring,
        mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
      push_cast; ring_nf
    have he := (hasSum_hurwitzZeta_of_one_lt_re (a := a / 2) ⟨by positivity, by linarith⟩
      ht).div_const (2 ^ t)
    have ho := ((hasSum_hurwitzZeta_of_one_lt_re (a := a / 2 + 1 / 2) ⟨by positivity, by linarith⟩
      ht).div_const (2 ^ t)).neg
    have hs := HasSum.even_add_odd (f := fun n : ℕ => (-1 : ℂ) ^ n / ((n : ℂ) + a) ^ t)
      (he.congr_fun fun k => ?_) (ho.congr_fun fun k => ?_)
    · rw [← neg_div, ← add_div, ← sub_eq_add_neg] at hs
      refine hs.tendsto_sum_nat.congr fun N => Finset.sum_congr rfl fun n _ => hterm n t
    · have := hsplit k (a / 2) (by positivity)
      rw [show (-1 : ℂ) ^ (2 * k) = 1 by rw [pow_mul]; norm_num,
        show ((2 * k : ℕ) : ℂ) + a = ((2 * k : ℕ) : ℂ) + 2 * ((a / 2 : ℝ) : ℂ) by push_cast; ring,
        this]
      push_cast
      field_simp
    · have := hsplit k (a / 2 + 1 / 2) (by positivity)
      rw [show (-1 : ℂ) ^ (2 * k + 1) = -1 by rw [pow_succ, pow_mul]; norm_num,
        show ((2 * k + 1 : ℕ) : ℂ) + a = ((2 * k : ℕ) : ℂ) + 2 * ((a / 2 + 1 / 2 : ℝ) : ℂ) by
        push_cast; ring, this]
      push_cast
      field_simp
  have hGs := heq ⟨hs0, hs⟩
  simp only [H] at hGs
  rw [← hGs]
  exact (hT s hs0).congr fun N => Finset.sum_congr rfl fun n _ => (hterm n s).symm

/-- **Hurwitz's Fourier series** (DLMF 25.11.9): `ζ(1-s, a) = (2Γ(s)/(2π)^s) ∑_{n≥1} n^{-s}
cos(πs/2 - 2nπa)` for `Re s > 0` if `0 < a < 1`, and `Re s > 1` if `a = 1`; partial-sum limit
(the series converges conditionally for `0 < Re s ≤ 1`). -/
@[dlmf 25.11.E9]
theorem hurwitzZeta_one_sub_fourier {s : ℂ} {a : ℝ}
    (h : (0 < a ∧ a < 1 ∧ 0 < s.re) ∨ (a = 1 ∧ 1 < s.re)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        1 / ((n : ℂ) + 1) ^ s * Complex.cos (π * s / 2 - 2 * (n + 1) * π * a)) atTop
      (𝓝 (hurwitzZeta (a : UnitAddCircle) (1 - s) * (2 * π) ^ s / (2 * Gamma s))) := by
  have hs0 : 0 < s.re := by rcases h with ⟨-, -, h⟩ | ⟨-, h⟩ <;> linarith
  have hnot : ∀ m : ℕ, s ≠ -m := fun m hm => by
    have := congrArg Complex.re hm; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hcond : ∀ x : ℝ, (0 < a ∧ a < 1 → ∀ m : ℤ, x ≠ m) →
      (((∀ m : ℤ, x ≠ m) ∧ 0 < s.re) ∨ 1 < s.re) := by
    intro x hx
    rcases h with ⟨h1, h2, h3⟩ | ⟨-, h4⟩
    · exact Or.inl ⟨hx ⟨h1, h2⟩, h3⟩
    · exact Or.inr h4
  have hnz : ∀ m : ℤ, 0 < a → a < 1 → a ≠ m := fun m h1 h2 hm => by
    subst hm
    have : (0 : ℤ) < m := by exact_mod_cast h1
    have : m < 1 := by exact_mod_cast h2
    omega
  have hA := s25b_tendsto_expZeta (x := a) (hcond a fun h' m => hnz m h'.1 h'.2)
  have hB := s25b_tendsto_expZeta (x := -a) (hcond (-a) fun h' m hm =>
    hnz (-m) h'.1 h'.2 (by push_cast; linarith))
  have hs' : (a : UnitAddCircle) ≠ 0 ∨ s ≠ 1 := by
    rcases h with ⟨h1, h2, -⟩ | ⟨-, h4⟩
    · left
      rw [Ne, AddCircle.coe_eq_zero_iff]
      rintro ⟨m, hm⟩
      exact hnz m h1 h2 (by simpa using hm.symm)
    · right; rintro rfl; simp at h4
  have hG : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
  have h2π : (2 * π : ℂ) ^ s ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; simp [Real.pi_ne_zero]
  rw [hurwitzZeta_one_sub _ hnot hs', ← AddCircle.coe_neg] at *
  have hlim := ((hB.const_mul (cexp (π * I * s / 2))).add
    (hA.const_mul (cexp (-π * I * s / 2)))).div_const 2
  convert hlim using 1
  · funext N
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hn : ((n : ℂ) + 1) ^ s ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; push Not; intro h0; exact absurd h0 (by norm_cast)
    rw [Complex.cos]
    have e1 : cexp ((π * s / 2 - 2 * (n + 1) * π * a) * I) =
        cexp (π * I * s / 2) * cexp (2 * π * I * (n + 1) * ((-a : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    have e2 : cexp (-(π * s / 2 - 2 * (n + 1) * π * a) * I) =
        cexp (-π * I * s / 2) * cexp (2 * π * I * (n + 1) * (a : ℂ)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [e1, e2]
    field_simp
  · congr 1
    rw [cpow_neg]
    field_simp
    ring_nf

/-- **Taylor series in `a` about `1`** (DLMF 25.11.10): for `s ≠ 1` and `|a - 1| < 1`,
`ζ(s, a) = ∑_{n≥0} ((s)_n/n!) ζ(n+s) (1-a)^n`.

Corrected statement (2026-10-25): the hypothesis `hs' : ∀ m : ℕ, s ≠ -m` is added. At
`s = 0, -1, -2, …` the term with `n + s = 1` is DLMF's limit of `(s)_n ζ(n+s)`, whereas Lean's
`poch s n · ζ(1)` gives `0`; see `r25b_hasSum_hurwitzZetaComplex_taylor_counterexample`. -/
@[dlmf 25.11.E10]
theorem hasSum_hurwitzZetaComplex_taylor {s a : ℂ} (hs : s ≠ 1) (hs' : ∀ m : ℕ, s ≠ -m)
    (ha : ‖a - 1‖ < 1) :
    HasSum (fun n : ℕ => poch s n / n ! * riemannZeta (n + s) * (1 - a) ^ n)
      (hurwitzZetaComplex s a) := by
  sorry

/-! ### Sums of Hurwitz zeta functions over rational parameters -/

/-- Reindexing a sum over `ZMod k` as a sum over `0 ≤ r < k`. -/
lemma q25b_sum_zmod_eq_sum_range {k : ℕ} [NeZero k] {M : Type*} [AddCommMonoid M]
    (f : ZMod k → M) : ∑ j : ZMod k, f j = ∑ r ∈ Finset.range k, f (r : ZMod k) := by
  refine Finset.sum_bij' (fun j _ => j.val) (fun r _ => (r : ZMod k)) ?_ ?_ ?_ ?_ ?_
  · intro j _; simpa using ZMod.val_lt j
  · intro r _; simp
  · intro j _; simp
  · intro r hr; simpa using ZMod.val_cast_of_lt (Finset.mem_range.mp hr)
  · intro j _; simp

/-- The `L`-function of the constant function `1` on `ZMod k` is Riemann's zeta function, for
`s ≠ 1` (analytic continuation from `Re s > 1`). -/
lemma q25b_LFunction_const_one {k : ℕ} [NeZero k] {s : ℂ} (hs : s ≠ 1) :
    ZMod.LFunction (fun _ : ZMod k => (1 : ℂ)) s = riemannZeta s := by
  set U : Set ℂ := {1}ᶜ
  have hUo : IsOpen U := isOpen_compl_singleton
  have hf : AnalyticOnNhd ℂ (ZMod.LFunction (fun _ : ZMod k => (1 : ℂ))) U :=
    DifferentiableOn.analyticOnNhd (fun u hu =>
      (ZMod.differentiableAt_LFunction _ u (Or.inl hu)).differentiableWithinAt) hUo
  have hg : AnalyticOnNhd ℂ riemannZeta U :=
    DifferentiableOn.analyticOnNhd (fun u hu =>
      (differentiableAt_riemannZeta hu).differentiableWithinAt) hUo
  have hUc : IsPreconnected U :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) _).isPreconnected
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg hUc (z₀ := 2) (by norm_num [U]) ?_ hs
  have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
  filter_upwards [hV] with z hz
  rw [ZMod.LFunction_eq_LSeries _ hz, ← LSeries_one_eq_riemannZeta hz]
  rfl

/-- **Distribution relation**: `∑_{r=1}^{k-1} ζ(s, r/k) = (k^s - 1) ζ(s)` for `s ≠ 1`, `k ≥ 1`
(Mathlib's Hurwitz zeta). -/
theorem q25b_sum_hurwitzZeta_rat {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : s ≠ 1) :
    ∑ r ∈ Finset.Ico 1 k, hurwitzZeta ((r / k : ℝ) : UnitAddCircle) s =
      ((k : ℂ) ^ s - 1) * riemannZeta s := by
  have : NeZero k := ⟨by omega⟩
  have h := q25b_LFunction_const_one (k := k) hs
  simp only [ZMod.LFunction, one_mul] at h
  rw [q25b_sum_zmod_eq_sum_range (fun j => hurwitzZeta (ZMod.toAddCircle j) s),
    Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)] at h
  simp only [Nat.cast_zero, map_zero, hurwitzZeta_zero, ZMod.toAddCircle_natCast] at h
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hks : (k : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hk0)
  rw [cpow_neg] at h
  field_simp at h
  linear_combination h

/-- The `s`-derivative of the distribution relation (DLMF 25.11.24). -/
theorem q25b_sum_deriv_hurwitzZeta_rat {s : ℂ} (hs : s ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    ∑ r ∈ Finset.Ico 1 k, deriv (hurwitzZeta ((r / k : ℝ) : UnitAddCircle)) s =
      ((k : ℂ) ^ s - 1) * deriv riemannZeta s + (k : ℂ) ^ s * riemannZeta s * Real.log k := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hev : (fun t => ∑ r ∈ Finset.Ico 1 k, hurwitzZeta ((r / k : ℝ) : UnitAddCircle) t) =ᶠ[𝓝 s]
      fun t => ((k : ℂ) ^ t - 1) * riemannZeta t := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with t ht
    exact q25b_sum_hurwitzZeta_rat hk ht
  have hD : HasDerivAt (fun t => ((k : ℂ) ^ t - 1) * riemannZeta t)
      ((k : ℂ) ^ s * Complex.log k * riemannZeta s + ((k : ℂ) ^ s - 1) * deriv riemannZeta s) s :=
    (((hasStrictDerivAt_const_cpow (Or.inl hk0)).hasDerivAt).sub_const 1).mul
      (differentiableAt_riemannZeta hs).hasDerivAt
  rw [← deriv_fun_sum (fun r _ => differentiableAt_hurwitzZeta _ hs), hev.deriv_eq, hD.deriv,
    ofReal_log (Nat.cast_nonneg k), ofReal_natCast]
  ring

/-! ### §25.11(v) Special values (throughout `Re a > 0`) -/

/-- **`ζ(s, 1/2) = (2^s - 1) ζ(s)`** (DLMF 25.11.11) for every `s ≠ 1`. (The natural-number case is
`DLMF.Gamma.hurwitzZeta_one_half_nat`.) -/
@[dlmf 25.11.E11]
theorem hurwitzZeta_one_half {s : ℂ} (hs : s ≠ 1) :
    hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) s = (2 ^ s - 1) * riemannZeta s := by
  have h := q25b_sum_hurwitzZeta_rat (k := 2) (by norm_num) hs
  simpa using h

/-- **Polygamma values** (DLMF 25.11.12): `ζ(n+1, a) = (-1)^{n+1} ψ⁽ⁿ⁾(a)/n!` for `n ≥ 1` and
complex `Re a > 0`. (The real case `0 < a ≤ 1` for Mathlib's function is
`DLMF.Gamma.polygamma_eq_hurwitzZeta`.) -/
@[dlmf 25.11.E12]
theorem hurwitzZetaComplex_nat_eq_polygamma {n : ℕ} (hn : 1 ≤ n) {a : ℂ} (ha : 0 < a.re) :
    hurwitzZetaComplex (n + 1) a = (-1) ^ (n + 1) * DLMF.Gamma.polygamma n a / n ! := by
  have hmem : a ∈ DLMF.Gamma.notNegNat := fun m h => by
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hH := hasSum_hurwitzZetaComplex (s := ((n + 1 : ℕ) : ℂ)) (by simp; omega)
    (fun m h => hmem m h)
  rw [DLMF.Gamma.polygamma_eq_tsum (by omega) hmem, show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by
    push_cast; ring, ← hH.tsum_eq]
  have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hsum :
      ∑' k : ℕ, (a + k) ^ (-1 - n : ℤ) = ∑' k : ℕ, 1 / ((k : ℂ) + a) ^ ((n + 1 : ℕ) : ℂ) := by
    congr 1; funext k
    rw [DLMF.Gamma.zpow_neg_one_sub_nat_eq, cpow_natCast, add_comm]
  rw [hsum]
  field_simp
  rw [show ((-1 : ℂ) ^ (n + 1)) ^ 2 = 1 by rw [← pow_mul, mul_comm, pow_mul]; simp, mul_one]

lemma q25b_bernoulli_eval_add_one (n : ℕ) (x : ℂ) :
    ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval (x + 1) =
      ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval x + n * x ^ (n - 1) := by
  have h := congrArg (Polynomial.aeval x) (Polynomial.bernoulli_comp_one_add_X n)
  simp only [Polynomial.aeval_comp, map_add, map_one, Polynomial.aeval_X, nsmul_eq_mul] at h
  simp only [Polynomial.eval_map_algebraMap]
  rw [add_comm x 1, h]
  simp

lemma q25b_poch_neg_nat (n j : ℕ) : poch (-(n : ℂ)) j = (-1) ^ j * (n.descFactorial j : ℂ) := by
  rw [poch, ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]

/-- Sum over `range (2 (M+1))` as a sum over pairs. -/
lemma q25b_sum_range_two_mul {M : Type*} [AddCommMonoid M] (T : ℕ → M) (K : ℕ) :
    ∑ i ∈ Finset.range (2 * K), T i = ∑ k ∈ Finset.range K, (T (2 * k) + T (2 * k + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, add_assoc]

lemma q25b_bernoulli_eval_eq_sum (n : ℕ) (w : ℂ) :
    ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval w =
      ∑ i ∈ Finset.range (n + 1), (bernoulli i : ℂ) * (n.choose i : ℂ) * w ^ (n - i) := by
  rw [Polynomial.bernoulli, Polynomial.map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Polynomial.eval_monomial]

/-- The Euler–Maclaurin correction terms at `s = -n` sum to `-B_{n+1}(w)/(n+1)`. -/
lemma q25b_emTail_neg_nat (n : ℕ) (w : ℂ) {M : ℕ} (hM : n ≤ 2 * M) :
    w ^ (1 - -(n : ℂ)) / (-(n : ℂ) - 1) + w ^ (-(-(n : ℂ))) / 2 +
      ∑ k ∈ Finset.range M, (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2).factorial : ℂ) *
        poch (-(n : ℂ)) (2 * k + 1) * w ^ (-(-(n : ℂ)) - (2 * k + 1)) =
      -((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)).eval w / (n + 1) := by
  set T : ℕ → ℂ := fun i => (bernoulli i : ℂ) * ((n + 1).choose i : ℂ) * w ^ (n + 1 - i) with hT
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hsum : ((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)).eval w =
      T 0 + T 1 + ∑ k ∈ Finset.range M, T (2 * k + 2) := by
    rw [q25b_bernoulli_eval_eq_sum]
    have h1 : ∑ i ∈ Finset.range (n + 1 + 1), T i = ∑ i ∈ Finset.range (2 * (M + 1)), T i := by
      refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun i _ hi => ?_
      simp only [Finset.mem_range, not_lt] at hi
      simp [T, Nat.choose_eq_zero_of_lt (by omega : n + 1 < i)]
    rw [h1, q25b_sum_range_two_mul, Finset.sum_range_succ']
    have hodd : ∀ k : ℕ, T (2 * (k + 1) + 1) = 0 := fun k => by
      simp only [T]
      rw [bernoulli_eq_zero_of_odd ⟨k + 1, by ring⟩ (by omega)]
      simp
    simp only [hodd, add_zero, mul_zero, zero_add]
    rw [add_comm]
    congr 1
  rw [hsum]
  have hT0 : T 0 = w ^ (n + 1) := by simp [T]
  have hT1 : T 1 = -(1 / 2) * ((n : ℂ) + 1) * w ^ n := by
    simp [T, bernoulli_one]
    ring
  have hterm : ∀ k : ℕ, (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2).factorial : ℂ) *
      poch (-(n : ℂ)) (2 * k + 1) * w ^ (-(-(n : ℂ)) - (2 * k + 1)) = -T (2 * k + 2) / (n + 1) := by
    intro k
    rw [q25b_poch_neg_nat]
    simp only [T]
    rcases le_or_gt (2 * k + 1) n with hk | hk
    · rw [show -(-(n : ℂ)) - (2 * k + 1) = ((n - (2 * k + 1) : ℕ) : ℂ) by
        push_cast [Nat.cast_sub hk]; ring, cpow_natCast,
        show n + 1 - (2 * k + 2) = n - (2 * k + 1) by omega]
      have hc : ((n.descFactorial (2 * k + 1) : ℕ) : ℂ) * ((n : ℂ) + 1) =
          ((n + 1).choose (2 * k + 2) : ℂ) * ((2 * k + 2).factorial : ℂ) := by
        have h1 := Nat.succ_descFactorial_succ n (2 * k + 1)
        have h2 := Nat.descFactorial_eq_factorial_mul_choose (n + 1) (2 * k + 2)
        have : n.descFactorial (2 * k + 1) * (n + 1) = (n + 1).choose (2 * k + 2) *
            (2 * k + 2).factorial := by
          rw [mul_comm, ← h1, h2, mul_comm]
        exact_mod_cast this
      have hf : ((2 * k + 2).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      rw [pow_succ, show (-1 : ℂ) ^ (2 * k) = 1 by rw [pow_mul]; simp]
      field_simp
      linear_combination (-(bernoulli (2 * k + 2) : ℂ) * w ^ (n - (2 * k + 1))) * hc
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.choose_eq_zero_of_lt (by omega)]
      simp
  simp_rw [hterm]
  rw [← Finset.sum_div, hT0, hT1, show (1 : ℂ) - -(n : ℂ) = ((n + 1 : ℕ) : ℂ) by push_cast; ring,
    show -(-(n : ℂ)) = ((n : ℕ) : ℂ) by ring, cpow_natCast, cpow_natCast,
    show -(n : ℂ) - 1 = -((n : ℂ) + 1) by ring, Finset.sum_neg_distrib]
  field_simp
  ring

/-- At `s = -n` the Euler–Maclaurin sequence is constant, equal to `-B_{n+1}(a)/(n+1)`
(Faulhaber), for every complex `a`. -/
lemma q25b_emSeq_neg_nat (n : ℕ) (a : ℂ) (N : ℕ) :
    z25b_emSeq (-(n : ℂ)) a N = -((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)).eval a /
      (n + 1) := by
  have hM : n ≤ 2 * (⌈(1 - (-(n : ℂ)).re) / 2⌉₊ + 1) := by
    have := Nat.le_ceil ((1 - (-(n : ℂ)).re) / 2)
    simp only [neg_re, natCast_re, sub_neg_eq_add] at this ⊢
    have h2 : ((n : ℝ) + 1) / 2 ≤ ⌈(1 + (n : ℝ)) / 2⌉₊ := by rw [add_comm]; exact this
    have : (n : ℝ) ≤ 2 * ((⌈(1 + (n : ℝ)) / 2⌉₊ : ℕ) + 1 : ℝ) := by linarith
    exact_mod_cast this
  unfold z25b_emSeq
  rw [add_assoc, add_assoc, ← add_assoc ((a + N) ^ (1 - -(n : ℂ)) / (-(n : ℂ) - 1)),
    q25b_emTail_neg_nat n (a + N) hM]
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [neg_neg, cpow_natCast]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ, ← add_assoc,
      q25b_bernoulli_eval_add_one (n + 1) (a + N)]
    field_simp at ih ⊢
    simp only [Nat.add_sub_cancel] at ih ⊢
    push_cast at ih ⊢
    linear_combination ih

/-- **`ζ(0, a) = 1/2 - a`** (DLMF 25.11.13), `Re a > 0`. -/
@[dlmf 25.11.E13]
theorem hurwitzZetaComplex_zero {a : ℂ} (ha : 0 < a.re) :
    hurwitzZetaComplex 0 a = 1 / 2 - a := by
  have _ := ha
  have h : hurwitzZetaComplex 0 a =
      -((Polynomial.bernoulli (0 + 1)).map (algebraMap ℚ ℂ)).eval a / ((0 : ℕ) + 1) := by
    rw [z25b_hurwitzZetaComplex_eq_limUnder]
    have : z25b_emSeq 0 a = fun _ =>
        -((Polynomial.bernoulli (0 + 1)).map (algebraMap ℚ ℂ)).eval a / ((0 : ℕ) + 1) := by
      funext N; have := q25b_emSeq_neg_nat 0 a N; simpa using this
    rw [this]
    exact tendsto_const_nhds.limUnder_eq
  rw [h, q25b_bernoulli_eval_eq_sum]
  simp [Finset.sum_range_succ, bernoulli_one]
  ring

/-- `ζ(0, x) = 1/2 - x` for Mathlib's Hurwitz zeta function, `0 < x ≤ 1` (DLMF 25.11.13). -/
@[dlmf 25.11.E13]
theorem r25b_hurwitzZeta_zero {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    hurwitzZeta (x : UnitAddCircle) 0 = 1 / 2 - x := by
  rw [← r25b_hurwitzZetaComplex_mathlib hx hx1 zero_ne_one, hurwitzZetaComplex_zero (by simpa)]

/-- **`hasSum_hurwitzZetaComplex_taylor` is false at `s = 0`** (and, similarly, at every
`s = 0, -1, -2, …`): the terms with `n + s = 1` involve the pole of `ζ`, where DLMF's product
`(s)_n ζ(n+s)` is a limit but Lean's `poch 0 n · ζ(1)` is `0`. At `s = 0`, `a = 1/2` the series
sums to `ζ(0) = -1/2`, while `ζ(0, 1/2) = 0`. -/
theorem r25b_hasSum_hurwitzZetaComplex_taylor_counterexample :
    ¬ HasSum (fun n : ℕ => poch 0 n / n ! * riemannZeta (n + 0) * (1 - 1 / 2 : ℂ) ^ n)
      (hurwitzZetaComplex 0 (1 / 2)) := by
  intro h
  have h0 : hurwitzZetaComplex 0 (1 / 2) = 0 := by
    rw [hurwitzZetaComplex_zero (by norm_num)]; ring
  have hs : HasSum (fun n : ℕ => poch 0 n / n ! * riemannZeta (n + 0) * (1 - 1 / 2 : ℂ) ^ n)
      (-1 / 2) := by
    convert hasSum_single (f := fun n : ℕ => poch 0 n / n ! * riemannZeta (n + 0) *
      (1 - 1 / 2 : ℂ) ^ n) 0 (fun n hn => by simp [poch, hn]) using 1
    simp [poch, riemannZeta_zero]
  rw [h0] at h
  have := h.unique hs
  norm_num at this

/-- **Values at negative integers** (DLMF 25.11.14): `ζ(-n, a) = -B_{n+1}(a)/(n+1)`,
`n = 0, 1, 2, …`, `Re a > 0`. (Mathlib's `HurwitzZeta.hurwitzZeta_neg_nat` is the case `n ≥ 1`,
real `0 ≤ a ≤ 1`.) -/
@[dlmf 25.11.E14]
theorem hurwitzZetaComplex_neg_nat (n : ℕ) {a : ℂ} (ha : 0 < a.re) :
    hurwitzZetaComplex (-n) a =
      -((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)).eval a / (n + 1) := by
  have _ := ha
  rw [z25b_hurwitzZetaComplex_eq_limUnder]
  have : z25b_emSeq (-(n : ℂ)) a = fun _ =>
      -((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)).eval a / (n + 1) :=
    funext (q25b_emSeq_neg_nat n a)
  rw [this]
  exact tendsto_const_nhds.limUnder_eq

/-- `(r w)^t = r^t w^t` for real `r > 0` and `w ≠ 0`. -/
lemma r25b_ofReal_mul_cpow {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ≠ 0) (t : ℂ) :
    ((r : ℂ) * w) ^ t = (r : ℂ) ^ t * w ^ t := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hr' hw), cpow_def_of_ne_zero hr', cpow_def_of_ne_zero hw,
    log_ofReal_mul hr hw, ← Complex.exp_add, Complex.ofReal_log hr.le]
  ring_nf

/-- `a + n ≠ 0` for `Re a > 0`. -/
lemma r25b_ne_neg_nat_of_re_pos {a : ℂ} (ha : 0 < a.re) : ∀ n : ℕ, a + n ≠ 0 := fun n h => by
  have := congrArg Complex.re h; simp at this; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- **Multiplication formula** (DLMF 25.11.15): `ζ(s, ka) = k^{-s} ∑_{n=0}^{k-1} ζ(s, a + n/k)`
for `s ≠ 1`, `k = 1, 2, 3, …`, `Re a > 0`. -/
@[dlmf 25.11.E15]
theorem hurwitzZetaComplex_mul {s : ℂ} (hs : s ≠ 1) {k : ℕ} (hk : 1 ≤ k) {a : ℂ}
    (ha : 0 < a.re) :
    hurwitzZetaComplex s (k * a) =
      (k : ℂ) ^ (-s) * ∑ n ∈ Finset.range k, hurwitzZetaComplex s (a + n / k) := by
  have : NeZero k := ⟨by omega⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hka : 0 < ((k : ℂ) * a).re := by simp; positivity
  have han : ∀ n : ℕ, 0 < (a + n / k).re := fun n => by
    have : ((n : ℂ) / k).re = n / k := by
      rw [show ((n : ℂ) / k) = ((n / k : ℝ) : ℂ) by push_cast; rfl, ofReal_re]
    rw [add_re, this]; positivity
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hf' : DifferentiableOn ℂ (fun t => hurwitzZetaComplex t (k * a)) {1}ᶜ :=
    fun t ht => (r25b_differentiableAt_hurwitzZetaComplex ht
      (r25b_ne_neg_nat_of_re_pos hka)).differentiableWithinAt
  have hg' : DifferentiableOn ℂ (fun t => (k : ℂ) ^ (-t) *
      ∑ n ∈ Finset.range k, hurwitzZetaComplex t (a + n / k)) {1}ᶜ := by
    intro t ht
    refine (DifferentiableAt.mul ((differentiableAt_id.neg).const_cpow (Or.inl hkC))
      (DifferentiableAt.fun_sum fun n _ => r25b_differentiableAt_hurwitzZetaComplex ht
        (r25b_ne_neg_nat_of_re_pos (han n)))).differentiableWithinAt
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (rank_real_complex ▸ Nat.one_lt_ofNat) _).isPreconnected
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine (hf'.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hg'.analyticOnNhd hU) hpc
    h2 ?_ hs
  have hopen : IsOpen {t : ℂ | 1 < t.re} := isOpen_lt continuous_const continuous_re
  filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with t ht
  have hne : ∀ b : ℂ, 0 < b.re → ∀ m : ℕ, b ≠ -m := fun b hb m h => by
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hL := hasSum_hurwitzZetaComplex ht (hne _ hka)
  have hR := fun n : ℕ => hasSum_hurwitzZetaComplex ht (hne _ (han n))
  rw [← hL.tsum_eq, Nat.sumByResidueClasses hL.summable k, q25b_sum_zmod_eq_sum_range,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_range] at hn
  rw [← (hR n).tsum_eq, ← tsum_mul_left]
  congr 1; funext j
  have hw : ((j : ℂ) + (a + n / k)) ≠ 0 := by
    have := (r25b_ne_neg_nat_of_re_pos (han n)) j; rwa [add_comm] at this
  have heq : (((((n : ZMod k).val + k * j : ℕ)) : ℂ) + k * a) =
      ((k : ℝ) : ℂ) * ((j : ℂ) + (a + n / k)) := by
    rw [ZMod.val_natCast_of_lt hn]
    push_cast
    field_simp
    ring
  rw [heq, r25b_ofReal_mul_cpow hk0 hw, cpow_neg]
  push_cast
  field_simp


/-- **Rational parameters** (DLMF 25.11.16): for integers `1 ≤ h ≤ k`,
`ζ(1-s, h/k) = (2Γ(s)/(2πk)^s) ∑_{r=1}^{k} cos(πs/2 - 2πrh/k) ζ(s, r/k)`.
DLMF requires `s ≠ 0, 1`; we also exclude `s = -1, -2, …` (implicit condition: there `Γ(s)` has a
pole and the right side is a limit; with Lean's `Γ(-m) = 0` the literal identity fails). -/
@[dlmf 25.11.E16]
theorem hurwitzZeta_one_sub_rat {s : ℂ} (hs1 : s ≠ 1) (hs : ∀ m : ℕ, s ≠ -m) {h k : ℕ}
    (hh : 1 ≤ h) (hhk : h ≤ k) :
    hurwitzZeta ((h / k : ℝ) : UnitAddCircle) (1 - s) =
      2 * Gamma s / (2 * π * k) ^ s * ∑ r ∈ Finset.Icc 1 k,
        Complex.cos (π * s / 2 - 2 * π * r * h / k) *
          hurwitzZeta ((r / k : ℝ) : UnitAddCircle) s := by
  have : NeZero k := ⟨by omega⟩
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- expZeta at a rational point as a combination of Hurwitz zeta functions
  have hE : ∀ (j : ℤ), expZeta (((j : ZMod k)).toAddCircle) s = (k : ℂ) ^ (-s) *
      ∑ r ∈ Finset.range k, cexp (2 * π * I * j * r / k) *
        hurwitzZeta ((r / k : ℝ) : UnitAddCircle) s := by
    intro j
    rw [← ZMod.LFunction_stdAddChar_eq_expZeta _ _ (Or.inr hs1), ZMod.LFunction,
      q25b_sum_zmod_eq_sum_range]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ZMod.toAddCircle_natCast, show ((j : ZMod k) * (r : ZMod k)) = ((j * r : ℤ) : ZMod k) by
      push_cast; ring, ZMod.stdAddChar_coe]
    push_cast; ring_nf
  have ha : ((h / k : ℝ) : UnitAddCircle) = ((h : ℤ) : ZMod k).toAddCircle := by
    rw [Int.cast_natCast, ZMod.toAddCircle_natCast]
  have ha' : -((h / k : ℝ) : UnitAddCircle) = ((-(h : ℤ) : ℤ) : ZMod k).toAddCircle := by
    rw [ha, Int.cast_neg, map_neg]
  rw [hurwitzZeta_one_sub _ hs (Or.inr hs1), ha', ha, hE, hE]
  -- the sum over `0 ≤ r < k` as the sum over `1 ≤ r ≤ k`
  set g : ℕ → ℂ := fun r => (cexp (-π * I * s / 2) * cexp (2 * π * I * (h : ℤ) * r / k) +
      cexp (π * I * s / 2) * cexp (2 * π * I * ((-(h : ℤ) : ℤ) : ℂ) * r / k)) *
    hurwitzZeta ((r / k : ℝ) : UnitAddCircle) s with hg
  have hg0 : g 0 = g k := by
    simp only [hg, Nat.cast_zero, mul_zero, zero_div, Complex.exp_zero, mul_one]
    rw [div_self (by exact_mod_cast hk0 : (k : ℝ) ≠ 0)]
    have h1 : cexp (2 * π * I * (h : ℤ) * k / k) = 1 := by
      rw [mul_div_assoc, div_self hk0, mul_one, show 2 * π * I * ((h : ℤ) : ℂ) =
        (h : ℕ) * (2 * π * I) by push_cast; ring, Complex.exp_nat_mul_two_pi_mul_I]
    have h2 : cexp (2 * π * I * ((-(h : ℤ) : ℤ) : ℂ) * k / k) = 1 := by
      rw [mul_div_assoc, div_self hk0, mul_one, show 2 * π * I * ((-(h : ℤ) : ℤ) : ℂ) =
        -((h : ℕ) * (2 * π * I)) by push_cast; ring, Complex.exp_neg,
        Complex.exp_nat_mul_two_pi_mul_I, inv_one]
    rw [h1, h2, mul_one, mul_one]
    congr 2
    rw [AddCircle.coe_period]
    rfl
  have hsum : ∑ r ∈ Finset.range k, g r = ∑ r ∈ Finset.Icc 1 k, g r := by
    have h1 := Finset.sum_range_succ g k
    have h2 := Finset.sum_range_succ' g k
    have h3 : ∑ r ∈ Finset.Icc 1 k, g r = ∑ r ∈ Finset.range k, g (r + 1) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      simp [add_comm]
    rw [h3]; linear_combination h1.symm.trans h2 + hg0
  have hcos : ∀ r : ℕ, g r = 2 * (Complex.cos (π * s / 2 - 2 * π * r * h / k) *
      hurwitzZeta ((r / k : ℝ) : UnitAddCircle) s) := by
    intro r
    simp only [hg, Complex.cos, ← Complex.exp_add]
    rw [← mul_assoc, mul_div_cancel₀ _ (two_ne_zero' ℂ), add_comm (cexp _)]
    congr 2
    · congr 1; push_cast; ring
    · congr 1; push_cast; ring
  have key : cexp (-π * I * s / 2) * ((k : ℂ) ^ (-s) * ∑ r ∈ Finset.range k,
        cexp (2 * π * I * ((h : ℤ) : ℂ) * r / k) * hurwitzZeta ((r / k : ℝ) : UnitAddCircle) s) +
      cexp (π * I * s / 2) * ((k : ℂ) ^ (-s) * ∑ r ∈ Finset.range k,
        cexp (2 * π * I * ((-(h : ℤ) : ℤ) : ℂ) * r / k) *
          hurwitzZeta ((r / k : ℝ) : UnitAddCircle) s) =
      (k : ℂ) ^ (-s) * ∑ r ∈ Finset.range k, g r := by
    simp only [hg, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hp : (2 * π : ℂ) ^ (-s) * (k : ℂ) ^ (-s) = 1 / (2 * π * k) ^ s := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl,
      show (k : ℂ) = ((k : ℝ) : ℂ) by push_cast; rfl,
      ← mul_cpow_ofReal_nonneg (by positivity) (by positivity), cpow_neg, one_div]
  rw [mul_assoc, key, hsum, Finset.sum_congr rfl fun r _ => hcos r, ← Finset.mul_sum]
  linear_combination (Gamma s * 2 * ∑ r ∈ Finset.Icc 1 k,
      Complex.cos (π * s / 2 - 2 * π * r * h / k) *
        hurwitzZeta ((r / k : ℝ) : UnitAddCircle) s) * hp

/-! ### §25.11(vi) Derivatives -/

/-- **`a`-derivative** (DLMF 25.11.17): `∂ζ(s,a)/∂a = -s ζ(s+1, a)` for `s ≠ 0, 1`, `Re a > 0`. -/
@[dlmf 25.11.E17]
theorem hasDerivAt_hurwitzZetaComplex_param {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) {a : ℂ}
    (ha : 0 < a.re) :
    HasDerivAt (hurwitzZetaComplex s) (-s * hurwitzZetaComplex (s + 1) a) a :=
  r25b_hasDerivAt_hurwitzZetaComplex_param hs0 hs1 ha

/-- `(x + a)^r` is integrable on `(0, ∞)` for `a > 0`, `r < -1`. -/
lemma s25b_integrableOn_add_rpow {a r : ℝ} (ha : 0 < a) (hr : r < -1) :
    IntegrableOn (fun x : ℝ => (x + a) ^ r) (Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ => ‖((1 : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ ((-r : ℝ) : ℂ)‖)
      (Ioi 0) := (r25b_integrableOn_bdd_div_cpow (f := fun _ => (1 : ℝ)) measurable_const
    (B := 1) (fun _ => by simp) (w := ((-r : ℝ) : ℂ)) (by simp; linarith) ha le_rfl).norm
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hxa : 0 < x + a := by linarith [mem_Ioi.mp hx]
  simp only [ofReal_one, norm_div, norm_one]
  rw [norm_cpow_eq_rpow_re_of_pos hxa, ofReal_re, Real.rpow_neg hxa.le, one_div, inv_inv]

/-- `|log y| ≤ (y^δ + y^{-δ})/δ` for `y > 0`, `δ > 0`. -/
lemma s25b_abs_log_le {y δ : ℝ} (hy : 0 < y) (hδ : 0 < δ) :
    |Real.log y| ≤ (y ^ δ + y ^ (-δ)) / δ := by
  have h1 := Real.log_le_rpow_div hy.le hδ
  have h2 := Real.log_le_rpow_div (inv_pos.mpr hy).le hδ
  rw [Real.log_inv, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le] at h2
  have h3 : 0 ≤ y ^ δ / δ := by positivity
  have h4 : 0 ≤ y ^ (-δ) / δ := by positivity
  rw [add_div]
  rcases le_or_gt 0 (Real.log y) with h | h
  · rw [abs_of_nonneg h]; linarith
  · rw [abs_of_neg h]; linarith

/-- **Differentiation under the integral sign** for `∫_0^∞ f(x)/(x+a)^{s+2} dx` with bounded
measurable `f`, `a > 0`, `Re s > -1`. -/
lemma s25b_hasDerivAt_integral_div_cpow {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : -1 < s.re) :
    HasDerivAt (fun t => ∫ x in Ioi (0 : ℝ), ((f x : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (t + 2))
      (-∫ x in Ioi (0 : ℝ), ((f x : ℝ) : ℂ) * (Real.log (x + a) : ℂ) /
        (((x + a : ℝ)) : ℂ) ^ (s + 2)) s := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set ε := (s.re + 1) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  set lo := s.re - ε + 2
  set hi := s.re + ε + 2
  have hlo : 1 < lo := by simp only [lo, ε]; linarith
  set δ := (lo - 1) / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  set F : ℂ → ℝ → ℂ := fun t x => ((f x : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (t + 2)
  set F' : ℂ → ℝ → ℂ := fun t x =>
    -(((f x : ℝ) : ℂ) * (Real.log (x + a) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (t + 2))
  have hmeasF : ∀ t, Measurable (F t) := fun t =>
    (Complex.measurable_ofReal.comp hf).div
      ((Complex.measurable_ofReal.comp (measurable_id.add_const a)).pow_const _)
  have hmeasF' : Measurable (F' s) :=
    (((Complex.measurable_ofReal.comp hf).mul (Complex.measurable_ofReal.comp
      (Real.measurable_log.comp (measurable_id.add_const a)))).div
      ((Complex.measurable_ofReal.comp (measurable_id.add_const a)).pow_const _)).neg
  set bound : ℝ → ℝ := fun x => B / δ * (((x + a) ^ (δ - lo) + (x + a) ^ (δ - hi)) +
    ((x + a) ^ (-δ - lo) + (x + a) ^ (-δ - hi)))
  have hbound : IntegrableOn bound (Ioi 0) := by
    refine Integrable.const_mul ?_ _
    refine Integrable.add (Integrable.add ?_ ?_) (Integrable.add ?_ ?_) <;>
      exact s25b_integrableOn_add_rpow ha (by simp only [δ, hi, lo, ε] at *; linarith)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := F) (F' := F') (x₀ := s) (bound := bound) (Metric.ball_mem_nhds s hε)
    (Eventually.of_forall fun t => (hmeasF t).aestronglyMeasurable)
    (r25b_integrableOn_bdd_div_cpow hf hB (w := s + 2) (by simp; linarith) ha le_rfl)
    hmeasF'.aestronglyMeasurable ?_ hbound ?_
  · simpa only [F, F', integral_neg] using h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx t ht
    have hxa : 0 < x + a := by linarith [mem_Ioi.mp hx]
    rw [Metric.mem_ball, dist_eq_norm] at ht
    have := abs_re_le_norm (t - s)
    simp only [sub_re] at this
    have h1 : lo ≤ t.re + 2 := by simp only [lo]; linarith [neg_abs_le (t.re - s.re)]
    have h2 : t.re + 2 ≤ hi := by simp only [hi]; linarith [le_abs_self (t.re - s.re)]
    simp only [F', norm_neg, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_cpow_eq_rpow_re_of_pos hxa]
    simp only [add_re, re_ofNat]
    have hlog := s25b_abs_log_le hxa hδ
    have hp : (x + a) ^ (-(t.re + 2)) ≤ (x + a) ^ (-lo) + (x + a) ^ (-hi) := by
      have := s25b_rpow_le_add (x := x + a) (σ := t.re + 1) (σ₀ := lo - 1) (R := hi - 1) hxa
        (by linarith) (by linarith)
      convert this using 2 <;> ring_nf
    rw [div_eq_mul_inv, ← Real.rpow_neg hxa.le]
    calc |f x| * |Real.log (x + a)| * (x + a) ^ (-(t.re + 2))
        ≤ B * ((((x + a) ^ δ + (x + a) ^ (-δ)) / δ) * ((x + a) ^ (-lo) + (x + a) ^ (-hi))) := by
          rw [mul_assoc]
          exact mul_le_mul (hB x) (mul_le_mul hlog hp (by positivity) (by positivity))
            (by positivity) hB0
      _ = bound x := by
          simp only [bound]
          rw [Real.rpow_sub hxa, Real.rpow_sub hxa, Real.rpow_sub hxa, Real.rpow_sub hxa,
            Real.rpow_neg hxa.le, Real.rpow_neg hxa.le, Real.rpow_neg hxa.le]
          field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx t _
    have hxa : 0 < x + a := by linarith [mem_Ioi.mp hx]
    have hy0 : (((x + a : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hxa.ne'
    have hlin : HasDerivAt (fun u : ℂ => -(u + 2)) (-1) t := by
      have := ((hasDerivAt_id t).add_const (2 : ℂ)).fun_neg
      simpa only [id] using this
    have hd := hlin.const_cpow (c := (((x + a : ℝ)) : ℂ)) (Or.inl hy0)
    have hd2 := hd.const_mul ((f x : ℝ) : ℂ)
    simp only [F, F']
    convert hd2 using 1
    · funext u; rw [div_eq_mul_inv, ← cpow_neg]
    · rw [← Complex.ofReal_log hxa.le, div_eq_mul_inv, ← cpow_neg]; ring


/-- `B̃₂ - B₂` is bounded. -/
lemma s25b_exists_bound_periodicBernoulli_two :
    ∃ B, ∀ x, |periodicBernoulli 2 x - (bernoulli 2 : ℝ)| ≤ B := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ y ∈ Icc (0 : ℝ) 1, ‖bernoulliFun 2 y‖ ≤ B :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc (continuous_bernoulliFun 2).continuousOn
  refine ⟨B + |(bernoulli 2 : ℝ)|, fun x => ?_⟩
  have := hB _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have h2 := abs_sub (periodicBernoulli 2 x) (bernoulli 2 : ℝ)
  rw [Real.norm_eq_abs] at this
  simp only [periodicBernoulli] at h2 ⊢
  linarith

/-- **`s`-derivative via `B̃₂`** (DLMF 25.11.19), `Re s > -1`, `s ≠ 1`, real `a > 0`. -/
@[dlmf 25.11.E19]
theorem deriv_hurwitzZetaComplex_eulerMaclaurin {s : ℂ} (hs : s ≠ 1) (hs0 : -1 < s.re) {a : ℝ}
    (ha : 0 < a) :
    deriv (fun t => hurwitzZetaComplex t a) s =
      -(Real.log a : ℂ) / (a : ℂ) ^ s * (1 / 2 + a / (s - 1)) - (a : ℂ) ^ (1 - s) / (s - 1) ^ 2 +
      s * (s + 1) / 2 * (∫ x in Ioi (0 : ℝ), ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) *
        (Real.log (x + a) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (s + 2)) -
      (2 * s + 1) / 2 * ∫ x in Ioi (0 : ℝ),
        ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (s + 2) := by
  obtain ⟨B, hB⟩ := s25b_exists_bound_periodicBernoulli_two
  set J : ℂ → ℂ := fun t => ∫ x in Ioi (0 : ℝ),
    ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (t + 2)
  have hJ := s25b_hasDerivAt_integral_div_cpow ((measurable_periodicBernoulli 2).sub_const _)
    hB ha hs0
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hev : (fun t => hurwitzZetaComplex t a) =ᶠ[𝓝 s]
      fun t => (a : ℂ) ^ (-t) * (1 / 2 + a / (t - 1)) - t * (t + 1) / 2 * J t := by
    have hU : IsOpen ({t : ℂ | -1 < t.re} \ {1}) :=
      (isOpen_lt continuous_const continuous_re).sdiff isClosed_singleton
    filter_upwards [hU.mem_nhds ⟨hs0, hs⟩] with t ht
    exact hurwitzZetaComplex_eulerMaclaurin_two ht.2 ht.1 ha
  rw [hev.deriv_eq]
  have hA : HasDerivAt (fun t : ℂ => (a : ℂ) ^ (-t)) ((a : ℂ) ^ (-s) * Complex.log a * (-1)) s :=
    (hasDerivAt_neg s).const_cpow (Or.inl ha0)
  have hR : HasDerivAt (fun t : ℂ => 1 / 2 + (a : ℂ) / (t - 1)) (-(a : ℂ) / (s - 1) ^ 2) s := by
    have := ((hasDerivAt_id s).sub_const (1 : ℂ)).inv hs1
    have := (this.const_mul (a : ℂ)).const_add (1 / 2 : ℂ)
    convert this using 1
    · funext t; simp [div_eq_mul_inv]
    · simp; ring
  have hP : HasDerivAt (fun t : ℂ => t * (t + 1) / 2) ((2 * s + 1) / 2) s := by
    have := ((hasDerivAt_id' s).fun_mul ((hasDerivAt_id' s).add_const (1 : ℂ))).div_const 2
    convert this using 1; ring
  have hD := (hA.fun_mul hR).fun_sub (hP.fun_mul hJ)
  rw [hD.deriv]
  rw [← Complex.ofReal_log ha.le, cpow_neg]
  have has : (a : ℂ) ^ s ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; simp [ha0]
  have h1s : (a : ℂ) ^ (1 - s) = a * ((a : ℂ) ^ s)⁻¹ := by
    rw [sub_eq_add_neg, cpow_add _ _ ha0, cpow_one, cpow_neg]
  rw [h1s]
  field_simp
  ring

/-- `ζ'(0, b) = (b - 1/2) ln b - b - (1/2) ∫_0^∞ (B̃₂(x) - B₂)/(x+b)² dx` for `b > 0`. -/
lemma s25b_deriv_hurwitzZetaComplex_zero_eq {b : ℝ} (hb : 0 < b) :
    deriv (fun s => hurwitzZetaComplex s b) 0 =
      ((b : ℂ) - 1 / 2) * (Real.log b : ℂ) - b - 1 / 2 * ∫ x in Ioi (0 : ℝ),
        ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) / (((x + b : ℝ)) : ℂ) ^ (2 : ℂ) := by
  rw [deriv_hurwitzZetaComplex_eulerMaclaurin (by norm_num) (by norm_num) hb, zero_add,
    cpow_zero, sub_zero, cpow_one]
  rw [show (0 : ℂ) + 2 = 2 by norm_num]
  norm_num
  ring

/-- The integral `∫_0^∞ (B̃₂(x) - B₂)/(x+a+n)² dx` tends to `0` as `n → ∞`. -/
lemma s25b_tendsto_integral_periodicBernoulli_two {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) /
      (((x + (a + n) : ℝ)) : ℂ) ^ (2 : ℂ)) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := s25b_exists_bound_periodicBernoulli_two
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hint := s25b_integrableOn_add_rpow ha (r := -2) (by norm_num)
  have hnorm : ∀ (n : ℕ) (x : ℝ), 0 < x → ‖((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) /
      (((x + (a + n) : ℝ)) : ℂ) ^ (2 : ℂ)‖ ≤ B * (x + (a + n)) ^ (-2 : ℝ) := by
    intro n x hx0
    have hxa : 0 < x + (a + n) := by positivity
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, norm_cpow_eq_rpow_re_of_pos hxa, ofReal_re,
      div_eq_mul_inv, ← Real.rpow_neg hxa.le]
    exact mul_le_mul_of_nonneg_right (hB x) (by positivity)
  rw [show (0 : ℂ) = ∫ x in Ioi (0 : ℝ), (0 : ℂ) by simp]
  refine tendsto_integral_of_dominated_convergence (fun x => B * (x + a) ^ (-2 : ℝ))
    (fun n => ?_) (hint.const_mul B) (fun n => ?_) ?_
  · exact ((Complex.measurable_ofReal.comp ((measurable_periodicBernoulli 2).sub_const _)).div
      ((Complex.measurable_ofReal.comp
        (measurable_id.add_const _)).pow_const _)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    refine (hnorm n x hx0).trans (mul_le_mul_of_nonneg_left ?_ hB0)
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    refine squeeze_zero_norm (fun n => hnorm n x hx0) ?_
    have h1 : Tendsto (fun n : ℕ => x + (a + n)) atTop atTop :=
      tendsto_atTop_add_const_left _ x (tendsto_atTop_add_const_left _ a
        tendsto_natCast_atTop_atTop)
    have := ((tendsto_rpow_neg_atTop (y := 2) (by norm_num)).comp h1).const_mul B
    rw [mul_zero] at this
    exact this

/-- **Lerch's formula** (DLMF 25.11.18): `ζ'(0, a) = ln Γ(a) - ½ ln(2π)` for real `a > 0`, the
prime denoting `∂/∂s`. -/
@[dlmf 25.11.E18]
theorem deriv_hurwitzZetaComplex_zero {a : ℝ} (ha : 0 < a) :
    deriv (fun s => hurwitzZetaComplex s a) 0 =
      (Real.log (Real.Gamma a) - Real.log (2 * π) / 2 : ℝ) := by
  set G : ℕ → ℂ := fun n => deriv (fun s => hurwitzZetaComplex s (a + n : ℝ)) 0 -
    (Real.log (Real.Gamma (a + n)) : ℂ)
  -- periodicity
  have hstep : ∀ n : ℕ, G (n + 1) = G n := by
    intro n
    set b : ℝ := a + n
    have hb : 0 < b := by positivity
    have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    have hbm : ∀ m : ℕ, (b : ℂ) ≠ -m := fun m h => by
      have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have hb1 : ((a + (n + 1 : ℕ) : ℝ) : ℂ) = (b : ℂ) + 1 := by simp [b]; ring
    have hev : (fun s => hurwitzZetaComplex s (b : ℂ)) =ᶠ[𝓝 0]
        fun s => hurwitzZetaComplex s ((b : ℂ) + 1) + (b : ℂ) ^ (-s) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds (show (0 : ℂ) ∈ ({1}ᶜ : Set ℂ) by simp)]
        with s hs
      exact hurwitzZetaComplex_eq_add_one hs hbm
    have hd1 := (r25b_differentiableAt_hurwitzZetaComplex (s₀ := 0) (z := (b : ℂ) + 1)
      (by norm_num) (fun m => by
        have := hbm (m + 1); intro h; apply this; push_cast; linear_combination h)).hasDerivAt
    have hd2 : HasDerivAt (fun s : ℂ => (b : ℂ) ^ (-s)) ((b : ℂ) ^ (-(0 : ℂ)) *
        Complex.log b * (-1)) 0 := (hasDerivAt_neg 0).const_cpow (Or.inl hb0)
    have hD : deriv (fun s => hurwitzZetaComplex s (b : ℂ)) 0 =
        deriv (fun s => hurwitzZetaComplex s ((b : ℂ) + 1)) 0 - Real.log b := by
      refine hev.deriv_eq.trans (((hd1.add hd2).deriv).trans ?_)
      rw [neg_zero, cpow_zero, ← Complex.ofReal_log hb.le]
      ring
    have hΓ : Real.log (Real.Gamma (a + (n + 1 : ℕ))) = Real.log (Real.Gamma b) + Real.log b := by
      rw [show a + ((n + 1 : ℕ) : ℝ) = b + 1 by simp [b]; ring, Real.Gamma_add_one hb.ne',
        Real.log_mul hb.ne' (Real.Gamma_pos_of_pos hb).ne']
      ring
    simp only [G]
    rw [hb1, hΓ, hD]
    push_cast
    ring
  have hconst : ∀ n : ℕ, G n = G 0 := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [hstep, ih]
  -- the limit
  have hlimA := (s25b_tendsto_integral_periodicBernoulli_two ha).const_mul (-(1 / 2 : ℂ))
  rw [mul_zero] at hlimA
  have hS := DLMF.Gamma.log_Gamma_stirling 0 (x := a + 1) (by linarith)
  set E : ℕ → ℝ := fun n => Real.log (Real.Gamma (a + (n + 1 : ℕ))) -
    ((a + (n + 1 : ℕ) - 1 / 2) * Real.log (a + (n + 1 : ℕ)) - (a + (n + 1 : ℕ)) +
      1 / 2 * Real.log (2 * π))
  have hE : Tendsto E atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t ^ (-(2 * ((0 : ℕ) : ℝ)) - 1)) atTop (𝓝 0) := by
      simpa using tendsto_rpow_neg_atTop (y := 1) (by norm_num)
    have h2 := (hS.trans_tendsto h1).comp tendsto_natCast_atTop_atTop
    refine h2.congr (fun n => ?_)
    have hc : (n : ℝ) + (a + 1) = a + ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    simp only [Function.comp, Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.sum_empty, add_zero,
      hc, E]
  have hlim : Tendsto (fun n : ℕ => G (n + 1)) atTop
      (𝓝 ((-(Real.log (2 * π) / 2) : ℝ) : ℂ)) := by
    have hE' := ((Complex.continuous_ofReal.tendsto 0).comp hE)
    have hA := hlimA.comp (tendsto_add_atTop_nat 1)
    have h3 := (hE'.neg.add hA).const_add (((-(Real.log (2 * π) / 2)) : ℝ) : ℂ)
    rw [Complex.ofReal_zero, neg_zero, add_zero, add_zero] at h3
    refine h3.congr (fun n => ?_)
    simp only [Function.comp, G, E]
    rw [s25b_deriv_hurwitzZetaComplex_zero_eq (by positivity)]
    push_cast
    ring
  have hG0 : G 0 = ((-(Real.log (2 * π) / 2)) : ℝ) := by
    refine tendsto_nhds_unique (f := fun _ : ℕ => G 0) (l := atTop) tendsto_const_nhds ?_
    exact hlim.congr (fun n => hconst (n + 1))
  have : G 0 = deriv (fun s => hurwitzZetaComplex s a) 0 - (Real.log (Real.Gamma a) : ℂ) := by
    simp [G]
  rw [this] at hG0
  rw [sub_eq_iff_eq_add] at hG0
  rw [hG0]
  push_cast
  ring

/-- **Higher `s`-derivatives** (DLMF 25.11.20): for `k ≥ 1` (for `k = 1` the last integral has
coefficient `0`), `Re s > -1`, `s ≠ 1`, real `a > 0`,
`(-1)^k ζ^{(k)}(s,a) = (ln a)^k a^{-s}(1/2 + a/(s-1)) + k! a^{1-s} ∑_{r=0}^{k-1}
(ln a)^r/(r!(s-1)^{k-r+1}) - (s(s+1)/2) I_k + (k(2s+1)/2) I_{k-1} - (k(k-1)/2) I_{k-2}`,
`I_j = ∫_0^∞ (B̃₂(x) - B₂)(ln(x+a))^j/(x+a)^{s+2} dx`. -/
@[dlmf 25.11.E20]
theorem iteratedDeriv_hurwitzZetaComplex {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : s ≠ 1)
    (hs0 : -1 < s.re) {a : ℝ} (ha : 0 < a) :
    let I : ℕ → ℂ := fun j => ∫ x in Ioi (0 : ℝ), ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) *
      (Real.log (x + a) : ℂ) ^ j / (((x + a : ℝ)) : ℂ) ^ (s + 2)
    (-1) ^ k * iteratedDeriv k (fun t => hurwitzZetaComplex t a) s =
      (Real.log a : ℂ) ^ k / (a : ℂ) ^ s * (1 / 2 + a / (s - 1)) +
      k ! * (a : ℂ) ^ (1 - s) * ∑ r ∈ Finset.range k,
        (Real.log a : ℂ) ^ r / (r ! * (s - 1) ^ (k - r + 1)) -
      s * (s + 1) / 2 * I k + k * (2 * s + 1) / 2 * I (k - 1) -
      k * (k - 1 : ℂ) / 2 * I (k - 2) := by
  sorry

/-- **`ζ'(1-2n, h/k)`** (DLMF 25.11.21), integers `1 ≤ h ≤ k`, `n ≥ 1`; `ψ = digamma`, primes are
`s`-derivatives, and `ζ'(1-2n)` is the derivative of Riemann's zeta function. -/
@[dlmf 25.11.E21]
theorem deriv_hurwitzZeta_one_sub_two_mul_rat {n : ℕ} (hn : 1 ≤ n) {h k : ℕ} (hh : 1 ≤ h)
    (hhk : h ≤ k) :
    deriv (hurwitzZeta ((h / k : ℝ) : UnitAddCircle)) (1 - 2 * n) =
      (digamma (2 * n) - Complex.log (2 * π * k)) *
          ((Polynomial.bernoulli (2 * n)).map (algebraMap ℚ ℂ)).eval ((h : ℂ) / k) / (2 * n) -
        (digamma (2 * n) - Complex.log (2 * π)) * bernoulli (2 * n) / (2 * n * (k : ℂ) ^ (2 * n)) +
        (-1) ^ (n + 1) * π / (2 * π * k) ^ (2 * n) * ∑ r ∈ Finset.Ico 1 k,
          Complex.sin (2 * π * r * h / k) * DLMF.Gamma.polygamma (2 * n - 1) ((r : ℂ) / k) +
        (-1) ^ (n + 1) * 2 * ((2 * n - 1 : ℕ) ! : ℂ) / (2 * π * k) ^ (2 * n) *
          ∑ r ∈ Finset.Ico 1 k, Complex.cos (2 * π * r * h / k) *
            deriv (hurwitzZeta ((r / k : ℝ) : UnitAddCircle)) (2 * n) +
        deriv riemannZeta (1 - 2 * n) / (k : ℂ) ^ (2 * n) := by
  sorry

/-- **`ζ'(1-2n, 1/2)`** (DLMF 25.11.22), `n ≥ 1`. -/
@[dlmf 25.11.E22]
theorem deriv_hurwitzZeta_one_sub_two_mul_half {n : ℕ} (hn : 1 ≤ n) :
    deriv (hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle)) (1 - 2 * n) =
      -(bernoulli (2 * n) : ℂ) * Real.log 2 / (n * 4 ^ n) -
        (2 ^ (2 * n - 1) - 1) * deriv riemannZeta (1 - 2 * n) / 2 ^ (2 * n - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hm : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  have hs : (1 : ℂ) - 2 * ((j + 1 : ℕ) : ℂ) = -((2 * j + 1 : ℕ) : ℂ) := by push_cast; ring
  have hs1 : (1 : ℂ) - 2 * ((j + 1 : ℕ) : ℂ) ≠ 1 := by
    rw [hs]; intro h; have := congrArg Complex.re h; simp at this; linarith
  have h := q25b_sum_deriv_hurwitzZeta_rat hs1 (k := 2) (by norm_num)
  simp only [show Finset.Ico 1 2 = {1} by rfl, Finset.sum_singleton, Nat.cast_one,
    Nat.cast_ofNat] at h
  rw [show ((1 : ℝ) / 2) = 1 / 2 by norm_num] at h
  rw [h, hm, hs, riemannZeta_neg_nat_eq_bernoulli, cpow_neg, cpow_natCast]
  have h2 : (2 : ℂ) ^ (2 * j + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  have h4 : (4 : ℂ) ^ (j + 1) = 2 ^ (2 * j + 1) * 2 := by
    rw [show (4 : ℂ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
  rw [h4, show (2 * j + 1 + 1 : ℕ) = 2 * (j + 1) by ring, pow_succ (-1 : ℂ),
    pow_mul (-1 : ℂ) 2 j]
  push_cast
  have hj : (2 * (j : ℂ) + 1 + 1) ≠ 0 := by norm_cast
  have hj' : ((j : ℂ) + 1) ≠ 0 := by norm_cast
  field_simp
  ring

/-- **`ζ'(1-2n, 1/3)`** (DLMF 25.11.23, **corrected**), `n ≥ 1`:
`ζ'(1-2n, 1/3) = -π(9ⁿ-1)B_{2n}/(8n√3·3^{2n-1}) - B_{2n} ln 3/(4n·3^{2n-1})
 - (-1)ⁿ ψ^{(2n-1)}(1/3)/(2√3(6π)^{2n-1}) - (3^{2n-1}-1) ζ'(1-2n)/(2·3^{2n-1})`.
DLMF 1.2.8 prints the first denominator as `8n√3(3^{2n-1} - 1)`; that version is off by the factor
`3^{2n-1}/(3^{2n-1} - 1)` in the first term (mpmath, `n = 1, …, 4`, and consistent with 25.11.21 at
`h = 1`, `k = 3`). -/
@[dlmf 25.11.E23]
theorem deriv_hurwitzZeta_one_sub_two_mul_third {n : ℕ} (hn : 1 ≤ n) :
    deriv (hurwitzZeta ((1 / 3 : ℝ) : UnitAddCircle)) (1 - 2 * n) =
      -(π : ℂ) * (9 ^ n - 1) * bernoulli (2 * n) / (8 * n * Real.sqrt 3 * 3 ^ (2 * n - 1)) -
        (bernoulli (2 * n) : ℂ) * Real.log 3 / (4 * n * 3 ^ (2 * n - 1)) -
        (-1) ^ n * DLMF.Gamma.polygamma (2 * n - 1) (1 / 3) /
          (2 * Real.sqrt 3 * (6 * π) ^ (2 * n - 1)) -
        (3 ^ (2 * n - 1) - 1) * deriv riemannZeta (1 - 2 * n) / (2 * 3 ^ (2 * n - 1)) := by
  sorry

/-- **Sum of derivatives over a period** (DLMF 25.11.24): for `s ≠ 1`, `k = 1, 2, 3, …`,
`∑_{r=1}^{k-1} ζ'(s, r/k) = (k^s - 1) ζ'(s) + k^s ζ(s) ln k`. -/
@[dlmf 25.11.E24]
theorem sum_deriv_hurwitzZeta_rat {s : ℂ} (hs : s ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    ∑ r ∈ Finset.Ico 1 k, deriv (hurwitzZeta ((r / k : ℝ) : UnitAddCircle)) s =
      ((k : ℂ) ^ s - 1) * deriv riemannZeta s + (k : ℂ) ^ s * riemannZeta s * Real.log k :=
  q25b_sum_deriv_hurwitzZeta_rat hs hk

end DLMF.Zeta

end
