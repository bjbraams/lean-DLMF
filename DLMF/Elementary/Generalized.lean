/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar

/-!
# Generalized logarithms and exponentials: DLMF §4.12

The explicit Clenshaw choice uses iterated exponentials and the first iterate of the
logarithm landing in `[0,1)`. The domain of the generalized exponential is `(-1,∞)`;
the generalized logarithm has domain all of `ℝ`. Values outside the former domain
are totalized by the displayed formula, without mathematical assertions there.
-/

@[expose] public section
open Set Filter
open scoped Topology
noncomputable section
namespace DLMF.Elementary

/-- A mutually inverse generalized exponential and logarithm, with their full domains. -/
structure IsGeneralizedExpLog (φ ψ : ℝ → ℝ) : Prop where
  /-- Exponential shift equation (4.12.1). -/
  exp_shift : ∀ x, -1 < x → φ (x + 1) = Real.exp (φ x)
  /-- Origin normalization (4.12.2). -/
  exp_zero : φ 0 = 0
  /-- Increasing normalization on the fundamental interval. -/
  exp_strictMono : StrictMonoOn φ (Icc 0 1)
  /-- Logarithmic inverse equation. -/
  log_exp : ∀ x, -1 < x → ψ (φ x) = x
  /-- Exponential inverse equation. -/
  exp_log : ∀ x, φ (ψ x) = x
  /-- The inverse stays inside the exponential domain. -/
  log_range : ∀ x, -1 < ψ x

/-- The generalized logarithm shift identity (4.12.3). -/
@[dlmf 4.12.E3]
theorem IsGeneralizedExpLog.log_shift {φ ψ : ℝ → ℝ} (h : IsGeneralizedExpLog φ ψ)
    (x : ℝ) : ψ (Real.exp x) = 1 + ψ x := by
  have h1 := h.exp_shift (ψ x) (h.log_range x)
  rw [h.exp_log x] at h1
  rw [← h1, h.log_exp _ (by linarith [h.log_range x])]
  ring

/-- The inverse normalization (4.12.4). -/
@[dlmf 4.12.E4]
theorem IsGeneralizedExpLog.log_zero {φ ψ : ℝ → ℝ} (h : IsGeneralizedExpLog φ ψ) :
    ψ 0 = 0 := by
  simpa [h.exp_zero] using h.log_exp 0 (by norm_num)

/-- A generalized exponential exceeds one beyond the fundamental interval. -/
lemma logR4_one_lt_exp {φ ψ : ℝ → ℝ} (h : IsGeneralizedExpLog φ ψ) {t : ℝ} (ht : 1 < t) :
    1 < φ t := by
  have base : ∀ s : ℝ, 1 < s → s ≤ 2 → 1 < φ s := by
    intro s hs1 hs2
    have he := h.exp_shift (s - 1) (by linarith)
    rw [show s - 1 + 1 = s by ring] at he
    have hp : φ 0 < φ (s - 1) := h.exp_strictMono ⟨le_rfl, by norm_num⟩
      ⟨by linarith, by linarith⟩ (by linarith)
    rw [he, h.exp_zero] at *
    exact Real.one_lt_exp_iff.mpr hp
  have key : ∀ n : ℕ, ∀ s : ℝ, 1 < s → s ≤ n + 2 → 1 < φ s := by
    intro n
    induction n with
    | zero => intro s hs1 hs2; exact base s hs1 (by simpa using hs2)
    | succ n ih =>
      intro s hs1 hs2
      by_cases hs : s ≤ 2
      · exact base s hs1 hs
      · push Not at hs
        have he := h.exp_shift (s - 1) (by linarith)
        rw [show s - 1 + 1 = s by ring] at he
        have := ih (s - 1) (by linarith) (by push_cast at hs2; linarith)
        rw [he]
        exact Real.one_lt_exp_iff.mpr (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_gt t
  exact key n t ht (by linarith)

/-- A normalized generalized exponential takes values in `[0,1]` only on `[0,1]`. -/
lemma logR4_mem_Icc_of_exp {φ ψ : ℝ → ℝ} (h : IsGeneralizedExpLog φ ψ) {t : ℝ}
    (ht : -1 < t) (hφ : φ t ∈ Icc 0 1) : t ∈ Icc 0 1 := by
  have h1 : φ 1 = 1 := by
    have := h.exp_shift 0 (by norm_num); simpa [h.exp_zero] using this
  by_contra hn
  rcases not_and_or.mp hn with h0 | h0
  · push Not at h0
    have he := h.exp_shift t ht
    have hlt : φ (t + 1) < φ 1 := h.exp_strictMono ⟨by linarith, by linarith⟩
      ⟨by norm_num, le_rfl⟩ (by linarith)
    rw [he, h1] at hlt
    have : φ t < 0 := Real.exp_lt_one_iff.mp hlt
    linarith [hφ.1]
  · push Not at h0
    linarith [logR4_one_lt_exp h h0, hφ.2]

/-- Generalized logarithms are strictly increasing on the fundamental interval. -/
theorem IsGeneralizedExpLog.log_strictMono {φ ψ : ℝ → ℝ}
    (h : IsGeneralizedExpLog φ ψ) : StrictMonoOn ψ (Icc 0 1) := by
  intro x hx y hy hxy
  have hx' := logR4_mem_Icc_of_exp h (h.log_range x) (by rw [h.exp_log]; exact hx)
  have hy' := logR4_mem_Icc_of_exp h (h.log_range y) (by rw [h.exp_log]; exact hy)
  by_contra hle
  push Not at hle
  have := h.exp_strictMono.monotoneOn hy' hx' hle
  rw [h.exp_log, h.exp_log] at this
  linarith

/-- Every positive argument eventually reaches `[0,1)` under iterated logarithms. -/
@[dlmf 4.12.E10]
theorem exists_iterate_log_mem_Ico {x : ℝ} (hx : 1 < x) :
    ∃ n : ℕ, (Real.log^[n]) x ∈ Set.Ico 0 1 := by
  by_contra hne
  push Not at hne
  have key : ∀ n : ℕ, 1 ≤ (Real.log^[n]) x ∧ (Real.log^[n]) x ≤ x - n := by
    intro n
    induction n with
    | zero => simp; linarith
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have h0 : 0 ≤ Real.log ((Real.log^[n]) x) := Real.log_nonneg ih.1
      have h1 : Real.log ((Real.log^[n]) x) ≤ (Real.log^[n]) x - 1 :=
        Real.log_le_sub_one_of_pos (by linarith [ih.1])
      have h2 : ¬ Real.log ((Real.log^[n]) x) < 1 := by
        intro hl; apply hne (n+1); rw [Function.iterate_succ_apply']; exact ⟨h0, hl⟩
      push_cast
      constructor <;> linarith [ih.2]
  obtain ⟨n, hn⟩ := exists_nat_gt x
  have := key n
  linarith [this.1, this.2]

/-- The first logarithmic iterate landing in the fundamental interval. -/
def logIterationCount (x : ℝ) : ℕ :=
  if hx : 1 < x then Nat.find (exists_iterate_log_mem_Ico hx) else 0

/-- The simplest generalized exponential (4.12.5–4.12.7). -/
def generalizedExp (x : ℝ) : ℝ :=
  if x < 0 then Real.log (x + 1)
  else (Real.exp^[⌊x⌋₊]) (x - ⌊x⌋₊)

/-- Its inverse generalized logarithm (4.12.5, 4.12.8–4.12.10). -/
def generalizedLog (x : ℝ) : ℝ :=
  if x < 0 then Real.exp x - 1
  else if x ≤ 1 then x
  else logIterationCount x + (Real.log^[logIterationCount x]) x

/-- Identity normalization on the closed fundamental interval (4.12.5). -/
@[dlmf 4.12.E5]
theorem generalized_eq_self {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    generalizedExp x = x ∧ generalizedLog x = x := by
  constructor
  · rcases hx.2.lt_or_eq with h | rfl
    · have : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr h
      simp [generalizedExp, not_lt.mpr hx.1, this]
    · simp [generalizedExp]
  · simp [generalizedLog, not_lt.mpr hx.1, hx.2]

/-- Generalized exponential immediately below the fundamental interval (4.12.6). -/
@[dlmf 4.12.E6]
theorem generalizedExp_neg {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 0) :
    generalizedExp x = Real.log (x + 1) := by
  simp [generalizedExp, hx.2]

/-- Iterated-exponential extension with the exact floor (4.12.7). -/
@[dlmf 4.12.E7]
theorem generalizedExp_gt_one {x : ℝ} (hx : 1 < x) :
    generalizedExp x = (Real.exp^[⌊x⌋₊]) (x - ⌊x⌋₊) := by
  simp [generalizedExp, show ¬x < 0 by linarith]

/-- Generalized logarithm on the negative half-axis (4.12.8). -/
@[dlmf 4.12.E8]
theorem generalizedLog_neg {x : ℝ} (hx : x < 0) :
    generalizedLog x = Real.exp x - 1 := by simp [generalizedLog, hx]

/-- Iterated-logarithm extension with the least admissible positive integer (4.12.9). -/
@[dlmf 4.12.E9]
theorem generalizedLog_gt_one {x : ℝ} (hx : 1 < x) :
    0 < logIterationCount x ∧
    generalizedLog x = logIterationCount x + (Real.log^[logIterationCount x]) x ∧
    (Real.log^[logIterationCount x]) x ∈ Set.Ico 0 1 ∧
    ∀ m < logIterationCount x, (Real.log^[m]) x ∉ Set.Ico 0 1 := by
  have hc : logIterationCount x = Nat.find (exists_iterate_log_mem_Ico hx) := by
    simp [logIterationCount, hx]
  rw [hc]
  refine ⟨?_, ?_, Nat.find_spec (exists_iterate_log_mem_Ico hx),
    fun m hm => Nat.find_min (exists_iterate_log_mem_Ico hx) hm⟩
  · apply Nat.pos_of_ne_zero
    intro h0
    have := Nat.find_spec (exists_iterate_log_mem_Ico hx)
    rw [h0] at this
    simp at this; linarith [this.2]
  · simp [generalizedLog, show ¬ x < 0 by linarith, show ¬ x ≤ 1 by linarith, hc]

/-- Iterated exponentials dominate a shift. -/
lemma logR4_add_le_exp_iterate (k : ℕ) (f : ℝ) : f + k ≤ (Real.exp^[k]) f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := Real.add_one_le_exp ((Real.exp^[k]) f)
    push_cast; linarith

/-- Iterated logarithms invert iterated exponentials. -/
lemma logR4_log_iterate_exp_iterate (m : ℕ) (u : ℝ) : (Real.log^[m]) ((Real.exp^[m]) u) = u := by
  induction m generalizing u with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply (f := Real.log), Function.iterate_succ_apply' (f := Real.exp),
      Real.log_exp, ih]

/-- Before the least landing index, iterated logarithms stay at least one. -/
lemma logR4_one_le_log_iterate {x : ℝ} (hx : 1 < x) {j : ℕ} (hj : j < logIterationCount x) :
    1 ≤ (Real.log^[j]) x := by
  obtain ⟨-, -, -, hmin⟩ := generalizedLog_gt_one hx
  induction j with
  | zero => simpa using hx.le
  | succ j ih =>
    have h1 := ih (by omega)
    rw [Function.iterate_succ_apply']
    have h0 : 0 ≤ Real.log ((Real.log^[j]) x) := Real.log_nonneg h1
    by_contra hlt
    push Not at hlt
    apply hmin (j+1) hj
    rw [Function.iterate_succ_apply']
    exact ⟨h0, hlt⟩

/-- Iterated exponentials invert iterated logarithms along positive orbits. -/
lemma logR4_exp_iterate_log_iterate (j : ℕ) {u : ℝ} (hu : ∀ i < j, 0 < (Real.log^[i]) u) :
    (Real.exp^[j]) ((Real.log^[j]) u) = u := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply (f := Real.exp), Function.iterate_succ_apply' (f := Real.log),
      Real.exp_log (hu j (by omega)), ih (fun i hi => hu i (by omega))]

/-- The inverse equation above the fundamental interval. -/
lemma logR4_exp_log_gt_one {x : ℝ} (hx : 1 < x) : generalizedExp (generalizedLog x) = x := by
  obtain ⟨hpos, he, hm, -⟩ := generalizedLog_gt_one hx
  set m := logIterationCount x
  rw [he]
  have hfl : ⌊(m:ℝ) + (Real.log^[m]) x⌋₊ = m := by
    rw [Nat.floor_eq_iff (by linarith [hm.1, (Nat.cast_nonneg m : (0:ℝ) ≤ m)])]
    constructor <;> linarith [hm.1, hm.2]
  simp only [generalizedExp, show ¬ ((m:ℝ) + (Real.log^[m]) x < 0) by
    linarith [hm.1, (Nat.cast_nonneg m : (0:ℝ) ≤ m)], ite_false, hfl, add_sub_cancel_left]
  exact logR4_exp_iterate_log_iterate m (fun i hi => by
    linarith [logR4_one_le_log_iterate hx hi])

/-- The logarithmic inverse equation above the fundamental interval. -/
lemma logR4_log_exp_gt_one {x : ℝ} (hx : 1 < x) : generalizedLog (generalizedExp x) = x := by
  set n := ⌊x⌋₊ with hn
  set f := x - n with hf
  have hn1 : 1 ≤ n := Nat.le_floor (by simpa using hx.le)
  have hf0 : 0 ≤ f := by rw [hf]; linarith [Nat.floor_le (show 0 ≤ x by linarith)]
  have hf1 : f < 1 := by rw [hf]; linarith [Nat.lt_floor_add_one x]
  have hgx : generalizedExp x = (Real.exp^[n]) f := by
    simp [generalizedExp, show ¬ x < 0 by linarith, hn, hf]
  set y := (Real.exp^[n]) f with hy
  have hyx : x ≤ y := by have := logR4_add_le_exp_iterate n f; rw [hf] at this; linarith
  have hy1 : 1 < y := by linarith
  have horbit : ∀ m ≤ n, (Real.log^[m]) y = (Real.exp^[n - m]) f := by
    intro m hm
    rw [hy, show n = m + (n - m) by omega, Function.iterate_add_apply,
      logR4_log_iterate_exp_iterate, show m + (n - m) - m = n - m by omega]
  have hcount : logIterationCount y = n := by
    simp only [logIterationCount, hy1, ↓reduceDIte]
    rw [Nat.find_eq_iff]
    refine ⟨by rw [horbit n le_rfl, Nat.sub_self]; exact ⟨hf0, hf1⟩, fun m hm hmem => ?_⟩
    rw [horbit m hm.le] at hmem
    have := logR4_add_le_exp_iterate (n - m) f
    have h1 : (1:ℝ) ≤ ((n - m : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n - m by omega)
    linarith [hmem.2]
  rw [hgx]
  simp only [generalizedLog, show ¬ y < 0 by linarith, show ¬ y ≤ 1 by linarith, ite_false,
    hcount, horbit n le_rfl, Nat.sub_self, Function.iterate_zero, id_eq]
  rw [hf]; ring

/-- The explicit pair satisfies the defining equations and inverse relations. -/
@[dlmf 4.12.E1, dlmf 4.12.E2]
theorem generalizedExpLog_spec : IsGeneralizedExpLog generalizedExp generalizedLog := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases lt_or_ge x 0 with h0 | h0
    · have hfl : ⌊x + 1⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      simp [generalizedExp, h0, show ¬ x + 1 < 0 by linarith, hfl,
        Real.exp_log (show 0 < x + 1 by linarith)]
    · have hfl : ⌊x + 1⌋₊ = ⌊x⌋₊ + 1 := Nat.floor_add_one h0
      simp only [generalizedExp, show ¬ x + 1 < 0 by linarith, show ¬ x < 0 by linarith,
        ite_false, hfl]
      rw [Function.iterate_succ_apply']
      congr 2
      push_cast; ring
  · simp [generalizedExp]
  · intro x hx y hy hxy
    rw [(generalized_eq_self hx).1, (generalized_eq_self hy).1]
    exact hxy
  · intro x hx
    rcases lt_or_ge x 0 with h0 | h0
    · have hl : Real.log (x + 1) < 0 := Real.log_neg (by linarith) (by linarith)
      simp [generalizedExp, generalizedLog, h0, hl, Real.exp_log (show 0 < x + 1 by linarith)]
    rcases le_or_gt x 1 with h1 | h1
    · rw [(generalized_eq_self ⟨h0, h1⟩).1, (generalized_eq_self ⟨h0, h1⟩).2]
    · exact logR4_log_exp_gt_one h1
  · intro x
    rcases lt_or_ge x 0 with h0 | h0
    · have hl : Real.exp x - 1 < 0 := by linarith [Real.exp_lt_one_iff.mpr h0]
      simp [generalizedExp, generalizedLog, h0, hl]
    rcases le_or_gt x 1 with h1 | h1
    · rw [(generalized_eq_self ⟨h0, h1⟩).2, (generalized_eq_self ⟨h0, h1⟩).1]
    · exact logR4_exp_log_gt_one h1
  · intro x
    rcases lt_or_ge x 0 with h0 | h0
    · simp [generalizedLog, h0, Real.exp_pos]
    rcases le_or_gt x 1 with h1 | h1
    · rw [(generalized_eq_self ⟨h0, h1⟩).2]; linarith
    · obtain ⟨-, he, hm, -⟩ := generalizedLog_gt_one h1
      rw [he]
      have : (0:ℝ) ≤ logIterationCount x := Nat.cast_nonneg _
      linarith [hm.1]

/-- A function glued at `0` from two `C¹` pieces with matching value and slope is `C¹`. -/
lemma logR4_junction {f g h g' h' : ℝ → ℝ} {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hg : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hh : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x)
    (hgc : ContinuousOn g' (Ioo a b)) (hhc : ContinuousOn h' (Ioo a b))
    (hfg : ∀ x ∈ Ioc a 0, f x = g x) (hfh : ∀ x ∈ Ico 0 b, f x = h x) (h0 : g' 0 = h' 0) :
    ContDiffOn ℝ 1 f (Ioo a b) := by
  have hs : IsOpen (Ioo a b) := isOpen_Ioo
  set d : ℝ → ℝ := fun x => if x < 0 then g' x else h' x
  have hd : ∀ x ∈ Ioo a b, HasDerivAt f (d x) x := by
    intro x hx
    rcases lt_trichotomy x 0 with hx0 | rfl | hx0
    · have hev : f =ᶠ[𝓝 x] g := by
        filter_upwards [Ioo_mem_nhds hx.1 hx0] with y hy using hfg y ⟨hy.1, hy.2.le⟩
      simp only [d, hx0, ite_true]
      exact (hg x hx).congr_of_eventuallyEq hev
    · have h1 : HasDerivWithinAt f (g' 0) (Iic 0) 0 := by
        apply (hg 0 hx).hasDerivWithinAt.congr_of_eventuallyEq _ (hfg 0 ⟨ha, le_rfl⟩)
        filter_upwards [inter_mem_nhdsWithin (Iic 0) (Ioi_mem_nhds ha), self_mem_nhdsWithin]
          with y hy hy' using hfg y ⟨hy.2, hy'⟩
      have h2 : HasDerivWithinAt f (g' 0) (Ici 0) 0 := by
        rw [h0]
        apply (hh 0 hx).hasDerivWithinAt.congr_of_eventuallyEq _ (hfh 0 ⟨le_rfl, hb⟩)
        filter_upwards [inter_mem_nhdsWithin (Ici 0) (Iio_mem_nhds hb), self_mem_nhdsWithin]
          with y hy hy' using hfh y ⟨hy', hy.2⟩
      have := h1.union h2
      rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
      simpa [d, h0] using this
    · have hev : f =ᶠ[𝓝 x] h := by
        filter_upwards [Ioo_mem_nhds hx0 hx.2] with y hy using hfh y ⟨hy.1.le, hy.2⟩
      simp only [d, not_lt.mpr hx0.le, ite_false]
      exact (hh x hx).congr_of_eventuallyEq hev
  have hdc : ContinuousOn d (Ioo a b) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hgx := (hgc x hx).continuousAt (Ioo_mem_nhds hx.1 hx.2)
    have hhx := (hhc x hx).continuousAt (Ioo_mem_nhds hx.1 hx.2)
    rcases lt_trichotomy x 0 with hx0 | rfl | hx0
    · apply hgx.congr
      filter_upwards [Iio_mem_nhds hx0] with y hy
      simp [d, show y < 0 from hy]
    · rw [continuousAt_iff_continuous_left_right]
      constructor
      · apply hgx.continuousWithinAt.congr
        · intro y hy
          rcases lt_or_eq_of_le (show y ≤ 0 from hy) with hy | rfl
          · simp [d, hy]
          · simp [d, h0]
        · simp [d, h0]
      · apply hhx.continuousWithinAt.congr
        · intro y hy; simp [d, not_lt.mpr (show (0:ℝ) ≤ y from hy)]
        · simp [d]
    · apply hhx.congr
      filter_upwards [Ioi_mem_nhds hx0] with y hy
      simp [d, not_lt.mpr (show (0:ℝ) < y from hy).le]
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hs]
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hdc.congr fun x hx => (hd x hx).deriv

/-- The explicit generalized exponential is continuously differentiable on its domain. -/
theorem generalizedExp_contDiffOn : ContDiffOn ℝ 1 generalizedExp (Ioi (-1)) := by
  have hs := generalizedExpLog_spec
  have base : ContDiffOn ℝ 1 generalizedExp (Ioo (-1) 1) := by
    apply logR4_junction (g := fun x => Real.log (x+1)) (h := id) (g' := fun x => (x+1)⁻¹)
      (h' := fun _ => 1) (by norm_num) (by norm_num)
    · intro x hx
      have hx1 : x + 1 ≠ 0 := by linarith [hx.1]
      simpa using ((hasDerivAt_id x).add_const 1).log hx1
    · intro x _; exact hasDerivAt_id x
    · apply ContinuousOn.inv₀ (by fun_prop)
      intro x hx; linarith [hx.1]
    · exact continuousOn_const
    · intro x hx
      rcases lt_or_eq_of_le hx.2 with h | rfl
      · exact generalizedExp_neg ⟨hx.1, h⟩
      · simp [(generalized_eq_self (x := 0) ⟨le_rfl, zero_le_one⟩).1]
    · intro x hx; exact (generalized_eq_self ⟨hx.1, hx.2.le⟩).1
    · norm_num
  have P : ∀ n : ℕ, ∀ x ∈ Ioo (-1:ℝ) (n+1), ContDiffAt ℝ 1 generalizedExp x := by
    intro n
    induction n with
    | zero =>
      intro x hx
      exact base.contDiffAt (Ioo_mem_nhds hx.1 (by simpa using hx.2))
    | succ n ih =>
      intro x hx
      rcases lt_or_ge x (n+1) with h | h
      · exact ih x ⟨hx.1, h⟩
      · have hx0 : 0 < x := by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
        have hev : (fun y => Real.exp (generalizedExp (y-1))) =ᶠ[𝓝 x] generalizedExp := by
          filter_upwards [Ioi_mem_nhds hx0] with y hy
          have := hs.exp_shift (y-1) (by simp at hy; linarith)
          rw [sub_add_cancel] at this
          exact this.symm
        refine ContDiffAt.congr_of_eventuallyEq ?_ hev.symm
        apply Real.contDiff_exp.contDiffAt.comp
        apply ContDiffAt.comp (g := generalizedExp) _ _ (contDiffAt_id.sub contDiffAt_const)
        apply ih
        have h2 := hx.2
        push_cast at h2
        simp only [id]
        constructor <;> linarith
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_gt x
  exact (P n x ⟨hx, by linarith⟩).contDiffWithinAt

/-- The explicit generalized logarithm is continuously differentiable on `ℝ`. -/
theorem generalizedLog_contDiff : ContDiff ℝ 1 generalizedLog := by
  have hs := generalizedExpLog_spec
  have base : ContDiffOn ℝ 1 generalizedLog (Ioo (-1) 1) := by
    apply logR4_junction (g := fun x => Real.exp x - 1) (h := id) (g' := Real.exp)
      (h' := fun _ => 1) (by norm_num) (by norm_num)
    · intro x _; exact (Real.hasDerivAt_exp x).sub_const 1
    · intro x _; exact hasDerivAt_id x
    · exact Real.continuous_exp.continuousOn
    · exact continuousOn_const
    · intro x hx
      rcases lt_or_eq_of_le hx.2 with h | rfl
      · exact generalizedLog_neg h
      · simp [(generalized_eq_self (x := 0) ⟨le_rfl, zero_le_one⟩).2]
    · intro x hx; exact (generalized_eq_self ⟨hx.1, hx.2.le⟩).2
    · simp
  have Q : ∀ n : ℕ, ∀ x : ℝ, x < n+1 → ContDiffAt ℝ 1 generalizedLog x := by
    intro n
    induction n with
    | zero =>
      intro x hx
      rcases lt_or_ge x (-1) with h | h
      · have hev : (fun y => Real.exp y - 1) =ᶠ[𝓝 x] generalizedLog := by
          filter_upwards [Iio_mem_nhds (show x < 0 by linarith)] with y hy
          exact (generalizedLog_neg hy).symm
        exact ((Real.contDiff_exp.sub contDiff_const).contDiffAt).congr_of_eventuallyEq hev.symm
      · rcases eq_or_lt_of_le h with h | h
        · subst h
          have hev : (fun y => Real.exp y - 1) =ᶠ[𝓝 (-1:ℝ)] generalizedLog := by
            filter_upwards [Iio_mem_nhds (show (-1:ℝ) < 0 by norm_num)] with y hy
            exact (generalizedLog_neg hy).symm
          exact ((Real.contDiff_exp.sub contDiff_const).contDiffAt).congr_of_eventuallyEq hev.symm
        · exact base.contDiffAt (Ioo_mem_nhds h (by simpa using hx))
    | succ n ih =>
      intro x hx
      rcases lt_or_ge x (n+1) with h | h
      · exact ih x h
      · have hx0 : 0 < x := by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
        have hev : (fun y => 1 + generalizedLog (Real.log y)) =ᶠ[𝓝 x] generalizedLog := by
          filter_upwards [Ioi_mem_nhds hx0] with y hy
          have := hs.log_shift (Real.log y)
          rw [Real.exp_log hy] at this
          exact this.symm
        refine ContDiffAt.congr_of_eventuallyEq ?_ hev.symm
        apply contDiffAt_const.add
        apply ContDiffAt.comp (g := generalizedLog) _ _ (Real.contDiffAt_log.mpr hx0.ne')
        apply ih
        have := Real.log_le_sub_one_of_pos hx0
        push_cast at hx
        linarith
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt x
  exact Q n x (by linarith)

/-- A nonlinear increasing reparametrization commuting with unit shifts. -/
def logR4_g (x : ℝ) : ℝ := ⌊x⌋ + (Int.fract x)^2

/-- The inverse of `logR4_g`. -/
def logR4_ginv (x : ℝ) : ℝ := ⌊x⌋ + Real.sqrt (Int.fract x)

/-- The reparametrization commutes with unit shifts. -/
lemma logR4_g_add_one (x : ℝ) : logR4_g (x + 1) = logR4_g x + 1 := by
  simp [logR4_g, Int.floor_add_one, Int.fract_add_one]; ring

/-- Floor and fractional part of an integer plus a number in `[0,1)`. -/
lemma logR4_floor_fract {n : ℤ} {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    ⌊(n:ℝ) + u⌋ = n ∧ Int.fract ((n:ℝ) + u) = u := by
  have hf : ⌊u⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩
  refine ⟨by rw [Int.floor_intCast_add, hf, add_zero], ?_⟩
  rw [Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨h0, h1⟩]

/-- `logR4_ginv` is a left inverse of `logR4_g`. -/
lemma logR4_ginv_g (x : ℝ) : logR4_ginv (logR4_g x) = x := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  obtain ⟨ha, hb⟩ := logR4_floor_fract (n := ⌊x⌋) (u := (Int.fract x)^2) (by positivity)
    (by nlinarith)
  rw [logR4_ginv, logR4_g, ha, hb, Real.sqrt_sq h0, Int.floor_add_fract]

/-- `logR4_ginv` is a right inverse of `logR4_g`. -/
lemma logR4_g_ginv (x : ℝ) : logR4_g (logR4_ginv x) = x := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  obtain ⟨ha, hb⟩ := logR4_floor_fract (n := ⌊x⌋) (u := Real.sqrt (Int.fract x))
    (Real.sqrt_nonneg _) (by rw [Real.sqrt_lt' one_pos]; simpa using h1)
  rw [logR4_g, logR4_ginv, ha, hb, Real.sq_sqrt h0, Int.floor_add_fract]

/-- The reparametrization preserves the exponential domain. -/
lemma logR4_g_gt {x : ℝ} (hx : -1 < x) : -1 < logR4_g x := by
  have hfl : -1 ≤ ⌊x⌋ := Int.le_floor.mpr (by push_cast; linarith)
  rcases hfl.lt_or_eq with h | h
  · have : (0:ℝ) ≤ ⌊x⌋ := by exact_mod_cast (show (0:ℤ) ≤ ⌊x⌋ by omega)
    rw [logR4_g]; nlinarith [sq_nonneg (Int.fract x)]
  · have hfr : Int.fract x = x + 1 := by rw [Int.fract, ← h]; push_cast; ring
    rw [logR4_g, ← h, hfr]; push_cast; nlinarith

/-- The inverse reparametrization preserves the exponential domain. -/
lemma logR4_ginv_gt {x : ℝ} (hx : -1 < x) : -1 < logR4_ginv x := by
  have hfl : -1 ≤ ⌊x⌋ := Int.le_floor.mpr (by push_cast; linarith)
  rcases hfl.lt_or_eq with h | h
  · have : (0:ℝ) ≤ ⌊x⌋ := by exact_mod_cast (show (0:ℤ) ≤ ⌊x⌋ by omega)
    rw [logR4_ginv]; linarith [Real.sqrt_nonneg (Int.fract x)]
  · have hfr : Int.fract x = x + 1 := by rw [Int.fract, ← h]; push_cast; ring
    rw [logR4_ginv, ← h, hfr]; push_cast
    linarith [Real.sqrt_pos.mpr (show 0 < x + 1 by linarith)]

/-- On the fundamental interval the reparametrization is squaring. -/
lemma logR4_g_Icc {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : logR4_g x = x^2 := by
  rcases hx.2.lt_or_eq with h | rfl
  · obtain ⟨ha, hb⟩ := logR4_floor_fract (n := 0) (u := x) hx.1 h
    simp only [Int.cast_zero, zero_add] at ha hb
    rw [logR4_g, ha, hb]; simp
  · simp [logR4_g]

/-- Generalized logarithms and exponentials are not unique (4.12, prose). -/
theorem generalizedExpLog_not_unique :
    ∃ φ ψ : ℝ → ℝ, IsGeneralizedExpLog φ ψ ∧ φ ≠ generalizedExp := by
  have hs := generalizedExpLog_spec
  refine ⟨fun x => generalizedExp (logR4_g x), fun x => logR4_ginv (generalizedLog x), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [logR4_g_add_one]
      exact hs.exp_shift _ (logR4_g_gt hx)
    · simp [logR4_g, hs.exp_zero]
    · intro x hx y hy hxy
      have hgx : logR4_g x ∈ Icc (0:ℝ) 1 := by
        rw [logR4_g_Icc hx]; exact ⟨sq_nonneg _, by nlinarith [hx.1, hx.2]⟩
      have hgy : logR4_g y ∈ Icc (0:ℝ) 1 := by
        rw [logR4_g_Icc hy]; exact ⟨sq_nonneg _, by nlinarith [hy.1, hy.2]⟩
      apply hs.exp_strictMono hgx hgy
      rw [logR4_g_Icc hx, logR4_g_Icc hy]
      nlinarith [hx.1, hy.1]
    · intro x hx
      rw [hs.log_exp _ (logR4_g_gt hx), logR4_ginv_g]
    · intro x
      rw [logR4_g_ginv, hs.exp_log]
    · intro x
      exact logR4_ginv_gt (hs.log_range x)
  · intro h
    have := congrFun h (1/2)
    rw [logR4_g_Icc ⟨by norm_num, by norm_num⟩, (generalized_eq_self ⟨by norm_num, by norm_num⟩).1,
      (generalized_eq_self ⟨by norm_num, by norm_num⟩).1] at this
    norm_num at this

end DLMF.Elementary
