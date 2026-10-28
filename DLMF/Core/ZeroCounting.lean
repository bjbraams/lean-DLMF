/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import TauCeti.Analysis.Complex.Conformal.Rouche
public import Mathlib.Analysis.Convex.Contractible

/-!
# Zero enumerations by modulus and one-zero-per-disc criteria

DLMF lists the complex zeros of a special function in a sector "arranged in order of increasing
absolute value". The project encodes this by `DLMF.orderedZero f S k`, an `epsilon`-choice of a
zero `z ∈ S` of `f` with exactly `k - 1` zeros of `f` in `S` of smaller modulus. This file gives
the combinatorics behind that encoding and the bridge from Rouché's theorem
(`TauCeti.rouche`, Tau Ceti) to it.

Write `Z = {z ∈ S | f z = 0}` and assume that every bounded part of `Z` is finite (true for an
entire function that is not identically zero, `zcnt_finite_zeros_lt`). Then:

* `zcnt_orderedZero_spec_iff`: the enumeration is well defined for every `k ≥ 1` if and only if
  the zeros in `S` have pairwise distinct moduli and there are infinitely many of them;
* `zcnt_orderedZero_strictMonoOn`: the enumeration is then strictly increasing in modulus;
* `zcnt_eq_orderedZero`: every zero in `S` is enumerated;
* `zcnt_injOn_infinite_of_discs`: "exactly one zero in each disc `D_k`, the discs lie in disjoint
  annuli of increasing radius, and every zero lies in some `D_k`" gives distinct moduli and
  infinitely many zeros;
* `zcnt_existsUnique_of_count_eq_one`, `zcnt_existsUnique_zero_of_rouche`: a zero count `1`
  (with multiplicity) on a disc, for instance transferred by Rouché's theorem from a model, gives
  exactly one zero in the disc.
-/

@[expose] public noncomputable section

open Complex Metric Set Filter
open scoped Topology

namespace DLMF

/-- The zeros of an entire function that is not identically zero form a finite set in every
closed disc about the origin. -/
theorem zcnt_finite_zeros_closedBall {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℂ}
    (hx : f x ≠ 0) (R : ℝ) : {z : ℂ | f z = 0 ∧ ‖z‖ ≤ R}.Finite := by
  have han : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have hcod := (han.preimage_zero_mem_codiscrete hx)
  have hcK : f ⁻¹' {0}ᶜ ∈ codiscreteWithin (closedBall (0 : ℂ) R) :=
    codiscreteWithin_mono (subset_univ _) hcod
  refine ((isCompact_closedBall (0 : ℂ) R).finite_sdiff_of_mem_codiscreteWithin hcK).subset ?_
  rintro z ⟨hz0, hzR⟩
  exact ⟨by simpa using hzR, by simpa using hz0⟩

/-- The zeros in `S` of modulus `< R` of an entire function that is not identically zero form a
finite set. -/
theorem zcnt_finite_zeros_lt {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    (S : Set ℂ) (R : ℝ) : {z : ℂ | z ∈ S ∧ f z = 0 ∧ ‖z‖ < R}.Finite :=
  (zcnt_finite_zeros_closedBall hf hx R).subset fun _ hz => ⟨hz.2.1, hz.2.2.le⟩

section Enumeration

variable {f : ℂ → ℂ} {S : Set ℂ}

/-- The zeros of `f` in `S` of modulus `< r`. -/
private abbrev B (f : ℂ → ℂ) (S : Set ℂ) (r : ℝ) : Set ℂ := {w : ℂ | w ∈ S ∧ f w = 0 ∧ ‖w‖ < r}

/-- Counting smaller zeros is monotone in the modulus. -/
private lemma B_ncard_le (hfin : ∀ r : ℝ, (B f S r).Finite) {r s : ℝ} (h : r ≤ s) :
    (B f S r).ncard ≤ (B f S s).ncard :=
  Set.ncard_le_ncard (fun _ hw => ⟨hw.1, hw.2.1, hw.2.2.trans_le h⟩) (hfin s)

/-- A zero of strictly smaller modulus has strictly fewer zeros below it. -/
private lemma B_ncard_lt (hfin : ∀ r : ℝ, (B f S r).Finite) {w z : ℂ} (hw : w ∈ S)
    (hw0 : f w = 0) (h : ‖w‖ < ‖z‖) : (B f S ‖w‖).ncard < (B f S ‖z‖).ncard := by
  have hsub : insert w (B f S ‖w‖) ⊆ B f S ‖z‖ := by
    rintro v (rfl | hv)
    · exact ⟨hw, hw0, h⟩
    · exact ⟨hv.1, hv.2.1, hv.2.2.trans h⟩
  have hnot : w ∉ B f S ‖w‖ := fun hv => lt_irrefl _ hv.2.2
  have := Set.ncard_le_ncard hsub (hfin _)
  rw [Set.ncard_insert_of_notMem hnot (hfin _)] at this
  omega

/-- If the enumeration is well defined for every index, the zeros in `S` have distinct moduli. -/
private lemma injOn_of_spec (hfin : ∀ r : ℝ, (B f S r).Finite)
    (hspec : ∀ k : ℕ, 1 ≤ k → orderedZero f S k ∈ S ∧ f (orderedZero f S k) = 0 ∧
      (B f S ‖orderedZero f S k‖).ncard = k - 1) :
    InjOn (fun z : ℂ => ‖z‖) {z : ℂ | z ∈ S ∧ f z = 0} := by
  intro z hz z' hz' hzz
  simp only at hzz
  by_contra hne
  set m := (B f S ‖z‖).ncard
  obtain ⟨hu, hu0, hcu⟩ := hspec (m + 2) (by omega)
  set u := orderedZero f S (m + 2)
  rcases le_or_gt ‖u‖ ‖z‖ with hle | hlt
  · have := B_ncard_le hfin hle
    omega
  · have hsub : insert z (insert z' (B f S ‖z‖)) ⊆ B f S ‖u‖ := by
      rintro v (rfl | rfl | hv)
      · exact ⟨hz.1, hz.2, hlt⟩
      · exact ⟨hz'.1, hz'.2, hzz ▸ hlt⟩
      · exact ⟨hv.1, hv.2.1, hv.2.2.trans hlt⟩
    have hz'n : z' ∉ B f S ‖z‖ := fun hv => lt_irrefl _ (hzz ▸ hv.2.2)
    have hzn : z ∉ insert z' (B f S ‖z‖) := by
      rintro (h | hv)
      · exact hne h
      · exact lt_irrefl _ hv.2.2
    have h1 := Set.ncard_le_ncard hsub (hfin _)
    rw [Set.ncard_insert_of_notMem hzn ((hfin _).insert z'),
      Set.ncard_insert_of_notMem hz'n (hfin _)] at h1
    omega

/-- Given distinct moduli and infinitely many zeros, the next zero above any modulus exists. -/
private lemma exists_next (hfin : ∀ r : ℝ, (B f S r).Finite)
    (hinf : {z : ℂ | z ∈ S ∧ f z = 0}.Infinite) (r : ℝ) :
    ∃ z, z ∈ S ∧ f z = 0 ∧ r < ‖z‖ ∧ ∀ w, w ∈ S → f w = 0 → r < ‖w‖ → ‖z‖ ≤ ‖w‖ := by
  obtain ⟨w₀, ⟨hw₀S, hw₀0⟩, hw₀r⟩ : ∃ w ∈ {z : ℂ | z ∈ S ∧ f z = 0}, r < ‖w‖ := by
    by_contra h
    push Not at h
    exact hinf ((hfin (r + 1)).subset fun w hw => ⟨hw.1, hw.2, (h w hw).trans_lt (by linarith)⟩)
  have hTfin : {w : ℂ | w ∈ S ∧ f w = 0 ∧ r < ‖w‖ ∧ ‖w‖ ≤ ‖w₀‖}.Finite :=
    (hfin (‖w₀‖ + 1)).subset fun w hw => ⟨hw.1, hw.2.1, hw.2.2.2.trans_lt (by linarith)⟩
  obtain ⟨z, hz, hzmin⟩ := Set.exists_min_image _ (fun w : ℂ => ‖w‖) hTfin
    ⟨w₀, hw₀S, hw₀0, hw₀r, le_rfl⟩
  refine ⟨z, hz.1, hz.2.1, hz.2.2.1, fun w hwS hw0 hwr => ?_⟩
  rcases le_or_gt ‖w‖ ‖w₀‖ with h | h
  · exact hzmin w ⟨hwS, hw0, hwr, h⟩
  · exact hz.2.2.2.trans h.le

/-- With distinct moduli and infinitely many zeros, every count `n` is attained. -/
private lemma exists_count (hfin : ∀ r : ℝ, (B f S r).Finite)
    (hinj : InjOn (fun z : ℂ => ‖z‖) {z : ℂ | z ∈ S ∧ f z = 0})
    (hinf : {z : ℂ | z ∈ S ∧ f z = 0}.Infinite) (n : ℕ) :
    ∃ z, z ∈ S ∧ f z = 0 ∧ (B f S ‖z‖).ncard = n := by
  induction n with
  | zero =>
    obtain ⟨z, hzS, hz0, -, hmin⟩ := exists_next hfin hinf (-1)
    refine ⟨z, hzS, hz0, ?_⟩
    rw [Set.ncard_eq_zero (hfin _)]
    refine Set.eq_empty_of_forall_notMem fun w hw => ?_
    have := hmin w hw.1 hw.2.1 (by linarith [norm_nonneg w])
    linarith [hw.2.2]
  | succ n ih =>
    obtain ⟨z, hzS, hz0, hzn⟩ := ih
    obtain ⟨z', hz'S, hz'0, hzz', hmin⟩ := exists_next hfin hinf ‖z‖
    refine ⟨z', hz'S, hz'0, ?_⟩
    have heq : B f S ‖z'‖ = insert z (B f S ‖z‖) := by
      ext w
      constructor
      · rintro ⟨hwS, hw0, hwlt⟩
        rcases lt_trichotomy ‖w‖ ‖z‖ with h | h | h
        · exact Or.inr ⟨hwS, hw0, h⟩
        · exact Or.inl (hinj ⟨hwS, hw0⟩ ⟨hzS, hz0⟩ h)
        · exact absurd (hmin w hwS hw0 h) (not_le.mpr hwlt)
      · rintro (rfl | hw)
        · exact ⟨hzS, hz0, hzz'⟩
        · exact ⟨hw.1, hw.2.1, hw.2.2.trans hzz'⟩
    have hnot : z ∉ B f S ‖z‖ := fun hv => lt_irrefl _ hv.2.2
    rw [heq, Set.ncard_insert_of_notMem hnot (hfin _), hzn]

/-- **The modulus enumeration is well defined** exactly when the zeros of `f` in `S` have
pairwise distinct moduli and are infinitely many, given that bounded parts of the zero set are
finite. -/
theorem zcnt_orderedZero_spec_iff
    (hfin : ∀ r : ℝ, {w : ℂ | w ∈ S ∧ f w = 0 ∧ ‖w‖ < r}.Finite) :
    (∀ k : ℕ, 1 ≤ k → orderedZero f S k ∈ S ∧ f (orderedZero f S k) = 0 ∧
        ({w : ℂ | w ∈ S ∧ f w = 0 ∧ ‖w‖ < ‖orderedZero f S k‖} : Set ℂ).ncard = k - 1) ↔
      (InjOn (fun z : ℂ => ‖z‖) {z : ℂ | z ∈ S ∧ f z = 0} ∧
        {z : ℂ | z ∈ S ∧ f z = 0}.Infinite) := by
  constructor
  · intro hspec
    refine ⟨injOn_of_spec hfin hspec, ?_⟩
    have hmaps : MapsTo (orderedZero f S) (Ici 1) {z : ℂ | z ∈ S ∧ f z = 0} :=
      fun k hk => ⟨(hspec k hk).1, (hspec k hk).2.1⟩
    refine Set.infinite_of_injOn_mapsTo (fun k hk l hl hkl => ?_) hmaps (Set.Ici_infinite 1)
    have h1 := (hspec k hk).2.2
    have h2 := (hspec l hl).2.2
    rw [hkl] at h1
    have : k - 1 = l - 1 := h1.symm.trans h2
    simp only [mem_Ici] at hk hl
    omega
  · rintro ⟨hinj, hinf⟩ k hk
    obtain ⟨z, hzS, hz0, hzn⟩ := exists_count hfin hinj hinf (k - 1)
    exact Classical.epsilon_spec (p := fun z => z ∈ S ∧ f z = 0 ∧
      ({w : ℂ | w ∈ S ∧ f w = 0 ∧ ‖w‖ < ‖z‖} : Set ℂ).ncard = k - 1) ⟨z, hzS, hz0, hzn⟩

/-- **The modulus enumeration is strictly increasing**, once it is well defined. -/
theorem zcnt_orderedZero_strictMonoOn
    (hfin : ∀ r : ℝ, {w : ℂ | w ∈ S ∧ f w = 0 ∧ ‖w‖ < r}.Finite)
    (hspec : ∀ k : ℕ, 1 ≤ k → orderedZero f S k ∈ S ∧ f (orderedZero f S k) = 0 ∧
        ({w : ℂ | w ∈ S ∧ f w = 0 ∧ ‖w‖ < ‖orderedZero f S k‖} : Set ℂ).ncard = k - 1) :
    StrictMonoOn (fun k => ‖orderedZero f S k‖) (Ici 1) := by
  intro k hk l hl hkl
  simp only [mem_Ici] at hk hl
  by_contra hle
  push Not at hle
  have := B_ncard_le hfin hle
  have h1 : (B f S ‖orderedZero f S k‖).ncard = k - 1 := (hspec k hk).2.2
  have h2 : (B f S ‖orderedZero f S l‖).ncard = l - 1 := (hspec l hl).2.2
  omega

/-- **Every zero in `S` is enumerated**: the zero `z` is the `(n+1)`-st, `n` being the number of
zeros in `S` of smaller modulus. -/
theorem zcnt_eq_orderedZero
    (hfin : ∀ r : ℝ, {w : ℂ | w ∈ S ∧ f w = 0 ∧ ‖w‖ < r}.Finite)
    (hspec : ∀ k : ℕ, 1 ≤ k → orderedZero f S k ∈ S ∧ f (orderedZero f S k) = 0 ∧
        ({w : ℂ | w ∈ S ∧ f w = 0 ∧ ‖w‖ < ‖orderedZero f S k‖} : Set ℂ).ncard = k - 1)
    {z : ℂ} (hzS : z ∈ S) (hz0 : f z = 0) :
    ∃ k : ℕ, 1 ≤ k ∧ z = orderedZero f S k := by
  set n := (B f S ‖z‖).ncard
  refine ⟨n + 1, by omega, ?_⟩
  obtain ⟨huS, hu0, hun⟩ := hspec (n + 1) (by omega)
  set u := orderedZero f S (n + 1)
  change (B f S ‖u‖).ncard = n + 1 - 1 at hun
  rcases lt_trichotomy ‖u‖ ‖z‖ with h | h | h
  · have := B_ncard_lt hfin huS hu0 h
    omega
  · exact injOn_of_spec hfin hspec ⟨hzS, hz0⟩ ⟨huS, hu0⟩ h.symm
  · have := B_ncard_lt hfin hzS hz0 h
    omega

end Enumeration

/-- **Discs to enumerations.** If each disc `ball (c k) (r k)` contains exactly one zero of `f`
in `S`, the discs lie in annuli of increasing radius (`‖c k‖ + r k ≤ ‖c (k+1)‖ - r (k+1)`), and
every zero of `f` in `S` lies in one of the discs, then the zeros of `f` in `S` have pairwise
distinct moduli and are infinitely many. -/
theorem zcnt_injOn_infinite_of_discs {f : ℂ → ℂ} {S : Set ℂ} {c : ℕ → ℂ} {r : ℕ → ℝ}
    (hone : ∀ k, ∃! z, z ∈ S ∧ f z = 0 ∧ z ∈ ball (c k) (r k))
    (hsep : ∀ k, ‖c k‖ + r k ≤ ‖c (k + 1)‖ - r (k + 1))
    (hcover : ∀ z, z ∈ S → f z = 0 → ∃ k, z ∈ ball (c k) (r k)) :
    InjOn (fun z : ℂ => ‖z‖) {z : ℂ | z ∈ S ∧ f z = 0} ∧
      {z : ℂ | z ∈ S ∧ f z = 0}.Infinite := by
  have hr : ∀ k, 0 ≤ r k := fun k => by
    obtain ⟨z, ⟨-, -, hz⟩, -⟩ := hone k
    exact (dist_nonneg.trans (mem_ball.mp hz).le)
  have hmono : ∀ k l, k < l → ‖c k‖ + r k ≤ ‖c l‖ - r l := by
    intro k l hkl
    induction l with
    | zero => omega
    | succ l ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hkl with h | h
      · have := ih h
        have := hsep l
        linarith [hr l]
      · subst h; exact hsep k
  have hnorm : ∀ k z, z ∈ ball (c k) (r k) → ‖c k‖ - r k < ‖z‖ ∧ ‖z‖ < ‖c k‖ + r k := by
    intro k z hz
    have hd : ‖z - c k‖ < r k := by simpa [dist_eq_norm] using hz
    constructor
    · linarith [norm_sub_norm_le (c k) z, norm_sub_rev z (c k)]
    · linarith [norm_le_insert' z (c k)]
  have hlt : ∀ k l z w, k < l → z ∈ ball (c k) (r k) → w ∈ ball (c l) (r l) → ‖z‖ < ‖w‖ :=
    fun k l z w hkl hz hw => by
      have := hmono k l hkl
      linarith [(hnorm k z hz).2, (hnorm l w hw).1]
  refine ⟨fun z hz w hw hzw => ?_, ?_⟩
  · simp only at hzw
    obtain ⟨k, hk⟩ := hcover z hz.1 hz.2
    obtain ⟨l, hl⟩ := hcover w hw.1 hw.2
    rcases lt_trichotomy k l with h | rfl | h
    · exact absurd hzw (hlt k l z w h hk hl).ne
    · exact (hone k).unique ⟨hz.1, hz.2, hk⟩ ⟨hw.1, hw.2, hl⟩
    · exact absurd hzw (hlt l k w z h hl hk).ne'
  · choose z hz _ using hone
    refine Set.infinite_of_injective_forall_mem (f := z) (fun k l hkl => ?_)
      fun k => ⟨(hz k).1, (hz k).2.1⟩
    rcases lt_trichotomy k l with h | h | h
    · exact absurd (congrArg norm hkl) (hlt k l _ _ h (hz k).2.2 (hz l).2.2).ne
    · exact h
    · exact absurd (congrArg norm hkl) (hlt l k _ _ h (hz l).2.2 (hz k).2.2).ne'

/-- If a natural-valued function has finite sum `1` over a set `s`, then exactly one point
of `s` has a nonzero value. -/
private lemma existsUnique_ne_zero_of_finsum_mem_eq_one {α : Type*} {s : Set α} {g : α → ℕ}
    (h : (∑ᶠ x ∈ s, g x) = 1) : ∃! z, z ∈ s ∧ g z ≠ 0 := by
  classical
  -- the support of `g` in `s` is finite, since the sum is nonzero
  have hfin : (s ∩ Function.support g).Finite := by
    by_contra hinf
    have : (∑ᶠ x ∈ s, g x) = 0 := by
      rw [finsum_mem_def]
      apply finsum_of_infinite_support
      intro hfin'
      apply hinf
      refine hfin'.subset ?_
      rintro x ⟨hxb, hxs⟩
      simp only [Function.mem_support, ne_eq] at hxs ⊢
      simpa [hxb] using hxs
    omega
  obtain ⟨z, hz, hzg⟩ : ∃ z ∈ s, g z ≠ 0 := by
    by_contra h'
    push Not at h'
    have : (∑ᶠ x ∈ s, g x) = 0 := finsum_mem_eq_zero_of_forall_eq_zero fun x hx => h' x hx
    omega
  refine ⟨z, ⟨hz, hzg⟩, ?_⟩
  rintro y ⟨hy, hyg⟩
  by_contra hyz
  have h2 : ∑ i ∈ ({y, z} : Finset α), g i ≤ ∑ᶠ x ∈ s, g x := by
    rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Set.Finite.mem_toFinset]
      rcases hx with rfl | rfl
      · exact ⟨hy, hyg⟩
      · exact ⟨hz, hzg⟩
    · intros; exact Nat.zero_le _
  rw [Finset.sum_pair hyz] at h2
  omega

/-- **Zero count one means exactly one zero.** If `f` is analytic on `closedBall c R` and its
zero count in the open disc (with multiplicity) is `1`, then `f` has exactly one zero there. -/
theorem zcnt_existsUnique_of_count_eq_one {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hcount : (∑ᶠ z ∈ ball c R, analyticOrderNatAt f z) = 1) :
    ∃! z, z ∈ ball c R ∧ f z = 0 := by
  obtain ⟨z, ⟨hz, hzord⟩, huniq⟩ := existsUnique_ne_zero_of_finsum_mem_eq_one hcount
  have hzero : ∀ y ∈ ball c R, analyticOrderNatAt f y ≠ 0 → f y = 0 := by
    intro y hy hord
    by_contra hne
    exact hord (by simp [analyticOrderNatAt,
      (hf y (ball_subset_closedBall hy)).analyticOrderAt_eq_zero.2 hne])
  -- the order is finite everywhere on the closed disc
  have hnetop : analyticOrderAt f z ≠ ⊤ := by
    intro htop
    exact hzord (by simp [analyticOrderNatAt, htop])
  have hfin_all : ∀ y ∈ closedBall c R, analyticOrderAt f y ≠ ⊤ := fun y hy =>
    hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected
      (ball_subset_closedBall hz) hy hnetop
  have hpos : ∀ y ∈ ball c R, f y = 0 → analyticOrderNatAt f y ≠ 0 := by
    intro y hy hy0
    have h1 : analyticOrderAt f y ≠ 0 :=
      (hf y (ball_subset_closedBall hy)).analyticOrderAt_ne_zero.2 hy0
    simp [analyticOrderNatAt, ENat.toNat_eq_zero, h1, hfin_all y (ball_subset_closedBall hy)]
  exact ⟨z, ⟨hz, hzero z hz hzord⟩, fun y hy => huniq y ⟨hy.1, hpos y hy.1 hy.2⟩⟩

/-- **Rouché transfer of a single zero.** If `f` and `g` are analytic on `closedBall c R`,
`‖f z - g z‖ < ‖g z‖` on the bounding circle, and `g` has zero count `1` in the open disc, then
`f` has exactly one zero in the open disc. -/
theorem zcnt_existsUnique_zero_of_rouche {f g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hs : ∀ z ∈ sphere c R, ‖f z - g z‖ < ‖g z‖)
    (hcount : (∑ᶠ z ∈ ball c R, analyticOrderNatAt g z) = 1) :
    ∃! z, z ∈ ball c R ∧ f z = 0 := by
  refine zcnt_existsUnique_of_count_eq_one hf ?_
  rw [← TauCeti.rouche hR hg hf (fun z hz => by rw [norm_sub_rev]; exact hs z hz), hcount]

end DLMF
