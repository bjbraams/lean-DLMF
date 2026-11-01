/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Zeros.RealZeros

/-!
# Limits of Bernoulli zeros from uniform convergence

This file proves the limiting locations of the real zeros of the Bernoulli polynomials (DLMF
§24.12(i)) and the count `R(n)` of real zeros.

## Main results

* `tendsto_bernoulliRealZero_even`, `tendsto_bernoulliRealZero_odd`: for fixed `m`, the limits
  of `x_{2m-1}^{(n)}` and `x_{2m}^{(n)}` as `n → ∞` through even and through odd values
  (DLMF 24.12.4, 24.12.5).
* `bernoulliRealZero_one_of_odd`, `bernoulliRealZero_two_of_odd`: `x_1^{(n)} = 1/2` and
  `x_2^{(n)} = 1` for odd `n`.
* `bernoulliRealZeroCount_eq_self`: `R(n) = n` for `1 ≤ n ≤ 5`.
* `bernoulliRealZeroCount_isEquivalent`: `R(n) ∼ 2n/(πe)` (DLMF 24.12.6).
* `tendsto_eulerRealZero_two_mul`, `tendsto_eulerRealZero_two_mul_add_one`: the limits of the
  Euler zeros, used for DLMF 24.12.8 and the corrected 24.12.11.

## Implementation notes

The limits "as `n → ∞` with `m` fixed" for even (odd) `n` are taken along `n = 2k`
(`n = 2k + 1`), `k → ∞`. The zero `x_{2m}^{(n)}` exists for large `n`, so the totalized value
does not matter in these limits. The limits are proved from the uniform limits 24.11.5–24.11.6
by a zero-counting (Hurwitz-type) argument (`realZeroCountBelow`); `R(n) = n` for `n ≤ 5` is
proved from the explicit polynomials.

## References

* NIST DLMF §24.12; Delange (1987).
-/

@[expose] public noncomputable section

open Filter Asymptotics Topology Polynomial

open scoped Nat Real

namespace DLMF.BernoulliEuler

/-! ### Limits of zeros from uniform convergence (24.12.4, 24.12.5, 24.12.8)

If `c_k P_k → g` and `c_k P_k' → g'` uniformly on compact subsets of `[1/2, ∞)`, where `g` has
simple zeros `z_1 < z_2 < ⋯` in `[1/2, ∞)`, then the `j`-th zero of `P_k` in `[1/2, ∞)` tends
to `z_j` (Hurwitz-type argument by counting zeros, Rolle and the mean value theorem). The
uniform limits are DLMF 24.11.5–24.11.6 (`DLMF.BernoulliEuler.Asymptotics`). -/
/-- In a sorted list, an index below the number of entries `< c` gives an entry `< c`. -/
private lemma getD_lt_of_lt_length_filter {l : List ℝ} (hs : l.Pairwise (· ≤ ·)) {c : ℝ} {i : ℕ}
    (h : i < (l.filter (fun x => decide (x < c))).length) : l.getD i 0 < c := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
    have hs' := List.pairwise_cons.mp hs
    by_cases hac : a < c
    · rw [List.filter_cons_of_pos (by simpa using hac), List.length_cons] at h
      rcases i with _ | i
      · simpa using hac
      · simp only [List.getD_cons_succ]
        exact ih hs'.2 (by omega)
    · have : l.filter (fun x => decide (x < c)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        have := hs'.1 x hx
        simp only [decide_eq_true_eq, not_lt]
        linarith [not_lt.mp hac]
      rw [List.filter_cons_of_neg (by simpa using hac), this] at h
      simp at h

/-- In a sorted list, an entry `< c` at index `i` lies among the entries `< c`. -/
private lemma lt_length_filter_of_getD_lt {l : List ℝ} (hs : l.Pairwise (· ≤ ·)) {c : ℝ} {i : ℕ}
    (hi : i < l.length) (h : l.getD i 0 < c) : i < (l.filter (fun x => decide (x < c))).length := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    have hs' := List.pairwise_cons.mp hs
    rcases i with _ | i
    · simp only [List.getD_cons_zero] at h
      rw [List.filter_cons_of_pos (by simpa using h)]; simp
    · simp only [List.getD_cons_succ] at h
      simp only [List.length_cons] at hi
      have hmem : l.getD i 0 ∈ l := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
      have hac : a < c := lt_of_le_of_lt (hs'.1 _ hmem) h
      rw [List.filter_cons_of_pos (by simpa using hac), List.length_cons]
      have := ih hs'.2 (by omega) h
      omega

/-- The number of roots (with multiplicity) of `p` in `[1/2, c)`. -/
noncomputable def realZeroCountBelow (p : ℝ[X]) (c : ℝ) : ℕ :=
  Multiset.card (p.roots.filter (fun x => 1 / 2 ≤ x ∧ x < c))

/-- The number of listed zeros below `c` is `realZeroCountBelow p c`. -/
private lemma length_filter_realZerosGE (p : ℝ[X]) (c : ℝ) :
    ((realZerosGE p).filter (fun x => decide (x < c))).length = realZeroCountBelow p c := by
  rw [realZeroCountBelow, ← Multiset.coe_card, ← Multiset.filter_coe, realZerosGE, Multiset.sort_eq,
    Multiset.filter_filter]
  congr 2
  funext x; simp [and_comm]

/-- If `realZeroCountBelow p (z - r) = j - 1` and `realZeroCountBelow p (z + r) = j`, then the `j`-th zero of
`p` in `[1/2, ∞)` lies in `[z - r, z + r)`. -/
private lemma getD_realZerosGE_mem_Ico_of_count {p : ℝ[X]} {j : ℕ} (hj : 1 ≤ j) {a b : ℝ}
    (ha : realZeroCountBelow p a = j - 1) (hb : realZeroCountBelow p b = j) :
    a ≤ (realZerosGE p).getD (j - 1) 0 ∧ (realZerosGE p).getD (j - 1) 0 < b := by
  have hs := realZerosGE_sorted p
  have hlb : j - 1 < ((realZerosGE p).filter (fun x => decide (x < b))).length := by
    rw [length_filter_realZerosGE, hb]; omega
  refine ⟨?_, getD_lt_of_lt_length_filter hs hlb⟩
  by_contra hlt
  push Not at hlt
  have hlen : j - 1 < (realZerosGE p).length :=
    lt_of_lt_of_le hlb (List.length_filter_le _ _)
  have := lt_length_filter_of_getD_lt hs hlen hlt
  rw [length_filter_realZerosGE, ha] at this
  omega

/-- Splitting the zero count at `a ≤ b`. -/
private lemma realZeroCountBelow_eq_add {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b) :
    realZeroCountBelow p b = realZeroCountBelow p a +
      Multiset.card (p.roots.filter (fun x => 1 / 2 ≤ x ∧ a ≤ x ∧ x < b)) := by
  rw [realZeroCountBelow, realZeroCountBelow, ← Multiset.card_add,
    ← Multiset.filter_add_not (fun x => x < a) (p.roots.filter fun x => 1 / 2 ≤ x ∧ x < b),
    Multiset.filter_filter, Multiset.filter_filter]
  congr 2
  · congr 1; funext x; apply propext; constructor
    · rintro ⟨h3, h1, h2⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h3, h1, by linarith⟩
  · congr 1; funext x; apply propext; constructor
    · rintro ⟨h3, h1, h2⟩; exact ⟨h1, not_lt.mp h3, h2⟩
    · rintro ⟨h1, h3, h2⟩; exact ⟨not_lt.mpr h3, h1, h2⟩

/-- No roots satisfy `q` if `p` does not vanish where `q` holds. -/
private lemma card_filter_roots_eq_zero {p : ℝ[X]} {q : ℝ → Prop} [DecidablePred q]
    (h : ∀ x, q x → p.eval x ≠ 0) : Multiset.card (p.roots.filter q) = 0 := by
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro x hx hq
  exact h x hq (isRoot_of_mem_roots hx)

/-- Exactly one root (with multiplicity) satisfies `q` when `ζ` is the unique zero there and
simple. -/
private lemma card_filter_roots_eq_one {p : ℝ[X]} (hp : p ≠ 0) {q : ℝ → Prop} [DecidablePred q] {ζ : ℝ}
    (hζ : q ζ) (hζ0 : p.eval ζ = 0) (hd : p.derivative.eval ζ ≠ 0)
    (huniq : ∀ x, q x → p.eval x = 0 → x = ζ) : Multiset.card (p.roots.filter q) = 1 := by
  have hfilt : p.roots.filter q = p.roots.filter (fun x => x = ζ) := by
    refine Multiset.filter_congr fun x hx => ⟨fun h => huniq x h (isRoot_of_mem_roots hx), ?_⟩
    rintro rfl; exact hζ
  rw [hfilt, Multiset.filter_eq', Multiset.card_replicate, count_roots]
  have h1 : 1 ≤ p.rootMultiplicity ζ := (rootMultiplicity_pos hp).mpr hζ0
  have h2 : p.rootMultiplicity ζ ≤ 1 := by
    by_contra h; push Not at h
    exact hd ((one_lt_rootMultiplicity_iff_isRoot hp).mp h).2
  omega

/-- Rolle: a function with nonvanishing derivative on `[a, b]` has at most one zero there. -/
private lemma eq_of_zero_of_deriv_ne_zero {F F' : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (F' x) x) {a b : ℝ}
    (hF' : ∀ x ∈ Set.Icc a b, F' x ≠ 0) {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hFx : F x = 0) (hFy : F y = 0) : x = y := by
  by_contra hne
  have hcont : Continuous F := continuous_iff_continuousAt.mpr fun t => (hF t).continuousAt
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hlt hcont.continuousOn (hFx.trans hFy.symm)
      fun t _ => hF t
    exact hF' c ⟨by linarith [hx.1, hc.1], by linarith [hy.2, hc.2]⟩ hc0
  · obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hlt hcont.continuousOn (hFy.trans hFx.symm)
      fun t _ => hF t
    exact hF' c ⟨by linarith [hy.1, hc.1], by linarith [hx.2, hc.2]⟩ hc0

/-- Mean value estimate at a simple zero: if `g z = 0` and `|g' - s| < |s|/4` on `[z - r, z + r]`,
then `s g(z ± r) ≷ ± (3/4) r s²`. -/
private lemma mul_apply_bounds_near_simple_zero {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) {z r s : ℝ}
    (hr : 0 < r) (hgz : g z = 0) (hd : ∀ x, |x - z| ≤ r → |g' x - s| < |s| / 4) :
    3 / 4 * r * s ^ 2 < s * g (z + r) ∧ s * g (z - r) < -(3 / 4 * r * s ^ 2) := by
  have hcont : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  have key : ∀ ξ, |ξ - z| ≤ r → 3 / 4 * s ^ 2 < s * g' ξ := by
    intro ξ hξ
    have h1 := hd ξ hξ
    have h2 : |s * (g' ξ - s)| < s ^ 2 / 4 + 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg s, abs_nonneg (g' ξ - s), sq_abs s]
    by_cases hs : s = 0
    · subst hs; simp at h1; linarith [abs_nonneg (g' ξ)]
    have hsp : 0 < |s| := abs_pos.mpr hs
    have h3 : |s * (g' ξ - s)| < s ^ 2 / 4 := by
      rw [abs_mul, ← sq_abs s]
      nlinarith
    have := (abs_lt.mp h3).1
    nlinarith
  constructor
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope g g' (by linarith : z < z + r)
      hcont.continuousOn fun t _ => hg t
    rw [hgz, sub_zero, show z + r - z = r by ring] at hξe
    have := key ξ (by rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2])
    rw [hξe] at this
    have h' : s * g (z + r) = r * (s * (g (z + r) / r)) := by field_simp
    rw [h']
    nlinarith
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope g g' (by linarith : z - r < z)
      hcont.continuousOn fun t _ => hg t
    rw [hgz, zero_sub, show z - (z - r) = r by ring] at hξe
    have := key ξ (by rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2])
    rw [hξe] at this
    have h' : s * g (z - r) = -(r * (s * (-g (z - r) / r))) := by field_simp
    rw [h']
    nlinarith

/-- Zeros of a uniformly convergent sequence of polynomials: if `c_k P_k → g` and
`c_k P_k' → g'` uniformly on bounded subsets of `[1/2, ∞)`, and the zeros of `g` in `[1/2, ∞)`
are the simple zeros `z₁ < z₂ < ⋯`, then the `j`-th zero of `P_k` in `[1/2, ∞)` tends to `z_j`.
(If `z₁ = 1/2` we require `P_k(1/2) = 0`.) -/
private lemma tendsto_realZerosGE_getD (P : ℕ → ℝ[X]) (c : ℕ → ℝ) (hc : ∀ k, c k ≠ 0)
    (g g' : ℝ → ℝ) (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g')
    (z : ℕ → ℝ) (hz : StrictMono z) (hz1 : 1 / 2 ≤ z 1)
    (hzero : ∀ x, 1 / 2 ≤ x → g x = 0 → ∃ i, 1 ≤ i ∧ x = z i)
    (hgz : ∀ i, 1 ≤ i → g (z i) = 0) (hg'z : ∀ i, 1 ≤ i → g' (z i) ≠ 0)
    (hhalf : z 1 = 1 / 2 → ∀ k, (P k).eval (1 / 2) = 0)
    (hconv : ∀ M ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x, 1 / 2 ≤ x → x ≤ M →
      |c k * (P k).eval x - g x| < ε ∧ |c k * (P k).derivative.eval x - g' x| < ε)
    {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun k => (realZerosGE (P k)).getD (j - 1) 0) atTop (𝓝 (z j)) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hgcont : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  -- choice of the radius `r`
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ε / 2 ∧ r < 1 ∧ (z 1 ≠ 1 / 2 → r < z 1 - 1 / 2) ∧
      (∀ i ∈ Finset.Icc 1 j, 2 * r < z (i + 1) - z i) ∧
      (∀ i ∈ Finset.Icc 1 j, ∀ x, |x - z i| ≤ r → |g' x - g' (z i)| < |g' (z i)| / 4) := by
    have hlt : ∀ a : ℝ, 0 < a → ∀ᶠ r in 𝓝[>] (0 : ℝ), r < a := fun a ha =>
      (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds
    have e3 : ∀ᶠ r in 𝓝[>] (0 : ℝ), z 1 ≠ 1 / 2 → r < z 1 - 1 / 2 := by
      by_cases h1 : z 1 = 1 / 2
      · exact Eventually.of_forall fun _ h => absurd h1 h
      · exact (hlt _ (by have := lt_of_le_of_ne hz1 (Ne.symm h1); linarith)).mono
          fun _ h _ => h
    have e4 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ i ∈ Finset.Icc 1 j, 2 * r < z (i + 1) - z i := by
      refine (eventually_all_finset _).mpr fun i _ => ?_
      have : 0 < z (i + 1) - z i := sub_pos.mpr (hz (Nat.lt_succ_self i))
      exact (hlt _ (by linarith : 0 < (z (i + 1) - z i) / 2)).mono fun r hr => by linarith
    have e5 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ i ∈ Finset.Icc 1 j, ∀ x, |x - z i| ≤ r →
        |g' x - g' (z i)| < |g' (z i)| / 4 := by
      refine (eventually_all_finset _).mpr fun i hi => ?_
      have hs : 0 < |g' (z i)| / 4 := by
        have := hg'z i (Finset.mem_Icc.mp hi).1; positivity
      obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff.mp
        ((hg'.tendsto (z i)).eventually (Metric.ball_mem_nhds _ hs))
      refine (hlt ρ hρ).mono fun r hr x hx => ?_
      have := hρ' (show dist x (z i) < ρ by rw [Real.dist_eq]; linarith)
      simpa [Metric.mem_ball, Real.dist_eq] using this
    filter_upwards [hlt (ε / 2) (by linarith), hlt 1 one_pos, e3, e4, e5] with r h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨r, ⟨hrε, hr1, hrz1, hgap, hg'r⟩, hr0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hr0 : (0 : ℝ) < r := hr0
  have hzle : ∀ {a b}, a ≤ b → z a ≤ z b := fun h => hz.monotone h
  have hzj : ∀ i ∈ Finset.Icc 1 j, z i ≤ z j := fun i hi => hzle (Finset.mem_Icc.mp hi).2
  -- the compact set where `g` has no zeros
  set Kc : Set ℝ := Set.Icc (1 / 2) (z j + r) ∩ ⋂ i ∈ Finset.Icc 1 j, {x | r ≤ |x - z i|}
  have hKc : IsCompact Kc := isCompact_Icc.inter_right (isClosed_biInter fun i _ =>
    isClosed_le continuous_const (continuous_id.sub continuous_const).abs)
  have hgK : ∀ x ∈ Kc, g x ≠ 0 := by
    intro x hx h0
    obtain ⟨i, hi, rfl⟩ := hzero x hx.1.1 h0
    have hx2 := Set.mem_iInter₂.mp hx.2
    by_cases hij : i ≤ j
    · have := hx2 i (Finset.mem_Icc.mpr ⟨hi, hij⟩)
      simp at this; linarith
    · have h1 := hgap j (Finset.mem_Icc.mpr ⟨hj, le_rfl⟩)
      have h2 : z (j + 1) ≤ z i := hzle (by omega)
      linarith [hx.1.2]
  obtain ⟨η0, hη0, hη0K⟩ : ∃ η0 : ℝ, 0 < η0 ∧ ∀ x ∈ Kc, η0 ≤ |g x| := by
    rcases Kc.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun x hx => by rw [he] at hx; exact hx.elim⟩
    · obtain ⟨x0, hx0, hmin⟩ := hKc.exists_isMinOn hne (hgcont.abs.continuousOn)
      exact ⟨|g x0|, abs_pos.mpr (hgK x0 hx0), fun x hx => hmin hx⟩
  set s : ℕ → ℝ := fun i => g' (z i)
  have hs0 : ∀ i ∈ Finset.Icc 1 j, 0 < |s i| := fun i hi =>
    abs_pos.mpr (hg'z i (Finset.mem_Icc.mp hi).1)
  have hk2 : ∀ i ∈ Finset.Icc 1 j, ∀ᶠ k in atTop, ∀ x, 1 / 2 ≤ x → x ≤ z j + 1 →
      |c k * (P k).eval x - g x| < min (r * |s i| / 2) (|s i| / 4) ∧
        |c k * (P k).derivative.eval x - g' x| < min (r * |s i| / 2) (|s i| / 4) := fun i hi =>
    hconv _ _ (lt_min (by have := hs0 i hi; positivity) (by have := hs0 i hi; positivity))
  filter_upwards [hconv (z j + 1) η0 hη0, (eventually_all_finset _).mpr hk2] with k hk1 hk2
  set F : ℝ → ℝ := fun x => c k * (P k).eval x
  set F' : ℝ → ℝ := fun x => c k * (P k).derivative.eval x
  have hF : ∀ x, HasDerivAt F (F' x) x := fun x => ((P k).hasDerivAt x).const_mul (c k)
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun t => (hF t).continuousAt
  have hPF : ∀ x, (P k).eval x = 0 ↔ F x = 0 := fun x => by
    simp only [F, mul_eq_zero, hc k, false_or]
  have hnoK : ∀ x ∈ Kc, (P k).eval x ≠ 0 := by
    intro x hx h0
    have := (hk1 x hx.1.1 (by linarith [hx.1.2])).1
    rw [show c k * (P k).eval x = 0 by rw [h0, mul_zero], zero_sub, abs_neg] at this
    linarith [hη0K x hx]
  -- one simple root near each `z i`
  have hone : ∀ i ∈ Finset.Icc 1 j, Multiset.card ((P k).roots.filter
      (fun x => 1 / 2 ≤ x ∧ z i - r ≤ x ∧ x < z i + r)) = 1 := by
    intro i hi
    have hi1 := (Finset.mem_Icc.mp hi).1
    have hbd := hk2 i hi
    have hF'ne : ∀ x, 1 / 2 ≤ x → |x - z i| ≤ r → F' x ≠ 0 := by
      intro x hx1 hx2 h0
      have h1 := (hbd x hx1 (by
        have := hzj i hi; rw [abs_le] at hx2; linarith)).2
      have h2 := hg'r i hi x hx2
      have hm := min_le_right (r * |s i| / 2) (|s i| / 4)
      change |F' x - g' x| < _ at h1
      rw [h0, zero_sub, abs_neg] at h1
      have : |s i| ≤ |g' x| + |g' x - s i| := by
        calc |s i| = |g' x - (g' x - s i)| := by ring_nf
          _ ≤ |g' x| + |g' x - s i| := abs_sub _ _
      have h2' : |g' x - s i| < |s i| / 4 := h2
      linarith [hs0 i hi]
    obtain ⟨ζ, hζ1, hζ2, hζ3, hζ0⟩ : ∃ ζ, 1 / 2 ≤ ζ ∧ z i - r ≤ ζ ∧ ζ < z i + r ∧ F ζ = 0 := by
      by_cases hzi : z i = 1 / 2
      · have hi1' : i = 1 := by
          by_contra hne
          have : z 1 < z i := hz (by omega)
          linarith
        subst hi1'
        refine ⟨1 / 2, le_rfl, by linarith, by linarith, (hPF _).mp (hhalf hzi k)⟩
      · have hzr : 1 / 2 ≤ z i - r := by
          rcases Nat.lt_or_ge i 2 with h | h
          · have : i = 1 := by omega
            subst this; linarith [hrz1 hzi]
          · have h12 := hgap 1 (Finset.mem_Icc.mpr ⟨le_rfl, hj⟩)
            have : z 2 ≤ z i := hzle h
            linarith
        obtain ⟨hp, hm⟩ := mul_apply_bounds_near_simple_zero hg hr0 (hgz i hi1) (hg'r i hi)
        have hb1 := (hbd (z i + r) (by linarith) (by linarith [hzj i hi])).1
        have hb2 := (hbd (z i - r) hzr (by linarith [hzj i hi])).1
        have hmin := min_le_left (r * |s i| / 2) (|s i| / 4)
        have hsi := hs0 i hi
        change |F (z i + r) - g (z i + r)| < _ at hb1
        change |F (z i - r) - g (z i - r)| < _ at hb2
        have e1 : |s i * (F (z i + r) - g (z i + r))| < r * s i ^ 2 / 2 := by
          rw [abs_mul, ← sq_abs (s i)]
          nlinarith
        have e2 : |s i * (F (z i - r) - g (z i - r))| < r * s i ^ 2 / 2 := by
          rw [abs_mul, ← sq_abs (s i)]
          nlinarith
        have f1 : 0 < s i * F (z i + r) := by
          have := (abs_lt.mp e1).1; nlinarith
        have f2 : s i * F (z i - r) < 0 := by
          have := (abs_lt.mp e2).2; nlinarith
        have hprod : F (z i - r) * F (z i + r) < 0 := by
          have : (s i * F (z i - r)) * (s i * F (z i + r)) < 0 := mul_neg_of_neg_of_pos f2 f1
          nlinarith [sq_nonneg (s i), sq_pos_of_pos hsi, sq_abs (s i)]
        obtain ⟨ζ, hζ, hζ0⟩ := exists_Ioo_eq_zero_of_mul_neg hFc (by linarith) hprod
        exact ⟨ζ, by linarith [hζ.1], hζ.1.le, hζ.2, hζ0⟩
    have hP0 : P k ≠ 0 := fun h0 => hF'ne ζ hζ1 (by rw [abs_le]; constructor <;> linarith)
      (by simp only [F', h0, derivative_zero, eval_zero, mul_zero])
    have hIcc : ∀ x, 1 / 2 ≤ x → z i - r ≤ x → x < z i + r →
        x ∈ Set.Icc (max (1 / 2) (z i - r)) (z i + r) := fun x h1 h2 h3 =>
      ⟨max_le h1 h2, h3.le⟩
    refine card_filter_roots_eq_one hP0 ⟨hζ1, hζ2, hζ3⟩ ((hPF ζ).mpr hζ0) ?_ ?_
    · intro hd
      exact hF'ne ζ hζ1 (by rw [abs_le]; constructor <;> linarith)
        (by simp only [F', hd, mul_zero])
    · rintro x ⟨hx1, hx2, hx3⟩ hx0
      refine eq_of_zero_of_deriv_ne_zero hF (fun y hy => hF'ne y (le_of_max_le_left hy.1)
        (by rw [abs_le]; constructor <;> linarith [le_of_max_le_right hy.1, hy.2]))
        (hIcc x hx1 hx2 hx3) (hIcc ζ hζ1 hζ2 hζ3) ((hPF x).mp hx0) hζ0
  -- counting
  have hC0 : realZeroCountBelow (P k) (z 1 - r) = 0 := by
    refine card_filter_roots_eq_zero fun x ⟨hx1, hx2⟩ => hnoK x ⟨⟨hx1, ?_⟩, ?_⟩
    · linarith [hzj 1 (Finset.mem_Icc.mpr ⟨le_rfl, hj⟩)]
    · refine Set.mem_iInter₂.mpr fun l hl => ?_
      have := hzle (Finset.mem_Icc.mp hl).1
      show r ≤ |x - z l|
      rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
  have hCgap : ∀ i, 1 ≤ i → i < j →
      realZeroCountBelow (P k) (z (i + 1) - r) = realZeroCountBelow (P k) (z i + r) := by
    intro i hi hij
    have hg1 := hgap i (Finset.mem_Icc.mpr ⟨hi, hij.le⟩)
    rw [realZeroCountBelow_eq_add (show z i + r ≤ z (i + 1) - r by linarith)]
    have h0 : ∀ x, (1 / 2 ≤ x ∧ z i + r ≤ x ∧ x < z (i + 1) - r) → (P k).eval x ≠ 0 := by
      rintro x ⟨hx1, hx2, hx3⟩
      refine hnoK x ⟨⟨hx1, ?_⟩, ?_⟩
      · linarith [hzj (i + 1) (Finset.mem_Icc.mpr ⟨by omega, hij⟩)]
      · refine Set.mem_iInter₂.mpr fun l hl => ?_
        show r ≤ |x - z l|
        rcases Nat.lt_or_ge i l with h | h
        · have := hzle (show i + 1 ≤ l by omega)
          rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
        · have := hzle h
          rw [abs_of_nonneg (by linarith)]; linarith
    rw [card_filter_roots_eq_zero h0, add_zero]
  have hCstep : ∀ i ∈ Finset.Icc 1 j,
      realZeroCountBelow (P k) (z i + r) = realZeroCountBelow (P k) (z i - r) + 1 := by
    intro i hi
    rw [realZeroCountBelow_eq_add (show z i - r ≤ z i + r by linarith), hone i hi]
  have hind : ∀ i, 1 ≤ i → i ≤ j → realZeroCountBelow (P k) (z i - r) = i - 1 ∧
      realZeroCountBelow (P k) (z i + r) = i := by
    intro i hi hij
    induction i, hi using Nat.le_induction with
    | base =>
      exact ⟨hC0, by rw [hCstep 1 (Finset.mem_Icc.mpr ⟨le_rfl, hj⟩), hC0]⟩
    | succ i hi ih =>
      obtain ⟨_, h2⟩ := ih (by omega)
      have h3 := hCgap i hi (by omega)
      refine ⟨by rw [h3, h2]; omega, ?_⟩
      rw [hCstep (i + 1) (Finset.mem_Icc.mpr ⟨by omega, hij⟩), h3, h2]
  obtain ⟨hA, hB⟩ := hind j hj le_rfl
  obtain ⟨h1, h2⟩ := getD_realZerosGE_mem_Ico_of_count hj hA hB
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Transfer complex uniform convergence on compacts to real bounds on `[1/2, M]`. -/
private lemma eventually_abs_sub_lt_of_tendstoUniformlyOn {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    (h : ∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn F G atTop K) (a : ℂ)
    (f : ℕ → ℝ → ℝ) (gr : ℝ → ℝ) (hf : ∀ k x, (f k x : ℂ) = a * F k x)
    (hg : ∀ x, (gr x : ℂ) = a * G x) (M ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x : ℝ, 1 / 2 ≤ x → x ≤ M → |f k x - gr x| < ε := by
  have hpos : 0 < ε / (‖a‖ + 1) := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (h _ (isCompact_closedBall (0 : ℂ) M)) _ hpos]
    with k hk x hx1 hxM
  have hx : (x : ℂ) ∈ Metric.closedBall (0 : ℂ) M := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]; exact hxM
  have h1 := hk _ hx
  rw [dist_eq_norm, norm_sub_rev] at h1
  have h2 : |f k x - gr x| = ‖a‖ * ‖F k x - G x‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub, hf, hg, ← mul_sub, norm_mul]
  rw [h2]
  calc ‖a‖ * ‖F k x - G x‖ ≤ ‖a‖ * (ε / (‖a‖ + 1)) := by gcongr
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [norm_nonneg a]

/-- Shift an eventual statement by one index. -/
private lemma eventually_one_le_and_sub_one {Q : ℕ → Prop} (h : ∀ᶠ k in atTop, Q k) :
    ∀ᶠ k in atTop, 1 ≤ k ∧ Q (k - 1) :=
  (eventually_ge_atTop 1).and ((tendsto_sub_atTop_nat 1).eventually h)

/-- `(-1)^(m-1) = -(-1)^m`. -/
private lemma neg_one_zpow_natCast_sub_one (m : ℕ) : (-1 : ℂ) ^ ((m : ℤ) - 1) = -(-1) ^ m := by
  rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_one]; ring

/-- Real evaluation of a rational polynomial, cast to `ℂ`, is complex evaluation. -/
private lemma ofReal_eval_map_eq_aeval (p : ℚ[X]) (x : ℝ) :
    (((p.map (algebraMap ℚ ℝ)).eval x : ℝ) : ℂ) = aeval (x : ℂ) p :=
  (aeval_ofReal_eq_eval_map p x).symm

/-- Zeros of `cos (2πx)` in `[1/2, ∞)`. -/
private lemma exists_eq_of_cos_two_pi_mul_eq_zero {x : ℝ} (hx : 1 / 2 ≤ x) (h : Real.cos (2 * π * x) = 0) :
    ∃ i : ℕ, 1 ≤ i ∧ x = (i : ℝ) / 2 + 1 / 4 := by
  obtain ⟨l, hl⟩ := Real.cos_eq_zero_iff.mp h
  have hx' : x = (2 * l + 1) / 4 := by
    have := Real.pi_pos; field_simp at hl ⊢; nlinarith
  have hl1 : (1 : ℝ) ≤ l := by
    have : (0 : ℝ) < l := by rw [hx'] at hx; linarith
    have : (0 : ℤ) < l := by exact_mod_cast this
    exact_mod_cast (show (1 : ℤ) ≤ l by omega)
  lift l to ℕ using (by exact_mod_cast (by linarith : (0 : ℝ) ≤ l))
  exact ⟨l, by exact_mod_cast hl1, by rw [hx']; push_cast; ring⟩

/-- Zeros of `sin (a πx)` (`a > 0`) in `[1/2, ∞)`. -/
private lemma exists_eq_of_sin_mul_pi_mul_eq_zero {a x : ℝ} (ha : 0 < a) (h : Real.sin (a * π * x) = 0) :
    ∃ n : ℤ, x = n / a := by
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
  refine ⟨n, ?_⟩
  have := Real.pi_pos; field_simp; nlinarith

/-- `x_j^{(2k)} → j/2 + 1/4` as `k → ∞` (the zeros of `cos 2πx`). -/
private lemma tendsto_bernoulliRealZero_two_mul {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun k => bernoulliRealZero (2 * k) j) atTop (𝓝 ((j : ℝ) / 2 + 1 / 4)) := by
  have hcplx : ∀ (k : ℕ) (x : ℝ), (((-(-1) ^ k * (2 * π) ^ (2 * k) / (2 * (2 * k)!) *
      ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℝ)).eval x : ℝ)) : ℂ) =
      1 * ((-1 : ℂ) ^ ((k : ℤ) - 1) * (2 * π) ^ (2 * k) / (2 * (2 * k)!) *
        bernoulliPolyB (2 * k) x) := by
    intro k x
    rw [neg_one_zpow_natCast_sub_one, bernoulliPolyB, ← ofReal_eval_map_eq_aeval]; push_cast; ring
  have hcplx' : ∀ (m : ℕ) (x : ℝ), (((-(-1) ^ (m + 1) * (2 * π) ^ (2 * (m + 1)) /
      (2 * (2 * (m + 1))!) *
      ((Polynomial.bernoulli (2 * (m + 1))).map (algebraMap ℚ ℝ)).derivative.eval x : ℝ)) : ℂ) =
      (-(2 * π) : ℂ) * ((-1 : ℂ) ^ ((m : ℤ) - 1) * (2 * π) ^ (2 * m + 1) / (2 * (2 * m + 1)!) *
        bernoulliPolyB (2 * m + 1) x) := by
    intro m x
    rw [derivative_map, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, derivative_bernoulli_add_one,
      neg_one_zpow_natCast_sub_one, bernoulliPolyB, ← ofReal_eval_map_eq_aeval, Nat.factorial_succ]
    simp only [Polynomial.map_mul, eval_mul, Polynomial.map_add, Polynomial.map_natCast,
      Polynomial.map_one, eval_add, eval_natCast, eval_one]
    have hf : ((2 * m + 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hm : (2 * (m : ℂ) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * m + 1)
    push_cast
    field_simp
    ring
  refine tendsto_realZerosGE_getD (fun k => (Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℝ))
    (fun k => -(-1) ^ k * (2 * π) ^ (2 * k) / (2 * (2 * k)!)) (fun k => ?_)
    (fun x => Real.cos (2 * π * x)) (fun x => -(2 * π) * Real.sin (2 * π * x)) (fun x => ?_)
    (by fun_prop) (fun i => (i : ℝ) / 2 + 1 / 4) (fun a b hab => ?_) (by norm_num)
    (fun x hx h => exists_eq_of_cos_two_pi_mul_eq_zero hx h) (fun i _ => ?_) (fun i _ => ?_) (fun h => ?_) ?_ hj
  · have := Nat.factorial_pos (2 * k)
    have := Real.pi_pos
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (by norm_num)))
      (pow_ne_zero _ (by positivity))) (by positivity)
  · have := ((hasDerivAt_id x).const_mul (2 * π)).cos
    simpa [mul_comm] using this
  · have : (a : ℝ) < b := by exact_mod_cast hab
    simp only; linarith
  · show Real.cos (2 * π * ((i : ℝ) / 2 + 1 / 4)) = 0
    rw [Real.cos_eq_zero_iff]; exact ⟨i, by push_cast; ring⟩
  · have hc : Real.cos (2 * π * ((i : ℝ) / 2 + 1 / 4)) = 0 := by
      rw [Real.cos_eq_zero_iff]; exact ⟨i, by push_cast; ring⟩
    have hs := Real.sin_sq_add_cos_sq (2 * π * ((i : ℝ) / 2 + 1 / 4))
    rw [hc] at hs
    have := Real.pi_pos
    intro h0
    have : Real.sin (2 * π * ((i : ℝ) / 2 + 1 / 4)) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · linarith
      · exact h
    rw [this] at hs; norm_num at hs
  · norm_num at h
  · intro M ε hε
    filter_upwards [eventually_abs_sub_lt_of_tendstoUniformlyOn (fun K hK => tendstoUniformlyOn_bernoulli_even hK) 1 _
        (fun x => Real.cos (2 * π * x)) hcplx (fun x => by push_cast; ring) M ε hε,
      eventually_one_le_and_sub_one (eventually_abs_sub_lt_of_tendstoUniformlyOn (fun K hK => tendstoUniformlyOn_bernoulli_odd hK)
        (-(2 * π)) _ (fun x => -(2 * π) * Real.sin (2 * π * x)) hcplx'
        (fun x => by push_cast; ring) M ε hε)] with k h1 h2 x hx1 hxM
    obtain ⟨hk1, h2⟩ := h2
    refine ⟨h1 x hx1 hxM, ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact h2 x hx1 hxM

/-- Zeros of `sin (2πx)`, `sin (πx)` are simple: the derivative `cos` is nonzero there. -/
private lemma cos_ne_zero_of_sin_eq_zero {θ : ℝ} (h : Real.sin θ = 0) : Real.cos θ ≠ 0 := by
  intro h0; have hs := Real.sin_sq_add_cos_sq θ; rw [h, h0] at hs; norm_num at hs

/-- `x_j^{(2k+1)} → j/2` as `k → ∞` (the zeros of `sin 2πx`). -/
private lemma tendsto_bernoulliRealZero_two_mul_add_one {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun k => bernoulliRealZero (2 * k + 1) j) atTop (𝓝 ((j : ℝ) / 2)) := by
  have hcplx : ∀ (k : ℕ) (x : ℝ), (((-(-1) ^ k * (2 * π) ^ (2 * k + 1) / (2 * (2 * k + 1)!) *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℝ)).eval x : ℝ)) : ℂ) =
      1 * ((-1 : ℂ) ^ ((k : ℤ) - 1) * (2 * π) ^ (2 * k + 1) / (2 * (2 * k + 1)!) *
        bernoulliPolyB (2 * k + 1) x) := by
    intro k x
    rw [neg_one_zpow_natCast_sub_one, bernoulliPolyB, ← ofReal_eval_map_eq_aeval]; push_cast; ring
  have hcplx' : ∀ (k : ℕ) (x : ℝ), (((-(-1) ^ k * (2 * π) ^ (2 * k + 1) / (2 * (2 * k + 1)!) *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℝ)).derivative.eval x : ℝ)) : ℂ) =
      ((2 * π : ℝ) : ℂ) * ((-1 : ℂ) ^ ((k : ℤ) - 1) * (2 * π) ^ (2 * k) / (2 * (2 * k)!) *
        bernoulliPolyB (2 * k) x) := by
    intro k x
    rw [derivative_map, derivative_bernoulli_add_one,
      neg_one_zpow_natCast_sub_one, bernoulliPolyB, ← ofReal_eval_map_eq_aeval, Nat.factorial_succ]
    simp only [Polynomial.map_mul, eval_mul, Polynomial.map_add, Polynomial.map_natCast,
      Polynomial.map_one, eval_add, eval_natCast, eval_one]
    have hf : ((2 * k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hm : (2 * (k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * k)
    push_cast
    field_simp
    ring
  refine tendsto_realZerosGE_getD (fun k => (Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℝ))
    (fun k => -(-1) ^ k * (2 * π) ^ (2 * k + 1) / (2 * (2 * k + 1)!)) (fun k => ?_)
    (fun x => Real.sin (2 * π * x)) (fun x => (2 * π) * Real.cos (2 * π * x)) (fun x => ?_)
    (by fun_prop) (fun i => (i : ℝ) / 2) (fun a b hab => ?_) (by norm_num)
    (fun x hx h => ?_) (fun i _ => ?_) (fun i _ => ?_) (fun _ k => ?_) ?_ hj
  · have := Nat.factorial_pos (2 * k + 1)
    have := Real.pi_pos
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (by norm_num)))
      (pow_ne_zero _ (by positivity))) (by positivity)
  · have := ((hasDerivAt_id x).const_mul (2 * π)).sin
    simpa [mul_comm] using this
  · have : (a : ℝ) < b := by exact_mod_cast hab
    simp only; linarith
  · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
    have hx' : x = n / 2 := by have := Real.pi_pos; field_simp at hn ⊢; nlinarith
    have : (0 : ℝ) < n := by rw [hx'] at hx; linarith
    have : (0 : ℤ) < n := by exact_mod_cast this
    lift n to ℕ using this.le
    exact ⟨n, by omega, by rw [hx']; push_cast; ring⟩
  · show Real.sin (2 * π * ((i : ℝ) / 2)) = 0
    rw [Real.sin_eq_zero_iff]; exact ⟨i, by push_cast; ring⟩
  · have hs : Real.sin (2 * π * ((i : ℝ) / 2)) = 0 := by
      rw [Real.sin_eq_zero_iff]; exact ⟨i, by push_cast; ring⟩
    have := Real.pi_pos
    exact mul_ne_zero (by positivity) (cos_ne_zero_of_sin_eq_zero hs)
  · have := bernoulliFun_eval_half_eq_zero k
    rwa [bernoulliFun, ← one_div] at this
  · intro M ε hε
    filter_upwards [eventually_abs_sub_lt_of_tendstoUniformlyOn (fun K hK => tendstoUniformlyOn_bernoulli_odd hK) 1 _
        (fun x => Real.sin (2 * π * x)) hcplx (fun x => by push_cast; ring) M ε hε,
      eventually_abs_sub_lt_of_tendstoUniformlyOn (fun K hK => tendstoUniformlyOn_bernoulli_even hK)
        _ _ (fun x => (2 * π) * Real.cos (2 * π * x)) hcplx'
        (fun x => by push_cast; ring) M ε hε] with k h1 h2 x hx1 hxM
    exact ⟨h1 x hx1 hxM, h2 x hx1 hxM⟩

/-- `y_j^{(2k)} → j` as `k → ∞` (the zeros of `sin πx`). -/
lemma tendsto_eulerRealZero_two_mul {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun k => eulerRealZero (2 * k) j) atTop (𝓝 (j : ℝ)) := by
  have hcplx : ∀ (k : ℕ) (x : ℝ), ((((-1) ^ k * π ^ (2 * k + 1) / (4 * (2 * k)!) *
      ((Polynomial.euler (2 * k)).map (algebraMap ℚ ℝ)).eval x : ℝ)) : ℂ) =
      1 * ((-1 : ℂ) ^ k * (π : ℂ) ^ (2 * k + 1) / (4 * (2 * k)!) * eulerPolyE (2 * k) x) := by
    intro k x
    rw [eulerPolyE, ← ofReal_eval_map_eq_aeval]; push_cast; ring
  have hcplx' : ∀ (m : ℕ) (x : ℝ), ((((-1) ^ (m + 1) * π ^ (2 * (m + 1) + 1) /
      (4 * (2 * (m + 1))!) *
      ((Polynomial.euler (2 * (m + 1))).map (algebraMap ℚ ℝ)).derivative.eval x : ℝ)) : ℂ) =
      ((π : ℝ) : ℂ) * ((-1 : ℂ) ^ (m + 1) * (π : ℂ) ^ (2 * m + 2) / (4 * (2 * m + 1)!) *
        eulerPolyE (2 * m + 1) x) := by
    intro m x
    rw [derivative_map, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, derivative_euler_succ,
      eulerPolyE, ← ofReal_eval_map_eq_aeval, Nat.factorial_succ]
    simp only [Polynomial.map_mul, eval_mul, Polynomial.map_add, Polynomial.map_natCast,
      Polynomial.map_one, eval_add, eval_natCast, eval_one]
    have hf : ((2 * m + 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hm : (2 * (m : ℂ) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * m + 1)
    push_cast
    field_simp
    ring
  refine tendsto_realZerosGE_getD (fun k => (Polynomial.euler (2 * k)).map (algebraMap ℚ ℝ))
    (fun k => (-1) ^ k * π ^ (2 * k + 1) / (4 * (2 * k)!)) (fun k => ?_)
    (fun x => Real.sin (π * x)) (fun x => π * Real.cos (π * x)) (fun x => ?_)
    (by fun_prop) (fun i => (i : ℝ)) (fun a b hab => ?_) (by norm_num)
    (fun x hx h => ?_) (fun i _ => ?_) (fun i _ => ?_) (fun h => ?_) ?_ hj
  · have := Nat.factorial_pos (2 * k)
    have := Real.pi_pos
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by positivity))) (by positivity)
  · have := ((hasDerivAt_id x).const_mul π).sin
    simpa [mul_comm] using this
  · show (a : ℝ) < b; exact_mod_cast hab
  · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
    have hx' : x = n := by have := Real.pi_pos; nlinarith
    have : (0 : ℝ) < n := by rw [hx'] at hx; linarith
    have : (0 : ℤ) < n := by exact_mod_cast this
    lift n to ℕ using this.le
    exact ⟨n, by omega, by rw [hx']; push_cast; ring⟩
  · show Real.sin (π * (i : ℝ)) = 0
    rw [Real.sin_eq_zero_iff]; exact ⟨i, by push_cast; ring⟩
  · have hs : Real.sin (π * (i : ℝ)) = 0 := by
      rw [Real.sin_eq_zero_iff]; exact ⟨i, by push_cast; ring⟩
    have := Real.pi_pos
    exact mul_ne_zero (by positivity) (cos_ne_zero_of_sin_eq_zero hs)
  · norm_num at h
  · intro M ε hε
    filter_upwards [eventually_abs_sub_lt_of_tendstoUniformlyOn (fun K hK => tendstoUniformlyOn_euler_even hK) 1 _
        (fun x => Real.sin (π * x)) hcplx (fun x => by push_cast; ring) M ε hε,
      eventually_one_le_and_sub_one (eventually_abs_sub_lt_of_tendstoUniformlyOn (fun K hK => tendstoUniformlyOn_euler_odd hK)
        _ _ (fun x => π * Real.cos (π * x)) hcplx'
        (fun x => by push_cast; ring) M ε hε)] with k h1 h2 x hx1 hxM
    obtain ⟨hk1, h2⟩ := h2
    refine ⟨h1 x hx1 hxM, ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact h2 x hx1 hxM

/-- Corrected form of DLMF 24.12.11: `y_j^{(2k+1)} → j - 1/2` as `k → ∞` (the zeros of
`cos πx`); in particular `y_{2m}^{(n)} → 2m - 1/2` for odd `n`, not `m - 1/2` as printed. -/
lemma tendsto_eulerRealZero_two_mul_add_one {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun k => eulerRealZero (2 * k + 1) j) atTop (𝓝 ((j : ℝ) - 1 / 2)) := by
  have hcplx : ∀ (k : ℕ) (x : ℝ), ((((-1) ^ (k + 1) * π ^ (2 * k + 2) / (4 * (2 * k + 1)!) *
      ((Polynomial.euler (2 * k + 1)).map (algebraMap ℚ ℝ)).eval x : ℝ)) : ℂ) =
      1 * ((-1 : ℂ) ^ (k + 1) * (π : ℂ) ^ (2 * k + 2) / (4 * (2 * k + 1)!) *
        eulerPolyE (2 * k + 1) x) := by
    intro k x
    rw [eulerPolyE, ← ofReal_eval_map_eq_aeval]; push_cast; ring
  have hcplx' : ∀ (k : ℕ) (x : ℝ), ((((-1) ^ (k + 1) * π ^ (2 * k + 2) / (4 * (2 * k + 1)!) *
      ((Polynomial.euler (2 * k + 1)).map (algebraMap ℚ ℝ)).derivative.eval x : ℝ)) : ℂ) =
      ((-π : ℝ) : ℂ) * ((-1 : ℂ) ^ k * (π : ℂ) ^ (2 * k + 1) / (4 * (2 * k)!) *
        eulerPolyE (2 * k) x) := by
    intro k x
    rw [derivative_map, derivative_euler_succ, eulerPolyE, ← ofReal_eval_map_eq_aeval,
      Nat.factorial_succ]
    simp only [Polynomial.map_mul, eval_mul, Polynomial.map_add, Polynomial.map_natCast,
      Polynomial.map_one, eval_add, eval_natCast, eval_one]
    have hf : ((2 * k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hm : (2 * (k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * k)
    push_cast
    field_simp
    ring
  refine tendsto_realZerosGE_getD (fun k => (Polynomial.euler (2 * k + 1)).map (algebraMap ℚ ℝ))
    (fun k => (-1) ^ (k + 1) * π ^ (2 * k + 2) / (4 * (2 * k + 1)!)) (fun k => ?_)
    (fun x => Real.cos (π * x)) (fun x => -π * Real.sin (π * x)) (fun x => ?_)
    (by fun_prop) (fun i => (i : ℝ) - 1 / 2) (fun a b hab => ?_) (by norm_num)
    (fun x hx h => ?_) (fun i hi => ?_) (fun i hi => ?_) (fun _ k => ?_) ?_ hj
  · have := Nat.factorial_pos (2 * k + 1)
    have := Real.pi_pos
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by positivity))) (by positivity)
  · have := ((hasDerivAt_id x).const_mul π).cos
    simpa [mul_comm] using this
  · have : (a : ℝ) < b := by exact_mod_cast hab
    simp only; linarith
  · obtain ⟨l, hl⟩ := Real.cos_eq_zero_iff.mp h
    have hx' : x = l + 1 / 2 := by
      have := Real.pi_pos; field_simp at hl ⊢; nlinarith
    have : (-1 : ℝ) < l := by rw [hx'] at hx; linarith
    have : (0 : ℤ) ≤ l := by
      have : (-1 : ℤ) < l := by exact_mod_cast this
      omega
    lift l to ℕ using this
    exact ⟨l + 1, by omega, by rw [hx']; push_cast; ring⟩
  · have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
    show Real.cos (π * ((i : ℝ) - 1 / 2)) = 0
    rw [Real.cos_eq_zero_iff]
    obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by omega⟩
    exact ⟨l, by push_cast; ring⟩
  · have hc : Real.cos (π * ((i : ℝ) - 1 / 2)) = 0 := by
      rw [Real.cos_eq_zero_iff]
      obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by omega⟩
      exact ⟨l, by push_cast; ring⟩
    have hs := Real.sin_sq_add_cos_sq (π * ((i : ℝ) - 1 / 2))
    rw [hc] at hs
    have := Real.pi_pos
    intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · rw [h] at hs; norm_num at hs
  · exact eulerFun_two_mul_add_one_half k
  · intro M ε hε
    filter_upwards [eventually_abs_sub_lt_of_tendstoUniformlyOn (fun K hK => tendstoUniformlyOn_euler_odd hK) 1 _
        (fun x => Real.cos (π * x)) hcplx (fun x => by push_cast; ring) M ε hε,
      eventually_abs_sub_lt_of_tendstoUniformlyOn (fun K hK => tendstoUniformlyOn_euler_even hK)
        _ _ (fun x => -π * Real.sin (π * x)) hcplx'
        (fun x => by push_cast; ring) M ε hε] with k h1 h2 x hx1 hxM
    exact ⟨h1 x hx1 hxM, h2 x hx1 hxM⟩

/-- DLMF 24.12.4: for fixed `m ≥ 1`, `x_{2m-1}^{(n)} → m - 1/4` and `x_{2m}^{(n)} → m + 1/4` as
`n → ∞` through even values. -/
@[dlmf 24.12.E4]
theorem tendsto_bernoulliRealZero_even {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun k : ℕ => bernoulliRealZero (2 * k) (2 * m - 1)) atTop (𝓝 (m - 1 / 4)) ∧
      Tendsto (fun k : ℕ => bernoulliRealZero (2 * k) (2 * m)) atTop (𝓝 (m + 1 / 4)) := by
  refine ⟨?_, ?_⟩
  · convert tendsto_bernoulliRealZero_two_mul (j := 2 * m - 1) (by omega) using 2
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  · convert tendsto_bernoulliRealZero_two_mul (j := 2 * m) (by omega) using 2
    push_cast; ring

/-- DLMF §24.12(i): for odd `n`, `x_1^{(n)} = 1/2`. -/
@[dlmf 24.12.i]
theorem bernoulliRealZero_one_of_odd {n : ℕ} (hn : Odd n) : bernoulliRealZero n 1 = 1 / 2 := by
  obtain ⟨k, rfl⟩ := hn
  refine getD_zero_eq_of_sorted (bernoulliRealZerosGE_sorted _) ?_ fun y hy => ?_
  · rw [mem_bernoulliRealZerosGE, one_div, bernoulliFun_eval_half_eq_zero]; norm_num
  · exact (mem_bernoulliRealZerosGE.mp hy).1

/-- DLMF §24.12(i): for odd `n ≥ 3`, `x_2^{(n)} = 1`. -/
@[dlmf 24.12.i]
theorem bernoulliRealZero_two_of_odd {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) :
    bernoulliRealZero n 2 = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have hk : 1 ≤ k := by omega
  set P := (Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℝ) with hP
  have hP0 : P ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr (bernoulli_polynomial_ne_zero _)
  have hroot : P.IsRoot (1 / 2) := by
    show bernoulliFun _ _ = 0; rw [one_div]; exact bernoulliFun_eval_half_eq_zero _
  have hd : (derivative P).eval (1 / 2) ≠ 0 := by
    have : (derivative P).eval (1 / 2) = ((2 * k + 1 : ℕ) : ℝ) * bernoulliFun (2 * k) (1 / 2) := by
      simp [P, Polynomial.derivative_map, Polynomial.derivative_bernoulli, bernoulliFun]
    rw [this, one_div, bernoulliFun_eval_half]
    have hB := bernoulli_two_mul_ne_zero hk
    have h2 : (2 : ℝ) / 2 ^ (2 * k) - 1 ≠ 0 := by
      have : (4 : ℝ) ≤ 2 ^ (2 * k) := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (2 * k) := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [sub_ne_zero, ne_eq, div_eq_one_iff_eq (by positivity)]
      intro h; linarith
    exact mul_ne_zero (by positivity) (mul_ne_zero h2 (by exact_mod_cast hB))
  have hmult : P.rootMultiplicity (1 / 2) ≤ 1 := by
    by_contra h; push Not at h
    exact hd ((one_lt_rootMultiplicity_iff_isRoot hP0).mp h).2
  have hcount : (bernoulliRealZerosGE (2 * k + 1)).count (1 / 2) ≤ 1 := by
    rw [bernoulliRealZerosGE, realZerosGE, ← Multiset.coe_count, Multiset.sort_eq,
      Multiset.count_filter_of_pos (by norm_num), count_roots]
    exact hmult
  have hz1 : bernoulliFun (2 * k + 1) 1 = 0 := by
    rw [bernoulliFun_endpoints_eq_of_ne_one (by omega), bernoulliFun_eval_zero,
      bernoulli_eq_zero_of_odd (odd_two_mul_add_one _) (by omega)]; simp
  have hzeros : ∀ x ∈ Set.Ioo (1 / 2 : ℝ) 1, bernoulliFun (2 * k + 1) x ≠ 0 := by
    intro x hx h
    apply bernoulliFun_two_mul_add_one_ne_zero k (x := 1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rw [bernoulliFun_eval_one_sub, h, mul_zero]
  refine getD_one_eq_of_sorted (bernoulliRealZerosGE_sorted _) ?_ ?_ (by norm_num) hcount ?_ ?_
  · exact mem_bernoulliRealZerosGE.mpr
      ⟨le_rfl, by rw [one_div]; exact bernoulliFun_eval_half_eq_zero _⟩
  · exact mem_bernoulliRealZerosGE.mpr ⟨by norm_num, hz1⟩
  · intro y hy; exact (mem_bernoulliRealZerosGE.mp hy).1
  · intro y hy hne
    obtain ⟨hy1, hy0⟩ := mem_bernoulliRealZerosGE.mp hy
    by_contra hlt; push Not at hlt
    exact hzeros y ⟨lt_of_le_of_ne hy1 (Ne.symm hne), hlt⟩ hy0

/-- DLMF 24.12.5: for fixed `m ≥ 1`, `x_{2m-1}^{(n)} → m - 1/2` and `x_{2m}^{(n)} → m` as
`n → ∞` through odd values. -/
@[dlmf 24.12.E5]
theorem tendsto_bernoulliRealZero_odd {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun k : ℕ => bernoulliRealZero (2 * k + 1) (2 * m - 1)) atTop (𝓝 (m - 1 / 2)) ∧
      Tendsto (fun k : ℕ => bernoulliRealZero (2 * k + 1) (2 * m)) atTop (𝓝 m) := by
  refine ⟨?_, ?_⟩
  · convert tendsto_bernoulliRealZero_two_mul_add_one (j := 2 * m - 1) (by omega) using 2
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  · convert tendsto_bernoulliRealZero_two_mul_add_one (j := 2 * m) (by omega) using 2
    push_cast; ring

/-- DLMF §24.12(i): `R(n) = n` for `1 ≤ n ≤ 5`. -/
@[dlmf 24.12.i]
theorem bernoulliRealZeroCount_eq_self {n : ℕ} (h1 : 1 ≤ n) (h5 : n ≤ 5) :
    bernoulliRealZeroCount n = n := by
  have hdeg : ((Polynomial.bernoulli n).map (algebraMap ℚ ℝ)).natDegree ≤ n := by
    refine natDegree_map_le.trans (natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_)
    rw [coeff_bernoulli]
    have : ¬ N ≤ n := by exact_mod_cast not_le.mpr hN
    simp [this]
  have hp : (Polynomial.bernoulli n).map (algebraMap ℚ ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr (bernoulli_polynomial_ne_zero _)
  have hc : Continuous (bernoulliFun n) := continuous_bernoulliFun n
  have key : ∀ l : List ℝ, l.Pairwise (· < ·) → l.length = n → (∀ x ∈ l, bernoulliFun n x = 0) →
      bernoulliRealZeroCount n = n := fun l hl hlen hr =>
    card_roots_eq_of_strictly_sorted_zeros hdeg l hl hlen hr hp
  interval_cases n
  · refine key [1 / 2] (by simp) rfl ?_
    intro x hx; simp only [List.mem_singleton] at hx; subst hx
    simp [bernoulliFun, Polynomial.bernoulli_one]
  · obtain ⟨a, ha, ha0⟩ := exists_Ioo_eq_zero_of_mul_neg hc (show (0 : ℝ) < 1 / 2 by norm_num)
      (by rw [bernoulliFun_two_apply, bernoulliFun_two_apply]; norm_num)
    obtain ⟨b, hb, hb0⟩ := exists_Ioo_eq_zero_of_mul_neg hc (show (1 / 2 : ℝ) < 1 by norm_num)
      (by rw [bernoulliFun_two_apply, bernoulliFun_two_apply]; norm_num)
    refine key [a, b] (by simp; linarith [ha.2, hb.1]) rfl ?_
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption
  · refine key [0, 1 / 2, 1] (by simp; norm_num) rfl ?_
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> rw [bernoulliFun_three_apply] <;> norm_num
  · obtain ⟨a, ha, ha0⟩ := exists_Ioo_eq_zero_of_mul_neg hc (show (-1 : ℝ) < 0 by norm_num)
      (by rw [bernoulliFun_four_apply, bernoulliFun_four_apply]; norm_num)
    obtain ⟨b, hb, hb0⟩ := exists_Ioo_eq_zero_of_mul_neg hc (show (0 : ℝ) < 1 / 2 by norm_num)
      (by rw [bernoulliFun_four_apply, bernoulliFun_four_apply]; norm_num)
    obtain ⟨c, hc', hc0⟩ := exists_Ioo_eq_zero_of_mul_neg hc (show (1 / 2 : ℝ) < 1 by norm_num)
      (by rw [bernoulliFun_four_apply, bernoulliFun_four_apply]; norm_num)
    obtain ⟨d, hd, hd0⟩ := exists_Ioo_eq_zero_of_mul_neg hc (show (1 : ℝ) < 2 by norm_num)
      (by rw [bernoulliFun_four_apply, bernoulliFun_four_apply]; norm_num)
    refine key [a, b, c, d] ?_ rfl ?_
    · simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
        forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, forall_const, List.Pairwise.nil, and_true]
      constructorm* _ ∧ _ <;> linarith [ha.1, ha.2, hb.1, hb.2, hc'.1, hc'.2, hd.1, hd.2]
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
  · obtain ⟨a, ha, ha0⟩ := exists_Ioo_eq_zero_of_mul_neg hc (show (-1 : ℝ) < -1 / 10 by norm_num)
      (by rw [bernoulliFun_five_apply, bernoulliFun_five_apply]; norm_num)
    obtain ⟨d, hd, hd0⟩ := exists_Ioo_eq_zero_of_mul_neg hc (show (11 / 10 : ℝ) < 2 by norm_num)
      (by rw [bernoulliFun_five_apply, bernoulliFun_five_apply]; norm_num)
    refine key [a, 0, 1 / 2, 1, d] ?_ rfl ?_
    · simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
        forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, forall_const, List.Pairwise.nil, and_true]
      constructorm* _ ∧ _ <;> linarith [ha.1, ha.2, hd.1, hd.2]
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> first | assumption | (rw [bernoulliFun_five_apply]; norm_num)

/-- DLMF 24.12.6: `R(n) ∼ 2n/(πe)` as `n → ∞`. -/
@[dlmf 24.12.E6]
theorem bernoulliRealZeroCount_isEquivalent :
    (fun n : ℕ => (bernoulliRealZeroCount n : ℝ)) ~[atTop]
      fun n => 2 * n / (π * Real.exp 1) := by
  sorry

end DLMF.BernoulliEuler
end
