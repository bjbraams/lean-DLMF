/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.ZeroTools

/-!
# Zero counts of Ferrers functions of positive order

Tools for the zero counts of DLMF §14.16(ii) beyond `𝖯^{-m}_ν`
(`lzt_ferrersP_neg_order_zero_count`). A real solution `f` of the Ferrers equation on `(-1, 1)`
is compared with `u = 𝖯^{-μ}_ν(x)`, recessive at `1`, and `v = 𝖯^{-μ}_ν(-x)`, recessive at `-1`
(`μ ≥ 0`):

* Sturm separation with a nonzero constant Wronskian gives between `N` and `N + 1` zeros,
  `N = max(⌈ν - μ⌉, 0)` the number of zeros of `u` (`lzc_count_bounds`,
  `lzc_ferrers_count_bounds`); the zero after the last zero of `u` comes from the divergence
  of `f/u` at `1`;
* the signs of the Wronskians `c₁ = W{u, f}` and `c₂ = W{v, f}` (times `1-x²`) fix the signs of
  `f` near `±1` and hence the parity of the number of zeros: `-(c₁ c₂)(-1)^n > 0`
  (`lzc_parity`, `lzc_parity_ends`, `lzc_ferrers_parity`);
* the Wronskians `W{𝖯^{-μ}_ν(-x), 𝖯^μ_ν(x)} = 2 sin(νπ)/(π(1-x²))` and
  `W{𝖯^{-μ}_ν(-x), 𝖰^μ_ν(x)} = cos(νπ)/(1-x²)` (`lzc_wronskian_reflect_P`,
  `lzc_wronskian_reflect_Q`), companions of DLMF 14.2.6–14.2.7.

All helper names carry the prefix `lzc_`.
-/

@[expose] public noncomputable section

open Set Filter Topology

namespace DLMF.Legendre

/-- **Sturm separation.** If `p q' - q p'` has no zeros on `[a, b]` and `q a = q b = 0`, then `p`
vanishes somewhere in `(a, b)` (Rolle's theorem for `q / p`). -/
theorem lzc_exists_zero_between {p p' q q' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (p' x) x) (hq : ∀ x ∈ Icc a b, HasDerivAt q (q' x) x)
    (hw : ∀ x ∈ Icc a b, p x * q' x - q x * p' x ≠ 0) (ha : q a = 0) (hb : q b = 0) :
    ∃ c ∈ Ioo a b, p c = 0 := by
  by_contra hne
  push Not at hne
  have hpne : ∀ x ∈ Icc a b, p x ≠ 0 := by
    intro x hx h0
    rcases eq_or_lt_of_le hx.1 with h1 | h1
    · subst h1; exact hw _ hx (by rw [h0, ha]; ring)
    rcases eq_or_lt_of_le hx.2 with h2 | h2
    · subst h2; exact hw _ hx (by rw [h0, hb]; ring)
    exact hne x ⟨h1, h2⟩ h0
  have hD : ∀ x ∈ Icc a b, HasDerivAt (fun t => q t / p t)
      ((q' x * p x - q x * p' x) / p x ^ 2) x :=
    fun x hx => (hq x hx).div (hp x hx) (hpne x hx)
  obtain ⟨ξ, hξ, hξ0⟩ := exists_hasDerivAt_eq_zero hab
    (fun x hx => (hD x hx).continuousAt.continuousWithinAt) (by simp [ha, hb])
    (fun x hx => hD x (Ioo_subset_Icc_self hx))
  have hξI := Ioo_subset_Icc_self hξ
  rw [div_eq_zero_iff, or_iff_left (pow_ne_zero 2 (hpne ξ hξI))] at hξ0
  exact hw ξ hξI (by linarith)

/-- If any two points of `T` are separated by a point of the finite set `S`, then `T` is finite
with at most `|S| + 1` points. -/
theorem lzc_ncard_le_succ {S T : Set ℝ} (hS : S.Finite)
    (hsep : ∀ a ∈ T, ∀ b ∈ T, a < b → ∃ s ∈ S, a < s ∧ s < b) :
    T.Finite ∧ T.ncard ≤ S.ncard + 1 := by
  classical
  obtain ⟨w, hw⟩ := hS.infinite_compl.nonempty
  let f : ℝ → ℝ := fun t => if (S ∩ Ioi t).Nonempty then sInf (S ∩ Ioi t) else w
  have hfin : ∀ t, (S ∩ Ioi t).Finite := fun t => hS.subset inter_subset_left
  have hmem : ∀ t, (S ∩ Ioi t).Nonempty → f t ∈ S ∩ Ioi t := fun t h => by
    simp only [f, h, ↓reduceIte]; exact h.csInf_mem (hfin t)
  have hmaps : ∀ t ∈ T, f t ∈ insert w S := fun t _ => by
    by_cases h : (S ∩ Ioi t).Nonempty
    · exact mem_insert_of_mem _ (hmem t h).1
    · simp only [f, h, ↓reduceIte]; exact mem_insert _ _
  have key : ∀ a ∈ T, ∀ b ∈ T, a < b → f a ≠ f b := by
    intro a ha b hb hab heq
    obtain ⟨s, hs, has, hsb⟩ := hsep a ha b hb hab
    have hne : (S ∩ Ioi a).Nonempty := ⟨s, hs, has⟩
    have hfa : f a ≤ s := by
      simp only [f, hne, ↓reduceIte]
      exact csInf_le (hfin a).bddBelow ⟨hs, has⟩
    have hfaS := (hmem a hne).1
    by_cases hb' : (S ∩ Ioi b).Nonempty
    · have := (hmem b hb').2
      simp only [mem_Ioi] at this
      linarith
    · have : f b = w := by simp only [f, hb', ↓reduceIte]
      rw [heq, this] at hfaS
      exact hw hfaS
  have hinj : InjOn f T := by
    intro a ha b hb heq
    rcases lt_trichotomy a b with h | h | h
    · exact absurd heq (key a ha b hb h)
    · exact h
    · exact absurd heq.symm (key b hb a ha h)
  have hfinI : (insert w S).Finite := hS.insert w
  refine ⟨Finite.of_finite_image (hfinI.subset (by rintro _ ⟨t, ht, rfl⟩; exact hmaps t ht)) hinj,
    ?_⟩
  exact (ncard_le_ncard_of_injOn f hmaps hinj hfinI).trans (ncard_insert_le w S)

/-- If every point of `S` is followed by a point of the finite set `T` before the next point of
`S`, then `|S| ≤ |T|`. -/
theorem lzc_ncard_le {S T : Set ℝ} (hT : T.Finite)
    (h : ∀ s ∈ S, ∃ t ∈ T, s < t ∧ ∀ s' ∈ S, s < s' → t < s') : S.ncard ≤ T.ncard := by
  classical
  choose! g hgT hgs hgn using h
  refine ncard_le_ncard_of_injOn g hgT ?_ hT
  intro a ha b hb heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hab
  · have h1 := hgn a ha b hb hab
    have h2 := hgs b hb
    rw [heq] at h1; linarith
  · have h1 := hgn b hb a ha hab
    have h2 := hgs a ha
    rw [heq] at h2; linarith

/-- Just left of a zero with positive derivative, the function is negative. -/
theorem lzc_neg_left_of_deriv_pos {f : ℝ → ℝ} {d z : ℝ} (hd : HasDerivAt f d z) (h0 : f z = 0)
    (hpos : 0 < d) : ∃ t < z, ∀ x ∈ Ioo t z, f x < 0 := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsLT_le_nhdsNE z)
  have hev : ∀ᶠ x in 𝓝[<] z, 0 < slope f z x := hs.eventually (lt_mem_nhds hpos)
  have hev2 : ∀ᶠ x in 𝓝[<] z, f x < 0 := by
    filter_upwards [hev, self_mem_nhdsWithin] with x hx hxz
    rw [slope_def_field, h0, sub_zero] at hx
    have : x - z < 0 := sub_neg.mpr hxz
    by_contra hc; push Not at hc
    have : f x / (x - z) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hc this.le
    linarith
  obtain ⟨t, ht, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev2
  exact ⟨t, ht, fun x hx => hsub hx⟩

/-- **Parity of a zero count.** If `f` has finitely many zeros in `(a, b)`, all simple, `f > 0`
near `a` and `σ f > 0` near `b`, then `σ (-1)^n > 0`, `n` the number of zeros. -/
theorem lzc_parity {f f' : ℝ → ℝ} {a : ℝ} (n : ℕ) : ∀ (b σ : ℝ), a < b →
    (∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) → (∀ x ∈ Ioo a b, f x = 0 → f' x ≠ 0) →
    {x | x ∈ Ioo a b ∧ f x = 0}.Finite → {x | x ∈ Ioo a b ∧ f x = 0}.ncard = n →
    (∃ s, a < s ∧ ∀ x ∈ Ioo a s, 0 < f x) → (∃ t < b, ∀ x ∈ Ioo t b, 0 < σ * f x) →
    0 < σ * (-1) ^ n := by
  induction n with
  | zero =>
    intro b σ hab hd _ hfin hn ⟨s, hs, hsl⟩ ⟨t, ht, htr⟩
    have hemp := (ncard_eq_zero hfin).mp hn
    have hne : ∀ x ∈ Ioo a b, f x ≠ 0 := fun x hx h0 => by
      have : x ∈ {x | x ∈ Ioo a b ∧ f x = 0} := ⟨hx, h0⟩
      rw [hemp] at this; exact this
    have hc : ContinuousOn f (Ioo a b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
    have m1 := lt_min hs hab
    have m2 := min_le_left s b
    have m3 := min_le_right s b
    have m4 := max_lt ht hab
    have m5 := le_max_left t a
    have m6 := le_max_right t a
    have hx1 : (a + min s b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have hx1s : (a + min s b) / 2 ∈ Ioo a s := ⟨by linarith, by linarith⟩
    have hx2 : (max t a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have hx2t : (max t a + b) / 2 ∈ Ioo t b := ⟨by linarith, by linarith⟩
    rcases lzt_sign ordConnected_Ioo hc hne with hp | hn'
    · have h1 := htr _ hx2t
      have h2 := hp _ hx2
      have : 0 < σ := pos_of_mul_pos_left h1 h2.le
      simpa using this
    · exact absurd (hsl _ hx1s) (not_lt.mpr (hn' _ hx1).le)
  | succ n ih =>
    intro b σ hab hd hsimp hfin hn hl ⟨t, ht, htr⟩
    set Z := {x | x ∈ Ioo a b ∧ f x = 0} with hZ
    have hZne : Z.Nonempty := nonempty_of_ncard_ne_zero (by rw [hn]; omega)
    set z := sSup Z
    have hzZ : z ∈ Z := hZne.csSup_mem hfin
    have hle : ∀ x ∈ Z, x ≤ z := fun x hx => le_csSup hfin.bddAbove hx
    -- no zeros in (z, b)
    have hnz : ∀ x ∈ Ioo z b, f x ≠ 0 := fun x hx h0 => by
      have := hle x ⟨⟨hzZ.1.1.trans hx.1, hx.2⟩, h0⟩; linarith [hx.1]
    have hc : ContinuousOn f (Ioo z b) := fun x hx =>
      (hd x ⟨hzZ.1.1.trans hx.1, hx.2⟩).continuousAt.continuousWithinAt
    have m4 := max_lt ht hzZ.1.2
    have m5 := le_max_left t z
    have m6 := le_max_right t z
    set x2 := (max t z + b) / 2 with hx2d
    have hx2 : x2 ∈ Ioo z b := ⟨by linarith, by linarith⟩
    have hx2t : x2 ∈ Ioo t b := ⟨by linarith, by linarith⟩
    have hσf : ∀ x ∈ Ioo z b, 0 < σ * f x := by
      have h1 := htr x2 hx2t
      rcases lzt_sign ordConnected_Ioo hc hnz with hp | hm
      · have hσ : 0 < σ := pos_of_mul_pos_left h1 (hp x2 hx2).le
        exact fun x hx => mul_pos hσ (hp x hx)
      · have hσ : σ < 0 := by
          by_contra hσ; push Not at hσ
          have := mul_nonpos_of_nonneg_of_nonpos hσ (hm x2 hx2).le; linarith
        exact fun x hx => mul_pos_of_neg_of_neg hσ (hm x hx)
    have hdz := hd z hzZ.1
    have hd' : HasDerivAt (fun x => σ * f x) (σ * f' z) z := hdz.const_mul σ
    have h0 : σ * f z = 0 := by rw [hzZ.2, mul_zero]
    have hnn := lzt_deriv_nonneg_right hd' h0 hzZ.1.2 hσf
    have hσ0 : σ ≠ 0 := fun h => by have := hσf x2 hx2; rw [h, zero_mul] at this; linarith
    have hpos : 0 < σ * f' z := lt_of_le_of_ne hnn
      (Ne.symm (mul_ne_zero hσ0 (hsimp z hzZ.1 hzZ.2)))
    obtain ⟨t', ht', ht'l⟩ := lzc_neg_left_of_deriv_pos hd' h0 hpos
    have hsub : {x | x ∈ Ioo a z ∧ f x = 0} = Z \ {z} := by
      ext x
      simp only [hZ, mem_ofPred_eq, Set.mem_sdiff, mem_singleton_iff, mem_Ioo]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨⟨h1, h2.trans hzZ.1.2⟩, h3⟩, h2.ne⟩
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        exact ⟨⟨h1, lt_of_le_of_ne (hle x ⟨⟨h1, h2⟩, h3⟩) h4⟩, h3⟩
    have hfin' : {x | x ∈ Ioo a z ∧ f x = 0}.Finite := by rw [hsub]; exact hfin.sdiff
    have hn' : {x | x ∈ Ioo a z ∧ f x = 0}.ncard = n := by
      rw [hsub, ncard_sdiff_singleton_of_mem hzZ, hn]; rfl
    have := ih z (-σ) hzZ.1.1 (fun x hx => hd x ⟨hx.1, hx.2.trans hzZ.1.2⟩)
      (fun x hx => hsimp x ⟨hx.1, hx.2.trans hzZ.1.2⟩) hfin' hn' hl
      ⟨t', ht', fun x hx => by have := ht'l x hx; linarith⟩
    rw [pow_succ]; linarith

/-- If `u > 0`, `(1-x²)u² = O(1-x)` and `(1-x²)(u f' - f u') = c > 0` near `1`, then `f > 0`
near `1` (`f/u` increases to `+∞`). -/
theorem lzc_pos_near_one {f f' u u' : ℝ → ℝ} {s K c : ℝ} (hs : -1 < s) (hs1 : s < 1)
    (hK : 0 < K) (hc : 0 < c)
    (hfd : ∀ x ∈ Ico s 1, HasDerivAt f (f' x) x) (hud : ∀ x ∈ Ico s 1, HasDerivAt u (u' x) x)
    (hu : ∀ x ∈ Ico s 1, 0 < u x)
    (hb : ∀ x ∈ Ico s 1, (1 - x ^ 2) * u x ^ 2 ≤ K * (1 - x))
    (hW : ∀ x ∈ Ico s 1, (1 - x ^ 2) * (u x * f' x - f x * u' x) = c) :
    ∃ t ∈ Ioo s 1, ∀ x ∈ Ioo t 1, 0 < f x := by
  have hp : ∀ x ∈ Ico s 1, 0 < 1 - x ^ 2 := fun x hx => by nlinarith [hx.1, hx.2]
  obtain ⟨x0, hx0, h0⟩ := lzt_ratio_right hs1 hK hc hfd hud hu hp hb (fun x hx => by
    simp only [lzt_W]
    have e : (1 - x ^ 2) * (u' x * f x - u x * f' x) =
        -((1 - x ^ 2) * (u x * f' x - f x * u' x)) := by ring
    rw [e, hW x hx]) 0
  refine ⟨x0, hx0, fun x hx => ?_⟩
  have hmono : StrictMonoOn (fun t => f t / u t) (Ico s 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico s 1)
    · exact fun t ht => ((hfd t ht).div (hud t ht) (hu t ht).ne').continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      have htI : t ∈ Ico s 1 := Ioo_subset_Ico_self ht
      rw [((hfd t htI).fun_div (hud t htI) (hu t htI).ne').deriv]
      have key : 0 < u t * f' t - f t * u' t :=
        (mul_pos_iff_of_pos_left (hp t htI)).mp (by rw [hW t htI]; exact hc)
      exact div_pos (by linarith) (pow_pos (hu t htI) 2)
  have hxI : x ∈ Ico s 1 := ⟨hx0.1.le.trans hx.1.le, hx.2⟩
  have := hmono ⟨hx0.1.le, hx0.2⟩ hxI hx.1
  have h2 : 0 < f x / u x := lt_trans h0 this
  exact (div_pos_iff_of_pos_right (hu x hxI)).mp h2

/-- If `u > 0`, `(1-x²)u² = O(1+x)` and `(1-x²)(u f' - f u') = c > 0` near `-1`, then `f < 0`
near `-1`. -/
theorem lzc_neg_near_neg_one {f f' u u' : ℝ → ℝ} {s K c : ℝ} (hs : -1 < s) (hs1 : s < 1)
    (hK : 0 < K) (hc : 0 < c)
    (hfd : ∀ x ∈ Ioc (-1) s, HasDerivAt f (f' x) x) (hud : ∀ x ∈ Ioc (-1) s, HasDerivAt u (u' x) x)
    (hu : ∀ x ∈ Ioc (-1) s, 0 < u x)
    (hb : ∀ x ∈ Ioc (-1) s, (1 - x ^ 2) * u x ^ 2 ≤ K * (1 + x))
    (hW : ∀ x ∈ Ioc (-1) s, (1 - x ^ 2) * (u x * f' x - f x * u' x) = c) :
    ∃ t ∈ Ioo (-1) s, ∀ x ∈ Ioo (-1) t, f x < 0 := by
  have hp : ∀ x ∈ Ioc (-1) s, 0 < 1 - x ^ 2 := fun x hx => by nlinarith [hx.1, hx.2]
  obtain ⟨x0, hx0, h0⟩ := lzt_ratio_left hs hK hc hfd hud hu hp hb (fun x hx => by
    simp only [lzt_W]
    have e : (1 - x ^ 2) * (u' x * f x - u x * f' x) =
        -((1 - x ^ 2) * (u x * f' x - f x * u' x)) := by ring
    rw [e, hW x hx])
  refine ⟨x0, hx0, fun x hx => ?_⟩
  have hmono : StrictMonoOn (fun t => f t / u t) (Ioc (-1) s) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioc (-1) s)
    · exact fun t ht => ((hfd t ht).div (hud t ht) (hu t ht).ne').continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      have htI : t ∈ Ioc (-1) s := Ioo_subset_Ioc_self ht
      rw [((hfd t htI).fun_div (hud t htI) (hu t htI).ne').deriv]
      have key : 0 < u t * f' t - f t * u' t :=
        (mul_pos_iff_of_pos_left (hp t htI)).mp (by rw [hW t htI]; exact hc)
      exact div_pos (by linarith) (pow_pos (hu t htI) 2)
  have hxI : x ∈ Ioc (-1) s := ⟨hx.1, hx.2.le.trans hx0.2.le⟩
  have := hmono hxI ⟨hx0.1, hx0.2.le⟩ hx.2
  have h2 : f x / u x < 0 := lt_trans this h0
  have h3 := mul_neg_of_neg_of_pos h2 (hu x hxI)
  rwa [div_mul_cancel₀ _ (hu x hxI).ne'] at h3

/-- A solution has a zero between the last zero `s₀` of the recessive solution `u` and `1`
(normalized signs). -/
lemma lzc_zero_right_aux {u u' y y' : ℝ → ℝ} {c K s s0 : ℝ}
    (hud : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt u (u' x) x) (hyd : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt y (y' x) x)
    (hc : 0 < c) (hW : ∀ x ∈ Ioo (-1:ℝ) 1, (1 - x ^ 2) * (u x * y' x - y x * u' x) = c)
    (hs0 : s0 ∈ Ioo (-1:ℝ) 1) (hu0 : u s0 = 0) (hpos : ∀ x ∈ Ioo s0 1, 0 < u x)
    (hs : s ∈ Ioo (-1:ℝ) 1) (hK : 0 < K)
    (hb : ∀ x ∈ Ico s 1, (1 - x ^ 2) * u x ^ 2 ≤ K * (1 - x)) :
    ∃ t ∈ Ioo s0 1, y t = 0 := by
  set s1 := max s ((s0 + 1) / 2) with hs1
  have a1 := le_max_left s ((s0 + 1) / 2)
  have a2 := le_max_right s ((s0 + 1) / 2)
  have a3 : s1 < 1 := max_lt hs.2 (by linarith [hs0.2])
  have hsub : Ico s1 1 ⊆ Ioo (-1:ℝ) 1 := fun x hx => ⟨by linarith [hx.1, hs.1], hx.2⟩
  have hsub' : Ico s1 1 ⊆ Ioo s0 1 := fun x hx => ⟨by linarith [hx.1, hs0.2], hx.2⟩
  obtain ⟨t, ht, htp⟩ := lzc_pos_near_one (f := y) (u := u) (by linarith [hs.1]) a3 hK hc
    (fun x hx => hyd x (hsub hx)) (fun x hx => hud x (hsub hx)) (fun x hx => hpos x (hsub' hx))
    (fun x hx => hb x ⟨by linarith [hx.1], hx.2⟩) (fun x hx => hW x (hsub hx))
  have hsub2 : Ico s0 1 ⊆ Ioo (-1:ℝ) 1 := fun x hx => ⟨by linarith [hx.1, hs0.1], hx.2⟩
  set y0 := (t + 1) / 2
  have hy0 : y0 ∈ Ioo t 1 := ⟨by simp only [y0]; linarith [ht.2], by simp only [y0]; linarith [ht.2]⟩
  have hy0' : y0 ∈ Ioo s0 1 := ⟨by linarith [ht.1, hy0.1], hy0.2⟩
  obtain ⟨e, he, -⟩ := ODE.sturmCount_existsUnique_zero_right (p := u) (q := y)
    (fun x hx => hud x (hsub2 hx)) (fun x hx => hyd x (hsub2 hx))
    (fun x hx => (mul_pos_iff_of_pos_left (show 0 < 1 - x ^ 2 by
      nlinarith [(hsub2 hx).1, (hsub2 hx).2])).mp (by rw [hW x (hsub2 hx)]; exact hc)) hu0
    (fun x hx => (hpos x hx).ne') ⟨y0, hy0', div_pos (htp y0 hy0) (hpos y0 hy0')⟩
  exact ⟨e, he.1, he.2⟩

/-- A solution independent of `u` has a zero between the last zero `s₀` of `u` and `1`, when `u`
is recessive at `1`. -/
theorem lzc_zero_right {u u' y y' : ℝ → ℝ} {c K s s0 : ℝ}
    (hud : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt u (u' x) x) (hyd : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt y (y' x) x)
    (hc : c ≠ 0) (hW : ∀ x ∈ Ioo (-1:ℝ) 1, (1 - x ^ 2) * (u x * y' x - y x * u' x) = c)
    (hs0 : s0 ∈ Ioo (-1:ℝ) 1) (hu0 : u s0 = 0) (hne : ∀ x ∈ Ioo s0 1, u x ≠ 0)
    (hs : s ∈ Ioo (-1:ℝ) 1) (hK : 0 < K)
    (hb : ∀ x ∈ Ico s 1, (1 - x ^ 2) * u x ^ 2 ≤ K * (1 - x)) :
    ∃ t ∈ Ioo s0 1, y t = 0 := by
  have hsub : Ioo s0 1 ⊆ Ioo (-1:ℝ) 1 := fun x hx => ⟨hs0.1.trans hx.1, hx.2⟩
  have hcont : ContinuousOn u (Ioo s0 1) := fun x hx =>
    (hud x (hsub hx)).continuousAt.continuousWithinAt
  -- normalize the sign of `y`
  have hy : ∀ {U U' : ℝ → ℝ} {C : ℝ}, (∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt U (U' x) x) → C ≠ 0 →
      (∀ x ∈ Ioo (-1:ℝ) 1, (1 - x ^ 2) * (U x * y' x - y x * U' x) = C) → U s0 = 0 →
      (∀ x ∈ Ioo s0 1, 0 < U x) → (∀ x ∈ Ico s 1, (1 - x ^ 2) * U x ^ 2 ≤ K * (1 - x)) →
      ∃ t ∈ Ioo s0 1, y t = 0 := by
    intro U U' C hU hC hWU hU0 hUp hbU
    rcases lt_or_gt_of_ne hC with hn | hp
    · obtain ⟨t, ht, h0⟩ := lzc_zero_right_aux (y := fun x => -y x) (y' := fun x => -y' x)
        (c := -C) hU (fun x hx => (hyd x hx).neg) (by linarith)
        (fun x hx => by have := hWU x hx; linarith [this]) hs0 hU0 hUp hs hK hbU
      exact ⟨t, ht, neg_eq_zero.mp h0⟩
    · exact lzc_zero_right_aux hU hyd hp hWU hs0 hU0 hUp hs hK hbU
  rcases lzt_sign ordConnected_Ioo hcont hne with hp | hn
  · exact hy hud hc hW hu0 hp hb
  · refine hy (U := fun x => -u x) (U' := fun x => -u' x) (C := -c) (fun x hx => (hud x hx).neg)
      (neg_ne_zero.mpr hc) (fun x hx => by have := hW x hx; linarith [this]) (by simp [hu0])
      (fun x hx => neg_pos.mpr (hn x hx)) (fun x hx => by have := hb x hx; simpa using this)

/-- **Zero count of an independent solution.** If `u` is recessive at `1`, has exactly `N`
zeros in `(-1, 1)`, and `(1-x²)(u y' - y u') = c ≠ 0`, then `y` has between `N` and `N + 1`
zeros there. -/
theorem lzc_count_bounds {u u' y y' : ℝ → ℝ} {c K s : ℝ} {N : ℕ}
    (hud : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt u (u' x) x) (hyd : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt y (y' x) x)
    (hc : c ≠ 0) (hW : ∀ x ∈ Ioo (-1:ℝ) 1, (1 - x ^ 2) * (u x * y' x - y x * u' x) = c)
    (huf : {x | x ∈ Ioo (-1:ℝ) 1 ∧ u x = 0}.Finite)
    (hun : {x | x ∈ Ioo (-1:ℝ) 1 ∧ u x = 0}.ncard = N)
    (hs : s ∈ Ioo (-1:ℝ) 1) (hK : 0 < K)
    (hb : ∀ x ∈ Ico s 1, (1 - x ^ 2) * u x ^ 2 ≤ K * (1 - x)) :
    {x | x ∈ Ioo (-1:ℝ) 1 ∧ y x = 0}.Finite ∧ N ≤ {x | x ∈ Ioo (-1:ℝ) 1 ∧ y x = 0}.ncard ∧
      {x | x ∈ Ioo (-1:ℝ) 1 ∧ y x = 0}.ncard ≤ N + 1 := by
  set Zu := {x | x ∈ Ioo (-1:ℝ) 1 ∧ u x = 0} with hZu
  set Zy := {x | x ∈ Ioo (-1:ℝ) 1 ∧ y x = 0} with hZy
  have hw : ∀ x ∈ Ioo (-1:ℝ) 1, u x * y' x - y x * u' x ≠ 0 := fun x hx h0 => by
    have := hW x hx; rw [h0, mul_zero] at this; exact hc this.symm
  have hsubI : ∀ {a b : ℝ}, a ∈ Ioo (-1:ℝ) 1 → b ∈ Ioo (-1:ℝ) 1 → Icc a b ⊆ Ioo (-1:ℝ) 1 :=
    fun ha hb => Icc_subset_Ioo ha.1 hb.2
  obtain ⟨hyfin, hup⟩ := lzc_ncard_le_succ huf (S := Zu) (T := Zy) fun a ha b hb hab => by
    obtain ⟨e, he, he0⟩ := lzc_exists_zero_between (p := u) (q := y) hab
      (fun x hx => hud x (hsubI ha.1 hb.1 hx)) (fun x hx => hyd x (hsubI ha.1 hb.1 hx))
      (fun x hx => hw x (hsubI ha.1 hb.1 hx)) ha.2 hb.2
    exact ⟨e, ⟨hsubI ha.1 hb.1 (Ioo_subset_Icc_self he), he0⟩, he.1, he.2⟩
  refine ⟨hyfin, ?_, by rw [← hun]; exact hup⟩
  rw [← hun]
  refine lzc_ncard_le hyfin fun s0 hs0 => ?_
  by_cases hnext : (Zu ∩ Ioi s0).Nonempty
  · have hfin : (Zu ∩ Ioi s0).Finite := huf.subset inter_subset_left
    set n := sInf (Zu ∩ Ioi s0)
    have hn := hnext.csInf_mem hfin
    have hn' : ∀ s' ∈ Zu, s0 < s' → n ≤ s' := fun s' hs' h => csInf_le hfin.bddBelow ⟨hs', h⟩
    obtain ⟨e, he, he0⟩ := lzc_exists_zero_between (p := y) (q := u) (a := s0) (b := n) hn.2
      (fun x hx => hyd x (hsubI hs0.1 hn.1.1 hx)) (fun x hx => hud x (hsubI hs0.1 hn.1.1 hx))
      (fun x hx h0 => hw x (hsubI hs0.1 hn.1.1 hx) (by linarith)) hs0.2 hn.1.2
    exact ⟨e, ⟨hsubI hs0.1 hn.1.1 (Ioo_subset_Icc_self he), he0⟩, he.1,
      fun s' hs' h => he.2.trans_le (hn' s' hs' h)⟩
  · have hne : ∀ x ∈ Ioo s0 1, u x ≠ 0 := fun x hx h0 =>
      hnext ⟨x, ⟨⟨hs0.1.1.trans hx.1, hx.2⟩, h0⟩, hx.1⟩
    obtain ⟨t, ht, h0⟩ := lzc_zero_right hud hyd hc hW hs0.1 hs0.2 hne hs hK hb
    exact ⟨t, ⟨⟨hs0.1.1.trans ht.1, ht.2⟩, h0⟩, ht.1,
      fun s' hs' h => absurd ⟨s', hs', h⟩ hnext⟩

/-- **Parity from the ends.** If `u > 0` is recessive at `1`, `v > 0` is recessive at `-1`, and
`f` has finitely many simple zeros with Wronskians `c₁ ≠ 0` against `u` and `c₂ ≠ 0` against
`v`, then `-(c₁ c₂)(-1)^n > 0`, `n` the number of zeros. -/
theorem lzc_parity_ends {f f' u u' v v' : ℝ → ℝ} {c₁ c₂ K s s' : ℝ}
    (hfd : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt f (f' x) x)
    (hsimp : ∀ x ∈ Ioo (-1:ℝ) 1, f x = 0 → f' x ≠ 0)
    (hfin : {x | x ∈ Ioo (-1:ℝ) 1 ∧ f x = 0}.Finite)
    (hs : s ∈ Ioo (-1:ℝ) 1) (hs' : s' ∈ Ioo (-1:ℝ) 1) (hK : 0 < K)
    (hud : ∀ x ∈ Ico s 1, HasDerivAt u (u' x) x) (hu : ∀ x ∈ Ico s 1, 0 < u x)
    (hbu : ∀ x ∈ Ico s 1, (1 - x ^ 2) * u x ^ 2 ≤ K * (1 - x))
    (hvd : ∀ x ∈ Ioc (-1) s', HasDerivAt v (v' x) x) (hv : ∀ x ∈ Ioc (-1) s', 0 < v x)
    (hbv : ∀ x ∈ Ioc (-1) s', (1 - x ^ 2) * v x ^ 2 ≤ K * (1 + x))
    (hc₁ : c₁ ≠ 0) (hW₁ : ∀ x ∈ Ico s 1, (1 - x ^ 2) * (u x * f' x - f x * u' x) = c₁)
    (hc₂ : c₂ ≠ 0) (hW₂ : ∀ x ∈ Ioc (-1) s', (1 - x ^ 2) * (v x * f' x - f x * v' x) = c₂) :
    0 < -(c₁ * c₂) * (-1) ^ {x | x ∈ Ioo (-1:ℝ) 1 ∧ f x = 0}.ncard := by
  have hsI : Ico s 1 ⊆ Ioo (-1:ℝ) 1 := fun x hx => ⟨hs.1.trans_le hx.1, hx.2⟩
  have hsI' : Ioc (-1) s' ⊆ Ioo (-1:ℝ) 1 := fun x hx => ⟨hx.1, hx.2.trans_lt hs'.2⟩
  -- the sign near `1`: `c₁ f > 0`
  have hright : ∃ t < 1, ∀ x ∈ Ioo t 1, 0 < c₁ * f x := by
    rcases lt_or_gt_of_ne hc₁ with hn | hp
    · obtain ⟨t, ht, h⟩ := lzc_pos_near_one (f := fun x => -f x) (f' := fun x => -f' x)
        (c := -c₁) hs.1 hs.2 hK (by linarith) (fun x hx => (hfd x (hsI hx)).neg) hud hu hbu
        (fun x hx => by have := hW₁ x hx; linarith [this])
      exact ⟨t, ht.2, fun x hx => by have := h x hx; nlinarith⟩
    · obtain ⟨t, ht, h⟩ := lzc_pos_near_one (f := f) (c := c₁) hs.1 hs.2 hK hp
        (fun x hx => hfd x (hsI hx)) hud hu hbu hW₁
      exact ⟨t, ht.2, fun x hx => mul_pos hp (h x hx)⟩
  -- the sign near `-1`: `c₂ f < 0`
  have hleft : ∃ t, -1 < t ∧ ∀ x ∈ Ioo (-1) t, 0 < -c₂ * f x := by
    rcases lt_or_gt_of_ne hc₂ with hn | hp
    · obtain ⟨t, ht, h⟩ := lzc_neg_near_neg_one (f := fun x => -f x) (f' := fun x => -f' x)
        (c := -c₂) hs'.1 hs'.2 hK (by linarith) (fun x hx => (hfd x (hsI' hx)).neg) hvd hv hbv
        (fun x hx => by have := hW₂ x hx; linarith [this])
      exact ⟨t, ht.1, fun x hx => by have := h x hx; nlinarith⟩
    · obtain ⟨t, ht, h⟩ := lzc_neg_near_neg_one (f := f) (c := c₂) hs'.1 hs'.2 hK hp
        (fun x hx => hfd x (hsI' hx)) hvd hv hbv hW₂
      exact ⟨t, ht.1, fun x hx => by have := h x hx; nlinarith⟩
  obtain ⟨t₁, ht₁, h₁⟩ := hright
  obtain ⟨t₂, ht₂, h₂⟩ := hleft
  -- apply the parity lemma to `g = -c₂ f`
  have hc₂' : -c₂ ≠ 0 := neg_ne_zero.mpr hc₂
  have hset : {x | x ∈ Ioo (-1:ℝ) 1 ∧ f x = 0} = {x | x ∈ Ioo (-1:ℝ) 1 ∧ -c₂ * f x = 0} := by
    ext x; simp [hc₂]
  have := lzc_parity (f := fun x => -c₂ * f x) (f' := fun x => -c₂ * f' x) (a := -1)
    {x | x ∈ Ioo (-1:ℝ) 1 ∧ f x = 0}.ncard 1 (c₁ / -c₂) (by norm_num)
    (fun x hx => (hfd x hx).const_mul _)
    (fun x hx h0 => mul_ne_zero hc₂' (hsimp x hx ((mul_eq_zero.mp h0).resolve_left hc₂')))
    (by rw [← hset]; exact hfin) (by rw [← hset]) ⟨t₂, ht₂, h₂⟩
    ⟨t₁, ht₁, fun x hx => by
      have := h₁ x hx
      rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hc₂']; exact this⟩
  have hsq : 0 < c₂ ^ 2 := by positivity
  have e : -(c₁ * c₂) = c₁ / -c₂ * c₂ ^ 2 := by field_simp
  rw [e, mul_assoc, mul_comm (c₂ ^ 2), ← mul_assoc]
  exact mul_pos this hsq

/-- Near `1`, `𝖯^{-μ}_ν` (`μ ≥ 0`) has no zeros and `(1-x²)(𝖯^{-μ}_ν)² = O(1-x)`. -/
theorem lzc_near_one (ν : ℝ) {μ : ℝ} (hμ : 0 ≤ μ) :
    ∃ s ∈ Ioo (-1:ℝ) 1, ∃ K > 0, ∀ x ∈ Ico s 1, (ferrersP ν (-μ : ℝ) x).re ≠ 0 ∧
      (1 - x ^ 2) * (ferrersP ν (-μ : ℝ) x).re ^ 2 ≤ K * (1 - x) := by
  obtain ⟨s₀, hs₀, M, hM⟩ := lzt_ferrersP_near_one ν hμ
  have a1 := le_max_left s₀ 0
  have a2 := le_max_right s₀ 0
  have a3 : max s₀ 0 < 1 := max_lt hs₀ one_pos
  refine ⟨(max s₀ 0 + 1) / 2, ⟨by linarith, by linarith⟩, 2 * M ^ 2 + 1, by positivity,
    fun x hx => ?_⟩
  have hx0 : x ∈ Ioo s₀ 1 := ⟨by linarith [hx.1], hx.2⟩
  have hxp : 0 ≤ x := by linarith [hx.1]
  obtain ⟨hne, hle⟩ := hM x hx0
  refine ⟨hne, ?_⟩
  have hp : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.2]
  have hr0 : 0 ≤ (1 - x ^ 2) ^ (μ / 2) := Real.rpow_nonneg hp _
  have hr1 : (1 - x ^ 2) ^ (μ / 2) ≤ 1 := Real.rpow_le_one hp (by nlinarith) (by linarith)
  have hsq : (ferrersP ν (-μ : ℝ) x).re ^ 2 ≤ M ^ 2 := by
    have h1 : |(ferrersP ν (-μ : ℝ) x).re| ≤ |M| := by
      refine hle.trans ?_
      calc M * (1 - x ^ 2) ^ (μ / 2) ≤ |M| * (1 - x ^ 2) ^ (μ / 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self M) hr0
        _ ≤ |M| * 1 := mul_le_mul_of_nonneg_left hr1 (abs_nonneg M)
        _ = |M| := mul_one _
    rw [← sq_abs, ← sq_abs M]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e1 : 1 - x ^ 2 ≤ 2 * (1 - x) := by nlinarith [hx.2]
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  calc (1 - x ^ 2) * (ferrersP ν (-μ : ℝ) x).re ^ 2 ≤ (1 - x ^ 2) * M ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hp
    _ ≤ 2 * (1 - x) * M ^ 2 := mul_le_mul_of_nonneg_right e1 hM2
    _ ≤ (2 * M ^ 2 + 1) * (1 - x) := by nlinarith [hx.2]

/-- A real solution `f` of the Ferrers equation with nonzero Wronskian against `𝖯^{-μ}_ν`
(`μ ≥ 0`, `ν ≥ -1/2`) has between `N` and `N + 1` zeros, `N = max(⌈ν - μ⌉, 0)`. -/
theorem lzc_ferrers_count_bounds {ν μ : ℝ} (hμ : 0 ≤ μ) (hν : -1/2 ≤ ν) {f f' : ℝ → ℝ}
    (hfd : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt f (f' x) x) {c : ℝ} (hc : c ≠ 0)
    (hW : ∀ x ∈ Ioo (-1:ℝ) 1, (1 - x ^ 2) * ((ferrersP ν (-μ:ℝ) x).re * f' x -
      f x * (deriv (ferrersP ν (-μ:ℝ)) x).re) = c) :
    {x | x ∈ Ioo (-1:ℝ) 1 ∧ f x = 0}.Finite ∧
      (max ⌈ν - μ⌉ 0).toNat ≤ {x | x ∈ Ioo (-1:ℝ) 1 ∧ f x = 0}.ncard ∧
      {x | x ∈ Ioo (-1:ℝ) 1 ∧ f x = 0}.ncard ≤ (max ⌈ν - μ⌉ 0).toNat + 1 := by
  obtain ⟨s, hs, K, hK, hnear⟩ := lzc_near_one ν hμ
  obtain ⟨hfin, hcard⟩ := lzt_ferrersP_neg_order_zero_count hμ hν
  exact lzc_count_bounds (fun x hx => (lzt_ferrersP_sol ν (-μ) hx).1) hfd hc hW hfin hcard hs hK
    (fun x hx => (hnear x hx).2)

/-- **Parity from the end Wronskians.** For a real solution `f` with simple zeros and constant
Wronskians `c₁` against `𝖯^{-μ}_ν(x)` and `c₂` against `𝖯^{-μ}_ν(-x)` (`μ ≥ 0`), the number
`n` of zeros satisfies `-(c₁ c₂)(-1)^n > 0`. -/
theorem lzc_ferrers_parity {ν μ : ℝ} (hμ : 0 ≤ μ) {f f' : ℝ → ℝ}
    (hfd : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt f (f' x) x)
    (hsimp : ∀ x ∈ Ioo (-1:ℝ) 1, f x = 0 → f' x ≠ 0)
    (hfin : {x | x ∈ Ioo (-1:ℝ) 1 ∧ f x = 0}.Finite) {c₁ c₂ : ℝ} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hW₁ : ∀ x ∈ Ioo (-1:ℝ) 1, (1 - x ^ 2) * ((ferrersP ν (-μ:ℝ) x).re * f' x -
      f x * (deriv (ferrersP ν (-μ:ℝ)) x).re) = c₁)
    (hW₂ : ∀ x ∈ Ioo (-1:ℝ) 1, (1 - x ^ 2) * ((ferrersP ν (-μ:ℝ) (-x)).re * f' x -
      f x * -(deriv (ferrersP ν (-μ:ℝ)) (-x)).re) = c₂) :
    0 < -(c₁ * c₂) * (-1) ^ {x | x ∈ Ioo (-1:ℝ) 1 ∧ f x = 0}.ncard := by
  obtain ⟨s, hs, K, hK, hnear⟩ := lzc_near_one ν hμ
  set u : ℝ → ℝ := fun x => (ferrersP ν (-μ:ℝ) x).re with hu
  set u' : ℝ → ℝ := fun x => (deriv (ferrersP ν (-μ:ℝ)) x).re with hu'
  have hsI : Ico s 1 ⊆ Ioo (-1:ℝ) 1 := fun x hx => ⟨hs.1.trans_le hx.1, hx.2⟩
  have hs' : -s ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hsI' : Ioc (-1) (-s) ⊆ Ioo (-1:ℝ) 1 := fun x hx => ⟨hx.1, hx.2.trans_lt hs'.2⟩
  have hIoc : ∀ x ∈ Ioc (-1) (-s), -x ∈ Ico s 1 := fun x hx =>
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hud : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt u (u' x) x := fun x hx =>
    (lzt_ferrersP_sol ν (-μ) hx).1
  have hvd : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt (fun t => u (-t)) (-u' (-x)) x := fun x hx => by
    have hx' : -x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have := (hud (-x) hx').comp x (hasDerivAt_neg x)
    simpa [Function.comp_def] using this
  have hbv : ∀ x ∈ Ioc (-1) (-s), (1 - x ^ 2) * u (-x) ^ 2 ≤ K * (1 + x) := fun x hx => by
    have := (hnear _ (hIoc x hx)).2
    rwa [neg_sq, sub_neg_eq_add] at this
  have hcont : ContinuousOn u (Ico s 1) := fun x hx =>
    (hud x (hsI hx)).continuousAt.continuousWithinAt
  rcases lzt_sign ordConnected_Ico hcont (fun x hx => (hnear x hx).1) with hp | hn
  · exact lzc_parity_ends (u := u) (u' := u') (v := fun t => u (-t)) (v' := fun t => -u' (-t))
      hfd hsimp hfin hs hs' hK (fun x hx => hud x (hsI hx)) hp (fun x hx => (hnear x hx).2)
      (fun x hx => hvd x (hsI' hx)) (fun x hx => hp _ (hIoc x hx)) hbv
      hc₁ (fun x hx => hW₁ x (hsI hx)) hc₂ (fun x hx => hW₂ x (hsI' hx))
  · have := lzc_parity_ends (u := fun t => -u t) (u' := fun t => -u' t)
      (v := fun t => -u (-t)) (v' := fun t => u' (-t)) (c₁ := -c₁) (c₂ := -c₂)
      hfd hsimp hfin hs hs' hK (fun x hx => (hud x (hsI hx)).neg)
      (fun x hx => neg_pos.mpr (hn x hx)) (fun x hx => by rw [neg_sq]; exact (hnear x hx).2)
      (fun x hx => by have := (hvd x (hsI' hx)).neg; rwa [neg_neg] at this)
      (fun x hx => neg_pos.mpr (hn _ (hIoc x hx))) (fun x hx => by rw [neg_sq]; exact hbv x hx)
      (neg_ne_zero.mpr hc₁) (fun x hx => by have := hW₁ x (hsI hx); linarith [this])
      (neg_ne_zero.mpr hc₂) (fun x hx => by have := hW₂ x (hsI' hx); linarith [this])
    simpa using this

section Wronskians

open Complex
open scoped Real

/-- The Wronskian of `𝖯^{-μ}_ν(-x)` and `𝖯^μ_ν(x)` is `2 sin(νπ)/(π(1-x²))` (from the even and odd
solutions, as in DLMF 14.2.7). -/
theorem lzc_wronskian_reflect_P (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ODE.wronskian (fun x => ferrersP ν (-μ) (-x)) (ferrersP ν μ) x =
      2*sin (ν*π)/(π*(1-x^2:ℂ)) := by
  rw [ferrersWronskian_of_even_odd (ferrersP_neg_reflect_eqOn_even_odd ν μ)
    (ferrersP_eqOn_even_odd ν μ) hx,
    show 2*sin (ν*π)/(π*(1-x^2:ℂ)) = sin (ν*π)*(2/(π*(1-x^2:ℂ))) by ring]
  congr 1
  obtain ⟨e1, o1, e2, o2⟩ := legendre_reflections ν μ
  have kT : (2:ℂ)^μ*((2:ℂ)^μ)⁻¹ = 1 := mul_inv_cancel₀ (by simp)
  rw [cpow_neg, show ν*π = (ν+μ)*π/2 + (ν-μ)*π/2 by ring, sin_add]
  generalize (Gamma ((1-ν-μ)/2))⁻¹ = A1 at e1
  generalize (Gamma (-(ν+μ)/2))⁻¹ = B1 at o1
  generalize (Gamma ((1-ν+μ)/2))⁻¹ = A2 at e2
  generalize (Gamma ((μ-ν)/2))⁻¹ = B2 at o2
  generalize (Gamma ((ν-μ+1)/2))⁻¹ = r1 at e2
  generalize (Gamma ((ν-μ+2)/2))⁻¹ = r2 at o2
  generalize (Gamma ((ν+μ+1)/2))⁻¹ = R1 at e1
  generalize (Gamma ((ν+μ+2)/2))⁻¹ = R2 at o1
  generalize ((2:ℂ)^μ)⁻¹ = Ti at kT
  generalize (2:ℂ)^μ = T at kT
  generalize sin ((ν+μ)*π/2) = sb at o1
  generalize cos ((ν+μ)*π/2) = cb at e1
  generalize sin ((ν-μ)*π/2) = sa at o2
  generalize cos ((ν-μ)*π/2) = ca at e2
  generalize (π:ℂ) = P at e1 o1 e2 o2
  linear_combination (sb*ca+cb*sa)*kT + T*Ti*(-(P*A2*r1)*o1 + sb*e2 - (P*B2*r2)*e1 - cb*o2)

/-- The Wronskian of `𝖯^{-μ}_ν(-x)` and `𝖰^μ_ν(x)` is `cos(νπ)/(1-x²)` (compare DLMF 14.2.6). -/
theorem lzc_wronskian_reflect_Q (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ}
    (hx : x ∈ Ioo (-1:ℝ) 1) :
    ODE.wronskian (fun x => ferrersP ν (-μ) (-x)) (ferrersQ ν μ) x = cos (ν*π)/(1-x^2:ℂ) := by
  have hne : 1-(x:ℂ)^2≠0 := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersWronskian_of_even_odd (ferrersP_neg_reflect_eqOn_even_odd ν μ)
    (ferrersQ_eqOn_even_odd ν μ) hx,
    show cos (ν*π)/(1-x^2:ℂ) = (π/2*cos (ν*π))*(2/(π*(1-x^2:ℂ))) by field_simp]
  congr 1
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero h
  obtain ⟨-, -, e2, o2⟩ := legendre_reflections ν μ
  have kT : (2:ℂ)^μ*((2:ℂ)^μ)⁻¹ = 1 := mul_inv_cancel₀ (by simp)
  have k1 : Gamma ((ν+μ+1)/2)*(Gamma ((ν+μ+1)/2))⁻¹ = 1 := mul_inv_cancel₀ hg1
  have k2 : Gamma ((ν+μ+2)/2)*(Gamma ((ν+μ+2)/2))⁻¹ = 1 := mul_inv_cancel₀ hg2
  rw [cpow_neg, show ν*π = (ν+μ)*π/2 + (ν-μ)*π/2 by ring, cos_add]
  generalize (Gamma ((1-ν+μ)/2))⁻¹ = A2 at e2
  generalize (Gamma ((μ-ν)/2))⁻¹ = B2 at o2
  generalize (Gamma ((ν-μ+1)/2))⁻¹ = r1 at e2
  generalize (Gamma ((ν-μ+2)/2))⁻¹ = r2 at o2
  generalize (Gamma ((ν+μ+1)/2))⁻¹ = R1 at k1
  generalize (Gamma ((ν+μ+2)/2))⁻¹ = R2 at k2
  generalize Gamma ((ν+μ+1)/2) = g1 at k1
  generalize Gamma ((ν+μ+2)/2) = g2 at k2
  generalize ((2:ℂ)^μ)⁻¹ = Ti at kT
  generalize (2:ℂ)^μ = T at kT
  generalize sin ((ν+μ)*π/2) = sb
  generalize cos ((ν+μ)*π/2) = cb
  generalize sin ((ν-μ)*π/2) = sa at o2
  generalize cos ((ν-μ)*π/2) = ca at e2
  linear_combination (π/2:ℂ)*((Ti*T*R2*g2*cb)*e2 + (Ti*T*R1*g1*sb)*o2 + cb*ca*(R2*g2*kT + k2) -
    sb*sa*(R1*g1*kT + k1))

end Wronskians

end DLMF.Legendre
