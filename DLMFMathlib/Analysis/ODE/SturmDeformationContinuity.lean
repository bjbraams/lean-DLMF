/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.SturmDeformation

/-!
# Continuity of the `k`-th zero in families of functions

Let `y(t, x)` be a family of real functions of `x`, depending on a parameter `t`, such that `y`
and `∂ₓ y` are jointly continuous and all zeros in `x` are simple. Enumerate the zeros of
`y(t, ·)` above a level `A` increasingly. If near `t₀` no zero enters through a fixed interval
`(A, A + η]`, then the `k`-th zero above `A` depends continuously on `t`: for `t` near `t₀` there
is a `k`-th zero within any prescribed distance of the `k`-th zero at `t₀`. The proof places
small windows around the first `k + 1` zeros at `t₀`, each containing exactly one zero of the
nearby members of the family (`ODE.SturmDeformation.local`), and excludes zeros elsewhere below
the last window by a compactness argument.

## Main results

* `ODE.SturmDeformation.eventually_exists_zero_encard_inter_Iio_eq`: continuity of the `k`-th
  zero above a level.
-/

@[expose] public section

open Set Filter Topology

namespace ODE

variable {T : Type*} [TopologicalSpace T] {Y Y' : T → ℝ → ℝ} {Λ : Set T}

/-- **Continuity of the `k`-th zero.** Let `y` and `∂ₓ y` be jointly continuous on `Λ × ℝ`
(`Λ` open), with simple zeros. Suppose that for `t` near `t₀` the interval `(A, A + η]` contains
no zero of `y(t, ·)`, and let `z` be the zero of `y(t₀, ·)` above `A` with exactly `k` smaller
zeros above `A`. Then for every `ε > 0` and all `t` near `t₀`, `y(t, ·)` has a zero `x` above `A`
with `|x - z| < ε` and exactly `k` smaller zeros above `A`. -/
theorem SturmDeformation.eventually_exists_zero_encard_inter_Iio_eq (hΛ : IsOpen Λ)
    (hcY : ContinuousOn (Function.uncurry Y) (Λ ×ˢ univ))
    (hcY' : ContinuousOn (Function.uncurry Y') (Λ ×ˢ univ))
    (hd : ∀ t ∈ Λ, ∀ x ∈ (univ : Set ℝ), HasDerivAt (Y t) (Y' t x) x)
    (hs : ∀ t ∈ Λ, ∀ x ∈ (univ : Set ℝ), Y t x = 0 → Y' t x ≠ 0) {t₀ : T} (ht₀ : t₀ ∈ Λ)
    {A η : ℝ} (hη : 0 < η) (hA : ∀ᶠ t in 𝓝 t₀, ∀ x ∈ Ioc A (A + η), Y t x ≠ 0)
    {z : ℝ} {k : ℕ} (hzA : A < z) (hz : Y t₀ z = 0)
    (hk : ({x | A < x ∧ Y t₀ x = 0} ∩ Iio z).encard = k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∃ x, |x - z| < ε ∧ A < x ∧ Y t x = 0 ∧
      ({y | A < y ∧ Y t y = 0} ∩ Iio x).encard = k := by
  set S₀ := {x | A < x ∧ Y t₀ x = 0} with hS₀
  set Z := S₀ ∩ Iic z with hZ
  have hS₀f : (S₀ ∩ Iio z).Finite := Set.finite_of_encard_eq_coe hk
  have hZf : Z.Finite := by
    refine (hS₀f.insert z).subset fun x hx => ?_
    rcases eq_or_lt_of_le hx.2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hx.1, h⟩
  have hzZ : z ∈ Z := ⟨⟨hzA, hz⟩, le_rfl⟩
  have hZη : ∀ w ∈ Z, A + η < w := by
    intro w hw
    by_contra h
    push Not at h
    exact hA.self_of_nhds w ⟨hw.1.1, h⟩ hw.1.2
  -- local one-zero windows
  have hloc : ∀ w ∈ Z, ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ →
      ∀ᶠ t in 𝓝 t₀, ∃! x, x ∈ Ioo (w - δ) (w + δ) ∧ Y t x = 0 := fun w hw =>
    SturmDeformation.local hΛ isOpen_univ hcY hcY' hd ht₀ (mem_univ w) hw.1.2
      (hs t₀ ht₀ w (mem_univ w) hw.1.2)
  choose! δ₀ hδ₀ hδloc using hloc
  -- a common radius
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ ε ∧ δ ≤ η ∧ (∀ w ∈ Z, δ ≤ δ₀ w / 2) ∧
      ∀ w ∈ Z, ∀ w' ∈ Z, w ≠ w' → 3 * δ ≤ |w - w'| := by
    have hle : ∀ c : ℝ, 0 < c → ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ c := fun c hc =>
      nhdsWithin_le_nhds (eventually_le_nhds hc)
    refine (hle ε hε).and ((hle η hη).and (((hZf.eventually_all).2 fun w hw =>
      hle _ (by linarith [hδ₀ w hw])).and ((hZf.eventually_all).2 fun w hw =>
        (hZf.eventually_all).2 fun w' hw' => ?_)))
    by_cases hww : w = w'
    · exact Eventually.of_forall fun _ h => absurd hww h
    · have hpos : 0 < |w - w'| / 3 := by
        have := abs_pos.mpr (sub_ne_zero.mpr hww); positivity
      filter_upwards [hle _ hpos] with δ hδ _
      linarith
  obtain ⟨δ, ⟨hδε, hδη, hδ₀', hsep⟩, hδpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδpos : (0 : ℝ) < δ := hδpos
  -- at `t₀` the window around `z` contains no zero other than `z`
  have hzonly : ∀ x, x ∈ Ioo (z - δ₀ z) (z + δ₀ z) → Y t₀ x = 0 → x = z := by
    obtain ⟨y, -, hy⟩ := (hδloc z hzZ (δ₀ z) (hδ₀ z hzZ) le_rfl).self_of_nhds
    intro x hx hx0
    rw [hy x ⟨hx, hx0⟩, hy z ⟨⟨by linarith [hδ₀ z hzZ], by linarith [hδ₀ z hzZ]⟩, hz⟩]
  -- the compact remainder
  set K := Icc (A + η) (z + δ) \ ⋃ w ∈ Z, Ioo (w - δ) (w + δ) with hK
  have hKc : IsCompact K := isCompact_Icc.diff (isOpen_biUnion fun w _ => isOpen_Ioo)
  have hK0 : ∀ x ∈ K, Y t₀ x ≠ 0 := by
    intro x hx h0
    refine hx.2 ?_
    rcases le_or_gt x z with hxz | hxz
    · have hxZ : x ∈ Z := ⟨⟨by linarith [hx.1.1], h0⟩, hxz⟩
      exact mem_iUnion₂.mpr ⟨x, hxZ, by linarith, by linarith⟩
    · have := hδ₀' z hzZ
      have := hzonly x ⟨by linarith, by linarith [hx.1.2]⟩ h0
      linarith
  have hKev : ∀ᶠ t in 𝓝 t₀, ∀ x ∈ K, Y t x ≠ 0 := by
    refine hKc.eventually_forall_of_forall_eventually fun x hx => ?_
    have hc := SturmDeformation.continuousAt hΛ isOpen_univ hcY ht₀ (mem_univ x)
    exact hc.eventually (isOpen_ne.mem_nhds (hK0 x hx))
  have hwin : ∀ᶠ t in 𝓝 t₀, ∀ w ∈ Z, ∃! x, x ∈ Ioo (w - δ) (w + δ) ∧ Y t x = 0 :=
    (hZf.eventually_all).2 fun w hw => hδloc w hw δ hδpos
      ((hδ₀' w hw).trans (by linarith [hδ₀ w hw]))
  filter_upwards [hKev, hA, hwin] with t hKt hAt hwt
  choose! X hX hXu using hwt
  have hXz := hX z hzZ
  have hdisj : ∀ w ∈ Z, ∀ w' ∈ Z, ∀ x, x ∈ Ioo (w - δ) (w + δ) →
      x ∈ Ioo (w' - δ) (w' + δ) → w = w' := by
    intro w hw w' hw' x hx hx'
    by_contra hne
    have h1 := hsep w hw w' hw' hne
    have : |w - w'| < 2 * δ := by
      rw [abs_lt]; constructor <;> linarith [hx.1, hx.2, hx'.1, hx'.2]
    linarith
  refine ⟨X z, ?_, by linarith [hXz.1.1, hZη z hzZ], hXz.2, ?_⟩
  · rw [abs_lt]; constructor <;> linarith [hXz.1.1, hXz.1.2]
  · have hset : {y | A < y ∧ Y t y = 0} ∩ Iio (X z) = X '' (S₀ ∩ Iio z) := by
      ext y
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Iio, mem_image]
      constructor
      · rintro ⟨⟨hyA, hy0⟩, hyX⟩
        have hyη : A + η < y := by
          by_contra h
          push Not at h
          exact hAt y ⟨hyA, h⟩ hy0
        have hyK : y ∉ K := fun h => hKt y h hy0
        have hyU : y ∈ ⋃ w ∈ Z, Ioo (w - δ) (w + δ) := by
          by_contra h
          exact hyK ⟨⟨hyη.le, by linarith [hXz.1.2]⟩, h⟩
        obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.mp hyU
        have hyX' : y = X w := hXu w hw y ⟨hyw, hy0⟩
        refine ⟨w, ⟨hw.1, lt_of_le_of_ne hw.2 fun hwz => ?_⟩, hyX'.symm⟩
        rw [hwz] at hyX'
        exact lt_irrefl _ (hyX' ▸ hyX)
      · rintro ⟨w, ⟨hwS, hwz⟩, rfl⟩
        have hw : w ∈ Z := ⟨hwS, hwz.le⟩
        have hXw := hX w hw
        have h3 := hsep w hw z hzZ hwz.ne
        rw [abs_sub_comm, abs_of_pos (by linarith)] at h3
        refine ⟨⟨by linarith [hXw.1.1, hZη w hw], hXw.2⟩, ?_⟩
        linarith [hXw.1.2, hXz.1.1]
    rw [hset, InjOn.encard_image, hk]
    intro w hw w' hw' h
    exact hdisj w ⟨hw.1, hw.2.le⟩ w' ⟨hw'.1, hw'.2.le⟩ (X w) (hX w ⟨hw.1, hw.2.le⟩).1
      (h ▸ (hX w' ⟨hw'.1, hw'.2.le⟩).1)

end ODE
