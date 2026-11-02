/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.EllipticFunctionsAndInvariants
public import DLMF.Weierstrass.DifferentialEquations

/-!
# Addition, duplication, `n`-tuple formulas and homogeneity (DLMF §23.10)

Addition theorems, duplication and `n`-tuple formulas, and homogeneity of the Weierstrass
functions `℘`, `ζ` and `σ`.

## Main definitions

* `divisionPoint`: the `n²` shifts `2jω₁/n + 2ℓω₃/n`, `0 ≤ j, ℓ < n`.
* `nTupleConst`: the constant `A_n` of DLMF 23.10.13, by the corrected DLMF 23.10.14.
* `nTupleG`: `G = ∏_{n≥1} (1 - q^{2n})` (DLMF 23.10.16).

## Main results

* `weierstrassP_add`, `weierstrassZeta_add`: DLMF 23.10.1–23.10.2.
* `weierstrassSigma_add_mul_sub`, `weierstrassSigma_three_term`: DLMF 23.10.3–23.10.4.
* `weierstrassP_det_eq_zero`, `weierstrassZeta_sum_sq`: DLMF 23.10.5–23.10.6.
* `weierstrassP_two_mul`, `weierstrassP_two_mul_sub_e`, `weierstrassZeta_two_mul`,
  `weierstrassSigma_two_mul`: duplication formulas, DLMF 23.10.7–23.10.10.
* `weierstrassP_nsmul`, `weierstrassZeta_nsmul`, `weierstrassSigma_nsmul`: `n`-tuple
  formulas, DLMF 23.10.11–23.10.13, with the stronger primed forms for all `n ≥ 1` (and, for
  `ζ` and `σ`, all `n` and `z`).
* `nTupleConst_eq`: the corrected DLMF 23.10.15.
* `weierstrassP_scale`, `weierstrassZeta_scale`, `weierstrassSigma_scale`: homogeneity,
  DLMF 23.10.17–23.10.19.

## Implementation notes

Derivatives of `ζ` and `℘'` are Lean derivatives. Each identity is stated where its
denominators are defined (points off the lattice, distinct values of `℘`).

**Source corrections in §23.10(iii).** DLMF 23.10.14 prints the product over `ℓ ≠ j`; the
correct index set (the nonzero `n`-division points) is `(j, ℓ) ≠ (0, 0)`. With the printed
index set 23.10.13 fails numerically (e.g. a relative error `0.71` for `n = 2`,
`ω₁ = 1.1 + 0.2i`, `ω₃ = 0.3 + 0.9i`), with the corrected one it holds to `10⁻⁹`. In 23.10.15
the factor `(π²G²/ω₁)^{n²-1}` must be `(πG²/ω₁)^{n²-1}`: the printed value differs from the
corrected 23.10.14 by exactly `π^{n²-1}` (checked for `n = 2, 3, 4` and three lattices).
Both corrected forms are the ones stated.
-/

@[expose] public section

open Complex PeriodPair
open scoped Real
open Filter Topology

noncomputable section

namespace DLMF.Weierstrass

/-! ### Addition theorems (§23.10(i)) -/

section Addition
open Classical in
/-- The order of `σ` is `1` at lattice points and `0` elsewhere. -/
private lemma meromorphicOrderAt_weierstrassSigma (L : PeriodPair) (x : ℂ) :
    meromorphicOrderAt (weierstrassSigma L) x = if x ∈ L.lattice then 1 else 0 := by
  have ha : AnalyticAt ℂ (weierstrassSigma L) x :=
    (differentiable_weierstrassSigma L).analyticAt x
  rw [ha.meromorphicOrderAt_eq]
  split_ifs with hx
  · rw [ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (weierstrassSigma_eq_zero_of_mem L hx)
      (deriv_weierstrassSigma_ne_zero L hx)]
    rfl
  · rw [ha.analyticOrderAt_eq_zero.mpr ((weierstrassSigma_eq_zero_iff L).not.mpr hx)]
    rfl

/-- `k ≤ o` gives `0 ≤ o - k` in `WithTop ℤ`. -/
private lemma nonneg_add_neg_of_le {o : WithTop ℤ} {k : ℤ} (h : (k : WithTop ℤ) ≤ o) :
    0 ≤ o + -(k : WithTop ℤ) := by
  cases o with
  | top => simp
  | coe n =>
    have : k ≤ n := WithTop.coe_le_coe.mp h
    have e : ((0 : ℤ) : WithTop ℤ) ≤ ((n + -k : ℤ) : WithTop ℤ) := WithTop.coe_le_coe.mpr (by omega)
    exact e

open Classical in
/-- Lower bound for the order of `℘ - ℘(v)` at a non-lattice point. -/
private lemma le_meromorphicOrderAt_weierstrassP_sub (L : PeriodPair) {v x : ℂ}
    (hx : x ∉ L.lattice) :
    (((if x + v ∈ L.lattice then 1 else 0) + (if x - v ∈ L.lattice then 1 else 0) : ℤ) :
      WithTop ℤ) ≤ meromorphicOrderAt (fun u => ℘[L] u - ℘[L] v) x := by
  have hA : AnalyticAt ℂ (fun u => ℘[L] u - ℘[L] v) x :=
    (L.analyticOnNhd_weierstrassP x hx).sub analyticAt_const
  have hval : x + v ∈ L.lattice ∨ x - v ∈ L.lattice → ℘[L] x - ℘[L] v = 0 := by
    rintro (h | h)
    · rw [show x = -v + ((⟨x + v, h⟩ : L.lattice) : ℂ) by simp, L.weierstrassP_add_coe,
        L.weierstrassP_neg, sub_self]
    · rw [show x = v + ((⟨x - v, h⟩ : L.lattice) : ℂ) by simp, L.weierstrassP_add_coe, sub_self]
  by_cases h1 : x + v ∈ L.lattice <;> by_cases h2 : x - v ∈ L.lattice
  · simp only [h1, h2, ite_true]
    have h2v : 2 * v ∈ L.lattice := by
      have := sub_mem h1 h2; rwa [show x + v - (x - v) = 2 * v by ring] at this
    have hd : deriv (fun u => ℘[L] u - ℘[L] v) x = 0 := by
      rw [deriv_sub_const, deriv_weierstrassP,
        show x = v + ((⟨x - v, h2⟩ : L.lattice) : ℂ) by simp, L.derivWeierstrassP_add_coe,
        derivWeierstrassP_eq_zero_of_two_mul_mem L h2v]
    have := two_le_meromorphicOrderAt_of_deriv_eq_zero hA (hval (.inl h1)) hd
    exact le_of_eq_of_le (by norm_num) this
  · simp only [h1, h2, ite_true, ite_false]
    rw [hA.meromorphicOrderAt_eq]
    have : analyticOrderAt (fun u => ℘[L] u - ℘[L] v) x ≠ 0 :=
      hA.analyticOrderAt_ne_zero.mpr (hval (.inl h1))
    cases h : analyticOrderAt (fun u => ℘[L] u - ℘[L] v) x with
    | top => simp
    | coe n =>
      rw [h] at this
      have : 1 ≤ n := by
        rcases n with _ | n
        · exact absurd rfl this
        · omega
      simp only [ENat.map_natCast]
      exact WithTop.coe_le_coe.mpr (by omega)
  · simp only [h1, h2, ite_true, ite_false]
    rw [hA.meromorphicOrderAt_eq]
    have : analyticOrderAt (fun u => ℘[L] u - ℘[L] v) x ≠ 0 :=
      hA.analyticOrderAt_ne_zero.mpr (hval (.inr h2))
    cases h : analyticOrderAt (fun u => ℘[L] u - ℘[L] v) x with
    | top => simp
    | coe n =>
      rw [h] at this
      have : 1 ≤ n := by
        rcases n with _ | n
        · exact absurd rfl this
        · omega
      simp only [ENat.map_natCast]
      exact WithTop.coe_le_coe.mpr (by omega)
  · simp only [h1, h2, ite_false]
    exact hA.meromorphicOrderAt_nonneg

/-- `(℘(u) - ℘(v))σ(u)²σ(v)² = -σ(u + v)σ(u - v)` off the singular set (Liouville). -/
private lemma weierstrassP_sub_mul_weierstrassSigma_div_eq (L : PeriodPair) {v : ℂ}
    (hv : v ∉ L.lattice) {u : ℂ}
    (hu : u ∉ L.lattice) (h1 : u + v ∉ L.lattice) (h2 : u - v ∉ L.lattice) :
    (℘[L] u - ℘[L] v) * (weierstrassSigma L u * weierstrassSigma L u * weierstrassSigma L v ^ 2) *
      (weierstrassSigma L (u + v) * weierstrassSigma L (u - v))⁻¹ = -1 := by
  set σ := weierstrassSigma L with hσ
  have hσd : Differentiable ℂ σ := differentiable_weierstrassSigma L
  have hσv : σ v ≠ 0 := (weierstrassSigma_eq_zero_iff L).not.mpr hv
  set F : ℂ → ℂ := fun u => (℘[L] u - ℘[L] v) * (σ u * σ u * σ v ^ 2) *
    (σ (u + v) * σ (u - v))⁻¹ with hF
  have hA : ∀ x, MeromorphicAt (fun u => ℘[L] u - ℘[L] v) x := fun x =>
    (L.meromorphic_weierstrassP x).sub (MeromorphicAt.const _ _)
  have hSa : ∀ c x, AnalyticAt ℂ (fun u => σ (u + c)) x := fun c x =>
    (hσd.comp (differentiable_id.add_const c)).analyticAt x
  have hSa' : ∀ c x, AnalyticAt ℂ (fun u => σ (u - c)) x := fun c x =>
    (hσd.comp (differentiable_id.sub_const c)).analyticAt x
  have hB : ∀ x, AnalyticAt ℂ (fun u => σ u * σ u * σ v ^ 2) x := fun x =>
    ((hσd.analyticAt x).mul (hσd.analyticAt x)).mul analyticAt_const
  have hC : ∀ x, AnalyticAt ℂ (fun u => σ (u + v) * σ (u - v)) x := fun x =>
    (hSa v x).mul (hSa' v x)
  have hFm : Meromorphic F := fun x =>
    ((hA x).mul (hB x).meromorphicAt).mul (hC x).meromorphicAt.inv
  -- periodicity
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, z₀ ∉ L.lattice := ⟨_, L.ω₁_div_two_notMem_lattice⟩
  have hper : ∀ z, ∀ l ∈ L.lattice, F (z + l) = F z := by
    intro z l hl
    obtain ⟨a, ha, hfa⟩ := exists_weierstrassSigma_add_mem L hl hz₀
    set c := weierstrassZeta L (z₀ + l) - weierstrassZeta L z₀
    simp only [hF]
    rw [show z + l + v = (z + v) + l by ring, show z + l - v = (z - v) + l by ring,
      hσ, hfa z, hfa (z + v), hfa (z - v), L.weierstrassP_add_coe z ⟨l, hl⟩]
    rw [← hσ]
    have he : cexp (c * (z + v)) * cexp (c * (z - v)) = cexp (c * z) * cexp (c * z) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
    by_cases hD : σ (z + v) * σ (z - v) = 0
    · have : a * cexp (c * (z + v)) * σ (z + v) * (a * cexp (c * (z - v)) * σ (z - v)) = 0 := by
        rw [show a * cexp (c * (z + v)) * σ (z + v) * (a * cexp (c * (z - v)) * σ (z - v)) =
          a * a * (cexp (c * (z + v)) * cexp (c * (z - v))) * (σ (z + v) * σ (z - v)) by ring, hD,
          mul_zero]
      rw [this, hD]; simp
    · have hE : cexp (c * z) ≠ 0 := Complex.exp_ne_zero _
      have hprod : a * cexp (c * (z + v)) * σ (z + v) * (a * cexp (c * (z - v)) * σ (z - v)) =
          (a * cexp (c * z)) ^ 2 * (σ (z + v) * σ (z - v)) := by
        linear_combination (a ^ 2 * σ (z + v) * σ (z - v)) * he
      rw [hprod]
      have hX : (a * cexp (c * z)) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero ha hE)
      calc (℘[L] z - ℘[L] v) * (a * cexp (c * z) * σ z * (a * cexp (c * z) * σ z) * σ v ^ 2) *
            ((a * cexp (c * z)) ^ 2 * (σ (z + v) * σ (z - v)))⁻¹
          = (℘[L] z - ℘[L] v) * (σ z * σ z * σ v ^ 2) * (σ (z + v) * σ (z - v))⁻¹ *
            ((a * cexp (c * z)) ^ 2 * ((a * cexp (c * z)) ^ 2)⁻¹) := by rw [mul_inv]; ring
        _ = _ := by rw [mul_inv_cancel₀ hX, mul_one]
  have hσnot : ∀ x, x ∉ L.lattice → σ x ≠ 0 := fun x hx =>
    (weierstrassSigma_eq_zero_iff L).not.mpr hx
  have hoσ := meromorphicOrderAt_weierstrassSigma L
  have hord : ∀ x, 0 ≤ meromorphicOrderAt F x := by
    intro x
    have eF : F = ((fun u => ℘[L] u - ℘[L] v) * (σ * σ * fun _ => σ v ^ 2)) *
        ((fun u => σ (u + v)) * (fun u => σ (u - v)))⁻¹ := rfl
    have mS : ∀ y, MeromorphicAt σ y := fun y => (hσd.analyticAt y).meromorphicAt
    rw [eF, meromorphicOrderAt_mul ((hA x).mul (((mS x).mul (mS x)).mul
        (MeromorphicAt.const _ _))) ((hSa v x).meromorphicAt.mul (hSa' v x).meromorphicAt).inv,
      meromorphicOrderAt_mul (hA x) (((mS x).mul (mS x)).mul (MeromorphicAt.const _ _)),
      meromorphicOrderAt_inv,
      meromorphicOrderAt_mul ((mS x).mul (mS x)) (MeromorphicAt.const _ _),
      meromorphicOrderAt_mul (mS x) (mS x),
      meromorphicOrderAt_mul (hSa v x).meromorphicAt (hSa' v x).meromorphicAt]
    have op : meromorphicOrderAt (fun u => σ (u + v)) x = meromorphicOrderAt σ (x + v) := by
      have := meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (f := σ) (c := v)
        (x := x)
      simpa using this
    have om : meromorphicOrderAt (fun u => σ (u - v)) x = meromorphicOrderAt σ (x - v) := by
      have := meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt (f := σ) (c := v)
        (x := x)
      simpa using this
    have oc : meromorphicOrderAt (fun _ : ℂ => σ v ^ 2) x = 0 := by
      classical
      rw [meromorphicOrderAt_const]; simp [hσv]
    rw [op, om, oc, hoσ, hoσ, hoσ]
    by_cases hx : x ∈ L.lattice
    · have hxp : x + v ∉ L.lattice := fun h => hv (by simpa using sub_mem h hx)
      have hxm : x - v ∉ L.lattice := fun h => hv (by simpa using sub_mem hx h)
      rw [meromorphicOrderAt_weierstrassP_sub_of_mem L hx]
      simp only [hx, hxp, hxm, ite_true, ite_false]
      decide
    · have hb := le_meromorphicOrderAt_weierstrassP_sub L (v := v) hx
      by_cases hxp : x + v ∈ L.lattice <;> by_cases hxm : x - v ∈ L.lattice <;>
        simp only [hx, hxp, hxm, ite_true, ite_false, add_zero, zero_add] at hb ⊢
      · exact nonneg_add_neg_of_le (k := 2) (by exact_mod_cast hb)
      · exact nonneg_add_neg_of_le (k := 1) (by exact_mod_cast hb)
      · exact nonneg_add_neg_of_le (k := 1) (by exact_mod_cast hb)
      · simpa using hb
  obtain ⟨c, hc⟩ := exists_eq_const_of_periodic_of_order_nonneg L hFm hper hord
  have hFan : ∀ w, w ∉ L.lattice → w + v ∉ L.lattice → w - v ∉ L.lattice → AnalyticAt ℂ F w :=
    fun w hw hwp hwm => (((L.analyticOnNhd_weierstrassP w hw).sub analyticAt_const).mul
      (hB w)).mul ((hC w).inv (mul_ne_zero (hσnot _ hwp) (hσnot _ hwm)))
  have hcont : Continuous fun w : ℂ => w + v := by fun_prop
  have hcont' : Continuous fun w : ℂ => w - v := by fun_prop
  have hmv : -v ∉ L.lattice := fun h => hv (by simpa using neg_mem h)
  have hopen : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have hev : ∀ᶠ w in 𝓝[≠] (0 : ℂ), F w = c := by
    filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      self_mem_nhdsWithin,
      nhdsWithin_le_nhds ((hcont.tendsto 0).eventually (hopen.mem_nhds (by simpa using hv))),
      nhdsWithin_le_nhds ((hcont'.tendsto 0).eventually (hopen.mem_nhds (by simpa using hmv)))]
      with w h1 h0 hp hm
    exact hc w (hFan w (fun h => h1 ⟨h, h0⟩) hp hm)
  -- the limit at `0`
  have hT1 : Tendsto (fun w => w ^ 2 * (℘[L] w - ℘[L] v)) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have hg := (analyticAt_weierstrassP_sub L (zero_mem _)).continuousAt
    have : Tendsto (fun w => 1 + w ^ 2 * (℘[L] w - 1 / (w - 0) ^ 2) - w ^ 2 * ℘[L] v)
        (𝓝[≠] (0 : ℂ)) (𝓝 (1 + 0 ^ 2 * (℘[L] 0 - 1 / (0 - 0) ^ 2) - 0 ^ 2 * ℘[L] v)) := by
      refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      exact ((tendsto_const_nhds.add ((continuous_pow 2).continuousAt.tendsto.mul hg)).sub
        ((continuous_pow 2).continuousAt.tendsto.mul tendsto_const_nhds))
    simp only [zero_pow two_ne_zero, zero_mul, add_zero, sub_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw0 : w ≠ 0 := hw
    field_simp
    ring
  have hT2 : Tendsto (fun w => σ w / w) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have := (hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_weierstrassSigma_zero L))
    refine this.congr' (Eventually.of_forall fun w => ?_)
    simp [slope_def_field, hσ, weierstrassSigma_eq_zero_of_mem L (zero_mem _)]
  have hT3 : Tendsto (fun w => (σ (w + v) * σ (w - v))⁻¹) (𝓝[≠] (0 : ℂ))
      (𝓝 (σ (0 + v) * σ (0 - v))⁻¹) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    refine Tendsto.inv₀ ?_
        (mul_ne_zero (hσnot _ (by simpa using hv)) (hσnot _ (by simpa using hmv)))
    exact ((hσd.continuous.comp hcont).tendsto 0).mul ((hσd.continuous.comp hcont').tendsto 0)
  have hlim : Tendsto F (𝓝[≠] (0 : ℂ)) (𝓝 (1 * (1 * 1 * σ v ^ 2) * (σ (0 + v) * σ (0 - v))⁻¹)) := by
    have := (hT1.mul ((hT2.mul hT2).mul (tendsto_const_nhds (x := σ v ^ 2)))).mul hT3
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw0 : w ≠ 0 := hw
    simp only [hF]
    field_simp
  have hval : 1 * (1 * 1 * σ v ^ 2) * (σ (0 + v) * σ (0 - v))⁻¹ = -1 := by
    rw [zero_add, zero_sub, hσ, weierstrassSigma_neg, ← hσ]
    field_simp
  rw [hval] at hlim
  have hc1 : c = -1 :=
      tendsto_nhds_unique (tendsto_const_nhds.congr' (hev.mono fun w hw => hw.symm))
    hlim
  rw [← hc1]
  exact hc u (hFan u hu h1 h2)

/-- `σ(u+v)σ(u-v) = (℘(v) - ℘(u)) σ(u)² σ(v)²` for `u, v ∉ 𝕃` (23.10.3 with cleared
denominators). -/
private lemma weierstrassSigma_add_mul_sub_of_not_mem (L : PeriodPair) {u v : ℂ}
    (hu : u ∉ L.lattice) (hv : v ∉ L.lattice) :
    weierstrassSigma L (u + v) * weierstrassSigma L (u - v) =
      (℘[L] v - ℘[L] u) * weierstrassSigma L u ^ 2 * weierstrassSigma L v ^ 2 := by
  by_cases h1 : u + v ∈ L.lattice
  · have : ℘[L] u = ℘[L] v := by
      rw [show u = -v + (u + v) by ring, weierstrassP_add_coe L (-v) ⟨u + v, h1⟩,
        weierstrassP_neg]
    rw [weierstrassSigma_eq_zero_of_mem L h1, this]
    simp
  by_cases h2 : u - v ∈ L.lattice
  · have : ℘[L] u = ℘[L] v := by
      rw [show u = v + (u - v) by ring, weierstrassP_add_coe L v ⟨u - v, h2⟩]
    rw [weierstrassSigma_eq_zero_of_mem L h2, this]
    simp
  have hp := weierstrassP_sub_mul_weierstrassSigma_div_eq L hv hu h1 h2
  have h1' : weierstrassSigma L (u + v) ≠ 0 := (weierstrassSigma_eq_zero_iff L).not.mpr h1
  have h2' : weierstrassSigma L (u - v) ≠ 0 := (weierstrassSigma_eq_zero_iff L).not.mpr h2
  field_simp at hp
  linear_combination hp

/-- `σ' = ζ σ` off the lattice. -/
private lemma deriv_weierstrassSigma_eq_zeta_mul (L : PeriodPair) {x : ℂ} (hx : x ∉ L.lattice) :
    deriv (weierstrassSigma L) x = weierstrassZeta L x * weierstrassSigma L x := by
  have hσ : weierstrassSigma L x ≠ 0 := (weierstrassSigma_eq_zero_iff L).not.mpr hx
  rw [weierstrassZeta_eq_deriv_div L hx]; field_simp

/-- `℘` has derivative `℘'` off the lattice. -/
theorem hasDerivAt_weierstrassP (L : PeriodPair) {x : ℂ} (hx : x ∉ L.lattice) :
    HasDerivAt ℘[L] (℘'[L] x) x := by
  have := ((L.analyticOnNhd_weierstrassP x hx).differentiableAt).hasDerivAt
  rwa [L.deriv_weierstrassP] at this

/-- `℘'` has derivative `6℘² - g₂/2` off the lattice. -/
theorem hasDerivAt_derivWeierstrassP (L : PeriodPair) {x : ℂ} (hx : x ∉ L.lattice) :
    HasDerivAt ℘'[L] (6 * ℘[L] x ^ 2 - L.g₂ / 2) x := by
  have h := (L.analyticOnNhd_weierstrassP x hx).deriv
  rw [L.deriv_weierstrassP] at h
  have := h.differentiableAt.hasDerivAt
  rwa [deriv_derivWeierstrassP L hx] at this

/-- The addition formula for `ζ` in terms of `℘` and `℘'`, together with `℘(u) ≠ ℘(v)`. -/
private lemma weierstrassP_ne_and_weierstrassZeta_add (L : PeriodPair) {u v : ℂ}
    (hu : u ∉ L.lattice) (hv : v ∉ L.lattice)
    (huv : u + v ∉ L.lattice) (huv' : u - v ∉ L.lattice) :
    ℘[L] u ≠ ℘[L] v ∧ weierstrassZeta L (u + v) = weierstrassZeta L u + weierstrassZeta L v +
      1 / 2 * ((℘'[L] u - ℘'[L] v) / (℘[L] u - ℘[L] v)) := by
  set σ := weierstrassSigma L with hσ
  set ζ := weierstrassZeta L with hζ
  have hσd : Differentiable ℂ σ := differentiable_weierstrassSigma L
  have hnz : ∀ x, x ∉ L.lattice → σ x ≠ 0 := fun x hx =>
    (weierstrassSigma_eq_zero_iff L).not.mpr hx
  have hopen : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have hne : ℘[L] v - ℘[L] u ≠ 0 := by
    intro h
    have := weierstrassSigma_add_mul_sub_of_not_mem L hu hv
    rw [h] at this
    simp only [zero_mul] at this
    exact mul_ne_zero (hnz _ huv) (hnz _ huv') this
  -- derivative in `u`
  have E1 : (℘[L] v - ℘[L] u) * (ζ (u + v) + ζ (u - v)) =
      -℘'[L] u + 2 * (℘[L] v - ℘[L] u) * ζ u := by
    have hf : HasDerivAt (fun w => σ (w + v) * σ (w - v))
        (deriv σ (u + v) * σ (u - v) + σ (u + v) * deriv σ (u - v)) u :=
      ((hσd _).hasDerivAt.comp_add_const u v).mul ((hσd _).hasDerivAt.comp_sub_const u v)
    have hg : HasDerivAt (fun w => (℘[L] v - ℘[L] w) * σ w ^ 2 * σ v ^ 2)
        ((-℘'[L] u * σ u ^ 2 + (℘[L] v - ℘[L] u) * (2 * σ u * deriv σ u)) * σ v ^ 2) u := by
      have h1 := ((hasDerivAt_weierstrassP L hu).const_sub (℘[L] v)).mul
        ((hσd u).hasDerivAt.pow 2)
      convert h1.mul_const (σ v ^ 2) using 1
      simp
    have heq : (fun w => σ (w + v) * σ (w - v)) =ᶠ[𝓝 u]
        (fun w => (℘[L] v - ℘[L] w) * σ w ^ 2 * σ v ^ 2) := by
      filter_upwards [hopen.mem_nhds hu] with w hw using
          weierstrassSigma_add_mul_sub_of_not_mem L hw hv
    have := (hf.congr_of_eventuallyEq heq.symm).unique hg
    rw [deriv_weierstrassSigma_eq_zeta_mul L huv, deriv_weierstrassSigma_eq_zeta_mul L huv',
        deriv_weierstrassSigma_eq_zeta_mul L hu] at this
    have hm := weierstrassSigma_add_mul_sub_of_not_mem L hu hv
    have hs : σ u ^ 2 * σ v ^ 2 ≠ 0 := by have := hnz u hu; have := hnz v hv; positivity
    apply mul_left_cancel₀ hs
    linear_combination this - (ζ (u + v) + ζ (u - v)) * hm
  -- derivative in `v`
  have E2 : (℘[L] v - ℘[L] u) * (ζ (u + v) - ζ (u - v)) =
      ℘'[L] v + 2 * (℘[L] v - ℘[L] u) * ζ v := by
    have hf : HasDerivAt (fun w => σ (u + w) * σ (u - w))
        (deriv σ (u + v) * σ (u - v) + σ (u + v) * (-deriv σ (u - v))) v :=
      ((hσd _).hasDerivAt.comp_const_add u v).mul ((hσd _).hasDerivAt.comp_const_sub u v)
    have hg : HasDerivAt (fun w => (℘[L] w - ℘[L] u) * σ u ^ 2 * σ w ^ 2)
        (℘'[L] v * σ u ^ 2 * σ v ^ 2 + (℘[L] v - ℘[L] u) * σ u ^ 2 * (2 * σ v * deriv σ v)) v := by
      have h1 := (((hasDerivAt_weierstrassP L hv).sub_const (℘[L] u)).mul_const (σ u ^ 2)).mul
        ((hσd v).hasDerivAt.pow 2)
      convert h1 using 1
      simp
    have heq : (fun w => σ (u + w) * σ (u - w)) =ᶠ[𝓝 v]
        (fun w => (℘[L] w - ℘[L] u) * σ u ^ 2 * σ w ^ 2) := by
      filter_upwards [hopen.mem_nhds hv] with w hw
      rw [weierstrassSigma_add_mul_sub_of_not_mem L hu hw]
    have := (hf.congr_of_eventuallyEq heq.symm).unique hg
    rw [deriv_weierstrassSigma_eq_zeta_mul L huv, deriv_weierstrassSigma_eq_zeta_mul L huv',
        deriv_weierstrassSigma_eq_zeta_mul L hv] at this
    have hm := weierstrassSigma_add_mul_sub_of_not_mem L hu hv
    have hs : σ u ^ 2 * σ v ^ 2 ≠ 0 := by have := hnz u hu; have := hnz v hv; positivity
    apply mul_left_cancel₀ hs
    linear_combination this - (ζ (u + v) - ζ (u - v)) * hm
  refine ⟨fun h => hne (by rw [h, sub_self]), ?_⟩
  have hne' : ℘[L] u - ℘[L] v ≠ 0 := fun h => hne (by linear_combination -h)
  field_simp
  linear_combination (-1 : ℂ) * (E1 + E2)

/-- Near a point `u` with `u, u ± v ∉ 𝕃`, the same holds. -/
private lemma eventually_not_mem_lattice_add_sub (L : PeriodPair) {u v : ℂ} (hu : u ∉ L.lattice)
    (huv : u + v ∉ L.lattice) (huv' : u - v ∉ L.lattice) :
    ∀ᶠ w in 𝓝 u, w ∉ L.lattice ∧ w + v ∉ L.lattice ∧ w - v ∉ L.lattice := by
  have hopen : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have h1 := hopen.mem_nhds hu
  have h2 := (continuous_id.add (continuous_const (y := v))).continuousAt.preimage_mem_nhds
      (hopen.mem_nhds huv)
  have h3 := (continuous_id.sub (continuous_const (y := v))).continuousAt.preimage_mem_nhds
      (hopen.mem_nhds huv')
  filter_upwards [h1, h2, h3] with w a b c using ⟨a, b, c⟩

/-- Derivative of `(℘'(w) - ℘'(v))/(℘(w) - ℘(v))` at `w = u`. -/
private lemma hasDerivAt_weierstrassP_difference_quotient (L : PeriodPair) {u v : ℂ}
    (hu : u ∉ L.lattice)
    (hne : ℘[L] u - ℘[L] v ≠ 0) :
    HasDerivAt (fun w => (℘'[L] w - ℘'[L] v) / (℘[L] w - ℘[L] v))
      (((6 * ℘[L] u ^ 2 - L.g₂ / 2) * (℘[L] u - ℘[L] v) - (℘'[L] u - ℘'[L] v) * ℘'[L] u) /
        (℘[L] u - ℘[L] v) ^ 2) u :=
  ((hasDerivAt_derivWeierstrassP L hu).sub_const _).div
      ((hasDerivAt_weierstrassP L hu).sub_const _) hne

/-- Differentiated `ζ`-addition formula: `℘(u+v) = ℘(u) - ½ X'(u)`. -/
private lemma neg_weierstrassP_add_eq_deriv_form (L : PeriodPair) {u v : ℂ} (hu : u ∉ L.lattice)
    (hv : v ∉ L.lattice)
    (huv : u + v ∉ L.lattice) (huv' : u - v ∉ L.lattice) :
    -℘[L] (u + v) = -℘[L] u + 1 / 2 *
      (((6 * ℘[L] u ^ 2 - L.g₂ / 2) * (℘[L] u - ℘[L] v) - (℘'[L] u - ℘'[L] v) * ℘'[L] u) /
        (℘[L] u - ℘[L] v) ^ 2) := by
  have hne : ℘[L] u - ℘[L] v ≠ 0 :=
      sub_ne_zero.mpr (weierstrassP_ne_and_weierstrassZeta_add L hu hv huv huv').1
  have heq : (fun w => weierstrassZeta L (w + v)) =ᶠ[𝓝 u] (fun w => weierstrassZeta L w +
      weierstrassZeta L v + 1 / 2 * ((℘'[L] w - ℘'[L] v) / (℘[L] w - ℘[L] v))) := by
    filter_upwards [eventually_not_mem_lattice_add_sub L hu huv huv'] with w ⟨a, b, c⟩
    exact (weierstrassP_ne_and_weierstrassZeta_add L a hv b c).2
  have hf := (hasDerivAt_weierstrassZeta L huv).comp_add_const u v
  have hg := (((hasDerivAt_weierstrassZeta L hu).add_const (weierstrassZeta L v)).add
    ((hasDerivAt_weierstrassP_difference_quotient L hu hne).const_mul (1 / 2)))
  exact (hf.congr_of_eventuallyEq heq.symm).unique hg

/-- The addition formula 23.10.1 (helper form). -/
private lemma weierstrassP_add_of_not_mem (L : PeriodPair) {u v : ℂ} (hu : u ∉ L.lattice)
    (hv : v ∉ L.lattice)
    (huv : u + v ∉ L.lattice) (huv' : u - v ∉ L.lattice) :
    ℘[L] (u + v) = 1 / 4 * ((℘'[L] u - ℘'[L] v) / (℘[L] u - ℘[L] v)) ^ 2 - ℘[L] u - ℘[L] v := by
  have hne : ℘[L] u - ℘[L] v ≠ 0 :=
      sub_ne_zero.mpr (weierstrassP_ne_and_weierstrassZeta_add L hu hv huv huv').1
  have h := neg_weierstrassP_add_eq_deriv_form L hu hv huv huv'
  have hp := L.derivWeierstrassP_sq u hu
  have hq := L.derivWeierstrassP_sq v hv
  field_simp at h ⊢
  linear_combination -h + hp - hq

/-- `ζ' = -℘` off the lattice. -/
private lemma deriv_weierstrassZeta (L : PeriodPair) {x : ℂ} (hx : x ∉ L.lattice) :
    deriv (weierstrassZeta L) x = -℘[L] x := (hasDerivAt_weierstrassZeta L hx).deriv

/-- `ζ'` agrees with `-℘` near points off the lattice. -/
private lemma deriv_weierstrassZeta_eventuallyEq (L : PeriodPair) {x : ℂ} (hx : x ∉ L.lattice) :
    deriv (weierstrassZeta L) =ᶠ[𝓝 x] fun y => -℘[L] y := by
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hx] with y hy
  exact deriv_weierstrassZeta L hy

/-- `ζ'' = -℘'` off the lattice. -/
private lemma deriv_deriv_weierstrassZeta (L : PeriodPair) {x : ℂ} (hx : x ∉ L.lattice) :
    deriv (deriv (weierstrassZeta L)) x = -℘'[L] x := by
  rw [(deriv_weierstrassZeta_eventuallyEq L hx).deriv_eq]
  exact ((hasDerivAt_weierstrassP L hx).neg).deriv

/-- The third derivative of `ζ` is `-(6℘² - g₂/2)` off the lattice. -/
private lemma deriv_deriv_deriv_weierstrassZeta (L : PeriodPair) {x : ℂ} (hx : x ∉ L.lattice) :
    deriv (deriv (deriv (weierstrassZeta L))) x = -(6 * ℘[L] x ^ 2 - L.g₂ / 2) := by
  have : deriv (deriv (weierstrassZeta L)) =ᶠ[𝓝 x] fun y => -℘'[L] y := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hx] with y hy
    exact deriv_deriv_weierstrassZeta L hy
  rw [this.deriv_eq]
  exact ((hasDerivAt_derivWeierstrassP L hx).neg).deriv

/-- The addition formula for `℘'`: `℘'(u+v) = X (℘(u) - ℘(u+v)) - ℘'(u)` with
`X = (℘'(u) - ℘'(v))/(℘(u) - ℘(v))`. -/
private lemma derivWeierstrassP_add (L : PeriodPair) {u v : ℂ} (hu : u ∉ L.lattice)
    (hv : v ∉ L.lattice)
    (huv : u + v ∉ L.lattice) (huv' : u - v ∉ L.lattice) :
    ℘'[L] (u + v) = (℘'[L] u - ℘'[L] v) / (℘[L] u - ℘[L] v) * (℘[L] u - ℘[L] (u + v)) -
      ℘'[L] u := by
  have hne : ℘[L] u - ℘[L] v ≠ 0 :=
      sub_ne_zero.mpr (weierstrassP_ne_and_weierstrassZeta_add L hu hv huv huv').1
  have heq : (fun w => ℘[L] (w + v)) =ᶠ[𝓝 u] (fun w => 1 / 4 *
      ((℘'[L] w - ℘'[L] v) / (℘[L] w - ℘[L] v)) ^ 2 - ℘[L] w - ℘[L] v) := by
    filter_upwards [eventually_not_mem_lattice_add_sub L hu huv huv'] with w ⟨a, b, c⟩
    exact weierstrassP_add_of_not_mem L a hv b c
  have hf := (hasDerivAt_weierstrassP L huv).comp_add_const u v
  have hg := ((((hasDerivAt_weierstrassP_difference_quotient L hu hne).pow 2).const_mul (1 / 4)).sub
    (hasDerivAt_weierstrassP L hu)).sub_const (℘[L] v)
  have h := (hf.congr_of_eventuallyEq heq.symm).unique hg
  have ha := neg_weierstrassP_add_eq_deriv_form L hu hv huv huv'
  norm_num at h
  linear_combination h - (℘'[L] u - ℘'[L] v) / (℘[L] u - ℘[L] v) * ha

/-- `℘'(z) ≠ 0` for `z, 2z ∉ 𝕃`. -/
theorem derivWeierstrassP_ne_zero_of_two_mul_not_mem (L : PeriodPair) {z : ℂ}
    (hz : z ∉ L.lattice)
    (h2z : 2 * z ∉ L.lattice) : ℘'[L] z ≠ 0 := by
  set H := halfPeriodsOf L
  have hl : H.lattice = L.lattice := halfPeriodsOf_lattice L
  have hP : ∀ x, ℘[H.periodPair] x = ℘[L] x := fun x =>
    weierstrassP_eq_of_lattice_eq _ _ hl x
  have hD : ℘'[H.periodPair] = ℘'[L] := by
    rw [← PeriodPair.deriv_weierstrassP, ← PeriodPair.deriv_weierstrassP]
    congr 1; funext x; exact hP x
  intro h0
  have hzH : z ∉ H.lattice := by rwa [hl]
  have hsq := H.derivWeierstrassP_sq_eq_prod hzH
  simp only [HalfPeriods.derivWeierstrassP, HalfPeriods.weierstrassP, hD, h0, hP] at hsq
  rw [zero_pow two_ne_zero] at hsq
  have key : ∃ j ∈ ({1, 2, 3} : Finset ℕ), ℘[L] z = ℘[L] (H.halfPeriod j) := by
    rcases mul_eq_zero.mp hsq.symm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · norm_num at h
        · exact ⟨1, by simp, by rw [sub_eq_zero.mp h, HalfPeriods.e, HalfPeriods.weierstrassP, hP]⟩
      · exact ⟨2, by simp, by rw [sub_eq_zero.mp h, HalfPeriods.e, HalfPeriods.weierstrassP, hP]⟩
    · exact ⟨3, by simp, by rw [sub_eq_zero.mp h, HalfPeriods.e, HalfPeriods.weierstrassP, hP]⟩
  obtain ⟨j, hj, heq⟩ := key
  have ha : H.halfPeriod j ∉ L.lattice := hl ▸ H.halfPeriod_notMem hj
  have h2a : 2 * H.halfPeriod j ∈ L.lattice := hl ▸ H.two_mul_halfPeriod_mem hj
  refine weierstrassP_ne_of_halfLattice L ha h2a hz ?_ heq
  intro hza
  have := sub_mem (add_mem hza hza) h2a
  exact h2z (by convert this using 1; ring)

/-- Generic case of 23.10.6. -/
private lemma weierstrassZeta_sum_sq_of_sub_not_mem (L : PeriodPair) {u v w : ℂ}
    (hu : u ∉ L.lattice)
    (hv : v ∉ L.lattice) (hw : w ∉ L.lattice) (h : u + v + w = 0) (huv' : u - v ∉ L.lattice) :
    (weierstrassZeta L u + weierstrassZeta L v + weierstrassZeta L w) ^ 2 +
      deriv (weierstrassZeta L) u + deriv (weierstrassZeta L) v +
        deriv (weierstrassZeta L) w = 0 := by
  have hw' : w = -(u + v) := by linear_combination h
  have huv : u + v ∉ L.lattice := fun hm => hw (by rw [hw']; exact neg_mem hm)
  obtain ⟨hne, hz⟩ := weierstrassP_ne_and_weierstrassZeta_add L hu hv huv huv'
  rw [deriv_weierstrassZeta L hu, deriv_weierstrassZeta L hv, deriv_weierstrassZeta L hw, hw',
    weierstrassZeta_neg, L.weierstrassP_neg, hz, weierstrassP_add_of_not_mem L hu hv huv huv']
  ring

/-- Points near `z` (`z ∉ 𝕃`) other than `z` satisfy `v ∉ 𝕃`, `z - v ∉ 𝕃`. -/
private lemma eventually_not_mem_lattice_sub_nhdsNE (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    ∀ᶠ v in 𝓝[≠] z, v ∉ L.lattice ∧ z - v ∉ L.lattice := by
  have hopen : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have hC := (continuous_const.sub continuous_id : Continuous fun y : ℂ => z - y).continuousAt
    |>.preimage_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds (z - z))
  filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hz), nhdsWithin_le_nhds hC,
    self_mem_nhdsWithin] with v h1 h2 h3
  refine ⟨h1, fun hm => h2 ⟨hm, fun he => h3 ?_⟩⟩
  have : z - v = z - z := he
  exact sub_right_injective this

/-- The difference quotient `(℘'(z) - ℘'(v))/(℘(z) - ℘(v))` tends to `℘''(z)/℘'(z)`. -/
private lemma tendsto_derivWeierstrassP_difference_quotient (L : PeriodPair) {z : ℂ}
    (hz : z ∉ L.lattice) (hp : ℘'[L] z ≠ 0) :
    Tendsto (fun v => (℘'[L] z - ℘'[L] v) / (℘[L] z - ℘[L] v)) (𝓝[≠] z)
      (𝓝 (deriv ℘'[L] z / ℘'[L] z)) := by
  have h1 := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_weierstrassP L hz)
  have hd : HasDerivAt ℘'[L] (deriv ℘'[L] z) z := by
    have h := (L.analyticOnNhd_weierstrassP z hz).deriv
    rw [L.deriv_weierstrassP] at h
    exact h.differentiableAt.hasDerivAt
  have h2 := hasDerivAt_iff_tendsto_slope.mp hd
  refine (h2.div h1 hp).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hv' : v - z ≠ 0 := sub_ne_zero.mpr hv
  rw [Pi.div_apply, slope_def_field, slope_def_field, div_div_div_cancel_right₀ hv',
      ← neg_sub (℘'[L] v), ← neg_sub (℘[L] v), neg_div_neg_eq]

/-- A continuous function vanishing off the lattice vanishes everywhere. -/
private lemma eq_zero_of_continuous_of_eq_zero_off_lattice (L : PeriodPair) {g : ℂ → ℂ}
    (hg : Continuous g)
    (h : ∀ x, x ∉ L.lattice → g x = 0) (x : ℂ) : g x = 0 := by
  have hev : ∀ᶠ y in 𝓝[≠] x, g y = 0 := by
    filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds x),
      self_mem_nhdsWithin] with y h1 h2
    exact h y (fun hm => h1 ⟨hm, h2⟩)
  exact tendsto_nhds_unique (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' (hev.mono fun y hy => hy.symm))

end Addition
/-- DLMF 23.10.1: `℘(u + v) = ¼((℘'(u) - ℘'(v))/(℘(u) - ℘(v)))² - ℘(u) - ℘(v)` for
`u, v, u ± v ∉ 𝕃`. -/
@[dlmf 23.10.E1]
theorem weierstrassP_add (L : PeriodPair) {u v : ℂ} (hu : u ∉ L.lattice) (hv : v ∉ L.lattice)
    (huv : u + v ∉ L.lattice) (huv' : u - v ∉ L.lattice) :
    ℘[L] (u + v) = 1 / 4 * ((℘'[L] u - ℘'[L] v) / (℘[L] u - ℘[L] v)) ^ 2 - ℘[L] u - ℘[L] v := by
  exact weierstrassP_add_of_not_mem L hu hv huv huv'

/-- DLMF 23.10.2: `ζ(u + v) = ζ(u) + ζ(v) + ½(ζ''(u) - ζ''(v))/(ζ'(u) - ζ'(v))` for
`u, v, u ± v ∉ 𝕃`. -/
@[dlmf 23.10.E2]
theorem weierstrassZeta_add (L : PeriodPair) {u v : ℂ} (hu : u ∉ L.lattice) (hv : v ∉ L.lattice)
    (huv : u + v ∉ L.lattice) (huv' : u - v ∉ L.lattice) :
    weierstrassZeta L (u + v) = weierstrassZeta L u + weierstrassZeta L v +
      1 / 2 * ((deriv (deriv (weierstrassZeta L)) u - deriv (deriv (weierstrassZeta L)) v) /
        (deriv (weierstrassZeta L) u - deriv (weierstrassZeta L) v)) := by
  rw [deriv_deriv_weierstrassZeta L hu, deriv_deriv_weierstrassZeta L hv,
      deriv_weierstrassZeta L hu,
    deriv_weierstrassZeta L hv, (weierstrassP_ne_and_weierstrassZeta_add L hu hv huv huv').2,
        neg_sub_neg, neg_sub_neg,
    ← neg_sub (℘'[L] u), ← neg_sub (℘[L] u), neg_div_neg_eq]

/-- DLMF 23.10.3: `σ(u + v)σ(u - v)/(σ²(u)σ²(v)) = ℘(v) - ℘(u)` for `u, v ∉ 𝕃`. -/
@[dlmf 23.10.E3]
theorem weierstrassSigma_add_mul_sub (L : PeriodPair) {u v : ℂ} (hu : u ∉ L.lattice)
    (hv : v ∉ L.lattice) :
    weierstrassSigma L (u + v) * weierstrassSigma L (u - v) /
        (weierstrassSigma L u ^ 2 * weierstrassSigma L v ^ 2) = ℘[L] v - ℘[L] u := by
  have hσu : weierstrassSigma L u ≠ 0 := (weierstrassSigma_eq_zero_iff L).not.mpr hu
  have hσv : weierstrassSigma L v ≠ 0 := (weierstrassSigma_eq_zero_iff L).not.mpr hv
  rw [div_eq_iff (by positivity), weierstrassSigma_add_mul_sub_of_not_mem L hu hv]
  ring

/-- DLMF 23.10.4: the three-term identity
`σ(u+v)σ(u-v)σ(x+y)σ(x-y) + σ(v+x)σ(v-x)σ(u+y)σ(u-y) + σ(x+u)σ(x-u)σ(v+y)σ(v-y) = 0`. -/
@[dlmf 23.10.E4]
theorem weierstrassSigma_three_term (L : PeriodPair) (u v x y : ℂ) :
    weierstrassSigma L (u + v) * weierstrassSigma L (u - v) * weierstrassSigma L (x + y) *
          weierstrassSigma L (x - y) +
        weierstrassSigma L (v + x) * weierstrassSigma L (v - x) * weierstrassSigma L (u + y) *
          weierstrassSigma L (u - y) +
        weierstrassSigma L (x + u) * weierstrassSigma L (x - u) * weierstrassSigma L (v + y) *
          weierstrassSigma L (v - y) = 0 := by
  set σ := weierstrassSigma L with hσ
  have hc : Continuous σ := (differentiable_weierstrassSigma L).continuous
  set E : ℂ → ℂ → ℂ → ℂ → ℂ := fun u v x y =>
    σ (u + v) * σ (u - v) * σ (x + y) * σ (x - y) + σ (v + x) * σ (v - x) * σ (u + y) * σ (u - y) +
      σ (x + u) * σ (x - u) * σ (v + y) * σ (v - y) with hE
  have h0 : ∀ u v x y, u ∉ L.lattice → v ∉ L.lattice → x ∉ L.lattice → y ∉ L.lattice →
      E u v x y = 0 := by
    intro u v x y hu hv hx hy
    have e1 := weierstrassSigma_add_mul_sub_of_not_mem L hu hv
    have e2 := weierstrassSigma_add_mul_sub_of_not_mem L hx hy
    have e3 := weierstrassSigma_add_mul_sub_of_not_mem L hv hx
    have e4 := weierstrassSigma_add_mul_sub_of_not_mem L hu hy
    have e5 := weierstrassSigma_add_mul_sub_of_not_mem L hx hu
    have e6 := weierstrassSigma_add_mul_sub_of_not_mem L hv hy
    rw [← hσ] at e1 e2 e3 e4 e5 e6
    simp only [hE]
    linear_combination σ (x + y) * σ (x - y) * e1 +
      (℘[L] v - ℘[L] u) * σ u ^ 2 * σ v ^ 2 * e2 + σ (u + y) * σ (u - y) * e3 +
      (℘[L] x - ℘[L] v) * σ v ^ 2 * σ x ^ 2 * e4 + σ (v + y) * σ (v - y) * e5 +
      (℘[L] u - ℘[L] x) * σ x ^ 2 * σ u ^ 2 * e6
  have h1 : ∀ u v x y, u ∉ L.lattice → v ∉ L.lattice → x ∉ L.lattice → E u v x y = 0 :=
    fun u v x y hu hv hx => eq_zero_of_continuous_of_eq_zero_off_lattice L (g := fun y => E u v x y)
      (by simp only [hE]; fun_prop) (fun y hy => h0 u v x y hu hv hx hy) y
  have h2 : ∀ u v x y, u ∉ L.lattice → v ∉ L.lattice → E u v x y = 0 :=
    fun u v x y hu hv => eq_zero_of_continuous_of_eq_zero_off_lattice L (g := fun x => E u v x y)
      (by simp only [hE]; fun_prop) (fun x hx => h1 u v x y hu hv hx) x
  have h3 : ∀ u v x y, u ∉ L.lattice → E u v x y = 0 :=
    fun u v x y hu => eq_zero_of_continuous_of_eq_zero_off_lattice L (g := fun v => E u v x y)
      (by simp only [hE]; fun_prop) (fun v hv => h2 u v x y hu hv) v
  exact eq_zero_of_continuous_of_eq_zero_off_lattice L (g := fun u => E u v x y)
    (by simp only [hE]; fun_prop) (fun u hu => h3 u v x y hu) u

/-- DLMF 23.10.5: if `u + v + w = 0` (`u, v, w ∉ 𝕃`), then
`det [[1, ℘(u), ℘'(u)], [1, ℘(v), ℘'(v)], [1, ℘(w), ℘'(w)]] = 0`. -/
@[dlmf 23.10.E5]
theorem weierstrassP_det_eq_zero (L : PeriodPair) {u v w : ℂ} (hu : u ∉ L.lattice)
    (hv : v ∉ L.lattice) (hw : w ∉ L.lattice) (h : u + v + w = 0) :
    Matrix.det !![1, ℘[L] u, ℘'[L] u; 1, ℘[L] v, ℘'[L] v; 1, ℘[L] w, ℘'[L] w] = 0 := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.tail_cons]
  have hw' : w = -(u + v) := by linear_combination h
  by_cases huv' : u - v ∈ L.lattice
  · have e1 : ℘[L] u = ℘[L] v := by
      rw [show u = v + (u - v) by ring, L.weierstrassP_add_coe v ⟨u - v, huv'⟩]
    have e2 : ℘'[L] u = ℘'[L] v := by
      rw [show u = v + (u - v) by ring, L.derivWeierstrassP_add_coe v ⟨u - v, huv'⟩]
    rw [e1, e2]; ring
  have huv : u + v ∉ L.lattice := fun hm => hw (by rw [hw']; exact neg_mem hm)
  have hne : ℘[L] u - ℘[L] v ≠ 0 :=
      sub_ne_zero.mpr (weierstrassP_ne_and_weierstrassZeta_add L hu hv huv huv').1
  have hP : ℘[L] w = ℘[L] (u + v) := by rw [hw', L.weierstrassP_neg]
  have hD : ℘'[L] w = -℘'[L] (u + v) := by rw [hw', L.derivWeierstrassP_neg]
  rw [hP, hD, derivWeierstrassP_add L hu hv huv huv']
  field_simp
  ring

/-- DLMF 23.10.6: if `u + v + w = 0` (`u, v, w ∉ 𝕃`), then
`(ζ(u) + ζ(v) + ζ(w))² + ζ'(u) + ζ'(v) + ζ'(w) = 0`. -/
@[dlmf 23.10.E6]
theorem weierstrassZeta_sum_sq (L : PeriodPair) {u v w : ℂ} (hu : u ∉ L.lattice)
    (hv : v ∉ L.lattice) (hw : w ∉ L.lattice) (h : u + v + w = 0) :
    (weierstrassZeta L u + weierstrassZeta L v + weierstrassZeta L w) ^ 2 +
      deriv (weierstrassZeta L) u + deriv (weierstrassZeta L) v +
        deriv (weierstrassZeta L) w = 0 := by
  by_cases huv' : u - v ∉ L.lattice
  · exact weierstrassZeta_sum_sq_of_sub_not_mem L hu hv hw h huv'
  rw [not_not] at huv'
  set ζ := weierstrassZeta L
  set f : ℂ → ℂ := fun y => (ζ u + ζ y + ζ (-u - y)) ^ 2 + deriv ζ u + deriv ζ y +
    deriv ζ (-u - y) with hf
  have hw' : w = -u - v := by linear_combination h
  have hopen : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have hcz : ∀ x, x ∉ L.lattice → ContinuousAt ζ x := fun x hx =>
    (hasDerivAt_weierstrassZeta L hx).continuousAt
  have hcd : ∀ x, x ∉ L.lattice → ContinuousAt (deriv ζ) x := fun x hx =>
    ((hasDerivAt_weierstrassP L hx).continuousAt.neg).congr
        (deriv_weierstrassZeta_eventuallyEq L hx).symm
  have hc1 : Continuous fun y : ℂ => -u - y := by fun_prop
  have hcont : ContinuousAt f v := by
    have h1 : ContinuousAt (fun y => ζ (-u - y)) v :=
      (hcz _ (by rwa [← hw'])).comp hc1.continuousAt
    have h2 : ContinuousAt (fun y => deriv ζ (-u - y)) v :=
      (hcd _ (by rwa [← hw'])).comp hc1.continuousAt
    exact ((((continuousAt_const.add (hcz v hv)).add h1).pow 2).add continuousAt_const |>.add
      (hcd v hv)).add h2
  have hev : ∀ᶠ y in 𝓝[≠] v, f y = 0 := by
    have hA := hopen.mem_nhds hv
    have hB := hc1.continuousAt.preimage_mem_nhds
        (hopen.mem_nhds (by rwa [← hw'] : -u - v ∉ L.lattice))
    have hC := (continuous_const.sub continuous_id : Continuous fun y : ℂ => u - y).continuousAt
      |>.preimage_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds (u - v))
    filter_upwards [nhdsWithin_le_nhds hA, nhdsWithin_le_nhds hB, nhdsWithin_le_nhds hC,
      self_mem_nhdsWithin] with y hy1 hy2 hy3 hy4
    refine weierstrassZeta_sum_sq_of_sub_not_mem L hu hy1 hy2 (by ring) ?_
    intro hm
    apply hy3
    refine ⟨hm, ?_⟩
    intro he
    exact hy4 (by simpa using he)
  have := tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' (hev.mono fun y hy => hy.symm))
  simpa [hf, hw'] using this

/-! ### Duplication formulas (§23.10(ii)) -/

/-- DLMF 23.10.7: `℘(2z) = -2℘(z) + ¼(℘''(z)/℘'(z))²` for `z, 2z ∉ 𝕃`. -/
@[dlmf 23.10.E7]
theorem weierstrassP_two_mul (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice)
    (h2z : 2 * z ∉ L.lattice) :
    ℘[L] (2 * z) = -2 * ℘[L] z + 1 / 4 * (deriv ℘'[L] z / ℘'[L] z) ^ 2 := by
  have hp := derivWeierstrassP_ne_zero_of_two_mul_not_mem L hz h2z
  have hzz : z + z ∉ L.lattice := by rwa [← two_mul]
  have hopen : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have hB := (continuous_const.add continuous_id : Continuous fun y : ℂ => z + y).continuousAt
    |>.preimage_mem_nhds (hopen.mem_nhds hzz)
  have hev : ∀ᶠ v in 𝓝[≠] z, ℘[L] (z + v) =
      1 / 4 * ((℘'[L] z - ℘'[L] v) / (℘[L] z - ℘[L] v)) ^ 2 - ℘[L] z - ℘[L] v := by
    filter_upwards [eventually_not_mem_lattice_sub_nhdsNE L hz, nhdsWithin_le_nhds hB]
        with v ⟨h1, h2⟩ h3
    exact weierstrassP_add_of_not_mem L hz h1 h3 h2
  have hl : Tendsto (fun v => ℘[L] (z + v)) (𝓝[≠] z) (𝓝 (℘[L] (z + z))) :=
    (((hasDerivAt_weierstrassP L hzz).continuousAt.comp
      (continuous_const.add continuous_id).continuousAt).tendsto).mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun v => 1 / 4 * ((℘'[L] z - ℘'[L] v) / (℘[L] z - ℘[L] v)) ^ 2 -
      ℘[L] z - ℘[L] v) (𝓝[≠] z)
      (𝓝 (1 / 4 * (deriv ℘'[L] z / ℘'[L] z) ^ 2 - ℘[L] z - ℘[L] z)) :=
    ((((tendsto_derivWeierstrassP_difference_quotient L hz hp).pow 2).const_mul _).sub_const _).sub
      ((hasDerivAt_weierstrassP L hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  rw [two_mul, tendsto_nhds_unique hl (hr.congr' (hev.mono fun v hv => hv.symm))]
  ring

namespace HalfPeriods

variable (H : HalfPeriods)

/-- DLMF 23.10.8 and its cyclic permutations: for `z, 2z ∉ 𝕃`,
`(℘(2z) - e₁)℘'²(z) = ((℘(z) - e₁)² - (e₁ - e₂)(e₁ - e₃))²`, and likewise with
`(e₁, e₂, e₃)` permuted cyclically. -/
@[dlmf 23.10.E8]
theorem weierstrassP_two_mul_sub_e {z : ℂ} (hz : z ∉ H.lattice) (h2z : 2 * z ∉ H.lattice) :
    (H.weierstrassP (2 * z) - H.e 1) * H.derivWeierstrassP z ^ 2 =
        ((H.weierstrassP z - H.e 1) ^ 2 - (H.e 1 - H.e 2) * (H.e 1 - H.e 3)) ^ 2 ∧
      (H.weierstrassP (2 * z) - H.e 2) * H.derivWeierstrassP z ^ 2 =
        ((H.weierstrassP z - H.e 2) ^ 2 - (H.e 2 - H.e 3) * (H.e 2 - H.e 1)) ^ 2 ∧
      (H.weierstrassP (2 * z) - H.e 3) * H.derivWeierstrassP z ^ 2 =
        ((H.weierstrassP z - H.e 3) ^ 2 - (H.e 3 - H.e 1) * (H.e 3 - H.e 2)) ^ 2 := by
  have hp := derivWeierstrassP_ne_zero_of_two_mul_not_mem H.periodPair hz h2z
  have h7 := weierstrassP_two_mul H.periodPair hz h2z
  rw [deriv_derivWeierstrassP H.periodPair hz] at h7
  have hsq := H.derivWeierstrassP_sq_eq_prod hz
  have hg := H.g₂_eq_e.1
  have hs := H.e_sum
  simp only [HalfPeriods.weierstrassP, HalfPeriods.derivWeierstrassP, HalfPeriods.g₂] at *
  have key : ∀ c : ℂ, (℘[H.periodPair] (2 * z) - c) * ℘'[H.periodPair] z ^ 2 =
      (-2 * ℘[H.periodPair] z - c) * ℘'[H.periodPair] z ^ 2 +
        1 / 4 * (6 * ℘[H.periodPair] z ^ 2 - H.periodPair.g₂ / 2) ^ 2 := by
    intro c; rw [h7]; field_simp; ring
  rw [key, key, key, hsq, hg]
  have h3 : H.e 3 = -H.e 1 - H.e 2 := by linear_combination hs
  rw [h3]
  refine ⟨by ring, by ring, by ring⟩

end HalfPeriods

/-- DLMF 23.10.9: `ζ(2z) = 2ζ(z) + ½ζ'''(z)/ζ''(z)` for `z, 2z ∉ 𝕃`. -/
@[dlmf 23.10.E9]
theorem weierstrassZeta_two_mul (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice)
    (h2z : 2 * z ∉ L.lattice) :
    weierstrassZeta L (2 * z) = 2 * weierstrassZeta L z +
      1 / 2 * (deriv (deriv (deriv (weierstrassZeta L))) z /
        deriv (deriv (weierstrassZeta L)) z) := by
  have hp := derivWeierstrassP_ne_zero_of_two_mul_not_mem L hz h2z
  have hzz : z + z ∉ L.lattice := by rwa [← two_mul]
  have hopen : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have hB := (continuous_const.add continuous_id : Continuous fun y : ℂ => z + y).continuousAt
    |>.preimage_mem_nhds (hopen.mem_nhds hzz)
  have hev : ∀ᶠ v in 𝓝[≠] z, weierstrassZeta L (z + v) = weierstrassZeta L z +
      weierstrassZeta L v + 1 / 2 * ((℘'[L] z - ℘'[L] v) / (℘[L] z - ℘[L] v)) := by
    filter_upwards [eventually_not_mem_lattice_sub_nhdsNE L hz, nhdsWithin_le_nhds hB]
        with v ⟨h1, h2⟩ h3
    exact (weierstrassP_ne_and_weierstrassZeta_add L hz h1 h3 h2).2
  have hl : Tendsto (fun v => weierstrassZeta L (z + v)) (𝓝[≠] z)
      (𝓝 (weierstrassZeta L (z + z))) :=
    (((hasDerivAt_weierstrassZeta L hzz).continuousAt.comp
      (continuous_const.add continuous_id).continuousAt).tendsto).mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun v => weierstrassZeta L z + weierstrassZeta L v +
      1 / 2 * ((℘'[L] z - ℘'[L] v) / (℘[L] z - ℘[L] v))) (𝓝[≠] z)
      (𝓝 (weierstrassZeta L z + weierstrassZeta L z + 1 / 2 * (deriv ℘'[L] z / ℘'[L] z))) :=
    (tendsto_const_nhds.add
      ((hasDerivAt_weierstrassZeta L hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).add
      ((tendsto_derivWeierstrassP_difference_quotient L hz hp).const_mul _)
  rw [two_mul, tendsto_nhds_unique hl (hr.congr' (hev.mono fun v hv => hv.symm)),
    deriv_deriv_weierstrassZeta L hz,
    (show deriv (deriv (deriv (weierstrassZeta L))) z = -deriv ℘'[L] z by
      rw [deriv_deriv_deriv_weierstrassZeta L hz, deriv_derivWeierstrassP L hz]), neg_div_neg_eq]
  ring

/-- DLMF 23.10.10: `σ(2z) = -℘'(z)σ⁴(z)` for `z ∈ ℂ` (both sides vanish on `𝕃`). -/
@[dlmf 23.10.E10]
theorem weierstrassSigma_two_mul (L : PeriodPair) (z : ℂ) :
    weierstrassSigma L (2 * z) = -℘'[L] z * weierstrassSigma L z ^ 4 := by
  by_cases hz : z ∈ L.lattice
  · have h2 : 2 * z ∈ L.lattice := by rw [two_mul]; exact add_mem hz hz
    rw [weierstrassSigma_eq_zero_of_mem L h2, weierstrassSigma_eq_zero_of_mem L hz]
    ring
  set σ := weierstrassSigma L with hσ
  have hσd : Differentiable ℂ σ := differentiable_weierstrassSigma L
  have hev : ∀ᶠ v in 𝓝[≠] z, σ (z + v) * -(σ (z - v) / (z - v)) =
      slope ℘[L] z v * σ z ^ 2 * σ v ^ 2 := by
    filter_upwards [eventually_not_mem_lattice_sub_nhdsNE L hz, self_mem_nhdsWithin]
        with v ⟨h1, _⟩ h3
    have hv' : z - v ≠ 0 := sub_ne_zero.mpr (Ne.symm h3)
    have hv'' : v - z ≠ 0 := sub_ne_zero.mpr h3
    have := weierstrassSigma_add_mul_sub_of_not_mem L hz h1
    rw [← hσ] at this
    calc σ (z + v) * -(σ (z - v) / (z - v)) = σ (z + v) * σ (z - v) / (v - z) := by
          rw [show v - z = -(z - v) by ring, div_neg_eq_neg_div, mul_neg, mul_div_assoc]
      _ = _ := by rw [this, slope_def_field]; field_simp
  have h0 : Tendsto (fun v => z - v) (𝓝[≠] z) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun y : ℂ => z - y) (𝓝 z) (𝓝 (z - z)) := tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with v hv
      exact sub_ne_zero.mpr (Ne.symm hv)
  have hT2 : Tendsto (fun w => σ w / w) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have := (hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_weierstrassSigma_zero L))
    refine this.congr' (Eventually.of_forall fun w => ?_)
    simp [slope_def_field, hσ, weierstrassSigma_eq_zero_of_mem L (zero_mem _)]
  have hl : Tendsto (fun v => σ (z + v) * -(σ (z - v) / (z - v))) (𝓝[≠] z)
      (𝓝 (σ (z + z) * -1)) :=
    ((((hσd.continuous.comp (continuous_const.add continuous_id)).tendsto z)).mono_left
      nhdsWithin_le_nhds).mul (hT2.comp h0).neg
  have hr : Tendsto (fun v => slope ℘[L] z v * σ z ^ 2 * σ v ^ 2) (𝓝[≠] z)
      (𝓝 (℘'[L] z * σ z ^ 2 * σ z ^ 2)) :=
    ((hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_weierstrassP L hz)).mul_const _).mul
      (((hσd.continuous.tendsto z).pow 2).mono_left nhdsWithin_le_nhds)
  have := tendsto_nhds_unique hl (hr.congr' (hev.mono fun v hv => hv.symm))
  rw [two_mul]
  linear_combination -this

/-! ### `n`-tuple formulas (§23.10(iii)) -/

namespace HalfPeriods

variable (H : HalfPeriods)

/-- The `n²` shifts `2jω₁/n + 2ℓω₃/n`, `0 ≤ j, ℓ < n`. -/
def divisionPoint (n j l : ℕ) : ℂ := 2 * j / n * H.ω₁ + 2 * l / n * H.ω₃

private lemma natCast_mul_divisionPoint {n : ℕ} (hn : n ≠ 0) (j l : ℕ) :
    (n : ℂ) * H.divisionPoint n j l = 2 * j * H.ω₁ + 2 * l * H.ω₃ := by
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  unfold divisionPoint; field_simp

private lemma mem_of_add_divisionPoint_mem {n : ℕ} (hn : n ≠ 0) {z : ℂ} (j l : ℕ)
    (h : z + H.divisionPoint n j l ∈ H.lattice) : (n : ℂ) * z ∈ H.lattice := by
  have h1 : (n : ℂ) * (z + H.divisionPoint n j l) ∈ H.lattice := by
    have := Submodule.smul_mem H.lattice (n : ℤ) h
    rw [mul_add]; simpa [zsmul_eq_mul, mul_add] using this
  have h2 : 2 * (j : ℂ) * H.ω₁ + 2 * l * H.ω₃ ∈ H.lattice :=
    H.mem_lattice_iff.mpr ⟨j, l, by push_cast; ring⟩
  have := sub_mem h1 h2
  rw [mul_add, natCast_mul_divisionPoint H hn] at this
  simpa using this

private lemma add_divisionPoint_not_mem {n : ℕ} (hn : n ≠ 0) {z : ℂ}
    (hz : (n : ℂ) * z ∉ H.lattice) (j l : ℕ) : z + H.divisionPoint n j l ∉ H.lattice :=
  fun h => hz (mem_of_add_divisionPoint_mem H hn j l h)

/-- Division points differing by a lattice vector coincide. -/
private lemma divisionPoint_sub_mem {n : ℕ} (hn : n ≠ 0) {j l j' l' : ℕ} (hj : j < n)
    (hl : l < n) (hj' : j' < n) (hl' : l' < n)
    (h : H.divisionPoint n j l - H.divisionPoint n j' l' ∈ H.lattice) : j = j' ∧ l = l' := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have e : H.divisionPoint n j l - H.divisionPoint n j' l' =
      (((j - j' : ℤ) : ℚ) / (n : ℤ) : ℚ) * H.periodPair.ω₁ +
        (((l - l' : ℤ) : ℚ) / (n : ℤ) : ℚ) * H.periodPair.ω₂ := by
    simp only [divisionPoint, periodPair_ω₁, periodPair_ω₂]
    push_cast; field_simp; ring
  rw [e, PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice,
    Rat.den_div_intCast_eq_one_iff _ _ (by exact_mod_cast hn),
    Rat.den_div_intCast_eq_one_iff _ _ (by exact_mod_cast hn)] at h
  have h1 := Int.eq_zero_of_abs_lt_dvd h.1 (by rw [abs_lt]; omega)
  have h2 := Int.eq_zero_of_abs_lt_dvd h.2 (by rw [abs_lt]; omega)
  omega

/-- For `nx ∈ 𝕃` exactly one shift `x + 2jω₁/n + 2ℓω₃/n` lies in `𝕃`. -/
private lemma exists_unique_add_divisionPoint_mem {n : ℕ} (hn : n ≠ 0) {x : ℂ}
    (hx : (n : ℂ) * x ∈ H.lattice) :
    ∃ j₀ < n, ∃ l₀ < n, x + H.divisionPoint n j₀ l₀ ∈ H.lattice ∧
      ∀ j < n, ∀ l < n, x + H.divisionPoint n j l ∈ H.lattice → j = j₀ ∧ l = l₀ := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have hnpos : (0 : ℤ) < n := by omega
  obtain ⟨a, b, hab⟩ := H.mem_lattice_iff.mp hx
  set j₀ := ((-a) % (n : ℤ)).toNat with hj₀
  set l₀ := ((-b) % (n : ℤ)).toNat with hl₀
  have ej : (j₀ : ℤ) = -a - n * ((-a) / n) := by
    rw [hj₀, Int.toNat_of_nonneg (Int.emod_nonneg _ hnz), Int.emod_def]
  have el : (l₀ : ℤ) = -b - n * ((-b) / n) := by
    rw [hl₀, Int.toNat_of_nonneg (Int.emod_nonneg _ hnz), Int.emod_def]
  have hj₀n : j₀ < n := by
    have := Int.emod_lt_of_pos (-a) hnpos
    have h0 := Int.emod_nonneg (-a) hnz
    omega
  have hl₀n : l₀ < n := by
    have := Int.emod_lt_of_pos (-b) hnpos
    have h0 := Int.emod_nonneg (-b) hnz
    omega
  have hmem : x + H.divisionPoint n j₀ l₀ ∈ H.lattice := by
    refine H.mem_lattice_iff.mpr ⟨-((-a) / n), -((-b) / n), ?_⟩
    apply mul_left_cancel₀ hn'
    rw [mul_add, natCast_mul_divisionPoint H hn, hab]
    have ej' : ((j₀ : ℤ) : ℂ) = -a - n * (((-a) / n : ℤ) : ℂ) := by
      rw [ej]; push_cast; ring
    have el' : ((l₀ : ℤ) : ℂ) = -b - n * (((-b) / n : ℤ) : ℂ) := by
      rw [el]; push_cast; ring
    push_cast at ej' el' ⊢
    rw [ej', el']; ring
  refine ⟨j₀, hj₀n, l₀, hl₀n, hmem, fun j hj l hl h => ?_⟩
  refine divisionPoint_sub_mem H hn hj hl hj₀n hl₀n ?_
  simpa using sub_mem h hmem

/-- `∑_{j,ℓ} ζ(z + 2jω₁/n + 2ℓω₃/n) - nζ(nz)`, the difference in DLMF 23.10.12. -/
private def nTupleZetaDiff (n : ℕ) (z : ℂ) : ℂ :=
  (∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n, H.weierstrassZeta (z + H.divisionPoint n j l)) -
    n * H.weierstrassZeta (n * z)

private lemma analyticAt_nTupleZetaDiff {n : ℕ} (hn : n ≠ 0) (x : ℂ) :
    AnalyticAt ℂ (H.nTupleZetaDiff n) x := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hζ := analyticOnNhd_weierstrassZeta H.periodPair
  by_cases hx : (n : ℂ) * x ∈ H.lattice
  · obtain ⟨j₀, hj₀, l₀, hl₀, hmem, huniq⟩ := exists_unique_add_divisionPoint_mem H hn hx
    set w := x + H.divisionPoint n j₀ l₀
    have heq : H.nTupleZetaDiff n = fun z =>
        (∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n,
          (H.weierstrassZeta (z + H.divisionPoint n j l) -
            if j = j₀ ∧ l = l₀ then 1 / (z + H.divisionPoint n j l - w) else 0)) -
        n * (H.weierstrassZeta (n * z) - 1 / (n * z - n * x)) := by
      funext z
      simp only [nTupleZetaDiff, Finset.sum_sub_distrib]
      have hs : (∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n,
          if j = j₀ ∧ l = l₀ then 1 / (z + H.divisionPoint n j l - w) else 0) =
          1 / (z - x) := by
        rw [Finset.sum_eq_single j₀, Finset.sum_eq_single l₀]
        · simp [w]
        · intro l _ hl; simp [hl]
        · intro h; exact absurd (Finset.mem_range.mpr hl₀) h
        · intro j _ hj; simp [hj]
        · intro h; exact absurd (Finset.mem_range.mpr hj₀) h
      rw [hs]
      have : (n : ℂ) * (1 / (n * z - n * x)) = 1 / (z - x) := by
        rw [← mul_sub]
        by_cases hzx : z - x = 0
        · simp [hzx]
        · field_simp
      rw [mul_sub, this]; ring
    rw [heq]
    refine AnalyticAt.sub (Finset.analyticAt_fun_sum _ fun j hj => Finset.analyticAt_fun_sum _
      fun l hl => ?_) (analyticAt_const.mul ?_)
    · by_cases hjl : j = j₀ ∧ l = l₀
      · obtain ⟨rfl, rfl⟩ := hjl
        simp only [and_self, ite_true]
        have := (analyticAt_weierstrassZeta_sub H.periodPair hmem).comp
          (f := fun z => z + H.divisionPoint n j l) (by fun_prop)
        exact this
      · simp only [hjl, ite_false, sub_zero]
        have hnm : x + H.divisionPoint n j l ∉ H.lattice := fun h =>
          hjl (huniq j (Finset.mem_range.mp hj) l (Finset.mem_range.mp hl) h)
        exact (hζ _ hnm).comp (f := fun z => z + H.divisionPoint n j l) (by fun_prop)
    · have h1 := (analyticAt_weierstrassZeta_sub H.periodPair hx).comp
        (f := fun z => (n : ℂ) * z) (by fun_prop)
      exact h1
  · refine AnalyticAt.sub (Finset.analyticAt_fun_sum _ fun j _ => Finset.analyticAt_fun_sum _
      fun l _ => ?_) (analyticAt_const.mul ?_)
    · exact (hζ _ (add_divisionPoint_not_mem H hn hx j l)).comp
        (f := fun z => z + H.divisionPoint n j l) (by fun_prop)
    · exact (hζ _ hx).comp (f := fun z => (n : ℂ) * z) (by fun_prop)

private lemma sum_range_succ_shift (g : ℕ → ℂ) (n : ℕ) :
    ∑ j ∈ Finset.range n, g (j + 1) = ∑ j ∈ Finset.range n, g j + (g n - g 0) := by
  have h1 := Finset.sum_range_succ' g n
  have h2 := Finset.sum_range_succ g n
  linear_combination h2 - h1

private lemma weierstrassZeta_add_two_mul_ω₁' {y : ℂ} (hy : y ∉ H.lattice) :
    H.weierstrassZeta (y + 2 * H.ω₁) = H.weierstrassZeta y + 2 * H.eta 1 :=
  H.weierstrassZeta_add_two_mul_halfPeriod hy (j := 1) (by simp)

private lemma weierstrassZeta_add_two_mul_ω₃' {y : ℂ} (hy : y ∉ H.lattice) :
    H.weierstrassZeta (y + 2 * H.ω₃) = H.weierstrassZeta y + 2 * H.eta 3 :=
  H.weierstrassZeta_add_two_mul_halfPeriod hy (j := 3) (by simp)

/-- The lattice `𝕃/n` of the division points. -/
private abbrev divisionPeriodPair (n : ℕ) (hn : n ≠ 0) : PeriodPair :=
  scalePeriodPair (1 / (n : ℂ)) (by simp; exact_mod_cast hn) H.periodPair

private lemma mem_divisionPeriodPair_iff {n : ℕ} (hn : n ≠ 0) {z : ℂ} :
    z ∈ (H.divisionPeriodPair n hn).lattice ↔ (n : ℂ) * z ∈ H.lattice := by
  rw [mem_scalePeriodPair_lattice_iff, div_div_eq_mul_div, div_one, mul_comm]

private lemma nTupleZetaDiff_add_ω₁_of_not_mem {n : ℕ} (hn : n ≠ 0) {z : ℂ}
    (hz : (n : ℂ) * z ∉ H.lattice) :
    H.nTupleZetaDiff n (z + 2 * H.ω₁ / n) = H.nTupleZetaDiff n z := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  set g : ℕ → ℂ := fun j => ∑ l ∈ Finset.range n, H.weierstrassZeta (z + H.divisionPoint n j l)
  have hg : ∀ j, ∑ l ∈ Finset.range n,
      H.weierstrassZeta (z + 2 * H.ω₁ / n + H.divisionPoint n j l) = g (j + 1) := by
    intro j; refine Finset.sum_congr rfl fun l _ => ?_
    congr 1; simp only [divisionPoint]; push_cast; ring
  have hgn : g n = g 0 + n * (2 * H.eta 1) := by
    simp only [g]
    have hc : (n : ℂ) * (2 * H.eta 1) = ∑ _l ∈ Finset.range n, 2 * H.eta 1 := by simp
    rw [hc, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← weierstrassZeta_add_two_mul_ω₁' H (add_divisionPoint_not_mem H hn hz 0 l)]
    congr 1; simp only [divisionPoint]; field_simp; ring
  have hnz : (n : ℂ) * (z + 2 * H.ω₁ / n) = n * z + 2 * H.ω₁ := by field_simp
  simp only [nTupleZetaDiff, hg, hnz, weierstrassZeta_add_two_mul_ω₁' H hz]
  rw [sum_range_succ_shift g n, hgn]
  simp only [g]; ring

private lemma nTupleZetaDiff_add_ω₃_of_not_mem {n : ℕ} (hn : n ≠ 0) {z : ℂ}
    (hz : (n : ℂ) * z ∉ H.lattice) :
    H.nTupleZetaDiff n (z + 2 * H.ω₃ / n) = H.nTupleZetaDiff n z := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hinner : ∀ j, ∑ l ∈ Finset.range n,
      H.weierstrassZeta (z + 2 * H.ω₃ / n + H.divisionPoint n j l) =
      ∑ l ∈ Finset.range n, H.weierstrassZeta (z + H.divisionPoint n j l) + 2 * H.eta 3 := by
    intro j
    set g : ℕ → ℂ := fun l => H.weierstrassZeta (z + H.divisionPoint n j l)
    have hg : ∀ l, H.weierstrassZeta (z + 2 * H.ω₃ / n + H.divisionPoint n j l) = g (l + 1) := by
      intro l; simp only [g]; congr 1; simp only [divisionPoint]; push_cast; ring
    have hgn : g n = g 0 + 2 * H.eta 3 := by
      simp only [g]
      rw [← weierstrassZeta_add_two_mul_ω₃' H (add_divisionPoint_not_mem H hn hz j 0)]
      congr 1; simp only [divisionPoint]; field_simp; ring
    simp only [hg]
    rw [sum_range_succ_shift g n, hgn]; ring
  have hnz : (n : ℂ) * (z + 2 * H.ω₃ / n) = n * z + 2 * H.ω₃ := by field_simp
  simp only [nTupleZetaDiff, hinner, hnz, weierstrassZeta_add_two_mul_ω₃' H hz,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

private lemma nTupleZetaDiff_periodic {n : ℕ} (hn : n ≠ 0) {t : ℂ}
    (ht : t = 2 * H.ω₁ / n ∨ t = 2 * H.ω₃ / n) :
    Function.Periodic (H.nTupleZetaDiff n) t := by
  intro z
  have hc : Continuous fun z => H.nTupleZetaDiff n (z + t) - H.nTupleZetaDiff n z :=
    ((continuous_iff_continuousAt.mpr fun x => (analyticAt_nTupleZetaDiff H hn x).continuousAt)
      |>.comp (continuous_id.add continuous_const)).sub
      (continuous_iff_continuousAt.mpr fun x => (analyticAt_nTupleZetaDiff H hn x).continuousAt)
  have := eq_zero_of_continuous_of_eq_zero_off_lattice (H.divisionPeriodPair n hn) hc
    (fun x hx => by
      rw [mem_divisionPeriodPair_iff] at hx
      rcases ht with rfl | rfl
      · rw [nTupleZetaDiff_add_ω₁_of_not_mem H hn hx, sub_self]
      · rw [nTupleZetaDiff_add_ω₃_of_not_mem H hn hx, sub_self]) z
  exact sub_eq_zero.mp this

private lemma exists_nTupleZetaDiff_eq_const {n : ℕ} (hn : n ≠ 0) :
    ∃ c, ∀ z, H.nTupleZetaDiff n z = c := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  set L' := H.divisionPeriodPair n hn
  have h1 : Function.Periodic (H.nTupleZetaDiff n) L'.ω₁ := by
    convert nTupleZetaDiff_periodic H hn (Or.inl rfl) using 1
    simp [L', scalePeriodPair]; ring
  have h2 : Function.Periodic (H.nTupleZetaDiff n) L'.ω₂ := by
    convert nTupleZetaDiff_periodic H hn (Or.inr rfl) using 1
    simp [L', scalePeriodPair]; ring
  obtain ⟨c, hc⟩ := exists_eq_const_of_periodic_of_order_nonneg L'
    (fun x => (analyticAt_nTupleZetaDiff H hn x).meromorphicAt)
    (fun z l hl => by
      obtain ⟨m, k, rfl⟩ := PeriodPair.mem_lattice.mp hl
      exact ((h1.int_mul m).add_period (h2.int_mul k)) z)
    (fun x => (analyticAt_nTupleZetaDiff H hn x).meromorphicOrderAt_nonneg)
  exact ⟨c, fun z => hc z (analyticAt_nTupleZetaDiff H hn z)⟩

private lemma weierstrassZeta_add_two_mul_ω₁_add_ω₃ {y : ℂ} (hy : y ∉ H.lattice) :
    H.weierstrassZeta (y + 2 * H.ω₁ + 2 * H.ω₃) =
      H.weierstrassZeta y + 2 * H.eta 1 + 2 * H.eta 3 := by
  have hy' : y + 2 * H.ω₁ ∉ H.lattice := fun h => hy (by
    simpa using sub_mem h H.two_mul_ω₁_mem)
  rw [weierstrassZeta_add_two_mul_ω₃' H hy', weierstrassZeta_add_two_mul_ω₁' H hy]

private lemma sum_weierstrassZeta_sub_divisionPoint {n : ℕ} (hn : n ≠ 0) {z : ℂ}
    (hz : (n : ℂ) * z ∉ H.lattice) :
    ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n, H.weierstrassZeta (z - H.divisionPoint n j l) =
      ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n,
        H.weierstrassZeta (z + (2 * H.ω₁ / n + 2 * H.ω₃ / n) + H.divisionPoint n j l) -
      n ^ 2 * (2 * H.eta 1 + 2 * H.eta 3) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  set t := 2 * H.ω₁ / n + 2 * H.ω₃ / n
  have hzt : (n : ℂ) * (z + t) ∉ H.lattice := by
    rw [show (n : ℂ) * (z + t) = n * z + 2 * H.ω₁ + 2 * H.ω₃ by simp only [t]; field_simp; ring]
    intro h; apply hz
    convert sub_mem (sub_mem h H.two_mul_ω₁_mem) H.two_mul_ω₃_mem using 1; ring
  have key : ∀ j ∈ Finset.range n, ∀ l ∈ Finset.range n,
      H.weierstrassZeta (z - H.divisionPoint n j l) =
      H.weierstrassZeta (z + t + H.divisionPoint n (n - 1 - j) (n - 1 - l)) -
        (2 * H.eta 1 + 2 * H.eta 3) := by
    intro j hj l hl
    have hj' := Finset.mem_range.mp hj
    have hl' := Finset.mem_range.mp hl
    set y := z - H.divisionPoint n j l
    have e : z + t + H.divisionPoint n (n - 1 - j) (n - 1 - l) = y + 2 * H.ω₁ + 2 * H.ω₃ := by
      simp only [y, t, divisionPoint]
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega),
        Nat.cast_sub (by omega)]
      field_simp; ring
    have hy : y ∉ H.lattice := fun h => add_divisionPoint_not_mem H hn hzt _ _ (by
      rw [e]; exact add_mem (add_mem h H.two_mul_ω₁_mem) H.two_mul_ω₃_mem)
    rw [e, weierstrassZeta_add_two_mul_ω₁_add_ω₃ H hy]; ring
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => key j hj l hl]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Finset.sum_range_reflect (fun j => ∑ l ∈ Finset.range n,
    H.weierstrassZeta (z + t + H.divisionPoint n j (n - 1 - l))) n]
  rw [Finset.sum_congr rfl fun j _ =>
    Finset.sum_range_reflect (fun l => H.weierstrassZeta (z + t + H.divisionPoint n j l)) n]
  ring

private lemma nTupleZetaDiff_eq {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    H.nTupleZetaDiff n z = n * (n - 1) * (H.eta 1 + H.eta 3) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  obtain ⟨c, hc⟩ := exists_nTupleZetaDiff_eq_const H hn
  rw [hc z]
  set z₀ := H.ω₁ / n
  have hω : H.ω₁ ∉ H.lattice := by simpa using H.halfPeriod_notMem (j := 1) (by simp)
  have hz₀ : (n : ℂ) * z₀ ∉ H.lattice := by simp only [z₀]; field_simp; exact hω
  have hz₀' : (n : ℂ) * z₀ = H.ω₁ := by simp only [z₀]; field_simp
  have h3 := sum_weierstrassZeta_sub_divisionPoint H hn hz₀
  set t := 2 * H.ω₁ / n + 2 * H.ω₃ / n
  have h1 := hc (-z₀)
  have h2 := hc (z₀ + t)
  simp only [nTupleZetaDiff] at h1 h2
  have hneg : ∀ j l, H.weierstrassZeta (-z₀ + H.divisionPoint n j l) =
      -H.weierstrassZeta (z₀ - H.divisionPoint n j l) := by
    intro j l
    rw [show -z₀ + H.divisionPoint n j l = -(z₀ - H.divisionPoint n j l) by ring]
    exact weierstrassZeta_neg _ _
  have hneg' : H.weierstrassZeta ((n : ℂ) * -z₀) = -H.weierstrassZeta (n * z₀) := by
    rw [mul_neg]; exact weierstrassZeta_neg _ _
  have hnt : H.weierstrassZeta ((n : ℂ) * (z₀ + t)) =
      H.weierstrassZeta (n * z₀) + 2 * H.eta 1 + 2 * H.eta 3 := by
    rw [show (n : ℂ) * (z₀ + t) = n * z₀ + 2 * H.ω₁ + 2 * H.ω₃ by simp only [t]; field_simp; ring,
      weierstrassZeta_add_two_mul_ω₁_add_ω₃ H hz₀]
  simp only [hneg, hneg', Finset.sum_neg_distrib] at h1
  rw [hnt] at h2
  linear_combination (-1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2 - (1 / 2 : ℂ) * h3

/-- DLMF 23.10.11 for `n ≥ 1`: `n²℘(nz) = ∑_{j,ℓ=0}^{n-1} ℘(z + 2jω₁/n + 2ℓω₃/n)` for
`nz ∉ 𝕃`. Stronger than DLMF, which assumes `n ≥ 2`. -/
@[dlmf 23.10.E11]
theorem weierstrassP_nsmul' {n : ℕ} (hn : n ≠ 0) {z : ℂ} (hz : (n : ℂ) * z ∉ H.lattice) :
    (n : ℂ) ^ 2 * H.weierstrassP (n * z) =
      ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n, H.weierstrassP (z + H.divisionPoint n j l) := by
  have h0 : HasDerivAt (H.nTupleZetaDiff n) 0 z := by
    have : H.nTupleZetaDiff n = fun _ => (n * (n - 1) * (H.eta 1 + H.eta 3) : ℂ) :=
      funext (nTupleZetaDiff_eq H hn)
    rw [this]; exact hasDerivAt_const _ _
  have h1 : HasDerivAt (H.nTupleZetaDiff n)
      ((∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n, -H.weierstrassP (z + H.divisionPoint n j l)) -
        n * (-H.weierstrassP (n * z) * n)) z := by
    refine HasDerivAt.sub (HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun l _ => ?_)
      (HasDerivAt.const_mul _ ?_)
    · exact (hasDerivAt_weierstrassZeta H.periodPair
        (add_divisionPoint_not_mem H hn hz j l)).comp_add_const z _
    · have := (hasDerivAt_weierstrassZeta H.periodPair hz).comp z
        ((hasDerivAt_id z).const_mul (n : ℂ))
      rw [mul_one] at this; exact this
  have := h1.unique h0
  simp only [Finset.sum_neg_distrib] at this
  linear_combination this

/-- DLMF 23.10.12 for every `n` and every `z`:
`nζ(nz) = -n(n-1)(η₁ + η₃) + ∑_{j,ℓ=0}^{n-1} ζ(z + 2jω₁/n + 2ℓω₃/n)`. With Lean's totalization
of `ζ` at lattice points (the regular part) the identity also holds for `nz ∈ 𝕃`. Stronger than
DLMF, which assumes `n ≥ 2` and `nz ∉ 𝕃`. -/
@[dlmf 23.10.E12]
theorem weierstrassZeta_nsmul' (n : ℕ) (z : ℂ) :
    (n : ℂ) * H.weierstrassZeta (n * z) = -(n * (n - 1)) * (H.eta 1 + H.eta 3) +
      ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n,
        H.weierstrassZeta (z + H.divisionPoint n j l) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  have := nTupleZetaDiff_eq H hpos.ne' z
  simp only [nTupleZetaDiff] at this
  linear_combination -this

/-- DLMF 23.10.11: `n²℘(nz) = ∑_{j,ℓ=0}^{n-1} ℘(z + 2jω₁/n + 2ℓω₃/n)`, `n ≥ 2`, `nz ∉ 𝕃`. -/
@[dlmf 23.10.E11]
theorem weierstrassP_nsmul {n : ℕ} (hn : 2 ≤ n) {z : ℂ} (hz : (n : ℂ) * z ∉ H.lattice) :
    (n : ℂ) ^ 2 * H.weierstrassP (n * z) =
      ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n, H.weierstrassP (z + H.divisionPoint n j l) :=
  H.weierstrassP_nsmul' (by omega) hz

/-- DLMF 23.10.12: `nζ(nz) = -n(n-1)(η₁ + η₃) + ∑_{j,ℓ=0}^{n-1} ζ(z + 2jω₁/n + 2ℓω₃/n)`,
`n ≥ 2`, `nz ∉ 𝕃`. -/
@[dlmf 23.10.E12]
theorem weierstrassZeta_nsmul {n : ℕ} (_hn : 2 ≤ n) {z : ℂ} (_hz : (n : ℂ) * z ∉ H.lattice) :
    (n : ℂ) * H.weierstrassZeta (n * z) = -(n * (n - 1)) * (H.eta 1 + H.eta 3) +
      ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n,
        H.weierstrassZeta (z + H.divisionPoint n j l) :=
  H.weierstrassZeta_nsmul' n z

/-- The constant `A_n` of 23.10.13, by the **corrected** DLMF 23.10.14:
`A_n = n ∏_{(j,ℓ) ≠ (0,0)} 1/σ((2jω₁ + 2ℓω₃)/n)`, `0 ≤ j, ℓ < n`.
Corrected from the printed DLMF formula: the printed index set `ℓ ≠ j` is wrong (relative error
0.71 at `n = 2`); the product runs over `(j, ℓ) ≠ (0, 0)`, excluding only the zero of `σ`. -/
@[dlmf 23.10.E14]
def nTupleConst (n : ℕ) : ℂ :=
  n * ∏ p ∈ (Finset.range n ×ˢ Finset.range n).erase (0, 0),
    1 / H.weierstrassSigma (H.divisionPoint n p.1 p.2)

private lemma divisionPoint_zero_zero (n : ℕ) : H.divisionPoint n 0 0 = 0 := by
  simp [divisionPoint]

/-- The product `∏_{j,ℓ} σ(z + 2jω₁/n + 2ℓω₃/n)` as a product over pairs. -/
private lemma prod_prod_eq_prod_product (n : ℕ) (f : ℕ → ℕ → ℂ) :
    ∏ j ∈ Finset.range n, ∏ l ∈ Finset.range n, f j l =
      ∏ p ∈ Finset.range n ×ˢ Finset.range n, f p.1 p.2 :=
  (Finset.prod_product' _ _ _).symm

/-- DLMF 23.10.13 for every `n` (with `A_n` as in the corrected 23.10.14). Stronger than DLMF,
which assumes `n ≥ 2`. -/
@[dlmf 23.10.E13]
theorem weierstrassSigma_nsmul' (n : ℕ) (z : ℂ) :
    H.weierstrassSigma (n * z) = H.nTupleConst n * cexp (-(n * (n - 1)) * (H.eta 1 + H.eta 3) * z) *
      ∏ j ∈ Finset.range n, ∏ l ∈ Finset.range n,
        H.weierstrassSigma (z + H.divisionPoint n j l) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [nTupleConst, weierstrassSigma_eq_zero_of_mem _ (zero_mem _)]
  have hn : n ≠ 0 := hpos.ne'
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  set κ : ℂ := n * (n - 1) * (H.eta 1 + H.eta 3)
  set S := Finset.range n ×ˢ Finset.range n
  set σ := Weierstrass.weierstrassSigma H.periodPair
  have hσd := differentiable_weierstrassSigma H.periodPair
  set P : ℂ → ℂ := fun z => ∏ p ∈ S, σ (z + H.divisionPoint n p.1 p.2)
  set g1 : ℂ → ℂ := fun z => σ (n * z) * cexp (κ * z)
  set U : Set ℂ := ((H.divisionPeriodPair n hn).lattice : Set ℂ)ᶜ
  have hU : IsOpen U := (H.divisionPeriodPair n hn).isClosed_lattice.isOpen_compl
  have hmemU : ∀ z, z ∈ U ↔ (n : ℂ) * z ∉ H.lattice := fun z => by
    simp only [U, Set.mem_compl_iff, SetLike.mem_coe, mem_divisionPeriodPair_iff]
  have hne : ∀ y, y ∉ H.lattice → σ y ≠ 0 := fun y hy =>
    (weierstrassSigma_eq_zero_iff _).not.mpr hy
  have hP0 : ∀ z, z ∈ U → P z ≠ 0 := fun z hz => Finset.prod_ne_zero_iff.mpr fun p _ =>
    hne _ (add_divisionPoint_not_mem H hn ((hmemU z).mp hz) _ _)
  have hg10 : ∀ z, z ∈ U → g1 z ≠ 0 := fun z hz =>
    mul_ne_zero (hne _ ((hmemU z).mp hz)) (Complex.exp_ne_zero _)
  have hdP : ∀ z, z ∈ U → HasDerivAt P (P z * ∑ p ∈ S,
      H.weierstrassZeta (z + H.divisionPoint n p.1 p.2)) z := by
    intro z hz
    have := HasDerivAt.fun_finsetProd (u := S) (x := z)
      (f := fun p y => σ (y + H.divisionPoint n p.1 p.2))
      (f' := fun p => H.weierstrassZeta (z + H.divisionPoint n p.1 p.2) *
        σ (z + H.divisionPoint n p.1 p.2)) (fun p _ => by
        have h := (hσd (z + H.divisionPoint n p.1 p.2)).hasDerivAt.comp_add_const z
          (H.divisionPoint n p.1 p.2)
        rwa [deriv_weierstrassSigma_eq_zeta_mul _
          (add_divisionPoint_not_mem H hn ((hmemU z).mp hz) _ _)] at h)
    convert this using 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [P]
    rw [smul_eq_mul, ← Finset.prod_erase_mul _ _ hp]
    ring
  have hdg1 : ∀ z, z ∈ U → HasDerivAt g1
      (g1 z * (n * H.weierstrassZeta (n * z) + κ)) z := by
    intro z hz
    have h1 : HasDerivAt (fun z => σ (n * z)) (H.weierstrassZeta (n * z) * σ (n * z) * n) z := by
      have h := (hσd (n * z)).hasDerivAt.comp z ((hasDerivAt_id z).const_mul (n : ℂ))
      rw [deriv_weierstrassSigma_eq_zeta_mul _ ((hmemU z).mp hz), mul_one] at h
      exact h
    have h2 : HasDerivAt (fun z => cexp (κ * z)) (cexp (κ * z) * κ) z := by
      have := ((hasDerivAt_id z).const_mul κ).cexp
      simpa using this
    convert h1.mul h2 using 1
    simp only [g1]; ring
  set h : ℂ → ℂ := fun z => g1 z / P z
  have hD : ∀ z ∈ U, HasDerivAt h 0 z := by
    intro z hz
    have hF := nTupleZetaDiff_eq H hn z
    simp only [nTupleZetaDiff] at hF
    rw [← Finset.sum_product'] at hF
    convert (hdg1 z hz).div (hdP z hz) (hP0 z hz) using 1
    rw [eq_div_iff (pow_ne_zero 2 (hP0 z hz))]
    linear_combination (g1 z * P z) * hF
  have hω : H.ω₁ ∉ H.lattice := by simpa using H.halfPeriod_notMem (j := 1) (by simp)
  have hz₀ : H.ω₁ / n ∈ U := by
    rw [hmemU]; rwa [mul_div_cancel₀ _ hn']
  have hconst : ∀ z ∈ U, h z = h (H.ω₁ / n) := fun z hz =>
    hU.is_const_of_deriv_eq_zero (isPreconnected_compl_lattice _)
      (fun y hy => (hD y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hD y hy).deriv) hz hz₀
  set K := h (H.ω₁ / n)
  have hall : ∀ z, σ (n * z) = K * cexp (-κ * z) * P z := by
    intro z
    by_cases hz : z ∈ U
    · have := hconst z hz
      simp only [h, g1] at this
      rw [div_eq_iff (hP0 z hz)] at this
      have he : cexp (κ * z) * cexp (-κ * z) = 1 := by rw [← Complex.exp_add]; simp
      linear_combination cexp (-κ * z) * this - σ (n * z) * he
    · rw [hmemU, not_not] at hz
      obtain ⟨j₀, hj₀, l₀, hl₀, hmem, -⟩ := exists_unique_add_divisionPoint_mem H hn hz
      have hP : P z = 0 := Finset.prod_eq_zero (i := (j₀, l₀))
        (Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj₀, Finset.mem_range.mpr hl₀⟩)
        (weierstrassSigma_eq_zero_of_mem _ hmem)
      rw [hP, mul_zero]; exact weierstrassSigma_eq_zero_of_mem _ hz
  have h00 : ((0, 0) : ℕ × ℕ) ∈ S :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr hpos, Finset.mem_range.mpr hpos⟩
  set Q : ℂ → ℂ := fun z => ∏ p ∈ S.erase (0, 0), σ (z + H.divisionPoint n p.1 p.2)
  have hPQ : ∀ z, P z = σ z * Q z := fun z => by
    simp only [P, Q]
    rw [← Finset.mul_prod_erase S _ h00, divisionPoint_zero_zero, add_zero]
  have hQd : Differentiable ℂ Q := by
    simp only [Q]
    exact Differentiable.fun_finsetProd fun p _ => hσd.comp (differentiable_id.add_const _)
  have hσ0 : σ 0 = 0 := weierstrassSigma_eq_zero_of_mem _ (zero_mem _)
  have hL : HasDerivAt (fun z => σ (n * z)) n 0 := by
    have h0 : HasDerivAt σ 1 ((n : ℂ) * 0) := by
      simpa using hasDerivAt_weierstrassSigma_zero H.periodPair
    have := h0.comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_mul (n : ℂ))
    simp only [one_mul, mul_one] at this; exact this
  have hR : HasDerivAt (fun z => K * cexp (-κ * z) * P z) (K * Q 0) 0 := by
    have he : HasDerivAt (fun z => K * cexp (-κ * z)) (K * (cexp (-κ * 0) * -κ)) 0 := by
      have := ((hasDerivAt_id (0 : ℂ)).const_mul (-κ)).cexp.const_mul K
      simpa using this
    have hp : HasDerivAt P (1 * Q 0 + σ 0 * deriv Q 0) 0 := by
      rw [show P = fun z => σ z * Q z from funext hPQ]
      exact (hasDerivAt_weierstrassSigma_zero H.periodPair).mul (hQd 0).hasDerivAt
    convert he.mul hp using 1
    rw [hPQ 0, hσ0]; simp
  rw [show (fun z => σ (n * z)) = fun z => K * cexp (-κ * z) * P z from funext hall] at hL
  have hKQ : (n : ℂ) = K * Q 0 := hL.unique hR
  have hQ0 : Q 0 ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun p hp => hne _ fun hmem => ?_
    obtain ⟨hp0, hpS⟩ := Finset.mem_erase.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpS
    have := divisionPoint_sub_mem H hn (Finset.mem_range.mp hp1) (Finset.mem_range.mp hp2)
      hpos hpos (by simpa [divisionPoint_zero_zero] using hmem)
    exact hp0 (Prod.ext this.1 this.2)
  have hK : H.nTupleConst n = K := by
    simp only [nTupleConst, Finset.prod_div_distrib, Finset.prod_const_one]
    rw [hKQ]
    simp only [Q, zero_add] at hQ0 ⊢
    rw [mul_one_div]; exact mul_div_cancel_right₀ K hQ0
  have hexp : -(n * (n - 1) : ℂ) * (H.eta 1 + H.eta 3) * z = -κ * z := by simp only [κ]; ring
  rw [hK, hexp, prod_prod_eq_prod_product]
  exact hall z

/-- DLMF 23.10.13: `σ(nz) = A_n e^{-n(n-1)(η₁+η₃)z} ∏_{j,ℓ=0}^{n-1} σ(z + 2jω₁/n + 2ℓω₃/n)`,
`n ≥ 2`, `z ∈ ℂ`, with `A_n` as in the corrected 23.10.14. -/
@[dlmf 23.10.E13]
theorem weierstrassSigma_nsmul {n : ℕ} (_hn : 2 ≤ n) (z : ℂ) :
    H.weierstrassSigma (n * z) = H.nTupleConst n * cexp (-(n * (n - 1)) * (H.eta 1 + H.eta 3) * z) *
      ∏ j ∈ Finset.range n, ∏ l ∈ Finset.range n,
        H.weierstrassSigma (z + H.divisionPoint n j l) :=
  H.weierstrassSigma_nsmul' n z

/-- `G = ∏_{n≥1} (1 - q^{2n})`, `q = e^{πiω₃/ω₁}` (DLMF 23.10.16). -/
@[dlmf 23.10.E16]
def nTupleG : ℂ := ∏' n : ℕ, (1 - H.nome ^ (2 * (n + 1)))

/-- DLMF 23.10.15, **corrected** (`π` in place of the printed `π²`):
`A_n = (πG²/ω₁)^{n²-1} q^{n(n-1)/2} i^{-(n-1)}
exp(-((n-1)η₁/(3ω₁))((2n-1)(ω₁² + ω₃²) + 3(n-1)ω₁ω₃))`, `n ≥ 2`.
Corrected from the printed DLMF formula: the printed `π²` should be `π`; with `π` the ratio of
the two sides is exactly 1, with `π²` it is `π^{-(n²-1)}` (n = 2, 3, 4, three lattices). -/
@[dlmf 23.10.E15]
theorem nTupleConst_eq {n : ℕ} (hn : 2 ≤ n) :
    H.nTupleConst n = (π * H.nTupleG ^ 2 / H.ω₁) ^ (n ^ 2 - 1) *
      H.nome ^ (n * (n - 1) / 2) / I ^ (n - 1) *
      cexp (-((n - 1 : ℂ) * H.eta 1 / (3 * H.ω₁)) *
        ((2 * n - 1) * (H.ω₁ ^ 2 + H.ω₃ ^ 2) + 3 * (n - 1) * H.ω₁ * H.ω₃)) := by
  sorry

end HalfPeriods

/-! ### Homogeneity (§23.10(iv)) -/

/-- DLMF 23.10.17: `℘(cz|c𝕃) = c⁻²℘(z|𝕃)`. -/
@[dlmf 23.10.E17]
theorem weierstrassP_scale (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) (z : ℂ) :
    ℘[scalePeriodPair c hc L] (c * z) = c⁻¹ ^ 2 * ℘[L] z := by
  simp only [PeriodPair.weierstrassP]
  rw [← (scalePeriodPairLatticeEquiv c hc L).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  simp only [scalePeriodPairLatticeEquiv, Equiv.coe_fn_mk]
  rw [← mul_sub, mul_pow, mul_pow]
  simp only [one_div, mul_inv, inv_pow]
  ring

/-- DLMF 23.10.18: `ζ(cz|c𝕃) = c⁻¹ζ(z|𝕃)`. -/
@[dlmf 23.10.E18]
theorem weierstrassZeta_scale (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) (z : ℂ) :
    weierstrassZeta (scalePeriodPair c hc L) (c * z) = c⁻¹ * weierstrassZeta L z := by
  simp only [weierstrassZeta]
  rw [← (scalePeriodPairLatticeEquiv c hc L).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  simp only [scalePeriodPairLatticeEquiv, Equiv.coe_fn_mk]
  rw [← mul_sub, mul_pow]
  simp only [mul_inv, div_eq_mul_inv]
  field_simp

/-- DLMF 23.10.19: `σ(cz|c𝕃) = cσ(z|𝕃)`. -/
@[dlmf 23.10.E19]
theorem weierstrassSigma_scale (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) (z : ℂ) :
    weierstrassSigma (scalePeriodPair c hc L) (c * z) = c * weierstrassSigma L z := by
  simp only [weierstrassSigma]
  rw [← (scalePeriodPairLatticeEquiv c hc L).tprod_eq, mul_assoc]
  congr 2
  refine tprod_congr fun l => ?_
  simp only [scalePeriodPairLatticeEquiv, Equiv.coe_fn_mk]
  rw [mul_div_mul_left _ _ hc, mul_pow, mul_pow,
    show c ^ 2 * z ^ 2 / (2 * (c ^ 2 * (l : ℂ) ^ 2)) = z ^ 2 / (2 * (l : ℂ) ^ 2) by
      rw [mul_left_comm 2, mul_div_mul_left _ _ (pow_ne_zero 2 hc)]]

end DLMF.Weierstrass
