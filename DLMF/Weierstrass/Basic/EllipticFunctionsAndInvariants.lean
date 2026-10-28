/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic.LatticesAndSigma

/-!
# Weierstrass elliptic functions and invariants

Elliptic-function uniqueness, half-period values, invariants and discriminant identities.

Source references and common attribution are retained in
`DLMF.Weierstrass.Basic`.
-/

@[expose] public section

open Complex PeriodPair

open scoped Real

noncomputable section

namespace DLMF.Weierstrass

/-! ### Liouville's theorem for elliptic functions and the values of `℘` at half-periods -/

section p23R1

open Filter Topology

/-- `℘ - c` has a pole of order exactly `2` at every lattice point. -/
theorem p23R1_order_weierstrassP_sub (L : PeriodPair) {x : ℂ} (hx : x ∈ L.lattice) (c : ℂ) :
    meromorphicOrderAt (fun z => ℘[L] z - c) x = -2 := by
  have hlt : meromorphicOrderAt ℘[L] x < meromorphicOrderAt (fun _ : ℂ => -c) x := by
    rw [L.order_weierstrassP x hx]
    exact lt_of_lt_of_le (by decide) (analyticAt_const.meromorphicOrderAt_nonneg)
  have h := meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const (-c) x) hlt
  rw [L.order_weierstrassP x hx] at h
  rw [← h]
  congr 1

/-- An analytic function with `g x = g'(x) = 0` has order at least `2` at `x`. -/
theorem p23R1_two_le_order {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) (h0 : g x = 0)
    (h1 : deriv g x = 0) : (2 : WithTop ℤ) ≤ meromorphicOrderAt g x := by
  have h2 : ((2 : ℕ) : ℕ∞) ≤ analyticOrderAt g x := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg]
    intro i hi
    interval_cases i <;> simp [h0, h1]
  rw [hg.meromorphicOrderAt_eq]
  cases h : analyticOrderAt g x with
  | top => simp
  | coe n =>
    rw [h] at h2
    have : 2 ≤ n := by exact_mod_cast h2
    simp only [ENat.map_natCast]
    have e : ((2 : ℤ) : WithTop ℤ) ≤ ((n : ℤ) : WithTop ℤ) := WithTop.coe_le_coe.mpr (by omega)
    exact e

/-- `-2 + o ≥ 0` for an order `o ≥ 2`. -/
lemma p23R1_nonneg_add {o : WithTop ℤ} (h : 2 ≤ o) : 0 ≤ (-2 : WithTop ℤ) + o := by
  cases o with
  | top => simp
  | coe n =>
    have h' : ((2 : ℤ) : WithTop ℤ) ≤ (n : WithTop ℤ) := h
    have : (2 : ℤ) ≤ n := WithTop.coe_le_coe.mp h'
    have e : ((0 : ℤ) : WithTop ℤ) ≤ ((-2 + n : ℤ) : WithTop ℤ) := WithTop.coe_le_coe.mpr (by omega)
    exact e

/-- Liouville for elliptic functions: a lattice-periodic meromorphic function with nonnegative
order everywhere takes one constant value at every point where it is analytic. -/
theorem p23R1_eq_const_of_elliptic (L : PeriodPair) {f : ℂ → ℂ} (hf : Meromorphic f)
    (hper : ∀ z, ∀ l ∈ L.lattice, f (z + l) = f z)
    (hord : ∀ x, 0 ≤ meromorphicOrderAt f x) :
    ∃ c, ∀ x, AnalyticAt ℂ f x → f x = c := by
  have hfU : MeromorphicOn f Set.univ := hf.meromorphicOn
  set Q := toMeromorphicNFOn f Set.univ with hQ
  have hQan : ∀ x, AnalyticAt ℂ Q x := by
    intro x
    have hnf : MeromorphicNFAt Q x := meromorphicNFOn_toMeromorphicNFOn f Set.univ (Set.mem_univ x)
    refine hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
    rw [meromorphicOrderAt_congr (hfU.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ x))]
    exact hord x
  have hQd : Differentiable ℂ Q := fun x => (hQan x).differentiableAt
  have hQf : ∀ x, Q =ᶠ[𝓝[≠] x] f := fun x => hfU.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ x)
  have hper' : ∀ z w, w ∈ L.lattice → Q (z + w) = Q z := by
    intro z w hw
    have h1 : Tendsto (fun y => Q (y + w)) (𝓝[≠] z) (𝓝 (Q (z + w))) :=
      ((hQd.continuous.comp (continuous_id.add continuous_const : Continuous fun y : ℂ => y + w)).tendsto z).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto Q (𝓝[≠] z) (𝓝 (Q z)) :=
      (hQd.continuous.tendsto z).mono_left nhdsWithin_le_nhds
    have hmap : Tendsto (fun y => y + w) (𝓝[≠] z) (𝓝[≠] (z + w)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_id.add continuous_const : Continuous fun y : ℂ => y + w).tendsto z |>.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      simpa using hy
    have hev : (fun y => Q (y + w)) =ᶠ[𝓝[≠] z] Q := by
      filter_upwards [hmap.eventually (hQf (z + w)), hQf z] with y hy1 hy2
      rw [hy1, hy2, hper y w hw]
    exact tendsto_nhds_unique (h1.congr' hev) h2
  have hc := IsZLattice.isCompact_range_of_periodic L.lattice Q hQd.continuous hper'
  refine ⟨Q 0, fun x hx => ?_⟩
  have hQx : Q x = Q 0 := hQd.apply_eq_apply_of_bounded hc.isBounded x 0
  rw [← hQx]
  exact tendsto_nhds_unique ((hx.continuousAt.tendsto).mono_left nhdsWithin_le_nhds)
    (((hQd.continuous.tendsto x).mono_left nhdsWithin_le_nhds).congr' (hQf x))

/-- `℘'(a) = 0` for every half-lattice point `a` (`2a ∈ 𝕃`). -/
theorem p23R1_derivWeierstrassP_of_two_mul_mem (L : PeriodPair) {a : ℂ}
    (h2a : 2 * a ∈ L.lattice) : ℘'[L] a = 0 := by
  have h1 := L.derivWeierstrassP_sub_coe a ⟨_, h2a⟩
  have h2 := L.derivWeierstrassP_neg a
  rw [show a - ((⟨2 * a, h2a⟩ : L.lattice) : ℂ) = -a by simp; ring, h2] at h1
  exact CharZero.eq_neg_self_iff.mp h1.symm

/-- For a half-lattice point `a` the product `(℘(z + a) - ℘(a))(℘(z) - ℘(a))` is constant. -/
theorem p23R1_halfPeriod_product (L : PeriodPair) {a : ℂ} (ha : a ∉ L.lattice)
    (h2a : 2 * a ∈ L.lattice) :
    ∃ K, ∀ z, z ∉ L.lattice → z + a ∉ L.lattice →
      (℘[L] (z + a) - ℘[L] a) * (℘[L] z - ℘[L] a) = K := by
  have hP : AnalyticOnNhd ℂ ℘[L] L.latticeᶜ := L.analyticOnNhd_weierstrassP
  have hP'a := p23R1_derivWeierstrassP_of_two_mul_mem L h2a
  have hneg : ℘[L] (-a) = ℘[L] a := L.weierstrassP_neg a
  have hneg' : ℘'[L] (-a) = 0 := by rw [L.derivWeierstrassP_neg, hP'a, neg_zero]
  have hmer1 : Meromorphic (fun z => ℘[L] (z + a) - ℘[L] a) := fun x =>
    (meromorphicAt_fun_comp_add_const_iff_meromorphicAt.mpr (L.meromorphic_weierstrassP _)).sub
      (MeromorphicAt.const _ _)
  have hmer2 : Meromorphic (fun z => ℘[L] z - ℘[L] a) := fun x =>
    (L.meromorphic_weierstrassP x).sub (MeromorphicAt.const _ _)
  have hf : Meromorphic (fun z => (℘[L] (z + a) - ℘[L] a) * (℘[L] z - ℘[L] a)) :=
    fun x => (hmer1 x).mul (hmer2 x)
  have hper : ∀ z, ∀ l ∈ L.lattice, (fun z => (℘[L] (z + a) - ℘[L] a) * (℘[L] z - ℘[L] a))
      (z + l) = (fun z => (℘[L] (z + a) - ℘[L] a) * (℘[L] z - ℘[L] a)) z := by
    intro z l hl
    simp only
    rw [show z + l + a = (z + a) + l by ring, L.weierstrassP_add_coe (z + a) ⟨l, hl⟩,
      L.weierstrassP_add_coe z ⟨l, hl⟩]
  have hA1 : ∀ x, x + a ∉ L.lattice → AnalyticAt ℂ (fun z => ℘[L] (z + a) - ℘[L] a) x :=
    fun x hx => ((hP _ hx).comp_of_eq (analyticAt_id.add analyticAt_const) rfl).sub analyticAt_const
  have hA2 : ∀ x, x ∉ L.lattice → AnalyticAt ℂ (fun z => ℘[L] z - ℘[L] a) x :=
    fun x hx => (hP _ hx).sub analyticAt_const
  have hord : ∀ x, 0 ≤ meromorphicOrderAt
      (fun z => (℘[L] (z + a) - ℘[L] a) * (℘[L] z - ℘[L] a)) x := by
    intro x
    rw [show (fun z => (℘[L] (z + a) - ℘[L] a) * (℘[L] z - ℘[L] a)) =
        (fun z => ℘[L] (z + a) - ℘[L] a) * (fun z => ℘[L] z - ℘[L] a) from rfl,
      meromorphicOrderAt_mul (hmer1 x) (hmer2 x)]
    by_cases hx : x ∈ L.lattice
    · have hxa : x + a ∉ L.lattice := fun h => ha (by simpa using sub_mem h hx)
      rw [p23R1_order_weierstrassP_sub L hx, add_comm]
      refine p23R1_nonneg_add (p23R1_two_le_order (hA1 x hxa) ?_ ?_)
      · rw [add_comm, L.weierstrassP_add_coe a ⟨x, hx⟩, sub_self]
      · rw [deriv_sub_const, deriv_comp_add_const, deriv_weierstrassP, add_comm,
          L.derivWeierstrassP_add_coe a ⟨x, hx⟩, hP'a]
    · by_cases hxa : x + a ∈ L.lattice
      · have h1 := meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt
          (f := fun w => ℘[L] w - ℘[L] a) (c := a) (x := x)
        rw [h1, p23R1_order_weierstrassP_sub L hxa]
        have hx' : x = -a + ((⟨x + a, hxa⟩ : L.lattice) : ℂ) := by simp
        refine p23R1_nonneg_add (p23R1_two_le_order (hA2 x hx) ?_ ?_)
        · rw [hx', L.weierstrassP_add_coe, hneg, sub_self]
        · rw [deriv_sub_const, deriv_weierstrassP, hx', L.derivWeierstrassP_add_coe, hneg']
      · exact add_nonneg (hA1 x hxa).meromorphicOrderAt_nonneg
          (hA2 x hx).meromorphicOrderAt_nonneg
  obtain ⟨c, hc⟩ := p23R1_eq_const_of_elliptic L hf hper hord
  exact ⟨c, fun z hz hza => hc z ((hA1 z hza).mul (hA2 z hz))⟩

/-- `℘` is not locally constant at any point off the lattice. -/
lemma p23R1_weierstrassP_not_eventually_const (L : PeriodPair) {z₀ : ℂ}
    (hz₀ : z₀ ∉ L.lattice) (c : ℂ) : ¬ ∀ᶠ z in 𝓝 z₀, ℘[L] z = c := by
  intro h
  have hA : AnalyticOnNhd ℂ (fun z => ℘[L] z - c) L.latticeᶜ :=
    fun x hx => (L.analyticOnNhd_weierstrassP x hx).sub analyticAt_const
  have h0 : (fun z => ℘[L] z - c) =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [h] with z hz
    simp [hz]
  have hc : ∀ w ∈ (L.latticeᶜ : Set ℂ), ℘[L] w = c := fun w hw =>
    sub_eq_zero.mp (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (wp23_isPreconnected_compl_lattice L) hz₀ h0 hw)
  have hev : ℘[L] =ᶠ[𝓝[≠] 0] fun _ ↦ c := by
    filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      self_mem_nhdsWithin] with w hw hw0
    exact hc w fun hl => hw ⟨hl, hw0⟩
  have h1 := L.order_weierstrassP 0 (zero_mem _)
  rw [meromorphicOrderAt_congr hev] at h1
  classical
  rw [meromorphicOrderAt_const] at h1
  split_ifs at h1 <;> revert h1 <;> decide

/-- `℘(b) ≠ ℘(a)` for a half-lattice point `a` unless `b ≡ ±a` modulo the lattice. -/
theorem p23R1_weierstrassP_ne_of_halfLattice (L : PeriodPair) {a b : ℂ} (ha : a ∉ L.lattice)
    (h2a : 2 * a ∈ L.lattice) (hb : b ∉ L.lattice) (hab : b + a ∉ L.lattice) :
    ℘[L] b ≠ ℘[L] a := by
  intro heq
  obtain ⟨K, hK⟩ := p23R1_halfPeriod_product L ha h2a
  have hK0 : K = 0 := by rw [← hK b hb hab, heq, sub_self, mul_zero]
  have hP : AnalyticOnNhd ℂ ℘[L] L.latticeᶜ := L.analyticOnNhd_weierstrassP
  have hopen : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have hA1 : AnalyticAt ℂ (fun z => ℘[L] (z + a) - ℘[L] a) b :=
    ((hP _ hab).comp_of_eq (analyticAt_id.add analyticAt_const) rfl).sub analyticAt_const
  have hA2 : AnalyticAt ℂ (fun z => ℘[L] z - ℘[L] a) b := (hP _ hb).sub analyticAt_const
  have hcont : Continuous fun z : ℂ => z + a := continuous_id.add continuous_const
  have hV : ∀ᶠ z in 𝓝 b, (℘[L] (z + a) - ℘[L] a) * (℘[L] z - ℘[L] a) = 0 := by
    have h1 : ∀ᶠ z in 𝓝 b, z + a ∉ L.lattice :=
      (hcont.tendsto b).eventually (hopen.mem_nhds hab)
    filter_upwards [hopen.mem_nhds hb, h1] with z hz hza
    rw [hK z hz hza, hK0]
  rcases hA2.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact p23R1_weierstrassP_not_eventually_const L hb (℘[L] a)
      (h.mono fun z hz => sub_eq_zero.mp hz)
  · have hfr : ∃ᶠ z in 𝓝[≠] b, ℘[L] (z + a) - ℘[L] a = 0 := by
      refine Filter.Eventually.frequently ?_
      filter_upwards [h, nhdsWithin_le_nhds hV] with z hz1 hz2
      exact (mul_eq_zero.mp hz2).resolve_right hz1
    have hev := hA1.frequently_zero_iff_eventually_zero.mp hfr
    have hsub : Filter.Tendsto (fun w : ℂ => w - a) (𝓝 (b + a)) (𝓝 b) := by
      have hc : Continuous fun w : ℂ => w - a := by fun_prop
      have := hc.tendsto (b + a)
      simpa only [add_sub_cancel_right] using this
    refine p23R1_weierstrassP_not_eventually_const L hab (℘[L] a) ?_
    filter_upwards [hsub.eventually hev] with w hw
    simpa using sub_eq_zero.mp hw

end p23R1

/-! ### Half-period values, `e_j` and `η_j` -/

namespace HalfPeriods

variable (H : HalfPeriods)

/-- The half-periods indexed as in DLMF: `ω_j` for `j = 1, 2, 3` (junk `0` otherwise). -/
def halfPeriod : ℕ → ℂ
  | 1 => H.ω₁
  | 2 => H.ω₂
  | 3 => H.ω₃
  | _ => 0

/-- Identity under the stated parameter and domain assumptions: `H.halfPeriod 1 = H.ω₁`. -/
@[simp] theorem halfPeriod_one : H.halfPeriod 1 = H.ω₁ := rfl
/-- Identity under the stated parameter and domain assumptions: `H.halfPeriod 2 = H.ω₂`. -/
@[simp] theorem halfPeriod_two : H.halfPeriod 2 = H.ω₂ := rfl
/-- Identity under the stated parameter and domain assumptions: `H.halfPeriod 3 = H.ω₃`. -/
@[simp] theorem halfPeriod_three : H.halfPeriod 3 = H.ω₃ := rfl

/-- `℘(z|𝕃)` for DLMF lattice data. -/
abbrev weierstrassP (z : ℂ) : ℂ := ℘[H.periodPair] z
/-- `℘'(z|𝕃)` for DLMF lattice data. -/
abbrev derivWeierstrassP (z : ℂ) : ℂ := ℘'[H.periodPair] z
/-- `ζ(z|𝕃)` for DLMF lattice data. -/
abbrev weierstrassZeta (z : ℂ) : ℂ := DLMF.Weierstrass.weierstrassZeta H.periodPair z
/-- `σ(z|𝕃)` for DLMF lattice data. -/
abbrev weierstrassSigma (z : ℂ) : ℂ := DLMF.Weierstrass.weierstrassSigma H.periodPair z
/-- The invariant `g₂` (DLMF 23.3.1), Mathlib's `PeriodPair.g₂`. -/
abbrev g₂ : ℂ := H.periodPair.g₂
/-- The invariant `g₃` (DLMF 23.3.2), Mathlib's `PeriodPair.g₃`. -/
abbrev g₃ : ℂ := H.periodPair.g₃

/-- The lattice roots `e_j = ℘(ω_j)` (DLMF 23.3.9), `j = 1, 2, 3`. -/
@[dlmf 23.3.E9]
def e (j : ℕ) : ℂ := H.weierstrassP (H.halfPeriod j)

/-- The constants `η_j = ζ(ω_j)` (DLMF 23.2.12), `j = 1, 2, 3`. -/
@[dlmf 23.2.E12]
def eta (j : ℕ) : ℂ := H.weierstrassZeta (H.halfPeriod j)

/-- Formula under the stated hypotheses: `2 * H.halfPeriod j ∈ H.lattice`. -/
theorem two_mul_halfPeriod_mem {j : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    2 * H.halfPeriod j ∈ H.lattice := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  exacts [H.two_mul_ω₁_mem, H.two_mul_ω₂_mem, H.two_mul_ω₃_mem]

/-- The stated relation follows from the given hypotheses: `H.halfPeriod j ∉ H.lattice`. -/
theorem halfPeriod_notMem {j : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    H.halfPeriod j ∉ H.lattice := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · simpa using H.periodPair.ω₁_div_two_notMem_lattice
  · intro h
    have h' : ((-1 / 2 : ℚ) : ℂ) * H.periodPair.ω₁ + ((-1 / 2 : ℚ) : ℂ) * H.periodPair.ω₂ ∈
        H.periodPair.lattice := by
      convert h using 1; simp [ω₂]; ring
    have := (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice).mp h'
    norm_num at this
  · simpa using H.periodPair.ω₂_div_two_notMem_lattice

/-- DLMF 23.2.9: `℘(z + 2ω_j) = ℘(z)`, `j = 1, 2, 3`. -/
@[dlmf 23.2.E9]
theorem weierstrassP_add_two_mul_halfPeriod (z : ℂ) {j : ℕ}
    (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    H.weierstrassP (z + 2 * H.halfPeriod j) = H.weierstrassP z :=
  H.periodPair.weierstrassP_add_coe z ⟨_, H.two_mul_halfPeriod_mem hj⟩

/-- DLMF 23.2.10: `℘'(ω_j) = 0`, `j = 1, 2, 3`. -/
@[dlmf 23.2.E10]
theorem derivWeierstrassP_halfPeriod {j : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    H.derivWeierstrassP (H.halfPeriod j) = 0 := by
  have h1 := H.periodPair.derivWeierstrassP_add_coe (-H.halfPeriod j)
    ⟨_, H.two_mul_halfPeriod_mem hj⟩
  have h2 := H.periodPair.derivWeierstrassP_neg (H.halfPeriod j)
  simp only at h1
  rw [show -H.halfPeriod j + 2 * H.halfPeriod j = H.halfPeriod j by ring, h2] at h1
  exact CharZero.eq_neg_self_iff.mp h1

/-- DLMF 23.2.11: `ζ` is quasi-periodic, `ζ(z + 2ω_j) = ζ(z) + 2η_j`, `j = 1, 2, 3`, for
`z ∉ 𝕃`. -/
@[dlmf 23.2.E11]
theorem weierstrassZeta_add_two_mul_halfPeriod {z : ℂ} (hz : z ∉ H.lattice) {j : ℕ}
    (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    H.weierstrassZeta (z + 2 * H.halfPeriod j) = H.weierstrassZeta z + 2 * H.eta j := by
  have hn := H.halfPeriod_notMem hj
  have hn' : -H.halfPeriod j ∉ H.lattice := fun h => hn (by simpa using neg_mem h)
  have := wp23_zeta_add_sub_const H.periodPair (H.two_mul_halfPeriod_mem hj) hz hn'
  rw [show -H.halfPeriod j + 2 * H.halfPeriod j = H.halfPeriod j by ring,
    DLMF.Weierstrass.weierstrassZeta_neg] at this
  simp only [HalfPeriods.weierstrassZeta, eta]
  linear_combination this

/-- DLMF 23.2.13: `η₁ + η₂ + η₃ = 0` (derived from the quasi-periodicity 23.2.11 and the
oddness of `ζ`). -/
@[dlmf 23.2.E13]
theorem eta_one_add_eta_two_add_eta_three : H.eta 1 + H.eta 2 + H.eta 3 = 0 := by
  have hn : H.ω₃ - H.ω₁ ∉ H.lattice := by
    intro h
    have h' : ((-1 / 2 : ℚ) : ℂ) * H.periodPair.ω₁ + ((1 / 2 : ℚ) : ℂ) * H.periodPair.ω₂ ∈
        H.periodPair.lattice := by
      convert h using 1; simp; ring
    have := (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice).mp h'
    norm_num at this
  have hn' : H.ω₁ - H.ω₃ ∉ H.lattice := by
    rw [show H.ω₁ - H.ω₃ = -(H.ω₃ - H.ω₁) by ring]
    exact fun h => hn (by simpa using neg_mem h)
  have h1 := H.weierstrassZeta_add_two_mul_halfPeriod hn (j := 1) (by simp)
  have h3 := H.weierstrassZeta_add_two_mul_halfPeriod hn' (j := 3) (by simp)
  simp only [halfPeriod_one, halfPeriod_three, HalfPeriods.weierstrassZeta] at h1 h3
  rw [show H.ω₃ - H.ω₁ + 2 * H.ω₁ = H.ω₁ + H.ω₃ by ring] at h1
  rw [show H.ω₁ - H.ω₃ + 2 * H.ω₃ = H.ω₁ + H.ω₃ by ring,
    show H.ω₁ - H.ω₃ = -(H.ω₃ - H.ω₁) by ring,
    DLMF.Weierstrass.weierstrassZeta_neg] at h3
  have h2 : H.eta 2 = -H.weierstrassZeta (H.ω₁ + H.ω₃) := by
    rw [eta, halfPeriod_two, ω₂, show -H.ω₁ - H.ω₃ = -(H.ω₁ + H.ω₃) by ring]
    simp only [HalfPeriods.weierstrassZeta, DLMF.Weierstrass.weierstrassZeta_neg]
  rw [h2]
  simp only [HalfPeriods.weierstrassZeta] at h1 h3 ⊢
  linear_combination (-(1 : ℂ) / 2) * (h1 + h3)

/-- DLMF 23.2.15: `σ(z + 2ω_j) = -e^{2η_j(z + ω_j)} σ(z)`, `j = 1, 2, 3`, for all `z ∈ ℂ`. -/
@[dlmf 23.2.E15]
theorem weierstrassSigma_add_two_mul_halfPeriod (z : ℂ) {j : ℕ}
    (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    H.weierstrassSigma (z + 2 * H.halfPeriod j) =
      -cexp (2 * H.eta j * (z + H.halfPeriod j)) * H.weierstrassSigma z := by
  set ω := H.halfPeriod j
  have hω : ω ∉ H.lattice := H.halfPeriod_notMem hj
  have hmω : -ω ∉ H.lattice := fun h => hω (by simpa using neg_mem h)
  obtain ⟨a, ha, hfa⟩ := p23R1_weierstrassSigma_add_mem H.periodPair
    (H.two_mul_halfPeriod_mem hj) hmω
  have hc : DLMF.Weierstrass.weierstrassZeta H.periodPair (-ω + 2 * ω) - DLMF.Weierstrass.weierstrassZeta H.periodPair (-ω) =
      2 * H.eta j := by
    rw [show -ω + 2 * ω = ω by ring, DLMF.Weierstrass.weierstrassZeta_neg]
    simp only [eta, HalfPeriods.weierstrassZeta, ω]; ring
  rw [hc] at hfa
  have hσω : DLMF.Weierstrass.weierstrassSigma H.periodPair ω ≠ 0 :=
    (DLMF.Weierstrass.weierstrassSigma_eq_zero_iff _).not.mpr hω
  have h1 := hfa (-ω)
  rw [show -ω + 2 * ω = ω by ring, DLMF.Weierstrass.weierstrassSigma_neg] at h1
  have ha' : a = -cexp (2 * H.eta j * ω) := by
    have he : cexp (2 * H.eta j * -ω) * cexp (2 * H.eta j * ω) = 1 := by
      rw [← Complex.exp_add]; simp
    have : (a + cexp (2 * H.eta j * ω)) * DLMF.Weierstrass.weierstrassSigma H.periodPair ω = 0 := by
      linear_combination (cexp (2 * H.eta j * ω)) * h1 - a * DLMF.Weierstrass.weierstrassSigma H.periodPair ω * he
    have := (mul_eq_zero.mp this).resolve_right hσω
    linear_combination this
  simp only [HalfPeriods.weierstrassSigma]
  rw [hfa z, ha', mul_add, Complex.exp_add]
  ring

/-- DLMF 23.2.16: `σ'(2ω_j) = -e^{2η_jω_j}`, `j = 1, 2, 3`. -/
@[dlmf 23.2.E16]
theorem deriv_weierstrassSigma_two_mul_halfPeriod {j : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    deriv H.weierstrassSigma (2 * H.halfPeriod j) = -cexp (2 * H.eta j * H.halfPeriod j) := by
  set ω := H.halfPeriod j
  have hfun : (fun y => H.weierstrassSigma (y + 2 * ω)) =
      fun y => -cexp (2 * H.eta j * (y + ω)) * H.weierstrassSigma y :=
    funext fun y => H.weierstrassSigma_add_two_mul_halfPeriod y hj
  have h1 : HasDerivAt (fun y => H.weierstrassSigma (y + 2 * ω))
      (deriv H.weierstrassSigma (2 * ω)) 0 := by
    have := ((DLMF.Weierstrass.differentiable_weierstrassSigma H.periodPair)
      (0 + 2 * ω)).hasDerivAt.comp_add_const 0 (2 * ω)
    simpa using this
  have he : HasDerivAt (fun y => cexp (2 * H.eta j * (y + ω)))
      (cexp (2 * H.eta j * (0 + ω)) * (2 * H.eta j)) 0 := by
    have := (((hasDerivAt_id (0 : ℂ)).add_const ω).const_mul (2 * H.eta j)).cexp
    simpa using this
  have h2 := he.neg.mul (p23R1_hasDerivAt_weierstrassSigma_zero H.periodPair)
  rw [hfun] at h1
  rw [h1.unique h2]
  simp [DLMF.Weierstrass.weierstrassSigma_eq_zero_of_mem H.periodPair (zero_mem _)]

/-! ### Invariants, roots and discriminant (§23.3(i)) -/

/-- Each half-period lies off the lattice; equivalently `e_j` is a finite value of `℘`. -/
theorem e_root_cubic {j : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    4 * H.e j ^ 3 - H.g₂ * H.e j - H.g₃ = 0 := by
  have h := H.periodPair.derivWeierstrassP_sq (H.halfPeriod j) (H.halfPeriod_notMem hj)
  have h0 := H.derivWeierstrassP_halfPeriod hj
  simp only [HalfPeriods.derivWeierstrassP] at h0
  rw [h0] at h
  simp only [e, HalfPeriods.weierstrassP]
  linear_combination -h

/-- DLMF 23.3.3: the lattice roots `e₁, e₂, e₃` satisfy `4z³ - g₂z - g₃ = 0`. -/
@[dlmf 23.3.E3]
theorem e_isRoot (j : ℕ) (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    4 * H.e j ^ 3 - H.g₂ * H.e j - H.g₃ = 0 :=
  H.e_root_cubic hj

/-- `e_k ≠ e_j` whenever `ω_k + ω_j ∉ 𝕃`. -/
lemma p23R1_e_ne {j k : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ)) (hk : k ∈ ({1, 2, 3} : Finset ℕ))
    (hjk : H.halfPeriod k + H.halfPeriod j ∉ H.lattice) : H.e k ≠ H.e j :=
  p23R1_weierstrassP_ne_of_halfLattice H.periodPair (H.halfPeriod_notMem hj)
    (H.two_mul_halfPeriod_mem hj) (H.halfPeriod_notMem hk) hjk

/-- DLMF §23.3(i): the lattice roots `e₁, e₂, e₃` are distinct. -/
@[dlmf 23.3.i]
theorem e_distinct : H.e 1 ≠ H.e 2 ∧ H.e 2 ≠ H.e 3 ∧ H.e 1 ≠ H.e 3 := by
  have hneg : ∀ j ∈ ({1, 2, 3} : Finset ℕ), -H.halfPeriod j ∉ H.lattice := fun j hj h =>
    H.halfPeriod_notMem hj (by simpa using neg_mem h)
  refine ⟨H.p23R1_e_ne (j := 2) (k := 1) (by simp) (by simp) ?_,
    H.p23R1_e_ne (j := 3) (k := 2) (by simp) (by simp) ?_,
    H.p23R1_e_ne (j := 3) (k := 1) (by simp) (by simp) ?_⟩
  · rw [show H.halfPeriod 1 + H.halfPeriod 2 = -H.halfPeriod 3 by simp [ω₂]; ring]
    exact hneg 3 (by simp)
  · rw [show H.halfPeriod 2 + H.halfPeriod 3 = -H.halfPeriod 1 by simp [ω₂]]
    exact hneg 1 (by simp)
  · rw [show H.halfPeriod 1 + H.halfPeriod 3 = -H.halfPeriod 2 by simp [ω₂]; ring]
    exact hneg 2 (by simp)

/-- DLMF 23.3.5: `e₁ + e₂ + e₃ = 0`. -/
@[dlmf 23.3.E5]
theorem e_sum : H.e 1 + H.e 2 + H.e 3 = 0 := by
  obtain ⟨h12, h23, h13⟩ := H.e_distinct
  have r1 := H.e_root_cubic (j := 1) (by simp)
  have r2 := H.e_root_cubic (j := 2) (by simp)
  have r3 := H.e_root_cubic (j := 3) (by simp)
  -- `4(e₁² + e₁e₂ + e₂²) = g₂` and likewise for `(1, 3)`.
  have a12 : 4 * (H.e 1 ^ 2 + H.e 1 * H.e 2 + H.e 2 ^ 2) = H.g₂ := by
    have : (H.e 1 - H.e 2) * (4 * (H.e 1 ^ 2 + H.e 1 * H.e 2 + H.e 2 ^ 2) - H.g₂) = 0 := by
      linear_combination r1 - r2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) h12
    · linear_combination h
  have a13 : 4 * (H.e 1 ^ 2 + H.e 1 * H.e 3 + H.e 3 ^ 2) = H.g₂ := by
    have : (H.e 1 - H.e 3) * (4 * (H.e 1 ^ 2 + H.e 1 * H.e 3 + H.e 3 ^ 2) - H.g₂) = 0 := by
      linear_combination r1 - r3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) h13
    · linear_combination h
  have : (H.e 2 - H.e 3) * (4 * (H.e 1 + H.e 2 + H.e 3)) = 0 := by
    linear_combination a12 - a13
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) h23
  · linear_combination h / 4

/-- `4(e₁² + e₁e₂ + e₂²) = g₂`. -/
lemma wp23_g₂_eq : 4 * (H.e 1 ^ 2 + H.e 1 * H.e 2 + H.e 2 ^ 2) = H.g₂ := by
  obtain ⟨h12, -, -⟩ := H.e_distinct
  have r1 := H.e_root_cubic (j := 1) (by simp)
  have r2 := H.e_root_cubic (j := 2) (by simp)
  have : (H.e 1 - H.e 2) * (4 * (H.e 1 ^ 2 + H.e 1 * H.e 2 + H.e 2 ^ 2) - H.g₂) = 0 := by
    linear_combination r1 - r2
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) h12
  · linear_combination h

/-- DLMF 23.3.6: `g₂ = 2(e₁² + e₂² + e₃²) = -4(e₂e₃ + e₃e₁ + e₁e₂)`. -/
@[dlmf 23.3.E6]
theorem g₂_eq_e : H.g₂ = 2 * (H.e 1 ^ 2 + H.e 2 ^ 2 + H.e 3 ^ 2) ∧
    H.g₂ = -4 * (H.e 2 * H.e 3 + H.e 3 * H.e 1 + H.e 1 * H.e 2) := by
  have hs := H.e_sum
  have hg := H.wp23_g₂_eq
  have h3 : H.e 3 = -H.e 1 - H.e 2 := by linear_combination hs
  rw [h3] at ⊢
  constructor <;> linear_combination -hg

/-- DLMF 23.3.7: `g₃ = 4e₁e₂e₃ = (4/3)(e₁³ + e₂³ + e₃³)`. -/
@[dlmf 23.3.E7]
theorem g₃_eq_e : H.g₃ = 4 * H.e 1 * H.e 2 * H.e 3 ∧
    H.g₃ = 4 / 3 * (H.e 1 ^ 3 + H.e 2 ^ 3 + H.e 3 ^ 3) := by
  have hs := H.e_sum
  have hg := H.wp23_g₂_eq
  have r1 := H.e_root_cubic (j := 1) (by simp)
  have h3 : H.e 3 = -H.e 1 - H.e 2 := by linear_combination hs
  rw [h3]
  constructor
  · linear_combination -r1 + H.e 1 * hg
  · linear_combination -r1 + H.e 1 * hg

/-- DLMF §23.3(i): `4x³ - g₂x - g₃ = 4(x - e₁)(x - e₂)(x - e₃)`. -/
@[dlmf 23.3.i]
theorem cubic_eq_mul (x : ℂ) :
    4 * x ^ 3 - H.g₂ * x - H.g₃ = 4 * (x - H.e 1) * (x - H.e 2) * (x - H.e 3) := by
  have hs := H.e_sum
  have h2 := (H.g₂_eq_e).2
  have h3 := (H.g₃_eq_e).1
  rw [h2, h3]
  linear_combination (4 * x ^ 2) * hs

end HalfPeriods

/-- The discriminant `Δ = g₂³ - 27g₃²` of a lattice (DLMF 23.3.4). -/
@[dlmf 23.3.E4]
def latticeDiscriminant (L : PeriodPair) : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

namespace HalfPeriods

variable (H : HalfPeriods)

/-- DLMF 23.3.4: `Δ = g₂³ - 27g₃² = 16(e₂ - e₃)²(e₃ - e₁)²(e₁ - e₂)²`. -/
@[dlmf 23.3.E4]
theorem latticeDiscriminant_eq :
    latticeDiscriminant H.periodPair =
      16 * (H.e 2 - H.e 3) ^ 2 * (H.e 3 - H.e 1) ^ 2 * (H.e 1 - H.e 2) ^ 2 := by
  have hs := H.e_sum
  have h2 := (H.g₂_eq_e).2
  have h3 := (H.g₃_eq_e).1
  have h3' : H.e 3 = -H.e 1 - H.e 2 := by linear_combination hs
  simp only [latticeDiscriminant]
  change H.g₂ ^ 3 - 27 * H.g₃ ^ 2 = _
  rw [h2, h3, h3']
  ring

/-- DLMF §23.3(i): the discriminant of a lattice is nonzero. -/
@[dlmf 23.3.i]
theorem latticeDiscriminant_ne_zero : latticeDiscriminant H.periodPair ≠ 0 := by
  rw [H.latticeDiscriminant_eq]
  obtain ⟨h12, h23, h13⟩ := H.e_distinct
  have a : H.e 3 - H.e 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h13)
  have b := sub_ne_zero.mpr h12
  have c := sub_ne_zero.mpr h23
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 c)) (pow_ne_zero 2 a))
    (pow_ne_zero 2 b)

/-- DLMF §23.3(i): `g₂`, `g₃` and the set `{e₁, e₂, e₃}` depend only on the lattice, not on
the choice of generators. -/
@[dlmf 23.3.i]
theorem invariants_roots_eq_of_lattice_eq (H' : HalfPeriods) (h : H.lattice = H'.lattice) :
    H.g₂ = H'.g₂ ∧ H.g₃ = H'.g₃ ∧
      ({H.e 1, H.e 2, H.e 3} : Set ℂ) = {H'.e 1, H'.e 2, H'.e 3} := by
  have hG : ∀ n, H.periodPair.G n = H'.periodPair.G n := by
    intro n
    simp only [PeriodPair.G]
    rw [← (Equiv.subtypeEquivRight (fun x => by rw [show H.periodPair.lattice = H'.periodPair.lattice
      from h]) : H.periodPair.lattice ≃ H'.periodPair.lattice).tsum_eq]
    rfl
  have h2 : H.g₂ = H'.g₂ := by simp only [HalfPeriods.g₂, PeriodPair.g₂, hG]
  have h3 : H.g₃ = H'.g₃ := by simp only [HalfPeriods.g₃, PeriodPair.g₃, hG]
  have hroots : ∀ (K : HalfPeriods) (x : ℂ),
      x ∈ ({K.e 1, K.e 2, K.e 3} : Set ℂ) ↔ 4 * x ^ 3 - K.g₂ * x - K.g₃ = 0 := by
    intro K x
    rw [K.cubic_eq_mul]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, mul_eq_zero, sub_eq_zero]
    norm_num [or_assoc]
  refine ⟨h2, h3, Set.ext fun x => ?_⟩
  rw [hroots H, hroots H', h2, h3]

end HalfPeriods

/-! ### The invariants form `℘(z; g₂, g₃)` (DLMF 23.3.8) -/

/-- Identity under the stated parameter and domain assumptions: `L.G n = L'.G n`. -/
theorem wp23_G_eq_of_lattice_eq (L L' : PeriodPair) (h : L.lattice = L'.lattice) (n : ℕ) :
    L.G n = L'.G n := by
  simp only [PeriodPair.G]
  rw [← (Equiv.subtypeEquivRight (fun x => by rw [h]) : L.lattice ≃ L'.lattice).tsum_eq]
  rfl

/-- Nonvanishing under the stated hypotheses: `L.ω₁ ≠ 0`. -/
lemma wp23_ω₁_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  simpa using L.indep.ne_zero 0

/-- Nonvanishing under the stated hypotheses: `(L.ω₂ / L.ω₁).im ≠ 0`. -/
lemma wp23_im_div_ne_zero (L : PeriodPair) : (L.ω₂ / L.ω₁).im ≠ 0 := by
  intro him
  have h1 := wp23_ω₁_ne_zero L
  have hq : L.ω₂ / L.ω₁ = ((L.ω₂ / L.ω₁).re : ℂ) := Complex.ext (by simp) (by simp [him])
  have h2 : L.ω₂ = ((L.ω₂ / L.ω₁).re : ℂ) * L.ω₁ := by
    rw [← hq]; field_simp
  have := LinearIndependent.pair_iff.mp L.indep ((L.ω₂ / L.ω₁).re) (-1)
    (by rw [Complex.real_smul, Complex.real_smul, ← h2]; simp)
  norm_num at this

/-- DLMF half-periods for an arbitrary Mathlib period pair: `ω₁ = L.ω₁/2` and
`ω₃ = ±L.ω₂/2`, the sign chosen so that `ℑ(ω₃/ω₁) > 0`. -/
def halfPeriodsOf (L : PeriodPair) : HalfPeriods :=
  if h : 0 < (L.ω₂ / L.ω₁).im then
    ⟨L.ω₁ / 2, L.ω₂ / 2, by simpa using wp23_ω₁_ne_zero L, by
      rwa [div_div_div_cancel_right₀ two_ne_zero]⟩
  else
    ⟨L.ω₁ / 2, -L.ω₂ / 2, by simpa using wp23_ω₁_ne_zero L, by
      rw [div_div_div_cancel_right₀ two_ne_zero, neg_div, neg_im]
      have := wp23_im_div_ne_zero L
      exact neg_pos.mpr (lt_of_le_of_ne (not_lt.mp h) this)⟩

/-- Identity under the stated parameter and domain assumptions: `(halfPeriodsOf L).lattice =
L.lattice`. -/
theorem halfPeriodsOf_lattice (L : PeriodPair) : (halfPeriodsOf L).lattice = L.lattice := by
  unfold halfPeriodsOf
  split_ifs with h
  · simp only [HalfPeriods.lattice, PeriodPair.lattice, HalfPeriods.periodPair_ω₁,
      HalfPeriods.periodPair_ω₂]
    rw [show 2 * (L.ω₁ / 2) = L.ω₁ by ring, show 2 * (L.ω₂ / 2) = L.ω₂ by ring]
  · simp only [HalfPeriods.lattice, PeriodPair.lattice, HalfPeriods.periodPair_ω₁,
      HalfPeriods.periodPair_ω₂]
    rw [show 2 * (L.ω₁ / 2) = L.ω₁ by ring, show 2 * (-L.ω₂ / 2) = -L.ω₂ by ring]
    apply le_antisymm <;> refine Submodule.span_le.mpr ?_ <;> rintro x (rfl | rfl)
    · exact Submodule.subset_span (by simp)
    · exact neg_mem (Submodule.subset_span (by simp))
    · exact Submodule.subset_span (by simp)
    · simpa using neg_mem (Submodule.subset_span (R := ℤ) (s := {L.ω₁, -L.ω₂})
        (show -L.ω₂ ∈ ({L.ω₁, -L.ω₂} : Set ℂ) by simp))

/-- DLMF §23.3(i): the discriminant of every lattice is nonzero. -/
@[dlmf 23.3.i]
theorem latticeDiscriminant_ne_zero' (L : PeriodPair) : latticeDiscriminant L ≠ 0 := by
  have h := (halfPeriodsOf L).latticeDiscriminant_ne_zero
  have hl := halfPeriodsOf_lattice L
  simpa [latticeDiscriminant, PeriodPair.g₂, PeriodPair.g₃,
    wp23_G_eq_of_lattice_eq _ _ hl] using h

/-! ### Homogeneity of the invariants (§23.10(iv)) -/

/-- The period pair `c𝕃` with periods `cω₁, cω₂` (`c ≠ 0`). -/
def scalePeriodPair (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) : PeriodPair :=
  ⟨c * L.ω₁, c * L.ω₂, by
    refine LinearIndependent.pair_iff.mpr fun s t h => ?_
    refine LinearIndependent.pair_iff.mp L.indep s t ?_
    have : c * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← h]; simp only [Complex.real_smul]; ring
    simpa [hc] using this⟩

/-- Formula under the stated hypotheses: `z ∈ (scalePeriodPair c hc L).lattice ↔ z / c ∈
L.lattice`. -/
theorem wp23_mem_scale_iff (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) {z : ℂ} :
    z ∈ (scalePeriodPair c hc L).lattice ↔ z / c ∈ L.lattice := by
  simp only [PeriodPair.mem_lattice, scalePeriodPair]
  constructor
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by field_simp⟩
  · rintro ⟨m, n, h⟩; exact ⟨m, n, by rw [← mul_div_cancel₀ z hc, ← h]; ring⟩

/-- Multiplication by `c` as a bijection `𝕃 ≃ c𝕃`. -/
def wp23_scaleEquiv (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) :
    L.lattice ≃ (scalePeriodPair c hc L).lattice where
  toFun l := ⟨c * l, (wp23_mem_scale_iff c hc L).mpr (by simp [hc])⟩
  invFun l := ⟨l / c, (wp23_mem_scale_iff c hc L).mp l.2⟩
  left_inv l := by ext; simp [hc]
  right_inv l := by ext; simp [mul_div_cancel₀ _ hc]

/-- `G_k(c𝕃) = c^{-k}G_k(𝕃)`. -/
lemma wp23_G_scale (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) (k : ℕ) :
    (scalePeriodPair c hc L).G k = c⁻¹ ^ k * L.G k := by
  simp only [PeriodPair.G]
  rw [← (wp23_scaleEquiv c hc L).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  simp only [wp23_scaleEquiv, Equiv.coe_fn_mk]
  rw [mul_pow, mul_inv, inv_pow]

/-- DLMF §23.10(iv): replacing `𝕃` by `c𝕃` divides `g₂` by `c⁴` and `g₃` by `c⁶`. -/
@[dlmf 23.10.iv]
theorem invariants_scale (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) :
    (scalePeriodPair c hc L).g₂ = L.g₂ / c ^ 4 ∧ (scalePeriodPair c hc L).g₃ = L.g₃ / c ^ 6 := by
  simp only [PeriodPair.g₂, PeriodPair.g₃, wp23_G_scale]
  constructor <;> field_simp

section p23R1Disc

open PeriodPair ModularForm EisensteinSeries UpperHalfPlane

/-- The lattice sums of the lattice `ℤ + ℤτ` are the full Eisenstein sums. -/
theorem p23R1_G_ofTau (τ : ℍ) (k : ℕ) :
    (HalfPeriods.ofTau (1 / 2) (by norm_num) τ).periodPair.G k =
      ∑' v : Fin 2 → ℤ, eisSummand k v τ := by
  set L := (HalfPeriods.ofTau (1 / 2) (by norm_num) τ).periodPair
  simp only [PeriodPair.G]
  rw [← ((finTwoArrowEquiv ℤ).trans
    ((Equiv.prodComm ℤ ℤ).trans L.latticeEquivProd.toEquiv.symm)).tsum_eq]
  refine tsum_congr fun v => ?_
  simp only [Equiv.trans_apply, eisSummand]
  rw [show ((L.latticeEquivProd.toEquiv.symm ((Equiv.prodComm ℤ ℤ) (finTwoArrowEquiv ℤ v)) :
    L.lattice) : ℂ) = _ from L.latticeEquiv_symm_apply _]
  simp [L, HalfPeriods.periodPair, _root_.zpow_neg, zpow_natCast]
  ring_nf

/-- `B₆ = 1/42`. -/
lemma p23R1_bernoulli_six : bernoulli 6 = 1 / 42 := by decide +kernel

/-- `ζ(6) = π⁶/945`. -/
theorem p23R1_riemannZeta_six : riemannZeta 6 = π ^ 6 / 945 := by
  have := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  norm_num [p23R1_bernoulli_six, Nat.factorial] at this
  rw [this]; ring

/-- `G_k(ℤ + ℤτ) = 2ζ(k)E_k(τ)` with Mathlib's normalised Eisenstein series. -/
theorem p23R1_G_eq_E (τ : ℍ) {k : ℕ} (hk : 3 ≤ k) :
    (HalfPeriods.ofTau (1 / 2) (by norm_num) τ).periodPair.G k =
      2 * riemannZeta k * E hk τ := by
  rw [p23R1_G_ofTau, tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk]
  have : (E hk : ℍ → ℂ) τ = (1 / 2 : ℂ) * eisensteinSeries 0 k τ := rfl
  rw [this]
  ring

end p23R1Disc

open ModularForm EisensteinSeries UpperHalfPlane in
/-- DLMF §23.3(i): if `g₂³ ≠ 27g₃²` there is a lattice with invariants `g₂, g₃`.  Proved from the
surjectivity of the modular invariant `E₄³/(E₄³ - E₆²)` and the homogeneity of the invariants. -/
@[dlmf 23.3.i]
theorem exists_periodPair_invariants (g₂ g₃ : ℂ) (h : g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0) :
    ∃ L : PeriodPair, L.g₂ = g₂ ∧ L.g₃ = g₃ := by
  obtain ⟨τ, hτ⟩ := p3w_exists_E₄_cube_div_eq (g₂ ^ 3 / (g₂ ^ 3 - 27 * g₃ ^ 2))
  set L0 := (HalfPeriods.ofTau (1 / 2) (by norm_num) τ).periodPair with hL0
  have z4 : riemannZeta ((4 : ℕ) : ℂ) = π ^ 4 / 90 := by exact_mod_cast riemannZeta_four
  have z6 : riemannZeta ((6 : ℕ) : ℂ) = π ^ 6 / 945 := by exact_mod_cast p23R1_riemannZeta_six
  have ha : L0.g₂ = 4 * π ^ 4 / 3 * E₄ τ := by
    rw [PeriodPair.g₂, p23R1_G_eq_E τ (k := 4) (by norm_num), z4]; ring
  have hb : L0.g₃ = 8 * π ^ 6 / 27 * E₆ τ := by
    rw [PeriodPair.g₃, p23R1_G_eq_E τ (k := 6) (by norm_num), z6]; ring
  have hD := p3w_E₄_cube_sub_E₆_sq_ne_zero τ
  have hΔ0 : L0.g₂ ^ 3 - 27 * L0.g₃ ^ 2 ≠ 0 := latticeDiscriminant_ne_zero' L0
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key : L0.g₂ ^ 3 * g₃ ^ 2 = g₂ ^ 3 * L0.g₃ ^ 2 := by
    simp only [p3wJ] at hτ
    rw [div_eq_div_iff hD h] at hτ
    rw [ha, hb]
    linear_combination (-(64 : ℂ) * π ^ 12 / 729) * hτ
  -- a scaling factor `u = c⁻²`
  obtain ⟨u, hu0, hu2, hu3⟩ : ∃ u : ℂ, u ≠ 0 ∧ u ^ 2 * L0.g₂ = g₂ ∧ u ^ 3 * L0.g₃ = g₃ := by
    by_cases h2 : g₂ = 0
    · have h3 : g₃ ≠ 0 := by rintro rfl; simp [h2] at h
      have ha0 : L0.g₂ = 0 := by
        rw [h2] at key; simpa [h3] using key
      have hb0 : L0.g₃ ≠ 0 := by rintro hb0; simp [ha0, hb0] at hΔ0
      obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (g₃ / L0.g₃) (by norm_num : 0 < 3)
      refine ⟨u, ?_, by simp [ha0, h2], by rw [hu]; field_simp⟩
      rintro rfl; exact div_ne_zero h3 hb0 (by simpa using hu.symm)
    by_cases h3 : g₃ = 0
    · have hb0 : L0.g₃ = 0 := by
        rw [h3] at key; simpa [h2] using key.symm
      have ha0 : L0.g₂ ≠ 0 := by rintro ha0; simp [ha0, hb0] at hΔ0
      obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (g₂ / L0.g₂) (by norm_num : 0 < 2)
      refine ⟨u, ?_, by rw [hu]; field_simp, by simp [hb0, h3]⟩
      rintro rfl; exact div_ne_zero h2 ha0 (by simpa using hu.symm)
    have ha0 : L0.g₂ ≠ 0 := by
      rintro ha0
      have : L0.g₃ = 0 := by simpa [ha0, h2] using key
      simp [ha0, this] at hΔ0
    have hb0 : L0.g₃ ≠ 0 := by
      rintro hb0
      have : L0.g₂ = 0 := by simpa [hb0, h3] using key
      simp [hb0, this] at hΔ0
    refine ⟨g₃ * L0.g₂ / (g₂ * L0.g₃), by simp [h2, h3, ha0, hb0], ?_, ?_⟩
    · rw [show (g₃ * L0.g₂ / (g₂ * L0.g₃)) ^ 2 * L0.g₂ =
          g₃ ^ 2 * L0.g₂ ^ 3 / (g₂ ^ 2 * L0.g₃ ^ 2) by ring,
        div_eq_iff (by simp [h2, hb0])]
      linear_combination key
    · rw [show (g₃ * L0.g₂ / (g₂ * L0.g₃)) ^ 3 * L0.g₃ =
          g₃ ^ 3 * L0.g₂ ^ 3 * L0.g₃ / (g₂ ^ 3 * L0.g₃ ^ 3) by ring,
        div_eq_iff (by simp [h2, hb0])]
      linear_combination (g₃ * L0.g₃) * key
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u⁻¹ (by norm_num : 0 < 2)
  have hc0 : c ≠ 0 := by rintro rfl; exact hu0 (by simpa using hc.symm)
  obtain ⟨s2, s3⟩ := invariants_scale c hc0 L0
  refine ⟨scalePeriodPair c hc0 L0, ?_, ?_⟩
  · rw [s2, show c ^ 4 = (c ^ 2) ^ 2 by ring, hc, ← hu2]; field_simp
  · rw [s3, show c ^ 6 = (c ^ 2) ^ 3 by ring, hc, ← hu3]; field_simp

section p23R1Uniq

open Filter Topology

/-- The differential equation of `℘` in terms of the regular part `p = ℘ - 1/z²` near `0`:
`(z³p' - 2)² = 4(1 + z²p)³ - g₂z⁴(1 + z²p) - g₃z⁶`. -/
lemma p23R1_ode_regularPart (L : PeriodPair) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), (z ^ 3 * deriv (fun w => ℘[L] w - 1 / w ^ 2) z - 2) ^ 2 =
      4 * (1 + z ^ 2 * (℘[L] z - 1 / z ^ 2)) ^ 3 -
        L.g₂ * z ^ 4 * (1 + z ^ 2 * (℘[L] z - 1 / z ^ 2)) - L.g₃ * z ^ 6 := by
  filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
    self_mem_nhdsWithin] with z hz hz0
  have hz0' : z ≠ 0 := hz0
  have hzL : z ∉ L.lattice := fun h => hz ⟨h, hz0⟩
  have hU : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have h1 : HasDerivAt ℘[L] (℘'[L] z) z := by
    have := (L.differentiableOn_weierstrassP z hzL).differentiableAt (hU.mem_nhds hzL)
    simpa using this.hasDerivAt
  have h2 : HasDerivAt (fun w : ℂ => 1 / w ^ 2) (-(2 * z) / (z ^ 2) ^ 2) z := by
    have := (hasDerivAt_pow 2 z).inv (pow_ne_zero 2 hz0')
    convert this using 1
    · funext w; simp [one_div]
    · simp
  have hd : deriv (fun w => ℘[L] w - 1 / w ^ 2) z = ℘'[L] z + 2 / z ^ 3 := by
    rw [(h1.fun_sub h2).deriv]
    field_simp
    ring
  have ode := L.derivWeierstrassP_sq z hzL
  rw [hd]
  have e1 : z ^ 3 * (℘'[L] z + 2 / z ^ 3) - 2 = z ^ 3 * ℘'[L] z := by field_simp; ring
  have e2 : 1 + z ^ 2 * (℘[L] z - 1 / z ^ 2) = z ^ 2 * ℘[L] z := by field_simp; ring
  rw [e1, e2]
  linear_combination z ^ 6 * ode

/-- Two lattices with the same invariants have the same `℘` near `0`. -/
lemma p23R1_weierstrassP_eventuallyEq_of_invariants (L L' : PeriodPair) (h₂ : L.g₂ = L'.g₂)
    (h₃ : L.g₃ = L'.g₃) :
    ∀ᶠ z in 𝓝 (0 : ℂ), ℘[L] z - 1 / z ^ 2 - (℘[L'] z - 1 / z ^ 2) = 0 := by
  set p : ℂ → ℂ := fun w => ℘[L] w - 1 / w ^ 2 with hp
  set q : ℂ → ℂ := fun w => ℘[L'] w - 1 / w ^ 2 with hq
  have hpa : AnalyticAt ℂ p 0 := by
    have := analyticAt_weierstrassP_sub L (zero_mem _)
    simp only [sub_zero] at this; exact this
  have hqa : AnalyticAt ℂ q 0 := by
    have := analyticAt_weierstrassP_sub L' (zero_mem _)
    simp only [sub_zero] at this; exact this
  set d : ℂ → ℂ := fun w => p w - q w with hd
  have hda : AnalyticAt ℂ d 0 := hpa.sub hqa
  show ∀ᶠ z in 𝓝 (0 : ℂ), d z = 0
  rw [← analyticOrderAt_eq_top]
  by_contra htop
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  obtain ⟨g, hga, hg0, hgd⟩ := (hda.analyticOrderAt_eq_natCast (n := n)).mp hn.symm
  simp only [sub_zero, smul_eq_mul] at hgd
  -- `z d'(z) = zⁿ (n g + z g')` near `0`.
  have hzd : ∀ᶠ z in 𝓝 (0 : ℂ), z * deriv d z = z ^ n * (n * g z + z * deriv g z) := by
    filter_upwards [hgd.eventually_nhds, hga.eventually_analyticAt] with z hz hgz
    rw [EventuallyEq.deriv_eq hz]
    rw [deriv_fun_mul (by fun_prop) hgz.differentiableAt, deriv_pow_field]
    rcases n with _ | m
    · simp
    · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
      ring
  -- the two differential equations
  have hP := p23R1_ode_regularPart L
  have hQ := p23R1_ode_regularPart L'
  set A : ℂ → ℂ := fun z => z ^ 3 * (deriv p z + deriv q z) - 4
  set B : ℂ → ℂ := fun z => 4 * ((1 + z ^ 2 * p z) ^ 2 + (1 + z ^ 2 * p z) * (1 + z ^ 2 * q z) +
    (1 + z ^ 2 * q z) ^ 2) - L.g₂ * z ^ 4
  have hbr : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      (n * g z + z * deriv g z) * A z - g z * B z = 0 := by
    filter_upwards [hP, hQ, nhdsWithin_le_nhds hzd, nhdsWithin_le_nhds hgd,
      self_mem_nhdsWithin, nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      nhdsWithin_le_nhds (L'.compl_lattice_sdiff_singleton_mem_nhds 0)]
      with z hPz hQz hzdz hgdz hz0 hzL hzL'
    have hz0' : z ≠ 0 := hz0
    have hdiff : ∀ M : PeriodPair, z ∉ M.lattice →
        DifferentiableAt ℂ (fun w => ℘[M] w - 1 / w ^ 2) z := by
      intro M hM
      have hU : IsOpen (M.latticeᶜ : Set ℂ) := M.isClosed_lattice.isOpen_compl
      have := (M.differentiableOn_weierstrassP z hM).differentiableAt (hU.mem_nhds hM)
      exact this.sub (by fun_prop (disch := exact pow_ne_zero 2 hz0'))
    have hdd : deriv d z = deriv p z - deriv q z :=
      deriv_sub (hdiff L fun h => hzL ⟨h, hz0⟩) (hdiff L' fun h => hzL' ⟨h, hz0⟩)
    have key : z ^ 2 * (z * deriv d z) * A z = z ^ 2 * d z * B z := by
      rw [hdd]
      simp only [A, B, d]
      rw [← h₂, ← h₃] at hQz
      linear_combination hPz - hQz
    rw [hzdz, hgdz] at key
    have hzn : z ^ 2 * z ^ n ≠ 0 := mul_ne_zero (pow_ne_zero _ hz0') (pow_ne_zero _ hz0')
    have : z ^ 2 * z ^ n * ((n * g z + z * deriv g z) * A z - g z * B z) = 0 := by
      linear_combination key
    exact (mul_eq_zero.mp this).resolve_left hzn
  have hcont : ContinuousAt (fun z => (n * g z + z * deriv g z) * A z - g z * B z) 0 := by
    have c1 := hga.continuousAt
    have c2 := hga.deriv.continuousAt
    have c3 := hpa.deriv.continuousAt
    have c4 := hqa.deriv.continuousAt
    have c5 := hpa.continuousAt
    have c6 := hqa.continuousAt
    simp only [A, B]
    fun_prop
  have h0 : (n * g 0 + 0 * deriv g 0) * A 0 - g 0 * B 0 = 0 :=
    tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (hbr.mono fun z hz => hz.symm))
  simp only [A, B] at h0
  have : (4 * (n : ℂ) + 12) * g 0 = 0 := by linear_combination -h0
  rcases mul_eq_zero.mp this with h | h
  · have : (4 * (n : ℝ) + 12) = 0 := by exact_mod_cast h
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  · exact hg0 h

/-- If two lattices have the same `℘` near `0`, the first is contained in the second. -/
theorem p3w_lattice_le_of_eventuallyEq (L L' : PeriodPair)
    (hev' : ∀ᶠ z in 𝓝 (0 : ℂ), ℘[L] z = ℘[L'] z) : L.lattice ≤ L'.lattice := by
  set U : Set ℂ := ((L.lattice : Set ℂ) ∪ L'.lattice)ᶜ with hUdef
  have hcount : ∀ M : PeriodPair, (M.lattice : Set ℂ).Countable := fun M => by
    have : Countable M.lattice := M.latticeEquivProd.toEquiv.injective.countable
    exact Set.countable_coe_iff.mp this
  have hUc : IsPreconnected U :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp [rank_real_complex])
      ((hcount L).union (hcount L'))).isPreconnected
  have hUo : IsOpen U := (L.isClosed_lattice.union L'.isClosed_lattice).isOpen_compl
  have hFa : AnalyticOnNhd ℂ (fun z => ℘[L] z - ℘[L'] z) U := fun z hz => by
    simp only [hUdef, Set.compl_union, Set.mem_inter_iff, Set.mem_compl_iff,
      SetLike.mem_coe] at hz
    exact (L.analyticOnNhd_weierstrassP z hz.1).sub (L'.analyticOnNhd_weierstrassP z hz.2)
  -- a point of `U` near `0` where `℘_L = ℘_{L'}` nearby
  have hpt : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ U ∧ ∀ᶠ y in 𝓝 z, ℘[L] y = ℘[L'] y := by
    filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      nhdsWithin_le_nhds (L'.compl_lattice_sdiff_singleton_mem_nhds 0), self_mem_nhdsWithin,
      nhdsWithin_le_nhds hev'.eventually_nhds] with z h1 h2 h0 h3
    refine ⟨?_, h3⟩
    simp only [hUdef, Set.compl_union, Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe]
    exact ⟨fun h => h1 ⟨h, h0⟩, fun h => h2 ⟨h, h0⟩⟩
  obtain ⟨z₁, hz₁U, hz₁⟩ := hpt.exists
  have hzero : Set.EqOn (fun z => ℘[L] z - ℘[L'] z) 0 U :=
    hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hz₁U
      (hz₁.mono fun y hy => by simp [hy])
  intro l hl
  by_contra hl'
  have hord := L.order_weierstrassP l hl
  have hloc : ℘[L] =ᶠ[𝓝[≠] l] ℘[L'] := by
    filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds l),
      nhdsWithin_le_nhds (L'.isClosed_lattice.isOpen_compl.mem_nhds hl'), self_mem_nhdsWithin]
      with z h1 h2 h0
    have hzU : z ∈ U := by
      simp only [hUdef, Set.compl_union, Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe]
      exact ⟨fun h => h1 ⟨h, h0⟩, h2⟩
    exact sub_eq_zero.mp (hzero hzU)
  rw [meromorphicOrderAt_congr hloc] at hord
  have := (L'.analyticOnNhd_weierstrassP l hl').meromorphicOrderAt_nonneg
  rw [hord] at this
  exact absurd this (by decide)

/-- A lattice with the same `℘` near `0` as another is contained in it. -/
lemma p23R1_lattice_le_of_invariants (L L' : PeriodPair) (h₂ : L.g₂ = L'.g₂)
    (h₃ : L.g₃ = L'.g₃) : L.lattice ≤ L'.lattice := by
  have hev := p23R1_weierstrassP_eventuallyEq_of_invariants L L' h₂ h₃
  exact p3w_lattice_le_of_eventuallyEq L L' (hev.mono fun z hz => by linear_combination hz)

end p23R1Uniq

/-- DLMF §23.3(i): the lattice is uniquely determined by its invariants. -/
@[dlmf 23.3.i]
theorem lattice_eq_of_invariants_eq (L L' : PeriodPair) (h₂ : L.g₂ = L'.g₂) (h₃ : L.g₃ = L'.g₃) :
    L.lattice = L'.lattice :=
  le_antisymm (p23R1_lattice_le_of_invariants L L' h₂ h₃)
    (p23R1_lattice_le_of_invariants L' L h₂.symm h₃.symm)

/-- The square lattice with half-periods `1, i`, used to see that `PeriodPair` is nonempty. -/
def wp23_squareHalfPeriods : HalfPeriods := ⟨1, I, one_ne_zero, by simp⟩

/-- The square lattice supplies a complex period pair. -/
instance : Nonempty PeriodPair := ⟨wp23_squareHalfPeriods.periodPair⟩

/-- A chosen period pair with invariants `g₂, g₃` (junk `PeriodPair` when none exists, i.e.
when `g₂³ = 27g₃²`). Used to define the invariants form of the Weierstrass functions. -/
def periodPairOfInvariants (g₂ g₃ : ℂ) : PeriodPair :=
  Classical.epsilon fun L : PeriodPair ↦ L.g₂ = g₂ ∧ L.g₃ = g₃

/-- `℘(z; g₂, g₃)` (DLMF 23.3.8): `℘(z|𝕃)` for the lattice with invariants `g₂, g₃`; DLMF
assumes `g₂³ ≠ 27g₃²`. -/
@[dlmf 23.3.E8]
def weierstrassPInvariants (g₂ g₃ z : ℂ) : ℂ := ℘[periodPairOfInvariants g₂ g₃] z

/-- `ζ(z; g₂, g₃)` (DLMF §23.3(i)). -/
@[dlmf 23.3.i]
def weierstrassZetaInvariants (g₂ g₃ z : ℂ) : ℂ := weierstrassZeta (periodPairOfInvariants g₂ g₃) z

/-- `σ(z; g₂, g₃)` (DLMF §23.3(i)). -/
@[dlmf 23.3.i]
def weierstrassSigmaInvariants (g₂ g₃ z : ℂ) : ℂ :=
  weierstrassSigma (periodPairOfInvariants g₂ g₃) z

/-- Identity under the stated parameter and domain assumptions: `(periodPairOfInvariants g₂ g₃).g₂
= g₂ ∧ (periodPairOfInvariants g₂ g₃).g₃ = g₃`. -/
theorem periodPairOfInvariants_spec (g₂ g₃ : ℂ) (h : g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0) :
    (periodPairOfInvariants g₂ g₃).g₂ = g₂ ∧ (periodPairOfInvariants g₂ g₃).g₃ = g₃ := by
  unfold periodPairOfInvariants
  exact Classical.epsilon_spec (exists_periodPair_invariants g₂ g₃ h)

/-- Identity under the stated parameter and domain assumptions: `℘[L] z = ℘[L'] z`. -/
theorem wp23_weierstrassP_eq_of_lattice_eq (L L' : PeriodPair) (h : L.lattice = L'.lattice)
    (z : ℂ) : ℘[L] z = ℘[L'] z := by
  simp only [PeriodPair.weierstrassP]
  rw [← (Equiv.subtypeEquivRight (fun x => by rw [h]) : L.lattice ≃ L'.lattice).tsum_eq]
  rfl

/-- Identity under the stated parameter and domain assumptions: `weierstrassZeta L z =
weierstrassZeta L' z`. -/
theorem wp23_weierstrassZeta_eq_of_lattice_eq (L L' : PeriodPair) (h : L.lattice = L'.lattice)
    (z : ℂ) : weierstrassZeta L z = weierstrassZeta L' z := by
  simp only [weierstrassZeta]
  rw [← (Equiv.subtypeEquivRight (fun x => by rw [h]) : L.lattice ≃ L'.lattice).tsum_eq]
  rfl

/-- Identity under the stated parameter and domain assumptions: `weierstrassSigma L z =
weierstrassSigma L' z`. -/
lemma wp23_weierstrassSigma_eq_of_lattice_eq (L L' : PeriodPair) (h : L.lattice = L'.lattice)
    (z : ℂ) : weierstrassSigma L z = weierstrassSigma L' z := by
  simp only [weierstrassSigma]
  rw [← (Equiv.subtypeEquivRight (fun x => by rw [h]) : L.lattice ≃ L'.lattice).tprod_eq]
  rfl

/-- DLMF 23.3.8: `℘(z; g₂, g₃) = ℘(z|𝕃)` for every lattice `𝕃` with invariants `g₂, g₃`. -/
@[dlmf 23.3.E8]
theorem weierstrassPInvariants_eq (L : PeriodPair) (z : ℂ) :
    weierstrassPInvariants L.g₂ L.g₃ z = ℘[L] z := by
  have hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := latticeDiscriminant_ne_zero' L
  obtain ⟨h₂, h₃⟩ := periodPairOfInvariants_spec L.g₂ L.g₃ hΔ
  exact wp23_weierstrassP_eq_of_lattice_eq _ _ (lattice_eq_of_invariants_eq _ _ h₂ h₃) z

/-- DLMF §23.3(i): `σ(z; g₂, g₃)` is an entire function of `(z, g₂, g₃)` (restricted to
`g₂³ ≠ 27g₃²` it is the invariants form of `σ`). -/
@[dlmf 23.3.i]
theorem exists_entire_weierstrassSigmaInvariants :
    ∃ F : ℂ × ℂ × ℂ → ℂ, AnalyticOnNhd ℂ F Set.univ ∧
      ∀ g₂ g₃ z, g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0 → F (z, g₂, g₃) = weierstrassSigmaInvariants g₂ g₃ z := by
  sorry

end DLMF.Weierstrass

end
end
