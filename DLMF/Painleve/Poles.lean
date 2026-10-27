/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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
# Poles of meromorphic Painlevé II solutions

The leading-order pole analysis in Beals–Wong §15.3 follows from Mathlib's
meromorphic orders and their behavior under differentiation and ring operations.
Meromorphicity at the point is an explicit hypothesis; these results do not
assert the global Painlevé property.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology

namespace DLMF.Painleve

/-- Every pole of a meromorphic PII solution is simple, Beals–Wong §15.3. The
equation is only needed in a punctured neighborhood of the pole. -/
theorem pole_order_eq_neg_one {u : ℂ → ℂ} {c x₀ : ℂ}
    (hu : MeromorphicAt u x₀) (hp : meromorphicOrderAt u x₀ < 0)
    (hode : ∀ᶠ x in 𝓝[≠] x₀, deriv (deriv u) x = 2 * u x ^ 3 + x * u x - c) :
    meromorphicOrderAt u x₀ = (-1 : ℤ) := by
  have htop : meromorphicOrderAt u x₀ ≠ ⊤ := ne_of_lt (hp.trans_le le_top)
  lift meromorphicOrderAt u x₀ to ℤ using htop with n hn
  have hnneg : n < 0 := by exact_mod_cast hp
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hnneg.ne
  have hn1 : ((n - 1 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (show n - 1 ≠ 0 by omega)
  have hd := meromorphicOrderAt_deriv_eq_sub_one hn0 hn.symm
  have hdd := meromorphicOrderAt_deriv_eq_sub_one hn1 hd
  have hpow : meromorphicOrderAt (fun x => 2 * u x ^ 3) x₀ = ((3 * n : ℤ) : WithTop ℤ) := by
    rw [show (fun x => 2 * u x ^ 3) = (fun _ => (2 : ℂ)) * (u ^ 3) from rfl,
      meromorphicOrderAt_mul_of_ne_zero (by fun_prop) (by norm_num), meromorphicOrderAt_pow hu,
      ← hn]
    norm_cast
  have hxord : 0 ≤ meromorphicOrderAt (fun x : ℂ => x) x₀ :=
    (analyticAt_id : AnalyticAt ℂ (fun x : ℂ => x) x₀).meromorphicOrderAt_nonneg
  have hcorder : 0 ≤ meromorphicOrderAt (fun _ : ℂ => -c) x₀ :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => -c) x₀).meromorphicOrderAt_nonneg
  have hprod : (n : WithTop ℤ) ≤ meromorphicOrderAt (fun x => x * u x) x₀ := by
    rw [show (fun x => x * u x) = (fun x : ℂ => x) * u from rfl,
      meromorphicOrderAt_mul (by fun_prop) hu, ← hn]
    simpa only [zero_add, add_zero, add_comm] using add_le_add_right hxord (n : WithTop ℤ)
  have hrest : (n : WithTop ℤ) ≤ meromorphicOrderAt (fun x => x * u x - c) x₀ := by
    have he := meromorphicOrderAt_add ((show MeromorphicAt (fun x : ℂ => x) x₀ by fun_prop).mul hu)
      (show MeromorphicAt (fun _ : ℂ => -c) x₀ by fun_prop)
    apply le_trans (le_min hprod (le_trans (by exact_mod_cast hnneg.le) hcorder))
    simpa only [Pi.add_def, Pi.mul_def, sub_eq_add_neg] using he
  have hlt : meromorphicOrderAt (fun x => 2 * u x ^ 3) x₀ <
      meromorphicOrderAt (fun x => x * u x - c) x₀ := by
    rw [hpow]
    exact lt_of_lt_of_le (by exact_mod_cast (show 3 * n < n by omega)) hrest
  have hrhs : meromorphicOrderAt (fun x => 2 * u x ^ 3 + x * u x - c) x₀ =
      ((3 * n : ℤ) : WithTop ℤ) := by
    have he := meromorphicOrderAt_add_eq_left_of_lt
      (show MeromorphicAt (fun x => x * u x - c) x₀ by fun_prop) hlt
    simpa only [Pi.add_def, add_sub_assoc, hpow] using he
  have he := meromorphicOrderAt_congr hode
  rw [hdd, hrhs] at he
  have hnrel : n - 1 - 1 = 3 * n := by exact_mod_cast he
  have hneq : n = -1 := by omega
  exact_mod_cast hneq

/-- A meromorphic Painlevé II pole has residue `+1` or `-1`: its local analytic
numerator in `u(z)=g(z)/(z-x₀)` has value `±1` at the pole. -/
theorem pole_analytic_factor {u : ℂ → ℂ} {c x₀ : ℂ}
    (hu : MeromorphicAt u x₀) (hp : meromorphicOrderAt u x₀ < 0)
    (hode : ∀ᶠ x in 𝓝[≠] x₀, deriv (deriv u) x = 2 * u x ^ 3 + x * u x - c) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g x₀ ∧ (g x₀ = 1 ∨ g x₀ = -1) ∧
      u =ᶠ[𝓝[≠] x₀] fun z => g z / (z - x₀) := by
  obtain ⟨g, hg, hg0, hfac⟩ := (meromorphicOrderAt_eq_int_iff hu).mp
    (pole_order_eq_neg_one hu hp hode)
  have heq : u =ᶠ[𝓝[≠] x₀] fun z => g z / (z - x₀) := by
    filter_upwards [hfac] with z hz
    simpa only [zpow_neg_one, smul_eq_mul, div_eq_mul_inv, mul_comm] using hz
  let f (z : ℂ) := g z / (z - x₀)
  let v (z : ℂ) := (deriv g z * (z - x₀) - g z) / (z - x₀) ^ 2
  have hnear : ∀ᶠ z in 𝓝[≠] x₀, AnalyticAt ℂ g z :=
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hfirst {z : ℂ} (hgz : AnalyticAt ℂ g z) (hz : z - x₀ ≠ 0) : HasDerivAt f (v z) z := by
    exact (hgz.differentiableAt.hasDerivAt.div ((hasDerivAt_id z).sub_const x₀) hz).congr_deriv
      (by dsimp only [v, id_eq]; ring)
  have hdu : deriv u =ᶠ[𝓝[≠] x₀] v := by
    filter_upwards [heq.nhdsNE_deriv, hnear, self_mem_nhdsWithin] with z hz hgz hzx
    rw [hz]
    exact (hfirst hgz (sub_ne_zero.mpr hzx)).deriv
  have hsecond {z : ℂ} (hgz : AnalyticAt ℂ g z) (hz : z - x₀ ≠ 0) :
      HasDerivAt v (((z - x₀) ^ 2 * deriv (deriv g) z -
        2 * (z - x₀) * deriv g z + 2 * g z) / (z - x₀) ^ 3) z := by
    have hd := (((hgz.deriv.differentiableAt.hasDerivAt.mul
      ((hasDerivAt_id z).sub_const x₀)).sub hgz.differentiableAt.hasDerivAt).div
      (((hasDerivAt_id z).sub_const x₀).pow 2) (pow_ne_zero _ hz))
    refine hd.congr_deriv ?_
    simp only [id_eq, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply]
    field_simp
    ring
  let H (z : ℂ) := (z - x₀) ^ 2 * deriv (deriv g) z -
    2 * (z - x₀) * deriv g z + 2 * g z - 2 * g z ^ 3 -
      z * g z * (z - x₀) ^ 2 + c * (z - x₀) ^ 3
  have hH : H =ᶠ[𝓝[≠] x₀] fun _ => 0 := by
    filter_upwards [hode, heq, hdu.nhdsNE_deriv, hnear, self_mem_nhdsWithin] with
      z hodez heqz hduz hgz hzx
    have hz : z - x₀ ≠ 0 := sub_ne_zero.mpr hzx
    rw [heqz, hduz, (hsecond hgz hz).deriv] at hodez
    dsimp only [H]
    linear_combination (norm := (field_simp [hz]; ring)) (z - x₀) ^ 3 * hodez
  have hcont : ContinuousAt H x₀ := by
    dsimp only [H]
    fun_prop (disch := first | exact hg.continuousAt | exact hg.deriv.continuousAt |
      exact hg.deriv.deriv.continuousAt)
  have hzero : H x₀ = 0 := tendsto_nhds_unique
    (hcont.tendsto.mono_left nhdsWithin_le_nhds) (tendsto_const_nhds.congr' hH.symm)
  have hpoly : g x₀ * (g x₀ - 1) * (g x₀ + 1) = 0 := by
    dsimp only [H] at hzero
    linear_combination -(1 / 2 : ℂ) * hzero
  have hsign : g x₀ = 1 ∨ g x₀ = -1 := by
    rcases mul_eq_zero.mp hpoly with hleft | hright
    · exact Or.inl (sub_eq_zero.mp ((mul_eq_zero.mp hleft).resolve_left hg0))
    · exact Or.inr (eq_neg_iff_add_eq_zero.mpr hright)
  exact ⟨g, hg, hsign, heq⟩

/-- The residue limit at any meromorphic PII pole is one of the two values `±1`. -/
theorem pole_residue_limit {u : ℂ → ℂ} {c x₀ : ℂ}
    (hu : MeromorphicAt u x₀) (hp : meromorphicOrderAt u x₀ < 0)
    (hode : ∀ᶠ x in 𝓝[≠] x₀, deriv (deriv u) x = 2 * u x ^ 3 + x * u x - c) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
      Tendsto (fun x => (x - x₀) * u x) (𝓝[≠] x₀) (𝓝 ε) := by
  obtain ⟨g, hg, hsign, heq⟩ := pole_analytic_factor hu hp hode
  refine ⟨g x₀, hsign, ?_⟩
  apply (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [heq, self_mem_nhdsWithin] with z hz hzx
  rw [hz]
  exact (mul_div_cancel₀ _ (sub_ne_zero.mpr hzx)).symm

end DLMF.Painleve
