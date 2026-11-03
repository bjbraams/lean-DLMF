/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Hurwitz.SeriesAndContinuation
public import DLMFMathlib.Analysis.Complex.NonInteger
public import DLMF.Gamma.PolygammaHurwitz

/-!
# Hurwitz zeta values and derivatives

Special values of the Hurwitz zeta function, the multiplication formula and rational
parameters, and derivatives with respect to `a` and `s` (DLMF 25.11.11–25.11.24).

## Main results

* `hurwitzZeta_one_half`: DLMF 25.11.11, `ζ(s, 1/2) = (2^s - 1) ζ(s)`.
* `hurwitzZetaComplex_nat_eq_polygamma`: polygamma values, DLMF 25.11.12.
* `hurwitzZetaComplex_zero`, `hurwitzZetaComplex_zero'`, `hurwitzZeta_zero_eq_one_half_sub`: DLMF
  25.11.13.
* `hurwitzZetaComplex_neg_nat`, `hurwitzZetaComplex_neg_nat'`: values at negative integers, DLMF
  25.11.14.
* `hurwitzZetaComplex_mul`: the multiplication formula DLMF 25.11.15.
* `hurwitzZeta_one_sub_rat`: rational parameters, DLMF 25.11.16.
* `hasDerivAt_hurwitzZetaComplex_param`: the `a`-derivative, DLMF 25.11.17.
* `deriv_hurwitzZetaComplex_zero`: Lerch's formula, DLMF 25.11.18.
* `deriv_hurwitzZetaComplex_eulerMaclaurin`, `iteratedDeriv_hurwitzZetaComplex`:
  `s`-derivatives, DLMF 25.11.19–25.11.20.
* `deriv_hurwitzZeta_one_sub_two_mul_rat`, `deriv_hurwitzZeta_one_sub_two_mul_half`,
  `deriv_hurwitzZeta_one_sub_two_mul_third`: DLMF 25.11.21–25.11.23, the last corrected.
* `sum_deriv_hurwitzZeta_rat`: DLMF 25.11.24.
* `not_hasSum_hurwitzZetaComplex_taylor_zero`: the Taylor series 25.11.10 fails at `s = 0`.

## Implementation notes

The conventions for the two Hurwitz zeta functions are described in `DLMF.Zeta.Hurwitz`.
-/

@[expose] public section

open Complex Filter Set MeasureTheory HurwitzZeta

open scoped Nat Real Topology

noncomputable section

namespace DLMF.Zeta


open DLMF.Hypergeometric (poch)

/-! ### Sums of Hurwitz zeta functions over rational parameters -/

/-- Reindexing a sum over `ZMod k` as a sum over `0 ≤ r < k`. -/
private lemma sum_zmod_eq_sum_range_natCast {k : ℕ} [NeZero k] {M : Type*} [AddCommMonoid M]
    (f : ZMod k → M) : ∑ j : ZMod k, f j = ∑ r ∈ Finset.range k, f (r : ZMod k) := by
  refine Finset.sum_bij' (fun j _ => j.val) (fun r _ => (r : ZMod k)) ?_ ?_ ?_ ?_ ?_
  · intro j _; simpa using ZMod.val_lt j
  · intro r _; simp
  · intro j _; simp
  · intro r hr; simpa using ZMod.val_cast_of_lt (Finset.mem_range.mp hr)
  · intro j _; simp

/-- The `L`-function of the constant function `1` on `ZMod k` is Riemann's zeta function, for
`s ≠ 1` (analytic continuation from `Re s > 1`). -/
private lemma LFunction_const_one_eq_riemannZeta {k : ℕ} [NeZero k] {s : ℂ} (hs : s ≠ 1) :
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
private lemma sum_hurwitzZeta_div_eq {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : s ≠ 1) :
    ∑ r ∈ Finset.Ico 1 k, hurwitzZeta ((r / k : ℝ) : UnitAddCircle) s =
      ((k : ℂ) ^ s - 1) * riemannZeta s := by
  have : NeZero k := ⟨by omega⟩
  have h := LFunction_const_one_eq_riemannZeta (k := k) hs
  simp only [ZMod.LFunction, one_mul] at h
  rw [sum_zmod_eq_sum_range_natCast (fun j => hurwitzZeta (ZMod.toAddCircle j) s),
    Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)] at h
  simp only [Nat.cast_zero, map_zero, hurwitzZeta_zero, ZMod.toAddCircle_natCast] at h
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hks : (k : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hk0)
  rw [cpow_neg] at h
  field_simp at h
  linear_combination h

/-- The `s`-derivative of the distribution relation (DLMF 25.11.24). -/
private lemma sum_deriv_hurwitzZeta_div_eq {s : ℂ} (hs : s ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    ∑ r ∈ Finset.Ico 1 k, deriv (hurwitzZeta ((r / k : ℝ) : UnitAddCircle)) s =
      ((k : ℂ) ^ s - 1) * deriv riemannZeta s + (k : ℂ) ^ s * riemannZeta s * Real.log k := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hev : (fun t => ∑ r ∈ Finset.Ico 1 k, hurwitzZeta ((r / k : ℝ) : UnitAddCircle) t) =ᶠ[𝓝 s]
      fun t => ((k : ℂ) ^ t - 1) * riemannZeta t := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with t ht
    exact sum_hurwitzZeta_div_eq hk ht
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
  have h := sum_hurwitzZeta_div_eq (k := 2) (by norm_num) hs
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

/-- Identity under the stated parameter and domain assumptions: `((Polynomial.bernoulli n).map
(algebraMap ℚ ℂ)).eval (x + 1) = ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval x + n *
x ^ (n - 1)`. -/
private lemma eval_add_one_map_bernoulli (n : ℕ) (x : ℂ) :
    ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval (x + 1) =
      ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval x + n * x ^ (n - 1) := by
  have h := congrArg (Polynomial.aeval x) (Polynomial.bernoulli_comp_one_add_X n)
  simp only [Polynomial.aeval_comp, map_add, map_one, Polynomial.aeval_X, nsmul_eq_mul] at h
  simp only [Polynomial.eval_map_algebraMap]
  rw [add_comm x 1, h]
  simp

/-- Identity under the stated parameter and domain assumptions: `poch (-(n : ℂ)) j = (-1) ^ j *
(n.descFactorial j : ℂ)`. -/
private lemma poch_neg_natCast (n j : ℕ) : poch (-(n : ℂ)) j = (-1) ^ j * (n.descFactorial j : ℂ) :=
    by
  rw [poch, ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]

/-- Sum over `range (2 (M+1))` as a sum over pairs. -/
private lemma sum_range_two_mul_eq_sum_pairs {M : Type*} [AddCommMonoid M] (T : ℕ → M) (K : ℕ) :
    ∑ i ∈ Finset.range (2 * K), T i = ∑ k ∈ Finset.range K, (T (2 * k) + T (2 * k + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, add_assoc]

/-- Formula under the stated hypotheses: `((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval w =
∑ i ∈ Finset.range (n + 1), (bernoulli i : ℂ) * (n.choose i : ℂ) * w ^ (n - i)`. -/
private lemma eval_map_bernoulli_eq_sum (n : ℕ) (w : ℂ) :
    ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval w =
      ∑ i ∈ Finset.range (n + 1), (bernoulli i : ℂ) * (n.choose i : ℂ) * w ^ (n - i) := by
  rw [Polynomial.bernoulli, Polynomial.map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Polynomial.eval_monomial]

/-- The Euler–Maclaurin correction terms at `s = -n` sum to `-B_{n+1}(w)/(n+1)`. -/
private lemma eulerMaclaurinCorrection_neg_natCast (n : ℕ) (w : ℂ) {M : ℕ} (hM : n ≤ 2 * M) :
    w ^ (1 - -(n : ℂ)) / (-(n : ℂ) - 1) + w ^ (-(-(n : ℂ))) / 2 +
      ∑ k ∈ Finset.range M, (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2).factorial : ℂ) *
        poch (-(n : ℂ)) (2 * k + 1) * w ^ (-(-(n : ℂ)) - (2 * k + 1)) =
      -((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)).eval w / (n + 1) := by
  set T : ℕ → ℂ := fun i => (bernoulli i : ℂ) * ((n + 1).choose i : ℂ) * w ^ (n + 1 - i) with hT
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hsum : ((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)).eval w =
      T 0 + T 1 + ∑ k ∈ Finset.range M, T (2 * k + 2) := by
    rw [eval_map_bernoulli_eq_sum]
    have h1 : ∑ i ∈ Finset.range (n + 1 + 1), T i = ∑ i ∈ Finset.range (2 * (M + 1)), T i := by
      refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun i _ hi => ?_
      simp only [Finset.mem_range, not_lt] at hi
      simp [T, Nat.choose_eq_zero_of_lt (by omega : n + 1 < i)]
    rw [h1, sum_range_two_mul_eq_sum_pairs, Finset.sum_range_succ']
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
    rw [poch_neg_natCast]
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
private lemma hurwitzEMSeq_neg_natCast (n : ℕ) (a : ℂ) (N : ℕ) :
    hurwitzEMSeq (-(n : ℂ)) a N = -((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)).eval a /
      (n + 1) := by
  have hM : n ≤ 2 * (⌈(1 - (-(n : ℂ)).re) / 2⌉₊ + 1) := by
    have := Nat.le_ceil ((1 - (-(n : ℂ)).re) / 2)
    simp only [neg_re, natCast_re, sub_neg_eq_add] at this ⊢
    have h2 : ((n : ℝ) + 1) / 2 ≤ ⌈(1 + (n : ℝ)) / 2⌉₊ := by rw [add_comm]; exact this
    have : (n : ℝ) ≤ 2 * ((⌈(1 + (n : ℝ)) / 2⌉₊ : ℕ) + 1 : ℝ) := by linarith
    exact_mod_cast this
  unfold hurwitzEMSeq
  rw [add_assoc, add_assoc, ← add_assoc ((a + N) ^ (1 - -(n : ℂ)) / (-(n : ℂ) - 1)),
    eulerMaclaurinCorrection_neg_natCast n (a + N) hM]
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [neg_neg, cpow_natCast]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ, ← add_assoc,
      eval_add_one_map_bernoulli (n + 1) (a + N)]
    field_simp at ih ⊢
    simp only [Nat.add_sub_cancel] at ih ⊢
    push_cast at ih ⊢
    linear_combination ih

/-- **`ζ(0, a) = 1/2 - a`** (DLMF 25.11.13), `Re a > 0`. This is stronger than DLMF, which assumes
`ℜ a > 0`. -/
@[dlmf 25.11.E13]
theorem hurwitzZetaComplex_zero' {a : ℂ} :
    hurwitzZetaComplex 0 a = 1 / 2 - a := by
  have h : hurwitzZetaComplex 0 a =
      -((Polynomial.bernoulli (0 + 1)).map (algebraMap ℚ ℂ)).eval a / ((0 : ℕ) + 1) := by
    rw [hurwitzZetaComplex_eq_limUnder_hurwitzEMSeq]
    have : hurwitzEMSeq 0 a = fun _ =>
        -((Polynomial.bernoulli (0 + 1)).map (algebraMap ℚ ℂ)).eval a / ((0 : ℕ) + 1) := by
      funext N; have := hurwitzEMSeq_neg_natCast 0 a N; simpa using this
    rw [this]
    exact tendsto_const_nhds.limUnder_eq
  rw [h, eval_map_bernoulli_eq_sum]
  simp [Finset.sum_range_succ, bernoulli_one]
  ring

/-- **`ζ(0, a) = 1/2 - a`** (DLMF 25.11.13), `Re a > 0`. -/
@[dlmf 25.11.E13]
theorem hurwitzZetaComplex_zero {a : ℂ} (_ha : 0 < a.re) :
    hurwitzZetaComplex 0 a = 1 / 2 - a :=
  hurwitzZetaComplex_zero'

/-- `ζ(0, x) = 1/2 - x` for Mathlib's Hurwitz zeta function, `0 < x ≤ 1` (DLMF 25.11.13). -/
@[dlmf 25.11.E13]
theorem hurwitzZeta_zero_eq_one_half_sub {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    hurwitzZeta (x : UnitAddCircle) 0 = 1 / 2 - x := by
  rw [← hurwitzZetaComplex_eq_hurwitzZeta hx hx1 zero_ne_one, hurwitzZetaComplex_zero (by simpa)]

/-- **`hasSum_hurwitzZetaComplex_taylor` is false at `s = 0`** (and, similarly, at every
`s = 0, -1, -2, …`): the terms with `n + s = 1` involve the pole of `ζ`, where DLMF's product
`(s)_n ζ(n+s)` is a limit but Lean's `poch 0 n · ζ(1)` is `0`. At `s = 0`, `a = 1/2` the series
sums to `ζ(0) = -1/2`, while `ζ(0, 1/2) = 0`. -/
lemma not_hasSum_hurwitzZetaComplex_taylor_zero :
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
real `0 ≤ a ≤ 1`.) This is stronger than DLMF, which assumes `ℜ a > 0`. -/
@[dlmf 25.11.E14]
theorem hurwitzZetaComplex_neg_nat' (n : ℕ) {a : ℂ} :
    hurwitzZetaComplex (-n) a =
      -((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)).eval a / (n + 1) := by
  rw [hurwitzZetaComplex_eq_limUnder_hurwitzEMSeq]
  have : hurwitzEMSeq (-(n : ℂ)) a = fun _ =>
      -((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)).eval a / (n + 1) :=
    funext (hurwitzEMSeq_neg_natCast n a)
  rw [this]
  exact tendsto_const_nhds.limUnder_eq

/-- **Values at negative integers** (DLMF 25.11.14): `ζ(-n, a) = -B_{n+1}(a)/(n+1)`,
`n = 0, 1, 2, …`, `Re a > 0`. (Mathlib's `HurwitzZeta.hurwitzZeta_neg_nat` is the case `n ≥ 1`,
real `0 ≤ a ≤ 1`.) -/
@[dlmf 25.11.E14]
theorem hurwitzZetaComplex_neg_nat (n : ℕ) {a : ℂ} (_ha : 0 < a.re) :
    hurwitzZetaComplex (-n) a =
      -((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)).eval a / (n + 1) :=
  hurwitzZetaComplex_neg_nat' n

/-- `(r w)^t = r^t w^t` for real `r > 0` and `w ≠ 0`. -/
theorem ofReal_mul_cpow_of_pos {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ≠ 0) (t : ℂ) :
    ((r : ℂ) * w) ^ t = (r : ℂ) ^ t * w ^ t := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hr' hw), cpow_def_of_ne_zero hr', cpow_def_of_ne_zero hw,
    log_ofReal_mul hr hw, ← Complex.exp_add, Complex.ofReal_log hr.le]
  ring_nf

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
    fun t ht => (differentiableAt_hurwitzZetaComplex_of_add_natCast_ne_zero' ht
      (Complex.add_natCast_ne_zero_of_re_pos hka)).differentiableWithinAt
  have hg' : DifferentiableOn ℂ (fun t => (k : ℂ) ^ (-t) *
      ∑ n ∈ Finset.range k, hurwitzZetaComplex t (a + n / k)) {1}ᶜ := by
    intro t ht
    refine (DifferentiableAt.mul ((differentiableAt_id.neg).const_cpow (Or.inl hkC))
      (DifferentiableAt.fun_sum fun n _ =>
          differentiableAt_hurwitzZetaComplex_of_add_natCast_ne_zero' ht
        (Complex.add_natCast_ne_zero_of_re_pos (han n)))).differentiableWithinAt
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
  rw [← hL.tsum_eq, Nat.sumByResidueClasses hL.summable k, sum_zmod_eq_sum_range_natCast,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_range] at hn
  rw [← (hR n).tsum_eq, ← tsum_mul_left]
  congr 1; funext j
  have hw : ((j : ℂ) + (a + n / k)) ≠ 0 := by
    have := (Complex.add_natCast_ne_zero_of_re_pos (han n)) j; rwa [add_comm] at this
  have heq : (((((n : ZMod k).val + k * j : ℕ)) : ℂ) + k * a) =
      ((k : ℝ) : ℂ) * ((j : ℂ) + (a + n / k)) := by
    rw [ZMod.val_natCast_of_lt hn]
    push_cast
    field_simp
    ring
  rw [heq, ofReal_mul_cpow_of_pos hk0 hw, cpow_neg]
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
      sum_zmod_eq_sum_range_natCast]
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
  hasDerivAt_hurwitzZetaComplex_param' hs0 hs1 ha

/-- `(x + a)^r` is integrable on `(0, ∞)` for `a > 0`, `r < -1`. -/
private lemma integrableOn_add_rpow_Ioi {a r : ℝ} (ha : 0 < a) (hr : r < -1) :
    IntegrableOn (fun x : ℝ => (x + a) ^ r) (Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ => ‖((1 : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ ((-r : ℝ) : ℂ)‖)
      (Ioi 0) := (integrableOn_bdd_div_add_cpow (f := fun _ => (1 : ℝ)) measurable_const
    (B := 1) (fun _ => by simp) (w := ((-r : ℝ) : ℂ)) (by simp; linarith) ha le_rfl).norm
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hxa : 0 < x + a := by linarith [mem_Ioi.mp hx]
  simp only [ofReal_one, norm_div, norm_one]
  rw [norm_cpow_eq_rpow_re_of_pos hxa, ofReal_re, Real.rpow_neg hxa.le, one_div, inv_inv]

/-- `|log y| ≤ (y^δ + y^{-δ})/δ` for `y > 0`, `δ > 0`. -/
private lemma abs_log_le_rpow_add_rpow_neg_div {y δ : ℝ} (hy : 0 < y) (hδ : 0 < δ) :
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
private lemma hasDerivAt_integral_bdd_div_add_cpow {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
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
      exact integrableOn_add_rpow_Ioi ha (by simp only [δ, hi, lo, ε] at *; linarith)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := F) (F' := F') (x₀ := s) (bound := bound) (Metric.ball_mem_nhds s hε)
    (Eventually.of_forall fun t => (hmeasF t).aestronglyMeasurable)
    (integrableOn_bdd_div_add_cpow hf hB (w := s + 2) (by simp; linarith) ha le_rfl)
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
    have hlog := abs_log_le_rpow_add_rpow_neg_div hxa hδ
    have hp : (x + a) ^ (-(t.re + 2)) ≤ (x + a) ^ (-lo) + (x + a) ^ (-hi) := by
      have := rpow_neg_sub_one_le_add (x := x + a) (σ := t.re + 1) (σ₀ := lo - 1) (R := hi - 1) hxa
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
private lemma exists_abs_periodicBernoulli_two_sub_le :
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
  obtain ⟨B, hB⟩ := exists_abs_periodicBernoulli_two_sub_le
  set J : ℂ → ℂ := fun t => ∫ x in Ioi (0 : ℝ),
    ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (t + 2)
  have hJ := hasDerivAt_integral_bdd_div_add_cpow ((measurable_periodicBernoulli 2).sub_const _)
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
private lemma deriv_hurwitzZetaComplex_zero_eq {b : ℝ} (hb : 0 < b) :
    deriv (fun s => hurwitzZetaComplex s b) 0 =
      ((b : ℂ) - 1 / 2) * (Real.log b : ℂ) - b - 1 / 2 * ∫ x in Ioi (0 : ℝ),
        ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) / (((x + b : ℝ)) : ℂ) ^ (2 : ℂ) := by
  rw [deriv_hurwitzZetaComplex_eulerMaclaurin (by norm_num) (by norm_num) hb, zero_add,
    cpow_zero, sub_zero, cpow_one]
  rw [show (0 : ℂ) + 2 = 2 by norm_num]
  norm_num
  ring

/-- The integral `∫_0^∞ (B̃₂(x) - B₂)/(x+a+n)² dx` tends to `0` as `n → ∞`. -/
private lemma tendsto_integral_periodicBernoulli_two_div {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) /
      (((x + (a + n) : ℝ)) : ℂ) ^ (2 : ℂ)) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := exists_abs_periodicBernoulli_two_sub_le
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hint := integrableOn_add_rpow_Ioi ha (r := -2) (by norm_num)
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
    have hd1 := (differentiableAt_hurwitzZetaComplex_of_add_natCast_ne_zero' (s₀ := 0)
        (z := (b : ℂ) + 1)
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
  have hlimA := (tendsto_integral_periodicBernoulli_two_div ha).const_mul (-(1 / 2 : ℂ))
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
    rw [deriv_hurwitzZetaComplex_zero_eq (by positivity)]
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
  have h := sum_deriv_hurwitzZeta_div_eq hs1 (k := 2) (by norm_num)
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

/-- `sinZeta (1/3) s = 3^{-s} (√3/2) (ζ(s, 1/3) - ζ(s, 2/3))` for `Re s > 1`. -/
private lemma sinZeta_third {s : ℂ} (hs : 1 < s.re) :
    sinZeta ((1 / 3 : ℝ) : UnitAddCircle) s = (3 : ℂ) ^ (-s) * (Real.sqrt 3 / 2) *
      (hurwitzZeta ((1 / 3 : ℝ) : UnitAddCircle) s -
        hurwitzZeta ((2 / 3 : ℝ) : UnitAddCircle) s) := by
  set Φ : ZMod 3 → ℂ := fun j => (Real.sin (2 * π * (1 / 3) * j.val) : ℂ)
  have hL := ZMod.LFunction_eq_LSeries Φ hs
  have hS := (LSeriesHasSum_sin (1 / 3) hs).LSeries_eq
  have hΦ : ∀ k : ℕ, Φ k = (Real.sin (2 * π * (1 / 3) * k) : ℂ) := by
    intro k
    simp only [Φ, ZMod.val_natCast]
    congr 1
    conv_rhs => rw [← Nat.mod_add_div k 3]
    push_cast
    rw [show 2 * π * (1 / 3) * ((k % 3 : ℕ) + 3 * (k / 3 : ℕ) : ℝ) =
      2 * π * (1 / 3) * (k % 3 : ℕ) + (k / 3 : ℕ) * (2 * π) by ring, Real.sin_add_nat_mul_two_pi]
  rw [← hS, ← LSeries_congr (fun {k} _ => hΦ k) s, ← hL, ZMod.LFunction]
  have h3 : ∀ f : ZMod 3 → ℂ, ∑ j, f j = f 0 + f 1 + f 2 := fun f => Fin.sum_univ_three f
  rw [h3]
  simp only [Φ, ZMod.toAddCircle_apply]
  have v1 : (1 : ZMod 3).val = 1 := rfl
  have v2 : (2 : ZMod 3).val = 2 := rfl
  have v0 : (0 : ZMod 3).val = 0 := rfl
  rw [v0, v1, v2]
  have e1 : Real.sin (2 * π * (1 / 3) * ((1 : ℕ) : ℝ)) = Real.sqrt 3 / 2 := by
    rw [show 2 * π * (1 / 3) * ((1 : ℕ) : ℝ) = π - π / 3 by push_cast; ring, Real.sin_pi_sub,
      Real.sin_pi_div_three]
  have e2 : Real.sin (2 * π * (1 / 3) * ((2 : ℕ) : ℝ)) = -(Real.sqrt 3 / 2) := by
    rw [show 2 * π * (1 / 3) * ((2 : ℕ) : ℝ) = π / 3 + π by push_cast; ring, Real.sin_add_pi,
      Real.sin_pi_div_three]
  rw [e1, e2]
  push_cast
  norm_num
  ring


/-- The derivative of the odd Hurwitz zeta function at a negative odd integer, from its
functional equation (the trivial zero of  at ). -/
private lemma deriv_hurwitzZetaOdd_one_sub_two_mul (a : UnitAddCircle) {n : ℕ} (hn : 1 ≤ n) :
    deriv (hurwitzZetaOdd a) (1 - 2 * n) =
      -(2 * (2 * π) ^ (-(2 * n : ℂ)) * Gamma (2 * n) * sinZeta a (2 * n) * (π / 2) * (-1) ^ n) := by
  set s₀ : ℂ := 2 * n
  have hs₀ : ∀ m : ℕ, s₀ ≠ -m := by
    intro m h
    have := congrArg Complex.re h
    simp [s₀] at this
    have : (0 : ℝ) < n := by exact_mod_cast hn
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  set F : ℂ → ℂ := fun s => 2 * (2 * π) ^ (-s) * Gamma s * sinZeta a s
  set Sn : ℂ → ℂ := fun s => Complex.sin (π * s / 2)
  have hev : (fun s => hurwitzZetaOdd a (1 - s)) =ᶠ[𝓝 s₀] fun s => F s * Sn s := by
    have hU : {s : ℂ | 0 < s.re} ∈ 𝓝 s₀ :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by
        simp only [mem_ofPred_eq, s₀]; simp; positivity)
    filter_upwards [hU] with s hs
    have hs' : ∀ m : ℕ, s ≠ -m := by
      intro m h; rw [h] at hs; simp at hs; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    rw [hurwitzZetaOdd_one_sub a hs']
    simp only [F, Sn]; ring
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hF : DifferentiableAt ℂ F s₀ := by
    refine ((DifferentiableAt.mul ?_ (Complex.differentiableAt_Gamma _ hs₀)).mul
      ((differentiableAt_sinZeta a) s₀))
    exact (differentiableAt_const _).mul
      ((differentiableAt_id.neg).const_cpow (Or.inl h2π))
  have hS : HasDerivAt Sn (Complex.cos (π * s₀ / 2) * (π / 2)) s₀ := by
    have := ((hasDerivAt_id s₀).const_mul (π : ℂ)).div_const 2
    simpa [Sn, mul_comm] using this.csin
  have hS0 : Sn s₀ = 0 := by
    simp only [Sn, s₀]
    rw [show (π : ℂ) * (2 * n) / 2 = n * π by ring, Complex.sin_nat_mul_pi]
  have hC : Complex.cos (π * s₀ / 2) = (-1) ^ n := by
    simp only [s₀]
    rw [show (π : ℂ) * (2 * n) / 2 = ((n * π : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
      Real.cos_nat_mul_pi]
    push_cast; ring
  have hD : HasDerivAt (fun s => F s * Sn s) _ s₀ := hF.hasDerivAt.mul hS
  have hd := hD.deriv
  rw [hS0, hC, mul_zero, zero_add] at hd
  have hcomp : deriv (fun s => hurwitzZetaOdd a (1 - s)) s₀ = -deriv (hurwitzZetaOdd a) (1 - s₀) :=
    deriv_comp_const_sub _ _ _
  rw [hev.deriv_eq, hd] at hcomp
  rw [show (1 : ℂ) - 2 * n = 1 - s₀ from rfl]
  rw [← neg_neg (deriv (hurwitzZetaOdd a) (1 - s₀)), ← hcomp]
  simp only [F, s₀]
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
  have hb : ((2 / 3 : ℝ) : UnitAddCircle) = -((1 / 3 : ℝ) : UnitAddCircle) := by
    rw [show (2 / 3 : ℝ) = -(1 / 3) + 1 by norm_num, AddCircle.coe_add_period, AddCircle.coe_neg]
  have hs₀ : (1 - 2 * n : ℂ) ≠ 1 := by
    intro h
    have : (2 : ℂ) * n = 0 := by linear_combination -h
    have : (n : ℂ) = 0 := by simpa using this
    have : n = 0 := by exact_mod_cast this
    omega
  have hEa := differentiableAt_hurwitzZetaEven ((1 / 3 : ℝ) : UnitAddCircle) hs₀
  have hOa := differentiable_hurwitzZetaOdd ((1 / 3 : ℝ) : UnitAddCircle) (1 - 2 * n)
  have hDa : deriv (hurwitzZeta ((1 / 3 : ℝ) : UnitAddCircle)) (1 - 2 * n) =
      deriv (hurwitzZetaEven ((1 / 3 : ℝ) : UnitAddCircle)) (1 - 2 * n) +
      deriv (hurwitzZetaOdd ((1 / 3 : ℝ) : UnitAddCircle)) (1 - 2 * n) := by
    rw [show hurwitzZeta ((1 / 3 : ℝ) : UnitAddCircle) = fun s =>
      hurwitzZetaEven ((1 / 3 : ℝ) : UnitAddCircle) s +
        hurwitzZetaOdd ((1 / 3 : ℝ) : UnitAddCircle) s from rfl]
    exact deriv_add hEa hOa
  have hDb : deriv (hurwitzZeta ((2 / 3 : ℝ) : UnitAddCircle)) (1 - 2 * n) =
      deriv (hurwitzZetaEven ((1 / 3 : ℝ) : UnitAddCircle)) (1 - 2 * n) -
      deriv (hurwitzZetaOdd ((1 / 3 : ℝ) : UnitAddCircle)) (1 - 2 * n) := by
    rw [hb, show hurwitzZeta (-((1 / 3 : ℝ) : UnitAddCircle)) = fun s =>
      hurwitzZetaEven ((1 / 3 : ℝ) : UnitAddCircle) s -
        hurwitzZetaOdd ((1 / 3 : ℝ) : UnitAddCircle) s by
      funext s; rw [hurwitzZeta, hurwitzZetaEven_neg, hurwitzZetaOdd_neg]; ring]
    exact deriv_sub hEa hOa
  have hsum := sum_deriv_hurwitzZeta_div_eq hs₀ (k := 3) (by norm_num)
  simp only [show Finset.Ico 1 3 = {1, 2} by rfl,
    Finset.sum_insert (by decide : 1 ∉ ({2} : Finset ℕ)), Finset.sum_singleton, Nat.cast_one,
    Nat.cast_ofNat] at hsum
  have hodd := deriv_hurwitzZetaOdd_one_sub_two_mul ((1 / 3 : ℝ) : UnitAddCircle) hn
  have hre : 1 < ((2 * n : ℂ)).re := by
    simp; have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hsin := sinZeta_third hre
  have h2n : (2 * n : ℂ) ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; have : (1:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h2 := sum_hurwitzZeta_div_eq (k := 3) (by norm_num) h2n
  simp only [show Finset.Ico 1 3 = {1, 2} by rfl,
    Finset.sum_insert (by decide : 1 ∉ ({2} : Finset ℕ)), Finset.sum_singleton, Nat.cast_one,
    Nat.cast_ofNat] at h2
  rw [hDa, hodd, hsin]
  have hE : deriv (hurwitzZetaEven ((1 / 3 : ℝ) : UnitAddCircle)) (1 - 2 * n) =
      ((3 ^ (1 - 2 * (n : ℂ)) - 1) * deriv riemannZeta (1 - 2 * n) +
        3 ^ (1 - 2 * (n : ℂ)) * riemannZeta (1 - 2 * n) * Real.log 3) / 2 := by
    rw [← hsum, hDa, hDb]; ring
  rw [hE, show hurwitzZeta ((2 / 3 : ℝ) : UnitAddCircle) (2 * n) =
    (3 ^ (2 * (n : ℂ)) - 1) * riemannZeta (2 * n) -
      hurwitzZeta ((1 / 3 : ℝ) : UnitAddCircle) (2 * n)
    by linear_combination h2]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hpsi := DLMF.Gamma.polygamma_eq_hurwitzZeta (n := 2 * j + 1) (by omega) (a := 1 / 3)
    (by norm_num) (by norm_num)
  have hz := riemannZeta_two_mul_nat (k := j + 1) (by omega)
  have hzn := riemannZeta_neg_nat_eq_bernoulli (2 * j + 1)
  have hΓ := Complex.Gamma_nat_eq_factorial (2 * j + 1)
  have c1 : (2 * ((j + 1 : ℕ) : ℂ)) = ((2 * j + 2 : ℕ) : ℂ) := by push_cast; ring
  have c2 : (1 - ((2 * j + 2 : ℕ) : ℂ)) = -((2 * j + 1 : ℕ) : ℂ) := by push_cast; ring
  have c3 : ((2 * j + 1 : ℕ) : ℂ) + 1 = ((2 * j + 2 : ℕ) : ℂ) := by push_cast; ring
  rw [c3] at hpsi hΓ
  rw [c1] at hz ⊢
  rw [c2]
  simp only [cpow_neg, cpow_natCast]
  rw [hzn, hΓ, hz]
  rw [show ((1 / 3 : ℝ) : ℂ) = 1 / 3 by push_cast; ring] at hpsi
  rw [show hurwitzZeta ((1 / 3 : ℝ) : UnitAddCircle) ((2 * j + 2 : ℕ) : ℂ) =
    DLMF.Gamma.polygamma (2 * j + 1) (1 / 3) / (2 * j + 1)! by
      have hF : ((2 * j + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      rw [hpsi, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, pow_mul]; field_simp; simp]
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, show 2 * (j + 1) = 2 * j + 2 by ring]
  have hr : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [show (3 : ℂ) ^ (2 * j + 2) = ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * 3 ^ (2 * j + 1) by rw [hr]; ring,
    show (9 : ℂ) ^ (j + 1) = ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * 3 ^ (2 * j + 1) by
      rw [hr, show (9 : ℂ) = 3 ^ 2 by norm_num, ← pow_mul]; ring,
    show (6 * (π : ℂ)) ^ (2 * j + 1) = 2 ^ (2 * j + 1) * 3 ^ (2 * j + 1) * π ^ (2 * j + 1) by
      rw [show (6 : ℂ) = 2 * 3 by norm_num, mul_pow, mul_pow],
    show (2 * (π : ℂ)) ^ (2 * j + 2) = 2 * 2 ^ (2 * j + 1) * π * π ^ (2 * j + 1) by ring,
    show (π : ℂ) ^ (2 * j + 2) = π * π ^ (2 * j + 1) by ring,
    show (2 * j + 2)! = (2 * j + 2) * (2 * j + 1)! from Nat.factorial_succ _,
    show 2 * j + 1 + 1 = 2 * j + 2 by ring, pow_succ (-1 : ℂ) (j + 1),
    show (-1 : ℂ) ^ (2 * j + 1) = -1 by rw [pow_succ, pow_mul]; simp]
  have hF : ((2 * j + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hr0 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hr; norm_num at hr
  push_cast
  generalize ((Real.sqrt 3 : ℝ) : ℂ) = r at *
  generalize ((2 * j + 1)! : ℂ) = F at *
  generalize DLMF.Gamma.polygamma (2 * j + 1) (1 / 3) = P
  generalize deriv riemannZeta (-(2 * (j : ℂ) + 1)) = Z
  have hT : (3 : ℂ) ^ (2 * j + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hW : (2 : ℂ) ^ (2 * j + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hQ : (π : ℂ) ^ (2 * j + 1) ≠ 0 := pow_ne_zero _ hπ
  generalize (3 : ℂ) ^ (2 * j + 1) = T at *
  generalize (2 : ℂ) ^ (2 * j + 1) = W at *
  generalize (π : ℂ) ^ (2 * j + 1) = Q at *
  have hj : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have hj2 : 2 * (j : ℂ) + 2 ≠ 0 := by
    rw [show 2 * (j : ℂ) + 2 = 2 * (j + 1) by ring]; exact mul_ne_zero two_ne_zero hj
  have hj3 : 2 * (j : ℂ) + 1 + 1 ≠ 0 := by rw [add_assoc]; norm_num; exact hj2
  have hj4 : 2 + (j : ℂ) * 2 ≠ 0 := by rw [show 2 + (j : ℂ) * 2 = 2 * j + 2 by ring]; exact hj2
  rcases neg_one_pow_eq_or ℂ (j + 1) with h | h <;> rw [h] <;> field_simp <;> ring

/-- A `k`-periodic arithmetic function has `L`-series `k^{-s} ∑_{r<k} f(r) ζ(s, r/k)` for
`Re s > 1`. -/
private lemma LSeries_periodic_eq_sum_hurwitzZeta {k : ℕ} (hk : 1 ≤ k) {f : ℕ → ℂ}
    (hf : ∀ m, f (m + k) = f m) {s : ℂ} (hs : 1 < s.re) :
    LSeries f s = (k : ℂ) ^ (-s) * ∑ r ∈ Finset.range k,
      f r * hurwitzZeta ((r / k : ℝ) : UnitAddCircle) s := by
  have : NeZero k := ⟨by omega⟩
  set Φ : ZMod k → ℂ := fun j => f j.val
  have hΦ : ∀ m : ℕ, Φ m = f m := by
    intro m
    simp only [Φ, ZMod.val_natCast]
    conv_rhs => rw [← Nat.mod_add_div m k]
    induction m / k with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, ← add_assoc, hf, ih]
  rw [← LSeries_congr (fun {m} _ => hΦ m) s, ← ZMod.LFunction_eq_LSeries Φ hs, ZMod.LFunction,
    sum_zmod_eq_sum_range_natCast]
  simp only [ZMod.toAddCircle_natCast, hΦ]

/-- `cosZeta (h/k) s = k^{-s} ∑_{r<k} cos(2πrh/k) ζ(s, r/k)` for `Re s > 1`. -/
private lemma cosZeta_div_eq_sum {h k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    cosZeta ((h / k : ℝ) : UnitAddCircle) s = (k : ℂ) ^ (-s) * ∑ r ∈ Finset.range k,
      (Real.cos (2 * π * r * h / k) : ℂ) * hurwitzZeta ((r / k : ℝ) : UnitAddCircle) s := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [← (LSeriesHasSum_cos (h / k) hs).LSeries_eq,
    LSeries_periodic_eq_sum_hurwitzZeta hk (fun m => ?_) hs]
  · congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 3
    ring
  · congr 1
    rw [show 2 * π * (h / k) * ((m + k : ℕ) : ℝ) = 2 * π * (h / k) * m + h * (2 * π) by
      push_cast; field_simp, Real.cos_add_nat_mul_two_pi]

/-- `sinZeta (h/k) s = k^{-s} ∑_{r<k} sin(2πrh/k) ζ(s, r/k)` for `Re s > 1`. -/
private lemma sinZeta_div_eq_sum {h k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    sinZeta ((h / k : ℝ) : UnitAddCircle) s = (k : ℂ) ^ (-s) * ∑ r ∈ Finset.range k,
      (Real.sin (2 * π * r * h / k) : ℂ) * hurwitzZeta ((r / k : ℝ) : UnitAddCircle) s := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [← (LSeriesHasSum_sin (h / k) hs).LSeries_eq,
    LSeries_periodic_eq_sum_hurwitzZeta hk (fun m => ?_) hs]
  · congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 3
    ring
  · congr 1
    rw [show 2 * π * (h / k) * ((m + k : ℕ) : ℝ) = 2 * π * (h / k) * m + h * (2 * π) by
      push_cast; field_simp, Real.sin_add_nat_mul_two_pi]

/-- The derivative of the even Hurwitz zeta function at a negative odd integer, from its
functional equation. -/
private lemma deriv_hurwitzZetaEven_one_sub_two_mul (a : UnitAddCircle) {n : ℕ} (hn : 1 ≤ n) :
    deriv (hurwitzZetaEven a) (1 - 2 * n) =
      -((-1) ^ n * deriv (fun s => 2 * (2 * π) ^ (-s) * Gamma s * cosZeta a s) (2 * n)) := by
  set s₀ : ℂ := 2 * n
  have hre : 1 < s₀.re := by
    simp only [s₀]; simp; have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hs₀ : ∀ m : ℕ, s₀ ≠ -m := by
    intro m h
    have := congrArg Complex.re h
    simp [s₀] at this
    have : (0 : ℝ) < n := by exact_mod_cast hn
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  set F : ℂ → ℂ := fun s => 2 * (2 * π) ^ (-s) * Gamma s * cosZeta a s
  set Cs : ℂ → ℂ := fun s => Complex.cos (π * s / 2)
  have hev : (fun s => hurwitzZetaEven a (1 - s)) =ᶠ[𝓝 s₀] fun s => F s * Cs s := by
    have hU : {s : ℂ | 1 < s.re} ∈ 𝓝 s₀ :=
      (isOpen_lt continuous_const continuous_re).mem_nhds hre
    filter_upwards [hU] with s hs
    have hs' : ∀ m : ℕ, s ≠ -m := by
      intro m h; rw [h] at hs; simp at hs; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
    rw [hurwitzZetaEven_one_sub a hs' (Or.inr hs1)]
    simp only [F, Cs]; ring
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hs₀1 : s₀ ≠ 1 := by intro h; rw [h] at hre; simp at hre
  have hF : DifferentiableAt ℂ F s₀ := by
    refine ((DifferentiableAt.mul ?_ (Complex.differentiableAt_Gamma _ hs₀)).mul
      (differentiableAt_cosZeta a (Or.inl hs₀1)))
    exact (differentiableAt_const _).mul
      ((differentiableAt_id.neg).const_cpow (Or.inl h2π))
  have hS : HasDerivAt Cs (-Complex.sin (π * s₀ / 2) * (π / 2)) s₀ := by
    have := ((hasDerivAt_id s₀).const_mul (π : ℂ)).div_const 2
    simpa [Cs, mul_comm] using this.ccos
  have hS0 : Complex.sin (π * s₀ / 2) = 0 := by
    simp only [s₀]
    rw [show (π : ℂ) * (2 * n) / 2 = n * π by ring, Complex.sin_nat_mul_pi]
  have hC : Cs s₀ = (-1) ^ n := by
    simp only [Cs, s₀]
    rw [show (π : ℂ) * (2 * n) / 2 = ((n * π : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
      Real.cos_nat_mul_pi]
    push_cast; ring
  have hD : HasDerivAt (fun s => F s * Cs s) _ s₀ := hF.hasDerivAt.mul hS
  have hd := hD.deriv
  rw [hS0, hC] at hd
  have hcomp : deriv (fun s => hurwitzZetaEven a (1 - s)) s₀ =
      -deriv (hurwitzZetaEven a) (1 - s₀) := deriv_comp_const_sub _ _ _
  rw [hev.deriv_eq, hd] at hcomp
  rw [show (1 : ℂ) - 2 * n = 1 - s₀ from rfl]
  rw [← neg_neg (deriv (hurwitzZetaEven a) (1 - s₀)), ← hcomp]
  simp only [F, s₀]
  ring

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
  have hk : 1 ≤ k := hh.trans hhk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set a : UnitAddCircle := ((h / k : ℝ) : UnitAddCircle) with ha_def
  set s₀ : ℂ := 2 * n with hs₀_def
  have hre : 1 < s₀.re := by
    simp only [s₀]; simp; have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hs₀1 : s₀ ≠ 1 := by intro h; rw [h] at hre; simp at hre
  have hsm : ∀ m : ℕ, s₀ ≠ -m := by
    intro m h
    have := congrArg Complex.re h
    simp [s₀] at this
    have : (0 : ℝ) < n := by exact_mod_cast hn
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h1 : (1 - 2 * n : ℂ) ≠ 1 := by
    intro h
    have : (2 : ℂ) * n = 0 := by linear_combination -h
    have : (n : ℂ) = 0 := by simpa using this
    have : n = 0 := by exact_mod_cast this
    omega
  -- even and odd parts
  have hDa : deriv (hurwitzZeta a) (1 - 2 * n) =
      deriv (hurwitzZetaEven a) (1 - 2 * n) + deriv (hurwitzZetaOdd a) (1 - 2 * n) := by
    rw [show hurwitzZeta a = fun s => hurwitzZetaEven a s + hurwitzZetaOdd a s from rfl]
    exact deriv_add (differentiableAt_hurwitzZetaEven a h1) (differentiable_hurwitzZetaOdd a _)
  rw [hDa, deriv_hurwitzZetaEven_one_sub_two_mul a hn, deriv_hurwitzZetaOdd_one_sub_two_mul a hn]
  have hR := deriv_hurwitzZetaEven_one_sub_two_mul 0 hn
  rw [hurwitzZetaEven_zero, cosZeta_zero] at hR
  rw [hR]
  -- the factor `G(s) = 2 (2π)^{-s} Γ(s)`
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  set G : ℂ → ℂ := fun s => 2 * (2 * π) ^ (-s) * Gamma s with hG_def
  have hΓ0 : Gamma s₀ ≠ 0 := Complex.Gamma_ne_zero hsm
  have hG : HasDerivAt G (G s₀ * (digamma s₀ - Complex.log (2 * π))) s₀ := by
    have hΓ : HasDerivAt Gamma (Gamma s₀ * digamma s₀) s₀ := by
      have := (Complex.differentiableAt_Gamma _ hsm).hasDerivAt
      rwa [show deriv Gamma s₀ = Gamma s₀ * digamma s₀ by
        rw [digamma_def, logDeriv_apply]; field_simp] at this
    have hc := ((hasDerivAt_neg s₀).const_cpow (c := 2 * π) (Or.inl h2π))
    have := (hc.const_mul 2).fun_mul hΓ
    convert this using 1
    simp only [G]; ring
  -- the cosine part
  set c : ℕ → ℂ := fun r => (Real.cos (2 * π * r * h / k) : ℂ) with hc_def
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hCev : cosZeta a =ᶠ[𝓝 s₀] fun s => (k : ℂ) ^ (-s) * ∑ r ∈ Finset.range k,
      c r * hurwitzZeta ((r / k : ℝ) : UnitAddCircle) s := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hre] with s hs
    exact cosZeta_div_eq_sum hk hs
  have hsum : HasDerivAt (fun s => ∑ r ∈ Finset.range k,
      c r * hurwitzZeta ((r / k : ℝ) : UnitAddCircle) s)
      (∑ r ∈ Finset.range k, c r * deriv (hurwitzZeta ((r / k : ℝ) : UnitAddCircle)) s₀) s₀ :=
    HasDerivAt.fun_sum fun r _ =>
      ((differentiableAt_hurwitzZeta _ hs₀1).hasDerivAt.const_mul _)
  have hC' : HasDerivAt (cosZeta a) (-(Complex.log k * cosZeta a s₀) + (k : ℂ) ^ (-s₀) *
      ∑ r ∈ Finset.range k, c r * deriv (hurwitzZeta ((r / k : ℝ) : UnitAddCircle)) s₀) s₀ := by
    have := ((hasDerivAt_neg s₀).const_cpow (c := (k : ℂ)) (Or.inl hk0)).fun_mul hsum
    rw [cosZeta_div_eq_sum hk hre]
    refine (this.congr_of_eventuallyEq hCev).congr_deriv ?_
    ring
  have hFa := (hG.fun_mul hC').deriv
  have hF0 := (hG.fun_mul (differentiableAt_riemannZeta hs₀1).hasDerivAt).deriv
  simp only [G] at hFa hF0
  rw [hFa, hF0]
  -- the sine part
  rw [sinZeta_div_eq_sum hk hre]
  -- split off `r = 0`
  have hsplit : ∀ f : ℕ → ℂ, ∑ r ∈ Finset.range k, f r = f 0 + ∑ r ∈ Finset.Ico 1 k, f r := by
    intro f
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  rw [hsplit, hsplit]
  simp only [c, Nat.cast_zero, zero_div, mul_zero, zero_mul, Real.cos_zero, Real.sin_zero,
    QuotientAddGroup.mk_zero, hurwitzZeta_zero, Complex.ofReal_zero, Complex.ofReal_one, one_mul,
    zero_add]
  have hsin : ∑ r ∈ Finset.Ico 1 k, Complex.sin (2 * π * r * h / k) *
      DLMF.Gamma.polygamma (2 * n - 1) ((r : ℂ) / k) = ((2 * n - 1 : ℕ) ! : ℂ) *
      ∑ r ∈ Finset.Ico 1 k, (Real.sin (2 * π * r * h / k) : ℂ) *
        hurwitzZeta ((r / k : ℝ) : UnitAddCircle) s₀ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' := Finset.mem_Ico.mp hr
    have hp := DLMF.Gamma.polygamma_eq_hurwitzZeta (n := 2 * n - 1) (by omega) (a := r / k)
      (by have : (0 : ℝ) < r := by exact_mod_cast hr'.1
          positivity)
      (div_le_one_of_le₀ (by exact_mod_cast hr'.2.le) hkR.le)
    rw [show ((2 * n - 1 : ℕ) : ℂ) + 1 = s₀ by
      simp only [s₀]; rw [Nat.cast_sub (by omega)]; push_cast; ring,
      show 2 * n - 1 + 1 = 2 * n by omega, pow_mul] at hp
    simp only [neg_one_sq, one_pow, one_mul] at hp
    push_cast at hp ⊢
    rw [hp]
    ring
  have hcos : ∑ r ∈ Finset.Ico 1 k, Complex.cos (2 * π * r * h / k) *
      deriv (hurwitzZeta ((r / k : ℝ) : UnitAddCircle)) s₀ =
      ∑ r ∈ Finset.Ico 1 k, (Real.cos (2 * π * r * h / k) : ℂ) *
        deriv (hurwitzZeta ((r / k : ℝ) : UnitAddCircle)) s₀ := by
    push_cast; rfl
  rw [hsin, hcos]
  have hCa : cosZeta a s₀ = (-1) ^ (n + 1) * (2 * π) ^ (2 * n) / 2 / (2 * n)! *
      ((Polynomial.bernoulli (2 * n)).map (algebraMap ℚ ℂ)).eval ((h : ℂ) / k) := by
    rw [ha_def, cosZeta_two_mul_nat (by omega) ⟨by positivity,
      div_le_one_of_le₀ (by exact_mod_cast hhk) hkR.le⟩]
    push_cast; ring
  have hlog : Complex.log (2 * π * k) = Complex.log (2 * π) + Complex.log k := by
    rw [show (2 * π * k : ℂ) = ((2 * π : ℝ) : ℂ) * ((k : ℝ) : ℂ) by push_cast; ring,
      show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      show (k : ℂ) = ((k : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul,
      ← Complex.ofReal_log (by positivity), ← Complex.ofReal_log (by positivity),
      ← Complex.ofReal_log (by positivity), Real.log_mul (by positivity) hkR.ne']
    push_cast; ring
  have hz := riemannZeta_two_mul_nat (k := n) (by omega)
  rw [← hs₀_def] at hz
  rw [hCa, hz, hlog]
  have hs₀n : s₀ = ((2 * n : ℕ) : ℂ) := by simp only [s₀]; push_cast; ring
  rw [show (2 * π : ℂ) ^ (-s₀) = ((2 * (π : ℂ)) ^ (2 * n))⁻¹ by rw [cpow_neg, hs₀n, cpow_natCast],
    show (k : ℂ) ^ (-s₀) = ((k : ℂ) ^ (2 * n))⁻¹ by rw [cpow_neg, hs₀n, cpow_natCast]]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hΓ := Complex.Gamma_nat_eq_factorial (2 * j + 1)
  rw [show ((2 * j + 1 : ℕ) : ℂ) + 1 = s₀ by simp only [s₀]; push_cast; ring] at hΓ
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, hΓ,
    show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.factorial_succ (2 * j + 1)]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hF : ((2 * j + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hj : (2 * (j : ℂ) + 1 + 1) ≠ 0 := by norm_cast
  rw [hs₀_def]
  push_cast
  generalize digamma (2 * ((j : ℂ) + 1)) = ψ
  generalize ((2 * j + 1)! : ℂ) = F at *
  rcases neg_one_pow_eq_or ℂ (j + 1) with h | h <;> rw [pow_succ (-1 : ℂ) (j + 1), h] <;>
    field_simp <;> ring

/-- **Sum of derivatives over a period** (DLMF 25.11.24): for `s ≠ 1`, `k = 1, 2, 3, …`,
`∑_{r=1}^{k-1} ζ'(s, r/k) = (k^s - 1) ζ'(s) + k^s ζ(s) ln k`. -/
@[dlmf 25.11.E24]
theorem sum_deriv_hurwitzZeta_rat {s : ℂ} (hs : s ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    ∑ r ∈ Finset.Ico 1 k, deriv (hurwitzZeta ((r / k : ℝ) : UnitAddCircle)) s =
      ((k : ℂ) ^ s - 1) * deriv riemannZeta s + (k : ℂ) ^ s * riemannZeta s * Real.log k :=
  sum_deriv_hurwitzZeta_div_eq hs hk

end DLMF.Zeta

end

end
