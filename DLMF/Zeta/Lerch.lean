/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Polylog
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-!
# Lerch's transcendent (DLMF §25.14)

* `lerchPhiSeries z s a = ∑_{n≥0} zⁿ/(a+n)^s` (DLMF 25.14.1), principal powers, as a `tsum`.
* `lerchPhi z s a` is DLMF's `Φ(z, s, a)`: for fixed `s`, `a` the analytic continuation in `z` of
  the series from the unit disk to the cut plane `ℂ \ [1, ∞)`, chosen as for `DLMF.Zeta.polylog`
  (`z25b_slitContinuation`), and the series itself on `[1, ∞)` (so `Φ(1, s, a) = ζ(s, a)` for
  `Re s > 1`). DLMF's parameter conditions (`|ph a| < π` if `s ∉ ℤ`; `a ≠ 0, -1, -2, …` if
  `s = 1, 2, …`; any `a` if `s = 0, -1, -2, …`) are `z25b_lerchParamOK s a`. The existence of the
  continuation, together with the convergence of the series in the disk, is the admitted
  `exists_lerchPhi_continuation` (DLMF §25.14(i), "defined by analytic continuation").

**Domain of Lerch's transformation formula 25.14.7.** DLMF prints no conditions. Numerically
(mpmath, 150 sample points) the formula holds for `0 < Re a < 1` and `0 < |z| < 1` and fails in
general for `Re a ∉ (0, 1)` (e.g. `a = 1.6 + 0.2i`, `a = -0.4 + 0.3i`, `a = 1`) and for `|z| ≥ 1`
(e.g. `z = 0.6 - 0.8i`, `z = 3 + 0.4i` with `Im a < 0`); it is acquired on the verified domain.

**25.14.9** is a convergent expansion for `|z| > 1` (the second sum diverges for `|z| < 1`); it is
acquired as an exact identity for `|z| > 1`, `|ph z| < π` (for `m ≥ 1` also `a ≠ 1, 2, …`, as
DLMF requires, and `a ≠ 0, -1, …`, needed for `Φ(-z, m, a)`).
-/

@[expose] public section

open Complex Filter Set MeasureTheory
open scoped Nat Real Topology

noncomputable section

namespace DLMF.Zeta

open DLMF.Confluent (hurwitzZetaComplex)

/-- **Lerch's series** `∑_{n≥0} zⁿ/(a+n)^s` (DLMF 25.14.1), as a `tsum`, principal powers. -/
@[dlmf 25.14.E1]
def lerchPhiSeries (z s a : ℂ) : ℂ := ∑' n : ℕ, z ^ n / (a + n) ^ s

open scoped Classical in
/-- **Lerch's transcendent** `Φ(z, s, a)` (DLMF §25.14(i)): the analytic continuation in `z` of
25.14.1 from the unit disk to `ℂ \ [1, ∞)`, and the series on `[1, ∞)`. -/
@[dlmf 25.14.i]
def lerchPhi (z s a : ℂ) : ℂ :=
  if z ∈ z25b_slitOne then z25b_slitContinuation (fun w => lerchPhiSeries w s a) z
  else lerchPhiSeries z s a

/-- DLMF's conditions on `a` in 25.14.1: `|ph a| < π` if `s` is not an integer, and
`a ≠ 0, -1, -2, …` if `s` is a positive integer (no condition if `s = 0, -1, -2, …`). -/
def z25b_lerchParamOK (s a : ℂ) : Prop :=
  ((∀ n : ℤ, s ≠ n) → a ∈ slitPlane) ∧ ((∃ n : ℕ, s = n + 1) → ∀ m : ℕ, a ≠ -m)

lemma z25b_lerchParamOK_add_nat {s a : ℂ} (h : z25b_lerchParamOK s a) (m : ℕ) :
    z25b_lerchParamOK s (a + m) := by
  refine ⟨fun hs => ?_, fun hs j hj => h.2 hs (j + m) (by push_cast; linear_combination hj)⟩
  rcases h.1 hs with h1 | h1
  · left; simp only [add_re, natCast_re]; positivity
  · right; simpa using h1

/-- **Convergence and continuation** (DLMF §25.14(i)): under the conditions of 25.14.1, the series
converges in the unit disk and extends analytically in `z` to `ℂ \ [1, ∞)`. -/
@[dlmf 25.14.i]
theorem exists_lerchPhi_continuation {s a : ℂ} (h : z25b_lerchParamOK s a) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F z25b_slitOne ∧
      ∀ z, ‖z‖ < 1 → HasSum (fun n : ℕ => z ^ n / (a + n) ^ s) (F z) := by
  have _ := h
  exact q25b_exists_isLerchCont s a

lemma z25b_lerchPhi_spec {s a : ℂ} (h : z25b_lerchParamOK s a) :
    AnalyticOnNhd ℂ (z25b_slitContinuation (fun w => lerchPhiSeries w s a)) z25b_slitOne ∧
      ∀ z, ‖z‖ < 1 → HasSum (fun n : ℕ => z ^ n / (a + n) ^ s)
        (z25b_slitContinuation (fun w => lerchPhiSeries w s a) z) := by
  obtain ⟨F, hF, hFz⟩ := exists_lerchPhi_continuation h
  have he : ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F z25b_slitOne ∧
      ∀ z, ‖z‖ < 1 → F z = lerchPhiSeries z s a :=
    ⟨F, hF, fun z hz => (hFz z hz).tsum_eq.symm⟩
  unfold z25b_slitContinuation
  simp only [he, ↓reduceDIte]
  refine ⟨he.choose_spec.1, fun z hz => ?_⟩
  rw [he.choose_spec.2 z hz, lerchPhiSeries]
  exact (hFz z hz).summable.hasSum

/-- On the cut plane, `Φ(z, s, a)` is the value of any continuation of Lerch's series (no
conditions on `s`, `a`). -/
lemma q25b_lerchPhi_eq {s a : ℂ} {F : ℂ → ℂ} (hF : q25b_IsLerchCont s a F) {z : ℂ}
    (hz : z ∈ z25b_slitOne) : lerchPhi z s a = F z := by
  obtain ⟨G, hG⟩ := q25b_exists_isLerchCont s a
  have he : ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F z25b_slitOne ∧
      ∀ z, ‖z‖ < 1 → F z = lerchPhiSeries z s a :=
    ⟨G, hG.1, fun z hz => (hG.2 z hz).tsum_eq.symm⟩
  simp only [lerchPhi, hz, ↓reduceIte, z25b_slitContinuation, he, ↓reduceDIte]
  refine q25b_eqOn_slit he.choose_spec.1 hF.1 (fun w hw => ?_) hz
  rw [he.choose_spec.2 w hw, lerchPhiSeries]
  exact (hF.2 w hw).tsum_eq

/-- For `Re s > 1` and `|z| ≤ 1`, Lerch's series converges (any `a`, Lean's conventions). -/
lemma q25b_summable_lerch_of_norm_le_one {s a z : ℂ} (hs : 1 < s.re) (hz : ‖z‖ ≤ 1) :
    Summable fun n : ℕ => z ^ n / (a + n) ^ s := by
  obtain ⟨m, hm⟩ := exists_nat_gt (-a.re)
  exact (q25b_hasSum_shift m (q25b_hasSum_lerchInt (a := a + m) (by linarith) (by simp; linarith)
    (Or.inr ⟨hz, hs⟩))).summable

/-- **The series in the unit disk** (DLMF 25.14.1): `Φ(z, s, a) = ∑ zⁿ/(a+n)^s` for `|z| < 1`
under the conditions on `a`. -/
@[dlmf 25.14.E1]
theorem hasSum_lerchPhi {z s a : ℂ} (h : z25b_lerchParamOK s a) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ n / (a + n) ^ s) (lerchPhi z s a) := by
  simp only [lerchPhi, z25b_mem_slitOne_of_norm_lt_one hz, ↓reduceIte]
  exact (z25b_lerchPhi_spec h).2 z hz

/-- **The series on the unit circle** (DLMF 25.14.1): for `|z| = 1` and `Re s > 1` (at `z = 1` by
definition; otherwise by Abel's theorem). -/
@[dlmf 25.14.E1]
theorem hasSum_lerchPhi_of_norm_eq_one {z s a : ℂ} (h : z25b_lerchParamOK s a) (hs : 1 < s.re)
    (hz : ‖z‖ = 1) :
    HasSum (fun n : ℕ => z ^ n / (a + n) ^ s) (lerchPhi z s a) := by
  have _ := h
  by_cases h1 : z = 1
  · subst h1
    have h1' : (1 : ℂ) ∉ z25b_slitOne := by simp [z25b_slitOne]
    simp only [lerchPhi, h1', ↓reduceIte, lerchPhiSeries]
    exact (q25b_summable_lerch_of_norm_le_one hs hz.le).hasSum
  · obtain ⟨F, hF⟩ := q25b_exists_isLerchCont s a
    have hzs := q25b_mem_slitOne_of_norm_le_one hz.le h1
    rw [q25b_lerchPhi_eq hF hzs]
    exact hF.hasSum_of_norm_le_one hs hz.le hzs

/-- **Analyticity in `z`** (DLMF §25.14(i)). -/
@[dlmf 25.14.i]
theorem analyticOnNhd_lerchPhi {s a : ℂ} (h : z25b_lerchParamOK s a) :
    AnalyticOnNhd ℂ (fun z => lerchPhi z s a) z25b_slitOne := by
  refine (z25b_lerchPhi_spec h).1.congr z25b_isOpen_slitOne fun z hz => ?_
  simp only [lerchPhi, hz, ↓reduceIte]

lemma z25b_hasSum_lerchPhi_of_cond {z s a : ℂ} (h : z25b_lerchParamOK s a)
    (hz : ‖z‖ < 1 ∨ (‖z‖ = 1 ∧ 1 < s.re)) :
    HasSum (fun n : ℕ => z ^ n / (a + n) ^ s) (lerchPhi z s a) := by
  rcases hz with hz | ⟨hz, hs⟩
  · exact hasSum_lerchPhi h hz
  · exact hasSum_lerchPhi_of_norm_eq_one h hs hz

/-- **Hurwitz zeta as a special case** (DLMF 25.14.2): `ζ(s, a) = Φ(1, s, a)` for `Re s > 1`,
`a ≠ 0, -1, -2, …`. -/
@[dlmf 25.14.E2]
theorem hurwitzZetaComplex_eq_lerchPhi {s a : ℂ} (hs : 1 < s.re) (ha : ∀ m : ℕ, a ≠ -m) :
    hurwitzZetaComplex s a = lerchPhi 1 s a := by
  have h1 : (1 : ℂ) ∉ z25b_slitOne := by simp [z25b_slitOne]
  simp only [lerchPhi, h1, ↓reduceIte, lerchPhiSeries, one_pow]
  rw [← (hasSum_hurwitzZetaComplex hs ha).tsum_eq]
  simp_rw [add_comm]

/-- **The polylogarithm as a special case** (DLMF 25.14.3): `Li_s(z) = z Φ(z, s, 1)` for `Re s > 1`,
`|z| ≤ 1`. -/
@[dlmf 25.14.E3]
theorem polylog_eq_mul_lerchPhi {s z : ℂ} (hs : 1 < s.re) (hz : ‖z‖ ≤ 1) :
    polylog s z = z * lerchPhi z s 1 := by
  have hp : z25b_lerchParamOK s 1 :=
    ⟨fun _ => Or.inl (by simp), fun _ m hm => by
      have := congrArg Complex.re hm; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]⟩
  have hc : ‖z‖ < 1 ∨ (‖z‖ = 1 ∧ 1 < s.re) := by
    rcases hz.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hs⟩
  have hL := (z25b_hasSum_lerchPhi_of_cond hp hc).mul_left z
  have hP : HasSum (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1) ^ s) (polylog s z) := by
    rcases hc with h | ⟨h, -⟩
    · exact hasSum_polylog h
    · exact hasSum_polylog_of_norm_eq_one hs h
  refine hP.unique (hL.congr_fun fun n => ?_)
  rw [pow_succ, add_comm (1 : ℂ)]
  ring

/-- **Expansion about `z = 1`** (DLMF 25.14.3_1): for `|ln z| < 2π`, `s ≠ 1, 2, 3, …`,
`a ≠ 0, -1, -2, …`,
`z^a Φ(z, s, a) = Γ(1-s)(-ln z)^{s-1} + ∑_{n≥0} ζ(s-n, a)(ln z)ⁿ/n!`. We take `z ∈ ℂ \ [1, ∞)`,
`z ≠ 0` (on the cut the principal branch is not defined) and DLMF's conditions on `a`. -/
@[dlmf 25.14.E3_1]
theorem hasSum_lerchPhi_log {z s a : ℂ} (hs : ∀ n : ℕ, s ≠ n + 1) (ha : z25b_lerchParamOK s a)
    (ha' : ∀ m : ℕ, a ≠ -m) (hz : z ∈ z25b_slitOne) (hz0 : z ≠ 0)
    (hlog : ‖Complex.log z‖ < 2 * π) :
    HasSum (fun n : ℕ => hurwitzZetaComplex (s - n) a * Complex.log z ^ n / n !)
      (z ^ a * lerchPhi z s a - Gamma (1 - s) * (-Complex.log z) ^ (s - 1)) := by
  sorry

/-- **Expansion about `z = 1`, integer order** (DLMF 25.14.3_2): for `m = 2, 3, …`, `|ln z| < 2π`,
`a ≠ 0, -1, -2, …`, `z^a Φ(z, m, a) = ∑'_{n≥0} ζ(m-n, a)(ln z)ⁿ/n! + ((ln z)^{m-1}/(m-1)!)
(ψ(m) - ψ(a) - ln(-ln z))`, the prime omitting `n = m - 1`; `z ∈ ℂ \ [1, ∞)`, `z ≠ 0`. -/
@[dlmf 25.14.E3_2]
theorem hasSum_lerchPhi_log_nat {m : ℕ} (hm : 2 ≤ m) {z a : ℂ} (ha : ∀ k : ℕ, a ≠ -k)
    (hz : z ∈ z25b_slitOne) (hz0 : z ≠ 0) (hlog : ‖Complex.log z‖ < 2 * π) :
    HasSum (fun n : ℕ => if n = m - 1 then 0 else
        hurwitzZetaComplex ((m : ℂ) - n) a * Complex.log z ^ n / n !)
      (z ^ a * lerchPhi z m a - Complex.log z ^ (m - 1) / (m - 1)! *
        (digamma m - digamma a - Complex.log (-Complex.log z))) := by
  sorry

/-- **Order one** (DLMF 25.14.3_3): `a Φ(z, 1, a) = F(a, 1; a+1; z)` (Gauss's hypergeometric
function) for `|z| < 1`, `a ≠ 0, -1, -2, …`. -/
@[dlmf 25.14.E3_3]
theorem mul_lerchPhi_one_eq_hypergeometric {z a : ℂ} (hz : ‖z‖ < 1) (ha : ∀ m : ℕ, a ≠ -m) :
    a * lerchPhi z 1 a = ordinaryHypergeometric a 1 (a + 1) z := by
  have hP : ∀ n : ℕ,
      (ascPochhammer ℂ n).eval a * (a + n) = a * (ascPochhammer ℂ n).eval (a + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
      push_cast
      linear_combination (a + 1 + n) * ih
  have hcoef : ∀ n : ℕ, ((n ! : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval 1 *
      ((ascPochhammer ℂ n).eval (a + 1))⁻¹) = a / (a + n) := by
    intro n
    have hn : a + n ≠ 0 := fun h => ha n (by linear_combination h)
    have hq : (ascPochhammer ℂ n).eval (a + 1) ≠ 0 := by
      rw [Ne, ascPochhammer_eval_eq_zero_iff]
      rintro ⟨k, -, hk⟩
      exact ha (k + 1) (by push_cast; linear_combination hk)
    rw [ascPochhammer_eval_one]
    have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    field_simp
    linear_combination hP n
  have hp : z25b_lerchParamOK 1 a :=
    ⟨fun h => absurd rfl (by exact_mod_cast h 1), fun _ m hm => ha m hm⟩
  rw [ordinaryHypergeometric_eq_tsum, ← ((hasSum_lerchPhi hp hz).mul_left a).tsum_eq]
  congr 1; funext n
  rw [hcoef n, smul_eq_mul, cpow_one]
  ring

/-! ### §25.14(ii) Properties -/

/-- **Recurrence in `a`** (DLMF 25.14.4): under the conditions of 25.14.1 (`|z| < 1`, or `|z| = 1`
and `Re s > 1`) and `m = 1, 2, 3, …`,
`Φ(z, s, a) = z^m Φ(z, s, a+m) + ∑_{n=0}^{m-1} zⁿ/(a+n)^s` (valid also for `m = 0`). -/
@[dlmf 25.14.E4]
theorem lerchPhi_eq_add_nat {z s a : ℂ} (h : z25b_lerchParamOK s a)
    (hz : ‖z‖ < 1 ∨ (‖z‖ = 1 ∧ 1 < s.re)) (m : ℕ) :
    lerchPhi z s a = z ^ m * lerchPhi z s (a + m) +
      ∑ n ∈ Finset.range m, z ^ n / (a + n) ^ s := by
  have h1 := (hasSum_nat_add_iff' m).mpr (z25b_hasSum_lerchPhi_of_cond h hz)
  have h2 := (z25b_hasSum_lerchPhi_of_cond (z25b_lerchParamOK_add_nat h m) hz).mul_left (z ^ m)
  have h3 : HasSum (fun n : ℕ => z ^ (n + m) / (a + ↑(n + m)) ^ s)
      (z ^ m * lerchPhi z s (a + m)) := by
    refine h2.congr_fun fun n => ?_
    rw [pow_add]; push_cast; ring_nf
  rw [← h1.unique h3]
  ring

/-- **Integral representation** (DLMF 25.14.5):
`Φ(z, s, a) = (1/Γ(s)) ∫_0^∞ x^{s-1} e^{-ax}/(1 - z e^{-x}) dx` for `Re s > 1`, `Re a > 0` if
`z = 1`, and `Re s > 0`, `Re a > 0` if `z ∈ ℂ \ [1, ∞)`. -/
@[dlmf 25.14.E5]
theorem lerchPhi_eq_integral {z s a : ℂ} (ha : 0 < a.re)
    (h : (z = 1 ∧ 1 < s.re) ∨ (z ∈ z25b_slitOne ∧ 0 < s.re)) :
    lerchPhi z s a = 1 / Gamma s *
      ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * cexp (-(a * x)) / (1 - z * cexp (-(x : ℂ))) := by
  rw [one_div]
  rcases h with ⟨rfl, hs⟩ | ⟨hz, hs⟩
  · have h1' : (1 : ℂ) ∉ z25b_slitOne := by simp [z25b_slitOne]
    simp only [lerchPhi, h1', ↓reduceIte, lerchPhiSeries]
    exact (q25b_hasSum_lerchInt (by linarith) ha (Or.inr ⟨by simp, hs⟩)).tsum_eq
  · obtain ⟨F, hF⟩ := q25b_exists_isLerchCont s a
    rw [q25b_lerchPhi_eq hF hz, hF.eq_lerchInt hs ha hz]
    rfl

/-- **Hermite-type formula** (DLMF 25.14.6): `Φ(z, s, a) = a^{-s}/2 + ∫_0^∞ z^x/(a+x)^s dx
- 2 ∫_0^∞ sin(x ln z - s arctan(x/a))/((a²+x²)^{s/2}(e^{2πx}-1)) dx` for `Re a > 0` if `|z| < 1`
(and `z ≠ 0`), and `Re s > 1`, `Re a > 0` if `|z| = 1` (then the first integral converges
conditionally and is the limit of `∫_0^X`). Principal branches throughout. -/
@[dlmf 25.14.E6]
theorem tendsto_lerchPhi_hermite {z s a : ℂ} (ha : 0 < a.re)
    (h : (0 < ‖z‖ ∧ ‖z‖ < 1) ∨ (‖z‖ = 1 ∧ 1 < s.re)) :
    Tendsto (fun X : ℝ => a ^ (-s) / 2 + (∫ x in (0 : ℝ)..X, z ^ (x : ℂ) / (a + x) ^ s) -
        2 * ∫ x in Ioi (0 : ℝ), Complex.sin (x * Complex.log z - s * Complex.arctan (x / a)) /
          ((a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2) * (Real.exp (2 * π * x) - 1 : ℝ))) atTop
      (𝓝 (lerchPhi z s a)) := by
  sorry

/-- **Lerch's transformation formula** (DLMF 25.14.7), on the verified domain `0 < Re a < 1`,
`0 < |z| < 1` (see the module docstring):
`Φ(z, s, a) = (i(2π)^{s-1}/z^a) Γ(1-s) (e^{-πis/2} Φ(e^{-2πia}, 1-s, ln z/(2πi))
 - e^{πi(2a + s/2)} Φ(e^{2πia}, 1-s, 1 - ln z/(2πi)))`, principal `ln z` and `z^a`. -/
@[dlmf 25.14.E7]
theorem lerchPhi_transformation {z s a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re < 1) (hz0 : z ≠ 0)
    (hz : ‖z‖ < 1) :
    lerchPhi z s a = I * (2 * π) ^ (s - 1) / z ^ a * Gamma (1 - s) *
      (cexp (-π * I * s / 2) *
          lerchPhi (cexp (-2 * π * I * a)) (1 - s) (Complex.log z / (2 * π * I)) -
        cexp (π * I * (2 * a + s / 2)) *
          lerchPhi (cexp (2 * π * I * a)) (1 - s) (1 - Complex.log z / (2 * π * I))) := by
  sorry

/-- **Mellin–Barnes integral** (DLMF 25.14.8): for `|ph z| < π`, `Re a > 0` and
`max(-Re a, -1) < σ < 0`,
`Φ(-z, s, a) = (1/2πi) ∫_{σ-i∞}^{σ+i∞} Γ(1+t)Γ(-t) z^t/(a+t)^s dt`. -/
@[dlmf 25.14.E8]
theorem lerchPhi_neg_eq_mellinBarnes {z s a : ℂ} (hz : z ∈ slitPlane) (ha : 0 < a.re) {σ : ℝ}
    (hσ1 : max (-a.re) (-1) < σ) (hσ2 : σ < 0) :
    lerchPhi (-z) s a = 1 / (2 * π) *
      ∫ y : ℝ, Gamma (1 + (σ + y * I)) * Gamma (-(σ + y * I)) * z ^ (σ + y * I) /
        (a + (σ + y * I)) ^ s := by
  sorry

/-- **Large-`z` expansion for integer order** (DLMF 25.14.9): for integer `m`, `|ph z| < π` and
`|z| > 1`,
`Φ(-z, m, a) = -(π/z^a) ∑_{n=0}^{m-1} bₙ (ln z)^{m-n-1}/Γ(m-n) - ∑_{n≥1} (-z)^{-n}/(a-n)^m`,
`bₙ` the Taylor coefficients of `csc(π(t - a))` at `t = 0`; the first sum is empty for `m ≤ 0`; for
`m ≥ 1` also `a ≠ 0, ±1, ±2, …`. -/
@[dlmf 25.14.E9]
theorem hasSum_lerchPhi_neg_large {m : ℤ} {z a : ℂ} (hz : z ∈ slitPlane) (hz1 : 1 < ‖z‖)
    (ha : 1 ≤ m → ∀ k : ℤ, a ≠ k) :
    HasSum (fun n : ℕ => (-z) ^ (-((n + 1 : ℕ) : ℤ)) / (a - (n + 1 : ℕ)) ^ m)
      (-(π : ℂ) / z ^ a * ∑ n ∈ Finset.range m.toNat,
          iteratedDeriv n (fun t : ℂ => 1 / Complex.sin (π * (t - a))) 0 / n ! *
            Complex.log z ^ (m.toNat - n - 1) / Gamma (m - n) -
        lerchPhi (-z) m a) := by
  sorry

end DLMF.Zeta

end
