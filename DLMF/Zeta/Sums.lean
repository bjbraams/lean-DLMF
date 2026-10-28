/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.SeriesExpansions
public import DLMFMathlib.NumberTheory.BernoulliTaylor
public import Mathlib.Analysis.SpecialFunctions.Integrals.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import DLMF.Zeta.Riemann

/-!
# Sums involving the Riemann zeta function (DLMF §25.8)

The power series 25.8.5–25.8.8 are derived from the project's Taylor series of `ψ(1+z)` and
`ln Γ(1+z)` (DLMF 5.7.3, 5.7.4, in `DLMF.Gamma.SeriesExpansions`) and the cotangent series
`Complex.hasSum_pi_mul_cot_zeta` (DLMF 4.19.6). Logarithms are principal: for `|z| < 1` the
values `Γ(1-z)` and `πz/sin(πz)` stay off the negative real axis, so DLMF's `ln Γ(1-z)` (the
branch continuous from `ln Γ(1) = 0`) and `ln(πz/sin(πz))` agree with `Complex.log` there.

Lean restrictions. 25.8.6 excludes `z = 0`, where `πz cot(πz)` is a removable `0 · ∞` form
(Lean's `cot 0 = 0`); 25.8.3 excludes `s = 0, -1, -2, …` besides DLMF's `s ≠ 1`: there the term
`(s)_{1-s} ζ(1)` of the printed series is a `0 · ∞` form, for which Lean's totalized
`riemannZeta 1` gives a wrong value.
-/

@[expose] public noncomputable section

open Complex Filter Topology Finset
open scoped Real Nat

namespace DLMF.Zeta

/-- `∑_{n≥0} 1/((n+1)(n+2)) = 1` (telescoping). -/
lemma r25a_hasSum_telescope :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + 2) * ((n : ℝ) + 1))) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity)]
  have e : ∀ N : ℕ, ∑ i ∈ range N, 1 / (((i : ℝ) + 2) * ((i : ℝ) + 1)) = 1 - 1 / ((N : ℝ) + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, ih]
      push_cast
      field_simp
      ring
  simp_rw [e]
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1

/-- The fibre sums `∑_{k≥0} (n+2)^{-(k+2)} = 1/((n+2)(n+1))`. -/
lemma r25a_hasSum_geom (n : ℕ) :
    HasSum (fun k : ℕ => (1 / ((n : ℝ) + 2)) ^ (k + 2)) (1 / (((n : ℝ) + 2) * ((n : ℝ) + 1))) := by
  have hr0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 2) := by positivity
  have hr1 : 1 / ((n : ℝ) + 2) < 1 := by
    rw [div_lt_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left ((1 / ((n : ℝ) + 2)) ^ 2)
  convert h using 1
  · funext k; ring
  · rw [show (1 : ℝ) - 1 / ((n : ℝ) + 2) = ((n : ℝ) + 1) / ((n : ℝ) + 2) by field_simp; ring]
    field_simp

/-- DLMF 25.8.1: `∑_{k≥2} (ζ(k) - 1) = 1`. -/
@[dlmf 25.8.E1]
theorem hasSum_riemannZeta_sub_one :
    HasSum (fun k : ℕ => riemannZeta (k + 2) - 1) 1 := by
  set F : ℕ × ℕ → ℝ := fun p => (1 / ((p.1 : ℝ) + 2)) ^ (p.2 + 2) with hF
  have hF0 : 0 ≤ F := fun p => by simp only [hF]; positivity
  have hS : Summable F := (summable_prod_of_nonneg hF0).mpr
    ⟨fun n => (r25a_hasSum_geom n).summable, by
      simp only [hF]
      exact r25a_hasSum_telescope.summable.congr fun n => (r25a_hasSum_geom n).tsum_eq.symm⟩
  have h1 : HasSum F 1 := by
    have := hS.hasSum.prod_fiberwise fun n => r25a_hasSum_geom n
    rw [r25a_hasSum_telescope.unique this]; exact hS.hasSum
  have h2 : HasSum (F ∘ Prod.swap) 1 := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr h1
  have hfib : ∀ k : ℕ, HasSum (fun n : ℕ => (F ∘ Prod.swap) (k, n))
      (∑' n : ℕ, (1 / ((n : ℝ) + 2)) ^ (k + 2)) := fun k => by
    have : Summable (fun n : ℕ => (1 / ((n : ℝ) + 2)) ^ (k + 2)) :=
      ((summable_prod_of_nonneg (f := F ∘ Prod.swap) (fun p => hF0 p.swap)).mp
        ((Equiv.prodComm ℕ ℕ).summable_iff.mpr hS)).1 k
    exact this.hasSum
  have h3 := h2.prod_fiberwise hfib
  have h4 := (Complex.ofRealCLM.hasSum h3)
  refine h4.congr_fun fun k => ?_
  simp only [ofRealCLM_apply]
  have hz := zeta_nat_eq_tsum_of_gt_one (k := k + 2) (by omega)
  push_cast at hz
  rw [hz]
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (k + 2)) := by
    have := Complex.summable_one_div_nat_cpow.mpr (show 1 < ((k + 2 : ℕ) : ℂ).re by
      rw [Complex.natCast_re]; exact_mod_cast (by omega : 1 < k + 2))
    simpa only [cpow_natCast] using this
  rw [hsum.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hsum).tsum_eq_zero_add,
    Complex.ofReal_tsum]
  have e : ∀ b : ℕ, 1 / (((b + 1 + 1 : ℕ) : ℂ)) ^ (k + 2) =
      (((1 / ((b : ℝ) + 2)) ^ (k + 2) : ℝ) : ℂ) := fun b => by
    push_cast; rw [div_pow, one_pow]; congr 2; ring
  simp only [e]
  simp

/-- Binomial series in Pochhammer form: `(1-x)^{-a} = ∑ (a)_k x^k / k!` for `‖x‖ < 1`. -/
lemma s25a_hasSum_pochhammer (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ => (ascPochhammer ℂ k).eval a / k ! * x ^ k) (1 / (1 - x) ^ a) := by
  have h := (one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero a).hasSum (y := x) (by
    simp only [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
    exact ENNReal.ofReal_lt_one.mpr hx)
  simp only [zero_add] at h
  convert h using 2 with k
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have e : Ring.choose (a + k - 1) k = Ring.multichoose a k := (Ring.multichoose_eq a k).symm
  have h2 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a k
  rw [Polynomial.ascPochhammer_smeval_eq_eval, nsmul_eq_mul] at h2
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hm : (ascPochhammer ℂ k).eval a / k ! = Ring.multichoose a k := by
    rw [← h2]; field_simp
  rw [e, hm, mul_comm]

/-- `(t)_k ≥ 0` for `t ≥ 0`. -/
lemma s25a_pochhammer_nonneg {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : 0 ≤ (ascPochhammer ℝ k).eval t := by
  induction k with
  | zero => simp
  | succ k ih => rw [ascPochhammer_succ_eval]; positivity

/-- `‖(s)_k‖ ≤ (‖s‖)_k`. -/
lemma s25a_norm_pochhammer_le (s : ℂ) (k : ℕ) :
    ‖(ascPochhammer ℂ k).eval s‖ ≤ (ascPochhammer ℝ k).eval ‖s‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, norm_mul]
    refine mul_le_mul ih ?_ (norm_nonneg _) ?_
    · refine (norm_add_le _ _).trans ?_
      simp
    · exact s25a_pochhammer_nonneg (norm_nonneg s) k

/-- The domain `ℂ ∖ {1, 0, -1, -2, …}`. -/
def s25a_U : Set ℂ := (Set.range fun n : ℕ => (1 : ℂ) - n)ᶜ

/-- Formula under the stated hypotheses: `s ∈ s25a_U ↔ ∀ n : ℕ, s ≠ 1 - n`. -/
lemma s25a_mem_U {s : ℂ} : s ∈ s25a_U ↔ ∀ n : ℕ, s ≠ 1 - n := by
  simp [s25a_U, eq_comm]

/-- The indicated domain is open: `IsOpen s25a_U`. -/
lemma s25a_isOpen_U : IsOpen s25a_U := by
  have : (Set.range fun n : ℕ => (1 : ℂ) - n) =
      Set.range ((↑) : ℤ → ℂ) ∩ {z : ℂ | z.re ≤ 1} := by
    ext z
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨⟨1 - n, by push_cast; ring⟩, by simp⟩
    · rintro ⟨⟨m, rfl⟩, hm⟩
      have hm' : m ≤ 1 := by have : (m : ℝ) ≤ 1 := by simpa using hm
                             exact_mod_cast this
      refine ⟨(1 - m).toNat, ?_⟩
      have : (((1 - m).toNat : ℤ) : ℂ) = 1 - m := by
        rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring
      show (1 : ℂ) - (((1 - m).toNat : ℕ) : ℂ) = m
      rw [show (((1 - m).toNat : ℕ) : ℂ) = (((1 - m).toNat : ℤ) : ℂ) by norm_cast, this]
      ring
  rw [s25a_U, this, isOpen_compl_iff]
  exact Complex.isClosed_range_intCast.inter (isClosed_le continuous_re continuous_const)

/-- The stated relation follows from the given hypotheses: `IsPreconnected s25a_U`. -/
lemma s25a_isPreconnected_U : IsPreconnected s25a_U :=
  ((Set.countable_range _).isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected

/-- Estimate under the stated parameter and domain assumptions: `{s : ℂ | 1 < s.re} ⊆ s25a_U`. -/
lemma s25a_re_gt_subset_U : {s : ℂ | 1 < s.re} ⊆ s25a_U := by
  intro s hs
  have hs' : 1 < s.re := hs
  rw [s25a_mem_U]
  intro n h
  have := congrArg re h
  simp at this
  have : s.re = 1 - n := this
  linarith [hs', (n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- `ζ(w) = ∑_{n≥0} (n+1)^{-w}` for `Re w > 1`, as a `HasSum`. -/
lemma s25a_hasSum_zeta {w : ℂ} (hw : 1 < w.re) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ w) (riemannZeta w) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hw]
  refine Summable.hasSum ?_
  have := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hw)
  simpa using this

/-- `‖ζ(w) - 1‖ ≤ 2^{2 - Re w} C` for `Re w ≥ 2`. -/
lemma s25a_norm_zeta_sub_one_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 2 ≤ w.re →
    ‖riemannZeta w - 1‖ ≤ (2 : ℝ) ^ (2 - w.re) * C := by
  have hC : Summable fun n : ℕ => 1 / ((n : ℝ) + 2) ^ (2 : ℕ) := by
    have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    refine (this.comp_injective (add_left_injective 2)).congr fun n => ?_
    simp [Function.comp]
  refine ⟨∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ (2 : ℕ), tsum_nonneg fun n => by positivity, ?_⟩
  intro w hw
  have hs1 : 1 < w.re := by linarith
  have hz := s25a_hasSum_zeta hs1
  have ht : HasSum (fun n : ℕ => 1 / ((n + 1 : ℕ) + 1 : ℂ) ^ w) (riemannZeta w - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr hz
    simpa using this
  have hn (n : ℕ) : ‖1 / ((n + 1 : ℕ) + 1 : ℂ) ^ w‖ ≤
      (2 : ℝ) ^ (2 - w.re) * (1 / ((n : ℝ) + 2) ^ (2 : ℕ)) := by
    have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    rw [show (((n + 1 : ℕ) : ℂ) + 1) = (((n : ℝ) + 2 : ℝ) : ℂ) by push_cast; ring, norm_div,
      norm_one, norm_cpow_eq_rpow_re_of_pos hpos]
    rw [show (2 : ℝ) ^ (2 - w.re) * (1 / ((n : ℝ) + 2) ^ (2 : ℕ)) =
      ((2 : ℝ) / ((n : ℝ) + 2)) ^ (2 - w.re) / ((n : ℝ) + 2) ^ w.re by
        rw [Real.div_rpow (by norm_num) hpos.le, Real.rpow_sub hpos, Real.rpow_two]
        field_simp]
    have h1 : ((2 : ℝ) / ((n : ℝ) + 2)) ^ (2 - w.re) ≥ 1 := by
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity)
      · rw [div_le_one hpos]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      · linarith
    have h2 : 0 < ((n : ℝ) + 2) ^ w.re := Real.rpow_pos_of_pos hpos _
    rw [div_le_div_iff_of_pos_right h2]
    exact h1
  calc ‖riemannZeta w - 1‖ = ‖∑' n : ℕ, 1 / ((n + 1 : ℕ) + 1 : ℂ) ^ w‖ := by
        rw [ht.tsum_eq]
    _ ≤ ∑' n : ℕ, (2 : ℝ) ^ (2 - w.re) * (1 / ((n : ℝ) + 2) ^ (2 : ℕ)) :=
        tsum_of_norm_bounded (hC.mul_left _).hasSum hn
    _ = _ := tsum_mul_left

/-- The real Pochhammer series `∑ (t)_k/k! x^k` converges for `0 ≤ x < 1`. -/
lemma s25a_summable_pochhammer_real (t : ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Summable fun k : ℕ => (ascPochhammer ℝ k).eval t / k ! * x ^ k := by
  have h := (s25a_hasSum_pochhammer (t : ℂ) (x := (x : ℂ)) (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx)).summable
  have e : ∀ k : ℕ, (ascPochhammer ℂ k).eval (t : ℂ) / k ! * (x : ℂ) ^ k =
      (((ascPochhammer ℝ k).eval t / k ! * x ^ k : ℝ) : ℂ) := by
    intro k
    rw [show (ascPochhammer ℂ k).eval (t : ℂ) = (((ascPochhammer ℝ k).eval t : ℝ) : ℂ) by
      rw [← ascPochhammer_map (algebraMap ℝ ℂ), Polynomial.eval_map]
      exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) t]
    push_cast; ring
  simp_rw [e] at h
  exact Complex.summable_ofReal.mp h

/-- DLMF 25.8.3 for `Re s > 1`. -/
lemma s25a_hasSum_838_re {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => (ascPochhammer ℂ k).eval s * riemannZeta (s + k) / (k ! * 2 ^ (s + k)))
      ((1 - 2 ^ (-s)) * riemannZeta s) := by
  set b : ℕ → ℝ := fun m => 2 * ((m : ℝ) + 1) with hb
  have hb0 : ∀ m, 0 < b m := fun m => by positivity
  have hb2 : ∀ m, 2 ≤ b m := fun m => by
    simp only [hb]; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  set f : ℕ × ℕ → ℂ := fun p => ((b p.2 : ℝ) : ℂ) ^ (-s) *
    ((ascPochhammer ℂ p.1).eval s / p.1 ! * (1 / ((b p.2 : ℝ) : ℂ)) ^ p.1) with hf
  have hx : ∀ m, ‖1 / ((b m : ℝ) : ℂ)‖ ≤ 1 / 2 := by
    intro m
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hb0 m)]
    exact one_div_le_one_div_of_le (by norm_num) (hb2 m)
  have hsum : Summable f := by
    have hg : Summable fun m : ℕ => (b m) ^ (-s.re) := by
      have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (show -s.re < -1 by
        linarith))
      refine (this.mul_left ((2 : ℝ) ^ (-s.re))).congr fun m => ?_
      simp only [hb]
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      push_cast; ring_nf
    have hh := s25a_summable_pochhammer_real ‖s‖ (x := 1 / 2) (by norm_num) (by norm_num)
    refine Summable.of_norm_bounded (hh.mul_of_nonneg hg
      (fun k => by have := s25a_pochhammer_nonneg (norm_nonneg s) k; positivity)
      (fun m => by have := hb0 m; positivity)) fun p => ?_
    simp only [hf, norm_mul, norm_pow]
    rw [norm_div ((ascPochhammer ℂ p.1).eval s), Complex.norm_natCast,
      norm_cpow_eq_rpow_re_of_pos (hb0 p.2), neg_re]
    have h1 := s25a_norm_pochhammer_le s p.1
    have h2 : ‖1 / ((b p.2 : ℝ) : ℂ)‖ ^ p.1 ≤ (1 / 2) ^ p.1 :=
      pow_le_pow_left₀ (norm_nonneg _) (hx p.2) _
    have h3 : 0 ≤ (b p.2) ^ (-s.re) := (Real.rpow_pos_of_pos (hb0 p.2) _).le
    have h4 : (0 : ℝ) < p.1 ! := by exact_mod_cast Nat.factorial_pos _
    have h5 : 0 ≤ (ascPochhammer ℝ p.1).eval ‖s‖ / p.1 ! :=
      div_nonneg (s25a_pochhammer_nonneg (norm_nonneg s) _) h4.le
    calc (b p.2) ^ (-s.re) * (‖(ascPochhammer ℂ p.1).eval s‖ / p.1 ! *
          ‖1 / ((b p.2 : ℝ) : ℂ)‖ ^ p.1)
        ≤ (b p.2) ^ (-s.re) * ((ascPochhammer ℝ p.1).eval ‖s‖ / p.1 ! * (1 / 2) ^ p.1) := by
          gcongr
      _ = (ascPochhammer ℝ p.1).eval ‖s‖ / p.1 ! * (1 / 2) ^ p.1 * (b p.2) ^ (-s.re) := by ring
  have hk : ∀ k : ℕ, HasSum (fun m : ℕ => f (k, m))
      ((ascPochhammer ℂ k).eval s * riemannZeta (s + k) / (k ! * 2 ^ (s + k))) := by
    intro k
    have hre : 1 < (s + k).re := by simp; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    have h := (s25a_hasSum_zeta hre).mul_left
      ((ascPochhammer ℂ k).eval s / k ! * (1 / (2 : ℂ) ^ (s + k)))
    convert h using 1
    · funext m
      simp only [hf]
      have hB : ((b m : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hb0 m).ne'
      have e1 : (1 / ((b m : ℝ) : ℂ)) ^ k = ((b m : ℝ) : ℂ) ^ (-(k : ℂ)) := by
        rw [cpow_neg, cpow_natCast, one_div, inv_pow]
      have e2 : ((b m : ℝ) : ℂ) ^ (-(s + k)) =
          (2 : ℂ) ^ (-(s + k)) * ((m : ℂ) + 1) ^ (-(s + k)) := by
        simp only [hb]
        push_cast
        rw [show ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
          show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
          mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
      rw [e1, mul_left_comm, mul_assoc, ← cpow_add _ _ hB, show -s + -(k : ℂ) = -(s + k) by ring,
        e2, cpow_neg, cpow_neg, one_div, one_div]
    · ring
  have hm : ∀ m : ℕ, HasSum (fun k : ℕ => f (k, m)) (1 / (2 * (m : ℂ) + 1) ^ s) := by
    intro m
    have h := (s25a_hasSum_pochhammer s (x := 1 / ((b m : ℝ) : ℂ))
      ((hx m).trans_lt (by norm_num))).mul_left (((b m : ℝ) : ℂ) ^ (-s))
    convert h using 1
    have hb1 : (0 : ℝ) ≤ 1 - 1 / b m := by
      have := hb2 m
      rw [sub_nonneg, div_le_one (hb0 m)]; linarith
    have e : (1 : ℂ) - 1 / ((b m : ℝ) : ℂ) = ((1 - 1 / b m : ℝ) : ℂ) := by push_cast; ring
    rw [e, cpow_neg, ← one_div, div_mul_div_comm, one_mul,
      ← mul_cpow_ofReal_nonneg (hb0 m).le hb1]
    congr 2
    simp only [hb]
    push_cast
    have : (m : ℂ) + 1 ≠ 0 := by
      rw [show (m : ℂ) + 1 = ((m + 1 : ℕ) : ℂ) by push_cast; ring]
      exact_mod_cast (show m + 1 ≠ 0 by omega)
    field_simp
    ring
  have hodd := riemannZeta_eq_odd_series hs
  have hne : (1 : ℂ) - 2 ^ (-s) ≠ 0 := by
    have h2 : ‖(2 : ℂ) ^ (-s)‖ < 1 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, norm_cpow_eq_rpow_re_of_pos (by norm_num)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by simp; linarith)
    intro h0
    rw [sub_eq_zero] at h0
    rw [← h0] at h2
    simp at h2
  have hv : (1 - 2 ^ (-s)) * riemannZeta s = ∑' n : ℕ, 1 / (2 * n + 1 : ℂ) ^ s := by
    rw [hodd.2]; field_simp
  rw [hv]
  have := hsum.hasSum.prod_fiberwise hk
  rw [(((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hsum.hasSum).prod_fiberwise hm).tsum_eq]
  exact this

/-- Analytic continuation of a series identity from `Re s > 1` to `ℂ ∖ {1, 0, -1, …}`. -/
lemma s25a_continuation (T : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (hT : ∀ k, DifferentiableOn ℂ (T k) s25a_U) (hg : DifferentiableOn ℂ g s25a_U)
    (hdom : ∀ x ∈ s25a_U, ∃ V ∈ 𝓝 x, ∃ N : ℕ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n, N ≤ n → ∀ y ∈ V, ‖T n y‖ ≤ u n)
    (hre : ∀ s : ℂ, 1 < s.re → HasSum (fun k => T k s) (g s)) :
    ∀ s ∈ s25a_U, HasSum (fun k => T k s) (g s) := by
  have hsum : ∀ s ∈ s25a_U, Summable fun k => T k s := by
    intro s hs
    obtain ⟨V, hV, N, u, hu, hle⟩ := hdom s hs
    refine (summable_nat_add_iff N).mp ?_
    exact Summable.of_norm_bounded ((summable_nat_add_iff N).mpr hu)
      fun k => hle (k + N) (by omega) s (mem_of_mem_nhds hV)
  have hd : DifferentiableOn ℂ (fun s => ∑' k, T k s) s25a_U :=
    Complex.differentiableOn_tsum_of_eventually_dominated s25a_isOpen_U hT hdom
  have h2 : (2 : ℂ) ∈ s25a_U := s25a_re_gt_subset_U (by norm_num)
  have heq : Set.EqOn (fun s => ∑' k, T k s) g s25a_U := by
    refine (hd.analyticOnNhd s25a_isOpen_U).eqOn_of_preconnected_of_eventuallyEq
      (hg.analyticOnNhd s25a_isOpen_U) s25a_isPreconnected_U h2 ?_
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact (hre z hz).tsum_eq
  intro s hs
  rw [← heq hs]
  exact (hsum s hs).hasSum

/-- `t ↦ (t)_k` is monotone on `[0, ∞)`. -/
lemma s25a_pochhammer_mono {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) (k : ℕ) :
    (ascPochhammer ℝ k).eval t ≤ (ascPochhammer ℝ k).eval u := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
    exact mul_le_mul ih (by linarith) (by positivity)
      (s25a_pochhammer_nonneg (ht.trans htu) k)

/-- Local data for the dominations: near `x`, `‖y‖ ≤ R` and, for `n ≥ N`, `Re(y+n) ≥ 2` and
`‖2^{-(y+n)}‖ ≤ 2^R 2^{-n}`. -/
lemma s25a_local (x : ℂ) : ∃ V ∈ 𝓝 x, ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ y ∈ V, ‖y‖ ≤ R ∧
    ∀ n : ℕ, N ≤ n → 2 ≤ (y + n).re ∧ ‖(2 : ℂ) ^ (y + n)‖⁻¹ ≤ 2 ^ R * (1 / 2) ^ n := by
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ‖x‖ + 1, by positivity,
    ⌈‖x‖ + 1⌉₊ + 2, fun y hy => ?_⟩
  have hy' : ‖y‖ ≤ ‖x‖ + 1 := by
    have := norm_le_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    exact this
  refine ⟨hy', fun n hn => ?_⟩
  have hre : -(‖x‖ + 1) ≤ y.re := by
    have := neg_abs_le y.re
    have := abs_re_le_norm y
    linarith
  have hc : (‖x‖ + 1 : ℝ) ≤ ⌈‖x‖ + 1⌉₊ := Nat.le_ceil _
  have hn' : ((⌈‖x‖ + 1⌉₊ + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  push_cast at hn'
  refine ⟨by simp; linarith, ?_⟩
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, norm_cpow_eq_rpow_re_of_pos (by norm_num),
    ← Real.rpow_neg (by norm_num)]
  rw [show (1 / 2 : ℝ) ^ n = (2 : ℝ) ^ (-(n : ℝ)) by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow],
    ← Real.rpow_add (by norm_num)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  simp
  linarith

/-- The terms of 25.8.3 are holomorphic on `ℂ ∖ {1, 0, -1, …}`. -/
lemma s25a_differentiableOn_T3 (k : ℕ) : DifferentiableOn ℂ (fun s : ℂ =>
    (ascPochhammer ℂ k).eval s * riemannZeta (s + k) / (k ! * 2 ^ (s + k))) s25a_U := by
  intro s hs
  have hs' := s25a_mem_U.mp hs
  have hz : s + k ≠ 1 := by
    intro h; exact hs' k (by linear_combination h)
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.div ((Polynomial.differentiable _).differentiableAt.mul
    ((differentiableAt_riemannZeta hz).comp s (differentiableAt_id.add_const _))) ?_ ?_
  · exact (differentiableAt_const _).mul
      ((differentiableAt_id.add_const _).const_cpow (Or.inl two_ne_zero))
  · exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero k)
      (cpow_ne_zero_iff.mpr (Or.inl two_ne_zero))

/-- `∑_k (s)_k x^k/(k+1)! = ((1-x)^{1-s} - 1)/((s-1)x)` for `0 < ‖x‖ < 1`, `s ≠ 1`. -/
lemma s25a_hasSum_pochhammer_succ {s x : ℂ} (hs : s ≠ 1) (hx0 : x ≠ 0) (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ => (ascPochhammer ℂ k).eval s / (k + 1) ! * x ^ k)
      ((1 / (1 - x) ^ (s - 1) - 1) / ((s - 1) * x)) := by
  have h := (hasSum_nat_add_iff' 1).mpr (s25a_hasSum_pochhammer (s - 1) hx)
  simp only [range_one, sum_singleton, ascPochhammer_zero, Polynomial.eval_one,
    Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one] at h
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have h' := h.div_const ((s - 1) * x)
  convert h' using 1
  funext k
  rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, sub_add_cancel]
  have hf : ((k + 1) ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  ring

/-- DLMF 25.8.2 core, for `Re s > 1`: `∑_k (s)_k/(k+1)! (ζ(s+k) - 1) = 1/(s-1)`. -/
lemma s25a_hasSum_822_re {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => (ascPochhammer ℂ k).eval s / (k + 1) ! * (riemannZeta (s + k) - 1))
      (1 / (s - 1)) := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  set c : ℕ → ℝ := fun m => (m : ℝ) + 2 with hc
  have hc0 : ∀ m, 0 < c m := fun m => by positivity
  have hc2 : ∀ m, 2 ≤ c m := fun m => by
    simp only [hc]; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  set f : ℕ × ℕ → ℂ := fun p => ((c p.2 : ℝ) : ℂ) ^ (-s) *
    ((ascPochhammer ℂ p.1).eval s / (p.1 + 1) ! * (1 / ((c p.2 : ℝ) : ℂ)) ^ p.1) with hf
  have hx : ∀ m, ‖1 / ((c m : ℝ) : ℂ)‖ ≤ 1 / 2 := by
    intro m
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hc0 m)]
    exact one_div_le_one_div_of_le (by norm_num) (hc2 m)
  have hsum : Summable f := by
    have hg : Summable fun m : ℕ => (c m) ^ (-s.re) := by
      have := (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow.mpr (show -s.re < -1 by
        linarith))
      refine this.congr fun m => ?_
      simp only [hc]; push_cast; ring_nf
    have hh := s25a_summable_pochhammer_real ‖s‖ (x := 1 / 2) (by norm_num) (by norm_num)
    refine Summable.of_norm_bounded (hh.mul_of_nonneg hg
      (fun k => by have := s25a_pochhammer_nonneg (norm_nonneg s) k; positivity)
      (fun m => by have := hc0 m; positivity)) fun p => ?_
    simp only [hf, norm_mul, norm_pow]
    rw [norm_div ((ascPochhammer ℂ p.1).eval s), Complex.norm_natCast,
      norm_cpow_eq_rpow_re_of_pos (hc0 p.2), neg_re]
    have h1 := s25a_norm_pochhammer_le s p.1
    have h2 : ‖1 / ((c p.2 : ℝ) : ℂ)‖ ^ p.1 ≤ (1 / 2) ^ p.1 :=
      pow_le_pow_left₀ (norm_nonneg _) (hx p.2) _
    have h3 : 0 ≤ (c p.2) ^ (-s.re) := (Real.rpow_pos_of_pos (hc0 p.2) _).le
    have h4 : (0 : ℝ) < p.1 ! := by exact_mod_cast Nat.factorial_pos _
    have h4' : (p.1 ! : ℝ) ≤ (p.1 + 1) ! := by exact_mod_cast Nat.factorial_le (by omega)
    have h5 : 0 ≤ (ascPochhammer ℝ p.1).eval ‖s‖ := s25a_pochhammer_nonneg (norm_nonneg s) _
    have h6 : ‖(ascPochhammer ℂ p.1).eval s‖ / ((p.1 + 1) ! : ℝ) ≤
        (ascPochhammer ℝ p.1).eval ‖s‖ / p.1 ! :=
      div_le_div₀ h5 h1 h4 h4'
    calc (c p.2) ^ (-s.re) * (‖(ascPochhammer ℂ p.1).eval s‖ / ((p.1 + 1) ! : ℝ) *
          ‖1 / ((c p.2 : ℝ) : ℂ)‖ ^ p.1)
        ≤ (c p.2) ^ (-s.re) * ((ascPochhammer ℝ p.1).eval ‖s‖ / p.1 ! * (1 / 2) ^ p.1) := by
          gcongr
      _ = (ascPochhammer ℝ p.1).eval ‖s‖ / p.1 ! * (1 / 2) ^ p.1 * (c p.2) ^ (-s.re) := by ring
  have hk : ∀ k : ℕ, HasSum (fun m : ℕ => f (k, m))
      ((ascPochhammer ℂ k).eval s / (k + 1) ! * (riemannZeta (s + k) - 1)) := by
    intro k
    have hre : 1 < (s + k).re := by simp; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    have h0 := (hasSum_nat_add_iff' 1).mpr (s25a_hasSum_zeta hre)
    simp only [range_one, sum_singleton, Nat.cast_zero, zero_add, one_cpow, div_one] at h0
    have h := h0.mul_left ((ascPochhammer ℂ k).eval s / (k + 1) !)
    convert h using 1
    funext m
    simp only [hf]
    have hC : ((c m : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hc0 m).ne'
    have e1 : (1 / ((c m : ℝ) : ℂ)) ^ k = ((c m : ℝ) : ℂ) ^ (-(k : ℂ)) := by
      rw [cpow_neg, cpow_natCast, one_div, inv_pow]
    have e2 : ((c m : ℝ) : ℂ) = ((m + 1 : ℕ) : ℂ) + 1 := by simp only [hc]; push_cast; ring
    rw [e1, mul_left_comm, ← cpow_add _ _ hC, show -s + -(k : ℂ) = -(s + k) by ring, e2,
      cpow_neg, one_div]
  have hm : ∀ m : ℕ, HasSum (fun k : ℕ => f (k, m))
      ((1 / ((m : ℂ) + 1) ^ (s - 1) - 1 / ((m : ℂ) + 2) ^ (s - 1)) / (s - 1)) := by
    intro m
    have hC : ((c m : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hc0 m).ne'
    have h := (s25a_hasSum_pochhammer_succ hs1 (one_div_ne_zero hC)
      ((hx m).trans_lt (by norm_num))).mul_left (((c m : ℝ) : ℂ) ^ (-s))
    convert h using 1
    have hc1 : (0 : ℝ) ≤ 1 - 1 / c m := by
      have := hc2 m
      rw [sub_nonneg, div_le_one (hc0 m)]; linarith
    have e : (1 : ℂ) - 1 / ((c m : ℝ) : ℂ) = ((1 - 1 / c m : ℝ) : ℂ) := by push_cast; ring
    have e3 : ((c m : ℝ) : ℂ) * ((1 - 1 / c m : ℝ) : ℂ) = (m : ℂ) + 1 := by
      simp only [hc]; push_cast
      have : (m : ℂ) + 2 ≠ 0 := by
        rw [show (m : ℂ) + 2 = ((m + 2 : ℕ) : ℂ) by push_cast; ring]
        exact_mod_cast (show m + 2 ≠ 0 by omega)
      field_simp; ring
    have e4 : ((c m : ℝ) : ℂ) = (m : ℂ) + 2 := by simp only [hc]; push_cast; ring
    have hcs : ((c m : ℝ) : ℂ) ^ (-s) = 1 / ((c m : ℝ) : ℂ) ^ (s - 1) / ((c m : ℝ) : ℂ) := by
      rw [cpow_sub _ _ hC, cpow_one, cpow_neg]; field_simp
    have hA : ((c m : ℝ) : ℂ) ^ (s - 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hC)
    have hB0 : ((1 - 1 / c m : ℝ) : ℂ) ≠ 0 := by
      intro h0
      have : ((c m : ℝ) : ℂ) * ((1 - 1 / c m : ℝ) : ℂ) = 0 := by rw [h0, mul_zero]
      rw [e3] at this
      have h1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
      push_cast at h1
      exact h1 this
    have hB : ((1 - 1 / c m : ℝ) : ℂ) ^ (s - 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hB0)
    have hAB : ((m : ℂ) + 1) ^ (s - 1) =
        ((c m : ℝ) : ℂ) ^ (s - 1) * ((1 - 1 / c m : ℝ) : ℂ) ^ (s - 1) := by
      rw [← e3, mul_cpow_ofReal_nonneg (hc0 m).le hc1]
    have hA2 : ((m : ℂ) + 2) ^ (s - 1) = ((c m : ℝ) : ℂ) ^ (s - 1) := by rw [e4]
    rw [e, hcs, hAB, hA2]
    field_simp
  have hA := hsum.hasSum.prod_fiberwise hk
  have hB := ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hsum.hasSum).prod_fiberwise hm
  set a : ℕ → ℂ := fun m => 1 / ((m : ℂ) + 1) ^ (s - 1) with ha
  have htel : ∀ N : ℕ, ∑ m ∈ range N,
      (1 / ((m : ℂ) + 1) ^ (s - 1) - 1 / ((m : ℂ) + 2) ^ (s - 1)) / (s - 1) =
      (a 0 - a N) / (s - 1) := by
    intro N
    rw [← sum_div, ← sum_range_sub' a N]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    simp only [ha]; push_cast; ring_nf
  have hlim : Tendsto (fun N : ℕ => (a 0 - a N) / (s - 1)) atTop (𝓝 (1 / (s - 1))) := by
    have h0 : a 0 = 1 := by simp [ha]
    have hN : Tendsto a atTop (𝓝 0) := by
      have h := (q25a_tendsto_cpow_atTop (z := 1 - s) (by simp; linarith)).comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
      refine h.congr fun N => ?_
      simp only [Function.comp_apply, ha]
      push_cast
      rw [show (1 : ℂ) - s = -(s - 1) by ring, cpow_neg, one_div]
    have := ((tendsto_const_nhds (x := a 0)).sub hN).div_const (s - 1)
    rw [h0, sub_zero] at this
    rw [h0]
    exact this
  have hval := tendsto_nhds_unique (hB.tendsto_sum_nat.congr htel) hlim
  rw [← hval]
  exact hA

/-- The terms of the 25.8.2 core series are holomorphic on `ℂ ∖ {1, 0, -1, …}`. -/
lemma s25a_differentiableOn_T2 (k : ℕ) : DifferentiableOn ℂ (fun s : ℂ =>
    (ascPochhammer ℂ k).eval s / (k + 1) ! * (riemannZeta (s + k) - 1)) s25a_U := by
  intro s hs
  have hs' := s25a_mem_U.mp hs
  have hz : s + k ≠ 1 := by
    intro h; exact hs' k (by linear_combination h)
  refine DifferentiableAt.differentiableWithinAt ?_
  exact ((Polynomial.differentiable _).differentiableAt.div_const _).mul
    (((differentiableAt_riemannZeta hz).comp s (differentiableAt_id.add_const _)).sub_const _)

/-- DLMF 25.8.2 core: `∑_k (s)_k/(k+1)! (ζ(s+k) - 1) = 1/(s-1)` on `ℂ ∖ {1, 0, -1, …}`. -/
lemma s25a_hasSum_822 {s : ℂ} (hs : s ∈ s25a_U) :
    HasSum (fun k : ℕ => (ascPochhammer ℂ k).eval s / (k + 1) ! * (riemannZeta (s + k) - 1))
      (1 / (s - 1)) := by
  obtain ⟨C, hC0, hC⟩ := s25a_norm_zeta_sub_one_le
  refine s25a_continuation (fun k s => (ascPochhammer ℂ k).eval s / (k + 1) ! *
      (riemannZeta (s + k) - 1)) (fun s => 1 / (s - 1)) s25a_differentiableOn_T2 ?_ ?_
    (fun s hs => s25a_hasSum_822_re hs) s hs
  · intro z hz
    have hz1 : z - 1 ≠ 0 := by
      have := s25a_mem_U.mp hz 0; exact sub_ne_zero.mpr (by simpa using this)
    have hd : DifferentiableAt ℂ (fun s : ℂ => 1 / (s - 1)) z :=
      (differentiableAt_const _).div (differentiableAt_id.sub_const _) hz1
    exact hd.differentiableWithinAt
  · intro x _
    obtain ⟨V, hV, R, hR, N, hloc⟩ := s25a_local x
    refine ⟨V, hV, N, fun n => (ascPochhammer ℝ n).eval R / n ! * (1 / 2) ^ n * (4 * 2 ^ R * C),
      (s25a_summable_pochhammer_real R (by norm_num) (by norm_num)).mul_right _, ?_⟩
    intro n hn y hy
    obtain ⟨hyR, hy2⟩ := hloc y hy
    obtain ⟨hre, h2⟩ := hy2 n hn
    have hP : ‖(ascPochhammer ℂ n).eval y‖ ≤ (ascPochhammer ℝ n).eval R :=
      (s25a_norm_pochhammer_le y n).trans (s25a_pochhammer_mono (norm_nonneg y) hyR n)
    have h4 : (2 : ℝ) ^ (2 - (y + n).re) = 4 * ‖(2 : ℂ) ^ (y + n)‖⁻¹ := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, norm_cpow_eq_rpow_re_of_pos (by norm_num),
        Real.rpow_sub (by norm_num), Real.rpow_two]
      ring
    have hZ : ‖riemannZeta (y + n) - 1‖ ≤ 4 * 2 ^ R * (1 / 2) ^ n * C := by
      have h := hC (y + n) hre
      rw [h4] at h
      calc _ ≤ 4 * ‖(2 : ℂ) ^ (y + n)‖⁻¹ * C := h
        _ ≤ 4 * (2 ^ R * (1 / 2) ^ n) * C := by gcongr
        _ = _ := by ring
    have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    have hf' : (n ! : ℝ) ≤ (n + 1) ! := by exact_mod_cast Nat.factorial_le (by omega)
    have hPn : 0 ≤ (ascPochhammer ℝ n).eval R := s25a_pochhammer_nonneg hR n
    rw [norm_mul, norm_div, Complex.norm_natCast]
    calc ‖(ascPochhammer ℂ n).eval y‖ / ((n + 1) ! : ℝ) * ‖riemannZeta (y + n) - 1‖
        ≤ (ascPochhammer ℝ n).eval R / n ! * (4 * 2 ^ R * (1 / 2) ^ n * C) := by
          gcongr
      _ = _ := by ring

/-- DLMF 25.8.2: `∑_{k≥0} Γ(s+k)/(k+1)! (ζ(s+k) - 1) = Γ(s-1)` for `s ≠ 1, 0, -1, -2, …`. -/
@[dlmf 25.8.E2]
theorem hasSum_Gamma_mul_riemannZeta_sub_one {s : ℂ} (hs : ∀ n : ℕ, s ≠ 1 - n) :
    HasSum (fun k : ℕ => Gamma (s + k) / (k + 1)! * (riemannZeta (s + k) - 1))
      (Gamma (s - 1)) := by
  have hU : s ∈ s25a_U := s25a_mem_U.mpr hs
  have hpole : ∀ m : ℕ, s ≠ -m := by
    intro m h; exact hs (m + 1) (by rw [h]; push_cast; ring)
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (by simpa using hs 0)
  have h := (s25a_hasSum_822 hU).mul_left (Gamma s)
  have hG : Gamma s = (s - 1) * Gamma (s - 1) := by
    rw [← Complex.Gamma_add_one _ hs1, sub_add_cancel]
  convert h using 1
  · funext k
    rw [← Complex.Gamma_add_nat_div_Gamma_eq s hpole]
    have hG0 : Gamma s ≠ 0 := Complex.Gamma_ne_zero hpole
    field_simp
  · rw [hG]; field_simp

/-- DLMF 25.8.3: `∑_{k≥0} (s)_k ζ(s+k)/(k! 2^{s+k}) = (1 - 2^{-s}) ζ(s)` for `s ≠ 1`; the Lean
statement also excludes `s = 0, -1, -2, …` (see the module docstring). -/
@[dlmf 25.8.E3]
theorem hasSum_pochhammer_mul_riemannZeta {s : ℂ} (hs1 : s ≠ 1) (hs : ∀ n : ℕ, s ≠ -n) :
    HasSum (fun k : ℕ => (ascPochhammer ℂ k).eval s * riemannZeta (s + k) /
        (k ! * 2 ^ (s + k))) ((1 - 2 ^ (-s)) * riemannZeta s) := by
  obtain ⟨C, hC0, hC⟩ := s25a_norm_zeta_sub_one_le
  have hU : s ∈ s25a_U := by
    rw [s25a_mem_U]
    intro n
    rcases n with _ | m
    · simpa using hs1
    · have := hs m; push_cast; intro h; exact this (by linear_combination h)
  refine s25a_continuation (fun k s => (ascPochhammer ℂ k).eval s * riemannZeta (s + k) /
      (k ! * 2 ^ (s + k))) (fun s => (1 - 2 ^ (-s)) * riemannZeta s) s25a_differentiableOn_T3 ?_ ?_
    (fun s hs => s25a_hasSum_838_re hs) s hU
  · intro z hz
    have hz1 : z ≠ 1 := by have := s25a_mem_U.mp hz 0; simpa using this
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((differentiableAt_const _).sub (differentiableAt_id.neg.const_cpow
      (Or.inl two_ne_zero))).mul (differentiableAt_riemannZeta hz1)
  · intro x _
    obtain ⟨V, hV, R, hR, N, hloc⟩ := s25a_local x
    refine ⟨V, hV, N, fun n => (ascPochhammer ℝ n).eval R / n ! * (1 / 2) ^ n * ((1 + C) * 2 ^ R),
      (s25a_summable_pochhammer_real R (by norm_num) (by norm_num)).mul_right _, ?_⟩
    intro n hn y hy
    obtain ⟨hyR, hy2⟩ := hloc y hy
    obtain ⟨hre, h2⟩ := hy2 n hn
    have hP : ‖(ascPochhammer ℂ n).eval y‖ ≤ (ascPochhammer ℝ n).eval R :=
      (s25a_norm_pochhammer_le y n).trans (s25a_pochhammer_mono (norm_nonneg y) hyR n)
    have hZ : ‖riemannZeta (y + n)‖ ≤ 1 + C := by
      have h := hC (y + n) hre
      have h' : (2 : ℝ) ^ (2 - (y + n).re) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
      calc ‖riemannZeta (y + n)‖ = ‖(riemannZeta (y + n) - 1) + 1‖ := by ring_nf
        _ ≤ ‖riemannZeta (y + n) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖riemannZeta (y + n) - 1‖ + 1 := by rw [norm_one]
        _ ≤ (2 : ℝ) ^ (2 - (y + n).re) * C + 1 := by linarith
        _ ≤ 1 * C + 1 := by gcongr
        _ = 1 + C := by ring
    have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    rw [norm_div, norm_mul, norm_mul, Complex.norm_natCast, div_eq_mul_inv, mul_inv]
    have hPn : 0 ≤ (ascPochhammer ℝ n).eval R := s25a_pochhammer_nonneg hR n
    calc ‖(ascPochhammer ℂ n).eval y‖ * ‖riemannZeta (y + n)‖ * ((n ! : ℝ)⁻¹ *
          ‖(2 : ℂ) ^ (y + n)‖⁻¹)
        ≤ (ascPochhammer ℝ n).eval R * (1 + C) * ((n ! : ℝ)⁻¹ * (2 ^ R * (1 / 2) ^ n)) := by
          gcongr
      _ = _ := by ring

/-- `∑_{n≥0} 1/(n+1)^N = ζ(N)` for `N ≥ 2`. -/
lemma s25a_hasSum_zeta_nat {N : ℕ} (hN : 2 ≤ N) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ N) (riemannZeta N) := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ N) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) ?_ fun n => ?_
    · have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
      simpa using this
    · rw [norm_div, norm_one, norm_pow, show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring,
        Complex.norm_natCast]
      push_cast
      gcongr
      · linarith
  convert hs.hasSum using 1
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp; exact_mod_cast (by omega : 1 < N))]
  congr 1; funext n; rw [cpow_natCast]

open Polynomial in
/-- `∏_{j<n} (x - e^{(2j+1)πi/n}) = xⁿ + 1`. -/
lemma s25a_prod_sub_roots {n : ℕ} (hn : 0 < n) (x : ℂ) :
    ∏ j ∈ range n, (x - cexp ((2 * j + 1) * π * I / n)) = x ^ n + 1 := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  have hα : cexp (π * I / n) ^ n = -1 := by
    rw [← Complex.exp_nat_mul, show (n : ℂ) * (π * I / n) = π * I by field_simp,
      Complex.exp_pi_mul_I]
  have h := congrArg (Polynomial.eval x) (X_pow_sub_C_eq_prod hζ hn hα)
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_prod] at h
  rw [sub_neg_eq_add] at h
  rw [h]
  refine prod_congr rfl fun j _ => ?_
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 2
  field_simp

/-- `∑_{j<n} e^{(2j+1)πi/n} = 0` for `n ≥ 2`. -/
lemma s25a_sum_roots {n : ℕ} (hn : 2 ≤ n) :
    ∑ j ∈ range n, cexp ((2 * j + 1) * π * I / n) = 0 := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hζ := Complex.isPrimitiveRoot_exp n (by omega)
  have h := hζ.geom_sum_eq_zero (by omega)
  have : ∀ j ∈ range n, cexp ((2 * j + 1) * π * I / n) =
      cexp (2 * π * I / n) ^ j * cexp (π * I / n) := by
    intro j _
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    field_simp
  rw [sum_congr rfl this, ← sum_mul, h, zero_mul]

/-- `∏_{j<n} x^{a_j} = x^{∑ a_j}` for `x ≠ 0`. -/
lemma s25a_prod_cpow {x : ℂ} (hx : x ≠ 0) (a : ℕ → ℂ) (n : ℕ) :
    ∏ j ∈ range n, x ^ a j = x ^ (∑ j ∈ range n, a j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [prod_range_succ, sum_range_succ, ih, cpow_add _ _ hx]

/-- The product of the Gamma sequences at `2 - e^{(2j+1)πi/n}`. -/
lemma s25a_prod_GammaSeq {n : ℕ} (hn : 2 ≤ n) {N : ℕ} (hN : 1 ≤ N) :
    ∏ j ∈ range n, GammaSeq (2 - cexp ((2 * j + 1) * π * I / n)) N =
      (N : ℂ) ^ (2 * n) * (N ! : ℂ) ^ n / ∏ k ∈ range (N + 1), (((k : ℂ) + 2) ^ n + 1) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp only [GammaSeq]
  rw [prod_div_distrib, prod_mul_distrib, s25a_prod_cpow hN0, sum_sub_distrib, s25a_sum_roots hn,
    prod_const, card_range, Finset.prod_comm]
  congr 1
  · congr 1
    rw [sub_zero, sum_const, card_range, nsmul_eq_mul, show (n : ℂ) * 2 = ((2 * n : ℕ) : ℂ) by
      push_cast; ring, cpow_natCast]
  · refine prod_congr rfl fun k _ => ?_
    rw [← s25a_prod_sub_roots (by omega)]
    refine prod_congr rfl fun j _ => ?_
    ring

/-- The double series behind DLMF 25.8.4. -/
lemma s25a_hasSum_log_prod {n : ℕ} (hn : 2 ≤ n) :
    ∃ T : ℂ, HasSum (fun k : ℕ => (-1) ^ (k + 1) / (k + 1) * (riemannZeta (n * (k + 1)) - 1)) T ∧
      HasSum (fun m : ℕ => -log (1 + 1 / ((m : ℂ) + 2) ^ n)) T := by
  set f : ℕ × ℕ → ℂ := fun p => (-1) ^ (p.1 + 1) / (p.1 + 1) * (1 / ((p.2 : ℂ) + 2) ^ n) ^ (p.1 + 1)
    with hf
  have hu : ∀ m : ℕ, ‖1 / ((m : ℂ) + 2) ^ n‖ = 1 / ((m : ℝ) + 2) ^ n := by
    intro m
    rw [norm_div, norm_one, norm_pow, show ((m : ℂ) + 2) = ((m + 2 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast]
    push_cast; ring
  have hu2 : ∀ m : ℕ, 1 / ((m : ℝ) + 2) ^ n ≤ 1 / ((m : ℝ) + 2) ^ 2 := by
    intro m
    gcongr
    · linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hq : ∀ m : ℕ, 1 / ((m : ℝ) + 2) ^ 2 ≤ 1 / 4 := by
    intro m
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hsum : Summable f := by
    have hg : Summable fun k : ℕ => (1 / 4 : ℝ) ^ k :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hh : Summable fun m : ℕ => 1 / ((m : ℝ) + 2) ^ 2 := by
      have := (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
      simpa using this
    refine Summable.of_norm_bounded (hg.mul_of_nonneg hh (fun k => by positivity)
      (fun m => by positivity)) fun p => ?_
    have hk : (1 : ℝ) ≤ ‖((p.1 : ℂ) + 1)‖ := by
      rw [show ((p.1 : ℂ) + 1) = ((p.1 + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      exact_mod_cast (by omega : 1 ≤ p.1 + 1)
    simp only [hf, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, hu]
    set u : ℝ := 1 / ((p.2 : ℝ) + 2) ^ n
    set v : ℝ := 1 / ((p.2 : ℝ) + 2) ^ 2
    have hu0 : 0 ≤ u := by positivity
    have huv : u ≤ v := hu2 p.2
    have hv : v ≤ 1 / 4 := hq p.2
    calc 1 / ‖(p.1 : ℂ) + 1‖ * u ^ (p.1 + 1) ≤ 1 * u ^ (p.1 + 1) := by
          gcongr; exact div_le_one_of_le₀ hk (norm_nonneg _)
      _ = u * u ^ p.1 := by ring
      _ ≤ v * (1 / 4) ^ p.1 := by gcongr; linarith
      _ = (1 / 4) ^ p.1 * v := by ring
  have hk : ∀ k : ℕ, HasSum (fun m : ℕ => f (k, m))
      ((-1) ^ (k + 1) / (k + 1) * (riemannZeta (n * (k + 1)) - 1)) := by
    intro k
    have h0 := s25a_hasSum_zeta_nat (N := n * (k + 1)) (by nlinarith)
    have h1 := ((hasSum_nat_add_iff' 1).mpr h0).mul_left ((-1 : ℂ) ^ (k + 1) / ((k : ℂ) + 1))
    simp only [range_one, sum_singleton, Nat.cast_zero, zero_add, one_pow, div_one] at h1
    push_cast at h1
    convert h1 using 1
    funext m
    simp only [hf]
    rw [div_pow, one_pow, ← pow_mul, show (m : ℂ) + 1 + 1 = m + 2 by ring]
  have hm : ∀ m : ℕ, HasSum (fun k : ℕ => f (k, m)) (-log (1 + 1 / ((m : ℂ) + 2) ^ n)) := by
    intro m
    have hn1 : ‖-(1 / ((m : ℂ) + 2) ^ n)‖ < 1 := by
      rw [norm_neg, hu]
      exact (hu2 m).trans_lt ((hq m).trans_lt (by norm_num))
    have h := Complex.hasSum_taylorSeries_neg_log' hn1
    rw [sub_neg_eq_add] at h
    convert h using 1
    funext k
    simp only [hf]
    rw [neg_pow, mul_comm ((-1 : ℂ) ^ (k + 1)), div_eq_mul_inv, div_eq_mul_inv]
    ring
  refine ⟨_, hsum.hasSum.prod_fiberwise hk, ?_⟩
  have hswap : HasSum (f ∘ Prod.swap) (∑' p, f p) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hsum.hasSum
  exact hswap.prod_fiberwise fun m => hm m

/-- `∏_{k≤N} (k+2) = (N+2)!`. -/
lemma s25a_prod_add_two (N : ℕ) : ∏ k ∈ range (N + 1), ((k : ℝ) + 2) = ((N + 2) ! : ℝ) := by
  induction N with
  | zero => simp [Nat.factorial]
  | succ N ih =>
    rw [prod_range_succ, ih]
    show _ = (((N + 2) + 1) ! : ℝ)
    rw [Nat.factorial_succ (N + 2)]
    push_cast; ring

/-- The Gamma-sequence product in terms of the partial products of `1 + (m+2)^{-n}`. -/
lemma s25a_GammaSeq_real (n : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (2 * n) * (N ! : ℝ) ^ n / ∏ k ∈ range (N + 1), (((k : ℝ) + 2) ^ n + 1) =
      ((N : ℝ) / (N + 1) * (N / (N + 2))) ^ n /
        ∏ k ∈ range (N + 1), (1 + 1 / ((k : ℝ) + 2) ^ n) := by
  have hprod : ∏ k ∈ range (N + 1), (((k : ℝ) + 2) ^ n + 1) =
      (∏ k ∈ range (N + 1), (1 + 1 / ((k : ℝ) + 2) ^ n)) * ((N + 2) ! : ℝ) ^ n := by
    rw [← s25a_prod_add_two, ← prod_pow, ← prod_mul_distrib]
    refine prod_congr rfl fun k _ => ?_
    have : ((k : ℝ) + 2) ^ n ≠ 0 := by positivity
    field_simp
  have hQ : 0 < ∏ k ∈ range (N + 1), (1 + 1 / ((k : ℝ) + 2) ^ n) :=
    prod_pos fun k _ => by positivity
  have hfac : ((N + 2) ! : ℝ) = ((N : ℝ) + 2) * ((N : ℝ) + 1) * (N ! : ℝ) := by
    show (((N + 1) + 1) ! : ℝ) = _
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [hprod, hfac]
  have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
  have h3 : ((N ! : ℕ) : ℝ) ≠ 0 := by positivity
  calc (N : ℝ) ^ (2 * n) * (N ! : ℝ) ^ n /
        ((∏ k ∈ range (N + 1), (1 + 1 / ((k : ℝ) + 2) ^ n)) *
          (((N : ℝ) + 2) * ((N : ℝ) + 1) * (N ! : ℝ)) ^ n)
      = ((N : ℝ) ^ 2 * (N ! : ℝ) / (((N : ℝ) + 2) * ((N : ℝ) + 1) * (N ! : ℝ))) ^ n /
          ∏ k ∈ range (N + 1), (1 + 1 / ((k : ℝ) + 2) ^ n) := by
        rw [div_pow, mul_pow, pow_mul]; ring
    _ = _ := by
        congr 2
        field_simp

/-- DLMF 25.8.4: for `n ≥ 2`,
`∑_{k≥1} ((-1)^k/k) (ζ(nk) - 1) = ln ∏_{j=0}^{n-1} Γ(2 - e^{(2j+1)πi/n})` (the product is a
positive real number). -/
@[dlmf 25.8.E4]
theorem hasSum_neg_one_pow_riemannZeta_mul_sub_one {n : ℕ} (hn : 2 ≤ n) :
    HasSum (fun k : ℕ => (-1) ^ (k + 1) / (k + 1) * (riemannZeta (n * (k + 1)) - 1))
      (log (∏ j ∈ range n, Gamma (2 - cexp ((2 * j + 1) * π * I / n)))) := by
  obtain ⟨T, h1, h2⟩ := s25a_hasSum_log_prod hn
  set a : ℕ → ℝ := fun m => 1 + 1 / ((m : ℝ) + 2) ^ n with ha_def
  have ha : ∀ m, 0 < a m := fun m => by positivity
  have hterm : ∀ m : ℕ, -log (1 + 1 / ((m : ℂ) + 2) ^ n) = ((-Real.log (a m) : ℝ) : ℂ) := by
    intro m
    rw [ofReal_neg, ofReal_log (ha m).le, ha_def]
    push_cast; rfl
  simp_rw [hterm] at h2
  have hre : HasSum (fun m => -Real.log (a m)) T.re := by
    simpa using Complex.hasSum_re h2
  have hT : T = (T.re : ℂ) := ((Complex.ofRealCLM.hasSum hre).unique h2).symm
  have hlog : HasSum (fun m => Real.log (a m)) (-T.re) := by simpa using hre.neg
  have hQ : Tendsto (fun N : ℕ => ∏ k ∈ range (N + 1), a k) atTop (𝓝 (Real.exp (-T.re))) := by
    have := (Real.continuous_exp.tendsto _).comp
      (hlog.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
    refine this.congr fun N => ?_
    simp only [Function.comp_apply]
    rw [Real.exp_sum]
    exact prod_congr rfl fun k _ => Real.exp_log (ha k)
  have hr : Tendsto (fun N : ℕ => ((N : ℝ) / (N + 1) * (N / (N + 2))) ^ n) atTop (𝓝 1) := by
    have h1' := tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1
    have h2' := tendsto_natCast_div_add_atTop (𝕜 := ℝ) 2
    simpa using (h1'.mul h2').pow n
  have hlim : Tendsto (fun N : ℕ => ∏ j ∈ range n, GammaSeq (2 - cexp ((2 * j + 1) * π * I / n)) N)
      atTop (𝓝 (((Real.exp (-T.re))⁻¹ : ℝ) : ℂ)) := by
    have := (continuous_ofReal.tendsto _).comp (hr.div hQ (Real.exp_pos _).ne')
    rw [one_div] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Function.comp_apply, Pi.div_apply, ha_def]
    rw [s25a_prod_GammaSeq hn hN, ← s25a_GammaSeq_real n hN]
    push_cast; rfl
  have hG := tendsto_finsetProd (range n)
    (fun j _ => GammaSeq_tendsto_Gamma (2 - cexp ((2 * j + 1) * π * I / n)))
  rw [tendsto_nhds_unique hG hlim, ← Real.exp_neg, neg_neg, ← ofReal_log (Real.exp_pos _).le,
    Real.log_exp, ← hT]
  exact h1

/-- DLMF 25.8.5: `∑_{k≥2} ζ(k) z^k = -γz - zψ(1-z)` for `|z| < 1`. Proved from the Taylor
series of `ψ(1+z)` (DLMF 5.7.4). -/
@[dlmf 25.8.E5]
theorem hasSum_riemannZeta_mul_pow {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => riemannZeta (k + 2) * z ^ (k + 2))
      (-Real.eulerMascheroniConstant * z - z * digamma (1 - z)) := by
  have hz' : ‖-z‖ < 1 := by rwa [norm_neg]
  have h := (DLMF.Gamma.hasSum_digamma_one_add_zeta hz').mul_left (-z)
  rw [show (1 : ℂ) + -z = 1 - z by ring] at h
  convert h using 1
  · funext k
    have h1 : ((-1 : ℂ)) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    rw [neg_pow]
    simp only [pow_succ]
    linear_combination (riemannZeta (k + 2) * z ^ k * z * z) * (-h1)
  · ring

/-- DLMF 25.8.6: `∑_{k≥0} ζ(2k) z^{2k} = -½ πz cot(πz)` for `0 < |z| < 1` (at `z = 0` the right
side is a removable singularity with value `ζ(0) = -½`). Proved from the cotangent series. -/
@[dlmf 25.8.E6]
theorem hasSum_riemannZeta_two_mul_mul_pow {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasSum (fun k : ℕ => riemannZeta (2 * k) * z ^ (2 * k)) (-(1 / 2) * π * z * cot (π * z)) := by
  have h := (_root_.Complex.hasSum_pi_mul_cot_zeta hz hz0).mul_left (-(1 / 2) : ℂ)
  refine (hasSum_nat_add_iff' 1).mp ?_
  simp only [range_one, sum_singleton, Nat.cast_zero, mul_zero, pow_zero, mul_one,
    riemannZeta_zero]
  convert h using 1
  · funext k
    push_cast
    ring
  · ring

/-- DLMF 25.8.7: `∑_{k≥2} (ζ(k)/k) z^k = -γz + ln Γ(1-z)` for `|z| < 1`, with the principal
logarithm. -/
@[dlmf 25.8.E7]
theorem hasSum_riemannZeta_div_mul_pow {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => riemannZeta (k + 2) / (k + 2) * z ^ (k + 2))
      (-Real.eulerMascheroniConstant * z + log (Gamma (1 - z))) := by
  have hz' : ‖-z‖ < 1 := by rwa [norm_neg]
  set A : ℕ → ℂ := fun k => (riemannZeta (k + 2) - 1) * z ^ (k + 2) / (k + 2) with hA
  have hAs : Summable A := by
    refine Summable.of_norm_bounded (g := fun k : ℕ => (1 / 2 : ℝ) ^ k)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)) fun k => ?_
    have hk : (1 : ℝ) ≤ ‖((k : ℂ) + 2)‖ := by
      rw [show ((k : ℂ) + 2) = ((k + 2 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      exact_mod_cast (by omega : 1 ≤ k + 2)
    have hzk : ‖z ^ (k + 2)‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz.le
    simp only [hA, norm_div, norm_mul]
    calc ‖riemannZeta (k + 2) - 1‖ * ‖z ^ (k + 2)‖ / ‖(k : ℂ) + 2‖
        ≤ ‖riemannZeta (k + 2) - 1‖ * ‖z ^ (k + 2)‖ := div_le_self (by positivity) hk
      _ ≤ (1 / 2 : ℝ) ^ k * 1 := by
          gcongr
          · exact DLMF.Gamma.norm_riemannZeta_add_two_sub_one_le k
      _ = _ := mul_one _
  have hlog := DLMF.Gamma.log_Gamma_one_add hz'
  have hterm : ∀ k : ℕ, (-1 : ℂ) ^ (k + 2) * (riemannZeta (k + 2) - 1) * (-z) ^ (k + 2) / (k + 2) =
      A k := by
    intro k
    simp only [hA]
    have h1 : ((-1 : ℂ)) ^ (k + 2) * (-1) ^ (k + 2) = 1 := by rw [← mul_pow]; norm_num
    rw [neg_pow z]
    linear_combination ((riemannZeta (k + 2) - 1) * z ^ (k + 2) / (k + 2)) * h1
  simp_rw [hterm, show (1 : ℂ) + -z = 1 - z by ring] at hlog
  have hB : HasSum (fun k : ℕ => z ^ (k + 2) / (k + 2)) (-log (1 - z) - z) := by
    have h := (hasSum_nat_add_iff' 2).mpr (Complex.hasSum_taylorSeries_neg_log hz)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.cast_zero, div_zero,
      zero_add, pow_one, Nat.cast_one, div_one] at h
    convert h using 2 with k
    push_cast; ring
  convert hAs.hasSum.add hB using 1
  · funext k
    simp only [hA]
    have hk : ((k : ℂ) + 2) ≠ 0 := by
      rw [show ((k : ℂ) + 2) = ((k + 2 : ℕ) : ℂ) by push_cast; ring]
      exact_mod_cast (by omega : k + 2 ≠ 0)
    field_simp
    ring
  · have : ∑' k, A k =
        log (Gamma (1 - z)) + log (1 - z) - -z * (1 - Real.eulerMascheroniConstant) := by
      rw [hlog]; ring
    rw [this]; ring

/-- The double series behind DLMF 25.8.8. -/
lemma s25a_hasSum_neg_log_prod {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ F : ℂ, HasSum (fun k : ℕ => riemannZeta (2 * (k + 1)) / (k + 1) * z ^ (2 * (k + 1))) F ∧
      HasSum (fun m : ℕ => -log (1 - z ^ 2 / ((m : ℂ) + 1) ^ 2)) F := by
  set f : ℕ × ℕ → ℂ := fun p => (z ^ 2 / ((p.2 : ℂ) + 1) ^ 2) ^ (p.1 + 1) / (p.1 + 1) with hf
  have hw : ∀ m : ℕ, ‖z ^ 2 / ((m : ℂ) + 1) ^ 2‖ = ‖z‖ ^ 2 / ((m : ℝ) + 1) ^ 2 := by
    intro m
    rw [norm_div, norm_pow, norm_pow, show ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast]
    push_cast; ring
  have hw1 : ∀ m : ℕ, ‖z ^ 2 / ((m : ℂ) + 1) ^ 2‖ < 1 := by
    intro m
    rw [hw, div_lt_one (by positivity)]
    have : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
    nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hsum : Summable f := by
    have hz2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
    have hg : Summable fun k : ℕ => (‖z‖ ^ 2) ^ (k + 1) :=
      ((summable_geometric_of_lt_one (by positivity) hz2).mul_left (‖z‖ ^ 2)).congr
        fun k => by ring
    have hh : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2 := by
      have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
      simpa using this
    refine Summable.of_norm_bounded (hg.mul_of_nonneg hh (fun k => by positivity)
      (fun m => by positivity)) fun p => ?_
    have hk : (1 : ℝ) ≤ ‖((p.1 : ℂ) + 1)‖ := by
      rw [show ((p.1 : ℂ) + 1) = ((p.1 + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      exact_mod_cast (by omega : 1 ≤ p.1 + 1)
    have hm : (1 : ℝ) ≤ ((p.2 : ℝ) + 1) ^ 2 := by
      have : (1 : ℝ) ≤ (p.2 : ℝ) + 1 := by linarith [(p.2.cast_nonneg : (0 : ℝ) ≤ p.2)]
      nlinarith
    simp only [hf, norm_div, norm_pow, hw]
    calc (‖z‖ ^ 2 / ((p.2 : ℝ) + 1) ^ 2) ^ (p.1 + 1) / ‖(p.1 : ℂ) + 1‖
        ≤ (‖z‖ ^ 2 / ((p.2 : ℝ) + 1) ^ 2) ^ (p.1 + 1) := div_le_self (by positivity) hk
      _ = (‖z‖ ^ 2) ^ (p.1 + 1) / (((p.2 : ℝ) + 1) ^ 2) ^ (p.1 + 1) := by rw [div_pow]
      _ ≤ (‖z‖ ^ 2) ^ (p.1 + 1) / ((p.2 : ℝ) + 1) ^ 2 := by
          gcongr
          exact le_self_pow₀ hm (by omega)
      _ = _ := by ring
  have hk : ∀ k : ℕ, HasSum (fun m : ℕ => f (k, m))
      (riemannZeta (2 * (k + 1)) / (k + 1) * z ^ (2 * (k + 1))) := by
    intro k
    have h := (s25a_hasSum_zeta_nat (N := 2 * (k + 1)) (by omega)).mul_left
      (z ^ (2 * (k + 1)) / (k + 1))
    push_cast at h
    convert h using 1
    · funext m
      simp only [hf]
      rw [div_pow, ← pow_mul, ← pow_mul]
      ring
    · ring
  have hm : ∀ m : ℕ, HasSum (fun k : ℕ => f (k, m)) (-log (1 - z ^ 2 / ((m : ℂ) + 1) ^ 2)) := by
    intro m
    have h := Complex.hasSum_taylorSeries_neg_log' (hw1 m)
    simpa [hf] using h
  refine ⟨_, hsum.hasSum.prod_fiberwise hk, ?_⟩
  have hswap : HasSum (f ∘ Prod.swap) (∑' p, f p) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hsum.hasSum
  exact hswap.prod_fiberwise fun m => hm m

/-- `‖z²/(m+1)²‖ < 1/(m+1)²` for `‖z‖ < 1`. -/
lemma s25a_norm_w_le {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    ‖z ^ 2 / ((m : ℂ) + 1) ^ 2‖ ≤ 1 / ((m : ℝ) + 1) ^ 2 := by
  rw [norm_div, norm_pow, norm_pow, show ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) by push_cast; ring,
    Complex.norm_natCast]
  push_cast
  gcongr
  nlinarith [norm_nonneg z]

/-- `‖z²/(m+1)²‖ < 1` for `‖z‖ < 1`. -/
lemma s25a_norm_w_lt {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) : ‖z ^ 2 / ((m : ℂ) + 1) ^ 2‖ < 1 := by
  rw [norm_div, norm_pow, norm_pow, show ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) by push_cast; ring,
    Complex.norm_natCast, div_lt_one (by positivity)]
  have : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  push_cast
  nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

/-- The exponential of the double series is `πz/sin(πz)`. -/
lemma s25a_exp_eq {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) {F : ℂ}
    (hF : HasSum (fun m : ℕ => -log (1 - z ^ 2 / ((m : ℂ) + 1) ^ 2)) F) :
    cexp F = π * z / sin (π * z) := by
  have hsin : sin (π * z) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hz' : z = k := by
      have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp at hk; linear_combination hk
    rw [hz', Complex.norm_intCast] at hz
    have : k = 0 := by
      have : |(k : ℝ)| < 1 := hz
      rw [abs_lt] at this
      have h1 : (-1 : ℤ) < k := by exact_mod_cast this.1
      have h2 : k < 1 := by exact_mod_cast this.2
      omega
    exact hz0 (by rw [hz', this]; simp)
  have hne : ∀ m : ℕ, (1 : ℂ) - z ^ 2 / ((m : ℂ) + 1) ^ 2 ≠ 0 := by
    intro m h
    have h1 : z ^ 2 / ((m : ℂ) + 1) ^ 2 = 1 := by linear_combination -h
    have := s25a_norm_w_lt hz m
    rw [h1, norm_one] at this
    exact lt_irrefl _ this
  set P : ℕ → ℂ := fun N => ∏ j ∈ range N, ((1 : ℂ) - z ^ 2 / ((j : ℂ) + 1) ^ 2) with hP
  have h1 : Tendsto (fun N => (P N)⁻¹) atTop (𝓝 (cexp F)) := by
    have := (continuous_exp.tendsto F).comp hF.tendsto_sum_nat
    refine this.congr fun N => ?_
    simp only [Function.comp_apply, hP]
    rw [Complex.exp_sum, ← prod_inv_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [Complex.exp_neg, Complex.exp_log (hne j)]
  have h2 : Tendsto (fun N => (P N)⁻¹) atTop (𝓝 (π * z / sin (π * z))) := by
    have hπz : (π : ℂ) * z ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) hz0
    have := ((Complex.tendsto_euler_sin_prod z).inv₀ hsin).const_mul ((π : ℂ) * z)
    refine this.congr fun N => ?_
    simp only [hP]
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hπz, one_mul]
  exact tendsto_nhds_unique h1 h2

/-- `|Im F| < π` for the double series. -/
lemma s25a_abs_im_lt {z : ℂ} (hz : ‖z‖ < 1) {F : ℂ}
    (hF : HasSum (fun m : ℕ => -log (1 - z ^ 2 / ((m : ℂ) + 1) ^ 2)) F) :
    |F.im| < π := by
  set L : ℕ → ℂ := fun m => -log (1 - z ^ 2 / ((m : ℂ) + 1) ^ 2) with hL
  have hbd : ∀ m : ℕ, ‖L (m + 1)‖ ≤ 2 * (1 / ((m : ℝ) + 2) ^ 2) := by
    intro m
    set w : ℂ := z ^ 2 / (((m + 1 : ℕ) : ℂ) + 1) ^ 2 with hwdef
    have hw : ‖w‖ ≤ 1 / ((m : ℝ) + 2) ^ 2 := by
      have := s25a_norm_w_le hz (m + 1)
      rw [show ((m + 1 : ℕ) : ℝ) + 1 = (m : ℝ) + 2 by push_cast; ring] at this
      exact this
    have hq : 1 / ((m : ℝ) + 2) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have hw' : ‖w‖ ≤ 1 / 4 := hw.trans hq
    have hl := Complex.norm_log_one_add_le (z := -w) (by rw [norm_neg]; linarith)
    rw [norm_neg] at hl
    have hLe : L (m + 1) = -log (1 + -w) := by
      simp only [hL, hwdef]; ring_nf
    rw [hLe, norm_neg]
    have hnn : 0 ≤ ‖w‖ := norm_nonneg _
    have hpos : 0 < 1 - ‖w‖ := by linarith
    have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hpos (by norm_num)]; linarith
    have : ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 ≤ ‖w‖ := by
      have h2 : ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ ≤ ‖w‖ ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      nlinarith
    linarith
  have hsL : Summable fun m : ℕ => L (m + 1) := (summable_nat_add_iff 1).mpr hF.summable
  have hb : HasSum (fun m : ℕ => 2 * (1 / ((m : ℝ) + 2) ^ 2)) (2 * (π ^ 2 / 6 - 1)) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one] at h
    norm_num at h
    refine (h.mul_left 2).congr_fun fun m => ?_
    ring_nf
  have hF' : F = L 0 + ∑' m, L (m + 1) := by
    rw [← hF.tsum_eq, hF.summable.tsum_eq_zero_add]
  have h0 : |(L 0).im| < π / 2 := by
    simp only [hL, neg_im, log_im, abs_neg, Nat.cast_zero, zero_add, one_pow, div_one]
    refine abs_arg_lt_pi_div_two_iff.mpr (Or.inl ?_)
    have : (z ^ 2).re ≤ ‖z‖ ^ 2 := by
      rw [← norm_pow]; exact re_le_norm _
    simp only [sub_re, one_re]
    nlinarith [norm_nonneg z]
  have hrest : |(∑' m, L (m + 1)).im| ≤ 2 * (π ^ 2 / 6 - 1) :=
    (abs_im_le_norm _).trans ((norm_tsum_le_tsum_norm hsL.norm).trans
      (hb.tsum_eq ▸ hsL.norm.tsum_le_tsum hbd hb.summable))
  rw [hF', add_im]
  have hπ := Real.pi_lt_d2
  have hπ3 := Real.pi_gt_three
  calc |(L 0).im + (∑' m, L (m + 1)).im| ≤ |(L 0).im| + |(∑' m, L (m + 1)).im| := abs_add_le _ _
    _ < π / 2 + 2 * (π ^ 2 / 6 - 1) := by linarith
    _ ≤ π := by nlinarith

/-- DLMF 25.8.8: `∑_{k≥1} (ζ(2k)/k) z^{2k} = ln(πz/sin(πz))` for `|z| < 1`, with the principal
logarithm (at `z = 0` both sides are `0`). -/
@[dlmf 25.8.E8]
theorem hasSum_riemannZeta_two_mul_div_mul_pow {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => riemannZeta (2 * (k + 1)) / (k + 1) * z ^ (2 * (k + 1)))
      (log (π * z / sin (π * z))) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  obtain ⟨F, h1, h2⟩ := s25a_hasSum_neg_log_prod hz
  have him := s25a_abs_im_lt hz h2
  rw [← s25a_exp_eq hz hz0 h2, Complex.log_exp (by linarith [(abs_lt.mp him).1])
    (by linarith [(abs_lt.mp him).2])]
  exact h1

/-- `0 ≤ πx cot(πx) ≤ 1` for `0 ≤ x ≤ 1/2`. -/
lemma r25a_pi_mul_cot_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    |π * x * Real.cot (π * x)| ≤ 1 := by
  rcases eq_or_lt_of_le hx0 with rfl | hx
  · simp
  have hy : 0 < π * x := by positivity
  have hy2 : π * x ≤ π / 2 := by nlinarith [Real.pi_pos]
  have hs : 0 < Real.sin (π * x) := Real.sin_pos_of_pos_of_lt_pi hy (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos (π * x) := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hy2
  rw [Real.cot_eq_cos_div_sin, abs_le]
  constructor
  · have : 0 ≤ π * x * (Real.cos (π * x) / Real.sin (π * x)) := by positivity
    linarith
  · rw [mul_div_assoc', div_le_one hs]
    rcases eq_or_lt_of_le hy2 with h | h
    · rw [h, Real.cos_pi_div_two, mul_zero, Real.sin_pi_div_two]; norm_num
    · have ht := Real.le_tan hy.le h
      rw [Real.tan_eq_sin_div_cos, le_div_iff₀ (by
        exact Real.cos_pos_of_mem_Ioo ⟨by linarith, h⟩)] at ht
      linarith

/-- `x ln sin(πx) → 0` as `x → 0` within `[0, 1/2]`. -/
lemma r25a_continuousWithinAt_mul_log_sin :
    ContinuousWithinAt (fun x : ℝ => x * Real.log (Real.sin (π * x))) (Set.Icc 0 (1 / 2)) 0 := by
  have hb : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2), ‖x * Real.log (Real.sin (π * x))‖ ≤
      ‖x * Real.log (2 * x)‖ := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | hx0
    · subst h; simp
    have h2 : 2 * x ≤ Real.sin (π * x) := by
      have := Real.mul_le_sin (x := π * x) (by positivity) (by nlinarith [Real.pi_pos, hx.2])
      rwa [show 2 / π * (π * x) = 2 * x by field_simp] at this
    have h1 : Real.sin (π * x) ≤ 1 := Real.sin_le_one _
    have hl1 : Real.log (Real.sin (π * x)) ≤ 0 := Real.log_nonpos (by linarith) h1
    have hl2 : Real.log (2 * x) ≤ Real.log (Real.sin (π * x)) := Real.log_le_log (by positivity) h2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hx0]
    refine mul_le_mul_of_nonneg_left ?_ hx0.le
    rw [abs_of_nonpos hl1, abs_of_nonpos (hl2.trans hl1)]
    linarith
  have hc : Tendsto (fun x : ℝ => x * Real.log (2 * x)) (𝓝[Set.Icc 0 (1 / 2)] 0) (𝓝 0) := by
    have h := (Real.continuous_mul_log.comp (continuous_const.mul continuous_id :
      Continuous fun x : ℝ => 2 * x)).tendsto 0
    have : (fun x : ℝ => x * Real.log (2 * x)) =
        fun x => (1 / 2) * ((2 * x) * Real.log (2 * x)) := by
      funext x; ring
    rw [this]
    simpa using (h.const_mul (1 / 2 : ℝ)).mono_left nhdsWithin_le_nhds
  show Tendsto _ _ _
  simp only [zero_mul]
  exact squeeze_zero_norm' (eventually_nhdsWithin_of_forall hb) (by simpa using hc.norm)

/-- `∫₀^{1/2} πx cot(πx) dx = ½ ln 2`. -/
lemma r25a_integral_pi_mul_cot :
    ∫ x in (0 : ℝ)..(1 / 2), π * x * Real.cot (π * x) = Real.log 2 / 2 := by
  set G : ℝ → ℝ := fun x => x * Real.log (Real.sin (π * x)) with hG
  have hlog : IntervalIntegrable (fun x : ℝ => Real.log (Real.sin (π * x))) MeasureTheory.volume
      0 (1 / 2) := by
    have := (intervalIntegrable_log_sin (a := 0) (b := π / 2)).comp_mul_left (c := π)
    simpa [Function.comp_def, show π / 2 / π = 1 / 2 by field_simp] using this
  have hcot : IntervalIntegrable (fun x : ℝ => π * x * Real.cot (π * x)) MeasureTheory.volume
      0 (1 / 2) := by
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' ?_ ?_
    · simp only [Real.cot_eq_cos_div_sin]
      exact (by fun_prop : Measurable fun x : ℝ =>
        π * x * (Real.cos (π * x) / Real.sin (π * x))).aestronglyMeasurable
    · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      refine MeasureTheory.ae_of_all _ fun x hx => ?_
      rw [Set.uIoc_of_le (by norm_num)] at hx
      exact r25a_pi_mul_cot_bound hx.1.le hx.2
  have hFTC : ∫ x in (0 : ℝ)..(1 / 2), (Real.log (Real.sin (π * x)) +
      π * x * Real.cot (π * x)) = G (1 / 2) - G 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) ?_ ?_ (hlog.add hcot)
    · intro x hx
      rcases eq_or_lt_of_le hx.1 with h | hx0
      · subst h; exact r25a_continuousWithinAt_mul_log_sin
      · refine ContinuousAt.continuousWithinAt ?_
        have hs : Real.sin (π * x) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (by positivity)
          (by nlinarith [Real.pi_pos, hx.2])).ne'
        exact continuousAt_id.mul ((Real.continuousAt_log hs).comp
          (f := fun x : ℝ => Real.sin (π * x)) (by fun_prop))
    · intro x hx
      have hs : Real.sin (π * x) ≠ 0 :=
        (Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos, hx.1])
          (by nlinarith [Real.pi_pos, hx.2])).ne'
      have h := (hasDerivAt_id x).mul ((((hasDerivAt_id x).const_mul π).sin).log hs)
      convert h using 1
      · funext y; simp [hG]
      · simp only [id, Real.cot_eq_cos_div_sin]
        field_simp
  have hG0 : G (1 / 2) - G 0 = 0 := by
    simp only [hG]
    rw [show π * (1 / 2) = π / 2 by ring, Real.sin_pi_div_two]
    simp
  rw [hG0, intervalIntegral.integral_add hlog hcot] at hFTC
  have hL : ∫ x in (0 : ℝ)..(1 / 2), Real.log (Real.sin (π * x)) = -Real.log 2 / 2 := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.log (Real.sin x)) Real.pi_ne_zero,
      mul_zero, show π * (1 / 2) = π / 2 by ring, integral_log_sin_zero_pi_div_two, smul_eq_mul]
    field_simp
  linarith

open scoped Interval in
/-- DLMF 25.8.9: `∑_{k≥1} ζ(2k)/((2k+1) 2^{2k}) = ½ - ½ ln 2`. -/
@[dlmf 25.8.E9]
theorem hasSum_riemannZeta_two_mul_div_odd :
    HasSum (fun k : ℕ => riemannZeta (2 * (k + 1)) / ((2 * (k + 1) + 1) * 2 ^ (2 * (k + 1))))
      (1 / 2 - 1 / 2 * Real.log 2) := by
  set F : ℕ → ℝ → ℂ := fun k x => riemannZeta (2 * (k + 1)) * (x : ℂ) ^ (2 * (k + 1)) with hF
  set f : ℝ → ℂ := fun x => (((1 - π * x * Real.cot (π * x)) / 2 : ℝ) : ℂ) with hf
  have hlim : ∀ x : ℝ, 0 < x → x ≤ 1 / 2 → HasSum (fun k => F k x) (f x) := by
    intro x hx0 hx1
    have hz : ‖(x : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; linarith
    have hz0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have h := (hasSum_nat_add_iff' 1).mpr (hasSum_riemannZeta_two_mul_mul_pow hz hz0)
    simp only [range_one, sum_singleton, Nat.cast_zero, mul_zero, pow_zero, mul_one,
      riemannZeta_zero] at h
    convert h using 1
    · funext k; simp only [hF]; push_cast; ring_nf
    · simp only [hf]
      rw [show (π : ℂ) * x = ((π * x : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cot]
      push_cast; ring
  have hzb : ∀ k : ℕ, ‖riemannZeta (2 * (k + 1))‖ ≤ 2 := by
    intro k
    have h := DLMF.Gamma.norm_riemannZeta_add_two_sub_one_le (2 * k)
    have e : ((2 * k : ℕ) : ℂ) + 2 = 2 * ((k : ℂ) + 1) := by push_cast; ring
    rw [e] at h
    have h1 : (1 / 2 : ℝ) ^ (2 * k) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have := norm_sub_norm_le (riemannZeta (2 * ((k : ℂ) + 1))) 1
    simp at this
    linarith
  set bound : ℕ → ℝ → ℝ := fun k _ => 2 * (1 / 4 : ℝ) ^ (k + 1) with hbound
  have hFb : ∀ k : ℕ, ∀ x ∈ Ι (0 : ℝ) (1 / 2), ‖F k x‖ ≤ bound k x := by
    intro k x hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    simp only [hF, hbound, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx.1]
    have : x ^ (2 * (k + 1)) ≤ (1 / 4 : ℝ) ^ (k + 1) := by
      rw [pow_mul, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hx.1.le hx.2 2) _
    exact mul_le_mul (hzb k) this (pow_nonneg hx.1.le _) (by norm_num)
  have hbs : Summable (fun k : ℕ => 2 * (1 / 4 : ℝ) ^ (k + 1)) :=
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1)).mul_left 2
  have hI := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := 0) (b := 1 / 2) bound
    (fun k => (by fun_prop : Continuous (F k)).aestronglyMeasurable)
    (fun k => MeasureTheory.ae_of_all _ (hFb k))
    (MeasureTheory.ae_of_all _ fun _ _ => hbs)
    (by simp only [hbound]; exact intervalIntegrable_const)
    (MeasureTheory.ae_of_all _ fun x hx => by
      rw [Set.uIoc_of_le (by norm_num)] at hx; exact hlim x hx.1 hx.2)
  have hFk : ∀ k : ℕ, ∫ x in (0 : ℝ)..(1 / 2), F k x =
      riemannZeta (2 * (k + 1)) *
        (((1 / 2 : ℝ) ^ (2 * (k + 1) + 1) / (2 * (k + 1) + 1) : ℝ) : ℂ) := by
    intro k
    simp only [hF]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have : (fun x : ℝ => (x : ℂ) ^ (2 * (k + 1))) = fun x : ℝ => ((x ^ (2 * (k + 1)) : ℝ) : ℂ) := by
      funext x; push_cast; rfl
    rw [this, intervalIntegral.integral_ofReal, integral_pow]
    push_cast; ring
  have hfI : ∫ x in (0 : ℝ)..(1 / 2), f x = ((1 / 4 - Real.log 2 / 4 : ℝ) : ℂ) := by
    simp only [hf]
    rw [intervalIntegral.integral_ofReal]
    congr 1
    have hc : IntervalIntegrable (fun x : ℝ => π * x * Real.cot (π * x)) MeasureTheory.volume
        0 (1 / 2) := by
      by_contra hn
      have := intervalIntegral.integral_undef hn
      rw [r25a_integral_pi_mul_cot] at this
      have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub intervalIntegrable_const hc,
      r25a_integral_pi_mul_cot]
    simp; ring
  simp only [hFk, hfI] at hI
  have h2 := hI.mul_left 2
  convert h2 using 1
  · funext k
    push_cast
    have h4 : ((1 : ℂ) / 2) ^ (2 * (k + 1) + 1) * 2 ^ (2 * (k + 1)) = 1 / 2 := by
      rw [pow_succ, mul_comm, ← mul_assoc, ← mul_pow]; norm_num
    have h5 : (2 * ((k : ℂ) + 1) + 1) ≠ 0 := by
      rw [show (2 * ((k : ℂ) + 1) + 1) = ((2 * k + 3 : ℕ) : ℂ) by push_cast; ring]
      exact_mod_cast (by omega : 2 * k + 3 ≠ 0)
    have h6 : (2 : ℂ) ^ (2 * (k + 1)) ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp
    linear_combination (-(2 : ℂ) * riemannZeta (2 * ((k : ℂ) + 1))) * h4
  · push_cast; ring

/-- DLMF 25.8.10: `∑_{k≥1} ζ(2k)/((2k+1)(2k+2) 2^{2k}) = ¼ - (7/(4π²)) ζ(3)`. -/
@[dlmf 25.8.E10]
theorem hasSum_riemannZeta_two_mul_div_odd_even :
    HasSum (fun k : ℕ => riemannZeta (2 * (k + 1)) /
        ((2 * (k + 1) + 1) * (2 * (k + 1) + 2) * 2 ^ (2 * (k + 1))))
      (1 / 4 - 7 / (4 * π ^ 2) * riemannZeta 3) := by
  sorry

end DLMF.Zeta
