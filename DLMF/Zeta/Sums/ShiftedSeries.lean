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
public import DLMF.Zeta.CotangentMoments
public import DLMF.Zeta.Riemann

/-!
# Series of shifted zeta values (DLMF 25.8.1–25.8.3)

Sums of `ζ(k) - 1` and the Pochhammer series of `ζ(s + k)`. The Pochhammer series 25.8.3
is first proved for large `ℜs` by the binomial series and then continued analytically to the
connected domain that excludes `s = 1` and the nonpositive integers.

## Main results

* `hasSum_riemannZeta_sub_one`: `∑_{k≥2} (ζ(k) - 1) = 1` (25.8.1).
* `hasSum_Gamma_mul_riemannZeta_sub_one`: 25.8.2.
* `hasSum_pochhammer_mul_riemannZeta`: 25.8.3, for `s ≠ 1` and `s ≠ 0, -1, -2, …`; at the
  excluded nonpositive integers Lean's totalized `riemannZeta 1` makes the printed series wrong.
-/

@[expose] public noncomputable section

open Complex Filter Topology Finset
open scoped Real Nat

namespace DLMF.Zeta

/-- `∑_{n≥0} 1/((n+1)(n+2)) = 1` (telescoping). -/
private lemma hasSum_one_div_add_two_mul_add_one :
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
private lemma hasSum_one_div_add_two_pow_add_two (n : ℕ) :
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
    ⟨fun n => (hasSum_one_div_add_two_pow_add_two n).summable, by
      simp only [hF]
      exact hasSum_one_div_add_two_mul_add_one.summable.congr fun n => (hasSum_one_div_add_two_pow_add_two n).tsum_eq.symm⟩
  have h1 : HasSum F 1 := by
    have := hS.hasSum.prod_fiberwise fun n => hasSum_one_div_add_two_pow_add_two n
    rw [hasSum_one_div_add_two_mul_add_one.unique this]; exact hS.hasSum
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
private lemma hasSum_ascPochhammer_div_factorial_mul_pow (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
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
private lemma ascPochhammer_eval_nonneg {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : 0 ≤ (ascPochhammer ℝ k).eval t := by
  induction k with
  | zero => simp
  | succ k ih => rw [ascPochhammer_succ_eval]; positivity

/-- `‖(s)_k‖ ≤ (‖s‖)_k`. -/
private lemma norm_ascPochhammer_eval_le (s : ℂ) (k : ℕ) :
    ‖(ascPochhammer ℂ k).eval s‖ ≤ (ascPochhammer ℝ k).eval ‖s‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, norm_mul]
    refine mul_le_mul ih ?_ (norm_nonneg _) ?_
    · refine (norm_add_le _ _).trans ?_
      simp
    · exact ascPochhammer_eval_nonneg (norm_nonneg s) k

/-- The domain `ℂ ∖ {1, 0, -1, -2, …}`. -/
def complOneSubNat : Set ℂ := (Set.range fun n : ℕ => (1 : ℂ) - n)ᶜ

/-- Formula under the stated hypotheses: `s ∈ complOneSubNat ↔ ∀ n : ℕ, s ≠ 1 - n`. -/
private lemma mem_complOneSubNat {s : ℂ} : s ∈ complOneSubNat ↔ ∀ n : ℕ, s ≠ 1 - n := by
  simp [complOneSubNat, eq_comm]

/-- The indicated domain is open: `IsOpen complOneSubNat`. -/
private lemma isOpen_complOneSubNat : IsOpen complOneSubNat := by
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
  rw [complOneSubNat, this, isOpen_compl_iff]
  exact Complex.isClosed_range_intCast.inter (isClosed_le continuous_re continuous_const)

/-- The stated relation follows from the given hypotheses: `IsPreconnected complOneSubNat`. -/
private lemma isPreconnected_complOneSubNat : IsPreconnected complOneSubNat :=
  ((Set.countable_range _).isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected

/-- Estimate under the stated parameter and domain assumptions: `{s : ℂ | 1 < s.re} ⊆ complOneSubNat`. -/
private lemma setOf_one_lt_re_subset_complOneSubNat : {s : ℂ | 1 < s.re} ⊆ complOneSubNat := by
  intro s hs
  have hs' : 1 < s.re := hs
  rw [mem_complOneSubNat]
  intro n h
  have := congrArg re h
  simp at this
  have : s.re = 1 - n := this
  linarith [hs', (n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- `ζ(w) = ∑_{n≥0} (n+1)^{-w}` for `Re w > 1`, as a `HasSum`. -/
private lemma hasSum_one_div_succ_cpow_riemannZeta {w : ℂ} (hw : 1 < w.re) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ w) (riemannZeta w) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hw]
  refine Summable.hasSum ?_
  have := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hw)
  simpa using this

/-- `‖ζ(w) - 1‖ ≤ 2^{2 - Re w} C` for `Re w ≥ 2`. -/
private lemma exists_norm_riemannZeta_sub_one_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 2 ≤ w.re →
    ‖riemannZeta w - 1‖ ≤ (2 : ℝ) ^ (2 - w.re) * C := by
  have hC : Summable fun n : ℕ => 1 / ((n : ℝ) + 2) ^ (2 : ℕ) := by
    have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    refine (this.comp_injective (add_left_injective 2)).congr fun n => ?_
    simp [Function.comp]
  refine ⟨∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ (2 : ℕ), tsum_nonneg fun n => by positivity, ?_⟩
  intro w hw
  have hs1 : 1 < w.re := by linarith
  have hz := hasSum_one_div_succ_cpow_riemannZeta hs1
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
private lemma summable_ascPochhammer_div_factorial_mul_pow_real (t : ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Summable fun k : ℕ => (ascPochhammer ℝ k).eval t / k ! * x ^ k := by
  have h := (hasSum_ascPochhammer_div_factorial_mul_pow (t : ℂ) (x := (x : ℂ)) (by
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
private lemma hasSum_ascPochhammer_mul_riemannZeta_div_two_pow_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
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
    have hh := summable_ascPochhammer_div_factorial_mul_pow_real ‖s‖ (x := 1 / 2) (by norm_num) (by norm_num)
    refine Summable.of_norm_bounded (hh.mul_of_nonneg hg
      (fun k => by have := ascPochhammer_eval_nonneg (norm_nonneg s) k; positivity)
      (fun m => by have := hb0 m; positivity)) fun p => ?_
    simp only [hf, norm_mul, norm_pow]
    rw [norm_div ((ascPochhammer ℂ p.1).eval s), Complex.norm_natCast,
      norm_cpow_eq_rpow_re_of_pos (hb0 p.2), neg_re]
    have h1 := norm_ascPochhammer_eval_le s p.1
    have h2 : ‖1 / ((b p.2 : ℝ) : ℂ)‖ ^ p.1 ≤ (1 / 2) ^ p.1 :=
      pow_le_pow_left₀ (norm_nonneg _) (hx p.2) _
    have h3 : 0 ≤ (b p.2) ^ (-s.re) := (Real.rpow_pos_of_pos (hb0 p.2) _).le
    have h4 : (0 : ℝ) < p.1 ! := by exact_mod_cast Nat.factorial_pos _
    have h5 : 0 ≤ (ascPochhammer ℝ p.1).eval ‖s‖ / p.1 ! :=
      div_nonneg (ascPochhammer_eval_nonneg (norm_nonneg s) _) h4.le
    calc (b p.2) ^ (-s.re) * (‖(ascPochhammer ℂ p.1).eval s‖ / p.1 ! *
          ‖1 / ((b p.2 : ℝ) : ℂ)‖ ^ p.1)
        ≤ (b p.2) ^ (-s.re) * ((ascPochhammer ℝ p.1).eval ‖s‖ / p.1 ! * (1 / 2) ^ p.1) := by
          gcongr
      _ = (ascPochhammer ℝ p.1).eval ‖s‖ / p.1 ! * (1 / 2) ^ p.1 * (b p.2) ^ (-s.re) := by ring
  have hk : ∀ k : ℕ, HasSum (fun m : ℕ => f (k, m))
      ((ascPochhammer ℂ k).eval s * riemannZeta (s + k) / (k ! * 2 ^ (s + k))) := by
    intro k
    have hre : 1 < (s + k).re := by simp; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    have h := (hasSum_one_div_succ_cpow_riemannZeta hre).mul_left
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
    have h := (hasSum_ascPochhammer_div_factorial_mul_pow s (x := 1 / ((b m : ℝ) : ℂ))
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
private lemma hasSum_on_complOneSubNat_of_one_lt_re (T : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (hT : ∀ k, DifferentiableOn ℂ (T k) complOneSubNat) (hg : DifferentiableOn ℂ g complOneSubNat)
    (hdom : ∀ x ∈ complOneSubNat, ∃ V ∈ 𝓝 x, ∃ N : ℕ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n, N ≤ n → ∀ y ∈ V, ‖T n y‖ ≤ u n)
    (hre : ∀ s : ℂ, 1 < s.re → HasSum (fun k => T k s) (g s)) :
    ∀ s ∈ complOneSubNat, HasSum (fun k => T k s) (g s) := by
  have hsum : ∀ s ∈ complOneSubNat, Summable fun k => T k s := by
    intro s hs
    obtain ⟨V, hV, N, u, hu, hle⟩ := hdom s hs
    refine (summable_nat_add_iff N).mp ?_
    exact Summable.of_norm_bounded ((summable_nat_add_iff N).mpr hu)
      fun k => hle (k + N) (by omega) s (mem_of_mem_nhds hV)
  have hd : DifferentiableOn ℂ (fun s => ∑' k, T k s) complOneSubNat :=
    Complex.differentiableOn_tsum_of_eventually_dominated isOpen_complOneSubNat hT hdom
  have h2 : (2 : ℂ) ∈ complOneSubNat := setOf_one_lt_re_subset_complOneSubNat (by norm_num)
  have heq : Set.EqOn (fun s => ∑' k, T k s) g complOneSubNat := by
    refine (hd.analyticOnNhd isOpen_complOneSubNat).eqOn_of_preconnected_of_eventuallyEq
      (hg.analyticOnNhd isOpen_complOneSubNat) isPreconnected_complOneSubNat h2 ?_
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact (hre z hz).tsum_eq
  intro s hs
  rw [← heq hs]
  exact (hsum s hs).hasSum

/-- `t ↦ (t)_k` is monotone on `[0, ∞)`. -/
private lemma ascPochhammer_eval_mono {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) (k : ℕ) :
    (ascPochhammer ℝ k).eval t ≤ (ascPochhammer ℝ k).eval u := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
    exact mul_le_mul ih (by linarith) (by positivity)
      (ascPochhammer_eval_nonneg (ht.trans htu) k)

/-- Local data for the dominations: near `x`, `‖y‖ ≤ R` and, for `n ≥ N`, `Re(y+n) ≥ 2` and
`‖2^{-(y+n)}‖ ≤ 2^R 2^{-n}`. -/
private lemma exists_nhds_bound_inv_two_cpow (x : ℂ) : ∃ V ∈ 𝓝 x, ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ y ∈ V, ‖y‖ ≤ R ∧
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
private lemma differentiableOn_ascPochhammer_mul_riemannZeta_div_two_pow (k : ℕ) : DifferentiableOn ℂ (fun s : ℂ =>
    (ascPochhammer ℂ k).eval s * riemannZeta (s + k) / (k ! * 2 ^ (s + k))) complOneSubNat := by
  intro s hs
  have hs' := mem_complOneSubNat.mp hs
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
private lemma hasSum_ascPochhammer_div_factorial_succ_mul_pow {s x : ℂ} (hs : s ≠ 1) (hx0 : x ≠ 0) (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ => (ascPochhammer ℂ k).eval s / (k + 1) ! * x ^ k)
      ((1 / (1 - x) ^ (s - 1) - 1) / ((s - 1) * x)) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_ascPochhammer_div_factorial_mul_pow (s - 1) hx)
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
private lemma hasSum_ascPochhammer_mul_riemannZeta_sub_one_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
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
    have hh := summable_ascPochhammer_div_factorial_mul_pow_real ‖s‖ (x := 1 / 2) (by norm_num) (by norm_num)
    refine Summable.of_norm_bounded (hh.mul_of_nonneg hg
      (fun k => by have := ascPochhammer_eval_nonneg (norm_nonneg s) k; positivity)
      (fun m => by have := hc0 m; positivity)) fun p => ?_
    simp only [hf, norm_mul, norm_pow]
    rw [norm_div ((ascPochhammer ℂ p.1).eval s), Complex.norm_natCast,
      norm_cpow_eq_rpow_re_of_pos (hc0 p.2), neg_re]
    have h1 := norm_ascPochhammer_eval_le s p.1
    have h2 : ‖1 / ((c p.2 : ℝ) : ℂ)‖ ^ p.1 ≤ (1 / 2) ^ p.1 :=
      pow_le_pow_left₀ (norm_nonneg _) (hx p.2) _
    have h3 : 0 ≤ (c p.2) ^ (-s.re) := (Real.rpow_pos_of_pos (hc0 p.2) _).le
    have h4 : (0 : ℝ) < p.1 ! := by exact_mod_cast Nat.factorial_pos _
    have h4' : (p.1 ! : ℝ) ≤ (p.1 + 1) ! := by exact_mod_cast Nat.factorial_le (by omega)
    have h5 : 0 ≤ (ascPochhammer ℝ p.1).eval ‖s‖ := ascPochhammer_eval_nonneg (norm_nonneg s) _
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
    have h0 := (hasSum_nat_add_iff' 1).mpr (hasSum_one_div_succ_cpow_riemannZeta hre)
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
    have h := (hasSum_ascPochhammer_div_factorial_succ_mul_pow hs1 (one_div_ne_zero hC)
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
      have h := (tendsto_ofReal_cpow_atTop_of_re_neg (z := 1 - s) (by simp; linarith)).comp
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
private lemma differentiableOn_ascPochhammer_mul_riemannZeta_sub_one (k : ℕ) : DifferentiableOn ℂ (fun s : ℂ =>
    (ascPochhammer ℂ k).eval s / (k + 1) ! * (riemannZeta (s + k) - 1)) complOneSubNat := by
  intro s hs
  have hs' := mem_complOneSubNat.mp hs
  have hz : s + k ≠ 1 := by
    intro h; exact hs' k (by linear_combination h)
  refine DifferentiableAt.differentiableWithinAt ?_
  exact ((Polynomial.differentiable _).differentiableAt.div_const _).mul
    (((differentiableAt_riemannZeta hz).comp s (differentiableAt_id.add_const _)).sub_const _)

/-- DLMF 25.8.2 core: `∑_k (s)_k/(k+1)! (ζ(s+k) - 1) = 1/(s-1)` on `ℂ ∖ {1, 0, -1, …}`. -/
private lemma hasSum_ascPochhammer_mul_riemannZeta_sub_one {s : ℂ} (hs : s ∈ complOneSubNat) :
    HasSum (fun k : ℕ => (ascPochhammer ℂ k).eval s / (k + 1) ! * (riemannZeta (s + k) - 1))
      (1 / (s - 1)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannZeta_sub_one_le
  refine hasSum_on_complOneSubNat_of_one_lt_re (fun k s => (ascPochhammer ℂ k).eval s / (k + 1) ! *
      (riemannZeta (s + k) - 1)) (fun s => 1 / (s - 1)) differentiableOn_ascPochhammer_mul_riemannZeta_sub_one ?_ ?_
    (fun s hs => hasSum_ascPochhammer_mul_riemannZeta_sub_one_of_one_lt_re hs) s hs
  · intro z hz
    have hz1 : z - 1 ≠ 0 := by
      have := mem_complOneSubNat.mp hz 0; exact sub_ne_zero.mpr (by simpa using this)
    have hd : DifferentiableAt ℂ (fun s : ℂ => 1 / (s - 1)) z :=
      (differentiableAt_const _).div (differentiableAt_id.sub_const _) hz1
    exact hd.differentiableWithinAt
  · intro x _
    obtain ⟨V, hV, R, hR, N, hloc⟩ := exists_nhds_bound_inv_two_cpow x
    refine ⟨V, hV, N, fun n => (ascPochhammer ℝ n).eval R / n ! * (1 / 2) ^ n * (4 * 2 ^ R * C),
      (summable_ascPochhammer_div_factorial_mul_pow_real R (by norm_num) (by norm_num)).mul_right _, ?_⟩
    intro n hn y hy
    obtain ⟨hyR, hy2⟩ := hloc y hy
    obtain ⟨hre, h2⟩ := hy2 n hn
    have hP : ‖(ascPochhammer ℂ n).eval y‖ ≤ (ascPochhammer ℝ n).eval R :=
      (norm_ascPochhammer_eval_le y n).trans (ascPochhammer_eval_mono (norm_nonneg y) hyR n)
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
    have hPn : 0 ≤ (ascPochhammer ℝ n).eval R := ascPochhammer_eval_nonneg hR n
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
  have hU : s ∈ complOneSubNat := mem_complOneSubNat.mpr hs
  have hpole : ∀ m : ℕ, s ≠ -m := by
    intro m h; exact hs (m + 1) (by rw [h]; push_cast; ring)
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (by simpa using hs 0)
  have h := (hasSum_ascPochhammer_mul_riemannZeta_sub_one hU).mul_left (Gamma s)
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
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannZeta_sub_one_le
  have hU : s ∈ complOneSubNat := by
    rw [mem_complOneSubNat]
    intro n
    rcases n with _ | m
    · simpa using hs1
    · have := hs m; push_cast; intro h; exact this (by linear_combination h)
  refine hasSum_on_complOneSubNat_of_one_lt_re (fun k s => (ascPochhammer ℂ k).eval s * riemannZeta (s + k) /
      (k ! * 2 ^ (s + k))) (fun s => (1 - 2 ^ (-s)) * riemannZeta s) differentiableOn_ascPochhammer_mul_riemannZeta_div_two_pow ?_ ?_
    (fun s hs => hasSum_ascPochhammer_mul_riemannZeta_div_two_pow_of_one_lt_re hs) s hU
  · intro z hz
    have hz1 : z ≠ 1 := by have := mem_complOneSubNat.mp hz 0; simpa using this
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((differentiableAt_const _).sub (differentiableAt_id.neg.const_cpow
      (Or.inl two_ne_zero))).mul (differentiableAt_riemannZeta hz1)
  · intro x _
    obtain ⟨V, hV, R, hR, N, hloc⟩ := exists_nhds_bound_inv_two_cpow x
    refine ⟨V, hV, N, fun n => (ascPochhammer ℝ n).eval R / n ! * (1 / 2) ^ n * ((1 + C) * 2 ^ R),
      (summable_ascPochhammer_div_factorial_mul_pow_real R (by norm_num) (by norm_num)).mul_right _, ?_⟩
    intro n hn y hy
    obtain ⟨hyR, hy2⟩ := hloc y hy
    obtain ⟨hre, h2⟩ := hy2 n hn
    have hP : ‖(ascPochhammer ℂ n).eval y‖ ≤ (ascPochhammer ℝ n).eval R :=
      (norm_ascPochhammer_eval_le y n).trans (ascPochhammer_eval_mono (norm_nonneg y) hyR n)
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
    have hPn : 0 ≤ (ascPochhammer ℝ n).eval R := ascPochhammer_eval_nonneg hR n
    calc ‖(ascPochhammer ℂ n).eval y‖ * ‖riemannZeta (y + n)‖ * ((n ! : ℝ)⁻¹ *
          ‖(2 : ℂ) ^ (y + n)‖⁻¹)
        ≤ (ascPochhammer ℝ n).eval R * (1 + C) * ((n ! : ℝ)⁻¹ * (2 ^ R * (1 / 2) ^ n)) := by
          gcongr
      _ = _ := by ring

end DLMF.Zeta
