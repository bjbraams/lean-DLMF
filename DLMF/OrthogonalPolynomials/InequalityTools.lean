/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Inequalities

/-!
# Tools for inequalities of classical orthogonal polynomials

Helpers for DLMF §18.14:

* elementary logarithmic inequalities proved by monotonicity from `0`
  (`opIneq_logRatio_even`, `opIneq_logRatio_odd`);
* sharp Gamma-ratio bounds of Kershaw type, obtained from a strictly increasing sequence
  dominated by Gautschi's bounds (DLMF 5.6.4): `opIneq_Gamma_even`, `opIneq_Gamma_odd`;
* a Sonine-type bound for solutions of the Gegenbauer equation with `0 < λ < 1`
  (`opIneq_gegenbauer_sonine`), which is the core of Lorch's inequality DLMF 18.14.7.
-/

@[expose] public section

open Filter Set
open scoped Topology

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- `Γ(x + m) = (x)_m Γ(x)` for real `x > 0`. -/
theorem opIneq_Gamma_add_nat {x : ℝ} (hx : 0 < x) (m : ℕ) :
    Real.Gamma (x + m) = (ascPochhammer ℝ m).eval x * Real.Gamma x := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, Nat.cast_succ, ← add_assoc,
      Real.Gamma_add_one (by positivity : x + (k : ℝ) ≠ 0), ih]
    ring

/-- A function vanishing at `0` with positive derivative on `(0, T)` is positive at `T`. -/
theorem opIneq_pos_of_hasDerivAt {F F' : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (h0 : F 0 = 0)
    (hF : ∀ s ∈ Icc 0 T, HasDerivAt F (F' s) s) (hF' : ∀ s ∈ Ioo 0 T, 0 < F' s) : 0 < F T := by
  have hmono : StrictMonoOn F (Icc 0 T) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 T)
      (fun s hs => (hF s hs).continuousAt.continuousWithinAt)
      (fun s hs => by
        rw [interior_Icc] at hs ⊢
        exact (hF s (Ioo_subset_Icc_self hs)).hasDerivWithinAt)
      (fun s hs => by rw [interior_Icc] at hs; exact hF' s hs)
  have := hmono ⟨le_rfl, hT.le⟩ ⟨hT.le, le_rfl⟩ hT
  rwa [h0] at this

/-- Derivative of `log (1 + a s) - log (1 - a s)`. -/
theorem opIneq_hasDerivAt_logRatio (a : ℝ) {s : ℝ} (hs : |a * s| < 1) :
    HasDerivAt (fun s => Real.log (1 + a * s) - Real.log (1 - a * s))
      (a / (1 + a * s) + a / (1 - a * s)) s := by
  have h1 : 0 < 1 + a * s := by linarith [neg_abs_le (a * s)]
  have h2 : 0 < 1 - a * s := by linarith [le_abs_self (a * s)]
  have e1 : HasDerivAt (fun s => 1 + a * s) a s := by
    simpa using ((hasDerivAt_id s).const_mul a).const_add 1
  have e2 : HasDerivAt (fun s => 1 - a * s) (-a) s := by
    simpa using ((hasDerivAt_id s).const_mul a).const_sub 1
  have := (e1.log h1.ne').sub (e2.log h2.ne')
  convert this using 1
  ring

/-- The logarithmic inequality behind the even case: for `0 < p < 1` and `0 < t < 1`,
`log((1 + p t)/(1 - p t)) < p log((1 + t)/(1 - t))`. -/
theorem opIneq_logRatio_even {p t : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    Real.log (1 + p * t) - Real.log (1 - p * t) <
      p * (Real.log (1 + 1 * t) - Real.log (1 - 1 * t)) := by
  set F : ℝ → ℝ := fun s => p * (Real.log (1 + 1 * s) - Real.log (1 - 1 * s)) -
    (Real.log (1 + p * s) - Real.log (1 - p * s))
  have hpos : 0 < F t := by
    refine opIneq_pos_of_hasDerivAt (F' := fun s => p * (1 / (1 + 1 * s) + 1 / (1 - 1 * s)) -
      (p / (1 + p * s) + p / (1 - p * s))) ht0 (by simp [F]) (fun s hs => ?_) (fun s hs => ?_)
    · have hs1 : |1 * s| < 1 := by rw [one_mul, abs_of_nonneg hs.1]; linarith [hs.2]
      have hsp : |p * s| < 1 := by
        rw [abs_of_nonneg (mul_nonneg hp0.le hs.1)]; nlinarith [hs.2, hs.1]
      exact ((opIneq_hasDerivAt_logRatio 1 hs1).const_mul p).sub (opIneq_hasDerivAt_logRatio p hsp)
    · obtain ⟨hs0, hs1⟩ := hs
      have a1 : 0 < 1 - s := by linarith
      have a2 : 0 < 1 - p * s := by nlinarith
      have a3 : 0 < 1 + p * s := by positivity
      have key : p * (1 / (1 + 1 * s) + 1 / (1 - 1 * s)) - (p / (1 + p * s) + p / (1 - p * s)) =
          2 * p * (1 - p ^ 2) * s ^ 2 / ((1 - s ^ 2) * (1 - p ^ 2 * s ^ 2)) := by
        have : (1 : ℝ) + 1 * s ≠ 0 := by linarith
        have : (1 : ℝ) - 1 * s ≠ 0 := by linarith
        have : (1 : ℝ) - s ^ 2 ≠ 0 := by nlinarith
        have : (1 : ℝ) - p ^ 2 * s ^ 2 ≠ 0 := by nlinarith
        field_simp
        ring
      rw [key]
      have : 0 < 1 - s ^ 2 := by nlinarith
      have : 0 < 1 - p ^ 2 * s ^ 2 := by nlinarith
      have : 0 < 1 - p ^ 2 := by nlinarith
      positivity
  simp only [F] at hpos
  linarith

/-- The logarithmic inequality behind the odd case: for `0 < λ < 1`, `c = λ(1-λ)` and
`0 < t ≤ 1/2`,
`½ log(((1+t)² + c t²)/((1-t)² + c t²)) < log((1+λt)/(1-λt)) + (1-λ) log((1+t)/(1-t))`. -/
theorem opIneq_logRatio_odd {l t : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    (Real.log ((1 + t) ^ 2 + l * (1 - l) * t ^ 2) -
        Real.log ((1 - t) ^ 2 + l * (1 - l) * t ^ 2)) / 2 <
      (Real.log (1 + l * t) - Real.log (1 - l * t)) +
        (1 - l) * (Real.log (1 + 1 * t) - Real.log (1 - 1 * t)) := by
  set c := l * (1 - l) with hc
  have hc0 : 0 < c := by positivity
  set F : ℝ → ℝ := fun s => (Real.log (1 + l * s) - Real.log (1 - l * s)) +
        (1 - l) * (Real.log (1 + 1 * s) - Real.log (1 - 1 * s)) -
      (Real.log ((1 + s) ^ 2 + c * s ^ 2) - Real.log ((1 - s) ^ 2 + c * s ^ 2)) / 2
  have hpos : 0 < F t := by
    refine opIneq_pos_of_hasDerivAt (F' := fun s => (l / (1 + l * s) + l / (1 - l * s)) +
        (1 - l) * (1 / (1 + 1 * s) + 1 / (1 - 1 * s)) -
        ((2 * (1 + s) + 2 * c * s) / ((1 + s) ^ 2 + c * s ^ 2) -
          (-(2 * (1 - s)) + 2 * c * s) / ((1 - s) ^ 2 + c * s ^ 2)) / 2)
      ht0 (by simp [F]) (fun s hs => ?_) (fun s hs => ?_)
    · obtain ⟨hs0, hs1⟩ := hs
      have hs1' : |1 * s| < 1 := by rw [one_mul, abs_of_nonneg hs0]; linarith
      have hsl : |l * s| < 1 := by rw [abs_of_nonneg (mul_nonneg hl0.le hs0)]; nlinarith
      have q1 : 0 < (1 + s) ^ 2 + c * s ^ 2 := by positivity
      have q2 : 0 < (1 - s) ^ 2 + c * s ^ 2 := by nlinarith
      have d1 : HasDerivAt (fun s => (1 + s) ^ 2 + c * s ^ 2) (2 * (1 + s) + 2 * c * s) s := by
        refine ((((hasDerivAt_id' s).const_add 1).pow 2).add
          ((hasDerivAt_pow 2 s).const_mul c)).congr_deriv ?_
        simp; ring
      have d2 : HasDerivAt (fun s => (1 - s) ^ 2 + c * s ^ 2) (-(2 * (1 - s)) + 2 * c * s) s := by
        refine ((((hasDerivAt_id' s).const_sub 1).pow 2).add
          ((hasDerivAt_pow 2 s).const_mul c)).congr_deriv ?_
        simp; ring
      exact (((opIneq_hasDerivAt_logRatio l hsl).add
        ((opIneq_hasDerivAt_logRatio 1 hs1').const_mul (1 - l))).sub
        (((d1.log q1.ne').sub (d2.log q2.ne')).div_const 2))
    · obtain ⟨hs0, hs1⟩ := hs
      have a1 : 0 < 1 - s := by linarith
      have a2 : 0 < 1 - l * s := by nlinarith
      have a3 : 0 < 1 + l * s := by positivity
      have q1 : 0 < (1 + s) ^ 2 + c * s ^ 2 := by positivity
      have q2 : 0 < (1 - s) ^ 2 + c * s ^ 2 := by nlinarith
      set Q := 2 - l + s ^ 2 * (3 + l - 4 * l ^ 2 + 2 * l ^ 3) -
        s ^ 4 * (l ^ 5 - 2 * l ^ 4 - 2 * l ^ 3 + 2 * l ^ 2 + 3 * l + 1) with hQ
      have key : (l / (1 + l * s) + l / (1 - l * s)) +
          (1 - l) * (1 / (1 + 1 * s) + 1 / (1 - 1 * s)) -
          ((2 * (1 + s) + 2 * c * s) / ((1 + s) ^ 2 + c * s ^ 2) -
            (-(2 * (1 - s)) + 2 * c * s) / ((1 - s) ^ 2 + c * s ^ 2)) / 2 =
          2 * l * (1 - l) * s ^ 2 * Q / ((1 - s ^ 2) * (1 - l ^ 2 * s ^ 2) *
            ((1 + s) ^ 2 + c * s ^ 2) * ((1 - s) ^ 2 + c * s ^ 2)) := by
        have : (1 : ℝ) + 1 * s ≠ 0 := by linarith
        have : (1 : ℝ) - 1 * s ≠ 0 := by linarith
        have : (1 : ℝ) - s ^ 2 ≠ 0 := by nlinarith
        have : (1 : ℝ) - l ^ 2 * s ^ 2 ≠ 0 := by nlinarith
        field_simp
        rw [hQ, hc]
        ring
      rw [key]
      have hs2 : s ^ 2 ≤ 1 / 4 := by nlinarith
      have hs4 : s ^ 4 ≤ 1 / 16 := by nlinarith
      have hQpos : 0 < Q := by
        have e1 : 0 ≤ 3 + l - 4 * l ^ 2 + 2 * l ^ 3 := by nlinarith
        have e2 : l ^ 5 - 2 * l ^ 4 - 2 * l ^ 3 + 2 * l ^ 2 + 3 * l + 1 ≤ 7 := by
          have : l ^ 5 ≤ 1 := pow_le_one₀ hl0.le hl1.le
          have : l ^ 2 ≤ 1 := pow_le_one₀ hl0.le hl1.le
          have : 0 ≤ l ^ 4 := by positivity
          have : 0 ≤ l ^ 3 := by positivity
          linarith
        have : 0 ≤ s ^ 4 := by positivity
        nlinarith [mul_nonneg (sq_nonneg s) e1]
      have : 0 < 1 - s ^ 2 := by nlinarith
      have : 0 < 1 - l ^ 2 * s ^ 2 := by nlinarith
      have : 0 < 1 - l := by linarith
      positivity
  simp only [F] at hpos
  linarith


/-- A strictly increasing sequence dominated eventually by a sequence tending to `0` is
negative. -/
theorem opIneq_neg_of_strictMono {s U : ℕ → ℝ} (hs : ∀ k, s k < s (k + 1))
    (hU : ∀ K, 1 ≤ K → s K ≤ U K) (hlim : Tendsto U atTop (𝓝 0)) (m : ℕ) : s m < 0 := by
  have hmono : StrictMono s := strictMono_nat_of_lt_succ hs
  have hle : s (m + 1) ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (m + 1)] with K hK
    exact (hmono.monotone hK).trans (hU K (by omega))
  exact (hs m).trans_le hle

/-- `log Γ(x + 1) = log x + log Γ(x)` for `x > 0`. -/
theorem opIneq_log_Gamma_succ {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma (x + 1)) = Real.log x + Real.log (Real.Gamma x) := by
  rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']

/-- `log(x/y) → 0` when `x/y → 1` along `ℕ`. -/
theorem opIneq_tendsto_log_ratio {a : ℝ} (ha : 0 < a) (u v : ℝ) :
    Tendsto (fun K : ℕ => Real.log ((a * K + u) / (a * K + v))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun K : ℕ => (a * K + u) / (a * K + v)) atTop (𝓝 1) := by
    have hK : Tendsto (fun K : ℕ => (K : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have e : ∀ᶠ K : ℕ in atTop, (a * K + u) / (a * K + v) =
        (a + u * (K : ℝ)⁻¹) / (a + v * (K : ℝ)⁻¹) := by
      filter_upwards [eventually_gt_atTop 0] with K hK
      have : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
      field_simp
    refine Tendsto.congr' (EventuallyEq.symm e) ?_
    have hinv := tendsto_inv_atTop_zero.comp hK
    have := ((tendsto_const_nhds (x := a)).add (hinv.const_mul u)).div
      ((tendsto_const_nhds (x := a)).add (hinv.const_mul v)) (by simp; exact ha.ne')
    simp only [mul_zero, add_zero, div_self ha.ne'] at this
    exact this
  have := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
  rwa [Real.log_one] at this


/-- Kershaw-type bound used for the even Gegenbauer case:
`Γ(m + λ)/Γ(m + 1) < (m + λ/2)^{λ - 1}` for `0 < λ < 1`. -/
theorem opIneq_Gamma_even {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (m : ℕ) :
    Real.Gamma (m + l) / Real.Gamma (m + 1) < ((m : ℝ) + l / 2) ^ (l - 1) := by
  set s : ℕ → ℝ := fun k => Real.log (Real.Gamma (k + l)) - Real.log (Real.Gamma (k + 1)) +
    (1 - l) * Real.log (k + l / 2) with hsdef
  have hs : ∀ k, s k < s (k + 1) := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have g1 : Real.log (Real.Gamma (((k + 1 : ℕ) : ℝ) + l)) =
        Real.log (k + l) + Real.log (Real.Gamma (k + l)) := by
      rw [show ((k + 1 : ℕ) : ℝ) + l = (k + l) + 1 by push_cast; ring]
      exact opIneq_log_Gamma_succ (by positivity)
    have g2 : Real.log (Real.Gamma (((k + 1 : ℕ) : ℝ) + 1)) =
        Real.log (k + 1) + Real.log (Real.Gamma (k + 1)) := by
      rw [show ((k + 1 : ℕ) : ℝ) + 1 = (k + 1) + 1 by push_cast; ring]
      exact opIneq_log_Gamma_succ (by positivity)
    set M : ℝ := (2 * k + 1 + l) / 2 with hM
    have hMpos : 0 < M := by positivity
    set t : ℝ := 1 / (2 * k + 1 + l) with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t < 1 := by rw [ht, div_lt_one (by positivity)]; linarith
    have key := opIneq_logRatio_even (p := 1 - l) (by linarith) (by linarith) ht0 ht1
    have hD : (2 * (k : ℝ) + 1 + l) ≠ 0 := by positivity
    have e1 : 1 + (1 - l) * t = (k + 1) / M := by rw [ht, hM]; field_simp; ring
    have e2 : 1 - (1 - l) * t = (k + l) / M := by rw [ht, hM]; field_simp; ring
    have e3 : 1 + 1 * t = (k + 1 + l / 2) / M := by rw [ht, hM]; field_simp; ring
    have e4 : 1 - 1 * t = (k + l / 2) / M := by rw [ht, hM]; field_simp; ring
    rw [e1, e2, e3, e4, Real.log_div (by positivity) hMpos.ne', Real.log_div (by positivity)
      hMpos.ne', Real.log_div (by positivity) hMpos.ne', Real.log_div (by positivity)
      hMpos.ne'] at key
    simp only [hsdef]
    rw [g1, g2, show ((k + 1 : ℕ) : ℝ) + l / 2 = k + 1 + l / 2 by push_cast; ring]
    linarith
  have hU : ∀ K : ℕ, 1 ≤ K → s K ≤ (1 - l) * Real.log ((1 * K + l / 2) / (1 * K + 0)) := by
    intro K hK
    have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
    have hG := (DLMF.Gamma.Gamma_ratio_bounds hK0 hl0 hl1).1
    have hpos : 0 < Real.Gamma (K + l) := Real.Gamma_pos_of_pos (by positivity)
    have hpos1 : 0 < Real.Gamma (K + 1) := Real.Gamma_pos_of_pos (by positivity)
    rw [lt_div_iff₀ hpos] at hG
    have hlog := Real.log_lt_log (by positivity) hG
    rw [Real.log_mul (by positivity) hpos.ne', Real.log_rpow hK0] at hlog
    simp only [hsdef]
    rw [one_mul, add_zero, Real.log_div (by positivity) hK0.ne']
    nlinarith
  have hlim : Tendsto (fun K : ℕ => (1 - l) * Real.log ((1 * K + l / 2) / (1 * K + 0)))
      atTop (𝓝 0) := by
    simpa using (opIneq_tendsto_log_ratio one_pos (l / 2) 0).const_mul (1 - l)
  have hneg := opIneq_neg_of_strictMono hs hU hlim m
  have hpos : 0 < Real.Gamma (m + l) := Real.Gamma_pos_of_pos (by positivity)
  have hpos1 : 0 < Real.Gamma (m + 1) := Real.Gamma_pos_of_pos (by positivity)
  rw [Real.lt_rpow_iff_log_lt (by positivity) (by positivity), Real.log_div hpos.ne' hpos1.ne']
  simp only [hsdef] at hneg
  linarith


/-- Gamma-ratio bound used for the odd Gegenbauer case: with `N = 2m + 1 + λ`, `0 < λ < 1`,
`(Γ(m + 1 + λ)/Γ(m + 1))² N² < (N/2)^{2λ} (N² + λ(1 - λ))`. -/
theorem opIneq_Gamma_odd {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (m : ℕ) :
    (Real.Gamma (m + 1 + l) / Real.Gamma (m + 1)) ^ 2 * (2 * m + 1 + l) ^ 2 <
      ((2 * m + 1 + l) / 2) ^ (2 * l) * ((2 * m + 1 + l) ^ 2 + l * (1 - l)) := by
  set c := l * (1 - l) with hc
  have hc0 : 0 < c := by positivity
  set s : ℕ → ℝ := fun k => 2 * (Real.log (Real.Gamma (k + 1 + l)) -
      Real.log (Real.Gamma (k + 1))) + 2 * Real.log (2 * k + 1 + l) -
      Real.log ((2 * k + 1 + l) ^ 2 + c) - 2 * l * Real.log ((2 * k + 1 + l) / 2) with hsdef
  have hs : ∀ k, s k < s (k + 1) := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have g1 : Real.log (Real.Gamma (((k + 1 : ℕ) : ℝ) + 1 + l)) =
        Real.log (k + 1 + l) + Real.log (Real.Gamma (k + 1 + l)) := by
      rw [show ((k + 1 : ℕ) : ℝ) + 1 + l = (k + 1 + l) + 1 by push_cast; ring]
      exact opIneq_log_Gamma_succ (by positivity)
    have g2 : Real.log (Real.Gamma (((k + 1 : ℕ) : ℝ) + 1)) =
        Real.log (k + 1) + Real.log (Real.Gamma (k + 1)) := by
      rw [show ((k + 1 : ℕ) : ℝ) + 1 = (k + 1) + 1 by push_cast; ring]
      exact opIneq_log_Gamma_succ (by positivity)
    set N : ℝ := 2 * k + 1 + l with hN
    have hNpos : 0 < N := by positivity
    set b : ℝ := N + 1 with hb
    have hbpos : 0 < b := by positivity
    set t : ℝ := 1 / b with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 / 2 := by
      rw [ht, div_le_div_iff₀ hbpos (by norm_num)]; linarith
    have key := opIneq_logRatio_odd hl0 hl1 ht0 ht1
    have hbne : b ≠ 0 := hbpos.ne'
    have e1 : 1 + l * t = (k + 1 + l) / (b / 2) := by
      rw [ht]; field_simp; rw [hb, hN]; ring
    have e2 : 1 - l * t = (k + 1) / (b / 2) := by
      rw [ht]; field_simp; rw [hb, hN]; ring
    have e3 : 1 + 1 * t = (N + 2) / b := by rw [ht]; field_simp; rw [hb]; ring
    have e4 : 1 - 1 * t = N / b := by rw [ht]; field_simp; rw [hb]; ring
    have e5 : (1 + t) ^ 2 + c * t ^ 2 = ((N + 2) ^ 2 + c) / b ^ 2 := by
      rw [ht]; field_simp; rw [hb]; ring
    have e6 : (1 - t) ^ 2 + c * t ^ 2 = (N ^ 2 + c) / b ^ 2 := by
      rw [ht]; field_simp; rw [hb]; ring
    have hb2 : 0 < b / 2 := by positivity
    rw [← hc, e1, e2, e3, e4, e5, e6, Real.log_div (by positivity) hb2.ne',
      Real.log_div (by positivity) hb2.ne', Real.log_div (by positivity) hbne,
      Real.log_div (by positivity) hbne, Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity)] at key
    simp only [hsdef]
    rw [g1, g2, show 2 * ((k + 1 : ℕ) : ℝ) + 1 + l = N + 2 by push_cast; rw [hN]; ring,
      ← hN, Real.log_div (by positivity) two_ne_zero, Real.log_div (by positivity) two_ne_zero]
    linarith
  have hU : ∀ K : ℕ, 1 ≤ K →
      s K ≤ 2 * l * Real.log ((2 * K + (2 + 2 * l)) / (2 * K + (1 + l))) := by
    intro K hK
    have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
    have hG := (DLMF.Gamma.Gamma_ratio_bounds (x := K + l) (by positivity)
      (show 0 < 1 - l by linarith) (by linarith)).2
    rw [show (K : ℝ) + l + 1 = K + 1 + l by ring, show (K : ℝ) + l + (1 - l) = K + 1 by ring,
      show 1 - (1 - l) = l by ring] at hG
    have hpos : 0 < Real.Gamma (K + 1 + l) := Real.Gamma_pos_of_pos (by positivity)
    have hpos1 : 0 < Real.Gamma (K + 1) := Real.Gamma_pos_of_pos (by positivity)
    have hlog := Real.log_lt_log (by positivity) hG
    rw [Real.log_div hpos.ne' hpos1.ne', Real.log_rpow (by positivity)] at hlog
    have hN2 : 2 * Real.log (2 * K + 1 + l) ≤ Real.log ((2 * K + 1 + l) ^ 2 + c) := by
      have := Real.log_pow 2 (x := 2 * (K : ℝ) + 1 + l)
      push_cast at this
      rw [← this]
      exact Real.log_le_log (by positivity) (by linarith)
    simp only [hsdef]
    rw [show (2 * (K : ℝ) + (2 + 2 * l)) / (2 * K + (1 + l)) =
        (K + 1 + l) / ((2 * K + 1 + l) / 2) by field_simp; ring]
    have l1 : Real.log ((K + 1 + l) / ((2 * K + 1 + l) / 2)) =
        Real.log (K + 1 + l) - Real.log ((2 * K + 1 + l) / 2) :=
      Real.log_div (by positivity) (by positivity)
    rw [l1]
    nlinarith
  have hlim : Tendsto (fun K : ℕ => 2 * l * Real.log ((2 * K + (2 + 2 * l)) / (2 * K + (1 + l))))
      atTop (𝓝 0) := by
    simpa using (opIneq_tendsto_log_ratio two_pos (2 + 2 * l) (1 + l)).const_mul (2 * l)
  have hneg := opIneq_neg_of_strictMono hs hU hlim m
  have hpos : 0 < Real.Gamma (m + 1 + l) := Real.Gamma_pos_of_pos (by positivity)
  have hpos1 : 0 < Real.Gamma (m + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hN : (0 : ℝ) < 2 * m + 1 + l := by positivity
  rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_div hpos.ne' hpos1.ne', Real.log_rpow (by positivity)]
  simp only [hsdef] at hneg
  push_cast at hneg ⊢
  linarith


/-- **Sonine-type bound for the Gegenbauer equation** with `0 < λ < 1`. If `y` solves
`(1 - x²) y'' - (2λ + 1) x y' + n(n + 2λ) y = 0`, then on `(-1, 1)`
`(1 - x²)^λ y(x)² ≤ y(0)² + y'(0)² / ((n + λ)² + λ(1 - λ))`. In the variable `θ = arccos x`
this is the monotonicity of `u² + u'²/Q` for `u = sin^λ θ · y(cos θ)`,
`Q = (n + λ)² + λ(1 - λ)/sin² θ` (Lorch's argument for DLMF 18.14.7). -/
theorem opIneq_gegenbauer_sonine {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {n : ℕ}
    {y y' y'' : ℝ → ℝ} (hy : ∀ x, HasDerivAt y (y' x) x) (hy' : ∀ x, HasDerivAt y' (y'' x) x)
    (hode : ∀ x, (1 - x ^ 2) * y'' x - (2 * l + 1) * x * y' x + n * (n + 2 * l) * y x = 0)
    {x : ℝ} (hx : |x| < 1) :
    (1 - x ^ 2) ^ l * y x ^ 2 ≤ y 0 ^ 2 + y' 0 ^ 2 / ((n + l) ^ 2 + l * (1 - l)) := by
  set c := l * (1 - l) with hc
  have hc0 : 0 < c := by positivity
  set N : ℝ := n + l with hN
  let E : ℝ → ℝ := fun t => l * t * y t - (1 - t ^ 2) * y' t
  let D : ℝ → ℝ := fun t => N ^ 2 * (1 - t ^ 2) + c
  let f : ℝ → ℝ := fun t => (1 - t ^ 2) ^ l * (y t ^ 2 + E t ^ 2 / D t)
  let f' : ℝ → ℝ := fun t => -(2 * l * (1 - l) * t * ((1 - t ^ 2) ^ l / (1 - t ^ 2)) *
    (E t ^ 2 / D t ^ 2))
  have hderiv : ∀ t, |t| < 1 → HasDerivAt f (f' t) t := by
    intro t ht
    have h1 : 0 < 1 - t ^ 2 := by
      have := abs_lt.mp ht; nlinarith
    have hD : 0 < D t := by
      have : 0 ≤ N ^ 2 * (1 - t ^ 2) := by positivity
      simp only [D]; linarith
    have hW : HasDerivAt (fun t => (1 - t ^ 2) ^ l)
        (-(2 * t) * l * ((1 - t ^ 2) ^ l / (1 - t ^ 2))) t := by
      have h := ((hasDerivAt_pow 2 t).const_sub 1).rpow_const (p := l) (Or.inl h1.ne')
      rw [Real.rpow_sub_one h1.ne'] at h
      convert h using 1
      push_cast; ring
    have hE : HasDerivAt E (l * y t + l * t * y' t + 2 * t * y' t - (1 - t ^ 2) * y'' t) t := by
      have := (((hasDerivAt_id' t).const_mul l).mul (hy t)).sub
        (((hasDerivAt_pow 2 t).const_sub 1).mul (hy' t))
      convert this using 1
      push_cast; ring
    have hDd : HasDerivAt D (N ^ 2 * (-(2 * t))) t := by
      have := (((hasDerivAt_pow 2 t).const_sub 1).const_mul (N ^ 2)).add_const c
      convert this using 1
      push_cast; ring
    have hall := hW.mul (((hy t).pow 2).add ((hE.pow 2).div hDd hD.ne'))
    refine hall.congr_deriv ?_
    have hy2 : y'' t = ((2 * l + 1) * t * y' t - n * (n + 2 * l) * y t) / (1 - t ^ 2) := by
      field_simp; linear_combination hode t
    simp only [f', E, D, Pi.add_apply, Pi.pow_apply, Pi.div_apply]
    rw [hy2]
    simp only [D] at hD
    field_simp
    rw [hc, hN]
    ring
  have hf'nonpos : ∀ t, 0 ≤ t → t < 1 → f' t ≤ 0 := by
    intro t ht0 ht1
    have h1 : 0 < 1 - t ^ 2 := by nlinarith
    have : 0 ≤ 2 * l * (1 - l) * t * ((1 - t ^ 2) ^ l / (1 - t ^ 2)) * (E t ^ 2 / D t ^ 2) := by
      have : 0 < 1 - l := by linarith
      positivity
    simp only [f']; linarith
  have hf'nonneg : ∀ t, -1 < t → t ≤ 0 → 0 ≤ f' t := by
    intro t ht0 ht1
    have h1 : 0 < 1 - t ^ 2 := by nlinarith
    have : 0 ≤ 2 * l * (1 - l) * (-t) * ((1 - t ^ 2) ^ l / (1 - t ^ 2)) * (E t ^ 2 / D t ^ 2) := by
      have : 0 < 1 - l := by linarith
      have : 0 ≤ -t := by linarith
      positivity
    simp only [f']; linarith
  have hfx : f x ≤ f 0 := by
    obtain ⟨hxl, hxr⟩ := abs_lt.mp hx
    rcases le_total 0 x with h0 | h0
    · have hanti : AntitoneOn f (Icc 0 x) := by
        refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') (convex_Icc 0 x)
          (fun t ht => (hderiv t (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).continuousAt.continuousWithinAt)
          (fun t ht => ?_) (fun t ht => ?_)
        · rw [interior_Icc] at ht
          exact (hderiv t (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).hasDerivWithinAt
        · rw [interior_Icc] at ht
          exact hf'nonpos t ht.1.le (by linarith [ht.2])
      exact hanti ⟨le_rfl, h0⟩ ⟨h0, le_rfl⟩ h0
    · have hmono : MonotoneOn f (Icc x 0) := by
        refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := f') (convex_Icc x 0)
          (fun t ht => (hderiv t (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).continuousAt.continuousWithinAt)
          (fun t ht => ?_) (fun t ht => ?_)
        · rw [interior_Icc] at ht
          exact (hderiv t (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).hasDerivWithinAt
        · rw [interior_Icc] at ht
          exact hf'nonneg t (by linarith [ht.1]) ht.2.le
      exact hmono ⟨le_rfl, h0⟩ ⟨h0, le_rfl⟩ h0
  have hf0 : f 0 = y 0 ^ 2 + y' 0 ^ 2 / ((n + l) ^ 2 + l * (1 - l)) := by
    simp only [f, E, D]
    norm_num
    rw [hN, hc]
  have hlow : (1 - x ^ 2) ^ l * y x ^ 2 ≤ f x := by
    have h1 : 0 < 1 - x ^ 2 := by have := abs_lt.mp hx; nlinarith
    have hD : 0 < D x := by
      have : 0 ≤ N ^ 2 * (1 - x ^ 2) := by positivity
      simp only [D]; linarith
    have : 0 ≤ E x ^ 2 / D x := by positivity
    have hW : 0 ≤ (1 - x ^ 2) ^ l := by positivity
    simp only [f]
    nlinarith
  linarith

end DLMF.OrthogonalPolynomials
