/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.BarnesResidue

/-!
# Closing a Mellin–Barnes contour: vertical-line integrals as residue series

Let `F` be meromorphic to the left of the line `Re s = c₀`, with one simple pole `p n` in each
strip `c (n+1) < Re s < c n` of a decreasing sequence of lines `c n`. Write
`F s = φ n s / (s - p n)` on the `n`-th closed strip, with `φ n` holomorphic there. If `F` is
integrable on every line, its integrals over horizontal cross-sections of every strip tend to `0`
at `±i∞`, and the line integrals tend to `0` as `n → ∞`, then

`∫ F(c₀ + iy) dy = 2π ∑ₙ φ n (p n)`,

the sum of the residues (times `2π`; the line integrals carry `dy`, not `ds = i dy`). The series
converges as the limit of its partial sums; it is a `HasSum` when the residue series is known
to be summable. The proof iterates `Complex.barnesRes_vertical_shift`.

For the poles of `Γ(s + a)` at `s = -n - a` we also record the factorization
`Γ(s + a) = Γ(s + a + n + 1) / ∏_{j ≤ n} (s + a + j)` and the residue
`(-1)^n / n!`. Bounds for `Γ` on vertical lines (`|Γ(x+iy)| ≤ C (1+|y|)^K e^{-π|y|/2}`) and for
`1/sin(πs)` are in `DLMF.Gamma.VerticalBounds` and `Complex.barnesRes_sin_lower_line`,
`Complex.barnesRes_sin_lower_far`.

## Main results

* `Complex.mbSeries_sub_eq_sum`: the finite contour shift across `N` poles.
* `Complex.mbSeries_tendsto`: the line integral as the limit of the partial residue sums.
* `Complex.mbSeries_hasSum`: the same with a `HasSum` conclusion for a summable residue series.
* `Complex.mbSeries_Gamma_mul_eq_div`, `Complex.mbSeries_Gamma_residue`: the residue data of
  `G(s) Γ(s + a)` at `s = -n - a`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Real intervalIntegral

open scoped Topology Interval

namespace Complex

/-- Hypotheses for closing a vertical-line integral to the left across simple poles: lines
`c n`, poles `p n` with `c (n+1) < Re (p n) < c n`, and holomorphic numerators `φ n` with
`F s = φ n s / (s - p n)` on the `n`-th closed strip. -/
structure MBSeriesData (F : ℂ → ℂ) (c : ℕ → ℝ) (p : ℕ → ℂ) (φ : ℕ → ℂ → ℂ) : Prop where
  /-- the pole `p n` lies strictly inside the strip `c (n+1) < Re s < c n`. -/
  lt_re : ∀ n, c (n + 1) < (p n).re
  re_lt : ∀ n, (p n).re < c n
  /-- the numerator is holomorphic on the closed strip. -/
  differentiableOn : ∀ n, DifferentiableOn ℂ (φ n) (re ⁻¹' Icc (c (n + 1)) (c n))
  /-- the factorization of `F` on the closed strip. -/
  eq_div : ∀ n, ∀ s ∈ re ⁻¹' Icc (c (n + 1)) (c n), s ≠ p n → F s = φ n s / (s - p n)
  /-- integrability of `F` on every line. -/
  integrable : ∀ n, Integrable fun y : ℝ => F (c n + y * I)
  /-- the horizontal cross-section integrals vanish at `+i∞`. -/
  top : ∀ n, Tendsto (fun T : ℝ => ∫ x in c (n + 1)..c n, F (x + T * I)) atTop (𝓝 0)
  /-- the horizontal cross-section integrals vanish at `-i∞`. -/
  bot : ∀ n, Tendsto (fun T : ℝ => ∫ x in c (n + 1)..c n, F (x + T * I)) atBot (𝓝 0)

/-- One step of the shift: crossing the `n`-th pole. -/
theorem mbSeries_step {F : ℂ → ℂ} {c : ℕ → ℝ} {p : ℕ → ℂ} {φ : ℕ → ℂ → ℂ}
    (h : MBSeriesData F c p φ) (n : ℕ) :
    (∫ y : ℝ, F (c n + y * I)) - ∫ y : ℝ, F (c (n + 1) + y * I) = 2 * π * φ n (p n) := by
  have hmem : ∀ x y : ℝ, x ∈ Icc (c (n + 1)) (c n) →
      ((x : ℂ) + y * I) ∈ re ⁻¹' Icc (c (n + 1)) (c n) := fun x y hx => by simpa using hx
  have hne_line : ∀ x y : ℝ, x ≠ (p n).re → (x : ℂ) + y * I ≠ p n := fun x y hx he => hx (by
    have := congrArg re he; simpa using this)
  have hne_horiz : ∀ x T : ℝ, T ≠ (p n).im → (x : ℂ) + T * I ≠ p n := fun x T hT he => hT (by
    have := congrArg im he; simpa using this)
  have hlo : c (n + 1) ≤ c n := (h.lt_re n).le.trans (h.re_lt n).le
  have hline : ∀ x : ℝ, x ∈ Icc (c (n + 1)) (c n) → x ≠ (p n).re →
      (fun y : ℝ => φ n (x + y * I) / (x + y * I - p n)) = fun y : ℝ => F (x + y * I) :=
    fun x hx hxp => funext fun y => (h.eq_div n _ (hmem x y hx) (hne_line x y hxp)).symm
  have h1 := hline (c (n + 1)) ⟨le_rfl, hlo⟩ (h.lt_re n).ne
  have h2 := hline (c n) ⟨hlo, le_rfl⟩ (h.re_lt n).ne'
  have hH : ∀ T : ℝ, T ≠ (p n).im →
      (∫ x in c (n + 1)..c n, φ n (x + T * I) / (x + T * I - p n)) =
        ∫ x in c (n + 1)..c n, F (x + T * I) := by
    intro T hT
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hlo] at hx
    exact (h.eq_div n _ (hmem x T hx) (hne_horiz x T hT)).symm
  have key := barnesRes_vertical_shift (h.lt_re n) (h.re_lt n) (h.differentiableOn n)
    (by rw [h1]; exact h.integrable (n + 1)) (by rw [h2]; exact h.integrable n)
    ((h.top n).congr' (by
      filter_upwards [eventually_gt_atTop (p n).im] with T hT; exact (hH T hT.ne').symm))
    ((h.bot n).congr' (by
      filter_upwards [eventually_lt_atBot (p n).im] with T hT; exact (hH T hT.ne).symm))
  rwa [h1, h2] at key

/-- **Finite contour shift.** Moving the line from `c 0` to `c N` crosses the poles
`p 0, …, p (N-1)`. -/
theorem mbSeries_sub_eq_sum {F : ℂ → ℂ} {c : ℕ → ℝ} {p : ℕ → ℂ} {φ : ℕ → ℂ → ℂ}
    (h : MBSeriesData F c p φ) (N : ℕ) :
    (∫ y : ℝ, F (c 0 + y * I)) - ∫ y : ℝ, F (c N + y * I) =
      ∑ n ∈ Finset.range N, 2 * π * φ n (p n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih, ← mbSeries_step h N]
    ring

/-- **Closing the contour.** If the line integrals tend to `0` as the line moves to the left,
the integral on the first line is the limit of the partial sums of `2π` times the residues. -/
theorem mbSeries_tendsto {F : ℂ → ℂ} {c : ℕ → ℝ} {p : ℕ → ℂ} {φ : ℕ → ℂ → ℂ}
    (h : MBSeriesData F c p φ)
    (hlim : Tendsto (fun N : ℕ => ∫ y : ℝ, F (c N + y * I)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, 2 * π * φ n (p n)) atTop
      (𝓝 (∫ y : ℝ, F (c 0 + y * I))) := by
  have := (tendsto_const_nhds (x := ∫ y : ℝ, F (c 0 + y * I))).sub hlim
  rw [sub_zero] at this
  exact this.congr fun N => mbSeries_sub_eq_sum h N

/-- **Closing the contour, summable form.** -/
theorem mbSeries_hasSum {F : ℂ → ℂ} {c : ℕ → ℝ} {p : ℕ → ℂ} {φ : ℕ → ℂ → ℂ}
    (h : MBSeriesData F c p φ)
    (hlim : Tendsto (fun N : ℕ => ∫ y : ℝ, F (c N + y * I)) atTop (𝓝 0))
    (hs : Summable fun n => φ n (p n)) :
    HasSum (fun n => 2 * π * φ n (p n)) (∫ y : ℝ, F (c 0 + y * I)) := by
  have hs' : Summable fun n => 2 * π * φ n (p n) := hs.mul_left _
  have h1 := hs'.hasSum
  rwa [tendsto_nhds_unique h1.tendsto_sum_nat (mbSeries_tendsto h hlim)] at h1

/-- Factorization of `G(s) Γ(s + a)` at the pole `s = -n - a`: if `s + a + j ≠ 0` for `j ≤ n`,
then `G s Γ(s + a) = (G s Γ(s + a + n + 1) / ∏_{j<n} (s + a + j)) / (s - (-n - a))`. -/
theorem mbSeries_Gamma_mul_eq_div (G : ℂ → ℂ) (a : ℂ) (n : ℕ) {s : ℂ}
    (hs : ∀ j : ℕ, j ≤ n → s + a + j ≠ 0) :
    G s * Gamma (s + a) =
      G s * Gamma (s + a + n + 1) / (∏ j ∈ Finset.range n, (s + a + j)) / (s - (-n - a)) := by
  have hG := barnesRes_Gamma_add_nat_succ (s + a) n hs
  have hP : ∏ j ∈ Finset.range n, (s + a + j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => hs j (Finset.mem_range.mp hj).le
  rw [hG, Finset.prod_range_succ, show s - (-n - a) = s + a + n by ring]
  have hn' : s + a + (n : ℂ) ≠ 0 := hs n le_rfl
  field_simp

/-- The residue numerator of `G(s) Γ(s + a)` at `s = -n - a` equals `(-1)^n G(-n-a) / n!`. -/
theorem mbSeries_Gamma_residue (G : ℂ → ℂ) (a : ℂ) (n : ℕ) :
    G (-n - a) * Gamma ((-n - a) + a + n + 1) / ∏ j ∈ Finset.range n, ((-n - a) + a + j) =
      (-1) ^ n * G (-n - a) / n.factorial := by
  have h1 : (-n - a) + a + n + 1 = (1 : ℂ) := by ring
  have h2 : ∏ j ∈ Finset.range n, ((-n - a) + a + (j : ℂ)) = (-1) ^ n * n.factorial := by
    rw [← barnesRes_prod_sub_nat]
    exact Finset.prod_congr rfl fun j _ => by ring
  rw [h1, Gamma_one, h2]
  have : ((n.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h3 : ((-1 : ℂ)) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  rw [← pow_mul, show n * 2 = 2 * n by ring, pow_mul]
  simp

end Complex
