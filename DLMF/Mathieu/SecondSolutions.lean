/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Properties
public import DLMF.Mathieu.FourierSeries

/-!
# Second solutions `fe_n`, `ge_n` (DLMF §28.5)

`fe_n(z, q) = mathieuFe n z q` and `ge_n(z, q) = mathieuGe n z q` (real `q`) are defined in
`DLMF.Mathieu.Basic` as the odd solution for `a = a_n(q)` and the even solution for
`a = b_n(q)`, normalized by 28.5.5 with `fe_n'(0, q) > 0`, `ge_n(0, q) > 0` (equivalent to DLMF's
sign rule `C_n f_n → sin nz`, `S_n g_n → cos nz` as `q → 0`), together with the factors
`C_n(q) = mathieuFeC n q`, `S_n(q) = mathieuGeS n q` and the periodic parts
`f_n = mathieuFeF n z q`, `g_n = mathieuGeG n z q`.

**Correction (28.5.6, second relation).** With DLMF's own sign rule for `C_n`, `S_n`, the
relation is `C_{2m+1}(-q) = -S_{2m+1}(q)`, not `C_{2m+1}(-q) = S_{2m+1}(q)`: numerically
(direct integration of 28.2.1) `C_1(-1) = -0.95506…`, `S_1(1) = 0.95506…`,
`C_3(-1) = -0.0051465…`, `S_3(1) = 0.0051465…`; analytically, `ge_{2m+1}(π/2 - z, q)` is an odd
multiple `c fe_{2m+1}(z, -q)` plus a multiple of `ce_{2m+1}(z, -q)` with
`sign c = -sign ge'_{2m+1}(π/2, q) = (-1)^m`, which gives `C_{2m+1}(-q) S_{2m+1}(q) < 0`.

**Remark (`n = 0`).** For `n = 0` the normalization 28.5.5 makes `fe_0'(0, q) ≈ 2/|q|` blow up as
`q → 0` (numerically `fe_0'(0, 0.01) = 201.0…`), so 28.5.5 and `fe_0(z, 0) = z` (28.5.7) are not
connected by continuity; `mathieuFe 0 z 0 = z` by definition.
-/

@[expose] public noncomputable section

open Complex Set Filter ComplexConjugate
open scoped Topology Real

namespace DLMF.Mathieu

/-- The Wronskian of two solutions of the same Mathieu equation is constant. -/
theorem IsMathieuSolution.wronskian_eq {a q : ℂ} {u v : ℂ → ℂ} (hu : IsMathieuSolution a q u)
    (hv : IsMathieuSolution a q v) (z w : ℂ) :
    u z * deriv v z - deriv u z * v z = u w * deriv v w - deriv u w * v w := by
  have hW : ∀ z, HasDerivAt (fun z => u z * deriv v z - deriv u z * v z) 0 z := by
    intro z
    have := ((hu.differentiable z).hasDerivAt.mul (hv.hasDerivAt_deriv z)).sub
      ((hu.hasDerivAt_deriv z).mul (hv.differentiable z).hasDerivAt)
    convert this using 1; ring
  exact is_const_of_deriv_eq_zero (fun z => (hW z).differentiableAt) (fun z => (hW z).deriv) z w

/-! ### Ince's theorem: no coexistence of periodic solutions -/

/-- A two-step recurrence `(e_m) x_{m+2} = q (x_m + x_{m+4})` with `q ≠ 0` propagates two
consecutive zeros `x_r = x_{r+2} = 0` upwards. -/
theorem p2x_rec_zero {q : ℂ} (hq : q ≠ 0) {e x : ℕ → ℂ}
    (hrec : ∀ m, e m * x (m + 2) = q * (x m + x (m + 4))) {r : ℕ} (h0 : x r = 0)
    (h2 : x (r + 2) = 0) : ∀ j, x (r + 2 * j) = 0 := by
  have key : ∀ j, x (r + 2 * j) = 0 ∧ x (r + 2 * j + 2) = 0 := by
    intro j
    induction j with
    | zero => exact ⟨h0, h2⟩
    | succ j ih =>
      refine ⟨by rw [show r + 2 * (j + 1) = r + 2 * j + 2 by ring]; exact ih.2, ?_⟩
      have := hrec (r + 2 * j)
      rw [ih.1, ih.2, show r + 2 * j + 4 = r + 2 * (j + 1) + 2 by ring] at this
      simpa [hq] using this.symm
  exact fun j => (key j).1

/-- The Casoratian `x_m y_{m+2} - x_{m+2} y_m` of two solutions of the recurrence
`e_m x_{m+2} = q (x_m + x_{m+4})` is invariant under `m ↦ m + 2`. -/
theorem p2x_casoratian {q : ℂ} (hq : q ≠ 0) {e x y : ℕ → ℂ}
    (hx : ∀ m, e m * x (m + 2) = q * (x m + x (m + 4)))
    (hy : ∀ m, e m * y (m + 2) = q * (y m + y (m + 4))) (m : ℕ) :
    x (m + 2) * y (m + 4) - x (m + 4) * y (m + 2) = x m * y (m + 2) - x (m + 2) * y m := by
  have h := hx m
  have h' := hy m
  apply mul_left_cancel₀ hq
  linear_combination y (m + 2) * h - x (m + 2) * h'

/-- If two sequences tend to `0` and solve the recurrence, their Casoratian vanishes. -/
theorem p2x_casoratian_eq_zero {q : ℂ} (hq : q ≠ 0) {e x y : ℕ → ℂ}
    (hx : ∀ m, e m * x (m + 2) = q * (x m + x (m + 4)))
    (hy : ∀ m, e m * y (m + 2) = q * (y m + y (m + 4)))
    (hx0 : Tendsto x atTop (𝓝 0)) (hy0 : Tendsto y atTop (𝓝 0)) (r : ℕ) :
    x r * y (r + 2) - x (r + 2) * y r = 0 := by
  set D : ℕ → ℂ := fun m => x m * y (m + 2) - x (m + 2) * y m
  have hD : ∀ j, D (r + 2 * j) = D r := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← ih]
      have := p2x_casoratian hq hx hy (r + 2 * j)
      simp only [D]
      rw [show r + 2 * (j + 1) = r + 2 * j + 2 by ring,
        show r + 2 * j + 2 + 2 = r + 2 * j + 4 by ring]
      exact this
  have hlim : Tendsto D atTop (𝓝 0) := by
    have h2 : Tendsto (fun m => m + 2) atTop atTop := tendsto_add_atTop_nat 2
    have := (hx0.mul (hy0.comp h2)).sub ((hx0.comp h2).mul hy0)
    simpa using this
  have hlim' : Tendsto (fun j => D (r + 2 * j)) atTop (𝓝 0) :=
    hlim.comp (tendsto_atTop_mono (fun j => show id j ≤ r + 2 * j by simp only [id]; omega)
      tendsto_id)
  simp only [hD] at hlim'
  exact tendsto_nhds_unique tendsto_const_nhds hlim'


/-- Shift of a sum: if each term at `w` is `s` times the term at `z`, so is the sum. -/
theorem p2x_hasSum_shift {F : ℂ → ℂ} {t : ℕ → ℂ → ℂ} (h : ∀ z, HasSum (fun m => t m z) (F z))
    {s z w : ℂ} (ht : ∀ m, t m w = s * t m z) : F w = s * F z := by
  have h2 := (h z).mul_left s
  rw [← funext ht] at h2
  exact (h w).unique h2

/-- **No coexistence** (Ince): for `q ≠ 0` the basic solutions `w_I`, `w_II` are not both
`2π`-periodic. -/
theorem p2x_not_coexist {a q : ℂ} (hq : q ≠ 0)
    (hI : ∀ z, mathieuWI a q (z + 2 * π) = mathieuWI a q z)
    (hII : ∀ z, mathieuWII a q (z + 2 * π) = mathieuWII a q z) : False := by
  obtain ⟨h1, h10, h11⟩ := mathieuWI_spec a q
  obtain ⟨h2, h20, h21⟩ := mathieuWII_spec a q
  have hpi := mathieuWI_pi_eq_deriv_mathieuWII_pi a q
  set f := mathieuWI a q with hf
  set g := mathieuWII a q with hg
  let α : ℤ → ℂ := fun k => ∫ x in (0 : ℝ)..2 * π, f x * Complex.cos (k * x)
  let β : ℤ → ℂ := fun k => ∫ x in (0 : ℝ)..2 * π, g x * Complex.sin (k * x)
  have hα : ∀ k : ℤ, (a - (k : ℂ) ^ 2) * α k = q * (α (k - 2) + α (k + 2)) :=
    fun k => p1a2_cos_rec h1 hI k
  have hβ : ∀ k : ℤ, (a - (k : ℂ) ^ 2) * β k = q * (β (k - 2) + β (k + 2)) :=
    fun k => p1a2_sin_rec h2 hII k
  have hαneg : ∀ k : ℤ, α (-k) = α k := by
    intro k; simp only [α]; push_cast; simp [neg_mul, Complex.cos_neg]
  have hβneg : ∀ k : ℤ, β (-k) = -β k := by
    intro k; simp only [β]; push_cast
    simp [neg_mul, Complex.sin_neg, intervalIntegral.integral_neg]
  have hβ0 : β 0 = 0 := by simp [β]
  let x : ℕ → ℂ := fun m => α m
  let y : ℕ → ℂ := fun m => β m
  let e : ℕ → ℂ := fun m => a - ((((m + 2 : ℕ) : ℤ) : ℂ)) ^ 2
  have hrw1 : ∀ m : ℕ, ((m + 2 : ℕ) : ℤ) - 2 = (m : ℤ) := fun m => by push_cast; ring
  have hrw2 : ∀ m : ℕ, ((m + 2 : ℕ) : ℤ) + 2 = ((m + 4 : ℕ) : ℤ) := fun m => by push_cast; ring
  have hx : ∀ m, e m * x (m + 2) = q * (x m + x (m + 4)) := by
    intro m; have := hα ((m + 2 : ℕ) : ℤ); rw [hrw1, hrw2] at this; exact this
  have hy : ∀ m, e m * y (m + 2) = q * (y m + y (m + 4)) := by
    intro m; have := hβ ((m + 2 : ℕ) : ℤ); rw [hrw1, hrw2] at this; exact this
  have hxe : ∀ m : ℕ, (∫ t in (0 : ℝ)..2 * π, f t * Complex.cos ((m : ℂ) * t)) = x m := by
    intro m; simp [x, α]
  have hye : ∀ m : ℕ, (∫ t in (0 : ℝ)..2 * π, g t * Complex.sin ((m : ℂ) * t)) = y m := by
    intro m; simp [y, β]
  have hx0 : Tendsto x atTop (𝓝 0) := by
    have := (p1a2_summable_cos_coeff h1.differentiable hI (mathieuWI_neg a q)).tendsto_atTop_zero
    simp only [hxe] at this
    exact tendsto_zero_iff_norm_tendsto_zero.mpr this
  have hy0 : Tendsto y atTop (𝓝 0) := by
    have := (p1a2_summable_sin_coeff h2.differentiable hII (mathieuWII_neg a q)).tendsto_atTop_zero
    simp only [hye] at this
    exact tendsto_zero_iff_norm_tendsto_zero.mpr this
  -- low indices
  have hk0 : a * x 0 = q * (2 * x 2) := by
    have := hα 0
    have e2 : α (0 - 2) = α 2 := by rw [show (0 : ℤ) - 2 = -2 by norm_num, hαneg]
    rw [e2] at this
    simp only [x]; push_cast at this ⊢; linear_combination this
  have hk1x : q * x 3 = (a - 1) * x 1 - q * x 1 := by
    have := hα 1
    have e2 : α (1 - 2) = α 1 := by rw [show (1 : ℤ) - 2 = -1 by norm_num, hαneg]
    rw [e2] at this
    simp only [x]; push_cast at this ⊢; linear_combination -this
  have hk1y : q * y 3 = (a - 1) * y 1 + q * y 1 := by
    have := hβ 1
    have e2 : β (1 - 2) = -β 1 := by rw [show (1 : ℤ) - 2 = -1 by norm_num, hβneg]
    rw [e2] at this
    simp only [y]; push_cast at this ⊢; linear_combination -this
  have hy0' : y 0 = 0 := by simpa [y] using hβ0
  have hD0 : x 0 * y 2 = 0 := by
    have := p2x_casoratian_eq_zero hq hx hy hx0 hy0 0
    rw [hy0'] at this; simpa using this
  have hD1 : x 1 * y 1 = 0 := by
    have := p2x_casoratian_eq_zero hq hx hy hx0 hy0 1
    have h2q : (2 * q) * (x 1 * y 1) = 0 := by
      linear_combination q * this - x 1 * hk1y + y 1 * hk1x
    exact (mul_eq_zero.mp h2q).resolve_left (mul_ne_zero two_ne_zero hq)
  -- vanishing of the even / odd coefficients
  have evx : x 0 = 0 → ∀ j, x (2 * j) = 0 := by
    intro h j
    have h2 : x 2 = 0 := by
      rw [h, mul_zero] at hk0
      exact ((mul_eq_zero.mp hk0.symm).resolve_left hq |> mul_eq_zero.mp).resolve_left two_ne_zero
    simpa using p2x_rec_zero hq hx h h2 j
  have evy : y 2 = 0 → ∀ j, y (2 * j) = 0 := by
    intro h j; simpa using p2x_rec_zero hq hy hy0' h j
  have odx : x 1 = 0 → ∀ j, x (2 * j + 1) = 0 := by
    intro h j
    have h3 : x 3 = 0 := by
      rw [h] at hk1x; simpa [hq] using hk1x
    simpa [add_comm] using p2x_rec_zero hq hx (r := 1) h h3 j
  have ody : y 1 = 0 → ∀ j, y (2 * j + 1) = 0 := by
    intro h j
    have h3 : y 3 = 0 := by
      rw [h] at hk1y; simpa [hq] using hk1y
    simpa [add_comm] using p2x_rec_zero hq hy (r := 1) h h3 j
  -- the Fourier series
  have sf : ∀ z, HasSum (fun m : ℕ => (if m = 0 then 1 / (2 * π) else 1 / π : ℂ) * x m *
      Complex.cos (m * z)) (f z) := by
    intro z; have := p1a2_hasSum_cos h1.differentiable hI (mathieuWI_neg a q) z
    simpa only [hxe] using this
  have sg : ∀ z, HasSum (fun m : ℕ => (1 / π : ℂ) * y m * Complex.sin (m * z)) (g z) := by
    intro z; have := p1a2_hasSum_sin h2.differentiable hII (mathieuWII_neg a q) z
    simpa only [hye] using this
  have sg' := p1a2_hasSum_deriv_sin h2.differentiable hII (mathieuWII_neg a q)
  simp only [hye] at sg'
  rcases mul_eq_zero.mp hD0 with hA | hA <;> rcases mul_eq_zero.mp hD1 with hB | hB
  · -- all `x` vanish
    have hz : ∀ m, x m = 0 := fun m => by
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
      · exact evx hA j
      · exact odx hB j
    have h0 := sf 0
    simp only [hz, mul_zero, zero_mul] at h0
    have := h0.unique hasSum_zero
    rw [h10] at this; exact one_ne_zero this
  · -- even `x`, odd `y` vanish
    have hfpi : f π = -1 * f 0 := p2x_hasSum_shift sf (fun m => by
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
      · simp [evx hA j]
      · rw [show ((2 * j + 1 : ℕ) : ℂ) * π = ((2 * j + 1 : ℕ) : ℂ) * (0 + π) by ring,
          p1a2_cos_odd_add_pi]; simp)
    have hgp : ∀ z, g (z + π) = 1 * g z := fun z => p2x_hasSum_shift sg (fun m => by
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
      · rw [p1a2_sin_even_add_pi]; ring
      · simp [ody hB j])
    have hd : deriv g π = deriv g 0 := by
      have := deriv_comp_add_const (f := g) (a := (π : ℂ)) (x := 0)
      simp only [hgp, one_mul, zero_add] at this
      exact this.symm
    rw [h10, hpi, hd, h21] at hfpi; norm_num at hfpi
  · -- odd `x`, even `y` vanish
    have hfpi : f π = 1 * f 0 := p2x_hasSum_shift sf (fun m => by
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
      · rw [show ((2 * j : ℕ) : ℂ) * π = ((2 * j : ℕ) : ℂ) * (0 + π) by ring,
          p1a2_cos_even_add_pi]; ring
      · simp [odx hB j])
    have hgp : ∀ z, g (z + π) = -1 * g z := fun z => p2x_hasSum_shift sg (fun m => by
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
      · simp [evy hA j]
      · rw [p1a2_sin_odd_add_pi]; ring)
    have hd : deriv g π = -deriv g 0 := by
      have := deriv_comp_add_const (f := g) (a := (π : ℂ)) (x := 0)
      simp only [hgp, zero_add] at this
      rw [← this]
      simp
    rw [h10, hpi, hd, h21] at hfpi; norm_num at hfpi
  · -- all `y` vanish
    have hz : ∀ m, y m = 0 := fun m => by
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
      · exact evy hA j
      · exact ody hB j
    have h0 := sg'
    simp only [hz, mul_zero] at h0
    have := h0.unique hasSum_zero
    rw [h21] at this; exact one_ne_zero this


/-- Two solutions with vanishing Wronskian at `0`, the first nontrivial, are proportional. -/
theorem p2x_eq_const_mul_of_wronskian {a q : ℂ} {w v : ℂ → ℂ} (hw : IsMathieuSolution a q w)
    (hw0 : w ≠ 0) (hv : IsMathieuSolution a q v)
    (hW : w 0 * deriv v 0 - deriv w 0 * v 0 = 0) : ∃ c : ℂ, v = fun z => c * w z := by
  have hwc := congrFun hw.eq_combination
  have hvc := congrFun hv.eq_combination
  set w0 := w 0
  set w1 := deriv w 0
  set v0 := v 0
  set v1 := deriv v 0
  by_cases h0 : w0 = 0
  · have h1 : w1 ≠ 0 := by
      rintro h1
      exact hw0 (funext fun z => by rw [hwc z, h0, h1]; simp)
    have hv0 : v0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at hW
      exact (mul_eq_zero.mp hW).resolve_left h1
    refine ⟨v1 / w1, funext fun z => ?_⟩
    rw [hvc z, hwc z, h0, hv0]
    field_simp
    ring
  · refine ⟨v0 / w0, funext fun z => ?_⟩
    rw [hvc z, hwc z]
    rw [div_mul_eq_mul_div, eq_div_iff h0]
    linear_combination (mathieuWII a q z) * hW

/-- Two solutions with nonvanishing Wronskian `W` at `0` span the solutions:
`u = ((u(0) v'(0) - u'(0) v(0)) w + (w(0) u'(0) - w'(0) u(0)) v) / W`. -/
theorem p2x_eq_comb_of_wronskian {a q : ℂ} {w v u : ℂ → ℂ} (hw : IsMathieuSolution a q w)
    (hv : IsMathieuSolution a q v) (hW : w 0 * deriv v 0 - deriv w 0 * v 0 ≠ 0)
    (hu : IsMathieuSolution a q u) :
    u = fun z => (u 0 * deriv v 0 - deriv u 0 * v 0) / (w 0 * deriv v 0 - deriv w 0 * v 0) *
      w z + (w 0 * deriv u 0 - deriv w 0 * u 0) / (w 0 * deriv v 0 - deriv w 0 * v 0) * v z := by
  set W := w 0 * deriv v 0 - deriv w 0 * v 0
  set α := (u 0 * deriv v 0 - deriv u 0 * v 0) / W
  set β := (w 0 * deriv u 0 - deriv w 0 * u 0) / W
  have hc := (hw.const_mul α).add (hv.const_mul β)
  have hd : deriv (fun z => α * w z + β * v z) 0 = α * deriv w 0 + β * deriv v 0 :=
    (((hw.differentiable 0).hasDerivAt.const_mul α).add
      ((hv.differentiable 0).hasDerivAt.const_mul β)).deriv
  refine hu.eq_of_initial hc (z₀ := 0) ?_ ?_
  · simp only [α, β]; field_simp; ring
  · rw [hd]; simp only [α, β]; field_simp; ring

/-- **Theorem of Ince** (DLMF §28.5(i)): for `q ≠ 0`, if a nontrivial solution has period `π` or
`2π`, any solution with period `2π` (in particular with period `π`) is a multiple of it. -/
@[dlmf 28.5.i]
theorem mathieu_ince {a q : ℂ} (hq : q ≠ 0) {w v : ℂ → ℂ} (hw : IsMathieuSolution a q w)
    (hw0 : w ≠ 0) (hwp : ∀ z, w (z + 2 * π) = w z) (hv : IsMathieuSolution a q v)
    (hvp : ∀ z, v (z + 2 * π) = v z) : ∃ c : ℂ, v = fun z => c * w z := by
  set W := w 0 * deriv v 0 - deriv w 0 * v 0
  by_cases hW : W = 0
  · exact p2x_eq_const_mul_of_wronskian hw hw0 hv hW
  · exfalso
    have hI := p2x_eq_comb_of_wronskian hw hv hW (isMathieuSolution_mathieuWI a q)
    have hII := p2x_eq_comb_of_wronskian hw hv hW (isMathieuSolution_mathieuWII a q)
    refine p2x_not_coexist hq (a := a) (fun z => ?_) (fun z => ?_)
    · rw [hI]; simp only [hwp, hvp]
    · rw [hII]; simp only [hwp, hvp]

/-- **DLMF 28.5.1**: `fe_n(z, q) = C_n(q)(z ce_n(z, q) + f_n(z, q))` whenever `C_n(q) ≠ 0`
(which holds for `q ≠ 0`, `mathieuFeC_ne_zero`, and for `(n, q) = (0, 0)`). -/
@[dlmf 28.5.E1]
theorem mathieuFe_eq {n : ℕ} {q : ℝ} (hC : mathieuFeC n q ≠ 0) (z : ℂ) :
    mathieuFe n z q = mathieuFeC n q * (z * mathieuCe n z q + mathieuFeF n z q) := by
  rw [mathieuFeF]; field_simp; ring

/-- **DLMF 28.5.2**: `ge_n(z, q) = S_n(q)(z se_n(z, q) + g_n(z, q))` whenever `S_n(q) ≠ 0`. -/
@[dlmf 28.5.E2]
theorem mathieuGe_eq {n : ℕ} {q : ℝ} (hS : mathieuGeS n q ≠ 0) (z : ℂ) :
    mathieuGe n z q = mathieuGeS n q * (z * mathieuSe n z q + mathieuGeG n z q) := by
  rw [mathieuGeG]; field_simp; ring

/-! ### Helpers -/

/-- If `w_I(z + π) = ε w_I(z)`, then `u = w_II - μ z w_I` with `μ = w_I(π) w_II(π)/π`
satisfies `u(z + π) = ε u(z)`. -/
theorem p1a1_feU_add_pi {a q ε : ℂ} (hε : ∀ z, mathieuWI a q (z + π) = ε * mathieuWI a q z)
    (z : ℂ) :
    mathieuWII a q (z + π) -
        mathieuWI a q π * mathieuWII a q π / π * (z + π) * mathieuWI a q (z + π) =
      ε * (mathieuWII a q z - mathieuWI a q π * mathieuWII a q π / π * z * mathieuWI a q z) := by
  obtain ⟨h1, h10, h11⟩ := mathieuWI_spec a q
  have he : mathieuWI a q π = ε := by simpa [h10] using hε 0
  have hd : deriv (mathieuWI a q) π = 0 := by
    have := congrArg (fun f => deriv f 0) (funext hε)
    rw [deriv_comp_add_const, zero_add, deriv_const_mul _ (h1.differentiable 0), h11,
      mul_zero] at this
    exact this
  have hW := mathieuWI_wronskian a q π
  rw [hd, ← mathieuWI_pi_eq_deriv_mathieuWII_pi, he] at hW
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [mathieuWII_add_pi, ← mathieuWI_pi_eq_deriv_mathieuWII_pi, hε, he]
  field_simp
  linear_combination (-(mathieuWII a q π) * mathieuWI a q z * π) * hW

/-- If `w_II(z + π) = ε w_II(z)`, then `u = w_I - μ z w_II` with `μ = w_I'(π) w_II'(π)/π`
satisfies `u(z + π) = ε u(z)`. -/
theorem p1a1_geU_add_pi {a q ε : ℂ} (hε : ∀ z, mathieuWII a q (z + π) = ε * mathieuWII a q z)
    (z : ℂ) :
    mathieuWI a q (z + π) - deriv (mathieuWI a q) π * deriv (mathieuWII a q) π / π * (z + π) *
        mathieuWII a q (z + π) =
      ε * (mathieuWI a q z -
        deriv (mathieuWI a q) π * deriv (mathieuWII a q) π / π * z * mathieuWII a q z) := by
  obtain ⟨h2, h20, h21⟩ := mathieuWII_spec a q
  have hd : deriv (mathieuWII a q) π = ε := by
    have := congrArg (fun f => deriv f 0) (funext hε)
    rw [deriv_comp_add_const, zero_add, deriv_const_mul _ (h2.differentiable 0), h21,
      mul_one] at this
    exact this
  have he : mathieuWII a q π = 0 := by simpa [h20] using hε 0
  have hW := mathieuWI_wronskian a q π
  rw [he, mathieuWI_pi_eq_deriv_mathieuWII_pi, hd] at hW
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [mathieuWI_add_pi, mathieuWI_pi_eq_deriv_mathieuWII_pi, hε, hd]
  field_simp
  linear_combination (-(deriv (mathieuWI a q) π * mathieuWII a q z * π)) * hW

/-- `w_I(z + π; a_n(q), q) = (-1)ⁿ w_I(z; a_n(q), q)`. -/
theorem p1a1_mathieuWI_mathieuA_add_pi (n : ℕ) (q : ℝ) (z : ℂ) :
    mathieuWI (mathieuA n q) q (z + π) = (-1) ^ n * mathieuWI (mathieuA n q) q z := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [m28a_mathieuWI_periodic (deriv_mathieuWI_half_pi_mathieuA_even k q), pow_mul]; simp
  · rw [m28a_mathieuWI_antiperiodic (mathieuWI_half_pi_mathieuA_odd k q), pow_succ, pow_mul]
    simp

/-- `w_II(z + π; b_n(q), q) = (-1)ⁿ w_II(z; b_n(q), q)`, `n ≥ 1`. -/
theorem p1a1_mathieuWII_mathieuB_add_pi {n : ℕ} (hn : n ≠ 0) (q : ℝ) (z : ℂ) :
    mathieuWII (mathieuB n q) q (z + π) = (-1) ^ n * mathieuWII (mathieuB n q) q z := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (j + 1) = 2 * j + 2 by ring,
      m28a_mathieuWII_periodic (mathieuWII_half_pi_mathieuB_even j q), pow_succ, pow_succ,
      pow_mul]
    simp
  · rw [m28a_mathieuWII_antiperiodic (deriv_mathieuWII_half_pi_mathieuB_odd k q), pow_succ,
      pow_mul]
    simp

/-- Helper for §28.5 (`p1a1_mathieuFeU_add_pi`). -/
theorem p1a1_mathieuFeU_add_pi (n : ℕ) (q : ℝ) (z : ℂ) :
    mathieuFeU n (z + π) q = (-1) ^ n * mathieuFeU n z q := by
  simp only [mathieuFeU, mathieuFeMu]
  exact p1a1_feU_add_pi (p1a1_mathieuWI_mathieuA_add_pi n q) z

/-- Helper for §28.5 (`p1a1_mathieuGeU_add_pi`). -/
theorem p1a1_mathieuGeU_add_pi {n : ℕ} (hn : n ≠ 0) (q : ℝ) (z : ℂ) :
    mathieuGeU n (z + π) q = (-1) ^ n * mathieuGeU n z q := by
  simp only [mathieuGeU, mathieuGeMu]
  exact p1a1_geU_add_pi (p1a1_mathieuWII_mathieuB_add_pi hn q) z

/-- Helper for §28.5 (`p1a1_mathieuFeU_neg`). -/
theorem p1a1_mathieuFeU_neg (n : ℕ) (q : ℝ) (z : ℂ) :
    mathieuFeU n (-z) q = -mathieuFeU n z q := by
  simp only [mathieuFeU, mathieuWI_neg, mathieuWII_neg]; ring

/-- Helper for §28.5 (`p1a1_mathieuGeU_neg`). -/
theorem p1a1_mathieuGeU_neg (n : ℕ) (q : ℝ) (z : ℂ) :
    mathieuGeU n (-z) q = mathieuGeU n z q := by
  simp only [mathieuGeU, mathieuWI_neg, mathieuWII_neg]; ring

/-- For `q ≠ 0` and `C_n(q) ≠ 0`: `f_n = (ce_n(0)/μ) u` and `C_n f_n = fe_n'(0) u`. -/
theorem p1a1_mathieuFeF_eq {n : ℕ} {q : ℝ} (hq : q ≠ 0) (hC : mathieuFeC n q ≠ 0) (z : ℂ) :
    mathieuFeF n z q = mathieuCeZero n q / mathieuFeMu n q * mathieuFeU n z q ∧
      mathieuFeC n q * mathieuFeF n z q = mathieuFeDerivZero n q * mathieuFeU n z q := by
  have hnq : ¬ (n = 0 ∧ q = 0) := fun h => hq h.2
  have hC' := hC
  simp only [mathieuFeC, hnq, ↓reduceIte] at hC'
  have hc : (mathieuCeZero n q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mathieuCeZero_pos n q).ne'
  have hd : (mathieuFeDerivZero n q : ℂ) ≠ 0 := by
    intro h; apply hC'; rw [h]; ring
  have hμ : mathieuFeMu n q ≠ 0 := by
    intro h; apply hC'; rw [h]; ring
  have e1 : mathieuFeF n z q = mathieuCeZero n q / mathieuFeMu n q * mathieuFeU n z q := by
    simp only [mathieuFeF, mathieuFe, mathieuFeC, hnq, ↓reduceIte, mathieuCe, mathieuFeU]
    field_simp
  refine ⟨e1, ?_⟩
  rw [e1]; simp only [mathieuFeC, hnq, ↓reduceIte]; field_simp

/-- For `S_n(q) ≠ 0`: `g_n = (se_n'(0)/μ) u` and `S_n g_n = ge_n(0) u`. -/
theorem p1a1_mathieuGeG_eq {n : ℕ} {q : ℝ} (hS : mathieuGeS n q ≠ 0) (z : ℂ) :
    mathieuGeG n z q = mathieuSeDerivZero n q / mathieuGeMu n q * mathieuGeU n z q ∧
      mathieuGeS n q * mathieuGeG n z q = mathieuGeZero n q * mathieuGeU n z q := by
  have hs : (mathieuSeDerivZero n q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mathieuSeDerivZero_pos n q).ne'
  have hd : (mathieuGeZero n q : ℂ) ≠ 0 := by
    intro h; apply hS; rw [mathieuGeS, h]; ring
  have hμ : mathieuGeMu n q ≠ 0 := by
    intro h; apply hS; rw [mathieuGeS, h]; ring
  have e1 : mathieuGeG n z q = mathieuSeDerivZero n q / mathieuGeMu n q * mathieuGeU n z q := by
    simp only [mathieuGeG, mathieuGe, mathieuGeS, mathieuSe, mathieuGeU]
    field_simp
  refine ⟨e1, ?_⟩
  rw [e1, mathieuGeS]; field_simp

/-- Helper for §28.5 (`p1a1_mathieuFeF_add_pi`). -/
theorem p1a1_mathieuFeF_add_pi {n : ℕ} {q : ℝ} (hq : q ≠ 0) (hC : mathieuFeC n q ≠ 0) (z : ℂ) :
    mathieuFeF n (z + π) q = (-1) ^ n * mathieuFeF n z q := by
  rw [(p1a1_mathieuFeF_eq hq hC _).1, (p1a1_mathieuFeF_eq hq hC _).1, p1a1_mathieuFeU_add_pi]
  ring

/-- Helper for §28.5 (`p1a1_mathieuFeF_neg`). -/
theorem p1a1_mathieuFeF_neg {n : ℕ} {q : ℝ} (hq : q ≠ 0) (hC : mathieuFeC n q ≠ 0) (z : ℂ) :
    mathieuFeF n (-z) q = -mathieuFeF n z q := by
  rw [(p1a1_mathieuFeF_eq hq hC _).1, (p1a1_mathieuFeF_eq hq hC _).1, p1a1_mathieuFeU_neg]
  ring

/-- Helper for §28.5 (`p1a1_mathieuGeG_add_pi`). -/
theorem p1a1_mathieuGeG_add_pi {n : ℕ} (hn : n ≠ 0) {q : ℝ} (hS : mathieuGeS n q ≠ 0)
    (z : ℂ) : mathieuGeG n (z + π) q = (-1) ^ n * mathieuGeG n z q := by
  rw [(p1a1_mathieuGeG_eq hS _).1, (p1a1_mathieuGeG_eq hS _).1, p1a1_mathieuGeU_add_pi hn]
  ring

/-- Helper for §28.5 (`p1a1_mathieuGeG_neg`). -/
theorem p1a1_mathieuGeG_neg {n : ℕ} {q : ℝ} (hS : mathieuGeS n q ≠ 0) (z : ℂ) :
    mathieuGeG n (-z) q = mathieuGeG n z q := by
  rw [(p1a1_mathieuGeG_eq hS _).1, (p1a1_mathieuGeG_eq hS _).1, p1a1_mathieuGeU_neg]

/-- The normalizing integral of `u` is positive once `fe_n'(0) ≠ 0`. -/
theorem p1a1_integral_pos_of_sqrt_ne {f : ℂ → ℂ}
    (h : Real.sqrt (π / ∫ x in (0 : ℝ)..2 * π, ‖f x‖ ^ 2) ≠ 0) :
    0 < ∫ x in (0 : ℝ)..2 * π, ‖f x‖ ^ 2 := by
  by_contra hle
  rw [not_lt] at hle
  exact h (Real.sqrt_eq_zero'.mpr (div_nonpos_of_nonneg_of_nonpos Real.pi_pos.le hle))

/-- Helper for §28.5 (`p1a1_mathieuFeU_real`). -/
theorem p1a1_mathieuFeU_real (n : ℕ) (q x : ℝ) : conj (mathieuFeU n x q) = mathieuFeU n x q := by
  simp only [mathieuFeU, mathieuFeMu, map_sub, map_mul, map_div₀, Complex.conj_ofReal]
  rw [p1a1_mathieuWI_real _ _ x, p1a1_mathieuWII_real _ _ x, p1a1_mathieuWI_real _ _ π,
    p1a1_mathieuWII_real _ _ π]

/-- Helper for §28.5 (`p1a1_mathieuGeU_real`). -/
theorem p1a1_mathieuGeU_real (n : ℕ) (q x : ℝ) : conj (mathieuGeU n x q) = mathieuGeU n x q := by
  simp only [mathieuGeU, mathieuGeMu, map_sub, map_mul, map_div₀, Complex.conj_ofReal]
  rw [p1a1_mathieuWI_real _ _ x, p1a1_mathieuWII_real _ _ x, p1a1_deriv_mathieuWI_real _ _ π,
    p1a1_deriv_mathieuWII_real _ _ π]

/-- Helper for §28.5 (`p1a1_fe_normalization`). -/
theorem p1a1_fe_normalization {n : ℕ} {q : ℝ} (hq : q ≠ 0) (hC : mathieuFeC n q ≠ 0) :
    mathieuFeC n q ^ 2 * ∫ x in (0 : ℝ)..2 * π, mathieuFeF n x q ^ 2 = π := by
  have key : ∀ x : ℝ, mathieuFeC n q ^ 2 * mathieuFeF n x q ^ 2 =
      ((mathieuFeDerivZero n q : ℂ) * mathieuFeU n x q) ^ 2 := fun x => by
    rw [← mul_pow, (p1a1_mathieuFeF_eq hq hC _).2]
  rw [← intervalIntegral.integral_const_mul]
  simp_rw [key]
  have hnq : ¬ (n = 0 ∧ q = 0) := fun h => hq h.2
  have hC' := hC
  simp only [mathieuFeC, hnq, ↓reduceIte] at hC'
  have hd : mathieuFeDerivZero n q ≠ 0 := by
    intro h; apply hC'; rw [h]; simp
  have h3 := p1a1_integral_pos_of_sqrt_ne (f := fun z => mathieuFeU n z q) hd
  exact p1a1_integral_normalized_sq (f := fun z => mathieuFeU n z q)
    (fun x => p1a1_mathieuFeU_real n q x) h3

/-- Helper for §28.5 (`p1a1_ge_normalization`). -/
theorem p1a1_ge_normalization {n : ℕ} {q : ℝ} (hS : mathieuGeS n q ≠ 0) :
    mathieuGeS n q ^ 2 * ∫ x in (0 : ℝ)..2 * π, mathieuGeG n x q ^ 2 = π := by
  have key : ∀ x : ℝ, mathieuGeS n q ^ 2 * mathieuGeG n x q ^ 2 =
      ((mathieuGeZero n q : ℂ) * mathieuGeU n x q) ^ 2 := fun x => by
    rw [← mul_pow, (p1a1_mathieuGeG_eq hS _).2]
  rw [← intervalIntegral.integral_const_mul]
  simp_rw [key]
  have hd : mathieuGeZero n q ≠ 0 := by
    intro h; apply hS; rw [mathieuGeS, h]; simp
  have h3 := p1a1_integral_pos_of_sqrt_ne (f := fun z => mathieuGeU n z q) hd
  exact p1a1_integral_normalized_sq (f := fun z => mathieuGeU n z q)
    (fun x => p1a1_mathieuGeU_real n q x) h3

/-- Shift invariance of `∫₀^{2π}` for a `π`-periodic real function. -/
theorem p1a1_integral_comp_add_of_periodic {g : ℝ → ℝ} (hg : ∀ x, g (x + π) = g x) (s : ℝ) :
    ∫ x in (0 : ℝ)..2 * π, g (x + s) = ∫ x in (0 : ℝ)..2 * π, g x := by
  have hp : Function.Periodic g (2 * π) := fun x => by
    rw [show x + 2 * π = x + π + π by ring, hg, hg]
  rw [intervalIntegral.integral_comp_add_right, zero_add,
    show 2 * π + s = s + 2 * π by ring, hp.intervalIntegral_add_eq s 0, zero_add]

/-- `√(π / (k² I)) = √(π / I) / k` for `k > 0`. -/
theorem p1a1_sqrt_div_sq {k I : ℝ} (hk : 0 < k) :
    Real.sqrt (π / (k ^ 2 * I)) = Real.sqrt (π / I) / k := by
  rw [mul_comm, ← div_div, Real.sqrt_div' _ (sq_nonneg k), Real.sqrt_sq hk.le]

/-- For real `A`, `B'` with `A B' = 1`: `A ‖B'‖ / ‖A‖ = B'`. -/
theorem p1a1_real_ratio {A B : ℂ} (hA : conj A = A) (hB : conj B = B) (h : A * B = 1) :
    A * ‖B‖ / ‖A‖ = B := by
  obtain ⟨r, rfl⟩ := Complex.conj_eq_iff_real.mp hA
  obtain ⟨s, rfl⟩ := Complex.conj_eq_iff_real.mp hB
  have h' : r * s = 1 := by exact_mod_cast h
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hr : r ≠ 0 := left_ne_zero_of_mul_eq_one h'
  have : r * |s| / |r| = s := by
    rcases lt_or_gt_of_ne hr with hr | hr
    · have hs : s < 0 := by nlinarith
      rw [abs_of_neg hr, abs_of_neg hs]; field_simp
    · have hs : 0 < s := by nlinarith
      rw [abs_of_pos hr, abs_of_pos hs]; field_simp
  exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) this

/-- **28.5.6**, even case, the `ce` normalizing factor: `ce_{2m}(0, -q) = ce_{2m}(0, q)/|B'|`
with `B' = w_II'(π/2; a_{2m}(q), q)`. -/
theorem p1a1_mathieuCeZero_even_neg (m : ℕ) (q : ℝ) :
    mathieuCeZero (2 * m) (-q) = mathieuCeZero (2 * m) q /
      ‖deriv (mathieuWII (mathieuA (2 * m) q) q) (π / 2)‖ := by
  set a : ℂ := (mathieuA (2 * m) q : ℂ)
  have hA' := deriv_mathieuWI_half_pi_mathieuA_even m q
  have hW := mathieuWI_wronskian a q (π / 2)
  rw [hA', zero_mul, sub_zero] at hW
  have hB : 0 < ‖deriv (mathieuWII a q) (π / 2)‖ :=
    norm_pos_iff.mpr (right_ne_zero_of_mul_eq_one hW)
  have e : ∀ x : ℝ, ‖mathieuWI (mathieuA (2 * m) (-q) : ℂ) ((-q : ℝ) : ℂ) x‖ ^ 2 =
      ‖deriv (mathieuWII a q) (π / 2)‖ ^ 2 * ‖mathieuWI a q ((x + π / 2 : ℝ) : ℂ)‖ ^ 2 := by
    intro x
    rw [mathieuA_even_neg, Complex.ofReal_neg, p1a1_mathieuWI_neg_q, hA', zero_mul, sub_zero,
      norm_mul, mul_pow]
    push_cast; rfl
  rw [mathieuCeZero, mathieuCeZero]
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul,
    p1a1_integral_comp_add_of_periodic (g := fun x => ‖mathieuWI a q x‖ ^ 2) (fun x => by
      push_cast; rw [p1a1_mathieuWI_mathieuA_add_pi, norm_mul]; simp; rfl),
    p1a1_sqrt_div_sq hB]

/-- Helper for §28.5 (`p1a1_feU_neg_q`). -/
theorem p1a1_feU_neg_q {a q : ℂ} (hA' : deriv (mathieuWI a q) (π / 2) = 0) (z : ℂ) :
    mathieuWII a (-q) z - mathieuWI a (-q) π * mathieuWII a (-q) π / π * z * mathieuWI a (-q) z =
      mathieuWI a q (π / 2) * (mathieuWII a q (z + π / 2) -
        mathieuWI a q π * mathieuWII a q π / π * (z + π / 2) * mathieuWI a q (z + π / 2)) := by
  have hW := mathieuWI_wronskian a q (π / 2)
  rw [hA', zero_mul, sub_zero] at hW
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← mathieuWI_pi_neg_q, mathieuWII_pi a (-q), p1a1_mathieuWII_half_pi_neg_q,
    p1a1_deriv_mathieuWII_half_pi_neg_q, p1a1_mathieuWI_neg_q, p1a1_mathieuWII_neg_q,
    m28a_mathieuWI_pi, mathieuWII_pi, hA']
  have hππ : (π : ℂ) * (π : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hπ
  linear_combination mathieuWII a q (π / 2) * mathieuWI a q (z + π / 2) *
    (mathieuWI a q (π / 2) * deriv (mathieuWII a q) (π / 2) + 1) * hW +
    mathieuWI a q (π / 2) ^ 2 * mathieuWII a q (π / 2) * mathieuWI a q (z + π / 2) *
      deriv (mathieuWII a q) (π / 2) ^ 2 * hππ

/-- Helper for §28.5 (`p1a1_mathieuFeDerivZero_even_neg`). -/
theorem p1a1_mathieuFeDerivZero_even_neg (m : ℕ) (q : ℝ) :
    mathieuFeDerivZero (2 * m) (-q) = mathieuFeDerivZero (2 * m) q /
      ‖mathieuWI (mathieuA (2 * m) q) q (π / 2)‖ := by
  set a : ℂ := (mathieuA (2 * m) q : ℂ)
  have hA' := deriv_mathieuWI_half_pi_mathieuA_even m q
  have hW := mathieuWI_wronskian a q (π / 2)
  rw [hA', zero_mul, sub_zero] at hW
  have hA : 0 < ‖mathieuWI a q (π / 2)‖ := norm_pos_iff.mpr (left_ne_zero_of_mul_eq_one hW)
  have e : ∀ x : ℝ, ‖mathieuFeU (2 * m) x (-q)‖ ^ 2 =
      ‖mathieuWI a q (π / 2)‖ ^ 2 * ‖mathieuFeU (2 * m) ((x + π / 2 : ℝ) : ℂ) q‖ ^ 2 := by
    intro x
    simp only [mathieuFeU, mathieuFeMu]
    rw [mathieuA_even_neg, Complex.ofReal_neg, p1a1_feU_neg_q hA', norm_mul, mul_pow]
    push_cast; rfl
  rw [mathieuFeDerivZero, mathieuFeDerivZero]
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul,
    p1a1_integral_comp_add_of_periodic (g := fun x => ‖mathieuFeU (2 * m) x q‖ ^ 2) (fun x => by
      push_cast; rw [p1a1_mathieuFeU_add_pi, norm_mul]; simp),
    p1a1_sqrt_div_sq hA]

/-- Helper for §28.5 (`p1a1_C_even_neg`). -/
theorem p1a1_C_even_neg (m : ℕ) (q : ℝ) : mathieuFeC (2 * m) (-q) = mathieuFeC (2 * m) q := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hnq : ¬ (2 * m = 0 ∧ q = 0) := fun h => hq h.2
  have hnq' : ¬ (2 * m = 0 ∧ -q = 0) := fun h => hq (neg_eq_zero.mp h.2)
  simp only [mathieuFeC, hnq, hnq', ↓reduceIte]
  rw [p1a1_mathieuCeZero_even_neg, p1a1_mathieuFeDerivZero_even_neg]
  set a : ℂ := (mathieuA (2 * m) q : ℂ)
  have hA' := deriv_mathieuWI_half_pi_mathieuA_even m q
  have hW := mathieuWI_wronskian a q (π / 2)
  rw [hA', zero_mul, sub_zero] at hW
  have hμ1 : mathieuFeMu (2 * m) (-q) =
      mathieuWI a q (π / 2) * deriv (mathieuWII a q) (π / 2) *
        (2 * mathieuWII a q (π / 2) * mathieuWI a q (π / 2)) / π := by
    rw [mathieuFeMu, mathieuA_even_neg, Complex.ofReal_neg, ← mathieuWI_pi_neg_q,
      mathieuWII_pi _ (-(q : ℂ)), p1a1_mathieuWII_half_pi_neg_q,
      p1a1_deriv_mathieuWII_half_pi_neg_q, m28a_mathieuWI_pi, hA']
    ring
  have hμ2 : mathieuFeMu (2 * m) q =
      mathieuWI a q (π / 2) * deriv (mathieuWII a q) (π / 2) *
        (2 * mathieuWII a q (π / 2) * deriv (mathieuWII a q) (π / 2)) / π := by
    rw [mathieuFeMu, m28a_mathieuWI_pi, mathieuWII_pi, hA']
    ring
  rw [hμ1, hμ2]
  have hAr : conj (mathieuWI a q (π / 2)) = mathieuWI a q (π / 2) := by
    have := p1a1_mathieuWI_real (mathieuA (2 * m) q) q (π / 2); push_cast at this; exact this
  have hBr : conj (deriv (mathieuWII a q) (π / 2)) = deriv (mathieuWII a q) (π / 2) := by
    have := p1a1_deriv_mathieuWII_real (mathieuA (2 * m) q) q (π / 2)
    push_cast at this; exact this
  have hr := p1a1_real_ratio hAr hBr hW
  have hA0 : (‖mathieuWI a q (π / 2)‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (left_ne_zero_of_mul_eq_one hW))
  have hB0 : (‖deriv (mathieuWII a q) (π / 2)‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (right_ne_zero_of_mul_eq_one hW))
  have hc : (mathieuCeZero (2 * m) q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mathieuCeZero_pos _ q).ne'
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr' : mathieuWI a q (π / 2) * (‖deriv (mathieuWII a q) (π / 2)‖ : ℂ) =
      deriv (mathieuWII a q) (π / 2) * ‖mathieuWI a q (π / 2)‖ := by
    rw [div_eq_iff hA0] at hr; exact hr
  push_cast
  generalize mathieuWI a q (π / 2) = A at *
  generalize deriv (mathieuWII a q) (π / 2) = Bp at *
  generalize mathieuWII a q (π / 2) = B at *
  field_simp
  linear_combination ((mathieuFeDerivZero (2 * m) q : ℂ) * A * Bp * B) * hr'

/-- Helper for §28.5 (`p1a1_feU_neg_q_odd`). -/
theorem p1a1_feU_neg_q_odd {a q : ℂ} (hB' : deriv (mathieuWII a q) (π / 2) = 0) (z : ℂ) :
    mathieuWII a (-q) z - mathieuWI a (-q) π * mathieuWII a (-q) π / π * z * mathieuWI a (-q) z =
      -mathieuWII a q (π / 2) * (mathieuWI a q (z + π / 2) -
        deriv (mathieuWI a q) π * deriv (mathieuWII a q) π / π * (z + π / 2) *
          mathieuWII a q (z + π / 2)) := by
  have hW := mathieuWI_wronskian a q (π / 2)
  rw [hB', mul_zero, zero_sub] at hW
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← mathieuWI_pi_neg_q, mathieuWII_pi a (-q), p1a1_mathieuWII_half_pi_neg_q,
    p1a1_deriv_mathieuWII_half_pi_neg_q, p1a1_mathieuWI_neg_q, p1a1_mathieuWII_neg_q,
    m28a_mathieuWI_pi, deriv_mathieuWI_pi, m28a_deriv_mathieuWII_pi, hB']
  have hππ : (π : ℂ) * (π : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hπ
  linear_combination (-(mathieuWI a q (π / 2) * mathieuWII a q (z + π / 2) *
    (1 - deriv (mathieuWI a q) (π / 2) * mathieuWII a q (π / 2)))) * hW -
    (mathieuWI a q (π / 2) * mathieuWII a q (z + π / 2) * mathieuWII a q (π / 2) ^ 2 *
      deriv (mathieuWI a q) (π / 2) ^ 2) * hππ

/-- Helper for §28.5 (`p1a1_geU_neg_q_even`). -/
theorem p1a1_geU_neg_q_even {a q : ℂ} (hB : mathieuWII a q (π / 2) = 0) (z : ℂ) :
    mathieuWI a (-q) z - deriv (mathieuWI a (-q)) π * deriv (mathieuWII a (-q)) π / π * z *
        mathieuWII a (-q) z =
      deriv (mathieuWII a q) (π / 2) * (mathieuWI a q (z + π / 2) -
        deriv (mathieuWI a q) π * deriv (mathieuWII a q) π / π * (z + π / 2) *
          mathieuWII a q (z + π / 2)) := by
  have hW := mathieuWI_wronskian a q (π / 2)
  rw [hB, mul_zero, sub_zero] at hW
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← mathieuWI_pi_eq_deriv_mathieuWII_pi a (-q), ← mathieuWI_pi_neg_q,
    deriv_mathieuWI_pi a (-q), p1a1_mathieuWI_half_pi_neg_q, p1a1_deriv_mathieuWI_half_pi_neg_q,
    p1a1_mathieuWI_neg_q, p1a1_mathieuWII_neg_q,
    m28a_mathieuWI_pi, deriv_mathieuWI_pi, m28a_deriv_mathieuWII_pi, hB]
  have hππ : (π : ℂ) * (π : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hπ
  linear_combination (deriv (mathieuWI a q) (π / 2) * mathieuWII a q (z + π / 2) *
    (mathieuWI a q (π / 2) * deriv (mathieuWII a q) (π / 2) + 1)) * hW +
    (deriv (mathieuWII a q) (π / 2) ^ 2 * deriv (mathieuWI a q) (π / 2) *
      mathieuWII a q (z + π / 2) * mathieuWI a q (π / 2) ^ 2) * hππ

/-- Helper for §28.5 (`p1a1_mathieuCeZero_odd_neg`). -/
theorem p1a1_mathieuCeZero_odd_neg (m : ℕ) (q : ℝ) :
    mathieuCeZero (2 * m + 1) (-q) = mathieuSeDerivZero (2 * m + 1) q /
      ‖deriv (mathieuWI (mathieuB (2 * m + 1) q) q) (π / 2)‖ := by
  set b : ℂ := (mathieuB (2 * m + 1) q : ℂ)
  have hB' := deriv_mathieuWII_half_pi_mathieuB_odd m q
  have hW := mathieuWI_wronskian b q (π / 2)
  rw [hB', mul_zero, zero_sub] at hW
  have hA : 0 < ‖deriv (mathieuWI b q) (π / 2)‖ :=
    norm_pos_iff.mpr (fun h => by rw [h] at hW; simp at hW)
  have e : ∀ x : ℝ, ‖mathieuWI (mathieuA (2 * m + 1) (-q) : ℂ) ((-q : ℝ) : ℂ) x‖ ^ 2 =
      ‖deriv (mathieuWI b q) (π / 2)‖ ^ 2 * ‖mathieuWII b q ((x + π / 2 : ℝ) : ℂ)‖ ^ 2 := by
    intro x
    rw [mathieuA_odd_neg, Complex.ofReal_neg, p1a1_mathieuWI_neg_q, hB', zero_mul, zero_sub,
      norm_neg, norm_mul, mul_pow]
    push_cast; rfl
  rw [mathieuCeZero, mathieuSeDerivZero]
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul,
    p1a1_integral_comp_add_of_periodic (g := fun x => ‖mathieuWII b q x‖ ^ 2) (fun x => by
      push_cast; rw [p1a1_mathieuWII_mathieuB_add_pi (by omega), norm_mul]; simp; rfl),
    p1a1_sqrt_div_sq hA]

/-- Helper for §28.5 (`p1a1_mathieuFeDerivZero_odd_neg`). -/
theorem p1a1_mathieuFeDerivZero_odd_neg (m : ℕ) (q : ℝ) :
    mathieuFeDerivZero (2 * m + 1) (-q) = mathieuGeZero (2 * m + 1) q /
      ‖mathieuWII (mathieuB (2 * m + 1) q) q (π / 2)‖ := by
  set b : ℂ := (mathieuB (2 * m + 1) q : ℂ)
  have hB' := deriv_mathieuWII_half_pi_mathieuB_odd m q
  have hW := mathieuWI_wronskian b q (π / 2)
  rw [hB', mul_zero, zero_sub] at hW
  have hB : 0 < ‖mathieuWII b q (π / 2)‖ :=
    norm_pos_iff.mpr (fun h => by rw [h] at hW; simp at hW)
  have e : ∀ x : ℝ, ‖mathieuFeU (2 * m + 1) x (-q)‖ ^ 2 =
      ‖mathieuWII b q (π / 2)‖ ^ 2 * ‖mathieuGeU (2 * m + 1) ((x + π / 2 : ℝ) : ℂ) q‖ ^ 2 := by
    intro x
    simp only [mathieuFeU, mathieuFeMu, mathieuGeU, mathieuGeMu]
    rw [mathieuA_odd_neg, Complex.ofReal_neg, p1a1_feU_neg_q_odd hB', norm_mul, norm_neg,
      mul_pow]
    push_cast; rfl
  rw [mathieuFeDerivZero, mathieuGeZero]
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul,
    p1a1_integral_comp_add_of_periodic (g := fun x => ‖mathieuGeU (2 * m + 1) x q‖ ^ 2)
      (fun x => by push_cast; rw [p1a1_mathieuGeU_add_pi (by omega), norm_mul]; simp),
    p1a1_sqrt_div_sq hB]

/-- Helper for §28.5 (`p1a1_C_odd_neg`). -/
theorem p1a1_C_odd_neg (m : ℕ) (q : ℝ) :
    mathieuFeC (2 * m + 1) (-q) = -mathieuGeS (2 * m + 1) q := by
  have hnq' : ¬ (2 * m + 1 = 0 ∧ -q = 0) := fun h => by omega
  simp only [mathieuFeC, hnq', ↓reduceIte, mathieuGeS]
  rw [p1a1_mathieuCeZero_odd_neg, p1a1_mathieuFeDerivZero_odd_neg]
  set b : ℂ := (mathieuB (2 * m + 1) q : ℂ)
  have hB' := deriv_mathieuWII_half_pi_mathieuB_odd m q
  have hW := mathieuWI_wronskian b q (π / 2)
  rw [hB', mul_zero, zero_sub] at hW
  have hμ1 : mathieuFeMu (2 * m + 1) (-q) =
      deriv (mathieuWI b q) (π / 2) * mathieuWII b q (π / 2) *
        (2 * mathieuWII b q (π / 2) * mathieuWI b q (π / 2)) / π := by
    rw [mathieuFeMu, mathieuA_odd_neg, Complex.ofReal_neg, ← mathieuWI_pi_neg_q,
      mathieuWII_pi _ (-(q : ℂ)), p1a1_mathieuWII_half_pi_neg_q,
      p1a1_deriv_mathieuWII_half_pi_neg_q, m28a_mathieuWI_pi, hB']
    ring
  have hμ2 : mathieuGeMu (2 * m + 1) q =
      2 * mathieuWI b q (π / 2) * deriv (mathieuWI b q) (π / 2) *
        (deriv (mathieuWI b q) (π / 2) * mathieuWII b q (π / 2)) / π := by
    rw [mathieuGeMu, deriv_mathieuWI_pi, m28a_deriv_mathieuWII_pi, hB']
    ring
  rw [hμ1, hμ2]
  have hAr : conj (-deriv (mathieuWI b q) (π / 2)) = -deriv (mathieuWI b q) (π / 2) := by
    have := p1a1_deriv_mathieuWI_real (mathieuB (2 * m + 1) q) q (π / 2)
    push_cast at this; rw [map_neg, this]
  have hBr : conj (mathieuWII b q (π / 2)) = mathieuWII b q (π / 2) := by
    have := p1a1_mathieuWII_real (mathieuB (2 * m + 1) q) q (π / 2)
    push_cast at this; exact this
  have hW' : -deriv (mathieuWI b q) (π / 2) * mathieuWII b q (π / 2) = 1 := by
    rw [neg_mul]; exact hW
  have hA0 : (‖deriv (mathieuWI b q) (π / 2)‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (fun h => by rw [h] at hW; simp at hW))
  have hB0 : (‖mathieuWII b q (π / 2)‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (fun h => by rw [h] at hW; simp at hW))
  have hr := p1a1_real_ratio hAr hBr hW'
  rw [norm_neg, div_eq_iff hA0] at hr
  have hs : (mathieuSeDerivZero (2 * m + 1) q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mathieuSeDerivZero_pos _ q).ne'
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  generalize mathieuWI b q (π / 2) = A at *
  generalize deriv (mathieuWI b q) (π / 2) = Ap at *
  generalize mathieuWII b q (π / 2) = B at *
  field_simp
  linear_combination (-((mathieuGeZero (2 * m + 1) q : ℂ) * Ap * B * A)) * hr

/-- Helper for §28.5 (`p1a1_mathieuSeDerivZero_even_neg`). -/
theorem p1a1_mathieuSeDerivZero_even_neg (m : ℕ) (q : ℝ) :
    mathieuSeDerivZero (2 * m + 2) (-q) = mathieuSeDerivZero (2 * m + 2) q /
      ‖mathieuWI (mathieuB (2 * m + 2) q) q (π / 2)‖ := by
  set b : ℂ := (mathieuB (2 * m + 2) q : ℂ)
  have hB := mathieuWII_half_pi_mathieuB_even m q
  have hW := mathieuWI_wronskian b q (π / 2)
  rw [hB, mul_zero, sub_zero] at hW
  have hA : 0 < ‖mathieuWI b q (π / 2)‖ := norm_pos_iff.mpr (left_ne_zero_of_mul_eq_one hW)
  have e : ∀ x : ℝ, ‖mathieuWII (mathieuB (2 * m + 2) (-q) : ℂ) ((-q : ℝ) : ℂ) x‖ ^ 2 =
      ‖mathieuWI b q (π / 2)‖ ^ 2 * ‖mathieuWII b q ((x + π / 2 : ℝ) : ℂ)‖ ^ 2 := by
    intro x
    rw [mathieuB_even_neg, Complex.ofReal_neg, p1a1_mathieuWII_neg_q, hB, zero_mul, sub_zero,
      norm_mul, mul_pow]
    push_cast; rfl
  rw [mathieuSeDerivZero, mathieuSeDerivZero]
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul,
    p1a1_integral_comp_add_of_periodic (g := fun x => ‖mathieuWII b q x‖ ^ 2) (fun x => by
      push_cast; rw [p1a1_mathieuWII_mathieuB_add_pi (by omega), norm_mul]; simp; rfl),
    p1a1_sqrt_div_sq hA]

/-- Helper for §28.5 (`p1a1_mathieuGeZero_even_neg`). -/
theorem p1a1_mathieuGeZero_even_neg (m : ℕ) (q : ℝ) :
    mathieuGeZero (2 * m + 2) (-q) = mathieuGeZero (2 * m + 2) q /
      ‖deriv (mathieuWII (mathieuB (2 * m + 2) q) q) (π / 2)‖ := by
  set b : ℂ := (mathieuB (2 * m + 2) q : ℂ)
  have hB := mathieuWII_half_pi_mathieuB_even m q
  have hW := mathieuWI_wronskian b q (π / 2)
  rw [hB, mul_zero, sub_zero] at hW
  have hBp : 0 < ‖deriv (mathieuWII b q) (π / 2)‖ :=
    norm_pos_iff.mpr (right_ne_zero_of_mul_eq_one hW)
  have e : ∀ x : ℝ, ‖mathieuGeU (2 * m + 2) x (-q)‖ ^ 2 =
      ‖deriv (mathieuWII b q) (π / 2)‖ ^ 2 *
        ‖mathieuGeU (2 * m + 2) ((x + π / 2 : ℝ) : ℂ) q‖ ^ 2 := by
    intro x
    simp only [mathieuGeU, mathieuGeMu]
    rw [mathieuB_even_neg, Complex.ofReal_neg, p1a1_geU_neg_q_even hB, norm_mul, mul_pow]
    push_cast; rfl
  rw [mathieuGeZero, mathieuGeZero]
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul,
    p1a1_integral_comp_add_of_periodic (g := fun x => ‖mathieuGeU (2 * m + 2) x q‖ ^ 2)
      (fun x => by push_cast; rw [p1a1_mathieuGeU_add_pi (by omega), norm_mul]; simp),
    p1a1_sqrt_div_sq hBp]

/-- Helper for §28.5 (`p1a1_S_even_neg`). -/
theorem p1a1_S_even_neg (m : ℕ) (q : ℝ) :
    mathieuGeS (2 * m + 2) (-q) = mathieuGeS (2 * m + 2) q := by
  rw [mathieuGeS, mathieuGeS, p1a1_mathieuGeZero_even_neg, p1a1_mathieuSeDerivZero_even_neg]
  set b : ℂ := (mathieuB (2 * m + 2) q : ℂ)
  have hB := mathieuWII_half_pi_mathieuB_even m q
  have hW := mathieuWI_wronskian b q (π / 2)
  rw [hB, mul_zero, sub_zero] at hW
  have hμ1 : mathieuGeMu (2 * m + 2) (-q) =
      2 * deriv (mathieuWII b q) (π / 2) * deriv (mathieuWI b q) (π / 2) *
        (mathieuWI b q (π / 2) * deriv (mathieuWII b q) (π / 2)) / π := by
    rw [mathieuGeMu, mathieuB_even_neg, Complex.ofReal_neg,
      ← mathieuWI_pi_eq_deriv_mathieuWII_pi _ (-(q : ℂ)), ← mathieuWI_pi_neg_q,
      deriv_mathieuWI_pi _ (-(q : ℂ)), p1a1_mathieuWI_half_pi_neg_q,
      p1a1_deriv_mathieuWI_half_pi_neg_q, m28a_mathieuWI_pi, hB]
    ring
  have hμ2 : mathieuGeMu (2 * m + 2) q =
      2 * mathieuWI b q (π / 2) * deriv (mathieuWI b q) (π / 2) *
        (mathieuWI b q (π / 2) * deriv (mathieuWII b q) (π / 2)) / π := by
    rw [mathieuGeMu, deriv_mathieuWI_pi, m28a_deriv_mathieuWII_pi, hB]
    ring
  rw [hμ1, hμ2]
  have hAr : conj (mathieuWI b q (π / 2)) = mathieuWI b q (π / 2) := by
    have := p1a1_mathieuWI_real (mathieuB (2 * m + 2) q) q (π / 2); push_cast at this; exact this
  have hBr : conj (deriv (mathieuWII b q) (π / 2)) = deriv (mathieuWII b q) (π / 2) := by
    have := p1a1_deriv_mathieuWII_real (mathieuB (2 * m + 2) q) q (π / 2)
    push_cast at this; exact this
  have hW' : deriv (mathieuWII b q) (π / 2) * mathieuWI b q (π / 2) = 1 := by
    rw [mul_comm]; exact hW
  have hA0 : (‖mathieuWI b q (π / 2)‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (left_ne_zero_of_mul_eq_one hW))
  have hB0 : (‖deriv (mathieuWII b q) (π / 2)‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (right_ne_zero_of_mul_eq_one hW))
  have hr := p1a1_real_ratio hBr hAr hW'
  rw [div_eq_iff hB0] at hr
  have hs : (mathieuSeDerivZero (2 * m + 2) q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mathieuSeDerivZero_pos _ q).ne'
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  generalize mathieuWI b q (π / 2) = A at *
  generalize deriv (mathieuWI b q) (π / 2) = Ap at *
  generalize deriv (mathieuWII b q) (π / 2) = Bp at *
  field_simp
  linear_combination ((mathieuGeZero (2 * m + 2) q : ℂ) * Bp * Ap * A) * hr

/-- `∫₀^{2π} ‖f‖² > 0` for an entire function `f ≢ 0`. -/
theorem p1a1_integral_normSq_pos_of_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) : 0 < ∫ x in (0 : ℝ)..2 * π, ‖f x‖ ^ 2 := by
  rcases (hf.analyticAt 0).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso; apply hne
    funext z
    exact AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun z _ => hf.analyticAt z) isPreconnected_univ (mem_univ 0) h (mem_univ z)
  · apply m28a_integral_normSq_pos hf.continuous
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        exact Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
    exact ht.eventually h

/-- If `w_II(z) = μ z w_I(z)` for all `z`, then `q = 0`. -/
theorem p1a1_q_eq_zero_of_mathieuWII_eq {a q μ : ℂ}
    (h : ∀ z, mathieuWII a q z = μ * z * mathieuWI a q z) : q = 0 := by
  obtain ⟨h1, h10, h11⟩ := mathieuWI_spec a q
  obtain ⟨h2, h20, h21⟩ := mathieuWII_spec a q
  have hd : ∀ z, HasDerivAt (mathieuWII a q)
      (μ * mathieuWI a q z + μ * z * deriv (mathieuWI a q) z) z := by
    intro z
    rw [show mathieuWII a q = fun z => μ * z * mathieuWI a q z from funext h]
    have := ((hasDerivAt_id' z).const_mul μ).mul (h1.differentiable z).hasDerivAt
    simp only [mul_one] at this
    exact this
  have hμ : μ = 1 := by
    have := (hd 0).deriv; rw [h21, h10, h11] at this; simpa using this.symm
  subst hμ
  have hdd : ∀ z, deriv (mathieuWI a q) z = 0 := by
    intro z
    have e1 : deriv (mathieuWII a q) = fun z =>
        mathieuWI a q z + z * deriv (mathieuWI a q) z := by
      funext z; rw [(hd z).deriv]; ring
    have e2 := h2.hasDerivAt_deriv z
    rw [e1] at e2
    have e3 := ((h1.differentiable z).hasDerivAt.add
      ((hasDerivAt_id z).mul (h1.hasDerivAt_deriv z)))
    have := e2.unique e3
    rw [h z] at this
    simp only [id] at this
    linear_combination -this / 2
  have hc : ∀ z, mathieuWI a q z = 1 := by
    intro z
    rw [← h10]
    exact is_const_of_deriv_eq_zero h1.differentiable hdd z 0
  have hz : ∀ z, (2 * q * Complex.cos (2 * z) - a) = 0 := by
    intro z
    have := h1.deriv_deriv z
    rw [show deriv (mathieuWI a q) = fun _ => 0 from funext hdd, deriv_const, hc] at this
    linear_combination -this
  have e0 := hz 0
  have e1 := hz (π / 2)
  rw [show 2 * ((π : ℂ) / 2) = π by ring, Complex.cos_pi] at e1
  simp at e0
  linear_combination (e0 - e1) / 4

/-- `C_n(q) ≠ 0` for real `q ≠ 0` (a consequence of Ince's theorem, DLMF §28.5(i)). -/
@[dlmf 28.5.i]
theorem mathieuFeC_ne_zero (n : ℕ) {q : ℝ} (hq : q ≠ 0) : mathieuFeC n q ≠ 0 := by
  have hince := @mathieu_ince
  have hq' : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
  have hnq : ¬ (n = 0 ∧ q = 0) := fun h => hq h.2
  set a : ℂ := (mathieuA n q : ℂ)
  obtain ⟨h1, h10, h11⟩ := mathieuWI_spec a q
  obtain ⟨h2, h20, h21⟩ := mathieuWII_spec a q
  have hW := mathieuWI_wronskian a q (π / 2)
  -- the coexistence of two periodic solutions is impossible
  have hco : ¬ ∀ z, mathieuWII a q (z + 2 * π) = mathieuWII a q z := by
    intro hp
    have hp1 : ∀ z, mathieuWI a q (z + 2 * π) = mathieuWI a q z := by
      intro z
      rw [show z + 2 * π = z + π + π by ring, p1a1_mathieuWI_mathieuA_add_pi,
        p1a1_mathieuWI_mathieuA_add_pi, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
      rfl
    obtain ⟨c, hc⟩ := hince hq' h1 (fun h => by simpa [h10] using congrFun h 0) hp1 h2 hp
    have := congrFun hc 0
    rw [h20, h10, mul_one] at this
    rw [← this] at hc
    have := congrArg (fun f => deriv f 0) hc
    simp [h21] at this
  intro hC
  simp only [mathieuFeC, hnq, ↓reduceIte] at hC
  have hc0 : (mathieuCeZero n q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mathieuCeZero_pos n q).ne'
  rcases mul_eq_zero.mp ((div_eq_zero_iff.mp hC).resolve_right hc0) with hd | hμ
  · have hpos := p1a1_integral_normSq_pos_of_ne_zero (f := fun z => mathieuFeU n z q)
      (by
        unfold mathieuFeU
        have := h1.differentiable; have := h2.differentiable
        fun_prop)
      (by
        intro h0
        apply hq'
        refine p1a1_q_eq_zero_of_mathieuWII_eq (a := a) (μ := mathieuFeMu n q) (fun z => ?_)
        have := congrFun h0 z
        simp only [mathieuFeU, Pi.zero_apply] at this
        linear_combination this)
    have hd' : mathieuFeDerivZero n q = 0 := by exact_mod_cast hd
    rw [mathieuFeDerivZero, Real.sqrt_eq_zero'] at hd'
    have := div_pos Real.pi_pos hpos
    linarith
  · have hπ0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [mathieuFeMu, div_eq_zero_iff, or_iff_left hπ0] at hμ
    have hI : mathieuWI a q π = (-1) ^ n := by
      have := p1a1_mathieuWI_mathieuA_add_pi n q 0; rwa [zero_add, h10, mul_one] at this
    rw [hI] at hμ
    have hB : mathieuWII a q π = 0 := (mul_eq_zero.mp hμ).resolve_left (pow_ne_zero _ (by norm_num))
    rw [mathieuWII_pi] at hB
    rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
    · have hA' : deriv (mathieuWI a q) (π / 2) = 0 := by
        have := deriv_mathieuWI_half_pi_mathieuA_even k q; rw [← hk] at this; exact this
      rcases mul_eq_zero.mp hB with hB | hB
      · rcases mul_eq_zero.mp hB with hB | hB
        · norm_num at hB
        · apply hco; intro z
          rw [show z + 2 * π = z + π + π by ring, m28a_mathieuWII_periodic hB,
            m28a_mathieuWII_periodic hB]
      · rw [hA', hB] at hW; simp at hW
    · have hA : mathieuWI a q (π / 2) = 0 := by
        have := mathieuWI_half_pi_mathieuA_odd k q; rw [← hk] at this; exact this
      rcases mul_eq_zero.mp hB with hB | hB
      · rcases mul_eq_zero.mp hB with hB | hB
        · norm_num at hB
        · rw [hA, hB] at hW; simp at hW
      · apply hco; intro z
        rw [show z + 2 * π = z + π + π by ring, m28a_mathieuWII_antiperiodic hB,
          m28a_mathieuWII_antiperiodic hB, neg_neg]

/-- `S_n(q) ≠ 0` for real `q ≠ 0` and `n ≥ 1` (Ince's theorem, DLMF §28.5(i)). -/
@[dlmf 28.5.i]
theorem mathieuGeS_ne_zero {n : ℕ} (hn : n ≠ 0) {q : ℝ} (hq : q ≠ 0) : mathieuGeS n q ≠ 0 := by
  have hince := @mathieu_ince
  have hq' : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
  set b : ℂ := (mathieuB n q : ℂ)
  obtain ⟨h1, h10, h11⟩ := mathieuWI_spec b q
  obtain ⟨h2, h20, h21⟩ := mathieuWII_spec b q
  have hW := mathieuWI_wronskian b q (π / 2)
  have hco : ¬ ∀ z, mathieuWI b q (z + 2 * π) = mathieuWI b q z := by
    intro hp
    have hp2 : ∀ z, mathieuWII b q (z + 2 * π) = mathieuWII b q z := by
      intro z
      rw [show z + 2 * π = z + π + π by ring, p1a1_mathieuWII_mathieuB_add_pi hn,
        p1a1_mathieuWII_mathieuB_add_pi hn, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
      rfl
    obtain ⟨c, hc⟩ := hince hq' h2 (fun h => by
      have := congrArg (fun f => deriv f 0) h; simp [h21] at this) hp2 h1 hp
    have := congrFun hc 0
    rw [h20, h10, mul_zero] at this
    exact one_ne_zero this
  intro hS
  simp only [mathieuGeS] at hS
  have hs0 : (mathieuSeDerivZero n q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mathieuSeDerivZero_pos n q).ne'
  rcases mul_eq_zero.mp ((div_eq_zero_iff.mp hS).resolve_right hs0) with hd | hμ
  · have hpos := p1a1_integral_normSq_pos_of_ne_zero (f := fun z => mathieuGeU n z q)
      (by
        unfold mathieuGeU
        have := h1.differentiable; have := h2.differentiable
        fun_prop)
      (by
        intro h0
        have := congrFun h0 0
        simp only [mathieuGeU, Pi.zero_apply, mul_zero, zero_mul, sub_zero] at this
        exact one_ne_zero ((mathieuWI_spec _ _).2.1.symm.trans this))
    have hd' : mathieuGeZero n q = 0 := by exact_mod_cast hd
    rw [mathieuGeZero, Real.sqrt_eq_zero'] at hd'
    have := div_pos Real.pi_pos hpos
    linarith
  · have hπ0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [mathieuGeMu, div_eq_zero_iff, or_iff_left hπ0] at hμ
    have hBπ : mathieuWII b q π = 0 := by
      have := p1a1_mathieuWII_mathieuB_add_pi hn q 0; rwa [zero_add, h20, mul_zero] at this
    have hWπ := mathieuWI_wronskian b q π
    rw [hBπ, mul_zero, sub_zero, mathieuWI_pi_eq_deriv_mathieuWII_pi] at hWπ
    have hB'π : deriv (mathieuWII b q) π ≠ 0 := fun h => by rw [h] at hWπ; simp at hWπ
    have hA'π := (mul_eq_zero.mp hμ).resolve_right hB'π
    rw [deriv_mathieuWI_pi] at hA'π
    rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hB : mathieuWII b q (π / 2) = 0 := by
        have := mathieuWII_half_pi_mathieuB_even j q
        rw [show 2 * j + 2 = 2 * (j + 1) by ring, ← hk] at this; exact this
      rcases mul_eq_zero.mp hA'π with hA | hA
      · rcases mul_eq_zero.mp hA with hA | hA
        · norm_num at hA
        · rw [hA, hB] at hW; simp at hW
      · apply hco; intro z
        rw [show z + 2 * π = z + π + π by ring, m28a_mathieuWI_periodic hA,
          m28a_mathieuWI_periodic hA]
    · have hB' : deriv (mathieuWII b q) (π / 2) = 0 := by
        have := deriv_mathieuWII_half_pi_mathieuB_odd k q; rw [← hk] at this; exact this
      rcases mul_eq_zero.mp hA'π with hA | hA
      · rcases mul_eq_zero.mp hA with hA | hA
        · norm_num at hA
        · apply hco; intro z
          rw [show z + 2 * π = z + π + π by ring, m28a_mathieuWI_antiperiodic hA,
            m28a_mathieuWI_antiperiodic hA, neg_neg]
      · rw [hA, hB'] at hW; simp at hW

/-- **DLMF 28.5.3**: `f_{2m}(z, q)` is `π`-periodic and odd, `f_{2m+1}(z, q)` is
`π`-antiperiodic and odd (real `q ≠ 0`). -/
@[dlmf 28.5.E3]
theorem mathieuFeF_periodicity (m : ℕ) {q : ℝ} (hq : q ≠ 0) (z : ℂ) :
    mathieuFeF (2 * m) (z + π) q = mathieuFeF (2 * m) z q ∧
      mathieuFeF (2 * m) (-z) q = -mathieuFeF (2 * m) z q ∧
      mathieuFeF (2 * m + 1) (z + π) q = -mathieuFeF (2 * m + 1) z q ∧
      mathieuFeF (2 * m + 1) (-z) q = -mathieuFeF (2 * m + 1) z q := by
  have h0 := mathieuFeC_ne_zero (2 * m) hq
  have h1 := mathieuFeC_ne_zero (2 * m + 1) hq
  refine ⟨?_, p1a1_mathieuFeF_neg hq h0 z, ?_, p1a1_mathieuFeF_neg hq h1 z⟩
  · rw [p1a1_mathieuFeF_add_pi hq h0, pow_mul]; simp
  · rw [p1a1_mathieuFeF_add_pi hq h1, pow_succ, pow_mul]; simp

/-- **DLMF 28.5.4**: `g_{2m+1}(z, q)` is `π`-antiperiodic and even, `g_{2m+2}(z, q)` is
`π`-periodic and even (real `q ≠ 0`). -/
@[dlmf 28.5.E4]
theorem mathieuGeG_periodicity (m : ℕ) {q : ℝ} (hq : q ≠ 0) (z : ℂ) :
    mathieuGeG (2 * m + 1) (z + π) q = -mathieuGeG (2 * m + 1) z q ∧
      mathieuGeG (2 * m + 1) (-z) q = mathieuGeG (2 * m + 1) z q ∧
      mathieuGeG (2 * m + 2) (z + π) q = mathieuGeG (2 * m + 2) z q ∧
      mathieuGeG (2 * m + 2) (-z) q = mathieuGeG (2 * m + 2) z q := by
  have h1 := mathieuGeS_ne_zero (n := 2 * m + 1) (by omega) hq
  have h2 := mathieuGeS_ne_zero (n := 2 * m + 2) (by omega) hq
  refine ⟨?_, p1a1_mathieuGeG_neg h1 z, ?_, p1a1_mathieuGeG_neg h2 z⟩
  · rw [p1a1_mathieuGeG_add_pi (by omega) h1, pow_succ, pow_mul]; simp
  · rw [p1a1_mathieuGeG_add_pi (by omega) h2, pow_succ, pow_succ, pow_mul]; simp

/-- **Uniqueness of `f_n`** (DLMF §28.5(i)): for real `q ≠ 0`, if
`fe_n = c (z ce_n + h)` with `h` odd and `π`-periodic (`n` even) or `π`-antiperiodic (`n` odd),
then `c = C_n(q)` and `h = f_n(·, q)`. -/
@[dlmf 28.5.i]
theorem mathieuFeF_unique {n : ℕ} {q : ℝ} (hq : q ≠ 0) {c : ℂ} {h : ℂ → ℂ}
    (hh : ∀ z, h (z + π) = (-1) ^ n * h z) (hodd : ∀ z, h (-z) = -h z)
    (he : ∀ z, mathieuFe n z q = c * (z * mathieuCe n z q + h z)) :
    c = mathieuFeC n q ∧ h = fun z => mathieuFeF n z q := by
  have hC := mathieuFeC_ne_zero n hq
  have hfe := mathieuFe_eq hC
  have hσ : ((-1 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h0 : h 0 = 0 := by have := hodd 0; rw [neg_zero] at this; linear_combination this / 2
  have f0 : mathieuFeF n 0 q = 0 := by
    have := p1a1_mathieuFeF_neg hq hC 0; rw [neg_zero] at this; linear_combination this / 2
  have hπ' : h π = 0 := by rw [show (π : ℂ) = 0 + π by ring, hh, h0, mul_zero]
  have fπ : mathieuFeF n π q = 0 := by
    rw [show (π : ℂ) = 0 + π by ring, p1a1_mathieuFeF_add_pi hq hC, f0, mul_zero]
  have ceπ : mathieuCe n π q ≠ 0 := by
    rw [mathieuCe, show (π : ℂ) = 0 + π by ring, p1a1_mathieuWI_mathieuA_add_pi,
      (mathieuWI_spec _ _).2.1, mul_one]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mathieuCeZero_pos n q).ne') hσ
  have hπ0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have e := (he π).symm.trans (hfe π)
  rw [hπ', fπ] at e
  simp only [add_zero] at e
  have hc : c = mathieuFeC n q := mul_right_cancel₀ (mul_ne_zero hπ0 ceπ) e
  refine ⟨hc, funext fun z => ?_⟩
  have e2 := (he z).symm.trans (hfe z)
  rw [hc] at e2
  have := mul_left_cancel₀ hC e2
  linear_combination this

/-- **Uniqueness of `g_n`** (DLMF §28.5(i)): for real `q ≠ 0`, `n ≥ 1`, if
`ge_n = c (z se_n + h)` with `h` even and `π`-(anti)periodic like `se_n`, then `c = S_n(q)` and
`h = g_n(·, q)`. -/
@[dlmf 28.5.i]
theorem mathieuGeG_unique {n : ℕ} (hn : n ≠ 0) {q : ℝ} (hq : q ≠ 0) {c : ℂ} {h : ℂ → ℂ}
    (hh : ∀ z, h (z + π) = (-1) ^ n * h z) (heven : ∀ z, h (-z) = h z)
    (he : ∀ z, mathieuGe n z q = c * (z * mathieuSe n z q + h z)) :
    c = mathieuGeS n q ∧ h = fun z => mathieuGeG n z q := by
  have hS := mathieuGeS_ne_zero hn hq
  have hge := mathieuGe_eq hS
  set σ : ℂ := (-1) ^ n
  have hσ2 : σ * σ = 1 := by rw [← pow_two, ← pow_mul, mul_comm, pow_mul]; simp
  have hse : ∀ z, mathieuSe n (z + π) q = σ * mathieuSe n z q := by
    intro z; simp only [mathieuSe]; rw [p1a1_mathieuWII_mathieuB_add_pi hn]; ring
  have key : ∀ z, (c - mathieuGeS n q) * π * mathieuSe n z q = 0 := by
    intro z
    have E1 := (he z).symm.trans (hge z)
    have E2 := (he (z + π)).symm.trans (hge (z + π))
    rw [hse, hh, p1a1_mathieuGeG_add_pi hn hS] at E2
    linear_combination σ * E2 - E1 - (c * ((z + π) * mathieuSe n z q + h z) -
      mathieuGeS n q * ((z + π) * mathieuSe n z q + mathieuGeG n z q)) * hσ2
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : c = mathieuGeS n q := by
    by_contra hne
    have h0 : (fun z => mathieuSe n z q) = fun _ => 0 := by
      funext z
      have := key z
      rcases mul_eq_zero.mp this with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd (sub_eq_zero.mp h2) hne
        · exact absurd h2 hπ
      · exact h1
    have := deriv_mathieuSe_zero n q
    rw [h0, deriv_const] at this
    exact (mathieuSeDerivZero_pos n q).ne' (by exact_mod_cast this.symm)
  refine ⟨hc, funext fun z => ?_⟩
  have E1 := (he z).symm.trans (hge z)
  rw [hc] at E1
  have := mul_left_cancel₀ hS E1
  linear_combination this

/-- **DLMF 28.5.5**: `C_n(q)² ∫₀^{2π} f_n(x, q)² dx = S_n(q)² ∫₀^{2π} g_n(x, q)² dx = π`
(real `q ≠ 0`, `n ≥ 1` for the second). -/
@[dlmf 28.5.E5]
theorem mathieuFe_mathieuGe_normalization {n : ℕ} {q : ℝ} (hq : q ≠ 0) :
    mathieuFeC n q ^ 2 * ∫ x in (0 : ℝ)..2 * π, mathieuFeF n x q ^ 2 = π ∧
      (n ≠ 0 → mathieuGeS n q ^ 2 * ∫ x in (0 : ℝ)..2 * π, mathieuGeG n x q ^ 2 = π) :=
  ⟨p1a1_fe_normalization hq (mathieuFeC_ne_zero n hq),
    fun hn => p1a1_ge_normalization (mathieuGeS_ne_zero hn hq)⟩

/-- **Limits as `q → 0`** (DLMF §28.5(i)): for `n ≠ 0`, `C_n(q) → 0`, `S_n(q) → 0`,
`C_n(q) f_n(z, q) → sin nz` and `S_n(q) g_n(z, q) → cos nz`. -/
@[dlmf 28.5.i]
theorem mathieuFeC_mathieuGeS_tendsto {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    Tendsto (fun q : ℝ => mathieuFeC n q) (𝓝[≠] 0) (𝓝 0) ∧
      Tendsto (fun q : ℝ => mathieuGeS n q) (𝓝[≠] 0) (𝓝 0) ∧
      Tendsto (fun q : ℝ => mathieuFeC n q * mathieuFeF n z q) (𝓝[≠] 0)
        (𝓝 (Complex.sin (n * z))) ∧
      Tendsto (fun q : ℝ => mathieuGeS n q * mathieuGeG n z q) (𝓝[≠] 0)
        (𝓝 (Complex.cos (n * z))) := by
  sorry

/-- **DLMF 28.5.6** (first relation): `C_{2m}(-q) = C_{2m}(q)`. -/
@[dlmf 28.5.E6]
theorem mathieuFeC_even_neg (m : ℕ) (q : ℝ) : mathieuFeC (2 * m) (-q) = mathieuFeC (2 * m) q :=
  p1a1_C_even_neg m q

/-- **DLMF 28.5.6** (second relation, **corrected sign**): `C_{2m+1}(-q) = -S_{2m+1}(q)`
(DLMF prints `C_{2m+1}(-q) = S_{2m+1}(q)`, which contradicts its own sign rule; see the module
docstring). -/
@[dlmf 28.5.E6]
theorem mathieuFeC_odd_neg (m : ℕ) (q : ℝ) :
    mathieuFeC (2 * m + 1) (-q) = -mathieuGeS (2 * m + 1) q :=
  p1a1_C_odd_neg m q

/-- **DLMF 28.5.6** (third relation): `S_{2m+2}(-q) = S_{2m+2}(q)`. -/
@[dlmf 28.5.E6]
theorem mathieuGeS_even_neg (m : ℕ) (q : ℝ) :
    mathieuGeS (2 * m + 2) (-q) = mathieuGeS (2 * m + 2) q :=
  p1a1_S_even_neg m q

/-- **DLMF 28.5.7**: `fe_0(z, 0) = z`. -/
@[dlmf 28.5.E7]
theorem mathieuFe_zero_zero (z : ℂ) : mathieuFe 0 z 0 = z := by
  simp [mathieuFe]

/-- **DLMF 28.5.7**: `fe_n(z, 0) = sin nz`, `n = 1, 2, 3, …`. -/
@[dlmf 28.5.E7]
theorem mathieuFe_q_zero {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    mathieuFe n z 0 = Complex.sin (n * z) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hμ : mathieuFeMu n 0 = 0 := by
    rw [mathieuFeMu, mathieuA_zero, p1a1_mathieuWII_sq_q_zero hn]
    simp [Complex.sin_nat_mul_pi]
  have hU : ∀ x : ℂ, mathieuFeU n x 0 = Complex.sin (n * x) / n := by
    intro x; rw [mathieuFeU, hμ, mathieuA_zero, p1a1_mathieuWII_sq_q_zero hn]; ring
  simp only [mathieuFe, hn, false_and, ↓reduceIte, mathieuFeDerivZero, hU,
    p1a1_norm_sin_div_sq]
  rw [mathieuA_zero, p1a1_mathieuWII_sq_q_zero hn, intervalIntegral.integral_div,
    p1a1_integral_sin_sq hn,
    show π / (π / (n : ℝ) ^ 2) = (n : ℝ) ^ 2 by field_simp, Real.sqrt_sq (Nat.cast_nonneg n)]
  push_cast; field_simp

/-- **DLMF 28.5.7**: `ge_n(z, 0) = cos nz`, `n = 1, 2, 3, …`. -/
@[dlmf 28.5.E7]
theorem mathieuGe_q_zero {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    mathieuGe n z 0 = Complex.cos (n * z) := by
  have hμ : mathieuGeMu n 0 = 0 := by
    rw [mathieuGeMu, mathieuB_zero hn, p1a1_mathieuWI_sq_q_zero n]
    rw [(p1a1_hasDerivAt_cos_mul (n : ℂ) π).deriv]
    simp [Complex.sin_nat_mul_pi]
  have hU : ∀ x : ℂ, mathieuGeU n x 0 = Complex.cos (n * x) := by
    intro x; rw [mathieuGeU, hμ, mathieuB_zero hn, p1a1_mathieuWI_sq_q_zero n]; ring
  simp only [mathieuGe, mathieuGeZero, hU, p1a1_norm_cos_sq]
  rw [mathieuB_zero hn, p1a1_mathieuWI_sq_q_zero n, p1a1_integral_cos_sq hn,
    div_self Real.pi_ne_zero, Real.sqrt_one, Complex.ofReal_one, one_mul]

/-- **Unboundedness** (DLMF §28.5(i)): for real `q ≠ 0`, every real-axis solution of Mathieu's
equation with `a = a_n(q)` that is not a multiple of `ce_n` is unbounded as `z → +∞` and as
`z → -∞` on `ℝ`; likewise for `a = b_n(q)`, `n ≥ 1`, and `se_n`. -/
@[dlmf 28.5.i]
theorem mathieu_secular_unbounded {n : ℕ} {q : ℝ} (hq : q ≠ 0) {w : ℂ → ℂ}
    (hw : IsMathieuSolution (mathieuA n q) q w)
    (hind : ∀ c : ℂ, w ≠ fun z => c * mathieuCe n z q) :
    ¬ BddAbove (Set.range fun x : Ici (0 : ℝ) => ‖w (x : ℝ)‖) ∧
      ¬ BddAbove (Set.range fun x : Iic (0 : ℝ) => ‖w (x : ℝ)‖) := by
  have hC := mathieuFeC_ne_zero n hq
  set a : ℂ := (mathieuA n q : ℂ)
  have hnq : ¬ (n = 0 ∧ q = 0) := fun h => hq h.2
  obtain ⟨h1, h10, h11⟩ := mathieuWI_spec a q
  obtain ⟨h2, h20, h21⟩ := mathieuWII_spec a q
  set μ := mathieuFeMu n q
  have hμ : μ ≠ 0 := by
    intro h; apply hC; simp only [mathieuFeC, hnq, ↓reduceIte]
    rw [show mathieuFeMu n q = 0 from h]; simp
  have hw1 : deriv w 0 ≠ 0 := by
    intro h0
    apply hind (w 0 / mathieuCeZero n q)
    have hc : (mathieuCeZero n q : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (mathieuCeZero_pos n q).ne'
    funext z
    conv_lhs => rw [hw.eq_combination]
    simp only [h0, mathieuCe, zero_mul, add_zero]
    field_simp
    rfl
  set σ : ℂ := (-1) ^ n
  have hσ : ‖σ‖ = 1 := by simp [σ]
  have hI : ∀ k : ℕ, mathieuWI a q (k * π) = σ ^ k := by
    intro k; induction k with
    | zero => simp [h10]
    | succ k ih =>
      rw [show ((k + 1 : ℕ) : ℂ) * π = k * π + π by push_cast; ring,
        p1a1_mathieuWI_mathieuA_add_pi, ih, pow_succ, mul_comm]
  have hU : ∀ k : ℕ, mathieuFeU n (k * π) q = 0 := by
    intro k; induction k with
    | zero => simp [mathieuFeU]; exact h20
    | succ k ih =>
      rw [show ((k + 1 : ℕ) : ℂ) * π = k * π + π by push_cast; ring,
        p1a1_mathieuFeU_add_pi, ih, mul_zero]
  have hII : ∀ k : ℕ, mathieuWII a q (k * π) = μ * (k * π) * σ ^ k := by
    intro k
    have := hU k
    simp only [mathieuFeU] at this
    rw [← hI k]; linear_combination this
  have hval : ∀ k : ℕ, ‖w (k * π)‖ = ‖w 0 + deriv w 0 * μ * π * k‖ := by
    intro k
    conv_lhs => rw [hw.eq_combination]
    beta_reduce
    rw [hI, hII, show w 0 * σ ^ k + deriv w 0 * (μ * (k * π) * σ ^ k) =
      σ ^ k * (w 0 + deriv w 0 * μ * π * k) by ring, norm_mul, norm_pow, hσ, one_pow, one_mul]
  have hval' : ∀ k : ℕ, ‖w (-(k * π))‖ = ‖w 0 - deriv w 0 * μ * π * k‖ := by
    intro k
    conv_lhs => rw [hw.eq_combination]
    beta_reduce
    rw [mathieuWI_neg, mathieuWII_neg, hI, hII, show w 0 * σ ^ k + deriv w 0 * -(μ * (k * π) *
      σ ^ k) = σ ^ k * (w 0 - deriv w 0 * μ * π * k) by ring, norm_mul, norm_pow, hσ, one_pow,
      one_mul]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hK : 0 < ‖deriv w 0 * μ * π‖ := norm_pos_iff.mpr (mul_ne_zero (mul_ne_zero hw1 hμ) hπ)
  have grow : ∀ M : ℝ, ∃ k : ℕ, M < ‖w 0 + deriv w 0 * μ * π * k‖ ∧
      M < ‖w 0 - deriv w 0 * μ * π * k‖ := by
    intro M
    obtain ⟨k, hk⟩ := exists_nat_gt ((M + ‖w 0‖) / ‖deriv w 0 * μ * π‖)
    refine ⟨k, ?_, ?_⟩
    · have h1 := norm_sub_norm_le (deriv w 0 * μ * π * k) (-w 0)
      rw [sub_neg_eq_add, norm_neg, add_comm] at h1
      have h2 : ‖deriv w 0 * μ * π * (k : ℂ)‖ = ‖deriv w 0 * μ * π‖ * k := by
        rw [norm_mul]; simp
      rw [div_lt_iff₀ hK] at hk
      nlinarith
    · have h1 := norm_sub_norm_le (deriv w 0 * μ * π * k) (w 0)
      rw [norm_sub_rev] at h1
      have h2 : ‖deriv w 0 * μ * π * (k : ℂ)‖ = ‖deriv w 0 * μ * π‖ * k := by
        rw [norm_mul]; simp
      rw [div_lt_iff₀ hK] at hk
      nlinarith
  constructor
  · rintro ⟨M, hM⟩
    obtain ⟨k, hk, -⟩ := grow M
    have := hM ⟨⟨k * π, Set.mem_Ici.mpr (by positivity)⟩, rfl⟩
    simp only at this
    rw [show ((k * π : ℝ) : ℂ) = k * π by push_cast; ring, hval] at this
    linarith
  · rintro ⟨M, hM⟩
    obtain ⟨k, -, hk⟩ := grow M
    have := hM ⟨⟨-(k * π), Set.mem_Iic.mpr (neg_nonpos.mpr (by positivity))⟩, rfl⟩
    simp only at this
    rw [show ((-(k * π) : ℝ) : ℂ) = -(k * π) by push_cast; ring, hval'] at this
    linarith

/-- **DLMF 28.5.8**: `𝒲{ce_n, fe_n} = ce_n(0, q) fe_n'(0, q)` (real `q`, `(n, q) ≠ (0, 0)`). -/
@[dlmf 28.5.E8]
theorem mathieuCe_mathieuFe_wronskian {n : ℕ} {q : ℝ} (h : ¬ (n = 0 ∧ q = 0)) (z : ℂ) :
    mathieuCe n z q * deriv (fun z => mathieuFe n z q) z -
        deriv (fun z => mathieuCe n z q) z * mathieuFe n z q =
      mathieuCe n 0 q * deriv (fun z => mathieuFe n z q) 0 := by
  rw [(isMathieuSolution_mathieuCe n q).wronskian_eq (isMathieuSolution_mathieuFe h) z 0]
  have h0 : deriv (fun z => mathieuCe n z q) 0 = 0 := by
    simp only [mathieuCe]
    rw [show deriv (fun z => (mathieuCeZero n q : ℂ) * mathieuWI (mathieuA n q) q z) 0 =
        (mathieuCeZero n q : ℂ) * deriv (mathieuWI (mathieuA n q) q) 0 from
      (((isMathieuSolution_mathieuWI _ _).differentiable 0).hasDerivAt.const_mul _).deriv,
      (mathieuWI_spec _ _).2.2, mul_zero]
  rw [h0, zero_mul, sub_zero]

/-- **DLMF 28.5.9**: `𝒲{se_n, ge_n} = -se_n'(0, q) ge_n(0, q)` (real `q`). -/
@[dlmf 28.5.E9]
theorem mathieuSe_mathieuGe_wronskian (n : ℕ) (q : ℝ) (z : ℂ) :
    mathieuSe n z q * deriv (fun z => mathieuGe n z q) z -
        deriv (fun z => mathieuSe n z q) z * mathieuGe n z q =
      -(deriv (fun z => mathieuSe n z q) 0 * mathieuGe n 0 q) := by
  rw [(isMathieuSolution_mathieuSe n q).wronskian_eq (isMathieuSolution_mathieuGe n q) z 0]
  have h0 : mathieuSe n 0 q = 0 := by simp [mathieuSe, (mathieuWII_spec _ _).2.1]
  rw [h0, zero_mul, zero_sub]

end DLMF.Mathieu
