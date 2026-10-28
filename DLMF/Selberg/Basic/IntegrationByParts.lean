/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Complex.TaylorSeries
public import DLMF.Hypergeometric.Identities

/-!
# Selberg integration by parts and Aomoto recurrences

Selberg integral definitions, cube integrability and integration-by-parts identities give the
Aomoto parameter recurrence.

Source references and common attribution are retained in
`DLMF.Selberg.Basic`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter

open scoped Real Topology

noncomputable section

namespace DLMF.Selberg

/-- The Selberg integrand on `[0,1]^n` (AAR §8.1). -/
def selbergIntegrand (n : ℕ) (a b c : ℂ) (t : Fin n → ℝ) : ℂ :=
  (∏ i : Fin n, (t i : ℂ) ^ (a - 1) * (1 - (t i : ℂ)) ^ (b - 1)) *
    ∏ i : Fin n, ∏ j : Fin n,
      if i.val < j.val then ((abs (t i - t j) : ℝ) : ℂ) ^ (2 * c) else 1

/-- The closed unit cube `[0,1]ⁿ`. -/
abbrev cube (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

/-- The unit cube `[0,1]ⁿ` is measurable. -/
theorem measurableSet_cube (n : ℕ) : MeasurableSet (cube n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- `(x, y)` lies in `[0,1]ⁿ⁺¹` iff `x ∈ [0,1]` and `y ∈ [0,1]ⁿ`. -/
theorem cons_mem_cube {n : ℕ} {x : ℝ} {y : Fin n → ℝ} :
    (Fin.cons x y : Fin (n + 1) → ℝ) ∈ cube (n + 1) ↔ x ∈ Icc (0 : ℝ) 1 ∧ y ∈ cube n := by
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Fin.forall_fin_succ, Fin.cons_zero,
    Fin.cons_succ]

/-- Splitting off the zeroth coordinate. -/
theorem integral_cube_succ {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℂ)
    (hg : IntegrableOn g (cube (n + 1))) :
    ∫ t in cube (n + 1), g t = ∫ y in cube n, ∫ x in Icc (0 : ℝ) 1, g (Fin.cons x y) := by
  have e := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have hpre : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm ⁻¹'
      (cube (n + 1)) = Icc (0 : ℝ) 1 ×ˢ cube n := by
    ext ⟨x, y⟩
    simp only [Set.mem_preimage, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.insertNth_zero', Set.mem_prod]
    exact cons_mem_cube
  have hsymm : ∀ p : ℝ × (Fin n → ℝ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p = Fin.cons p.1 p.2 := by
    intro p
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.insertNth_zero']
  have h1 : ∫ t in cube (n + 1), g t =
      ∫ p in Icc (0 : ℝ) 1 ×ˢ cube n, g (Fin.cons p.1 p.2) := by
    rw [← hpre, ← e.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _)]
    simp only [hsymm]
  have hint : IntegrableOn (fun p : ℝ × (Fin n → ℝ) => g (Fin.cons p.1 p.2))
      (Icc (0 : ℝ) 1 ×ˢ cube n) := by
    rw [← hpre]
    have := (e.integrableOn_comp_preimage (MeasurableEquiv.measurableEmbedding _)).mpr hg
    simpa only [Function.comp_def, hsymm] using this
  rw [Measure.volume_eq_prod] at h1 hint
  rw [h1, setIntegral_prod _ hint, integral_integral_swap]
  rw [IntegrableOn, ← Measure.prod_restrict] at hint
  exact hint

/-- The one-variable Selberg weight `x^{a-1}(1-x)^{b-1}`. -/
def weight (a b : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ (a - 1) * (1 - (x : ℂ)) ^ (b - 1)

/-- The Vandermonde factor `∏_{i<j} |tᵢ - tⱼ|^{2c}`. -/
def vdm (n : ℕ) (c : ℂ) (t : Fin n → ℝ) : ℂ :=
  ∏ i : Fin n, ∏ j : Fin n, if i.val < j.val then ((|t i - t j| : ℝ) : ℂ) ^ (2 * c) else 1

/-- The Selberg integrand is the product of the one-variable weights times the
Vandermonde factor. -/
theorem selbergIntegrand_eq (n : ℕ) (a b c : ℂ) (t : Fin n → ℝ) :
    selbergIntegrand n a b c t = (∏ i, weight a b (t i)) * vdm n c t := rfl

/-- Splitting off the first coordinate: `Δ(x, y)^{2c} = ∏ⱼ |x - yⱼ|^{2c} · Δ(y)^{2c}`. -/
theorem vdm_cons {n : ℕ} (c : ℂ) (x : ℝ) (y : Fin n → ℝ) :
    vdm (n + 1) c (Fin.cons x y) =
      (∏ j : Fin n, ((|x - y j| : ℝ) : ℂ) ^ (2 * c)) * vdm n c y := by
  simp only [vdm, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ]
  simp

/-- Splitting off the first coordinate of the Selberg integrand. -/
theorem selbergIntegrand_cons {n : ℕ} (a b c : ℂ) (x : ℝ) (y : Fin n → ℝ) :
    selbergIntegrand (n + 1) a b c (Fin.cons x y) =
      weight a b x * (∏ j : Fin n, ((|x - y j| : ℝ) : ℂ) ^ (2 * c)) *
        selbergIntegrand n a b c y := by
  rw [selbergIntegrand_eq, selbergIntegrand_eq, vdm_cons, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-- For `x ≥ 0`, `x^{2c} = x^c · x^c`. -/
theorem ofReal_cpow_two_mul {x : ℝ} (hx : 0 ≤ x) (c : ℂ) :
    (x : ℂ) ^ (2 * c) = (x : ℂ) ^ c * (x : ℂ) ^ c := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rcases eq_or_ne c 0 with rfl | hc
    · simp
    · simp [Complex.zero_cpow hc, Complex.zero_cpow (mul_ne_zero two_ne_zero hc)]
  · rw [two_mul, Complex.cpow_add _ _ (by exact_mod_cast hx0)]

/-- Symmetric form of the Vandermonde factor, `∏_{i ≠ j} |tᵢ - tⱼ|^c`. -/
theorem vdm_eq_sym (n : ℕ) (c : ℂ) (t : Fin n → ℝ) :
    vdm n c t = ∏ i : Fin n, ∏ j : Fin n,
      if i ≠ j then ((|t i - t j| : ℝ) : ℂ) ^ c else 1 := by
  have hsplit : ∀ i j : Fin n, (if i ≠ j then ((|t i - t j| : ℝ) : ℂ) ^ c else 1) =
      (if i.val < j.val then ((|t i - t j| : ℝ) : ℂ) ^ c else 1) *
        (if j.val < i.val then ((|t i - t j| : ℝ) : ℂ) ^ c else 1) := by
    intro i j
    rcases lt_trichotomy i.val j.val with h | h | h
    · have : i ≠ j := Fin.ne_of_val_ne (Nat.ne_of_lt h)
      simp [h, this, Nat.lt_asymm h]
    · have : i = j := Fin.ext h
      subst this; simp
    · have : i ≠ j := Fin.ne_of_val_ne (Nat.ne_of_gt h)
      simp [h, this, Nat.lt_asymm h]
  simp_rw [hsplit, Finset.prod_mul_distrib]
  rw [Finset.prod_comm (f := fun i j =>
    if j.val < i.val then ((|t i - t j| : ℝ) : ℂ) ^ c else 1)]
  rw [vdm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases h : i.val < j.val
  · simp only [h, ite_true]
    rw [abs_sub_comm (t j) (t i)]
    exact ofReal_cpow_two_mul (abs_nonneg _) c
  · simp [h]

/-- The Vandermonde factor `∏_{i<j} |tᵢ - tⱼ|^{2c}` is symmetric under permutations. -/
theorem vdm_comp_perm (n : ℕ) (c : ℂ) (t : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    vdm n c (t ∘ σ) = vdm n c t := by
  rw [vdm_eq_sym, vdm_eq_sym]
  simp only [Function.comp_apply]
  rw [← Equiv.prod_comp σ (fun i => ∏ j : Fin n,
    if i ≠ j then ((|t i - t j| : ℝ) : ℂ) ^ c else 1)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Equiv.prod_comp σ (fun j => if σ i ≠ j then ((|t (σ i) - t j| : ℝ) : ℂ) ^ c else 1)]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [ne_eq, σ.injective.eq_iff]

/-- The Selberg integrand is symmetric under permutations of the variables. -/
theorem selbergIntegrand_comp_perm (n : ℕ) (a b c : ℂ) (t : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    selbergIntegrand n a b c (t ∘ σ) = selbergIntegrand n a b c t := by
  rw [selbergIntegrand_eq, selbergIntegrand_eq, vdm_comp_perm]
  congr 1
  exact Equiv.prod_comp σ (fun i => weight a b (t i))

/-- The cube `[0,1]ⁿ` is invariant under permutations of the coordinates. -/
theorem comp_perm_mem_cube {n : ℕ} (t : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    t ∘ σ ∈ cube n ↔ t ∈ cube n := by
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Function.comp_apply]
  exact ⟨fun h i => by simpa using h (σ.symm i), fun h i => h (σ i)⟩

/-- Integrals over the cube are invariant under permutations of the coordinates. -/
theorem integral_cube_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (g : (Fin n → ℝ) → ℂ) :
    ∫ t in cube n, g (t ∘ σ) = ∫ t in cube n, g t := by
  have e := volume_preserving_arrowCongr' (α₁ := Fin n) (α₂ := Fin n) σ.symm
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id volume)
  have hT : ∀ t : Fin n → ℝ, (MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl ℝ)) t =
      t ∘ σ := by
    intro t; ext i; simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr']
  have hpre : (MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl ℝ)) ⁻¹' cube n =
      cube n := by
    ext t; simp only [Set.mem_preimage, hT]; exact comp_perm_mem_cube t σ
  calc ∫ t in cube n, g (t ∘ σ)
      = ∫ t in (MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl ℝ)) ⁻¹' cube n,
          g ((MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl ℝ)) t) := by
        rw [hpre]; simp only [hT]
    _ = ∫ t in cube n, g t := e.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _) _ _

/-- Integrability on the cube is preserved by permuting the variables. -/
theorem integrableOn_cube_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) {g : (Fin n → ℝ) → ℂ}
    (hg : IntegrableOn g (cube n)) : IntegrableOn (fun t => g (t ∘ σ)) (cube n) := by
  have e := volume_preserving_arrowCongr' (α₁ := Fin n) (α₂ := Fin n) σ.symm
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id volume)
  have hT : ∀ t : Fin n → ℝ, (MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl ℝ)) t =
      t ∘ σ := by
    intro t; ext i; simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr']
  have hpre : (MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl ℝ)) ⁻¹' cube n =
      cube n := by
    ext t; simp only [Set.mem_preimage, hT]; exact comp_perm_mem_cube t σ
  have := (e.integrableOn_comp_preimage (MeasurableEquiv.measurableEmbedding _)).mpr hg
  rw [hpre] at this
  simpa only [Function.comp_def, hT] using this

/-! ### One-variable integration by parts -/

/-- `∏ⱼ |x - yⱼ|^{2c}`. -/
def vprod {n : ℕ} (y : Fin n → ℝ) (c : ℂ) (x : ℝ) : ℂ :=
  ∏ j : Fin n, ((|x - y j| : ℝ) : ℂ) ^ (2 * c)

/-- For `u ≠ 0`, `|u|^w = exp(w log u)` (with the real logarithm `log u = log |u|`). -/
theorem ofReal_abs_cpow_eq_exp {u : ℝ} (hu : u ≠ 0) (w : ℂ) :
    ((|u| : ℝ) : ℂ) ^ w = Complex.exp ((Real.log u : ℂ) * w) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast abs_ne_zero.mpr hu),
    ← Complex.ofReal_log (abs_nonneg u), Real.log_abs]

/-- For `x ≠ y`, the derivative of `x ↦ |x - y|^w` is `w/(x - y) · |x - y|^w`. -/
theorem hasDerivAt_abs_sub_cpow {x y : ℝ} (hxy : x ≠ y) (w : ℂ) :
    HasDerivAt (fun x : ℝ => ((|x - y| : ℝ) : ℂ) ^ w)
      (w / ((x : ℂ) - y) * ((|x - y| : ℝ) : ℂ) ^ w) x := by
  have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hev : (fun x : ℝ => ((|x - y| : ℝ) : ℂ) ^ w) =ᶠ[𝓝 x]
      fun x : ℝ => Complex.exp ((Real.log (x - y) : ℂ) * w) := by
    filter_upwards [(continuous_sub_right y).continuousAt.eventually_ne hne] with z hz
    exact ofReal_abs_cpow_eq_exp hz w
  have hlog : HasDerivAt (fun x : ℝ => Real.log (x - y)) (1 / (x - y)) x := by
    simpa using ((hasDerivAt_id x).sub_const y).log hne
  have h := ((hlog.ofReal_comp).mul_const w).cexp
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [← ofReal_abs_cpow_eq_exp hne w]
  push_cast
  field_simp

/-- Logarithmic derivative of `∏ⱼ |x - yⱼ|^{2c}` off the points `yⱼ`. -/
theorem hasDerivAt_vprod {n : ℕ} (y : Fin n → ℝ) (c : ℂ) {x : ℝ} (hx : ∀ j, x ≠ y j) :
    HasDerivAt (vprod y c) ((∑ j : Fin n, 2 * c / ((x : ℂ) - y j)) * vprod y c x) x := by
  classical
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (f := fun j (x : ℝ) => ((|x - y j| : ℝ) : ℂ) ^ (2 * c))
    (fun j _ => hasDerivAt_abs_sub_cpow (hx j) (2 * c))
  refine h.congr_deriv ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, vprod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  ring

/-- The function differentiated in the one-variable integration by parts. -/
def ibpF {n : ℕ} (y : Fin n → ℝ) (α β c : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ α * (1 - (x : ℂ)) ^ β * vprod y c x

/-- Its derivative off the points `yⱼ`. -/
def ibpD {n : ℕ} (y : Fin n → ℝ) (α β c : ℂ) (x : ℝ) : ℂ :=
  (α * (x : ℂ) ^ (α - 1) * (1 - (x : ℂ)) ^ β - β * (x : ℂ) ^ α * (1 - (x : ℂ)) ^ (β - 1)) *
      vprod y c x +
    (x : ℂ) ^ α * (1 - (x : ℂ)) ^ β * ((∑ j : Fin n, 2 * c / ((x : ℂ) - y j)) * vprod y c x)

/-- `ibpD` is the derivative of `ibpF` on `(0,1)` away from the points `yⱼ`. -/
theorem hasDerivAt_ibpF {n : ℕ} (y : Fin n → ℝ) (α β c : ℂ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hxy : ∀ j, x ≠ y j) : HasDerivAt (ibpF y α β c) (ibpD y α β c x) x := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ α) (α * (x : ℂ) ^ (α - 1)) x := by
    have := ((hasDerivAt_id (x : ℂ)).cpow_const (c := α)
      (by simpa using Complex.ofReal_mem_slitPlane.2 hx.1)).comp_ofReal
    simpa using this
  have h2 : HasDerivAt (fun x : ℝ => (1 - (x : ℂ)) ^ β) (-(β * (1 - (x : ℂ)) ^ (β - 1))) x := by
    have hs : (1 - (x : ℂ)) ∈ slitPlane := by
      have : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
      rw [this]; exact Complex.ofReal_mem_slitPlane.2 (by linarith [hx.2])
    have := (((hasDerivAt_id (x : ℂ)).const_sub 1).cpow_const (c := β) hs).comp_ofReal
    simpa using this
  have h := (h1.mul h2).mul (hasDerivAt_vprod y c hxy)
  unfold ibpF
  refine h.congr_deriv ?_
  unfold ibpD
  simp only [Pi.mul_apply]
  ring

/-- For `y ∈ [0,1]ⁿ`, `x ∈ [0,1]` and `Re c ≥ 0`, `‖∏ⱼ |x - yⱼ|^{2c}‖ ≤ 1`. -/
theorem norm_vprod_le {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ cube n) {c : ℂ} (hc : 0 ≤ c.re)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : ‖vprod y c x‖ ≤ 1 := by
  unfold vprod
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
  have hyj := hy j (Set.mem_univ _)
  have hle : |x - y j| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hyj.1, hyj.2]
  rcases eq_or_lt_of_le (abs_nonneg (x - y j)) with h0 | hpos
  · rw [← h0]
    rcases eq_or_ne c 0 with rfl | hc0
    · simp
    · simp [Complex.zero_cpow (mul_ne_zero two_ne_zero hc0)]
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    exact Real.rpow_le_one (abs_nonneg _) hle (by simp; linarith)

/-- `‖2c/(x-yⱼ) · ∏ₖ |x-yₖ|^{2c}‖ ≤ 2‖c‖` when `Re c ≥ 1/2`. -/
theorem norm_div_mul_vprod_le {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ cube n) {c : ℂ}
    (hc : 1 / 2 ≤ c.re) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (j : Fin n) :
    ‖2 * c / ((x : ℂ) - y j) * vprod y c x‖ ≤ 2 * ‖c‖ := by
  classical
  rcases eq_or_ne x (y j) with hxy | hxy
  · simp [hxy]
  have hyj := hy j (Set.mem_univ _)
  have hpos : 0 < |x - y j| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hle : |x - y j| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hyj.1, hyj.2]
  unfold vprod
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), norm_mul, norm_mul]
  have hrest : ‖∏ k ∈ Finset.univ.erase j, ((|x - y k| : ℝ) : ℂ) ^ (2 * c)‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun k _ => ?_
    have := norm_vprod_le (y := fun _ : Fin 1 => y k) (fun _ _ => hy k (Set.mem_univ _))
      (c := c) (by linarith) hx
    simpa [vprod] using this
  have hj : ‖((|x - y j| : ℝ) : ℂ) ^ (2 * c)‖ ≤ |x - y j| := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    calc |x - y j| ^ (2 * c).re ≤ |x - y j| ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hpos hle (by simp; linarith)
      _ = |x - y j| := Real.rpow_one _
  have hd : ‖2 * c / ((x : ℂ) - y j)‖ = 2 * ‖c‖ / |x - y j| := by
    rw [norm_div, norm_mul, show ((x : ℂ) - y j) = ((x - y j : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    simp
  rw [hd]
  calc 2 * ‖c‖ / |x - y j| * (‖((|x - y j| : ℝ) : ℂ) ^ (2 * c)‖ *
        ‖∏ k ∈ Finset.univ.erase j, ((|x - y k| : ℝ) : ℂ) ^ (2 * c)‖)
      ≤ 2 * ‖c‖ / |x - y j| * (|x - y j| * 1) := by gcongr
    _ = 2 * ‖c‖ := by field_simp

/-- The cast of `1 - x` from `ℝ` to `ℂ`. -/
theorem one_sub_ofReal (x : ℝ) : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; ring

/-- `x ↦ ∏ⱼ |x - yⱼ|^{2c}` is measurable. -/
theorem measurable_vprod {n : ℕ} (y : Fin n → ℝ) (c : ℂ) : Measurable (vprod y c) := by
  unfold vprod
  fun_prop

/-- The integration-by-parts derivative `ibpD` is measurable. -/
theorem measurable_ibpD {n : ℕ} (y : Fin n → ℝ) (α β c : ℂ) : Measurable (ibpD y α β c) := by
  unfold ibpD
  have := measurable_vprod y c
  fun_prop

/-- The integration-by-parts function `ibpF` is continuous on `[0,1]`. -/
theorem continuousOn_ibpF {n : ℕ} (y : Fin n → ℝ) {α β c : ℂ} (hα : 0 < α.re)
    (hβ : 0 < β.re ∨ β = 0) (hc : 0 < c.re) : ContinuousOn (ibpF y α β c) (Icc 0 1) := by
  refine continuousOn_of_forall_continuousAt fun x _ => ?_
  unfold ibpF vprod
  refine ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_
  · exact continuousAt_ofReal_cpow_const x α (Or.inl hα)
  · rcases hβ with hβ | rfl
    · simp_rw [one_sub_ofReal]
      exact (continuousAt_ofReal_cpow_const (1 - x) β (Or.inl hβ)).comp
        (continuous_const.sub continuous_id).continuousAt
    · simp only [Complex.cpow_zero]; exact continuousAt_const
  · refine tendsto_finsetProd _ fun j _ => ?_
    have hg : ContinuousAt (fun x : ℝ => |x - y j|) x :=
      (continuous_id.sub continuous_const).abs.continuousAt
    have hc2 : 0 < (2 * c).re := by simp; linarith
    exact ContinuousAt.comp (f := fun x : ℝ => |x - y j|) (g := fun z : ℝ => (z : ℂ) ^ (2 * c))
      (continuousAt_ofReal_cpow_const |x - y j| (2 * c) (Or.inl hc2)) hg

/-- An integrable majorant for `ibpD`, independent of `y`. -/
def ibpBound (n : ℕ) (α β c : ℂ) (x : ℝ) : ℝ :=
  ‖α‖ * x ^ (α.re - 1) + (if β = 0 then 0 else ‖β‖ * (1 - x) ^ (β.re - 1)) + n * (2 * ‖c‖)

/-- The majorant `ibpBound` is integrable on `[0,1]`. -/
theorem intervalIntegrable_ibpBound (n : ℕ) {α β c : ℂ} (hα : 0 < α.re)
    (hβ : 0 < β.re ∨ β = 0) : IntervalIntegrable (ibpBound n α β c) volume 0 1 := by
  refine ((IntervalIntegrable.const_mul ?_ _).add ?_).add intervalIntegrable_const
  · exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  · rcases hβ with hβ | rfl
    · have hb0 : β ≠ 0 := fun h => by simp [h] at hβ
      simp only [hb0, ite_false]
      refine IntervalIntegrable.const_mul ?_ _
      have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
        (r := β.re - 1) (by linarith)).comp_sub_left 1
      simpa using h.symm
    · simp

/-- For `Re c ≥ 1/2`, `‖ibpD‖` is bounded by `ibpBound` on `(0,1)`. -/
theorem norm_ibpD_le {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ cube n) {α β c : ℂ}
    (hα : 0 < α.re) (hβ : 0 < β.re ∨ β = 0) (hc : 1 / 2 ≤ c.re) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : ‖ibpD y α β c x‖ ≤ ibpBound n α β c x := by
  have hx0 : 0 < x := hx.1
  have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx0.le, hx.2.le⟩
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have hV := norm_vprod_le hy (by linarith : (0 : ℝ) ≤ c.re) hxI
  have hxa : ‖(x : ℂ) ^ α‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    exact Real.rpow_le_one hx0.le hx.2.le hα.le
  have hxb : ‖(1 - (x : ℂ)) ^ β‖ ≤ 1 := by
    rw [one_sub_ofReal, Complex.norm_cpow_eq_rpow_re_of_pos h1x]
    refine Real.rpow_le_one h1x.le (by linarith) ?_
    rcases hβ with hβ | rfl
    · exact hβ.le
    · simp
  have hT1 : ‖α * (x : ℂ) ^ (α - 1) * (1 - (x : ℂ)) ^ β * vprod y c x‖ ≤
      ‖α‖ * x ^ (α.re - 1) := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [Complex.sub_re, Complex.one_re]
    calc ‖α‖ * x ^ (α.re - 1) * ‖(1 - (x : ℂ)) ^ β‖ * ‖vprod y c x‖
        ≤ ‖α‖ * x ^ (α.re - 1) * 1 * 1 := by gcongr
      _ = _ := by ring
  have hT2 : ‖β * (x : ℂ) ^ α * (1 - (x : ℂ)) ^ (β - 1) * vprod y c x‖ ≤
      if β = 0 then 0 else ‖β‖ * (1 - x) ^ (β.re - 1) := by
    by_cases hb0 : β = 0
    · simp [hb0]
    simp only [hb0, ite_false]
    rw [norm_mul, norm_mul, norm_mul, one_sub_ofReal, Complex.norm_cpow_eq_rpow_re_of_pos h1x]
    simp only [Complex.sub_re, Complex.one_re]
    calc ‖β‖ * ‖(x : ℂ) ^ α‖ * (1 - x) ^ (β.re - 1) * ‖vprod y c x‖
        ≤ ‖β‖ * 1 * (1 - x) ^ (β.re - 1) * 1 := by gcongr
      _ = _ := by ring
  have hT3 : ‖(x : ℂ) ^ α * (1 - (x : ℂ)) ^ β *
      ((∑ j : Fin n, 2 * c / ((x : ℂ) - y j)) * vprod y c x)‖ ≤ n * (2 * ‖c‖) := by
    rw [norm_mul, norm_mul, Finset.sum_mul]
    have hs : ‖∑ j : Fin n, 2 * c / ((x : ℂ) - y j) * vprod y c x‖ ≤ n * (2 * ‖c‖) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j : Fin n, ‖2 * c / ((x : ℂ) - y j) * vprod y c x‖
          ≤ ∑ _j : Fin n, 2 * ‖c‖ :=
            Finset.sum_le_sum fun j _ => norm_div_mul_vprod_le hy hc hxI j
        _ = n * (2 * ‖c‖) := by simp
    calc ‖(x : ℂ) ^ α‖ * ‖(1 - (x : ℂ)) ^ β‖ *
          ‖∑ j : Fin n, 2 * c / ((x : ℂ) - y j) * vprod y c x‖
        ≤ 1 * 1 * (n * (2 * ‖c‖)) := by gcongr
      _ = _ := by ring
  unfold ibpD ibpBound
  rw [sub_mul]
  calc _ ≤ ‖α * (x : ℂ) ^ (α - 1) * (1 - (x : ℂ)) ^ β * vprod y c x‖ +
        ‖β * (x : ℂ) ^ α * (1 - (x : ℂ)) ^ (β - 1) * vprod y c x‖ +
        ‖(x : ℂ) ^ α * (1 - (x : ℂ)) ^ β *
          ((∑ j : Fin n, 2 * c / ((x : ℂ) - y j)) * vprod y c x)‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ _ := by linarith

/-- Almost every point of `(0,1]` lies in `(0,1)`. -/
theorem ae_mem_Ioo_of_mem_uIoc : ∀ᵐ x : ℝ, x ∈ Set.uIoc (0 : ℝ) 1 → x ∈ Ioo (0 : ℝ) 1 := by
  have hnull : ∀ᵐ x : ℝ, x ≠ 1 := (ae_iff).2 (by simp)
  filter_upwards [hnull] with x hx1 hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  exact ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩

/-- For `Re c ≥ 1/2`, `ibpD` is integrable on `[0,1]`. -/
theorem intervalIntegrable_ibpD {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ cube n) {α β c : ℂ}
    (hα : 0 < α.re) (hβ : 0 < β.re ∨ β = 0) (hc : 1 / 2 ≤ c.re) :
    IntervalIntegrable (ibpD y α β c) volume 0 1 := by
  refine (intervalIntegrable_ibpBound n (c := c) hα hβ).mono_fun'
    (measurable_ibpD y α β c).aestronglyMeasurable ?_
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [ae_mem_Ioo_of_mem_uIoc] with x hx hx'
  exact norm_ibpD_le hy hα hβ hc (hx hx')

/-- **One-variable integration by parts.** -/
theorem integral_ibpD {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ cube n) {α β c : ℂ}
    (hα : 0 < α.re) (hβ : 0 < β.re ∨ β = 0) (hc : 1 / 2 ≤ c.re) :
    ∫ x in (0 : ℝ)..1, ibpD y α β c x = if β = 0 then vprod y c 1 else 0 := by
  rw [integral_eq_of_hasDerivAt_off_countable_of_le (ibpF y α β c) (ibpD y α β c) zero_le_one
    (Set.countable_range y) (continuousOn_ibpF y hα hβ (by linarith))
    (fun x hx => hasDerivAt_ibpF y α β c hx.1 (fun j h => hx.2 ⟨j, h.symm⟩))
    (intervalIntegrable_ibpD hy hα hβ hc)]
  have hα0 : α ≠ 0 := fun h => by simp [h] at hα
  unfold ibpF
  rcases hβ with hβ | rfl
  · have hβ0 : β ≠ 0 := fun h => by simp [h] at hβ
    simp [Complex.zero_cpow hα0, Complex.zero_cpow hβ0, hβ0]
  · simp [Complex.zero_cpow hα0]

/-! ### Integration by parts in the zeroth coordinate of the cube -/

/-- Integrability on `[0,1]ⁿ⁺¹` from integrability of `(x, y) ↦ g(x, y)` on
`[0,1] × [0,1]ⁿ`. -/
theorem integrableOn_cube_succ {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℂ)
    (hg : IntegrableOn (fun p : ℝ × (Fin n → ℝ) => g (Fin.cons p.1 p.2))
      (Icc (0 : ℝ) 1 ×ˢ cube n) (volume.prod volume)) : IntegrableOn g (cube (n + 1)) := by
  have e := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have hpre : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm ⁻¹'
      (cube (n + 1)) = Icc (0 : ℝ) 1 ×ˢ cube n := by
    ext ⟨x, y⟩
    simp only [Set.mem_preimage, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.insertNth_zero', Set.mem_prod]
    exact cons_mem_cube
  have hsymm : ∀ p : ℝ × (Fin n → ℝ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p = Fin.cons p.1 p.2 := by
    intro p
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.insertNth_zero']
  rw [← Measure.volume_eq_prod, ← hpre] at hg
  refine (e.integrableOn_comp_preimage (MeasurableEquiv.measurableEmbedding _)).mp ?_
  simpa only [Function.comp_def, hsymm] using hg

/-- `(x, y) ↦ ibpD y α β c x` is jointly measurable. -/
theorem measurable_ibpD_uncurry {n : ℕ} (α β c : ℂ) :
    Measurable (fun p : ℝ × (Fin n → ℝ) => ibpD p.2 α β c p.1) := by
  unfold ibpD vprod
  fun_prop

/-- For the product of the restricted measures, almost every `(x, y)` has `x ∈ (0,1)`
and `y ∈ [0,1]ⁿ`. -/
theorem ae_prod_Ioo_cube {n : ℕ} :
    ∀ᵐ p ∂((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (cube n))),
      p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2 ∈ cube n := by
  have h1 : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ Ioo (0 : ℝ) 1 := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have h0 : ∀ᵐ x : ℝ, x ≠ 0 := (ae_iff).2 (by simp)
    have h1 : ∀ᵐ x : ℝ, x ≠ 1 := (ae_iff).2 (by simp)
    filter_upwards [h0, h1] with x hx0 hx1 hx
    exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
  have h2 : ∀ᵐ y ∂(volume.restrict (cube n)), y ∈ cube n :=
    ae_restrict_mem (measurableSet_cube n)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1,
    Measure.quasiMeasurePreserving_snd.ae h2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

/-- Integrability on `[0,1]ⁿ⁺¹` of `K(tail t) · ibpD (tail t) α β c (t₀)` for integrable `K`. -/
theorem integrableOn_ibp {n : ℕ} {α β c : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re ∨ β = 0)
    (hc : 1 / 2 ≤ c.re) {K : (Fin n → ℝ) → ℂ} (hK : IntegrableOn K (cube n)) :
    IntegrableOn (fun t : Fin (n + 1) → ℝ => K (Fin.tail t) * ibpD (Fin.tail t) α β c (t 0))
      (cube (n + 1)) := by
  refine integrableOn_cube_succ _ ?_
  simp only [Fin.tail_cons, Fin.cons_zero]
  rw [IntegrableOn, ← Measure.prod_restrict]
  have hB : Integrable (fun p : ℝ × (Fin n → ℝ) => ibpBound n α β c p.1 * ‖K p.2‖)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (cube n))) := by
    refine Integrable.mul_prod ?_ hK.norm
    have := (intervalIntegrable_ibpBound n (c := c) hα hβ)
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one] at this
    exact this
  refine hB.mono' ((hK.aestronglyMeasurable.comp_snd (μ := volume.restrict (Icc (0 : ℝ) 1))).mul
    (measurable_ibpD_uncurry α β c).aestronglyMeasurable) ?_
  filter_upwards [ae_prod_Ioo_cube] with p hp
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_ibpD_le hp.2 hα hβ hc hp.1) (norm_nonneg _)

/-- **Integration by parts in the zeroth coordinate.** -/
theorem integral_cube_ibp {n : ℕ} {α β c : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re ∨ β = 0)
    (hc : 1 / 2 ≤ c.re) {K : (Fin n → ℝ) → ℂ} (hK : IntegrableOn K (cube n)) :
    ∫ t in cube (n + 1), K (Fin.tail t) * ibpD (Fin.tail t) α β c (t 0) =
      if β = 0 then ∫ y in cube n, K y * vprod y c 1 else 0 := by
  rw [integral_cube_succ _ (integrableOn_ibp hα hβ hc hK)]
  simp only [Fin.tail_cons, Fin.cons_zero]
  have hin : ∀ y ∈ cube n, ∫ x in Icc (0 : ℝ) 1, K y * ibpD y α β c x =
      K y * (if β = 0 then vprod y c 1 else 0) := by
    intro y hy
    rw [integral_const_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
      zero_le_one, integral_ibpD hy hα hβ hc]
  rw [setIntegral_congr_fun (measurableSet_cube n) hin]
  split_ifs <;> simp

/-! ### Integrability on the cube -/

/-- For `Re a, Re b > 0`, the weight `x^{a-1}(1-x)^{b-1}` is integrable on `[0,1]`. -/
theorem integrableOn_weight {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (weight a b) (Icc (0 : ℝ) 1) := by
  have h := Complex.betaIntegral_convergent ha hb
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one] at h
  exact h

/-- A product `∏ᵢ f(tᵢ)` of integrable functions is integrable on `[0,1]ⁿ`. -/
theorem integrableOn_prod_cube {n : ℕ} {f : ℝ → ℂ} (hf : IntegrableOn f (Icc (0 : ℝ) 1)) :
    IntegrableOn (fun t : Fin n → ℝ => ∏ i, f (t i)) (cube n) := by
  rw [IntegrableOn, volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod (fun _ => hf)

/-- The Selberg integrand is measurable. -/
theorem measurable_selbergIntegrand (n : ℕ) (a b c : ℂ) :
    Measurable (selbergIntegrand n a b c) := by
  unfold selbergIntegrand
  fun_prop

/-- The weight `x^{a-1}(1-x)^{b-1}` is measurable. -/
theorem measurable_weight (a b : ℂ) : Measurable (weight a b) := by
  unfold weight
  fun_prop

/-- On the cube and for `Re c ≥ 0`, the Vandermonde factor has norm at most `1`. -/
theorem norm_vdm_le_one {n : ℕ} {c : ℂ} (hc : 0 ≤ c.re) {t : Fin n → ℝ} (ht : t ∈ cube n) :
    ‖vdm n c t‖ ≤ 1 := by
  unfold vdm
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
  split_ifs
  · have := norm_vprod_le (y := fun _ : Fin 1 => t j) (fun _ _ => ht j (Set.mem_univ _))
      (c := c) hc (ht i (Set.mem_univ _))
    simpa [vprod] using this
  · simp

/-- On the cube and for `Re c ≥ 0`, the Selberg integrand is dominated by the
product of the weights. -/
theorem norm_selbergIntegrand_le {n : ℕ} {a b c : ℂ} (hc : 0 ≤ c.re) {t : Fin n → ℝ}
    (ht : t ∈ cube n) : ‖selbergIntegrand n a b c t‖ ≤ ‖∏ i, weight a b (t i)‖ := by
  rw [selbergIntegrand_eq, norm_mul]
  calc ‖∏ i, weight a b (t i)‖ * ‖vdm n c t‖ ≤ ‖∏ i, weight a b (t i)‖ * 1 := by
        gcongr; exact norm_vdm_le_one hc ht
    _ = _ := mul_one _

/-- A bounded measurable function times the Selberg integrand is integrable (`Re c ≥ 0`). -/
theorem integrableOn_mul_selbergIntegrand {n : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 ≤ c.re) {h : (Fin n → ℝ) → ℂ} (hh : Measurable h) {M : ℝ}
    (hM : ∀ t ∈ cube n, ‖h t‖ ≤ M) :
    IntegrableOn (fun t => h t * selbergIntegrand n a b c t) (cube n) := by
  have hW := (integrableOn_prod_cube (n := n) (integrableOn_weight ha hb)).norm.const_mul M
  refine hW.mono' (hh.mul (measurable_selbergIntegrand n a b c)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_cube n)] with t ht
  rw [norm_mul]
  exact mul_le_mul (hM t ht) (norm_selbergIntegrand_le hc ht) (norm_nonneg _)
    ((norm_nonneg _).trans (hM t ht))

/-- Splitting the Selberg integrand at the coordinate `t₀`. -/
theorem selbergIntegrand_eq_cons_tail {n : ℕ} (a b c : ℂ) (t : Fin (n + 1) → ℝ) :
    selbergIntegrand (n + 1) a b c t =
      weight a b (t 0) * vprod (Fin.tail t) c (t 0) * selbergIntegrand n a b c (Fin.tail t) := by
  conv_lhs => rw [← Fin.cons_self_tail t]
  rw [selbergIntegrand_cons]
  rfl

/-- The tail of a point of `[0,1]ⁿ⁺¹` lies in `[0,1]ⁿ`. -/
theorem tail_mem_cube {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : t ∈ cube (n + 1)) :
    Fin.tail t ∈ cube n := by
  rw [← Fin.cons_self_tail t, cons_mem_cube] at ht
  exact ht.2

/-- The first coordinate of a point of `[0,1]ⁿ⁺¹` lies in `[0,1]`. -/
theorem zero_mem_Icc_of_mem_cube {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : t ∈ cube (n + 1)) :
    t 0 ∈ Icc (0 : ℝ) 1 := ht 0 (Set.mem_univ _)

/-- The singular factor `2c/(t₀ - t_{j+1})` is absorbed by `|t₀ - t_{j+1}|^{2c}` when
`Re c ≥ 1/2`. -/
theorem norm_div_mul_selbergIntegrand_le {n : ℕ} {a b c : ℂ} (hc : 1 / 2 ≤ c.re)
    {t : Fin (n + 1) → ℝ} (ht : t ∈ cube (n + 1)) (j : Fin n) :
    ‖2 * c / ((t 0 : ℂ) - t j.succ) * selbergIntegrand (n + 1) a b c t‖ ≤
      2 * ‖c‖ * ‖∏ i, weight a b (t i)‖ := by
  have hy := tail_mem_cube ht
  rw [selbergIntegrand_eq_cons_tail]
  have h1 := norm_div_mul_vprod_le hy hc (zero_mem_Icc_of_mem_cube ht) j
  have h2 := norm_selbergIntegrand_le (a := a) (b := b) (by linarith : (0 : ℝ) ≤ c.re) hy
  have hsucc : t j.succ = Fin.tail t j := rfl
  rw [hsucc, Fin.prod_univ_succ]
  calc ‖2 * c / ((t 0 : ℂ) - Fin.tail t j) *
        (weight a b (t 0) * vprod (Fin.tail t) c (t 0) * selbergIntegrand n a b c (Fin.tail t))‖
      = ‖weight a b (t 0)‖ * ‖2 * c / ((t 0 : ℂ) - Fin.tail t j) * vprod (Fin.tail t) c (t 0)‖ *
          ‖selbergIntegrand n a b c (Fin.tail t)‖ := by
        simp only [norm_mul]; ring
    _ ≤ ‖weight a b (t 0)‖ * (2 * ‖c‖) * ‖∏ i, weight a b (Fin.tail t i)‖ := by gcongr
    _ = _ := by rw [norm_mul]; simp only [Fin.tail]; ring

/-- For `Re c ≥ 1/2` and bounded measurable `h`, the cross term
`h(t) · 2c/(t₀ - tⱼ₊₁) · Φ(t)` is integrable on the cube. -/
theorem integrableOn_mul_div_selbergIntegrand {n : ℕ} {a b c : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) (hc : 1 / 2 ≤ c.re) (j : Fin n) {h : (Fin (n + 1) → ℝ) → ℂ}
    (hh : Measurable h) {M : ℝ} (hM : ∀ t ∈ cube (n + 1), ‖h t‖ ≤ M) :
    IntegrableOn (fun t => h t * (2 * c / ((t 0 : ℂ) - t j.succ) *
      selbergIntegrand (n + 1) a b c t)) (cube (n + 1)) := by
  have hW := ((integrableOn_prod_cube (n := n + 1) (integrableOn_weight ha hb)).norm.const_mul
    (2 * ‖c‖)).const_mul M
  have hmeas : Measurable fun t : Fin (n + 1) → ℝ =>
      h t * (2 * c / ((t 0 : ℂ) - t j.succ) * selbergIntegrand (n + 1) a b c t) := by
    have := measurable_selbergIntegrand (n + 1) a b c
    fun_prop
  refine hW.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_cube (n + 1))] with t ht
  rw [norm_mul]
  exact mul_le_mul (hM t ht) (norm_div_mul_selbergIntegrand_le hc ht j) (norm_nonneg _)
    ((norm_nonneg _).trans (hM t ht))

/-! ### Aomoto's recurrence -/

/-- For `z ≠ 0`, `z^w = z · z^{w-1}`. -/
theorem cpow_eq_mul_cpow_sub_one {z : ℂ} (hz : z ≠ 0) (w : ℂ) : z ^ w = z * z ^ (w - 1) := by
  conv_lhs => rw [show w = 1 + (w - 1) by ring]
  rw [Complex.cpow_add _ _ hz, Complex.cpow_one]

/-- `ibpD` in terms of the weight. -/
theorem ibpD_eq {n : ℕ} (y : Fin n → ℝ) (α β c : ℂ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ibpD y α β c x = weight α β x * vprod y c x *
      (α * (1 - x) - β * x + x * (1 - x) * ∑ j : Fin n, 2 * c / ((x : ℂ) - y j)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
  have hx1 : (1 - (x : ℂ)) ≠ 0 := by
    rw [one_sub_ofReal]; exact_mod_cast (show (1 - x) ≠ 0 by linarith [hx.2])
  unfold ibpD weight
  rw [cpow_eq_mul_cpow_sub_one hx0 α, cpow_eq_mul_cpow_sub_one hx1 β]
  ring

/-- The integration-by-parts derivative for `β = 0`. -/
theorem ibpD_zero_eq {n : ℕ} (y : Fin n → ℝ) (α c : ℂ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ibpD y α 0 c x = weight α 1 x * vprod y c x *
      (α + x * ∑ j : Fin n, 2 * c / ((x : ℂ) - y j)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
  unfold ibpD weight
  rw [cpow_eq_mul_cpow_sub_one hx0 α]
  simp only [sub_self, Complex.cpow_zero, zero_mul, sub_zero, mul_one]
  ring

/-- The diagonal `tᵢ = tⱼ` is a null set. -/
theorem ae_ne_coord {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    ∀ᵐ t : Fin N → ℝ, t i ≠ t j := by
  classical
  set L : (Fin N → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i : (Fin N → ℝ) →ₗ[ℝ] ℝ) - (LinearMap.proj j : (Fin N → ℝ) →ₗ[ℝ] ℝ)
  have hker : (LinearMap.ker L : Set (Fin N → ℝ)) = {t | t i = t j} := by
    ext t; simp [L, sub_eq_zero]
  have hne : LinearMap.ker L ≠ ⊤ := by
    intro h
    have : (Pi.single i (1 : ℝ) : Fin N → ℝ) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    simp [L, hij.symm] at this
  have h0 := Measure.addHaar_submodule volume (LinearMap.ker L) hne
  rw [hker] at h0
  exact (ae_iff).2 (by simpa using h0)

/-- `∏ᵢ∈S tᵢ`. -/
def mono {N : ℕ} (S : Finset (Fin N)) (t : Fin N → ℝ) : ℂ := ∏ i ∈ S, (t i : ℂ)

/-- Aomoto's integrals `∫ ∏ᵢ∈S tᵢ · Φ(t) dt`. -/
def aomotoInt (N : ℕ) (a b c : ℂ) (S : Finset (Fin N)) : ℂ :=
  ∫ t in cube N, mono S t * selbergIntegrand N a b c t

/-- The monomial `∏ᵢ∈S tᵢ` is measurable. -/
theorem measurable_mono {N : ℕ} (S : Finset (Fin N)) : Measurable (mono S) := by
  unfold mono; fun_prop

/-- On the cube, the monomial `∏ᵢ∈S tᵢ` has norm at most `1`. -/
theorem norm_mono_le {N : ℕ} (S : Finset (Fin N)) {t : Fin N → ℝ} (ht : t ∈ cube N) :
    ‖mono S t‖ ≤ 1 := by
  unfold mono
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
  have := ht i (Set.mem_univ _)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [this.1, this.2]

/-- Permuting the variables of a monomial permutes its index set. -/
theorem mono_comp_perm {N : ℕ} (S : Finset (Fin N)) (σ : Equiv.Perm (Fin N))
    (t : Fin N → ℝ) : mono S (t ∘ σ) = mono (S.map σ.toEmbedding) t := by
  unfold mono
  simp [Finset.prod_map]

/-- Aomoto's integral is invariant under permutations of the index set `S`. -/
theorem aomotoInt_map_perm {N : ℕ} (a b c : ℂ) (S : Finset (Fin N)) (σ : Equiv.Perm (Fin N)) :
    aomotoInt N a b c (S.map σ.toEmbedding) = aomotoInt N a b c S := by
  unfold aomotoInt
  rw [← integral_cube_comp_perm σ (fun t => mono S t * selbergIntegrand N a b c t)]
  simp only [mono_comp_perm, selbergIntegrand_comp_perm]

/-- The preimage of `S` under `Fin.succ`. -/
def succPre {n : ℕ} (S : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun j => j.succ ∈ S

/-- If `0 ∉ S`, the monomial `∏ᵢ∈S tᵢ` depends only on `tail t`. -/
theorem mono_eq_tail {n : ℕ} {S : Finset (Fin (n + 1))} (hS : (0 : Fin (n + 1)) ∉ S)
    (t : Fin (n + 1) → ℝ) : mono S t = mono (succPre S) (Fin.tail t) := by
  classical
  unfold mono succPre
  have h1 : ∏ i ∈ S, (t i : ℂ) = ∏ i : Fin (n + 1), if i ∈ S then (t i : ℂ) else 1 := by
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [h1, Fin.prod_univ_succ]
  simp only [hS, ↓reduceIte, one_mul]
  rw [Finset.prod_filter]
  rfl

/-- Almost every point of `ℝᴺ` has `i`-th coordinate different from `x`. -/
theorem ae_coord_ne {N : ℕ} (i : Fin N) (x : ℝ) : ∀ᵐ t : Fin N → ℝ, t i ≠ x := by
  rw [volume_pi]
  exact Measure.ae_eval_ne (μ := fun _ : Fin N => (volume : Measure ℝ)) i x

/-- Almost every point of `[0,1]ⁿ⁺¹` has first coordinate in `(0,1)`. -/
theorem ae_coord_mem_Ioo {n : ℕ} :
    ∀ᵐ t : Fin (n + 1) → ℝ, t ∈ cube (n + 1) → t 0 ∈ Ioo (0 : ℝ) 1 := by
  filter_upwards [ae_coord_ne 0 0, ae_coord_ne 0 1] with t h0 h1 ht
  have := zero_mem_Icc_of_mem_cube ht
  exact ⟨lt_of_le_of_ne this.1 (Ne.symm h0), lt_of_le_of_ne this.2 h1⟩

/-- The integration-by-parts identity behind Aomoto's recurrence. -/
theorem aomoto_ibp {n : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 1 / 2 ≤ c.re)
    {S : Finset (Fin (n + 1))} (hS : (0 : Fin (n + 1)) ∉ S) :
    ∫ t in cube (n + 1), mono S t * selbergIntegrand (n + 1) a b c t *
      (a * (1 - t 0) - b * t 0 + t 0 * (1 - t 0) *
        ∑ j : Fin n, 2 * c / ((t 0 : ℂ) - t j.succ)) = 0 := by
  have hK : IntegrableOn (fun y => mono (succPre S) y * selbergIntegrand n a b c y) (cube n) :=
    integrableOn_mul_selbergIntegrand ha hb (by linarith) (measurable_mono _)
      (fun y hy => norm_mono_le _ hy)
  have h := integral_cube_ibp ha (Or.inl hb) hc hK
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  simp only [hb0, ↓reduceIte] at h
  rw [← h]
  refine setIntegral_congr_ae (measurableSet_cube _) ?_
  filter_upwards [ae_coord_mem_Ioo] with t ht0 ht
  rw [ibpD_eq _ _ _ _ (ht0 ht), selbergIntegrand_eq_cons_tail, mono_eq_tail hS]
  simp only [Fin.tail]
  ring

/-- Expansion of the Aomoto identity. -/
theorem aomoto_expand {n : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 1 / 2 ≤ c.re)
    {S : Finset (Fin (n + 1))} (hS : (0 : Fin (n + 1)) ∉ S) :
    a * aomotoInt (n + 1) a b c S - (a + b) * aomotoInt (n + 1) a b c (insert 0 S) +
      ∑ j : Fin n, ∫ t in cube (n + 1), mono S t * ((t 0 : ℂ) * (1 - t 0)) *
        (2 * c / ((t 0 : ℂ) - t j.succ) * selbergIntegrand (n + 1) a b c t) = 0 := by
  have hc0 : (0 : ℝ) ≤ c.re := by linarith
  have hI1 : IntegrableOn (fun t => mono S t * selbergIntegrand (n + 1) a b c t)
      (cube (n + 1)) :=
    integrableOn_mul_selbergIntegrand ha hb hc0 (measurable_mono _) (fun t ht => norm_mono_le _ ht)
  have hI2 : IntegrableOn (fun t => mono (insert 0 S) t * selbergIntegrand (n + 1) a b c t)
      (cube (n + 1)) :=
    integrableOn_mul_selbergIntegrand ha hb hc0 (measurable_mono _) (fun t ht => norm_mono_le _ ht)
  have hI3 : ∀ j : Fin n, IntegrableOn (fun t => mono S t * ((t 0 : ℂ) * (1 - t 0)) *
      (2 * c / ((t 0 : ℂ) - t j.succ) * selbergIntegrand (n + 1) a b c t)) (cube (n + 1)) := by
    intro j
    refine integrableOn_mul_div_selbergIntegrand ha hb hc j (M := 1) ?_ ?_
    · have := measurable_mono S; fun_prop
    · intro t ht
      have h0 := zero_mem_Icc_of_mem_cube ht
      rw [norm_mul]
      have h1 : ‖(t 0 : ℂ) * (1 - t 0)‖ ≤ 1 := by
        rw [one_sub_ofReal, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_le]
        constructor <;> nlinarith [h0.1, h0.2]
      calc ‖mono S t‖ * ‖(t 0 : ℂ) * (1 - t 0)‖ ≤ 1 * 1 :=
            mul_le_mul (norm_mono_le S ht) h1 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  have hmono : ∀ t : Fin (n + 1) → ℝ, mono (insert 0 S) t = (t 0 : ℂ) * mono S t := by
    intro t; unfold mono; rw [Finset.prod_insert hS]
  have hpt : ∀ t : Fin (n + 1) → ℝ, mono S t * selbergIntegrand (n + 1) a b c t *
      (a * (1 - t 0) - b * t 0 + t 0 * (1 - t 0) *
        ∑ j : Fin n, 2 * c / ((t 0 : ℂ) - t j.succ)) =
      a * (mono S t * selbergIntegrand (n + 1) a b c t) -
        (a + b) * (mono (insert 0 S) t * selbergIntegrand (n + 1) a b c t) +
        ∑ j : Fin n, mono S t * ((t 0 : ℂ) * (1 - t 0)) *
          (2 * c / ((t 0 : ℂ) - t j.succ) * selbergIntegrand (n + 1) a b c t) := by
    intro t
    rw [hmono, mul_add, Finset.mul_sum, Finset.mul_sum]
    have : ∀ j : Fin n, mono S t * selbergIntegrand (n + 1) a b c t *
        ((t 0 : ℂ) * (1 - t 0) * (2 * c / ((t 0 : ℂ) - t j.succ))) =
        mono S t * ((t 0 : ℂ) * (1 - t 0)) *
          (2 * c / ((t 0 : ℂ) - t j.succ) * selbergIntegrand (n + 1) a b c t) := fun j => by ring
    simp_rw [this]
    ring
  have h := aomoto_ibp ha hb hc hS
  simp_rw [hpt] at h
  have hA : IntegrableOn (fun t => a * (mono S t * selbergIntegrand (n + 1) a b c t) -
      (a + b) * (mono (insert 0 S) t * selbergIntegrand (n + 1) a b c t)) (cube (n + 1)) :=
    (hI1.const_mul a).sub (hI2.const_mul (a + b))
  have hB : IntegrableOn (fun t => ∑ j : Fin n, mono S t * ((t 0 : ℂ) * (1 - t 0)) *
      (2 * c / ((t 0 : ℂ) - t j.succ) * selbergIntegrand (n + 1) a b c t)) (cube (n + 1)) :=
    integrable_finsetSum _ fun j _ => hI3 j
  rw [integral_add hA hB, integral_sub (hI1.const_mul a) (hI2.const_mul (a + b)),
    integral_const_mul, integral_const_mul, integral_finsetSum _ fun j _ => hI3 j] at h
  exact h

/-- Symmetrization: if `f(t) + f(t ∘ σ) = g(t)` a.e. on the cube, then
`2 ∫ f = ∫ g`. -/
theorem two_mul_integral_eq_of_swap {N : ℕ} (σ : Equiv.Perm (Fin N)) {f g : (Fin N → ℝ) → ℂ}
    (hf : IntegrableOn f (cube N)) (hg : ∀ᵐ t, t ∈ cube N → f t + f (t ∘ σ) = g t) :
    2 * ∫ t in cube N, f t = ∫ t in cube N, g t := by
  have h1 := integral_cube_comp_perm σ f
  rw [← setIntegral_congr_ae (measurableSet_cube N) hg,
    integral_add hf (integrableOn_cube_comp_perm σ hf), h1]
  ring

/-- A permutation fixing `S` pointwise leaves `∏ᵢ∈S tᵢ` unchanged. -/
theorem mono_comp_of_fix {N : ℕ} {S : Finset (Fin N)} {σ : Equiv.Perm (Fin N)}
    (hσ : ∀ i ∈ S, σ i = i) (t : Fin N → ℝ) : mono S (t ∘ σ) = mono S t := by
  unfold mono
  exact Finset.prod_congr rfl fun i hi => by simp [hσ i hi]

/-- If `0, k ∉ S`, the transposition `(0 k)` fixes `S` pointwise. -/
theorem swap_fix_of_not_mem {n : ℕ} {S : Finset (Fin (n + 1))} (hS : (0 : Fin (n + 1)) ∉ S)
    {k : Fin (n + 1)} (hk : k ∉ S) : ∀ i ∈ S, Equiv.swap (0 : Fin (n + 1)) k i = i := by
  intro i hi
  refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
  · rintro rfl; exact hS hi
  · rintro rfl; exact hk hi

/-- For `Re a, Re b > 0` and `Re c ≥ 0`, `∏ᵢ∈S tᵢ · Φ(t)` is integrable on the cube. -/
theorem integrableOn_mono_selberg {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 ≤ c.re) (S : Finset (Fin N)) :
    IntegrableOn (fun t => mono S t * selbergIntegrand N a b c t) (cube N) :=
  integrableOn_mul_selbergIntegrand ha hb hc (measurable_mono _) (fun _ ht => norm_mono_le _ ht)

/-- The cross term when `j+1 ∉ S`. -/
theorem aomoto_cross_not_mem {n : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 1 / 2 ≤ c.re) {S : Finset (Fin (n + 1))} (hS : (0 : Fin (n + 1)) ∉ S) (j : Fin n)
    (hj : j.succ ∉ S) :
    ∫ t in cube (n + 1), mono S t * ((t 0 : ℂ) * (1 - t 0)) *
        (2 * c / ((t 0 : ℂ) - t j.succ) * selbergIntegrand (n + 1) a b c t) =
      c * (aomotoInt (n + 1) a b c S - 2 * aomotoInt (n + 1) a b c (insert 0 S)) := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin (n + 1)), σ = Equiv.swap 0 j.succ := ⟨_, rfl⟩
  have hfix : ∀ i ∈ S, σ i = i := hσ ▸ swap_fix_of_not_mem hS hj
  have hsw0 : ∀ t : Fin (n + 1) → ℝ, (t ∘ σ) 0 = t j.succ := fun t => by simp [hσ]
  have hsw1 : ∀ t : Fin (n + 1) → ℝ, (t ∘ σ) j.succ = t 0 := fun t => by simp [hσ]
  have hc0 : (0 : ℝ) ≤ c.re := by linarith
  have hI : IntegrableOn (fun t => mono S t * ((t 0 : ℂ) * (1 - t 0)) *
      (2 * c / ((t 0 : ℂ) - t j.succ) * selbergIntegrand (n + 1) a b c t)) (cube (n + 1)) := by
    refine integrableOn_mul_div_selbergIntegrand ha hb hc j (M := 1) ?_ ?_
    · have := measurable_mono S; fun_prop
    · intro t ht
      have h0 := zero_mem_Icc_of_mem_cube ht
      rw [norm_mul]
      have h1 : ‖(t 0 : ℂ) * (1 - t 0)‖ ≤ 1 := by
        rw [one_sub_ofReal, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith [h0.1, h0.2]
      calc ‖mono S t‖ * ‖(t 0 : ℂ) * (1 - t 0)‖ ≤ 1 * 1 :=
            mul_le_mul (norm_mono_le S ht) h1 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  have h2 := two_mul_integral_eq_of_swap σ hI (g := fun t => 2 * c *
      (mono S t * selbergIntegrand (n + 1) a b c t -
        (t 0 : ℂ) * (mono S t * selbergIntegrand (n + 1) a b c t) -
        (t j.succ : ℂ) * (mono S t * selbergIntegrand (n + 1) a b c t))) (by
    filter_upwards [ae_ne_coord (Fin.succ_ne_zero j).symm] with t hne _
    simp only [hsw0, hsw1, mono_comp_of_fix hfix, selbergIntegrand_comp_perm]
    have hd : (t 0 : ℂ) - t j.succ ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
    have hd' : (t j.succ : ℂ) - t 0 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne.symm)
    field_simp
    ring)
  have hswap : ∫ t in cube (n + 1), (t j.succ : ℂ) * (mono S t * selbergIntegrand (n + 1) a b c t) =
      aomotoInt (n + 1) a b c (insert 0 S) := by
    unfold aomotoInt
    rw [← integral_cube_comp_perm σ]
    refine setIntegral_congr_fun (measurableSet_cube _) fun t _ => ?_
    rw [hsw1, mono_comp_of_fix hfix, selbergIntegrand_comp_perm]
    simp only [mono, Finset.prod_insert hS]
    ring
  have hI1 := integrableOn_mono_selberg ha hb hc0 (N := n + 1) S
  have hI0 : IntegrableOn (fun t => (t 0 : ℂ) * (mono S t * selbergIntegrand (n + 1) a b c t))
      (cube (n + 1)) := by
    refine integrableOn_mul_selbergIntegrand ha hb hc0 (h := fun t => (t 0 : ℂ) * mono S t)
      (M := 1) (by have := measurable_mono S; fun_prop) (fun t ht => ?_) |>.congr_fun
      (fun t _ => by ring) (measurableSet_cube _)
    rw [norm_mul]
    have h0 := zero_mem_Icc_of_mem_cube ht
    have : ‖(t 0 : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith [h0.1, h0.2]
    calc ‖(t 0 : ℂ)‖ * ‖mono S t‖ ≤ 1 * 1 :=
          mul_le_mul this (norm_mono_le S ht) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hIs : IntegrableOn (fun t => (t j.succ : ℂ) *
      (mono S t * selbergIntegrand (n + 1) a b c t)) (cube (n + 1)) := by
    have := integrableOn_cube_comp_perm σ hI0
    refine this.congr_fun (fun t _ => ?_) (measurableSet_cube _)
    simp only [selbergIntegrand_comp_perm, mono_comp_of_fix hfix]
    rw [hsw0 t]
  have hins : aomotoInt (n + 1) a b c (insert 0 S) =
      ∫ t in cube (n + 1), (t 0 : ℂ) * (mono S t * selbergIntegrand (n + 1) a b c t) := by
    unfold aomotoInt
    refine setIntegral_congr_fun (measurableSet_cube _) fun t _ => ?_
    simp only [mono, Finset.prod_insert hS]
    ring
  have hA : IntegrableOn (fun t => mono S t * selbergIntegrand (n + 1) a b c t -
      (t 0 : ℂ) * (mono S t * selbergIntegrand (n + 1) a b c t)) (cube (n + 1)) := hI1.sub hI0
  rw [integral_const_mul, integral_sub hA hIs, integral_sub hI1 hI0, hswap, ← hins] at h2
  unfold aomotoInt at h2 ⊢
  linear_combination h2 / 2

/-- The cross term when `j+1 ∈ S`. -/
theorem aomoto_cross_mem {n : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 1 / 2 ≤ c.re) {S : Finset (Fin (n + 1))} (hS : (0 : Fin (n + 1)) ∉ S) (j : Fin n)
    (hj : j.succ ∈ S) :
    ∫ t in cube (n + 1), mono S t * ((t 0 : ℂ) * (1 - t 0)) *
        (2 * c / ((t 0 : ℂ) - t j.succ) * selbergIntegrand (n + 1) a b c t) =
      -c * aomotoInt (n + 1) a b c (insert 0 S) := by
  classical
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin (n + 1)), σ = Equiv.swap 0 j.succ := ⟨_, rfl⟩
  set S' := S.erase j.succ with hS'
  have hS'0 : (0 : Fin (n + 1)) ∉ S' := fun h => hS (Finset.mem_of_mem_erase h)
  have hfix : ∀ i ∈ S', σ i = i := hσ ▸ swap_fix_of_not_mem hS'0 (Finset.notMem_erase j.succ S)
  have hsw0 : ∀ t : Fin (n + 1) → ℝ, (t ∘ σ) 0 = t j.succ := fun t => by simp [hσ]
  have hsw1 : ∀ t : Fin (n + 1) → ℝ, (t ∘ σ) j.succ = t 0 := fun t => by simp [hσ]
  have hmS : ∀ t : Fin (n + 1) → ℝ, mono S t = (t j.succ : ℂ) * mono S' t := by
    intro t; unfold mono; rw [hS', Finset.mul_prod_erase S (fun i => (t i : ℂ)) hj]
  have hc0 : (0 : ℝ) ≤ c.re := by linarith
  have hI : IntegrableOn (fun t => mono S t * ((t 0 : ℂ) * (1 - t 0)) *
      (2 * c / ((t 0 : ℂ) - t j.succ) * selbergIntegrand (n + 1) a b c t)) (cube (n + 1)) := by
    refine integrableOn_mul_div_selbergIntegrand ha hb hc j (M := 1) ?_ ?_
    · have := measurable_mono S; fun_prop
    · intro t ht
      have h0 := zero_mem_Icc_of_mem_cube ht
      rw [norm_mul]
      have h1 : ‖(t 0 : ℂ) * (1 - t 0)‖ ≤ 1 := by
        rw [one_sub_ofReal, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith [h0.1, h0.2]
      calc ‖mono S t‖ * ‖(t 0 : ℂ) * (1 - t 0)‖ ≤ 1 * 1 :=
            mul_le_mul (norm_mono_le S ht) h1 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  have h2 := two_mul_integral_eq_of_swap σ hI (g := fun t => -(2 * c) *
      ((t 0 : ℂ) * (mono S t * selbergIntegrand (n + 1) a b c t))) (by
    filter_upwards [ae_ne_coord (Fin.succ_ne_zero j).symm] with t hne _
    rw [hmS, hmS (t ∘ σ)]
    simp only [hsw0, hsw1, mono_comp_of_fix hfix, selbergIntegrand_comp_perm]
    have hd : (t 0 : ℂ) - t j.succ ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
    have hd' : (t j.succ : ℂ) - t 0 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne.symm)
    field_simp
    ring)
  have hins : aomotoInt (n + 1) a b c (insert 0 S) =
      ∫ t in cube (n + 1), (t 0 : ℂ) * (mono S t * selbergIntegrand (n + 1) a b c t) := by
    unfold aomotoInt
    refine setIntegral_congr_fun (measurableSet_cube _) fun t _ => ?_
    simp only [mono, Finset.prod_insert hS]
    ring
  rw [integral_const_mul, ← hins] at h2
  linear_combination h2 / 2

/-- If `0 ∉ S`, the preimage of `S` under `Fin.succ` has the same cardinality. -/
theorem card_succPre {n : ℕ} {S : Finset (Fin (n + 1))} (hS : (0 : Fin (n + 1)) ∉ S) :
    (succPre S).card = S.card := by
  have : S = (succPre S).map (Fin.succEmb n) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [hS, false_iff, Finset.mem_map, Fin.coe_succEmb, not_exists, not_and]
      exact fun j _ h => Fin.succ_ne_zero j h
    · simp [succPre]
  conv_rhs => rw [this]
  rw [Finset.card_map]

/-- **Aomoto's recurrence** (AAR (8.1.5)): for `0 ∉ S`, with `k = |S|`,
`(a + (n-k)c) A(S) = (a + b + (2n-k)c) A(S ∪ {0})`. -/
theorem aomoto_step {n : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 1 / 2 ≤ c.re)
    {S : Finset (Fin (n + 1))} (hS : (0 : Fin (n + 1)) ∉ S) :
    (a + ((n : ℂ) - S.card) * c) * aomotoInt (n + 1) a b c S =
      (a + b + (2 * (n : ℂ) - S.card) * c) * aomotoInt (n + 1) a b c (insert 0 S) := by
  classical
  have h := aomoto_expand ha hb hc hS
  set A := aomotoInt (n + 1) a b c S
  set A' := aomotoInt (n + 1) a b c (insert 0 S)
  have hsum : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      ∫ t in cube (n + 1), mono S t * ((t 0 : ℂ) * (1 - t 0)) *
        (2 * c / ((t 0 : ℂ) - t j.succ) * selbergIntegrand (n + 1) a b c t) =
      if j.succ ∈ S then -c * A' else c * (A - 2 * A') := by
    intro j _
    split_ifs with hj
    · exact aomoto_cross_mem ha hb hc hS j hj
    · exact aomoto_cross_not_mem ha hb hc hS j hj
  rw [Finset.sum_congr rfl hsum, Finset.sum_ite, Finset.sum_const, Finset.sum_const] at h
  have hc1 : (Finset.univ.filter fun j : Fin n => j.succ ∈ S).card = S.card :=
    card_succPre hS
  have hc2 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun j : Fin n => j.succ ∈ S)
  rw [hc1, Finset.card_univ, Fintype.card_fin] at hc2
  rw [hc1, nsmul_eq_mul, nsmul_eq_mul] at h
  have hc2' : ((Finset.univ.filter fun j : Fin n => j.succ ∉ S).card : ℂ) = n - S.card := by
    have : (((Finset.univ.filter fun j : Fin n => j.succ ∉ S).card : ℕ) : ℂ) + S.card = n := by
      exact_mod_cast (by omega : (Finset.univ.filter fun j : Fin n => j.succ ∉ S).card +
        S.card = n)
    linear_combination this
  rw [hc2'] at h
  linear_combination h

/-- The initial segment `{i | i < m}`. -/
def iseg (N m : ℕ) : Finset (Fin N) := Finset.univ.filter fun i => i.val < m

/-- The initial segment `{i | i < m}` of `Fin N` has `m` elements for `m ≤ N`. -/
theorem card_iseg {N m : ℕ} (hm : m ≤ N) : (iseg N m).card = m := by
  unfold iseg
  rw [Fin.card_filter_val_lt]
  omega

/-- The image of `{i | i < m}` under the cycle `(0 1 ⋯ m)` is `{i | 1 ≤ i ≤ m}`. -/
theorem iseg_map_cycleRange {n m : ℕ} (hm : m ≤ n) :
    (iseg (n + 1) m).map (Fin.cycleRange (⟨m, by omega⟩ : Fin (n + 1))).toEmbedding =
      Finset.univ.filter fun i : Fin (n + 1) => 1 ≤ i.val ∧ i.val < m + 1 := by
  ext k
  simp only [iseg, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [Fin.coe_cycleRange_of_lt (show i < ⟨m, by omega⟩ from hi)]
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨⟨k.val - 1, by omega⟩, by simp; omega, ?_⟩
    ext
    rw [Fin.coe_cycleRange_of_lt (show (⟨k.val - 1, by omega⟩ : Fin (n + 1)) < ⟨m, by omega⟩
      from by simp [Fin.lt_def]; omega)]
    simp; omega

/-- Aomoto's recurrence along initial segments. -/
theorem aomoto_iseg_step {n : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 1 / 2 ≤ c.re)
    {m : ℕ} (hm : m ≤ n) :
    (a + ((n : ℂ) - m) * c) * aomotoInt (n + 1) a b c (iseg (n + 1) m) =
      (a + b + (2 * (n : ℂ) - m) * c) * aomotoInt (n + 1) a b c (iseg (n + 1) (m + 1)) := by
  set S := Finset.univ.filter fun i : Fin (n + 1) => 1 ≤ i.val ∧ i.val < m + 1 with hSdef
  have hS0 : (0 : Fin (n + 1)) ∉ S := by simp [hSdef]
  have hmap := iseg_map_cycleRange (n := n) hm
  have hcard : S.card = m := by
    rw [hSdef, ← hmap, Finset.card_map, card_iseg (by omega)]
  have hins : insert 0 S = iseg (n + 1) (m + 1) := by
    ext k
    simp only [hSdef, iseg, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (rfl | ⟨_, h⟩)
      · simp
      · exact h
    · intro h
      by_cases hk : k.val = 0
      · left; ext; exact hk
      · right; omega
  have h := aomoto_step ha hb hc hS0
  rw [hcard, hins] at h
  rw [← aomotoInt_map_perm a b c (iseg (n + 1) m) (Fin.cycleRange ⟨m, by omega⟩), hmap]
  exact h

/-- The ratio in Aomoto's formula. -/
def aomotoFactor (N : ℕ) (a b c : ℂ) (j : ℕ) : ℂ :=
  (a + ((N - 1 - j : ℕ) : ℂ) * c) / (a + b + ((2 * N - 2 - j : ℕ) : ℂ) * c)

/-- The Selberg integral as a function of its parameters. -/
def selbergInt (N : ℕ) (a b c : ℂ) : ℂ := ∫ t in cube N, selbergIntegrand N a b c t

/-- Aomoto's integral with empty index set is the Selberg integral. -/
theorem aomotoInt_empty (N : ℕ) (a b c : ℂ) : aomotoInt N a b c ∅ = selbergInt N a b c := by
  simp [aomotoInt, selbergInt, mono]

/-- Aomoto's formula for `Re c ≥ 1/2`: the integral of `t₁ ⋯ tₘ Φ(t)` is
`∏_{j<m} (a + (N-1-j)c)/(a + b + (2N-2-j)c)` times the Selberg integral. -/
theorem aomoto_prod {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 1 / 2 ≤ c.re)
    {m : ℕ} (hm : m ≤ N) :
    aomotoInt N a b c (iseg N m) =
      (∏ j ∈ Finset.range m, aomotoFactor N a b c j) * selbergInt N a b c := by
  induction m with
  | zero =>
    rw [← aomotoInt_empty]
    simp [iseg]
  | succ m ih =>
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hstep := aomoto_iseg_step ha hb hc (n := n) (m := m) (by omega)
    rw [Finset.prod_range_succ, mul_comm _ (aomotoFactor _ _ _ _ m), mul_assoc, ← ih (by omega)]
    have hden : a + b + (2 * (n : ℂ) - m) * c ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.zero_re] at this
      have hnm : (m : ℝ) ≤ n := by exact_mod_cast (by omega : m ≤ n)
      norm_num at this
      nlinarith
    unfold aomotoFactor
    have e1 : (((n + 1 - 1 - m : ℕ) : ℂ)) = (n : ℂ) - m := by
      rw [show n + 1 - 1 - m = n - m by omega, Nat.cast_sub (by omega)]
    have e2 : (((2 * (n + 1) - 2 - m : ℕ) : ℂ)) = 2 * (n : ℂ) - m := by
      rw [show 2 * (n + 1) - 2 - m = 2 * n - m by omega, Nat.cast_sub (by omega)]
      push_cast; ring
    rw [e1, e2, div_mul_eq_mul_div, eq_div_iff hden]
    linear_combination -hstep

/-- Multiplying the integrand by `t₁ ⋯ t_N` shifts `a` to `a + 1`. -/
theorem mono_univ_mul_selbergIntegrand {N : ℕ} {a b c : ℂ} (ha : a ≠ 0) (t : Fin N → ℝ) :
    mono Finset.univ t * selbergIntegrand N a b c t = selbergIntegrand N (a + 1) b c t := by
  rw [selbergIntegrand_eq, selbergIntegrand_eq, mono, ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold weight
  rw [add_sub_cancel_right]
  rcases eq_or_ne (t i) 0 with h0 | h0
  · rw [h0]
    simp [Complex.zero_cpow ha]
  · rw [cpow_eq_mul_cpow_sub_one (by exact_mod_cast h0) a]
    ring

/-- **The `a`-shift of the Selberg integral.** -/
theorem selbergInt_add_one {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 1 / 2 ≤ c.re) :
    selbergInt N (a + 1) b c =
      (∏ j ∈ Finset.range N, aomotoFactor N a b c j) * selbergInt N a b c := by
  rw [← aomoto_prod ha hb hc le_rfl]
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hiseg : iseg N N = Finset.univ := by ext i; simp [iseg]
  rw [hiseg, aomotoInt, selbergInt]
  exact setIntegral_congr_fun (measurableSet_cube N) fun t ht =>
    (mono_univ_mul_selbergIntegrand ha0 t).symm

/-! ### Reflection `t ↦ 1 - t` -/

/-- The reflection `t ↦ 1 - t` of the cube. -/
def reflect {N : ℕ} (t : Fin N → ℝ) : Fin N → ℝ := fun i => 1 - t i

/-- The reflection `t ↦ 1 - t` is an involution. -/
theorem reflect_reflect {N : ℕ} (t : Fin N → ℝ) : reflect (reflect t) = t := by
  ext i; simp [reflect]

/-- The reflection `t ↦ 1 - t` is measurable. -/
theorem measurable_reflect (N : ℕ) : Measurable (reflect (N := N)) := by
  unfold reflect; fun_prop

/-- The reflection `t ↦ 1 - t` preserves Lebesgue measure. -/
theorem measurePreserving_reflect (N : ℕ) : MeasurePreserving (reflect (N := N)) :=
  volume_preserving_pi fun _ => Measure.measurePreserving_sub_left volume (1 : ℝ)

/-- The reflection `t ↦ 1 - t` is a measurable embedding. -/
theorem measurableEmbedding_reflect (N : ℕ) : MeasurableEmbedding (reflect (N := N)) :=
  MeasurableEmbedding.of_measurable_inverse (measurable_reflect N)
    (by
      have : Set.range (reflect (N := N)) = Set.univ :=
        Set.eq_univ_of_forall fun t => ⟨reflect t, reflect_reflect t⟩
      rw [this]; exact MeasurableSet.univ)
    (measurable_reflect N) reflect_reflect

/-- The cube is invariant under `t ↦ 1 - t`. -/
theorem reflect_preimage_cube (N : ℕ) : reflect ⁻¹' cube N = cube N := by
  ext t
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, reflect, Set.mem_Icc]
  exact ⟨fun h i => ⟨by linarith [(h i).2], by linarith [(h i).1]⟩,
    fun h i => ⟨by linarith [(h i).2], by linarith [(h i).1]⟩⟩

/-- Integrals over the cube are invariant under `t ↦ 1 - t`. -/
theorem integral_cube_reflect {N : ℕ} (g : (Fin N → ℝ) → ℂ) :
    ∫ t in cube N, g (reflect t) = ∫ t in cube N, g t := by
  conv_lhs => rw [← reflect_preimage_cube N]
  exact (measurePreserving_reflect N).setIntegral_preimage_emb
    (measurableEmbedding_reflect N) _ _

/-- The reflection `t ↦ 1 - t` exchanges the parameters `a` and `b` of the integrand. -/
theorem selbergIntegrand_reflect (N : ℕ) (a b c : ℂ) (t : Fin N → ℝ) :
    selbergIntegrand N a b c (reflect t) = selbergIntegrand N b a c t := by
  rw [selbergIntegrand_eq, selbergIntegrand_eq]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [weight, reflect]
    push_cast
    rw [sub_sub_cancel]
    ring
  · unfold vdm
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    simp only [reflect, show 1 - t i - (1 - t j) = -(t i - t j) by ring, abs_neg]

/-- **Symmetry** of the Selberg integral in `a` and `b`. -/
theorem selbergInt_comm (N : ℕ) (a b c : ℂ) : selbergInt N a b c = selbergInt N b a c := by
  unfold selbergInt
  rw [← integral_cube_reflect]
  simp only [selbergIntegrand_reflect]

end DLMF.Selberg
end
end
