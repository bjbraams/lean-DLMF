/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import Mathlib.Tactic.CrossRefAttribute
public import DLMF.Hypergeometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.Liouville
public import DLMF.Hypergeometric.Identities

/-!
# The Selberg and Aomoto integrals (AAR §§8.1–8.4)

Mathlib has the Selberg *sieve*, not Selberg's integral. The `n = 1` case is the Beta
integral already in Mathlib (`Complex.betaIntegral`).

## Proof of Selberg's integral

We follow Aomoto's proof (AAR §8.1), completed by Carlson's theorem and a recursion in the
dimension, and extend to the full domain of convergence by analytic continuation.

1. *Integration by parts* in one coordinate (`integral_cube_ibp`), with the Vandermonde factor
   handled off the diagonal, gives **Aomoto's recurrence** (`aomoto_step`) for `Re c ≥ 1/2`,
   and hence the shift `S(a+1) = ∏ⱼ (a+(n-1-j)c)/(a+b+(2n-2-j)c) · S(a)`
   (`selbergInt_add_one`).
2. `S/R` is therefore `1`-periodic in `a`; it is holomorphic and of polynomial growth on
   vertical strips, so it is constant by **Carlson's theorem** (`selbergRatio_eq_one_left`).
   By the symmetry `a ↔ b` it depends on `c` only.
3. A boundary integration by parts gives the **dimension recursion**
   `(a + n c) S_{n+1}(a, 1, c) = S_n(a, 1 + 2c, c)` (`selbergInt_succ_one`), which the
   right-hand side also satisfies, so the constant is `1` (`selbergInt_eq_of_half_le`).
4. The identity extends to `Re c > 0` by analytic continuation in `c`. Integrability on the
   full domain `Re c > -min(1/n, Re a/(n-1), Re b/(n-1))` follows from a **Landau-type
   theorem** for Mellin transforms of positive measures
   (`integrable_mul_rpow_of_analytic`), after which the identity theorem gives
   `selberg_integral`.
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

lemma measurableSet_cube (n : ℕ) : MeasurableSet (cube n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

lemma cons_mem_cube {n : ℕ} {x : ℝ} {y : Fin n → ℝ} :
    (Fin.cons x y : Fin (n + 1) → ℝ) ∈ cube (n + 1) ↔ x ∈ Icc (0 : ℝ) 1 ∧ y ∈ cube n := by
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Fin.forall_fin_succ, Fin.cons_zero,
    Fin.cons_succ]

/-- Splitting off the zeroth coordinate. -/
lemma integral_cube_succ {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℂ)
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

lemma selbergIntegrand_eq (n : ℕ) (a b c : ℂ) (t : Fin n → ℝ) :
    selbergIntegrand n a b c t = (∏ i, weight a b (t i)) * vdm n c t := rfl

lemma vdm_cons {n : ℕ} (c : ℂ) (x : ℝ) (y : Fin n → ℝ) :
    vdm (n + 1) c (Fin.cons x y) =
      (∏ j : Fin n, ((|x - y j| : ℝ) : ℂ) ^ (2 * c)) * vdm n c y := by
  simp only [vdm, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ]
  simp

lemma selbergIntegrand_cons {n : ℕ} (a b c : ℂ) (x : ℝ) (y : Fin n → ℝ) :
    selbergIntegrand (n + 1) a b c (Fin.cons x y) =
      weight a b x * (∏ j : Fin n, ((|x - y j| : ℝ) : ℂ) ^ (2 * c)) *
        selbergIntegrand n a b c y := by
  rw [selbergIntegrand_eq, selbergIntegrand_eq, vdm_cons, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

lemma ofReal_cpow_two_mul {x : ℝ} (hx : 0 ≤ x) (c : ℂ) :
    (x : ℂ) ^ (2 * c) = (x : ℂ) ^ c * (x : ℂ) ^ c := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rcases eq_or_ne c 0 with rfl | hc
    · simp
    · simp [Complex.zero_cpow hc, Complex.zero_cpow (mul_ne_zero two_ne_zero hc)]
  · rw [two_mul, Complex.cpow_add _ _ (by exact_mod_cast hx0)]

/-- Symmetric form of the Vandermonde factor, `∏_{i ≠ j} |tᵢ - tⱼ|^c`. -/
lemma vdm_eq_sym (n : ℕ) (c : ℂ) (t : Fin n → ℝ) :
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

lemma vdm_comp_perm (n : ℕ) (c : ℂ) (t : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    vdm n c (t ∘ σ) = vdm n c t := by
  rw [vdm_eq_sym, vdm_eq_sym]
  simp only [Function.comp_apply]
  rw [← Equiv.prod_comp σ (fun i => ∏ j : Fin n,
    if i ≠ j then ((|t i - t j| : ℝ) : ℂ) ^ c else 1)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Equiv.prod_comp σ (fun j => if σ i ≠ j then ((|t (σ i) - t j| : ℝ) : ℂ) ^ c else 1)]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [ne_eq, σ.injective.eq_iff]

lemma selbergIntegrand_comp_perm (n : ℕ) (a b c : ℂ) (t : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    selbergIntegrand n a b c (t ∘ σ) = selbergIntegrand n a b c t := by
  rw [selbergIntegrand_eq, selbergIntegrand_eq, vdm_comp_perm]
  congr 1
  exact Equiv.prod_comp σ (fun i => weight a b (t i))

lemma comp_perm_mem_cube {n : ℕ} (t : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    t ∘ σ ∈ cube n ↔ t ∈ cube n := by
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Function.comp_apply]
  exact ⟨fun h i => by simpa using h (σ.symm i), fun h i => h (σ i)⟩

/-- Integrals over the cube are invariant under permutations of the coordinates. -/
lemma integral_cube_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (g : (Fin n → ℝ) → ℂ) :
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

lemma integrableOn_cube_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) {g : (Fin n → ℝ) → ℂ}
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

lemma ofReal_abs_cpow_eq_exp {u : ℝ} (hu : u ≠ 0) (w : ℂ) :
    ((|u| : ℝ) : ℂ) ^ w = Complex.exp ((Real.log u : ℂ) * w) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast abs_ne_zero.mpr hu),
    ← Complex.ofReal_log (abs_nonneg u), Real.log_abs]

lemma hasDerivAt_abs_sub_cpow {x y : ℝ} (hxy : x ≠ y) (w : ℂ) :
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

lemma hasDerivAt_vprod {n : ℕ} (y : Fin n → ℝ) (c : ℂ) {x : ℝ} (hx : ∀ j, x ≠ y j) :
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

lemma hasDerivAt_ibpF {n : ℕ} (y : Fin n → ℝ) (α β c : ℂ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
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

lemma norm_vprod_le {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ cube n) {c : ℂ} (hc : 0 ≤ c.re)
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
lemma norm_div_mul_vprod_le {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ cube n) {c : ℂ}
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

lemma one_sub_ofReal (x : ℝ) : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; ring

lemma measurable_vprod {n : ℕ} (y : Fin n → ℝ) (c : ℂ) : Measurable (vprod y c) := by
  unfold vprod
  fun_prop

lemma measurable_ibpD {n : ℕ} (y : Fin n → ℝ) (α β c : ℂ) : Measurable (ibpD y α β c) := by
  unfold ibpD
  have := measurable_vprod y c
  fun_prop

lemma continuousOn_ibpF {n : ℕ} (y : Fin n → ℝ) {α β c : ℂ} (hα : 0 < α.re)
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

lemma intervalIntegrable_ibpBound (n : ℕ) {α β c : ℂ} (hα : 0 < α.re)
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

lemma norm_ibpD_le {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ cube n) {α β c : ℂ}
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

lemma ae_mem_Ioo_of_mem_uIoc : ∀ᵐ x : ℝ, x ∈ Set.uIoc (0 : ℝ) 1 → x ∈ Ioo (0 : ℝ) 1 := by
  have hnull : ∀ᵐ x : ℝ, x ≠ 1 := (ae_iff).2 (by simp)
  filter_upwards [hnull] with x hx1 hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  exact ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩

lemma intervalIntegrable_ibpD {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ cube n) {α β c : ℂ}
    (hα : 0 < α.re) (hβ : 0 < β.re ∨ β = 0) (hc : 1 / 2 ≤ c.re) :
    IntervalIntegrable (ibpD y α β c) volume 0 1 := by
  refine (intervalIntegrable_ibpBound n (c := c) hα hβ).mono_fun'
    (measurable_ibpD y α β c).aestronglyMeasurable ?_
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [ae_mem_Ioo_of_mem_uIoc] with x hx hx'
  exact norm_ibpD_le hy hα hβ hc (hx hx')

/-- **One-variable integration by parts.** -/
lemma integral_ibpD {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ cube n) {α β c : ℂ}
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

lemma integrableOn_cube_succ {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℂ)
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

lemma measurable_ibpD_uncurry {n : ℕ} (α β c : ℂ) :
    Measurable (fun p : ℝ × (Fin n → ℝ) => ibpD p.2 α β c p.1) := by
  unfold ibpD vprod
  fun_prop

lemma ae_prod_Ioo_cube {n : ℕ} :
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

lemma integrableOn_ibp {n : ℕ} {α β c : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re ∨ β = 0)
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
lemma integral_cube_ibp {n : ℕ} {α β c : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re ∨ β = 0)
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

lemma integrableOn_weight {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (weight a b) (Icc (0 : ℝ) 1) := by
  have h := Complex.betaIntegral_convergent ha hb
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one] at h
  exact h

lemma integrableOn_prod_cube {n : ℕ} {f : ℝ → ℂ} (hf : IntegrableOn f (Icc (0 : ℝ) 1)) :
    IntegrableOn (fun t : Fin n → ℝ => ∏ i, f (t i)) (cube n) := by
  rw [IntegrableOn, volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod (fun _ => hf)

lemma measurable_selbergIntegrand (n : ℕ) (a b c : ℂ) :
    Measurable (selbergIntegrand n a b c) := by
  unfold selbergIntegrand
  fun_prop

lemma measurable_weight (a b : ℂ) : Measurable (weight a b) := by
  unfold weight
  fun_prop

lemma norm_vdm_le_one {n : ℕ} {c : ℂ} (hc : 0 ≤ c.re) {t : Fin n → ℝ} (ht : t ∈ cube n) :
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

lemma norm_selbergIntegrand_le {n : ℕ} {a b c : ℂ} (hc : 0 ≤ c.re) {t : Fin n → ℝ}
    (ht : t ∈ cube n) : ‖selbergIntegrand n a b c t‖ ≤ ‖∏ i, weight a b (t i)‖ := by
  rw [selbergIntegrand_eq, norm_mul]
  calc ‖∏ i, weight a b (t i)‖ * ‖vdm n c t‖ ≤ ‖∏ i, weight a b (t i)‖ * 1 := by
        gcongr; exact norm_vdm_le_one hc ht
    _ = _ := mul_one _

/-- A bounded measurable function times the Selberg integrand is integrable (`Re c ≥ 0`). -/
lemma integrableOn_mul_selbergIntegrand {n : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 ≤ c.re) {h : (Fin n → ℝ) → ℂ} (hh : Measurable h) {M : ℝ}
    (hM : ∀ t ∈ cube n, ‖h t‖ ≤ M) :
    IntegrableOn (fun t => h t * selbergIntegrand n a b c t) (cube n) := by
  have hW := (integrableOn_prod_cube (n := n) (integrableOn_weight ha hb)).norm.const_mul M
  refine hW.mono' (hh.mul (measurable_selbergIntegrand n a b c)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_cube n)] with t ht
  rw [norm_mul]
  exact mul_le_mul (hM t ht) (norm_selbergIntegrand_le hc ht) (norm_nonneg _)
    ((norm_nonneg _).trans (hM t ht))

lemma selbergIntegrand_eq_cons_tail {n : ℕ} (a b c : ℂ) (t : Fin (n + 1) → ℝ) :
    selbergIntegrand (n + 1) a b c t =
      weight a b (t 0) * vprod (Fin.tail t) c (t 0) * selbergIntegrand n a b c (Fin.tail t) := by
  conv_lhs => rw [← Fin.cons_self_tail t]
  rw [selbergIntegrand_cons]
  rfl

lemma tail_mem_cube {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : t ∈ cube (n + 1)) :
    Fin.tail t ∈ cube n := by
  rw [← Fin.cons_self_tail t, cons_mem_cube] at ht
  exact ht.2

lemma zero_mem_Icc_of_mem_cube {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : t ∈ cube (n + 1)) :
    t 0 ∈ Icc (0 : ℝ) 1 := ht 0 (Set.mem_univ _)

/-- The singular factor `2c/(t₀ - t_{j+1})` is absorbed by `|t₀ - t_{j+1}|^{2c}` when
`Re c ≥ 1/2`. -/
lemma norm_div_mul_selbergIntegrand_le {n : ℕ} {a b c : ℂ} (hc : 1 / 2 ≤ c.re)
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

lemma integrableOn_mul_div_selbergIntegrand {n : ℕ} {a b c : ℂ} (ha : 0 < a.re)
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

lemma cpow_eq_mul_cpow_sub_one {z : ℂ} (hz : z ≠ 0) (w : ℂ) : z ^ w = z * z ^ (w - 1) := by
  conv_lhs => rw [show w = 1 + (w - 1) by ring]
  rw [Complex.cpow_add _ _ hz, Complex.cpow_one]

/-- `ibpD` in terms of the weight. -/
lemma ibpD_eq {n : ℕ} (y : Fin n → ℝ) (α β c : ℂ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ibpD y α β c x = weight α β x * vprod y c x *
      (α * (1 - x) - β * x + x * (1 - x) * ∑ j : Fin n, 2 * c / ((x : ℂ) - y j)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
  have hx1 : (1 - (x : ℂ)) ≠ 0 := by
    rw [one_sub_ofReal]; exact_mod_cast (show (1 - x) ≠ 0 by linarith [hx.2])
  unfold ibpD weight
  rw [cpow_eq_mul_cpow_sub_one hx0 α, cpow_eq_mul_cpow_sub_one hx1 β]
  ring

lemma ibpD_zero_eq {n : ℕ} (y : Fin n → ℝ) (α c : ℂ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ibpD y α 0 c x = weight α 1 x * vprod y c x *
      (α + x * ∑ j : Fin n, 2 * c / ((x : ℂ) - y j)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
  unfold ibpD weight
  rw [cpow_eq_mul_cpow_sub_one hx0 α]
  simp only [sub_self, Complex.cpow_zero, zero_mul, sub_zero, mul_one]
  ring

/-- The diagonal `tᵢ = tⱼ` is a null set. -/
lemma ae_ne_coord {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
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

lemma measurable_mono {N : ℕ} (S : Finset (Fin N)) : Measurable (mono S) := by
  unfold mono; fun_prop

lemma norm_mono_le {N : ℕ} (S : Finset (Fin N)) {t : Fin N → ℝ} (ht : t ∈ cube N) :
    ‖mono S t‖ ≤ 1 := by
  unfold mono
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
  have := ht i (Set.mem_univ _)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [this.1, this.2]

lemma mono_comp_perm {N : ℕ} (S : Finset (Fin N)) (σ : Equiv.Perm (Fin N))
    (t : Fin N → ℝ) : mono S (t ∘ σ) = mono (S.map σ.toEmbedding) t := by
  unfold mono
  simp [Finset.prod_map]

lemma aomotoInt_map_perm {N : ℕ} (a b c : ℂ) (S : Finset (Fin N)) (σ : Equiv.Perm (Fin N)) :
    aomotoInt N a b c (S.map σ.toEmbedding) = aomotoInt N a b c S := by
  unfold aomotoInt
  rw [← integral_cube_comp_perm σ (fun t => mono S t * selbergIntegrand N a b c t)]
  simp only [mono_comp_perm, selbergIntegrand_comp_perm]

/-- The preimage of `S` under `Fin.succ`. -/
def succPre {n : ℕ} (S : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun j => j.succ ∈ S

lemma mono_eq_tail {n : ℕ} {S : Finset (Fin (n + 1))} (hS : (0 : Fin (n + 1)) ∉ S)
    (t : Fin (n + 1) → ℝ) : mono S t = mono (succPre S) (Fin.tail t) := by
  classical
  unfold mono succPre
  have h1 : ∏ i ∈ S, (t i : ℂ) = ∏ i : Fin (n + 1), if i ∈ S then (t i : ℂ) else 1 := by
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [h1, Fin.prod_univ_succ]
  simp only [hS, ↓reduceIte, one_mul]
  rw [Finset.prod_filter]
  rfl

lemma ae_coord_ne {N : ℕ} (i : Fin N) (x : ℝ) : ∀ᵐ t : Fin N → ℝ, t i ≠ x := by
  rw [volume_pi]
  exact Measure.ae_eval_ne (μ := fun _ : Fin N => (volume : Measure ℝ)) i x

lemma ae_coord_mem_Ioo {n : ℕ} :
    ∀ᵐ t : Fin (n + 1) → ℝ, t ∈ cube (n + 1) → t 0 ∈ Ioo (0 : ℝ) 1 := by
  filter_upwards [ae_coord_ne 0 0, ae_coord_ne 0 1] with t h0 h1 ht
  have := zero_mem_Icc_of_mem_cube ht
  exact ⟨lt_of_le_of_ne this.1 (Ne.symm h0), lt_of_le_of_ne this.2 h1⟩

/-- The integration-by-parts identity behind Aomoto's recurrence. -/
lemma aomoto_ibp {n : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 1 / 2 ≤ c.re)
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
lemma aomoto_expand {n : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 1 / 2 ≤ c.re)
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

lemma two_mul_integral_eq_of_swap {N : ℕ} (σ : Equiv.Perm (Fin N)) {f g : (Fin N → ℝ) → ℂ}
    (hf : IntegrableOn f (cube N)) (hg : ∀ᵐ t, t ∈ cube N → f t + f (t ∘ σ) = g t) :
    2 * ∫ t in cube N, f t = ∫ t in cube N, g t := by
  have h1 := integral_cube_comp_perm σ f
  rw [← setIntegral_congr_ae (measurableSet_cube N) hg,
    integral_add hf (integrableOn_cube_comp_perm σ hf), h1]
  ring

lemma mono_comp_of_fix {N : ℕ} {S : Finset (Fin N)} {σ : Equiv.Perm (Fin N)}
    (hσ : ∀ i ∈ S, σ i = i) (t : Fin N → ℝ) : mono S (t ∘ σ) = mono S t := by
  unfold mono
  exact Finset.prod_congr rfl fun i hi => by simp [hσ i hi]

lemma swap_fix_of_not_mem {n : ℕ} {S : Finset (Fin (n + 1))} (hS : (0 : Fin (n + 1)) ∉ S)
    {k : Fin (n + 1)} (hk : k ∉ S) : ∀ i ∈ S, Equiv.swap (0 : Fin (n + 1)) k i = i := by
  intro i hi
  refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
  · rintro rfl; exact hS hi
  · rintro rfl; exact hk hi

lemma integrableOn_mono_selberg {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 ≤ c.re) (S : Finset (Fin N)) :
    IntegrableOn (fun t => mono S t * selbergIntegrand N a b c t) (cube N) :=
  integrableOn_mul_selbergIntegrand ha hb hc (measurable_mono _) (fun _ ht => norm_mono_le _ ht)

/-- The cross term when `j+1 ∉ S`. -/
lemma aomoto_cross_not_mem {n : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
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
lemma aomoto_cross_mem {n : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
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

lemma card_succPre {n : ℕ} {S : Finset (Fin (n + 1))} (hS : (0 : Fin (n + 1)) ∉ S) :
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
lemma aomoto_step {n : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 1 / 2 ≤ c.re)
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

lemma card_iseg {N m : ℕ} (hm : m ≤ N) : (iseg N m).card = m := by
  unfold iseg
  rw [Fin.card_filter_val_lt]
  omega

lemma iseg_map_cycleRange {n m : ℕ} (hm : m ≤ n) :
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
lemma aomoto_iseg_step {n : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 1 / 2 ≤ c.re)
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

lemma aomotoInt_empty (N : ℕ) (a b c : ℂ) : aomotoInt N a b c ∅ = selbergInt N a b c := by
  simp [aomotoInt, selbergInt, mono]

lemma aomoto_prod {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 1 / 2 ≤ c.re)
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

lemma mono_univ_mul_selbergIntegrand {N : ℕ} {a b c : ℂ} (ha : a ≠ 0) (t : Fin N → ℝ) :
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
lemma selbergInt_add_one {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
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

lemma reflect_reflect {N : ℕ} (t : Fin N → ℝ) : reflect (reflect t) = t := by
  ext i; simp [reflect]

lemma measurable_reflect (N : ℕ) : Measurable (reflect (N := N)) := by
  unfold reflect; fun_prop

lemma measurePreserving_reflect (N : ℕ) : MeasurePreserving (reflect (N := N)) :=
  volume_preserving_pi fun _ => Measure.measurePreserving_sub_left volume (1 : ℝ)

lemma measurableEmbedding_reflect (N : ℕ) : MeasurableEmbedding (reflect (N := N)) :=
  MeasurableEmbedding.of_measurable_inverse (measurable_reflect N)
    (by
      have : Set.range (reflect (N := N)) = Set.univ :=
        Set.eq_univ_of_forall fun t => ⟨reflect t, reflect_reflect t⟩
      rw [this]; exact MeasurableSet.univ)
    (measurable_reflect N) reflect_reflect

lemma reflect_preimage_cube (N : ℕ) : reflect ⁻¹' cube N = cube N := by
  ext t
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, reflect, Set.mem_Icc]
  exact ⟨fun h i => ⟨by linarith [(h i).2], by linarith [(h i).1]⟩,
    fun h i => ⟨by linarith [(h i).2], by linarith [(h i).1]⟩⟩

lemma integral_cube_reflect {N : ℕ} (g : (Fin N → ℝ) → ℂ) :
    ∫ t in cube N, g (reflect t) = ∫ t in cube N, g t := by
  conv_lhs => rw [← reflect_preimage_cube N]
  exact (measurePreserving_reflect N).setIntegral_preimage_emb
    (measurableEmbedding_reflect N) _ _

lemma selbergIntegrand_reflect (N : ℕ) (a b c : ℂ) (t : Fin N → ℝ) :
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
lemma selbergInt_comm (N : ℕ) (a b c : ℂ) : selbergInt N a b c = selbergInt N b a c := by
  unfold selbergInt
  rw [← integral_cube_reflect]
  simp only [selbergIntegrand_reflect]

/-! ### The recursion in the dimension -/

lemma scaling_cross {n : ℕ} {a c : ℂ} (ha : 0 < a.re) (hc : 1 / 2 ≤ c.re) (j : Fin n) :
    ∫ t in cube (n + 1), (t 0 : ℂ) * (2 * c / ((t 0 : ℂ) - t j.succ) *
        selbergIntegrand (n + 1) a 1 c t) = c * selbergInt (n + 1) a 1 c := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin (n + 1)), σ = Equiv.swap 0 j.succ := ⟨_, rfl⟩
  have hsw0 : ∀ t : Fin (n + 1) → ℝ, (t ∘ σ) 0 = t j.succ := fun t => by simp [hσ]
  have hsw1 : ∀ t : Fin (n + 1) → ℝ, (t ∘ σ) j.succ = t 0 := fun t => by simp [hσ]
  have h1 : (0 : ℝ) < (1 : ℂ).re := by simp
  have hI : IntegrableOn (fun t => (t 0 : ℂ) * (2 * c / ((t 0 : ℂ) - t j.succ) *
      selbergIntegrand (n + 1) a 1 c t)) (cube (n + 1)) := by
    refine integrableOn_mul_div_selbergIntegrand ha h1 hc j (M := 1) (by fun_prop) ?_
    intro t ht
    have h0 := zero_mem_Icc_of_mem_cube ht
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith [h0.1, h0.2]
  have h2 := two_mul_integral_eq_of_swap σ hI
    (g := fun t => 2 * c * selbergIntegrand (n + 1) a 1 c t) (by
      filter_upwards [ae_ne_coord (Fin.succ_ne_zero j).symm] with t hne _
      simp only [hsw0, hsw1, selbergIntegrand_comp_perm]
      have hd : (t 0 : ℂ) - t j.succ ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
      have hd' : (t j.succ : ℂ) - t 0 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne.symm)
      field_simp
      ring)
  rw [integral_const_mul] at h2
  unfold selbergInt
  linear_combination h2 / 2

/-- **The recursion in the dimension**: `(a + n c) S_{n+1}(a, 1, c) = S_n(a, 1 + 2c, c)`. -/
lemma selbergInt_succ_one {n : ℕ} {a c : ℂ} (ha : 0 < a.re) (hc : 1 / 2 ≤ c.re) :
    (a + n * c) * selbergInt (n + 1) a 1 c = selbergInt n a (1 + 2 * c) c := by
  have h1 : (0 : ℝ) < (1 : ℂ).re := by simp
  have hc0 : (0 : ℝ) ≤ c.re := by linarith
  have hK : IntegrableOn (selbergIntegrand n a 1 c) (cube n) := by
    have := integrableOn_mul_selbergIntegrand ha h1 hc0 (n := n) (h := fun _ => (1 : ℂ))
      (M := 1) measurable_const (fun _ _ => by simp)
    simpa using this
  have h := integral_cube_ibp ha (Or.inr rfl) hc hK
  simp only [↓reduceIte] at h
  have hR : ∫ y in cube n, selbergIntegrand n a 1 c y * vprod y c 1 =
      selbergInt n a (1 + 2 * c) c := by
    refine setIntegral_congr_fun (measurableSet_cube n) fun y hy => ?_
    rw [selbergIntegrand_eq, selbergIntegrand_eq, vprod]
    rw [mul_right_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have hyi := hy i (Set.mem_univ _)
    simp only [weight, sub_self, Complex.cpow_zero, mul_one, add_sub_cancel_left]
    rw [show |1 - y i| = 1 - y i from abs_of_nonneg (by linarith [hyi.2]), one_sub_ofReal]
  have hL : ∫ t in cube (n + 1), selbergIntegrand n a 1 c (Fin.tail t) *
      ibpD (Fin.tail t) a 0 c (t 0) =
      ∫ t in cube (n + 1), (a * selbergIntegrand (n + 1) a 1 c t +
        ∑ j : Fin n, (t 0 : ℂ) * (2 * c / ((t 0 : ℂ) - t j.succ) *
          selbergIntegrand (n + 1) a 1 c t)) := by
    refine setIntegral_congr_ae (measurableSet_cube _) ?_
    filter_upwards [ae_coord_mem_Ioo] with t ht0 ht
    rw [ibpD_zero_eq _ _ _ (ht0 ht), selbergIntegrand_eq_cons_tail, Finset.mul_sum]
    simp only [Fin.tail]
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      ring
  have hI0 : IntegrableOn (fun t => a * selbergIntegrand (n + 1) a 1 c t) (cube (n + 1)) := by
    have := integrableOn_mul_selbergIntegrand ha h1 hc0 (n := n + 1) (h := fun _ => a)
      (M := ‖a‖) measurable_const (fun _ _ => le_rfl)
    simpa using this
  have hIj : ∀ j : Fin n, IntegrableOn (fun t => (t 0 : ℂ) * (2 * c / ((t 0 : ℂ) - t j.succ) *
      selbergIntegrand (n + 1) a 1 c t)) (cube (n + 1)) := by
    intro j
    refine integrableOn_mul_div_selbergIntegrand ha h1 hc j (M := 1) (by fun_prop) ?_
    intro t ht
    have h0 := zero_mem_Icc_of_mem_cube ht
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith [h0.1, h0.2]
  rw [hL, hR, integral_add hI0 (integrable_finsetSum _ fun j _ => hIj j), integral_const_mul,
    integral_finsetSum _ fun j _ => hIj j] at h
  simp only [scaling_cross ha hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h
  rw [← h]
  unfold selbergInt
  ring

/-! ### Holomorphy of parametric integrals -/

/-- A parametric integral of functions holomorphic in the parameter, locally dominated by an
integrable function, is holomorphic. -/
theorem differentiableOn_integral_of_dominated {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {U : Set ℂ} (hU : IsOpen U) {F : ℂ → α → ℂ}
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) μ)
    (hdiff : ∀ᵐ x ∂μ, DifferentiableOn ℂ (fun z => F z x) U)
    (hbound : ∀ z₀ ∈ U, ∃ ε > 0, Metric.closedBall z₀ ε ⊆ U ∧ ∃ g : α → ℝ, Integrable g μ ∧
      ∀ᵐ x ∂μ, ∀ z ∈ Metric.closedBall z₀ ε, ‖F z x‖ ≤ g x) :
    DifferentiableOn ℂ (fun z => ∫ x, F z x ∂μ) U := by
  apply Complex.differentiableOn_integral_of_locally_dominated hU hmeas hdiff
  intro z₀ hz₀
  obtain ⟨ε, hε, _, g, hg, hgb⟩ := hbound z₀ hz₀
  exact ⟨Metric.closedBall z₀ ε, Metric.closedBall_mem_nhds z₀ hε, g, hg, hgb⟩

/-! ### The right-hand side -/

/-- The right-hand side of Selberg's formula. -/
def selbergRHS (n : ℕ) (a b c : ℂ) : ℂ :=
  ∏ j : Fin n,
    Gamma (a + (j : ℕ) * c) * Gamma (b + (j : ℕ) * c) * Gamma (1 + ((j : ℕ) + 1) * c) /
      (Gamma (a + b + (n + j - 1 : ℕ) * c) * Gamma (1 + c))

lemma selbergRHS_eq_range (n : ℕ) (a b c : ℂ) : selbergRHS n a b c =
    ∏ j ∈ Finset.range n, Gamma (a + j * c) * Gamma (b + j * c) * Gamma (1 + (j + 1) * c) /
      (Gamma (a + b + (n + j - 1 : ℕ) * c) * Gamma (1 + c)) :=
  Fin.prod_univ_eq_prod_range (fun j : ℕ => Gamma (a + j * c) * Gamma (b + j * c) *
    Gamma (1 + (j + 1) * c) / (Gamma (a + b + (n + j - 1 : ℕ) * c) * Gamma (1 + c))) n

lemma selbergRHS_comm (n : ℕ) (a b c : ℂ) : selbergRHS n a b c = selbergRHS n b a c := by
  unfold selbergRHS
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [add_comm a b]
  ring

lemma re_add_nat_mul_pos {a c : ℂ} (ha : 0 < a.re) (hc : 0 ≤ c.re) (x : ℝ) (hx : 0 ≤ x) :
    0 < (a + x * c).re := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  nlinarith

lemma Gamma_ne_zero_of_re_pos' {z : ℂ} (hz : 0 < z.re) : Gamma z ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos hz

/-- The `a`-shift of the right-hand side. -/
lemma selbergRHS_add_one {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 ≤ c.re) :
    selbergRHS N (a + 1) b c =
      (∏ j ∈ Finset.range N, aomotoFactor N a b c j) * selbergRHS N a b c := by
  rw [selbergRHS_eq_range, selbergRHS_eq_range]
  have hab : 0 < (a + b).re := by simp; linarith
  -- each factor
  have hfac : ∀ j ∈ Finset.range N,
      Gamma (a + 1 + j * c) * Gamma (b + j * c) * Gamma (1 + (j + 1) * c) /
          (Gamma (a + 1 + b + (N + j - 1 : ℕ) * c) * Gamma (1 + c)) =
        (a + j * c) / (a + b + (N + j - 1 : ℕ) * c) *
          (Gamma (a + j * c) * Gamma (b + j * c) * Gamma (1 + (j + 1) * c) /
            (Gamma (a + b + (N + j - 1 : ℕ) * c) * Gamma (1 + c))) := by
    intro j _
    have h1 : 0 < (a + (j : ℂ) * c).re := by
      have := re_add_nat_mul_pos ha hc j (Nat.cast_nonneg j); simpa using this
    have h2 : 0 < (a + b + ((N + j - 1 : ℕ) : ℂ) * c).re := by
      have := re_add_nat_mul_pos hab hc (N + j - 1 : ℕ) (Nat.cast_nonneg _); simpa using this
    have hc1 : 0 < (1 + c).re := by simp; linarith
    rw [show a + 1 + (j : ℂ) * c = (a + j * c) + 1 by ring,
      show a + 1 + b + ((N + j - 1 : ℕ) : ℂ) * c = (a + b + (N + j - 1 : ℕ) * c) + 1 by ring,
      Complex.Gamma_add_one _ (fun h => by simp [h] at h1),
      Complex.Gamma_add_one _ (fun h => by simp [h] at h2)]
    have g1 := Gamma_ne_zero_of_re_pos' h1
    have g2 := Gamma_ne_zero_of_re_pos' h2
    have g3 := Gamma_ne_zero_of_re_pos' hc1
    have n2 : a + b + ((N + j - 1 : ℕ) : ℂ) * c ≠ 0 := fun h => by simp [h] at h2
    field_simp
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_range_reflect (fun j : ℕ => (a + (j : ℂ) * c) /
    (a + b + ((N + j - 1 : ℕ) : ℂ) * c)) N]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  unfold aomotoFactor
  rw [show N + (N - 1 - j) - 1 = 2 * N - 2 - j by omega]

/-- The dimension recursion of the right-hand side. -/
lemma selbergRHS_succ_one {n : ℕ} {a c : ℂ} (ha : 0 < a.re) (hc : 0 ≤ c.re) :
    (a + n * c) * selbergRHS (n + 1) a 1 c = selbergRHS n a (1 + 2 * c) c := by
  rw [selbergRHS_eq_range, selbergRHS_eq_range]
  set u : ℕ → ℂ := fun j => Gamma (a + j * c) with hu
  set v : ℕ → ℂ := fun j => Gamma (1 + j * c) with hv
  set w : ℕ → ℂ := fun j => Gamma (a + 1 + j * c) with hw
  set G := Gamma (1 + c) with hG
  have hL : ∀ j ∈ Finset.range (n + 1),
      Gamma (a + j * c) * Gamma (1 + j * c) * Gamma (1 + (j + 1) * c) /
        (Gamma (a + 1 + ((n + 1 + j - 1 : ℕ) : ℂ) * c) * Gamma (1 + c)) =
      u j * v j * v (j + 1) / (w (n + j) * G) := by
    intro j _
    simp only [hu, hv, hw, hG]
    rw [show n + 1 + j - 1 = n + j by omega]
    push_cast; ring_nf
  have hR : ∀ j ∈ Finset.range n,
      Gamma (a + j * c) * Gamma (1 + 2 * c + j * c) * Gamma (1 + (j + 1) * c) /
        (Gamma (a + (1 + 2 * c) + ((n + j - 1 : ℕ) : ℂ) * c) * Gamma (1 + c)) =
      u j * v (j + 2) * v (j + 1) / (w (n + j + 1) * G) := by
    intro j hj
    rw [Finset.mem_range] at hj
    simp only [hu, hv, hw, hG]
    rw [Nat.cast_sub (by omega)]
    push_cast; ring_nf
  rw [Finset.prod_congr rfl hL, Finset.prod_congr rfl hR]
  simp only [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range]
  rw [Finset.prod_range_succ u, Finset.prod_range_succ' v, Finset.prod_range_succ
    (fun j => v (j + 1)), Finset.prod_range_succ' (fun j => w (n + j))]
  have hT : (∏ j ∈ Finset.range n, v (j + 2)) * G =
      (∏ j ∈ Finset.range n, v (j + 1)) * v (n + 1) := by
    have h := Finset.prod_range_succ' (fun j => v (j + 1)) n
    rw [Finset.prod_range_succ] at h
    simp only [hv, hG] at h ⊢
    rw [show (((0 : ℕ) + 1 : ℕ) : ℂ) = 1 by simp, one_mul] at h
    rw [h]
  have hv0 : v 0 = 1 := by simp [hv]
  have hc1 : 0 < (1 + c).re := by simp; linarith
  have hGne : G ≠ 0 := Gamma_ne_zero_of_re_pos' hc1
  have hwne : ∀ k : ℕ, w k ≠ 0 := fun k => Gamma_ne_zero_of_re_pos' (by
    have := re_add_nat_mul_pos (a := a + 1) (by simp; linarith) hc k (Nat.cast_nonneg k)
    simpa using this)
  have hW : (∏ j ∈ Finset.range n, w (n + (j + 1))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hwne _
  have hun : (a + n * c) * u n = w n := by
    simp only [hu, hw]
    have h1 : 0 < (a + (n : ℂ) * c).re := by
      have := re_add_nat_mul_pos ha hc n (Nat.cast_nonneg n); simpa using this
    rw [show a + 1 + (n : ℂ) * c = (a + n * c) + 1 by ring,
      Complex.Gamma_add_one _ (fun h => by simp [h] at h1)]
  have hwn : w (n + 0) = w n := by simp
  rw [hwn, hv0]
  simp only [show ∀ j : ℕ, n + j + 1 = n + (j + 1) from fun j => by omega]
  rw [← hun]
  have hT' : ∏ j ∈ Finset.range n, v (j + 2) =
      (∏ j ∈ Finset.range n, v (j + 1)) * v (n + 1) / G := by
    rw [eq_div_iff hGne, hT]
  rw [hT']
  have hun0 : u n ≠ 0 := Gamma_ne_zero_of_re_pos' (by
    have := re_add_nat_mul_pos ha hc n (Nat.cast_nonneg n); simpa using this)
  have han : a + n * c ≠ 0 := fun h => by
    have := re_add_nat_mul_pos ha hc n (Nat.cast_nonneg n); simp [h] at this
  field_simp
  ring

/-! ### Holomorphy in the parameters -/

lemma ae_cube_coords_Ioo (N : ℕ) :
    ∀ᵐ t : Fin N → ℝ, t ∈ cube N → ∀ i, t i ∈ Ioo (0 : ℝ) 1 := by
  have h0 : ∀ᵐ t : Fin N → ℝ, ∀ i, t i ≠ 0 := ae_all_iff.2 fun i => ae_coord_ne i 0
  have h1 : ∀ᵐ t : Fin N → ℝ, ∀ i, t i ≠ 1 := ae_all_iff.2 fun i => ae_coord_ne i 1
  filter_upwards [h0, h1] with t ht0 ht1 ht i
  have := ht i (Set.mem_univ _)
  exact ⟨lt_of_le_of_ne this.1 (Ne.symm (ht0 i)), lt_of_le_of_ne this.2 (ht1 i)⟩

lemma norm_weight_le_of_re_le {a a' b : ℂ} (h : a'.re ≤ a.re) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : ‖weight a b x‖ ≤ ‖weight a' b x‖ := by
  unfold weight
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1,
    Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2.le ?_
  simp only [Complex.sub_re, Complex.one_re]
  linarith

lemma norm_weight_le_one_left {a b : ℂ} (h : 1 ≤ a.re) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ‖weight a b x‖ ≤ ‖weight 1 b x‖ := by
  exact norm_weight_le_of_re_le (a := a) (a' := 1) (b := b) (by rw [Complex.one_re]; exact h) hx

lemma differentiableAt_ofReal_cpow_sub_one {x : ℝ} (hx : 0 < x) (a : ℂ) :
    DifferentiableAt ℂ (fun a : ℂ => (x : ℂ) ^ (a - 1)) a :=
  ((differentiableAt_id.sub_const 1).const_cpow (Or.inl (by exact_mod_cast hx.ne')))

/-- The Selberg integral is holomorphic in `a` on the right half-plane. -/
lemma differentiableOn_selbergInt_a (N : ℕ) {b c : ℂ} (hb : 0 < b.re) (hc : 0 ≤ c.re) :
    DifferentiableOn ℂ (fun a => selbergInt N a b c) {a | 0 < a.re} := by
  unfold selbergInt
  refine differentiableOn_integral_of_dominated (isOpen_lt continuous_const Complex.continuous_re)
    (fun a _ => (measurable_selbergIntegrand N a b c).aestronglyMeasurable) ?_ ?_
  · filter_upwards [ae_restrict_mem (measurableSet_cube N),
      (ae_restrict_iff' (measurableSet_cube N)).2 (ae_cube_coords_Ioo N)] with t ht ht'
    intro a _
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold selbergIntegrand
    refine DifferentiableAt.mul (DifferentiableAt.fun_finsetProd fun i _ => ?_)
      (differentiableAt_const _)
    exact (differentiableAt_ofReal_cpow_sub_one (ht' i).1 a).mul (differentiableAt_const _)
  · intro a₀ ha₀
    refine ⟨a₀.re / 2, by simp at ha₀; positivity, fun z hz => ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      have := Complex.abs_re_le_norm (z - a₀)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      simp at ha₀
      have h2 : |(z - a₀).re| ≤ a₀.re / 2 := this.trans hz
      rw [Complex.sub_re, abs_le] at h2
      linarith
    refine ⟨fun t => ‖∏ i, weight ((a₀.re / 2 : ℝ) : ℂ) b (t i)‖, ?_, ?_⟩
    · exact (integrableOn_prod_cube (n := N) (integrableOn_weight (by simp at ha₀ ⊢; positivity)
        hb)).norm
    · filter_upwards [ae_restrict_mem (measurableSet_cube N),
        (ae_restrict_iff' (measurableSet_cube N)).2 (ae_cube_coords_Ioo N)] with t ht ht' z hz
      refine (norm_selbergIntegrand_le hc ht).trans ?_
      rw [norm_prod, norm_prod]
      refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
      refine norm_weight_le_of_re_le ?_ (ht' i)
      have := Complex.abs_re_le_norm (z - a₀)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have h2 : |(z - a₀).re| ≤ a₀.re / 2 := this.trans hz
      rw [Complex.sub_re, abs_le] at h2
      simp only [Complex.ofReal_re]
      linarith

/-! ### Carlson's theorem in `a` -/

lemma re_pos_add_nat_mul {a c : ℂ} (ha : 0 < a.re) (hc : 0 ≤ c.re) (k : ℕ) :
    0 < (a + (k : ℂ) * c).re := by
  have := re_add_nat_mul_pos ha hc k (Nat.cast_nonneg k); simpa using this

lemma selbergRHS_ne_zero {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 ≤ c.re) :
    selbergRHS N a b c ≠ 0 := by
  have hab : 0 < (a + b).re := by simp; linarith
  have hc1 : 0 < (1 : ℂ).re := by simp
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  refine div_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) (mul_ne_zero ?_ ?_)
  · exact Gamma_ne_zero_of_re_pos' (re_pos_add_nat_mul ha hc j)
  · exact Gamma_ne_zero_of_re_pos' (re_pos_add_nat_mul hb hc j)
  · have := re_pos_add_nat_mul hc1 hc (j + 1)
    exact Gamma_ne_zero_of_re_pos' (by simpa using this)
  · exact Gamma_ne_zero_of_re_pos' (re_pos_add_nat_mul hab hc _)
  · exact Gamma_ne_zero_of_re_pos' (by simp; linarith)

lemma aomotoFactor_ne_zero {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 ≤ c.re)
    (j : ℕ) : aomotoFactor N a b c j ≠ 0 := by
  have hab : 0 < (a + b).re := by simp; linarith
  unfold aomotoFactor
  refine div_ne_zero (fun h => ?_) (fun h => ?_)
  · have := re_pos_add_nat_mul ha hc (N - 1 - j); rw [h] at this; simp at this
  · have := re_pos_add_nat_mul hab hc (2 * N - 2 - j); rw [h] at this; simp at this

lemma ne_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) : ∀ m : ℕ, s ≠ -m := fun m h => by
  rw [h] at hs; simp at hs; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

lemma differentiableOn_selbergRHS_a (N : ℕ) {b c : ℂ} (hb : 0 < b.re) (hc : 0 ≤ c.re) :
    DifferentiableOn ℂ (fun a => selbergRHS N a b c) {a | 0 < a.re} := by
  intro a ha
  have ha' : 0 < a.re := ha
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold selbergRHS
  refine DifferentiableAt.fun_finsetProd fun j _ => ?_
  have hab : 0 < (a + b).re := by simp; linarith
  refine DifferentiableAt.div (DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_) ?_ ?_
  · exact (Complex.differentiableAt_Gamma _
      (ne_neg_nat_of_re_pos (re_pos_add_nat_mul ha' hc j))).comp a
      (by fun_prop : DifferentiableAt ℂ (fun x : ℂ => x + ((j : ℕ) : ℂ) * c) a)
  · exact differentiableAt_const _
  · exact differentiableAt_const _
  · refine DifferentiableAt.mul ?_ (differentiableAt_const _)
    exact (Complex.differentiableAt_Gamma _
      (ne_neg_nat_of_re_pos (re_pos_add_nat_mul hab hc (N + j - 1)))).comp a
      (by fun_prop : DifferentiableAt ℂ
        (fun x : ℂ => x + b + ((N + (j : ℕ) - 1 : ℕ) : ℂ) * c) a)
  · refine mul_ne_zero (Gamma_ne_zero_of_re_pos' (re_pos_add_nat_mul hab hc _))
      (Gamma_ne_zero_of_re_pos' (by simp; linarith))

/-- Polynomial growth of `1/R` on the strip `1 ≤ Re a ≤ 2`. -/
lemma exists_norm_recip_selbergRHS_le (N : ℕ) {b c : ℂ} (hb : 0 < b.re) (hc : 0 ≤ c.re) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ a : ℂ, 1 ≤ a.re → a.re ≤ 2 →
      ‖(selbergRHS N a b c)⁻¹‖ ≤ C * (1 + |a.im|) ^ K := by
  have hp : ∀ j : Fin N, 0 < (b + ((N + j - 1 : ℕ) : ℂ) * c).re :=
    fun j => re_pos_add_nat_mul hb hc _
  have h1 : ∀ j : Fin N, ∃ C : ℝ, ∃ K : ℕ, 0 ≤ C ∧ ∀ d : ℂ,
      1 + (b + ((N + j - 1 : ℕ) : ℂ) * c).re ≤ (d + (b + ((N + j - 1 : ℕ) : ℂ) * c)).re →
      (d + (b + ((N + j - 1 : ℕ) : ℂ) * c)).re ≤ 2 + (b + ((N + j - 1 : ℕ) : ℂ) * c).re →
      ‖Gamma (d + (b + ((N + j - 1 : ℕ) : ℂ) * c))‖ ≤
        C * (1 + |d.im|) ^ K * Real.exp (-(π * |d.im|) / 2) :=
    fun j => DLMF.Hypergeometric.CarlsonAux.exists_norm_Gamma_add_le_strip _ (by linarith [hp j])
  have h2 : ∀ j : Fin N, ∃ C : ℝ, ∃ K : ℕ, 0 ≤ C ∧ ∀ d : ℂ,
      |(d + ((j : ℕ) : ℂ) * c).re| ≤ 2 + |(((j : ℕ) : ℂ) * c).re| →
      ‖(Gamma (d + ((j : ℕ) : ℂ) * c))⁻¹‖ ≤ C * (1 + |d.im|) ^ K * Real.exp (π * |d.im| / 2) :=
    fun j => DLMF.Hypergeometric.CarlsonAux.exists_norm_recip_Gamma_add_le_strip _ _
  choose C1 K1 hC1 hb1 using h1
  choose C2 K2 hC2 hb2 using h2
  set D : Fin N → ℝ := fun j => C1 j * C2 j * ‖Gamma (1 + c)‖ * ‖(Gamma (b + (j : ℕ) * c))⁻¹‖ *
    ‖(Gamma (1 + ((j : ℕ) + 1) * c))⁻¹‖ with hD
  refine ⟨∏ j, D j, ∑ j, (K1 j + K2 j), fun a ha1 ha2 => ?_⟩
  unfold selbergRHS
  rw [← Finset.prod_inv_distrib, norm_prod, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
  have hX : 1 ≤ 1 + |a.im| := by linarith [abs_nonneg a.im]
  have e1 := hb1 j a (by simp only [Complex.add_re]; linarith)
    (by simp only [Complex.add_re]; linarith)
  have e2 := hb2 j a (by
    rw [Complex.add_re]
    have := abs_add_le a.re ((((j : ℕ) : ℂ) * c).re)
    rw [abs_of_pos (by linarith : (0 : ℝ) < a.re)] at this
    linarith)
  have hab : a + b + ((N + j - 1 : ℕ) : ℂ) * c = a + (b + ((N + j - 1 : ℕ) : ℂ) * c) := by ring
  rw [inv_div, hab, norm_div, norm_mul, norm_mul, norm_mul, div_eq_mul_inv, mul_inv, mul_inv,
    ← norm_inv, ← norm_inv, ← norm_inv]
  have hexp : Real.exp (-(π * |a.im|) / 2) * Real.exp (π * |a.im| / 2) = 1 := by
    rw [← Real.exp_add, show -(π * |a.im|) / 2 + π * |a.im| / 2 = 0 by ring, Real.exp_zero]
  calc ‖Gamma (a + (b + ((N + j - 1 : ℕ) : ℂ) * c))‖ * ‖Gamma (1 + c)‖ *
        (‖(Gamma (a + (j : ℕ) * c))⁻¹‖ * ‖(Gamma (b + (j : ℕ) * c))⁻¹‖ *
          ‖(Gamma (1 + ((j : ℕ) + 1) * c))⁻¹‖)
      ≤ (C1 j * (1 + |a.im|) ^ K1 j * Real.exp (-(π * |a.im|) / 2)) * ‖Gamma (1 + c)‖ *
        ((C2 j * (1 + |a.im|) ^ K2 j * Real.exp (π * |a.im| / 2)) *
          ‖(Gamma (b + (j : ℕ) * c))⁻¹‖ * ‖(Gamma (1 + ((j : ℕ) + 1) * c))⁻¹‖) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right e1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e2 (norm_nonneg _))
            (norm_nonneg _)) (by positivity) ?_
        exact mul_nonneg (mul_nonneg (mul_nonneg (hC1 j) (by positivity)) (by positivity))
          (norm_nonneg _)
    _ = D j * (1 + |a.im|) ^ (K1 j + K2 j) *
          (Real.exp (-(π * |a.im|) / 2) * Real.exp (π * |a.im| / 2)) := by
        simp only [hD]; ring
    _ = D j * (1 + |a.im|) ^ (K1 j + K2 j) := by rw [hexp, mul_one]

/-- The Selberg integral is bounded on `Re a ≥ 1`. -/
lemma norm_selbergInt_le {N : ℕ} {a b c : ℂ} (ha : 1 ≤ a.re) (hb : 0 < b.re) (hc : 0 ≤ c.re) :
    ‖selbergInt N a b c‖ ≤ ∫ t in cube N, ‖∏ i, weight 1 b (t i)‖ := by
  unfold selbergInt
  refine norm_integral_le_of_norm_le
    (integrableOn_prod_cube (integrableOn_weight (by simp) hb)).norm ?_
  filter_upwards [ae_restrict_mem (measurableSet_cube N),
    (ae_restrict_iff' (measurableSet_cube N)).2 (ae_cube_coords_Ioo N)] with t ht ht'
  refine (norm_selbergIntegrand_le hc ht).trans ?_
  rw [norm_prod, norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ =>
    norm_weight_le_one_left ha (ht' i)

/-- `S/R` is `1`-periodic in `a`. -/
lemma selbergRatio_add_one {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 1 / 2 ≤ c.re) :
    selbergInt N (a + 1) b c / selbergRHS N (a + 1) b c =
      selbergInt N a b c / selbergRHS N a b c := by
  have hc0 : (0 : ℝ) ≤ c.re := by linarith
  rw [selbergInt_add_one ha hb hc, selbergRHS_add_one ha hb hc0]
  have hP : ∏ j ∈ Finset.range N, aomotoFactor N a b c j ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => aomotoFactor_ne_zero ha hb hc0 j
  rw [mul_div_mul_left _ _ hP]

/-- **Carlson's theorem in `a`**: `S/R` does not depend on `a`. -/
lemma selbergRatio_eq_one_left {N : ℕ} {b c : ℂ} (hb : 0 < b.re) (hc : 1 / 2 ≤ c.re)
    {a : ℂ} (ha : 0 < a.re) :
    selbergInt N a b c / selbergRHS N a b c = selbergInt N 1 b c / selbergRHS N 1 b c := by
  have hc0 : (0 : ℝ) ≤ c.re := by linarith
  set F : ℂ → ℂ := fun a => selbergInt N a b c / selbergRHS N a b c with hF
  have hFd : DifferentiableOn ℂ F {a | 0 < a.re} :=
    (differentiableOn_selbergInt_a N hb hc0).div (differentiableOn_selbergRHS_a N hb hc0)
      fun a ha => selbergRHS_ne_zero ha hb hc0
  set f : ℂ → ℂ := fun w => F (w + 1) - F 1 with hf
  obtain ⟨C, K, hC⟩ := exists_norm_recip_selbergRHS_le N hb hc0
  set B := ∫ t in cube N, ‖∏ i, weight 1 b (t i)‖ with hB
  have hB0 : 0 ≤ B := setIntegral_nonneg (measurableSet_cube N) fun _ _ => norm_nonneg _
  have hfz : ∀ w : ℂ, 0 ≤ w.re → f w = 0 := by
    refine DLMF.Hypergeometric.CarlsonAux.eq_zero_of_periodic_of_bound (δ := 1 / 2)
      (by norm_num) ?_ ?_ (C := B * max C 0 + ‖F 1‖) (σ := 0) (K := K) Real.pi_pos ?_ ?_
    · intro w hw
      refine DifferentiableWithinAt.sub ?_ (differentiableWithinAt_const _)
      have hw' : 0 < (w + 1).re := by simp at hw ⊢; linarith
      exact ((hFd (w + 1) hw').differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw')).comp w
        (differentiableAt_id.add_const 1) |>.differentiableWithinAt
    · intro w hw
      simp only [hf, hF]
      have hw' : 0 < (w + 1).re := by simp; linarith
      rw [selbergRatio_add_one hw' hb hc]
    · intro w hw0 hw1
      have h1 : 1 ≤ (w + 1).re := by simp; linarith
      have h2 : (w + 1).re ≤ 2 := by simp; linarith
      have hS := norm_selbergInt_le (N := N) (c := c) h1 hb hc0
      have hR := hC (w + 1) h1 h2
      have hR' : ‖(selbergRHS N (w + 1) b c)⁻¹‖ ≤ max C 0 * (1 + |w.im|) ^ K := by
        refine hR.trans ?_
        simp only [Complex.add_im, Complex.one_im, add_zero]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      have hX : 1 ≤ (1 + |w.im|) ^ K := one_le_pow₀ (by linarith [abs_nonneg w.im])
      simp only [hf, hF, zero_mul, Real.exp_zero, mul_one]
      calc ‖selbergInt N (w + 1) b c / selbergRHS N (w + 1) b c -
            selbergInt N 1 b c / selbergRHS N 1 b c‖
          ≤ ‖selbergInt N (w + 1) b c‖ * ‖(selbergRHS N (w + 1) b c)⁻¹‖ +
              ‖selbergInt N 1 b c / selbergRHS N 1 b c‖ := by
            rw [div_eq_mul_inv, ← norm_mul]; exact norm_sub_le _ _
        _ ≤ B * (max C 0 * (1 + |w.im|) ^ K) +
              ‖selbergInt N 1 b c / selbergRHS N 1 b c‖ * (1 + |w.im|) ^ K := by
            gcongr
            · exact le_mul_of_one_le_right (norm_nonneg _) hX
        _ = (B * max C 0 + ‖selbergInt N 1 b c / selbergRHS N 1 b c‖) * (1 + |w.im|) ^ K := by
            ring
    · simp [hf]
  by_cases h1 : 1 ≤ a.re
  · have := hfz (a - 1) (by simp; linarith)
    simp only [hf, sub_add_cancel, sub_eq_zero] at this
    exact this
  · have := hfz a ha.le
    simp only [hf, hF, sub_eq_zero] at this
    rw [← this]
    exact (selbergRatio_add_one ha hb hc).symm

lemma selbergRatio_eq_one_one {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 1 / 2 ≤ c.re) :
    selbergInt N a b c / selbergRHS N a b c = selbergInt N 1 1 c / selbergRHS N 1 1 c := by
  have h1 : (0 : ℝ) < (1 : ℂ).re := by simp
  rw [selbergRatio_eq_one_left hb hc ha, selbergInt_comm, selbergRHS_comm,
    selbergRatio_eq_one_left h1 hc hb]

lemma selbergInt_zero (a b c : ℂ) : selbergInt 0 a b c = 1 := by
  have hcube : cube 0 = Set.univ := Set.eq_univ_of_forall fun t => fun i => i.elim0
  rw [selbergInt, hcube, Measure.restrict_univ]
  simp only [selbergIntegrand, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
    integral_const]
  rw [Measure.real, volume_pi, Measure.pi_univ]
  simp

lemma selbergRHS_zero (a b c : ℂ) : selbergRHS 0 a b c = 1 := by
  simp [selbergRHS]

lemma selbergRatio_one_one_eq_one {c : ℂ} (hc : 1 / 2 ≤ c.re) :
    ∀ N : ℕ, selbergInt N 1 1 c / selbergRHS N 1 1 c = 1 := by
  have h1 : (0 : ℝ) < (1 : ℂ).re := by simp
  have hc0 : (0 : ℝ) ≤ c.re := by linarith
  intro N
  induction N with
  | zero => simp [selbergInt_zero, selbergRHS_zero]
  | succ n ih =>
    have hb2 : 0 < (1 + 2 * c).re := by simp; linarith
    have hS := selbergInt_succ_one (n := n) h1 hc
    have hR := selbergRHS_succ_one (n := n) h1 hc0
    have hK := selbergRatio_eq_one_one (N := n) h1 hb2 hc
    rw [ih] at hK
    have hRn : selbergRHS n 1 (1 + 2 * c) c ≠ 0 := selbergRHS_ne_zero h1 hb2 hc0
    rw [div_eq_one_iff_eq hRn] at hK
    have hR1 : selbergRHS (n + 1) 1 1 c ≠ 0 := selbergRHS_ne_zero h1 h1 hc0
    have hnc : (1 : ℂ) + n * c ≠ 0 := fun h => by
      have := re_pos_add_nat_mul h1 hc0 n; rw [h] at this; simp at this
    rw [div_eq_one_iff_eq hR1]
    apply mul_left_cancel₀ hnc
    rw [hS, hR, hK]

/-- **Selberg's integral** for `Re a, Re b > 0` and `Re c ≥ 1/2`. -/
theorem selbergInt_eq_of_half_le {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 1 / 2 ≤ c.re) : selbergInt N a b c = selbergRHS N a b c := by
  have h := selbergRatio_eq_one_one (N := N) ha hb hc
  rw [selbergRatio_one_one_eq_one hc N,
    div_eq_one_iff_eq (selbergRHS_ne_zero ha hb (by linarith))] at h
  exact h

/-! ### Extension to `Re c > 0` -/

lemma ae_coords_ne (N : ℕ) : ∀ᵐ t : Fin N → ℝ, ∀ i j, i ≠ j → t i ≠ t j := by
  refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
  by_cases hij : i = j
  · exact Eventually.of_forall fun _ h => absurd hij h
  · filter_upwards [ae_ne_coord hij] with t ht _ using ht

lemma differentiableAt_selbergIntegrand_c {N : ℕ} (a b : ℂ) {t : Fin N → ℝ}
    (ht : ∀ i j, i ≠ j → t i ≠ t j) (c : ℂ) :
    DifferentiableAt ℂ (fun c => selbergIntegrand N a b c t) c := by
  unfold selbergIntegrand
  refine (differentiableAt_const _).mul (DifferentiableAt.fun_finsetProd fun i _ =>
    DifferentiableAt.fun_finsetProd fun j _ => ?_)
  split_ifs with hij
  · have hne : ((|t i - t j| : ℝ) : ℂ) ≠ 0 := by
      have : t i - t j ≠ 0 := sub_ne_zero.mpr (ht i j (Fin.ne_of_lt hij))
      exact_mod_cast abs_ne_zero.mpr this
    exact (differentiableAt_id.const_mul 2).const_cpow (Or.inl hne)
  · exact differentiableAt_const _

lemma differentiableOn_selbergInt_c (N : ℕ) {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    DifferentiableOn ℂ (fun c => selbergInt N a b c) {c | 0 < c.re} := by
  unfold selbergInt
  refine differentiableOn_integral_of_dominated (isOpen_lt continuous_const Complex.continuous_re)
    (fun c _ => (measurable_selbergIntegrand N a b c).aestronglyMeasurable) ?_ ?_
  · filter_upwards [ae_restrict_of_ae (ae_coords_ne N)] with t ht
    exact fun c _ => (differentiableAt_selbergIntegrand_c a b ht c).differentiableWithinAt
  · intro c₀ hc₀
    have hc₀' : 0 < c₀.re := hc₀
    refine ⟨c₀.re / 2, by positivity, fun z hz => ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      have := Complex.abs_re_le_norm (z - c₀)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have h2 : |(z - c₀).re| ≤ c₀.re / 2 := this.trans hz
      rw [Complex.sub_re, abs_le] at h2
      linarith
    refine ⟨fun t => ‖∏ i, weight a b (t i)‖,
      (integrableOn_prod_cube (n := N) (integrableOn_weight ha hb)).norm, ?_⟩
    filter_upwards [ae_restrict_mem (measurableSet_cube N)] with t ht z hz
    refine norm_selbergIntegrand_le ?_ ht
    have := Complex.abs_re_le_norm (z - c₀)
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have h2 : |(z - c₀).re| ≤ c₀.re / 2 := this.trans hz
    rw [Complex.sub_re, abs_le] at h2
    linarith

/-- The domain of convergence in `c` for fixed `a`, `b`. -/
def cDomain (N : ℕ) (a b : ℂ) : Set ℂ :=
  {c | 0 < 1 + N * c.re ∧ 0 < a.re + ((N - 1 : ℕ) : ℝ) * c.re ∧
    0 < b.re + ((N - 1 : ℕ) : ℝ) * c.re}

lemma isOpen_cDomain (N : ℕ) (a b : ℂ) : IsOpen (cDomain N a b) := by
  have h1 : Continuous fun c : ℂ => 1 + (N : ℝ) * c.re := by fun_prop
  have h2 : Continuous fun c : ℂ => a.re + ((N - 1 : ℕ) : ℝ) * c.re := by fun_prop
  have h3 : Continuous fun c : ℂ => b.re + ((N - 1 : ℕ) : ℝ) * c.re := by fun_prop
  have := ((isOpen_lt (continuous_const (y := (0 : ℝ))) h1).inter
    (isOpen_lt (continuous_const (y := (0 : ℝ))) h2)).inter
    (isOpen_lt (continuous_const (y := (0 : ℝ))) h3)
  convert this using 1
  ext c
  simp [cDomain, and_assoc]

lemma convex_cDomain (N : ℕ) (a b : ℂ) : Convex ℝ (cDomain N a b) := by
  unfold cDomain
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.smul_re, smul_eq_mul] at hx hy ⊢
  have key : ∀ {u v : ℝ}, 0 < u → 0 < v → 0 < s * u + t * v := fun hu hv => by
    rcases eq_or_lt_of_le hs with rfl | hs'
    · have : t = 1 := by linarith
      subst this; simpa using hv
    · exact add_pos_of_pos_of_nonneg (mul_pos hs' hu) (mul_nonneg ht hv.le)
  refine ⟨?_, ?_, ?_⟩
  · have e : 1 + N * (s * x.re + t * y.re) = s * (1 + N * x.re) + t * (1 + N * y.re) := by
      linear_combination (-1 : ℝ) * hst
    rw [e]; exact key hx.1 hy.1
  · have e : a.re + ((N - 1 : ℕ) : ℝ) * (s * x.re + t * y.re) =
        s * (a.re + ((N - 1 : ℕ) : ℝ) * x.re) + t * (a.re + ((N - 1 : ℕ) : ℝ) * y.re) := by
      linear_combination (-a.re) * hst
    rw [e]; exact key hx.2.1 hy.2.1
  · have e : b.re + ((N - 1 : ℕ) : ℝ) * (s * x.re + t * y.re) =
        s * (b.re + ((N - 1 : ℕ) : ℝ) * x.re) + t * (b.re + ((N - 1 : ℕ) : ℝ) * y.re) := by
      linear_combination (-b.re) * hst
    rw [e]; exact key hx.2.2 hy.2.2

lemma re_pos_of_mem_cDomain {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hc : c ∈ cDomain N a b)
    {j : ℕ} (hj : j ≤ N - 1) : 0 < (a + (j : ℂ) * c).re := by
  obtain ⟨_, h2, _⟩ := hc
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
    sub_zero]
  have hj' : (j : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hj
  rcases le_or_gt 0 c.re with h | h
  · nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  · nlinarith

lemma re_one_add_pos_of_mem_cDomain {N : ℕ} {a b c : ℂ} (hc : c ∈ cDomain N a b)
    {j : ℕ} (hj : j ≤ N) : 0 < (1 + (j : ℂ) * c).re := by
  obtain ⟨h1, _, _⟩ := hc
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero]
  have hj' : (j : ℝ) ≤ N := by exact_mod_cast hj
  rcases le_or_gt 0 c.re with h | h
  · nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  · nlinarith

lemma pos_mem_cDomain (N : ℕ) {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) :
    c ∈ cDomain N a b := by
  refine ⟨by positivity, by positivity, by positivity⟩

lemma differentiableOn_selbergRHS_c {N : ℕ} {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hN : 0 < N) : DifferentiableOn ℂ (fun c => selbergRHS N a b c) (cDomain N a b) := by
  intro c hc
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold selbergRHS
  refine DifferentiableAt.fun_finsetProd fun j _ => ?_
  have hj : (j : ℕ) ≤ N - 1 := by omega
  have hc1 : 0 < (1 + c).re := by
    have := re_one_add_pos_of_mem_cDomain hc (j := 1) (by omega); simpa using this
  refine DifferentiableAt.mul ?_ ?_
  · refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_
    · exact (Complex.differentiableAt_Gamma _
        (ne_neg_nat_of_re_pos (re_pos_of_mem_cDomain ha hc hj))).comp c
        (by fun_prop : DifferentiableAt ℂ (fun x : ℂ => a + ((j : ℕ) : ℂ) * x) c)
    · have hc' : c ∈ cDomain N b a := ⟨hc.1, hc.2.2, hc.2.1⟩
      exact (Complex.differentiableAt_Gamma _
        (ne_neg_nat_of_re_pos (re_pos_of_mem_cDomain hb hc' hj))).comp c
        (by fun_prop : DifferentiableAt ℂ (fun x : ℂ => b + ((j : ℕ) : ℂ) * x) c)
    · have := re_one_add_pos_of_mem_cDomain hc (j := (j : ℕ) + 1) (by omega)
      exact (Complex.differentiableAt_Gamma _
        (ne_neg_nat_of_re_pos (by simpa using this))).comp c
        (by fun_prop : DifferentiableAt ℂ (fun x : ℂ => 1 + (((j : ℕ) : ℂ) + 1) * x) c)
  · have hG : Gamma (1 + c) ≠ 0 := Gamma_ne_zero_of_re_pos' hc1
    have h1 : DifferentiableAt ℂ (fun x : ℂ => (Gamma (a + b + ((N + j - 1 : ℕ) : ℂ) * x))⁻¹) c :=
      (Complex.differentiable_one_div_Gamma.differentiableAt.comp c
        (by fun_prop : DifferentiableAt ℂ (fun x : ℂ => a + b + ((N + j - 1 : ℕ) : ℂ) * x) c)
        ).congr_of_eventuallyEq (Eventually.of_forall fun x => by simp)
    have h2 : DifferentiableAt ℂ (fun x : ℂ => (Gamma (1 + x))⁻¹) c :=
      (Complex.differentiable_one_div_Gamma.differentiableAt.comp c
        (by fun_prop : DifferentiableAt ℂ (fun x : ℂ => 1 + x) c)
        ).congr_of_eventuallyEq (Eventually.of_forall fun x => by simp)
    have := h1.mul h2
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, mul_inv]

/-- **Selberg's integral** for `Re a, Re b, Re c > 0`. -/
theorem selbergInt_eq_of_re_pos {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) : selbergInt N a b c = selbergRHS N a b c := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [selbergInt_zero, selbergRHS_zero]
  have hV : IsOpen {c : ℂ | 0 < c.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf := (differentiableOn_selbergInt_c N ha hb).analyticOnNhd hV
  have hg := ((differentiableOn_selbergRHS_c ha hb hN).mono
    fun c hc => pos_mem_cDomain N ha hb hc).analyticOnNhd hV
  have hconv : Convex ℝ {c : ℂ | 0 < c.re} := convex_halfSpace_re_gt 0
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg hconv.isPreconnected
    (z₀ := 1) (by simp) ?_ hc
  have hW : IsOpen {c : ℂ | 1 / 2 < c.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hW.mem_nhds (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re)] with c hc'
  exact selbergInt_eq_of_half_le ha hb (le_of_lt hc')

/-! ### A Landau-type continuation theorem -/

/-- Uniqueness of real power-series coefficients from one-sided vanishing. -/
lemma eq_zero_of_hasSum_pow_eq_zero {e : ℕ → ℝ} {ε r : ℝ} (hr : 0 < r) (hrε : r < ε)
    (hs : Summable fun k => |e k| * r ^ k)
    (h : ∀ w : ℝ, 0 < w → w < ε → HasSum (fun k => e k * w ^ k) 0) : ∀ k, e k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  -- the shifted series vanishes
  have hshift : ∀ w : ℝ, 0 < w → w < ε → HasSum (fun j => e (j + k) * w ^ j) 0 := by
    intro w hw hwε
    have h1 := h w hw hwε
    have h2 : ∑ i ∈ Finset.range k, e i * w ^ i = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [ih i (Finset.mem_range.mp hi), zero_mul]
    rw [← hasSum_nat_add_iff' k, h2, sub_zero] at h1
    have h3 := h1.mul_left (w ^ k)⁻¹
    rw [mul_zero] at h3
    refine h3.congr_fun fun j => ?_
    rw [pow_add]
    field_simp
  have hsum' : Summable fun j => |e (j + k)| * r ^ j := by
    have := (summable_nat_add_iff k).mpr hs
    refine (this.mul_left (r ^ k)⁻¹).congr fun j => ?_
    rw [pow_add]
    field_simp
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun w j => e (j + k) * w ^ j) (g := fun j => if j = 0 then e k else 0) hsum'
    (fun j => by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp
      · simp only [Nat.pos_iff_ne_zero.mp hj, ↓reduceIte]
        have : Tendsto (fun w : ℝ => w ^ j) (𝓝[>] 0) (𝓝 0) := by
          have := ((continuous_pow j).tendsto (0 : ℝ)).mono_left
            (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
          simpa [zero_pow (Nat.pos_iff_ne_zero.mp hj)] using this
        simpa using this.const_mul (e (j + k)))
    (by
      filter_upwards [Ioo_mem_nhdsGT hr] with w hw j
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hw.1]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw.1.le hw.2.le j) (abs_nonneg _))
  rw [tsum_ite_eq] at hlim
  have hzero : (∑' j, (fun w j => e (j + k) * w ^ j) · j) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhdsGT (hr.trans hrε)] with w hw
    exact (hshift w hw.1 hw.2).tsum_eq
  exact tendsto_nhds_unique (hlim.congr' hzero) tendsto_const_nhds

/-- Absolute convergence of a Taylor series strictly inside the disc of holomorphy. -/
lemma summable_norm_taylor {R : ℂ → ℂ} {z₀ : ℂ} {ρ : ℝ}
    (hR : DifferentiableOn ℂ R (Metric.ball z₀ ρ)) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < ρ) :
    Summable fun k : ℕ => ‖(k.factorial : ℂ)⁻¹ * iteratedDeriv k R z₀‖ * r ^ k := by
  set r' := (r + ρ) / 2 with hr'
  have hr'0 : 0 < r' := by rw [hr']; linarith
  have hrr' : r < r' := by rw [hr']; linarith
  have hmem : z₀ + (r' : ℂ) ∈ Metric.ball z₀ ρ := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr'0, hr']
    linarith
  have hT := Complex.hasSum_taylorSeries_on_ball hR hmem
  have hT0 := hT.summable.tendsto_atTop_zero
  obtain ⟨B, hB⟩ := (hT0.norm).bddAbove_range
  have hterm : ∀ k : ℕ, ‖(k.factorial : ℂ)⁻¹ * iteratedDeriv k R z₀‖ * r' ^ k ≤ B := by
    intro k
    have := hB ⟨k, rfl⟩
    simp only [add_sub_cancel_left, smul_eq_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr'0] at this
    calc ‖(k.factorial : ℂ)⁻¹ * iteratedDeriv k R z₀‖ * r' ^ k
        = ‖(k.factorial : ℂ)⁻¹‖ * (r' ^ k * ‖iteratedDeriv k R z₀‖) := by rw [norm_mul]; ring
      _ ≤ B := this
  have hq : 0 ≤ r / r' := div_nonneg hr0 hr'0.le
  have hq1 : r / r' < 1 := (div_lt_one hr'0).mpr hrr'
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_geometric_of_lt_one hq hq1).mul_left B)
  calc ‖(k.factorial : ℂ)⁻¹ * iteratedDeriv k R z₀‖ * r ^ k
      = ‖(k.factorial : ℂ)⁻¹ * iteratedDeriv k R z₀‖ * r' ^ k * (r / r') ^ k := by
        rw [mul_assoc, ← mul_pow]
        congr 2
        field_simp
    _ ≤ B * (r / r') ^ k := by gcongr; exact hterm k

lemma hasSum_mul_rpow_sub {y : ℝ} (hy : 0 < y) (W σ₁ v : ℝ) :
    HasSum (fun k : ℕ => v ^ k / k.factorial * (W * (-Real.log y) ^ k * y ^ σ₁))
      (W * y ^ (σ₁ - v)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (v * -Real.log y)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (W * y ^ σ₁)
  have hval : W * y ^ σ₁ * Real.exp (v * -Real.log y) = W * y ^ (σ₁ - v) := by
    rw [Real.rpow_sub hy, Real.rpow_def_of_pos hy v, div_eq_mul_inv, ← Real.exp_neg]
    ring_nf
  rw [hval] at h2
  refine h2.congr_fun fun k => ?_
  rw [mul_pow]
  ring

/-- **Landau's theorem** in the form needed here: if `σ ↦ ∫ W Y^σ` (with `0 < Y ≤ 1`) agrees
for `0 < σ ≤ σ₁` with a function holomorphic on the disc of radius `ρ > σ₁` about `σ₁`, then
`W Y^σ` is integrable for all `σ > σ₁ - ρ`. -/
theorem integrable_mul_rpow_of_analytic {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W Y : α → ℝ} (hW : Integrable W μ) (hW0 : ∀ᵐ x ∂μ, 0 ≤ W x) (hYm : AEMeasurable Y μ)
    (hY : ∀ᵐ x ∂μ, 0 < Y x ∧ Y x ≤ 1) {R : ℂ → ℂ} {σ₁ ρ : ℝ} (hσ₁ : 0 < σ₁)
    (hR : DifferentiableOn ℂ R (Metric.ball (σ₁ : ℂ) ρ))
    (heq : ∀ σ : ℝ, 0 < σ → σ ≤ σ₁ → ((∫ x, W x * Y x ^ σ ∂μ : ℝ) : ℂ) = R σ)
    {σ : ℝ} (hσ : σ₁ - ρ < σ) : Integrable (fun x => W x * Y x ^ σ) μ := by
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable (fun x => W x * Y x ^ s) μ := fun s =>
    hW.aestronglyMeasurable.mul (hYm.pow_const s).aestronglyMeasurable
  have hnn : ∀ s : ℝ, ∀ᵐ x ∂μ, 0 ≤ W x * Y x ^ s := fun s => by
    filter_upwards [hW0, hY] with x hx hy
    exact mul_nonneg hx (Real.rpow_nonneg hy.1.le s)
  -- nonnegative exponents
  have hpos : ∀ s : ℝ, 0 ≤ s → Integrable (fun x => W x * Y x ^ s) μ := by
    intro s hs
    refine hW.mono' (hmeas s) ?_
    filter_upwards [hW0, hY] with x hx hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx (Real.rpow_nonneg hy.1.le s))]
    exact mul_le_of_le_one_right hx (Real.rpow_le_one hy.1.le hy.2 hs)
  rcases le_or_gt 0 σ with hσ0 | hσ0
  · exact hpos σ hσ0
  -- the moments
  set X : α → ℝ := fun x => -Real.log (Y x) with hX
  set M : ℕ → ENNReal := fun k => ∫⁻ x, ENNReal.ofReal (W x * X x ^ k * Y x ^ σ₁) ∂μ with hM
  have hXm : AEMeasurable X μ := (Real.measurable_log.comp_aemeasurable hYm).neg
  have hfin_meas : ∀ k : ℕ, AEMeasurable (fun x => ENNReal.ofReal (W x * X x ^ k * Y x ^ σ₁)) μ :=
    fun k => ENNReal.measurable_ofReal.comp_aemeasurable
      ((hW.aemeasurable.mul (hXm.pow_const k)).mul (hYm.pow_const σ₁))
  have hX0 : ∀ᵐ x ∂μ, 0 ≤ X x := by
    filter_upwards [hY] with x hy
    exact neg_nonneg.mpr (Real.log_nonpos hy.1.le hy.2)
  have hterm_nn : ∀ k : ℕ, ∀ᵐ x ∂μ, 0 ≤ W x * X x ^ k * Y x ^ σ₁ := fun k => by
    filter_upwards [hW0, hX0, hY] with x hw hx hy
    exact mul_nonneg (mul_nonneg hw (pow_nonneg hx k)) (Real.rpow_nonneg hy.1.le _)
  -- the lintegral identity
  have hlin : ∀ v : ℝ, 0 ≤ v → ∫⁻ x, ENNReal.ofReal (W x * Y x ^ (σ₁ - v)) ∂μ =
      ∑' k, ENNReal.ofReal (v ^ k / k.factorial) * M k := by
    intro v hv
    have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (W x * Y x ^ (σ₁ - v)) =
        ∑' k, ENNReal.ofReal (v ^ k / k.factorial) *
          ENNReal.ofReal (W x * X x ^ k * Y x ^ σ₁) := by
      filter_upwards [hY, ae_all_iff.2 hterm_nn] with x hy hk
      have h := hasSum_mul_rpow_sub hy.1 (W x) σ₁ v
      rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (by positivity) (hk k))
        h.summable]
      exact tsum_congr fun k => ENNReal.ofReal_mul (by positivity)
    rw [lintegral_congr_ae hpt, lintegral_tsum fun k => (hfin_meas k).const_mul _]
    exact tsum_congr fun k => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- finiteness of the moments
  have hlt : ∀ v : ℝ, 0 ≤ v → v < σ₁ →
      ∫⁻ x, ENNReal.ofReal (W x * Y x ^ (σ₁ - v)) ∂μ ≠ ⊤ := by
    intro v _ hv
    have hI := hpos (σ₁ - v) (by linarith)
    rw [← ofReal_integral_eq_lintegral_ofReal hI (hnn _)]
    exact ENNReal.ofReal_ne_top
  have hMfin : ∀ k, M k ≠ ⊤ := by
    intro k
    have h1 := hlt (σ₁ / 2) (by positivity) (by linarith)
    rw [hlin _ (by positivity)] at h1
    have h2 := ENNReal.le_tsum (f := fun k => ENNReal.ofReal ((σ₁ / 2) ^ k / k.factorial) * M k) k
    have h3 : ENNReal.ofReal ((σ₁ / 2) ^ k / k.factorial) * M k ≠ ⊤ :=
      ne_top_of_le_ne_top h1 h2
    have hpos' : ENNReal.ofReal ((σ₁ / 2) ^ k / k.factorial) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; positivity
    intro hk
    exact h3 (ENNReal.mul_eq_top.mpr (Or.inl ⟨hpos', hk⟩))
  set m : ℕ → ℝ := fun k => (M k).toReal with hm
  have hMm : ∀ k, M k = ENNReal.ofReal (m k) := fun k => (ENNReal.ofReal_toReal (hMfin k)).symm
  have hm0 : ∀ k, 0 ≤ m k := fun k => ENNReal.toReal_nonneg
  have hterm : ∀ v : ℝ, 0 ≤ v → ∀ k : ℕ, ENNReal.ofReal (v ^ k / k.factorial) * M k =
      ENNReal.ofReal (v ^ k / k.factorial * m k) := fun v hv k => by
    rw [hMm, ← ENNReal.ofReal_mul (by positivity)]
  -- the real expansion for `0 ≤ v < σ₁`
  have hreal : ∀ v : ℝ, 0 ≤ v → v < σ₁ →
      HasSum (fun k => v ^ k / k.factorial * m k) (∫ x, W x * Y x ^ (σ₁ - v) ∂μ) := by
    intro v hv hvσ
    have h1 := hlin v hv
    have h2 := hlt v hv hvσ
    simp_rw [hterm v hv] at h1
    rw [h1] at h2
    have hnn' : ∀ k : ℕ, 0 ≤ v ^ k / k.factorial * m k := fun k =>
      mul_nonneg (by positivity) (hm0 k)
    have hs : Summable fun k => v ^ k / k.factorial * m k :=
      (ENNReal.summable_toReal h2).congr fun k => ENNReal.toReal_ofReal (hnn' k)
    rw [integral_eq_lintegral_of_nonneg_ae (hnn _) (hmeas _), h1,
      ENNReal.tsum_toReal_eq (fun k => ENNReal.ofReal_ne_top),
      tsum_congr fun k => ENNReal.toReal_ofReal (hnn' k)]
    exact hs.hasSum
  -- the Taylor expansion of `R`
  set d : ℕ → ℂ := fun k => (k.factorial : ℂ)⁻¹ * iteratedDeriv k R σ₁ with hd
  have htaylor : ∀ v : ℝ, |v| < ρ →
      HasSum (fun k => d k * ((-v) ^ k : ℝ)) (R ((σ₁ - v : ℝ) : ℂ)) := by
    intro v hv
    have hmem : ((σ₁ - v : ℝ) : ℂ) ∈ Metric.ball (σ₁ : ℂ) ρ := by
      rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, show σ₁ - v - σ₁ = -v by ring, abs_neg]
      exact hv
    refine (Complex.hasSum_taylorSeries_on_ball hR hmem).congr_fun fun k => ?_
    simp only [hd, smul_eq_mul, ← Complex.ofReal_sub, show σ₁ - v - σ₁ = -v by ring]
    push_cast
    try ring
  -- the coefficient identity
  set e : ℕ → ℝ := fun k => m k / k.factorial - (d k).re * (-1) ^ k with he_def
  have he : ∀ v : ℝ, 0 < v → v < σ₁ → HasSum (fun k => e k * v ^ k) 0 := by
    intro v hv hvσ
    have h1 := hreal v hv.le hvσ
    have h2 := htaylor v (by rw [abs_of_pos hv]; linarith)
    rw [← heq (σ₁ - v) (by linarith) (by linarith)] at h2
    have h4 := Complex.hasSum_re h2
    simp only [Complex.ofReal_re] at h4
    have := h1.sub h4
    rw [sub_self] at this
    refine this.congr_fun fun k => ?_
    simp only [he_def, Complex.re_mul_ofReal, neg_pow v k]
    field_simp
    try ring
  have hsum_e : Summable fun k => |e k| * (σ₁ / 2) ^ k := by
    have h1 := (hreal (σ₁ / 2) (by positivity) (by linarith)).summable
    have h2 := summable_norm_taylor hR (r := σ₁ / 2) (by positivity) (by linarith)
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (h1.add h2)
    simp only [he_def]
    calc |m k / k.factorial - (d k).re * (-1) ^ k| * (σ₁ / 2) ^ k
        ≤ (|m k / k.factorial| + |(d k).re * (-1) ^ k|) * (σ₁ / 2) ^ k := by
          gcongr; exact abs_sub _ _
      _ ≤ (σ₁ / 2) ^ k / k.factorial * m k + ‖d k‖ * (σ₁ / 2) ^ k := by
          rw [abs_of_nonneg (div_nonneg (hm0 k) (by positivity)), abs_mul, abs_pow, abs_neg,
            abs_one, one_pow, mul_one, add_mul,
            show m k / k.factorial * (σ₁ / 2) ^ k = (σ₁ / 2) ^ k / k.factorial * m k by ring]
          gcongr
          exact Complex.abs_re_le_norm _
  have he0 := eq_zero_of_hasSum_pow_eq_zero (ε := σ₁) (r := σ₁ / 2) (by positivity)
    (by linarith) hsum_e he
  have hmle : ∀ k : ℕ, m k / k.factorial ≤ ‖d k‖ := by
    intro k
    have h := he0 k
    simp only [he_def, sub_eq_zero] at h
    rw [h]
    calc (d k).re * (-1) ^ k ≤ |(d k).re * (-1) ^ k| := le_abs_self _
      _ = |(d k).re| := by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
      _ ≤ ‖d k‖ := Complex.abs_re_le_norm _
  -- the conclusion
  set w := σ₁ - σ with hw
  have hw0 : 0 ≤ w := by rw [hw]; linarith
  have hwρ : w < ρ := by rw [hw]; linarith
  have hsd := summable_norm_taylor hR hw0 hwρ
  have hfinal : ∫⁻ x, ENNReal.ofReal (W x * Y x ^ σ) ∂μ < ⊤ := by
    have h := hlin w hw0
    rw [show σ₁ - w = σ by rw [hw]; ring] at h
    rw [h]
    calc ∑' k, ENNReal.ofReal (w ^ k / k.factorial) * M k
        = ∑' k, ENNReal.ofReal (w ^ k / k.factorial * m k) := tsum_congr (hterm w hw0)
      _ ≤ ∑' k, ENNReal.ofReal (‖d k‖ * w ^ k) := by
          refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
          calc w ^ k / k.factorial * m k = m k / k.factorial * w ^ k := by ring
            _ ≤ ‖d k‖ * w ^ k := by gcongr; exact hmle k
      _ = ENNReal.ofReal (∑' k, ‖d k‖ * w ^ k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsd).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  exact ⟨hmeas σ, (hasFiniteIntegral_iff_ofReal (hnn σ)).2 hfinal⟩

/-! ### Real forms of the integrand -/

/-- `∏_{i<j} (tᵢ - tⱼ)²`. -/
def vdmSq (N : ℕ) (t : Fin N → ℝ) : ℝ :=
  ∏ i : Fin N, ∏ j : Fin N, if i.val < j.val then (t i - t j) ^ 2 else 1

/-- The real weight `∏ tᵢ^{α-1}(1-tᵢ)^{β-1}`. -/
def weightR (N : ℕ) (α β : ℝ) (t : Fin N → ℝ) : ℝ :=
  ∏ i : Fin N, t i ^ (α - 1) * (1 - t i) ^ (β - 1)

lemma measurable_vdmSq (N : ℕ) : Measurable (vdmSq N) := by
  unfold vdmSq; fun_prop

lemma measurable_weightR (N : ℕ) (α β : ℝ) : Measurable (weightR N α β) := by
  unfold weightR; fun_prop

lemma vdmSq_pos {N : ℕ} {t : Fin N → ℝ} (ht : ∀ i j, i ≠ j → t i ≠ t j) : 0 < vdmSq N t := by
  unfold vdmSq
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => ?_
  split_ifs with hij
  · have := sub_ne_zero.mpr (ht i j (Fin.ne_of_lt hij)); positivity
  · exact one_pos

lemma vdmSq_le_one {N : ℕ} {t : Fin N → ℝ} (ht : t ∈ cube N) : vdmSq N t ≤ 1 := by
  unfold vdmSq
  refine Finset.prod_le_one₀ (fun i _ => Finset.prod_nonneg fun j _ => by split_ifs <;> positivity)
    fun i _ => Finset.prod_le_one₀ (fun j _ => by split_ifs <;> positivity) fun j _ => ?_
  split_ifs
  · have hi := ht i (Set.mem_univ _)
    have hj := ht j (Set.mem_univ _)
    have : |t i - t j| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hi.1, hi.2, hj.1, hj.2]
    calc (t i - t j) ^ 2 = |t i - t j| ^ 2 := (sq_abs _).symm
      _ ≤ 1 := pow_le_one₀ (abs_nonneg _) this
  · exact le_rfl

lemma norm_vdm_eq {N : ℕ} (c : ℂ) {t : Fin N → ℝ} (ht : ∀ i j, i ≠ j → t i ≠ t j) :
    ‖vdm N c t‖ = vdmSq N t ^ c.re := by
  unfold vdm vdmSq
  rw [norm_prod, ← Real.finsetProd_rpow _ _ fun i _ => Finset.prod_nonneg fun j _ => by
    split_ifs <;> positivity]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_prod, ← Real.finsetProd_rpow _ _ fun j _ => by split_ifs <;> positivity]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs with hij
  · have hne : t i - t j ≠ 0 := sub_ne_zero.mpr (ht i j (Fin.ne_of_lt hij))
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hne), ← sq_abs, ← Real.rpow_natCast,
      ← Real.rpow_mul (abs_nonneg _)]
    simp
  · simp

lemma norm_prod_weight_eq {N : ℕ} (a b : ℂ) {t : Fin N → ℝ} (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1) :
    ‖∏ i, weight a b (t i)‖ = weightR N a.re b.re t := by
  unfold weightR
  rw [norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : 0 < 1 - t i := by linarith [(ht i).2]
  unfold weight
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ht i).1, one_sub_ofReal,
    Complex.norm_cpow_eq_rpow_re_of_pos h1]
  simp

lemma norm_selbergIntegrand_eq {N : ℕ} (a b c : ℂ) {t : Fin N → ℝ}
    (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1) (ht' : ∀ i j, i ≠ j → t i ≠ t j) :
    ‖selbergIntegrand N a b c t‖ = weightR N a.re b.re t * vdmSq N t ^ c.re := by
  rw [selbergIntegrand_eq, norm_mul, norm_prod_weight_eq a b ht, norm_vdm_eq c ht']

lemma weightR_nonneg {N : ℕ} (α β : ℝ) {t : Fin N → ℝ} (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1) :
    0 ≤ weightR N α β t :=
  Finset.prod_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (ht i).1.le _)
    (Real.rpow_nonneg (by linarith [(ht i).2]) _)

/-- For real parameters the integrand is the real nonnegative integrand. -/
lemma selbergIntegrand_ofReal {N : ℕ} (α β σ : ℝ) {t : Fin N → ℝ}
    (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1) (ht' : ∀ i j, i ≠ j → t i ≠ t j) :
    selbergIntegrand N α β σ t = ((weightR N α β t * vdmSq N t ^ σ : ℝ) : ℂ) := by
  have h := norm_selbergIntegrand_eq (α : ℂ) β σ ht ht'
  simp only [Complex.ofReal_re] at h
  rw [← h]
  -- the integrand is a nonnegative real number
  have hreal : selbergIntegrand N α β σ t =
      ((∏ i, t i ^ (α - 1) * (1 - t i) ^ (β - 1)) *
        ∏ i : Fin N, ∏ j : Fin N, if i.val < j.val then |t i - t j| ^ (2 * σ) else 1 : ℝ) := by
    unfold selbergIntegrand
    push_cast
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      have h1 : 0 ≤ 1 - t i := by linarith [(ht i).2]
      rw [Complex.ofReal_cpow (ht i).1.le, Complex.ofReal_cpow h1]
      push_cast; ring_nf
    · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
      split_ifs
      · rw [Complex.ofReal_cpow (abs_nonneg _)]; push_cast; ring_nf
      · rfl
  rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  refine mul_nonneg (Finset.prod_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (ht i).1.le _)
    (Real.rpow_nonneg (by linarith [(ht i).2]) _)) (Finset.prod_nonneg fun i _ =>
    Finset.prod_nonneg fun j _ => by split_ifs <;> positivity)

lemma integrableOn_weightR {N : ℕ} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IntegrableOn (weightR N α β) (cube N) := by
  have h := (integrableOn_prod_cube (n := N) (integrableOn_weight (a := (α : ℂ)) (b := (β : ℂ))
    (by simpa using hα) (by simpa using hβ))).norm
  refine Integrable.congr h ?_
  filter_upwards [(ae_restrict_iff' (measurableSet_cube N)).2 (ae_cube_coords_Ioo N)] with t ht
  rw [norm_prod_weight_eq _ _ ht]
  simp

lemma ae_cube_good (N : ℕ) : ∀ᵐ t ∂(volume.restrict (cube N)),
    (∀ i, t i ∈ Ioo (0 : ℝ) 1) ∧ (∀ i j, i ≠ j → t i ≠ t j) ∧ t ∈ cube N := by
  filter_upwards [(ae_restrict_iff' (measurableSet_cube N)).2 (ae_cube_coords_Ioo N),
    ae_restrict_of_ae (ae_coords_ne N), ae_restrict_mem (measurableSet_cube N)] with t h1 h2 h3
  exact ⟨h1, h2, h3⟩

lemma selbergInt_ofReal {N : ℕ} (α β σ : ℝ) :
    selbergInt N α β σ = ((∫ t in cube N, weightR N α β t * vdmSq N t ^ σ : ℝ) : ℂ) := by
  rw [selbergInt, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [ae_cube_good N] with t ht
  exact selbergIntegrand_ofReal α β σ ht.1 ht.2.1

/-- **Integrability of the Selberg integrand** on its full domain of convergence, by Landau's
theorem. -/
lemma integrableOn_weightR_mul_vdmSq_rpow {N : ℕ} {α β σ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hσ : (σ : ℂ) ∈ cDomain N α β) :
    IntegrableOn (fun t => weightR N α β t * vdmSq N t ^ σ) (cube N) := by
  have hW := integrableOn_weightR (N := N) hα hβ
  have hmeas : AEStronglyMeasurable (fun t => weightR N α β t * vdmSq N t ^ σ)
      (volume.restrict (cube N)) :=
    ((measurable_weightR N α β).mul ((measurable_vdmSq N).pow_const σ)).aestronglyMeasurable
  rcases le_or_gt 0 σ with h0 | h0
  · refine hW.mono' hmeas ?_
    filter_upwards [ae_cube_good N] with t ht
    have hW0 := weightR_nonneg α β ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hW0 (Real.rpow_nonneg
      (vdmSq_pos ht.2.1).le _))]
    exact mul_le_of_le_one_right hW0 (Real.rpow_le_one (vdmSq_pos ht.2.1).le
      (vdmSq_le_one ht.2.2) h0)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine hW.mono' hmeas (Eventually.of_forall fun t => ?_)
    simp [vdmSq, weightR]
  obtain ⟨h1, h2, h3⟩ := hσ
  simp only [Complex.ofReal_re] at h1 h2 h3
  set m := min (1 + N * σ) (min (α + ((N - 1 : ℕ) : ℝ) * σ) (β + ((N - 1 : ℕ) : ℝ) * σ))
    with hm
  have hm0 : 0 < m := lt_min h1 (lt_min h2 h3)
  have hmN : m / 2 ≥ N * (m / (2 * (N + 1))) := by
    rw [ge_iff_le, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  set s := σ - m / (2 * (N + 1)) with hs
  have hN1 : (((N - 1 : ℕ) : ℝ)) ≤ N := by exact_mod_cast Nat.sub_le N 1
  have hsdom : ∀ z : ℂ, s < z.re → z ∈ cDomain N α β := by
    intro z hz
    have hd : 0 ≤ m / (2 * (N + 1)) := by positivity
    refine ⟨?_, ?_, ?_⟩
    · have : 1 + N * σ - N * (m / (2 * (N + 1))) > 0 := by
        have h4 : m ≤ 1 + N * σ := by rw [hm]; exact min_le_left _ _
        linarith
      nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    · have : α + ((N - 1 : ℕ) : ℝ) * σ - ((N - 1 : ℕ) : ℝ) * (m / (2 * (N + 1))) > 0 := by
        have h4 : m ≤ α + ((N - 1 : ℕ) : ℝ) * σ := by
          rw [hm]; exact (min_le_right _ _).trans (min_le_left _ _)
        have : ((N - 1 : ℕ) : ℝ) * (m / (2 * (N + 1))) ≤ N * (m / (2 * (N + 1))) :=
          mul_le_mul_of_nonneg_right hN1 hd
        linarith
      simp only [Complex.ofReal_re]
      nlinarith [(Nat.cast_nonneg (N - 1) : (0 : ℝ) ≤ ((N - 1 : ℕ) : ℝ))]
    · have : β + ((N - 1 : ℕ) : ℝ) * σ - ((N - 1 : ℕ) : ℝ) * (m / (2 * (N + 1))) > 0 := by
        have h4 : m ≤ β + ((N - 1 : ℕ) : ℝ) * σ := by
          rw [hm]; exact (min_le_right _ _).trans (min_le_right _ _)
        have : ((N - 1 : ℕ) : ℝ) * (m / (2 * (N + 1))) ≤ N * (m / (2 * (N + 1))) :=
          mul_le_mul_of_nonneg_right hN1 hd
        linarith
      simp only [Complex.ofReal_re]
      nlinarith [(Nat.cast_nonneg (N - 1) : (0 : ℝ) ≤ ((N - 1 : ℕ) : ℝ))]
  have hs0 : s < 0 := by
    have : 0 < m / (2 * (N + 1)) := by positivity
    linarith
  have hball : Metric.ball ((1 : ℝ) : ℂ) (1 - s) ⊆ cDomain N α β := by
    intro z hz
    refine hsdom z ?_
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have := Complex.abs_re_le_norm (z - ((1 : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re, abs_le] at this
    linarith
  have hR := (differentiableOn_selbergRHS_c (a := α) (b := β) (by simpa using hα)
    (by simpa using hβ) hN).mono hball
  have hYm : AEMeasurable (vdmSq N) (volume.restrict (cube N)) :=
    (measurable_vdmSq N).aemeasurable
  have hsσ : s < σ := by
    have : 0 < m / (2 * (N + 1)) := by positivity
    linarith
  refine integrable_mul_rpow_of_analytic hW ?_ hYm ?_ one_pos hR ?_ (by linarith)
  · filter_upwards [ae_cube_good N] with t ht
    exact weightR_nonneg α β ht.1
  · filter_upwards [ae_cube_good N] with t ht
    exact ⟨vdmSq_pos ht.2.1, vdmSq_le_one ht.2.2⟩
  · intro σ' hσ' _
    rw [← selbergInt_ofReal, selbergInt_eq_of_re_pos (by simpa using hα) (by simpa using hβ)
      (by simpa using hσ')]

lemma mem_cDomain_re {N : ℕ} {a b c : ℂ} (hc : c ∈ cDomain N a b) :
    (c.re : ℂ) ∈ cDomain N (a.re : ℂ) (b.re : ℂ) := by
  obtain ⟨h1, h2, h3⟩ := hc
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩

lemma differentiableOn_selbergInt_cDomain (N : ℕ) {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    DifferentiableOn ℂ (fun c => selbergInt N a b c) (cDomain N a b) := by
  unfold selbergInt
  refine differentiableOn_integral_of_dominated (isOpen_cDomain N a b)
    (fun c _ => (measurable_selbergIntegrand N a b c).aestronglyMeasurable) ?_ ?_
  · filter_upwards [ae_restrict_of_ae (ae_coords_ne N)] with t ht
    exact fun c _ => (differentiableAt_selbergIntegrand_c a b ht c).differentiableWithinAt
  · intro c₀ hc₀
    obtain ⟨ε', hε', hball⟩ := Metric.isOpen_iff.mp (isOpen_cDomain N a b) c₀ hc₀
    set ε := ε' / 2 with hε
    have hε0 : 0 < ε := by positivity
    have hcl : Metric.closedBall c₀ ε ⊆ cDomain N a b :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    set σm := c₀.re - ε with hσm
    have hmem : (σm : ℂ) ∈ cDomain N (a.re : ℂ) (b.re : ℂ) := by
      have h := mem_cDomain_re (hcl (show c₀ - (ε : ℂ) ∈ Metric.closedBall c₀ ε by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]))
      simpa [hσm] using h
    refine ⟨ε, hε0, hcl, fun t => weightR N a.re b.re t * vdmSq N t ^ σm,
      integrableOn_weightR_mul_vdmSq_rpow ha hb hmem, ?_⟩
    filter_upwards [ae_cube_good N] with t ht z hz
    rw [norm_selbergIntegrand_eq a b z ht.1 ht.2.1]
    refine mul_le_mul_of_nonneg_left ?_ (weightR_nonneg _ _ ht.1)
    refine Real.rpow_le_rpow_of_exponent_ge (vdmSq_pos ht.2.1) (vdmSq_le_one ht.2.2) ?_
    have := Complex.abs_re_le_norm (z - c₀)
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have h2 : |(z - c₀).re| ≤ ε := this.trans hz
    rw [Complex.sub_re, abs_le] at h2
    linarith

/-- **Selberg's integral** on its full domain of convergence. -/
theorem selbergInt_eq {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : c ∈ cDomain N a b) : selbergInt N a b c = selbergRHS N a b c := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [selbergInt_zero, selbergRHS_zero]
  have hU := isOpen_cDomain N a b
  have hf := (differentiableOn_selbergInt_cDomain N ha hb).analyticOnNhd hU
  have hg := (differentiableOn_selbergRHS_c ha hb hN).analyticOnNhd hU
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_cDomain N a b).isPreconnected
    (z₀ := 1) (pos_mem_cDomain N ha hb (by simp)) ?_ hc
  have hV : IsOpen {c : ℂ | 0 < c.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hV.mem_nhds (by simp : (0 : ℝ) < (1 : ℂ).re)] with c hc'
  exact selbergInt_eq_of_re_pos ha hb hc'

/-! ### Aomoto's integral -/

lemma differentiableOn_integral_mul_selbergIntegrand_c (N : ℕ) {a b : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) {h : (Fin N → ℝ) → ℂ} (hh : Measurable h)
    (hh1 : ∀ t ∈ cube N, ‖h t‖ ≤ 1) :
    DifferentiableOn ℂ (fun c => ∫ t in cube N, h t * selbergIntegrand N a b c t)
      {c | 0 < c.re} := by
  refine differentiableOn_integral_of_dominated (isOpen_lt continuous_const Complex.continuous_re)
    (fun c _ => (hh.mul (measurable_selbergIntegrand N a b c)).aestronglyMeasurable) ?_ ?_
  · filter_upwards [ae_restrict_of_ae (ae_coords_ne N)] with t ht
    exact fun c _ => ((differentiableAt_selbergIntegrand_c a b ht c).const_mul (h t))
      |>.differentiableWithinAt
  · intro c₀ hc₀
    have hc₀' : 0 < c₀.re := hc₀
    refine ⟨c₀.re / 2, by positivity, fun z hz => ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      have := Complex.abs_re_le_norm (z - c₀)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have h2 : |(z - c₀).re| ≤ c₀.re / 2 := this.trans hz
      rw [Complex.sub_re, abs_le] at h2
      linarith
    refine ⟨fun t => ‖∏ i, weight a b (t i)‖,
      (integrableOn_prod_cube (n := N) (integrableOn_weight ha hb)).norm, ?_⟩
    filter_upwards [ae_restrict_mem (measurableSet_cube N)] with t ht z hz
    rw [norm_mul]
    have hz' : 0 ≤ z.re := by
      have := Complex.abs_re_le_norm (z - c₀)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have h2 : |(z - c₀).re| ≤ c₀.re / 2 := this.trans hz
      rw [Complex.sub_re, abs_le] at h2
      linarith
    calc ‖h t‖ * ‖selbergIntegrand N a b z t‖ ≤ 1 * ‖∏ i, weight a b (t i)‖ :=
          mul_le_mul (hh1 t ht) (norm_selbergIntegrand_le hz' ht) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

lemma differentiableAt_aomotoFactor {N : ℕ} {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (j : ℕ)
    {c : ℂ} (hc : 0 ≤ c.re) : DifferentiableAt ℂ (fun c => aomotoFactor N a b c j) c := by
  unfold aomotoFactor
  have hab : 0 < (a + b).re := by simp; linarith
  refine DifferentiableAt.div (by fun_prop) (by fun_prop) fun h => ?_
  have := re_pos_add_nat_mul hab hc (2 * N - 2 - j)
  rw [h] at this; simp at this

/-- Aomoto's formula for `Re c > 0`. -/
theorem aomotoInt_eq {N m : ℕ} {a b c : ℂ} (hm : m ≤ N) (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) :
    aomotoInt N a b c (iseg N m) =
      (∏ j ∈ Finset.range m, aomotoFactor N a b c j) * selbergInt N a b c := by
  have hV : IsOpen {c : ℂ | 0 < c.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (fun c => aomotoInt N a b c (iseg N m)) {c | 0 < c.re} :=
    (differentiableOn_integral_mul_selbergIntegrand_c N ha hb (measurable_mono _)
      (fun t ht => norm_mono_le _ ht)).analyticOnNhd hV
  have hg : AnalyticOnNhd ℂ (fun c => (∏ j ∈ Finset.range m, aomotoFactor N a b c j) *
      selbergInt N a b c) {c | 0 < c.re} := by
    refine DifferentiableOn.analyticOnNhd ?_ hV
    refine DifferentiableOn.mul ?_ (differentiableOn_selbergInt_c N ha hb)
    intro c hc'
    exact (DifferentiableAt.fun_finsetProd fun j _ =>
      differentiableAt_aomotoFactor ha hb j (le_of_lt hc')).differentiableWithinAt
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt 0).isPreconnected
    (z₀ := 1) (by simp) ?_ hc
  have hW : IsOpen {c : ℂ | 1 / 2 < c.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hW.mem_nhds (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re)] with c hc'
  exact aomoto_prod ha hb (le_of_lt hc') hm

/-- Selberg's integral, AAR Theorem 8.1.1. Indexed so that `j : Fin n` corresponds to
the factor with shift `j · c`. -/
@[dlmf 5.14.E4]
theorem selberg_integral {n : ℕ} {a b c : ℂ} (hn : 0 < n)
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < 1 + n * c.re)
    (hca : 0 < a.re + (n - 1 : ℕ) * c.re)
    (hcb : 0 < b.re + (n - 1 : ℕ) * c.re) :
    ∫ t : Fin n → ℝ in Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1,
        selbergIntegrand n a b c t =
      ∏ j : Fin n,
        Gamma (a + (j : ℕ) * c) * Gamma (b + (j : ℕ) * c) * Gamma (1 + ((j : ℕ) + 1) * c) /
          (Gamma (a + b + (n + j - 1 : ℕ) * c) * Gamma (1 + c)) :=
  selbergInt_eq ha hb ⟨hc, hca, hcb⟩

/-- The `n = 1` case is the Beta integral (independent of `c`). -/
@[dlmf 5.12.E1]
theorem selberg_integral_one {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) =
      Gamma a * Gamma b / Gamma (a + b) := by
  have hG : Gamma (a + b) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp [add_re]; linarith)
  change betaIntegral a b = _
  rw [eq_div_iff_mul_eq hG, mul_comm, Gamma_mul_Gamma_eq_betaIntegral ha hb]

/-- Aomoto's extension (AAR §8.1, §8.3): inserting `∏_{i=1}^m t_i`. -/
@[dlmf 5.14.E4]
theorem aomoto_integral {n m : ℕ} {a b c : ℂ} (hm : m ≤ n)
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) :
    ∫ t : Fin n → ℝ in Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1,
        selbergIntegrand n a b c t * ∏ i : Fin m, (t (Fin.castLE hm i) : ℂ) =
      (∏ j : Fin m, (a + (n - 1 - j : ℕ) * c) / (a + b + (2 * n - 2 - j : ℕ) * c)) *
        ∏ j : Fin n,
          Gamma (a + (j : ℕ) * c) * Gamma (b + (j : ℕ) * c) * Gamma (1 + ((j : ℕ) + 1) * c) /
            (Gamma (a + b + (n + j - 1 : ℕ) * c) * Gamma (1 + c)) := by
  have h := aomotoInt_eq hm ha hb hc
  rw [selbergInt_eq ha hb (pos_mem_cDomain n ha hb hc)] at h
  have hP : ∏ j : Fin m, (a + ((n - 1 - j : ℕ) : ℂ) * c) / (a + b + ((2 * n - 2 - j : ℕ) : ℂ) * c) =
      ∏ j ∈ Finset.range m, aomotoFactor n a b c j :=
    Fin.prod_univ_eq_prod_range (fun j => aomotoFactor n a b c j) m
  rw [hP]
  change _ = _ * selbergRHS n a b c
  rw [← h]
  refine setIntegral_congr_fun (measurableSet_cube n) fun t _ => ?_
  rw [mul_comm]
  congr 1
  unfold mono iseg
  have hset : (Finset.univ.filter fun i : Fin n => i.val < m) =
      Finset.univ.map (Fin.castLEEmb hm) := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, Fin.castLEEmb_apply]
    constructor
    · intro hi; exact ⟨⟨i, hi⟩, Fin.ext rfl⟩
    · rintro ⟨j, rfl⟩; simp
  rw [hset, Finset.prod_map]
  rfl


end DLMF.Selberg
