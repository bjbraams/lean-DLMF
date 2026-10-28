/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Multidimensional.SelbergLimits

/-!
# Dyson circular integrals

Dimension reduction, integer exponents and Carlson continuation establish the circular Dyson
integral.

Source references and common attribution are retained in
`DLMF.Gamma.Multidimensional`.
-/

@[expose] public section

open Complex MeasureTheory

open scoped Real

noncomputable section

namespace DLMF.Gamma

section DysonIntegral

/-! ### Dyson's integral

For a nonnegative integer exponent `b = k`, the integrand is the Laurent polynomial
`∏_{j ≠ l} (1 - z_j/z_l)^k` on the torus, whose constant term `(nk)!/(k!)^n` is Dyson's
conjecture; we follow Good's proof (AAR Theorem 8.8.1), with a recursion coming from Lagrange
interpolation and the removal of variables with zero exponent. The integral and
`Γ(1+nb)/Γ(1+b)^n` are both of exponential type in `Re b ≥ 0` (the latter by Gauss's
multiplication formula and the Beta integral) and bounded on vertical lines, so Carlson's
theorem gives the identity for `Re b ≥ 0`. Landau's theorem then gives integrability for
`Re b > -1/n`, and the identity theorem extends the formula there. -/

open Set Filter
open scoped Topology

/-- The box `[-π, π]ⁿ`. -/
abbrev circBox (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Icc (-π) π

/-- The box `[-π, π]ⁿ` is measurable. -/
theorem measurableSet_circBox (n : ℕ) : MeasurableSet (circBox n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- The box `[-π, π]ⁿ` is compact. -/
theorem isCompact_circBox (n : ℕ) : IsCompact (circBox n) :=
  isCompact_univ_pi fun _ => isCompact_Icc

/-- One row of Dyson's product, `∏_{l ≠ j} (1 - e^{i(θ_j - θ_l)})^m`. -/
def dysonRow {n : ℕ} (θ : Fin n → ℝ) (j : Fin n) (m : ℕ) : ℂ :=
  ∏ l : Fin n, if j = l then 1 else (1 - Complex.exp (I * ((θ j - θ l : ℝ) : ℂ))) ^ m

/-- Dyson's product `∏_{j ≠ l} (1 - z_j / z_l)^{a_j}` with `z_j = e^{iθ_j}`. -/
def dysonTerm (n : ℕ) (a : Fin n → ℕ) (θ : Fin n → ℝ) : ℂ := ∏ j, dysonRow θ j (a j)

/-- The torus integral of Dyson's product. -/
def dysonInt (n : ℕ) (a : Fin n → ℕ) : ℂ := ∫ θ in circBox n, dysonTerm n a θ

/-- Dyson's product is continuous. -/
theorem continuous_dysonTerm (n : ℕ) (a : Fin n → ℕ) : Continuous (dysonTerm n a) := by
  unfold dysonTerm dysonRow
  refine continuous_finsetProd _ fun j _ => continuous_finsetProd _ fun l _ => ?_
  split_ifs
  · exact continuous_const
  · fun_prop

/-- Dyson's product is integrable on `[-π, π]ⁿ`. -/
theorem integrableOn_dysonTerm (n : ℕ) (a : Fin n → ℕ) :
    IntegrableOn (dysonTerm n a) (circBox n) :=
  (continuous_dysonTerm n a).continuousOn.integrableOn_compact (isCompact_circBox n)

/-- `row(m + 1) = row(m) · row(1)` for one row of Dyson's product. -/
theorem dysonRow_succ {n : ℕ} (θ : Fin n → ℝ) (j : Fin n) (m : ℕ) :
    dysonRow θ j (m + 1) = dysonRow θ j m * dysonRow θ j 1 := by
  unfold dysonRow
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  split_ifs <;> ring

/-- Lowering the exponent `aⱼ` by one removes one copy of the `j`-th row of Dyson's product. -/
theorem dysonTerm_update {n : ℕ} (a : Fin n → ℕ) (θ : Fin n → ℝ) {j : Fin n} (h : 1 ≤ a j) :
    dysonTerm n a θ = dysonTerm n (Function.update a j (a j - 1)) θ * dysonRow θ j 1 := by
  unfold dysonTerm
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ (fun i => dysonRow θ i (Function.update a j (a j - 1) i))
      (Finset.mem_univ j), Function.update_self]
  have hrest : ∏ i ∈ Finset.univ.erase j, dysonRow θ i (Function.update a j (a j - 1) i) =
      ∏ i ∈ Finset.univ.erase j, dysonRow θ i (a i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hrest]
  obtain ⟨m, hm⟩ : ∃ m, a j = m + 1 := ⟨a j - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel, dysonRow_succ]
  ring

/-- Good's identity `∑_j ∏_{l ≠ j} (1 - z_j/z_l)⁻¹ = 1`, from Lagrange interpolation of the
constant `1` evaluated at `0`. -/
theorem sum_recip_dysonRow_one {n : ℕ} (hn : 0 < n) {θ : Fin n → ℝ}
    (hθ : ∀ j l, j ≠ l → Complex.exp (I * ((θ j - θ l : ℝ) : ℂ)) ≠ 1) :
    ∑ j, (dysonRow θ j 1)⁻¹ = 1 := by
  set v : Fin n → ℂ := fun j => Complex.exp (I * (θ j : ℂ)) with hv
  have hv0 : ∀ j, v j ≠ 0 := fun j => Complex.exp_ne_zero _
  have hquot : ∀ j l, Complex.exp (I * ((θ j - θ l : ℝ) : ℂ)) = v j / v l := fun j l => by
    rw [hv]; simp only
    rw [← Complex.exp_sub]; congr 1; push_cast; ring
  have hinj : Set.InjOn v (Finset.univ : Finset (Fin n)) := by
    intro j _ l _ hjl
    by_contra hne
    exact hθ j l hne (by rw [hquot, hjl, div_self (hv0 l)])
  have hsum := Lagrange.sum_basis hinj (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
  have h0 := congr_arg (Polynomial.eval 0) hsum
  rw [Polynomial.eval_finsetSum, Polynomial.eval_one] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Lagrange.basis, Polynomial.eval_prod, dysonRow,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), ite_eq_left rfl, one_mul,
    ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun l hl => ?_
  have hjl : j ≠ l := (Finset.ne_of_mem_erase hl).symm
  rw [ite_eq_right hjl, pow_one, hquot]
  have hne : v j ≠ v l := fun h => hθ j l hjl (by rw [hquot, h, div_self (hv0 l)])
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X]
  have h1 : v j - v l ≠ 0 := sub_ne_zero.mpr hne
  field_simp [hv0 l, h1]
  ring

/-- `e^(ix) ≠ 1` for `0 < |x| < 2π`. -/
theorem exp_I_mul_ne_one {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 2 * π) :
    Complex.exp (I * (x : ℂ)) ≠ 1 := by
  intro h
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h
  have hx' : (x : ℂ) = m * (2 * π) := by
    have := congr_arg (fun w => w / I) hm
    rw [mul_div_cancel_left₀ _ Complex.I_ne_zero] at this
    rw [this]; field_simp
  have hxr : x = m * (2 * π) := by exact_mod_cast hx'
  rcases lt_trichotomy m 0 with h | h | h
  · have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr h
    rw [hxr, abs_lt] at hx; nlinarith [Real.pi_pos]
  · simp [h] at hxr; exact hx0 hxr
  · have : (1 : ℝ) ≤ m := by exact_mod_cast h
    rw [hxr, abs_lt] at hx; nlinarith [Real.pi_pos]

/-- For almost every `θ ∈ [-π, π]ⁿ`, `e^(i(θⱼ - θₗ)) ≠ 1` for all `j ≠ l`. -/
theorem ae_circBox_good (n : ℕ) : ∀ᵐ θ ∂(volume.restrict (circBox n)),
    ∀ j l, j ≠ l → Complex.exp (I * ((θ j - θ l : ℝ) : ℂ)) ≠ 1 := by
  have h1 : ∀ᵐ θ : Fin n → ℝ, ∀ j, θ j ≠ π ∧ θ j ≠ -π := by
    rw [ae_all_iff]
    intro j
    filter_upwards [DLMF.Selberg.ae_coord_ne j π, DLMF.Selberg.ae_coord_ne j (-π)] with θ h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [ae_restrict_mem (measurableSet_circBox n), ae_restrict_of_ae h1,
    ae_restrict_of_ae (DLMF.Selberg.ae_coords_ne n)] with θ hθ hpi hne j l hjl
  have hj := hθ j (Set.mem_univ _)
  have hl := hθ l (Set.mem_univ _)
  have hj' : -π < θ j ∧ θ j < π :=
    ⟨lt_of_le_of_ne hj.1 (hpi j).2.symm, lt_of_le_of_ne hj.2 (hpi j).1⟩
  have hl' : -π < θ l ∧ θ l < π :=
    ⟨lt_of_le_of_ne hl.1 (hpi l).2.symm, lt_of_le_of_ne hl.2 (hpi l).1⟩
  refine exp_I_mul_ne_one (sub_ne_zero.mpr (hne j l hjl)) ?_
  rw [abs_lt]; constructor <;> linarith

/-- At such generic `θ`, every row of Dyson's product is nonzero. -/
theorem dysonRow_ne_zero {n : ℕ} {θ : Fin n → ℝ}
    (hθ : ∀ j l, j ≠ l → Complex.exp (I * ((θ j - θ l : ℝ) : ℂ)) ≠ 1) (j : Fin n) (m : ℕ) :
    dysonRow θ j m ≠ 0 := by
  unfold dysonRow
  refine Finset.prod_ne_zero_iff.mpr fun l _ => ?_
  split_ifs with h
  · exact one_ne_zero
  · exact pow_ne_zero _ (sub_ne_zero.mpr (hθ j l h).symm)

/-- Good's recursion for the torus integrals. -/
theorem dysonInt_rec {n : ℕ} (hn : 0 < n) (a : Fin n → ℕ) (h : ∀ j, 1 ≤ a j) :
    dysonInt n a = ∑ j, dysonInt n (Function.update a j (a j - 1)) := by
  unfold dysonInt
  rw [← integral_finsetSum _ fun j _ => integrableOn_dysonTerm n _]
  refine integral_congr_ae ?_
  filter_upwards [ae_circBox_good n] with θ hθ
  have key : ∀ j, dysonTerm n (Function.update a j (a j - 1)) θ =
      dysonTerm n a θ * (dysonRow θ j 1)⁻¹ := fun j => by
    rw [dysonTerm_update a θ (h j), mul_assoc, mul_inv_cancel₀ (dysonRow_ne_zero hθ j 1),
      mul_one]
  simp only [key, ← Finset.mul_sum, sum_recip_dysonRow_one hn hθ, mul_one]

/-! ### Removing a coordinate with zero exponent -/

/-- `insertNth k x y ∈ [-π, π]^(n+1)` iff `x ∈ [-π, π]` and `y ∈ [-π, π]ⁿ`. -/
theorem insertNth_mem_circBox {n : ℕ} (k : Fin (n + 1)) {x : ℝ} {y : Fin n → ℝ} :
    (k.insertNth x y : Fin (n + 1) → ℝ) ∈ circBox (n + 1) ↔
      x ∈ Icc (-π) π ∧ y ∈ circBox n := by
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  rw [Fin.forall_iff_succAbove k]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-- Splitting off the `k`-th coordinate of the box. -/
theorem integral_circBox_insertNth {n : ℕ} (k : Fin (n + 1)) (g : (Fin (n + 1) → ℝ) → ℂ)
    (hg : IntegrableOn g (circBox (n + 1))) :
    ∫ θ in circBox (n + 1), g θ =
      ∫ y in circBox n, ∫ x in Icc (-π) π, g (k.insertNth x y) := by
  have e := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k).symm
  have hsymm : ∀ p : ℝ × (Fin n → ℝ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k).symm p =
        k.insertNth p.1 p.2 := by
    intro p
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk]
  have hpre : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k).symm ⁻¹'
      (circBox (n + 1)) = Icc (-π) π ×ˢ circBox n := by
    ext ⟨x, y⟩
    rw [Set.mem_preimage, hsymm, Set.mem_prod]
    exact insertNth_mem_circBox k
  have h1 : ∫ θ in circBox (n + 1), g θ =
      ∫ p in Icc (-π) π ×ˢ circBox n, g (k.insertNth p.1 p.2) := by
    rw [← hpre, ← e.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _)]
    simp only [hsymm]
  have hint : IntegrableOn (fun p : ℝ × (Fin n → ℝ) => g (k.insertNth p.1 p.2))
      (Icc (-π) π ×ˢ circBox n) := by
    rw [← hpre]
    have := (e.integrableOn_comp_preimage (MeasurableEquiv.measurableEmbedding _)).mpr hg
    simpa only [Function.comp_def, hsymm] using this
  rw [Measure.volume_eq_prod] at h1 hint
  rw [h1, setIntegral_prod _ hint, integral_integral_swap]
  rw [IntegrableOn, ← Measure.prod_restrict] at hint
  exact hint

/-- `∫_{-π}^{π} (e^(-ix))^i dx = 2π` if `i = 0` and `0` otherwise. -/
theorem integral_exp_neg_I_pow (i : ℕ) :
    ∫ x in Icc (-π) π, Complex.exp (-(I * (x : ℂ))) ^ i = if i = 0 then 2 * π else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  split_ifs with hi
  · subst hi; simp; ring
  · have hc : (-(I * (i : ℂ))) ≠ 0 := by
      simp [Complex.I_ne_zero, hi]
    have hfun : (fun x : ℝ => Complex.exp (-(I * (x : ℂ))) ^ i) =
        fun x : ℝ => Complex.exp (-(I * (i : ℂ)) * x) := by
      ext x
      rw [← Complex.exp_nat_mul]; congr 1; ring
    rw [hfun, integral_exp_mul_complex hc]
    have h2 : Complex.exp (-(I * (i : ℂ)) * ((-π : ℝ) : ℂ)) =
        Complex.exp (-(I * (i : ℂ)) * (π : ℂ)) * Complex.exp (i * (2 * π * I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [h2, Complex.exp_nat_mul_two_pi_mul_I, mul_one, sub_self, zero_div]
    simp

/-- The average over a circle of a polynomial in `e^{-ix}` is its constant term. -/
theorem integral_prod_one_sub_exp {n : ℕ} (y : Fin n → ℝ) (m : Fin n → ℕ) :
    ∫ x in Icc (-π) π, ∏ j, (1 - Complex.exp (I * ((y j - x : ℝ) : ℂ))) ^ m j = 2 * π := by
  set P : Polynomial ℂ := ∏ j, (1 - Polynomial.C (Complex.exp (I * (y j : ℂ))) *
    Polynomial.X) ^ m j with hP
  have hev : ∀ x : ℝ, ∏ j, (1 - Complex.exp (I * ((y j - x : ℝ) : ℂ))) ^ m j =
      ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * Complex.exp (-(I * (x : ℂ))) ^ i := by
    intro x
    rw [← Polynomial.eval_eq_sum_range, hP, Polynomial.eval_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [← Complex.exp_add]; congr 3; push_cast; ring
  simp_rw [hev]
  rw [integral_finsetSum _ fun i _ => ((by fun_prop : Continuous fun x : ℝ =>
    P.coeff i * Complex.exp (-(I * (x : ℂ))) ^ i).continuousOn.integrableOn_compact
      isCompact_Icc)]
  simp_rw [integral_const_mul, integral_exp_neg_I_pow]
  rw [Finset.sum_eq_single 0 (fun i _ hi => by rw [ite_eq_right hi]; simp)
    (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h), ite_eq_left rfl,
    Polynomial.coeff_zero_eq_eval_zero, hP, Polynomial.eval_prod]
  simp

/-- The `k`-th row with exponent `0` is `1`. -/
theorem dysonRow_insertNth_self {n : ℕ} (k : Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ) :
    dysonRow (k.insertNth x y : Fin (n + 1) → ℝ) k 0 = 1 := by
  unfold dysonRow
  exact Finset.prod_eq_one fun l _ => by split_ifs <;> simp

/-- Inserting a variable at `k` multiplies the other rows by the factors involving the new variable.
-/
theorem dysonRow_insertNth {n : ℕ} (k : Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ) (j : Fin n)
    (m : ℕ) :
    dysonRow (k.insertNth x y : Fin (n + 1) → ℝ) (k.succAbove j) m =
      dysonRow y j m * (1 - Complex.exp (I * ((y j - x : ℝ) : ℂ))) ^ m := by
  unfold dysonRow
  rw [Fin.prod_univ_succAbove _ k, ite_eq_right (Fin.succAbove_ne k j), mul_comm]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    (Fin.succAbove_right_injective (p := k)).eq_iff]

/-- Dyson's product with `a_k = 0` factors after inserting the `k`-th variable. -/
theorem dysonTerm_insertNth {n : ℕ} (a : Fin (n + 1) → ℕ) {k : Fin (n + 1)} (hk : a k = 0)
    (x : ℝ) (y : Fin n → ℝ) :
    dysonTerm (n + 1) a (k.insertNth x y) =
      dysonTerm n (a ∘ k.succAbove) y *
        ∏ j : Fin n, (1 - Complex.exp (I * ((y j - x : ℝ) : ℂ))) ^ a (k.succAbove j) := by
  unfold dysonTerm
  rw [Fin.prod_univ_succAbove _ k, hk, dysonRow_insertNth_self, one_mul,
    ← Finset.prod_mul_distrib]
  simp only [dysonRow_insertNth, Function.comp_apply]

/-- If `a_k = 0`, integrating out the `k`-th variable gives `2π` times the integral in `n`
variables. -/
theorem dysonInt_succ_of_eq_zero {n : ℕ} (a : Fin (n + 1) → ℕ) {k : Fin (n + 1)} (hk : a k = 0) :
    dysonInt (n + 1) a = 2 * π * dysonInt n (a ∘ k.succAbove) := by
  unfold dysonInt
  rw [integral_circBox_insertNth k _ (integrableOn_dysonTerm _ a), ← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_circBox n) fun y _ => ?_
  simp_rw [dysonTerm_insertNth a hk]
  rw [integral_const_mul, integral_prod_one_sub_exp]
  ring

/-! ### Multinomial coefficients and the integer case -/

/-- The multinomial coefficient `(∑ aⱼ)! / ∏ aⱼ!`. -/
def mnom {n : ℕ} (a : Fin n → ℕ) : ℂ :=
  ((∑ j, a j).factorial : ℂ) / ∏ j, ((a j).factorial : ℂ)

/-- `∏ aⱼ! ≠ 0`. -/
theorem prod_factorial_ne_zero {n : ℕ} (a : Fin n → ℕ) : ∏ j, ((a j).factorial : ℂ) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (Nat.factorial_pos _).ne'

/-- The multinomial coefficient is unchanged by removing a zero exponent. -/
theorem mnom_succAbove {n : ℕ} (a : Fin (n + 1) → ℕ) {k : Fin (n + 1)} (hk : a k = 0) :
    mnom a = mnom (a ∘ k.succAbove) := by
  unfold mnom
  rw [Fin.sum_univ_succAbove _ k, Fin.prod_univ_succAbove _ k, hk]
  simp

/-- Lowering `aⱼ ≥ 1` by one lowers `∑ aᵢ` by one. -/
theorem sum_update_pred {n : ℕ} (a : Fin n → ℕ) {j : Fin n} (h : 1 ≤ a j) :
    (∑ i, Function.update a j (a j - 1) i) + 1 = ∑ i, a i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ a (Finset.mem_univ j), Function.update_self]
  rw [Finset.sum_congr rfl fun i hi => Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _]
  omega

/-- `mnom(a - eⱼ) · ∑ aᵢ = mnom(a) · aⱼ`. -/
theorem mnom_update_mul {n : ℕ} (a : Fin n → ℕ) {j : Fin n} (h : 1 ≤ a j) :
    mnom (Function.update a j (a j - 1)) * (∑ i, a i : ℕ) = mnom a * a j := by
  unfold mnom
  have hS := sum_update_pred a h
  have hP : (∏ i, ((Function.update a j (a j - 1) i).factorial : ℂ)) * (a j : ℂ) =
      ∏ i, ((a i).factorial : ℂ) := by
    have hrest : ∏ i ∈ Finset.univ.erase j,
        ((Function.update a j (a j - 1) i).factorial : ℂ) =
        ∏ i ∈ Finset.univ.erase j, ((a i).factorial : ℂ) :=
      Finset.prod_congr rfl fun i hi => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
      ← Finset.mul_prod_erase _ (fun i => ((a i).factorial : ℂ)) (Finset.mem_univ j),
      Function.update_self, hrest]
    obtain ⟨m, hm⟩ : ∃ m, a j = m + 1 := ⟨a j - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast; ring
  have h1 := prod_factorial_ne_zero (Function.update a j (a j - 1))
  have haj : (a j : ℂ) ≠ 0 := by exact_mod_cast (show a j ≠ 0 by omega)
  rw [← hS, ← hP, Nat.factorial_succ]
  push_cast
  field_simp

/-- Pascal recursion for multinomial coefficients: `mnom(a) = ∑ⱼ mnom(a - eⱼ)` when all `aⱼ ≥ 1`. -/
theorem mnom_rec {n : ℕ} (hn : 0 < n) (a : Fin n → ℕ) (h : ∀ j, 1 ≤ a j) :
    mnom a = ∑ j, mnom (Function.update a j (a j - 1)) := by
  have hS0 : ((∑ i, a i : ℕ) : ℂ) ≠ 0 := by
    have : 1 ≤ ∑ i, a i := (h ⟨0, hn⟩).trans
      (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ _))
    exact_mod_cast (show ∑ i, a i ≠ 0 by omega)
  have key : ∀ j, mnom (Function.update a j (a j - 1)) = mnom a * a j / (∑ i, a i : ℕ) :=
    fun j => by rw [← mnom_update_mul a (h j), mul_div_cancel_right₀ _ hS0]
  simp_rw [key, ← Finset.sum_div, ← Finset.mul_sum]
  rw [mul_div_assoc, show (∑ i, (a i : ℂ)) = ((∑ i, a i : ℕ) : ℂ) by push_cast; rfl,
    div_self hS0, mul_one]

/-- **Dyson's conjecture** (Gunson, Wilson; Good's proof): the constant term of
`∏_{j ≠ l} (1 - z_j/z_l)^{a_j}` is the multinomial coefficient. -/
theorem dysonInt_eq (n : ℕ) (a : Fin n → ℕ) : dysonInt n a = (2 * π : ℂ) ^ n * mnom a := by
  induction n with
  | zero =>
    have hset : circBox 0 = Set.univ := Set.eq_univ_of_forall fun t => fun i => i.elim0
    simp [dysonInt, dysonTerm, mnom, hset, Measure.real, volume_pi]
  | succ n ih =>
    suffices H : ∀ S, ∀ a : Fin (n + 1) → ℕ, ∑ j, a j = S →
        dysonInt (n + 1) a = (2 * π : ℂ) ^ (n + 1) * mnom a from H _ a rfl
    intro S
    induction S using Nat.strong_induction_on with
    | _ S hS =>
      intro a ha
      by_cases hz : ∃ k, a k = 0
      · obtain ⟨k, hk⟩ := hz
        rw [dysonInt_succ_of_eq_zero a hk, ih, mnom_succAbove a hk]
        ring
      · simp only [not_exists] at hz
        have h1 : ∀ j, 1 ≤ a j := fun j => Nat.one_le_iff_ne_zero.mpr (hz j)
        rw [dysonInt_rec (Nat.succ_pos n) a h1, mnom_rec (Nat.succ_pos n) a h1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        refine hS _ ?_ _ rfl
        have := sum_update_pred a (h1 j)
        omega

/-! ### The circular integrand at integer exponents -/

/-- The integrand of 5.14.7. -/
def circIntegrand (n : ℕ) (b : ℂ) (θ : Fin n → ℝ) : ℂ :=
  ∏ j : Fin n, ∏ k : Fin n,
    (if j.val < k.val then
      (‖Complex.exp (I * θ j) - Complex.exp (I * θ k)‖ : ℂ) ^ (2 * b) else 1)

/-- `|e^(ix) - e^(iy)|² = (1 - e^(i(x-y)))(1 - e^(i(y-x)))`. -/
theorem norm_exp_sub_sq (x y : ℝ) :
    ((‖Complex.exp (I * x) - Complex.exp (I * y)‖ ^ 2 : ℝ) : ℂ) =
      (1 - Complex.exp (I * ((x - y : ℝ) : ℂ))) * (1 - Complex.exp (I * ((y - x : ℝ) : ℂ))) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  have hc : ∀ t : ℝ, (starRingEnd ℂ) (Complex.exp (I * t)) = (Complex.exp (I * t))⁻¹ := by
    intro t
    rw [← Complex.exp_conj, ← Complex.exp_neg]
    simp [Complex.conj_ofReal]
  rw [map_sub, hc, hc]
  have hsub : ∀ s t : ℝ, Complex.exp (I * ((s - t : ℝ) : ℂ)) =
      Complex.exp (I * s) * (Complex.exp (I * t))⁻¹ := by
    intro s t
    rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [hsub, hsub]
  have h1 := Complex.exp_ne_zero (I * x)
  have h2 := Complex.exp_ne_zero (I * y)
  field_simp

/-- `∏_{j<l} f(j,l) f(l,j) = ∏_{j≠l} f(j,l)`. -/
theorem prod_lt_mul_eq_prod_ne {n : ℕ} (f : Fin n → Fin n → ℂ) :
    (∏ j : Fin n, ∏ l : Fin n, if j.val < l.val then f j l * f l j else 1) =
      ∏ j : Fin n, ∏ l : Fin n, if j = l then 1 else f j l := by
  have hsplit : ∀ j l : Fin n, (if j = l then (1 : ℂ) else f j l) =
      (if j.val < l.val then f j l else 1) * (if l.val < j.val then f j l else 1) := by
    intro j l
    rcases lt_trichotomy j.val l.val with h | h | h
    · rw [ite_eq_right (Fin.ne_of_val_ne h.ne), ite_eq_left h, ite_eq_right (by omega),
        mul_one]
    · rw [ite_eq_left (Fin.ext h), ite_eq_right (by omega), ite_eq_right (by omega), mul_one]
    · rw [ite_eq_right (Fin.ne_of_val_ne h.ne'), ite_eq_right (by omega), ite_eq_left h,
        one_mul]
  have hswap : (∏ j : Fin n, ∏ l : Fin n, if l.val < j.val then f j l else 1) =
      ∏ j : Fin n, ∏ l : Fin n, if j.val < l.val then f l j else 1 :=
    Finset.prod_comm
  simp_rw [hsplit, Finset.prod_mul_distrib]
  rw [hswap, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  split_ifs <;> simp

/-- For natural `k`, the integrand of 5.14.7 is Dyson's product with all exponents `k`. -/
theorem circIntegrand_natCast (n k : ℕ) (θ : Fin n → ℝ) :
    circIntegrand n k θ = dysonTerm n (fun _ => k) θ := by
  unfold circIntegrand dysonTerm dysonRow
  have hpow : ∀ j l : Fin n, ((‖Complex.exp (I * θ j) - Complex.exp (I * θ l)‖ : ℝ) : ℂ) ^
      (2 * (k : ℂ)) = (1 - Complex.exp (I * ((θ j - θ l : ℝ) : ℂ))) ^ k *
        (1 - Complex.exp (I * ((θ l - θ j : ℝ) : ℂ))) ^ k := by
    intro j l
    rw [show (2 * (k : ℂ)) = ((2 * k : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast,
      pow_mul, ← Complex.ofReal_pow, norm_exp_sub_sq, mul_pow]
  simp_rw [hpow]
  exact prod_lt_mul_eq_prod_ne (fun j l => (1 - Complex.exp (I * ((θ j - θ l : ℝ) : ℂ))) ^ k)

/-- The left-hand side of 5.14.7. -/
def circInt (n : ℕ) (b : ℂ) : ℂ :=
  (1 / (2 * π : ℂ) ^ (n : ℂ)) * ∫ θ in circBox n, circIntegrand n b θ

/-- The right-hand side of 5.14.7. -/
def circRHS (n : ℕ) (b : ℂ) : ℂ := Complex.Gamma (1 + b * n) / Complex.Gamma (1 + b) ^ n

/-- 5.14.7 for natural `b = k` (Dyson's constant-term identity). -/
theorem circInt_natCast (n k : ℕ) : circInt n k = circRHS n k := by
  unfold circInt circRHS
  simp_rw [circIntegrand_natCast]
  rw [show (∫ θ in circBox n, dysonTerm n (fun _ => k) θ) = dysonInt n (fun _ => k) from rfl,
    dysonInt_eq, Complex.cpow_natCast]
  have h0 : (2 * π : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero])
  rw [← mul_assoc, one_div, inv_mul_cancel₀ h0, one_mul, mnom]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Finset.prod_const]
  rw [show (1 + (k : ℂ) * n) = ((n * k : ℕ) : ℂ) + 1 by push_cast; ring,
    show (1 + (k : ℂ)) = ((k : ℕ) : ℂ) + 1 by ring, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial]

/-! ### Modulus of the circular integrand -/

/-- The squared modulus `∏_{j<k} |e^{iθ_j} - e^{iθ_k}|²`. -/
def circV (n : ℕ) (θ : Fin n → ℝ) : ℝ :=
  ∏ j : Fin n, ∏ k : Fin n,
    if j.val < k.val then ‖Complex.exp (I * θ j) - Complex.exp (I * θ k)‖ ^ 2 else 1

/-- The squared modulus `∏_{j<k} |e^(iθⱼ) - e^(iθₖ)|²` is measurable. -/
theorem measurable_circV (n : ℕ) : Measurable (circV n) := by
  unfold circV
  fun_prop

/-- The integrand of 5.14.7 is measurable. -/
theorem measurable_circIntegrand (n : ℕ) (b : ℂ) : Measurable (circIntegrand n b) := by
  unfold circIntegrand
  fun_prop

/-- The squared modulus `circV` is nonnegative. -/
theorem circV_nonneg (n : ℕ) (θ : Fin n → ℝ) : 0 ≤ circV n θ := by
  unfold circV
  exact Finset.prod_nonneg fun j _ => Finset.prod_nonneg fun k _ => by
    split_ifs <;> positivity

/-- `|e^(ix) - e^(iy)| ≤ 2`. -/
theorem norm_exp_sub_le (x y : ℝ) : ‖Complex.exp (I * x) - Complex.exp (I * y)‖ ≤ 2 := by
  calc ‖Complex.exp (I * x) - Complex.exp (I * y)‖
      ≤ ‖Complex.exp (I * x)‖ + ‖Complex.exp (I * y)‖ := norm_sub_le _ _
    _ = 2 := by rw [Complex.norm_exp_I_mul_ofReal, Complex.norm_exp_I_mul_ofReal]; norm_num

/-- `circV n θ ≤ 4^(n²)`. -/
theorem circV_le (n : ℕ) (θ : Fin n → ℝ) : circV n θ ≤ 4 ^ (n * n) := by
  unfold circV
  calc (∏ j : Fin n, ∏ k : Fin n,
        if j.val < k.val then ‖Complex.exp (I * θ j) - Complex.exp (I * θ k)‖ ^ 2 else 1)
      ≤ ∏ _j : Fin n, ∏ _k : Fin n, (4 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun j _ => Finset.prod_nonneg fun k _ => by
          split_ifs <;> positivity) fun j _ => ?_
        refine Finset.prod_le_prod₀ (fun k _ => by split_ifs <;> positivity) fun k _ => ?_
        split_ifs
        · have h := norm_exp_sub_le (θ j) (θ k)
          have h0 := norm_nonneg (Complex.exp (I * θ j) - Complex.exp (I * θ k))
          nlinarith
        · norm_num
    _ = 4 ^ (n * n) := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [← pow_mul]

/-- At generic `θ`, `e^(iθⱼ) ≠ e^(iθₗ)` for `j ≠ l`. -/
theorem exp_ne_exp_of_good {n : ℕ} {θ : Fin n → ℝ}
    (hθ : ∀ j l, j ≠ l → Complex.exp (I * ((θ j - θ l : ℝ) : ℂ)) ≠ 1) {j l : Fin n}
    (hjl : j ≠ l) : Complex.exp (I * θ j) - Complex.exp (I * θ l) ≠ 0 := by
  intro h
  apply hθ j l hjl
  rw [show I * ((θ j - θ l : ℝ) : ℂ) = I * θ j - I * θ l by push_cast; ring, Complex.exp_sub,
    sub_eq_zero.mp h, div_self (Complex.exp_ne_zero _)]

/-- At generic `θ`, `circV n θ > 0`. -/
theorem circV_pos {n : ℕ} {θ : Fin n → ℝ}
    (hθ : ∀ j l, j ≠ l → Complex.exp (I * ((θ j - θ l : ℝ) : ℂ)) ≠ 1) : 0 < circV n θ := by
  unfold circV
  refine Finset.prod_pos fun j _ => Finset.prod_pos fun k _ => ?_
  split_ifs with h
  · have := exp_ne_exp_of_good hθ (Fin.ne_of_lt h)
    positivity
  · exact one_pos

/-- At generic `θ`, the modulus of the integrand of 5.14.7 is `circV n θ ^ Re b`. -/
theorem norm_circIntegrand {n : ℕ} {θ : Fin n → ℝ}
    (hθ : ∀ j l, j ≠ l → Complex.exp (I * ((θ j - θ l : ℝ) : ℂ)) ≠ 1) (b : ℂ) :
    ‖circIntegrand n b θ‖ = circV n θ ^ b.re := by
  unfold circIntegrand circV
  rw [norm_prod, ← Real.finsetProd_rpow _ _ fun i _ => Finset.prod_nonneg fun j _ => by
    split_ifs <;> positivity]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [norm_prod, ← Real.finsetProd_rpow _ _ fun k _ => by split_ifs <;> positivity]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs with hjk
  · have hpos : 0 < ‖Complex.exp (I * θ j) - Complex.exp (I * θ k)‖ :=
      norm_pos_iff.mpr (exp_ne_exp_of_good hθ (Fin.ne_of_lt hjk))
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, ← Real.rpow_natCast,
      ← Real.rpow_mul (norm_nonneg _)]
    simp
  · simp

/-- For real `σ`, the integrand of 5.14.7 is the cast of `circV n θ ^ σ`. -/
theorem circIntegrand_ofReal {n : ℕ} (σ : ℝ) (θ : Fin n → ℝ) :
    circIntegrand n σ θ = ((circV n θ ^ σ : ℝ) : ℂ) := by
  unfold circIntegrand circV
  rw [← Real.finsetProd_rpow _ _ fun i _ => Finset.prod_nonneg fun j _ => by
    split_ifs <;> positivity, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Real.finsetProd_rpow _ _ fun k _ => by split_ifs <;> positivity, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
      Complex.ofReal_cpow (norm_nonneg _)]
    push_cast; ring_nf
  · simp

/-- At generic `θ`, the integrand of 5.14.7 is holomorphic in `b`. -/
theorem differentiableAt_circIntegrand {n : ℕ} {θ : Fin n → ℝ}
    (hθ : ∀ j l, j ≠ l → Complex.exp (I * ((θ j - θ l : ℝ) : ℂ)) ≠ 1) (b : ℂ) :
    DifferentiableAt ℂ (fun b => circIntegrand n b θ) b := by
  unfold circIntegrand
  refine DifferentiableAt.fun_finsetProd fun j _ => DifferentiableAt.fun_finsetProd fun k _ => ?_
  split_ifs with h
  · have hne : ((‖Complex.exp (I * θ j) - Complex.exp (I * θ k)‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (exp_ne_exp_of_good hθ (Fin.ne_of_lt h)))
    exact (differentiableAt_id.const_mul 2).const_cpow (Or.inl hne)
  · exact differentiableAt_const _

/-- `circV n θ ^ σ` is integrable on `[-π, π]ⁿ` for `σ ≥ 0`. -/
theorem integrableOn_circV_rpow_of_nonneg (n : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    IntegrableOn (fun θ => circV n θ ^ σ) (circBox n) := by
  refine Measure.integrableOn_of_bounded (M := ((4 : ℝ) ^ (n * n)) ^ σ)
    (isCompact_circBox n).measure_lt_top.ne
    ((measurable_circV n).pow_const σ).aestronglyMeasurable
    (Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (circV_nonneg n θ) σ)]
  exact Real.rpow_le_rpow (circV_nonneg n θ) (circV_le n θ) hσ

/-- Holomorphy of the circular integral wherever the moduli are integrable. -/
theorem differentiableOn_circInt {n : ℕ} {s0 : ℝ}
    (hint : ∀ σ : ℝ, s0 < σ → IntegrableOn (fun θ => circV n θ ^ σ) (circBox n)) :
    DifferentiableOn ℂ (circInt n) {b | s0 < b.re} := by
  have h : DifferentiableOn ℂ (fun b => ∫ θ in circBox n, circIntegrand n b θ)
      {b | s0 < b.re} := by
    refine DLMF.Gamma.vb_differentiableOn_integral
      (isOpen_lt continuous_const Complex.continuous_re)
      (fun b _ => (measurable_circIntegrand n b).aestronglyMeasurable) ?_ ?_
    · filter_upwards [ae_circBox_good n] with θ hθ
      exact fun b _ => (differentiableAt_circIntegrand hθ b).differentiableWithinAt
    · intro b₀ hb₀
      have hb₀' : s0 < b₀.re := hb₀
      set ε := (b₀.re - s0) / 2 with hε
      have hε0 : 0 < ε := by rw [hε]; linarith
      have hre : ∀ z ∈ Metric.closedBall b₀ ε, b₀.re - ε ≤ z.re ∧ z.re ≤ b₀.re + ε := by
        intro z hz
        have := Complex.abs_re_le_norm (z - b₀)
        rw [Metric.mem_closedBall, dist_eq_norm] at hz
        have h2 : |(z - b₀).re| ≤ ε := this.trans hz
        rw [Complex.sub_re, abs_le] at h2
        constructor <;> linarith
      refine ⟨ε, hε0, fun z hz => ?_,
        fun θ => circV n θ ^ (b₀.re - ε) + circV n θ ^ (b₀.re + ε),
        (hint _ (by linarith)).add (hint _ (by linarith)), ?_⟩
      · show s0 < z.re
        linarith [(hre z hz).1]
      · filter_upwards [ae_circBox_good n] with θ hθ z hz
        rw [norm_circIntegrand hθ]
        have hV := circV_pos hθ
        obtain ⟨h1, h2⟩ := hre z hz
        rcases le_or_gt (circV n θ) 1 with hV1 | hV1
        · have := Real.rpow_le_rpow_of_exponent_ge hV hV1 h1
          linarith [Real.rpow_nonneg hV.le (b₀.re + ε)]
        · have := Real.rpow_le_rpow_of_exponent_le hV1.le h2
          linarith [Real.rpow_nonneg hV.le (b₀.re - ε)]
  exact h.const_mul _

/-- Exponential-type bound for the left side of 5.14.7 on `Re w ≥ 0`. -/
theorem exists_norm_circInt_le (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, 0 ≤ w.re → ‖circInt n w‖ ≤ A * ((4 : ℝ) ^ (n * n)) ^ w.re := by
  have : IsFiniteMeasure (volume.restrict (circBox n)) :=
    isFiniteMeasure_restrict.2 (isCompact_circBox n).measure_lt_top.ne
  refine ⟨‖1 / (2 * π : ℂ) ^ (n : ℂ)‖ * (volume.restrict (circBox n)).real Set.univ,
    by positivity, fun w hw => ?_⟩
  unfold circInt
  rw [norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [mul_comm]
  refine norm_integral_le_of_norm_le_const ?_
  filter_upwards [ae_circBox_good n] with θ hθ
  rw [norm_circIntegrand hθ]
  exact Real.rpow_le_rpow (circV_nonneg n θ) (circV_le n θ) hw

/-! ### The right-hand side -/

/-- `Γ(1 + nb)/Γ(1 + b)ⁿ` is holomorphic on `Re b > -1/n`. -/
theorem differentiableOn_circRHS {n : ℕ} (hn : 0 < n) :
    DifferentiableOn ℂ (circRHS n) {b | (-1 / n : ℝ) < b.re} := by
  intro b hb
  have hb' : (-1 / n : ℝ) < b.re := hb
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1n : -1 < n * b.re := by rw [div_lt_iff₀ hn'] at hb'; linarith
  have h1 : 0 < (1 + b * n).re := by simp; linarith
  have h2 : 0 < (1 + b).re := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simp
    rcases le_or_gt 0 b.re with h | h
    · linarith
    · nlinarith
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold circRHS
  refine DifferentiableAt.div ?_ ?_ (pow_ne_zero _ (Complex.Gamma_ne_zero_of_re_pos h2))
  · exact (Complex.differentiableAt_Gamma _ (DLMF.Hypergeometric.not_neg_nat_of_re_pos h1)).comp b
      (by fun_prop)
  · exact ((Complex.differentiableAt_Gamma _ (DLMF.Hypergeometric.not_neg_nat_of_re_pos h2)).comp b
      (by fun_prop)).pow n

/-- `Γ(w+a)/Γ(w+1)` is bounded on the closed right half-plane for `0 < a ≤ 1`, by the Beta
integral. -/
theorem exists_norm_Gamma_add_div_le {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∃ K : ℝ, ∀ w : ℂ, 0 ≤ w.re → ‖Complex.Gamma (w + a) / Complex.Gamma (w + 1)‖ ≤ K := by
  rcases eq_or_lt_of_le ha1 with rfl | ha1
  · refine ⟨1, fun w hw => ?_⟩
    have : Complex.Gamma (w + 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    simp [div_self this]
  set g : ℝ → ℝ := fun x =>
    ‖(x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ (((1 - a : ℝ) : ℂ) - 1)‖ with hg
  have hgi : IntervalIntegrable g volume 0 1 :=
    (Complex.betaIntegral_convergent (u := a) (v := ((1 - a : ℝ) : ℂ)) (by simpa using ha0)
      (by simp; linarith)).norm
  have hG1a : Complex.Gamma ((1 - a : ℝ) : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  refine ⟨(∫ x in (0 : ℝ)..1, g x) / ‖Complex.Gamma ((1 - a : ℝ) : ℂ)‖, fun w hw => ?_⟩
  have hs : 0 < (w + a).re := by simp; linarith
  have ht : 0 < (((1 - a : ℝ) : ℂ)).re := by simp; linarith
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral hs ht
  rw [show w + a + ((1 - a : ℝ) : ℂ) = w + 1 by push_cast; ring] at hB
  have hGw : Complex.Gamma (w + 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hq : Complex.Gamma (w + a) / Complex.Gamma (w + 1) =
      Complex.betaIntegral (w + a) ((1 - a : ℝ) : ℂ) / Complex.Gamma ((1 - a : ℝ) : ℂ) := by
    rw [div_eq_div_iff hGw hG1a]
    linear_combination hB
  rw [hq, norm_div]
  refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
  unfold Complex.betaIntegral
  refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ hgi
  refine Eventually.of_forall fun x hx => ?_
  simp only [hg, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
  refine Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 ?_
  simp
  linarith

/-- Exponential-type bound for `Γ(1 + nb)/Γ(1 + b)ⁿ` on `Re w ≥ 0`. -/
theorem exists_norm_circRHS_le {n : ℕ} (hn : 0 < n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, 0 ≤ w.re → ‖circRHS n w‖ ≤ B * ((n : ℝ) ^ n) ^ w.re := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hex : ∀ k : Fin n, ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, 0 ≤ w.re →
      ‖Complex.Gamma (w + ((((k : ℕ) : ℝ) + 1) / n : ℝ)) / Complex.Gamma (w + 1)‖ ≤ K := by
    intro k
    obtain ⟨K, hK⟩ := exists_norm_Gamma_add_div_le (a := (((k : ℕ) : ℝ) + 1) / n)
      (by positivity) (by rw [div_le_one hn']; exact_mod_cast k.isLt)
    exact ⟨max K 0, le_max_right _ _, fun w hw => (hK w hw).trans (le_max_left _ _)⟩
  choose K hK0 hK using hex
  refine ⟨‖(2 * π : ℂ) ^ ((1 - n : ℂ) / 2)‖ * Real.sqrt n * ∏ k, K k,
    mul_nonneg (by positivity) (Finset.prod_nonneg fun k _ => hK0 k), fun w hw => ?_⟩
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmul := Complex.Gamma_mul_nat hn (w + 1 / n)
  rw [show (n : ℂ) * (w + 1 / n) = 1 + w * n by field_simp; ring] at hmul
  have hprod : ∏ k ∈ Finset.range n, Complex.Gamma (w + 1 / n + k / n) =
      ∏ k ∈ Finset.range n, Complex.Gamma (w + (((k : ℝ) + 1) / n : ℝ)) :=
    Finset.prod_congr rfl fun k _ => by congr 1; push_cast; ring
  have heq : circRHS n w = (2 * π : ℂ) ^ ((1 - n : ℂ) / 2) * (n : ℂ) ^ (1 + w * n - 1 / 2) *
      ∏ k ∈ Finset.range n, (Complex.Gamma (w + (((k : ℝ) + 1) / n : ℝ)) /
        Complex.Gamma (w + 1)) := by
    unfold circRHS
    rw [hmul, hprod, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
      show (1 + w) = (w + 1) by ring]
    ring
  have hpow : ‖(n : ℂ) ^ (1 + w * n - 1 / 2)‖ = Real.sqrt n * ((n : ℝ) ^ n) ^ w.re := by
    have hre : (1 + w * n - 1 / 2 : ℂ).re = n * w.re + 1 / 2 := by simp; ring
    rw [show (n : ℂ) ^ (1 + w * n - 1 / 2) = ((n : ℝ) : ℂ) ^ (1 + w * n - 1 / 2) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn', hre, Real.rpow_add hn', Real.sqrt_eq_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul hn'.le]
    ring_nf
  have hP : ∏ k ∈ Finset.range n, ‖Complex.Gamma (w + (((k : ℝ) + 1) / n : ℝ)) /
      Complex.Gamma (w + 1)‖ ≤ ∏ k, K k := by
    rw [← Fin.prod_univ_eq_prod_range (fun k => ‖Complex.Gamma (w + (((k : ℝ) + 1) / n : ℝ)) /
      Complex.Gamma (w + 1)‖) n]
    exact Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => hK k w hw
  rw [heq, norm_mul, norm_mul, norm_prod, hpow]
  calc ‖(2 * π : ℂ) ^ ((1 - n : ℂ) / 2)‖ * (Real.sqrt n * ((n : ℝ) ^ n) ^ w.re) *
        ∏ k ∈ Finset.range n, ‖Complex.Gamma (w + (((k : ℝ) + 1) / n : ℝ)) /
          Complex.Gamma (w + 1)‖
      ≤ ‖(2 * π : ℂ) ^ ((1 - n : ℂ) / 2)‖ * (Real.sqrt n * ((n : ℝ) ^ n) ^ w.re) *
        ∏ k, K k := mul_le_mul_of_nonneg_left hP (by positivity)
    _ = _ := by ring

/-! ### Carlson's theorem and continuation -/

/-- Dyson's integral 5.14.7 on the half-plane `Re w > 0`: Carlson's theorem from the integer
values (Good's identity), then the identity theorem. -/
private lemma circInt_eq_circRHS_of_re_pos {n : ℕ} (hn : 0 < n) {w : ℂ} (hw : 0 < w.re) :
    circInt n w = circRHS n w := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hneg : (-1 / n : ℝ) < 0 := by
    have : (0 : ℝ) < 1 / n := by positivity
    rw [neg_div]; linarith
  have hdA : DifferentiableOn ℂ (circInt n) {b | (0 : ℝ) < b.re} :=
    differentiableOn_circInt (s0 := 0) fun σ hσ => integrableOn_circV_rpow_of_nonneg n hσ.le
  have hdG := differentiableOn_circRHS hn
  have hD0 : {b : ℂ | (0 : ℝ) < b.re} ⊆ {b : ℂ | (-1 / n : ℝ) < b.re} := fun b hb => by
    simp only [Set.mem_ofPred_eq] at hb ⊢; linarith
  -- Carlson's theorem for `f z = F (z + 1) - G (z + 1)`
  set f : ℂ → ℂ := fun z => circInt n (z + 1) - circRHS n (z + 1) with hf
  have hfd : DifferentiableOn ℂ f {z : ℂ | (-1 : ℝ) < z.re} := by
    have hmaps : ∀ z ∈ {z : ℂ | (-1 : ℝ) < z.re}, z + 1 ∈ {b : ℂ | (0 : ℝ) < b.re} :=
      fun z hz => by simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.one_re] at hz ⊢; linarith
    exact (hdA.comp (by fun_prop) hmaps).sub ((hdG.mono hD0).comp (by fun_prop) hmaps)
  have hfcl : DiffContOnCl ℂ f {z : ℂ | 0 < z.re} := by
    refine (hfd.mono ?_).diffContOnCl
    intro z hz
    have := closure_lt_subset_le continuous_const Complex.continuous_re hz
    simp only [Set.mem_ofPred_eq] at this ⊢
    linarith
  obtain ⟨A, hA0, hA⟩ := exists_norm_circInt_le n
  obtain ⟨B, hB0, hB⟩ := exists_norm_circRHS_le hn
  set M : ℝ := (4 : ℝ) ^ (n * n) with hM
  set P : ℝ := (n : ℝ) ^ n with hP
  have hM1 : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hP1 : 1 ≤ P := one_le_pow₀ (by exact_mod_cast hn)
  have hbound : ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ A * M ^ (z.re + 1) + B * P ^ (z.re + 1) := by
    intro z hz
    have hw : 0 ≤ (z + 1).re := by simp; linarith
    have hre : (z + 1).re = z.re + 1 := by simp
    calc ‖f z‖ ≤ ‖circInt n (z + 1)‖ + ‖circRHS n (z + 1)‖ := norm_sub_le _ _
      _ ≤ _ := by rw [← hre]; exact add_le_add (hA _ hw) (hB _ hw)
  set τ := Real.log M + Real.log P with hτ
  have hτ0 : 0 ≤ τ := add_nonneg (Real.log_nonneg hM1) (Real.log_nonneg hP1)
  have hrpow : ∀ (X : ℝ), 1 ≤ X → Real.log X ≤ τ → ∀ z : ℂ, 0 ≤ z.re →
      X ^ (z.re + 1) ≤ X * Real.exp (τ * ‖z‖) := by
    intro X hX hXτ z hz
    have hX0 : 0 < X := by linarith
    rw [Real.rpow_add hX0, Real.rpow_one, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hX0.le
    rw [Real.rpow_def_of_pos hX0]
    refine Real.exp_le_exp.mpr ?_
    have h1 := Complex.re_le_norm z
    have h2 := Real.log_nonneg hX
    nlinarith [norm_nonneg z]
  have hexp : ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ (A * M + B * P) * Real.exp (τ * ‖z‖) := by
    intro z hz
    refine (hbound z hz).trans ?_
    have h1 := hrpow M hM1 (by rw [hτ]; linarith [Real.log_nonneg hP1]) z hz
    have h2 := hrpow P hP1 (by rw [hτ]; linarith [Real.log_nonneg hM1]) z hz
    nlinarith [Real.exp_pos (τ * ‖z‖)]
  have him : ∀ y : ℝ, ‖f (y * I)‖ ≤ (A * M + B * P) * Real.exp (0 * |y|) := by
    intro y
    have h := hbound (y * I) (by simp)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, zero_add, Real.rpow_one] at h
    simpa using h
  have hzero : ∀ k : ℕ, f k = 0 := fun k => by
    simp only [hf]
    rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, circInt_natCast, sub_self]
  have hcarl := Complex.eqOn_zero_of_natCast_eq_zero hfcl hexp him Real.pi_pos hzero
  have hge1 : ∀ w : ℂ, 1 ≤ w.re → circInt n w = circRHS n w := fun w hw => by
    have := hcarl (w - 1) (by simp; linarith)
    simp only [hf, sub_add_cancel] at this
    exact sub_eq_zero.mp this
  have hU : IsOpen {b : ℂ | (0 : ℝ) < b.re} := isOpen_lt continuous_const Complex.continuous_re
  refine (hdA.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    ((hdG.mono hD0).analyticOnNhd hU) (convex_halfSpace_re_gt 0).isPreconnected
    (z₀ := 2) (by simp) ?_ hw
  have hV : IsOpen {c : ℂ | 1 < c.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hV.mem_nhds (by simp : (2 : ℂ) ∈ {c : ℂ | 1 < c.re})] with c hc
  exact hge1 c (le_of_lt hc)

/-- For `σ > -1/n`, `circV n θ ^ σ` is integrable on `[-π, π]ⁿ`, by Landau's theorem applied to
the analytic continuation of the integral from `Re b > 0`. -/
private lemma integrableOn_circV_rpow {n : ℕ} (hn : 0 < n) {σ : ℝ} (hσ : (-1 / n : ℝ) < σ) :
    IntegrableOn (fun θ => circV n θ ^ σ) (circBox n) := by
  have hdG := differentiableOn_circRHS hn
  have hpos : ∀ w : ℂ, 0 < w.re → circInt n w = circRHS n w :=
    fun w hw => circInt_eq_circRHS_of_re_pos hn hw
  set M : ℝ := (4 : ℝ) ^ (n * n)
  have hMpos : 0 < M := by positivity
  have : IsFiniteMeasure (volume.restrict (circBox n)) :=
    isFiniteMeasure_restrict.2 (isCompact_circBox n).measure_lt_top.ne
  set R : ℂ → ℂ := fun z => (M : ℂ) ^ (-z) * ((2 * π : ℂ) ^ (n : ℂ) * circRHS n z) with hR
  have hRd : DifferentiableOn ℂ R (Metric.ball ((1 : ℝ) : ℂ) (1 + 1 / n)) := by
    have hball : Metric.ball ((1 : ℝ) : ℂ) (1 + 1 / n) ⊆ {b : ℂ | (-1 / n : ℝ) < b.re} := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have := Complex.abs_re_le_norm (z - ((1 : ℝ) : ℂ))
      rw [Complex.sub_re, Complex.ofReal_re, abs_le] at this
      simp only [Set.mem_ofPred_eq]
      rw [neg_div]
      linarith
    refine DifferentiableOn.mul (fun z _ => ?_) ((hdG.mono hball).const_mul _)
    exact (differentiableAt_id.neg.const_cpow
      (Or.inl (by exact_mod_cast hMpos.ne'))).differentiableWithinAt
  have heq : ∀ σ' : ℝ, 0 < σ' → σ' ≤ 1 →
      ((∫ θ, (fun _ => (1 : ℝ)) θ * (fun θ => circV n θ / M) θ ^ σ'
        ∂(volume.restrict (circBox n)) : ℝ) : ℂ) = R σ' := by
    intro σ' hσ' _
    have h1 : (∫ θ in circBox n, (fun _ => (1 : ℝ)) θ * (fun θ => circV n θ / M) θ ^ σ') =
        M ^ (-σ') * ∫ θ in circBox n, circV n θ ^ σ' := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
      simp only
      rw [one_mul, Real.div_rpow (circV_nonneg n θ) hMpos.le, Real.rpow_neg hMpos.le]
      ring
    have h2 : ((∫ θ in circBox n, circV n θ ^ σ' : ℝ) : ℂ) =
        ∫ θ in circBox n, circIntegrand n σ' θ := by
      rw [← integral_complex_ofReal]
      simp_rw [circIntegrand_ofReal]
    have h3 := hpos σ' (by simpa using hσ')
    unfold circInt at h3
    have h2π : (2 * π : ℂ) ^ (n : ℂ) ≠ 0 := by
      rw [Complex.cpow_natCast]; exact pow_ne_zero _ (by simp [Real.pi_ne_zero])
    rw [h1, Complex.ofReal_mul, h2, Complex.ofReal_cpow hMpos.le, hR]
    simp only
    rw [← h3]
    push_cast
    field_simp
  have hY : ∀ᵐ θ ∂(volume.restrict (circBox n)),
      0 < (fun θ => circV n θ / M) θ ∧ (fun θ => circV n θ / M) θ ≤ 1 := by
    filter_upwards [ae_circBox_good n] with θ hθ
    exact ⟨div_pos (circV_pos hθ) hMpos, (div_le_one hMpos).mpr (circV_le n θ)⟩
  have hlan := DLMF.Selberg.integrable_mul_rpow_of_analytic (μ := volume.restrict (circBox n))
    (W := fun _ => (1 : ℝ)) (Y := fun θ => circV n θ / M) (integrable_const 1)
    (Eventually.of_forall fun _ => zero_le_one) ((measurable_circV n).div_const M).aemeasurable
    hY one_pos hRd heq (σ := σ) (by rw [neg_div] at hσ; linarith)
  have hfun : (fun θ => circV n θ ^ σ) =
      fun θ => M ^ σ * ((fun _ => (1 : ℝ)) θ * (fun θ => circV n θ / M) θ ^ σ) := by
    funext θ
    simp only
    rw [one_mul, Real.div_rpow (circV_nonneg n θ) hMpos.le]
    field_simp [(Real.rpow_pos_of_pos hMpos σ).ne']
  rw [hfun]
  exact hlan.const_mul _

/-- **Dyson's integral** (Morris), DLMF 5.14.7, via Good's constant-term identity at the
integers, Carlson's theorem, Landau's integrability theorem and analytic continuation. -/
theorem circInt_eq_circRHS {n : ℕ} (hn : 0 < n) {b : ℂ} (hb : (-1 / n : ℝ) < b.re) :
    circInt n b = circRHS n b := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hneg : (-1 / n : ℝ) < 0 := by
    have : (0 : ℝ) < 1 / n := by positivity
    rw [neg_div]; linarith
  have hdG := differentiableOn_circRHS hn
  have hpos : ∀ w : ℂ, 0 < w.re → circInt n w = circRHS n w :=
    fun w hw => circInt_eq_circRHS_of_re_pos hn hw
  have hint : ∀ σ : ℝ, (-1 / n : ℝ) < σ →
      IntegrableOn (fun θ => circV n θ ^ σ) (circBox n) := fun σ hσ =>
    integrableOn_circV_rpow hn hσ
  -- the identity theorem on the full domain
  have hdB := differentiableOn_circInt (s0 := -1 / n) hint
  have hU : IsOpen {b : ℂ | (-1 / n : ℝ) < b.re} := isOpen_lt continuous_const Complex.continuous_re
  refine (hdB.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hdG.analyticOnNhd hU)
    (convex_halfSpace_re_gt _).isPreconnected (z₀ := 1) (by simp; linarith) ?_ hb
  have hV : IsOpen {c : ℂ | 0 < c.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hV.mem_nhds (by simp : (1 : ℂ) ∈ {c : ℂ | 0 < c.re})] with c hc
  exact hpos c hc

/-- Dyson's circular integral, DLMF 5.14.7: the average over the torus of
`∏_{j<k} |e^{iθⱼ} - e^{iθₖ}|^(2b)` is `Γ(1 + bn) / Γ(1 + b)ⁿ`. -/
@[dlmf 5.14.E7]
theorem selberg_circular {n : ℕ} {b : ℂ} (hb : (-1 / n : ℝ) < b.re) :
    (1 / (2 * π : ℂ) ^ (n : ℂ)) *
        ∫ θ : Fin n → ℝ in Set.pi Set.univ fun _ => Set.Icc (-π) π,
          ∏ j : Fin n, ∏ k : Fin n,
            (if j.val < k.val then
              (‖Complex.exp (I * θ j) - Complex.exp (I * θ k)‖ : ℂ) ^ (2 * b)
            else 1) =
      Complex.Gamma (1 + b * n) / Complex.Gamma (1 + b) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hset : (Set.pi Set.univ fun _ => Set.Icc (-π) π : Set (Fin 0 → ℝ)) = Set.univ :=
      Set.eq_univ_of_forall fun t => fun i => i.elim0
    simp [hset, Measure.real, volume_pi]
  exact circInt_eq_circRHS hn hb

end DysonIntegral

end DLMF.Gamma

end
end
