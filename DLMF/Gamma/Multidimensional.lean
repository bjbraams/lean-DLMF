/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Selberg.Basic
public import DLMF.Gamma.Simplex.MvBetaIntegral
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Multidimensional integrals (DLMF §5.14)

The Selberg/Aomoto identities 5.14.4 are already in `DLMF.Selberg.Basic`.
Dirichlet's simplex integrals 5.14.1–5.14.2 follow from the solid-simplex evaluation of the
multivariate Beta function in `DLMF.Gamma.Simplex` (ported from lean-codes). The Laguerre and
Hermite forms 5.14.5–5.14.6 are limits of the Selberg integral, and Dyson's circular integral
5.14.7 follows from Good's proof of Dyson's constant-term identity and Carlson's theorem.
`Δ` is the Vandermonde product 5.14.3.
-/

@[expose] public section

open Complex MeasureTheory
open scoped Real

noncomputable section

namespace DLMF.Gamma

/-- Vandermonde product, DLMF 5.14.3. -/
@[dlmf 5.14.E3]
def vandermonde {n : ℕ} (t : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, if i.val < j.val then t i - t j else 1

/-- The open simplex `(0, ∞)ⁿ ∩ {∑ tᵢ ≤ 1}` agrees a.e. with the closed solid simplex. -/
theorem openSimplex_ae_eq_mvBetaSimplex (n : ℕ) :
    ((Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ)) ∩ {t : Fin n → ℝ | ∑ i, t i ≤ 1} :
      Set (Fin n → ℝ)) =ᵐ[volume] Simplex.Complex.mvBetaSimplex n := by
  have hN : ∀ᵐ x : Fin n → ℝ, ∀ i, x i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    refine measure_mono_null (fun x hx => ?_) ((volume_pi (ι := Fin n) (α := fun _ => ℝ)).symm ▸
      Measure.pi_hyperplane (fun _ : Fin n => (volume : Measure ℝ)) i 0)
    simpa using hx
  filter_upwards [hN] with x hx
  simp only [Simplex.Complex.mvBetaSimplex, eq_iff_iff]
  change x ∈ (Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ)) ∩ {t | ∑ i, t i ≤ 1} ↔
    (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1
  simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, Set.mem_Ioi, true_implies,
    Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨fun i => (h.1 i).le, h.2⟩,
    fun h => ⟨fun i => lt_of_le_of_ne (h.1 i) (hx i).symm, h.2⟩⟩

@[dlmf 5.14.E1]
theorem dirichlet_simplex {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, 0 < (z i).re) :
    ∫ t : Fin n → ℝ in
        (Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ)) ∩ {t | ∑ i, t i ≤ 1},
        ∏ i : Fin n, (t i : ℂ) ^ (z i - 1) =
      (∏ i : Fin n, Complex.Gamma (z i)) / Complex.Gamma (1 + ∑ i, z i) := by
  rw [setIntegral_congr_set (openSimplex_ae_eq_mvBetaSimplex n)]
  have h := Simplex.Complex.mvBetaIntegralOne_eq_mvBeta hz
  rw [Simplex.Complex.mvBetaIntegralOne, Simplex.Complex.mvBeta] at h
  rw [h, Fin.prod_univ_succ, Fin.sum_univ_succ]
  simp

@[dlmf 5.14.E2]
theorem dirichlet_simplex_full {n : ℕ} (z : Fin (n + 1) → ℂ)
    (hz : ∀ i, 0 < (z i).re) :
    ∫ t : Fin n → ℝ in
        (Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ)) ∩ {t | ∑ i, t i ≤ 1},
        (1 - ∑ i, (t i : ℂ)) ^ (z ⟨n, Nat.lt_succ_self n⟩ - 1) *
          ∏ i : Fin n, (t i : ℂ) ^ (z i.castSucc - 1) =
      (∏ i : Fin (n + 1), Complex.Gamma (z i)) / Complex.Gamma (∑ i, z i) := by
  rw [setIntegral_congr_set (openSimplex_ae_eq_mvBetaSimplex n)]
  have h := Simplex.Complex.mvBetaIntegral_eq_mvBeta (b₀ := z (Fin.last n))
    (b := fun i => z i.castSucc) (hz _) (fun i => hz _)
  rw [Simplex.Complex.mvBetaIntegral, Simplex.Complex.mvBeta] at h
  push_cast at h
  rw [show (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n from rfl, h,
    Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring_nf

section LaguerreLimit

/-! ### Laguerre–Selberg integral as a limit of Aomoto's integral

With `b = N + 1` and the substitution `t = x/N`, Aomoto's integral becomes an integral of
`(1 - x/N)^N`-weights over `(0, N]ⁿ`; dominated convergence gives the Laguerre integral, and
the Gamma-ratio asymptotics `Γ(N+p)/Γ(N+q) ~ N^{p-q}` give its value. -/

open Set Filter
open scoped Topology

/-! ### Scaling lemmas -/

theorem integral_pi_Ioc_scale {n : ℕ} (g : (Fin n → ℝ) → ℂ) {L : ℝ} (hL : 0 < L) :
    ∫ x in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) L), g x =
      (L : ℂ) ^ n * ∫ t in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1), g (L • t) := by
  have hmem : ∀ t : Fin n → ℝ, L • t ∈ Set.pi Set.univ (fun _ => Ioc (0 : ℝ) L) ↔
      t ∈ Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1) := by
    intro t
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioc, Pi.smul_apply, smul_eq_mul]
    refine forall_congr' fun i => ?_
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 hL.le, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos hL h1, by nlinarith⟩
  have h := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure (Fin n → ℝ)))
    ((Set.pi Set.univ (fun _ => Ioc (0 : ℝ) L)).indicator g) L
  rw [Module.finrank_fin_fun] at h
  have hind : (fun t : Fin n → ℝ => (Set.pi Set.univ (fun _ => Ioc (0 : ℝ) L)).indicator g
      (L • t)) = (Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1)).indicator (fun t => g (L • t)) := by
    ext t
    by_cases ht : t ∈ Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1)
    · rw [Set.indicator_of_mem ((hmem t).mpr ht), Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem (fun h => ht ((hmem t).mp h)), Set.indicator_of_notMem ht]
  rw [hind, integral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Ioc),
    integral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)] at h
  rw [h, abs_of_pos (inv_pos.mpr (pow_pos hL n)), Complex.real_smul]
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero n (by exact_mod_cast hL.ne')), one_mul]

/-! ### Power algebra -/

theorem ofReal_prod_cpow {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
    (w : ℂ) : ((∏ i ∈ s, f i : ℝ) : ℂ) ^ w = ∏ i ∈ s, ((f i : ℝ) : ℂ) ^ w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Complex.ofReal_mul,
      ← ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]
    exact Complex.mul_cpow_ofReal_nonneg (hf j (Finset.mem_insert_self j s))
      (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)) w

theorem ofReal_pow_cpow {x : ℝ} (hx : 0 < x) (k : ℕ) (w : ℂ) :
    ((x ^ k : ℝ) : ℂ) ^ w = (x : ℂ) ^ ((k : ℂ) * w) := by
  rw [Complex.ofReal_pow, ← Complex.cpow_natCast, ← Complex.cpow_mul]
  · rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_im]; linarith [Real.pi_pos]
  · rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_im]; linarith [Real.pi_pos]

theorem prod_ite_lt_const {n : ℕ} (x : ℝ) :
    ∏ i : Fin n, ∏ j : Fin n, (if i.val < j.val then x else 1) = x ^ (n * (n - 1) / 2) := by
  have hrow : ∀ i : Fin n, ∏ j : Fin n, (if i.val < j.val then x else 1) = x ^ (n - 1 - i.val) := by
    intro i
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    congr 1
    have h1 := Fin.card_filter_val_lt (n := n) (m := i.val + 1)
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun j : Fin n => i.val < j.val)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    have h3 : (Finset.univ.filter fun j : Fin n => ¬ i.val < j.val) =
        Finset.univ.filter fun j : Fin n => j.val < i.val + 1 := by
      ext j; simp
    rw [h3, h1] at h2
    have := i.isLt
    omega
  rw [Finset.prod_congr rfl fun i _ => hrow i, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) n, Finset.sum_range_reflect (fun i => i) n,
    Finset.sum_range_id]

theorem vandermonde_smul {n : ℕ} (L : ℝ) (t : Fin n → ℝ) :
    vandermonde (L • t) = L ^ (n * (n - 1) / 2) * vandermonde t := by
  unfold vandermonde
  rw [← prod_ite_lt_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> simp [Pi.smul_apply, smul_eq_mul, mul_sub]

theorem two_mul_pairs (n : ℕ) : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
  rw [← Finset.sum_range_id, mul_comm, Finset.sum_range_id_mul_two]

/-! ### The Laguerre integrand and its approximations -/

/-- The integrand of 5.14.5. -/
def lagIntegrand (n m : ℕ) (hm : m ≤ n) (a c : ℂ) (x : Fin n → ℝ) : ℂ :=
  (∏ i : Fin m, (x (Fin.castLE hm i) : ℂ)) *
    (∏ i : Fin n, (x i : ℂ) ^ (a - 1) * Complex.exp (-(x i : ℂ))) *
    ((|vandermonde x| : ℝ) : ℂ) ^ (2 * c)

/-- Its approximation with `(1 - x/N)^N` in place of `e^{-x}`. -/
def lagApprox (n m : ℕ) (hm : m ≤ n) (a c : ℂ) (N : ℕ) (x : Fin n → ℝ) : ℂ :=
  (∏ i : Fin m, (x (Fin.castLE hm i) : ℂ)) *
    (∏ i : Fin n, (x i : ℂ) ^ (a - 1) * (((1 - x i / N) ^ N : ℝ) : ℂ)) *
    ((|vandermonde x| : ℝ) : ℂ) ^ (2 * c)

theorem prod_ite_abs_cpow_eq {n : ℕ} (c : ℂ) (t : Fin n → ℝ) :
    (∏ i : Fin n, ∏ j : Fin n,
      if i.val < j.val then ((|t i - t j| : ℝ) : ℂ) ^ (2 * c) else 1) =
      ((|vandermonde t| : ℝ) : ℂ) ^ (2 * c) := by
  unfold vandermonde
  rw [Finset.abs_prod]
  simp_rw [Finset.abs_prod]
  rw [ofReal_prod_cpow _ _ (fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofReal_prod_cpow _ _ (fun j _ => abs_nonneg _)]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem lagApprox_smul {n m : ℕ} (hm : m ≤ n) (a c : ℂ) {N : ℕ} (hN : 0 < N)
    {t : Fin n → ℝ} (ht : ∀ i, 0 ≤ t i) :
    lagApprox n m hm a c N ((N : ℝ) • t) =
      (N : ℂ) ^ ((m : ℂ) + n * (a - 1) + ((n * (n - 1) : ℕ) : ℂ) * c) *
        (DLMF.Selberg.selbergIntegrand n a ((N : ℂ) + 1) c t *
          ∏ i : Fin m, (t (Fin.castLE hm i) : ℂ)) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold lagApprox DLMF.Selberg.selbergIntegrand
  rw [prod_ite_abs_cpow_eq, vandermonde_smul, abs_mul, abs_pow, abs_of_pos hNpos,
    Complex.ofReal_mul (_ ^ _), Complex.mul_cpow_ofReal_nonneg (by positivity) (abs_nonneg _),
    ofReal_pow_cpow hNpos]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_natCast]
  have h1 : ∏ i : Fin m, ((N : ℂ) * (t (Fin.castLE hm i) : ℂ)) =
      (N : ℂ) ^ m * ∏ i : Fin m, (t (Fin.castLE hm i) : ℂ) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h2 : ∏ i : Fin n, ((N : ℂ) * (t i : ℂ)) ^ (a - 1) * (((1 - N * t i / N) ^ N : ℝ) : ℂ) =
      ((N : ℂ) ^ (a - 1)) ^ n *
        ∏ i : Fin n, (t i : ℂ) ^ (a - 1) * (1 - (t i : ℂ)) ^ ((N : ℂ) + 1 - 1) := by
    rw [show ((N : ℂ) ^ (a - 1)) ^ n = ∏ _i : Fin n, (N : ℂ) ^ (a - 1) by simp,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hmul : ((N : ℂ) * (t i : ℂ)) ^ (a - 1) = (N : ℂ) ^ (a - 1) * (t i : ℂ) ^ (a - 1) := by
      have := Complex.mul_cpow_ofReal_nonneg hNpos.le (ht i) (a - 1)
      simpa using this
    rw [hmul, mul_div_cancel_left₀ _ hN0, add_sub_cancel_right, Complex.cpow_natCast]
    push_cast
    ring
  rw [h1, h2]
  have hexp : (N : ℂ) ^ m * ((N : ℂ) ^ (a - 1)) ^ n *
      (N : ℂ) ^ (((n * (n - 1) / 2 : ℕ) : ℂ) * (2 * c)) =
      (N : ℂ) ^ ((m : ℂ) + n * (a - 1) + ((n * (n - 1) : ℕ) : ℂ) * c) := by
    rw [Complex.cpow_add _ _ hNC, Complex.cpow_add _ _ hNC, ← Complex.cpow_nat_mul,
      Complex.cpow_natCast]
    congr 2
    rw [show ((n * (n - 1) : ℕ) : ℂ) = 2 * ((n * (n - 1) / 2 : ℕ) : ℂ) by
      have := two_mul_pairs n
      exact_mod_cast this.symm]
    ring
  rw [← hexp]
  ring

theorem integral_lagApprox_eq {n m : ℕ} (hm : m ≤ n) {a c : ℂ} (ha : 0 < a.re) (hc : 0 < c.re)
    {N : ℕ} (hN : 0 < N) :
    ∫ x in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) N), lagApprox n m hm a c N x =
      (N : ℂ) ^ n * (N : ℂ) ^ ((m : ℂ) + n * (a - 1) + ((n * (n - 1) : ℕ) : ℂ) * c) *
        ((∏ j : Fin m, (a + (n - 1 - j : ℕ) * c) / (a + ((N : ℂ) + 1) + (2 * n - 2 - j : ℕ) * c)) *
          ∏ j : Fin n, Gamma (a + (j : ℕ) * c) * Gamma (((N : ℂ) + 1) + (j : ℕ) * c) *
            Gamma (1 + ((j : ℕ) + 1) * c) /
            (Gamma (a + ((N : ℂ) + 1) + (n + j - 1 : ℕ) * c) * Gamma (1 + c))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : 0 < ((N : ℂ) + 1).re := by simp; positivity
  rw [integral_pi_Ioc_scale _ hNpos, mul_assoc,
    ← DLMF.Selberg.aomoto_integral hm ha hb hc, Complex.ofReal_natCast]
  congr 1
  have hae : (Set.pi Set.univ fun _ => Ioc (0 : ℝ) 1 : Set (Fin n → ℝ)) =ᵐ[volume]
      (Set.pi Set.univ fun _ => Icc (0 : ℝ) 1) := by
    rw [volume_pi]
    have := Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin n => (volume : Measure ℝ))
      (f := fun _ => (0 : ℝ)) (g := fun _ => (1 : ℝ))
    rwa [← Set.pi_univ_Icc] at this
  rw [← setIntegral_congr_set hae, ← integral_const_mul]
  · refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) fun t ht => ?_
    exact lagApprox_smul hm a c hN fun i => (ht i (Set.mem_univ _)).1.le
/-! ### Domination -/

theorem abs_vandermonde_le {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    |vandermonde x| ≤ (∏ i, (1 + x i)) ^ (2 * n) := by
  unfold vandermonde
  rw [Finset.abs_prod]
  have hstep : ∀ i j : Fin n, |if i.val < j.val then x i - x j else 1| ≤ (1 + x i) * (1 + x j) := by
    intro i j
    have hi := hx i
    have hj := hx j
    split_ifs
    · rw [abs_le]; constructor <;> nlinarith
    · simp; nlinarith
  calc ∏ i, |∏ j, if i.val < j.val then x i - x j else 1|
      = ∏ i, ∏ j, |if i.val < j.val then x i - x j else 1| := by simp_rw [Finset.abs_prod]
    _ ≤ ∏ i : Fin n, ∏ j : Fin n, ((1 + x i) * (1 + x j)) := by
        refine Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _)
          fun i _ => Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => hstep i j
    _ = (∏ i, (1 + x i)) ^ (2 * n) := by
        simp_rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [Finset.prod_pow, two_mul, pow_add]

theorem prod_castLE_le {n m : ℕ} (hm : m ≤ n) {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    ∏ i : Fin m, x (Fin.castLE hm i) ≤ ∏ i, (1 + x i) := by
  calc ∏ i : Fin m, x (Fin.castLE hm i) ≤ ∏ i : Fin m, (1 + x (Fin.castLE hm i)) :=
        Finset.prod_le_prod₀ (fun i _ => hx _) fun i _ => by linarith [hx (Fin.castLE hm i)]
    _ = ∏ i ∈ Finset.univ.map (Fin.castLEEmb hm), (1 + x i) := by rw [Finset.prod_map]; rfl
    _ ≤ ∏ i, (1 + x i) :=
        Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
          (fun i _ => by linarith [hx i]) fun i _ _ => by linarith [hx i]

/-- The one-variable majorant `y^{α-1} e^{-y} (1+y)^M`. -/
def lagMajor (α M : ℝ) (y : ℝ) : ℝ := y ^ (α - 1) * Real.exp (-y) * (1 + y) ^ M

theorem integrableOn_lagMajor {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M) :
    IntegrableOn (lagMajor α M) (Ioi 0) := by
  have h1 := Real.GammaIntegral_convergent hα
  have h2 := Real.GammaIntegral_convergent (show 0 < α + M by linarith)
  refine ((h1.add h2).const_mul (2 ^ M)).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    unfold lagMajor
    refine ContinuousOn.mul (ContinuousOn.mul ?_ (by fun_prop)) ?_
    · exact ContinuousOn.rpow_const continuousOn_id fun y hy => Or.inl (ne_of_gt hy)
    · exact ContinuousOn.rpow_const (by fun_prop) fun y hy =>
        Or.inl (by have : (0 : ℝ) < y := hy; positivity)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun y (hy : 0 < y) => ?_
    unfold lagMajor
    have hb : (1 + y) ^ M ≤ 2 ^ M * (1 + y ^ M) := by
      rcases le_total y 1 with hy1 | hy1
      · calc (1 + y) ^ M ≤ 2 ^ M := Real.rpow_le_rpow (by positivity) (by linarith) hM
          _ ≤ 2 ^ M * (1 + y ^ M) := le_mul_of_one_le_right (by positivity)
              (by linarith [Real.rpow_nonneg hy.le M])
      · calc (1 + y) ^ M ≤ (2 * y) ^ M := Real.rpow_le_rpow (by positivity) (by linarith) hM
          _ = 2 ^ M * y ^ M := Real.mul_rpow (by norm_num) hy.le
          _ ≤ 2 ^ M * (1 + y ^ M) := by gcongr; linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc y ^ (α - 1) * Real.exp (-y) * (1 + y) ^ M
        ≤ y ^ (α - 1) * Real.exp (-y) * (2 ^ M * (1 + y ^ M)) := by gcongr
      _ = 2 ^ M * (Real.exp (-y) * y ^ (α - 1) + Real.exp (-y) * y ^ (α + M - 1)) := by
          rw [show α + M - 1 = (α - 1) + M by ring, Real.rpow_add hy]
          ring

theorem integrableOn_prod_lagMajor {n : ℕ} {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M) :
    IntegrableOn (fun x : Fin n → ℝ => ∏ i, lagMajor α M (x i))
      (Set.pi Set.univ fun _ => Ioi (0 : ℝ)) := by
  rw [IntegrableOn, volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod (fun _ => integrableOn_lagMajor hα hM)

theorem norm_lagApprox_le {n m : ℕ} (hm : m ≤ n) {a c : ℂ} (hc : 0 < c.re) {N : ℕ}
    {x : Fin n → ℝ} (hx : ∀ i, x i ∈ Ioc (0 : ℝ) N) :
    ‖lagApprox n m hm a c N x‖ ≤ ∏ i, lagMajor a.re (1 + 4 * n * c.re) (x i) := by
  have hx0 : ∀ i, 0 ≤ x i := fun i => (hx i).1.le
  set P := ∏ i, (1 + x i) with hP
  have hP1 : 1 ≤ P := Finset.one_le_prod₀ fun i _ => by linarith [hx0 i]
  have hP0 : 0 < P := by linarith
  unfold lagApprox
  rw [norm_mul, norm_mul, norm_prod, norm_prod,
    Complex.norm_cpow_eq_rpow_re_of_nonneg (abs_nonneg _) (by simp; linarith)]
  have h1 : ∏ i : Fin m, ‖(x (Fin.castLE hm i) : ℂ)‖ ≤ P := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hx0 _)]
    exact prod_castLE_le hm hx0
  have h2 : ∏ i : Fin n, ‖(x i : ℂ) ^ (a - 1) * (((1 - x i / N) ^ N : ℝ) : ℂ)‖ ≤
      ∏ i : Fin n, (x i ^ (a.re - 1) * Real.exp (-x i)) := by
    refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
    have hxN : x i ≤ N := (hx i).2
    have hN : (0 : ℝ) < N := lt_of_lt_of_le (hx i).1 hxN
    have hq : 0 ≤ 1 - x i / N := by rw [sub_nonneg, div_le_one hN]; exact hxN
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hx i).1, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq N)]
    simp only [Complex.sub_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left (Real.one_sub_div_pow_le_exp_neg hxN)
      (Real.rpow_nonneg (hx0 i) _)
  have h3 : |vandermonde x| ^ (2 * c).re ≤ P ^ (4 * n * c.re) := by
    have hre : (2 * c).re = 2 * c.re := by simp
    rw [hre]
    calc |vandermonde x| ^ (2 * c.re) ≤ (P ^ (2 * n)) ^ (2 * c.re) :=
          Real.rpow_le_rpow (abs_nonneg _) (abs_vandermonde_le hx0) (by linarith)
      _ = P ^ (4 * n * c.re) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]; push_cast; ring_nf
  calc (∏ i : Fin m, ‖(x (Fin.castLE hm i) : ℂ)‖) *
        (∏ i : Fin n, ‖(x i : ℂ) ^ (a - 1) * (((1 - x i / N) ^ N : ℝ) : ℂ)‖) *
        |vandermonde x| ^ (2 * c).re
      ≤ P * (∏ i : Fin n, (x i ^ (a.re - 1) * Real.exp (-x i))) * P ^ (4 * n * c.re) := by
        gcongr
        exact mul_nonneg hP0.le (Finset.prod_nonneg fun i _ =>
          mul_nonneg (Real.rpow_nonneg (hx0 i) _) (Real.exp_pos _).le)
    _ = (∏ i : Fin n, (x i ^ (a.re - 1) * Real.exp (-x i))) * P ^ (1 + 4 * n * c.re) := by
        rw [Real.rpow_add hP0, Real.rpow_one]; ring
    _ = ∏ i, lagMajor a.re (1 + 4 * n * c.re) (x i) := by
        rw [hP, ← Real.finsetProd_rpow _ _ fun i _ => by linarith [hx0 i],
          ← Finset.prod_mul_distrib]
        rfl

theorem measurable_lagApprox (n m : ℕ) (hm : m ≤ n) (a c : ℂ) (N : ℕ) :
    Measurable (lagApprox n m hm a c N) := by
  unfold lagApprox vandermonde
  fun_prop

theorem tendsto_lagApprox {n m : ℕ} (hm : m ≤ n) (a c : ℂ) (x : Fin n → ℝ) :
    Tendsto (fun N : ℕ => lagApprox n m hm a c N x) atTop (𝓝 (lagIntegrand n m hm a c x)) := by
  unfold lagApprox lagIntegrand
  refine (tendsto_const_nhds.mul (tendsto_finsetProd _ fun i _ => ?_)).mul tendsto_const_nhds
  refine tendsto_const_nhds.mul ?_
  have h := Real.tendsto_one_add_div_pow_exp (-x i)
  have h2 := (Complex.continuous_ofReal.tendsto _).comp h
  rw [Complex.ofReal_exp, Complex.ofReal_neg] at h2
  refine h2.congr fun N => ?_
  simp [neg_div, sub_eq_add_neg]

theorem tendsto_integral_lagApprox {n m : ℕ} (hm : m ≤ n) {a c : ℂ} (ha : 0 < a.re)
    (hc : 0 < c.re) :
    Tendsto (fun N : ℕ => ∫ x in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) N),
        lagApprox n m hm a c N x) atTop
      (𝓝 (∫ x in Set.pi Set.univ (fun _ => Ioi (0 : ℝ)), lagIntegrand n m hm a c x)) := by
  have hsub : ∀ N : ℕ, (Set.pi Set.univ (fun _ => Ioc (0 : ℝ) N) : Set (Fin n → ℝ)) ⊆
      Set.pi Set.univ (fun _ => Ioi (0 : ℝ)) :=
    fun N x hx i hi => (hx i hi).1
  have hrw : ∀ N : ℕ, ∫ x in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) N), lagApprox n m hm a c N x =
      ∫ x in Set.pi Set.univ (fun _ => Ioi (0 : ℝ)),
        (Set.pi Set.univ (fun _ => Ioc (0 : ℝ) N)).indicator (lagApprox n m hm a c N) x := by
    intro N
    rw [setIntegral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Ioc),
      Set.inter_eq_right.mpr (hsub N)]
  simp_rw [hrw]
  have hM : (0 : ℝ) ≤ 1 + 4 * n * c.re := by positivity
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => ∏ i, lagMajor a.re (1 + 4 * n * c.re) (x i))
    (Eventually.of_forall fun N => ((measurable_lagApprox n m hm a c N).indicator
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)).aestronglyMeasurable)
    (Eventually.of_forall fun N => ?_) (integrableOn_prod_lagMajor ha hM) ?_
  · rw [ae_restrict_iff' (MeasurableSet.univ_pi fun _ => measurableSet_Ioi)]
    refine Eventually.of_forall fun x hx => ?_
    by_cases hxN : x ∈ Set.pi Set.univ (fun _ => Ioc (0 : ℝ) N)
    · rw [Set.indicator_of_mem hxN]
      exact norm_lagApprox_le hm hc fun i => hxN i (Set.mem_univ _)
    · rw [Set.indicator_of_notMem hxN, norm_zero]
      refine Finset.prod_nonneg fun i _ => ?_
      have := hx i (Set.mem_univ _)
      unfold lagMajor
      have : (0 : ℝ) < x i := this
      positivity
  · rw [ae_restrict_iff' (MeasurableSet.univ_pi fun _ => measurableSet_Ioi)]
    refine Eventually.of_forall fun x hx => ?_
    have hev : ∀ᶠ N : ℕ in atTop, x ∈ Set.pi Set.univ (fun _ => Ioc (0 : ℝ) N) := by
      have : ∀ i, ∀ᶠ N : ℕ in atTop, x i ≤ N := fun i =>
        tendsto_natCast_atTop_atTop.eventually_ge_atTop (x i)
      filter_upwards [Filter.eventually_all.2 this] with N hN i _
      exact ⟨hx i (Set.mem_univ _), hN i⟩
    refine (tendsto_lagApprox hm a c x).congr' ?_
    filter_upwards [hev] with N hN
    rw [Set.indicator_of_mem hN]

/-! ### The limit of the right-hand side -/

theorem tendsto_natCast_div_add (β : ℂ) :
    Tendsto (fun N : ℕ => (N : ℂ) / (N + β)) atTop (𝓝 1) := by
  have h0 : Tendsto (fun N : ℕ => β / (N : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_div, Complex.norm_natCast]
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun N : ℕ => ((N + β) / (N : ℂ))⁻¹) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℂ))).add h0
    rw [add_zero] at this
    have h2 := this.inv₀ one_ne_zero
    rw [inv_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with N hN
    have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    rw [add_div, div_self this]
  refine h1.congr fun N => ?_
  rw [inv_div]

theorem tendsto_Gamma_ratio_nat (p q : ℂ) :
    Tendsto (fun N : ℕ => Gamma (N + p) / Gamma (N + q) * (N : ℂ) ^ (q - p)) atTop (𝓝 1) := by
  have h := (Gamma_ratio_power (a := p) (b := q)).comp tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  simp only [Function.comp_apply, Complex.ofReal_natCast]
  rw [div_eq_mul_inv _ ((N : ℂ) ^ (p - q)), ← Complex.cpow_neg, neg_sub]

theorem tendsto_lag_rhs {n m : ℕ} (hn : 0 < n) {a c : ℂ} :
    Tendsto (fun N : ℕ =>
      (N : ℂ) ^ n * (N : ℂ) ^ ((m : ℂ) + n * (a - 1) + ((n * (n - 1) : ℕ) : ℂ) * c) *
        ((∏ j : Fin m, (a + (n - 1 - j : ℕ) * c) / (a + ((N : ℂ) + 1) + (2 * n - 2 - j : ℕ) * c)) *
          ∏ j : Fin n, Gamma (a + (j : ℕ) * c) * Gamma (((N : ℂ) + 1) + (j : ℕ) * c) *
            Gamma (1 + ((j : ℕ) + 1) * c) /
            (Gamma (a + ((N : ℂ) + 1) + (n + j - 1 : ℕ) * c) * Gamma (1 + c)))) atTop
      (𝓝 ((∏ j : Fin m, (a + (n - 1 - j : ℕ) * c)) *
        ∏ j : Fin n, (Gamma (a + (j : ℕ) * c) * Gamma (1 + ((j : ℕ) + 1) * c) /
          Gamma (1 + c)))) := by
  set w : ℂ := a + ((n - 1 : ℕ) : ℂ) * c with hw
  have hlim : Tendsto (fun N : ℕ =>
      (∏ j : Fin m, (a + (n - 1 - j : ℕ) * c) *
        ((N : ℂ) / (N + (a + 1 + (2 * n - 2 - j : ℕ) * c)))) *
      ∏ j : Fin n, (Gamma (a + (j : ℕ) * c) * Gamma (1 + ((j : ℕ) + 1) * c) / Gamma (1 + c) *
        (Gamma (N + (1 + (j : ℕ) * c)) / Gamma (N + (a + 1 + (n + j - 1 : ℕ) * c)) *
          (N : ℂ) ^ ((a + 1 + (n + j - 1 : ℕ) * c) - (1 + (j : ℕ) * c))))) atTop
      (𝓝 ((∏ j : Fin m, (a + (n - 1 - j : ℕ) * c)) *
        ∏ j : Fin n, (Gamma (a + (j : ℕ) * c) * Gamma (1 + ((j : ℕ) + 1) * c) /
          Gamma (1 + c)))) := by
    refine Tendsto.mul ?_ ?_
    · have := tendsto_finsetProd (Finset.univ : Finset (Fin m)) fun j _ =>
        (tendsto_const_nhds (x := a + ((n - 1 - j : ℕ) : ℂ) * c)).mul
          (tendsto_natCast_div_add (a + 1 + ((2 * n - 2 - j : ℕ) : ℂ) * c))
      simpa using this
    · have := tendsto_finsetProd (Finset.univ : Finset (Fin n)) fun j _ =>
        (tendsto_const_nhds (x := Gamma (a + ((j : ℕ) : ℂ) * c) *
          Gamma (1 + (((j : ℕ) : ℂ) + 1) * c) / Gamma (1 + c))).mul
          (tendsto_Gamma_ratio_nat (1 + ((j : ℕ) : ℂ) * c)
            (a + 1 + ((n + j - 1 : ℕ) : ℂ) * c))
      simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hexp : ∀ j : Fin n, (a + 1 + ((n + j - 1 : ℕ) : ℂ) * c) - (1 + ((j : ℕ) : ℂ) * c) = w := by
    intro j
    rw [hw, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  simp_rw [hexp]
  -- regroup the powers of `N`
  have hpow : (N : ℂ) ^ n * (N : ℂ) ^ ((m : ℂ) + n * (a - 1) + ((n * (n - 1) : ℕ) : ℂ) * c) =
      (∏ _j : Fin m, (N : ℂ)) * ∏ _j : Fin n, (N : ℂ) ^ w := by
    rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.card_univ, Fintype.card_fin, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast,
      ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hN', ← Complex.cpow_add _ _ hN']
    congr 1
    rw [hw, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast; ring
  rw [hpow]
  rw [show ∀ (A B C D : ℂ), A * B * (C * D) = (A * C) * (B * D) from fun A B C D => by ring,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    field_simp
    ring_nf
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [show ((N : ℂ) + 1) + ((j : ℕ) : ℂ) * c = N + (1 + ((j : ℕ) : ℂ) * c) by ring,
      show a + ((N : ℂ) + 1) + ((n + j - 1 : ℕ) : ℂ) * c =
        N + (a + 1 + ((n + j - 1 : ℕ) : ℂ) * c) by ring]
    ring

lemma selberg_laguerrePolyL_aux {n m : ℕ} {a c : ℂ} (hm : m ≤ n)
    (ha : 0 < a.re) (hc : 0 < c.re) :
    ∫ t : Fin n → ℝ in Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ),
        (∏ i : Fin m, (t (Fin.castLE hm i) : ℂ)) *
          (∏ i : Fin n, (t i : ℂ) ^ (a - 1) * Complex.exp (-(t i : ℂ))) *
          ((|vandermonde t| : ℝ) : ℂ) ^ (2 * c) =
      (∏ k : Fin m, (a + (n - 1 - k : ℕ) * c)) *
        (∏ k : Fin n, Complex.Gamma (a + (n - 1 - k : ℕ) * c) *
          Complex.Gamma (1 + ((k : ℕ) + 1) * c)) /
        Complex.Gamma (1 + c) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : m = 0 := Nat.le_zero.mp hm
    have hset : (Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ) : Set (Fin 0 → ℝ)) = Set.univ :=
      Set.eq_univ_of_forall fun t => fun i => i.elim0
    rw [hset, Measure.restrict_univ]
    simp [vandermonde, Measure.real, volume_pi]
  have hlim := tendsto_integral_lagApprox hm ha hc
  have hrhs := tendsto_lag_rhs (m := m) (a := a) (c := c) hn
  have hrhs' := hrhs.congr' (by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (integral_lagApprox_eq hm ha hc hN).symm)
  have hJ := tendsto_nhds_unique hlim hrhs'
  change ∫ t in _, lagIntegrand n m hm a c t = _
  rw [hJ]
  have hrefl : ∏ k : Fin n, Complex.Gamma (a + (n - 1 - k : ℕ) * c) =
      ∏ k : Fin n, Complex.Gamma (a + (k : ℕ) * c) := by
    rw [Fin.prod_univ_eq_prod_range (fun k => Complex.Gamma (a + (n - 1 - k : ℕ) * c)) n,
      Fin.prod_univ_eq_prod_range (fun k => Complex.Gamma (a + (k : ℕ) * c)) n]
    exact Finset.prod_range_reflect (fun k => Complex.Gamma (a + (k : ℕ) * c)) n
  rw [Finset.prod_mul_distrib, hrefl, Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

end LaguerreLimit

section HermiteLimit

/-! ### Mehta's integral as a limit of Selberg's integral

With `a = b = N + 1` and the affine substitution `x = 2√(2N) t - √(2N)`, Selberg's integral
becomes an integral of `(1 - x²/(2N))^N`-weights over `[-√(2N), √(2N)]ⁿ`. Integrability of the
limit integrand on the full domain `Re c > -1/n` follows from Fatou's lemma, since for real `c`
the approximating integrals are nonnegative and converge; dominated convergence then gives
the value, with the duplication formula for the right-hand side. -/

open Set Filter
open scoped Topology

/-! ### Affine change of variables on a cube -/

theorem integral_pi_Icc_affine {n : ℕ} (g : (Fin n → ℝ) → ℂ) {s : ℝ} (hs : 0 < s) :
    ∫ x in Set.pi Set.univ (fun _ => Icc (-s) s), g x =
      ((2 * s : ℝ) : ℂ) ^ n *
        ∫ t in Set.pi Set.univ (fun _ => Icc (0 : ℝ) 1), g (fun i => 2 * s * t i - s) := by
  set S := (Set.pi Set.univ (fun _ => Icc (-s) s) : Set (Fin n → ℝ)) with hS
  set T := (Set.pi Set.univ (fun _ => Icc (0 : ℝ) 1) : Set (Fin n → ℝ)) with hT
  have hL : (0 : ℝ) < 2 * s := by positivity
  set v : Fin n → ℝ := fun _ => -s with hv
  have hmem : ∀ t : Fin n → ℝ, (2 * s) • t + v ∈ S ↔ t ∈ T := by
    intro t
    simp only [hS, hT, hv, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    refine forall_congr' fun i => ?_
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · nlinarith
      · nlinarith
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
  set F := S.indicator g with hF
  have h1 := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure (Fin n → ℝ)))
    (fun y => F (y + v)) (2 * s)
  rw [Module.finrank_fin_fun, integral_add_right_eq_self (fun y => F y) v] at h1
  have hind : (fun t : Fin n → ℝ => F ((2 * s) • t + v)) =
      T.indicator (fun t => g (fun i => 2 * s * t i - s)) := by
    ext t
    by_cases ht : t ∈ T
    · rw [hF, Set.indicator_of_mem ((hmem t).mpr ht), Set.indicator_of_mem ht]
      congr 1
    · rw [hF, Set.indicator_of_notMem (fun h => ht ((hmem t).mp h)), Set.indicator_of_notMem ht]
  rw [hind, integral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Icc), hF,
    integral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Icc)] at h1
  rw [h1, abs_of_pos (inv_pos.mpr (pow_pos hL n)), Complex.real_smul]
  push_cast
  have h2 : (2 : ℂ) * (s : ℂ) ≠ 0 := by
    have : ((2 * s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    simpa using this
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero n h2), one_mul]

/-! ### The Hermite integrand and its approximations -/

/-- The integrand of 5.14.6. -/
def hermIntegrand (n : ℕ) (c : ℂ) (x : Fin n → ℝ) : ℂ :=
  ((|vandermonde x| : ℝ) : ℂ) ^ (2 * c) * ∏ k : Fin n, Complex.exp (-(x k : ℂ) ^ 2 / 2)

/-- Its approximation with `(1 - x²/(2N))^N` in place of `e^{-x²/2}`. -/
def hermApprox (n : ℕ) (c : ℂ) (N : ℕ) (x : Fin n → ℝ) : ℂ :=
  ((|vandermonde x| : ℝ) : ℂ) ^ (2 * c) * ∏ k : Fin n, (((1 - x k ^ 2 / (2 * N)) ^ N : ℝ) : ℂ)

theorem vandermonde_affine {n : ℕ} (L v : ℝ) (t : Fin n → ℝ) :
    vandermonde (fun i => L * t i - v) = L ^ (n * (n - 1) / 2) * vandermonde t := by
  rw [← vandermonde_smul]
  unfold vandermonde
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  split_ifs
  · simp [Pi.smul_apply, smul_eq_mul]
  · rfl

theorem hermApprox_affine {n : ℕ} (c : ℂ) {N : ℕ} (hN : 0 < N) (t : Fin n → ℝ) :
    hermApprox n c N (fun i => 2 * √(2 * N) * t i - √(2 * N)) =
      (4 : ℂ) ^ (n * N) * ((2 * √(2 * N) : ℝ) : ℂ) ^ (((n * (n - 1) : ℕ) : ℂ) * c) *
        DLMF.Selberg.selbergIntegrand n ((N : ℂ) + 1) ((N : ℂ) + 1) c t := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set s := √(2 * N) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hss : s ^ 2 = 2 * N := Real.sq_sqrt (by positivity)
  have hL : (0 : ℝ) < 2 * s := by positivity
  unfold hermApprox DLMF.Selberg.selbergIntegrand
  rw [prod_ite_abs_cpow_eq, vandermonde_affine, abs_mul, abs_pow, abs_of_pos hL,
    Complex.ofReal_mul (_ ^ _), Complex.mul_cpow_ofReal_nonneg (by positivity) (abs_nonneg _),
    ofReal_pow_cpow hL]
  have hfac : ∀ i : Fin n, (((1 - (2 * s * t i - s) ^ 2 / (2 * N)) ^ N : ℝ) : ℂ) =
      4 ^ N * ((t i : ℂ) ^ ((N : ℂ) + 1 - 1) * (1 - (t i : ℂ)) ^ ((N : ℂ) + 1 - 1)) := by
    intro i
    have h1 : 1 - (2 * s * t i - s) ^ 2 / (2 * N) = 4 * (t i * (1 - t i)) := by
      have : (2 * s * t i - s) ^ 2 = s ^ 2 * (2 * t i - 1) ^ 2 := by ring
      rw [this, hss]
      field_simp
      ring
    rw [h1, add_sub_cancel_right, Complex.cpow_natCast, Complex.cpow_natCast, ← mul_pow,
      ← mul_pow]
    push_cast
    ring
  rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hexp : ((2 * s : ℝ) : ℂ) ^ (((n * (n - 1) / 2 : ℕ) : ℂ) * (2 * c)) =
      ((2 * s : ℝ) : ℂ) ^ (((n * (n - 1) : ℕ) : ℂ) * c) := by
    congr 1
    rw [show ((n * (n - 1) : ℕ) : ℂ) = 2 * ((n * (n - 1) / 2 : ℕ) : ℂ) by
      have := two_mul_pairs n
      exact_mod_cast this.symm]
    ring
  rw [hexp]
  ring

theorem integral_hermApprox_eq {n : ℕ} {c : ℂ} {N : ℕ}
    (hc : c ∈ DLMF.Selberg.cDomain n ((N : ℂ) + 1) ((N : ℂ) + 1)) (hN : 0 < N) :
    ∫ x in Set.pi Set.univ (fun _ => Icc (-√(2 * N)) √(2 * N)), hermApprox n c N x =
      ((2 * √(2 * N) : ℝ) : ℂ) ^ n * ((4 : ℂ) ^ (n * N) *
        ((2 * √(2 * N) : ℝ) : ℂ) ^ (((n * (n - 1) : ℕ) : ℂ) * c) *
          DLMF.Selberg.selbergRHS n ((N : ℂ) + 1) ((N : ℂ) + 1) c) := by
  have hs0 : 0 < √(2 * N) := Real.sqrt_pos.mpr (by positivity)
  have hb : 0 < ((N : ℂ) + 1).re := by simp; positivity
  rw [integral_pi_Icc_affine _ hs0]
  congr 1
  simp_rw [hermApprox_affine c hN]
  rw [integral_const_mul]
  congr 1
  exact DLMF.Selberg.selbergInt_eq hb hb hc

theorem measurable_hermApprox (n : ℕ) (c : ℂ) (N : ℕ) : Measurable (hermApprox n c N) := by
  unfold hermApprox vandermonde
  fun_prop

theorem tendsto_hermApprox {n : ℕ} (c : ℂ) (x : Fin n → ℝ) :
    Tendsto (fun N : ℕ => hermApprox n c N x) atTop (𝓝 (hermIntegrand n c x)) := by
  unfold hermApprox hermIntegrand
  refine tendsto_const_nhds.mul (tendsto_finsetProd _ fun i _ => ?_)
  have h := Real.tendsto_one_add_div_pow_exp (-x i ^ 2 / 2)
  have h2 := (Complex.continuous_ofReal.tendsto _).comp h
  rw [Complex.ofReal_exp] at h2
  refine (h2.congr fun N => ?_).trans (le_of_eq ?_)
  · simp only [Function.comp_apply]
    congr 2
    ring
  · congr 2
    push_cast
    ring

/-! ### The limit of the right-hand side -/

theorem herm_ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (w : ℂ) :
    ((x : ℝ) : ℂ) ^ w = Complex.exp (w * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le,
    mul_comm]

theorem herm_ofReal_eq_exp {x : ℝ} (hx : 0 < x) : ((x : ℝ) : ℂ) = Complex.exp (Real.log x : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_log hx]

/-- One factor of the Hermite right-hand side, rewritten via the duplication formula. -/
theorem herm_factor_eq {n : ℕ} (hn : 0 < n) (c : ℂ) (j : ℕ) {N : ℕ} (hN : 0 < N) :
    ((2 * √(2 * N) : ℝ) : ℂ) ^ (1 + ((n - 1 : ℕ) : ℂ) * c) * (4 : ℂ) ^ N *
      (Gamma ((N : ℂ) + 1 + (j : ℂ) * c) * Gamma ((N : ℂ) + 1 + (j : ℂ) * c) *
        Gamma (1 + ((j : ℂ) + 1) * c) /
        (Gamma ((N : ℂ) + 1 + ((N : ℂ) + 1) + ((n + j - 1 : ℕ) : ℂ) * c) * Gamma (1 + c))) =
      ((√(2 * π) : ℝ) : ℂ) *
        Complex.exp (((j : ℂ) - ((n - 1 : ℕ) : ℂ) / 2) * c *
          ((Real.log N - Real.log 2 : ℝ) : ℂ)) *
        (Gamma (N + (1 + (j : ℂ) * c)) / Gamma (N + (1 + ((n + j - 1 : ℕ) : ℂ) * c / 2)) *
          (N : ℂ) ^ ((1 + ((n + j - 1 : ℕ) : ℂ) * c / 2) - (1 + (j : ℂ) * c))) *
        (Gamma (N + (1 + (j : ℂ) * c)) /
          Gamma (N + (1 + ((n + j - 1 : ℕ) : ℂ) * c / 2 + 1 / 2)) *
          (N : ℂ) ^ ((1 + ((n + j - 1 : ℕ) : ℂ) * c / 2 + 1 / 2) - (1 + (j : ℂ) * c))) *
        (Gamma (1 + ((j : ℂ) + 1) * c) / Gamma (1 + c)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set z : ℂ := N + (1 + ((n + j - 1 : ℕ) : ℂ) * c / 2) with hz
  have hdup := Complex.Gamma_mul_Gamma_add_half z
  have h2z : (N : ℂ) + 1 + ((N : ℂ) + 1) + ((n + j - 1 : ℕ) : ℂ) * c = 2 * z := by
    rw [hz]; ring
  have hzh : N + (1 + ((n + j - 1 : ℕ) : ℂ) * c / 2 + 1 / 2) = z + 1 / 2 := by rw [hz]; ring
  rw [h2z, hzh, show (N : ℂ) + 1 + (j : ℂ) * c = N + (1 + (j : ℂ) * c) by ring]
  have hpi : ((√π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h2pow : (2 : ℂ) ^ (1 - 2 * z) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; simp
  -- replace `Γ(2z)`
  have hG2 : Gamma (2 * z) = Gamma z * Gamma (z + 1 / 2) / ((2 : ℂ) ^ (1 - 2 * z) * √π) := by
    rw [hdup]; field_simp
  rw [hG2]
  have hs : (0 : ℝ) < 2 * √(2 * N) := by positivity
  have hl1 : Real.log (2 * √(2 * N)) = Real.log 2 + (Real.log 2 + Real.log N) / 2 := by
    rw [Real.log_mul (by norm_num) (Real.sqrt_pos.mpr (by positivity)).ne', Real.log_sqrt
      (by positivity), Real.log_mul (by norm_num) hNpos.ne']
  have hl2 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hl3 : Real.log √(2 * π) = (Real.log 2 + Real.log π) / 2 := by
    rw [Real.log_sqrt (by positivity), Real.log_mul (by norm_num) Real.pi_pos.ne']
  have hl4 : Real.log √π = Real.log π / 2 := Real.log_sqrt Real.pi_pos.le
  have hcast : ((n + j - 1 : ℕ) : ℂ) = n + j - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hcast' : ((n - 1 : ℕ) : ℂ) = n - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  -- the scalar identity
  have hpow : ((2 * √(2 * N) : ℝ) : ℂ) ^ (1 + ((n - 1 : ℕ) : ℂ) * c) * (4 : ℂ) ^ N *
      ((2 : ℂ) ^ (1 - 2 * z) * ((√π : ℝ) : ℂ)) =
      ((√(2 * π) : ℝ) : ℂ) *
        Complex.exp (((j : ℂ) - ((n - 1 : ℕ) : ℂ) / 2) * c *
          ((Real.log N - Real.log 2 : ℝ) : ℂ)) *
        ((N : ℂ) ^ ((1 + ((n + j - 1 : ℕ) : ℂ) * c / 2) - (1 + (j : ℂ) * c)) *
          (N : ℂ) ^ ((1 + ((n + j - 1 : ℕ) : ℂ) * c / 2 + 1 / 2) - (1 + (j : ℂ) * c))) := by
    have hN' : ((N : ℕ) : ℂ) = ((N : ℝ) : ℂ) := (Complex.ofReal_natCast N).symm
    rw [herm_ofReal_cpow_eq_exp hs, hN', herm_ofReal_cpow_eq_exp hNpos,
      herm_ofReal_cpow_eq_exp hNpos,
      show (4 : ℂ) ^ N = Complex.exp ((N : ℂ) * (Real.log 4 : ℂ)) by
        rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, ← Complex.cpow_natCast,
          herm_ofReal_cpow_eq_exp (by norm_num)],
      show (2 : ℂ) ^ (1 - 2 * z) = Complex.exp ((1 - 2 * z) * (Real.log 2 : ℂ)) by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, herm_ofReal_cpow_eq_exp (by norm_num)],
      herm_ofReal_eq_exp (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * π)),
      herm_ofReal_eq_exp (Real.sqrt_pos.mpr Real.pi_pos)]
    simp only [← Complex.exp_add]
    congr 1
    rw [hl1, hl2, hl3, hl4, hz, hcast, hcast']
    push_cast
    ring
  calc ((2 * √(2 * N) : ℝ) : ℂ) ^ (1 + ((n - 1 : ℕ) : ℂ) * c) * (4 : ℂ) ^ N *
        (Gamma (N + (1 + (j : ℂ) * c)) * Gamma (N + (1 + (j : ℂ) * c)) *
          Gamma (1 + ((j : ℂ) + 1) * c) /
          (Gamma z * Gamma (z + 1 / 2) / ((2 : ℂ) ^ (1 - 2 * z) * ((√π : ℝ) : ℂ)) *
            Gamma (1 + c)))
      = (((2 * √(2 * N) : ℝ) : ℂ) ^ (1 + ((n - 1 : ℕ) : ℂ) * c) * (4 : ℂ) ^ N *
          ((2 : ℂ) ^ (1 - 2 * z) * ((√π : ℝ) : ℂ))) *
          (Gamma (N + (1 + (j : ℂ) * c)) * Gamma (N + (1 + (j : ℂ) * c)) *
            Gamma (1 + ((j : ℂ) + 1) * c) / (Gamma z * Gamma (z + 1 / 2) * Gamma (1 + c))) := by
        simp only [div_eq_mul_inv, mul_inv, inv_inv]; ring
    _ = _ := by rw [hpow, hz]; simp only [div_eq_mul_inv, mul_inv]; ring

theorem sum_fin_sub_half (n : ℕ) :
    ∑ j : Fin n, ((j : ℕ) - ((n - 1 : ℕ) : ℂ) / 2) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range (fun j => ((j : ℕ) : ℂ)) n, ← Nat.cast_sum]
  have h := Finset.sum_range_id_mul_two n
  have h' : ((∑ i ∈ Finset.range n, i : ℕ) : ℂ) * 2 = n * ((n - 1 : ℕ) : ℂ) := by
    exact_mod_cast h
  rw [nsmul_eq_mul]
  linear_combination h' / 2

theorem tendsto_herm_rhs {n : ℕ} (hn : 0 < n) (c : ℂ) :
    Tendsto (fun N : ℕ => ((2 * √(2 * N) : ℝ) : ℂ) ^ n * ((4 : ℂ) ^ (n * N) *
        ((2 * √(2 * N) : ℝ) : ℂ) ^ (((n * (n - 1) : ℕ) : ℂ) * c) *
          DLMF.Selberg.selbergRHS n ((N : ℂ) + 1) ((N : ℂ) + 1) c)) atTop
      (𝓝 (∏ j : Fin n, (((√(2 * π) : ℝ) : ℂ) *
        (Gamma (1 + (((j : ℕ) : ℂ) + 1) * c) / Gamma (1 + c))))) := by
  have hlim : Tendsto (fun N : ℕ => ∏ j : Fin n, (((√(2 * π) : ℝ) : ℂ) *
      (Gamma (N + (1 + ((j : ℕ) : ℂ) * c)) / Gamma (N + (1 + ((n + j - 1 : ℕ) : ℂ) * c / 2)) *
        (N : ℂ) ^ ((1 + ((n + j - 1 : ℕ) : ℂ) * c / 2) - (1 + ((j : ℕ) : ℂ) * c))) *
      (Gamma (N + (1 + ((j : ℕ) : ℂ) * c)) /
        Gamma (N + (1 + ((n + j - 1 : ℕ) : ℂ) * c / 2 + 1 / 2)) *
        (N : ℂ) ^ ((1 + ((n + j - 1 : ℕ) : ℂ) * c / 2 + 1 / 2) - (1 + ((j : ℕ) : ℂ) * c))) *
      (Gamma (1 + (((j : ℕ) : ℂ) + 1) * c) / Gamma (1 + c)))) atTop
      (𝓝 (∏ j : Fin n, (((√(2 * π) : ℝ) : ℂ) *
        (Gamma (1 + (((j : ℕ) : ℂ) + 1) * c) / Gamma (1 + c))))) := by
    have := tendsto_finsetProd (Finset.univ : Finset (Fin n)) fun j _ =>
      (((tendsto_const_nhds (x := ((√(2 * π) : ℝ) : ℂ))).mul
        (tendsto_Gamma_ratio_nat (1 + ((j : ℕ) : ℂ) * c)
          (1 + ((n + j - 1 : ℕ) : ℂ) * c / 2))).mul
        (tendsto_Gamma_ratio_nat (1 + ((j : ℕ) : ℂ) * c)
          (1 + ((n + j - 1 : ℕ) : ℂ) * c / 2 + 1 / 2))).mul
        (tendsto_const_nhds (x := Gamma (1 + (((j : ℕ) : ℂ) + 1) * c) / Gamma (1 + c)))
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : (0 : ℝ) < 2 * √(2 * N) := by positivity
  have hsC : ((2 * √(2 * N) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  -- rewrite the left side as a product of the factors of `herm_factor_eq`
  have hsplit : ((2 * √(2 * N) : ℝ) : ℂ) ^ n * ((4 : ℂ) ^ (n * N) *
      ((2 * √(2 * N) : ℝ) : ℂ) ^ (((n * (n - 1) : ℕ) : ℂ) * c) *
        DLMF.Selberg.selbergRHS n ((N : ℂ) + 1) ((N : ℂ) + 1) c) =
      ∏ j : Fin n, (((2 * √(2 * N) : ℝ) : ℂ) ^ (1 + ((n - 1 : ℕ) : ℂ) * c) * (4 : ℂ) ^ N *
        (Gamma ((N : ℂ) + 1 + ((j : ℕ) : ℂ) * c) * Gamma ((N : ℂ) + 1 + ((j : ℕ) : ℂ) * c) *
          Gamma (1 + (((j : ℕ) : ℂ) + 1) * c) /
          (Gamma ((N : ℂ) + 1 + ((N : ℂ) + 1) + ((n + j - 1 : ℕ) : ℂ) * c) *
            Gamma (1 + c)))) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, DLMF.Selberg.selbergRHS, pow_mul]
    have hpw : ((2 * √(2 * N) : ℝ) : ℂ) ^ n *
        ((2 * √(2 * N) : ℝ) : ℂ) ^ (((n * (n - 1) : ℕ) : ℂ) * c) =
        (((2 * √(2 * N) : ℝ) : ℂ) ^ (1 + ((n - 1 : ℕ) : ℂ) * c)) ^ n := by
      rw [← Complex.cpow_nat_mul, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hsC]
      congr 1
      rw [Nat.cast_mul]
      ring
    rw [← hpw]
    ring
  rw [hsplit]
  have hf := fun j : ℕ => herm_factor_eq (n := n) hn c j hN
  simp only [hf]
  -- the exponential factors multiply to one
  have hexp : ∏ j : Fin n, Complex.exp ((((j : ℕ) : ℂ) - ((n - 1 : ℕ) : ℂ) / 2) * c *
      ((Real.log N - Real.log 2 : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_sum, ← Finset.sum_mul, ← Finset.sum_mul, sum_fin_sub_half n]
    simp
  rw [← one_mul (∏ j : Fin n, _), ← hexp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

/-! ### Integrability on the full domain -/

theorem neg_one_lt_mul_of_div_lt {n : ℕ} (hn : 0 < n) {σ : ℝ} (hσ : (-1 / n : ℝ) < σ) :
    -1 < n * σ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_lt_iff₀ hn'] at hσ
  linarith

theorem one_add_mul_pos {n : ℕ} (hn : 0 < n) {σ : ℝ} (hσ : (-1 / n : ℝ) < σ) {k : ℕ}
    (hk : k ≤ n) : 0 < 1 + k * σ := by
  have h := neg_one_lt_mul_of_div_lt hn hσ
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
  rcases le_or_gt 0 σ with h0 | h0
  · positivity
  · nlinarith

theorem mem_cDomain_herm {n : ℕ} (hn : 0 < n) {c : ℂ} (hc : (-1 / n : ℝ) < c.re) (N : ℕ) :
    c ∈ DLMF.Selberg.cDomain n ((N : ℂ) + 1) ((N : ℂ) + 1) := by
  have h1 := neg_one_lt_mul_of_div_lt hn hc
  have h2 := one_add_mul_pos hn hc (Nat.sub_le n 1)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine ⟨by linarith, ?_, ?_⟩ <;> simp <;> linarith

/-- The modulus of the Hermite integrand for a real exponent `σ`. -/
def hermBound (n : ℕ) (σ : ℝ) (x : Fin n → ℝ) : ℝ :=
  |vandermonde x| ^ (2 * σ) * ∏ k : Fin n, Real.exp (-x k ^ 2 / 2)

theorem hermBound_nonneg (n : ℕ) (σ : ℝ) (x : Fin n → ℝ) : 0 ≤ hermBound n σ x := by
  unfold hermBound
  positivity

theorem measurable_hermBound (n : ℕ) (σ : ℝ) : Measurable (hermBound n σ) := by
  unfold hermBound vandermonde
  fun_prop

theorem vandermonde_ne_zero {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i j, i ≠ j → x i ≠ x j) :
    vandermonde x ≠ 0 := by
  unfold vandermonde
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  split_ifs with h
  · exact sub_ne_zero.mpr (hx i j (Fin.ne_of_lt h))
  · exact one_ne_zero

theorem ae_vandermonde_ne_zero (n : ℕ) : ∀ᵐ x : Fin n → ℝ, vandermonde x ≠ 0 := by
  filter_upwards [DLMF.Selberg.ae_coords_ne n] with x hx using vandermonde_ne_zero hx

theorem norm_vandermonde_cpow {n : ℕ} {x : Fin n → ℝ} (hx : vandermonde x ≠ 0) (c : ℂ) :
    ‖((|vandermonde x| : ℝ) : ℂ) ^ (2 * c)‖ = |vandermonde x| ^ (2 * c.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hx)]
  simp

theorem norm_hermIntegrand_eq {n : ℕ} {x : Fin n → ℝ} (hx : vandermonde x ≠ 0) (c : ℂ) :
    ‖hermIntegrand n c x‖ = hermBound n c.re x := by
  unfold hermIntegrand hermBound
  rw [norm_mul, norm_vandermonde_cpow hx, norm_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Complex.norm_exp, show (-(x k : ℂ) ^ 2 / 2) = ((-x k ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]

theorem one_sub_div_pow_mem {N : ℕ} {y : ℝ} (hy : y ∈ Icc (-√(2 * N)) √(2 * N)) :
    0 ≤ (1 - y ^ 2 / (2 * N)) ^ N ∧ (1 - y ^ 2 / (2 * N)) ^ N ≤ Real.exp (-y ^ 2 / 2) := by
  have hsq : y ^ 2 ≤ 2 * N := by
    have h := sq_le_sq' hy.1 hy.2
    rwa [Real.sq_sqrt (by positivity)] at h
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : y ^ 2 = 0 := by simp at hsq; nlinarith [sq_nonneg y]
    simp [this]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : 0 ≤ 1 - y ^ 2 / (2 * N) := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact hsq
  refine ⟨pow_nonneg hq N, ?_⟩
  have hx2 : y ^ 2 / 2 ≤ N := by linarith
  have := Real.one_sub_div_pow_le_exp_neg (n := N) hx2
  rw [show y ^ 2 / 2 / N = y ^ 2 / (2 * N) by ring] at this
  calc (1 - y ^ 2 / (2 * N)) ^ N ≤ Real.exp (-(y ^ 2 / 2)) := this
    _ = Real.exp (-y ^ 2 / 2) := by ring_nf

theorem norm_hermApprox_le_hermBound {n : ℕ} (c : ℂ) {N : ℕ} {x : Fin n → ℝ}
    (hv : vandermonde x ≠ 0) (hx : ∀ i, x i ∈ Icc (-√(2 * N)) √(2 * N)) :
    ‖hermApprox n c N x‖ ≤ hermBound n c.re x := by
  unfold hermApprox hermBound
  rw [norm_mul, norm_vandermonde_cpow hv, norm_prod]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  obtain ⟨h0, h1⟩ := one_sub_div_pow_mem (hx i)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

/-- The real form of the approximating integrand for a real exponent. -/
def hermApproxR (n : ℕ) (σ : ℝ) (N : ℕ) (x : Fin n → ℝ) : ℝ :=
  |vandermonde x| ^ (2 * σ) * ∏ k : Fin n, (1 - x k ^ 2 / (2 * N)) ^ N

theorem hermApprox_ofReal (n : ℕ) (σ : ℝ) (N : ℕ) (x : Fin n → ℝ) :
    hermApprox n σ N x = (hermApproxR n σ N x : ℂ) := by
  unfold hermApprox hermApproxR
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (abs_nonneg _), Complex.ofReal_prod]
  push_cast
  rfl

/-- The box `[-√(2N), √(2N)]ⁿ`. -/
abbrev hermBox (n N : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Icc (-√(2 * (N : ℝ))) √(2 * N))

theorem eventually_mem_hermBox {n : ℕ} (x : Fin n → ℝ) : ∀ᶠ N : ℕ in atTop, x ∈ hermBox n N := by
  have hs : Tendsto (fun N : ℕ => √(2 * (N : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
  have : ∀ i, ∀ᶠ N : ℕ in atTop, |x i| ≤ √(2 * (N : ℝ)) := fun i =>
    hs.eventually_ge_atTop |x i|
  filter_upwards [Filter.eventually_all.2 this] with N hN i _
  exact abs_le.mp (hN i)

theorem herm_rhs_ne_zero {n : ℕ} (hn : 0 < n) {σ : ℝ} (hσ : (-1 / n : ℝ) < σ) :
    ∏ j : Fin n, (((√(2 * π) : ℝ) : ℂ) *
      (Gamma (1 + (((j : ℕ) : ℂ) + 1) * σ) / Gamma (1 + σ))) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun j _ => mul_ne_zero ?_ (div_ne_zero ?_ ?_)
  · exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * π)).ne'
  · refine Complex.Gamma_ne_zero_of_re_pos ?_
    have := one_add_mul_pos hn hσ (k := (j : ℕ) + 1) j.isLt
    simpa using this
  · refine Complex.Gamma_ne_zero_of_re_pos ?_
    have := one_add_mul_pos hn hσ (k := 1) hn
    simpa using this

/-- Integrability of `e^{-|x|²/2} |Δ(x)|^{2σ}` for `σ > -1/n`, by Fatou's lemma applied to the
Selberg approximations. -/
theorem integrable_hermBound {n : ℕ} (hn : 0 < n) {σ : ℝ} (hσ : (-1 / n : ℝ) < σ) :
    Integrable (hermBound n σ) := by
  have hσc : (-1 / n : ℝ) < (σ : ℂ).re := by simpa using hσ
  have hval := (tendsto_herm_rhs hn (σ : ℂ)).congr' (by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (integral_hermApprox_eq (mem_cDomain_herm hn hσc N) hN).symm)
  set L := ∏ j : Fin n, (((√(2 * π) : ℝ) : ℂ) *
      (Gamma (1 + (((j : ℕ) : ℂ) + 1) * σ) / Gamma (1 + σ))) with hL
  have hne : ∀ᶠ N in atTop, ∫ x in hermBox n N, hermApprox n σ N x ≠ 0 :=
    hval.eventually_ne (herm_rhs_ne_zero hn hσ)
  set g : ℕ → (Fin n → ℝ) → ℝ := fun N => (hermBox n N).indicator (hermApproxR n σ N) with hg
  have hbox : ∀ N, MeasurableSet (hermBox n N) := fun N =>
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hR_nonneg : ∀ N, ∀ x ∈ hermBox n N, 0 ≤ hermApproxR n σ N x := fun N x hx => by
    unfold hermApproxR
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ =>
      (one_sub_div_pow_mem (hx i (Set.mem_univ _))).1)
  have hg_nonneg : ∀ N x, 0 ≤ g N x := fun N x => by
    simp only [hg]
    by_cases hx : x ∈ hermBox n N
    · rw [Set.indicator_of_mem hx]; exact hR_nonneg N x hx
    · rw [Set.indicator_of_notMem hx]
  have hg_meas : ∀ N, Measurable (g N) := fun N => by
    refine Measurable.indicator ?_ (hbox N)
    unfold hermApproxR vandermonde
    fun_prop
  -- integrability and the value of `∫ g N`
  have hgval : ∀ᶠ N in atTop, Integrable (g N) ∧
      ∫ x, g N x = ‖∫ x in hermBox n N, hermApprox n σ N x‖ := by
    filter_upwards [hne] with N hN
    have hI : IntegrableOn (hermApprox n σ N) (hermBox n N) := Integrable.of_integral_ne_zero hN
    have hIR : IntegrableOn (hermApproxR n σ N) (hermBox n N) := by
      have hfun : hermApprox n σ N = fun x => (hermApproxR n σ N x : ℂ) :=
        funext (hermApprox_ofReal n σ N)
      have : IntegrableOn (fun x => (hermApproxR n σ N x : ℂ)) (hermBox n N) := by
        rw [← hfun]; exact hI
      exact this.re
    refine ⟨(integrable_indicator_iff (hbox N)).2 hIR, ?_⟩
    simp only [hg]
    rw [integral_indicator (hbox N)]
    simp_rw [hermApprox_ofReal]
    rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (setIntegral_nonneg (hbox N) (hR_nonneg N))]
  -- pointwise convergence
  have hlim : ∀ᵐ x, Tendsto (fun N => g N x) atTop (𝓝 (hermBound n σ x)) := by
    filter_upwards [ae_vandermonde_ne_zero n] with x hv
    have h := (tendsto_hermApprox (σ : ℂ) x).norm
    rw [norm_hermIntegrand_eq hv, Complex.ofReal_re] at h
    refine h.congr' ?_
    filter_upwards [eventually_mem_hermBox x] with N hN
    simp only [hg]
    rw [Set.indicator_of_mem hN, hermApprox_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hR_nonneg N x hN)]
  -- Fatou
  have hfatou := lintegral_liminf_le' (μ := (volume : Measure (Fin n → ℝ)))
    (f := fun N x => ENNReal.ofReal (g N x)) (u := atTop)
    (fun N => (hg_meas N).ennreal_ofReal.aemeasurable)
  have hleft : ∫⁻ x, ENNReal.ofReal (hermBound n σ x) =
      ∫⁻ x, liminf (fun N => ENNReal.ofReal (g N x)) atTop := by
    refine lintegral_congr_ae ?_
    filter_upwards [hlim] with x hx
    exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
  have hright : liminf (fun N => ∫⁻ x, ENNReal.ofReal (g N x)) atTop = ENNReal.ofReal ‖L‖ := by
    refine Tendsto.liminf_eq ?_
    have h := (ENNReal.continuous_ofReal.tendsto _).comp hval.norm
    refine h.congr' ?_
    filter_upwards [hgval] with N hN
    rw [Function.comp_apply, ← hN.2, ofReal_integral_eq_lintegral_ofReal hN.1
      (Eventually.of_forall (hg_nonneg N))]
  refine ⟨(measurable_hermBound n σ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (hermBound_nonneg n σ)), hleft]
  exact lt_of_le_of_lt (hfatou.trans hright.le) ENNReal.ofReal_lt_top

/-- Convergence of the box integrals on the full domain `Re c > -1/n`. -/
theorem tendsto_integral_hermApprox {n : ℕ} (hn : 0 < n) {c : ℂ} (hc : (-1 / n : ℝ) < c.re) :
    Tendsto (fun N : ℕ => ∫ x in hermBox n N, hermApprox n c N x) atTop
      (𝓝 (∫ x, hermIntegrand n c x)) := by
  simp_rw [← integral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Icc)]
  refine tendsto_integral_filter_of_dominated_convergence (hermBound n c.re)
    (Eventually.of_forall fun N => ((measurable_hermApprox n c N).indicator
      (MeasurableSet.univ_pi fun _ => measurableSet_Icc)).aestronglyMeasurable)
    (Eventually.of_forall fun N => ?_) (integrable_hermBound hn hc) ?_
  · filter_upwards [ae_vandermonde_ne_zero n] with x hv
    by_cases hx : x ∈ hermBox n N
    · rw [Set.indicator_of_mem hx]
      exact norm_hermApprox_le_hermBound c hv fun i => hx i (Set.mem_univ _)
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact hermBound_nonneg n c.re x
  · refine Eventually.of_forall fun x => (tendsto_hermApprox c x).congr' ?_
    filter_upwards [eventually_mem_hermBox x] with N hN
    rw [Set.indicator_of_mem hN]

/-- Mehta's integral on the full domain `Re c > -1/n`, as a limit of Selberg's integral. -/
theorem integral_hermIntegrand {n : ℕ} (hn : 0 < n) {c : ℂ} (hc : (-1 / n : ℝ) < c.re) :
    ∫ x, hermIntegrand n c x =
      ∏ j : Fin n, (((√(2 * π) : ℝ) : ℂ) *
        (Gamma (1 + (((j : ℕ) : ℂ) + 1) * c) / Gamma (1 + c))) := by
  have hrhs := (tendsto_herm_rhs hn c).congr' (by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (integral_hermApprox_eq (mem_cDomain_herm hn hc N) hN).symm)
  exact tendsto_nhds_unique (tendsto_integral_hermApprox hn hc) hrhs

theorem sqrt_two_pi_pow (n : ℕ) :
    ((√(2 * π) : ℝ) : ℂ) ^ n = (2 * π : ℂ) ^ (n / 2 : ℂ) := by
  rw [show (n / 2 : ℂ) = (n : ℂ) * (1 / 2 : ℝ) by push_cast; ring, Complex.cpow_nat_mul,
    show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity), Real.sqrt_eq_rpow]

lemma selberg_hermite_aux {n : ℕ} {c : ℂ} (hc : (-1 / n : ℝ) < c.re) :
    (1 / (2 * π : ℂ) ^ (n / 2 : ℂ)) *
        ∫ t : Fin n → ℝ,
          ((|vandermonde t| : ℝ) : ℂ) ^ (2 * c) *
            ∏ k : Fin n, Complex.exp (-(t k : ℂ) ^ 2 / 2) =
      (∏ k : Fin n, Complex.Gamma (1 + ((k : ℕ) + 1) * c)) /
        Complex.Gamma (1 + c) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [vandermonde, Measure.real, volume_pi]
  change (1 / (2 * π : ℂ) ^ (n / 2 : ℂ)) * ∫ t, hermIntegrand n c t = _
  rw [integral_hermIntegrand hn hc, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, sqrt_two_pi_pow, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h0 : (2 * π : ℂ) ^ (n / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => by simp [Real.pi_ne_zero] at h
  rw [← mul_assoc, one_div, inv_mul_cancel₀ h0, one_mul]

end HermiteLimit

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

theorem measurableSet_circBox (n : ℕ) : MeasurableSet (circBox n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

theorem isCompact_circBox (n : ℕ) : IsCompact (circBox n) :=
  isCompact_univ_pi fun _ => isCompact_Icc

/-- One row of Dyson's product, `∏_{l ≠ j} (1 - e^{i(θ_j - θ_l)})^m`. -/
def dysonRow {n : ℕ} (θ : Fin n → ℝ) (j : Fin n) (m : ℕ) : ℂ :=
  ∏ l : Fin n, if j = l then 1 else (1 - Complex.exp (I * ((θ j - θ l : ℝ) : ℂ))) ^ m

/-- Dyson's product `∏_{j ≠ l} (1 - z_j / z_l)^{a_j}` with `z_j = e^{iθ_j}`. -/
def dysonTerm (n : ℕ) (a : Fin n → ℕ) (θ : Fin n → ℝ) : ℂ := ∏ j, dysonRow θ j (a j)

/-- The torus integral of Dyson's product. -/
def dysonInt (n : ℕ) (a : Fin n → ℕ) : ℂ := ∫ θ in circBox n, dysonTerm n a θ

theorem continuous_dysonTerm (n : ℕ) (a : Fin n → ℕ) : Continuous (dysonTerm n a) := by
  unfold dysonTerm dysonRow
  refine continuous_finsetProd _ fun j _ => continuous_finsetProd _ fun l _ => ?_
  split_ifs
  · exact continuous_const
  · fun_prop

theorem integrableOn_dysonTerm (n : ℕ) (a : Fin n → ℕ) :
    IntegrableOn (dysonTerm n a) (circBox n) :=
  (continuous_dysonTerm n a).continuousOn.integrableOn_compact (isCompact_circBox n)

theorem dysonRow_succ {n : ℕ} (θ : Fin n → ℝ) (j : Fin n) (m : ℕ) :
    dysonRow θ j (m + 1) = dysonRow θ j m * dysonRow θ j 1 := by
  unfold dysonRow
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  split_ifs <;> ring

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

theorem dysonRow_insertNth_self {n : ℕ} (k : Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ) :
    dysonRow (k.insertNth x y : Fin (n + 1) → ℝ) k 0 = 1 := by
  unfold dysonRow
  exact Finset.prod_eq_one fun l _ => by split_ifs <;> simp

theorem dysonRow_insertNth {n : ℕ} (k : Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ) (j : Fin n)
    (m : ℕ) :
    dysonRow (k.insertNth x y : Fin (n + 1) → ℝ) (k.succAbove j) m =
      dysonRow y j m * (1 - Complex.exp (I * ((y j - x : ℝ) : ℂ))) ^ m := by
  unfold dysonRow
  rw [Fin.prod_univ_succAbove _ k, ite_eq_right (Fin.succAbove_ne k j), mul_comm]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    (Fin.succAbove_right_injective (p := k)).eq_iff]

theorem dysonTerm_insertNth {n : ℕ} (a : Fin (n + 1) → ℕ) {k : Fin (n + 1)} (hk : a k = 0)
    (x : ℝ) (y : Fin n → ℝ) :
    dysonTerm (n + 1) a (k.insertNth x y) =
      dysonTerm n (a ∘ k.succAbove) y *
        ∏ j : Fin n, (1 - Complex.exp (I * ((y j - x : ℝ) : ℂ))) ^ a (k.succAbove j) := by
  unfold dysonTerm
  rw [Fin.prod_univ_succAbove _ k, hk, dysonRow_insertNth_self, one_mul,
    ← Finset.prod_mul_distrib]
  simp only [dysonRow_insertNth, Function.comp_apply]

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

theorem prod_factorial_ne_zero {n : ℕ} (a : Fin n → ℕ) : ∏ j, ((a j).factorial : ℂ) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (Nat.factorial_pos _).ne'

theorem mnom_succAbove {n : ℕ} (a : Fin (n + 1) → ℕ) {k : Fin (n + 1)} (hk : a k = 0) :
    mnom a = mnom (a ∘ k.succAbove) := by
  unfold mnom
  rw [Fin.sum_univ_succAbove _ k, Fin.prod_univ_succAbove _ k, hk]
  simp

theorem sum_update_pred {n : ℕ} (a : Fin n → ℕ) {j : Fin n} (h : 1 ≤ a j) :
    (∑ i, Function.update a j (a j - 1) i) + 1 = ∑ i, a i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ a (Finset.mem_univ j), Function.update_self]
  rw [Finset.sum_congr rfl fun i hi => Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _]
  omega

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

theorem measurable_circV (n : ℕ) : Measurable (circV n) := by
  unfold circV
  fun_prop

theorem measurable_circIntegrand (n : ℕ) (b : ℂ) : Measurable (circIntegrand n b) := by
  unfold circIntegrand
  fun_prop

theorem circV_nonneg (n : ℕ) (θ : Fin n → ℝ) : 0 ≤ circV n θ := by
  unfold circV
  exact Finset.prod_nonneg fun j _ => Finset.prod_nonneg fun k _ => by
    split_ifs <;> positivity

theorem norm_exp_sub_le (x y : ℝ) : ‖Complex.exp (I * x) - Complex.exp (I * y)‖ ≤ 2 := by
  calc ‖Complex.exp (I * x) - Complex.exp (I * y)‖
      ≤ ‖Complex.exp (I * x)‖ + ‖Complex.exp (I * y)‖ := norm_sub_le _ _
    _ = 2 := by rw [Complex.norm_exp_I_mul_ofReal, Complex.norm_exp_I_mul_ofReal]; norm_num

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

theorem exp_ne_exp_of_good {n : ℕ} {θ : Fin n → ℝ}
    (hθ : ∀ j l, j ≠ l → Complex.exp (I * ((θ j - θ l : ℝ) : ℂ)) ≠ 1) {j l : Fin n}
    (hjl : j ≠ l) : Complex.exp (I * θ j) - Complex.exp (I * θ l) ≠ 0 := by
  intro h
  apply hθ j l hjl
  rw [show I * ((θ j - θ l : ℝ) : ℂ) = I * θ j - I * θ l by push_cast; ring, Complex.exp_sub,
    sub_eq_zero.mp h, div_self (Complex.exp_ne_zero _)]

theorem circV_pos {n : ℕ} {θ : Fin n → ℝ}
    (hθ : ∀ j l, j ≠ l → Complex.exp (I * ((θ j - θ l : ℝ) : ℂ)) ≠ 1) : 0 < circV n θ := by
  unfold circV
  refine Finset.prod_pos fun j _ => Finset.prod_pos fun k _ => ?_
  split_ifs with h
  · have := exp_ne_exp_of_good hθ (Fin.ne_of_lt h)
    positivity
  · exact one_pos

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
    refine DLMF.Selberg.differentiableOn_integral_of_dominated
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
  · exact (Complex.differentiableAt_Gamma _ (DLMF.Selberg.ne_neg_nat_of_re_pos h1)).comp b
      (by fun_prop)
  · exact ((Complex.differentiableAt_Gamma _ (DLMF.Selberg.ne_neg_nat_of_re_pos h2)).comp b
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

/-- **Dyson's integral** (Morris), DLMF 5.14.7, via Good's constant-term identity at the
integers, Carlson's theorem, Landau's integrability theorem and analytic continuation. -/
theorem circInt_eq_circRHS {n : ℕ} (hn : 0 < n) {b : ℂ} (hb : (-1 / n : ℝ) < b.re) :
    circInt n b = circRHS n b := by
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
  -- the identity theorem on the right half-plane
  have hpos : ∀ w : ℂ, 0 < w.re → circInt n w = circRHS n w := by
    have hU : IsOpen {b : ℂ | (0 : ℝ) < b.re} := isOpen_lt continuous_const Complex.continuous_re
    intro w hw
    refine (hdA.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
      ((hdG.mono hD0).analyticOnNhd hU) (convex_halfSpace_re_gt 0).isPreconnected
      (z₀ := 2) (by simp) ?_ hw
    have hV : IsOpen {c : ℂ | 1 < c.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hV.mem_nhds (by simp : (2 : ℂ) ∈ {c : ℂ | 1 < c.re})] with c hc
    exact hge1 c (le_of_lt hc)
  -- integrability on the full domain by Landau's theorem
  have hMpos : 0 < M := by positivity
  have hint : ∀ σ : ℝ, (-1 / n : ℝ) < σ →
      IntegrableOn (fun θ => circV n θ ^ σ) (circBox n) := by
    intro σ hσ
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
  -- the identity theorem on the full domain
  have hdB := differentiableOn_circInt (s0 := -1 / n) hint
  have hU : IsOpen {b : ℂ | (-1 / n : ℝ) < b.re} := isOpen_lt continuous_const Complex.continuous_re
  refine (hdB.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hdG.analyticOnNhd hU)
    (convex_halfSpace_re_gt _).isPreconnected (z₀ := 1) (by simp; linarith) ?_ hb
  have hV : IsOpen {c : ℂ | 0 < c.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hV.mem_nhds (by simp : (1 : ℂ) ∈ {c : ℂ | 0 < c.re})] with c hc
  exact hpos c hc

lemma selberg_circular_aux {n : ℕ} {b : ℂ} (hb : (-1 / n : ℝ) < b.re) :
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

@[dlmf 5.14.E5]
theorem selberg_laguerrePolyL {n m : ℕ} {a c : ℂ} (hm : m ≤ n)
    (ha : 0 < a.re) (hc : 0 < c.re) :
    ∫ t : Fin n → ℝ in Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ),
        (∏ i : Fin m, (t (Fin.castLE hm i) : ℂ)) *
          (∏ i : Fin n, (t i : ℂ) ^ (a - 1) * Complex.exp (-(t i : ℂ))) *
          ((|vandermonde t| : ℝ) : ℂ) ^ (2 * c) =
      (∏ k : Fin m, (a + (n - 1 - k : ℕ) * c)) *
        (∏ k : Fin n, Complex.Gamma (a + (n - 1 - k : ℕ) * c) *
          Complex.Gamma (1 + ((k : ℕ) + 1) * c)) /
        Complex.Gamma (1 + c) ^ n :=
  selberg_laguerrePolyL_aux hm ha hc

@[dlmf 5.14.E6]
theorem selberg_hermite {n : ℕ} {c : ℂ} (hc : (-1 / n : ℝ) < c.re) :
    (1 / (2 * π : ℂ) ^ (n / 2 : ℂ)) *
        ∫ t : Fin n → ℝ,
          ((|vandermonde t| : ℝ) : ℂ) ^ (2 * c) *
            ∏ k : Fin n, Complex.exp (-(t k : ℂ) ^ 2 / 2) =
      (∏ k : Fin n, Complex.Gamma (1 + ((k : ℕ) + 1) * c)) /
        Complex.Gamma (1 + c) ^ n :=
  selberg_hermite_aux hc

@[dlmf 5.14.E7]
theorem selberg_circular {n : ℕ} {b : ℂ} (hb : (-1 / n : ℝ) < b.re) :
    (1 / (2 * π : ℂ) ^ (n : ℂ)) *
        ∫ θ : Fin n → ℝ in Set.pi Set.univ fun _ => Set.Icc (-π) π,
          ∏ j : Fin n, ∏ k : Fin n,
            (if j.val < k.val then
              (‖Complex.exp (I * θ j) - Complex.exp (I * θ k)‖ : ℂ) ^ (2 * b)
            else 1) =
      Complex.Gamma (1 + b * n) / Complex.Gamma (1 + b) ^ n :=
  selberg_circular_aux hb

end DLMF.Gamma
