/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.DifferentialEquations
public import DLMF.GeneralizedHypergeometric.Integrals
public import TauCeti.Analysis.Contour.Residue.Basic
public import DLMFMathlib.Analysis.Complex.BarnesResidue

/-!
# Generalized hypergeometric asymptotics: DLMF §16.11

All powers are evaluated on a specified logarithm sheet. Thus the two formal
exponential series at phases w±πi are not collapsed by principal argument reduction.
Algebraic terms are Barnes residues, deduplicated at resonant poles; multiple poles
automatically retain the logarithmic terms mentioned in the source. The printed
coefficient recurrence is continued through repeated lower parameters by a specified
limit. Formal E/H series are coefficient families, never asserted convergent except
where DLMF explicitly claims convergence (p=q+1, |z|>1).

Residues are the proved pinned TauCeti API (authors and origin retained upstream).
-/

@[expose] public section
open Complex Filter Set Finset
open scoped Topology Real
noncomputable section
namespace DLMF.Hypergeometric

/-- The positive exponential index kappa, for p<q+1 (16.11.3). -/
@[dlmf 16.11.E3]
def genAsymptoticKappa (p q : ℕ) : ℕ := q + 1 - p

/-- The full complex exponent nu (16.11.3). -/
@[dlmf 16.11.E3]
def genAsymptoticNu {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) : ℂ :=
  (∑ j, a j) - (∑ j, b j) + ((q : ℂ) - p) / 2

/-- Append the fixed lower parameter b_(q+1)=1 used by the coefficient recurrence. -/
def genAsymptoticAugment {q : ℕ} (b : Fin q → ℂ) (j : Fin (q + 1)) : ℂ :=
  if hj : j.val < q then b ⟨j.val, hj⟩ else 1

/-- The raw e_(k,m) coefficient, where the augmented lower parameters are distinct. -/
@[dlmf 16.11.E5]
def genAsymptoticEkm {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (k m : ℕ) : ℂ :=
  ∑ j : Fin (q + 1),
    poch (1 - genAsymptoticNu a b - genAsymptoticKappa p q * genAsymptoticAugment b j + m)
      (genAsymptoticKappa p q + k - m) *
    (∏ i, (a i - genAsymptoticAugment b j)) /
      (∏ i ∈ univ.erase j, (genAsymptoticAugment b i - genAsymptoticAugment b j))

/-- Raw c coefficients from the complete finite recurrence (16.11.4). -/
@[dlmf 16.11.E4]
def genAsymptoticCRaw {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => -(∑ m : Fin (k + 1), genAsymptoticCRaw a b m.val *
      genAsymptoticEkm a b (k + 1) m.val) /
      ((k + 1 : ℂ) * (genAsymptoticKappa p q : ℂ) ^ genAsymptoticKappa p q)
termination_by k => k

/-- Distinct generic perturbation of the lower parameters, keeping the appended one fixed. -/
def genAsymptoticPerturb {q : ℕ} (b : Fin q → ℂ) (ε : ℂ) (j : Fin q) : ℂ :=
  b j + (j.val + 1) * ε

/-- The coefficient c_k with removable repeated-parameter cases retained by continuation. -/
def genAsymptoticC {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (k : ℕ) : ℂ :=
  limUnder (𝓝[≠] (0 : ℂ)) (fun ε => genAsymptoticCRaw a (genAsymptoticPerturb b ε) k)

/-- The kth formal exponential term E_(p,q) on the logarithm sheet w (16.11.1). -/
@[dlmf 16.11.E1]
def genETermLog {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (w : ℂ) (k : ℕ) : ℂ :=
  let κ := (genAsymptoticKappa p q : ℂ)
  let ν := genAsymptoticNu a b
  (2 * Real.pi : ℂ) ^ (((p : ℂ) - q) / 2) * κ ^ (-ν - 1 / 2) *
    Complex.exp (κ * Complex.exp (w / κ)) * genAsymptoticC a b k *
    Complex.exp ((ν - k) * (Complex.log κ + w / κ))

/-- The formal algebraic simple-pole term H_(p,q) on logarithm sheet w (16.11.2). -/
@[dlmf 16.11.E2]
def genHTermLog {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (w : ℂ) (jk : Fin p × ℕ) : ℂ :=
  (-1 : ℂ) ^ jk.2 / jk.2.factorial * Gamma (a jk.1 + jk.2) *
    (∏ i ∈ univ.erase jk.1, Gamma (a i - a jk.1 - jk.2)) /
    genGamma (genShift (genParams b) (-a jk.1 - jk.2)) *
    Complex.exp ((-a jk.1 - jk.2) * w)

/-- The distinct upper-pole set, which does not count resonant coincidences twice. -/
def genHPoleSet {p : ℕ} (a : Fin p → ℂ) : Set ℂ :=
  {s | ∃ j : Fin p, ∃ k : ℕ, s = -a j - k}

/-- The algebraic formal term at any pole, including logarithmic multiple-pole terms. -/
def genHResidueLog {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (w s : ℂ) : ℂ :=
  TauCeti.Contour.residue (genBarnesKernelLog (genParams a) (genParams b) w) s

/-- A finite set of distinct algebraic poles through order N. -/
def genHPoleTrunc {p : ℕ} (a : Fin p → ℂ) (N : ℕ) : Finset ℂ := by
  classical
  exact ((Finset.univ : Finset (Fin p)).product (Finset.range N)).image (fun jk : Fin p × ℕ => -a jk.1 - jk.2)

/-- The finite algebraic expansion, retaining full residues at resonant poles. -/
def genHTruncLog {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (w : ℂ) (N : ℕ) : ℂ :=
  ∑ s ∈ genHPoleTrunc a N, genHResidueLog a b w s

/-- The exponential remainder scale, with its branch fixed by w. -/
def genEScaleLog {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (w : ℂ) (N : ℕ) : ℂ :=
  let κ := (genAsymptoticKappa p q : ℂ)
  Complex.exp (κ * Complex.exp (w / κ)) *
    Complex.exp ((genAsymptoticNu a b - N) * (Complex.log κ + w / κ))

/-- An algebraic remainder bound, with sufficient logarithmic degree for repeated poles. -/
def genHScaleLog {p : ℕ} (a : Fin p → ℂ) (w : ℂ) (N : ℕ) : ℝ :=
  (1 + ‖w‖) ^ (p - 1) * ∑ j, ‖Complex.exp ((-a j - N) * w)‖

/-- Approach to infinity in a closed half of the full principal logarithm sector. -/
def genInfinityLogHalf (ε : ℝ) : Filter ℂ :=
  comap Complex.re atTop ⊓ 𝓟 {w : ℂ | |w.im| ≤ Real.pi ∧ 0 ≤ ε * w.im}

/-- The selected large-parameter shift for16.11.10. -/
def genPartialShift {n : ℕ} (a : Fin n → ℂ) (k : ℕ) (r : ℝ) (j : Fin n) : ℂ :=
  if j.val < k then a j + r else a j

/-- All repeated lower-parameter cases have the finite limiting coefficient. -/
@[dlmf 16.11.E4, dlmf 16.11.E5]
theorem genAsymptoticC_limit {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (hpq : p < q + 1) (k : ℕ) :
    Tendsto (fun ε : ℂ => genAsymptoticCRaw a (genAsymptoticPerturb b ε) k)
      (𝓝[≠] 0) (𝓝 (genAsymptoticC a b k)) := by
  sorry

/-- The complete printed recurrence on its nonsingular augmented-parameter domain. -/
@[dlmf 16.11.E4]
theorem genAsymptoticC_recurrence {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (hpq : p < q + 1)
    (hb : Function.Injective (genAsymptoticAugment b)) :
    genAsymptoticC a b 0 = 1 ∧ ∀ k : ℕ, genAsymptoticC a b (k + 1) =
      -(∑ m ∈ range (k + 1), genAsymptoticC a b m * genAsymptoticEkm a b (k + 1) m) /
        ((k + 1 : ℂ) * (genAsymptoticKappa p q : ℂ) ^ genAsymptoticKappa p q) := by
  sorry

/-- Gamma is analytic away from its poles. -/
lemma ghbR4_Gamma_analyticAt {c : ℂ} (hc : ∀ m : ℕ, c ≠ -m) : AnalyticAt ℂ Gamma c := by
  have hU : IsOpen {s : ℂ | ∀ m : ℕ, s ≠ -m} := by
    simpa using barnesRes_isOpen_ne_sub_nat (0 : ℂ)
  exact DifferentiableOn.analyticAt (fun s hs => (differentiableAt_Gamma s hs).differentiableWithinAt)
    (hU.mem_nhds hc)

/-- Local pole factor of Gamma at `-m`. -/
noncomputable def ghbR4_GammaPoleFactor (m : ℕ) (x : ℂ) : ℂ :=
  Gamma (x + m + 1) / ∏ k ∈ range m, (x + k)

/-- The pole factor is analytic at its pole. -/
lemma ghbR4_GammaPoleFactor_analyticAt (m : ℕ) :
    AnalyticAt ℂ (ghbR4_GammaPoleFactor m) (-m) := by
  unfold ghbR4_GammaPoleFactor
  apply AnalyticAt.div
  · have h1 : AnalyticAt ℂ Gamma ((-(m : ℂ)) + m + 1) := by
      rw [show (-(m : ℂ)) + m + 1 = 1 by ring]
      exact ghbR4_Gamma_analyticAt (fun k hk => by
        have := congrArg Complex.re hk; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
    exact (h1.comp_of_eq (f := fun x : ℂ => x + m + 1) (by fun_prop) rfl :)
  · fun_prop
  · rw [prod_ne_zero_iff]
    intro k hk
    have hk := Finset.mem_range.mp hk
    intro h
    have : (k : ℂ) = m := by linear_combination h
    exact absurd (by exact_mod_cast this : k = m) (by omega)

/-- Value of the pole factor at `-m`: the Gamma residue `(-1)^m/m!`. -/
lemma ghbR4_GammaPoleFactor_value (m : ℕ) :
    ghbR4_GammaPoleFactor m (-m) = (-1) ^ m / m.factorial := by
  unfold ghbR4_GammaPoleFactor
  rw [show (-(m : ℂ)) + m + 1 = 1 by ring, Gamma_one]
  have : ∏ k ∈ range m, (-(m : ℂ) + k) = (-1) ^ m * m.factorial := by
    rw [← barnesRes_prod_sub_nat]; exact prod_congr rfl fun k _ => by ring
  rw [this]
  have h1 : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; simp
  have h2 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  field_simp
  linear_combination (-1) * h1

/-- Near `-m`, Gamma is `(x+m)^(-1)` times the pole factor. -/
lemma ghbR4_Gamma_eq_pole (m : ℕ) :
    ∀ᶠ x in 𝓝[≠] (-(m : ℂ)), Gamma x = (x - (-(m : ℂ))) ^ (-1 : ℤ) * ghbR4_GammaPoleFactor m x := by
  have hball' : ∀ᶠ x in 𝓝 (-(m : ℂ)), dist x (-(m : ℂ)) < 1 / 2 :=
    Metric.ball_mem_nhds _ (by norm_num)
  have hball : ∀ᶠ x in 𝓝 (-(m : ℂ)), ‖x - (-(m : ℂ))‖ < 1 / 2 :=
    hball'.mono fun x hx => by rwa [dist_eq_norm] at hx
  filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with x hx hne
  have hne : x ≠ -(m : ℂ) := hne
  have hnp : ∀ j : ℕ, j ≤ m → x + j ≠ 0 := by
    intro j hj h
    by_cases hjm : j = m
    · apply hne; subst hjm; linear_combination h
    · have hx' : x = -(j : ℂ) := by linear_combination h
      rw [hx'] at hx
      have : ‖(-(j : ℂ)) - (-(m : ℂ))‖ = |(m : ℝ) - j| := by
        rw [show (-(j : ℂ)) - (-(m : ℂ)) = (((m : ℝ) - j : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs]
      rw [this] at hx
      have h1 : (1 : ℝ) ≤ |(m : ℝ) - j| := by
        rcases lt_or_gt_of_ne hjm with h | h
        · have : (j : ℝ) + 1 ≤ m := by exact_mod_cast h
          rw [abs_of_pos (by linarith)]
          linarith
        · omega
      linarith
  have hG := barnesRes_Gamma_add_nat_succ x m hnp
  unfold ghbR4_GammaPoleFactor
  rw [hG, prod_range_succ]
  have hxm : x + m ≠ 0 := hnp m le_rfl
  have hprod : ∏ k ∈ range m, (x + k) ≠ 0 :=
    prod_ne_zero_iff.mpr fun k hk => hnp k (by have := Finset.mem_range.mp hk; omega)
  rw [show x - -(m : ℂ) = x + m by ring, zpow_neg_one]
  field_simp

/-- Gamma with its possible simple pole at `c` removed. -/
noncomputable def ghbR4_localGamma (c : ℂ) (x : ℂ) : ℂ := by
  classical
  exact if h : ∃ m : ℕ, c = -m then ghbR4_GammaPoleFactor h.choose x else Gamma x

/-- The pole exponent of Gamma at `c`. -/
noncomputable def ghbR4_poleExp (c : ℂ) : ℕ := by
  classical
  exact if ∃ m : ℕ, c = -m then 1 else 0

/-- The pole-removed Gamma function is analytic at its base point. -/
lemma ghbR4_localGamma_analyticAt (c : ℂ) : AnalyticAt ℂ (ghbR4_localGamma c) c := by
  classical
  unfold ghbR4_localGamma
  split_ifs with h
  · have := ghbR4_GammaPoleFactor_analyticAt h.choose
    rwa [← h.choose_spec] at this
  · push Not at h
    exact ghbR4_Gamma_analyticAt h

/-- Gamma times its local pole power is the pole-removed Gamma function. -/
lemma ghbR4_localGamma_eq (c : ℂ) :
    ∀ᶠ x in 𝓝[≠] c, Gamma x * (x - c) ^ ghbR4_poleExp c = ghbR4_localGamma c x := by
  classical
  unfold ghbR4_localGamma ghbR4_poleExp
  split_ifs with h
  · have hc := h.choose_spec
    have := ghbR4_Gamma_eq_pole h.choose
    rw [← hc] at this
    filter_upwards [this, self_mem_nhdsWithin] with x hx hne
    have hne : x - c ≠ 0 := sub_ne_zero.mpr hne
    rw [hx, zpow_neg_one, pow_one]
    field_simp
  · exact Eventually.of_forall fun x => by simp

/-- Value of the pole-removed Gamma function at a pole. -/
lemma ghbR4_localGamma_pole_value (m : ℕ) :
    ghbR4_localGamma (-(m : ℂ)) (-(m : ℂ)) = (-1) ^ m / m.factorial := by
  classical
  unfold ghbR4_localGamma
  split_ifs with h
  · have hk : h.choose = m := by
      have := h.choose_spec
      exact_mod_cast (neg_inj.mp this).symm
    rw [hk, ghbR4_GammaPoleFactor_value]
  · exact absurd ⟨m, rfl⟩ h

/-- Away from poles nothing is removed. -/
lemma ghbR4_localGamma_of_not_pole {c : ℂ} (hc : ∀ m : ℕ, c ≠ -m) :
    ghbR4_localGamma c = Gamma := by
  classical
  unfold ghbR4_localGamma
  funext x
  split_ifs with h
  · obtain ⟨m, hm⟩ := h; exact absurd hm (hc m)
  · rfl

/-- The pole exponent vanishes away from poles. -/
lemma ghbR4_poleExp_of_not_pole {c : ℂ} (hc : ∀ m : ℕ, c ≠ -m) : ghbR4_poleExp c = 0 := by
  classical
  unfold ghbR4_poleExp
  split_ifs with h
  · obtain ⟨m, hm⟩ := h; exact absurd hm (hc m)
  · rfl

/-- The pole exponent is one at a pole. -/
lemma ghbR4_poleExp_pole (m : ℕ) : ghbR4_poleExp (-(m : ℂ)) = 1 := by
  classical
  unfold ghbR4_poleExp
  split_ifs with h
  · rfl
  · exact absurd ⟨m, rfl⟩ h

/-- Local factorization of a finite Gamma product near any point. -/
lemma ghbR4_prod_Gamma_local {p : ℕ} (a : Fin p → ℂ) (s₀ : ℂ) :
    ∀ᶠ s in 𝓝[≠] s₀, (∏ i, Gamma (a i + s)) * (s - s₀) ^ (∑ i, ghbR4_poleExp (a i + s₀)) =
      ∏ i, ghbR4_localGamma (a i + s₀) (a i + s) := by
  have hmap : ∀ i, Tendsto (fun s => a i + s) (𝓝[≠] s₀) (𝓝[≠] (a i + s₀)) := by
    intro i
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((continuous_const.add continuous_id).tendsto s₀).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      intro h; exact hs (add_left_cancel h)
  have hall : ∀ᶠ s in 𝓝[≠] s₀, ∀ i, Gamma (a i + s) * (s - s₀) ^ ghbR4_poleExp (a i + s₀) =
      ghbR4_localGamma (a i + s₀) (a i + s) := by
    rw [eventually_all]
    intro i
    filter_upwards [hmap i (ghbR4_localGamma_eq (a i + s₀))] with s hs
    rw [← hs]; congr 2; ring
  filter_upwards [hall] with s hs
  rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  exact prod_congr rfl fun i _ => hs i

/-- A shifted parameter Gamma product as a finite product. -/
lemma ghbR4_genGamma_shift_params {p : ℕ} (a : Fin p → ℂ) (s : ℂ) :
    genGamma (genShift (genParams a) s) = ∏ i, Gamma (a i + s) := by
  simp [genGamma, genShift, genParams, List.map_ofFn, List.prod_ofFn, Function.comp_def]

/-- The reciprocal lower Gamma block of the Barnes kernel is entire. -/
lemma ghbR4_invGamma_shift_analyticAt {q : ℕ} (b : Fin q → ℂ) (s₀ : ℂ) :
    AnalyticAt ℂ (fun s => (genGamma (genShift (genParams b) s))⁻¹) s₀ := by
  simp only [ghbR4_genGamma_shift_params, ← prod_inv_distrib]
  apply Finset.analyticAt_fun_prod
  intro i _
  have h : Differentiable ℂ (fun s : ℂ => (Gamma s)⁻¹) := by
    simpa [one_div] using differentiable_one_div_Gamma
  exact (h.analyticAt (b i + s₀)).comp_of_eq (f := fun s => b i + s) (by fun_prop) rfl

/-- The Barnes kernel near a point, after removing all Gamma poles from the upper block. -/
lemma ghbR4_kernel_local {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (w s₀ : ℂ) :
    ∀ᶠ s in 𝓝[≠] s₀, genBarnesKernelLog (genParams a) (genParams b) w s =
      (s - s₀) ^ (-((∑ i, ghbR4_poleExp (a i + s₀) : ℕ) : ℤ)) •
        ((∏ i, ghbR4_localGamma (a i + s₀) (a i + s)) *
          (genGamma (genShift (genParams b) s))⁻¹ * Gamma (-s) * Complex.exp (s * w)) := by
  filter_upwards [ghbR4_prod_Gamma_local a s₀, self_mem_nhdsWithin] with s hs hne
  have hne : s - s₀ ≠ 0 := sub_ne_zero.mpr hne
  rw [← hs, genBarnesKernelLog, ghbR4_genGamma_shift_params, zpow_neg, zpow_natCast, smul_eq_mul]
  field_simp

/-- Each vector parameter belongs to its multiset. -/
lemma ghbR4_mem_genParams {p : ℕ} (a : Fin p → ℂ) (i : Fin p) : a i ∈ genParams a := by
  simp [genParams]

/-- The reflected Gamma factor is regular at every upper pole. -/
lemma ghbR4_Gamma_neg_analyticAt {p : ℕ} (a : Fin p → ℂ) (ha : genDenRegular (genParams a))
    (j : Fin p) (k : ℕ) : AnalyticAt ℂ (fun s => Gamma (-s)) (-a j - k) := by
  have hnp : ∀ m : ℕ, -(-a j - k) ≠ -m := by
    intro m h
    apply ha (a j) (ghbR4_mem_genParams a j) (m + k)
    push_cast; linear_combination h
  exact (ghbR4_Gamma_analyticAt hnp).comp_of_eq (f := fun s => -s) (by fun_prop) rfl

/-- The pole-removed Barnes kernel is analytic at an upper pole. -/
lemma ghbR4_G_analyticAt {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (ha : genDenRegular (genParams a))
    (j : Fin p) (k : ℕ) (w : ℂ) :
    AnalyticAt ℂ (fun s => (∏ i, ghbR4_localGamma (a i + (-a j - k)) (a i + s)) *
      (genGamma (genShift (genParams b) s))⁻¹ * Gamma (-s) * Complex.exp (s * w)) (-a j - k) := by
  have h1 : AnalyticAt ℂ (fun s => ∏ i, ghbR4_localGamma (a i + (-a j - k)) (a i + s)) (-a j - k) := by
    apply Finset.analyticAt_fun_prod
    intro i _
    exact (ghbR4_localGamma_analyticAt _).comp_of_eq (f := fun s => a i + s) (by fun_prop) rfl
  exact ((h1.mul (ghbR4_invGamma_shift_analyticAt b _)).mul
    (ghbR4_Gamma_neg_analyticAt a ha j k)).mul (by fun_prop)

/-- Gamma poles are simple. -/
lemma ghbR4_poleExp_le_one (c : ℂ) : ghbR4_poleExp c ≤ 1 := by
  classical
  unfold ghbR4_poleExp; split_ifs <;> omega

/-- The algebraic coefficients equal the corresponding simple Barnes residues. -/
@[dlmf 16.11.E2]
theorem genH_simple_residue {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (ha : genDenRegular (genParams a))
    (hdiff : ∀ i j, i ≠ j → ∀ n : ℤ, a i - a j ≠ n)
    (w : ℂ) (j : Fin p) (k : ℕ) :
    genHResidueLog a b w (-a j - k) = genHTermLog a b w (j, k) := by
  classical
  set s₀ := -a j - k with hs₀
  have hnp : ∀ i, i ≠ j → ∀ m : ℕ, a i + s₀ ≠ -m := by
    intro i hij m h
    apply hdiff i j hij ((k : ℤ) - m)
    push_cast; linear_combination h
  have hj : a j + s₀ = -(k : ℂ) := by rw [hs₀]; ring
  have hN : ∑ i, ghbR4_poleExp (a i + s₀) = 1 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hj, ghbR4_poleExp_pole,
      Finset.sum_eq_zero (fun i hi => ghbR4_poleExp_of_not_pole (hnp i (Finset.ne_of_mem_erase hi)))]
    rfl
  have hloc := ghbR4_kernel_local a b w s₀
  rw [hN] at hloc
  unfold genHResidueLog
  rw [TauCeti.Contour.residue_eq_of_eventuallyEq_zpow_smul (by norm_num)
    (ghbR4_G_analyticAt a b ha j k w) hloc]
  norm_num
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  rw [hj, ghbR4_localGamma_pole_value]
  rw [Finset.prod_congr rfl (fun i hi => by
    rw [ghbR4_localGamma_of_not_pole (hnp i (Finset.ne_of_mem_erase hi))])]
  unfold genHTermLog
  rw [add_comm (k : ℂ) (a j)]
  rw [Finset.prod_congr rfl (fun i _ => by rw [show a i + (-a j - k) = a i - a j - k by ring])]
  simp only [div_eq_mul_inv]
  ring

/-- A repeated pole contributes an exponential times a polynomial in the logarithm. -/
theorem genH_resonant_log_polynomial {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (ha : genDenRegular (genParams a)) {s : ℂ} (hs : s ∈ genHPoleSet a) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ p - 1 ∧
      ∀ w : ℂ, genHResidueLog a b w s = Complex.exp (s * w) * P.eval w := by
  classical
  obtain ⟨j, k, rfl⟩ := hs
  set s₀ := -a j - k with hs₀
  set N := ∑ i, ghbR4_poleExp (a i + s₀) with hNdef
  have hj : a j + s₀ = -(k : ℂ) := by rw [hs₀]; ring
  have hN1 : 1 ≤ N := by
    have := Finset.single_le_sum (f := fun i => ghbR4_poleExp (a i + s₀))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [hj, ghbR4_poleExp_pole] at this
    exact this
  have hNp : N ≤ p := by
    calc N ≤ ∑ _i : Fin p, 1 := Finset.sum_le_sum fun i _ => ghbR4_poleExp_le_one _
      _ = p := by simp
  set G0 : ℂ → ℂ := fun s => (∏ i, ghbR4_localGamma (a i + s₀) (a i + s)) *
      (genGamma (genShift (genParams b) s))⁻¹ * Gamma (-s) with hG0
  have hG0a : AnalyticAt ℂ G0 s₀ := by
    have h1 : AnalyticAt ℂ (fun s => ∏ i, ghbR4_localGamma (a i + s₀) (a i + s)) s₀ := by
      apply Finset.analyticAt_fun_prod
      intro i _
      exact (ghbR4_localGamma_analyticAt _).comp_of_eq (f := fun s => a i + s) (by fun_prop) rfl
    exact (h1.mul (ghbR4_invGamma_shift_analyticAt b _)).mul (ghbR4_Gamma_neg_analyticAt a ha j k)
  set n := N - 1 with hn
  refine ⟨∑ i ∈ range (n + 1), Polynomial.C ((n.choose i : ℂ) * iteratedDeriv i G0 s₀ /
    n.factorial) * Polynomial.X ^ (n - i), ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    omega
  · intro w
    have hloc := ghbR4_kernel_local a b w s₀
    unfold genHResidueLog
    have hE : AnalyticAt ℂ (fun s : ℂ => Complex.exp (s * w)) s₀ := by fun_prop
    rw [TauCeti.Contour.residue_eq_of_eventuallyEq_zpow_smul (by omega) (hG0a.mul hE) hloc]
    have hidx : (-1 - -((N : ℕ) : ℤ)).toNat = n := by omega
    rw [hidx]
    have hL := iteratedDeriv_fun_mul (n := n) (x := s₀) hG0a.contDiffAt hE.contDiffAt
    have hexp : ∀ m, iteratedDeriv m (fun s : ℂ => Complex.exp (s * w)) s₀ =
        w ^ m * Complex.exp (s₀ * w) := by
      intro m
      have := congrFun (iteratedDeriv_cexp_const_mul m w) s₀
      simp only [mul_comm _ w] at this ⊢
      exact this
    rw [show (G0 * fun s => Complex.exp (s * w)) = fun s => G0 s * Complex.exp (s * w) from rfl, hL]
    simp only [hexp, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, mul_sum, sum_div]
    apply sum_congr rfl
    intro i _
    ring

/-- The full H residue series converges to the continued function at |z|>1, including resonances and both closed cut sides. -/
@[dlmf 16.11.E6]
theorem genH_balanced_converges {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (ha : genDenRegular (genParams a)) (hb : genDenRegular (genParams b))
    {w : ℂ} (hr : 0 < w.re) (hi : |w.im| ≤ Real.pi) :
    HasSum (fun s : genHPoleSet a => genHResidueLog a b w s)
      (genGamma (genParams a) / genGamma (genParams b) *
        genHGNegativeLog (genParams a) (genParams b) w) := by
  sorry

/-- All orders of the equal-order expansion, with the full phase convention and resonant residues. -/
@[dlmf 16.11.E7]
theorem genHG_equal_order_asymptotic {q : ℕ} (a b : Fin q → ℂ)
    (ha : genDenRegular (genParams a)) (hb : genDenRegular (genParams b))
    (N : ℕ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Asymptotics.IsBigO (genInfinityLogHalf ε)
      (fun w => genGamma (genParams a) / genGamma (genParams b) *
        genHG (genParams a) (genParams b) (Complex.exp w) -
        genHTruncLog a b (w - ε * Real.pi * I) N - ∑ k ∈ range N, genETermLog a b w k)
      (fun w => genHScaleLog a (w - ε * Real.pi * I) N + ‖genEScaleLog a b w N‖) := by
  sorry

/-- All orders with p=q−1, both shifted E branches, and the full algebraic residue series. -/
@[dlmf 16.11.E8]
theorem genHG_one_lower_asymptotic {p : ℕ} (a : Fin p → ℂ) (b : Fin (p + 1) → ℂ)
    (ha : genDenRegular (genParams a)) (hb : genDenRegular (genParams b)) (N : ℕ) :
    Asymptotics.IsBigO (DLMF.logSector Real.pi)
      (fun w => genGamma (genParams a) / genGamma (genParams b) *
        genHG (genParams a) (genParams b) (-Complex.exp w) - genHTruncLog a b w N -
        ∑ k ∈ range N, (genETermLog a b (w - Real.pi * I) k + genETermLog a b (w + Real.pi * I) k))
      (fun w => genHScaleLog a w N + ‖genEScaleLog a b (w - Real.pi * I) N‖ +
        ‖genEScaleLog a b (w + Real.pi * I) N‖) := by
  sorry

/-- All orders with p≤q−2 on the full principal sector, with both E branch contributions. -/
@[dlmf 16.11.E9]
theorem genHG_fewer_upper_asymptotic {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (hpq : p + 2 ≤ q)
    (ha : genDenRegular (genParams a)) (hb : genDenRegular (genParams b)) (N : ℕ) :
    Asymptotics.IsBigO (DLMF.logSector Real.pi)
      (fun w => genGamma (genParams a) / genGamma (genParams b) *
        genHG (genParams a) (genParams b) (-Complex.exp w) -
        ∑ k ∈ range N, (genETermLog a b (w - Real.pi * I) k + genETermLog a b (w + Real.pi * I) k))
      (fun w => ‖genEScaleLog a b (w - Real.pi * I) N‖ +
        ‖genEScaleLog a b (w + Real.pi * I) N‖) := by
  sorry

/-- Every printed partial large-parameter shift, with unrestricted shifted bottoms and the full principal z domain. -/
@[dlmf 16.11.E10]
theorem genHG_partial_large_parameter_asymptotic {p : ℕ} (a : Fin (p + 1) → ℂ) (b : Fin p → ℂ)
    {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ p)
    (hb : ∀ j : Fin p, k ≤ j.val → ∀ n : ℕ, b j ≠ -n)
    {z : ℂ} (hz : z ∈ cutPlane) (m : ℕ) :
    Asymptotics.IsBigO atTop
      (fun r : ℝ => genHG (genParams (genPartialShift a (k - 1) r))
        (genParams (genPartialShift b k r)) z -
        ∑ n ∈ range m, genCoeff (genParams (genPartialShift a (k - 1) r))
          (genParams (genPartialShift b k r)) n * z ^ n)
      (fun r : ℝ => 1 / r ^ m) := by
  sorry

/-- The comparison product `∏_{k<n} (r/2+k)` dominates `(r/2)^n`. -/
lemma ghbR4_P_ge {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (r / 2) ^ n ≤ ∏ k ∈ range n, (r / 2 + k) := by
  calc (r / 2) ^ n = ∏ _k ∈ range n, (r / 2) := by rw [prod_const, card_range]
    _ ≤ _ := by
      gcongr with k hk
      linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]

/-- Upper bound for a rising factorial at a large real shift. -/
lemma ghbR4_poch_shift_le {x : ℂ} {r : ℝ} (hr : 0 < r) (hx : ‖x‖ ≤ r) (n : ℕ) :
    ‖poch (x + r) n‖ ≤ 4 ^ n * ∏ k ∈ range n, (r / 2 + k) := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [poch_succ, norm_mul, prod_range_succ, pow_succ]
    have h1 : ‖x + r + n‖ ≤ 4 * (r / 2 + n) := by
      refine (norm_add₃_le).trans ?_
      rw [Complex.norm_real, Complex.norm_natCast, Real.norm_of_nonneg hr.le]
      linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    calc ‖poch (x + r) n‖ * ‖x + r + n‖ ≤ (4 ^ n * ∏ k ∈ range n, (r / 2 + k)) * (4 * (r / 2 + n)) :=
          mul_le_mul ih h1 (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- Lower bound for a rising factorial at a large real shift. -/
lemma ghbR4_poch_shift_ge {y : ℂ} {r : ℝ} (hr : 0 < r) (hy : ‖y‖ ≤ r / 2) (n : ℕ) :
    ∏ k ∈ range n, (r / 2 + k) ≤ ‖poch (y + r) n‖ := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [poch_succ, norm_mul, prod_range_succ]
    have h1 : r / 2 + n ≤ ‖y + r + n‖ := by
      have : ‖((r : ℂ) + n)‖ = r + n := by
        rw [show ((r : ℂ) + n) = ((r + n : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
      have h2 := norm_sub_norm_le ((r : ℂ) + n) (-y)
      rw [sub_neg_eq_add, norm_neg, this] at h2
      rw [show y + r + n = (r : ℂ) + n + y by ring]
      linarith
    exact mul_le_mul ih h1 (by positivity) (norm_nonneg _)

/-- Upper bound for a shifted multiset rising-factorial product. -/
lemma ghbR4_genPoch_shift_le {r : ℝ} (hr : 0 < r) (c : Multiset ℂ) (hc : ∀ x ∈ c, ‖x‖ ≤ r)
    (n : ℕ) : ‖genPoch (genShift c r) n‖ ≤ (4 ^ n * ∏ k ∈ range n, (r / 2 + k)) ^ c.card := by
  induction c using Multiset.induction_on with
  | empty => simp [genPoch, genShift]
  | @cons x c ih =>
    simp only [genPoch, genShift, Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons,
      pow_succ] at ih ⊢
    rw [norm_mul, mul_comm _ (4 ^ n * _)]
    exact mul_le_mul (ghbR4_poch_shift_le hr (hc x (Multiset.mem_cons_self x c)) n)
      (ih fun y hy => hc y (Multiset.mem_cons_of_mem hy)) (norm_nonneg _) (by positivity)

/-- Lower bound for a shifted multiset rising-factorial product. -/
lemma ghbR4_genPoch_shift_ge {r : ℝ} (hr : 0 < r) (c : Multiset ℂ) (hc : ∀ x ∈ c, ‖x‖ ≤ r / 2)
    (n : ℕ) : (∏ k ∈ range n, (r / 2 + k)) ^ c.card ≤ ‖genPoch (genShift c r) n‖ := by
  induction c using Multiset.induction_on with
  | empty => simp [genPoch, genShift]
  | @cons x c ih =>
    simp only [genPoch, genShift, Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons,
      pow_succ] at ih ⊢
    rw [norm_mul, mul_comm _ (∏ k ∈ range n, (r / 2 + k))]
    exact mul_le_mul (ghbR4_poch_shift_ge hr (hc x (Multiset.mem_cons_self x c)) n)
      (ih fun y hy => hc y (Multiset.mem_cons_of_mem hy)) (by positivity) (norm_nonneg _)

/-- Uniform coefficient bound for large common real shifts, p≤q. -/
lemma ghbR4_genCoeff_shift_le {r : ℝ} (hr : 0 < r) (a b : Multiset ℂ) (hab : a.card ≤ b.card)
    (ha : ∀ x ∈ a, ‖x‖ ≤ r) (hb : ∀ x ∈ b, ‖x‖ ≤ r / 2) (n : ℕ) :
    ‖genCoeff (genShift a r) (genShift b r) n‖ ≤
      (4 ^ a.card * (2 / r) ^ (b.card - a.card)) ^ n / n.factorial := by
  set P := ∏ k ∈ range n, (r / 2 + k) with hP
  have hP0 : 0 < P := prod_pos fun k _ => by positivity
  have hPge := ghbR4_P_ge hr n
  have h1 := ghbR4_genPoch_shift_le hr a ha n
  have h2 := ghbR4_genPoch_shift_ge hr b hb n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  unfold genCoeff
  rw [norm_div, norm_mul, Complex.norm_natCast]
  have hB : 0 < ‖genPoch (genShift b r) n‖ := lt_of_lt_of_le (by positivity) h2
  rw [div_le_div_iff₀ (by positivity) hf]
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hf.le
  have hsplit : P ^ b.card = P ^ (b.card - a.card) * P ^ a.card := by
    rw [← pow_add]; congr 1; omega
  have e : ((2 / r) ^ (b.card - a.card)) ^ n * ((r / 2) ^ n) ^ (b.card - a.card) = 1 := by
    rw [← pow_mul, ← pow_mul, mul_comm (b.card - a.card) n, ← mul_pow, div_mul_div_comm,
      mul_comm 2 r, div_self (by positivity), one_pow]
  calc ‖genPoch (genShift a r) n‖ ≤ (4 ^ n * P) ^ a.card := h1
    _ = (4 ^ a.card) ^ n * P ^ a.card := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm a.card n]
    _ = (4 ^ a.card) ^ n * ((2 / r) ^ (b.card - a.card)) ^ n *
          (((r / 2) ^ n) ^ (b.card - a.card) * P ^ a.card) := by
        rw [show (4 ^ a.card : ℝ) ^ n * ((2 / r) ^ (b.card - a.card)) ^ n *
          (((r / 2) ^ n) ^ (b.card - a.card) * P ^ a.card) = (4 ^ a.card) ^ n *
          (((2 / r) ^ (b.card - a.card)) ^ n * ((r / 2) ^ n) ^ (b.card - a.card)) * P ^ a.card
          by ring, e, mul_one]
    _ ≤ (4 ^ a.card) ^ n * ((2 / r) ^ (b.card - a.card)) ^ n *
          (P ^ (b.card - a.card) * P ^ a.card) := by gcongr
    _ ≤ (4 ^ a.card * (2 / r) ^ (b.card - a.card)) ^ n * ‖genPoch (genShift b r) n‖ := by
        rw [← hsplit, mul_pow]; gcongr

/-- Every full large-parameter shift for p<q, without unnecessary exclusions on the unshifted constants. -/
@[dlmf 16.11.E11]
theorem genHG_all_large_parameter_asymptotic {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (hpq : p < q) (z : ℂ) (m : ℕ) :
    Asymptotics.IsBigO atTop
      (fun r : ℝ => genHG (genShift (genParams a) r) (genShift (genParams b) r) z -
        ∑ n ∈ range m, genCoeff (genShift (genParams a) r) (genShift (genParams b) r) n * z ^ n)
      (fun r : ℝ => 1 / r ^ ((q - p) * m)) := by
  have hca : (genParams a).card = p := by simp [genParams]
  have hcb : (genParams b).card = q := by simp [genParams]
  set R0 : ℝ := 2 * (∑ i, ‖a i‖ + ∑ j, ‖b j‖) + 1 with hR0
  set K : ℝ := 4 ^ p * 2 ^ (q - p) * ‖z‖ with hK
  set S : ℝ := ∑' n : ℕ, K ^ n / n.factorial with hS
  have hK0 : 0 ≤ K := by positivity
  refine Asymptotics.IsBigO.of_bound (K ^ m * S) ?_
  filter_upwards [eventually_ge_atTop R0] with r hr
  have hsa : 0 ≤ ∑ i, ‖a i‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hsb : 0 ≤ ∑ j, ‖b j‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hr1 : 1 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have ha : ∀ x ∈ genParams a, ‖x‖ ≤ r := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (by simpa [genParams] using hx)
    have := single_le_sum (f := fun i => ‖a i‖) (fun _ _ => norm_nonneg _) (mem_univ i)
    linarith
  have hb : ∀ x ∈ genParams b, ‖x‖ ≤ r / 2 := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (by simpa [genParams] using hx)
    have := single_le_sum (f := fun i => ‖b i‖) (fun _ _ => norm_nonneg _) (mem_univ i)
    linarith
  have hreg : genDenRegular (genShift (genParams b) r) := by
    intro x hx n hxn
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    have h1 := congrArg Complex.re hxn
    simp only [add_re, ofReal_re, neg_re, natCast_re] at h1
    have h2 := (abs_re_le_norm y).trans (hb y hy)
    have h3 := neg_abs_le y.re
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hsum := genHG_hasSum_entire (a := genShift (genParams a) r) (b := genShift (genParams b) r)
    (by simp [genShift, hca, hcb]; omega) hreg z
  set c := fun n => genCoeff (genShift (genParams a) r) (genShift (genParams b) r) n * z ^ n
    with hc
  have hrem : genHG (genShift (genParams a) r) (genShift (genParams b) r) z -
      ∑ n ∈ range m, c n = ∑' n, c (n + m) := by
    rw [← hsum.tsum_eq, ← hsum.summable.sum_add_tsum_nat_add m]; ring
  rw [hrem]
  set t : ℝ := (1 / r) ^ (q - p) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := pow_le_one₀ (by positivity) (by rw [div_le_one hr0]; exact hr1)
  have hbound : ∀ n, ‖c (n + m)‖ ≤ (K * t) ^ m * (K ^ n / n.factorial) := by
    intro n
    have hco := ghbR4_genCoeff_shift_le hr0 (genParams a) (genParams b) (by omega) ha hb (n + m)
    rw [hca, hcb] at hco
    simp only [hc, norm_mul, norm_pow]
    have hKt : 4 ^ p * (2 / r) ^ (q - p) * ‖z‖ = K * t := by
      rw [hK, ht, div_eq_mul_one_div 2 r, mul_pow]; ring
    calc ‖genCoeff (genShift (genParams a) r) (genShift (genParams b) r) (n + m)‖ * ‖z‖ ^ (n + m)
        ≤ (4 ^ p * (2 / r) ^ (q - p)) ^ (n + m) / (n + m).factorial * ‖z‖ ^ (n + m) := by gcongr
      _ = (K * t) ^ (n + m) / (n + m).factorial := by rw [← hKt, mul_pow _ ‖z‖]; ring
      _ ≤ (K * t) ^ (n + m) / n.factorial := by
          gcongr
          omega
      _ = (K * t) ^ m * ((K * t) ^ n / n.factorial) := by rw [pow_add]; ring
      _ ≤ (K * t) ^ m * (K ^ n / n.factorial) := by
          gcongr
          calc K * t ≤ K * 1 := by gcongr
            _ = K := mul_one K
  have hS' := ((Real.summable_pow_div_factorial K).hasSum).mul_left ((K * t) ^ m)
  have hle := tsum_of_norm_bounded hS' hbound
  rw [← hS] at hle
  have hnorm : ‖(1 : ℝ) / r ^ ((q - p) * m)‖ = t ^ m := by
    rw [Real.norm_of_nonneg (by positivity), ht, ← pow_mul, one_div_pow]
  rw [hnorm]
  calc ‖∑' n, c (n + m)‖ ≤ (K * t) ^ m * S := hle
    _ = K ^ m * S * t ^ m := by rw [mul_pow]; ring

end DLMF.Hypergeometric
