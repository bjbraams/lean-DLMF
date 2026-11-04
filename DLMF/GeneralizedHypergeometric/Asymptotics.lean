/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.DifferentialEquations
public import DLMFMathlib.Analysis.Complex.BarnesResidue
public import TauCeti.Analysis.Contour.Residue.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.Algebra.Monoid

/-!
# Asymptotic expansions of `ₚF_q` (DLMF §16.11)

## Main definitions

* `genAsymptoticKappa`, `genAsymptoticNu`: the exponential index `κ` and exponent `ν`,
  DLMF 16.11.3.
* `genAsymptoticCRaw`, `genAsymptoticC`, `genAsymptoticEkm`: the coefficients of the
  exponential expansion, DLMF 16.11.4–16.11.5.
* `genETermLog`, `genHTermLog`: the formal exponential and algebraic series, DLMF 16.11.1–16.11.2.
* `genHResidueLog`, `genHTruncLog`: algebraic terms at arbitrary (possibly multiple) poles.

## Main results

* `genAsymptoticC_recurrence`, `genAsymptoticC_limit`: the coefficient recurrence and its
  continuation to repeated lower parameters (`genAsymptoticC_limit'` for all `p`, `q`).
* `genH_simple_residue`, `genH_resonant_log_polynomial`: algebraic terms as Barnes residues.
* `genH_balanced_converges`: convergence of the algebraic series for `p = q + 1`, `|z| > 1`,
  DLMF 16.11.6.
* `generalizedHypergeometric_equal_order_asymptotic`,
  `generalizedHypergeometric_one_lower_asymptotic`,
  `generalizedHypergeometric_fewer_upper_asymptotic`: large-`z` expansions, DLMF 16.11.7–16.11.9.
* `generalizedHypergeometric_partial_large_parameter_asymptotic`,
  `generalizedHypergeometric_all_large_parameter_asymptotic`: large-parameter expansions, DLMF
  16.11.10–16.11.11.

## Implementation notes

All powers are evaluated on a specified logarithm sheet, so the two formal exponential series at
phases `w ± πi` are not collapsed by principal argument reduction. Algebraic terms are Barnes
residues, deduplicated at resonant poles; multiple poles retain the logarithmic terms mentioned
in DLMF. The coefficient recurrence is continued through repeated lower parameters by a
specified limit. Formal `E` and `H` series are coefficient families, asserted convergent only
where DLMF claims convergence (`p = q + 1`, `|z| > 1`). Residues use the TauCeti residue API.
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
    pochhammer (1 - genAsymptoticNu a b - genAsymptoticKappa p q * genAsymptoticAugment b j + m)
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
    gammaProduct (shiftParameters (parametersOfFin b) (-a jk.1 - jk.2)) *
    Complex.exp ((-a jk.1 - jk.2) * w)

/-- The distinct upper-pole set, which does not count resonant coincidences twice. -/
def genHPoleSet {p : ℕ} (a : Fin p → ℂ) : Set ℂ :=
  {s | ∃ j : Fin p, ∃ k : ℕ, s = -a j - k}

/-- The algebraic formal term at any pole, including logarithmic multiple-pole terms. -/
def genHResidueLog {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (w s : ℂ) : ℂ :=
  TauCeti.Contour.residue (barnesKernelLog (parametersOfFin a) (parametersOfFin b) w) s

/-- A finite set of distinct algebraic poles through order N. -/
def genHPoleTrunc {p : ℕ} (a : Fin p → ℂ) (N : ℕ) : Finset ℂ := by
  classical
  exact ((Finset.univ : Finset (Fin p)).product (Finset.range N)).image
      (fun jk : Fin p × ℕ => -a jk.1 - jk.2)

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

/-- Each augmented lower parameter varies continuously with the parameter vector. -/
private lemma genAsymptoticAugment_continuous {q : ℕ} (j : Fin (q + 1)) :
    Continuous (fun b : Fin q → ℂ => genAsymptoticAugment b j) := by
  unfold genAsymptoticAugment
  split_ifs <;> fun_prop

/-- The exponential exponent is continuous in the lower parameters. -/
private lemma genAsymptoticNu_continuous {p q : ℕ} (a : Fin p → ℂ) :
    Continuous (fun b : Fin q → ℂ => genAsymptoticNu a b) := by
  unfold genAsymptoticNu
  fun_prop

/-- The finite coefficient sum is continuous where the augmented lower parameters are distinct. -/
lemma genAsymptoticEkm_continuousAt {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (hb : Function.Injective (genAsymptoticAugment b)) (k m : ℕ) :
    ContinuousAt (fun c : Fin q → ℂ => genAsymptoticEkm a c k m) b := by
  classical
  unfold genAsymptoticEkm
  apply tendsto_finsetSum
  intro j hj
  apply ContinuousAt.div
  · apply ContinuousAt.mul
    · exact (ascPochhammer ℂ _).continuous.continuousAt.comp (by
        exact (((continuous_const.sub (genAsymptoticNu_continuous a)).sub
          (continuous_const.mul (genAsymptoticAugment_continuous j))).add
              continuous_const).continuousAt)
    · apply tendsto_finsetProd
      intro i hi
      exact (continuous_const.sub (genAsymptoticAugment_continuous j)).continuousAt
  · apply tendsto_finsetProd
    intro i hi
    exact ((genAsymptoticAugment_continuous i).sub (genAsymptoticAugment_continuous j)).continuousAt
  · exact Finset.prod_ne_zero_iff.mpr fun i hi =>
      sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hi).1 (hb he))

/-- The raw finite recurrence is continuous at distinct augmented lower parameters. -/
lemma genAsymptoticCRaw_continuousAt {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (hb : Function.Injective (genAsymptoticAugment b)) (k : ℕ) :
    ContinuousAt (fun c : Fin q → ℂ => genAsymptoticCRaw a c k) b := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simpa [genAsymptoticCRaw] using (continuousAt_const :
        ContinuousAt (fun _ : Fin q → ℂ => (1 : ℂ)) b)
    | succ k =>
      simp only [genAsymptoticCRaw]
      apply ContinuousAt.div_const
      apply ContinuousAt.neg
      apply tendsto_finsetSum
      intro m hm
      exact (ih m m.isLt).mul (genAsymptoticEkm_continuousAt a b hb (k + 1) m)

/-- At distinct augmented lower parameters, the selected limiting coefficient equals
the ordinary finite recurrence coefficient. -/
lemma genAsymptoticC_eq_raw {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (hb : Function.Injective (genAsymptoticAugment b)) (k : ℕ) :
    genAsymptoticC a b k = genAsymptoticCRaw a b k := by
  have he : genAsymptoticPerturb b 0 = b := by ext j; simp [genAsymptoticPerturb]
  have hc := (genAsymptoticCRaw_continuousAt a b hb k).comp_of_eq (show ContinuousAt
    (fun ε : ℂ => genAsymptoticPerturb b ε) 0 by
      unfold genAsymptoticPerturb
      fun_prop) he
  simpa only [genAsymptoticC, Function.comp_def, he] using
    (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))).limUnder_eq

/-- The complete printed recurrence on its nonsingular augmented-parameter domain. -/
@[dlmf 16.11.E4]
theorem genAsymptoticC_recurrence {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (hb : Function.Injective (genAsymptoticAugment b)) :
    genAsymptoticC a b 0 = 1 ∧ ∀ k : ℕ, genAsymptoticC a b (k + 1) =
      -(∑ m ∈ range (k + 1), genAsymptoticC a b m * genAsymptoticEkm a b (k + 1) m) /
        ((k + 1 : ℂ) * (genAsymptoticKappa p q : ℂ) ^ genAsymptoticKappa p q) := by
  constructor
  · rw [genAsymptoticC_eq_raw a b hb, genAsymptoticCRaw]
  · intro k
    simp only [genAsymptoticC_eq_raw a b hb, genAsymptoticCRaw]
    congr 2
    exact Fin.sum_univ_eq_sum_range (fun m => genAsymptoticCRaw a b m *
      genAsymptoticEkm a b (k + 1) m) (k + 1)

/-! ### Continuation of the coefficients through repeated lower parameters -/

namespace DividedDifference

open Polynomial

/-- Products over the complement of a point as products over `succAbove`. -/
private lemma prod_erase_eq_prod_succAbove {m : ℕ} (f : Fin (m + 1) → ℂ) (j : Fin (m + 1)) :
    ∏ i ∈ univ.erase j, f i = ∏ i : Fin m, f (j.succAbove i) := by
  classical
  have h := Fin.prod_univ_succAbove (fun i => if i = j then 1 else f i) j
  rw [← Finset.mul_prod_erase univ _ (mem_univ j)] at h
  simp only [↓reduceIte, one_mul] at h
  rw [show ∏ i ∈ univ.erase j, f i = ∏ i ∈ univ.erase j, (if i = j then 1 else f i) from
    prod_congr rfl fun i hi => by simp [ne_of_mem_erase hi], h]
  exact prod_congr rfl fun i _ => by simp [Fin.succAbove_ne j i]

/-- Splitting off the node `0` from a product over the complement of `k.succ`. -/
private lemma prod_erase_succ {m : ℕ} (f : Fin (m + 1) → ℂ) (k : Fin m) :
    ∏ i ∈ univ.erase k.succ, f i = f 0 * ∏ i ∈ univ.erase k, f i.succ := by
  cases m with
  | zero => exact k.elim0
  | succ m =>
    rw [prod_erase_eq_prod_succAbove, prod_erase_eq_prod_succAbove, Fin.prod_univ_succ,
      Fin.succ_succAbove_zero]
    simp only [Fin.succ_succAbove_succ]

/-- The divided-difference sum of the monomial `X ^ d` at the nodes `x`. -/
private noncomputable def monomialSum {n : ℕ} (d : ℕ) (x : Fin n → ℂ) : ℂ :=
  ∑ j, x j ^ d / ∏ i ∈ univ.erase j, (x j - x i)

private lemma monomialSum_succ {m : ℕ} (d : ℕ) (x : Fin (m + 1) → ℂ) (hx : Function.Injective x) :
    monomialSum (d + 1) x = monomialSum d (Fin.tail x) + x 0 * monomialSum d x := by
  have hsplit : monomialSum (d + 1) x =
      ∑ j, x j ^ d * (x j - x 0) / ∏ i ∈ univ.erase j, (x j - x i) + x 0 * monomialSum d x := by
    rw [monomialSum, monomialSum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [hsplit, Fin.sum_univ_succ, sub_self, mul_zero, zero_div, zero_add]
  congr 1
  rw [monomialSum]
  refine sum_congr rfl fun k _ => ?_
  rw [prod_erase_succ (fun i => x k.succ - x i)]
  have hne : x k.succ - x 0 ≠ 0 := sub_ne_zero.mpr (hx.ne (Fin.succ_ne_zero k))
  simp only [Fin.tail]
  field_simp


private lemma exists_continuous_monomialSum (n d : ℕ) :
    ∃ Q : (Fin n → ℂ) → ℂ, Continuous Q ∧
      ∀ x, Function.Injective x → monomialSum d x = Q x := by
  induction n generalizing d with
  | zero => exact ⟨fun _ => 0, continuous_const, fun x _ => by simp [monomialSum]⟩
  | succ m ihm =>
    induction d with
    | zero =>
      refine ⟨fun _ => (1 : Polynomial ℂ).coeff m, continuous_const, fun x hx => ?_⟩
      have h := Lagrange.coeff_eq_sum (s := (univ : Finset (Fin (m + 1)))) (v := x)
        hx.injOn (P := 1) (by simp; positivity)
      simp only [card_univ, Fintype.card_fin, Nat.add_sub_cancel, Polynomial.eval_one] at h
      rw [h, monomialSum]
      simp
    | succ d ihd =>
      obtain ⟨Q₁, hQ₁, hQ₁e⟩ := ihm d
      obtain ⟨Q₂, hQ₂, hQ₂e⟩ := ihd
      refine ⟨fun x => Q₁ (Fin.tail x) + x 0 * Q₂ x, ?_, fun x hx => ?_⟩
      · have ht : Continuous (fun x : Fin (m + 1) → ℂ => Fin.tail x) := by
          unfold Fin.tail; fun_prop
        exact (hQ₁.comp ht).add ((continuous_apply 0).mul hQ₂)
      · rw [monomialSum_succ d x hx, hQ₁e (Fin.tail x) (hx.comp (Fin.succ_injective m)), hQ₂e x hx]

/-- The divided-difference sum of a polynomial as a combination of monomial sums. -/
private lemma sum_eval_div_eq {n N : ℕ} (P : Polynomial ℂ) (hP : P.natDegree < N) (x : Fin n → ℂ) :
    ∑ j, P.eval (x j) / ∏ i ∈ univ.erase j, (x j - x i) =
      ∑ d ∈ Finset.range N, P.coeff d * monomialSum d x := by
  simp_rw [monomialSum, mul_sum, Polynomial.eval_eq_sum_range' hP, sum_div]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun d _ => ?_
  ring

/-- Coefficients of a family of polynomials of bounded degree depending continuously on a
parameter at every point are continuous in the parameter. -/
private lemma continuous_coeff {N : ℕ} (P : ℂ → Polynomial ℂ) (hP : ∀ ε, (P ε).natDegree < N)
    (hc : ∀ t, Continuous fun ε => (P ε).eval t) (d : ℕ) :
    Continuous fun ε => (P ε).coeff d := by
  have hinj : Set.InjOn (fun i : ℕ => (i : ℂ)) (Finset.range N) :=
    fun i _ j _ h => by simpa using h
  have he : ∀ ε, (P ε).coeff d = ∑ i ∈ Finset.range N,
      (P ε).eval (i : ℂ) * (Lagrange.basis (Finset.range N) (fun i : ℕ => (i : ℂ)) i).coeff d := by
    intro ε
    have hdeg : (P ε).degree < (Finset.range N).card := by
      rw [card_range]
      exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hP ε)
    conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg]
    rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul]
  simp_rw [he]
  exact continuous_finsetSum _ fun i _ => (hc _).mul continuous_const

/-- Divided-difference sums of continuously varying polynomials at continuously varying nodes
agree, at distinct nodes, with a continuous function. -/
private lemma exists_continuous_sum_eval_div {n N : ℕ} (P : ℂ → Polynomial ℂ)
    (hP : ∀ ε, (P ε).natDegree < N) (hc : ∀ t, Continuous fun ε => (P ε).eval t)
    (x : ℂ → Fin n → ℂ) (hx : Continuous x) :
    ∃ G : ℂ → ℂ, Continuous G ∧ ∀ ε, Function.Injective (x ε) →
      ∑ j, (P ε).eval (x ε j) / ∏ i ∈ univ.erase j, (x ε j - x ε i) = G ε := by
  choose Q hQ hQe using fun d => exists_continuous_monomialSum n d
  refine ⟨fun ε => ∑ d ∈ Finset.range N, (P ε).coeff d * Q d (x ε), ?_, fun ε hε => ?_⟩
  · exact continuous_finsetSum _ fun d _ =>
      (continuous_coeff P hP hc d).mul ((hQ d).comp hx)
  · rw [sum_eval_div_eq (P ε) (hP ε)]
    exact sum_congr rfl fun d _ => by rw [hQe d _ hε]

end DividedDifference

namespace CoefficientLimit

open Polynomial DividedDifference

private lemma eventually_affine_ne_zero (α β : ℂ) (hβ : β ≠ 0) :
    ∀ᶠ ε in 𝓝[≠] (0 : ℂ), α + β * ε ≠ 0 := by
  by_cases hα : α = 0
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa [hα] using mul_ne_zero hβ hε
  · have ht : Tendsto (fun ε : ℂ => α + β * ε) (𝓝 0) (𝓝 α) := by
      have hc : Continuous (fun ε : ℂ => α + β * ε) := by fun_prop
      have h0 := hc.tendsto 0
      rwa [mul_zero, add_zero] at h0
    exact (ht.eventually_ne hα).filter_mono nhdsWithin_le_nhds

/-- Slopes of the perturbed augmented parameters. -/
private def augmentSlope (q : ℕ) (j : Fin (q + 1)) : ℂ := if j.val < q then (j.val + 1 : ℂ) else 0

private lemma augment_perturb {q : ℕ} (b : Fin q → ℂ) (ε : ℂ) (j : Fin (q + 1)) :
    genAsymptoticAugment (genAsymptoticPerturb b ε) j =
      genAsymptoticAugment b j + augmentSlope q j * ε := by
  unfold genAsymptoticAugment augmentSlope genAsymptoticPerturb
  split_ifs <;> simp

private lemma augmentSlope_injective (q : ℕ) : Function.Injective (augmentSlope q) := by
  intro i j h
  unfold augmentSlope at h
  apply Fin.ext
  split_ifs at h with hi hj hj
  · have : ((i.val : ℕ) : ℂ) = (j.val : ℕ) := by linear_combination h
    exact_mod_cast this
  · exact absurd h (by norm_cast)
  · exact absurd h.symm (by norm_cast)
  · omega

private lemma eventually_injective_augment {q : ℕ} (b : Fin q → ℂ) :
    ∀ᶠ ε in 𝓝[≠] (0 : ℂ),
      Function.Injective (genAsymptoticAugment (genAsymptoticPerturb b ε)) := by
  have h : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), ∀ ij : Fin (q + 1) × Fin (q + 1), ij.1 ≠ ij.2 →
      genAsymptoticAugment (genAsymptoticPerturb b ε) ij.1 ≠
        genAsymptoticAugment (genAsymptoticPerturb b ε) ij.2 := by
    rw [eventually_all]
    rintro ⟨i, j⟩
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => absurd hij h
    · filter_upwards [eventually_affine_ne_zero
        (genAsymptoticAugment b i - genAsymptoticAugment b j)
        (augmentSlope q i - augmentSlope q j)
        (sub_ne_zero.mpr ((augmentSlope_injective q).ne hij))] with ε hε _
      rw [augment_perturb, augment_perturb]
      intro he
      apply hε
      linear_combination he
  filter_upwards [h] with ε hε i j he
  by_contra hne
  exact hε (i, j) hne he

private lemma continuous_augment_perturb {q : ℕ} (b : Fin q → ℂ) :
    Continuous fun ε : ℂ => genAsymptoticAugment (genAsymptoticPerturb b ε) := by
  refine continuous_pi fun j => ?_
  simp_rw [augment_perturb]
  fun_prop

private lemma continuous_nu_perturb {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) :
    Continuous fun ε : ℂ => genAsymptoticNu a (genAsymptoticPerturb b ε) := by
  unfold genAsymptoticNu genAsymptoticPerturb
  fun_prop

private lemma exists_continuous_ekm {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (k m : ℕ) :
    ∃ G : ℂ → ℂ, Continuous G ∧ ∀ ε,
      Function.Injective (genAsymptoticAugment (genAsymptoticPerturb b ε)) →
        genAsymptoticEkm a (genAsymptoticPerturb b ε) k m = G ε := by
  set M := genAsymptoticKappa p q + k - m
  set κ : ℂ := (genAsymptoticKappa p q : ℂ)
  set ν := fun ε : ℂ => genAsymptoticNu a (genAsymptoticPerturb b ε)
  let P : ℂ → Polynomial ℂ := fun ε => C ((-1 : ℂ) ^ q) *
    (ascPochhammer ℂ M).comp (C (1 - ν ε + m) - C κ * X) * ∏ i, (C (a i) - X)
  have hdeg : ∀ ε, (P ε).natDegree < M + p + 1 := by
    intro ε
    refine Nat.lt_succ_of_le ?_
    refine (natDegree_mul_le).trans (add_le_add ?_ ?_)
    · refine (natDegree_C_mul_le _ _).trans ((natDegree_comp_le).trans ?_)
      rw [ascPochhammer_natDegree]
      have h1 : (C (1 - ν ε + m) - C κ * X).natDegree ≤ 1 := by compute_degree
      nlinarith
    · refine (Polynomial.natDegree_prod_le (s := univ) (f := fun i => C (a i) - X)).trans ?_
      have h2 : ∀ i, (C (a i) - X).natDegree ≤ 1 := fun i => by compute_degree
      calc ∑ i, (C (a i) - X).natDegree ≤ ∑ _i : Fin p, 1 :=
            Finset.sum_le_sum (f := fun i => (C (a i) - X).natDegree) (g := fun _ => 1)
              fun i _ => h2 i
        _ = p := by simp
  have heval : ∀ ε t, (P ε).eval t =
      (-1 : ℂ) ^ q * pochhammer (1 - ν ε - κ * t + m) M * ∏ i, (a i - t) := by
    intro ε t
    simp only [P, eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_prod, pochhammer]
    congr 3
    ring
  have hc : ∀ t, Continuous fun ε => (P ε).eval t := by
    intro t
    simp_rw [heval]
    have := continuous_nu_perturb a b
    exact (continuous_const.mul ((ascPochhammer ℂ M).continuous.comp
      (((continuous_const.sub this).sub continuous_const).add continuous_const))).mul
        continuous_const
  obtain ⟨G, hG, hGe⟩ := exists_continuous_sum_eval_div P hdeg hc _
    (continuous_augment_perturb b)
  refine ⟨G, hG, fun ε hε => ?_⟩
  rw [← hGe ε hε, genAsymptoticEkm]
  refine sum_congr rfl fun j _ => ?_
  rw [heval]
  have hprod : ∏ i ∈ univ.erase j, (genAsymptoticAugment (genAsymptoticPerturb b ε) i -
      genAsymptoticAugment (genAsymptoticPerturb b ε) j) = (-1 : ℂ) ^ q *
      ∏ i ∈ univ.erase j, (genAsymptoticAugment (genAsymptoticPerturb b ε) j -
        genAsymptoticAugment (genAsymptoticPerturb b ε) i) := by
    rw [show (-1 : ℂ) ^ q = ∏ _i ∈ univ.erase j, (-1 : ℂ) by simp, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => by ring
  rw [hprod]
  have hs : ((-1 : ℂ) ^ q) ^ 2 = 1 := by rw [← pow_mul, pow_mul']; norm_num
  have hne : ∏ i ∈ univ.erase j, (genAsymptoticAugment (genAsymptoticPerturb b ε) j -
        genAsymptoticAugment (genAsymptoticPerturb b ε) i) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i hi => sub_ne_zero.mpr (fun he => (mem_erase.mp hi).1 (hε he).symm)
  have h1 : ((-1 : ℂ) ^ q) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  rw [hs, mul_one, mul_comm]
  congr 2
  simp only [ν, κ]
  ring

private lemma exists_continuous_cRaw {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (k : ℕ) :
    ∃ G : ℂ → ℂ, Continuous G ∧
      ∀ᶠ ε in 𝓝[≠] (0 : ℂ), genAsymptoticCRaw a (genAsymptoticPerturb b ε) k = G ε := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => exact ⟨fun _ => 1, continuous_const, Eventually.of_forall fun ε => by
        simp [genAsymptoticCRaw]⟩
    | succ k =>
      choose C hC hCe using fun m : Fin (k + 1) => ih m.val (by omega)
      choose E hE hEe using fun m : Fin (k + 1) => exists_continuous_ekm a b (k + 1) m.val
      refine ⟨fun ε => -(∑ m : Fin (k + 1), C m ε * E m ε) /
        ((k + 1 : ℂ) * (genAsymptoticKappa p q : ℂ) ^ genAsymptoticKappa p q), ?_, ?_⟩
      · exact ((continuous_finsetSum _ fun m _ => (hC m).mul (hE m)).neg).div_const _
      · have hall : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), ∀ m : Fin (k + 1),
            genAsymptoticCRaw a (genAsymptoticPerturb b ε) m.val = C m ε :=
          eventually_all.mpr hCe
        filter_upwards [hall, eventually_injective_augment b] with ε hε hinj
        rw [genAsymptoticCRaw]
        congr 2
        exact sum_congr rfl fun m _ => by rw [hε m, hEe m ε hinj]

end CoefficientLimit

/-- All repeated lower-parameter cases have the finite limiting coefficient, for all `p` and `q`.
Stronger than DLMF, which assumes `p < q + 1`. -/
@[dlmf 16.11.E4, dlmf 16.11.E5]
theorem genAsymptoticC_limit' {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (k : ℕ) :
    Tendsto (fun ε : ℂ => genAsymptoticCRaw a (genAsymptoticPerturb b ε) k)
      (𝓝[≠] 0) (𝓝 (genAsymptoticC a b k)) := by
  obtain ⟨G, hG, hGe⟩ := CoefficientLimit.exists_continuous_cRaw a b k
  have ht : Tendsto (fun ε : ℂ => genAsymptoticCRaw a (genAsymptoticPerturb b ε) k)
      (𝓝[≠] 0) (𝓝 (G 0)) :=
    ((hG.tendsto 0).mono_left nhdsWithin_le_nhds).congr' (hGe.mono fun ε h => h.symm)
  rwa [genAsymptoticC, ht.limUnder_eq]

/-- All repeated lower-parameter cases have the finite limiting coefficient. -/
@[dlmf 16.11.E4, dlmf 16.11.E5]
theorem genAsymptoticC_limit {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (_hpq : p < q + 1)
    (k : ℕ) :
    Tendsto (fun ε : ℂ => genAsymptoticCRaw a (genAsymptoticPerturb b ε) k)
      (𝓝[≠] 0) (𝓝 (genAsymptoticC a b k)) :=
  genAsymptoticC_limit' a b k

/-- Gamma is analytic away from its poles. -/
private lemma analyticAt_Gamma_of_ne_neg_nat {c : ℂ} (hc : ∀ m : ℕ, c ≠ -m) : AnalyticAt
    ℂ Gamma c := by
  have hU : IsOpen {s : ℂ | ∀ m : ℕ, s ≠ -m} := by
    simpa using BarnesResidue.isOpen_ne_sub_nat (0 : ℂ)
  exact DifferentiableOn.analyticAt
      (fun s hs => (differentiableAt_Gamma s hs).differentiableWithinAt)
    (hU.mem_nhds hc)

/-- Local pole factor of Gamma at `-m`. -/
noncomputable def gammaPoleFactor (m : ℕ) (x : ℂ) : ℂ :=
  Gamma (x + m + 1) / ∏ k ∈ range m, (x + k)

/-- The pole factor is analytic at its pole. -/
private lemma analyticAt_gammaPoleFactor (m : ℕ) :
    AnalyticAt ℂ (gammaPoleFactor m) (-m) := by
  unfold gammaPoleFactor
  apply AnalyticAt.div
  · have h1 : AnalyticAt ℂ Gamma ((-(m : ℂ)) + m + 1) := by
      rw [show (-(m : ℂ)) + m + 1 = 1 by ring]
      exact analyticAt_Gamma_of_ne_neg_nat (fun k hk => by
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
private lemma gammaPoleFactor_neg_nat (m : ℕ) :
    gammaPoleFactor m (-m) = (-1) ^ m / m.factorial := by
  unfold gammaPoleFactor
  rw [show (-(m : ℂ)) + m + 1 = 1 by ring, Gamma_one]
  have : ∏ k ∈ range m, (-(m : ℂ) + k) = (-1) ^ m * m.factorial := by
    rw [← BarnesResidue.prod_sub_nat]; exact prod_congr rfl fun k _ => by ring
  rw [this]
  have h1 : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; simp
  have h2 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  field_simp
  linear_combination (-1) * h1

/-- Near `-m`, Gamma is `(x+m)^(-1)` times the pole factor. -/
private lemma Gamma_eq_zpow_mul_gammaPoleFactor (m : ℕ) :
    ∀ᶠ x in 𝓝[≠] (-(m : ℂ)), Gamma x = (x - (-(m : ℂ))) ^ (-1 : ℤ) * gammaPoleFactor m x := by
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
  have hG := BarnesResidue.Gamma_add_nat_succ x m hnp
  unfold gammaPoleFactor
  rw [hG, prod_range_succ]
  have hxm : x + m ≠ 0 := hnp m le_rfl
  have hprod : ∏ k ∈ range m, (x + k) ≠ 0 :=
    prod_ne_zero_iff.mpr fun k hk => hnp k (by have := Finset.mem_range.mp hk; omega)
  rw [show x - -(m : ℂ) = x + m by ring, zpow_neg_one]
  field_simp

/-- Gamma with its possible simple pole at `c` removed. -/
noncomputable def poleRemovedGamma (c : ℂ) (x : ℂ) : ℂ := by
  classical
  exact if h : ∃ m : ℕ, c = -m then gammaPoleFactor h.choose x else Gamma x

/-- The pole exponent of Gamma at `c`. -/
noncomputable def gammaPoleOrder (c : ℂ) : ℕ := by
  classical
  exact if ∃ m : ℕ, c = -m then 1 else 0

/-- The pole-removed Gamma function is analytic at its base point. -/
private lemma analyticAt_poleRemovedGamma (c : ℂ) : AnalyticAt ℂ (poleRemovedGamma c) c := by
  classical
  unfold poleRemovedGamma
  split_ifs with h
  · have := analyticAt_gammaPoleFactor h.choose
    rwa [← h.choose_spec] at this
  · push Not at h
    exact analyticAt_Gamma_of_ne_neg_nat h

/-- Gamma times its local pole power is the pole-removed Gamma function. -/
private lemma Gamma_mul_pow_gammaPoleOrder_eq (c : ℂ) :
    ∀ᶠ x in 𝓝[≠] c, Gamma x * (x - c) ^ gammaPoleOrder c = poleRemovedGamma c x := by
  classical
  unfold poleRemovedGamma gammaPoleOrder
  split_ifs with h
  · have hc := h.choose_spec
    have := Gamma_eq_zpow_mul_gammaPoleFactor h.choose
    rw [← hc] at this
    filter_upwards [this, self_mem_nhdsWithin] with x hx hne
    have hne : x - c ≠ 0 := sub_ne_zero.mpr hne
    rw [hx, zpow_neg_one, pow_one]
    field_simp
  · exact Eventually.of_forall fun x => by simp

/-- Value of the pole-removed Gamma function at a pole. -/
private lemma poleRemovedGamma_neg_nat (m : ℕ) :
    poleRemovedGamma (-(m : ℂ)) (-(m : ℂ)) = (-1) ^ m / m.factorial := by
  classical
  unfold poleRemovedGamma
  split_ifs with h
  · have hk : h.choose = m := by
      have := h.choose_spec
      exact_mod_cast (neg_inj.mp this).symm
    rw [hk, gammaPoleFactor_neg_nat]
  · exact absurd ⟨m, rfl⟩ h

/-- Away from poles nothing is removed. -/
private lemma poleRemovedGamma_of_ne_neg_nat {c : ℂ} (hc : ∀ m : ℕ, c ≠ -m) :
    poleRemovedGamma c = Gamma := by
  classical
  unfold poleRemovedGamma
  funext x
  split_ifs with h
  · obtain ⟨m, hm⟩ := h; exact absurd hm (hc m)
  · rfl

/-- The pole exponent vanishes away from poles. -/
private lemma gammaPoleOrder_of_ne_neg_nat {c : ℂ} (hc : ∀ m : ℕ, c ≠ -m) :
    gammaPoleOrder c = 0 := by
  classical
  unfold gammaPoleOrder
  split_ifs with h
  · obtain ⟨m, hm⟩ := h; exact absurd hm (hc m)
  · rfl

/-- The pole exponent is one at a pole. -/
private lemma gammaPoleOrder_neg_nat (m : ℕ) : gammaPoleOrder (-(m : ℂ)) = 1 := by
  classical
  unfold gammaPoleOrder
  split_ifs with h
  · rfl
  · exact absurd ⟨m, rfl⟩ h

/-- Local factorization of a finite Gamma product near any point. -/
private lemma prod_Gamma_mul_pow_eq_prod_poleRemovedGamma {p : ℕ} (a : Fin p → ℂ) (s₀ : ℂ) :
    ∀ᶠ s in 𝓝[≠] s₀, (∏ i, Gamma (a i + s)) * (s - s₀) ^ (∑ i, gammaPoleOrder (a i + s₀)) =
      ∏ i, poleRemovedGamma (a i + s₀) (a i + s) := by
  have hmap : ∀ i, Tendsto (fun s => a i + s) (𝓝[≠] s₀) (𝓝[≠] (a i + s₀)) := by
    intro i
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((continuous_const.add continuous_id).tendsto s₀).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      intro h; exact hs (add_left_cancel h)
  have hall : ∀ᶠ s in 𝓝[≠] s₀, ∀ i, Gamma (a i + s) * (s - s₀) ^ gammaPoleOrder (a i + s₀) =
      poleRemovedGamma (a i + s₀) (a i + s) := by
    rw [eventually_all]
    intro i
    filter_upwards [hmap i (Gamma_mul_pow_gammaPoleOrder_eq (a i + s₀))] with s hs
    rw [← hs]; congr 2; ring
  filter_upwards [hall] with s hs
  rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  exact prod_congr rfl fun i _ => hs i

/-- A shifted parameter Gamma product as a finite product. -/
private lemma gammaProduct_shiftParameters_parametersOfFin {p : ℕ} (a : Fin p → ℂ) (s : ℂ) :
    gammaProduct (shiftParameters (parametersOfFin a) s) = ∏ i, Gamma (a i + s) := by
  simp [gammaProduct, shiftParameters, parametersOfFin, List.map_ofFn, List.prod_ofFn,
      Function.comp_def]

/-- The reciprocal lower Gamma block of the Barnes kernel is entire. -/
private lemma analyticAt_inv_gammaProduct_shiftParameters {q : ℕ} (b : Fin q → ℂ) (s₀ : ℂ) :
    AnalyticAt ℂ (fun s => (gammaProduct (shiftParameters (parametersOfFin b) s))⁻¹) s₀ := by
  simp only [gammaProduct_shiftParameters_parametersOfFin, ← prod_inv_distrib]
  apply Finset.analyticAt_fun_prod
  intro i _
  have h : Differentiable ℂ (fun s : ℂ => (Gamma s)⁻¹) := by
    simpa [one_div] using differentiable_one_div_Gamma
  exact (h.analyticAt (b i + s₀)).comp_of_eq (f := fun s => b i + s) (by fun_prop) rfl

/-- The Barnes kernel near a point, after removing all Gamma poles from the upper block. -/
private lemma barnesKernelLog_eq_zpow_smul_poleRemoved {p q : ℕ} (a : Fin p → ℂ)
    (b : Fin q → ℂ) (w s₀ : ℂ) :
    ∀ᶠ s in 𝓝[≠] s₀, barnesKernelLog (parametersOfFin a) (parametersOfFin b) w s =
      (s - s₀) ^ (-((∑ i, gammaPoleOrder (a i + s₀) : ℕ) : ℤ)) •
        ((∏ i, poleRemovedGamma (a i + s₀) (a i + s)) *
          (gammaProduct (shiftParameters (parametersOfFin b) s))⁻¹ * Gamma (-s) *
              Complex.exp (s * w)) := by
  filter_upwards [prod_Gamma_mul_pow_eq_prod_poleRemovedGamma a s₀,
      self_mem_nhdsWithin] with s hs hne
  have hne : s - s₀ ≠ 0 := sub_ne_zero.mpr hne
  rw [← hs, barnesKernelLog, gammaProduct_shiftParameters_parametersOfFin, zpow_neg,
      zpow_natCast, smul_eq_mul]
  field_simp

/-- Each vector parameter belongs to its multiset. -/
private lemma mem_parametersOfFin {p : ℕ} (a : Fin p → ℂ) (i : Fin p) : a i ∈
    parametersOfFin a := by
  simp [parametersOfFin]

/-- The reflected Gamma factor is regular at every upper pole. -/
private lemma analyticAt_Gamma_neg_of_upper_pole {p : ℕ} (a : Fin p → ℂ)
    (ha : LowerParametersRegular (parametersOfFin a))
    (j : Fin p) (k : ℕ) : AnalyticAt ℂ (fun s => Gamma (-s)) (-a j - k) := by
  have hnp : ∀ m : ℕ, -(-a j - k) ≠ -m := by
    intro m h
    apply ha (a j) (mem_parametersOfFin a j) (m + k)
    push_cast; linear_combination h
  exact (analyticAt_Gamma_of_ne_neg_nat hnp).comp_of_eq (f := fun s => -s) (by fun_prop) rfl

/-- The pole-removed Barnes kernel is analytic at an upper pole. -/
private lemma analyticAt_poleRemoved_barnesKernel {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (ha : LowerParametersRegular (parametersOfFin a))
    (j : Fin p) (k : ℕ) (w : ℂ) :
    AnalyticAt ℂ (fun s => (∏ i, poleRemovedGamma (a i + (-a j - k)) (a i + s)) *
      (gammaProduct (shiftParameters (parametersOfFin b) s))⁻¹ * Gamma (-s) *
          Complex.exp (s * w)) (-a j - k) := by
  have h1 : AnalyticAt ℂ (fun s => ∏ i, poleRemovedGamma (a i + (-a j - k)) (a i + s))
      (-a j - k) := by
    apply Finset.analyticAt_fun_prod
    intro i _
    exact (analyticAt_poleRemovedGamma _).comp_of_eq (f := fun s => a i + s) (by fun_prop) rfl
  exact ((h1.mul (analyticAt_inv_gammaProduct_shiftParameters b _)).mul
    (analyticAt_Gamma_neg_of_upper_pole a ha j k)).mul (by fun_prop)

/-- Gamma poles are simple. -/
private lemma gammaPoleOrder_le_one (c : ℂ) : gammaPoleOrder c ≤ 1 := by
  classical
  unfold gammaPoleOrder; split_ifs <;> omega

/-- The algebraic coefficients equal the corresponding simple Barnes residues. -/
@[dlmf 16.11.E2]
theorem genH_simple_residue {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (ha : LowerParametersRegular (parametersOfFin a))
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
  have hN : ∑ i, gammaPoleOrder (a i + s₀) = 1 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hj, gammaPoleOrder_neg_nat,
      Finset.sum_eq_zero (fun i hi =>
          gammaPoleOrder_of_ne_neg_nat (hnp i (Finset.ne_of_mem_erase hi)))]
    rfl
  have hloc := barnesKernelLog_eq_zpow_smul_poleRemoved a b w s₀
  rw [hN] at hloc
  unfold genHResidueLog
  rw [TauCeti.Contour.residue_eq_of_eventuallyEq_zpow_smul (by norm_num)
    (analyticAt_poleRemoved_barnesKernel a b ha j k w) hloc]
  norm_num
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  rw [hj, poleRemovedGamma_neg_nat]
  rw [Finset.prod_congr rfl (fun i hi => by
    rw [poleRemovedGamma_of_ne_neg_nat (hnp i (Finset.ne_of_mem_erase hi))])]
  unfold genHTermLog
  rw [add_comm (k : ℂ) (a j)]
  rw [Finset.prod_congr rfl (fun i _ => by rw [show a i + (-a j - k) = a i - a j - k by ring])]
  simp only [div_eq_mul_inv]
  ring

/-- A repeated pole contributes an exponential times a polynomial in the logarithm. -/
theorem genH_resonant_log_polynomial {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (ha : LowerParametersRegular (parametersOfFin a)) {s : ℂ} (hs : s ∈ genHPoleSet a) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ p - 1 ∧
      ∀ w : ℂ, genHResidueLog a b w s = Complex.exp (s * w) * P.eval w := by
  classical
  obtain ⟨j, k, rfl⟩ := hs
  set s₀ := -a j - k with hs₀
  set N := ∑ i, gammaPoleOrder (a i + s₀) with hNdef
  have hj : a j + s₀ = -(k : ℂ) := by rw [hs₀]; ring
  have hN1 : 1 ≤ N := by
    have := Finset.single_le_sum (f := fun i => gammaPoleOrder (a i + s₀))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [hj, gammaPoleOrder_neg_nat] at this
    exact this
  have hNp : N ≤ p := by
    calc N ≤ ∑ _i : Fin p, 1 := Finset.sum_le_sum fun i _ => gammaPoleOrder_le_one _
      _ = p := by simp
  set G0 : ℂ → ℂ := fun s => (∏ i, poleRemovedGamma (a i + s₀) (a i + s)) *
      (gammaProduct (shiftParameters (parametersOfFin b) s))⁻¹ * Gamma (-s) with hG0
  have hG0a : AnalyticAt ℂ G0 s₀ := by
    have h1 : AnalyticAt ℂ (fun s => ∏ i, poleRemovedGamma (a i + s₀) (a i + s)) s₀ := by
      apply Finset.analyticAt_fun_prod
      intro i _
      exact (analyticAt_poleRemovedGamma _).comp_of_eq (f := fun s => a i + s) (by fun_prop) rfl
    exact (h1.mul (analyticAt_inv_gammaProduct_shiftParameters b _)).mul
        (analyticAt_Gamma_neg_of_upper_pole a ha j k)
  set n := N - 1 with hn
  refine ⟨∑ i ∈ range (n + 1), Polynomial.C ((n.choose i : ℂ) * iteratedDeriv i G0 s₀ /
    n.factorial) * Polynomial.X ^ (n - i), ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    omega
  · intro w
    have hloc := barnesKernelLog_eq_zpow_smul_poleRemoved a b w s₀
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

/-- The full H residue series converges to the continued function at |z|>1, including resonances and
both closed cut sides. -/
@[dlmf 16.11.E6]
theorem genH_balanced_converges {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (ha : LowerParametersRegular (parametersOfFin a))
        (hb : LowerParametersRegular (parametersOfFin b))
    {w : ℂ} (hr : 0 < w.re) (hi : |w.im| ≤ Real.pi) :
    HasSum (fun s : genHPoleSet a => genHResidueLog a b w s)
      (gammaProduct (parametersOfFin a) / gammaProduct (parametersOfFin b) *
        genHGNegativeLog (parametersOfFin a) (parametersOfFin b) w) := by
  sorry

/-- All orders of the equal-order expansion, with the full phase convention and resonant residues.
-/
@[dlmf 16.11.E7]
theorem generalizedHypergeometric_equal_order_asymptotic {q : ℕ} (a b : Fin q → ℂ)
    (ha : LowerParametersRegular (parametersOfFin a))
        (hb : LowerParametersRegular (parametersOfFin b))
    (N : ℕ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Asymptotics.IsBigO (genInfinityLogHalf ε)
      (fun w => gammaProduct (parametersOfFin a) / gammaProduct (parametersOfFin b) *
        generalizedHypergeometric (parametersOfFin a) (parametersOfFin b) (Complex.exp w) -
        genHTruncLog a b (w - ε * Real.pi * I) N - ∑ k ∈ range N, genETermLog a b w k)
      (fun w => genHScaleLog a (w - ε * Real.pi * I) N + ‖genEScaleLog a b w N‖) := by
  sorry

/-- All orders with p=q−1, both shifted E branches, and the full algebraic residue series. -/
@[dlmf 16.11.E8]
theorem generalizedHypergeometric_one_lower_asymptotic {p : ℕ} (a : Fin p → ℂ) (b : Fin (p + 1) → ℂ)
    (ha : LowerParametersRegular (parametersOfFin a))
        (hb : LowerParametersRegular (parametersOfFin b)) (N : ℕ) :
    Asymptotics.IsBigO (DLMF.Core.logSector Real.pi)
      (fun w => gammaProduct (parametersOfFin a) / gammaProduct (parametersOfFin b) *
        generalizedHypergeometric (parametersOfFin a) (parametersOfFin b) (-Complex.exp w) -
            genHTruncLog a b w N -
        ∑ k ∈ range N, (genETermLog a b (w - Real.pi * I) k + genETermLog a b (w + Real.pi * I) k))
      (fun w => genHScaleLog a w N + ‖genEScaleLog a b (w - Real.pi * I) N‖ +
        ‖genEScaleLog a b (w + Real.pi * I) N‖) := by
  sorry

/-- All orders with p≤q−2 on the full principal sector, with both E branch contributions. -/
@[dlmf 16.11.E9]
theorem generalizedHypergeometric_fewer_upper_asymptotic {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (hpq : p + 2 ≤ q)
    (ha : LowerParametersRegular (parametersOfFin a))
        (hb : LowerParametersRegular (parametersOfFin b)) (N : ℕ) :
    Asymptotics.IsBigO (DLMF.Core.logSector Real.pi)
      (fun w => gammaProduct (parametersOfFin a) / gammaProduct (parametersOfFin b) *
        generalizedHypergeometric (parametersOfFin a) (parametersOfFin b) (-Complex.exp w) -
        ∑ k ∈ range N, (genETermLog a b (w - Real.pi * I) k + genETermLog a b (w + Real.pi * I) k))
      (fun w => ‖genEScaleLog a b (w - Real.pi * I) N‖ +
        ‖genEScaleLog a b (w + Real.pi * I) N‖) := by
  sorry

/-- Every printed partial large-parameter shift, with unrestricted shifted bottoms and the full
principal z domain. -/
@[dlmf 16.11.E10]
theorem generalizedHypergeometric_partial_large_parameter_asymptotic {p : ℕ} (a : Fin (p + 1) → ℂ)
    (b : Fin p → ℂ)
    {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ p)
    (hb : ∀ j : Fin p, k ≤ j.val → ∀ n : ℕ, b j ≠ -n)
    {z : ℂ} (hz : z ∈ cutPlane) (m : ℕ) :
    Asymptotics.IsBigO atTop
      (fun r : ℝ => generalizedHypergeometric (parametersOfFin (genPartialShift a (k - 1) r))
        (parametersOfFin (genPartialShift b k r)) z -
        ∑ n ∈ range m, generalizedHypergeometricCoeff
            (parametersOfFin (genPartialShift a (k - 1) r))
          (parametersOfFin (genPartialShift b k r)) n * z ^ n)
      (fun r : ℝ => 1 / r ^ m) := by
  sorry

/-- The comparison product `∏_{k<n} (r/2+k)` dominates `(r/2)^n`. -/
private lemma pow_le_prod_half_add {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (r / 2) ^ n ≤ ∏ k ∈ range n, (r / 2 + k) := by
  calc (r / 2) ^ n = ∏ _k ∈ range n, (r / 2) := by rw [prod_const, card_range]
    _ ≤ _ := by
      gcongr with k hk
      linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]

/-- Upper bound for a rising factorial at a large real shift. -/
private lemma norm_pochhammer_add_le {x : ℂ} {r : ℝ} (hr : 0 < r) (hx : ‖x‖ ≤ r) (n : ℕ) :
    ‖pochhammer (x + r) n‖ ≤ 4 ^ n * ∏ k ∈ range n, (r / 2 + k) := by
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    rw [pochhammer_succ, norm_mul, prod_range_succ, pow_succ]
    have h1 : ‖x + r + n‖ ≤ 4 * (r / 2 + n) := by
      refine (norm_add₃_le).trans ?_
      rw [Complex.norm_real, Complex.norm_natCast, Real.norm_of_nonneg hr.le]
      linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    calc ‖pochhammer (x + r) n‖ * ‖x + r + n‖ ≤ (4 ^ n * ∏ k ∈ range n, (r / 2 + k)) *
           (4 * (r / 2 + n)) :=
          mul_le_mul ih h1 (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- Lower bound for a rising factorial at a large real shift. -/
private lemma prod_le_norm_pochhammer_add {y : ℂ} {r : ℝ} (hr : 0 < r) (hy : ‖y‖ ≤ r / 2) (n : ℕ) :
    ∏ k ∈ range n, (r / 2 + k) ≤ ‖pochhammer (y + r) n‖ := by
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    rw [pochhammer_succ, norm_mul, prod_range_succ]
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
private lemma norm_pochhammerProduct_shiftParameters_le {r : ℝ} (hr : 0 < r) (c : Multiset ℂ)
    (hc : ∀ x ∈ c, ‖x‖ ≤ r)
    (n : ℕ) : ‖pochhammerProduct (shiftParameters c r) n‖ ≤
        (4 ^ n * ∏ k ∈ range n, (r / 2 + k)) ^ c.card := by
  induction c using Multiset.induction_on with
  | empty => simp [pochhammerProduct, shiftParameters]
  | @cons x c ih =>
    simp only [pochhammerProduct, shiftParameters, Multiset.map_cons, Multiset.prod_cons,
        Multiset.card_cons,
      pow_succ] at ih ⊢
    rw [norm_mul, mul_comm _ (4 ^ n * _)]
    exact mul_le_mul (norm_pochhammer_add_le hr (hc x (Multiset.mem_cons_self x c)) n)
      (ih fun y hy => hc y (Multiset.mem_cons_of_mem hy)) (norm_nonneg _) (by positivity)

/-- Lower bound for a shifted multiset rising-factorial product. -/
private lemma le_norm_pochhammerProduct_shiftParameters {r : ℝ} (hr : 0 < r) (c : Multiset ℂ)
    (hc : ∀ x ∈ c, ‖x‖ ≤ r / 2)
    (n : ℕ) : (∏ k ∈ range n, (r / 2 + k)) ^ c.card ≤
        ‖pochhammerProduct (shiftParameters c r) n‖ := by
  induction c using Multiset.induction_on with
  | empty => simp [pochhammerProduct, shiftParameters]
  | @cons x c ih =>
    simp only [pochhammerProduct, shiftParameters, Multiset.map_cons, Multiset.prod_cons,
        Multiset.card_cons,
      pow_succ] at ih ⊢
    rw [norm_mul, mul_comm _ (∏ k ∈ range n, (r / 2 + k))]
    exact mul_le_mul (prod_le_norm_pochhammer_add hr (hc x (Multiset.mem_cons_self x c)) n)
      (ih fun y hy => hc y (Multiset.mem_cons_of_mem hy)) (by positivity) (norm_nonneg _)

/-- Uniform coefficient bound for large common real shifts, p≤q. -/
private lemma norm_generalizedHypergeometricCoeff_shiftParameters_le {r : ℝ} (hr : 0 < r)
    (a b : Multiset ℂ)
    (hab : a.card ≤ b.card)
    (ha : ∀ x ∈ a, ‖x‖ ≤ r) (hb : ∀ x ∈ b, ‖x‖ ≤ r / 2) (n : ℕ) :
    ‖generalizedHypergeometricCoeff (shiftParameters a r) (shiftParameters b r) n‖ ≤
      (4 ^ a.card * (2 / r) ^ (b.card - a.card)) ^ n / n.factorial := by
  set P := ∏ k ∈ range n, (r / 2 + k) with hP
  have hP0 : 0 < P := prod_pos fun k _ => by positivity
  have hPge := pow_le_prod_half_add hr n
  have h1 := norm_pochhammerProduct_shiftParameters_le hr a ha n
  have h2 := le_norm_pochhammerProduct_shiftParameters hr b hb n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  unfold generalizedHypergeometricCoeff
  rw [norm_div, norm_mul, Complex.norm_natCast]
  have hB : 0 < ‖pochhammerProduct (shiftParameters b r) n‖ := lt_of_lt_of_le (by positivity) h2
  rw [div_le_div_iff₀ (by positivity) hf]
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hf.le
  have hsplit : P ^ b.card = P ^ (b.card - a.card) * P ^ a.card := by
    rw [← pow_add]; congr 1; omega
  have e : ((2 / r) ^ (b.card - a.card)) ^ n * ((r / 2) ^ n) ^ (b.card - a.card) = 1 := by
    rw [← pow_mul, ← pow_mul, mul_comm (b.card - a.card) n, ← mul_pow, div_mul_div_comm,
      mul_comm 2 r, div_self (by positivity), one_pow]
  calc ‖pochhammerProduct (shiftParameters a r) n‖ ≤ (4 ^ n * P) ^ a.card := h1
    _ = (4 ^ a.card) ^ n * P ^ a.card := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm a.card n]
    _ = (4 ^ a.card) ^ n * ((2 / r) ^ (b.card - a.card)) ^ n *
          (((r / 2) ^ n) ^ (b.card - a.card) * P ^ a.card) := by
        rw [show (4 ^ a.card : ℝ) ^ n * ((2 / r) ^ (b.card - a.card)) ^ n *
          (((r / 2) ^ n) ^ (b.card - a.card) * P ^ a.card) = (4 ^ a.card) ^ n *
          (((2 / r) ^ (b.card - a.card)) ^ n * ((r / 2) ^ n) ^ (b.card - a.card)) * P ^ a.card
          by ring, e, mul_one]
    _ ≤ (4 ^ a.card) ^ n * ((2 / r) ^ (b.card - a.card)) ^ n *
          (P ^ (b.card - a.card) * P ^ a.card) := by gcongr
    _ ≤ (4 ^ a.card * (2 / r) ^ (b.card - a.card)) ^ n *
        ‖pochhammerProduct (shiftParameters b r) n‖ := by
        rw [← hsplit, mul_pow]; gcongr

/-- Every full large-parameter shift for p<q, without unnecessary exclusions on the unshifted
constants. -/
@[dlmf 16.11.E11]
theorem generalizedHypergeometric_all_large_parameter_asymptotic {p q : ℕ} (a : Fin p → ℂ)
    (b : Fin q → ℂ) (hpq : p < q)
    (z : ℂ) (m : ℕ) :
    Asymptotics.IsBigO atTop
      (fun r : ℝ => generalizedHypergeometric (shiftParameters (parametersOfFin a) r)
          (shiftParameters (parametersOfFin b) r) z -
        ∑ n ∈ range m, generalizedHypergeometricCoeff (shiftParameters (parametersOfFin a) r)
            (shiftParameters (parametersOfFin b) r) n * z ^ n)
      (fun r : ℝ => 1 / r ^ ((q - p) * m)) := by
  have hca : (parametersOfFin a).card = p := by simp [parametersOfFin]
  have hcb : (parametersOfFin b).card = q := by simp [parametersOfFin]
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
  have ha : ∀ x ∈ parametersOfFin a, ‖x‖ ≤ r := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (by simpa [parametersOfFin] using hx)
    have := single_le_sum (f := fun i => ‖a i‖) (fun _ _ => norm_nonneg _) (mem_univ i)
    linarith
  have hb : ∀ x ∈ parametersOfFin b, ‖x‖ ≤ r / 2 := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (by simpa [parametersOfFin] using hx)
    have := single_le_sum (f := fun i => ‖b i‖) (fun _ _ => norm_nonneg _) (mem_univ i)
    linarith
  have hreg : LowerParametersRegular (shiftParameters (parametersOfFin b) r) := by
    intro x hx n hxn
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    have h1 := congrArg Complex.re hxn
    simp only [add_re, ofReal_re, neg_re, natCast_re] at h1
    have h2 := (abs_re_le_norm y).trans (hb y hy)
    have h3 := neg_abs_le y.re
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hsum := generalizedHypergeometric_hasSum_entire (a := shiftParameters (parametersOfFin a) r)
      (b := shiftParameters (parametersOfFin b) r)
    (by simp [shiftParameters, hca, hcb]; omega) hreg z
  set c := fun n => generalizedHypergeometricCoeff (shiftParameters (parametersOfFin a) r)
      (shiftParameters (parametersOfFin b) r) n * z ^ n
    with hc
  have hrem : generalizedHypergeometric (shiftParameters (parametersOfFin a) r)
      (shiftParameters (parametersOfFin b) r) z -
      ∑ n ∈ range m, c n = ∑' n, c (n + m) := by
    rw [← hsum.tsum_eq, ← hsum.summable.sum_add_tsum_nat_add m]; ring
  rw [hrem]
  set t : ℝ := (1 / r) ^ (q - p) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := pow_le_one₀ (by positivity) (by rw [div_le_one hr0]; exact hr1)
  have hbound : ∀ n, ‖c (n + m)‖ ≤ (K * t) ^ m * (K ^ n / n.factorial) := by
    intro n
    have hco := norm_generalizedHypergeometricCoeff_shiftParameters_le hr0 (parametersOfFin a)
        (parametersOfFin b) (by omega) ha hb (n + m)
    rw [hca, hcb] at hco
    simp only [hc, norm_mul, norm_pow]
    have hKt : 4 ^ p * (2 / r) ^ (q - p) * ‖z‖ = K * t := by
      rw [hK, ht, div_eq_mul_one_div 2 r, mul_pow]; ring
    calc ‖generalizedHypergeometricCoeff (shiftParameters (parametersOfFin a) r)
           (shiftParameters (parametersOfFin b) r) (n + m)‖ * ‖z‖ ^ (n + m)
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
