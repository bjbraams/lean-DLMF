/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.UnitArgument

/-!
# Finite Dougall sums at unit argument (DLMF 16.4.9–16.4.10)

## Main results

* `generalizedHypergeometric_dougall_5F4_terminating`: the terminating Dougall `₅F₄(1)` sum,
  DLMF 16.4.9.
* `generalizedHypergeometric_dougall_7F6`: Dougall's terminating `₇F₆(1)` sum, DLMF 16.4.10.

## Implementation notes

The finite Dougall `₅F₄` evaluation is the `q → 1` limit of the rational terminating `₆φ₅`
identity `DLMF.QHypergeometric.sum_sixTerm_eq`, with Bailey's polynomial unit factor handling the
very-well-poised pair without square-root branch restrictions. The finite Dougall `₇F₆` follows
from Whipple's transformation and Saalschütz's sum, with continuity of finite rational sums
retaining the removable cancelled-parameter cases. Both use Pochhammer quotients, which retain the
removable cases hidden by quotients of poles in the printed Gamma formulas.
-/

@[expose] public section
open Complex Filter Set Finset
open scoped Topology Real
noncomputable section
namespace DLMF.Hypergeometric

section DougallFinite

open DLMF.QSeries DLMF.QHypergeometric

/-- The normalized polynomial unit-Bailey factor has the expected classical limit. Bailey’s
cleared identity avoids square-root choices in the very-well-poised pair. -/
private lemma dougall_unitD_classical_limit (a : ℂ) (ha : a ≠ 0) (k : ℕ) :
    Tendsto (fun q : ℝ => DLMF.Bailey.unitD ((q : ℂ) ^ a) q k / (1 - (q : ℂ)) ^ k)
      (𝓝[<] 1) (𝓝 (pochhammer a k * (a + 2 * k) / a)) := by
  have h := (tendsto_qPochhammer_normalized a k).mul
    ((tendsto_cpow_increment (a + 2 * k)).div (tendsto_cpow_increment a) ha)
  convert h.congr' ?_ using 1
  · ring
  filter_upwards [(tendsto_cpow_increment a).eventually_ne ha,
    Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with q hqa hq
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.1.ne'
  have hD : 1 - (q : ℂ) ≠ 0 := by
    intro h0
    have : q = 1 := by exact_mod_cast (sub_eq_zero.mp h0).symm
    exact hq.2.ne this
  have hA : 1 - (q : ℂ) ^ a ≠ 0 := by
    intro h0
    exact hqa (by rw [h0, zero_div])
  have hunit := DLMF.Bailey.qPochhammer_mul_one_sub_pow ((q : ℂ) ^ a) q k
  simp only [Pi.div_apply]
  rw [show (q : ℂ) ^ (a + 2 * k) = (q : ℂ) ^ a * (q : ℂ) ^ (2 * k : ℕ) by
    rw [Complex.cpow_add _ _ hq0]
    norm_cast]
  field_simp
  linear_combination hunit

/-- Dividing the unit-Bailey factor by the factorial q-Pochhammer gives its classical
coefficient normalization. -/
private lemma dougall_unitD_factorial_classical_limit (a : ℂ) (ha : a ≠ 0) (k : ℕ) :
    Tendsto (fun q : ℝ => DLMF.Bailey.unitD ((q : ℂ) ^ a) q k / qPochhammer q q k)
      (𝓝[<] 1) (𝓝 (pochhammer a k * (a + 2 * k) / (a * (k.factorial : ℂ)))) := by
  have h := (dougall_unitD_classical_limit a ha k).div (tendsto_qPochhammer_normalized 1 k)
    (by simpa only [pochhammer_nat_one] using
      (show (k.factorial : ℂ) ≠ 0 by exact_mod_cast k.factorial_ne_zero))
  simp only [Complex.cpow_one, pochhammer_nat_one] at h
  convert h.congr' ?_ using 1
  · ring
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with q hq
  have hD : 1 - (q : ℂ) ≠ 0 := by
    intro h0
    have : q = 1 := by exact_mod_cast (sub_eq_zero.mp h0).symm
    exact hq.2.ne this
  simpa only [Pi.div_apply] using div_div_div_cancel_right₀ (pow_ne_zero k hD)
    (DLMF.Bailey.unitD ((q : ℂ) ^ a) q k) (qPochhammer q q k)

/-- The classical unit factor equals the usual half-parameter Pochhammer quotient whenever
the lower half-parameter is regular. -/
private lemma dougall_classical_unit_eq (a : ℂ) (ha : ∀ j : ℕ, a / 2 ≠ -j) (k : ℕ) :
    pochhammer a k * (a + 2 * k) / a = pochhammer a k * pochhammer (a / 2 + 1) k /
        pochhammer (a / 2) k := by
  have ha0 : a ≠ 0 := by intro h; simpa [h] using ha 0
  have hp := pochhammer_ne_zero_of_not_neg_nat ha k
  have hs : (a / 2) * pochhammer (a / 2 + 1) k = pochhammer (a / 2) k * (a / 2 + k) := by
    rw [← pochhammer_succ_left, pochhammer_succ]
  generalize pochhammer (a / 2 + 1) k = X at hs ⊢
  generalize pochhammer (a / 2) k = Y at hs hp ⊢
  field_simp
  linear_combination -2 * pochhammer a k * hs

/-- A finite q-Pochhammer product stays nonzero near the classical limit when its limiting
rising factorial is nonzero. -/
private lemma dougall_qPochhammer_eventually_ne_zero (a : ℂ) (n : ℕ) (ha : pochhammer a n ≠ 0) :
    ∀ᶠ q : ℝ in 𝓝[<] 1, qPochhammer ((q : ℂ) ^ a) q n ≠ 0 := by
  filter_upwards [(tendsto_qPochhammer_normalized a n).eventually_ne ha] with q hq hzero
  exact hq (by rw [hzero, zero_div])

/-- The lower parameters and argument in the rational q-Dougall sum become sums and
differences of classical exponents. -/
private lemma dougall_qpow_params (a b c : ℂ) (n : ℕ) {q : ℂ} (hq : q ≠ 0) :
    q ^ a * q / q ^ b = q ^ (a - b + 1) ∧
    q ^ a * q ^ (n + 1) = q ^ (a + n + 1) ∧
    q ^ a * q ^ (n + 1) / (q ^ b * q ^ c) = q ^ (a + n + 1 - b - c) := by
  constructor
  · rw [Complex.cpow_add _ _ hq, Complex.cpow_sub _ _ hq, Complex.cpow_one]
    ring
  constructor
  · rw [show a + (n : ℂ) + 1 = a + ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.cpow_add _ _ hq, Complex.cpow_natCast]
  · rw [Complex.cpow_sub _ _ hq, Complex.cpow_sub _ _ hq,
      show a + (n : ℂ) + 1 = a + ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.cpow_add _ _ hq, Complex.cpow_natCast]
    ring

/-- Each rational terminating q-Dougall summand tends to the corresponding classical
very-well-poised `₅F₄` coefficient. -/
private lemma dougall_qterm_classical_limit (a b c : ℂ) (n k : ℕ)
    (hb : LowerParametersRegular {a / 2, a - b + 1, a - c + 1, a + n + 1}) :
    Tendsto (fun q : ℝ => sixTerm ((q : ℂ) ^ a) ((q : ℂ) ^ b) ((q : ℂ) ^ c) q n k)
      (𝓝[<] 1) (𝓝 (generalizedHypergeometricCoeff {a, a / 2 + 1, b, c, (-n : ℂ)}
        {a / 2, a - b + 1, a - c + 1, a + n + 1} k)) := by
  have hA : ∀ j : ℕ, a / 2 ≠ -j := hb _ (by simp)
  have ha : a ≠ 0 := by intro h; simpa [h] using hA 0
  have hU := dougall_unitD_factorial_classical_limit a ha k
  have hR := tendsto_qPochhammerList_ratio [b, c, (-n : ℂ)]
    [a - b + 1, a - c + 1, a + n + 1] k rfl (by
      intro p hp j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> exact hb _ (by simp) j)
  have hq : Tendsto (fun q : ℝ => (q : ℂ)) (𝓝[<] 1) (𝓝 1) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun q : ℝ => (q : ℂ) ^ (a + n + 1 - b - c)) (𝓝[<] 1) (𝓝 1) := by
    simpa only [Function.comp_def, Complex.one_cpow] using
      (continuousAt_cpow_const (a := 1) (b := a + n + 1 - b - c)
      (by simp)).tendsto.comp hq
  convert ((hU.mul hR).mul (hz.pow k)).congr' ?_ using 1
  · congr 1
    simp only [generalizedHypergeometricCoeff, pochhammerProduct, Multiset.insert_eq_cons,
        Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton,
      Multiset.map_coe, Multiset.prod_coe, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, one_pow]
    rw [show pochhammer a k * (a + 2 * k) / (a * (k.factorial : ℂ)) =
        (pochhammer a k * (a + 2 * k) / a) / k.factorial by ring,
      dougall_classical_unit_eq a hA k]
    ring
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with q hq
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.1.ne'
  simp only [qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  have hB := (dougall_qpow_params a b c n hq0).1
  have hC := (dougall_qpow_params a c b n hq0).1
  obtain ⟨hN, hZ⟩ := (dougall_qpow_params a b c n hq0).2
  rw [sixTerm, hB, hC, hZ, hN,
    show (q : ℂ) ^ (-(n : ℤ)) = (q : ℂ) ^ (-(n : ℂ)) by
      rw [Complex.cpow_neg, Complex.cpow_natCast, zpow_neg, zpow_natCast]]
  ring

/-- Dougall terminating 5F4, with all removable cases retained by finite products. -/
@[dlmf 16.4.E9]
theorem generalizedHypergeometric_dougall_5F4_terminating (n : ℕ) (a b c : ℂ)
    (hb : LowerParametersRegular {a / 2, a - b + 1, a - c + 1, a + n + 1}) :
    generalizedHypergeometricTruncated n {a, a / 2 + 1, b, c, (-n : ℂ)}
      {a / 2, a - b + 1, a - c + 1, a + n + 1} 1 =
      pochhammer (a + 1) n * pochhammer (a - b - c + 1) n /
        (pochhammer (a - b + 1) n * pochhammer (a - c + 1) n) := by
  have hL := tendsto_finsetSum (range (n + 1)) fun k _ => dougall_qterm_classical_limit a b c n k hb
  have hR := tendsto_qPochhammerList_ratio [a + 1, a - b - c + 1]
    [a - b + 1, a - c + 1] n rfl (by
      intro p hp j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact hb _ (by simp) j)
  have hB := dougall_qPochhammer_eventually_ne_zero (a - b + 1) n
    (pochhammer_ne_zero_of_not_neg_nat (hb _ (by simp)) n)
  have hC := dougall_qPochhammer_eventually_ne_zero (a - c + 1) n
    (pochhammer_ne_zero_of_not_neg_nat (hb _ (by simp)) n)
  have hN := dougall_qPochhammer_eventually_ne_zero (a + n + 1) n
    (pochhammer_ne_zero_of_not_neg_nat (hb _ (by simp)) n)
  have heq : (fun q : ℝ => ∑ k ∈ range (n + 1),
      sixTerm ((q : ℂ) ^ a) ((q : ℂ) ^ b) ((q : ℂ) ^ c) q n k) =ᶠ[𝓝[<] 1]
      (fun q => qPochhammerList ([a + 1, a - b - c + 1].map fun x => (q : ℂ) ^ x) q n /
        qPochhammerList ([a - b + 1, a - c + 1].map fun x => (q : ℂ) ^ x) q n) := by
    filter_upwards [hB, hC, hN, Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with q hB hC hN hq
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.1.ne'
    have hqn : ‖(q : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq.1]
      exact hq.2
    have hBpow := (dougall_qpow_params a b c n hq0).1
    have hCpow := (dougall_qpow_params a c b n hq0).1
    have hNpow := (dougall_qpow_params a b c n hq0).2.1
    have hS := sum_sixTerm_eq hq0 hqn n
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hq0))
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hq0))
      (by rwa [hBpow]) (by rwa [hCpow]) (by rwa [hNpow])
    have hAQ : (q : ℂ) ^ a * q = (q : ℂ) ^ (a + 1) := by
      rw [Complex.cpow_add _ _ hq0, Complex.cpow_one]
    have hABC : (q : ℂ) ^ a * q / ((q : ℂ) ^ b * (q : ℂ) ^ c) =
        (q : ℂ) ^ (a - b - c + 1) := by
      have h := (dougall_qpow_params a b c 0 hq0).2.2
      simpa only [Nat.cast_zero, add_zero, zero_add, pow_one,
        show a + 1 - b - c = a - b - c + 1 by ring] using h
    rw [hABC, hBpow, hCpow, hAQ] at hS
    simpa only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one] using hS
  have h := tendsto_nhds_unique hL (hR.congr' heq.symm)
  simpa [generalizedHypergeometricTruncated, pochhammerProduct] using h

end DougallFinite

section DougallSeven

/-- The balancing relation reflects the last denominator Pochhammer into the regular lower
parameter paired with `f`, so that denominator stays nonzero. -/
private lemma dougall7_last_den_ne (n : ℕ) (a b c d f : ℂ)
    (hbal : 2 * a + 1 = b + c + d + f - n) (hF : pochhammer (a - f + 1) n ≠ 0) :
    pochhammer (a - b - c - d + 1) n ≠ 0 := by
  have hRef := pochhammer_reflect (a - b - c - d + 1) n
  rw [show 1 - (a - b - c - d + 1) - n = a - f + 1 by linear_combination -hbal] at hRef
  intro hzero
  rw [hzero, mul_zero] at hRef
  exact hF hRef

/-- On a punctured neighborhood of any complex point, the nonpositive integers are avoided.
This combines their discreteness with openness of their complement. -/
private lemma dougall_eventually_not_neg_nat_at (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, ∀ j : ℕ, w ≠ -(j : ℂ) := by
  by_cases hz : ∀ j : ℕ, z ≠ -(j : ℂ)
  · exact nhdsWithin_le_nhds (isOpen_not_neg_nat.mem_nhds hz)
  · push Not at hz
    obtain ⟨j, rfl⟩ := hz
    exact eventually_nhdsWithin_ne_neg_nat j

/-- A fixed rising factorial is a polynomial in its parameter, hence continuous. -/
private lemma dougall_pochhammer_continuous (k : ℕ) : Continuous (fun z : ℂ => pochhammer z k) :=
  (ascPochhammer ℂ k).continuous

attribute [local fun_prop] dougall_pochhammer_continuous

/-- Under the Dougall balance, Pochhammer reflection turns the Whipple prefactor times
Saalschütz’s value into the finite `₇F₆` product. -/
private lemma dougall7_product_eval (n : ℕ) (a b c d f : ℂ)
    (hbal : 2 * a + 1 = b + c + d + f - n)
    (hb : LowerParametersRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1}) :
    pochhammer (a + 1) n * pochhammer (a - d - f + 1) n /
        (pochhammer (a - d + 1) n * pochhammer (a - f + 1) n) *
      (pochhammer (a - b + 1 - d) n * pochhammer (a - b + 1 - f) n /
        (pochhammer (a - b + 1) n * pochhammer (a - b + 1 - d - f) n)) =
      pochhammer (a + 1) n * pochhammer (a - b - c + 1) n * pochhammer (a - b - d + 1) n *
        pochhammer (a - c - d + 1) n /
      (pochhammer (a - b + 1) n * pochhammer (a - c + 1) n * pochhammer (a - d + 1) n *
        pochhammer (a - b - c - d + 1) n) := by
  have hB := pochhammer_ne_zero_of_not_neg_nat (hb (a - b + 1) (by simp)) n
  have hC := pochhammer_ne_zero_of_not_neg_nat (hb (a - c + 1) (by simp)) n
  have hD := pochhammer_ne_zero_of_not_neg_nat (hb (a - d + 1) (by simp)) n
  have hF := pochhammer_ne_zero_of_not_neg_nat (hb (a - f + 1) (by simp)) n
  have hRef := pochhammer_reflect (a - b - c - d + 1) n
  rw [show 1 - (a - b - c - d + 1) - n = a - f + 1 by linear_combination -hbal] at hRef
  have hBCD := dougall7_last_den_ne n a b c d f hbal hF
  rw [show a - d - f + 1 = 1 - (a - b - c + 1) - n by linear_combination hbal,
    pochhammer_reflect, show a - b + 1 - d = a - b - d + 1 by ring,
    show a - b + 1 - f = 1 - (a - c - d + 1) - n by linear_combination hbal,
    pochhammer_reflect, show a - b - d + 1 - f = 1 - (a - c + 1) - n by linear_combination hbal,
    pochhammer_reflect, hRef]
  have hsign : (-1 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- Whipple’s terminating transformation and Saalschütz’s sum prove finite Dougall when the
parameter canceled from the transformed `₄F₃` is regular. -/
private lemma dougall7_generic (n : ℕ) (a b c d f : ℂ)
    (hbal : 2 * a + 1 = b + c + d + f - n)
    (hb : LowerParametersRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1})
    (hY : ∀ j : ℕ, a - b - c + 1 ≠ -j) :
    generalizedHypergeometricTruncated n {a, a / 2 + 1, b, c, d, f, (-n : ℂ)}
      {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1} 1 =
      pochhammer (a + 1) n * pochhammer (a - b - c + 1) n * pochhammer (a - b - d + 1) n *
        pochhammer (a - c - d + 1) n /
      (pochhammer (a - b + 1) n * pochhammer (a - c + 1) n * pochhammer (a - d + 1) n *
        pochhammer (a - b - c - d + 1) n) := by
  have hYE : d + f - a - n = a - b - c + 1 := by linear_combination -hbal
  have hSA : 1 + d + f - (a - b + 1) - n = a - c + 1 := by linear_combination -hbal
  have hW := whipple_7F6 (a := a) (b := b) (c := c) (d := d) (e := f) n (by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hb _ (by simp)
    · exact hb _ (by simp)
    · exact hb _ (by simp)
    · exact hb _ (by simp)
    · exact hb _ (by simp)
    · exact hb _ (by simp)
    · rw [hYE]; exact hY)
  have hL : generalizedHypergeometricTruncated n {a, a / 2 + 1, b, c, d, f, (-n : ℂ)}
      {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1} 1 =
      ∑ k ∈ range (n + 1),
        pochhammer a k * pochhammer (a / 2 + 1) k * pochhammer b k * pochhammer c k *
            pochhammer d k * pochhammer f k *
          pochhammer (-n : ℂ) k /
          (pochhammer (a / 2) k * pochhammer (a - b + 1) k * pochhammer (a - c + 1) k *
            pochhammer (a - d + 1) k * pochhammer (a - f + 1) k * pochhammer (a + n + 1) k *
                k.factorial) := by
    unfold generalizedHypergeometricTruncated
    refine sum_congr rfl fun k hk => ?_
    simp only [generalizedHypergeometricCoeff, pochhammerProduct, Multiset.insert_eq_cons,
        Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, one_pow, mul_one]
    ring
  have hR : (∑ k ∈ range (n + 1),
      pochhammer (a - b - c + 1) k * pochhammer d k * pochhammer f k * pochhammer (-n : ℂ) k /
        (pochhammer (a - b + 1) k * pochhammer (a - c + 1) k * pochhammer (d + f - a - n) k *
            k.factorial)) =
      ∑ k ∈ range (n + 1), pochhammer (-n : ℂ) k * pochhammer d k * pochhammer f k /
        (pochhammer (a - b + 1) k * pochhammer (a - c + 1) k * k.factorial) := by
    refine sum_congr rfl fun k hk => ?_
    rw [hYE]
    have hYk := pochhammer_ne_zero_of_not_neg_nat hY k
    have hBk := pochhammer_ne_zero_of_not_neg_nat (hb (a - b + 1) (by simp)) k
    have hCk := pochhammer_ne_zero_of_not_neg_nat (hb (a - c + 1) (by simp)) k
    have hFk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  have hS := pfaff_saalschutz n (a := d) (b := f) (c := a - b + 1)
    (hb _ (by simp)) (by rw [hSA]; exact pochhammer_ne_zero_of_not_neg_nat (hb _ (by simp)) n)
  rw [hSA] at hS
  rw [← hL, hR, hS] at hW
  exact hW.trans (dougall7_product_eval n a b c d f hbal hb)

/-- The difference of the finite Dougall sum and its product is continuous in a varying
parameter, because the displayed denominators are nonzero at the reference point. -/
private lemma dougall7_difference_continuous (n : ℕ) (a b c d f : ℂ) (F : ℂ → ℂ)
    (hFB : F b = f) (hFc : Continuous F)
    (hbal : 2 * a + 1 = b + c + d + f - n)
    (hb : LowerParametersRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1}) :
    ContinuousAt (fun t : ℂ =>
    generalizedHypergeometricTruncated n {a, a / 2 + 1, t, c, d, F t, (-n : ℂ)}
      {a / 2, a - t + 1, a - c + 1, a - d + 1, a - F t + 1, a + n + 1} 1 -
      pochhammer (a + 1) n * pochhammer (a - t - c + 1) n * pochhammer (a - t - d + 1) n *
        pochhammer (a - c - d + 1) n /
      (pochhammer (a - t + 1) n * pochhammer (a - c + 1) n * pochhammer (a - d + 1) n *
        pochhammer (a - t - c - d + 1) n)) b := by
  refine ContinuousAt.sub ?_ ?_
  · simp only [generalizedHypergeometricTruncated]
    refine tendsto_finsetSum _ fun k hk => ?_
    have hden : pochhammerProduct
        {a / 2, a - b + 1, a - c + 1, a - d + 1, a - F b + 1, a + n + 1} k *
        (k.factorial : ℂ) ≠ 0 := by
      rw [hFB]
      exact mul_ne_zero (pochhammerProduct_ne_zero hb k) (by exact_mod_cast k.factorial_ne_zero)
    simp only [pochhammerProduct, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton] at hden
    have hc : ContinuousAt (fun t : ℂ => generalizedHypergeometricCoeff
        {a, a / 2 + 1, t, c, d, F t, (-n : ℂ)}
        {a / 2, a - t + 1, a - c + 1, a - d + 1, a - F t + 1, a + n + 1} k) b := by
      simp only [generalizedHypergeometricCoeff, pochhammerProduct, Multiset.insert_eq_cons,
          Multiset.map_cons,
        Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
      fun_prop (disch := exact hden)
    simpa only [one_pow, mul_one] using hc.tendsto
  · have hden : pochhammer (a - b + 1) n * pochhammer (a - c + 1) n * pochhammer (a - d + 1) n *
        pochhammer (a - b - c - d + 1) n ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero
        (pochhammer_ne_zero_of_not_neg_nat (hb _ (by simp)) n)
        (pochhammer_ne_zero_of_not_neg_nat (hb _ (by simp)) n))
        (pochhammer_ne_zero_of_not_neg_nat (hb _ (by simp)) n))
        (dougall7_last_den_ne n a b c d f hbal
            (pochhammer_ne_zero_of_not_neg_nat (hb _ (by simp)) n))
    fun_prop (disch := exact hden)

/-- Dougall terminating 2-balanced 7F6, including n=0. -/
@[dlmf 16.4.E10]
theorem generalizedHypergeometric_dougall_7F6 (n : ℕ) (a b c d f : ℂ)
    (hbal : 2 * a + 1 = b + c + d + f - n)
    (hb : LowerParametersRegular {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1}) :
    generalizedHypergeometricTruncated n {a, a / 2 + 1, b, c, d, f, (-n : ℂ)}
      {a / 2, a - b + 1, a - c + 1, a - d + 1, a - f + 1, a + n + 1} 1 =
      pochhammer (a + 1) n * pochhammer (a - b - c + 1) n * pochhammer (a - b - d + 1) n *
        pochhammer (a - c - d + 1) n /
      (pochhammer (a - b + 1) n * pochhammer (a - c + 1) n * pochhammer (a - d + 1) n *
        pochhammer (a - b - c - d + 1) n) := by
  let F : ℂ → ℂ := fun t => f + b - t
  have hFB : F b = f := by dsimp [F]; ring
  have hFc : Continuous F := by dsimp [F]; fun_prop
  let G : ℂ → ℂ := fun t =>
    generalizedHypergeometricTruncated n {a, a / 2 + 1, t, c, d, F t, (-n : ℂ)}
      {a / 2, a - t + 1, a - c + 1, a - d + 1, a - F t + 1, a + n + 1} 1 -
      pochhammer (a + 1) n * pochhammer (a - t - c + 1) n * pochhammer (a - t - d + 1) n *
        pochhammer (a - c - d + 1) n /
      (pochhammer (a - t + 1) n * pochhammer (a - c + 1) n * pochhammer (a - d + 1) n *
        pochhammer (a - t - c - d + 1) n)
  have hB := (show ContinuousAt (fun t : ℂ => a - t + 1) b by fun_prop).tendsto.eventually
    (isOpen_not_neg_nat.mem_nhds (hb (a - b + 1) (by simp)))
  have hF := (show ContinuousAt (fun t : ℂ => a - F t + 1) b by fun_prop).tendsto.eventually
    (isOpen_not_neg_nat.mem_nhds (by rw [hFB]; exact hb (a - f + 1) (by simp)))
  have hmap : Tendsto (fun t : ℂ => a - t - c + 1) (𝓝[≠] b) (𝓝[≠] (a - b - c + 1)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (show ContinuousAt (fun t : ℂ => a - t - c + 1) b by fun_prop).tendsto.mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change t ≠ b at ht
      change a - t - c + 1 ≠ a - b - c + 1
      intro heq
      apply ht
      linear_combination -heq
  have hY := hmap.eventually (dougall_eventually_not_neg_nat_at (a - b - c + 1))
  have heq : G =ᶠ[𝓝[≠] b] fun _ => 0 := by
    filter_upwards [nhdsWithin_le_nhds hB, nhdsWithin_le_nhds hF, hY] with t hBt hFt hYt
    have hbt : LowerParametersRegular
        {a / 2, a - t + 1, a - c + 1, a - d + 1, a - F t + 1, a + n + 1} := by
      intro z hz
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hb _ (by simp)
      · exact hBt
      · exact hb _ (by simp)
      · exact hb _ (by simp)
      · exact hFt
      · exact hb _ (by simp)
    exact sub_eq_zero.mpr (dougall7_generic n a t c d (F t)
      (by dsimp [F]; linear_combination hbal) hbt hYt)
  have hg : ContinuousAt G b :=
    dougall7_difference_continuous n a b c d f F hFB hFc hbal hb
  have hzero : G b = 0 := tendsto_nhds_unique
    (hg.tendsto.mono_left nhdsWithin_le_nhds) (tendsto_const_nhds.congr' heq.symm)
  simpa only [G, hFB, sub_eq_zero] using hzero

end DougallSeven

end DLMF.Hypergeometric
