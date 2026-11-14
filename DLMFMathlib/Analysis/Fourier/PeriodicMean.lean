/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public import Mathlib.Analysis.Fourier.AddCircleMulti
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Topology.Instances.AddCircle.UnitAddTorus
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic

/-!
# Complex translation invariance of periodic means

The integral of an entire function over a real unit cube is unchanged by complex translation
when every integer vector is a period. Real translation invariance follows by descending to
the unit torus and using Haar invariance; analytic continuation gives complex translations.

The proof uses Mathlib's unit-torus integration and identity theorem, and TauCeti's quotient
map and compact-parameter analytic integration APIs. No nonempty coordinate assumption is needed.

## Main results

* `Complex.setIntegral_unitCube_add_real_of_periodic`: real translation invariance.
* `Complex.analyticOnNhd_integral_unitCube_affine`: analytic affine parameter dependence.
* `Complex.setIntegral_unitCube_add_complex_of_periodic`: complex translation invariance.
-/

public noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology
namespace Complex
variable {ι : Type*} [Fintype ι]
/-- The mean of a continuous integer-periodic function is invariant under real translation. -/
lemma setIntegral_unitCube_add_real_of_periodic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ι → ℂ) → E} (hf : Continuous f)
    (hp : ∀ (m : ι → ℤ) (z : ι → ℂ), f (z + fun i => (m i : ℂ)) = f z)
    (w : ι → ℂ) (a : ι → ℝ) :
    (∫ u : ι → ℝ in {u : ι → ℝ | ∀ i, u i ∈ Ioc (0 : ℝ) 1},
      f ((fun i => (u i : ℂ)) + w + fun i => (a i : ℂ))) =
      ∫ u : ι → ℝ in {u : ι → ℝ | ∀ i, u i ∈ Ioc (0 : ℝ) 1},
        f ((fun i => (u i : ℂ)) + w) := by
  classical
  have hF : Continuous (fun u : ι → ℝ => f ((fun i => (u i : ℂ)) + w)) := by fun_prop
  have hperiod (m : ι → ℤ) : Function.Periodic
      (fun u : ι → ℝ => f ((fun i => (u i : ℂ)) + w)) (fun i => (m i : ℝ)) := by
    intro u
    convert hp m ((fun i => (u i : ℂ)) + w) using 1
    dsimp only
    congr 1
    funext i
    simp only [Pi.add_apply, ofReal_add, ofReal_intCast]
    ring
  obtain ⟨g, _, hg⟩ := TauCeti.UnitAddTorus.exists_continuous_comp_coe_eq hF hperiod
  let aT : UnitAddTorus ι := fun i => (a i : UnitAddCircle)
  have he (u : ι → ℝ) : g ((fun i => (u i : UnitAddCircle)) + aT) =
      f ((fun i => (u i : ℂ)) + w + fun i => (a i : ℂ)) := by
    calc
      _ = g (fun i => ((u + a) i : UnitAddCircle)) := by congr 1
      _ = _ := hg (u + a)
      _ = _ := by
        congr 1
        funext i
        simp only [Pi.add_apply, ofReal_add]
        ring
  have hl := UnitAddTorus.integral_preimage (fun z => g (z + aT)) (0 : ι → ℝ)
  have hr := UnitAddTorus.integral_preimage g (0 : ι → ℝ)
  have h := integral_add_right_eq_self (μ := volume) g aT
  simp only [volume_pi, AddCircle.volume_eq_smul_haarAddCircle,
    ENNReal.ofReal_one, one_smul] at h
  simp only [volume] at hl hr
  rw [hl, hr] at h
  simpa only [Pi.zero_apply, zero_add, he, hg, volume_pi, volume] using h

/-- Integrating an entire function over a unit cube preserves analytic affine dependence. -/
lemma analyticOnNhd_integral_unitCube_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : (ι → ℂ) → E} (hf : Differentiable ℂ f) (w v : ι → ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ =>
      ∫ u : ι → ℝ in {u : ι → ℝ | ∀ i, u i ∈ Ioc (0 : ℝ) 1},
        f ((fun i => (u i : ℂ)) + w + z • v)) univ := by
  classical
  by_cases hE : CompleteSpace E
  swap
  · simp only [integral_of_not_completeSpace hE]
    exact analyticOnNhd_const
  intro z _
  let φ : (ι → ℝ) → (ι → ℂ) := fun u i => (projIcc 0 1 zero_le_one (u i) : ℝ)
  let K : Set (ι → ℂ) := (fun u : ι → ℝ => fun i => (u i : ℂ)) '' Icc 0 1
  have hφ : Continuous φ := by
    apply continuous_pi
    intro i
    exact continuous_ofReal.comp ((continuous_subtype_val.comp continuous_projIcc).comp
      (continuous_apply i))
  have hφK (u : ι → ℝ) : φ u ∈ K := by
    refine ⟨fun i => (projIcc 0 1 zero_le_one (u i) : ℝ), ?_, rfl⟩
    exact ⟨fun i => (projIcc 0 1 zero_le_one (u i)).property.1,
      fun i => (projIcc 0 1 zero_le_one (u i)).property.2⟩
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have ha : ∀ y ∈ K, AnalyticAt ℂ
      (fun p : ℂ × (ι → ℂ) => f (p.2 + w + p.1 • v)) (z, y) := by
    intro y _
    apply DifferentiableOn.analyticAt_of_finiteDimensional (s := univ)
    · exact (hf.comp ((differentiable_snd.add_const w).add
        (differentiable_fst.smul_const v))).differentiableOn
    · exact univ_mem
  have hc : IsCompact (Icc (0 : ι → ℝ) 1) := isCompact_Icc
  have hm : MeasurableSet {u : ι → ℝ | ∀ i, u i ∈ Ioc (0 : ℝ) 1} :=
    MeasurableSet.univ_pi' fun _ => measurableSet_Ioc
  have hsub : {u : ι → ℝ | ∀ i, u i ∈ Ioc (0 : ℝ) 1} ⊆ Icc 0 1 := by
    intro u hu
    exact ⟨fun i => (hu i).1.le, fun i => (hu i).2⟩
  have hw : Integrable (fun _ : ι → ℝ => (1 : ℂ))
      (volume.restrict {u : ι → ℝ | ∀ i, u i ∈ Ioc (0 : ℝ) 1}) :=
    integrableOn_const (ne_of_lt (lt_of_le_of_lt (measure_mono hsub) hc.measure_lt_top))
  have h := TauCeti.analyticAt_integral_smul
    (μ := volume.restrict {u : ι → ℝ | ∀ i, u i ∈ Ioc (0 : ℝ) 1})
    (g := fun _ : ι → ℝ => (1 : ℂ)) hK hφ hφK ha hw
  convert h using 1
  ext q
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hm] with u hu
  simp only [one_smul]
  congr 1
  funext i
  simp only [Pi.add_apply, φ, projIcc_of_mem zero_le_one (Ioc_subset_Icc_self (hu i))]

/-- The unit-cube mean of an entire integer-periodic function is invariant under complex
translation, including for an empty coordinate type. -/
lemma setIntegral_unitCube_add_complex_of_periodic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : (ι → ℂ) → E} (hf : Differentiable ℂ f)
    (hp : ∀ (m : ι → ℤ) (z : ι → ℂ), f (z + fun i => (m i : ℂ)) = f z)
    (w : ι → ℂ) :
    (∫ u : ι → ℝ in {u : ι → ℝ | ∀ i, u i ∈ Ioc (0 : ℝ) 1},
      f ((fun i => (u i : ℂ)) + w)) =
      ∫ u : ι → ℝ in {u : ι → ℝ | ∀ i, u i ∈ Ioc (0 : ℝ) 1},
        f (fun i => (u i : ℂ)) := by
  let wr : ι → ℂ := fun i => ((w i).re : ℂ)
  let wi : ι → ℂ := fun i => ((w i).im : ℂ)
  let G : ℂ → E := fun q =>
    ∫ u : ι → ℝ in {u : ι → ℝ | ∀ i, u i ∈ Ioc (0 : ℝ) 1},
      f ((fun i => (u i : ℂ)) + wr + q • wi)
  have hG := analyticOnNhd_integral_unitCube_affine hf wr wi
  have hr (t : ℝ) : G (t : ℂ) = G 0 := by
    dsimp only [G]
    simp only [zero_smul, add_zero]
    convert setIntegral_unitCube_add_real_of_periodic hf.continuous hp wr
      (fun i => t * (w i).im) using 1
    congr 1
    funext u
    congr 1
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofReal_mul, wi]
  have hsub : ofReal '' Ioi (0 : ℝ) ⊆ {q | G q = G 0} \ {0} := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨hr t, by simpa using ne_of_gt ht⟩
  have hcl : (0 : ℂ) ∈ closure (ofReal '' Ioi (0 : ℝ)) := by
    simpa only [ofReal_zero] using mem_closure_image (x := (0 : ℝ))
      (s := Ioi (0 : ℝ)) continuous_ofReal.continuousAt
      (by simp only [closure_Ioi, mem_Ici, le_refl])
  have he := hG.eqOn_of_preconnected_of_mem_closure analyticOnNhd_const
    isPreconnected_univ (mem_univ (0 : ℂ)) (closure_mono hsub hcl)
  have hgi : G I = G 0 := he (mem_univ I)
  have hw : wr + I • wi = w := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wr, wi]
    rw [mul_comm I]
    exact re_add_im (w i)
  dsimp only [G] at hgi
  simp only [zero_smul, add_zero, add_assoc, hw] at hgi
  rw [hgi]
  simpa only [add_zero] using setIntegral_unitCube_add_real_of_periodic
    hf.continuous hp 0 (fun i => (w i).re)

end Complex
