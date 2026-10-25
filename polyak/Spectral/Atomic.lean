import polyak.Waves.Finite
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
Article: finite support of optimal spectra and its use in the original startup realization.
Use: a probability spectrum concentrated on a finite set is exactly the already
defined finiteSpectrum; its weights are actual nonnegative singleton masses.
Proof: the finite-support Dirac decomposition, finite additivity and probability mass one.
-/

noncomputable section

open MeasureTheory

namespace polyak.Spectral

/-- Article: exact atomic representation of a spectrum concentrated on a finite carrier.
Use: instantiate the arbitrary-set support theorem with the finite-mixture startup theorem.
Zero masses are permitted, as in the established finiteSpectrum definition. -/
theorem exists_finiteSpectrum_of_support (ν : Spectrum) {F : Set Frequency} [Fintype F]
    (hnull : (ν : Measure Frequency) Fᶜ=0) :
    ∃ w : F → NNReal, ∃ hw : ∑ j,w j=1,
      Waves.finiteSpectrum w (fun j => j.val) hw=ν := by
  classical
  have hF : F.Finite := Set.toFinite F
  let S := hF.toFinset
  have hS (c : Frequency) : c ∈ S ↔ c ∈ F := hF.mem_toFinset
  have hae : ∀ᵐ c ∂(ν : Measure Frequency), c ∈ S := by
    rw [ae_iff]
    have he : {c : Frequency | c ∉ S}=Fᶜ := by ext c; simp only [Set.mem_ofPred_eq,Set.mem_compl_iff,hS]
    rw [he]
    exact hnull
  have hmeasure : (ν : Measure Frequency)=
      ∑ c ∈ S, (ν : Measure Frequency) {c} • Measure.dirac c :=
    Measure.ae_mem_finset_iff.mp hae
  let w : F → NNReal := fun j => ((ν : Measure Frequency) {j.val}).toNNReal
  have hweight (j : F) : (w j : ENNReal)=(ν : Measure Frequency) {j.val} := by
    exact ENNReal.coe_toNNReal (measure_ne_top _ _)
  have hsum : (∑ j : F,(ν : Measure Frequency) {j.val})=1 := by
    rw [← Finset.sum_subtype S hS (fun c => (ν : Measure Frequency) {c}),
      MeasureTheory.sum_measure_singleton]
    have he : (S : Set Frequency)=F := by ext c; exact hS c
    rw [he,measure_of_measure_compl_eq_zero hnull,measure_univ]
  have hw : ∑ j,w j=1 := by
    apply ENNReal.coe_injective
    push_cast
    simp only [hweight]
    exact hsum
  refine ⟨w,hw,?_⟩
  apply Subtype.ext
  change (∑ j : F,(w j : ENNReal) • Measure.dirac j.val)=(ν : Measure Frequency)
  simp_rw [hweight]
  exact (Finset.sum_subtype S hS (fun c => (ν : Measure Frequency) {c} • Measure.dirac c)).symm.trans
    hmeasure.symm

end polyak.Spectral
