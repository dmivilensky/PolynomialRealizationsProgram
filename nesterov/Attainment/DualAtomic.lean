import nesterov.Attainment.Active

/-! Exact atomic decomposition of the actual dual probability measure once
strict minimizer reserve and the active-lag bound remove the compactification points. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace nesterov.Attainment
open Spectral

theorem exists_finiteDualMeasure_of_support (ν : DualMeasure) {F : Set DualLabel} [Fintype F]
    (hnull : (ν : Measure DualLabel) Fᶜ=0) :
    ∃ w : F → NNReal, ∃ hw : ∑ j,w j=1,
      finiteDualMeasure w (fun j => j.val) hw=ν := by
  classical
  have hF : F.Finite := Set.toFinite F
  let S := hF.toFinset
  have hS (c : DualLabel) : c ∈ S ↔ c ∈ F := hF.mem_toFinset
  have hae : ∀ᵐ c ∂(ν : Measure DualLabel), c ∈ S := by
    rw [ae_iff]
    have he : {c : DualLabel | c ∉ S}=Fᶜ := by ext c; simp only [Set.mem_ofPred_eq,Set.mem_compl_iff,hS]
    rw [he]
    exact hnull
  have hmeasure : (ν : Measure DualLabel)=
      ∑ c ∈ S, (ν : Measure DualLabel) {c} • Measure.dirac c :=
    Measure.ae_mem_finset_iff.mp hae
  let w : F → NNReal := fun j => ((ν : Measure DualLabel) {j.val}).toNNReal
  have hweight (j : F) : (w j : ENNReal)=(ν : Measure DualLabel) {j.val} := by
    exact ENNReal.coe_toNNReal (measure_ne_top _ _)
  have hsum : (∑ j : F,(ν : Measure DualLabel) {j.val})=1 := by
    rw [← Finset.sum_subtype S hS (fun c => (ν : Measure DualLabel) {c}),
      MeasureTheory.sum_measure_singleton]
    have he : (S : Set DualLabel)=F := by ext c; exact hS c
    rw [he,measure_of_measure_compl_eq_zero hnull,measure_univ]
  have hw : ∑ j,w j=1 := by
    apply ENNReal.coe_injective
    push_cast
    simp only [hweight]
    exact hsum
  refine ⟨w,hw,?_⟩
  apply Subtype.ext
  change (∑ j : F,(w j : ENNReal) • Measure.dirac j.val)=(ν : Measure DualLabel)
  simp_rw [hweight]
  exact (Finset.sum_subtype S hS (fun c => (ν : Measure DualLabel) {c} • Measure.dirac c)).symm.trans
    hmeasure.symm

end nesterov.Attainment
