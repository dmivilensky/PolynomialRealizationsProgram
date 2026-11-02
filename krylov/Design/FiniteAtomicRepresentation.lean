import krylov.Design.PolynomialSupportBound
import krylov.Design.AtomExtension
import Mathlib.Data.Fintype.EquivFin

/-!
Article: main_krylov, thm:B and apC:lem:natoms, actual finite spectral realization.
Use: recover positive distinct finite spectral data from a genuine probability
measure with finite topological support. Zero-mass entries are discarded, and
the resulting weighted Dirac sum is proved equal to the original measure.
Source: mathlib's finite-support Dirac decomposition and finite enumeration.
-/

namespace krylov.Design
noncomputable section
open Polynomial MeasureTheory Matrix Set jacobi.Finite
open scoped BigOperators

/-- Every finite-support physical probability measure has an equal positive finite spectral realization, with no increase in support size.
Article: main_krylov, thm:B and apC:lem:natoms.
Proof: use the actual finite Dirac decomposition, remove all zero masses, and
enumerate the remaining original interval points. -/
theorem finite_support_atomic_representation (I : chebyshev1.SpectralInterval)
    (ν : ProbabilityMeasure (Spectrum I)) (hf : (ν : Measure (Spectrum I)).support.Finite) :
    ∃ K : ℕ, ∃ M : DiscreteMeasure K, ∃ hM : ∀ i, M.node i ∈ Icc I.mu I.L,
      K ≤ (ν : Measure (Spectrum I)).support.ncard ∧
      ν = atomicProbability M (fun i => ⟨M.node i, hM i⟩ : Fin K → Spectrum I) := by
  let s := hf.toFinset
  let t := s.filter (fun x => (ν : Measure (Spectrum I)) {x} ≠ 0)
  have hae : ∀ᵐ x ∂(ν : Measure (Spectrum I)), x ∈ s := by
    filter_upwards [(ν : Measure (Spectrum I)).support_mem_ae] with x hx
    exact hf.mem_toFinset.mpr hx
  have hrep : (ν : Measure (Spectrum I)) =
      ∑ x ∈ t, (ν : Measure (Spectrum I)) {x} • Measure.dirac x := by
    calc
      _ = ∑ x ∈ s, (ν : Measure (Spectrum I)) {x} • Measure.dirac x :=
        Measure.ae_mem_finset_iff.mp hae
      _ = _ := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : (ν : Measure (Spectrum I)) {x} = 0
        · simp [hx]
        · simp [hx]
  have hprob : ∑ x ∈ t, (ν : Measure (Spectrum I)) {x} = 1 := by
    have h := congrArg (fun μ : Measure (Spectrum I) => μ Set.univ) hrep
    simpa only [measure_univ, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, mul_one] using h.symm
  have hprobReal : ∑ x ∈ t, ((ν : Measure (Spectrum I)) {x}).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun x _ => measure_ne_top (ν : Measure (Spectrum I)) {x}),
      hprob, ENNReal.toReal_one]
  let e : Fin t.card ≃ t := t.equivFin.symm
  let M : DiscreteMeasure t.card := {
    node := fun i => (e i).val.val
    distinct := fun i j hij => e.injective (Subtype.ext (Subtype.ext hij))
    weight := fun i => ((ν : Measure (Spectrum I)) {(e i).val}).toReal
    positive := fun i => ENNReal.toReal_pos (Finset.mem_filter.mp (e i).property).2
      (measure_ne_top (ν : Measure (Spectrum I)) {(e i).val})
    probability := by
      calc
        _ = ∑ x : t, ((ν : Measure (Spectrum I)) {x.val}).toReal :=
          Fintype.sum_equiv e _ _ (fun _ => rfl)
        _ = 1 := by
          change (∑ x ∈ t.attach, ((ν : Measure (Spectrum I)) {x.val}).toReal) = 1
          exact (Finset.sum_attach t (fun x : Spectrum I =>
            ((ν : Measure (Spectrum I)) {x}).toReal)).trans hprobReal }
  have hM : ∀ i, M.node i ∈ Icc I.mu I.L := fun i => (e i).val.property
  refine ⟨t.card, M, hM, ?_, ?_⟩
  · exact (Finset.card_filter_le _ _).trans_eq (Set.ncard_eq_toFinset_card _ hf).symm
  · apply Subtype.ext
    change (ν : Measure (Spectrum I)) =
      ∑ i : Fin t.card, ENNReal.ofReal (M.weight i) • Measure.dirac (⟨M.node i, hM i⟩ : Spectrum I)
    rw [hrep]
    symm
    calc
      _ = ∑ x : t, (ν : Measure (Spectrum I)) {x.val} • Measure.dirac x.val := by
        apply Fintype.sum_equiv e
        intro i
        change ENNReal.ofReal (((ν : Measure (Spectrum I)) {(e i).val}).toReal) •
          Measure.dirac (e i).val = _
        rw [ENNReal.ofReal_toReal (measure_ne_top (ν : Measure (Spectrum I)) {(e i).val})]
      _ = _ := by
        change (∑ x ∈ t.attach, (ν : Measure (Spectrum I)) {x.val} • Measure.dirac x.val) = _
        exact Finset.sum_attach t (fun x => (ν : Measure (Spectrum I)) {x} • Measure.dirac x)

end
end krylov.Design
