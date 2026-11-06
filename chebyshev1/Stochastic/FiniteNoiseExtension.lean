import Mathlib.Probability.Independence.Basic

/-! Finite independent noise families may be continued by deterministic zero on
their original probability space. No extra random samples are introduced. -/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F] [Zero F]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

def zeroAfter (N : ℕ) (Z : ℕ → Ω → F) (s : ℕ) : Ω → F :=
  if s<N then Z s else fun _ => 0

omit [MeasurableSpace Ω] [MeasurableSpace F] in
theorem zeroAfter_eq (N : ℕ) (Z : ℕ → Ω → F) {s : ℕ} (hs : s<N) :
    zeroAfter N Z s=Z s := by simp only [zeroAfter,hs,ite_true]

omit [IsProbabilityMeasure μ] in
theorem zeroAfter_measurable (N : ℕ) (Z : ℕ → Ω → F)
    (hm : ∀ s<N, Measurable (Z s)) (s : ℕ) : Measurable (zeroAfter N Z s) := by
  by_cases hs : s<N
  · rw [zeroAfter_eq N Z hs]
    exact hm s hs
  · simp only [zeroAfter,hs,ite_false]
    exact measurable_const

/-- An infinite independent family is derived by deterministic continuation;
independence is assumed only for the finitely many active samples. -/
theorem zeroAfter_iIndepFun (N : ℕ) (Z : ℕ → Ω → F)
    (hind : iIndepFun (fun s : Fin N => Z s.val) μ) : iIndepFun (zeroAfter N Z) μ := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  let T := S.filter (fun s => s<N)
  by_cases hbad : ∃ s∈S, ¬s<N ∧ (0:F)∉sets s
  · obtain ⟨s,hs,hsN,hzero⟩ := hbad
    have he : zeroAfter N Z s ⁻¹' sets s=∅ := by simp [zeroAfter,hsN,hzero]
    have hall : (⋂ t∈S, zeroAfter N Z t ⁻¹' sets t)=∅ := by
      ext ω
      constructor
      · intro hω
        have hh := Set.mem_iInter.mp (Set.mem_iInter.mp hω s) hs
        rw [he] at hh
        exact hh
      · intro hh
        exact hh.elim
    rw [hall,measure_empty]
    exact (Finset.prod_eq_zero hs (by rw [he,measure_empty])).symm
  · have hgood (s : ℕ) (hs : s∈S) (hsN : ¬s<N) : (0:F)∈sets s := by
      by_contra hh
      exact hbad ⟨s,hs,hsN,hh⟩
    have hall : (⋂ t∈S, zeroAfter N Z t ⁻¹' sets t)=(⋂ t∈T, Z t ⁻¹' sets t) := by
      ext ω
      simp only [Set.mem_iInter]
      constructor
      · intro hω t ht
        have htS := (Finset.mem_filter.mp ht).1
        have htN := (Finset.mem_filter.mp ht).2
        simpa only [zeroAfter_eq N Z htN] using hω t htS
      · intro hω t ht
        by_cases htN : t<N
        · rw [zeroAfter_eq N Z htN]
          exact hω t (Finset.mem_filter.mpr ⟨ht,htN⟩)
        · simpa only [zeroAfter,htN,ite_false,Set.mem_preimage] using hgood t ht htN
    have hprod : (∏ t∈S, μ (zeroAfter N Z t ⁻¹' sets t))=
        ∏ t∈T, μ (Z t ⁻¹' sets t) := by
      calc
        _ = ∏ t∈S, if t<N then μ (Z t ⁻¹' sets t) else 1 := by
          apply Finset.prod_congr rfl
          intro t ht
          by_cases htN : t<N
          · simp only [zeroAfter_eq N Z htN,htN,ite_true]
          · simp [zeroAfter,htN,hgood t ht htN]
        _ = _ := (Finset.prod_filter _ _).symm
    rw [hall,hprod]
    let f : T → Fin N := fun t => ⟨t.val,(Finset.mem_filter.mp t.property).2⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      exact congrArg Fin.val hij
    have hi : iIndepFun (fun t : T => Z t.val) μ := hind.precomp hf
    have hh := hi.measure_inter_preimage_eq_mul Finset.univ
      (sets := fun t : T => sets t.val)
      (fun t _ => hsets t.val (Finset.mem_filter.mp t.property).1)
    have he : (⋂ t : T, Z t.val ⁻¹' sets t.val)=(⋂ t∈T, Z t ⁻¹' sets t) := by
      ext ω
      simp
    simp only [Finset.mem_univ,Set.iInter_true] at hh
    rw [he,Finset.prod_coe_sort T (fun t => μ (Z t ⁻¹' sets t))] at hh
    exact hh

end
end chebyshev1.Stochastic
