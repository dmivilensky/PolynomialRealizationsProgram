import krylov.Functions.PlanarUniformBounds

/-!
Article: main_krylov, thm:Fplanar, attained full planar information radius.
Use: retain one true maximizing chord before choosing the method or scale,
so the genuine fourth-order lower remainder has one fixed uniform constant.
Source: the actual diagonal tensor ball is a closed subset of its proved
coefficient unit cube; the true chord objective is continuous.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Tensor.BinaryCubic

/-- Reconstruction preserves the entire actual finite coefficient vector.
Article: main_krylov, thm:Fplanar. -/
theorem binaryCoefficientVector_fromVector (q : Fin 4 → ℝ) :
    binaryCoefficientVector (binaryFromVector q)=q := by
  funext i
  fin_cases i <;> rfl

/-- The genuine diagonal unit ball is closed in its four real coordinates.
Article: main_krylov, thm:Fplanar. -/
theorem binaryFromVector_inBall_isClosed :
    IsClosed {q : Fin 4 → ℝ | (binaryFromVector q).InBall} := by
  change IsClosed {q : Fin 4 → ℝ | ∀ c s : ℝ, c^2+s^2=1 → |(binaryFromVector q).eval c s|≤1}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro c
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro _
  apply isClosed_le _ continuous_const
  unfold binaryFromVector krylov.Tensor.BinaryCubic.eval
  fun_prop

/-- The full true observation-chord set is compact in actual coefficients.
Article: main_krylov, thm:Fplanar. -/
theorem binaryChord_isCompact (r : ℝ) :
    IsCompact {z : (Fin 4 → ℝ) × (Fin 4 → ℝ) |
      Chord r (binaryFromVector z.1) (binaryFromVector z.2)} := by
  have hc : IsClosed {z : (Fin 4 → ℝ) × (Fin 4 → ℝ) |
      Chord r (binaryFromVector z.1) (binaryFromVector z.2)} := by
    unfold Chord
    apply IsClosed.inter
      (binaryFromVector_inBall_isClosed.preimage continuous_fst)
    apply IsClosed.inter
      (binaryFromVector_inBall_isClosed.preimage continuous_snd)
    apply IsClosed.inter (isClosed_eq (by unfold binaryFromVector; fun_prop) (by unfold binaryFromVector; fun_prop))
    apply IsClosed.inter <;> apply isClosed_eq <;> unfold binaryFromVector <;> fun_prop
  apply (isCompact_closedBall (0 : (Fin 4 → ℝ) × (Fin 4 → ℝ)) 1).of_isClosed_subset hc
  intro z hz
  have h0 := binaryCoefficientVector_bound hz.1
  have h1 := binaryCoefficientVector_bound hz.2.1
  rw [binaryCoefficientVector_fromVector] at h0 h1
  simpa only [mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff] using And.intro h0 h1

/-- One actual admissible chord attains the true supremum M_F(r).
Article: main_krylov, thm:Fplanar. -/
theorem exists_chord_attaining_fibreMinimax (r : ℝ) :
    ∃ t u : krylov.Tensor.BinaryCubic, Chord r t u ∧ chordValue r t u=fibreMinimax r := by
  let C := {z : (Fin 4 → ℝ) × (Fin 4 → ℝ) | Chord r (binaryFromVector z.1) (binaryFromVector z.2)}
  let F := fun z : (Fin 4 → ℝ) × (Fin 4 → ℝ) => chordValue r (binaryFromVector z.1) (binaryFromVector z.2)
  have hne : C.Nonempty := by
    refine ⟨0,?_⟩
    change Chord r (⟨0,0,0,0⟩ : krylov.Tensor.BinaryCubic) ⟨0,0,0,0⟩
    exact ⟨zero_inBall,zero_inBall,rfl,rfl,rfl⟩
  have hF : Continuous F := by unfold F chordValue binaryFromVector; fun_prop
  obtain ⟨z,hz,hmax⟩ := (binaryChord_isCompact r).exists_isMaxOn hne hF.continuousOn
  refine ⟨binaryFromVector z.1,binaryFromVector z.2,hz,le_antisymm ?_ ?_⟩
  · exact le_csSup (chordValues_bddAbove r) ⟨_,_,hz,rfl⟩
  · apply csSup_le ⟨0,zero_mem_chordValues r⟩
    rintro v ⟨t,u,h,rfl⟩
    have hm : (binaryCoefficientVector t,binaryCoefficientVector u)∈C := by
      change Chord r (binaryFromVector (binaryCoefficientVector t)) (binaryFromVector (binaryCoefficientVector u))
      simpa only [binaryFromVector_coefficientVector] using h
    have hb : F (binaryCoefficientVector t,binaryCoefficientVector u)≤F z := hmax hm
    simpa only [F,binaryFromVector_coefficientVector] using hb

end
end krylov.Functions
