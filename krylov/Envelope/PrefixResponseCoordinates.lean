import krylov.Envelope.ExploredFlag
import krylov.Variation.ResponseCoordinates

set_option autoImplicit false
/-!
Article: main_krylov, apB:eq:nu and cor:lm, genuine finite-prefix FC response coordinates.
Use: retain actual finite unexplored CG tails before exhaustion and identify
their true old-flag projection coordinates without requiring a full ambient
active basis or replacing the prefix by the terminal response.
Source: actual finite CG orthonormal prefixes, true old-flag projections
and the previously proved finite triangular summation identities.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Finset krylov.Reference krylov.Secant krylov.Variation
open scoped InnerProductSpace BigOperators
variable {n N : ℕ}

/-- Each actual later nonstagnating CG unit step is orthogonal to every genuine earlier old flag on its true finite prefix.
Use: Each actual later nonstagnating CG unit step is orthogonal to every genuine earlier old flag on its true finite prefix.
Article: main_krylov, apB:eq:nu and cor:lm, genuine finite-prefix FC response coordinates.
Proof: The actual finite CG prefix is orthonormal; extend its genuine earlier-generator zero pairings through the real old span. -/
theorem unitStep_prefix_oldFlag_orthogonal (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : N≤referenceAtomCount base hb g)
    {i l : ℕ} (hi : i<N) (hli : l < i) : canonicalCGUnitStep base g i∈(oldFlag base g l)ᗮ := by
  -- Use the true active finite CG prefix, without a full ambient orthonormal basis premise.
  have hq := canonicalCGUnitStep_orthonormal base hb g N (fun j hj => cg_nonstagnation base hb g j (hj.trans_le hN))
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨j,hj,rfl⟩ := hv
    change j≤l at hj
    have he : (⟨j,by omega⟩ : Fin N)≠⟨i,hi⟩ := by
      intro he
      have he' : j=i := congrArg Fin.val he
      omega
    simpa only [Fin.val_mk] using hq.inner_eq_zero he
  | zero => exact inner_zero_left _
  | add v w _ _ hv hw => rw [inner_add_left,hv,hw,add_zero]
  | smul a v _ hv => rw [real_inner_smul_left,hv,mul_zero]

/-- The genuine pairing of an actual finite-prefix CG step with a true old-flag projection retains exactly the flags containing its real index.
Use: The genuine pairing of an actual finite-prefix CG step with a true old-flag projection retains exactly the flags containing its real index.
Article: main_krylov, apB:eq:nu and cor:lm, genuine finite-prefix FC response coordinates.
Proof: Transfer the true self-adjoint orthogonal projection to the actual normalized CG step; genuine membership and true later-step orthogonality give the two real cases. -/
theorem step_inner_oldFlag_prefix (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : N≤referenceAtomCount base hb g)
    {i : ℕ} (hi : i<N) (l : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (canonicalCGStep base g i) ((oldFlag base g l).starProjection v)=
      if i≤l then inner ℝ (canonicalCGStep base g i) v else 0 := by
  -- Retain the actual physical step scale outside the genuine normalized projector identity.
  have hs : canonicalCGStep base g i=‖canonicalCGStep base g i‖ • canonicalCGUnitStep base g i :=
    (NormedSpace.norm_smul_normalize _).symm
  rw [hs,real_inner_smul_left,← Submodule.inner_starProjection_left_eq_right]
  by_cases hil : i≤l
  · rw [(oldFlag base g l).starProjection_eq_self_iff.mpr (unitStep_mem_oldFlag base g hil),ite_eq_left hil,hs,real_inner_smul_left]
  · have hp : (oldFlag base g l).starProjection (canonicalCGUnitStep base g i)=0 := by
      change ((oldFlag base g l).orthogonalProjectionOnto (canonicalCGUnitStep base g i) : EuclideanSpace ℝ (Fin n))=0
      rw [(oldFlag base g l).orthogonalProjectionOnto_eq_zero_iff.mpr
        (unitStep_prefix_oldFlag_orthogonal base hb g hN hi (by omega))]
      rfl
    rw [hp,inner_zero_left,mul_zero,ite_eq_right hil]

/-- The true finite-prefix triangular old-flag response formed with actual remaining steps only up to the genuine horizon.
Use: The true finite-prefix triangular old-flag response formed with actual remaining steps only up to the genuine horizon.
Article: main_krylov, apB:eq:nu and cor:lm, genuine finite-prefix FC response coordinates.
Proof: Use the actual old CG flags and true finite canonical step tails. -/
def partialCycleResponse (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) : EuclideanSpace ℝ (Fin n) :=
  ∑ l∈range N, (oldFlag base g l).starProjection
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (E l) (∑ j∈Ico (l+1) N, canonicalCGStep base g j))

/-- The genuine finite-prefix triangular response belongs to the true explored CG flag.
Use: The genuine finite-prefix triangular response belongs to the true explored CG flag.
Article: main_krylov, apB:eq:nu and cor:lm, genuine finite-prefix FC response coordinates.
Proof: Each real projected summand belongs to an actual old flag generated entirely inside the genuine finite prefix. -/
theorem partialCycleResponse_mem (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) : partialCycleResponse base g N E∈exploredFlag base g N := by
  -- Every actual old projected summand is generated by genuine steps strictly within this finite horizon.
  apply Submodule.sum_mem
  intro l hl
  have hle : oldFlag base g l≤exploredFlag base g N := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    exact Submodule.subset_span ⟨(⟨i,by have := mem_range.mp hl;change i≤l at hi;omega⟩ : Fin N),rfl⟩
  exact hle ((oldFlag base g l).starProjection_apply_mem _)

/-- The actual finite-prefix triangular response has exactly the true CG-step coordinates of the real cumulative-increment staircase.
Use: The actual finite-prefix triangular response has exactly the true CG-step coordinates of the real cumulative-increment staircase.
Article: main_krylov, apB:eq:nu and cor:lm, genuine finite-prefix FC response coordinates.
Proof: Use genuine old-flag coordinate selection, expand the actual finite remaining-step tail and reuse the proved finite triangular sum interchange. -/
theorem partialCycleResponse_coordinates (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : N≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) {i : ℕ} (hi : i<N) :
    inner ℝ (canonicalCGStep base g i) (partialCycleResponse base g N E)=
      ∑ j∈Ico (i+1) N, inner ℝ (canonicalCGStep base g i)
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (∑ l∈Ico i j, E l) (canonicalCGStep base g j)) := by
  -- The last flag has zero tail, so the full range N has the same response as the printed preterminal range.
  unfold partialCycleResponse
  rw [inner_sum]
  simp_rw [step_inner_oldFlag_prefix base hb g hN hi]
  rw [← sum_filter]
  have hset : (range N).filter (fun l => i≤l)=Ico i N := by ext l; simp only [mem_filter,mem_range,mem_Ico]; tauto
  rw [hset]
  calc
    _ = ∑ l∈Ico i N, ∑ j∈Ico (l+1) N, inner ℝ (canonicalCGStep base g i)
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (E l) (canonicalCGStep base g j)) := by
      apply sum_congr rfl
      intro l hl
      rw [map_sum,inner_sum]
    _ = ∑ j∈Ico i N, ∑ l∈Ico i j, inner ℝ (canonicalCGStep base g i)
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (E l) (canonicalCGStep base g j)) := sum_Ico_Ico_comm' i N _
    _ = _ := by
      rw [sum_eq_sum_Ico_succ_bot (by omega : i<N)]
      simp only [Ico_self,sum_empty,zero_add]
      apply sum_congr rfl
      intro j _
      rw [map_sum,_root_.sum_apply,inner_sum]

end
end krylov.Envelope
