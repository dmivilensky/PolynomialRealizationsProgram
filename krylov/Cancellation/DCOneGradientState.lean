import krylov.Cancellation.DCReferenceTools
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(b), actual one-gradient quadratic DC execution.
Use: derive genuine full-memory basis growth, positive direction factors and
real evaluated-gradient decomposition from the original data-only policy.
Source: native tilted/Galerkin trial identity, actual positive CG conjugacy
and true one-gradient history induction, without an assumed quadratic trajectory.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual incoming CG-direction factor of the original one-gradient DC policy.
Use: the real chosen estimate and the preceding genuine CG length determine
the source's t_k recurrence; all history data are from actual original queries.
Article: main_krylov, thm:dcs(b). -/
def dcIncomingFactor (estimate : History E → ℝ) (Q : E →L[ℝ] E) (g : E) : ℕ → ℝ
  | 0 => 1
  | k+1 => estimate (oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => Q) g k)*
      dcIncomingFactor estimate Q g k/CG.length Q g k

/-- The original one-gradient full-memory DC executor builds a true independent
CG flag and its actual incoming gradient has the derived positive CG residual
factor plus a genuine old-flag vector at every active reference prefix.
Use: derive every actual model domain and the real t_k trajectory from original
positive data-only estimates, without supplying either as an invariant field.
Article: main_krylov, thm:dcs(b).
Proof: genuine Galerkin and scaled conjugacy uniqueness identify each actual
query as its real old correction plus a nonzero scaled new CG direction.
This proves true stored-basis growth. The real quadratic gradient update and
the original CG recurrence give the next positive factor and old-flag component. -/
theorem dc_one_gradient_state (estimate : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0<estimate (oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => Q) g i))
    (k : ℕ) (hk : k≤N) :
    let H := oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => Q) g k
    0<dcIncomingFactor estimate Q g k ∧ LinearIndependent ℝ (windowSteps H.pairs) ∧
      pairSpan H.pairs=directionFlag Q g k ∧
      ∃ v∈directionFlag Q g k,H.gradient=dcIncomingFactor estimate Q g k • CG.gradient Q g k+v := by
  induction k with
  | zero =>
    refine ⟨zero_lt_one,?_,?_,0,Submodule.zero_mem _,?_⟩
    · change LinearIndependent ℝ (fun i : Fin 0 => windowSteps ([] : List (E × E)) i)
      exact linearIndependent_empty_type
    · change pairSpan ([] : List (E × E))=directionFlag Q g 0
      rw [directionFlag_zero]
      simp only [pairSpan,windowSteps_range,List.not_mem_nil,Set.ofPred_false,Set.image_empty,Submodule.span_empty]
    · change g=(1 : ℝ) • g+0
      rw [one_smul,add_zero]
  | succ k ih =>
    let m := dcSlideOneGradient fullMemory estimate
    let H := oneGradientRun m (fun _ => Q) g k
    let rho := dcIncomingFactor estimate Q g k
    let tau := estimate H
    obtain ⟨hrho,hLI,hspan,v,hv,hgrad⟩ := ih (by omega)
    have hprefix : ∀ i<k,CG.gradient Q g i≠0 := fun i hi => hpre i (by omega)
    have hInv := CG.invariant Q hQ hpos g k hprefix
    obtain ⟨hd,hAlpha,_⟩ := CG.invariant_line_pos Q hpos g k hInv (hpre k (by omega))
    have htau : 0<tau := ht k (by omega)
    have hy : ∀ i,windowImages H.pairs i=Q (windowSteps H.pairs i) := fun i =>
      oneGradientRun_pairs_quadratic m Q g k (H.pairs.get i) (List.get_mem _ i)
    have hstep : m.step H=CG.displacement Q g k-H.displacement+(tau*rho) • CG.direction Q g k :=
      dc_one_gradient_step_from_flag estimate Q hQ hpos g k hprefix H
        (oneGradientRun_quadratic_gradient m Q g k) hy hLI hspan rho v hv hgrad htau.ne'
    have hu : CG.displacement Q g k-H.displacement∈directionFlag Q g k := by
      rw [← hspan]
      exact (pairSpan H.pairs).sub_mem (by rw [hspan];exact displacement_mem_directionFlag Q g k) H.displacement_mem_pairSpan
    have hdflag : CG.direction Q g k∉directionFlag Q g k := by
      intro hmem
      exact (hpos _ hd).ne' (directionFlag_conjugate Q hQ hpos g k hprefix hmem)
    have hnew : m.step H∉pairSpan H.pairs := by
      rw [hspan,hstep]
      intro hmem
      have h := (directionFlag Q g k).smul_mem (tau*rho)⁻¹ ((directionFlag Q g k).sub_mem hmem hu)
      apply hdflag
      rw [add_sub_cancel_left,smul_smul,inv_mul_cancel₀ (mul_pos htau hrho).ne',one_smul] at h
      exact h
    have hLInew : LinearIndependent ℝ (windowSteps (oneGradientRun m (fun _ => Q) g (k+1)).pairs) := by
      rw [oneGradientRun_pairs_succ,windowSteps_cons]
      exact hLI.finCons hnew
    have hspanNew : pairSpan (oneGradientRun m (fun _ => Q) g (k+1)).pairs=directionFlag Q g (k+1) := by
      rw [oneGradientRun_pairs_succ,pairSpan_cons,hspan,hstep,
        trial_span_extension _ _ _ hu _ (mul_pos htau hrho).ne',directionFlag_succ]
    have hdisp : (oneGradientRun m (fun _ => Q) g (k+1)).displacement=
        CG.displacement Q g k+(tau*rho) • CG.direction Q g k := by
      change m.step H+H.displacement=_
      rw [hstep]
      abel
    have hnext : (oneGradientRun m (fun _ => Q) g (k+1)).gradient=
        CG.gradient Q g k+(tau*rho) • Q (CG.direction Q g k) := by
      rw [oneGradientRun_quadratic_gradient,hdisp,map_add,map_smul,CG.gradient_displacement]
      abel
    have hfactor : dcIncomingFactor estimate Q g (k+1)=tau*rho/CG.length Q g k := rfl
    have hfactorPos : 0<dcIncomingFactor estimate Q g (k+1) := by
      rw [hfactor]
      exact div_pos (mul_pos htau hrho) hAlpha
    have hcancel : dcIncomingFactor estimate Q g (k+1)*CG.length Q g k=tau*rho := by
      rw [hfactor,div_mul_cancel₀ _ hAlpha.ne']
    refine ⟨hfactorPos,hLInew,hspanNew,(1-dcIncomingFactor estimate Q g (k+1)) • CG.gradient Q g k,
      (directionFlag Q g (k+1)).smul_mem _ (cg_gradient_mem_next_directionFlag Q g k),?_⟩
    rw [hnext,CG.gradient_succ,smul_add,smul_smul,hcancel]
    module

end
end krylov.Cancellation
