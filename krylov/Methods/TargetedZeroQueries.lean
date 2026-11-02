import krylov.Methods.TargetedReference

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist, genuine zero queries on the chosen reference.
Use: verify the real targeted one-query policy satisfies the exact correction part of CG consistency on its fixed prior quadratic data.
Source: the actual zero inverse-model right-hand side and genuine chosen-reference CG gradients and directions.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If the actual searched gradient equals the genuine fixed target, the real target-model correction tree queries exactly zero.
Use: If the actual searched gradient equals the genuine fixed target, the real target-model correction tree queries exactly zero.
Article: main_krylov, apB:prop:consist, genuine zero queries on the chosen reference.
Proof: The true gradient difference is zero, hence all genuine inverse-model coefficients and the actual synthesized query are zero. -/
theorem targetedCorrection_at_target (target : E) (H : History E) (z : E)
    (h : searchedGradient H.gradient ((fcMethod fullMemory).direction H) z=target) :
    targetedCorrection target H z=.query 0 (fun _ => .done) := by
  -- The genuine target difference is zero, so the actual model solve has zero right-hand side and makes a real zero query.
  unfold targetedCorrection
  dsimp only
  rw [h,sub_self]
  have hz : coordinates (windowSteps (((fcMethod fullMemory).direction H,z)::H.pairs)) (0 : E)=0 := by
    ext i
    exact inner_zero_right _
  change CorrectionTree.query _ (fun _ => .done)=_
  rw [modelCoefficients_zero _ _ _ hz]
  simp only [combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero]

/-- Every actual correction query of the genuine targeted method is zero on its chosen quadratic reference, including true stopped tails.
Use: Every actual correction query of the genuine targeted method is zero on its chosen quadratic reference, including true stopped tails.
Article: main_krylov, apB:prop:consist, genuine zero queries on the chosen reference.
Proof: At the actual designated iteration the real searched CG gradient equals its fixed target; all other genuine correction branches are empty. -/
theorem targetedFinalMethod_reference_zero (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N k : ℕ) :
    let m := targetedFinalMethod N (CG.gradient Q g N)
    let H := methodRun m (fun _ => Q) (fun _ => Q) g k
    ZeroCorrections (m.correction H (Q (m.direction H))) Q
      (searchedGradient H.gradient (m.direction H) (Q (m.direction H))) := by
  -- The actual chosen-reference gradients and directions are genuine CG even though no global consistency is assumed.
  let m := targetedFinalMethod N (CG.gradient Q g N)
  let H := methodRun m (fun _ => Q) (fun _ => Q) g k
  have hg : H.gradient=CG.gradient Q g k := (targetedFinalMethod_static Q hQ hpos g N k).1
  have hd : (fcMethod fullMemory).direction H=CG.direction Q g k :=
    targetedFinalMethod_reference_direction Q hQ hpos g N k
  change ZeroCorrections (if H.records.length+1=N then _ else _) Q _
  -- Only the actual target iteration can query; its true incoming gradient equals the fixed target.
  by_cases he : H.records.length+1=N
  · rw [ite_eq_left he]
    have hkN : k+1=N := by have hh : H.records.length=k := methodRun_length _ _ _ _ k;omega
    have hgp : searchedGradient H.gradient ((fcMethod fullMemory).direction H) (Q (m.direction H))=CG.gradient Q g N := by
      change searchedGradient H.gradient ((fcMethod fullMemory).direction H) (Q ((fcMethod fullMemory).direction H))=_
      rw [hg,hd]
      change CG.gradient Q g (k+1)=CG.gradient Q g N
      rw [hkN]
    rw [targetedCorrection_at_target _ _ _ hgp]
    exact ⟨rfl,trivial⟩
  · rw [ite_eq_right he]
    trivial
end
end krylov.Methods
