import krylov.Convergence.VirtualFields
import krylov.Convergence.OneGradientOutputTaylor
import krylov.Methods.XRFC

/-!
Article: main_krylov, thm:V and lem:cycle-transfer.
Use: derive C-two regularity of the genuine full semantic output from
primitive observed trial charts. Initial-gradient drift and the semantic
output operator vary jointly in their true finite coordinates.
Source: actual XRFC query induction, virtual model domains and full CG termination.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.Stability
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Primitive C-two trial charts imply C-two of the complete independent
operator output at the true quadratic reference. Article: thm:V, V1. -/
theorem xrfcFiniteOutput_contDiffAt
    (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 →0 < inner ℝ v (Q v))
    (N : ℕ) (g : E) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>Q) g i)≠0)
    (hT : ∀ i<N,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _=>Q) g i)) :
    ContDiffAt ℝ 2 (oneGradientFiniteOutput (xrfcMethod fullMemory trial) Q N) (g,0) := by
  let A := fun z : E × ((Fin N → E →L[ℝ] E) × (E →L[ℝ] E))=>fcFiniteOperatorPath Q N z.2.1
  have hA (i : ℕ) : ContDiffAt ℝ 2 (fun z=>A z i) (g,0) := by
    by_cases hi : i<N
    · simp only [A,fcFiniteOperatorPath,dite_eq_left hi]
      let e := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin N=>E →L[ℝ] E) ⟨i,hi⟩
      exact contDiffAt_const.add (e.contDiff.contDiffAt.comp (g,0) contDiffAt_snd.fst)
    · simp only [A,fcFiniteOperatorPath,dite_eq_right hi]
      exact contDiffAt_const
  have hAz : A (g,0)=fun _=>Q := fcFiniteOperatorPath_zero Q N
  have hh := quadraticXRFC_output_contDiffAt trial A (fun z=>Q+z.2.2) Prod.fst (g,0)
    hA (contDiffAt_const.add contDiffAt_snd.snd) contDiffAt_fst Q hAz hQ hpos N hpre ht
    (by rw [hAz];exact hT)
  exact hh.2

/-- The complete finite semantic map is exactly the true quadratic zero
at every full-atom reference with nonzero primitive trials. Article: thm:V. -/
theorem xrfcFiniteOutput_reference_zero {n : ℕ}
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial)
      (fun _=>cgOperator base) g i)≠0) :
    oneGradientFiniteOutput (xrfcMethod fullMemory trial) (cgOperator base) n (g,0)=0 := by
  have hh := (xrfc_full_terminates base hb g trial (fun i hi=>ht i (by omega))).2.1
  rw [hcount] at hh
  simpa [oneGradientFiniteOutput,fcFiniteOperatorPath_zero] using hh

end
end krylov.Convergence
