import krylov.Information.ObservedCentreGauge
import krylov.Information.ModelReversal
import krylov.Correction.ReferenceBasis

/-!
Article: main_krylov, s4:cor-Q, actual RFC model and common physical centre.
Use: identify the real stored full model with the same physical centre used
by the method-independent pre-quadratic reflected twin construction.
Source: actual common CG steps and probe actions, true positive reference
line lengths, exact finite reversal and diagonal inverse-congruence invariance.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The actual full RFC correction basis equals its genuine common quadratic reference basis.
Use: Preserve the real recorded total-step columns and actual terminal raw direction.
Article: main_krylov, s4:cor-Q, H=UᵀJ_DU.
Proof: Complete prefix shadow fixes the true terminal decision state; all earlier actually executed steps are the proved physical reference CG steps. -/
theorem Scenario.PreQuadratic.rfc_stepBasis {S : Scenario (N+1)}
    {Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (h : S.PreQuadratic (cgOperator Q) g N) :
    probedStepBasis (rfcMethod fullMemory 1) S.probeOracle (S.correctionOracle N) g N=
      referenceModelBasis Q g N := by
  -- Fix the real current decision state and all actual earlier recorded CG steps.
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (N+1)))
  have hm := rfcMethod_consistent fullMemory (fun _ ha => ha) 1 (E := EuclideanSpace ℝ (Fin (N+1)))
  -- Old measured secants inherit the true reference-direction probe action by linearity.
  have hp := cgOperator_positive Q hQ
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change m.direction (methodRun m _ _ g N)=_
    rw [h.run hp.1 hp.2 m hm le_rfl]
    rfl
  · change probedStep m _ _ g (N-1-j.val)=_
    rw [h.step hp.1 hp.2 m hm (by have := j.isLt; omega)]
    exact (referenceModelBasis_succ Q hQ g N j).symm

/-- Each real augmented observed-image column is its actual chronological physical probe applied to that same real stored column.
Use: Relate the actual newest-first measured secants to chronological latest information.
Article: main_krylov, s4:cor-Q, H=UᵀJ_DU.
Proof: The head is the true current probe. Each genuine old measured secant is the reference operator on the common CG step; the primitive pre-quadratic probe agreement extends to that step by its true line scalar. -/
theorem Scenario.PreQuadratic.imageBasis {S : Scenario (N+1)}
    {Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (h : S.PreQuadratic (cgOperator Q) g N)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m) :
    probedImageBasis m S.probeOracle (S.correctionOracle N) g N=
      fun i => S.probeOracle (N-i.val) (probedStepBasis m S.probeOracle (S.correctionOracle N) g N i) := by
  -- Transfer the actual old probe action to each real CG step by its true line scalar.
  have hp := cgOperator_positive Q hQ
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · have hj : N-1-j.val<N := by have := j.isLt; omega
    change probedSecant m _ _ g (N-1-j.val)=S.probeOracle (N-j.succ.val) (probedStep m _ _ g (N-1-j.val))
    rw [h.step hp.1 hp.2 m hm hj,h.secant hp.1 hp.2 m hm hj]
    rw [show N-j.succ.val=N-1-j.val by simp only [Fin.val_succ]; omega]
    simp only [referenceStep,map_smul,h _ hj]

/-- The genuine native full reference columns are reversed chronological CG directions times nonzero actual line scales.
Use: cancel the real stored step lengths when identifying the physical common centre.
Article: main_krylov, s4:cor-Q, actual full reference column scales.
Proof: full active CG gives positive true line lengths. The actual head scale is one and every older recorded column is precisely its real physical CG step. -/
theorem referenceModelBasis_direction_scales
    (Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hQ : Q.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount Q hQ g=N+1) :
    ∃ s : Fin (N+1) → ℝ, (∀ i, s i≠0) ∧
      ∀ i, referenceModelBasis Q g N i=s i • CG.direction (cgOperator Q) g (N-i.val) := by
  -- The real old line scales are nonzero on the full active reference domain.
  let s : Fin (N+1) → ℝ := Fin.cons 1 (fun j => cgLine Q g (N-1-j.val))
  have hp := cgOperator_positive Q hQ
  have hl (j : ℕ) (hj : j≤N) : cgLine Q g j≠0 := by
    exact (CG.invariant_line_pos _ hp.2 g j
      (CG.invariant _ hp.1 hp.2 g j (fun i hi => cg_nonstagnation Q hQ g i (by omega)))
      (cg_nonstagnation Q hQ g j (by omega))).2.1.ne'
  refine ⟨s,?_,?_⟩
  · intro i
    refine Fin.cases (by simp only [s,Fin.cons_zero,ne_eq,one_ne_zero,not_false_eq_true])
      (fun j => ?_) i
    exact hl _ (by omega)
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [referenceModelBasis_zero Q hQ,s,Fin.cons_zero,Fin.val_zero,Nat.sub_zero,one_smul]
    · rw [referenceModelBasis_succ Q hQ]
      simp only [s,Fin.cons_succ,cgStep,Fin.val_succ,show N-(j.val+1)=N-1-j.val by omega]


/-- The common pre-quadratic physical centre is exactly the latest model of the original physical chronological probes.
Use: Remove the intermediate forward-coordinate representation from the actual observed centre.
Article: main_krylov, s4:cor-Q, H=UᵀJ_DU.
Proof: The genuine full CG direction basis is nonsingular, so forward coordinate transport followed by physical inverse transport recovers the original physical source. -/
theorem Scenario.preQuadraticCentre_observed (S : Scenario (N+1))
    (Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hQ : Q.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount Q hQ g=N+1) :
    S.preQuadraticCentre Q g=observedPhysicalCentre
      (fullBasisMatrix (referenceDirectionColumns Q g)) S.probe := by
  let D := fullBasisMatrix (referenceDirectionColumns Q g)
  have hD : IsUnit D.det := fullBasisMatrix_unit _ (referenceDirectionColumns_independent Q hQ g hcount)
  change inverseCongruence D (latest (Dᵀ*pairImages D ((S.inCoordinates D).inPhysical D).probe))=_
  rw [S.inCoordinates_inPhysical D hD]
  rfl

/-- The inverse congruence of the actual full RFC observed coefficient model is exactly the common pre-quadratic physical centre.
Use: Discharge the true native-model identification in the instance-optimality proof.
Article: main_krylov, s4:cor-Q, H=UᵀJ_DU.
Proof: First identify the actual physical step and measured-image arrays. Reverse their true newest-first order into chronological observations. Their genuine nonzero CG line scales cancel by the exact observed-centre invariance, leaving precisely the common original physical centre. -/
theorem Scenario.PreQuadratic.rfc_model_centre {S : Scenario (N+1)}
    {Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount Q hQ g=N+1)
    (h : S.PreQuadratic (cgOperator Q) g N) :
    let U := probedStepBasis (rfcMethod fullMemory 1) S.probeOracle (S.correctionOracle N) g N
    let Z := probedImageBasis (rfcMethod fullMemory 1) S.probeOracle (S.correctionOracle N) g N
    inverseCongruence (fullBasisMatrix U) (pairModel U Z)=S.preQuadraticCentre Q g := by
  -- Actual physical steps and actual observed images are fixed before changing any coordinates.
  dsimp only
  rw [h.imageBasis hQ _ (rfcMethod_consistent fullMemory (fun _ ha => ha) 1),h.rfc_stepBasis hQ]
  let U := referenceModelBasis Q g N
  let u := fun i : Fin (N+1) => U i.rev
  let D := fullBasisMatrix (referenceDirectionColumns Q g)
  let R := fullBasisMatrix u
  have hH : pairModel U (fun i => S.probeOracle (N-i.val) (U i))=
      (latest (Rᵀ*pairImages R S.probe)).submatrix Fin.rev Fin.rev := by
    simpa only [u,Fin.rev_rev,Fin.val_rev,Nat.add_sub_add_right,Scenario.probeOracle]
      using pairModel_reverse_observations u S.probe
  have hU : fullBasisMatrix U=R.submatrix id Fin.rev := by
    ext i j
    simp only [R,u,fullBasisMatrix,Matrix.of_apply,Matrix.submatrix_apply,id_eq,Fin.rev_rev]
  rw [show pairModel (referenceModelBasis Q g N)
    (fun i => S.probeOracle (N-i.val) (referenceModelBasis Q g N i))=_ from hH,hU]
  have hr := inverseCongruence_reindex R (latest (Rᵀ*pairImages R S.probe)) Fin.revPerm
  change inverseCongruence (R.submatrix id Fin.rev)
    ((latest (Rᵀ*pairImages R S.probe)).submatrix Fin.rev Fin.rev)=_ at hr
  rw [hr]
  -- Chronological CG directions differ from stored steps by genuine nonzero line scales.
  obtain ⟨s,hs,hscale⟩ := referenceModelBasis_direction_scales Q hQ g hcount
  have hR : R=D*diagonal (fun i => s i.rev) := by
    ext a i
    have hi : N-i.rev.val=i.val := by simp only [Fin.val_rev]; have := i.isLt; omega
    have hc : u i=s i.rev • referenceDirectionColumns Q g i := by
      dsimp only [u,U]
      rw [hscale,hi]
      rfl
    simpa only [R,D,fullBasisMatrix,Matrix.of_apply,Matrix.mul_diagonal,PiLp.smul_apply,smul_eq_mul,mul_comm]
      using congrArg (fun v : EuclideanSpace ℝ (Fin (N+1)) => v a) hc
  have hsdet : IsUnit (diagonal (fun i : Fin (N+1) => s i.rev)).det := by
    rw [det_diagonal,isUnit_iff_ne_zero]
    exact prod_ne_zero_iff.mpr (fun i _ => hs i.rev)
  change observedPhysicalCentre R S.probe=S.preQuadraticCentre Q g
  rw [hR,observedPhysicalCentre_rescale D S.probe _ hsdet,
    S.preQuadraticCentre_observed Q hQ g hcount]

end
end krylov.Information
