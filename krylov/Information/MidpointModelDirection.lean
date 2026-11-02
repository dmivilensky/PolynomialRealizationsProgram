import krylov.Correction.FirstIncrementGeometry
import krylov.LinearAlgebra.RankOneNorm

/-!
Article: main_krylov, thm:C2(c), native informed diagonal model direction.
Use: pull the original first-CG-coordinate form into the real native model
and identify its exact action on the genuine one-increment fresh defect.
Source: actual full reference basis rank, inverse-congruence cancellation
and the proved original first-increment staircase geometry.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Secant krylov.Envelope
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The original first unit-CG-coordinate form expressed in the actual unnormalized reference coefficient model.
Use: the informed scalar replacement uses only the known base and known initial gradient, with all true column energies retained.
Article: main_krylov, thm:C2(c), native energy-scaled oldest-diagonal model change. -/
def midpointModelDirection (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (N+1))) : Matrix (Fin (N+1)) (Fin (N+1)) ℝ :=
  let V := metricRoot base*fullBasisMatrix (referenceModelBasis base g N)
  let e := canonicalCGUnitStep base g 0
  Vᵀ*vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)*V

/-- Canonical transport of the actual native informed model change is exactly the first-CG rank-one form times its chosen scalar.
Use: eliminate all actual reference column scales in the genuine modified-solve leading coefficient.
Article: main_krylov, thm:C2(c), exact canonical informed replacement.
Proof: actual full quadratic CG gives independent native reference columns.
Their metric-root matrix is nonsingular, so both real congruence inverses
cancel exactly around the original first-coordinate form. -/
theorem midpointModelDirection_canonical (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin (N+1)))
    (hcount : referenceAtomCount base hb g=N+1) (q : ℝ) :
    let V := metricRoot base*fullBasisMatrix (referenceModelBasis base g N)
    let e := canonicalCGUnitStep base g 0
    inverseCongruence V (q • midpointModelDirection base g)=q • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e) := by
  -- Derive the genuine native reference inverse before cancelling the original congruence.
  let V := metricRoot base*fullBasisMatrix (referenceModelBasis base g N)
  have hpre (i : ℕ) (hi : i≤N) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (by omega)
  have hU : LinearIndependent ℝ (referenceModelBasis base g N) := probedStepBasis_independent _
    (rfcMethod_consistent fullMemory (fun _ ha => ha) 1) _ (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 g N hpre
  have hV : IsUnit V.det := by
    change IsUnit (metricRoot base*fullBasisMatrix (referenceModelBasis base g N)).det
    rw [det_mul]
    exact (metricRoot_det_unit base hb).mul (fullBasisMatrix_unit _ hU)
  have ht : IsUnit Vᵀ.det := by simpa only [det_transpose] using hV
  change inverseCongruence V (q • (Vᵀ*_ *V))=_
  simp only [inverseCongruence,Matrix.mul_smul,Matrix.smul_mul,← Matrix.mul_assoc,
    nonsing_inv_mul _ ht,Matrix.one_mul]
  rw [Matrix.mul_assoc,mul_nonsing_inv _ hV,Matrix.mul_one]

/-- The actual one-increment modified-model leading vector has precisely the original hidden-entry error times the true terminal cross entry.
Use: the observed completion midpoint directly bounds the genuine executed informed coefficient.
Article: main_krylov, thm:C2(c), (q−q̂)(ŝ₀ᵀE₀ŝ_last)ŝ₀.
Proof: the genuine source staircase and fresh vector have their proved
first-coordinate forms. Exact native-change transport subtracts the chosen
scalar on that same true unit coordinate, giving the printed product. -/
theorem midpointModelDirection_leading (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin (N+1)))
    (hcount : referenceAtomCount base hb g=N+1) (hN : 0<N)
    (M : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (q : ℝ) :
    let V := metricRoot base*fullBasisMatrix (referenceModelBasis base g N)
    let e := canonicalCGUnitStep base g 0
    let f := canonicalCGUnitStep base g N
    (staircaseOperator base g (firstIncrement M) 0 (N+1)-cgOperator (inverseCongruence V (q • midpointModelDirection base g)))
      (freshDefect base g (firstIncrement M) (N+1))=
      ((inner ℝ e (cgOperator M e)-q)*inner ℝ e (cgOperator M f)) • e := by
  -- Evaluate the actual native replacement on the exact genuine first-increment fresh vector.
  have ho := canonicalCG_frame_of_full_atoms base hb g hcount
  have he : ‖canonicalCGUnitStep base g 0‖=1 := by simpa only [Fin.val_zero] using ho.norm_eq_one (0 : Fin (N+1))
  dsimp only
  rw [_root_.sub_apply,firstIncrement_staircase_fresh base g hN he M,
    midpointModelDirection_canonical base hb g hcount q,firstIncrement_fresh base g hN he M]
  have hee : inner ℝ (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g 0)=1 := by
    rw [real_inner_self_eq_norm_sq,he,one_pow]
  simp only [cgOperator,map_smul,_root_.smul_apply,toEuclideanCLM_rankOne,
    WithLp.toLp_ofLp,InnerProductSpace.rankOne_apply,hee,mul_one,smul_smul,← sub_smul]
  congr 1
  ring

end
end krylov.Information
