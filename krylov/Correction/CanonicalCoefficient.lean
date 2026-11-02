import krylov.Correction.ReferenceModel

/-!
Article: main_krylov, thm:C, exact geometric identification of the native coefficient.
Use: identify the leading factor of the actual full physical expansion with
the source staircase acting on its genuine fresh defect and true last-step norm.
Source: all reference right-hand-side, model and Gram identities are proved
from actual RFC execution and actual CG flags in the preceding modules.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Reference krylov.Variation krylov.Envelope krylov.Methods krylov.Secant
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- The native full RFC second-order coefficient is exactly the source geometric coefficient in the genuine canonical metric.
Use: transfer the already proved actual cubic expansion and sharp geometric
bound to the same physical run, with all reference normalization identities discharged.
Article: main_krylov, thm:C, A^(−1/2)U₀^(−T)L₁H₀^(−1)r₁=‖ŝ_last‖𝓛f̂.
Proof: the actual full reference family is independent by genuine CG
nonstagnation. Its true Gram, model-error and incoming-vector identities
reduce the native coefficient to the proved exact metric-coordinate
cancellation; the staircase matrix is recovered from its actual operator. -/
theorem native_coefficient_canonical {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (F : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) :
    let U := referenceModelBasis base g k
    let H := pairModel U (probedImageBasis (rfcMethod fullMemory 1)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g k)
    let L := Matrix.of fun i j : Fin (k+1) => inner ℝ (U i)
      ((canonicalCorrectionOperator base E F k-canonicalFCPath base E 1 (k-(min i j).val)) (U j))
    let R := fullBasisMatrix U
    cgOperator (metricRoot base)⁻¹
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (Rᵀ⁻¹*(L*H⁻¹))
        (frozenIncoming (cgOperator base) g (canonicalFCPath base E 1) k))=
      ‖canonicalCGStep base g k‖ • staircaseOperator base g E F (k+1)
        (freshDefect base g E (k+1)) := by
  -- Every matrix and coefficient here belongs to the actual static reference window.
  let U := referenceModelBasis base g k
  let R := fullBasisMatrix U
  let S := (Matrix.toEuclideanCLM (n := Fin (k+1)) (𝕜 := ℝ)).toAlgEquiv.symm
    (staircaseOperator base g E F (k+1))
  have hS : cgOperator S=staircaseOperator base g E F (k+1) :=
    (Matrix.toEuclideanCLM (n := Fin (k+1)) (𝕜 := ℝ)).toAlgEquiv.apply_symm_apply _
  have hpre (i : ℕ) (hi : i≤k) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (by omega)
  have hU : LinearIndependent ℝ U := probedStepBasis_independent _
    (rfcMethod_consistent fullMemory (fun _ ha => ha) 1) _ (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 g k hpre
  have hL : (Matrix.of fun i j : Fin (k+1) => inner ℝ (U i)
      ((canonicalCorrectionOperator base E F k-canonicalFCPath base E 1 (k-(min i j).val)) (U j)))=
      Rᵀ*metricRoot base*S*metricRoot base*R := by
    rw [reference_model_staircase base hb g k hN E F,← hS,fullBasisMatrix_compression,
      fullBasisMatrix_map]
    simp only [R,U,transpose_mul,(metricRoot_isSymm base).eq,Matrix.mul_assoc]
  have hH : pairModel U (probedImageBasis (rfcMethod fullMemory 1)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g k)=Rᵀ*base*R := by
    rw [reference_model_gram base hb,fullBasisMatrix_compression]
  have hr : frozenIncoming (cgOperator base) g (canonicalFCPath base E 1) k=
      Matrix.toEuclideanCLM (𝕜 := ℝ) (Rᵀ*metricRoot base)
        (‖canonicalCGStep base g k‖ • freshDefect base g E (k+1)) := by
    rw [frozenIncoming_reference_fresh base hb g k hN,projectedResidual_fullBasisMatrix]
    simp only [R,U,map_mul,mul_apply_eq_comp,cgOperator]
  change cgOperator (metricRoot base)⁻¹
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (Rᵀ⁻¹*(_*_⁻¹)) _)=_
  rw [hL,hH,hr]
  have hc := full_reference_coefficient base R S hb (fullBasisMatrix_unit _ hU)
    (‖canonicalCGStep base g k‖ • freshDefect base g E (k+1))
  rw [← hS]
  simpa only [map_mul,mul_apply_eq_comp,cgOperator,map_smul] using hc

end
end krylov.Correction
