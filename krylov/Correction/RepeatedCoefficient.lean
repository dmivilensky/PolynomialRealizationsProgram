import krylov.Correction.CanonicalCoefficient
import krylov.Correction.RepeatedReconstruction

/-!
Article: main_krylov, thm:C2(b), canonical repeated-correction products.
Use: identify the actual native leading product with the source ordered
staircase product, retaining every independently varying last operator.
Source: exact full reference coordinate cancellation and the genuine CG flag
identities; no factor commutation or asymptotic product identity is assumed.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Reference krylov.Variation krylov.Envelope krylov.Methods krylov.Secant
  krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- The full native repeated leading coefficient is exactly the signed canonical ordered staircase product.
Use: all intermediate reference coordinate factors cancel in their true chronological order.
Article: main_krylov, thm:C2(b), (−1)^k_c‖ŝ_last‖𝓛_k_c⋯𝓛_1f̂.
Proof: the actual full CG reference is independent. Each native factor
intertwines with its true staircase factor by the proved Gram and compression
identities. The inverse coordinate change maps the true frozen incoming
vector to the last-step norm times the fresh defect. Finite induction and
the existing newest-left ordered-product theorem give the exact result.
-/
theorem native_repeated_coefficient_canonical {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (F : ℕ → Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (count : ℕ) :
    let U := referenceModelBasis base g k
    let H := pairModel U (probedImageBasis (rfcMethod fullMemory 1)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g k)
    let L := fun j => Matrix.of fun a b : Fin (k+1) => inner ℝ (U a)
      ((canonicalCorrectionOperator base E (F j) k-canonicalFCPath base E 1 (k-(min a b).val)) (U b))
    let R := fullBasisMatrix U
    cgOperator (metricRoot base)⁻¹ (cgOperator Rᵀ⁻¹
      (correctionRun (fun j (_ : Unit) => cgOperator (L j*H⁻¹))
        (fun _ => frozenIncoming (cgOperator base) g (canonicalFCPath base E 1) k) count ()))=
      ((-1 : ℝ)^count*‖canonicalCGStep base g k‖) •
        (chebyshev1.orderedProduct (fun j => staircaseOperator base g E (F j) (k+1)) count)
          (freshDefect base g E (k+1)) := by
  -- These are the actual static measured model and reference physical columns.
  let U := referenceModelBasis base g k
  let R := fullBasisMatrix U
  let H := pairModel U (probedImageBasis (rfcMethod fullMemory 1)
    (fun _ => cgOperator base) (fun _ => cgOperator base) g k)
  let L := fun j => Matrix.of fun a b : Fin (k+1) => inner ℝ (U a)
    ((canonicalCorrectionOperator base E (F j) k-canonicalFCPath base E 1 (k-(min a b).val)) (U b))
  let S := fun j => (Matrix.toEuclideanCLM (n := Fin (k+1)) (𝕜 := ℝ)).toAlgEquiv.symm
    (staircaseOperator base g E (F j) (k+1))
  let W := cgOperator ((metricRoot base)⁻¹*Rᵀ⁻¹)
  let r := frozenIncoming (cgOperator base) g (canonicalFCPath base E 1) k
  have hS (j : ℕ) : cgOperator (S j)=staircaseOperator base g E (F j) (k+1) :=
    (Matrix.toEuclideanCLM (n := Fin (k+1)) (𝕜 := ℝ)).toAlgEquiv.apply_symm_apply _
  have hpre (i : ℕ) (hi : i≤k) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (by omega)
  have hU : LinearIndependent ℝ U := probedStepBasis_independent _
    (rfcMethod_consistent fullMemory (fun _ ha => ha) 1) _ (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 g k hpre
  have hu : IsUnit R.det := fullBasisMatrix_unit _ hU
  have hH : H=Rᵀ*base*R := by
    dsimp only [H,U]
    rw [reference_model_gram base hb,fullBasisMatrix_compression]
  have hL (j : ℕ) : L j=Rᵀ*metricRoot base*S j*metricRoot base*R := by
    dsimp only [L,U]
    rw [reference_model_staircase base hb g k hN E (F j),← hS j,fullBasisMatrix_compression,
      fullBasisMatrix_map]
    simp only [R,U,transpose_mul,(metricRoot_isSymm base).eq,Matrix.mul_assoc]
  have hi (j : ℕ) (v : EuclideanSpace ℝ (Fin (k+1))) :
      W (cgOperator (L j*H⁻¹) v)=staircaseOperator base g E (F j) (k+1) (W v) := by
    rw [hL,hH,← hS]
    exact full_reference_factor base R (S j) hb hu v
  -- The true initial vector transforms without an error at the frozen reference.
  have hr : W r=‖canonicalCGStep base g k‖ • freshDefect base g E (k+1) := by
    have ht : IsUnit Rᵀ.det := by simpa only [det_transpose] using hu
    have he : ((metricRoot base)⁻¹*Rᵀ⁻¹)*(Rᵀ*metricRoot base)=1 := by
      calc
        _ = (metricRoot base)⁻¹*(Rᵀ⁻¹*Rᵀ)*metricRoot base := by noncomm_ring
        _ = 1 := by rw [nonsing_inv_mul _ ht,Matrix.mul_one,nonsing_inv_mul _ (metricRoot_det_unit base hb)]
    have hr' : r=cgOperator (Rᵀ*metricRoot base)
        (‖canonicalCGStep base g k‖ • freshDefect base g E (k+1)) := by
      dsimp only [r]
      rw [frozenIncoming_reference_fresh base hb g k hN,projectedResidual_fullBasisMatrix]
      simp only [R,U,cgOperator,map_mul,mul_apply_eq_comp]
    rw [hr']
    simp only [W,cgOperator,← mul_apply_eq_comp,← map_mul,he,map_one,one_apply_eq_self]
  have hc := correctionRun_map (fun j (_ : Unit) => cgOperator (L j*H⁻¹))
    (fun j (_ : Unit) => staircaseOperator base g E (F j) (k+1)) (fun _ => r) W count ()
      (fun j _ v => hi j v)
  rw [hr] at hc
  rw [correctionRun_orderedProduct (fun j (_ : Unit) => staircaseOperator base g E (F j) (k+1))
    (fun _ => ‖canonicalCGStep base g k‖ • freshDefect base g E (k+1)) count (),map_smul,smul_smul] at hc
  have hW (v : EuclideanSpace ℝ (Fin (k+1))) :
      W v=cgOperator (metricRoot base)⁻¹ (cgOperator Rᵀ⁻¹ v) := by
    simp only [W,cgOperator,map_mul,mul_apply_eq_comp]
  rw [hW] at hc
  exact hc

end
end krylov.Correction
