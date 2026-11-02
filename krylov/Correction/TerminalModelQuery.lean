import krylov.Correction.CleanModelStaircase
import krylov.Correction.ChronologicalModel
import krylov.Correction.UniformTerminalOperator

/-!
Article: main_krylov, thm:UCq, genuine measured terminal model response.
Use: Derive the terminal cubic remainder from the actual measured latest
model, its real inverse solve and the true chronological operator increments.
Source: the existing projected correction recurrence, exact full-basis
reconstruction, clean-model flag identity and Neumann inverse estimates.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Inverse-transpose reconstruction cancels the actual full-family projected residual.
Use: Recover the true physical returned gradient from its real measured coordinates.
Article: main_krylov, thm:UCq.
Proof: The existing full-column projection identity gives the actual transpose action; its derived nonsingular inverse cancels exactly.
-/
theorem full_projection_inverse_transpose (t : Fin n → EuclideanSpace ℝ (Fin n))
    (hT : IsUnit (fullBasisMatrix t).det) (v : EuclideanSpace ℝ (Fin n)) :
    cgOperator (fullBasisMatrix t)ᵀ⁻¹ (projectedResidual t v)=v := by
  rw [projectedResidual_fullBasisMatrix]
  simp only [cgOperator]
  rw [← mul_apply_eq_comp,← map_mul,
    Matrix.nonsing_inv_mul _ (by simpa only [Matrix.det_transpose] using hT),map_one,one_apply_eq_self]

/-- The actual full model correction returns exactly the reconstructed model-error action on its genuine solved right-hand side.
Use: Relate the uniform terminal remainder to the real correction query and returned gradient.
Article: main_krylov, thm:UCq.
Proof: Reuse the exact projected correction recurrence, then reconstruct with the true inverse transpose. Both actual inverse domains are explicit.
-/
theorem full_model_query_error (t : Fin n → EuclideanSpace ℝ (Fin n))
    (H B : Matrix (Fin n) (Fin n) ℝ) (hT : IsUnit (fullBasisMatrix t).det)
    (hH : IsUnit H.det) (v : EuclideanSpace ℝ (Fin n)) :
    v+cgOperator B (combine t (modelCoefficients t H v))=
      -cgOperator (fullBasisMatrix t)ᵀ⁻¹
        (cgOperator (correctionCompression t (cgOperator B)-H)
          (cgOperator H⁻¹ (cgOperator (fullBasisMatrix t)ᵀ v))) := by
  have hp := modelCorrection_projected t H hH (cgOperator B) v
  have hp' : projectedResidual t (v+cgOperator B (combine t (modelCoefficients t H v)))=
      -cgOperator (correctionCompression t (cgOperator B)-H)
        (cgOperator H⁻¹ (projectedResidual t v)) := by
    apply WithLp.ofLp_injective 2
    change coordinates t (v+cgOperator B (combine t (modelCoefficients t H v)))=
      -((correctionCompression t (cgOperator B)-H)*ᵥ(H⁻¹*ᵥcoordinates t v))
    simpa only [Matrix.neg_mulVec,Matrix.mulVec_mulVec] using hp
  have he := congrArg (cgOperator (fullBasisMatrix t)ᵀ⁻¹) hp'
  rw [full_projection_inverse_transpose t hT,map_neg,projectedResidual_fullBasisMatrix] at he
  exact he

/-- The genuine measured terminal model-error factor differs from its actual oblique-staircase compression by at most dimension times the true secant contamination.
Use: Derive the second-order model-factor allowance from observed data.
Article: main_krylov, thm:UCq.
Proof: The exact clean-model factorization cancels both common terminal compressions. Bound the remaining two genuine latest models using their own unit-column image discrepancies.
-/
theorem terminal_measured_model_error_bound
    (t y : Fin n → EuclideanSpace ℝ (Fin n)) (ht : ∀ i, ‖t i‖=1)
    (hT : IsUnit (fullBasisMatrix t).det)
    (A E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ j, (A j).IsSymm) (hInc : ∀ j<n, A (j+1)-A j=E j)
    {η : ℝ} (hη : 0≤η) (hy : ∀ i, ‖y i-cgOperator (A i.val) (t i)‖≤η) :
    ‖correctionCompression t (cgOperator (A n+F))-latest (crossGram t y)-
      (fullBasisMatrix t)ᵀ*obliqueStaircase (fullBasisMatrix t) E F n*fullBasisMatrix t‖≤(n : ℝ)*η := by
  rw [← clean_observed_model_factorization t hT A E F hA hInc]
  have he : correctionCompression t (cgOperator (A n+F))-latest (crossGram t y)-
      (correctionCompression t (cgOperator (A n+F))-
        latest (crossGram t (fun i => cgOperator (A i.val) (t i))))=
        latest (crossGram t (fun i => cgOperator (A i.val) (t i)))-latest (crossGram t y) := by abel
  rw [he,norm_sub_rev]
  exact latest_crossGram_difference_bound t y _ ht hη hy

/-- The actual measured full-model query has an explicit uniform cubic remainder around its true moving oblique-staircase response.
Use: Assemble the ordinary RFC terminal expansion without a minimum CG step size or an assumed model-error expansion.
Article: main_krylov, thm:UCq.
Proof: Derive the true full-basis and observed-model inverse domains from their measured near-identity bounds. The actual clean-model flag identity and secant errors supply the second-order model-factor error. Apply the exact reconstructed operator split to this genuine query, retaining the stated fresh-vector error.
-/
theorem terminal_measured_query_cubic
    (t y : Fin n → EuclideanSpace ℝ (Fin n)) (ht : ∀ i, ‖t i‖=1)
    (A E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ j, (A j).IsSymm) (hInc : ∀ j<n, A (j+1)-A j=E j)
    (v f : EuclideanSpace ℝ (Fin n))
    {a b c d e r ε : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) (he : 0≤e)
    (hε : 0≤ε) (hε1 : ε≤1) (haε : a*ε≤1/2) (hbε : b*ε≤1/2)
    (hGram : ‖(fullBasisMatrix t)ᵀ*fullBasisMatrix t-1‖≤a*ε)
    (hModel : ‖latest (crossGram t y)-1‖≤b*ε)
    (hy : ∀ i, ‖y i-cgOperator (A i.val) (t i)‖≤c*ε^2)
    (hL : ‖obliqueStaircase (fullBasisMatrix t) E F n‖≤d*ε)
    (hvf : ‖v-f‖≤e*ε^2) (hf : ‖f‖≤r*ε) :
    ‖v+cgOperator (A n+F) (combine t (modelCoefficients t (latest (crossGram t y)) v))+
      cgOperator (obliqueStaircase (fullBasisMatrix t) E F n) f‖≤
      ((8*(n : ℝ)*c+d*(8*b+4*a))*(r+e)+d*e)*ε^3 := by
  let T := fullBasisMatrix t
  let H := latest (crossGram t y)
  let N := correctionCompression t (cgOperator (A n+F))-H
  let L := obliqueStaircase T E F n
  have hGhalf := hGram.trans haε
  obtain ⟨hu,hT,hTi,_herr⟩ := full_column_inverse_transpose_bounds T hGhalf
  obtain ⟨hHu,hH,hHerr⟩ := near_identity_inverse H (hModel.trans hbε)
  have hHerr' : ‖H⁻¹-1‖≤(2*b)*ε :=
    hHerr.trans ((mul_le_mul_of_nonneg_left hModel (by norm_num : (0 : ℝ)≤2)).trans_eq (by ring))
  have hprimal : ‖T*Tᵀ-1‖≤(4*a)*ε :=
    (full_column_primal_gram_error T hGhalf).trans
      ((mul_le_mul_of_nonneg_left hGram (by norm_num : (0 : ℝ)≤4)).trans_eq (by ring))
  have hN : ‖N-Tᵀ*L*T‖≤((n : ℝ)*c)*ε^2 :=
    (terminal_measured_model_error_bound t y ht hu A E F hA hInc
      (mul_nonneg hc (sq_nonneg ε)) hy).trans_eq (by ring)
  have hPY (w : EuclideanSpace ℝ (Fin n)) : cgOperator Tᵀ⁻¹ (cgOperator Tᵀ w)=w := by
    simpa only [T,cgOperator,projectedResidual_fullBasisMatrix] using full_projection_inverse_transpose t hu w
  have hNc : ‖cgOperator N-(cgOperator Tᵀ).comp ((cgOperator L).comp (cgOperator T))‖≤
      ((n : ℝ)*c)*ε^2 := by
    have he : cgOperator N-(cgOperator Tᵀ).comp ((cgOperator L).comp (cgOperator T))=
        cgOperator (N-Tᵀ*L*T) := by
      simp only [cgOperator,map_sub,map_mul,Matrix.mul_assoc]
      rfl
    rw [he,cgOperator,Matrix.l2_opNorm_toEuclideanCLM]
    exact hN
  have hHc : ‖cgOperator H⁻¹-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤(2*b)*ε := by
    change ‖cgOperator H⁻¹-1‖≤(2*b)*ε
    simpa only [cgOperator,map_sub,map_one,Matrix.l2_opNorm_toEuclideanCLM] using
      (show ‖cgOperator (H⁻¹-1)‖≤(2*b)*ε by
        simpa only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] using hHerr')
  have hXY : ‖(cgOperator T).comp (cgOperator Tᵀ)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤(4*a)*ε := by
    have he : (cgOperator T).comp (cgOperator Tᵀ)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))=
        cgOperator (T*Tᵀ-1) := by
      simp only [cgOperator,map_sub,map_mul,map_one]
      rfl
    rw [he,cgOperator,Matrix.l2_opNorm_toEuclideanCLM]
    exact hprimal
  rw [full_model_query_error t H (A n+F) hu hHu v]
  have hbound := terminal_model_uniform_cubic (cgOperator T) (cgOperator Tᵀ)
    (cgOperator Tᵀ⁻¹) (cgOperator N) (cgOperator H⁻¹) (cgOperator L) v f
    (by positivity : 0≤4*a) (by positivity : 0≤2*b) (by positivity : 0≤(n : ℝ)*c)
    hd he hε hε1 hPY
    (by simpa only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] using hT)
    (by simpa only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM,transpose_norm] using hT)
    (by simpa only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] using hTi)
    (by simpa only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] using hH)
    hNc hHc hXY (by simpa only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] using hL) hvf hf
  exact hbound.trans_eq (by ring)

end
end krylov.Correction
