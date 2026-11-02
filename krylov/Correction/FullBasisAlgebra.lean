import krylov.Correction.FullReconstruction
import krylov.Secant.ModelError

/-!
Article: main_krylov, thm:C, exact full reference coordinate cancellation.
Use: remove the actual reference energy scales from a full physical model
coefficient before applying the already proved cubic remainder theorem.
Source: the existing exact matrix-column compression and genuine nonsingular
positive-root cancellation. These identities do not assume orthonormal raw columns.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {n : ℕ}

/-- The genuine full physical operator compression is the matrix congruence by its actual column matrix.
Use: identify reference Gram and model-error matrices without replacing real columns by normalized ones.
Article: main_krylov, thm:C, U₀ᵀTU₀.
Proof: use the existing exact entry pairing for each pair of real physical columns. -/
theorem fullBasisMatrix_compression (u : Fin n → EuclideanSpace ℝ (Fin n))
    (M : Matrix (Fin n) (Fin n) ℝ) :
    correctionCompression u (cgOperator M)=(fullBasisMatrix u)ᵀ*M*fullBasisMatrix u := by
  ext i j
  exact (compressed_entry_pairing (fullBasisMatrix u) M i j).symm

/-- Applying a physical matrix to every true full column multiplies its actual column matrix on the left.
Use: form the genuine positive-root reference matrix A¹ᐟ²U₀.
Article: main_krylov, thm:C, canonical full reference columns.
Proof: each genuine matrix-product column is its actual Euclidean operator action. -/
theorem fullBasisMatrix_map (u : Fin n → EuclideanSpace ℝ (Fin n))
    (M : Matrix (Fin n) (Fin n) ℝ) :
    fullBasisMatrix (fun i => cgOperator M (u i))=M*fullBasisMatrix u := by
  ext i j
  rfl

/-- The real canonical coefficient cancels all actual full reference coordinate and energy factors.
Use: transfer the genuine native physical expansion to its geometric canonical staircase action.
Article: main_krylov, thm:C, cancellation of Q and C in the leading term.
Proof: expand the inverse of the actual reference Gram using A=R_A².
The genuine step matrix and metric root are nonsingular; reassociate the
three adjacent inverse pairs and cancel them, preserving the staircase factor. -/
theorem full_reference_coefficient (base R S : Matrix (Fin n) (Fin n) ℝ)
    (hb : base.PosDef) (hR : IsUnit R.det) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ)
      ((metricRoot base)⁻¹*(Rᵀ⁻¹*((Rᵀ*metricRoot base*S*metricRoot base*R)*(Rᵀ*base*R)⁻¹)))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (Rᵀ*metricRoot base) x)=cgOperator S x := by
  -- Cancel the full reference coordinates only after deriving both genuine inverse domains.
  have ht : IsUnit Rᵀ.det := by simpa only [det_transpose] using hR
  have hr := metricRoot_det_unit base hb
  have hG : Rᵀ*base*R=Rᵀ*(metricRoot base*metricRoot base)*R := by
    rw [metricRoot_square base hb]
  have he : (metricRoot base)⁻¹*(Rᵀ⁻¹*((Rᵀ*metricRoot base*S*metricRoot base*R)*
      (Rᵀ*base*R)⁻¹))*(Rᵀ*metricRoot base)=S := by
    rw [hG]
    simp only [Matrix.mul_inv_rev]
    calc
      _ = ((metricRoot base)⁻¹*(Rᵀ⁻¹*Rᵀ)*metricRoot base)*S*
          (metricRoot base*(R*R⁻¹)*(metricRoot base)⁻¹)*
          ((metricRoot base)⁻¹*(Rᵀ⁻¹*Rᵀ)*metricRoot base) := by noncomm_ring
      _ = S := by
        rw [nonsing_inv_mul _ ht,mul_nonsing_inv _ hR]
        simp only [Matrix.mul_one,nonsing_inv_mul _ hr,mul_nonsing_inv _ hr,
          Matrix.one_mul]
  rw [← mul_apply_eq_comp,← map_mul,he]
  rfl

/-- The true reference inverse-transpose and inverse-root change intertwines one native factor with its canonical factor.
Use: cancel the full reference coordinates between successive ordered correction factors.
Article: main_krylov, thm:C2(b), native-to-canonical factor identity.
Proof: the inverse change maps every native vector to a canonical vector
and its forward map cancels exactly on the proved reference domains. Apply
the existing full reference coefficient identity to that canonical vector. -/
theorem full_reference_factor (base R S : Matrix (Fin n) (Fin n) ℝ)
    (hb : base.PosDef) (hR : IsUnit R.det) (v : EuclideanSpace ℝ (Fin n)) :
    cgOperator ((metricRoot base)⁻¹*Rᵀ⁻¹)
      (cgOperator ((Rᵀ*metricRoot base*S*metricRoot base*R)*(Rᵀ*base*R)⁻¹) v)=
        cgOperator S (cgOperator ((metricRoot base)⁻¹*Rᵀ⁻¹) v) := by
  -- Both actual coordinate factors are units before cancelling the forward map.
  have ht : IsUnit Rᵀ.det := by simpa only [det_transpose] using hR
  have hr := metricRoot_det_unit base hb
  have he : (Rᵀ*metricRoot base)*((metricRoot base)⁻¹*Rᵀ⁻¹)=1 := by
    calc
      _ = Rᵀ*(metricRoot base*(metricRoot base)⁻¹)*Rᵀ⁻¹ := by noncomm_ring
      _ = 1 := by rw [mul_nonsing_inv _ hr,Matrix.mul_one,mul_nonsing_inv _ ht]
  have hf : Matrix.toEuclideanCLM (𝕜 := ℝ) (Rᵀ*metricRoot base)
      (cgOperator ((metricRoot base)⁻¹*Rᵀ⁻¹) v)=v := by
    rw [cgOperator,← mul_apply_eq_comp,← map_mul,he,map_one,one_apply_eq_self]
  have hc := full_reference_coefficient base R S hb hR
    (cgOperator ((metricRoot base)⁻¹*Rᵀ⁻¹) v)
  rw [hf] at hc
  simpa only [cgOperator,map_mul,mul_apply_eq_comp] using hc

end
end krylov.Correction
