import krylov.Correction.PairingOrders
import krylov.Secant.CorrectionOrder
import krylov.LinearAlgebra.MatrixAsymptotics

/-!
Article: main_krylov, thm:C and apD:lem-model, second-order actual coefficient solves.
Use: allow the genuine positive reference model H₀ rather than assuming the
actual computed model has identity reference coordinates.
Source: reuse the existing spectral matrix correction expansion after an
exact nonsingular reference-model normalization.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.LinearAlgebra krylov.Secant
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {p : ℕ}

/-- The actual matrix correction product has its cubic remainder around an arbitrary genuine nonsingular reference model.
Use: apply the proved identity-reference correction calculus to the actual
observed model coordinates without replacing their reference Gram by an assumption.
Article: main_krylov, thm:C and apD:lem-model, −NH⁻¹r=−N₁H₀⁻¹r₁+O(ω³).
Proof: normalize the actual model on the right by H₀⁻¹. The proved
identity-reference matrix theorem applies; exact inverse multiplication
cancels the inserted reference factors in the true computed operator. -/
theorem reference_matrix_correction_order
    (H N L : X → Matrix (Fin p) (Fin p) ℝ)
    (g r : X → EuclideanSpace ℝ (Fin p))
    (hH : AnalyticAt ℝ H 0) (hu : IsUnit (H 0).det)
    (hN : (fun z => N z-L z) =O[𝓝 (0 : X)] (fun z => ‖z‖^2))
    (hL : L =O[𝓝 (0 : X)] (fun z => ‖z‖))
    (hg : (fun z => g z-r z) =O[𝓝 (0 : X)] (fun z => ‖z‖^2))
    (hr : r =O[𝓝 (0 : X)] (fun z => ‖z‖)) :
    (fun z => -(Matrix.toEuclideanCLM (𝕜 := ℝ) (N z*(H z)⁻¹) (g z))+
      Matrix.toEuclideanCLM (𝕜 := ℝ) (L z*(H 0)⁻¹) (r z)) =O[𝓝 (0 : X)] (fun z => ‖z‖^3) := by
  -- Normalize only by the proved nonsingular actual reference model.
  let J := fun z => H z*(H 0)⁻¹
  let E := fun z => N z*(H 0)⁻¹
  let M := fun z => L z*(H 0)⁻¹
  have hJ : (fun z => J z-1) =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
    have he := matrix_mul_const_bigO (fun z => H z-H 0) (H 0)⁻¹ _ (analytic_reference_order H hH)
    apply he.congr_left
    intro z
    rw [Matrix.sub_mul,mul_nonsing_inv _ hu]
  have hE : (fun z => E z-M z) =O[𝓝 (0 : X)] (fun z => ‖z‖^2) := by
    simpa only [Matrix.sub_mul] using matrix_mul_const_bigO (fun z => N z-L z) (H 0)⁻¹ _ hN
  have hM : M =O[𝓝 (0 : X)] (fun z => ‖z‖) := matrix_mul_const_bigO L (H 0)⁻¹ _ hL
  have he := matrix_correction_vector_order J E M g r (fun z => ‖z‖) 1
    (by simpa only [norm_zero] using continuous_norm.tendsto (0 : X)) hJ hE hM hg
      (by simpa only [pow_one] using hr)
  have hc (z : X) : E z*(J z)⁻¹=N z*(H z)⁻¹ := by
    simp only [E,J,Matrix.mul_inv_rev,nonsing_inv_nonsing_inv _ hu]
    calc
      N z*(H 0)⁻¹*(H 0*(H z)⁻¹)=N z*((H 0)⁻¹*H 0)*(H z)⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [nonsing_inv_mul _ hu,Matrix.mul_one]
  simpa only [hc,M,Nat.reduceAdd] using he

end
end krylov.Correction
