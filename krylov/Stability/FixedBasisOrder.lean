import krylov.Correction.FullReconstruction
import krylov.Correction.PairingOrders
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(b), true full-basis remainder transfer.
Use: reconstruct vector remainder orders from actual reference-step pairings
and freeze genuine C-one moving steps against a vanishing terminal gradient.
Source: reused finite Euclidean coordinate bounds, the proved actual full
basis inverse and Cauchy--Schwarz product-order calculus.
-/

namespace krylov.Stability
noncomputable section
open Matrix Filter Asymptotics krylov.Methods krylov.Reference krylov.LinearAlgebra krylov.Correction
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ} {α : Type*} {f : Filter α}

/-- Every true full independent Euclidean reference basis transfers the orders
of all its genuine scalar pairings to the actual vector order.
Use: end-cycle cancellation is reconstructed in the original full CG basis.
Article: main_krylov, apH:dcs2(b), reference-basis remainder reconstruction.
Proof: the actual column matrix is nonsingular. Its genuine bounded inverse
transpose reconstructs the real vector from its finite Euclidean pairings. -/
theorem fixed_basis_vector_order (s : Fin n → EuclideanSpace ℝ (Fin n))
    (hs : LinearIndependent ℝ s) (v : α → EuclideanSpace ℝ (Fin n)) (w : α → ℝ)
    (hpair : ∀ i,(fun z => inner ℝ (s i) (v z)) =O[f] w) : v =O[f] w := by
  let T := fullBasisMatrix s
  have hu : IsUnit Tᵀ.det := by simpa only [det_transpose] using fullBasisMatrix_unit s hs
  have hp : (fun z => projectedResidual s (v z)) =O[f] w :=
    (euclidean_bigO_iff_entry _ _).mpr hpair
  have hb := operator_action_order (fun _ : α => Matrix.toEuclideanCLM (𝕜 := ℝ) Tᵀ⁻¹)
    (fun z => projectedResidual s (v z)) (fun _ => (1 : ℝ)) w
    (tendsto_const_nhds.isBigO_one ℝ) hp
  have hb' : (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) Tᵀ⁻¹ (projectedResidual s (v z))) =O[f] w := by
    simpa only [one_mul] using hb
  apply hb'.congr_left
  intro z
  rw [projectedResidual_fullBasisMatrix,← mul_apply_eq_comp,← map_mul,nonsing_inv_mul _ hu,map_one,one_apply_eq_self]

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A genuine differentiable map changes by first order in the source norm.
Use: C-one primitive method charts suffice for the moving-step replacement.
Article: main_krylov, apH:dcs2(b), actual first-order trajectory changes.
Proof: use mathlib's differentiable increment big-O theorem in the true norm. -/
theorem differentiable_reference_order {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : X → V) (hv : DifferentiableAt ℝ v 0) :
    (fun z => v z-v 0) =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
  simpa only [sub_zero] using hv.isBigO_sub.norm_right

/-- Freezing a genuine differentiable moving step against a genuine
vanishing differentiable terminal gradient costs quadratic order.
Use: remove actual moving-basis changes without requiring C-two coefficients.
Article: main_krylov, apH:dcs2(b), true full-cycle basis freezing.
Proof: the actual step difference and the actual zero-reference gradient
are each first order; the reused real inner-product order calculus multiplies them. -/
theorem frozen_terminal_pairing_order (s g : X → E)
    (hs : DifferentiableAt ℝ s 0) (hg : DifferentiableAt ℝ g 0) (hg0 : g 0=0) :
    (fun z => inner ℝ (s z) (g z)-inner ℝ (s 0) (g z)) =O[𝓝 (0 : X)] (fun z => ‖z‖^2) := by
  have hgo : g =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
    simpa only [hg0,sub_zero] using differentiable_reference_order g hg
  have hh := inner_order (fun z => s z-s 0) g (fun z => ‖z‖) (fun z => ‖z‖)
    (differentiable_reference_order s hs) hgo
  simpa only [inner_sub_left,← pow_two] using hh

end
end krylov.Stability
