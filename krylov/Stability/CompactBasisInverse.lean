import krylov.Stability.FixedBasisOrder
import krylov.Stability.ContDiffSpectralMatrix
import Mathlib.Analysis.Normed.Group.Bounded
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(b), genuine compact full-reference reconstruction.
Use: turn all true scalar reference-step remainder coordinates into one
uniform vector estimate without inverting the perturbed moving basis.
Source: proved actual full-basis nonsingularity, true matrix inverse
continuity on its genuine domain and the standard compact image bound.
-/

namespace krylov.Stability
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Correction
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

/-- The actual inverse reference-basis reconstruction has one genuine bound
over every compact family of independent full physical reference bases.
Use: the full native end-cycle vector remainder follows from its proved
scalar pairings with a common constant chosen before the reference.
Article: main_krylov, apH:dcs2(b), true compact inverse-reference bound.
Proof: real full-basis independence derives every inverse domain. The
actual inverse transpose is continuous there and hence bounded on the
original compact family. Its exact action reconstructs each actual vector
from the finite Euclidean vector of its true reference pairings. -/
theorem compact_basis_inverse_bound
    (s : X → Fin n → EuclideanSpace ℝ (Fin n)) (K : Set X) (hK : IsCompact K)
    (hs : ∀ x∈K,∀ i,ContDiffAt ℝ 1 (fun y => s y i) x)
    (hLI : ∀ x∈K,LinearIndependent ℝ (s x)) :
    ∃ M : ℝ,0≤M ∧ ∀ x∈K,∀ v : EuclideanSpace ℝ (Fin n),
      ‖v‖≤M*‖projectedResidual (s x) v‖ := by
  let T := fun x => fullBasisMatrix (s x)
  let D := fun x => ((T x)ᵀ)⁻¹
  have hu (x : X) (hx : x∈K) : IsUnit (T x)ᵀ.det := by
    simpa only [det_transpose] using fullBasisMatrix_unit (s x) (hLI x hx)
  have hD : ContinuousOn D K := by
    intro x hx
    have hentry (i j : Fin n) : ContDiffAt ℝ 1 (fun y => (T y)ᵀ i j) x :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j).contDiff.contDiffAt.comp x (hs x hx i)
    have hT : ContinuousAt (fun y => (T y)ᵀ) x :=
      (contDiff_spectral_matrix (fun y => (T y)ᵀ) x hentry).continuousAt
    have hinv : ContinuousAt (fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹) ((T x)ᵀ) :=
      continuousAt_matrix_inv ((T x)ᵀ) (by
        rw [show (Ring.inverse : ℝ → ℝ)=Inv.inv from funext Ring.inverse_eq_inv]
        exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp (hu x hx)))
    have hi := hinv.comp (f := fun y : X => (T y)ᵀ) hT
    exact hi.continuousWithinAt
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hD
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro x hx v
  have he : Matrix.toEuclideanCLM (𝕜 := ℝ) (D x) (projectedResidual (s x) v)=v := by
    rw [projectedResidual_fullBasisMatrix]
    change Matrix.toEuclideanCLM (𝕜 := ℝ) ((T x)ᵀ)⁻¹ (Matrix.toEuclideanCLM (𝕜 := ℝ) (T x)ᵀ v)=v
    rw [← mul_apply_eq_comp,← map_mul,nonsing_inv_mul _ (hu x hx),map_one,one_apply_eq_self]
  calc
    ‖v‖=‖Matrix.toEuclideanCLM (𝕜 := ℝ) (D x) (projectedResidual (s x) v)‖ := congrArg norm he.symm
    _≤‖D x‖*‖projectedResidual (s x) v‖ := (Matrix.toEuclideanCLM (𝕜 := ℝ) (D x)).le_opNorm _
    _≤max M 0*‖projectedResidual (s x) v‖ :=
      mul_le_mul_of_nonneg_right ((hM x hx).trans (le_max_left _ _)) (norm_nonneg _)

end
end krylov.Stability
