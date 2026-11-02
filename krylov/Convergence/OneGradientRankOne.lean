import krylov.Convergence.EvaluatedOrthogonalResponse
import krylov.Convergence.VirtualTensorBanach
import krylov.Functions.RankOneGeometry

/-!
Article: main_krylov, prop:EL, genuine rank-one tensor algebra.
Use: specialize the true canonical third-tensor slices on a single real
unit CG direction, keeping the actual old projections and launch vector.
Source: genuine Riesz tensor pairing and orthogonal projection symmetry.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Finset krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
  krylov.Correction krylov.Variation krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Exact actual Riesz action of the genuine rank-one third tensor.
Article: main_krylov, prop:EL. -/
theorem canonicalVariation_rankOneCubic_apply (a : E) (M : ℝ) (v w : E) :
    canonicalVariation (rankOneCubic a M) v w=(M*inner ℝ a v*inner ℝ a w) • a := by
  apply ext_inner_left ℝ
  intro b
  rw [canonicalVariation_pair,rankOneCubic_apply,inner_smul_right,real_inner_comm b a]
  ring

/-- Every true self-adjoint old projection preserving the rank-one axis
leaves its actual compressed cubic slice unchanged. Article: prop:EL. -/
theorem canonicalVariation_rankOneCubic_compression (a : E) (M : ℝ)
    (P : E →L[ℝ] E) (hP : P.toLinearMap.IsSymmetric) (hPa : P a=a) (v w : E) :
    P (canonicalVariation (rankOneCubic a M) v (P w))=(M*inner ℝ a v*inner ℝ a w) • a := by
  rw [canonicalVariation_rankOneCubic_apply,map_smul,hPa]
  have hi : inner ℝ a (P w)=inner ℝ a w := by
    have hh := (hP a w).symm
    change inner ℝ a (P w)=inner ℝ (P a) w at hh
    simpa only [hPa] using hh
  rw [hi]

end
end krylov.Convergence
