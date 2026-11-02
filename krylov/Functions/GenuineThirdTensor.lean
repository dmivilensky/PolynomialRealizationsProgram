import krylov.Functions.GenuineHessianSymmetry
import krylov.Functions.CubicSegment

/-!
Article: main_krylov, thm:Htransfer and thm:Hp, the genuine scalar third tensor.
Use: construct the actual symmetric cubic from the original objective and
its true successive derivatives. Both independent tensor swaps follow from
Schwarz, rather than being assumed as tensor-compatibility input fields.
Source: mathlib second_derivative_symmetric_of_eventually, applied to the
actual vector gradient and the original scalar objective.
-/

namespace krylov.Functions
noncomputable section
open Filter Set Metric Topology
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual third derivative is symmetric in its first two vector arguments.
Article: main_krylov, thm:Htransfer, genuine vector Schwarz identity. -/
theorem genuine_third_vectors_symmetric (T : E ≃L[ℝ] E)
    (G : E → E) (H : E → E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0) {r : ℝ} (hr : 0 < r)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z) (v w : E) :
    D v w = D w v := by
  have hmem : (0 : E) ∈ {z : E | ‖T z‖ < r} := by
    simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hr
  have hnb : ∀ᶠ z : E in 𝓝 0, ‖T z‖ < r :=
    (isOpen_lt T.continuous.norm continuous_const).mem_nhds hmem
  exact second_derivative_symmetric_of_eventually (hnb.mono (fun z hz => hG z hz.le)) hD v w

/-- The actual scalar third tensor obtained from the genuine vector Hessian derivative.
Article: main_krylov, thm:Htransfer and thm:Hp.
Proof: continuous linear composition constructs the real curried form. Vector
Schwarz proves the first adjacent swap, and actual Hessian-slice Schwarz proves the second. -/
def genuineThirdCubic (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0) {r : ℝ} (hr : 0 < r)
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z) : SymmetricCubic E where
  form := ((ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ)) (innerSL ℝ)).comp D
  swap₁ := by
    intro a b c
    change inner ℝ (D a b) c = inner ℝ (D b a) c
    rw [genuine_third_vectors_symmetric T G H D hD hr hG a b]
  swap₂ := by
    intro a b c
    change inner ℝ (D a b) c = inner ℝ (D a c) b
    exact (genuine_third_slice_symmetric T f G H D hD hr hF hG a b c).trans (real_inner_comm _ _)

/-- The constructed genuine symmetric cubic is precisely the original scalar third derivative contraction.
Article: main_krylov, thm:Htransfer, the tensor/native derivative dictionary. -/
theorem genuineThirdCubic_apply (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0) {r : ℝ} (hr : 0 < r)
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z) (a b c : E) :
    (genuineThirdCubic T f G H D hD hr hF hG).form a b c = inner ℝ c (D a b) :=
  real_inner_comm _ _

end
end krylov.Functions
