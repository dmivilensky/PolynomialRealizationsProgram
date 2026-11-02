import krylov.Methods.DeferredDirection

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d) and thm:DC, genuine exact deferred residual transfer.
Use: express the true final old-step residual as the actual fresh operator
mismatch plus the genuine unresolved old-residual multiplier.
Source: actual nonsingular deferred observed conjugacy equations and
genuine symmetric old secant actions; the real line scalar is arbitrary.
-/

namespace krylov.Methods
noncomputable section
open Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual deferred direction gives the exact genuine old-step residual transfer with its real fresh operator defect and true inverse-estimate damping factor.
Use: The actual deferred direction gives the exact genuine old-step residual transfer with its real fresh operator defect and true inverse-estimate damping factor.
Article: main_krylov, apB:lem:mu(d) and thm:DC, genuine exact deferred residual transfer.
Proof: Use the genuine symmetric old secant identity to replace the actual old operator pairing by the real prescribed tilted conjugacy right-hand side; expand the true updated residual. -/
theorem deferred_residual_transfer (s y : ι → E) (g : E) (a α : ℝ)
    (D : E →L[ℝ] E) (C : ι → E →L[ℝ] E)
    (hC : ∀ i, (C i).toLinearMap.IsSymmetric) (hy : ∀ i, y i=C i (s i))
    (hdet : IsUnit (crossGram y s).det) (i : ι) :
    inner ℝ (s i) (g+α • D (deferredDirection s y g a))=
      (1-α/a)*inner ℝ (s i) g+
        inner ℝ (s i) ((D-C i) (α • deferredDirection s y g a)) := by
  have hp : inner ℝ (s i) (C i (deferredDirection s y g a))= -a⁻¹*inner ℝ (s i) g := by
    have hs := hC i (s i) (deferredDirection s y g a)
    change inner ℝ (C i (s i)) (deferredDirection s y g a)=inner ℝ (s i) (C i (deferredDirection s y g a)) at hs
    rw [← hs,← hy i]
    exact deferredDirection_conjugacy s y g a hdet i
  simp only [inner_add_right,real_inner_smul_right,_root_.sub_apply,map_smul,inner_sub_right,hp]
  ring
end
end krylov.Methods
