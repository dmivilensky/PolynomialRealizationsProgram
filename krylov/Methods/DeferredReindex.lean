import krylov.Methods.DeferredCoefficients
import krylov.Methods.WindowCoordinates
import krylov.Methods.HistoryWindowCharts

set_option autoImplicit false
/-!
Article: main_krylov, s3:def:DC and apB:lem:mu(d), genuine deferred observed-coordinate invariance.
Use: identify the actual chronological list deferred solve with its real
fixed finite observed coefficient chart without changing any physical query.
Source: existing actual conjugacy/model inverse reindexing and genuine
finite physical sum invariance under a true bijective index change.
-/

namespace krylov.Methods
noncomputable section
open Matrix
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The actual deferred coefficients reindex exactly under every genuine bijective change of the true observed columns.
Use: The actual deferred coefficients reindex exactly under every genuine bijective change of the true observed columns.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), genuine deferred observed-coordinate invariance.
Proof: Use the real conjugacy/model coefficient split and both existing genuine inverse-solve reindexing identities. -/
theorem deferredCoefficients_reindex (e : κ ≃ ι) (s y : ι → E) (g : E) (a : ℝ) (i : κ) :
    deferredCoefficients (s ∘ e) (y ∘ e) g a i=deferredCoefficients s y g a (e i) := by
  rw [deferredCoefficients_split,deferredCoefficients_split]
  change conjugacyCoefficients (s ∘ e) (y ∘ e) g i+
    a⁻¹*modelCoefficients (s ∘ e) (crossGram (y ∘ e) (s ∘ e)) g i=
    conjugacyCoefficients s y g (e i)+a⁻¹*modelCoefficients s (crossGram y s) g (e i)
  rw [conjugacyCoefficients_reindex]
  have hC : crossGram (y ∘ e) (s ∘ e)=(crossGram y s).submatrix e e := rfl
  rw [hC,modelCoefficients_reindex]

/-- The genuine physical deferred direction is unchanged by every actual bijective relabeling of its true observed step/image pairs.
Use: The genuine physical deferred direction is unchanged by every actual bijective relabeling of its true observed step/image pairs.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), genuine deferred observed-coordinate invariance.
Proof: The real coefficients and genuine physical column sum reindex together. -/
theorem deferredDirection_reindex (e : κ ≃ ι) (s y : ι → E) (g : E) (a : ℝ) :
    deferredDirection (s ∘ e) (y ∘ e) g a=deferredDirection s y g a := by
  unfold deferredDirection combine
  simp only [deferredCoefficients_reindex,Function.comp_apply]
  rw [Equiv.sum_comp e (fun i => deferredCoefficients s y g a i • s i)]

/-- The genuine chronological list deferred direction is exactly its actual fixed finite getter-array direction.
Use: The genuine chronological list deferred direction is exactly its actual fixed finite getter-array direction.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), genuine deferred observed-coordinate invariance.
Proof: Apply the proved true list-column coordinate casts and genuine deferred physical reindexing. -/
theorem deferredDirection_getD_array (W : List (E × E)) (p : ℕ) (hp : W.length=p) (g : E) (a : ℝ) :
    deferredDirection (windowSteps W) (windowImages W) g a=
      deferredDirection (fun i : Fin p => (W.getD i.val (0,0)).1)
        (fun i : Fin p => (W.getD i.val (0,0)).2) g a := by
  rw [windowSteps_getD_array W p hp,windowImages_getD_array W p hp,deferredDirection_reindex]
end
end krylov.Methods
