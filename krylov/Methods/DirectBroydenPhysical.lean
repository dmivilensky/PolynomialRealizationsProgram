import krylov.Methods.DirectBroydenCompression
import krylov.LinearAlgebra.InverseComparison
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), true physical congruence comparison.
Use: the native bounded-operator recursion yields the literal source
matrix identity on its own actual physical step and image columns.
Source: exact Euclidean matrix/operator dictionary, actual inner-product
compression, positive reference Gram forms and genuine spectral calculus.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability krylov.LinearAlgebra krylov.Secant
open Matrix Filter Topology Asymptotics
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {α : Type*} {n p : ℕ} {l : Filter α} {t : α → ℝ}

/-- The genuine finite physical step matrix of the primitive perturbation.
Use: all compressed and inverse models retain the actual source columns.
Article: main_krylov, prop:classical(c), apE:broyden. -/
def directBroydenPhysicalSteps
    (D : DirectBroydenPerturbation (E := EuclideanSpace ℝ (Fin n)) l t p) (z : α) : Matrix (Fin n) (Fin p) ℝ :=
  fun i j => D.step z j.val i

/-- The genuine observed pairing matrix of the actual physical pairs.
Use: latest-information comparisons use the same native observations.
Article: main_krylov, prop:classical(c), apE:broyden. -/
def directBroydenPhysicalObserved
    (D : DirectBroydenPerturbation (E := EuclideanSpace ℝ (Fin n)) l t p) (z : α) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j => inner ℝ (D.step z i.val) (D.image z j.val)

/-- The literal executed direct model in its true physical matrix coordinates.
Use: no alternative matrix model replaces the actual chronological update.
Article: main_krylov, prop:classical(c), apE:broyden. -/
def directBroydenPhysicalModel
    (D : DirectBroydenPerturbation (E := EuclideanSpace ℝ (Fin n)) l t p) (z : α) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm (directBroydenPerturbedModel D z p)

/-- Genuine Euclidean compression has exactly the original physical
transpose-congruence entries for arbitrary rectangular step matrices.
Use: identify the literal source congruence with the proved native entries.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: the true Euclidean inner product is the matrix dot-product action;
the standard dot-product associativity is exactly matrix multiplication. -/
theorem directBroyden_physical_compression_entry (S : Matrix (Fin n) (Fin p) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin p) :
    (Sᵀ*B*S) i j=inner ℝ (WithLp.toLp 2 (Sᵀ i))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) B (WithLp.toLp 2 (Sᵀ j))) := by
  rw [Matrix.inner_toEuclideanCLM,Matrix.dotProduct_mulVec]
  rfl

/-- The actual physical native direct Broyden model satisfies the full
source congruence identity with its own true latest-information model,
with genuine second-order error in the original spectral norm.
Use: closes the actual matrix part of the original comparison for all
finite pair counts, including rectangular partial histories.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: the exact physical Euclidean compression dictionary identifies
each genuine native entry; apply the proved full spectral model identity. -/
theorem directBroyden_physical_model_second_order
    (D : DirectBroydenPerturbation (E := EuclideanSpace ℝ (Fin n)) l t p) :
    (fun z => (directBroydenPhysicalSteps D z)ᵀ*directBroydenPhysicalModel D z*directBroydenPhysicalSteps D z-
      latest (directBroydenPhysicalObserved D z)) =O[l] (fun z => t z^2) := by
  have he (z : α) : (directBroydenPhysicalSteps D z)ᵀ*directBroydenPhysicalModel D z*directBroydenPhysicalSteps D z=
      (fun i j : Fin p => inner ℝ (D.step z i.val) (directBroydenPerturbedModel D z p (D.step z j.val))) := by
    ext i j
    rw [directBroyden_physical_compression_entry]
    have hm : Matrix.toEuclideanCLM (𝕜 := ℝ) (directBroydenPhysicalModel D z)=directBroydenPerturbedModel D z p :=
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).apply_symm_apply _
    rw [hm]
    rfl
  simp only [he]
  exact directBroyden_latest_second_order D p le_rfl

end
end krylov.Methods
