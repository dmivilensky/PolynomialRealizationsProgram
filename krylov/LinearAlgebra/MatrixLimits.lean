import krylov.LinearAlgebra.MatrixAsymptotics
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), true spectral matrix limits.
Use: derive native observed and physical basis limits from their genuine
convergent finite coordinates without changing the matrix norm.
Source: the existing continuous spectral finite-coordinate equivalence.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
variable {α : Type*} {n p : ℕ}

/-- Genuine finite entry limits imply convergence in the original spectral
matrix norm, for arbitrary rectangular physical matrices.
Use: derive native model, inverse and basis domains from actual pair limits.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: assemble the actual coordinate limits and compose the proved
continuous inverse finite-coordinate equivalence into spectral matrices. -/
theorem matrix_tendsto_of_entries (M : α → Matrix (Fin n) (Fin p) ℝ)
    (M0 : Matrix (Fin n) (Fin p) ℝ) (l : Filter α)
    (h : ∀ i j,Tendsto (fun z => M z i j) l (𝓝 (M0 i j))) : Tendsto M l (𝓝 M0) := by
  let e := matrixEntryEquiv n p
  have he : Tendsto (fun z => e (M z)) l (𝓝 (e M0)) :=
    tendsto_pi_nhds.mpr (fun ij => h ij.1 ij.2)
  simpa only [Function.comp_def,e.symm_apply_apply] using
    (e.symm.continuousAt.tendsto.comp he)

end
end krylov.LinearAlgebra
