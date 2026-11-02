import krylov.Methods.DirectBroydenComparison
import krylov.LinearAlgebra.MatrixAsymptotics
import krylov.Secant.Model
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), complete native latest model comparison.
Use: the full genuine compressed direct Broyden model differs from the
actual latest-information observed model by second order in spectral norm.
Source: proved native chronological induction, genuine model symmetry and
the existing spectral finite-entry asymptotic equivalence.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability krylov.LinearAlgebra krylov.Secant
open Matrix Filter Topology Asymptotics
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual full compressed direct Broyden model equals the genuine
latest-information model of its own observed pairs up to second order,
in the original spectral matrix norm, for every finite native prefix.
Use: closes the source model identity without assuming any model rate,
smooth interpolation schedule or first-order convergence of the steps.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: the genuine chronological induction gives every actual upper
entry; actual native symmetry supplies every lower entry. The proved
finite-coordinate equivalence transfers these bounds to spectral norm. -/
theorem directBroyden_latest_second_order {l : Filter α} {t : α → ℝ} {p : ℕ}
    (D : DirectBroydenPerturbation (E := E) l t p) (k : ℕ) (hk : k≤ p) :
    (fun z => (show Matrix (Fin k) (Fin k) ℝ from fun i j => inner ℝ (D.step z i.val)
      (directBroydenPerturbedModel D z k (D.step z j.val)))-
      latest (fun i j : Fin k => inner ℝ (D.step z i.val) (D.image z j.val)))
        =O[l] (fun z => t z^2) := by
  apply (matrix_bigO_iff_entry _ _).mpr
  intro i j
  have hc := (directBroyden_native_comparison D k hk).2
  change (fun z => inner ℝ (D.step z i.val) (directBroydenPerturbedModel D z k (D.step z j.val))-
    inner ℝ (D.step z (min i j).val) (D.image z (max i j).val)) =O[l] (fun z => t z^2)
  by_cases hij : i≤ j
  · rw [min_eq_left hij,max_eq_right hij]
    exact hc i.val i.isLt j.val j.isLt hij
  · have hji : j≤ i := le_of_not_ge hij
    have h := hc j.val j.isLt i.val i.isLt hji
    apply h.congr' ?_ EventuallyEq.rfl
    filter_upwards [directBroydenPerturbation_symmetric D k hk] with z hz
    rw [min_eq_right hji,max_eq_left hji]
    have he : inner ℝ (D.step z i.val) (directBroydenPerturbedModel D z k (D.step z j.val))=
        inner ℝ (D.step z j.val) (directBroydenPerturbedModel D z k (D.step z i.val)) :=
      (hz (D.step z i.val) (D.step z j.val)).symm.trans (real_inner_comm _ _)
    rw [he]

end
end krylov.Methods
