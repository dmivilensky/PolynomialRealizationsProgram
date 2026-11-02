import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Operator.Asymptotics
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Article: main_krylov, lem:projected-residual, genuine Euclidean coordinate orders.
Use: finite coordinate calculations preserve the actual Euclidean norm of
projected residuals, including empty finite families.
Source: mathlib's PiLp continuous coordinate equivalence and finite-product big-O characterization.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Filter Asymptotics
variable {α : Type*} {p : ℕ} {f : Filter α}

/-- Genuine finite Euclidean big-O is equivalent to big-O of every actual coordinate.
Use: transfer normalized residual orders to the next real recorded window without changing its norm.
Article: main_krylov, lem:projected-residual, finite coordinate transfer.
Proof: the genuine continuous linear equivalence with finite coordinates
preserves big-O in both directions; apply the existing finite-product criterion. -/
theorem euclidean_bigO_iff_entry (v : α → EuclideanSpace ℝ (Fin p)) (ω : α → ℝ) :
    v =O[f] ω ↔ ∀ i, (fun x => v x i) =O[f] ω := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin p => ℝ)
  constructor
  · intro hv
    exact isBigO_pi.mp ((e.isBigO_comp v f).trans hv)
  · intro hv
    exact (e.isBigO_comp_rev v f).trans (isBigO_pi.mpr hv)

end
end krylov.LinearAlgebra
