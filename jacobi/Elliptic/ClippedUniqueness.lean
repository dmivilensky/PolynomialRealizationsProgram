import jacobi.Elliptic.TurningHeight
import jacobi.Variational.NoDescent
import jacobi.Young.SemilinearUniqueness
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Connected.Clopen

/-!
Article: jacobi, Theorem D.5.
The genuine clipped equation has a locally Lipschitz vector field, including
at y=0. Equal value and slope determine its global solution. This supplies
reflection symmetry and rules out repeated turning points of the actual
elliptic optimizer before deriving its quadrature change of variables.
Source: Picard--Lindelof uniqueness and connectedness, using the shared Young continuation theorem.
Use: global initial-value uniqueness supplies symmetry and excludes periodic optimizer states.
-/
namespace jacobi.Elliptic
noncomputable section
open Set Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The autonomous clipped field of the actual normalized elliptic Euler equation.
Use: global initial-value uniqueness supplies symmetry and excludes periodic optimizer states.
Article: jacobi, Theorem D.5.
-/
def clippedField (σ : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (z.2,4*(z.1-σ)-6*(max z.1 0)^2)

/-- The clipped field is locally Lipschitz also on the free-boundary axis.
Use: discharges the actual vector-field regularity premise of Picard--Lindelof.
Article: jacobi, Theorem D.5.
Proof: factor the field into a globally Lipschitz positive-part embedding
and a smooth polynomial map on the enlarged product space. -/
theorem clippedField_locallyLipschitz (σ : ℝ) : LocallyLipschitz (clippedField σ) := by
  let P (z : (ℝ × ℝ) × ℝ) : ℝ × ℝ := (z.1.2,4*(z.1.1-σ)-6*z.2^2)
  have hP : ContDiff ℝ 1 P := by dsimp only [P]; fun_prop
  have hE : LocallyLipschitz (fun z : ℝ × ℝ => (z,max z.1 0)) :=
    LipschitzWith.id.locallyLipschitz.prodMk ((LipschitzWith.prod_fst.max_const 0).locallyLipschitz)
  exact hP.locallyLipschitz.comp hE

/-- Global uniqueness for the actual clipped second-order equation, including its free boundary.
Use: identifies reflected and translated actual optimizer states from their turning data.
Article: jacobi, Theorem D.5.
Source: Picard--Lindelof uniqueness and connectedness of the real line.
Proof: the proved clipped vector field is locally Lipschitz. The set where the
two value/slope pairs agree is closed by continuity and open by local ODE
uniqueness. The initial equality makes this clopen set the whole line. -/
theorem clipped_unique {f d g e : ℝ → ℝ} (σ b : ℝ)
    (hf : ∀ x, HasDerivAt f (d x) x)
    (hd : ∀ x, HasDerivAt d (4*(f x-σ)-6*(max (f x) 0)^2) x)
    (hg : ∀ x, HasDerivAt g (e x) x)
    (he : ∀ x, HasDerivAt e (4*(g x-σ)-6*(max (g x) 0)^2) x)
    (h0 : f b=g b) (h1 : d b=e b) : f=g ∧ d=e := by
  have hh := jacobi.Young.autonomous_unique (clippedField_locallyLipschitz σ)
    (fun x => (hf x).prodMk (hd x)) (fun x => (hg x).prodMk (he x)) (Prod.ext h0 h1)
  exact ⟨funext (fun x => congrArg Prod.fst (congrFun hh x)),
    funext (fun x => congrArg Prod.snd (congrFun hh x))⟩

end
end jacobi.Elliptic
