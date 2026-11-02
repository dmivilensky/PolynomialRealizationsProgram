import krylov.Information.CommonTwinAdmissible
import krylov.Information.FiniteCentre

/-!
Article: main_krylov, s4:cor-Q, genuine common terminal information geometry.
Use: the actual common physical pre-quadratic twin has opposite terminal
operators about its true observed centre; every original one-correction
method sees the same actual incoming gradient and one common correction.
Source: real common-prefix/probe preservation, finite-horizon physical
reflection and the existing exact actual one-query robust radius theorem.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The genuine observed physical centre formed in the original common chronological CG direction flag.
Use: compare the same terminal physical centre across the original pre-quadratic information regime.
Article: main_krylov, s4:cor-Q, the common physical latest-information centre. -/
def Scenario.preQuadraticCentre (S : Scenario (N+1)) (Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (N+1))) : Matrix (Fin (N+1)) (Fin (N+1)) ℝ :=
  let D := fullBasisMatrix (referenceDirectionColumns Q g)
  (S.inCoordinates D).physicalCentre D

/-- The one actual common pre-quadratic twin has exactly the opposite genuine terminal operator about the original common observed physical centre.
Use: the common source pair has the real two-scenario centre structure without assumptions on unqueried future source operators.
Article: main_krylov, s4:cor-Q, actual common terminal reflection.
Proof: the genuine full original CG frame supplies the real direction
inverse. Original finite source symmetry survives forward coordinates.
The proved finite-horizon physical centre identity applies there; the
genuine zero intermediate-defect replacement preserves its terminal operator. -/
theorem Scenario.preQuadraticTwin_terminal (S : Scenario (N+1))
    (Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hQ : Q.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount Q hQ g=N+1)
    (hbase : S.base.IsSymm) (hE : ∀ i<N, (S.increment i).IsSymm) :
    (S.preQuadraticTwin Q g).lastOperator N=(2 : ℝ) • S.preQuadraticCentre Q g-S.lastOperator N := by
  -- Use only the original finite physical source symmetries in the actual common direction basis.
  let D := fullBasisMatrix (referenceDirectionColumns Q g)
  let C := S.inCoordinates D
  have hD : IsUnit D.det := fullBasisMatrix_unit _ (referenceDirectionColumns_independent Q hQ g hcount)
  have hCb : C.base.IsSymm := formMap_isSymm D S.base hbase
  have hCE (i : ℕ) (hi : i<N) : (C.increment i).IsSymm := formMap_isSymm D _ (hE i hi)
  change (((C.reflect N).inPhysical D).withCorrections (fun _ => 0)).lastOperator N=
    (2 : ℝ) • C.physicalCentre D-S.lastOperator N
  rw [Scenario.withCorrections_lastOperator,C.physical_reflect_about_centre_finite D hD hCb hCE]
  rw [S.inCoordinates_inPhysical D hD]



end
end krylov.Information
