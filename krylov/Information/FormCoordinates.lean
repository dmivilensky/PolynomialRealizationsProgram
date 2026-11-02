import krylov.Information.PreQuadraticPrefix
import krylov.Information.QueryBasis
import krylov.Secant.NormalizedModel

/-!
Article: main_krylov, s4:cor-Q and thm:centre, genuine common physical form coordinates.
Use: transport an original physical scenario into an actual full direction
basis and back exactly; derive the required full pre-quadratic basis rank
from the real reference and true CG-consistent direction scales.
Source: real linear form congruence, proved nonsingular inverse cancellation
and the actual full canonical CG query independence theorem.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- The forward linear congruence of an original physical form into a true full direction basis.
Use: form actual direction coordinates before constructing the physical reflected source.
Article: main_krylov, s4:cor-Q and thm:centre, actual physical direction coordinates. -/
def formMap (D : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun X := Dᵀ*X*D
  map_add' := by intro X Y; simp only [Matrix.mul_add,Matrix.add_mul]
  map_smul' := by intro c X; simp only [Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply]

/-- The actual physical scenario represented by its genuine full direction-coordinate forms.
Use: use the existing coordinate reflection theorem on original physical source data.
Article: main_krylov, s4:cor-Q and thm:centre, actual physical direction coordinates. -/
def Scenario.inCoordinates (S : Scenario n) (D : Matrix (Fin n) (Fin n) ℝ) : Scenario n :=
  S.mapForms (formMap D)

/-- A genuine nonsingular direction basis transports every actual physical form into its coordinates and back exactly.
Use: the physical reflected-scenario construction reconstructs the original source without a representation premise.
Article: main_krylov, s4:cor-Q and thm:centre, actual physical direction coordinates.
Proof: cancel the actual inverse transpose and actual inverse around the original physical form. -/
theorem inverseFormMap_formMap (D X : Matrix (Fin n) (Fin n) ℝ) (hD : IsUnit D.det) :
    inverseFormMap D (formMap D X)=X := by
  have ht : IsUnit Dᵀ.det := by simpa only [det_transpose] using hD
  change Dᵀ⁻¹*(Dᵀ*X*D)*D⁻¹=X
  simp only [← Matrix.mul_assoc,nonsing_inv_mul _ ht,Matrix.one_mul]
  rw [Matrix.mul_assoc,mul_nonsing_inv _ hD,Matrix.mul_one]

/-- A genuine physical source scenario is recovered exactly after forward direction-coordinate transport and its inverse physical transport.
Use: all existing coordinate twin and admissibility theorems apply to arbitrary original physical scenarios.
Article: main_krylov, s4:cor-Q and thm:centre, actual physical direction coordinates.
Proof: the proved exact form cancellation applies separately to the true base, each original increment, terminal perturbation and every independent correction defect. -/
theorem Scenario.inCoordinates_inPhysical (S : Scenario n) (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : IsUnit D.det) : (S.inCoordinates D).inPhysical D=S := by
  apply Scenario.ext
  · exact inverseFormMap_formMap D S.base hD
  · funext i
    exact inverseFormMap_formMap D (S.increment i) hD
  · exact inverseFormMap_formMap D S.terminal hD
  · funext i
    exact inverseFormMap_formMap D (S.correction i) hD

/-- The genuine original CG raw direction family in chronological source order.
Use: the common pre-quadratic direction basis retains actual raw query scales.
Article: main_krylov, s4:cor-Q and thm:centre, actual physical direction coordinates. -/
def referenceDirectionColumns (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (N+1))) (i : Fin (N+1)) : EuclideanSpace ℝ (Fin (N+1)) :=
  CG.direction (cgOperator A) g i.val

/-- The actual full original CG raw direction family is independent under the genuine full active-atom reference premise.
Use: derive the common pre-quadratic coordinate inverse from the real algorithm.
Article: main_krylov, s4:cor-Q and thm:centre, actual physical direction coordinates.
Proof: the proved canonical query independence remains independent after reversing its genuine chronological indexing. Its original physical direction family is independent because its true root image is independent. -/
theorem referenceDirectionColumns_independent (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount A hA g=N+1) :
    LinearIndependent ℝ (referenceDirectionColumns A g) := by
  -- Reverse the real full reference query ordering before returning to original physical directions.
  apply LinearIndependent.of_comp (cgOperator (metricRoot A)).toLinearMap
  have hc := (canonicalReferenceQueries_independent A hA g hcount).comp Fin.rev Fin.rev_injective
  convert hc using 1
  funext i
  change cgOperator (metricRoot A) (CG.direction (cgOperator A) g i.val)=
    cgOperator (metricRoot A) (CG.direction (cgOperator A) g (N-i.rev.val))
  congr 2
  have hi := i.isLt
  simp only [Fin.val_rev]
  omega


/-- Every globally CG-consistent method has a genuine nonsingular full actual direction matrix on the original pre-quadratic source class.
Use: all physical twin inverses are derived from original reference data and actual method consistency, rather than assumed.
Article: main_krylov, s4:cor-Q and thm:centre, actual physical direction coordinates.
Proof: each actual source direction is its true common CG direction times a strictly positive real unit. The proved independent genuine reference family remains independent under those actual individual scalings. -/
theorem Scenario.PreQuadratic.directionMatrix_unit {S : Scenario (N+1)}
    {A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hA : A.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount A hA g=N+1)
    (h : S.PreQuadratic (cgOperator A) g N)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m) :
    IsUnit (fullBasisMatrix (fun i : Fin (N+1) => probedDirection m S.probeOracle (S.correctionOracle N) g i.val)).det := by
  have hp := cgOperator_positive A hA
  choose c hc hd using (fun i : Fin (N+1) => h.direction hp.1 hp.2 m hm (show i.val≤N by omega))
  apply fullBasisMatrix_unit
  have hli := (referenceDirectionColumns_independent A hA g hcount).units_smul (fun i => Units.mk0 (c i) (hc i).ne')
  convert hli using 1
  funext i
  exact hd i

end
end krylov.Information
