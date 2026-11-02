import krylov.Functions.MetricFCOwnCubicRemainder
import krylov.Functions.GenuineThirdTensor
import krylov.Stability.MetricRootRegularity

/-!
Article: main_krylov, thm:Htransfer, canonical dictionary for the original actual-A₀ reference.
Use: construct the actual positive matrix represented by the observed first
secant, derive its full spectral count from true CG nonstagnation, and convert
the genuine native derivative coefficient into the literal printed spatial response.
Source: true matrix/operator equivalence, actual CG stopping and thm:A.
-/

namespace krylov.Functions
noncomputable section
open Set Metric Matrix Finset Filter Topology krylov.Methods krylov.Reference krylov.Nonlinear krylov.Variation krylov.Secant krylov.Stability
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator MatrixOrder
variable {n : ℕ}

/-- The actual matrix of a physical continuous linear operator in the genuine Euclidean basis.
Article: main_krylov, thm:Htransfer, actual original A₀ matrix. -/
def physicalOperatorMatrix (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm A

/-- The actual observed matrix represents exactly the original physical operator.
Article: main_krylov, thm:Htransfer, true A₀ dictionary. -/
theorem physicalOperatorMatrix_operator (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    cgOperator (physicalOperatorMatrix A) = A :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).apply_symm_apply A

/-- A genuine positive symmetric physical secant gives a genuinely positive definite observed matrix.
Article: main_krylov, thm:Htransfer, actual original reference positivity. -/
theorem physicalOperatorMatrix_posDef (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : A.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (A v)) :
    (physicalOperatorMatrix A).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    change (cgOperator (physicalOperatorMatrix A)).toLinearMap.IsSymmetric
    rw [physicalOperatorMatrix_operator]
    exact hA
  · intro x hx
    let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
    have hv : v ≠ 0 := by
      intro hz
      exact hx (congrArg WithLp.ofLp hz)
    have hp := hpos v hv
    rw [← physicalOperatorMatrix_operator A] at hp
    unfold cgOperator at hp
    rw [Matrix.inner_toEuclideanCLM] at hp
    simpa only [star_trivial] using hp

/-- True nonstagnation through the full ambient prefix forces exactly the full active spectral count.
Article: main_krylov, thm:Htransfer, the original full-reference hypothesis. -/
theorem referenceAtomCount_eq_of_full_nonstagnation (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hpre : ∀ i < n, CG.gradient (cgOperator base) g i ≠ 0) :
    referenceAtomCount base hb g = n := by
  have hz : CG.gradient (cgOperator base) g n = 0 := by
    have h := cg_gradient_finrank_zero (cgOperator base) (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g
    simpa only [finrank_euclideanSpace_fin] using h
  have hle := (cg_stopping_iff base hb g n).mp hz
  have hge : n ≤ referenceAtomCount base hb g := by
    by_contra hn
    exact hpre _ (by omega) (cg_terminates base hb g)
  omega

/-- The original own-reference compatible increment is the true canonical slice at the printed midpoint half-sum.
Article: main_krylov, thm:Htransfer, T[ξ_l] in the original A₀ coordinates. -/
def ownFCCompatibleIncrements (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (l : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  physicalCanonicalMatrix base hb (D ((1 / 2 : ℝ) •
    (referenceStep (cgOperator base) g l + referenceStep (cgOperator base) g (l + 1))))

/-- The actual own-A₀ derivative coefficient equals exactly the literal printed CG flag/tail response on compatible tensor slices.
Article: main_krylov, thm:Htransfer, original-reference spatial coefficient. -/
theorem fcOwnLeading_eq_fullCycleResponse (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hDsym : ∀ v, (D v).toLinearMap.IsSymmetric) (g u : EuclideanSpace ℝ (Fin n))
    (hcount : referenceAtomCount base hb g = n) :
    let m := fcOwnReferenceMidpoint (cgOperator base) g u
    cgOperator (metricRoot base)⁻¹
      (fcLeadingOperator (cgOperator base) n g (fun i => D (m i.val - m 0))) =
      fullCycleResponse base g (range n) (ownFCCompatibleIncrements base hb D g) := by
  let m := fcOwnReferenceMidpoint (cgOperator base) g u
  have hc := fcLeadingOperator_eq_fullCycleResponse base hb g hcount (fun i => D (m i - m 0))
    (fun i _ => hDsym _)
  convert hc using 2
  funext l
  rw [← physicalCanonicalMatrix_sub, ← map_sub]
  have heq : (m (l + 1) - m 0) - (m l - m 0) = m (l + 1) - m l := by abel
  rw [heq]
  exact congrArg (fun v => physicalCanonicalMatrix base hb (D v))
    (fcOwnReferenceMidpoint_sub (cgOperator base) g u l).symm

/-- The inverse-root operator of a true positive matrix is continuous within any genuine positive reference family.
Article: main_krylov, thm:Htransfer, original reference metric uniformity.
Proof: the actual positive CFC root is continuous on the positive cone and
its real inverse is continuous at every genuine invertible root. -/
theorem own_inverseRoot_continuousOn (K : Set ((EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n)))
    (hquad : ∀ z ∈ K, z.1.toLinearMap.IsSymmetric ∧ ∀ v, v ≠ 0 → 0 < inner ℝ v (z.1 v)) :
    ContinuousOn (fun z => cgOperator (metricRoot (physicalOperatorMatrix z.1))⁻¹) K := by
  let L := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm.toAlgEquiv.toLinearMap.toContinuousLinearMap
  have hbase : Continuous (fun z : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) => physicalOperatorMatrix z.1) :=
    L.continuous.comp continuous_fst
  intro z hz
  have hb := physicalOperatorMatrix_posDef z.1 (hquad z hz).1 (hquad z hz).2
  have hsqrt : ContinuousWithinAt (fun B : Matrix (Fin n) (Fin n) ℝ => CFC.sqrt B)
      {B | 0 ≤ B} (physicalOperatorMatrix z.1) := CFC.continuousOn_sqrt _ hb.posSemidef.nonneg
  have hbc : ContinuousWithinAt
      (fun y : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) => physicalOperatorMatrix y.1) K z :=
    hbase.continuousAt.continuousWithinAt
  have hmaps : MapsTo
      (fun y : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) => physicalOperatorMatrix y.1)
      K {B | 0 ≤ B} :=
    fun y hy => (physicalOperatorMatrix_posDef y.1 (hquad y hy).1 (hquad y hy).2).posSemidef.nonneg
  have hroot : ContinuousWithinAt (fun y => metricRoot (physicalOperatorMatrix y.1)) K z :=
    hsqrt.comp (f := fun y : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) => physicalOperatorMatrix y.1) hbc hmaps
  have hu : IsUnit (metricRoot (physicalOperatorMatrix z.1)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (metricRoot_det_unit _ hb)
  have hi := contDiffAt_ringInverse (n := 1) ℝ hu.unit
  rw [hu.unit_spec] at hi
  have hinv : ContinuousWithinAt (fun y => (metricRoot (physicalOperatorMatrix y.1))⁻¹) K z := by
    simpa only [Function.comp_def, ← Matrix.nonsing_inv_eq_ringInverse] using hi.continuousAt.comp_continuousWithinAt
      (f := fun y : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) => metricRoot (physicalOperatorMatrix y.1)) hroot
  let P := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap.toContinuousLinearMap
  exact P.continuous.continuousAt.comp_continuousWithinAt
    (f := fun y : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) => (metricRoot (physicalOperatorMatrix y.1))⁻¹) hinv

/-- The actual inverse roots are uniformly bounded on every genuine compact positive own-reference family.
Article: main_krylov, thm:Htransfer, original canonical compact uniformity. -/
theorem own_inverseRoot_compact_bound
    (K : Set ((EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K)
    (hquad : ∀ z ∈ K, z.1.toLinearMap.IsSymmetric ∧ ∀ v, v ≠ 0 → 0 < inner ℝ v (z.1 v)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K, ‖cgOperator (metricRoot (physicalOperatorMatrix z.1))⁻¹‖ ≤ M := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (own_inverseRoot_continuousOn K hquad)
  exact ⟨|M|, abs_nonneg _, fun z hz => (hM z hz).trans (le_abs_self _)⟩

/-- Genuine inverse-root transport converts the actual own-reference native derivative remainder to exactly the printed spatial-response remainder.
Article: main_krylov, thm:Htransfer, canonical native output dictionary. -/
theorem fcOwnCanonical_error_bound (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hDsym : ∀ v, (D v).toLinearMap.IsSymmetric) (g u : EuclideanSpace ℝ (Fin n))
    (hcount : referenceAtomCount base hb g = n) (ε : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    let m := fcOwnReferenceMidpoint (cgOperator base) g u
    ‖cgOperator (metricRoot base)⁻¹ v - ε ^ 2 •
      fullCycleResponse base g (range n) (ownFCCompatibleIncrements base hb D g)‖ ≤
      ‖cgOperator (metricRoot base)⁻¹‖ * ‖v - ε ^ 2 •
        fcLeadingOperator (cgOperator base) n g (fun i => D (m i.val - m 0))‖ := by
  let m := fcOwnReferenceMidpoint (cgOperator base) g u
  have hc := fcOwnLeading_eq_fullCycleResponse base hb D hDsym g u hcount
  have hn := (cgOperator (metricRoot base)⁻¹).le_opNorm
    (v - ε ^ 2 • fcLeadingOperator (cgOperator base) n g (fun i => D (m i.val - m 0)))
  rw [map_sub, map_smul, hc] at hn
  exact hn

end
end krylov.Functions
