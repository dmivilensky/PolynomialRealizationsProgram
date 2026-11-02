import krylov.OneGradient.InformedStaircase
import krylov.Stability.MovingFullReference
import krylov.Stability.MovingCoefficient
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), original moving-reference coefficient.
Use: identify the genuine source quadratic expression on the actual A0
reference and prove its cubic difference from the fixed known frame.
Source: actual CG flag dictionaries, genuine primitive moving-reference
regularity and the proved full quadratic coefficient-freezing theorem.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset Filter Topology Asymptotics krylov.Reference krylov.Secant krylov.Stability
  krylov.Correction krylov.Envelope krylov.Variation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The exact finite full-frame expression for a quadratic source coefficient.
Use: keep the physical matrix fields explicit when composing primitive
moving-frame calculus, avoiding any reduction of the actual CG recurrence.
Article: main_krylov, thm:local(a), finite source coefficient program. -/
def referenceCoefficientProgram
    (R : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (P : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (D : ℕ → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (h : EuclideanSpace ℝ (Fin (n+1))) (sigma eps : ℝ) : EuclideanSpace ℝ (Fin (n+1)) :=
  let f := ∑ k∈range n,(cgOperator (P k)*R) (D k (R h))
  sigma • ((∑ l∈range (n+1),(cgOperator (P l)ᵀ*R) (D l ((R*cgOperator (P l)) f)))-
    eps • R (D n (R h)))

/-- The original source quadratic output coefficient in a genuine own
reference metric, with actual increments and measured last relative error.
Use: both fixed known and actual moving A0 frames use the same source
fresh defect and staircase, and the true reference last-step scale.
Article: main_krylov, thm:local(a), full source coefficient. -/
def referenceQuadraticCoefficient
    (B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (g : EuclideanSpace ℝ (Fin (n+1)))
    (A : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (eps : ℝ) : EuclideanSpace ℝ (Fin (n+1)) :=
  let E := canonicalIncrement B A
  let h := canonicalCGUnitStep B g n
  ‖canonicalCGStep B g n‖ •
    (staircaseOperator B g E (E n) (n+1) (freshDefect B g E (n+1))-eps • cgOperator (E n) h)

/-- The source quadratic coefficient has its exact genuine full-CG
transported-matrix expression in the original physical increments.
Use: primitive moving-frame calculus concerns exactly the source objects.
Article: main_krylov, thm:local(a), exact source coefficient dictionary.
Proof: real full CG flags are the true orthogonal projections and their
transposes agree. The final projection is identity, giving the actual
uncompressed output increment. Expand the true fresh-defect definition. -/
theorem referenceQuadraticCoefficient_dictionary
    (B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : B.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount B hb g=n+1)
    (A : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (eps : ℝ) :
    referenceQuadraticCoefficient B g A eps=referenceCoefficientProgram
      (cgOperator (metricRoot B)⁻¹)
      (fun l => transportedFlag (canonicalCGUnitMatrix B g) l)
      (fun l => cgOperator (A (l+1)-A l)) (canonicalCGUnitStep B g n)
      ‖canonicalCGStep B g n‖ eps := by
  let R := cgOperator (metricRoot B)⁻¹
  let P := fun l => transportedFlag (canonicalCGUnitMatrix B g) l
  let D := fun l => cgOperator (A (l+1)-A l)
  let E := canonicalIncrement B A
  let h := canonicalCGUnitStep B g n
  let f := freshDefect B g E (n+1)
  have hP (l : ℕ) : cgOperator (P l)=(oldFlag B g l).starProjection := canonicalCG_transportedFlag B hb g hc l
  have hPt (l : ℕ) : cgOperator (P l)ᵀ=(oldFlag B g l).starProjection := by
    rw [cgOperator_transpose,hP]
    exact (Submodule.starProjection_isSymmetric _).clm_adjoint_eq
  have hE (l : ℕ) : cgOperator (E l)=R*D l*R := by
    simp only [E,canonicalIncrement,relativeOperator,cgOperator,map_mul]
    rfl
  have hf : f=∑ k∈range n,(cgOperator (P k)*R) (D k (R h)) := by
    simp only [f,freshDefect,Nat.add_sub_cancel,hE,hP,mul_apply_eq_comp,h]
  have hL : (∑ l∈range (n+1),cgOperator (P l)ᵀ*cgOperator (E l)*cgOperator (P l))=
      staircaseOperator B g E (E n) (n+1) := by
    simp_rw [hPt,hP]
    rw [sum_range_succ,fullCG_last_projection B hb g hc,one_mul,mul_one]
    rfl
  have hsum : (∑ l∈range (n+1),(cgOperator (P l)ᵀ*R) (D l ((R*cgOperator (P l)) f)))=
      staircaseOperator B g E (E n) (n+1) f := by
    rw [← hL]
    simp only [_root_.sum_apply,hE,mul_apply_eq_comp]
  change _=‖canonicalCGStep B g n‖ • _
  rw [← hf,hsum]
  change ‖canonicalCGStep B g n‖ •
    (staircaseOperator B g E (E n) (n+1) f-eps • cgOperator (E n) h)=_
  rw [hE]
  rfl

/-- The full original source coefficient on the moving actual positive
reference differs cubically from its fixed known-reference coefficient.
Every CG frame, flag, inverse, scale and domain follows from primitive
C-one reference data, while all real increments and epsilon are retained.
Use: closes the original own-A0 frame replacement in the native formula.
Article: main_krylov, thm:local(a), genuine moving source coefficient.
Proof: true moving full CG frame data give every primitive coefficient
chart and the actual reference neighborhood. Physical increments vanish
at the known reference. Instantiate the proved general quadratic freezing
theorem, then apply the exact source dictionary on that real neighborhood. -/
theorem referenceQuadraticCoefficient_moving_cubic
    (B : X → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hB : ContDiffAt ℝ 1 B 0)
    (hpos : ∀ᶠ z in 𝓝 (0 : X),(B z).PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1)))
    (hc : referenceAtomCount (B 0) hpos.self_of_nhds g=n+1)
    (A : X → ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : ∀ j,A 0 j=B 0)
    (eps : X → ℝ) (heps : ContDiffAt ℝ 1 eps 0) (heps0 : eps 0=0) :
    (fun z => referenceQuadraticCoefficient (B z) g (A z) (eps z)-
      referenceQuadraticCoefficient (B 0) g (A z) (eps z)) =O[𝓝 0] (fun z => ‖z‖^3) := by
  let R := fun z => cgOperator (metricRoot (B z))⁻¹
  let P := fun l z => transportedFlag (canonicalCGUnitMatrix (B z) g) l
  let U := fun l z => cgOperator (P l z)ᵀ*R z
  let V := fun l z => R z*cgOperator (P l z)
  let D := fun l z => cgOperator (A z (l+1)-A z l)
  let h := fun z => canonicalCGUnitStep (B z) g n
  let sigma := fun z => ‖canonicalCGStep (B z) g n‖
  have hR : ContDiffAt ℝ 1 R 0 := matrixOperator_contDiffAt _ 0 (metricRoot_inverse_contDiffAt B 0 hB hpos)
  have hP (l : ℕ) : ContDiffAt ℝ 1 (P l) 0 := (moving_reference_flag_data B hB hpos g hc l).1
  have hPt (l : ℕ) : ContDiffAt ℝ 1 (fun z => (P l z)ᵀ) 0 := by
    let L := (Matrix.transposeLinearEquiv (R := ℝ) (m := Fin (n+1)) (n := Fin (n+1)) (α := ℝ)).toContinuousLinearEquiv
    exact L.toContinuousLinearMap.contDiff.contDiffAt.comp 0 (hP l)
  have hU (l : ℕ) : ContDiffAt ℝ 1 (U l) 0 := (matrixOperator_contDiffAt _ 0 (hPt l)).mul hR
  have hV (l : ℕ) : ContDiffAt ℝ 1 (V l) 0 := hR.mul (matrixOperator_contDiffAt _ 0 (hP l))
  have hD (l : ℕ) : ContDiffAt ℝ 1 (D l) 0 := matrixOperator_contDiffAt _ 0 ((hA (l+1)).sub (hA l))
  have hD0 (l : ℕ) : D l 0=0 := by simp only [D,hA0,sub_self,cgOperator,map_zero]
  have hstep := canonicalCG_step_contDiffAt B hB hpos g n (by omega)
  have hfreeze := movingQuadraticCoefficient_freeze_cubic (range (n+1)) (range n) U V D
    (fun l z => cgOperator (P l z)) R D (D n) h sigma eps
    (fun l _ => hU l) (fun l _ => hV l) (fun l _ => hD l) (fun l _ => hD0 l)
    (fun l _ => matrixOperator_contDiffAt _ 0 (hP l)) hR
    (fun l _ => hD l) (fun l _ => hD0 l) (hD n) (hD0 n) hstep.2.2 hstep.2.1 heps heps0
  have hprogram : (fun z => referenceCoefficientProgram (R z) (fun l => P l z) (fun l => D l z)
      (h z) (sigma z) (eps z)-referenceCoefficientProgram (R 0) (fun l => P l 0) (fun l => D l z)
        (h 0) (sigma 0) (eps z)) =O[𝓝 0] (fun z => ‖z‖^3) := by
    apply hfreeze.congr_left
    intro z
    dsimp only [referenceCoefficientProgram,movingDriftCoefficient,U,V]
  apply hprogram.congr' ?_ EventuallyEq.rfl
  filter_upwards [moving_reference_full_atoms B hB hpos g hc] with z hz
  obtain ⟨hb,hcount⟩ := hz
  have hm : referenceQuadraticCoefficient (B z) g (A z) (eps z)=
      referenceCoefficientProgram (R z) (fun l => P l z) (fun l => D l z) (h z) (sigma z) (eps z) :=
    referenceQuadraticCoefficient_dictionary (B z) hb g hcount (A z) (eps z)
  have hf : referenceQuadraticCoefficient (B 0) g (A z) (eps z)=
      referenceCoefficientProgram (R 0) (fun l => P l 0) (fun l => D l z) (h 0) (sigma 0) (eps z) :=
    referenceQuadraticCoefficient_dictionary (B 0) hpos.self_of_nhds g hc (A z) (eps z)
  exact congrArg₂ (fun v w => v-w) hm.symm hf.symm

end
end krylov.OneGradient
