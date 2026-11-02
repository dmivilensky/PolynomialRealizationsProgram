import krylov.OneGradient.InformedNativeCurvature
import krylov.Reference.CGCurvatureCoordinates
import krylov.OneGradient.IncomingFreshDictionary
import krylov.Stability.MetricRootRegularity
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual canonical informed pivot.
Use: the real native S relative error has the printed unknown-prior plus
observed-increment canonical diagonal, with a true quadratic remainder.
Source: actual native informed curvature jet, genuine CG quotient
normalization and exact telescoping of real canonical physical increments.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual canonical last-curvature change is precisely the true
unknown base prior plus the actual observed canonical increment sum.
Use: the source diagonal retains every real physical perturbation.
Article: main_krylov, thm:local(a), exact prior/increment decomposition.
Proof: actual increments telescope and the fixed inverse-root congruence
is additive; the remaining physical matrix identity is additive cancellation. -/
theorem canonical_prior_increment_sum (base : Matrix (Fin n) (Fin n) ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) :
    relativeOperator base (A N-base)=relativeOperator base (A 0-base)+
      ∑ l∈range N,canonicalIncrement base A l := by
  have hs := canonicalIncrement_sum_Ico base A 0 N (Nat.zero_le N)
  rw [Nat.Ico_zero_eq_range] at hs
  rw [hs]
  simp only [relativeOperator,← Matrix.mul_add,← Matrix.add_mul]
  congr 2
  abel

/-- The true implemented informed S last-pivot error has the original
prior-plus-increments coefficient with a quadratic primitive-parameter
remainder. The direction, quotient branch and every actual smoothness
domain are derived from the observed implementation.
Use: supplies the genuine unmeasured-pivot coefficient for the original
known-base upper estimates and physical attaining source families.
Article: main_krylov, thm:local(a), actual informed epsilon expansion.
Proof: use the proved genuine native physical curvature remainder. Its
actual frozen CG quotient is exactly its unit-CG canonical diagonal;
the true physical prior and all observed increments telescope exactly. -/
theorem informed_native_step_pivot_remainder
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (A : X → ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : ∀ j,A 0 j=base) :
    let op := fun z j => cgOperator (A z j)
    let h := canonicalCGUnitStep base g n
    (fun z => xrfcNativeTrialError false (informedTrial (cgOperator base)) (op z) g n+
      inner ℝ h (cgOperator (relativeOperator base (A z 0-base)+
        ∑ l∈range n,canonicalIncrement base (A z) l) h)) =O[𝓝 0] (fun z => ‖z‖^2) := by
  let op := fun z j => cgOperator (A z j)
  have hop : ∀ j,ContDiffAt ℝ 1 (fun z => op z j) 0 := fun j => matrixOperator_contDiffAt _ 0 (hA j)
  have hop0 : op 0=fun _ => cgOperator base := funext (fun j => congrArg cgOperator (hA0 j))
  have hk : n<referenceAtomCount base hb g := by omega
  have hr := informed_native_step_curvature_remainder base hb g (n+1)
    (fun i hi => cg_nonstagnation base hb g i (by omega)) op hop hop0 n (by omega)
  apply hr.congr_left
  intro z
  have he : op z n-cgOperator base=cgOperator (A z n-base) := by simp only [op,cgOperator,map_sub]
  rw [he,canonicalCG_curvature_quotient base hb g n hk,
    ← canonical_prior_increment_sum base (A z) n]
  simp only [op,relativeOperator,cgOperator,map_mul,map_sub]

end
end krylov.OneGradient
