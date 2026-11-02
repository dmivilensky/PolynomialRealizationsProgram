import krylov.XR.RadauEstimates

/-!
Article: main_krylov, apG:radau-adequate, actual primitive source theorem.
Use: close the full chain from true reference positivity, independent
observed unit secants and their actual error to the algorithm's ordinary
Schur coefficients and sharp midpoint adequacy. The strict spectral
enclosure gives exact containment for sufficiently accurate observations.
Source: constructive physical extension proved in RadauPrimitive, followed
by the original attained consistency-interval and scalar midpoint theorems.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Convergence krylov.Secant
  krylov.Completion krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- Genuine unit-direction source adequacy, with explicit sufficient
smallness bounds and no assumed Schur feasibility, endpoint order, inverse
domain, trial accuracy or future acceptance.
Article: main_krylov, apG:radau-adequate. -/
theorem radau_primitive_adequate
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian)
    (s y : Fin p → EuclideanSpace ℝ (Fin n)) (hs : ∀ i,‖s i‖=1)
    (d : EuclideanSpace ℝ (Fin n)) (hd : ‖d‖=1)
    (mu a b upper sigma epsilon : ℝ) (hmu : 0<mu) (hmua : mu<a)
    (hupper : b<upper) (hband : mu≤upper) (ha : 0<a) (hb : 0<b)
    (hsigma : 0<sigma) (hsigma₁ : sigma≤1) (he : 0≤epsilon)
    (hHlo : (H-a • 1).PosSemidef) (hHhi : (b • 1-H).PosSemidef)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),a*‖v‖^2 ≤ inner ℝ v (cgOperator H v))
    (hHnorm : ‖cgOperator H‖≤b)
    (hgain : ∀ c : Fin p → ℝ,sigma^2*‖WithLp.toLp 2 c‖^2≤‖combine s c‖^2)
    (hy : ∀ i,‖y i-cgOperator H (s i)‖≤epsilon)
    (ho : ∀ i,inner ℝ (y i) d=0)
    (hsmall : Real.sqrt p*epsilon≤a*sigma^2/2)
    (hsmalllo : (p+1 : ℕ)*epsilon<(a-mu)*(a*sigma^2/(2*b)))
    (hsmallhi : (p+1 : ℕ)*epsilon<(upper-b)*(a*sigma^2/(2*b))) :
    let lo := lowerConsistencyCoefficient s (latest (crossGram s y)) d mu
    let hi := upperConsistencyCoefficient s (latest (crossGram s y)) d upper
    mu≤lo ∧ lo ≤ inner ℝ d (cgOperator H d) ∧ inner ℝ d (cgOperator H d)≤hi ∧ hi≤upper ∧
      mu≤(lo+hi)/2 ∧ (lo+hi)/2≤upper ∧
      inner ℝ d (cgOperator H d)/((lo+hi)/2)≤2*hi/(hi+lo) ∧
      2*hi/(hi+lo)≤2*upper/(upper+mu) := by
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have hg : 0<a*sigma^2/(2*b) := by positivity
  have haug := radau_augmented_gain (cgOperator H) hsym s y d a b sigma epsilon ha hb
    hsigma hsigma₁ he hd hlower hHnorm hgain hy ho hsmall
  have hS := radauStepMatrix_injective s (sigma^2) (sq_pos_of_pos hsigma) hgain
  have hnew := radau_new_direction s d _ hg haug
  have hc := radau_primitive_completion H hH s y hs d hd mu a b upper sigma epsilon
    hmua hupper hband ha hb hsigma hsigma₁ he hHlo hHhi hlower hHnorm hgain hy ho
    hsmall hsmalllo hsmallhi
  have hp := radau_pencil_restrict s d _ _ mu upper hc.1 hc.2.1
  obtain ⟨B,hB,hBc⟩ := hc.2.2
  have hr := radau_coefficients_feasible s hS d hnew _ mu upper hmu hband hp.1 hp.2 ⟨B,hB⟩
  have hcurv := hr.2.2.2 B hB
  have heq : inner ℝ d (cgOperator B d)=inner ℝ d (cgOperator H d) := by
    simpa only [cgOperator,Matrix.inner_toEuclideanCLM,star_trivial] using hBc
  rw [heq,hd,one_pow,mul_one,mul_one] at hcurv
  have hratio := radau_midpoint_ratio mu upper _ _ (inner ℝ d (cgOperator H d))
    hmu hr.1 hr.2.1 hr.2.2.1 hcurv.2
  refine ⟨hr.1,hcurv.1,hcurv.2,hr.2.2.1,?_,?_,hratio.2.1,hratio.2.2⟩ <;>
    linarith only [hr.1,hr.2.1,hr.2.2.1]

end
end krylov.XR
