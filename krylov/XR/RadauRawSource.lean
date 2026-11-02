import krylov.XR.RadauScaling

/-!
Article: main_krylov, apG:radau-adequate, full raw-direction source theorem.
Use: apply the proved primitive unit argument to the actual nonzero physical
direction. Both implemented coefficients remain literally unchanged.
Source: exact normalization dictionary, not a modified algorithm.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Convergence krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- Complete original physical source adequacy for the actual arbitrary
nonzero raw direction. Article: main_krylov, apG:radau-adequate. -/
theorem radau_primitive_adequate_raw
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian)
    (s y : Fin p → EuclideanSpace ℝ (Fin n)) (hs : ∀ i,‖s i‖=1)
    (d : EuclideanSpace ℝ (Fin n)) (hd : d≠0)
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
    mu≤lo ∧ lo ≤ (inner ℝ d (cgOperator H d)/‖d‖^2) ∧ (inner ℝ d (cgOperator H d)/‖d‖^2)≤hi ∧ hi≤upper ∧
      mu≤(lo+hi)/2 ∧ (lo+hi)/2≤upper ∧
      (inner ℝ d (cgOperator H d)/‖d‖^2)/((lo+hi)/2)≤2*hi/(hi+lo) ∧
      2*hi/(hi+lo)≤2*upper/(upper+mu) := by
  let v := (‖d‖⁻¹ : ℝ) • d
  have hv : ‖v‖=1 := norm_smul_inv_norm hd
  have hvo : ∀ i,inner ℝ (y i) v=0 := by
    intro i
    simp only [v,real_inner_smul_right,ho i,mul_zero]
  have hc := radau_coefficients_smul s (latest (crossGram s y)) d hd (‖d‖⁻¹) mu upper
    (inv_ne_zero (norm_ne_zero_iff.mpr hd))
  have hr := radau_primitive_adequate H hH s y hs v hv mu a b upper sigma epsilon
    hmu hmua hupper hband ha hb hsigma hsigma₁ he hHlo hHhi hlower hHnorm hgain hy hvo
    hsmall hsmalllo hsmallhi
  simpa only [v,hc.1,hc.2,radau_normalized_energy] using hr

end
end krylov.XR
