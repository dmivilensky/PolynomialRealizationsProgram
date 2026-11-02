import krylov.XR.RadauRadius

/-!
Article: main_krylov, prop:floor, primitive upper-only consistency bound.
Use: derive the true upper Schur bound from the strict upper spectral
margin alone, irrespective of the algorithm's supplied lower estimate.
Source: apply the constructive Radau theorem with the auxiliary positive
class lower bound a/2; the actual upper coefficient is unchanged.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Convergence krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- A strict upper class margin alone gives a positive actual upper
consistency coefficient enclosing the true physical curvature.
Article: main_krylov, prop:floor. -/
theorem radau_upper_only_adequacy
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian)
    (s y : Fin p → EuclideanSpace ℝ (Fin n)) (hs : ∀ i,‖s i‖=1)
    (d : EuclideanSpace ℝ (Fin n)) (hd : d≠0)
    (a b upper sigma epsilon : ℝ) (ha : 0<a) (hab : a≤b) (hupper : b<upper) (hb : 0<b)
    (hsigma : 0<sigma) (hsigma₁ : sigma≤1) (he : 0≤epsilon)
    (hHlo : (H-a • 1).PosSemidef) (hHhi : (b • 1-H).PosSemidef)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),a*‖v‖^2 ≤ inner ℝ v (cgOperator H v))
    (hHnorm : ‖cgOperator H‖≤b)
    (hgain : ∀ c : Fin p → ℝ,sigma^2*‖WithLp.toLp 2 c‖^2≤‖combine s c‖^2)
    (hy : ∀ i,‖y i-cgOperator H (s i)‖≤epsilon)
    (ho : ∀ i,inner ℝ (y i) d=0)
    (hsmall : Real.sqrt p*epsilon≤a*sigma^2/2)
    (hsmalllo : (p+1 : ℕ)*epsilon<(a-a/2)*(a*sigma^2/(2*b)))
    (hsmallhi : (p+1 : ℕ)*epsilon<(upper-b)*(a*sigma^2/(2*b))) :
    a≤upperConsistencyCoefficient s (latest (crossGram s y)) d upper ∧
      inner ℝ d (cgOperator H d)≤
        upperConsistencyCoefficient s (latest (crossGram s y)) d upper*‖d‖^2 ∧
      upperConsistencyCoefficient s (latest (crossGram s y)) d upper≤upper := by
  have hr := radau_primitive_adequate_raw H hH s y hs d hd (a/2) a b upper sigma epsilon
    (by positivity) (by linarith) hupper (by linarith) ha hb hsigma hsigma₁ he hHlo hHhi
    hlower hHnorm hgain hy ho hsmall hsmalllo hsmallhi
  have hD : 0<‖d‖^2 := pow_pos (norm_pos_iff.mpr hd) _
  have hl : a ≤ inner ℝ d (cgOperator H d)/‖d‖^2 :=
    (le_div_iff₀ hD).mpr (hlower d)
  exact ⟨hl.trans hr.2.2.1,(div_le_iff₀ hD).mp hr.2.2.1,hr.2.2.2.1⟩

end
end krylov.XR
