import krylov.XR.LocalSchurNormalization

/-!
Article: main_krylov, apG:radau-adequate, genuine arbitrary raw windows.
Use: recover both literal consistency endpoints, their midpoint enclosure
and the sharp curvature ratio on the actual unnormalized stored steps.
Source: constructive Radau completion and exact raw-pair congruence; all
inverse domains and consistency are derived from primitive physical data.
-/

/-!
Article: krylov, Proposition F.9 [apG:radau-adequate].

A strict spectral band and small genuine secant errors imply all actual Schur inverse domains
and the midpoint adequacy ratio, uniformly over window sizes.
The raw physical-source theorem is stronger than the printed O(ε) estimate: it constructs a
feasible compression preserving the true directional curvature. The Armijo restriction remains
explicit.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant krylov.Reference krylov.Convergence
open krylov.Methods hiding unitWindow unitWindow_norm unitWindow_diagonal_unit
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- The original full Radau statement on actual arbitrary raw steps and
raw new direction. Its exact inclusion is stronger than the printed Oε
endpoint error, and the preceding radius is uniform over p≤n. -/
theorem rawWindow_radau_adequate
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian)
    (s y : Fin p → EuclideanSpace ℝ (Fin n)) (hs : ∀ i,s i≠0)
    (d : EuclideanSpace ℝ (Fin n)) (hd : d≠0)
    (mu a b upper sigma epsilon : ℝ) (hmu : 0<mu) (hmua : mu<a)
    (hupper : b<upper) (hband : mu≤upper) (ha : 0<a) (hb : 0<b)
    (hsigma : 0<sigma) (hsigma₁ : sigma≤1) (he : 0≤epsilon)
    (hHlo : (H-a • 1).PosSemidef) (hHhi : (b • 1-H).PosSemidef)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),a*‖v‖^2 ≤ inner ℝ v (cgOperator H v))
    (hHnorm : ‖cgOperator H‖≤b)
    (hgain : ∀ c : Fin p → ℝ,sigma^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow s) c‖^2)
    (hy : ∀ i,‖y i-cgOperator H (s i)‖≤epsilon*‖s i‖)
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
  have hr := radau_primitive_adequate_raw H hH (unitWindow s) (unitWindowImages s y)
    (unitWindow_norm s hs) d hd mu a b upper sigma epsilon hmu hmua hupper hband ha hb hsigma hsigma₁ he
    hHlo hHhi hlower hHnorm hgain (unitWindow_reference_error _ s y hs epsilon hy)
    (by intro i; change inner ℝ (‖s i‖⁻¹ • y i) d = 0; rw [real_inner_smul_left, ho, mul_zero])
    hsmall hsmalllo hsmallhi
  have hlo : lowerConsistencyCoefficient (unitWindow s)
      (latest (crossGram (unitWindow s) (unitWindowImages s y))) d mu =
      lowerConsistencyCoefficient s (latest (crossGram s y)) d mu := by
    change lowerConsistencyCoefficient (rescaleWindow s (fun i => ‖s i‖⁻¹))
      (ss1Model (rescaleWindow s (fun i => ‖s i‖⁻¹))
        (rescaleWindow y (fun i => ‖s i‖⁻¹))) d mu = _
    rw [ss1Model_rescale, lowerConsistencyCoefficient_rescale _ _ _
      (unitWindow_diagonal_unit s hs)]
    rfl
  have hhi : upperConsistencyCoefficient (unitWindow s)
      (latest (crossGram (unitWindow s) (unitWindowImages s y))) d upper =
      upperConsistencyCoefficient s (latest (crossGram s y)) d upper := by
    change upperConsistencyCoefficient (rescaleWindow s (fun i => ‖s i‖⁻¹))
      (ss1Model (rescaleWindow s (fun i => ‖s i‖⁻¹))
        (rescaleWindow y (fun i => ‖s i‖⁻¹))) d upper = _
    rw [ss1Model_rescale, upperConsistencyCoefficient_rescale _ _ _
      (unitWindow_diagonal_unit s hs)]
    rfl
  dsimp only at hr ⊢
  rw [hlo, hhi] at hr
  exact hr

end
end krylov.XR
