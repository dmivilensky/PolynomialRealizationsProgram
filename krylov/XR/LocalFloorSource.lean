import krylov.XR.LocalSchurNormalization
import krylov.XR.LocalSelectedModel

/-!
Article: main_krylov, prop:floor and thm:XR, literal floored trial.
Use: derive all three G3 inequalities for the actual computed curvature
from primitive raw secant errors, incoming gain and a compact interval of
strict upper class bounds. The actual conjugacy and inverse domain are
derived from the observed data; no desired curvature or acceptance bound
is an input. Source: physical Radau completion and the actual adequacy floor.
-/

/-!
Article: krylov, Proposition F.10 [prop:floor].

The literal spectral curvature with its upper-only floor satisfies G3 under true local source
conditions and a strict upper spectral margin; quadratic upper clipping cannot increase trial
error.
This is a property of the spectral policy. The secant policy uses G3 as a hypothesis and does
not inherit this floor guarantee.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant krylov.Convergence krylov.Reference
open krylov.Methods hiding unitWindow unitWindow_norm unitWindow_diagonal_unit
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- One tolerance works for every actual raw partial window and every
running upper estimate in the fixed compact strict-upper interval. -/
theorem algorithmComputedCurvature_uniform_floor_radius
    (P : Parameters) (hP : P.Valid n)
    (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (a b lowerUpper upperUpper sigma : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : 0 < b) (hmargin : b < lowerUpper)
    (hsigma : 0 < sigma) (hsigma₁ : sigma ≤ 1)
    (hHlo : (base-a • 1).PosSemidef) (hHhi : (b • 1-base).PosSemidef)
    (hpositive : ∀ v : EuclideanSpace ℝ (Fin n), a*‖v‖^2 ≤ inner ℝ v (cgOperator base v))
    (hnorm : ‖cgOperator base‖ ≤ b) :
    ∃ radius > 0, ∀ (S : State (EuclideanSpace ℝ (Fin n))) (bounds : ℝ × ℝ),
      (algorithmModel P S).bounds = some bounds →
      lowerUpper ≤ bounds.2 → bounds.2 ≤ upperUpper →
      (∀ i, storedSteps (algorithmModel P S).pairs i ≠ 0) →
      (∀ w : Fin (algorithmModel P S).pairs.length → ℝ,
        sigma^2*‖WithLp.toLp 2 w‖^2 ≤
          ‖combine (unitWindow (storedSteps (algorithmModel P S).pairs)) w‖^2) →
      (∀ i, ‖storedImages (algorithmModel P S).pairs i -
        cgOperator base (storedSteps (algorithmModel P S).pairs i)‖ ≤
          radius * ‖storedSteps (algorithmModel P S).pairs i‖) →
      algorithmSelectedDirection P S ≠ 0 →
      let d := algorithmSelectedDirection P S
      (a/(2*(2*(1-P.armijo)-P.adequacyMargin)))*‖d‖^2 ≤ algorithmComputedCurvature P S ∧
        algorithmComputedCurvature P S ≤ upperUpper*‖d‖^2 ∧
        inner ℝ (cgOperator base d) d ≤
          (2*(1-P.armijo)-P.adequacyMargin/2)*algorithmComputedCurvature P S := by
  obtain ⟨rR, hrR, hR⟩ := radau_uniform_radius n (a/2) a b lowerUpper sigma ha hb hsigma
    (by linarith) hmargin
  let radius := min rR (a*sigma^2/(8*((n : ℝ)+1)))
  have hradius : 0 < radius := by dsimp only [radius]; positivity
  refine ⟨radius, hradius, ?_⟩
  intro S bounds hbounds hlow hupp hs hgain hy hd
  let W := (algorithmModel P S).pairs
  let d := algorithmSelectedDirection P S
  have hlen : W.length ≤ n := (algorithmModel_length_le P S).trans (min_le_right _ _)
  have hlenR : (W.length : ℝ) ≤ n := by exact_mod_cast hlen
  have hsmall : (W.length : ℝ)*radius ≤ a*sigma^2/4 := by
    have heps : radius ≤ a*sigma^2/(8*((n : ℝ)+1)) := min_le_right _ _
    have hh := (le_div_iff₀ (by positivity : 0 < 8*((n : ℝ)+1))).mp heps
    nlinarith [mul_le_mul_of_nonneg_right hlenR hradius.le]
  have hsym := (cgOperator_positive base hbase).1
  have hdom := local_raw_window_domains (cgOperator base) hsym (storedSteps W) (storedImages W)
    hs a sigma radius ha hsigma hradius.le hpositive hgain hy hsmall
  have hconj : ∀ i, inner ℝ (storedImages W i) d = 0 := by
    intro i
    exact congrFun (modelDirection_conjugate (storedSteps W) (storedImages W)
      (selectedModel P W) hdom.2.2.1 S.gradient) i
  have hRR := hR W.length hlen radius hradius.le (min_le_left _ _)
  have hRhi : (W.length+1 : ℕ)*radius < (bounds.2-b)*(a*sigma^2/(2*b)) :=
    hRR.2.2.trans_le (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hq := rawWindow_upper_consistency_adequate base hbase.isHermitian (storedSteps W) (storedImages W)
    hs d hd a b bounds.2 sigma radius ha hab (hmargin.trans_le hlow) hb hsigma hsigma₁ hradius.le
    hHlo hHhi hpositive hnorm hgain hy hconj hRR.1 hRR.2.1 hRhi
  let q := upperConsistencyCoefficient (storedSteps W) (storedModel W) d bounds.2
  have hqa : a ≤ q := hq.1
  have hq₀ : 0 < q := ha.trans_le hqa
  have hA : 1 ≤ 2*(1-P.armijo)-P.adequacyMargin := by
    have := hP.2.2.2.2.2.2.2.2.2.2.2
    linarith
  have hd₂ : 0 < ‖d‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
  let estimate :=
    let lo := lowerConsistencyCoefficient (storedSteps W) (storedModel W) d bounds.1
    let mid := (lo+q)/2
    (if lo ≤ q then mid else min (max mid bounds.1) bounds.2)*‖d‖^2
  have hc : algorithmComputedCurvature P S =
      adequacyFloor P.armijo P.adequacyMargin q (‖d‖^2) estimate := by
    unfold algorithmComputedCurvature
    dsimp only
    rw [hbounds]
    change observedTrialCurvature P W (storedModel W) d bounds = _
    exact ite_eq_left hq₀
  rw [hc]
  have hbnd := adequacyFloor_spectral_bounds hA ha (by linarith : a/2 ≤ q)
    (hq.2.2.trans hupp) hd₂.le estimate
  have hmem := adequacyFloor_mem hA hq₀.le hd₂.le estimate
  have hfloor₀ : 0 ≤ adequacyFloor P.armijo P.adequacyMargin q (‖d‖^2) estimate :=
    (by positivity : 0 ≤ (a/(2*(2*(1-P.armijo)-P.adequacyMargin)))*‖d‖^2).trans hbnd.1
  have hfloor : q*‖d‖^2 ≤ (2*(1-P.armijo)-P.adequacyMargin)*
      adequacyFloor P.armijo P.adequacyMargin q (‖d‖^2) estimate := by
    simpa only [mul_comm] using
      (div_le_iff₀ (by linarith : 0 < 2*(1-P.armijo)-P.adequacyMargin)).mp hmem.1
  refine ⟨hbnd.1, hbnd.2, ?_⟩
  have hcurv : inner ℝ d (cgOperator base d) ≤ q*‖d‖^2 := hq.2.1
  rw [real_inner_comm] at hcurv
  have heta : 0 < P.adequacyMargin := hP.2.2.2.2.2.2.2.2.2.2.1
  nlinarith [mul_nonneg heta.le hfloor₀]

end
end krylov.XR
