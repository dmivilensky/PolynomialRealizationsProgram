import krylov.OneGradient.InformedPriorNormalization
import krylov.OneGradient.KnownBaseAsymptoticUpper
import krylov.OneGradient.InformedPhysicalLeading
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), original physical sharpness metric squeeze.
Use: true known-frame output coefficients transfer to the original source
ratio with its own metric and exact own CG-error normalization.
Source: actual physical prior Loewner domination, exact prior norm formula
and genuine dual-norm comparison, retaining the actual native output vector.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset krylov.Reference krylov.Secant krylov.Information
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual original risk on the genuine physical prior family is
squeezed between its true known-metric normalized risk times sqrt(1+c*t)
and that same quantity divided by 1+c*t. Both factors tend to one.
Use: exact known-frame actual output sharpness gives original source-own
sharpness without assuming moving-axis alignment or a metric limit.
Article: main_krylov, thm:local(b), genuine physical own-risk squeeze.
Proof: the actual prior base dominates the known base and is at most
(1+c*t) times it. Genuine dual-norm comparisons bound the same real output
in both metrics. Its actual own penultimate error is exactly sigma/sqrt(1+c*t).
Divide these proved positive real inequalities, retaining the true output. -/
theorem informedPhysicalScenario_risk_squeeze_basis (directions : Bool)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (D : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (c t : ℝ) (hc0 : 0≤c) (ht : 0<t) (hct : c*t<1) :
    let S := informedPhysicalScenario A hA g hg hc D F c t
    let known := ‖cgOperator (metricRoot A)⁻¹ (informedScenarioOutput directions A g S)‖/
      (t^2*‖cgCanonicalError A g n‖)
    Real.sqrt (1+c*t)/(1+c*t)*known≤ informedSourceRisk directions A g S t ∧
      informedSourceRisk directions A g S t≤Real.sqrt (1+c*t)*known := by
  dsimp only
  let S := informedPhysicalScenario A hA g hg hc D F c t
  let B := informedPriorBase A hA g hg hc (c*t)
  let out := informedScenarioOutput directions A g S
  let sigma := ‖cgCanonicalError A g n‖
  let f := 1+c*t
  let b := Real.sqrt f
  let N := ‖cgOperator (metricRoot A)⁻¹ out‖
  let O := ‖cgOperator (metricRoot B)⁻¹ out‖
  have hct0 : 0≤c*t := mul_nonneg hc0 ht.le
  have hB := informedPriorBase_posDef A hA g hg hc (c*t) hct0
  have hsigma : 0<sigma := krylov.Stability.canonical_error_pos A hA
    (CG.gradient (cgOperator A) g n) (cg_nonstagnation A hA g n (by rw [full_gradient_atom_count A hA g hc];omega))
  have hf : 0<f := by dsimp only [f];linarith
  have hb : 0<b := Real.sqrt_pos.mpr hf
  have hden : 0<t^2*sigma := mul_pos (sq_pos_of_pos ht) hsigma
  have hdom := informedPriorBase_domination A hA g hg hc (c*t) hct0
  have hupper : B≤f • A := (relative_displacement_base A B hA hB.1.isSymm hct0 hct
    (informedPriorBase_budget A hA g hg hc (c*t) hct0).le).2.1
  have hO : O≤N := by
    have h := dual_norm_le_of_base_upper B A hB hA (le_refl (1 : ℝ))
      (by simpa only [one_smul] using hdom) out
    simpa only [one_mul] using h
  have hN : N≤f*O := dual_norm_le_of_base_upper A B hA hB (by dsimp only [f];linarith) hupper out
  have hnormalize : ‖cgCanonicalError B g n‖=sigma/b :=
    informedPriorBase_error_norm A hA g hg hc (c*t) hct0
  have hrisk : informedSourceRisk directions A g S t=(b*O)/(t^2*sigma) := by
    change O/(t^2*‖cgCanonicalError B g n‖)=_
    rw [hnormalize]
    field_simp
  change (b/f)*(N/(t^2*sigma))≤ informedSourceRisk directions A g S t ∧
    informedSourceRisk directions A g S t≤b*(N/(t^2*sigma))
  rw [hrisk]
  constructor
  · have hmul := mul_le_mul_of_nonneg_left hN (div_nonneg hb.le hf.le)
    have hcancel : (b/f)*(f*O)=b*O := by field_simp [hf.ne']
    rw [hcancel] at hmul
    have h := div_le_div_of_nonneg_right hmul hden.le
    simpa only [mul_div_assoc] using h
  · have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hO hb.le) hden.le
    simpa only [mul_div_assoc] using h

/-- The original S specialization of the common native-basis theorem.
Use: preserve the established step-policy physical source interface.
Article: main_krylov, thm:local(b).
Proof: specialize the shared genuine physical theorem to the S basis. -/
theorem informedPhysicalScenario_risk_squeeze
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (D : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (c t : ℝ) (hc0 : 0≤c) (ht : 0<t) (hct : c*t<1) :
    let S := informedPhysicalScenario A hA g hg hc D F c t
    let known := ‖cgOperator (metricRoot A)⁻¹ (informedScenarioOutput false A g S)‖/
      (t^2*‖cgCanonicalError A g n‖)
    Real.sqrt (1+c*t)/(1+c*t)*known≤ informedSourceRisk false A g S t ∧
      informedSourceRisk false A g S t≤Real.sqrt (1+c*t)*known  := by
  exact informedPhysicalScenario_risk_squeeze_basis false A hA g hg hc D F c t hc0 ht hct

end
end krylov.OneGradient
