import krylov.OneGradient.ObservedPriorAttainment
import krylov.OneGradient.SpectralUniformMinimax
set_option autoImplicit false
/-!
Article: main_krylov, cor:quant(a), literal prior-wide harmonic fibre rule.
Use: connect the original known-prior observed rule to the true physical
information endpoints and exact coefficient on every spectral-prior fibre.
Source: actual attained physical spectral interval, original observed-prior
harmonic dictionary and the proved strict original spectral coefficient bound.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Methods krylov.Secant

/-- The original known spectral matrix class in physical coordinates.
Use: the same class predicate enters one history-only rule for all references.
Article: main_krylov, cor:quant(a). -/
def spectralPriorSet (m : ℕ) (mu upper : ℝ) : Set (Matrix (Fin m) (Fin m) ℝ) :=
  {A | (A-mu • 1).PosSemidef ∧ (upper • 1-A).PosSemidef}

/-- Either actual XRFC basis with the literal single observed-prior harmonic
rule on the original known spectral class.
Use: its final trial is read from the actual transcript's entire compatible
physical fibre, with no reference-dependent endpoints captured in the method.
Article: main_krylov, cor:quant(a). -/
def spectralPriorHarmonicMethod (directions : Bool) (n : ℕ) (mu upper : ℝ)
    (earlier : History (EuclideanSpace ℝ (Fin (n+2))) → ℝ) : OneGradientMethod (EuclideanSpace ℝ (Fin (n+2))) :=
  xrfcBasisMethod directions (observedPriorLastTrial (n+1) (spectralPriorSet (n+2) mu upper) earlier)

/-- The one original observed-prior policy attains each true physical fibre's
exact harmonic coefficient, simultaneously on the entire known spectral class.
Use: its coefficient is strictly below the sharp uniform value on every
individual full-atom reference, while the actual irreducible family approaches it.
Article: main_krylov, cor:quant(a), literal harmonic fibrewise attainment.
Proof: true spectral feasibility gives the genuine physical endpoint interval
and positive lower pivot gap. The same prior-wide observed rule is its exact
harmonic trial; apply the genuine two-basis original-prior output theorem. -/
theorem spectral_observed_harmonic_fibre_upper (directions : Bool) {mu upper : ℝ}
    (hmu : 0 < mu) {n : ℕ} (P : SpectralPriorReference n mu upper)
    (earlier : History (EuclideanSpace ℝ (Fin (n+2))) → ℝ) (he : ∀ H,0 < earlier H)
    {omega : ℝ} (homega : 0≤omega) (b : ℝ)
    (hlo : (lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b-mu • 1).PosSemidef)
    (hhi : (upper • 1-lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b).PosSemidef)
    (B : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hB : B.IsSymm)
    (hbudget : relativeBudget (lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b)
      (B-lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b)≤omega) :
    fibreScenarioError P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support
      (spectralPriorHarmonicMethod directions n mu upper earlier) b B≤omega*spectralPriorCoefficient P := by
  let A := P.matrix
  let hA := P.positive
  let g := P.gradient
  let hg := P.gradient_ne_zero
  let hc := P.full_support
  let lo := spectralLowerPivot A hA g hg hc mu
  let hi := spectralUpperPivot A hA g hg hc upper
  obtain ⟨horder,hinterval⟩ := physical_spectral_fibre_interval A hA g hg hc mu upper (spectral_prior_nonempty_fibre P)
  have hgap := (spectral_fibre_endpoint_gaps A hA g hg hc mu upper hmu (spectral_prior_nonempty_fibre P)).1
  have hpositive : lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹ < lo := by linarith
  exact xrfc_observed_prior_fibre_upper directions A hA g hg hc (spectralPriorSet (n+2) mu upper) lo hi
    hpositive horder hinterval earlier he homega b ((hinterval b).mp ⟨hlo,hhi⟩) B hB hbudget

/-- The literal single observed-information harmonic rule is an admissible
attainer of the exact original uniform spectral minimum, in both native bases.
Use: it is chosen before all physical references, completions and outputs.
Article: main_krylov, cor:quant(a), single observed harmonic optimizer.
Proof: every actual fibre has the true harmonic bound, and each such original
coefficient lies strictly below the proved sharp global supremum. Actual
observed-span theorems give admissibility independently of the prior data. -/
theorem spectral_prior_observed_harmonic_attainment (directions : Bool) (mu upper : ℝ)
    (hmu : 0 < mu) (hmuL : mu < upper) (n : ℕ)
    (earlier : History (EuclideanSpace ℝ (Fin (n+2))) → ℝ) (he : ∀ H,0 < earlier H)
    {omega : ℝ} (homega : 0≤omega) :
    OneGradientSpanRestricted (spectralPriorHarmonicMethod directions n mu upper earlier) ∧
      spectralPriorGuarantee n mu upper omega (spectralPriorHarmonicMethod directions n mu upper earlier)
        (((upper-mu)/(upper+mu))*omega) := by
  constructor
  · cases directions with
    | false => exact xrfcMethod_spanRestricted fullMemory _
    | true => exact xrfcDMethod_spanRestricted fullMemory _
  · intro P b hlo hhi B hB hbudget
    have hout := spectral_observed_harmonic_fibre_upper directions hmu P earlier he homega b hlo hhi B hB hbudget
    have hc := mul_le_mul_of_nonneg_left (spectral_prior_coefficient_bounds hmu hmuL P).2.le homega
    exact hout.trans (by simpa only [mul_comm] using hc)

end
end krylov.OneGradient
