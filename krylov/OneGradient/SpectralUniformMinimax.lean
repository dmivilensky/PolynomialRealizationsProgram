import krylov.OneGradient.SpectralSharpSupremum
import krylov.OneGradient.XRFCUniformSpectral
import krylov.Methods.DirectionInformation
set_option autoImplicit false
/-!
Article: main_krylov, cor:quant(a), complete original uniform spectral minimax.
Use: take the minimum over actual data-only span-restricted methods and the
uniform guarantee over all real physical information fibres and output balls.
Source: the genuine arbitrary-method physical lower bound and one original
history-only observed harmonic XRFC policy attaining the upper bound.
-/

/-!
Article: krylov, Corollary C.8 [cor:quant].

IsLeast quantifies the method before all reference/scenario choices, with one actual history-
only harmonic policy attaining the spectral and relative-ball uniform guarantees.
The spectral reference supremum is strict for each irreducible reference. The relative-ball
centre supplies actual attained endpoint adversaries; zero output radius is included.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Methods krylov.Secant

/-- An original uniform guarantee over the entire physical spectral prior,
constant prefixes and all genuine unobserved output matrices.
Use: a single actual method is chosen before the reference, information
fibre, completion and output matrix.
Article: main_krylov, cor:quant(a). -/
def spectralPriorGuarantee (n : ℕ) (mu upper omega : ℝ)
    (method : OneGradientMethod (EuclideanSpace ℝ (Fin (n+2)))) (v : ℝ) : Prop :=
  ∀ P : SpectralPriorReference n mu upper,∀ b : ℝ,
    (lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b-mu • 1).PosSemidef →
    (upper • 1-lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b).PosSemidef →
    ∀ B : Matrix (Fin (n+2)) (Fin (n+2)) ℝ,B.IsSymm →
      relativeBudget (lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b)
        (B-lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b)≤omega →
      fibreScenarioError P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support method b B≤v

/-- Either actual XRFC basis with the one original observed spectral harmonic
rule has the uniform guarantee over every real original information fibre.
Use: arbitrary earlier positive observed decisions are allowed, and the
policy receives only the known endpoints and actual observed history.
Article: main_krylov, cor:quant(a), uniform original-prior attainment.
Proof: every admitted original completion is genuinely positive and retains
all actual active atoms. Apply the proved original physical output bound to
that real reference and its real output matrix. -/
theorem xrfc_spectral_prior_guarantee (directions : Bool) (mu upper : ℝ)
    (hmu : 0 < mu) (hmuL : mu≤upper) (n : ℕ)
    (earlier : History (EuclideanSpace ℝ (Fin (n+2))) → ℝ) (he : ∀ H,0 < earlier H)
    {omega : ℝ} (homega : 0≤omega) :
    spectralPriorGuarantee n mu upper omega (spectralXRFCMethod directions (n+1) mu upper earlier)
      (((upper-mu)/(upper+mu))*omega) := by
  intro P b hlo hhi B hB hbudget
  let C := lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b
  have hC : C.PosDef := spectral_fibre_completion_positive P.matrix P.positive P.gradient
    P.gradient_ne_zero P.full_support mu b hmu hlo
  have hcount : referenceAtomCount C hC P.gradient=(n+1)+1 :=
    completion_full_atoms P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b hC
  exact xrfc_spectral_output_upper directions C hC P.gradient (n+1) hcount mu upper hmu hmuL
    hlo hhi earlier he homega B hB hbudget

/-- The complete original uniform spectral one-gradient minimax value is
rho_kappa times the output radius, in every fixed dimension at least two.
Use: this is an actual attained minimum over a single original admissible
method chosen before all physical reference and scenario quantifiers.
Article: main_krylov, cor:quant(a).
Proof: the actual history-only harmonic XRFC policy supplies membership of
the achievable-guarantee set. Every competing span-restricted method is
bounded below by the genuine endpoint adversaries and real sharp family. -/
theorem spectral_prior_exact_uniform_minimax (mu upper : ℝ) (hmu : 0 < mu) (hmuL : mu < upper)
    (n : ℕ) {omega : ℝ} (homega : 0≤omega) (hsmall : omega≤1) :
    IsLeast {v : ℝ | ∃ method : OneGradientMethod (EuclideanSpace ℝ (Fin (n+2))),
      OneGradientSpanRestricted method ∧ spectralPriorGuarantee n mu upper omega method v}
      (((upper-mu)/(upper+mu))*omega) := by
  constructor
  · let method : OneGradientMethod (EuclideanSpace ℝ (Fin (n+2))) :=
      spectralXRFCMethod false (n+1) mu upper (fun _ => 1)
    refine ⟨method,xrfcMethod_spanRestricted fullMemory _,?_⟩
    exact xrfc_spectral_prior_guarantee false mu upper hmu hmuL.le n (fun _ => 1) (fun _ => zero_lt_one) homega
  · rintro v ⟨method,hm,hv⟩
    exact spectral_prior_method_uniform_lower mu upper hmu hmuL n method hm homega hsmall v hv

/-- Both implemented XRFC stored bases belong to the original one-gradient
span-restricted class and attain the same exact original uniform minimum.
Use: the concrete optimizer is reviewable in either source basis.
Article: main_krylov, cor:quant(a), two attaining implementations.
Proof: actual observed-span theorems apply to every history and every trial;
the original uniform upper theorem applies to the single observed policy. -/
theorem spectral_prior_two_basis_attainment (directions : Bool) (mu upper : ℝ)
    (hmu : 0 < mu) (hmuL : mu≤upper) (n : ℕ)
    (earlier : History (EuclideanSpace ℝ (Fin (n+2))) → ℝ) (he : ∀ H,0 < earlier H)
    {omega : ℝ} (homega : 0≤omega) :
    OneGradientSpanRestricted (spectralXRFCMethod directions (n+1) mu upper earlier) ∧
      spectralPriorGuarantee n mu upper omega (spectralXRFCMethod directions (n+1) mu upper earlier)
        (((upper-mu)/(upper+mu))*omega) := by
  constructor
  · cases directions with
    | false => exact xrfcMethod_spanRestricted fullMemory _
    | true => exact xrfcDMethod_spanRestricted fullMemory _
  · exact xrfc_spectral_prior_guarantee directions mu upper hmu hmuL n earlier he homega

end
end krylov.OneGradient
