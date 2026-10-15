import «2610.05164v2».Primal.SpectralVariation
import «2610.05164v2».Primal.Contraction

/-!
Article: 2610.05164v2, Proposition 13.
Printed variation formulas and the analytic primal-family package.
Result: `«2610.05164v2».Primal.proposition_13` supplies the stated article conclusion.
-/
namespace «2610.05164v2».Primal
noncomputable section
open Set Real MeasureTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

/--
Defines `determinantGradient` of type `ℝ` by `-6*exp (-φ t)*(s*t^3*(2-t^3)/κ+ nonlinearFilter
hφ κ s t*reflectedNonlinearFilter hφ κ s t)/ (2+nonlinearFilter hφ κ s
t+reflectedNonlinearFilter hφ κ s t)`.

Use: `«2610.05164v2».Primal.determinant_comparison_diagonal` rewrites with this definition to
establish the precise assertion is `familyDeterminantComparison hψ hθ κ s a a t=
determinantGradient (affineProfile_continuous hψ hθ a) κ s t`.

Article: 2610.05164v2, Proposition 13 via
`«2610.05164v2».Primal.familyLogDeterminant_derivative_printed`.
-/
def determinantGradient {φ : ℝ → ℝ} (hφ : Continuous φ) (κ s t : ℝ) : ℝ :=
  -6*exp (-φ t)*(s*t^3*(2-t^3)/κ+
    nonlinearFilter hφ κ s t*reflectedNonlinearFilter hφ κ s t)/
    (2+nonlinearFilter hφ κ s t+reflectedNonlinearFilter hφ κ s t)

/--
Defines `traceGradient` of type `ℝ` by `3*exp (-φ t)*(2*linearFilter hφ κ
t*reflectedLinearFilter hφ κ t- t^3*(2-t^3)*(linearFilter hφ κ t+reflectedLinearFilter hφ κ
t))`.

Use: `«2610.05164v2».Primal.trace_comparison_diagonal` rewrites with this definition to
establish the precise assertion is `familyTraceComparison hψ hθ κ a a t= traceGradient
(affineProfile_continuous hψ hθ a) κ t`.

Article: 2610.05164v2, Proposition 13 via
`«2610.05164v2».Primal.familySquareTrace_derivative_printed`.
-/
def traceGradient {φ : ℝ → ℝ} (hφ : Continuous φ) (κ t : ℝ) : ℝ :=
  3*exp (-φ t)*(2*linearFilter hφ κ t*reflectedLinearFilter hφ κ t-
    t^3*(2-t^3)*(linearFilter hφ κ t+reflectedLinearFilter hφ κ t))

/--
The precise assertion is `familyDeterminantComparison hψ hθ κ s a a t= determinantGradient
(affineProfile_continuous hψ hθ a) κ s t`.

Use: `«2610.05164v2».Primal.familyLogDeterminant_derivative_printed` rewrites with this
identity to establish the actual Fréchet derivative: `HasFDerivAt (familyLogDeterminant hψ hθ
hκ s) (∫ t in (0:ℝ)..1,determinantGradient (affineProfile_continuous hψ hθ a) κ s t •
profileForm θ t) a`.

Article: 2610.05164v2, Proposition 13 via
`«2610.05164v2».Primal.familyLogDeterminant_derivative_printed`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.affineProfile_continuous`,
`«2610.05164v2».Primal.unitClamp_eq` with the arguments shown in the proof.
-/
theorem determinant_comparison_diagonal {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) (κ s : ℝ) (a : ι → ℝ)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    familyDeterminantComparison hψ hθ κ s a a t=
      determinantGradient (affineProfile_continuous hψ hθ a) κ s t := by
  -- Use the identities/estimates `«2610.05164v2».Primal.affineProfile_continuous`,
  -- `«2610.05164v2».Primal.unitClamp_eq` with the arguments shown in the proof.
  simp only [familyDeterminantComparison,familyNonlinearFilter,Bool.false_eq_true,
    ite_true,ite_false,unitClamp_eq ht,determinantGradient]
  rw [show 2+reflectedNonlinearFilter (affineProfile_continuous hψ hθ a) κ s t+
    nonlinearFilter (affineProfile_continuous hψ hθ a) κ s t=
    2+nonlinearFilter (affineProfile_continuous hψ hθ a) κ s t+
      reflectedNonlinearFilter (affineProfile_continuous hψ hθ a) κ s t by ring]
  rw [mul_comm (reflectedNonlinearFilter (affineProfile_continuous hψ hθ a) κ s t)]
  ring

/--
The precise assertion is `familyTraceComparison hψ hθ κ a a t= traceGradient
(affineProfile_continuous hψ hθ a) κ t`.

Use: `«2610.05164v2».Primal.familySquareTrace_derivative_printed` rewrites with this identity
to establish the actual Fréchet derivative: `HasFDerivAt (familySquareTrace hψ hθ hκ) (∫ t in
(0:ℝ)..1,traceGradient (affineProfile_continuous hψ hθ a) κ t • profileForm θ t) a`.

Article: 2610.05164v2, Proposition 13 via
`«2610.05164v2».Primal.familySquareTrace_derivative_printed`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.unitClamp_eq` with the arguments
shown in the proof.
-/
theorem trace_comparison_diagonal {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) (κ : ℝ) (a : ι → ℝ)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    familyTraceComparison hψ hθ κ a a t=
      traceGradient (affineProfile_continuous hψ hθ a) κ t := by
  simp only [familyTraceComparison,familyLinearFilter,Bool.false_eq_true,
    ite_true,ite_false,unitClamp_eq ht,traceGradient]
  ring

/--
Formula (53), as a full Frechet derivative rather than only its columns.

The actual Fréchet derivative: `HasFDerivAt (familyLogDeterminant hψ hθ hκ s) (∫ t in
(0:ℝ)..1,determinantGradient (affineProfile_continuous hψ hθ a) κ s t • profileForm θ t) a`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Proposition 13.

Proof: Use the identities/estimates `«2610.05164v2».Primal.unitClamp_eq`,
`«2610.05164v2».Primal.determinant_comparison_diagonal`,
`«2610.05164v2».Primal.familyLogDeterminant_derivative` with the arguments shown in the proof.
-/
theorem familyLogDeterminant_derivative_printed {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ s : ℝ}
    (hκ : 0<κ) (hs : 0≤s) (a : ι → ℝ) :
    HasFDerivAt (familyLogDeterminant hψ hθ hκ s)
      (∫ t in (0:ℝ)..1,determinantGradient (affineProfile_continuous hψ hθ a) κ s t •
        profileForm θ t) a := by
  -- Use the identities/estimates `«2610.05164v2».Primal.unitClamp_eq`,
  -- `«2610.05164v2».Primal.determinant_comparison_diagonal`,
  -- `«2610.05164v2».Primal.familyLogDeterminant_derivative` with the arguments shown in the
  -- proof.
  convert familyLogDeterminant_derivative hψ hθ hκ hs a using 1
  apply intervalIntegral.integral_congr
  intro t ht
  have hu : t∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  dsimp only
  rw [unitClamp_eq hu,determinant_comparison_diagonal hψ hθ κ s a hu]

/--
The square-trace formula (53), including the actual ground parameter.

The actual Fréchet derivative: `HasFDerivAt (familySquareTrace hψ hθ hκ) (∫ t in
(0:ℝ)..1,traceGradient (affineProfile_continuous hψ hθ a) κ t • profileForm θ t) a`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Proposition 13.

Proof: Use the identities/estimates `«2610.05164v2».Primal.unitClamp_eq`,
`«2610.05164v2».Primal.trace_comparison_diagonal`,
`«2610.05164v2».Primal.familySquareTrace_derivative` with the arguments shown in the proof.
-/
theorem familySquareTrace_derivative_printed {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ}
    (hκ : 0<κ) (a : ι → ℝ) :
    HasFDerivAt (familySquareTrace hψ hθ hκ)
      (∫ t in (0:ℝ)..1,traceGradient (affineProfile_continuous hψ hθ a) κ t •
        profileForm θ t) a := by
  -- Use the identities/estimates `«2610.05164v2».Primal.unitClamp_eq`,
  -- `«2610.05164v2».Primal.trace_comparison_diagonal`,
  -- `«2610.05164v2».Primal.familySquareTrace_derivative` with the arguments shown in the
  -- proof.
  convert familySquareTrace_derivative hψ hθ hκ a using 1
  apply intervalIntegral.integral_congr
  intro t ht
  have hu : t∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  dsimp only
  rw [unitClamp_eq hu,trace_comparison_diagonal hψ hθ κ a hu]

/--
Every actual half-integer density moment has its actual parameter derivative.

The actual Fréchet derivative: `HasFDerivAt (fun a => ∫ x,(speedData (affineProfile ψ θ a)
(affineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2)) (∫ t in
(0:ℝ)..1,familyMomentKernelDerivative ψ θ κ j a t) a`.

Use: a standalone supporting Fréchet derivative formula for the article chain below; no
retained declaration currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 13.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem density_family_moment_derivative {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ)
    {j : ℕ} (hj : 0<j) (a : ι → ℝ) :
    HasFDerivAt (fun a => ∫ x,(speedData (affineProfile ψ θ a)
      (affineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))
      (∫ t in (0:ℝ)..1,familyMomentKernelDerivative ψ θ κ j a t) a := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  have he : (fun a => ∫ x,(speedData (affineProfile ψ θ a)
      (affineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))=familyMoment ψ θ κ j :=
    funext (fun a => (familyMoment_density hψ hθ hκ hj a).symm)
  rw [he]
  exact «2610.05164v2».Calculus.unit_parameter_integral_derivative
    (familyMomentKernel_continuous hψ hθ κ j)
    (familyMomentKernelDerivative_continuous hψ hθ hκ j)
    (fun a t _ => familyMomentKernel_derivative ψ θ hκ j a t) a

/--
Proposition 13, for continuous directions and hence for all polynomial families.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Proposition 13.

Proof: Use the identities/estimates `«2610.05164v2».Primal.density_family_moment_c1`,
`«2610.05164v2».Primal.familyLogDeterminant_c1`, `«2610.05164v2».Primal.familySquareTrace_c1`
with the arguments shown in the proof.
-/
theorem proposition_13 {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ) :
    (∀ j : ℕ,0<j → ContDiff ℝ 1 (fun a => ∫ x,(speedData (affineProfile ψ θ a)
      (affineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))) ∧
    (∀ s : ℝ,0≤s → ContDiff ℝ 1 (familyLogDeterminant hψ hθ hκ s)) ∧
    ContDiff ℝ 1 (familySquareTrace hψ hθ hκ) ∧
    ∀ a : ι → ℝ,
      (∫ x,(speedData (affineProfile ψ θ a) (affineProfile_continuous hψ hθ a)).density κ x^(3/2:ℝ))≤
      exp (‖a‖*∑ i,‖unitDirection (hθ i)‖)*(∫ x,(speedData ψ hψ).density κ x^(3/2:ℝ)) :=
  ⟨fun _ hj => density_family_moment_c1 hψ hθ hκ hj,
    fun _ hs => familyLogDeterminant_c1 hψ hθ hκ hs,familySquareTrace_c1 hψ hθ hκ,
    affine_family_energy_bound hψ hθ hκ⟩

end
end «2610.05164v2».Primal
