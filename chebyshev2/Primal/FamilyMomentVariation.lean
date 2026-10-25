import chebyshev2.Primal.MomentVariation
import chebyshev2.Calculus.FiniteParameterIntegral

/-!
Article: chebyshev2, Proposition 13.
Proposition 13's multivariable C1 moment statement for any finite family of continuous directions.
Use: `chebyshev2.Primal.density_family_moment_c1` feeds `chebyshev2.Primal.proposition_13`
(Proposition 13, for continuous directions and hence for all polynomial families).
Proof chain: `chebyshev2.Primal.familyConstraintMap_c1` — chebyshev2, Theorem 5.2; Contraction
implies exact feasible density, uniqueness, iteration error and energy bound.
-/
namespace chebyshev2.Primal
noncomputable section
open Set Real MeasureTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

/--
Defines `affineProfile` of type `ℝ` by `ψ t+∑ i,a i*θ i t`.

Use: `chebyshev2.Primal.affineProfile_continuous` uses this definition to establish
continuity of the displayed function: `Continuous (affineProfile ψ θ a)`.

Article: chebyshev2, Theorem 5.2 via
`chebyshev2.Primal.exact_primal_family_of_contraction`.
-/
def affineProfile (ψ : ℝ → ℝ) (θ : ι → ℝ → ℝ) (a : ι → ℝ) (t : ℝ) : ℝ :=
  ψ t+∑ i,a i*θ i t

/--
Defines `profileForm` of type `(ι → ℝ) →L[ℝ] ℝ` by `∑ i,(θ i t) • ContinuousLinearMap.proj i`.

Use: `chebyshev2.Primal.familyMomentKernelDerivative` uses this definition in the displayed
construction of `familyMomentKernelDerivative`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def profileForm (θ : ι → ℝ → ℝ) (t : ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i,(θ i t) • ContinuousLinearMap.proj i

/--
Exact identity `profileForm θ t a=∑ i,a i*θ i t`.

Use: `chebyshev2.Primal.familyMomentKernel_derivative` uses this identity to establish the
actual Fréchet derivative: `HasFDerivAt (fun a => familyMomentKernel ψ θ κ j a t)
(familyMomentKernelDerivative ψ θ κ j a t) a`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem profileForm_apply (θ : ι → ℝ → ℝ) (t : ℝ) (a : ι → ℝ) :
    profileForm θ t a=∑ i,a i*θ i t := by
  simp only [profileForm,sum_apply,smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,mul_comm]

/--
Continuity of the displayed function: `Continuous (affineProfile ψ θ a)`.

Use: `chebyshev2.Primal.density_family_moment_c1` uses this continuity result to establish
smoothness to the stated order: `ContDiff ℝ 1 (fun a => ∫ x,(speedData (affineProfile ψ θ a)
(affineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))`.

Article: chebyshev2, Theorem 5.2 via
`chebyshev2.Primal.exact_primal_family_of_contraction`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem affineProfile_continuous {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) (a : ι → ℝ) :
    Continuous (affineProfile ψ θ a) := by
  unfold affineProfile
  fun_prop

/--
Defines `unitClamp` of type `ℝ` by `max 0 (min 1 t)`.

Use: `chebyshev2.Primal.familyMomentKernel` uses this definition in the displayed
construction of `familyMomentKernel`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def unitClamp (t : ℝ) : ℝ := max 0 (min 1 t)

/--
Membership in the specified domain/enclosure: `unitClamp t∈Icc (0:ℝ) 1`.

Use: `chebyshev2.Primal.familyMomentKernelDerivative_continuous` uses this assertion to
establish continuity of the displayed function: `Continuous (familyMomentKernelDerivative ψ θ κ
j).uncurry`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem unitClamp_mem (t : ℝ) : unitClamp t∈Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩

/--
Exact identity `unitClamp t=t`.

Use: `chebyshev2.Primal.familyMoment_density` rewrites with this identity to establish the
precise assertion is `familyMoment ψ θ κ j a= ∫ x,(speedData (affineProfile ψ θ a)
(affineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem unitClamp_eq {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : unitClamp t=t := by simp only [unitClamp,min_eq_right ht.2,max_eq_right ht.1]

/--
Continuity of the displayed function: `Continuous unitClamp`.

Use: `chebyshev2.Primal.familyMomentKernelDerivative_continuous` uses this continuity
result to establish continuity of the displayed function: `Continuous
(familyMomentKernelDerivative ψ θ κ j).uncurry`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[fun_prop] theorem unitClamp_continuous : Continuous unitClamp := by
  unfold unitClamp
  fun_prop

/--
Defines `scalarMoment` of type `ℝ` by `momentIntegrand (fun _ => y) κ j t`.

Use: `chebyshev2.Primal.familyMomentKernel` uses this definition in the displayed
construction of `familyMomentKernel`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def scalarMoment (κ : ℝ) (j : ℕ) (t y : ℝ) : ℝ := momentIntegrand (fun _ => y) κ j t
/--
Defines `scalarMomentDerivative` of type `ℝ` by `momentVariationIntegrand (fun _ => 0) (fun _
=> 1) κ j y t`.

Use: `chebyshev2.Primal.familyMomentKernelDerivative` uses this definition in the displayed
construction of `familyMomentKernelDerivative`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def scalarMomentDerivative (κ : ℝ) (j : ℕ) (t y : ℝ) : ℝ :=
  momentVariationIntegrand (fun _ => 0) (fun _ => 1) κ j y t

/--
Exact identity `lineProfile (fun _ => 0) (fun _ => 1) y=fun _ => y`.

Use: `chebyshev2.Primal.familyMomentKernelDerivative_continuous` rewrites with this
identity to establish continuity of the displayed function: `Continuous
(familyMomentKernelDerivative ψ θ κ j).uncurry`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem lineProfile_zero_one (y : ℝ) : lineProfile (fun _ => 0) (fun _ => 1) y=fun _ => y := by
  funext t
  simp only [lineProfile,mul_one,zero_add]

/--
The actual derivative at the stated point: `HasDerivAt (scalarMoment κ j t)
(scalarMomentDerivative κ j t y) y`.

Use: `chebyshev2.Primal.familyMomentKernel_derivative` uses this derivative formula to
establish the actual Fréchet derivative: `HasFDerivAt (fun a => familyMomentKernel ψ θ κ j a t)
(familyMomentKernelDerivative ψ θ κ j a t) a`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem scalarMoment_derivative {κ t : ℝ} (hκ : 0<κ) (ht : t∈Icc (0:ℝ) 1)
    (j : ℕ) (y : ℝ) : HasDerivAt (scalarMoment κ j t) (scalarMomentDerivative κ j t y) y := by
  unfold scalarMoment scalarMomentDerivative
  convert! momentIntegrand_directional_derivative (fun _ => 0) (fun _ => 1) hκ ht j y using 1
  funext a
  simp only [momentIntegrand,normalizedAmplitude,lineProfile,zero_add,mul_one]

/--
Defines `familyMomentKernel` of type `ℝ` by `scalarMoment κ j (unitClamp t) (affineProfile ψ θ
a (unitClamp t))`.

Use: `chebyshev2.Primal.familyMoment` uses this definition in the displayed construction of
`familyMoment`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def familyMomentKernel (ψ : ℝ → ℝ) (θ : ι → ℝ → ℝ) (κ : ℝ) (j : ℕ)
    (a : ι → ℝ) (t : ℝ) : ℝ :=
  scalarMoment κ j (unitClamp t) (affineProfile ψ θ a (unitClamp t))

/--
Defines `familyMomentKernelDerivative` of type `(ι → ℝ) →L[ℝ] ℝ` by `scalarMomentDerivative κ j
(unitClamp t) (affineProfile ψ θ a (unitClamp t)) • profileForm θ (unitClamp t)`.

Use: `chebyshev2.Primal.familyMomentKernelDerivative_continuous` uses this definition to
establish continuity of the displayed function: `Continuous (familyMomentKernelDerivative ψ θ κ
j).uncurry`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def familyMomentKernelDerivative (ψ : ℝ → ℝ) (θ : ι → ℝ → ℝ) (κ : ℝ) (j : ℕ)
    (a : ι → ℝ) (t : ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  scalarMomentDerivative κ j (unitClamp t) (affineProfile ψ θ a (unitClamp t)) •
    profileForm θ (unitClamp t)

/--
The actual Fréchet derivative: `HasFDerivAt (fun a => familyMomentKernel ψ θ κ j a t)
(familyMomentKernelDerivative ψ θ κ j a t) a`.

Use: `chebyshev2.Primal.familyMoment_c1` uses this Fréchet derivative formula to establish
smoothness to the stated order: `ContDiff ℝ 1 (familyMoment ψ θ κ j)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Primal.profileForm_apply`,
`chebyshev2.Primal.scalarMoment_derivative`, `chebyshev2.Primal.unitClamp_mem` with the
arguments shown in the proof.
-/
theorem familyMomentKernel_derivative (ψ : ℝ → ℝ) (θ : ι → ℝ → ℝ)
    {κ : ℝ} (hκ : 0<κ) (j : ℕ) (a : ι → ℝ) (t : ℝ) :
    HasFDerivAt (fun a => familyMomentKernel ψ θ κ j a t)
      (familyMomentKernelDerivative ψ θ κ j a t) a := by
  -- Use the identities/estimates `chebyshev2.Primal.profileForm_apply`,
  -- `chebyshev2.Primal.scalarMoment_derivative`, `chebyshev2.Primal.unitClamp_mem`
  -- with the arguments shown in the proof.
  have hφ : HasFDerivAt (fun a => affineProfile ψ θ a (unitClamp t))
      (profileForm θ (unitClamp t)) a := by
    simpa only [affineProfile,profileForm_apply] using
      ((profileForm θ (unitClamp t)).hasFDerivAt).const_add (ψ (unitClamp t))
  simpa only [familyMomentKernel,familyMomentKernelDerivative,Function.comp_def] using
    (scalarMoment_derivative hκ (unitClamp_mem t) j (affineProfile ψ θ a (unitClamp t))).comp_hasFDerivAt a hφ

/--
Continuity of the displayed function: `Continuous (familyMomentKernel ψ θ κ j).uncurry`.

Use: `chebyshev2.Primal.familyMoment_c1` uses this continuity result to establish
smoothness to the stated order: `ContDiff ℝ 1 (familyMoment ψ θ κ j)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem familyMomentKernel_continuous {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) (κ : ℝ) (j : ℕ) :
    Continuous (familyMomentKernel ψ θ κ j).uncurry := by
  unfold familyMomentKernel scalarMoment momentIntegrand normalizedAmplitude affineProfile unitClamp
  fun_prop

/--
Continuity of the displayed function: `Continuous (familyMomentKernelDerivative ψ θ κ
j).uncurry`.

Use: `chebyshev2.Primal.familyMoment_c1` uses this continuity result to establish
smoothness to the stated order: `ContDiff ℝ 1 (familyMoment ψ θ κ j)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem familyMomentKernelDerivative_continuous {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ) (j : ℕ) :
    Continuous (familyMomentKernelDerivative ψ θ κ j).uncurry := by
  -- Establish continuity hφ before using the function at limits or in calculus arguments.
  have hφ : Continuous (fun p : (ι → ℝ) × ℝ => affineProfile ψ θ p.1 (unitClamp p.2)) := by
    unfold affineProfile unitClamp
    fun_prop
  -- Establish continuity hz before using the function at limits or in calculus arguments.
  have hz : Continuous (fun p : (ι → ℝ) × ℝ =>
      normalizedAmplitude (fun _ => affineProfile ψ θ p.1 (unitClamp p.2)) κ (unitClamp p.2)) := by
    unfold normalizedAmplitude unitClamp
    fun_prop
  have hden : ∀ p : (ι → ℝ) × ℝ,
      2*normalizedAmplitude (fun _ => affineProfile ψ θ p.1 (unitClamp p.2)) κ (unitClamp p.2)≠0 :=
    fun p => (mul_pos (by norm_num) (normalizedAmplitude_positive_on _ hκ (unitClamp_mem p.2))).ne'
  have hquot := ((Real.continuous_exp.comp hφ).div_const κ).div (hz.const_mul 2) hden
  -- Establish continuity hform before using the function at limits or in calculus arguments.
  have hform : Continuous (fun t => profileForm θ (unitClamp t)) := by
    unfold profileForm unitClamp
    fun_prop
  unfold familyMomentKernelDerivative scalarMomentDerivative momentVariationIntegrand Function.uncurry
  dsimp only [lineProfile]
  simp only [zero_add,mul_one]
  -- Establish continuity hlead before using the function at limits or in calculus arguments.
  have hlead : Continuous (fun p : (ι → ℝ) × ℝ =>
      6*exp (-affineProfile ψ θ p.1 (unitClamp p.2))*(unitClamp p.2)^j) := by
    fun_prop
  convert! (hlead.mul ((hz.pow j).neg.add (((hz.pow (j-1)).const_mul (j:ℝ)).mul hquot))).smul
    (hform.comp continuous_snd) using 1
  funext p
  ext v
  simp [lineProfile_zero_one]

/--
Defines `familyMoment` of type `ℝ` by `∫ t in (0:ℝ)..1,familyMomentKernel ψ θ κ j a t`.

Use: `chebyshev2.Primal.density_family_moment_c1` uses this definition to establish
smoothness to the stated order: `ContDiff ℝ 1 (fun a => ∫ x,(speedData (affineProfile ψ θ a)
(affineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def familyMoment (ψ : ℝ → ℝ) (θ : ι → ℝ → ℝ) (κ : ℝ) (j : ℕ) (a : ι → ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1,familyMomentKernel ψ θ κ j a t

/--
Smoothness to the stated order: `ContDiff ℝ 1 (familyMoment ψ θ κ j)`.

Use: `chebyshev2.Primal.density_family_moment_c1` uses this assertion to establish
smoothness to the stated order: `ContDiff ℝ 1 (fun a => ∫ x,(speedData (affineProfile ψ θ a)
(affineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Calculus.unit_parameter_integral_c1`,
`chebyshev2.Primal.familyMomentKernel_continuous`,
`chebyshev2.Primal.familyMomentKernelDerivative_continuous` with the arguments shown in the
proof.
-/
theorem familyMoment_c1 {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ) (j : ℕ) :
    ContDiff ℝ 1 (familyMoment ψ θ κ j) :=
  chebyshev2.Calculus.unit_parameter_integral_c1 (familyMomentKernel_continuous hψ hθ κ j)
    (familyMomentKernelDerivative_continuous hψ hθ hκ j)
    (fun a t _ => familyMomentKernel_derivative ψ θ hκ j a t)

/--
The precise assertion is `familyMoment ψ θ κ j a= ∫ x,(speedData (affineProfile ψ θ a)
(affineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2)`.

Use: `chebyshev2.Primal.density_family_moment_c1` uses this identity to establish
smoothness to the stated order: `ContDiff ℝ 1 (fun a => ∫ x,(speedData (affineProfile ψ θ a)
(affineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Primal.affineProfile_continuous`,
`chebyshev2.Primal.density_moment_cubic`, `chebyshev2.Primal.unitClamp_eq` with the
arguments shown in the proof.
-/
theorem familyMoment_density {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ)
    {j : ℕ} (hj : 0<j) (a : ι → ℝ) :
    familyMoment ψ θ κ j a=
      ∫ x,(speedData (affineProfile ψ θ a) (affineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2) := by
  -- Use the identities/estimates `chebyshev2.Primal.affineProfile_continuous`,
  -- `chebyshev2.Primal.density_moment_cubic`, `chebyshev2.Primal.unitClamp_eq` with
  -- the arguments shown in the proof.
  rw [density_moment_cubic (affineProfile_continuous hψ hθ a) hκ hj]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  simp only [familyMomentKernel,scalarMoment,unitClamp_eq ht',momentIntegrand,normalizedAmplitude]

/--
Smoothness to the stated order: `ContDiff ℝ 1 (fun a => ∫ x,(speedData (affineProfile ψ θ a)
(affineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))`.

Use: `chebyshev2.Primal.familyObservation_c1` uses this identity to establish smoothness to
the stated order: `ContDiff ℝ 1 (familyObservation hψ hθ hκ observation)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem density_family_moment_c1 {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ)
    {j : ℕ} (hj : 0<j) :
    ContDiff ℝ 1 (fun a => ∫ x,(speedData (affineProfile ψ θ a)
      (affineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2)) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have he : (fun a => ∫ x,(speedData (affineProfile ψ θ a)
      (affineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))=familyMoment ψ θ κ j :=
    funext (fun a => (familyMoment_density hψ hθ hκ hj a).symm)
  rw [he]
  exact familyMoment_c1 hψ hθ hκ j

end
end chebyshev2.Primal
