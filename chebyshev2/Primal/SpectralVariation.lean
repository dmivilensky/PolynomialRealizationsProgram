import chebyshev2.Primal.FamilyFilterContinuity
import chebyshev2.Primal.TraceComparisonRegular
import chebyshev2.Calculus.FiniteComparisonDerivative

/-!
Article: chebyshev2, Proposition 13.
Proposition 13: actual spectral observations of a finite primal family are C1.
Use: `chebyshev2.Primal.familySquareTrace_c1` feeds `chebyshev2.Primal.proposition_13`
(Proposition 13, for continuous directions and hence for all polynomial families).
Proof chain: `chebyshev2.Primal.familyConstraintMap_c1` — chebyshev2, Theorem 5.2; Contraction
implies exact feasible density, uniqueness, iteration error and energy bound.
-/
namespace chebyshev2.Primal
noncomputable section
open Set Real MeasureTheory chebyshev2.Continuum chebyshev2.Filters
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

/--
Defines `familyLogDeterminant` of type `ℝ` by `logDeterminant (kernelEigenvalue ((speedData _
(affineProfile_continuous hψ hθ a)).density_integrable hκ) ((speedData _
(affineProfile_continuous hψ hθ a)).density_nonneg hκ)) s`.

Use: `chebyshev2.Primal.familyLogDeterminant_comparison` rewrites with this definition to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def familyLogDeterminant {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ)
    (s : ℝ) (a : ι → ℝ) : ℝ :=
  logDeterminant (kernelEigenvalue
    ((speedData _ (affineProfile_continuous hψ hθ a)).density_integrable hκ)
    ((speedData _ (affineProfile_continuous hψ hθ a)).density_nonneg hκ)) s

/--
Defines `familySquareTrace` of type `ℝ` by `κ^2/4*∑' j,(kernelEigenvalue ((speedData _
(affineProfile_continuous hψ hθ a)).density_integrable hκ) ((speedData _
(affineProfile_continuous hψ hθ a)).density_nonneg hκ) j)^2`.

Use: `chebyshev2.Primal.familySquareTrace_integral` uses this definition to establish the
precise assertion is `familySquareTrace hψ hθ hκ a= ∫ x,(κ*causal 2 ((speedData _
(affineProfile_continuous hψ hθ a)).density κ) x)^2`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def familySquareTrace {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ)
    (a : ι → ℝ) : ℝ :=
  κ^2/4*∑' j,(kernelEigenvalue
    ((speedData _ (affineProfile_continuous hψ hθ a)).density_integrable hκ)
    ((speedData _ (affineProfile_continuous hψ hθ a)).density_nonneg hκ) j)^2

/--
Defines `familyDeterminantComparison` of type `ℝ`. The displayed construction fixes its
component data; its proof fields enforce the listed compatibility properties.

Use: `chebyshev2.Primal.familyLogDeterminant_comparison` rewrites with this definition to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def familyDeterminantComparison {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) (κ s : ℝ)
    (a b : ι → ℝ) (t : ℝ) : ℝ :=
  let u := unitClamp t
  let l := familyNonlinearFilter hψ hθ κ s false a t
  let r := familyNonlinearFilter hψ hθ κ s true b t
  let lMirror := familyNonlinearFilter hψ hθ κ s true a t
  let rMirror := familyNonlinearFilter hψ hθ κ s false b t
  (-3:ℝ)*exp (-affineProfile ψ θ b u)*
    ((s*u^3*(2-u^3)/κ+l*r)/(2+l+r)+(s*u^3*(2-u^3)/κ+lMirror*rMirror)/(2+lMirror+rMirror))

/--
Defines `familyTraceComparison` of type `ℝ`. The displayed construction fixes its component
data; its proof fields enforce the listed compatibility properties.

Use: `chebyshev2.Primal.familySquareTrace_comparison` rewrites with this definition to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def familyTraceComparison {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) (κ : ℝ)
    (a b : ι → ℝ) (t : ℝ) : ℝ :=
  let u := unitClamp t
  let l := familyLinearFilter hψ hθ κ false a t
  let r := familyLinearFilter hψ hθ κ true b t
  let lMirror := familyLinearFilter hψ hθ κ true a t
  let rMirror := familyLinearFilter hψ hθ κ false b t
  (3/2:ℝ)*exp (-affineProfile ψ θ b u)*
    (2*l*r-u^3*(2-u^3)*(l+r)+2*lMirror*rMirror-u^3*(2-u^3)*(lMirror+rMirror))

/--
The stated quantitative bound `0≤familyNonlinearFilter hψ hθ κ s r a t`.

Use: `chebyshev2.Primal.familyDeterminantComparison_continuous` uses this bound to
establish continuity of the displayed function: `Continuous (fun p : (ι → ℝ) × (ι → ℝ) × ℝ =>
familyDeterminantComparison hψ hθ κ s p.1 p.2.1 p.2.2)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Primal.nonlinearFilter_nonneg`,
`chebyshev2.Primal.affineProfile_continuous`,
`chebyshev2.Primal.reflectedNonlinearFilter_nonneg` with the arguments shown in the proof.
-/
theorem familyNonlinearFilter_nonneg {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ s : ℝ}
    (hκ : 0<κ) (hs : 0≤s) (r : Bool) (a : ι → ℝ) (t : ℝ) :
    0≤familyNonlinearFilter hψ hθ κ s r a t := by
  cases r with
  | false => exact nonlinearFilter_nonneg (affineProfile_continuous hψ hθ a) hκ hs _
  | true => exact reflectedNonlinearFilter_nonneg (affineProfile_continuous hψ hθ a) hκ hs _

/--
Continuity of the displayed function: `Continuous (fun p : (ι → ℝ) × (ι → ℝ) × ℝ =>
familyDeterminantComparison hψ hθ κ s p.1 p.2.1 p.2.2)`.

Use: `chebyshev2.Primal.familyLogDeterminant_c1` uses this continuity result to establish
smoothness to the stated order: `ContDiff ℝ 1 (familyLogDeterminant hψ hθ hκ s)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates
`chebyshev2.Primal.familyNonlinearFilter_joint_continuous`,
`chebyshev2.Primal.familyNonlinearFilter_nonneg` with the arguments shown in the proof.
-/
theorem familyDeterminantComparison_continuous {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ s : ℝ}
    (hκ : 0<κ) (hs : 0≤s) :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) × ℝ =>
      familyDeterminantComparison hψ hθ κ s p.1 p.2.1 p.2.2) := by
  -- Establish continuity hL before using the function at limits or in calculus arguments.
  have hL (r : Bool) : Continuous (fun p : (ι → ℝ) × (ι → ℝ) × ℝ =>
      familyNonlinearFilter hψ hθ κ s r p.1 p.2.2) :=
    (familyNonlinearFilter_joint_continuous hψ hθ hκ hs r).comp (f:=fun p : (ι → ℝ) × (ι → ℝ) × ℝ => (p.1,p.2.2))
      (continuous_fst.prodMk continuous_snd.snd)
  -- Establish continuity hR before using the function at limits or in calculus arguments.
  have hR (r : Bool) : Continuous (fun p : (ι → ℝ) × (ι → ℝ) × ℝ =>
      familyNonlinearFilter hψ hθ κ s r p.2.1 p.2.2) :=
    (familyNonlinearFilter_joint_continuous hψ hθ hκ hs r).comp (f:=fun p : (ι → ℝ) × (ι → ℝ) × ℝ => p.2) continuous_snd
  have hden (r rMirror : Bool) (p : (ι → ℝ) × (ι → ℝ) × ℝ) :
      2+familyNonlinearFilter hψ hθ κ s r p.1 p.2.2+
        familyNonlinearFilter hψ hθ κ s rMirror p.2.1 p.2.2≠0 := by
    linarith [familyNonlinearFilter_nonneg hψ hθ hκ hs r p.1 p.2.2,
      familyNonlinearFilter_nonneg hψ hθ hκ hs rMirror p.2.1 p.2.2]
  -- Establish continuity hφ before using the function at limits or in calculus arguments.
  have hφ : Continuous (fun p : (ι → ℝ) × (ι → ℝ) × ℝ =>
      affineProfile ψ θ p.2.1 (unitClamp p.2.2)) := by
    unfold affineProfile
    fun_prop
  -- Establish continuity hQ before using the function at limits or in calculus arguments.
  have hQ : Continuous (fun p : (ι → ℝ) × (ι → ℝ) × ℝ =>
      s*(unitClamp p.2.2)^3*(2-(unitClamp p.2.2)^3)/κ) := by fun_prop
  exact (((Real.continuous_exp.comp hφ.neg).const_mul (-3)).mul
    (((hQ.add ((hL false).mul (hR true))).div
      ((continuous_const.add (hL false)).add (hR true)) (hden false true)).add
    ((hQ.add ((hL true).mul (hR false))).div
      ((continuous_const.add (hL true)).add (hR false)) (hden true false))))

/--
Continuity of the displayed function: `Continuous (fun p : (ι → ℝ) × (ι → ℝ) × ℝ =>
familyTraceComparison hψ hθ κ p.1 p.2.1 p.2.2)`.

Use: `chebyshev2.Primal.familySquareTrace_c1` uses this continuity result to establish
smoothness to the stated order: `ContDiff ℝ 1 (familySquareTrace hψ hθ hκ)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Primal.familyLinearFilter_joint_continuous`
with the arguments shown in the proof.
-/
theorem familyTraceComparison_continuous {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ) :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) × ℝ =>
      familyTraceComparison hψ hθ κ p.1 p.2.1 p.2.2) := by
  -- Establish continuity hL before using the function at limits or in calculus arguments.
  have hL (r : Bool) : Continuous (fun p : (ι → ℝ) × (ι → ℝ) × ℝ =>
      familyLinearFilter hψ hθ κ r p.1 p.2.2) :=
    (familyLinearFilter_joint_continuous hψ hθ hκ r).comp (f:=fun p : (ι → ℝ) × (ι → ℝ) × ℝ => (p.1,p.2.2))
      (continuous_fst.prodMk continuous_snd.snd)
  -- Establish continuity hR before using the function at limits or in calculus arguments.
  have hR (r : Bool) : Continuous (fun p : (ι → ℝ) × (ι → ℝ) × ℝ =>
      familyLinearFilter hψ hθ κ r p.2.1 p.2.2) :=
    (familyLinearFilter_joint_continuous hψ hθ hκ r).comp (f:=fun p : (ι → ℝ) × (ι → ℝ) × ℝ => p.2) continuous_snd
  -- Establish continuity hφ before using the function at limits or in calculus arguments.
  have hφ : Continuous (fun p : (ι → ℝ) × (ι → ℝ) × ℝ =>
      affineProfile ψ θ p.2.1 (unitClamp p.2.2)) := by
    unfold affineProfile
    fun_prop
  -- Establish continuity hQ before using the function at limits or in calculus arguments.
  have hQ : Continuous (fun p : (ι → ℝ) × (ι → ℝ) × ℝ =>
      (unitClamp p.2.2)^3*(2-(unitClamp p.2.2)^3)) := by fun_prop
  have hleft := (((hL false).const_mul 2).mul (hR true)).sub
    (hQ.mul ((hL false).add (hR true)))
  have hboth := (hleft.add (((hL true).const_mul 2).mul (hR false))).sub
    (hQ.mul ((hL true).add (hR false)))
  exact ((Real.continuous_exp.comp hφ.neg).const_mul (3/2)).mul hboth

/--
The precise assertion is `affineProfile ψ θ b t-affineProfile ψ θ a t= -profileForm θ t (a-b)`.

Use: `chebyshev2.Primal.familyLogDeterminant_comparison` rewrites with this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Primal.profileForm_apply` with the
arguments shown in the proof.
-/
theorem affineProfile_difference_form (ψ : ℝ → ℝ) (θ : ι → ℝ → ℝ)
    (a b : ι → ℝ) (t : ℝ) :
    affineProfile ψ θ b t-affineProfile ψ θ a t= -profileForm θ t (a-b) := by
  rw [profileForm_apply]
  unfold affineProfile
  simp only [Pi.sub_apply,sub_mul,Finset.sum_sub_distrib]
  ring

/--
The precise assertion is `familyLogDeterminant hψ hθ hκ s a-familyLogDeterminant hψ hθ hκ s b=
∫ t in (0:ℝ)..1,familyDeterminantComparison hψ hθ κ s a b t*
chebyshev2.Calculus.exponentialIncrement (profileForm θ (unitClamp t)) b a`.

Use: `chebyshev2.Primal.familyLogDeterminant_c1` uses this identity to establish smoothness
to the stated order: `ContDiff ℝ 1 (familyLogDeterminant hψ hθ hκ s)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Primal.affineProfile_continuous`,
`chebyshev2.Primal.determinant_profile_difference_cubic`,
`chebyshev2.Primal.affineProfile_difference_form` with the arguments shown in the proof.
-/
theorem familyLogDeterminant_comparison {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ s : ℝ}
    (hκ : 0<κ) (hs : 0≤s) (a b : ι → ℝ) :
    familyLogDeterminant hψ hθ hκ s a-familyLogDeterminant hψ hθ hκ s b=
      ∫ t in (0:ℝ)..1,familyDeterminantComparison hψ hθ κ s a b t*
        chebyshev2.Calculus.exponentialIncrement (profileForm θ (unitClamp t)) b a := by
  -- Use the identities/estimates `chebyshev2.Primal.affineProfile_continuous`,
  -- `chebyshev2.Primal.determinant_profile_difference_cubic`,
  -- `chebyshev2.Primal.affineProfile_difference_form` with the arguments shown in the
  -- proof.
  rw [familyLogDeterminant,familyLogDeterminant,determinant_profile_difference_cubic
    (affineProfile_continuous hψ hθ a) (affineProfile_continuous hψ hθ b) hκ hs]
  apply intervalIntegral.integral_congr
  intro t ht
  have hu : t∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  simp only [familyDeterminantComparison,chebyshev2.Calculus.exponentialIncrement,
    familyNonlinearFilter,Bool.false_eq_true,ite_true,ite_false,unitClamp_eq hu,
    determinantDifferenceCore,determinantDifferenceReflectedCore,
    affineProfile_difference_form]
  ring

/--
The precise assertion is `familySquareTrace hψ hθ hκ a= ∫ x,(κ*causal 2 ((speedData _
(affineProfile_continuous hψ hθ a)).density κ) x)^2`.

Use: `chebyshev2.Primal.familySquareTrace_comparison` rewrites with this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Primal.affineProfile_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
proof.
-/
theorem familySquareTrace_integral {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ) (a : ι → ℝ) :
    familySquareTrace hψ hθ hκ a=
      ∫ x,(κ*causal 2 ((speedData _ (affineProfile_continuous hψ hθ a)).density κ) x)^2 := by
  -- Use the identities/estimates `chebyshev2.Primal.affineProfile_continuous`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
  -- proof.
  have h := linear_square_trace
    ((speedData _ (affineProfile_continuous hψ hθ a)).density_integrable hκ)
    ((speedData _ (affineProfile_continuous hψ hθ a)).density_nonneg hκ)
  rw [(speedData _ (affineProfile_continuous hψ hθ a)).groundParameter_density hκ] at h
  simpa only [familySquareTrace,linear,
    (speedData _ (affineProfile_continuous hψ hθ a)).groundParameter_density hκ] using h.symm

/--
The precise assertion is `familySquareTrace hψ hθ hκ a-familySquareTrace hψ hθ hκ b= ∫ t in
(0:ℝ)..1,familyTraceComparison hψ hθ κ a b t* chebyshev2.Calculus.exponentialIncrement
(profileForm θ (unitClamp t)) b a`.

Use: `chebyshev2.Primal.familySquareTrace_c1` uses this identity to establish smoothness to
the stated order: `ContDiff ℝ 1 (familySquareTrace hψ hθ hκ)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Primal.affineProfile_continuous`,
`chebyshev2.Primal.familySquareTrace_integral`,
`chebyshev2.Primal.trace_profile_difference_cubic` with the arguments shown in the proof.
-/
theorem familySquareTrace_comparison {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ}
    (hκ : 0<κ) (a b : ι → ℝ) :
    familySquareTrace hψ hθ hκ a-familySquareTrace hψ hθ hκ b=
      ∫ t in (0:ℝ)..1,familyTraceComparison hψ hθ κ a b t*
        chebyshev2.Calculus.exponentialIncrement (profileForm θ (unitClamp t)) b a := by
  -- Use the identities/estimates `chebyshev2.Primal.affineProfile_continuous`,
  -- `chebyshev2.Primal.familySquareTrace_integral`,
  -- `chebyshev2.Primal.trace_profile_difference_cubic` with the arguments shown in the
  -- proof.
  rw [familySquareTrace_integral hψ hθ hκ a,familySquareTrace_integral hψ hθ hκ b,
    trace_profile_difference_cubic (affineProfile_continuous hψ hθ a)
      (affineProfile_continuous hψ hθ b) hκ]
  apply intervalIntegral.integral_congr
  intro t ht
  have hu : t∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  simp only [familyTraceComparison,chebyshev2.Calculus.exponentialIncrement,
    familyLinearFilter,Bool.false_eq_true,ite_true,ite_false,unitClamp_eq hu,
    traceDifferenceCore,traceDifferenceReflectedCore,affineProfile_difference_form]
  ring

/--
Continuity of the displayed function: `Continuous (fun t => profileForm θ (unitClamp t))`.

Use: `chebyshev2.Primal.familyLogDeterminant_c1` uses this continuity result to establish
smoothness to the stated order: `ContDiff ℝ 1 (familyLogDeterminant hψ hθ hκ s)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem profileForm_clamped_continuous {θ : ι → ℝ → ℝ} (hθ : ∀ i,Continuous (θ i)) :
    Continuous (fun t => profileForm θ (unitClamp t)) := by
  unfold profileForm
  fun_prop

/--
The actual Fréchet derivative: `HasFDerivAt (familyLogDeterminant hψ hθ hκ s) (∫ t in
(0:ℝ)..1,familyDeterminantComparison hψ hθ κ s a a t • profileForm θ (unitClamp t)) a`.

Use: `chebyshev2.Primal.familyLogDeterminant_derivative_printed` uses this Fréchet
derivative formula to establish the actual Fréchet derivative: `HasFDerivAt
(familyLogDeterminant hψ hθ hκ s) (∫ t in (0:ℝ)..1,determinantGradient
(affineProfile_continuous hψ hθ a) κ s t • profileForm θ t) a`.

Article: chebyshev2, Proposition 13 via
`chebyshev2.Primal.familyLogDeterminant_derivative_printed`.

Proof: Use the identities/estimates `chebyshev2.Calculus.finite_comparison_derivative`,
`chebyshev2.Primal.familyDeterminantComparison_continuous`,
`chebyshev2.Primal.profileForm_clamped_continuous` with the arguments shown in the proof.
-/
theorem familyLogDeterminant_derivative {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ s : ℝ}
    (hκ : 0<κ) (hs : 0≤s) (a : ι → ℝ) :
    HasFDerivAt (familyLogDeterminant hψ hθ hκ s)
      (∫ t in (0:ℝ)..1,familyDeterminantComparison hψ hθ κ s a a t •
        profileForm θ (unitClamp t)) a :=
  chebyshev2.Calculus.finite_comparison_derivative
    (familyDeterminantComparison_continuous hψ hθ hκ hs) (profileForm_clamped_continuous hθ)
    (familyLogDeterminant_comparison hψ hθ hκ hs) a

/--
Smoothness to the stated order: `ContDiff ℝ 1 (familyLogDeterminant hψ hθ hκ s)`.

Use: `chebyshev2.Primal.familyObservation_c1` uses this assertion to establish smoothness
to the stated order: `ContDiff ℝ 1 (familyObservation hψ hθ hκ observation)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Calculus.finite_comparison_c1`,
`chebyshev2.Primal.familyDeterminantComparison_continuous`,
`chebyshev2.Primal.profileForm_clamped_continuous` with the arguments shown in the proof.
-/
theorem familyLogDeterminant_c1 {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ s : ℝ}
    (hκ : 0<κ) (hs : 0≤s) : ContDiff ℝ 1 (familyLogDeterminant hψ hθ hκ s) :=
  chebyshev2.Calculus.finite_comparison_c1
    (familyDeterminantComparison_continuous hψ hθ hκ hs) (profileForm_clamped_continuous hθ)
    (familyLogDeterminant_comparison hψ hθ hκ hs)

/--
The actual Fréchet derivative: `HasFDerivAt (familySquareTrace hψ hθ hκ) (∫ t in
(0:ℝ)..1,familyTraceComparison hψ hθ κ a a t • profileForm θ (unitClamp t)) a`.

Use: `chebyshev2.Primal.familySquareTrace_derivative_printed` uses this Fréchet derivative
formula to establish the actual Fréchet derivative: `HasFDerivAt (familySquareTrace hψ hθ hκ)
(∫ t in (0:ℝ)..1,traceGradient (affineProfile_continuous hψ hθ a) κ t • profileForm θ t) a`.

Article: chebyshev2, Proposition 13 via
`chebyshev2.Primal.familySquareTrace_derivative_printed`.

Proof: Use the identities/estimates `chebyshev2.Calculus.finite_comparison_derivative`,
`chebyshev2.Primal.familyTraceComparison_continuous`,
`chebyshev2.Primal.profileForm_clamped_continuous` with the arguments shown in the proof.
-/
theorem familySquareTrace_derivative {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ}
    (hκ : 0<κ) (a : ι → ℝ) :
    HasFDerivAt (familySquareTrace hψ hθ hκ)
      (∫ t in (0:ℝ)..1,familyTraceComparison hψ hθ κ a a t •
        profileForm θ (unitClamp t)) a :=
  chebyshev2.Calculus.finite_comparison_derivative
    (familyTraceComparison_continuous hψ hθ hκ) (profileForm_clamped_continuous hθ)
    (familySquareTrace_comparison hψ hθ hκ) a

/--
Smoothness to the stated order: `ContDiff ℝ 1 (familySquareTrace hψ hθ hκ)`.

Use: `chebyshev2.Primal.familyObservation_c1` uses this assertion to establish smoothness
to the stated order: `ContDiff ℝ 1 (familyObservation hψ hθ hκ observation)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Calculus.finite_comparison_c1`,
`chebyshev2.Primal.familyTraceComparison_continuous`,
`chebyshev2.Primal.profileForm_clamped_continuous` with the arguments shown in the proof.
-/
theorem familySquareTrace_c1 {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ}
    (hκ : 0<κ) : ContDiff ℝ 1 (familySquareTrace hψ hθ hκ) :=
  chebyshev2.Calculus.finite_comparison_c1
    (familyTraceComparison_continuous hψ hθ hκ) (profileForm_clamped_continuous hθ)
    (familySquareTrace_comparison hψ hθ hκ)

end
end chebyshev2.Primal
