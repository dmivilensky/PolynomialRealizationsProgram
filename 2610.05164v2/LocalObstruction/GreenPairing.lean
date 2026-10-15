import «2610.05164v2».LocalObstruction.GreenResolvent

/-!
Article: 2610.05164v2, Theorem 6.1.
A signed L1 direction defines a bounded linear diagonal functional on operators.
Use: `«2610.05164v2».LocalObstruction.green_gradient_integral_operator` feeds
`«2610.05164v2».LocalObstruction.green_density_gradient_scale_derivative` (green density gradient
scale derivative).
Proof chain: `«2610.05164v2».LocalObstruction.theorem_6_1` — 2610.05164v2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real «2610.05164v2».Continuum «2610.05164v2».Filters
open scoped InnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 /--
The stated quantitative bound `‖inner ℝ (feature x) (A (feature x))‖≤‖A‖`.

Use: `«2610.05164v2».LocalObstruction.feature_diagonal_integrable` uses this bound to establish
integrability of the displayed function: `Integrable (fun x => v x*inner ℝ (feature x) (A
(feature x)))`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.feature_norm` with the arguments
shown in the proof.
-/
theorem feature_diagonal_bound (A : FeatureOperator) (x : ℝ) :
    ‖inner ℝ (feature x) (A (feature x))‖≤‖A‖ := by
  calc
    _ ≤ ‖feature x‖*‖A (feature x)‖ := norm_inner_le_norm _ _
    _ ≤ ‖feature x‖*(‖A‖*‖feature x‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
    _ = _ := by rw [feature_norm];ring

 /--
Integrability of the displayed function: `Integrable (fun x => v x*inner ℝ (feature x) (A
(feature x)))`.

Use: `«2610.05164v2».LocalObstruction.featureDiagonal` uses this integrability result in the
displayed construction of `featureDiagonal`. Its inputs and component formulas are fixed by
that definition.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.bounded_forcing_integrable`,
`«2610.05164v2».Continuum.feature_continuous`,
`«2610.05164v2».LocalObstruction.feature_diagonal_bound` with the arguments shown in the proof.
-/
theorem feature_diagonal_integrable {v : ℝ → ℝ} (hv : Integrable v) (A : FeatureOperator) :
    Integrable (fun x => v x*inner ℝ (feature x) (A (feature x))) :=
  bounded_forcing_integrable hv
    (feature_continuous.inner (A.continuous.comp feature_continuous)).aestronglyMeasurable
    (feature_diagonal_bound A)

 /--
Constructs `featureDiagonalLinear` of type `FeatureOperator →ₗ[ℝ] ℝ` by the displayed record
fields. Data fields specify the construction; proof fields discharge its required properties.

Use: `«2610.05164v2».LocalObstruction.featureDiagonal` uses this definition in the displayed
construction of `featureDiagonal`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.
-/
def featureDiagonalLinear {v : ℝ → ℝ} (hv : Integrable v) : FeatureOperator →ₗ[ℝ] ℝ where
  toFun A := ∫ x,v x*inner ℝ (feature x) (A (feature x))
  map_add' A B := by
    simp only [add_apply,inner_add_right,mul_add]
    exact integral_add (feature_diagonal_integrable hv A) (feature_diagonal_integrable hv B)
  map_smul' a A := by
    simp only [smul_apply,real_inner_smul_right,smul_eq_mul]
    have he : (fun x => v x*(a*inner ℝ (feature x) (A (feature x))))=
        fun x => a*(v x*inner ℝ (feature x) (A (feature x))) := by funext x;ring
    rw [he,integral_const_mul]
    rfl

 /--
Defines `featureDiagonal` of type `FeatureOperator →L[ℝ] ℝ`. The displayed construction fixes
its component data; its proof fields enforce the listed compatibility properties.

Use: `«2610.05164v2».LocalObstruction.featureDiagonal_apply` uses this definition to establish
exact identity `featureDiagonal hv A=∫ x,v x*inner ℝ (feature x) (A (feature x))`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.
-/
def featureDiagonal {v : ℝ → ℝ} (hv : Integrable v) : FeatureOperator →L[ℝ] ℝ :=
  (featureDiagonalLinear hv).mkContinuous (∫ x,|v x|) (fun A => by
    apply (norm_integral_le_integral_norm _).trans
    rw [← integral_mul_const]
    apply integral_mono_ae (feature_diagonal_integrable hv A).norm (hv.norm.mul_const _)
    exact Filter.Eventually.of_forall (fun x => by
      dsimp only
      rw [norm_mul,Real.norm_eq_abs (v x)]
      exact mul_le_mul_of_nonneg_left (feature_diagonal_bound A x) (abs_nonneg _)))

 /--
Exact identity `featureDiagonal hv A=∫ x,v x*inner ℝ (feature x) (A (feature x))`.

Use: `«2610.05164v2».LocalObstruction.green_gradient_integral_operator` rewrites with this
identity to establish `(∫ x,greenScaleGradient s m x*v x)=
featureDiagonal hv (-((fullResolvent m s) ∘L ((1/2:ℝ) • densityOperator m) ∘L (fullResolvent m
s)))/2`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem featureDiagonal_apply {v : ℝ → ℝ} (hv : Integrable v) (A : FeatureOperator) :
    featureDiagonal hv A=∫ x,v x*inner ℝ (feature x) (A (feature x)) := rfl

 /--
Exact identity `(∫ x,greenKernel s m x x*v x)=featureDiagonal hv (fullResolvent m s)/2`.

Use: `«2610.05164v2».LocalObstruction.green_density_gradient_scale_derivative` rewrites with
this identity to establish the actual derivative at the stated point: `HasDerivAt (fun t : ℝ =>
t*(∫ x,greenKernel t m x x*v x)) (∫ x,(greenKernel s m x x+s*greenScaleGradient s m x)*v x) s`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem green_integral_operator {m v : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    (hc : Continuous m) {s : ℝ} (hs : 0≤s) (he : ∀ x,m (-x)=m x) (hv : Integrable v) :
    (∫ x,greenKernel s m x x*v x)=featureDiagonal hv (fullResolvent m s)/2 := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [featureDiagonal_apply,← integral_div]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [greenKernel_eq_resolventGreen hm hn hc hs he]
    unfold resolventGreen
    ring)

 /--
The precise assertion is `(∫ x,greenScaleGradient s m x*v x)= featureDiagonal hv
(-((fullResolvent m s) ∘L ((1/2:ℝ) • densityOperator m) ∘L (fullResolvent m s)))/2`.

Use: `«2610.05164v2».LocalObstruction.green_density_gradient_scale_derivative` rewrites with
this identity to establish the actual derivative at the stated point: `HasDerivAt (fun t : ℝ =>
t*(∫ x,greenKernel t m x x*v x)) (∫ x,(greenKernel s m x x+s*greenScaleGradient s m x)*v x) s`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem green_gradient_integral_operator {m v : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    (hc : Continuous m) {s : ℝ} (hs : 0≤s) (he : ∀ x,m (-x)=m x) (hv : Integrable v) :
    (∫ x,greenScaleGradient s m x*v x)=
      featureDiagonal hv (-((fullResolvent m s) ∘L ((1/2:ℝ) • densityOperator m) ∘L
        (fullResolvent m s)))/2 := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [featureDiagonal_apply,← integral_div]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [greenScaleGradient_operator hm hn hc hs he]
    simp only [neg_apply,ContinuousLinearMap.comp_apply,smul_apply,map_smul,
      inner_neg_right,real_inner_smul_right]
    rw [← fullResolvent_symmetric hm hn hs]
    ring)

end
end «2610.05164v2».LocalObstruction
