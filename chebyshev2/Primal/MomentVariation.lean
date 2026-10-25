import chebyshev2.Primal.Moments
import chebyshev2.Calculus.ScalarParameterIntegral

/-!
Article: chebyshev2, Proposition 13.
Proposition 13: differentiation of the actual two masses and energy along any continuous profile
direction.
Result: `chebyshev2.Primal.sqrt_mass_directional_derivative` supplies the stated article
conclusion.
-/
namespace chebyshev2.Primal
noncomputable section
open Set Real MeasureTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `lineProfile` of type `ℝ` by `ψ t+a*θ t`.

Use: `chebyshev2.Primal.mass_variation_integrand` uses this definition to establish the
precise assertion is `momentVariationIntegrand ψ θ κ 2 a t= -6*exp (-lineProfile ψ θ a
t)*t^3*(2-t^3)/κ*θ t`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def lineProfile (ψ θ : ℝ → ℝ) (a t : ℝ) : ℝ := ψ t+a*θ t

/--
Continuity of the displayed function: `Continuous (lineProfile ψ θ a)`.

Use: `chebyshev2.Primal.moment_directional_c1` uses this continuity result to establish
smoothness to the stated order: `ContDiff ℝ 1 (fun a => ∫ x,(speedData (lineProfile ψ θ a)
(lineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))`.

Article: chebyshev2, Proposition 13 via `chebyshev2.Primal.mass_directional_derivative`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem lineProfile_continuous {ψ θ : ℝ → ℝ} (hψ : Continuous ψ) (hθ : Continuous θ)
    (a : ℝ) : Continuous (lineProfile ψ θ a) := hψ.add (hθ.const_mul a)

/--
Defines `momentIntegrand` of type `ℝ` by `6*exp (-φ t)*t^j*(normalizedAmplitude φ κ t)^j`.

Use: `chebyshev2.Primal.moment_directional_c1` uses this definition to establish smoothness
to the stated order: `ContDiff ℝ 1 (fun a => ∫ x,(speedData (lineProfile ψ θ a)
(lineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def momentIntegrand (φ : ℝ → ℝ) (κ : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  6*exp (-φ t)*t^j*(normalizedAmplitude φ κ t)^j

/--
Defines `momentVariationIntegrand` of type `ℝ` by `let φ := lineProfile ψ θ a let z :=
normalizedAmplitude φ κ t 6*exp (-φ t)*t^j*(-z^j+(j:ℝ)*z^(j-1)*(exp (φ t)/κ/(2*z)))*θ t`.

Use: `chebyshev2.Primal.momentIntegrand_directional_derivative` uses this definition to
establish the actual derivative at the stated point: `HasDerivAt (fun a => momentIntegrand
(lineProfile ψ θ a) κ j t) (momentVariationIntegrand ψ θ κ j a t) a`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def momentVariationIntegrand (ψ θ : ℝ → ℝ) (κ : ℝ) (j : ℕ) (a t : ℝ) : ℝ :=
  let φ := lineProfile ψ θ a
  let z := normalizedAmplitude φ κ t
  6*exp (-φ t)*t^j*(-z^j+(j:ℝ)*z^(j-1)*(exp (φ t)/κ/(2*z)))*θ t

/--
The stated quantitative bound `0<normalizedAmplitude φ κ t`.

Use: `chebyshev2.Primal.mass_variation_integrand` uses this bound to establish the precise
assertion is `momentVariationIntegrand ψ θ κ 2 a t= -6*exp (-lineProfile ψ θ a
t)*t^3*(2-t^3)/κ*θ t`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem normalizedAmplitude_positive_on (φ : ℝ → ℝ) {κ t : ℝ} (hκ : 0<κ)
    (ht : t∈Icc (0:ℝ) 1) : 0<normalizedAmplitude φ κ t := by
  have ht3 : t^3≤1 := pow_le_one₀ ht.1 ht.2
  unfold normalizedAmplitude
  exact sqrt_pos.mpr (div_pos (add_pos_of_pos_of_nonneg (exp_pos _)
    (mul_nonneg ht.1 (by linarith))) hκ)

/--
The actual derivative at the stated point: `HasDerivAt (fun a => momentIntegrand (lineProfile ψ
θ a) κ j t) (momentVariationIntegrand ψ θ κ j a t) a`.

Use: `chebyshev2.Primal.moment_directional_c1` uses this derivative formula to establish
smoothness to the stated order: `ContDiff ℝ 1 (fun a => ∫ x,(speedData (lineProfile ψ θ a)
(lineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem momentIntegrand_directional_derivative (ψ θ : ℝ → ℝ) {κ t : ℝ}
    (hκ : 0<κ) (ht : t∈Icc (0:ℝ) 1) (j : ℕ) (a : ℝ) :
    HasDerivAt (fun a => momentIntegrand (lineProfile ψ θ a) κ j t)
      (momentVariationIntegrand ψ θ κ j a t) a := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hφ : HasDerivAt (fun a => lineProfile ψ θ a t) (θ t) a := by
    simpa only [lineProfile,one_mul,id_eq] using ((hasDerivAt_id a).mul_const (θ t)).const_add (ψ t)
  have hz := ((hφ.exp.add_const (t*(2-t^3))).div_const κ).sqrt
    (ne_of_gt (by
      have ht3 : t^3≤1 := pow_le_one₀ ht.1 ht.2
      exact div_pos (add_pos_of_pos_of_nonneg (exp_pos _)
        (mul_nonneg ht.1 (by linarith))) hκ))
  have h := (((hφ.neg.exp.const_mul 6).mul_const (t^j)).mul (hz.pow j))
  convert! h using 1
  dsimp only [momentVariationIntegrand,normalizedAmplitude,Pi.neg_apply,Pi.pow_apply]
  ring

/--
Continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => momentVariationIntegrand ψ θ κ
j p.1 p.2) (univ ×ˢ Icc (0:ℝ) 1)`.

Use: `chebyshev2.Primal.moment_directional_c1` uses this continuity result to establish
smoothness to the stated order: `ContDiff ℝ 1 (fun a => ∫ x,(speedData (lineProfile ψ θ a)
(lineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))`.

Article: chebyshev2, Proposition 13 via `chebyshev2.Primal.mass_directional_derivative`.

Proof: Use the identities/estimates `chebyshev2.Primal.normalizedAmplitude_positive_on`
with the arguments shown in the proof.
-/
theorem momentVariationIntegrand_joint_continuous {ψ θ : ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : Continuous θ) {κ : ℝ} (hκ : 0<κ) (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => momentVariationIntegrand ψ θ κ j p.1 p.2)
      (univ ×ˢ Icc (0:ℝ) 1) := by
  -- Establish continuity hφ before using the function at limits or in calculus arguments.
  have hφ : Continuous (fun p : ℝ × ℝ => lineProfile ψ θ p.1 p.2) := by
    unfold lineProfile
    fun_prop
  -- Establish continuity hz before using the function at limits or in calculus arguments.
  have hz : Continuous (fun p : ℝ × ℝ => normalizedAmplitude (lineProfile ψ θ p.1) κ p.2) := by
    unfold normalizedAmplitude
    fun_prop
  -- Establish continuity hquot before using the function at limits or in calculus arguments.
  have hquot : ContinuousOn (fun p : ℝ × ℝ =>
      exp (lineProfile ψ θ p.1 p.2)/κ/(2*normalizedAmplitude (lineProfile ψ θ p.1) κ p.2))
      (univ ×ˢ Icc (0:ℝ) 1) :=
    ((Real.continuous_exp.comp hφ).div_const κ).continuousOn.div (hz.const_mul 2).continuousOn
      (fun p hp => (mul_pos (by norm_num) (normalizedAmplitude_positive_on _ hκ hp.2)).ne')
  unfold momentVariationIntegrand
  -- Establish continuity hlead before using the function at limits or in calculus arguments.
  have hlead : Continuous (fun p : ℝ × ℝ => 6*exp (-lineProfile ψ θ p.1 p.2)*p.2^j) := by
    fun_prop
  exact (hlead.continuousOn.mul ((hz.pow j).neg.continuousOn.add
    (((hz.pow (j-1)).const_mul (j:ℝ)).continuousOn.mul hquot))).mul
      (hθ.comp continuous_snd).continuousOn

/--
The actual derivative at the stated point: `HasDerivAt (fun a => ∫ x,(speedData (lineProfile ψ
θ a) (lineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2)) (∫ t in
(0:ℝ)..1,momentVariationIntegrand ψ θ κ j a t) a`.

Use: `chebyshev2.Primal.mass_directional_derivative` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt (fun a => ∫ x,(speedData
(lineProfile ψ θ a) (lineProfile_continuous hψ hθ a)).density κ x) (∫ t in (0:ℝ)..1,-6*exp
(-lineProfile ψ θ a t)*t^3*(2-t^3)/κ*θ t) a`.

Article: chebyshev2, Proposition 13 via `chebyshev2.Primal.mass_directional_derivative`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem moment_directional_derivative {ψ θ : ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : Continuous θ) {κ : ℝ} (hκ : 0<κ)
    {j : ℕ} (hj : 0<j) (a : ℝ) :
    HasDerivAt (fun a => ∫ x,(speedData (lineProfile ψ θ a)
      (lineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))
      (∫ t in (0:ℝ)..1,momentVariationIntegrand ψ θ κ j a t) a := by
  -- Establish continuity hF before using the function at limits or in calculus arguments.
  have hF : ContinuousOn (fun p : ℝ × ℝ =>
      momentIntegrand (lineProfile ψ θ p.1) κ j p.2) (univ ×ˢ Icc (0:ℝ) 1) := by
    apply Continuous.continuousOn
    unfold momentIntegrand normalizedAmplitude lineProfile
    fun_prop
  have h := chebyshev2.Calculus.scalar_unit_integral_derivative hF
    (momentVariationIntegrand_joint_continuous hψ hθ hκ j)
    (fun a t ht => momentIntegrand_directional_derivative ψ θ hκ ht j a) a
  have he : (fun a => ∫ x,(speedData (lineProfile ψ θ a)
      (lineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))=
      fun a => ∫ t in (0:ℝ)..1,momentIntegrand (lineProfile ψ θ a) κ j t := by
    funext a
    exact density_moment_cubic (lineProfile_continuous hψ hθ a) hκ hj
  rw [he]
  exact h

/--
Smoothness to the stated order: `ContDiff ℝ 1 (fun a => ∫ x,(speedData (lineProfile ψ θ a)
(lineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 13.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem moment_directional_c1 {ψ θ : ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : Continuous θ) {κ : ℝ} (hκ : 0<κ)
    {j : ℕ} (hj : 0<j) :
    ContDiff ℝ 1 (fun a => ∫ x,(speedData (lineProfile ψ θ a)
      (lineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2)) := by
  -- Establish continuity hF before using the function at limits or in calculus arguments.
  have hF : ContinuousOn (fun p : ℝ × ℝ =>
      momentIntegrand (lineProfile ψ θ p.1) κ j p.2) (univ ×ˢ Icc (0:ℝ) 1) := by
    apply Continuous.continuousOn
    unfold momentIntegrand normalizedAmplitude lineProfile
    fun_prop
  have h := chebyshev2.Calculus.scalar_unit_integral_c1 hF
    (momentVariationIntegrand_joint_continuous hψ hθ hκ j)
    (fun a t ht => momentIntegrand_directional_derivative ψ θ hκ ht j a)
  have he : (fun a => ∫ x,(speedData (lineProfile ψ θ a)
      (lineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))=
      fun a => ∫ t in (0:ℝ)..1,momentIntegrand (lineProfile ψ θ a) κ j t := by
    funext a
    exact density_moment_cubic (lineProfile_continuous hψ hθ a) hκ hj
  rwa [he]

/--
Exact identity `(normalizedAmplitude φ κ t)^2=(exp (φ t)+t*(2-t^3))/κ`.

Use: `chebyshev2.Primal.mass_variation_integrand` uses this identity to establish the
precise assertion is `momentVariationIntegrand ψ θ κ 2 a t= -6*exp (-lineProfile ψ θ a
t)*t^3*(2-t^3)/κ*θ t`.

Article: chebyshev2, Proposition 13 via `chebyshev2.Primal.mass_directional_derivative`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem normalizedAmplitude_square_on (φ : ℝ → ℝ) {κ t : ℝ} (hκ : 0<κ)
    (ht : t∈Icc (0:ℝ) 1) :
    (normalizedAmplitude φ κ t)^2=(exp (φ t)+t*(2-t^3))/κ := by
  have ht3 : t^3≤1 := pow_le_one₀ ht.1 ht.2
  exact sq_sqrt (div_nonneg (add_nonneg (exp_pos _).le
    (mul_nonneg ht.1 (by linarith))) hκ.le)

/--
The first formula in (52), with its nonsingular cubic-coordinate kernel.

The precise assertion is `momentVariationIntegrand ψ θ κ 2 a t= -6*exp (-lineProfile ψ θ a
t)*t^3*(2-t^3)/κ*θ t`.

Use: `chebyshev2.Primal.mass_directional_derivative` uses this identity to establish the
actual derivative at the stated point: `HasDerivAt (fun a => ∫ x,(speedData (lineProfile ψ θ a)
(lineProfile_continuous hψ hθ a)).density κ x) (∫ t in (0:ℝ)..1,-6*exp (-lineProfile ψ θ a
t)*t^3*(2-t^3)/κ*θ t) a`.

Article: chebyshev2, Proposition 13 via `chebyshev2.Primal.mass_directional_derivative`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem mass_variation_integrand (ψ θ : ℝ → ℝ) {κ t : ℝ} (hκ : 0<κ)
    (ht : t∈Icc (0:ℝ) 1) (a : ℝ) :
    momentVariationIntegrand ψ θ κ 2 a t=
      -6*exp (-lineProfile ψ θ a t)*t^3*(2-t^3)/κ*θ t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  let φ := lineProfile ψ θ a
  let z := normalizedAmplitude φ κ t
  have hz : 0<z := normalizedAmplitude_positive_on φ hκ ht
  have hcancel : 2*z*(exp (φ t)/κ/(2*z))=exp (φ t)/κ := by
    field_simp
  have hs : z^2=(exp (φ t)+t*(2-t^3))/κ := normalizedAmplitude_square_on φ hκ ht
  change 6*exp (-φ t)*t^2*(-z^2+(2:ℝ)*z^(2-1)*(exp (φ t)/κ/(2*z)))*θ t=_
  norm_num only [show 2-1=1 by rfl,pow_one]
  rw [hcancel,hs]
  dsimp [φ]
  ring

/--
The second formula in (52), after cancellation of the apparent t=0 singularity.

The precise assertion is `momentVariationIntegrand ψ θ κ 1 a t= -3*exp (-lineProfile ψ θ a
t)*t* (exp (lineProfile ψ θ a t)+2*t*(2-t^3))/ (κ*normalizedAmplitude (lineProfile ψ θ a) κ
t)*θ t`.

Use: `chebyshev2.Primal.sqrt_mass_directional_derivative` uses this identity to establish
the derivative formula stated in that declaration.

Article: chebyshev2, Proposition 13 via
`chebyshev2.Primal.sqrt_mass_directional_derivative`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem sqrt_mass_variation_integrand (ψ θ : ℝ → ℝ) {κ t : ℝ} (hκ : 0<κ)
    (ht : t∈Icc (0:ℝ) 1) (a : ℝ) :
    momentVariationIntegrand ψ θ κ 1 a t=
      -3*exp (-lineProfile ψ θ a t)*t*
        (exp (lineProfile ψ θ a t)+2*t*(2-t^3))/
        (κ*normalizedAmplitude (lineProfile ψ θ a) κ t)*θ t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  let φ := lineProfile ψ θ a
  let z := normalizedAmplitude φ κ t
  have hz : 0<z := normalizedAmplitude_positive_on φ hκ ht
  have hs : κ*z^2=exp (φ t)+t*(2-t^3) := by
    rw [normalizedAmplitude_square_on φ hκ ht]
    field_simp
  dsimp only [momentVariationIntegrand]
  norm_num only [pow_one,Nat.cast_one,Nat.sub_self,pow_zero,one_mul]
  change 6*exp (-φ t)*t*(-z+exp (φ t)/κ/(2*z))*θ t=
    -3*exp (-φ t)*t*(exp (φ t)+2*t*(2-t^3))/(κ*z)*θ t
  field_simp
  linear_combination -12*t*θ t*hs

/--
The actual derivative at the stated point: `HasDerivAt (fun a => ∫ x,(speedData (lineProfile ψ
θ a) (lineProfile_continuous hψ hθ a)).density κ x) (∫ t in (0:ℝ)..1,-6*exp (-lineProfile ψ θ a
t)*t^3*(2-t^3)/κ*θ t) a`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Proposition 13.

Proof: Use the identities/estimates `chebyshev2.Primal.moment_directional_derivative`,
`chebyshev2.Primal.mass_variation_integrand` with the arguments shown in the proof.
-/
theorem mass_directional_derivative {ψ θ : ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : Continuous θ) {κ : ℝ} (hκ : 0<κ) (a : ℝ) :
    HasDerivAt (fun a => ∫ x,(speedData (lineProfile ψ θ a)
      (lineProfile_continuous hψ hθ a)).density κ x)
      (∫ t in (0:ℝ)..1,-6*exp (-lineProfile ψ θ a t)*t^3*(2-t^3)/κ*θ t) a := by
  -- Use the identities/estimates `chebyshev2.Primal.moment_directional_derivative`,
  -- `chebyshev2.Primal.mass_variation_integrand` with the arguments shown in the proof.
  have h := moment_directional_derivative hψ hθ hκ (j:=2) (by decide) a
  norm_num only [Nat.cast_ofNat,show (2:ℝ)/2=1 by norm_num,rpow_one] at h
  convert h using 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact (mass_variation_integrand ψ θ hκ (by simpa only [uIcc_of_le zero_le_one] using ht) a).symm

/--
The actual derivative at the stated point: `HasDerivAt (fun a => ∫ x,Real.sqrt ((speedData
(lineProfile ψ θ a) (lineProfile_continuous hψ hθ a)).density κ x)) (∫ t in (0:ℝ)..1,-3*exp
(-lineProfile ψ θ a t)*t* (exp (lineProfile ψ θ a t)+2*t*(2-t^3))/ (κ*normalizedAmplitude
(lineProfile ψ θ a) κ t)*θ t) a`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Proposition 13.

Proof: Use the identities/estimates `chebyshev2.Primal.moment_directional_derivative`,
`chebyshev2.Primal.sqrt_mass_variation_integrand` with the arguments shown in the proof.
-/
theorem sqrt_mass_directional_derivative {ψ θ : ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : Continuous θ) {κ : ℝ} (hκ : 0<κ) (a : ℝ) :
    HasDerivAt (fun a => ∫ x,Real.sqrt ((speedData (lineProfile ψ θ a)
      (lineProfile_continuous hψ hθ a)).density κ x))
      (∫ t in (0:ℝ)..1,-3*exp (-lineProfile ψ θ a t)*t*
        (exp (lineProfile ψ θ a t)+2*t*(2-t^3))/
        (κ*normalizedAmplitude (lineProfile ψ θ a) κ t)*θ t) a := by
  -- Use the identities/estimates `chebyshev2.Primal.moment_directional_derivative`,
  -- `chebyshev2.Primal.sqrt_mass_variation_integrand` with the arguments shown in the
  -- proof.
  have h := moment_directional_derivative hψ hθ hκ (j:=1) (by decide) a
  norm_num only [Nat.cast_ofNat] at h
  simp only [sqrt_eq_rpow] at ⊢
  convert h using 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact (sqrt_mass_variation_integrand ψ θ hκ (by simpa only [uIcc_of_le zero_le_one] using ht) a).symm

end
end chebyshev2.Primal
