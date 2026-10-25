import chebyshev2.Primal.Symmetry
import chebyshev2.Comparison.SymmetricTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Article: chebyshev2, Theorem 5.1.
The four primal spectral observations are observations of the actual compact density.
Result: `chebyshev2.Primal.square_trace_cubic` supplies the stated article conclusion.
-/
namespace chebyshev2.Primal
noncomputable section
open Set MeasureTheory Real chebyshev2.PrescribedSpeed chebyshev2.Filters chebyshev2.Continuum
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
The precise assertion is `(∫ x in Iic (0:ℝ),f x)= ∫ t in (0:ℝ)..1,normalizedVelocity φ t*f
(normalizedX hφ t)`.

Use: `chebyshev2.Primal.determinant_cubic` rewrites with this identity to establish the
identity stated in that declaration.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem half_integral_cubic {φ : ℝ → ℝ} (hφ : Continuous φ) {f : ℝ → ℝ}
    (hf : Integrable f) (hz : ∀ x≤(speedData φ hφ).X 0,f x=0) :
    (∫ x in Iic (0:ℝ),f x)=
      ∫ t in (0:ℝ)..1,normalizedVelocity φ t*f (normalizedX hφ t) := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  have he := intervalIntegral.integral_Iic_sub_Iic
    (a:=(speedData φ hφ).X 0) (b:=0) hf.integrableOn hf.integrableOn
  have hz' : (∫ x in Iic ((speedData φ hφ).X 0),f x)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    exact hz x hx
  rw [hz',sub_zero] at he
  rw [he]
  have hc := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f:=normalizedX hφ) (f':=normalizedVelocity φ) (g:=f) (a:=0) (b:=1)
    (normalizedX_continuous hφ).continuousOn
    (fun t ht => (normalizedX_derivative hφ t
      ⟨by simpa using ht.1.le,by simpa using ht.2.le⟩).hasDerivAt
        (Icc_mem_nhds (by simpa using ht.1) (by simpa using ht.2)))
    (fun _ _ => by unfold normalizedVelocity;positivity)
  simpa only [Function.comp_def,normalizedX,zero_pow (by decide : 3≠0),one_pow,
    SpeedData.X,intervalIntegral.integral_same,mul_comm] using hc.symm

/--
The stated quantitative bound `IntervalIntegrable (fun t => normalizedVelocity φ t*f
(normalizedX hφ t)) volume 0 1`.

Use: `chebyshev2.Primal.full_integral_cubic` rewrites with this identity to establish exact
identity `(∫ x,f x)=∫ t in (0:ℝ)..1, normalizedVelocity φ t*(f (normalizedX hφ t)+f
(-normalizedX hφ t))`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Primal.normalizedX_continuous`,
`chebyshev2.Primal.normalizedX_derivative` with the arguments shown in the proof.
-/
theorem normalized_integrable {φ : ℝ → ℝ} (hφ : Continuous φ) {f : ℝ → ℝ}
    (hf : Integrable f) :
    IntervalIntegrable (fun t => normalizedVelocity φ t*f (normalizedX hφ t)) volume 0 1 := by
  -- Use the identities/estimates `chebyshev2.Primal.normalizedX_continuous`,
  -- `chebyshev2.Primal.normalizedX_derivative` with the arguments shown in the proof.
  have hc := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (f:=normalizedX hφ) (f':=normalizedVelocity φ) (g:=f) (a:=0) (b:=1)
    (normalizedX_continuous hφ).continuousOn
    (fun t ht => (normalizedX_derivative hφ t
      ⟨by simpa using ht.1.le,by simpa using ht.2.le⟩).hasDerivAt
        (Icc_mem_nhds (by simpa using ht.1) (by simpa using ht.2)))
    (fun _ _ => by unfold normalizedVelocity;positivity)
  simpa only [Function.comp_def,mul_comm] using hc.mpr hf.intervalIntegrable

/--
Both charts of a symmetric coordinate, without assuming that the integrand itself is symmetric.
Both exterior contributions are accounted for.

Exact identity `(∫ x,f x)=∫ t in (0:ℝ)..1, normalizedVelocity φ t*(f (normalizedX hφ t)+f
(-normalizedX hφ t))`.

Use: `chebyshev2.Primal.determinant_profile_difference_cubic` rewrites with this identity
to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Primal.X_reflection`,
`chebyshev2.Primal.half_integral_cubic`, `chebyshev2.Primal.normalized_integrable` with
the arguments shown in the proof.
-/
theorem full_integral_cubic {φ : ℝ → ℝ} (hφ : Continuous φ) {f : ℝ → ℝ}
    (hf : Integrable f)
    (hl : ∀ x≤(speedData φ hφ).X 0,f x=0)
    (hr : ∀ x,(speedData φ hφ).X 2≤x → f x=0) :
    (∫ x,f x)=∫ t in (0:ℝ)..1,
      normalizedVelocity φ t*(f (normalizedX hφ t)+f (-normalizedX hφ t)) := by
  -- Establish hfn as the integrability justification for the later integral estimates or
  -- changes of order.
  have hfn : Integrable (fun x => f (-x)) :=
    (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hf
  have hx : (speedData φ hφ).X 2=-(speedData φ hφ).X 0 :=
    by simpa only [sub_zero] using X_reflection hφ 0
  have hn : ∀ x≤(speedData φ hφ).X 0,f (-x)=0 := by
    intro x h
    exact hr (-x) (by rw [hx];linarith)
  have href := integral_comp_neg_Iic (0:ℝ) f
  rw [neg_zero] at href
  rw [← intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn (b:=0),
    ← href,half_integral_cubic hφ hf hl,half_integral_cubic hφ hfn hn,
    ← intervalIntegral.integral_add (normalized_integrable hφ hf) (normalized_integrable hφ hfn)]
  apply intervalIntegral.integral_congr
  intro t _
  ring

/--
Defines `determinantCore` of type `ℝ` by `6*exp (-φ t)*nonlinearFilter hφ κ s t`.

Use: `chebyshev2.Primal.determinant_cubic` uses this definition to establish the identity
stated in that declaration.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.
-/
def determinantCore {φ : ℝ → ℝ} (hφ : Continuous φ) (κ s t : ℝ) : ℝ :=
  6*exp (-φ t)*nonlinearFilter hφ κ s t
/--
Defines `traceCore` of type `ℝ` by `6*exp (-φ t)*(linearFilter hφ κ t)^2`.

Use: `chebyshev2.Primal.square_trace_cubic` uses this definition to establish the precise
assertion is `κ^2/4*(∑' j,kernelEigenvalue ((speedData φ hφ).density_integrable hκ) ((speedData
φ hφ).density_nonneg hκ) j^2)= (∫ t in (0:ℝ)..1,traceCore hφ κ t)+(linearFilter hφ κ 1)^2`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.square_trace_cubic`.
-/
def traceCore {φ : ℝ → ℝ} (hφ : Continuous φ) (κ t : ℝ) : ℝ :=
  6*exp (-φ t)*(linearFilter hφ κ t)^2

/--
The precise assertion is `logDeterminant (kernelEigenvalue ((speedData φ hφ).density_integrable
hκ) ((speedData φ hφ).density_nonneg hκ)) s= (∫ t in (0:ℝ)..1,determinantCore hφ κ s t)+ log
(1+nonlinearFilter hφ κ s 1)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 5.1.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg`,
`chebyshev2.Comparison.symmetric_logDeterminant` with the arguments shown in the proof.
-/
theorem determinant_cubic {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ s : ℝ} (hκ : 0<κ) (hs : 0≤s) :
    logDeterminant (kernelEigenvalue ((speedData φ hφ).density_integrable hκ)
      ((speedData φ hφ).density_nonneg hκ)) s=
      (∫ t in (0:ℝ)..1,determinantCore hφ κ s t)+
        log (1+nonlinearFilter hφ κ s 1) := by
  -- Use the identities/estimates
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_nonneg`,
  -- `chebyshev2.Comparison.symmetric_logDeterminant` with the arguments shown in the
  -- proof.
  rw [chebyshev2.Comparison.symmetric_logDeterminant
    ((speedData φ hφ).density_integrable hκ) ((speedData φ hφ).density_nonneg hκ)
    (density_continuous hφ κ) hs (density_reflection hφ κ)]
  rw [half_integral_cubic hφ (nonlinear_integrable
    ((speedData φ hφ).density_integrable hκ) ((speedData φ hφ).density_nonneg hκ) hs)
    (fun x hx => nonlinear_left_of_density_zero x s (fun y hy =>
      (speedData φ hφ).density_zero_outside κ (fun hi => (not_lt_of_ge (hy.trans hx)) hi.1))),
    ← intervalIntegral.integral_const_mul]
  congr 1
  · apply intervalIntegral.integral_congr
    intro t _
    dsimp only [normalizedVelocity,determinantCore,nonlinearFilter]
    ring
  · congr 2
    norm_num [nonlinearFilter,normalizedX,SpeedData.X]

/--
The precise assertion is `κ^2/4*(∑' j,kernelEigenvalue ((speedData φ hφ).density_integrable hκ)
((speedData φ hφ).density_nonneg hκ) j^2)= (∫ t in (0:ℝ)..1,traceCore hφ κ t)+(linearFilter hφ
κ 1)^2`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 5.1.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem square_trace_cubic {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ) :
    κ^2/4*(∑' j,kernelEigenvalue ((speedData φ hφ).density_integrable hκ)
      ((speedData φ hφ).density_nonneg hκ) j^2)=
      (∫ t in (0:ℝ)..1,traceCore hφ κ t)+(linearFilter hφ κ 1)^2 := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hg := ground_exact hφ hκ
  have he := chebyshev2.Comparison.symmetric_square_trace
    ((speedData φ hφ).density_integrable hκ) ((speedData φ hφ).density_nonneg hκ)
    (density_continuous hφ κ) (density_reflection hφ κ)
  rw [hg] at he
  have hl : chebyshev2.Filters.linear ((speedData φ hφ).density_integrable hκ)
      ((speedData φ hφ).density_nonneg hκ)=fun x => κ*causal 2 ((speedData φ hφ).density κ) x := by
    funext x
    rw [chebyshev2.Filters.linear,hg]
  rw [hl] at he
  rw [half_integral_cubic hφ
    ((causal_square_integrable ((speedData φ hφ).density_integrable hκ)
      ((speedData φ hφ).density_nonneg hκ)).const_mul (κ^2) |>.congr
      (Filter.Eventually.of_forall (fun x => (mul_pow κ _ 2).symm)))
    (fun x hx => by
      have hz : causal 2 ((speedData φ hφ).density κ) x=0 := by
        unfold causal
        have hz' : (∫ y in Iic x,exp (2*y)*(speedData φ hφ).density κ y)=0 := by
          apply integral_eq_zero_of_ae
          filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
          rw [(speedData φ hφ).density_zero_outside κ
            (fun hi => (not_lt_of_ge (hy.trans hx)) hi.1),mul_zero]
          rfl
        rw [hz',mul_zero]
      rw [hz,mul_zero,zero_pow (by decide : 2≠0)]),
    ← intervalIntegral.integral_const_mul] at he
  rw [he]
  congr 1
  · apply intervalIntegral.integral_congr
    intro t _
    dsimp only [traceCore,linearFilter,normalizedVelocity]
    ring
  · norm_num [linearFilter,normalizedX,SpeedData.X]

end
end chebyshev2.Primal
