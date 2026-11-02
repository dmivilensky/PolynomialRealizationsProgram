import jacobi.GelfandLevitan.FiniteKernelDifferentiation

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The original finite-system coefficients have genuine second spatial
derivatives. This follows from the true reference differential equation
and the independently differentiated original finite inverse system.
These derivatives supply the actual finite Darboux calculation; the
differential identity itself is a separate assertion.
Use: differentiating the original finite source slopes proves the actual finite coefficient second derivatives needed in the finite transformed differential equation.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution solutionSlope solutionAcceleration realSolution realSlope

/-- The genuine real selected reference slope has its actual acceleration from the original reference differential equation.
Use: differentiating the original finite source slopes proves the actual finite coefficient second derivatives needed in the finite transformed differential equation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: take the real part of the independently proved actual complex reference-slope derivative. Substitute its genuine original Schrodinger equation and the proved original real-energy values. -/
theorem realSlope_hasDerivAt_equation {a t : ℝ} (ha : -1<a) (E : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (realSlope a E) ((potential a t-E)*realSolution a E t) t := by
  -- The acceleration is obtained from the actual original differential equation, not by differentiating a spatial estimate.
  have he : solutionAcceleration a (E:ℂ) t=((potential a t-E:ℝ):ℂ)*solution a (E:ℂ) t := by
    push_cast
    linear_combination -solution_equation ha (E:ℂ) ht
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (solutionSlope_hasDerivAt a (E:ℂ) ht)
  rw [he,← realSolution_cast,← Complex.ofReal_mul] at h
  unfold realSlope
  exact h

/-- The derivative of the original finite coefficient operator is itself genuinely differentiable on every positive physical strip.
Use: finiteFeatureCoefficientsSlope_differentiableWithinAt differentiates the actual original coefficient slope, obtaining genuine second spatial derivatives.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: each genuine selected original reference factor has its actual spatial slope. Products, fixed signed weights, coordinate matrix units and true finite sums preserve differentiability in the original operator norm. -/
theorem finiteFeatureSystemSlope_differentiableWithinAt {a d t : ℝ} (ha : -1<a) (hd : 0<d) (N : ℕ)
    (ht : t∈Icc d (1/2)) : DifferentiableWithinAt ℝ (finiteFeatureSystemSlope a ha N) (Icc d (1/2)) t := by
  -- This is finite norm calculus for the actual original selected functions at their genuine source energies.
  have hsol (i : FeatureIndex N) : DifferentiableWithinAt ℝ
      (realSolution a (finiteFeatureEnergy a ha i)) (Icc d (1/2)) t :=
    (realSolution_hasDerivAt a (finiteFeatureEnergy a ha i)
      ⟨hd.trans_le ht.1,by linarith [ht.2]⟩).differentiableAt.differentiableWithinAt
  exact DifferentiableWithinAt.fun_sum (fun i _ => DifferentiableWithinAt.fun_sum (fun j _ =>
    (((hsol i).mul (hsol j)).const_mul (finiteFeatureWeight a ha i)).smul_const (featureMatrixUnit i j)))

/-- The actual original finite selected-slope source vector is genuinely differentiable throughout its positive physical strip.
Use: finiteFeatureCoefficientsSlope_differentiableWithinAt differentiates the genuine original inverse-system coefficient slope.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the original selected slope has its independently proved genuine acceleration at each original feature energy; fixed original weights and community finite product-space calculus preserve differentiability. -/
theorem finiteFeatureSourceSlope_differentiableWithinAt {a d t : ℝ} (ha : -1<a) (hd : 0<d) (N : ℕ)
    (ht : t∈Icc d (1/2)) : DifferentiableWithinAt ℝ (finiteFeatureSourceSlope a ha N) (Icc d (1/2)) t := by
  apply differentiableWithinAt_pi.mpr
  intro i
  exact ((realSlope_hasDerivAt_equation ha (finiteFeatureEnergy a ha i)
    ⟨hd.trans_le ht.1,by linarith [ht.2]⟩).const_mul (finiteFeatureWeight a ha i)).differentiableAt.differentiableWithinAt

/-- The actual original finite coefficient slope is genuinely differentiable on the physical positive strip at every actual finite-system unit.
Use: finiteFeatureCoefficients_secondDerivative_exists supplies the real second spatial derivatives used in the finite Darboux and transformed differential-equation calculation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the genuine original inverse and source have their already proved actual derivatives. The original system slope and source slope are independently differentiable by the actual reference differential equation. Apply the community product, difference and bounded-operator evaluation calculus to the same genuine original coefficient-slope formula. -/
theorem finiteFeatureCoefficientsSlope_differentiableWithinAt {a d t : ℝ} (ha : -1<a) (hd : 0<d) (N : ℕ)
    (ht : t∈Icc d (1/2)) (hu : IsUnit (finiteFeatureSystem a ha N t)) :
    DifferentiableWithinAt ℝ (finiteFeatureCoefficientsSlope a ha N) (Icc d (1/2)) t := by
  -- Every differentiated factor is the actual original finite-system factor already identified with the original GL reconstruction.
  have hQ := (finiteFeatureSystemInverse_hasDerivWithinAt ha hd N ht hu).differentiableWithinAt
  have hB := finiteFeatureSystemSlope_differentiableWithinAt ha hd N ht
  have hsource := (finiteFeatureSource_hasDerivWithinAt ha hd N ht).differentiableWithinAt
  have hslope := finiteFeatureSourceSlope_differentiableWithinAt ha hd N ht
  exact ((((hQ.mul hB).mul hQ).clm_apply hsource).sub (hQ.clm_apply hslope))

/-- The actual original finite-system kernel coefficients have genuine second spatial derivatives on every positive physical strip for every sufficiently long original spectral prefix, with invertibility discharged.
Use: the finite differential-equation calculation can differentiate the original coefficient equation twice, using these actual original first and second derivatives.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the genuine original finite-system unit threshold is uniform in the physical endpoint. At each physical point its actual coefficient slope is differentiable by the original inverse and reference differential calculus, giving its genuine within-strip derivative. -/
theorem finiteFeatureCoefficients_secondDerivative_exists (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ (d : ℝ) (_hd : 0<d) (t : ℝ),t∈Icc d (1/2) →
      ∃ a2 : FeatureIndex N→ℝ,HasDerivWithinAt (finiteFeatureCoefficientsSlope a ha N) a2 (Icc d (1/2)) t := by
  filter_upwards [finiteFeatureSystem_isUnit a ha] with N hN d hd t ht
  exact ⟨_,(finiteFeatureCoefficientsSlope_differentiableWithinAt ha hd N ht (hN t)).hasDerivWithinAt⟩

end
end jacobi.GelfandLevitan
