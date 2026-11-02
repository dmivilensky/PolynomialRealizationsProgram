import jacobi.Variational.FredholmGreen
import jacobi.Continuum.NuclearPairing

/-!
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
The actual bounded derivative operator s*R-s*I composed with any signed
L1 feature-density operator is genuinely trace class. Its nuclear trace
is the integral against the continuous bounded Green-diagonal gradient.
Source: nuclear rank-one integration and the proved Green diagonal bounds.
Use: its composition with K_delta is the genuine operator appearing in the trace variation.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real chebyshev2.Continuum
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The bounded resolvent expression for the scalar Fredholm derivative at the actual operator.
Use: its composition with K_delta is the genuine operator appearing in the trace variation.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
-/
def L1Source.fredholmDerivativeOperator (m : L1Source) (s : ℝ) (hs : 0≤s)
    (hp : s*observe m .top<1) : FeatureSpace →L[ℝ] FeatureSpace :=
  s • m.fredholmResolvent s hs hp-s • ContinuousLinearMap.id ℝ FeatureSpace

/-- The actual continuous Green-diagonal Fredholm gradient.
Use: supplies the multiplier rule's measurable bounded linear first-variation integrand.
Article: jacobi, Theorem D.7.
-/
def L1Source.fredholmGradient (m : L1Source) (s : ℝ) (hs : 0≤s)
    (hp : s*observe m .top<1) (x : ℝ) : ℝ :=
  s*(2*m.fredholmGreen s hs hp x x-1)

/-- The actual Fredholm gradient is continuous on the full real line.
Use: provides the regularity input of the Fredholm multiplier rule.
Article: jacobi, Theorem D.7.
Proof: restrict the jointly continuous Green kernel to its diagonal. -/
theorem L1Source.fredholmGradient_continuous (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) : Continuous (m.fredholmGradient s hs hp) := by
  unfold L1Source.fredholmGradient
  exact continuous_const.mul ((continuous_const.mul
    ((m.fredholmGreen_continuous hs hp).comp (continuous_id.prodMk continuous_id))).sub continuous_const)

/-- The actual gradient is nonnegative and uniformly bounded by the printed spectral margin.
Use: makes its pairing finite for every signed L1 perturbation.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: multiply the proved lower and upper Green diagonal bounds by the nonnegative parameter. -/
theorem L1Source.fredholmGradient_bounds (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x : ℝ) :
    0≤m.fredholmGradient s hs hp x ∧
      m.fredholmGradient s hs hp x≤s*((1-s*observe m .top)⁻¹-1) := by
  obtain ⟨hl,hu⟩ := m.fredholmGreen_diagonal hs hp x
  have he : 1/(2*(1-s*observe m .top))=(1/2:ℝ)*(1-s*observe m .top)⁻¹ := by field_simp
  rw [he] at hu
  unfold L1Source.fredholmGradient
  constructor
  · exact mul_nonneg hs (by linarith)
  · exact mul_le_mul_of_nonneg_left (by linarith) hs

/-- The derivative operator's feature quadratic value is exactly the Green-diagonal gradient.
Use: identifies the literal operator trace with the printed scalar first variation.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: each feature is a unit vector and the Green kernel has its defining half factor. -/
theorem L1Source.fredholmDerivativeOperator_feature (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x : ℝ) :
    inner ℝ (m.fredholmDerivativeOperator s hs hp (feature x)) (feature x)=
      m.fredholmGradient s hs hp x := by
  change inner ℝ (s • m.fredholmResolvent s hs hp (feature x)-s • feature x) (feature x)=_
  rw [inner_sub_left,real_inner_smul_left,real_inner_smul_left,real_inner_self_eq_norm_sq,feature_norm]
  unfold L1Source.fredholmGradient L1Source.fredholmGreen
  ring

/-- The actual trace-class Fredholm derivative pairing for every signed integrable perturbation.
Use: proves the article's operator trace gradient identity independently of the chosen Hilbert basis.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: the nuclear composition has exactly the underlying operator f_s'(K_m)*K_delta;
its proved trace integral is identified pointwise with the Green-diagonal gradient. -/
theorem L1Source.fredholm_trace_gradient (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) {d : ℝ → ℝ} (hd : Integrable d)
    {ι : Type*} (b : HilbertBasis ι ℝ FeatureSpace) :
    (jacobi.Continuum.composedDensity (m.fredholmDerivativeOperator s hs hp) d).val=
      m.fredholmDerivativeOperator s hs hp ∘L densityOperator d ∧
    TraceClassOperator.trace b
      (jacobi.Continuum.composedDensity (m.fredholmDerivativeOperator s hs hp) d)=
      ∫ x,m.fredholmGradient s hs hp x*d x := by
  -- Trace class is supplied by the nuclear integral, rather than assumed for this composition.
  refine ⟨jacobi.Continuum.composedDensity_val _ hd,?_⟩
  rw [jacobi.Continuum.composedDensity_trace b _ hd]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change d x*inner ℝ (m.fredholmDerivativeOperator s hs hp (feature x)) (feature x)=_
    rw [m.fredholmDerivativeOperator_feature hs hp]
    ring

end
end jacobi.Variational
