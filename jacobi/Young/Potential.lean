import jacobi.Young.Sobolev
import jacobi.Variational.SecondMoment
import chebyshev2.GroundState.ConvolutionRegularity

/-!
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
The exponential potential is constructed from the actual H1 convolution of
chebyshev2 by an explicit spatial rescaling. Its Sobolev membership, literal
kernel formula and energy identity are proved, so the sharp Sobolev theorem
applies without an assumed weak solution or an energy certificate.
Use: reuses the already proved H1 convolution instead of rebuilding weak Green theory.
-/
namespace jacobi.Young
noncomputable section
open MeasureTheory Set Filter Real jacobi.Variational
open chebyshev2.Sobolev chebyshev2.GroundState chebyshev2.Continuum
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The rescaled L1 source that converts the old exponent-one kernel to exponent two.
Use: reuses the already proved H1 convolution instead of rebuilding weak Green theory.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
-/
def source (m : Density) (x : ℝ) : ℝ := m.value (x/2)

/-- The rescaled source is genuinely integrable.
Use: discharges every hypothesis of the reused H1 convolution construction.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: apply the Lebesgue change of variables for multiplication by 1/2. -/
theorem source_integrable (m : Density) : Integrable (source m) := by
  change Integrable (fun x => m.value (x/2))
  simpa only [div_eq_inv_mul] using
    (integrable_comp_mul_left_iff m.value (by norm_num : (2 : ℝ)⁻¹ ≠ 0)).mpr m.integrable

/-- The literal exponent-two Green potential in the original spatial coordinate.
Use: combines sharp Sobolev with the exact second spectral moment.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
-/
def potential (m : Density) (x : ℝ) : ℝ := (1/2 : ℝ)*H1.rep (convolution (source m)) (2*x)

/-- The actual derivative of the exponent-two potential.
Use: states its Sobolev energy in the same coordinate as the density m.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
-/
def potentialSlope (m : Density) (x : ℝ) : ℝ := convolutionSlope (source m) (2*x)

/-- Spatial rescaling preserves L2 membership of a continuous representative.
Use: both the potential and its continuous derivative have the required L2 norms.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Source: Lebesgue change of variables and the L2 squared-integral characterization.
Proof: change variables in the squared integral and use continuity for measurability. -/
theorem memLp_two_comp_mul {f : ℝ → ℝ} (hf : MemLp f 2 volume) (hc : Continuous f)
    {a : ℝ} (ha : a ≠ 0) : MemLp (fun x => f (a*x)) 2 volume := by
  apply (memLp_two_iff_integrable_sq (hc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mpr
  exact (integrable_comp_mul_left_iff (fun x => f x^2) ha).mpr hf.integrable_sq

/-- The exponent-two potential is an actual H1 representative with its actual derivative.
Use: fully discharges the hypotheses of sharp_sobolev_nonneg for the Green potential.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: scale the previously constructed H1 convolution, using its proved C1
representative and continuous L2 derivative to obtain local absolute continuity. -/
theorem potential_sobolev (m : Density) : SobolevRegular (potential m) (potentialSlope m) := by
  -- The old convolution supplies all regularity; only the exact scale factors are new.
  have hi := source_integrable m
  have hc : ContDiff ℝ 1 (potential m) :=
    contDiff_const.mul ((convolution_contDiff hi).comp (contDiff_const.mul contDiff_id))
  refine ⟨?_,?_,fun a b => hc.contDiffOn.absolutelyContinuousOnInterval,?_⟩
  · exact (memLp_two_comp_mul (H1.regular (convolution (source m))).value_memLp
      (H1.continuous_rep _) (by norm_num : (2 : ℝ) ≠ 0)).const_mul (1/2 : ℝ)
  · exact memLp_two_comp_mul (convolutionSlope_memLp hi) (convolutionSlope_continuous hi)
      (by norm_num : (2 : ℝ) ≠ 0)
  · exact Filter.Eventually.of_forall fun x => by
      convert ((convolution_hasDerivAt hi (2*x)).comp x
        ((hasDerivAt_id x).const_mul 2)).const_mul (1/2 : ℝ) using 1
      · rfl
      · dsimp [potentialSlope]
        ring

/-- The constructed potential equals the literal convolution in the article.
Use: connects its H1 energy to the actual second kernel moment.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: substitute z=2y in the exponent-one convolution and cancel its Jacobian. -/
theorem potential_kernel (m : Density) (x : ℝ) :
    potential m x = ∫ y, m.value y*exp (-2*|x-y|) := by
  -- The prefactor 1/2 is exactly the inverse Jacobian of the substitution.
  change (1/2 : ℝ)*H1.rep (convolution (source m)) (2*x) = _
  rw [convolution_rep (source_integrable m)]
  have h := Measure.integral_comp_mul_left
    (fun z : ℝ => exp (-|2*x-z|)*source m z) (2 : ℝ)
  norm_num only [invOf_eq_inv,inv_eq_one_div,abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹),smul_eq_mul] at h
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only [source]
    rw [show 2*x-2*y=2*(x-y) by ring,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [show -(2*|x-y|)=-2*|x-y| by ring,show (2*y)/2=y by ring,mul_comm]

/-- Positivity of the actual Green potential.
Use: the nonnegative sharp Sobolev theorem applies to every admissible density.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: every factor of its literal convolution integrand is nonnegative. -/
theorem potential_nonneg (m : Density) (x : ℝ) : 0 ≤ potential m x := by
  rw [potential_kernel]
  exact integral_nonneg (fun y => mul_nonneg (m.nonneg y) (exp_pos _).le)

/-- The convolution is the Riesz representative of twice the density pairing.
Use: derives the potential energy identity from the existing H1 representation.
Article: jacobi, Section 3.2 (sharp Young inequality).
Source: the reproducing-kernel construction in chebyshev2, Theorem 3.1.
Proof: apply the continuous inner functional to the Bochner feature integral
and use the exact normalization of the H1 representative. -/
theorem convolution_form {j : ℝ → ℝ} (hj : Integrable j) (v : H1) :
    inner ℝ v (convolution j)=2*(∫ x, j x*H1.rep v x) := by
  -- The Bochner integral is integrable before the inner functional is commuted with it.
  change inner ℝ v (sqrt 2 • ∫ x, j x • feature x) = _
  rw [real_inner_smul_right,← integral_inner (synthesisL1_integrable hj) v,
    ← integral_const_mul,← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [real_inner_smul_right]
    change sqrt 2*(j x*inner ℝ v (feature x)) =
      2*(j x*((sqrt 2)⁻¹*inner ℝ (feature x) v))
    rw [real_inner_comm v (feature x)]
    have hs : sqrt 2=2*(sqrt 2)⁻¹ := by field_simp; nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ = (2*(sqrt 2)⁻¹)*(j x*inner ℝ v (feature x)) := congrArg (fun c => c*(j x*inner ℝ v (feature x))) hs
      _ = _ := by ring

/-- The two versions of the old convolution derivative have identical squared integral.
Use: translates its H1 norm identity to the continuous derivative used after rescaling.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: uniqueness of the a.e. derivative identifies the H1 slope and convolutionSlope. -/
theorem convolution_slope_integral {j : ℝ → ℝ} (hj : Integrable j) :
    (∫ x, H1.slope (convolution j) x^2) = ∫ x, convolutionSlope j x^2 := by
  apply integral_congr_ae
  filter_upwards [(H1.regular (convolution j)).derivative_ae,convolution_derivative_ae hj] with x h1 h2
  rw [h1.unique h2]

/-- The constructed potential has energy exactly four times the actual second moment.
Use: the final analytic bridge in sharp Young; no weak-energy equality is assumed.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: scale the H1 norm and its Riesz pairing by z=2x, then identify
the density-potential pairing with the genuine spectral second moment. -/
theorem potential_energy (m : Density) :
    (∫ x, potentialSlope m x^2)+4*(∫ x, potential m x^2)=4*observe m .second := by
  -- First obtain the old exact H1 energy equality, then scale both its terms and its pairing.
  let U := convolution (source m)
  have he := convolution_form (source_integrable m) U
  rw [real_inner_self_eq_norm_sq,H1.norm_sq_energy,convolution_slope_integral (source_integrable m)] at he
  have hd : (∫ x, potentialSlope m x^2)=(1/2 : ℝ)*(∫ x, convolutionSlope (source m) x^2) := by
    simpa only [potentialSlope,smul_eq_mul,invOf_eq_inv,inv_eq_one_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 1/2)] using
      Measure.integral_comp_mul_left (fun x => convolutionSlope (source m) x^2) 2
  have hv : (∫ x, potential m x^2)=(1/8 : ℝ)*(∫ x, H1.rep U x^2) := by
    simp_rw [potential,mul_pow]
    rw [integral_const_mul,Measure.integral_comp_mul_left (fun x => H1.rep U x^2)]
    norm_num [smul_eq_mul]
    ring
  have hp : (∫ x, source m x*H1.rep U x)=4*(∫ x, m.value x*potential m x) := by
    have h := Measure.integral_comp_mul_left (fun x => source m x*H1.rep U x) (2 : ℝ)
    have hs : (fun x => source m (2*x)*H1.rep U (2*x)) =
        (fun x => 2*(m.value x*potential m x)) := by
      funext x
      dsimp [source,potential,U]
      rw [show (2*x)/2=x by ring]
      ring
    rw [hs,integral_const_mul] at h
    norm_num [smul_eq_mul] at h
    linarith
  have hG : observe m .second=∫ x, m.value x*potential m x := by
    rw [← m.secondPairing_self,secondPairing_iterated m.integrable m.integrable m.measurable m.measurable]
    simp_rw [potential_kernel]
  rw [hd,hv,hG]
  linarith

end
end jacobi.Young
