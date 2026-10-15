import «2610.05164v2».GroundState.Existence
import «2610.05164v2».GroundState.ConvolutionRegularity

/-!
Article: 2610.05164v2, Theorem 3.1.
Classical and Sobolev regularity of the ground state, for general L1 density: no continuity or
boundedness of m is assumed.
Use: `«2610.05164v2».GroundState.exists_regular_positive_ground` feeds
`«2610.05164v2».GroundState.exists_ground_square_identity` (The ground logarithmic derivative and
equation (11) are constructed for every general L1 density; the Riccati hypotheses are proved from
its actual classical ground function, rather than supplied as a certificate).
Proof chain: `«2610.05164v2».GroundState.ground_state` — 2610.05164v2, Theorem 3.1; Sharp
ground-state variational principle, ODE, simplicity and intrinsic coordinate.
-/
namespace «2610.05164v2».GroundState
noncomputable section
open «2610.05164v2».Continuum «2610.05164v2».Sobolev Set MeasureTheory Real
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, sqrt (m x)*H1.rep
(convolution (fun y => sqrt (m y)*f y)) x=r*f x`.

Use: `«2610.05164v2».GroundState.exists_regular_positive_ground` uses this identity to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem kernel_eigen_convolution_relation {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    {f : FeatureSpace} {r : ℝ} (he : kernelOperator hm hn f=r • f) :
    ∀ᵐ x, sqrt (m x)*H1.rep (convolution (fun y => sqrt (m y)*f y)) x=r*f x := by
  filter_upwards [kernelOperator_coe hm hn f,Lp.coeFn_smul r f] with x hx hs
  rw [he,hs] at hx
  change r*f x=sqrt (m x)*∫ y, exp (-|x-y|)*sqrt (m y)*f y at hx
  rw [convolution_rep (synthesis_coefficient_integrable hm hn f)]
  simpa only [mul_assoc] using hx.symm

/--
Classical and Sobolev regularity of the ground state, for general L1 density: no continuity or
boundedness of m is assumed.

Use: `«2610.05164v2».GroundState.exists_ground_square_identity` uses this identity to establish
the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem exists_regular_positive_ground {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hM : 0 < ∫ x, m x) : ∃ (u : H1) (d : ℝ → ℝ),
      (∀ x, 0 < H1.rep u x) ∧ ContDiff ℝ 1 (H1.rep u) ∧
      (∀ x, HasDerivAt (H1.rep u) (d x) x) ∧
      (∀ a b, AbsolutelyContinuousOnInterval d a b) ∧ MemLp d 2 volume ∧
      (∀ x, |d x| ≤ H1.rep u x) ∧
      (∀ᵐ x, HasDerivAt d ((1-groundParameter hm hn*m x)*H1.rep u x) x) ∧
      densityOperator m u=kernelEigenvalue hm hn 0 • u := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  obtain ⟨f,hf,hfn,he⟩ := exists_nonnegative_maximizer hm hn hM
  let j : ℝ → ℝ := fun x => sqrt (m x)*f x
  -- Establish hj as the integrability justification for the later integral estimates or
  -- changes of order.
  have hj : Integrable j := synthesis_coefficient_integrable hm hn f
  have hjn : ∀ᵐ x, 0 ≤ j x := hfn.mono (fun x hx => mul_nonneg (sqrt_nonneg _) hx)
  have hjp : 0 < ∫ x, j x := maximizer_source_positive hm hn hM hf hfn he
  refine ⟨convolution j,convolutionSlope j,convolution_positive hj hjn hjp,
    convolution_contDiff hj,convolution_hasDerivAt hj,convolutionSlope_locallyAC hj,
    convolutionSlope_memLp hj,convolutionSlope_abs_le hj hjn,?_,maximizer_convolution_eigen hm hn f he⟩
  filter_upwards [convolution_second_derivative_ae hj,kernel_eigen_convolution_relation hm hn he] with x hd hr
  have hp := (top_density_attained hm hn hM).1
  have hs : 2*j x=groundParameter hm hn*m x*H1.rep (convolution j) x := by
    have h := congrArg (fun z => sqrt (m x)*z) hr
    change sqrt (m x)*(sqrt (m x)*H1.rep (convolution j) x)=
      sqrt (m x)*(kernelEigenvalue hm hn 0*f x) at h
    have hsq := sq_sqrt (hn x)
    change 2*(sqrt (m x)*f x)=(2/kernelEigenvalue hm hn 0)*m x*H1.rep (convolution j) x
    field_simp
    linear_combination -h+H1.rep (convolution j) x*hsq
  convert hd using 1
  rw [hs]
  ring

end
end «2610.05164v2».GroundState
