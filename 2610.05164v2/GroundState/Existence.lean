import «2610.05164v2».GroundState.PositiveMaximizer

/-!
Article: 2610.05164v2, Theorem 3.1.
The ground eigenfunction solves the article's ODE weakly against every actual H1 test function, with
the exact prescribed spectral coupling.
Use: `«2610.05164v2».GroundState.ground_eigenfunction_weak_equation` feeds
`«2610.05164v2».GroundState.density_ground_energy` (density ground energy).
Proof chain: `«2610.05164v2».GroundState.ground_state` — 2610.05164v2, Theorem 3.1; Sharp
ground-state variational principle, ODE, simplicity and intrinsic coordinate.
-/
namespace «2610.05164v2».GroundState
noncomputable section
open «2610.05164v2».Continuum «2610.05164v2».Sobolev Set MeasureTheory Real
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `densityOperator m (convolution (fun x => sqrt (m x)*f x))= r •
convolution (fun x => sqrt (m x)*f x)`.

Use: `«2610.05164v2».GroundState.exists_positive_ground_eigenfunction` uses this identity to
establish constructs witnesses with the exact properties `∃ u : H1, (∀ x, 0 < H1.rep u x) ∧
densityOperator m u=kernelEigenvalue hm hn 0 • u`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Use the identities/estimates
`«2610.05164v2».Continuum.evaluationOperator_adjoint_apply`,
`«2610.05164v2».Continuum.evaluationOperator_adjoint_comp` with the arguments shown in the
proof.
-/
theorem maximizer_convolution_eigen {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (f : FeatureSpace) {r : ℝ} (he : kernelOperator hm hn f=r • f) :
    densityOperator m (convolution (fun x => sqrt (m x)*f x))=
      r • convolution (fun x => sqrt (m x)*f x) := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.evaluationOperator_adjoint_apply`,
  -- `«2610.05164v2».Continuum.evaluationOperator_adjoint_comp` with the arguments shown in the
  -- proof.
  let A := evaluationOperator hm hn
  have hu : convolution (fun x => sqrt (m x)*f x)=sqrt 2 • A.adjoint f := by
    rw [evaluationOperator_adjoint_apply]
    rfl
  rw [hu,← evaluationOperator_adjoint_comp hm hn]
  change A.adjoint (A (sqrt 2 • A.adjoint f)) = r • (sqrt 2 • A.adjoint f)
  have hfe : A (A.adjoint f)=r • f := he
  simp only [map_smul,hfe,smul_smul]
  rw [mul_comm]

/--
The stated quantitative bound `0 < ∫ x, sqrt (m x)*f x`.

Use: `«2610.05164v2».GroundState.exists_positive_ground_eigenfunction` uses this bound to
establish constructs witnesses with the exact properties `∃ u : H1, (∀ x, 0 < H1.rep u x) ∧
densityOperator m u=kernelEigenvalue hm hn 0 • u`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem maximizer_source_positive {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hM : 0 < ∫ x, m x) {f : FeatureSpace} (hf : ‖f‖=1) (hfn : ∀ᵐ x, 0 ≤ f x)
    (he : kernelOperator hm hn f=kernelEigenvalue hm hn 0 • f) :
    0 < ∫ x, sqrt (m x)*f x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hj := synthesis_coefficient_integrable hm hn f
  have hjn : ∀ᵐ x, 0 ≤ sqrt (m x)*f x := hfn.mono (fun x hx => mul_nonneg (sqrt_nonneg _) hx)
  apply lt_of_le_of_ne (integral_nonneg_of_ae hjn)
  intro hz
  have hae := (integral_eq_zero_iff_of_nonneg_ae hjn hj).mp hz.symm
  have ha : (evaluationOperator hm hn).adjoint f=0 := by
    rw [evaluationOperator_adjoint_apply]
    have hzero : (fun x => (sqrt (m x)*f x) • feature x) =ᵐ[volume] (fun _ => 0) := by
      filter_upwards [hae] with x hx
      rw [hx]
      exact zero_smul _ _
    rw [integral_congr_ae hzero, integral_zero]
  have hk : kernelOperator hm hn f=0 := by simp [kernelOperator,ha]
  have hs : kernelEigenvalue hm hn 0 • f=0 := he.symm.trans hk
  have hfp : f=0 := (smul_eq_zero.mp hs).resolve_left
    (ne_of_gt (top_density_attained hm hn hM).1)
  rw [hfp,norm_zero] at hf
  norm_num at hf

/--
Strictly positive ground eigenfunction in literal H1, constructed from the nonnegative L2
maximizer and the exponential convolution.

Constructs witnesses with the exact properties `∃ u : H1, (∀ x, 0 < H1.rep u x) ∧
densityOperator m u=kernelEigenvalue hm hn 0 • u`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.1.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.exists_nonnegative_maximizer`,
`«2610.05164v2».Continuum.synthesis_coefficient_integrable`,
`«2610.05164v2».GroundState.maximizer_source_positive` with the arguments shown in the proof.
-/
theorem exists_positive_ground_eigenfunction {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hM : 0 < ∫ x, m x) : ∃ u : H1,
      (∀ x, 0 < H1.rep u x) ∧ densityOperator m u=kernelEigenvalue hm hn 0 • u := by
  -- Use the identities/estimates `«2610.05164v2».GroundState.exists_nonnegative_maximizer`,
  -- `«2610.05164v2».Continuum.synthesis_coefficient_integrable`,
  -- `«2610.05164v2».GroundState.maximizer_source_positive` with the arguments shown in the
  -- proof.
  obtain ⟨f,hf,hfn,he⟩ := exists_nonnegative_maximizer hm hn hM
  let j : ℝ → ℝ := fun x => sqrt (m x)*f x
  -- Establish hj as the integrability justification for the later integral estimates or
  -- changes of order.
  have hj : Integrable j := synthesis_coefficient_integrable hm hn f
  have hjn : ∀ᵐ x, 0 ≤ j x := hfn.mono (fun x hx => mul_nonneg (sqrt_nonneg _) hx)
  have hjp : 0 < ∫ x, j x := maximizer_source_positive hm hn hM hf hfn he
  refine ⟨convolution j, convolution_positive hj hjn hjp, ?_⟩
  exact maximizer_convolution_eigen hm hn f he

/--
The ground eigenfunction solves the article's ODE weakly against every actual H1 test function,
with the exact prescribed spectral coupling.

The precise assertion is `(∫ x, H1.slope v x*H1.slope u x)+(∫ x, H1.rep v x*H1.rep u x)=
groundParameter hm hn*∫ x, m x*H1.rep v x*H1.rep u x`.

Use: `«2610.05164v2».GroundState.density_ground_energy` uses this identity to establish exact
identity `‖v‖^2=groundParameter hm hn*(∫ x, m x*H1.rep v x^2)`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Use the identities/estimates `«2610.05164v2».Sobolev.H1.inner_energy`,
`«2610.05164v2».GroundState.top_density_attained`,
`«2610.05164v2».Sobolev.sobolevDensityOperator_form` with the arguments shown in the proof.
-/
theorem ground_eigenfunction_weak_equation {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hM : 0 < ∫ x, m x) {u : H1}
    (he : densityOperator m u=kernelEigenvalue hm hn 0 • u) (v : H1) :
    (∫ x, H1.slope v x*H1.slope u x)+(∫ x, H1.rep v x*H1.rep u x)=
      groundParameter hm hn*∫ x, m x*H1.rep v x*H1.rep u x := by
  -- Use the identities/estimates `«2610.05164v2».Sobolev.H1.inner_energy`,
  -- `«2610.05164v2».GroundState.top_density_attained`,
  -- `«2610.05164v2».Sobolev.sobolevDensityOperator_form` with the arguments shown in the
  -- proof.
  rw [← H1.inner_energy]
  have hi := congrArg (fun w => inner ℝ v w) he
  rw [sobolevDensityOperator_form hm,real_inner_smul_right] at hi
  have hp := (top_density_attained hm hn hM).1
  dsimp [groundParameter]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (ne_of_gt hp)).mpr
  change inner ℝ v u*kernelEigenvalue hm hn 0=
    2*(∫ x, m x*H1.rep v x*H1.rep u x)
  linarith

end
end «2610.05164v2».GroundState
