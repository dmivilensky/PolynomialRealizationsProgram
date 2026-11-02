import jacobi.Variational.FredholmSpectrum
import chebyshev2.HalfLine.Resolvent
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
Article: jacobi, Theorem D.7.
The actual feature-operator pencil is inverted under the printed condition
s*lambda_top<1, without replacing the eigenvalue by the larger total mass.
Its inverse obeys the sharp norm bound and is symmetric. These are the
operator inputs for the Green function and the Fredholm quadratic remainder.
Source: coercive self-adjoint operators and the actual compact spectral decomposition.
Use: the Neumann series uses the full subcritical spectral domain rather than s*mass<1.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real chebyshev2.Continuum chebyshev2.HalfLine
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The feature operator's norm is bounded by its actual leading eigenvalue.
Use: the Neumann series uses the full subcritical spectral domain rather than s*mass<1.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: express the norm of a symmetric operator as the supremum of its
absolute Rayleigh quotients; positivity and the actual top quadratic bound apply. -/
theorem densityOperator_norm_top (m : L1Source) : ‖densityOperator m.value‖≤observe m .top := by
  -- The Hilbert-space norm bound comes from the actual complete spectral data.
  let K := densityOperator m.value
  let D := densitySpectralData m.integrable m.nonneg
  have hp := densityOperator_positive m.integrable m.nonneg
  have he : D.eigenvalue=m.spectrum := density_kernel_eigenvalue_eq m.integrable m.nonneg D
  rw [K.norm_eq_iSup_rayleighQuotient hp.isSymmetric]
  apply ciSup_le
  intro u
  by_cases hu : u=0
  · simp only [hu,ContinuousLinearMap.rayleighQuotient,norm_zero,
      zero_pow (by decide : 2≠0),div_zero,abs_zero]
    exact (kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg 0
  have hn : 0<‖u‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hpos : 0 ≤ inner ℝ u (K u) := hp.re_inner_nonneg_right u
  have hb := D.top_quadratic_bound u
  rw [he] at hb
  change inner ℝ u (densityOperator m.value u)≤observe m .top*‖u‖^2 at hb
  change |inner ℝ (K u) u/‖u‖^2|≤_
  rw [real_inner_comm u (K u),abs_of_nonneg (div_nonneg hpos hn.le),div_le_iff₀ hn]
  exact hb

/-- The article's self-adjoint feature pencil I-s*K_m.
Use: the inverse is shared by Green evaluation, trace gradients and resolvent perturbation.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
-/
def L1Source.fredholmPencil (m : L1Source) (s : ℝ) : FeatureSpace →L[ℝ] FeatureSpace :=
  ContinuousLinearMap.id ℝ FeatureSpace-s • densityOperator m.value

/-- The actual pencil has the printed lower coercivity constant.
Use: proves invertibility and the sharp inverse norm bound.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: subtract s times the established actual top-eigenvalue Rayleigh bound. -/
theorem L1Source.fredholmPencil_coercive (m : L1Source) {s : ℝ} (hs : 0≤s) (u : FeatureSpace) :
    (1-s*observe m .top)*‖u‖^2 ≤ inner ℝ (m.fredholmPencil s u) u := by
  -- The feature and kernel spectra agree, so the existing quadratic bound uses the printed eigenvalue.
  let D := densitySpectralData m.integrable m.nonneg
  have he := density_kernel_eigenvalue_eq m.integrable m.nonneg D
  have hb := D.top_quadratic_bound u
  rw [he] at hb
  change inner ℝ u (densityOperator m.value u)≤observe m .top*‖u‖^2 at hb
  change (1-s*observe m .top)*‖u‖^2 ≤ inner ℝ (u-s • densityOperator m.value u) u
  rw [inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
    real_inner_comm u (densityOperator m.value u)]
  nlinarith [mul_le_mul_of_nonneg_left hb hs]

/-- The printed strict spectral pole condition makes the actual feature pencil invertible.
Use: constructs the Green resolvent with no additional small-mass assumption.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: the coercivity bound implies the Hilbert-space bounded-below form criterion. -/
theorem L1Source.fredholmPencil_isUnit (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) : IsUnit (m.fredholmPencil s) := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _
    (c := ⟨1-s*observe m .top,by linarith⟩) (by exact_mod_cast sub_pos.mpr hp)
  intro u
  have hb : ‖u‖^2*(1-s*observe m .top) ≤ inner ℝ (m.fredholmPencil s u) u := by
    simpa only [mul_comm] using m.fredholmPencil_coercive hs u
  exact hb.trans (le_abs_self _)

/-- The actual subcritical Fredholm resolvent, defined as the proved inverse of I-s*K_m.
Use: defines the Green kernel and its diagonal, then the Fredholm trace gradient.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
-/
def L1Source.fredholmResolvent (m : L1Source) (s : ℝ) (hs : 0≤s) (hp : s*observe m .top<1) :
    FeatureSpace →L[ℝ] FeatureSpace := inverseOfUnit _ (m.fredholmPencil_isUnit hs hp)

/-- Applying the pencil after its constructed resolvent is the identity.
Use: Green evaluation and the inverse norm bound use the exact operator equation.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: specialize the proved two-sided inverse identity. -/
theorem L1Source.pencil_resolvent (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (u : FeatureSpace) :
    m.fredholmPencil s (m.fredholmResolvent s hs hp u)=u :=
  DFunLike.congr_fun (inverseOfUnit_right _ (m.fredholmPencil_isUnit hs hp)) u

/-- Applying the constructed resolvent after its pencil is also the identity.
Use: uniqueness of the Green representative and the resolvent perturbation identity.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: specialize the proved two-sided inverse identity. -/
theorem L1Source.resolvent_pencil (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (u : FeatureSpace) :
    m.fredholmResolvent s hs hp (m.fredholmPencil s u)=u :=
  DFunLike.congr_fun (inverseOfUnit_left _ (m.fredholmPencil_isUnit hs hp)) u

/-- The actual inverse has the sharp spectral-margin norm bound.
Use: bounds the Green diagonal and both factors in the quadratic Fredholm remainder.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: apply coercivity to R*u, replace its pencil by u, and use Cauchy--Schwarz. -/
theorem L1Source.fredholmResolvent_norm (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) :
    ‖m.fredholmResolvent s hs hp‖≤(1-s*observe m .top)⁻¹ := by
  -- Cancel ||R*u|| only after treating its possible zero value.
  have hc : 0<1-s*observe m .top := sub_pos.mpr hp
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le)
  intro u
  let v := m.fredholmResolvent s hs hp u
  have hb := m.fredholmPencil_coercive hs v
  rw [m.pencil_resolvent hs hp] at hb
  have hi := real_inner_le_norm u v
  by_cases hv : ‖v‖=0
  · change ‖v‖≤_
    rw [hv]
    positivity
  have hvp : 0<‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  change ‖v‖≤_
  rw [← div_eq_inv_mul,le_div_iff₀ hc]
  nlinarith

/-- The actual subcritical resolvent is symmetric.
Use: Green symmetry and trace-gradient identities do not require a choice of eigenbasis.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: insert the pencil on each side and use its symmetry, then cancel the two inverse identities. -/
theorem L1Source.fredholmResolvent_symmetric (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) : (m.fredholmResolvent s hs hp).IsSymmetric := by
  -- Symmetry of an invertible pencil passes to its inverse through the exact equations.
  have hA : (m.fredholmPencil s).IsSymmetric :=
    LinearMap.IsSymmetric.id.sub ((densityOperator_positive m.integrable m.nonneg).isSymmetric.smul
      (c := s) (by simp))
  intro u v
  have h : inner ℝ (m.fredholmPencil s (m.fredholmResolvent s hs hp u))
      (m.fredholmResolvent s hs hp v)=inner ℝ (m.fredholmResolvent s hs hp u)
      (m.fredholmPencil s (m.fredholmResolvent s hs hp v)) :=
    hA _ _
  change inner ℝ (m.fredholmResolvent s hs hp u) v=inner ℝ u (m.fredholmResolvent s hs hp v)
  simpa only [m.pencil_resolvent hs hp] using h.symm

end
end jacobi.Variational
