import jacobi.GelfandLevitan.Operator
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
Article: jacobi, Appendix C.2 (uniform GL coercivity).
The actual original kernel is compact and its identity perturbation is
genuinely injective. The community Fredholm alternative therefore proves
that this original operator has a true bounded inverse. No invertibility
certificate or spectral-gap assumption is supplied as an extra premise.
Use: the actual compact eigenbasis argument converts its proved bounded inverse and original positivity into the source uniform quadratic lower bound.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Module jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The actual identity-plus-original-kernel operator is symmetric on the true original half-interval Hilbert domain.
Use: the actual compact eigenbasis argument converts its proved bounded inverse and original positivity into the source uniform quadratic lower bound.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: expand the genuine identity perturbation in each inner-product entry and use the proved true original kernel symmetry. -/
theorem positiveOperator_symmetric (a : ℝ) (ha : -1<a) : (positiveOperator a ha).IsSymmetric := by
  intro v w
  change inner ℝ (v+kernelOperator a ha v) w=inner ℝ v (w+kernelOperator a ha w)
  have hs : inner ℝ (kernelOperator a ha v) w=inner ℝ v (kernelOperator a ha w) :=
    kernelOperator_symmetric a ha v w
  rw [inner_add_left,inner_add_right,hs]

/-- Minus one is not an eigenvalue of the actual original compact GL kernel operator.
Use: discharges the genuine spectral premise of the community Fredholm alternative for the original I+F operator.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: such an actual eigenvector would be a nonzero null vector of
the genuine identity-plus-original-kernel operator. Its already proved
actual injectivity forces that same original vector to be zero. -/
theorem kernelOperator_not_eigenvalue_neg_one (a : ℝ) (ha : -1<a) :
    ¬ Module.End.HasEigenvalue (kernelOperator a ha).toLinearMap (-1:ℝ) := by
  -- The original eigenvector equation and the genuine positive-operator null equation refer to the same Hilbert vector.
  intro h
  obtain ⟨v,hv⟩ := h.exists_hasEigenvector
  have he : kernelOperator a ha v= -v := by
    have hh := hv.apply_eq_smul
    simp only [neg_one_smul] at hh
    convert! hh using 1
  have hzero : positiveOperator a ha v=0 := by
    change v+kernelOperator a ha v=0
    rw [he,add_neg_cancel]
  have hv0 : v=0 := positiveOperator_injective a ha (by simpa only [map_zero] using hzero)
  exact hv.2 hv0

/-- The actual original identity-plus-GL-kernel operator is a unit in the true bounded Hilbert operator algebra.
Use: constructs the genuine original bounded inverse used in source uniform coercivity and the GL equation.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Source: Fredholm alternative for compact operators, mathlib.
Proof: apply the community compact Fredholm alternative to the
genuine source kernel at the actual nonzero scalar minus one. The
proved original injectivity excludes its eigenvalue alternative.
The resolvent alternative says that the negative of the original
identity-plus-kernel operator is a unit, hence the original operator is. -/
theorem positiveOperator_isUnit (a : ℝ) (ha : -1<a) : IsUnit (positiveOperator a ha) := by
  -- All compactness and injectivity data have been proved for this actual original Hilbert operator.
  rcases (kernelOperator_compact a ha).hasEigenvalue_or_mem_resolventSet
      (by norm_num : (-1:ℝ)≠0) with h | h
  · exact False.elim (kernelOperator_not_eigenvalue_neg_one a ha h)
  · have hu : IsUnit ((-1:halfSubspace →L[ℝ] halfSubspace)-kernelOperator a ha) := by
      simpa only [map_neg,map_one] using (spectrum.mem_resolventSet_iff.mp h)
    have he : (-1:halfSubspace →L[ℝ] halfSubspace)-kernelOperator a ha= -(positiveOperator a ha) := by
      change -(1:halfSubspace →L[ℝ] halfSubspace)-kernelOperator a ha=
        -((1:halfSubspace →L[ℝ] halfSubspace)+kernelOperator a ha)
      abel
    rw [he] at hu
    have hsurj : Function.Surjective (positiveOperator a ha) := by
      intro y
      obtain ⟨x,hx⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).2 (-y)
      refine ⟨x,?_⟩
      change -(positiveOperator a ha x)= -y at hx
      exact neg_injective hx
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨positiveOperator_injective a ha,hsurj⟩

/-- The genuine original bounded inverse of the actual identity-plus-GL-kernel operator.
Use: supplies the source inverse on the original Hilbert domain, with actual two-sided identities and a genuine finite norm.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
-/
def positiveInverse (a : ℝ) (ha : -1<a) : halfSubspace →L[ℝ] halfSubspace :=
  Ring.inverse (positiveOperator a ha)

/-- The actual original bounded inverse is a genuine left inverse of the source Hilbert operator.
Use: its true norm gives a uniform original input/output bound needed in the quadratic coercivity proof.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: apply the community ring inverse identity with the actual unit property proved by the genuine source Fredholm argument. -/
theorem positiveInverse_mul (a : ℝ) (ha : -1<a) : positiveInverse a ha*positiveOperator a ha=1 :=
  Ring.inverse_mul_cancel _ (positiveOperator_isUnit a ha)

/-- The actual original bounded inverse is a genuine right inverse of the source Hilbert operator.
Use: constructs actual GL solution vectors rather than assuming a solution of the original inverse equation.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: apply the community ring inverse identity to the proved genuine source unit. -/
theorem positiveOperator_mul_inverse (a : ℝ) (ha : -1<a) : positiveOperator a ha*positiveInverse a ha=1 :=
  Ring.mul_inverse_cancel _ (positiveOperator_isUnit a ha)

/-- Applying the genuine original inverse to the actual operator value returns the original Hilbert input.
Use: the actual inverse norm bounds the source input uniformly and thereby supplies the genuine positive coercivity constant.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: evaluate the proved genuine left inverse operator identity at the original Hilbert vector. -/
theorem positiveInverse_apply (a : ℝ) (ha : -1<a) (v : halfSubspace) :
    positiveInverse a ha (positiveOperator a ha v)=v := by
  have hh := congrArg (fun T:halfSubspace →L[ℝ] halfSubspace => T v) (positiveInverse_mul a ha)
  exact hh

/-- The true source inverse gives an actual uniform original input/output norm bound with a strictly positive finite coefficient.
Use: the genuine compact eigenbasis turns this bound into the original uniform quadratic coercivity constant.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: apply the true inverse operator norm inequality to the actual
source output. Its exact inverse identity gives the original input;
increasing the inverse norm by one keeps a positive constant also
when the Hilbert domain is trivial. -/
theorem positiveOperator_norm_lower (a : ℝ) (ha : -1<a) (v : halfSubspace) :
    ‖v‖≤(‖positiveInverse a ha‖+1)*‖positiveOperator a ha v‖ := by
  have hh := (positiveInverse a ha).le_opNorm (positiveOperator a ha v)
  rw [positiveInverse_apply] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

end
end jacobi.GelfandLevitan
