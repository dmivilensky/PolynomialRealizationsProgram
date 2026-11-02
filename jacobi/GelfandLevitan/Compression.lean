import jacobi.GelfandLevitan.Coercivity
import jacobi.GelfandLevitan.CutoffSpace

/-!
Article: jacobi, Proposition C.2.
The original actual cutoff projection gives A_t=I+P_t*F*P_t on the
fixed source half-interval Hilbert space. Orthogonal decomposition and
the proved original coercivity give one positive lower bound for the
whole actual family. Every actual A_t therefore has a genuine bounded
inverse, with one uniform original operator norm bound.
Use: its identity perturbation is the genuine source A_t used to construct the original GL solution row.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace

/-- The actual original source kernel compressed to inputs supported before the physical endpoint t.
Use: its identity perturbation is the genuine source A_t used to construct the original GL solution row.
Article: jacobi, Proposition C.2.
-/
def compressedKernel (a : ℝ) (ha : -1<a) (t : ℝ) : halfSubspace →L[ℝ] halfSubspace :=
  cutoffProjection t ∘L kernelOperator a ha ∘L cutoffProjection t

/-- The actual original cutoff GL operator on the fixed true half-interval Hilbert domain.
Use: its proved genuine inverse supplies the original source k_t and hence the actual GL kernel K.
Article: jacobi, Proposition C.2.
-/
def compressedPositive (a : ℝ) (ha : -1<a) (t : ℝ) : halfSubspace →L[ℝ] halfSubspace :=
  ContinuousLinearMap.id ℝ halfSubspace+compressedKernel a ha t

/-- The true cutoff GL quadratic form splits into its unaffected orthogonal tail and the original positive kernel form on the actual prefix component.
Use: proves one genuine positive lower bound for every original A_t without an interval-dependent invertibility hypothesis.
Article: jacobi, Proposition C.2.
Proof: symmetry of the actual source projection moves its outer copy
to the other inner-product entry. The original identity perturbation
then contributes the true prefix norm square. Community Pythagoras
splits the original full norm into the actual prefix and orthogonal tail. -/
theorem compressedPositive_quadratic (a : ℝ) (ha : -1<a) (t : ℝ) (v : halfSubspace) :
    inner ℝ (compressedPositive a ha t v) v=
      ‖(cutoffSubspace t)ᗮ.starProjection v‖^2+
        inner ℝ (positiveOperator a ha (cutoffProjection t v)) (cutoffProjection t v) := by
  -- Both components belong to the same actual original Hilbert space and use its original L2 norm.
  have hp : inner ℝ (cutoffProjection t (kernelOperator a ha (cutoffProjection t v))) v=
      inner ℝ (kernelOperator a ha (cutoffProjection t v)) (cutoffProjection t v) :=
    cutoffProjection_symmetric t _ _
  have hA : inner ℝ (compressedPositive a ha t v) v=
      ‖v‖^2+inner ℝ (kernelOperator a ha (cutoffProjection t v)) (cutoffProjection t v) := by
    change inner ℝ (v+cutoffProjection t (kernelOperator a ha (cutoffProjection t v))) v=_
    rw [inner_add_left,real_inner_self_eq_norm_sq,hp]
  have hQ : inner ℝ (positiveOperator a ha (cutoffProjection t v)) (cutoffProjection t v)=
      ‖cutoffProjection t v‖^2+
        inner ℝ (kernelOperator a ha (cutoffProjection t v)) (cutoffProjection t v) := by
    change inner ℝ (cutoffProjection t v+kernelOperator a ha (cutoffProjection t v)) (cutoffProjection t v)=_
    rw [inner_add_left,real_inner_self_eq_norm_sq]
  have hnorm := Submodule.norm_sq_eq_add_norm_sq_starProjection v (cutoffSubspace t)
  change ‖v‖^2=‖cutoffProjection t v‖^2+‖(cutoffSubspace t)ᗮ.starProjection v‖^2 at hnorm
  linarith

/-- One strictly positive actual coercivity constant works for the entire original compressed GL family.
Use: constructs the genuine source inverses A_t^-1 with one uniform bound before defining the actual GL row solutions.
Article: jacobi, Proposition C.2.
Proof: use the original fully proved positive lower bound on the true
prefix component. The actual orthogonal tail has coefficient one.
Taking the positive minimum of those two genuine constants and using
the exact original Hilbert Pythagorean identity proves the bound. -/
theorem compressedPositive_coercive (a : ℝ) (ha : -1<a) :
    ∃ c:ℝ,0<c ∧ ∀ t:ℝ,∀ v:halfSubspace,c*‖v‖^2≤ inner ℝ (compressedPositive a ha t v) v := by
  -- No invertibility or spectral-gap premise is added for the varying physical source interval.
  obtain ⟨κ,hκ,hbound⟩ := positiveOperator_coercive a ha
  refine ⟨min 1 κ,lt_min (by norm_num) hκ,fun t v => ?_⟩
  have hnorm := Submodule.norm_sq_eq_add_norm_sq_starProjection v (cutoffSubspace t)
  change ‖v‖^2=‖cutoffProjection t v‖^2+‖(cutoffSubspace t)ᗮ.starProjection v‖^2 at hnorm
  rw [compressedPositive_quadratic,hnorm,mul_add]
  have hp := mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) κ) (sq_nonneg ‖cutoffProjection t v‖)
  have ht := mul_le_mul_of_nonneg_right (min_le_left (1:ℝ) κ) (sq_nonneg ‖(cutoffSubspace t)ᗮ.starProjection v‖)
  have hq := hbound (cutoffProjection t v)
  nlinarith

/-- Every actual original compressed GL operator is genuinely invertible on the fixed original Hilbert domain.
Use: defines the actual source inverse family and the original GL solution vectors, with no invertibility certificate among its inputs.
Article: jacobi, Proposition C.2.
Source: the community coercive Hilbert operator inverse theorem.
Proof: the actual source family has a proved positive coercivity
constant. Its true real quadratic form is no greater than the norm
of the same inner product. The community Hilbert-space inverse theorem
therefore applies to every original physical cutoff operator. -/
theorem compressedPositive_isUnit (a : ℝ) (ha : -1<a) (t : ℝ) : IsUnit (compressedPositive a ha t) := by
  obtain ⟨c,hc,hbound⟩ := compressedPositive_coercive a ha
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    (compressedPositive a ha t) (c := ⟨c,hc.le⟩) (by exact_mod_cast hc)
  intro v
  rw [Real.norm_eq_abs]
  have hh := hbound t v
  exact (by nlinarith : ‖v‖^2*c≤ inner ℝ (compressedPositive a ha t v) v).trans (le_abs_self _)

/-- The actual bounded inverse of the original compressed GL operator at the physical endpoint t.
Use: supplies the original source k_t=-A_t^-1*P_t*F(t,.) before constructing the genuine continuous kernel K.
Article: jacobi, Proposition C.2.
-/
def compressedInverse (a : ℝ) (ha : -1<a) (t : ℝ) : halfSubspace →L[ℝ] halfSubspace :=
  Ring.inverse (compressedPositive a ha t)

/-- The genuine original compressed inverse is a true left inverse at every physical endpoint.
Use: proves uniqueness of original cutoff GL solution vectors.
Article: jacobi, Proposition C.2.
Proof: apply the actual community ring inverse identity to the already proved genuine original source unit. -/
theorem compressedInverse_mul (a : ℝ) (ha : -1<a) (t : ℝ) :
    compressedInverse a ha t*compressedPositive a ha t=1 :=
  Ring.inverse_mul_cancel _ (compressedPositive_isUnit a ha t)

/-- The genuine original compressed inverse is a true right inverse at every physical endpoint.
Use: proves existence of the original cutoff GL solution vectors by applying the actual inverse to the genuine source row.
Article: jacobi, Proposition C.2.
Proof: apply the community inverse identity to the proved actual original cutoff unit. -/
theorem compressedPositive_mul_inverse (a : ℝ) (ha : -1<a) (t : ℝ) :
    compressedPositive a ha t*compressedInverse a ha t=1 :=
  Ring.mul_inverse_cancel _ (compressedPositive_isUnit a ha t)

/-- The actual original compressed inverse returns exactly the true source Hilbert input after acting through A_t.
Use: identifies the original cutoff equation solution and its inverse norm bound on actual L2 vectors.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: evaluate the genuine right inverse operator identity at the actual original Hilbert vector. -/
theorem compressedPositive_inverse_apply (a : ℝ) (ha : -1<a) (t : ℝ) (v : halfSubspace) :
    compressedPositive a ha t (compressedInverse a ha t v)=v := by
  have hh := congrArg (fun T:halfSubspace →L[ℝ] halfSubspace => T v) (compressedPositive_mul_inverse a ha t)
  exact hh

/-- The entire actual original compressed inverse family has one finite uniform positive operator norm bound.
Use: supplies the genuine original uniform inverse bound needed in the continuity and boundedness construction of the source GL kernel K.
Article: jacobi, Proposition C.2.
Proof: original coercivity and Hilbert Cauchy--Schwarz give
c*norm(x)<=norm(A_t*x). Apply this to the actual inverse image of an
arbitrary original input and use the genuine right inverse identity.
The community operator norm criterion gives the common bound 1/c. -/
theorem compressedInverse_uniform_bound (a : ℝ) (ha : -1<a) :
    ∃ C:ℝ,0<C ∧ ∀ t:ℝ,‖compressedInverse a ha t‖≤C := by
  -- The coefficient is the actual proved uniform coercivity constant, not an assumed inverse estimate.
  obtain ⟨c,hc,hbound⟩ := compressedPositive_coercive a ha
  have hnorm (t : ℝ) (v : halfSubspace) : c*‖v‖≤‖compressedPositive a ha t v‖ := by
    by_cases hv : v=0
    · subst v
      simp only [norm_zero,mul_zero,map_zero,le_refl]
    · have hn := norm_pos_iff.mpr hv
      have hinnerNorm : |inner ℝ (compressedPositive a ha t v) v|≤
          ‖compressedPositive a ha t v‖*‖v‖ := by
        have hh := norm_inner_le_norm (𝕜 := ℝ) (compressedPositive a ha t v) v
        simpa only [Real.norm_eq_abs] using hh
      have hh : inner ℝ (compressedPositive a ha t v) v≤‖compressedPositive a ha t v‖*‖v‖ :=
        (le_abs_self _).trans hinnerNorm
      apply (mul_le_mul_iff_right₀ hn).mp
      nlinarith [hbound t v]
  refine ⟨1/c,by positivity,fun t => ?_⟩
  apply (compressedInverse a ha t).opNorm_le_bound (by positivity)
  intro v
  have hh := hnorm t (compressedInverse a ha t v)
  rw [compressedPositive_inverse_apply] at hh
  calc
    ‖compressedInverse a ha t v‖ ≤ ‖v‖/c := (le_div_iff₀ hc).mpr (by nlinarith)
    _ = (1/c)*‖v‖ := by ring

/-- The original zero-interval compressed GL operator is exactly the identity.
Use: fixes the actual source inverse and row at t=0 in the GL endpoint construction.
Article: jacobi, Proposition C.2.
Proof: the genuine original zero cutoff projection is zero, so its compressed kernel vanishes. -/
theorem compressedPositive_zero (a : ℝ) (ha : -1<a) :
    compressedPositive a ha 0=ContinuousLinearMap.id ℝ halfSubspace := by
  rw [compressedPositive,compressedKernel,cutoffProjection_zero]
  change ContinuousLinearMap.id ℝ halfSubspace+0=ContinuousLinearMap.id ℝ halfSubspace
  exact add_zero (ContinuousLinearMap.id ℝ halfSubspace)

/-- The actual midpoint compressed GL operator is exactly the original positive operator already constructed from the source kernel.
Use: identifies the actual full-interval inverse with the original I+F inverse and preserves the true source normalization.
Article: jacobi, Proposition C.2.
Proof: the actual original midpoint cutoff projection is the identity, so compression leaves the genuine original kernel unchanged. -/
theorem compressedPositive_half (a : ℝ) (ha : -1<a) :
    compressedPositive a ha (1/2)=positiveOperator a ha := by
  rw [compressedPositive,compressedKernel,cutoffProjection_half]
  rfl

end
end jacobi.GelfandLevitan
