import jacobi.GelfandLevitan.CompressionContinuity

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The literal finite spectral prefixes of F give compressed operators
converging uniformly in the physical endpoint to the original A_t.
Their genuine coercivity, invertibility and common inverse bound follow
from the already proved original coercivity, rather than being premises
of the finite approximation argument.
Use: the finite approximation uses the same original topology and norm as compressedPositive.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] rankCorrection kernelOperator

/-- The existing original Hilbert seminormed structure, cached for typeclass inference through the nested physical support subtype.
Use: the finite approximation uses the same original topology and norm as compressedPositive.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
local instance : SeminormedAddCommGroup halfSubspace := inferInstance

/-- The existing original operator-norm structure, cached for continuity inference.
Use: norm convergence of the genuine spectral prefixes gives the actual finite compressed coercivity threshold.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
local instance : SeminormedAddCommGroup (halfSubspace →L[ℝ] halfSubspace) := inferInstance

/-- The actual finite spectral prefix of the original source GL operator.
Use: finiteCompressedPositive supplies precisely the finite-sum GL equations used in the original differential-equation approximation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteKernelOperator (a : ℝ) (ha : -1<a) (N : ℕ) : halfSubspace →L[ℝ] halfSubspace :=
  ∑ k∈Finset.range N,rankCorrection a ha k

/-- The actual original finite-sum GL operator compressed to its unchanged physical prefix.
Use: finiteCompressedPositive_coercive proves invertibility uniformly in the physical endpoint for all sufficiently large spectral prefixes.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteCompressedPositive (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) : halfSubspace →L[ℝ] halfSubspace :=
  ContinuousLinearMap.id ℝ halfSubspace+cutoffProjection t ∘L finiteKernelOperator a ha N ∘L cutoffProjection t

/-- The actual finite-prefix inverse, whose genuine inverse identities are proved for all sufficiently large prefixes.
Use: constructs the original finite inverse rows after finiteCompressedPositive_isUnit has discharged their invertibility.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteCompressedInverse (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) : halfSubspace →L[ℝ] halfSubspace :=
  Ring.inverse (finiteCompressedPositive a ha N t)

/-- Compression does not increase the actual operator-norm error of a genuine original spectral prefix.
Use: transfers the proved original spectral convergence to every physical prefix with one common error bound.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the original difference is exactly P_t(F^(N)-F)P_t and the genuine orthogonal cutoff has norm at most one. -/
theorem finiteCompressedPositive_error (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) :
    ‖finiteCompressedPositive a ha N t-compressedPositive a ha t‖≤
      ‖finiteKernelOperator a ha N-kernelOperator a ha‖ := by
  -- Both copies of the actual cutoff are contractions on the same original Hilbert space.
  have he : finiteCompressedPositive a ha N t-compressedPositive a ha t=
      cutoffProjection t*(finiteKernelOperator a ha N-kernelOperator a ha)*cutoffProjection t := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [finiteCompressedPositive,compressedPositive,compressedKernel,add_apply,sub_apply,
      ContinuousLinearMap.comp_apply,mul_apply_eq_comp,map_sub]
    abel
  rw [he]
  have hP := cutoffProjection_norm_le t
  calc
    _ ≤ (‖cutoffProjection t‖*‖finiteKernelOperator a ha N-kernelOperator a ha‖)*‖cutoffProjection t‖ :=
      (norm_mul_le (cutoffProjection t*(finiteKernelOperator a ha N-kernelOperator a ha)) (cutoffProjection t)).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le (cutoffProjection t) (finiteKernelOperator a ha N-kernelOperator a ha)) (norm_nonneg _))
    _ ≤ (1*‖finiteKernelOperator a ha N-kernelOperator a ha‖)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hP (norm_nonneg (finiteKernelOperator a ha N-kernelOperator a ha)))
        hP (norm_nonneg (cutoffProjection t)) (by positivity)
    _ = _ := by ring

/-- The genuine original finite spectral prefixes have one positive coercivity constant for every physical endpoint once the prefix is sufficiently large.
Use: discharges both the original finite GL invertibility and the uniform inverse bound needed to construct and compare the actual K^(N).
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the original A_t has one proved positive coercivity constant. The genuine spectral error tends to zero in operator norm; compression does not increase it. Hilbert Cauchy--Schwarz bounds its quadratic error, leaving half the original coercivity for every physical t. -/
theorem finiteCompressedPositive_coercive (a : ℝ) (ha : -1<a) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,∀ t : ℝ,∀ v : halfSubspace,
      c*‖v‖^2≤ inner ℝ (finiteCompressedPositive a ha N t v) v := by
  -- The convergence threshold depends only on the original spectral tail, not on the physical endpoint.
  obtain ⟨c,hc,hA⟩ := compressedPositive_coercive a ha
  have he : Tendsto (fun N => ‖finiteKernelOperator a ha N-kernelOperator a ha‖) atTop (𝓝 (0:ℝ)) := by
    simpa only [finiteKernelOperator,sub_self,norm_zero] using
      ((kernelOperator_limit a ha).sub (tendsto_const_nhds (x := kernelOperator a ha))).norm
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [(tendsto_order.mp he).2 (c/2) (by positivity)] with N hN t v
  have hD := finiteCompressedPositive_error a ha N t
  have hb : |inner ℝ ((finiteCompressedPositive a ha N t-compressedPositive a ha t) v) v|≤
      ‖finiteKernelOperator a ha N-kernelOperator a ha‖*‖v‖^2 := by
    calc
      _ ≤ ‖(finiteCompressedPositive a ha N t-compressedPositive a ha t) v‖*‖v‖ :=
        by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) _ v
      _ ≤ (‖finiteCompressedPositive a ha N t-compressedPositive a ha t‖*‖v‖)*‖v‖ :=
        mul_le_mul_of_nonneg_right ((finiteCompressedPositive a ha N t-compressedPositive a ha t).le_opNorm v) (norm_nonneg v)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hD (sq_nonneg ‖v‖)]
  rw [sub_apply,inner_sub_left] at hb
  have hlow := neg_abs_le (inner ℝ (finiteCompressedPositive a ha N t v) v-inner ℝ (compressedPositive a ha t v) v)
  have hsmall := mul_le_mul_of_nonneg_right hN.le (sq_nonneg ‖v‖)
  nlinarith [hA t v]

/-- Every sufficiently long original finite spectral prefix is genuinely invertible at every physical endpoint, with a common positive operator-norm bound on its actual inverse.
Use: supplies the actual finite inverse family used in the original finite transformation kernels and their limiting differential equation, with no unproved inverse hypothesis.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: mathlib's coercive Hilbert-operator inverse theorem.
Proof: apply the community inverse theorem to the proved actual uniform finite coercivity. Cauchy--Schwarz then bounds each genuine inverse image by the reciprocal of that same positive constant, independently of N and t. -/
theorem finiteCompressedPositive_isUnit (a : ℝ) (ha : -1<a) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ N : ℕ in atTop,∀ t : ℝ,
      IsUnit (finiteCompressedPositive a ha N t) ∧ ‖finiteCompressedInverse a ha N t‖≤B := by
  -- Invertibility and the bound are derived from the same actual finite coercivity estimate.
  obtain ⟨c,hc,hA⟩ := finiteCompressedPositive_coercive a ha
  refine ⟨1/c,by positivity,?_⟩
  filter_upwards [hA] with N hN t
  have hu : IsUnit (finiteCompressedPositive a ha N t) := by
    apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
      (finiteCompressedPositive a ha N t) (c := ⟨c,hc.le⟩) (by exact_mod_cast hc)
    intro v
    rw [Real.norm_eq_abs]
    exact (by nlinarith [hN t v] : ‖v‖^2*c≤ inner ℝ (finiteCompressedPositive a ha N t v) v).trans (le_abs_self _)
  refine ⟨hu,?_⟩
  apply (finiteCompressedInverse a ha N t).opNorm_le_bound (by positivity)
  intro v
  let x := finiteCompressedInverse a ha N t v
  have hright : finiteCompressedPositive a ha N t x=v :=
    congrArg (fun T : halfSubspace →L[ℝ] halfSubspace => T v) (Ring.mul_inverse_cancel _ hu)
  have hb := (hN t x).trans (le_abs_self _)
  have hi : |inner ℝ (finiteCompressedPositive a ha N t x) x|≤‖v‖*‖x‖ := by
    rw [hright]
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) v x
  by_cases hx : x=0
  · change ‖x‖≤_
    rw [hx,norm_zero]
    positivity
  · have hn : 0<‖x‖ := norm_pos_iff.mpr hx
    have hnorm : c*‖x‖≤‖v‖ := by nlinarith
    change ‖x‖≤_
    calc
      _ ≤ ‖v‖/c := (le_div_iff₀ hc).mpr (by nlinarith)
      _ = _ := by ring

end
end jacobi.GelfandLevitan
