import jacobi.Analytic.L2Kernel

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The complex GL operators act on the genuine physical prefix L2 spaces.
Orthogonal projection restricts the output to that prefix; its pairing
with a prefix input is exactly the original kernel double integral.
Their perturbation bound is uniform in the endpoint.
Use: supplies precisely F_t on L2(0,t) in the uniform inverse estimate.
-/
namespace jacobi.Analytic
noncomputable section
open Set MeasureTheory Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- The actual integral-kernel part on the genuine complex physical prefix.
Use: supplies precisely F_t on L2(0,t) in the uniform inverse estimate.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def complexPrefixKernel (F : C(KernelSquare,ℂ)) (t : ℝ) : complexPrefix t →L[ℂ] complexPrefix t :=
  (complexPrefix t).orthogonalProjectionOnto ∘L complexKernelOperator F ∘L (complexPrefix t).subtypeL

/-- The actual continued complex GL operator on its original physical prefix domain.
Use: its genuine inverse and uniform norm estimate are the remaining operator assertion in Appendix E.1.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def complexPrefixPositive (F : C(KernelSquare,ℂ)) (t : ℝ) : complexPrefix t →L[ℂ] complexPrefix t :=
  1+complexPrefixKernel F t

/-- The prefix integral operator norm is bounded by the kernel norm uniformly in the physical endpoint.
Use: the same kernel continuity neighborhood controls every actual operator F_t simultaneously.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: both the orthogonal projection and the subspace inclusion are contractions; use the proved bound for the genuine ambient kernel operator. -/
theorem complexPrefixKernel_norm (F : C(KernelSquare,ℂ)) (t : ℝ) :
    ‖complexPrefixKernel F t‖≤‖F‖ := by
  -- The physical compression is a contraction on both sides of the same actual kernel action.
  apply (complexPrefixKernel F t).opNorm_le_bound (norm_nonneg F)
  intro v
  have hp := (complexPrefix t).orthogonalProjectionOnto.le_of_opNorm_le
    (complexPrefix t).orthogonalProjectionOnto_norm_le (complexKernelOperator F (v:ComplexL2))
  have hk := (complexKernelOperator F).le_of_opNorm_le (complexKernelOperator_norm F) (v:ComplexL2)
  change ‖(complexPrefix t).orthogonalProjectionOnto (complexKernelOperator F (v:ComplexL2))‖≤_
  rw [one_mul] at hp
  exact hp.trans hk

/-- The genuine GL operator difference equals the compression of the true kernel difference.
Use: turns uniform kernel continuity into uniform operator perturbation for all t.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the literal kernel integral preserves subtraction; both interval projections are linear, and the identity terms cancel. -/
theorem complexPrefixPositive_sub (F G : C(KernelSquare,ℂ)) (t : ℝ) :
    complexPrefixPositive F t-complexPrefixPositive G t=complexPrefixKernel (F-G) t := by
  -- Cancel the unchanged identity operator before using literal kernel linearity.
  apply ContinuousLinearMap.ext
  intro v
  change v+(complexPrefix t).orthogonalProjectionOnto (complexKernelOperator F (v:ComplexL2))-
    (v+(complexPrefix t).orthogonalProjectionOnto (complexKernelOperator G (v:ComplexL2)))=
      (complexPrefix t).orthogonalProjectionOnto (complexKernelOperator (F-G) (v:ComplexL2))
  rw [complexKernelOperator_sub]
  change _=(complexPrefix t).orthogonalProjectionOnto
    (complexKernelOperator F (v:ComplexL2)-complexKernelOperator G (v:ComplexL2))
  rw [map_sub]
  abel

/-- The true physical GL perturbation is bounded by the actual uniform kernel difference, independently of t.
Use: chooses one complex order disk for the inverse bound on every physical L2 interval.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: identify the exact kernel-difference compression and apply its contraction bound. -/
theorem complexPrefixPositive_dist (F G : C(KernelSquare,ℂ)) (t : ℝ) :
    ‖complexPrefixPositive F t-complexPrefixPositive G t‖≤‖F-G‖ := by
  rw [complexPrefixPositive_sub]
  exact complexPrefixKernel_norm _ _

/-- The actual compressed GL quadratic form is the genuine complex L2 norm plus the original kernel integral.
Use: identifies its real part with the two original real forms at the base order.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual orthogonal projection preserves pairing with a true prefix input. The proved ambient operator pairing then gives the literal double integral. -/
theorem complexPrefixPositive_inner (F : C(KernelSquare,ℂ)) (t : ℝ) (v : complexPrefix t) :
    inner ℂ v (complexPrefixPositive F t v)=(‖v‖^2:ℂ)+∫ p:Interval×Interval,
      (star ((v:ComplexL2) p.1)*(v:ComplexL2) p.2)*F (halfClamp p.1,halfClamp p.2)
        ∂(volume.prod volume) := by
  change inner ℂ v (v+(complexPrefix t).orthogonalProjectionOnto
    (complexKernelOperator F (v:ComplexL2)))=_
  rw [inner_add_right,inner_self_eq_norm_sq_to_K,
    (complexPrefix t).inner_orthogonalProjectionOnto_eq_of_mem_left,complexKernelOperator_inner]
  norm_cast

end
end jacobi.Analytic
