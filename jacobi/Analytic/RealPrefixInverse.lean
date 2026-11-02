import jacobi.Analytic.PrefixOperators
import jacobi.GelfandLevitan.ForcedUniqueness
import jacobi.GelfandLevitan.Triangle

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The original real GL inverse solves every continuous square forcing,
not just the particular kernel forcing. This proves invertibility on
one fixed continuous-kernel Banach space by reusing the genuine Hilbert
inverse and its already proved continuous spatial reconstruction.
Use: identifies the real base of the analytic operator family with the already proved original real GL problem.
-/
namespace jacobi.Analytic
noncomputable section
open Set MeasureTheory jacobi.Reference jacobi.GelfandLevitan
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] jacobi.GelfandLevitan.kernel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The original real GL kernel on its unaltered compact physical half square.
Use: identifies the real base of the analytic operator family with the already proved original real GL problem.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def realKernelMap (a : ℝ) (ha : -1<a) : C(KernelSquare,ℝ) :=
  ⟨fun p => jacobi.GelfandLevitan.kernel a ha p.1 p.2,
    (jacobi.GelfandLevitan.kernel_continuousOn a ha).comp_continuous
      (f := fun p : KernelSquare => ((p.1:ℝ),(p.2:ℝ)))
      (by fun_prop) (fun p => ⟨p.1.property,p.2.property⟩)⟩

/-- The original real identity-plus-prefix-integral operator on continuous physical square kernels.
Use: its genuine invertibility supplies the base point for the complex Banach inverse theorem.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def realGLoperator (a : ℝ) (ha : -1<a) : C(KernelSquare,ℝ) →L[ℝ] C(KernelSquare,ℝ) :=
  1+prefixOperator (realKernelMap a ha)

/-- Clamping a genuine point before the physical midpoint and including it back preserves its actual unit-interval coordinate.
Use: the continuous square forcing reconstruction has exactly the original forced GL integrand on each physical prefix.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the minimum with one half is the original coordinate, and subtype extensionality preserves that equality. -/
theorem halfInclusion_halfClamp {r : Interval} (hr : (r:ℝ)≤1/2) : halfInclusion (halfClamp r)=r :=
  Subtype.ext (min_eq_left hr)

/-- The full continuous forced equation determines the genuine inverse reconstruction at every spatial coordinate, including outside its physical prefix.
Use: proves injectivity of the real continuous-square GL operator, beyond its Hilbert-prefix restriction.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the already proved forced-prefix uniqueness identifies the candidate Hilbert vector. Its true kernel action is the original prefix integral; the full forcing equation then identifies the same continuous reconstruction at every point. -/
theorem continuous_forced_unique_all (a : ℝ) (ha : -1<a) (t : HalfInterval)
    (q b : C(Interval,ℝ))
    (hq : ∀ s : Interval,q s+b s+
      (∫ r : Interval in prefixSet (t:ℝ),q r* jacobi.GelfandLevitan.kernel a ha (halfTime s) (halfTime r))=0)
    (s : Interval) : q s=forcedKernel a ha t b s := by
  have hv := candidateVector_eq_forced a ha t q b (fun u _ => hq u)
  have haction := candidateVector_action a ha t q s
  rw [hv] at haction
  change q s= -b s-kernelActionMap a ha (forcedRow a ha t b) s
  rw [haction]
  linarith [hq s]

/-- The genuine continuous forced inverse is zero for zero forcing.
Use: uniqueness of the original forced rows proves injectivity of the real square GL operator.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual continuous-to-L2 embedding, projections, compressed inverse and integral reconstruction are linear and therefore map zero to zero. -/
theorem forcedKernel_zero (a : ℝ) (ha : -1<a) (t : HalfInterval) :
    forcedKernel a ha t 0=0 := by
  change -(0:C(Interval,ℝ))-kernelActionCLM a ha
    (-(compressedInverse a ha (t:ℝ) (cutoffProjection (t:ℝ)
      (halfSubspace.orthogonalProjectionOnto (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume 0)))))=0
  simp only [map_zero,neg_zero,sub_zero]

/-- The genuine continuous-square GL operator has the exact original forced row equation after evaluation at a clamped physical coordinate.
Use: compares arbitrary square candidates to the original forced Hilbert inverse and its reconstruction.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: evaluate the identity perturbation, use the proved original subtype prefix formula, and apply symmetry of the original real kernel. -/
theorem realGLoperator_row (a : ℝ) (ha : -1<a) (K : C(KernelSquare,ℝ))
    (t : HalfInterval) (s : Interval) :
    realGLoperator a ha K (t,halfClamp s)=K (t,halfClamp s)+
      ∫ r : Interval in prefixSet (t:ℝ),K (t,halfClamp r)*
        jacobi.GelfandLevitan.kernel a ha (halfTime s) (halfTime r) := by
  change K (t,halfClamp s)+prefixProduct K (realKernelMap a ha) (t,halfClamp s)=_
  rw [prefixProduct_subtype]
  congr 1
  apply setIntegral_congr_fun (prefixSet_measurable _)
  intro r _
  dsimp only [realKernelMap,ContinuousMap.coe_mk]
  rw [jacobi.GelfandLevitan.kernel_symmetric]
  rfl

/-- Every continuous square forcing has its genuine original real GL inverse reconstructed continuously in both physical coordinates.
Use: proves surjectivity of the actual real base operator, with no new solvability premise.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def realForcedSquare (a : ℝ) (ha : -1<a) (G : C(KernelSquare,ℝ)) : C(KernelSquare,ℝ) where
  toFun p := forcedKernel a ha p.1 (-((G.curry p.1).comp halfClamp)) (halfInclusion p.2)
  continuous_toFun := by
    -- The already proved original inverse is jointly continuous in endpoint and actual uniform-norm forcing.
    have hrows : Continuous (fun p : KernelSquare => -((G.curry p.1).comp halfClamp)) :=
      ((ContinuousMap.compCLM ℝ ℝ halfClamp).continuous.comp
        (G.curry.continuous.comp continuous_fst)).neg
    exact ((forcedKernel_joint_continuous a ha).comp (continuous_fst.prodMk hrows)).eval
      (halfInclusion.continuous.comp continuous_snd)

/-- The reconstructed square inverse solves the original continuous GL operator equation for every square forcing.
Use: proves surjectivity of the real base GL operator before analytic continuation.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the original forced reconstruction satisfies the literal GL equation. On its physical prefix the half clamp and inclusion preserve every original integration point, so its actual integral equals the square operator's prefix integral; symmetry gives the required source ordering. -/
theorem realForcedSquare_equation (a : ℝ) (ha : -1<a) (G : C(KernelSquare,ℝ)) :
    realGLoperator a ha (realForcedSquare a ha G)=G := by
  -- The square reconstruction uses the original inverse for the true physical forcing row.
  apply ContinuousMap.ext
  rintro ⟨t,s⟩
  have he := forcedKernel_GL a ha t (-((G.curry t).comp halfClamp)) (halfInclusion s)
  have hi : (∫ r : Interval in prefixSet (t:ℝ),realForcedSquare a ha G (t,halfClamp r)*
      jacobi.GelfandLevitan.kernel a ha (s:ℝ) (halfTime r))=
      ∫ r : Interval in prefixSet (t:ℝ),forcedKernel a ha t (-((G.curry t).comp halfClamp)) r*
        jacobi.GelfandLevitan.kernel a ha (halfTime (halfInclusion s)) (halfTime r) := by
    apply setIntegral_congr_fun (prefixSet_measurable _)
    intro r hr
    have hrh : (r:ℝ)≤1/2 := hr.trans t.property.2
    change forcedKernel a ha t _ (halfInclusion (halfClamp r))*_=_
    rw [halfInclusion_halfClamp hrh]
    rw [show halfTime (halfInclusion s)=(s:ℝ) from min_eq_left s.property.2]
  have hr := realGLoperator_row a ha (realForcedSquare a ha G) t (halfInclusion s)
  rw [halfClamp_halfInclusion,show halfTime (halfInclusion s)=(s:ℝ) from min_eq_left s.property.2,hi] at hr
  simp only [ContinuousMap.neg_apply,ContinuousMap.comp_apply,ContinuousMap.curry_apply,
    halfClamp_halfInclusion] at he
  change realGLoperator a ha (realForcedSquare a ha G) (t,s)=G (t,s)
  change realGLoperator a ha (realForcedSquare a ha G) (t,s)=
    forcedKernel a ha t (-((G.curry t).comp halfClamp)) (halfInclusion s)+_ at hr
  linarith

/-- The original real continuous-square GL operator is genuinely invertible.
Use: supplies the actual real base inverse for Appendix E.1, with all original positivity, coercivity and arbitrary-forcing solvability already discharged.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: reconstruct an inverse image for every square forcing using the proved original forced inverse. For injectivity, a homogeneous square candidate solves the actual full forced row equation; original forced uniqueness and zero forcing make every row zero. The community Banach operator theorem turns genuine bijectivity into a bounded inverse. -/
theorem realGLoperator_isUnit (a : ℝ) (ha : -1<a) : IsUnit (realGLoperator a ha) := by
  -- No inverse or regularity certificate is required: the original forced equation provides every inverse image.
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  constructor
  · have hzero (K : C(KernelSquare,ℝ)) (hK : realGLoperator a ha K=0) : K=0 := by
      apply ContinuousMap.ext
      rintro ⟨t,s⟩
      let q : C(Interval,ℝ) := (K.curry t).comp halfClamp
      have hq (u : Interval) : q u+(0:C(Interval,ℝ)) u+
          (∫ r : Interval in prefixSet (t:ℝ),q r* jacobi.GelfandLevitan.kernel a ha (halfTime u) (halfTime r))=0 := by
        have he := realGLoperator_row a ha K t u
        rw [hK,ContinuousMap.zero_apply] at he
        change _=q u+_ at he
        simpa only [q,ContinuousMap.comp_apply,ContinuousMap.curry_apply,
          ContinuousMap.zero_apply,add_zero] using he.symm
      have hu := continuous_forced_unique_all a ha t q 0 hq (halfInclusion s)
      rw [forcedKernel_zero,ContinuousMap.zero_apply] at hu
      simpa only [q,ContinuousMap.comp_apply,ContinuousMap.curry_apply,
        halfClamp_halfInclusion,ContinuousMap.zero_apply] using hu
    intro K L h
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub,h,sub_self]
  · intro G
    exact ⟨realForcedSquare a ha G,realForcedSquare_equation a ha G⟩

end
end jacobi.Analytic
