import jacobi.GelfandLevitan.ForcedRows

/-!
Article: jacobi, Theorem 2.1.
The original inhomogeneous inverse row has a genuine continuous
spatial reconstruction. It solves the exact forced GL equation and
depends continuously in uniform norm on the actual endpoint and
continuous forcing. This is the same reconstruction mechanism used
for K, applied to its original derivative forcing.
Use: the derivative forcing dot F+w*F produces the original continuous candidate for partial_t K, while difference-quotient forcings use precisely the same proved reconstruction.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] kernel

/-- The genuine continuous reconstruction of the original forced GL inverse row.
Use: the derivative forcing dot F+w*F produces the original continuous candidate for partial_t K, while difference-quotient forcings use precisely the same proved reconstruction.
Article: jacobi, Theorem 2.1.
-/
def forcedKernel (a : ℝ) (ha : -1<a) (t : HalfInterval) (g : C(Interval,ℝ)) : C(Interval,ℝ) :=
  -g-kernelActionMap a ha (forcedRow a ha t g)

/-- The actual forced inverse row is exactly the zero-extended original continuous reconstruction on its physical prefix.
Use: forcedKernel_GL identifies the actual inverse equation with the literal original forced spatial GL equation, including every physical point.
Article: jacobi, Theorem 2.1.
Proof: on the prefix the true almost-everywhere forced row equation gives the reconstruction formula. Outside it the original vector vanishes because it is fixed by the actual cutoff projection. -/
theorem forcedKernel_representative (a : ℝ) (ha : -1<a) (t : HalfInterval) (g : C(Interval,ℝ)) :
    (forcedRow a ha t g:Space)=ᵐ[volume] (prefixSet (t:ℝ)).indicator (forcedKernel a ha t g) := by
  -- The quotient-space representative is identified on its genuine prefix and on its genuine zero extension separately.
  have hmem : forcedRow a ha t g∈cutoffSubspace (t:ℝ) := by
    rw [← forcedRow_projected a ha t g]
    exact cutoffProjection_mem _ _
  filter_upwards [forcedRow_spatial_equation a ha t g,(mem_cutoffSubspace_iff _ _).mp hmem] with s he hs
  by_cases hst : s∈prefixSet (t:ℝ)
  · rw [indicator_of_mem hst]
    have hh := he hst
    change (forcedRow a ha t g:Space) s= -g s-kernelActionMap a ha (forcedRow a ha t g) s
    linarith
  · rw [indicator_of_notMem hst]
    exact hs (lt_of_not_ge hst)

/-- The original continuous forced reconstruction satisfies the literal physical-prefix inhomogeneous GL equation.
Use: supplies the actual differentiated-equation solution once the original derivative forcing is inserted; exact GL difference quotients can be compared to the same reconstruction.
Article: jacobi, Theorem 2.1.
Proof: the genuine kernel action is its proved original integral pairing. Replace the true inverse row by its actual prefix-indicator continuous representative and apply the community indicator integral identity. -/
theorem forcedKernel_GL (a : ℝ) (ha : -1<a) (t : HalfInterval) (g : C(Interval,ℝ)) (s : Interval) :
    forcedKernel a ha t g s+g s+
      (∫ r : Interval in prefixSet (t:ℝ),forcedKernel a ha t g r*
        kernel a ha (halfTime s) (halfTime r))=0 := by
  -- The original spatial integral uses the actual physical prefix, without an operator normalization change.
  have hi : kernelActionMap a ha (forcedRow a ha t g) s=
      ∫ r : Interval in prefixSet (t:ℝ),forcedKernel a ha t g r*kernel a ha (halfTime s) (halfTime r) := by
    change inner ℝ (kernelRowVector a ha (halfClamp s)) (forcedRow a ha t g)=_
    rw [kernelRowVector_inner,← integral_indicator (prefixSet_measurable (t:ℝ))]
    apply integral_congr_ae
    filter_upwards [forcedKernel_representative a ha t g] with r hr
    rw [hr]
    by_cases hp : r∈prefixSet (t:ℝ)
    · rw [indicator_of_mem hp,indicator_of_mem hp]
      rfl
    · rw [indicator_of_notMem hp,indicator_of_notMem hp,zero_mul]
  change -g s-kernelActionMap a ha (forcedRow a ha t g) s+g s+_=0
  rw [← hi]
  ring

/-- The genuine continuous original forced reconstruction varies jointly continuously in uniform norm with its physical endpoint and true forcing.
Use: continuous derivative forcings yield continuous spatial derivative candidates, and actual uniform forcing limits pass through this same original inverse and reconstruction.
Article: jacobi, Theorem 2.1.
Proof: the genuine forced Hilbert inverse row is jointly continuous, and the already constructed actual integral-kernel action is a bounded linear map into continuous functions with their genuine uniform norm. Subtract its continuous image from the original continuous forcing. -/
theorem forcedKernel_joint_continuous (a : ℝ) (ha : -1<a) :
    Continuous (fun p : HalfInterval × C(Interval,ℝ) => forcedKernel a ha p.1 p.2) :=
  continuous_snd.neg.sub ((kernelActionCLM a ha).continuous.comp (forcedRow_joint_continuous a ha))

end
end jacobi.GelfandLevitan
