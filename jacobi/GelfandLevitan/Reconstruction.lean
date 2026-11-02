import jacobi.GelfandLevitan.SolutionRows
import jacobi.GelfandLevitan.CompressionContinuity

/-!
Article: jacobi, Proposition C.2.
The genuine inverse solution rows vary continuously in the original
Hilbert norm. Their actual pairings with the source kernel rows define
the original reconstruction formula, a continuous bounded function
on the entire physical square. The pointwise GL equation is proved
separately by identifying its prefix representative with k_t.
Use: the original reconstruction pairing gives a jointly continuous pointwise kernel, including at the genuine singular endpoint.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] kernel

/-- The original inverse solution row is continuous in its actual physical endpoint in the original L2 norm.
Use: the original reconstruction pairing gives a jointly continuous pointwise kernel, including at the genuine singular endpoint.
Article: jacobi, Proposition C.2.
Proof: the actual source Hilbert row is continuous, and its physical
projection depends jointly continuously on the endpoint and row.
The proved genuine inverse family is norm continuous, so continuous
operator evaluation and the actual overall minus sign finish. -/
theorem solutionRow_continuous (a : ℝ) (ha : -1<a) :
    Continuous (solutionRow a ha) := by
  -- Specify the actual source maps before composition to keep the infinite kernel and its inverse folded during elaboration.
  have hpair : Continuous (fun t:HalfInterval => ((t:ℝ),kernelRowVector a ha t)) :=
    continuous_subtype_val.prodMk (kernelRowVector a ha).continuous
  have hp : Continuous (fun t:HalfInterval =>
      cutoffProjection (t:ℝ) (kernelRowVector a ha t)) :=
    Continuous.comp (g := fun p:ℝ×halfSubspace => cutoffProjection p.1 p.2)
      (f := fun t:HalfInterval => ((t:ℝ),kernelRowVector a ha t))
      cutoffProjection_joint_continuous hpair
  have hi : Continuous (fun t:HalfInterval => compressedInverse a ha (t:ℝ)) :=
    (compressedInverse_continuous a ha).comp continuous_subtype_val
  exact (hi.clm_apply hp).neg

/-- The actual pointwise reconstruction from the original inverse GL rows and source kernel.
Use: this continuous source function is subsequently identified with the unique original GL solution, and determines the transformed source solution u.
Article: jacobi, Proposition C.2.
-/
def transformationKernel (a : ℝ) (ha : -1<a) (t s : HalfInterval) : ℝ :=
  -kernel a ha (t:ℝ) (s:ℝ)-inner ℝ (kernelRowVector a ha s) (solutionRow a ha t)

/-- The reconstructed original kernel is jointly continuous over the entire genuine physical square.
Use: restricts to the original GL triangle and justifies parameter integrals and endpoint limits of the transformed source solutions.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the original kernel is continuous on the physical square;
its genuine Hilbert source rows and actual inverse solution rows are
continuous. The original inner product is continuous in both entries,
so their exact reconstruction pairing is jointly continuous. -/
theorem transformationKernel_continuous (a : ℝ) (ha : -1<a) :
    Continuous (fun p:HalfInterval×HalfInterval => transformationKernel a ha p.1 p.2) := by
  have hF : Continuous (fun p:HalfInterval×HalfInterval => kernel a ha (p.1:ℝ) (p.2:ℝ)) :=
    ContinuousOn.comp_continuous
      (g := fun p:ℝ×ℝ => kernel a ha p.1 p.2)
      (kernel_continuousOn a ha)
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
      (fun p => ⟨p.1.property,p.2.property⟩)
  exact hF.neg.sub (((kernelRowVector a ha).continuous.comp continuous_snd).inner
    ((solutionRow_continuous a ha).comp continuous_fst))

/-- The actual reconstructed original GL kernel has a finite positive uniform pointwise bound.
Use: all original triangular kernel integrals exist and their true endpoint and series estimates have a genuine uniform constant.
Article: jacobi, Proposition C.2.
Proof: the reconstructed source kernel is continuous on the original compact physical square; its actual supremum norm plus one gives a positive common bound. -/
theorem transformationKernel_bounded (a : ℝ) (ha : -1<a) :
    ∃ B:ℝ,0<B ∧ ∀ t s:HalfInterval,|transformationKernel a ha t s|≤B := by
  let K : C(HalfInterval×HalfInterval,ℝ) :=
    ⟨fun p => transformationKernel a ha p.1 p.2,transformationKernel_continuous a ha⟩
  refine ⟨‖K‖+1,by positivity,fun t s => ?_⟩
  exact (K.norm_coe_le_norm (t,s)).trans (by linarith)

/-- The original reconstruction has exactly the literal source spatial integral formula.
Use: after identifying k_t with the actual prefix representative of K, this becomes the original pointwise GL equation.
Article: jacobi, Proposition C.2.
Proof: the genuine Hilbert source row pairing is the already proved actual kernel integral. Source kernel symmetry puts it in the printed original variable order. -/
theorem transformationKernel_reconstruction (a : ℝ) (ha : -1<a) (t s : HalfInterval) :
    transformationKernel a ha t s= -kernel a ha (t:ℝ) (s:ℝ)-
      ∫ r:Interval,(solutionRow a ha t:Space) r*kernel a ha (halfTime r) (s:ℝ) := by
  rw [transformationKernel,kernelRowVector_inner]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun r => by dsimp only; rw [kernel_symmetric])

/-- The reconstructed original kernel vanishes at its actual left endpoint.
Use: fixes the original GL endpoint and the transformed source branch normalization.
Article: jacobi, Proposition C.2.
Proof: the original source zero row and true inverse zero row both vanish; the exact reconstruction formula therefore vanishes. -/
theorem transformationKernel_zero (a : ℝ) (ha : -1<a) (s : HalfInterval) :
    transformationKernel a ha halfZero s=0 := by
  rw [transformationKernel,solutionRow_zero,inner_zero_right]
  change -kernel a ha 0 (s:ℝ)-0=0
  rw [kernel_zero,neg_zero,sub_zero]

end
end jacobi.GelfandLevitan
