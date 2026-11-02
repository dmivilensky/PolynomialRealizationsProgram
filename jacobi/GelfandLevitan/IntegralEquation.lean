import jacobi.GelfandLevitan.Reconstruction
import jacobi.GelfandLevitan.KernelRepresentative

/-!
Article: jacobi, Proposition C.2.
The constructed continuous original kernel has the actual
inverse solution row as its physical prefix representative. Substitution
in the proved original reconstruction formula gives the literal source
GL integral equation, with the genuine physical interval and measure.
Use: substitutes the original continuous K for k_t in the genuine reconstruction integral, proving the printed pointwise GL equation.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] kernel

/-- The original inverse solution row is precisely the physical-prefix representative of the constructed continuous kernel.
Use: substitutes the original continuous K for k_t in the genuine reconstruction integral, proving the printed pointwise GL equation.
Article: jacobi, Proposition C.2.
Proof: on the actual prefix, the true spatial inverse equation is
exactly the reconstruction formula for K. Beyond that physical prefix,
the original inverse row vanishes by its proved source support, as
does the genuine indicator representative. -/
theorem solutionRow_representative (a : ℝ) (ha : -1<a) (t : HalfInterval) :
    (solutionRow a ha t:Space)=ᵐ[volume]
      (prefixSet (t:ℝ)).indicator
        (fun s:Interval => transformationKernel a ha t (halfClamp s)) := by
  -- The source row and continuous reconstruction are compared on their original physical prefix only.
  filter_upwards [solutionRow_spatial_equation a ha t,
    (mem_cutoffSubspace_iff _ _).mp (solutionRow_mem a ha t)] with s he hs
  by_cases hp : s∈prefixSet (t:ℝ)
  · rw [indicator_of_mem hp]
    have hh := he hp
    rw [kernelRows_apply] at hh
    change (solutionRow a ha t:Space) s+
      inner ℝ (kernelRowVector a ha (halfClamp s)) (solutionRow a ha t)=
        -kernel a ha (t:ℝ) (halfTime s) at hh
    change (solutionRow a ha t:Space) s=
      -kernel a ha (t:ℝ) (halfTime s)-
        inner ℝ (kernelRowVector a ha (halfClamp s)) (solutionRow a ha t)
    linarith
  · rw [indicator_of_notMem hp]
    exact hs (lt_of_not_ge hp)

/-- The constructed original continuous kernel satisfies the literal pointwise GL integral equation on the actual physical interval.
Use: this is the source transformation kernel defining u and all subsequent continuum persymmetry statements; the actual interval-supported integral uses the original Lebesgue subtype measure.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the original reconstruction integral is over the true
zero-extended source row. That same original row is now proved to be
the genuine physical indicator times K. Replace it almost everywhere,
and the community indicator integral identity restricts precisely to
the original physical prefix. Rearrangement gives the source equation. -/
theorem transformationKernel_GL (a : ℝ) (ha : -1<a) (t s : HalfInterval) :
    transformationKernel a ha t s+kernel a ha (t:ℝ) (s:ℝ)+
      (∫ r:Interval in prefixSet (t:ℝ),
        transformationKernel a ha t (halfClamp r)*kernel a ha (halfTime r) (s:ℝ))=0 := by
  -- Every replacement is justified in the actual source measure; no pointwise evaluation of an arbitrary L2 class is assumed.
  have hi : (∫ r:Interval,(solutionRow a ha t:Space) r*kernel a ha (halfTime r) (s:ℝ))=
      ∫ r:Interval in prefixSet (t:ℝ),
        transformationKernel a ha t (halfClamp r)*kernel a ha (halfTime r) (s:ℝ) := by
    rw [← integral_indicator (prefixSet_measurable (t:ℝ))]
    apply integral_congr_ae
    filter_upwards [solutionRow_representative a ha t] with r hr
    rw [hr]
    by_cases hp : r∈prefixSet (t:ℝ)
    · rw [indicator_of_mem hp,indicator_of_mem hp]
    · rw [indicator_of_notMem hp,indicator_of_notMem hp,zero_mul]
  have he := transformationKernel_reconstruction a ha t s
  rw [hi] at he
  linarith

/-- The original reconstructed GL kernel is zero at its source spatial zero endpoint.
Use: ensures the actual transformation preserves the original singular reference branch normalization.
Article: jacobi, Proposition C.2.
Proof: the true zero Hilbert row vanishes; actual source kernel symmetry reduces its other zero endpoint to the proved original zero row. -/
theorem transformationKernel_zero_right (a : ℝ) (ha : -1<a) (t : HalfInterval) :
    transformationKernel a ha t halfZero=0 := by
  rw [transformationKernel,kernelRowVector_zero,inner_zero_left]
  change -kernel a ha (t:ℝ) 0-0=0
  rw [kernel_symmetric,kernel_zero,neg_zero,sub_zero]

end
end jacobi.GelfandLevitan
