import jacobi.GelfandLevitan.RegularizedDerivativeSeries
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
Article: jacobi, Theorem 2.1.
The original F-flat has the actual continuous termwise spatial
derivative throughout the required closed strips. At the midpoint
the derivative is understood from the physical left. Symmetry gives
the corresponding second-coordinate assertion for the same kernel.
Use: the endpoint extension theorem adds the physical midpoint derivative; these are the continuous regularized data needed in Differentiability of K.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] regularizedKernel regularizedSlope

/-- The derivative of the actual regularization at an interior first coordinate is the sum of the genuine term derivatives.
Use: the endpoint extension theorem adds the physical midpoint derivative; these are the continuous regularized data needed in Differentiability of K.
Article: jacobi, Theorem 2.1.
Proof: on an open strip around the genuine point the proved summable uniform derivative majorant applies to the actual individual derivatives. The original regularized series converges there, and its proved exact sum identifies the community termwise derivative with the actual F-flat. -/
theorem regularizedKernel_hasDerivAt {a t s : ℝ} (ha : -1<a)
    (ht : t∈Ioo (0:ℝ) (1/2)) (hs : s∈Icc (0:ℝ) (1/2)) :
    HasDerivAt (fun x => regularizedKernel a ha x s) (regularizedSlope a ha t s) t := by
  -- Use an actual open interval separated from the singular endpoint, without extending the physical series beyond the midpoint.
  let d : ℝ := t/2
  have hd : 0<d := by dsimp [d]; linarith [ht.1]
  have ht' : t∈Ioo d (1/2) := ⟨by dsimp [d]; linarith [ht.1],ht.2⟩
  obtain ⟨u,hu,hbound⟩ := regularizedSlopeTerm_summable_majorant ha hd
  have hsum : Summable (fun k => regularizedTerm a ha k t s) :=
    summable_norm_iff.mp (by simpa only [Real.norm_eq_abs] using regularized_absolute_summable ha ⟨ht.1.le,ht.2.le⟩ hs)
  have hder := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo d (1/2)).isPreconnected
    (fun k x hx => regularizedTerm_hasDerivAt a ha k s ⟨hd.trans hx.1,by linarith [hx.2]⟩)
    (fun k x hx => by simpa only [Real.norm_eq_abs] using hbound k x ⟨hx.1.le,hx.2.le⟩ s hs)
    ht' hsum ht'
  rw [regularizedSlope]
  apply hder.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht'] with x hx
  exact (regularized_kernel_series ha ⟨(hd.trans hx.1).le,hx.2.le⟩ hs).tsum_eq.symm

/-- The same original regularization has the genuine one-sided spatial derivative at its physical midpoint.
Use: completes the closed first-coordinate strip in Structure of F, including the boundary data used when differentiating the GL equation at t=1/2.
Article: jacobi, Theorem 2.1.
Proof: the already proved interior derivative is the original uniformly convergent derivative series, continuous up to the midpoint. The original F-flat is continuous there; apply the community endpoint derivative extension theorem to its actual derivative limit. -/
theorem regularizedKernel_hasDerivWithinAt_midpoint {a s : ℝ} (ha : -1<a)
    (hs : s∈Icc (0:ℝ) (1/2)) :
    HasDerivWithinAt (fun x => regularizedKernel a ha x s) (regularizedSlope a ha (1/2) s)
      (Iic (1/2)) (1/2) := by
  -- The endpoint argument identifies an actual left derivative, rather than defining a derivative by its candidate series.
  have hdiff : DifferentiableOn ℝ (fun x => regularizedKernel a ha x s) (Ioo (1/4:ℝ) (1/2)) :=
    fun x hx => (regularizedKernel_hasDerivAt ha ⟨by linarith [hx.1],hx.2⟩ hs).differentiableAt.differentiableWithinAt
  have hbase : ContinuousOn (fun x => regularizedKernel a ha x s) (Icc (1/4:ℝ) (1/2)) :=
    (regularizedKernel_continuousOn ha).comp (continuousOn_id.prodMk continuousOn_const)
      (fun x hx => ⟨⟨by change 0≤x; linarith [hx.1],hx.2⟩,hs⟩)
  have hslope : ContinuousOn (fun x => regularizedSlope a ha x s) (Icc (1/4:ℝ) (1/2)) :=
    (regularizedSlope_continuousOn ha (by norm_num : (0:ℝ)<1/4)).comp
      (continuousOn_id.prodMk continuousOn_const) (fun _ hx => ⟨hx,hs⟩)
  apply hasDerivWithinAt_Iic_of_tendsto_deriv hdiff
    ((hbase (1/2) ⟨by norm_num,le_rfl⟩).mono Ioo_subset_Icc_self)
    (Ioo_mem_nhdsLT (by norm_num : (1/4:ℝ)<1/2))
  have hlim := (hslope (1/2) ⟨by norm_num,le_rfl⟩).tendsto.mono_left
    (nhdsWithin_le_iff.mpr (Icc_mem_nhdsLT (by norm_num : (1/4:ℝ)<1/2)))
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1/4:ℝ)<1/2)] with x hx
  exact (regularizedKernel_hasDerivAt ha ⟨by linarith [hx.1],hx.2⟩ hs).deriv.symm

/-- The original F-flat has its continuous termwise first derivative on each entire closed required physical strip.
Use: this is the complete first-coordinate assertion of Structure of F (c), to be combined with the actual Green factorization when forming dot F for Differentiability of K.
Article: jacobi, Theorem 2.1.
Proof: use the genuine interior derivative below the midpoint and the proved actual left derivative at the midpoint; restrict both to the required closed strip. Joint continuity is independently established by the uniform original derivative series. -/
theorem regularizedKernel_hasDerivWithinAt {a d t s : ℝ} (ha : -1<a) (hd : 0<d)
    (ht : t∈Icc d (1/2)) (hs : s∈Icc (0:ℝ) (1/2)) :
    HasDerivWithinAt (fun x => regularizedKernel a ha x s) (regularizedSlope a ha t s)
      (Icc d (1/2)) t := by
  rcases ht.2.lt_or_eq with h | h
  · exact (regularizedKernel_hasDerivAt ha ⟨hd.trans_le ht.1,h⟩ hs).hasDerivWithinAt
  · subst t
    exact (regularizedKernel_hasDerivWithinAt_midpoint ha hs).mono Icc_subset_Iic_self

/-- The actual second-coordinate derivative is the reflected first-coordinate derivative of the same original regularization.
Use: provides the second-coordinate regularized input for the s derivative of the GL kernel; the Green term supplies its separate diagonal kink.
Article: jacobi, Theorem 2.1.
Proof: rewrite the actual regularized function using its proved original symmetry and apply the complete first-coordinate derivative theorem. -/
theorem regularizedKernel_hasDerivWithinAt_snd {a d t s : ℝ} (ha : -1<a) (hd : 0<d)
    (ht : t∈Icc (0:ℝ) (1/2)) (hs : s∈Icc d (1/2)) :
    HasDerivWithinAt (fun x => regularizedKernel a ha t x) (regularizedSlope a ha s t)
      (Icc d (1/2)) s := by
  simpa only [regularizedKernel_symmetric a ha t] using regularizedKernel_hasDerivWithinAt ha hd hs ht

end
end jacobi.GelfandLevitan
