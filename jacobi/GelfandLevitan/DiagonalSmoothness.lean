import jacobi.GelfandLevitan.DiagonalDerivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
Article: jacobi, Proposition C.2.
The proved actual diagonal derivative is packaged as the community C1
predicate on the full original positive half interval, including the
one-sided midpoint. Its value is the sum of the genuine original partial
derivatives; no derivative regularity is assumed in this packaging.
Use: kernelDiagonal_contDiffOn localizes this genuine C1 statement to the full original domain (0,1/2], providing the actual regularity of the coefficient in the transformed differential equation.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original GL diagonal is C1 on every closed positive nondegenerate physical strip.
Use: kernelDiagonal_contDiffOn localizes this genuine C1 statement to the full original domain (0,1/2], providing the actual regularity of the coefficient in the transformed differential equation.
Article: jacobi, Proposition C.2.
Source: mathlib's characterization of C1 by differentiability and continuity of derivWithin on a domain with unique derivatives.
Proof: the genuine derivative identity supplies differentiability and identifies derivWithin with the already proved continuous original diagonal-slope row. -/
theorem kernelDiagonal_contDiffOn_strip {a d : ℝ} (ha : -1<a) (hd : 0<d) (hds : d<(1/2:ℝ)) :
    ContDiffOn ℝ 1 (fun x : ℝ => kernelDiagonal a ha (halfParameterClamp x)) (Icc d (1/2)) := by
  -- Unique derivatives on the genuine nondegenerate physical strip identify the community derivative with the actual continuous diagonal slope.
  let P : C(ℝ,DerivativeStrip d) := ⟨Set.projIcc d (1/2) hds.le,continuous_projIcc⟩
  let g := (diagonalSlopeRows ha hd hds.le).comp P
  have hder (x : ℝ) (hx : x∈Icc d (1/2)) :
      HasDerivWithinAt (fun y : ℝ => kernelDiagonal a ha (halfParameterClamp y)) (g x) (Icc d (1/2)) x := by
    have he : g x=diagonalSlopeRows ha hd hds.le ⟨x,hx⟩ := by
      change diagonalSlopeRows ha hd hds.le (Set.projIcc d (1/2) hds.le x)=_
      rw [Set.projIcc_of_mem hds.le hx]
    rw [he]
    exact kernelDiagonal_hasDerivWithinAt ha hd ⟨x,⟨(hd.trans_le hx.1).le,hx.2⟩⟩ hx.1
  apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hds)).mpr
  refine ⟨fun x hx => (hder x hx).differentiableWithinAt,?_⟩
  exact g.continuous.continuousOn.congr (fun x hx => (hder x hx).derivWithin ((uniqueDiffOn_Icc hds) x hx))

/-- The actual original GL diagonal is C1 on the entire original positive half interval, with its genuine midpoint one-sided derivative.
Use: completes the literal C1 assertion of Differentiability of K (c) needed for the actual transformed potential q_alpha+2*w' and the general target-operator Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: at each positive physical point use the proved C1 closed strip with lower endpoint half that point. This strip is a relative neighborhood in the original physical domain, so community locality of ContDiffWithinAt gives the full assertion. -/
theorem kernelDiagonal_contDiffOn (a : ℝ) (ha : -1<a) :
    ContDiffOn ℝ 1 (fun x : ℝ => kernelDiagonal a ha (halfParameterClamp x)) (Ioc (0:ℝ) (1/2)) := by
  intro t ht
  have hd : 0<t/2 := by linarith [ht.1]
  have hds : t/2<(1/2:ℝ) := by linarith [ht.1,ht.2]
  apply ((kernelDiagonal_contDiffOn_strip ha hd hds) t ⟨by linarith [ht.1],ht.2⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show t/2<t by linarith [ht.1]))] with x hx hlt
  exact ⟨hlt.le,hx.2⟩

end
end jacobi.GelfandLevitan
