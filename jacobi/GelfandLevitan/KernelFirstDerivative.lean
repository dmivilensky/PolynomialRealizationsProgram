import jacobi.GelfandLevitan.KernelRightDerivative
import jacobi.GelfandLevitan.RightDerivativeExtension

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The original constructed K has the actual continuous first-coordinate
derivative on every required closed physical lower triangle. Its
value is the independently constructed original derivative-forcing
solution, now identified through actual original difference quotients.
The physical midpoint and diagonal use their genuine one-sided derivatives.
Use: supplies the actual t derivative in Differentiability of K (a), the transformed-solution first derivative and the original differential equation in Proposition C.2.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] kernel kernelSlope transformationKernel

/-- The original constructed K has its genuine first-coordinate derivative throughout each required closed physical slice, including its diagonal and midpoint.
Use: supplies the actual t derivative in Differentiability of K (a), the transformed-solution first derivative and the original differential equation in Proposition C.2.
Article: jacobi, Theorem 2.1.
Proof: the original K right derivatives have already been identified from exact actual GL difference quotients. Their independently constructed genuine derivative-forcing solution is continuous in spatial uniform norm. After explicit constant parameter extension, the right-derivative FTC gives the true derivative throughout the original closed slice, including its physical endpoints. -/
theorem transformationKernel_hasDerivWithinAt_first {a d : ℝ} (ha : -1<a) (hd : 0<d)
    (t s : HalfInterval) (hdt : d≤(t:ℝ)) (hst : (s:ℝ)≤(t:ℝ)) :
    HasDerivWithinAt (fun x : ℝ => transformationKernel a ha (halfParameterClamp x) s)
      (derivativeCandidateRows ha hd ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩ (halfInclusion s))
      (Icc (max d (s:ℝ)) (1/2)) (t:ℝ) := by
  -- Every right derivative is already a theorem about the actual original K; only the endpoint extension remains.
  have hds : d≤(1/2:ℝ) := hdt.trans t.property.2
  let P : C(ℝ,DerivativeStrip d) := ⟨Set.projIcc d (1/2) hds,continuous_projIcc⟩
  let g : ℝ → ℝ := fun x => derivativeCandidateRows ha hd (P x) (halfInclusion s)
  have hg : Continuous g := (ContinuousMap.evalCLM ℝ (halfInclusion s)).continuous.comp
    ((derivativeCandidateRows ha hd).continuous.comp P.continuous)
  have hf : Continuous (fun x : ℝ => transformationKernel a ha (halfParameterClamp x) s) :=
    (transformationKernel_continuous a ha).comp (halfParameterClamp.continuous.prodMk continuous_const)
  have hright (x : ℝ) (hx : x∈Ico (max d (s:ℝ)) (1/2)) :
      HasDerivWithinAt (fun y : ℝ => transformationKernel a ha (halfParameterClamp y) s) (g x) (Ici x) x := by
    have hdx : d≤x := (le_max_left d (s:ℝ)).trans hx.1
    have hsx : (s:ℝ)≤x := (le_max_right d (s:ℝ)).trans hx.1
    have hpoint : x∈Icc (0:ℝ) (1/2) := ⟨(hd.trans_le hdx).le,hx.2.le⟩
    have h := transformationKernel_hasDerivWithinAt_right ha hd ⟨x,hpoint⟩ s hdx hx.2 hsx
    have he : g x=derivativeCandidateRows ha hd ⟨x,⟨hdx,hx.2.le⟩⟩ (halfInclusion s) := by
      change derivativeCandidateRows ha hd (Set.projIcc d (1/2) hds x) (halfInclusion s)=_
      rw [Set.projIcc_of_mem hds ⟨hdx,hx.2.le⟩]
    rw [he]
    exact h
  have h := continuous_hasDerivWithinAt_of_right hf hg ⟨max_le hdt hst,t.property.2⟩ hright
  have he : g (t:ℝ)=derivativeCandidateRows ha hd ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩ (halfInclusion s) := by
    change derivativeCandidateRows ha hd (Set.projIcc d (1/2) hds (t:ℝ)) (halfInclusion s)=_
    rw [Set.projIcc_of_mem hds ⟨hdt,t.property.2⟩]
  rw [he] at h
  exact h

/-- The actual first-coordinate derivative values of K on its physical triangle have a jointly continuous extension to the full positive parameter strip times the physical half interval.
Use: the actual differentiated GL equation, diagonal differentiation and transformed-solution calculus use these same continuous values on the physical triangle, where transformationKernel_hasDerivWithinAt_first identifies them with the original K derivative.
Article: jacobi, Theorem 2.1.
Proof: the independently constructed genuine derivative-forcing rows are continuous in their actual uniform norm; community continuous evaluation gives joint continuity, including physical diagonal and midpoint values. -/
theorem transformationKernel_firstDerivative_continuous {a d : ℝ} (ha : -1<a) (hd : 0<d) :
    Continuous (fun p : DerivativeStrip d × HalfInterval =>
      derivativeCandidateRows ha hd p.1 (halfInclusion p.2)) :=
  (derivativeCandidateRows ha hd).uncurry.continuous.comp
    (continuous_fst.prodMk (halfInclusion.continuous.comp continuous_snd))

end
end jacobi.GelfandLevitan
