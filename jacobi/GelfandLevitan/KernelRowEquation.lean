import jacobi.GelfandLevitan.ShrinkingIntegral

/-!
Article: jacobi, Proposition C.2.
The exact original GL equation is an identity of continuous spatial
rows, with its original real physical interval integral. This allows
two genuine endpoint equations to be subtracted in the same Banach
space before their true difference quotients are passed to the limit.
Use: transformationRows_GL converts the original subtype-prefix equation to its unchanged real physical interval integral.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] kernel transformationKernel

/-- Real parameter clipping agrees exactly with the existing physical half clamp on the original unit subtype.
Use: transformationRows_GL converts the original subtype-prefix equation to its unchanged real physical interval integral.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the original unit coordinate is nonnegative, so max(0,min(1/2,r)) is the same actual half-coordinate minimum. -/
theorem halfParameterClamp_unit (r : Interval) : halfParameterClamp (r:ℝ)=halfClamp r := by
  apply Subtype.ext
  change max (0:ℝ) (min (1/2) (r:ℝ))=min (r:ℝ) (1/2)
  rw [max_eq_right (le_min (by norm_num) r.property.1),min_comm]

/-- The existing physical half clamp has exactly the original half-time real coordinate.
Use: original Banach-row integrals and their scalar representatives retain the same coordinate when converted to actual GL interval equations.
Article: jacobi, Theorem 2.1.
Proof: the existing physical half clamp is defined by the original half-time coordinate. -/
theorem halfClamp_val (r : Interval) : ((halfClamp r):ℝ)=halfTime r := rfl

/-- The actual original K rows form a continuous curve in the genuine spatial uniform norm.
Use: kernelDifferenceQuotient uses the true original K values, and the moving-tail integrand uses the same independently constructed transformation kernel.
Article: jacobi, Theorem 2.1.
-/
def transformationRows (a : ℝ) (ha : -1<a) : C(HalfInterval,C(Interval,ℝ)) :=
  let K : C(HalfInterval×HalfInterval,ℝ) := ⟨fun p => transformationKernel a ha p.1 p.2,transformationKernel_continuous a ha⟩
  ⟨fun t => ContinuousMap.compCLM ℝ ℝ halfClamp (K.curry t),
    (ContinuousMap.compCLM ℝ ℝ halfClamp).continuous.comp K.curry.continuous⟩

/-- The genuine continuous K row evaluates to the previously constructed original transformation kernel.
Use: identifies its actual difference quotients with the literal original K difference quotients at every physical point.
Article: jacobi, Theorem 2.1.
Proof: genuine currying and precomposition retain exactly the original kernel values at the unchanged half coordinate. -/
theorem transformationRows_apply (a : ℝ) (ha : -1<a) (t : HalfInterval) (r : Interval) :
    transformationRows a ha t r=transformationKernel a ha t (halfClamp r) := rfl

/-- The actual original K(u,r)*F(r,.) as a jointly continuous function with values in genuine continuous spatial rows.
Use: its affineAverage is the exact moving-boundary term in the original K difference-quotient forcing, and has the proved true uniform-norm diagonal limit.
Article: jacobi, Theorem 2.1.
-/
def glTailIntegrand (a : ℝ) (ha : -1<a) : C(HalfInterval×HalfInterval,C(Interval,ℝ)) :=
  ⟨fun p => transformationKernel a ha p.1 p.2 • kernelRows a ha p.2,
    (transformationKernel_continuous a ha).smul ((kernelRows a ha).continuous.comp continuous_snd)⟩

/-- The actual continuous moving-tail row has exactly its literal original scalar kernel integrand.
Use: transformationRows_GL and the exact original difference-quotient equation use the same unmodified original K and F.
Article: jacobi, Theorem 2.1.
Proof: evaluate the genuine scalar action on the actual original F row. -/
theorem glTailIntegrand_apply (a : ℝ) (ha : -1<a) (u r : HalfInterval) (s : Interval) :
    glTailIntegrand a ha (u,r) s=transformationKernel a ha u r*kernel a ha (r:ℝ) (halfTime s) := by
  change transformationKernel a ha u r*kernelRows a ha r s=_
  rw [kernelRows_apply]

/-- The true moving-tail integrand is a continuous Banach-valued real-coordinate function at every actual original endpoint.
Use: every original real interval integral and each continuous evaluation of it are justified before subtracting the original GL equations.
Article: jacobi, Theorem 2.1.
Proof: fix the original first physical parameter and compose the jointly continuous genuine row integrand with the explicit physical half clamp. -/
theorem glTailIntegrand_continuous (a : ℝ) (ha : -1<a) (u : HalfInterval) :
    Continuous (fun r : ℝ => glTailIntegrand a ha (u,halfParameterClamp r)) :=
  (glTailIntegrand a ha).continuous.comp (continuous_const.prodMk halfParameterClamp.continuous)

/-- The original Banach-valued GL row integral with independently specified first endpoint parameter and physical upper integration limit.
Use: the exact original difference-quotient equation splits its moving integral at the fixed prefix endpoint before applying the original inverse.
Article: jacobi, Theorem 2.1.
-/
def glPrefixIntegral (a : ℝ) (ha : -1<a) (u : HalfInterval) (x : ℝ) : C(Interval,ℝ) :=
  ∫ r in (0:ℝ)..x,glTailIntegrand a ha (u,halfParameterClamp r)

/-- Every original scalar GL integrand is genuinely integrable on each actual physical prefix.
Use: the exact difference-quotient equation may subtract and scale its true original spatial integrals.
Article: jacobi, Theorem 2.1.
Proof: evaluate the original continuous Banach-valued integrand after the existing physical half clamp; continuity on the compact unit subtype implies integrability on every physical prefix. -/
theorem glTailPrefix_integrable (a : ℝ) (ha : -1<a) (u t : HalfInterval) (s : Interval) :
    IntegrableOn (fun r : Interval => transformationKernel a ha u (halfClamp r)*
      kernel a ha (halfTime r) (halfTime s)) (prefixSet (t:ℝ)) volume := by
  have hc : Continuous (fun r : Interval => glTailIntegrand a ha (u,halfClamp r) s) :=
    (ContinuousMap.evalCLM ℝ s).continuous.comp
      ((glTailIntegrand a ha).continuous.comp (continuous_const.prodMk halfClamp.continuous))
  have hi : Integrable (fun r : Interval => glTailIntegrand a ha (u,halfClamp r) s) volume :=
    integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)
  simpa only [glTailIntegrand_apply,halfClamp_val] using hi.integrableOn (s := prefixSet (t:ℝ))

/-- The actual Banach-valued original GL prefix integral has precisely its literal scalar physical-prefix representative.
Use: the original K difference-quotient integral is the evaluated linear difference of two glPrefixIntegral rows.
Article: jacobi, Theorem 2.1.
Proof: continuous point evaluation commutes with the actual integrable Banach-valued row. The original prefix-integral identity and the exact physical-clamp agreement identify its scalar spatial integrand on the genuine unit subtype. -/
theorem glPrefixIntegral_apply (a : ℝ) (ha : -1<a) (u t : HalfInterval) (s : Interval) :
    glPrefixIntegral a ha u (t:ℝ) s=
      ∫ r : Interval in prefixSet (t:ℝ),transformationKernel a ha u (halfClamp r)*
        kernel a ha (halfTime r) (halfTime s) := by
  -- The compact-domain representative and the real-coordinate integral are identified in their original measures.
  have hint := (glTailIntegrand_continuous a ha u).intervalIntegrable (μ := volume) (0:ℝ) (t:ℝ)
  have he := (ContinuousMap.evalCLM ℝ s).intervalIntegral_comp_comm hint
  change (∫ r in (0:ℝ)..(t:ℝ),glTailIntegrand a ha (u,halfParameterClamp r) s)=glPrefixIntegral a ha u (t:ℝ) s at he
  rw [← he]
  have hp := prefix_integral (fun r : ℝ => glTailIntegrand a ha (u,halfParameterClamp r) s)
    (show (t:ℝ)∈Icc (0:ℝ) 1 from ⟨t.property.1,by linarith [t.property.2]⟩)
  simp_rw [halfParameterClamp_unit,glTailIntegrand_apply,halfClamp_val] at hp
  simp_rw [glTailIntegrand_apply]
  exact hp.symm

/-- The actual normalized moving tail is the exact difference of its original prefix integrals.
Use: the original difference-quotient GL equation is obtained algebraically from two genuine row equations, retaining the moving-boundary contribution exactly.
Article: jacobi, Theorem 2.1.
Proof: the proved affine-average substitution gives the true normalized tail. Additivity of the independently integrable original Banach-valued intervals identifies that tail with its two original prefix integrals. -/
theorem glTailAverage_prefix (a : ℝ) (ha : -1<a) (t u : HalfInterval) (htu : u≠t) :
    affineAverage (glTailIntegrand a ha) t u=((u:ℝ)-(t:ℝ))⁻¹ •
      (glPrefixIntegral a ha u (u:ℝ)-glPrefixIntegral a ha u (t:ℝ)) := by
  rw [affineAverage_integral _ _ _ htu]
  congr 1
  have hcont := glTailIntegrand_continuous a ha u
  have h := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (0:ℝ) (t:ℝ))
    (hcont.intervalIntegrable (μ := volume) (t:ℝ) (u:ℝ))
  dsimp only [glPrefixIntegral]
  exact eq_sub_of_add_eq' h

/-- The original pointwise GL equation is an exact identity of its genuine continuous spatial rows with the original real physical interval integral.
Use: subtracting two such true Banach-space equations gives the actual K difference-quotient equation; there is no new differentiability or integral-kernel premise.
Article: jacobi, Theorem 2.1.
Proof: continuous point evaluation commutes with the genuine Banach-valued interval integral. The proved physical prefix-integral identity and the exact half-clamp agreement convert its original scalar representative to the independently proved original pointwise GL equation. -/
theorem transformationRows_GL (a : ℝ) (ha : -1<a) (t : HalfInterval) :
    transformationRows a ha t+kernelRows a ha t+
      (∫ r in (0:ℝ)..(t:ℝ),glTailIntegrand a ha (t,halfParameterClamp r))=0 := by
  -- Every row identity is established by genuine continuous evaluation of an already integrable original row function.
  ext s
  change transformationKernel a ha t (halfClamp s)+kernelRows a ha t s+
    glPrefixIntegral a ha t (t:ℝ) s=0
  rw [kernelRows_apply,glPrefixIntegral_apply]
  exact transformationKernel_GL a ha t (halfClamp s)

end
end jacobi.GelfandLevitan
