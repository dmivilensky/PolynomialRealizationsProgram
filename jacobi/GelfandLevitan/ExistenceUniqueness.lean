import jacobi.GelfandLevitan.CandidateRows
import jacobi.GelfandLevitan.Triangle

/-!
Article: jacobi, Proposition C.2.
Existence and uniqueness hold for the literal original continuous
kernel on its actual closed physical triangle. All source spectral
data are fixed by the article, and their coercivity, original integral
representation and genuine inverse construction are already proved.
An arbitrary triangular candidate is extended by continuous clipping
only for the proof; no extension or operator hypothesis is assumed.
Use: the uniquely determined kernel defines the original transformed solutions u and the subsequent target continuum operator.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] kernel

/-- The actual reconstructed continuous source transformation kernel on the genuine closed GL triangle.
Use: the uniquely determined kernel defines the original transformed solutions u and the subsequent target continuum operator.
Article: jacobi, Proposition C.2.
-/
def triangleKernel (a : ℝ) (ha : -1<a) : C(Triangle,ℝ) :=
  (⟨fun p:HalfInterval×HalfInterval => transformationKernel a ha p.1 p.2,
    transformationKernel_continuous a ha⟩ : C(HalfInterval×HalfInterval,ℝ)).comp triangleInclusion

/-- The literal original GL equation for a continuous candidate on its true closed physical triangle.
Use: states the actual existence and uniqueness theorem directly on the original source domain; the clipping extension in the integral agrees with the candidate on the physical integration prefix.
Article: jacobi, Proposition C.2.
-/
def SatisfiesGL (a : ℝ) (ha : -1<a) (K : C(Triangle,ℝ)) : Prop :=
  ∀ p:Triangle,K p+kernel a ha (p.val.1:ℝ) (p.val.2:ℝ)+
    (∫ r:Interval in prefixSet (p.val.1:ℝ),
      K (triangleClip (p.val.1,halfClamp r))*kernel a ha (halfTime r) (p.val.2:ℝ))=0

/-- The actual constructed source kernel and its triangle clipping agree at every original prefix integration point.
Use: the proved physical GL equation is exactly the literal original triangular equation, with no altered integrand on its source interval.
Article: jacobi, Proposition C.2.
Proof: at an actual physical prefix point, the clamped original coordinate is already at most t. The triangle clipping minimum is therefore that unaltered coordinate. -/
theorem triangleKernel_prefix (a : ℝ) (ha : -1<a) (t : HalfInterval)
    (r : Interval) (hr : r∈prefixSet (t:ℝ)) :
    triangleKernel a ha (triangleClip (t,halfClamp r))=
      transformationKernel a ha t (halfClamp r) := by
  change transformationKernel a ha t
    ⟨min (t:ℝ) (halfTime r),_⟩=transformationKernel a ha t (halfClamp r)
  congr 1
  apply Subtype.ext
  exact min_eq_right ((min_le_left (r:ℝ) (1/2)).trans hr)

/-- The constructed continuous triangular kernel satisfies the original GL equation at every original physical point.
Use: supplies existence in the source GL theorem and fixes the true transformation kernel used for continuum persymmetry.
Article: jacobi, Proposition C.2.
Proof: the source square reconstruction already obeys the actual
physical interval equation. Its true triangular restriction preserves
both original point values; the clipping extension preserves every
original prefix integration point, hence also the true interval integral. -/
theorem triangleKernel_satisfiesGL (a : ℝ) (ha : -1<a) :
    SatisfiesGL a ha (triangleKernel a ha) := by
  -- Clipping changes only the unintegrated portion beyond the original physical prefix.
  intro p
  have hi : (∫ r:Interval in prefixSet (p.val.1:ℝ),
      triangleKernel a ha (triangleClip (p.val.1,halfClamp r))*
        kernel a ha (halfTime r) (p.val.2:ℝ))=
      ∫ r:Interval in prefixSet (p.val.1:ℝ),
        transformationKernel a ha p.val.1 (halfClamp r)*
          kernel a ha (halfTime r) (p.val.2:ℝ) := by
    apply setIntegral_congr_fun (prefixSet_measurable _)
    intro r hr
    dsimp only
    rw [triangleKernel_prefix a ha _ _ hr]
  rw [hi]
  exact transformationKernel_GL a ha p.val.1 p.val.2

/-- Every arbitrary original continuous triangular GL candidate equals the constructed source kernel.
Use: fixes all actual transformed solutions and continuum quantities independently of the inverse construction used in the proof.
Article: jacobi, Proposition C.2.
Proof: continuously clip the second coordinate to extend the arbitrary
source candidate. For a fixed original t its spatial row is an actual
continuous unit-domain function. The original candidate equation and
source F symmetry give the literal row equation. The proved original
row uniqueness identifies it pointwise at every true triangle point. -/
theorem triangleKernel_unique (a : ℝ) (ha : -1<a) (K : C(Triangle,ℝ))
    (hK : SatisfiesGL a ha K) : K=triangleKernel a ha := by
  -- The extension is constructed from the arbitrary original triangular candidate; none is required as an additional premise.
  apply ContinuousMap.ext
  intro p
  let L : C(HalfInterval×HalfInterval,ℝ) := K.comp triangleClip
  let g : C(Interval,ℝ) := ((L.curry) p.val.1).comp halfClamp
  have hg (s : Interval) (hst : (s:ℝ)≤(p.val.1:ℝ)) :
      g s+kernelRows a ha p.val.1 s+
        (∫ r:Interval in prefixSet (p.val.1:ℝ),g r*kernel a ha (halfTime s) (halfTime r))=0 := by
    let q : Triangle := ⟨(p.val.1,halfClamp s),(min_le_left (s:ℝ) (1/2)).trans hst⟩
    have he := hK q
    have hq : triangleClip (p.val.1,halfClamp s)=q := triangleClip_inclusion q
    have hi : (∫ r:Interval in prefixSet (p.val.1:ℝ),g r*kernel a ha (halfTime s) (halfTime r))=
        ∫ r:Interval in prefixSet (p.val.1:ℝ),g r*kernel a ha (halfTime r) (halfTime s) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun r => by dsimp only; rw [kernel_symmetric])
    rw [kernelRows_apply,hi]
    change K (triangleClip (p.val.1,halfClamp s))+kernel a ha (p.val.1:ℝ) (halfTime s)+
      (∫ r:Interval in prefixSet (p.val.1:ℝ),K (triangleClip (p.val.1,halfClamp r))*
        kernel a ha (halfTime r) (halfTime s))=0
    rw [hq]
    exact he
  have hu := continuous_row_unique a ha p.val.1 g hg p.val.2 p.property
  have he : g (halfInclusion p.val.2)=K p := by
    change K (triangleClip (p.val.1,halfClamp (halfInclusion p.val.2)))=K p
    rw [halfClamp_halfInclusion]
    exact congrArg K (triangleClip_inclusion p)
  exact he.symm.trans hu

/-- The original article data determine exactly one continuous GL kernel on the genuine closed physical triangle.
Use: closes the existence-and-uniqueness part of the source GL construction before the separate differentiability and continuum persymmetry arguments.
Article: jacobi, Proposition C.2.
Proof: the actual constructed triangular kernel satisfies the literal original equation, and the fully proved arbitrary-candidate uniqueness theorem identifies every other continuous solution. -/
theorem GL_exists_unique (a : ℝ) (ha : -1<a) :
    ∃! K:C(Triangle,ℝ),SatisfiesGL a ha K :=
  ⟨triangleKernel a ha,triangleKernel_satisfiesGL a ha,triangleKernel_unique a ha⟩

end
end jacobi.GelfandLevitan
