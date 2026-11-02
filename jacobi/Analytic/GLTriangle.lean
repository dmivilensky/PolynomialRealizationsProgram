import jacobi.Analytic.GLInverse

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The analytic inverse construction solves the literal physical GL
equation. Uniqueness holds for every continuous triangular candidate:
a forced reconstruction extends it to a full-square solution, where
the already proved genuine inverse determines it.
Use: defines the original transformed solutions and the analytic persymmetric profile.
-/
namespace jacobi.Analytic
noncomputable section
open Set MeasureTheory jacobi.Reference jacobi.GelfandLevitan
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The genuine continued transformation kernel on the article's original closed physical triangle.
Use: defines the original transformed solutions and the analytic persymmetric profile.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def OrderDisk.GLtriangle {a0 : ℝ} (D : OrderDisk a0) (a : ℂ) : C(Triangle,ℂ) :=
  (D.GLsolution a).comp triangleInclusion

/-- The literal original GL equation for an arbitrary continuous complex triangular candidate.
Use: states genuine existence and uniqueness on exactly the source domain, without assuming an extension of the candidate solves the equation outside the triangle.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The prefix product is proved equal to the unchanged integral over the physical prefix; clipping only extends unused spatial coordinates continuously. -/
def OrderDisk.SatisfiesGL {a0 : ℝ} (D : OrderDisk a0) (a : ℂ) (K : C(Triangle,ℂ)) : Prop :=
  ∀ p : Triangle,K p+D.kernelMap a p.val+
    prefixProduct (K.comp triangleClip) (D.kernelMap a) p.val=0

/-- The original square GL solution solves the actual physical GL equation whenever its genuine operator is invertible.
Use: restricting this equation to the true triangle gives the article's continuous complex transformation kernel.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: evaluate the proved actual inverse equation at the physical coordinate pair and rearrange its unchanged identity-plus-prefix-integral terms. -/
theorem OrderDisk.GLsolution_pointwise {a0 : ℝ} (D : OrderDisk a0) {a : ℂ}
    (hu : IsUnit (D.GLoperator a)) (p : KernelSquare) :
    D.GLsolution a p+D.kernelMap a p+
      prefixProduct (D.GLsolution a) (D.kernelMap a) p=0 := by
  have he := congrArg (fun f : C(KernelSquare,ℂ) => f p) (D.GLsolution_equation hu)
  change D.GLsolution a p+prefixProduct (D.GLsolution a) (D.kernelMap a) p= -D.kernelMap a p at he
  linear_combination he

/-- The actual analytic triangular transformation kernel satisfies the original complex GL equation.
Use: establishes existence on the exact closed source triangle before proving uniqueness for arbitrary candidates.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: clipping preserves the square solution at every true prefix integration point. Its literal prefix product therefore agrees with the square product there; restrict the proved square GL equation to the triangle. -/
theorem OrderDisk.GLtriangle_satisfiesGL {a0 : ℝ} (D : OrderDisk a0) {a : ℂ}
    (hu : IsUnit (D.GLoperator a)) : D.SatisfiesGL a (D.GLtriangle a) := by
  -- Equality is needed only on the actual physical integration prefix, where clipping fixes the second coordinate.
  intro p
  have hi : prefixProduct ((D.GLtriangle a).comp triangleClip) (D.kernelMap a) p.val=
      prefixProduct (D.GLsolution a) (D.kernelMap a) p.val := by
    rcases p with ⟨⟨t,s⟩,hp⟩
    rw [prefixProduct_subtype,prefixProduct_subtype]
    apply setIntegral_congr_fun (prefixSet_measurable _)
    intro r hr
    have hrt : (halfClamp r:ℝ)≤(t:ℝ) := (min_le_left (r:ℝ) (1/2)).trans hr
    dsimp only
    congr 1
    change D.GLsolution a (triangleInclusion (triangleClip (t,halfClamp r)))=D.GLsolution a (t,halfClamp r)
    congr 1
    apply Prod.ext
    · rfl
    · exact Subtype.ext (min_eq_right hrt)
  rw [hi]
  exact D.GLsolution_pointwise hu p.val

/-- Every arbitrary continuous complex triangular GL candidate equals the genuine analytic inverse kernel.
Use: establishes full uniqueness in the original source domain and identifies independently constructed real kernels with the analytic continuation.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: extend the candidate to the square by its own forced reconstruction, minus F minus its original prefix integral. Its given GL equation makes this extension agree with the candidate on the triangle. The extension therefore has the same actual prefix integral and solves the square GL equation. The proved true inverse fixes that extension, hence fixes the original candidate. -/
theorem OrderDisk.GLtriangle_unique {a0 : ℝ} (D : OrderDisk a0) {a : ℂ}
    (hu : IsUnit (D.GLoperator a)) (K : C(Triangle,ℂ)) (hK : D.SatisfiesGL a K) :
    K=D.GLtriangle a := by
  -- The full-square extension is constructed from the arbitrary candidate; it is not an extra premise on that candidate.
  let Q : C(KernelSquare,ℂ) := K.comp triangleClip
  let L : C(KernelSquare,ℂ) := -D.kernelMap a-prefixProduct Q (D.kernelMap a)
  have hL (p : Triangle) : L p.val=K p := by
    have he := hK p
    change K p+D.kernelMap a p.val+prefixProduct Q (D.kernelMap a) p.val=0 at he
    change -D.kernelMap a p.val-prefixProduct Q (D.kernelMap a) p.val=K p
    linear_combination -he
  have hi : prefixProduct L (D.kernelMap a)=prefixProduct Q (D.kernelMap a) := by
    apply ContinuousMap.ext
    rintro ⟨t,s⟩
    rw [prefixProduct_subtype,prefixProduct_subtype]
    apply setIntegral_congr_fun (prefixSet_measurable _)
    intro r hr
    let p : Triangle := ⟨(t,halfClamp r),(min_le_left (r:ℝ) (1/2)).trans hr⟩
    have hp : triangleClip (t,halfClamp r)=p := triangleClip_inclusion p
    change L p.val*_=K (triangleClip (t,halfClamp r))*_
    rw [hL p,hp]
  have hEq : D.GLoperator a L= -D.kernelMap a := by
    change L+prefixProduct L (D.kernelMap a)= -D.kernelMap a
    rw [hi]
    change (-D.kernelMap a-prefixProduct Q (D.kernelMap a))+prefixProduct Q (D.kernelMap a)=_
    exact sub_add_cancel _ _
  have hsol := D.GLsolution_unique hu hEq
  apply ContinuousMap.ext
  intro p
  exact (hL p).symm.trans (congrArg (fun f : C(KernelSquare,ℂ) => f p.val) hsol)

end
end jacobi.Analytic
