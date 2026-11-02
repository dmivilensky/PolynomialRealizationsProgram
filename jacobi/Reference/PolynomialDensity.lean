import jacobi.Reference.WeightedSpace
import Mathlib.Topology.ContinuousMap.Polynomial

/-!
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Polynomials in the actual reference cosine coordinate are uniformly
dense in all continuous functions on the physical interval, by the
community Stone--Weierstrass theorem. They are consequently dense in
the actual weighted L2 space. No completeness premise is assumed.
Use: generates the full continuous polynomial algebra for the original reference completeness proof.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory Polynomial
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- The actual cosine coordinate as a continuous function on the original reference interval.
Use: generates the full continuous polynomial algebra for the original reference completeness proof.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def coordinateMap : C(Interval,ℝ) :=
  ⟨fun t => coordinate t,(continuous_iff_continuousAt.mpr fun t => (coordinate_hasDerivAt t).continuousAt).comp continuous_subtype_val⟩

/-- The actual physical reference cosine coordinate separates all distinct points of the closed interval.
Use: discharges the exact hypothesis of the community Stone--Weierstrass theorem.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: cosine is strictly decreasing on [0,pi]; the original real points are recovered after multiplying by nonzero pi. -/
theorem coordinateMap_injective : Function.Injective coordinateMap := by
  intro x y hxy
  have hx : Real.pi*(x:ℝ)∈Icc 0 Real.pi := ⟨mul_nonneg Real.pi_pos.le x.property.1,by nlinarith [Real.pi_pos,x.property.2]⟩
  have hy : Real.pi*(y:ℝ)∈Icc 0 Real.pi := ⟨mul_nonneg Real.pi_pos.le y.property.1,by nlinarith [Real.pi_pos,y.property.2]⟩
  have hcos : cos (Real.pi*(x:ℝ))=cos (Real.pi*(y:ℝ)) := by
    change (1-cos (Real.pi*(x:ℝ)))/2=(1-cos (Real.pi*(y:ℝ)))/2 at hxy
    linarith
  have h := Real.strictAntiOn_cos.injOn hx hy hcos
  exact Subtype.ext (mul_left_cancel₀ Real.pi_ne_zero h)

/-- The actual polynomial algebra in the physical reference coordinate is uniformly dense in the continuous functions.
Use: supplies genuine completeness of the original reference polynomial system after passage to weighted L2.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Source: Stone--Weierstrass, ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints.
Proof: the algebra contains the actual coordinate function, which separates every pair of distinct physical points. -/
theorem coordinatePolynomial_denseRange : DenseRange (Polynomial.aeval (R := ℝ) coordinateMap) := by
  -- The density theorem is applied to the actual coordinate-generated algebra, not to an assumed complete system.
  have hsep : (Polynomial.aeval (R := ℝ) coordinateMap).range.SeparatesPoints := by
    intro x y hxy
    refine ⟨coordinateMap,⟨coordinateMap,⟨Polynomial.X,by simp⟩,rfl⟩,?_⟩
    exact fun h => hxy (coordinateMap_injective h)
  rw [denseRange_iff_closure_range]
  change closure (↑((Polynomial.aeval (R := ℝ) coordinateMap).range) : Set C(Interval,ℝ))=univ
  rw [← Subalgebra.topologicalClosure_coe,
    ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep]
  rfl

/-- The actual coordinate-polynomial evaluation map into the original weighted L2 space.
Use: produces a dense genuine reference polynomial system and transports it through the already proved onto multiplication unitary.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def polynomialWeightedL2 (a : ℝ) (ha : -1<a) : Polynomial ℝ →ₗ[ℝ] Lp ℝ 2 (hilbertWeight a ha).measure :=
  (ContinuousMap.toLp 2 (hilbertWeight a ha).measure ℝ).toLinearMap.comp
    (Polynomial.aeval (R := ℝ) coordinateMap).toLinearMap

/-- The actual reference coordinate polynomials are dense in the genuine weighted L2 space.
Use: the source reference basis completeness follows by the earlier article's onto sine-power multiplication unitary.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: compose the proved uniform polynomial density with the community density of continuous functions in L2 for the actual finite weighted measure. -/
theorem polynomialWeightedL2_denseRange (a : ℝ) (ha : -1<a) : DenseRange (polynomialWeightedL2 a ha) := by
  exact (ContinuousMap.toLp_denseRange ℝ (hilbertWeight a ha).measure (p := 2) ℝ (by norm_num)).comp
    coordinatePolynomial_denseRange (ContinuousMap.toLp 2 (hilbertWeight a ha).measure ℝ).continuous

/-- Every genuine polynomial class has its literal original coordinate-polynomial representative almost everywhere for the weighted measure.
Use: identifies the transported dense classes with the actual source reference eigenfunctions.
Article: jacobi, Lemma C.1.
Proof: the community continuous-function L2 map has its original continuous representative almost everywhere. -/
theorem polynomialWeightedL2_ae (a : ℝ) (ha : -1<a) (p : Polynomial ℝ) :
    polynomialWeightedL2 a ha p=ᵐ[(hilbertWeight a ha).measure] fun t : Interval => p.eval (coordinate t) := by
  change ContinuousMap.toLp 2 (hilbertWeight a ha).measure ℝ ((Polynomial.aeval (R := ℝ) coordinateMap) p)=ᵐ[(hilbertWeight a ha).measure] _
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) (hilbertWeight a ha).measure
    ((Polynomial.aeval (R := ℝ) coordinateMap) p)] with t ht
  rw [ht,Polynomial.aeval_continuousMap_apply]
  rfl

end
end jacobi.Reference
