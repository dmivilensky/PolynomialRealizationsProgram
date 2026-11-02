import jacobi.GelfandLevitan.Operator
import Mathlib.Topology.CompactOpen

/-!
Article: jacobi, Theorem 2.1.
The original continuous kernel has a continuous row map in the genuine
uniform function norm. The earlier article's continuous-function L2
inclusion and the actual half-domain orthogonal projection turn these
same source rows into a continuous Hilbert-vector curve. Their true
pairings are exactly the original spatial integrals.
Use: its compact topology includes both actual source endpoints when constructing the continuous row curve and K.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] kernel

/-- The genuine closed physical half interval for the original pointwise GL kernel.
Use: its compact topology includes both actual source endpoints when constructing the continuous row curve and K.
Article: jacobi, Proposition C.4.
-/
abbrev HalfInterval := {t:ℝ // t∈Icc (0:ℝ) (1/2)}

/-- The actual singular left endpoint in the original physical half interval.
Use: fixes the genuine zero source row and the original GL endpoint value K(0,s)=0.
Article: jacobi, Proposition C.2.
-/
def halfZero : HalfInterval := ⟨0,by norm_num⟩

/-- The actual physical half interval included continuously in the shared original unit interval.
Use: curries the original compact-domain kernel at the unaltered source parameter t.
Article: jacobi, Proposition C.2.
-/
def halfInclusion : C(HalfInterval,Interval) where
  toFun t := ⟨t.val,⟨t.property.1,by linarith [t.property.2]⟩⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The original continuous kernel rows in the uniform norm on the fixed compact spatial domain.
Use: gives actual Hilbert row continuity for the source right-hand side P_t*F(t,.), without taking point evaluations of arbitrary L2 representatives.
Article: jacobi, Proposition C.2.
-/
def kernelRows (a : ℝ) (ha : -1<a) : C(HalfInterval,C(Interval,ℝ)) :=
  (kernelMap a ha).curry.comp halfInclusion

/-- Evaluation of the actual compact-domain row is exactly the original source kernel at its genuine physical first coordinate.
Use: identifies the original source Hilbert row pairings with their literal GL spatial integrals.
Article: jacobi, Proposition C.2.
Proof: genuine currying preserves pointwise values; the first physical coordinate is already at most one half, so its actual clamp is the coordinate itself. -/
theorem kernelRows_apply (a : ℝ) (ha : -1<a) (t : HalfInterval) (s : Interval) :
    kernelRows a ha t s=kernel a ha (t:ℝ) (halfTime s) := by
  change kernel a ha (min (t:ℝ) (1/2)) (halfTime s)=_
  rw [min_eq_left t.property.2]

/-- The original continuous kernel row as a vector of the genuine source half-interval Hilbert space, continuously in the physical endpoint.
Use: defines the original source right-hand side and actual inverse solution k_t, with genuine parameter continuity in L2.
Article: jacobi, Proposition C.2.
-/
def kernelRowVector (a : ℝ) (ha : -1<a) : C(HalfInterval,halfSubspace) where
  toFun t := halfSubspace.orthogonalProjectionOnto
    (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume (kernelRows a ha t))
  continuous_toFun := halfSubspace.orthogonalProjectionOnto.continuous.comp
    ((ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume).continuous.comp (kernelRows a ha).continuous)

/-- Pairing with the original Hilbert row gives exactly the true source kernel integral against any actual half-domain L2 input.
Use: the original GL reconstruction formula for K has a genuine continuous Hilbert pairing and the exact required spatial integral value.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the actual orthogonal projection preserves pairing with the
genuine half-domain input. The original L2 inner product is its real
spatial integral. Replace the true continuous row representative
almost everywhere and use its proved exact original kernel value. -/
theorem kernelRowVector_inner (a : ℝ) (ha : -1<a) (t : HalfInterval) (v : halfSubspace) :
    inner ℝ (kernelRowVector a ha t) v=
      ∫ s:Interval,(v:Space) s*kernel a ha (t:ℝ) (halfTime s) := by
  -- The source row remains a original integral, rather than a selected pointwise L2 representative.
  change inner ℝ (halfSubspace.orthogonalProjectionOnto
    (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume (kernelRows a ha t))) v=_
  rw [halfSubspace.inner_orthogonalProjectionOnto_eq_of_mem_right,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume (kernelRows a ha t)] with s hs
  rw [hs,kernelRows_apply]
  rfl

/-- The genuine source Hilbert rows have one finite positive uniform norm bound over the entire original physical half interval.
Use: combines with the proved original uniform inverse bound to give bounded actual GL solution rows and the source pointwise kernel bound.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the actual Hilbert row curve is continuous on the genuine compact parameter interval and has its true continuous-map supremum norm; increase it by one. -/
theorem kernelRowVector_bounded (a : ℝ) (ha : -1<a) :
    ∃ B:ℝ,0<B ∧ ∀ t:HalfInterval,‖kernelRowVector a ha t‖≤B := by
  refine ⟨‖kernelRowVector a ha‖+1,by positivity,fun t => ?_⟩
  exact ((kernelRowVector a ha).norm_coe_le_norm t).trans (by linarith)

/-- The original continuous kernel row at its genuine singular endpoint is exactly zero.
Use: fixes the original GL row and kernel endpoint data, independently of any representative choices.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: every point of the original zero row is the already proved actual zero kernel endpoint value. -/
theorem kernelRows_zero (a : ℝ) (ha : -1<a) : kernelRows a ha halfZero=0 := by
  apply ContinuousMap.ext
  intro s
  rw [kernelRows_apply]
  change kernel a ha 0 (halfTime s)=0
  exact kernel_zero a ha (halfTime s)

/-- The original Hilbert source row at the actual left endpoint is the true zero vector.
Use: the original inverse GL solution starts with the actual zero source datum, preserving K(0,s)=0.
Article: jacobi, Proposition C.2.
Proof: its actual continuous source row is zero, and both the original continuous-function L2 inclusion and true orthogonal projection are linear. -/
theorem kernelRowVector_zero (a : ℝ) (ha : -1<a) : kernelRowVector a ha halfZero=0 := by
  change halfSubspace.orthogonalProjectionOnto
    (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume (kernelRows a ha halfZero))=0
  rw [kernelRows_zero,map_zero,map_zero]

end
end jacobi.GelfandLevitan
