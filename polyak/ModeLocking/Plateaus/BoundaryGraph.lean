import polyak.ModeLocking.Boundary.Frontier
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Connected.LocallyConnected

/-! The actual divergence frontier is globally homeomorphic to the open
finite-boundary domain in the original two source parameters. -/
noncomputable section
namespace polyak.ModeLocking.Plateaus
open General Levels Set Filter
open Global.Threshold

def finiteBoundaryDomain : Set ParameterStrip := {p | (kappaBoundary p : EReal)<⊤}

theorem finiteBoundaryDomain_isOpen : IsOpen finiteBoundaryDomain :=
  isOpen_Iio.preimage (continuous_subtype_val.comp continuous_kappaBoundary)

private theorem boundary_ne_bot (p : ParameterStrip) : (kappaBoundary p : EReal)≠⊥ :=
  ne_bot_of_gt ((kappaBoundary p).property)

def boundaryCondition (p : finiteBoundaryDomain) : ConditionNumber :=
  ⟨(kappaBoundary p.val : EReal).toReal, by
    have h : (1 : EReal)<(kappaBoundary p.val : EReal) := (kappaBoundary p.val).property
    rw [←EReal.coe_toReal p.property.ne (boundary_ne_bot p.val)] at h
    exact_mod_cast h⟩

@[simp] theorem boundaryCondition_coe (p : finiteBoundaryDomain) :
    ((boundaryCondition p : ℝ) : EReal)=(kappaBoundary p.val : EReal) :=
  EReal.coe_toReal p.property.ne (boundary_ne_bot p.val)

theorem continuous_boundaryCondition : Continuous boundaryCondition := by
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (EReal.tendsto_toReal p.property.ne (boundary_ne_bot p.val)).comp
    (((continuous_subtype_val.comp continuous_kappaBoundary).comp continuous_subtype_val).continuousAt)

def boundaryProjection (q : frontier Regions.divergenceSet) : finiteBoundaryDomain :=
  ⟨parameters q.val, by
    have h := (kappaBoundary_eq_iff (parameters q.val) (conditionNumber q.val)).mpr
      (by simpa only [fixedThreshold,tuning_parameters] using sigma_eq_zero_on_frontier q.property)
    change (kappaBoundary (parameters q.val) : EReal)<⊤
    rw [h]
    exact EReal.coe_lt_top _⟩

def boundaryLift (p : finiteBoundaryDomain) : frontier Regions.divergenceSet :=
  ⟨tuning p.val (boundaryCondition p), by
    apply (mem_frontier_iff_sigma_zero _).mpr
    exact (kappaBoundary_eq_iff p.val (boundaryCondition p)).mp (boundaryCondition_coe p).symm⟩

/-- This is a homeomorphism of the actual source spaces, not a local graph
assumption used to postulate local connectedness of the frontier. -/
def boundaryGraphHomeomorph : (frontier Regions.divergenceSet) ≃ₜ finiteBoundaryDomain where
  toFun := boundaryProjection
  invFun := boundaryLift
  left_inv q := by
    apply Subtype.ext
    have hk := (kappaBoundary_eq_iff (parameters q.val) (conditionNumber q.val)).mpr
      (by simpa only [fixedThreshold,tuning_parameters] using sigma_eq_zero_on_frontier q.property)
    have hc : boundaryCondition (boundaryProjection q)=conditionNumber q.val := by
      apply Subtype.ext
      change (kappaBoundary (parameters q.val) : EReal).toReal=q.val.kappa
      rw [hk,EReal.toReal_coe]
      rfl
    change tuning (parameters q.val) (boundaryCondition (boundaryProjection q))=q.val
    rw [hc,tuning_parameters]
  right_inv p := by
    apply Subtype.ext
    rfl
  continuous_toFun := (continuous_parameters.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_tuning.comp
    (continuous_subtype_val.prodMk continuous_boundaryCondition)).subtype_mk _


theorem parameterStrip_convex : Convex ℝ
    {p : ℝ×ℝ | 0≤p.2 ∧ p.2<1 ∧ 0<p.1 ∧ p.1<2*(1+p.2)} := by
  intro x hx y hy a b ha hb hab
  change 0≤x.2 ∧ x.2<1 ∧ 0<x.1 ∧ x.1<2*(1+x.2) at hx
  change 0≤y.2 ∧ y.2<1 ∧ 0<y.1 ∧ y.1<2*(1+y.2) at hy
  change 0≤a*x.2+b*y.2 ∧ a*x.2+b*y.2<1 ∧ 0<a*x.1+b*y.1 ∧
    a*x.1+b*y.1<2*(1+(a*x.2+b*y.2))
  by_cases ha0 : a=0
  · subst a
    have hb1 : b=1 := by linarith
    simpa only [zero_mul,zero_add,hb1,one_mul] using hy
  have ha' : 0<a := lt_of_le_of_ne ha (Ne.symm ha0)
  refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),?_,?_,?_⟩
  · have h1 := mul_pos ha' (sub_pos.mpr hx.2.1)
    have h2 := mul_nonneg hb (sub_nonneg.mpr hy.2.1.le)
    nlinarith [h1,h2]
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx.2.2.1) (mul_nonneg hb hy.2.2.1.le)
  · have h1 := mul_pos ha' (sub_pos.mpr hx.2.2.2)
    have h2 := mul_nonneg hb (sub_nonneg.mpr hy.2.2.2.le)
    nlinarith [h1,h2]

instance parameterStrip_locallyConnected : LocallyConnectedSpace ParameterStrip := by
  have : LocallyPathConnectedSpace ParameterStrip := parameterStrip_convex.locallyPathConnectedSpace
  infer_instance

instance finiteBoundaryDomain_locallyConnected : LocallyConnectedSpace finiteBoundaryDomain :=
  finiteBoundaryDomain_isOpen.locallyConnectedSpace

instance frontier_locallyConnected : LocallyConnectedSpace (frontier Regions.divergenceSet) :=
  boundaryGraphHomeomorph.isOpenEmbedding.locallyConnectedSpace

end polyak.ModeLocking.Plateaus
