import polyak.Boundary.P1.GeometrySlope
import polyak.Boundary.P1.Endpoint
import Mathlib.Analysis.Calculus.MeanValue

/-! Article: endpoint monotonicity supplies the closed P1 atom bound without interval overestimation. -/
noncomputable section
namespace polyak.Boundary.P1
open Filter
open scoped Topology

def atomFactor (g : ℝ → Coordinates) (z : ℝ) : ℝ := 1/2+z*g z 1

theorem atomFactor_hasDerivAt {g : ℝ → Coordinates} {z : ℝ} {v : Coordinates}
    (hg : HasDerivAt g v z) : HasDerivAt (atomFactor g) (g z 1+z*v 1) z := by
  have hB := (ContinuousLinearMap.proj (1 : Fin 2) : Coordinates →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt z hg
  change HasDerivAt (fun r => g r 1) (v 1) z at hB
  convert ((hasDerivAt_id z).mul hB).const_add (1/2 : ℝ) using 1
  · rfl
  · simp only [one_mul,id_eq]

theorem atomFactor_strictAntiOn {g : ℝ → Coordinates} {a b : ℝ}
    (hg : ContinuousOn (atomFactor g) (Set.Icc a b))
    (hv : ∀ z∈Set.Ioo a b, ∃ v : Coordinates, HasDerivAt g v z ∧ g z 1+z*v 1<0) :
    StrictAntiOn (atomFactor g) (Set.Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b) hg
  intro z hz
  have hz' : z∈Set.Ioo a b := by simpa only [interior_Icc] using hz
  obtain ⟨v,hv,hn⟩ := hv z hz'
  rwa [(atomFactor_hasDerivAt hv).deriv]

theorem atomFactor_nonneg_before_endpoint {g : ℝ → Coordinates} {a b : ℝ}
    (hg : ContinuousOn (atomFactor g) (Set.Icc a b))
    (hv : ∀ z∈Set.Ioo a b, ∃ v : Coordinates, HasDerivAt g v z ∧ g z 1+z*v 1<0)
    (hab : a≤b) (hb : atomFactor g b=0) {z : ℝ} (hz : z∈Set.Icc a b) :
    0≤atomFactor g z := by
  rw [← hb]
  exact (atomFactor_strictAntiOn hg hv).antitoneOn hz ⟨hab,le_rfl⟩ hz.2

theorem atom_lower_of_factor_nonneg {z B : ℝ} (hz : 0≤z) (h : 0≤1/2+z*B) :
    -z/2≤branchAtom z B := by
  have hp := mul_nonneg hz h
  unfold branchAtom
  nlinarith

theorem atomFactor_endpoint {g : ℝ → Coordinates} (hg : g zW=endpoint) : atomFactor g zW=0 := by
  unfold atomFactor
  rw [hg]
  norm_num [endpoint]
  field_simp [zW_pos.ne']
  norm_num

end polyak.Boundary.P1
