import polyak.Boundary.P2.Arc
import polyak.Boundary.P2.Inverse

/-! Article: Theorem p2arc(vii), actual derivatives of V on the closed P₂ arc. -/
namespace polyak.Boundary.P2
noncomputable section
open Spectral Filter
open scoped Topology

/-- Article: the actual boundary has its exact derivative within the whole closed P₂ arc. -/
theorem hasDerivWithinAt_V {z t : ℝ} (hz : z∈Set.Icc zeta1 zetaA)
    (ht : Real.cosh t=G z) : HasDerivWithinAt V (boundaryDerivative z t) exponentArc t := by
  apply hasDerivWithinAt_of_branch V ?_ hz ht
  intro z hz t ht
  exact optimal (arc_mem_interval hz) hz.1 hz.2 ht

/-- Article: in the open P₂ regime the boundary has its ordinary derivative. -/
theorem hasDerivAt_V {z t : ℝ} (hz : z∈Set.Ioo zeta1 zetaA)
    (ht : Real.cosh t=G z) : HasDerivAt V (boundaryDerivative z t) t := by
  have hm:=arc_mem_interval ⟨hz.1.le,hz.2.le⟩
  have hlo : Ga<Real.cosh t := by rw [ht]; exact G_strictAntiOn hm zetaA_mem hz.2
  have hhi : Real.cosh t<Boundary.G1 := by
    rw [ht,←G_zeta1]
    exact G_strictAntiOn zeta1_mem hm hz.1
  apply (hasDerivWithinAt_V ⟨hz.1.le,hz.2.le⟩ ht).hasDerivAt
  have hn : {s : ℝ | Ga<Real.cosh s ∧ Real.cosh s<Boundary.G1}∈𝓝 t :=
    ((isOpen_lt continuous_const Real.continuous_cosh).inter
      (isOpen_lt Real.continuous_cosh continuous_const)).mem_nhds ⟨hlo,hhi⟩
  exact Filter.mem_of_superset hn (fun s hs => ⟨hs.1.le,hs.2.le⟩)

/-- Article: the ordinary derivative of the optimal boundary is strictly bounded by one. -/
theorem abs_deriv_V_lt_one {z t : ℝ} (hz : z∈Set.Ioo zeta1 zetaA)
    (ht : Real.cosh t=G z) : |deriv V t|<1 := by
  rw [(hasDerivAt_V hz ht).deriv]
  exact abs_boundaryDerivative_lt_one (arc_mem_interval ⟨hz.1.le,hz.2.le⟩) ht

end
end polyak.Boundary.P2
