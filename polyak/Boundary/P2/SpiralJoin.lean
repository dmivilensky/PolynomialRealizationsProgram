import polyak.Boundary.P2.Derivative
import polyak.Boundary.P2.Endpoint
import polyak.Boundary.SpiralRegularity
import polyak.Boundary.SpiralEndpoint

/-! Article: the rational arc and the spiral have the same actual boundary derivative at G₁. -/
namespace polyak.Boundary.P2
noncomputable section
open Spectral
open scoped Topology

/-- Article: exact agreement of the two derivative formulas at the spiral switch. -/
theorem boundaryDerivative_zeta1 {t : ℝ} (ht : Real.cosh t=Boundary.G1) :
    boundaryDerivative zeta1 t=Boundary.spiralBoundaryDerivative t := by
  unfold boundaryDerivative Boundary.spiralBoundaryDerivative
  rw [u_zeta1,slope_zeta1,ht]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- Article: the actual V is differentiable across the spiral-to-P₂ switch. -/
theorem hasDerivAt_V_at_G1 {t : ℝ} (ht : Real.cosh t=Boundary.G1) :
    HasDerivAt V (boundaryDerivative zeta1 t) t := by
  have hp:=hasDerivWithinAt_V (show zeta1∈Set.Icc zeta1 zetaA from ⟨le_rfl,zeta1_lt_zetaA.le⟩)
    (ht.trans G_zeta1.symm)
  have hmem : t∈Boundary.spiralExponentArc := by
    change Boundary.G1≤Real.cosh t ∧ Real.cosh t≤Boundary.GW
    rw [ht]
    exact ⟨le_rfl,Boundary.G1_lt_GW.le⟩
  have hs:=Boundary.hasDerivWithinAt_V_spiral hmem
  rw [←boundaryDerivative_zeta1 ht] at hs
  apply (hp.union hs).hasDerivAt
  have hn : {s : ℝ | Ga<Real.cosh s ∧ Real.cosh s<Boundary.GW}∈𝓝 t :=
    ((isOpen_lt continuous_const Real.continuous_cosh).inter
      (isOpen_lt Real.continuous_cosh continuous_const)).mem_nhds
      (by change Ga<Real.cosh t ∧ Real.cosh t<Boundary.GW
          rw [ht]
          exact ⟨Ga_lt_G1,Boundary.G1_lt_GW⟩)
  apply Filter.mem_of_superset hn
  intro s hs
  by_cases h : Real.cosh s ≤ Boundary.G1
  · exact Or.inl ⟨hs.1.le,h⟩
  · exact Or.inr ⟨(le_of_not_ge h),hs.2.le⟩

/-- Article: the strict derivative bound includes the spiral-to-P₂ switch itself. -/
theorem abs_deriv_V_at_G1_lt_one {t : ℝ} (ht : Real.cosh t=Boundary.G1) : |deriv V t|<1 := by
  rw [(hasDerivAt_V_at_G1 ht).deriv]
  exact abs_boundaryDerivative_lt_one zeta1_mem (ht.trans G_zeta1.symm)

end
end polyak.Boundary.P2
