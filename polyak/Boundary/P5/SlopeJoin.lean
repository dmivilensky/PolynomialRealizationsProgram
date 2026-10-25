import polyak.Boundary.P5.SlopeJoinEquality
import polyak.Boundary.P5.Derivative
import polyak.Boundary.P2.Derivative

/-! Ordinary differentiability of the actual boundary across both copies of Ga.
The KKT envelope identity proves exact slope matching before the one-sided
source derivatives are glued. -/
noncomputable section
namespace polyak.Boundary.P5
open Spectral
open scoped Topology

/-- The complete source derivative agrees with the rational derivative at the join. -/
theorem boundaryDerivative_at_Ga {t : ℝ} (ht : Real.cosh t=P2.Ga) :
    boundaryDerivative t=P2.boundaryDerivative P2.zetaA t := by
  unfold boundaryDerivative P2.boundaryDerivative
  rw [ht,SlopeJoin.source_slope_eq,SlopeJoin.endpoint_values.1]

/-- The actual boundary has its ordinary derivative at both P2/P5 switches. -/
theorem hasDerivAt_V_at_Ga {t : ℝ} (ht : Real.cosh t=P2.Ga) :
    HasDerivAt V (P2.boundaryDerivative P2.zetaA t) t := by
  have hp2:=P2.hasDerivWithinAt_V
    (show P2.zetaA∈Set.Icc P2.zeta1 P2.zetaA from ⟨P2.zeta1_lt_zetaA.le,le_rfl⟩) ht
  have hG : 1<Real.cosh t := by rw [ht]; linarith [P2.Ga_bounds.1]
  have hp5:=hasDerivWithinAt_V hG ht.le
  rw [boundaryDerivative_at_Ga ht] at hp5
  apply (hp2.union hp5).hasDerivAt
  have hn : {s : ℝ | 1<Real.cosh s ∧ Real.cosh s<Boundary.G1}∈𝓝 t :=
    ((isOpen_lt continuous_const Real.continuous_cosh).inter
      (isOpen_lt Real.continuous_cosh continuous_const)).mem_nhds
        ⟨hG,by change Real.cosh t<Boundary.G1; rw [ht]; exact P2.Ga_lt_G1⟩
  apply Filter.mem_of_superset hn
  intro s hs
  by_cases h : P2.Ga≤Real.cosh s
  · exact Or.inl ⟨h,hs.2.le⟩
  · exact Or.inr (le_of_not_ge h)

/-- The strict bound is an ordinary derivative bound at the join itself. -/
theorem abs_deriv_V_at_Ga_lt_one {t : ℝ} (ht : Real.cosh t=P2.Ga) : |deriv V t|<1 := by
  rw [(hasDerivAt_V_at_Ga ht).deriv]
  exact P2.abs_boundaryDerivative_lt_one P2.zetaA_mem ht

end polyak.Boundary.P5
