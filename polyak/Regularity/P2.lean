import polyak.Boundary.P2.Analytic
import polyak.Regularity.Inverse

/-! Article: regularity of the exact original rate in the open rational P₂ regime. -/
namespace polyak.Regularity
noncomputable section
open Spectral Boundary Set

theorem conditionRate_analyticAt_p2 {κ : ℝ} (hκ : 1<κ)
    (hG : Real.cosh (T (Dynamics.conditionQ κ))∈Ioo P2.Ga G1) :
    AnalyticAt ℝ conditionRate κ := by
  obtain ⟨z,hparam,_⟩:=P2.existsUnique_parameter ⟨hG.1.le,hG.2.le⟩
  have hz : z∈Icc P2.zeta1 P2.zetaA ∧ Real.cosh (T (Dynamics.conditionQ κ))=P2.G z :=
    ⟨hparam.1,hparam.2.symm⟩
  have hz' : z∈Ioo P2.zeta1 P2.zetaA := by
    constructor
    · apply lt_of_le_of_ne hz.1.1
      intro he
      have ht:=hz.2
      rw [←he,P2.G_zeta1] at ht
      linarith [hG.2]
    · apply lt_of_le_of_ne hz.1.2
      intro he
      have ht:=hz.2
      rw [he] at ht
      change Real.cosh (T (Dynamics.conditionQ κ))=P2.Ga at ht
      linarith [hG.1]
  apply conditionRate_analyticAt_of_boundary hκ (P2.V_analyticAt hz' hz.2)
  exact ne_of_lt ((abs_lt.mp (P2.abs_deriv_V_lt_one hz' hz.2)).2)

end
end polyak.Regularity
