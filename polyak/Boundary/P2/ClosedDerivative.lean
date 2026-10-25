import polyak.Boundary.P2.SpiralJoin
import polyak.Boundary.P5.SlopeJoin

/-! Ordinary derivatives, including both joins, on the entire closed rational arc. -/
noncomputable section
namespace polyak.Boundary.P2
open Spectral

theorem hasDerivAt_V_closed {z t : ℝ} (hz : z∈Set.Icc zeta1 zetaA)
    (ht : Real.cosh t=G z) : HasDerivAt V (boundaryDerivative z t) t := by
  rcases hz.1.eq_or_lt with he|hl
  · subst z
    exact hasDerivAt_V_at_G1 (ht.trans G_zeta1)
  · rcases hz.2.eq_or_lt with he|hu
    · subst z
      exact P5.hasDerivAt_V_at_Ga ht
    · exact hasDerivAt_V ⟨hl,hu⟩ ht

theorem abs_deriv_V_lt_one_closed {z t : ℝ} (hz : z∈Set.Icc zeta1 zetaA)
    (ht : Real.cosh t=G z) : |deriv V t|<1 := by
  rw [(hasDerivAt_V_closed hz ht).deriv]
  exact abs_boundaryDerivative_lt_one (arc_mem_interval hz) ht

end polyak.Boundary.P2

namespace polyak.Boundary.P5
open Spectral

theorem hasDerivAt_V_closed {t : ℝ} (hl : 1<Real.cosh t) (hu : Real.cosh t≤P2.Ga) :
    HasDerivAt V (boundaryDerivative t) t := by
  rcases hu.eq_or_lt with he|hh
  · rw [boundaryDerivative_at_Ga he]
    exact hasDerivAt_V_at_Ga he
  · exact hasDerivAt_V hl hh

theorem abs_deriv_V_lt_one_closed {t : ℝ} (hl : 1<Real.cosh t) (hu : Real.cosh t≤P2.Ga) :
    |deriv V t|<1 := by
  rw [(hasDerivAt_V_closed hl hu).deriv]
  exact abs_boundaryDerivative_lt_one hl hu

end polyak.Boundary.P5
