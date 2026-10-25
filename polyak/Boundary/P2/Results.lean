import polyak.Boundary.P2.SpiralJoin
import polyak.Boundary.P2.Polynomial

/-! Article: Theorem p2arc. Source-facing conclusions on the complete closed rational arc. -/
namespace polyak.Boundary.P2
noncomputable section
open Spectral

/-- Article: P₂ is optimal throughout the complete physical G interval, for both signs of t. -/
theorem p2_arc {t : ℝ} (ht : Real.cosh t∈Set.Icc Ga Boundary.G1) :
    ∃! z : ℝ,z∈Set.Icc zeta1 zetaA ∧ Real.cosh t=G z ∧
      V t=Real.arsinh (u z) := by
  obtain ⟨z,hz,hu⟩:=existsUnique_parameter ht
  refine ⟨z,⟨hz.1,hz.2.symm,optimal (arc_mem_interval hz.1) hz.1.1 hz.1.2 hz.2.symm⟩,?_⟩
  intro z' hz'
  exact hu z' ⟨hz'.1,hz'.2.1.symm⟩

/-- Article: the actual two-atom measure is optimal, with its specified affine minimizer. -/
theorem spectrum_optimal {z t : ℝ} (hz : z∈Set.Icc zeta1 zetaA) (ht : Real.cosh t=G z) :
    Feasible (V t) t (spectrum z (arc_mem_interval hz) hz.1) (d z/Real.sinh t) := by
  rw [optimal (arc_mem_interval hz) hz.1 hz.2 ht]
  unfold Feasible
  rw [Real.sinh_arsinh]
  exact feasibleU (arc_mem_interval hz) hz.1 hz.2 ht

/-- Article: all strict decimal enclosures of the full P₂ arc are exact rational bounds. -/
theorem data_bounds {z : ℝ} (hz : z∈Set.Icc zeta1 zetaA) :
    (10233/10000<G z ∧ G z<10337/10000) ∧
    (511/1000<u z ∧ u z<517/1000) ∧
    (-101/200<x z ∧ x z< -12/25) ∧
    (1/4<y z ∧ y z<57/200) ∧
    (0≤p z ∧ p z<1) ∧ (p z=0↔z=zeta1) ∧
    (181/500<W z ∧ W z<183/500) ∧ (0<slope z ∧ slope z<1) := by
  have hm:=arc_mem_interval hz
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,x_bounds hm,y_bounds hm,p_mem hm hz.1,
    p_eq_zero_iff hm hz.1,⟨?_,?_⟩,slope_bounds hm⟩
  · linarith [G_lower_positive z hm]
  · linarith [G_upper_positive z hm]
  · linarith [u_lower_positive z hm]
  · linarith [u_upper_positive z hm]
  · linarith [W_lower_positive z hm]
  · linarith [W_upper_positive z hm]

end
end polyak.Boundary.P2
