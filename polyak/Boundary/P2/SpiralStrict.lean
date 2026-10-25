import polyak.Boundary.P2.Parameter
import polyak.Boundary.P2.Arc

/-! Article: Proposition spiralsub, the exact rational P2 improvement over the spiral. -/
noncomputable section
namespace polyak.Boundary.P2
open Spectral

theorem spiral_improvement_identity {z : ℝ} (hz : z∈parameterInterval) :
    u z-(1-1/(2*G z))=8*(endpointCubic z)^2/((z^4-4)*(z^4+4)) := by
  have hz0 : z≠0 := (parameter_pos hz).ne'
  have hm : rMinus z≠0 := (rMinus_pos hz).ne'
  have hp : z^4+4≠0 := by positivity
  have hden : z^4-4≠0 := by
    have he : z^4-4=rMinus z*(z^2+2) := by unfold rMinus; ring
    rw [he]
    exact mul_ne_zero hm (by positivity)
  unfold u G endpointCubic qMinus
  field_simp [hz0,hm,hp,hden]
  unfold rMinus
  ring

theorem twist_strict_spiral {z : ℝ} (hz : z∈parameterInterval) (h1 : zeta1<z) :
    1-1/(2*G z)<u z := by
  have hc := endpointCubic_strictMonoOn zeta1_mem hz h1
  rw [endpointCubic_zeta1] at hc
  have hd : 0<z^4-4 := by
    have he : z^4-4=rMinus z*(z^2+2) := by unfold rMinus; ring
    rw [he]
    exact mul_pos (rMinus_pos hz) (by positivity)
  have he := spiral_improvement_identity hz
  have hp : 0<8*(endpointCubic z)^2/((z^4-4)*(z^4+4)) :=
    div_pos (mul_pos (by norm_num) (sq_pos_of_pos hc)) (mul_pos hd (by positivity))
  linarith

theorem strict_spiral {z t : ℝ} (hz : z∈parameterInterval) (h1 : zeta1<z) (ha : z≤zetaA)
    (ht : Real.cosh t=G z) : Real.arsinh (1-1/(2*Real.cosh t))<V t := by
  rw [optimal hz h1.le ha ht,ht]
  exact Real.arsinh_strictMono (twist_strict_spiral hz h1)

end polyak.Boundary.P2
