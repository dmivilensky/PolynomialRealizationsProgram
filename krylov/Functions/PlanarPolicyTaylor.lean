import krylov.Functions.PlanarCentrePolicy

/-!
Article: main_krylov, thm:Fplanar, matching actual-function upper bound.
Use: realize the optimal leading fibre centre by one explicit observation-only
output, uniformly over every actual admissible scalar cubic.
Source: exact polynomial gradient Taylor identity and uniform bounds on the
entire genuine coefficient ball; no output remainder is assumed.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Tensor.BinaryCubic
open scoped InnerProductSpace ENNReal

/-- Exact reconstruction in the genuine Hilbert plane.
Article: main_krylov, thm:Fplanar. -/
theorem planeOfPair_pairOfPlane (v : Plane) : planeOfPair (pairOfPlane v)=v := by
  ext i
  fin_cases i <;> rfl

/-- The actual Euclidean gradient has its exact terminal affine model plus
the genuine homogeneous quadratic cubic remainder.
Article: main_krylov, thm:Fplanar. -/
theorem planeCubicGradient_terminal_identity (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (v : Plane) :
    gradient (planeCubicObjective p r t) (planeOfPair (p,r*p)+v)=
      p^2 • planeTerminalRho r t+v+p • planeTerminalOperator r t v+
        planeOfPair (planarValueCoordinateDerivative 0 r t (pairOfPlane v)) := by
  rw [planeCubicGradient_actual]
  have hh := congrArg planeOfPair (planarCubicGradient_terminal_identity p r t (pairOfPlane v))
  rw [planeOfPair_sub,planeTerminalModel_eq,planeOfPair_pairOfPlane] at hh
  have he : pairOfPlane (planeOfPair (p,r*p)+v)=(p,r*p)+pairOfPlane v := rfl
  change planeOfPair (planarCubicGradient p r t (pairOfPlane (planeOfPair (p,r*p)+v)))=_
  rw [he]
  exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

set_option maxHeartbeats 600000 in
/-- Every admissible predicted terminal Hessian gives its actual leading
cubic discrepancy with a uniform genuine fourth-order remainder.
Article: main_krylov, thm:Fplanar, concrete function upper transfer. -/
theorem planeCubic_predicted_output_remainder (r : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → p≤1 →
      ∀ t u : krylov.Tensor.BinaryCubic, t.InBall → u.InBall →
      let ρ := planeTerminalRho r t
      let v := -p^2 • ρ+p^3 • planeTerminalOperator r u ρ
      ‖gradient (planeCubicObjective p r t) (planeOfPair (p,r*p)+v)-
        p^3 • (planeTerminalOperator r u-planeTerminalOperator r t) ρ‖≤C*p^4 := by
  obtain ⟨M,hM,hbound⟩ := planeTerminal_uniform_bounds r
  obtain ⟨B,hB,hhomogeneous⟩ := planeCubic_homogeneous_uniform_bound r
  let V := M+M^2
  have hV : 0<V := by dsimp only [V]; positivity
  refine ⟨M^3+B*V^2,by positivity,?_⟩
  intro p hp hp₁ t u ht hu
  let ρ := planeTerminalRho r t
  let Lt := planeTerminalOperator r t
  let Lu := planeTerminalOperator r u
  let v := -p^2 • ρ+p^3 • Lu ρ
  have hρ : ‖ρ‖≤M := (hbound t ht).2
  have hLt : ‖Lt‖≤M := (hbound t ht).1
  have hLu : ‖Lu‖≤M := (hbound u hu).1
  have hLuρ : ‖Lu ρ‖≤M^2 := (Lu.le_opNorm ρ).trans ((mul_le_mul hLu hρ (norm_nonneg _) hM.le).trans_eq (by ring))
  have hp₃ : p^3≤p^2 := by nlinarith only [mul_le_mul_of_nonneg_left hp₁ (sq_nonneg p)]
  have hv : ‖v‖≤V*p^2 := by
    have hn := norm_add_le (-p^2 • ρ) (p^3 • Lu ρ)
    simp only [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (sq_nonneg p),
      abs_of_nonneg (pow_nonneg hp.le 3)] at hn
    calc
      _ ≤ p^2*‖ρ‖+p^3*‖Lu ρ‖ := hn
      _ ≤ p^2*M+p^3*M^2 := add_le_add (mul_le_mul_of_nonneg_left hρ (sq_nonneg _))
        (mul_le_mul_of_nonneg_left hLuρ (pow_nonneg hp.le 3))
      _ ≤ V*p^2 := by dsimp only [V]; nlinarith only [mul_le_mul_of_nonneg_right hp₃ (sq_nonneg M)]
  have hrem := hhomogeneous t ht v
  have hvsq : ‖v‖^2≤V^2*p^4 := ((sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤V*p^2)).mpr hv).trans_eq (by ring)
  have hquartic : ‖Lt (Lu ρ)‖≤M^3 := (Lt.le_opNorm _).trans
    ((mul_le_mul hLt hLuρ (norm_nonneg _) hM.le).trans_eq (by ring))
  have he : p^2 • ρ+v+p • Lt v-p^3 • (Lu-Lt) ρ=p^4 • Lt (Lu ρ) := by
    dsimp only [v]
    simp only [map_add,map_smul,_root_.sub_apply]
    module
  change ‖gradient (planeCubicObjective p r t) (planeOfPair (p,r*p)+v)-p^3 • (Lu-Lt) ρ‖≤_
  rw [planeCubicGradient_terminal_identity]
  have he' : p^2 • ρ+v+p • Lt v+
      planeOfPair (planarValueCoordinateDerivative 0 r t (pairOfPlane v))-p^3 • (Lu-Lt) ρ=
      p^4 • Lt (Lu ρ)+planeOfPair (planarValueCoordinateDerivative 0 r t (pairOfPlane v)) := by
    rw [←he]
    abel
  rw [he']
  apply (norm_add_le _ _).trans
  rw [norm_smul,Real.norm_of_nonneg (pow_nonneg hp.le 4)]
  have hb := add_le_add (mul_le_mul_of_nonneg_left hquartic (pow_nonneg hp.le 4))
    (hrem.trans (mul_le_mul_of_nonneg_left hvsq hB.le))
  exact hb.trans_eq (by ring)

/-- The actual data-only centre output attains the full sharp leading
minimax constant on the entire original scalar cubic family, with one
uniform fourth-order remainder. Article: main_krylov, thm:Fplanar. -/
theorem planeCentreOutput_gradient_upper (r : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → p≤1 →
      ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      ‖gradient (planeCubicObjective p r t) (planeCentreOutput r p (observe r t))‖≤
        r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r*p^3+C*p^4 := by
  obtain ⟨C,hC,hremainder⟩ := planeCubic_predicted_output_remainder r
  refine ⟨C,hC,?_⟩
  intro p hp hp₁ t ht
  let u := planeCentreTensor r (observe r t)
  have hu : u.InBall := planeCentreTensor_inBall ht r
  have hobs : observe r t=observe r u := (observe_complete r _ _).symm
  have hρ := planeTerminalRho_eq r t u hobs
  have hh := hremainder p hp hp₁ t u ht hu
  have hout : planeCentreOutput r p (observe r t)=planeOfPair (p,r*p)+
      (-p^2 • planeTerminalRho r t+p^3 • planeTerminalOperator r u (planeTerminalRho r t)) := by
    unfold planeCentreOutput
    change planeOfPair (p,r*p)-p^2 • planeTerminalRho r u+p^3 • planeTerminalOperator r u (planeTerminalRho r u)=_
    rw [←hρ]
    module
  rw [hout]
  have hb := planeCentre_leading_bound ht r
  calc
    _ ≤ ‖gradient (planeCubicObjective p r t) _-
        p^3 • (planeTerminalOperator r u-planeTerminalOperator r t) (planeTerminalRho r t)‖+
        ‖p^3 • (planeTerminalOperator r u-planeTerminalOperator r t) (planeTerminalRho r t)‖ := norm_le_norm_sub_add _ _
    _ ≤ C*p^4+p^3*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r) := by
      rw [norm_smul,Real.norm_of_nonneg (pow_nonneg hp.le 3)]
      exact add_le_add hh (mul_le_mul_of_nonneg_left hb (pow_nonneg hp.le 3))
    _ = _ := by ring

end
end krylov.Functions
