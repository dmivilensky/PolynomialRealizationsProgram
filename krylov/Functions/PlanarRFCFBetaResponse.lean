import krylov.Functions.PlanarRFCFBetaSolve
import krylov.Functions.PlanarRFCFResponse

/-!
Article: main_krylov, thm:Fplanar, uniform independent-base C_Y response.
Use: control the actual value-model solve for every independent beta of
size O(p), with its true scalar objective and actual gradient. Source:
positive model normal equations and the exact cancellation of the common
unknown diagonal. No response expansion or correction-size premise is used.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods krylov.Correction krylov.Tensor.BinaryCubic
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- A bounded true model perturbation retains its quantitative curvature.
Article: main_krylov, thm:Fplanar. -/
theorem planePerturbedModel_lower (p : ℝ) (hp : 0≤p) (W : Plane →L[ℝ] Plane) (v : Plane) :
    (1-p*‖W‖)*‖v‖^2≤ inner ℝ v ((ContinuousLinearMap.id ℝ Plane+p • W) v) := by
  have hh := (abs_real_inner_le_norm v (W v)).trans
    (mul_le_mul_of_nonneg_left (W.le_opNorm v) (norm_nonneg _))
  have hl := (abs_le.mp hh).1
  simp only [_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.id_apply,inner_add_right,
    inner_smul_right,real_inner_self_eq_norm_sq]
  nlinarith only [mul_le_mul_of_nonneg_left hl hp]

set_option maxHeartbeats 1200000 in
/-- The actual value-informed solve has the same sharp C_Y response for the
entire independent base interval |beta|≤B*p. The common unknown diagonal is
reconstructed by the true observations and cancels from the leading error.
Article: main_krylov, thm:Fplanar, full independent-beta upper family. -/
theorem planeBetaRFCFOutput_gradient_remainder (r B : ℝ) (hr : r≠0) (hB : 0≤B) :
    ∃ ep C : ℝ, 0<ep ∧ 0<C ∧ ∀ p b : ℝ, 0<p → p<ep → |b|≤B →
      ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      ‖gradient (planeBetaCubicObjective p r (p*b) t) (planeBetaRFCFOutput p r (p*b) t)+
        p^3 • ((planeTerminalOperator r t-planeRFCFModelOperator r t) (planeTerminalRho r t))‖≤C*p^4 := by
  obtain ⟨M,hM,hbound⟩ := planeRFCF_uniform_bounds r
  obtain ⟨H,hH,hhomogeneous⟩ := planeCubic_homogeneous_uniform_bound r
  let A := M+B*‖planeLastProjection‖+B+1
  have hA : 0<A := by dsimp only [A]; positivity
  have hMA : M≤A := by dsimp only [A]; nlinarith only [mul_nonneg hB (norm_nonneg planeLastProjection),hB]
  have hBA : B≤A := by dsimp only [A]; nlinarith only [mul_nonneg hB (norm_nonneg planeLastProjection),hM]
  refine ⟨1/(2*(A+1)),4*A^3+H*(2*A)^2,by positivity,by positivity,?_⟩
  intro p b hp hep hb t ht
  obtain ⟨hLt,hρ,hMt⟩ := hbound t ht
  let v := planeBetaRFCFCorrection p r (p*b) t
  let ρ := planeTerminalRho r t
  let L := planeTerminalOperator r t+b • planeLastProjection
  let W := planeRFCFModelOperator r t+b • planeLastProjection
  let E := L-W
  have hlast : ‖b • planeLastProjection‖≤B*‖planeLastProjection‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have hL : ‖L‖≤A := (norm_add_le _ _).trans ((add_le_add hLt hlast).trans (by dsimp only [A]; linarith))
  have hW : ‖W‖≤A := (norm_add_le _ _).trans ((add_le_add hMt hlast).trans (by dsimp only [A]; linarith))
  have hρA : ‖ρ‖≤A := hρ.trans hMA
  have hpA : p*A≤1/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0<2*(A+1))).mp hep
    nlinarith only [hh,hp]
  have hsmall : p*‖W‖≤1/2 := (mul_le_mul_of_nonneg_left hW hp.le).trans hpA
  have hβ : 1+p*b≠0 := by
    have hh : |p*b|≤1/2 := by
      rw [abs_mul,abs_of_pos hp]
      exact (mul_le_mul_of_nonneg_left hb hp.le).trans ((mul_le_mul_of_nonneg_left hBA hp.le).trans hpA)
    have hl := (abs_le.mp hh).1
    linarith
  have hpos z (hz : z≠0) : 0 < inner ℝ z ((ContinuousLinearMap.id ℝ Plane+p • W) z) := by
    have hh := planePerturbedModel_lower p hp.le W z
    have hn := sq_pos_of_pos (norm_pos_iff.mpr hz)
    nlinarith only [hh,mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖z‖),hn]
  have hsolve := planeBetaRFCFCorrection_equation p r b hp.ne' hr hβ t hpos
  change v+p • W v= -p^2 • ρ at hsolve
  have hv0 : v=(-p^2 • ρ)-p • W v := eq_sub_of_add_eq hsolve
  have hv : ‖v‖≤2*A*p^2 := by
    have hh := norm_sub_le (-p^2 • ρ) (p • W v)
    simp only [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (sq_nonneg p),abs_of_pos hp] at hh
    have hh' : ‖v‖≤p^2*‖ρ‖+p*(‖W‖*‖v‖) := by
      calc
        _ = ‖(-p^2 • ρ)-p • W v‖ := congrArg norm hv0
        _ ≤ _ := hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (W.le_opNorm v) hp.le))
    nlinarith only [hh',mul_le_mul_of_nonneg_right hsmall (norm_nonneg v),
      mul_le_mul_of_nonneg_left hρA (sq_nonneg p)]
  have hE : ‖E‖≤2*A := (norm_sub_le _ _).trans (by linarith only [hL,hW])
  have hjet : ‖v+p^2 • ρ‖≤2*A^2*p^3 := by
    have he : v+p^2 • ρ= -p • W v := by
      calc
        _ = v-(-p^2 • ρ) := by module
        _ = v-(v+p • W v) := by rw [hsolve]
        _ = _ := by module
    rw [he,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos hp]
    calc
      _ ≤ p*(‖W‖*‖v‖) := mul_le_mul_of_nonneg_left (W.le_opNorm v) hp.le
      _ ≤ p*(A*(2*A*p^2)) := mul_le_mul_of_nonneg_left
        (mul_le_mul hW hv (norm_nonneg _) hA.le) hp.le
      _ = _ := by ring
  have hlin : p^2 • ρ+v+p • L v+p^3 • E ρ=p • E (v+p^2 • ρ) := by
    have hz : p^2 • ρ+v+p • W v=0 := by rw [add_assoc,hsolve]; module
    calc
      _ = p • E (v+p^2 • ρ)+(p^2 • ρ+v+p • W v) := by
        dsimp only [E]
        simp only [_root_.sub_apply,map_add,map_smul]
        module
      _ = _ := by rw [hz,add_zero]
  have hEeq : E=planeTerminalOperator r t-planeRFCFModelOperator r t := planeBetaRFCF_discrepancy r b t
  rw [←hEeq]
  change ‖gradient (planeBetaCubicObjective p r (p*b) t) (planeOfPair (p,r*p)+v)+p^3 • E ρ‖≤_
  rw [planeBetaCubicGradient_terminal_identity]
  have he : p^2 • ρ+v+p • planeTerminalOperator r t v+(p*b) • planeLastProjection v+
      planeOfPair (planarValueCoordinateDerivative 0 r t (pairOfPlane v))+p^3 • E ρ=
      p • E (v+p^2 • ρ)+planeOfPair (planarValueCoordinateDerivative 0 r t (pairOfPlane v)) := by
    rw [←hlin]
    dsimp only [L]
    simp only [_root_.add_apply,_root_.smul_apply]
    module
  rw [he]
  have hsq : ‖v‖^2≤(2*A)^2*p^4 :=
    ((sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤2*A*p^2)).mpr hv).trans_eq (by ring)
  apply (norm_add_le _ _).trans
  rw [norm_smul,Real.norm_of_nonneg hp.le]
  calc
    _ ≤ p*(‖E‖*‖v+p^2 • ρ‖)+H*‖v‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_left (E.le_opNorm _) hp.le) (hhomogeneous t ht v)
    _ ≤ p*((2*A)*(2*A^2*p^3))+H*((2*A)^2*p^4) := add_le_add
      (mul_le_mul_of_nonneg_left (mul_le_mul hE hjet (norm_nonneg _) (by positivity)) hp.le)
      (mul_le_mul_of_nonneg_left hsq hH.le)
    _ = _ := by ring

/-- Actual independent-base RFC-F norm response, with the exact original
binary C_Y objective and a uniform fourth-order scalar-source error.
Article: main_krylov, thm:Fplanar. -/
theorem planeBetaRFCFOutput_norm_remainder (r B : ℝ) (hr : r≠0) (hB : 0≤B) :
    ∃ ep C : ℝ, 0<ep ∧ 0<C ∧ ∀ p b : ℝ, 0<p → p<ep → |b|≤B →
      ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      |‖gradient (planeBetaCubicObjective p r (p*b) t) (planeBetaRFCFOutput p r (p*b) t)‖-
        (r^2/4*rfcObjective r t)*p^3|≤C*p^4 := by
  obtain ⟨ep,C,hep,hC,hrem⟩ := planeBetaRFCFOutput_gradient_remainder r B hr hB
  refine ⟨ep,C,hep,hC,?_⟩
  intro p b hp he hb t ht
  have hh := abs_norm_sub_norm_le
    (gradient (planeBetaCubicObjective p r (p*b) t) (planeBetaRFCFOutput p r (p*b) t))
    (-p^3 • ((planeTerminalOperator r t-planeRFCFModelOperator r t) (planeTerminalRho r t)))
  rw [neg_smul,sub_neg_eq_add,norm_neg,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hp.le 3),planeRFCF_leading_norm] at hh
  rw [show p^3*(r^2/4*rfcObjective r t)=r^2/4*rfcObjective r t*p^3 by ring] at hh
  exact hh.trans (hrem p b hp he hb t ht)

end
end krylov.Functions
