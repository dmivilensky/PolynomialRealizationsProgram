import krylov.Functions.PlanarRFCFSolve

/-!
Article: main_krylov, thm:Fplanar, genuine finite-scale RFC-F response.
Use: derive the sharp leading polynomial from the implemented observed
model solve, with a uniform fourth-order true-gradient remainder.
Source: exact model normal equations, true cubic Taylor identity and compact
coefficient-ball bounds; no output or correction expansion is assumed.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Tensor.BinaryCubic krylov.Methods krylov.Correction
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator

/-- The actual observed normalized model retains its true positive margin.
Article: main_krylov, thm:Fplanar. -/
theorem planeRFCFModel_lower (p r : ℝ) (hp : 0≤p) (t : krylov.Tensor.BinaryCubic) (v : Plane) :
    (1-p*‖planeRFCFModelOperator r t‖)*‖v‖^2≤ inner ℝ v
      ((ContinuousLinearMap.id ℝ Plane+p • planeRFCFModelOperator r t) v) := by
  have hh := (abs_real_inner_le_norm v (planeRFCFModelOperator r t v)).trans
    (mul_le_mul_of_nonneg_left ((planeRFCFModelOperator r t).le_opNorm v) (norm_nonneg _))
  have hl := (abs_le.mp hh).1
  simp only [_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.id_apply,inner_add_right,
    inner_smul_right,real_inner_self_eq_norm_sq]
  nlinarith only [mul_le_mul_of_nonneg_left hl hp]

/-- The size of the actual model correction follows from its solved normal
equation and genuine curvature. Article: main_krylov, thm:Fplanar. -/
theorem planeRFCFCorrection_norm (p r : ℝ) (hp : 0<p) (hr : r≠0)
    (t : krylov.Tensor.BinaryCubic) (hsmall : p*‖planeRFCFModelOperator r t‖≤1/2) :
    ‖planeRFCFCorrection p r t‖≤2*‖planeTerminalRho r t‖*p^2 := by
  have hpos v (hv : v≠0) : 0 < inner ℝ v
      ((ContinuousLinearMap.id ℝ Plane+p • planeRFCFModelOperator r t) v) := by
    have hh := planeRFCFModel_lower p r hp.le t v
    have hn := sq_pos_of_pos (norm_pos_iff.mpr hv)
    nlinarith only [hh,mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖v‖),hn]
  have he := planeRFCFCorrection_equation p r hp.ne' hr t hpos
  let v := planeRFCFCorrection p r t
  have hv : v=(-p^2 • planeTerminalRho r t)-p • planeRFCFModelOperator r t v :=
    eq_sub_of_add_eq he
  have hh := norm_sub_le (-p^2 • planeTerminalRho r t) (p • planeRFCFModelOperator r t v)
  simp only [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (sq_nonneg p),abs_of_pos hp] at hh
  have hh' : ‖v‖≤p^2*‖planeTerminalRho r t‖+p*(‖planeRFCFModelOperator r t‖*‖v‖) := by
    calc
      _ = ‖(-p^2 • planeTerminalRho r t)-p • planeRFCFModelOperator r t v‖ := congrArg norm hv
      _ ≤ _ := hh.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
        ((planeRFCFModelOperator r t).le_opNorm v) hp.le))
  nlinarith only [hh',mul_le_mul_of_nonneg_right hsmall (norm_nonneg v)]

/-- Uniform actual normalized-model bounds on the whole original binary ball.
Article: main_krylov, thm:Fplanar. -/
theorem planeRFCF_uniform_bounds (r : ℝ) :
    ∃ M : ℝ, 0<M ∧ ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      ‖planeTerminalOperator r t‖≤M ∧ ‖planeTerminalRho r t‖≤M ∧
      ‖planeRFCFModelOperator r t‖≤M := by
  obtain ⟨B,hB,hbound⟩ := planeTerminal_uniform_bounds r
  have hc : Continuous (fun q : Fin 4 → ℝ=>planeRFCFModelOperator r (binaryFromVector q)) := by
    unfold planeRFCFModelOperator binaryFromVector planeOfPair
    fun_prop
  obtain ⟨A,hA⟩ := (isCompact_closedBall (0 : Fin 4 → ℝ) 1).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨B+|A|+1,by positivity,?_⟩
  intro t ht
  have hb := hbound t ht
  have hm := hA (binaryCoefficientVector t) (by simpa only [mem_closedBall,dist_zero_right] using binaryCoefficientVector_bound ht)
  rw [binaryFromVector_coefficientVector] at hm
  exact ⟨hb.1.trans (by linarith only [abs_nonneg A]),hb.2.trans (by linarith only [abs_nonneg A]),
    hm.trans (by linarith only [le_abs_self A,hB])⟩

set_option maxHeartbeats 1000000 in
/-- The true value-corrected observed solve has the full printed RFC-F
leading polynomial with uniform O(p⁴) actual scalar-gradient error.
Article: main_krylov, thm:Fplanar, exact finite-scale C_Y realization. -/
theorem planeRFCFOutput_gradient_remainder (r : ℝ) (hr : r≠0) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ p : ℝ, 0<p → p<ε₀ →
      ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      ‖gradient (planeCubicObjective p r t) (planeRFCFOutput p r t)+
        p^3 • ((planeTerminalOperator r t-planeRFCFModelOperator r t) (planeTerminalRho r t))‖≤C*p^4 := by
  obtain ⟨M,hM,hbound⟩ := planeRFCF_uniform_bounds r
  obtain ⟨B,hB,hhomogeneous⟩ := planeCubic_homogeneous_uniform_bound r
  refine ⟨1/(2*(M+1)),4*M^3+B*(2*M)^2,by positivity,by positivity,?_⟩
  intro p hp hep t ht
  obtain ⟨hLt,hρ,hMt⟩ := hbound t ht
  let v := planeRFCFCorrection p r t
  let ρ := planeTerminalRho r t
  let Lt := planeTerminalOperator r t
  let Mt := planeRFCFModelOperator r t
  let E := Lt-Mt
  have hpm : p*M≤1/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0<2*(M+1))).mp hep
    nlinarith only [hh,hp]
  have hsmall : p*‖Mt‖≤1/2 := (mul_le_mul_of_nonneg_left hMt hp.le).trans hpm
  have hv : ‖v‖≤2*M*p^2 := (planeRFCFCorrection_norm p r hp hr t hsmall).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ (by norm_num : (0:ℝ)≤2)) (sq_nonneg _))
  have hpos z (hz : z≠0) : 0 < inner ℝ z ((ContinuousLinearMap.id ℝ Plane+p • Mt) z) := by
    have hh := planeRFCFModel_lower p r hp.le t z
    have hn := sq_pos_of_pos (norm_pos_iff.mpr hz)
    nlinarith only [hh,mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖z‖),hn]
  have hsolve := planeRFCFCorrection_equation p r hp.ne' hr t hpos
  change v+p • Mt v= -p^2 • ρ at hsolve
  have hE : ‖E‖≤2*M := (norm_sub_le _ _).trans (by linarith only [hLt,hMt])
  have hjet : ‖v+p^2 • ρ‖≤2*M^2*p^3 := by
    have he : v+p^2 • ρ= -p • Mt v := by
      calc
        _ = v-(-p^2 • ρ) := by module
        _ = v-(v+p • Mt v) := by rw [hsolve]
        _ = _ := by module
    rw [he,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos hp]
    calc
      _ ≤ p*(‖Mt‖*‖v‖) := mul_le_mul_of_nonneg_left (Mt.le_opNorm v) hp.le
      _ ≤ p*(M*(2*M*p^2)) := mul_le_mul_of_nonneg_left
        (mul_le_mul hMt hv (norm_nonneg _) hM.le) hp.le
      _ = _ := by ring
  have hlin : p^2 • ρ+v+p • Lt v+p^3 • E ρ=p • E (v+p^2 • ρ) := by
    have hz : p^2 • ρ+v+p • Mt v=0 := by rw [add_assoc,hsolve]; module
    calc
      _ = p • E (v+p^2 • ρ)+(p^2 • ρ+v+p • Mt v) := by
        dsimp only [E]
        simp only [_root_.sub_apply,map_add,map_smul]
        module
      _ = _ := by rw [hz,add_zero]
  change ‖gradient (planeCubicObjective p r t) (planeOfPair (p,r*p)+v)+p^3 • E ρ‖≤_
  rw [planeCubicGradient_terminal_identity]
  have he : p^2 • ρ+v+p • Lt v+
      planeOfPair (planarValueCoordinateDerivative 0 r t (pairOfPlane v))+p^3 • E ρ=
      p • E (v+p^2 • ρ)+planeOfPair (planarValueCoordinateDerivative 0 r t (pairOfPlane v)) := by
    rw [←hlin]
    abel
  rw [he]
  have hsq : ‖v‖^2≤(2*M)^2*p^4 :=
    ((sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤2*M*p^2)).mpr hv).trans_eq (by ring)
  apply (norm_add_le _ _).trans
  rw [norm_smul,Real.norm_of_nonneg hp.le]
  calc
    _ ≤ p*(‖E‖*‖v+p^2 • ρ‖)+B*‖v‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_left (E.le_opNorm _) hp.le) (hhomogeneous t ht v)
    _ ≤ p*((2*M)*(2*M^2*p^3))+B*((2*M)^2*p^4) := add_le_add
      (mul_le_mul_of_nonneg_left (mul_le_mul hE hjet (norm_nonneg _) (by positivity)) hp.le)
      (mul_le_mul_of_nonneg_left hsq hB.le)
    _ = _ := by ring

 /-- The actual gradient norm has the exact binary RFC-F leading objective,
with one uniform fourth-order error over the entire original tensor ball.
Article: main_krylov, thm:Fplanar, C_Y finite-scale norm formula. -/
theorem planeRFCFOutput_norm_remainder (r : ℝ) (hr : r≠0) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ p : ℝ, 0<p → p<ε₀ →
      ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      |‖gradient (planeCubicObjective p r t) (planeRFCFOutput p r t)‖-
        (r^2/4*rfcObjective r t)*p^3|≤C*p^4 := by
  obtain ⟨ep,C,hep,hC,hrem⟩ := planeRFCFOutput_gradient_remainder r hr
  refine ⟨ep,C,hep,hC,?_⟩
  intro p hp he t ht
  have hh := abs_norm_sub_norm_le (gradient (planeCubicObjective p r t) (planeRFCFOutput p r t))
    (-p^3 • ((planeTerminalOperator r t-planeRFCFModelOperator r t) (planeTerminalRho r t)))
  rw [neg_smul,sub_neg_eq_add,norm_neg,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hp.le 3),planeRFCF_leading_norm] at hh
  rw [show p^3*(r^2/4*rfcObjective r t)=r^2/4*rfcObjective r t*p^3 by ring] at hh
  exact hh.trans (hrem p hp he t ht)

end
end krylov.Functions
