import jacobi.Reference.CharacteristicNormalization
import jacobi.Complex.GammaModulus

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
The proved negative-energy asymptotic of the actual reference
characteristic gives the vertical Gamma modulus asymptotic. This is
the boundary input for the half-plane Phragmen--Lindelof argument;
no complex Stirling formula is assumed.
Use: gamma_vertical_weight_limit transfers the already proved genuine characteristic asymptotic to the imaginary-axis boundary estimate for Gamma quotients.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology ComplexConjugate
set_option backward.isDefEq.respectTransparency false

/-- The actual negative-axis reference characteristic is the reciprocal squared modulus of its vertical Gamma factor.
Use: gamma_vertical_weight_limit transfers the already proved genuine characteristic asymptotic to the imaginary-axis boundary estimate for Gamma quotients.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: substitute the genuine frequency i*pi*y in the original characteristic and use Gamma conjugation and the complex norm identity. -/
theorem characteristicTau_vertical_gamma (s y : ℝ) :
    (characteristicTau (2*s-3/2)
      ((jacobi.Jacobi.endpointCorrection (2*s-3/2)-(Real.pi*y)^2:ℝ):ℂ)).re=
        (‖Complex.Gamma ((s:ℂ)+Complex.I*(y:ℂ))‖^2)⁻¹ := by
  -- The same original characteristic is evaluated through its root-independent frequency formula.
  have hg : gamma (2*s-3/2)=s := by dsimp [gamma]; ring
  have hsq : (Complex.I*((Real.pi*y:ℝ):ℂ))^2=
      ((jacobi.Jacobi.endpointCorrection (2*s-3/2)-(Real.pi*y)^2:ℝ):ℂ)-
        (jacobi.Jacobi.endpointCorrection (2*s-3/2):ℂ) := by
    push_cast
    rw [mul_pow,Complex.I_sq]
    ring
  have harg : Complex.I*((Real.pi*y:ℝ):ℂ)/(Real.pi:ℂ)=Complex.I*(y:ℂ) := by
    push_cast
    field_simp
  rw [characteristicTau_eq _ hsq,characteristicGamma,hg,harg,← mul_inv]
  have hc : (s:ℂ)-Complex.I*(y:ℂ)=conj ((s:ℂ)+Complex.I*(y:ℂ)) := by simp [sub_eq_add_neg]
  rw [hc,Complex.Gamma_conj,mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_inv,Complex.ofReal_re]

/-- The normalized reciprocal squared vertical Gamma modulus has a genuine finite strictly positive limit for every shift greater than one quarter.
Use: bounds the imaginary-axis values of normalized Gamma quotients, allowing halfPlane_bound to prove the sharp uniform complex-frequency power estimate for Delta_tau.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: use alpha=2*s-3/2 in the proved reference negative-axis limit, replace its frequency by pi*y and cancel the fixed positive power of pi. -/
theorem gamma_vertical_weight_limit {s : ℝ} (hs : 1/4<s) :
    ∃ L : ℝ,0<L ∧ Tendsto (fun y : ℝ =>
      y^(2*s-1)*Real.exp (-Real.pi*y)/
        ‖Complex.Gamma ((s:ℂ)+Complex.I*(y:ℂ))‖^2) atTop (𝓝 L) := by
  -- The complex Gamma estimate is deduced from the already normalized original beta integral.
  have ha : -1<2*s-3/2 := by linarith
  let p : ℝ := 2*s-1
  let L : ℝ := (Real.pi^(2*s-3/2)/(2*Real.sqrt Real.pi))/Real.pi^p
  have hpi : 0<Real.pi^p := Real.rpow_pos_of_pos Real.pi_pos _
  refine ⟨L,by dsimp [L]; positivity,?_⟩
  have ht : Tendsto (fun y : ℝ => Real.pi*y) atTop atTop :=
    tendsto_id.const_mul_atTop Real.pi_pos
  have hh := ((characteristicTau_negative_asymptotic ha).comp ht).div_const (Real.pi^p)
  change Tendsto _ _ (𝓝 L) at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  dsimp only [Function.comp_apply]
  rw [show 2*s-3/2+1/2=p by dsimp [p]; ring,
    characteristicTau_vertical_gamma,Real.mul_rpow Real.pi_pos.le hy.le]
  rw [show -(Real.pi*y)= -Real.pi*y by ring]
  dsimp only [p]
  field_simp [hpi.ne']

end
end jacobi.Reference
