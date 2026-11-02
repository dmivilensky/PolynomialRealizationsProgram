import jacobi.Reference.CosineHypergeometric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
The original angular cosine substitution is monotone, with its genuine
Jacobian. Euler's proved transformation identifies the cosine divided
by the half-angle cosine with the exact Gauss function whose denominator
is raised by beta convolution.
Source: the Mehler--Dirichlet substitution, DLMF 14.12.1; proved here.
Use: changes the literal Mehler--Dirichlet integral to the beta-convolution integral.
-/
namespace jacobi.Reference.Hypergeometric
noncomputable section
open Real Set MeasureTheory _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The real angular version of the original cosine coordinate.
Use: changes the literal Mehler--Dirichlet integral to the beta-convolution integral.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def angularCoordinate (v : ℝ) : ℝ := (1-Real.cos v)/2

/-- The real coordinate embeds exactly as the actual complex cosine argument.
Use: transfers the already proved entire cosine representation to the original real integration variable.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: real inclusion commutes with the actual cosine and affine arithmetic. -/
theorem angularCoordinate_cast (v : ℝ) : (angularCoordinate v:ℂ)=cosineArgument (v:ℂ) := by
  simp [angularCoordinate,cosineArgument]

/-- The literal angular coordinate has its genuine nonnegative physical Jacobian.
Use: applies the community change-of-variables theorem to the original singular endpoint integrals.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: differentiate the actual real cosine and the affine outer map. -/
theorem angularCoordinate_hasDerivAt (v : ℝ) :
    HasDerivAt angularCoordinate (Real.sin v/2) v := by
  convert! ((hasDerivAt_const v (1:ℝ)).sub (Real.hasDerivAt_cos v)).div_const 2 using 1
  simp

/-- The original angular cosine coordinate increases strictly before pi and has its true zero endpoint.
Use: its physical integration segment maps exactly to [0,x], with every interior beta base positive.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the community strict decrease of the real cosine reverses under subtraction from one. -/
theorem angularCoordinate_properties : angularCoordinate 0=0 ∧
    StrictMonoOn angularCoordinate (Icc (0:ℝ) Real.pi) := by
  refine ⟨by simp [angularCoordinate],?_⟩
  intro u hu v hv huv
  have hh := Real.strictAntiOn_cos hu hv huv
  dsimp [angularCoordinate]
  linarith

/-- Every physical angular point before pi has its actual coordinate in the original Gauss convergence interval.
Use: both the cosine representation and beta convolution apply to every original angular integration point.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the global cosine upper bound gives nonnegativity; strict cosine decrease up to pi gives the strict upper endpoint. -/
theorem angularCoordinate_mem {v : ℝ} (hv : v∈Ico (0:ℝ) Real.pi) :
    angularCoordinate v∈Ico (0:ℝ) 1 := by
  have hh := Real.strictAntiOn_cos ⟨hv.1,hv.2.le⟩ ⟨Real.pi_pos.le,le_rfl⟩ hv.2
  rw [Real.cos_pi] at hh
  dsimp [angularCoordinate]
  constructor <;> linarith [Real.cos_le_one v]

/-- The genuine angular coordinate is strictly positive in the physical open interval.
Use: cancels only genuinely nonzero endpoint powers in the Abel Jacobian.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: strict monotonicity from the original zero endpoint gives strict positivity. -/
theorem angularCoordinate_pos {v : ℝ} (hv : v∈Ioo (0:ℝ) Real.pi) : 0<angularCoordinate v := by
  have hh := angularCoordinate_properties.2 ⟨le_rfl,Real.pi_pos.le⟩ ⟨hv.1.le,hv.2.le⟩ hv.1
  simpa only [angularCoordinate_properties.1] using hh

/-- The literal beta coordinate has the exact square-root Jacobian factor, with the positive branch fixed by the physical interval.
Use: converts the actual angular cosine integral to beta convolution in mehler_beta_identity.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: sqrt(x)=sin(v/2) on 0<v<pi. The real power -1/2 is its
genuine inverse, and the ordinary double-angle identity cancels the
strictly positive sine factor. -/
theorem angularCoordinate_jacobian {v : ℝ} (hv : v∈Ioo (0:ℝ) Real.pi) :
    (angularCoordinate v)^(-1/2:ℝ)*(Real.sin v/2)=Real.cos (v/2) := by
  -- Positivity fixes the square-root sign and justifies the cancellation.
  have hs : 0<Real.sin (v/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hv.1]) (by linarith [hv.2,Real.pi_pos])
  have hu := angularCoordinate_pos hv
  have hroot : Real.sqrt (angularCoordinate v)=Real.sin (v/2) := by
    rw [angularCoordinate,← Real.abs_sin_half,abs_of_pos hs]
  rw [show (-1/2:ℝ)= -(1/2) by ring,Real.rpow_neg hu.le,← Real.sqrt_eq_rpow,hroot]
  have hd := Real.sin_two_mul (v/2)
  rw [show 2*(v/2)=v by ring] at hd
  rw [hd]
  field_simp [hs.ne']

/-- The actual cosine has exactly the half-angle weighted Gauss representation used in the beta integral.
Use: removes the square-root Jacobian from the original Mehler--Dirichlet integrand before beta convolution.
Article: jacobi, Lemma C.1.
Source: the classical trigonometric Gauss identity, proved here from Euler's transformation and the genuine cosine equation.
Proof: apply the proved Euler transformation to the two half-shifted
parameters. The remaining Gauss function is the actual cosine. Its
power factor is the inverse positive half-angle cosine, which cancels
the printed multiplier, including at v=0. -/
theorem cosine_beta_representation (lam : ℂ) {v : ℝ} (hv : v∈Ico (0:ℝ) Real.pi) :
    Complex.cos (lam*(v:ℂ))=(Real.cos (v/2):ℂ)*
      ordinaryHypergeometric ((1/2:ℂ)-lam) ((1/2:ℂ)+lam) (1/2:ℂ) (angularCoordinate v:ℂ) := by
  -- The Euler identity is applied to the same actual convergent community Gauss series.
  have hu := angularCoordinate_mem hv
  have hnorm : ‖(angularCoordinate v:ℂ)‖<1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu.1]
    exact hu.2
  have hcos : 0<Real.cos (v/2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [hv.1,Real.pi_pos],by linarith [hv.2]⟩
  have he := euler_transform (a := (1/2:ℂ)-lam) (b := (1/2:ℂ)+lam)
    (c := (1/2:ℂ)) (by norm_num) hnorm
  have hd : (1/2:ℂ)-((1/2:ℂ)-lam)-((1/2:ℂ)+lam)= -1/2 := by ring
  have hm : (1/2:ℂ)-((1/2:ℂ)-lam)=lam := by ring
  have hp : (1/2:ℂ)-((1/2:ℂ)+lam)= -lam := by ring
  have hcheb := cosine_hypergeometric (-lam) hv
  simp only [neg_neg,neg_mul,Complex.cos_neg] at hcheb
  rw [hd,hm,hp,angularCoordinate_cast,hcheb] at he
  have hpow : (1-cosineArgument (v:ℂ))^(-1/2:ℂ)=((Real.cos (v/2))⁻¹:ℂ) := by
    have hroot : Real.sqrt (1-angularCoordinate v)=Real.cos (v/2) := by
      rw [show 1-angularCoordinate v=(1+Real.cos v)/2 by dsimp [angularCoordinate]; ring,
        ← Real.cos_half (by linarith [hv.1,Real.pi_pos] : -Real.pi≤v) hv.2.le]
    have hreal : (1-angularCoordinate v)^(-1/2:ℝ)=(Real.cos (v/2))⁻¹ := by
      rw [show (-1/2:ℝ)= -(1/2) by ring,Real.rpow_neg (by linarith [hu.2] : 0≤1-angularCoordinate v),
        ← Real.sqrt_eq_rpow,hroot]
    rw [← angularCoordinate_cast,show (1:ℂ)-(angularCoordinate v:ℂ)=((1-angularCoordinate v:ℝ):ℂ) by push_cast; rfl,
      show (-1/2:ℂ)=((-1/2:ℝ):ℂ) by norm_num,← Complex.ofReal_cpow (by linarith [hu.2] : 0≤1-angularCoordinate v)]
    exact_mod_cast hreal
  rw [hpow] at he
  rw [angularCoordinate_cast,he,← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hcos.ne'),one_mul]

end
end jacobi.Reference.Hypergeometric
