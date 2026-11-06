import nesterov.Trace.BoundaryAlgebra
import nesterov.Trace.Numerator

/-! The exact TMM transfer identity and its step, lead and zero-symbol consequences. -/
namespace nesterov.Trace
noncomputable section
open Polynomial Complex
namespace DoubleRootData
variable (A : DoubleRootData)

theorem tmmTransfer_iff_cross_identity : A.tmmTransfer ↔
    (C 3*X-C 1)*A.v= -(X-C 1)^2*A.u := by
  have hx : ((X-C (1:ℝ))^2)≠0 := pow_ne_zero 2 (X_sub_C_ne_zero 1)
  unfold tmmTransfer
  have hv : A.v=(X-C 1)^2*A.q := A.factor
  rw [hv]
  constructor
  · intro hh
    rw [hh]
    norm_num
    ring
  · intro hh
    apply mul_left_cancel₀ hx
    linear_combination hh

theorem tmmTransfer_phi_eq_numerator (h : A.tmmTransfer) : A.phi 1=A.numerator := by
  have hv : A.v=(X-C 1)^2*A.q := A.factor
  rw [phi,hv,h]
  unfold numerator
  simp only [C_ofNat,C_1]
  ring

theorem numerator_eq_phi_iff_tmmTransfer : A.numerator=A.phi 1 ↔ A.tmmTransfer := by
  refine ⟨fun hh=>?_,fun hh=>(A.tmmTransfer_phi_eq_numerator hh).symm⟩
  have hv : A.v=(X-C 1)^2*A.q := A.factor
  unfold tmmTransfer
  unfold numerator phi at hh
  rw [hv] at hh
  norm_num only [C_1,C_ofNat] at hh ⊢
  linear_combination -hh

theorem tmmTransfer_step (h : A.tmmTransfer) : A.y=2 := by
  have hh := congrArg (Polynomial.eval (1:ℝ)) h
  simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_X,
    A.u_one,A.q_one] at hh
  field_simp [A.y_pos.ne'] at hh
  linarith

theorem tmmTransfer_effectiveLead (h : A.tmmTransfer) : A.effectiveLead=1/2 := by
  have hy := A.tmmTransfer_step h
  have hh := congrArg (fun p : Polynomial ℝ=>p.derivative.eval 1) h
  simp only [Polynomial.derivative_mul,Polynomial.derivative_sub,Polynomial.derivative_C,
    Polynomial.derivative_X,zero_sub,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_neg,
    Polynomial.eval_zero,Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_X,A.q_one] at hh
  rw [hy] at hh
  norm_num at hh
  unfold effectiveLead
  rw [hy]
  linarith

theorem tmmTransfer_zero_symbol (h : A.tmmTransfer) : ∀ ω : ℝ,A.symbol ω=0 := by
  intro ω
  let z := Complex.exp ((ω:ℂ)*Complex.I)
  have hz : Complex.normSq z=1 := by simp [z,Complex.normSq_eq_norm_sq]
  have hφ : eval (A.phi 1) z= -z*(z+1)*eval A.q z := by
    rw [A.tmmTransfer_phi_eq_numerator h,A.numerator_eval]
  have hφ0 : eval (A.phi 0) z= -(z-1)^2*eval A.q z := by
    simp only [phi,C_0,zero_mul,zero_sub,eval_neg]
    change -eval A.method.recurrencePolynomial z=_
    rw [A.factor,eval_mul,eval_pow,eval_sub,eval_X,eval_C,Complex.ofReal_one]
    ring
  have hS : A.symbol ω=((z-1)^3*(eval A.q z*star (eval (A.phi 1) z))).re := by
    change ((1-z)*eval (A.phi 0) z*star (eval (A.phi 1) z)).re=_
    rw [hφ0]
    congr 1
    ring
  have hT : (-z*(z+1)*(eval A.q z*star (eval (A.phi 1) z))).im=0 := by
    rw [←mul_assoc,←hφ]
    simp only [Complex.star_def,Complex.mul_conj,Complex.ofReal_im]
  have hh := weighted_product_identity hz (eval A.q z*star (eval (A.phi 1) z))
  rw [←hS,hT,mul_zero] at hh
  by_cases hx : 1+z.re=0
  · have hre : z.re= -1 := by linarith
    have him : z.im=0 := by simp only [Complex.normSq_apply,hre] at hz;nlinarith
    have he : z= -1 := Complex.ext (by simp [hre]) (by simp [him])
    rw [hS,hφ,he]
    simp
  · exact (mul_eq_zero.mp hh).resolve_left hx

end DoubleRootData
end
end nesterov.Trace
