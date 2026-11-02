import krylov.Tensor.BinaryCubic

/-!
Article: main_krylov, apD:lem-binary(b).
Use: prove the sharp 1/3 product bound in the genuine diagonal-norm ball,
including the printed extremizing cubic. No mixed tensor norm is assumed.
Source: the two-point dual certificate and polynomial sum-of-squares
certificate in Appendix D of main_krylov, simplified algebraically.
-/

namespace krylov.Tensor.BinaryCubic
noncomputable section

/-- Homogeneity transports the true unit-circle bound to a circle of radius R.
Article: main_krylov, apD:lem-binary(b), projective dual certificate. -/
theorem bound_at_radius {t : BinaryCubic} (ht : t.InBall) (c s R : ℝ)
    (hR : 0<R) (hcs : c^2+s^2=R^2) : |t.eval c s|≤R^3 := by
  have hR0 : R≠0 := hR.ne'
  have hcirc : (c/R)^2+(s/R)^2=1 := by field_simp; nlinarith
  have hb := ht (c/R) (s/R) hcirc
  have he : t.eval c s=R^3*t.eval (c/R) (s/R) := by
    unfold eval
    field_simp
  rw [he,abs_mul,abs_of_pos (pow_pos hR 3)]
  nlinarith [pow_pos hR 3]

/-- The exact two-point support certificate on the zero-pure-coefficient slice.
Article: main_krylov, apD:lem-binary(b), t1+t2≤2/sqrt3.
Proof: test the genuine cubic at projective coordinates p,q; their circle
radii are (3sqrt7 ± sqrt3)/6. Their cubic radii add to 2sqrt7. -/
theorem zero_slice_sum_le {t : BinaryCubic} (ht : t.InBall) (h0 : t.t0=0) :
    Real.sqrt 3*(t.t1+t.t2)≤2 := by
  let a := Real.sqrt 7
  let b := Real.sqrt 3
  have ha : 0<a := Real.sqrt_pos.mpr (by norm_num)
  have hb : 0<b := Real.sqrt_pos.mpr (by norm_num)
  have ha2 : a^2=7 := Real.sq_sqrt (by norm_num)
  have hb2 : b^2=3 := Real.sq_sqrt (by norm_num)
  let p := (3+a*b)/6
  let q := (3-a*b)/6
  let A := (3*a+b)/6
  let B := (3*a-b)/6
  have hA : 0<A := by dsimp [A];positivity
  have hB : 0<B := by dsimp [B];nlinarith
  have hAp : p^2+1=A^2 := by
    dsimp [p,A]
    field_simp
    nlinarith [sq_nonneg (a*b),show (a*b)^2=21 by rw [mul_pow,ha2,hb2];norm_num]
  have hBq : q^2+1=B^2 := by
    dsimp [q,B]
    field_simp
    nlinarith [sq_nonneg (a*b),show (a*b)^2=21 by rw [mul_pow,ha2,hb2];norm_num]
  have hp := (abs_le.mp (bound_at_radius ht p 1 A hA (by simpa using hAp))).2
  have hq := (abs_le.mp (bound_at_radius ht q 1 B hB (by simpa using hBq))).1
  have hdiff : t.eval p 1-t.eval q 1=a*b*(t.t1+t.t2) := by
    simp only [eval,h0,zero_mul,zero_add,one_pow,mul_one]
    dsimp [p,q]
    ring
  have hsum : A^3+B^3=2*a := by
    dsimp [A,B]
    nlinarith [show a^3=7*a by nlinarith,show a*b^2=3*a by rw [hb2];ring]
  have hbound : a*(b*(t.t1+t.t2))≤a*2 := by nlinarith
  exact (mul_le_mul_iff_right₀ ha).mp hbound

/-- The support certificate controls both signs, using the actual negation symmetry.
Article: main_krylov, apD:lem-binary(b). -/
theorem zero_slice_sum_abs {t : BinaryCubic} (ht : t.InBall) (h0 : t.t0=0) :
    |Real.sqrt 3*(t.t1+t.t2)|≤2 := by
  apply abs_le.mpr
  constructor
  · have h := zero_slice_sum_le (inBall_neg ht) (by simp [neg,h0])
    dsimp only [neg] at h
    nlinarith
  · exact zero_slice_sum_le ht h0

/-- The exact global upper bound on the hidden product in the zero slice.
Article: main_krylov, apD:lem-binary(b), sup t1*t2≤1/3.
Proof: square the proved support certificate and subtract (t1-t2)^2. -/
theorem zero_slice_product_le {t : BinaryCubic} (ht : t.InBall) (h0 : t.t0=0) :
    t.t1*t.t2≤1/3 := by
  have h := zero_slice_sum_abs ht h0
  have hs : (Real.sqrt 3*(t.t1+t.t2))^2≤4 := by
    nlinarith [sq_abs (Real.sqrt 3*(t.t1+t.t2)),abs_nonneg (Real.sqrt 3*(t.t1+t.t2))]
  rw [mul_pow,Real.sq_sqrt (by norm_num)] at hs
  nlinarith [sq_nonneg (t.t1-t.t2)]

/-- The actual coefficient vector attaining the printed sharp product.
Article: main_krylov, apD:lem-binary(b). -/
def sharpCubic : BinaryCubic :=
  ⟨0,1/Real.sqrt 3,1/Real.sqrt 3,-4*Real.sqrt 3/9⟩

/-- A homogeneous sum-of-squares identity for the extremizing cubic.
Article: main_krylov, apD:lem-binary(b).
Proof: combine the two conjugate linear factors in the paper into
s²+3cs−3c². The remaining factor is manifestly positive after a square. -/
theorem sharpCubic_gap (c s : ℝ) :
    27*((c^2+s^2)^3-(sharpCubic.eval c s)^2)=
      (s^2+3*c*s-3*c^2)^2*(11*s^2+6*c*s+3*c^2) := by
  have hsq : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hinv : 1/Real.sqrt 3=Real.sqrt 3/3 := by
    apply (div_eq_iff hne).mpr
    nlinarith
  simp only [eval,sharpCubic,hinv,zero_mul,zero_add]
  ring_nf
  rw [hsq]
  ring

/-- The printed extremizer belongs to the genuine cubic unit ball.
Article: main_krylov, apD:lem-binary(b).
Proof: its exact homogeneous gap is a square times a positive quadratic. -/
theorem sharpCubic_inBall : sharpCubic.InBall := by
  intro c s hcs
  have hq : 0≤11*s^2+6*c*s+3*c^2 := by
    nlinarith [sq_nonneg (11*s+3*c),sq_nonneg c]
  have hgap := sharpCubic_gap c s
  have hp := mul_nonneg (sq_nonneg (s^2+3*c*s-3*c^2)) hq
  rw [hcs,one_pow] at hgap
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (sharpCubic.eval c s+1),sq_nonneg (sharpCubic.eval c s-1)]

/-- The genuine extremizer has the exact sharp product 1/3.
Article: main_krylov, apD:lem-binary(b). -/
theorem sharpCubic_product : sharpCubic.t1*sharpCubic.t2=1/3 := by
  have hsq : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  dsimp only [sharpCubic]
  rw [div_mul_div_comm,show Real.sqrt 3*Real.sqrt 3=3 by nlinarith]
  norm_num

end
end krylov.Tensor.BinaryCubic
