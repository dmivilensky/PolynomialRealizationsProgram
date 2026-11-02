import jacobi.RootMass.Polynomials
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
Article: jacobi, Appendix D.5 (exact positivity certificate and strict constraint monotonicity).
The two printed matrices are checked as actual real positive definite
matrices by exact rational LDL square decompositions. Their polynomial
identity proves positivity on the full unbounded half-line, without
sampling or trusting an external numerical certificate.
Source: Sylvester/LDL positivity and the explicit certificate printed in the supplement.
Use: its strictly positive quadratic form certifies the constant part of the sharp endpoint polynomial.
-/
namespace jacobi.RootMass
noncomputable section
open Matrix Real
set_option backward.isDefEq.respectTransparency false

/-- The supplement's literal four-by-four rational positivity matrix.
Use: its strictly positive quadratic form certifies the constant part of the sharp endpoint polynomial.
Article: jacobi, Appendix D.5 (exact positivity certificate and strict constraint monotonicity).
-/
def S0 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![72,81,4,-114;81,624,-14,-538;4,-14,116,-89;-114,-538,-89,600]

/-- The supplement's literal three-by-three rational positivity matrix.
Use: its nonnegative quadratic form certifies the t-weighted part of the endpoint polynomial.
Article: jacobi, Appendix D.5 (exact positivity certificate and strict constraint monotonicity).
-/
def S1 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![198,-10,-144;-10,336,-286;-144,-286,378]

/-- The exact rational LDL decomposition of the first printed matrix's quadratic form.
Use: proves actual positive definiteness of S_0 without an assumed determinant or eigenvalue certificate.
Article: jacobi, Appendix D.5 (exact positivity certificate and strict constraint monotonicity).
Proof: expand the literal matrix and compare the coefficients of the rational sum of four squares. -/
theorem S0_squares (x : Fin 4 → ℝ) : star x ⬝ᵥ (S0 *ᵥ x)=
    72*(x 0+(9/8:ℝ)*x 1+(1/18:ℝ)*x 2-(19/12:ℝ)*x 3)^2+
    (4263/8:ℝ)*(x 1-(148/4263:ℝ)*x 2-(3278/4263:ℝ)*x 3)^2+
    (1472468/12789:ℝ)*(x 2-(1239153/1472468:ℝ)*x 3)^2+
    (101099401/4417404:ℝ)*(x 3)^2 := by
  simp [dotProduct,mulVec,S0,Fin.sum_univ_succ]
  ring

/-- The exact rational LDL decomposition of the second printed matrix's quadratic form.
Use: proves actual positive definiteness of S_1 by a genuine three-square identity.
Article: jacobi, Appendix D.5 (exact positivity certificate and strict constraint monotonicity).
Proof: expand the literal matrix and compare rational polynomial coefficients. -/
theorem S1_squares (x : Fin 3 → ℝ) : star x ⬝ᵥ (S1 *ᵥ x)=
    198*(x 0-(5/99:ℝ)*x 1-(8/11:ℝ)*x 2)^2+
    (33214/99:ℝ)*(x 1-(14517/16607:ℝ)*x 2)^2+
    (280800/16607:ℝ)*(x 2)^2 := by
  simp [dotProduct,mulVec,S1,Fin.sum_univ_succ]
  ring

/-- The first printed rational matrix is positive definite in Lean's actual matrix sense.
Use: proves strict positivity of the sharp endpoint polynomial at every t>=0.
Article: jacobi, Appendix D.5 (exact positivity certificate and strict constraint monotonicity).
Proof: the exact LDL decomposition has positive diagonal weights. Inspect
the last nonzero coordinate; its corresponding square is strictly positive. -/
theorem S0_posDef : S0.PosDef := by
  -- A finite triangular elimination proves positivity for every nonzero vector.
  apply PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [S0]
  · intro x hx
    rw [S0_squares]
    by_cases h3 : x 3=0
    · rw [h3]
      simp only [mul_zero,sub_zero,add_zero,zero_pow (by decide : 2≠0)]
      by_cases h2 : x 2=0
      · rw [h2]
        simp only [mul_zero,sub_zero,add_zero,zero_pow (by decide : 2≠0)]
        by_cases h1 : x 1=0
        · rw [h1]
          simp only [mul_zero,add_zero,zero_pow (by decide : 2≠0)]
          have h0 : x 0≠0 := by intro hz; apply hx; ext i; fin_cases i <;> simp [hz,h1,h2,h3]
          positivity
        · positivity
      · positivity
    · positivity

/-- The second printed rational matrix is positive definite in Lean's actual matrix sense.
Use: the t-weighted term in the polynomial certificate is nonnegative on the whole half-line.
Article: jacobi, Appendix D.5 (exact positivity certificate and strict constraint monotonicity).
Proof: its exact triangular three-square decomposition has strictly positive
weights, and the last nonzero vector coordinate gives a positive term. -/
theorem S1_posDef : S1.PosDef := by
  -- The argument covers all real vectors, not only polynomial moment vectors.
  apply PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [S1]
  · intro x hx
    rw [S1_squares]
    by_cases h2 : x 2=0
    · rw [h2]
      simp only [mul_zero,sub_zero,add_zero,zero_pow (by decide : 2≠0)]
      by_cases h1 : x 1=0
      · rw [h1]
        simp only [mul_zero,sub_zero,add_zero,zero_pow (by decide : 2≠0)]
        have h0 : x 0≠0 := by intro hz; apply hx; ext i; fin_cases i <;> simp [hz,h1,h2]
        positivity
      · positivity
    · positivity

/-- The exact degree-six polynomial at the sharp permitted parameter.
Use: certifies monotonicity of the root-mass constraint throughout eta>=-34/5.
Article: jacobi, Appendix D.5 (exact positivity certificate and strict constraint monotonicity).
-/
def PiSharp (t : ℝ) : ℝ := 300*t^6+100*t^5-766*t^4-104*t^3+306*t^2+180*t+36

/-- The literal two-matrix certificate is an exact identity of real polynomials.
Use: transfers the proved matrix positivity to the unbounded scalar profile domain.
Article: jacobi, Appendix D.5 (exact positivity certificate and strict constraint monotonicity).
Proof: expand the printed moment vectors and matrices and compare coefficients. -/
theorem certificate_identity (t : ℝ) :
    2*PiSharp t=star (![1,t,t^2,t^3] : Fin 4 → ℝ) ⬝ᵥ (S0 *ᵥ ![1,t,t^2,t^3])+
      t*(star (![1,t,t^2] : Fin 3 → ℝ) ⬝ᵥ (S1 *ᵥ ![1,t,t^2])) := by
  simp [PiSharp,S0,S1,dotProduct,mulVec,Fin.sum_univ_succ]
  ring

/-- The sharp endpoint polynomial is strictly positive at every nonnegative real argument.
Use: discharges the supplement's global polynomial positivity premise in Q'>0.
Article: jacobi, Appendix D.5 (exact positivity certificate and strict constraint monotonicity).
Proof: the first moment vector has nonzero constant coordinate. Its actual
S_0 quadratic form is strictly positive, while the second term is nonnegative. -/
theorem PiSharp_pos {t : ℝ} (ht : 0≤t) : 0<PiSharp t := by
  have hz : (![1,t,t^2,t^3] : Fin 4 → ℝ)≠0 := by intro hh; have hh0 := congrFun hh 0; norm_num at hh0
  have hw : (![1,t,t^2] : Fin 3 → ℝ)≠0 := by intro hh; have hh0 := congrFun hh 0; norm_num at hh0
  have h0 := S0_posDef.dotProduct_mulVec_pos hz
  have h1 := mul_nonneg ht (S1_posDef.dotProduct_mulVec_pos hw).le
  have hid := certificate_identity t
  linarith

end
end jacobi.RootMass
