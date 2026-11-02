import jacobi.Laguerre.Polynomial
import jacobi.Counterexample.LaguerreFactor

/-!
Article: jacobi, Proposition 6.1.
The literal square-root Cholesky product is the original Laguerre
Jacobi matrix. Its complete determinant is the classical Laguerre
polynomial with its actual signed normalization.
Source: Szego, Orthogonal Polynomials; DLMF 18.5.12 and 18.9.1.
Use: matrix_eq_factor and leading_polynomial identify the full finite original characteristic polynomial, for every dimension.
-/
namespace jacobi.Laguerre
noncomputable section
open Polynomial Matrix chebyshev1 jacobi.Counterexample
set_option backward.isDefEq.respectTransparency false

/-- The original infinite Laguerre recurrence coefficients.
Use: matrix_eq_factor and leading_polynomial identify the full finite original characteristic polynomial, for every dimension.
Article: jacobi, Proposition 6.1.
Source: Szego, Orthogonal Polynomials, Laguerre recurrence. -/
def data (a:ℝ) : JacobiData where
  b i := 2*(i:ℝ)+a+1
  aSq i := (i:ℝ)*((i:ℝ)+a)

/-- Every actual squared Laguerre coupling is nonnegative in the whole source order range.
Use: characteristic_polynomial invokes the already proved original continuant determinant theorem.
Article: jacobi, Proposition 6.1.
Proof: the zeroth coupling is zero; at every positive natural index both original factors are positive. -/
theorem data_nonneg {a:ℝ} (ha:-1<a) (i:ℕ) : 0≤(data a).aSq i := by
  cases i with
  | zero => simp [data]
  | succ i =>
    change 0≤((i+1:ℕ):ℝ)*(((i+1:ℕ):ℝ)+a)
    push_cast
    have hi:0≤(i:ℝ) := Nat.cast_nonneg i
    apply mul_nonneg <;> linarith

/-- The literal Laguerre Cholesky product equals the original Laguerre recurrence matrix at every finite entry.
Use: characteristic_polynomial identifies the exact full source polynomial for the independently constructed finite optimizer.
Article: jacobi, Proposition 6.1.
Proof: the diagonal is already proved. On each neighboring diagonal,
the genuine square roots multiply to sqrt(i*(i+a)); outside the
band both actual finite matrices vanish. -/
theorem matrix_eq_factor {a:ℝ} (ha:-1<a) (N:ℕ) :
    (data a).matrix 0 N=bidiagonal (laguerreDiagonal a) laguerreLower N*
      (bidiagonal (laguerreDiagonal a) laguerreLower N)ᵀ := by
  -- The two finite boundary rows are included in the original entry formulas.
  ext i j
  by_cases hij:i=j
  · subst j
    rw [JacobiData.matrix_apply,ite_eq_left rfl,laguerre_matrix_diagonal ha]
    simp only [data,Nat.zero_add]
  rw [JacobiData.matrix_apply,bidiagonal,chebyshev2.Bidiagonal.mul_transpose_apply]
  simp only [hij,ite_false,Nat.zero_add,data]
  by_cases hu:i.val+1=j.val
  · have hc:(i:ℝ)+a+1=(j:ℝ)+a := by
      have h:(i:ℝ)+1=(j:ℝ) := by exact_mod_cast hu
      linarith
    simp only [hu,ite_true,laguerreDiagonal,laguerreLower,hc]
    rw [Real.sqrt_mul (Nat.cast_nonneg j.val)]
    ring
  · by_cases hl:j.val+1=i.val
    · have hc:(j:ℝ)+a+1=(i:ℝ)+a := by
        have h:(j:ℝ)+1=(i:ℝ) := by exact_mod_cast hl
        linarith
      simp only [hu,ite_false,hl,ite_true,laguerreDiagonal,laguerreLower,hc]
      rw [Real.sqrt_mul (Nat.cast_nonneg i.val)]
    · simp only [hu,hl,ite_false]

/-- The actual signed normalization converting the source's normalized Laguerre polynomial to a monic polynomial.
Use: leading_polynomial computes the complete actual characteristic polynomial.
Article: jacobi, Proposition 6.1.
-/
def signedNormalization (a:ℝ) (n:ℕ) : ℝ :=
  (-1:ℝ)^n*(ascPochhammer ℝ n).eval (a+1)

/-- The genuine classical Laguerre polynomial with its standard value (a+1)_n/n! at zero.
Use: characteristic_classical and the original affine counterexample polynomial retain the printed L_n^(a), rather than a monic replacement.
Article: jacobi, Proposition 6.1.
Source: DLMF 18.5.12, standard Laguerre normalization. -/
def classical (a:ℝ) (n:ℕ) : Polynomial ℝ :=
  C ((ascPochhammer ℝ n).eval (a+1)/(n.factorial:ℝ))*polynomial a n

/-- The actual Laguerre recurrence determinant is its classical normalized polynomial times the precise signed normalization.
Use: characteristic_polynomial identifies the complete original matrix polynomial, including every zero and the leading coefficient.
Article: jacobi, Proposition 6.1.
Proof: the original continuant and the classical polynomial have the
same two initial values. In the three-term recurrence the rising-factorial
normalization gains -(a+n+1), giving exactly the original squared coupling. -/
theorem leading_polynomial {a:ℝ} (ha:-1<a) (n:ℕ) :
    (data a).leading n=C (signedNormalization a n)*polynomial a n := by
  -- The original continuant recurrence from chebyshev1 supplies the determinant induction.
  induction n using Nat.twoStepInduction with
  | zero => simp [JacobiData.leading,JacobiData.block,signedNormalization,polynomial_zero]
  | one =>
    norm_num only [JacobiData.leading,JacobiData.block,data,Nat.zero_add,Nat.cast_zero,mul_zero,zero_add]
    rw [polynomial_one]
    simp only [signedNormalization,pow_one,ascPochhammer_succ_eval,ascPochhammer_zero,
      eval_one,one_mul,Nat.cast_zero,add_zero,neg_one_mul,map_neg]
    have hp:C (a+1)*C (1/(a+1))=(1:Polynomial ℝ) := by
      rw [← map_mul,mul_one_div_cancel (by linarith : a+1≠0),map_one]
    calc
      X-C (a+1)= -C (a+1)+X*1 := by ring
      _ = -C (a+1)+X*(C (a+1)*C (1/(a+1))) := by rw [hp]
      _ = _ := by ring
  | more n ih0 ih1 =>
    rw [JacobiData.leading_add_two,ih0,ih1]
    have hrec := congrArg (fun p:Polynomial ℝ=>C (-signedNormalization a (n+1))*p)
      (polynomial_recurrence ha n)
    have hscale:signedNormalization a (n+1)= -signedNormalization a n*(a+(n:ℝ)+1) := by
      simp only [signedNormalization,pow_succ,ascPochhammer_succ_eval]
      ring
    have hscale2:signedNormalization a (n+2)= -signedNormalization a (n+1)*(a+(n:ℝ)+2) := by
      simp only [signedNormalization,pow_succ,ascPochhammer_succ_eval]
      push_cast
      ring
    rw [hscale2]
    simp only [data,Nat.cast_add,Nat.cast_one] at *
    rw [hscale] at hrec ⊢
    rw [show 2*((n:ℝ)+1)+a+1=2*n+a+3 by ring,
      show (n:ℝ)+1+a=a+n+1 by ring]
    rw [show (n:ℝ)+a+2=a+n+2 by ring] at hrec
    simp only [map_mul,map_neg] at hrec ⊢
    linear_combination -hrec

/-- The original positive Laguerre Cholesky matrix has exactly the complete normalized Laguerre characteristic polynomial.
Use: the actual affine attaining fibre in Proposition 6.1 has the source's original polynomial, not merely the same limiting spectrum.
Article: jacobi, Proposition 6.1.
Proof: identify the literal factor matrix with its original Jacobi
recurrence matrix, reuse the determinant theorem from chebyshev1, and insert
the proved classical recurrence normalization. -/
theorem characteristic_polynomial {a:ℝ} (ha:-1<a) (N:ℕ) :
    (bidiagonal (laguerreDiagonal a) laguerreLower N*
      (bidiagonal (laguerreDiagonal a) laguerreLower N)ᵀ).charpoly=
        C (signedNormalization a N)*polynomial a N := by
  rw [← matrix_eq_factor ha,← JacobiData.block_eq_charpoly _ (data_nonneg ha)]
  exact leading_polynomial ha N

/-- The genuine Laguerre matrix determinant equals (-1)^n*n!*L_n^(a) in the exact classical normalization.
Use: the affine characteristic identity gives the printed n!/H_n^n*L_n^(1/2)(H_n*(1-x)) counterexample polynomial.
Article: jacobi, Proposition 6.1.
Proof: the genuine nonzero natural factorial cancels in the standard
normalization. The remaining signed rising factorial is exactly the
already proved monic determinant normalization. -/
theorem characteristic_classical {a:ℝ} (ha:-1<a) (N:ℕ) :
    (bidiagonal (laguerreDiagonal a) laguerreLower N*
      (bidiagonal (laguerreDiagonal a) laguerreLower N)ᵀ).charpoly=
        C ((-1:ℝ)^N*(N.factorial:ℝ))*classical a N := by
  rw [characteristic_polynomial ha,classical,← mul_assoc,← map_mul]
  congr 2
  unfold signedNormalization
  field_simp

end
end jacobi.Laguerre
