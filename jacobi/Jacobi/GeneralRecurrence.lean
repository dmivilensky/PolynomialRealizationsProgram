import jacobi.Jacobi.GeneralLadder
import jacobi.Finite.Basic

/-!
The standard Jacobi recurrence with independent parameters.
Positive endpoint-normalized forward and backward coefficients avoid
the removable singularity in the customary first off-diagonal formula.
Use: StandardJacobi identifies the genuine finite characteristic polynomial
and the positive endpoint solution used by the Green tail factorization.
Source: the classical Jacobi degree recurrence, derived here from the ODE.
Article: jacobi, Theorem 5.4, Equation (5.10).
Article role: the classical ladder identities and the actual standard recurrence.
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial chebyshev1 chebyshev2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The forward coefficient in the endpoint-normalized recurrence.
The first row has its regular formula even when a+b equals minus one.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
def standardForward (a b : ℝ) (n : ℕ) : ℝ :=
  if n=0 then 2*(a+1)/(a+b+2) else
    2*((n:ℝ)+a+1)*((n:ℝ)+a+b+1)/
      ((2*(n:ℝ)+a+b+1)*(2*(n:ℝ)+a+b+2))

/-- The backward coefficient, zero precisely at the initial row.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
def standardBackward (a b : ℝ) (n : ℕ) : ℝ :=
  if n=0 then 0 else 2*(n:ℝ)*((n:ℝ)+b)/
    ((2*(n:ℝ)+a+b)*(2*(n:ℝ)+a+b+1))

/-- All genuine forward coefficients are strictly positive on a,b>-1.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
theorem standardForward_pos {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    0<standardForward a b n := by
  unfold standardForward
  split_ifs with hn
  · exact div_pos (by linarith) (by linarith)
  · have hn : (1:ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact div_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)) (mul_pos (by linarith) (by linarith))

/-- Every positive-degree backward coefficient is strictly positive.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
theorem standardBackward_pos {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {n : ℕ} (hn : 0<n) : 0<standardBackward a b n := by
  rw [standardBackward,ite_eq_right (Nat.ne_of_gt hn)]
  have hn : (1:ℝ)≤n := by exact_mod_cast hn
  exact div_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)) (mul_pos (by linarith) (by linarith))

/-- The zero-degree Jacobi polynomial is the literal constant one.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
theorem shiftedPolynomial_initial (a b : ℝ) : shiftedPolynomial a b 0=1 := by
  simp [shiftedPolynomial,coefficient_zero]

/-- The genuine first polynomial, with no restriction on a+b+1.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
theorem shiftedPolynomial_first {a b : ℝ} (ha : -1<a) :
    shiftedPolynomial a b 1=1-C ((a+b+2)/(a+1))*X := by
  apply equation_unique ha 1
  · exact shiftedPolynomial_residual ha 1
  · simp only [equationResidual,derivative_sub,derivative_mul,derivative_one,derivative_C,
      derivative_X,zero_mul,mul_zero,zero_add,sub_zero,zero_sub,derivative_neg,
      neg_zero,one_mul,Nat.cast_one]
    have h : (a+1)*((a+b+2)/(a+1))=a+b+2 := by field_simp [show a+1≠0 by linarith]
    have hc := congrArg (C : ℝ →+* ℝ[X]) h
    simp only [map_mul,map_add,map_one,map_ofNat] at hc
    linear_combination (norm := (simp only [map_add,map_one,map_ofNat]; ring)) -hc
  · simp [shiftedPolynomial_zero]

/-- The exact degree recurrence before division by its positive leading
coefficient. Raising and lowering at the same polynomial cancel derivatives.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
theorem general_degree_recurrence {a b : ℝ} (ha : -1<a) (n : ℕ) :
    let m : ℝ := (n:ℝ)+1
    let L := (2*m+a+b)*(m+a+1)*(m+a+b+1)
    let H := m*(m+b)*(2*m+a+b+2)
    let T := (2*m+a+b)*(2*m+a+b+1)*(2*m+a+b+2)
    C L*shiftedPolynomial a b (n+2)=
      (C (L+H)-C T*X)*shiftedPolynomial a b (n+1)-
        C H*shiftedPolynomial a b n := by
  dsimp only
  have hr := general_raise_eq (b := b) ha (n+1)
  have hl := general_lower_eq (b := b) ha n
  simp only [generalRaise,generalLower,Nat.cast_add,Nat.cast_one] at hr hl
  linear_combination (norm := (simp only [map_add,map_mul,map_one,map_ofNat]; ring))
    C (2*((n:ℝ)+1)+a+b)*hr+C (2*((n:ℝ)+1)+a+b+2)*hl

/-- The endpoint-normalized three-term identity in every degree.
Its initial row is proved separately, so no exceptional parameter sum
is excluded by cancelling a vanishing classical prefactor.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
theorem standard_polynomial_recurrence {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    C (standardForward a b n)*shiftedPolynomial a b (n+1)=
      ((1-2*X)-C (1-standardForward a b n-standardBackward a b n))*
        shiftedPolynomial a b n-
      C (standardBackward a b n)*shiftedPolynomial a b (n-1) := by
  cases n with
  | zero =>
    rw [shiftedPolynomial_first ha,shiftedPolynomial_initial]
    simp only [standardForward,standardBackward,ite_true,sub_zero,mul_one]
    have h : (2*(a+1)/(a+b+2))*((a+b+2)/(a+1))=2 := by
      field_simp [show a+1≠0 by linarith,show a+b+2≠0 by linarith]
    have hc := congrArg (C : ℝ →+* ℝ[X]) h
    simp only [map_mul,map_ofNat] at hc
    linear_combination (norm := (simp only [map_sub,map_one,map_zero]; ring)) -X*hc
  | succ n =>
    let m : ℝ := (n:ℝ)+1
    let L := (2*m+a+b)*(m+a+1)*(m+a+b+1)
    let H := m*(m+b)*(2*m+a+b+2)
    let T := (2*m+a+b)*(2*m+a+b+1)*(2*m+a+b+2)
    let t : ℝ := T/2
    have hm : 1≤m := by dsimp [m]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have h1 : 0<2*m+a+b := by linarith
    have h2 : 0<2*m+a+b+1 := by linarith
    have h3 : 0<2*m+a+b+2 := by linarith
    have ht : t≠0 := ne_of_gt (by dsimp [t,T]; positivity)
    have hv : t*standardForward a b (n+1)=L := by
      simp only [standardForward,ite_eq_right (Nat.succ_ne_zero n),Nat.cast_add,Nat.cast_one]
      change ((2*m+a+b)*(2*m+a+b+1)*(2*m+a+b+2)/2)*
        (2*(m+a+1)*(m+a+b+1)/((2*m+a+b+1)*(2*m+a+b+2)))=L
      dsimp [L]
      field_simp [h2.ne',h3.ne']
    have hw : t*standardBackward a b (n+1)=H := by
      simp only [standardBackward,ite_eq_right (Nat.succ_ne_zero n),Nat.cast_add,Nat.cast_one]
      change ((2*m+a+b)*(2*m+a+b+1)*(2*m+a+b+2)/2)*
        (2*m*(m+b)/((2*m+a+b)*(2*m+a+b+1)))=H
      dsimp [H]
      field_simp [h1.ne',h2.ne']
    have hcv : C t*C (standardForward a b (n+1))=C L := by rw [← map_mul,hv]
    have hcw : C t*C (standardBackward a b (n+1))=C H := by rw [← map_mul,hw]
    have hct : 2*C t=C T := by
      rw [← map_ofNat (C : ℝ →+* ℝ[X]) 2,← map_mul]
      congr 1
      dsimp [t]
      ring
    have hr := general_degree_recurrence (b := b) ha n
    change C L*shiftedPolynomial a b (n+2)=
      (C (L+H)-C T*X)*shiftedPolynomial a b (n+1)-C H*shiftedPolynomial a b n at hr
    have hz : C t*(C (standardForward a b (n+1))*shiftedPolynomial a b (n+2)-
        (((1-2*X)-C (1-standardForward a b (n+1)-standardBackward a b (n+1)))*
          shiftedPolynomial a b (n+1)-C (standardBackward a b (n+1))*shiftedPolynomial a b n))=0 := by
      linear_combination (norm := (simp only [map_add,map_sub,map_one]; ring))
        hr+(shiftedPolynomial a b (n+2)-shiftedPolynomial a b (n+1))*hcv+
          (shiftedPolynomial a b n-shiftedPolynomial a b (n+1))*hcw+
          X*shiftedPolynomial a b (n+1)*hct
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (C_ne_zero.mpr ht))

/-- The concrete symmetric standard coefficient encoding. Squared
off-diagonals are the product of adjacent endpoint-normalized coefficients.
Only the finite tails are truncated; all genuine rows use the same family.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
def standardChain (a b : ℝ) (ha : -1<a) (hb : -1<b) (N : ℕ) : chebyshev2.Jacobi N where
  data := {
    b := fun i => if i<N then 1-standardForward a b i-standardBackward a b i else 0
    aSq := fun i => if 0 < i ∧ i < N then standardForward a b (i-1)*standardBackward a b i else 0 }
  coupling_nonneg i := by
    change 0≤(if 0 < i ∧ i < N then standardForward a b (i-1)*standardBackward a b i else 0)
    split_ifs with hi
    · exact mul_nonneg (standardForward_pos ha hb _).le (standardBackward_pos ha hb hi.1).le
    · exact le_refl 0
  coupling_zero := by simp
  diagonal_tail i hi := by simp [not_lt.mpr hi]
  coupling_tail i hi := by simp [not_lt.mpr hi]

/-- Every actual interior off-diagonal of the standard chain is positive.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
theorem standardChain_irreducible {a b : ℝ} (ha : -1<a) (hb : -1<b) (N : ℕ) :
    (standardChain a b ha hb N).Irreducible := by
  intro i hi hiN
  change 0<(if 0 < i ∧ i < N then standardForward a b (i-1)*standardBackward a b i else 0)
  rw [ite_eq_left ⟨hi,hiN⟩]
  exact mul_pos (standardForward_pos ha hb _) (standardBackward_pos ha hb hi)

end
end jacobi.Jacobi
