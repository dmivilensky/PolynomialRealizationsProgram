import krylov.Reference.EnergyMinimum

/-!
Article: main_krylov, prop:dict(i), genuine normalized CG/Galerkin uniqueness.
Use: identify an actual constructed normalized polynomial with the real
computed CG residual from true orthogonality, rather than supplied recurrence data.
Source: classical positive quadratic Galerkin uniqueness (Hestenes--Stiefel,
Meurant, Golub--Meurant); reuse the proved normalized polynomial difference.
-/

namespace krylov.Reference.CG
noncomputable section
open Polynomial
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Any actual normalized degree-k polynomial whose true operator action is orthogonal to the genuine old Krylov space has exactly the real computed CG gradient action.
Use: the raw tridiagonal determinant dictionary can identify its actual spectral-measure CG run without assuming the desired coefficients.
Article: main_krylov, prop:dict(i).
Proof: divide the true normalized difference by X. Its real low-degree
operator action lies in the old Krylov space; both genuine residuals are
orthogonal to it. Positive actual operator energy forces that difference
action to vanish, proving the actual CG identity.
-/
theorem normalized_galerkin_unique (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hpre : ∀ i<k, gradient Q g i≠0) (p : ℝ[X]) (hp : p.natDegree≤k) (h0 : p.eval 0=1)
    (horth : ∀ v∈krylovSpace Q g k, inner ℝ v (polynomialAction Q g p)=0) :
    polynomialAction Q g p=gradient Q g k := by
  -- The normalized difference has one fewer true polynomial degree, so its actual action is in the old Krylov space.
  obtain ⟨q,hq,hd⟩ := krylov.Reference.normalized_difference hp (polynomial_degree Q g k).1
    (h0.trans (residualPolynomial_zero Q g k).symm)
  let v := polynomialAction Q g q
  have hv : v∈krylovSpace Q g k := ⟨q,hd,rfl⟩
  have hx : polynomialAction Q g (X*q)=Q v := by
    change aeval Q (X*q) g=Q (aeval Q q g)
    rw [map_mul,aeval_X,mul_apply_eq_comp]
  have he : Q v=polynomialAction Q g p-gradient Q g k := by
    rw [← hx,← hq,map_sub,(polynomialAction_pair Q g k).1]
  have hi : inner ℝ v (Q v)=0 := by
    rw [he,inner_sub_right,horth v hv,gradient_orthogonal_krylov Q hQ hpos g k hpre hv,sub_self]
  have hz : v=0 := by
    by_contra hn
    exact (hpos v hn).ne' hi
  have hdiff : polynomialAction Q g p-gradient Q g k=0 := he.symm.trans (by rw [hz,map_zero])
  exact sub_eq_zero.mp hdiff
end
end krylov.Reference.CG
