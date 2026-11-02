import krylov.XR.CanonicalBounds

/-!
Article: main_krylov, apH:canon, exact two-pair amplification.
Use: identify the actual relative defect in dimension two, including its
determinant denominator and the resulting dependence on near dependence.
Source: X^T J X=det(X)J and the genuine positive-root determinant identity.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant
open scoped Matrix.Norms.L2Operator

/-- The unique real two-dimensional skew form with the given upper
off-diagonal entry. Article: main_krylov, apH:canon. -/
def skewTwo (δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0,δ;-δ,0]

/-- Every actual two-pair skew defect is this literal skew form.
Article: main_krylov, apH:canon. -/
theorem skewTwo_eq (D : Matrix (Fin 2) (Fin 2) ℝ) (hD : Dᵀ= -D) :
    D=skewTwo (D 0 1) := by
  have h₀ := congrFun (congrFun hD 0) 0
  have h₁ := congrFun (congrFun hD 1) 1
  have h₂ := congrFun (congrFun hD 0) 1
  change D 0 0= -D 0 0 at h₀
  change D 1 1= -D 1 1 at h₁
  change D 1 0= -D 0 1 at h₂
  have hd₀ : D 0 0=0 := by linarith
  have hd₁ : D 1 1=0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewTwo,hd₀,hd₁,h₂]

/-- The exact genuine Euclidean operator norm of the two-dimensional
skew form. Article: main_krylov, apH:canon. -/
theorem skewTwo_norm (δ : ℝ) : ‖skewTwo δ‖=|δ| := by
  have he : star (skewTwo δ)*skewTwo δ=δ^2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [skewTwo,Matrix.mul_apply,Fin.sum_univ_two,pow_two]
  have hn := congrArg norm he
  rw [CStarRing.norm_star_mul_self,norm_smul,norm_one,mul_one,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg δ)] at hn
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg δ)).mp
  rw [sq_abs]
  simpa only [pow_two] using hn

/-- Arbitrary true two-dimensional congruence scales the skew form by
exactly its determinant. Article: main_krylov, apH:canon. -/
theorem skewTwo_congruence (X : Matrix (Fin 2) (Fin 2) ℝ) (δ : ℝ) :
    Xᵀ*skewTwo δ*X=skewTwo (X.det*δ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,skewTwo,Matrix.det_fin_two] <;> ring

/-- The actual two-dimensional relative skew norm has exactly the
printed positive determinant denominator. Article: apH:canon. -/
theorem relativeBudget_two (T D : Matrix (Fin 2) (Fin 2) ℝ) (hT : T.PosDef)
    (hD : Dᵀ= -D) : relativeBudget T D=|D 0 1|/Real.sqrt T.det := by
  have hs : ((metricRoot T)⁻¹)ᵀ=(metricRoot T)⁻¹ := by
    rw [transpose_nonsing_inv,(metricRoot_isSymm T).eq]
  have hd : (metricRoot T).det^2=T.det := by
    have hh := congrArg Matrix.det (metricRoot_square T hT)
    simpa only [det_mul,pow_two] using hh
  have ha : |(metricRoot T).det|=Real.sqrt T.det := by
    rw [←hd,Real.sqrt_sq_eq_abs]
  change ‖(metricRoot T)⁻¹*D*(metricRoot T)⁻¹‖=_
  have he : (metricRoot T)⁻¹*D*(metricRoot T)⁻¹=
      skewTwo (((metricRoot T)⁻¹).det*D 0 1) := by
    calc
      _ = ((metricRoot T)⁻¹)ᵀ*skewTwo (D 0 1)*(metricRoot T)⁻¹ := by rw [hs,←skewTwo_eq D hD]
      _ = _ := skewTwo_congruence _ _
  rw [he,skewTwo_norm,abs_mul,det_nonsing_inv,Ring.inverse_eq_inv,abs_inv,ha]
  ring

/-- The literal observed two-pair window has exactly the canonical
defect formula of the article. Article: main_krylov, apH:canon. -/
theorem canonical_two_pair_formula (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : (latest M).PosDef) :
    relativeBudget (latest M) (defect M)=
      |canonicalDefect M 0 1|/Real.sqrt (canonicalModel M).det := by
  rw [←canonical_relativeBudget M hM]
  apply relativeBudget_two _ _ (canonicalModel_posDef M hM)
  rw [canonicalDefect_congruence M hM]
  simp only [transpose_mul,pairNormalizer,diagonal_transpose,defect_transpose,
    Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_assoc]

end
end krylov.XR
