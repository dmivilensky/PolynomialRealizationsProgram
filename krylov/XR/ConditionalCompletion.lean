import krylov.XR.CanonicalBounds
import krylov.XR.ConditionalRadiusAlgebra

/-!
Article: main_krylov, prop:cond, actual two-dimensional completion fibre.
Use: the conditional scalar interval is equivalent to the true spectral
budget of the original symmetric matrix, not an assumed feasible interval.
Source: the earlier spectral-ball/Loewner theorem and completing the two
Schur squares, with the actual real operator norm throughout.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator

/-- The actual compressed old increment of a two-pair conjugate window.
Article: main_krylov, prop:cond. -/
def conditionalMatrix (y δ k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![y,δ;δ,k]

/-- The actual compressed old increment is symmetric. Article: prop:cond. -/
theorem conditionalMatrix_isSymm (y δ k : ℝ) : (conditionalMatrix y δ k).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conditionalMatrix]

/-- The original two-dimensional matrix has precisely the scalar Schur
quadratic form used in the source proof. Article: main_krylov, prop:cond. -/
theorem conditionalMatrix_form (y δ k : ℝ) (w : Fin 2 → ℝ) :
    w ⬝ᵥ (conditionalMatrix y δ k*ᵥ w)=y*w 0^2+2*δ*w 0*w 1+k*w 1^2 := by
  simp only [dotProduct,mulVec,Fin.sum_univ_two,conditionalMatrix]
  simp
  ring

/-- Both shifted physical forms have the original Schur coefficients.
Article: main_krylov, prop:cond. -/
theorem conditionalMatrix_shift_forms (y δ k ω : ℝ) (w : Fin 2 → ℝ) :
    w ⬝ᵥ ((ω • 1-conditionalMatrix y δ k)*ᵥ w)=
      (ω-y)*w 0^2-2*δ*w 0*w 1+(ω-k)*w 1^2 ∧
    w ⬝ᵥ ((ω • 1+conditionalMatrix y δ k)*ᵥ w)=
      (ω+y)*w 0^2+2*δ*w 0*w 1+(ω+k)*w 1^2 := by
  simp only [sub_mulVec,add_mulVec,smul_mulVec,one_mulVec,dotProduct_sub,dotProduct_add,
    dotProduct_smul,smul_eq_mul,conditionalMatrix_form]
  simp only [dotProduct,Fin.sum_univ_two]
  constructor <;> ring

/-- Elementary Schur completion of a true scalar quadratic form.
Article: main_krylov, prop:cond. -/
theorem schur_square_identity (a b c x z : ℝ) (hc : c≠0) :
    a*x^2+2*b*x*z+c*z^2=c*(z+b/c*x)^2+(a-b^2/c)*x^2 := by
  field_simp
  ring

/-- The full genuine spectral completion fibre is exactly the printed
closed scalar interval whenever its observed pivot is interior.
Article: main_krylov, prop:cond(a), Davis--Kahan--Weinberger fibre. -/
theorem conditionalMatrix_norm_iff (y δ k ω : ℝ) (hk : |k|<ω) :
    ‖conditionalMatrix y δ k‖≤ω ↔
      -ω+δ^2/(ω+k)≤y ∧ y≤ω-δ^2/(ω-k) := by
  have hω : 0<ω := (abs_nonneg k).trans_lt hk
  have hp : 0<ω+k := by linarith [(abs_lt.mp hk).1]
  have hm : 0<ω-k := by linarith [(abs_lt.mp hk).2]
  have hs := Matrix.isHermitian_iff_isSymm.mpr (conditionalMatrix_isSymm y δ k)
  have hplus : (ω • (1 : Matrix (Fin 2) (Fin 2) ℝ)+conditionalMatrix y δ k).IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    simp only [IsSymm,transpose_add,transpose_smul,transpose_one,(conditionalMatrix_isSymm y δ k).eq]
  have hminus : (ω • (1 : Matrix (Fin 2) (Fin 2) ℝ)-conditionalMatrix y δ k).IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    simp only [IsSymm,transpose_sub,transpose_smul,transpose_one,(conditionalMatrix_isSymm y δ k).eq]
  change chebyshev1.opNorm (conditionalMatrix y δ k)≤ω ↔ _
  rw [spectral_norm_iff_shifted_posSemidef _ hs hω.le]
  constructor
  · rintro ⟨hlo,hhi⟩
    have hl := hlo.dotProduct_mulVec_nonneg (![1,δ/(ω-k)] : Fin 2 → ℝ)
    have hu := hhi.dotProduct_mulVec_nonneg (![1,-δ/(ω+k)] : Fin 2 → ℝ)
    rw [star_trivial,(conditionalMatrix_shift_forms y δ k ω _).1] at hl
    rw [star_trivial,(conditionalMatrix_shift_forms y δ k ω _).2] at hu
    simp only [cons_val_zero,cons_val_one,one_pow,mul_one] at hl hu
    have he₁ : (ω-y)-2*δ*(δ/(ω-k))+(ω-k)*(δ/(ω-k))^2=ω-y-δ^2/(ω-k) := by
      field_simp
      ring
    have he₂ : (ω+y)+2*δ*(-δ/(ω+k))+(ω+k)*(-δ/(ω+k))^2=ω+y-δ^2/(ω+k) := by
      field_simp
      ring
    rw [he₁] at hl
    rw [he₂] at hu
    constructor <;> linarith
  · rintro ⟨hlo,hhi⟩
    constructor
    · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hminus
      intro w
      rw [star_trivial,(conditionalMatrix_shift_forms y δ k ω w).1]
      have he := schur_square_identity (ω-y) (-δ) (ω-k) (w 0) (w 1) hm.ne'
      simp only [neg_sq] at he
      have hc : 0≤ω-y-δ^2/(ω-k) := by linarith
      have hh := add_nonneg (mul_nonneg hm.le (sq_nonneg (w 1+(-δ)/(ω-k)*w 0)))
        (mul_nonneg hc (sq_nonneg (w 0)))
      convert hh using 1
      nlinarith only [he]
    · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hplus
      intro w
      rw [star_trivial,(conditionalMatrix_shift_forms y δ k ω w).2]
      rw [schur_square_identity _ _ _ _ _ hp.ne']
      exact add_nonneg (mul_nonneg hp.le (sq_nonneg _))
        (mul_nonneg (by linarith : 0≤ω+y-δ^2/(ω+k)) (sq_nonneg _))

end
end krylov.XR
