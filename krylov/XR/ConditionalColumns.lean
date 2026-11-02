import krylov.XR.ConditionalCompletion

/-!
Article: main_krylov, prop:cond, physical feasibility and attaining endpoints.
Use: the actual spectral budget forces the original column constraint;
the traceless endpoint matrices attain it in genuine dimension two.
Source: real operator-norm action and the C*-norm square identity.
-/
namespace krylov.XR
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator

/-- The original true spectral budget implies the exact revealed-column
feasibility condition, including singular boundary pivots. Article: prop:cond. -/
theorem conditionalMatrix_column_feasible (y δ k ω : ℝ) (hω : 0≤ω)
    (hbudget : ‖conditionalMatrix y δ k‖≤ω) : δ^2+k^2≤ω^2 := by
  let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (![0,1] : Fin 2 → ℝ)
  have hv : ‖v‖=1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [v,Fin.sum_univ_two]
  let T := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (conditionalMatrix y δ k)
  have ha : WithLp.ofLp (T v)=(![δ,k] : Fin 2 → ℝ) := by
    ext i
    fin_cases i <;> simp [T,v,conditionalMatrix]
  have hn : ‖T v‖^2=δ^2+k^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rw [ha]
    simp [Fin.sum_univ_two]
  have hm := T.le_opNorm v
  rw [show ‖T‖=‖conditionalMatrix y δ k‖ from Matrix.l2_opNorm_toEuclideanCLM _,hv,mul_one] at hm
  have hh := hm.trans hbudget
  nlinarith [norm_nonneg (T v)]

/-- The genuine traceless endpoint has exactly the square root of its
column energy as its true Euclidean operator norm. Article: prop:cond. -/
theorem conditionalMatrix_traceless_norm (δ k : ℝ) :
    ‖conditionalMatrix (-k) δ k‖=Real.sqrt (δ^2+k^2) := by
  have hs : star (conditionalMatrix (-k) δ k)=conditionalMatrix (-k) δ k := by
    rw [star_eq_conjTranspose,conjTranspose_eq_transpose_of_trivial,
      (conditionalMatrix_isSymm _ _ _).eq]
  have he : conditionalMatrix (-k) δ k*conditionalMatrix (-k) δ k=
      (δ^2+k^2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conditionalMatrix,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
  have hn : ‖conditionalMatrix (-k) δ k‖*‖conditionalMatrix (-k) δ k‖=δ^2+k^2 := by
    rw [←CStarRing.norm_star_mul_self,hs,he,norm_smul,norm_one,mul_one,Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0≤δ^2+k^2)]
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity : 0≤δ^2+k^2)]
  simpa only [pow_two] using hn

end
end krylov.XR
