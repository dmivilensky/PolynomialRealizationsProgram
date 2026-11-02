import krylov.Convergence.SS1FScalar
import krylov.Convergence.SecantCubicSource
import krylov.Convergence.SS1FModel

/-!
Article: main_krylov, thm:ss1F, sharp scalar cancellation.
Use: compare the actual one-pair value model directly with the current
Hessian before comparing it with radial curvature. This avoids adding the
two separate T3-linear errors. Source: actual one-dimensional matrix action,
the original (S), and the sharp anchored endpoint trapezoid kernel.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Functions krylov.Secant krylov.Methods krylov.Reference chebyshev1.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
local notation "E" => EuclideanSpace ℝ (Fin 1)

/-- The true spectral norm of a one-dimensional matrix is its sole entry. -/
theorem scalar_matrix_norm (M : Matrix (Fin 1) (Fin 1) ℝ) : ‖M‖=|M 0 0| := by
  have he : M=(M 0 0) • 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  calc
    ‖M‖ = ‖(M 0 0) • (1:Matrix (Fin 1) (Fin 1) ℝ)‖ := congrArg norm he
    _ = |M 0 0| := by rw [norm_smul,norm_one,mul_one,Real.norm_eq_abs]

/-- The Euclidean one-dimensional norm is the absolute coordinate. -/
theorem scalar_euclidean_norm (v : E) : ‖v‖=|v 0| := by
  have he : v=(v 0) • EuclideanSpace.single 0 1 := by
    ext i
    rw [Subsingleton.elim i (0:Fin 1)]
    simp only [PiLp.smul_apply,PiLp.single_apply,ite_true,smul_eq_mul,mul_one]
  calc
    ‖v‖ = ‖(v 0) • EuclideanSpace.single (0:Fin 1) (1:ℝ)‖ := congrArg norm he
    _ = |v 0| := by rw [norm_smul,PiLp.norm_single,norm_one,mul_one,Real.norm_eq_abs]

/-- A genuine one-pair unit frame and its actual inverse both have norm one. -/
theorem scalar_unit_window_inverse_norm (s : Fin 1 → E) (hs : s 0≠0) :
    ‖(windowMatrix (unitWindow s))⁻¹‖=1 := by
  have hu : |windowMatrix (unitWindow s) 0 0|=1 := by
    change |unitWindow s 0 0|=1
    rw [←scalar_euclidean_norm]
    exact unitWindow_norm s (by intro i; fin_cases i; exact hs) 0
  rw [scalar_matrix_norm,Matrix.inv_subsingleton,diagonal_apply_eq,Ring.inverse_eq_inv,abs_inv,hu,inv_one]

/-- In one dimension, conjugation by the real normalized step leaves every
actual scalar model unchanged, including its totalized inverse convention. -/
theorem scalar_unit_inverseCongruence (s : Fin 1 → E) (hs : s 0≠0)
    (M : Matrix (Fin 1) (Fin 1) ℝ) :
    inverseCongruence (windowMatrix (unitWindow s)) M=M := by
  let V := windowMatrix (unitWindow s)
  have hn : ‖V⁻¹‖=1 := scalar_unit_window_inverse_norm s hs
  rw [scalar_matrix_norm] at hn
  have hsq : (V⁻¹ 0 0)^2=1 := by nlinarith only [sq_abs (V⁻¹ 0 0),hn]
  have ht : Vᵀ=V := by ext i j; fin_cases i; fin_cases j; rfl
  ext i j
  fin_cases i
  fin_cases j
  change (Vᵀ⁻¹*M*V⁻¹) 0 0=M 0 0
  rw [ht]
  simp only [Matrix.mul_apply,Fin.sum_univ_one]
  calc
    _ = (V⁻¹ 0 0)^2*M 0 0 := by ring
    _ = _ := by rw [hsq,one_mul]

/-- A genuine bilinear Hessian on the scalar Euclidean space has exactly
its scalar matrix entry times the squared physical step norm. -/
theorem scalar_hessian_pair (A : E →L[ℝ] E) (s : E) :
    inner ℝ (A s) s=secantMatrix A 0 0*‖s‖^2 := by
  have he := congrArg (fun F : E →L[ℝ] E=>(F s) 0) (secantMatrix_operator A)
  change (secantMatrix A*ᵥWithLp.ofLp s) 0=(A s) 0 at he
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_one] at he
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Fin.sum_univ_one]
  rw [←he,scalar_euclidean_norm,sq_abs]
  ring

/-- The actually computed scalar value model differs from the genuine
current Hessian by at most L3*|s|²/12, with no T3 term. -/
theorem scalar_ss1F_model_current_bound
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (T : E → SymmetricCubic E)
    (S : Set E) (hS : Convex ℝ S)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (L : ℝ≥0) (hLip : ∀ z∈S,∀ w∈S,∀ h:E,‖h‖=1 →
      |(T z).form h h h-(T w).form h h h|≤(L:ℝ)*‖z-w‖)
    (a s : Fin 1 → E) (l : Fin 1 → ℝ) (hs : s 0≠0)
    (ha : a 0∈S) (hb : a 0+s 0∈S) (hhalf : l 0=1/2) :
    ‖inverseCongruence (windowMatrix (unitWindow s)) (ss1FNormalizedModel f G a s l)-
      secantMatrix (H (a 0+s 0))‖≤(L:ℝ)/12*‖s 0‖^2 := by
  rw [scalar_unit_inverseCongruence s hs,scalar_matrix_norm,Matrix.sub_apply,
    ss1FNormalizedModel_diagonal,hhalf]
  have hc := ss1F_corrected_diagonal_bound f (gradientDifferential G) (gradientHessian H) T S hS hf
    (fun z hz=>gradientDifferential_hasFDerivAt G H z (hG z hz)) hT L hLip
    (a 0) (s 0) (a 0+s 0) ha hb hb (1/2) 0 ‖canonicalVariation (T (a 0+s 0))‖ (norm_nonneg (canonicalVariation (T (a 0+s 0))))
    (canonicalVariation_unit_diagonal_bound (T (a 0+s 0)))
    (by simp only [splitRemainder_endpoint,sub_self,sub_self,zero_smul,norm_zero,mul_zero,le_refl])
  simp only [sub_self,norm_zero,mul_zero,zero_add,add_zero] at hc
  change |correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) (a 0) (s 0) (1/2)-
    inner ℝ (H (a 0+s 0) (s 0)) (s 0)|≤_ at hc
  rw [scalar_hessian_pair] at hc
  have hn : ‖s 0‖≠0 := norm_ne_zero_iff.mpr hs
  have he : ‖s 0‖⁻¹*correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) (a 0) (s 0) (1/2)*‖s 0‖⁻¹-
      secantMatrix (H (a 0+s 0)) 0 0=
      ‖s 0‖⁻¹*(correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) (a 0) (s 0) (1/2)-
        secantMatrix (H (a 0+s 0)) 0 0*‖s 0‖^2)*‖s 0‖⁻¹ := by field_simp
  rw [he,abs_mul,abs_mul,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc
    (inv_nonneg.mpr (norm_nonneg _))) (inv_nonneg.mpr (norm_nonneg _))).trans_eq
  field_simp
  ring

/-- Direct scalar model/radial-curvature comparison retains the exact
T3/2 coefficient by canceling their common current-Hessian term first. -/
theorem scalar_ss1F_model_radial_bound
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (T : E → SymmetricCubic E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (L : ℝ≥0) (hLip : ∀ z∈S,∀ w∈S,∀ h:E,‖h‖=1 →
      |(T z).form h h h-(T w).form h h h|≤(L:ℝ)*‖z-w‖)
    {B : ℝ} (hB : 0≤B) (hbudget : ∀ h:E,‖h‖=1 → |(T 0).form h h h|≤B)
    (a s : Fin 1 → E) (l : Fin 1 → ℝ) (hs : s 0≠0)
    (ha : a 0∈S) (hb : a 0+s 0∈S) (hhalf : l 0=1/2) :
    ‖inverseCongruence (windowMatrix (unitWindow s)) (ss1FNormalizedModel f G a s l)-
      secantMatrix (averagedDerivative H 0 (a 0+s 0))‖≤
      (L:ℝ)/12*‖s 0‖^2+B/2*‖a 0+s 0‖+2*(L:ℝ)*‖a 0+s 0‖^2 := by
  let J := inverseCongruence (windowMatrix (unitWindow s)) (ss1FNormalizedModel f G a s l)
  let Hc := secantMatrix (H (a 0+s 0))
  let A := secantMatrix (averagedDerivative H 0 (a 0+s 0))
  have hcurrent := scalar_ss1F_model_current_bound f G H T S hS hf hG hT L hLip a s l hs ha hb hhalf
  have hrad := hessian_minus_radial_cubic_bound H T S hS h₀ hT L hLip hB hbudget (a 0+s 0) hb
  have hscalar : ‖Hc-A‖=‖H (a 0+s 0)-averagedDerivative H 0 (a 0+s 0)‖ := by
    have he : Hc-A=secantMatrix (H (a 0+s 0)-averagedDerivative H 0 (a 0+s 0)) := by
      simp only [Hc,A,secantMatrix,map_sub]
    rw [he,secantMatrix_norm]
  have he : J-A=(J-Hc)+(Hc-A) := by abel
  change ‖J-A‖≤_
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hcurrent (hscalar.le.trans hrad)).trans_eq (by ring))

end
end krylov.Convergence
