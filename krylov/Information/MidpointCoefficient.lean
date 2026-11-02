import krylov.Information.BudgetMidpoint
import krylov.Correction.InformedScalar

/-!
Article: main_krylov, thm:C2(c), the genuine informed leading coefficient.
Use: the actual observed-data midpoint has sharp coefficient 2/(3√3),
with a quantified geometric loss from the true moving normal direction.
Source: boundary-inclusive consistency midpoint bounds, symmetric operator
cross-action geometry and the proved sharp scalar cubic tradeoff.
-/

namespace krylov.Information
noncomputable section
open Matrix Set Finset krylov.Reference krylov.Secant krylov.Envelope krylov.LinearAlgebra krylov.Correction
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual normalized cross entry is bounded by the observed cross-vector norm plus twice the true normal-direction displacement.
Use: transfer the source's hidden-entry midpoint width to the original reference first/last CG coordinates.
Article: main_krylov, thm:C2(c), |eᵀRf|≤‖x‖+2‖v−e‖.
Proof: split the original old direction into the moving normal and its
small difference. Symmetry transfers the normal's pairing onto its actual
image, whose perpendicular part is the observed cross vector. Its parallel
part costs at most the normal displacement because the original first and
last reference directions are exactly orthogonal.
-/
theorem midpoint_cross_entry_bound (v e f : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖=1) (hf : ‖f‖=1) (hef : inner ℝ e f=0)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm) (hRn : ‖R‖≤1) :
    let x := cgOperator R v-(inner ℝ v (cgOperator R v)) • v
    |inner ℝ e (cgOperator R f)|≤‖x‖+2*‖v-e‖ := by
  -- The actual spectral norm controls both the raw image and its original reference pairing.
  let T := cgOperator R
  let x := T v-(inner ℝ v (T v)) • v
  have hnorm : ‖T‖≤1 := by simpa only [T,cgOperator,Matrix.l2_opNorm_toEuclideanCLM] using hRn
  have himage : ‖T f‖≤1 := by
    have ht := T.le_opNorm f
    rw [hf,mul_one] at ht
    exact ht.trans hnorm
  have hsym : ∀ a b, inner ℝ (T a) b=inner ℝ a (T b) :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hR)
  have hdiag : |inner ℝ v (T v)|≤1 := by
    simpa only [hv,one_pow] using contraction_quadratic_bound T hnorm v
  have hd : |inner ℝ v f|≤‖v-e‖ := by
    have heq : inner ℝ v f=inner ℝ (v-e) f := by rw [inner_sub_left,hef,sub_zero]
    rw [heq]
    simpa only [hf,mul_one] using abs_real_inner_le_norm (v-e) f
  have he : |inner ℝ (e-v) (T f)|≤‖v-e‖ := by
    have hh := (abs_real_inner_le_norm (e-v) (T f)).trans
      (mul_le_mul_of_nonneg_left himage (norm_nonneg _))
    simpa only [mul_one,norm_sub_rev] using hh
  have hx : |inner ℝ x f|≤‖x‖ := by simpa only [hf,mul_one] using abs_real_inner_le_norm x f
  have hentry : inner ℝ e (T f)=inner ℝ (e-v) (T f)+inner ℝ x f+
      inner ℝ v (T v)*inner ℝ v f := by
    simp only [x,inner_sub_left,real_inner_smul_left]
    rw [hsym]
    ring
  have hparallel : |inner ℝ v (T v)*inner ℝ v f|≤‖v-e‖ := by
    rw [abs_mul]
    exact (mul_le_mul hdiag hd (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  change |inner ℝ e (T f)|≤‖x‖+2*‖v-e‖
  rw [hentry]
  exact ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add he hx)) hparallel)).trans_eq (by ring)

/-- The genuine observed-data unit-budget midpoint has the sharp informed source leading coefficient with only an explicit moving-normal displacement loss.
Use: the actual algorithm's scalar correction is controlled on all original unit spectral scenarios, including singular endpoint completions.
Article: main_krylov, thm:C2(c), |q−q̂||x_f|≤2/(3√3)+2‖v−ŝ₀‖.
Proof: the actual midpoint error is at most 1−t², where t is the true
observed cross-vector norm. Its nonnegativity derives t≤1. The proved
reference cross-entry estimate costs t+2‖v−e‖. Multiply the two genuine
bounds, apply the sharp cubic maximum t(1−t²), and retain the explicit
normal-direction displacement needed by the actual cubic remainder.
-/
theorem completionMidpoint_coefficient_bound (v e f : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖=1) (he : ‖e‖=1) (hf : ‖f‖=1) (hef : inner ℝ e f=0)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm) (hRn : ‖R‖≤1) :
    |completionQuadratic e R-completionMidpoint v e R| * |inner ℝ e (cgOperator R f)|≤
      2/(3*Real.sqrt 3)+2*‖v-e‖ := by
  -- Derive the actual observed cross radius and its admissible interval from the genuine midpoint theorem.
  let t := ‖cgOperator R v-(inner ℝ v (cgOperator R v)) • v‖
  have hm := (completionMidpoint_bounds v e hv he R hR hRn).2
  have ht : 0≤t := norm_nonneg _
  have hgap : 0≤1-t^2 := (abs_nonneg _).trans hm
  have hc := midpoint_cross_entry_bound v e f hv hf hef R hR hRn
  have hprod := mul_le_mul hm hc (abs_nonneg _) hgap
  have hmax := cubic_tradeoff_max ht
  have hsmall : (1-t^2)*(2*‖v-e‖)≤2*‖v-e‖ := by nlinarith [mul_nonneg (sq_nonneg t) (norm_nonneg (v-e))]
  change _≤2/(3*Real.sqrt 3)+2*‖v-e‖
  change _≤(1-t^2)*(t+2*‖v-e‖) at hprod
  nlinarith


/-- Scaling an actual source matrix scales its true hidden quadratic entry by the same real factor.
Use: return the exact unit-budget midpoint coefficient to the source's original physical perturbation scale.
Article: main_krylov, thm:C2(c), linearity of the genuine quadratic entry.
Proof: the actual matrix action and the real inner product are linear in the operator. -/
theorem completionQuadratic_smul (e : EuclideanSpace ℝ (Fin n))
    (R : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    completionQuadratic e (c • R)=c*completionQuadratic e R := by
  simp only [completionQuadratic,cgOperator,map_smul,_root_.smul_apply,real_inner_smul_right]

/-- The original primitive-budget consistency midpoint has the sharp informed quadratic coefficient with an explicit actual moving-normal error, including every zero budget.
Use: a proved first-order normal displacement gives the complete genuine cubic loss in the actual informed terminal expansion.
Article: main_krylov, thm:C2(c), |q−q̂||eᵀRf|≤2ω²/(3√3)+2ω²‖v−e‖.
Proof: a zero budget forces the actual matrix and both original scalar
entries to vanish. For a positive budget, normalize the genuine matrix to
the unit spectral ball. Both original quadratic factors scale by exactly
ω, so the actual unit midpoint coefficient bound scales by ω².
-/
theorem budgetCompletionMidpoint_coefficient_bound (ω : ℝ) (hω : 0≤ω)
    (v e f : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖=1) (he : ‖e‖=1) (hf : ‖f‖=1)
    (hef : inner ℝ e f=0) (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm) (hRn : ‖R‖≤ω) :
    |completionQuadratic e R-budgetCompletionMidpoint ω v e R| * |inner ℝ e (cgOperator R f)|≤
      (2/(3*Real.sqrt 3))*ω^2+2*ω^2*‖v-e‖ := by
  -- Genuine zero profiles require neither a normalizing division nor an inverse-gap assumption.
  by_cases hw : ω=0
  · have hz : R=0 := norm_eq_zero.mp (le_antisymm (hRn.trans_eq hw) (norm_nonneg _))
    simp only [hw,hz,budgetCompletionMidpoint,zero_mul,completionQuadratic,cgOperator,map_zero,
      _root_.zero_apply,inner_zero_right,sub_zero,abs_zero,mul_zero,zero_pow (by omega : 2≠0),add_zero,le_refl]
  · have hunit : ‖ω⁻¹ • R‖≤1 := by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hω)]
      exact (mul_le_mul_of_nonneg_left hRn (inv_nonneg.mpr hω)).trans_eq (inv_mul_cancel₀ hw)
    have hb := completionMidpoint_coefficient_bound v e f hv he hf hef (ω⁻¹ • R) (hR.smul _) hunit
    have hrestore : ω • (ω⁻¹ • R)=R := by rw [smul_smul,mul_inv_cancel₀ hw,one_smul]
    have hq := congrArg (completionQuadratic e) hrestore
    rw [completionQuadratic_smul] at hq
    have hc : inner ℝ e (cgOperator R f)=ω*inner ℝ e (cgOperator (ω⁻¹ • R) f) := by
      have hh := congrArg (fun M => inner ℝ e (cgOperator M f)) hrestore
      simpa only [cgOperator,map_smul,_root_.smul_apply,real_inner_smul_right] using hh.symm
    rw [← hq,budgetCompletionMidpoint,← mul_sub,hc,abs_mul,abs_mul,abs_of_nonneg hω]
    have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg ω)
    convert hh using 1 <;> ring

end
end krylov.Information
