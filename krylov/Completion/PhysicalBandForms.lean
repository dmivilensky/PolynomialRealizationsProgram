import krylov.Completion.ProperObservedPencils
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau and s8:dcsdef, physical class forms.
Use: pass the original two physical positive-semidefinite class inequalities
to the exact real Hilbert-space forms used by the actual CG domain calculus.
Source: standard finite positive forms and the existing true Euclidean matrix map.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace
variable {n : ℕ}

/-- The original physical spectral-band inequalities give their genuine
Hilbert-space lower and upper quadratic bounds on every real vector.
Use: strict proper-Krylov inverse domains are derived directly from the
source matrix class, with no extra form or spectral-margin assumptions.
Article: main_krylov, thm:radau and s8:dcsdef.
Proof: evaluate both positive-semidefinite shifted matrix forms on the actual
physical vector, use the true matrix/operator inner-product dictionary and
collect the original real identity-form norm. -/
theorem physical_band_operator_forms (base : Matrix (Fin n) (Fin n) ℝ) (mu upper : ℝ)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef) :
    (∀ v : EuclideanSpace ℝ (Fin n),mu*‖v‖^2≤ inner ℝ v (cgOperator base v)) ∧
      ∀ v : EuclideanSpace ℝ (Fin n),inner ℝ v (cgOperator base v)≤upper*‖v‖^2 := by
  have hform (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef)
      (v : EuclideanSpace ℝ (Fin n)) : 0≤ inner ℝ v (cgOperator M v) := by
    simpa only [cgOperator,Matrix.inner_toEuclideanCLM,star_trivial] using
      hM.dotProduct_mulVec_nonneg (WithLp.ofLp v)
  constructor
  · intro v
    have h := hform _ hlo v
    simp only [cgOperator,map_sub,map_smul,map_one,_root_.sub_apply,_root_.smul_apply,
      one_apply_eq_self,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq] at h
    exact sub_nonneg.mp h
  · intro v
    have h := hform _ hhi v
    simp only [cgOperator,map_sub,map_smul,map_one,_root_.sub_apply,_root_.smul_apply,
      one_apply_eq_self,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq] at h
    exact sub_nonneg.mp h

end
end krylov.Completion
