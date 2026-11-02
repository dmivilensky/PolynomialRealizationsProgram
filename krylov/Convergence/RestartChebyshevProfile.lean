import krylov.Design.FCDesignBridge
import krylov.Design.HyperbolicDictionary
import krylov.Functions.RFCFPrintedTensor
import krylov.Tensor.CubicBanach
import krylov.Convergence.RestartConstants

/-!
Article: main_krylov, thm:D and apG:D, true restarted energy profiles.
Use: derive the exact Chebyshev error profile of genuine positive full-active
references and the sharp tensor-compatible FC coefficient before applying
the native scalar-function transfer.
Source: genuine energy spectral measures, the actual Christoffel/Chebyshev
minimum, true CG termination and Banach's cubic mixed-norm identity.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Finset krylov.Methods krylov.Reference krylov.Nonlinear krylov.Functions krylov.Tensor
  krylov.Variation krylov.Stability krylov.Design krylov.LinearAlgebra krylov.Secant
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every actual CG error has the original Chebyshev majorant, including
and after genuine termination. Article: main_krylov, thm:D. -/
theorem reference_error_chebyshev (I : chebyshev1.SpectralInterval)
    (R : FCReference n I.mu I.kappa) (m : ℕ) :
    ‖cgCanonicalError R.base R.gradient m‖≤I.epsilon m*R.initialNorm := by
  by_cases hm : m<n
  · let M := energySpectralData R.base R.positive R.gradient R.nonzero
    let ν := atomicProbability M (fun i=>(⟨M.node i,fcReference_energy_nodes I R i⟩ : Spectrum I))
    have hcheb := christoffel_le_chebyshev I m ν
    rw [interval_christoffel_atomic I M (fcReference_energy_nodes I R) (by have := R.full; omega)] at hcheb
    have henergy := cg_energy_christoffel R.base R.positive R.gradient R.nonzero (by have := R.full; omega : m<referenceAtomCount R.base R.positive R.gradient)
    have hh := mul_le_mul_of_nonneg_left hcheb (sq_nonneg R.initialNorm)
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (chebyshev_scale_pos I m).le R.initialNorm_pos.le)).mp
    change ‖cgCanonicalError R.base R.gradient m‖^2≤(I.epsilon m*R.initialNorm)^2
    change ‖cgCanonicalError R.base R.gradient m‖^2=R.initialNorm^2*(christoffelKernel M m 0)⁻¹ at henergy
    nlinarith only [henergy,hh]
  · have hz := (cg_stopping_iff R.base R.positive R.gradient m).mpr (by have := R.full; omega)
    simp only [cgCanonicalError,hz,map_zero,norm_zero]
    exact mul_nonneg (chebyshev_scale_pos I m).le R.initialNorm_pos.le

/-- The actual tensor's diagonal budget controls its genuine operator
slices with the exact Banach constant. Article: main_krylov, thm:D. -/
theorem cubic_slice_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (T : SymmetricCubic E) (C : ℝ) (hC : 0≤C)
    (hdiag : ∀ v,‖v‖=1 → |T.form v v v|≤C) (w : E) :
    ‖canonicalVariation T w‖≤C*‖w‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _))
  intro v
  let z := canonicalVariation T w v
  have hh := cubic_diagonal_bound T C hdiag w z v
  rw [←canonicalVariation_pair,show canonicalVariation T w v=z from rfl,
    real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at hh
  change ‖z‖≤C*‖w‖*‖v‖
  by_cases hz : z=0
  · rw [hz,norm_zero]
    positivity
  have hn : 0<‖z‖ := norm_pos_iff.mpr hz
  nlinarith only [hh,hn]

/-- True termination removes the last formal increment from the full
response, for every actual increment family. Article: thm:A and thm:D. -/
theorem fullCycleResponse_preterminal
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hcount : referenceAtomCount A hA g=n+1)
    (E : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    fullCycleResponse A g (range (n+1)) E=fullCycleResponse A g (range n) E := by
  have hz : remainingTail A g n=0 := by
    apply norm_eq_zero.mp
    rw [remainingTail_norm]
    have hg := (cg_stopping_iff A hA g (n+1)).mpr (by omega)
    simp only [cgCanonicalError,hg,map_zero,norm_zero]
  simp only [fullCycleResponse,sum_range_succ,hz,map_zero,add_zero]

/-- The genuine compatible FC coefficient is bounded by the actual
successive-error product profile, with the exact half tensor norm.
Article: main_krylov, thm:D, before the Chebyshev substitution. -/
theorem fc_tensor_error_profile
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (D : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin (n+1))))
    (hT : ∀ a b c,T.form (cgOperator (metricRoot A) a) (cgOperator (metricRoot A) b)
      (cgOperator (metricRoot A) c)=inner ℝ (D a b) c)
    (m : ℝ) (hm : 0≤m) (hdiag : ∀ v,‖v‖=1 → |T.form v v v|≤2*m)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hcount : referenceAtomCount A hA g=n+1) :
    ‖fullCycleResponse A g (range (n+1)) (ownFCCompatibleIncrements A hA D g)‖≤
      m*∑ l∈range n,‖cgCanonicalError A g l‖*‖cgCanonicalError A g (l+1)‖ := by
  rw [fullCycleResponse_preterminal A hA g hcount]
  have hbound (l : ℕ) (hl : l∈range n) :
      ‖ownFCCompatibleIncrements A hA D g l‖≤m*‖cgCanonicalError A g l‖ := by
    rw [ownFCCompatibleIncrements_third_tensor A hA D T hT,cubicSliceMatrix_norm]
    have hs := cubic_slice_norm_le T (2*m) (by positivity) hdiag (referenceMidpointDrift A g l)
    have hm' := reference_midpoint_drift_le A hA g l (by have := mem_range.mp hl; omega)
    exact hs.trans (by nlinarith only [mul_le_mul_of_nonneg_left hm' hm])
  have hb := spectral_response_le A g (range n) (ownFCCompatibleIncrements A hA D g)
    (fun l=>m*‖cgCanonicalError A g l‖) hbound
  exact hb.trans_eq (by rw [mul_sum]; apply sum_congr rfl; intro l _; ring)

/-- The original FC tensor coefficient has exactly the printed finite
Chebyshev restart constant. Article: main_krylov, thm:D, FC line. -/
theorem fc_tensor_chebyshev_constant (I : chebyshev1.SpectralInterval)
    (R : FCReference (n+1) I.mu I.kappa)
    (D : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin (n+1))))
    (hT : ∀ a b c,T.form (cgOperator (metricRoot R.base) a) (cgOperator (metricRoot R.base) b)
      (cgOperator (metricRoot R.base) c)=inner ℝ (D a b) c)
    (m : ℝ) (hm : 0≤m) (hdiag : ∀ v,‖v‖=1 → |T.form v v v|≤2*m) :
    ‖fullCycleResponse R.base R.gradient (range (n+1))
      (ownFCCompatibleIncrements R.base R.positive D R.gradient)‖≤
        m*fcRestartConstant (designSpacing I) n*R.initialNorm^2 := by
  apply (fc_tensor_error_profile R.base R.positive D T hT m hm hdiag R.gradient R.full).trans
  have hs : (∑ l∈range n, ‖cgCanonicalError R.base R.gradient l‖*
      ‖cgCanonicalError R.base R.gradient (l+1)‖)≤
      fcRestartConstant (designSpacing I) n*R.initialNorm^2 := by
    unfold fcRestartConstant
    rw [sum_mul]
    apply sum_le_sum
    intro l _
    have hh := mul_le_mul (reference_error_chebyshev I R l)
      (reference_error_chebyshev I R (l+1)) (norm_nonneg _)
      (mul_nonneg (chebyshev_scale_pos I l).le R.initialNorm_pos.le)
    simp only [epsilon_eq_sech,Nat.cast_add,Nat.cast_one] at hh
    exact hh.trans_eq (by ring)
  exact (mul_le_mul_of_nonneg_left hs hm).trans_eq (by ring)

end
end krylov.Convergence
