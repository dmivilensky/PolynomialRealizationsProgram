import krylov.Information.CentredRFC

/-!
Article: main_krylov, s4:cor-Q, genuine own-normalized instance comparison.
Use: Actual original-budget inverse-model instance factor in the common base metric.
Source: actual common-centre execution and robust radius, genuine compact
CG reference regularity and elementary real order and positive-ratio algebra.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- Every actual one-correction CG-consistent method has common-twin fixed-base output radius at least the true RFC output divided by 1+4n times the primitive maximal budget.
Use: Derive the original inverse-model instance factor from real source budgets.
Article: main_krylov, s4:cor-Q, original instance factor and normalization.
Proof: The primitive total and maximal budgets prove the genuine centre domain and relative inverse bound. Its true hidden-error budget bounds the actual robust operator norm by 4n times the maximal budget. The proved real common-twin radius then gives the stated actual-output comparison. -/
theorem Scenario.PreQuadratic.rfc_instance_fixed_metric {S : Scenario (N+1)}
    {Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount Q hQ g=N+1)
    (h : S.PreQuadratic (cgOperator Q) g N) (hN : 0<N) (hbase : S.base.PosDef)
    (hE : ∀ l<N, (S.increment l).IsSymm) (hT : S.terminal.IsSymm)
    (ω : ℕ → ℝ) (w μ : ℝ) (hμ : 0≤μ)
    (hω : ∀ l<N, relativeBudget S.base (S.increment l)≤ω l)
    (hw : relativeBudget S.base S.terminal≤w)
    (hprofile : ∀ l<N, ω l≤μ) (hwμ : w≤μ)
    (hsmall : 4*((N : ℝ)+1)*(∑ l∈range N, ω l)≤1) (hμsmall : 6*((N : ℝ)+1)*μ≤1)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m) (h1 : OneCorrectionMethod m) :
    ‖cgOperator (metricRoot S.base)⁻¹
      (probedGradient (rfcMethod fullMemory 1) S.probeOracle (S.correctionOracle N) g (N+1))‖≤
      (1+4*((N : ℝ)+1)*μ)*
      max ‖cgOperator (metricRoot S.base)⁻¹ (probedGradient m S.probeOracle (S.correctionOracle N) g (N+1))‖
        ‖cgOperator (metricRoot S.base)⁻¹ (probedGradient m (S.preQuadraticTwin Q g).probeOracle
          ((S.preQuadraticTwin Q g).correctionOracle N) g (N+1))‖ := by
  -- Primitive profile bounds supply the genuine centre inverse domain and robust factor.
  let W := ∑ l∈range N, ω l
  let J := S.preQuadraticCentre Q g
  let Δ := S.lastOperator N-J
  let K := cgOperator (relativeOperator S.base Δ*(relativeOperator S.base J)⁻¹)
  have hWμ : W≤(N : ℝ)*μ := by
    calc
      _ ≤ ∑ l∈range N, μ := sum_le_sum fun l hl => hprofile l (mem_range.mp hl)
      _ = _ := by simp
  have hhalf : 3*W≤(1/2 : ℝ) := by nlinarith
  obtain ⟨_,hJu,hinv⟩ := h.centre_domain hQ hcount hbase hE hT ω w hω hw hsmall hhalf
  have hdb : ‖relativeOperator S.base Δ‖≤2*W+w :=
    (h.centre_budgets hQ hcount hbase hE hT ω w hω hw hsmall).2
  have hKn : ‖K‖≤4*((N : ℝ)+1)*μ := by
    change ‖relativeOperator S.base Δ*(relativeOperator S.base J)⁻¹‖≤_
    have hp := norm_mul_le (relativeOperator S.base Δ) (relativeOperator S.base J)⁻¹
    have hm' := mul_le_mul_of_nonneg_left hinv (norm_nonneg (relativeOperator S.base Δ))
    nlinarith [norm_nonneg (relativeOperator S.base Δ)]
  have hr := h.common_radius_rfc hQ hcount hN hbase hE hJu m hm h1
  have hk : 0≤‖K‖ := norm_nonneg _
  have hs : 0<Real.sqrt (1+‖K‖^2) := Real.sqrt_pos.mpr (by positivity)
  have hb : Real.sqrt (1+‖K‖^2)≤1+‖K‖ := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith⟩
  have hx := (div_le_iff₀ hs).mp hr
  exact hx.trans ((mul_le_mul_of_nonneg_left (hb.trans (by linarith))
    (le_max_of_le_left (norm_nonneg _))).trans_eq (mul_comm _ _))

end
end krylov.Information
