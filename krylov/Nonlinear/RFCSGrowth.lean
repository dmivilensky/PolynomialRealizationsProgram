import krylov.Correction.RFCSOperatorCoordinates
import krylov.Correction.RFCSCompactBounds
import krylov.Nonlinear.RFCSFunction

/-!
Article: main_krylov, thm:RFCS, growth of genuine nonlinear prefixes.
Use: Derive uniform bounds on every actual gradient, selected direction
and physical iterate of a real finite-probe RFC-S cycle from small genuine
gradient-model Lipschitz error and compact full-active reference data.
Source: actual self-adjoint measured secant representatives, the exact finite
operator dictionary, compact genuine prefix bounds and proved exact field
homogeneity. The actual operators and trajectories are constructed, not assumed.
-/

namespace krylov.Nonlinear
noncomputable section
open Set krylov.Methods krylov.Reference krylov.Correction
open scoped NNReal
variable {k : ℕ}

/-- One compact-reference tube controls the genuine nonlinear RFC-S gradients and directions by the actual cycle scale and all true intermediate point displacements by the finite sum of those step bounds.
Use: Localize genuine finite nonlinear requests before substituting averaged Hessians in the source remainder theorem.
Article: main_krylov, thm:RFCS, uniform actual nonlinear prefix localization.
Proof: Construct uniformly close self-adjoint operators from the actual measured probes and total steps. Pack the real transcript into the direct source, apply the proved compact bounds to its normalized initial gradient, and use exact homogeneity. Summing the true recorded total steps bounds every actual physical iterate.
-/
theorem compact_rfcs_function_prefix_bounds (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g) :
    ∃ δ M : ℝ, 0<δ ∧ 0<M ∧
      ∀ G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)),
      ∀ x₀ : EuclideanSpace ℝ (Fin (k+1)), ∀ h : ℕ → ℝ, (∀ i, h i≠0) →
      ∀ η : ℝ≥0, LipschitzWith η (fun x => G x-cgOperator base x) → 2*(η : ℝ)≤δ →
      ∀ ε : ℝ, 0<ε → ∀ g∈K, ‖ε⁻¹ • G x₀-g‖≤δ →
      (∀ i≤k+1, ‖(rfcSFunctionRun fullMemory G x₀ h i).gradient‖≤ε*M ∧
        ‖rfcSFunctionPoint fullMemory G x₀ h i-x₀‖≤(k+1 : ℕ)*(ε*M)) ∧
      (∀ i<k+1, ‖windowDirection (selectedWindow fullMemory (rfcSFunctionRun fullMemory G x₀ h i))
        (rfcSFunctionRun fullMemory G x₀ h i).gradient‖≤ε*M) := by
  obtain ⟨δ,M,hδ,hM,hbound⟩ := compact_rfcs_operator_prefix_bounds base hb K hK hN
  refine ⟨δ,M,hδ,hM,?_⟩
  intro G x₀ h hh η hG hη ε hε g hg hv
  have hQ : IsSelfAdjoint (cgOperator base) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    exact (cgOperator_positive base hb).1
  obtain ⟨Ap,A,hclose,hrep⟩ := rfcSFunctionRun_representatives fullMemory G x₀ h hh (cgOperator base) hQ hG
  let Θ := rfcsParametersOfOperators base Ap A
  let g' := ε⁻¹ • G x₀
  let z := (g',Θ)
  let P := rfcsDirectProbe base z
  let S := rfcsDirectLine base z
  have hΘ : ‖Θ‖≤δ := (rfcsParametersOfOperators_norm_le base Ap A η.2
    (fun i _ => (hclose i).2.1) (fun i _ => (hclose i).2.2.2)).trans hη
  have hg' : g+(g'-g)=g' := by abel
  have hfields := hbound g hg (g'-g) Θ (norm_prod_le_iff.mpr ⟨hv,hΘ⟩)
  rw [hg'] at hfields
  have he (i : ℕ) (hi : i≤k+1) : rfcSFunctionRun fullMemory G x₀ h i=rfcSRun fullMemory P S S (G x₀) i := by
    rw [hrep i]
    exact rfcsParametersOfOperators_realizes base Ap A (G x₀) i hi
  have hscale : G x₀=ε • g' := by simp only [g',smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
  have hstep i (hi : i<k+1) : ‖rfcSStep fullMemory P S S (G x₀) i‖≤ε*M := by
    rw [hscale,((rfcS_scalar fullMemory P S S g' ε hε.ne' (i+1)).2 i (by omega)).2.2.1,
      norm_smul,Real.norm_of_nonneg hε.le]
    exact mul_le_mul_of_nonneg_left (hfields.2 i hi).2 hε.le
  refine ⟨?_,?_⟩
  · intro i hi
    constructor
    · rw [he i hi]
      change ‖rfcSGradient fullMemory P S S (G x₀) i‖≤ε*M
      rw [hscale,(rfcS_scalar fullMemory P S S g' ε hε.ne' i).1,norm_smul,Real.norm_of_nonneg hε.le]
      exact mul_le_mul_of_nonneg_left (hfields.1 i hi) hε.le
    · simp only [rfcSFunctionPoint,add_sub_cancel_left]
      rw [he i hi,rfcSRun_displacement_sum]
      calc
        _ ≤ ∑ j∈Finset.range i, ‖rfcSStep fullMemory P S S (G x₀) j‖ := norm_sum_le _ _
        _ ≤ ∑ _j∈Finset.range i, ε*M := Finset.sum_le_sum fun j hj => hstep j ((Finset.mem_range.mp hj).trans_le hi)
        _ = (i : ℝ)*(ε*M) := by simp
        _ ≤ (k+1 : ℕ)*(ε*M) := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi) (by positivity)
  · intro i hi
    rw [he i hi.le]
    change ‖rfcSDirection fullMemory P S S (G x₀) i‖≤ε*M
    rw [hscale,((rfcS_scalar fullMemory P S S g' ε hε.ne' (i+1)).2 i (by omega)).1,
      norm_smul,Real.norm_of_nonneg hε.le]
    exact mul_le_mul_of_nonneg_left (hfields.2 i hi).1 hε.le

end
end krylov.Nonlinear
