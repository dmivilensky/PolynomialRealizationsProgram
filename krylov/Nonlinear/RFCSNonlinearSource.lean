import krylov.Nonlinear.RFCSC1Localization
import krylov.Nonlinear.RFCSAveragedBounds
import krylov.Nonlinear.GradientQuadratic

/-!
Article: main_krylov, thm:RFCS, actual uniform nonlinear source dictionary.
Use: Derive one finite direct operator profile from the real averaged
Hessians and normalized initial gradient of every sufficiently small
nonlinear RFC-S cycle, with genuine complete-prefix equality and actual
query bounds uniform before compact references and bounded finite probes.
Source: true continuous-derivative localization, genuine averaged-Hessian
FTC, the original local Hessian Lipschitz bound and actual gradient Taylor error.
-/

namespace krylov.Nonlinear
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Correction
open scoped NNReal
variable {k : ℕ}

/-- The original finite direct operator source profile of the true averaged full-step and finite-probe Hessians of a genuine nonlinear RFC-S cycle.
Use: Keep every source entry tied to actual gradient requests and physical segments.
Article: main_krylov, thm:RFCS, actual uniform nonlinear source profile.
-/
def rfcSFunctionSource (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (x₀ : EuclideanSpace ℝ (Fin (k+1))) (h : ℕ → ℝ) : RFCSOperatorParameters (k+1) :=
  rfcsParametersOfOperators base (rfcSFunctionProbeOperator fullMemory G H x₀ h)
    (rfcSFunctionSegment fullMemory G H x₀ h)

/-- Every actual locally Lipschitz-Hessian nonlinear RFC-S cycle has one uniformly bounded genuine direct-source profile proportional to its cycle size, realizing its complete true prefixes and localizing every actual query at that scale.
Use: Share the actual nonlinear source realization between cubic remainders, true search/correction geometry and canonical self-concordant bounds.
Article: main_krylov, thm:RFCS, actual uniform nonlinear source profile.
Proof: Use the proved continuous-derivative localization to enclose all actual requests in one shrinking convex ball. The real Hessian Lipschitz bound controls its genuine averaged operators; actual gradient Taylor error controls its normalized initial datum. Pack those true operators into the original source and use the complete genuine measured-transcript dictionary for every real prefix.
-/
theorem compact_rfcs_nonlinear_source (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (r B T : ℝ) (hr : 0<r) (hB : 0<B) (hT : 0≤T)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base) {L : ℝ≥0}
    (hH : LipschitzOnWith L H (ball 0 r)) (hG : ∀ x∈ball 0 r, HasFDerivAt G (H x) x) :
    ∃ ε₀ D C : ℝ, 0<ε₀ ∧ 0<D ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤B → cgOperator base u∈K →
      ∀ h : ℕ → ℝ, (∀ i, h i≠0) → (∀ i<k+1, |h i|≤T) →
      let Θ := rfcSFunctionSource base G H (ε • u) h
      let z := (ε⁻¹ • G (ε • u),Θ)
      ‖(ε⁻¹ • G (ε • u)-cgOperator base u,Θ)‖≤C*ε ∧
      (∀ N≤k+1, rfcSFunctionRun fullMemory G (ε • u) h N=
        rfcSRun fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) (G (ε • u)) N ∧
        ‖rfcSFunctionPoint fullMemory G (ε • u) h N‖≤ε*D) ∧
      ∀ i<k+1, ‖rfcSFunctionPoint fullMemory G (ε • u) h i+h i •
        windowDirection (selectedWindow fullMemory (rfcSFunctionRun fullMemory G (ε • u) h i))
          (rfcSFunctionRun fullMemory G (ε • u) h i).gradient‖≤ε*D := by
  have hcont : ContinuousAt H 0 := (hH.continuousOn 0 (mem_ball_self hr)).continuousAt (ball_mem_nhds _ hr)
  obtain ⟨ε₁,D,hε₁,hD,hlocalized⟩ := compact_rfcs_C1_localization base hb K hK hN G H r B T hr hB hT hG₀ hH₀ hcont hG
  let C := (L : ℝ)*(B^2+2*D+1)+1
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨min ε₁ (r/(D+1)),D,C,lt_min hε₁ (div_pos hr (by positivity)),hD,hC,?_⟩
  intro ε hε he u hu hKu h hh hTbound
  dsimp only
  have he₁ := he.trans_le (min_le_left _ _)
  have her : ε*D<r := by
    have he' := (lt_div_iff₀ (by positivity : 0<D+1)).mp (he.trans_le (min_le_right _ _))
    nlinarith
  have hqueries := hlocalized ε hε he₁ u hu hKu h hh hTbound
  let S := closedBall (0 : EuclideanSpace ℝ (Fin (k+1))) (ε*D)
  have hpoint i (hi : i≤k+1) : rfcSFunctionPoint fullMemory G (ε • u) h i∈S := by
    rw [mem_closedBall_zero_iff]
    exact (hqueries.1 i hi).2
  have hprobe i (hi : i<k+1) : rfcSFunctionPoint fullMemory G (ε • u) h i+h i •
      windowDirection (selectedWindow fullMemory (rfcSFunctionRun fullMemory G (ε • u) h i))
        (rfcSFunctionRun fullMemory G (ε • u) h i).gradient∈S := by
    rw [mem_closedBall_zero_iff]
    exact (hqueries.2 i hi).2
  have hsub : S⊆ball 0 r := by
    intro x hx
    rw [mem_ball_zero_iff]
    exact (mem_closedBall_zero_iff.mp hx).trans_lt her
  have hHbound x (hx : x∈S) : ‖H x-cgOperator base‖≤(L : ℝ)*(ε*D) := by
    have hl := hH.norm_sub_le (hsub hx) (mem_ball_self hr)
    rw [hH₀,sub_zero] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) L.2)
  have hbounds := rfcSFunction_averaged_operator_bounds fullMemory G H (ε • u) h (k+1) S
    (convex_closedBall _ _) (hH.continuousOn.mono hsub) (cgOperator base) hHbound hpoint hprobe
  have hsource := rfcsParametersOfOperators_norm_le base
    (rfcSFunctionProbeOperator fullMemory G H (ε • u) h) (rfcSFunctionSegment fullMemory G H (ε • u) h)
    (by positivity : 0≤(L : ℝ)*(ε*D)) (fun i hi => (hbounds i hi).1) (fun i hi => (hbounds i hi).2)
  have hsource' : ‖rfcSFunctionSource base G H (ε • u) h‖≤C*ε := by
    apply hsource.trans
    dsimp only [C]
    calc
      2*((L : ℝ)*(ε*D)) = ((L : ℝ)*ε)*(2*D) := by ring
      _ ≤ ((L : ℝ)*ε)*(B^2+2*D+1) := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg B]) (mul_nonneg L.2 hε.le)
      _ ≤ ((L : ℝ)*ε)*(B^2+2*D+1)+ε := by linarith
      _ = _ := by ring
  have hx₀ : ε • u∈ball 0 r := by
    have hx := (hqueries.1 0 (by omega)).1
    simpa only [rfcSFunctionPoint,rfcSFunctionRun,History.displacement,List.map_nil,List.sum_nil,add_zero] using hx
  have hinit := normalized_gradient_quadratic_error G H (cgOperator base) (ball 0 r) (convex_ball 0 r)
    (mem_ball_self hr) hG₀ hH₀ hH hG u hε hx₀
  have hinit' : ‖ε⁻¹ • G (ε • u)-cgOperator base u‖≤C*ε := by
    apply hinit.trans
    have hu2 := (sq_le_sq₀ (norm_nonneg u) hB.le).mpr hu
    have hb' := mul_le_mul_of_nonneg_left hu2 (show 0≤(L : ℝ)/2*ε by positivity)
    dsimp only [C]
    have hp : 0≤(L : ℝ)*ε*D := by positivity
    nlinarith [mul_nonneg (mul_nonneg L.2 hε.le) (sq_nonneg B),mul_nonneg L.2 hε.le]
  refine ⟨norm_prod_le_iff.mpr ⟨hinit',hsource'⟩,?_,fun i hi => (hqueries.2 i hi).2⟩
  intro N hN'
  refine ⟨?_,(hqueries.1 N hN').2⟩
  have hr' := rfcSFunctionRun_averaged fullMemory G H (ε • u) h N S (convex_closedBall _ _)
    (hH.continuousOn.mono hsub) (fun x hx => hG x (hsub hx)) (fun i _ => hh i)
    (fun i hi => hpoint i (hi.trans hN')) (fun i hi => hprobe i (hi.trans_le hN'))
  exact hr'.trans (rfcsParametersOfOperators_realizes base _ _ (G (ε • u)) N hN')

end
end krylov.Nonlinear
