import krylov.Convergence.VirtualNearExact
import krylov.Convergence.VirtualDirectionTensorCubic
import krylov.Convergence.VirtualDirectionReferenceComparison
import krylov.Convergence.VirtualReferenceTrialDictionary

/-!
Article: main_krylov, thm:V, direction-basis near-exact cubic consequence.
Use: prove the literal native direction-basis XRFC output is cubic from
original positive smooth direction trial data and near-exact reference
trials. The shared coefficient envelope needs no additional step-basis
hypotheses: these follow from exact equality of reference histories.
Source: genuine native tensor remainder and physical gradient Taylor bound.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
  krylov.Stability krylov.OneGradient krylov.Secant
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
set_option maxHeartbeats 1000000

/-- The actual direction-basis policy has cubic dual-gradient and true
error bounds for reference trial misses of order epsilon, uniformly on
its original compact full-reference family. -/
theorem xrfcDFunction_near_exact_cubic
    (trial : History E → ℝ) (hhom : ObservedTrialHomogeneous trial)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (U : Set E) (hU : IsCompact U)
    (hcount : ∀ u∈U,referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ u∈U,∀ i<n,0<trial (oneGradientRun (xrfcDMethod fullMemory trial)
      (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ u∈U,∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (r : ℝ) (hr : 0<r)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base) {L : ℝ≥0}
    (hH : LipschitzOnWith L H (ball 0 r))
    (hF : ∀ x∈ball 0 r,HasFDerivAt f (innerSL ℝ (G x)) x)
    (hG : ∀ x∈ball 0 r,HasFDerivAt G (H x) x)
    (D : E → E →L[ℝ] E →L[ℝ] E)
    (hD : ∀ z∈ball 0 r,HasFDerivAt H (D z) z)
    {L₃ : ℝ≥0} (hL₃ : LipschitzOnWith L₃ D (ball 0 r)) (hn : 0<n)
    (B : ℝ) (hB : 0≤B) :
    ∃ ep C : ℝ,0<ep ∧0<C ∧∀ ε : ℝ,0<ε →ε<ep →∀ u∈U,
      (∀ l<n,|xrfcTrialError trial base (cgOperator base u) l|≤B*ε) →
      ‖cgOperator (metricRoot base)⁻¹ (G (xrfcDFunctionOutput trial G (ε • u)))‖≤C*ε^3 ∧
      ‖metricCoordinates base hb (xrfcDFunctionOutput trial G (ε • u))‖≤C*ε^3 := by
  let R:=cgOperator (metricRoot base)⁻¹
  let M:=‖R‖^3*‖D 0‖
  have hdict (u) (hu : u∈U):=
    xrfc_reference_trial_dictionary_of_direction trial (cgOperator base)
      (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 (cgOperator base u) n
      (fun i hi=>cg_nonstagnation base hb (cgOperator base u) i (by rw [hcount u hu];exact hi))
      (ht u hu) 2 (hT u hu)
  have htS : ∀ u∈U,∀ i<n,0<trial (oneGradientRun (xrfcMethod fullMemory trial)
      (fun _=>cgOperator base) (cgOperator base u) i):=fun u hu=>(hdict u hu).1
  have hTS : ∀ u∈U,∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i):=
    fun u hu=>(hdict u hu).2
  obtain ⟨Ct,hCt,hcoef⟩:=xrfc_compact_near_exact_tensor_coefficients trial base hb U hU hcount htS hTS
    (D 0) M (by dsimp only [M];positivity) (canonical_third_slice_operator_budget base hb (D 0))
  obtain ⟨eg,Cg,heg,hCg,hgrad⟩:=xrfcDFunction_compact_tensor_cubic_remainder trial hhom base hb U hU hcount ht hT
    f G H r hr hG₀ hH₀ hH hF hG D hD hL₃ hn
  obtain ⟨ep,Cp,hep,hCp,hpoint⟩:=xrfcDFunction_compact_reference_comparison trial hhom base hb U hU hcount ht hT
    G H r hr hG₀ hH₀ hH hG
  let E₄:=‖R‖*((L:ℝ)/2)*Cp^2
  have hE₄ : 0≤E₄:=by dsimp only [E₄];positivity
  refine ⟨min eg (min ep (min 1 (r/(Cp+1)))),Cg+Ct*B+E₄+1,by positivity,by positivity,?_⟩
  intro ε hε he u hu herr
  have he1 : ε≤1:=he.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heR : ε<r/(Cp+1):=he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hg:=hgrad ε hε (he.trans_le (min_le_left _ _)) u hu
  have hc:=(hcoef u hu (B*ε) (mul_nonneg hB hε.le) herr).2
  have hp:=(hpoint ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu).2
  let x:=xrfcDFunctionOutput trial G (ε • u)
  have hgnorm : ‖R (G x)‖≤(Cg+Ct*B)*ε^3 := by
    calc
      _ ≤ ‖R (G x)-ε^2 • xrfcDTensorCoefficient trial base (D 0) u‖+
          ‖ε^2 • xrfcDTensorCoefficient trial base (D 0) u‖ := norm_le_norm_sub_add _ _
      _ ≤ Cg*ε^3+ε^2*(Ct*(B*ε)) := by
        apply add_le_add hg
        rw [norm_smul,Real.norm_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_left hc (sq_nonneg _)
      _ = _ := by ring
  have he2 : ε^2≤ε:=by nlinarith only [hε,he1]
  have hx : x∈ball (0:E) r := by
    rw [mem_ball_zero_iff]
    have hh:=(lt_div_iff₀ (by positivity : 0<Cp+1)).mp heR
    exact hp.trans_lt (by nlinarith only [hh,hε,mul_le_mul_of_nonneg_left he2 hCp.le])
  have htaylor:=gradient_model_quadratic_error G H (cgOperator base) (ball 0 r)
    (convex_ball 0 r) (mem_ball_self hr) hH₀ hH hG x hx
  rw [hG₀,sub_zero] at htaylor
  have hrem : ‖R (G x-cgOperator base x)‖≤E₄*ε^3 := by
    have hh:=(R.le_opNorm _).trans (mul_le_mul_of_nonneg_left htaylor (norm_nonneg _))
    have hs:=pow_le_pow_left₀ (norm_nonneg _) hp 2
    have hε4 : ε^4≤ε^3:=by nlinarith only [mul_le_mul_of_nonneg_right he1 (pow_nonneg hε.le 3)]
    calc
      _ ≤ ‖R‖*((L:ℝ)/2*‖x‖^2) := hh
      _ ≤ ‖R‖*((L:ℝ)/2*(Cp*ε^2)^2) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hs (by positivity)) (norm_nonneg _)
      _ = E₄*ε^4 := by dsimp only [E₄];ring
      _ ≤ E₄*ε^3 := mul_le_mul_of_nonneg_left hε4 hE₄
  constructor
  · exact hgnorm.trans (by nlinarith only [hE₄,pow_pos hε 3])
  · calc
      _ = ‖R (G x)-R (G x-cgOperator base x)‖ := by
        rw [map_sub,sub_sub_cancel]
        exact (congrArg norm (canonical_reference_action base hb x)).symm
      _ ≤ ‖R (G x)‖+‖R (G x-cgOperator base x)‖ := norm_sub_le _ _
      _ ≤ (Cg+Ct*B)*ε^3+E₄*ε^3 := add_le_add hgnorm hrem
      _ ≤ (Cg+Ct*B+E₄+1)*ε^3 := by nlinarith only [pow_pos hε 3]


/-- Only the genuine original C-three, Lipschitz-third hypotheses and
primitive direction-basis trial data are used in the cubic consequence. -/
theorem xrfcDFunction_near_exact_original_C3_cubic
    (trial : History E → ℝ) (hhom : ObservedTrialHomogeneous trial)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (U : Set E) (hU : IsCompact U)
    (hcount : ∀ u∈U,referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ u∈U,∀ i<n,0<trial (oneGradientRun (xrfcDMethod fullMemory trial)
      (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ u∈U,∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (r : ℝ) (hr : 0<r)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hF : ∀ x∈ball 0 r,HasFDerivAt f (innerSL ℝ (G x)) x)
    (hG : ∀ x∈ball 0 r,HasFDerivAt G (H x) x)
    (D : E → E →L[ℝ] E →L[ℝ] E)
    (hD : ∀ z∈ball 0 r,HasFDerivAt H (D z) z)
    {L₃ : ℝ≥0} (hL₃ : LipschitzOnWith L₃ D (ball 0 r)) (hn : 0<n)
    (B : ℝ) (hB : 0≤B) :
    ∃ ep C : ℝ,0<ep ∧0<C ∧∀ ε : ℝ,0<ε →ε<ep →∀ u∈U,
      (∀ l<n,|xrfcTrialError trial base (cgOperator base u) l|≤B*ε) →
      ‖cgOperator (metricRoot base)⁻¹ (G (xrfcDFunctionOutput trial G (ε • u)))‖≤C*ε^3 ∧
      ‖metricCoordinates base hb (xrfcDFunctionOutput trial G (ε • u))‖≤C*ε^3 := by
  have hDc : ContinuousAt D 0:=hL₃.continuousOn.continuousAt
    (isOpen_ball.mem_nhds (mem_ball_self hr))
  obtain ⟨s,L,hs,hsr,hLip⟩:=exists_hessian_lipschitz_ball H D hr hD hDc
  have hsub : ball (0:E) s⊆ball 0 r:=ball_subset_ball hsr
  exact xrfcDFunction_near_exact_cubic trial hhom base hb U hU hcount ht hT
    f G H s hs hG₀ hH₀ hLip (fun z hz=>hF z (hsub hz)) (fun z hz=>hG z (hsub hz))
    D (fun z hz=>hD z (hsub hz)) (hL₃.mono hsub) hn B hB

end
end krylov.Convergence
