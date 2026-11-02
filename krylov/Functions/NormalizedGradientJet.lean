import krylov.Functions.MidpointReferenceJet
import chebyshev1.Nonlinear.AveragedHessian

/-!
Article: main_krylov, lem:cycle-transfer, genuine normalized gradient first jet.
Use: derive the missing initial-gradient component of the complete native
finite source from actual derivatives, uniformly over bounded starts.
Source: the genuine averaged-Hessian midpoint expansion and exact FTC on
the actual radial segment. No normalized input jet is assumed.
-/

namespace krylov.Functions
noncomputable section
open Set Metric chebyshev1.Nonlinear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The actual normalized initial gradient has its precise first jet
one-half D[u]u, uniformly over every bounded family of actual starts.
Article: main_krylov, lem:cycle-transfer. -/
theorem normalizedGradient_reference_jet (G : E → F) (H : E → E →L[ℝ] F)
    (Q : E →L[ℝ] F) (D : E →L[ℝ] E →L[ℝ] F)
    {r : ℝ} (hr : 0<r) (hG0 : G 0=0) (hH0 : H 0=Q)
    (hc : ContinuousOn H (ball 0 r)) (hD : HasFDerivAt H D 0)
    (hG : ∀ z∈ball 0 r, HasFDerivAt G (H z) z)
    (B : ℝ) (hB : 0<B) :
    ∀ η : ℝ, 0<η → ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ → ∀ u : E, ‖u‖≤B →
      ‖ε⁻¹ • G (ε • u)-Q u-ε • ((1/2 : ℝ) • D u u)‖≤η*ε := by
  intro η hη
  obtain ⟨ej,hej,hjet⟩ := averagedHessian_reference_jet H D hr hc hD (B+1) 0
    (by positivity) (le_refl 0) (η/(B+1)) (by positivity)
  refine ⟨min ej (r/(B+1)),by positivity,?_⟩
  intro ε hε he u hu
  have hseg (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) : ‖(0 : E)+t • (ε • u)‖≤B*ε := by
    rw [zero_add,norm_smul,norm_smul,Real.norm_of_nonneg ht.1,Real.norm_of_nonneg hε.le]
    have hm := mul_le_mul_of_nonneg_left hu hε.le
    have ht' := mul_le_mul_of_nonneg_right ht.2 (by positivity : 0≤ε*‖u‖)
    nlinarith only [hm,ht']
  have hscale : B*ε<r := by
    have hh := (lt_div_iff₀ (by positivity : 0<B+1)).mp (he.trans_le (min_le_right _ _))
    nlinarith only [hh,hε]
  have hpath (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) : (0 : E)+t • (ε • u)∈ball 0 r := by
    simpa only [mem_ball,dist_zero_right] using (hseg t ht).trans_lt hscale
  have ha : ContinuousOn (fun t : ℝ => H ((0 : E)+t • (ε • u))) (Icc 0 1) :=
    hc.comp (by fun_prop) hpath
  have hFTC := averagedDerivative_apply G H 0 (ε • u) ha (fun t ht => hG _ (hpath t ht))
  rw [zero_add,hG0,sub_zero,map_smul] at hFTC
  have hnorm : ε⁻¹ • G (ε • u)=averagedDerivative H 0 (ε • u) u := by
    rw [←hFTC,smul_smul,inv_mul_cancel₀ hε.ne',one_smul]
  have hp := hjet ε hε (he.trans_le (min_le_left _ _)) 0 (ε • u) ((1/2 : ℝ) • u)
    (fun t ht => (hseg t ht).trans (by nlinarith only [hε.le]))
    (by simp only [zero_add,smul_smul,mul_comm,sub_self,norm_zero,mul_zero,le_refl])
  rw [hH0] at hp
  have heq : ε⁻¹ • G (ε • u)-Q u-ε • ((1/2 : ℝ) • D u u) =
      (averagedDerivative H 0 (ε • u)-Q-ε • D ((1/2 : ℝ) • u)) u := by
    rw [hnorm]
    simp only [_root_.sub_apply,map_smul,_root_.smul_apply,smul_smul]
  rw [heq]
  calc
    _ ≤ ‖averagedDerivative H 0 (ε • u)-Q-ε • D ((1/2 : ℝ) • u)‖*‖u‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (η/(B+1)*ε)*B := by gcongr
    _ ≤ η*ε := by
      have hh : (B+1)*(η/(B+1))=η := by field_simp
      have hhe := congrArg (fun z : ℝ => z*ε) hh
      have hm := mul_nonneg (div_nonneg hη.le (by positivity : 0≤B+1)) hε.le
      nlinarith only [hhe,hm]

end
end krylov.Functions
