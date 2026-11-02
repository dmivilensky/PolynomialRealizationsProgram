import krylov.Information.KnownBaseMinimaxValue

/-!
Article: main_krylov, thm:C2(c), genuine known-base minimax risk.
Use: the real finite-history informed algorithm attains the sharp source
infimum of true physical scenario suprema, with derived finiteness and a
common cubic remainder including zero budgets.
Source: genuine fixed-base signed physical lower witnesses, actual informed
all-scenario upper and complete-lattice comparisons for the true method class.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant krylov.Envelope
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability krylov.Variation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- The true known-base minimax and actual informed-policy source supremum have the same sharp quadratic coefficient and common cubic bracket.
Use: the finite-history midpoint algorithm attains the genuine physical-source minimax to the printed order.
Article: main_krylov, thm:C2(c), actual sharp known-base minimax bound.
Proof: choose the actual all-source informed tube before every budget. The genuine signed lower pair forces every real strategy, while the observed midpoint policy is an actual member of that same source information class. Its real physical supremum gives the matching common upper endpoint. -/
theorem knownBase_minimax_bracket
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N) (hcount : referenceAtomCount A hA g=N+1) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ ω : ℝ, 0≤ω → ω≤δ →
      ENNReal.ofReal ((2/(3*Real.sqrt 3))*ω^2-C*ω^3)≤knownBaseMinimax A g N ω ∧
      knownBaseMinimax A g N ω≤knownBaseWorstOutputRatio (knownBaseMidpointMethod A g ω) A g N ω ∧
      knownBaseWorstOutputRatio (knownBaseMidpointMethod A g ω) A g N ω≤
        ENNReal.ofReal ((2/(3*Real.sqrt 3))*ω^2+C*ω^3) := by
  -- Fix the true common source tube before the budget and all competing policies.
  obtain ⟨δU,CU,hδU,hCU,hupper⟩ := admissible_midpoint_sharp_upper A hA g hcount hN
  refine ⟨min δU (1/2),CU+2,lt_min hδU (by norm_num),by positivity,?_⟩
  intro ω hω hωδ
  have hωU : ω≤δU := hωδ.trans (min_le_left _ _)
  have hωhalf : ω≤(1/2 : ℝ) := hωδ.trans (min_le_right _ _)
  have hpow := pow_nonneg hω 3
  refine ⟨?_,?_,?_⟩
  · apply le_iInf
    intro M
    exact (ENNReal.ofReal_le_ofReal (by nlinarith :
      (2/(3*Real.sqrt 3))*ω^2-(CU+2)*ω^3≤(2/(3*Real.sqrt 3))*ω^2-2*ω^3)).trans
      (knownBaseWorst_sharp_lower A hA g hN hcount M.method.policy M.consistent M.oneCorrection ω hω hωhalf)
  · exact iInf_le _ (changedFinalStrategy N (midpointModelChange A g ω))
  · unfold knownBaseWorstOutputRatio
    apply iSup_le
    intro S
    apply ENNReal.ofReal_le_ofReal
    exact (hupper ω hω hωU S.val S.property.1 S.property.2).trans (by nlinarith)


/-- Both the genuine known-base minimax and the actual midpoint-policy worst physical risk are finite and differ from the sharp informed coefficient by at most one uniform cubic amount.
Use: the complete actual minimax assertion is an ordinary real error estimate, including the zero profile.
Article: main_krylov, thm:C2(c), actual sharp known-base minimax bound.
Proof: the true source bracket proves finiteness from its finite upper endpoint. The proved real-risk conversion then yields both sharp-coefficient cubic absolute-error bounds. -/
theorem knownBase_minimax_cubic
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N) (hcount : referenceAtomCount A hA g=N+1) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ ω : ℝ, 0≤ω → ω≤δ →
      knownBaseMinimax A g N ω≠⊤ ∧
      knownBaseWorstOutputRatio (knownBaseMidpointMethod A g ω) A g N ω≠⊤ ∧
      |(knownBaseMinimax A g N ω).toReal-(2/(3*Real.sqrt 3))*ω^2|≤C*ω^3 ∧
      |(knownBaseWorstOutputRatio (knownBaseMidpointMethod A g ω) A g N ω).toReal-
        (2/(3*Real.sqrt 3))*ω^2|≤C*ω^3 := by
  -- Convert the same actual source bracket for both genuine risks.
  obtain ⟨δ,C,hδ,hC,hbound⟩ := knownBase_minimax_bracket A hA g hN hcount
  refine ⟨δ,C,hδ,hC,?_⟩
  intro ω hω hωδ
  obtain ⟨hl,hm,hu⟩ := hbound ω hω hωδ
  have hK : 0≤(2/(3*Real.sqrt 3))*ω^2 := by positivity
  have he : 0≤C*ω^3 := mul_nonneg hC.le (pow_nonneg hω 3)
  have hmin := realRisk_bracket hK he hl (hm.trans hu)
  have hinformed := realRisk_bracket hK he (hl.trans hm) hu
  exact ⟨hmin.1,hinformed.1,hmin.2,hinformed.2⟩



end
end krylov.Information
