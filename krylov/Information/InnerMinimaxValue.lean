import krylov.Information.InnerLower
import krylov.Information.MinimaxBound


/-!
Article: main_krylov, s4:cor-Q, genuine inner-class sharp minimax attainment.
Use: take the actual original pre-quadratic inner-source supremum and
genuine source-method infimum, proving the same sharp coefficient and
uniform cubic remainder with real RFC attainment for every profile.
Source: actual scaled admissible signed witnesses, true whole-source RFC
upper bound and complete-lattice source risk comparisons.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
variable {N : ℕ}

/-- The original physical pre-quadratic class with an existential genuine positive full-active quadratic reference.
Use: Define the actual source subclass without supplying a common flag or desired execution.
Article: main_krylov, s4:cor-Q, genuine inner-class minimax attainment. -/
def Scenario.FullPreQuadratic (S : Scenario (N+1)) (g : EuclideanSpace ℝ (Fin (N+1))) : Prop :=
  ∃ (Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hQ : Q.PosDef),
    referenceAtomCount Q hQ g=N+1 ∧ S.PreQuadratic (cgOperator Q) g N

/-- The genuine supremal own-normalized output risk over original pre-quadratic inner physical source scenarios.
Use: State sharp attainment on the actual original subclass Q ∩ S^natural.
Article: main_krylov, s4:cor-Q, genuine inner-class minimax attainment. -/
def innerWorstOutputRatio (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1))))
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (g : EuclideanSpace ℝ (Fin (N+1)))
    (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ) : ENNReal :=
  ⨆ S : {S : Scenario (N+1) // S.NaturalInner A r ω w τ ∧ S.FullPreQuadratic g},
    ENNReal.ofReal (S.val.outputRatio m g N)

/-- The genuine infimum of inner-source worst risks over the actual original one-correction CG-consistent information class.
Use: Compare the original minimax leading value with the value attained inside its original inner subclass.
Article: main_krylov, s4:cor-Q, genuine inner-class minimax attainment. -/
def innerOneCorrectionMinimax (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (N+1))) (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ) : ENNReal :=
  ⨅ M : OneCorrectionCGStrategy (EuclideanSpace ℝ (Fin (N+1))),
    innerWorstOutputRatio M.method.policy A g r ω w τ

/-- Restricting the original physical sources to the actual pre-quadratic inner class decreases the genuine worst risk.
Use: Transfer the proved whole-source sharp RFC upper bound to the actual inner supremum.
Article: main_krylov, s4:cor-Q, genuine inner-class minimax attainment.
Proof: Every real inner-class source satisfies the original admissibility constraints, so each genuine indexed risk belongs to the outer supremum. -/
theorem innerWorstOutputRatio_le_outer (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1))))
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (g : EuclideanSpace ℝ (Fin (N+1)))
    (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ) :
    innerWorstOutputRatio m A g r ω w τ≤worstOutputRatio m A g N r ω w τ := by
  apply iSup_le
  intro S
  exact le_iSup_of_le ⟨S.val,S.property.1.original⟩ le_rfl

/-- The true risks of any two actual pre-quadratic inner sources are bounded by their genuine source supremum.
Use: Insert the real signed attaining witnesses into the actual inner risk.
Article: main_krylov, s4:cor-Q, genuine inner-class minimax attainment.
Proof: The nonnegative embedding preserves maxima and both genuine sources are actual indices of the same inner supremum. -/
theorem max_outputRatio_le_inner (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1))))
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (g : EuclideanSpace ℝ (Fin (N+1)))
    (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ) (S T : Scenario (N+1))
    (hS : S.NaturalInner A r ω w τ ∧ S.FullPreQuadratic g)
    (hT : T.NaturalInner A r ω w τ ∧ T.FullPreQuadratic g) :
    ENNReal.ofReal (max (S.outputRatio m g N) (T.outputRatio m g N)) ≤ (innerWorstOutputRatio m A g r ω w τ) := by
  rw [ENNReal.ofReal_max]
  exact max_le (le_iSup_of_le ⟨S,hS⟩ le_rfl) (le_iSup_of_le ⟨T,hT⟩ le_rfl)

/-- Every genuine original source method has the sharp actual inner-subclass worst-risk lower bound with a common cubic remainder.
Use: Promote explicit admissible pre-quadratic signed witnesses to the original physical subclass supremum.
Article: main_krylov, s4:cor-Q, genuine inner-class minimax attainment.
Proof: The proved actual inner signed scenarios satisfy every original primitive margin and real probe condition. Their actual maximum forces the sharp lower coefficient and belongs to the genuine indexed source supremum. -/
theorem innerWorstOutputRatio_sharp_lower
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N) (hcount : referenceAtomCount A hA g=N+1) :
    ∃ ε C : ℝ, 0<ε ∧ 0<C ∧
      ∀ (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))), CGConsistent m → OneCorrectionMethod m →
      ∀ (ω : ℕ → ℝ) (w τ r : ℝ), (∀ i<N, 0≤ω i) → 0≤w → 0≤τ → 0≤r →
        (∑ i∈range N, ω i)+w≤(1/2 : ℝ) →
        (5+4*r)*(∑ i∈range N, ω i)≤r → (∑ i∈range N, ω i)<ε →
        4*((N : ℝ)+1)*(∑ i∈range N, ω i)≤1 →
        ENNReal.ofReal (sharpConstant (∑ i∈range N, ω i) w-C*((∑ i∈range N, ω i)+w)^3)≤
          innerWorstOutputRatio m A g r ω w τ := by
  -- The actual signed witnesses supply genuine indices of the original inner source supremum.
  obtain ⟨ε,C,hε,hC,hlower⟩ := inner_preQuadratic_normalized_lower A hA g hN hcount
  refine ⟨ε,C,hε,hC,?_⟩
  intro m hm h1 ω w τ r hω hw hτ hr hs hmargin hWε hslack
  obtain ⟨S,T,hS,hT,hpreS,hpreT,hbound⟩ := hlower m hm h1 ω w τ r hω hw hτ hr hs hmargin hWε hslack
  exact (ENNReal.ofReal_le_ofReal hbound).trans (max_outputRatio_le_inner m A g r ω w τ S T
    ⟨hS,⟨A,hA,hcount,hpreS⟩⟩ ⟨hT,⟨A,hA,hcount,hpreT⟩⟩)


end
end krylov.Information
