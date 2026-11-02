import krylov.Information.AdmissibleUpper
import krylov.Methods.Classes

/-!
Article: main_krylov, thm:C, genuine unknown-base source-class minimax value.
Use: take the actual physical scenario supremum and the infimum over all
real nonanticipating span-restricted CG-consistent one-correction policies.
Source: the derived admissible signed lower pair, genuine full-physical-class
RFC upper bound and standard complete-lattice infimum/supremum comparisons.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant
  krylov.Correction krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A genuine member of the source's CG-consistent at-most-one-correction information class.
Use: the minimax infimum retains the true observed-span and nonanticipating protocol constraints.
Article: main_krylov, thm:C, M_CG^(1). -/
structure OneCorrectionCGStrategy (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The actual nonanticipating stored-span information-class member. -/
  method : ProbedClass E
  /-- Its actual positive-quadratic execution is globally CG-consistent. -/
  consistent : CGConsistent method.policy
  /-- Every actual iteration makes at most one correction query. -/
  oneCorrection : OneCorrectionMethod method.policy

/-- Genuine full-memory RFC belongs to the precise actual source minimax class.
Use: provide an actual admissible policy for the infimum upper bound.
Article: main_krylov, thm:C, the RFC attaining strategy. -/
def rfcMinimaxStrategy (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    OneCorrectionCGStrategy E :=
  ⟨rfcClass fullMemory 1,rfcMethod_consistent fullMemory (fun _ hk => hk) 1,rfcMethod_oneCorrection fullMemory⟩

/-- The genuine worst normalized finite-output risk over all original admissible physical scenarios.
Use: an extended nonnegative supremum includes arbitrary source methods with unbounded risk without imposing boundedness.
Article: main_krylov, thm:C, sup_{Ξ∈S} ρ_M(Ξ). -/
def worstOutputRatio (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ) : ENNReal :=
  ⨆ S : {S : Scenario n // S.Admissible N A r ω w τ}, ENNReal.ofReal (S.val.outputRatio m g N)

/-- The actual original unknown-base minimax risk over the genuine full one-correction source information class.
Use: this is the source infimum of genuine physical scenario suprema, not an assumed first-variation price.
Article: main_krylov, thm:C, inf_M sup_{Ξ∈S} ρ_M(Ξ). -/
def oneCorrectionMinimax (A : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ) : ENNReal :=
  ⨅ M : OneCorrectionCGStrategy (EuclideanSpace ℝ (Fin n)),
    worstOutputRatio M.method.policy A g N r ω w τ

/-- An actual uniform physical output bound controls the genuine worst-scenario source supremum.
Use: convert the proved RFC all-scenario estimate to its true supremal risk.
Article: main_krylov, thm:C, physical-source supremum upper comparison.
Proof: every actual admissible source scenario obeys the same real bound;
monotonicity of the nonnegative embedding preserves that inequality.
-/
theorem worstOutputRatio_le (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (r : ℝ) (ω : ℕ → ℝ) (w τ K : ℝ)
    (h : ∀ S : Scenario n, S.Admissible N A r ω w τ → S.outputRatio m g N≤K) :
    worstOutputRatio m A g N r ω w τ≤ENNReal.ofReal K := by
  exact iSup_le fun S => ENNReal.ofReal_le_ofReal (h S.val S.property)

/-- A genuine admissible signed pair bounds the actual worst source risk below by its real maximum.
Use: the explicit physical lower witnesses feed the true source supremum directly.
Article: main_krylov, thm:C, physical-source two-scenario supremum lower comparison.
Proof: both genuinely admissible scenarios occur in the actual supremum;
their real maximum is preserved by the monotone nonnegative embedding.
-/
theorem max_outputRatio_le_worst (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ)
    (S T : Scenario n) (hS : S.Admissible N A r ω w τ) (hT : T.Admissible N A r ω w τ) :
    ENNReal.ofReal (max (S.outputRatio m g N) (T.outputRatio m g N))≤worstOutputRatio m A g N r ω w τ := by
  unfold worstOutputRatio
  rw [ENNReal.ofReal_max]
  apply max_le
  · exact le_iSup_of_le (⟨S,hS⟩ : {R : Scenario n // R.Admissible N A r ω w τ}) le_rfl
  · exact le_iSup_of_le (⟨T,hT⟩ : {R : Scenario n // R.Admissible N A r ω w τ}) le_rfl

/-- Every source method's genuine worst physical normalized risk has the sharp quadratic lower coefficient with a uniform cubic loss.
Use: no regularity of the competing policy or boundedness of its risk is assumed.
Article: main_krylov, thm:C, actual method-uniform source-supremum lower bound.
Proof: the explicit original admissible signed scenarios force the genuine
own-base normalized lower radius. Their actual maximum belongs to the
physical source supremum, including zero profiles and unbounded methods.
-/
theorem worstOutputRatio_sharp_lower {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1) :
    ∃ ε C : ℝ, 0<ε ∧ 0<C ∧
      ∀ (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))), CGConsistent m → OneCorrectionMethod m →
      ∀ (ω : ℕ → ℝ) (w τ r : ℝ), (∀ i∈range N, 0≤ω i) → 0≤w → 0≤τ →
      (∑ i∈range N, ω i)+w≤(1/2 : ℝ) → (∑ i∈range N, ω i)≤r → (∑ i∈range N, ω i)<ε →
      ENNReal.ofReal (sharpConstant (∑ i∈range N, ω i) w-C*((∑ i∈range N, ω i)+w)^3)≤
        worstOutputRatio m A g N r ω w τ := by
  -- The same true signed lower pair serves the actual source supremum for every policy.
  obtain ⟨ε,C,hε,hC,hpair⟩ := admissible_planar_normalized_lower A hA g hN hcount
  refine ⟨ε,C,hε,hC,?_⟩
  intro m hm h1 ω w τ r hω hw hτ hs hWr hWε
  obtain ⟨hplus,hminus,_,_,hlower⟩ := hpair m hm h1 ω w τ r hω hw hτ hs hWr hWε
  exact (ENNReal.ofReal_le_ofReal hlower).trans (max_outputRatio_le_worst m A g N r ω w τ _ _ hplus hminus)


end
end krylov.Information
