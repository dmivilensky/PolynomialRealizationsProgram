import krylov.Information.FrobeniusUpper
import krylov.Information.FrobeniusLower
import krylov.Information.MinimaxBound

/-!
Article: main_krylov, thm:C2(a), actual physical Frobenius minimax value.
Use: the true source minimax and actual RFC supremum have sharp coefficient
K/√2, both with unknown bases and already with the base exactly known.
Source: the genuine fixed-base admissible signed lower pair, full physical
Frobenius RFC upper and actual source information class of the minimax theorem.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant
  krylov.Correction krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine worst normalized risk on the original physical Frobenius class, optionally restricting to the exactly known base.
Use: one source supremum covers both the unknown-base and known-base norm variant without changing the actual method executor.
Article: main_krylov, thm:C2(a), sup_Ξ ρ_M with independent Frobenius budgets. -/
def frobeniusWorstOutputRatio (known : Bool) (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ) : ENNReal :=
  ⨆ S : {S : Scenario n // S.FrobeniusAdmissible N A r ω w τ ∧ (known=true → S.base=A)},
    ENNReal.ofReal (S.val.outputRatio m g N)

/-- The actual infimum of genuine physical Frobenius scenario suprema over the full CG-consistent one-correction source information class.
Use: compare the same actual full class under either unknown or exactly known bases.
Article: main_krylov, thm:C2(a), genuine Frobenius minimax risk. -/
def frobeniusMinimax (known : Bool) (A : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ) : ENNReal :=
  ⨅ M : OneCorrectionCGStrategy (EuclideanSpace ℝ (Fin n)),
    frobeniusWorstOutputRatio known M.method.policy A g N r ω w τ

/-- A genuine known-base admissible signed pair gives the same sharp lower bound for both actual physical Frobenius source suprema.
Use: the known-base obstruction is an actual subset of the unknown-base source class.
Article: main_krylov, thm:C2(a), true worst-scenario Frobenius lower bound.
Proof: both explicit signed physical scenarios satisfy all original budgets
and have base exactly A. Their genuine output maximum forces the proved
normalized K/√2 radius and belongs to either true source supremum.
-/
theorem frobeniusWorst_sharp_lower {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1) (known : Bool)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m) (h1 : OneCorrectionMethod m)
    (ω : ℕ → ℝ) (w τ r : ℝ) (hω : ∀ i<N, 0≤ω i) (hw : 0≤w) (hτ : 0≤τ) (hr : 0≤r)
    (hs : (∑ i∈range N, ω i)+w≤(1/2 : ℝ)) :
    ENNReal.ofReal (sharpConstant (∑ i∈range N, ω i) w/Real.sqrt 2-2*((∑ i∈range N, ω i)+w)^3)≤
      frobeniusWorstOutputRatio known m A g N r ω w τ := by
  -- The same genuinely admissible known-base witnesses occur in either true physical scenario supremum.
  obtain ⟨hBp,hBm,hp,hn,hl⟩ := admissible_frobenius_normalized_lower A hA g hN hcount m hm h1 ω w τ r hω hw hτ hr hs
  apply (ENNReal.ofReal_le_ofReal hl).trans
  rw [ENNReal.ofReal_max]
  unfold frobeniusWorstOutputRatio
  apply max_le
  · exact le_iSup_of_le (⟨_,hp,fun _ => hBp⟩ : {S : Scenario (N+1) //
      S.FrobeniusAdmissible N A r ω w τ ∧ (known=true → S.base=A)}) le_rfl
  · exact le_iSup_of_le (⟨_,hn,fun _ => hBm⟩ : {S : Scenario (N+1) //
      S.FrobeniusAdmissible N A r ω w τ ∧ (known=true → S.base=A)}) le_rfl

end
end krylov.Information
