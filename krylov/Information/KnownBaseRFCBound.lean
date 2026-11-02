import krylov.Information.KnownBaseRFCLower

/-!
Article: main_krylov, thm:C2(c), ordinary RFC worst known-base risk.
Use: a genuine admissible physical single-increment witness gives the
sharp one-half coefficient for actual RFC, with the matching full-source
upper bound, derived finite supremum and one common cubic loss.
Source: actual planar reflection budgets, genuine joint source cubic tube,
exact physical output reconstruction and the proved all-source RFC upper.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant krylov.Envelope
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability krylov.Variation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The genuine worst physical known-base source risk of ordinary RFC is finite and differs from ω₀²/2 by at most one common cubic amount.
Use: complete the stated strict leading-constant comparison between ordinary RFC and the informed midpoint method.
Article: main_krylov, thm:C2(c), actual ordinary RFC sharp worst-case cubic estimate.
Proof: the concrete genuine physical witness gives the common one-half
lower endpoint. The original full physical RFC upper applies to every
known-base scenario, and its exact one-increment sharp constant is ω₀²/2.
The actual supremum is finite under that upper bound; the proved real-risk
conversion gives the stated sharp-coefficient absolute error. -/
theorem knownBase_rfc_cubic (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N) (hcount : referenceAtomCount A hA g=N+1) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ ω : ℝ, 0≤ω → ω≤δ →
      knownBaseWorstOutputRatio (rfcMethod fullMemory 1) A g N ω≠⊤ ∧
      |(knownBaseWorstOutputRatio (rfcMethod fullMemory 1) A g N ω).toReal-ω^2/2|≤C*ω^3 := by
  -- Compare the same actual source supremum against both genuine uniform cubic endpoints.
  obtain ⟨δL,CL,hδL,hCL,hlower⟩ := knownBase_rfc_lower A hA g hN hcount
  obtain ⟨r₀,δU,CU,hr₀,hδU,hCU,hupper⟩ := admissible_rfc_sharp_upper A hA g hN hcount
  refine ⟨min δL δU,CL+CU,lt_min hδL hδU,add_pos hCL hCU,?_⟩
  intro ω hω hωδ
  have hpow := pow_nonneg hω 3
  have hl : ENNReal.ofReal (ω^2/2-(CL+CU)*ω^3)≤knownBaseWorstOutputRatio (rfcMethod fullMemory 1) A g N ω :=
    (ENNReal.ofReal_le_ofReal (by nlinarith)).trans (hlower ω hω (hωδ.trans (min_le_left _ _)))
  have hu : knownBaseWorstOutputRatio (rfcMethod fullMemory 1) A g N ω≤ENNReal.ofReal (ω^2/2+(CL+CU)*ω^3) := by
    unfold knownBaseWorstOutputRatio
    apply iSup_le
    intro S
    have ht := hupper 0 hr₀.le (firstBudget ω) 0 0 ω hω (hωδ.trans (min_le_right _ _))
      (fun i _ => by
        by_cases hi : i=0
        · simp only [firstBudget,ite_eq_left hi,le_refl]
        · simpa only [firstBudget,ite_eq_right hi] using hω) hω hω S.val S.property.1
    rw [firstBudget_sum ω hN,sharpConstant_no_terminal hω] at ht
    exact ENNReal.ofReal_le_ofReal (ht.trans (by nlinarith))
  exact realRisk_bracket (by positivity : 0≤ω^2/2) (by positivity : 0≤(CL+CU)*ω^3) hl hu


/-- The true ordinary RFC worst physical known-base risk has the literal one-half quadratic coefficient and cubic remainder along every shrinking nonnegative budget family.
Use: complete the printed actual worst-case asymptotic alongside the informed minimax comparison.
Article: main_krylov, thm:C2(c), sup_Ξ ρ_RFC=ω₀²/2+O(ω₀³).
Proof: every shrinking nonnegative budget eventually enters the genuine
uniform source tube. Its actual finite real supremum satisfies the proved
one-half cubic absolute-error bound, which is exactly the Big-O claim. -/
theorem knownBase_rfc_asymptotic (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N) (hcount : referenceAtomCount A hA g=N+1)
    (T : Type*) (l : Filter T) (ω : T → ℝ) (htend : Tendsto ω l (𝓝 0))
    (hω : ∀ᶠ t in l, 0≤ω t) :
    (fun t => (knownBaseWorstOutputRatio (rfcMethod fullMemory 1) A g N (ω t)).toReal-(ω t)^2/2)
      =O[l] (fun t => (ω t)^3) := by
  -- Use the actual common all-source tube before the shrinking family enters it.
  obtain ⟨δ,C,hδ,_,hbound⟩ := knownBase_rfc_cubic A hA g hN hcount
  have hsmall : ∀ᶠ t in l, ω t≤δ := ((tendsto_order.mp htend).2 δ hδ).mono fun _ ht => ht.le
  apply isBigO_iff.mpr ⟨C,?_⟩
  filter_upwards [hsmall,hω] with t ht hp
  simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hp 3)] using (hbound (ω t) hp ht).2

end
end krylov.Information
