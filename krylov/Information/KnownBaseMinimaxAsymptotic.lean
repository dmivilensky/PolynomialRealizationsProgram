import krylov.Information.KnownBaseMinimaxBound

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

/-- The true known-base minimax and the genuine finite-history informed-policy source supremum have the literal sharp cubic asymptotic along every shrinking nonnegative budget family.
Use: the source statement is about actual physical output risks and an actual attaining policy, with no selector regularity assumption.
Article: main_krylov, thm:C2(c), sharp informed minimax asymptotic and midpoint attainment.
Proof: the genuine uniform real cubic tube is chosen before the family.
Every shrinking nonnegative budget eventually enters that tube. Its two
actual-risk absolute-error estimates are precisely the two Big-O claims. -/
theorem knownBase_minimax_asymptotic
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N) (hcount : referenceAtomCount A hA g=N+1)
    (T : Type*) (l : Filter T) (ω : T → ℝ) (htend : Tendsto ω l (𝓝 0))
    (hω : ∀ᶠ t in l, 0≤ω t) :
    (fun t => (knownBaseMinimax A g N (ω t)).toReal-(2/(3*Real.sqrt 3))*(ω t)^2) =O[l] (fun t => (ω t)^3) ∧
    (fun t => (knownBaseWorstOutputRatio (knownBaseMidpointMethod A g (ω t)) A g N (ω t)).toReal-
      (2/(3*Real.sqrt 3))*(ω t)^2) =O[l] (fun t => (ω t)^3) := by
  -- The genuine common cubic constants precede the whole shrinking budget family.
  obtain ⟨δ,C,hδ,_,hbound⟩ := knownBase_minimax_cubic A hA g hN hcount
  have hsmall : ∀ᶠ t in l, ω t≤δ := ((tendsto_order.mp htend).2 δ hδ).mono fun _ ht => ht.le
  have hest : ∀ᶠ t in l,
      ‖(knownBaseMinimax A g N (ω t)).toReal-(2/(3*Real.sqrt 3))*(ω t)^2‖≤C*‖(ω t)^3‖ ∧
      ‖(knownBaseWorstOutputRatio (knownBaseMidpointMethod A g (ω t)) A g N (ω t)).toReal-
        (2/(3*Real.sqrt 3))*(ω t)^2‖≤C*‖(ω t)^3‖ := by
    filter_upwards [hsmall,hω] with t ht hp
    have hb := hbound (ω t) hp ht
    simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hp 3)] using hb.2.2
  exact ⟨isBigO_iff.mpr ⟨C,hest.mono fun _ ht => ht.1⟩,
    isBigO_iff.mpr ⟨C,hest.mono fun _ ht => ht.2⟩⟩

end
end krylov.Information
