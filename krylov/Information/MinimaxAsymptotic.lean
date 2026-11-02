import krylov.Information.MinimaxBound

/-!
Article: main_krylov, thm:C, the actual attained minimax asymptotic.
Use: the literal source O(ω³) assertion holds for the true unknown-base
infimum–supremum and RFC's genuine worst physical-scenario normalized risk.
Source: the proved common all-profile real cubic estimates and the standard
filter definition of Big-O, including degenerate shrinking budget profiles.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant
  krylov.Correction krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
/-- The genuine unknown-base minimax value and actual RFC worst physical-source risk have the printed third-order remainder along every shrinking admissible budget family.
Use: the quantitative common constants give the literal source asymptotic, with the largest budget as the small parameter.
Article: main_krylov, thm:C, inf_M sup_Ξ ρ_M=K+O(ω³), attained asymptotically by RFC.
Proof: choose the same real all-profile cubic tube once for each fixed
positive source radius. Every shrinking admissible family eventually enters
that tube. Its actual real minimax and RFC supremal risks obey the same
uniform cubic absolute-error bound, which is exactly the two Big-O claims.
-/
theorem oneCorrection_minimax_asymptotic {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1) :
    ∃ r₀ : ℝ, 0<r₀ ∧ ∀ r : ℝ, 0<r → r≤r₀ →
      ∀ (T : Type*) (l : Filter T) (ω : T → ℕ → ℝ) (w μ : T → ℝ),
        Tendsto μ l (𝓝 0) →
        (∀ᶠ t in l, 0≤μ t ∧ (∀ i<N, 0≤ω t i ∧ ω t i≤μ t) ∧ 0≤w t ∧ w t≤μ t) →
        (fun t => (oneCorrectionMinimax A g N r (ω t) (w t) (μ t)).toReal-
          sharpConstant (∑ i∈range N, ω t i) (w t)) =O[l] (fun t => (μ t)^3) ∧
        (fun t => (worstOutputRatio (rfcMethod fullMemory 1) A g N r (ω t) (w t) (μ t)).toReal-
          sharpConstant (∑ i∈range N, ω t i) (w t)) =O[l] (fun t => (μ t)^3) := by
  -- The true quantitative constants are chosen before the family and its approach to zero.
  obtain ⟨r₀,hr₀,hcubic⟩ := oneCorrection_minimax_cubic A hA g hN hcount
  refine ⟨r₀,hr₀,?_⟩
  intro r hr hrr
  obtain ⟨δ,C,hδ,_,hbound⟩ := hcubic r hr hrr
  intro T l ω w μ hμ hprofile
  have hsmall : ∀ᶠ t in l, μ t≤δ := ((tendsto_order.mp hμ).2 δ hδ).mono fun _ ht => ht.le
  have hest : ∀ᶠ t in l,
      ‖(oneCorrectionMinimax A g N r (ω t) (w t) (μ t)).toReal-sharpConstant (∑ i∈range N, ω t i) (w t)‖≤C*‖(μ t)^3‖ ∧
      ‖(worstOutputRatio (rfcMethod fullMemory 1) A g N r (ω t) (w t) (μ t)).toReal-
        sharpConstant (∑ i∈range N, ω t i) (w t)‖≤C*‖(μ t)^3‖ := by
    filter_upwards [hsmall,hprofile] with t ht hp
    have hb := hbound (ω t) (w t) (μ t) hp.1 ht hp.2.1 hp.2.2.1 hp.2.2.2
    simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hp.1 3)] using hb.2.2
  exact ⟨isBigO_iff.mpr ⟨C,hest.mono fun _ ht => ht.1⟩,
    isBigO_iff.mpr ⟨C,hest.mono fun _ ht => ht.2⟩⟩

end
end krylov.Information
