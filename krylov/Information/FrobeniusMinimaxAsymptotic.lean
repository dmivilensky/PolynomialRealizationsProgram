import krylov.Information.FrobeniusMinimaxBound

/-!
Article: main_krylov, thm:C2(a), attained actual Frobenius minimax asymptotic.
Use: every shrinking genuine source profile has actual minimax and RFC
risks equal to K/√2 up to the literal third-order remainder, in both
unknown-base and exactly-known-base physical scenario classes.
Source: the proved true common all-profile finite real cubic bound.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant
  krylov.Correction krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
/-- Genuine unknown-base and known-base Frobenius minimax risks, and actual RFC's physical-source supremum, have the literal sharp third-order asymptotic along every shrinking profile family.
Use: the same true source coefficient K/√2 applies in both knowledge regimes, with all constants fixed before every budget profile.
Article: main_krylov, thm:C2(a), actual norm-sensitive minimax asymptotic attained by RFC.
Proof: both genuine real source risks obey the common all-profile cubic
estimate. Any shrinking nonnegative budget family eventually enters that
actual tube, and its two absolute-error bounds are exactly the Big-O claims.
-/
theorem frobenius_minimax_asymptotic {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1) :
    ∃ r₀ : ℝ, 0<r₀ ∧ ∀ r : ℝ, 0≤r → r≤r₀ → ∀ known : Bool,
      ∀ (T : Type*) (l : Filter T) (ω : T → ℕ → ℝ) (w μ : T → ℝ),
        Tendsto μ l (𝓝 0) →
        (∀ᶠ t in l, 0≤μ t ∧ (∀ i<N, 0≤ω t i ∧ ω t i≤μ t) ∧ 0≤w t ∧ w t≤μ t) →
        (fun t => (frobeniusMinimax known A g N r (ω t) (w t) (μ t)).toReal-
          sharpConstant (∑ i∈range N, ω t i) (w t)/Real.sqrt 2) =O[l] (fun t => (μ t)^3) ∧
        (fun t => (frobeniusWorstOutputRatio known (rfcMethod fullMemory 1) A g N r (ω t) (w t) (μ t)).toReal-
          sharpConstant (∑ i∈range N, ω t i) (w t)/Real.sqrt 2) =O[l] (fun t => (μ t)^3) := by
  -- The genuine tube and constants precede both knowledge regimes and all shrinking families.
  obtain ⟨r₀,δ,C,hr₀,hδ,_,hbound⟩ := frobenius_minimax_cubic A hA g hN hcount
  refine ⟨r₀,hr₀,?_⟩
  intro r hr hrr known T l ω w μ hμ hprofile
  have hsmall : ∀ᶠ t in l, μ t≤δ := ((tendsto_order.mp hμ).2 δ hδ).mono fun _ ht => ht.le
  have hest : ∀ᶠ t in l,
      ‖(frobeniusMinimax known A g N r (ω t) (w t) (μ t)).toReal-
        sharpConstant (∑ i∈range N, ω t i) (w t)/Real.sqrt 2‖≤C*‖(μ t)^3‖ ∧
      ‖(frobeniusWorstOutputRatio known (rfcMethod fullMemory 1) A g N r (ω t) (w t) (μ t)).toReal-
        sharpConstant (∑ i∈range N, ω t i) (w t)/Real.sqrt 2‖≤C*‖(μ t)^3‖ := by
    filter_upwards [hsmall,hprofile] with t ht hp
    have hb := hbound r hr hrr known (ω t) (w t) (μ t) hp.1 ht hp.2.1 hp.2.2.1 hp.2.2.2
    simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hp.1 3)] using hb.2.2
  exact ⟨isBigO_iff.mpr ⟨C,hest.mono fun _ ht => ht.1⟩,
    isBigO_iff.mpr ⟨C,hest.mono fun _ ht => ht.2⟩⟩

end
end krylov.Information
