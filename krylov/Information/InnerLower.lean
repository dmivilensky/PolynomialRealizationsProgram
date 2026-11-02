import krylov.Information.InnerScenario
import krylov.Information.InnerSharpScalar

/-!
Article: main_krylov, s4:cor-Q, actual sharp inner-subclass source witnesses.
Use: construct two genuine original pre-quadratic inner scenarios forcing
the same sharp all-profile coefficient for every original source method.
Source: proved original signed normalized lower witnesses, exact inner
budget scaling, actual prefix probes and degree-two sharp homogeneity.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
variable {N : ℕ}

/-- Every original small nonnegative profile has actual pre-quadratic inner-class signed scenarios forcing the printed sharp coefficient with one uniform cubic loss for every genuine one-correction CG-consistent method.
Use: verify sharp attainment inside the actual original inner subclass, including zero and degenerate profiles.
Article: main_krylov, s4:cor-Q, sharp attainment on Q ∩ S^natural.
Proof: scale every actual increment and terminal budget by precisely 1−4nW. The original explicit normalized signed lower construction fits the reduced physical base radius. Its real primitive constraints imply every inner-class margin, and its actual terminal-fibre probes are pre-quadratic. Exact degree-two homogeneity and the proved cubic slack-loss bound restore the original sharp coefficient. -/
theorem inner_preQuadratic_normalized_lower
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N) (hcount : referenceAtomCount A hA g=N+1) :
    ∃ ε C : ℝ, 0<ε ∧ 0<C ∧
      ∀ (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))), CGConsistent m → OneCorrectionMethod m →
      ∀ (ω : ℕ → ℝ) (w τ r : ℝ), (∀ i<N, 0≤ω i) → 0≤w → 0≤τ → 0≤r →
        (∑ i∈range N, ω i)+w≤(1/2 : ℝ) →
        (5+4*r)*(∑ i∈range N, ω i)≤r → (∑ i∈range N, ω i)<ε →
        4*((N : ℝ)+1)*(∑ i∈range N, ω i)≤1 →
      ∃ S T : Scenario (N+1), S.NaturalInner A r ω w τ ∧ T.NaturalInner A r ω w τ ∧
        S.PreQuadratic (cgOperator A) g N ∧ T.PreQuadratic (cgOperator A) g N ∧
        sharpConstant (∑ i∈range N, ω i) w-C*((∑ i∈range N, ω i)+w)^3≤
          max (S.outputRatio m g N) (T.outputRatio m g N) := by
  -- Start with the genuine all-profile normalized signed witnesses, then impose only the original inner slack.
  obtain ⟨ε,C,hε,hC,hlower⟩ := admissible_planar_normalized_lower A hA g hN hcount
  refine ⟨ε,C+8*((N : ℝ)+1),hε,by positivity,?_⟩
  intro m hm h1 ω w τ r hω hw hτ hr hs hmargin hWε hslack
  let W := ∑ i∈range N, ω i
  let θ := 1-4*((N : ℝ)+1)*W
  let ωs := fun i => θ*ω i
  let ws := θ*w
  have hW : 0≤W := sum_nonneg fun i hi => hω i (mem_range.mp hi)
  have hθ : 0≤θ := by dsimp only [θ]; linarith
  have hθ₁ : θ≤1 := by dsimp only [θ]; nlinarith
  have hsum : (∑ i∈range N, ωs i)=θ*W := by dsimp only [ωs,W]; rw [← mul_sum]
  have hωs (i : ℕ) (hi : i∈range N) : 0≤ωs i := mul_nonneg hθ (hω i (mem_range.mp hi))
  have hws : 0≤ws := mul_nonneg hθ hw
  have hs' : (∑ i∈range N, ωs i)+ws≤(1/2 : ℝ) := by
    rw [hsum]
    calc
      _ = θ*(W+w) := by dsimp only [ws]; ring
      _ ≤ W+w := (mul_le_mul_of_nonneg_right hθ₁ (add_nonneg hW hw)).trans_eq (one_mul _)
      _ ≤ _ := hs
  have hr' : (∑ i∈range N, ωs i)≤r-4*(1+r)*W := by rw [hsum]; nlinarith [mul_le_mul_of_nonneg_right hθ₁ hW]
  have hε' : (∑ i∈range N, ωs i)<ε := by
    rw [hsum]
    exact ((mul_le_mul_of_nonneg_right hθ₁ hW).trans_eq (one_mul _)).trans_lt hWε
  have hb := hlower m hm h1 ωs ws τ (r-4*(1+r)*W) hωs hws hτ hs' hr' hε'
  let a := maximizingCross (∑ i∈range N, ωs i) ws
  let γ := maximizingComplement (∑ i∈range N, ωs i) ws
  let S := fun σ => (planarLowerScenario (canonicalCGUnitStep A g 0) (canonicalCGUnitStep A g N)
    ωs ws N a γ σ).inPhysical (metricRoot A)⁻¹
  have hSp : (S 1).Admissible N A (r-4*(1+r)*W) ωs ws τ := hb.1
  have hSm : (S (-1)).Admissible N A (r-4*(1+r)*W) ωs ws τ := hb.2.1
  have hlower' : sharpConstant (θ*W) (θ*w)-C*(θ*(W+w))^3≤
      max ((S 1).outputRatio m g N) ((S (-1)).outputRatio m g N) := by
    have hh := hb.2.2.2.2
    change sharpConstant (∑ i∈range N, ωs i) ws-C*((∑ i∈range N, ωs i)+ws)^3≤
      max ((S 1).outputRatio m g N) ((S (-1)).outputRatio m g N) at hh
    rw [hsum] at hh
    simpa only [ws,← mul_add] using hh
  refine ⟨S 1,S (-1),?_,?_,?_,?_,?_⟩
  · exact (S 1).naturalInner_of_scaled_admissible A r w τ ω hr hw hω hSp
  · exact (S (-1)).naturalInner_of_scaled_admissible A r w τ ω hr hw hω hSm
  · exact physical_planarLowerScenario_preQuadratic A hA g hN hcount ωs ws a γ 1
  · exact physical_planarLowerScenario_preQuadratic A hA g hN hcount ωs ws a γ (-1)
  · exact inner_sharp_cubic_loss ((N : ℝ)+1) W w C _ (by positivity) hW hw hC.le hslack hlower'

end
end krylov.Information
