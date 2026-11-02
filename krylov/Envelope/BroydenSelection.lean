import krylov.Methods.BroydenSmoothClass
import krylov.Envelope.NamedFinalAttainers
import krylov.Envelope.CorrectionFreeExcess

set_option autoImplicit false
/-!
Article: main_krylov, cor:lm and s3:cor:qn, genuine convex Broyden selection consequences.
Use: specialize actual final-correction minimax attainment and true strict correction-free excess to the genuine smooth positive-scalar-initialized convex Broyden source family.
Source: complete actual primitive smooth convex Broyden membership and the proved genuine class-quantified selection and excess theorems.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods Matrix
open scoped Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- Every actual smooth inverse convex Broyden method followed by one genuine final latest-information correction attains the true selection value.
Use: Every actual smooth inverse convex Broyden method followed by one genuine final latest-information correction attains the true selection value.
Article: main_krylov, cor:lm and s3:cor:qn, genuine convex Broyden selection consequences.
Proof: Apply the actual generic final-wrapper theorem to the genuine primitive smooth correction-free Broyden member. -/
theorem broyden_final_correction_attains (c : ℝ) (hc : 0<c) (θ : ℕ → ℝ) (hθ : ∀ i,0≤θ i ∧ θ i≤1)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    OneCorrectionMethod (finalizedSmoothClass (smoothBroydenClass (E := EuclideanSpace ℝ (Fin n)) c hc θ hθ) N).policy ∧
      worstTransverse (finalizedSmoothClass (smoothBroydenClass (E := EuclideanSpace ℝ (Fin n)) c hc θ hθ) N).policy base g N ω=
        selectionValue base g N ω :=
  named_final_correction_attains _ (smoothBroydenClass_correctionFree c hc θ hθ) base hb g N hN hcount ω

/-- Every actual positive-scalar-initialized inverse convex Broyden method has the printed genuine correction-free excess and strict separation for positive final budget.
Use: Every actual positive-scalar-initialized inverse convex Broyden method has the printed genuine correction-free excess and strict separation for positive final budget.
Article: main_krylov, cor:lm and s3:cor:qn, genuine convex Broyden selection consequences.
Proof: Specialize the genuine class-quantified excess theorem to its true primitive smooth Broyden implementation. -/
theorem broyden_excess (c : ℝ) (hc : 0<c) (θ : ℕ → ℝ) (hθ : ∀ i,0≤θ i ∧ θ i≤1)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    Real.sqrt ((selectionValue base g N ω)^2+cgEnergy base g (N-1)*(ω ⟨N-2,by omega⟩ : ℝ)^2)≤
      worstTransverse (smoothBroydenClass (E := EuclideanSpace ℝ (Fin n)) c hc θ hθ).policy base g N ω ∧
    (0<ω ⟨N-2,by omega⟩ → selectionValue base g N ω<
      worstTransverse (smoothBroydenClass (E := EuclideanSpace ℝ (Fin n)) c hc θ hθ).policy base g N ω) :=
  ⟨correctionFree_excess_lower _ (smoothBroydenClass_correctionFree c hc θ hθ) base hb g N hN hcount ω,
    correctionFree_strict_excess _ (smoothBroydenClass_correctionFree c hc θ hθ) base hb g N hN hcount ω⟩
end
end krylov.Envelope
