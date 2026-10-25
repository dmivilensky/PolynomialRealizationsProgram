import polyak.FiniteHorizon.Banded
import polyak.FiniteHorizon.FactorizationGap
import polyak.FiniteHorizon.FactorizationOneAtom

/-!
Article: Appendix C, actual boundary certificates in Lemma prices.
Use: true branch factors are converted to dense-window data at width seven.
The source symbol identities below are exact algebraic identifications of the
quadratic coefficients, not assumptions of strictness or spectral factorability.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Energy Boundary Spectral Filter
open scoped BigOperators Topology

/-- Concrete coefficient data sufficient for the actual local decomposition. -/
structure BandedData7 (C : WindowMatrix7) (d : ℕ → ℝ) (ε : ℝ) where
  factors : GramFactors 7 (fun θ => -coefficientSymbol C θ-ε)
  charge : ∑ a ∈ Finset.range 8, d a=0

def bandedDataOfFactors7 {C : WindowMatrix7} {d : ℕ → ℝ} {ε : ℝ}
    {F : FrequencyCircle → ℝ} (cert : SquareFactorization 7 F)
    (hF : ∀ θ, F θ= -coefficientSymbol C θ-ε)
    (hd : ∑ a ∈ Finset.range 8, d a=0) : BandedData7 C d ε :=
  ⟨(cert.congr hF).toGram,hd⟩

/-- The source offset is −1, and its strict diagonal is the original time j. -/
def BandedData7.primitive {C : WindowMatrix7} {d : ℕ → ℝ} {ε : ℝ}
    (data : BandedData7 C d ε) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : ℤ → E) (h : ℤ → ℝ) (j : ℤ) : ℝ :=
  bandedPrimitive7 C d data.factors 1 (-1) f h j

/-- Exact inequality used to build the actual positive prices above the rate. -/
theorem BandedData7.step {C : WindowMatrix7} {d : ℕ → ℝ} {ε : ℝ}
    (data : BandedData7 C d ε) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : ℤ → E) (h : ℤ → ℝ) (j : ℤ)
    (hB : 0≤bandedFunctional7 C d f h (j-1)) :
    ε*‖f j‖^2≤data.primitive f h (j+1)-data.primitive f h j := by
  have he:=banded_telescoping_offset7 C d data.factors 1 (-1) data.charge f h j
  have hs : 0≤∑ k, ‖∑ a : Fin 8, data.factors.coefficient k a • f (j+(-1 : ℤ)+(a : ℤ))‖^2 := by
    positivity
  norm_num only [Fin.isValue,Fin.val_one,Nat.cast_one,add_neg_cancel_right] at he
  rw [show j+(-1 : ℤ)+1=j by ring] at he
  change bandedFunctional7 C d f h (j-1)= _ at he
  change ε*‖f j‖^2≤bandedPrimitive7 C d data.factors 1 (-1) f h (j+1)-
    bandedPrimitive7 C d data.factors 1 (-1) f h j
  linarith

/-- The full P₂ arc supplies actual banded data, with the proved branch factors. -/
def p2BandedData7 {z v γ ε : ℝ} (hz : z∈P2.parameterInterval)
    (C : WindowMatrix7) (d : ℕ → ℝ)
    (hC : ∀ θ, coefficientSymbol C θ=
      dualSymbol (P2.dualWeights z hz) v (P2.G z) (frequencyCosine θ)+2*γ*g v (frequencyCosine θ))
    (hd : ∑ a ∈ Finset.range 8, d a=0)
    (huv : P2.u z≤v) (hγ : 0≤γ) (hsmall : 4*γ≤v^2-P2.u z^2)
    (hε : ε≤(P2.G z-1)*(v^2-P2.u z^2)+2*γ*v^2) : BandedData7 C d ε :=
  bandedDataOfFactors7 (p2StrictGapFactorization hz huv hγ hsmall hε)
    (fun θ => by rw [hC]; ring) hd

/-- The whole exact spiral arc supplies actual banded data. -/
def spiralBandedData7 {G v γ ε : ℝ} (hG : G1≤G) (hGW : G≤GW)
    (C : WindowMatrix7) (d : ℕ → ℝ)
    (hC : ∀ θ, coefficientSymbol C θ=
      dualSymbol (weights23 (spiralWeight G)
        (spiralWeight_mem (by linarith [G1_bounds.1]) hGW).1
        (spiralWeight_mem (by linarith [G1_bounds.1]) hGW).2)
        v G (frequencyCosine θ)+2*γ*g v (frequencyCosine θ))
    (hd : ∑ a ∈ Finset.range 8, d a=0)
    (huv : 1-1/(2*G)≤v) (hγ : 0≤γ) (hsmall : 4*γ≤v^2-(1-1/(2*G))^2)
    (hε : ε≤(G-1)*(v^2-(1-1/(2*G))^2)+2*γ*v^2) : BandedData7 C d ε :=
  bandedDataOfFactors7 (spiralStrictGapFactorization hG hGW huv hγ hsmall hε)
    (fun θ => by rw [hC]; ring) hd

theorem selectedSymbol_eq_oneAtom (u G c : ℝ) :
    dualSymbol (P5.weights235 0 1 (by norm_num) (by norm_num) (by norm_num)) u G c=
      dualSymbol P1.weights u G c := by
  rw [P5.dualSymbol_weights235]
  simp [dualSymbol,P1.weights]

/-- Actual one-atom source factors, padded to the same common width. -/
def oneAtomSelectedFactorization {z u a : ℝ} (hz : 0<z) (hz1 : z≤1)
    (h0 : P1.quartic z u a=0) (h1 : P1.quarticDerivative z u a=0)
    (hq : |P1.residualLinear z u a|≤P1.residualConstant z u a) :
    SquareFactorization 7 (fun θ =>
      -dualSymbol (P5.weights235 0 1 (by norm_num) (by norm_num) (by norm_num))
        u (1/z) (frequencyCosine θ)) :=
  ((oneAtomSymbolFactorization hz hz1 h0 h1 hq).widen (by norm_num)).congr
    (fun θ => by rw [selectedSymbol_eq_oneAtom])

/-- P₁ banded data use the true contact equations and true quadratic residual
reserve, so no factorization certificate is left as a hypothesis. -/
def oneAtomBandedData7 {z u a v γ ε : ℝ} (hz : 0<z) (hz1 : z≤1)
    (h0 : P1.quartic z u a=0) (h1 : P1.quarticDerivative z u a=0)
    (hq : |P1.residualLinear z u a|≤P1.residualConstant z u a)
    (C : WindowMatrix7) (d : ℕ → ℝ)
    (hC : ∀ θ, coefficientSymbol C θ=dualSymbol P1.weights v (1/z) (frequencyCosine θ)+
      2*γ*g v (frequencyCosine θ))
    (hd : ∑ a ∈ Finset.range 8, d a=0) (hu : 0≤u) (huv : u≤v) (hγ : 0≤γ)
    (hsmall : 4*γ≤v^2-u^2) (hε : ε≤(1/z-1)*(v^2-u^2)+2*γ*v^2) : BandedData7 C d ε := by
  have hG : 1≤1/z:=(le_div_iff₀ hz).mpr (by linarith)
  have hf:=selectedStrictGapFactorization hG (by norm_num : (0 : ℝ)≤0)
    (by norm_num : (0 : ℝ)≤1) (by norm_num : (0 : ℝ)≤1-0-1)
    (oneAtomSelectedFactorization hz hz1 h0 h1 hq) hu huv hγ hsmall hε
  exact bandedDataOfFactors7 hf (fun θ => by rw [selectedSymbol_eq_oneAtom,hC]; ring) hd

/-- Actual critical P₅ data follow on the proved common source neighborhood. -/
theorem eventually_p5BandedData7 :
    ∀ᶠ h in 𝓝 (0 : ℝ), 0≤h →
      ∃ h₂ : 0≤P5.localBranch h 5, ∃ h₃ : 0≤P5.localBranch h 6,
      ∃ h₅ : 0≤1-P5.localBranch h 5-P5.localBranch h 6,
      ∀ (C : WindowMatrix7) (d : ℕ → ℝ) (v γ ε : ℝ),
        (∀ θ, coefficientSymbol C θ=dualSymbol (P5.weights235 _ _ h₂ h₃ h₅)
          v (1+h) (frequencyCosine θ)+2*γ*g v (frequencyCosine θ)) →
        (∑ a ∈ Finset.range 8, d a=0) →
        1/2+h*P5.localBranch h 0≤v → 0≤γ →
        4*γ≤v^2-(1/2+h*P5.localBranch h 0)^2 →
        ε≤h*(v^2-(1/2+h*P5.localBranch h 0)^2)+2*γ*v^2 →
        Nonempty (BandedData7 C d ε) := by
  filter_upwards [eventually_p5StrictGapFactorization] with h hf hh
  obtain ⟨h₂,h₃,h₅,hf⟩:=hf hh
  refine ⟨h₂,h₃,h₅,?_⟩
  intro C d v γ ε hC hd huv hγ hs hε
  obtain ⟨cert⟩:=hf v γ ε huv hγ hs hε
  exact ⟨bandedDataOfFactors7 cert (fun θ => by rw [hC]; ring) hd⟩

end polyak.FiniteHorizon
