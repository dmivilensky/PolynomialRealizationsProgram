import polyak.FiniteHorizon.FactorizationChebyshev
import polyak.FiniteHorizon.FactorizationSource

/-!
Article: Appendix C, the actual strict linear-gap symbols after increasing u.
Use: all additional nonnegative terms, the optional equal minimizer weights,
and the subtracted strict gap have explicit real causal factors of width seven.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Energy Boundary Spectral Filter
open scoped Topology

/-- Exact decomposition of the scalar gap after the equal minimizer correction. -/
def correctedGapFactorization {G u v γ ε : ℝ} (_hG : 1≤G)
    (_hu : 0≤u) (_huv : u≤v) (hγ : 0≤γ)
    (hsmall : 4*γ≤v^2-u^2)
    (hε : ε≤(G-1)*(v^2-u^2)+2*γ*v^2) :
    SquareFactorization 2 (fun θ =>
      (G-frequencyCosine θ)*(v^2-u^2)+2*γ*(frequencyCosine θ^2+v^2-1)-ε) := by
  have hA:=(linearSquareFactorization 1 (-1)).scale (r:=2*γ) (by positivity)
  have hB:=((one_sub_cosine.scale (r:=v^2-u^2-4*γ) (by linarith))).widen
    (show 1≤2 by omega)
  have hC:=(constantFactorization (a:=(G-1)*(v^2-u^2)+2*γ*v^2-ε)
    (by linarith)).widen (show 0≤2 by omega)
  exact ((hA.add hB).add hC).congr (fun θ => by ring)

/-- Increasing the actual twist preserves a real width-seven factorization,
including a positive strict gap and the critical-point minimizer correction. -/
def selectedStrictGapFactorization {G u v w₂ w₃ γ ε : ℝ} (hG : 1≤G)
    (h₂ : 0≤w₂) (h₃ : 0≤w₃) (h₅ : 0≤1-w₂-w₃)
    (cert : SquareFactorization 7 (fun θ =>
      -dualSymbol (P5.weights235 w₂ w₃ h₂ h₃ h₅) u G (frequencyCosine θ)))
    (hu : 0≤u) (huv : u≤v) (hγ : 0≤γ)
    (hsmall : 4*γ≤v^2-u^2)
    (hε : ε≤(G-1)*(v^2-u^2)+2*γ*v^2) :
    SquareFactorization 7 (fun θ =>
      -dualSymbol (P5.weights235 w₂ w₃ h₂ h₃ h₅) v G (frequencyCosine θ)-
        2*γ*g v (frequencyCosine θ)-ε) := by
  have hd : 0≤v^2-u^2:=by nlinarith
  have ha:=(((gapFactorization hG).mul
    (selectedAlphaReserveFactorization hG h₂ h₃ h₅)).scale hd).widen (show 5≤7 by omega)
  have hb:=(((gapFactorization hG).mul (sineSquareFactorization.mul
    (selectedBetaFactorization hG h₂ h₃ h₅))).scale
    (r:=2*(v-u)) (by linarith)).widen (show 6≤7 by omega)
  have hm:=(correctedGapFactorization hG hu huv hγ hsmall hε).widen (show 2≤7 by omega)
  exact (((cert.add ha).add hb).add hm).congr (fun θ => by
    rw [selected_symbol_factor hG u w₂ w₃ h₂ h₃ h₅,
      selected_symbol_factor hG v w₂ w₃ h₂ h₃ h₅]
    unfold g
    ring)

/-- Equal weights at lags two and three have exactly the selected {2,3,5}
symbol with zero fifth weight, so no additional source premise is introduced. -/
theorem selectedSymbol_eq_weights23 (G u w : ℝ) (h0 : 0≤w) (h1 : w≤1) (c : ℝ) :
    dualSymbol (P5.weights235 w (1-w) h0 (by linarith) (by linarith)) u G c=
      dualSymbol (weights23 w h0 h1) u G c := by
  rw [P5.dualSymbol_weights235,dualSymbol_weights23]
  ring

/-- The full actual P₂ branch supplies the baseline factors required above. -/
def p2SelectedFactorization {z : ℝ} (hz : z∈P2.parameterInterval) :
    SquareFactorization 7 (fun θ =>
      -dualSymbol (P5.weights235 (P2.W z) (1-P2.W z)
        (P2.weight_bounds hz).1.le (by linarith [(P2.weight_bounds hz).2]) (by linarith))
        (P2.u z) (P2.G z) (frequencyCosine θ)) := by
  exact ((p2SymbolFactorization hz).widen (show 5≤7 by omega)).congr (fun θ => by
    rw [selectedSymbol_eq_weights23]
    rfl)

/-- The entire exact spiral arc supplies the same baseline factors. -/
def spiralSelectedFactorization {G : ℝ} (hG : G1≤G) (hGW : G≤GW) :
    SquareFactorization 7 (fun θ =>
      -dualSymbol (P5.weights235 (spiralWeight G) (1-spiralWeight G)
        (spiralWeight_mem (by linarith [G1_bounds.1]) hGW).1
        (by linarith [(spiralWeight_mem (by linarith [G1_bounds.1]) hGW).2])
        (by linarith)) (1-1/(2*G)) G (frequencyCosine θ)) := by
  exact ((spiralSymbolFactorization hG hGW).widen (show 5≤7 by omega)).congr (fun θ => by
    rw [selectedSymbol_eq_weights23])

/-- Actual P₂ strict perturbations, with no assumed baseline factorization. -/
def p2StrictGapFactorization {z v γ ε : ℝ} (hz : z∈P2.parameterInterval)
    (huv : P2.u z≤v) (hγ : 0≤γ) (hsmall : 4*γ≤v^2-P2.u z^2)
    (hε : ε≤(P2.G z-1)*(v^2-P2.u z^2)+2*γ*v^2) :
    SquareFactorization 7 (fun θ =>
      -dualSymbol (P2.dualWeights z hz) v (P2.G z) (frequencyCosine θ)-
        2*γ*g v (frequencyCosine θ)-ε) := by
  have hu : 0≤P2.u z:=by linarith [P2.u_lower_positive z hz]
  have h:=selectedStrictGapFactorization (P2.one_lt_G hz).le
    (P2.weight_bounds hz).1.le (by linarith [(P2.weight_bounds hz).2]) (by linarith)
    (p2SelectedFactorization hz) hu huv hγ hsmall hε
  exact h.congr (fun θ => by rw [selectedSymbol_eq_weights23]; rfl)

/-- Actual spiral strict perturbations, with no assumed baseline factorization. -/
def spiralStrictGapFactorization {G v γ ε : ℝ} (hG : G1≤G) (hGW : G≤GW)
    (huv : 1-1/(2*G)≤v) (hγ : 0≤γ) (hsmall : 4*γ≤v^2-(1-1/(2*G))^2)
    (hε : ε≤(G-1)*(v^2-(1-1/(2*G))^2)+2*γ*v^2) :
    SquareFactorization 7 (fun θ =>
      -dualSymbol (weights23 (spiralWeight G)
        (spiralWeight_mem (by linarith [G1_bounds.1]) hGW).1
        (spiralWeight_mem (by linarith [G1_bounds.1]) hGW).2)
        v G (frequencyCosine θ)-2*γ*g v (frequencyCosine θ)-ε) := by
  have hg : 1≤G:=by linarith [G1_bounds.1]
  have hdiv : 1/(2*G)≤1:=by
    apply (div_le_one (by positivity : 0<2*G)).mpr
    linarith
  have h:=selectedStrictGapFactorization hg
    (spiralWeight_mem hg hGW).1 (by linarith [(spiralWeight_mem hg hGW).2]) (by linarith)
    (spiralSelectedFactorization hG hGW) (by linarith) huv hγ hsmall hε
  exact h.congr (fun θ => by rw [selectedSymbol_eq_weights23])

/-- On the actual critical P₅ neighborhood, every source strict perturbation
has explicit width-seven factors, including the equal minimizer multipliers. -/
theorem eventually_p5StrictGapFactorization :
    ∀ᶠ h in 𝓝 (0 : ℝ), 0≤h →
      ∃ h₂ : 0≤P5.localBranch h 5, ∃ h₃ : 0≤P5.localBranch h 6,
      ∃ h₅ : 0≤1-P5.localBranch h 5-P5.localBranch h 6,
      ∀ v γ ε : ℝ, 1/2+h*P5.localBranch h 0≤v → 0≤γ →
        4*γ≤v^2-(1/2+h*P5.localBranch h 0)^2 →
        ε≤h*(v^2-(1/2+h*P5.localBranch h 0)^2)+2*γ*v^2 →
        Nonempty (SquareFactorization 7 (fun θ =>
          -dualSymbol (P5.weights235 _ _ h₂ h₃ h₅) v (1+h) (frequencyCosine θ)-
            2*γ*g v (frequencyCosine θ)-ε)) := by
  have hc : ContinuousAt (fun h : ℝ => 1/2+h*P5.localBranch h 0) 0 := by
    have hz:=(continuous_apply (0 : Fin 7)).continuousAt.comp P5.localBranch_analyticAt.continuousAt
    fun_prop
  have hu:=continuousAt_const.eventually_lt hc (by norm_num : (0 : ℝ)<1/2+(0 : ℝ)*P5.localBranch 0 0)
  filter_upwards [eventually_p5SymbolFactorization,hu] with h hf hu hh
  obtain ⟨h₂,h₃,h₅,⟨cert⟩⟩:=hf hh
  refine ⟨h₂,h₃,h₅,?_⟩
  intro v γ ε huv hγ hsmall hε
  refine ⟨selectedStrictGapFactorization (by linarith : (1 : ℝ)≤1+h)
    h₂ h₃ h₅ cert hu.le huv hγ hsmall ?_⟩
  convert hε using 1; ring

end polyak.FiniteHorizon
