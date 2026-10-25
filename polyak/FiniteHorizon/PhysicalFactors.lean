import polyak.FiniteHorizon.PolyakSource

/-!
Article: Appendix C, the concrete branch factor factories.
Use: the actual normalized interpolation matrix and actual sampled-value
coefficients discharge every symbol and zero-charge premise of the P₁, P₂,
spiral and critical P₅ factorizations.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Spectral Boundary Filter
open scoped Topology BigOperators

theorem p2_weights_lag_le_five {z : ℝ} (hz : z∈P2.parameterInterval) :
    ∀ n∈(P2.dualWeights z hz).lags,n≤5 := by
  intro n hn
  change n∈({2,3} : Finset ℕ) at hn
  simp only [Finset.mem_insert,Finset.mem_singleton] at hn
  omega

def p2PhysicalBandedData7 {z q t γ ε : ℝ} (hz : z∈P2.parameterInterval) (hq : 0<q)
    (hG : Real.cosh t=P2.G z) (hγ : 0≤γ)
    (huv : P2.u z≤Real.sinh (t-Real.log q))
    (hsmall : 4*γ≤Real.sinh (t-Real.log q)^2-P2.u z^2)
    (hε : ε≤(P2.G z-1)*(Real.sinh (t-Real.log q)^2-P2.u z^2)+
      2*γ*Real.sinh (t-Real.log q)^2) :
    BandedData7 (normalizedMatrix7 (P2.dualWeights z hz) q t γ hγ)
      (normalizedValues7 (P2.dualWeights z hz) t γ hγ) ε :=
  p2BandedData7 hz _ _
    (fun θ => by rw [normalizedMatrix7_symbol _ hq _ _ _ (p2_weights_lag_le_five hz),hG])
    (normalizedValues7_charge _ _ _ _ (p2_weights_lag_le_five hz)) huv hγ hsmall hε

theorem spiral_weights_lag_le_five {G : ℝ} (hG : 1≤G) (hGW : G≤GW) :
    ∀ n∈(weights23 (spiralWeight G) (spiralWeight_mem hG hGW).1 (spiralWeight_mem hG hGW).2).lags,n≤5 := by
  intro n hn
  change n∈({2,3} : Finset ℕ) at hn
  simp only [Finset.mem_insert,Finset.mem_singleton] at hn
  omega

def spiralPhysicalBandedData7 {q t γ ε : ℝ} (hq : 0<q) (hG : G1≤Real.cosh t)
    (hGW : Real.cosh t≤GW) (hγ : 0≤γ)
    (huv : 1-1/(2*Real.cosh t)≤Real.sinh (t-Real.log q))
    (hsmall : 4*γ≤Real.sinh (t-Real.log q)^2-(1-1/(2*Real.cosh t))^2)
    (hε : ε≤(Real.cosh t-1)*(Real.sinh (t-Real.log q)^2-(1-1/(2*Real.cosh t))^2)+
      2*γ*Real.sinh (t-Real.log q)^2) :
    BandedData7
      (normalizedMatrix7 (weights23 (spiralWeight (Real.cosh t))
        (spiralWeight_mem (Real.one_le_cosh t) hGW).1 (spiralWeight_mem (Real.one_le_cosh t) hGW).2) q t γ hγ)
      (normalizedValues7 (weights23 (spiralWeight (Real.cosh t))
        (spiralWeight_mem (Real.one_le_cosh t) hGW).1 (spiralWeight_mem (Real.one_le_cosh t) hGW).2) t γ hγ) ε :=
  spiralBandedData7 hG hGW _ _
    (fun θ => normalizedMatrix7_symbol _ hq _ _ _ (spiral_weights_lag_le_five (Real.one_le_cosh t) hGW) θ)
    (normalizedValues7_charge _ _ _ _ (spiral_weights_lag_le_five (Real.one_le_cosh t) hGW)) huv hγ hsmall hε

theorem oneAtom_weights_lag_le_five : ∀ n∈P1.weights.lags,n≤5 := by
  intro n hn
  change n∈({3} : Finset ℕ) at hn
  simp only [Finset.mem_singleton] at hn
  omega

def oneAtomPhysicalBandedData7 {z u a q t γ ε : ℝ} (hz : 0<z) (hz1 : z≤1)
    (h0 : P1.quartic z u a=0) (h1 : P1.quarticDerivative z u a=0)
    (hqres : |P1.residualLinear z u a|≤P1.residualConstant z u a) (hq : 0<q)
    (hG : Real.cosh t=1/z) (hu : 0≤u) (hγ : 0≤γ)
    (huv : u≤Real.sinh (t-Real.log q)) (hsmall : 4*γ≤Real.sinh (t-Real.log q)^2-u^2)
    (hε : ε≤(1/z-1)*(Real.sinh (t-Real.log q)^2-u^2)+2*γ*Real.sinh (t-Real.log q)^2) :
    BandedData7 (normalizedMatrix7 P1.weights q t γ hγ) (normalizedValues7 P1.weights t γ hγ) ε :=
  oneAtomBandedData7 hz hz1 h0 h1 hqres _ _
    (fun θ => by rw [normalizedMatrix7_symbol _ hq _ _ _ oneAtom_weights_lag_le_five,hG])
    (normalizedValues7_charge _ _ _ _ oneAtom_weights_lag_le_five) hu huv hγ hsmall hε

theorem p5_weights_lag_le_five {w₂ w₃ : ℝ} (h₂ : 0≤w₂) (h₃ : 0≤w₃) (h₅ : 0≤1-w₂-w₃) :
    ∀ n∈(P5.weights235 w₂ w₃ h₂ h₃ h₅).lags,n≤5 := by
  intro n hn
  change n∈({2,3,5} : Finset ℕ) at hn
  simp only [Finset.mem_insert,Finset.mem_singleton] at hn
  omega

theorem eventually_p5PhysicalBandedData7 :
    ∀ᶠ h in 𝓝 (0 : ℝ),0≤h →
      ∃ h₂ : 0≤P5.localBranch h 5,∃ h₃ : 0≤P5.localBranch h 6,
      ∃ h₅ : 0≤1-P5.localBranch h 5-P5.localBranch h 6,
      ∀ (q t γ ε : ℝ) (_hq : 0<q) (hγ : 0≤γ),Real.cosh t=1+h →
        1/2+h*P5.localBranch h 0≤Real.sinh (t-Real.log q) →
        4*γ≤Real.sinh (t-Real.log q)^2-(1/2+h*P5.localBranch h 0)^2 →
        ε≤h*(Real.sinh (t-Real.log q)^2-(1/2+h*P5.localBranch h 0)^2)+
          2*γ*Real.sinh (t-Real.log q)^2 →
        Nonempty (BandedData7
          (normalizedMatrix7 (P5.weights235 _ _ h₂ h₃ h₅) q t γ hγ)
          (normalizedValues7 (P5.weights235 _ _ h₂ h₃ h₅) t γ hγ) ε) := by
  filter_upwards [eventually_p5BandedData7] with h hh hnonneg
  obtain ⟨h₂,h₃,h₅,hdata⟩:=hh hnonneg
  refine ⟨h₂,h₃,h₅,?_⟩
  intro q t γ ε hq hγ hG huv hs hε
  let W:=P5.weights235 (P5.localBranch h 5) (P5.localBranch h 6) h₂ h₃ h₅
  apply hdata (normalizedMatrix7 W q t γ hγ) (normalizedValues7 W t γ hγ)
    (Real.sinh (t-Real.log q)) γ ε
  · intro θ
    rw [normalizedMatrix7_symbol _ hq _ _ _ (p5_weights_lag_le_five h₂ h₃ h₅),hG]
  · exact normalizedValues7_charge _ _ _ _ (p5_weights_lag_le_five h₂ h₃ h₅)
  · exact huv
  · exact hγ
  · exact hs
  · exact hε

end polyak.FiniteHorizon
