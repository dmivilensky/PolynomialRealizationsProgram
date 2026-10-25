import polyak.FiniteHorizon.SourceFactories
import polyak.Boundary.P5.PhysicalRoot

/-!
Article: Appendix C, the complete continued P₅ source factorization.
Use: genuine continued-root geometry supplies both double contacts and the
uniform positive residual reserve. The actual source optimum then identifies
the boundary in the physical interpolation factory.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Spectral Boundary
open scoped BigOperators

def p5SourcePolynomialFactorization {h : ℝ} {Z : P5.Coordinates}
    (hb : P5.ContinuationGeometry h Z) (hZ : P5.regularSystem (h,Z)=0) :
    SquareFactorization 6 (fun θ => (P5.dualReal h Z).eval (frequencyCosine θ)) :=
  (sexticContactFactorization (P5.branchX h Z) (Z 2)
    (a:=P5.residual₀ h Z) (b:=P5.residual₁ h Z) (d:=P5.residual₂ h Z)
    (by linarith [hb.residual])).congr (fun θ => by
      rw [P5.continuation_dual_factor hb.tail.h_pos.le hZ hb.mass_lt_one
        hb.tail.x_interior.2 hb.atoms_ordered])

def p5SourceSymbolFactorization {h : ℝ} {Z : P5.Coordinates}
    (hb : P5.ContinuationGeometry h Z) (hZ : P5.regularSystem (h,Z)=0)
    (hw5 : 0≤1-Z 5-Z 6) :
    SquareFactorization 7 (fun θ =>
      -dualSymbol (P5.weights235 (Z 5) (Z 6) hb.weight2.le hb.weight3.le hw5)
        (P5.branchU h Z) (1+h) (frequencyCosine θ)) := by
  have hG : 1≤1+h:=by linarith [hb.tail.h_pos]
  let den:=(1+h)*(4*(1+h)^2-1)*(16*(1+h)^4-12*(1+h)^2+1)
  have hd : 0<den:=P5.commonDenominator_pos hG
  let hQ:=(p5SourcePolynomialFactorization hb hZ).scale (r:=1/den) (by positivity)
  exact ((gapFactorization hG).mul hQ).congr (fun θ => by
    rw [dualPolynomial_factor _ _ hG,P5.dualPolynomial_eq_source_of_le hG _ _ _
      hb.weight2.le hb.weight3.le hw5]
    unfold P5.branchU
    rw [←P5.dualReal_closed]
    dsimp [den]
    ring)

def p5SourcePhysicalBandedData7 {h q t γ ε : ℝ} {Z : P5.Coordinates}
    (hb : P5.ContinuationGeometry h Z) (hZ : P5.regularSystem (h,Z)=0)
    (hw5 : 0≤1-Z 5-Z 6) (hq : 0<q) (hG : Real.cosh t=1+h) (hγ : 0≤γ)
    (huv : P5.branchU h Z≤Real.sinh (t-Real.log q))
    (hsmall : 4*γ≤Real.sinh (t-Real.log q)^2-(P5.branchU h Z)^2)
    (hε : ε≤h*(Real.sinh (t-Real.log q)^2-(P5.branchU h Z)^2)+
      2*γ*Real.sinh (t-Real.log q)^2) :
    BandedData7
      (normalizedMatrix7 (P5.weights235 (Z 5) (Z 6) hb.weight2.le hb.weight3.le hw5) q t γ hγ)
      (normalizedValues7 (P5.weights235 (Z 5) (Z 6) hb.weight2.le hb.weight3.le hw5) t γ hγ) ε := by
  have hW:=p5_weights_lag_le_five hb.weight2.le hb.weight3.le hw5
  have hG1 : 1≤1+h:=by linarith [hb.tail.h_pos]
  have hfact:=selectedStrictGapFactorization hG1 hb.weight2.le hb.weight3.le hw5
    (p5SourceSymbolFactorization hb hZ hw5) hb.tail.toTailBounds.u_nonneg huv hγ hsmall (by simpa using hε)
  exact bandedDataOfFactors7 hfact (fun θ => by
    rw [normalizedMatrix7_symbol _ hq _ _ _ hW,hG]
    ring) (normalizedValues7_charge _ _ _ _ hW)

theorem hasPhysicalFactors7_p5_sourceRoot {h q t : ℝ} {Z : P5.Coordinates}
    (hb : P5.ContinuationGeometry h Z) (hZ : P5.regularSystem (h,Z)=0)
    (hw5 : 0≤1-Z 5-Z 6) (hq : 0<q) (ht : Real.cosh t=1+h)
    (hp : ∀ n : ℕ,1≤n → n<24 → ∀ σ : ℝ,(σ= -1 ∨ σ=1) → 0≤P5.actualPrimal h Z n σ) :
    HasPhysicalFactors7 q t := by
  let W:=P5.weights235 (Z 5) (Z 6) hb.weight2.le hb.weight3.le hw5
  refine ⟨W,p5_weights_lag_le_five hb.weight2.le hb.weight3.le hw5,?_⟩
  intro γ ε hγ huv hs hε
  have hu : Real.sinh (V t)=P5.branchU h Z:=by
    rw [P5.sourceRoot_optimal hb hZ hw5 ht hp,Real.sinh_arsinh]
  rw [hu] at huv hs hε
  rw [ht] at hε
  exact ⟨p5SourcePhysicalBandedData7 hb hZ hw5 hq ht hγ huv hs (by simpa using hε)⟩

end polyak.FiniteHorizon
