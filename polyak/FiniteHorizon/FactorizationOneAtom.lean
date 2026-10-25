import polyak.FiniteHorizon.FactorizationConstructors
import polyak.Boundary.P1.Algebra

/-!
Article: Appendix C, actual source one-atom factors.
Use: the contact equations and the scalar residual reserve proved for the
physical P₁ branch produce real causal factors; these are genuine source
equations, rather than an assumed spectral-factor existence certificate.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Boundary Energy Spectral

/-- The independently defined P₁ quartic has real causal factors of width four. -/
def oneAtomQuarticFactorization {z u a : ℝ}
    (h0 : P1.quartic z u a=0) (h1 : P1.quarticDerivative z u a=0)
    (hq : |P1.residualLinear z u a|≤P1.residualConstant z u a) :
    SquareFactorization 4 (fun θ => P1.quartic z u (frequencyCosine θ)) := by
  have h0':=linearSquareFactorization (-a) 1
  have h1':=quadraticPositiveLeadingFactorization (d:=z^2) (sq_nonneg _) hq
  exact (h0'.mul h1').congr (fun θ => by
    rw [P1.quartic_factor h0 h1]
    unfold P1.residual
    ring)

/-- The actual P₁ dual symbol has real causal factors of width five. -/
def oneAtomSymbolFactorization {z u a : ℝ} (hz : 0<z) (hz1 : z≤1)
    (h0 : P1.quartic z u a=0) (h1 : P1.quarticDerivative z u a=0)
    (hq : |P1.residualLinear z u a|≤P1.residualConstant z u a) :
    SquareFactorization 5 (fun θ => -dualSymbol P1.weights u (1/z) (frequencyCosine θ)) := by
  have hG : 1≤1/z:=(le_div_iff₀ hz).mpr (by linarith)
  have hd : 0<4-z^2:=by nlinarith
  have h:=((gapFactorization hG).mul (oneAtomQuarticFactorization h0 h1 hq)).scale
    (r:=4/(4-z^2)) (by positivity)
  exact h.congr (fun θ => by
    have he:=P1.dualSymbol_quartic hz.ne' hd.ne' u (frequencyCosine θ)
    calc
      _=(4*(1/z-frequencyCosine θ)*P1.quartic z u (frequencyCosine θ))/(4-z^2) := by ring
      _=_ := by
        apply (div_eq_iff hd.ne').mpr
        linear_combination he)

end polyak.FiniteHorizon
