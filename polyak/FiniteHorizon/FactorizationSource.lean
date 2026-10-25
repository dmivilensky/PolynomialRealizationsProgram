import polyak.FiniteHorizon.FactorizationConstructors
import polyak.Boundary.P2.Dual
import polyak.Boundary.P5.LocalDual
import polyak.Boundary.SpiralArc

/-!
Article: Appendix C, the actual boundary symbols in the telescoping factorization.
Use: the proved source double contacts and residual reserves give explicit real
causal square factors, without an existential spectral-factor assumption.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Energy Spectral Boundary Filter
open scoped Topology

theorem frequencyCosine_mem (θ : FrequencyCircle) :
    -1≤frequencyCosine θ ∧ frequencyCosine θ≤1 := by
  have h : |frequencyCosine θ|≤1 := by
    apply (Complex.abs_re_le_norm (character 1 θ)).trans
    simp [character]
  exact abs_le.mp h

/-- The entire certified P₂ arc has an actual width-four real factorization. -/
def p2PolynomialFactorization {z : ℝ} (hz : z∈P2.parameterInterval) :
    SquareFactorization 4 (fun θ =>
      (dualPolynomial (P2.dualWeights z hz) (P2.u z) (P2.G z)).eval (frequencyCosine θ)) := by
  have hg:=P2.one_lt_G hz
  have hw:=(P2.weight_bounds hz).2
  have hp : 0≤4*(1-P2.W z)/(4*P2.G z^2-1):=
    div_nonneg (by linarith) (by nlinarith)
  exact ((doubleContactFactorization (P2.x z) (P2.y z)).scale hp).congr (fun θ => by
    have he:=P2.dualPolynomial_factor_p2 hz ⟨frequencyCosine θ,frequencyCosine_mem θ⟩
    rw [P2.atomPolynomial_factor hz] at he
    simpa only [mul_pow] using he.symm)

/-- Multiplication by G-c gives the actual full P₂ dual-symbol factorization. -/
def p2SymbolFactorization {z : ℝ} (hz : z∈P2.parameterInterval) :
    SquareFactorization 5 (fun θ =>
      -dualSymbol (P2.dualWeights z hz) (P2.u z) (P2.G z) (frequencyCosine θ)) := by
  have hG:1≤P2.G z:=(P2.one_lt_G hz).le
  exact ((gapFactorization hG).mul (p2PolynomialFactorization hz)).congr (fun θ => by
    rw [dualPolynomial_factor _ _ hG]
    ring)

/-- The exact spiral residual has a real width-two factorization on its full arc. -/
def spiralResidualFactorization {G : ℝ} (hG : G1≤G) :
    SquareFactorization 2 (fun θ => spiralResidual G (frequencyCosine θ)) := by
  have hg : 0<G:=by linarith [G1_bounds.1]
  have hs : 0≤spiralSwitch G/(8*G):=
    div_nonneg (spiralSwitch_nonneg hG) (by positivity)
  have h:=(linearSquareFactorization (-(2*G-1)/(4*G)) 1).scale
    (show 0≤2*G by positivity)
  have h0:=(constantFactorization hs).widen (show 0≤2 by omega)
  exact (h.add h0).congr (fun θ => by
    rw [spiralResidual_square (ne_of_gt hg)]
    ring)

/-- The exact spiral symbol has real causal width five, including its endpoint. -/
def spiralSymbolFactorization {G : ℝ} (hG : G1≤G) (hGW : G≤GW) :
    SquareFactorization 5 (fun θ =>
      -dualSymbol (weights23 (spiralWeight G)
        (spiralWeight_mem (by linarith [G1_bounds.1]) hGW).1
        (spiralWeight_mem (by linarith [G1_bounds.1]) hGW).2)
        (1-1/(2*G)) G (frequencyCosine θ)) := by
  have hg : 1≤G:=by linarith [G1_bounds.1]
  have h:=(gapFactorization hg).mul
    ((linearSquareFactorization 1 (2*G)).mul (spiralResidualFactorization hG))
  have hs : 0≤1/(2*G^3*(4*G+1)):=by positivity
  exact (h.scale hs).congr (fun θ => by
    rw [spiralSymbol_factor hg hGW]
    ring)

/-- The actual analytic P₅ branch has a width-six factorization on a neighborhood
of the critical point; its only premise is nonnegativity of the real parameter. -/
theorem eventually_p5PolynomialFactorization :
    ∀ᶠ h in 𝓝 (0 : ℝ), 0≤h →
      Nonempty (SquareFactorization 6 (fun θ =>
        (P5.dualReal h (P5.localBranch h)).eval (frequencyCosine θ))) := by
  filter_upwards [P5.localBranch_equations,P5.eventually_branch_dual_parameters,
    P5.eventually_branchResidual_reserve] with h hz hp hr hh
  obtain ⟨h2,h3,h5,hp,hx,hxy⟩:=hp
  obtain ⟨hy,hdx,hdy⟩:=P5.regularSystem_dual_exact h (P5.localBranch h)
  rw [hz] at hy hdx hdy
  refine ⟨(sexticContactFactorization (P5.branchMain h) (P5.branchAux h)
    (a:=P5.branchResidual₀ h) (b:=P5.branchResidual₁ h) (d:=P5.branchResidual₂ h)
    (by linarith)).congr (fun θ => ?_)⟩
  have hf:=P5.hermite_sextic_eval (P5.dualReal_natDegree h (P5.localBranch h))
    (ne_of_lt hxy) (P5.dualReal_main_root hh hz hp hx) hdx.symm hy.symm hdy.symm
    (frequencyCosine θ)
  simpa only [P5.branchResidual₂,P5.branchResidual₁,P5.branchResidual₀,
    P5.branchCoefficient,add_assoc] using hf.symm

/-- The normalized actual P₅ symbol has width seven on the same critical
neighborhood. The simplex signs are conclusions of the source branch proof. -/
theorem eventually_p5SymbolFactorization :
    ∀ᶠ h in 𝓝 (0 : ℝ), 0≤h →
      ∃ h₂ : 0≤P5.localBranch h 5, ∃ h₃ : 0≤P5.localBranch h 6,
      ∃ h₅ : 0≤1-P5.localBranch h 5-P5.localBranch h 6,
      Nonempty (SquareFactorization 7 (fun θ =>
        -dualSymbol (P5.weights235 _ _ h₂ h₃ h₅)
          (1/2+h*P5.localBranch h 0) (1+h) (frequencyCosine θ))) := by
  filter_upwards [eventually_p5PolynomialFactorization,
    P5.eventually_branch_dual_parameters] with h hfact hw hh
  let h₂:=hw.1.le
  let h₃:=hw.2.1.le
  let h₅:=hw.2.2.1.le
  refine ⟨h₂,h₃,h₅,?_⟩
  obtain ⟨cert⟩:=hfact hh
  have hG : 1≤1+h:=by linarith
  let den:=(1+h)*(4*(1+h)^2-1)*(16*(1+h)^4-12*(1+h)^2+1)
  have hd : 0<den:=P5.commonDenominator_pos hG
  have hQ:=cert.scale (r:=1/den) (by positivity)
  refine ⟨((gapFactorization hG).mul hQ).congr (fun θ => ?_)⟩
  rw [dualPolynomial_factor _ _ hG,
    P5.dualPolynomial_eq_source_of_le hG _ _ _ h₂ h₃ h₅]
  rw [←P5.dualReal_closed]
  dsimp only [den]
  ring

end polyak.FiniteHorizon
