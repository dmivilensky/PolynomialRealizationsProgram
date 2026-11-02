import krylov.OneGradient.KnownBaseCentredUpper
import krylov.OneGradient.TwoQueryRiskAttainment
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), original full physical two-query guarantee.
Use: quantify the genuine known-base source class before choosing any
increment, hidden completion or unevaluated output operator.
Source: actual data-only M1 execution, the true penultimate CG energy
normalization, finite physical centring and attained robust game.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Secant
open scoped Matrix.Norms.L2Operator

/-- A genuine uniform bound on every original symmetric physical second
segment and independent symmetric unevaluated output segment, in the
known base metric and true penultimate reference normalization.
Use: the method is fixed before all original physical scenario quantifiers.
Article: main_krylov, thm:local(c), original two-dimensional M1 guarantee. -/
def knownBaseTwoQueryGuarantee (base : Matrix (Fin 2) (Fin 2) ℝ)
    (g : EuclideanSpace ℝ (Fin 2)) (eta radius : ℝ)
    (m : OneGradientMethod (EuclideanSpace ℝ (Fin 2))) (v : ℝ) : Prop :=
  ∀ C : Matrix (Fin 2) (Fin 2) ℝ,C.IsSymm → relativeBudget base (C-base)≤ eta →
    ∀ B : Matrix (Fin 2) (Fin 2) ℝ,B.IsSymm → relativeBudget base (B-C)≤ radius →
      ‖cgOperator (metricRoot base)⁻¹ (m.outputGradient (cgOperator B)
        (oneGradientRun m (twoQueryOperators (cgOperator base) (cgOperator C)) g 2))‖≤
        ‖cgCanonicalError base g 1‖*v

/-- One actual history-only centred M1 method uniformly guarantees V2
with a common explicit cubic loss on the entire original scenario class.
Use: the attaining algorithm is chosen before every unknown matrix.
Article: main_krylov, thm:local(c), genuine source-wide upper guarantee.
Proof: apply the proved actual physical finite estimate to each genuine
scenario under its original relative budgets and true normalization. -/
theorem knownBaseCentredMethod_twoQueryGuarantee
    (base : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin 2)) (hc : referenceAtomCount base hb g=2)
    (W w omega : ℝ) (hW : 0< W) (hw : 0≤ w) (homega : 0< omega)
    (hsmall : W*omega≤(1/2 : ℝ)) :
    knownBaseTwoQueryGuarantee base g (W*omega) (w*omega)
      (knownBaseCentredMethod base (W*omega))
      (twoDimensionalValue W w*omega^2+2*W^2*(W+w)*omega^3) := by
  intro C hC hbudget B _ houtput
  exact knownBaseCentredMethod_physical_upper base C B hb hC g hc W w omega hW hw homega hsmall hbudget houtput

/-- Any genuine uniform physical guarantee bounds the complete actual
hidden-model robust game at its true common recorded output.
Use: a finite arbitrary-output game lower bound applies to all original
methods and physical scenarios, without a scalar-risk relaxation.
Article: main_krylov, thm:local(c), original physical guarantee dictionary.
Proof: realize the true robust game with a genuine symmetric output
matrix. Both physical hidden endpoints obey the original increment
budget, and the same actual output perturbation obeys its exact relative
budget. Apply the original guarantee to both real semantic outputs. -/
theorem knownBaseTwoQueryGuarantee_robust_game
    (base C D : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef) (hC : C.IsSymm) (hDs : D.IsSymm)
    (g : EuclideanSpace ℝ (Fin 2)) (eta radius v : ℝ) (hradius : 0< radius)
    (m : OneGradientMethod (EuclideanSpace ℝ (Fin 2)))
    (hD : cgOperator D (m.step (oneGradientRun m (fun _ => cgOperator base) g 1))=0)
    (hp : relativeBudget base (C+D-base)≤ eta) (hm : relativeBudget base (C-D-base)≤ eta)
    (hguarantee : knownBaseTwoQueryGuarantee base g eta radius m v) :
    let H := oneGradientRun m (twoQueryOperators (cgOperator base) (cgOperator C)) g 2
    twoModelRisk (cgOperator (relativeOperator base C)) (cgOperator (relativeOperator base D))
      (cgOperator (metricRoot base)⁻¹ H.gradient) (cgOperator (metricRoot base) (m.output H)) radius≤
      ‖cgCanonicalError base g 1‖*v := by
  obtain ⟨F,hFs,hFn,hreal⟩ := twoQuery_physical_risk_attained base C D hb m g hD radius hradius
  have hp' := hguarantee (C+D) (hC.add hDs) hp (C+D+F) ((hC.add hDs).add hFs)
    (by simpa only [add_sub_cancel_left] using hFn)
  have hm' := hguarantee (C-D) (hC.sub hDs) hm (C-D+F) ((hC.sub hDs).add hFs)
    (by simpa only [add_sub_cancel_left] using hFn)
  exact hreal.trans (max_le hp' hm')

end
end krylov.OneGradient
