import krylov.OneGradient.KnownBaseTwoQueryGuarantee
import krylov.OneGradient.TwoQueryPhysicalCoordinates
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), original physical four-model guarantee.
Use: apply actual uniform M1 guarantees to original physical hidden
completions built from genuine canonical endpoint contractions.
Source: exact inverse-root form transport, actual arbitrary-query residual
coordinates and physical attainment of the full robust output game.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Secant krylov.Information
open scoped Matrix.Norms.L2Operator

/-- Every original physical uniform guarantee bounds the true transported
hidden-pair game on the method's actual query and actual common-data output.
Endpoint budgets and hidden-query annihilation are imposed on genuine
canonical matrices and then derived for their real physical transports.
Use: the finite V2 game is tied to the full original source class before
taking any asymptotic limit or optimizing over methods.
Article: main_krylov, thm:local(c), genuine physical lower-game dictionary.
Proof: transport both true forms by the known positive root. Linearity
and exact identity transport give the two actual relative endpoint budgets.
The real hidden action vanishes on the genuine second query. Apply the
proved physical guarantee dictionary and exact native residual coordinates. -/
theorem twoQuery_transported_game_bound
    (base J K : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef) (hJ : J.IsSymm) (hK : K.IsSymm)
    (g : EuclideanSpace ℝ (Fin 2)) (eta radius v : ℝ) (hradius : 0< radius)
    (m : OneGradientMethod (EuclideanSpace ℝ (Fin 2)))
    (hhidden : cgOperator K (cgOperator (metricRoot base) (oneGradientStep m (fun _ => cgOperator base) g 1))=0)
    (hp : ‖J+K-1‖≤ eta) (hm : ‖J-K-1‖≤ eta)
    (hguarantee : knownBaseTwoQueryGuarantee base g eta radius m v) :
    let R := cgOperator (metricRoot base)
    let C := inverseFormMap (metricRoot base)⁻¹ J
    let H := oneGradientRun m (twoQueryOperators (cgOperator base) (cgOperator C)) g 2
    let rho := cgOperator (metricRoot base)⁻¹ g+
      R (oneGradientStep m (fun _ => cgOperator base) g 0)+
      cgOperator J (R (oneGradientStep m (fun _ => cgOperator base) g 1))
    twoModelRisk (cgOperator J) (cgOperator K) rho (R (m.output H)) radius≤‖cgCanonicalError base g 1‖*v := by
  let T := inverseFormMap (metricRoot base)⁻¹
  let C := T J
  let D := T K
  have hC : C.IsSymm := inverseForm_isSymm _ J hJ
  have hD : D.IsSymm := inverseForm_isSymm _ K hK
  have hzero : cgOperator D (m.step (oneGradientRun m (fun _ => cgOperator base) g 1))=0 :=
    twoQuery_physical_hidden_action base K hb _ hhidden
  have hplus : relativeBudget base (C+D-base)≤ eta := by
    have he : C+D-base=T (J+K-1) := by
      rw [map_sub,map_add,inverseRootForm_one base hb]
    rw [he]
    change ‖relativeOperator base (T (J+K-1))‖≤ eta
    rw [relativeOperator_inverseRootForm base _ hb]
    exact hp
  have hminus : relativeBudget base (C-D-base)≤ eta := by
    have he : C-D-base=T (J-K-1) := by
      rw [map_sub,map_sub,inverseRootForm_one base hb]
    rw [he]
    change ‖relativeOperator base (T (J-K-1))‖≤ eta
    rw [relativeOperator_inverseRootForm base _ hb]
    exact hm
  have hbound := knownBaseTwoQueryGuarantee_robust_game base C D hb hC hD g eta radius v hradius m
    hzero hplus hminus hguarantee
  dsimp only at hbound ⊢
  rw [relativeOperator_inverseRootForm base J hb,relativeOperator_inverseRootForm base K hb,
    twoQuery_physical_form_gradient base J hb m g] at hbound
  exact hbound

end
end krylov.OneGradient
