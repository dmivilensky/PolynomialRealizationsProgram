import krylov.Convergence.OneGradientFunctions
import krylov.Nonlinear.GradientExtension
import krylov.Methods.OneGradientCoordinates

/-!
Article: main_krylov, thm:V, prop:EL and lem:cycle-transfer.
Use: represent genuine nonlinear one-gradient observations by actual nearby
self-adjoint operators before localizing any query. This auxiliary global
representation permits a local-gradient extension argument and prevents
circular assumptions about the native query domain.
Source: genuine measured self-adjoint backward error (Rump03, Lemma 5.1),
already proved in the gradient-extension module, and exact query recursion.
-/
namespace krylov.Convergence
noncomputable section
open Set krylov.Methods krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A real one-gradient prefix reads exactly its past operator actions;
the current and all future operators remain absent from its decisions.
Article: main_krylov, def:classes(M₁). -/
theorem oneGradientRun_congr_prefix (m : OneGradientMethod E) (A B : ℕ → E →L[ℝ] E)
    (g : E) (N : ℕ) (hAB : ∀ i<N,A i=B i) :
    oneGradientRun m A g N=oneGradientRun m B g N := by
  induction N with
  | zero=>rfl
  | succ k ih=>
    rw [oneGradientRun,oneGradientRun,ih (fun i hi=>hAB i (by omega)),hAB k (by omega)]

omit [CompleteSpace E] in
/-- Genuine measured secant actions suffice for an exact whole scalar
transcript representation, including stopped or zero query steps.
Article: lem:cycle-transfer, thm:V and prop:EL. -/
theorem oneGradientFunctionRun_eq_of_actions (m : OneGradientMethod E) (G : E → E)
    (x₀ : E) (A : ℕ → E →L[ℝ] E) (N : ℕ)
    (hA : ∀ i<N,A i (m.step (oneGradientFunctionRun m G x₀ i))=
      G (oneGradientFunctionPoint m G x₀ i+m.step (oneGradientFunctionRun m G x₀ i))-
        G (oneGradientFunctionPoint m G x₀ i)) :
    oneGradientFunctionRun m G x₀ N=oneGradientRun m A (G x₀) N := by
  induction N with
  | zero=>rfl
  | succ k ih=>
    have he := ih (fun i hi=>hA i (by omega))
    have hs := hA k (by omega)
    rw [←oneGradientFunctionRun_gradient m G x₀ k] at hs
    rw [oneGradientFunctionRun,oneGradientRun,←he]
    have hnew : G (x₀+(oneGradientFunctionRun m G x₀ k).displacement+
        m.step (oneGradientFunctionRun m G x₀ k))=
        (oneGradientFunctionRun m G x₀ k).gradient+A k (m.step (oneGradientFunctionRun m G x₀ k)) :=
      (eq_sub_iff_add_eq.mp hs).symm.trans (add_comm _ _)
    simp only [oneGradientFunctionAdvance,oneGradientAdvance,hnew]

/-- Every actual nonlinear one-gradient transcript has uniformly close
self-adjoint segment representatives when its true gradient error has a
global Lipschitz bound. The queried points themselves are unrestricted.
Article: thm:V and prop:EL, genuine nonlinear query localization backend. -/
theorem oneGradientFunctionRun_representatives (m : OneGradientMethod E) (G : E → E)
    (x₀ : E) (Q : E →L[ℝ] E) (hQ : IsSelfAdjoint Q)
    {η : ℝ≥0} (hG : LipschitzWith η (fun x=>G x-Q x)) :
    ∃ A : ℕ → E →L[ℝ] E,
      (∀ i,IsSelfAdjoint (A i) ∧‖A i-Q‖≤(η:ℝ)) ∧
      ∀ N,oneGradientFunctionRun m G x₀ N=oneGradientRun m A (G x₀) N := by
  have hs i := exists_selfAdjoint_secant_of_lipschitz_error G Q hQ hG
    (oneGradientFunctionPoint m G x₀ i) (m.step (oneGradientFunctionRun m G x₀ i))
  choose A hA hbound himage using hs
  exact ⟨A,fun i=>⟨hA i,hbound i⟩,fun N=>
    oneGradientFunctionRun_eq_of_actions m G x₀ A N (fun i _=>himage i)⟩

end
end krylov.Convergence
