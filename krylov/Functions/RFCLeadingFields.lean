import krylov.Functions.RFCReferenceFields
import krylov.Functions.FCLeadingFields
import krylov.Functions.NativeRFCBootstrap

/-!
Article: main_krylov, thm:Htransfer, genuine finite ordinary RFC terminal map.
Use: state the true finite normalized operator response map and its genuine
second derivative, and identify the actual native returned gradient with that
map. No asymptotic coefficient or flatness is built into its definition.
Source: actual ordinary RFC execution, quadratic CG termination and genuine
native/operator transcript equality.
-/
namespace krylov.Functions
noncomputable section
open Set krylov.Methods krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual finite ordinary RFC terminal map in independent true search and
correction operator coordinates. Article: main_krylov, thm:Htransfer. -/
def rfcFiniteTerminal (Q : E →L[ℝ] E) (N : ℕ)
    (z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E))) : E :=
  probedGradient (rfcMethod fullMemory 1) (fcFiniteOperatorPath Q N z.2.1)
    (fcFiniteOperatorPath Q N z.2.2) z.1 N

/-- The genuine second operator coefficient of the actual ordinary RFC map.
Article: main_krylov, thm:Htransfer, the degree-three physical response.
The factor one half is the actual second Taylor coefficient. -/
def rfcSecondOperator (Q : E →L[ℝ] E) (N : ℕ) (g : E)
    (Θ Ξ : Fin N → E →L[ℝ] E) : E :=
  (1/2:ℝ) • iteratedFDeriv ℝ 2 (rfcFiniteTerminal Q N) (g,0) (fun _=>(0,(Θ,Ξ)))

/-- The actual ordinary RFC finite terminal map is analytic at every true
nondegenerate positive quadratic reference. Article: main_krylov, lem:U(d). -/
theorem rfcFiniteTerminal_analytic (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (g : E) (hpre : ∀ i<N, CG.gradient Q g i≠0) :
    AnalyticAt ℝ (rfcFiniteTerminal Q N) (g,0) := by
  let A := fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E))=>fcFiniteOperatorPath Q N z.2.1
  let B := fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E))=>fcFiniteOperatorPath Q N z.2.2
  have hA i : AnalyticAt ℝ (fun z=>A z i) (g,0) := by
    by_cases hi : i<N
    · simp only [A,fcFiniteOperatorPath,dite_eq_left hi]
      have hp : AnalyticAt ℝ (fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E))=>z.2.1) (g,0) :=
        analyticAt_fst.comp analyticAt_snd
      exact analyticAt_const.add (((ContinuousLinearMap.proj (R:=ℝ)
        (φ:=fun _ : Fin N=>E →L[ℝ] E) ⟨i,hi⟩).analyticAt (0 : Fin N → E →L[ℝ] E)).comp (g:=fun y : Fin N → E →L[ℝ] E=>y ⟨i,hi⟩)
          (f:=fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E))=>z.2.1) hp)
    · simp only [A,fcFiniteOperatorPath,dite_eq_right hi]
      exact analyticAt_const
  have hB i : AnalyticAt ℝ (fun z=>B z i) (g,0) := by
    by_cases hi : i<N
    · simp only [B,fcFiniteOperatorPath,dite_eq_left hi]
      have hp : AnalyticAt ℝ (fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E))=>z.2.2) (g,0) :=
        analyticAt_snd.comp analyticAt_snd
      exact analyticAt_const.add (((ContinuousLinearMap.proj (R:=ℝ)
        (φ:=fun _ : Fin N=>E →L[ℝ] E) ⟨i,hi⟩).analyticAt (0 : Fin N → E →L[ℝ] E)).comp (g:=fun y : Fin N → E →L[ℝ] E=>y ⟨i,hi⟩)
          (f:=fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E))=>z.2.2) hp)
    · simp only [B,fcFiniteOperatorPath,dite_eq_right hi]
      exact analyticAt_const
  exact (quadraticRFC_prefix_analytic fullMemory 1 A B Prod.fst (g,0) hA hB analyticAt_fst Q
    (fcFiniteOperatorPath_zero Q N) (fcFiniteOperatorPath_zero Q N) hQ hpos
    (fun _ _ hk=>hk) N hpre).1

variable [FiniteDimensional ℝ E]

/-- The true full-dimensional quadratic ordinary RFC terminal slice vanishes
for every initial gradient. Article: main_krylov, lem:consistent(a). -/
theorem rfcFiniteTerminal_reference_zero (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) : rfcFiniteTerminal Q (Module.finrank ℝ E) (g,0)=0 := by
  change probedGradient (rfcMethod fullMemory 1) (fcFiniteOperatorPath Q (Module.finrank ℝ E) 0)
    (fcFiniteOperatorPath Q (Module.finrank ℝ E) 0) g (Module.finrank ℝ E)=0
  rw [fcFiniteOperatorPath_zero]
  exact ((rfcMethod_static fullMemory 1 Q hQ hpos g (fun _ _ hk=>hk) _).1).trans
    (cg_gradient_finrank_zero Q hQ hpos g)

omit [FiniteDimensional ℝ E] in
/-- The actual native terminal gradient is exactly its genuine finite
normalized RFC map, on all true segment operators.
Article: main_krylov, thm:Htransfer, faithful finite input dictionary. -/
theorem NativeRFCPrefixBounds.normalized_terminal
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (r : ℝ) (u : E) (ε M D C : ℝ) (hε : ε≠0) (N : ℕ)
    (hp : NativeRFCPrefixBounds T f G H Q r u ε M D C N) :
    let Θ : Fin N → E →L[ℝ] E := fun j=>rfcFunctionSearchOperator T f G H fullMemory r (ε • u) j.val-Q
    let Ξ : Fin N → E →L[ℝ] E := fun j=>rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u) j.val-Q
    G (rfcFunctionPoint T f G fullMemory r (ε • u) N)=
      ε • rfcFiniteTerminal Q N (ε⁻¹ • G (ε • u),(Θ,Ξ)) := by
  intro Θ Ξ
  let A := rfcFunctionSearchOperator T f G H fullMemory r (ε • u)
  let B := rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u)
  have hA j (hj : j<N) : A j=fcFiniteOperatorPath Q N Θ j := by
    simp only [fcFiniteOperatorPath,dite_eq_left hj,Θ]
    change A j=Q+(A j-Q)
    abel
  have hB j (hj : j<N) : B j=fcFiniteOperatorPath Q N Ξ j := by
    simp only [fcFiniteOperatorPath,dite_eq_left hj,Ξ]
    change B j=Q+(B j-Q)
    abel
  have hinit : G (ε • u)=ε • (ε⁻¹ • G (ε • u)) := by rw [smul_smul,mul_inv_cancel₀ hε,one_smul]
  rw [←rfcFunctionRun_gradient T f G fullMemory r (ε • u) N,(hp.1 N le_rfl).2]
  conv_lhs => rw [hinit]
  have hh := methodRun_congr_prefix (rfcMethod fullMemory 1) A B
    (fcFiniteOperatorPath Q N Θ) (fcFiniteOperatorPath Q N Ξ) (ε • (ε⁻¹ • G (ε • u))) N hA hB
  rw [hh]
  exact (rfc_scalar fullMemory 1 _ _ (ε⁻¹ • G (ε • u)) ε hε N).1

end
end krylov.Functions
