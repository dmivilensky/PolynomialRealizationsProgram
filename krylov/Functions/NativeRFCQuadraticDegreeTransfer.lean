import krylov.Functions.NativeRFCInputJet
import krylov.Functions.NativeQuadraticInputJets
import krylov.Functions.HomogeneousQuadraticTransfer

/-!
Article: main_krylov, lem:cycle-transfer, arbitrary native ordinary RFC response degree.
Use: transfer an independently proved genuine degree-d finite operator
response to the actual scalar objective executor with degree d+1, with an order-(d+2) remainder.
All actual source bounds, all actual initial-gradient/secant first jets and
the exact native/output dictionary are derived from original derivatives.
Only the independent operator theorem is a response hypothesis.
Source: true native ordinary RFC embedding and genuine multilinear substitution.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Every genuine degree-d finite ordinary RFC operator expansion transfers to the
actual scalar function at degree d+1 with order-(d+2) error, compact-uniformly on the original
reference family. No native trajectory, source jet or native output
expansion is assumed. Article: main_krylov, lem:cycle-transfer. -/
theorem nativeRFCPoint_homogeneous_quadratic_transfer (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (D : E → E →L[ℝ] E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L L₃ : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hD : ∀ z : E, ‖T z‖≤r → HasFDerivAt H (D z) z)
    (hDlip : LipschitzOnWith L₃ D (T ⁻¹' closedBall (0:E) r))
    (hF : ∀ z : E, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i<N, CG.gradient Q g i≠0)
    (B : ℝ) (hB : 0<B) (d : ℕ)
    (P : E → ContinuousMultilinearMap ℝ (fun _ : Fin d => E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E))) E)
    (C : ℝ) (hC : 0≤C) (hP : ∀ u : E, ‖u‖≤B → Q u∈K → ‖P u‖≤C)
    (A : ℝ) (hA : 0≤A)
    (hop : ∃ δ : ℝ, 0<δ ∧ ∀ u : E, ‖u‖≤B → Q u∈K →
      ∀ I : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E)), ‖I‖<δ →
        ‖rfcFiniteTerminal Q N (Q u+I.1,I.2)-homogeneousResponse (P u) I‖≤A*‖I‖^(d+1)) :
    ∃ ε₀ C₀ : ℝ, 0<ε₀ ∧ 0≤C₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : E, ‖u‖≤B → Q u∈K →
        ‖G (rfcFunctionPoint T f G fullMemory r (ε • u) N)-
          ε^(d+1) • homogeneousResponse (P u) (nativeRFCReferenceInputJet Q (D 0) u N)‖≤C₀*ε^(d+2) := by
  have hD0 : HasFDerivAt H (D 0) 0 := hD 0 (by simpa only [map_zero,norm_zero] using hr.le)
  let U : Set E := {u | ‖u‖≤B ∧ Q u∈K}
  let x := fun ε u => nativeRFCInput T f G H Q r ε u N
  let v := fun u => nativeRFCReferenceInputJet Q (D 0) u N
  let F := fun u (I : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E))) => rfcFiniteTerminal Q N (Q u+I.1,I.2)
  obtain ⟨ex,Cx,hex,hCx,hsource⟩ := nativeRFCInput_bound T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos N K hK hpre B hB
  have hxb : ∃ ep : ℝ, 0<ep ∧ ∀ ε : ℝ, 0<ε → ε<ep → ∀ u∈U, ‖x ε u‖≤Cx*ε := by
    exact ⟨ex,hex,fun ε hε he u hu => hsource ε hε he u hu.1 hu.2⟩
  have hjet : ∀ τ : ℝ, 0<τ → ∃ ep : ℝ, 0<ep ∧ ∀ ε : ℝ, 0<ε → ε<ep →
      ∀ u∈U, ‖x ε u-ε • v u‖≤τ*ε := by
    intro τ hτ
    obtain ⟨ep,hep,hj⟩ := nativeRFCInput_reference_jet T hT f G H Q (D 0) hD0 hr hG₀ hH₀ hHc₀
      hLr hH hF hG hQ hpos N K hK hpre B hB τ hτ
    exact ⟨ep,hep,fun ε hε he u hu => hj ε hε he u hu.1 hu.2⟩
  have hv := uniform_jet_leading_bound x v U Cx hxb hjet
  have hxb' : ∃ ep : ℝ, 0<ep ∧ ∀ ε : ℝ, 0<ε → ε<ep → ∀ u∈U, ‖x ε u‖≤(Cx+1)*ε := by
    refine ⟨ex,hex,?_⟩
    intro ε hε he u hu
    exact (hsource ε hε he u hu.1 hu.2).trans (by nlinarith only [hε.le])
  obtain ⟨ej,J,hej,hJ,hjb⟩ := nativeRFCInput_reference_jet_quadratic T hT f G H Q D
    hr hG₀ hH₀ hHc₀ hLr hH hD hDlip hF hG hQ hpos N K hK hpre B hB
  have ht := homogeneous_cycle_transfer_quadratic F P x v U (Cx+1) C J A (by positivity) hC hJ hA
    (fun u hu => hP u hu.1 hu.2) hv hxb'
    ⟨ej,hej,fun ε hε he u hu => hjb ε hε he u hu.1 hu.2⟩
    (by obtain ⟨δ,hδ,hb⟩ := hop; exact ⟨δ,hδ,fun u hu I hI => hb u hu.1 hu.2 I hI⟩)
  obtain ⟨eb,M,Da,Cp,heb,_,_,_,hprefix⟩ := nativeRFC_compact_prefix T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos N K hK hpre B hB
  obtain ⟨ep,C₀,hep,hC₀,hb⟩ := ht
  refine ⟨min eb ep,C₀,lt_min heb hep,hC₀,?_⟩
  intro ε hε he u hu hKu
  have hp := hprefix ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  have hd := hp.input_terminal T f G H Q r u ε M Da Cp hε.ne' N
  rw [hd]
  exact hb ε hε (he.trans_le (min_le_right _ _)) u ⟨hu,hKu⟩

end
end krylov.Functions
