import krylov.Functions.MetricFCInputJet
import krylov.Functions.HomogeneousCycleTransfer

/-!
Article: main_krylov, lem:cycle-transfer, arbitrary native FC response degree.
Use: transfer an independently proved genuine degree-d finite operator
response to the actual scalar objective executor with degree d+1.
All actual source bounds, all actual initial-gradient/secant first jets and
the exact native/output dictionary are derived from original derivatives.
Only the independent operator theorem is a response hypothesis.
Source: true native FC embedding and genuine multilinear substitution.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Every genuine degree-d finite FC operator expansion transfers to the
actual scalar function at degree d+1, compact-uniformly on the original
reference family. No native trajectory, source jet or native output
expansion is assumed. Article: main_krylov, lem:cycle-transfer. -/
theorem metricFCPoint_homogeneous_transfer (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i<N, CG.gradient Q g i≠0)
    (B : ℝ) (hB : 0<B) (d : ℕ)
    (P : E → ContinuousMultilinearMap ℝ (fun _ : Fin d => E × (Fin N → E →L[ℝ] E)) E)
    (C : ℝ) (hC : 0≤C) (hP : ∀ u : E, ‖u‖≤B → Q u∈K → ‖P u‖≤C)
    (hop : ∀ τ : ℝ, 0<τ → ∃ δ : ℝ, 0<δ ∧ ∀ u : E, ‖u‖≤B → Q u∈K →
      ∀ I : E × (Fin N → E →L[ℝ] E), ‖I‖<δ →
        ‖fcFiniteTerminal Q N (Q u+I.1,I.2)-homogeneousResponse (P u) I‖≤τ*‖I‖^d) :
    ∀ η : ℝ, 0<η → ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : E, ‖u‖≤B → Q u∈K →
        ‖G (metricFCPoint T f G fullMemory r (ε • u) N)-
          ε^(d+1) • homogeneousResponse (P u) (metricFCReferenceInputJet Q D u N)‖≤η*ε^(d+1) := by
  let U : Set E := {u | ‖u‖≤B ∧ Q u∈K}
  let x := fun ε u => metricFCInput T f G H Q r ε u N
  let v := fun u => metricFCReferenceInputJet Q D u N
  let F := fun u (I : E × (Fin N → E →L[ℝ] E)) => fcFiniteTerminal Q N (Q u+I.1,I.2)
  obtain ⟨ex,Cx,hex,hCx,hsource⟩ := metricFCInput_bound T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG B hB
  have hxb : ∃ ep : ℝ, 0<ep ∧ ∀ ε : ℝ, 0<ε → ε<ep → ∀ u∈U, ‖x ε u‖≤Cx*ε := by
    exact ⟨ex,hex,fun ε hε he u hu => (hsource ε hε he u hu.1).2 N⟩
  have hjet : ∀ τ : ℝ, 0<τ → ∃ ep : ℝ, 0<ep ∧ ∀ ε : ℝ, 0<ε → ε<ep →
      ∀ u∈U, ‖x ε u-ε • v u‖≤τ*ε := by
    intro τ hτ
    obtain ⟨ep,hep,hj⟩ := metricFCInput_reference_jet T hT f G H Q D hD hr hG₀ hH₀ hHc₀
      hLr hH hF hG hQ hpos N K hK hpre B hB τ hτ
    exact ⟨ep,hep,fun ε hε he u hu => hj ε hε he u hu.1 hu.2⟩
  have hv := uniform_jet_leading_bound x v U Cx hxb hjet
  have hxb' : ∃ ep : ℝ, 0<ep ∧ ∀ ε : ℝ, 0<ε → ε<ep → ∀ u∈U, ‖x ε u‖≤(Cx+1)*ε := by
    refine ⟨ex,hex,?_⟩
    intro ε hε he u hu
    exact ((hsource ε hε he u hu.1).2 N).trans (by nlinarith only [hε.le])
  have ht := homogeneous_cycle_transfer F P x v U (Cx+1) C (by positivity) hC
    (fun u hu => hP u hu.1 hu.2) hv hxb' hjet
    (fun τ hτ => by
      obtain ⟨δ,hδ,hb⟩ := hop τ hτ
      exact ⟨δ,hδ,fun u hu I hI => hb u hu.1 hu.2 I hI⟩)
  intro η hη
  obtain ⟨ep,hep,hb⟩ := ht η hη
  refine ⟨min ex ep,lt_min hex hep,?_⟩
  intro ε hε he u hu hKu
  have hx₀ := (hsource ε hε (he.trans_le (min_le_left _ _)) u hu).1
  have hd := metricFCPoint_gradient_eq_finiteTerminal T hT f G H Q hr hG₀ hHc₀ hLr hH hF hG
    ε hε.ne' u hx₀ N
  rw [hd]
  exact hb ε hε (he.trans_le (min_le_right _ _)) u ⟨hu,hKu⟩

end
end krylov.Functions
