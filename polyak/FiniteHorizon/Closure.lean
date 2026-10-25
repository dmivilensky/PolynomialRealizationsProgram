import polyak.FiniteHorizon.PricesLimit
import Mathlib.Topology.Order.Compact

/-!
Article: Appendix C, the compact-neighborhood step of Lemma nearkernel.
Use: strict contraction on the zero-price slice extends to one uniform positive
price neighborhood of every compact normalized endpoint set.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth.FiniteHorizon
open scoped Topology Matrix.Norms.Elementwise

/-- Exact compactness argument used after the smaller-rate kernel estimate.
The endpoint set may contain all dimensions; only its proved compactness enters. -/
theorem exists_near_kernel_contraction {H : ℕ} (L : WindowPrice H) {c : ℝ}
    (P : Set (WindowSpace H × WindowSpace H)) (hP : IsCompact P)
    (hpos : ∀ Y∈P,0≤L Y.1)
    (hkernel : ∀ Y∈P,L Y.1=0 → traceWindow Y.2<c) :
    ∃ η : ℝ, 0<η ∧ ∀ Y∈P,L Y.1≤η → traceWindow Y.2<c := by
  let bad := P∩{Y | c≤traceWindow Y.2}
  have hbad : IsCompact bad:=hP.inter_right
    (isClosed_le continuous_const ((traceWindow_continuous H).comp continuous_snd))
  have hl : ∀ Y∈bad, 0<L Y.1 := by
    intro Y hY
    have hn:=hpos Y hY.1
    by_contra h
    have hz : L Y.1=0:=le_antisymm (by linarith) hn
    exact (not_lt_of_ge hY.2) (hkernel Y hY.1 hz)
  obtain ⟨η,hη,hmin⟩:=hbad.exists_forall_le'
    (L.continuous.comp continuous_fst).continuousOn hl
  refine ⟨η/2,by linarith,?_⟩
  intro Y hY hsmall
  by_contra h
  have hYbad : Y∈bad:=⟨hY,le_of_not_gt h⟩
  have hm:=hmin Y hYbad
  change η≤L Y.1 at hm
  linarith

/-- The closed actual zero-price slice of a compact trace-one window cone is compact. -/
theorem priceKernel_trace_one_isCompact (A B β : ℝ) (H : ℕ) (L : WindowPrice H) :
    IsCompact {Y : WindowSpace H | Y∈priceKernel A B β H L ∧ traceWindow Y=1} := by
  have hc:=windowCone_trace_one_isCompact A B β H
  have he : {Y : WindowSpace H | Y∈priceKernel A B β H L ∧ traceWindow Y=1}=
      {Y : WindowSpace H | Y∈windowCone A B β H ∧ traceWindow Y=1}∩{Y | L Y=0} := by
    ext Y
    simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,priceKernel]
    tauto
  rw [he]
  exact hc.inter_right (isClosed_eq L.continuous continuous_const)

end polyak.FiniteHorizon
