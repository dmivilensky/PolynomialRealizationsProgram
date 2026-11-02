import krylov.LotkaVolterra.Barrier

/-!
Article: main_krylov, apC:prop:g1, invariance of the escape wedge.
Use: lift the two strict boundary signs to actual forward orbit invariance.
Source: the first-contact barrier lemma and the exact coordinate exponential
formula; no assumed maximal flow or separating orbit is used.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set

/-- Once an actual endpoint orbit enters P₁, it remains there for the
rest of its existing forward time interval. -/
theorem endpoint_escape_forward_invariant {l r a b : ℝ} {α : ℝ → ℝ × ℝ}
    (hα : IsSolutionOn 1 α (Ioo l r)) (ha : a ∈ Ioo l r) (hb : b ∈ Ioo l r)
    (hab : a ≤ b) (hPa : α a ∈ endpointEscapeRegion) :
    α b ∈ endpointEscapeRegion := by
  have hsub : Icc a b ⊆ Ioo l r :=
    fun _ ht ↦ ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩
  have hs : ∀ t ∈ Icc a b, HasDerivAt (fun u ↦ (α u).1 - 4)
      (sRate 1 (α t).1 (α t).2) t := by
    intro t ht
    exact (solution_s_hasDerivAt (hα t (hsub ht))).sub_const 4
  have hg : ∀ t ∈ Icc a b, HasDerivAt (fun u ↦ (α u).1 / 4 - (α u).2)
      (sRate 1 (α t).1 (α t).2 / 4 - uRate (α t).1 (α t).2) t := by
    intro t ht
    exact ((solution_s_hasDerivAt (hα t (hsub ht))).div_const 4).sub
      (solution_u_hasDerivAt (hα t (hsub ht)))
  have hbar := pair_positive_invariant hab hs hg
    (sub_pos.mpr hPa.1) (sub_pos.mpr hPa.2.2)
    (fun t _ he hge ↦ ?_) (fun t _ he hpos ↦ ?_)
  · have hpos : α a ∈ positiveQuadrant := ⟨by linarith [hPa.1], hPa.2.1⟩
    have hUb := (solution_positive_on_interval hα ha hpos b hb).2
    exact ⟨by linarith [hbar.1], hUb, by linarith [hbar.2]⟩
  · have hst : (α t).1 = 4 := by linarith
    rw [hst]
    apply endpoint_escape_vertical_inward
    linarith
  · have hst : 4 < (α t).1 := by linarith
    have hUt : (α t).2 = (α t).1 / 4 := by linarith
    rw [hUt]
    have hh := endpoint_escape_edge_inward hst
    linarith

end
end krylov.LotkaVolterra
