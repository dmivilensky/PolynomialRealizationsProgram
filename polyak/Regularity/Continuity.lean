import polyak.Regularity.Critical

/-!
Article: Theorem classification, continuity of the actual spectral boundary.
Use: compactness gives upper semicontinuity, and strict twist shrink gives
lower semicontinuity away from zero. The genuine local central branch covers zero.
-/
noncomputable section
namespace polyak.Regularity
open Spectral Set Filter
open scoped Topology

theorem V_upperSemicontinuousAt (t : ℝ) : UpperSemicontinuousAt V t := by
  rw [upperSemicontinuousAt_iff]
  intro b hb
  let K := Icc (0 : ℝ) (Real.arsinh 1) ×ˢ Icc (t-1) (t+1)
  let S : Set ((ℝ×ℝ)×(Spectrum×ℝ)) :=
    {p | p.1∈K ∧ Feasible p.1.1 p.1.2 p.2.1 p.2.2 ∧ b≤p.1.1}
  have hcomp : IsCompact S := by
    have hcb : IsClosed {p : (ℝ×ℝ)×(Spectrum×ℝ) | b≤p.1.1} :=
      isClosed_le continuous_const continuous_fst.fst
    convert (isCompact_feasible_over (isCompact_Icc.prod isCompact_Icc : IsCompact K)).inter_right
      hcb using 1
    ext p
    simp only [S,K,mem_inter_iff,mem_ofPred_eq,and_assoc]
  have hbad : IsClosed ((fun p : (ℝ×ℝ)×(Spectrum×ℝ) => p.1.2) '' S) :=
    (hcomp.image continuous_fst.snd).isClosed
  have ht : t∉(fun p : (ℝ×ℝ)×(Spectrum×ℝ) => p.1.2) '' S := by
    rintro ⟨⟨⟨v,s⟩,ν,C⟩,hp,he⟩
    dsimp at he
    subst s
    have hh : v≤V t := (isGreatest_V t).2 ⟨ν,C,hp.2.1⟩
    linarith [hp.2.2]
  have hnear : ∀ᶠ s in 𝓝 t,s∈Icc (t-1) (t+1) :=
    Icc_mem_nhds (by linarith) (by linarith)
  filter_upwards [hbad.isOpen_compl.mem_nhds ht,hnear] with s hs hsI
  by_contra hn
  obtain ⟨ν,C,hf⟩ := V_mem s
  exact hs ⟨((V s,s),(ν,C)),⟨⟨⟨V_nonneg s,V_le_arsinh_one s⟩,hsI⟩,hf,le_of_not_gt hn⟩,rfl⟩

theorem V_lowerSemicontinuousAt {t : ℝ} (ht : t≠0) : LowerSemicontinuousAt V t := by
  rw [lowerSemicontinuousAt_iff]
  intro b hb
  by_cases hb0 : b<0
  · exact Eventually.of_forall (fun s => hb0.trans_le (V_nonneg s))
  · let v := (b+V t)/2
    have hv0 : 0≤v := by dsimp [v]; linarith
    have hvt : v<V t := by dsimp [v]; linarith
    have hbv : b<v := by dsimp [v]; linarith
    obtain ⟨ν,C,hf⟩ := V_mem t
    obtain ⟨C',hlocal⟩ := hf.interior_mono ht hv0 hvt
    have hp : Tendsto (fun s : ℝ => (v,s)) (𝓝 t) (𝓝 (v,t)) :=
      continuousAt_const.prodMk_nhds continuousAt_id
    filter_upwards [hp.eventually hlocal] with s hs
    exact hbv.trans_le ((isGreatest_V s).2 ⟨ν,C',hs⟩)

theorem V_continuous : Continuous V := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t=0
  · subst t
    exact Boundary.P5.V_analyticAt_zero.continuousAt
  · exact continuousAt_iff_lower_upperSemicontinuousAt.mpr
      ⟨V_lowerSemicontinuousAt ht,V_upperSemicontinuousAt t⟩

end polyak.Regularity
