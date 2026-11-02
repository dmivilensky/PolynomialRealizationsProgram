import krylov.Methods.DirectionReplay
import krylov.Methods.InformationSpan

/-!
Article: main_krylov, def:classes(M₁), XRFC-D actual information admissibility.
Use: prove that actual direction replay and every evaluated XRFC-D step
remain in the span of genuinely observed data, for arbitrary histories.
Source: actual gradient differences, data-only replay and finite observed-span induction.
-/

namespace krylov.Methods
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Adding a real observed iteration preserves the complete earlier observed-vector span.
Use: actual replay may use older observations without obtaining any unobserved operator action.
Article: main_krylov, def:classes(M₁), information grows with actual observations.
Proof: earlier pair/record generators persist; the previous gradient is the
new actual gradient minus the new observed secant difference. -/
theorem History.observedSpan_cons (H : History E) (r : IterationRecord E) :
    H.observedSpan≤(History.mk H.initial (r::H.records)).observedSpan := by
  -- Recover the previous gradient using only the genuinely observed new gradient and its recorded difference.
  let Hnew := History.mk H.initial (r::H.records)
  have hy : r.gradient-H.gradient∈Hnew.observedSpan := by
    apply Submodule.subset_span
    exact Or.inl (Or.inr ⟨(r.step,r.gradient-H.gradient),List.mem_cons_self,rfl⟩)
  have hg : H.gradient∈Hnew.observedSpan := by
    have h := Submodule.sub_mem Hnew.observedSpan Hnew.gradient_mem_observedSpan hy
    change r.gradient-(r.gradient-H.gradient)∈Hnew.observedSpan at h
    rwa [sub_sub_cancel] at h
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with ((hv | hv) | hv) | hv
  · rcases hv with rfl | rfl
    · exact Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inl rfl))))
    · exact hg
  · obtain ⟨p,hp,rfl⟩ := hv
    apply Submodule.subset_span
    exact Or.inl (Or.inl (Or.inr ⟨p,List.mem_cons_of_mem _ hp,rfl⟩))
  · obtain ⟨p,hp,rfl⟩ := hv
    apply Submodule.subset_span
    exact Or.inl (Or.inr ⟨p,List.mem_cons_of_mem _ hp,rfl⟩)
  · obtain ⟨old,hold,hv⟩ := hv
    apply Submodule.subset_span
    exact Or.inr ⟨old,List.mem_cons_of_mem r hold,hv⟩

/-- Every actual direction replay entry consists of vectors in the genuine observed information span.
Use: reconstructed direction images use actual observations even off quadratics and for arbitrary data histories.
Article: main_krylov, def:classes(M₁), XRFC-D observed-span admissibility.
Proof: induct on the actual history. Previous replay entries stay in the
growing observed span; virtual gradients and directions combine prior observations, and the new image is a scalar multiple of the actual new gradient minus that computed virtual gradient. -/
theorem directionReplay_mem_observedSpan (memory : ℕ → ℕ) (trial : History E → ℝ)
    (initial : E) (records : List (IterationRecord E)) :
    ∀ p∈directionReplay memory trial initial records,
      p.1∈(History.mk initial records).observedSpan ∧ p.2∈(History.mk initial records).observedSpan := by
  -- The argument uses only data-level linear combinations; no quadratic consistency or unknown operator is assumed.
  induction records with
  | nil => simp only [directionReplay,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | cons r rs ih =>
    let H := History.mk initial rs
    let Hnew := History.mk initial (r::rs)
    let W := (directionReplay memory trial initial rs).take (memory rs.length)
    have hstep (i : Fin W.length) : windowSteps W i∈H.observedSpan :=
      (ih (W.get i) (List.mem_of_mem_take (List.get_mem W i))).1
    have himage (i : Fin W.length) : windowImages W i∈H.observedSpan :=
      (ih (W.get i) (List.mem_of_mem_take (List.get_mem W i))).2
    have hgv : virtualGradient W H.gradient∈H.observedSpan :=
      H.observedSpan.add_mem H.gradient_mem_observedSpan (combine_mem _ _ himage _)
    have hd : windowDirection W (virtualGradient W H.gradient)∈H.observedSpan :=
      H.observedSpan.add_mem (H.observedSpan.neg_mem hgv) (combine_mem _ _ hstep _)
    intro p hp
    change p∈(windowDirection W (virtualGradient W H.gradient),
      (trial H)⁻¹ • (r.gradient-virtualGradient W H.gradient))::directionReplay memory trial initial rs at hp
    rcases List.mem_cons.mp hp with he | he
    · rw [he]
      exact ⟨H.observedSpan_cons r hd,Hnew.observedSpan.smul_mem _
        (Hnew.observedSpan.sub_mem Hnew.gradient_mem_observedSpan (H.observedSpan_cons r hgv))⟩
    · exact ⟨H.observedSpan_cons r (ih p he).1,H.observedSpan_cons r (ih p he).2⟩

/-- Every evaluated actual XRFC-D displacement lies in the span of genuinely observed data.
Use: proves the exact source one-gradient information restriction for the actual reconstructed-direction policy on arbitrary histories.
Article: main_krylov, def:classes(M₁), XRFC-D is data-only and span restricted.
Proof: all actually selected replay vectors and images lie in the observed
span; actual virtual solves, extrapolated gradients, directions and trials are finite combinations in that same span. -/
theorem xrfcDMethod_spanRestricted (memory : ℕ → ℕ) (trial : History E → ℝ) :
    OneGradientSpanRestricted (xrfcDMethod memory trial : OneGradientMethod E) := by
  -- This is an information theorem for every possible history, independently of the quadratic execution theorem.
  intro H
  let W := selectedDirectionWindow memory trial H
  have hs (i : Fin W.length) : windowSteps W i∈H.observedSpan :=
    (directionReplay_mem_observedSpan memory trial H.initial H.records (W.get i)
      (List.mem_of_mem_take (List.get_mem W i))).1
  have hy (i : Fin W.length) : windowImages W i∈H.observedSpan :=
    (directionReplay_mem_observedSpan memory trial H.initial H.records (W.get i)
      (List.mem_of_mem_take (List.get_mem W i))).2
  have hg : virtualGradient W H.gradient∈H.observedSpan :=
    H.observedSpan.add_mem H.gradient_mem_observedSpan (combine_mem _ _ hy _)
  have hd : windowDirection W (virtualGradient W H.gradient)∈H.observedSpan :=
    H.observedSpan.add_mem (H.observedSpan.neg_mem hg) (combine_mem _ _ hs _)
  exact H.observedSpan.add_mem (combine_mem _ _ hs _) (H.observedSpan.smul_mem _ hd)

end
end krylov.Methods
