import krylov.Methods.DirectBroydenModel
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), actual conjugate direct models.
Use: derive all genuine stored secants of the native direct recursion on
the reference conjugate pairs for every nonnegative interpolation schedule.
Source: literal direct Broyden update, actual symmetry and real rank-one
annihilation; no matrix-model correctness field is assumed.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine direct update preserves a true older secant when the actual
new and old observed pairs have both conjugate cross pairings.
Use: exact reference correctness concerns the literal chronological model.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: actual old symmetry turns the old secant into zero new curvature
pairing; the genuine correction vector also annihilates the old step.
All three literal rank-update changes therefore vanish. -/
theorem directBroydenUpdate_preserves_secant (B : E →ₗ[ℝ] E)
    (hB : B.IsSymmetric) (s y u v : E) (phi : ℝ)
    (hu : B u=v) (hsv : inner ℝ s v=0) (hyu : inner ℝ y u=0) :
    directBroydenUpdate B s y phi u=v := by
  have hsu : inner ℝ s (B u)=0 := by rw [hu,hsv]
  have hBu : inner ℝ (B s) u=0 := (hB s u).trans hsu
  have hvu : inner ℝ (directBroydenVector B s y) u=0 := by
    rw [directBroydenVector,inner_sub_left,real_inner_smul_left,real_inner_smul_left,hyu,hBu]
    ring
  rw [directBroydenUpdate_apply,hsu,hyu,hvu]
  simp only [zero_div,zero_smul,sub_zero,add_zero,mul_zero,hu]

/-- The actual native direct Broyden model imposes every real observed
secant on a positive pairwise conjugate reference transcript.
Use: all original convex schedules have exact reference model columns,
including schedules that vary without a perturbation limit.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: derive the true old model positivity and actual new denominators;
the new secant is imposed exactly and both true cross pairings preserve
every genuine older secant through the literal update. -/
theorem directBroydenOperatorModel_conjugate_secants (B0 : E →L[ℝ] E)
    (hB0 : B0.toLinearMap.IsSymmetric) (hpos : ∀ w : E,w≠0 → 0 < inner ℝ w (B0 w))
    (phi : ℕ → ℝ) (hphi : ∀ i,0≤phi i) (W : List (E × E))
    (hpair : ∀ p∈W,0 < inner ℝ p.1 p.2)
    (hconj : W.Pairwise (fun p q => inner ℝ p.1 q.2=0 ∧ inner ℝ p.2 q.1=0)) :
    ∀ p∈W,directBroydenOperatorModel B0 phi W p.1=p.2 := by
  induction W with
  | nil => simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | cons p W ih =>
    have ht : ∀ q∈W,0 < inner ℝ q.1 q.2 := fun q hq => hpair q (List.mem_cons_of_mem p hq)
    have hold := directBroydenOperatorModel_positive B0 hB0 hpos phi hphi W ht
    have hp := directBroydenOperatorModel_pivots B0 hB0 hpos phi hphi (p::W) hpair
    have hc := List.pairwise_cons.mp hconj
    intro q hq
    change directBroydenUpdate (directBroydenOperatorModel B0 phi W).toLinearMap
      p.1 p.2 (phi W.length) q.1=q.2
    rcases List.mem_cons.mp hq with rfl | hq
    · exact directBroydenUpdate_secant _ _ _ _ hp.1 hp.2.1
    · exact directBroydenUpdate_preserves_secant _ hold.1 _ _ _ _ _
        (ih ht hc.2 q hq) (hc.1 q hq).1 (hc.1 q hq).2

end
end krylov.Methods
