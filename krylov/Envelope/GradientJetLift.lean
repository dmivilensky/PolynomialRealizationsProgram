import krylov.Envelope.FirstJets
import krylov.Reference.PolynomialAction
import krylov.Reference.Stopping

/-!
Article: main_krylov, apB:lem:filtration, genuine reference-gradient jet coordinates.
Use: lift actual observed gradient derivatives linearly from the true
orthogonal reference gradients, and prove consistency of the lift on every
real earlier Krylov flag. No trajectory expansion is part of the definition.
Source: actual CG gradient orthogonality, nonzero reference energies and the
previously proved equality of genuine gradient and polynomial Krylov flags.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual reference-gradient coordinate lift of the supplied genuine gradient derivative sequence.
Use: The actual reference-gradient coordinate lift of the supplied genuine gradient derivative sequence.
Article: main_krylov, apB:lem:filtration, genuine reference-gradient jet coordinates.
Proof: Use the true measured orthogonal reference gradients and their real nonzero energy denominators on the active prefix. -/
def gradientJetLift (Q : E →L[ℝ] E) (g : E) (δg : ℕ → E) (k : ℕ) : E →ₗ[ℝ] E where
  -- The lift uses the genuine orthogonal reference-gradient coordinates.
  toFun v := ∑ i∈Finset.range (k+1), (inner ℝ (CG.gradient Q g i) v/‖CG.gradient Q g i‖^2) • δg i
  map_add' u v := by simp only [inner_add_right,add_div,add_smul,Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [real_inner_smul_right,Finset.smul_sum,smul_smul,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring

/-- Distinct actual nonstagnating reference gradients have zero genuine Euclidean pairing.
Use: Distinct actual nonstagnating reference gradients have zero genuine Euclidean pairing.
Article: main_krylov, apB:lem:filtration, genuine reference-gradient jet coordinates.
Proof: Use the true CG geometric invariant in the actual index order. -/
theorem cg_gradient_inner_ne (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hpre : ∀ i < k, CG.gradient Q g i≠0) (i j : ℕ) (hi : i < k) (hj : j < k) (hij : i≠j) :
    inner ℝ (CG.gradient Q g i) (CG.gradient Q g j)=0 := by
  rcases lt_or_gt_of_ne hij with h|h
  · exact (CG.invariant Q hQ hpos g j (fun l hl => hpre l (hl.trans hj))).old_gradient i h
  · rw [real_inner_comm]
    exact (CG.invariant Q hQ hpos g i (fun l hl => hpre l (hl.trans hi))).old_gradient j h

/-- The genuine coordinate lift recovers each actual prescribed reference-gradient derivative exactly.
Use: The genuine coordinate lift recovers each actual prescribed reference-gradient derivative exactly.
Article: main_krylov, apB:lem:filtration, genuine reference-gradient jet coordinates.
Proof: True CG orthogonality removes all other actual reference coordinates and its own nonzero gradient norm cancels the remaining diagonal. -/
theorem gradientJetLift_gradient (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (δg : ℕ → E) (k : ℕ)
    (hpre : ∀ i ≤ k, CG.gradient Q g i≠0) (j : ℕ) (hj : j ≤ k) :
    gradientJetLift Q g δg k (CG.gradient Q g j)=δg j := by
  -- Cancel only the actual tested diagonal gradient energy; every other true pairing is exactly zero.
  change (∑ i∈Finset.range (k+1), (inner ℝ (CG.gradient Q g i) (CG.gradient Q g j)/‖CG.gradient Q g i‖^2) • δg i)=_
  rw [Finset.sum_eq_single j]
  · rw [real_inner_self_eq_norm_sq,div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hpre j hj))),one_smul]
  · intro i hi hij
    rw [cg_gradient_inner_ne Q hQ hpos g (k+1) (fun l hl => hpre l (by omega)) i j
      (Finset.mem_range.mp hi) (by omega) hij,zero_div,zero_smul]
  · intro hj'
    exact (hj' (Finset.mem_range.mpr (by omega))).elim

/-- Actual reference-gradient lifts agree on every genuine earlier Krylov flag.
Use: Actual reference-gradient lifts agree on every genuine earlier Krylov flag.
Article: main_krylov, apB:lem:filtration, genuine reference-gradient jet coordinates.
Proof: The earlier true gradients span that actual polynomial Krylov space; both genuine lifts agree on each actual generator, so linearity extends their equality. -/
theorem gradientJetLift_restrict (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (δg : ℕ → E) (k j : ℕ)
    (hpre : ∀ i ≤ k, CG.gradient Q g i≠0) (hjk : j ≤ k) {v : E}
    (hv : v∈CG.krylovSpace Q g (j+1)) : gradientJetLift Q g δg k v=gradientJetLift Q g δg j v := by
  -- Derive the true positive reference lines before using the proved actual polynomial flag identification.
  have hline (i : ℕ) (hi : i < j+1) : CG.length Q g i≠0 :=
    (CG.invariant_line_pos Q hpos g i (CG.invariant Q hQ hpos g i
      (fun l hl => hpre l (by omega))) (hpre i (by omega))).2.1.ne'
  rw [CG.krylovSpace_eq_span_gradients Q g (j+1) hline] at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i,hi,rfl⟩ := hv
    rw [gradientJetLift_gradient Q hQ hpos g δg k hpre i (by change i < j+1 at hi;omega),
      gradientJetLift_gradient Q hQ hpos g δg j (fun l hl => hpre l (hl.trans hjk)) i (by change i < j+1 at hi;omega)]
  | zero => simp only [map_zero]
  | add u v _ _ hu hv => rw [map_add,map_add,hu,hv]
  | smul a v _ hv => rw [map_smul,map_smul,hv]
end
end krylov.Envelope
